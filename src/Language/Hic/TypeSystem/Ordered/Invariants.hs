{-# LANGUAGE DataKinds             #-}
{-# LANGUAGE DeriveGeneric         #-}
{-# LANGUAGE FlexibleContexts      #-}
{-# LANGUAGE FlexibleInstances     #-}
{-# LANGUAGE GADTs                 #-}
{-# LANGUAGE LambdaCase            #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE OverloadedStrings     #-}
{-# LANGUAGE PatternSynonyms       #-}
{-# LANGUAGE TupleSections         #-}

module Language.Hic.TypeSystem.Ordered.Invariants
    ( InvariantResult (..)
    , runInvariantAnalysis
    ) where

import           Control.Applicative                         ((<|>))
import           Control.Monad                               (foldM, forM_,
                                                              unless, void,
                                                              when)
import           Control.Monad.Identity                      (Identity (..))
import           Control.Monad.State.Strict                  (State, StateT,
                                                              execState, lift)
import qualified Control.Monad.State.Strict                  as State
import           Data.Aeson                                  (ToJSON)
import           Data.Bifunctor                              (bimap)
import           Data.Fix                                    (Fix (..), foldFix,
                                                              foldFixM, unFix)
import           Data.Foldable                               (fold, toList)
import           Data.List                                   (find, foldl', nub)

import           Data.Map.Strict                             (Map)
import qualified Data.Map.Strict                             as Map
import           Data.Maybe                                  (catMaybes,
                                                              fromMaybe, isJust,
                                                              listToMaybe,
                                                              mapMaybe)
import           Data.Set                                    (Set)
import qualified Data.Set                                    as Set
import           Data.Text                                   (Text)
import qualified Data.Text                                   as T
import qualified Debug.Trace                                 as Debug
import           GHC.Generics                                (Generic)
import           Language.Cimple                             (Lexeme (..), Node,
                                                              NodeF (..))
import qualified Language.Cimple                             as C
import qualified Language.Cimple.Program                     as Program
import           Language.Hic.Core.AstUtils                  (getParamName,
                                                              parseInteger)
import           Language.Hic.Core.DataFlow                  (CFG, CFGNode (..),
                                                              DataFlow (..),
                                                              buildCFG,
                                                              fixpoint)
import           Language.Hic.Core.Errors                    (MismatchReason (..))
import           Language.Hic.Core.TypeSystem                (Invariant (..),
                                                              Phase (..),
                                                              StdType (..),
                                                              TemplateId (..),
                                                              TypeDescr (..),
                                                              TypeSystem,
                                                              pattern Array,
                                                              pattern BuiltinType,
                                                              pattern Const,
                                                              pattern Pointer,
                                                              pattern Singleton,
                                                              pattern Template,
                                                              pattern TypeRef)
import           Language.Hic.TypeSystem.Core.Base           (stripAllWrappers)

import qualified Language.Hic.TypeSystem.Core.Base           as TS
import           Language.Hic.TypeSystem.Core.Constraints    (Constraint (..))
import qualified Language.Hic.TypeSystem.Core.Constraints    as Constraints
import qualified Language.Hic.TypeSystem.Ordered.Specializer as Spec

import           Language.Hic.TypeSystem.Ordered.CallGraph   (SccType (..),
                                                              pattern Acyclic,
                                                              pattern Cyclic)

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

data InvariantResult = InvariantResult
    { irInvariants    :: Map Text [Invariant 'Global] -- StructName -> Invariants
    , irFunctionLinks :: Map Text [Invariant 'Global] -- FunctionName -> Links between params
    , irTypeSystem    :: TypeSystem                   -- Updated TypeSystem with integrated invariants
    } deriving (Show, Generic)

instance ToJSON InvariantResult

-- | Flow-sensitive facts tracked during data flow analysis.
data InvariantFacts = InvariantFacts
    { ifVars       :: Map Text (Set (TS.TypeInfo 'Local))
    , ifPathGuards :: Set (TS.TypeInfo 'Local)
    , ifStructs    :: Set (TS.TypeInfo 'Local) -- Struct instances encountered in expressions
    } deriving (Eq, Show)

-- | Read-only context for the data flow analysis of a single function.
data InvariantContext l = InvariantContext
    { icCurrentFunc :: l
    , icParamTypes  :: [TS.TypeInfo 'Local]
    }

-- | Global state accumulated across all functions and SCC iterations.
data AnalysisState = AnalysisState
    { asTypeSystem    :: TypeSystem
    , asNextId        :: Int
    , asInvariants    :: Map Text (Set (Invariant 'Global))
    , asFunctionLinks :: Map Text (Set (Invariant 'Global))
    , asReturnOrigins :: Map Text (Set (TS.TypeInfo 'Global)) -- FunctionName -> Formal origins of return value
    } deriving (Eq, Show)

type Analyze = State AnalysisState

instance DataFlow Analyze InvariantContext Text InvariantFacts () where
    emptyFacts _ = return $ InvariantFacts Map.empty Set.empty Set.empty

    join _ a b = return $ InvariantFacts
        { ifVars = Map.unionWith Set.union (ifVars a) (ifVars b)
        , ifPathGuards = Set.intersection (ifPathGuards a) (ifPathGuards b)
        , ifStructs = Set.union (ifStructs a) (ifStructs b)
        }

    transfer ctx _ _ facts stmt = do
        facts' <- transferStmt ctx facts stmt
        return (facts', Set.empty)

transferStmt :: InvariantContext Text -> InvariantFacts -> Node (Lexeme Text) -> Analyze InvariantFacts
transferStmt ctx facts n = do
    (_, facts') <- State.runStateT (foldFixM collect n) facts
    return facts'
  where
    collect :: NodeF (Lexeme Text) (Node (Lexeme Text)) -> StateT InvariantFacts Analyze (Node (Lexeme Text))
    collect node = do
        let n' = Fix node
        facts' <- State.get
        case node of
            C.VarDeclStmt (Fix (C.VarDecl ty (L _ _ name) _)) mInit -> do
                st <- lift State.get
                case State.runState (foldFixM TS.collectTypes (Fix $ C.MemberDecl ty Nothing)) (asTypeSystem st, asNextId st) of
                    (tyFormal:_, (ts', nextId')) -> do
                        lift $ State.modify $ \s -> s { asTypeSystem = ts', asNextId = nextId' }
                        let origin = TS.LocalVar name
                            tyLocal = TS.toLocal 0 origin (TS.toGlobal (TS.toLocal 0 TS.TopLevel tyFormal))
                        case mInit of
                            Just initVal -> do
                                origins <- lift $ trackInitialiser ctx facts' tyLocal initVal
                                State.modify $ \s -> s { ifVars = Map.insert name origins (ifVars s) }
                            Nothing ->
                                State.modify $ \s -> s { ifVars = Map.insert name (Set.singleton tyLocal) (ifVars s) }
                    _ -> return ()

            C.FunctionCall (Fix (C.VarExpr (L _ _ "__tokstyle_assume_true"))) [cond] -> do
                guards <- lift $ getGuards ctx facts' cond
                State.modify $ \s -> s { ifPathGuards = guards `Set.union` ifPathGuards s }

            C.FunctionCall (Fix (C.VarExpr (L _ _ "__tokstyle_assume_false"))) [cond] -> do
                guards <- lift $ getInverseGuards ctx facts' cond
                State.modify $ \s -> s { ifPathGuards = guards `Set.union` ifPathGuards s }

            C.FunctionCall func args -> do
                funcOrigins <- lift $ getOrigin ctx facts' func
                mArgsOrigins <- lift $ mapM (getOrigin ctx facts') args

                lift $ forM_ (Set.toList funcOrigins) $ \ft -> do
                    ts <- State.gets asTypeSystem
                    let resolvedFt = TS.resolveRefLocal ts ft
                    case TS.getTypeParams ts resolvedFt of
                        Just formalParams -> do
                            -- CASE A: ft is a callback being executed: cb(u)
                            let voidCbParams = [ (i, TS.stripAllWrappers p) | (i, p) <- zip [0..] formalParams, isVoidLike (TS.stripAllWrappers p) ]
                            forM_ voidCbParams $ \(i, dvp) -> do
                                if i < length mArgsOrigins
                                    then forM_ (Set.toList (mArgsOrigins !! i)) $ \a_data -> do
                                        promoteInvariant ctx facts' [ft, a_data, dvp] (\finalize -> InvCoordinatedPair (finalize ft) (TS.getInnerType (finalize a_data)) (finalize dvp))
                                    else return ()

                            -- CASE B: ft is a regular function taking callbacks as arguments: register(cb, u)
                            let interests = zip formalParams mArgsOrigins
                                isCallback p = isJust (TS.getTypeParams ts p)
                                isData p = TS.isPointerLike p && not (isCallback p)
                                callbacks = [ (i, p, a) | (i, (p, a)) <- zip [(0 :: Int)..] interests, isCallback p ]
                                datas     = [ (i, p, a) | (i, (p, a)) <- zip [(0 :: Int)..] interests, isData p ]

                            forM_ callbacks $ \(i_cb, p_cb, a_cb) -> do
                                let cbParams = fromMaybe [] (TS.getTypeParams ts p_cb)
                                let voidCbParams' = [ TS.stripAllWrappers p | p <- cbParams, isVoidLike (TS.stripAllWrappers p) ]
                                unless (null voidCbParams') $ do
                                    let adjacentBefore = find (\(i_d, _, _) -> i_d == i_cb - 1) datas
                                        adjacentAfter  = find (\(i_d, _, _) -> i_d == i_cb + 1) datas
                                        mTarget = adjacentAfter <|> adjacentBefore <|> (case datas of [d] -> Just d; _ -> Nothing)
                                    case mTarget of
                                        Just (_, p_data, a_data_set) -> do
                                            let targetInner = TS.getInnerType p_data
                                                hasNonGenericMatch = any (\p -> not (isVoidLike (TS.stripAllWrappers p)) && (TS.stripAllWrappers p == TS.stripAllWrappers targetInner)) cbParams
                                            unless hasNonGenericMatch $
                                                forM_ (Set.toList a_cb) $ \a_cb_origin ->
                                                forM_ (Set.toList a_data_set) $ \a_data ->
                                                forM_ voidCbParams' $ \dvp ->
                                                    promoteInvariant ctx facts' [a_cb_origin, a_data, dvp] (\finalize -> InvCoordinatedPair (finalize a_cb_origin) (TS.getInnerType (finalize a_data)) (finalize dvp))
                                        Nothing -> return ()
                        Nothing -> return ()

                    -- Callback or generic call
                    let combinations = sequence (map Set.toList mArgsOrigins)
                    forM_ combinations $ \argOrigins -> do
                        rt <- nextSolverTemplate (Just "ret")
                        let allOps = rt : ft : argOrigins
                        let mk finalize =
                                let rt' = finalize rt
                                    ft' = finalize ft
                                    args' = map finalize argOrigins
                                in InvCallable ft' args' rt'
                        promoteInvariant ctx facts' allOps mk

                case unFix func of
                    C.VarExpr (L _ _ name) -> do
                        allFuncLinks <- lift $ State.gets asFunctionLinks
                        case Map.lookup name allFuncLinks of
                            Just links -> do
                                let combinations = sequence (map Set.toList mArgsOrigins)
                                lift $ forM_ combinations $ \argOrigins -> do
                                    let substMap = getSubstMap argOrigins
                                    forM_ (Set.toList links) $ \link -> do
                                        let linkInst = TS.instantiateInvariant 0 (TS.Source name) substMap link
                                        promoteInvariant ctx facts' argOrigins (\finalize -> TS.mapInvariant finalize linkInst)
                            Nothing -> return ()
                    _ -> return ()

            C.AssignExpr lhs op rhs -> do
                lOs <- lift $ getOrigin ctx facts' lhs
                rOs <- lift $ getOrigin ctx facts' rhs
                lift $ forM_ (Set.toList lOs) $ \lo ->
                    forM_ (Set.toList rOs) $ \ro -> do
                        let mk finalize = if op == C.AopEq then InvEquality (finalize lo) (finalize ro)
                                          else InvSubtype (finalize ro) (finalize lo)
                        promoteInvariant ctx facts' [lo, ro] mk

                case unFix lhs of
                    C.VarExpr (L _ _ name) -> do
                        unless (Set.null rOs) $
                            State.modify $ \s -> s { ifVars = Map.insert name rOs (ifVars s) }
                    _ -> return ()

            C.Return mExpr -> do
                case mExpr of
                    Just expr -> do
                        origins <- lift $ getOrigin ctx facts' expr
                        let funcName = icCurrentFunc ctx
                        lift $ State.modify $ \s -> s { asReturnOrigins = Map.insertWith Set.union funcName (Set.map toFormalFunc origins) (asReturnOrigins s) }
                    Nothing -> return ()

            C.MemberAccess obj _ -> do
                origins <- lift $ getOrigin ctx facts' obj
                State.modify $ \s -> s { ifStructs = origins `Set.union` ifStructs s }

            C.PointerAccess obj _ -> do
                origins <- lift $ getOrigin ctx facts' obj
                State.modify $ \s -> s { ifStructs = origins `Set.union` ifStructs s }

            _ -> return ()
        return n'

runInvariantAnalysis :: TypeSystem -> [SccType] -> Program.Program Text -> InvariantResult
runInvariantAnalysis ts sccs program =
    let allNodes = concatMap snd (Program.toList program)
        functions = concatMap findFunctions allNodes
        nodesMap = Map.fromList $ mapMaybe (\n -> (,n) <$> getFuncName n) functions
        initialState = dtrace ("runInvariantAnalysis: found functions: " ++ show (Map.keys nodesMap) ++ " sccs: " ++ show sccs) $
                       AnalysisState ts 0 Map.empty Map.empty Map.empty
        finalState = foldl' (analyzeScc nodesMap) initialState sccs

        -- Integrate invariants into TypeSystem
        ts' = Map.foldlWithKey' (\acc name invs ->
                dtrace ("Integrating " ++ show (length invs) ++ " invariants into struct " ++ T.unpack name) $
                Map.adjust (addInvariants (Set.toList invs)) name acc
              ) (asTypeSystem finalState) (asInvariants finalState)

    in InvariantResult
        (Map.map Set.toList (asInvariants finalState))
        (Map.map Set.toList (asFunctionLinks finalState))
        ts'
  where
    addInvariants invs = \case
        StructDescr l tps members _ -> StructDescr l tps members invs
        UnionDescr l tps members _  -> UnionDescr l tps members invs
        descr                      -> descr
    findFunctions n = case unFix n of
        C.FunctionDefn {} -> [n]
        C.ExternC nodes   -> concatMap findFunctions nodes
        C.Group nodes     -> concatMap findFunctions nodes
        _                 -> []

    getFuncName (Fix (C.FunctionDefn _ proto _)) = case unFix proto of
        C.FunctionPrototype _ (L _ _ name) _ -> Just name
        _                                    -> Nothing
    getFuncName _ = Nothing

    analyzeScc nodesMap s scc = case scc of
        Acyclic func ->
            case Map.lookup func nodesMap of
                Just node -> execState (analyzeFunc node) s
                Nothing   -> s
        Cyclic funcs ->
            let cycleNodes = mapMaybe (`Map.lookup` nodesMap) funcs
                iteratePass :: Int -> AnalysisState -> AnalysisState
                iteratePass n state =
                    dtrace ("Invariant Pass " ++ show n ++ " for SCC " ++ show funcs) $
                    -- Reset asNextId for deterministic iteration
                    let stateWithResetId = state { asNextId = 0 }
                        state' = execState (mapM_ analyzeFunc cycleNodes) stateWithResetId
                    in if asInvariants state' == asInvariants state && asFunctionLinks state' == asFunctionLinks state
                       then state'
                       else iteratePass (n + 1) state'
            in iteratePass 1 s

nextSolverTemplate :: Maybe Text -> Analyze (TS.TypeInfo 'Local)
nextSolverTemplate mHint = do
    i <- State.gets asNextId
    State.modify $ \t -> t { asNextId = i + 1 }
    return $ Template (TS.TIdSolver i mHint) Nothing

analyzeFunc :: Node (Lexeme Text) -> Analyze ()
analyzeFunc n@(Fix (C.FunctionDefn _ proto _)) = do
    case unFix proto of
        C.FunctionPrototype _ (L _ _ name) params -> do
            dtraceM $ "Analyzing function: " ++ T.unpack name
            st <- State.get
            let (paramResults, nextId') = foldl' (addParam (asTypeSystem st)) ([], asNextId st) (zip [0..] params)
                (paramNames, paramTys) = unzip paramResults
                initialFacts = InvariantFacts (Map.fromList $ zip paramNames (map Set.singleton paramTys)) Set.empty Set.empty
                ctx = InvariantContext name paramTys

            State.modify $ \t -> t { asNextId = nextId' }
            cfg <- buildCFG ctx n initialFacts
            void $ fixpoint ctx name cfg
        _ -> return ()
analyzeFunc _ = return ()

promoteInvariant :: InvariantContext Text -> InvariantFacts -> [TS.TypeInfo 'Local] -> ((TS.TypeInfo 'Local -> TS.TypeInfo 'Global) -> Invariant 'Global) -> Analyze ()
promoteInvariant ctx facts localTys finalize = do
    dtraceM $ "    promoteInvariant types=" ++ show localTys
    let allTids = concatMap getLocalTemplates localTys
        roots = nub $ flip mapMaybe allTids $ \case
            TS.TIdPoly _ _ _ o -> Just o
            _ -> Nothing
        guards = Set.toList (ifPathGuards facts)

    dtraceM $ "    promoteInvariant in " ++ T.unpack (icCurrentFunc ctx) ++ ": guards=" ++ show (map TS.toGlobal guards)

    -- Additional check: don't promote invariants that link to specific global functions
    -- or concrete types.
    let isPurelyInternal inv =
            let check ty = TS.isGeneric ty
            in case inv of
                InvCallable f as r        -> check f && all check as && check r
                InvEquality t1 t2         -> check t1 && check t2
                InvSubtype t1 t2          -> check t1 && check t2
                InvCoordinatedPair tr a e -> check tr && check a && check e

    -- Helper to wrap a constraint in an InvCoordinatedPair if guards are present.
    let wrap finalize' base =
            if all TS.isGeneric guards then
                case guards of
                    [] -> [base]
                    (g:_) -> case base of
                        InvEquality t1 t2         -> [InvCoordinatedPair (finalize' g) t1 t2]
                        InvSubtype t1 t2          -> [InvCoordinatedPair (finalize' g) t1 t2]
                        InvCoordinatedPair _ a e -> [InvCoordinatedPair (finalize' g) a e]
                        _                         -> []
            else []

    -- STAGE 1: Promote to Function Link
    let baseInvF = finalize toFormalFunc
    when (isPurelyInternal baseInvF) $
        forM_ (wrap toFormalFunc baseInvF) $ \formalInv -> do
            dtraceM $ "    Promoting LINK for function " ++ T.unpack (icCurrentFunc ctx) ++ ": " ++ show formalInv
            State.modify $ \t -> t { asFunctionLinks = Map.insertWith Set.union (icCurrentFunc ctx) (Set.singleton formalInv) (asFunctionLinks t) }

    -- STAGE 2: Promote to Struct Invariant (via Lineage)
    let allOrigins = nub $ mapMaybe getOriginFromTid allTids
        lineageNodes = nub $ concatMap TS.getOriginLineage allOrigins
    forM_ lineageNodes $ \base -> do
        -- Find the type of this base object
        mBaseTy <- case base of
            TS.LocalVar n -> return $ listToMaybe . Set.toList =<< Map.lookup n (ifVars facts)
            TS.Arg i      -> if i < length (icParamTypes ctx) then return (Just (icParamTypes ctx !! i)) else return Nothing
            TS.Source n   -> do
                ts <- State.gets asTypeSystem
                case Map.lookup n ts of
                    Just descr -> return $ Just (TS.toLocal 0 (TS.Source n) (TS.typeDescrToType descr))
                    Nothing    -> return Nothing
            _ -> return $ listToMaybe . Set.toList $ Set.filter (\t -> (getOriginFromType t) == Just base) (ifStructs facts)

        case mBaseTy of
            Just bty -> do
                let peel ty = case stripAllWrappers (unwrap ty) of
                        TypeRef ref (L _ _ tid) args | ref `elem` [TS.StructRef, TS.UnionRef] -> Just (ref, tid, args)
                        Array (Just et) _ -> peel et
                        _ -> Nothing
                case peel bty of
                    Just (_, tid, args) -> do
                        let structName = TS.templateIdBaseName tid
                        ts <- State.gets asTypeSystem
                        case TS.lookupType structName ts of
                            Just descr -> do
                                let formalTids = TS.getDescrTemplates descr
                                    -- Map actual arguments back to formal parameters, ignoring origins for the key
                                    revMap' = Map.fromList $ concat $ zipWith (\f a -> [ (TS.templateIdBaseName (TS.ftId v), f) | v <- TS.getTemplateVars a ]) formalTids args

                                let isInternalTid t = case t of
                                        TS.TIdPoly _ _ _ o -> base `Set.member` Set.fromList (TS.getOriginLineage o) || o == TS.Internal || o == TS.TopLevel
                                        TS.TIdSolver {} -> True
                                        _ -> False

                                let canFormalize = all isInternalTid allTids && all (all isInternalTid . getLocalTemplates) guards

                                when (length allTids >= 2 && canFormalize) $ do
                                    let toFormalS = foldFix (Fix . bimap convertIdS id)
                                        convertIdS tid' =
                                            let baseName = TS.templateIdBaseName tid'
                                            in case Map.lookup baseName revMap' of
                                                Just fTid -> fTid
                                                Nothing   -> TS.toGlobalId tid'

                                        baseInvS = finalize toFormalS

                                    when (isPurelyInternal baseInvS) $
                                        forM_ (wrap toFormalS baseInvS) $ \formalInv' -> do
                                            dtraceM $ "    Promoting INVARIANT for struct " ++ T.unpack structName ++ " (via lineage " ++ show base ++ "): " ++ show formalInv'
                                            State.modify $ \t -> t { asInvariants = Map.insertWith Set.union structName (Set.singleton formalInv') (asInvariants t) }
                            Nothing -> return ()
                    _ -> return ()
            Nothing -> return ()

    -- STAGE 3: Promote to Root Invariant (Fallback/Generic)
    forM_ roots $ \r -> do
        let peel ty = case stripAllWrappers (unwrap ty) of
                TypeRef ref' (L _ _ t) _ -> Just (ref', TS.templateIdBaseName t)
                Array (Just et) _        -> peel et
                _                        -> Nothing
        let mPtInfos = case r of
                       TS.Arg argIdx -> if argIdx < length (icParamTypes ctx) then peel (icParamTypes ctx !! argIdx)
                                        else Nothing
                       TS.Source n -> Just (TS.StructRef, n)
                       _ -> Nothing

        case mPtInfos of
            Just (ref, sName) | ref `elem` [TS.StructRef, TS.UnionRef] -> do
                let isSameRoot t = case t of { TS.TIdPoly _ _ _ r' -> r' == r; _ -> False }
                    isInternalTid t = isSameRoot t || (case t of { TS.TIdSolver {} -> True; TS.TIdPoly _ _ _ TS.Internal -> True; _ -> False })

                let canFormalize = all isInternalTid allTids && all (all isInternalTid . getLocalTemplates) guards

                when (length allTids >= 2 && canFormalize) $ do
                    let toFormalR = foldFix (Fix . bimap convertIdR id)
                        convertIdR tid' = case tid' of
                            TS.TIdPoly _ i h r' | r' == r -> TS.TIdParam i h TS.TopLevel
                            _ -> TS.toGlobalId tid'
                    let baseInvR = finalize toFormalR

                    when (isPurelyInternal baseInvR) $
                        forM_ (wrap toFormalR baseInvR) $ \formalInv' -> do
                            dtraceM $ "    Promoting INVARIANT for root struct " ++ T.unpack sName ++ ": " ++ show formalInv'
                            State.modify $ \t -> t { asInvariants = Map.insertWith Set.union sName (Set.singleton formalInv') (asInvariants t) }
            _ -> return ()
  where
    unwrap (TS.Const t) = unwrap t
    unwrap t            = TS.unwrap t

toFormalFunc :: TS.TypeInfo 'Local -> TS.TypeInfo 'Global
toFormalFunc = foldFix (Fix . bimap convertIdFunc id)

convertIdFunc :: TS.TemplateId 'Local -> TS.TemplateId 'Global
convertIdFunc = \case
    TS.TIdPoly _ i h (TS.Arg argIdx) -> TS.TIdParam i h (TS.Arg argIdx)
    TS.TIdPoly _ i h (TS.Source s)   -> TS.TIdParam i h (TS.Source s)
    tid -> TS.toGlobalId tid

getSubstMap :: [TS.TypeInfo 'Local] -> Map (TS.TemplateId 'Global) (TS.TypeInfo 'Local)
getSubstMap argOrigins = Map.fromList $ concat $ zipWith (\argIdx argOrigin ->
    let vts = TS.getTemplateVars argOrigin
    in zipWith (\i (TS.FT tid idx) -> (TS.TIdParam i (TS.templateIdHint tid) (TS.Arg argIdx), Fix (TS.TemplateF (TS.FT tid idx)))) [0..] vts
    ) [0..] argOrigins

getLocalTemplates :: TS.TypeInfo 'Local -> [TS.TemplateId 'Local]
getLocalTemplates = foldFix $ \case
    TS.TemplateF (TS.FT tid _) -> [tid]
    f -> concat f

isVoidLike :: TS.TypeInfo p -> Bool
isVoidLike t = TS.isVoid t || TS.isGeneric t

addParam :: TypeSystem -> ([(Text, TS.TypeInfo 'Local)], Int) -> (Int, Node (Lexeme Text)) -> ([(Text, TS.TypeInfo 'Local)], Int)
addParam ts (acc, nextId) (argIdx, Fix (C.VarDecl ty (L _ _ name) _)) =
    case State.runState (foldFixM TS.collectTypes (Fix $ C.MemberDecl ty Nothing)) (ts, nextId) of
        (tyFormal:_, (_, nextId')) ->
            let origin = TS.Arg argIdx
                tyResolved = TS.resolveRefLocal ts (TS.toLocal 0 TS.TopLevel tyFormal)
                tyLocal = TS.toLocal 0 origin (TS.toGlobal tyResolved)
            in (acc ++ [(name, tyLocal)], nextId')
        _ -> (acc, nextId)
addParam _ acc _ = acc

getOrigin :: InvariantContext Text -> InvariantFacts -> Node (Lexeme Text) -> Analyze (Set (TS.TypeInfo 'Local))
getOrigin ctx facts (Fix node) = do
    case node of
        C.VarExpr (L _ _ name) -> return $ fromMaybe Set.empty . Map.lookup name $ ifVars facts
        C.LiteralExpr C.Int (L _ _ val) ->
            return $ case parseInteger val of
                Just i  -> Set.singleton (Singleton S32Ty i)
                Nothing -> Set.empty
        C.MemberAccess obj (L _ _ field) -> traceMemberAccess ctx facts obj field
        C.PointerAccess obj (L _ _ field) -> traceMemberAccess ctx facts obj field
        C.ArrayAccess base idxExpr -> do
            baseTys <- getOrigin ctx facts base
            idxTys <- getOrigin ctx facts idxExpr
            let mIdxTy = case listToMaybe (Set.toList idxTys) of
                    Just t@(Fix (TS.SingletonF _ _)) -> Just t
                    _                                -> Nothing
            let mIdxLit = case mIdxTy of
                    Just (Singleton _ i) -> Just i
                    _                    -> Nothing
            let res = flip Set.map baseTys $ \bt ->
                        let unwrapped = unwrapAll bt
                            origin = case getOriginFromType bt of
                                Just o  -> TS.ArrayOrigin o mIdxLit
                                Nothing -> TS.ArrayOrigin (TS.Source "array") mIdxLit
                        in dtrace ("ArrayAccess: bt=" ++ show bt ++ " unwrapped=" ++ show unwrapped) $
                        case unFix unwrapped of
                            TS.ArrayF (Just et) _ ->
                                let res' = maybe et (`TS.indexTemplates` et) mIdxTy
                                in TS.setOrigin origin res'
                            TS.PointerF et ->
                                let res' = maybe et (`TS.indexTemplates` et) mIdxTy
                                in TS.setOrigin origin res'
                            _ -> bt
            return res
        C.UnaryExpr op e | op `elem` [C.UopAddress, C.UopDeref] -> do
            origins <- getOrigin ctx facts e
            return $ flip Set.map origins $ \o ->
                case op of
                    C.UopAddress -> TS.Pointer o
                    C.UopDeref   -> TS.getInnerType o
                    _            -> o
        C.BinaryExpr lhs op _ | op `elem` [C.BopPlus, C.BopMinus] -> getOrigin ctx facts lhs
        C.TernaryExpr _ t e -> do
            ot <- getOrigin ctx facts t
            oe <- getOrigin ctx facts e
            return (ot `Set.union` oe)
        C.CastExpr _ e -> getOrigin ctx facts e
        C.FunctionCall funcExpr args -> do
            case unFix funcExpr of
                C.VarExpr (L _ _ name) -> do
                    allReturnOrigins <- State.gets asReturnOrigins
                    case Map.lookup name allReturnOrigins of
                        Just formalReturns -> do
                            mArgsOrigins <- mapM (getOrigin ctx facts) args
                            let combinations = sequence (map Set.toList mArgsOrigins)
                            let results = flip concatMap combinations $ \argOrigins ->
                                    let substMap = getSubstMap argOrigins
                                        actualArgOrigins = map (fromMaybe TS.Internal . getOriginFromType) argOrigins
                                        rebase = rebaseType actualArgOrigins
                                    in Set.toList $ Set.map (rebase . TS.instantiate 0 TS.TopLevel substMap) formalReturns
                            return $ Set.fromList results
                        Nothing -> return Set.empty
                _ -> return Set.empty

        _ -> return Set.empty

unwrapAll :: TS.TypeInfo p -> TS.TypeInfo p
unwrapAll (Const t)           = unwrapAll t
unwrapAll (Pointer (Const t)) = Pointer (unwrapAll t) -- Special case for pointer to const
unwrapAll (TS.Owner t)        = unwrapAll t
unwrapAll (TS.Nonnull t)      = unwrapAll t
unwrapAll (TS.Nullable t)     = unwrapAll t
unwrapAll (TS.Sized t _)      = unwrapAll t
unwrapAll (TS.Var _ t)        = unwrapAll t
unwrapAll t                   = TS.unwrap t

getGuards :: InvariantContext Text -> InvariantFacts -> Node (Lexeme Text) -> Analyze (Set (TS.TypeInfo 'Local))
getGuards ctx facts (Fix node) = case node of
    C.BinaryExpr lhs op rhs ->
        case op of
            C.BopNe -> do
                lo <- getOrigin ctx facts lhs
                ro <- getOrigin ctx facts rhs
                if isNullExpr rhs then return lo
                else if isNullExpr lhs then return ro
                else return Set.empty
            C.BopAnd -> do
                lg <- getGuards ctx facts lhs
                rg <- getGuards ctx facts rhs
                return (lg `Set.union` rg)
            _ -> return Set.empty
    C.UnaryExpr C.UopNot e -> getInverseGuards ctx facts e
    C.ParenExpr e -> getGuards ctx facts e
    _ -> getOrigin ctx facts (Fix node) -- if (x) ...
  where
    isNullExpr (Fix (C.LiteralExpr _ (L _ _ "nullptr"))) = True
    isNullExpr (Fix (C.LiteralExpr _ (L _ _ "0")))       = True
    isNullExpr _                                         = False

getInverseGuards :: InvariantContext Text -> InvariantFacts -> Node (Lexeme Text) -> Analyze (Set (TS.TypeInfo 'Local))
getInverseGuards ctx facts (Fix node) = case node of
    C.BinaryExpr lhs op rhs ->
        case op of
            C.BopEq -> do
                lo <- getOrigin ctx facts lhs
                ro <- getOrigin ctx facts rhs
                if isNullExpr rhs then return lo
                else if isNullExpr lhs then return ro
                else return Set.empty
            C.BopOr -> do
                lg <- getInverseGuards ctx facts lhs
                rg <- getInverseGuards ctx facts rhs
                return (lg `Set.union` rg)
            _ -> return Set.empty
    C.UnaryExpr C.UopNot e -> getGuards ctx facts e
    C.ParenExpr e -> getInverseGuards ctx facts e
    _ -> return Set.empty
  where
    isNullExpr (Fix (C.LiteralExpr _ (L _ _ "nullptr"))) = True
    isNullExpr (Fix (C.LiteralExpr _ (L _ _ "0")))       = True
    isNullExpr _                                         = False

trackInitialiser :: InvariantContext Text -> InvariantFacts -> TS.TypeInfo 'Local -> Node (Lexeme Text) -> Analyze (Set (TS.TypeInfo 'Local))
trackInitialiser ctx facts varTy initVal = case unFix initVal of
    C.InitialiserList exprs -> do
        ts <- State.gets asTypeSystem
        case stripAllWrappers (unwrapAll varTy) of
            TypeRef ref (L _ _ tid) args | ref `elem` [TS.StructRef, TS.UnionRef] -> do
                let name = TS.templateIdBaseName tid
                    origin = fromMaybe TS.TopLevel $ listToMaybe $ mapMaybe (\case { TS.TIdPoly _ _ _ o -> Just o; _ -> Nothing }) (getLocalTemplates varTy)
                case TS.lookupType name ts of
                    Just (StructDescr _ formalTids members _) -> do
                        let argMap = Map.fromList (zip formalTids args)

                        -- Map each template ID in 'args' to its discovered origins
                        tidOrigins <- foldM (\acc ((L _ _ field, _), expr) -> do
                            exprOrigins <- getOrigin ctx facts expr
                            case TS.lookupMemberType field (StructDescr (L (C.AlexPn 0 0 0) C.IdSueType "") formalTids members []) of
                                Just mty -> do
                                    let mty' = TS.instantiate 0 origin argMap mty
                                    forM_ (Set.toList exprOrigins) $ \o -> do
                                        let mk finalize = InvEquality (finalize mty') (finalize o)
                                        promoteInvariant ctx facts [mty', o] mk

                                    -- Map templates found in mty' to exprOrigins
                                    let vts = TS.getTemplateVars mty'
                                        newAcc = foldl' (\a (TS.FT t _) -> Map.insertWith Set.union t exprOrigins a) acc vts
                                    return newAcc
                                Nothing -> return acc
                            ) Map.empty (zip members exprs)

                        -- Generate Cartesian product of instantiated struct types
                        return $ cartesianInstantiate varTy tidOrigins
                    _ -> return $ Set.singleton varTy
            _ -> return $ Set.singleton varTy
    _ -> do
        getOrigin ctx facts initVal

cartesianInstantiate :: TS.TypeInfo 'Local -> Map (TS.TemplateId 'Local) (Set (TS.TypeInfo 'Local)) -> Set (TS.TypeInfo 'Local)
cartesianInstantiate ty origins =
    let tids = getLocalTemplates ty
        possibleChoices = map (\tid -> (tid, Set.toList $ fromMaybe (Set.singleton (Fix $ TS.TemplateF (TS.FT tid Nothing))) (Map.lookup tid origins))) tids
        combinations = sequence $ map snd possibleChoices
        tidMaps = map (Map.fromList . zip (map fst possibleChoices)) combinations
    in Set.fromList $ map (\m -> TS.mapTemplates (\(TS.FT tid i) -> fromMaybe (Fix $ TS.TemplateF (TS.FT tid i)) (Map.lookup tid m)) ty) tidMaps

traceMemberAccess :: InvariantContext Text -> InvariantFacts -> Node (Lexeme Text) -> Text -> Analyze (Set (TS.TypeInfo 'Local))
traceMemberAccess ctx facts obj field = do
    baseTys <- getOrigin ctx facts obj
    ts <- State.gets asTypeSystem
    let results = flip Set.map baseTys $ \bt ->
            case stripAllWrappers (unwrapAll bt) of
                TypeRef ref (L _ _ tid) args | ref `elem` [TS.StructRef, TS.UnionRef] ->
                    let name = TS.templateIdBaseName tid
                        origin = case getOriginFromType bt of
                            Just o  -> TS.MemberOrigin o field
                            Nothing -> TS.MemberOrigin (TS.Source name) field
                    in case TS.lookupType name ts of
                        Just descr ->
                            let formalTids = TS.getDescrTemplates descr
                            in case TS.lookupMemberType field descr of
                                Just mty ->
                                    let argMap = Map.fromList (zip formalTids args)
                                        mty' = TS.instantiate 0 origin argMap mty
                                    in [TS.setOrigin origin mty']
                                Nothing -> []
                        Nothing -> []
                _ -> []
    return $ Set.fromList (concat (Set.toList results))

getOriginFromType :: TS.TypeInfo p -> Maybe TS.Origin
getOriginFromType = foldFix $ \case
    TS.TemplateF (TS.FullTemplate (TS.TIdPoly _ _ _ o) _) -> Just o
    TS.TemplateF (TS.FullTemplate (TS.TIdParam _ _ o) _) -> Just o
    f -> listToMaybe (catMaybes (Data.Foldable.toList f))

getOriginFromTid :: TS.TemplateId p -> Maybe TS.Origin
getOriginFromTid = \case
    TS.TIdPoly _ _ _ o -> Just o
    TS.TIdParam _ _ o -> Just o
    _ -> Nothing

rebaseType :: [TS.Origin] -> TS.TypeInfo 'Local -> TS.TypeInfo 'Local
rebaseType actuals = foldFix (Fix . bimap (rebaseId actuals) id)

rebaseId :: [TS.Origin] -> TS.TemplateId 'Local -> TS.TemplateId 'Local
rebaseId actuals = \case
    TS.TIdPoly ph i h o -> TS.TIdPoly ph i h (rebaseOrigin actuals o)
    tid -> tid

rebaseOrigin :: [TS.Origin] -> TS.Origin -> TS.Origin
rebaseOrigin actuals = \case
    TS.Arg i | i < length actuals -> actuals !! i
    TS.MemberOrigin o f -> TS.MemberOrigin (rebaseOrigin actuals o) f
    TS.ArrayOrigin o i  -> TS.ArrayOrigin (rebaseOrigin actuals o) i
    o -> o

