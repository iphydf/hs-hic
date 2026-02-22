{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE DeriveGeneric     #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE RecordWildCards   #-}
{-# LANGUAGE TupleSections     #-}
{-# OPTIONS_GHC -Wno-unused-top-binds #-}
module Language.Hic.TypeSystem.Ordered.Base
    ( OrderedSolverResult (..)
    , runOrderedSolver
    ) where

import           Control.Applicative                                  ((<|>))
import           Control.Monad                                        (foldM,
                                                                       forM_,
                                                                       unless,
                                                                       void,
                                                                       when,
                                                                       zipWithM_,
                                                                       (<=<))
import           Control.Monad.State.Strict                           (State,
                                                                       StateT,
                                                                       evalState,
                                                                       execState,
                                                                       lift)
import qualified Control.Monad.State.Strict                           as State
import           Data.Aeson                                           (ToJSON)
import           Data.Bifunctor                                       (Bifunctor (..))
import           Data.Fix                                             (Fix (..),
                                                                       foldFix,
                                                                       unFix)
import           Data.List                                            (find,
                                                                       foldl',
                                                                       nub)
import           Data.Map.Strict                                      (Map)
import qualified Data.Map.Strict                                      as Map
import           Data.Maybe                                           (fromMaybe,
                                                                       listToMaybe,
                                                                       mapMaybe)
import           Data.Set                                             (Set)
import qualified Data.Set                                             as Set
import           Data.Text                                            (Text)
import qualified Data.Text                                            as T
import qualified Data.Tree                                            as Tree
import qualified Debug.Trace                                          as Debug
import           GHC.Generics                                         (Generic)
import           Language.Cimple                                      (Lexeme (..))
import qualified Language.Cimple                                      as C
import           Language.Hic.Core.Errors                             (Context (..),
                                                                       ErrorInfo (..),
                                                                       MismatchReason (..),
                                                                       Provenance (..),
                                                                       TypeError (..))
import qualified Language.Hic.Core.Pretty                             as P
import           Language.Hic.Core.TypeSystem                         (FullTemplate,
                                                                       FullTemplateF (..),
                                                                       Invariant (..),
                                                                       Phase (..),
                                                                       StdType (..),
                                                                       TemplateId (..),
                                                                       TypeDescr (..),
                                                                       TypeInfo,
                                                                       TypeInfoF (..),
                                                                       TypeRef (..),
                                                                       TypeSystem,
                                                                       isVoid,
                                                                       pattern Array,
                                                                       pattern BuiltinType,
                                                                       pattern Const,
                                                                       pattern FullTemplate,
                                                                       pattern Function,
                                                                       pattern Nonnull,
                                                                       pattern Nullable,
                                                                       pattern Owner,
                                                                       pattern Pointer,
                                                                       pattern Singleton,
                                                                       pattern Sized,
                                                                       pattern Template,
                                                                       pattern TypeRef,
                                                                       pattern Var,
                                                                       pattern VarArg,
                                                                       templateIdBaseName,
                                                                       templateIdToText)
import           Language.Hic.TypeSystem.Core.Base                    (isPointerLike,
                                                                       isVarArg,
                                                                       stripAllWrappers,
                                                                       unwrap)
import qualified Language.Hic.TypeSystem.Core.Base                    as TS
import           Language.Hic.TypeSystem.Core.Constraints             (mapTypes)
import qualified Language.Hic.TypeSystem.Core.GraphSolver             as GS
import qualified Language.Hic.TypeSystem.Core.TypeGraph               as TG
import           Language.Hic.TypeSystem.Ordered.ArrayUsage           (ArrayUsageResult (..))
import           Language.Hic.TypeSystem.Ordered.CallGraph            (SccType (..))
import           Language.Hic.TypeSystem.Ordered.ConstraintGeneration (Constraint (..),
                                                                       ConstraintGenResult (..))
import           Language.Hic.TypeSystem.Ordered.Invariants           (InvariantResult (..))
import qualified Language.Hic.TypeSystem.Ordered.Specializer          as Spec
import qualified Language.Hic.TypeSystem.Ordered.Unification          as U

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

data OrderedSolverResult = OrderedSolverResult
    { osrErrors       :: [ErrorInfo 'Local]
    , osrInferredSigs :: Map Text (TypeInfo 'Local)
    } deriving (Show, Generic)

instance ToJSON OrderedSolverResult

data SolverState = SolverState
    { ssBindings      :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local)
    , ssBindingsIndex :: Map (TemplateId 'Local) [FullTemplate 'Local]
    , ssErrors        :: [ErrorInfo 'Local]
    , ssTypeSystem    :: TypeSystem
    , ssArrayUsage    :: ArrayUsageResult
    , ssInferred      :: Map Text (TypeInfo 'Local)
    , ssInvariants    :: InvariantResult
    , ssFuncPhases    :: Map Text Integer
    , ssActivePhases  :: Set Integer
    , ssNextId        :: Int
    , ssFinalPass     :: Bool
    , ssResolvedKeys  :: Set (FullTemplate 'Local)
    }

type Solver = State SolverState

runOrderedSolver :: TypeSystem -> ArrayUsageResult -> InvariantResult -> [SccType] -> ConstraintGenResult -> OrderedSolverResult
runOrderedSolver _ aur ir sccs cgr =
    let ts = irTypeSystem ir
        initialState = SolverState Map.empty Map.empty [] ts aur Map.empty ir (cgrFuncPhases cgr) Set.empty 0 True Set.empty
        finalState = execState (mapM_ (solveScc (cgrConstraints cgr)) sccs) initialState
    in OrderedSolverResult (ssErrors finalState) (ssInferred finalState)

solveScc :: Map Text [Constraint 'Local] -> SccType -> Solver ()
solveScc constrMap scc = do
    dtraceM $ "Solving SCC: " ++ show scc
    phases <- State.gets ssFuncPhases
    let activePhases = case scc of
            Acyclic func -> maybe Set.empty Set.singleton (Map.lookup func phases)
            Cyclic funcs -> Set.fromList $ mapMaybe (`Map.lookup` phases) funcs
    State.modify $ \s -> s { ssActivePhases = activePhases }
    case scc of
        Acyclic func -> do
            State.modify $ \s -> s { ssFinalPass = False }
            let constrs = Map.findWithDefault [] func constrMap
            dtraceM $ "Solving Acyclic SCC " ++ show func ++ " (Pass 1/2) with " ++ show (length constrs) ++ " constraints"
            mapM_ solveConstraint constrs
            resolveBindings

            State.modify $ \s -> s { ssFinalPass = True }
            dtraceM $ "Solving Acyclic SCC " ++ show func ++ " (Pass 2/2)"
            mapM_ solveConstraint constrs
            captureSignature func constrs
        Cyclic funcs -> do
            State.modify $ \s -> s { ssFinalPass = False }
            let constrs = concatMap (\f -> Map.findWithDefault [] f constrMap) funcs
            -- Structural Pass 1: Build initial structural bindings
            mapM_ solveConstraint constrs
            resolveBindings
            -- Structural Pass 2: Resolve HasMember/Callable using Pass 1 info
            mapM_ solveConstraint constrs
            resolveBindings
            -- Pass 3: Final propagation and settling
            State.modify $ \s -> s { ssFinalPass = True }
            mapM_ solveConstraint constrs
            resolveBindings
            mapM_ (`captureSignature` constrs) funcs

-- | Resolves all current bindings co-inductively to their fixed points.
-- Uses incremental resolution: only processes bindings added since the last
-- call, using the graph solver.  Already-resolved bindings are pre-substituted
-- into new binding types so the graph solver only operates on the small new set.
resolveBindings :: Solver ()
resolveBindings = do
    bindings <- State.gets ssBindings
    resolvedKeys <- State.gets ssResolvedKeys
    let newKeys = Map.keysSet bindings `Set.difference` resolvedKeys
    if Set.null newKeys then return ()
    else do
        let resolvedBindings = Map.restrictKeys bindings resolvedKeys
            newBindings = Map.restrictKeys bindings newKeys
            -- Pre-substitute already-resolved binding values into new binding types
            -- so the graph solver only needs to handle new-to-new dependencies.
            preSubst = Map.map (\(ty, prov) -> (substBindings resolvedBindings ty, prov)) newBindings
            graph = Map.map (\(ty, _) -> Set.singleton (TG.fromTypeInfo ty)) preSubst
            resolvedMap = GS.solveAll graph (Map.keys preSubst)
        State.modify $ \s -> s
            { ssBindings = Map.mapWithKey (\k (ty, prov) ->
                if Set.member k newKeys
                then (maybe ty TG.toTypeInfo (Map.lookup k resolvedMap), prov)
                else (ty, prov)) (ssBindings s)
            , ssResolvedKeys = Map.keysSet bindings
            }

captureSignature :: Text -> [Constraint 'Local] -> Solver ()
captureSignature func _ = do
    ts <- State.gets ssTypeSystem
    case TS.lookupType func ts of
        Just descr -> case descr of
            FuncDescr l _ ret ps -> do
                phId <- fromMaybe 0 . Map.lookup func <$> State.gets ssFuncPhases
                sig <- applyBindingsDeep (Function (TS.toLocal phId (TS.Source func) ret) (map (TS.toLocal phId (TS.Source func)) ps))
                case sig of
                    Function ret' ps' -> do
                        let (tys', templates) = TS.normalizeDescr (map convertBack (ret':ps'))
                        let (ret'', ps'') = case tys' of (r:p) -> (r, p); _ -> (ret, ps)
                        let descr' = FuncDescr l templates ret'' ps''
                        let sig'' = Function (TS.toLocal 0 TS.TopLevel ret'') (map (TS.toLocal 0 TS.TopLevel) ps'')
                        dtraceM $ "Captured Signature for " ++ show func ++ ": " ++ show sig''

                        State.modify $ \s -> s { ssInferred = Map.insert func sig'' (ssInferred s)
                                               , ssTypeSystem = Map.insert func descr' (ssTypeSystem s)
                                               }
                    _ -> return ()
            _ -> return ()
        _ -> return ()
  where
    convertBack :: TypeInfo 'Local -> TypeInfo 'Global
    convertBack (Fix f) = case f of
        TemplateF (FullTemplate t mi) ->
            let mi' = fmap convertBack mi in
            case t of
                TIdInst _ tid'    -> Template tid' mi'
                TIdPoly _ idx h o -> Template (TIdParam idx h o) mi'
                TIdSolver idx h   -> Template (TIdParam idx h TS.TopLevel) mi'
                TIdAnonymous i h  -> Template (TIdAnonymous i h) mi'
                TIdRec idx        -> Template (TIdRec idx) mi'
        _ -> Fix (bimap convertId convertBack f)

    convertId :: TemplateId 'Local -> TemplateId 'Global
    convertId = \case
        TIdInst _ tid'   -> tid'
        TIdPoly _ i h o  -> TIdParam i h o
        TIdSolver i h    -> TIdParam i h TS.TopLevel
        TIdAnonymous i h -> TIdAnonymous i h
        TIdRec i         -> TIdRec i

solveConstraint :: Constraint 'Local -> Solver ()
solveConstraint c = do
    State.gets ssFinalPass >>= \final -> when final $ dtraceM $ "solveConstraint: " ++ show c
    st <- State.get
    let action = case c of
            Equality t1 t2 loc ctx reason -> void $ U.unify t1 t2 reason loc ctx
            Subtype actual expected loc ctx reason -> void $ U.subtype actual expected reason loc ctx
            _ -> return ()

    let initialState = U.UnifyState (ssBindings st) (ssBindingsIndex st) [] (ssTypeSystem st) Set.empty (ssNextId st) (ssFinalPass st)
    let finalUnifyState = execState action initialState

    State.modify $ \s -> s
        { ssBindings = U.usBindings finalUnifyState
        , ssBindingsIndex = U.usBindingsIndex finalUnifyState
        , ssErrors = if ssFinalPass st then ssErrors s ++ U.usErrors finalUnifyState else ssErrors s
        , ssNextId = U.usNextId finalUnifyState
        }

    case c of
        Callable ft atys rt loc ctx csId shouldRefresh ->
            solveCallable ft atys rt GeneralMismatch loc ctx csId shouldRefresh
        HasMember t field mt loc ctx reason ->
            solveMemberAccess t field mt reason loc ctx
        CoordinatedPair trigger actual expected loc ctx mCsId ->
            solveCoordinatedPair trigger actual expected loc ctx mCsId
        _ -> return ()

solveCoordinatedPair :: TypeInfo 'Local -> TypeInfo 'Local -> TypeInfo 'Local -> Maybe (Lexeme Text) -> [Context 'Local] -> Maybe Integer -> Solver ()
solveCoordinatedPair trigger actual expected loc ctx mCsId = do
    st <- State.get
    let initialState = U.UnifyState (ssBindings st) (ssBindingsIndex st) [] (ssTypeSystem st) Set.empty (ssNextId st) (ssFinalPass st)
    let tr = evalState (U.resolveType =<< U.applyBindings trigger) initialState
    let ft = TS.toFlat tr
    dtraceM $ "solveCoordinatedPair trigger=" ++ show tr ++ " quals=" ++ show (TS.ftQuals ft)
    if TS.QNonnull `Set.member` TS.ftQuals ft
        then do
            expected' <- refreshTemplates mCsId expected
            let finalUnifyState = execState (void $ U.unify actual expected' GeneralMismatch loc ctx) initialState
            State.modify $ \s -> s
                { ssBindings = U.usBindings finalUnifyState
                , ssBindingsIndex = U.usBindingsIndex finalUnifyState
                , ssErrors = ssErrors s ++ U.usErrors finalUnifyState
                , ssNextId = U.usNextId finalUnifyState
                }
        else return ()

solveMemberAccess :: TypeInfo 'Local -> Text -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver ()
solveMemberAccess t field mt reason ml ctx = do
    bt <- applyBindings t
    rt <- resolveType bt
    ts <- State.gets ssTypeSystem
    dtraceM $ "solveMemberAccess member=" ++ T.unpack field ++ " base_orig=" ++ show t ++ " base_bt=" ++ show bt ++ " base_rt=" ++ show rt

    let getIdx ty = case unFix ty of
            TemplateF (FT tid (Just idx)) -> dtrace ("getIdx: Template " ++ show tid ++ " has index " ++ show idx) $ Just idx
            TypeRefF _ _ args -> dtrace ("getIdx: TypeRef has args " ++ show args) $ listToMaybe $ mapMaybe getIdx args
            PointerF t' -> getIdx t'
            ArrayF (Just t') _ -> getIdx t'
            QualifiedF _ t' -> getIdx t'
            VarF _ t' -> getIdx t'
            SizedF t' _ -> getIdx t'
            _ -> Nothing
    let mIdx = getIdx t <|> getIdx bt <|> getIdx rt

    case stripAllWrappers rt of
        TypeRef _ (L _ _ tid) args -> do
            let name = TS.templateIdBaseName tid
            dtraceM $ "  Found struct type " ++ show name ++ " mIdx=" ++ show mIdx
            case TS.lookupType name ts of
                Just descr -> do
                    let argMap = Map.fromList (zip (TS.getDescrTemplates descr) args)
                    case TS.lookupMemberType field descr of
                        Just mty -> do
                            let mty' = TS.instantiate 0 (TS.Source name) argMap mty
                            let mty'' = maybe mty' (`Spec.specializeType` mty') mIdx
                            st <- State.get
                            let initialState = U.UnifyState (ssBindings st) (ssBindingsIndex st) [] (ssTypeSystem st) Set.empty (ssNextId st) (ssFinalPass st)
                            let finalUnifyState = execState (U.unify mty'' mt reason ml ctx) initialState
                            State.modify $ \s -> s
                                { ssBindings = U.usBindings finalUnifyState
                                , ssBindingsIndex = U.usBindingsIndex finalUnifyState
                                , ssErrors = ssErrors s ++ U.usErrors finalUnifyState
                                , ssNextId = U.usNextId finalUnifyState
                                }

                            -- TRIGGER STRUCT INVARIANTS
                            let invariants = case descr of
                                    StructDescr _ _ _ invs -> invs
                                    UnionDescr _ _ _ invs  -> invs
                                    _                      -> []
                            triggerInvariants name invariants argMap mIdx "invariants"
                        Nothing -> dtraceM $ "  member " ++ show field ++ " not found in struct " ++ show name
                Nothing -> dtraceM $ "  struct " ++ show name ++ " not found in type system"
        _ -> dtraceM $ "  base type is not a struct: " ++ show rt

bind :: TemplateId 'Local -> Maybe (TypeInfo 'Local) -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver ()
bind tid index ty reason ml ctx = do
    rep <- applyBindingsDeep (Template tid index)
    case rep of
        Template tid' index' -> do
            bindings <- State.gets ssBindings
            let k = FullTemplate tid' index'
            case Map.lookup k bindings of
                Just (existing, _) -> solveConstraint (Equality existing ty ml ctx reason)
                Nothing ->
                    case ty of
                        Template tid'' i'' | tid'' == tid' && i'' == index' -> return ()
                        _ | occurs tid' index' ty -> reportError ml ctx (InfiniteType (T.pack $ show tid') ty)
                        _ -> do
                            let prov = FromContext (ErrorInfo ml ctx (TypeMismatch (Template tid' index') ty reason Nothing) [])
                            State.modify $ \s -> s { ssBindings = Map.insert k (ty, prov) (ssBindings s)
                                                   , ssBindingsIndex = Map.insertWith (++) tid' [k] (ssBindingsIndex s) }
        _ -> solveConstraint (Equality rep ty ml ctx reason)

occurs :: TemplateId p -> Maybe (TypeInfo p) -> TypeInfo p -> Bool
occurs tid index ty = snd $ foldFix alg ty
  where
    alg f = (Fix (fmap fst f), (Fix (fmap fst f) == Template tid index) || any snd f)

applyBindings :: TypeInfo 'Local -> Solver (TypeInfo 'Local)
applyBindings ty = applyBindingsWith Set.empty ty

applyBindingsWith :: Set (FullTemplate 'Local) -> TypeInfo 'Local -> Solver (TypeInfo 'Local)
applyBindingsWith seen ty = case unFix ty of
    TemplateF (FullTemplate tid i) ->
        let k = FullTemplate tid i in
        if Set.member k seen
        then return ty
        else do
            bindings <- State.gets ssBindings
            case Map.lookup k bindings of
                Just (target, _) -> applyBindingsWith (Set.insert k seen) target
                Nothing          -> case i of
                    Nothing -> return ty
                    Just idx -> case Map.lookup (FullTemplate tid Nothing) bindings of
                        Just (baseTarget, _) -> do
                            baseTarget' <- resolveType baseTarget
                            applyBindingsWith (Set.insert k seen) (TS.indexTemplates idx baseTarget')
                        Nothing -> return ty
    _ -> return ty

applyBindingsDeep :: TypeInfo 'Local -> Solver (TypeInfo 'Local)
applyBindingsDeep ty = do
    bindings <- State.gets ssBindings
    return $ resolveDeep bindings Set.empty ty

-- | Deeply resolves a type expression by recursively substituting bound
-- template variables.  Cycle detection via the 'seen' set prevents infinite
-- loops for equi-recursive types.
resolveDeep :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local) -> Set (FullTemplate 'Local) -> TypeInfo 'Local -> TypeInfo 'Local
resolveDeep bindings seen = foldFix $ \case
    TemplateF ft@(FullTemplate tid i)
        | Set.member ft seen -> Template tid i
        | otherwise -> case Map.lookup ft bindings of
            Just (resolved, _) -> resolveDeep bindings (Set.insert ft seen) resolved
            Nothing            -> Template tid i
    f -> Fix f

-- | Substitutes all bound template variables in a type expression (one level).
-- Assumes that binding values are already fully resolved (e.g. after
-- 'resolveBindings').
substBindings :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local) -> TypeInfo 'Local -> TypeInfo 'Local
substBindings bindings = foldFix $ \case
    TemplateF ft@(FullTemplate tid i) ->
        case Map.lookup ft bindings of
            Just (resolved, _) -> resolved
            Nothing            -> Template tid i
    f -> Fix f

resolveType :: TypeInfo 'Local -> Solver (TypeInfo 'Local)
resolveType ty = do
    st <- State.get
    let initialState = U.UnifyState (ssBindings st) (ssBindingsIndex st) [] (ssTypeSystem st) Set.empty (ssNextId st) (ssFinalPass st)
    return $ evalState (U.resolveType ty) initialState

reportError :: Maybe (Lexeme Text) -> [Context 'Local] -> TypeError 'Local -> Solver ()
reportError ml ctx err = do
    isFinal <- State.gets ssFinalPass
    when isFinal $ do
        bindings <- State.gets ssBindings
        let allTypes = case err of
                TypeMismatch expected actual _ _ -> expected : actual : concatMap getContextTypes ctx
                _ -> concatMap getContextTypes ctx
        let expls = concatMap (P.explainType bindings) allTypes
        State.modify $ \s -> s { ssErrors = ssErrors s ++ [ErrorInfo ml ctx err (P.dedupDocs expls)] }
  where
    getContextTypes = \case { InUnification e a _ -> [e, a]; _ -> [] }

solveCallable :: TypeInfo 'Local -> [TypeInfo 'Local] -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Maybe Integer -> Bool -> Solver ()
solveCallable ft atys rt reason ml ctx mCsId shouldRefresh = do
    ft' <- case ft of
        TypeRef TS.FuncRef (L _ _ tid) _ -> do
            let name = templateIdBaseName tid
            inferred <- State.gets ssInferred
            case Map.lookup name inferred of
                Just sig -> applyBindings sig
                Nothing  -> resolveType =<< applyBindings ft
        _ -> resolveType =<< applyBindings ft
    ft'' <- if shouldRefresh then refreshTemplates mCsId ft' else return ft'
    when shouldRefresh $
        case ft of
            TypeRef TS.FuncRef (L _ _ tid) args -> do
                ts <- State.gets ssTypeSystem
                case TS.lookupType (TS.templateIdBaseName tid) ts of
                    Just descr ->
                        let tps = TS.getDescrTemplates descr
                        in when (length tps == length args) $ do
                            tps' <- mapM (refreshTemplates mCsId . TS.toLocal 0 TS.TopLevel . (\t -> Template t Nothing)) tps
                            zipWithM_ (\a t' -> solveConstraint (Equality a t' ml ctx reason)) args tps'

                            let formalTids = tps
                            let substMap = Map.fromList (zip formalTids tps')

                            -- Find any index from the actual arguments (e.g. from indexed structs or literal integers)
                            let mIdx = case mapMaybe (\case { Fix (TemplateF (FullTemplate _ (Just idx))) -> Just idx; Fix (SingletonF s v) -> Just (Singleton s v); _ -> Nothing }) args of
                                            (idx:_) -> Just idx
                                            []      -> Nothing

                            -- TRIGGER FUNCTION LINKS (Global)
                            let name = TS.templateIdBaseName tid
                            ir <- State.gets ssInvariants
                            let fLinks = Map.findWithDefault [] name (irFunctionLinks ir)
                            triggerInvariants name fLinks substMap mIdx "function links"
                    _ -> return ()
            _ -> return ()
    rt'' <- deVoidify ft''
    case stripAllWrappers rt'' of
        Function ret params -> do
            let isVariadic = any isVarArg params
                isSpecial p' = isVarArg p' || TS.isVoid p'
                expectedParams = filter (not . isSpecial) params
                nExpected = length expectedParams
                nActual = length atys
            st <- State.get
            let initialState = U.UnifyState (ssBindings st) (ssBindingsIndex st) [] (ssTypeSystem st) Set.empty (ssNextId st) (ssFinalPass st)
            let action = do
                    void $ U.unify ret rt reason ml ctx
                    if isVariadic then
                        when (nActual < nExpected) $ U.reportError ml ctx (TooFewArgs nExpected nActual)
                        >> mapM_ (uncurry (\a p -> void $ U.subtype a p reason ml ctx)) (zip atys expectedParams)
                    else
                        if nActual < nExpected then U.reportError ml ctx (TooFewArgs nExpected nActual)
                        else if nActual > nExpected then U.reportError ml ctx (TooManyArgs nExpected nActual)
                        else mapM_ (uncurry (\a p -> void $ U.subtype a p reason ml ctx)) (zip atys expectedParams)
            let finalUnifyState = execState action initialState
            State.modify $ \s -> s
                { ssBindings = U.usBindings finalUnifyState
                , ssBindingsIndex = U.usBindingsIndex finalUnifyState
                , ssErrors = ssErrors s ++ U.usErrors finalUnifyState
                , ssNextId = U.usNextId finalUnifyState
                }
        Template tid i -> do
            bindings <- State.gets ssBindings
            case mCsId of
                Just csId -> do
                    let retTid = TIdInst csId (TIdName "ret")
                    case Map.lookup (FullTemplate tid i) bindings of
                        Just (Fix (TS.FunctionF _ _), _) -> return ()
                        _ -> bind tid i (Function (Template retTid Nothing) atys) reason ml ctx
                Nothing -> return ()
        _ -> return ()

deVoidify :: TypeInfo 'Local -> Solver (TypeInfo 'Local)
deVoidify = snd . foldFix alg
  where
    alg f = (Fix (fmap fst f), case f of
        PointerF (orig, _) | TS.isVoid orig -> do
            tp <- nextSolverTemplate Nothing
            let applyWrappers (BuiltinType VoidTy) x = x
                applyWrappers (Const t') x = Const (applyWrappers t' x)
                applyWrappers (Owner t') x = Owner (applyWrappers t' x)
                applyWrappers (Nonnull t') x = Nonnull (applyWrappers t' x)
                applyWrappers (Nullable t') x = Nullable (applyWrappers t' x)
                applyWrappers (Var l t') x = Var l (applyWrappers t' x)
                applyWrappers (Sized t' l) x = Sized (applyWrappers t' x) l
                applyWrappers _ x = x
            return $ Pointer (applyWrappers orig tp)
        _ -> Fix <$> traverse snd f)

refreshTemplates :: Maybe Integer -> TypeInfo 'Local -> Solver (TypeInfo 'Local)
refreshTemplates mCsId ty = State.evalStateT (snd (foldFix alg ty)) Map.empty
  where
    alg f = (Fix (fmap fst f), do
        case f of
            TemplateF (FullTemplate tid i) -> do
                m <- State.get
                let k = FullTemplate tid (fst <$> i)
                case Map.lookup k m of
                    Just t' -> return t'
                    Nothing -> do
                        i' <- maybe (return Nothing) (fmap Just . snd) i
                        case tid of
                            TIdPoly ph _ _ _ -> do
                                active <- lift $ State.gets ssActivePhases
                                if Set.member ph active then return $ Template tid i'
                                else do
                                    t' <- lift $ case mCsId of
                                        Just csId -> return $ Template (TIdInst csId (convertId tid)) i'
                                        Nothing   -> nextSolverTemplate (Just $ templateIdToText tid)
                                    State.modify $ Map.insert k t'
                                    return t'
                            TIdSolver _ _ -> return $ Template tid i'
                            _ -> do
                                t' <- lift $ case mCsId of
                                    Just csId -> return $ Template (TIdInst csId (convertId tid)) i'
                                    Nothing   -> nextSolverTemplate (Just $ templateIdBaseName tid)
                                State.modify $ Map.insert k t'
                                return t'
            _ -> Fix <$> traverse snd f)
    convertId :: TemplateId 'Local -> TemplateId 'Global
    convertId = \case
        TIdInst _ tid'   -> tid'
        TIdPoly _ i h o  -> TIdParam i h o
        TIdSolver i h    -> TIdParam i h TS.TopLevel
        TIdAnonymous i h -> TIdAnonymous i h
        TIdRec i         -> TIdRec i

nextSolverTemplate :: Maybe Text -> Solver (TypeInfo 'Local)
nextSolverTemplate mHint = do
    i <- State.gets ssNextId
    State.modify $ \s -> s { ssNextId = i + 1 }
    return $ Template (TIdSolver i mHint) Nothing

triggerInvariants :: Text -> [Invariant 'Global] -> Map (TemplateId 'Global) (TypeInfo 'Local) -> Maybe (TypeInfo 'Local) -> String -> Solver ()
triggerInvariants name invariants substMap mIdx desc = do
    unless (null invariants) $ do
        dtraceM $ "  Triggering " ++ show (length invariants) ++ " " ++ desc ++ " for " ++ show name
        forM_ invariants $ \inv -> do
            let inv' = TS.mapInvariant (TS.instantiate 0 (TS.Source name) substMap) inv
            -- If we have an index, specialize the invariant.
            -- If not, solve the universal version.
            let inv'' = maybe inv' (`specializeInvariant` inv') mIdx
            solveConstraint (invariantToConstraint inv'' Nothing [] GeneralMismatch)

specializeInvariant :: TypeInfo 'Local -> Invariant 'Local -> Invariant 'Local
specializeInvariant idx = TS.mapInvariant (Spec.specializeType idx)

invariantToConstraint :: Invariant p -> Maybe (Lexeme Text) -> [Context p] -> MismatchReason -> Constraint p
invariantToConstraint inv ml ctx reason = case inv of
    InvCallable f as r        -> Callable f as r ml ctx Nothing True
    InvEquality t1 t2         -> Equality t1 t2 ml ctx reason
    InvSubtype t1 t2          -> Subtype t1 t2 ml ctx reason
    InvCoordinatedPair tr a e -> CoordinatedPair tr a e ml ctx Nothing

constraintToInvariant :: Constraint p -> Maybe (Invariant p)
constraintToInvariant = \case
    Callable f as r _ _ _ _      -> Just $ InvCallable f as r
    Equality t1 t2 _ _ _         -> Just $ InvEquality t1 t2
    Subtype t1 t2 _ _ _          -> Just $ InvSubtype t1 t2
    CoordinatedPair tr a e _ _ _ -> Just $ InvCoordinatedPair tr a e
    _                            -> Nothing

-- end of file
