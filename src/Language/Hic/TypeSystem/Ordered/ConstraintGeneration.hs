{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE KindSignatures      #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
{-# OPTIONS_GHC -Wno-unused-top-binds -Wno-unused-matches -Wno-unused-record-wildcards #-}
module Language.Hic.TypeSystem.Ordered.ConstraintGeneration
    ( Constraint (..)
    , ConstraintGenResult (..)
    , runConstraintGeneration
    ) where

import           Control.Applicative                             ((<|>))
import           Control.Monad                                   (when,
                                                                  zipWithM_)
import           Control.Monad.State.Strict                      (State,
                                                                  execState)
import qualified Control.Monad.State.Strict                      as State
import           Data.Aeson                                      (ToJSON)
import           Data.Fix                                        (Fix (..),
                                                                  foldFix,
                                                                  foldFixM,
                                                                  unFix)
import           Data.List                                       (find, foldl')
import           Data.Map.Strict                                 (Map)
import qualified Data.Map.Strict                                 as Map
import           Data.Maybe                                      (fromJust,
                                                                  fromMaybe,
                                                                  isJust,
                                                                  mapMaybe)
import           Data.Set                                        (Set)
import qualified Data.Set                                        as Set
import           Data.Text                                       (Text)
import qualified Data.Text                                       as T
import qualified Debug.Trace                                     as Debug
import           GHC.Generics                                    (Generic)
import           Language.Cimple                                 (Lexeme (..),
                                                                  Node)
import qualified Language.Cimple                                 as C
import qualified Language.Cimple.Program                         as Program
import           Language.Hic.Core.AstUtils                      (getAlexPosn,
                                                                  getLexeme,
                                                                  parseInteger)
import           Language.Hic.Core.Errors                        (Context (..),
                                                                  MismatchReason (..))
import           Language.Hic.Core.TypeSystem                    (Phase (..),
                                                                  Qualifier (..),
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
                                                                  pattern Function,
                                                                  pattern Nonnull,
                                                                  pattern Nullable,
                                                                  pattern Owner,
                                                                  pattern Pointer,
                                                                  pattern Qualified,
                                                                  pattern Singleton,
                                                                  pattern Sized,
                                                                  pattern Template,
                                                                  pattern TypeRef,
                                                                  pattern Unsupported,
                                                                  pattern Var)
import           Language.Hic.TypeSystem.Core.Base               (getInnerType,
                                                                  isPointerLike,
                                                                  promote,
                                                                  stripAllWrappers,
                                                                  unwrap)
import qualified Language.Hic.TypeSystem.Core.Base               as TS
import           Language.Hic.TypeSystem.Core.Constraints        (Constraint (..))
import           Language.Hic.TypeSystem.Ordered.ArrayUsage      (ArrayFlavor (..),
                                                                  ArrayIdentity (..),
                                                                  ArrayUsageResult (..))
import           Language.Hic.TypeSystem.Ordered.HotspotAnalysis (GlobalAnalysisResult (..))
import           Language.Hic.TypeSystem.Ordered.Nullability     (NullabilityResult (..))

debugging :: Bool
debugging = False

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

data ConstraintGenResult = ConstraintGenResult
    { cgrConstraints :: Map Text [Constraint 'Local] -- FunctionName -> [Constraint]
    , cgrDiagnostics :: [Text]               -- Unhandled nodes or other issues
    , cgrFuncPhases  :: Map Text Integer      -- FunctionName -> PhaseId
    } deriving (Show, Generic)

instance ToJSON ConstraintGenResult

data ExtractionState = ExtractionState
    { esVars        :: [Map Text (TypeInfo 'Local)]    -- Stack of maps for lexical scoping
    , esMacros      :: Map Text ([Text], Node (Lexeme Text))
    , esTypeSystem  :: TypeSystem
    , esContext     :: [Context 'Local]
    , esNextId      :: Int
    , esCallSiteId  :: Integer
    , esPhaseId     :: Integer
    , esFuncPhases  :: Map Text Integer
    , esReturnType  :: Maybe (TypeInfo 'Local)
    , esGlobals     :: Set Text
    , esArrayUsage  :: ArrayUsageResult
    , esNullability :: NullabilityResult
    , esCurrentFunc :: Maybe Text
    , esCurrentPos  :: Maybe C.AlexPosn
    , esFuncConstrs :: Map Text [Constraint 'Local]
    , esDiagnostics :: [Text]
    }

type Extract = State ExtractionState

runConstraintGeneration :: TypeSystem -> ArrayUsageResult -> NullabilityResult -> Program.Program Text -> ConstraintGenResult
runConstraintGeneration ts aur nr program =
    let globals = collectGlobals ts
        initialState = ExtractionState [globals] Map.empty ts [] 0 0 1 Map.empty Nothing (Set.fromList (Map.keys globals)) aur nr Nothing Nothing Map.empty []
        finalState = execState (mapM_ ((\(path, nodes) -> withContext (InFile path) (checkNodes nodes))) (Program.toList program)) initialState
    in ConstraintGenResult (esFuncConstrs finalState) (esDiagnostics finalState) (esFuncPhases finalState)
  where
    checkNodes []           = return ()
    checkNodes (node:nodes) = traverseNode node >> checkNodes nodes

    collectGlobals :: TypeSystem -> Map Text (TypeInfo 'Local)
    collectGlobals = Map.foldlWithKey' toTypeInfo Map.empty
      where
        toTypeInfo acc name = \case
            EnumDescr l mems     -> foldl' (\a -> \case TS.EnumMem ml@(L _ _ tid) -> Map.insert (TS.templateIdBaseName tid) (TS.toLocal 0 TS.TopLevel (TypeRef EnumRef (fmap TIdName l) [])) a; _ -> a) acc mems
            AliasDescr _ _ t     -> Map.insert name (TS.toLocal 0 TS.TopLevel t) acc
            _                    -> acc

withContext :: Context 'Local -> Extract a -> Extract a
withContext c m = do
    State.modify $ \s -> s { esContext = c : esContext s }
    res <- m
    State.modify $ \s -> s { esContext = drop 1 (esContext s) }
    return res

addDiagnostic :: Text -> Extract ()
addDiagnostic msg = State.modify $ \s -> s { esDiagnostics = msg : esDiagnostics s }

addConstraint :: Constraint 'Local -> Extract ()
addConstraint c = do
    dtraceM $ "addConstraint: " ++ show c
    mFunc <- State.gets esCurrentFunc
    case mFunc of
        Just f -> State.modify $ \s -> s { esFuncConstrs = Map.insertWith (flip (++)) f [c] (esFuncConstrs s) }
        Nothing -> return ()

nextTemplate :: Maybe Text -> Extract (TypeInfo 'Local)
nextTemplate mHint = do
    i <- State.gets esNextId
    State.modify $ \s -> s { esNextId = i + 1 }
    let res = Template (TIdSolver i mHint) Nothing
    dtraceM $ "nextTemplate: " ++ show res
    return res

nextPhaseId :: Extract Integer
nextPhaseId = do
    ph <- State.gets esPhaseId
    State.modify $ \s -> s { esPhaseId = ph + 1 }
    return ph

enterScope :: Extract ()
enterScope = do
    dtraceM "enterScope"
    State.modify $ \s -> s { esVars = Map.empty : esVars s }

exitScope :: Extract ()
exitScope = do
    dtraceM "exitScope"
    State.modify $ \s -> s { esVars = drop 1 (esVars s) }

addVar :: Text -> TypeInfo 'Local -> Extract ()
addVar name ty = do
    dtraceM $ "addVar: " ++ T.unpack name ++ " :: " ++ show ty
    State.modify $ \s ->
        case esVars s of
            (m:ms) -> s { esVars = Map.insert name ty m : ms }
            []     -> s { esVars = [Map.singleton name ty] }

lookupVar :: Text -> Extract (TypeInfo 'Local)
lookupVar name = do
    dtraceM $ "lookupVar: " ++ T.unpack name
    vars <- State.gets esVars
    res <- case foldl' (\acc m -> acc <|> Map.lookup name m) Nothing vars of
        Just ty -> do
            mPos <- State.gets esCurrentPos
            mFunc <- State.gets esCurrentFunc
            nr <- State.gets esNullability
            let mFacts = do
                    func <- mFunc
                    Map.lookup func (nrStatementFacts nr)
            let isNonnull = fromMaybe False $ do
                    pos <- mPos
                    factsMap <- mFacts
                    (_, facts) <- Map.lookupLE pos factsMap
                    return $ Set.member name facts

            when (not isNonnull && isJust mPos && isJust mFacts) $ do
                let factsMap = fromJust mFacts
                let pos = fromJust mPos
                let matches = [ (k, k == pos) | k <- Map.keys factsMap ]
                dtraceM $ "lookupVar MISS: " ++ T.unpack name ++ " at " ++ show pos ++ " keys=" ++ show matches

            dtraceM $ "lookupVar " ++ T.unpack name ++ " at " ++ show mPos ++ " in " ++ show mFunc ++ " isNonnull=" ++ show isNonnull
            if isNonnull
                then return $ Nonnull (promoteNonnull ty)
                else return ty
        Nothing -> do
            ts <- State.gets esTypeSystem
            case TS.lookupType name ts of
                Just descr -> instantiateTypeDescr (L (C.AlexPn 0 0 0) C.IdVar (TS.mkId name)) descr
                _ | name `elem` ["__func__", "__FUNCTION__", "__PRETTY_FUNCTION__"] -> return $ Pointer (Const (BuiltinType CharTy))
                _ -> return $ Unsupported $ "undefined variable: " <> name
    dtraceM $ "lookupVar result: " ++ show res
    return res

-- | Promote Nullable to Nonnull in qualifier wrappers, but stop at structural
-- types (Pointer, Array, etc.) to avoid corrupting pointee qualifiers.
promoteNonnull :: TypeInfo p -> TypeInfo p
promoteNonnull (Qualified qs t) = Qualified (Set.insert QNonnull (Set.delete QNullable qs)) (promoteNonnull t)
promoteNonnull (Var l t)        = Var l (promoteNonnull t)
promoteNonnull (Sized t l)      = Sized (promoteNonnull t) l
promoteNonnull t                = t

traverseNode :: Node (Lexeme Text) -> Extract (TypeInfo 'Local)
traverseNode = snd . foldFix alg
  where
    alg f = (Fix (fmap fst f), do
        let nOrig = Fix (fmap fst f)
        case getAlexPosn nOrig of
            Just pos -> State.modify $ \s -> s { esCurrentPos = Just pos }
            Nothing  -> return ()
        case f of
            C.FunctionDefn _ (_, protoAction) (_, bodyAction) -> do
                case unFix nOrig of
                    C.FunctionDefn _ proto body -> do
                        case unFix proto of
                            C.FunctionPrototype ty (L _ _ name) params -> do
                                phId <- nextPhaseId
                                State.modify $ \s -> s { esFuncPhases = Map.insert name phId (esFuncPhases s) }
                                oldFunc <- State.gets esCurrentFunc
                                oldVars <- State.gets esVars
                                oldRt <- State.gets esReturnType
                                ts <- State.gets esTypeSystem
                                case TS.lookupType name ts of
                                    Just (FuncDescr _ _ sigRet sigParams) -> do
                                        rt <- convertToTypeInfo ty
                                        ctx <- State.gets esContext
                                        State.modify $ \s -> s { esCurrentFunc = Just name }
                                        addConstraint $ Equality rt (TS.toLocal phId (TS.Source name) sigRet) Nothing ctx GeneralMismatch
                                        State.modify $ \s -> s { esReturnType = Just rt }
                                        enterScope
                                        mapM_ registerParam params
                                        vars <- State.gets esVars
                                        let getParamType' p = case unFix p of
                                                C.VarDecl _ (L _ _ pName) _ -> case vars of
                                                    (v:_) -> Map.lookup pName v
                                                    []    -> Nothing
                                                C.NonNullParam p' -> getParamType' p'
                                                C.NullableParam p' -> getParamType' p'
                                                _ -> Nothing
                                        let paramTypes = mapMaybe getParamType' params
                                        mapM_ (uncurry (\p sigP -> addConstraint $ Equality p (TS.toLocal phId (TS.Source name) sigP) Nothing ctx GeneralMismatch)) (zip paramTypes sigParams)
                                    _ -> do
                                        let globalScope = case oldVars of
                                                (g:_) -> g
                                                []    -> Map.empty
                                        State.modify $ \s -> s { esCurrentFunc = Just name, esVars = [globalScope] }
                                        enterScope
                                        rt <- convertToTypeInfo ty
                                        State.modify $ \s -> s { esReturnType = Just rt }
                                        mapM_ registerParam params
                                _ <- bodyAction
                                State.modify $ \s -> s { esCurrentFunc = oldFunc, esVars = oldVars, esReturnType = oldRt }
                                return $ BuiltinType VoidTy
                            _ -> sequence_ (fmap snd f) >> return (BuiltinType VoidTy)
                    _ -> sequence_ (fmap snd f) >> return (BuiltinType VoidTy)

            C.IfStmt (condOrig, condAction) (_, thenAction) mElse -> do
                checkExpected (BuiltinType BoolTy) condOrig
                _ <- thenAction
                mapM_ snd mElse
                return $ BuiltinType VoidTy

            C.WhileStmt (condOrig, condAction) (_, bodyAction) -> do
                checkExpected (BuiltinType BoolTy) condOrig
                _ <- bodyAction
                return $ BuiltinType VoidTy

            C.DoWhileStmt (_, bodyAction) (condOrig, condAction) -> do
                _ <- bodyAction
                checkExpected (BuiltinType BoolTy) condOrig
                return $ BuiltinType VoidTy

            C.CompoundStmt stmts -> do
                enterScope
                mapM_ snd stmts
                exitScope
                return $ BuiltinType VoidTy

            C.SwitchStmt (condOrig, condAction) cases -> do
                _ <- inferExpr condOrig
                mapM_ snd cases
                return $ BuiltinType VoidTy

            C.Case (labelOrig, labelAction) (_, stmtAction) -> do
                _ <- inferExpr labelOrig
                _ <- stmtAction
                return $ BuiltinType VoidTy

            C.Default (_, stmtAction) -> do
                _ <- stmtAction
                return $ BuiltinType VoidTy

            C.ForStmt init' cond step body -> do
                enterScope
                _ <- snd init'
                checkExpected (BuiltinType BoolTy) (fst cond)
                _ <- snd step
                _ <- snd body
                exitScope
                return $ BuiltinType VoidTy

            C.Return mExpr -> do
                mRet <- State.gets esReturnType
                case (mRet, mExpr) of
                    (Just ret, Just (exprOrig, exprAction)) -> do
                        checkExpected ret exprOrig
                        return ()
                    _ -> sequence_ (fmap snd mExpr)
                return $ BuiltinType VoidTy

            C.ExprStmt (exprOrig, exprAction) -> do
                _ <- exprAction
                return $ BuiltinType VoidTy

            C.VarDeclStmt decl mInit -> do
                t <- snd decl
                case mInit of
                    Just init' -> checkExpected t (fst init')
                    Nothing    -> return ()
                return t

            C.VarDecl ty (L _ _ name) arrs -> do
                t <- convertToTypeInfo (fst ty) >>= flip addArrays (map fst arrs)
                addVar name t
                return t

            C.AssignExpr (lhsOrig, lhsAction) op (rhsOrig, rhsAction) -> do
                lt <- inferExpr lhsOrig
                rt <- inferExpr rhsOrig
                let reason = if op == C.AopEq then AssignmentMismatch else GeneralMismatch
                ctx <- State.gets esContext
                addConstraint $ Subtype rt lt (getLexeme lhsOrig) ctx reason
                return lt

            C.BinaryExpr (lhsOrig, lhsAction) _ (rhsOrig, rhsAction) -> do
                t <- inferExpr nOrig
                return t

            C.UnaryExpr _ (eOrig, eAction) -> do
                t <- inferExpr nOrig
                return t

            C.ArrayAccess (baseOrig, baseAction) (idxOrig, idxAction) -> do
                t <- inferExpr nOrig
                return t

            C.MemberAccess (objOrig, objAction) _ -> do
                t <- inferExpr nOrig
                return t

            C.PointerAccess (objOrig, objAction) _ -> do
                t <- inferExpr nOrig
                return t

            C.TernaryExpr (cOrig, cAction) (tOrig, tAction) (eOrig, eAction) -> do
                ty <- inferExpr nOrig
                return ty

            C.FunctionCall fun args -> inferExpr nOrig

            C.StaticAssert (eOrig, eAction) _ -> do
                return $ BuiltinType VoidTy

            C.CallbackDecl (L p1 t1 ty) (L p2 t2 name) -> do
                ts <- State.gets esTypeSystem
                case TS.lookupType ty ts of
                    Just (FuncDescr _ _ _ _) -> do
                        addVar name (Pointer (TypeRef TS.FuncRef (L p1 t1 (TS.mkId ty)) []))
                    _ -> return ()
                return $ BuiltinType VoidTy

            C.PreprocDefineMacro (L _ _ name) params (bodyOrig, bodyAction) -> do
                let getParamName p = case unFix p of
                        C.MacroParam (L _ _ n) -> Just n
                        _                      -> Nothing
                let paramNames = mapMaybe getParamName (map fst params)
                State.modify $ \s -> s { esMacros = Map.insert name (paramNames, bodyOrig) (esMacros s) }
                return $ BuiltinType VoidTy

            C.AttrPrintf _ _ (_, nAction) -> nAction >> return (BuiltinType VoidTy)

            C.PreprocDefine l -> do
                State.modify $ \s -> s { esMacros = Map.insert (C.lexemeText l) ([], Fix (C.LiteralExpr C.Int (L (C.AlexPn 0 0 0) C.IdVar "1"))) (esMacros s) }
                return $ BuiltinType VoidTy

            C.PreprocDefineConst (L _ _ name) (bodyOrig, _) -> do
                State.modify $ \s -> s { esMacros = Map.insert name ([], bodyOrig) (esMacros s) }
                return $ BuiltinType VoidTy

            C.PreprocUndef (L _ _ name) -> do
                State.modify $ \s -> s { esMacros = Map.delete name (esMacros s) }
                return $ BuiltinType VoidTy

            C.ConstDecl ty (L _ _ name) -> do
                t <- convertToTypeInfo (fst ty)
                addVar name t
                return t

            C.ConstDefn _ ty (L _ _ name) _ -> do
                t <- convertToTypeInfo (fst ty)
                addVar name t
                return t

            C.VLA ty (L _ _ name) (sizeOrig, sizeAction) -> do
                t <- convertToTypeInfo (fst ty)
                _ <- sizeAction
                addVar name (Array (Just t) [])
                return t

            C.Group nodes -> mapM_ snd nodes >> return (BuiltinType VoidTy)
            C.ExternC nodes -> mapM_ snd nodes >> return (BuiltinType VoidTy)

            _ -> do
                sequence_ (fmap snd f)
                inferExpr nOrig)

registerParam :: Node (Lexeme Text) -> Extract ()
registerParam = snd . foldFix alg
  where
    alg f = (Fix (fmap fst f), case f of
        C.VarDecl ty (L _ _ name) arrs -> do
            t <- convertToTypeInfo (fst ty) >>= flip addArrays (map fst arrs)
            addVar name t
        C.NonNullParam (_, action) -> action
        C.NullableParam (_, action) -> action
        _ -> sequence_ (fmap snd f))

addArrays :: TypeInfo 'Local -> [Node (Lexeme Text)] -> Extract (TypeInfo 'Local)
addArrays = foldM add
  where
    add ty (Fix node) = case node of
        C.DeclSpecArray _ (Just n) -> case unFix n of
            C.LiteralExpr C.Int l -> return $ Array (Just ty) [Singleton S32Ty (read (T.unpack (C.lexemeText l)))]
            _ -> do
                dt <- inferExpr n
                return $ Array (Just ty) [dt]
        C.DeclSpecArray _ Nothing -> return $ Array (Just ty) []
        _ -> do
            dt <- inferExpr (Fix node)
            return $ Array (Just ty) [dt]

    foldM _ z [] = return z
    foldM f z (x:xs) = do
        z' <- f z x
        foldM f z' xs

checkExpected :: TypeInfo 'Local -> Node (Lexeme Text) -> Extract ()
checkExpected expected expr = case unFix expr of
    C.InitialiserList exprs -> processInitializerList expected exprs
    _ -> do
        actual <- inferExpr expr
        case (expected, actual) of
            (BuiltinType BoolTy, t) | isPointerLike t -> return ()
            _ -> do
                ctx <- State.gets esContext
                addConstraint $ Subtype actual expected (getLexeme expr) ctx GeneralMismatch
        return ()

processInitializerList :: TypeInfo 'Local -> [Node (Lexeme Text)] -> Extract ()
processInitializerList target exprs = do
    rt <- resolveType target
    case rt of
        TypeRef StructRef l args -> do
            let name = TS.templateIdBaseName (C.lexemeText l)
            ts <- State.gets esTypeSystem
            case TS.lookupType name ts of
                Just (TS.StructDescr dl _ members _) -> do
                    -- Simple zip for now, matching the test case
                    let memberTypes = map (TS.toLocal 0 TS.TopLevel . snd) members
                    zipWithM_ checkExpected memberTypes exprs
                _ -> return ()
        TypeRef UnionRef l args -> do
            let name = TS.templateIdBaseName (C.lexemeText l)
            ts <- State.gets esTypeSystem
            case TS.lookupType name ts of
                Just (TS.UnionDescr _ _ members _) ->
                    case (members, exprs) of
                        (((_, t):_), (e:_)) -> checkExpected (TS.toLocal 0 TS.TopLevel t) e
                        _                   -> return ()
                _ -> return ()
        Array (Just et) _ ->
            mapM_ (checkExpected et) exprs
        _ -> return ()

deVoidify :: TypeInfo 'Local -> Extract (TypeInfo 'Local)
deVoidify = foldFixM $ \case
    BuiltinTypeF VoidTy -> nextTemplate Nothing
    f                   -> return $ Fix f

instantiateTypeDescr :: Lexeme (TemplateId 'Local) -> TypeDescr 'Global -> Extract (TypeInfo 'Local)
instantiateTypeDescr _ descr = do
    let tps = TS.getDescrTemplates descr
    args <- mapM (nextTemplate . TS.templateIdHint) tps
    case descr of
      AliasDescr _ _ target -> do
          let m = Map.fromList (zip (TS.getDescrTemplates descr) args)
          resolveType $ TS.instantiate 0 TS.TopLevel m target
      IntDescr _ std -> return $ BuiltinType std
      StructDescr l _ _ _ -> return $ TypeRef StructRef (fmap TS.mkId l) args
      UnionDescr l _ _ _  -> return $ TypeRef UnionRef (fmap TS.mkId l) args
      EnumDescr l _       -> return $ TypeRef EnumRef (fmap TS.mkId l) args
      FuncDescr l _ _ _   -> return $ TypeRef FuncRef (fmap TS.mkId l) args

convertToTypeInfo :: Node (Lexeme Text) -> Extract (TypeInfo 'Local)
convertToTypeInfo = foldFixM $ \case
    C.TyStd l -> return $ TS.toLocal 0 TS.TopLevel (TS.builtin l)
    C.TyPointer it -> deVoidify (Pointer it)
    C.TyConst it -> return $ Const it
    C.TyNonnull it -> return $ Nonnull it
    C.TyNullable it -> return $ Nullable it
    C.TyOwner it -> return $ Owner it
    C.TyBitwise it -> return it
    C.TyForce _ -> nextTemplate Nothing
    C.TyStruct (L p t name) -> do
        ts <- State.gets esTypeSystem
        case TS.lookupType name ts of
            Just descr -> instantiateTypeDescr (L p t (TS.mkId name)) descr
            Nothing    -> return $ TypeRef StructRef (L p t (TS.mkId name)) []
    C.TyUnion (L p t name) -> do
        ts <- State.gets esTypeSystem
        case TS.lookupType name ts of
            Just descr -> instantiateTypeDescr (L p t (TS.mkId name)) descr
            Nothing    -> return $ TypeRef UnionRef (L p t (TS.mkId name)) []
    C.TyFunc (L p t name) -> do
        ts <- State.gets esTypeSystem
        case TS.lookupType name ts of
            Just descr -> instantiateTypeDescr (L p t (TS.mkId name)) descr
            Nothing    -> return $ TypeRef TS.FuncRef (L p t (TS.mkId name)) []
    C.TyUserDefined l@(L p t name) -> do
        ts <- State.gets esTypeSystem
        case TS.lookupType name ts of
            Just descr -> instantiateTypeDescr (L p t (TS.mkId name)) descr
            Nothing -> case TS.builtin l of
                TypeRef TS.UnresolvedRef (L p' t' _) _ -> return $ TypeRef TS.UnresolvedRef (L p' t' (TS.mkId name)) []
                b -> return $ TS.toLocal 0 TS.TopLevel b
    C.Commented _ it -> return it
    _ -> return $ BuiltinType VoidTy

resolveType :: TypeInfo 'Local -> Extract (TypeInfo 'Local)
resolveType ty = do
    ts <- State.gets esTypeSystem
    return $ TS.resolveRefLocal ts ty

inferExpr :: Node (Lexeme Text) -> Extract (TypeInfo 'Local)
inferExpr (Fix node') = do
    let decay = \case
            Singleton b _ -> BuiltinType b
            t             -> t
    case node' of
        C.LiteralExpr C.Int (L _ _ val) ->
            case parseInteger val of
                Just n  -> return $ Singleton S32Ty n
                Nothing -> return $ BuiltinType S32Ty
        C.LiteralExpr C.Char _ -> return $ BuiltinType CharTy
        C.LiteralExpr C.Float _ -> return $ BuiltinType F32Ty
        C.LiteralExpr C.Bool _ -> return $ BuiltinType BoolTy
        C.LiteralExpr C.String _ -> return $ Pointer (BuiltinType CharTy)
        C.LiteralExpr C.ConstId (L _ _ "nullptr") -> return $ BuiltinType NullPtrTy
        C.LiteralExpr C.ConstId (L _ _ "__FILE__") -> return $ Pointer (Const (BuiltinType CharTy))
        C.LiteralExpr C.ConstId (L _ _ "__func__") -> return $ Pointer (Const (BuiltinType CharTy))
        C.LiteralExpr C.ConstId (L _ _ "__LINE__") -> return $ BuiltinType S32Ty
        C.LiteralExpr _ (L _ _ name) -> lookupVar name

        C.VarExpr (L _ _ name) -> lookupVar name

        C.UnaryExpr op e -> do
            case op of
                C.UopDeref   -> do
                    t <- inferExpr e
                    let inner = getInnerType t
                    mt <- if isPointerLike t && not (isVoid inner)
                          then return inner
                          else nextTemplate Nothing
                    ctx <- State.gets esContext
                    addConstraint $ Subtype t (Pointer mt) (getLexeme e) ctx GeneralMismatch
                    return mt
                C.UopAddress -> Pointer <$> inferExpr e
                C.UopNot     -> inferExpr e >> return (BuiltinType BoolTy)
                C.UopNeg     -> inferExpr e
                C.UopMinus   -> inferExpr e
                C.UopIncr    -> inferExpr e
                C.UopDecr    -> inferExpr e

        C.BinaryExpr lhs op rhs -> do
            ctx <- State.gets esContext
            case op of
                C.BopEq -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    addConstraint (Equality (decay lt) (decay rt) (getLexeme lhs) ctx GeneralMismatch)
                    return (BuiltinType BoolTy)
                C.BopNe -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    addConstraint (Equality (decay lt) (decay rt) (getLexeme lhs) ctx GeneralMismatch)
                    return (BuiltinType BoolTy)
                C.BopAnd -> checkExpected (BuiltinType BoolTy) lhs >> checkExpected (BuiltinType BoolTy) rhs >> return (BuiltinType BoolTy)
                C.BopOr -> checkExpected (BuiltinType BoolTy) lhs >> checkExpected (BuiltinType BoolTy) rhs >> return (BuiltinType BoolTy)
                C.BopPlus -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    if isPointerLike lt
                        then checkExpected (BuiltinType S32Ty) rhs >> return lt
                        else if isPointerLike rt
                        then checkExpected (BuiltinType S32Ty) lhs >> return rt
                        else return $ promote lt rt
                C.BopMinus -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    if isPointerLike lt && isPointerLike rt
                        then return (BuiltinType SizeTy)
                        else if isPointerLike lt
                        then checkExpected (BuiltinType S32Ty) rhs >> return lt
                        else return $ promote lt rt
                C.BopMul -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    return $ promote lt rt
                C.BopDiv -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    return $ promote lt rt
                C.BopMod -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    return $ promote lt rt
                C.BopBitAnd -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    return $ promote lt rt
                C.BopBitOr -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    return $ promote lt rt
                C.BopBitXor -> do
                    lt <- inferExpr lhs
                    rt <- inferExpr rhs
                    return $ promote lt rt
                C.BopLsh -> do
                    lt <- inferExpr lhs
                    return lt
                C.BopRsh -> do
                    lt <- inferExpr lhs
                    return lt
                C.BopLt -> inferExpr lhs >> inferExpr rhs >> return (BuiltinType BoolTy)
                C.BopLe -> inferExpr lhs >> inferExpr rhs >> return (BuiltinType BoolTy)
                C.BopGt -> inferExpr lhs >> inferExpr rhs >> return (BuiltinType BoolTy)
                C.BopGe -> inferExpr lhs >> inferExpr rhs >> return (BuiltinType BoolTy)

        C.ArrayAccess base idx -> do
            bt <- inferExpr base
            rt <- resolveType bt
            it <- inferExpr idx
            mId <- getArrayIdentity base
            aur <- State.gets esArrayUsage
            let flavor = case mId of
                    Just ident -> Map.findWithDefault FlavorHomogeneous ident (aurFlavors aur)
                    Nothing    -> FlavorHomogeneous

            inner <- case unwrap rt of
                Array (Just et) _ -> return et
                Pointer et        -> return et
                _ -> do
                    et <- nextTemplate Nothing
                    ctx <- State.gets esContext
                    addConstraint $ Subtype rt (Array (Just et) []) (getLexeme base) ctx GeneralMismatch
                    return et

            let isLiteral = \case { Fix (SingletonF _ _) -> True; _ -> False }
            case flavor of
                FlavorHeterogeneous -> do
                    inner' <- resolveType inner
                    return $ TS.indexTemplates it inner'
                FlavorMixed | isLiteral (stripAllWrappers it) -> do
                    inner' <- resolveType inner
                    return $ TS.indexTemplates it inner'
                _                   -> return inner

        C.PointerAccess obj field -> do
            ot <- inferExpr obj
            mt <- nextTemplate (Just $ C.lexemeText field)
            ctx <- State.gets esContext
            addConstraint $ HasMember (stripAllWrappers ot) (C.lexemeText field) mt (getLexeme obj) ctx GeneralMismatch
            return mt

        C.MemberAccess obj field -> do
            ot <- inferExpr obj
            mt <- nextTemplate (Just $ C.lexemeText field)
            ctx <- State.gets esContext
            addConstraint $ HasMember ot (C.lexemeText field) mt (getLexeme obj) ctx GeneralMismatch
            return mt

        C.FunctionCall fun args -> do
            ft <- inferExpr fun
            atys <- concat <$> mapM (\argOrig -> do
                ty <- inferExpr argOrig
                case (unFix argOrig, ty) of
                    (C.VarExpr (L _ _ "__VA_ARGS__"), Array Nothing ts) -> return ts
                    (C.LiteralExpr C.ConstId (L _ _ "__VA_ARGS__"), Array Nothing ts) -> return ts
                    _ -> return [ty]) args
            rt <- nextTemplate (Just "ret")
            ctx <- State.gets esContext
            csId <- State.gets esCallSiteId
            State.modify $ \s -> s { esCallSiteId = csId + 1 }
            ts <- State.gets esTypeSystem
            let resolvedFt = TS.resolveRefLocal ts ft
            let formalParams = fromMaybe [] (TS.getTypeParams ts resolvedFt)
            dtraceM $ "FunctionCall: fun=" ++ show fun ++ " formalParams=" ++ show formalParams ++ " atys=" ++ show atys
            let isVoidLike t = isVoid t || case unwrap t of Template _ _ -> True; _ -> False

            let interests = zip3 [(0 :: Int)..] formalParams atys
                isCallback p = isJust (TS.getTypeParams ts p)
                isData p = isPointerLike p && not (isCallback p)
                callbacks = [ (i, p, a) | (i, p, a) <- interests, isCallback p ]
                datas     = [ (i, p, a) | (i, p, a) <- interests, isData p ]

            dtraceM $ "FunctionCall: callbacks=" ++ show (map (\(i,_,_) -> i) callbacks) ++ " datas=" ++ show (map (\(i,_,_) -> i) datas)

            mapM_ (\(i_cb, p_cb, a_cb) -> do
                let cbParams = fromMaybe [] (TS.getTypeParams ts p_cb)
                let voidCbParams = [ stripAllWrappers p | p <- cbParams, isVoidLike (stripAllWrappers p) ]
                dtraceM $ "FunctionCall: callback i=" ++ show i_cb ++ " voidCbParams=" ++ show voidCbParams
                when (not (null voidCbParams)) $ do
                    let adjacentBefore = find (\(i, _, _) -> i == i_cb - 1) datas
                    let adjacentAfter  = find (\(i, _, _) -> i == i_cb + 1) datas
                    let mTarget = adjacentAfter <|> adjacentBefore <|>
                                  (case datas of [d] -> Just d; _ -> Nothing)
                    dtraceM $ "FunctionCall: callback i=" ++ show i_cb ++ " mTarget=" ++ show (fmap (\(i,_,_) -> i) mTarget)
                    case mTarget of
                        Just (_, p_data, a_data) -> do
                            let targetInner = getInnerType p_data
                            let hasNonGenericMatch = any (\p -> not (isVoidLike (stripAllWrappers p)) &&
                                                               (stripAllWrappers p == stripAllWrappers targetInner)) cbParams
                            when (not hasNonGenericMatch) $
                                mapM_ (\dvp -> do
                                    dtraceM $ "FunctionCall: emit CoordinatedPair for i=" ++ show i_cb ++ " data=" ++ show a_data ++ " dvp=" ++ show dvp
                                    addConstraint $ CoordinatedPair a_cb (getInnerType a_data) dvp (getLexeme fun) ctx (Just csId)
                                    ) voidCbParams
                        Nothing -> return ()
                ) callbacks
            mName <- case unFix fun of
                C.VarExpr (L _ _ name)               -> return $ Just name
                C.LiteralExpr C.ConstId (L _ _ name) -> return $ Just name
                _                                    -> return Nothing
            case mName of
                Just name -> do
                    macros <- State.gets esMacros
                    case Map.lookup name macros of
                        Just (params, body) -> do
                            oldVars <- State.gets esVars
                            let subVars = Map.fromList $ zip params atys
                            let vaArgs = drop (length params) atys
                            let subVars' = case vaArgs of
                                                [] -> subVars
                                                _  -> Map.insert "__VA_ARGS__" (Array Nothing vaArgs) subVars
                            State.modify $ \s -> s { esVars = subVars' : oldVars }
                            res <- withContext (InMacro name) $ inferExpr body
                            _ <- withContext (InMacro name) $ traverseNode body
                            State.modify $ \s -> s { esVars = oldVars }
                            return res
                        Nothing -> fallback ft atys rt ctx csId
                Nothing -> fallback ft atys rt ctx csId
          where
            fallback ft atys rt ctx csId = do
                addConstraint $ Callable ft atys rt (getLexeme fun) ctx (Just csId) True
                return rt

        C.TernaryExpr cond thenE elseE -> do
            checkExpected (BuiltinType BoolTy) cond
            tt <- inferExpr thenE
            et <- inferExpr elseE
            ctx <- State.gets esContext
            addConstraint $ Equality (decay tt) (decay et) (getLexeme thenE) ctx GeneralMismatch
            return tt

        C.AssignExpr lhs _ rhs -> inferExpr lhs

        C.ParenExpr e -> traverseNode e
        C.CastExpr ty e -> do
            et <- inferExpr e
            t <- convertToTypeInfo ty
            let hasForce = foldFix (\case { C.TyForce _ -> True; f -> any id f }) ty
            if hasForce
                then return t
                else do
                    ctx <- State.gets esContext
                    addConstraint $ Subtype et t (getLexeme e) ctx CastMismatch
                    return t
        C.CompoundLiteral ty e -> do
            t <- convertToTypeInfo ty
            checkExpected t e
            return t

        C.SizeofExpr _ -> return $ BuiltinType SizeTy
        C.SizeofType _ -> return $ BuiltinType SizeTy

        _ -> do
            let name = T.pack $ take 40 $ show node'
            addDiagnostic $ "unhandled expression: " <> name
            return $ Unsupported name

getArrayIdentity :: Node (Lexeme Text) -> Extract (Maybe ArrayIdentity)
getArrayIdentity (Fix node) = case node of
    C.VarExpr (L _ _ name) -> do
        mFunc <- State.gets esCurrentFunc
        return $ Just $ case mFunc of
            Just f  -> LocalArray f name
            Nothing -> GlobalArray name
    C.PointerAccess obj (L _ _ field) -> do
        mObjTy <- inferExpr obj
        case stripAllWrappers mObjTy of
            TypeRef _ (L _ _ tid) _ ->
                let name = TS.templateIdBaseName tid in
                return $ Just $ MemberArray name field
            _ -> return Nothing
    C.MemberAccess obj (L _ _ field) -> do
        mObjTy <- inferExpr obj
        case stripAllWrappers mObjTy of
            TypeRef _ (L _ _ tid) _ ->
                let name = TS.templateIdBaseName tid in
                return $ Just $ MemberArray name field
            _ -> return Nothing
    _ -> return Nothing
