{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE KindSignatures    #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
{-# LANGUAGE TupleSections     #-}
module Language.Hic.TypeSystem.Standard.Constraints
    ( Constraint (..)
    , extractConstraints
    ) where

import           Control.Arrow                           (second)
import           Control.Monad                           (forM, forM_, when)
import           Control.Monad.State.Strict              (State, execState)
import qualified Control.Monad.State.Strict              as State
import           Data.Fix                                (Fix (..), foldFixM,
                                                          unFix)
import           Data.Map.Strict                         (Map)
import qualified Data.Map.Strict                         as Map
import           Data.Maybe                              (mapMaybe)
import           Data.Set                                (Set)
import qualified Data.Set                                as Set
import           Data.Text                               (Text)
import qualified Data.Text                               as T
import qualified Debug.Trace                             as Debug
import           Language.Cimple                         (AssignOp (..),
                                                          BinaryOp (..),
                                                          Lexeme (..), Node,
                                                          UnaryOp (..))
import qualified Language.Cimple                         as C
import           Language.Hic.Core.AstUtils              (getLexeme,
                                                          isExpression)
import           Language.Hic.Core.CFG                   (CFG, CFGNode (..),
                                                          buildCFG)
import           Language.Hic.Core.Errors                (Context (..),
                                                          ErrorInfo (..),
                                                          MismatchReason (..),
                                                          TypeError (..))

import           Language.Hic.Core.TypeSystem            (FullTemplate,
                                                          Origin (..),
                                                          Phase (..),
                                                          StdType (..),
                                                          TemplateId (..),
                                                          TypeDescr (..),
                                                          TypeInfo,
                                                          TypeInfoF (..),
                                                          TypeRef (..),
                                                          TypeSystem, isVoid,
                                                          pattern Array,
                                                          pattern BuiltinType,
                                                          pattern Const,
                                                          pattern ExternalType,
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
                                                          pattern Unconstrained,
                                                          pattern Unsupported,
                                                          pattern Var,
                                                          pattern VarArg,
                                                          templateIdBaseName)
import           Language.Hic.TypeSystem.Core.Base       (builtin,
                                                          isPointerLike,
                                                          lookupType, unwrap)
import qualified Language.Hic.TypeSystem.Core.Base       as TS
import qualified Language.Hic.TypeSystem.Core.Base       as TypeSystem
import           Language.Hic.TypeSystem.Core.BuiltinMap (builtinMap)

debugging :: Bool
debugging = False

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

-- | A type constraint represents a relationship that must hold between types.
data Constraint (p :: Phase)
    = Equality (TypeInfo p) (TypeInfo p) (Maybe (Lexeme Text)) [Context p] MismatchReason
    | Subtype (TypeInfo p) (TypeInfo p) (Maybe (Lexeme Text)) [Context p] MismatchReason
    | Callable (TypeInfo p) [TypeInfo p] (Maybe (Lexeme Text)) [Context p] (Maybe Integer) Bool
    | HasMember (TypeInfo p) Text (TypeInfo p) (Maybe (Lexeme Text)) [Context p] MismatchReason
    | CoordinatedPair (TypeInfo p) (TypeInfo p) (TypeInfo p) (Maybe (Lexeme Text)) [Context p]
    -- ^ If the first TypeInfo (the trigger) is Nonnull, then the second (actual) must be a subtype of the third (expected).
    deriving (Show, Eq, Ord)

data ExtractionState = ExtractionState
    { esConstraints :: [Constraint 'Local]
    , esVars        :: Map Text (TypeInfo 'Local)
    , esMacros      :: Map Text ([Text], Node (Lexeme Text))
    , esTypeSystem  :: TypeSystem
    , esContext     :: [Context 'Local]
    , esNextId      :: Int
    , esCallSiteId  :: Integer
    , esCurrentCFG  :: Maybe (CFG Text)
    , esSeenNodes   :: Set Int
    , esReturnType  :: Maybe (TypeInfo 'Local)
    , esGlobals     :: Set Text
    , esErrors      :: [ErrorInfo 'Local]
    }

type Extract = State ExtractionState

addConstraint :: Constraint 'Local -> Extract ()
addConstraint c = do
    dtraceM $ "addConstraint: " ++ show c
    State.modify $ \s -> s { esConstraints = esConstraints s ++ [c] }

reportError :: Maybe (Lexeme Text) -> TypeError 'Local -> Extract ()
reportError ml err = do
    ctx <- State.gets esContext
    State.modify $ \s -> s { esErrors = esErrors s ++ [ErrorInfo ml ctx err []] }

withContext :: Context 'Local -> Extract a -> Extract a
withContext c m = do
    State.modify $ \s -> s { esContext = c : esContext s }
    res <- m
    State.modify $ \s -> s { esContext = drop 1 (esContext s) }
    return res

nextTemplate :: Maybe Text -> Extract (TypeInfo 'Local)
nextTemplate mHint = nextTemplateIdx mHint Nothing

nextTemplateIdx :: Maybe Text -> Maybe (TypeInfo 'Local) -> Extract (TypeInfo 'Local)
nextTemplateIdx mHint idx = do
    i <- State.gets esNextId
    State.modify $ \s -> s { esNextId = i + 1 }
    return $ Template (TIdSolver i mHint) idx

nextTemplateQual :: Text -> Extract (TypeInfo 'Local)
nextTemplateQual qual = nextTemplate (Just qual)

extractConstraints :: TypeSystem -> FilePath -> Node (Lexeme Text) -> Int -> Integer -> ([Constraint 'Local], [ErrorInfo 'Local], Int, Integer)
extractConstraints ts path node startId startCallSiteId =
    let s = execState (collectDefs node >> withContext (InFile path) (checkNode node)) initialState
    in (esConstraints s, esErrors s, esNextId s, esCallSiteId s)
  where
    initialState = ExtractionState [] builtinMap Map.empty ts [] startId startCallSiteId Nothing Set.empty Nothing (Set.fromList (Map.keys builtinMap)) []

    insertType l descr = do
        ts' <- State.gets esTypeSystem
        let nameText = C.lexemeText l
        let existing = Map.lookup nameText ts'
        let shouldOverwrite = case (descr, existing) of
                (StructDescr _ _ mems _, Just (StructDescr _ _ existingMems _)) ->
                    null existingMems && not (null mems)
                (UnionDescr _ _ mems _, Just (UnionDescr _ _ existingMems _)) ->
                    null existingMems && not (null mems)
                (_, Just _) -> False -- Don't overwrite existing definitions with anything else for now
                _ -> True
        if shouldOverwrite
            then do
                let resolved = case descr of
                        StructDescr dcl tps mems invs -> StructDescr dcl tps (map (second (TypeSystem.resolveRef ts')) mems) invs
                        UnionDescr dcl tps mems invs -> UnionDescr dcl tps (map (second (TypeSystem.resolveRef ts')) mems) invs
                        FuncDescr dcl tps ret params -> FuncDescr dcl tps (TypeSystem.resolveRef ts' ret) (map (TypeSystem.resolveRef ts') params)
                        AliasDescr dcl tps ty' -> AliasDescr dcl tps (TypeSystem.resolveRef ts' ty')
                        t -> t
                -- Re-collect templates after resolution
                let finalDescr = case resolved of
                        StructDescr dcl _ mems invs -> StructDescr dcl (TypeSystem.collectTemplates (map snd mems)) mems invs
                        UnionDescr dcl _ mems invs -> UnionDescr dcl (TypeSystem.collectTemplates (map snd mems)) mems invs
                        FuncDescr dcl _ ret params -> FuncDescr dcl (TypeSystem.collectTemplates (ret:params)) ret params
                        AliasDescr dcl _ ty' -> AliasDescr dcl (TypeSystem.getTemplates ty') ty'
                        t -> t
                State.modify $ \s -> s { esTypeSystem = Map.insert nameText finalDescr (esTypeSystem s) }
            else return ()

    resolveTypeInfo :: TypeInfo 'Local -> Extract (TypeInfo 'Local)
    resolveTypeInfo t = do
        ts' <- State.gets esTypeSystem
        case t of
            TypeRef _ l _ ->
                let name = templateIdBaseName (C.lexemeText l) in
                case Map.lookup name ts' of
                    Just (AliasDescr _ _ t') -> resolveTypeInfo (TS.toLocal 0 TopLevel t')
                    _                        -> return t
            Var _ t' -> resolveTypeInfo t'
            _ -> return t

    addCoordinatedPair :: TypeInfo 'Local -> TypeInfo 'Local -> Node (Lexeme Text) -> Extract ()
    addCoordinatedPair ct ot cb = do
        ctx <- State.gets esContext
        -- We assume the callback's first parameter is the object
        let unwrapFunction = \case
                Nonnull t  -> unwrapFunction t
                Nullable t -> unwrapFunction t
                Pointer t  -> unwrapFunction t
                t          -> t
        let connectTemplates (expected:params) = do
                addConstraint $ CoordinatedPair ct ot expected (getLexeme cb) ctx
                let tps1 = TypeSystem.getTemplateVars expected
                forM_ params $ \p -> do
                    let tpsP = TypeSystem.getTemplateVars p
                    forM_ (zip tps1 tpsP) $ \(FullTemplate t1 i1, FullTemplate t2 i2) ->
                        addConstraint $ Equality (Template t1 i1) (Template t2 i2) (getLexeme cb) ctx GeneralMismatch
            connectTemplates [] = return ()
        case unwrapFunction ct of
            TypeRef TS.FuncRef l _ -> do
                let cbName = TS.templateIdBaseName (C.lexemeText l)
                ts' <- State.gets esTypeSystem
                case Map.lookup cbName ts' of
                    Just (TS.FuncDescr _ _ _ params) -> connectTemplates (map (TS.toLocal 0 TopLevel) params)
                    _                                -> return ()
            Function _ params -> connectTemplates params
            _ -> return ()

    collectMember (Fix node') = case node' of
        C.MemberDecl typeNode (Just name) -> do
            t <- convertToTypeInfo Nothing typeNode
            return [(name, t)]
        C.MemberDecl (Fix (C.VarDecl ty (L _ _ name) arrs)) _ -> do
            t <- convertToTypeInfo Nothing ty >>= flip addArrays arrs
            return [(L (C.AlexPn 0 0 0) C.IdVar name, t)]
        C.Commented _ n -> collectMember n
        C.Group nodes -> concat <$> mapM collectMember nodes
        _ -> return []

    getParamName (Fix (C.MacroParam (L _ _ n))) = Just n
    getParamName _                              = Nothing

    getParamType f@(Fix node') = case node' of
        C.VarDecl ty _ _    -> ty
        C.CallbackDecl ty _ -> Fix (C.TyFunc ty)
        _                   -> f

    collectDefs (Fix node') = case node' of
        C.PreprocDefineMacro (L _ _ name) params body -> do
            let paramNames = mapMaybe getParamName params
            dtraceM $ "collectDefs: collected macro " ++ T.unpack name
            State.modify $ \s -> s { esMacros = Map.insert name (paramNames, body) (esMacros s) }
        C.PreprocDefineConst (L _ _ name) body -> do
            State.modify $ \s -> s { esMacros = Map.insert name ([], body) (esMacros s) }
        C.Typedef ty l _ -> do
            t <- convertToTypeInfo Nothing ty
            let tg = TS.toGlobal t
            insertType l (AliasDescr l (TypeSystem.getTemplates tg) tg)
            case unFix ty of
                C.Struct _ members -> do
                    mTypes <- concat <$> mapM collectMember members
                    let mTypesG = map (second TS.toGlobal) mTypes
                    insertType l (StructDescr l (TypeSystem.collectTemplates (map snd mTypesG)) mTypesG [])
                C.Union _ members -> do
                    mTypes <- concat <$> mapM collectMember members
                    let mTypesG = map (second TS.toGlobal) mTypes
                    insertType l (UnionDescr l (TypeSystem.collectTemplates (map snd mTypesG)) mTypesG [])
                _ -> return ()
        C.TypedefFunction (Fix (C.FunctionPrototype ty l params)) -> do
            retTy <- convertToTypeInfo Nothing ty
            paramTypes <- mapM (convertToTypeInfo Nothing . getParamType) params
            let retTyG = TS.toGlobal retTy
                paramTypesG = map TS.toGlobal paramTypes
                tps = TypeSystem.collectTemplates (retTyG : paramTypesG)
            dtraceM $ "collectDefs: TypedefFunction " ++ T.unpack (C.lexemeText l) ++ " tps=" ++ show tps
            insertType l (FuncDescr l tps retTyG paramTypesG)
        C.Struct l members -> do
            mTypes <- concat <$> mapM collectMember members
            let mTypesG = map (second TS.toGlobal) mTypes
            insertType l (StructDescr l (TypeSystem.collectTemplates (map snd mTypesG)) mTypesG [])
        C.Union l members -> do
            mTypes <- concat <$> mapM collectMember members
            let mTypesG = map (second TS.toGlobal) mTypes
            insertType l (UnionDescr l (TypeSystem.collectTemplates (map snd mTypesG)) mTypesG [])
        C.FunctionDecl _scope (Fix (C.FunctionPrototype ty (L _ _ name) params)) -> do
            vars <- State.gets esVars
            if Map.member name vars && Map.member name builtinMap
                then return ()
                else do
                    retTy <- convertToTypeInfo (Just name) ty
                    paramTypes <- mapM (convertToTypeInfo (Just name) . getParamType) params
                    dtraceM $ "collectDefs: FunctionDecl " ++ T.unpack name ++ " ty=" ++ show (Function retTy paramTypes)
                    State.modify $ \s -> s { esVars = Map.insert name (Function retTy paramTypes) (esVars s), esGlobals = Set.insert name (esGlobals s) }
        C.FunctionDefn _scope (Fix (C.FunctionPrototype ty (L _ _ name) params)) _body -> do
            vars <- State.gets esVars
            if Map.member name vars && Map.member name builtinMap
                then return ()
                else do
                    retTy <- convertToTypeInfo (Just name) ty
                    paramTypes <- mapM (convertToTypeInfo (Just name) . getParamType) params
                    dtraceM $ "collectDefs: FunctionDefn " ++ T.unpack name ++ " ty=" ++ show (Function retTy paramTypes)
                    State.modify $ \s -> s { esVars = Map.insert name (Function retTy paramTypes) (esVars s), esGlobals = Set.insert name (esGlobals s) }
        C.VarDeclStmt (Fix (C.VarDecl ty (L _ _ name) arrs)) _mInit -> do
            t <- convertToTypeInfo Nothing ty >>= flip addArrays arrs
            State.modify $ \s -> s { esVars = Map.insert name t (esVars s) }
        C.AggregateDecl n -> collectDefs n
        C.Group nodes -> mapM_ collectDefs nodes
        C.Commented _ n -> collectDefs n
        _ -> dtraceM $ "collectDefs fallback: " ++ show (fmap (const ()) node')

    checkCFG nodeId = do
        seen <- State.gets esSeenNodes
        if Set.member nodeId seen
            then return ()
            else do
                State.modify $ \s -> s { esSeenNodes = Set.insert nodeId seen }
                mCfg <- State.gets esCurrentCFG
                case mCfg of
                    Just cfg -> case Map.lookup nodeId cfg of
                        Just node'' -> do
                            -- dtraceM $ "checkCFG node " ++ show nodeId ++ " stmts: " ++ show (length (cfgStmts node''))
                            mapM_ checkNode (cfgStmts node'')
                            mapM_ checkCFG (cfgSuccs node'')
                        Nothing -> return () -- dtraceM $ "checkCFG node " ++ show nodeId ++ " not found"
                    Nothing -> return ()

    checkNode (Fix node') = case node' of
        C.FunctionDecl _scope proto@(Fix (C.FunctionPrototype _ (L _ _ name) _)) ->
            withContext (InFunction name) $ do
                oldVars <- State.gets esVars
                checkNode proto
                State.modify $ \s -> s { esVars = oldVars }
        C.FunctionDefn _scope proto@(Fix (C.FunctionPrototype ty (L _ _ name) params)) _body ->
            withContext (InFunction name) $ do
                oldVars <- State.gets esVars
                oldRt <- State.gets esReturnType

                -- Unify local params/return with global signature to connect templates
                vars <- State.gets esVars
                case Map.lookup name vars of
                    Just (Function sigRet sigParams) -> do
                        -- Unify return type
                        rt <- convertToTypeInfo Nothing ty
                        ctx <- State.gets esContext
                        addConstraint $ Subtype rt sigRet Nothing ctx GeneralMismatch
                        State.modify $ \s -> s { esReturnType = Just rt }

                        -- Unify params
                        checkNode proto -- This registers params in esVars
                        vars' <- State.gets esVars
                        let getParamType' (Fix (C.VarDecl _ (L _ _ pName) _)) = Map.lookup pName vars'
                            getParamType' (Fix (C.CallbackDecl _ (L _ _ pName))) = Map.lookup pName vars'
                            getParamType' (Fix (C.NonNullParam p)) = getParamType' p
                            getParamType' (Fix (C.NullableParam p)) = getParamType' p
                            getParamType' _ = Nothing

                        let paramTypes = mapMaybe getParamType' params
                        mapM_ (uncurry (\p sigP -> addConstraint $ Subtype sigP p Nothing ctx GeneralMismatch)) (zip paramTypes sigParams)
                    _ -> do
                        checkNode proto
                        rt <- convertToTypeInfo Nothing ty
                        State.modify $ \s -> s { esReturnType = Just rt }

                let cfg = buildCFG (Fix node')
                State.modify $ \s -> s { esCurrentCFG = Just cfg, esSeenNodes = Set.empty }
                checkCFG 0
                State.modify $ \s -> s { esCurrentCFG = Nothing, esSeenNodes = Set.empty, esVars = oldVars, esReturnType = oldRt }
        C.FunctionPrototype _ty (L _ _ _name) params -> do
            mapM_ registerParam params
            return ()
        C.CompoundStmt stmts -> mapM_ checkNode stmts
        C.IfStmt cond then' mElse -> do
            _ <- inferExpr cond
            checkNode then'
            mapM_ checkNode mElse
        C.WhileStmt cond body -> do
            _ <- inferExpr cond
            checkNode body
        C.ForStmt init' cond step body -> do
            checkNode init'
            _ <- inferExpr cond
            checkNode step
            checkNode body
        C.Return mExpr -> do
            rt <- State.gets esReturnType
            case (rt, mExpr) of
                (Just r, Just e) -> do
                    it <- inferExpr e
                    ctx <- State.gets esContext
                    addConstraint $ Subtype it r (getLexeme e) ctx ReturnMismatch
                _ -> return ()
            return ()
        C.SwitchStmt cond body -> do
            _ <- inferExpr cond
            mapM_ checkNode body
        C.Case _ stmt -> checkNode stmt
        C.Default stmt -> checkNode stmt
        C.MacroBodyStmt body -> checkNode body
        C.MacroBodyFunCall body -> checkNode body
        C.VarDeclStmt (Fix (C.VarDecl ty (L _ _ name) arrs)) mInit -> do
            t <- convertToTypeInfo Nothing ty >>= flip addArrays arrs
            State.modify $ \s -> s { esVars = Map.insert name t (esVars s) }
            case mInit of
                Just init' -> processInitializer t init'
                Nothing    -> return ()
        C.ExprStmt e -> checkNode e
        C.AggregateDecl n -> checkNode n
        C.Struct {} -> return ()
        C.Union {} -> return ()
        C.EnumDecl {} -> return ()
        C.EnumConsts {} -> return ()
        C.Typedef {} -> return ()
        C.TypedefFunction {} -> return ()
        C.PreprocInclude {} -> return ()
        C.PreprocDefine {} -> return ()
        C.PreprocDefineConst {} -> return ()
        C.PreprocDefineMacro {} -> return ()
        C.PreprocIf cond thenNodes elseNode -> do
            checkNode cond
            mapM_ checkNode thenNodes
            checkNode elseNode
        C.PreprocIfdef _ thenNodes elseNode -> do
            mapM_ checkNode thenNodes
            checkNode elseNode
        C.PreprocIfndef _ thenNodes elseNode -> do
            mapM_ checkNode thenNodes
            checkNode elseNode
        C.PreprocElse nodes -> mapM_ checkNode nodes
        C.PreprocElif cond thenNodes elseNode -> do
            checkNode cond
            mapM_ checkNode thenNodes
            checkNode elseNode
        C.PreprocUndef {} -> return ()
        C.PreprocDefined {} -> return ()
        C.PreprocScopedDefine cond thenNodes elseNode -> do
            checkNode cond
            mapM_ checkNode thenNodes
            checkNode elseNode
        C.MacroParam {} -> return ()
        C.StaticAssert {} -> return ()
        C.Comment {} -> return ()
        C.CommentSection _ nodes _ -> mapM_ checkNode nodes
        C.CommentSectionEnd {} -> return ()
        C.CommentInfo {} -> return ()
        C.LicenseDecl {} -> return ()
        C.CopyrightDecl {} -> return ()
        C.ExternC nodes -> mapM_ checkNode nodes
        C.Group nodes -> mapM_ checkNode nodes
        C.Commented _ n -> checkNode n
        _ -> do
             dtraceM $ "checkNode fallback: " ++ show (fmap (const ()) node')
             _ <- inferExpr (Fix node')
             return ()

    registerParam (Fix node') = case node' of
        C.VarDecl ty (L _ _ name) _ -> do
            t <- convertToTypeInfo Nothing ty
            State.modify $ \s -> s { esVars = Map.insert name t (esVars s) }
        C.CallbackDecl (L p1 t1 ty) (L _ _ name) -> do
            ts' <- State.gets esTypeSystem
            args <- case Map.lookup ty ts' of
                Just descr -> mapM (nextTemplate . TS.templateIdHint) (TypeSystem.getDescrTemplates descr)
                _          -> return []
            State.modify $ \s -> s { esVars = Map.insert name (Pointer (TypeRef FuncRef (L p1 t1 (TS.mkId ty)) args)) (esVars s) }
        C.NullableParam p -> do
            t <- convertToTypeInfo Nothing (Fix node')
            case p of
                Fix (C.VarDecl _ (L _ _ name) _) -> State.modify $ \s -> s { esVars = Map.insert name t (esVars s) }
                _ -> return ()
        C.NonNullParam p -> do
            t <- convertToTypeInfo Nothing (Fix node')
            case p of
                Fix (C.VarDecl _ (L _ _ name) _) -> State.modify $ \s -> s { esVars = Map.insert name t (esVars s) }
                _ -> return ()
        _ -> return ()

    processInitializer :: TypeInfo 'Local -> Node (Lexeme Text) -> Extract ()
    processInitializer target (Fix (C.InitialiserList [expr])) = do
        rt <- resolveTypeInfo target
        case rt of
            BuiltinType {} -> processInitializer target expr
            _              -> processInitializerList target [expr]

    processInitializer target (Fix (C.InitialiserList exprs)) =
        processInitializerList target exprs

    processInitializer target expr = do
        it <- inferExpr expr
        ctx <- State.gets esContext
        addConstraint $ Subtype it target (getLexeme expr) ctx InitializerMismatch

    processInitializerList :: TypeInfo 'Local -> [Node (Lexeme Text)] -> Extract ()
    processInitializerList target exprs = do
        rt <- resolveTypeInfo target
        case rt of
            TypeRef StructRef l args -> do
                let name = TS.templateIdBaseName (C.lexemeText l)
                ts' <- State.gets esTypeSystem
                case TypeSystem.lookupType name ts' of
                    Just descr@(TS.StructDescr _ _ _ _) -> do
                        -- Instantiate members with args if any
                        let instantiated = TypeSystem.instantiateDescr 0 TopLevel (Map.fromList (zip (TypeSystem.getDescrTemplates descr) args)) descr
                        case instantiated of
                            TS.StructDescr _ _ members' _ ->
                                mapM_ (uncurry processInitializer) (zip (map snd members') exprs)
                            _ -> fallback
                    _ -> fallback
            Array (Just et) _ ->
                mapM_ (processInitializer et) exprs
            _ -> fallback
      where
        fallback = do
            it <- inferExpr (Fix (C.InitialiserList exprs))
            ctx <- State.gets esContext
            addConstraint $ Subtype it target (getLexeme (Fix (C.InitialiserList exprs))) ctx InitializerMismatch

    inferExpr nOrig@(Fix node') = case node' of
        C.VarExpr (L _ _ name) -> do
            if name == "__func__"
                then return $ Pointer (Const (BuiltinType CharTy))
                else do
                    vars <- State.gets esVars
                    case Map.lookup name vars of
                        Just ty -> return ty
                        Nothing -> nextTemplate Nothing
        C.LiteralExpr C.Int lx -> do
            let val = read (T.unpack (C.lexemeText lx))
            return $ Singleton S32Ty val
        C.LiteralExpr C.Bool _ -> return $ BuiltinType BoolTy
        C.LiteralExpr C.Char _ -> return $ BuiltinType CharTy
        C.LiteralExpr C.Float _ -> return $ BuiltinType F32Ty
        C.LiteralExpr C.String _ -> return $ Pointer (BuiltinType CharTy)
        C.LiteralExpr C.ConstId (L _ _ name)
            | name == "nullptr" -> return $ BuiltinType NullPtrTy
            | name == "__FILE__" || name == "__func__" -> return $ Pointer (Const (BuiltinType CharTy))
            | name == "__LINE__" -> return $ BuiltinType S32Ty
            | otherwise -> do
                vars <- State.gets esVars
                case Map.lookup name vars of
                    Just ty -> return ty
                    Nothing -> nextTemplate Nothing
        C.ArrayAccess base idx -> do
            bt <- inferExpr base
            it <- inferExpr idx
            res <- case unwrap bt of
                Array (Just et) _ -> return $ TypeSystem.indexTemplates it et
                Pointer et -> return $ TypeSystem.indexTemplates it et
                _ -> do
                    et <- nextTemplate Nothing
                    ctx <- State.gets esContext
                    addConstraint $ Subtype bt (Array (Just et) []) (getLexeme base) ctx GeneralMismatch
                    return $ TypeSystem.indexTemplates it et
            dtraceM $ "ArrayAccess: bt=" ++ show bt ++ " it=" ++ show it ++ " res=" ++ show res
            return res
        C.MemberAccess obj field -> do
            ot <- inferExpr obj
            mt <- nextTemplate Nothing
            ctx <- State.gets esContext
            addConstraint $ HasMember ot (C.lexemeText field) mt (getLexeme obj) ctx GeneralMismatch
            return mt
        C.PointerAccess obj field -> do
            ot <- inferExpr obj
            mt <- nextTemplate Nothing
            ctx <- State.gets esContext
            addConstraint $ HasMember (unwrapInner' ot) (C.lexemeText field) mt (getLexeme obj) ctx GeneralMismatch
            return mt
          where
            unwrapInner' (Pointer t)  = t
            unwrapInner' (Nonnull t)  = unwrapInner' t
            unwrapInner' (Nullable t) = unwrapInner' t
            unwrapInner' t            = t
        C.UnaryExpr C.UopAddress e -> Nonnull . Pointer <$> inferExpr e
        C.UnaryExpr C.UopDeref e -> do
            et <- inferExpr e
            case et of
                Pointer t            -> return t
                Nonnull (Pointer t)  -> return t
                Nullable (Pointer t) -> return t
                _                    -> nextTemplate Nothing
        C.CastExpr ty e -> do
            targetTy <- convertToTypeInfo Nothing ty
            processInitializer targetTy e
            return targetTy
        C.MacroBodyStmt body -> inferExpr body
        C.MacroBodyFunCall body -> inferExpr body
        C.ParenExpr e -> inferExpr e
        C.InitialiserList exprs -> do
            tys <- mapM inferExpr exprs
            case tys of
                []    -> return $ Array Nothing []
                (t:_) -> return $ Array (Just t) tys
        C.AssignExpr lhs op rhs -> do
            lt <- inferExpr lhs
            case (op, unFix rhs) of
                (C.AopEq, C.InitialiserList _) -> do
                    processInitializer lt rhs
                    return lt
                _ -> do
                    rt <- inferExpr rhs
                    ctx <- State.gets esContext
                    let reason = if op == C.AopEq then AssignmentMismatch else GeneralMismatch
                    addConstraint $ Subtype rt lt (getLexeme lhs) ctx reason
                    return lt
        C.FunctionCall fun args -> inferFunctionCall fun args
        C.BinaryExpr lhs op rhs -> do
            lt <- decay <$> inferExpr lhs
            rt <- decay <$> inferExpr rhs
            ctx <- State.gets esContext
            case op of
                C.BopEq -> return $ BuiltinType BoolTy
                C.BopNe -> return $ BuiltinType BoolTy
                C.BopLt -> return $ BuiltinType BoolTy
                C.BopLe -> return $ BuiltinType BoolTy
                C.BopGt -> return $ BuiltinType BoolTy
                C.BopGe -> return $ BuiltinType BoolTy
                C.BopAnd -> do
                    addConstraint $ Subtype (decay lt) (BuiltinType BoolTy) (getLexeme lhs) ctx GeneralMismatch
                    addConstraint $ Subtype (decay rt) (BuiltinType BoolTy) (getLexeme rhs) ctx GeneralMismatch
                    return $ BuiltinType BoolTy
                C.BopOr -> do
                    addConstraint $ Subtype (decay lt) (BuiltinType BoolTy) (getLexeme lhs) ctx GeneralMismatch
                    addConstraint $ Subtype (decay rt) (BuiltinType BoolTy) (getLexeme rhs) ctx GeneralMismatch
                    return $ BuiltinType BoolTy
                C.BopPlus -> do
                    if isPointerLike lt
                        then do
                            addConstraint $ Subtype rt (BuiltinType S32Ty) (getLexeme rhs) ctx GeneralMismatch
                            return lt
                        else if isPointerLike rt
                        then do
                            addConstraint $ Subtype lt (BuiltinType S32Ty) (getLexeme lhs) ctx GeneralMismatch
                            return rt
                        else do
                            addConstraint $ Equality lt rt (getLexeme lhs) ctx GeneralMismatch
                            return lt
                C.BopMinus -> do
                    if isPointerLike lt && isPointerLike rt
                        then return $ BuiltinType SizeTy
                        else if isPointerLike lt
                        then do
                            addConstraint $ Subtype rt (BuiltinType S32Ty) (getLexeme rhs) ctx GeneralMismatch
                            return lt
                        else do
                            addConstraint $ Equality lt rt (getLexeme lhs) ctx GeneralMismatch
                            return lt
                _ -> do
                    addConstraint $ Equality lt rt (getLexeme lhs) ctx GeneralMismatch
                    return lt
        C.UnaryExpr C.UopNot e -> do
            _ <- inferExpr e
            return $ BuiltinType BoolTy
        C.UnaryExpr _ e -> inferExpr e
        C.TernaryExpr cond then' else' -> do
            _ <- inferExpr cond
            tt <- decay <$> inferExpr then'
            et <- decay <$> inferExpr else'
            ctx <- State.gets esContext
            addConstraint $ Equality tt et (getLexeme then') ctx GeneralMismatch
            return tt
        C.CompoundLiteral ty e -> do
            targetTy <- convertToTypeInfo Nothing ty
            processInitializer targetTy e
            return targetTy
        C.SizeofExpr _ -> return $ BuiltinType SizeTy
        C.SizeofType _ -> return $ BuiltinType SizeTy
        C.Commented _ e -> inferExpr e
        C.CommentExpr _ e -> inferExpr e
        C.Comment {} -> return Unconstrained
        _ -> do
            let name = T.pack $ take 40 $ show node'
            when (isExpression node') $
                reportError (getLexeme nOrig) (UnhandledConstruct name)
            return $ Unsupported name

    inferFunctionCall fun args = do
        -- dtraceM $ "inferFunctionCall: fun=" ++ show (fmap (const ()) (unFix fun))
        ft <- inferExpr fun
        atys <- mapM inferExpr args
        ctx <- State.gets esContext

        csId <- State.gets esCallSiteId
        State.modify $ \s -> s { esCallSiteId = csId + 1 }

        globals <- State.gets esGlobals
        let shouldRefresh = case unFix fun of
                C.VarExpr (L _ _ name) -> Set.member name globals
                _                      -> False

        -- dtraceM $ "inferFunctionCall: adding Callable constraint for " ++ show ft
        let datys = map decay atys
        addConstraint $ Callable ft datys (getLexeme fun) ctx (Just csId) shouldRefresh

        -- CoordinatedPair for registration patterns
        let isReg name = "registerhandler" `T.isInfixOf` name || "callback" `T.isInfixOf` name
        case (unFix fun, datys) of
            (C.VarExpr (L _ _ name), [ot, _, _, ct]) | name == "sort" -> do
                addCoordinatedPair ct ot (args !! 3)
            (C.VarExpr (L _ _ name), [_, _, ct, ot]) | isReg name -> do
                addCoordinatedPair ct ot (args !! 2)
            (C.VarExpr (L _ _ name), [ot, ct]) | isReg name -> do
                addCoordinatedPair ct ot (args !! 1)
            (C.VarExpr (L _ _ name), [ct, ot]) | isReg name -> do
                addCoordinatedPair ct ot (args !! 0)
            _ -> return ()

        -- Macro expansion
        let mName = case unFix fun of
                C.VarExpr (L _ _ name)               -> Just name
                C.LiteralExpr C.ConstId (L _ _ name) -> Just name
                _                                    -> Nothing

        mMacroRes <- case mName of
            Just name -> do
                macros <- State.gets esMacros
                -- dtraceM $ "inferFunctionCall: looking up macro " ++ T.unpack name ++ ", available: " ++ show (Map.keys macros)
                case Map.lookup name macros of
                    Just (params, body) -> do
                        withContext (InMacro name) $ do
                            -- Substitute params with args in esVars
                            oldVars <- State.gets esVars
                            let subVars = Map.fromList $ zip params atys
                            State.modify $ \s -> s { esVars = Map.union subVars (esVars s) }
                            res <- inferExpr body
                            checkNode body
                            State.modify $ \s -> s { esVars = oldVars }
                            return (Just res)
                    Nothing -> return Nothing
            Nothing -> return Nothing

        case mMacroRes of
            Just res -> return res
            Nothing -> do
                ts' <- State.gets esTypeSystem
                let resolvedFt = case ft of
                        TypeRef TS.FuncRef l _ ->
                            let name = templateIdBaseName (C.lexemeText l) in
                            case Map.lookup name ts' of
                                Just (FuncDescr _ _ ret ps) -> Function (TS.toLocal 0 TopLevel ret) (map (TS.toLocal 0 TopLevel) ps)
                                _                           -> ft
                        _ -> ft
                case resolvedFt of
                    Function ret _params -> return ret
                    _                    -> nextTemplate Nothing

    convertToTypeInfo :: Maybe Text -> Node (Lexeme Text) -> Extract (TypeInfo 'Local)
    convertToTypeInfo mQual (Fix node') = case node' of
        C.TyStd l     -> return $ TS.toLocal 0 TopLevel (TS.builtin l)
        C.NonNullParam p -> Nonnull <$> convertToTypeInfo mQual p
        C.NullableParam p -> Nullable <$> convertToTypeInfo mQual p
        C.VarDecl ty _ arrs -> convertToTypeInfo mQual ty >>= flip addArrays arrs
        C.TyConst t   -> Const <$> convertToTypeInfo mQual t
        C.TyOwner t   -> Owner <$> convertToTypeInfo mQual t
        C.TyNonnull t -> Nonnull <$> convertToTypeInfo mQual t
        C.TyNullable t -> Nullable <$> convertToTypeInfo mQual t
        C.TyPointer t -> do
            it <- convertToTypeInfo mQual t
            deVoidifyType mQual (Pointer it)
        C.TyStruct l@(L _ _ name) -> do
            ts' <- State.gets esTypeSystem
            case Map.lookup name ts' of
                Just descr -> do
                    descr' <- deVoidifyDescr mQual descr
                    let tps = TypeSystem.getDescrTemplates descr'
                    args <- case mQual of
                        Just q  -> mapM (const (nextTemplate (Just q))) tps
                        Nothing -> mapM (nextTemplate . TS.templateIdHint) tps
                    return $ TypeRef StructRef (fmap TS.mkId l) args
                _ -> return $ TypeRef StructRef (fmap TS.mkId l) []
        C.TyUnion l@(L _ _ name) -> do
            ts' <- State.gets esTypeSystem
            case Map.lookup name ts' of
                Just descr -> do
                    descr' <- deVoidifyDescr mQual descr
                    let tps = TypeSystem.getDescrTemplates descr'
                    args <- case mQual of
                        Just q  -> mapM (const (nextTemplate (Just q))) tps
                        Nothing -> mapM (nextTemplate . TS.templateIdHint) tps
                    return $ TypeRef UnionRef (fmap TS.mkId l) args
                _ -> return $ TypeRef UnionRef (fmap TS.mkId l) []
        C.TyFunc l@(L _ _ name) -> do
            ts' <- State.gets esTypeSystem
            args <- case Map.lookup name ts' of
                Just descr -> case mQual of
                    Just q  -> mapM (const (nextTemplate (Just q))) (TypeSystem.getDescrTemplates descr)
                    Nothing -> mapM (nextTemplate . TS.templateIdHint) (TypeSystem.getDescrTemplates descr)
                _ -> return []
            return $ TypeRef FuncRef (fmap TS.mkId l) args
        C.Ellipsis -> return VarArg
        C.TyUserDefined l@(L pos ty name) -> do
            ts' <- State.gets esTypeSystem
            case Map.lookup name ts' of
                Just (AliasDescr _ _ t) -> do
                    deVoidifyType mQual (TS.toLocal 0 TopLevel t)
                Just descr -> do
                    descr' <- deVoidifyDescr mQual descr
                    let tps = TypeSystem.getDescrTemplates descr'
                    args <- case mQual of
                        Just q  -> mapM (const (nextTemplate (Just q))) tps
                        Nothing -> mapM (nextTemplate . TS.templateIdHint) tps
                    let (ref, name') = case descr' of
                                StructDescr dl _ _ _ -> (StructRef, C.lexemeText dl)
                                UnionDescr dl _ _ _ -> (UnionRef, C.lexemeText dl)
                                FuncDescr dl _ _ _ -> (FuncRef, C.lexemeText dl)
                                _ -> (UnresolvedRef, name)
                    return $ TypeRef ref (L pos ty (TS.mkId name')) args
                _ -> return $ TypeRef UnresolvedRef (fmap TS.mkId l) []
        _ -> return $ BuiltinType VoidTy

    decay (Singleton std _)  = BuiltinType std
    decay (Array (Just t) _) = Pointer t
    decay t                  = t

    deVoidifyType :: Maybe Text -> TypeInfo 'Local -> Extract (TypeInfo 'Local)
    deVoidifyType mQual = foldFixM $ \case
        PointerF t | isVoid t -> do
            tp <- case mQual of
                Just q  -> nextTemplateQual q
                Nothing -> nextTemplate Nothing
            let applyWrappers (BuiltinType VoidTy) x = x
                applyWrappers (Const t') x           = Const (applyWrappers t' x)
                applyWrappers (Owner t') x           = Owner (applyWrappers t' x)
                applyWrappers (Nonnull t') x         = Nonnull (applyWrappers t' x)
                applyWrappers (Nullable t') x       = Nullable (applyWrappers t' x)
                applyWrappers (Var l t') x           = Var l (applyWrappers t' x)
                applyWrappers (Sized t' l) x         = Sized (applyWrappers t' x) l
                applyWrappers _ x                   = x
            return $ Pointer (applyWrappers t tp)
        f -> return $ Fix f

    deVoidifyDescr :: Maybe Text -> TypeDescr 'Global -> Extract (TypeDescr 'Local)
    deVoidifyDescr mQual = \case
        StructDescr l _ mems invs -> do
            mems' <- mapM (\(ln, t) -> (ln,) <$> deVoidifyType mQual (TS.toLocal 0 TopLevel t)) mems
            return $ StructDescr l (TypeSystem.collectTemplates (map snd mems')) mems' (map (TS.mapInvariant (TS.toLocal 0 TopLevel)) invs)
        UnionDescr l _ mems invs -> do
            mems' <- mapM (\(ln, t) -> (ln,) <$> deVoidifyType mQual (TS.toLocal 0 TopLevel t)) mems
            return $ UnionDescr l (TypeSystem.collectTemplates (map snd mems')) mems' (map (TS.mapInvariant (TS.toLocal 0 TopLevel)) invs)
        FuncDescr l _ ret ps -> do
            ret' <- deVoidifyType mQual (TS.toLocal 0 TopLevel ret)
            ps' <- mapM (deVoidifyType mQual . (TS.toLocal 0 TopLevel)) ps
            return $ FuncDescr l (TypeSystem.collectTemplates (ret' : ps')) ret' ps'
        AliasDescr l _ ty -> do
            ty' <- deVoidifyType mQual (TS.toLocal 0 TopLevel ty)
            return $ AliasDescr l (TypeSystem.collectTemplates [ty']) ty'
        t -> return $ TS.instantiateDescr 0 TopLevel Map.empty t

    addArrays ty [] = return ty
    addArrays ty arrs = do
        dtys <- forM arrs $ \case
            Fix (C.DeclSpecArray _ (Just s)) -> inferExpr s
            _ -> return Unconstrained
        return $ Array (Just ty) dtys
