{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Standard.Solver
    ( solveConstraints
    ) where

import           Control.Applicative                          ((<|>))
import           Control.Monad                                (foldM, forM_,
                                                               mapM_, void)
import           Control.Monad.State.Strict                   (State, StateT,
                                                               execState)
import qualified Control.Monad.State.Strict                   as State
import           Data.Fix                                     (Fix (..),
                                                               foldFix)
import           Data.List                                    (nub)
import           Data.Map.Strict                              (Map)
import qualified Data.Map.Strict                              as Map
import           Data.Maybe                                   (fromMaybe)
import           Data.Set                                     (Set)
import qualified Data.Set                                     as Set
import           Data.Text                                    (Text)
import qualified Data.Text                                    as T
import qualified Data.Tree                                    as Tree
import qualified Debug.Trace                                  as Debug
import           Language.Cimple                              (Lexeme (..))
import qualified Language.Cimple                              as C
import           Language.Hic.Core.Errors                     (Context (..),
                                                               ErrorInfo (..),
                                                               MismatchContext (..),
                                                               MismatchDetail (..),
                                                               MismatchReason (..),
                                                               Provenance (..),
                                                               Qualifier (..),
                                                               TypeError (..))
import qualified Language.Hic.Core.Pretty                     as P
import           Language.Hic.Core.TypeSystem                 (FullTemplate,
                                                               FullTemplateF (..),
                                                               Origin (..),
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
                                                               pattern ExternalType,
                                                               pattern FullTemplate,
                                                               pattern Function,
                                                               pattern IntLit,
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
import           Language.Hic.TypeSystem.Core.Base            (getDescrTemplates,
                                                               indexTemplates,
                                                               instantiateDescr,
                                                               isInt, isLPSTR,
                                                               isNetworkingStruct,
                                                               isPointerLike,
                                                               isPointerToChar,
                                                               isSockaddr,
                                                               isSockaddrIn,
                                                               isSockaddrIn6,
                                                               isSockaddrStorage,
                                                               isSpecial,
                                                               isVarArg,
                                                               lookupType,
                                                               resolveType',
                                                               unwrap)
import qualified Language.Hic.TypeSystem.Core.Base            as TS
import qualified Language.Hic.TypeSystem.Core.GraphSolver     as GS
import qualified Language.Hic.TypeSystem.Core.TypeGraph       as TG
import           Language.Hic.TypeSystem.Standard.Constraints (Constraint (..))

debugging :: Bool
debugging = False

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

data SolverState = SolverState
    { ssBindings   :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local)
    , ssErrors     :: [ErrorInfo 'Local]
    , ssTypeSystem :: TypeSystem
    , ssNextId     :: Int
    , ssFinalPass  :: Bool
    }

type Solver = State SolverState

-- | Solves a set of type constraints and returns any errors found.
solveConstraints :: TypeSystem -> [Constraint 'Local] -> [ErrorInfo 'Local]
solveConstraints ts constraints =
    let -- Pass 1-3: Structural refinement
        s1 = execState (mapM_ solve constraints >> resolveBindings) initialState
        s2 = execState (mapM_ solve constraints >> resolveBindings) s1
        s3 = execState (mapM_ solve constraints >> resolveBindings) s2
        -- Pass 4: Final error reporting
        finalState = execState (do
            State.modify (\s -> s { ssErrors = [], ssFinalPass = True })
            mapM_ solve constraints
            resolveBindings) s3
    in ssErrors finalState
  where
    initialState = SolverState Map.empty [] ts 0 False

-- | Resolves all current bindings co-inductively to their fixed points.
resolveBindings :: Solver ()
resolveBindings = do
    bindings <- State.gets ssBindings
    let graph = Map.map (\(ty, _) -> Set.singleton (TG.fromTypeInfo ty)) bindings
        resolvedMap = GS.solveAll graph (Map.keys bindings)
    State.modify $ \s -> s { ssBindings = Map.mapWithKey (\k (ty, prov) -> (maybe ty TG.toTypeInfo (Map.lookup k resolvedMap), prov)) (ssBindings s) }

nextTemplate :: Maybe Text -> Solver (TypeInfo 'Local)
nextTemplate mHint = do
    i <- State.gets ssNextId
    State.modify $ \s -> s { ssNextId = i + 1 }
    return $ Template (TIdSolver i mHint) Nothing

refreshTemplates :: Maybe Integer -> TypeInfo 'Local -> Solver (TypeInfo 'Local)
refreshTemplates mCsId ty = State.evalStateT (snd (foldFix alg ty)) Map.empty
  where
    alg :: TypeInfoF (TemplateId 'Local) (TypeInfo 'Local, StateT (Map (FullTemplate 'Local) (TypeInfo 'Local)) Solver (TypeInfo 'Local)) -> (TypeInfo 'Local, StateT (Map (FullTemplate 'Local) (TypeInfo 'Local)) Solver (TypeInfo 'Local))
    alg f = (Fix (fmap fst f), do
        case f of
            TemplateF (FullTemplate t i) -> do
                m <- State.get
                let k = FullTemplate t (fst <$> i)
                case Map.lookup k m of
                    Just t' -> return t'
                    Nothing -> do
                        i' <- maybe (return Nothing) (fmap Just . snd) i
                        t' <- State.lift $ case mCsId of
                            Just csId -> return $ Template (TIdInst csId (convertId t)) i'
                            Nothing   -> nextTemplate (Just $ templateIdBaseName t)
                        State.modify $ Map.insert k t'
                        return t'
            _ -> Fix <$> traverse (\(_, getInner) -> getInner) f)

    convertId :: TemplateId 'Local -> TemplateId 'Global
    convertId (TIdInst _ tid')   = tid'
    convertId (TIdPoly _ i h o)  = TIdParam i h o
    convertId (TIdSolver _ h)    = TIdParam 0 h TopLevel
    convertId (TIdAnonymous _ h) = TIdAnonymous 0 h
    convertId (TIdRec i)         = TIdRec i

solve :: Constraint 'Local -> Solver ()
solve = \case
    Equality t1 t2 loc ctx reason -> do
        mDetail <- unify t1 t2 reason loc ctx
        case mDetail of
            Just detail -> reportError loc ctx (TypeMismatch t2 t1 reason (Just detail))
            Nothing -> return ()
    Subtype actual expected loc ctx reason -> do
        mDetail <- subtype actual expected reason loc ctx
        case mDetail of
            Just detail -> reportError loc ctx (TypeMismatch expected actual reason (Just detail))
            Nothing -> return ()
    Callable t args loc ctx csId shouldRefresh -> checkCallable t args loc ctx csId shouldRefresh
    HasMember t field mt loc ctx reason -> checkMemberAccess t field mt reason loc ctx
    CoordinatedPair trigger actual expected loc ctx -> do
        tr <- resolveType =<< applyBindings trigger
        let isNull = \case
                BuiltinType NullPtrTy -> True
                _ -> False
        case tr of
            _ | isNull tr -> return ()
            _             -> do
                mDetail <- subtype actual expected GeneralMismatch loc ctx
                case mDetail of
                    Just detail -> reportError loc ctx (TypeMismatch expected actual GeneralMismatch (Just detail))
                    Nothing -> return ()

unify :: TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver (Maybe (MismatchDetail 'Local))
unify t1 t2 reason loc ctx = do
    dtraceM $ "UNIFY: " ++ show t1 ++ " with " ++ show t2
    m1 <- subtype t1 t2 reason loc ctx
    m2 <- subtype t2 t1 reason loc ctx
    return (m1 <|> m2)

subtype :: TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver (Maybe (MismatchDetail 'Local))
subtype actual expected reason ml ctx = do
    let ctx' = InUnification expected actual reason : ctx
    ab1 <- resolveType =<< applyBindings actual
    eb1 <- resolveType =<< applyBindings expected
    case (ab1, eb1) of
        (Template t i, a) -> bind t i a reason ml ctx' >> return Nothing
        (a, Template t i) -> bind t i a reason ml ctx' >> return Nothing

        _ | Just (FullTemplate t i) <- getTemplate (resolveType' ab1) -> bind t i eb1 reason ml ctx' >> return Nothing
        _ | Just (FullTemplate t i) <- getTemplate (resolveType' eb1) -> bind t i ab1 reason ml ctx' >> return Nothing

        (Nonnull a, Nonnull e)   -> subtype a e reason ml ctx'
        (Nullable a, Nullable e) -> subtype a e reason ml ctx'

        (Pointer a, Function re pe) -> subtype a (Function re pe) reason ml ctx'
        (Function ra pa, Pointer e) -> subtype (Function ra pa) e reason ml ctx'

        (Owner a, Owner e)       -> subtype a e reason ml ctx'
        (Const a, Const e)       -> subtype a e reason ml ctx'

        (Pointer a, Pointer e) -> fmap (wrap InPointer) <$> subtypePtr a e reason ml ctx'
        (Array (Just a) _, Pointer e) -> fmap (wrap InPointer) <$> subtypePtr a e reason ml ctx'
        (Pointer a, Array (Just e) _) -> fmap (wrap InPointer) <$> subtypePtr a e reason ml ctx'
        (Array (Just a) ds1, Array (Just e) ds2) -> do
            m1 <- fmap (wrap InArray) <$> subtype a e reason ml ctx'
            if not (null ds2) && length ds1 /= length ds2
                then return $ m1 <|> Just (BaseMismatch expected actual)
                else do
                    m2 <- foldM (\m (d1, d2) -> (m <|>) . fmap (wrap InArray) <$> subtype d1 d2 reason ml ctx') Nothing (zip ds1 ds2)
                    return $ m1 <|> m2

        (Function ra pa, Function re pe) -> do
            mRet <- fmap (wrap InFunctionReturn) <$> subtype ra re reason ml ctx'
            let expCount = length (filter (not . isVarArg) pe)
            let actCount = length pa
            if actCount < expCount
                then return $ mRet <|> Just (ArityMismatch expCount actCount)
                else if actCount > expCount && not (any isVarArg pe)
                    then return $ mRet <|> Just (ArityMismatch expCount actCount)
                    else do
                        -- Check argument types
                        mArgs <- foldM (\m (i, (p_act, p_exp)) -> (m <|>) . fmap (wrap (InFunctionParam i)) <$> subtype p_exp p_act reason ml ctx') Nothing (zip [0..] (zip pa (filter (not . isVarArg) pe)))
                        return $ mRet <|> mArgs

        (Function ra pa, Nonnull e) -> subtype (Function ra pa) e reason ml ctx'
        (Function ra pa, Nullable e) -> subtype (Function ra pa) e reason ml ctx'

        (Nonnull a, e)           -> subtype a e reason ml ctx'
        (Nullable a, e)          -> subtype a e reason ml ctx'
        (a, Nullable e)          -> subtype a e reason ml ctx'

        (_, Nonnull _)           -> return $ Just (MissingQualifier QNonnull expected actual)
        (_, Owner _)
            | ab1 == BuiltinType NullPtrTy -> return Nothing
            | otherwise -> return $ Just (MissingQualifier QOwner expected actual)
        (Owner a, e)             -> subtype a e reason ml ctx'
        (Const a, e)
            | not (isPointerLike ab1) -> subtype a e reason ml ctx'
            | otherwise -> return $ Just (MissingQualifier QConst expected actual)

        (Function ra pa, TypeRef FuncRef (L _ _ tid) args) -> do
            ts <- State.gets ssTypeSystem
            let name = templateIdBaseName tid
            case lookupType name ts of
                Just descr@(FuncDescr _ _ _ _) ->
                    case TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) args)) descr of
                        FuncDescr _ _ re pe ->
                            subtype (Function ra pa) (Function re pe) reason ml ctx'
                        _ -> error "impossible"
                _ -> return $ Just (BaseMismatch expected actual)

        (TypeRef FuncRef (L _ _ tid) args, Function re pe) -> do
            ts <- State.gets ssTypeSystem
            let name = templateIdBaseName tid
            case lookupType name ts of
                Just descr@(FuncDescr _ _ _ _) ->
                    case TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) args)) descr of
                        FuncDescr _ _ ra pa ->
                            subtype (Function ra pa) (Function re pe) reason ml ctx'
                        _ -> error "impossible"
                _ -> return $ Just (BaseMismatch expected actual)

        (TypeRef r1 l1 a1, TypeRef r2 l2 a2)
            | (r1 == r2 || r1 == UnresolvedRef || r2 == UnresolvedRef) && C.lexemeText l1 == C.lexemeText l2 -> do
                ts <- State.gets ssTypeSystem
                let getArgs l a = if null a
                        then do
                            let name = templateIdBaseName (C.lexemeText l)
                            let lText = fmap (const name) l
                            let tps = getDescrTemplates (Map.findWithDefault (AliasDescr lText [] (BuiltinType VoidTy)) name ts)
                            mapM (nextTemplate . TS.templateIdHint) tps
                        else mapM applyBindings a
                a1' <- getArgs l1 a1
                a2' <- getArgs l2 a2
                if length a1' /= length a2'
                    then return $ Just (BaseMismatch expected actual)
                    else do
                        mArgs <- foldM (\m (v1, v2) -> (m <|>) <$> unify v1 v2 reason ml ctx') Nothing (zip a1' a2')
                        return mArgs

        (a, e) -> if compatible a e
                    then return Nothing
                    else return $ Just (BaseMismatch expected actual)
  where
    wrap mctx detail = MismatchDetail expected actual reason (Just (mctx, detail))

subtypePtr :: TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver (Maybe (MismatchDetail 'Local))
subtypePtr actual expected reason ml ctx = do
    let ctx' = InUnification expected actual reason : ctx
    ab1 <- resolveType =<< applyBindings actual
    eb1 <- resolveType =<< applyBindings expected
    case (ab1, eb1) of
        _ | isNetworkingStruct ab1 && isNetworkingStruct eb1 -> return Nothing
        (Const a, Const e) -> subtypePtr a e reason ml ctx'
        (a, Const e)       -> subtypePtr a e reason ml ctx'
        (Const _, e) | Just _ <- getTemplate (resolveType' e) -> subtype ab1 eb1 reason ml ctx'
        (Const _, _)       -> return $ Just (MissingQualifier QConst expected actual)
        _                  -> subtype ab1 eb1 reason ml ctx'

bind :: TemplateId 'Local -> Maybe (TypeInfo 'Local) -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver ()
bind name index ty reason ml ctx = do
    bindings <- State.gets ssBindings
    ty' <- applyBindings ty
    dtraceM $ "bind name=" ++ show name ++ " index=" ++ show index ++ " to " ++ show ty'

    let unifyAndReport existing = do
            mDetail <- unify existing ty' reason ml ctx
            case mDetail of
                Just detail -> reportError ml ctx (TypeMismatch ty' existing reason (Just detail))
                Nothing -> return ()

    -- Check conflicts with ALL compatible indices, including exact match.
    -- We do this even if an exact match exists to ensure that conflicts
    -- detected during inference are also reported during the final pass.
    forM_ (Map.toList bindings) $ \case
        (FullTemplate n i, (existing, _)) | n == name ->
            case (index, i) of
                (Just idx, Just idx')
                    | compatible idx idx' || compatible idx' idx -> unifyAndReport existing
                (Nothing, Nothing) -> unifyAndReport existing
                _ -> return ()
        _ -> return ()

    -- Now add or update the binding if not already present.
    let k = FullTemplate name index
    case Map.lookup k bindings of
        Just _ -> return ()
        Nothing ->
            if occurs name index ty'
                then return () -- Occur check failed
                else do
                    let prov = FromContext (ErrorInfo ml ctx (TypeMismatch (Template name index) ty' reason Nothing) [])
                    State.modify $ \s -> s { ssBindings = Map.insert k (ty', prov) (ssBindings s) }

occurs :: TemplateId 'Local -> Maybe (TypeInfo 'Local) -> TypeInfo 'Local -> Bool
occurs name index ty = snd $ foldFix alg ty
  where
    alg f = (Fix (fmap fst f), (Fix (fmap fst f) == Template name index) || any snd f)

applyBindings :: TypeInfo 'Local -> Solver (TypeInfo 'Local)
applyBindings ty = snd (foldFix alg ty) Set.empty
  where
    alg :: TypeInfoF (TemplateId 'Local) (TypeInfo 'Local, Set (FullTemplate 'Local) -> Solver (TypeInfo 'Local)) -> (TypeInfo 'Local, Set (FullTemplate 'Local) -> Solver (TypeInfo 'Local))
    alg f = (Fix (fmap fst f), \seen -> case f of
        VarF l (_, tAction) -> Var l <$> tAction seen
        TemplateF (FullTemplate t i) -> do
            i'' <- maybe (return Nothing) (fmap Just . (\(_, getInner) -> getInner seen)) i
            let k = FullTemplate t i''
            if Set.member k seen
                then return $ Template t i''
                else do
                    bindings <- State.gets ssBindings
                    case Map.lookup k bindings of
                        Just (target, _) -> applyBindings' (Set.insert k seen) target
                        Nothing -> case i'' of
                            Nothing -> return $ Template t Nothing
                            Just idx -> case Map.lookup (FullTemplate t Nothing) bindings of
                                Just (baseTarget, _) -> applyBindings' (Set.insert k seen) (indexTemplates idx baseTarget)
                                Nothing -> return $ Template t i''
        _ -> Fix <$> traverse (\(_, getInner) -> getInner seen) f)

    applyBindings' seen ty' = snd (foldFix alg ty') seen

resolveType :: TypeInfo 'Local -> Solver (TypeInfo 'Local)
resolveType ty = resolveTypeWith Set.empty ty

resolveTypeWith :: Set Text -> TypeInfo 'Local -> Solver (TypeInfo 'Local)
resolveTypeWith seen ty = snd (foldFix alg ty) seen
  where
    alg :: TypeInfoF (TemplateId 'Local) (TypeInfo 'Local, Set Text -> Solver (TypeInfo 'Local)) -> (TypeInfo 'Local, Set Text -> Solver (TypeInfo 'Local))
    alg f = (Fix (fmap fst f), \s -> case f of
        VarF _ (_, tAction) -> tAction s
        TypeRefF _ (L _ _ tid) _ ->
            let name = templateIdBaseName tid in
            if Set.member name s
            then return $ Fix (fmap fst f)
            else do
                ts <- State.gets ssTypeSystem
                case lookupType name ts of
                    Just (AliasDescr _ _ target) -> resolveTypeWith (Set.insert name s) (TS.toLocal 0 TopLevel target)
                    _                            -> return $ Fix (fmap fst f)
        _ -> Fix <$> traverse (\(_, getInner) -> getInner s) f)

getTemplate :: TypeInfo 'Local -> Maybe (FullTemplate 'Local)
getTemplate = \case
    Template t i -> Just (FullTemplate t i)
    _            -> Nothing

compatible :: TypeInfo 'Local -> TypeInfo 'Local -> Bool
compatible t1 t2 | t1 == t2 = True
compatible (ExternalType l1) (ExternalType l2) =
    templateIdBaseName (C.lexemeText l1) == templateIdBaseName (C.lexemeText l2)
compatible t1 t2 | isNetworkingStruct t1 && isNetworkingStruct t2 = True
compatible t1 t2 | isLPSTR t1 && isPointerToChar t2 = True
compatible t1 t2 | isLPSTR t2 && isPointerToChar t1 = True
compatible (Singleton b1 _) (BuiltinType b2) | isInt b1 && isInt b2 = True
compatible (BuiltinType b1) (Singleton b2 _) | isInt b1 && b2 == b1 = True
compatible (Singleton b1 v1) (Singleton b2 v2) = b1 == b2 && v1 == v2
compatible (IntLit (L _ _ v1)) (IntLit (L _ _ v2)) = v1 == v2
compatible (IntLit (L _ _ v1)) (Singleton _ v2) = (case T.unpack (TS.templateIdBaseName v1) of "" -> False; s -> read s == v2)
compatible (Singleton _ v1) (IntLit (L _ _ v2)) = (case T.unpack (TS.templateIdBaseName v2) of "" -> False; s -> v1 == read s)
compatible (IntLit _) (BuiltinType b) = isInt b
compatible (BuiltinType b) (IntLit _) = isInt b
compatible (BuiltinType b1) (BuiltinType b2) | isInt b1 && isInt b2 = True
compatible (Pointer _) (Array _ _) = True
compatible (Array _ _) (Pointer _) = True
compatible (BuiltinType NullPtrTy) (Pointer _) = True
compatible (Pointer _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType NullPtrTy) (Nullable _) = True
compatible (Nullable _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType NullPtrTy) (Owner _) = True
compatible (Owner _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType VoidTy) (BuiltinType VoidTy) = True

-- Ignore wrappers on either side for basic compatibility
compatible (Const t1) t2 = compatible t1 t2
compatible t1 (Const t2) = compatible t1 t2
compatible (Owner t1) t2 = compatible t1 t2
compatible t1 (Owner t2) = compatible t1 t2
compatible (Nonnull t1) t2 = compatible t1 t2
compatible t1 (Nonnull t2) = compatible t1 t2
compatible (Nullable t1) t2 = compatible t1 t2
compatible t1 (Nullable t2) = compatible t1 t2
compatible (Sized t1 _) t2 = compatible t1 t2
compatible t1 (Sized t2 _) = compatible t1 t2
compatible (Var _ t1) t2 = compatible t1 t2
compatible t1 (Var _ t2) = compatible t1 t2

compatible _ _ = False

reportError :: Maybe (Lexeme Text) -> [Context 'Local] -> TypeError 'Local -> Solver ()
reportError ml ctx err = do
    dtraceM $ "reportError: " ++ show err
    isFinal <- State.gets ssFinalPass
    err' <- case err of
        TypeMismatch expected actual reason mDetail -> do
            expected' <- resolveType =<< applyBindings expected
            actual' <- resolveType =<< applyBindings actual
            return $ TypeMismatch expected' actual' reason mDetail
        _ -> return err
    if isFinal
    then do
        bindings <- State.gets ssBindings
        let allTypes = case err of
                TypeMismatch expected actual _ _ -> expected : actual : concatMap getContextTypes ctx
                _ -> concatMap getContextTypes ctx
        let expls = concatMap (P.explainType bindings) allTypes
        State.modify $ \s -> s { ssErrors = ssErrors s ++ [ErrorInfo ml ctx err' (P.dedupDocs expls)] }
    else
        State.modify $ \s -> s { ssErrors = ssErrors s ++ [ErrorInfo ml ctx err' []] }
  where
    getContextTypes = \case
        InUnification e a _ -> [e, a]
        _ -> []

checkCallable :: TypeInfo 'Local -> [TypeInfo 'Local] -> Maybe (Lexeme Text) -> [Context 'Local] -> Maybe Integer -> Bool -> Solver ()
checkCallable t args ml ctx mCsId shouldRefresh = do
    rt <- resolveType =<< applyBindings t
    -- Refresh templates for all callables to allow polymorphism
    rt' <- if shouldRefresh
               then refreshTemplates mCsId rt
               else return rt
    -- Also de-voidify the resolved type recursively
    rt'' <- deVoidify rt'
    case resolveType' rt'' of
        Function ret params -> handleFunction ret params rt''
        Pointer (Function ret params) -> handleFunction ret params rt''
        TypeRef FuncRef (L _ _ tid) tps -> handleFuncRef tid tps rt''
        Pointer (TypeRef FuncRef (L _ _ tid) tps) -> handleFuncRef tid tps rt''
        Template tid i -> do
            -- Proactively bind the template to a function type based on how it's being called.
            -- Deterministic template names based on csId ensure monotonicity.
            bindings <- State.gets ssBindings
            case mCsId of
                Just csId -> do
                    let retTid = TIdInst csId (TIdName "ret")
                    case Map.lookup (FullTemplate tid i) bindings of
                        Just (Fix (FunctionF _ _), _) -> return ()
                        _ -> bind tid i (Function (Template retTid Nothing) args) GeneralMismatch ml ctx
                Nothing -> return () -- Cannot proactively bind without stable ID
        BuiltinType VoidTy -> return () -- Safe fallback for incomplete inference
        BuiltinType NullPtrTy -> return ()
        _ -> reportError ml ctx (CallingNonFunction "expression" rt)
  where
    deVoidify = snd . foldFix alg
      where
        alg :: TypeInfoF (TemplateId 'Local) (TypeInfo 'Local, Solver (TypeInfo 'Local)) -> (TypeInfo 'Local, Solver (TypeInfo 'Local))
        alg f = (Fix (fmap fst f), case f of
            PointerF (orig, _) | TS.isVoid orig -> do
                tp <- nextTemplate Nothing
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

    handleFunction _ret params _rt' = do
        let expCount = length (filter (not . isSpecial) params)
        let actualParams = filter (not . isSpecial) params
        let actCount = length args
        if actCount < expCount
            then reportError ml ctx (TooFewArgs expCount actCount)
            else if actCount > expCount && not (any isVarArg params)
                then reportError ml ctx (TooManyArgs expCount actCount)
                else do
                    -- Check argument types
                    forM_ (zip [0..] (zip args actualParams)) $ \(i, (p_act, p_exp)) -> do
                        mDetail <- subtype p_act p_exp (ArgumentMismatch i) ml ctx
                        case mDetail of
                            Just detail -> reportError ml ctx (TypeMismatch p_exp p_act (ArgumentMismatch i) (Just detail))
                            Nothing -> return ()

    handleFuncRef tid tps rt = do
        let name = templateIdBaseName tid
        ts <- State.gets ssTypeSystem
        case lookupType name ts of
            Just descr@(FuncDescr _ _ _ _) -> do
                case TS.instantiateDescr 0 TopLevel (Map.fromList (zip (getDescrTemplates descr) tps)) descr of
                    FuncDescr _ _ ret params -> handleFunction ret params rt
                    _                        -> error "impossible"
            _ -> reportError ml ctx (CallingNonFunction (templateIdBaseName tid) rt)

checkMemberAccess :: TypeInfo 'Local -> Text -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Solver ()
checkMemberAccess t field mt reason ml ctx = do
    rt <- resolveType =<< applyBindings t
    ts <- State.gets ssTypeSystem
    dtraceM $ "checkMemberAccess: t=" ++ show t ++ " (resolved=" ++ show rt ++ ") field=" ++ T.unpack field ++ " mt=" ++ show mt
    let go rt' = case resolveType' rt' of
            Pointer inner -> go inner
            TypeRef _ (L _ _ tid) args ->
                let name = TS.templateIdBaseName tid in
                case lookupType name ts of
                    Just descr ->
                        let descr' = TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) args)) descr
                        in dtraceM ("  found descr for " ++ T.unpack name ++ ": " ++ show descr') >> case descr' of
                            StructDescr _ _ members _ -> findMember members
                            UnionDescr  _ _ members _ -> findMember members
                            _                         -> return ()
                    _ -> return ()
            _ -> return ()
    go rt
  where
    findMember members =
        case filter (\(l, _) -> C.lexemeText l == field) members of
            ((_, mty):_) -> do
                dtraceM ("  unifying mty=" ++ show mty ++ " with mt=" ++ show mt)
                mDetail <- unify mty mt reason Nothing []
                case mDetail of
                    Just detail -> reportError ml ctx (TypeMismatch mt mty reason (Just detail))
                    Nothing -> return ()
            [] -> reportError ml ctx (CustomError $ "member '" <> field <> "' not found")
