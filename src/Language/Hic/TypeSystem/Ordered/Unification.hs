{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Ordered.Unification
    ( UnifyResult (..)
    , UnifyState (..)
    , Unify
    , runUnification
    , buildBindingsIndex
    , unify
    , subtype
    , applyBindings
    , applyBindingsDeep
    , resolveType
    , unwrap
    , reportError
    ) where

import           Control.Applicative                        ((<|>))
import           Control.Monad                              (foldM, forM_,
                                                             unless, void, when,
                                                             zipWithM_)
import           Control.Monad.State.Strict                 (State, StateT,
                                                             execState, lift)
import qualified Control.Monad.State.Strict                 as State
import           Data.Fix                                   (Fix (..), foldFix,
                                                             foldFixM, unFix)
import qualified Data.Graph                                 as Graph
import           Data.Map.Strict                            (Map)
import qualified Data.Map.Strict                            as Map
import           Data.Maybe                                 (catMaybes,
                                                             fromMaybe, isJust,
                                                             isNothing,
                                                             mapMaybe)
import           Data.Set                                   (Set)
import qualified Data.Set                                   as Set
import           Data.Text                                  (Text)
import qualified Data.Text                                  as T
import qualified Data.Tree                                  as Tree
import qualified Debug.Trace                                as Debug
import           Language.Cimple                            (Lexeme (..))
import qualified Language.Cimple                            as C
import           Language.Hic.Core.Errors                   (Context (..),
                                                             ErrorInfo (..),
                                                             MismatchContext (..),
                                                             MismatchDetail (..),
                                                             MismatchReason (..),
                                                             Provenance (..),
                                                             Qualifier (..),
                                                             TypeError (..))
import qualified Language.Hic.Core.Pretty                   as P
import           Language.Hic.Core.TypeSystem               (FullTemplate,
                                                             FullTemplateF (..),
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
                                                             pattern EnumMem,
                                                             pattern ExternalType,
                                                             pattern FullTemplate,
                                                             pattern Function,
                                                             pattern IntLit,
                                                             pattern NameLit,
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
                                                             pattern Var,
                                                             pattern VarArg,
                                                             templateIdBaseName,
                                                             templateIdHint,
                                                             templateIdToText)
import           Language.Hic.TypeSystem.Core.Base          (isLPSTR,
                                                             isNetworkingStruct,
                                                             isPointerLike,
                                                             isPointerToChar,
                                                             isVarArg,
                                                             unwrap)
import qualified Language.Hic.TypeSystem.Core.Base          as TS
import qualified Language.Hic.TypeSystem.Core.GraphSolver   as GS
import           Language.Hic.TypeSystem.Core.Lattice       (join)
import           Language.Hic.TypeSystem.Core.Qualification (QualState (..),
                                                             allowCovariance,
                                                             stepQual,
                                                             subtypeQuals)
import qualified Language.Hic.TypeSystem.Core.TypeGraph     as TG

debugging :: Bool
debugging = False

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

data UnifyResult = UnifyResult
    { urErrors   :: [ErrorInfo 'Local]
    , urBindings :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local)
    } deriving (Show)

data UnifyState = UnifyState
    { usBindings      :: Map (FullTemplate 'Local) (TypeInfo 'Local, Provenance 'Local)
    , usBindingsIndex :: Map (TemplateId 'Local) [FullTemplate 'Local]
    , usErrors        :: [ErrorInfo 'Local]
    , usTypeSystem    :: TypeSystem
    , usSeen          :: Set (TypeInfo 'Local, TypeInfo 'Local, QualState)
    , usNextId        :: Int
    , usFinalPass     :: Bool
    }

type Unify = State UnifyState

runUnification :: TypeSystem -> Unify a -> UnifyResult
runUnification ts action =
    let initialState = UnifyState Map.empty Map.empty [] ts Set.empty 0 True
        finalState = execState action initialState
    in UnifyResult (usErrors finalState) (usBindings finalState)

buildBindingsIndex :: Map (FullTemplate 'Local) a -> Map (TemplateId 'Local) [FullTemplate 'Local]
buildBindingsIndex = Map.foldlWithKey' (\acc ft _ -> Map.insertWith (++) (ftId ft) [ft] acc) Map.empty

unify :: TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
unify = unifyRecursive QualTop

unifyRecursive :: QualState -> TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
unifyRecursive qstate t1 t2 reason ml ctx = do
    dtraceM $ "UNIFY(" ++ show qstate ++ "): " ++ show t1 ++ " with " ++ show t2
    m1 <- subtypeRecursive qstate t1 t2 reason ml ctx
    m2 <- subtypeRecursive qstate t2 t1 reason ml ctx
    return (m1 <|> m2)

subtype :: TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
subtype actual expected reason ml ctx = subtypeRecursive QualTop actual expected reason ml ctx

subtypeRecursive :: QualState -> TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
subtypeRecursive qstate actual expected reason ml ctx = do
    ab0 <- resolveType =<< applyBindings actual
    eb0 <- resolveType =<< applyBindings expected
    ab1 <- deVoidify ab0
    eb1 <- deVoidify eb0

    dtraceM $ "SUBTYPE(" ++ show qstate ++ "): " ++ show ab1 ++ " <: " ++ show eb1
    seen <- State.gets usSeen
    if Set.member (ab1, eb1, qstate) seen
        then dtraceM "  ALREADY SEEN" >> return Nothing
        else do
            State.modify $ \s -> s { usSeen = Set.insert (ab1, eb1, qstate) (usSeen s) }
            res <- subtypeImpl qstate ab1 eb1 reason ml ctx
            State.modify $ \s -> s { usSeen = seen }
            return res

deVoidify :: TypeInfo 'Local -> Unify (TypeInfo 'Local)
deVoidify = foldFixM alg
  where
    alg (PointerF it) | TS.isVoid it = do
        tid <- nextSolverTemplate Nothing
        -- Hoist wrappers (Nullable, Nonnull, etc.) outside the Pointer so
        -- that e.g. void *_Nullable becomes Nullable(Pointer(Template T))
        -- rather than Pointer(Nullable(Template T)).  The annotation
        -- qualifies the pointer, not the pointee.
        return $ applyWrappers it (Pointer tid)
    alg f = return $ Fix f

    applyWrappers (BuiltinType VoidTy) x = x
    applyWrappers (Const t) x            = Const (applyWrappers t x)
    applyWrappers (Owner t) x            = Owner (applyWrappers t x)
    applyWrappers (Nonnull t) x          = Nonnull (applyWrappers t x)
    applyWrappers (Nullable t) x         = Nullable (applyWrappers t x)
    applyWrappers (Qualified qs t) x     = Qualified qs (applyWrappers t x)
    applyWrappers (Var l t) x            = Var l (applyWrappers t x)
    applyWrappers (Sized t l) x          = Sized (applyWrappers t x) l
    applyWrappers _ x                    = x

nextSolverTemplate :: Maybe Text -> Unify (TypeInfo 'Local)
nextSolverTemplate mHint = do
    i <- State.gets usNextId
    State.modify $ \s -> s { usNextId = i + 1 }
    return $ Template (TIdSolver i mHint) Nothing

subtypeImpl :: QualState -> TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
subtypeImpl qstate actual expected reason ml ctx = do
    let ctx' = InUnification expected actual reason : ctx
    let reportMismatch d = reportError ml ctx' (TypeMismatch expected actual reason (Just d)) >> return (Just d)
    dtraceM $ "subtypeImpl " ++ show actual ++ " <: " ++ show expected
    case (actual, expected) of
        (TS.Unconstrained, _) -> return Nothing
        (_, TS.Unconstrained) -> return Nothing
        (_, e) | TS.isConflict e -> return Nothing -- Everything is a subtype of Conflict
        (a, _) | TS.isConflict a -> reportMismatch (BaseMismatch expected actual)
        (Unsupported msg, _) -> reportError ml ctx' (CustomError $ "unsupported expression: " <> msg) >> return (Just (BaseMismatch expected actual))
        (_, Unsupported msg) -> reportError ml ctx' (CustomError $ "unsupported type: " <> msg) >> return (Just (BaseMismatch expected actual))

        (BuiltinType NullPtrTy, Nonnull _) -> reportMismatch (MissingQualifier QNonnull expected actual)
        (BuiltinType NullPtrTy, Nullable _) -> return Nothing
        (BuiltinType NullPtrTy, Pointer _) -> return Nothing
        (BuiltinType NullPtrTy, Owner _) -> return Nothing
        (BuiltinType NullPtrTy, Array _ _) -> return Nothing
        (BuiltinType NullPtrTy, Sized _ _) -> return Nothing
        (Nullable _, BuiltinType NullPtrTy) -> return Nothing
        (Pointer _, BuiltinType NullPtrTy) -> return Nothing
        (Owner _, BuiltinType NullPtrTy) -> return Nothing
        (Array _ _, BuiltinType NullPtrTy) -> return Nothing
        (Sized _ _, BuiltinType NullPtrTy) -> return Nothing

        (BuiltinType VoidTy, a) -> do
            let tid = TIdAnonymous 0 (Just "") -- Default hint for anonymous void*
            bind tid Nothing a reason ml ctx' >> return Nothing
        (a, BuiltinType VoidTy) -> do
            let tid = TIdAnonymous 0 (Just "")
            bind tid Nothing a reason ml ctx' >> return Nothing

        (Template t i, a) -> bind t i a reason ml ctx' >> return Nothing
        (a, Template t i) -> bind t i a reason ml ctx' >> return Nothing

        -- Sized is metadata (length tracking from joinSizer), strip it before
        -- qualifier checks so that Nullable/Nonnull match correctly on both sides.
        (Sized a _, Sized e _)   -> subtypeRecursive qstate a e reason ml ctx'
        (Sized a _, e)           -> subtypeRecursive qstate a e reason ml ctx'
        (a, Sized e _)           -> subtypeRecursive qstate a e reason ml ctx'

        (Qualified qs a, Qualified es e) -> do
            let errNonnull = if Set.member QNonnull es && not (Set.member QNonnull qs)
                             then Just (MissingQualifier QNonnull expected actual)
                             else Nothing
            let errNullable = if Set.member QNullable qs && not (Set.member QNullable es)
                              then Just (BaseMismatch expected actual)
                              else Nothing
            let errConst = if Set.member QConst es && not (Set.member QConst qs) && not (allowCovariance qstate)
                           then Just (MissingQualifier QConst expected actual)
                           else if Set.member QConst qs && not (Set.member QConst es) && qstate /= QualTop
                           then Just (UnexpectedQualifier QConst expected actual)
                           else Nothing
            let errOwner = if Set.member QOwner es && not (Set.member QOwner qs)
                           then Just (MissingQualifier QOwner expected actual)
                           else Nothing
            case catMaybes [errNonnull, errNullable, errConst, errOwner] of
                (err:_) -> reportMismatch err
                []      -> subtypeRecursive qstate a e reason ml ctx'

        (Qualified qs a, e) -> do
            -- Allow nullable actual when:
            -- (1) The expected type is an Array — nullable pointers can be
            --     indexed (programmer is responsible for null-checking).
            -- (2) The constraint comes from a cast — explicit casts should be
            --     able to strip nullable (e.g. casting a deVoidified void*
            --     _Nullable return value to a concrete pointer type).
            let isArr = case e of { Array _ _ -> True; _ -> False }
            let errNullable = if Set.member QNullable qs && not isArr && reason /= CastMismatch
                              then Just (BaseMismatch expected actual)
                              else Nothing
            let errConst = if Set.member QConst qs && qstate /= QualTop
                           then Just (UnexpectedQualifier QConst expected actual)
                           else Nothing
            case catMaybes [errNullable, errConst] of
                (err:_) -> reportMismatch err
                []      -> subtypeRecursive qstate a e reason ml ctx'

        (a, Qualified es e) -> do
            let check q = case q of
                    QNonnull -> if Set.member QNonnull es
                                then case a of
                                    _ | isPointerLike a -> Nothing
                                    Function {} -> Nothing
                                    _ -> Just (MissingQualifier QNonnull expected actual)
                                else Nothing
                    QConst -> if Set.member QConst es && not (allowCovariance qstate)
                              then Just (MissingQualifier QConst expected actual)
                              else Nothing
                    QOwner -> if Set.member QOwner es && not (Set.member QOwner (TS.ftQuals (TS.toFlat actual)))
                              then Just (MissingQualifier QOwner expected actual)
                              else Nothing
                    _ -> Nothing
            case catMaybes [check QNonnull, check QConst, check QOwner] of
                (err:_) -> reportMismatch err
                []      -> subtypeRecursive qstate a e reason ml ctx'

        (Pointer _, Pointer _) -> fmap (wrap InPointer) <$> subtypePtr qstate actual expected reason ml ctx'
        (Array (Just _) _, Pointer _) -> fmap (wrap InPointer) <$> subtypePtr qstate actual expected reason ml ctx'
        (Pointer _, Array (Just _) _) -> fmap (wrap InPointer) <$> subtypePtr qstate actual expected reason ml ctx'
        (Array (Just a) ds1, Array (Just e) ds2) -> do
            m1 <- fmap (wrap InArray) <$> subtypeRecursive qstate a e reason ml ctx'
            if not (null ds2) && length ds1 /= length ds2
                then reportMismatch (BaseMismatch expected actual)
                else do
                    m2 <- foldM (\m (d1, d2) -> (m <|>) . fmap (wrap InArray) <$> subtypeRecursive qstate d1 d2 reason ml ctx') Nothing (zip ds1 ds2)
                    return $ m1 <|> m2

        (Function ra pa, Pointer e) -> subtypeRecursive qstate (Function ra pa) e reason ml ctx'
        (Pointer a, Function re pe) -> subtypeRecursive qstate a (Function re pe) reason ml ctx'

        (Pointer a, TypeRef FuncRef (L _ _ tid) args) -> do
            ts <- State.gets usTypeSystem
            case TS.lookupType (TS.templateIdBaseName tid) ts of
                Just descr ->
                    let descr' = TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) args)) descr
                    in case descr' of
                        FuncDescr _ _ ret params ->
                            subtypeRecursive qstate (Pointer a) (Pointer (Function ret params)) reason ml ctx'
                        _ -> reportMismatch (BaseMismatch expected actual)
                _ -> reportMismatch (BaseMismatch expected actual)

        (TypeRef FuncRef (L _ _ tid) args, Pointer e) -> do
            ts <- State.gets usTypeSystem
            case TS.lookupType (TS.templateIdBaseName tid) ts of
                Just descr ->
                    let descr' = TS.instantiateDescr 0 TopLevel (Map.fromList (zip (TS.getDescrTemplates descr) args)) descr
                    in case descr' of
                        FuncDescr _ _ ret params ->
                            subtypeRecursive qstate (Function ret params) e reason ml ctx'
                        _ -> reportMismatch (BaseMismatch expected actual)
                _ -> reportMismatch (BaseMismatch expected actual)

        (Function ra pa, Function re pe) -> do
            mRet <- fmap (wrap InFunctionReturn) <$> subtype ra re reason ml ctx'
            let expCount = length (filter (not . isVarArg) pe)
                actCount = length pa
            if actCount < expCount
                then reportError ml ctx' (TooFewArgs expCount actCount) >> reportMismatch (ArityMismatch expCount actCount)
                else if actCount > expCount && not (any isVarArg pe)
                    then reportError ml ctx' (TooManyArgs expCount actCount) >> reportMismatch (ArityMismatch expCount actCount)
                    else do
                        mArgs <- foldM (\m (i, (p_act, p_exp)) -> (m <|>) . fmap (wrap (InFunctionParam i)) <$> subtype p_exp p_act reason ml ctx') Nothing (zip [0..] (zip pa (filter (not . isVarArg) pe)))
                        return $ mRet <|> mArgs

        (TypeRef r1 (L _ _ n1) a1, TypeRef r2 (L _ _ n2) a2)
            | (r1 == r2 || r1 == TS.UnresolvedRef || r2 == TS.UnresolvedRef) && n1 == n2 && length a1 == length a2 ->
                foldM (\m (v1, v2) -> (m <|>) <$> unifyRecursive QualUnshielded v1 v2 reason ml ctx') Nothing (zip a1 a2)

        (BuiltinType b1, BuiltinType b2) | b1 == b2 -> return Nothing
        (Singleton b1 v1, Singleton b2 v2) | b1 == b2 && v1 == v2 -> return Nothing
        (Singleton b1 v1, Singleton b2 v2) | b1 == b2 && v1 /= v2 -> reportMismatch (BaseMismatch expected actual)
        (IntLit (L _ _ v1), Singleton b2 v2) | TS.isInt b2 && (read (T.unpack (TS.templateIdBaseName v1)) :: Integer) == v2 -> return Nothing
        (Singleton b1 v1, IntLit (L _ _ v2)) | TS.isInt b1 && v1 == (read (T.unpack (TS.templateIdBaseName v2)) :: Integer) -> return Nothing
        (Singleton b1 _, BuiltinType b2) | b1 == b2 -> return Nothing
        (BuiltinType b1, Singleton b2 _) | b1 == b2 -> return Nothing

        (TypeRef TS.EnumRef _ _, BuiltinType b) | TS.isInt b -> return Nothing

        (a, e) | a == e -> return Nothing
        (a, e) -> if compatible a e
                    then return Nothing
                    else reportMismatch (BaseMismatch expected actual)
  where
    wrap mctx detail = MismatchDetail expected actual reason (Just (mctx, detail))

subtypePtr :: QualState -> TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
subtypePtr qstate actual expected reason ml ctx = do
    let ctx' = InUnification expected actual reason : ctx
    let reportMismatch d = reportError ml ctx' (TypeMismatch expected actual reason (Just d)) >> return (Just d)
    ab1 <- resolveType =<< applyBindings actual
    eb1 <- resolveType =<< applyBindings expected
    case (ab1, eb1) of
        (Const a, Const e) -> subtypePtr qstate a e reason ml ctx'
        (a, Const e)       -> subtypePtr' qstate True a e reason ml ctx'
        (Const _, _)       -> reportMismatch (MissingQualifier QConst expected actual)
        _                  -> subtypePtr' qstate (isPtrToConst eb1) ab1 eb1 reason ml ctx'
  where
    isPtrToConst = \case
        Pointer e -> isTargetConst e
        Array (Just e) _ -> isTargetConst e
        _ -> False

    isTargetConst = \case
        Fix (QualifiedF qs t) -> QConst `Set.member` qs || isTargetConst t
        Fix (VarF _ t) -> isTargetConst t
        Fix (SizedF t _) -> isTargetConst t
        _ -> False

subtypePtr' :: QualState -> Bool -> TypeInfo 'Local -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify (Maybe (MismatchDetail 'Local))
subtypePtr' qstate isCurrentConst actual expected reason ml ctx = do
    let ctx' = InUnification expected actual reason : ctx
    let reportMismatch d = reportError ml ctx' (TypeMismatch expected actual reason (Just d)) >> return (Just d)
    ab1 <- resolveType =<< applyBindings actual
    eb1 <- resolveType =<< applyBindings expected
    let canBeCovariant = allowCovariance qstate
    let nextQstate = stepQual qstate isCurrentConst
    let subUnify a e = do
            -- Enforce strict aliasing: pointers to different scalars are incompatible.
            case (TS.stripAllWrappers a, TS.stripAllWrappers e) of
                (BuiltinType b1, BuiltinType b2) | b1 /= b2 -> reportMismatch (BaseMismatch e a)
                _ -> if canBeCovariant
                     then subtypeRecursive nextQstate a e reason ml ctx'
                     else unifyRecursive nextQstate a e reason ml ctx'
    case (ab1, eb1) of
        (Pointer a, Pointer e) -> subUnify a e
        (Array (Just a) _, Pointer e) -> subUnify a e
        (Pointer a, Array (Just e) _) -> subUnify a e
        (a, e) -> if canBeCovariant
                    then subtypeRecursive nextQstate a e reason ml ctx'
                    else if compatible a e
                        then return Nothing
                        else reportMismatch (BaseMismatch expected actual)

compatible :: TypeInfo 'Local -> TypeInfo 'Local -> Bool
compatible t1 t2 | t1 == t2 = True
compatible t1 t2 | isNetworkingStruct t1 && isNetworkingStruct t2 = True
compatible t1 t2 | isLPSTR t1 && isPointerToChar t2 = True
compatible t1 t2 | isLPSTR t2 && isPointerToChar t1 = True
compatible (ExternalType (L _ _ n1)) (ExternalType (L _ _ n2)) = TS.templateIdBaseName n1 == TS.templateIdBaseName n2
compatible (BuiltinType NullPtrTy) (Pointer _) = True
compatible (Pointer _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType NullPtrTy) (Nullable _) = True
compatible (Nullable _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType NullPtrTy) (Array _ _) = True
compatible (Array _ _) (BuiltinType NullPtrTy) = True
compatible (BuiltinType NullPtrTy) (Sized _ _) = True
compatible (Sized _ _) (BuiltinType NullPtrTy) = True
compatible (Template _ _) _ = True
compatible _ (Template _ _) = True
compatible (Pointer _) (Array _ _) = True
compatible (Array _ _) (Pointer _) = True
compatible (BuiltinType b1) (BuiltinType b2)
    | b1 == b2 = True
    | TS.isInt b1 && TS.isInt b2 = True
    | b1 == BoolTy && TS.isInt b2 = True
    | TS.isInt b1 && b2 == BoolTy = True
    | otherwise = False
compatible (Singleton b1 v1) (Singleton b2 v2) = b1 == b2 && v1 == v2
compatible (Singleton b1 _) (BuiltinType b2) = compatible (BuiltinType b1) (BuiltinType b2)
compatible (BuiltinType b1) (Singleton b2 _) = compatible (BuiltinType b1) (BuiltinType b2)
compatible (IntLit (L _ _ v1)) (IntLit (L _ _ v2)) = TS.templateIdBaseName v1 == TS.templateIdBaseName v2
compatible (NameLit (L _ _ v1)) (NameLit (L _ _ v2)) = TS.templateIdBaseName v1 == TS.templateIdBaseName v2
compatible (EnumMem (L _ _ v1)) (EnumMem (L _ _ v2)) = TS.templateIdBaseName v1 == TS.templateIdBaseName v2
compatible (IntLit (L _ _ v1)) (Singleton b2 v2) = TS.isInt b2 && (read (T.unpack (TS.templateIdBaseName v1)) :: Integer) == v2
compatible (Singleton b1 v1) (IntLit (L _ _ v2)) = TS.isInt b1 && v1 == (read (T.unpack (TS.templateIdBaseName v2)) :: Integer)
compatible (IntLit _) (BuiltinType b) = TS.isInt b

compatible (Var _ a) e = compatible a e
compatible a (Var _ e) = compatible a e
compatible a e | TS.isConflict a || TS.isConflict e = True
compatible _ _ = False


bind :: TemplateId 'Local -> Maybe (TypeInfo 'Local) -> TypeInfo 'Local -> MismatchReason -> Maybe (Lexeme Text) -> [Context 'Local] -> Unify ()
bind tid index ty reason ml ctx = do
    rep <- applyBindings (Template tid index)
    case rep of
        Template tid' index' -> do
            s <- State.get
            let bindings = usBindings s
            let k = FullTemplate tid' index'

            -- Conflict check across exact/compatible matches using secondary index.
            let related = Map.findWithDefault [] tid' (usBindingsIndex s)
            forM_ related $ \ft@(FullTemplate _ index'') ->
                case Map.lookup ft bindings of
                    Just (existing, _) ->
                        case (index', index'') of
                            (Nothing, Nothing) -> void $ unify existing ty reason ml ctx
                            (Just idx, Just idx')
                                | compatible idx idx' || compatible idx' idx -> void $ unify existing ty reason ml ctx
                            _ -> return ()
                    Nothing -> return ()

            -- Add the binding if not already exactly present
            case Map.lookup k bindings of
                Just (existing, _) -> void $ unify existing ty reason ml ctx
                Nothing -> do
                    case ty of
                        Template tid''' i''' | tid''' == tid' && i''' == index' -> return () -- Exact alias
                        _ | occurs tid' index' ty -> do
                            let prov = FromContext (ErrorInfo ml ctx (TypeMismatch (Template tid' index') ty reason Nothing) [])
                            dtraceM $ "  BIND (Occurs): " ++ show (Template tid' index') ++ " -> " ++ show ty
                            State.modify $ \s' -> s' { usBindings = Map.insert k (ty, prov) (usBindings s')
                                                     , usBindingsIndex = Map.insertWith (++) tid' [k] (usBindingsIndex s') }
                        Unsupported _ -> return ()
                        _ -> do
                            let prov = FromContext (ErrorInfo ml ctx (TypeMismatch (Template tid' index') ty reason Nothing) [])
                            dtraceM $ "  BIND: " ++ show (Template tid' index') ++ " -> " ++ show ty
                            State.modify $ \s' -> s' { usBindings = Map.insert k (ty, prov) (usBindings s')
                                                     , usBindingsIndex = Map.insertWith (++) tid' [k] (usBindingsIndex s') }
        _ -> void $ unify rep ty reason ml ctx


occurs :: TemplateId 'Local -> Maybe (TypeInfo 'Local) -> TypeInfo 'Local -> Bool
occurs tid index ty = snd $ foldFix alg ty
  where
    alg f = (Fix (fmap fst f), (Fix (fmap fst f) == Template tid index) || any snd f)

applyBindings :: TypeInfo 'Local -> Unify (TypeInfo 'Local)
applyBindings ty = resolveChain Set.empty ty

resolveChain :: Set (FullTemplate 'Local) -> TypeInfo 'Local -> Unify (TypeInfo 'Local)
resolveChain seen t@(Fix (TemplateF (FullTemplate tid i))) = do
    bindings <- State.gets usBindings
    let k = FullTemplate tid i
    if Set.member k seen
    then return t
    else case Map.lookup k bindings of
        Just (target, _) -> resolveChain (Set.insert k seen) target
        Nothing          -> case i of
            Nothing -> return t
            Just idx -> case Map.lookup (FullTemplate tid Nothing) bindings of
                Just (baseTarget, _) | not (TS.isConflict baseTarget) -> do
                    baseTarget' <- resolveType baseTarget
                    if TS.isConflict baseTarget' then return t
                    else resolveChain (Set.insert k seen) (TS.indexTemplates idx baseTarget')
                _ -> return t
resolveChain _ t = return t

applyBindingsDeep :: TypeInfo 'Local -> Unify (TypeInfo 'Local)
applyBindingsDeep ty = do
    bindings <- State.gets usBindings
    let graph = Map.map (\(t, _) -> Set.singleton (TG.fromTypeInfo t)) bindings
        initialKeys = TS.collectUniqueTemplateVars [ty]
        resolvedMap = GS.solveAll graph initialKeys
    return $ foldFix (alg resolvedMap) ty
  where
    alg m (TemplateF (FullTemplate tid i)) =
        maybe (Template tid i) TG.toTypeInfo (Map.lookup (FullTemplate tid i) m)
    alg _ f = Fix f

resolveType :: TypeInfo 'Local -> Unify (TypeInfo 'Local)
resolveType ty = do
    ts <- State.gets usTypeSystem
    return $ go ts Set.empty ty
  where
    go ts seen (TypeRef ref l@(L _ _ tid) args) =
        let name = TS.templateIdBaseName tid in
        if Set.member name seen
        then TypeRef ref l (map (go ts seen) args)
        else case TS.lookupType name ts of
            Nothing -> TypeRef ref l (map (go ts seen) args)
            Just descr ->
                let tps = TS.getDescrTemplates descr
                    args' = if null args && not (null tps)
                            then [ TS.instantiate 0 TS.TopLevel (Map.fromList (zip tps args)) (TS.Template t Nothing) | t <- tps ]
                            else args
                    descr' = TS.instantiateDescr 0 TS.TopLevel (Map.fromList (zip tps args')) descr
                in case descr' of
                    AliasDescr _ _ target ->
                        go ts (Set.insert name seen) target
                    FuncDescr _ _ ret params ->
                        go ts (Set.insert name seen) (Function ret params)
                    _ ->
                        let ref' = case descr' of
                                     StructDescr{} -> TS.StructRef
                                     UnionDescr{}  -> TS.UnionRef
                                     EnumDescr{}   -> TS.EnumRef
                                     _             -> TS.IntRef
                        in TypeRef ref' (TS.getDescrLexeme descr') (map (go ts seen) args')
    go ts seen (Fix (TS.VarF _ inner)) = go ts seen inner
    go ts seen (Fix f) = Fix (fmap (go ts seen) f)

reportError :: Maybe (Lexeme Text) -> [Context 'Local] -> TypeError 'Local -> Unify ()
reportError ml ctx err = do
    isFinal <- State.gets usFinalPass
    dtraceM $ "reportError: final=" ++ show isFinal ++ " err=" ++ show err
    when isFinal $ do
        bindings <- State.gets usBindings
        let allTypes = case err of
                TypeMismatch expected actual _ _ -> expected : actual : concatMap getContextTypes ctx
                _ -> concatMap getContextTypes ctx
        let expls = concatMap (P.explainType bindings) allTypes
        State.modify $ \s -> s { usErrors = usErrors s ++ [ErrorInfo ml ctx err (P.dedupDocs expls)] }
  where
    getContextTypes = \case
        InUnification e a _ -> [e, a]
        _ -> []
