{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE MonoLocalBinds      #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RecordWildCards     #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE Strict              #-}
{-# LANGUAGE TupleSections       #-}

module Language.Hic.Refined.Inference
    ( RefinedResult (..)
    , inferRefined
    , ProductState (..)
    ) where

import           Control.Applicative                         ((<|>))
import           Control.Monad                               (join, zipWithM_)
import           Control.Monad.State.Strict                  (State, get, gets,
                                                              modify, runState)
import           Data.Fix                                    (Fix (..), foldFix,
                                                              unFix)
import           Data.Foldable                               (fold)
import           Data.Hashable                               (hash)
import qualified Data.IntMap.Strict                          as IntMap
import           Data.List                                   (find, findIndex,
                                                              nub)
import           Data.Map.Strict                             (Map)
import qualified Data.Map.Strict                             as Map
import           Data.Maybe                                  (fromMaybe,
                                                              mapMaybe)
import qualified Data.Set                                    as Set
import           Data.Text                                   (Text)

import qualified Data.Text                                   as T
import qualified Data.Text.Read                              as TR
import           Data.Word                                   (Word32)

import           Language.Cimple                             (Lexeme (..))
import qualified Language.Cimple                             as C
import           Language.Hic.Core.Errors
import           Language.Hic.Refined.Context
import           Language.Hic.Refined.Inference.Lifter
import           Language.Hic.Refined.Inference.Substitution
import           Language.Hic.Refined.Inference.Translator
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Inference.Utils
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.PathContext
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Solver                 (Constraint (..),
                                                              solve)
import           Language.Hic.Refined.State

import           Language.Hic.Ast                            (CleanupAction (..),
                                                              HicNode (..),
                                                              MatchCase (..),
                                                              Node, NodeF (..),
                                                              ReturnIntent (..),
                                                              TaggedUnionMember (..))
import           Language.Hic.Inference                      (lower)
import           Language.Hic.Inference.Program              (Program (..))
import           Language.Hic.Refined.Transition
import           Language.Hic.Refined.Types

import qualified Language.Hic.TypeSystem.Core.Base           as TS

getHicLoc :: Node (Lexeme Text) -> Maybe (Lexeme Text)
getHicLoc n = case foldFix C.concats n of
    []  -> Nothing
    l:_ -> Just l

-- | Traverses the Hic AST to identify hotspots for refined analysis.
inferRefined :: TS.TypeSystem -> Program (Lexeme Text) -> RefinedResult
inferRefined ts prog =
    let (registry, st) = runState (translateAndCollect ts prog) (emptyTranslatorState ts)
        hotspots = nub $ concatMap (concatMap collectHotspots) (Map.elems (progAsts prog))
        resSolved = solve registry (tsNodes st) (tsConstraints st) (0, 1, 2, 0)
        solverErrs = case resSolved of
                        Right finalRefs ->
                            dtrace ("Final refinements: " ++ show (mrRefinements finalRefs)) []
                        Left ps -> dtrace ("SOLVER FAILED at " ++ show ps) [solverStateToErrorInfo (tsNodes st) ps]
        res = RefinedResult hotspots (tsNodes st) registry resSolved (solverErrs ++ tsErrors st)
    in dtrace ("tsTaggedUnions: " ++ show (Map.keys (tsTaggedUnions st))) res

solverStateToErrorInfo :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> ProductState -> ErrorInfo 'TS.Global
solverStateToErrorInfo nodes ps =
    let loc = psOrigin ps
        file = fromMaybe "unknown" (psFile ps)
        ctx = [InFile file]
        -- Try to determine the error type
        errType = case (Map.lookup (psNodeL ps) nodes, Map.lookup (psNodeR ps) nodes) of
            (Just (AnyRigidNodeF (RReference _ QNonnull' _ _)), _) -> RefinedNullabilityMismatch
            (_, Just (AnyRigidNodeF (RReference _ QNonnull' _ _))) -> RefinedNullabilityMismatch
            (Just (AnyRigidNodeF (RObject (VVariant _) _)), _) -> RefinedVariantMismatch
            (_, Just (AnyRigidNodeF (RObject (VVariant _) _))) -> RefinedVariantMismatch
            -- Fallback for now
            _ -> CustomError "Refined type mismatch detected in fixpoint solver"
    in ErrorInfo loc ctx errType []

addError :: Maybe (Lexeme Text) -> TypeError 'TS.Global -> State TranslatorState ()
addError loc err = modify $ \s ->
    s { tsErrors = ErrorInfo loc [InFile (tsCurrentFile s)] err [] : tsErrors s }

translateAndCollect :: TS.TypeSystem -> Program (Lexeme Text) -> State TranslatorState (Registry Word32)
translateAndCollect ts prog = do
    initialReg <- translateRegistry ts
    reg <- liftImplicitPolymorphism initialReg
    -- Pre-pass: gather all TaggedUnion definitions
    dtraceM ("translateAndCollect: gathering TaggedUnions from " ++ show (Map.size (progAsts prog)) ++ " files")
    mapM_ (mapM_ gatherTaggedUnions) (progAsts prog)
    mapM_ (\(path, ast) -> do
        modify $ \s -> s { tsCurrentFile = path }
        mapM_ (collectRefinements reg (PathContext Map.empty Map.empty)) ast
        ) (Map.toList (progAsts prog))
    return reg

gatherTaggedUnions :: Node (Lexeme Text) -> State TranslatorState ()
gatherTaggedUnions (Fix node) = case node of
    HicNode (TaggedUnion{..}) -> do
        dtraceM ("gatherTaggedUnions: FOUND " ++ show (C.lexemeText tuName))
        let tuInfo = TaggedUnionInfo
                { tuiTagField = C.lexemeText tuTagField
                , tuiUnionField = C.lexemeText tuUnionField
                , tuiMembers = Map.fromList [ (C.lexemeText (tumEnumVal m), C.lexemeText (tumMember m)) | m <- tuMembers ]
                }
        modify (addTaggedUnion (C.lexemeText tuName) tuInfo)
        mapM_ (gatherTaggedUnions . tumType) tuMembers
    CimpleNode f -> mapM_ gatherTaggedUnions f
    HicNode h -> mapM_ gatherTaggedUnions h

getConstantIndex :: Node (Lexeme Text) -> Maybe Integer
getConstantIndex (Fix node) = case node of
    CimpleNode (C.LiteralExpr C.Int l) -> case TR.decimal (C.lexemeText l) of
        Right (i, _) -> Just i
        Left _       -> Nothing
    CimpleNode (C.ParenExpr e) -> getConstantIndex e
    CimpleNode (C.CastExpr _ e) -> getConstantIndex e
    _ -> Nothing

collectRefinements :: Registry Word32 -> PathContext -> Node (Lexeme Text) -> State TranslatorState (Maybe Word32)
collectRefinements reg ctx (Fix node) =
    let loc = getHicLoc (Fix node)
    in case node of
        HicNode h    -> collectRefinementsHic reg ctx loc h
        CimpleNode c -> collectRefinementsCimple reg ctx loc c

linkTypes :: Maybe (Lexeme Text) -> PathContext -> Maybe Word32 -> Maybe Word32 -> State TranslatorState ()
linkTypes loc ctx mL mR = case (mL, mR) of
    (Just lId, Just rId) -> modify (addConstraintCoerced loc ctx rId lId)
    _                    -> return ()

collectRefinementsHic :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> HicNode (Lexeme Text) (Node (Lexeme Text)) -> State TranslatorState (Maybe Word32)
collectRefinementsHic reg ctx loc = \case
    Match obj _isPtr _tf cases def -> do
        dtraceM "collectRefinements: ENTERING Match"
        mObjId <- collectRefinements reg ctx obj
        case mObjId of
            Just objId -> do
                st <- get
                let tyName = getObjectTypeName st objId
                dtraceM ("Match: obj=" ++ show (matchObjPath obj) ++ ", objId=" ++ show objId ++ ", tyName=" ++ show tyName ++ ", inTaggedUnions=" ++ show (maybe False (`Map.member` tsTaggedUnions st) tyName))
                case tyName >>= \n -> Map.lookup n (tsTaggedUnions st) of
                    Just tu -> mapM_ (collectMatchCase reg ctx obj objId tu) cases
                    _ -> mapM_ (collectRefinements reg ctx . mcBody) cases
            Nothing -> mapM_ (collectRefinements reg ctx . mcBody) cases

        _ <- traverse (collectRefinements reg ctx) def
        return Nothing

    TaggedUnion{..} -> do
        let tuInfo = TaggedUnionInfo
                { tuiTagField = C.lexemeText tuTagField
                , tuiUnionField = C.lexemeText tuUnionField
                , tuiMembers = Map.fromList [ (C.lexemeText (tumEnumVal m), C.lexemeText (tumMember m)) | m <- tuMembers ]
                }
        modify (addTaggedUnion (C.lexemeText tuName) tuInfo)
        mapM_ (collectRefinements reg ctx . tumType) tuMembers
        return Nothing

    TaggedUnionMemberAccess obj uf field -> do
        mObjId <- collectRefinements reg ctx obj
        st <- get
        dtraceM ("TaggedUnionMemberAccess: objPath=" ++ show (matchObjPath obj) ++ ", uf=" ++ show (C.lexemeText uf) ++ ", field=" ++ show (C.lexemeText field))
        case (mObjId, matchObjPath obj) of
            (Just objId, matchPath) -> do
                let fieldName = C.lexemeText field
                let ufName = C.lexemeText uf
                case matchPath of
                    Just path' -> do
                        let path = extendPath (FieldStep ufName) path'
                        dtraceM ("Checking path: " ++ show path ++ " in ctx " ++ show (Map.keys (pcRefinements ctx)))
                        case Map.lookup path (pcRefinements ctx) of
                            Just (EqVariant idx) -> do
                                mUId <- getMemberId reg objId ufName
                                case mUId of
                                    Just uId ->
                                        case getMemberIndex reg st uId fieldName of
                                            Just actualIdx | fromIntegral actualIdx == idx ->
                                                getMemberId reg uId fieldName
                                            Just actualIdx -> do
                                                dtraceM ("Refined variant conflict: expected " ++ show idx ++ ", got " ++ show actualIdx)
                                                -- Refined to a different variant: Conflict!
                                                addError loc RefinedVariantMismatch
                                                return Nothing
                                            Nothing -> return Nothing
                                    Nothing -> return Nothing
                            _ -> do
                                -- No variant refinement in context, fallback to raw access
                                mUId <- getMemberId reg objId ufName
                                case mUId of
                                    Just uId -> getMemberId reg uId fieldName
                                    Nothing  -> return Nothing
                    Nothing -> do
                        mUId <- getMemberId reg objId ufName
                        case mUId of
                            Just uId -> getMemberId reg uId fieldName
                            Nothing  -> return Nothing
            _ -> return Nothing

    Scoped r b c -> do
        _ <- collectRefinements reg ctx r
        _ <- collectRefinements reg ctx b
        mapM_ (collectRefinements reg ctx . cleanupBody) c
        return Nothing

    Raise out val retIntent -> do
        _ <- traverse (collectRefinements reg ctx) out
        mVal <- collectRefinements reg ctx val
        st <- get
        linkTypes loc ctx (tsCurrentReturn st) mVal
        case retIntent of
            ReturnValue v -> do
                _ <- collectRefinements reg ctx v
                return ()
            ReturnError e -> do
                _ <- collectRefinements reg ctx e
                return ()
            ReturnVoid    -> return ()
        return Nothing

    Transition fr to -> do
        _ <- collectRefinements reg ctx fr
        _ <- collectRefinements reg ctx to
        return Nothing

    TaggedUnionGet _ p o _isPtr _tf _tv _uf _m e -> do
        _ <- collectRefinements reg ctx p
        _ <- collectRefinements reg ctx o
        _ <- collectRefinements reg ctx e
        return Nothing

    TaggedUnionGetTag _ p o _isPtr _tf -> do
        _ <- collectRefinements reg ctx p
        _ <- collectRefinements reg ctx o
        return Nothing

    TaggedUnionConstruct o _isPtr _ty _tf _tv _uf _m d -> do
        _ <- collectRefinements reg ctx o
        _ <- collectRefinements reg ctx d
        return Nothing

    ForEach _is in' c s cons b _hi -> do
        _ <- collectRefinements reg ctx in'
        _ <- collectRefinements reg ctx c
        _ <- collectRefinements reg ctx s
        mapM_ (collectRefinements reg ctx) cons
        _ <- collectRefinements reg ctx b
        return Nothing

    Find _i in' c s con p f m -> do
        _ <- collectRefinements reg ctx in'
        _ <- collectRefinements reg ctx c
        _ <- collectRefinements reg ctx s
        _ <- collectRefinements reg ctx con
        _ <- collectRefinements reg ctx p
        _ <- collectRefinements reg ctx f
        _ <- traverse (collectRefinements reg ctx) m
        return Nothing

    IterationElement _ container -> do
        mConId <- collectRefinements reg ctx container
        case mConId of
            Just conId -> do
                mNode <- lookThroughVariables conId
                case mNode of
                    Just (AnyRigidNodeF (RReference (Arr eId _) _ _ _)) -> do
                        instId <- refreshInstance loc eId
                        modify (\s -> s { tsConstraints = CInherit instId eId loc (tsCurrentFile s) : tsConstraints s })
                        return (Just instId)
                    Just (AnyRigidNodeF (RReference (Ptr (TargetObject eId)) _ _ _)) -> do
                        instId <- refreshInstance loc eId
                        modify (\s -> s { tsConstraints = CInherit instId eId loc (tsCurrentFile s) : tsConstraints s })
                        return (Just instId)
                    _ -> return Nothing
            Nothing -> return Nothing

    IterationIndex i -> do
        st <- get
        return $ Map.lookup (C.lexemeText i) (tsVars st)

collectRefinementsCimple :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> State TranslatorState (Maybe Word32)
collectRefinementsCimple reg ctx loc node =
    fromMaybe (error $ "Incomplete Inference: unhandled CimpleNode: " ++ show (Fix (CimpleNode node))) $
        collectRefinementsCimpleType reg ctx node <|>
        collectRefinementsCimpleDecl reg ctx loc node <|>
        collectRefinementsCimpleExpr reg ctx loc node <|>
        collectRefinementsCimpleStmt reg ctx loc node <|>
        collectRefinementsCimpleMisc reg ctx loc node

collectRefinementsCimpleType :: Registry Word32 -> PathContext -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> Maybe (State TranslatorState (Maybe Word32))
collectRefinementsCimpleType reg ctx = \case
        C.TyBitwise t -> Just $ collectRefinements reg ctx t
        C.TyForce t -> Just $ collectRefinements reg ctx t
        C.TyConst t -> Just $ collectRefinements reg ctx t
        C.TyOwner t -> Just $ collectRefinements reg ctx t
        C.TyNonnull t -> Just $ collectRefinements reg ctx t
        C.TyNullable t -> Just $ collectRefinements reg ctx t

        C.TyStd l -> Just $ Just <$> translateType (TS.builtin l)
        C.TyStruct l -> Just $ Just <$> translateType (TS.TypeRef TS.StructRef (fmap TS.TIdName l) [])
        C.TyUnion l -> Just $ Just <$> translateType (TS.TypeRef TS.UnionRef (fmap TS.TIdName l) [])
        C.TyFunc l -> Just $ Just <$> translateType (TS.TypeRef TS.FuncRef (fmap TS.TIdName l) [])
        C.TyUserDefined l -> Just $ do
            st <- get
            let name = C.lexemeText l
            case TS.lookupType name (tsTypeSystem st) of
                Just (TS.AliasDescr _ _ target) -> Just <$> translateType target
                _ -> Just <$> translateType (TS.TypeRef TS.UnresolvedRef (fmap TS.TIdName l) [])

        C.NonNull _ _ e -> Just $ collectRefinements reg ctx e
        C.NonNullParam e -> Just $ collectRefinements reg ctx e
        C.NullableParam e -> Just $ collectRefinements reg ctx e
        _ -> Nothing

collectRefinementsCimpleDecl :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> Maybe (State TranslatorState (Maybe Word32))
collectRefinementsCimpleDecl reg ctx loc = \case
        C.FunctionDecl _ protoNode -> Just $ do
            st <- get
            case lower protoNode of
                Fix (C.FunctionPrototype _ name _) -> do
                    let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower protoNode)
                    nid <- translateType tyInfo
                    modify (addFunction (C.lexemeText name) nid)
                    return (Just nid)
                _ -> return Nothing

        C.FunctionDefn _ proto body -> Just $ do
            st <- get
            case lower proto of
                Fix (C.FunctionPrototype ret name params) -> do
                    dtraceM ("collectRefinements: processing function " ++ show (C.lexemeText name))
                    let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower proto)
                    nid <- translateType tyInfo
                    modify (addFunction (C.lexemeText name) nid)

                    let retTyInfo = nodeToTypeInfo (tsTypeSystem st) ret
                    retNid <- case retTyInfo of
                        Fix (TS.BuiltinTypeF TS.VoidTy) -> return Nothing
                        _ -> Just <$> translateType retTyInfo

                    let oldRet = tsCurrentReturn st
                    modify $ \s -> s { tsCurrentReturn = retNid }

                    stPostRet <- get
                    let paramIds = case Map.lookup nid (tsNodes stPostRet) of
                            Just (AnyRigidNodeF (RFunction pIds _)) -> pIds
                            _                                       -> []

                    -- Bind parameters
                    zipWithM_ (\pId pDecl -> case pDecl of
                        Fix (C.VarDecl ty pName _) -> do
                            st' <- get
                            let pTyInfo = nodeToTypeInfo (tsTypeSystem st') ty
                            pNid <- translateType pTyInfo
                            pNid' <- refreshInstance loc pNid
                            -- LINK: Propagate body refinements to signature
                            modify (addConstraintCoerced loc ctx pId pNid')
                            modify (addVar (C.lexemeText pName) pNid')
                        _ -> return ()) paramIds params

                    _ <- collectRefinements reg ctx body
                    modify $ \s -> s { tsCurrentReturn = oldRet }
                    return (Just nid)
                _ -> return Nothing

        C.VarDecl ty name dims -> Just $ do
            st <- get
            let baseTy = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            let tyInfo = if null dims then baseTy else TS.Array (Just baseTy) (map (nodeToTypeInfo (tsTypeSystem st) . lower) dims)
            nid <- translateType tyInfo
            nid' <- refreshInstance loc nid
            modify (addVar (C.lexemeText name) nid')
            return (Just nid')

        C.Typedef ty _ _ -> Just $ collectRefinements reg ctx ty >> return Nothing
        C.TypedefFunction{} -> Just $ return Nothing
        C.Struct _ fields -> Just $ mapM_ (collectRefinements reg ctx) fields >> return Nothing
        C.Union _ fields -> Just $ mapM_ (collectRefinements reg ctx) fields >> return Nothing
        C.EnumDecl _ decls _ -> Just $ mapM_ (collectRefinements reg ctx) decls >> return Nothing
        C.EnumConsts _ decls -> Just $ mapM_ (collectRefinements reg ctx) decls >> return Nothing
        C.Enumerator _ mInit -> Just $ traverse (collectRefinements reg ctx) mInit >> return Nothing
        C.MemberDecl ty _ -> Just $ collectRefinements reg ctx ty >> return Nothing
        C.AggregateDecl ty -> Just $ collectRefinements reg ctx ty >> return Nothing
        C.CallbackDecl _ _ -> Just $ return Nothing

        C.ConstDecl ty name -> Just $ do
            st <- get
            let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            nid <- translateTypePhysical tyInfo
            modify (addVar (C.lexemeText name) nid)
            return (Just nid)

        C.ConstDefn _ ty name init' -> Just $ do
            st <- get
            let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            nid <- translateTypePhysical tyInfo
            modify (addVar (C.lexemeText name) nid)
            mInitId <- collectRefinements reg ctx init'
            case mInitId of
                Just iId -> modify (addConstraintCoerced loc ctx nid iId)
                Nothing  -> return ()
            return (Just nid)

        C.VLA ty name size -> Just $ do
            st <- get
            let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            nid <- translateType tyInfo
            arrId <- register $ AnyRigidNodeF (RReference (Arr nid []) QUnspecified QNonOwned' (Quals False False))
            modify (addVar (C.lexemeText name) arrId)
            _ <- collectRefinements reg ctx size
            return (Just arrId)
        _ -> Nothing

collectRefinementsCimpleExpr :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> Maybe (State TranslatorState (Maybe Word32))
collectRefinementsCimpleExpr reg ctx loc = \case
        C.AssignExpr lhs _ rhs -> Just $ do
            mLhs <- collectRefinements reg ctx lhs
            mRhs <- collectRefinements reg ctx rhs
            case (mLhs, mRhs) of
                (Just lId, Just rId) -> do
                    modify (addConstraintCoerced loc ctx rId lId)
                _ -> return ()
            return mLhs

        C.VarExpr l -> Just $ do
            st <- get
            let name = C.lexemeText l
            case Map.lookup name (tsVars st) <|> Map.lookup name (tsFunctions st) of
                Just nid -> case Map.lookup nid (tsNodes st) of
                    Just (AnyRigidNodeF (RFunction argIds ret)) ->
                        -- Implicit decay: function name as value becomes a pointer to the function
                        Just <$> register (AnyRigidNodeF (RReference (Ptr (TargetFunction argIds ret)) QNonnull' QNonOwned' (Quals False False)))
                    _ -> return (Just nid)
                Nothing -> return Nothing

        C.MemberAccess obj field -> Just $ do
            mObjId <- collectRefinements reg ctx obj
            case mObjId of
                Just objId -> getMemberId reg objId (C.lexemeText field)
                Nothing    -> return Nothing

        C.PointerAccess obj field -> Just $ do
            mObjId <- collectRefinements reg ctx obj
            case mObjId of
                Just objId -> do
                    -- Witness Enforcement: Pointer access requires Nonnull.
                    nonnullPtr <- translateType (TS.Nonnull (TS.Pointer (TS.builtin (L (C.AlexPn 0 0 0) C.IdVar "void"))))
                    modify (addConstraint loc ctx nonnullPtr objId)
                    getMemberId reg objId (C.lexemeText field)
                Nothing    -> return Nothing

        C.UnaryExpr op e -> Just $ do
            mId <- collectRefinements reg ctx e
            mNode <- case mId of
                Just nid -> lookThroughVariables nid
                Nothing  -> return Nothing
            case (op, mId) of
                (C.UopIncr, Just _) | not (isNumeric mNode) -> do
                    addError loc (CustomError "Increment operator not supported on pointers in refined analysis")
                    return Nothing
                (C.UopDecr, Just _) | not (isNumeric mNode) -> do
                    addError loc (CustomError "Decrement operator not supported on pointers in refined analysis")
                    return Nothing
                (C.UopIncr, _) -> return mId
                (C.UopDecr, _) -> return mId
                (C.UopAddress, Just nid) -> do
                    st <- get
                    case Map.lookup nid (tsNodes st) of
                        Just (AnyRigidNodeF (RFunction argIds ret)) ->
                            Just <$> register (AnyRigidNodeF (RReference (Ptr (TargetFunction argIds ret)) QNonnull' QNonOwned' (Quals False False)))
                        _ ->
                            Just <$> register (AnyRigidNodeF (RReference (Ptr (TargetObject nid)) QNonnull' QNonOwned' (Quals False False)))
                (C.UopDeref, Just nid) -> do
                    -- Witness Enforcement: Dereferencing requires the pointer to be Nonnull.
                    nonnullPtr <- translateType (TS.Nonnull (TS.Pointer (TS.builtin (L (C.AlexPn 0 0 0) C.IdVar "void"))))
                    modify (addConstraint loc ctx nonnullPtr nid)

                    mDerefNode <- lookThroughVariables nid
                    case mDerefNode of
                        Just (AnyRigidNodeF (RReference (Ptr (TargetObject oId)) _ _ _)) -> return (Just oId)
                        Just (AnyRigidNodeF (RReference (Ptr (TargetOpaque tid)) _ _ quals)) ->
                            Just <$> register (AnyRigidNodeF (RObject (VVar tid Nothing) quals))
                        Just (AnyRigidNodeF (RTerminal SBottom)) -> return (Just 2) -- SConflict (Witness of illegal operation)
                        _ -> return (Just 2) -- SConflict (Witness of illegal operation)
                _ -> return mId

        C.BinaryExpr lhs op rhs -> Just $ do
            mLhs <- collectRefinements reg ctx lhs
            mRhs <- collectRefinements reg ctx rhs
            mNodeL <- case mLhs of { Just nid -> lookThroughVariables nid; Nothing -> return Nothing }
            mNodeR <- case mRhs of { Just nid -> lookThroughVariables nid; Nothing -> return Nothing }
            st <- get
            case (op, mLhs, mRhs) of
                (C.BopPlus, Just _, Just _) | not (isNumeric mNodeL) || not (isNumeric mNodeR) -> do
                    -- Pointer arithmetic forbidden (Section 2.D)
                    addError loc (CustomError "Pointer arithmetic not supported in refined analysis")
                    return Nothing
                (C.BopMinus, Just _, Just _) | not (isNumeric mNodeL) || not (isNumeric mNodeR) -> do
                    -- Pointer subtraction forbidden (Section 2.H)
                    addError loc (CustomError "Pointer subtraction not supported in refined analysis")
                    return Nothing
                (C.BopMul, Just lId, Just rId) -> do
                    -- Handle n * sizeof(T)
                    let checkConst iId = case Map.lookup iId (tsNodes st) of
                            Just (AnyRigidNodeF (RObject (VSingleton _ v) _)) -> Just v
                            _ -> Nothing
                        checkProp iId = case Map.lookup iId (tsNodes st) of
                            Just (AnyRigidNodeF (RObject (VProperty _ _) _)) -> Just iId
                            _ -> Nothing
                    case (checkConst lId, checkProp rId) of
                        (Just n, Just pId) -> Just <$> register (AnyRigidNodeF (RObject (VSizeExpr [(pId, n)]) (Quals True True)))
                        _ -> case (checkProp lId, checkConst rId) of
                            (Just pId, Just n) -> Just <$> register (AnyRigidNodeF (RObject (VSizeExpr [(pId, n)]) (Quals True True)))
                            _ -> return Nothing
                _ | op `elem` [C.BopNe, C.BopEq, C.BopLt, C.BopLe, C.BopGt, C.BopGe, C.BopAnd, C.BopOr] ->
                    Just <$> translateType (Fix (TS.BuiltinTypeF TS.BoolTy))
                _ -> return (mLhs <|> mRhs)

        C.TernaryExpr cond then' else' -> Just $ do
            _ <- collectRefinements reg ctx cond
            mThen <- collectRefinements reg ctx then'
            mElse <- collectRefinements reg ctx else'
            case (mThen, mElse) of
                (Just tId, Just eId) -> do
                    modify (addConstraintCoerced loc ctx tId eId)
                    return (Just tId)
                _ -> return (mThen <|> mElse)

        C.ArrayAccess obj idx -> Just $ do
            mObjId <- collectRefinements reg ctx obj
            _ <- collectRefinements reg ctx idx
            dtraceM ("ArrayAccess: mObjId=" ++ show mObjId ++ ", idx=" ++ show (getConstantIndex idx))
            case (mObjId, getConstantIndex idx) of
                (Just objId, Just i) -> do
                    st <- get
                    case Map.lookup (objId, i) (tsArrayInstances st) of
                        Just instId -> do
                            dtraceM ("ArrayAccess: found cached instId=" ++ show instId)
                            return (Just instId)
                        Nothing -> do
                            mNode <- lookThroughVariables objId
                            dtraceM ("ArrayAccess: lookThroughVariables(array)=" ++ show (fmap (fmap (const ())) mNode))
                            case mNode of
                                Just (AnyRigidNodeF (RReference (Arr eId _) _ _ _)) -> do
                                    instId <- refreshInstance loc eId
                                    dtraceM ("ArrayAccess: created fresh instId=" ++ show instId ++ " from eId=" ++ show eId)
                                    modify (\s -> s { tsConstraints = CInherit instId eId loc (tsCurrentFile s) : tsConstraints s })
                                    modify $ \s -> s { tsArrayInstances = Map.insert (objId, i) instId (tsArrayInstances s) }
                                    return (Just instId)
                                Just (AnyRigidNodeF (RReference (Ptr (TargetObject eId)) _ _ _)) -> do
                                    instId <- refreshInstance loc eId
                                    modify (\s -> s { tsConstraints = CInherit instId eId loc (tsCurrentFile s) : tsConstraints s })
                                    modify $ \s -> s { tsArrayInstances = Map.insert (objId, i) instId (tsArrayInstances s) }
                                    return (Just instId)
                                _ -> return Nothing
                (Just objId, Nothing) -> do
                    mNode <- lookThroughVariables objId
                    case mNode of
                        Just (AnyRigidNodeF (RReference (Arr eId _) _ _ _)) -> do
                            instId <- refreshInstance loc eId
                            modify (addConstraint loc ctx instId eId)
                            return (Just instId)
                        Just (AnyRigidNodeF (RReference (Ptr (TargetObject eId)) _ _ _)) -> do
                            instId <- refreshInstance loc eId
                            modify (addConstraint loc ctx instId eId)
                            return (Just instId)
                        _ -> return Nothing
                _ -> return Nothing

        C.InitialiserList exprs -> Just $ do
            -- For now, just collect refinements from members.
            -- We should really map these to struct/array members.
            mapM_ (collectRefinements reg ctx) exprs
            return Nothing

        C.ParenExpr e -> Just $ collectRefinements reg ctx e

        C.LiteralExpr ty l -> Just $ do
            let t = C.lexemeText l
            case ty of
                C.ConstId | t == "nullptr" -> do
                    targetId <- translateType (Fix (TS.QualifiedF (Set.singleton TS.QConst) (Fix (TS.BuiltinTypeF TS.NullPtrTy))))
                    Just <$> register (AnyRigidNodeF (RReference (Ptr (TargetObject targetId)) QNullable' QNonOwned' (Quals False False)))
                C.Int ->
                    Just <$> translateType (TS.IntLit (fmap TS.TIdName l))
                C.Float ->
                    if "f" `T.isSuffixOf` t
                    then Just <$> translateType (Fix (TS.BuiltinTypeF TS.F32Ty))
                    else Just <$> translateType (Fix (TS.BuiltinTypeF TS.F64Ty))
                C.Bool ->
                    Just <$> translateType (Fix (TS.BuiltinTypeF TS.BoolTy))
                C.Char ->
                    Just <$> translateType (Fix (TS.BuiltinTypeF TS.CharTy))
                C.String -> do
                    -- String literals point to physically constant memory.
                    targetId <- register (AnyRigidNodeF (RObject (VBuiltin CharTy) (Quals True True)))
                    Just <$> register (AnyRigidNodeF (RReference (Ptr (TargetObject targetId)) QNonnull' QNonOwned' (Quals True True)))
                _ -> return Nothing

        C.SizeofExpr e -> Just $ do
            mId <- collectRefinements reg ctx e
            case mId of
                Just nid -> Just <$> register (AnyRigidNodeF (RObject (VProperty nid PSize) (Quals True True)))
                Nothing -> return Nothing

        C.SizeofType ty -> Just $ do
            st <- get
            let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            nid <- translateType tyInfo
            Just <$> register (AnyRigidNodeF (RObject (VProperty nid PSize) (Quals True True)))

        C.CastExpr ty e -> Just $ do
            mId <- collectRefinements reg ctx e
            st <- get
            let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            newId <- translateType tyInfo
            newId' <- refreshInstance loc newId
            case mId of
                Just oldId ->
                    modify (addConstraintCoerced loc ctx newId' oldId)
                Nothing -> return ()
            return (Just newId')

        C.FunctionCall func args -> Just $ do
            mFuncId <- collectRefinements reg ctx func
            mArgIds <- mapM (collectRefinements reg ctx) args
            st <- get
            case mFuncId of
                Just fId -> do
                    -- Witness Enforcement: Function call requires Nonnull.
                    nonnullPtr <- translateType (TS.Nonnull (TS.Pointer (TS.builtin (L (C.AlexPn 0 0 0) C.IdVar "void"))))
                    modify (addConstraint loc ctx nonnullPtr fId)

                    case Map.lookup fId (tsNodes st) of
                        Just (AnyRigidNodeF (RReference (Ptr (TargetFunction paramIds ret)) _ _ _)) -> do
                            dtraceM ("Indirect Call to " ++ show fId ++ " with " ++ show (length paramIds) ++ " params")
                            (paramIds', ret', nodeMapping) <- refreshSignature paramIds ret
                            -- Link instantiated variables back to origins: Information flows def -> call-site (One-Way)
                            _ <- Map.traverseWithKey (\origId freshId -> modify $ \s -> s { tsConstraints = CInherit freshId origId loc (tsCurrentFile s) : tsConstraints s }) nodeMapping

                            case matchObjPath func of
                                Just (SymbolicPath (VarRoot name) []) ->
                                    hardenCall name paramIds' mArgIds ret' loc ctx
                                _ -> return ()

                            zipWithM_ (\p a -> case a of
                                Just aId -> modify (addConstraintCoerced loc ctx aId p)
                                Nothing  -> return ()) paramIds' mArgIds
                            case ret' of
                                RetVal rId -> return (Just rId)
                                RetVoid    -> return Nothing
                        Just (AnyRigidNodeF (RFunction paramIds ret)) -> do
                            dtraceM ("Direct Call to " ++ show fId ++ " with " ++ show (length paramIds) ++ " params")
                            (paramIds', ret', nodeMapping) <- refreshSignature paramIds ret
                            -- Link instantiated variables back to origins: One-Way inheritance
                            _ <- Map.traverseWithKey (\origId freshId -> modify $ \s -> s { tsConstraints = CInherit freshId origId loc (tsCurrentFile s) : tsConstraints s }) nodeMapping

                            case matchObjPath func of
                                Just (SymbolicPath (VarRoot name) []) ->
                                    hardenCall name paramIds' mArgIds ret' loc ctx
                                _ -> return ()

                            zipWithM_ (\p a -> case a of
                                Just aId -> modify (addConstraintCoerced loc ctx aId p)
                                Nothing  -> return ()) paramIds' mArgIds
                            case ret' of
                                RetVal rId -> return (Just rId)
                                RetVoid    -> return Nothing
                        Just (AnyRigidNodeF (RTerminal SBottom)) -> return (Just 2) -- SConflict
                        _ -> return Nothing
                _ -> return Nothing

        C.CompoundLiteral ty init' -> Just $ do
            st <- get
            let tyInfo = nodeToTypeInfo (tsTypeSystem st) (lower ty)
            nid <- translateType tyInfo
            _ <- collectRefinements reg ctx init'
            return (Just nid)

        C.CommentExpr _ e -> Just $ collectRefinements reg ctx e >> return Nothing
        _ -> Nothing

collectRefinementsCimpleStmt :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> Maybe (State TranslatorState (Maybe Word32))
collectRefinementsCimpleStmt reg ctx loc = \case
        C.MacroBodyStmt e -> Just $ collectRefinements reg ctx e >> return Nothing
        C.MacroBodyFunCall e -> Just $ collectRefinements reg ctx e >> return Nothing
        C.MacroParam{} -> Just $ return Nothing

        C.VarDeclStmt d mInit -> Just $ do
            mVarId <- collectRefinements reg ctx d
            mInitId <- traverse (collectRefinements reg ctx) mInit
            case (mVarId, join mInitId) of
                (Just vId, Just iId) -> modify (addConstraintCoerced loc ctx iId vId)
                _                    -> return ()
            return mVarId

        C.ExprStmt e -> Just $ collectRefinements reg ctx e >> return Nothing
        C.CompoundStmt ss -> Just $ mapM_ (collectRefinements reg ctx) ss >> return Nothing
        C.Group ss -> Just $ mapM_ (collectRefinements reg ctx) ss >> return Nothing
        C.ExternC ss -> Just $ mapM_ (collectRefinements reg ctx) ss >> return Nothing

        C.Return mVal -> Just $ do
            mValId <- traverse (collectRefinements reg ctx) mVal
            st <- get
            case (tsCurrentReturn st, join mValId) of
                (Just rId, Just vId) -> modify (addConstraintCoerced loc ctx vId rId)
                _                    -> return ()
            return Nothing

        C.SwitchStmt obj cases -> Just $ do
            _ <- collectRefinements reg ctx obj
            mapM_ (collectRefinements reg ctx) cases
            return Nothing

        C.IfStmt cond then' mElse -> Just $ do
            _ <- collectRefinements reg ctx cond
            _ <- collectRefinements reg ctx then'
            _ <- traverse (collectRefinements reg ctx) mElse
            return Nothing

        C.ForStmt init' cond incr body -> Just $ do
            _ <- collectRefinements reg ctx init'
            _ <- collectRefinements reg ctx cond
            _ <- collectRefinements reg ctx incr
            _ <- collectRefinements reg ctx body
            return Nothing

        C.WhileStmt cond body -> Just $ do
            _ <- collectRefinements reg ctx cond
            _ <- collectRefinements reg ctx body
            return Nothing

        C.DoWhileStmt body cond -> Just $ do
            _ <- collectRefinements reg ctx body
            _ <- collectRefinements reg ctx cond
            return Nothing

        C.Case _ body -> Just $ collectRefinements reg ctx body >> return Nothing
        C.Default body -> Just $ collectRefinements reg ctx body >> return Nothing

        C.Label _ e -> Just $ collectRefinements reg ctx e >> return Nothing
        C.Goto{} -> Just $ return Nothing
        C.Break -> Just $ return Nothing
        C.Continue -> Just $ return Nothing
        _ -> Nothing

collectRefinementsCimpleMisc :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> Maybe (State TranslatorState (Maybe Word32))
collectRefinementsCimpleMisc reg ctx _loc = \case
        C.Ellipsis -> Just $ return Nothing
        C.DeclSpecArray _ mSize -> Just $ traverse (collectRefinements reg ctx) mSize >> return Nothing

        C.LicenseDecl{} -> Just $ return Nothing
        C.CopyrightDecl{} -> Just $ return Nothing
        C.Comment{} -> Just $ return Nothing
        C.CommentSection start decls end -> Just $ do
            _ <- collectRefinements reg ctx start
            mapM_ (collectRefinements reg ctx) decls
            _ <- collectRefinements reg ctx end
            return Nothing
        C.CommentSectionEnd{} -> Just $ return Nothing
        C.Commented _ e -> Just $ collectRefinements reg ctx e >> return Nothing
        C.CommentInfo{} -> Just $ return Nothing

        C.PreprocInclude{} -> Just $ return Nothing
        C.PreprocDefine{} -> Just $ return Nothing
        C.PreprocDefineConst{} -> Just $ return Nothing
        C.PreprocDefineMacro{} -> Just $ return Nothing
        C.PreprocIf _ ss1 ss2 -> Just $ do
            mapM_ (collectRefinements reg ctx) ss1
            _ <- collectRefinements reg ctx ss2
            return Nothing
        C.PreprocIfdef _ ss1 ss2 -> Just $ do
            mapM_ (collectRefinements reg ctx) ss1
            _ <- collectRefinements reg ctx ss2
            return Nothing
        C.PreprocIfndef _ ss1 ss2 -> Just $ do
            mapM_ (collectRefinements reg ctx) ss1
            _ <- collectRefinements reg ctx ss2
            return Nothing
        C.PreprocElse ss -> Just $ mapM_ (collectRefinements reg ctx) ss >> return Nothing
        C.PreprocElif _ ss1 ss2 -> Just $ do
            mapM_ (collectRefinements reg ctx) ss1
            _ <- collectRefinements reg ctx ss2
            return Nothing
        C.PreprocUndef{} -> Just $ return Nothing
        C.PreprocDefined{} -> Just $ return Nothing
        C.PreprocScopedDefine _ ss1 ss2 -> Just $ do
            mapM_ (collectRefinements reg ctx) ss1
            _ <- collectRefinements reg ctx ss2
            return Nothing

        C.StaticAssert{} -> Just $ return Nothing

        C.AttrPrintf _ _ e -> Just $ collectRefinements reg ctx e
        _ -> Nothing


resolveVVar :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> [Constraint] -> Word32 -> Word32
resolveVVar nodes constraints = go Set.empty
  where
    go visited nid
        | nid `Set.member` visited = nid
        | otherwise =
            case Map.lookup nid nodes of
                Just (AnyRigidNodeF (RObject (VVar _ _) _)) ->
                    let isMeetTarget = \case
                            CSubtype l' r' PMeet _ _ _ _ _ _ | l' == nid -> Just r'
                            _ -> Nothing
                        isJoinTarget = \case
                            CSubtype l' r' PJoin _ _ _ _ _ _ | l' == nid -> Just r'
                            _ -> Nothing
                        isInheritTarget = \case
                            CInherit l' r' _ _ | l' == nid -> Just r'
                            _ -> Nothing
                    in case mapMaybe isMeetTarget constraints ++ mapMaybe isJoinTarget constraints ++ mapMaybe isInheritTarget constraints of
                        (targetId:_) -> go (Set.insert nid visited) targetId
                        []           -> nid
                _ -> nid

lookThroughVariables :: Word32 -> State TranslatorState (Maybe (AnyRigidNodeF TemplateId Word32))
lookThroughVariables nid = do
    st <- get
    let resId = resolveVVar (tsNodes st) (tsConstraints st) nid
    return $ Map.lookup resId (tsNodes st)

followToNominal :: TranslatorState -> Word32 -> Maybe (Lexeme TemplateId, [Word32])
followToNominal st nid =
    let resId = resolveVVar (tsNodes st) (tsConstraints st) nid
    in case Map.lookup resId (tsNodes st) of
        Just (AnyRigidNodeF (RObject (VNominal l ps) _)) -> Just (l, ps)
        Just (AnyRigidNodeF (RObject (VExistential _ bodyId) _)) -> followToNominal st bodyId
        Just (AnyRigidNodeF (RReference (Ptr (TargetObject nid')) _ _ _)) -> followToNominal st nid'
        _ -> Nothing

getObjectTypeName :: TranslatorState -> Word32 -> Maybe Text
getObjectTypeName st nid =
    case followToNominal st nid of
        Just (l, _) -> case C.lexemeText l of
            TIdName n -> Just n
            _         -> Nothing
        Nothing -> Nothing

getMemberId :: Registry Word32 -> Word32 -> Text -> State TranslatorState (Maybe Word32)
getMemberId reg nid fieldName = do
    st <- get
    dtraceM ("getMemberId: entry nid=" ++ show nid ++ ", fieldName=" ++ show fieldName)
    let isBot' = case Map.lookup nid (tsNodes st) of
            Just (AnyRigidNodeF (RTerminal SBottom)) -> True
            _                                        -> False
    if isBot'
    then dtrace ("getMemberId: nid=" ++ show nid ++ " is SBottom, returning SConflict") $ return (Just 2)
    else do
        mNode <- lookThroughVariables nid
        case mNode of
            Just (AnyRigidNodeF (RObject (VNominal l params) _)) ->
                let tyName = case C.lexemeText l of { TIdName n -> n; _ -> "" }
                in dtrace ("getMemberId: nid=" ++ show nid ++ ", tyName=" ++ show tyName ++ ", fieldName=" ++ show fieldName) $
                   case Map.lookup tyName (regDefinitions reg) of
                    Just def -> do
                        let formalParams = case def of
                                StructDef _ ps _ -> map fst ps
                                UnionDef _ ps _  -> map fst ps
                                _                -> []
                            members = case def of
                                StructDef _ _ ms -> ms
                                UnionDef _ _ ms  -> ms
                                _                -> []
                            substMap = Map.fromList (zip formalParams params)
                        dtraceM ("getMemberId: substMap for " ++ show tyName ++ ": " ++ show substMap)
                        case find ((== fieldName) . C.lexemeText . mName) members of
                            Just mem -> do
                                let lookupFunc tid = case Map.lookup tid substMap of
                                        Just actualId -> return (Just actualId)
                                        Nothing | isRefinable tid -> do
                                            let tid' = TIdSkolem nid nid (fromIntegral (Data.Hashable.hash tid))
                                            resId <- register $ AnyRigidNodeF (RObject (VVar tid' Nothing) (Quals False False))
                                            dtraceM ("getMemberId: lookupFunc tid=" ++ show tid ++ " -> fresh " ++ show resId)
                                            return (Just resId)
                                        Nothing -> dtrace ("getMemberId: lookupFunc tid=" ++ show tid ++ " -> Nothing") $ return Nothing
                                modify $ \s -> s { tsSubstCache = Map.empty }
                                resId <- substitute lookupFunc (mType mem)
                                dtraceM ("getMemberId: nid=" ++ show nid ++ ", fieldName=" ++ show fieldName ++ " -> " ++ show resId)
                                return (Just resId)
                            Nothing -> dtrace ("getMemberId: nid=" ++ show nid ++ ", fieldName=" ++ show fieldName ++ " not found") $ return Nothing
                    Nothing -> dtrace ("getMemberId: tyName=" ++ show tyName ++ " not found in registry") $ return Nothing

            Just (AnyRigidNodeF (RObject (VExistential tids bodyId) _)) -> do
                dtraceM ("getMemberId: unpacking existential for nid=" ++ show nid)
                let lookupFunc tid = case findIndex (== tid) tids of
                        Just idx -> do
                            let tid' = TIdSkolem nid nid (fromIntegral idx)
                            resId <- register $ AnyRigidNodeF (RObject (VVar tid' Nothing) (Quals False False))
                            return (Just resId)
                        Nothing -> return Nothing
                modify $ \s -> s { tsSubstCache = Map.empty }
                unpackedId <- substitute lookupFunc bodyId
                getMemberId reg unpackedId fieldName

            Just (AnyRigidNodeF (RObject (VVar tid _) _)) -> do
                dtraceM ("getMemberId: nid=" ++ show nid ++ " is VVar " ++ show tid ++ " and lookThroughVariables returned it (no target)")
                return Nothing

            Just (AnyRigidNodeF (RReference (Ptr (TargetObject nid')) _ _ _)) -> do
                dtraceM ("getMemberId: following pointer nid=" ++ show nid ++ " -> target=" ++ show nid')
                getMemberId reg nid' fieldName

            Just node -> dtrace ("getMemberId: nid=" ++ show nid ++ " has unexpected node type: " ++ show node) $ return Nothing
            Nothing -> dtrace ("getMemberId: nid=" ++ show nid ++ " not found in tsNodes") $ return Nothing

hardenCall :: Text -> [Word32] -> [Maybe Word32] -> ReturnType Word32 -> Maybe (Lexeme Text) -> PathContext -> State TranslatorState ()
hardenCall name paramIds argIds ret loc ctx = do
    dtraceM ("hardenCall: name=" ++ show name ++ " params=" ++ show paramIds ++ " args=" ++ show argIds)
    st <- get
    case (name, paramIds, argIds, ret) of
        ("malloc", _, Just sizeArgId : _, RetVal retId) ->
            case Map.lookup retId (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr target) _ _ _)) -> do
                    mNid <- case target of
                            TargetObject tId -> return $ Just tId
                            TargetOpaque tId -> Just <$> register (AnyRigidNodeF (RObject (VVar tId Nothing) (Quals False False)))
                            _                -> return Nothing
                    case mNid of
                        Just tId -> do
                            sizePropId <- register $ AnyRigidNodeF (RObject (VProperty tId PSize) (Quals True True))
                            modify (addConstraint loc ctx sizeArgId sizePropId)
                        Nothing -> return ()
                _ -> return ()
        ("my_qsort", baseParamId : _, _ : _ : Just sizeArgId : _, _) ->
            case Map.lookup baseParamId (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr target) _ _ _)) -> do
                    mNid <- case target of
                            TargetObject tId -> return $ Just tId
                            TargetOpaque tId -> Just <$> register (AnyRigidNodeF (RObject (VVar tId Nothing) (Quals False False)))
                            _                -> return Nothing
                    case mNid of
                        Just tId -> do
                            sizePropId <- register $ AnyRigidNodeF (RObject (VProperty tId PSize) (Quals True True))
                            modify (addConstraint loc ctx sizeArgId sizePropId)
                        Nothing -> return ()
                _ -> return ()
        _ -> return ()

getMemberIndex :: Registry Word32 -> TranslatorState -> Word32 -> Text -> Maybe Int
getMemberIndex reg st nid fieldName =
    case followToNominal st nid of
        Just (l, _) ->
            let tyName = case C.lexemeText l of { TIdName n -> n; _ -> "" }
            in case Map.lookup tyName (regDefinitions reg) of
                Just (StructDef _ _ members) -> findIndex ((== fieldName) . C.lexemeText . mName) members
                Just (UnionDef _ _ members) -> findIndex ((== fieldName) . C.lexemeText . mName) members
                _ -> Nothing
        Nothing -> Nothing

matchObjPath :: Node (C.Lexeme Text) -> Maybe SymbolicPath
matchObjPath = foldFix $ \case
    CimpleNode node -> case node of
        C.VarExpr l           -> Just $ SymbolicPath (VarRoot (C.lexemeText l)) []
        C.PointerAccess obj l -> extendPath (FieldStep (C.lexemeText l)) <$> obj
        C.MemberAccess obj l  -> extendPath (FieldStep (C.lexemeText l)) <$> obj
        C.ParenExpr e         -> e
        C.CastExpr _ e        -> e
        _                     -> Nothing
    HicNode node -> case node of
        IterationElement l _ -> Just $ SymbolicPath (VarRoot (C.lexemeText l)) []
        IterationIndex l     -> Just $ SymbolicPath (VarRoot (C.lexemeText l)) []
        Match obj _ _ _ _    -> obj
        _                    -> Nothing

collectHotspots :: Node (Lexeme Text) -> [Text]
collectHotspots = foldFix $ \case
    HicNode Match{} -> ["Match"]
    HicNode TaggedUnionMemberAccess{} -> ["TaggedUnionMemberAccess"]
    CimpleNode f -> concat f
    HicNode h -> concat h

collectMatchCase :: Registry Word32 -> PathContext -> Node (Lexeme Text) -> Word32 -> TaggedUnionInfo -> MatchCase (Lexeme Text) (Node (Lexeme Text)) -> State TranslatorState ()
collectMatchCase reg ctx obj objId tu (MatchCase val body) = do
    let loc = getHicLoc body
    let mTagVal = case val of
            Fix (CimpleNode (C.VarExpr l))       -> Just (C.lexemeText l)
            Fix (CimpleNode (C.LiteralExpr _ l)) -> Just (C.lexemeText l)
            _                                    -> Nothing
    dtraceM ("collectMatchCase: val=" ++ show val ++ ", tagVal=" ++ show mTagVal ++ ", objPath=" ++ show (matchObjPath obj))
    case (mTagVal >>= \v -> Map.lookup v (tuiMembers tu), matchObjPath obj) of
        (Just memName, Just path') -> do
            st <- get
            dtraceM ("collectMatchCase: memName=" ++ show memName ++ ", path=" ++ show path' ++ ", tuUnionField=" ++ show (tuiUnionField tu))
            mUId <- getMemberId reg objId (tuiUnionField tu)
            case mUId of
                Just uId -> do
                    dtraceM ("collectMatchCase: uId=" ++ show uId)
                    case getMemberIndex reg st uId memName of
                        Just idx -> do
                            dtraceM ("collectMatchCase: idx=" ++ show idx)
                            mMemId <- getMemberId reg uId memName
                            case mMemId of
                                Just memId -> do
                                    variantId <- register (AnyRigidNodeF (RObject (VVariant (IntMap.singleton idx memId)) (Quals False False)))
                                    modify (addConstraint loc ctx uId variantId)
                                    -- Adjust path: replace tag field with union field if obj points to the tag.
                                    -- Or if obj is the container, append union field.
                                    -- In TaggedUnion, obj is usually the container (switch(c.tag) -> match(c)).
                                    let path = extendPath (FieldStep (tuiUnionField tu)) path'
                                    dtraceM ("Adding refinement: " ++ show path ++ " -> EqVariant " ++ show idx)
                                    let refinements = Map.insert path (EqVariant (fromIntegral idx)) (pcRefinements ctx)
                                    let ctx' = ctx { pcRefinements = refinements }
                                    _ <- collectRefinements reg ctx' body
                                    return ()
                                Nothing -> dtrace "collectMatchCase: getMemberId memName failed" fallback
                        Nothing -> dtrace "collectMatchCase: getMemberIndex failed" fallback
                Nothing -> dtrace ("collectMatchCase: getMemberId " ++ show (tuiUnionField tu) ++ " failed for objId " ++ show objId) fallback
        _ -> dtrace "collectMatchCase: memName or path lookup failed" fallback
  where
    fallback = collectRefinements reg ctx body >> return ()
