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
    , Collected
    , inferRefined
    , collectRefined
    , collectedSize
    , solveCollected
    , ProductState (..)
    ) where

import           Control.Applicative                         ((<|>))
import           Control.Monad                               (forM_, join,
                                                              unless, void,
                                                              when, zipWithM_)
import           Control.Monad.State.Strict                  (State, get, gets,
                                                              modify, runState)
import           Data.Containers.ListUtils                   (nubOrd, nubOrdOn)
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
import           Language.Hic.Refined.BufferSize             (analyseBufferSizes,
                                                              sizeErrors)
import           Language.Hic.Refined.Context
import           Language.Hic.Refined.Inference.Lifter
import           Language.Hic.Refined.Inference.Substitution
import           Language.Hic.Refined.Inference.Translator
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Inference.Utils
import           Language.Hic.Refined.LatticeOp
import           Language.Hic.Refined.Nullability            (checkNullability)
import           Language.Hic.Refined.PathContext
import           Language.Hic.Refined.Pretty                 (ppAnyRefinedType)
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Solver                 (Constraint (..),
                                                              solveAll)
import           Language.Hic.Refined.State

import           Language.Hic.Ast                            (CleanupAction (..),
                                                              HicNode (..),
                                                              MatchCase (..),
                                                              Node, NodeF (..),
                                                              ReturnIntent (..),
                                                              TaggedUnionMember (..))
import           Language.Hic.Inference                      (lower)
import           Language.Hic.Inference.Program              (Program (..))
import qualified Language.Hic.Refined.Inference.Platform     as Platform
import           Language.Hic.Refined.Transition
import           Language.Hic.Refined.Types

import qualified Language.Hic.TypeSystem.Core.Base           as TS
import           Prettyprinter                               (Doc, pretty,
                                                              (<+>))
import           Prettyprinter.Render.Terminal               (AnsiStyle)

getHicLoc :: Node (Lexeme Text) -> Maybe (Lexeme Text)
getHicLoc n = case foldFix C.concats n of
    []  -> Nothing
    l:_ -> Just l

-- | Traverses the Hic AST to identify hotspots for refined analysis.
inferRefined :: TS.TypeSystem -> Program (Lexeme Text) -> RefinedResult
inferRefined ts prog = solveCollected prog (collectRefined ts prog)

-- | The constraints collected from a program, ready to solve.
data Collected = Collected (Registry Word32) TranslatorState

collectRefined :: TS.TypeSystem -> Program (Lexeme Text) -> Collected
collectRefined ts prog = uncurry Collected $ runState (translateAndCollect ts prog) (emptyTranslatorState ts)

-- | The number of type nodes collected.
collectedSize :: Collected -> Int
collectedSize (Collected _ st) = Map.size (tsNodes st)

solveCollected :: Program (Lexeme Text) -> Collected -> RefinedResult
solveCollected prog (Collected registry st) =
    let hotspots = nub $ concatMap (concatMap collectHotspots) (Map.elems (progAsts prog))
        (conflicts, finalRefs, steps, origins) = solveAll registry (tsNodes st) (Map.toList (tsDefinitions st)) (tsConstraints st) (0, 1, 2, 0)
        resSolved = case conflicts of
            (ps, _):_ -> Left ps
            []        -> Right finalRefs
        -- One line can conflict through several constraints (e.g. a cast and
        -- the assignment it's in): report each conflicting pair once per line.
        conflictKey ps = (psFile ps, fmap (\(L (C.AlexPn _ line _) _ _) -> line) (psOrigin ps), psNodeL ps, psNodeR ps)
        fromCast (_, root) = Set.member (psNodeL root, psNodeR root) (tsCasts st)
        solverErrs = [ solverStateToErrorInfo (tsNodes st) finalRefs (fromCast c) (fst c) | c <- nubOrdOn (conflictKey . fst) conflicts ]
        lowered = [ (path, map lower ast) | (path, ast) <- Map.toList (progAsts prog) ]
        sizes = analyseBufferSizes lowered
        sizeErrs = sizeErrors sizes
        platformErrs = Platform.checkPlatformUse lowered
        nullErrs = checkNullability sizes lowered
        res = RefinedResult hotspots (tsNodes st) registry resSolved steps origins (tsNodesByFunction st) (tsFunctionStarts st) (solverErrs ++ tsErrors st ++ sizeErrs ++ platformErrs ++ nullErrs)
    in dtrace ("tsTaggedUnions: " ++ show (Map.keys (tsTaggedUnions st))) res

solverStateToErrorInfo :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Bool -> ProductState -> ErrorInfo 'TS.Global
solverStateToErrorInfo nodes refs cast ps =
    let loc = psOrigin ps
        file = fromMaybe "unknown" (psFile ps)
        ctx = [InFile file]
        -- Try to determine the error type
        errType = if cast then RefinedCastMismatch else case (Map.lookup (psNodeL ps) nodes, Map.lookup (psNodeR ps) nodes) of
            (Just (AnyRigidNodeF (RReference _ QNullable' _ _)), Just (AnyRigidNodeF (RReference _ QNonnull' _ _))) -> RefinedNullabilityMismatch
            (Just (AnyRigidNodeF (RReference _ QNonnull' _ _)), Just (AnyRigidNodeF (RReference _ QNullable' _ _))) -> RefinedNullabilityMismatch
            (Just (AnyRigidNodeF (RObject (VVariant _) _)), _) -> RefinedVariantMismatch
            (_, Just (AnyRigidNodeF (RObject (VVariant _) _))) -> RefinedVariantMismatch
            -- Fallback for now
            _ -> CustomError "Refined type mismatch detected in fixpoint solver"
    in ErrorInfo loc ctx errType
        [ "NodeL:" <+> ppNode nodes refs (psDepthL ps) 4 (psNodeL ps)
        , "NodeR:" <+> ppNode nodes refs (psDepthR ps) 4 (psNodeR ps)
        ]

-- | A node's type for an error message, with its variables as what the
-- solution binds them to, cut off a few levels down, as types can be
-- recursive.
ppNode :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Int -> Word32 -> Doc AnsiStyle
ppNode nodes refs varDepth = go
  where
    go limit nid
        | limit <= 0 = "..."
        | otherwise = case Map.lookup nid nodes of
            Just (AnyRigidNodeF (RObject (VVar tid _) _))
                | isRefinable tid
                , Just bound <- getRefinement (variableKey nodes varDepth tid) refs
                , bound /= nid -> go (limit - 1) bound
            Just node -> ppAnyRefinedType (go (limit - 1)) node
            Nothing -> pretty nid

addError :: Maybe (Lexeme Text) -> TypeError 'TS.Global -> State TranslatorState ()
addError loc err = modify $ \s ->
    s { tsErrors = ErrorInfo loc [InFile (tsCurrentFile s)] err [] : tsErrors s }

translateAndCollect :: TS.TypeSystem -> Program (Lexeme Text) -> State TranslatorState (Registry Word32)
translateAndCollect ts prog = do
    modify $ \s -> s { tsCurrentFile = "<types>", tsCurrentFunction = "<struct types>" }
    initialReg <- translateRegistry ts
    modify $ \s -> s { tsCurrentFunction = "<implicit parameters>" }
    reg <- liftImplicitPolymorphism initialReg
    modify $ \s -> s { tsCurrentFunction = "<top level>" }
    -- Pre-pass: gather all TaggedUnion definitions
    dtraceM ("translateAndCollect: gathering TaggedUnions from " ++ show (Map.size (progAsts prog)) ++ " files")
    mapM_ (mapM_ gatherTaggedUnions) (progAsts prog)
    -- Pre-pass: every function's signature, so that a call is checked whatever
    -- order the files come in. A prototype comes second: it has the
    -- annotations (a definition's parameters often have none), and the body is
    -- bound to it.
    forM_ [True, False] $ \definitions -> forM_ (Map.toList (progAsts prog)) $ \(path, ast) -> do
        modify $ \s -> s { tsCurrentFile = path }
        mapM_ (declareFunctions definitions) ast
    mapM_ (\(path, ast) -> do
        modify $ \s -> s { tsCurrentFile = path }
        mapM_ (collectRefinements reg (PathContext Map.empty Map.empty)) ast
        ) (Map.toList (progAsts prog))
    modify $ \s -> s { tsCurrentFile = "<struct calls>", tsCurrentFunction = "<struct calls>", tsFunctionLoc = Nothing }
    applyStructCalls reg
    return reg

-- | Registers the signatures of the function prototypes (or definitions) in a
-- node.
declareFunctions :: Bool -> Node (Lexeme Text) -> State TranslatorState ()
declareFunctions definitions (Fix node) = case node of
    CimpleNode (C.FunctionDecl _ proto)   -> unless definitions $ declare proto
    CimpleNode (C.FunctionDefn _ proto _) -> when definitions $ declare proto
    _                                     -> mapM_ (declareFunctions definitions) node
  where
    declare proto = case lower proto of
        Fix (C.FunctionPrototype _ name _) -> do
            st <- get
            nid <- ownSignature =<< translateType (nodeToTypeInfo (tsTypeSystem st) (lower proto))
            modify (addFunction (C.lexemeText name) nid)
        _ -> return ()

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

    -- out = val; return ret;
    Raise out val retIntent -> do
        case out of
            Just o  -> void $ collectRefinements reg ctx (Fix (CimpleNode (C.AssignExpr o C.AopEq val)))
            Nothing -> void $ collectRefinements reg ctx val
        let ret = case retIntent of
                ReturnValue v -> Just v
                ReturnError e -> Just e
                ReturnVoid    -> Nothing
        _ <- collectRefinements reg ctx (Fix (CimpleNode (C.Return ret)))
        return Nothing

    Transition fr to -> do
        _ <- collectRefinements reg ctx fr
        _ <- collectRefinements reg ctx to
        return Nothing

    -- return obj->tag == tv ? obj->uf.m : e;
    TaggedUnionGet _ p o _isPtr _tf tv uf m e -> collectFunction ctx loc p $ do
        mObjId <- collectRefinements reg ctx o
        _ <- collectRefinements reg ctx tv
        mUnionId <- maybe (return Nothing) (\objId -> getMemberId reg objId (C.lexemeText uf)) mObjId
        mMemberId <- maybe (return Nothing) (\uId -> getMemberId reg uId (C.lexemeText m)) mUnionId
        mElseId <- collectRefinements reg ctx e
        st <- get
        linkTypes loc ctx (tsCurrentReturn st) mMemberId
        linkTypes loc ctx (tsCurrentReturn st) mElseId

    -- return obj->tf;
    TaggedUnionGetTag _ p o _isPtr tf -> collectFunction ctx loc p $ do
        mObjId <- collectRefinements reg ctx o
        mTagId <- maybe (return Nothing) (\objId -> getMemberId reg objId (C.lexemeText tf)) mObjId
        st <- get
        linkTypes loc ctx (tsCurrentReturn st) mTagId

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
                        modify (addInherit loc instId eId)
                        return (Just instId)
                    Just (AnyRigidNodeF (RReference (Ptr (TargetObject eId)) _ _ _)) -> do
                        instId <- refreshInstance loc eId
                        modify (addInherit loc instId eId)
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
        -- Declared before collecting (declareFunctions).
        C.FunctionDecl _ protoNode -> Just $ case lower protoNode of
            Fix (C.FunctionPrototype _ name _) -> gets (Map.lookup (C.lexemeText name) . tsFunctions)
            _                                  -> return Nothing

        C.FunctionDefn _ proto body -> Just $
            collectFunction ctx loc proto (void $ collectRefinements reg ctx body)

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
        -- A member is no variable.
        C.MemberDecl (Fix (CimpleNode C.VarDecl{})) _ -> Just $ return Nothing
        C.MemberDecl decl _ -> Just $ collectRefinements reg ctx decl >> return Nothing
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

-- | Links a call argument to its parameter. Whether an array parameter's
-- argument is big enough is checked by "Language.Hic.Refined.BufferSize".
linkArgument :: Maybe (Lexeme Text) -> PathContext -> Word32 -> Word32 -> State TranslatorState ()
linkArgument loc ctx paramId argId = modify (addConstraintCoerced loc ctx argId paramId)

-- | Collects a function definition: registers its type, binds its parameters
-- and collects its body with the return type in scope.
collectFunction :: PathContext -> Maybe (Lexeme Text) -> Node (Lexeme Text) -> State TranslatorState () -> State TranslatorState (Maybe Word32)
collectFunction ctx loc proto collectBody = do
    st <- get
    case lower proto of
        Fix (C.FunctionPrototype _ name params) -> do
            dtraceM ("collectRefinements: processing function " ++ show (C.lexemeText name))
            let L (C.AlexPn _ startLine _) _ _ = name
                oldFunction = tsCurrentFunction st
            let oldFunctionLoc = tsFunctionLoc st
            modify $ \s -> s
                { tsCurrentFunction = C.lexemeText name
                , tsFunctionLoc = Just name
                , tsFunctionStarts = Map.insertWith Map.union (tsCurrentFile s) (Map.singleton startLine (C.lexemeText name)) (tsFunctionStarts s)
                }
            -- The signature declared before collecting (declareFunctions).
            nid <- case Map.lookup (C.lexemeText name) (tsFunctions st) of
                Just declared -> return declared
                Nothing -> do
                    declared <- ownSignature =<< translateType (nodeToTypeInfo (tsTypeSystem st) (lower proto))
                    modify (addFunction (C.lexemeText name) declared)
                    return declared

            stSig <- get
            let (paramIds, retNid) = case Map.lookup nid (tsNodes stSig) of
                    Just (AnyRigidNodeF (RFunction pIds (RetVal r))) -> (pIds, Just r)
                    Just (AnyRigidNodeF (RFunction pIds RetVoid))    -> (pIds, Nothing)
                    _                                                -> ([], Nothing)
                oldRet = tsCurrentReturn st
                -- The function's parameters and locals are its own.
                oldVars = tsVars st
            modify $ \s -> s { tsCurrentReturn = retNid }

            -- Bind parameters
            zipWithM_ (\pId pDecl -> case pDecl of
                Fix (C.VarDecl _ pName _) -> do
                    st' <- get
                    -- The whole declaration, as in the signature: an array
                    -- parameter's dimensions are in the declarator.
                    let pTyInfo = nodeToTypeInfo (tsTypeSystem st') pDecl
                    pNid <- translateType pTyInfo
                    pNid' <- refreshInstance loc pNid
                    -- LINK: Propagate body refinements to signature
                    modify (addConstraintCoerced loc ctx pId pNid')
                    modify (addVar (C.lexemeText pName) pNid')
                _ -> return ()) paramIds params

            collectBody
            modify $ \s -> s { tsCurrentReturn = oldRet, tsCurrentFunction = oldFunction, tsFunctionLoc = oldFunctionLoc, tsVars = oldVars }
            return (Just nid)
        _ -> return Nothing

collectRefinementsCimpleExpr :: Registry Word32 -> PathContext -> Maybe (Lexeme Text) -> C.NodeF (Lexeme Text) (Node (Lexeme Text)) -> Maybe (State TranslatorState (Maybe Word32))
collectRefinementsCimpleExpr reg ctx loc = \case
        C.AssignExpr lhs op rhs -> Just $ do
            mLhs <- collectRefinements reg ctx lhs
            mRhs <- collectRefinements reg ctx rhs
            mNodeL <- maybe (return Nothing) lookThroughVariables mLhs
            case (mLhs, mRhs) of
                -- p += n is p = p + n: the pointer is assigned from itself, not from n.
                (Just lId, Just _) | op `elem` [C.AopPlus, C.AopMinus] && isReference mNodeL -> do
                    pId <- degradeToPointer lId
                    modify (addConstraintCoerced loc ctx pId lId)
                (Just lId, Just rId) ->
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
            st0 <- get
            let isFunctionName name = Map.notMember name (tsVars st0) && Map.member name (tsFunctions st0)
            case (op, mId) of
                (C.UopIncr, Just nid) | not (isNumeric mNode) && isReference mNode -> Just <$> degradeToPointer nid
                (C.UopDecr, Just nid) | not (isNumeric mNode) && isReference mNode -> Just <$> degradeToPointer nid
                (C.UopIncr, _) -> return mId
                (C.UopDecr, _) -> return mId
                -- A function's name is already the pointer to it.
                (C.UopAddress, Just nid) | Fix (CimpleNode (C.VarExpr l)) <- e, isFunctionName (C.lexemeText l) -> return (Just nid)
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
                        Just (AnyRigidNodeF (RReference (Arr eId _) _ _ _)) -> return (Just eId)
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
                (C.BopPlus, Just lId, Just _) | isReference mNodeL && not (isReference mNodeR) ->
                    Just <$> degradeToPointer lId
                (C.BopPlus, Just _, Just rId) | not (isReference mNodeL) && isReference mNodeR ->
                    Just <$> degradeToPointer rId
                (C.BopPlus, Just _, Just _) | isReference mNodeL && isReference mNodeR -> do
                    addError loc (CustomError "Pointer arithmetic not supported in refined analysis")
                    return Nothing
                (C.BopMinus, Just lId, Just _) | isReference mNodeL && not (isReference mNodeR) ->
                    Just <$> degradeToPointer lId
                (C.BopMinus, Just _, Just _) | isReference mNodeL && isReference mNodeR ->
                    Just <$> translateType (Fix (TS.BuiltinTypeF TS.S64Ty))
                (C.BopMinus, Just _, Just _) | not (isReference mNodeL) && isReference mNodeR -> do
                    addError loc (CustomError "Pointer arithmetic not supported in refined analysis")
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
            st <- get
            let isNullptr nid = case Map.lookup nid (tsNodes st) of
                    Just (AnyRigidNodeF (RReference (Ptr (TargetObject t)) _ _ _)) ->
                        Map.lookup t (tsNodes st) == Just (AnyRigidNodeF (RObject (VBuiltin NullPtrTy) (Quals True False)))
                    _ -> False
                -- `c ? p : nullptr` is p or nothing: p, nullable.
                orNull nid = case Map.lookup nid (tsNodes st) of
                    Just (AnyRigidNodeF (RReference ref _ o q)) -> register (AnyRigidNodeF (RReference ref QNullable' o q))
                    _                                         -> return nid
            case (mThen, mElse) of
                (Just tId, Just eId)
                    | isNullptr eId -> Just <$> orNull tId
                    | isNullptr tId -> Just <$> orNull eId
                    | otherwise -> do
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
                                    modify (addInherit loc instId eId)
                                    modify $ \s -> s { tsArrayInstances = Map.insert (objId, i) instId (tsArrayInstances s) }
                                    return (Just instId)
                                Just (AnyRigidNodeF (RReference (Ptr (TargetObject eId)) _ _ _)) -> do
                                    instId <- refreshInstance loc eId
                                    modify (addInherit loc instId eId)
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
            mOld <- traverse lookThroughVariables mId
            stCast <- get
            let handleCast = maybe False Platform.isHandle (typeName (lower ty))
            -- Whether a pointer is to bytes that are const.
            let bytes :: TranslatorState -> Maybe (AnyRigidNodeF TemplateId Word32) -> Maybe Bool
                bytes st' node = case node of
                    Just (AnyRigidNodeF (RReference (Ptr (TargetObject eId)) _ _ _)) -> byteConst st' eId
                    Just (AnyRigidNodeF (RReference (Arr eId _) _ _ _))              -> byteConst st' eId
                    _                                                                -> Nothing
                byteConst :: TranslatorState -> Word32 -> Maybe Bool
                byteConst st' eId = case Map.lookup eId (tsNodes st') of
                    Just (AnyRigidNodeF (RObject (VBuiltin b) q)) | b `elem` [CharTy, U08Ty, S08Ty] -> Just (qConst q)
                    _                                                                              -> Nothing
                isSize = \case
                    Just (AnyRigidNodeF (RObject VProperty{} _)) -> True
                    Just (AnyRigidNodeF (RObject VSizeExpr{} _)) -> True
                    _                                            -> False
                newNode = Map.lookup newId (tsNodes stCast)
            case mId of
                -- A cast between numbers (integers, enums, sizes) is a
                -- conversion asked for: the number doesn't have to be the other
                -- kind.
                Just _ | isNumber (tsTypeSystem stCast) newNode, Just old <- mOld, isNumber (tsTypeSystem stCast) old || isSize old -> return ()
                -- What the operating system's interfaces say may be cast.
                Just oldId | platformView stCast newId oldId -> return ()
                Just _ | Just old <- mOld, handleCast, isNumber (tsTypeSystem stCast) old -> return ()
                -- Bytes are bytes: a char and a uint8_t have the same values
                -- and may see the same memory. What's const stays so.
                Just _ | Just old <- mOld, Just newConst <- bytes stCast newNode, Just oldConst <- bytes stCast old, newConst || not oldConst -> return ()
                Just oldId ->
                    modify (addCastConstraint loc ctx newId' oldId)
                Nothing -> return ()
            return (Just newId')

        C.FunctionCall func args -> Just $ do
            recordStructCalls reg ctx func args
            mFuncId <- collectRefinements reg ctx func
            mArgIds <- mapM (collectRefinements reg ctx) (readOnlyArgs func args)
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
                            _ <- Map.traverseWithKey (\origId freshId -> modify (addInherit loc freshId origId)) nodeMapping

                            case matchObjPath func of
                                Just (SymbolicPath (VarRoot name) []) ->
                                    hardenCall name paramIds' mArgIds ret' loc ctx
                                _ -> return ()

                            zipWithM_ (\p a -> traverse (linkArgument loc ctx p) a) paramIds' mArgIds
                            case ret' of
                                RetVal rId -> return (Just rId)
                                RetVoid    -> return Nothing
                        Just (AnyRigidNodeF (RFunction paramIds ret)) -> do
                            dtraceM ("Direct Call to " ++ show fId ++ " with " ++ show (length paramIds) ++ " params")
                            (paramIds', ret', nodeMapping) <- refreshSignature paramIds ret
                            -- Link instantiated variables back to origins: One-Way inheritance
                            _ <- Map.traverseWithKey (\origId freshId -> modify (addInherit loc freshId origId)) nodeMapping

                            case matchObjPath func of
                                Just (SymbolicPath (VarRoot name) []) ->
                                    hardenCall name paramIds' mArgIds ret' loc ctx
                                _ -> return ()

                            zipWithM_ (\p a -> traverse (linkArgument loc ctx p) a) paramIds' mArgIds
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
        C.AttrAllocSize _ e -> Just $ collectRefinements reg ctx e
        _ -> Nothing


resolveVVar :: TranslatorState -> Word32 -> Word32
resolveVVar st = go Set.empty
  where
    go visited nid
        | nid `Set.member` visited = nid
        | otherwise =
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RObject (VVar _ _) _)) ->
                    let ts = lookThroughTargets st nid
                        visited' = Set.insert nid visited
                    -- Meets before inheritance; skip constraints back to a variable
                    -- we've seen, e.g. from @p = p + 1@.
                    in case filter (`Set.notMember` visited') ([t | (MeetTarget, t) <- ts] ++ [t | (InheritTarget, t) <- ts]) of
                        (targetId:_) -> go visited' targetId
                        []           -> nid
                _ -> nid

lookThroughVariables :: Word32 -> State TranslatorState (Maybe (AnyRigidNodeF TemplateId Word32))
lookThroughVariables nid = do
    st <- get
    let resId = resolveVVar st nid
    return $ Map.lookup resId (tsNodes st)

-- | Degrade an array reference to a pointer reference, preserving element type
-- and qualifiers. If the node is already a pointer (or anything else), return
-- the original ID unchanged.
degradeToPointer :: Word32 -> State TranslatorState Word32
degradeToPointer nid = do
    st <- get
    case Map.lookup nid (tsNodes st) of
        Just (AnyRigidNodeF (RReference (Arr elementId _dims) nullability ownership quals)) ->
            register (AnyRigidNodeF (RReference (Ptr (TargetObject elementId)) nullability ownership quals))
        _ -> return nid

-- | Whether a cast is from a pointer to one of the operating system's types
-- to a pointer to another it may be seen as ('Platform.sameObject').
platformView :: TranslatorState -> Word32 -> Word32 -> Bool
platformView st newId oldId = case (pointee newId, pointee oldId) of
    (Just a, Just b) -> Platform.sameObject a b
    _                -> False
  where
    pointee nid = case Map.lookup (resolveVVar st nid) (tsNodes st) of
        Just (AnyRigidNodeF (RReference (Ptr (TargetObject oid)) _ _ _)) -> case Map.lookup (resolveVVar st oid) (tsNodes st) of
            Just (AnyRigidNodeF (RObject (VNominal (L _ _ (TIdName n)) _) _)) -> Just n
            _                                                                -> Nothing
        _ -> Nothing

-- | A call's arguments, with a string cast to one that may be written given
-- as it is where the function only reads it ('Platform.readOnlyStrings').
readOnlyArgs :: Node (Lexeme Text) -> [Node (Lexeme Text)] -> [Node (Lexeme Text)]
readOnlyArgs func args = case func of
    Fix (CimpleNode (C.VarExpr (L _ _ f))) | Just ks <- Map.lookup f Platform.readOnlyStrings ->
        [ if k `elem` ks then uncast arg else arg | (k, arg) <- zip [0 ..] args ]
    _ -> args
  where
    uncast arg = case arg of
        Fix (CimpleNode (C.CastExpr ty e))
            | Just t <- typeName (lower ty), Platform.isStringPointer t -> e
        _ -> arg

-- | The name of a type that is just a name: one of C's or the platform's,
-- or one a typedef gives.
typeName :: C.Node (Lexeme Text) -> Maybe Text
typeName (Fix node) = case node of
    C.TyStd (L _ _ t)         -> Just t
    C.TyUserDefined (L _ _ t) -> Just t
    _                         -> Nothing

followToNominal :: TranslatorState -> Word32 -> Maybe (Lexeme TemplateId, [Word32])
followToNominal st nid =
    let resId = resolveVVar st nid
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
getMemberId reg nid = memberOf reg nid False nid

-- | Reads field @fieldName@ of the struct at @nid@, an access of instance
-- @inst@: the struct's parameters become skolems tied to that instance.
-- Through a pointer, a struct is an existential: it's another object, so its
-- arguments say nothing about this instance and every parameter is a skolem.
memberOf :: Registry Word32 -> Word32 -> Bool -> Word32 -> Text -> State TranslatorState (Maybe Word32)
memberOf reg inst viaPointer nid fieldName = do
    st <- get
    dtraceM ("memberOf: inst=" ++ show inst ++ ", nid=" ++ show nid ++ ", fieldName=" ++ show fieldName)
    let isBot' = case Map.lookup nid (tsNodes st) of
            Just (AnyRigidNodeF (RTerminal SBottom)) -> True
            _                                        -> False
        skolem :: TemplateId -> State TranslatorState (Maybe Word32)
        skolem tid = Just <$> instanceSkolem inst tid
    if isBot'
    then return (Just 2) -- SConflict
    else do
        mNode <- lookThroughVariables nid
        case mNode of
            Just (AnyRigidNodeF (RObject (VNominal l params) _)) ->
                let tyName = case C.lexemeText l of { TIdName n -> n; _ -> "" }
                in case Map.lookup tyName (regDefinitions reg) of
                    Just def -> do
                        let formalParams = case def of
                                StructDef _ ps _ -> map fst ps
                                UnionDef _ ps _  -> map fst ps
                                _                -> []
                            members = case def of
                                StructDef _ _ ms -> ms
                                UnionDef _ _ ms  -> ms
                                _                -> []
                            substMap = if viaPointer then Map.empty else Map.fromList (zip formalParams params)
                        modify $ \s -> s { tsStructInstances = Map.insertWith (Map.unionWith const) tyName
                            (Map.singleton inst (if viaPointer then Nothing else Just substMap)) (tsStructInstances s) }
                        case find ((== fieldName) . C.lexemeText . mName) members of
                            Just mem -> do
                                modify $ \s -> s { tsAccessedFields = Set.insert (inst, fieldName) (tsAccessedFields s) }
                                let lookupFunc tid = case Map.lookup tid substMap of
                                        Just actualId          -> return (Just actualId)
                                        Nothing | isRefinable tid -> skolem tid
                                        Nothing                -> return Nothing
                                    -- The same field of the same instance always has the same type.
                                    key = (inst, tyName, if viaPointer then [] else params, fieldName)
                                resId <- cached tsMemberTypes (\m s -> s { tsMemberTypes = m }) key $ do
                                    modify $ \s -> s { tsSubstCache = Map.empty }
                                    substitute lookupFunc (mType mem)
                                Just <$> pointerFieldInstance inst fieldName resId
                            Nothing -> return Nothing
                    Nothing -> return Nothing

            Just (AnyRigidNodeF (RObject (VExistential tids bodyId) _)) -> do
                let lookupFunc tid = if tid `elem` tids then skolem tid else return Nothing
                unpackedId <- cached tsUnpacked (\m s -> s { tsUnpacked = m }) (inst, bodyId) $ do
                    modify $ \s -> s { tsSubstCache = Map.empty }
                    substitute lookupFunc bodyId
                memberOf reg inst False unpackedId fieldName

            Just (AnyRigidNodeF (RReference (Ptr (TargetObject nid')) _ _ _)) ->
                memberOf reg inst True nid' fieldName

            _ -> return Nothing

-- | Parameter @tid@ of the struct instance @inst@, read through a pointer.
instanceSkolem :: Word32 -> TemplateId -> State TranslatorState Word32
instanceSkolem inst tid = cached tsSkolems (\m s -> s { tsSkolems = m }) (inst, tid) $
    register $ AnyRigidNodeF (RObject (VVar (TIdSkolem inst inst (fromIntegral (Data.Hashable.hash tid))) Nothing) (Quals False False))

-- | Looks a result up in one of the translator's caches, or makes and keeps it.
cached :: Ord k => (TranslatorState -> Map k Word32) -> (Map k Word32 -> TranslatorState -> TranslatorState) -> k -> State TranslatorState Word32 -> State TranslatorState Word32
cached getCache setCache key make = do
    st <- get
    case Map.lookup key (getCache st) of
        Just nid -> return nid
        Nothing -> do
            nid <- make
            modify $ \s -> setCache (Map.insert key nid (getCache s)) s
            return nid

-- | Records a call like @p->cb(p->userdata)@, which passes a struct's own
-- data to its own callback: every instance of the struct must allow it, not
-- only @p@, so it's checked on each of them after collection.
recordStructCalls :: Registry Word32 -> PathContext -> Node (Lexeme Text) -> [Node (Lexeme Text)] -> State TranslatorState ()
recordStructCalls reg ctx func args = case accessOf func of
    Just (base, f) | Just basePath <- matchObjPath base -> do
        mObjId <- collectRefinements reg ctx base
        st <- get
        let calls = [ (name, C.lexemeText f, k, C.lexemeText g)
                    | Just name <- [mObjId >>= getObjectTypeName st]
                    , (k, arg) <- zip [0..] args
                    , Just (argBase, g) <- [accessOf arg]
                    , matchObjPath argBase == Just basePath
                    ]
        modify $ \s -> s { tsStructCalls = calls ++ tsStructCalls s }
    _ -> return ()
  where
    accessOf (Fix (CimpleNode (C.PointerAccess b l))) = Just (b, l)
    accessOf (Fix (CimpleNode (C.MemberAccess b l)))  = Just (b, l)
    accessOf _                                        = Nothing

-- | Checks each recorded struct call on every instance of its struct, as if
-- the instance made the call itself. Only instances that use both fields can
-- break it: on any other, one side is unconstrained.
applyStructCalls :: Registry Word32 -> State TranslatorState ()
applyStructCalls reg = do
    st <- get
    let ctx = PathContext Map.empty Map.empty
        uses inst field = Set.member (inst, field) (tsAccessedFields st)
    forM_ (nubOrd (tsStructCalls st)) $ \(name, f, k, g) ->
        forM_ (filter (\inst -> uses inst f && uses inst g) (Map.keys (Map.findWithDefault Map.empty name (tsStructInstances st)))) $ \inst -> do
            mFuncId <- getMemberId reg inst f
            mArgId <- getMemberId reg inst g
            mFunc <- maybe (return Nothing) lookThroughVariables mFuncId
            case (mFunc, mArgId) of
                (Just (AnyRigidNodeF (RReference (Ptr (TargetFunction paramIds ret)) _ _ _)), Just argId) | k < length paramIds -> do
                    (paramIds', _, nodeMapping) <- refreshSignature paramIds ret
                    _ <- Map.traverseWithKey (\origId freshId -> modify (addInherit Nothing freshId origId)) nodeMapping
                    case drop k paramIds' of
                        paramId : _ -> linkArgument Nothing ctx paramId argId
                        []          -> return ()
                _ -> return ()

-- | A field that points to a struct is its own instance, the same one each
-- time it's read from the same instance, so @x->inner->cb@ and
-- @x->inner->userdata@ agree, and @y->inner@ is another.
pointerFieldInstance :: Word32 -> Text -> Word32 -> State TranslatorState Word32
pointerFieldInstance inst fieldName resId = do
    st <- get
    let pointsToStruct = case Map.lookup resId (tsNodes st) of
            Just (AnyRigidNodeF (RReference (Ptr (TargetObject t)) _ _ _)) -> case Map.lookup t (tsNodes st) of
                Just (AnyRigidNodeF (RObject VNominal{} _))     -> True
                Just (AnyRigidNodeF (RObject VExistential{} _)) -> True
                _                                               -> False
            _ -> False
    case Map.lookup (inst, fieldName) (tsFieldInstances st) of
        Just fieldInst -> return fieldInst
        Nothing | pointsToStruct -> do
            fieldInst <- register $ AnyRigidNodeF (RObject (VVar (TIdInstance (toInteger (tsNextId st))) Nothing) (Quals False False))
            modify $ \s -> (addConstraint Nothing (PathContext Map.empty Map.empty) fieldInst resId s)
                { tsFieldInstances = Map.insert (inst, fieldName) fieldInst (tsFieldInstances s) }
            return fieldInst
        Nothing -> return resId

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
