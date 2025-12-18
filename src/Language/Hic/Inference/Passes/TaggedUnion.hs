{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Inference.Passes.TaggedUnion
    ( feature
    ) where

import           Control.Applicative                  ((<|>))
import           Control.Monad                        (guard)
import           Control.Monad.State.Strict           (State, modify)
import qualified Control.Monad.State.Strict           as State
import           Data.Bifunctor                       (Bifunctor (..))
import           Data.Fix                             (Fix (..), foldFix)
import           Data.Foldable                        (fold)
import           Data.List                            (isPrefixOf)
import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Maybe                           (fromMaybe, mapMaybe)
import           Data.Set                             (Set)
import qualified Data.Set                             as Set
import           Data.Text                            (Text)
import qualified Data.Text                            as T
import qualified Debug.Trace                          as Debug
import qualified Language.Cimple                      as C
import           Language.Hic.Ast                     (HicNode (..),
                                                       MatchCase (..), Node,
                                                       TaggedUnionMember (..))
import qualified Language.Hic.Ast                     as H
import           Language.Hic.Inference.Context       (Context (..))
import           Language.Hic.Inference.Feature       (Feature (..))
import           Language.Hic.Inference.Passes.Type   (getType)
import           Language.Hic.Inference.Program.Types (Program (..))
import           Language.Hic.Inference.Utils         (dummyLexeme, getTypeName,
                                                       matchAccess,
                                                       resolveTypedef)

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg = if debugging then Debug.trace msg else id

dtraceM :: Monad m => String -> m ()
dtraceM msg = if debugging then Debug.traceM msg else return ()

feature :: Feature
feature = Feature
    { featureName     = "TaggedUnion"
    , featureGather   = gather
    , featureInfer    = infer
    , featureValidate = validate
    , featureLower    = lower
    }

-- | Phase 1: Gather TaggedUnion definitions from the AST.
gather :: Program (C.Lexeme Text) -> Context -> Context
gather (prog :: Program (C.Lexeme Text)) ctx =
    let -- traverse all nodes to find TaggedUnions
        findTUs = snd . foldFix alg
        alg f = (Fix (fmap fst f), (case f of
            H.HicNode tu@TaggedUnion{} -> (C.lexemeText (tuName tu), fmap fst tu) : foldMap snd tu
            _ -> foldMap snd f))
        tus = concatMap (concatMap findTUs) (Map.elems (progAsts prog))
    in dtrace ("gather TaggedUnions: " ++ show (Map.keys $ Map.fromList tus)) $
       ctx { ctxTaggedUnions = Map.union (ctxTaggedUnions ctx) (Map.fromList tus) }

-- | Phase 2: Infer TaggedUnion constructs.
infer :: Context -> FilePath -> Node (C.Lexeme Text) -> State Bool (Node (C.Lexeme Text))
infer ctx _file node = snd (foldFix alg node) Map.empty
  where
    alg f =
        let original = Fix (fmap fst f)
        in (original, \env -> do
            let env' = updateEnv ctx env (fmap fst f)
            f' <- traverse (\(_, transform) -> transform env') f
            let n' = Fix f'
            case attemptTransform ctx env' n' of
                Just newNode -> dtraceM ("Transformed: " ++ show original ++ " -> " ++ show newNode) >> modify (const True) >> return newNode
                Nothing      -> return n')

attemptTransform :: Context -> Map Text Text -> Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text))
attemptTransform ctx env node =
    case node of
        Fix (H.CimpleNode (C.Struct name fields)) ->
            inferStruct ctx name fields
        Fix (H.CimpleNode (C.SwitchStmt expr cases)) ->
            inferMatch ctx env expr cases
        Fix (H.CimpleNode (C.FunctionDefn scope proto body)) ->
            inferGetter ctx env scope proto body
                <|> inferTagGetter ctx env scope proto body
        Fix (H.CimpleNode (C.CompoundStmt stmts)) ->
            Fix . H.CimpleNode . C.CompoundStmt <$> coalesceAssignments ctx env stmts
        Fix (H.CimpleNode (C.Group stmts)) ->
            Fix . H.CimpleNode . C.Group <$> coalesceAssignments ctx env stmts
        _ -> Nothing

coalesceAssignments :: Context -> Map Text Text -> [Node (C.Lexeme Text)] -> Maybe [Node (C.Lexeme Text)]
coalesceAssignments ctx env stmts =
    case go env stmts of
        (stmts', True) -> Just stmts'
        (_, False)     -> Nothing
  where
    go _ [] = ([], False)
    go _ [s] = ([s], False)
    go e (s1@(Fix f1):s2:ss) =
        let e' = updateEnv ctx e f1
            (rest, restChanged) = go e' (s2:ss)
        in case (matchTagAssign s1, matchDataAssign s2) of
            (Just (obj1, isPtr1, tagField, tagVal), Just (obj2, isPtr2, uf, mem, dataVal))
                | isPtr1 == isPtr2 && stripLoc obj1 == stripLoc obj2 ->
                    case getType ctx e obj1 of
                        Just tyName ->
                            case Map.lookup tyName (ctxTaggedUnions ctx) of
                                Just tu | C.lexemeText (tuTagField tu) == tagField && C.lexemeText (tuUnionField tu) == uf ->
                                    if isCorrectMember tu tagVal mem
                                    then
                                        let newStmt = Fix $ H.HicNode $
                                                TaggedUnionConstruct obj1 isPtr1 (tuName tu) (tuTagField tu) tagVal (tuUnionField tu) (dummyLexeme mem) dataVal
                                            (rest', _) = go e' ss
                                        in (newStmt : rest', True)
                                    else (s1 : rest, restChanged)
                                _ -> (s1 : rest, restChanged)
                        Nothing -> (s1 : rest, restChanged)
            _ -> (s1 : rest, restChanged)

    stripLoc = foldFix $ \case
        H.CimpleNode n -> Fix $ H.CimpleNode (bimap (\(C.L _ c t) -> C.L (C.AlexPn 0 0 0) c t) id n)
        H.HicNode n    -> Fix $ H.HicNode (bimap (\(C.L _ c t) -> C.L (C.AlexPn 0 0 0) c t) id n)

    matchTagAssign (Fix (H.CimpleNode (C.ExprStmt (Fix (H.CimpleNode (C.AssignExpr lhs C.AopEq val)))))) = do
        (obj, isPtr, field) <- matchAccess lhs
        return (obj, isPtr, C.lexemeText field, val)
    matchTagAssign _ = Nothing

    matchDataAssign (Fix (H.CimpleNode (C.ExprStmt (Fix (H.CimpleNode (C.AssignExpr lhs C.AopEq val)))))) =
        case lhs of
            Fix (H.CimpleNode (C.MemberAccess base mem)) -> do
                (obj, isPtr, uf) <- matchAccess base
                return (obj, isPtr, C.lexemeText uf, C.lexemeText mem, val)
            _ -> Nothing
    matchDataAssign _ = Nothing

    isCorrectMember tu tagVal mem =
        let bless' v = any (\m -> C.lexemeText (tumEnumVal m) == C.lexemeText v && C.lexemeText (tumMember m) == mem) (tuMembers tu)
        in case tagVal of
            Fix (H.CimpleNode node) ->
                case node of
                    C.VarExpr v       -> bless' v
                    C.LiteralExpr _ v -> bless' v
                    _                 -> False
            _ -> False

updateEnv :: Context -> Map Text Text -> H.NodeF (C.Lexeme Text) (Node (C.Lexeme Text)) -> Map Text Text
updateEnv ctx env = \case
    H.CimpleNode (C.VarDecl ty name _) ->
        case getTypeName ty of
            Just tyName -> Map.insert (C.lexemeText name) tyName env
            Nothing     -> env
    H.CimpleNode (C.VarDeclStmt (Fix (H.CimpleNode (C.VarDecl ty name _))) _) ->
        case getTypeName ty of
            Just tyName -> Map.insert (C.lexemeText name) tyName env
            Nothing     -> env
    H.CimpleNode (C.FunctionDefn _ (Fix (H.CimpleNode (C.FunctionPrototype _ _ params))) _) ->
        foldl updateFromParam env params
    H.CimpleNode (C.FunctionPrototype _ _ params) ->
        foldl updateFromParam env params
    H.HicNode (H.ForEach iterators _ _ _ containers _ _) ->
        foldl updateFromContainer env (zip iterators containers)
    _ -> env
  where
    updateFromParam e (Fix (H.CimpleNode (C.VarDecl ty name _))) =
        case getTypeName ty of
            Just tyName -> Map.insert (C.lexemeText name) tyName e
            Nothing     -> e
    updateFromParam e _ = e

    updateFromContainer e (iter, container) =
        case getType ctx e container of
            Just tyName -> Map.insert (C.lexemeText iter) tyName e
            Nothing     -> e

inferStruct :: Context -> C.Lexeme Text -> [Node (C.Lexeme Text)] -> Maybe (Node (C.Lexeme Text))
inferStruct ctx name fields =
    case fields of
        [ Fix (H.CimpleNode (C.MemberDecl (Fix (H.CimpleNode (C.VarDecl tagType tagField []))) Nothing))
            , Fix (H.CimpleNode (C.MemberDecl (Fix (H.CimpleNode (C.VarDecl unionType unionField []))) Nothing))
            ] -> do
            let eName = fromMaybe "" (getTypeName tagType)
            let uName = fromMaybe "" (getTypeName unionType)
            let enumName = resolveTypedef ctx eName
            let unionName = resolveTypedef ctx uName

            case (Map.lookup enumName (ctxEnums ctx), Map.lookup unionName (ctxUnions ctx)) of
                (Just enumMembers, Just unionMembers) -> do
                    let (mapping, _diags) = inferMapping (C.lexemeText name) enumMembers unionMembers
                    return $ Fix $ H.HicNode $ TaggedUnion name tagType tagField unionType unionField mapping
                (me, mu) ->
                    let msg = "inferStruct " ++ T.unpack (C.lexemeText name) ++ " failed: enumName=" ++ T.unpack enumName ++ " (found=" ++ show (me /= Nothing) ++ "), unionName=" ++ T.unpack unionName ++ " (found=" ++ show (mu /= Nothing) ++ ")"
                    in dtrace msg Nothing
        _ -> Nothing

inferMatch :: Context -> Map Text Text -> Node (C.Lexeme Text) -> [Node (C.Lexeme Text)] -> Maybe (Node (C.Lexeme Text))
inferMatch ctx env expr cases = do
    (obj, isPtr, tagField) <- matchTagAccess expr
    tyName <- getType ctx env obj
    tu <- Map.lookup tyName (ctxTaggedUnions ctx)
    let (caseNodes, defaultNodes) = partitionCases cases
    hicCases <- mapM (matchCase tu obj isPtr) caseNodes
    defCase <- case defaultNodes of
        []  -> return Nothing
        [d] -> findDefault d
        _   -> return Nothing
    return $ Fix $ H.HicNode $ Match obj isPtr tagField hicCases defCase
  where
    partitionCases [] = ([], [])
    partitionCases (c@(Fix (H.CimpleNode (C.Case _ _))):cs) =
        let (cas, def) = partitionCases cs in (c:cas, def)
    partitionCases (d@(Fix (H.CimpleNode (C.Default _))):cs) =
        let (cas, def) = partitionCases cs in (cas, d:def)
    partitionCases (Fix (H.CimpleNode (C.Group ss)):cs) =
        let (cas, def) = partitionCases ss
            (cas', def') = partitionCases cs
        in (cas ++ cas', def ++ def')
    partitionCases (_:cs) = partitionCases cs

    matchTagAccess = matchAccess

    matchCase tu obj isPtr (Fix (H.CimpleNode (C.Case valExpr body))) = do
        guard $ isSupportedBody body
        let transformedBody = liftMemberAccesses ctx tu obj isPtr body
        return $ MatchCase valExpr (removeTrailingBreak transformedBody)
    matchCase _ _ _ _ = Nothing

    findDefault (Fix (H.CimpleNode (C.Default body))) = do
        guard $ isSupportedBody body
        return $ Just $ removeTrailingBreak body
    findDefault _ = Nothing

isSupportedBody :: Node lexeme -> Bool
isSupportedBody (Fix (H.CimpleNode (C.CompoundStmt stmts))) =
    case reverse stmts of
        (Fix (H.CimpleNode C.Break):_)      -> True
        (Fix (H.CimpleNode (C.Return _)):_) -> True
        _                                   -> False
isSupportedBody (Fix (H.CimpleNode (C.Return _))) = True
isSupportedBody _ = False

removeTrailingBreak :: Node lexeme -> Node lexeme
removeTrailingBreak (Fix (H.CimpleNode (C.CompoundStmt stmts))) =
    Fix $ H.CimpleNode $ C.CompoundStmt $ case reverse stmts of
        (Fix (H.CimpleNode C.Break):rest) -> reverse rest
        _                                 -> stmts
removeTrailingBreak n = n

liftMemberAccesses :: Context -> H.HicNode (C.Lexeme Text) (Node (C.Lexeme Text)) -> Node (C.Lexeme Text) -> Bool -> Node (C.Lexeme Text) -> Node (C.Lexeme Text)
liftMemberAccesses _ tu obj isPtr = foldFix $ \f ->
    case f of
        H.CimpleNode (C.MemberAccess base member) ->
            case matchUnionField base of
                Just (obj', isPtr', uf) | isPtr' == isPtr && stripLoc obj' == stripLoc obj && uf == C.lexemeText (tuUnionField tu) ->
                    Fix $ H.HicNode $ TaggedUnionMemberAccess obj' (dummyLexeme uf) member
                _ -> Fix f
        _ -> Fix f
  where
    matchUnionField base = do
        (o, p, field) <- matchAccess base
        return (o, p, C.lexemeText field)

    stripLoc = foldFix $ \case
        H.CimpleNode n -> Fix $ H.CimpleNode (bimap (\(C.L _ c t) -> C.L (C.AlexPn 0 0 0) c t) id n)
        H.HicNode n    -> Fix $ H.HicNode (bimap (\(C.L _ c t) -> C.L (C.AlexPn 0 0 0) c t) id n)

inferGetter :: Context -> Map Text Text -> C.Scope -> Node (C.Lexeme Text) -> Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text))
inferGetter ctx env scope proto body =
    case body of
        Fix (H.CimpleNode (C.CompoundStmt [Fix (H.CimpleNode (C.Return (Just (Fix (H.CimpleNode (C.TernaryExpr cond thenExpr elseExpr))))))])) -> do
            (obj, isPtr, tagField, tagVal) <- matchTagCheck cond
            (unionField, member) <- matchMemberAccess thenExpr
            tyName <- getType ctx env obj
            _ <- Map.lookup tyName (ctxTaggedUnions ctx)
            return $ Fix $ H.HicNode $ TaggedUnionGet scope proto obj isPtr tagField tagVal unionField member elseExpr
        _ -> Nothing
  where
    matchTagCheck (Fix (H.CimpleNode (C.BinaryExpr lhs C.BopEq tagVal))) = do
        (obj, isPtr, field) <- matchAccess lhs
        return (obj, isPtr, field, tagVal)
    matchTagCheck _ = Nothing

    matchMemberAccess (Fix (H.CimpleNode (C.MemberAccess base member))) = do
        (_, _, unionField) <- matchAccess base
        return (unionField, member)
    matchMemberAccess (Fix (H.CimpleNode (C.PointerAccess base member))) = do
        (_, _, unionField) <- matchAccess base
        return (unionField, member)
    matchMemberAccess _ = Nothing


inferTagGetter :: Context -> Map Text Text -> C.Scope -> Node (C.Lexeme Text) -> Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text))
inferTagGetter ctx env scope proto body =
    case body of
        Fix (H.CimpleNode (C.CompoundStmt [Fix (H.CimpleNode (C.Return (Just expr)))])) -> do
            (obj, isPtr, tagField) <- matchTagAccess expr
            tyName <- getType ctx env obj
            _ <- Map.lookup tyName (ctxTaggedUnions ctx)
            return $ Fix $ H.HicNode $ TaggedUnionGetTag scope proto obj isPtr tagField
        _ -> Nothing
  where
    matchTagAccess = matchAccess


inferMapping :: Text -> [Text] -> [Text] -> ([TaggedUnionMember (C.Lexeme Text) (Node (C.Lexeme Text))], [Text])
inferMapping nameText enums unions =
    let prefix = findCommonPrefix enums
        (members, diags) = unzip $ map (mapEnum prefix) enums
    in (mapMaybe id members, concat diags)
  where
    mapEnum prefix enumVal =
        let normalized = T.toLower $ fromMaybe enumVal $ T.stripPrefix prefix enumVal
        in case findMatch normalized unions of
            Just unionMem -> (Just $ TaggedUnionMember (dummyLexeme enumVal) (dummyLexeme unionMem) (Fix (H.CimpleNode C.Continue)), [])
            Nothing ->
                let isSentinel = "invalid" `T.isSuffixOf` normalized || "unknown" `T.isSuffixOf` normalized
                    diags = if isSentinel then [] else ["TaggedUnion " <> nameText <> ": could not find union member for enum value " <> enumVal]
                in (Nothing, diags)

    findMatch normalized unionsMems =
        let stripped = T.replace "_" "" normalized
            normalize m = T.replace "struct " "" $ T.replace "_" "" (T.toLower m)
        in case filter (\m -> stripped `T.isSuffixOf` normalize m || normalize m `T.isSuffixOf` stripped) unionsMems of
            (m:_) -> Just m
            []    -> Nothing


findCommonPrefix :: [Text] -> Text
findCommonPrefix [] = ""
findCommonPrefix [x] =
    case T.breakOnEnd "_" x of
        (p, s) | not (T.null p) && not (T.null s) -> p
        _                                         -> ""
findCommonPrefix (x:xs) = foldl commonPrefix x xs
  where
    commonPrefix a b = T.pack $ map fst $ takeWhile (uncurry (==)) $ zip (T.unpack a) (T.unpack b)


-- | Phase 3: Validate invariants.
validate :: Context -> Program (C.Lexeme Text) -> [Text]
validate ctx (prog :: Program (C.Lexeme Text)) =
    concatMap (validateFile ctx) (Map.toList (progAsts prog))

validateFile :: Context -> (FilePath, [Node (C.Lexeme Text)]) -> [Text]
validateFile ctx (file, nodes) =
    concatMap (\node -> snd (foldFix alg node) Map.empty Nothing Map.empty) nodes
  where
    alg f = (Fix (fmap fst f), \env func safe ->
        case f of
            H.HicNode tu@TaggedUnion{} ->
                checkTaggedUnion ctx (fmap fst tu) ++ foldMap (\(_, check) -> check env func safe) f

            H.HicNode (Match obj _isPtr _tf cases def) ->
                let diags = snd obj env func safe
                    checkCase (MatchCase val body) =
                        let safe' = maybe safe (bless ctx env (fst obj) (fst val) safe) (matchObjName (fst obj))
                        in snd body env func safe'
                in diags ++ concatMap checkCase cases ++ maybe [] (\d -> snd d env func safe) def

            H.HicNode (TaggedUnionGet _ _ obj _isPtr _tf _tagVal uf m elseExpr) ->
                let safe' = maybe safe (\name -> Map.insertWith Set.union name (Set.singleton (C.lexemeText m)) safe) (matchObjName (fst obj))
                in snd obj env func safe ++
                   checkAccess "low-level" ctx env file func safe' (Fix (H.CimpleNode (C.PointerAccess (fst obj) uf))) m ++
                   snd elseExpr env func safe

            H.HicNode (TaggedUnionMemberAccess obj _uf field) ->
                snd obj env func safe ++
                checkAccess "high-level" ctx env file func safe (fst obj) field

            H.HicNode (TaggedUnionGetTag _ _ obj _isPtr _tf) ->
                snd obj env func safe
            H.HicNode TaggedUnionConstruct{} -> []

            H.CimpleNode (C.FunctionDefn _ proto body) ->
                case fst proto of
                    Fix (H.CimpleNode (C.FunctionPrototype _ name _)) ->
                        let func' = Just (C.lexemeText name)
                            env' = updateEnv ctx env (fmap fst f)
                        in snd body env' func' safe
                    _ -> snd body env func safe

            H.CimpleNode (C.CompoundStmt stmts) ->
                snd $ foldl (\(e, acc) (orig, check) -> (updateEnv ctx e (unFix orig), acc ++ check e func safe)) (env, []) stmts

            H.CimpleNode (C.Group stmts) ->
                snd $ foldl (\(e, acc) (orig, check) -> (updateEnv ctx e (unFix orig), acc ++ check e func safe)) (env, []) stmts

            H.CimpleNode (C.SwitchStmt expr _cases) ->
                case matchAccess (fst expr) of
                    Just (obj, _isPtr, _tf) ->
                        case getType ctx env obj of
                            Just tyName | Map.member tyName (ctxTaggedUnions ctx) ->
                                [C.sloc file (nodeLexeme (fst expr)) <> ": in function '" <> fromMaybe "" func <> "': Switch on tagged union '" <> tyName <> "' was not lifted to a match. Check for missing break/return in cases."]
                            _ -> foldMap (\(_, check) -> check env func safe) f
                    Nothing -> foldMap (\(_, check) -> check env func safe) f

            _ ->
                let env' = updateEnv ctx env (fmap fst f)
                    diags = foldMap (\(_, check) -> check env' func safe) f
                    localDiags = case f of
                        H.CimpleNode (C.MemberAccess obj field) -> checkAccess "low-level" ctx env' file func safe (fst obj) field
                        H.CimpleNode (C.PointerAccess obj field) -> checkAccess "low-level" ctx env' file func safe (fst obj) field
                        _ -> []
                in diags ++ localDiags)

type SafeAccesses = Map Text (Set Text)

matchObjName :: Node (C.Lexeme Text) -> Maybe Text
matchObjName = foldFix $ \case
    H.CimpleNode node -> case node of
        C.VarExpr l           -> Just (C.lexemeText l)
        C.PointerAccess obj _ -> obj
        C.MemberAccess obj _  -> obj
        _                     -> Nothing
    H.HicNode node -> case node of
        H.IterationElement l _ -> Just (C.lexemeText l)
        H.IterationIndex l     -> Just (C.lexemeText l)
        _                      -> Nothing

bless :: Context -> Map Text Text -> Node (C.Lexeme Text) -> Node (C.Lexeme Text) -> SafeAccesses -> Text -> SafeAccesses
bless ctx env expr val safe name =
    let tyName = case matchAccess expr of
            Just (obj, _, _) -> getType ctx env obj
            Nothing          -> getType ctx env expr
    in case (tyName, val) of
        (Just t, Fix (H.CimpleNode node)) ->
            let bless' v =
                    case Map.lookup t (ctxTaggedUnions ctx) of
                        Just tu ->
                            case filter (\m -> C.lexemeText (tumEnumVal m) == C.lexemeText v) (tuMembers tu) of
                                (m:_) ->
                                    let safeFields = Set.fromList [C.lexemeText (tumMember m), C.lexemeText (tuUnionField tu)]
                                    in Map.insertWith Set.union name safeFields safe
                                []    -> safe
                        Nothing -> safe
            in case node of
                C.VarExpr v       -> bless' v
                C.LiteralExpr _ v -> bless' v
                _                 -> safe
        _ -> safe

checkTaggedUnion :: Context -> H.HicNode (C.Lexeme Text) (Node (C.Lexeme Text)) -> [Text]
checkTaggedUnion ctx (TaggedUnion name tagType _ unionType _ _) =
    let eName = fromMaybe "" (getTypeName tagType)
        uName = fromMaybe "" (getTypeName unionType)
        enumName = resolveTypedef ctx eName
        unionName = resolveTypedef ctx uName
    in case Map.lookup unionName (ctxUnions ctx) of
        Just unionMembers ->
            let enumMembers = fromMaybe [] (Map.lookup enumName (ctxEnums ctx))
                (_, diags) = inferMapping (C.lexemeText name) enumMembers unionMembers
            in diags
        Nothing -> []
checkTaggedUnion _ _ = []

nodeLexeme :: Node (C.Lexeme Text) -> C.Lexeme Text
nodeLexeme n = case foldFix C.concats n of
    (l:_) -> l
    []    -> dummyLexeme "unknown"

checkAccess :: Text -> Context -> Map Text Text -> FilePath -> Maybe Text -> SafeAccesses -> Node (C.Lexeme Text) -> C.Lexeme Text -> [Text]
checkAccess kind ctx env file func safe obj field =
    case getType ctx env obj of
        Just tyName | Map.member tyName (ctxTaggedUnions ctx) ->
             if isSafe safe obj field
             then []
             else
                 let loc = C.sloc file field
                     msg = ": Unrecognized " <> kind <> " access to tagged union '" <> tyName <> "' field '" <> C.lexemeText field <> "'"
                     fmsg = maybe "" (\f -> ": in function '" <> f <> "'") func
             in [loc <> fmsg <> msg]
        _ -> []

isSafe :: SafeAccesses -> Node (C.Lexeme Text) -> C.Lexeme Text -> Bool
isSafe safe obj field =
    case matchObjName obj of
        Just name -> maybe False (Set.member (C.lexemeText field)) (Map.lookup name safe)
        Nothing   -> False


-- | Lowering logic.
lower :: forall l. H.HicNode l (C.Node l) -> Maybe (C.Node l)
lower (TaggedUnion name tagType tagField unionType unionField _members) =
    Just $ Fix $ C.Struct name
        [ Fix $ C.MemberDecl (Fix $ C.VarDecl tagType tagField []) Nothing
        , Fix $ C.MemberDecl (Fix $ C.VarDecl unionType unionField []) Nothing
        ]

lower (TaggedUnionGet scope proto obj isPtr tagField tagVal unionField member elseExpr) =
    Just $ Fix $ C.FunctionDefn scope proto $
        Fix $ C.CompoundStmt [Fix $ C.Return $ Just $
            Fix $ C.TernaryExpr cond thenExpr elseExpr]
  where
    cond = Fix $ C.BinaryExpr (if isPtr then Fix (C.PointerAccess obj tagField) else Fix (C.MemberAccess obj tagField)) C.BopEq tagVal
    thenExpr = Fix $ C.MemberAccess (if isPtr then Fix (C.PointerAccess obj unionField) else Fix (C.MemberAccess obj unionField)) member

lower (Match obj isPtr tagField cases def) =
    Just $ Fix $ C.SwitchStmt expr (map lowerCase cases ++ maybe [] ((:[]) . lowerDefault) def)
  where
    expr = Fix $ if isPtr then C.PointerAccess obj tagField else C.MemberAccess obj tagField
    lowerCase (MatchCase val body) = Fix $ C.Case val (addTrailingBreak body)
    lowerDefault body = Fix $ C.Default (addTrailingBreak body)

lower (TaggedUnionMemberAccess obj unionField member) =
    Just $ Fix $ C.MemberAccess (Fix $ C.PointerAccess obj unionField) member

lower (TaggedUnionGetTag scope proto obj isPtr tagField) =
    Just $ Fix $ C.FunctionDefn scope proto $
        Fix $ C.CompoundStmt [Fix $ C.Return $ Just $
            if isPtr then Fix (C.PointerAccess obj tagField) else Fix (C.MemberAccess obj tagField)]

lower (TaggedUnionConstruct obj isPtr _ty tagField tagVal unionField member dataVal) =
    Just $ Fix $ C.Group
        [ Fix $ C.ExprStmt $ Fix $ C.AssignExpr lhsTag C.AopEq tagVal
        , Fix $ C.ExprStmt $ Fix $ C.AssignExpr lhsData C.AopEq dataVal
        ]
  where
    lhsTag = if isPtr then Fix (C.PointerAccess obj tagField) else Fix (C.MemberAccess obj tagField)
    lhsData =
        let base = if isPtr then Fix (C.PointerAccess obj unionField) else Fix (C.MemberAccess obj unionField)
        in Fix $ C.MemberAccess base member

lower _ = Nothing

addTrailingBreak :: C.Node l -> C.Node l
addTrailingBreak (Fix (C.CompoundStmt stmts)) =
    Fix $ C.CompoundStmt $ case reverse stmts of
        (Fix (C.Return _):_) -> stmts
        (Fix C.Break:_)      -> stmts
        _                    -> stmts ++ [Fix C.Break]
addTrailingBreak n = n

