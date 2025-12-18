{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE RankNTypes          #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Inference.Passes.Iteration
    ( feature
    ) where

import           Control.Monad.State.Strict           (State, modify)
import qualified Control.Monad.State.Strict           as State
import           Data.Fix                             (Fix (..), foldFix)
import           Data.Foldable                        (foldMap)
import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Maybe                           (listToMaybe)
import           Data.Text                            (Text)
import qualified Language.Cimple                      as C
import           Language.Hic.Ast                     (HicNode (..), Node,
                                                       NodeF (..))
import           Language.Hic.Inference.Context       (Context (..))
import           Language.Hic.Inference.Feature       (Feature (..))
import           Language.Hic.Inference.Program.Types (Program (..))
import           Language.Hic.Inference.Utils         (dummyLexeme, getTypeName)

feature :: Feature
feature = Feature
    { featureName     = "Iteration"
    , featureGather   = \_ ctx -> ctx
    , featureInfer    = infer
    , featureValidate = validate
    , featureLower    = lower
    }

-- | Phase 2: Infer Iteration constructs.
infer :: Context -> FilePath -> Node (C.Lexeme Text) -> State Bool (Node (C.Lexeme Text))
infer ctx _file node = snd (foldFix alg node) Map.empty
  where
    alg f =
        let original = Fix (fmap fst f)
        in (original, \env -> do
            let env' = updateEnv env (fmap fst f)
            f' <- traverse (\(_, transform) -> transform env') f
            let n' = Fix f'
            case attemptTransform ctx env' n' of
                Just newNode -> modify (const True) >> return newNode
                Nothing      -> return n')

attemptTransform :: Context -> Map Text Text -> Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text))
attemptTransform _ctx _env node =
    case node of
        Fix (CimpleNode (C.ForStmt lInit lCond lStep lBody)) ->
            inferFor lInit lCond lStep lBody
        Fix (CimpleNode (C.CompoundStmt stmts)) ->
            Fix . CimpleNode . C.CompoundStmt <$> inferFind stmts
        _ -> Nothing

inferFor :: Node (C.Lexeme Text) -> Node (C.Lexeme Text) -> Node (C.Lexeme Text) -> Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text))
inferFor lInit lCond lStep lBody = do
    (itL, _) <- matchInit lInit
    (itL2, _, _) <- matchCond lCond
    let it = C.lexemeText itL
    if it /= C.lexemeText itL2 then Nothing else do
        _ <- matchStep it lStep
        containers <- identifyContainers it lBody
        if isAssigned it lBody then Nothing else do
            let feBody' = substitute it containers lBody
            return $ Fix $ HicNode $ ForEach
                { feIterators  = replicate (length containers) itL
                , feInit       = lInit
                , feCond       = lCond
                , feStep       = lStep
                , feContainers = containers
                , feBody       = feBody'
                , feHasIndex   = hasIndex feBody'
                }

matchInit :: Node (C.Lexeme Text) -> Maybe (C.Lexeme Text, Node (C.Lexeme Text))
matchInit (Fix (CimpleNode (C.VarDeclStmt (Fix (CimpleNode (C.VarDecl _ name []))) (Just val)))) =
    Just (name, val)
matchInit (Fix (CimpleNode (C.AssignExpr (Fix (CimpleNode (C.VarExpr name))) C.AopEq val))) =
    Just (name, val)
matchInit _ = Nothing

matchCond :: Node (C.Lexeme Text) -> Maybe (C.Lexeme Text, C.BinaryOp, Node (C.Lexeme Text))
matchCond (Fix (CimpleNode (C.BinaryExpr (Fix (CimpleNode (C.VarExpr name))) op bound))) =
    Just (name, op, bound)
matchCond _ = Nothing

matchStep :: Text -> Node (C.Lexeme Text) -> Maybe ()
matchStep it (Fix (CimpleNode (C.UnaryExpr op (Fix (CimpleNode (C.VarExpr name))))))
    | it == C.lexemeText name && (op == C.UopIncr) = Just ()
matchStep it (Fix (CimpleNode (C.AssignExpr (Fix (CimpleNode (C.VarExpr name))) C.AopPlus val)))
    | it == C.lexemeText name && isOne val = Just ()
matchStep _ _ = Nothing

isOne :: Node (C.Lexeme Text) -> Bool
isOne = foldFix $ \case
    CimpleNode (C.LiteralExpr C.Int l) -> C.lexemeText l == "1"
    _                                  -> False

identifyContainers :: Text -> Node (C.Lexeme Text) -> Maybe [Node (C.Lexeme Text)]
identifyContainers it bodyNode =
    let usages = findUsages it bodyNode
        indexings = [ c | Indexing c <- usages ]
    in if null indexings
       then Nothing
       else do
           let containerMap = Map.fromList [ (C.removeSloc (stripHic c), c) | c <- indexings ]
           let uniqueContainers = Map.elems containerMap
           if all isStable uniqueContainers then Just uniqueContainers else Nothing

isStable :: Node (C.Lexeme Text) -> Bool
isStable node = fst $ foldFix alg node
  where
    alg f = (stable, constant)
      where
        constant = case f of
            CimpleNode (C.LiteralExpr _ _) -> True
            _                              -> False

        stable = case f of
            CimpleNode (C.VarExpr _)                 -> True
            CimpleNode (C.MemberAccess (s, _) _)     -> s
            CimpleNode (C.PointerAccess (s, _) _)    -> s
            CimpleNode (C.ArrayAccess (s, _) (_, c)) -> s && c
            CimpleNode (C.ParenExpr (s, _))          -> s
            _                                        -> False

isAssigned :: Text -> Node (C.Lexeme Text) -> Bool
isAssigned it node = fst $ foldFix alg node
  where
    alg :: NodeF (C.Lexeme Text) (Bool, Bool) -> (Bool, Bool)
    alg f = (assigned, isIter)
      where
        isIter = case f of
            CimpleNode (C.VarExpr i) -> C.lexemeText i == it
            _                        -> False

        assigned = (case f of
            CimpleNode (C.AssignExpr (_, lhsIsIter) _ (rhsAssigned, _)) -> lhsIsIter || rhsAssigned
            CimpleNode (C.UnaryExpr op (eAssigned, eIsIter)) ->
                (op `elem` [C.UopIncr, C.UopDecr] && eIsIter) || eAssigned
            _ -> any fst f)

stripHic :: Node (C.Lexeme Text) -> C.Node (C.Lexeme Text)
stripHic = foldFix $ \case
    CimpleNode f -> Fix f
    HicNode h    ->
        case h of
            IterationElement _ c -> Fix (C.ArrayAccess c (Fix (C.VarExpr (dummyLexeme "dummy"))))
            IterationIndex _     -> Fix (C.VarExpr (dummyLexeme "dummy"))
            _                    -> error "Unexpected HicNode in identifyContainers"

data Usage = Indexing (Node (C.Lexeme Text))

data UsageInfo = UsageInfo
    { uiNode   :: Node (C.Lexeme Text)
    , uiUsages :: [Usage]
    , uiIsIter :: Bool
    }

findUsages :: Text -> Node (C.Lexeme Text) -> [Usage]
findUsages it = uiUsages . foldFix alg
  where
    alg :: NodeF (C.Lexeme Text) UsageInfo -> UsageInfo
    alg f = UsageInfo
        { uiNode = Fix (fmap uiNode f)
        , uiUsages = usages
        , uiIsIter = isIter
        }
      where
        isIter = case f of
            CimpleNode (C.VarExpr i) -> C.lexemeText i == it
            _                        -> False

        usages = (case f of
            CimpleNode (C.ArrayAccess container idx) ->
                if uiIsIter idx then [Indexing (uiNode container)] else []
            HicNode (IterationElement _ container) -> [Indexing (uiNode container)]
            _ -> []) ++ foldMap uiUsages f

isVar :: Text -> Node (C.Lexeme Text) -> Bool
isVar it = foldFix $ \case
    CimpleNode (C.VarExpr i) -> C.lexemeText i == it
    HicNode (IterationIndex i) -> C.lexemeText i == it
    _                        -> False

substitute :: Text -> [Node (C.Lexeme Text)] -> Node (C.Lexeme Text) -> Node (C.Lexeme Text)
substitute it containers = foldFix $ \f ->
    case f of
        CimpleNode (C.ArrayAccess c idx)
            | isVar it idx ->
                case listToMaybe [ con | con <- containers, C.removeSloc (stripHic c) == C.removeSloc (stripHic con) ] of
                    Just con | length containers == 1 ->
                        case extractLexeme idx of
                            Just l  -> Fix (HicNode (IterationElement l con))
                            Nothing -> error "substitute: expected VarExpr"
                    _ -> Fix (CimpleNode (C.ArrayAccess c (Fix (HicNode (IterationIndex (dummyLexeme it))))))
        CimpleNode (C.VarExpr i)
            | C.lexemeText i == it ->
                Fix (HicNode (IterationIndex i))
        _ -> Fix f
  where
    extractLexeme :: Node (C.Lexeme Text) -> Maybe (C.Lexeme Text)
    extractLexeme = foldFix $ \case
        CimpleNode (C.VarExpr l)   -> Just l
        CimpleNode (C.ParenExpr e) -> e
        HicNode (IterationIndex l) -> Just l
        _                          -> Nothing

hasIndex :: Node (C.Lexeme Text) -> Bool
hasIndex = foldFix $ \case
    HicNode (IterationIndex _) -> True
    f                          -> any id f

inferFind :: [Node (C.Lexeme Text)] -> Maybe [Node (C.Lexeme Text)]
inferFind stmts = do
    (prefix, loop, suffix) <- findLoop stmts
    case loop of
        Fix (CimpleNode (C.ForStmt lInit lCond lStep lBody)) -> do
            (itL, _) <- matchInit lInit
            (itL2, _, _) <- matchCond lCond
            let it = C.lexemeText itL
            if it /= C.lexemeText itL2 then Nothing else do
                _ <- matchStep it lStep
                (lPred, foundAction) <- matchFindBody it lBody
                containers <- identifyContainers it lPred
                container <- listToMaybe containers
                let newStmt = Fix $ HicNode $ Find
                        { fIterator  = itL
                        , fInit      = lInit
                        , fCond      = lCond
                        , fStep      = lStep
                        , fContainer = container
                        , fPredicate = substitute it [container] lPred
                        , fOnFound   = substitute it [container] foundAction
                        , fOnMissing = listToMaybe suffix
                        }
                return $ prefix ++ [newStmt] ++ drop 1 suffix
        Fix (HicNode (ForEach (itL:_) lInit lCond lStep _ lBody _)) -> do
            let it = C.lexemeText itL
            (lPred, foundAction) <- matchFindBody it lBody
            -- ForEach already has containers, but we want the one used in lPred
            containers' <- identifyContainers it lPred
            container <- listToMaybe containers'
            let newStmt = Fix $ HicNode $ Find
                    { fIterator  = itL
                    , fInit      = lInit
                    , fCond      = lCond
                    , fStep      = lStep
                    , fContainer = container
                    , fPredicate = substitute it [container] lPred
                    , fOnFound   = substitute it [container] foundAction
                    , fOnMissing = listToMaybe suffix
                    }
            return $ prefix ++ [newStmt] ++ drop 1 suffix
        _ -> Nothing

findLoop :: [Node (C.Lexeme Text)] -> Maybe ([Node (C.Lexeme Text)], Node (C.Lexeme Text), [Node (C.Lexeme Text)])
findLoop [] = Nothing
findLoop (s@(Fix (CimpleNode C.ForStmt{})) : ss) = Just ([], s, ss)
findLoop (s@(Fix (HicNode ForEach{})) : ss)      = Just ([], s, ss)
findLoop (s : ss) = do
    (p, l, su) <- findLoop ss
    return (s:p, l, su)

matchFindBody :: Text -> Node (C.Lexeme Text) -> Maybe (Node (C.Lexeme Text), Node (C.Lexeme Text))
matchFindBody it (Fix (CimpleNode (C.CompoundStmt [Fix (CimpleNode (C.IfStmt cond then_ Nothing)) ]))) =
    if usesIterator it cond then Just (cond, then_) else Nothing
matchFindBody it (Fix (CimpleNode (C.IfStmt cond (Fix (CimpleNode (C.CompoundStmt [then_]))) Nothing))) =
    if usesIterator it cond then Just (cond, then_) else Nothing
matchFindBody it (Fix (CimpleNode (C.IfStmt cond then_ Nothing))) =
    if usesIterator it cond then Just (cond, then_) else Nothing
matchFindBody _ _ = Nothing

usesIterator :: Text -> Node (C.Lexeme Text) -> Bool
usesIterator it = foldFix $ \case
    CimpleNode (C.VarExpr i) | C.lexemeText i == it -> True
    HicNode (IterationIndex i) | C.lexemeText i == it -> True
    HicNode (IterationElement i _) | C.lexemeText i == it -> True
    f -> any id f

updateEnv :: Map Text Text -> NodeF (C.Lexeme Text) (Node (C.Lexeme Text)) -> Map Text Text
updateEnv env (CimpleNode (C.VarDecl ty name _)) =
    case getTypeName ty of
        Just tyName -> Map.insert (C.lexemeText name) tyName env
        Nothing     -> env
updateEnv env (CimpleNode (C.VarDeclStmt (Fix (CimpleNode (C.VarDecl ty name _))) _)) =
    case getTypeName ty of
        Just tyName -> Map.insert (C.lexemeText name) tyName env
        Nothing     -> env
updateEnv env (CimpleNode (C.FunctionDefn _ (Fix (CimpleNode (C.FunctionPrototype _ _ params))) _)) =
    foldl updateFromParam env params
  where
    updateFromParam e (Fix (CimpleNode (C.VarDecl ty name _))) =
        case getTypeName ty of
            Just tyName -> Map.insert (C.lexemeText name) tyName e
            Nothing     -> e
    updateFromParam e _ = e
updateEnv env (CimpleNode (C.FunctionPrototype _ _ params)) =
    foldl updateFromParam env params
  where
    updateFromParam e (Fix (CimpleNode (C.VarDecl ty name _))) =
        case getTypeName ty of
            Just tyName -> Map.insert (C.lexemeText name) tyName e
            Nothing     -> e
    updateFromParam e _ = e
updateEnv env _ = env


paraFix :: Functor f => (f (Fix f, a) -> a) -> Fix f -> a
paraFix f = snd . foldFix (\x -> (Fix (fmap fst x), f x))

validate :: Context -> Program (C.Lexeme Text) -> [Text]
validate _ ctx = concatMap validateFile (Map.toList (progAsts ctx))
  where
    validateFile (file, nodes) = concatMap (checkIteration file) nodes

    checkIteration file = paraFix $ \f ->
        checkNode file (Fix (fmap fst f)) ++ foldMap snd f

    checkNode file (Fix (CimpleNode (C.ForStmt lInit lCond lStep lBody))) =
        case matchInit lInit of
            Just (itL, _) ->
                let it = C.lexemeText itL in
                case matchCond lCond of
                    Just (itL2, _, _) | it == C.lexemeText itL2 ->
                        case matchStep it lStep of
                            Just () -> checkIterationCandidate file itL lBody
                            Nothing -> []
                    _ -> []
            _ -> []
    checkNode _ _ = []

    checkIterationCandidate file itL lBody =
        let it = C.lexemeText itL
            usages = findUsages it lBody
            indexings = [ c | Indexing c <- usages ]
        in if null indexings then []
           else if isAssigned it lBody then [C.sloc file itL <> ": Induction variable '" <> it <> "' is modified within the loop body. Refactor to enable for_each lifting."]
           else case Map.elems $ Map.fromList [ (stripHic c, c) | c <- indexings ] of
               cs | any (not . isStable) cs -> [C.sloc file itL <> ": Container expression is not stable. Refactor to enable for_each lifting."]
               _ -> []

lower :: forall l. HicNode l (C.Node l) -> Maybe (C.Node l)
lower (ForEach _is lInit lCond lStep _cons lBody _hi) =
    Just $ Fix $ C.ForStmt lInit lCond lStep lBody

lower (Find _i lInit lCond lStep _con lPred foundAction m) =
    let body = Fix $ C.CompoundStmt [ Fix $ C.IfStmt lPred foundAction Nothing ]
    in Just $ Fix $ C.Group $
        [ Fix $ C.ForStmt lInit lCond lStep body ]
        ++ maybe [] (:[]) m

lower (IterationElement i c) =
    Just $ Fix $ C.ArrayAccess c (Fix (C.VarExpr i))

lower (IterationIndex i) =
    Just $ Fix $ C.VarExpr i

lower _ = Nothing
