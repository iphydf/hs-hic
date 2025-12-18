{-# LANGUAGE BangPatterns      #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE StrictData        #-}
{-# LANGUAGE TupleSections     #-}

module Language.Hic.Refined.Transition
    ( TransitionEnv (..)
    , StepResult
    , step
    , isRefinable
    , isParameter
    , isBot
    , isTop
    , isNonnull
    , variableKey
    ) where

import           Control.Applicative              ((<|>))
import           Control.Monad                    (zipWithM)
import           Control.Monad.Writer.Strict      (Writer, listen, runWriter,
                                                   tell)
import           Data.Bits                        ((.&.), (.|.))
import qualified Data.Char                        as Char
import           Data.Hashable                    (hash)
import qualified Data.IntMap.Merge.Strict         as IntMap
import           Data.IntMap.Strict               (IntMap)
import qualified Data.IntMap.Strict               as IntMap
import qualified Data.List                        as List
import qualified Data.Map.Merge.Strict            as Map
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Maybe                       (fromJust, fromMaybe, isJust,
                                                   isNothing)
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Text                        (Text)
import qualified Data.Text                        as T
import           Data.Word                        (Word16, Word32)
import qualified Debug.Trace                      as Debug
import           Language.Cimple                  (Lexeme (..))
import qualified Language.Cimple                  as C
import           Language.Hic.Refined.Context     (MappingContext,
                                                   MappingRefinements (..),
                                                   emptyRefinements, getMapping,
                                                   getRefinement, pushMapping,
                                                   setRefinement)
import           Language.Hic.Refined.LatticeOp   (Polarity (..), Variance (..),
                                                   applyVariance)
import           Language.Hic.Refined.PathContext (PathContext (..),
                                                   SymbolicPath,
                                                   ValueConstraint (..))
import           Language.Hic.Refined.Registry    (Member (..), Registry (..),
                                                   TypeDefinition (..))
import           Language.Hic.Refined.State       (ProductState (..))
import           Language.Hic.Refined.Types       (AnyRigidNodeF (..),
                                                   Index (..),
                                                   LatticePhase (..),
                                                   Nullability (..),
                                                   ObjectStructure (..),
                                                   Ownership (..),
                                                   PropertyKind (..),
                                                   PtrTarget (..), Quals (..),
                                                   RefStructure (..),
                                                   ReturnType (..),
                                                   RigidNodeF (..),
                                                   StdType (..),
                                                   TemplateId (..),
                                                   TerminalNode (..))

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

-- | Deterministic, Node ID-invariant identifier for a node.
getStableNodeIdent :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> Word32 -> (Int, Int)
getStableNodeIdent nodes i = getStableNodeIdent' Set.empty nodes i

getStableNodeIdent' :: Set Word32 -> Map Word32 (AnyRigidNodeF TemplateId Word32) -> Word32 -> (Int, Int)
getStableNodeIdent' visited nodes i
    | Set.member i visited = (13 :: Int, 0 :: Int) -- Cycle detected
    | otherwise = case Map.lookup i nodes of
        Just (AnyRigidNodeF (RObject s _)) ->
            case s of
                VNominal l ps -> (0 :: Int, hash (C.lexemeText l, map (getStableNodeIdent' (Set.insert i visited) nodes) ps))
                VBuiltin bt  -> (1 :: Int, fromEnum bt)
                VVar tid _   -> (2 :: Int, hashTemplateId' (Set.insert i visited) nodes tid)
                VEnum l      -> (3 :: Int, hash (C.lexemeText l))
                VSingleton _ val -> (4 :: Int, fromIntegral (val .&. 0xFFFFFFFF))
                VExistential ts b -> (5 :: Int, hash (ts, getStableNodeIdent' (Set.insert i visited) nodes b))
                VVariant m -> (6 :: Int, hash (IntMap.keys m))
                VProperty _ pk -> (7 :: Int, hash pk)
                VSizeExpr ts -> (8 :: Int, hash (map snd ts))
        Just (AnyRigidNodeF (RReference r _ _ _)) ->
            let rIdent = case r of { Arr _ _ -> 0 :: Int; Ptr _ -> 1 :: Int }
            in (9 :: Int, rIdent)
        Just (AnyRigidNodeF (RFunction _ _))      -> (10 :: Int, 0 :: Int)
        Just (AnyRigidNodeF (RTerminal t))         ->
            let tIdent = case t of { SBottom -> 0 :: Int; SAny -> 1 :: Int; SConflict -> 2 :: Int; STerminal _ -> 3 :: Int }
            in (11 :: Int, tIdent)
        _ -> (12 :: Int, fromIntegral i)

-- | Stable comparison for TemplateId that ignores Node IDs where possible.
hashTemplateId :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> TemplateId -> Int
hashTemplateId nodes tid = hashTemplateId' Set.empty nodes tid

hashTemplateId' :: Set Word32 -> Map Word32 (AnyRigidNodeF TemplateId Word32) -> TemplateId -> Int
hashTemplateId' visited nodes = \case
    TIdName t      -> hash (0 :: Int, t)
    TIdParam p i _ -> hash (1 :: Int, p, i)
    TIdSkolem l r i -> hash (2 :: Int, i, getStableNodeIdent' visited nodes l, getStableNodeIdent' visited nodes r)
    TIdInstance i  -> hash (3 :: Int, i)
    TIdDeBruijn i  -> hash (4 :: Int, i)

getQuals :: AnyRigidNodeF tid a -> Quals
getQuals = \case
    AnyRigidNodeF (RObject _ q)         -> q
    AnyRigidNodeF (RReference _ _ _ q)  -> q
    AnyRigidNodeF (RFunction _ _)       -> Quals False False -- Functions are not 'objects' anyway
    AnyRigidNodeF (RTerminal _)         -> Quals True False  -- Terminals are semantically constant but not physical objects

isObject :: RigidNodeF k tid a -> Bool
isObject = \case
    RObject{} -> True
    _         -> False

-- | DETERMINISTIC comparison of TemplateIds to ensure commutativity and stable variable choice.
stableCompareTID :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> TemplateId -> TemplateId -> Ordering
stableCompareTID nodes tid1 tid2 = compare (tidIdent' Set.empty tid1) (tidIdent' Set.empty tid2)
  where
    tidIdent' :: Set Word32 -> TemplateId -> (Int, Int, Int, Int)
    tidIdent' visited = \case
        TIdName t       -> (0 :: Int, hash t, 0, 0)
        TIdParam p i _  -> (1 :: Int, fromIntegral i, fromEnum p, 0)
        TIdSkolem l r i ->
            let (cL, vL) = getStableNodeIdent' visited nodes l
                (cR, vR) = getStableNodeIdent' visited nodes r
            in (2 :: Int, fromIntegral i, hash (cL, vL), hash (cR, vR))
        TIdInstance i   -> (3 :: Int, fromIntegral (i .&. 0xFFFFFFFF), 0, 0)
        TIdDeBruijn i   -> (4 :: Int, fromIntegral i, 0, 0)

-- | The environment for a single step of the Product Automaton.
data TransitionEnv a = TransitionEnv
    { teNodes       :: Map Word32 (AnyRigidNodeF TemplateId a)
    -- ^ The type graph segment being solved
    , teRegistry    :: Registry a
    -- ^ Source of truth for nominal type members
    , tePolarity    :: Polarity
    -- ^ Join or Meet
    , tePathCtx     :: PathContext
    -- ^ Local symbolic state for refinement projection
    , teCurrentPath :: SymbolicPath
    -- ^ Current symbolic cursor (e.g., p->tag)
    , teTerminals   :: (a, a, a, a)
    -- ^ (Bottom, Any, Conflict, STerminal) IDs for the graph
    , teRefineL     :: Bool
    -- ^ Whether psNodeL can be refined
    , teRefineR     :: Bool
    -- ^ Whether psNodeR can be refined
    }
    deriving (Show, Eq, Ord)

-- | The result of a transition step.
-- Maps to a node where each child is a 'ProductState' (L_id, R_id, Gamma).
type StepResult = AnyRigidNodeF TemplateId ProductState

getEffectiveNode :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) (Word32, Maybe (AnyRigidNodeF TemplateId Word32))
getEffectiveNode nodes refs depth i = case Map.lookup i nodes of
    Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid ->
        let key = variableKey nodes depth tid
        in do
            tell (Set.singleton key)
            case getRefinement key refs of
                Just refinedId | refinedId /= i ->
                    dtrace ("getEffectiveNode: following " ++ show i ++ " (" ++ show tid ++ ") -> " ++ show refinedId) $
                    getEffectiveNode nodes refs depth refinedId
                _               -> return (i, Map.lookup i nodes)
    n -> return (i, n)

getEffectiveObject :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) (Maybe (ObjectStructure TemplateId Word32))
getEffectiveObject nodes refs depth rId = do
    (_, mNode) <- getEffectiveNode nodes refs depth rId
    case mNode of
        Just (AnyRigidNodeF (RObject s _)) ->
            return $ Just $ case s of
                VBuiltin bt       -> VBuiltin bt
                VSingleton bt v   -> VSingleton bt v
                VNominal l ps     -> VNominal (fmap id l) ps
                VEnum l           -> VEnum (fmap id l)
                VVar tid idx      -> VVar (id tid) (fmap (fmap id) idx)
                VExistential ts b -> VExistential (map id ts) b
                VVariant m        -> VVariant m
                VProperty a pk    -> VProperty a pk
                VSizeExpr ts      -> VSizeExpr ts
        _ -> return Nothing

isNull :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) Bool
isNull nodes refs depth i = do
    (_, mNode) <- getEffectiveNode nodes refs depth i
    return $ case mNode of
        Just (AnyRigidNodeF (RObject (VBuiltin NullPtrTy) _)) -> True
        Just (AnyRigidNodeF (RTerminal SBottom))              -> True
        _                                                     -> False

isBot :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) Bool
isBot nodes refs depth i = fst <$> isBot' Map.empty Set.empty nodes refs depth i

isBot' :: Map Word32 Bool -> Set Word32 -> Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) (Bool, Map Word32 Bool)
isBot' memo visited nodes refs depth i
    | Just res <- Map.lookup i memo = return (res, memo)
    | Set.member i visited = return (False, memo)
    | otherwise = do
        ((_, mNode), _) <- listen $ getEffectiveNode nodes refs depth i
        case mNode of
            Just (AnyRigidNodeF n) ->
                case n of
                    RTerminal SBottom                      -> return (True, Map.insert i True memo)
                    RObject (VBuiltin NullPtrTy) _         -> return (True, Map.insert i True memo)
                    RObject (VVariant m) _ | IntMap.null m -> return (True, Map.insert i True memo)
                    _ -> do
                        let go m' [] = return (False, m')
                            go m' (c:cs) = do
                                (res, m'') <- isBot' m' (Set.insert i visited) nodes refs depth c
                                if res then return (True, Map.insert i True m'')
                                       else go m'' cs
                        go memo (foldMap (:[]) n)
            _ -> return (False, Map.insert i False memo)

isTop :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) Bool
isTop nodes refs depth i = fst <$> isTop' Map.empty Set.empty nodes refs depth i

isTop' :: Map Word32 Bool -> Set Word32 -> Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) (Bool, Map Word32 Bool)
isTop' memo visited nodes refs depth i
    | Just res <- Map.lookup i memo = return (res, memo)
    | Set.member i visited = return (False, memo)
    | otherwise = do
        ((_, mNode), _) <- listen $ getEffectiveNode nodes refs depth i
        case mNode of
            Just (AnyRigidNodeF n) -> do
                selfTop <- case n of
                    RTerminal SConflict -> return True
                    RReference (Ptr (TargetObject t)) QNonnull' _ _ -> isBot nodes refs depth t
                    RReference (Arr e _) QNonnull' _ _ -> isBot nodes refs depth e
                    _ -> return False
                if selfTop then return (True, Map.insert i True memo)
                else do
                    let go m' [] = return (False, m')
                        go m' (c:cs) = do
                            (res, m'') <- isTop' m' (Set.insert i visited) nodes refs depth c
                            if res then return (True, Map.insert i True m'')
                                   else go m'' cs
                    go memo (foldMap (:[]) n)
            _ -> return (False, Map.insert i False memo)

isNonnull :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> MappingRefinements -> Int -> Word32 -> Writer (Set Int) Bool
isNonnull nodes refs depth i = do
    (_, mNode) <- getEffectiveNode nodes refs depth i
    return $ case mNode of
        Just (AnyRigidNodeF (RReference _ QNonnull' _ _)) -> True
        Just (AnyRigidNodeF (RFunction _ _))              -> True
        _                                                 -> False

-- | Handles mismatched categories in the Product Automaton.
stepMismatch :: Polarity -> MappingRefinements -> (StepResult, MappingRefinements)
stepMismatch pol refs = case pol of
    PJoin -> (AnyRigidNodeF (RTerminal SAny), refs) -- Generalize to Top
    PMeet -> (AnyRigidNodeF (RTerminal SConflict), refs) -- Conflict during refinement

-- | Handles function cases in the Product Automaton.
stepFunction :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Maybe (AnyRigidNodeF TemplateId Word32) -> Maybe (AnyRigidNodeF TemplateId Word32) -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepFunction env ps refs nodeL nodeR =
    let gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        pol = psPolarity ps
        oneWay = psOneWay ps
    in case (nodeL, nodeR) of
        (Just (AnyRigidNodeF (RFunction aL rL)), Just (AnyRigidNodeF (RFunction aR rR))) ->
            if length aL /= length aR
               then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
               else do
                   (refs1, aStates) <- refineParams env pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps) refs (replicate (length aL) Contravariant) aL aR
                   (newRefs, mRet) <- refineReturnType env pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps) refs1 rL rR
                   case mRet of
                       Just ret -> return $ Just (AnyRigidNodeF (RFunction aStates ret), newRefs)
                       Nothing  -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
        _ -> return Nothing

-- | Handles reference cases (pointers and arrays) in the Product Automaton.
stepReference :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Maybe (AnyRigidNodeF TemplateId Word32) -> Maybe (AnyRigidNodeF TemplateId Word32) -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepReference env ps refs nodeL nodeR =
    let nodes = teNodes env
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        pol = psPolarity ps
        oneWay = psOneWay ps
    in case (nodeL, nodeR) of
        (Just (AnyRigidNodeF (RReference sL nL oL qL)), Just (AnyRigidNodeF (RReference sR nR oR qR))) ->
            let qRes = Quals { qConst = case pol of
                                    PJoin -> qConst qL || qConst qR
                                    PMeet -> qConst qL && qConst qR
                             , qPhysical = case pol of
                                    PJoin -> qPhysical qL && qPhysical qR
                                    PMeet -> qPhysical qL || qPhysical qR
                             }
                nRes = case pol of
                    PJoin -> max nL nR
                    PMeet -> min nL nR
                oRes = case pol of
                    PJoin -> min oL oR -- Join(Owned, NonOwned) = NonOwned
                    PMeet -> max oL oR -- Meet(Owned, NonOwned) = Owned
            in case (sL, sR) of
                (Ptr pL, Ptr pR) -> do
                    let isTargetBot' d  = \case { TargetObject i -> isBot nodes refs d i; _ -> return False }
                        isTargetTop' d  = \case { TargetObject i -> isTop nodes refs d i; _ -> return False }
                    -- Lattice: Ptr(Bottom) = Bottom, Ptr(Conflict) = Conflict
                    resIsConflictL <- isTargetTop' depthL pL
                    resIsConflictR <- isTargetTop' depthR pR
                    let resIsConflict = case pol of
                            PJoin -> resIsConflictL || resIsConflictR
                            PMeet -> resIsConflictL || resIsConflictR

                    resIsBotL <- isTargetBot' depthL pL
                    resIsBotR <- isTargetBot' depthR pR
                    let resIsBot = case pol of
                            PMeet -> resIsBotL || resIsBotR
                            PJoin -> resIsBotL && resIsBotR

                    -- Contradiction check: Nonnull pointer to NULL.
                    botR <- isBot nodes refs depthR (psNodeR ps)
                    botL <- isBot nodes refs depthL (psNodeL ps)
                    botPL <- isTargetBot' depthL pL
                    botPR <- isTargetBot' depthR pR
                    let isNonnullContradiction = pol == PMeet &&
                            ( (nL == QNonnull' && botR)
                            || (nR == QNonnull' && botL)
                            || (nL == QNonnull' && botPL)
                            || (nR == QNonnull' && botPR) )

                    dtrace ("step RReference: isNonnullContra=" ++ show isNonnullContradiction ++ " resIsBot=" ++ show resIsBot ++ " resIsConflict=" ++ show resIsConflict) $
                       if isNonnullContradiction || resIsConflict
                       then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                       else if resIsBot then return $ Just (AnyRigidNodeF (RTerminal SBottom), refs)
                       else do
                           (mTarget, newRefs) <- stepPtrTarget env pol oneWay (psNodeL ps) (psNodeR ps) pL pR gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps) refs
                           case mTarget of
                               Just target -> return $ Just (AnyRigidNodeF (RReference (Ptr target) nRes oRes qRes), newRefs)
                               Nothing     -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                (Arr eL dL, Arr eR dR) -> do
                    botL <- isBot nodes refs depthL eL
                    botR <- isBot nodes refs depthR eR
                    let resIsBot = case pol of
                            PMeet -> botL || botR
                            PJoin -> botL && botR
                    topL <- isTop nodes refs depthL eL
                    topR <- isTop nodes refs depthR eR
                    let resIsTop = case pol of
                            PJoin -> topL || topR
                            PMeet -> topL || topR
                    if resIsBot then return $ Just (AnyRigidNodeF (RTerminal SBottom), refs)
                    else if resIsTop then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                    else if length dL /= length dR then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                    else do
                        (refs1, eStates) <- refineParams env pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps) refs [Covariant] [eL] [eR]
                        (newRefs, dStates) <- refineParams env pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps) refs1 (replicate (length dL) Covariant) dL dR
                        case eStates of
                            [eState] -> return $ Just (AnyRigidNodeF (RReference (Arr eState dStates) nRes oRes qRes), newRefs)
                            _        -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                _ -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
        _ -> return Nothing

-- | Handles object structure cases in the Product Automaton.
stepObject :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Maybe (AnyRigidNodeF TemplateId Word32) -> Maybe (AnyRigidNodeF TemplateId Word32) -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepObject env ps refs nodeL nodeR = do
    let nodes = teNodes env
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        pol = psPolarity ps
        oneWay = psOneWay ps
    case (nodeL, nodeR) of
        (Just (AnyRigidNodeF (RObject sL qL)), Just (AnyRigidNodeF (RObject sR qR))) -> do
            let qRes = Quals { qConst = case pol of
                                    PJoin -> qConst qL || qConst qR
                                    PMeet -> qConst qL && qConst qR
                             , qPhysical = case pol of
                                    PJoin -> qPhysical qL && qPhysical qR
                                    PMeet -> qPhysical qL || qPhysical qR
                             }

            case (sL, sR) of
                (VProperty _ _, VBuiltin bR) | bR /= NullPtrTy ->
                    -- Decay: Symbolic property satisfies physical requirement.
                    -- Force qPhysical to False because numeric values are copied.
                    return $ Just (AnyRigidNodeF (RObject (VBuiltin bR) qRes { qPhysical = qPhysical qR }), refs)

                (VBuiltin bL, VProperty _ _) | bL /= NullPtrTy ->
                    -- Conflict: Physical integer cannot satisfy symbolic requirement.
                    case pol of
                        PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bL) qRes { qPhysical = qPhysical qL }), refs)
                        PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                (VSingleton bt v, VProperty _ _) | bt /= NullPtrTy ->
                    -- Literal satisfies symbolic requirement (pragmatic C support).
                    case pol of
                        PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bt) qRes { qPhysical = qPhysical qL }), refs)
                        PMeet -> return $ Just (AnyRigidNodeF (RObject (VSingleton bt v) qRes { qPhysical = qPhysical qL }), refs)

                (VProperty _ _, VSingleton bt v) | bt /= NullPtrTy ->
                    case pol of
                        PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bt) qRes { qPhysical = qPhysical qR }), refs)
                        PMeet -> return $ Just (AnyRigidNodeF (RObject (VSingleton bt v) qRes { qPhysical = qPhysical qR }), refs)

                (VSizeExpr _, VBuiltin bR) | bR /= NullPtrTy ->
                    return $ Just (AnyRigidNodeF (RObject (VBuiltin bR) qRes { qPhysical = qPhysical qR }), refs)

                (VBuiltin bL, VSizeExpr _) | bL /= NullPtrTy ->
                    case pol of
                        PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bL) qRes { qPhysical = qPhysical qL }), refs)
                        PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                (VSingleton bt v, VSizeExpr _) | bt /= NullPtrTy ->
                    case pol of
                        PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bt) qRes { qPhysical = qPhysical qL }), refs)
                        PMeet -> return $ Just (AnyRigidNodeF (RObject (VSingleton bt v) qRes { qPhysical = qPhysical qL }), refs)

                (VSizeExpr _, VSingleton bt v) | bt /= NullPtrTy ->
                    case pol of
                        PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bt) qRes { qPhysical = qPhysical qR }), refs)
                        PMeet -> return $ Just (AnyRigidNodeF (RObject (VSingleton bt v) qRes { qPhysical = qPhysical qR }), refs)

                _ -> do
                    let isContradiction = (not (qConst qL) && qPhysical qL) ||
                                          (not (qConst qR) && qPhysical qR) ||
                                          (pol == PMeet && (qPhysical qL || qPhysical qR) && not (qConst qRes))

                    dtrace ("step RObject: sL=" ++ show (fmap (const ()) sL) ++ " qL=" ++ show qL ++ " sR=" ++ show (fmap (const ()) sR) ++ " qR=" ++ show qR ++ " pol=" ++ show pol ++ " isContra=" ++ show isContradiction) $
                       if isContradiction then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                       else do
                        isNullL <- isNull nodes refs depthL (psNodeL ps)
                        if isNullL then
                           case pol of
                               PJoin -> return $ Just (AnyRigidNodeF (RObject (fmap (\i -> ProductState i i pol oneWay gamma depthR depthR (psParentVar ps) (psOrigin ps) (psFile ps)) sR) qRes), refs)
                               PMeet -> return $ Just (AnyRigidNodeF (RObject (fmap (\i -> ProductState i i pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) sL) qRes), refs)
                        else do
                         isNullR <- isNull nodes refs depthR (psNodeR ps)
                         if isNullR then
                           case pol of
                               PJoin -> return $ Just (AnyRigidNodeF (RObject (fmap (\i -> ProductState i i pol oneWay gamma depthL depthL (psParentVar ps) (psOrigin ps) (psFile ps)) sL) qRes), refs)
                               PMeet -> return $ Just (AnyRigidNodeF (RObject (fmap (\i -> ProductState i i pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) sR) qRes), refs)
                         else case (sL, sR) of
                            (VVar tidL idxL, VVar tidR idxR) ->
                                -- Check alpha-equivalence via MappingContext
                                let eqTid l' r' = case (l', r') of
                                        (TIdDeBruijn iL, TIdDeBruijn iR) ->
                                            case getMapping (fromIntegral iL) gamma of
                                                Just iR' -> fromIntegral iR' == iR
                                                Nothing  -> iL == iR -- Free variable
                                        _ -> l' == r'
                                    eqIdx l' r' = case (l', r') of
                                        (Just (ILit iL), Just (ILit iR)) -> iL == iR
                                        (Just (IVar tL), Just (IVar tR)) -> eqTid tL tR
                                        (Nothing, Nothing)               -> True
                                        _                                -> False
                                in if eqTid tidL tidR
                                   then if eqIdx idxL idxR
                                        then return $ Just (AnyRigidNodeF (RObject (VVar tidL idxL) qRes), refs)
                                        else return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                                   else case (isRefinable tidL && teRefineL env, isRefinable tidR && teRefineR env) of
                                       (True, True) -> do
                                           let keyL = variableKey (teNodes env) depthL tidL
                                               keyR = variableKey (teNodes env) depthR tidR
                                           tell (Set.fromList [keyL, keyR])
                                           case (getRefinement keyL refs, getRefinement keyR refs) of
                                               (Just oldL, _) | oldL /= psNodeL ps ->
                                                   return $ Just (AnyRigidNodeF (RTerminal (STerminal $ ProductState oldL (psNodeR ps) pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps))), refs)
                                               (_, Just oldR) | oldR /= psNodeR ps ->
                                                   return $ Just (AnyRigidNodeF (RTerminal (STerminal $ ProductState (psNodeL ps) oldR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps))), refs)
                                               _ ->
                                                   -- Symmetric variable choice for commutativity and ID invariance.
                                                   let (resTid, resIdx, !newRefs) =
                                                           if stableCompareTID (teNodes env) tidL tidR == LT
                                                           then (tidL, idxL, setRefinement keyR (psNodeL ps) refs)
                                                           else (tidR, idxR, setRefinement keyL (psNodeR ps) refs)
                                                   in return $ Just (AnyRigidNodeF (RObject (VVar resTid resIdx) qRes), newRefs)
                                       (True, False) ->
                                           -- One-way inheritance: Don't unify variables.
                                           -- Only refine L if R is already concrete (handled by getEffectiveNode).
                                           -- If both are variables, we return L to satisfy the constraint for now.
                                           return $ Just (AnyRigidNodeF (RObject (VVar tidL idxL) qRes), refs)
                                       (False, True) ->
                                           return $ Just (AnyRigidNodeF (RObject (VVar tidR idxR) qRes), refs)
                                       _ -> case pol of
                                           PJoin -> return $ Just (AnyRigidNodeF (RTerminal SAny), refs)
                                           PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                            (VVar tidL idxL, _) | isRefinable tidL ->
                                Just <$> refineVarL env ps refs tidL idxL (fromJust nodeR)

                            (_, VVar tidR idxR) | isRefinable tidR ->
                                Just <$> refineVarR env ps refs tidR idxR (fromJust nodeL)

                            (VExistential tidsL bodyL, VExistential tidsR bodyR) ->
                                return $ Just $ stepObjectExistential ps refs tidsL bodyL tidsR bodyR qRes

                            (sL', VExistential tidsR bodyR) ->
                                stepObjectPackR env ps refs sL' tidsR bodyR qRes

                            (VExistential tidsL bodyL, sR') ->
                                stepObjectPackL env ps refs tidsL bodyL sR' qRes

                            (VBuiltin NullPtrTy, _) ->
                               case pol of
                                   PJoin -> let next'' i = ProductState i i pol oneWay gamma depthR depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                                            in return $ Just (AnyRigidNodeF (RObject (fmap next'' sR) qRes), refs)
                                   PMeet -> return $ Just (AnyRigidNodeF (RObject (VBuiltin NullPtrTy) qRes), refs)

                            (_, VBuiltin NullPtrTy) ->
                               case pol of
                                   PJoin -> let next'' i = ProductState i i pol oneWay gamma depthL depthL (psParentVar ps) (psOrigin ps) (psFile ps)
                                            in return $ Just (AnyRigidNodeF (RObject (fmap next'' sL) qRes), refs)
                                   PMeet -> return $ Just (AnyRigidNodeF (RObject (VBuiltin NullPtrTy) qRes), refs)

                            (VBuiltin bL, VBuiltin bR) | bL == bR ->
                                return $ Just (AnyRigidNodeF (RObject (VBuiltin bR) qRes), refs)

                            (VNominal nameL paramsL, VNominal nameR paramsR) ->
                                Just <$> stepObjectNominal env ps refs nameL paramsL nameR paramsR qRes

                            (VNominal nameL paramsL, VVariant mR) ->
                                return $ Just $ stepObjectNominalVariant env ps refs nameL paramsL mR qRes

                            (VVariant mL, VNominal nameR paramsR) ->
                                return $ Just $ stepObjectVariantNominal env ps refs mL nameR paramsR qRes

                            (VEnum nameL, VEnum nameR) | C.lexemeText nameL == C.lexemeText nameR ->
                                return $ Just (AnyRigidNodeF (RObject (VEnum nameL) qRes), refs)

                            (VSingleton bL vL, VSingleton bR vR) | bL == bR && vL == vR ->
                                return $ Just (AnyRigidNodeF (RObject (VSingleton bL vL) qRes), refs)

                            (VSingleton bL vL, VBuiltin bR) | bL == bR ->
                                case pol of
                                    PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bR) qRes), refs)
                                    PMeet -> return $ Just (AnyRigidNodeF (RObject (VSingleton bL vL) qRes), refs)

                            (VBuiltin bL, VSingleton bR vR) | bL == bR ->
                                case pol of
                                    PJoin -> return $ Just (AnyRigidNodeF (RObject (VBuiltin bL) qRes), refs)
                                    PMeet -> return $ Just (AnyRigidNodeF (RObject (VSingleton bR vR) qRes), refs)

                            (VVariant mL, VVariant mR) ->
                                return $ Just $ stepObjectVariant env ps refs mL mR qRes

                            (VProperty aL pkL, VProperty aR pkR) | pkL == pkR ->
                                let nextL' rL rR = ProductState rL rR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                                in return $ Just (AnyRigidNodeF (RObject (VProperty (nextL' aL aR) pkL) qRes), refs)

                            (VSizeExpr termsL, VSizeExpr termsR) ->
                                stepObjectSizeExpr env ps refs termsL termsR qRes

                            (VBuiltin _, _) -> dtrace "step RObject: VBuiltin catch-all L" $ case pol of
                                PJoin -> return $ Just (AnyRigidNodeF (RTerminal SAny), refs)
                                PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                            (_, VBuiltin _) -> dtrace "step RObject: VBuiltin catch-all R" $ case pol of
                                PJoin -> return $ Just (AnyRigidNodeF (RTerminal SAny), refs)
                                PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                            (VVar{}, _) -> dtrace "step RObject: VVar catch-all L" $ case pol of
                                PJoin -> return $ Just (AnyRigidNodeF (RTerminal SAny), refs)
                                PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                            (_, VVar{}) -> dtrace "step RObject: VVar catch-all R" $ case pol of
                                PJoin -> return $ Just (AnyRigidNodeF (RTerminal SAny), refs)
                                PMeet -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

                            _ -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
        _ -> return Nothing

-- | Handles general variable refinement cases in the Product Automaton.
stepVariable :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Maybe (AnyRigidNodeF TemplateId Word32) -> Maybe (AnyRigidNodeF TemplateId Word32) -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepVariable env ps refs nodeL nodeR =
    case (nodeL, nodeR) of
        -- 3. General Variable Refinement (Category-independent placeholders)
        (Just (AnyRigidNodeF (RObject (VVar tidL idxL) _)), Just nR@(AnyRigidNodeF nodeR'))
            | isRefinable tidL && not (isObject nodeR') ->
                Just <$> refineVarL env ps refs tidL idxL nR

        (Just nL@(AnyRigidNodeF nodeL'), Just (AnyRigidNodeF (RObject (VVar tidR idxR) _)))
            | isRefinable tidR && not (isObject nodeL') ->
                Just <$> refineVarR env ps refs tidR idxR nL
        _ -> return Nothing

-- | Handles terminal node cases in the Product Automaton.
stepTerminal :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Maybe (AnyRigidNodeF TemplateId Word32) -> Maybe (AnyRigidNodeF TemplateId Word32) -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepTerminal env ps refs nodeL nodeR =
    let nodes = teNodes env
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        pol = psPolarity ps
        oneWay = psOneWay ps
    in case (nodeL, nodeR) of
        -- 0. Conflict Poisoning (Absolute Absorber)
        (Just (AnyRigidNodeF (RTerminal SConflict)), _) ->
            let !newRefs = case nodeR of
                    Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && teRefineR env -> setRefinement (variableKey nodes depthR tid) (psNodeL ps) refs
                    _ -> refs
            in return $ Just (AnyRigidNodeF (RTerminal SConflict), newRefs)
        (_, Just (AnyRigidNodeF (RTerminal SConflict))) ->
            let !newRefs = case nodeL of
                    Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && teRefineL env -> setRefinement (variableKey nodes depthL tid) (psNodeR ps) refs
                    _ -> refs
            in return $ Just (AnyRigidNodeF (RTerminal SConflict), newRefs)

        -- 1. Lattice Top (SAny) Propagation
        (Just (AnyRigidNodeF (RTerminal SAny)), _) -> do
            topR <- isTop nodes refs depthR (psNodeR ps)
            if topR
            then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs) -- Poisoning
            else case pol of
                PJoin ->
                    let !newRefs = case nodeR of
                            Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && teRefineR env -> setRefinement (variableKey nodes depthR tid) (psNodeL ps) refs
                            _ -> refs
                    in return $ Just (AnyRigidNodeF (RTerminal SAny), newRefs) -- Absorber
                PMeet -> case nodeR of
                    Just (AnyRigidNodeF nR) -> return $ Just (AnyRigidNodeF (fmap (\i -> ProductState i i pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) nR), refs) -- Identity
                    Nothing -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

        (_, Just (AnyRigidNodeF (RTerminal SAny))) -> do
            topL <- isTop nodes refs depthL (psNodeL ps)
            if topL
            then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs) -- Poisoning
            else case pol of
                PJoin ->
                    let !newRefs = case nodeL of
                            Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && teRefineL env -> setRefinement (variableKey nodes depthL tid) (psNodeR ps) refs
                            _ -> refs
                    in return $ Just (AnyRigidNodeF (RTerminal SAny), newRefs) -- Absorber
                PMeet -> case nodeL of
                    Just (AnyRigidNodeF nL) -> return $ Just (AnyRigidNodeF (fmap (\i -> ProductState i i pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) nL), refs) -- Identity
                    Nothing -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

        -- 2. Lattice Bottom (SBottom) Propagation
        (Just (AnyRigidNodeF (RTerminal SBottom)), _) -> do
            topR <- isTop nodes refs depthR (psNodeR ps)
            if topR
            then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs) -- Poisoning
            else case pol of
                PJoin -> case nodeR of
                    Just (AnyRigidNodeF nR) -> return $ Just (AnyRigidNodeF (fmap (\i -> ProductState i i pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) nR), refs) -- Identity
                    Nothing -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                PMeet -> do
                    nnR <- isNonnull nodes refs depthR (psNodeR ps)
                    if nnR
                         then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs) -- Contradiction
                         else
                             let !newRefs = case nodeR of
                                     Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && teRefineR env -> setRefinement (variableKey nodes depthR tid) (psNodeL ps) refs
                                     _ -> refs
                             in return $ Just (AnyRigidNodeF (RTerminal SBottom), newRefs) -- Absorber

        (_, Just (AnyRigidNodeF (RTerminal SBottom))) -> do
            topL <- isTop nodes refs depthL (psNodeL ps)
            if topL
            then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs) -- Poisoning
            else case pol of
                PJoin -> case nodeL of
                    Just (AnyRigidNodeF nL) -> return $ Just (AnyRigidNodeF (fmap (\i -> ProductState i i pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) nL), refs) -- Identity
                    Nothing -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
                PMeet -> do
                    nnL <- isNonnull nodes refs depthL (psNodeL ps)
                    if nnL
                         then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs) -- Contradiction
                         else
                             let !newRefs = case nodeL of
                                     Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && teRefineL env -> setRefinement (variableKey nodes depthL tid) (psNodeR ps) refs
                                     _ -> refs
                             in return $ Just (AnyRigidNodeF (RTerminal SBottom), newRefs) -- Absorber

        (Just (AnyRigidNodeF (RTerminal (STerminal idL))), Just (AnyRigidNodeF (RTerminal (STerminal idR)))) ->
            return $ Just (AnyRigidNodeF (RTerminal (STerminal (ProductState idL idR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)))), refs)

        (Just (AnyRigidNodeF (RTerminal (STerminal idL))), _) ->
            case nodeR of
                Just (AnyRigidNodeF nR) -> return $ Just (AnyRigidNodeF (fmap (\rR' -> ProductState idL rR' pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) nR), refs)
                Nothing -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

        (_, Just (AnyRigidNodeF (RTerminal (STerminal idR)))) ->
            case nodeL of
                Just (AnyRigidNodeF nL) -> return $ Just (AnyRigidNodeF (fmap (\lL' -> ProductState lL' idR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)) nL), refs)
                Nothing -> return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
        _ -> return Nothing

-- | A single step of the Product Automaton.
-- Performs local pattern matching on two nodes and returns the structural product.
step :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> (StepResult, MappingRefinements, Set Int)
step env ps refs =
    let nodes = teNodes env
        depthL = psDepthL ps
        depthR = psDepthR ps

        ((effIdL, nodeL), depsL) = runWriter $ getEffectiveNode nodes refs depthL (psNodeL ps)
        ((effIdR, nodeR), depsR) = runWriter $ getEffectiveNode nodes refs depthR (psNodeR ps)

        pol = psPolarity ps

        (mRes, depsStep) = runWriter $
            stepTerminal env ps refs nodeL nodeR >>= \case
                Just r -> return (Just r)
                Nothing -> stepVariable env ps refs nodeL nodeR >>= \case
                    Just r -> return (Just r)
                    Nothing -> stepObject env ps refs nodeL nodeR >>= \case
                        Just r -> return (Just r)
                        Nothing -> stepReference env ps refs nodeL nodeR >>= \case
                            Just r -> return (Just r)
                            Nothing -> stepFunction env ps refs nodeL nodeR >>= \case
                                Just r -> return (Just r)
                                Nothing -> return Nothing

        (res, finalRefs) = fromMaybe (stepMismatch pol refs) mRes
        allDeps = Set.unions [depsL, depsR, depsStep]

    in dtrace ("step: L=" ++ show (psNodeL ps) ++ " R=" ++ show (psNodeR ps) ++ " pol=" ++ show pol ++ " effL=" ++ show effIdL ++ " effR=" ++ show effIdR ++ " parent=" ++ show (psParentVar ps)) $
       (res, finalRefs, allDeps)

-- | Sequential refinement propagation for collections of types.
refineParams :: TransitionEnv Word32 -> Polarity -> Bool -> MappingContext -> Int -> Int -> Maybe (Int, TemplateId) -> Maybe (Lexeme Text) -> Maybe FilePath -> MappingRefinements -> [Variance] -> [Word32] -> [Word32] -> Writer (Set Int) (MappingRefinements, [ProductState])
refineParams env pol oneWay gamma dL dR parentVar loc mFile initialRefs variances ls rs =
    let go refs [] [] [] acc = return (refs, reverse acc)
        go refs (v:vRest) (lL:lRest) (rR:rRest) acc = do
            let p = applyVariance v pol
                nodes = teNodes env
            (effL, nodeL) <- getEffectiveNode nodes refs dL lL
            (effR, nodeR) <- getEffectiveNode nodes refs dR rR

            -- Preview refinement for VVar
            !newRefs <-
                    case (nodeL, nodeR) of
                        (Just (AnyRigidNodeF (RObject (VVar tidL _) _)), Just (AnyRigidNodeF (RObject (VVar tidR _) _)))
                            | isRefinable tidL && teRefineL env && isRefinable tidR && teRefineR env && effL /= effR ->
                                if stableCompareTID nodes tidL tidR == LT
                                then let keyR = variableKey nodes dR tidR
                                     in return $ setRefinement keyR effL refs
                                else let keyL = variableKey nodes dL tidL
                                     in return $ setRefinement keyL effR refs
                        (Just (AnyRigidNodeF (RObject (VVar tidL _) _)), _)
                            | isRefinable tidL && teRefineL env && effL /= effR ->
                                let keyL = variableKey nodes dL tidL
                                in return $ setRefinement keyL effR refs
                        (_, Just (AnyRigidNodeF (RObject (VVar tidR _) _)))
                            | isRefinable tidR && teRefineR env && effL /= effR ->
                                let keyR = variableKey nodes dR tidR
                                in return $ setRefinement keyR effL refs
                        _ -> return refs
            let state = ProductState effL effR p oneWay gamma dL dR parentVar loc mFile
            go newRefs vRest lRest rRest (state : acc)
        go refs _ _ _ acc = return (refs, reverse acc) -- Should be unreachable due to length checks
    in go initialRefs variances ls rs []

-- | Sequential refinement for ReturnType.
refineReturnType :: TransitionEnv Word32 -> Polarity -> Bool -> MappingContext -> Int -> Int -> Maybe (Int, TemplateId) -> Maybe (Lexeme Text) -> Maybe FilePath -> MappingRefinements -> ReturnType Word32 -> ReturnType Word32 -> Writer (Set Int) (MappingRefinements, Maybe (ReturnType ProductState))
refineReturnType env pol oneWay gamma dL dR parentVar loc mFile refs rL rR =
    case (rL, rR) of
        (RetVal lL, RetVal lR) -> do
            (newRefs, states) <- refineParams env pol oneWay gamma dL dR parentVar loc mFile refs [Covariant] [lL] [lR]
            case states of
                [state] -> return (newRefs, Just $ RetVal state)
                _       -> return (newRefs, Nothing)
        (RetVoid, RetVoid) -> return (refs, Just RetVoid)
        _ -> return (refs, Nothing)

-- | Traverses PtrTarget structure in the Product Automaton.
stepPtrTarget :: TransitionEnv Word32 -> Polarity -> Bool -> Word32 -> Word32 -> PtrTarget TemplateId Word32 -> PtrTarget TemplateId Word32 -> MappingContext -> Int -> Int -> Maybe (Int, TemplateId) -> Maybe (Lexeme Text) -> Maybe FilePath -> MappingRefinements -> Writer (Set Int) (Maybe (PtrTarget TemplateId ProductState), MappingRefinements)
stepPtrTarget env pol oneWay idL idR pL pR gamma dL dR parentVar loc mFile refs =
    let next' rL rR = ProductState rL rR pol oneWay gamma dL dR parentVar loc mFile
    in case (pL, pR) of
        (TargetObject oL, TargetObject oR) -> do
            -- Dereferencing a pointer to Bottom is a contradiction (Section 1.B)
            let nodes = teNodes env
            botL <- isBot nodes refs dL oL
            botR <- isBot nodes refs dR oR
            if pol == PMeet && (botL || botR)
            then return (Nothing, refs)
            else do
                (newRefs, states) <- refineParams env pol oneWay gamma dL dR parentVar loc mFile refs [Covariant] [oL] [oR]
                case states of
                    [state] -> return (Just $ TargetObject state, newRefs)
                    _       -> return (Nothing, refs)
        (TargetFunction aL rL, TargetFunction aR rR) ->
            if length aL /= length aR
            then return (Nothing, refs)
            else do
                (refs1, aStates) <- refineParams env pol oneWay gamma dL dR parentVar loc mFile refs (replicate (length aL) Contravariant) aL aR
                (newRefs, mRet) <- refineReturnType env pol oneWay gamma dL dR parentVar loc mFile refs1 rL rR
                case mRet of
                    Just ret -> return (Just $ TargetFunction aStates ret, newRefs)
                    Nothing  -> return (Nothing, refs)
        (TargetOpaque tidL, TargetOpaque tidR) | isRefinable tidL && isRefinable tidR ->
            if tidL == tidR then return (Just $ TargetOpaque tidL, refs)
            else
                -- Symmetric variable choice for commutativity and ID invariance.
                let keyL = variableKey (teNodes env) dL tidL
                    keyR = variableKey (teNodes env) dR tidR
                in case (teRefineL env, teRefineR env) of
                    (True, True) -> do
                        tell (Set.fromList [keyL, keyR])
                        let (chosen, !newRefs) = if stableCompareTID (teNodes env) tidL tidR == LT
                                             then (tidL, setRefinement keyR idL refs)
                                             else (tidR, setRefinement keyL idR refs)
                        return (Just $ TargetOpaque chosen, newRefs)
                    (True, False) -> do
                        tell (Set.singleton keyL)
                        let !newRefs = setRefinement keyL idR refs
                        return (Just $ TargetOpaque tidR, newRefs)
                    (False, True) -> do
                        tell (Set.singleton keyR)
                        let !newRefs = setRefinement keyR idL refs
                        return (Just $ TargetOpaque tidL, newRefs)
                    (False, False) ->
                        return (Just $ TargetOpaque tidL, refs) -- Cannot refine, but they are both refinable names

        (TargetOpaque tL, TargetOpaque tR) | tL == tR ->
            return (Just $ TargetOpaque tL, refs)

        (TargetOpaque tidL, TargetObject oR) | isRefinable tidL && teRefineL env -> do
            let key = variableKey (teNodes env) dL tidL
            tell (Set.singleton key)
            case getRefinement key refs of
                Nothing ->
                    let !newRefs = setRefinement key oR refs
                    in return (Just $ TargetObject (next' oR oR), newRefs)
                Just oldID ->
                    return (Just $ TargetObject (next' oldID oR), refs)

        (TargetObject oL, TargetOpaque tidR) | isRefinable tidR && teRefineR env -> do
            let key = variableKey (teNodes env) dR tidR
            tell (Set.singleton key)
            case getRefinement key refs of
                Nothing ->
                    let !newRefs = setRefinement key oL refs
                    in return (Just $ TargetObject (next' oL oL), newRefs)
                Just oldID ->
                    return (Just $ TargetObject (next' oL oldID), refs)

        (TargetOpaque tidL, TargetFunction aR rR) | isRefinable tidL && teRefineL env ->
            -- Refine void* to a function signature
            let nextR rL' rR' = ProductState rL' rR' pol oneWay gamma dR dR parentVar loc mFile
            in return (Just $ TargetFunction (map (\r -> nextR r r) aR) (fmap (\r -> nextR r r) rR), refs)

        (TargetFunction aL rL, TargetOpaque tidR) | isRefinable tidR && teRefineR env ->
            let nextL rL' rR' = ProductState rL' rR' pol oneWay gamma dL dL parentVar loc mFile
            in return (Just $ TargetFunction (map (\r -> nextL r r) aL) (fmap (\r -> nextL r r) rL), refs)

        _ -> return (Nothing, refs)

setQuals :: Quals -> AnyRigidNodeF tid a -> AnyRigidNodeF tid a
setQuals q (AnyRigidNodeF node) = case node of
    RObject s _        -> AnyRigidNodeF (RObject s q)
    RReference s n o _ -> AnyRigidNodeF (RReference s n o q)
    RFunction args ret -> AnyRigidNodeF (RFunction args ret)
    RTerminal t        -> AnyRigidNodeF (RTerminal t)

refineVarL :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> TemplateId -> Maybe (Index TemplateId) -> AnyRigidNodeF TemplateId Word32 -> Writer (Set Int) (StepResult, MappingRefinements)
refineVarL env ps refs tidL idxL nodeR = do
    let nodes = teNodes env
        depthL = psDepthL ps
        depthR = psDepthR ps
        gamma = psGamma ps
        pol = psPolarity ps
        oneWay = psOneWay ps
        key = variableKey nodes depthL tidL
        qL = getQuals (fromMaybe (AnyRigidNodeF (RTerminal SConflict)) $ Map.lookup (psNodeL ps) nodes)
        qR = getQuals nodeR
        qRes = Quals { qConst = if pol == PJoin then qConst qL || qConst qR else qConst qL && qConst qR
                         , qPhysical = if pol == PJoin then qPhysical qL || qPhysical qR else qPhysical qL && qPhysical qR
                         }
    tell (Set.singleton key)
    case getRefinement key refs of
        Nothing | psNodeL ps /= psNodeR ps ->
            let resNode = fmap (\i -> ProductState i i pol oneWay gamma depthR depthR (Just (depthL, tidL)) (psOrigin ps) (psFile ps)) nodeR
                res = if isObjectAny nodeR then setQuals qRes resNode else resNode
            in if teRefineL env
               then return (res, setRefinement key (psNodeR ps) refs)
               else return (res, refs)
        Just oldID | oldID /= psNodeL ps ->
            return (AnyRigidNodeF (RTerminal (STerminal $ ProductState oldID (psNodeR ps) pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps))), refs)
        _ -> if pol == PJoin
             then return (AnyRigidNodeF (RObject (VVar tidL idxL) qRes), refs)
             else let resNode = fmap (\i -> ProductState i i pol oneWay gamma depthR depthR (Just (depthL, tidL)) (psOrigin ps) (psFile ps)) nodeR
                  in return (if isObjectAny nodeR then setQuals qRes resNode else resNode, refs)

refineVarR :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> TemplateId -> Maybe (Index TemplateId) -> AnyRigidNodeF TemplateId Word32 -> Writer (Set Int) (StepResult, MappingRefinements)
refineVarR env ps refs tidR idxR nodeL = do
    let nodes = teNodes env
        depthL = psDepthL ps
        depthR = psDepthR ps
        gamma = psGamma ps
        pol = psPolarity ps
        oneWay = psOneWay ps
        key = variableKey nodes depthR tidR
        qR = getQuals (fromMaybe (AnyRigidNodeF (RTerminal SConflict)) $ Map.lookup (psNodeR ps) nodes)
        qL = getQuals nodeL
        qRes = Quals { qConst = if pol == PJoin then qConst qL || qConst qR else qConst qL && qConst qR
                         , qPhysical = if pol == PJoin then qPhysical qL || qPhysical qR else qPhysical qL && qPhysical qR
                         }
    tell (Set.singleton key)
    case getRefinement key refs of
        Nothing | psNodeL ps /= psNodeR ps ->
            let resNode = fmap (\i -> ProductState i i pol oneWay gamma depthL depthL (Just (depthR, tidR)) (psOrigin ps) (psFile ps)) nodeL
                res = if isObjectAny nodeL then setQuals qRes resNode else resNode
            in if teRefineR env
               then return (res, setRefinement key (psNodeL ps) refs)
               else return (res, refs)
        Just oldID | oldID /= psNodeR ps ->
            return (AnyRigidNodeF (RTerminal (STerminal $ ProductState (psNodeL ps) oldID pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps))), refs)
        _ -> if pol == PJoin
             then return (AnyRigidNodeF (RObject (VVar tidR idxR) qRes), refs)
             else let resNode = fmap (\i -> ProductState i i pol oneWay gamma depthL depthL (Just (depthR, tidR)) (psOrigin ps) (psFile ps)) nodeL
                  in return (if isObjectAny nodeL then setQuals qRes resNode else resNode, refs)

isObjectAny :: AnyRigidNodeF tid a -> Bool
isObjectAny (AnyRigidNodeF n) = isObject n

-- | Identifies variables that are bound by an existential quantifier.
isBound :: TemplateId -> Bool
isBound TIdDeBruijn{} = True
isBound _             = False

-- | Identifies variables that are part of a type's template parameters.
-- These are used during instantiation to create fresh local placeholders.
isParameter :: TemplateId -> Bool
isParameter TIdParam{}   = True
isParameter TIdSkolem{}  = True
isParameter TIdInstance{} = True
isParameter TIdDeBruijn{} = False
isParameter (TIdName t)   = t == "T" || (T.length t >= 2 && T.head t == 'T' && T.all Char.isDigit (T.drop 1 t))

-- | Identifies variables that represent opaque Skolem or Instance placeholders.
isRefinable :: TemplateId -> Bool
isRefinable = \case
    TIdParam{}           -> True
    TIdSkolem{}          -> True
    TIdInstance{}         -> True
    TIdDeBruijn{}         -> False
    TIdName t             -> t == "T" || (T.length t >= 2 && T.head t == 'T' && T.all Char.isDigit (T.drop 1 t))


-- | Searches for an existing existential node that wraps a given nominal type name and arity.
findExistentialPromotion :: TransitionEnv Word32 -> Lexeme TemplateId -> Int -> Maybe (AnyRigidNodeF TemplateId Word32, Word32)
findExistentialPromotion env lexName arity =
    let isMatch nid (AnyRigidNodeF (RObject (VExistential tids bodyId) _)) =
            length tids == arity &&
            case Map.lookup bodyId (teNodes env) of
                Just (AnyRigidNodeF (RObject (VNominal n ps) _)) ->
                    let L _ _ valN = n
                        L _ _ valLex = lexName
                        res = valN == valLex && length ps == arity
                    in dtrace ("findExistentialPromotion: checking " ++ show nid ++ " nominal name=" ++ show valN ++ " match=" ++ show res) res
                _ -> False
        isMatch _ _ = False
        matches = filter (uncurry isMatch) (Map.toList (teNodes env))
    in dtrace ("findExistentialPromotion: searching for " ++ show (C.lexemeText lexName) ++ " arity=" ++ show arity ++ " in " ++ show (Map.size (teNodes env)) ++ " nodes") $
       case matches of
        [] -> Nothing
        _  -> let (i, n) = List.minimumBy (\(i1, _) (i2, _) -> compare (getStableNodeIdent (teNodes env) i1) (getStableNodeIdent (teNodes env) i2)) matches
              in Just (n, i)

-- | Computes a stable unique key for a refinable variable in 'MappingRefinements'.
-- Absolute level is used for De Bruijn variables to ensure stability.
-- Hashed semantic identifiers are used for others.
variableKey :: Map Word32 (AnyRigidNodeF TemplateId Word32) -> Int -> TemplateId -> Int
variableKey nodes currentDepth = \case
    TIdDeBruijn i   -> currentDepth - fromIntegral i
    TIdSkolem l r i -> fromIntegral (hash (0 :: Int, i, getStableNodeIdent nodes l, getStableNodeIdent nodes r))
    TIdInstance i   -> fromIntegral (hash (1 :: Int, i))
    TIdParam p i _  -> fromIntegral (hash (2 :: Int, p, i))
    TIdName t       -> fromIntegral (hash (3 :: Int, currentDepth, t))

templateIdName :: TemplateId -> Text
templateIdName (TIdName t) = t
templateIdName _           = ""

stepObjectExistential :: ProductState -> MappingRefinements -> [TemplateId] -> Word32 -> [TemplateId] -> Word32 -> Quals -> (StepResult, MappingRefinements)
stepObjectExistential ps refs tidsL bodyL tidsR bodyR qRes =
    if length tidsL /= length tidsR then (AnyRigidNodeF (RTerminal SConflict), refs)
    else
        -- Synchronize binders by pushing them into the mapping context.
        let gamma = psGamma ps
            depthL = psDepthL ps
            depthR = psDepthR ps
            pol = psPolarity ps
            oneWay = psOneWay ps
            newGamma = foldr pushMapping gamma [0..length tidsL - 1]
            newDL = min 30 (depthL + length tidsL)
            newDR = min 30 (depthR + length tidsR)
            next rL rR = ProductState rL rR pol oneWay newGamma newDL newDR (psParentVar ps) (psOrigin ps) (psFile ps)
        in (AnyRigidNodeF (RObject (VExistential tidsL (next bodyL bodyR)) qRes), refs)

stepObjectPackR :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> ObjectStructure TemplateId Word32 -> [TemplateId] -> Word32 -> Quals -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepObjectPackR env ps refs sL' tidsR bodyR qRes = do
    let nodes = teNodes env
        depthL = psDepthL ps
        depthR = psDepthR ps
        gamma = psGamma ps
        pol = psPolarity ps
        oneWay = psOneWay ps
    (effIdL, _) <- getEffectiveNode nodes refs depthL (psNodeL ps)
    mBodyR <- getEffectiveObject nodes refs (depthR + length tidsR) bodyR
    let checkCompatible = case (sL', mBodyR) of
            (VVar tid _, _) | (isRefinable tid || isBound tid) && teRefineL env -> True
            (_, Just (VVar tid _)) | (isRefinable tid || isBound tid) && teRefineR env -> True
            (VBuiltin b1, Just (VBuiltin b2)) -> b1 == b2
            (VNominal n1 p1, Just (VNominal n2 p2)) -> C.lexemeText n1 == C.lexemeText n2 && length p1 == length p2
            (VEnum n1, Just (VEnum n2)) -> C.lexemeText n1 == C.lexemeText n2
            (VSingleton b1 _, Just (VBuiltin b2)) -> b1 == b2
            (VBuiltin b1, Just (VSingleton b2 _)) -> b1 == b2
            (VSingleton b1 v1, Just (VSingleton b2 v2)) -> b1 == b2 && v1 == v2
            _ -> False
    if not checkCompatible then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
       else
        let newGamma = foldr pushMapping gamma [0..length tidsR - 1]
            newDR = min 30 (depthR + length tidsR)
        in case pol of
            PJoin ->
                -- Generalization: result is the Existential
                let next rL rR = ProductState rL rR PJoin oneWay newGamma depthL newDR (psParentVar ps) (psOrigin ps) (psFile ps)
                in return $ Just (AnyRigidNodeF (RObject (VExistential tidsR (next effIdL bodyR)) qRes), refs)
            PMeet ->
                -- Refinement: result is the Concrete structure
                let next rL rR = ProductState rL rR PMeet oneWay newGamma depthL newDR (psParentVar ps) (psOrigin ps) (psFile ps)
                in return $ Just (AnyRigidNodeF (RObject (fmap (\idL' -> next idL' bodyR) sL') qRes), refs)

stepObjectPackL :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> [TemplateId] -> Word32 -> ObjectStructure TemplateId Word32 -> Quals -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepObjectPackL env ps refs tidsL bodyL sR' qRes = do
    let nodes = teNodes env
        depthL = psDepthL ps
        depthR = psDepthR ps
        gamma = psGamma ps
        pol = psPolarity ps
        oneWay = psOneWay ps
    (effIdR, _) <- getEffectiveNode nodes refs depthR (psNodeR ps)
    mBodyL <- getEffectiveObject nodes refs (depthL + length tidsL) bodyL
    let checkCompatible = case (mBodyL, sR') of
            (Just (VVar tid _), _) | (isRefinable tid || isBound tid) && teRefineL env -> True
            (_, VVar tid _) | (isRefinable tid || isBound tid) && teRefineR env -> True
            (Just (VBuiltin b1), VBuiltin b2) -> b1 == b2
            (Just (VNominal n1 p1), VNominal n2 p2) -> C.lexemeText n1 == C.lexemeText n2 && length p1 == length p2
            (Just (VEnum n1), VEnum n2) -> C.lexemeText n1 == C.lexemeText n2
            (Just (VSingleton b1 _), VBuiltin b2) -> b1 == b2
            (Just (VBuiltin b1), VSingleton b2 _) -> b1 == b2
            (Just (VSingleton b1 v1), VSingleton b2 v2) -> b1 == b2 && v1 == v2
            _ -> False
    if not checkCompatible then return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)
       else
        let newGamma = foldr pushMapping gamma [0..length tidsL - 1]
            newDL = min 30 (depthL + length tidsL)
        in case pol of
            PJoin ->
                let next rL rR = ProductState rL rR PJoin oneWay newGamma newDL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                in return $ Just (AnyRigidNodeF (RObject (VExistential tidsL (next bodyL effIdR)) qRes), refs)
            PMeet ->
                let next rL rR = ProductState rL rR PMeet oneWay newGamma newDL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                in return $ Just (AnyRigidNodeF (RObject (fmap (bodyL `next`) sR') qRes), refs)

stepObjectNominal :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Lexeme TemplateId -> [Word32] -> Lexeme TemplateId -> [Word32] -> Quals -> Writer (Set Int) (StepResult, MappingRefinements)
stepObjectNominal env ps refs nameL paramsL nameR paramsR qRes = do
    let pol = psPolarity ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        gamma = psGamma ps
        oneWay = psOneWay ps
    if C.lexemeText nameL /= C.lexemeText nameR || length paramsL /= length paramsR
    then return (AnyRigidNodeF (RTerminal SConflict), refs)
    else do
        -- 1. Existential Promotion for heterogeneous collections (Section 4.A).
        effParamsL <- mapM (getEffectiveNode (teNodes env) refs depthL) paramsL
        effParamsR <- mapM (getEffectiveNode (teNodes env) refs depthR) paramsR
        let effIdsL = map fst effParamsL
            effIdsR = map fst effParamsR

            (newRefs', mPromoted) = if pol == PJoin && effIdsL /= effIdsR then
                dtrace ("VNominal Join PROMOTING: name=" ++ show (C.lexemeText nameL) ++ " effIdsL=" ++ show effIdsL ++ " effIdsR=" ++ show effIdsR) $
                case findExistentialPromotion env nameL (length paramsL) of
                    Just (AnyRigidNodeF (RObject (VExistential tids bodyId) _), existId) ->
                        let newGamma = foldr pushMapping gamma [0..length tids - 1]
                            next'' rL rR = ProductState rL rR PJoin oneWay newGamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)

                            -- Update variable refinement if we found a supertype
                            !r' = case Map.lookup (psNodeR ps) (teNodes env) of
                                Just (AnyRigidNodeF (RObject (VVar tidR _) _)) | isRefinable tidR && teRefineR env ->
                                    dtrace ("Promotion Refinement Update R: " ++ show tidR ++ " -> " ++ show existId) $
                                    setRefinement (variableKey (teNodes env) depthR tidR) existId refs
                                _ -> case Map.lookup (psNodeL ps) (teNodes env) of
                                    Just (AnyRigidNodeF (RObject (VVar tidL _) _)) | isRefinable tidL && teRefineL env ->
                                        dtrace ("Promotion Refinement Update L: " ++ show tidL ++ " -> " ++ show existId) $
                                        setRefinement (variableKey (teNodes env) depthL tidL) existId refs
                                    _ -> refs
                        in (r', Just $ AnyRigidNodeF (RObject (VExistential tids (next'' (psNodeL ps) bodyId)) qRes))
                    _ -> (refs, Nothing)
                else (refs, Nothing)

        case mPromoted of
            Just promoted -> return (promoted, newRefs')
            Nothing -> do
                let variances = case Map.lookup (templateIdName (C.lexemeText nameL)) (regDefinitions (teRegistry env)) of
                        Just (StructDef _ ps' _) -> map snd ps'
                        Just (UnionDef _ ps' _)  -> map snd ps'
                        _ -> replicate (length paramsL) Covariant
                (newRefsParams, states) <- refineParams env pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps) refs variances paramsL paramsR

                -- Apply PathContext refinement for Unions during PMeet.
                let mRefined :: Maybe StepResult
                    mRefined = if pol == PMeet then
                        case Map.lookup (teCurrentPath env) (pcRefinements (tePathCtx env)) of
                            Just (EqVariant idx) ->
                                case Map.lookup (templateIdName (C.lexemeText nameL)) (regDefinitions (teRegistry env)) of
                                    Just (UnionDef _ _ members) | fromIntegral idx < length members ->
                                        let mId = mType (members !! fromIntegral idx)
                                            next'' rL rR = ProductState rL rR PMeet oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                                        in Just $ AnyRigidNodeF (RObject (VVariant (IntMap.singleton (fromIntegral idx) (next'' mId mId))) qRes)
                                    _ -> Nothing
                            _ -> Nothing
                        else Nothing
                return (fromMaybe (AnyRigidNodeF (RObject (VNominal nameL states) qRes)) mRefined, newRefsParams)

stepObjectNominalVariant :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> Lexeme TemplateId -> [Word32] -> IntMap Word32 -> Quals -> (StepResult, MappingRefinements)
stepObjectNominalVariant env ps refs nameL paramsL mR qRes =
    let pol = psPolarity ps
        oneWay = psOneWay ps
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
    in case Map.lookup (templateIdName (C.lexemeText nameL)) (regDefinitions (teRegistry env)) of
        Just (UnionDef _ _ members) ->
            let check = all (\rIdx -> rIdx >= 0 && rIdx < length members) (IntMap.keys mR)
            in if check
               then case pol of
                   PMeet ->
                       let nextState rIdx mIdR =
                               let mIdL = mType (members !! rIdx)
                               in ProductState mIdL mIdR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                       in (AnyRigidNodeF (RObject (VVariant (IntMap.mapWithKey nextState mR)) qRes), refs)
                   PJoin -> (AnyRigidNodeF (RObject (VNominal nameL (map (\r -> ProductState r r pol oneWay gamma depthL depthL (psParentVar ps) (psOrigin ps) (psFile ps)) paramsL)) qRes), refs)
               else (AnyRigidNodeF (RTerminal SConflict), refs)
        _ -> (AnyRigidNodeF (RTerminal SConflict), refs)

stepObjectVariantNominal :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> IntMap Word32 -> Lexeme TemplateId -> [Word32] -> Quals -> (StepResult, MappingRefinements)
stepObjectVariantNominal env ps refs mL nameR paramsR qRes =
    let pol = psPolarity ps
        oneWay = psOneWay ps
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
    in case Map.lookup (templateIdName (C.lexemeText nameR)) (regDefinitions (teRegistry env)) of
        Just (UnionDef _ _ members) ->
            let check = all (\rIdx -> rIdx >= 0 && rIdx < length members) (IntMap.keys mL)
            in if check
               then case pol of
                   PMeet ->
                       let nextState rIdx mIdL =
                               let mIdR = mType (members !! rIdx)
                               in ProductState mIdL mIdR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                       in (AnyRigidNodeF (RObject (VVariant (IntMap.mapWithKey nextState mL)) qRes), refs)
                   PJoin -> (AnyRigidNodeF (RObject (VNominal nameR (map (\r -> ProductState r r pol oneWay gamma depthR depthR (psParentVar ps) (psOrigin ps) (psFile ps)) paramsR)) qRes), refs)
               else (AnyRigidNodeF (RTerminal SConflict), refs)
        _ -> (AnyRigidNodeF (RTerminal SConflict), refs)

stepObjectVariant :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> IntMap Word32 -> IntMap Word32 -> Quals -> (StepResult, MappingRefinements)
stepObjectVariant env ps refs mL mR qRes =
    let pol = psPolarity ps
        oneWay = psOneWay ps
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        bot = let (b, _, _, _) = teTerminals env in b
        nextL rL rR = ProductState rL rR pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps)
        mRes = case pol of
            PJoin ->
                let nextJL l' = ProductState l' bot PJoin oneWay gamma depthL 0 (psParentVar ps) (psOrigin ps) (psFile ps)
                    nextJR r' = ProductState bot r' PJoin oneWay gamma 0 depthR (psParentVar ps) (psOrigin ps) (psFile ps)
                in IntMap.merge (IntMap.mapMissing (\_ l' -> nextJL l'))
                                (IntMap.mapMissing (\_ r' -> nextJR r'))
                                (IntMap.zipWithMatched (\_ l' r' -> nextL l' r'))
                                mL mR
            PMeet ->
                IntMap.merge IntMap.dropMissing
                             IntMap.dropMissing
                             (IntMap.zipWithMatched (\_ l' r' -> nextL l' r'))
                             mL mR
        in if pol == PMeet && IntMap.null mRes && not (IntMap.null mL || IntMap.null mR)
           then (AnyRigidNodeF (RTerminal SConflict), refs)
           else (AnyRigidNodeF (RObject (VVariant mRes) qRes), refs)

stepObjectSizeExpr :: TransitionEnv Word32 -> ProductState -> MappingRefinements -> [(Word32, Integer)] -> [(Word32, Integer)] -> Quals -> Writer (Set Int) (Maybe (StepResult, MappingRefinements))
stepObjectSizeExpr env ps refs termsL termsR qRes = do
    let pol = psPolarity ps
        oneWay = psOneWay ps
        gamma = psGamma ps
        depthL = psDepthL ps
        depthR = psDepthR ps
        nodes = teNodes env
        getPropIdent :: Word32 -> Writer (Set Int) (PropertyKind, Int)
        getPropIdent rId = do
            (effRId, mRNode) <- getEffectiveNode nodes refs (max depthL depthR) rId
            case mRNode of
                Just (AnyRigidNodeF (RObject (VProperty a pk) _)) -> do
                    (effA, mANode) <- getEffectiveNode nodes refs (max depthL depthR) a
                    let targetIdent :: Int
                        targetIdent = case mANode of
                            Just (AnyRigidNodeF (RObject s _)) ->
                                case s of
                                    VNominal l _ -> hash (C.lexemeText l)
                                    VBuiltin bt  -> hash bt
                                    VVar tid _   -> hashTemplateId nodes tid
                                    VEnum l      -> hash (C.lexemeText l)
                                    _            -> fromIntegral effA
                            _ -> fromIntegral effA
                    return (pk, targetIdent)
                _ -> return (PSize, fromIntegral effRId)

    tsLRaw <- mapM (\(idL', c) -> (,c) <$> getPropIdent idL') termsL
    tsRRaw <- mapM (\(idR', c) -> (,c) <$> getPropIdent idR') termsR

    -- Semantic property identifier -> (Original ID, Coefficient)
    let mapL = Map.fromList [ (pIdent, (idL', c)) | ((idL', c), (pIdent, _)) <- zip termsL tsLRaw ]
        mapR = Map.fromList [ (pIdent, (idR', c)) | ((idR', c), (pIdent, _)) <- zip termsR tsRRaw ]

    let tsL_agg = Map.fromListWith (+) tsLRaw
        tsR_agg = Map.fromListWith (+) tsRRaw

    if tsL_agg == tsR_agg
       then -- Expressions are semantically identical.
            -- Reconstruct by pairing original IDs that refer to the same properties.
            let finalTerms = [ (ProductState idL' idR' pol oneWay gamma depthL depthR (psParentVar ps) (psOrigin ps) (psFile ps), c)
                             | (pIdent, c) <- Map.toList tsL_agg
                             , let (idL', _) = mapL Map.! pIdent
                             , let (idR', _) = mapR Map.! pIdent
                             ]
            in return $ Just (AnyRigidNodeF (RObject (VSizeExpr finalTerms) qRes), refs)
       else return $ Just (AnyRigidNodeF (RTerminal SConflict), refs)

-- end of file
