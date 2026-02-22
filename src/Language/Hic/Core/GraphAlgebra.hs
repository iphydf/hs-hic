{-# LANGUAGE FlexibleContexts     #-}
{-# LANGUAGE RankNTypes           #-}
{-# LANGUAGE ScopedTypeVariables  #-}
{-# LANGUAGE StandaloneDeriving   #-}
{-# LANGUAGE UndecidableInstances #-}

module Language.Hic.Core.GraphAlgebra
    ( Graph (..)
    , NodeId
    , universalProduct
    , minimize
    , merge
    , prune
    ) where

import           Control.Monad.State.Strict (execState, modify)
import           Data.IntMap.Strict         (IntMap)
import qualified Data.IntMap.Strict         as IntMap
import           Data.IntSet                (IntSet)
import qualified Data.IntSet                as IntSet
import           Data.List                  (foldl')
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.Maybe                 (fromMaybe)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import qualified Debug.Trace                as Debug

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

-- | A generic structural graph (automaton).
-- Nodes are indexed by NodeId and contain a value of type 'f NodeId'.
-- Negative NodeIds are reserved for terminal/virtual nodes.
data Graph f = Graph
    { gNodes :: IntMap (f NodeId)
    , gRoot  :: NodeId
    }

deriving instance Show (f NodeId) => Show (Graph f)
deriving instance Eq (f NodeId) => Eq (Graph f)
deriving instance Ord (f NodeId) => Ord (Graph f)

type NodeId = Int

-- | Computes the Product Automaton of two graphs over a finite auxiliary state space 's'.
-- This algorithm uses reachability-based construction (Worklist) to avoid
-- generating unreachable states. It is provably terminating and total.
universalProduct :: forall f s. (Traversable f, Ord s, Show s, Ord (f ()), Ord (f NodeId))
                 => (NodeId -> NodeId -> s -> f (NodeId, NodeId, s))
                 -- ^ Pure, non-recursive transition function
                 -> IntMap (f NodeId) -- ^ Structure of terminal nodes
                 -> [NodeId]          -- ^ Opaque terminal NodeIds (atomic)
                 -> [s]               -- ^ (Unused in reachability version) Finite auxiliary state space
                 -> Graph f           -- ^ Input Graph 1
                 -> Graph f           -- ^ Input Graph 2
                 -> s                 -- ^ Initial auxiliary state
                 -> Graph f
universalProduct combine structuredTerminals atomicTerminals _allStates g1 g2 startState =
    let terminals = atomicTerminals ++ IntMap.keys structuredTerminals
        startTriple = (gRoot g1, gRoot g2, startState)
        (nodes, stateToId) = buildReachability terminals startTriple
        rootId = fromMaybe (error "GA: root not found") $ Map.lookup startTriple stateToId
    in prune $ minimize structuredTerminals atomicTerminals $ Graph nodes rootId
  where
    buildReachability _terminals start =
        let go seen worklist accMap idAcc
                | Set.null worklist = (idAcc, accMap)
                | otherwise =
                    let (triple@(i, j, s), rest) = Set.deleteFindMin worklist
                        msg = "GA.buildReachability: triple=" ++ show triple ++ " worklist_size=" ++ show (Set.size worklist)
                    in dtrace msg $
                    let sId = fromMaybe (error "GA: internal worklist error") $ Map.lookup triple accMap
                        nodeF = combine i j s
                        -- Determine child triples
                        childTriples = execState (traverse (\t -> modify (t:)) nodeF) []
                        -- Update state mapping for new children
                        (accMap', idAcc', newWork) = foldl' (register seen) (accMap, idAcc, Set.empty) childTriples
                        -- Set child IDs in node structure
                        nodeF' = fmap (\t -> fromMaybe (error "GA: lookup failure") (Map.lookup t accMap')) nodeF
                        idAcc'' = IntMap.insert sId nodeF' idAcc'
                    in go (Set.insert triple seen) (Set.union rest newWork) accMap' idAcc''

            register seen (m, iAcc, nw) triple
                | triple `Map.member` m = (m, iAcc, nw)
                | otherwise =
                    let newId = Map.size m
                        m' = Map.insert triple newId m
                    in (m', iAcc, if Set.member triple seen then nw else Set.insert triple nw)

            (initialMap, _, _) = register Set.empty (Map.empty, IntMap.empty, Set.empty) start
        in go Set.empty (Set.singleton start) initialMap IntMap.empty

-- | Minimizes a structural graph using Moore's Algorithm (Partition Refinement).
-- This algorithm is strictly reductive on the partition of a finite set of nodes.
minimize :: forall f. (Traversable f, Ord (f ()), Ord (f NodeId))
         => IntMap (f NodeId) -- ^ Structure of terminal nodes to allow merging
         -> [NodeId]          -- ^ Opaque terminal NodeIds (atomic)
         -> Graph f -> Graph f
minimize structuredTerminals atomicTerminals (Graph nodes root) =
    let terminals = IntSet.fromList (atomicTerminals ++ IntMap.keys structuredTerminals)
        (classMap, groupsByClass) = findPartition structuredTerminals atomicTerminals nodes
        (lookupFinal, realGroups) = buildRemapping terminals classMap groupsByClass

        allNodes = nodes `IntMap.union` structuredTerminals
        newNodes = IntMap.fromList
            [ (newIdx, fmap lookupFinal (getNode allNodes (head group)))
            | (newIdx, group) <- zip [0..] realGroups ]
        newRoot = lookupFinal root
    in Graph newNodes newRoot

-- | Merges two graphs into one, ensuring semantically identical nodes are shared.
merge :: forall f. (Traversable f, Ord (f ()), Ord (f NodeId))
      => IntMap (f NodeId) -- ^ Structure of terminal nodes
      -> [NodeId]          -- ^ Opaque terminal NodeIds (atomic)
      -> Graph f -> Graph f -> (Graph f, NodeId, NodeId)
merge structuredTerminals atomicTerminals g1 g2 =
    let terminals = IntSet.fromList (atomicTerminals ++ IntMap.keys structuredTerminals)
        nodes1 = gNodes g1
        nodes2 = gNodes g2
        offset = (case IntMap.maxViewWithKey nodes1 of { Just ((k, _), _) -> k; Nothing -> 0 }) + 1
        shift i | IntSet.member i terminals = i
                | otherwise                 = i + offset
        nodes2' = IntMap.fromList [ (shift k, fmap shift n) | (k, n) <- IntMap.toList nodes2 ]

        mergedNodes = IntMap.union nodes1 nodes2'
        (classMap, groupsByClass) = findPartition structuredTerminals atomicTerminals mergedNodes
        (lookupFinal, realGroups) = buildRemapping terminals classMap groupsByClass

        allNodes = mergedNodes `IntMap.union` structuredTerminals
        newNodes = IntMap.fromList
            [ (newIdx, fmap lookupFinal (getNode allNodes (head group)))
            | (newIdx, group) <- zip [0..] realGroups ]
        newRoot1 = lookupFinal (gRoot g1)
        newRoot2 = lookupFinal (shift (gRoot g2))
    in (Graph newNodes newRoot1, newRoot1, newRoot2)

-- | Standard reachability pruning.
prune :: forall f. (Traversable f) => Graph f -> Graph f
prune (Graph nodes root) =
    let reachableIds = foldl' expand (Set.singleton root) [1 .. IntMap.size nodes]
        expand seen _ = Set.union seen (Set.fromList $ concatMap (getChildren nodes) (Set.toList seen))
        newNodes = IntMap.filterWithKey (\k _ -> Set.member k reachableIds) nodes
    in Graph newNodes root

--------------------------------------------------------------------------------
-- Internal Helpers
--------------------------------------------------------------------------------

findPartition :: forall f. (Traversable f, Ord (f ()), Ord (f NodeId))
              => IntMap (f NodeId) -> [NodeId] -> IntMap (f NodeId) -> (IntMap Int, Map Int [NodeId])
findPartition structuredTerminals atomicTerminals nodes =
    let allNodes = nodes `IntMap.union` structuredTerminals
        terminals = IntSet.fromList (atomicTerminals ++ IntMap.keys structuredTerminals)
        initialPartition = [ [t] | t <- atomicTerminals ] ++
            (Map.elems $ Map.fromListWith (++) $
                [ (fmap (const ()) node, [i]) | (i, node) <- IntMap.toList allNodes ])
        (classMap0, groups0) = buildClassMapAndGroups terminals initialPartition
    in refine allNodes terminals classMap0 groups0

refine :: forall f. (Traversable f, Ord (f NodeId))
       => IntMap (f NodeId) -> IntSet -> IntMap Int -> Map Int [NodeId] -> (IntMap Int, Map Int [NodeId])
refine allNodes terminals classMap groupsByClass =
    let numGroups = Map.size groupsByClass
        msg = "GA.refine: partition_size=" ++ show numGroups
    in dtrace msg $
    let groups = Map.elems groupsByClass
        newGroups = concatMap (split allNodes terminals classMap) groups
    in if length newGroups == numGroups
       then (classMap, groupsByClass)
       else let (classMap', groups') = buildClassMapAndGroups terminals newGroups
            in refine allNodes terminals classMap' groups'

split :: forall f. (Traversable f, Ord (f NodeId))
      => IntMap (f NodeId) -> IntSet -> IntMap Int -> [NodeId] -> [[NodeId]]
split allNodes terminals classMap currentGroup =
    -- Opaque terminal nodes are atomic and never split.
    -- Structured terminals CAN be merged with regular nodes if they stay bisimilar.
    if any (`IntSet.member` terminals) currentGroup && all (`IntSet.member` terminals) currentGroup
    then [currentGroup]
    else Map.elems $ Map.fromListWith (++) [ (fmap (lookupClass terminals classMap) (getNode allNodes i), [i]) | i <- currentGroup ]

getNode :: IntMap (f NodeId) -> NodeId -> f NodeId
getNode nodes i = fromMaybe (error $ "GraphAlgebra: missing node " ++ show i) $ IntMap.lookup i nodes

lookupClass :: IntSet -> IntMap Int -> NodeId -> Int
lookupClass terminals classMap i
    | IntSet.member i terminals = i
    | otherwise = IntMap.findWithDefault i i classMap

buildClassMap :: IntSet -> [[NodeId]] -> IntMap Int
buildClassMap terminals groups = IntMap.fromList
    [ (i, classId)
    | group <- groups
    , let classId = case filter (`IntSet.member` terminals) group of
            (t:_) -> t
            []    -> head group
    , i <- group
    ]

-- | Build both classMap and groupsByClass in a single pass from groups.
buildClassMapAndGroups :: IntSet -> [[NodeId]] -> (IntMap Int, Map Int [NodeId])
buildClassMapAndGroups terminals groups =
    let classMap = IntMap.fromList
            [ (i, classId)
            | group <- groups
            , let classId = case filter (`IntSet.member` terminals) group of
                    (t:_) -> t
                    []    -> head group
            , i <- group
            ]
        groupsByClass = Map.fromListWith (++) [ (c, [i]) | (i, c) <- IntMap.toList classMap ]
    in (classMap, groupsByClass)

-- | Build a remapping from old NodeIds to new sequential IDs.
-- Terminal nodes keep their IDs. Non-terminal nodes in groups
-- containing a terminal map to that terminal's ID. Other nodes
-- get sequential IDs (0, 1, 2, ...).
buildRemapping :: IntSet -> IntMap Int -> Map Int [NodeId] -> (NodeId -> NodeId, [[NodeId]])
buildRemapping terminals _classMap groupsByClass =
    let realGroups = [ group | group <- Map.elems groupsByClass
                     , not (any (`IntSet.member` terminals) group) ]
        finalMap = IntMap.fromList $
            [ (i, newIdx) | (newIdx, group) <- zip [0..] realGroups, i <- group ] ++
            [ (i, t) | group <- Map.elems groupsByClass
                      , let ts = filter (`IntSet.member` terminals) group
                      , not (null ts)
                      , let t = head ts
                      , i <- group
                      , not (IntSet.member i terminals) ]
        lookupFinal i
            | IntSet.member i terminals = i
            | otherwise = IntMap.findWithDefault i i finalMap
    in (lookupFinal, realGroups)

getChildren :: forall f. (Traversable f) => IntMap (f NodeId) -> NodeId -> [NodeId]
getChildren nodes i
    | i < 0 = []
    | otherwise = case IntMap.lookup i nodes of
        Just node -> execState (traverse (\c -> modify (c:)) node) []
        Nothing   -> []
