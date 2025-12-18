{-# LANGUAGE BangPatterns        #-}
{-# LANGUAGE DeriveGeneric       #-}
{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE StrictData          #-}
module Language.Hic.Refined.Solver
    ( TypeSummary (..)
    , SolverEnv (..)
    , FilterResult (..)
    , Constraint (..)
    , solve
    , runWorklist
    ) where

import qualified Data.IntMap.Merge.Strict         as IntMap
import           Data.IntMap.Strict               (IntMap)
import qualified Data.IntMap.Strict               as IntMap
import           Data.IntSet                      (IntSet)
import qualified Data.IntSet                      as IntSet
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Set                         (Set)
import qualified Data.Set                         as Set
import           Data.Text                        (Text)
import           Data.Word                        (Word32)
import qualified Debug.Trace                      as Debug
import           GHC.Generics                     (Generic)
import           Language.Cimple                  (Lexeme)
import           Language.Hic.Refined.Context     (MappingContext,
                                                   MappingRefinements (..),
                                                   emptyContext,
                                                   emptyRefinements, mrHash,
                                                   mrRefinements, setRefinement)
import           Language.Hic.Refined.LatticeOp   (Polarity (..))
import           Language.Hic.Refined.PathContext (PathContext (..), emptyPath)
import           Language.Hic.Refined.Registry    (Registry)
import           Language.Hic.Refined.State       (ProductState (..))
import           Language.Hic.Refined.Transition  (TransitionEnv (..),
                                                   isRefinable, step,
                                                   variableKey)
import           Language.Hic.Refined.Types       (AnyRigidNodeF (..),
                                                   ObjectStructure (..),
                                                   RigidNodeF (..), TemplateId,
                                                   TerminalNode (..))

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

-- | A compact representation of a solved SCC's refined type information.
-- Used to isolate SCCs and enable incremental compilation.
data TypeSummary = TypeSummary
    { tsExportedTypes :: Map Text (AnyRigidNodeF TemplateId Int)
    -- ^ Map of names to their canonical refined type structure IDs.
    }
    deriving (Show, Eq, Ord, Generic)

-- | Environment for the project-wide Refined Solver.
data SolverEnv = SolverEnv
    { seSummaries :: Map Text TypeSummary
    -- ^ Cached summaries from already-solved SCCs.
    }
    deriving (Show, Eq, Ord, Generic)

-- | Result of the Refinement Filter (linear symbolic pass).
-- Identifies which fragments of the project require the rigorous graph solver.
data FilterResult = FilterResult
    { frRequiresRigorousSolver :: Bool
    -- ^ True if the code contains Refinement Triggers (Existentials, Tagged Unions).
    , frHotspots               :: [Text]
    -- ^ Names of functions/structs identified as hotspots.
    }
    deriving (Show, Eq, Ord, Generic)

-- | A subtyping constraint to be solved.
data Constraint
    = CSubtype Word32 Word32 Polarity MappingContext PathContext Int Int (Maybe (Lexeme Text)) FilePath
    | CInherit Word32 Word32 (Maybe (Lexeme Text)) FilePath
    deriving (Show, Eq, Ord, Generic)

-- | Executes the project-wide fixpoint solver on a set of constraints.
solve :: Registry Word32
      -> Map Word32 (AnyRigidNodeF TemplateId Word32)
      -> [Constraint]
      -> (Word32, Word32, Word32, Word32) -- ^ (Bottom, Any, Conflict, STerminal) IDs
      -> Either ProductState MappingRefinements
solve registry nodes constraints terminals =
    let toProductState = \case
            CSubtype l r pol gamma _ dL dR loc file -> ProductState l r pol False gamma dL dR Nothing loc (Just file)
            CInherit l r loc file                   -> ProductState l r PMeet True  emptyContext 0 0 Nothing loc (Just file)
        getPathCtx = \case
            CSubtype _ _ _ _ c _ _ _ _ -> c
            CInherit _ _ _ _           -> PathContext Map.empty Map.empty
        constraintMap = Map.fromList [ (toProductState c, getPathCtx c) | c <- constraints ]
        topLevel = Map.keysSet constraintMap
    in runWorklist registry nodes constraintMap topLevel terminals emptyRefinements topLevel Set.empty IntMap.empty Map.empty

terminalToId :: TerminalNode a -> (Word32, Word32, Word32, Word32) -> Maybe Word32
terminalToId term (bot, any', conflict, _) = case term of
    SBottom     -> Just bot
    SAny        -> Just any'
    SConflict   -> Just conflict
    STerminal{} -> Nothing

-- | Core worklist loop for the Product Automaton.
-- Only moves UP the lattice. Restarts on refinement changes to ensure consistency.
runWorklist :: Registry Word32
            -> Map Word32 (AnyRigidNodeF TemplateId Word32)
            -> Map ProductState PathContext
            -> Set ProductState
            -> (Word32, Word32, Word32, Word32)
            -> MappingRefinements
            -> Set ProductState
            -> Set ProductState
            -> IntMap (Set ProductState)
            -> Map ProductState (Set Int)
            -> Either ProductState MappingRefinements
runWorklist registry nodes constraints topLevel terminals !refs worklist visited deps revDeps
    | Set.null worklist = Right refs
    | otherwise =
        let (ps, rest) = Set.deleteFindMin worklist
        in if ps `Set.member` visited
           then runWorklist registry nodes constraints topLevel terminals refs rest visited deps revDeps
           else dtrace ("solve step: " ++ show (psNodeL ps, psNodeR ps, psPolarity ps)) $
               let pathCtx = Map.findWithDefault (PathContext Map.empty Map.empty) ps { psParentVar = Nothing } constraints
                   (refineL, refineR) = (True, not (psOneWay ps))
                   env = TransitionEnv nodes registry (psPolarity ps) pathCtx emptyPath terminals refineL refineR

                   -- Special handling for CInherit: Don't refine psNodeR
                   (result, !newRefsStep, psDeps) = step env ps refs

                   -- Update dependency tracking
                   oldDeps = Map.findWithDefault Set.empty ps revDeps
                   !newDepsMap = if oldDeps == psDeps then deps
                                 else foldr (\k m -> IntMap.insertWith Set.union k (Set.singleton ps) m)
                                            (foldr (\k m -> IntMap.update (\s -> let s' = Set.delete ps s in if Set.null s' then Nothing else Just s') k m) deps oldDeps)
                                            psDeps
                   !newRevDeps = if oldDeps == psDeps then revDeps else Map.insert ps psDeps revDeps

                   requeue changedRefs oldRefs currentWorklist currentVisited currentDeps =
                       let !changedKeys = IntMap.merge IntMap.preserveMissing IntMap.dropMissing
                                          (IntMap.zipWithMaybeMatched (\_ v1 v2 -> if v1 == v2 then Nothing else Just v1))
                                          (mrRefinements changedRefs) (mrRefinements oldRefs)
                           !affectedStates = IntMap.foldlWithKey' (\acc k _ -> Set.union acc (IntMap.findWithDefault Set.empty k currentDeps)) Set.empty changedKeys
                       in if Set.null affectedStates
                          then (currentWorklist, currentVisited)
                          else (Set.union currentWorklist affectedStates, Set.difference currentVisited affectedStates)

               in dtrace ("solve step: " ++ show ps ++ " -> res: " ++ show result) $ case result of
                   AnyRigidNodeF (RTerminal SConflict) ->
                       let nodeL = Map.lookup (psNodeL ps) nodes
                           nodeR = Map.lookup (psNodeR ps) nodes
                       in dtrace ("CONFLICT at " ++ show ps ++ "\n  Origin: " ++ show (psOrigin ps) ++ "\n  NodeL: " ++ show nodeL ++ "\n  NodeR: " ++ show nodeR) (Left ps)
                   AnyRigidNodeF (RTerminal term) | Just termId <- terminalToId term terminals ->
                       let refsParent = case psParentVar ps of
                               Just (d, tid) | psPolarity ps == PMeet ->
                                   dtrace ("Refining Parent " ++ show tid ++ " at depth " ++ show d ++ " to " ++ show termId) $
                                   setRefinement (variableKey nodes d tid) termId newRefsStep
                               _ -> newRefsStep
                           refsL = case Map.lookup (psNodeL ps) nodes of
                               Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && psPolarity ps == PMeet && refineL ->
                                   dtrace ("Refining L " ++ show tid ++ " to " ++ show termId) $
                                   setRefinement (variableKey nodes (psDepthL ps) tid) termId refsParent
                               _ -> refsParent
                           refsR = case Map.lookup (psNodeR ps) nodes of
                               Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && psPolarity ps == PMeet && refineR ->
                                   dtrace ("Refining R " ++ show tid ++ " to " ++ show termId) $
                                   setRefinement (variableKey nodes (psDepthR ps) tid) termId refsL
                               _ -> refsL
                       in if mrHash refsR /= mrHash refs
                          then let (newWorklist, newVisited) = requeue refsR refs rest (Set.insert ps visited) newDepsMap
                                   children = Set.fromList $ foldMap (:[]) (AnyRigidNodeF (RTerminal term))
                                   finalWorklist = Set.union newWorklist children
                               in runWorklist registry nodes constraints topLevel terminals refsR finalWorklist newVisited newDepsMap newRevDeps
                          else let children = Set.fromList $ foldMap (:[]) (AnyRigidNodeF (RTerminal term))
                                   newWorklist = Set.union rest children
                               in runWorklist registry nodes constraints topLevel terminals refsR newWorklist (Set.insert ps visited) newDepsMap newRevDeps
                   AnyRigidNodeF n ->
                       if mrHash newRefsStep /= mrHash refs
                       then let (newWorklist, newVisited) = requeue newRefsStep refs rest (Set.insert ps visited) newDepsMap
                                children = Set.fromList $ foldMap (:[]) n
                                finalWorklist = Set.union newWorklist children
                            in runWorklist registry nodes constraints topLevel terminals newRefsStep finalWorklist newVisited newDepsMap newRevDeps
                       else
                           let children = Set.fromList $ foldMap (:[]) n
                               newWorklist = Set.union rest children
                           in runWorklist registry nodes constraints topLevel terminals refs newWorklist (Set.insert ps visited) newDepsMap newRevDeps
