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
    , solveAll
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
import           Language.Cimple                  (Lexeme (..))
import qualified Language.Cimple                  as C
import           Language.Hic.Refined.Context     (MappingContext,
                                                   MappingRefinements (..),
                                                   changedKeys, clearChanged,
                                                   emptyContext,
                                                   emptyRefinements,
                                                   getRefinement, mrHash,
                                                   mrRefinements, setRefinement)
import           Language.Hic.Refined.LatticeOp   (Polarity (..))
import           Language.Hic.Refined.PathContext (PathContext (..), emptyPath)
import           Language.Hic.Refined.Registry    (Registry)
import           Language.Hic.Refined.State       (ProductState (..))
import           Language.Hic.Refined.Transition  (TransitionEnv (..),
                                                   betterBinding, isRefinable,
                                                   step, transitionEnv,
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

-- | Executes the project-wide fixpoint solver on a set of constraints: the
-- first conflict it meets, or the refinements. It stops there, so the
-- conflict can be with a binding that 'solveAll' would replace later.
solve :: Registry Word32
      -> Map Word32 (AnyRigidNodeF TemplateId Word32)
      -> [Constraint]
      -> (Word32, Word32, Word32, Word32) -- ^ (Bottom, Any, Conflict, STerminal) IDs
      -> Either ProductState MappingRefinements
solve registry nodes constraints terminals =
    let constraintMap = Map.fromList [ (constraintState c, constraintPathContext c) | c <- constraints ]
        topLevel = Map.keysSet constraintMap
    in case worklist (baseEnv registry nodes terminals) True 0 Map.empty Map.empty constraintMap emptyRefinements topLevel Set.empty IntMap.empty Map.empty of
        (_, Just ps, _, _, _)    -> Left ps
        (_, Nothing, refs, _, _) -> Right refs

-- | Like 'solve', but returns all conflicts, with the number of states it
-- processed, in all and by the source line (file, line) of the constraint each
-- state came from. A conflicting state refines nothing, so one conflict
-- doesn't cause others.
--
-- The conflicts are the solution's: the states the constraints reach with the
-- final refinements, that conflict with them. On the way, a state can
-- conflict with a binding that a better one replaces later (see
-- 'betterBinding'); it's then stepped again, or no longer reached.
--
-- A variable made for a declaration is bound to the type it's declared with
-- from the start, and stays so: what's assigned to it is checked against its
-- declaration, whatever the solver meets first.
solveAll :: Registry Word32
         -> Map Word32 (AnyRigidNodeF TemplateId Word32)
         -> [(Word32, Word32)] -- ^ (variable, declared type) of each declaration
         -> [Constraint]
         -> (Word32, Word32, Word32, Word32) -- ^ (Bottom, Any, Conflict, STerminal) IDs
         -> ([(ProductState, ProductState)], MappingRefinements, Int, Map (Maybe FilePath, Int) Int)
solveAll registry nodes definitions constraints terminals =
    let constraintMap = Map.fromList [ (constraintState c, constraintPathContext c) | c <- constraints ]
        topLevel = Map.keysSet constraintMap
        declared = [ (variableKey nodes 0 tid, ty) | (var, ty) <- definitions, Just (AnyRigidNodeF (RObject (VVar tid _) _)) <- [Map.lookup var nodes] ]
        initialRefs = clearChanged (foldr (uncurry setRefinement) emptyRefinements declared)
        env = (baseEnv registry nodes terminals) { teFixed = IntSet.fromList (map fst declared) }
        (results, _, refs, steps, origins) =
            worklist env False 0 Map.empty Map.empty constraintMap initialRefs topLevel Set.empty IntMap.empty Map.empty
    in (finalConflicts results topLevel, refs, steps, origins)

-- | The environment of every step, with the graph's indexes built once: each
-- step sets its own polarity, path context and which sides it refines.
baseEnv :: Registry Word32 -> Map Word32 (AnyRigidNodeF TemplateId Word32) -> (Word32, Word32, Word32, Word32) -> TransitionEnv Word32
baseEnv registry nodes terminals = transitionEnv nodes registry PMeet (PathContext Map.empty Map.empty) emptyPath terminals True True

constraintState :: Constraint -> ProductState
constraintState = \case
    CSubtype l r pol gamma _ dL dR loc file -> ProductState l r pol False gamma dL dR Nothing loc (Just file)
    CInherit l r loc file                   -> ProductState l r PMeet True  emptyContext 0 0 Nothing loc (Just file)

constraintPathContext :: Constraint -> PathContext
constraintPathContext = \case
    CSubtype _ _ _ _ c _ _ _ _ -> c
    CInherit _ _ _ _           -> PathContext Map.empty Map.empty

terminalToId :: TerminalNode a -> (Word32, Word32, Word32, Word32) -> Maybe Word32
terminalToId term (bot, any', conflict, _) = case term of
    SBottom     -> Just bot
    SAny        -> Just any'
    SConflict   -> Just conflict
    STerminal{} -> Nothing

-- | The latest step of each state: whether it conflicted, and the states it
-- leads to.
type Results = Map ProductState (Bool, [ProductState])

-- | The conflicting states the constraints reach through each state's latest
-- step, each once, as first reached, with the constraint it was reached from.
finalConflicts :: Results -> Set ProductState -> [(ProductState, ProductState)]
finalConflicts results = go Set.empty [] . map (\c -> (c, c)) . Set.toList
  where
    go _ acc [] = reverse acc
    go seen acc ((ps, root):rest)
        | ps `Set.member` seen = go seen acc rest
        | otherwise = case Map.lookup ps results of
            Just (True, _)         -> go seen' ((ps, root) : acc) rest
            Just (False, children) -> go seen' acc (map (\c -> (c, root)) children ++ rest)
            Nothing                -> go seen' acc rest
      where
        seen' = Set.insert ps seen

-- | The worklist loop: steps states until none is left whose refinements
-- changed since its latest step. With @stopAtFirst@, it stops at the first
-- conflict it meets.
worklist :: TransitionEnv Word32 -> Bool -> Int -> Map (Maybe FilePath, Int) Int -> Results
            -> Map ProductState PathContext
            -> MappingRefinements
            -> Set ProductState
            -> Set ProductState
            -> IntMap (Set ProductState)
            -> Map ProductState IntSet
            -> (Results, Maybe ProductState, MappingRefinements, Int, Map (Maybe FilePath, Int) Int)
worklist env0 stopAtFirst !steps !origins !results constraints !refs work visited deps revDeps
    | Set.null work = (results, Nothing, refs, steps, origins)
    | otherwise =
        let nodes = teNodes env0
            terminals = teTerminals env0
            (ps, rest) = Set.deleteFindMin work
        in if ps `Set.member` visited
           then worklist env0 stopAtFirst steps origins results constraints refs rest visited deps revDeps
           else dtrace ("solve step: " ++ show (psNodeL ps, psNodeR ps, psPolarity ps)) $
               let pathCtx = Map.findWithDefault (PathContext Map.empty Map.empty) ps { psParentVar = Nothing } constraints
                   (refineL, refineR) = (True, not (psOneWay ps))
                   env = env0 { tePolarity = psPolarity ps, tePathCtx = pathCtx, teRefineL = refineL, teRefineR = refineR }

                   -- Special handling for CInherit: Don't refine psNodeR
                   (result, !newRefsStep, psDeps) = step env ps (clearChanged refs)
                   !origins' = Map.insertWith (+) (psFile ps, maybe 0 (\(L (C.AlexPn _ line _) _ _) -> line) (psOrigin ps)) 1 origins

                   -- Update dependency tracking
                   oldDeps = Map.findWithDefault IntSet.empty ps revDeps
                   !newDepsMap = if oldDeps == psDeps then deps
                                 else IntSet.foldr (\k m -> IntMap.insertWith Set.union k (Set.singleton ps) m)
                                            (IntSet.foldr (\k m -> IntMap.update (\s -> let s' = Set.delete ps s in if Set.null s' then Nothing else Just s') k m) deps oldDeps)
                                            psDeps
                   !newRevDeps = if oldDeps == psDeps then revDeps else Map.insert ps psDeps revDeps

                   -- Steps the states whose refinements changed again, and the
                   -- states this one leads to.
                   continue refs' children =
                       let !results' = Map.insert ps (False, children) results
                           visited' = Set.insert ps visited
                           work' = Set.union rest (Set.fromList children)
                       in if mrHash refs' == mrHash refs
                          then worklist env0 stopAtFirst (steps + 1) origins' results' constraints refs work' visited' newDepsMap newRevDeps
                          else
                              let !affected = IntSet.foldl' (\acc k -> Set.union acc (IntMap.findWithDefault Set.empty k newDepsMap)) Set.empty (changedKeys refs')
                              in worklist env0 stopAtFirst (steps + 1) origins' results' constraints refs' (Set.union work' affected) (Set.difference visited' affected) newDepsMap newRevDeps

               in dtrace ("solve step: " ++ show ps ++ " -> res: " ++ show result) $ case result of
                   AnyRigidNodeF (RTerminal SConflict) ->
                       dtrace ("CONFLICT at " ++ show ps ++ "\n  Origin: " ++ show (psOrigin ps)) $
                       if stopAtFirst then (results, Just ps, refs, steps + 1, origins')
                       else worklist env0 stopAtFirst (steps + 1) origins' (Map.insert ps (True, []) results) constraints refs rest (Set.insert ps visited) newDepsMap newRevDeps
                   AnyRigidNodeF (RTerminal term) | Just termId <- terminalToId term terminals ->
                       -- The variables this state is about are that terminal,
                       -- unless they're bound to something better already.
                       let bindTerminal key r
                               | IntSet.member key (teFixed env0) = r
                               | otherwise = case getRefinement key refs of
                                   Just current | not (betterBinding nodes termId current) -> r
                                   _ -> setRefinement key termId r
                           refsParent = case psParentVar ps of
                               Just (d, tid) | psPolarity ps == PMeet ->
                                   dtrace ("Refining Parent " ++ show tid ++ " at depth " ++ show d ++ " to " ++ show termId) $
                                   bindTerminal (variableKey nodes d tid) newRefsStep
                               _ -> newRefsStep
                           refsL = case Map.lookup (psNodeL ps) nodes of
                               Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && psPolarity ps == PMeet && refineL ->
                                   dtrace ("Refining L " ++ show tid ++ " to " ++ show termId) $
                                   bindTerminal (variableKey nodes (psDepthL ps) tid) refsParent
                               _ -> refsParent
                           refsR = case Map.lookup (psNodeR ps) nodes of
                               Just (AnyRigidNodeF (RObject (VVar tid _) _)) | isRefinable tid && psPolarity ps == PMeet && refineR ->
                                   dtrace ("Refining R " ++ show tid ++ " to " ++ show termId) $
                                   bindTerminal (variableKey nodes (psDepthR ps) tid) refsL
                               _ -> refsL
                       in continue refsR []
                   AnyRigidNodeF n -> continue newRefsStep (foldMap (:[]) n)
