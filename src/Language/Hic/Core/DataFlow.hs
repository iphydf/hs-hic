{-# LANGUAGE AllowAmbiguousTypes    #-}
{-# LANGUAGE FlexibleContexts       #-}
{-# LANGUAGE FlexibleInstances      #-}
{-# LANGUAGE FunctionalDependencies #-}
{-# LANGUAGE KindSignatures         #-}
{-# LANGUAGE LambdaCase             #-}
{-# LANGUAGE MultiParamTypeClasses  #-}
{-# LANGUAGE MultiWayIf             #-}
{-# LANGUAGE OverloadedStrings      #-}
{-# LANGUAGE ScopedTypeVariables    #-}
{-# LANGUAGE TupleSections          #-}

-- | This module provides a generic framework for forward data flow analysis
-- on C code, represented by the 'Language.Cimple.Ast'. It includes tools
-- for building a control flow graph (CFG) from a function definition and
-- a fixpoint solver to compute data flow facts.
--
-- The core components are:
--
-- * 'CFG': A control flow graph representation, where nodes contain basic
--   blocks of statements.
-- * 'DataFlow': A type class that defines the specific analysis to be
--   performed (e.g., reaching definitions, liveness analysis).
-- * 'buildCFG': A function to construct a 'CFG' from a 'C.FunctionDefn'.
-- * 'fixpoint': A generic solver that iteratively computes data flow facts
--   until a stable state (fixpoint) is reached.
--
-- To use this module, you need to:
--
-- 1. Define a data type for your data flow facts.
-- 2. Create an instance of the 'DataFlow' type class for your data type,
--    implementing 'emptyFacts', 'transfer', and 'join'.
-- 3. Build the CFG for a function using 'buildCFG'.
-- 4. Run the 'fixpoint' solver on the generated CFG.
-- 5. Extract and use the computed 'cfgInFacts' and 'cfgOutFacts' from the
--    resulting CFG.
module Language.Hic.Core.DataFlow
    ( CFGNode (..)
    , CFG
    , DataFlow (..)
    , fixpoint
    , buildCFG
    ) where

import           Control.Monad              (foldM)
import           Data.Fix                   (Fix (Fix, unFix))
import           Data.Foldable              (foldl')
import           Data.Kind                  (Type)
import           Data.List                  (partition)
import           Data.Map.Strict            (Map)
import qualified Data.Map.Strict            as Map
import           Data.Maybe                 (mapMaybe)
import           Data.Set                   (Set)
import qualified Data.Set                   as Set
import           Data.String                (IsString)
import           Debug.Trace                (trace)
import           Language.Cimple            (NodeF (..))
import qualified Language.Cimple            as C
import           Language.Cimple.Pretty     (showNodePlain)
import qualified Language.Hic.Core.CFG      as CFGBuilder
import           Language.Hic.Core.Types    (lookupOrError)
import           Language.Hic.Core.Worklist
import           Prettyprinter              (Pretty (..))

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then trace msg x else x

-- | A node in the control flow graph. Each node represents a basic block
-- of statements.
data CFGNode l a = CFGNode
    { cfgNodeId   :: Int -- ^ A unique identifier for the node.
    , cfgPreds    :: [Int] -- ^ A list of predecessor node IDs.
    , cfgSuccs    :: [Int] -- ^ A list of successor node IDs.
    , cfgStmts    :: [C.Node (C.Lexeme l)] -- ^ The statements in this basic block.
    , cfgInFacts  :: a -- ^ The data flow facts at the entry of this node.
    , cfgOutFacts :: a -- ^ The data flow facts at the exit of this node.
    }
    deriving (Show, Eq)

-- | The Control Flow Graph is a map from node IDs to 'CFGNode's.
type CFG l a = Map Int (CFGNode l a)

-- | A type class for data flow analysis. Users of this framework must
-- provide an instance of this class for their specific analysis.
class (Eq a, Show a, Monad m, Ord callCtx) => DataFlow m (c :: Type -> Type) l a callCtx | a -> l, a -> callCtx where
    -- | The facts for an empty basic block.
    emptyFacts :: c l -> m a
    -- | The transfer function defines how a single statement affects the
    -- data flow facts. It takes the facts before the statement and
    -- returns the facts after the statement, plus any new work discovered.
    transfer :: c l -> l -> Int -> a -> C.Node (C.Lexeme l) -> m (a, Set (l, callCtx))
    -- | The join operator combines facts from multiple predecessor nodes.
    -- This is used at control flow merge points (e.g., after an if-statement
    -- or at the start of a loop).
    join :: c l -> a -> a -> m a
    -- | The join where a loop goes back to: the same, unless something is
    -- worth working out only there.
    joinLoop :: c l -> a -> a -> m a
    joinLoop = join
    -- | The join where a loop goes back to, of what comes in from before the
    -- loop and what comes back round it, given the statements in the loop.
    joinLoopHead :: c l -> [C.Node (C.Lexeme l)] -> a -> a -> m a
    joinLoopHead ctx _ = joinLoop ctx
    -- | Widening: given a block's old entry facts and the newly joined ones,
    -- what to use instead once they have changed often. Facts that
    -- change every time round a loop (a pointer moved forward each time)
    -- must jump to something stable here, or the fixpoint never ends.
    widen :: c l -> a -> a -> m a
    widen _ _ new = return new
    -- | Widening where a loop goes back to, given the statements in the
    -- loop: what the loop doesn't change needn't be widened there, as it
    -- only changes where something round it does.
    widenLoop :: c l -> [C.Node (C.Lexeme l)] -> a -> a -> m a
    widenLoop ctx _ = widen ctx

-- | A generic fixpoint solver for forward data flow analysis. This function
-- iteratively applies the transfer function to each node in the CFG until
-- the data flow facts no longer change. It uses a worklist algorithm for
-- efficiency, and returns the final CFG along with any new work discovered.
fixpoint :: forall m c l a callCtx. (DataFlow m c l a callCtx, Show l, Ord l) => c l -> l -> CFG l a -> m (CFG l a, Set (l, callCtx))
fixpoint ctx funcName (cfg :: CFG l a) =
    let
        worklist = fromList (Map.keys cfg)
    in
        go worklist cfg Map.empty Set.empty False
    where
        -- | How many times a block's entry facts change before they're widened.
        widenAfter = 2 :: Int
        -- | How many times every block is worked out again after widening,
        -- from what's known then: each time is still true of every run, and
        -- gets back some of what widening gave up.
        descents = 2 :: Int

        (heads, order) = loopHeads cfg
        bodies = loopBodies cfg
        loopStmts h = concatMap cfgStmts (mapMaybe (`Map.lookup` cfg) (Set.toList (Map.findWithDefault Set.empty h bodies)))

        joinedFacts :: CFG l a -> CFGNode l a -> m a
        joinedFacts cfg' node = case mapMaybe (`Map.lookup` cfg') (cfgPreds node) of
            []                    -> return $ cfgInFacts node
            preds | Set.member h heads, (back@(_:_), entry@(_:_)) <- partition ((`Set.member` body) . cfgNodeId) preds -> do
                before <- joinAll (joinLoop ctx) entry
                round' <- joinAll (joinLoop ctx) back
                joinLoopHead ctx (loopStmts h) before round'
            preds -> joinAll (if Set.member h heads then joinLoop ctx else join ctx) preds
          where
            h = cfgNodeId node
            body = Map.findWithDefault Set.empty h bodies
            joinAll joining (p : ps) = foldM joining (cfgOutFacts p) (map cfgOutFacts ps)
            joinAll _ []             = return $ cfgInFacts node

        go :: Worklist Int -> CFG l a -> Map Int Int -> Set (l, callCtx) -> Bool -> m (CFG l a, Set (l, callCtx))
        go worklist cfg' changeCounts accumulatedWork widened
            | Just (currentId, worklist') <- pop worklist = do
                let node = lookupOrError "fixpoint" cfg' currentId
                let timesChanged = Map.findWithDefault 0 currentId changeCounts
                let widening = timesChanged >= widenAfter && Set.member currentId heads

                joined <- joinedFacts cfg' node
                inFacts' <- if widening then widenLoop ctx (loopStmts currentId) (cfgInFacts node) joined else return joined

                (outFacts', blockWork) <-
                    foldM
                        (\(accFacts, accWork) stmt -> do
                            (newFacts, newWork) <- transfer ctx funcName (cfgNodeId node) (dtrace ("fixpoint fold: accFacts=" <> show accFacts) accFacts) stmt
                            return (newFacts, Set.union accWork newWork))
                        (inFacts', Set.empty)
                        (cfgStmts node)

                let outFactsChanged = outFacts' /= cfgOutFacts node
                let cfg'' = dtrace (unlines [ "fixpoint (" <> show funcName <> ", node " <> show currentId <> "):"
                                            , "  inFacts': " <> show inFacts'
                                            , "  outFacts': " <> show outFacts'
                                            , "  old outFacts: " <> show (cfgOutFacts node)
                                            , "  outFactsChanged: " <> show outFactsChanged
                                            ]) $ Map.insert currentId (node { cfgInFacts = inFacts', cfgOutFacts = outFacts' }) cfg'
                let worklist'' = if outFactsChanged
                        then pushList (cfgSuccs node) worklist'
                        else worklist'
                let accumulatedWork' = Set.union accumulatedWork blockWork
                -- Reached for the first time isn't a change.
                let changedFromKnown = inFacts' /= cfgInFacts node && cfgInFacts node /= cfgInFacts (lookupOrError "fixpoint" cfg currentId)
                let timesChanged' = if changedFromKnown then timesChanged + 1 else timesChanged
                go worklist'' cfg'' (Map.insert currentId timesChanged' changeCounts) accumulatedWork' (widened || widening)
            | widened = descend descents cfg' accumulatedWork
            | otherwise = return (cfg', accumulatedWork)

        descend :: Int -> CFG l a -> Set (l, callCtx) -> m (CFG l a, Set (l, callCtx))
        descend n cfg' accumulatedWork
            | n <= 0 = return (cfg', accumulatedWork)
            | otherwise = do
                (cfg'', work) <- foldM again (cfg', accumulatedWork) order
                if cfg'' == cfg' then return (cfg'', work) else descend (n - 1) cfg'' work
        again (cfg', work) nodeId = do
            let node = lookupOrError "fixpoint" cfg' nodeId
            inFacts' <- joinedFacts cfg' node
            (outFacts', blockWork) <-
                foldM
                    (\(accFacts, accWork) stmt -> do
                        (newFacts, newWork) <- transfer ctx funcName (cfgNodeId node) accFacts stmt
                        return (newFacts, Set.union accWork newWork))
                    (inFacts', Set.empty)
                    (cfgStmts node)
            return (Map.insert nodeId node { cfgInFacts = inFacts', cfgOutFacts = outFacts' } cfg', Set.union work blockWork)

-- | The blocks a loop goes back to, which are the only ones widened, and
-- every block in an order where one comes before what follows it, but for
-- going back round a loop: from a walk along the graph from the first block
-- (and from any it doesn't reach).
loopHeads :: CFG l a -> (Set Int, [Int])
loopHeads cfg =
    let (_, heads, post) = foldl' (visit Set.empty) (Set.empty, Set.empty, []) (Map.keys cfg)
    in (heads, post)
  where
    visit onPath (seen, heads, post) n
        | Set.member n seen = (seen, heads, post)
        | otherwise =
            let onPath' = Set.insert n onPath
                step acc@(seen', heads', post') s
                    | Set.member s onPath' = (seen', Set.insert s heads', post')
                    | otherwise = visit onPath' acc s
                (seen'', heads'', post'') = foldl' step (Set.insert n seen, heads, post) (maybe [] cfgSuccs (Map.lookup n cfg))
            in (seen'', heads'', n : post'')

-- | The blocks of each loop, by the block it goes back to: those from
-- which a block going back to it can be reached without passing it.
loopBodies :: CFG l a -> Map Int (Set Int)
loopBodies cfg = Map.fromListWith Set.union [ (h, body h src) | (src, h) <- backEdges ]
  where
    backEdges = let (_, es) = foldl' (visit Set.empty) (Set.empty, []) (Map.keys cfg) in es
    visit onPath (seen, es) n
        | Set.member n seen = (seen, es)
        | otherwise =
            let onPath' = Set.insert n onPath
                step acc@(seen', es') s
                    | Set.member s onPath' = (seen', (n, s) : es')
                    | otherwise = visit onPath' acc s
            in foldl' step (Set.insert n seen, es) (maybe [] cfgSuccs (Map.lookup n cfg))
    body h src = go (Set.fromList [h, src]) [src]
      where
        go acc [] = acc
        go acc (x : xs)
            | x == h = go acc xs
            | otherwise =
                let new = [ p | p <- maybe [] cfgPreds (Map.lookup x cfg), Set.notMember p acc ]
                in go (foldr Set.insert acc new) (new ++ xs)

-- | Build a control flow graph for a function definition. This is the main
-- entry point for constructing a CFG from a Cimple AST.
buildCFG :: forall m c l a callCtx. (DataFlow m c l a callCtx, Pretty l, Ord l, Show l, IsString l) => c l -> C.Node (C.Lexeme l) -> a -> m (CFG l a)
buildCFG ctx cNode@(Fix (C.FunctionDefn _ (Fix (C.FunctionPrototype _ (C.L _ _ funcName) _)) _)) initialFacts = do
    let structuralCFG = CFGBuilder.buildCFG cNode

    let addFacts :: Int -> CFGBuilder.CFGNode l -> m (CFGNode l a)
        addFacts nodeId structuralNode = do
            facts <- if nodeId == 0 then return initialFacts else emptyFacts ctx
            return $ CFGNode
                    { cfgNodeId   = CFGBuilder.cfgNodeId structuralNode
                    , cfgPreds    = CFGBuilder.cfgPreds structuralNode
                    , cfgSuccs    = CFGBuilder.cfgSuccs structuralNode
                    , cfgStmts    = CFGBuilder.cfgStmts structuralNode
                    , cfgInFacts  = facts
                    , cfgOutFacts = facts
                    }

    dfaCFG <- Map.traverseWithKey addFacts structuralCFG
    return $ dtrace ("\n--- CFG for " <> show funcName <> " ---\n" <> show (fmap (\n -> (cfgNodeId n, cfgPreds n, cfgSuccs n, map showNodePlain (cfgStmts n))) dfaCFG)) dfaCFG
buildCFG _ _ _ = return Map.empty
