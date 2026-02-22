{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.GraphSolver
    ( ConstraintGraph
    , solveGraph
    , solveAll
    ) where

import qualified Data.Graph                                    as Graph
import           Data.Map.Strict                               (Map)
import qualified Data.Map.Strict                               as Map
import           Data.Maybe                                    (fromMaybe)
import           Data.Set                                      (Set)
import qualified Data.Set                                      as Set
import           Language.Hic.Core.TypeSystem                  (FullTemplate,
                                                                FullTemplateF (..),
                                                                TemplateId (..),
                                                                TypeInfo)
import qualified Language.Hic.TypeSystem.Core.Base             as TS
import           Language.Hic.TypeSystem.Core.TypeGraph        (TypeGraph)
import qualified Language.Hic.TypeSystem.Core.TypeGraph        as TG

import           Language.Hic.Core.AlgebraicSolver             (solveSCC)
import           Language.Hic.TypeSystem.Core.Canonicalization (minimizeGraph)
import           Language.Hic.TypeSystem.Core.Lattice          (joinGraph)

-- | A graph of constraints where each template points to a set of structural requirements.
type ConstraintGraph p = Map (FullTemplate p) (Set (TypeGraph p))

-- | Resolves a template through the constraint graph co-inductively.
-- Guaranteed to terminate by processing the dependency graph's SCCs.
solveGraph :: ConstraintGraph p -> FullTemplate p -> TypeInfo p
solveGraph graph start = fromMaybe (TS.Template (ftId start) (ftIndex start)) (fmap TG.toTypeInfo (Map.lookup start (solveAll graph [start])))

-- | Resolves multiple templates simultaneously.
solveAll :: forall p. ConstraintGraph p -> [FullTemplate p] -> Map (FullTemplate p) (TypeGraph p)
solveAll graph starts =
    let reachableKeys = collectReachable Set.empty starts
        nodes = [ (k, k, getDeps k) | k <- Set.toList reachableKeys ]
        sccs = Graph.stronglyConnComp nodes
    in foldl resolveScc Map.empty sccs
  where
    getDeps k = case Map.lookup k graph of
        Nothing  -> []
        Just gs -> concatMap TG.collectTemplateVarsFromGraph (Set.toList gs)

    collectReachable seen [] = seen
    collectReachable seen (k:ks)
        | Set.member k seen = collectReachable seen ks
        | otherwise = collectReachable (Set.insert k seen) (getDeps k ++ ks)

    resolveScc :: Map (FullTemplate p) (TypeGraph p) -> Graph.SCC (FullTemplate p) -> Map (FullTemplate p) (TypeGraph p)
    resolveScc acc (Graph.AcyclicSCC k) = resolveAcyclicScc acc k
    resolveScc acc (Graph.CyclicSCC ks) = resolveCyclicScc acc ks

    substituteAll acc g =
        let vars = TG.collectTemplateVarsFromGraph g
            substituted = foldl (\accG v -> case Map.lookup v acc of
                                    Just vG -> TG.substitute v vG accG
                                    Nothing -> accG) g vars
        in minimizeGraph substituted

    resolveAcyclicScc acc k =
        case Map.lookup k graph of
            Nothing -> Map.insert k (TG.fromTypeInfo (TS.Template (ftId k) (ftIndex k))) acc
            Just gs ->
                let isVar ft = ftId ft == ftId k
                    resolvedGraphs = map (substituteAll acc) (Set.toList gs)
                    merged = foldl (joinGraph isVar) (TG.fromTypeInfo TS.Unconstrained) resolvedGraphs
                in Map.insert k (minimizeGraph merged) acc

    resolveCyclicScc acc ks =
        let isInternal ft = ftId ft `elem` map ftId ks

            -- In the domain of equi-recursive types, LFP is handled by TG.lfp.
            lfp' v g = TG.lfp v g

            -- Substitution replaces a template with its solved expression.
            subst' v vG targetG = TG.substitute v vG targetG

            join' g1 g2 = joinGraph isInternal g1 g2

            -- Initial equations for the SCC: substitute everything from outside the SCC.
            eqns = Map.fromList [ (k, Set.map (substituteAll acc) (fromMaybe Set.empty (Map.lookup k graph))) | k <- ks ]
            bottom = TG.fromTypeInfo TS.Unconstrained

            -- Solve the system of equations using variable elimination.
            resultMap = Map.map minimizeGraph $ solveSCC subst' lfp' join' bottom eqns
        in Map.union resultMap acc


