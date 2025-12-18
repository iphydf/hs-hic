{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Core.AlgebraicSolver
    ( solveSCC
    ) where

import           Data.Map.Strict (Map)
import qualified Data.Map.Strict as Map
import           Data.Set        (Set)
import qualified Data.Set        as Set
import qualified Debug.Trace     as Debug

debugging :: Bool
debugging = False

dtrace :: String -> a -> a
dtrace msg x = if debugging then Debug.trace msg x else x

-- | Solves a system of monotonic equations for a single SCC.
-- Uses structural variable elimination (Kleene's algorithm / State Elimination).
--
-- This algorithm is purely reductive on the set of variables, ensuring
-- termination if the 'lfp' function for a single variable is terminating.
solveSCC :: forall var expr. (Ord var, Eq expr, Show var, Show expr)
         => (var -> expr -> expr -> expr) -- ^ substitute var expr in_expr
         -> (var -> expr -> expr)         -- ^ lfp of var in_expr
         -> (expr -> expr -> expr)         -- ^ join/merge
         -> expr                          -- ^ bottom (least element)
         -> Map var (Set expr)             -- ^ equations (var = join requirements)
         -> Map var expr
solveSCC subst lfp merge bottom eqns =
    let initial_m = Map.map (foldl (\acc e -> let res = merge acc e in dtrace ("merge " ++ show acc ++ " " ++ show e ++ " -> " ++ show res) res) bottom . Set.toList) eqns
    in solve (Map.keys eqns) (dtrace ("solveSCC initial_m: " ++ show initial_m) initial_m)
  where
    solve :: [var] -> Map var expr -> Map var expr
    solve [] _ = Map.empty
    solve [v] m =
        let e = Map.findWithDefault bottom v m
            v_solved = lfp v e
            res = Map.singleton v v_solved
        in dtrace ("solve [v] " ++ show v ++ " m=" ++ show m ++ " -> " ++ show res) res
    solve (v:vs) m =
        let -- 1. Express v in terms of v and vs.
            e_v = Map.findWithDefault bottom v m
            -- 2. "Eliminate" self-dependency of v by finding its LFP.
            --    This results in an expression v* = f(vs).
            v_star = lfp v e_v
            -- 3. Substitute v* into the equations for the remaining variables.
            m' = Map.map (subst v v_star) (Map.delete v m)
            -- 4. Recursively solve the smaller system.
            solved_vs = solve vs m'
            -- 5. Finally, substitute the solved vs back into v*.
            v_final = Map.foldrWithKey subst v_star solved_vs
            res = Map.insert v v_final solved_vs
        in dtrace ("solve (v:vs) v=" ++ show v ++ " v_star=" ++ show v_star ++ " -> " ++ show res) res
