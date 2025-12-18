{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TupleSections       #-}
module Language.Hic.Core.AlgebraicSolverSpec (spec) where

import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as Map
import           Data.Set                          (Set)
import qualified Data.Set                          as Set
import qualified Debug.Trace                       as Debug
import           Language.Hic.Core.AlgebraicSolver
import           Test.Hspec
import           Test.QuickCheck

-- | A more powerful expression language representing:
--   max(constant, var1 + k1, var2 + k2, ...)
-- This can represent chains of dependencies like X = Y + 1 (e.g. X is Pointer to Y).
-- We cap the value at 10 to ensure the lattice is finite.
data Expr var = Expr
    { eConst :: Int
    , eVars  :: Map var Int -- variable -> increment
    } deriving (Show, Eq, Ord)

-- | Evaluate an expression with a set of variable bindings.
eval :: Ord var => Map var Int -> Expr var -> Int
eval m (Expr c vs) =
    let varVals = [ Map.findWithDefault 0 v m + k | (v, k) <- Map.toList vs ]
    in min 10 $ foldl max c varVals

-- | Substitute a variable with another expression.
substitute :: Ord var => var -> Expr var -> Expr var -> Expr var
substitute v v_star expr = simplify $ case Map.lookup v (eVars expr) of
    Nothing -> expr
    Just k  ->
        let c_new = max (eConst expr) (eConst v_star + k)
            vs_base = Map.delete v (eVars expr)
            vs_new = Map.foldrWithKey (\v' k' acc -> Map.insertWith max v' (min 10 (k' + k)) acc) vs_base (eVars v_star)
        in Expr c_new vs_new

-- | Simplify an expression.
simplify :: Expr var -> Expr var
simplify (Expr c vs) =
    let c' = min 10 c
        maxK = if Map.null vs then 0 else maximum (Map.elems vs)
    in if c' >= 10 || maxK >= 10
       then Expr 10 Map.empty
       else Expr c' vs

-- | Find the least fixed point of v = expr.
findLFP :: Ord var => var -> Expr var -> Expr var
findLFP v expr = simplify $
    case Map.lookup v (eVars expr) of
        Just k | k > 0 -> Expr 10 Map.empty
        _              -> Expr (eConst expr) (Map.delete v (eVars expr))

-- | Join two expressions.
merge :: Ord var => Expr var -> Expr var -> Expr var
merge e1 e2 =
    let res = Expr (max (eConst e1) (eConst e2)) (Map.unionWith max (eVars e1) (eVars e2))
    in simplify res

spec :: Spec
spec = do
    describe "AlgebraicSolver (Advanced)" $ do
        it "solves a simple identity X = 5" $ do
            let eqns = Map.singleton ("X" :: String) (Set.singleton (Expr 5 Map.empty))
                res = solveSCC substitute findLFP merge (Expr 0 Map.empty) eqns
            fmap (eval Map.empty) (Map.lookup "X" res) `shouldBe` Just 5

        it "solves a simple cycle X = X + 1, X = 2" $ do
            let eqns = Map.singleton ("X" :: String) (Set.fromList [Expr 0 (Map.singleton "X" 1), Expr 2 Map.empty])
                res = solveSCC substitute findLFP merge (Expr 0 Map.empty) eqns
            -- X = max(X+1, 2) hits the ceiling
            fmap (eval Map.empty) (Map.lookup "X" res) `shouldBe` Just 10

        it "solves mutual recursion X = Y + 1, Y = X, X = 5" $ do
            let eqns = Map.fromList
                    [ ("X" :: String, Set.fromList [Expr 0 (Map.singleton "Y" 1), Expr 5 Map.empty])
                    , ("Y", Set.singleton (Expr 0 (Map.singleton "X" 0)))
                    ]
                res = solveSCC substitute findLFP merge (Expr 0 Map.empty) eqns
            -- X = max(X+1, 5) hits the ceiling
            fmap (eval Map.empty) (Map.lookup "X" res) `shouldBe` Just 10
            fmap (eval Map.empty) (Map.lookup "Y" res) `shouldBe` Just 10

        it "solves a complex chain X = Y + 1, Y = Z + 1, Z = 2" $ do
            let eqns = Map.fromList
                    [ ("X" :: String, Set.singleton (Expr 0 (Map.singleton "Y" 1)))
                    , ("Y", Set.singleton (Expr 0 (Map.singleton "Z" 1)))
                    , ("Z", Set.singleton (Expr 2 Map.empty))
                    ]
                res = solveSCC substitute findLFP merge (Expr 0 Map.empty) eqns
            fmap (eval Map.empty) (Map.lookup "X" res) `shouldBe` Just 4
            fmap (eval Map.empty) (Map.lookup "Y" res) `shouldBe` Just 3
            fmap (eval Map.empty) (Map.lookup "Z" res) `shouldBe` Just 2

        it "solves the previously failing QuickCheck case" $ do
            let eqns = Map.fromList
                    [ (1 :: Int, Set.fromList [Expr 0 Map.empty, Expr 0 (Map.fromList [(2,1),(3,0)]), Expr 6 (Map.fromList [(2,0)]), Expr 8 Map.empty])
                    , (2, Set.fromList [Expr 0 Map.empty, Expr 8 Map.empty, Expr 9 Map.empty, Expr 10 Map.empty])
                    , (3, Set.fromList [Expr 1 Map.empty, Expr 2 (Map.fromList [(1,1)]), Expr 7 (Map.fromList [(1,1),(3,1)]), Expr 8 Map.empty])
                    ]
                res = solveSCC substitute findLFP merge (Expr 0 Map.empty) eqns
                resVals = Map.map (eval Map.empty) res
            resVals `shouldBe` Map.fromList [(1,10),(2,10),(3,10)]

        it "satisfies the fixed-point property (QuickCheck)" $ property $ \(Positive (n :: Int)) ->
            -- Generate a random system of equations over n variables.
            let n' = n `mod` 10 + 1
                vars = [1..n']
                genExpr :: Gen (Expr Int)
                genExpr = do
                    c <- choose (0, 10)
                    numVars <- choose (0, 2)
                    vs <- vectorOf numVars ((,) <$> elements vars <*> choose (0, 2))
                    return $ simplify $ Expr c (Map.fromList vs)
                genEqns = Map.fromList <$> (mapM (\v -> (v,) . Set.fromList <$> listOf1 genExpr) vars)
            in forAll genEqns $ \eqns ->
                let res = solveSCC substitute findLFP merge (Expr 0 Map.empty) eqns
                    resVals = Map.map (eval Map.empty) res
                    check v requirements =
                        let expected = foldl max 0 (map (eval resVals) (Set.toList requirements))
                        in Map.lookup v resVals == Just expected

                    -- Simple iterative solver to find the LFP.
                    solveIterative current =
                        let next = Map.map (\reqs -> foldl max 0 (map (eval current) (Set.toList reqs))) eqns
                        in if next == current then current else solveIterative next
                    lfpVals = solveIterative (Map.fromSet (const 0) (Map.keysSet eqns))
                in counterexample ("res: " ++ show res ++ "\nresVals: " ++ show resVals ++ "\nlfpVals: " ++ show lfpVals ++ "\neqns: " ++ show eqns) $
                   all (uncurry check) (Map.toList eqns) && resVals == lfpVals

        it "verifies substitute is consistent with eval" $ property $ \v (Positive (n :: Int)) ->
            let vars = [1..n `mod` 10 + 1]
                genExpr = do
                    c <- choose (0, 10)
                    numVars <- choose (0, 2)
                    vs <- vectorOf numVars ((,) <$> elements vars <*> choose (0, 2))
                    return $ simplify $ Expr c (Map.fromList vs)
            in forAll ((,,) <$> genExpr <*> genExpr <*> (Map.fromList <$> vectorOf (length vars) ((,) <$> elements vars <*> choose (0, 10)))) $ \(v_star, expr, env) ->
                let expr' = substitute (v :: Int) v_star expr
                    val_v_star = eval env v_star
                    env' = Map.insert v val_v_star env
                in eval env expr' == eval env' expr

        it "verifies findLFP is consistent with eval" $ property $ \v (Positive (n :: Int)) ->
            let vars = [1..n `mod` 10 + 1]
                genExpr = do
                    c <- choose (0, 10)
                    numVars <- choose (0, 2)
                    vs <- vectorOf numVars ((,) <$> elements (v:vars) <*> choose (0, 2))
                    return $ simplify $ Expr c (Map.fromList vs)
            in forAll ((,) <$> genExpr <*> (Map.fromList <$> (let vs = filter (/= v) (v:vars) in vectorOf (length vs) ((,) <$> elements vs <*> choose (0, 10))))) $ \(expr, env) ->
                let v_star = findLFP (v :: Int) expr
                    val_v_star = eval env v_star
                    check val = eval (Map.insert v val env) expr
                in counterexample ("v_star: " ++ show v_star ++ "\nval_v_star: " ++ show val_v_star ++ "\nenv: " ++ show env ++ "\nexpr: " ++ show expr) $
                   check val_v_star == val_v_star && all (\x -> check x /= x || val_v_star <= x) [0..10]
