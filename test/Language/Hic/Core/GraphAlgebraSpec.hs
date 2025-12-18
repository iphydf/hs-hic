{-# LANGUAGE DeriveTraversable   #-}
{-# LANGUAGE FlexibleContexts    #-}
{-# LANGUAGE FlexibleInstances   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Core.GraphAlgebraSpec (spec) where

import           Data.IntMap.Strict             (IntMap)
import qualified Data.IntMap.Strict             as IntMap
import           Data.Maybe                     (fromMaybe)
import           Language.Hic.Core.GraphAlgebra
import           Test.Hspec
import           Test.QuickCheck

-- | A simple functor for testing graph algorithms.
data TestF a = Leaf Int | Branch a a deriving (Show, Eq, Ord, Functor, Foldable, Traversable)

instance Arbitrary a => Arbitrary (TestF a) where
    arbitrary = oneof
        [ Leaf <$> arbitrary
        , Branch <$> arbitrary <*> arbitrary
        ]

instance Arbitrary (Graph TestF) where
    arbitrary = do
        numNodes <- choose (1, 5)
        let genNode = oneof
                [ Leaf <$> arbitrary
                , Branch <$> choose (0, numNodes - 1) <*> choose (0, numNodes - 1)
                ]
        nodesList <- vectorOf numNodes genNode
        let nodes = IntMap.fromList (zip [0..] nodesList)
        root <- choose (0, numNodes - 1)
        return $ prune $ Graph nodes root

spec :: Spec
spec = do
    describe "minimize" $ do
        it "minimizes a simple tree" $ do
            let nodes = IntMap.fromList
                    [ (0, Branch 1 2)
                    , (1, Leaf 10)
                    , (2, Leaf 10)
                    ]
                g = Graph nodes 0
                g' = minimize IntMap.empty [] g
            -- Nodes 1 and 2 are identical, so they should be merged.
            IntMap.size (gNodes g') `shouldBe` 2
            gRoot g' `shouldBe` 1 -- New root index after minimization

        it "minimizes a cyclic graph" $ do
            let nodes = IntMap.fromList
                    [ (0, Branch 1 1)
                    , (1, Branch 0 0)
                    ]
                g = Graph nodes 0
                g' = minimize IntMap.empty [] g
            -- Both nodes point to branches of the same structure, they are bisimilar.
            IntMap.size (gNodes g') `shouldBe` 1

        it "produces a canonical normal form (idempotence)" $ do
            let nodes = IntMap.fromList
                    [ (0, Branch 1 2)
                    , (1, Leaf 10)
                    , (2, Leaf 10)
                    ]
                g = Graph nodes 0
                gMin = minimize IntMap.empty [] g
                gMinMin = minimize IntMap.empty [] gMin
            gMin `shouldBe` gMinMin

        it "produces identical graphs for isomorphic inputs" $ do
            let g1 = Graph (IntMap.fromList [(0, Branch 1 2), (1, Leaf 10), (2, Leaf 10)]) 0
                g2 = Graph (IntMap.fromList [(10, Branch 20 30), (20, Leaf 10), (30, Leaf 10)]) 10
            minimize IntMap.empty [] g1 `shouldBe` minimize IntMap.empty [] g2

        it "preserves terminal nodes" $ do
            let terminals = [-1, -2]
                nodes = IntMap.fromList
                    [ (0, Branch (-1) (-2))
                    ]
                g = Graph nodes 0
                g' = minimize IntMap.empty terminals g
            gNodes g' `shouldBe` IntMap.fromList [(0, Branch (-1) (-2))]

    describe "prune" $ do
        it "removes unreachable nodes" $ do
            let nodes = IntMap.fromList
                    [ (0, Leaf 10)
                    , (1, Leaf 20)
                    ]
                g = Graph nodes 0
                g' = prune g
            IntMap.member 1 (gNodes g') `shouldBe` False

        it "removes unreachable cycles" $ do
            let nodes = IntMap.fromList
                    [ (0, Leaf 10)
                    , (1, Branch 2 2)
                    , (2, Branch 1 1)
                    ]
                g = Graph nodes 0
                g' = prune g
            IntMap.member 1 (gNodes g') `shouldBe` False
            IntMap.member 2 (gNodes g') `shouldBe` False

    describe "merge" $ do
        it "merges two identical trees into one shared representation" $ do
            let g1 = Graph (IntMap.fromList [(0, Leaf 10)]) 0
                g2 = Graph (IntMap.fromList [(0, Leaf 10)]) 0
                (gMerged, r1, r2) = merge IntMap.empty [] g1 g2
            r1 `shouldBe` r2
            IntMap.size (gNodes gMerged) `shouldBe` 1

        it "merges different trees" $ do
            let g1 = Graph (IntMap.fromList [(0, Leaf 10)]) 0
                g2 = Graph (IntMap.fromList [(0, Leaf 20)]) 0
                (gMerged, r1, r2) = merge IntMap.empty [] g1 g2
            r1 `shouldNotBe` r2
            IntMap.size (gNodes gMerged) `shouldBe` 2

        it "merges graphs with overlapping cycles" $ do
            let g1 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                g2 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                (gMerged, r1, r2) = merge IntMap.empty [] g1 g2
            r1 `shouldBe` r2
            IntMap.size (gNodes gMerged) `shouldBe` 1

    describe "universalProduct" $ do
        it "computes the product of two simple graphs (Join-like)" $ do
            let g1 = Graph (IntMap.fromList [(0, Leaf 10)]) 0
                g2 = Graph (IntMap.fromList [(0, Leaf 20)]) 0
                -- Transition function that takes the max of two leaves
                combine i j () = case (IntMap.lookup i (gNodes g1), IntMap.lookup j (gNodes g2)) of
                    (Just (Leaf v1), Just (Leaf v2)) -> Leaf (max v1 v2)
                    _                                -> error "unexpected nodes"
                gRes = universalProduct combine IntMap.empty [] [()] g1 g2 ()

            gNodes gRes `shouldBe` IntMap.fromList [(0, Leaf 20)]

        it "handles cycles in product construction" $ do
            -- G1: 0 -> Branch 0 0
            -- G2: 0 -> Branch 0 0
            let g1 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                g2 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                combine i j () = Branch (i, j, ()) (i, j, ())
                gRes = universalProduct combine IntMap.empty [] [()] g1 g2 ()

            IntMap.size (gNodes gRes) `shouldBe` 1
            case IntMap.lookup (gRoot gRes) (gNodes gRes) of
                Just (Branch l r) -> do
                    l `shouldBe` gRoot gRes
                    r `shouldBe` gRoot gRes
                _ -> expectationFailure "Expected a Branch"

        it "terminates on complex cross-graph cycles" $ do
            -- G1: 0 -> Branch 1 1, 1 -> Leaf 10
            -- G2: 0 -> Branch 0 0
            let g1 = Graph (IntMap.fromList [(0, Branch 1 1), (1, Leaf 10)]) 0
                g2 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                combine i j () = case (getNode g1 i, getNode g2 j) of
                    (Branch l r, Branch l' r') -> Branch (l, l', ()) (r, r', ())
                    (Leaf v, _)                -> Leaf v
                    _                          -> error "mismatch"
                gRes = universalProduct combine IntMap.empty [] [()] g1 g2 ()
            -- Should terminate and produce a finite graph
            IntMap.size (gNodes gRes) `shouldSatisfy` (> 0)

        it "handles terminal nodes in universalProduct" $ do
            let g1 = Graph (IntMap.fromList [(0, Leaf 10)]) 0
                g2 = Graph (IntMap.fromList [(0, Leaf 20)]) 0
                terminals = [-1]
                combine i j () = case (i, j) of
                    (-1, _) -> Leaf (-1)
                    (_, -1) -> Leaf (-1)
                    _       -> Branch (i, -1, ()) (j, -1, ())
                -- The universe should include (-1, -1, ()) and others.
                gRes = universalProduct combine IntMap.empty terminals [()] g1 g2 ()

            IntMap.size (gNodes gRes) `shouldSatisfy` (> 0)
            -- Note: In the current implementation, (-1, -1, ()) will be assigned a NEW positive ID.
            -- It will NOT be the terminal ID -1.
            let rootNode = fromMaybe (error "no root") $ IntMap.lookup (gRoot gRes) (gNodes gRes)
            case rootNode of
                Branch l r -> do
                    l `shouldSatisfy` (>= 0)
                    r `shouldSatisfy` (>= 0)
                _ -> expectationFailure "Expected a Branch"

        it "handles non-trivial state transitions in universalProduct" $ do
            let g1 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                g2 = Graph (IntMap.fromList [(0, Branch 0 0)]) 0
                -- Different structure for different states to avoid minimization merging them
                combine i j 0 = Branch (i, j, 1) (i, j, 1)
                combine _ _ _ = Leaf 42
                gRes = universalProduct combine IntMap.empty [] [0, 1] g1 g2 (0 :: Int)
            -- Node 0: Branch Node1 Node1
            -- Node 1: Leaf 42
            IntMap.size (gNodes gRes) `shouldBe` 2

    describe "properties" $ do
        it "minimize is idempotent" $ property $ \(g :: Graph TestF) ->
            minimize IntMap.empty [] (minimize IntMap.empty [] g) == minimize IntMap.empty [] g

        it "universalProduct is commutative" $ property $ \(g1 :: Graph TestF) (g2 :: Graph TestF) ->
            let combine i j () = case (getNode g1 i, getNode g2 j) of
                    (Leaf v1, Leaf v2)         -> Leaf (max v1 v2)
                    (Branch l r, Branch l' r') -> Branch (l, l', ()) (r, r', ())
                    (Leaf v1, _)               -> Leaf v1
                    (_, Leaf v2)               -> Leaf v2
                g12 = universalProduct combine IntMap.empty [] [()] g1 g2 ()
                swapTriple (i', j', s') = (j', i', s')
                g21 = universalProduct (\j i s -> swapTriple <$> combine i j s) IntMap.empty [] [()] g2 g1 ()
            in minimize IntMap.empty [] g12 == minimize IntMap.empty [] g21

        it "universalProduct is associative" $ property $ \(g1 :: Graph TestF) (g2 :: Graph TestF) (g3 :: Graph TestF) ->
            let combine12 i j () = case (getNode g1 i, getNode g2 j) of
                    (Leaf v1, Leaf v2)       -> Leaf (max v1 v2)
                    (Branch _ _, Branch _ _) -> Branch (i, j, ()) (i, j, ())
                    (Leaf v1, _)             -> Leaf v1
                    (_, Leaf v2)             -> Leaf v2
                g12 = universalProduct combine12 IntMap.empty [] [()] g1 g2 ()

                combine12_3 i12 k () =
                    case (getNode g12 i12, getNode g3 k) of
                        (Leaf v12, Leaf v3) -> Leaf (max v12 v3)
                        (Branch _ _, Branch _ _) -> Branch (i12, k, ()) (i12, k, ())
                        (Leaf v12, _) -> Leaf v12
                        (_, Leaf v3) -> Leaf v3
                g12_3 = universalProduct combine12_3 IntMap.empty [] [()] g12 g3 ()

                combine23 j k () = case (getNode g2 j, getNode g3 k) of
                    (Leaf v2, Leaf v3)       -> Leaf (max v2 v3)
                    (Branch _ _, Branch _ _) -> Branch (j, k, ()) (j, k, ())
                    (Leaf v2, _)             -> Leaf v2
                    (_, Leaf v3)             -> Leaf v3
                g23 = universalProduct combine23 IntMap.empty [] [()] g2 g3 ()

                combine1_23 i j23 () =
                    case (getNode g1 i, getNode g23 j23) of
                        (Leaf v1, Leaf v23) -> Leaf (max v1 v23)
                        (Branch _ _, Branch _ _) -> Branch (i, j23, ()) (i, j23, ())
                        (Leaf v1, _) -> Leaf v1
                        (_, Leaf v23) -> Leaf v23
                g1_23 = universalProduct combine1_23 IntMap.empty [] [()] g1 g23 ()

            in minimize IntMap.empty [] g12_3 == minimize IntMap.empty [] g1_23

        it "merges a regular node into a structured terminal if bisimilar" $ do
            -- Terminal -1 has structure Leaf 10
            let termStructs = IntMap.fromList [(-1, Leaf 10)]
                -- Graph has a regular node 0 with structure Leaf 10
                g = Graph (IntMap.fromList [(0, Leaf 10)]) 0
                gMin = minimize termStructs [] g
            -- Root should now be -1
            gRoot gMin `shouldBe` (-1)
            IntMap.null (gNodes gMin) `shouldBe` True

  where
    getNode g i = fromMaybe (error $ "getNode " ++ show i) $ IntMap.lookup i (gNodes g)
