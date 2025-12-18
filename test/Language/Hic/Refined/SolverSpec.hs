{-# LANGUAGE GADTs               #-}
{-# LANGUAGE LambdaCase          #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Refined.SolverSpec (spec) where

import           Data.Either                      (isLeft, isRight)
import           Data.IntMap.Strict               (IntMap)
import qualified Data.IntMap.Strict               as IntMap
import           Data.Map.Strict                  (Map)
import qualified Data.Map.Strict                  as Map
import           Data.Word                        (Word32)
import           Language.Cimple                  (AlexPosn (..), Lexeme (..),
                                                   LexemeClass (..))
import           Language.Hic.Refined.Arbitrary   (dummyL)
import           Language.Hic.Refined.Context     (MappingRefinements (..),
                                                   emptyContext, getRefinement,
                                                   mrRefinements)
import           Language.Hic.Refined.LatticeOp   (Polarity (..), Variance (..))
import           Language.Hic.Refined.PathContext (PathContext (..))
import           Language.Hic.Refined.Registry    (Registry (..),
                                                   TypeDefinition (..))
import           Language.Hic.Refined.Solver      (Constraint (..), solve)
import           Language.Hic.Refined.State       (ProductState (..))
import           Language.Hic.Refined.Transition  (variableKey)
import           Language.Hic.Refined.Types       (AnyRigidNodeF (..),
                                                   LatticePhase (..),
                                                   ObjectStructure (..),
                                                   Quals (..), RigidNodeF (..),
                                                   StdType (..),
                                                   TemplateId (..),
                                                   TerminalNode (..))
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

-- | A generated random type graph.
data TypeGraph = TypeGraph
    { tgNodes :: Map Word32 (AnyRigidNodeF TemplateId Word32)
    } deriving (Show)

instance Arbitrary TypeGraph where
    arbitrary = sized $ \n -> do
        let numNodes = max 5 (n `div` 2)
        -- Generate random structures for nodes 2..numNodes
        -- Child IDs are restricted to 0..numNodes to ensure a closed graph
        nodeList <- vectorOf numNodes (arbitrary :: Gen (AnyRigidNodeF TemplateId Word32))
        let remap (AnyRigidNodeF node) = AnyRigidNodeF (fmap (\i -> i `mod` (fromIntegral numNodes + 2)) node)
        let nodes = Map.fromList $ zip [2..] (map remap nodeList)
        return $ TypeGraph $ Map.insert 0 (AnyRigidNodeF (RTerminal SBottom)) $
                             Map.insert 1 (AnyRigidNodeF (RTerminal SAny)) $
                             Map.insert 2 (AnyRigidNodeF (RTerminal SConflict)) nodes

spec :: Spec
spec = do
    let emptyReg = Registry Map.empty
    let terminals = (0, 1, 2, 0)
    let baseNodes = Map.fromList
            [ (0, AnyRigidNodeF (RTerminal SBottom))
            , (1, AnyRigidNodeF (RTerminal SAny))
            , (2, AnyRigidNodeF (RTerminal SConflict))
            , (3, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
            , (4, AnyRigidNodeF (RObject (VBuiltin F32Ty) (Quals False False)))
            ]
    let emptyPathCtx = PathContext Map.empty Map.empty

    describe "Unit Tests" $ do
        it "solves simple compatible types" $ do
            let constraints = [CSubtype 3 3 PMeet emptyContext emptyPathCtx 0 0 Nothing ""]
            let res = solve emptyReg baseNodes constraints terminals
            res `shouldSatisfy` isRight

        it "reports conflict for incompatible built-ins" $ do
            let constraints = [CSubtype 3 4 PMeet emptyContext emptyPathCtx 0 0 Nothing ""]
            let res = solve emptyReg baseNodes constraints terminals
            res `shouldSatisfy` isLeft

        it "refines a polymorphic variable to a concrete type" $ do
            let nodes = Map.insert 5 (AnyRigidNodeF (RObject (VVar (TIdName "T") Nothing) (Quals False False))) baseNodes
            let constraints = [CSubtype 5 3 PMeet emptyContext emptyPathCtx 0 0 Nothing ""]
            case solve emptyReg nodes constraints terminals of
                Right refs -> IntMap.null (mrRefinements refs) `shouldBe` False
                Left _     -> expectationFailure "Solver should have succeeded"

        it "detects refinement conflict through a shared variable" $ do
            -- T <: int32 and T <: float32  => Conflict
            let nodes = Map.insert 5 (AnyRigidNodeF (RObject (VVar (TIdName "T") Nothing) (Quals False False))) baseNodes
            let constraints =
                    [ CSubtype 5 3 PMeet emptyContext emptyPathCtx 0 0 Nothing ""
                    , CSubtype 5 4 PMeet emptyContext emptyPathCtx 0 0 Nothing ""
                    ]
            let res = solve emptyReg nodes constraints terminals
            res `shouldSatisfy` isLeft

        it "terminates on a refinement cycle between variables" $ do
            -- T1 <: T2 and T2 <: T1
            let nodes = Map.fromList
                    [ (0, AnyRigidNodeF (RTerminal SBottom))
                    , (1, AnyRigidNodeF (RTerminal SAny))
                    , (2, AnyRigidNodeF (RTerminal SConflict))
                    , (5, AnyRigidNodeF (RObject (VVar (TIdName "T1") Nothing) (Quals False False)))
                    , (6, AnyRigidNodeF (RObject (VVar (TIdName "T2") Nothing) (Quals False False)))
                    ]
            let constraints =
                    [ CSubtype 5 6 PMeet emptyContext emptyPathCtx 0 0 Nothing ""
                    , CSubtype 6 5 PMeet emptyContext emptyPathCtx 0 0 Nothing ""
                    ]
            within 1000000 $ do
                let res = solve emptyReg nodes constraints terminals
                res `shouldSatisfy` isRight

        it "handles existential synchronization in joins" $ do
            -- Joint of two identical existentials should be successful
            let nodes = Map.fromList
                    [ (0, AnyRigidNodeF (RTerminal SBottom))
                    , (1, AnyRigidNodeF (RTerminal SAny))
                    , (2, AnyRigidNodeF (RTerminal SConflict))
                    , (3, AnyRigidNodeF (RObject (VExistential [TIdName "T"] 4) (Quals False False)))
                    , (4, AnyRigidNodeF (RObject (VVar (TIdName "T") Nothing) (Quals False False)))
                    ]
            let constraints = [CSubtype 3 3 PJoin emptyContext emptyPathCtx 0 0 Nothing ""]
            let res = solve emptyReg nodes constraints terminals
            res `shouldSatisfy` isRight

        it "isolates calls using CInherit (Rank-1 Poly-variance)" $ do
            -- T  : Global template variable
            -- T1 : Fresh variable for call 1
            -- T2 : Fresh variable for call 2
            let nodes = Map.fromList
                    [ (0, AnyRigidNodeF (RTerminal SBottom))
                    , (1, AnyRigidNodeF (RTerminal SAny))
                    , (2, AnyRigidNodeF (RTerminal SConflict))
                    , (3, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))) -- Int
                    , (4, AnyRigidNodeF (RObject (VBuiltin F32Ty) (Quals False False))) -- Float
                    , (5, AnyRigidNodeF (RObject (VVar (TIdName "T") Nothing) (Quals False False)))
                    , (6, AnyRigidNodeF (RObject (VVar (TIdName "T1") Nothing) (Quals False False)))
                    , (7, AnyRigidNodeF (RObject (VVar (TIdName "T2") Nothing) (Quals False False)))
                    ]
            -- Use CInherit: Fresh variables inherit from Global, but don't leak back.
            let constraints =
                    [ CSubtype 6 3 PMeet emptyContext emptyPathCtx 0 0 Nothing "" -- T1 <: Int
                    , CSubtype 7 4 PMeet emptyContext emptyPathCtx 0 0 Nothing "" -- T2 <: Float
                    , CInherit 6 5 Nothing "" -- T1 inherits from T
                    , CInherit 7 5 Nothing "" -- T2 inherits from T
                    ]
            case solve emptyReg nodes constraints terminals of
                Right refs -> do
                    -- Check that T1 and T2 are refined, but T is not.
                    -- This proves that refinements only flow definition -> call-site.
                    let key1 = variableKey nodes 0 (TIdName "T1")
                    let key2 = variableKey nodes 0 (TIdName "T2")
                    let keyGlobal = variableKey nodes 0 (TIdName "T")
                    getRefinement key1 refs `shouldBe` Just 3 -- T1 refined to Int
                    getRefinement key2 refs `shouldBe` Just 4 -- T2 refined to Float
                    getRefinement keyGlobal refs `shouldBe` Nothing -- T remains polymorphic (no bleeding)
                Left _ -> expectationFailure "Solver should have succeeded"

    describe "Property Tests" $ do
        prop "terminates on any finite graph and constraints" $ \(tg :: TypeGraph) (constraints :: [Constraint]) ->
            -- Ensure constraints refer to valid nodes in the graph
            let maxId = fromIntegral (Map.size (tgNodes tg))
                validConstraints = map (\case
                    CSubtype l r p ctx path dL dR loc f -> CSubtype (l `mod` maxId) (r `mod` maxId) p ctx path dL dR loc f
                    CInherit l r loc f -> CInherit (l `mod` maxId) (r `mod` maxId) loc f) constraints
                numExistentials = length $ filter isExistential (Map.elems (tgNodes tg))
                isExistential (AnyRigidNodeF (RObject VExistential{} _)) = True
                isExistential _                                          = False
            in label ("Nodes: " ++ show (maxId `div` 5 * 5)) $
               label ("Existentials: " ++ show numExistentials) $
               within 1000000 $ -- 1 second timeout to catch infinite loops
                let res = solve emptyReg (tgNodes tg) validConstraints terminals
                in res `seq` True

        prop "is commutative: solve(C1, C2) == solve(C2, C1)" $ \(tg :: TypeGraph) (c1 :: Constraint) (c2 :: Constraint) ->
            let maxId = fromIntegral (Map.size (tgNodes tg))
                fixC (CSubtype l r p ctx path dL dR loc f) = CSubtype (l `mod` maxId) (r `mod` maxId) p ctx path dL dR loc f
                fixC (CInherit l r loc f) = CInherit (l `mod` maxId) (r `mod` maxId) loc f
                c1' = fixC c1
                c2' = fixC c2
                res12 = solve emptyReg (tgNodes tg) [c1', c2'] terminals
                res21 = solve emptyReg (tgNodes tg) [c2', c1'] terminals
            in case (res12, res21) of
                (Right refs12, Right refs21) -> mrRefinements refs12 === mrRefinements refs21
                (Left _, Left _)             -> property True
                _                            -> property False

        prop "is idempotent: solve(C, C) == solve(C)" $ \(tg :: TypeGraph) (c :: Constraint) ->
            let maxId = fromIntegral (Map.size (tgNodes tg))
                fixC (CSubtype l r p ctx path dL dR loc f) = CSubtype (l `mod` maxId) (r `mod` maxId) p ctx path dL dR loc f
                fixC (CInherit l r loc f) = CInherit (l `mod` maxId) (r `mod` maxId) loc f
                c' = fixC c
                res1 = solve emptyReg (tgNodes tg) [c'] terminals
                res2 = solve emptyReg (tgNodes tg) [c', c'] terminals
            in case (res1, res2) of
                (Right refs1, Right refs2) -> mrRefinements refs1 === mrRefinements refs2
                (Left _, Left _)           -> property True
                _                          -> property False

        prop "monotonicity: adding constraints only increases refinements" $ \(tg :: TypeGraph) (c1 :: Constraint) (c2 :: Constraint) ->
            let maxId = fromIntegral (Map.size (tgNodes tg))
                fixC (CSubtype l r p ctx path dL dR loc f) = CSubtype (l `mod` maxId) (r `mod` maxId) p ctx path dL dR loc f
                fixC (CInherit l r loc f) = CInherit (l `mod` maxId) (r `mod` maxId) loc f
                c1' = fixC c1
                c2' = fixC c2
                res1 = solve emptyReg (tgNodes tg) [c1'] terminals
                res12 = solve emptyReg (tgNodes tg) [c1', c2'] terminals
            in case (res1, res12) of
                (Right refs1, Right refs12) -> property $ all (\(k, v) -> IntMap.lookup k (mrRefinements refs12) == Just v) (IntMap.toList (mrRefinements refs1))
                _                           -> property True

    describe "Regression: Infinite Loops" $ do
        it "terminates on a self-referential existential cycle" $ do
            -- Node 3: ∃T. Node 4
            -- Node 4: struct { Node 3 *next; }
            let nodes = Map.fromList
                    [ (0, AnyRigidNodeF (RTerminal SBottom))
                    , (1, AnyRigidNodeF (RTerminal SAny))
                    , (2, AnyRigidNodeF (RTerminal SConflict))
                    , (3, AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0] 4) (Quals False False)))
                    , (4, AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "Loop")) [3]) (Quals False False)))
                    ]
            let constraints = [CSubtype 3 3 PJoin emptyContext (PathContext Map.empty Map.empty) 0 0 Nothing ""]
            within 1000000 $
                let res = solve emptyReg nodes constraints terminals
                in res `shouldSatisfy` isRight

    describe "Existential Promotion in Joins" $ do
        it "solves for a common existential supertype in a heterogeneous list" $ do
            -- My_Callback<int> <: ElementType
            -- My_Callback<float> <: ElementType
            -- Where ElementType should be promoted to exists T. My_Callback<T>
            let nodes = Map.fromList
                    [ (0, AnyRigidNodeF (RTerminal SBottom))
                    , (1, AnyRigidNodeF (RTerminal SAny))
                    , (2, AnyRigidNodeF (RTerminal SConflict))
                    , (3, AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
                    , (4, AnyRigidNodeF (RObject (VBuiltin F32Ty) (Quals False False)))
                    -- 10: My_Callback<int>
                    , (10, AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "My_Callback")) [3]) (Quals False False)))
                    -- 11: My_Callback<float>
                    , (11, AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "My_Callback")) [4]) (Quals False False)))
                    -- 12: ElementType (Placeholder variable)
                    , (12, AnyRigidNodeF (RObject (VVar (TIdName "T1") Nothing) (Quals False False)))
                    -- 20: exists T. My_Callback<T> (The expected supertype)
                    , (20, AnyRigidNodeF (RObject (VExistential [TIdDeBruijn 0] 21) (Quals False False)))
                    , (21, AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "My_Callback")) [22]) (Quals False False)))
                    , (22, AnyRigidNodeF (RObject (VVar (TIdDeBruijn 0) Nothing) (Quals False False)))
                    ]
            let reg = Registry $ Map.fromList
                    [ ("My_Callback", StructDef (dummyL "My_Callback") [(TIdParam PGlobal 0 Nothing, Invariant)] [])
                    ]
            let constraints =
                    [ CSubtype 10 12 PJoin emptyContext emptyPathCtx 0 0 Nothing ""
                    , CSubtype 11 12 PJoin emptyContext emptyPathCtx 0 0 Nothing ""
                    ]
            case solve reg nodes constraints terminals of
                Right refs -> do
                    -- T1 should be refined to something semantically equivalent to node 20
                    case getRefinement (variableKey nodes 0 (TIdName "T1")) refs of
                        Just rId -> do
                            -- In this test environment, the solver doesn't have a way to register new nodes
                            -- except through the teNodes map which is fixed.
                            -- This means findExistentialPromotion MUST find node 20.
                            rId `shouldBe` 20
                        Nothing -> expectationFailure "Variable E was not refined"
                Left _ -> expectationFailure "Solver should have succeeded"
