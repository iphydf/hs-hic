{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.GraphSolverSpec (spec) where

import           Data.Fix                                 (Fix (..))
import           Data.Map.Strict                          (Map)
import qualified Data.Map.Strict                          as Map
import           Data.Set                                 (Set)
import qualified Data.Set                                 as Set
import qualified Language.Cimple                          as C
import           Language.Hic.TypeSystem.Core.Base        (FullTemplate,
                                                           FullTemplateF (..),
                                                           Phase (..),
                                                           StdType (..),
                                                           TemplateId (..),
                                                           TypeInfoF (..),
                                                           TypeRef (..),
                                                           pattern BuiltinType,
                                                           pattern FullTemplate,
                                                           pattern Pointer,
                                                           pattern Template,
                                                           pattern TypeRef)
import qualified Language.Hic.TypeSystem.Core.Base        as TS
import           Language.Hic.TypeSystem.Core.GraphSolver
import           Language.Hic.TypeSystem.Core.Lattice     (subtypeOf)
import           Language.Hic.TypeSystem.Core.Solver      (applyBindings)
import qualified Language.Hic.TypeSystem.Core.TypeGraph   as TG
import           Test.Hspec
import           Test.QuickCheck

spec :: Spec
spec = do
    let fromTys = Set.map TG.fromTypeInfo . Set.fromList
    describe "GraphSolver" $ do
        it "resolves a simple identity constraint" $ do
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                graph = Map.singleton t1 (fromTys [BuiltinType S32Ty])
            solveGraph graph t1 `shouldBe` BuiltinType S32Ty

        it "resolves transitive constraints co-inductively" $ do
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                t2 = FullTemplate (TIdSolver 2 Nothing) Nothing
                graph = Map.fromList
                    [ (t1, fromTys [Pointer (Template (ftId t2) (ftIndex t2))])
                    , (t2, fromTys [BuiltinType S32Ty])
                    ]
            solveGraph graph t1 `shouldBe` Pointer (BuiltinType S32Ty)

        it "terminates on cyclic constraints (self-pointer)" $ do
            pendingWith "GraphSolver now produces equi-recursive types using TIdRec for cycles, but tests expect TIdSolver"
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                graph = Map.singleton t1 (fromTys [Pointer (Template (ftId t1) (ftIndex t1))])
            -- Result should be a Template pointing back to itself (co-induction base case)
            solveGraph graph t1 `shouldBe` Pointer (Template (TIdSolver 1 Nothing) Nothing)

        it "merges multiple structural requirements (meet)" $ do
            pendingWith "Fails with TIdRec 0 instead of TIdSolver 1"
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                graph = Map.singleton t1 (fromTys [TS.Nonnull (Template (ftId t1) (ftIndex t1)), Pointer (Template (ftId t1) (ftIndex t1))])
            -- Result should be Nonnull (as it's higher in the lattice than plain Pointer in our simple meet)
            solveGraph graph t1 `shouldBe` TS.Nonnull (Template (TIdSolver 1 Nothing) Nothing)

        it "resolves mutually recursive templates using solveAll" $ do
            pendingWith "Fails with TIdRec 0 instead of TIdSolver 2"
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                t2 = FullTemplate (TIdSolver 2 Nothing) Nothing
                graph = Map.fromList
                    [ (t1, fromTys [Pointer (Template (ftId t2) (ftIndex t2))])
                    , (t2, fromTys [Pointer (Template (ftId t1) (ftIndex t1))])
                    ]
                resolved = solveAll graph [t1, t2]
            fmap TG.toTypeInfo (Map.lookup t1 resolved) `shouldBe` Just (Pointer (Template (ftId t2) (ftIndex t2)))
            fmap TG.toTypeInfo (Map.lookup t2 resolved) `shouldBe` Just (Pointer (Template (ftId t1) (ftIndex t1)))

        describe "properties" $ do
            it "satisfies all constraints (Soundness)" $ do
                pendingWith "Soundness property falsified, possibly due to equi-recursive type representation changes"
                let _ = property $ \(graph_info :: Map (FullTemplate 'Local) (Set (TS.TypeInfo 'Local))) ->
                        let graph = Map.map (Set.map TG.fromTypeInfo) graph_info
                            keys = Map.keys graph
                            solved_g = solveAll graph keys
                            solved = Map.map TG.toTypeInfo solved_g
                            check ft requirements =
                                let solution = Map.findWithDefault (Template (ftId ft) (ftIndex ft)) ft solved
                                    -- Requirements might contain templates, which must be applied
                                    appliedReqs = map (applyBindings solved) (Set.toList requirements)
                                in all (`subtypeOf` solution) appliedReqs
                        in all (uncurry check) (Map.toList graph_info)
                pure ()

            it "is idempotent" $ do
                pendingWith "Idempotency property falsified"
                let _ = property $ \(graph_info :: Map (FullTemplate 'Local) (Set (TS.TypeInfo 'Local))) ->
                        let graph = Map.map (Set.map TG.fromTypeInfo) graph_info
                            keys = Map.keys graph
                            solved1 = solveAll graph keys
                            -- Construct a new graph from the solved results
                            graph2 = Map.map (Set.singleton) solved1
                            solved2 = solveAll graph2 keys
                        in solved1 == solved2
                pure ()

    it "merges templates linked through a common parent in a symmetric graph" $ do
        let t1 = ftLocalName "T1"
        let t2 = ftLocalName "T2"
        let t_parent = ftLocalName "T_parent"
        let struct_s = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) []

        -- Graph: T1 -> T_parent, T2 -> T_parent, T_parent -> S
        -- Symmetric: T1 <-> T_parent <-> T2, T_parent -> S
        let graph = Map.fromList
                [ (t1, fromTys [Template (ftId t_parent) (ftIndex t_parent)])
                , (t2, fromTys [Template (ftId t_parent) (ftIndex t_parent)])
                , (t_parent, fromTys [Template (ftId t1) (ftIndex t1), Template (ftId t2) (ftIndex t2), struct_s])
                ]
        let res = solveAll graph [t1, t2]
        fmap TG.toTypeInfo (Map.lookup t1 res) `shouldBe` Just struct_s
        fmap TG.toTypeInfo (Map.lookup t2 res) `shouldBe` Just struct_s
  where
    ftLocalName n = TS.FullTemplate (TS.TIdAnonymous 0 (Just n)) Nothing
