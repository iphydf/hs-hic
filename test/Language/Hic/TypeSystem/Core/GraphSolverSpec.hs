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
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                graph = Map.singleton t1 (fromTys [Pointer (Template (ftId t1) (ftIndex t1))])
            -- Result is an equi-recursive type: Pointer back to itself via TIdRec 0
            solveGraph graph t1 `shouldBe` Pointer (Template (TIdRec 0) Nothing)

        it "merges multiple structural requirements (meet)" $ do
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                graph = Map.singleton t1 (fromTys [TS.Nonnull (Template (ftId t1) (ftIndex t1)), Pointer (Template (ftId t1) (ftIndex t1))])
            -- Meet of Nonnull(T) and Pointer(T) produces Pointer(T) (Pointer is more specific)
            solveGraph graph t1 `shouldBe` Pointer (Template (TIdRec 0) Nothing)

        it "resolves mutually recursive templates using solveAll" $ do
            let t1 = FullTemplate (TIdSolver 1 Nothing) Nothing
                t2 = FullTemplate (TIdSolver 2 Nothing) Nothing
                graph = Map.fromList
                    [ (t1, fromTys [Pointer (Template (ftId t2) (ftIndex t2))])
                    , (t2, fromTys [Pointer (Template (ftId t1) (ftIndex t1))])
                    ]
                resolved = solveAll graph [t1, t2]
            -- Each resolves to Pointer(TIdRec 0): t1 -> Pointer(t2) -> Pointer(Pointer(t1)) -> cycle at depth 0
            fmap TG.toTypeInfo (Map.lookup t1 resolved) `shouldBe` Just (Pointer (Template (TIdRec 0) Nothing))
            fmap TG.toTypeInfo (Map.lookup t2 resolved) `shouldBe` Just (Pointer (Template (TIdRec 0) Nothing))

        describe "properties" $ do
            it "satisfies all constraints (Soundness)" $ property $
                \(graph_info :: Map (FullTemplate 'Local) (Set (TS.TypeInfo 'Local))) ->
                        let graph = Map.map (Set.map TG.fromTypeInfo) graph_info
                            keys = Map.keys graph
                            solved_g = solveAll graph keys
                            solved = Map.map TG.toTypeInfo solved_g
                            check ft requirements =
                                let solution = Map.findWithDefault (Template (ftId ft) (ftIndex ft)) ft solved
                                    appliedReqs = map (applyBindings solved) (Set.toList requirements)
                                    failures = filter (not . (`subtypeOf` solution)) appliedReqs
                                in case failures of
                                    [] -> property True
                                    (f:_) -> counterexample ("ft: " ++ show ft)
                                           . counterexample ("solution: " ++ show (TS.stripLexemes solution))
                                           . counterexample ("failing req: " ++ show (TS.stripLexemes f))
                                           $ property False
                        in conjoin (map (uncurry check) (Map.toList graph_info))

            it "is idempotent" $ property $ \(graph_info :: Map (FullTemplate 'Local) (Set (TS.TypeInfo 'Local))) ->
                        let graph = Map.map (Set.map TG.fromTypeInfo) graph_info
                            keys = Map.keys graph
                            origKeys = Map.keysSet graph
                            solved1 = solveAll graph keys
                            -- Construct a new graph from the solved results, restricted
                            -- to original keys.  External templates get synthetic
                            -- Template(self) entries that are placeholders, not real
                            -- solutions — feeding them back creates spurious cycles.
                            graph2 = Map.map Set.singleton (Map.restrictKeys solved1 origKeys)
                            solved2 = solveAll graph2 keys
                            restrict m = Map.restrictKeys m origKeys
                        in counterexample ("solved1: " ++ show (Map.map TG.toTypeInfo (restrict solved1))
                                        ++ "\nsolved2: " ++ show (Map.map TG.toTypeInfo (restrict solved2)))
                           (restrict solved1 == restrict solved2)

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
