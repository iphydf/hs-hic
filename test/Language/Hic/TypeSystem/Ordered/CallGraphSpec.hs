{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Ordered.CallGraphSpec (spec) where

import           Data.List                                 (sort)
import qualified Data.Map.Strict                           as Map
import qualified Data.Set                                  as Set
import           Language.Hic.TestUtils                    (mustParse)
import           Language.Hic.TypeSystem.Ordered.CallGraph
import           Test.Hspec

spec :: Spec
spec = do
    it "identifies direct calls" $ do
        prog <- mustParse
            [ "void my_g();"
            , "void my_f() { my_g(); }"
            ]
        let res = runCallGraphAnalysis prog
        Map.lookup "my_f" (cgrDirectCalls res) `shouldBe` Just (Set.singleton "my_g")

    it "identifies self-recursion" $ do
        prog <- mustParse ["void my_f() { my_f(); }"]
        let res = runCallGraphAnalysis prog
        Map.lookup "my_f" (cgrDirectCalls res) `shouldBe` Just (Set.singleton "my_f")
        cgrSccs res `shouldBe` [Cyclic ["my_f"]]

    it "identifies mutual recursion" $ do
        prog <- mustParse
            [ "void my_g();"
            , "void my_f() { my_g(); }"
            , "void my_g() { my_f(); }"
            ]
        let res = runCallGraphAnalysis prog
        -- SCCs are returned in reverse topological order, but for a cycle it's one SCC
        case cgrSccs res of
            [Cyclic nodes] -> sort nodes `shouldBe` ["my_f", "my_g"]
            _              -> expectationFailure $ "Expected one Cyclic SCC, got: " ++ show (cgrSccs res)

    it "identifies multiple callers" $ do
        prog <- mustParse
            [ "void my_h();"
            , "void my_f() { my_h(); }"
            , "void my_g() { my_h(); }"
            ]
        let res = runCallGraphAnalysis prog
        Map.lookup "my_f" (cgrDirectCalls res) `shouldBe` Just (Set.singleton "my_h")
        Map.lookup "my_g" (cgrDirectCalls res) `shouldBe` Just (Set.singleton "my_h")

    it "handles nested calls" $ do
        prog <- mustParse
            [ "void my_h();"
            , "void my_g() { my_h(); }"
            , "void my_f() { my_g(); }"
            ]
        let res = runCallGraphAnalysis prog
        -- Data.Graph.stronglyConnComp returns SCCs in reverse topological order.
        -- So leaf should come first.
        cgrSccs res `shouldBe` [Acyclic "my_h", Acyclic "my_g", Acyclic "my_f"]

    it "ignores function pointer calls (for now)" $ do
        prog <- mustParse
            [ "typedef void my_ptr_cb();"
            , "void my_f(my_ptr_cb *my_ptr) { my_ptr(); }"
            ]
        let res = runCallGraphAnalysis prog
        Map.lookup "my_f" (cgrDirectCalls res) `shouldBe` Just Set.empty

    it "identifies calls in initializers" $ do
        prog <- mustParse ["int g(); void f() { int x = g(); }"]
        let res = runCallGraphAnalysis prog
        Map.lookup "f" (cgrDirectCalls res) `shouldBe` Just (Set.singleton "g")

    it "handles multiple calls to the same function" $ do
        prog <- mustParse ["void g(); void f() { g(); g(); }"]
        let res = runCallGraphAnalysis prog
        Map.lookup "f" (cgrDirectCalls res) `shouldBe` Just (Set.singleton "g")
