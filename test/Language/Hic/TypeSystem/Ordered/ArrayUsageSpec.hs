{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Ordered.ArrayUsageSpec (spec) where

import           Data.Map.Strict                                 (Map)
import qualified Data.Map.Strict                                 as Map
import qualified Data.Set                                        as Set
import           Language.Hic.TestUtils                          (mustParse)
import           Language.Hic.TypeSystem.Ordered.ArrayUsage
import qualified Language.Hic.TypeSystem.Ordered.HotspotAnalysis as GSA
import           Test.Hspec

spec :: Spec
spec = do
    it "identifies homogeneous local arrays" $ do
        prog <- mustParse ["void f() { int a[10]; int i = 0; a[i] = 1; }"]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (LocalArray "f" "a") (aurFlavors res) `shouldBe` Just FlavorHomogeneous

    it "identifies heterogeneous local arrays" $ do
        prog <- mustParse ["void f() { int a[10]; a[0] = 1; a[1] = 2; }"]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (LocalArray "f" "a") (aurFlavors res) `shouldBe` Just FlavorHeterogeneous

    it "identifies mixed access as mixed" $ do
        prog <- mustParse ["void f() { int a[10]; int i = 0; a[0] = 1; a[i] = 2; }"]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (LocalArray "f" "a") (aurFlavors res) `shouldBe` Just FlavorMixed

    it "tracks struct member arrays across functions" $ do
        prog <- mustParse
            [ "struct Registry { int h[10]; };"
            , "void set(struct Registry *r, int i) { r->h[i] = 1; }"
            , "void f(struct Registry *r) { r->h[0] = 2; }"
            ]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (MemberArray "Registry" "h") (aurFlavors res) `shouldBe` Just FlavorMixed

    it "distinguishes between different struct members" $ do
        prog <- mustParse
            [ "struct My_Struct { int a[10]; int b[10]; };"
            , "void f(struct My_Struct *s) { s->a[0] = 1; s->b[1] = 2; }"
            ]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (MemberArray "My_Struct" "a") (aurFlavors res) `shouldBe` Just FlavorHeterogeneous
        Map.lookup (MemberArray "My_Struct" "b") (aurFlavors res) `shouldBe` Just FlavorHeterogeneous

    it "handles hexadecimal indices" $ do
        prog <- mustParse ["void f() { int a[10]; a[0x1] = 1; a[0x2] = 2; }"]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (LocalArray "f" "a") (aurFlavors res) `shouldBe` Just FlavorHeterogeneous
        Map.lookup (LocalArray "f" "a") (aurAccesses res) `shouldBe` Just (Set.fromList [Just 1, Just 2])

    it "handles nested struct member arrays" $ do
        prog <- mustParse
            [ "struct Inner { int h[10]; };"
            , "struct Outer { struct Inner in; };"
            , "void f(struct Outer *s) { s->in.h[0] = 1; }"
            ]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        Map.lookup (MemberArray "Inner" "h") (aurFlavors res) `shouldBe` Just FlavorHeterogeneous

    it "handles arrays accessed via pointer to struct member" $ do
        prog <- mustParse
            [ "struct My_Struct { int h[10]; };"
            , "void f(struct My_Struct *s) { int *p = s->h; p[0] = 1; }"
            ]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        let res = runArrayUsageAnalysis ts prog
        -- Currently we don't track pointers to arrays, so p[0] might be missed
        -- or identified as LocalArray "f" "p".
        Map.lookup (LocalArray "f" "p") (aurFlavors res) `shouldBe` Just FlavorHeterogeneous
