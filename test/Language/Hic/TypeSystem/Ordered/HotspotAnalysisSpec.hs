{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Ordered.HotspotAnalysisSpec (spec) where

import qualified Data.Map.Strict                                 as Map
import qualified Data.Set                                        as Set
import           Language.Hic.TestUtils                          (mustParse)
import           Language.Hic.TypeSystem.Ordered.HotspotAnalysis
import           Test.Hspec

spec :: Spec
spec = do
    it "identifies structs with void* as hotspots" $ do
        prog <- mustParse ["struct My_Struct { void *p; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Struct"]

    it "identifies structs with templates as hotspots" $ do
        -- Template is inferred for void* in our system
        prog <- mustParse ["struct My_Struct { void *p; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Struct"]

    it "identifies functions with void* as hotspots" $ do
        prog <- mustParse ["void my_f(void *p);"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [FunctionHotspot "my_f"]

    it "does not identify simple structs as hotspots" $ do
        prog <- mustParse ["struct My_Struct { int x; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.empty

    it "identifies unions with void* as hotspots" $ do
        prog <- mustParse ["union My_Union { void *p; int x; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Union"]

    it "identifies functions with generic return types as hotspots" $ do
        prog <- mustParse ["void *my_f(int x);"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [FunctionHotspot "my_f"]

    it "identifies structs with generic arrays as hotspots" $ do
        prog <- mustParse ["struct My_Struct { void *arr[10]; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Struct"]

    it "propagates hotspots through typedefs" $ do
        prog <- mustParse
            [ "typedef void *Generic;"
            , "struct My_Struct { Generic p; };"
            ]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Struct"]

    it "does not identify concrete pointers as hotspots" $ do
        prog <- mustParse
            [ "struct My_Struct { int *p; };"
            , "void my_f(int *p);"
            ]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.empty

    it "does not identify concrete typedefs as hotspots" $ do
        prog <- mustParse
            [ "typedef int My_Int;"
            , "typedef My_Int *My_Int_Ptr;"
            , "struct My_Struct { My_Int_Ptr p; };"
            , "void my_f(My_Int x);"
            ]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.empty

    it "does not identify forward declared concrete structs as hotspots" $ do
        prog <- mustParse
            [ "struct My_Struct;"
            , "void my_f(struct My_Struct *s);"
            , "struct My_Struct { int x; };"
            ]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.empty

    it "does not identify void functions or parameters as hotspots" $ do
        prog <- mustParse
            [ "void my_f(void);"
            , "void my_g();"
            ]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.empty

    it "handles complex nested generic types in hotspots" $ do
        prog <- mustParse
            [ "struct My_Struct { int x; };"
            , "void my_f(struct My_Struct *s);" -- Not generic
            , "void my_g_func(void *p);"   -- Generic
            , "struct My_G_struct { void **pp; };" -- Generic
            ]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [FunctionHotspot "my_g_func", StructHotspot "My_G_struct"]

    it "identifies deep generic pointers as hotspots" $ do
        prog <- mustParse ["typedef void *GenericPointer; struct My_Struct { GenericPointer **ppp; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Struct"]

    it "identifies structs with _Owned pointers as hotspots" $ do
        prog <- mustParse ["struct My_Struct { int *_Owned p; };"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [StructHotspot "My_Struct"]

    it "identifies functions with _Owned parameters as hotspots" $ do
        prog <- mustParse ["void my_f(int *_Owned p);"]
        let res = runGlobalStructuralAnalysis prog
        garHotspots res `shouldBe` Set.fromList [FunctionHotspot "my_f"]
