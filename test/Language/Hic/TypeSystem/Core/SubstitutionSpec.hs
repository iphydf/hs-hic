{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Core.SubstitutionSpec (spec) where

import           Test.Hspec

import           Data.Map.Strict                           (Map)
import qualified Data.Map.Strict                           as Map
import qualified Language.Cimple                           as C
import           Language.Hic.TypeSystem.Core.Base         (StdType (..),
                                                            TemplateId (..),
                                                            TypeDescr (..),
                                                            pattern BuiltinType,
                                                            pattern FullTemplate,
                                                            pattern Template)
import           Language.Hic.TypeSystem.Core.Substitution

spec :: Spec
spec = do
    let l = C.L (C.AlexPn 0 0 0) C.IdVar "f"
    let t0 = Template (TIdSolver 0 Nothing) Nothing
    let ft0 = FullTemplate (TIdSolver 0 Nothing) Nothing
    let s2 = BuiltinType S32Ty

    describe "substituteType" $ do
        it "replaces a template with its binding" $ do
            let bindings = Map.fromList [(ft0, s2)]
            substituteType bindings t0 `shouldBe` s2

        it "leaves unbound templates alone" $ do
            let bindings = Map.empty
            substituteType bindings t0 `shouldBe` t0

    describe "substituteDescr" $ do
        it "substitutes in a FuncDescr" $ do
            let bindings = Map.fromList [(ft0, s2)]
            let descr = FuncDescr l [] t0 [t0]
            let expected = FuncDescr l [] s2 [s2]
            substituteDescr bindings descr `shouldBe` expected

    describe "substituteTypeSystem" $ do
        it "substitutes across the whole type system" $ do
            let bindings = Map.fromList [(ft0, s2)]
            let ts = Map.fromList [("f", FuncDescr l [] t0 [t0])]
            let expected = Map.fromList [("f", FuncDescr l [] s2 [s2])]
            substituteTypeSystem bindings ts `shouldBe` expected
