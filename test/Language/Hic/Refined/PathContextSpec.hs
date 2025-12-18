{-# LANGUAGE OverloadedStrings #-}

module Language.Hic.Refined.PathContextSpec (spec) where

import qualified Data.Map.Strict                  as Map
import           Language.Hic.Refined.Arbitrary   ()
import           Language.Hic.Refined.PathContext
import           Test.Hspec
import           Test.Hspec.QuickCheck            (prop)

spec :: Spec
spec = do
    describe "SymbolicPath" $ do
        it "can represent a local variable" $ do
            let path = SymbolicPath (VarRoot "p") []
            spRoot path `shouldBe` VarRoot "p"
            spSteps path `shouldBe` []

        it "can represent field access" $ do
            let path = SymbolicPath (VarRoot "p") [FieldStep "tag"]
            spSteps path `shouldBe` [FieldStep "tag"]

        it "can represent nested access" $ do
            let path = SymbolicPath (VarRoot "p") [FieldStep "data", FieldStep "i"]
            spSteps path `shouldBe` [FieldStep "data", FieldStep "i"]

    describe "extendPath" $ do
        prop "increases length of steps by 1" $ \step path ->
            length (spSteps (extendPath step path)) == length (spSteps path) + 1

        prop "last step matches the added step" $ \step path ->
            last (spSteps (extendPath step path)) == step

    describe "simplifyPath" $ do
        it "follows a simple alias" $ do
            let aliases = Map.singleton "m2" (SymbolicPath (VarRoot "m1") [])
                path = SymbolicPath (VarRoot "m2") [FieldStep "f"]
            simplifyPath aliases path `shouldBe` SymbolicPath (VarRoot "m1") [FieldStep "f"]

        it "prepends steps from alias" $ do
            let aliases = Map.singleton "p" (SymbolicPath (VarRoot "obj") [FieldStep "ptr"])
                path = SymbolicPath (VarRoot "p") [FieldStep "val"]
            simplifyPath aliases path `shouldBe` SymbolicPath (VarRoot "obj") [FieldStep "ptr", FieldStep "val"]


