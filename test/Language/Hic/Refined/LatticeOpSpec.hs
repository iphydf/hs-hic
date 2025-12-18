{-# LANGUAGE OverloadedStrings #-}

module Language.Hic.Refined.LatticeOpSpec (spec) where

import           Language.Hic.Refined.Arbitrary ()
import           Language.Hic.Refined.LatticeOp
import           Test.Hspec
import           Test.Hspec.QuickCheck          (prop)

spec :: Spec
spec = do
    describe "applyVariance" $ do
        it "preserves polarity for Covariant" $ do
            applyVariance Covariant PJoin `shouldBe` PJoin
            applyVariance Covariant PMeet `shouldBe` PMeet

        it "flips polarity for Contravariant" $ do
            applyVariance Contravariant PJoin `shouldBe` PMeet
            applyVariance Contravariant PMeet `shouldBe` PJoin

        it "returns PMeet for Invariant in both phases" $ do
            applyVariance Invariant PMeet `shouldBe` PMeet
            applyVariance Invariant PJoin `shouldBe` PMeet

        prop "applying Covariant is identity" $ \p ->
            applyVariance Covariant p == p

        prop "applying Contravariant is flipPol" $ \p ->
            applyVariance Contravariant p == flipPol p

    describe "flipPol" $ do
        it "flips PJoin to PMeet" $ do
            flipPol PJoin `shouldBe` PMeet
        it "flips PMeet to PJoin" $ do
            flipPol PMeet `shouldBe` PJoin

        prop "flipPol is its own inverse" $ \p ->
            flipPol (flipPol p) == p
