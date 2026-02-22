{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.TypeSystem.Core.Transition.VarianceSpec (spec) where

import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           Language.Hic.TypeSystem.Core.Qualification       (Constness (..),
                                                                   Nullability (..),
                                                                   Ownership (..),
                                                                   QualState (..),
                                                                   allowCovariance,
                                                                   stepQual)
import           Language.Hic.TypeSystem.Core.Transition.Types
import           Language.Hic.TypeSystem.Core.Transition.Variance

spec :: Spec
spec = do
    describe "getTargetState" $ do
        let terminals = (0 :: Int, 1 :: Int)
        let bot = 0
        let top = 1
        let getQuals = const (QNonnull', QNonOwned', QMutable')

        describe "Lattice Identity (Neutrality)" $ do
            prop "joining with terminal does not force const at top level" $ \ (c :: Constness) (child :: Int) ->
                let ps = ProductState PJoin QualTop QualTop False
                    (ps', _) = getTargetState ps terminals getQuals c c child bot
                in psForceConst ps' `shouldBe` False

            it "joining with terminal does not force const in invariant context" $ do
                let ps = ProductState PJoin QualUnshielded QualUnshielded False
                let (ps', _) = getTargetState ps terminals getQuals QMutable' QMutable' 10 bot
                psForceConst ps' `shouldBe` False

            prop "meeting with terminal does not force const" $ \qL qR (c :: Constness) (child :: Int) ->
                let ps = ProductState PMeet qL qR False
                    (ps', _) = getTargetState ps terminals getQuals c c child top
                in psForceConst ps' `shouldBe` False

        describe "Sound LUB Discovery (Strict Rules)" $ do
            it "does not force const when concrete targets differ at top level (LUB is structural)" $ do
                let ps = ProductState PJoin QualTop QualTop False
                let (ps', can) = getTargetState ps terminals getQuals QMutable' QMutable' 10 20
                psForceConst ps' `shouldBe` False
                can `shouldBe` True

            it "refuses to join when concrete targets differ in invariant context" $ do
                let ps = ProductState PJoin QualUnshielded QualUnshielded False
                let (ps', can) = getTargetState ps terminals getQuals QMutable' QMutable' 10 20
                psForceConst ps' `shouldBe` False
                can `shouldBe` False

        describe "Structural Persistence" $ do
            prop "canJoin is True for Meet" $ \qL qR (cL :: Constness) (cR :: Constness) (tL :: Int) (tR :: Int) ->
                let ps = ProductState PMeet qL qR False
                    (_, can) = getTargetState ps terminals getQuals cL cR tL tR
                in can `shouldBe` True

            prop "canJoin is only True for Join if covariance is allowed, targets match, or one is identity" $ \pol qL qR (cL :: Constness) (cR :: Constness) (tL :: Int) (tR :: Int) ->
                let ps = ProductState pol qL qR False
                    (_, can) = getTargetState ps terminals getQuals cL cR tL tR
                    isIdentity t = t == (if pol == PJoin then bot else top)
                    isNeutral = isIdentity tL || isIdentity tR
                in if pol == PMeet || isNeutral || tL == tR || allowCovariance qL || allowCovariance qR
                   then can `shouldBe` True
                   else can `shouldBe` False

    describe "C11 Subtyping (Const-Shielding)" $ do
        it "allows covariance on the side that is const in PMeet" $ do
            let terminals = (0 :: Int, 1 :: Int)
            let ps = ProductState PMeet QualTop QualTop False
            let getQuals i = if i == 20 then (QNonnull', QNonOwned', QConst') else (QNonnull', QNonOwned', QMutable')
            let (ps', _) = getTargetState ps terminals getQuals QMutable' QMutable' 10 20
            psQualR ps' `shouldBe` QualLevel1Const
            psQualL ps' `shouldBe` QualLevel1Mutable

