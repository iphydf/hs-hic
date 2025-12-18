{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Core.QualificationSpec (spec) where

import           Data.Set                                   (Set)
import qualified Data.Set                                   as Set
import           Language.Hic.Core.TypeSystem               (Qualifier (..))
import           Language.Hic.TypeSystem.Core.Qualification
import           Test.Hspec
import           Test.QuickCheck

spec :: Spec
spec = do
    describe "stepQual" $ do
        it "transitions from Top correctly" $ do
            stepQual QualTop True `shouldBe` QualLevel1Const
            stepQual QualTop False `shouldBe` QualLevel1Mutable

        it "transitions from Level1 correctly" $ do
            stepQual QualLevel1Const True `shouldBe` QualShielded
            stepQual QualLevel1Const False `shouldBe` QualUnshielded
            stepQual QualLevel1Mutable True `shouldBe` QualShielded
            stepQual QualLevel1Mutable False `shouldBe` QualUnshielded

        it "stays shielded if const" $ do
            stepQual QualShielded True `shouldBe` QualShielded
            stepQual QualShielded False `shouldBe` QualUnshielded

        it "stays unshielded" $ do
            stepQual QualUnshielded True `shouldBe` QualUnshielded
            stepQual QualUnshielded False `shouldBe` QualUnshielded

    describe "subtypeQuals" $ do
        it "is reflexive" $ property $ \(n, o, c) ->
            subtypeQuals (fromQuals n o c) (fromQuals n o c)

        it "handles Nullability" $ do
            subtypeQuals (fromQuals QNonnull' QNonOwned' QMutable') (fromQuals QUnspecified QNonOwned' QMutable') `shouldBe` True
            subtypeQuals (fromQuals QUnspecified QNonOwned' QMutable') (fromQuals QNullable' QNonOwned' QMutable') `shouldBe` True
            subtypeQuals (fromQuals QNonnull' QNonOwned' QMutable') (fromQuals QNullable' QNonOwned' QMutable') `shouldBe` True
            subtypeQuals (fromQuals QNullable' QNonOwned' QMutable') (fromQuals QNonnull' QNonOwned' QMutable') `shouldBe` False

        it "handles Constness" $ do
            subtypeQuals (fromQuals QUnspecified QNonOwned' QMutable') (fromQuals QUnspecified QNonOwned' QConst') `shouldBe` True
            subtypeQuals (fromQuals QUnspecified QNonOwned' QConst') (fromQuals QUnspecified QNonOwned' QMutable') `shouldBe` False

        it "handles Ownership" $ do
            subtypeQuals (fromQuals QUnspecified QNonOwned' QMutable') (fromQuals QUnspecified QOwned' QMutable') `shouldBe` True
            subtypeQuals (fromQuals QUnspecified QOwned' QMutable') (fromQuals QUnspecified QNonOwned' QMutable') `shouldBe` False

    describe "joinQuals" $ do
        it "picks the maximum element" $ do
            joinQuals (fromQuals QNonnull' QOwned' QMutable') (fromQuals QNullable' QNonOwned' QConst')
                `shouldBe` fromQuals QNullable' QOwned' QConst'

    describe "meetQuals" $ do
        it "picks the minimum element" $ do
            meetQuals (fromQuals QNonnull' QOwned' QMutable') (fromQuals QNullable' QNonOwned' QConst')
                `shouldBe` fromQuals QNonnull' QNonOwned' QMutable'
