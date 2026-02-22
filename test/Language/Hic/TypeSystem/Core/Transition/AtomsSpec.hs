module Language.Hic.TypeSystem.Core.Transition.AtomsSpec (spec) where

import           Data.Functor                                  (void)
import           Test.Hspec
import           Test.Hspec.QuickCheck
import           Test.QuickCheck

import           Language.Hic.Core.TypeSystem                  (StdType (..))
import           Language.Hic.TypeSystem.Core.Qualification    (QualState (..))
import           Language.Hic.TypeSystem.Core.Transition.Atoms
import           Language.Hic.TypeSystem.Core.Transition.Types

spec :: Spec
spec = do
    describe "isIdentityFor" $ do
        it "treats Unconstrained as identity for Join" $
            isIdentityFor PJoin (RSpecial SUnconstrained) `shouldBe` True

        it "does not treat Conflict as identity for Join" $
            isIdentityFor PJoin (RSpecial SConflict) `shouldBe` False

        it "treats Conflict as identity for Meet" $
            isIdentityFor PMeet (RSpecial SConflict) `shouldBe` True

        it "does not treat Unconstrained as identity for Meet" $
            isIdentityFor PMeet (RSpecial SUnconstrained) `shouldBe` False

    describe "isZeroFor" $ do
        it "treats Conflict as zero for Join" $
            isZeroFor PJoin (RSpecial SConflict) `shouldBe` True

        it "treats Unconstrained as zero for Meet" $
            isZeroFor PMeet (RSpecial SUnconstrained) `shouldBe` True

    describe "mergeAtoms" $ do
        let psJoin = ProductState PJoin QualTop QualTop False
        let psJoinInv = ProductState PJoin QualUnshielded QualUnshielded False
        let psMeet = ProductState PMeet QualTop QualTop False
        let mergeAtoms' = mergeAtoms :: ProductState -> ValueStructure () () -> ValueStructure () () -> Maybe (ValueStructure () (), Bool, Bool)

        describe "VBuiltin" $ do
            it "joins identical builtins" $
                mergeAtoms' psJoin (VBuiltin S32Ty) (VBuiltin S32Ty) `shouldBe` Just (VBuiltin S32Ty, True, True)

            it "joins different integers to wider" $
                mergeAtoms' psJoin (VBuiltin S16Ty) (VBuiltin S32Ty) `shouldBe` Just (VBuiltin S32Ty, False, True)

            it "enforces invariance for different builtins" $
                mergeAtoms' psJoinInv (VBuiltin S16Ty) (VBuiltin S32Ty) `shouldBe` Nothing

        describe "VSingleton" $ do
            it "joins identical singletons" $
                mergeAtoms' psJoin (VSingleton S32Ty 10) (VSingleton S32Ty 10) `shouldBe` Just (VSingleton S32Ty 10, True, True)

            it "widens singletons with different values" $
                mergeAtoms' psJoin (VSingleton S32Ty 10) (VSingleton S32Ty 20) `shouldBe` Just (VBuiltin S32Ty, False, False)

            it "widens singletons with different values at invariant (same C type)" $
                mergeAtoms' psJoinInv (VSingleton S32Ty 10) (VSingleton S32Ty 20) `shouldBe` Just (VBuiltin S32Ty, False, False)

        describe "Cross merge (Builtin vs Singleton)" $ do
            it "widens singleton to builtin on Join" $
                mergeAtoms' psJoin (VSingleton S32Ty 10) (VBuiltin S32Ty) `shouldBe` Just (VBuiltin S32Ty, False, True)

            it "narrows builtin to singleton on Meet" $
                mergeAtoms' psMeet (VSingleton S32Ty 10) (VBuiltin S32Ty) `shouldBe` Just (VSingleton S32Ty 10, True, False)

            it "enforces invariance for different base types" $
                mergeAtoms' psJoinInv (VSingleton S16Ty 10) (VBuiltin S32Ty) `shouldBe` Nothing

            it "allows singleton-to-builtin widening at invariant (same C type)" $ do
                let psMeetInv = ProductState PMeet QualUnshielded QualUnshielded False
                mergeAtoms' psJoinInv (VSingleton S32Ty 10) (VBuiltin S32Ty) `shouldBe` Just (VBuiltin S32Ty, False, True)
                mergeAtoms' psMeetInv (VSingleton S32Ty 10) (VBuiltin S32Ty) `shouldBe` Just (VSingleton S32Ty 10, True, False)

        it "correctly identifies side-specific identity" $ do
            let ps = ProductState PMeet QualTop QualTop False
            -- meet S32 S16 -> S16.
            -- identL = (S16 == S32) = False
            -- identR = (S16 == S16) = True
            mergeAtoms' ps (VBuiltin S32Ty) (VBuiltin S16Ty) `shouldBe` Just (VBuiltin S16Ty, False, True)

    describe "Properties" $ do
        let genAtom :: Gen (ValueStructure () ())
            genAtom = oneof
                [ VBuiltin <$> arbitrary
                , VSingleton <$> arbitrary <*> arbitrary
                ]

        prop "mergeAtoms is reflexive" $ \ps ->
            forAll genAtom $ \a ->
                mergeAtoms ps a a == Just (a, True, True)

        prop "mergeAtoms is commutative" $ \ps ->
            forAll genAtom $ \a ->
                forAll genAtom $ \b ->
                    let psRev = ps { psQualL = psQualR ps, psQualR = psQualL ps }
                        res1 = mergeAtoms ps a b
                        res2 = mergeAtoms psRev b a
                        swap (x, l, r) = (x, r, l)
                    in res1 == fmap swap res2


