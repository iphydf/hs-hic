{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Core.ConstraintsSpec (spec) where

import           Test.Hspec

import           Language.Hic.Core.Errors                 (MismatchReason (..))
import           Language.Hic.TypeSystem.Core.Base        (StdType (..),
                                                           TemplateId (..),
                                                           pattern BuiltinType,
                                                           pattern FullTemplate,
                                                           pattern Template)
import           Language.Hic.TypeSystem.Core.Constraints

spec :: Spec
spec = do
    let t0 = Template (TIdSolver 0 Nothing) Nothing
    let t1 = Template (TIdSolver 1 Nothing) Nothing
    let ft0 = FullTemplate (TIdSolver 0 Nothing) Nothing
    let ft1 = FullTemplate (TIdSolver 1 Nothing) Nothing

    describe "collectTemplates" $ do
        it "collects from Equality" $ do
            collectTemplates (Equality t0 t1 Nothing [] GeneralMismatch) `shouldMatchList` [ft0, ft1]

        it "collects from Subtype" $ do
            collectTemplates (Subtype t0 t1 Nothing [] GeneralMismatch) `shouldMatchList` [ft0, ft1]

        it "collects from Lub" $ do
            collectTemplates (Lub t0 [t1] Nothing [] GeneralMismatch) `shouldMatchList` [ft0, ft1]

        it "collects from Callable" $ do
            collectTemplates (Callable t0 [t1] t0 Nothing [] Nothing False) `shouldMatchList` [ft0, ft1]

        it "collects from HasMember" $ do
            let t2 = Template (TIdSolver 2 Nothing) Nothing
            let ft2 = FullTemplate (TIdSolver 2 Nothing) Nothing
            collectTemplates (HasMember t0 "a" t2 Nothing [] GeneralMismatch) `shouldMatchList` [ft0, ft2]

        it "collects from CoordinatedPair" $ do
            let t2 = Template (TIdSolver 2 Nothing) Nothing
            let ft2 = FullTemplate (TIdSolver 2 Nothing) Nothing
            collectTemplates (CoordinatedPair t0 t1 t2 Nothing [] Nothing) `shouldMatchList` [ft0, ft1, ft2]

    describe "mapTypes" $ do
        it "transforms all types in a constraint" $ do
            let f = \case
                    BuiltinType S32Ty -> BuiltinType S64Ty
                    t -> t
            let c = Equality (BuiltinType S32Ty) (BuiltinType S32Ty) Nothing [] GeneralMismatch
            let expected = Equality (BuiltinType S64Ty) (BuiltinType S64Ty) Nothing [] GeneralMismatch
            mapTypes f c `shouldBe` expected

        it "transforms types in Lub" $ do
            let f = \case
                    BuiltinType S32Ty -> BuiltinType S64Ty
                    t -> t
            let c = Lub (BuiltinType S32Ty) [BuiltinType S32Ty] Nothing [] GeneralMismatch
            let expected = Lub (BuiltinType S64Ty) [BuiltinType S64Ty] Nothing [] GeneralMismatch
            mapTypes f c `shouldBe` expected

        it "transforms types in Callable" $ do
            let f = \case
                    BuiltinType S32Ty -> BuiltinType S64Ty
                    t -> t
            let c = Callable (BuiltinType S32Ty) [BuiltinType S32Ty] (BuiltinType S32Ty) Nothing [] Nothing False
            let expected = Callable (BuiltinType S64Ty) [BuiltinType S64Ty] (BuiltinType S64Ty) Nothing [] Nothing False
            mapTypes f c `shouldBe` expected

        it "transforms types in HasMember" $ do
            let f = \case
                    BuiltinType S32Ty -> BuiltinType S64Ty
                    t -> t
            let c = HasMember (BuiltinType S32Ty) "a" (BuiltinType S32Ty) Nothing [] GeneralMismatch
            let expected = HasMember (BuiltinType S64Ty) "a" (BuiltinType S64Ty) Nothing [] GeneralMismatch
            mapTypes f c `shouldBe` expected

        it "transforms types in CoordinatedPair" $ do
            let f = \case
                    BuiltinType S32Ty -> BuiltinType S64Ty
                    t -> t
            let c = CoordinatedPair (BuiltinType S32Ty) (BuiltinType S32Ty) (BuiltinType S32Ty) Nothing [] Nothing
            let expected = CoordinatedPair (BuiltinType S64Ty) (BuiltinType S64Ty) (BuiltinType S64Ty) Nothing [] Nothing
            mapTypes f c `shouldBe` expected
