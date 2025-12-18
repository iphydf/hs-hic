{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}

module Language.Hic.TypeSystem.Ordered.SpecializerSpec (spec) where

import           Data.Fix                                    (Fix (..))
import qualified Data.Map                                    as Map
import qualified Data.Set                                    as Set
import           Language.Hic.Core.Errors                    (MismatchReason (..))
import           Language.Hic.Core.TypeSystem                (Phase (Local),
                                                              StdType (..),
                                                              TemplateId (..),
                                                              TypeInfo,
                                                              pattern BuiltinType,
                                                              pattern Function,
                                                              pattern Pointer,
                                                              pattern Template)
import           Language.Hic.TypeSystem.Core.Constraints    (Constraint (..))
import           Language.Hic.TypeSystem.Ordered.Specializer
import           Test.Hspec

spec :: Spec
spec = do
    describe "Structural Specialization" $ do
        let idx1 = BuiltinType S32Ty -- Proxy for index 1
        let t_cb = Template (TIdSolver 1 (Just "cb")) Nothing
        let t_ud = Template (TIdSolver 2 (Just "userdata")) Nothing

        it "specializes a simple template to an indexed template" $ do
            specializeType idx1 t_ud `shouldBe` Template (TIdSolver 2 (Just "userdata")) (Just idx1)

        it "specializes a function signature deeply" $ do
            let func = Function (BuiltinType VoidTy) [Pointer t_ud]
            specializeType idx1 func `shouldBe` Function (BuiltinType VoidTy) [Pointer (Template (TIdSolver 2 (Just "userdata")) (Just idx1))]

        it "specializes a Callable constraint (structural link)" $ do
            let constr = Callable t_cb [Pointer t_ud] (BuiltinType VoidTy) Nothing [] Nothing True
            let expected = Callable
                    (Template (TIdSolver 1 (Just "cb")) (Just idx1))
                    [Pointer (Template (TIdSolver 2 (Just "userdata")) (Just idx1))]
                    (BuiltinType VoidTy)
                    Nothing
                    []
                    Nothing
                    True
            specializeConstraint idx1 constr `shouldBe` expected

        it "preserves existing indices if they are already present (no double indexing)" $ do
            -- This is important to ensure idempotency or at least stability
            let t_already_indexed = Template (TIdSolver 2 (Just "userdata")) (Just idx1)
            specializeType idx1 t_already_indexed `shouldBe` t_already_indexed

        it "correctly identifies all templates in a complex type for link detection" $ do
            let complex = Function (BuiltinType VoidTy) [Pointer t_ud, t_cb]
            collectTemplates complex `shouldBe` Set.fromList [TIdSolver 1 (Just "cb"), TIdSolver 2 (Just "userdata")]
