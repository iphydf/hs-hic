{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
{-# LANGUAGE TypeApplications    #-}

module Language.Hic.Refined.SemanticEqualitySpec (spec) where

import           Data.Map.Strict                       (Map)
import qualified Data.Map.Strict                       as Map
import qualified Language.Cimple                       as C
import           Language.Hic.Refined.Arbitrary        ()
import           Language.Hic.Refined.Context          (emptyContext,
                                                        emptyRefinements)
import           Language.Hic.Refined.LatticeOp        (Polarity (..))
import           Language.Hic.Refined.SemanticEquality
import           Language.Hic.Refined.State
import           Language.Hic.Refined.Types
import           Test.Hspec
import           Test.Hspec.QuickCheck                 (prop)

spec :: Spec
spec = do
    describe "semEqStep" $ do
        it "matches a builtin type" $ do
            let ps = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
                orig = AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))
            semEqStep @TemplateId ps psNodeL orig `shouldBe` True

        it "matches a linear expression with different order" $ do
            let ps = AnyRigidNodeF (RObject (VSizeExpr [(ProductState 2 3 PJoin False emptyContext 0 0 Nothing Nothing Nothing, 1), (ProductState 4 5 PJoin False emptyContext 0 0 Nothing Nothing Nothing, 2)]) (Quals False False))
                orig = AnyRigidNodeF (RObject (VSizeExpr [(4, 2), (2, 1)]) (Quals False False))
            semEqStep @TemplateId ps psNodeL orig `shouldBe` True

    describe "VNominal structural similarity" $ do
        it "matches VNominal nodes with different parameters if selector maps them to same originals" $ do
            let ps = AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Point")) [ProductState 10 11 PJoin False emptyContext 0 0 Nothing Nothing Nothing]) (Quals False False))
                orig = AnyRigidNodeF (RObject (VNominal (dummyL' (TIdName "Point")) [10]) (Quals False False))
            semEqStep @TemplateId ps psNodeL orig `shouldBe` True

    describe "semEqResult" $ do
        prop "is reflexive (canonicalized)" $ \(node :: AnyRigidNodeF TemplateId ProductState) ->
            semEqResult node node

dummyL' :: t -> C.Lexeme t
dummyL' = C.L (C.AlexPn 0 0 0) C.IdSueType
