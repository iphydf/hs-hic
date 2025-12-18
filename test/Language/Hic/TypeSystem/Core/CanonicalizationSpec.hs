{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Core.CanonicalizationSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Fix                                      (Fix (..),
                                                                foldFix, unFix)
import qualified Language.Cimple                               as C
import           Language.Hic.TypeSystem.Core.Base             (Phase (..),
                                                                StdType (..),
                                                                TemplateId (..),
                                                                pattern BuiltinType,
                                                                pattern Pointer,
                                                                pattern Template)
import qualified Language.Hic.TypeSystem.Core.Base             as TS
import           Language.Hic.TypeSystem.Core.Canonicalization
import           Language.Hic.TypeSystem.Core.Lattice          (subtypeOf)

spec :: Spec
spec = do
    let intTy = BuiltinType S32Ty
    let pInt = Pointer intTy

    it "minimizes a simple concrete type to itself" $ do
        minimize intTy `shouldBe` intTy
        minimize pInt `shouldBe` pInt

    it "identifies semantically equivalent unrolled types" $ do
        -- G1: T = Pointer T  =>  0: Pointer 0
        let recursive = Pointer (Template (TIdRec 0) Nothing)

        -- G2: T = Pointer (Pointer T) => 0: Pointer 1, 1: Pointer 0
        let unrolled = Pointer (Pointer (Template (TIdRec 0) Nothing))

        bisimilar recursive unrolled `shouldBe` True

    it "minimizes unrolled recursive types to a compact form" $ do
        let recursive = Pointer (Template (TIdRec 0) Nothing)
        let unrolled = Pointer (Pointer (Pointer (Template (TIdRec 0) Nothing)))

        let m1 = minimize recursive
        let m2 = minimize unrolled
        m1 `shouldBe` m2

    it "minimizes mutual recursion to a simple cycle" $ do
        -- G1: A -> B, B -> A  (2-node cycle)
        -- A = Pointer B, B = Pointer A
        -- In our tree representation with TIdRec:
        -- A = Pointer (Pointer (TIdRec 0))
        let mutual = Pointer (Pointer (Template (TIdRec 0) Nothing))
        -- G2: C -> C (1-node cycle)
        -- C = Pointer C
        let simple = Pointer (Template (TIdRec 0) Nothing)

        minimize mutual `shouldBe` minimize simple

    it "branching recursion minimizes correctly" $ do
        -- T = Pair(T, T)
        -- represented as a function for testing branching
        let branch = TS.Function (Template (TIdRec 0) Nothing) [Template (TIdRec 0) Nothing]
        let unrolled = TS.Function branch [branch]

        bisimilar branch unrolled `shouldBe` True
        minimize unrolled `shouldBe` minimize branch

    it "is position-blind during minimization" $ do
        let l1 = C.L (C.AlexPn 10 1 10) C.IdSueType (TS.TIdName "S")
        let l2 = C.L (C.AlexPn 20 2 20) C.IdSueType (TS.TIdName "S")
        let t1 = TS.TypeRef TS.StructRef l1 []
        let t2 = TS.TypeRef TS.StructRef l2 []

        let m1 = minimize t1
        let m2 = minimize t2
        m1 `shouldBe` m2

    describe "properties" $ do
        it "is idempotent" $ property $ \t ->
            minimize (minimize (t :: TS.TypeInfo 'Global)) == minimize t

        it "preserves semantic equivalence after unrolling cycles" $ property $ \t ->
            -- Unroll cycles: replace every TIdRec with the actual sub-tree it points to.
            -- To avoid physical cycles that would diverge in Eq, we use a depth-limited
            -- unrolling that doesn't use self-referential 'let'.
            let unroll t_orig = go [] (0 :: Int) t_orig
                go stack depth (Fix f)
                    | depth > 4 = Fix f
                    | otherwise = case f of
                        TS.TemplateF (TS.FullTemplate (TS.TIdRec i) Nothing)
                            | i >= 0 && i < length stack -> stack !! i
                        _ -> Fix $ fmap (go (Fix f : stack) (depth + 1)) f
            in bisimilar (unroll (t :: TS.TypeInfo 'Global)) t

        it "is a congruence" $ property $ \t1 ->
            -- If we take a type and minimize it, they are bisimilar by definition.
            -- Wrapping them both in Pointer should preserve bisimilarity.
            let t2 = minimize t1
            in bisimilar (Pointer (t1 :: TS.TypeInfo 'Global)) (Pointer t2)

        it "preserves subtype relationships" $ property $ \t1 t2 ->
            let m1 = minimize (t1 :: TS.TypeInfo 'Global)
                m2 = minimize (t2 :: TS.TypeInfo 'Global)
            in subtypeOf t1 t2 == subtypeOf m1 m2
