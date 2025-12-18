{-# LANGUAGE DataKinds           #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE PatternSynonyms     #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Core.TypeSystemSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Fix                     (Fix (..))
import           Data.Maybe                   (isJust)
import qualified Data.Set                     as Set
import qualified Language.Cimple              as C
import           Language.Hic.Core.TypeSystem

spec :: Spec
spec = do
    describe "zipWithF" $ do
        it "is symmetric for successful zips" $ property $ \(t1 :: TypeInfo 'Local) (t2 :: TypeInfo 'Local) ->
            case (zipWithF (,) (unFix t1) (unFix t2), zipWithF (,) (unFix t2) (unFix t1)) of
                (Just _, Just _)   -> True
                (Nothing, Nothing) -> True
                _                  -> False

        it "returns Just iff same top-level constructor and compatible metadata" $ property $ \(t1 :: TypeInfo 'Local) (t2 :: TypeInfo 'Local) ->
            let res = zipWithF (,) (unFix t1) (unFix t2)
            in case (unFix t1, unFix t2) of
                (PointerF _, PointerF _) -> isJust res
                (QualifiedF qs1 _, QualifiedF qs2 _) -> isJust res == (qs1 == qs2)
                (SizedF _ l1, SizedF _ l2) -> isJust res == (l1 == l2)
                (BuiltinTypeF s1, BuiltinTypeF s2) -> isJust res == (s1 == s2)
                (ExternalTypeF l1, ExternalTypeF l2) -> isJust res == (l1 == l2)
                (TemplateF (FT id1 i1), TemplateF (FT id2 i2)) ->
                    isJust res == (id1 == id2 && isJust i1 == isJust i2)
                (ArrayF _ d1, ArrayF _ d2) ->
                    isJust res == (length d1 == length d2)
                (VarF l1 _, VarF l2 _) -> isJust res == (l1 == l2)
                (FunctionF _ p1, FunctionF _ p2) ->
                    isJust res == (length p1 == length p2)
                (SingletonF s1 i1, SingletonF s2 i2) ->
                    isJust res == (s1 == s2 && i1 == i2)
                (VarArgF, VarArgF) -> isJust res
                (IntLitF l1, IntLitF l2) -> isJust res == (l1 == l2)
                (NameLitF l1, NameLitF l2) -> isJust res == (l1 == l2)
                (EnumMemF l1, EnumMemF l2) -> isJust res == (l1 == l2)
                (UnconstrainedF, UnconstrainedF) -> isJust res
                (ConflictF, ConflictF) -> isJust res
                (UnsupportedF u1, UnsupportedF u2) -> isJust res == (u1 == u2)
                (TypeRefF r1 l1 _, TypeRefF r2 l2 _) -> isJust res == (r1 == r2 && l1 == l2)
                _ -> not (isJust res)

        it "is complete (returns Just when given the same structure twice)" $ property $ \(t :: TypeInfo 'Local) ->
            isJust (zipWithF (\_ _ -> ()) (unFix t) (unFix t))

    describe "normalizeType" $ do
        it "simplifies Array Nothing to Array Unconstrained" $ do
            normalizeType (Array Nothing []) `shouldBe` Array (Just Unconstrained) []

        it "is idempotent" $ property $ \(t :: TypeInfo 'Local) ->
            normalizeType (normalizeType t) == normalizeType t

    describe "wrapQualified" $ do
        it "collapses qualifiers on Unconstrained" $ do
            Qualified (normalizeQuals $ Set.singleton QConst) Unconstrained `shouldBe` Unconstrained

        it "collapses qualifiers on Conflict" $ do
            Qualified (normalizeQuals $ Set.singleton QNullable) Conflict `shouldBe` Conflict

        it "propagates qualifiers through Sized" $ do
            let loc = C.L (C.AlexPn 0 0 0) C.IdVar (TIdName "len")
            let ty = Sized (BuiltinType S32Ty) loc
            Qualified (normalizeQuals $ Set.singleton QConst) ty `shouldBe` Sized (Const (BuiltinType S32Ty)) loc

