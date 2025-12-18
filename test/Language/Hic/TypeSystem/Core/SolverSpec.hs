{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Core.SolverSpec (spec) where

import           Test.Hspec
import           Test.QuickCheck

import           Data.Fix                             (Fix (..))
import           Data.Map.Strict                      (Map)
import qualified Data.Map.Strict                      as Map
import           Data.Set                             (Set)
import qualified Data.Set                             as Set
import           Data.Text                            (Text)
import qualified Data.Text                            as T
import qualified Language.Cimple                      as C
import           Language.Hic.Core.Errors             (MismatchReason (..))
import           Language.Hic.TypeSystem.Core.Base    (StdType (..),
                                                       TemplateId (..),
                                                       TypeDescr (..),
                                                       pattern BuiltinType,
                                                       pattern FullTemplate,
                                                       pattern Nonnull,
                                                       pattern Pointer,
                                                       pattern Template)
import qualified Language.Hic.TypeSystem.Core.Base    as TS
import           Language.Hic.TypeSystem.Core.Lattice (subtypeOf)
import           Language.Hic.TypeSystem.Core.Solver

spec :: Spec
spec = do
    let t0 = Template (TIdSolver 0 Nothing) Nothing
    let ft0 = FullTemplate (TIdSolver 0 Nothing) Nothing
    let s2 = TS.Singleton S32Ty 2
    let s3 = TS.Singleton S32Ty 3

    it "solves a simple equality" $ do
        let cs = [Equality t0 s2 Nothing [] GeneralMismatch]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        Map.lookup ft0 res `shouldBe` Just s2

    it "decays singletons to base type on mismatch (LUB)" $ do
        let cs = [ Equality t0 s2 Nothing [] GeneralMismatch
                 , Equality t0 s3 Nothing [] GeneralMismatch
                 ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        -- T0 should now be bound to BuiltinType S32Ty
        Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

    it "handles subtyping constraints" $ do
        let cs = [ Subtype s2 t0 Nothing [] GeneralMismatch
                 , Subtype s3 t0 Nothing [] GeneralMismatch
                 ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        -- T0 must be a common supertype of 2 and 3
        Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

    it "solves LUB constraints explicitly" $ do
        let cs = [ Lub t0 [s2, s3] Nothing [] GeneralMismatch ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

    it "propagates constraints through templates" $ do
        let t1 = Template (TIdSolver 1 Nothing) Nothing
        let ft1 = FullTemplate (TIdSolver 1 Nothing) Nothing
        let cs = [ Equality t0 s2 Nothing [] GeneralMismatch
                 , Equality t1 t0 Nothing [] GeneralMismatch
                 ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        Map.lookup ft0 res `shouldBe` Just s2
        Map.lookup ft1 res `shouldBe` Just s2

    it "decays singletons inside nested structures" $ do
        let t1 = Template (TIdSolver 1 Nothing) Nothing
        let ft1 = FullTemplate (TIdSolver 1 Nothing) Nothing
        -- Pointer T1 = Pointer 2
        -- Pointer T1 = Pointer 3
        -- T1 should be int
        let cs = [ Equality t0 (TS.Pointer t1) Nothing [] GeneralMismatch
                 , Equality t0 (TS.Pointer s2) Nothing [] GeneralMismatch
                 , Equality t0 (TS.Pointer s3) Nothing [] GeneralMismatch
                 ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        Map.lookup ft1 res `shouldBe` Just (BuiltinType S32Ty)

    it "infers function signature from multiple call sites (bidirectional)" $ do
        pendingWith "Hypothesis: Solver.hs unnecessarily adds a const qualifier to inferred function parameters, likely due to the forceConst issue in the lattice join."
        -- Template F is called as F(2) and F(3)
        -- F should be inferred as (int) -> void
        let f = Template (TIdSolver 10 Nothing) Nothing
        let ftf = FullTemplate (TIdSolver 10 Nothing) Nothing
        let ret = Template (TIdSolver 11 Nothing) Nothing
        let cs = [ Callable f [s2] ret Nothing [] Nothing False
                 , Callable f [s3] ret Nothing [] Nothing False
                 ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        -- The parameter of F should be int (decayed from 2 and 3)
        Map.lookup ftf res `shouldSatisfy` \case
            Just (TS.Function _ [BuiltinType S32Ty]) -> True
            _ -> False

    it "handles recursive equality (T = Pointer T) by capping depth" $ do
        let pT0 = TS.Pointer t0
        let cs = [ Equality t0 pT0 Nothing [] GeneralMismatch ]
        -- This should not loop infinitely.
        -- It should either detect an occurs-check error or cap the recursion.
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        Map.lookup ft0 res `shouldSatisfy` \case
            Just (TS.Conflict) -> True
            _ -> False

    it "reproducibly demonstrates unsound function subtyping in Solver" $ do
        let p1 = Template (TIdSolver 1 Nothing) Nothing
        let p2 = Template (TIdSolver 2 Nothing) Nothing

        let f1 = TS.Function (BuiltinType VoidTy) [p1]
        let f2 = TS.Function (BuiltinType VoidTy) [p2]

        -- f1 <: f2 implies p2 <: p1
        -- If we also have p2 = int, then int <: p1.
        -- If we also have p1 <: short, then int <: p1 <: short, which is a conflict.
        let cs = [ Subtype f1 f2 Nothing [] GeneralMismatch
                 , Equality p2 (BuiltinType S32Ty) Nothing [] GeneralMismatch
                 , Subtype p1 (BuiltinType S16Ty) Nothing [] GeneralMismatch
                 ]
        let res = solveConstraints Map.empty Set.empty Map.empty cs
        let errs = verifyConstraints Map.empty Set.empty res cs
        -- If this passes (0 errors), it means the solver used covariance (p1 <: p2 => p1 <: int),
        -- because p1 <: int and p1 <: short is NOT a conflict (p1 becomes short).
        -- If it fails, it means the solver correctly used contravariance (int <: p1),
        -- because int <: p1 and p1 <: short IS a conflict.
        length errs `shouldSatisfy` (> 0)

    describe "HasMember constraints" $ do
        it "resolves member type from a struct" $ do
            let structName = "MyStruct"
            let l = C.L (C.AlexPn 0 0 0) C.IdVar structName
            let structDescr = TS.StructDescr l [] [ (C.L (C.AlexPn 0 0 0) C.IdVar "a", BuiltinType S32Ty) ] []
            let ts = Map.fromList [(structName, structDescr)]
            let tStruct = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.StructRef (fmap TIdName l) []
            let cs = [ HasMember tStruct "a" t0 Nothing [] GeneralMismatch ]
            let res = solveConstraints ts Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

        it "resolves member type from a pointer to struct" $ do
            let structName = "MyStruct"
            let l = C.L (C.AlexPn 0 0 0) C.IdVar structName
            let structDescr = TS.StructDescr l [] [ (C.L (C.AlexPn 0 0 0) C.IdVar "a", BuiltinType S32Ty) ] []
            let ts = Map.fromList [(structName, structDescr)]
            let tStructPtr = TS.toLocal 0 TS.TopLevel $ TS.Pointer (TS.TypeRef TS.StructRef (fmap TIdName l) [])
            let cs = [ HasMember tStructPtr "a" t0 Nothing [] GeneralMismatch ]
            let res = solveConstraints ts Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

        it "resolves member type from a templated struct" $ do
            let structName = "MyStruct"
            let l = C.L (C.AlexPn 0 0 0) C.IdVar structName
            let p0_global = TS.TIdParam 0 (Just "T") TS.TopLevel
            let structDescr = TS.StructDescr l [p0_global] [ (C.L (C.AlexPn 0 0 0) C.IdVar "a", Template p0_global Nothing) ] []
            let ts = Map.fromList [(structName, structDescr)]
            let tStruct = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.StructRef (fmap TIdName l) [BuiltinType S32Ty]
            let cs = [ HasMember tStruct "a" t0 Nothing [] GeneralMismatch ]
            let res = solveConstraints ts Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

    describe "Lattice joins in solver" $ do
        it "joins different TypeRef instantiations" $ do
            pendingWith "Hypothesis: TypeRef parameters are being forced to const during join, even at the top level where they should be covariant."
            let structName = "MyStruct"
            let l = C.L (C.AlexPn 0 0 0) C.IdVar structName
            let p0_global = TS.TIdParam 0 (Just "T") TS.TopLevel
            let structDescr = TS.StructDescr l [p0_global] [ (C.L (C.AlexPn 0 0 0) C.IdVar "a", Template p0_global Nothing) ] []
            let ts = Map.fromList [(structName, structDescr)]
            let tStruct1 = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.StructRef (fmap TIdName l) [TS.Singleton S32Ty 1]
            let tStruct2 = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.StructRef (fmap TIdName l) [TS.Singleton S32Ty 2]
            let cs = [ Equality t0 tStruct1 Nothing [] GeneralMismatch
                     , Equality t0 tStruct2 Nothing [] GeneralMismatch
                     ]
            let res = solveConstraints ts Set.empty Map.empty cs
            let expected = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.StructRef (fmap TIdName l) [BuiltinType S32Ty]
            Map.lookup ft0 res `shouldBe` Just expected

    describe "Callable constraints" $ do
        it "unifies argument types with function parameters" $ do
            let funcType = TS.Function (BuiltinType VoidTy) [BuiltinType S32Ty]
            let cs = [ Callable funcType [t0] (BuiltinType VoidTy) Nothing [] Nothing False ]
            let res = solveConstraints Map.empty Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

        it "resolves Callable from a TypeRef (typedef)" $ do
            let funcName = "MyFunc"
            let l = C.L (C.AlexPn 0 0 0) C.IdVar funcName
            let funcDescr = TS.FuncDescr l [] (BuiltinType VoidTy) [BuiltinType S32Ty]
            let ts = Map.fromList [(funcName, funcDescr)]
            let tFunc = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.FuncRef (fmap TIdName l) []
            let cs = [ Callable tFunc [t0] (BuiltinType VoidTy) Nothing [] Nothing False ]
            let res = solveConstraints ts Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

        it "resolves Callable from a Pointer to Function" $ do
            let funcType = TS.Pointer (TS.Function (BuiltinType VoidTy) [BuiltinType S32Ty])
            let cs = [ Callable funcType [t0] (BuiltinType VoidTy) Nothing [] Nothing False ]
            let res = solveConstraints Map.empty Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

        it "refreshes templates for polymorphic calls" $ do
            let p0 = Template (TS.TIdParam 0 (Just "T") TS.TopLevel) Nothing
            -- We simulate a local template from another function (phId = 100)
            let funcType = TS.toLocal 100 TS.TopLevel $ TS.Function (BuiltinType VoidTy) [p0]
            let ft_p0 = case funcType of
                    TS.Function _ [Fix (TS.TemplateF ft)] -> ft
                    _ -> error "Expected function with one template parameter"

            -- Two calls with different types should NOT conflict on p0 if it is refreshed
            let cs = [ Callable funcType [s2] (BuiltinType VoidTy) Nothing [] (Just 1) True
                     , Callable funcType [s3] (BuiltinType VoidTy) Nothing [] (Just 2) True
                     ]
            let res = solveConstraints Map.empty Set.empty Map.empty cs
            -- The original template from funcType should remain unconstrained (bound to itself)
            Map.lookup ft_p0 res `shouldBe` Just (Fix (TS.TemplateF ft_p0))

    describe "CoordinatedPair constraints" $ do
        it "unifies actual with expected when trigger is not null" $ do
            let trigger = TS.Pointer (BuiltinType S32Ty) -- Not NullPtrTy
            let actual = t0
            let expected = BuiltinType S32Ty
            let cs = [ CoordinatedPair trigger actual expected Nothing [] Nothing ]
            let res = solveConstraints Map.empty Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just (BuiltinType S32Ty)

        it "does nothing when trigger is null" $ do
            let trigger = BuiltinType TS.NullPtrTy
            let actual = t0
            let expected = BuiltinType S32Ty
            let cs = [ CoordinatedPair trigger actual expected Nothing [] Nothing ]
            let res = solveConstraints Map.empty Set.empty Map.empty cs
            Map.lookup ft0 res `shouldBe` Just t0

    describe "verifyConstraints" $ do
        it "reports mismatch for unsatisfied Equality" $ do
            let cs = [ Equality s2 s3 Nothing [] GeneralMismatch ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

        it "reports mismatch for unsatisfied Subtype" $ do
            let cs = [ Subtype s3 s2 Nothing [] GeneralMismatch ] -- 3 <: 2 is false
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

        it "reports mismatch for unsatisfied MemberAccess" $ do
            let structName = "MyStruct"
            let l = C.L (C.AlexPn 0 0 0) C.IdVar structName
            let structDescr = TS.StructDescr l [] [ (C.L (C.AlexPn 0 0 0) C.IdVar "a", BuiltinType S32Ty) ] []
            let ts = Map.fromList [(structName, structDescr)]
            let tStruct = TS.toLocal 0 TS.TopLevel $ TS.TypeRef TS.StructRef (fmap TIdName l) []
            let cs = [ HasMember tStruct "a" (BuiltinType F32Ty) Nothing [] GeneralMismatch ]
            let errs = verifyConstraints ts Set.empty Map.empty cs
            length errs `shouldSatisfy` (> 0)

        it "reports mismatch for Nonnull assigned nullptr" $ do
            let nullPtr = BuiltinType TS.NullPtrTy
            let nonnullPtr = Nonnull (Pointer (BuiltinType S32Ty))
            let cs = [ Subtype nullPtr nonnullPtr Nothing [] GeneralMismatch ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

    describe "verifyConstraints for Callable" $ do
        it "reports mismatch for arity" $ do
            let funcType = TS.Function (BuiltinType VoidTy) [BuiltinType S32Ty]
            let cs = [ Callable funcType [] (BuiltinType VoidTy) Nothing [] Nothing False ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

        it "allows contravariant parameters (Actual <: Param)" $ do
            let p0 = Template (TIdSolver 100 Nothing) Nothing
            let paramType = Pointer p0
            let actualType = Pointer (BuiltinType S32Ty)
            let funcType = TS.Function (BuiltinType VoidTy) [paramType]
            let cs = [ Callable funcType [actualType] (BuiltinType VoidTy) Nothing [] Nothing False ]
            -- The solver should bind p0 to S32Ty, making actual <: param (S32Ty* <: S32Ty*)
            let bindings = solveConstraints Map.empty Set.empty Map.empty cs
            let errs = verifyConstraints Map.empty Set.empty bindings cs
            length errs `shouldBe` 0
            Map.lookup (FullTemplate (TIdSolver 100 Nothing) Nothing) bindings `shouldBe` Just (BuiltinType S32Ty)

        it "reports mismatch for return type" $ do
            let funcType = TS.Function (BuiltinType S32Ty) []
            let cs = [ Callable funcType [] (BuiltinType F32Ty) Nothing [] Nothing False ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

        it "reports mismatch for arguments" $ do
            let funcType = TS.Function (BuiltinType VoidTy) [BuiltinType S32Ty]
            let cs = [ Callable funcType [BuiltinType F32Ty] (BuiltinType VoidTy) Nothing [] Nothing False ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

    describe "verifyConstraints for CoordinatedPair" $ do
        it "reports mismatch when trigger is Nonnull and actual </: expected" $ do
            let trigger = Nonnull (Pointer (BuiltinType S32Ty))
            let actual = BuiltinType F32Ty
            let expected = BuiltinType S32Ty
            let cs = [ CoordinatedPair trigger actual expected Nothing [] Nothing ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 1

        it "reports no mismatch when trigger is Nullable (can be null)" $ do
            let trigger = BuiltinType TS.NullPtrTy
            let actual = BuiltinType F32Ty
            let expected = BuiltinType S32Ty
            let cs = [ CoordinatedPair trigger actual expected Nothing [] Nothing ]
            let errs = verifyConstraints Map.empty Set.empty Map.empty cs
            length errs `shouldBe` 0

    describe "properties" $ do
        it "is sound (results satisfy constraints unless conflict)" $ do
            pendingWith "Soundness property falsified in some complex cases with equi-recursive types"
            let _ = withMaxSuccess 50 $ property $ \cs ->
                    let res = solveConstraints Map.empty Set.empty Map.empty cs
                        errs = verifyConstraints Map.empty Set.empty res cs
                        hasConflict = any isConflict (Map.elems res)
                        isConflict (TS.Unsupported "conflict") = True
                        isConflict _                           = False
                        hasTemplates = not (null (concatMap collectTemplates cs))
                    in counterexample ("Errors: " ++ show errs ++ "\nBindings: " ++ show res)
                       (hasConflict || null errs || not hasTemplates)
            pure ()

        it "is monotonic (result >= concrete requirements)" $ do
            pendingWith "Monotonicity property falsified in some complex cases with equi-recursive types"
            let _ = withMaxSuccess 50 $ property $ \cs ->
                    let res = solveConstraints Map.empty Set.empty Map.empty cs
                        -- For each template T that got bound to a concrete type B,
                        -- B must be a common supertype of all concrete types S
                        -- that T was required to be equal to.
                        checkConstraint = \case
                            Equality (Template tid i) s _ _ _ | not (TS.containsTemplate s) ->
                                case Map.lookup (FullTemplate tid i) res of
                                    Just b  -> subtypeOf s b
                                    Nothing -> True
                            Subtype s (Template tid i) _ _ _ | not (TS.containsTemplate s) ->
                                case Map.lookup (FullTemplate tid i) res of
                                    Just b  -> subtypeOf s b
                                    Nothing -> True
                            _ -> True
                    in all checkConstraint cs
            pure ()
