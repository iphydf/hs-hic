{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Ordered.UnificationSpec (spec) where

import           Control.Monad                               (forM_, void)
import           Control.Monad.State.Strict                  (evalState)
import qualified Control.Monad.State.Strict                  as State
import           Data.Map.Strict                             (Map)
import qualified Data.Map.Strict                             as Map
import           Data.Set                                    (Set)
import qualified Data.Set                                    as Set
import           Data.Text                                   (Text)
import qualified Data.Text                                   as T
import           Language.Cimple                             (Lexeme (..))
import qualified Language.Cimple                             as C
import           Language.Hic.Core.Errors                    (ErrorInfo (..),
                                                              MismatchReason (..),
                                                              Provenance (..),
                                                              TypeError (..))
import           Language.Hic.TypeSystem.Core.Base           (Phase (..),
                                                              StdType (..),
                                                              TypeDescr (..),
                                                              TypeInfo,
                                                              TypeRef (..),
                                                              pattern Array,
                                                              pattern BuiltinType,
                                                              pattern Const,
                                                              pattern EnumMem,
                                                              pattern ExternalType,
                                                              pattern Function,
                                                              pattern IntLit,
                                                              pattern NameLit,
                                                              pattern Nonnull,
                                                              pattern Nullable,
                                                              pattern Owner,
                                                              pattern Pointer,
                                                              pattern Singleton,
                                                              pattern Sized,
                                                              pattern Template,
                                                              pattern TypeRef,
                                                              pattern Unsupported,
                                                              pattern Var,
                                                              pattern VarArg)
import qualified Language.Hic.TypeSystem.Core.Base           as TS
import           Language.Hic.TypeSystem.Ordered.Unification (Unify,
                                                              UnifyResult (..),
                                                              UnifyState (..),
                                                              applyBindings,
                                                              applyBindingsDeep,
                                                              buildBindingsIndex,
                                                              resolveType,
                                                              runUnification,
                                                              subtype, unify)
import           Test.Hspec

runUnifyWithBindings :: TS.TypeSystem -> Map.Map (TS.FullTemplate 'TS.Local) (TS.TypeInfo 'TS.Local, Provenance 'TS.Local) -> Unify a -> a
runUnifyWithBindings ts bindings action =
    evalState action (UnifyState bindings (buildBindingsIndex bindings) [] ts Set.empty 0 True)

spec :: Spec
spec = do
    let ts = Map.empty
    let tLocalName n = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName n) Nothing
    let ftLocalName n = TS.FullTemplate (TS.TIdAnonymous 0 (Just n)) Nothing

    it "unifies simple types" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ BuiltinType S32Ty
        let t2 = TS.toLocal 0 TS.TopLevel $ BuiltinType S32Ty
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "unifies templates with concrete types" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "T0") Nothing
        let t2 = TS.toLocal 0 TS.TopLevel $ BuiltinType S32Ty
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (TS.FullTemplate (TS.TIdAnonymous 0 (Just "T0")) Nothing) (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "handles recursive types with co-induction (self-pointer)" $ do
        -- T0 = T0*
        let t1 = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "T0") Nothing
        let t2 = TS.toLocal 0 TS.TopLevel $ Pointer (Template (TS.TIdName "T0") Nothing)
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles recursive types with co-induction (struct Tox_Memory pattern)" $ do
        -- Tox_Memory<P0, P1> = { funcs: Tox_Memory_Funcs<P0, P1>*, user_data: P0 }
        -- Tox_Memory_Funcs<P0, P1> = { dealloc: (P0, P1) -> void }
        -- Simplified model: struct M<P1> { f: (M<P1>*, P1) -> void }
        -- Task: unify M<P1>* with P1.

        let p1 = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "P1") Nothing
        let m_p1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "M")) [TS.Template (TS.TIdName "P1") Nothing]

        -- The constraint is p1 = m_p1*
        let res = runUnification ts (unify p1 (Pointer m_p1) GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "detects real type mismatches" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ BuiltinType S32Ty
        let t2 = TS.toLocal 0 TS.TopLevel $ BuiltinType F32Ty
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "decays singletons to base type on mismatch when bound to template" $ do
        pendingWith "Hypothesis: Binding a template to mismatching singletons results in TypeMismatch instead of decaying to the base type in the Unification engine."
        let t = tLocalName "T0"
        let s2 = TS.toLocal 0 TS.TopLevel $ Singleton S32Ty 2
        let s3 = TS.toLocal 0 TS.TopLevel $ Singleton S32Ty 3
        let res = runUnification ts $ do
                void $ unify t s2 GeneralMismatch Nothing []
                void $ unify t s3 GeneralMismatch Nothing []
                applyBindings t
        urErrors res `shouldSatisfy` null
        -- T0 should now be bound to BuiltinType S32Ty
        let k = TS.FullTemplate (TS.TIdAnonymous 0 (Just "T0")) Nothing
        case Map.lookup k (urBindings res) of
            Just (BuiltinType S32Ty, _) -> return ()
            _ -> expectationFailure $ "Expected BuiltinType S32Ty, got " ++ show (Map.lookup k (urBindings res))

    it "unifies all builtin types with themselves" $ do
        let builtins = [VoidTy, BoolTy, CharTy, U08Ty, S08Ty, U16Ty, S16Ty, U32Ty, S32Ty, U64Ty, S64Ty, SizeTy, F32Ty, F64Ty, NullPtrTy]
        forM_ builtins $ \bt -> do
            let t = BuiltinType bt
            let res = runUnification ts (unify t t GeneralMismatch Nothing [])
            urErrors res `shouldSatisfy` null

    it "treats different integer types as compatible for subtyping" $ do
        let ints = [CharTy, U08Ty, S08Ty, U16Ty, S16Ty, U32Ty, S32Ty, U64Ty, S64Ty, SizeTy]
        forM_ ints $ \i1 ->
            forM_ ints $ \i2 -> do
                let t1 = BuiltinType i1
                let t2 = BuiltinType i2
                let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
                urErrors res `shouldSatisfy` null

    it "handles basic pointer subtyping" $ do
        let t1 = Pointer (BuiltinType S32Ty)
        let t2 = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows subtyping from T* to const T*" $ do
        let t1 = Pointer (BuiltinType S32Ty)
        let t2 = Pointer (Const (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping from const T* to T*" $ do
        let t1 = Pointer (Const (BuiltinType S32Ty))
        let t2 = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "allows subtyping from nullptr_t to any pointer" $ do
        let t1 = BuiltinType NullPtrTy
        let t2 = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows subtyping from nullptr_t to nullable types" $ do
        let t1 = BuiltinType NullPtrTy
        let t2 = Nullable (BuiltinType S32Ty)
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping from nullptr_t to nonnull types" $ do
        let t1 = BuiltinType NullPtrTy
        let t2 = Nonnull (Pointer (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles array-to-pointer decay" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ Array (Just (BuiltinType S32Ty)) [IntLit (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "10"))]
        let t2 = TS.toLocal 0 TS.TopLevel $ Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles basic function pointer subtyping" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ Function (BuiltinType S32Ty) [BuiltinType S32Ty]
        let t2 = TS.toLocal 0 TS.TopLevel $ Function (BuiltinType S32Ty) [BuiltinType S32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows function pointer subtyping with return type mismatch" $ do
        let t1 = Function (BuiltinType S32Ty) [BuiltinType S32Ty]
        let t2 = Function (BuiltinType F32Ty) [BuiltinType S32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles contravariant function parameters in subtyping" $ do
        -- (const int*) -> void  <:  (int*) -> void
        -- This is allowed because the implementation takes a more general type.
        let t1 = Function (BuiltinType VoidTy) [Pointer (Const (BuiltinType S32Ty))]
        let t2 = Function (BuiltinType VoidTy) [Pointer (BuiltinType S32Ty)]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles sockaddr compatibility" $ do
        let sockaddr = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "sockaddr")) []
        let sockaddr_in = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "sockaddr_in")) []
        let res = runUnification ts (subtype sockaddr_in sockaddr GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "binds a template to a concrete type via subtyping" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "T0") Nothing
        let t2 = TS.toLocal 0 TS.TopLevel $ BuiltinType S32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (TS.FullTemplate (TS.TIdAnonymous 0 (Just "T0")) Nothing) (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "resolves nested templates in applyBindings" $ do
        let t0 = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "T0") Nothing
        let t1 = TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "T1") Nothing
        let res = runUnification ts $ do
                void $ unify t0 (Pointer t1) GeneralMismatch Nothing []
                void $ unify t1 (BuiltinType S32Ty) GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null
        let bindings = urBindings res
        let finalT0 = runUnifyWithBindings ts bindings (applyBindingsDeep t0)
        finalT0 `shouldBe` Pointer (BuiltinType S32Ty)

    it "unifies two templates through pointers" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ Pointer (Template (TS.TIdName "T0") Nothing)
        let t2 = TS.toLocal 0 TS.TopLevel $ Pointer (Template (TS.TIdName "T1") Nothing)
        let res = runUnification ts $ do
                void $ unify t1 t2 GeneralMismatch Nothing []
                void $ subtype (TS.toLocal 0 TS.TopLevel $ Template (TS.TIdName "T0") Nothing) (BuiltinType S32Ty) GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null
        -- T0 is bound to T1, and T1 is bound to S32Ty
        let b1 = Map.lookup (TS.FullTemplate (TS.TIdAnonymous 0 (Just "T0")) Nothing) (urBindings res)
        let b2 = Map.lookup (TS.FullTemplate (TS.TIdAnonymous 0 (Just "T1")) Nothing) (urBindings res)
        b1 `shouldSatisfy` (\case { Just (Template (TS.TIdAnonymous 0 (Just "T1")) Nothing, _) -> True; _ -> False })
        b2 `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "handles mutual recursion through templates" $ do
        -- T0 = T1*
        -- T1 = T0*
        let t0 = tLocalName "T0"
        let t1 = tLocalName "T1"
        let res = runUnification ts $ do
                void $ unify t0 (Pointer t1) GeneralMismatch Nothing []
                void $ unify t1 (Pointer t0) GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "binds templates with wrappers" $ do
        let t0 = tLocalName "T0"
        let t1 = Pointer (Const (BuiltinType S32Ty))
        let res = runUnification ts (unify t0 t1 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (Pointer (Const (BuiltinType S32Ty)), _) -> True; _ -> False })

    it "handles deeply nested recursive types" $ do
        -- T0 = Pointer (Pointer T0)
        let t0 = tLocalName "T0"
        let res = runUnification ts (unify t0 (Pointer (Pointer t0)) GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "unifies TypeRefs with template arguments" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [Template (TS.TIdName "T0") Nothing]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [BuiltinType S32Ty]
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "disallows unification of different TypeRefs" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "T")) []
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles co-inductive subtyping with nested recursive structs" $ do
        -- struct S { struct S *next; }
        -- We represent this as S<T> where T = S<T>*
        let t = tLocalName "T"
        let s_t = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) [Template (TS.TIdName "T") Nothing]
        let res = runUnification ts (unify t (Pointer s_t) GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping between Nonnull and Nullable types" $ do
        let base = Pointer (BuiltinType S32Ty)
        let nn = Nonnull base
        let nb = Nullable base

        -- Nonnull <: Nullable (allowed)
        let res1 = runUnification ts (subtype nn nb GeneralMismatch Nothing [])
        urErrors res1 `shouldSatisfy` null

        -- Nullable <: Nonnull (disallowed)
        let res2 = runUnification ts (subtype nb nn GeneralMismatch Nothing [])
        length (urErrors res2) `shouldSatisfy` (> 0)

    it "enforces sound pointer subtyping (qualification invariance)" $ do
        -- int* <: const int* (allowed)
        let res1 = runUnification ts (subtype (Pointer (BuiltinType S32Ty)) (Pointer (Const (BuiltinType S32Ty))) GeneralMismatch Nothing [])
        urErrors res1 `shouldSatisfy` null

        -- int** <: const int** (disallowed - unsound)
        let res2 = runUnification ts (subtype (Pointer (Pointer (BuiltinType S32Ty))) (Pointer (Pointer (Const (BuiltinType S32Ty)))) GeneralMismatch Nothing [])
        length (urErrors res2) `shouldSatisfy` (> 0)

    it "disallows subtyping between T** and const T**" $ do
        -- int** <: const int** (disallowed - unsound)
        let t1 = Pointer (Pointer (BuiltinType S32Ty))
        let t2 = Pointer (Pointer (Const (BuiltinType S32Ty)))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "allows subtyping from T** to T* const* (sound intermediate const)" $ do
        -- int** <: int* const* (allowed)
        let t1 = Pointer (Pointer (BuiltinType S32Ty))
        let t2 = Pointer (Const (Pointer (BuiltinType S32Ty)))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping from concrete pointer to void*" $ do
        -- int* <: void*
        -- In Hic, void* is often a Template
        let t1 = Pointer (BuiltinType S32Ty)
        let t2 = tLocalName "P0"
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "P0") (urBindings res) `shouldSatisfy` (\case { Just (Pointer (BuiltinType S32Ty), _) -> True; _ -> False })

    it "handles subtyping of TypeRefs with same template arguments" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [BuiltinType S32Ty]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [BuiltinType S32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping of TypeRefs with incompatible template arguments" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [BuiltinType S32Ty]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [BuiltinType F32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "disallows subtyping of TypeRefs with different argument counts" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [BuiltinType S32Ty]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "disallows subtyping between functions with different argument counts" $ do
        let t1 = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let t2 = Function (BuiltinType VoidTy) [BuiltinType S32Ty, BuiltinType S32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "allows subtyping of variadic functions" $ do
        let t1 = Function (BuiltinType VoidTy) [BuiltinType S32Ty, VarArg]
        let t2 = Function (BuiltinType VoidTy) [BuiltinType S32Ty, VarArg]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows subtyping from non-variadic to variadic function" $ do
        -- void(int) <: void(int, ...)
        let t1 = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let t2 = Function (BuiltinType VoidTy) [BuiltinType S32Ty, VarArg]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping between function pointers with incompatible parameters" $ do
        let t1 = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let t2 = Function (BuiltinType VoidTy) [BuiltinType F32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping between Sized and non-Sized pointers" $ do
        let base = Pointer (BuiltinType S32Ty)
        let sized = TS.toLocal 0 TS.TopLevel $ Sized base (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "len"))

        -- Sized <: base (allowed)
        let res1 = runUnification ts (subtype sized base GeneralMismatch Nothing [])
        urErrors res1 `shouldSatisfy` null

        -- base <: Sized (allowed — Sized is metadata from joinSizer, not a constraint on actual)
        let res2 = runUnification ts (subtype base sized GeneralMismatch Nothing [])
        urErrors res2 `shouldSatisfy` null

    it "handles subtyping between Owner and non-Owner pointers" $ do
        let base = Pointer (BuiltinType S32Ty)
        let owner = Owner base

        -- Owner <: base (allowed)
        let res1 = runUnification ts (subtype owner base GeneralMismatch Nothing [])
        urErrors res1 `shouldSatisfy` null

        -- base <: Owner (disallowed)
        let res2 = runUnification ts (subtype base owner GeneralMismatch Nothing [])
        length (urErrors res2) `shouldSatisfy` (> 0)

    it "allows subtyping from const T to T (copy)" $ do
        let t1 = Const (BuiltinType S32Ty)
        let t2 = BuiltinType S32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping of recursive TypeRefs with different arguments" $ do
        -- struct List<T> { T data; struct List<T> *next; }
        -- List<int> should be void $ subtype of List<const int>?
        -- In C, structs are nominal, but Hic treats them as structural with templates.
        -- If we follow C, List<int> and List<const int> are DIFFERENT types.
        let l1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "List")) [BuiltinType S32Ty]
        let l2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "List")) [Const (BuiltinType S32Ty)]

        let res = runUnification ts (subtype l1 l2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping between singletons and builtin types" $ do
        let t1 = Singleton S32Ty 42
        let t2 = BuiltinType S32Ty

        -- Singleton <: Builtin (allowed)
        let res1 = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res1 `shouldSatisfy` null

        -- Builtin <: Singleton (allowed for C compatibility)
        let res2 = runUnification ts (subtype t2 t1 GeneralMismatch Nothing [])
        urErrors res2 `shouldSatisfy` null

    it "disallows subtyping between different singletons" $ do
        let t1 = Singleton S32Ty 42
        let t2 = Singleton S32Ty 43
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping between compatible singletons of different types" $ do
        -- char(42) <: int (allowed)
        let t1 = Singleton CharTy 42
        let t2 = BuiltinType S32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping from larger singleton to smaller builtin" $ do
        -- int(42) <: char (allowed in Hic because it's based on compatibility)
        let t1 = Singleton S32Ty 42
        let t2 = BuiltinType CharTy
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping between compatible integer types" $ do
        -- char <: int (allowed)
        let t1 = BuiltinType CharTy
        let t2 = BuiltinType S32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "binds a template to a Nonnull type via subtyping" $ do
        let t1 = tLocalName "T0"
        let t2 = Nonnull (Pointer (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (Nonnull (Pointer (BuiltinType S32Ty)), _) -> True; _ -> False })

    it "binds a template to a Nullable type via subtyping" $ do
        let t1 = tLocalName "T0"
        let t2 = Nullable (Pointer (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (Nullable (Pointer (BuiltinType S32Ty)), _) -> True; _ -> False })

    it "handles subtyping from Nonnull template to plain template" $ do
        -- Nonnull T0 <: T1
        -- Should bind T1 to Nonnull T0 (or just T0 if we are loose)
        let t1 = Nonnull (tLocalName "T0")
        let t2 = tLocalName "T1"
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T1") (urBindings res) `shouldSatisfy` (\case { Just (Nonnull (Template (TS.TIdAnonymous 0 (Just "T0")) Nothing), _) -> True; _ -> False })

    it "disallows subtyping between incompatible recursive types" $ do
        -- T0 = struct S { int data; T0 *next; }
        -- T1 = struct S { float data; T1 *next; }
        let t0g = Template (TS.TIdName "T0") Nothing
        let t1g = Template (TS.TIdName "T1") Nothing
        let s0g = TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) [BuiltinType S32Ty, Pointer t0g]
        let s1g = TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) [BuiltinType F32Ty, Pointer t1g]

        let t0 = TS.toLocal 0 TS.TopLevel t0g
        let t1 = TS.toLocal 0 TS.TopLevel t1g
        let s0 = TS.toLocal 0 TS.TopLevel s0g
        let s1 = TS.toLocal 0 TS.TopLevel s1g

        let res = runUnification ts $ do
                void $ unify t0 s0 GeneralMismatch Nothing []
                void $ unify t1 s1 GeneralMismatch Nothing []
                void $ subtype t0 t1 GeneralMismatch Nothing []
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping between identical recursive TypeRefs" $ do
        -- struct List { struct List *next; }
        let l = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "List")) []
        -- In our TS, List would have a member pointing back to List.
        -- Here we just test List <: List
        let res = runUnification ts (subtype l l GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping between recursive structs with compatible modifications" $ do
        -- struct S { struct S *next; int x; }
        -- This is complex to set up purely with TypeInfo without a full TypeSystem.
        -- Model using templates for structural simulation.
        -- T0 = struct S { T0 *next; }
        -- T1 = struct S { T1 *next; }
        let t0 = tLocalName "T0"
        let t1 = tLocalName "T1"
        let s_t0 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) [Template (TS.TIdName "T0") Nothing]
        let s_t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) [Template (TS.TIdName "T1") Nothing]

        let res = runUnification ts $ do
                void $ unify t0 (Pointer s_t0) GeneralMismatch Nothing []
                void $ unify t1 (Pointer s_t1) GeneralMismatch Nothing []
                void $ subtype t0 t1 GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "disallows subtyping between recursive and non-recursive types" $ do
        let t0 = tLocalName "T0"
        let res = runUnification ts $ do
                void $ unify t0 (Pointer t0) GeneralMismatch Nothing []
                void $ subtype t0 (BuiltinType S32Ty) GeneralMismatch Nothing []
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles deep pointer subtyping with top-level const" $ do
        -- int*** <: int** const*
        let t1 = Pointer (Pointer (Pointer (BuiltinType S32Ty)))
        let t2 = Pointer (Const (Pointer (Pointer (BuiltinType S32Ty))))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows deep pointer subtyping if intermediate const is missing" $ do
        -- int*** <: const int** const*  (unsound)
        let t1 = Pointer (Pointer (Pointer (BuiltinType S32Ty)))
        let t2 = Pointer (Const (Pointer (Pointer (Const (BuiltinType S32Ty)))))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping with multiple different templates" $ do
        -- (T0, T1) -> T0  <:  (int, float) -> int
        let t0 = tLocalName "T0"
        let t1 = tLocalName "T1"
        let f1 = Function t0 [t0, t1]
        let f2 = Function (BuiltinType S32Ty) [BuiltinType S32Ty, BuiltinType F32Ty]
        let res = runUnification ts (subtype f1 f2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })
        Map.lookup (ftLocalName "T1") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType F32Ty, _) -> True; _ -> False })

    it "disallows subtyping when template constraints conflict" $ do
        -- (T0, T0) -> void  <:  (int, float) -> void
        let t0 = tLocalName "T0"
        let f1 = Function (BuiltinType VoidTy) [t0, t0]
        let f2 = Function (BuiltinType VoidTy) [BuiltinType S32Ty, BuiltinType F32Ty]
        let res = runUnification ts (subtype f1 f2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping with nested templates" $ do
        -- List<T0> <: List<int>
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "List")) [Template (TS.TIdName "T0") Nothing]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "List")) [BuiltinType S32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "handles subtyping between function pointers and TypeRef FuncRefs" $ do
        -- int(*)(int) <: ident
        -- where typedef int ident(int);
        let tsWithIdent = Map.fromList [("ident", TS.FuncDescr (C.L (C.AlexPn 0 0 0) C.IdVar "ident") [] (BuiltinType S32Ty) [BuiltinType S32Ty])]
        let t1 = Pointer (Function (BuiltinType S32Ty) [BuiltinType S32Ty])
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef FuncRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "ident")) []
        let res = runUnification tsWithIdent (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping between void* templates and nested structures" $ do
        -- void* <: struct S*
        let p0 = tLocalName "P0"
        let s = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let res = runUnification ts (subtype s p0 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "P0") (urBindings res) `shouldSatisfy` (\case { Just (TypeRef StructRef (C.L _ _ (TS.TIdAnonymous 0 (Just "S"))) [], _) -> True; _ -> False })

    it "disallows multi-level pointer qualification conversion (strict C soundness)" $ do
        -- int*** <: const int*** (disallowed - unsound)
        let t1 = Pointer (Pointer (Pointer (BuiltinType S32Ty)))
        let t2 = Pointer (Pointer (Pointer (Const (BuiltinType S32Ty))))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles sound usage of owned pointer as unowned" $ do
        -- _Owned int* <: int* (allowed)
        let base = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype (Owner base) base GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping from unowned to owned pointer" $ do
        -- int* <: _Owned int* (disallowed - unsound)
        let base = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype base (Owner base) GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping from Nonnull to non-wrapped" $ do
        -- _Nonnull int* <: int*
        let t1 = Nonnull (Pointer (BuiltinType S32Ty))
        let t2 = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping from Nonnull to Nullable" $ do
        -- _Nonnull int* <: _Nullable int*
        let base = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype (Nonnull base) (Nullable base) GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows subtyping from unqualified pointer to Nonnull pointer" $ do
        -- int* <: _Nonnull int* (allowed - unqualified is not nullable)
        let t1 = Pointer (BuiltinType S32Ty)
        let t2 = Nonnull (Pointer (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows subtyping from unqualified struct pointer to Nonnull struct pointer" $ do
        -- struct S* <: _Nonnull struct S*
        let s = TS.toLocal 0 TS.TopLevel $ Pointer (TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) [])
        let t2 = Nonnull s
        let res = runUnification ts (subtype s t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping from Nullable pointer to Nonnull pointer" $ do
        -- _Nullable int* <: _Nonnull int* (disallowed)
        let base = Pointer (BuiltinType S32Ty)
        let res = runUnification ts (subtype (Nullable base) (Nonnull base) GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "disallows subtyping between different TypeRef categories" $ do
        -- struct S <: union S
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef UnionRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping with Unsupported types" $ do
        let t1 = Unsupported "foo"
        let t2 = BuiltinType S32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles recursive subtyping with multiple distinct branches" $ do
        -- struct S { struct S *a; struct S *b; }
        let t = tLocalName "T"
        -- Simulation: T = { a: T*, b: T* }
        let res = runUnification ts $ do
                void $ unify t (TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [Pointer (Template (TS.TIdName "T") Nothing), Pointer (Template (TS.TIdName "T") Nothing)]) GeneralMismatch Nothing []
                void $ subtype t t GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "disallows subtyping between different recursive structures" $ do
        -- T0 = T0*
        -- T1 = { T1*, T1* }
        let t0 = tLocalName "T0"
        let t1 = tLocalName "T1"
        let res = runUnification ts $ do
                void $ unify t0 (Pointer t0) GeneralMismatch Nothing []
                void $ unify t1 (TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) [Pointer (Template (TS.TIdName "T1") Nothing), Pointer (Template (TS.TIdName "T1") Nothing)]) GeneralMismatch Nothing []
                void $ subtype t0 t1 GeneralMismatch Nothing []
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping between qualified and unqualified TypeRefs" $ do
        -- struct S <: const struct S
        let s = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let res = runUnification ts (subtype s (Const s) GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows subtyping from const struct to mutable struct (copy)" $ do
        -- const struct S <: struct S
        let s = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "S")) []
        let res = runUnification ts (subtype (Const s) s GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping of function pointers with qualifiers" $ do
        -- void(*)(int) <: void(* const)(int)
        let f = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let res = runUnification ts (subtype (Pointer f) (Const (Pointer f)) GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping between deeply nested function pointers" $ do
        -- void(*(*)(int))(int) <: void(*(*)(int))(int)
        let f = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let pf = Pointer f
        let h = Function pf [BuiltinType S32Ty]
        let res = runUnification ts (subtype h h GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping with mixed wrappers (Nonnull + Const)" $ do
        -- _Nonnull const int* <: const int*
        let t1 = Nonnull (Const (Pointer (BuiltinType S32Ty)))
        let t2 = Const (Pointer (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping of arrays of pointers" $ do
        -- int* [10] <: int* [10]
        let p = Pointer (BuiltinType S32Ty)
        let t = TS.toLocal 0 TS.TopLevel $ Array (Just p) [IntLit (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "10"))]
        let res = runUnification ts (subtype t t GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping of complex recursive structs with multiple templates" $ do
        -- struct Node<T, U> { T data; struct Node<T, U> *next; U metadata; }
        let node_t_u = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Node")) [Template (TS.TIdName "T") Nothing, Template (TS.TIdName "U") Nothing]

        let res = runUnification ts (unify node_t_u node_t_u GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "binds multiple templates in a single subtyping check" $ do
        -- struct Pair<T, U> <: struct Pair<int, float>
        let pair_t_u = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "Pair")) [Template (TS.TIdName "T") Nothing, Template (TS.TIdName "U") Nothing]
        let pair_int_float = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "Pair")) [BuiltinType S32Ty, BuiltinType F32Ty]

        let res = runUnification ts (subtype pair_t_u pair_int_float GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })
        Map.lookup (ftLocalName "U") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType F32Ty, _) -> True; _ -> False })


    it "handles subtyping of function pointers with templates" $ do
        -- T0(*)(T1) <: int(*)(float)
        let t0 = tLocalName "T0"
        let t1 = tLocalName "T1"
        let f1 = Pointer (Function t0 [t1])
        let f2 = Pointer (Function (BuiltinType S32Ty) [BuiltinType F32Ty])

        let res = runUnification ts (subtype f1 f2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })
        Map.lookup (ftLocalName "T1") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType F32Ty, _) -> True; _ -> False })

    it "handles deep template unification in recursive structures" $ do
        -- struct List<T> { T data; struct List<T> *next; }
        -- List<T0> <: List<int>
        let l_t0 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "List")) [Template (TS.TIdName "T0") Nothing]
        let l_int = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "List")) [BuiltinType S32Ty]

        let res = runUnification ts (subtype l_t0 l_int GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "correctly identifies incompatible deeply nested pointers" $ do
        -- int*** <: int**
        let t1 = Pointer (Pointer (Pointer (BuiltinType S32Ty)))
        let t2 = Pointer (Pointer (BuiltinType S32Ty))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping with multiple recursive constraints" $ do
        -- T0 = T0*, T1 = T1*
        -- T0 <: T1
        let t0 = tLocalName "T0"
        let t1 = tLocalName "T1"
        let res = runUnification ts $ do
                void $ unify t0 (Pointer t0) GeneralMismatch Nothing []
                void $ unify t1 (Pointer t1) GeneralMismatch Nothing []
                void $ subtype t0 t1 GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "handles function-to-pointer decay in subtyping" $ do
        -- void(int) <: void(*)(int)
        let f = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let pf = Pointer f
        let res = runUnification ts (subtype f pf GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles pointer-to-function subtyping" $ do
        -- void(*)(int) <: void(int)
        let f = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let pf = Pointer f
        let res = runUnification ts (subtype pf f GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "binds a template to a singleton via subtyping" $ do
        -- T0 <: int(42)
        let t0 = tLocalName "T0"
        let s = Singleton S32Ty 42
        let res = runUnification ts (subtype t0 s GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (Singleton S32Ty 42, _) -> True; _ -> False })

    it "handles subtyping with deep recursive cross-references" $ do
        -- struct A { struct B *b; }
        -- struct B { struct A *a; }
        let a = tLocalName "A"
        let b = tLocalName "B"
        let res = runUnification ts $ do
                void $ unify a (TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "A")) [Pointer (Template (TS.TIdName "B") Nothing)]) GeneralMismatch Nothing []
                void $ unify b (TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "B")) [Pointer (Template (TS.TIdName "A") Nothing)]) GeneralMismatch Nothing []
                void $ subtype a a GeneralMismatch Nothing []
                void $ subtype b b GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "disallows subtyping between variadic and non-variadic functions in the wrong direction" $ do
        -- void(int, ...) <: void(int) (disallowed)
        let t1 = Function (BuiltinType VoidTy) [BuiltinType S32Ty, VarArg]
        let t2 = Function (BuiltinType VoidTy) [BuiltinType S32Ty]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping between identical ExternalTypes" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ ExternalType (C.L (C.AlexPn 0 0 0) C.IdStdType (TS.TIdName "va_list"))
        let t2 = TS.toLocal 0 TS.TopLevel $ ExternalType (C.L (C.AlexPn 0 0 0) C.IdStdType (TS.TIdName "va_list"))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping with Var and Owner" $ do
        let base = Pointer (BuiltinType S32Ty)
        let owner = Owner base
        let varOwner = TS.toLocal 0 TS.TopLevel $ Var (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "p")) owner

        let res = runUnification ts (subtype varOwner owner GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping with Template bound to Owner" $ do
        let base = Pointer (BuiltinType S32Ty)
        let owner = Owner base
        let t = tLocalName "T0"
        let bindings = Map.fromList [( ftLocalName "T0", (owner, FromContext (ErrorInfo Nothing [] (CustomError "foo") [])) )]

        let res = runUnification ts $ do
                State.modify $ \s -> s { usBindings = bindings }
                void $ subtype t owner GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "handles subtyping between Var-wrapped pointer and qualified pointer" $ do
        let p = Pointer (BuiltinType S32Ty)
        let constP = Pointer (Const (BuiltinType S32Ty))
        let varP = TS.toLocal 0 TS.TopLevel $ Var (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "p")) p

        let res = runUnification ts (subtype varP constP GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "unify preserves Owner when binding to Template" $ do
        let p = Pointer (BuiltinType S32Ty)
        let ownerP = Owner p
        let t = tLocalName "T0"
        let res = runUnification ts (unify ownerP t GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (Owner _, _) -> True; _ -> False })

    it "handles My_Struct with recursive ownership subtyping" $ do
        -- struct My_Struct { struct My_Struct *_Owned next; }
        -- Represented as T = My_Struct<_Owned T*>
        let t = tLocalName "T"
        let my_struct_t = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "My_Struct")) [Owner (Pointer (Template (TS.TIdName "T") Nothing))]
        let res = runUnification ts $ do
                void $ unify t my_struct_t GeneralMismatch Nothing []
                void $ subtype t t GeneralMismatch Nothing []
        urErrors res `shouldSatisfy` null

    it "disallows subtyping between different ExternalTypes" $ do
        let t1 = TS.toLocal 0 TS.TopLevel $ ExternalType (C.L (C.AlexPn 0 0 0) C.IdStdType (TS.TIdName "va_list"))
        let t2 = TS.toLocal 0 TS.TopLevel $ ExternalType (C.L (C.AlexPn 0 0 0) C.IdStdType (TS.TIdName "foo_t"))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "handles subtyping from smaller integer to larger integer" $ do
        -- uint8_t <: uint32_t
        let t1 = BuiltinType U08Ty
        let t2 = BuiltinType U32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping from signed to unsigned (allowed in Hic for simplicity)" $ do
        -- int8_t <: uint32_t
        let t1 = BuiltinType S08Ty
        let t2 = BuiltinType U32Ty
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows T** to const T* const* subtyping (C soundness rule)" $ do
        -- int** <: const int* const* (allowed)
        let t1 = Pointer (Pointer (BuiltinType S32Ty))
        let t2 = Pointer (Const (Pointer (Const (BuiltinType S32Ty))))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "allows T*** to T* const* const* subtyping (sound multi-level conversion)" $ do
        -- Soundness explanation:
        -- int*** <: int* const* const* is sound because every level where a qualifier is
        -- added (Level 2: adding const, Level 3: adding const) is "shielded" by a const
        -- qualifier at all outer levels (Level 1: const, Level 2: const).
        --
        -- Bug prevention:
        -- In a conversion int*** -> P, a bug could only occur if P allowed us to write
        -- a 'const int*' into a memory location that the source expects to be 'int*'.
        -- However, since the intermediate level (Level 1) in the target is 'const',
        -- the compiler/solver prevents any modification of that intermediate pointer,
        -- thus "shielding" the non-const source from having const-data smuggled into it.
        let t1 = Pointer (Pointer (Pointer (BuiltinType S32Ty)))
        let t2 = Pointer (Const (Pointer (Const (Pointer (BuiltinType S32Ty)))))
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "handles subtyping between literal integers and Singletons" $ do
        -- 42 <: int(42)
        let t1 = TS.toLocal 0 TS.TopLevel $ IntLit (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "42"))
        let t2 = Singleton S32Ty 42
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "unifies arrays with compatible dimensions" $ do
        -- int[10] <: int[10]
        let t1 = TS.toLocal 0 TS.TopLevel $ Array (Just (BuiltinType S32Ty)) [IntLit (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "10"))]
        let t2 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 10]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "disallows subtyping between arrays with incompatible dimensions" $ do
        -- int[10] <: int[20]
        let t1 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 10]
        let t2 = Array (Just (BuiltinType S32Ty)) [Singleton S32Ty 20]
        let res = runUnification ts (subtype t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "expands function typedefs in resolveType" $ do
        -- typedef void ident(void *p);
        let tsWithIdent = Map.fromList [("ident", TS.FuncDescr (C.L (C.AlexPn 0 0 0) C.IdVar "ident") [] (BuiltinType VoidTy) [Pointer (BuiltinType VoidTy)])]
        let t = TS.toLocal 0 TS.TopLevel $ TypeRef FuncRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "ident")) []
        let resolved = runUnifyWithBindings tsWithIdent Map.empty (resolveType t)
        resolved `shouldBe` Function (BuiltinType VoidTy) [Pointer (BuiltinType VoidTy)]

    it "unifies TypeRefs with identical template arguments" $ do
        -- Tox<int> = Tox<int>
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [BuiltinType S32Ty]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [BuiltinType S32Ty]
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null

    it "unifies TypeRefs with unassigned template parameters" $ do
        -- Tox<T0> = Tox<int>  => T0 = int
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [Template (TS.TIdName "T0") Nothing]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [BuiltinType S32Ty]
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        urErrors res `shouldSatisfy` null
        Map.lookup (ftLocalName "T0") (urBindings res) `shouldSatisfy` (\case { Just (BuiltinType S32Ty, _) -> True; _ -> False })

    it "disallows unification of TypeRefs with conflicting template arguments" $ do
        -- Tox<int> = Tox<float> => ERROR
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [BuiltinType S32Ty]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [BuiltinType F32Ty]
        let res = runUnification ts (unify t1 t2 GeneralMismatch Nothing [])
        length (urErrors res) `shouldSatisfy` (> 0)

    it "detects conflicts through shared template parameters in TypeRefs" $ do
        -- T0 = int; Tox<T0> = Tox<float> => ERROR
        let t0 = ftLocalName "T0"
        let initialBindings = Map.fromList [( t0, (BuiltinType S32Ty, FromContext (ErrorInfo Nothing [] (CustomError "init") [])) )]
        let t1 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [Template (TS.TIdName "T0") Nothing]
        let t2 = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) [BuiltinType F32Ty]
        let finalState = State.execState (void $ unify t1 t2 GeneralMismatch Nothing []) (UnifyState initialBindings (buildBindingsIndex initialBindings) [] ts Set.empty 0 True)
        length (usErrors finalState) `shouldSatisfy` (> 0)

    it "detects conflict between Template (bound to Struct) and Builtin" $ do
        let t0 = ftLocalName "T0"
            structTy = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "My_Struct")) []
            intTy = BuiltinType S32Ty
            initialBindings = Map.fromList [(t0, (structTy, FromContext (ErrorInfo Nothing [] (CustomError "init") [])))]
            finalState = State.execState (void $ unify (Template (TS.ftId t0) (TS.ftIndex t0)) intTy GeneralMismatch Nothing []) (UnifyState initialBindings (buildBindingsIndex initialBindings) [] ts Set.empty 0 True)
        length (usErrors finalState) `shouldSatisfy` (> 0)

    it "preserves template arguments of StructRef in resolveType" $ do
        let structName = "Tox"
            descr = TS.StructDescr (C.L (C.AlexPn 0 0 0) C.IdVar structName) [TS.TIdName "T"] [] []
            tsWithStruct = Map.fromList [(structName, descr)]
            t = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName structName)) [BuiltinType S32Ty]
        let resolved = runUnifyWithBindings tsWithStruct Map.empty (resolveType t)
        resolved `shouldBe` t

    it "resolves nested TypeRef FuncRefs in resolveType" $ do
        let name = "ident"
            descr = TS.FuncDescr (C.L (C.AlexPn 0 0 0) C.IdVar name) [] (BuiltinType VoidTy) [Pointer (BuiltinType VoidTy)]
            tsWithIdent = Map.fromList [(name, descr)]
            t = TS.toLocal 0 TS.TopLevel $ Pointer (TypeRef FuncRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName name)) [])
        let resolved = runUnifyWithBindings tsWithIdent Map.empty (resolveType t)
        resolved `shouldBe` Pointer (Function (BuiltinType VoidTy) [Pointer (BuiltinType VoidTy)])

    it "detects conflicts through subtyping chain (Tox case repro)" $ do
        let t_tox = tLocalName "T_tox"
        let t_inv = tLocalName "T_inv"
        let t_hnd = tLocalName "T_hnd"
        let my_data = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "My_Data")) []
        let int_ty = BuiltinType S32Ty

        let res = runUnification ts $ do
                void $ subtype t_tox t_inv GeneralMismatch Nothing []
                void $ subtype t_inv t_hnd GeneralMismatch Nothing []
                void $ unify t_hnd my_data GeneralMismatch Nothing []
                void $ unify t_tox int_ty GeneralMismatch Nothing []

        let isMyDataIntMismatch = \case
                ErrorInfo { errType = TypeMismatch t1 t2 _ _ } ->
                    (t1 == my_data && t2 == int_ty) || (t1 == int_ty && t2 == my_data)
                _ -> False
        any isMyDataIntMismatch (urErrors res) `shouldBe` True

    it "detects conflicts through linked template parameters (bug reproduction)" $ do
        -- Reproduces bug where T1 -> T2, then T2 -> struct S, then T1 -> int succeeds (should fail)
        let t1 = tLocalName "T1"
        let t2 = tLocalName "T2"
        let struct_s = TS.toLocal 0 TS.TopLevel $ TypeRef StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "S")) []
        let int_ty = BuiltinType S32Ty

        let res = runUnification ts $ do
                void $ unify t1 t2 GeneralMismatch Nothing [] -- T1 -> T2
                void $ unify t2 struct_s GeneralMismatch Nothing [] -- T2 -> S
                void $ unify t1 int_ty GeneralMismatch Nothing [] -- T1 -> int (should fail)
        length (urErrors res) `shouldSatisfy` (> 0)

-- end of tests
