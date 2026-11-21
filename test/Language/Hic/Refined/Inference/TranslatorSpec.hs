{-# LANGUAGE GADTs               #-}
{-# LANGUAGE OverloadedStrings   #-}
{-# LANGUAGE ScopedTypeVariables #-}
module Language.Hic.Refined.Inference.TranslatorSpec (spec) where

import           Control.Monad.State.Strict                (runState)
import           Data.Fix                                  (Fix (..))
import qualified Data.Map.Strict                           as Map
import qualified Data.Set                                  as Set
import           Data.Word                                 (Word32)
import qualified Language.Cimple                           as C
import           Language.Hic.Refined.Inference.Translator
import           Language.Hic.Refined.Inference.Types
import           Language.Hic.Refined.Registry
import           Language.Hic.Refined.Types
import qualified Language.Hic.TypeSystem.Core.Base         as TS
import           Test.Hspec

spec :: Spec
spec = do
    let emptyTS = Map.empty :: TS.TypeSystem
    let st0 = emptyTranslatorState emptyTS

    describe "translateStdType" $ do
        it "maps BoolTy correctly" $ do
            translateStdType TS.BoolTy `shouldBe` Just BoolTy
        it "maps VoidTy to Nothing" $ do
            translateStdType TS.VoidTy `shouldBe` Nothing

    describe "translateType" $ do
        it "translates int32_t to VBuiltin S32Ty" $ do
            let ty = TS.builtin (dummyL "int32_t")
            let (nid, st) = runState (translateType ty) st0
            Map.lookup nid (tsNodes st) `shouldBe` Just (AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))

        it "translates pointer types" $ do
            let ty = TS.Pointer (TS.builtin (dummyL "int32_t"))
            let (nid, st) = runState (translateType ty) st0
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr (TargetObject innerId)) _ _ _)) ->
                    Map.lookup (innerId :: Word32) (tsNodes st) `shouldBe` Just (AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
                _ -> expectationFailure "Expected nid to be a pointer to int32_t"

        it "handles void* by creating a fresh template parameter" $ do
            let ty = TS.Pointer (TS.builtin (dummyL "void"))
            let (nid1, st1) = runState (translateType ty) st0
            let (nid2, _) = runState (translateType ty) st1
            nid1 `shouldNotBe` nid2

        it "preserves const qualifiers" $ do
            let ty = TS.Const (TS.builtin (dummyL "int32_t"))
            let (nid, st) = runState (translateType ty) st0
            Map.lookup nid (tsNodes st) `shouldBe` Just (AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals True False)))

        it "handles nested pointers (Recursive Translation)" $ do
            let ty = TS.Pointer (TS.Pointer (TS.builtin (dummyL "int32_t")))
            let (nid, st) = runState (translateType ty) st0
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr (TargetObject p1)) _ _ _)) ->
                    case Map.lookup p1 (tsNodes st) of
                        Just (AnyRigidNodeF (RReference (Ptr (TargetObject p2)) _ _ _)) ->
                            Map.lookup p2 (tsNodes st) `shouldBe` Just (AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False)))
                        _ -> expectationFailure "Expected p1 to be a pointer"
                _ -> expectationFailure "Expected nid to be a pointer"

        it "returns a VNominal type for a nominal type even if an existential is registered" $ do
            let baseName = "My_Callback"
            let ty = TS.TypeRef TS.StructRef (dummyL (TS.TIdName baseName)) []
            let existId = 100
            let st = st0 { tsExistentials = Map.singleton baseName existId }
            let (nid, st') = runState (translateType ty) st
            nid `shouldNotBe` existId
            case Map.lookup nid (tsNodes st') of
                Just (AnyRigidNodeF (RObject (VNominal l _) _)) ->
                    C.lexemeText l `shouldBe` TIdName baseName
                _ -> expectationFailure "Expected nid to be a VNominal"

        it "returns a VNominal type for a nominal type with generic parameters" $ do
            let baseName = "My_Callback"
            let param = TS.Template (TS.TIdParam 0 Nothing TS.TopLevel) Nothing
            let ty = TS.TypeRef TS.StructRef (dummyL (TS.TIdName baseName)) [param]
            let existId = 100
            let st = st0 { tsExistentials = Map.singleton baseName existId }
            let (nid, st') = runState (translateType ty) st
            nid `shouldNotBe` existId
            case Map.lookup nid (tsNodes st') of
                Just (AnyRigidNodeF (RObject (VNominal l _) _)) ->
                    C.lexemeText l `shouldBe` TIdName baseName
                _ -> expectationFailure "Expected nid to be a VNominal"

    describe "translateRegistry" $ do
        let param i = TS.TIdParam i Nothing TS.TopLevel
            field name ty = (dummyL name, ty)
            ref name args = TS.TypeRef TS.StructRef (dummyL (TS.TIdName name)) (map (`TS.Template` Nothing) args)
            struct name ps ms = (name, TS.StructDescr (dummyL name) ps ms [])
            -- The type system gives Outer the parameter of the Inner it points to.
            ts = Map.fromList
                [ struct "Inner" [param 0] [field "data" (TS.Pointer (TS.Template (param 0) Nothing))]
                , struct "Outer" [param 0, param 1]
                    [ field "data" (TS.Pointer (TS.Template (param 0) Nothing))
                    , field "inner" (TS.Pointer (ref "Inner" [param 1]))
                    ]
                , struct "Holder" [param 0] [field "inner" (ref "Inner" [param 0])]
                ]
            params name st = case Map.lookup name (regDefinitions (fst st)) of
                Just (StructDef _ ps _) -> map fst ps
                _                       -> error ("no struct " ++ show name)
            translated = runState (translateRegistry ts) (emptyTranslatorState ts)

        it "gives a struct only the parameters of its own storage" $ do
            params "Outer" translated `shouldBe` [translateTemplateIdGlobal (param 0)]

        it "keeps the parameters of a struct held by value" $ do
            params "Holder" translated `shouldBe` [translateTemplateIdGlobal (param 0)]

        it "gives a struct behind a pointer no arguments" $ do
            let (nid, st) = runState (translateType (TS.Pointer (ref "Inner" [param 2]))) (snd translated)
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr (TargetObject o)) _ _ _)) -> case Map.lookup o (tsNodes st) of
                    Just (AnyRigidNodeF (RObject (VNominal _ args) _)) -> args `shouldBe` []
                    other -> expectationFailure $ "Expected a VNominal, got " ++ show other
                other -> expectationFailure $ "Expected a pointer, got " ++ show other

        it "takes a reference with fewer arguments than parameters as to any instance" $ do
            -- What the type system gives a reference inside a group of types
            -- that refer to each other.
            let (nid, st) = runState (translateType (ref "Outer" [param 2])) (snd translated)
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RObject (VNominal _ args) _)) -> args `shouldBe` []
                _ -> expectationFailure "Expected a VNominal"

        it "drops the arguments of a struct's parameters that aren't its own" $ do
            let (nid, st) = runState (translateType (ref "Outer" [param 2, param 3])) (snd translated)
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RObject (VNominal _ args) _)) -> length args `shouldBe` 1
                _ -> expectationFailure "Expected a VNominal"

    describe "translateType (Function Pointers)" $ do
        it "gives a pointer to a function typedef the reference's arguments" $ do
            -- typedef void cb(void *data); and a cb * whose data is param 5.
            let own = TS.TIdParam 0 Nothing TS.TopLevel
                arg = TS.TIdParam 5 Nothing TS.TopLevel
                cbTy = TS.FuncDescr (dummyL "cb") [own] (TS.BuiltinType TS.VoidTy) [TS.Template own Nothing]
                ts = Map.singleton "cb" cbTy
                ref = TS.Pointer (TS.TypeRef TS.FuncRef (dummyL (TS.TIdName "cb")) [TS.Template arg Nothing])
                (nid, st) = runState (translateType ref) (emptyTranslatorState ts)
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr (TargetFunction [a] _)) _ _ _)) ->
                    Map.lookup a (tsNodes st) `shouldBe` Just (AnyRigidNodeF (RObject (VVar (translateTemplateIdGlobal arg) Nothing) (Quals False False)))
                other -> expectationFailure $ "Expected a function pointer, got " ++ show other

        it "pairs a function typedef reference's arguments with its own parameters" $ do
            -- typedef void cb(struct S *s, void *data); where S<a> gives cb
            -- the parameter a, and the reference has an argument for data only.
            let a = TS.TIdParam 0 Nothing TS.TopLevel
                own = TS.TIdParam 1 Nothing TS.TopLevel
                arg = TS.TIdParam 5 Nothing TS.TopLevel
                sRef = TS.TypeRef TS.StructRef (dummyL (TS.TIdName "S")) [TS.Template a Nothing]
                ts = Map.fromList
                    [ ("S", TS.StructDescr (dummyL "S") [a] [(dummyL "x", TS.Pointer (TS.Template a Nothing))] [])
                    , ("cb", TS.FuncDescr (dummyL "cb") [a, own] (TS.BuiltinType TS.VoidTy) [TS.Pointer sRef, TS.Template own Nothing])
                    ]
                ref' = TS.Pointer (TS.TypeRef TS.FuncRef (dummyL (TS.TIdName "cb")) [TS.Template arg Nothing])
                (nid, st) = runState (translateRegistry ts >> translateType ref') (emptyTranslatorState ts)
            case Map.lookup nid (tsNodes st) of
                Just (AnyRigidNodeF (RReference (Ptr (TargetFunction [_, d] _)) _ _ _)) ->
                    Map.lookup d (tsNodes st) `shouldBe` Just (AnyRigidNodeF (RObject (VVar (translateTemplateIdGlobal arg) Nothing) (Quals False False)))
                other -> expectationFailure $ "Expected a function pointer, got " ++ show other

    describe "translateType (Array Elements)" $ do
        it "favors existential types for array elements" $ do
            let baseName = "My_Callback"
            let elemTy = TS.TypeRef TS.StructRef (dummyL (TS.TIdName baseName)) []
            let arrayTy = TS.Array (Just elemTy) []
            let existId = 100
            let st = st0 { tsExistentials = Map.singleton baseName existId }
            let (nid, st') = runState (translateType arrayTy) st
            case Map.lookup nid (tsNodes st') of
                Just (AnyRigidNodeF (RReference (Arr innerId _) _ _ _)) ->
                    innerId `shouldBe` existId
                _ -> expectationFailure "Expected nid to be an array with existential elements"

    describe "translateTemplateIdGlobal" $ do
        it "maps TIdName" $ do
            translateTemplateIdGlobal (TS.TIdName "foo") `shouldBe` TIdName "foo"
        it "maps TIdParam" $ do
            translateTemplateIdGlobal (TS.TIdParam 5 (Just "T") TS.TopLevel) `shouldBe` TIdParam PGlobal 5 (Just "T")

    describe "translateType' (Constructors)" $ do
        it "translates NameLitF to VEnum" $ do
            let ty = TS.NameLit (dummyL (TS.TIdName "MY_CONST"))
            let (node, _) = runState (translateType' ty) st0
            node `shouldBe` AnyRigidNodeF (RObject (VEnum (dummyL (TIdName "MY_CONST"))) (Quals False False))

        it "translates EnumMemF to VEnum" $ do
            let ty = TS.EnumMem (dummyL (TS.TIdName "MY_ENUM_MEM"))
            let (node, _) = runState (translateType' ty) st0
            node `shouldBe` AnyRigidNodeF (RObject (VEnum (dummyL (TIdName "MY_ENUM_MEM"))) (Quals False False))

        it "translates ExternalTypeF to VNominal" $ do
            let ty = TS.ExternalType (dummyL (TS.TIdName "pthread_mutex_t"))
            let (node, _) = runState (translateType' ty) st0
            node `shouldBe` AnyRigidNodeF (RObject (VNominal (dummyL (TIdName "pthread_mutex_t")) []) (Quals False False))

        it "translates UnconstrainedF to SAny" $ do
            let ty = TS.Unconstrained
            let (node, _) = runState (translateType' ty) st0
            node `shouldBe` AnyRigidNodeF (RTerminal SAny)

        it "translates ProxyF by recursing" $ do
            let ty = TS.Proxy (TS.builtin (dummyL "int32_t"))
            let (node, _) = runState (translateType' ty) st0
            node `shouldBe` AnyRigidNodeF (RObject (VBuiltin S32Ty) (Quals False False))

dummyL :: t -> C.Lexeme t
dummyL = C.L (C.AlexPn 0 0 0) C.IdSueType
