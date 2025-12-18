{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Core.BaseSpec (spec) where

import           Data.Fix                          (unFix)
import           Data.Map.Strict                   (Map)
import qualified Data.Map.Strict                   as Map
import           Data.Text                         (Text)
import qualified Language.Cimple                   as C
import           Language.Cimple.Program           as Program
import           Language.Hic.TestUtils            (mustParse)
import qualified Language.Hic.TypeSystem.Core.Base as TS
import           Test.Hspec

spec :: Spec
spec = do
    it "normalizes templates in structs" $ do
        prog <- mustParse ["struct My_Struct { void *a; void *b; };"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ tps members _) -> do
                tps `shouldBe` [TS.TIdParam 0 (Just "a") TS.TopLevel, TS.TIdParam 1 (Just "b") TS.TopLevel]
                length members `shouldBe` 2
                case members of
                    [(_, tyA), (_, tyB)] -> do
                        tyA `shouldBe` TS.Pointer (TS.Template (TS.TIdParam 0 (Just "a") TS.TopLevel) Nothing)
                        tyB `shouldBe` TS.Pointer (TS.Template (TS.TIdParam 1 (Just "b") TS.TopLevel) Nothing)
                    _ -> expectationFailure "Expected 2 members"
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

    it "reuses named templates" $ do
        prog <- mustParse
            [ "typedef void *Generic;"
            , "struct My_Struct { Generic a; Generic b; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ tps _ _) -> do
                tps `shouldBe` [TS.TIdParam 0 (Just "") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

    it "handles function pointers in structs correctly" $ do
        prog <- mustParse
            [ "typedef void my_cb(void *obj);"
            , "struct My_Struct { my_cb *f; void *o; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ tps _ _) -> do
                -- Both 'f' and 'o' now have independent templates.
                tps `shouldBe` [TS.TIdParam 0 (Just "obj") TS.TopLevel, TS.TIdParam 1 (Just "o") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

    it "lookups system structs" $ do
        -- Test that internal definitions for sockaddr etc are available
        case TS.lookupType "sockaddr" Map.empty of
            Just (TS.StructDescr _ _ members _) -> do
                let names = [ C.lexemeText l | (l, _) <- members ]
                names `shouldContain` ["sa_family", "sa_data"]
            _ -> expectationFailure "Expected system StructDescr for 'sockaddr'"

    it "identifies Tox<T> pattern as templated" $ do
        prog <- mustParse ["struct Tox { void *userdata; };"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Tox" ts of
            Just (TS.StructDescr _ tps _ _) ->
                tps `shouldBe` [TS.TIdParam 0 (Just "userdata") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'Tox'"

    it "handles recursive templates in structs" $ do
        prog <- mustParse ["struct List { void *data; struct List *next; };"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "List" ts of
            Just (TS.StructDescr _ tps members _) -> do
                tps `shouldBe` [TS.TIdParam 0 (Just "data") TS.TopLevel]
                case lookup "next" [ (C.lexemeText l, t) | (l, t) <- members ] of
                    Just (TS.Pointer (TS.TypeRef TS.StructRef _ [TS.Template (TS.TIdParam 0 (Just "data") TS.TopLevel) Nothing])) -> return ()
                    res -> expectationFailure $ "Expected recursive TypeRef with template, got: " ++ show res
            _ -> expectationFailure "Expected StructDescr for 'List'"

    it "resolveRef populates missing template arguments for structs" $ do
        prog <- mustParse ["struct Tox { void *userdata; };"]
        let ts = TS.collect (Program.toList prog)
        let ty = TS.TypeRef TS.StructRef (C.L (C.AlexPn 0 0 0) C.IdSueType (TS.TIdName "Tox")) []
        let resolved = TS.resolveRef ts ty
        case resolved of
            TS.TypeRef TS.StructRef _ [TS.Template (TS.TIdParam 0 (Just "userdata") TS.TopLevel) Nothing] -> return ()
            _ -> expectationFailure $ "Expected resolveRef to populate templates, got: " ++ show resolved

    it "resolveRef populates missing template arguments for functions" $ do
        prog <- mustParse ["void tox_handler(void *userdata) { /* comment */ }"]
        let ts = TS.collect (Program.toList prog)
        let ty = TS.TypeRef TS.FuncRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "tox_handler")) []
        let resolved = TS.resolveRef ts ty
        case resolved of
            TS.TypeRef TS.FuncRef _ [TS.Template (TS.TIdParam 0 (Just "userdata") TS.TopLevel) Nothing] -> return ()
            _ -> expectationFailure $ "Expected resolveRef to populate templates for function, got: " ++ show resolved

    it "resolveRef propagates template arguments through aliases" $ do
        prog <- mustParse
            [ "struct Tox { void *userdata; };"
            , "typedef struct Tox Memory;"
            ]
        let ts = TS.collect (Program.toList prog)
        -- ty is Memory<int>
        let ty = TS.TypeRef TS.UnresolvedRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "Memory")) [TS.BuiltinType TS.S32Ty]
        let resolved = TS.resolveRef ts ty
        case resolved of
            TS.TypeRef TS.StructRef _ [TS.BuiltinType TS.S32Ty] -> return ()
            _ -> expectationFailure $ "Expected substitute int into Tox, got: " ++ show resolved

    it "resolveRef substitutes arguments into aliases" $ do
        prog <- mustParse
            [ "struct Tox { void *userdata; };"
            , "typedef struct Tox Memory;"
            ]
        let ts = TS.collect (Program.toList prog)
        -- Memory<int>
        let ty = TS.TypeRef TS.UnresolvedRef (C.L (C.AlexPn 0 0 0) C.IdVar (TS.TIdName "Memory")) [TS.BuiltinType TS.S32Ty]
        let resolved = TS.resolveRef ts ty
        case resolved of
            TS.TypeRef TS.StructRef _ [TS.BuiltinType TS.S32Ty] -> return ()
            _ -> expectationFailure $ "Expected substitute int into Tox, got: " ++ show resolved

    it "resolveRef substitutes into nested templated structs through aliases" $ do
        prog <- mustParse
            [ "struct Inner { void *ptr; };"
            , "typedef struct Inner Alias;"
            , "struct Outer { Alias *a; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Outer" ts of
            Just (TS.StructDescr _ _ [(_, TS.Pointer (TS.TypeRef TS.StructRef _ [TS.Template (TS.TIdParam 0 (Just "ptr") TS.TopLevel) Nothing]))] _) -> return ()
            _ -> expectationFailure "Expected StructDescr for 'Outer'"

    it "propagates templates from nested structs to parent struct" $ do
        prog <- mustParse
            [ "struct Inner { void *ptr; };"
            , "struct Outer { struct Inner inner; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Outer" ts of
            Just (TS.StructDescr _ tps _ _) ->
                tps `shouldBe` [TS.TIdParam 0 (Just "ptr") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'Outer' to have templates from 'Inner'"

    it "propagates templates from nested structs in arrays to parent struct" $ do
        prog <- mustParse
            [ "struct Inner { void *ptr; };"
            , "struct Outer { struct Inner inner[10]; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Outer" ts of
            Just (TS.StructDescr _ tps _ _) ->
                tps `shouldBe` [TS.TIdParam 0 (Just "ptr") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'Outer' to have templates from 'Inner' (array)"

    it "resolves typedef chains" $ do
        prog <- mustParse
            [ "typedef int My_Int;"
            , "typedef My_Int My_Int_Alias;"
            , "struct My_Struct { My_Int_Alias x; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ _ [(_, TS.BuiltinType TS.S32Ty)] _) -> return ()
            _ -> expectationFailure "Expected StructDescr for 'My_Struct' with resolved int member"

    it "handles built-in va_list" $ do
        prog <- mustParse ["void f(va_list args);"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "f" ts of
            Just (TS.FuncDescr _ _ _ [TS.Var _ ty]) ->
                case ty of
                    TS.ExternalType _ -> return ()
                    _ -> expectationFailure $ "Expected ExternalType for va_list, got: " ++ show ty
            _ -> expectationFailure "Expected FuncDescr for 'f'"

    it "collects enums" $ do
        prog <- mustParse ["enum My_Color { RED, GREEN, BLUE };"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Color" ts of
            Just (TS.EnumDescr _ _) -> return ()
            _ -> expectationFailure "Expected EnumDescr for 'My_Color'"

    it "instantiates templated structs" $ do
        prog <- mustParse ["struct My_Struct { void *ptr; };"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just descr -> do
                let instantiated :: TS.TypeDescr TS.Local
                    instantiated = TS.instantiateDescr 0 TS.TopLevel (Map.singleton (TS.TIdParam 0 (Just "ptr") TS.TopLevel) (TS.BuiltinType TS.S32Ty)) descr
                case instantiated of
                    TS.StructDescr _ [] [(_, TS.Pointer (TS.BuiltinType TS.S32Ty))] [] -> return ()
                    _ -> expectationFailure $ "Expected instantiated StructDescr, got: " ++ show instantiated
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

    it "collects function signatures" $ do
        prog <- mustParse ["void f(int x, void *p);"]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "f" ts of
            Just (TS.FuncDescr _ tps ret params) -> do
                tps `shouldBe` [TS.TIdParam 0 (Just "p") TS.TopLevel]
                ret `shouldBe` TS.BuiltinType TS.VoidTy
                params `shouldSatisfy` \ps -> length ps == 2
            _ -> expectationFailure "Expected FuncDescr for 'f'"

    it "propagates templates through aliases" $ do
        prog <- mustParse
            [ "struct Tox { void *userdata; };"
            , "typedef struct Tox Memory;"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Memory" ts of
            Just (TS.AliasDescr _ [_] _) -> return ()
            _ -> expectationFailure "Expected AliasDescr for 'Memory' with 1 template"

    it "reaches a stable fixpoint for mutually recursive types" $ do
        prog <- mustParse
            [ "struct My_B;"
            , "struct My_A { struct My_B *b; };"
            , "struct My_B { struct My_A *a; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_A" ts of
            Just (TS.StructDescr _ _ [(_, TS.Pointer (TS.TypeRef TS.StructRef _ []))] _) -> return ()
            _ -> expectationFailure "Expected StructDescr for 'My_A'"

    it "handles _Owned, _Nonnull, and _Nullable qualifiers" $ do
        prog <- mustParse
            [ "struct My_Struct {"
            , "    int *_Owned p_owned;"
            , "    int *_Nonnull p_nonnull;"
            , "    int *_Nullable p_nullable;"
            , "};"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ _ members _) -> do
                let mTypes = map snd members
                mTypes `shouldBe` [ TS.Owner (TS.Pointer (TS.BuiltinType TS.S32Ty))
                                  , TS.Nonnull (TS.Pointer (TS.BuiltinType TS.S32Ty))
                                  , TS.Nullable (TS.Pointer (TS.BuiltinType TS.S32Ty))
                                  ]
            _ -> expectationFailure $ "Expected StructDescr for 'My_Struct', got: " ++ show (Map.keys ts)

    it "joins sizers for Sized types" $ do
        prog <- mustParse
            [ "struct My_Struct {"
            , "    int *data;"
            , "    uint32_t data_length;"
            , "};"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ _ [(_, TS.Sized (TS.Pointer (TS.BuiltinType TS.S32Ty)) _)] _) -> return ()
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

    it "handles _Owned in joinSizer" $ do
        prog <- mustParse
            [ "struct My_Struct {"
            , "    int *_Owned data;"
            , "    uint32_t data_length;"
            , "};"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ _ members _) -> do
                let memberMap = Map.fromList [ (C.lexemeText l, ty) | (l, ty) <- members ]
                case Map.lookup "data" memberMap of
                    Just (TS.Sized (TS.Owner (TS.Pointer (TS.BuiltinType TS.S32Ty))) l)
                        | TS.templateIdBaseName (C.lexemeText l) == "data_length" -> return ()
                    other -> expectationFailure $ "Expected Sized Owner type for 'data', got: " ++ show other
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

    it "stabilizes templates for Logger-style mutual recursion" $ do
        prog <- mustParse
            [ "struct Logger { void *ctx; struct App *app; };"
            , "struct App { void *state; struct Logger *logger; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Logger" ts of
            Just (TS.StructDescr _ tps _ _) -> do
                -- Both Logger and App templates are now independent
                tps `shouldBe` [TS.TIdParam 0 (Just "ctx") TS.TopLevel, TS.TIdParam 1 (Just "state") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'Logger'"

    it "terminates on self-referential template expansion (Tox_Memory pattern)" $ do
        prog <- mustParse
            [ "typedef void dealloc_cb(void *ptr);"
            , "struct Memory { dealloc_cb *dealloc; void *ptr; };"
            ]
        -- This forces resolve to handle:
        -- Memory<P0, P1> = { dealloc: (Memory<P0, P1>*) -> void, ptr: P1 }
        -- where P0 is derived from the dealloc_cb template.
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "Memory" ts of
            Just (TS.StructDescr _ tps _ _) -> do
                length tps `shouldSatisfy` (> 0)
            _ -> expectationFailure "Expected StructDescr for 'Memory'"

    it "propagates all templates from structs to function signatures" $ do
        prog <- mustParse
            [ "struct My_Struct { void *a; void *b; };"
            , "void f(struct My_Struct *s);"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_Struct" ts of
            Just (TS.StructDescr _ tps _ _) -> tps `shouldBe` [TS.TIdParam 0 (Just "a") TS.TopLevel, TS.TIdParam 1 (Just "b") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'My_Struct'"

        case Map.lookup "f" ts of
            Just (TS.FuncDescr _ tps _ _) -> tps `shouldBe` [TS.TIdParam 0 (Just "a") TS.TopLevel, TS.TIdParam 1 (Just "b") TS.TopLevel]
            _ -> expectationFailure "Expected FuncDescr for 'f'"

    it "does not incorrectly merge independent templates during multi-pass resolution" $ do
        prog <- mustParse
            [ "struct My_A { void *p; };"
            , "struct My_B { struct My_A *a; void *q; };"
            ]
        let ts = TS.collect (Program.toList prog)
        case Map.lookup "My_B" ts of
            Just (TS.StructDescr _ tps _ _) -> tps `shouldBe` [TS.TIdParam 0 (Just "p") TS.TopLevel, TS.TIdParam 1 (Just "q") TS.TopLevel]
            _ -> expectationFailure "Expected StructDescr for 'My_B' with 2 templates"

    it "toLocal preserves template identity" $ do
        let p0 = TS.TIdParam 0 Nothing TS.TopLevel
        let p1 = TS.TIdParam 1 Nothing TS.TopLevel
        let l0 = TS.toLocal 0 TS.TopLevel (TS.Template p0 Nothing)
        let l1 = TS.toLocal 0 TS.TopLevel (TS.Template p1 Nothing)
        l0 `shouldNotBe` l1

    describe "Topological Resolution" $ do
        it "resolves a chain of aliases in correct order" $ do
            let p = TS.TIdName
                l = C.L (C.AlexPn 0 0 0) C.IdVar
                -- C -> B -> A -> int
                tys = Map.fromList
                    [ ("C", TS.AliasDescr (l "C") [] (TS.TypeRef TS.UnresolvedRef (l (p "B")) []))
                    , ("B", TS.AliasDescr (l "B") [] (TS.TypeRef TS.UnresolvedRef (l (p "A")) []))
                    , ("A", TS.AliasDescr (l "A") [] (TS.BuiltinType TS.S32Ty))
                    ]
                resolved = TS.resolve tys

            case Map.lookup "C" resolved of
                Just (TS.AliasDescr _ _ target) -> target `shouldBe` TS.BuiltinType TS.S32Ty
                _ -> expectationFailure "C should be an alias to S32"

        it "handles mutual recursion without infinite loops" $ do
            let p = TS.TIdName
                l = C.L (C.AlexPn 0 0 0) C.IdVar
                -- A -> B*, B -> A*
                tys = Map.fromList
                    [ ("A", TS.AliasDescr (l "A") [] (TS.Pointer (TS.TypeRef TS.UnresolvedRef (l (p "B")) [])))
                    , ("B", TS.AliasDescr (l "B") [] (TS.Pointer (TS.TypeRef TS.UnresolvedRef (l (p "A")) [])))
                    ]
                -- resolution should stop and leave them as pointers to the cyclic ref
                resolved = TS.resolve tys
            Map.member "A" resolved `shouldBe` True
            Map.member "B" resolved `shouldBe` True
