{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE GADTs             #-}
{-# LANGUAGE LambdaCase        #-}
{-# LANGUAGE MonoLocalBinds    #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Ordered.ConstraintGenerationSpec (spec) where

import           Data.Fix                                             (Fix (..),
                                                                       foldFix)
import           Data.Map.Strict                                      (Map)
import qualified Data.Map.Strict                                      as Map
import           Data.Text                                            (Text)
import qualified Language.Cimple                                      as C
import qualified Language.Cimple.Program                              as Program
import           Language.Hic.TestUtils                               (mustParse)
import           Language.Hic.TypeSystem.Core.Base                    (Phase (..),
                                                                       TypeInfo,
                                                                       pattern BuiltinType,
                                                                       pattern Pointer,
                                                                       pattern Singleton,
                                                                       pattern Template,
                                                                       pattern TypeRef)
import qualified Language.Hic.TypeSystem.Core.Base                    as TS
import           Language.Hic.TypeSystem.Ordered.ArrayUsage           (runArrayUsageAnalysis)
import           Language.Hic.TypeSystem.Ordered.ConstraintGeneration
import qualified Language.Hic.TypeSystem.Ordered.HotspotAnalysis      as GSA
import           Language.Hic.TypeSystem.Ordered.Nullability          (runNullabilityAnalysis)
import           Test.Hspec

runCG :: Program.Program Text -> ConstraintGenResult
runCG prog =
    let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        aur = runArrayUsageAnalysis ts prog
        nr = runNullabilityAnalysis prog
    in runConstraintGeneration ts aur nr prog

spec :: Spec
spec = do
    it "keeps mixed-access arrays indexed for literal accesses" $ do
        prog <- mustParse
            [ "struct My_Struct { void *h[2]; };"
            , "void set(struct My_Struct *r, int i, void *o) { r->h[i] = o; }"
            , "void f(struct My_Struct *r, int *p) { r->h[0] = p; }"
            ]
        let res = runCG prog

        -- In 'f', the assignment 'r->h[0] = p' should use an indexed template
        -- because even if 'h' is mixed-access, literal access [0] can be specialized.
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- We expect a Subtype constraint where the expected type is indexed
                let isIndexed (Subtype _ (Template _ (Just _)) _ _ _) = True
                    isIndexed _                                       = False
                any isIndexed constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "keeps strictly heterogeneous arrays indexed" $ do
        prog <- mustParse
            [ "struct My_Struct { void *h[2]; };"
            , "void f(struct My_Struct *r, int *p1, float *p2) {"
            , "    r->h[0] = p1;"
            , "    r->h[1] = p2;"
            , "}"
            ]
        let res = runCG prog

        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- We expect Subtype constraints with indexed templates
                let isIndexed (Subtype _ (Template _ (Just _)) _ _ _) = True
                    isIndexed _                                       = False
                filter isIndexed constrs `shouldSatisfy` \cs -> length cs >= 2
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "generates MemberAccess constraints" $ do
        prog <- mustParse
            [ "struct My_Struct { int x; };"
            , "void f(struct My_Struct *s) { s->x = 1; }"
            ]
        let res = runCG prog

        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isHasMember (HasMember _ "x" _ _ _ _) = True
                    isHasMember _                         = False
                any isHasMember constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "resolves typedefs during variable declaration" $ do
        prog <- mustParse
            [ "typedef int My_Int;"
            , "void f() { My_Int x = 1; }"
            ]
        let res = runCG prog

        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- We expect an assignment constraint: 1 (S32) -> x (S32)
                let isIntAssignment (Subtype (BuiltinType TS.S32Ty) (BuiltinType TS.S32Ty) _ _ _) = True
                    isIntAssignment (Subtype (Singleton TS.S32Ty _) (BuiltinType TS.S32Ty) _ _ _) = True
                    isIntAssignment _ = False
                any isIntAssignment constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "handles pointer dereference in assignments" $ do
        prog <- mustParse ["void f(int *p, int x) { *p = x; }"]
        let res = runCG prog

        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- *p (int) = x (int)
                let isIntAssignment (Subtype (BuiltinType TS.S32Ty) (BuiltinType TS.S32Ty) _ _ _) = True
                    isIntAssignment _ = False
                any isIntAssignment constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "resolves struct typedefs" $ do
        prog <- mustParse
            [ "struct My_Struct { int x; };"
            , "typedef struct My_Struct My_Alias;"
            , "void f(My_Alias *s) { s->x = 1; }"
            ]
        let res = runCG prog

        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- We expect a HasMember constraint where the base is My_Struct
                let isMyStructMember (HasMember (TypeRef _ l _) "x" _ _ _ _)
                        | TS.templateIdToText (C.lexemeText l) == "My_Struct" = True
                    isMyStructMember _ = False
                any isMyStructMember constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "generates constraints for ternary expressions" $ do
        prog <- mustParse ["int f(int c, int x, int y) { return c ? x : y; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Expect equality between then and else branches
                let isEquality (Equality (BuiltinType TS.S32Ty) (BuiltinType TS.S32Ty) _ _ _) = True
                    isEquality _ = False
                any isEquality constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles nested struct member access" $ do
        prog <- mustParse
            [ "struct Inner { int x; };"
            , "struct Outer { struct Inner inner; };"
            , "void f(struct Outer *o) { o->inner.x = 1; }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isInnerMember (HasMember _ "inner" _ _ _ _) = True
                    isInnerMember _                             = False
                let isXMember (HasMember _ "x" _ _ _ _) = True
                    isXMember _                         = False
                any isInnerMember constrs `shouldBe` True
                any isXMember constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "emits CoordinatedPair for registration patterns" $ do
        prog <- mustParse
            [ "typedef void my_handler_cb(void *obj);"
            , "void r(my_handler_cb *f, void *o);"
            , "void my_handler(int *x);"
            , "void f(int *p) { r(my_handler, p); }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let containsTemplate' = foldFix $ \case
                        TS.TemplateF _ -> True
                        f              -> any id f
                let isCoordinatedPair (CoordinatedPair _ _ t _ _ _) = containsTemplate' t
                    isCoordinatedPair _                            = False
                any isCoordinatedPair constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "emits CoordinatedPair for non-adjacent callback and data (sort pattern)" $ do
        prog <- mustParse
            [ "typedef int compare_cb(const void *a, const void *b);"
            , "void sort(void *base, int nmemb, int size, compare_cb *compar);"
            , "int compare_int(const int *a, const int *b);"
            , "void f(int *arr) { sort(arr, 10, 4, compare_int); }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isCoordinatedPair (CoordinatedPair _ _ _ _ _ _) = True
                    isCoordinatedPair _                             = False
                any isCoordinatedPair constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "expands macros and generates constraints from their bodies" $ do
        prog <- mustParse
            [ "#define MY_ASSIGN(x, y) do { x = y; } while (0)"
            , "void f(int *a, int b) { MY_ASSIGN(*a, b); }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Expect Subtype (int -> int) from the macro body
                let isIntAssignment (Subtype (BuiltinType TS.S32Ty) (BuiltinType TS.S32Ty) _ _ _) = True
                    isIntAssignment _ = False
                any isIntAssignment constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "generates detailed field-by-field constraints for struct initializers" $ do
        prog <- mustParse
            [ "struct My_Struct { int x; float y; };"
            , "void f() { struct My_Struct s = { 1, 1.0f }; }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let hasIntInit = any (\case Subtype (Singleton TS.S32Ty _) (BuiltinType TS.S32Ty) _ _ _ -> True; _ -> False) constrs
                let hasFloatInit = any (\case Subtype (BuiltinType TS.F32Ty) (BuiltinType TS.F32Ty) _ _ _ -> True; _ -> False) constrs
                hasIntInit `shouldBe` True
                hasFloatInit `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles binary operator promotions for pointer arithmetic" $ do
        prog <- mustParse ["void f(int *p, int i) { int *q = p + i; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Expect Subtype (i -> S32)
                let isIdxSubtype (Subtype (BuiltinType TS.S32Ty) (BuiltinType TS.S32Ty) _ _ _) = True
                    isIdxSubtype _ = False
                any isIdxSubtype constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "performs recursive de-voidification on structs" $ do
        prog <- mustParse
            [ "struct My_Struct { void *ptr; };"
            , "void f(struct My_Struct *s) { /* hotspots should ensure `ptr` is a template */ }"
            ]
        let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        case TS.lookupType "My_Struct" ts of
            Just (TS.StructDescr _ _ [(_, TS.Template _ _)] _) -> return ()
            Just (TS.StructDescr _ _ [(_, TS.Pointer (TS.Template _ _))] _) -> return ()
            other -> expectationFailure $ "Expected templated member in My_Struct, but got: " ++ show other

    it "handles literal array dimensions in parameters" $ do
        prog <- mustParse ["void f(int a[10]) { a[0] = 1; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- The type of 'a' should be an array of int, not contain Unsupported
                let isUnsupported (Subtype t1 t2 _ _ _) = containsUnsupported t1 || containsUnsupported t2
                    isUnsupported _ = False
                any isUnsupported constrs `shouldBe` False
            _ -> expectationFailure "Expected constraints for f"

    it "traverses through control flow statements" $ do
        prog <- mustParse
            [ "void f(int x) {"
            , "    START: {"
            , "        x = 1;"
            , "    }"
            , "    while (x == 1) {"
            , "        if (x == 1) {"
            , "            break;"
            , "        }"
            , "        if (x == 1) {"
            , "            continue;"
            , "        }"
            , "    }"
            , "    if (x == 1) {"
            , "        goto START;"
            , "    }"
            , "}"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isAssignment (Subtype (Singleton TS.S32Ty 1) (BuiltinType TS.S32Ty) _ _ _) = True
                    isAssignment _ = False
                any isAssignment constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "generates constraints for cast expressions" $ do
        prog <- mustParse ["void f(float x) { int y = (int)x; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- We expect a constraint between the <int> result and y (int)
                -- and ideally between x (float) and the cast target (int)
                let isCastConstraint (Subtype (BuiltinType TS.F32Ty) (BuiltinType TS.S32Ty) _ _ _) = True
                    isCastConstraint _ = False
                any isCastConstraint constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles bitwise operators and increment/decrement" $ do
        prog <- mustParse ["void f(int x) { ++x; --x; x = x & 1; x = x | 2; x = x ^ 3; x = ~x; x = x << 1; x = x >> 1; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isUnsupported (Subtype t1 t2 _ _ _) = containsUnsupported t1 || containsUnsupported t2
                    isUnsupported _ = False
                any isUnsupported constrs `shouldBe` False
            _ -> expectationFailure "Expected constraints for f"

    it "generates constraints for union initializers" $ do
        prog <- mustParse
            [ "union My_Union { int x; float y; };"
            , "void f() { union My_Union u = { 1 }; }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Union initializer should constrain the first member (int)
                let isIntInit (Subtype (Singleton TS.S32Ty 1) (BuiltinType TS.S32Ty) _ _ _) = True
                    isIntInit _ = False
                any isIntInit constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles variadic function calls" $ do
        prog <- mustParse ["void my_printf(const char *fmt, ...);", "void f() { my_printf(\"%d\", 1); }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isCallable (Callable _ _ _ _ _ _ _) = True
                    isCallable _                        = False
                any isCallable constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles function pointer calls" $ do
        prog <- mustParse
            [ "typedef void my_cb(int x);"
            , "void f(my_cb *cb) { cb(1); }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Function pointers should generate a Callable constraint
                let isCallable (Callable _ [Singleton TS.S32Ty 1] (Template _ Nothing) _ _ _ _) = True
                    isCallable _ = False
                if any isCallable constrs
                    then return ()
                    else expectationFailure $ "Expected Callable constraint. Constraints: " ++ show constrs
            _ -> expectationFailure "Expected constraints for f"

    it "respects variable shadowing" $ do
        prog <- mustParse
            [ "static const float x_global = 1.0f;"
            , "void f() {"
            , "    float x = 1.0f;"
            , "    { int x = 1; }"
            , "}"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let hasFloatInit = any (\case Subtype (BuiltinType TS.F32Ty) (BuiltinType TS.F32Ty) _ _ _ -> True; _ -> False) constrs
                let hasIntInit = any (\case Subtype (Singleton TS.S32Ty 1) (BuiltinType TS.S32Ty) _ _ _ -> True; _ -> False) constrs
                hasFloatInit `shouldBe` True
                hasIntInit `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles enum member usage" $ do
        prog <- mustParse
            [ "enum My_Enum { VAL1, VAL2 };"
            , "void f() { int x = VAL1; }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Enum members are now correctly collected as globals
                let isEnumAssign (Subtype (TS.EnumMem _) (BuiltinType TS.S32Ty) _ _ _) = True
                    isEnumAssign (Subtype (TypeRef TS.EnumRef _ _) (BuiltinType TS.S32Ty) _ _ _) = True
                    isEnumAssign _ = False
                if any isEnumAssign constrs
                    then return ()
                    else expectationFailure $ "Expected EnumRef assignment. Constraints: " ++ show constrs
            _ -> expectationFailure "Expected constraints for f"

    it "handles recursive function calls" $ do
        prog <- mustParse ["void f(int n) { if (n > 0) { f(n - 1); } }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Recursive call to f(n - 1)
                let isFCall (Callable _ [BuiltinType TS.S32Ty] _ _ _ _ _) = True
                    isFCall _ = False
                any isFCall constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles variadic macros with __VA_ARGS__" $ do
        prog <- mustParse
            [ "#define MY_PRINT(fmt, ...) my_printf(fmt, __VA_ARGS__)"
            , "void my_printf(const char *fmt, ...);"
            , "void f() { MY_PRINT(\"%d\", 1); }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- The expanded call to my_printf should be present
                let isCallable (Callable _ [Pointer (BuiltinType TS.CharTy), Singleton TS.S32Ty 1] _ _ _ _ _) = True
                    isCallable _ = False
                any isCallable constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "handles _Owned pointers in constraints" $ do
        prog <- mustParse ["void f(int *_Owned p) { int *q = p; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Expect Subtype (Owner(int) -> int)
                let isOwnerSubtype (Subtype (TS.Owner _) _ _ _ _) = True
                    isOwnerSubtype _                              = False
                any isOwnerSubtype constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "generates constraints for self-deallocation pattern" $ do
        prog <- mustParse
            [ "struct Tox_Memory;"
            , "void tox_memory_dealloc(const struct Tox_Memory *mem, void *_Owned ptr);"
            , "void tox_memory_free(struct Tox_Memory *_Owned mem) {"
            , "    tox_memory_dealloc(mem, mem);"
            , "}"
            ]
        let res = runCG prog
        case Map.lookup "tox_memory_free" (cgrConstraints res) of
            Just constrs -> do
                -- Expect a Callable constraint where 'mem' is passed twice
                let isDeallocCall (Callable _ [TS.Owner _, TS.Owner _] _ _ _ _ _) = True
                    isDeallocCall _                                              = False
                -- Note: 'mem' is declared as 'struct Tox_Memory *_Owned mem'
                -- So both arguments in the call should be 'Owner (TypeRef ...)'
                any isDeallocCall constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for tox_memory_free"

    it "generates Pointer constraints for dereferences" $ do
        prog <- mustParse ["void f(int x) { *x = 1; }"]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- Expect Subtype (x -> Pointer T)
                let isPointerConstraint (Subtype (BuiltinType TS.S32Ty) (Pointer _) _ _ _) = True
                    isPointerConstraint _                                                  = False
                any isPointerConstraint constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for f"

    it "instantiates templated structs in function parameters" $ do
        prog <- mustParse
            [ "struct Tox { void *userdata; };"
            , "void f(struct Tox *t) { void *p = t->userdata; }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                let isToxHasMember = \case
                        HasMember (TypeRef _ l (_:_)) "userdata" _ _ _ _
                            | TS.templateIdToText (C.lexemeText l) == "Tox" -> True
                        _ -> False
                any isToxHasMember constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

    it "instantiates templated functions when used as expressions" $ do
        prog <- mustParse
            [ "typedef void tox_cb(void *userdata);"
            , "void tox_handler(void *userdata) { /* comment */ }"
            , "void f() { tox_cb *p = tox_handler; }"
            ]
        let res = runCG prog
        case Map.lookup "f" (cgrConstraints res) of
            Just constrs -> do
                -- We expect an assignment where the right side is a TypeRef with template arguments
                let isTemplatedHandlerAssignment = \case
                        Subtype (TypeRef _ l (_:_)) _ _ _ _
                            | TS.templateIdToText (C.lexemeText l) == "tox_handler" -> True
                        _ -> False
                any isTemplatedHandlerAssignment constrs `shouldBe` True
            _ -> expectationFailure "Expected constraints for function 'f'"

containsUnsupported :: TypeInfo p -> Bool
containsUnsupported = foldFix $ \case
    TS.UnsupportedF _ -> True
    f -> any id f
