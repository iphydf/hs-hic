{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.TypeSystem.Standard.BaseSpec (spec) where

import           Data.Text                             (Text)
import qualified Data.Text                             as T
import           GHC.Stack                             (HasCallStack)
import qualified Language.Cimple                       as C
import           Language.Hic.Core.Errors              (ErrorInfo (..))
import           Language.Hic.Core.Pretty              (ppErrorInfo,
                                                        renderPlain)
import           Language.Hic.TestUtils                (mustParse)
import           Language.Hic.TypeSystem.Core.Base     (Phase (..))
import qualified Language.Hic.TypeSystem.Standard.Base as TC
import           Prettyprinter                         (Doc,
                                                        defaultLayoutOptions,
                                                        layoutPretty,
                                                        unAnnotate)
import           Prettyprinter.Render.Terminal         (AnsiStyle)
import           Test.Hspec
import           Test.QuickCheck                       (within)

shouldHaveError :: HasCallStack => [(FilePath, ErrorInfo 'Local)] -> [Text] -> Expectation
shouldHaveError errors expectedLines =
    let actualLines = concatMap (T.lines . (\(path, ei) -> renderPlain (ppErrorInfo path ei Nothing))) errors
    in actualLines `shouldBe` expectedLines

shouldHaveNoErrors :: HasCallStack => [(FilePath, ErrorInfo 'Local)] -> Expectation
shouldHaveNoErrors errors =
    if null errors
    then return ()
    else expectationFailure $ T.unpack $ T.unlines $
            "expected no errors, but got:" :
            map (\(path, ei) -> renderPlain (ppErrorInfo path ei Nothing)) errors


spec :: Spec
spec = do
    describe "Basic type checking" $ do
        it "infers types of simple literals" $ do
            prog <- mustParse ["void f() { int x = 1; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers type of a variable" $ do
            prog <- mustParse ["void f() { int x = 1; int y = x; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers types of macros used as templates" $ do
            prog <- mustParse
                [ "void g(int p);"
                , "#define CALL_G(x) g(x)"
                , "void f() { CALL_G(1); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers types of struct member access" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "void f() { struct My_Struct s; s.x = 1; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers types of statement-like macros" $ do
            prog <- mustParse
                [ "#define SWAP_INT(x, y) do { int tmp = x; x = y; y = tmp; } while (0)"
                , "void f() { int a = 1; int b = 2; SWAP_INT(a, b); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports type mismatch in statement-like macros" $ do
            prog <- mustParse
                [ "#define SWAP_INT(x, y) do { int tmp = x; x = y; y = tmp; } while (0)"
                , "void f() { int a = 1; int *b = nullptr; SWAP_INT(a, b); }"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: assignment type mismatch: expected int32_t, got int32_t*"
                , "  expected int32_t, but got int32_t*"
                , "  in macro 'SWAP_INT'"
                , "  in function 'f'"
                , "test.c:1: assignment type mismatch: expected int32_t*, got int32_t"
                , "  expected int32_t*, but got int32_t"
                , "  in macro 'SWAP_INT'"
                , "  in function 'f'"
                ]

        it "infers types of comparison operators" $ do
            prog <- mustParse ["void f() { bool b = (1 == 2); }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers types of sizeof expressions" $ do
            prog <- mustParse ["void f() { int s = sizeof(int); }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles function parameters in scope" $ do
            prog <- mustParse ["void f(int x) { int y = x; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles nullary functions with (void)" $ do
            prog <- mustParse ["void f(void); void g() { f(); }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles templated struct pointer compatibility" $ do
            prog <- mustParse
                [ "struct Memory { void *ptr; };"
                , "void f(struct Memory *m) {"
                , "    struct Memory *m2 = m;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles templates in nested structures" $ do
            prog <- mustParse
                [ "struct Memory { void *ptr; };"
                , "struct Context { const struct Memory *mem; };"
                , "void f(struct Context *ctx, const struct Memory *mem) {"
                , "    ctx->mem = mem;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles forward declared templated structs" $ do
            prog <- mustParse
                [ "struct Memory;"
                , "void f(const struct Memory *m);"
                , "struct Memory { void *ptr; };"
                , "void g(struct Memory *m) { f(m); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles structs with multiple void pointers" $ do
            prog <- mustParse
                [ "struct Multi { void *a; void *b; };"
                , "void f(struct Multi *m) {"
                , "    int x;"
                , "    float y;"
                , "    m->a = &x;"
                , "    m->b = &y;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "does not incorrectly merge independent templates in nested structures" $ do
            prog <- mustParse
                [ "struct My_A { void *p; };"
                , "struct My_B { struct My_A *a; void *q; };"
                , "void f(struct My_B *b) {"
                , "    int *i = b->a->p;"
                , "    float *f = b->q;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles __func__ predefined identifier" $ do
            prog <- mustParse ["void f() { const char *s = __func__; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles __FILE__ and __LINE__ predefined macros" $ do
            prog <- mustParse ["void f() { const char *file = __FILE__; uint32_t line = __LINE__; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles enum comparisons" $ do
            prog <- mustParse
                [ "typedef enum Color { COLOR_RED, COLOR_GREEN, COLOR_BLUE } Color;"
                , "void f(Color c) { if (c >= COLOR_GREEN) return; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles nested macro constants with enums" $ do
            prog <- mustParse
                [ "typedef enum Level { LVL_INFO, LVL_WARN } Level;"
                , "#define MIN_LVL LVL_INFO"
                , "void f(Level l) { if (l >= MIN_LVL) return; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles enum members directly" $ do
            prog <- mustParse
                [ "typedef enum Level { LVL_INFO, LVL_WARN } Level;"
                , "void f() { Level l = LVL_INFO; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles UINT32_C macro" $ do
            prog <- mustParse ["void f() { uint32_t x = UINT32_C(1); }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles LOGGER_WRITE macro pattern" $ do
            prog <- mustParse
                [ "typedef enum Logger_Level { LOGGER_LEVEL_DEBUG } Logger_Level;"
                , "struct Logger { int x; };"
                , "void logger_write(const struct Logger *log, Logger_Level level, const char *file, uint32_t line, const char *func, const char *format, ...);"
                , "#define MIN_LOGGER_LEVEL LOGGER_LEVEL_DEBUG"
                , "#define LOGGER_WRITE(log, level, ...) do { if (level >= MIN_LOGGER_LEVEL) { logger_write(log, level, __FILE__, __LINE__, __func__, __VA_ARGS__); } } while (0)"
                , "#define LOGGER_DEBUG(log, ...) LOGGER_WRITE(log, LOGGER_LEVEL_DEBUG, __VA_ARGS__)"
                , "void f(const struct Logger *log) { LOGGER_DEBUG(log, \"test %d\", 1); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles enums" $ do
            prog <- mustParse
                [ "typedef enum Color { COLOR_RED, COLOR_GREEN, COLOR_BLUE } Color;"
                , "void f() { Color c = COLOR_RED; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles static function scope" $ do
            prog <- mustParse
                [ "static int g(int x) { return x; }"
                , "int f() { return g(1); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles struct array access" $ do
            prog <- mustParse
                [ "struct DHT_Friend { int client_list[8]; };"
                , "int f(struct DHT_Friend *dht_friend) { return dht_friend->client_list[0]; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles array compatibility with different integer types" $ do
            prog <- mustParse
                [ "void f() {"
                , "    char a[8];"
                , "    char *p = a;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles array-to-pointer decay in function calls" $ do
            prog <- mustParse
                [ "void g(char *p);"
                , "void f() {"
                , "    char a[8];"
                , "    g(a);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles typedef of forward-declared struct" $ do
            prog <- mustParse
                [ "typedef struct DHT_Friend DHT_Friend;"
                , "struct DHT_Friend { int x; };"
                , "int f(DHT_Friend *dht_friend) { return dht_friend->x; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles nested struct member access" $ do
            prog <- mustParse
                [ "struct Inner { int y; };"
                , "struct Outer { struct Inner x; };"
                , "int f(struct Outer *o) { return o->x.y; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles struct with comments" $ do
            prog <- mustParse
                [ "struct Inner {"
                , "    /* comment */"
                , "    int y;"
                , "};"
                , ""
                , "struct Outer { struct Inner x; };"
                , "int f(struct Outer *o) { return o->x.y; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles nested struct with commented field" $ do
            prog <- mustParse
                [ "struct Inner { int y; };"
                , "struct Outer {"
                , "    /** comment */"
                , "    struct Inner x;"
                , "};"
                , ""
                , "int f(struct Outer *o) { return o->x.y; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles struct with #ifdef" $ do
            prog <- mustParse
                [ "struct Inner { int y; };"
                , "struct Outer {"
                , "#ifdef FOO_BAR"
                , "    struct Inner x;"
                , "#endif /* FOO_BAR */"
                , "};"
                , ""
                , "int f(struct Outer *o) { return o->x.y; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles typedef of a named struct definition" $ do
            prog <- mustParse
                [ "typedef struct My_S { int x; } My_S;"
                , "int f(My_S *s) { return s->x; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles typedef of forward-declared struct in reverse order" $ do
            prog <- mustParse
                [ "struct My_DHT_Friend { int x; };"
                , "typedef struct My_DHT_Friend My_DHT_Friend;"
                , "int f(My_DHT_Friend *dht_friend) { return dht_friend->x; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles memeq function with pointers and comparisons" $ do
            prog <- mustParse
                [ "bool memeq(uint8_t const *a, size_t a_size, uint8_t const *b, size_t b_size)"
                , "{"
                , "    return a_size == b_size && memcmp(a, b, a_size) == 0;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles variadic functions" $ do
            prog <- mustParse
                [ "void my_printf(const char *fmt, ...);"
                , "void f() { my_printf(\"%d %d\", 1, 2); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports too few arguments for variadic functions" $ do
            prog <- mustParse
                [ "void my_printf(const char *fmt, ...);"
                , "void f() { my_printf(); }"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:2: too few arguments in function call: expected 1, got 0"
                , "  in function 'f'"
                ]

    describe "BinPack patterns" $ do
        it "handles bin_pack_array_cb pattern with template inference" $ do
            prog <- mustParse
                [ "struct Logger { void *config; };"
                , "struct Bin_Pack { int x; };"
                , "typedef bool bin_pack_array_cb(const void *_Nullable arr, uint32_t index, const struct Logger *_Nullable logger, struct Bin_Pack *_Nonnull bp);"
                , "uint32_t bin_pack_obj_array_b_size(bin_pack_array_cb *_Nonnull callback, const void *_Nullable arr, uint32_t arr_size, const struct Logger *_Nullable logger);"
                , "static bool bin_pack_node_handler(const void *_Nullable arr, uint32_t index, const struct Logger *_Nullable logger, struct Bin_Pack *_Nonnull bp)"
                , "{"
                , "    const int *nodes = (const int *)arr;"
                , "    return true;"
                , "}"
                , "int pack_nodes(const struct Logger *logger, const int *nodes, uint16_t number)"
                , "{"
                , "    return bin_pack_obj_array_b_size(bin_pack_node_handler, nodes, number, logger);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Basic expressions" $ do
        it "reports error for assignment of incompatible types" $ do
            prog <- mustParse ["void f() { int x; x = \"hello\"; }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: assignment type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  in function 'f'"
                ]

        it "reports error for arithmetic with incompatible types" $ do
            prog <- mustParse ["void f() { int x = 1 + \"hello\"; }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: initializer type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  in function 'f'"
                ]

        it "infers type of dereferenced pointer" $ do
            prog <- mustParse ["void f(int *p) { int x = *p; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers type of address-of expression" $ do
            prog <- mustParse ["void f() { int x = 1; int *p = &x; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Control flow" $ do
        it "reports error for return type mismatch" $ do
            prog <- mustParse ["int f() { return \"hello\"; }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: return type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  in function 'f'"
                ]

        it "reports error for if condition mismatch" $ do
            prog <- mustParse ["void f() { if (\"hello\") { /* nothing */ } }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: argument 0 type mismatch: expected bool, got char*"
                , "  expected bool, but got char*"
                , "  in function 'f'"
                , "test.c:1: argument 0 type mismatch: expected bool, got char*"
                , "  expected bool, but got char*"
                , "  in function 'f'"
                ]

        it "reports error for while condition mismatch" $ do
            prog <- mustParse ["void f() { while (\"hello\") { /* nothing */ } }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: argument 0 type mismatch: expected bool, got char*"
                , "  expected bool, but got char*"
                , "  in function 'f'"
                , "test.c:1: argument 0 type mismatch: expected bool, got char*"
                , "  expected bool, but got char*"
                , "  in function 'f'"
                ]

        it "infers types of ternary operator" $ do
            prog <- mustParse ["void f() { int x = ((1 == 1) ? 1 : 2); }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for ternary operator branch mismatch" $ do
            prog <- mustParse ["void f() { int x = (1 == 1 ? 1 : \"hello\"); }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: type mismatch: expected char*, got int32_t"
                , "  expected char*, but got int32_t"
                , "  in function 'f'"
                ]

        it "reports error for switch condition mismatch" $ do
            prog <- mustParse ["void f(int *p) { switch (p) { case 1: break; } }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: argument 0 type mismatch: expected int32_t, got int32_t*"
                , "  expected int32_t, but got int32_t*"
                , "  in function 'f'"
                ]

    describe "Logical and Bitwise operators" $ do
        it "infers types of logical operators" $ do
            prog <- mustParse ["void f() { bool b = ((1 == 1) && (2 == 2)) || !(1 == 1); }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for logical operator operand mismatch" $ do
            prog <- mustParse ["void f() { bool b = (1 == 1) && \"hello\"; }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: type mismatch: expected bool, got char*"
                , "  expected bool, but got char*"
                , "  in function 'f'"
                ]

        it "infers types of bitwise operators" $ do
            prog <- mustParse ["void f() { int x = (1 & 2) | (3 ^ 4) << 1; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Aggregate types" $ do
        it "handles union member access" $ do
            prog <- mustParse
                [ "union My_Union { int x; float y; };"
                , "void f() { union My_Union u; u.x = 1; }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for inconsistent types in initializer list" $ do
            prog <- mustParse ["void f() { int a[2] = { 1, \"hello\" }; }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: initializer type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  in function 'f'"
                ]

    describe "Pointers" $ do
        it "handles pointer arithmetic" $ do
            prog <- mustParse ["void f(int *p) { int *q = p + 1; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles pointer arithmetic on arrays" $ do
            prog <- mustParse ["void f() { int a[10]; int *p = a + 1; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles dereferencing arrays" $ do
            prog <- mustParse ["void f() { int a[10]; int x = *a; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles subtraction of array pointers" $ do
            prog <- mustParse ["void f() { int a[10]; int *p = a; int *q = a + 5; size_t diff = q - p; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for pointer arithmetic with incompatible types" $ do
            prog <- mustParse ["void f(int *p) { int *q = p + \"hello\"; }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  in function 'f'"
                ]

        it "handles double pointers" $ do
            prog <- mustParse ["void f(int **p) { int *q = *p; int x = **p; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Function calls" $ do
        it "reports error for argument mismatch" $ do
            prog <- mustParse ["void g(int x); void f() { g(\"hello\"); }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: argument 0 type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  in function 'f'"
                ]

        it "reports error for too many arguments" $ do
            prog <- mustParse ["void g(int x); void f() { g(1, 2); }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: too many arguments in function call: expected 1, got 2"
                , "  in function 'f'"
                ]


    describe "unsoundness and C compatibility" $ do
        it "allows memcmp result to be compared with 0 (necessary unsoundness)" $ do
            prog <- mustParse
                [ "void *memcpy(void *dest, const void *src, size_t n);"
                , "int memcmp(const void *s1, const void *s2, size_t n);"
                , "void f(int *a, int *b, size_t n) {"
                , "    if (memcmp(a, b, n) == 0) { memcpy(a, b, n); }"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "demonstrates unsoundness: optimistic narrowing of variable to constant" $ do
            -- See OrderedSolverSpec.hs for a detailed explanation of this
            -- documented unsoundness. In short: we allow 'Builtin <: Singleton'
            -- to support standard C comparisons (e.g. 'res == 0'), which allows
            -- variables in comparisons to be unsoundly fixed to constants.
            prog <- mustParse
                [ "void set(void *a[2], int *pi, float *pf) {"
                , "    a[0] = pi;"
                , "    a[1] = pf;"
                , "}"
                , "void f(void **a, int i, int *p) {"
                , "    if (i == 0) { return; }"
                , "    *(a + i) = p;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "void* template inference" $ do
        it "allows memcpy with matching pointer types" $ do
            prog <- mustParse
                [ "void *memcpy(void *dest, const void *src, size_t n);"
                , "void f(int *a, int *b) { memcpy(a, b, sizeof(int)); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for memcpy with mismatching pointer types" $ do
            prog <- mustParse ["void f(int *a, float *b, uint32_t n) { memcpy(a, b, n); }"]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: argument 1 type mismatch: expected int32_t const*, got float*"
                , "  while checking pointer target of T:inst:0 const* and float*:"
                , "    expected int32_t, but got float"
                , "  in function 'f'"
                , ""
                , "  where template T:inst:0 was bound to int32_t due to argument 0 type mismatch: expected T:inst:0, got int32_t"
                ]

        it "infers parameter type from cast in function body" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "void f(void *obj) { struct My_Struct *s = (struct My_Struct *)obj; }"
                , "void g() {"
                , "    struct My_Struct s;"
                , "    f(&s);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error when passing wrong type to inferred templated function" $ do
            prog <- mustParse
                [ "void f(void *p) { int *x = (int *)p; }"
                , "struct My_Struct { int x; };"
                , "void g() {"
                , "    struct My_Struct s;"
                , "    f(&s);"
                , "    int y = 1;"
                , "    f(&y);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:5: argument 0 type mismatch: expected int32_t*, got struct My_Struct* nonnull"
                , "  while checking pointer target of int32_t* and struct My_Struct*:"
                , "    expected int32_t, but got struct My_Struct"
                , "  in function 'g'"
                ]

        it "reports error for incompatible casts of the same void * pointer" $ do
            prog <- mustParse
                [ "struct My_A { int x; };"
                , "struct My_B { float y; };"
                , "void f(void *p) {"
                , "    struct My_A *a = (struct My_A *)p;"
                , "    struct My_B *b = (struct My_B *)p;"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:5: initializer type mismatch: expected struct My_B*, got struct My_A*"
                , "  while checking pointer target of struct My_B* and T1*:"
                , "    expected struct My_B, but got struct My_A"
                , "  in function 'f'"
                , ""
                , "  where template T1 was bound to struct My_A due to initializer type mismatch: expected T1, got struct My_A"
                ]

        it "handles templated typedefs and callback registration" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "typedef void cb_cb(void *obj);"
                , "void register_callback(cb_cb *f, void *obj);"
                , "void my_handler(void *obj) { struct My_Struct *s = (struct My_Struct *)obj; }"
                , "void g() {"
                , "    struct My_Struct s;"
                , "    register_callback(my_handler, &s);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "allows assigning an inferred callback to a _Nullable callback pointer" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *userdata);"
                , "struct My_Handler {"
                , "    my_cb *_Nullable callback;"
                , "    void *userdata;"
                , "};"
                , "void my_handler(void *userdata) {"
                , "    int *p = (int *)userdata;"
                , "}"
                , "void f(struct My_Handler *h, int *p) {"
                , "    h->callback = my_handler;"
                , "    h->userdata = p;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for mismatched callback and userdata in registry" $ within 1000000 $ do
            pendingWith "Reports no errors, but expected complex unification details."
            prog <- mustParse
                [ "typedef void my_cb(void *obj);"
                , "struct My_Handler { my_cb *f; void *o; };"
                , "struct Registry { struct My_Handler h[2]; };"
                , "void set(struct Registry *r, int i, void *o) { r->h[i].o = o; }"
                , "void call(struct Registry *r, int i) { r->h[i].f(r->h[i].o); }"
                , "void handler(void *obj) { int *x = (int *)obj; }"
                , "void f(struct Registry *r, float *p) {"
                , "    set(r, 0, p);"
                , "    r->h[0].f = &handler;"
                , "    call(r, 0);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:10: argument 0 type mismatch: expected int32_t, got float"
                , "  while unifying int32_t and float (argument 0)"
                , "  while unifying int32_t* and float* obj (argument 0)"
                , "  while unifying void(float* obj) and void(int32_t*) (argument 0)"
                , "  while unifying my_cb<float> and void(int32_t*) (argument 0)"
                , "  while unifying my_cb<float>* and void(int32_t*)* (argument 0)"
                , "  while unifying T18 and nonnull void(handler_T7*)* (argument 0)"
                , "  in function 'f'"
                , ""
                , "  where template T18 was bound to my_cb<float>* due to type mismatch: expected T18, got my_cb<float>*"
                , "        template handler_T7 was bound to T16 due to type mismatch: expected handler_T7, got T16"
                , "        template T16 was bound to int32_t due to initializer type mismatch: expected T16, got int32_t"
                ]

        it "handles passing a _Nullable callback to another function" $ do
            prog <- mustParse
                [ "typedef void my_cb(void *userdata);"
                , "void g(my_cb *_Nullable callback, void *userdata) {"
                , "    if (callback != nullptr) { callback(userdata); }"
                , "}"
                , "void f(my_cb *_Nullable callback, void *userdata) {"
                , "    g(callback, userdata);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for mismatched callback and userdata" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "typedef void cb_cb(void *obj);"
                , "void register_callback(cb_cb *f, void *obj) { f(obj); }"
                , "void my_handler(void *obj) { struct My_Struct *s = (struct My_Struct *)obj; }"
                , "void g() {"
                , "    int x;"
                , "    register_callback(my_handler, &x);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:7: argument 1 type mismatch: expected struct My_Struct*, got int32_t* nonnull"
                , "  while checking pointer target of struct My_Struct* and int32_t*:"
                , "    expected struct My_Struct, but got int32_t"
                , "  in function 'g'"
                , ""
                , "  where template P0(obj):inst:1 was bound to struct My_Struct due to argument 0 type mismatch: expected P0(obj):inst:1, got struct My_Struct"
                ]

        it "handles heterogeneous callback arrays" $ do
            prog <- mustParse
                [ "typedef void dht_ip_cb(void *userdata);"
                , "struct Callback_Slot {"
                , "    dht_ip_cb *_Nullable callback;"
                , "    void *userdata;"
                , "};"
                , "struct DHT_Friend {"
                , "    struct Callback_Slot slots[10];"
                , "};"
                , "void h1(void *userdata) { int *x = (int *)userdata; }"
                , "void h2(void *userdata) { float *x = (float *)userdata; }"
                , "void f(struct DHT_Friend *f, int *p1, float *p2) {"
                , "    f->slots[0].callback = h1;"
                , "    f->slots[0].userdata = p1;"
                , "    f->slots[1].callback = h2;"
                , "    f->slots[1].userdata = p2;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "repro template count mismatch in struct member" $ do
            prog <- mustParse
                [ "struct Logger {"
                , "    logger_cb *callback;"
                , "};"
                , ""
                , "typedef void logger_cb(void *context);"
                , ""
                , "void h(void *context) {"
                , "    int *x = (int *)context;"
                , "}"
                , ""
                , "void g(logger_cb *cb) {"
                , "    struct Logger l;"
                , "    l.callback = cb;"
                , "}"
                , ""
                , "void f(struct Logger *log) {"
                , "    log->callback = h;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "infers template type for structs with void* members" $ do
            prog <- mustParse
                [ "struct My_S { void *data; };"
                , "void set_data(struct My_S *s, void *d) { s->data = d; }"
                , "void f() {"
                , "    struct My_S s;"
                , "    int x;"
                , "    set_data(&s, &x);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error when using a templated struct with incompatible types" $ do
            prog <- mustParse
                [ "struct Memory { void *ptr; };"
                , "void g(struct Memory *m, int *p) { m->ptr = p; }"
                , "void f() {"
                , "    struct Memory m;"
                , "    int x;"
                , "    float y;"
                , "    g(&m, &x);"
                , "    g(&m, &y);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:8: argument 1 type mismatch: expected int32_t*, got float* nonnull"
                , "  while checking pointer target of int32_t* and float*:"
                , "    expected int32_t, but got float"
                , "  in function 'f'"
                ]

        it "handles Tox<T> global inference pattern" $ do
            prog <- mustParse
                [ "struct Tox { void *userdata; };"
                , "typedef void tox_cb(struct Tox *tox, void *userdata);"
                , "void tox_callback(struct Tox *tox, tox_cb *cb);"
                , "struct My_Data { int x; };"
                , "void tox_handler(struct Tox *tox, void *userdata) {"
                , "    struct My_Data *d = (struct My_Data *)userdata;"
                , "}"
                , "void f() {"
                , "    struct Tox *tox;"
                , "    struct My_Data d;"
                , "    tox_callback(tox, tox_handler);"
                , "    tox->userdata = &d;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for Tox<T> when userdata is inconsistent" $ do
            prog <- mustParse
                [ "struct Tox { void *userdata; };"
                , "typedef void tox_cb(struct Tox *tox, void *userdata);"
                , "void tox_callback(struct Tox *tox, tox_cb *cb);"
                , "struct My_Data { int x; };"
                , "void tox_handler(struct Tox *tox, void *userdata) {"
                , "    struct My_Data *d = (struct My_Data *)userdata;"
                , "}"
                , "void f() {"
                , "    struct Tox tox;"
                , "    struct My_Data d;"
                , "    tox_callback(&tox, &tox_handler);"
                , "    int x;"
                , "    tox.userdata = &x;"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:13: assignment type mismatch: expected struct My_Data*, got int32_t* nonnull"
                , "  while checking pointer target of struct My_Data* and int32_t*:"
                , "    expected struct My_Data, but got int32_t"
                , "  in function 'f'"
                , ""
                , "  where template T12 was bound to struct My_Data* due to type mismatch: expected T12, got struct My_Data*"
                ]

        it "handles polymorphic sort-like function with multiple different callbacks" $ do
            prog <- mustParse
                [ "typedef int compare_cb(const void *a, const void *b);"
                , "void qsort(void *base, int nmemb, int size, compare_cb *compar) {"
                , "    compar(base, base);"
                , "}"
                , "int compare_int(const void *a, const void *b) {"
                , "    const int *ia = (const int *)a;"
                , "    const int *ib = (const int *)b;"
                , "    if (*ia < *ib) return -1;"
                , "    if (*ia > *ib) return 1;"
                , "    return 0;"
                , "}"
                , "int compare_float(const void *a, const void *b) {"
                , "    float const *fa = (float const *)a;"
                , "    float const *fb = (float const *)b;"
                , "    if (*fa < *fb) return -1;"
                , "    if (*fa > *fb) return 1;"
                , "    return 0;"
                , "}"
                , "void f() {"
                , "    int ia[10];"
                , "    qsort(ia, 10, sizeof(int), compare_int);"
                , "    float fa[10];"
                , "    qsort(fa, 10, sizeof(float), compare_float);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for polymorphic sort when callback and data mismatch" $ do
            prog <- mustParse
                [ "typedef int compare_cb(const void *a, const void *b);"
                , "void sort(void *base, uint32_t nmemb, uint32_t size, compare_cb *compar);"
                , "int compare_int(const int *a, const int *b) { return (*a - *b); }"
                , "void f() {"
                , "    float arr[10];"
                , "    sort(arr, 10, sizeof(float), compare_int);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:6: argument 3 type mismatch: expected compare_cb<float, float>*, got int32_t(int32_t const*, int32_t const*)"
                , "  while checking parameter 0 of int32_t(float const* a, float const* b) and int32_t(int32_t const*, int32_t const*):"
                , "    while checking pointer target of int32_t const* and float const*:"
                , "      expected int32_t, but got float"
                , "  in function 'f'"
                , ""
                , "  where template P0(sort):inst:0 was bound to float due to argument 0 type mismatch: expected P0(sort):inst:0, got float"
                , "test.c:6: type mismatch: expected int32_t const*, got float*"
                , "  while checking pointer target of int32_t const* and float*:"
                , "    expected int32_t, but got float"
                , "  in function 'f'"
                ]

        it "reports error for mismatching types in nested polymorphic calls" $ do
            prog <- mustParse
                [ "void h(int *p) { int *x = 0; p = x; }"
                , "void g(int **pp, float f) { h(*pp); *pp = &f; }"
                , "void f(int **pp, float f) { g(pp, f); }"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:1: initializer type mismatch: expected int32_t*, got int32_t=0"
                , "  expected int32_t*, but got int32_t=0"
                , "  in function 'h'"
                , "test.c:2: assignment type mismatch: expected int32_t*, got float* nonnull"
                , "  while checking pointer target of int32_t* and float*:"
                , "    expected int32_t, but got float"
                , "  in function 'g'"
                ]

        it "handles multiple void* parameters with same inference" $ do
            prog <- mustParse
                [ "void g(void *a, void *b) { a = b; }"
                , "void f() {"
                , "    int x;"
                , "    float y;"
                , "    int *px = &x;"
                , "    float *py = &y;"
                , "    g(px, px);"
                , "    g(px, py);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:8: argument 1 type mismatch: expected int32_t*, got float*"
                , "  while checking pointer target of P0:inst:1* and float*:"
                , "    expected int32_t, but got float"
                , "  in function 'f'"
                , ""
                , "  where template P0:inst:1 was bound to int32_t due to argument 0 type mismatch: expected P0:inst:1, got int32_t"
                ]

        it "infers polymorphic type through nested structs" $ do
            prog <- mustParse
                [ "struct Inner { void *ptr; };"
                , "struct Outer { struct Inner inner; };"
                , "void h(struct Inner *i, int *p) { i->ptr = p; }"
                , "void g(struct Outer *o, float *f) {"
                , "    h(&o->inner, f);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:5: argument 1 type mismatch: expected int32_t*, got float*"
                , "  while checking pointer target of int32_t* and float*:"
                , "    expected int32_t, but got float"
                , "  in function 'g'"
                ]

        it "infers polymorphic type from function return value" $ do
            prog <- mustParse
                [ "void *identity(void *p) { return p; }"
                , "void f(int *p) {"
                , "    float *fp = identity(p);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:3: argument 0 type mismatch: expected float*, got int32_t*"
                , "  while checking pointer target of float* and int32_t*:"
                , "    expected float, but got int32_t"
                , "  in function 'f'"
                ]

    describe "Recursion" $ do
        it "handles simple recursion" $ do
            prog <- mustParse
                [ "int factorial(int n) {"
                , "    if (n <= 1) return 1;"
                , "    return n * factorial(n - 1);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles mutual recursion" $ do
            prog <- mustParse
                [ "bool is_even(int n);"
                , "bool is_odd(int n) {"
                , "    if (n == 0) return false;"
                , "    return is_even(n - 1);"
                , "}"
                , "bool is_even(int n) {"
                , "    if (n == 0) return true;"
                , "    return is_odd(n - 1);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for polymorphic recursion mismatch" $ do
            prog <- mustParse
                [ "struct List { void *data; struct List *next; };"
                , "void process_list(struct List *l) {"
                , "    if (!l) return;"
                , "    int *x = l->data;"
                , "    float *y = l->next->data;"
                , "    process_list(l->next);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:5: initializer type mismatch: expected float*, got int32_t*"
                , "  while checking pointer target of float* and T6:"
                , "    expected float, but got int32_t"
                , "  in function 'process_list'"
                , ""
                , "  where template T6 was bound to int32_t* due to type mismatch: expected T6, got int32_t*"
                ]

        it "infers polymorphic type through multiple recursive calls" $ do
            prog <- mustParse
                [ "void h(void *p) { h(p); }"
                , "void g(void *p) { h(p); }"
                , "void f() {"
                , "    int x;"
                , "    float y;"
                , "    int *px = &x;"
                , "    float *py = &y;"
                , "    g(px);"
                , "    g(py);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Qualifiers and Custom Keywords" $ do
        it "reports error when assigning const to non-const" $ do
            prog <- mustParse
                [ "void f() {"
                , "    const int x = 1;"
                , "    int *p;"
                , "    p = &x;"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:4: assignment type mismatch: expected int32_t*, got int32_t const* nonnull"
                , "  while checking pointer target of int32_t* and int32_t const*:"
                , "    actual type is missing const qualifier"
                , "  in function 'f'"
                ]

        it "allows assigning non-const to const" $ do
            prog <- mustParse
                [ "void f() {"
                , "    int x = 1;"
                , "    const int *p = &x;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for _Nonnull pointer assigned nullptr" $ do
            prog <- mustParse
                [ "void f(int * _Nonnull p);"
                , "void g() { f(nullptr); }"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:2: argument 0 type mismatch: expected int32_t* nonnull, got nullptr_t"
                , "  actual type is missing nonnull qualifier"
                , "  in function 'g'"
                ]

        it "allows _Nullable pointer assigned nullptr" $ do
            prog <- mustParse
                [ "void f(int * _Nullable p);"
                , "void g() { f(nullptr); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles owner qualifier in assignments" $ do
            prog <- mustParse
                [ "void f() {"
                , "    int * owner p = nullptr;"
                , "    int *q = p;"
                , "    return;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Const correctness" $ do
        it "allows assigning const int to int (copy)" $ do
            prog <- mustParse
                [ "void f() {"
                , "    const int x = 1;"
                , "    int y = x;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error when assigning const int* to int* (pointer)" $ do
            prog <- mustParse
                [ "void f(const int *p) {"
                , "    int *q = p;"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:2: initializer type mismatch: expected int32_t*, got int32_t const*"
                , "  while checking pointer target of int32_t* and int32_t const*:"
                , "    actual type is missing const qualifier"
                , "  in function 'f'"
                ]

    describe "Complex Patterns" $ do
        it "handles array of function pointers" $ do
            prog <- mustParse
                [ "typedef void worker_cb(int x);"
                , "void task1(int x) { return; }"
                , "void task2(int x) { return; }"
                , "void f() {"
                , "    worker_cb *workers[2];"
                , "    workers[0] = task1;"
                , "    workers[1] = task2;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error for mismatch in array of function pointers" $ do
            prog <- mustParse
                [ "typedef void worker_cb(int x);"
                , "void h1(int x) { /* */ }"
                , "void h2(float x) { /* */ }"
                , "void f() {"
                , "    worker_cb *workers[2];"
                , "    workers[0] = &h1;"
                , "    workers[1] = &h2;"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:7: assignment type mismatch: expected worker_cb*, got void(float)* nonnull"
                , "  while checking pointer target of worker_cb* and void(float)*:"
                , "    while checking parameter 0 of void(int32_t x) and void(float):"
                , "      expected float, but got int32_t"
                , "  in function 'f'"
                ]

        it "handles calling a non-null function pointer" $ do
            prog <- mustParse
                [ "typedef int callback_cb(int x);"
                , "void f(callback_cb *_Nonnull callback) {"
                , "    callback(1);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles function pointers with wrappers unified with typedefs" $ do
            prog <- mustParse
                [ "typedef int callback_cb(void *_Nullable obj);"
                , "void register_callback(callback_cb *_Nullable cb);"
                , "int my_handler(void *_Nonnull obj) { return 0; }"
                , "void f() { register_callback(&my_handler); }"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:4: argument 0 type mismatch: expected callback_cb<P0(register_callback):inst:0>* nullable, got int32_t(T4* nonnull)* nonnull"
                , "  while checking pointer target of callback_cb<P0(register_callback):inst:0>* and int32_t(T4* nonnull)*:"
                , "    while checking parameter 0 of int32_t(P0(register_callback):inst:0* nullable obj) and int32_t(T4* nonnull):"
                , "      actual type is missing nonnull qualifier"
                , "  in function 'f'"
                , ""
                , "  where template P0(register_callback):inst:0 is unbound"
                , "        template T2(my_handler) was bound to T4 due to type mismatch: expected T2(my_handler), got T4"
                , "        template T4 is unbound"
                ]

        it "successfully solves polymorphic callbacks with consistent nullability" $ within 1000000 $ do
            prog <- mustParse
                [ "typedef struct IP_Port IP_Port;"
                , "typedef struct Networking_Core Networking_Core;"
                , "typedef int packet_handler_cb(void *_Nullable object, const IP_Port *_Nonnull source, uint8_t const *_Nonnull packet, uint16_t length, void *_Nullable userdata);"
                , "struct Packet_Handler { packet_handler_cb *function; void *object; };"
                , "typedef struct Packet_Handler Packet_Handler;"
                , "struct Networking_Core { Packet_Handler packethandlers[256]; };"
                , "void networking_registerhandler(Networking_Core *_Nonnull net, uint8_t byte, packet_handler_cb *_Nullable cb, void *_Nullable object) {"
                , "    net->packethandlers[byte].function = cb;"
                , "    net->packethandlers[byte].object = object;"
                , "}"
                , "typedef struct Net_Crypto Net_Crypto;"
                , "struct Net_Crypto { int x; };"
                , "static int udp_handle_cookie_request(void *_Nullable object, const IP_Port *_Nonnull source, uint8_t const *_Nonnull packet, uint16_t length, void *_Nullable userdata) {"
                , "    const Net_Crypto *c = (const Net_Crypto *)object;"
                , "    return 0;"
                , "}"
                , "void f(Networking_Core *_Nonnull net, Net_Crypto *_Nonnull temp) {"
                , "    networking_registerhandler(net, 1, &udp_handle_cookie_request, temp);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles polymorphic callbacks with _Nonnull/_Nullable divergence" $ within 1000000 $ do
            prog <- mustParse
                [ "typedef struct IP_Port IP_Port;"
                , "typedef struct Networking_Core Networking_Core;"
                , "typedef int packet_handler_cb(void *_Nullable object, const IP_Port *_Nonnull source, uint8_t const *_Nonnull packet, uint16_t length, void *_Nullable userdata);"
                , "struct Packet_Handler { packet_handler_cb *function; void *object; };"
                , "typedef struct Packet_Handler Packet_Handler;"
                , "struct Networking_Core { Packet_Handler packethandlers[256]; };"
                , "void networking_registerhandler(Networking_Core *_Nonnull net, uint8_t byte, packet_handler_cb *_Nullable cb, void *_Nullable object) {"
                , "    net->packethandlers[byte].function = cb;"
                , "    net->packethandlers[byte].object = object;"
                , "}"
                , "typedef struct Net_Crypto Net_Crypto;"
                , "struct Net_Crypto { int x; };"
                , "static int udp_handle_cookie_request(void *_Nonnull object, const IP_Port *_Nonnull source, uint8_t const *_Nonnull packet, uint16_t length, void *_Nullable userdata) {"
                , "    const Net_Crypto *c = (const Net_Crypto *)object;"
                , "    return 0;"
                , "}"
                , "void f(Networking_Core *_Nonnull net, Net_Crypto *_Nonnull temp) {"
                , "    networking_registerhandler(net, 1, &udp_handle_cookie_request, temp);"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:18: argument 2 type mismatch: expected packet_handler_cb<struct Net_Crypto, struct Net_Crypto>* nullable, got int32_t(struct Net_Crypto* nonnull, struct IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, struct Net_Crypto* nullable)* nonnull"
                , "  while checking pointer target of packet_handler_cb<struct Net_Crypto, struct Net_Crypto>* and int32_t(struct Net_Crypto* nonnull, struct IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, struct Net_Crypto* nullable)*:"
                , "    while checking parameter 0 of int32_t(struct Net_Crypto* nullable object, IP_Port const* nonnull source, uint8_t const* nonnull packet, uint16_t length, struct Net_Crypto* nullable userdata) and int32_t(struct Net_Crypto* nonnull, struct IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, struct Net_Crypto* nullable):"
                , "      actual type is missing nonnull qualifier"
                , "  in function 'f'"
                , ""
                , "  where template P0(object):inst:0[uint8_t] was bound to struct Net_Crypto due to argument 3 type mismatch: expected P0(object):inst:0[uint8_t], got struct Net_Crypto"
                , "        template P0(userdata):inst:0[uint8_t] was bound to struct Net_Crypto due to argument 2 type mismatch: expected P0(userdata):inst:0[uint8_t], got T32"
                , "        template T16(udp_handle_cookie_request) was bound to struct Net_Crypto due to type mismatch: expected T16(udp_handle_cookie_request), got T31"
                , "        template T17(udp_handle_cookie_request) was bound to struct Net_Crypto due to type mismatch: expected T17(udp_handle_cookie_request), got T32"
                ]

        it "handles member access on a _Nonnull pointer" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "void f(struct My_Struct *_Nonnull p) {"
                , "    p->x = 1;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

    describe "Networking types" $ do
        it "handles sockaddr_in to sockaddr* implicit conversion" $ do
            prog <- mustParse
                [ "void f() {"
                , "    struct sockaddr_in saddr = {0};"
                , "    int s = socket(2, 1, 0);"
                , "    bind(s, (const struct sockaddr *)&saddr, sizeof(saddr));"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles sockaddr_in6 to sockaddr* implicit conversion" $ do
            prog <- mustParse
                [ "void f() {"
                , "    struct sockaddr_in6 saddr = {0};"
                , "    int s = socket(10, 1, 0);"
                , "    connect(s, (const struct sockaddr *)&saddr, sizeof(saddr));"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles sockaddr_storage compatibility" $ do
            prog <- mustParse
                [ "void f(int s) {"
                , "    struct sockaddr_storage addr;"
                , "    socklen_t len = sizeof(addr);"
                , "    getsockopt(s, 0, 0, &addr, &len);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles Windows-specific WSAStartup and MAKEWORD" $ do
            prog <- mustParse
                [ "void f() {"
                , "    WSADATA wsaData;"
                , "    WSAStartup(MAKEWORD(2, 2), &wsaData);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles WSAAddressToString and LPSOCKADDR" $ do
            prog <- mustParse
                [ "void f(struct sockaddr_in *saddr) {"
                , "    char buf[64];"
                , "    DWORD len = 64;"
                , "    WSAAddressToString((LPSOCKADDR)saddr, sizeof(*saddr), nullptr, buf, &len);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles LPSTR casts" $ do
            prog <- mustParse
                [ "void f(const char *s) {"
                , "    LPSTR s2 = (LPSTR)s;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles implicit conversion from int to bool in networking error checks" $ do
            prog <- mustParse
                [ "void f(int s) {"
                , "    struct sockaddr_in saddr = {0};"
                , "    if (bind(s, (struct sockaddr *)&saddr, sizeof(saddr)) == -1) {"
                , "        /* error handling */"
                , "    }"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles inet_ntop and inet_pton with void* templates" $ do
            prog <- mustParse
                [ "void f(struct in_addr *addr) {"
                , "    char buf[16];"
                , "    inet_ntop(2, addr, buf, 16);"
                , "    inet_pton(2, \"127.0.0.1\", addr);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles addrinfo structure and getaddrinfo" $ do
            prog <- mustParse
                [ "void f() {"
                , "    struct addrinfo hints = {0};"
                , "    struct addrinfo *res;"
                , "    getaddrinfo(\"localhost\", \"80\", &hints, &res);"
                , "    freeaddrinfo(res);"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles errno as a built-in variable" $ do
            prog <- mustParse
                [ "void f() {"
                , "    int err = errno;"
                , "    errno = 0;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles structure member access for networking types" $ do
            prog <- mustParse
                [ "void f(struct sockaddr_in *saddr) {"
                , "    saddr->sin_family = 2;"
                , "    saddr->sin_port = 80;"
                , "    saddr->sin_addr.s_addr = 0;"
                , "}"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles ipv6_mreq initialization" $ do
            prog <- mustParse ["void f() { struct ipv6_mreq mreq = {{{{0}}}}; }"]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "handles dereferencing function call result" $ do
            prog <- mustParse
                [ "typedef struct My_Struct { int x; } My_Struct;"
                , "const My_Struct *get_s(int i) { return nullptr; }"
                , "void f() { const My_Struct s_var = *get_s(1); }"
                ]
            shouldHaveNoErrors $ TC.typeCheckProgram prog

        it "reports error with inference chain for template conflict" $ do
            prog <- mustParse
                [ "void f(void *a, void *b) {"
                , "    int *ia = (int *)a;"
                , "    float *fb = (float *)b;"
                , "    a = b;"
                , "}"
                ]
            TC.typeCheckProgram prog `shouldHaveError`
                [ "test.c:4: assignment type mismatch: expected int32_t*, got float*"
                , "  while checking pointer target of T2* and T3*:"
                , "    expected int32_t, but got float"
                , "  in function 'f'"
                , ""
                , "  where template T2 was bound to int32_t due to initializer type mismatch: expected T2, got int32_t"
                , "        template T3 was bound to float due to initializer type mismatch: expected T3, got float"
                ]

-- end of tests
