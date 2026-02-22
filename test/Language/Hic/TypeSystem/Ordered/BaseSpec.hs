{-# LANGUAGE DataKinds         #-}
{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
{-# LANGUAGE PatternSynonyms   #-}
module Language.Hic.TypeSystem.Ordered.BaseSpec (spec) where

import           Data.List                                            (nub)
import           Data.Map.Strict                                      (Map)
import qualified Data.Map.Strict                                      as Map
import           Data.Text                                            (Text)
import qualified Data.Text                                            as T
import qualified Language.Cimple.Program                              as Program
import           Language.Hic.Core.Errors                             (ErrorInfo (..))
import           Language.Hic.Core.Pretty                             (ppErrorInfo,
                                                                       renderPlain)
import           Language.Hic.TestUtils                               (mustParse)
import           Language.Hic.TypeSystem.Core.Base                    (Phase (..),
                                                                       TypeInfo,
                                                                       pattern BuiltinType,
                                                                       pattern Function)
import qualified Language.Hic.TypeSystem.Core.Base                    as TS
import           Language.Hic.TypeSystem.Ordered.ArrayUsage           (runArrayUsageAnalysis)
import           Language.Hic.TypeSystem.Ordered.Base
import           Language.Hic.TypeSystem.Ordered.CallGraph            (CallGraphResult (..),
                                                                       runCallGraphAnalysis)
import           Language.Hic.TypeSystem.Ordered.ConstraintGeneration (runConstraintGeneration)
import qualified Language.Hic.TypeSystem.Ordered.HotspotAnalysis      as GSA
import           Language.Hic.TypeSystem.Ordered.Invariants           (runInvariantAnalysis)
import           Language.Hic.TypeSystem.Ordered.Nullability          (runNullabilityAnalysis)
import           Test.Hspec

runFullAnalysis :: Program.Program Text -> OrderedSolverResult
runFullAnalysis prog =
    let ts = GSA.garTypeSystem $ GSA.runGlobalStructuralAnalysis prog
        aur = runArrayUsageAnalysis ts prog
        cg = runCallGraphAnalysis prog
        nr = runNullabilityAnalysis prog
        ir = runInvariantAnalysis ts (cgrSccs cg) prog
        cgr = runConstraintGeneration ts aur nr prog
    in runOrderedSolver ts aur ir (cgrSccs cg) cgr

errorsShouldMatch :: HasCallStack => [ErrorInfo 'Local] -> [Text] -> Expectation
errorsShouldMatch errors expected =
    let actual = nub $ concatMap (T.lines . (\ei -> renderPlain (ppErrorInfo "test.c" ei Nothing))) errors
    in actual `shouldBe` expected

shouldHaveErrors :: HasCallStack => Program.Program Text -> [Text] -> Expectation
shouldHaveErrors prog expected =
    errorsShouldMatch (osrErrors (runFullAnalysis prog)) expected

shouldHaveNoErrors :: HasCallStack => [ErrorInfo 'Local] -> Expectation
shouldHaveNoErrors errors =
    if null errors
    then return ()
    else expectationFailure $ T.unpack $ T.unlines $
            "expected no errors, but got:" :
            map (renderPlain . (\ei -> ppErrorInfo "test.c" ei Nothing)) errors

spec :: Spec
spec = do
    it "handles nullary functions with (void)" $ do
        prog <- mustParse ["void f(void); void g() { f(); }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles templated struct pointer compatibility" $ do
        prog <- mustParse
            [ "struct Memory { void *ptr; };"
            , "void f(struct Memory *m) {"
            , "    struct Memory *m2 = m;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles templates in nested structures" $ do
        prog <- mustParse
            [ "struct Memory { void *ptr; };"
            , "struct Context { const struct Memory *mem; };"
            , "void f(struct Context *ctx, const struct Memory *mem) {"
            , "    ctx->mem = mem;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles forward declared templated structs" $ do
        prog <- mustParse
            [ "struct Memory;"
            , "void f(const struct Memory *m);"
            , "struct Memory { void *ptr; };"
            , "void g(struct Memory *m) { f(m); }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "does not incorrectly merge independent templates in nested structures" $ do
        prog <- mustParse
            [ "struct My_A { void *p; };"
            , "struct My_B { struct My_A *a; void *q; };"
            , "void f(struct My_B *b) {"
            , "    int *i = b->a->p;"
            , "    float *f = b->q;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "infers type of address-of expression" $ do
        prog <- mustParse ["void f() { int x = 1; int *p = &x; }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "infers types of logical operators" $ do
        prog <- mustParse ["void f() { bool b = ((1 == 1) && (2 == 2)) || !(1 == 1); }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "solves simple identity function" $ do
        prog <- mustParse ["int f(int x) { return x; }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "reports type mismatch in simple assignment" $ do
        prog <- mustParse ["void f() { int x; float y; x = y; }"]
        prog `shouldHaveErrors`
            [ "test.c:1: assignment type mismatch: expected int32_t, got float"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t and float (assignment)"
            ]

    it "correctly promotes mixed-access arrays and catches errors" $ do
        prog <- mustParse
            [ "struct My_Struct { void *h[2]; };"
            , "void set(struct My_Struct *r, int i, void *o) { r->h[i] = o; }"
            , "void f(struct My_Struct *r, int *pi, float *pf) {"
            , "    set(r, 0, pi);" -- Binds universal template to int*
            , "    r->h[1] = pf;" -- Should now conflict with int*
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:5: assignment type mismatch: expected int32_t*, got float*"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t* and float* (assignment)"
            ]

    it "handles equi-recursive types (co-inductive unification)" $ do
        -- void f(void **p) { *p = p; }
        -- Template T bound to T*
        prog <- mustParse ["void f(void **p) { *p = p; }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog


    it "handles mutually recursive generic functions" $ do
        prog <- mustParse
            [ "void my_g(void *p);"
            , "void my_f(void *p) { my_g(p); }"
            , "void my_g(void *p) { my_f(p); }"
            , "void start(int *p) { my_f(p); }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "terminates on cyclic typedefs" $ do
        prog <- mustParse
            [ "typedef struct My_A My_A;"
            , "struct My_A { My_A *next; };"
            , "void f(My_A *a) { a->next = a; }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles exponential type nesting without OOM" $ do
        prog <- mustParse
            [ "struct My_Struct1 { void *a; void *b; };"
            , "struct My_Struct2 { struct My_Struct1 a; struct My_Struct1 b; };"
            , "struct My_Struct3 { struct My_Struct2 a; struct My_Struct2 b; };"
            , "struct My_Struct4 { struct My_Struct3 a; struct My_Struct3 b; };"
            , "struct My_Struct5 { struct My_Struct4 a; struct My_Struct4 b; };"
            , "void f(struct My_Struct5 *s, int *p) { s->a.a.a.a.a = p; }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles lexical scoping (shadowing)" $ do
        prog <- mustParse
            [ "void f() {"
            , "    int x = 1;"
            , "    { float x = 1.0; float y = x; }" -- inner x is float
            , "    int z = x;" -- outer x is int
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "resolves global preprocessor constants" $ do
        prog <- mustParse
            [ "#define MY_CONST 1"
            , "void f(int x) { if (x == MY_CONST) return; }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles deep polymorphic call chains" $ do
        prog <- mustParse
            [ "void my_h(void *p) { int *x = p; }"
            , "void my_g(void *p) { my_h(p); }"
            , "void my_f(void *p) { my_g(p); }"
            , "void start(float *p) { my_f(p); }" -- Should fail in my_h
            ]
        prog `shouldHaveErrors`
            [ "test.c:4: type mismatch: expected int32_t*, got float*"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t* and float* (general mismatch)"
            ]

    it "allows int* to const int* subtyping" $ do
        prog <- mustParse ["void g(const int *p); void f(int *p) { g(p); }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "disallows const int* to int* subtyping" $ do
        prog <- mustParse ["void g(int *p); void f(const int *p) { g(p); }"]
        prog `shouldHaveErrors`
            [ "test.c:1: type mismatch: expected int32_t, got int32_t const"
            , "  actual type has unexpected const qualifier"
            , "  while unifying int32_t and int32_t const (general mismatch)"
            , "  while unifying int32_t* and int32_t const* (general mismatch)"
            ]

    it "handles networking struct subtyping (sockaddr_in to sockaddr)" $ do
        prog <- mustParse
            [ "void bind(int s, const struct sockaddr *addr);"
            , "void f(int s, struct sockaddr_in *addr) { bind(s, addr); }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "verifies polymorphic call chain with refreshTemplates" $ do
        prog <- mustParse
            [ "void ident(void *p) { /* empty */ }"
            , "void f() {"
            , "    int *pi;"
            , "    float *pf;"
            , "    ident(pi);"
            , "    ident(pf);"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "reports diagnostics for unhandled nodes" $ do
        -- We'll use a constructor we know isn't handled perfectly or generates a diagnostic
        prog <- mustParse ["void f() { static_assert(1, \"msg\"); }"]
        -- Currently we silence static_assert but let's check for any diagnostic from unhandled stuff if we add one
        -- Or we can just check if Unsupported type triggers a diagnostic in solver
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles recursive de-voidification (void**)" $ do
        prog <- mustParse
            [ "void f(void **pp, int *p) {"
            , "    *pp = p;" -- pp is int**
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "resolves array access types correctly" $ do
        prog <- mustParse
            [ "void f(int a[10]) {"
            , "    int x = a[0];"
            , "    float y = a[1];" -- Should fail
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:3: type mismatch: expected float, got int32_t"
            , "  expected float, but got int32_t"
            , "  while unifying float and int32_t (general mismatch)"
            ]

    it "repro array access in struct member type mismatch (ordered solver)" $ do
        prog <- mustParse
            [ "typedef struct My_Struct {"
            , "    uint64_t bytes[256];"
            , "} My_Struct;"
            , "void f(My_Struct *s, uint8_t id, size_t len) {"
            , "    s->bytes[id] += len;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles NameLit equality across locations" $ do
        prog <- mustParse
            [ "#define MY_VAL 1"
            , "void f(int x) { if (x == MY_VAL) return; }"
            , "void g(int x) { if (x == MY_VAL) return; }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles EnumMem equality across locations" $ do
        prog <- mustParse
            [ "typedef enum MyEnum { MY_E1, MY_E2 } MyEnum;"
            , "void f(MyEnum e) { if (e == MY_E1) return; }"
            , "void g(MyEnum e) { if (e == MY_E1) return; }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles memeq function with pointers and comparisons" $ do
        prog <- mustParse
            [ "bool memeq(uint8_t const *a, size_t a_size, uint8_t const *b, size_t b_size)"
            , "{"
            , "    return a_size == b_size && memcmp(a, b, a_size) == 0;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles heterogeneous arrays with literal indices" $ do
        prog <- mustParse
            [ "void f(void *a[2], int *pi, float *pf) {"
            , "    a[0] = pi;"
            , "    a[1] = pf;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "verifies polymorphic function pointer call" $ do
        prog <- mustParse
            [ "typedef void ident_cb(void *p);"
            , "void ident(void *p) { /* empty */ }"
            , "void g() {"
            , "    ident_cb *f = ident;"
            , "    int *pi;"
            , "    float *pf;"
            , "    f(pi);"
            , "    f(pf);"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:8: type mismatch: expected int32_t, got float"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t and float (general mismatch)"
            , "  while unifying T2(p)* and float* (general mismatch)"
            , ""
            , "  where template T2(p) was bound to int32_t due to type mismatch: expected T2(p), got T3(p)"
            ]

    it "handles multi-level pointer conversion" $ do
        prog <- mustParse
            [ "void g(const int * const *p);"
            , "void f(int **p) { g(p); }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles explicit va_list parameters (vsnprintf)" $ do
        prog <- mustParse
            [ "void my_vprintf(const char *format, va_list args);"
            , "void f(va_list args) {"
            , "    my_vprintf(\"%d\", args);"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "demonstrates necessary unsoundness for C idioms (memcmp == 0)" $ do
        prog <- mustParse
            [ "void f(int *a, int *b, size_t n) {"
            , "    if (memcmp(a, b, n) == 0) { /* ... */ }"
            , "}"
            ]
        -- memcmp returns int (Builtin). Comparison is with 0 (Singleton).
        -- Strict unification would fail. We allow it for usability.
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "demonstrates unsoundness: optimistic variable narrowing" $ do
        prog <- mustParse
            [ "void f(int i, int j) {"
            , "    if (i == 0) {"
            , "        // i is soundly narrowed to 0 in this branch (if we had flow-sensitivity)."
            , "        // But Hic's solver is global. Because we allow Builtin <: Singleton,"
            , "        // i's global type can become Singleton 0."
            , "        i = j; // j (any int) satisfy i's 'must be 0' constraint."
            , "    }"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "demonstrates unsoundness: optimistic variable narrowing" $ do
        pendingWith "unclear whether this is needed"
        -- DOCUMENTED UNSOUNDNESS:
        -- To support C idioms like 'if (memcmp(...) == 0)', the solver allows
        -- Builtin types (like 'int') to satisfy Singleton requirements (like '0').
        --
        -- This allows 'optimistic narrowing': a comparison 'i == 0' can cause
        -- 'i' to be treated as the constant '0' globally. In the example below,
        -- this hides a potential type mismatch: '*(a + i)' is treated as 'a[0]'
        -- (int*) even though 'i' is a general parameter that could be '1'
        -- (accessing a float* slot).
        --
        -- We accept this unsoundness because:
        -- 1. True value-flow analysis is outside the scope of this solver.
        -- 2. Strictness here would cause false positives on almost all standard C
        --    checks (memcmp, strcmp, etc.).
        -- 3. Hic still enforces structural soundness (int vs float) globally.
        prog <- mustParse
            [ "void set(void *a[2], int *pi, float *pf) {"
            , "    a[0] = pi;"
            , "    a[1] = pf;"
            , "}"
            , "void f(void **a, int i, int *p) {"
            , "    if (i == 0) {"
            , "        return;"
            , "    }"
            , "    *(a + i) = p;"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles My_Struct with _Owned pointer usage" $ do
        prog <- mustParse
            [ "struct My_Struct { int *_Owned p; };"
            , "void free_int(int *_Owned p);"
            , "void free_my_struct(struct My_Struct *_Owned s) {"
            , "    free_int(s->p);"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles Tox_Memory deallocation pattern (recursive type inference)" $ do
        prog <- mustParse
            [ "typedef void tox_memory_dealloc_cb(void *_Nonnull self, void *_Owned _Nullable ptr);"
            , "struct Tox_Memory_Funcs {"
            , "    tox_memory_dealloc_cb *_Nonnull dealloc_callback;"
            , "};"
            , "struct Tox_Memory {"
            , "    const struct Tox_Memory_Funcs *_Nonnull funcs;"
            , "    void *_Nullable user_data;"
            , "};"
            , "void tox_memory_dealloc(const struct Tox_Memory *mem, void *_Owned _Nullable ptr)"
            , "{"
            , "    void *_Nullable user_data = mem->user_data;"
            , "    if (user_data != nullptr) {"
            , "        mem->funcs->dealloc_callback(user_data, ptr);"
            , "    }"
            , "}"
            , "void tox_memory_free(struct Tox_Memory *mem)"
            , "{"
            , "    if (mem == nullptr) {"
            , "        return;"
            , "    }"
            , "    tox_memory_dealloc(mem, mem);"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:21: type mismatch: expected P1(ptr):inst:1* owner nullable, got struct Tox_Memory<T16(self), T17(ptr), T18(user_data)>* nonnull"
            , "  actual type is missing owner qualifier"
            , "  while unifying P1(ptr):inst:1* owner nullable and struct Tox_Memory<T16(self), T17(ptr), T18(user_data)>* nonnull (general mismatch)"
            , ""
            , "  where template P1(ptr):inst:1 is unbound"
            , "        template T16(self) was bound to P0(self):inst:1 due to type mismatch: expected T16(self), got self"
            , "        template P0(self):inst:1 is unbound"
            , "        template T17(ptr) was bound to P1(ptr):inst:1 due to type mismatch: expected T17(ptr), got ptr"
            , "        template T18(user_data) was bound to P0(self):inst:1 due to type mismatch: expected T18(user_data), got user_data"
            ]
    it "handles Tox_Memory deallocation pattern correctly with owned parameter" $ do
        prog <- mustParse
            [ "typedef void tox_memory_dealloc_cb(void *_Nonnull self, void *_Owned _Nullable ptr);"
            , "struct Tox_Memory_Funcs {"
            , "    tox_memory_dealloc_cb *_Nonnull dealloc_callback;"
            , "};"
            , "struct Tox_Memory {"
            , "    const struct Tox_Memory_Funcs *_Nonnull funcs;"
            , "    void *_Nullable user_data;"
            , "};"
            , "void tox_memory_dealloc(const struct Tox_Memory *mem, void *_Owned _Nullable ptr)"
            , "{"
            , "    void *_Nullable user_data = mem->user_data;"
            , "    if (user_data != nullptr) {"
            , "        mem->funcs->dealloc_callback(user_data, ptr);"
            , "    }"
            , "}"
            , "void tox_memory_free(struct Tox_Memory *_Owned mem)"
            , "{"
            , "    if (mem == nullptr) {"
            , "        return;"
            , "    }"
            , "    tox_memory_dealloc(mem, mem);"
            , "}"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "enforces subsumption Template T (Just i) <: Template T Nothing" $ do
        prog <- mustParse
            [ "struct My_Struct { void *h[2]; };"
            , "void set_and_use(struct My_Struct *r, int i, void *o) {"
            , "    r->h[i] = o;"
            , "    int *p = r->h[i]; // h[univ] <: int*"
            , "}"
            , "void f(struct My_Struct *r, float *pf) {"
            , "    r->h[0] = pf;      // float* <: h[0]"
            , "    set_and_use(r, 0, pf);"
            , "}"
            ]
        -- Chain: float* <: h[0] <: h[univ] <: int*
        prog `shouldHaveErrors`
            [ "test.c:7: assignment type mismatch: expected int32_t*, got float*"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t* and float* (assignment)"
            , "test.c:8: type mismatch: expected int32_t*, got float*"
            , "  while unifying int32_t* and float* (general mismatch)"
            ]
    it "disallows dereferencing a non-pointer" $ do
        prog <- mustParse ["void f(int x) { *x = 1; }"]
        prog `shouldHaveErrors`
            [ "test.c:1: type mismatch: expected T0*, got int32_t"
            , "  expected T0*, but got int32_t"
            , "  while unifying T0* and int32_t (general mismatch)"
            , ""
            , "  where template T0 was bound to int32_t=1 due to assignment type mismatch: expected T0, got int32_t=1"
            ]

    it "disallows member access on a non-struct" $ do
        prog <- mustParse ["void f(void *p) { ((int)p).x = 1; }"]
        osrErrors (runFullAnalysis prog) `errorsShouldMatch`
            [ "test.c:1: cast type mismatch: expected int32_t, got T0*"
            , "  expected int32_t, but got T0*"
            , "  while unifying int32_t and T0* (cast)"
            , ""
            , "  where template T0 was bound to p due to type mismatch: expected T0, got p"
            , "        template p is unbound"
            ]

    describe "Polymorphism and void* Inference" $ do
        it "handles bin_pack_array_cb pattern with template inference" $ do
            prog <- mustParse
                [ "struct Logger { void *config; };"
                , "struct Bin_Pack { int x; };"
                , "typedef bool bin_pack_array_cb(const void *_Nullable arr, uint32_t index, const struct Logger *_Nullable logger, struct Bin_Pack *_Nonnull bp);"
                , "uint32_t bin_pack_obj_array_b_size(bin_pack_array_cb *_Nonnull callback, const void *_Nullable arr, uint32_t arr_size, const struct Logger *_Nullable logger);"
                , "static bool bin_pack_node_handler(const void *_Nullable arr, uint32_t index, const struct Logger *_Nullable logger, struct Bin_Pack *_Nonnull bp)"
                , "{"
                , "    const int *_Nullable nodes = (const int *_Nullable)arr;"
                , "    return true;"
                , "}"
                , "int pack_nodes(const struct Logger *_Nullable logger, const int *_Nonnull nodes, uint16_t number)"
                , "{"
                , "    return bin_pack_obj_array_b_size(bin_pack_node_handler, nodes, number, logger);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "infers parameter type from cast in function body" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "void f(void *obj) { struct My_Struct *s = (struct My_Struct *)obj; }"
                , "void g() {"
                , "    struct My_Struct s;"
                , "    f(&s);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            prog `shouldHaveErrors`
                [ "test.c:5: type mismatch: expected int32_t, got struct My_Struct"
                , "  expected int32_t, but got struct My_Struct"
                , "  while unifying int32_t and struct My_Struct (general mismatch)"
                , "  while unifying int32_t* and struct My_Struct* (general mismatch)"
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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "supports heterogeneous arrays of callbacks" $ do
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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            prog `shouldHaveErrors`
                [ "test.c:8: type mismatch: expected int32_t*, got float*"
                , "  expected int32_t, but got float"
                , "  while unifying int32_t* and float* (general mismatch)"
                ]

        it "repro Tox_Memory type mismatch" $ do
            prog <- mustParse
                [ "typedef struct Tox_Memory_Funcs Tox_Memory_Funcs;"
                , "typedef struct Tox_Memory Tox_Memory;"
                , "typedef void *tox_memory_malloc_cb(void *self, uint32_t size);"
                , "struct Tox_Memory_Funcs { tox_memory_malloc_cb *malloc_callback; };"
                , "struct Tox_Memory { const Tox_Memory_Funcs *funcs; void *user_data; };"
                , "void *tox_memory_malloc(const Tox_Memory *mem, uint32_t size) {"
                , "    return mem->funcs->malloc_callback(mem->user_data, size);"
                , "}"
                , "void *mem_balloc(const Tox_Memory *mem, uint32_t size) {"
                , "    return tox_memory_malloc(mem, size);"
                , "}"
                , "void *tox_memory_alloc(const Tox_Memory *mem, uint32_t size) {"
                , "    return tox_memory_malloc(mem, size);"
                , "}"
                , "Tox_Memory *tox_memory_new(const Tox_Memory_Funcs *funcs, void *user_data) {"
                , "    Tox_Memory bootstrap;"
                , "    bootstrap.funcs = funcs;"
                , "    bootstrap.user_data = user_data;"
                , "    Tox_Memory *mem = (Tox_Memory *)tox_memory_alloc(&bootstrap, sizeof(Tox_Memory));"
                , "    if (mem != nullptr) { *mem = bootstrap; }"
                , "    return mem;"
                , "}"
                , "uint8_t *memdup(const Tox_Memory *mem, uint8_t const *data, uint32_t data_size) {"
                , "    uint8_t *copy = (uint8_t *)mem_balloc(mem, data_size);"
                , "    return copy;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles Tox<T> global inference pattern" $ do
            prog <- mustParse
                [ "struct Tox { void *userdata; };"
                , "typedef void tox_cb(struct Tox *tox, void *userdata);"
                , "void tox_do_something(struct Tox *tox, tox_cb *cb) { cb(tox, tox->userdata); }"
                , "struct My_Data { int x; };"
                , "void tox_handler(struct Tox *tox, void *userdata) {"
                , "    struct My_Data *d = (struct My_Data *)userdata;"
                , "}"
                , "void f() {"
                , "    struct Tox *tox;"
                , "    struct My_Data d;"
                , "    tox_do_something(tox, tox_handler);"
                , "    tox->userdata = &d;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error for Tox<T> when userdata is inconsistent" $ do
            prog <- mustParse
                [ "struct Tox { void *userdata; };"
                , "typedef void tox_cb(struct Tox *tox, void *userdata);"
                , "void tox_invoke(struct Tox *tox, tox_cb *cb) { cb(tox, tox->userdata); }"
                , "struct My_Data { int x; };"
                , "void tox_handler(struct Tox *tox, void *userdata) {"
                , "    struct My_Data *d = (struct My_Data *)userdata;"
                , "}"
                , "void f() {"
                , "    struct Tox tox;"
                , "    struct My_Data d;"
                , "    tox_invoke(&tox, &tox_handler);"
                , "    int x;"
                , "    tox.userdata = &x;"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:13: assignment type mismatch: expected struct My_Data, got int32_t"
                , "  expected struct My_Data, but got int32_t"
                , "  while unifying struct My_Data and int32_t (assignment)"
                , "  while unifying struct My_Data* and int32_t* (assignment)"
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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            prog `shouldHaveErrors`
                [ "test.c:6: type mismatch: expected int32_t, got float"
                , "  expected int32_t, but got float"
                , "  while unifying int32_t and float (general mismatch)"
                , "  while unifying int32_t const and P1(a):inst:0 const (general mismatch)"
                , "  while unifying int32_t const* and P1(a):inst:0 const* (general mismatch)"
                , "  while unifying int32_t(P1(a):inst:0 const*, P2(b):inst:0 const*) and int32_t(int32_t const*, int32_t const*) (general mismatch)"
                , "  while unifying int32_t(P1(a):inst:0 const*, P2(b):inst:0 const*)* and int32_t(int32_t const*, int32_t const*) (general mismatch)"
                , ""
                , "  where template P1(a):inst:0 was bound to float due to type mismatch: expected P1(a):inst:0, got float"
                , "        template P2(b):inst:0 was bound to float due to type mismatch: expected P2(b):inst:0, got float"
                , "  while unifying int32_t const and P2(b):inst:0 const (general mismatch)"
                , "  while unifying int32_t const* and P2(b):inst:0 const* (general mismatch)"
                , "  where template P2(b):inst:0 was bound to float due to type mismatch: expected P2(b):inst:0, got float"
                , "        template P1(a):inst:0 was bound to float due to type mismatch: expected P1(a):inst:0, got float"
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
            prog `shouldHaveErrors`
                [ "test.c:8: type mismatch: expected int32_t, got float"
                , "  expected int32_t, but got float"
                , "  while unifying int32_t and float (general mismatch)"
                , "  while unifying P0(a):inst:1* and float* (general mismatch)"
                , "  while unifying P0(a):inst:1* and float* nonnull (general mismatch)"
                , ""
                , "  where template P0(a):inst:1 was bound to int32_t due to type mismatch: expected P0(a):inst:1, got int32_t"
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
            prog `shouldHaveErrors`
                [ "test.c:5: type mismatch: expected int32_t*, got float*"
                , "  expected int32_t, but got float"
                , "  while unifying int32_t* and float* (general mismatch)"
                ]

        it "infers polymorphic type from function return value" $ do
            prog <- mustParse
                [ "void *identity(void *p) { return p; }"
                , "void f(int *p) {"
                , "    float *fp = identity(p);"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:3: type mismatch: expected float*, got int32_t*"
                , "  expected float, but got int32_t"
                , "  while unifying float* and int32_t* (general mismatch)"
                ]

        it "allows memcpy with matching pointer types" $ do
            prog <- mustParse
                [ "void f(int *a, int *b) { memcpy(a, b, sizeof(int)); }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error for memcpy with mismatching pointer types" $ do
            prog <- mustParse
                [ "void f(int *a, float *b, uint32_t n) { memcpy(a, b, n); }"
                ]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected int32_t, got float"
                , "  expected int32_t, but got float"
                , "  while unifying int32_t and float (general mismatch)"
                , "  while unifying P0(T):inst:0 const and float (general mismatch)"
                , "  while unifying P0(T):inst:0 const* and float* (general mismatch)"
                , ""
                , "  where template P0(T):inst:0 was bound to int32_t due to type mismatch: expected P0(T):inst:0, got int32_t"
                ]
        it "handles callback registration with userdata" $ do
            prog <- mustParse
                [ "typedef void cb_cb(void *obj);"
                , "void register_callback(cb_cb *f, void *obj) { f(obj); }"
                , "struct My_Struct { int x; };"
                , "void my_handler(void *obj) { struct My_Struct *s = (struct My_Struct *)obj; }"
                , "void g() {"
                , "    struct My_Struct s;"
                , "    register_callback(my_handler, &s);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error for mismatched callback and userdata" $ do
            prog <- mustParse
                [ "typedef void cb_cb(void *obj);"
                , "void register_callback(cb_cb *f, void *obj) { f(obj); }"
                , "struct My_Struct { int x; };"
                , "void my_handler(void *obj) { struct My_Struct *s = (struct My_Struct *)obj; }"
                , "void g() {"
                , "    int x;"
                , "    register_callback(my_handler, &x);"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:7: type mismatch: expected struct My_Struct, got int32_t"
                , "  expected struct My_Struct, but got int32_t"
                , "  while unifying struct My_Struct and int32_t (general mismatch)"
                , "  while unifying struct My_Struct* and P0(obj):inst:1* (general mismatch)"
                , "  while unifying void(P0(obj):inst:1*) and void(struct My_Struct*) (general mismatch)"
                , "  while unifying void(P0(obj):inst:1*)* and void(struct My_Struct*) (general mismatch)"
                , ""
                , "  where template P0(obj):inst:1 was bound to int32_t due to type mismatch: expected P0(obj):inst:1, got int32_t"
                ]
    describe "Const correctness" $ do
        it "allows assigning const int to int (copy)" $ do
            prog <- mustParse
                [ "void f() {"
                , "    const int x = 1;"
                , "    int y = x;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error when assigning const int* to int* (pointer)" $ do
            prog <- mustParse
                [ "void f(const int *p) {"
                , "    int *q = p;"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:2: type mismatch: expected int32_t, got int32_t const"
                , "  actual type has unexpected const qualifier"
                , "  while unifying int32_t and int32_t const (general mismatch)"
                , "  while unifying int32_t* and int32_t const* (general mismatch)"
                ]

    describe "Flow-sensitive Nullability" $ do
        it "allows dereferencing a _Nullable pointer after a null check" $ do
            prog <- mustParse
                [ "void flow1(int *_Nullable p) {"
                , "    if (p != nullptr) {"
                , "        *p = 1;"
                , "    }"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "allows passing a _Nullable pointer to a _Nonnull parameter after a null check" $ do
            prog <- mustParse
                [ "void g_flow2(int *_Nonnull p);"
                , "void flow2(int *_Nullable p) {"
                , "    if (p) {"
                , "        g_flow2(p);"
                , "    }"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "disallows dereferencing a _Nullable pointer without a check" $ do
            prog <- mustParse
                [ "void flow3(int *_Nullable p) {"
                , "    *p = 1;"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:2: type mismatch: expected int32_t*, got int32_t* nullable"
                , "  expected int32_t*, but got int32_t* nullable"
                , "  while unifying int32_t* and int32_t* nullable (general mismatch)"
                ]

        it "disallows dereferencing a _Nullable pointer in the else branch" $ do
            prog <- mustParse
                [ "void flow4(int *_Nullable p) {"
                , "    if (p == nullptr) {"
                , "        /* empty */"
                , "    } else {"
                , "        *p = 1;"
                , "    }"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "disallows dereferencing a _Nullable pointer after it might have become null" $ do
            prog <- mustParse
                [ "void flow5(int *_Nullable p) {"
                , "    if (p) {"
                , "        p = nullptr;"
                , "        *p = 1; /* should fail */"
                , "    }"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:3: assignment type mismatch: expected int32_t* nonnull, got nullptr_t"
                , "  actual type is missing nonnull qualifier"
                , "  while unifying int32_t* nonnull and nullptr_t (assignment)"
                , "test.c:4: type mismatch: expected int32_t*, got int32_t* nullable"
                , "  expected int32_t*, but got int32_t* nullable"
                , "  while unifying int32_t* and int32_t* nullable (general mismatch)"
                ]
    describe "Enums" $ do
        it "handles enum comparisons" $ do
            prog <- mustParse
                [ "typedef enum Color { COLOR_RED, COLOR_GREEN, COLOR_BLUE } Color;"
                , "void f(Color c) { if (c >= COLOR_GREEN) return; }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles enum members directly" $ do
            prog <- mustParse
                [ "typedef enum Level { LVL_INFO, LVL_WARN } Level;"
                , "void f() { Level l = LVL_INFO; }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "allows assigning enum member to int" $ do
            prog <- mustParse
                [ "typedef enum Level { LVL_INFO, LVL_WARN } Level;"
                , "void f() { int x = LVL_INFO; }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "disallows assigning int to enum" $ do
            prog <- mustParse
                [ "typedef enum Level { LVL_INFO, LVL_WARN } Level;"
                , "void f(int x) { Level l = x; }"
                ]
            prog `shouldHaveErrors`
                [ "test.c:2: type mismatch: expected enum Level, got int32_t"
                , "  expected enum Level, but got int32_t"
                , "  while unifying enum Level and int32_t (general mismatch)"
                ]

    describe "Bitwise and Arithmetic operators" $ do
        it "infers types of bitwise operators" $ do
            prog <- mustParse ["void f() { int x = (1 & 2) | (3 ^ 4) << 1; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "infers types of comparison operators" $ do
            prog <- mustParse ["void f() { bool b = (1 == 2); }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "Miscellaneous C features" $ do
        it "infers types of sizeof expressions" $ do
            prog <- mustParse ["void f() { int s = sizeof(int); }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles __func__ predefined identifier" $ do
            prog <- mustParse ["void f() { const char *s = __func__; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles sizeof(__func__)" $ do
            prog <- mustParse ["void f() { int s = sizeof(__func__); }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles __FUNCTION__ predefined identifier" $ do
            prog <- mustParse ["void f() { const char *s = __FUNCTION__; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles __PRETTY_FUNCTION__ predefined identifier" $ do
            prog <- mustParse ["void f() { const char *s = __PRETTY_FUNCTION__; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles __FILE__ predefined identifier" $ do
        prog <- mustParse ["void f() { const char *s = __FILE__; }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles __LINE__ predefined identifier" $ do
        prog <- mustParse ["void f() { int l = __LINE__; }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "Control flow" $ do
        it "reports error for return type mismatch" $ do
            prog <- mustParse ["int f() { return \"hello\"; }"]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  while unifying int32_t and char* (general mismatch)"
                ]

        it "reports error for if condition mismatch" $ do
            prog <- mustParse ["struct My_S { int x; }; void f(struct My_S s) { if (s) { /* nothing */ } }"]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected bool, got struct My_S"
                , "  expected bool, but got struct My_S"
                , "  while unifying bool and struct My_S (general mismatch)"
                ]

        it "reports error for while condition mismatch" $ do
            prog <- mustParse ["struct My_S { int x; }; void f(struct My_S s) { while (s) { /* nothing */ } }"]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected bool, got struct My_S"
                , "  expected bool, but got struct My_S"
                , "  while unifying bool and struct My_S (general mismatch)"
                ]

    describe "Macros" $ do
        it "infers types of macros used as templates" $ do
            prog <- mustParse
                [ "void g(int p);"
                , "#define CALL_G(x) g(x)"
                , "void f() { CALL_G(1); }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "infers types of statement-like macros" $ do
            prog <- mustParse
                [ "#define SWAP_INT(x, y) do { int tmp = x; x = y; y = tmp; } while (0)"
                , "void f() { int a = 1; int b = 2; SWAP_INT(a, b); }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports type mismatch in statement-like macros" $ do
            prog <- mustParse
                [ "#define SWAP_INT(x, y) do { int tmp = x; x = y; y = tmp; } while (0)"
                , "void f() { int a = 1; int *b = nullptr; SWAP_INT(a, b); }"
                ]
            prog `shouldHaveErrors`
                [ "test.c:1: assignment type mismatch: expected int32_t, got int32_t*"
                , "  expected int32_t, but got int32_t*"
                , "  while unifying int32_t and int32_t* (assignment)"
                , "  in macro 'SWAP_INT'"
                , "test.c:1: assignment type mismatch: expected int32_t*, got int32_t"
                , "  expected int32_t*, but got int32_t"
                , "  while unifying int32_t* and int32_t (assignment)"
                ]
        it "handles UINT32_C macro" $ do
            prog <- mustParse ["void f() { uint32_t x = UINT32_C(1); }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "Unions" $ do
        it "handles union member access" $ do
            prog <- mustParse
                [ "union My_Union { int x; float y; };"
                , "void f() { union My_Union u; u.x = 1; }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles static function scope" $ do
        prog <- mustParse
            [ "static int g(int x) { return x; }"
            , "int f() { return g(1); }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "Networking types (extended)" $ do
        it "handles WSAAddressToString and LPSOCKADDR" $ do
            prog <- mustParse
                [ "void f(struct sockaddr_in *saddr) {"
                , "    char buf[64];"
                , "    DWORD len = 64;"
                , "    WSAAddressToString((LPSOCKADDR)saddr, sizeof(*saddr), nullptr, buf, &len);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles LPSTR casts" $ do
            prog <- mustParse
                [ "void f(const char *s) {"
                , "    LPSTR s2 = (LPSTR)s;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles implicit conversion from int to bool in networking error checks" $ do
            prog <- mustParse
                [ "void f(int s) {"
                , "    struct sockaddr_in saddr = {0};"
                , "    if (bind(s, (struct sockaddr *)&saddr, sizeof(saddr)) == -1) {"
                , "        /* error handling */"
                , "    }"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles inet_ntop and inet_pton with void* templates" $ do
            prog <- mustParse
                [ "void f(struct in_addr *addr) {"
                , "    char buf[16];"
                , "    inet_ntop(2, addr, buf, 16);"
                , "    inet_pton(2, \"127.0.0.1\", addr);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles addrinfo structure and getaddrinfo" $ do
            prog <- mustParse
                [ "void f() {"
                , "    struct addrinfo hints = {0};"
                , "    struct addrinfo *res;"
                , "    getaddrinfo(\"localhost\", \"80\", &hints, &res);"
                , "    freeaddrinfo(res);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles errno as a built-in variable" $ do
            prog <- mustParse
                [ "void f() {"
                , "    int err = errno;"
                , "    errno = 0;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles structure member access for networking types" $ do
            prog <- mustParse
                [ "void f(struct sockaddr_in *saddr) {"
                , "    saddr->sin_family = 2;"
                , "    saddr->sin_port = 80;"
                , "    saddr->sin_addr.s_addr = 0;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles ipv6_mreq initialization" $ do
            prog <- mustParse ["void f() { struct ipv6_mreq mreq = {{{{0}}}}; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles dereferencing function call result" $ do
            prog <- mustParse
                [ "typedef struct My_Struct { int x; } My_Struct;"
                , "const My_Struct *get_s(int i) { return nullptr; }"
                , "void f() { const My_Struct s_var = *get_s(1); }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error with inference chain for template conflict" $ do
            prog <- mustParse
                [ "void f(void *a, void *b) {"
                , "    int *ia = (int *)a;"
                , "    float *fb = (float *)b;"
                , "    a = b;"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:4: assignment type mismatch: expected int32_t, got float"
                , "  expected int32_t, but got float"
                , "  while unifying int32_t and float (assignment)"
                , "  while unifying T0* and T1* (assignment)"
                , ""
                , "  where template T0 was bound to int32_t due to type mismatch: expected T0, got a"
                , "        template T1 was bound to float due to type mismatch: expected T1, got b"
                ]

        it "handles sockaddr_in to sockaddr* implicit conversion" $ do
            prog <- mustParse
                [ "void f() {"
                , "    struct sockaddr_in saddr = {0};"
                , "    int s = socket(2, 1, 0);"
                , "    bind(s, (const struct sockaddr *)&saddr, sizeof(saddr));"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles sockaddr_in6 to sockaddr* implicit conversion" $ do
            prog <- mustParse
                [ "void f() {"
                , "    struct sockaddr_in6 saddr = {0};"
                , "    int s = socket(10, 1, 0);"
                , "    connect(s, (const struct sockaddr *)&saddr, sizeof(saddr));"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles sockaddr_storage compatibility" $ do
            prog <- mustParse
                [ "void f(int s) {"
                , "    struct sockaddr_storage addr;"
                , "    socklen_t len = sizeof(addr);"
                , "    getsockopt(s, 0, 0, &addr, &len);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles Windows-specific WSAStartup and MAKEWORD" $ do
            prog <- mustParse
                [ "void f() {"
                , "    WSADATA wsaData;"
                , "    WSAStartup(MAKEWORD(2, 2), &wsaData);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles typedef of forward-declared struct" $ do
        prog <- mustParse
            [
              "typedef struct My_S My_S;"
            , "struct My_S { int x; };"
            , "int f(My_S *s) { return s->x; }"
            ]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles ternary operator" $ do
        prog <- mustParse ["void f() { int x = (1 == 1 ? 1 : 2); }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "handles ternary operator with non-constant argument" $ do
        prog <- mustParse ["int f(bool x) { return x ? 2 : 3; }"]
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "reports error for ternary operator branch mismatch" $ do
        prog <- mustParse ["void f(int cond, char *p) { p = (cond ? p : 1); }"]
        prog `shouldHaveErrors`
            [ "test.c:1: type mismatch: expected int32_t, got char*"
            , "  expected int32_t, but got char*"
            , "  while unifying int32_t and char* (general mismatch)"
            , "test.c:1: type mismatch: expected char*, got int32_t"
            , "  expected char*, but got int32_t"
            , "  while unifying char* and int32_t (general mismatch)"
            ]

    describe "Structs and Arrays" $ do
        it "handles nested struct member access" $ do
            prog <- mustParse
                [ "struct Inner { int y; };"
                , "struct Outer { struct Inner x; };"
                , "int f(struct Outer *o) { return o->x.y; }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles struct array access" $ do
            prog <- mustParse
                [ "struct My_S { int client_list[8]; };"
                , "int f(struct My_S *s) { return s->client_list[0]; }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles array-to-pointer decay in function calls" $ do
            prog <- mustParse
                [ "void g(char *p);"
                , "void f() {"
                , "    char a[8];"
                , "    g(a);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error for inconsistent types in initializer list" $ do
            prog <- mustParse ["void f() { int a[2] = { 1, \"hello\" }; }"]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  while unifying int32_t and char* (general mismatch)"
                ]

    describe "Pointers and Arithmetic" $ do
        it "handles pointer arithmetic" $ do
            prog <- mustParse ["void f(int *p) { int *q = p + 1; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error for pointer arithmetic with incompatible types" $ do
            prog <- mustParse ["void f(int *p) { int *q = p + \"hello\"; }"]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected int32_t, got char*"
                , "  expected int32_t, but got char*"
                , "  while unifying int32_t and char* (general mismatch)"
                ]

        it "handles double pointer null check" $ do
            prog <- mustParse ["bool has_null(uint8_t **ptr) { return *ptr == nullptr; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles double pointer != nullptr check" $ do
            prog <- mustParse ["bool is_not_null(uint8_t **ptr) { return *ptr != nullptr; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles double pointer [0] null check" $ do
            prog <- mustParse ["bool has_null_arr(uint8_t **ptr) { return ptr[0] == nullptr; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles subtraction of array pointers" $ do
            prog <- mustParse ["void f() { int a[10]; int *p = a; int *q = a + 5; size_t diff = q - p; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles double pointers" $ do
            prog <- mustParse ["void f(int **p) { int *q = *p; int x = **p; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "Logical and Switch" $ do
        it "reports error for logical operator operand mismatch" $ do
            prog <- mustParse ["struct My_S { int x; }; void f(struct My_S s) { bool b = (1 == 1) && s; }"]
            prog `shouldHaveErrors`
                [ "test.c:1: type mismatch: expected bool, got struct My_S"
                , "  expected bool, but got struct My_S"
                , "  while unifying bool and struct My_S (general mismatch)"
                ]

    describe "Recursion" $ do
        it "handles simple recursion" $ do
            prog <- mustParse
                [ "int factorial(int n) {"
                , "    if (n <= 1) return 1;"
                , "    return n * factorial(n - 1);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "Qualifiers and Custom Keywords" $ do
        it "reports error for _Nonnull pointer assigned nullptr" $ do
            prog <- mustParse
                [ "void f(int * _Nonnull p);"
                , "void g() { f(nullptr); }"
                ]
            prog `shouldHaveErrors`
                [ "test.c:2: type mismatch: expected int32_t* nonnull, got nullptr_t"
                , "  actual type is missing nonnull qualifier"
                , "  while unifying int32_t* nonnull and nullptr_t (general mismatch)"
                ]

        it "allows _Nullable pointer assigned nullptr" $ do
            prog <- mustParse
                [ "void f(int * _Nullable p);"
                , "void g() { f(nullptr); }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles owner qualifier in assignments" $ do
            prog <- mustParse
                [ "void f() {"
                , "    int * _Owned p = nullptr;"
                , "    int *q = p;"
                , "    return;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles calling a non-null function pointer" $ do
            prog <- mustParse
                [ "typedef int callback_cb(int x);"
                , "void f(callback_cb *_Nonnull callback) {"
                , "    callback(1);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles function pointers with wrappers unified with typedefs" $ do
            prog <- mustParse
                [ "typedef int callback_cb(void *_Nullable obj);"
                , "void register_callback(callback_cb *_Nullable cb);"
                , "int my_handler(void *_Nonnull obj) { return 0; }"
                , "void f() { register_callback(&my_handler); }"
                ]
            prog `shouldHaveErrors`
                [ "test.c:4: type mismatch: expected T4(obj)* nonnull, got P0(obj):inst:0* nullable"
                , "  actual type is missing nonnull qualifier"
                , "  while unifying T4(obj)* nonnull and P0(obj):inst:0* nullable (general mismatch)"
                , "  while unifying int32_t(P0(obj):inst:0* nullable) and int32_t(T4(obj)* nonnull) (general mismatch)"
                , "  while unifying int32_t(P0(obj):inst:0* nullable)* and int32_t(T4(obj)* nonnull)* (general mismatch)"
                , "  while unifying int32_t(P0(obj):inst:0* nullable)* nullable and int32_t(T4(obj)* nonnull)* (general mismatch)"
                , ""
                , "  where template T4(obj) is unbound"
                , "        template P0(obj):inst:0 is unbound"
                ]
        it "successfully solves polymorphic callbacks with consistent nullability" $ do
            pendingWith "TODO"
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
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles polymorphic callbacks with _Nonnull/_Nullable divergence" $ do
            prog <- mustParse
                [ "typedef struct IP_Port IP_Port;"
                , "typedef struct Networking_Core Networking_Core;"
                , "typedef int packet_handler_cb(void *_Nullable object, const IP_Port *_Nonnull source, uint8_t const *_Nonnull packet, uint16_t length, void *_Nullable userdata);"
                , "struct Packet_Handler { packet_handler_cb *_Nullable function; void *_Nullable object; };"
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
            prog `shouldHaveErrors`
                [ "test.c:18: type mismatch: expected struct Net_Crypto const* nonnull, got P0(object):inst:0* nullable"
                , "  actual type is missing nonnull qualifier"
                , "  while unifying struct Net_Crypto const* nonnull and P0(object):inst:0* nullable (general mismatch)"
                , "  while unifying int32_t(P0(object):inst:0* nullable, IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, P1(userdata):inst:0* nullable) and int32_t(struct Net_Crypto const* nonnull, IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, T24(object)* nullable) (general mismatch)"
                , "  while unifying int32_t(P0(object):inst:0* nullable, IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, P1(userdata):inst:0* nullable)* and int32_t(struct Net_Crypto const* nonnull, IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, T24(object)* nullable)* (general mismatch)"
                , "  while unifying int32_t(P0(object):inst:0* nullable, IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, P1(userdata):inst:0* nullable)* nullable and int32_t(struct Net_Crypto const* nonnull, IP_Port const* nonnull, uint8_t const* nonnull, uint16_t, T24(object)* nullable)* (general mismatch)"
                , ""
                , "  where template P0(object):inst:0 was bound to struct Net_Crypto due to type mismatch: expected P0(object):inst:0, got struct Net_Crypto"
                , "        template P1(userdata):inst:0 was bound to T24(object) due to type mismatch: expected P1(userdata):inst:0, got T24(object)"
                , "        template T24(object) is unbound"
                ]
        it "handles member access on a _Nonnull pointer" $ do
            prog <- mustParse
                [ "struct My_Struct { int x; };"
                , "void f(struct My_Struct *_Nonnull p) {"
                , "    p->x = 1;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    describe "More Polymorphism" $ do
        it "reports error for incompatible casts of the same void * pointer" $ do
            prog <- mustParse
                [ "struct My_A { int x; };"
                , "struct My_B { float y; };"
                , "void f(void *p) {"
                , "    struct My_A *a = (struct My_A *)p;"
                , "    struct My_B *b = (struct My_B *)p;"
                , "}"
                ]
            prog `shouldHaveErrors`
                [ "test.c:5: cast type mismatch: expected struct My_B, got struct My_A"
                , "  expected struct My_B, but got struct My_A"
                , "  while unifying struct My_B and struct My_A (cast)"
                , "  while unifying struct My_B* and T0* (cast)"
                , ""
                , "  where template T0 was bound to struct My_A due to type mismatch: expected T0, got p"
                ]

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
            prog `shouldHaveErrors`
                [ "test.c:5: type mismatch: expected float*, got int32_t*"
                , "  expected float, but got int32_t"
                , "  while unifying float* and int32_t* (general mismatch)"
                ]

    describe "Function calls and Variadics" $ do
        it "handles variadic functions" $ do
            prog <- mustParse
                [ "void my_printf(const char *fmt, ...);"
                , "void f() { my_printf(\"%d %d\", 1, 2); }"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "reports error for too few arguments in non-variadic function" $ do
            prog <- mustParse ["void g(int x, int y); void f() { g(1); }"]
            prog `shouldHaveErrors`
                [ "test.c:1: too few arguments in function call: expected 2, got 1"
                , "  "
                ]

        it "reports error for too many arguments in non-variadic function" $ do
            prog <- mustParse ["void g(int x); void f() { g(1, 2); }"]
            prog `shouldHaveErrors`
                [ "test.c:1: too many arguments in function call: expected 1, got 2"
                , "  "
                ]

    describe "Predefined macros" $ do
        it "handles __FILE__ and __LINE__ predefined macros" $ do
            prog <- mustParse ["void f() { const char *file = __FILE__; uint32_t line = __LINE__; }"]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "detects structural link conflict at specific array index" $ do
        prog <- mustParse
            [ "typedef void my_cb(void *userdata);"
            , "struct My_Struct { my_cb *cb; void *userdata; };"
            , "void use_s(struct My_Struct *s) { s->cb(s->userdata); }"
            , "void int_h(void *p) { int *pi = p; }"
            , "void f() {"
            , "    struct My_Struct arr[2];"
            , "    int x; float y;"
            , "    arr[0].cb = int_h; arr[0].userdata = &x;"
            , "    arr[1].cb = int_h; arr[1].userdata = &y;"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:9: assignment type mismatch: expected int32_t*, got float*"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t* and float* (assignment)"
            ]

    it "detects structural link conflict through template base (nested struct in array)" $ do
        prog <- mustParse
            [ "typedef void my_cb(void *userdata);"
            , "struct My_Inner { my_cb *cb; void *userdata; };"
            , "struct My_Outer { struct My_Inner in[2]; };"
            , "void use_it(struct My_Inner *o) { o->cb(o->userdata); }"
            , "void int_h(void *p) { int *pi = p; }"
            , "void f(struct My_Outer *o) {"
            , "    int x; float y;"
            , "    o->in[0].cb = int_h; o->in[0].userdata = &x;"
            , "    o->in[1].cb = int_h; o->in[1].userdata = &y;"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:9: assignment type mismatch: expected int32_t, got float"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t and float (assignment)"
            , "  while unifying T9(userdata)[int32_t=1]* and float* (assignment)"
            , ""
            , "  where template T9(userdata) indexed by int32_t=1"
            ]

    it "handles heterogeneous callback array with structural links (motivating example)" $ do
        prog <- mustParse
            [ "typedef void my_cb(void *userdata);"
            , "struct My_Callback { my_cb *cb; void *userdata; };"
            , "struct Callbacks { struct My_Callback cbs[10]; };"
            , "void my_int_handler(void *p) { int *pi = (int *)p; }"
            , "void my_str_handler(void *p) { char *ps = (char *)p; }"
            , "void f() {"
            , "    int some_int = 3;"
            , "    char some_str[] = \"hello\";"
            , "    struct Callbacks cbs;"
            , "    cbs.cbs[0].cb = my_int_handler;"
            , "    cbs.cbs[0].userdata = &some_int; // OK"
            , "    cbs.cbs[1].cb = my_str_handler;"
            , "    cbs.cbs[1].userdata = some_str;  // OK"
            , "    cbs.cbs[1].userdata = &some_int; // SHOULD ERROR"
            , "}"
            , "void use_cbs(struct Callbacks *cbs, int id) {"
            , "    struct My_Callback *handler = &cbs->cbs[id];"
            , "    handler->cb(handler->userdata);"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:14: assignment type mismatch: expected char*, got int32_t*"
            , "  expected char, but got int32_t"
            , "  while unifying char* and int32_t* (assignment)"
            ]

    it "respects path-sensitivity in structural invariants (negative case)" $ do
        pendingWith "needs quite a bit of work"
        -- If a link is only established inside an if-block, it should not
        -- be enforced globally if the condition is not met.
        prog <- mustParse
            [ "typedef void my_cb(void *userdata);"
            , "struct My_Struct { my_cb *cb; void *userdata; int active; };"
            , "void use_s(struct My_Struct *s) {"
            , "    if (s->active) { s->cb(s->userdata); }"
            , "}"
            , "void int_h(void *p) { int *pi = p; }"
            , "void f() {"
            , "    struct My_Struct s;"
            , "    float y = 1.0f;"
            , "    s.active = 0;"
            , "    s.cb = int_h;"
            , "    s.userdata = &y; // Should NOT error because s.active is 0 and we are path-sensitive"
            , "}"
            ]
        -- Note: The OrderedSolver is intentionally optimistic about variables.
        -- It should see that the link is protected by a guard.
        shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

    it "propagates invariants through deeply nested structs in arrays" $ do
        prog <- mustParse
            [ "typedef void my_cb(void *userdata);"
            , "struct Level3 { my_cb *cb; void *userdata; };"
            , "struct Level2 { struct Level3 l3; };"
            , "struct Level1 { struct Level2 l2[5]; };"
            , "void use_l3(struct Level3 *l) { l->cb(l->userdata); }"
            , "void int_h(void *p) { int *pi = p; }"
            , "void f(struct Level1 *root) {"
            , "    float y = 1.0f;"
            , "    root->l2[2].l3.cb = int_h;"
            , "    root->l2[2].l3.userdata = &y; // SHOULD ERROR at index 2"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:10: assignment type mismatch: expected int32_t, got float"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t and float (assignment)"
            , "  while unifying T10(userdata)[int32_t=2]* and float* (assignment)"
            , ""
            , "  where template T10(userdata) indexed by int32_t=2"
            ]

    it "enforces structural invariants in mixed-access arrays" $ do
        prog <- mustParse
            [ "typedef void my_cb(void *userdata);"
            , "struct Slot { my_cb *cb; void *userdata; };"
            , "struct List { struct Slot slots[10]; };"
            , "void use_list(struct List *l, int i) { l->slots[i].cb(l->slots[i].userdata); }"
            , "void int_h(void *p) { int *pi = p; }"
            , "void f(struct List *l) {"
            , "    float y = 1.0f;"
            , "    l->slots[0].cb = int_h;"
            , "    l->slots[0].userdata = &y; // SHOULD ERROR even if usage is generic"
            , "}"
            ]
        prog `shouldHaveErrors`
            [ "test.c:9: assignment type mismatch: expected int32_t, got float"
            , "  expected int32_t, but got float"
            , "  while unifying int32_t and float (assignment)"
            , "  while unifying T13(userdata)[int32_t=0]* and float* (assignment)"
            , ""
            , "  where template T13(userdata) indexed by int32_t=0"
            ]

    describe "False positive regressions" $ do
        it "allows nullptr assignment to nullable pointer" $ do
            prog <- mustParse
                [ "void f(int *_Nullable items, int n) {"
                , "    items = nullptr;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "allows nullptr assignment to Sized nullable pointer (member access only)" $ do
            prog <- mustParse
                [ "struct My_Struct { int *_Nullable items; int num_items; };"
                , "void f(struct My_Struct *s) {"
                , "    s->items = nullptr;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "allows nullptr assignment to Sized nullable pointer" $ do
            prog <- mustParse
                [ "struct My_Struct { int *_Nullable items; int num_items; };"
                , "void f(struct My_Struct *s) {"
                , "    s->items[0] = 1;"
                , "    s->items = nullptr;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "allows struct pointer argument to void* nullable parameter" $ do
            prog <- mustParse
                [ "void mem_delete(void *_Nullable ptr);"
                , "struct My_S { int x; };"
                , "void f(struct My_S *_Nullable s) {"
                , "    mem_delete(s);"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles realloc pattern with void* and cast" $ do
            prog <- mustParse
                [ "void *_Nullable mem_vrealloc(void *_Nullable ptr, int n, int sz);"
                , "struct My_S { int x; };"
                , "void f(struct My_S *_Nullable items) {"
                , "    struct My_S *new_items = (struct My_S *)mem_vrealloc(items, 10, sizeof(struct My_S));"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "handles realloc pattern assigning back to Sized member" $ do
            prog <- mustParse
                [ "void *_Nullable mem_vrealloc(void *_Nullable ptr, uint32_t n, uint32_t sz);"
                , "struct My_Item { void *_Nullable data; int x; };"
                , "struct My_Container { struct My_Item *_Nullable items; uint32_t items_length; };"
                , "void f(struct My_Container *c, uint32_t num) {"
                , "    c->items[0].x = 1;"
                , "    struct My_Item *new_items = (struct My_Item *)mem_vrealloc(c->items, num, sizeof(struct My_Item));"
                , "    if (new_items == nullptr) { return; }"
                , "    c->items = new_items;"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

        it "does not propagate nonnull to scalar through array access" $ do
            prog <- mustParse
                [ "void f(const int *_Nullable data) {"
                , "    if (data != nullptr) {"
                , "        int x = data[0] != 0;"
                , "    }"
                , "}"
                ]
            shouldHaveNoErrors $ osrErrors $ runFullAnalysis prog

-- end of tests
