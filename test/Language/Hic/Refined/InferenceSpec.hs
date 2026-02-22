{-# LANGUAGE FlexibleContexts  #-}
{-# LANGUAGE OverloadedStrings #-}
module Language.Hic.Refined.InferenceSpec (spec) where

import           Data.Text                                       (Text)
import qualified Data.Text                                       as T
import           GHC.Stack                                       (HasCallStack)
import qualified Language.Hic.Core.Errors                        as E
import           Language.Hic.Inference.EngineSpec               (mustParse)
import           Language.Hic.Inference.Program                  (fromCimple)
import           Language.Hic.Refined.Inference                  (inferRefined,
                                                                  rrErrors)
import qualified Language.Hic.TypeSystem.Core.Base               as TS
import           Language.Hic.TypeSystem.Ordered.HotspotAnalysis (garTypeSystem,
                                                                  runGlobalStructuralAnalysis)
import           Test.Hspec

shouldHaveRefinedError :: HasCallStack => [Text] -> [Text] -> Expectation
shouldHaveRefinedError input expectedErrorTexts = do
    prog <- mustParse input
    let globalAnalysis = runGlobalStructuralAnalysis prog
    let hicProgram = fromCimple prog
    let refinedResult = inferRefined (garTypeSystem globalAnalysis) hicProgram
    let actualErrorTexts = map errorToText (rrErrors refinedResult)
    actualErrorTexts `shouldMatchList` expectedErrorTexts
  where
    errorToText ei = case E.errType ei of
        E.CustomError t -> t
        E.RefinedVariantMismatch -> "Refined type mismatch detected in fixpoint solver"
        E.RefinedNullabilityMismatch -> "Refined type mismatch detected in fixpoint solver"
        _ -> T.pack $ show (E.errType ei)

shouldHaveNoRefinedErrors :: HasCallStack => [Text] -> Expectation
shouldHaveNoRefinedErrors input = shouldHaveRefinedError input []

spec :: Spec
spec = do
    describe "Basic type checking" $ do
        it "allows incrementing integers" $ do
            shouldHaveNoRefinedErrors
                [ "void f() {"
                , "    int32_t i = 0;"
                , "    ++i;"
                , "}"
                ]

        it "allows decrementing integers" $ do
            shouldHaveNoRefinedErrors
                [ "void f() {"
                , "    int32_t i = 10;"
                , "    --i;"
                , "}"
                ]

        it "UNIQUE_ERROR: allows assigning 0 to uint64_t (Section 10.B/1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void f() {"
                , "    uint64_t i = 0;"
                , "}"
                ]

        it "allows basic arithmetic on integers" $ do
            shouldHaveNoRefinedErrors
                [ "void f() {"
                , "    int32_t a = 10;"
                , "    int32_t b = 20;"
                , "    int32_t c = a + b;"
                , "    int32_t d = a - b;"
                , "}"
                ]

        it "allows passing an array element to a function taking void*" $ do
            shouldHaveNoRefinedErrors
                [ "void my_free(void *p);"
                , "void test(int32_t **ary, int32_t n) {"
                , "    for (int32_t i = 0; i < n; ++i) {"
                , "        my_free(ary[i]);"
                , "    }"
                , "}"
                ]

        it "allows packing a boolean into a byte array (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void net_pack_bool(uint8_t *bytes, bool v) {"
                , "    bytes[0] = v ? 1 : 0;"
                , "}"
                ]

        it "reports error when assigning nullptr to a byte array (Section 2.A)" $ do
            shouldHaveRefinedError
                [ "void test(uint8_t *bytes) {"
                , "    bytes[0] = nullptr;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "allows returning a numeric literal from a function (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "size_t get_one() {"
                , "    return 1;"
                , "}"
                ]

        it "allows assigning matching pointer types (Section 1.A)" $ do
            shouldHaveNoRefinedErrors
                [ "void f() {"
                , "    int32_t i;"
                , "    int32_t *p;"
                , "    p = &i;"
                , "}"
                ]

        it "reports refined type mismatch for incompatible pointers (Section 1.A)" $ do
            shouldHaveRefinedError
                [ "void f() {"
                , "    int32_t i;"
                , "    float f;"
                , "    int32_t *pi = &i;"
                , "    float *pf = &f;"
                , "    pf = (float *)pi;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "reports error for nominal arity mismatch between structs (Section 2.B)" $ do
            shouldHaveRefinedError
                [ "struct Small { int32_t a; };"
                , "struct Large { int32_t a; int32_t b; };"
                , "void test(struct Small *s) {"
                , "    struct Large *l = (struct Large *)s;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "enforces nominal identity: same fields, different names (Section 1.A)" $ do
            -- Hic enforces strict nominal identity. Even if two structs have the same
            -- fields, they are incompatible if their names differ.
            shouldHaveRefinedError
                [ "struct Alpha { int32_t x; };"
                , "struct Beta { int32_t x; };"
                , "void test(struct Alpha *a) {"
                , "    struct Beta *b = (struct Beta *)a;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "forbids arity modification: treating a large struct as a smaller one (Section 2.B)" $ do
            -- This is the "Base/Derived" pattern often used in C but forbidden in Hic.
            shouldHaveRefinedError
                [ "struct Base { int32_t type; };"
                , "struct Derived { int32_t type; float value; };"
                , "void test(struct Derived *d) {"
                , "    struct Base *b = (struct Base *)d; // Error: arity mismatch"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Function calls" $ do
        it "reports error for function parameter mismatch (Section 1.A)" $ do
            shouldHaveRefinedError
                [ "void print_float(float *pf) { return; }"
                , "void test() {"
                , "    int32_t i;"
                , "    int32_t *pi = &i;"
                , "    print_float((float *)pi);"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "void* handling" $ do
        it "reports error when void* is used to smuggle wrong type (Section 1.B)" $ do
            shouldHaveRefinedError
                [ "void test() {"
                , "    int32_t i;"
                , "    void *p = &i;"
                , "    float *pf = p;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "supports recursive indirection of void* (Section 1.B)" $ do
            shouldHaveRefinedError
                [ "void test() {"
                , "    int32_t i;"
                , "    int32_t *pi = &i;"
                , "    void **pp = &pi;"
                , "    float **ppf = (float **)pp; // Error: T** cannot be unified with float**"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "supports isolated use of void* for different types in different calls (Call-Site Refresh - Section 5.A)" $ do
            shouldHaveNoRefinedErrors
                [ "void *malloc(size_t size);"
                , "void test() {"
                , "    int32_t *pi = (int32_t *)malloc(4);"
                , "    float *pf = (float *)malloc(4);"
                , "}"
                ]

        it "Issue 2: supports isolated use of void* for different types in different calls (Call-Site Refresh - Section 5.A)" $ do
            -- If void* uses a global T node, these two calls will conflict.
            shouldHaveNoRefinedErrors
                [ "void f(void *p);"
                , "void test() {"
                , "    int32_t i;"
                , "    float f_val;"
                , "    f(&i);"
                , "    f(&f_val);"
                , "}"
                ]

        it "Issue 3: allows assigning a symbolic size property to a concrete integer type (Section 10.B/decay)" $ do
            -- This verifies that VProperty (Algebraic Property) can decay to VBuiltin (Physical Integer).
            shouldHaveNoRefinedErrors
                [ "void test(void *p) {"
                , "    int32_t sz = sizeof(*p);"
                , "}"
                ]

    describe "Pointers and Qualifiers" $ do
        it "Issue 4: infers non-null for address-of operator (Section 1.B)" $ do
            -- &i is always non-null. It should be safe to pass to a non-null parameter.
            shouldHaveNoRefinedErrors
                [ "void take_nonnull(int32_t * _Nonnull p);"
                , "void test() {"
                , "    int32_t i;"
                , "    take_nonnull(&i);"
                , "}"
                ]

        it "allows casting away const from a mutable stack variable (Syntactic Refinement - Section 1.F)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            -- Hic allows this because the underlying memory (i) is actually mutable.
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    int32_t i = 10;"
                , "    const int32_t *p = &i;"
                , "    int32_t *q = (int32_t *)p;"
                , "    *q = 20;"
                , "}"
                ]

        it "allows passing a mutable pointer to a const parameter (Subtyping - Section 1.F)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "void f(const int32_t *p);"
                , "void test() {"
                , "    int32_t i;"
                , "    int32_t *p = &i;"
                , "    f(p);"
                , "}"
                ]

        it "reports error when attempting to refine a physically constant literal (Physical Stability - Section 12.C.5)" $ do
            -- pendingWith "implementation currently exempts literals from physical constancy check"
            -- Literals (like nullptr) are physically const and cannot be refined to mutable.
            shouldHaveRefinedError
                [ "void test() {"
                , "    int32_t *p = (int32_t *)nullptr;"
                , "    *p = 10;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Existential Inference and Structural Links" $ do
        it "Issue 5: enforces consistency between callback and userdata (Structural Link - Section 4.A)" $ do
            shouldHaveRefinedError
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback {"
                , "    callback_cb *cb;"
                , "    void *userdata;"
                , "};"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test() {"
                , "    float f = 1.0f;"
                , "    struct My_Callback m;"
                , "    m.cb = (callback_cb *)handle_int;"
                , "    m.userdata = &f;"
                , "    m.cb(m.userdata); // Trigger discovery"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "allows valid structural links (Section 4.A)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback {"
                , "    callback_cb *cb;"
                , "    void *userdata;"
                , "};"
                , "void handle_int(int32_t *pi) { *pi = 0; }"
                , "void test() {"
                , "    int32_t i = 10;"
                , "    struct My_Callback m;"
                , "    m.cb = (callback_cb *)handle_int;"
                , "    m.userdata = &i;"
                , "    m.cb(m.userdata);"
                , "}"
                ]

    describe "Pointer Arithmetic and Arrays" $ do
        it "supports pointer increment (degrades to pointer)" $ do
            shouldHaveNoRefinedErrors
                [ "void test(int32_t *p) {"
                , "    ++p;"
                , "}"
                ]

        it "supports pointer subtraction (returns ptrdiff_t)" $ do
            shouldHaveNoRefinedErrors
                [ "void test(int32_t *p1, int32_t *p2) {"
                , "    int64_t d = p1 - p2;"
                , "}"
                ]

    describe "Recursive Refresh" $ do
        it "supports isolated use of void* in struct fields for different instances (Section 5.C)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "struct Box { void *data; };"
                , "void test() {"
                , "    int32_t i;"
                , "    float f;"
                , "    struct Box b1;"
                , "    struct Box b2;"
                , "    b1.data = &i;"
                , "    b2.data = &f;"
                , "}"
                ]

        it "supports isolated use of void* in multiple fields of the same struct (Section 1.B)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            -- Section 1.B: Every void* is a FRESH template parameter.
            -- struct Duo is lifted to Duo<T1, T2>, allowing independent types.
            shouldHaveNoRefinedErrors
                [ "struct Duo { void *left; void *right; };"
                , "void test() {"
                , "    int32_t i;"
                , "    float f;"
                , "    struct Duo d;"
                , "    d.left = &i;"
                , "    d.right = &f;"
                , "}"
                ]

        it "reports error when sharing a polymorphic variable incorrectly within an instance (Section 5.D)" $ do
            -- In this case, both cb and userdata use the same T (syntactically void*).
            -- The solver should enforce consistency between them.
            shouldHaveRefinedError
                [ "typedef void callback_cb(void *userdata);"
                , "struct Entry { callback_cb *cb; void *userdata; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test() {"
                , "    float f;"
                , "    struct Entry e;"
                , "    e.cb = (callback_cb *)handle_int;"
                , "    e.userdata = &f;"
                , "    e.cb(e.userdata); // Trigger discovery"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Nested Structures and Substitution" $ do
        it "supports structural links through nested struct access (Section 6.B)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "struct Wrapper { struct My_Callback inner; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test() {"
                , "    int32_t i;"
                , "    struct Wrapper w;"
                , "    w.inner.cb = (callback_cb *)handle_int;"
                , "    w.inner.userdata = &i;"
                , "    w.inner.cb(w.inner.userdata);"
                , "}"
                ]

        it "supports structural links through pointer-to-struct access (Section 6.B)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test(struct My_Callback *p) {"
                , "    int32_t i;"
                , "    p->cb = (callback_cb *)handle_int;"
                , "    p->userdata = &i;"
                , "    p->cb(p->userdata);"
                , "}"
                ]

        it "reports error when structural link is broken through a pointer (Section 6.B)" $ do
            shouldHaveRefinedError
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test(struct My_Callback *p) {"
                , "    float f;"
                , "    p->cb = (callback_cb *)handle_int;"
                , "    p->userdata = &f;"
                , "    p->cb(p->userdata); // Trigger discovery"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Polymorphic Returns and Chains" $ do
        it "supports returning a polymorphic struct instance (Section 6.B)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "struct Box { void *data; };"
                , "struct Box make_int_box(int32_t *pi) {"
                , "    struct Box b;"
                , "    b.data = pi;"
                , "    return b;"
                , "}"
                , "void test() {"
                , "    int32_t i;"
                , "    struct Box b = make_int_box(&i);"
                , "    int32_t *p = b.data;"
                , "}"
                ]

        it "reports error when return value violates instance consistency (Section 6.B)" $ do
            -- pendingWith "not working yet"
            shouldHaveRefinedError
                [ "struct Box { void *data; };"
                , "struct Box make_int_box(int32_t *pi) {"
                , "    struct Box b;"
                , "    b.data = pi;"
                , "    return b;"
                , "}"
                , "void test() {"
                , "    int32_t i;"
                , "    struct Box b = make_int_box(&i);"
                , "    float *p = b.data;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Tagged Unions" $ do
        it "prevents accessing wrong variant in match (Section 1.C)" $ do
            shouldHaveRefinedError
                [ "typedef enum Tag { TAG_I, TAG_F } Tag;"
                , "typedef union Data { int32_t i; float f; } Data;"
                , "typedef struct Container { Tag tag; Data d; } Container;"
                , "void test(Container *c) {"
                , "  switch (c->tag) {"
                , "    case TAG_I: {"
                , "      c->d.f = 1.0f; // Error: expected int in this branch"
                , "      break;"
                , "    }"
                , "  }"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "forbids post-initialization variant mutation (Section 2.C)" $ do
            pendingWith "tagged union mutation check not implemented"
            shouldHaveRefinedError
                [ "typedef enum Tag { TAG_I, TAG_F } Tag;"
                , "typedef union Data { int32_t i; float f; } Data;"
                , "typedef struct Container { Tag tag; Data d; } Container;"
                , "void test(Container *c) {"
                , "  c->tag = TAG_F; // Error: variants are immutable after construction"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Regression Tests for Architectural Flaws" $ do
        it "ensures function parameters are isolated across calls but respect internal constraints (Section 1.A & 5.A)" $ do
            -- pendingWith "fresh variable generation is currently causing incorrect structural links"
            -- Section 1.A: No Pointer Type Punning. Even though calls are isolated (5.A),
            -- the internal cast in f() fixes the parameter type to int32_t*.
            -- Passing a float* from the caller is a structural truth violation.
            shouldHaveRefinedError
                [ "void f(void *p) {"
                , "    int32_t *pi = (int32_t *)p;"
                , "}"
                , "void test() {"
                , "    float f_val = 1.0f;"
                , "    f(&f_val);"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "allows assigning 0 to int64_t (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    int64_t x = 0;"
                , "}"
                ]

        it "correctly isolates unrelated uses of global template names (Section 5.A)" $ do
            pendingWith "unrelated uses of global templates are not yet isolated"
            shouldHaveNoRefinedErrors
                [ "void f1(void *p1) {"
                , "    int32_t *pi = (int32_t *)p1;"
                , "}"
                , "void f2(void *p2) {"
                , "    float *pf = (float *)p2;"
                , "}"
                ]

        it "enforces size consistency in hardened polymorphic functions (Section 10.C)" $ do
            -- Mocking a hardened qsort-like signature
            shouldHaveRefinedError
                [ "void my_qsort(void *base, uint64_t nmemb, uint64_t size);"
                , "void test(int32_t *pi) {"
                , "    my_qsort(pi, 10, sizeof(float)); // Error: sizeof(float) != sizeof(int32_t)"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "Issue 1: forbids using integer 0 as a null pointer constant (Section 2.A)" $ do
            shouldHaveRefinedError
                [ "void test() {"
                , "    int32_t *pi = 0;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "supports isolated use of nullptr for different pointer types (Section 1.B)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    int32_t *pi = nullptr;"
                , "    float *pf = nullptr;"
                , "}"
                ]

        it "implements indirection collapse: reference to Bottom is Bottom (Section 12.C.2)" $ do
            shouldHaveRefinedError
                [ "void test() {"
                , "    int32_t **pp = &nullptr;"
                , "    int32_t *p = *pp; // Error: dereferencing a pointer to Bottom"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "handles infinite recursion in self-referential function pointers (Section 12.B)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "typedef void loop_cb(loop_cb *f);"
                , "void test(loop_cb *f) {"
                , "    return;"
                , "}"
                ]

        it "handles deep implicit polymorphism via deep lifting (Section 5.C)" $ do
            -- pendingWith "Refined type mismatch detected in fixpoint solver"
            shouldHaveNoRefinedErrors
                [ "struct Inner {"
                , "    void *p;"
                , "};"
                , "struct Outer {"
                , "    struct Inner inner;"
                , "};"
                , "void test() {"
                , "    int32_t i = 0;"
                , "    float f_val = 1.0f;"
                , "    struct Outer o1;"
                , "    struct Outer o2;"
                , "    o1.inner.p = &i;"
                , "    o2.inner.p = &f_val;"
                , "}"
                ]

        it "enforces member access refinements are persistent (Section 1.D)" $ do
            shouldHaveRefinedError
                [ "struct Inner { void *p; };"
                , "void test(struct Inner i) {"
                , "    int32_t *pi = (int32_t *)i.p;"
                , "    float *pf = (float *)i.p;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "freezes structural refinements after initialization scope (Section 1.D)" $ do
            pendingWith "initialization scope freezing not implemented"
            shouldHaveRefinedError
                [ "struct Box { void *data; };"
                , "void test() {"
                , "    struct Box b;"
                , "    { "
                , "        int32_t i = 0;"
                , "        b.data = &i;"
                , "    }"
                , "    // b.data escaped its initialization block. Its type is now frozen as int32_t*."
                , "    float *pf = (float *)b.data; // Error: frozen as int32_t*"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "implements the Escape Rule: contamination via external functions (Section 7.A)" $ do
            pendingWith "Escape Rule (contamination logic) not yet implemented"
            shouldHaveRefinedError
                [ "struct Inner { void *p; };"
                , "void external_escape(void *i);"
                , "void test() {"
                , "    int32_t val;"
                , "    struct Inner i;"
                , "    i.p = &val; // Refined to int*"
                , "    external_escape(&i); // ESCAPE: link contaminated"
                , "    float *pf = (float *)i.p; // Error: still int* due to Single Structural Truth"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Advanced Collections and Sizing" $ do
        it "promotes elements to existential types in heterogeneous arrays (Section 4.A)" $ do
            shouldHaveNoRefinedErrors
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void handle_float(float *pf) { return; }"
                , "void test() {"
                , "    int32_t i;"
                , "    float f;"
                , "    struct My_Callback cbs[2];"
                , "    cbs[0].cb = (callback_cb *)handle_int;"
                , "    cbs[0].userdata = &i;"
                , "    cbs[1].cb = (callback_cb *)handle_float;"
                , "    cbs[1].userdata = &f;"
                , "    // Each index should preserve its own structural link"
                , "    cbs[0].cb(cbs[0].userdata);"
                , "    cbs[1].cb(cbs[1].userdata);"
                , "}"
                ]

        it "reports error when an array element violates its internal structural link (Section 4.A)" $ do
            shouldHaveRefinedError
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test() {"
                , "    float f = 1.0f;"
                , "    struct My_Callback cbs[1];"
                , "    cbs[0].cb = (callback_cb *)handle_int;"
                , "    cbs[0].userdata = &f;"
                , "    cbs[0].cb(cbs[0].userdata); // Trigger discovery"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "supports structural links through nested existentials (Section 6.B)" $ do
            shouldHaveNoRefinedErrors
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "struct Outer { struct My_Callback inner; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void test(struct Outer *o, int32_t *pi) {"
                , "    o->inner.cb = (callback_cb *)handle_int;"
                , "    o->inner.userdata = pi;"
                , "    o->inner.cb(o->inner.userdata);"
                , "}"
                ]

        it "reports error when passing userdata from one existential index to a callback from another (Section 12.B)" $ do
            shouldHaveRefinedError
                [ "typedef void callback_cb(void *userdata);"
                , "struct My_Callback { callback_cb *cb; void *userdata; };"
                , "void handle_int(int32_t *pi) { return; }"
                , "void handle_float(float *pf) { return; }"
                , "void test() {"
                , "    int32_t i = 0;"
                , "    float f = 1.0f;"
                , "    struct My_Callback cbs[2];"
                , "    cbs[0].cb = (callback_cb *)handle_int;"
                , "    cbs[0].userdata = &i;"
                , "    cbs[1].cb = (callback_cb *)handle_float;"
                , "    cbs[1].userdata = &f;"
                , "    // ERROR: cbs[0].userdata (int*) passed to cbs[1].cb (float*)"
                , "    cbs[1].cb(cbs[0].userdata); "
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "verifies consistency of linear size expressions (Section 10.B)" $ do
            shouldHaveNoRefinedErrors
                [ "void *my_malloc(uint64_t size);"
                , "void test() {"
                , "    int32_t *p = (int32_t *)my_malloc(2 * sizeof(int32_t));"
                , "}"
                ]

        it "treats 'int' as 'int32_t' (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    int i;"
                , "    int32_t *p = &i;"
                , "}"
                ]

        it "treats 'unsigned int' as 'uint32_t' (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    unsigned int i;"
                , "    uint32_t *p = &i;"
                , "}"
                ]

        it "treats 'long' as 'int64_t' (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    long i;"
                , "    int64_t *p = &i;"
                , "}"
                ]

        it "treats 'unsigned long' as 'uint64_t' (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    unsigned long i;"
                , "    uint64_t *p = &i;"
                , "}"
                ]

    describe "Formal Safety and Invariants" $ do
        it "reports contradiction when non-null pointer is assigned nullptr (Section 12.C.1)" $ do
            shouldHaveRefinedError
                [ "void test() {"
                , "    int32_t * _Nonnull p = nullptr;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "forbids refining physically const globals to mutable (Section 12.C.5)" $ do
            shouldHaveRefinedError
                [ "const int32_t global_val = 10;"
                , "void test() {"
                , "    int32_t *p = (int32_t *)&global_val;"
                , "    *p = 20;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "forbids refining string literals to mutable (Section 12.C.5)" $ do
            shouldHaveRefinedError
                [ "void test() {"
                , "    char *s = (char *)\"hello\";"
                , "    *s = 'H';"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

        it "permits whitelisted external functions to preserve structural links (Section 7.C)" $ do
            pendingWith "whitelist not implemented yet"
            shouldHaveNoRefinedErrors
                [ "typedef int compare_cb(const void *a, const void *b);"
                , "struct Inner { void *p; };"
                , "extern void qsort(void *base, uint64_t nmemb, uint64_t size, compare_cb *compar);"
                , "void test(struct Inner *i) {"
                , "    int32_t val;"
                , "    i->p = &val;"
                , "    qsort(i, 1, sizeof(struct Inner), nullptr);"
                , "    int32_t *pi = (int32_t *)i->p;"
                , "}"
                ]

        it "allows size arithmetic with constants (Section 10.B)" $ do
            shouldHaveNoRefinedErrors
                [ "void test() {"
                , "    uint64_t sz = sizeof(int32_t) + 1;"
                , "}"
                ]

    describe "Numeric Coercion" $ do
        it "allows assigning between different integer types (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test(uint8_t a, uint64_t b) {"
                , "    size_t c = a;"
                , "    uint32_t d = b;"
                , "}"
                ]

        it "allows using enums as integers (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "enum Mode { START, STOP };"
                , "void test() {"
                , "    int32_t i = START;"
                , "    uint8_t j = STOP;"
                , "}"
                ]

        it "allows using bool in numeric contexts (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "void test(bool b) {"
                , "    int32_t i = b ? 1 : 0;"
                , "    uint8_t j = b;"
                , "}"
                ]

        it "allows assignments between typedef'd integers (Section 1.E)" $ do
            shouldHaveNoRefinedErrors
                [ "typedef uint32_t My_Int;"
                , "void test(My_Int a) {"
                , "    uint64_t b = a;"
                , "    My_Int c = 10;"
                , "}"
                ]

        it "still reports error for assigning pointer to integer (Section 2.A)" $ do
            shouldHaveRefinedError
                [ "void test(int32_t *p) {"
                , "    int32_t i = p;"
                , "}"
                ]
                ["Refined type mismatch detected in fixpoint solver"]

    describe "Cimple Node Coverage" $ do
        it "handles TyStruct in function bodies" $ do
            shouldHaveNoRefinedErrors
                [ "struct My_Struct { int32_t x; };"
                , "void test(void *p) {"
                , "    struct My_Struct *s = (struct My_Struct *)p;"
                , "}"
                ]

        it "handles TyUnion in function bodies" $ do
            shouldHaveNoRefinedErrors
                [ "union My_Union { int32_t x; float f; };"
                , "void test(void *p) {"
                , "    union My_Union *u = (union My_Union *)p;"
                , "}"
                ]

        it "handles TyUserDefined (typedef) in function bodies" $ do
            shouldHaveNoRefinedErrors
                [ "typedef int32_t My_Int;"
                , "void test(void *p) {"
                , "    My_Int *pi = (My_Int *)p;"
                , "}"
                ]

        it "handles global struct typedef" $ do
            shouldHaveNoRefinedErrors
                [ "struct My_Struct { int32_t x; };"
                , "typedef struct My_Struct My_Alias;"
                ]

        it "handles TyNonnull with TyStruct" $ do
            shouldHaveNoRefinedErrors
                [ "struct My_Struct { int32_t x; };"
                , "void test(struct My_Struct *p) {"
                , "    struct My_Struct * _Nonnull s = p;"
                , "}"
                ]

    describe "Reproduction Cases" $ do
        it "allows packing a boolean and returning 1 (net_pack_bool)" $ do
            shouldHaveNoRefinedErrors
                [ "size_t net_pack_bool(uint8_t *bytes, bool v) {"
                , "    bytes[0] = v ? 1 : 0;"
                , "    return 1;"
                , "}"
                ]

        it "allows returning sizeof(int32_t) as size_t" $ do
            shouldHaveNoRefinedErrors
                [ "size_t test() {"
                , "    return sizeof(int32_t);"
                , "}"
                ]
