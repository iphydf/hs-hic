# Hic Safety Model

Hic is not just a C analyzer; it is a safer variant of C that enforces a more
formal type system inspired by Rust. To maintain mathematical soundness
(monotonicity) in its type lattice and provide formal safety, Hic imposes the
following restrictions.

## 1. The Core Safety Restrictions

### A. Mandatory Immutability for Covariance

C's raw pointers are invariant by default, which breaks lattice monotonicity.
Hic resolves this by mandating that **subtyping is only allowed for immutable
data**.

-   `T*` is strictly invariant. `T*` is a subtype of `S*` only if `T == S`.
-   `const T*` is covariant. `const T*` is a subtype of `const S*` if `T <: S`.
-   **LUB Discovery**: Joining two different types `T*` and `S*` results in
    `const LUB(T, S)*`. This synthesis of `const` shields the targets, allowing
    a sound covariant join.

### B. Strict Separation of Pointers and Arrays

To eliminate the ambiguity of C's pointer-array decay, Hic treats them as
distinct constructors in the lattice.

-   **Raw Pointers (`T*`)**: Represent a reference to exactly one element. No
    indexing is allowed.
-   **Arrays/Slices (`T[]`)**: Represent a collection of elements.
-   The solver forbids structural cross-joins between them in invariant
    contexts, preventing the "fake array" hacks common in C analysis.

### C. Explicit Ownership & Move Semantics

Hic uses the `_Owned` qualifier to implement a linear type system.

-   An `_Owned` pointer cannot be aliased.
-   Assignment of an `_Owned` pointer results in a **Move**, rendering the
    source variable inaccessible.

### D. Non-Nullable by Default

Hic adopts the modern safety standard where all pointers are `_Nonnull` by
default.

-   Nullability must be explicitly opted into using the `_Nullable` qualifier.
-   This creates a strict, monotonic nullability lattice: `Nonnull < Unspecified
    < Nullable`.

--------------------------------------------------------------------------------

## 2. Core Language Invariants (Strict Hic)

To ensure maximum safety and solver efficiency, Hic enforces the following
invariants. The overarching philosophy is to move C's semantic model toward a
**Rust-like strictness**, prioritizing nominal safety and explicit semantic
links over physical layout-based assumptions.

### A. Nominal Identity (No Structural Punning)

Unlike standard C, a memory location in Hic has a **Single Nominal Truth**. Even
if two structs have identical fields and layout, they are treated as **distinct,
incompatible types** unless they share the same nominal declaration name.

-   **Goal**: This aligns Hic with the safety guarantees of languages like Rust
    or Java and provides performance optimizations for the solver by replacing
    recursive structural bisimulation with $O(1)$ nominal ID comparisons.
-   **Constraint**: Casting between unrelated nominal types (e.g., `(struct Beta
    *)alpha_ptr`) is a hard type violation, even if the structs are physically
    identical.

### B. Deprecation of Raw `void *`

The type-erasing `void *` is removed from the internal semantic model. In Hic,
`void *` is treated as a **Syntactic Alias** for a fresh template parameter `T`.

-   **Occurrence-Based Freshness**: Each syntactic occurrence of `void *` in a
    struct or function signature is lifted to a **Unique** template parameter
    (e.g., `T1`, `T2`). This ensures that independent pointers do not conflict
    unless a semantic link is discovered.
-   **User Writes**: `void *p, void *q`
-   **Hic Sees**: `T1 *p, T2 *q` (where T1 and T2 are independent polymorphic
    variables)
-   **Recursive Indirection**: This rule applies recursively to all pointer
    derivatives. `void **` is treated as `T **`, and `void ***` as `T ***`. The
    "Single Nominal Truth" must be maintained at every level of indirection.
-   **Null Pointers**: The keyword `nullptr` is modeled as a **Reference to the
    `NullPtrTy` Terminal** ($Reference(\perp_{obj})$). This terminal acts as the
    **Nominal Bottom** for the object hierarchy.
    -   **Subtyping Rule**: Since $\perp_{obj} \sqsubseteq T$ for all object
        types $T$, it follows that $Reference(\perp_{obj}) \sqsubseteq
        Reference(T)$ via standard covariance.
    -   **Verification**: Dereferencing a Reference to Bottom is a proof of
        contradiction (uninhabited type), triggering a safety violation and
        collapsing to the **SConflict** state.
-   **Hardened Built-ins**: Functions that operate on raw memory (e.g.,
    `memcpy`, `memcmp`) are hardened in the internal registry to use a **Single
    Template Parameter**:
    -   `memcpy<T>(T *dest, const T *src, size_t n)`
-   **Effect**: This ensures that every pointer has a stable nominal identity.
    Hardening built-ins prevents `memcpy` from being used as a "backdoor" for
    pointer type-punning, as the solver forces the destination and source to be
    nominally unified.

### C. Flat Nominal Scope (No Inner or Anonymous Types)

Hic forbids the use of inner or anonymous struct/union definitions. All types
must be defined at the global scope with an explicit nominal identifier.

-   **Anonymous Types**: Forbid `union { int i; float f; }`.
-   **Inner Types**: Forbid `struct Outer { struct Inner { int x; } in; };`.
-   **Reasoning**: This ensures that `Pure Nominal Identity` (1.A) is
    unambiguous across all translation units and eliminates the need for
    unstable name-mangling heuristics for anonymous members.

### D. Syntactic Union Refinement (No Raw Access)

Raw access to union members (e.g., `p->data.i`) is forbidden. Instead, Hic
performs a syntactic transformation up-front to ensure that union access only
occurs within a **Match** or **Switch** on its associated tag.

-   This grounds the refinement in the program's syntax, simplifying the type
    checker and eliminating the need for complex, probabilistic
    path-sensitivity.

### E. Global Type Persistence (No "Kill Rule")

Hic enforces **Identity-Based Stability**: types are stable and refined
identities (including the active variant of a union) are **immutable after
construction**.

-   **Strict Immutability**: Once a pointer instance escapes its initialization
    scope (e.g., after the constructor returns or the block ends), its tag and
    internal semantic refinement are frozen for its entire lifetime.
-   **No "Kill Rule"**: Because refinements are persistent, the solver does not
    need to invalidate facts after function calls. A refinement discovered for a
    pointer instance remains valid forever.
-   **Single Allocation Stability**: Refinements are tied to the unique identity
    of an allocation (stack entry or `malloc`).
-   **No Custom Allocators**: Hic forbids custom memory pools or allocators that
    reuse memory for different object types, ensuring that "Global Persistence"
    is mathematically sound.

### F. Explicitly Sized Integer Types

Hic does not support standard C integer types (`int`, `long`, `unsigned`, etc.)
in its internal semantic model. All integers are mapped to their bit-sized
versions assuming the **LP64 data model**:

-   `int` -> `i32` (S32Ty)
-   `unsigned int` -> `u32` (U32Ty)
-   `long` -> `i64` (S64Ty)
-   `unsigned long` -> `u64` (U64Ty)
-   `short` -> `i16` (S16Ty)

This ensures that type size and layout are unambiguous and platform-independent
within the solver.

### G. Qualifier Subtyping (Mutability)

Hic treats qualifiers (specifically `const`) as a restriction on capabilities.

-   **Lattice Rule**: `Mutable` is a subtype of `Const` ($Mutable \sqsubset
    Const$).
-   **Generalization (Join)**: `Join(Mutable, Const) = Const`. If a value can be
    either mutable or const, the solver assumes it is `Const` to remain safe.
-   **Refinement (Meet)**: `Meet(Mutable, Const) = Mutable`. If a value must
    satisfy both constraints, it must be the more restricted `Mutable` form
    (allowing both read and write).
-   **Function Parameters**: Passing a `T *` (Mutable) to a function expecting
    `const T *` (Const) is permitted, as it is a safe up-cast in the lattice.

--------------------------------------------------------------------------------

## 3. Forbidden C Constructs

To maintain soundness, the following common C patterns are strictly forbidden in
Hic:

### A. Type-Erasing Casts

-   Casting a pointer to an unrelated pointer type (e.g., `(int
    *)my_float_ptr`).
-   Casting pointers to integers and back (e.g., `(uintptr_t)p`).
-   Using `void *` for any purpose other than as a template parameter $T$.
-   Using the integer literal `0` as a null pointer constant. All null pointers
    must be explicitly written as `nullptr`.

### B. Nominal Arity Modification

-   Casting between "Base" and "Derived" struct patterns (e.g., treating a large
    struct as a smaller one by casting the pointer).
-   Accessing struct fields via offsets rather than their declared names.

### C. Post-Initialization Variant Mutation

-   Changing the tag of a `TaggedUnion` after its initial construction.
-   Overwriting the active member of a union with a different variant.
-   Once a union is refined, its variant identity is fixed for its lifetime.

### D. Raw Pointers as Arrays

-   Using pointer arithmetic (e.g., `p++`, `p + 5`) on a type declared as a raw
    pointer `T *`.
-   Indexing into a pointer that was not declared as an array `T[]`.
-   Hic strictly separates **References** (point to 1 element) from
    **Collections** (point to $N$ elements).

### E. Manual Memory Layout Assumptions

-   Assuming specific padding or alignment for struct fields.
-   Using `sizeof` for logic that depends on the physical byte-layout of types.
-   The solver treats types **Algebraically**, not physically.

### F. Custom Allocators and Memory Pools

-   Reusing a memory region for a different object type or variant without a
    formal deallocation/reallocation cycle.
-   Custom memory management that bypasses the standard stack/heap lifecycle is
    forbidden, as it breaks the identity-based stability of the solver.

### G. Volatile and Restrict Qualifiers

-   The `volatile` and `restrict` qualifiers are not supported in the Hic
    semantic model.
-   **Volatile**: Hic assumes that memory is stable and only modified by the
    code being analyzed (or safe external calls). Asynchronous modification of
    memory (MMIO, signal handlers) is outside the solver's formal model.
-   **Restrict**: Aliasing is handled through **Lexical Alias Tracking** and
    **Single Nominal Truth**. The `restrict` hint for optimization is ignored by
    the safety engine.

### H. Unsupported Pointer Difference Type (ptrdiff_t)

-   The `ptrdiff_t` type and the operation of pointer subtraction (e.g., `p1 -
    p2`) are not supported.
-   Because Hic treats **References** as points to individual objects rather
    than memory addresses, the concept of a numeric "distance" between pointers
    is semantically invalid.
-   Relative indexing is only permitted within an **Array** context via integer
    indices.

--------------------------------------------------------------------------------

## 4. Soundness and Path Persistence

In the Strict Hic model, soundness is maintained through nominal stability
rather than conservative invalidation.

### A. Immutable Variants

Refined tagged unions are **Immutable after Construction**. Once a union is
initialized as a specific variant (indicated by its tag), the tag and the active
member must not be mutated. This allows the solver to treat the refinement as a
global truth for that object instance.

### B. Captured Consistency (Skolem Variables)

When accessing an existential (like a callback in a heterogeneous array), the
solver "Unpacks" the hidden type as a **Skolem Variable** (a fresh, opaque ID).

-   **Instance Propagation**: This ID is not restricted to a single function
    scope. Hic uses **Symbolic Return Mapping** to track the flow of pointers
    through the call graph.
-   **Inter-procedural Stability**: If a function returns one of its parameters
    (`return p;`), the solver unifies the return value with the parameter's
    Instance ID. This ensures that the semantic link (e.g., `cb` vs `userdata`)
    persists even after the pointer is passed through multiple layers of
    non-inlined function calls.

--------------------------------------------------------------------------------

## 5. Modular Soundness and External Boundaries

When a struct "escapes" the analysis scope (e.g., it is passed to an unanalyzed
external library), the solver must assume a pessimistic state to maintain
modular soundness.

### A. The Escape Rule

If a struct `∃T. My_Callback<T>` is passed to an external function `extern void
foo(struct My_Callback *m)`, the solver assumes the external library could break
the semantic link. In the Strict Hic model, this is even more critical because
the external library might perform raw casts that are illegal in Hic. The
"trapped" property for that specific pointer instance is lost upon escape.

### B. Contamination Boundaries

Invalidation is limited to the **Pointer Instance** that escaped. Other
instances of the same struct type that remain within analyzed code preserve
their existential refinements. If a contaminated instance is used in a way that
requires refinement, the solver collapses it to its base template form (e.g.,
`My_Callback<T>`).

### C. Safe Externalities (Whitelisting)

Common C library functions that are known to preserve existential integrity
(e.g., `qsort`, `pthread_create`) are whitelisted. Passing a refined struct to
these functions does not trigger an "Escape" event.

--------------------------------------------------------------------------------

## 6. Motivating Examples

### A. Automatic Lifting of Heterogeneous Arrays

Hic infers complex existential types from standard C code by observing usage
patterns and semantic links.

**What the User Writes (Raw C):**

```c
struct My_Callback {
    void (*cb)(void *userdata);
    void *userdata;
};

struct Callbacks {
    struct My_Callback cbs[256];
};

cbs.cbs[0].cb = int_cb; // void (*)(int *)
cbs.cbs[0].userdata = &my_int;
```

**What Hic Infers (Semantic Model):**

1.  **Lifting**: `struct My_Callback<T1, T2> { void (*cb)(T1 *u); T2 *u; };`
2.  **Discovery**: Observing the call `m->cb(m->userdata)` creates a semantic
    link forcing $T1 = T2$.
3.  **Promotion**: `cbs :: Array<∃T. My_Callback<T>>`
4.  **Unpacking**: Indexing `cbs[id]` produces a unique Skolem variable $S$ such
    that `cb` is `void (*)(S *)` and `userdata` is $S *$.
5.  **Result**: The call `m->cb(m->userdata)` is provably safe because the
    internal `T` is synchronized across the instance.

### B. Tagged Unions and Syntactic Refinement

```c
struct Packet {
    int type;
    union {
        int i;
        char *s;
    } data;
};

// Syntactic transformation forces access to be guarded by tag
switch (p->type) {
    case PACKET_INT:
        print_int(p->data.i); // Safe: data.i is refined in this branch
        break;
    case PACKET_STR:
        print_str(p->data.s); // Safe: data.s is refined in this branch
        break;
}
```

--------------------------------------------------------------------------------

## 7. Safety & Diagnostics (Validation Model)

Hic uses a validation model for safety. During validation, the engine tracks
which field accesses are safe based on the surrounding control flow (e.g.,
inside a `Match` case for the specific variant).

-   Any direct field access to a `TaggedUnion` that has not been explicitly
    validated as safe is flagged with an "Unrecognized access" diagnostic.
-   To enforce consistency and safety, Hic identifies and coalesces sequential
    assignments to the tag and data fields into a single `TaggedUnionConstruct`
    construct. Raw field-by-field assignments that cannot be safely coalesced
    are discouraged and flagged as low-level violations.

When the inference engine detects a pattern that *almost* matches a high-level
construct but violates a safety condition (e.g., a potential resource leak in a
`Scoped` block), it should produce a diagnostic rather than a silent incorrect
lift.
