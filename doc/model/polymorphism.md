# Polymorphism and Topological Generalization

Hic implements a sound polymorphic type system for C designed for decidability.
It reconstructs generic intent from C's use of `void*` and callback patterns
while ensuring that unrelated usages do not "bleed" into each other.

## 1. The Core Principle: Scope Separation

To achieve sound polymorphism, Hic maintains a strict separation between the
**Declaration Scope (Scope A)** and the **Analysis Scope (Scope B)**.

-   **Scope A (Declarations):** Types live in the global `TypeSystem` with
    stable, universal parameter IDs (e.g., `P0`, `P1`). These represent "for all
    T, the type T*".
-   **Scope B (Analysis):** During the analysis of a specific function body, Hic
    uses fresh, existential solver variables (e.g., `T100`, `T101`). These
    represent an unknown type subject to inference.

## 2. The Type Lifecycle

Every type in Hic passes through a strictly bounded three-stage lifecycle:

### Stage 1: Instantiation (Call Site)

Whenever a generic function or `typedef` is used, it is **instantiated**.

-   **Algorithm:** A structural natural transformation (`hoistFix`) walks the
    type tree once.
-   **Transformation:** All universal parameters (`P`) are cloned into fresh
    solver variables (`T`) unique to that specific call site ID.
-   **Guarantee:** This ensures that call site A (using `int`) does not
    accidentally constrain call site B (using `float`).

### Stage 2: Solving (Topological SCC)

Hic solves type constraints in topological order according to the call graph.

-   **Algorithm:** A worklist-based graph solver propagates constraints through
    the local "World B" variables.
-   **Termination:** Because the type lattice and structural depth are finite
    (constrained by the AST), the solver is guaranteed to reach a stable least
    fixed point. Hic uses co-inductive unification to handle equi-recursive
    cycles (e.g., `struct Node { void* next; }`).

### Stage 3: Generalization (SCC Exit)

Once an entire SCC (Strongly Connected Component) of the call graph is solved,
its signatures are **generalized**.

-   **Algorithm:** A structural catamorphism (`foldFix`) identifies solver
    variables that are not constrained by the global environment.
-   **Transformation:** These variables are promoted to a canonical sequence of
    stable universal parameters (`P0`, `P1`, ...).
-   **Result:** The function now has a stable, polymorphic signature ready to be
    used (and re-instantiated) by the next level of the call graph.

## 3. Decidability

Unlike "fuel-based" solvers or arbitrary fixed-point loops, this architecture is
guaranteed to terminate:

1.  **Strictly Bounded Traversal:** Both Instantiation and Generalization are
    single-pass recursion schemes (`foldFix`/`hoistFix`). They move
    monotonically through the data structure and cannot loop.
2.  **Topological Solving:** Hic only generalizes a function when it is
    mathematically certain that every possible constraint on its types has been
    processed.
3.  **No Backtracking:** The solver always moves towards more specific types on
    a finite lattice.

## 4. Special C Semantics (The Decay Rule)

Hic integrates standard C "decay" rules directly into the polymorphic engine:

-   **Implicit Nonnull:** Functions and Arrays are implicitly treated as
    satisfying `_Nonnull` pointer requirements.
-   **Unique Anonymity:** Anonymous generic types (derived from raw `void*`)
    incorporate their source code position (`AlexPosn`) into their identity to
    prevent accidental collision between unrelated `void*` parameters in the
    same translation unit.

--------------------------------------------------------------------------------

## 5. Poly-variance and Call-Site Refinement

To support complex patterns like generic memory allocators (`tox_memory`)
without causing type "bleeding" across the project, Hic implements **Rank-1
Poly-variance** for all lifted `void *` parameters.

### A. The Call-Site Refresh Rule

Whenever a function containing syntactic `void *` (semantic $T$) is called, the
solver does not unify the arguments with a global $T$. Instead, it creates
**Fresh Local Type Variables** for that specific call site.

-   **Example**: An allocator `void *malloc(size_t)` is inferred as `template<T>
    T* malloc(size_t)`.
-   **Effect**: If Call Site A casts the result to `int*` and Call Site B casts
    it to `char*`, the two calls remain isolated. $T_A$ and $T_B$ are distinct
    variables, preventing a project-wide conflict between `int` and `char`.

### B. Refined Return Type

Functions returning `void *` are treated as returning a **Universal Supertype**.

-   The specific refinement of the return value is deferred to the caller.
-   A cast in C (`(Tox_Memory *)tox_memory_alloc(...)`) is treated by the solver
    as a **Refinement Event** for that specific pointer instance, rather than a
    global constraint on the function's definition.

### C. Lexical Instance Isolation

For callbacks stored in structs (e.g., `self` pointers), Hic uses the
**Unpacking Rule** (Section 6.B).

-   A `void *self` field in a struct is lifted to a template parameter $S$.
-   When the struct is accessed, $S$ is bound to a **Pointer-Instance-Specific
    Skolem ID**.
-   This ensures that consistency is maintained *within* a single allocator
    instance, while allowing different instances (e.g., a system heap vs. a pool
    allocator) to handle different underlying types.

### D. Global Struct Integrity

Template parameters within a struct are unified globally at the type-definition
level.

-   **Invariant Persistence**: A semantic link (e.g., `cb` argument type
    matching `userdata` type) is an inherent property of the `Nominal` type node
    in the global `TypeGraph`.
-   **Inter-procedural Safety**: Passing a struct through multiple function
    layers does not "refresh" its internal variables independently. The solver
    ensures that the internal consistency captured at the definition site is
    enforced at every point of usage, regardless of call depth.
