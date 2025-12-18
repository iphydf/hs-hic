# Soundness and Multi-Pass Type Checking

This document describes the sound multi-pass architecture of the `cimple-hic`
type checker. The system is designed for **formal soundness**, specifically
addressing the challenges of `void*` templates and heterogeneous arrays in C.

## The Soundness Problem: Index Ambiguity

The type checker supports limited dependent types by indexing templates with
symbolic values (e.g., `Template T (Just 0)` vs `Template T (Just i)`).
Soundness is compromised when an array is accessed via both literal and variable
indices if they are treated as independent.

### Example of Unsoundness

```c
void set(Registry *r, int i, void *o) { r->h[i].o = o; } // Index 'i' (Variable)
void f(Registry *r) {
    set(r, 0, some_float_ptr);         // Binds T_idx_i to float
    r->h[0].handler = some_int_handler; // Binds T_idx_0 to int
}
```

If `T_idx_i` and `T_idx_0` are independent, the solver misses the conflict.

## The Soundness Problem: Flow-Insensitivity

The type checker must account for control-flow guards like null-checks to avoid
false positives. Without this, a `_Nullable` pointer checked for null and then
used safely is flagged as an error.

### Example

```c
void f(int *_Nullable p) {
    if (p == nullptr) return;
    *p = 1; // Safe, but requires flow sensitivity to know p is Nonnull here
}
```

## Sound Multi-Pass Architecture

To ensure soundness and avoid infinite fixpoint loops, the type checker uses a
sequential multi-pass pipeline.

### Phase 1: Global Structural Analysis

-   **Goal:** Build the global `TypeSystem` and identify generic "Hotspots".
-   **Hotspot Detection:** Flag any struct containing `void*` or any function
    signature using generic templates.
-   **Normalization:** Templates are normalized to consistent names (e.g., `P0`,
    `P1`) to allow comparison across different parts of the AST.

### Phase 2: Array Usage Analysis

-   **Goal:** Categorize every array into a "Flavor" based on its usage patterns
    across the entire codebase.
-   **Flavors:**
    1.  **Flavor A (Homogeneous):** Only variable indices are used.
    2.  **Flavor B (Heterogeneous):** Only literal indices are used. Elements
        can safely have different types.
    3.  **Flavor C (Mixed):** Both literal and variable indices are used.
-   **Soundness Rule (Promotion):** Any array identified as **Flavor C** is
    immediately promoted to **Flavor A**. All its elements are unified into a
    single "Universal" template.

### Phase 3: Call Graph Analysis

-   **Goal:** Determine the solving order and identify recursion.
-   **SCC Detection:** Groups functions into Strongly Connected Components
    (SCCs).
-   **Benefit:** Eliminates the need for a global fixpoint loop in the
    type-checking phases (1-6). Global fixpoints are deferred to the high-level
    inference phase (Phase 7).
-   **Direct Calls only:** Indirect calls (function pointers) are treated as
    interfaces based on their `typedef` signature.

### Phase 4: Nullability Analysis

-   **Goal:** Track flow-sensitive non-null facts to safely handle `_Nullable`
    pointers guarded by checks.
-   **Mechanism:** Forward data-flow analysis on the Control Flow Graph (CFG)
    using `__tokstyle_assume_*` markers.
-   **Result:** Produces a map of guaranteed non-null variables at each program
    point.

### Phase 5: Constraint Generation

-   **Goal:** Extract specialized constraints per function body.
-   **Lexical Scoping:** Proper support for block-scoped variables and
    shadowing.
-   **Promotion Implementation:** Implements the Phase 2 flavors. Mixed-access
    arrays generate `Template T Nothing` (Universal), while heterogeneous ones
    keep `Template T (Just idx)`.
-   **Nullability Integration:** Uses Phase 4 results to upgrade variable types
    to `_Nonnull` when guarded by checks.
-   **Diagnostic Visibility:** Unhandled AST nodes return an `Unsupported` type,
    ensuring gaps in the analyzer are visible as warnings rather than silent
    successes.

### Phase 6: Ordered Solver

-   **Goal:** Solve constraints bottom-up according to the Call Graph.
-   **Topological Order:** Leaf functions are solved first. Their refined
    signatures are then used by their callers.
-   **Minimal Fixpoints:** A fixpoint loop is only used within a single
    recursive SCC, eliminating the risk of a global infinite loop.
-   **Co-inductive Unification:** Employs graph-based unification with a "seen"
    set to safely handle recursive type definitions without falling into
    infinite loops or incorrectly rejecting valid C patterns (e.g.,
    self-referential allocators).
-   **Subsumption Rule:** Enforces `Template T (Just i) <: Template T Nothing`.
    This ensures that specific type information from literal indices propagates
    to general variable indices, closing the final soundness hole.

### Phase 7: High-Level Construct Inference

-   **Goal:** Lift low-level C constructs into high-level intent nodes.
-   **Mechanism:** Runs a global fixpoint loop over all inference features to
    support multi-stage lifting.
-   **Validation:** Uses verified types from Phase 6 to ensure safety.

## Recursive Types and Co-induction

Idiomatic C frequently employs recursive patterns that involve `void*`
templates, such as allocators that deallocate themselves (e.g., `Tox_Memory`).
Standard Hindley-Milner inference uses an **occurs check** to prevent infinite
type expansion, which would normally reject such patterns as "infinite types".

### Sound Co-inductive Unification

To support these patterns soundly and with guaranteed termination, the solver
employs **co-inductive unification** (also known as graph-based bisimulation).

1.  **Stateful Unification:** The solver maintains a "seen" set of type pairs
    `(Actual, Expected)` currently being unified.
2.  **Cycle Detection:** If the solver encounters a pair already in the "seen"
    set, it treats the unification as a success (assuming the recursive
    constraint is satisfied).
3.  **Guaranteed Termination:** Since the number of types and templates within
    any SCC is finite, the number of possible pairs is also finite. This ensures
    the solver **always terminates**, even when discovering complex
    equi-recursive types.

## Key Soundness Properties

1.  **Homogeneity Promotion:** Variable indices are never allowed to "bypass"
    type constraints established by literal indices in the same array.
2.  **Explicit Failure:** Missing type information (due to unhandled C
    constructs) is injected into the constraint graph as "Unsupported" tokens,
    preventing silent unsoundness.
3.  **Order-Aware Solving:** Information flows from callees to callers, ensuring
    that polymorphic usage is correctly constrained by the actual
    implementation's requirements.
4.  **Co-inductive Termination:** Self-referential type constraints are resolved
    through bisimulation rather than infinite expansion, providing a sound basis
    for recursive data flow.
