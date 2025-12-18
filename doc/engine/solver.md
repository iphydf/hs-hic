# Constraint-Based Type Solving

This document describes the architecture of the Hic type checker, which uses a
decoupled constraint-based solver. This architecture is designed to ensure
soundness, support least upper bound (LUB) calculations (such as singleton
decay), and guarantee decidability.

## 1. Motivation

The current `OrderedSolver` relies on eager unification (via `Unification.hs`).
While efficient, this approach has several drawbacks:

-   **Order Dependency**: Unification results can differ depending on the order
    in which expressions are visited.
-   **Inflexible Widening**: It is difficult to "backtrack" or widen a type once
    it has been bound to a specific literal (e.g., `Singleton 2` cannot easily
    decay to `int` when `Singleton 3` is encountered later).
-   **Diagnostics**: Errors are reported at the moment of discovery, making it
    hard to present the "global picture" of why a type conflict occurred.

## 2. Architecture Overview

The system is split into three strictly decoupled stages, integrated into the
existing multi-pass pipeline.

### Stage A: Constraint Generation (Phase 5)

The generator performs a single, total traversal of the function body. It
collects facts and requirements without attempting to solve them.

**Output:** A list of `Constraint` objects:

-   `Equality(T1, T2)`: T1 and T2 must be the same type.
-   `Subtype(Actual, Expected)`: Actual must be assignable to Expected.
-   `LUB(T, [T1, T2, ...])`: T is the least upper bound of a set of types.

### Stage B: The Ordered Solver (Phase 6)

The solver processes constraints according to the Call Graph's topological
ordering. For each SCC (Strongly Connected Component):

1.  **Worklist Processing**: Constraints are added to a worklist.
2.  **Fixed-Point Iteration**: The solver iteratively refines template bindings
    on a finite type lattice.
3.  **Lattice Rules**: Defined in `TypeSystem.Lattice`, these rules govern how
    types merge (e.g., `Singleton S32 2 ∪ Singleton S32 3 = Builtin S32`).
4.  **Co-inductive Cycles**: Uses graph-based bisimulation to handle
    equi-recursive types without infinite expansion.

### Stage C: Substitution & Inflation (Phase 6.5)

Once an SCC is solved, the resulting template bindings are "applied" back to the
AST. This ensures that subsequent phases (like High-Level Inference) operate on
concrete types rather than solver variables.

## 3. The Type Lattice

To guarantee termination, the solver operates on a lattice of finite height.

Level        | Example                 | Widening Path
:----------- | :---------------------- | :---------------------------------
**Specific** | `Singleton S32 2`       | → `Builtin S32`
**General**  | `Builtin S32`           | → `Builtin S64` (in some contexts)
**Top**      | `Unsupported` / `void*` | (Terminal)

**Soundness Guarantee**: Every step in the solver must move "up" the lattice.
Since the lattice height is bounded by the complexity of the `TypeInfo`
structure and the finite set of C types, the solver must terminate.

--------------------------------------------------------------------------------

## 4. Deep Dive: Constraint Solver

The goal is to replace the current stateful, fuel-based unification engine with
a total functional solver that is provably terminating.

### A. Core Mathematical Constraints

To ensure the solver is robust and suitable for formal verification, it must
adhere to the following principles:

1.  **Totality**: Every function in the solver must be **total**. No `error`,
    `undefined`, or partial functions are allowed. Termination must be
    guaranteed for all possible inputs.
2.  **Decidability**: The solver must not be capable of general recursion. It
    must be implemented using:
    -   **Structural Recursion**: Folds over type trees (`foldFix`) and maps.
    -   **Reductive Recursion**: Recursion over strictly decreasing finite sets
        (e.g., variable elimination).
    -   **Product Construction**: Traversing the finite Cartesian product of
        graph nodes.
3.  **Monotonicity**: The solver operates on a lattice of finite height. Every
    transformation step (joining requirements) must move **strictly up** the
    lattice. To ensure stability and satisfy lattice laws (absorption,
    associativity), the solver uses an **Attributed Canonical Form**. This form
    eliminates all "wrapper" nodes (e.g., `Qualified`, `Sized`). Qualifiers and
    sizes are stored as bitfields/attributes on the structural constructor nodes
    themselves.
4.  **Equi-Recursive Integrity**: C types are equi-recursive ($T = \text{Pointer
    } T$). The solver must represent these cycles as finite graphs and use
    **Bisimulation** to determine semantic equality. Structs are handled
    **nominally** (by name + template arguments) to ensure the graph remains
    finite.

### B. Architectural Building Blocks

The solver is decomposed into four strictly decoupled, independently testable
modules:

1.  **`GraphAlgebra` (Mathematical Foundation)**:

    -   A generic, type-agnostic library for structural graph operations.
    -   **Universal Product**: An implementation of the Product Automaton using
        **Exhaustive Domain Traversal**. It maps the finite Cartesian product of
        input domains to the result, ensuring 100% totality and zero recursion.
    -   **Minimization**: An implementation of **Moore's Algorithm** (Partition
        Refinement) for structural bisimulation.

2.  **`AlgebraicSolver` (Generic Logic)**:

    -   A purely structural implementation of **Variable Elimination** (Kleene's
        Algorithm).
    -   **Algorithm**: Recursively eliminates one variable at a time, solving
        local LFPs.
    -   **Termination**: Strictly reductive on the size of the variable set.

3.  **`TypeGraph` (Representation)**:

    -   A formal representation of C types as **Directed Graphs of Rigid
        Nodes**.
    -   **Consolidated Nodes**: Every node in the graph is a `RigidNode {
        Constructor, Qualifiers, Size, Children }`. This eliminates the
        complexity of "peeling" wrappers during graph traversal and ensures
        commutativity by design.
    -   Uses absolute `NodeId`s to eliminate the complexity of relative indexing
        during substitution.
    -   Provides stable `fromTypeInfo` / `toTypeInfo` conversions that maintain
        semantic bisimilarity.

4.  **`Lattice` (Semantic Rules)**:

    -   Defines the partial order ($\le$) and the transition rules for the
        Product Automaton.
    -   **Record Merge**: The transition function is a non-recursive merge of
        two `RigidNode` records.
    -   **Safety-Enforcing Monotonicity**: Standard C pointers violate
        monotonicity (invariance). Hic restores monotonicity by enforcing a
        restricted safety model (Invariance by default, Shielded Covariance).

## 5. The Refinement Pipeline

The Refined type system operates in three distinct phases, bridging the gap
between raw C syntax and graph-based verification.

### Phase 1: Syntactic Pattern Recognition (Front-End)

Before the type solver begins, Hic performs an upfront syntactic transformation
(e.g., `TaggedUnion.hs`).

-   **Lifting**: It identifies C idioms (like a `switch` on a tag field) and
    "lifts" them into high-level AST nodes like **`Match`** or
    **`TaggedUnionMemberAccess`**.
-   **Enforcement**: It enforces the "No Raw Access" invariant by flagging
    direct union member access that isn't guarded by a tag check.
-   **Benefit**: This turns a complex data-flow problem (tracking tag values)
    into a simple lexical scope problem for the type checker.

### Phase 2: Refinement Injection (Inference)

The constraint generator treats the lifted AST nodes as **Refinement
Boundaries**.

-   When entering a `Match` case, the generator injects a refinement constraint
    for that specific pointer instance.
-   It identifies **Internal Semantic Links** by observing captured access
    patterns (e.g., passing a struct field to a function pointer from the same
    struct).

### Phase 3: Formal Verification (Solving)

The project-wide solver (using `GraphAlgebra` and `Refined.Transition`) attempts
to find a stable Least Fixed Point (LFP) in the type graph.

-   It verifies that all "Packed" existentials and "Refined" variants are
    internally consistent across all possible execution paths.
-   If a semantic link is broken (e.g., via an external library escape), the
    solver detects the mismatch and triggers a fallback or conflict.

--------------------------------------------------------------------------------

## 6. Performance and Complexity Control

To prevent a combinatorial explosion of the state space, the solver employs
several mitigation strategies.

### A. Evidence-Based Promotion

The solver does not blindly speculate on existentials. Refinement and
Existentialization are only triggered by a **Hard Conflict** during unification
or joining. In the Strict Hic model, the lack of `void *` means most pointers
have fixed identities, making this check very fast.

### B. Semantic Link Heuristics

"Semantic Links" are identified during the first pass. A link is flagged if two
fields are accessed via the same base pointer in a single expression (e.g.,
`P->cb(P->userdata)`). The solver only tracks local links, keeping the discovery
phase $O(N)$.

### C. Nominal Equality via Opaque Atoms

To maintain performance during graph minimization, a "Packed" existential is
treated as an **Opaque Atom**. External subtyping checks ignore the hidden
internal types, preventing the number of edges in the product automaton from
exploding.

### D. Scope Bounding of Skolem IDs

Fresh IDs generated during "Unpacking" are strictly scoped to the local
variables derived from that access. Once the solver moves beyond the captured
consistency scope, these IDs are collapsed, ensuring the number of active graph
nodes remains proportional to local complexity.

--------------------------------------------------------------------------------

## 7. Whole-Program Inference Strategy

Hic utilizes **Whole-Program Analysis** (processing the entire library AST at
once) to ensure that refinements are connected across translation units without
the need for inter-procedural annotations.

1.  **Global Constraint Collection**: Every initialization in TU-A and every
    usage in TU-B is added to a single, project-wide constraint graph.
2.  **Promotion Identification**: Every struct with polymorphic parameters is
    identified as a candidate for **Evidence-Based Promotion**.
3.  **Refinement Discovery**:
    -   **Semantic Links**: Discovered via captured access patterns (e.g.,
        `P->cb(P->userdata)`), regardless of where the pointer was initialized.
    -   **Heterogeneous Arrays**: Discovered via constant-index initialization
        across any number of files.
4.  **Simultaneous Verification**: The solver attempts to find a stable LFP
    (Least Fixed Point) in the global graph. If no stable existential
    representation can be found that satisfies the union of all project-wide
    constraints, it collapses to `Conflict`.

--------------------------------------------------------------------------------

## Appendix: GADT Implementation Reference

The system is located in `src/Language/Hic/Refined/`. It uses a
layered attribute model to make invalid types (like arrays of functions)
unrepresentable.

The core `RigidNodeF` structure is defined as a kind-indexed GADT to ensure
architectural invariants are enforced at compile-time.

For the full implementation details, please refer to:
`src/Language/Hic/Refined/Types.hs`
