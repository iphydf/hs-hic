# Roadmap: Enhanced Diagnostics for Refined Type Analysis

This document outlines the phased plan to transform "Refined check failed" into
actionable, high-fidelity error messages that guide developers directly to the
source of type violations.

## Goal: Actionable Error Messages

A high-fidelity diagnostic answers three questions:

1.  **Where** is the violation? (File, Line, Column + Code Snippet)
2.  **What** is the violation? (Refined type mismatch, nullability conflict,
    etc.)
3.  **Why** did it happen? (The chain of inference/logic that led the solver to
    this conclusion)

--------------------------------------------------------------------------------

## Phase 1: Location-Aware Constraints (Infrastructure)

*The solver currently operates on numeric IDs. We must thread source metadata
through the algebraic graph.*

-   [ ] **Extend `Constraint`**: Add `Maybe (Lexeme Text)` to the `CSubtype` and
    `CInherit` constructors in `Language.Hic.Refined.Solver`.
-   [ ] **Update Inference**: Modify the `collectRefinements` passes in
    `Inference.hs` to capture the `Lexeme` of the expression or statement
    triggering the constraint.
-   [ ] **Trace Conflict Origin**: When the Product Automaton hits `SConflict`,
    capture the `ProductState` and the specific constraint that triggered the
    transition to the terminal error state.

## Phase 2: Integration with Standard Diagnostics

*Reuse the project's existing error reporting UI to provide snippets and
carets.*

-   [ ] **Map to `ErrorInfo`**: Create a translator from `RefinedResult` errors
    to `Language.Hic.Core.Errors`.
-   [ ] **Snippet Extraction**: Ensure `hic-check` can correctly display the
    offending line of C code using the captured `Lexeme`.
-   [ ] **Refined Mismatch Variants**: Extend `TypeError` to include
    refined-specific mismatches (e.g., `RefinedVariantMismatch`,
    `RefinedNullabilityMismatch`).

## Phase 3: Conflict Backtracking

*Since errors often result from a chain of assignments across files, we must be
able to explain the "Chain of Logic".*

-   [ ] **Dependency Graph Traversal**: Utilize the `deps` and `revDeps` maps in
    the solver to walk back from a `SConflict`.
-   [ ] **Evidence Collection**: Identify the "Refinement Triggers" (Match
    statements, casts, pointer dereferences) that contributed to the poisoned
    state.
-   [ ] **Chain of Logic Formatting**: Present the evidence as a numbered list
    of events:
    1.  `p` was initialized as `NULL` at `file.c:10`.
    2.  `p` was passed to `foo` at `file.c:15`.
    3.  `p` was dereferenced in `foo` at `bar.c:20`, which requires `Nonnull`.

## Phase 4: Refined Type Pretty-Printing

*Enable the solver to talk about types in a way that makes sense to a C
programmer.*

-   [ ] **`ppRefinedType`**: Implement a pretty-printer for `RigidNodeF`.
    -   Convert `VNominal` back to C-style `struct Name`.
    -   Represent `VVariant` as "Refined Union (Variant X)".
    -   Represent `VExistential` using a readable notation like `∃T. struct
        Callback<T>`.
-   [ ] **Symbolic Property Resolution**: Translate `VProperty T PSize` back to
    `sizeof(T)` in error messages.

## Phase 5: Interactive/Verbose Mode

-   [ ] **`--explain` flag**: Add a flag to `hic-check` that outputs the full
    constraint graph and dependency trace for a specific error.
-   [ ] **GraphViz Export**: Allow exporting the "Conflict SCC" (the minimal set
    of related type nodes that caused a failure) as a `.dot` file for debugging
    complex project-wide leaks.
