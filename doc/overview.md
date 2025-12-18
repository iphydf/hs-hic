# Hic Design Principles

Hic is designed to provide a semantic bridge between low-level C code and
high-level language features (similar to Rust, Haskell, or C++). It treats C as
a "high-level assembly" and attempts to reconstruct the original programmer's
intent.

## 1. Reversibility

The most critical constraint of Hic is **strict reversibility**.
`lower(infer(source)) == source`.

-   Any high-level construct must contain enough metadata to reconstruct the
    original C AST exactly (ignoring source locations).
-   If a pattern is ambiguous and cannot be lowered back to the *exact* same
    original AST, Hic must either:
    1.  Produce a diagnostic error.
    2.  Fall back to a standard `CimpleNode` wrapper.

## 2. Global Semantic Inference

While C is traditionally processed file-by-file, Hic processes the entire
`C.Program` at once. This allows heuristics to:

-   Trace `typedef` chains.
-   Understand struct field layouts across headers.
-   Identify ownership transfer patterns based on function naming conventions
    and types.

## 3. Supported Intent Structures

Hic currently identifies or is planned to identify the following constructs:

### Control Flow & Safety

-   **`Scoped`**: Reconstructs scoped resource management. It identifies
    allocation/initialization followed by a mandatory label-based cleanup block
    (the `goto CLEANUP` pattern).
-   **`Raise`**: Identifies error propagation logic, such as setting an
    out-parameter error variable and returning a sentinel value (e.g., `-1`,
    `nullptr`, or `false`).

### Data & Iteration

-   **`ForEach`**: Lifts standard index-based `for` loops into functional-style
    iterations over collections.
-   **`Find` / `Index`**: Reconstructs search logic returning elements or
    indices.
-   **`Any` / `All`**: Lifts loops that verify predicates across collections.
-   **`IterationElement` / `IterationIndex`**: Semantic representation of
    collection access within a loop.

### Protocols & State

-   **`Transition`**: Within a `switch`-based state machine, identifies
    assignment to a state variable as a first-class state transition.
-   **`TaggedUnion`**: Reconstructs sum types from a struct containing an enum
    tag and a union of data variants.

### Patterns

-   **`Match`**: Reconstructs pattern matching over a `TaggedUnion`. It verifies
    that member access is safely guarded by the corresponding tag value and
    enforces strict control flow (mandatory `break` or `return` at the end of
    each branch).
-   **`TaggedUnionGet`**: Lifts ternary expressions that safely extract a union
    member into a type-safe getter.
-   **`TaggedUnionGetTag`**: Lifts simple getter functions that return the tag
    of a sum type.
-   **`TaggedUnionMemberAccess`**: Reconstructs high-level semantic access to a
    union member (rendered as `obj.member`), hiding the internal union field
    layout.
-   **`TaggedUnionConstruct`**: Represents the atomic initialization of a sum
    type. It is inferred from either C compound literals or coalesced from
    sequential assignments to the tag and a corresponding union member.
