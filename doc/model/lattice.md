# Type System Transition Logic (Lattice Model)

This document defines the mathematical model and implementation rules for the
`Transition` module. This module serves as the single source of truth for the
Hic type system lattice operations (Join and Meet).

## 1. Goal: Separation of Logic and Traversal

The type system must support two distinct execution models while guaranteeing
identical results:

1.  **Symbolic (Fold-based)**: High-performance recursion over type trees.
2.  **Rigorous (Product-based)**: Guaranteed termination for equi-recursive
    types (graphs).

To achieve this, the **Lattice Rules** are decoupled from the **Walking
Strategy**. The `Transition` module defines the rules as a pure state machine:
`stepTransition :: (ProductState, RigidNodeL, RigidNodeR) ->
RigidNodeF(NextProductStates)`

## 2. Lattice State Model (Rigid Nodes)

To ensure the solver is decidable and provably terminating, we represent types
in an **Attributed Canonical Form**. The data structure itself enforces Hic's
safety invariants, ensuring that illegal states are unrepresentable by design.

### A. The Lattice State Sum Type

```haskell
data RigidNodeF tid a
    = Bottom           -- Absolute lattice Bottom (Identity for Join, Zero for Meet)
    | Top              -- Absolute lattice Top (Zero for Join, Identity for Meet)
    | Node (RigidStructure tid a) Quals

-- | Quals: Immutability property of the value.
data Quals = Quals { qConst :: Bool }

-- | Hic Nullability Lattice: Nonnull < Unspecified < Nullable
data Nullability = Nonnull | Unspecified | Nullable

-- | Hic Ownership: Only applies to references (Pointers/Arrays).
data Ownership = Owned | Unowned

data RigidStructure tid a
    -- Object Types (Values)
    | Builtin   ObjectBuiltin
    | Singleton ObjectBuiltin Integer          -- Literal refinement (e.g. '0')
    | Struct    (Lexeme tid) [a]               -- Generic Struct
    | Union     (Lexeme tid) [a]               -- Generic Union
    | Enum      (Lexeme tid)                   -- Enums are strictly non-generic
    | Pointer   Nullability Ownership (RigidRef tid a)
    | Array     Nullability Ownership a        -- Elements must be Object types
    | Var       tid (Maybe (Index tid))        -- Polymorphic variable with index

data RigidRef tid a
    | RefObject a                              -- Points to an Object Type
    | RefVoid   Quals                          -- Points to 'void' (with Quals)
    | RefFunc   { rfArgs :: [a], rfRet :: RigidRet tid a, rfVariadic :: Bool }

data RigidRet tid a
    = RetObject a                              -- Returns an Object
    | RetVoid                                  -- Returns 'void'

-- | Index: Represents a symbolic pointer into an array.
data Index tid
    = Literal  Integer          -- e.g., cbs[0] (Flavor B)
    | Variable tid              -- e.g., cbs[i] (Flavor A)
```

### B. Structural Totality (Correct by Construction)

This structure ensures that the type system enforces its own invariants at the
data level:

1.  **No Naked Functions/Void**: Functions and `void` are represented as special
    "Descriptors" (`RigidRef`, `RigidRet`). It is impossible to declare a
    variable, array element, or struct field of type `void` or `function`.
2.  **Ownership/Nullability Safety**: Ownership and Nullability are strictly
    tied to `Pointer` and `Array`.
3.  **Identity Stability**: Polymorphic variables (`Var`) are tied to simple
    symbolic names. Any complex expression (e.g., `i+1`, `i*2`) is treated as
    "Unknown" (`Nothing`), triggering the **Promotion Rule** to maintain
    soundness.

### C. The Recursive Collapse Rule (Identity Uniqueness)

To maintain the uniqueness of absolute lattice terminals, the solver applies the
following collapse rules during smart construction (`packNode`):

1.  **Conflict Propagation**: A structural node whose mandatory children have
    reached `Top` (Conflict) collapses to the absolute `Top`.
2.  **Structural Terminals**: `Pointer Nullable Unowned (RefObject Bottom)`
    represents the `NullPtr` type. It does **not** collapse to absolute
    `Bottom`.
3.  **Identity Identity**: Only the absolute `Bottom` (Unconstrained) acts as
    the identity for all `Join` operations across different constructor
    families.

## 3. Transition Rules

### A. Instance-Based Consistency (Path-Dependent Safety)

Hic enforces safety through **Conservative Rejection** of cross-instance usage.

-   **The Rule:** Fields of a generic struct (like `cb` and `userdata`) are only
    compatible if accessed through the **exact same pointer instance** in the
    code.
-   **The Result:** Even if two pointers `p1` and `p2` both resolve to the same
    index (e.g., `i+1`), the call `p1->cb(p2->userdata)` is **rejected**.
-   **Soundness:** This eliminates the need for complex symbolic math (Offsets).
    Safety is guaranteed because the solver doesn't have to "guess" if two
    expressions are the same; it only trusts a single stable reference.

### B. Index Promotion (Var Merge)

When joining two `Var tid (Maybe (Index tid))`:

-   `(T[0], T[0]) -> T[0]` (Identity)
-   `(T[0], T[i]) -> T` (Promotion to Flavor A / Universal)
-   `(T, T[0]) -> T` (Subsumption)

### C. Synthesis (Join Only)

If `psPolarity == PJoin` and we encounter mismatched pointers in an invariant
context, we synthesize a `const` qualifier for the resulting pointer. This
"shields" the target level, allowing the `Join` to remain a `Pointer`
(covariant) instead of collapsing to `Top`.

## 4. Formal Properties (Axioms)

The `stepTransition` function must satisfy:

1.  **Symmetry**: `step(Pol, qL, qR, A, B) == swap(step(Pol, qR, qL, B, A))`
2.  **Idempotence**: `step(Pol, q, q, A, A)` must return `A`.
3.  **Associativity**: `Join(A, Join(B, C)) == Join(Join(A, B), C)`.
4.  **Attribute Monotonicity**:
    -   **Quals, Nullability, Ownership**:
        -   `Join`: LUB of nullability ($Nonnull < Unspecified < Nullable$),
            `Set.union` for boolean `Quals` (const), and `Set.intersection` for
            `Ownership` (Unowned wins).
        -   `Meet`: GLB of nullability, `Set.intersection` for `Quals`, and
            `Set.union` for `Ownership` (Owned wins).

--------------------------------------------------------------------------------

## 5. Numeric Coercion and Symbolic Decay

In the **Strict Hic** model, we treat memory-related integer values
(specifically results from `sizeof`, `alignof`, and `offsetof`) as **Symbolic
Properties** (`VProperty`). These properties are nominally linked to a specific
type `T`.

Standard C, treats these values as generic integers. This creates a tension:

1.  **Strictness**: We want to ensure that `malloc(size)` uses a `size` that
    actually matches the type of the pointer being assigned.
2.  **Flexibility**: We want to allow `return 1;` from a `size_t` function, or
    assigning `sizeof(int)` to a `uint64_t` variable, without generating type
    errors.

### A. The "Bleeding" Conflict

Because built-in types (like `uint64_t`) are modeled as global nodes in the type
graph, any refinement applied to them at one call-site (e.g., "this `uint64_t`
parameter must be `sizeof(int)`") propagates project-wide. If another call-site
tries to use `sizeof(float)`, a conflict occurs on the shared global node.

### B. Proposed Model: Information Erasure at Boundaries

To resolve this, Hic implements **Directional Coercion** (or "Decay") at
refinement boundaries (assignments, function returns, and parameter passing).

#### 1. Symbolic vs. Physical Types

*   **Symbolic Properties ($P_T$)**: Algebraic atoms like `VProperty T PSize`.
    They carry a proof of nominal identity.
*   **Physical Integers ($I$)**: Built-in bit-sized types like `U32Ty`, `U64Ty`,
    `SizeTy`. They carry only magnitude.

#### 2. The Decay Rule (Implicit Cast)

When a Symbolic Property $P_T$ meets a Physical Integer requirement $I$ (or vice
versa), the system performs **Information Erasure**:

1.  **Meet ($P_T \sqcap I$)**: If the context allows decay, the symbolic
    information is discarded. The result is the **Physical Integer** ($I$).
    *   *Rationale*: Storing a "Size of T" into a generic `uint64_t` variable is
        safe, but the variable "forgets" it was a size. It becomes just a
        number.
2.  **Join ($P_T \sqcup I$)**: The result is always the **Physical Integer**
    ($I$).
    *   *Rationale*: If a path can be either a specific size or a generic
        number, we must assume it is a generic number to remain sound.

### C. Implementation Strategy: Solver-Level Erasure

Rather than inserting physical `Cast` nodes into the AST, the solver's
transition function (`Transition.hs`) is updated to handle these matches:

```haskell
-- In stepObject:
(VProperty a pk, VBuiltin bt) ->
    case pol of
        PJoin -> return $ VBuiltin bt      -- Decay to number
        PMeet -> return $ VBuiltin bt      -- Erase symbolic info
```

By returning `VBuiltin` during a `PMeet`, the solver effectively "swallows" the
symbolic evidence when it crosses into a non-symbolic variable. This allows the
code to pass while preventing the "symbolic identity" from polluting the global
built-in node.

--------------------------------------------------------------------------------

## 6. Symbolic Properties and Linear Size Expressions

To support standard C patterns like `malloc` and `qsort`, Hic incorporates a
restricted form of symbolic reasoning for memory-related integer values.

### A. Algebraic Properties

Hic represents metadata properties of types (like `sizeof`, `alignof`, and
`offsetof`) as algebraic atoms rather than physical numbers.

-   **`VProperty T PSize`**: Represents the value `sizeof(T)`.
-   **Identity**: `VProperty T PSize` is equal to `VProperty S PSize` if and
    only if $T$ and $S$ are the same nominal type.
-   **Abstraction**: The solver never needs to know the physical value (e.g., 4
    or 8); it only tracks symbolic identity.

### B. Pure Linear Size Expressions

Since C code often involves allocating collections of objects (e.g., `malloc(n *
sizeof(T))` or `calloc(n, size)`), Hic uses **Pure Linear Size Expressions** to
represent refined integer types.

-   **Form**: $\sum c_i P_i$, where $P_i$ are properties (e.g., `sizeof(T)`).
-   **Strict Matching**: This model is strictly for **Homogeneous or
    Heterogeneous Collections**. The only permitted size arithmetic is the
    multiplication of a type property by an instance count.
-   **No Extra Memory**: Allocating "extra" bytes for manual padding, metadata
    headers, or trailing buffers (e.g., `sizeof(T) + 16`) is strictly forbidden.
    Memory must exactly match the nominal identity of the types it contains.
    *Note: This restriction prioritizes sound verification over supporting
    intrusive metadata patterns, positioning Hic as a formal subset of C.*
-   **Unification**: The solver performs symbolic simplification to unify
    expressions. For example, `sizeof(T) + sizeof(T)` is automatically
    canonicalized to `2 * sizeof(T)`.
-   **Mismatch Detection**: If the code passes `sizeof(char)` where
    `sizeof(int)` is expected, the solver sees $PSize(i8) \neq PSize(i32)$ and
    triggers a `Conflict`.

--------------------------------------------------------------------------------

## 7. Formal Calculus and Transition Rules

This section provides the mathematical grounding for the lattice operations.

### A. Lattice Algebra (Existentials)

To ensure termination and stability, we define the following axioms for
Existentials ($\exists$):

1.  **Packing Rule (Introduction)**: A concrete type $A[T]$ is a subtype of its
    existential form:

    $$
    A[T] \le \exists S. A[S]
    $$

2.  **Existential Join**: Joining two existentials preserves the abstraction and
    the internal links by synchronizing binders:

    $$
    (\exists S. A[S]) \sqcup (\exists R. B[R]) = \exists Q. (A[S \to Q] \sqcup B[R \to Q])
    $$

    *Note: This ensures that if fields in A and B point to their respective
    variables, they will both point to Q in the result, preserving internal
    consistency.*

3.  **Existential Meet**: Meeting two existentials requires **Nominal Identity**
    of their templates:

    $$
    (\exists S. A[S]) \sqcap (\exists R. B[R]) = \exists Q. (A[S \to Q] \sqcap B[R \to Q])
    $$

    *Note: To maintain soundness, the solver first verifies that $A$ and $B$
    share the same nominal declaration. If the templates are not nominally
    identical, the meet collapses to **SConflict**, as Hic forbids casting
    between different nominal types even if they are structurally bisimilar.*

### B. Normalization and Contradiction Rules

To maintain the "Correct-by-Construction" property and fulfill the **Axiom of
Inescapability**, the transition function applies the following rules:

1.  **Nullability Contradiction (Witness Rule)**: Meeting a Nonnull requirement
    with a **Bottom state** (SBottom or NullPtrTy) is a safety violation. This
    applies to dereferences, function calls, and pointer-based member access.

    $$
    RReference(Ptr(TargetObject(SBottom)), Nonnull, \dots) \implies SConflict
    $$

    *Note: Contradictions collapse to SConflict so that they poison both Joins
    and Meets. If they collapsed to SBottom, the solver would unsoundly ignore
    the error branch.*

2.  **Indirection Collapse**: A reference to Bottom (unreachable) is itself
    Bottom.

    $$
    RReference(Arr(SBottom), \dots) \implies SBottom
    $$

3.  **Nominal Mismatch**: Nominal types (Structs) or Existentials with different
    nominal identities or parameter/binder counts collapse to **SConflict**.

    -   **Soundness**: This enforces strict nominal integrity. Hic forbids
        casting between different nominal templates to ensure that types remain
        stable and predictable.

4.  **Catch-All Mismatch**: Any attempt to meet two incompatible constructors
    (e.g. Object and Function) results in **SConflict**. Any attempt to join
    them results in **SAny**.

5.  **Canonicalization Rule**: Before entering the solver, all nodes must be
    canonicalized to ensure $O(V^2)$ state space:

    -   **Existentials**: All binder IDs are replaced with **De Bruijn
        Indices**.
    -   **Nominals**: Struct and Union member types are pre-resolved from the
        `Registry` into concrete Node IDs.

6.  **Qualifier Contradiction**: Physically `const` objects (literals, const
    globals) cannot be refined to `Mutable`.

    -   While pointer capabilities allow $Mutable \sqsubset Const$, the
        **Inherent Qualifiers** of an allocation are invariant. Any attempt to
        meet a physically `const` object with a `Mutable` requirement results in
        **SConflict**.

--------------------------------------------------------------------------------

## 8. Formal Calculus of the Safety Algebra

To ensure soundness and sound error propagation, the solver operates on a
**Safety Algebra** $(\mathcal{L}, \sqcap, \sqcup)$ rather than a standard
set-theoretic lattice. This section formally axiomatizes the behavior of the
terminal nodes and the safety ordering.

### A. The Domain and Terminals

Let $\mathcal{L}$ be the set of all type structures. We distinguish three
terminal elements:

-   **$\bot$ (SBottom)**: The uninhabited (unreachable) terminal.
-   **$\top_{any}$ (SAny)**: The universal supertype (top of the valid
    hierarchy).
-   **$\top_{conflict}$ (SConflict)**: The absorbing error state (broken
    invariant).

### B. The Safety Ordering ($\le_{safe}$)

The algebra is governed by a total safety ordering at the terminal boundaries:

$$
\bot < \text{Live} < \top_{any} < \top_{conflict}
$$

-   **The Witness Set ($\mathcal{W}$)**: A subset of Live nodes that require a
    non-bottom inhabitant for semantic validity. Specifically:

    $$
    \mathcal{W} = \{ RReference(p, Nonnull, \dots) \} \cup \{ RFunction(\dots) \}
    $$

-   **Monotonicity**: The solver's transition function $\text{step}$ is
    monotonic with respect to $\le_{safe}$. Any transition from a live node
    toward $\top_{conflict}$ is a non-decreasing step in the safety domain.

### C. Axioms of the Terminal Operations

The operations $\sqcup$ (Join) and $\sqcap$ (Meet) are defined by the following
axioms:

#### 1. Axiom of Inescapability (Conflict Poisoning)

The Conflict terminal is the **Universal Zero** for the entire algebra. Once a
violation is witnessed, it cannot be discarded:

$$
\forall X \in \mathcal{L}, \forall \sigma \in \{\sqcap, \sqcup\} : X \star_{\sigma} \top_{conflict} = \top_{conflict}
$$

#### 2. Axiom of Universal Supertype (SAny)

$\\top_{any}$ acts as the identity for refinement and the absorber for
generalization within the live domain:

-   **Meet (Identity)**: $\forall X \le \top_{any} : X \sqcap \top_{any} = X$.
-   **Join (Absorber)**: $\forall X \le \top_{any} : X \sqcup \top_{any} =
    \top_{any}$.

#### 3. Axiom of Unreachability (SBottom)

$\\bot$ acts as the identity for generalization and the zero for refinement:

-   **Join (Identity)**: $\forall X \in \mathcal{L} \setminus
    \{\top_{conflict}\} : X \sqcup \bot = X$.
-   **Meet (Zero)**: $\forall X \in \text{Live} \setminus \mathcal{W} : X \sqcap
    \bot = \bot$.

#### 4. Axiom of Witness (Safety Enforcement)

Meeting a **Witness Requirement** with an **Uninhabited State** ($\\bot$) is a
proof of contradiction:

$$
\forall W \in \mathcal{W} : W \sqcap \bot = \top_{conflict}
$$

*Note: This is the core mechanism that enables sound null safety. Dereferencing
or calling an unreachable subject transforms unreachability into a conflict.*
