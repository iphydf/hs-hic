# Strict Hic: Making Sound, Whole-Program Static Analysis of C Tractable via Idiomatic Subsetting

## Abstract

Retrofitting memory safety onto legacy C involves a trade-off between the
computational cost of sound analysis and the human cost of manual annotation.
This paper introduces **Hic**, a system that resolves this tension by exploiting
the **structural idioms** of systems programming to enable sound, whole-program
type and ownership inference without annotations. We define **"Strict Hic,"** a
decidable subset of C where safety properties are encoded in the program's
control-flow and data-access patterns. By enforcing nominal identity, linear
ownership, and idiomatic tagged-union access, Hic renders inter-procedural
safety verification decidable and computationally tractable, while ensuring
**zero runtime overhead** and **strict C ABI compatibility**. We demonstrate
Hic's effectiveness on the Toxcore codebase, achieving near-linear analysis
performance and high precision by treating C idioms as implicit semantic
annotations. Our results suggest that for a significant class of systems
software, the information required for formal safety verification is already
present in the code’s idiomatic structure.

## 1. Introduction

C remains the standard language for systems infrastructure despite its
well-documented lack of memory safety. Efforts to secure C code have
traditionally followed four paths:

1.  **Sound Static Analysis:** Tools like Frama-C [1] or Astrée [2] offer rigor
    but often suffer from state-space explosion or excessive imprecision when
    analyzing complex aliasing in standard C.
2.  **Hybrid/Runtime Systems:** Earlier systems such as CCured [6] demonstrated
    that pointer safety could be inferred (SAFE/SEQ/WILD). However, these
    systems rely on **runtime instrumentation** and "fat pointers" to handle
    unsafe patterns, imposing significant performance overhead and breaking
    binary compatibility with uninstrumented libraries.
3.  **Heuristic Analysis:** Tools like Facebook Infer [3] employ techniques like
    bi-abduction on small scope windows. To maintain performance, they often
    drop constraints in complex scenarios, sacrificing soundness.
4.  **Dialect/Annotation Systems:** Projects like Checked C [4] or RefinedC [5]
    introduce safe types (`_Ptr<T>`) or logical contracts. However, the burden
    of manually annotating millions of lines of legacy code prevents widespread
    adoption.

We propose a fifth approach: **Idiomatic Subsetting**. Instead of analyzing the
full specification of ISO C, we define a strict subset, **"Strict Hic,"** which
aligns with the memory models of modern safe languages. By paying the cost of
reduced language flexibility, we gain the ability to run a total, provably
terminating, and sound type inference engine on unannotated code. Crucially,
this static-only approach ensures **zero runtime overhead** and maintains
**strict C ABI compatibility**, making it suitable for low-level systems
infrastructure where runtime instrumentation is unacceptable.

## 2. The Strict Hic Model: Axioms of Tractability

The core insight of Hic is that the ambiguity of C's type system is the primary
barrier to tractable analysis. Strict Hic converts undecidable problems into
linear-time constraints by enforcing the following axioms:

### 2.1. Nominal Stability

Standard C permits "structural punning", i.e. treating a struct as a different
type if the layout matches. Hic enforces **Nominal Identity**: a pointer to
`struct A` can never be cast to `struct B`, regardless of physical layout. This
reduces type equality checks from graph isomorphism problems to $O(1)$ nominal
comparisons.

### 2.2. Ownership Invariance

Hic enforces memory safety via a linear ownership model. It distinguishes
between **Owning** pointers (`_Owned T*`), which grant the right to deallocate,
and **Borrowed References** (`T*`), which are ephemeral views. To ensure
predictable deallocation without a garbage collector or reference counting, Hic
mandates that the **ownership graph must be a DAG**. While types may be
recursive (e.g., a node pointing to a child), any back-pointer (e.g., a `prev`
link in a list) is automatically inferred as a **Borrowed Reference**. This
prevents ownership cycles while still permitting common recursive data
structures.

### 2.3. Syntactic Refinement

Branch-dependent facts (e.g., null-checks or union tag checks) are tied to
lexical scopes. This eliminates the need for path-sensitive SMT solving; "truth"
is derived from the AST structure itself.

### 2.4. Rank-1 Poly-variance

Hic treats `void*` as a syntactic alias for a generic template parameter
$\forall T$. It employs Rank-1 poly-variance where every call site instantiates
fresh local type variables, and function signatures are generalized bottom-up
according to the call graph's Strongly Connected Components (SCCs).

## 3. Architecture: Solver Design

Hic employs a multi-pass architecture designed to guarantee termination. The
pipeline is strictly stratified to avoid global fixpoints.

### 3.1. Phased Analysis

The solver processes the program in topological order:

1.  **Array Flavor Inference:** Categorizes arrays into Homogeneous (Flavor A)
    or Heterogeneous (Flavor B) based on indexing patterns.
2.  **SCC Decomposition:** Identifies recursive function groups.
3.  **Topological Solving:** Solves constraints bottom-up. Leaf functions are
    solved once; their summaries are used by callers, preventing "bleeding" of
    type information across unrelated call sites.

### 3.2. Lattice and Co-induction

The solver operates on a lattice of finite height. To support the **Nominal
Recursion** required for lists and trees without triggering infinite type
expansion, Hic employs **Co-inductive Unification** (graph-based bisimulation).
This allows the solver to identify that a pointer to `struct Node` within the
definition of `struct Node` is a stable identity rather than an infinite
sequence of nested types. This guarantees that the solver reaches a stable Least
Fixed Point (LFP) even when analyzing complex, self-referential C structures.

## 4. Semantic Lifting: Structure as Annotation

Hic treats idiomatic code patterns as implicit semantic annotations, recovering
contracts directly from the source.

*   **Tagged Unions:** Hic promotes sum-type patterns to first-class Tagged
    Unions. A `union` paired with an enum tag is identified and isolated; once
    promoted, the internal `union` structure is hidden, and Hic **forbids** any
    direct member access or tag mutation. Access is only permitted through
    idiomatic `switch` or `if` guards, which are lifted into type-safe `Match`
    constructs. By converting a heuristic observation into a mandatory semantic
    invariant, Hic ensures that the safety of the union is mathematically sound.
*   **Iteration:** Standard C `for` loops are promoted to high-level `ForEach`
    or `Find` constructs. Hic enforces a **Strict Iteration Invariant**: the
    induction variable and collection bound must be immutable within the loop
    body. If the code attempts to "bypass" the iterator (e.g., via manual index
    mutation or out-of-bounds pointer arithmetic), the promotion fails, and the
    loop is rejected as unsafe. The "lift" thus serves as a formal proof of
    memory safety for the collection traversal.
*   **Reversibility:** A core design constraint of Hic is **Strict
    Reversibility**: `lower(lift(source)) == source`. Unlike traditional
    refactoring tools that produce machine-generated artifacts, Hic ensures that
    high-level refinements are bidirectional projections of the original source,
    preserving comments, indentation, and brace style. This ensures that safety
    verification remains fully compatible with the existing C toolchain.

## 5. Evaluation: The Toxcore Case Study

Hic was evaluated on **Toxcore**, a ~100k LOC networking library.

*   **Performance:** Hic achieves near-linear analysis time, avoiding the
    exponential blowup typical of abstract interpretation on standard C.
*   **Ambiguity Rejection:** Unlike Infer, which silences errors to maintain
    usability, Hic's "Hard Rejection" model flags semantically ambiguous code.
    For example, Hic identified "Mixed Index" (Flavor C) usage in packet
    registries that, while valid C, were inherently impossible to prove safe
    without manual annotations.
*   **Precision:** Hic successfully identified ownership leaks in resource
    allocation paths that were invisible to shallow linters by enforcing linear
    move semantics across function boundaries.

## 6. Related Work

*   **CCured (2002):** Pioneered the classification of C pointers into SAFE,
    SEQ, and WILD categories. While Hic adopts a similar inference strategy, it
    fundamentally diverges in its enforcement: Hic employs **static rejection**
    instead of runtime instrumentation, ensuring zero runtime overhead and
    preserving standard C ABI compatibility.
*   **Frama-C / Astrée:** Provide sound analysis but struggle with standard C's
    aliasing. Hic achieves tractability by restricting the language to a
    decidable subset.
*   **Checked C / RefinedC:** Achieve safety through annotations. Hic removes
    the annotation tax by treating common C idioms as implicit semantic markers.

## 7. Conclusion

The novelty of Hic lies not in the underlying type theory, but in the
engineering of a language subset (**Strict Hic**) that renders that theory
computationally tractable for legacy systems. By requiring code to be
"idiomatically compliant" and rejecting the underspecified or ambiguous features
of the C specification, we enable sound, whole-program verification without the
need for manual annotations.

## References

-   [1] Cuoq, P., et al. "Frama-C: A software analysis perspective." SEFM 2012.
-   [2] Cousot, P., et al. "The ASTRÉE Analyzer." ESOP 2005.
-   [3] Calcagno, C., et al. "Moving Fast with Software Verification." NFM 2015.
-   [4] Elliott, A., et al. "Checked C: Making C Safe by Default." 2018.
-   [5] Sammler, M., et al. "RefinedC: Automating the Foundational Verification
    of C Code with Refined Type Systems." PLDI 2021.
-   [6] Necula, G., et al. "CCured: Type-safe retrofitting of legacy software."
    POPL 2002.
