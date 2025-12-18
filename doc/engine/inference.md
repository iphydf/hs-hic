# Design Doc: High-Level Iteration Inference (ForEach / Find)

This document outlines the design for inferring high-level iteration constructs
(like `for_each`, `find`, `any`, and `all`) from low-level C `for` loops within
the Hic framework.

## 1. Goal

The goal is to lift imperative C loops into declarative functional-style
operations. This improves readability, enables formal verification of collection
properties, and simplifies translation to languages with built-in iterator
abstractions (Rust, Haskell, C++).

## 2. Target Patterns

We target the most common iteration patterns found in the Toxcore codebase:

### 2.1. Basic ForEach

**C Pattern:**

```c
for (uint32_t i = 0; i < collection_size; ++i) {
    process(collection[i]);
}
```

**Hic Lift:** `for_each(item in collection) { process(item); }`

### 2.2. Find / IndexOf

**C Pattern:**

```c
for (uint32_t i = 0; i < size; ++i) {
    if (match(collection[i], key)) {
        return i; // or return &collection[i]
    }
}
return NOT_FOUND;
```

**Hic Lift:** `find_index(item in collection where match(item, key))`

### 2.3. All / Any (Predicates)

**C Pattern:**

```c
for (uint32_t i = 0; i < size; ++i) {
    if (!is_valid(collection[i])) return false;
}
return true;
```

**Hic Lift:** `all(item in collection satisfies is_valid(item))`

## 3. Inference Heuristics

The inference engine identifies loops as candidates if they satisfy the
following criteria:

1.  **Induction Variable**: A single numeric variable (`i`) initialized to `0`
    and incremented by `1`.
2.  **Bound**: The loop condition compares `i` against a constant or a "length"
    field of a struct.
3.  **Access Pattern**: Within the loop body, the induction variable is
    primarily used as an index into one or more arrays (`collection[i]`).
4.  **No Induction Mutation**: The loop body must not modify the induction
    variable or the collection's bound.

### Lifting Search/Find logic

If the loop body consists of an `if` statement containing a `return` or `break`,
and that condition involves an array access at the current index, the entire
loop (and potentially the trailing `return` sentinel) is lifted into a `Find`
construct.

## 4. IR Representation (`HicNode`)

To satisfy the **reversibility constraint**, the lifted nodes must retain enough
information to reconstruct the original C loop headers exactly.

```haskell
| ForEach
    { feIterators  :: [lexeme]
    , feInit       :: a
    , feCond       :: a
    , feStep       :: a
    , feContainers :: [a]
    , feBody       :: a
    , feHasIndex   :: Bool
    }
| Find
    { fIterator  :: lexeme
    , fInit      :: a
    , fCond      :: a
    , fStep      :: a
    , fContainer :: a
    , fPredicate :: a
    , fOnFound   :: a
    , fOnMissing :: Maybe a
    }
| IterationElement
    { ieIterator  :: lexeme
    , ieContainer :: a
    }
| IterationIndex
    { iiIterator :: lexeme
    }
```

## 5. Implementation Strategy

Iteration inference is performed during **Phase 7: High-Level Construct
Inference**, utilizing the sound type information verified in Phases 1-6.

1.  **Recognition**:
    *   Implement `inferIteration` in `Language.Hic.Inference.Passes.Iteration`.
    *   Recognize `for` loops and verify induction variable properties.
    *   Trace usage of the index variable to identify the primary container.
2.  **Type Validation**:
    *   Use the verified types from the **Ordered Solver (Phase 6)** to ensure
        that array accesses and element types are consistent with the lifted
        construct.
3.  **Round-trip Verification**:
    *   Ensure that the lifted `ForEach` or `Find` node can be lowered back to
        the exact same imperative C loop.
4.  **Pretty-Printing**:
    *   Show `for_each item in container { ... }`.
    *   Show `find item in container where ...`.

## 6. Case Study: `net_crypto.c`

In `getcryptconnection_id`:

```c
for (uint32_t i = 0; i < c->crypto_connections_length; ++i) {
    if (pk_equal(public_key, c->crypto_connections[i].public_key)) {
        return i;
    }
}
return -1;
```

**Lifted Hic:**

```c
find i in c.crypto_connections where pk_equal(public_key, i.public_key) {
    return index;
} else {
    return -1;
}
```

## 7. Reversibility

To satisfy Hic's core mandate, the `ForEach`/`Find` nodes must store the
original induction variable name and the exact comparison operator used in the
loop header to ensure that `lower(lift(source)) == source`.
