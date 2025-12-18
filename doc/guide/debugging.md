# Hic Debugging Guide

This document explains how to develop and debug Hic (High-level Cimple).

## Debugging ASTs

When implementing new heuristics, it is often necessary to see the exact
structure of the Cimple AST. You can use the `dump-ast` tool from the
`hs-cimple` package.

### Using `dump-ast`

To dump the AST of a C file:

```bash
bazel run //hs-cimple/tools:dump-ast -- $PWD/path/to/file.c
```

**Note**: Always use absolute paths (e.g., via `$PWD`) when running tools via
Bazel if the files are outside the Bazel sandbox.

### Understanding the Output

The output is a Haskell-style representation of the `Node` structure. For
example:

```haskell
Fix (ForStmt
  (Fix (VarDeclStmt ...))
  (Fix (BinaryExpr ...))
  (Fix (UnaryExpr ...))
  (Fix (CompoundStmt ...)))
```

You can use this output to identify the patterns you want to match in
`Language.Hic.Inference`.

## Implementing a New Heuristic

1.  **Define the Node**: Add a new constructor to `HicNode` in
    `src/Language/Hic/Ast.hs`.
2.  **Implement Lowering**: Update `lowerHic` in `src/Language/Hic.hs` to
    transform your new node back into standard Cimple nodes.
3.  **Implement Inference**: Add a pattern match in
    `src/Language/Hic/Inference.hs` within `inferNode`.
4.  **Verify Round-trip**: Run the verification tool to ensure your change is
    reversible and doesn't break existing code: `bash
    ./hs-hic/tools/run-hic-check.sh`

## Debugging the Type Checker

The type checker follows a 7-phase modular architecture. You can debug each
phase independently using the `hic-check` tool.

### Phase-Based Debugging

Use `--stop-after` to halt execution at a specific phase and `--dump-json` to
export the results:

```bash
bazel run //hs-hic/tools:hic-check -- \
    $PWD/file.c \
    --stop-after global-structural \
    --dump-json output
```

This will produce `output-global-structural.json`.

### Inspecting Results with `jq`

-   **List generic hotspots**:

    ```bash
    jq '.garHotspots' output-global-structural.json
    ```

-   **Count mixed-access arrays**:

    ```bash
    jq '.aurFlavors | map(select(.[1] == "FlavorMixed")) | length' output-array-usage.json
    ```

-   **Check recursion in call graph**:

    ```bash
    jq '.cgrSccs | map(select(.tag == "Cyclic"))' output-call-graph.json
    ```

-   **View constraints for a specific function**:

    ```bash
    jq '.cgrConstraints["my_func"]' output-constraint-gen.json
    ```

-   **Check nullability facts**:

    ```bash
    jq '.narFacts' output-nullability.json
    ```

-   **Inspect high-level inference results**:

    ```bash
    jq '.hirNodes' output-inference.json
    ```

## Running and Filtering Tests

To run the type system tests:

```bash
bazel test //hs-hic:test-typesystem-ordered
```

### Filtering Tests

When debugging a specific issue, you can run a subset of tests using the
`--match` flag via `bazel run`:

```bash
# Either bazel run:
bazel run //hs-hic:test-typesystem-ordered -- --match="some test description"
# Or bazel test:
bazel test //hs-hic:test-typesystem-ordered --test_arg=--match="some test description"
```

This is often faster and provides more direct output than running the full test
suite.
