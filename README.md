# Hic: High Integrity Cimple

Hic is a "reverse compiler" for the Cimple C-dialect. It employs heuristic-based
analysis to infer high-level language constructs from standard C patterns,
producing an intent-rich AST that is strictly reversible.

## Core Concepts

-   **Lifting (Inference)**: Identifying low-level C patterns (like `goto
    CLEANUP`) and lifting them into semantic constructs (like `Scoped`).
-   **Lowering**: The process of transforming high-level constructs back into
    identical Cimple AST nodes, ensuring that the original code structure is
    preserved.
-   **Global Inference**: Analysis that leverages cross-file information (struct
    definitions, global constants, typedefs) to identify complex domain
    patterns.

## Project Structure

-   `src/Language/Hic/Ast.hs`: Defines the high-level Hic AST.
-   `src/Language/Hic/Inference.hs`: Heuristic engine for lifting C to Hic.
-   `src/Language/Hic.hs`: Core transformation logic (Lowering).
-   `src/Language/Hic/Inference/Program.hs`: Global program-level state
    management.
-   `tools/hic-check.hs`: Verification tool for round-trip integrity.

## Documentation

For detailed design principles and a list of supported constructs, see the
[Design Documentation](doc/design.md).
