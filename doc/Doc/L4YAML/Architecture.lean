/-
  L4YAML Documentation — Architecture
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Architecture" =>
%%%
tag := "architecture"
%%%

{index}[architecture]
L4YAML implements a two-pass pipeline that mirrors the layered
structure of the YAML 1.2.2 specification itself.
Input bytes flow through a character-level {ref "scanner"}[scanner],
producing a typed token stream, which a {ref "token-parser"}[recursive-descent parser]
converts into a structured AST.

# Scanner (Lexical Layer)
%%%
tag := "scanner"
%%%

{index}[scanner]
The scanner (`Scanner.lean`, ~920 lines) converts a UTF-8 input string
into a stream of `YamlToken` values.
It implements 132 YAML productions from the specification and maintains
several pieces of state:

 * _Indentation stack_ — tracks block-level nesting via column positions
 * _Flow level counter_ — distinguishes block context from flow context
   (`[`, `]`, `{`, `}`)
 * _Simple key state_ — manages the YAML "simple key" lifecycle where a
   plain scalar may retroactively become a mapping key when `:` is encountered
 * _Anchor map_ — records anchor names for alias resolution
 * _Position tracking_ — offset, line, and column for every token

The scanner returns `Except ScanError (Array YamlToken)`, where
`ScanError` carries position information and a human-readable message.

## Token Types
%%%
tag := "token-types"
%%%

{index}[YamlToken]
The `YamlToken` inductive defines the full set of lexical elements:

 * Stream markers: `streamStart`, `streamEnd`
 * Document markers: `documentStart`, `documentEnd`
 * Structure indicators: `blockSequenceStart`, `blockMappingStart`,
   `blockEnd`, `flowSequenceStart`, `flowSequenceEnd`,
   `flowMappingStart`, `flowMappingEnd`, `key`, `value`,
   `blockEntry`, `flowEntry`
 * Content tokens: `scalar` (with style tag: plain, single-quoted,
   double-quoted, literal, folded), `anchor`, `alias`, `tag`
 * Placeholder tokens: used as reservation slots for simple key
   backpatching (filtered before output)

## Append-Only Design
%%%
tag := "append-only"
%%%

{index}[append-only tokens]
A critical design choice is the _append-only token stream_.
When the scanner encounters a potential simple key, it pushes two
placeholder tokens (for the future `key` and `blockMappingStart`
indicators) and records their indices.
If the key is later confirmed (by encountering `:`), these
placeholders are overwritten in-place via `setIfInBounds`.
If not confirmed, they remain as placeholders and are filtered
out before the token stream is returned.

This avoids `insertAt` operations that would shift array indices
and invalidate saved positions — a property that is essential for
the formal proof that the scanner makes monotonic progress.

# Token Parser (Syntactic Layer)
%%%
tag := "token-parser"
%%%

{index}[token parser]
The token parser (`TokenParser.lean`, ~426 lines) consumes the
`YamlToken` stream and produces an `Array YamlDocument`.
It implements 54 YAML productions via hand-written recursive descent
(no parser combinator library).

Key responsibilities:

 * _Multi-document support_ — handles `---` and `...` boundaries
 * _Alias resolution_ — substitutes `*anchor` references with
   previously anchored values
 * _Tag resolution_ — applies `%TAG` directive handle expansion
   and schema-level type resolution
 * _Schema application_ — resolves untagged scalars to typed values
   (`null`, `bool`, `int`, `float`, `str`) via the Core Schema

# Type System
%%%
tag := "type-system"
%%%

{index}[YamlValue]
The output AST is centered on `YamlValue`, a compact inductive type:

 * `YamlValue.scalar` — tagged string value with resolved `YamlType`
 * `YamlValue.sequence` — ordered list of values
 * `YamlValue.mapping` — list of key-value pairs (preserving order)

Each value is wrapped in `YamlDocument`, which carries document-level
metadata including directive tags and version indicators.

Position tracking is provided by `YamlPos` (offset, line, column),
enabling precise error reporting that maps back to the original input.

# Module Organization
%%%
tag := "module-organization"
%%%

{index}[module organization]
The project is organized into several module groups:

:::table +header
*
  * Group
  * Key Modules
  * Purpose
*
  * Core
  * `Types.lean`, `Token.lean`, `Grammar.lean`, `YamlSpec.lean`, `CharPredicates.lean`
  * Type definitions, token types, grammar inductive, spec production predicates
*
  * Scanner
  * `Scanner/Scanner.lean` (umbrella), `State.lean`, `Whitespace.lean`, `Indent.lean`, `Document.lean`, `NodeProperties.lean`, `Scalar.lean`, `SimpleKey.lean`
  * Character-to-token conversion with full state management. Split into seven role-named submodules (Blueprint Phase 2, 2026-04-21); the umbrella owns flow-collection indicators and the `scanNextToken` dispatch / `scan` / `scanLoop` main loop.
*
  * Parser
  * `Parser/Composition.lean` (umbrella), `TokenParser.lean` (mutual block), `State.lean`, `Fuel.lean`
  * Token-to-AST recursive descent. Split into four role-named files (Blueprint Phase 3, 2026-04-21); `Composition.lean` owns the user-facing pipeline (`parseYaml*`, `scanAndParse`, comment classification), `TokenParser.lean` keeps the 14-function mutually-recursive block plus `parseStream` / `parseDocument`, `State.lean` holds `ParseState` + `NodeProperties` helpers, and `Fuel.lean` factors out the `initialFuel := 4*N+4` formula.
*
  * Validation
  * `Limits.lean`, `Schema.lean`
  * Security limits, Core Schema type resolution
*
  * Output
  * `Emitter.lean`, `Dump.lean`, `RoundTrip.lean`
  * Canonical emitter (~164L), style-aware dump, round-trip properties
*
  * FFI
  * `FFI.lean`, `ffi/`, `python/`, `rust/`
  * C/Python/Rust bindings via `@[export]`
*
  * Proofs
  * `Proofs/` (61 modules, ~47,000 lines)
  * Machine-checked theorems for soundness, completeness, progress, well-formedness
:::

# Import Graph
%%%
tag := "import-graph"
%%%

The project's dependency structure can be visualized using
`lake exe graph`.
The FFI layer sits at the top, depending on `Config`, which
in turn depends on the scanner/parser/schema pipeline:

```
FFI ← Config ← Dump ← Schema ← Token ← Scanner ← TokenParser
                                   ↑
                          CharPredicates ← YamlSpec
```

The full import graph and component-level dependency graphs are
available in the `graphs/` directory as Graphviz DOT files.
