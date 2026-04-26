/-
  L4YAML Documentation — Architecture
-/
import VersoManual
import Doc.L4YAML.ModuleGroups

open Verso.Genre Manual
open Doc.L4YAML.ModuleGroups

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
The project is organized into several module groups.
The table below is regenerated at doc-elaboration time by walking each
group's source directory under `L4YAML/`, so the file lists stay in
sync with the actual code.

:::moduleGroups
:::

# Import Graph
%%%
tag := "import-graph"
%%%

The runtime module dependency graph (Scanner, Parser, Surface, Schema,
Output, FFI, Config — the `Proofs/` subtree is excluded) is regenerated
in CI by `lake exe graph` and rendered to SVG via Graphviz.

![L4YAML runtime import graph](graphs/import-graph.svg)
