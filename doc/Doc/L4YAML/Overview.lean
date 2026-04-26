/-
  L4YAML Documentation — Overview
-/
import VersoManual
import Doc.L4YAML.StatsTable

open Verso.Genre Manual
open Doc.L4YAML.StatsTable

set_option pp.rawOnError true

#doc (Manual) "Overview" =>
%%%
tag := "overview"
%%%

{index}[L4YAML]
L4YAML is a pure Lean 4 implementation of the YAML 1.2.2 specification
({index}[YAML 1.2.2]RFC 9512).
No external parsing libraries, no C dependencies in the core, and no
use of `partial def` — every function is provably terminating.

The project demonstrates that a production-quality parser for a
complex real-world format can be built and formally verified in
Lean 4, with practical performance and comprehensive test coverage.

# At a Glance
%%%
tag := "at-a-glance"
%%%

:::statsTable
:::

# Key Design Decisions
%%%
tag := "design-decisions"
%%%

The parser is built around several deliberate design choices:

 * *Pure Lean 4, zero external dependencies.*
   The core parser has no C FFI calls and no dependency on external
   parsing libraries.
   This ensures every line of parsing logic is visible to the
   Lean kernel for formal verification.

 * *Total functions only.*
   Every function terminates provably.
   The `partial` keyword is never used in production code.
   Termination is proved via well-founded recursion over input
   offsets, indentation levels, and flow nesting depth.

 * *Append-only token streams.*
   Tokens are emitted into a pre-allocated array with placeholder
   reservation slots.
   Backpatching uses `setIfInBounds` (bounded update) rather than
   `insertAt` (which would shift indices).
   This design ensures monotonic progress and simplifies the
   formal proof of scanner correctness.

 * *Two-pass architecture.*
   A character-level scanner emits a `YamlToken` stream, which a
   separate recursive-descent parser converts to a typed AST.
   This separation mirrors the YAML specification's own layered
   structure and enables independent verification of each layer.

 * *Configurable security limits.*
   All resource bounds (nesting depth, string length, collection sizes)
   are configurable via `ParserLimits`, with four built-in presets
   from `strict` to `unlimited`.
