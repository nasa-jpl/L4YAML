/-
  L4YAML Documentation — Verification Strategy
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Verification" =>
%%%
tag := "verification"
%%%

{index}[verification]
L4YAML employs a three-layer verification strategy that combines
formal proofs, compile-time checks, and runtime tests to achieve
comprehensive coverage of the YAML 1.2.2 specification.

# Three-Layer Strategy
%%%
tag := "three-layer-strategy"
%%%

## Layer 1: Machine-Checked Proofs
%%%
tag := "formal-proofs"
%%%

{index}[machine-checked proofs]
The core layer consists of 2,309 Lean 4 theorems across 61 proof
modules (~47,000 lines).
These proofs are checked by the Lean kernel — the small trusted
core of the system — and establish properties including:

 * *Soundness* — every token stream produced by the scanner
   corresponds to a valid YAML grammar derivation
 * *Completeness* — every valid YAML input is accepted (not
   rejected with an error)
 * *Progress* — the scanner's input offset strictly increases
   on every step, guaranteeing termination
 * *Well-formedness preservation* — internal invariants
   (indentation stack consistency, flow level balance, simple key
   lifecycle) are maintained across all scanner operations
 * *Pipeline composition* — scanner and parser compose correctly
   to deliver end-to-end guarantees

## Layer 2: Compile-Time Guards
%%%
tag := "compile-time-guards"
%%%

{index}[compile-time guards]
2,124 `#guard` statements are evaluated by the Lean kernel at
build time.
These are not runtime tests — they are _kernel-evaluated assertions_
that must hold for the project to compile.
A failing `#guard` is a build error, not a test failure.

Guards are used extensively for:

 * Concrete scanner behavior on specific inputs
 * Round-trip properties (parse → emit → parse = original)
 * Token stream structure for specification examples
 * Character predicate boundary conditions

## Layer 3: Runtime Tests
%%%
tag := "runtime-tests"
%%%

{index}[runtime tests]
1,041 runtime tests across 19 suites provide additional coverage:

 * _Specification examples_ — all 132/132 YAML 1.2.2 examples
 * _yaml-test-suite_ — 225/225 applicable test IDs (354/406 total;
   52 YAML 1.1/1.3 tests are correctly skipped)
 * _Property tests_ — randomized input generation for edge cases
 * _Mutation tests_ — systematic input perturbation
 * _Adversarial tests_ — handcrafted inputs targeting parser limits
 * _Round-trip tests_ — parse → dump → parse cycle validation

# Key Theorems
%%%
tag := "key-theorems"
%%%

{index}[key theorems]
The following capstone theorems represent the main formal
guarantees established by L4YAML.  Each is machine-checked
by the Lean kernel with zero axioms beyond the built-in
foundations.

## Pipeline Composition
%%%
tag := "thm-pipeline"
%%%

These theorems establish that the scanner and parser compose
correctly into a single end-to-end pipeline.

:::table +header
*
  * Theorem
  * Module
  * Statement
*
  * `parseYaml_pipeline`
  * `Composition`
  * End-to-end: scan then parse composes correctly.  If `scanFiltered` produces tokens and `parseStream` accepts them, then `parseYaml` succeeds with the same result.
*
  * `parseYamlRaw_pipeline`
  * `Composition`
  * Raw pipeline variant without schema resolution.
*
  * `parseYamlRaw_ok_decompose`
  * `Composition`
  * Every successful `parseYamlRaw` result decomposes into a successful scan step followed by a successful parse step.
*
  * `parseYaml_ok_iff`
  * `Completeness`
  * `parseYaml` succeeds if and only if the input is valid YAML — the bridge between the implementation and the specification.
:::

## Scanner Correctness
%%%
tag := "thm-scanner"
%%%

{index}[scanner correctness]
Properties of the character-to-token scanner:

:::table +header
*
  * Theorem
  * Module
  * Statement
*
  * `scan_produces_valid_tokens`
  * `ScannerCorrectness`
  * The scanner output satisfies `ValidTokenStream`: every emitted token is well-formed, positions are monotonically increasing, and the stream is bracketed by `STREAM_START`/`STREAM_END`.
*
  * `advance_offset_lt`
  * `ScannerProgress`
  * Scanner advance _strictly_ increases the byte offset when the offset is within bounds — this is the core termination lemma.
*
  * `scanLoop_success_emits_streamEnd`
  * `ScannerCorrectness`
  * A successful scan loop always terminates with a `STREAM_END` token.
:::

## Parser Correctness
%%%
tag := "thm-parser"
%%%

{index}[parser correctness]
Properties of the token-to-AST parser:

:::table +header
*
  * Theorem
  * Module
  * Statement
*
  * `parseStream_sound`
  * `ParserSoundness`
  * If the parser produces an AST, it corresponds to a valid YAML grammar derivation.
*
  * `parseNode_anchors_grow`
  * `ParserNodeProofs`
  * The anchor set grows monotonically through `parseNode` — anchors are never lost during parsing.
*
  * `parseNode_aliases_resolve'`
  * `ParserNodeProofs`
  * Every alias (`*name`) in the output of `parseNode` resolves to a previously defined anchor (`&name`).
*
  * `parseStream_output_anchors_wellformed`
  * `ParserWfaProofs`
  * After `parseStream` completes, all output anchors are well-formed: every alias target exists and every anchor body is `Grammable`.
:::

## Soundness
%%%
tag := "thm-soundness"
%%%

{index}[soundness]
Theorems establishing that the AST-to-value conversion
faithfully implements the YAML specification:

:::table +header
*
  * Theorem
  * Module
  * Statement
*
  * `toYamlValue_correct`
  * `Soundness`
  * The `toYamlValue` function correctly implements the specification's construction rules.
*
  * `nodeToValue_total`
  * `Soundness`
  * Every well-formed AST node can be converted to a `YamlValue` — the conversion is total.
*
  * `nodeToValue_deterministic`
  * `Soundness`
  * AST-to-value conversion is deterministic: the same input always produces the same output.
*
  * `scalar_content_preserved`
  * `Soundness`
  * Scalar string content is preserved through the parsing pipeline — no characters are added, dropped, or reordered.
:::

## Round-Trip Properties
%%%
tag := "thm-roundtrip"
%%%

{index}[round-trip]
Theorems about the parse → emit → parse cycle:

:::table +header
*
  * Theorem
  * Module
  * Statement
*
  * `contentEq_refl`
  * `RoundTrip`
  * Content equality is reflexive: every YAML value is content-equal to itself.
*
  * `contentEq_symm`
  * `RoundTrip`
  * Content equality is symmetric.
*
  * `contentEq_trans`
  * `RoundTrip`
  * Content equality is transitive — together with reflexivity and symmetry, this makes `contentEq` an equivalence relation.
*
  * `emit_content_invariant`
  * `ScannerEmitBridge`
  * The emitter preserves content equality: if two values are content-equal, their emitted canonical forms are identical.
*
  * `escapeTag_roundtrip`
  * `RoundTrip`
  * Tag URI escape and unescape are inverse operations.
:::

# Key Proof Modules
%%%
tag := "proof-modules"
%%%

:::table +header
*
  * Module
  * Theorems
  * Scope
*
  * `ScannerCorrectness.lean`
  * 259 theorems + 1,063 guards
  * Character-to-token correctness for all scanner operations
*
  * `Completeness.lean`
  * 63 theorems
  * Valid YAML inputs are accepted
*
  * `Soundness.lean`
  * 28 theorems
  * Output corresponds to valid grammar derivations
*
  * `RoundTrip.lean`
  * 58 theorems + 63 guards
  * Parse-emit-parse cycle properties
*
  * `Composition.lean`
  * 12 theorems
  * Scanner + parser pipeline correctness
*
  * `ScannerEmitBridge.lean`
  * 12 theorems + 64 guards
  * Bridge between scanner emissions and grammar predicates
*
  * `ParserSoundness.lean`
  * 12 theorems
  * Grammar-to-implementation correspondence
*
  * `ParserWfaProofs.lean`
  * 50 theorems
  * Well-formed anchors through entire parser pipeline
*
  * `ParserNodeProofs.lean`
  * 57 theorems
  * Anchor growth and alias resolution
*
  * `ParserWellBehaved.lean`
  * 102 theorems
  * Flow nesting, token preservation, scannable properties
*
  * `ScannerProgress.lean`
  * 24 theorems
  * Offset strictly increases on every scanner step
*
  * `ScannerSimpleKey.lean`
  * Multiple theorems
  * Simple key lifecycle well-formedness
*
  * `ScannerDispatch.lean`
  * Multiple theorems
  * Dispatch pipeline preserves all invariants
:::

# Theorem Dependency Visualization
%%%
tag := "theorem-graphs"
%%%

{index}[dependency graphs]
L4YAML includes tooling for visualizing theorem dependencies as
bipartite graphs.  Each graph shows a key theorem at the center,
with:

 * _Functions_ (left, blue) — the implementation functions the
   theorem proves a property about
 * _Proof dependencies_ (right, green) — the supporting theorems
   used in the proof

## Generating Graphs

Generate DOT files for all key theorems:

```
lake build theoremgraph
lake exe theoremgraph tmp/graphs
```

Render to SVG with Graphviz:

```
for f in tmp/graphs/*.dot; do
  dot -Tsvg "$f" -o "${f%.dot}.svg"
done
```

Then open `tmp/graphs/index.html` for an overview page.

Generate a single theorem's graph:

```
lake exe theoremgraph --dot parseYaml_pipeline
```

List all available key theorems:

```
lake exe theoremgraph --list
```

## Dependency Extraction

The lower-level `depgraph` tool extracts three complete dependency
graphs from the L4YAML environment:

 1. *Function call graph* — definition → definition calls
 2. *Theorem dependency graph* — theorem → theorems used in proof
 3. *Function–theorem map* — which functions each theorem is about

```
lake build depgraph
lake exe depgraph --dot calls   > calls.dot
lake exe depgraph --dot thmdeps > thmdeps.dot
lake exe depgraph --dot about   > about.dot
lake exe depgraph --stats
```

## Theorem Coverage Analysis

The `analyzethms` tool identifies leaf theorems (proved but never
cited in other proofs) and `native_decide` usage patterns:

```
lake build analyzethms
lake exe analyzethms tmp/analysis
```

This writes `leaf_thms.json`, `native_decide_leaves.json`,
`duplicates.json`, and `stats.txt`.

# Proof Engineering Patterns
%%%
tag := "proof-patterns"
%%%

{index}[proof engineering]
Several patterns emerged during the verification effort:

 * _Decomposition_ — large functions are decomposed into
   validation (error guards), state transformation (pure updates),
   and emission (token output) phases, each proved independently
   then composed.

 * _Append-only invariant_ — the switch from `insertAt` to
   placeholder reservation slots with `setIfInBounds` backpatching
   eliminated the hardest class of proof obligations (index shifting).

 * _Monotonic progress_ — proving `offset_lt` (strict increase)
   for every scanner operation provides termination and guarantees
   no infinite loops.

 * _Well-formedness threading_ — a `WellFormed` predicate on
   scanner state is threaded through every operation, establishing
   that invariants are maintained from `scannerInit` through
   `scanNextToken` to stream completion.

 * _Anchor monotonicity_ — the `AnchorsGrow` relation is proved
   transitively across all 14 mutually recursive parser functions,
   establishing that anchors accumulate but are never dropped.

 * _Fuel-based termination_ — the parser's 14 mutual functions
   use `fuel : Nat` as a decreasing argument.  Initial fuel is
   set to `4 * tokens.size + 4`, large enough for any valid input.

# Zero-Axiom Policy
%%%
tag := "zero-axiom"
%%%

{index}[zero axioms]
The project uses zero axioms beyond Lean's built-in foundations
(`propext`, `Quot.sound`, `Classical.choice`).
No `sorry` appears anywhere in the codebase.
No `partial def` is used — every function has a kernel-checked
termination proof.

This means the formal guarantees are as strong as the Lean kernel
itself: if the kernel accepts the proofs, the properties hold.
