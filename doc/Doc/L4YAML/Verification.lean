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

Each theorem is accompanied by a bipartite dependency graph
showing the implementation functions it proves properties
about (blue, left) and the supporting theorems used in
its proof (green, right).  Stdlib lemmas surface in orange
when they are domain-relevant.

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

### `parseYaml_pipeline`

![parseYaml_pipeline dependency graph](graphs/parseYaml_pipeline.svg)

### `parseYamlRaw_pipeline`

![parseYamlRaw_pipeline dependency graph](graphs/parseYamlRaw_pipeline.svg)

### `parseYamlRaw_ok_decompose`

![parseYamlRaw_ok_decompose dependency graph](graphs/parseYamlRaw_ok_decompose.svg)

### `parseYaml_ok_iff`

![parseYaml_ok_iff dependency graph](graphs/parseYaml_ok_iff.svg)

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

### `scan_produces_valid_tokens`

![scan_produces_valid_tokens dependency graph](graphs/scan_produces_valid_tokens.svg)

### `advance_offset_lt`

![advance_offset_lt dependency graph](graphs/advance_offset_lt.svg)

### `scanLoop_success_emits_streamEnd`

![scanLoop_success_emits_streamEnd dependency graph](graphs/scanLoop_success_emits_streamEnd.svg)

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

### `parseStream_sound`

![parseStream_sound dependency graph](graphs/parseStream_sound.svg)

### `parseNode_anchors_grow`

![parseNode_anchors_grow dependency graph](graphs/parseNode_anchors_grow.svg)

### `parseNode_aliases_resolve'`

![parseNode_aliases_resolve' dependency graph](graphs/parseNode_aliases_resolve_27.svg)

### `parseStream_output_anchors_wellformed`

![parseStream_output_anchors_wellformed dependency graph](graphs/parseStream_output_anchors_wellformed.svg)

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

### `toYamlValue_correct`

![toYamlValue_correct dependency graph](graphs/toYamlValue_correct.svg)

### `nodeToValue_total`

![nodeToValue_total dependency graph](graphs/nodeToValue_total.svg)

### `nodeToValue_deterministic`

![nodeToValue_deterministic dependency graph](graphs/nodeToValue_deterministic.svg)

### `scalar_content_preserved`

![scalar_content_preserved dependency graph](graphs/scalar_content_preserved.svg)

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

### `contentEq_refl`

![contentEq_refl dependency graph](graphs/contentEq_refl.svg)

### `contentEq_symm`

![contentEq_symm dependency graph](graphs/contentEq_symm.svg)

### `contentEq_trans`

![contentEq_trans dependency graph](graphs/contentEq_trans.svg)

### `emit_content_invariant`

![emit_content_invariant dependency graph](graphs/emit_content_invariant.svg)

### `escapeTag_roundtrip`

![escapeTag_roundtrip dependency graph](graphs/escapeTag_roundtrip.svg)

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

# What L4YAML Proves
%%%
tag := "theorem-graphs"
%%%

{index}[headline theorems]
{index}[dependency graphs]
This page is the front-door answer to _what L4YAML proves_.  Each
card below embeds one headline theorem's _functorial chain graph_
— the proof-term dependency structure extracted by the FGM
`theoremgraph` tool — together with its plain-English summary and
a ChainDepth tag that classifies how tightly the theorem's proof
is pinned to the pipeline functions it names.  The ChainDepth tags
carry the honesty labelling from §Mind the Fibration Gap: _deep_
theorems are canaries for silent behavioural drift, _propBridge_
theorems delegate that role to a wrapped predicate, and _weak_
theorems do not participate in the fibration at all.

Only the headline + categoryCapstone entries (~11 theorems) are
embedded here; the full catalogue is published as the
`theorem-graphs-all.tar.gz` asset on the
[`graphs-latest` release of L4YAML.FGM](https://github.jpl.nasa.gov/pass/L4YAML.FGM/releases/tag/graphs-latest)
and is downloadable on demand.  Per-module hierarchical browsing
of the full catalogue inside this site is a planned step.

## Pipeline Composition
%%%
tag := "theorem-graphs-pipeline"
%%%

### `parseYaml_pipeline` — deep

_1.1_ — `parseYaml` decomposes as `parseStream ∘ scanFiltered`.
The pipeline's decomposition capstone: every downstream
soundness/completeness headline routes through it.

![parseYaml_pipeline chain graph](graphs/L4YAML/Proofs/Composition/parseYaml_pipeline.chain.svg)

 * _ChainDepth_: `deep`
 * _Module_: `L4YAML.Proofs.Composition`

## Scanner
%%%
tag := "theorem-graphs-scanner"
%%%

### `scan_full_consumption` — deep

_2.1_ — a successful scan consumes the entire input.  Rules out
the common correctness trap where a scanner returns `.ok` after
stopping early on an unexpected character.

![scan_full_consumption chain graph](graphs/L4YAML/Proofs/Scanner/ScanStrictCoupling/scan_full_consumption.chain.svg)

 * _ChainDepth_: `deep`
 * _Module_: `L4YAML.Proofs.Scanner.ScanStrictCoupling`

## Parser
%%%
tag := "theorem-graphs-parser"
%%%

### `parseStream_respects_grammar_unconditional` — deep

_3.1_ — the parser respects the YAML 1.2.2 grammar with no
well-formedness precondition.  The root anchor for the grammar-
production chain.

![parseStream_respects_grammar_unconditional chain graph](graphs/L4YAML/Proofs/EndToEndCorrectness/parseStream_respects_grammar_unconditional.chain.svg)

 * _ChainDepth_: `deep`
 * _Module_: `L4YAML.Proofs.EndToEndCorrectness`

## End-to-End Correctness
%%%
tag := "theorem-graphs-end-to-end"
%%%

The two soundness variants (`parse_sound_shallow` and
`parse_sound_deep`) are the fibration-gap worked example — see
§Fibration Gap — Worked Example for the side-by-side walkthrough.

### `parse_sound_shallow` — propBridge

_4.1_ — `parse .ok → ValidYamlProp`.  The shallow variant hides
the pipeline stages inside the `ValidYamlProp` predicate; the
chain walker cannot descend.  Useful as a minimal soundness
statement; not the canary.

![parse_sound_shallow chain graph](graphs/L4YAML/Proofs/EndToEndCorrectness/parse_sound_shallow.chain.svg)

 * _ChainDepth_: `propBridge`
 * _Module_: `L4YAML.Proofs.EndToEndCorrectness`

### `parse_sound_deep` — deep

_4.1d_ — same soundness claim with every pipeline stage exposed
in the type and each stage's lemma cited in the proof.  The
canary for silent code changes along `parseYaml → parseYamlRaw →
parseStream`.

![parse_sound_deep chain graph](graphs/L4YAML/Proofs/EndToEndCorrectness/parse_sound_deep.chain.svg)

 * _ChainDepth_: `deep`
 * _Module_: `L4YAML.Proofs.EndToEndCorrectness`

### `parse_complete` — propBridge

_4.2_ — `ValidYamlProp → parse .ok`.  Completeness with the
same `Prop`-wrapping shape as `parse_sound_shallow`; an
engineering follow-up analogous to `parse_sound_deep` would
expose the pipeline stages and cite the completeness lemmas
directly.

![parse_complete chain graph](graphs/L4YAML/Proofs/EndToEndCorrectness/parse_complete.chain.svg)

 * _ChainDepth_: `propBridge`
 * _Module_: `L4YAML.Proofs.EndToEndCorrectness`

### `parse_deterministic` — weak

_4.3_ — `parse` is a function (same input, same output).
Structurally weak: the proof is tactic-only and cites no project
lemmas, so no functorial chain exists.  Serves as a type-level
sanity check on the API shape, not as a canary.

![parse_deterministic chain graph](graphs/L4YAML/Proofs/EndToEndCorrectness/parse_deterministic.chain.svg)

 * _ChainDepth_: `weak` (structural)
 * _Module_: `L4YAML.Proofs.EndToEndCorrectness`

## Values — Soundness
%%%
tag := "theorem-graphs-values"
%%%

### `validYaml_construct` — weak

_5.1_ — constructing `ValidYaml` from a parse result is
well-defined.  Establishes that the packaging step from `docs`
to `ValidYaml` respects the underlying invariants; the proof is
structural and carries no fibration signal.

![validYaml_construct chain graph](graphs/L4YAML/Proofs/Soundness/validYaml_construct.chain.svg)

 * _ChainDepth_: `weak` (structural)
 * _Module_: `L4YAML.Proofs.Soundness`

## Roundtrip
%%%
tag := "theorem-graphs-roundtrip"
%%%

### `universal_roundtrip` — deep (🚧 sorry-reachable via 6.9)

_6.1_ — the universal YAML round-trip property: emit ∘ parse is
content-preserving up to `contentEq`.  Fibration-aligned against
the emitter/parser composition; carries a sorry marker via 6.9
pending the final stage's proof.

![universal_roundtrip chain graph](graphs/L4YAML/Proofs/Output/EmitterScannability/universal_roundtrip.chain.svg)

 * _ChainDepth_: `deep`
 * _Module_: `L4YAML.Proofs.Output.EmitterScannability`

## Grammar Production
%%%
tag := "theorem-graphs-production"
%%%

### `parse_strict_proof` — deep (🚧 sorry-reachable via 7.2, 7.6)

_7.1_ — parser acceptance implies `InYamlLanguage`.  Bridges the
parser-level chain to the grammar-production relation used by the
Blueprint.  Sorry-reachable via the scanner-side 7.2/7.6 lemmas.

![parse_strict_proof chain graph](graphs/L4YAML/Proofs/Production/DocumentProduction/parse_strict_proof.chain.svg)

 * _ChainDepth_: `deep`
 * _Module_: `L4YAML.Proofs.Production.DocumentProduction`

## Surface Coupling
%%%
tag := "theorem-graphs-surface-coupling"
%%%

### `SIndent_zero` — weak

_8.1_ — bundle representative for character-level
indent/character predicates.  Structural lemma connecting the
scanner's character-class tests to the `SIndent` surface
predicate; does not itself expose a call chain.

![SIndent_zero chain graph](graphs/L4YAML/Proofs/Coupling/SurfaceCoupling/SIndent_zero.chain.svg)

 * _ChainDepth_: `weak` (structural)
 * _Module_: `L4YAML.Proofs.Coupling.SurfaceCoupling`

## Generating graphs locally

The `theoremgraph` tool lives in the
[L4YAML.FGM](https://github.jpl.nasa.gov/pass/L4YAML.FGM) bridge
project; see its `tools/README.md` for invocations.  Common
starting points:

```
cd ../L4YAML.FGM
lake build theoremgraph
lake exe theoremgraph --list                       # catalogue
lake exe theoremgraph --chain parse_sound_deep     # one chain DOT
lake exe theoremgraph --tier headline tmp/out      # headline tarball contents
lake exe theoremgraph tmp/graphs                   # full tree (≈400 DOTs)
```

# Mind the Fibration Gap
%%%
tag := "fibration-gap"
%%%

{index}[fibration gap]
{index}[functorial chain]
{index}[canary theorem]
When you read "this theorem is machine-checked," two follow-up
questions are worth asking:

 1. _How significant is this theorem?_  Is it a deep statement about
    how the code behaves, or a shallow observation about the code's
    shape?
 2. _Would this theorem break if we changed the code?_  If a refactor
    silently broke the parser, would the kernel catch it — or would
    the theorem quietly survive the change?

These are not philosophical questions.  They have a mechanical,
_kernel-objective_ answer that is read directly off the proof term
the kernel has already accepted.  The answer comes from stitching
together two natural bipartite graphs —

 * the _function call graph_ (`f` calls `f'`), and
 * the _theorem dependency graph_ (`T` cites `T'` in its proof) —

using the _about_ relation (the theorem `T` mentions the function
`f` in its type) as the bridge between them.  A theorem that threads
all three relations tightly together is said to _fibrate_ over the
call graph; one that does not leaves a _fibration gap_.

Two natural fibrations run through every proof module, corresponding
to the three relations above:

 * _The "about" fibration_ — each theorem projects to the set of
   project functions mentioned in its type.  This is what
   `#about_functions` reports.
 * _The "uses" fibration_ — each theorem projects to the set of
   other project theorems cited in its proof term.  This is what
   `#proof_deps` reports.

A theorem is _deep_ when the two fibrations align: the lemmas cited
in its proof are themselves about the callees of the functions the
root theorem is about.  The `FGM.ExploreGraph.findFunctorialChains`
analyzer walks this alignment one step at a time, and the
`ChainDepth` classifier tags the result as `deep`, `propBridge`,
`weak`, or `noAbout`.

## Why Fibration Matters: The Canary Theorem
%%%
tag := "canary-theorem"
%%%

A deeply fibrated theorem acts as a _canary_.  Because its proof
term cites specific lemmas about specific callees, any code change
that invalidates the underlying behaviour invalidates those lemmas,
which invalidates the theorem, which the kernel then refuses to
re-accept.  The build breaks at the theorem that pinned the claim,
pointing directly at the layer of the pipeline whose behaviour has
shifted.  The deeper the fibration, the more callees are pinned, and
the more sensitive the canary.

A weak, unfibrated theorem gives no such signal.  Because its proof
never descends into the callees, it can survive code changes that
genuinely affect parser behaviour.  `parse_sound_shallow` is a working
example: its statement asserts only that _some_ token stream exists
for which the pipeline decomposition equation holds — it says
nothing about which tokens came out of the scanner, nor what the
parsed documents actually contain.  A refactor that shuffles the
parser's internal decision tree, or silently corrupts the emitted
document content, can leave `parse_sound_shallow` intact and the kernel
silent.  Strong behavioural guarantees must come from somewhere
else — from the underlying parser-correctness lemmas, or from a
canary like `parse_sound_deep` that explicitly cites them.

This does not mean structurally weak theorems are worthless.  They
may still carry value — as witnesses that two definitions are
definitionally equal, as type-class coherence lemmas, as rewriting
hints, or as quick sanity checks on API shape.  Those uses are
legitimate, but they answer a different question than fibration
does.  _For the specific question "does this theorem catch breaking
code changes?", the fibration structure is the right instrument_,
and it is the one this document measures.

## The Alignment Rule
%%%
tag := "alignment-rule"
%%%

A chain link `(T, f)` — a root theorem `T` paired with a function
`f` that `T` is about — extends to `(T', f')` iff _all three_
conditions hold:

 1. `T' ∈ thmDeps(T)` — `T'` is a project theorem cited in the
    proof term of `T`
 2. `f' ∈ about(T')` — the type of `T'` mentions `f'`
 3. `f' ∈ fnDeps(f)` — `f`'s body calls `f'`

Informally, the square

```
     T  --uses-->  T'
     |              |
   about          about
     v              v
     f  --calls--> f'
```

must commute.  Each arrow corresponds to one edge colour in the
bipartite graph — green for `uses`, blue for `calls`, purple for
`about`.  Alignment requires _three_ simultaneous edges at every
step, which is exactly categorical base-change: the functorial
chain is the lifting of the call-graph path `f → f'` along the
about-fibration, guided by the proof-chain `T → T'`.

## What Breaks Alignment
%%%
tag := "alignment-antipatterns"
%%%

 * _Prop-wrapping_ — stating the theorem as `… → SomeProp args`
   pushes the about-fibration into the definition body of `SomeProp`.
   `collectAbout` only inspects the raw type, so the analyzer sees
   `SomeProp` as a single opaque target.  The three-way alignment
   collapses before step 1.
 * _Tactic-only proofs_ — `unfold; split; injection`, `rfl`,
   `grind`, `decide`, and friends produce proof terms with no
   project-theorem citations.  Condition 1 fails trivially and no
   chain extends.
 * _Co-location_ — citing only lemmas that are about the _same_
   top-level function the root is about.  The alignment square
   collapses to the identity on the function side: condition 3 fails
   because no new call edge is exposed.

## The Engineering Rule
%%%
tag := "engineering-rule"
%%%

When engineering a headline theorem intended for dependency-analysis
consumption:

 1. _Expose the fibration in the type_.  Name the pipeline functions
    explicitly in the statement; avoid `Prop`-wrappers that hide them.
 2. _Cite lemmas about callees_.  Every project lemma used in the
    proof should itself be about a function that is a strict callee
    of the function the root theorem is about.
 3. _Prefer a step-wise proof over a tactic blob_.  Each
    `have ⟨…⟩ := lemma …` contributes one functorial step;
    each uncited `unfold`/`split`/`grind` discards one.

# Fibration Gap — Worked Example
%%%
tag := "fibration-worked-example"
%%%

`EndToEndCorrectness` ships two soundness headlines that differ
only in how much of the fibration they expose.  They are an
exact demonstration of the alignment rule.

## `parse_sound_shallow` — fibration-hidden
%%%
tag := "parse-sound-shallow"
%%%

```
theorem parse_sound_shallow (input : String) (docs : Array YamlDocument)
    (h : TokenParser.parseYaml input = .ok docs) :
    ValidYamlProp input docs
```

 * _Type_ mentions `parseYaml`, `YamlDocument`, `ScanError`, and
   `ValidYamlProp`.  The pipeline stages (`scanFiltered`,
   `parseStream`, `YamlDocument.compose`) are hidden inside the
   existential body of `ValidYamlProp`.
 * _Proof_ is four tactics: `unfold; split; injection; …`.  No
   project theorem is cited.
 * _Consequence_: condition 1 of the alignment rule fails at every
   root function, so the chain walker returns zero functorial chains.
   The `ChainDepth` classifier tags this theorem `propBridge` —
   recognisable by its Prop-typed target — and renders a diagnostic
   overlay labelled "NOT proof deps of the headline."

## `parse_sound_deep` — fibration-aligned
%%%
tag := "parse-sound-deep"
%%%

```
theorem parse_sound_deep (input : String) (docs : Array YamlDocument)
    (h : TokenParser.parseYaml input = .ok docs) :
    ∃ (tokens : Array (Positioned YamlToken))
      (raw_docs : Array YamlDocument),
      Scanner.scanFiltered input = .ok tokens ∧
      TokenParser.parseYamlRaw input = .ok raw_docs ∧
      TokenParser.parseStream tokens = .ok raw_docs ∧
      docs = raw_docs.map YamlDocument.compose ∧
      (∀ doc ∈ docs.toList, ∃ node : ValidNode,
         stripAnnotations (toYamlValue node) = stripAnnotations doc.value)
```

 * _Type_ mentions `parseYaml`, `parseYamlRaw`, `parseStream`,
   `scanFiltered`, `YamlDocument.compose`, `toYamlValue`, and
   `ValidNode` directly.  Every pipeline stage is a first-class
   citizen of the about-fibration.
 * _Proof_ cites `parseYamlRaw_ok_decompose` (about `parseYamlRaw`,
   `scanFiltered`, `parseStream`) and `parseYaml_produces_valid_nodes`
   (about `parseYaml`, `toYamlValue`), the second of which
   transitively drags in `parseStream_output_grammable` (about
   `parseStream`).
 * _Consequence_: conditions 1, 2, and 3 of the alignment rule
   close simultaneously at multiple root functions.  The
   `ChainDepth` classifier tags this theorem `deep`.

## Chain-Analysis Confirmation
%%%
tag := "fibration-confirmation"
%%%

Running the FGM `theoremgraph` tool in `--chain` mode on both
theorems produces the following metrics (tool output captured
on 2026-04-24).

:::table +header
*
  * Metric
  * `parse_sound_shallow`
  * `parse_sound_deep`
*
  * Project theorems on chain
  * 0
  * 4 (root + 3 proof deps)
*
  * `uses` edges (theorem-fibration steps)
  * 0
  * 4
*
  * `calls` edges (function-fibration steps)
  * 0
  * 9
*
  * Aligned `about` edges
  * 0
  * 12
*
  * `ChainDepth` classification
  * `propBridge`
  * `deep`
:::

The proof-dep theorems surfaced on `parse_sound_deep` are:

 * `parseYamlRaw_ok_decompose` (module `Composition`) — splits a
   successful `parseYamlRaw` into a successful `scanFiltered` step
   and a successful `parseStream` step
 * `parseYaml_produces_valid_nodes` (module `ParserGrammable`) —
   bridges `parseYaml` success to per-document `ValidNode` witnesses
 * `parseStream_output_grammable` (module `ParserGrammable`) —
   guarantees every `parseStream`-produced document is grammable

Each of these is _about_ a strict callee of `parseYaml`, so the
alignment square closes at every step of the descent:

```
parse_sound_deep --uses--> parseYamlRaw_ok_decompose --uses--> parseStream_output_grammable
         |                          |                                  |
       about                      about                              about
         v                          v                                  v
     parseYaml --calls--> parseYamlRaw --calls--> parseStream
```

`parse_sound_shallow`'s chain graph, by contrast, is a diagnostic overlay:
it enumerates the catalogue entries that _would_ be relevant if the
alignment existed, and the legend explicitly labels those nodes
"NOT proof deps of the headline."  The absence of any `uses` or
`calls` edge is the fibration gap made visible.

Takeaway: a theorem passing the kernel is a statement about
correctness; a theorem passing the chain walker is additionally a
statement about _traceability_.  The two are not the same.  The
`deep` / `propBridge` / `weak` / `noAbout` classification in
`FGM.TheoremGraph` is the knob that surfaces this distinction
across the catalogue.

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
