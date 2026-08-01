# Terminology

Shared vocabulary for L4YAML. Whenever a property or theorem uses one
of these words, it must refer to the precise definition here.

## Specification-side terms (the "what")

<details>
<summary>
These refer to concepts from the YAML 1.2.2 specification itself,
independent of any implementation.
</summary>

### Grammar

<details>
<summary> 

The **YAML 1.2.2 specification grammar** — the 221 numbered BNF
productions of [YAML 1.2.2](https://yaml.org/spec/1.2.2/).

</summary>

- **In Lean**: the `Grammar` namespace in [`L4YAML/Spec/Grammar.lean`](../L4YAML/Spec/Grammar.lean).
  Production predicates live in [`L4YAML/Spec/YamlSpec.lean`](../L4YAML/Spec/YamlSpec.lean).
- **Key inductives**: `Grammar.ValidNode`, `Grammar.ValidYaml`,
  `Grammar.ValidDocument`, `Grammar.ValidStream`, `Grammar.ValidTokenStream`.
- **Read "`Grammar.ValidX thing`" as**: *`thing` is a valid YAML `X`
  per the spec*.
- **Not to be confused with**: the *implementation's* parser
  (`parseYaml`). Grammar is the reference; the parser is the code
  under verification.

</details>

### Surface (syntax)

<details>
<summary> 

The **character-level view** of YAML: which byte sequences are valid
YAML text per the spec's `l-*` / `c-*` / `ns-*` / `s-*` productions.

</summary>

- **In Lean**: the `Surface` namespace under
  [`L4YAML/Surface/`](../L4YAML/Surface/). Contains character
  predicates (`SIndent`, `GChar`, `SBBreak`, etc.) and recognizers
  for indentation, breaks, plain-scalar content, etc.
- **Read "surface-level"**: pertaining to raw characters, before any
  tokenization.
- **Coupling proofs** (`SurfaceCoupling.lean`, `ScalarCoupling.lean`,
  `StructureCoupling.lean`) show that every scanner operation's
  character-level behavior matches the corresponding surface
  predicate.

</details>

### Production

<details>
<summary> 

A named BNF rule from the spec, e.g. `[183] l+block-sequence(n)`.

</summary>

- **Category**: spec
- **Why central**: Named BNF rule; everything else defers to these.
- **In Lean**: production predicates are defined in `YamlSpec.lean`.
- **Linked via**: `@[yaml_spec "8.2.1" 183 "l+block-sequence(n)"]`
  attributes on functions and theorems. The scanner and parser
  functions each carry one or more such tags.

</details>

### Schema (Core Schema)

<details>
<summary> 

The **type-resolution layer** defined in YAML 1.2.2 §10.3
("Core Schema"). Maps unquoted scalars to `null`, `bool`, `int`,
`float`, or `str` based on lexical form.

</summary>

- **In Lean**: `Schema` namespace; [`L4YAML/Schema/Schema.lean`](../L4YAML/Schema/Schema.lean)
  (umbrella) + other files in [`L4YAML/Schema/`](../L4YAML/Schema/).
- **Scope**: only applies to *untagged* scalars. Explicit tags
  (`!!int`, `!!str`, etc.) override schema resolution.
- **Distinct from**: user-defined application schemas. L4YAML
  currently implements the Core Schema only.

</details>

### Tags

<details>
<summary> 

YAML **type annotations**, both the short forms (`!!str`, `!!int`)
and the full URI forms (`tag:yaml.org,2002:str`).

</summary>

- **In Lean**: `YamlToken.tag` variant carries `(handle : String)
  (suffix : String)`. [`L4YAML/Proofs/Schema/TagResolution.lean`](../L4YAML/Proofs/Schema/TagResolution.lean)
  handles `%TAG` directive expansion and `escapeTag` URI escaping.
- **Two separate operations**: *parsing* (resolving `!` + `handle` +
  `suffix` via `%TAG` directives in force) and *applying* (using
  the resolved tag to type a value).

</details>

### Anchors and Aliases

<details>
<summary> 

YAML's **reference mechanism**. `&name` marks a node as the anchor
for `name`; `*name` elsewhere in the same document is an alias
referring to that anchored node.

</summary>

- **Category**: spec+impl
- **Why central**: `*name` consumers (aliases) are distinct from `&name` producers (anchors); both flavors carry separate proof obligations.
- **In Lean**: `YamlToken.anchor`, `YamlToken.alias`; `ParseState`
  carries an `anchors : Array (String × YamlValue)` map.
- **Key predicates**:
  - `AnchorsGrow` (ParserAnchorProofs) — the anchor map is
    monotonic: anchors accumulate, never get dropped.
  - `AllAliasesResolve` (ParserAnchorProofs) — every alias in the
    output has a matching anchor defined earlier.
  - `WellFormedAnchors` / `WFA` (ParserWfaProofs) — the anchor
    map's bodies are themselves `Grammable`.

</details>

### Document

<details>
<summary> 

One logical YAML document — the content between `---` markers (or
the whole stream if no markers).

</summary>

- **In Lean**: `YamlDocument`, a structure carrying the `YamlValue`
  plus directive metadata (`%YAML` version, `%TAG` handles).
- **Stream**: an ordered sequence of documents; `parseYaml` returns
  `Array YamlDocument`.
- **`...` vs `---`**: `...` ends a document and permits a bare
  next document; without `...`, the next document must be explicit
  (`---` or directives). Encoded by `StreamState` in TokenParser.

</details>

</details>

## Implementation-side terms (the "how")

<details>
<summary>
These name the actual functions, types, and invariants in L4YAML's
code.
</summary>

### Scanner

<details>
<summary>

The **lexical-layer** function `scan : String → Except ScanError
(Array (Positioned YamlToken))`.

</summary>

- **Module**: the [`L4YAML/Scanner/`](../L4YAML/Scanner/) folder —
  [`Scanner.lean`](../L4YAML/Scanner/Scanner.lean) is the dispatch
  umbrella over seven submodules (`State`, `Whitespace`, `Indent`,
  `Document`, `NodeProperties`, `Scalar`, `SimpleKey`). An
  intrinsically-indexed twin lives beside it (`IndexedScanner.lean`,
  `IndexedState.lean`, `IndexedDispatch.lean`,
  `IndexedPresenter.lean`; see *Indexed pipeline* below).
- **State** (`ScannerState`): input offset, indentation stack, flow
  level, simple-key slot, anchor map, position cursor.
- **Invariant**: `WellFormed` / `BoundInv` — offset ≤ inputEnd,
  indent stack monotone, flow level ≥ 0, etc.
- **Public entry points**: `scan` (raw) and `scanFiltered`
  (placeholder tokens stripped).

</details>

### Token

<details>
<summary>

A **lexical element** of YAML. Defined as `YamlToken` inductive in
[`L4YAML/Token/Token.lean`](../L4YAML/Token/Token.lean).

</summary>

- **Variants**: `streamStart`, `streamEnd`, `documentStart`,
  `documentEnd`, `blockSequenceStart`, `blockMappingStart`,
  `blockEnd`, `flowSequenceStart`, `flowSequenceEnd`,
  `flowMappingStart`, `flowMappingEnd`, `key`, `value`,
  `blockEntry`, `flowEntry`, `scalar content style`, `anchor`,
  `alias`, `tag`, `comment`, `versionDirective`, `tagDirective`,
  `placeholder` (scanner-internal).
- **Positioned**: wrapped as `Positioned YamlToken`, carrying
  `YamlPos` (offset, line, column).

</details>

### Parser

<details>
<summary>

The **syntactic-layer** function `parseStream : Array (Positioned
YamlToken) → Except ScanError (Array YamlDocument)`.

</summary>

- **Module**: [`L4YAML/Parser/TokenParser.lean`](../L4YAML/Parser/TokenParser.lean)
  (~830 LoC; within the [`L4YAML/Parser/`](../L4YAML/Parser/)
  folder, alongside `State.lean`, `Fuel.lean`, `Composition.lean`,
  and the indexed twin `TokenParserIx.lean`).
- **Strategy**: hand-written recursive descent; 18 mutually-recursive
  functions — 7 top-level parsers (`parseNode`, `parseFlowSequence`,
  `parseFlowMapping`, `parseBlockSequence`, `parseBlockMapping`,
  `parseImplicitBlockSequence`, `parseSinglePairMapping`), 5
  `*Loop` helpers, and 6 entry/value helpers (`parseNodeContent`,
  `parseBlockMappingEntryValue`, `handleBlockMappingKeyEntry`,
  `handleBlockMappingValueEntry`, `parseFlowMappingValue`,
  `parseExplicitKey`). `parseNodeProperties` is a plain `def` in
  [`Parser/State.lean`](../L4YAML/Parser/State.lean), outside the
  mutual block.
- **Termination**: fuel-based (`fuel : Nat`), initialized to
  `4 * tokens.size + 4` in `parseDocument`. No `partial def`.
- **State** (`ParseState`): token array + cursor + anchor map +
  current path + tracking flags.

</details>

### Composition (`parseYaml` family)

<details>
<summary>

The **end-to-end** function `parseYaml : String → Except ScanError
(Array YamlDocument)`, defined as `compose ∘ parseStream ∘
scanFiltered`.

</summary>

- **Category**: impl
- **Why central**: The object of the top-level theorems.
- **Module**: [`L4YAML/Parser/Composition.lean`](../L4YAML/Parser/Composition.lean)
  (`parseYamlRaw` at line 73, `parseYaml` at line 86);
  decomposition theorems in
  [`L4YAML/Proofs/Composition.lean`](../L4YAML/Proofs/Composition.lean).
- **`parseYamlRaw`**: without schema resolution (scalars remain as
  strings).
- **`parseYaml`**: applies schema; final result is typed.

</details>

### Emitter

<details>
<summary>

The **canonical serializer**: `emit : YamlValue → String`.

</summary>

- **Category**: impl
- **Why central**: Distinct from Dumper; *canonical* serializer used in round-trip proofs.
- **Module**: [`L4YAML/Output/Emitter.lean`](../L4YAML/Output/Emitter.lean) (~164 LoC).
- **Canonical**: deterministic, style-insensitive. Always produces
  the same bytes for the same `YamlValue`.
- **Distinct from Dumper** (below). The Emitter's role in proofs is
  to be the left inverse of `parse` modulo content equivalence.

</details>

### Dumper (style-aware serializer)

<details>
<summary>

The **configurable serializer**: `dump : DumpConfig → YamlValue →
String`.

</summary>

- **Module**: [`L4YAML/Output/Dump.lean`](../L4YAML/Output/Dump.lean).
- **Difference from Emitter**: honors style hints (flow vs block,
  quoted vs plain scalar, literal vs folded), uses configurable
  indentation, inserts comments. Output is human-readable YAML but
  not canonical.
- **In proofs**: `DumpRoundTrip.lean` handles dumper properties;
  `RoundTripComposition.lean` covers the `dump → parse → resolve`
  cycle.

</details>

### YamlValue

<details>
<summary>

The **runtime AST** — the user-facing data type produced by
`parseYaml`. Simple inductive: `scalar`, `sequence`, `mapping`.

</summary>

- **Category**: impl
- **Why central**: The runtime AST — what users see.
- **Module**: [`L4YAML/Spec/Types.lean`](../L4YAML/Spec/Types.lean).
- **Does not carry**: grammar-derivation annotations. For that,
  see `YamlNode`.

</details>

### YamlNode (grammar-level AST)

<details>
<summary>

The **annotated AST** used inside grammar witnesses: carries
position, style, and derivation information beyond the bare
`YamlValue`.

</summary>

- **Category**: spec
- **Why central**: The annotated AST that grammar witnesses produce.
- **Module**: [`L4YAML/Spec/Grammar.lean`](../L4YAML/Spec/Grammar.lean) (inside `Grammar`).
- **`stripAnnotations : YamlNode → YamlValue`**: the forgetful map.
- **Used when**: stating soundness (`∃ node : YamlNode,
  stripAnnotations (toYamlValue node) = v`).

</details>

### Fuel

<details>
<summary>

The **decreasing argument** threaded through the parser's mutually
recursive functions.

</summary>

- **Category**: impl
- **Why central**: Parser's decreasing argument; appears in every parser theorem.
- Each recursive call passes `fuel` (unchanged, in a nested call) or
  `fuel - 1` (in a tail call). Reaching `fuel = 0` returns
  `Except.error .nestingDepthExceeded` at top-level parsers, or a
  degenerate `.ok (#[], ps)` at loop helpers (structural base case).
- **Standard bound**: `4 * tokens.size + 4`, established in
  `parseDocument`. Monotonicity lemmas allow larger fuel without
  changing the result.

</details>

### ParseState

<details>
<summary>

The **parser's cursor plus context**.

</summary>

- **Category**: impl
- **Why central**: Parser's state vector; arguments of nearly every parser lemma.
- `tokens : Array (Positioned YamlToken)` — input
- `pos : Nat` — cursor
- `anchors : Array (String × YamlValue)` — anchor map
- `currentPath : YamlPath` — for error reporting (G5c)
- `trackPositions : Bool`, `nodePositions : Array ...` — tracking
  flags (G5c position spans)

</details>

### Grammable

<details>
<summary>

**Implementation-side predicate** on `YamlValue`: "this value could
arise from a valid grammar derivation."

</summary>

- **Category**: bridge
- **Why central**: The predicate linking runtime values to grammar.
- **Bool flavor**: `Grammable v flow_context : Bool` in `Grammar.lean`.
- **Prop flavor**: `GrammableProp`, relates to `∃ node, stripAnnotations
  (toYamlValue node) = v`.
- **Bridging theorems** in [`ParserGrammable.lean`](../L4YAML/Proofs/Parser/ParserGrammable.lean) /
  [`ParserSoundness.lean`](../L4YAML/Proofs/Parser/ParserSoundness.lean) discharge the
  grammability hypothesis unconditionally for parser output.

</details>

### ContentEq

<details>
<summary>

**Value equivalence modulo annotations and presentation**.

</summary>

- **Category**: bridge
- **Why central**: The equivalence used in round-trip statements.
- Defined structurally: scalars equal by content (disregarding style),
  sequences equal pointwise, mappings equal as multisets of pairs
  (key order is *preserved* but `contentEq` may weaken that).
- **Role in proofs**: universal round-trip states `contentEq v
  (parse (emit v) ).fst` rather than `v = ...`, because the emitter
  normalizes style.

</details>

### WellFormed / BoundInv

<details>
<summary>

The **scanner's internal invariants**. Bundled in `ScannerState.WellFormed`
and `BoundInv`; each scanner step is proved to preserve them.

</summary>

- **Category**: impl
- **Why central**: The scanner invariant preserved through the pipeline.

</details>

### Config / Limits

<details>
<summary>

**Resource bounds** — nesting depth, string length, collection
cardinality. Configurable via `ParserLimits`; 4 built-in presets
(`strict`, `permissive`, `unlimited`, `safeTagsOnly`).

</summary>

- **Modules**: [`L4YAML/Config/Config.lean`](../L4YAML/Config/Config.lean),
  [`L4YAML/Config/Limits.lean`](../L4YAML/Config/Limits.lean),
  [`L4YAML/Config/LoadConfig.lean`](../L4YAML/Config/LoadConfig.lean)
  (load-time policy: `LoadConfig` bundling `EqMode` +
  `DuplicateKeyPolicy`).

</details>

### Indexed pipeline (intrinsic twin)

<details>
<summary>

The **position-indexed re-implementation** of the scanner/parser
pipeline, built on intrinsic indexed types in Initiative 4
([`08-initiative-4-intrinsic-foundations.md`](08-initiative-4-intrinsic-foundations.md)).

</summary>

- **Category**: impl
- **In Lean**: core types in [`L4YAML/Indexed/`](../L4YAML/Indexed/)
  (`CharStream`, `Range`, `RepGraph`, `TokenStream`, all indexed by
  the input string); scanner twin
  [`Scanner/IndexedScanner.lean`](../L4YAML/Scanner/IndexedScanner.lean)
  (+ `IndexedState`, `IndexedDispatch`, and the token-stream renderer
  [`IndexedPresenter.lean`](../L4YAML/Scanner/IndexedPresenter.lean));
  parser twin
  [`Parser/TokenParserIx.lean`](../L4YAML/Parser/TokenParserIx.lean)
  (`parseStreamIx`) with entry point `parseYamlSingleIx` in
  [`Parser/IndexedComposition.lean`](../L4YAML/Parser/IndexedComposition.lean).
- **Proofs**: the `Indexed*` twins under `Proofs/Scanner/`,
  `Proofs/Parser/` — capstoned in
  [`IndexedCompleteness.lean`](../L4YAML/Proofs/Parser/IndexedCompleteness.lean) —
  and `Proofs/Output/IndexedEmitterScannability/`.
- **Status**: wired into the library build since 2026-07-31
  (formerly parked under Initiative 4's Guardrail 1).

</details>

### Algebra (law library)

<details>
<summary>

**Reusable algebraic laws** factored out ahead of the proofs that
consume them (Initiative 4 Phase 2 — "algebra before threading").

</summary>

- **Category**: bridge
- **In Lean**: [`L4YAML/Algebra/`](../L4YAML/Algebra/) — 13 modules
  (`AnchorMap`, `Combinators`, `Equivalence`, `Fuel`, `Idempotence`,
  `Indent`, `LawfulBEq`, `Position`, `Schema`, `StringList`,
  `Token`, `TokenStream`, `Value`).
- **Absorbed**: the former `Proofs/Foundation/LawfulBEq.lean` and
  `Proofs/Foundation/ValueAlgebra.lean` (now
  `Algebra/LawfulBEq.lean`, `Algebra/Value.lean`).

</details>

</details>

## Other terms (defined in module documentation)

<details>
<summary>
These appear in proofs and code but are local enough that their
canonical definition lives in the relevant module's documentation,
not here.
</summary>

| Term | Category | Where defined / why noted |
| ---- | -------- | ------------------------- |
| **Simple key** | impl | [`Scanner/SimpleKey.lean`](../L4YAML/Scanner/SimpleKey.lean) — a plain scalar that *may become* a mapping key retroactively. Explains the placeholder/backpatch design. |
| **Flow vs Block context** | spec+impl | [`Scanner/Scanner.lean`](../L4YAML/Scanner/Scanner.lean) flow-level counter. YAML's two syntactic modes; orthogonal to everything else, but threaded through scanner and grammar. |
| **Schema resolution** | spec | [`Schema/Schema.lean`](../L4YAML/Schema/Schema.lean) — the *act* of applying the Core Schema, vs the Schema itself (defined above). |
| **Adversarial instantiation** | method | [`Tests/Guards/`](../Tests/Guards/) — pre-proof validation technique that exercises edge cases ahead of the formal soundness chain. |

</details>
