# Terminology

Shared vocabulary for L4YAML. Whenever a property or theorem uses one
of these words, it must refer to the precise definition here.

## Specification-side terms (the "what")

These refer to concepts from the YAML 1.2.2 specification itself,
independent of any implementation.

### Grammar
The **YAML 1.2.2 specification grammar** — the 221 numbered BNF
productions of [YAML 1.2.2](https://yaml.org/spec/1.2.2/).
- **In Lean**: the `Grammar` namespace in [`L4YAML/Spec/Grammar.lean`](../L4YAML/Spec/Grammar.lean).
  Production predicates live in [`L4YAML/Spec/YamlSpec.lean`](../L4YAML/Spec/YamlSpec.lean).
- **Key inductives**: `Grammar.ValidNode`, `Grammar.ValidYaml`,
  `Grammar.ValidDocument`, `Grammar.ValidStream`, `Grammar.ValidTokenStream`.
- **Read "`Grammar.ValidX thing`" as**: *`thing` is a valid YAML `X`
  per the spec*.
- **Not to be confused with**: the *implementation's* parser
  (`parseYaml`). Grammar is the reference; the parser is the code
  under verification.

### Surface (syntax)
The **character-level view** of YAML: which byte sequences are valid
YAML text per the spec's `l-*` / `c-*` / `ns-*` / `s-*` productions.
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

### Production
A named BNF rule from the spec, e.g. `[183] l+block-sequence(n)`.
- **Category**: spec
- **Why central**: Named BNF rule; everything else defers to these.
- **In Lean**: production predicates are defined in `YamlSpec.lean`.
- **Linked via**: `@[yaml_spec "8.2.1" 183 "l+block-sequence(n)"]`
  attributes on functions and theorems. The scanner and parser
  functions each carry one or more such tags.

### Schema (Core Schema)
The **type-resolution layer** defined in YAML 1.2.2 §10.3
("Core Schema"). Maps unquoted scalars to `null`, `bool`, `int`,
`float`, or `str` based on lexical form.
- **In Lean**: `Schema` namespace; [`L4YAML/Schema/Schema.lean`](../L4YAML/Schema/Schema.lean)
  (umbrella) + other files in [`L4YAML/Schema/`](../L4YAML/Schema/).
- **Scope**: only applies to *untagged* scalars. Explicit tags
  (`!!int`, `!!str`, etc.) override schema resolution.
- **Distinct from**: user-defined application schemas. L4YAML
  currently implements the Core Schema only.

### Tags
YAML **type annotations**, both the short forms (`!!str`, `!!int`)
and the full URI forms (`tag:yaml.org,2002:str`).
- **In Lean**: `YamlToken.tag` variant carries `(handle : String)
  (suffix : String)`. [`L4YAML/Proofs/TagResolution.lean`](../L4YAML/Proofs/TagResolution.lean)
  handles `%TAG` directive expansion and `escapeTag` URI escaping.
- **Two separate operations**: *parsing* (resolving `!` + `handle` +
  `suffix` via `%TAG` directives in force) and *applying* (using
  the resolved tag to type a value).

### Anchors and Aliases
YAML's **reference mechanism**. `&name` marks a node as the anchor
for `name`; `*name` elsewhere in the same document is an alias
referring to that anchored node.
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

### Document
One logical YAML document — the content between `---` markers (or
the whole stream if no markers).
- **In Lean**: `YamlDocument`, a structure carrying the `YamlValue`
  plus directive metadata (`%YAML` version, `%TAG` handles).
- **Stream**: an ordered sequence of documents; `parseYaml` returns
  `Array YamlDocument`.
- **`...` vs `---`**: `...` ends a document and permits a bare
  next document; without `...`, the next document must be explicit
  (`---` or directives). Encoded by `StreamState` in TokenParser.

## Implementation-side terms (the "how")

These name the actual functions, types, and invariants in L4YAML's
code.

### Scanner
The **lexical-layer** function `scan : String → Except ScanError
(Array (Positioned YamlToken))`.
- **Module**: [`L4YAML/Scanner/Scanner.lean`](../L4YAML/Scanner/Scanner.lean) (~920 LoC).
- **State** (`ScannerState`): input offset, indentation stack, flow
  level, simple-key slot, anchor map, position cursor.
- **Invariant**: `WellFormed` / `BoundInv` — offset ≤ inputEnd,
  indent stack monotone, flow level ≥ 0, etc.
- **Public entry points**: `scan` (raw) and `scanFiltered`
  (placeholder tokens stripped).

### Token
A **lexical element** of YAML. Defined as `YamlToken` inductive in
[`L4YAML/Token/Token.lean`](../L4YAML/Token/Token.lean).
- **Variants**: `streamStart`, `streamEnd`, `documentStart`,
  `documentEnd`, `blockSequenceStart`, `blockMappingStart`,
  `blockEnd`, `flowSequenceStart`, `flowSequenceEnd`,
  `flowMappingStart`, `flowMappingEnd`, `key`, `value`,
  `blockEntry`, `flowEntry`, `scalar content style`, `anchor`,
  `alias`, `tag`, `comment`, `versionDirective`, `tagDirective`,
  `placeholder` (scanner-internal).
- **Positioned**: wrapped as `Positioned YamlToken`, carrying
  `YamlPos` (offset, line, column).

### Parser
The **syntactic-layer** function `parseStream : Array (Positioned
YamlToken) → Except ScanError (Array YamlDocument)`.
- **Module**: [`L4YAML/Parser/TokenParser.lean`](../L4YAML/Parser/TokenParser.lean) (~800 LoC).
- **Strategy**: hand-written recursive descent; 14 mutually-recursive
  functions (`parseNode`, `parseFlowSequence`, `parseFlowMapping`,
  `parseBlockSequence`, `parseBlockMapping`,
  `parseImplicitBlockSequence`, `parseSinglePairMapping`, plus 5
  `*Loop` helpers).
- **Termination**: fuel-based (`fuel : Nat`), initialized to
  `4 * tokens.size + 4` in `parseDocument`. No `partial def`.
- **State** (`ParseState`): token array + cursor + anchor map +
  current path + tracking flags.

### Composition (`parseYaml` family)
The **end-to-end** function `parseYaml : String → Except ScanError
(Array YamlDocument)`, defined as `compose ∘ parseStream ∘
scanFiltered`.
- **Category**: impl
- **Why central**: The object of the top-level theorems.
- **Module**: [`L4YAML/Parser/TokenParser.lean`](../L4YAML/Parser/TokenParser.lean)
  (`parseYaml`, `parseYamlRaw`); decomposition theorems in
  [`L4YAML/Proofs/Composition.lean`](../L4YAML/Proofs/Composition.lean).
- **`parseYamlRaw`**: without schema resolution (scalars remain as
  strings).
- **`parseYaml`**: applies schema; final result is typed.

### Emitter
The **canonical serializer**: `emit : YamlValue → String`.
- **Category**: impl
- **Why central**: Distinct from Dumper; *canonical* serializer used in round-trip proofs.
- **Module**: [`L4YAML/Output/Emitter.lean`](../L4YAML/Output/Emitter.lean) (~164 LoC).
- **Canonical**: deterministic, style-insensitive. Always produces
  the same bytes for the same `YamlValue`.
- **Distinct from Dumper** (below). The Emitter's role in proofs is
  to be the left inverse of `parse` modulo content equivalence.

### Dumper (style-aware serializer)
The **configurable serializer**: `dump : DumpConfig → YamlValue →
String`.
- **Module**: [`L4YAML/Output/Dump.lean`](../L4YAML/Output/Dump.lean).
- **Difference from Emitter**: honors style hints (flow vs block,
  quoted vs plain scalar, literal vs folded), uses configurable
  indentation, inserts comments. Output is human-readable YAML but
  not canonical.
- **In proofs**: `DumpRoundTrip.lean` handles dumper properties;
  `RoundTripComposition.lean` covers the `dump → parse → resolve`
  cycle.

### YamlValue
The **runtime AST** — the user-facing data type produced by
`parseYaml`. Simple inductive: `scalar`, `sequence`, `mapping`.
- **Category**: impl
- **Why central**: The runtime AST — what users see.
- **Module**: [`L4YAML/Spec/Types.lean`](../L4YAML/Spec/Types.lean).
- **Does not carry**: grammar-derivation annotations. For that,
  see `YamlNode`.

### YamlNode (grammar-level AST)
The **annotated AST** used inside grammar witnesses: carries
position, style, and derivation information beyond the bare
`YamlValue`.
- **Category**: spec
- **Why central**: The annotated AST that grammar witnesses produce.
- **Module**: [`L4YAML/Spec/Grammar.lean`](../L4YAML/Spec/Grammar.lean) (inside `Grammar`).
- **`stripAnnotations : YamlNode → YamlValue`**: the forgetful map.
- **Used when**: stating soundness (`∃ node : YamlNode,
  stripAnnotations (toYamlValue node) = v`).

### Fuel
The **decreasing argument** threaded through the parser's mutually
recursive functions.
- **Category**: impl
- **Why central**: Parser's decreasing argument; appears in every parser theorem.
- Each recursive call passes `fuel` (unchanged, in a nested call) or
  `fuel - 1` (in a tail call). Reaching `fuel = 0` returns
  `Except.error .nestingDepthExceeded` at top-level parsers, or a
  degenerate `.ok (#[], ps)` at loop helpers (structural base case).
- **Standard bound**: `4 * tokens.size + 4`, established in
  `parseDocument`. Monotonicity lemmas allow larger fuel without
  changing the result.

### ParseState
The **parser's cursor plus context**.
- **Category**: impl
- **Why central**: Parser's state vector; arguments of nearly every parser lemma.
- `tokens : Array (Positioned YamlToken)` — input
- `pos : Nat` — cursor
- `anchors : Array (String × YamlValue)` — anchor map
- `currentPath : YamlPath` — for error reporting (G5c)
- `trackPositions : Bool`, `nodePositions : Array ...` — tracking
  flags (G5c position spans)

### Grammable
**Implementation-side predicate** on `YamlValue`: "this value could
arise from a valid grammar derivation."
- **Category**: bridge
- **Why central**: The predicate linking runtime values to grammar.
- **Bool flavor**: `Grammable v flow_context : Bool` in `Grammar.lean`.
- **Prop flavor**: `GrammableProp`, relates to `∃ node, stripAnnotations
  (toYamlValue node) = v`.
- **Bridging theorems** in [`ParserGrammable.lean`](../L4YAML/Proofs/ParserGrammable.lean) /
  [`ParserSoundness.lean`](../L4YAML/Proofs/ParserSoundness.lean) discharge the
  grammability hypothesis unconditionally for parser output.

### ContentEq
**Value equivalence modulo annotations and presentation**.
- **Category**: bridge
- **Why central**: The equivalence used in round-trip statements.
- Defined structurally: scalars equal by content (disregarding style),
  sequences equal pointwise, mappings equal as multisets of pairs
  (key order is *preserved* but `contentEq` may weaken that).
- **Role in proofs**: universal round-trip states `contentEq v
  (parse (emit v) ).fst` rather than `v = ...`, because the emitter
  normalizes style.

### WellFormed / BoundInv
The **scanner's internal invariants**. Bundled in `ScannerState.WellFormed`
and `BoundInv`; each scanner step is proved to preserve them.
- **Category**: impl
- **Why central**: The scanner invariant preserved through the pipeline.

### Config / Limits
**Resource bounds** — nesting depth, string length, collection
cardinality. Configurable via `ParserLimits`; 4 built-in presets
(`strict`, `default`, `relaxed`, `unlimited`).
- **Modules**: [`L4YAML/Config/Config.lean`](../L4YAML/Config/Config.lean),
  [`L4YAML/Config/Limits.lean`](../L4YAML/Config/Limits.lean).

## Other terms (defined in module documentation)

These appear in proofs and code but are local enough that their
canonical definition lives in the relevant module's documentation,
not here.

| Term | Category | Where defined / why noted |
| ---- | -------- | ------------------------- |
| **Simple key** | impl | [`Scanner/SimpleKey.lean`](../L4YAML/Scanner/SimpleKey.lean) — a plain scalar that *may become* a mapping key retroactively. Explains the placeholder/backpatch design. |
| **Flow vs Block context** | spec+impl | [`Scanner/Scanner.lean`](../L4YAML/Scanner/Scanner.lean) flow-level counter. YAML's two syntactic modes; orthogonal to everything else, but threaded through scanner and grammar. |
| **Schema resolution** | spec | [`Schema/Schema.lean`](../L4YAML/Schema/Schema.lean) — the *act* of applying the Core Schema, vs the Schema itself (defined above). |
| **Adversarial instantiation** | method | [`Tests/Guards/`](../Tests/Guards/) — pre-proof validation technique that exercises edge cases ahead of the formal soundness chain. |
