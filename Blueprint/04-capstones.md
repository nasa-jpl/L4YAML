# Capstone theorems

The top-down specification of what L4YAML guarantees. Every lemma
in the repository must justify its existence by traceable use
(transitively) in one of the theorems below.

For each capstone this file now records **why it matters in
practice** and **what risk we would carry without the proof** — so a
reader can judge the guarantees on impact, not just on their formal
statement.

## Status snapshot (2026-07-04)

The build is **`sorry`-, `axiom`-, and `partial`-free.  Zero active
`sorry` sites remain: `universal_roundtrip` is fully machine-checked**
(axioms: `propext`, `Classical.choice`, `Quot.sound` plus the
pre-existing per-declaration `native_decide` reflected-decide leaves —
no `sorryAx` anywhere on the closed path).

**Track B closed 2026-07-04.**  The two former non-all-scalar locality
sorries (`emit_roundtrip_sequence_content_eq` /
`emit_roundtrip_mapping_content_eq`) are proven by the
**general-locality chain**, six new modules under
[`Proofs/Output/EmitterScannability/`](../L4YAML/Proofs/Output/):

| Module | Content |
|--------|---------|
| `TokVals.lean` | `emitTokVals` — the value-determined `.val`-run of an emission — and the `FlowCleanTok` window gate |
| `TokValsPin.lean` | the scanner Bridge: `scanFiltered (emit v)` pinned to `[streamStart] ++ emitTokVals v ++ [streamEnd]` (parallel deep-producer mirror; content-pinning scalar leaf) |
| `ValueLocality.lean` | the **both-success two-fuel value-locality joint** over the parser clique (`parseNode_joint`): `.val`-agreeing flow-clean windows + a one-sided standalone frame ⇒ equal values, equal advances, token preservation; step inversions for both flow loops; proper-exit-gated loop joints |
| `ValuePurity.lean` | `parseNode_pure`: values parsed from clean token arrays are `resolveAliases`-invariant, `stripAnchors`-invariant, anchor-free — collapsing `compose` to the identity on both sides |
| `StreamNodeWitness.lean` | `parseStream_single_doc_node_witness`: a single-document stream forces one `parseNode` at position 1 ending exactly at `streamEnd` — the joint's standalone frame |
| `GeneralLocality.lean` | the walks (`parseFlowSeqLoop_tokvals_value_at` / `parseFlowMapLoop_tokvals_pair_at`, R601/R608 generalized): each whole-stream slot equals its element's standalone composed value |

Consumption (`stdElt_of_grammable` + the two branch rewrites in
`EmitterScannability.lean`) subsumes the all-scalar template.  Key
design points, each Rule-2 probed before construction
(`Tests/Reflections/GeneralLocalityBirth.lean`): the joint must be
two-fuel (standalone vs in-stream fuels differ); two-fuel loop joints
are refutable at fuel 0, so they carry proper-exit hypotheses supplied
by the enclosing close-checks; the flow-clean gate replaces all
anchors/tagHandles hypotheses (emissions contain no anchor/alias/tag/
block syntax); and the frame is one-sided because only the standalone
run can supply it without re-importing bracket machinery.

**Track A closed 2026-07-03.**  The three former Track-A sorries —
`parseStream_emitSequence` / `scanFiltered_emitMap_nonempty_structure`
(both `FlowSubrangesOk`) and the R447 navigator linchpin
`seqBody_recseqbody_provider` — are now fully proven (`sorryAx`-free,
audited) by the **deep-family positional navigator**
([`DeepNavigator.lean`](../L4YAML/Proofs/Output/EmitterScannability/DeepNavigator.lean)):
the severance-free `RecSeqBodyDeep`/`RecMapBodyDeep` root bodies (off
emission) are walked positionally to EVERY close-gated sub-window
(`deep_navigate_core`), per-window `SeqBodyProps`/`MapBodyProps` are
read directly off the stored pair structure
(`mapBodyProps_of_recmapbodydeep`), and `FlowSubrangesOk` follows from
its definition (`flowSubrangesOk_of_deep_nav`) — no interior-separator
carrier and no six-fact assembler on the closed path.  Two Rule-2
catches were part of the closure (both refuted mechanically before
building): the navigator provider's original statement lacked its
close-gate (`Tests/Reflections/ProviderCloseGate.lean`), and the
landed guarded bracket-`succ` assembler hypotheses are unsatisfiable
on two-bracket-pair emissions (the R548 decoy at the hypothesis
level), which the direct producer bypasses.

Everything else — the scanner (Group 2), parser correctness /
soundness / completeness / determinism (Groups 3–4), value semantics
(Group 5), grammar-production and **acceptance strictness** (Group 7),
and surface coupling (Group 8) — is fully proved and kernel-checked.

**This supersedes the April-2026 accounting** that this file and the
now-retired `05-current-state.md` once carried, which described
~90–100 `sorry`s. Those have been discharged or removed:

- The `parser_fuel_mono_succ` fuel-monotonicity subtree (~24
  sub-theorems, ~3,200 LoC) and the rest of `ParserWellBehaved.lean`'s
  dead code were **deleted** after a `unified-dep-table
  --external-only` run proved they had zero out-of-namespace callers
  — validating the observation that motivated this blueprint (see
  [`README.md`](README.md), [`VERSION-0.4.7.md`](../VERSION-0.4.7.md)).
- `StreamAccum.lean`'s "28 sorries" were **docstring artifacts**
  (narrative mentions of `sorry'd`), not tactics; the file builds
  clean.
- Group 2.2, 5.2, and all of Group 7's forward direction have
  **closed** since April.

**Two converse theorems remain open** — they are the entire
work-remaining frontier:

1. **Universal round-trip** (Group 6.1, `universal_roundtrip`) — the
   2 `sorry`s above. *Emit-then-parse recovers content.*
2. **Grammar completeness** (Group 7.7, `parse_iff_grammar` converse)
   — **not yet declared**; blocked on the round-trip work and on
   removing two over-approximation grammar constructors
   ([`VERSION-0.4.8.md`](../VERSION-0.4.8.md)). *We accept **exactly**
   the YAML language, not merely a subset of well-formed inputs.*

**Status legend**
- ✅ proved (no `sorry`, kernel-checked)
- 🧩 proved conditional on an unproved hypothesis (by design, not a `sorry`)
- 🚧 partially proved (contains `sorry`s but not abandoned)
- ⏳ planned, not started
- 📝 stated only in a docstring/comment; not yet declared as a Lean theorem
- ❓ stated but possibly unsound — needs audit
- 🗑 deletion candidate

Each capstone entry shows: **Module** · **Status** · **One-line
meaning**, followed by a **Significance & risk** block giving, per
theorem, why it matters and what we would risk without it. Where
relevant, **Depends on** names the immediate predecessors in the
dependency DAG.

**Numbering convention**: each group's lead (headline or
categoryCapstone) is row `N.1`; supports follow.

**Tooling note**: the `| # | `\`name\`` | module | status |` row shape
is consumed by `check-capstones` (it diffs ✅ rows against the
`@[key_theorem]` catalogue in the sibling `L4YAML.FGM` repo). Rows
promoted from 🚧 to ✅ in this pass (2.2, 5.2, 7.1–7.6) now need
matching catalogue annotations — a follow-up tagging task, flagged
in [`README.md`](README.md) Initiative 2.

## Proof file locations (Phase 4 complete)

[Initiative 1 Phase 4](README.md) finished moving
`L4YAML/Proofs/*.lean` into role-named subclusters; the links below
point at the **current** paths. Four capstones stay at `Proofs/` root
because they are the top-down anchors of this blueprint:

- [`Composition.lean`](../L4YAML/Proofs/Composition.lean) — Group 1
- [`Completeness.lean`](../L4YAML/Proofs/Completeness.lean) — Group 1 + 3.12–3.14
- [`Soundness.lean`](../L4YAML/Proofs/Soundness.lean) — Group 5
- [`EndToEndCorrectness.lean`](../L4YAML/Proofs/EndToEndCorrectness.lean) — Group 4

---

## Group 1 — Pipeline composition

The scanner and parser compose to `parseYaml`. These theorems nail
down how the layers fit together.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 1.1 | `parseYaml_pipeline` (categoryCapstone) | [`Composition`](../L4YAML/Proofs/Composition.lean) | ✅ |
| 1.2 | `parseYamlRaw_pipeline` | `Composition` | ✅ |
| 1.3 | `parseYamlRaw_ok_decompose` | `Composition` | ✅ |
| 1.4 | `parseYaml_of_parseYamlRaw_ok` | `Composition` | ✅ |
| 1.5 | `parseYaml_ok_iff` | [`Completeness`](../L4YAML/Proofs/Completeness.lean) | ✅ |
| 1.6 | error-propagation theorems (`parseYamlRaw_scan_error`, `parseYamlRaw_parse_error`) | `Composition` | ✅ |

**Role**: the "plumbing" theorems — if `scanFiltered` succeeds with
tokens *T* and `parseStream T` succeeds with docs *D*, then
`parseYaml` succeeds with `D.map compose`. No soundness or
completeness claims here, just compositional decomposition.

**Significance & risk**

- **1.1 `parseYaml_pipeline`** — *Significance:* certifies that the
  one function users call *is* exactly scanner-then-parser composed,
  so every guarantee proved on the two-stage model transfers to the
  shipping entrypoint. *Risk if absent:* the properties we prove and
  the code that runs could diverge at the seam — soundness proved on
  a model nobody executes.
- **1.2 `parseYamlRaw_pipeline`** — *Significance:* the same
  guarantee for the position-preserving `Raw` variant that
  comment-aware and tooling APIs build on. *Risk if absent:* the
  tooling/editor path would be an unverified fork of the parser.
- **1.3 `parseYamlRaw_ok_decompose`** — *Significance:* lets any
  successful parse be split back into its token stream and document
  set — the lever nearly every downstream proof pulls. *Risk if
  absent:* each downstream property would have to re-derive the
  decomposition, or could not be stated at all.
- **1.4 `parseYaml_of_parseYamlRaw_ok`** — *Significance:* ties the
  two public entrypoints together so they cannot silently disagree.
  *Risk if absent:* `parseYaml` and `parseYamlRaw` could accept
  different inputs — a latent interop trap.
- **1.5 `parseYaml_ok_iff`** — *Significance:* a clean iff-characterization
  of parse success that downstream reasoning triggers on. *Risk if
  absent:* no crisp predicate to hang soundness/completeness off of.
- **1.6 error-propagation** — *Significance:* a scanner or parser
  error is always surfaced as a `parseYaml` error, never swallowed.
  *Risk if absent:* silent acceptance of input that a stage actually
  rejected — the most dangerous class of parser bug.

---

## Group 2 — Scanner correctness

Lexical-layer guarantees: every output token is well-formed, positions
are monotonic, termination is certified.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 2.1 | `scan_full_consumption` (categoryCapstone) | [`ScanStrictCoupling`](../L4YAML/Proofs/Scanner/ScanStrictCoupling.lean) | ✅ |
| 2.2 | `scan_produces_valid_tokens` | [`ScannerCorrectness`](../L4YAML/Proofs/Scanner/ScannerCorrectness.lean) | ✅ |
| 2.3 | `advance_offset_lt` | [`ScannerProgress`](../L4YAML/Proofs/Scanner/ScannerProgress.lean) | ✅ |
| 2.4 | `scanLoop_success_emits_streamEnd` | `ScannerCorrectness` | ✅ |
| 2.5 | `scanNextToken_preserves_bound` | [`ScannerBound`](../L4YAML/Proofs/Scanner/ScannerBound.lean) | ✅ |
| 2.6 | `advance_preserves_wellFormed` | [`ScannerLoopInvariant`](../L4YAML/Proofs/Scanner/ScannerLoopInvariant.lean) | ✅ |
| 2.7 | Simple-key lifecycle: `saveSimpleKey_*`, `scanKey`, `scanValue` preserve `WellFormed` | [`ScannerSimpleKey`](../L4YAML/Proofs/Scanner/ScannerSimpleKey.lean) | ✅ |
| 2.8 | Dispatch preservation: `scanNextToken` branches preserve `WellFormed` (repr `with_needIndentCheck_preserves_wellFormed`) | [`ScannerDispatch`](../L4YAML/Proofs/Scanner/ScannerDispatch.lean) | ✅ |
| 2.9 | Document-marker WF: `scanDirective`, `scanDocumentStart`, `scanDocumentEnd` preserve `WellFormed` (repr `with_docStart_flags_preserves_wellFormed`) | [`ScannerDocument`](../L4YAML/Proofs/Scanner/ScannerDocument.lean) | ✅ |

**Depends on**: surface coupling (Group 8).

**Change since April**: 2.2 was 🚧 (3 `sorry`s); it is now ✅ —
`ScannerCorrectness.lean` is `sorry`-free.

**Significance & risk**

- **2.1 `scan_full_consumption`** — *Significance:* the scanner
  consumes the entire input; a successful scan leaves no trailing
  bytes silently discarded. *Risk if absent:* truncated reads
  accepted as success — a classic parser-differential / request-smuggling
  vector where two implementations disagree on where the document ends.
- **2.2 `scan_produces_valid_tokens`** — *Significance:* every token
  the scanner emits is structurally well-formed, so the parser never
  sees garbage. *Risk if absent:* malformed tokens reach the parser →
  crashes, panics, or a nonsense AST from valid-looking input.
- **2.3 `advance_offset_lt`** — *Significance:* each step strictly
  advances the input offset, which certifies scanner **termination**.
  *Risk if absent:* adversarial input could hang the scanner — a
  denial-of-service on any service that parses untrusted YAML.
- **2.4 `scanLoop_success_emits_streamEnd`** — *Significance:* a
  successful scan is properly framed with a terminating `streamEnd`
  token. *Risk if absent:* the parser could read past the end or
  mis-frame document boundaries.
- **2.5 `scanNextToken_preserves_bound`** — *Significance:* the
  in-bounds invariant on the scanner's cursor is preserved at every
  step. *Risk if absent:* out-of-bounds indexing — a memory-safety
  fault once the core is driven through the C/Rust FFI.
- **2.6 `advance_preserves_wellFormed`** — *Significance:* the
  scanner-state invariant survives each `advance`, so all later
  step-level reasoning is sound. *Risk if absent:* one broken step
  invalidates every invariant that depends on it downstream.
- **2.7 simple-key lifecycle** — *Significance:* YAML's simple-key
  machinery (the lookahead that decides whether `foo:` is a key)
  preserves well-formedness across save/promote/scan. *Risk if
  absent:* mis-scanned keys silently reshape a mapping — a
  content-corruption bug in exactly YAML's most notoriously subtle
  area.
- **2.8 dispatch preservation** — *Significance:* *every* branch of
  the main token dispatcher preserves the state invariant. *Risk if
  absent:* the invariant is only as strong as its weakest branch —
  one unguarded case would let corruption in on specific inputs.
- **2.9 document-marker WF** — *Significance:* `---`, `...`, and
  directives preserve the invariant, so multi-document streams split
  correctly. *Risk if absent:* documents mis-merged or mis-split —
  wrong data delivered from a multi-doc stream.

---

## Group 3 — Parser correctness

Syntactic-layer guarantees: parser output corresponds to a valid
grammar derivation; anchors grow; aliases resolve; anchors are
well-formed.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 3.1 | `parseStream_respects_grammar_unconditional` (headline) | [`EndToEndCorrectness`](../L4YAML/Proofs/EndToEndCorrectness.lean) | ✅ |
| 3.2 | `parseStream_sound` | [`ParserSoundness`](../L4YAML/Proofs/Parser/ParserSoundness.lean) | ✅ |
| 3.3 | `yamlValue_has_witness` (mutual recursion with `Classical.choice`) | `ParserSoundness` | ✅ |
| 3.4 | `parseNode_anchors_grow` | [`ParserAnchorProofs`](../L4YAML/Proofs/Parser/ParserAnchorProofs.lean) / [`ParserNodeProofs`](../L4YAML/Proofs/Parser/ParserNodeProofs.lean) | ✅ |
| 3.5 | `parseNode_aliases_resolve` (public wrapper over `ParserNodeProofs.parseNode_aliases_resolve'`) | [`ParserAnchorProofs`](../L4YAML/Proofs/Parser/ParserAnchorProofs.lean) | ✅ |
| 3.6 | `parseDocument_aliases_resolve` | `ParserAnchorProofs` | ✅ |
| 3.7 | `parseStream_output_aliases_resolve` | `ParserAnchorProofs` | ✅ |
| 3.8 | `parseStream_output_anchors_wellformed` | [`ParserWfaProofs`](../L4YAML/Proofs/Parser/ParserWfaProofs.lean) | ✅ |
| 3.9 | `parseStream_output_grammable` | [`ParserGrammable`](../L4YAML/Proofs/Parser/ParserGrammable.lean) | ✅ |
| 3.10 | `parseYaml_produces_valid_nodes` | `ParserGrammable` | ✅ |
| 3.11 | `parseStream_respects_grammar` | [`ParserCorrectness`](../L4YAML/Proofs/Parser/ParserCorrectness.lean) | 🧩 (conditional) |
| 3.12 | `grammar_value_roundtrip` (completeness direction) | [`ParserCompleteness`](../L4YAML/Proofs/Parser/ParserCompleteness.lean) | ✅ (noncomputable) |
| 3.13 | `parseStream_complete` | `ParserCompleteness` | ✅ (noncomputable, conditional on grammability) |
| 3.14 | `soundness_completeness_compose` | `ParserCompleteness` | ✅ |

**Depends on**: Group 2 (scanner). The "unconditional" suffix
(theorem 3.1) means the grammability hypothesis has been discharged
via Group 3.9.

**Significance & risk**

- **3.1 `parseStream_respects_grammar_unconditional`** *(headline)* —
  *Significance:* every AST the parser produces corresponds to an
  actual derivation in the written YAML 1.2.2 grammar — and
  unconditionally, because 3.9 discharges the grammability side
  condition. *Risk if absent:* the parser could manufacture ASTs with
  no grammatical basis, accepting structures the spec forbids and
  diverging from every conformant implementation.
- **3.2 `parseStream_sound`** — *Significance:* soundness stated at
  the token-stream level, the workhorse behind 3.1. *Risk if absent:*
  no bridge from token stream to grammar derivation.
- **3.3 `yamlValue_has_witness`** — *Significance:* every produced
  value carries an explicit derivation witness. *Risk if absent:*
  "valid" values that cannot actually be derived — soundness in name
  only.
- **3.4 `parseNode_anchors_grow`** — *Significance:* the anchor
  environment only ever grows as parsing proceeds. *Risk if absent:*
  anchor-scoping bugs where a later definition shadows or drops an
  earlier one, corrupting alias resolution.
- **3.5 `parseNode_aliases_resolve`** — *Significance:* every `*alias`
  resolves to a previously defined `&anchor`. *Risk if absent:*
  dangling aliases resolving to undefined or arbitrary nodes —
  crashes, or a data-injection primitive.
- **3.6 / 3.7 doc- and stream-level alias resolution** —
  *Significance:* lifts alias soundness to whole documents and
  multi-document streams. *Risk if absent:* cross-document alias
  leakage — an anchor in one document silently satisfying an alias in
  another.
- **3.8 `parseStream_output_anchors_wellformed`** — *Significance:*
  the resolved anchor graph is well-formed. *Risk if absent:* a
  malformed anchor graph that later stages trust and mishandle.
- **3.9 `parseStream_output_grammable`** — *Significance:* parser
  output is always grammable, which is precisely what upgrades 3.11
  into the unconditional 3.1. *Risk if absent:* the headline
  guarantee stays hypothesis-gated — i.e. not actually established.
- **3.10 `parseYaml_produces_valid_nodes`** — *Significance:* the
  user-facing statement that `parseYaml` yields valid nodes. *Risk if
  absent:* consumers cannot trust the shape of the AST they receive.
- **3.11 `parseStream_respects_grammar`** — *Significance:* the
  hypothesis-gated precursor to 3.1, retained for its fibration /
  witness structure. Marked 🧩 because it *takes* a grammability
  hypothesis by design — **it contains no `sorry`** and is subsumed
  by 3.1. *Risk if absent:* 3.1 loses the intermediate it is built
  from.
- **3.12 `grammar_value_roundtrip`** — *Significance:* the
  completeness direction — every grammar-valid value round-trips
  through the parser (noncomputable, via `Classical.choice`). *Risk
  if absent:* the parser could reject structures the grammar permits.
- **3.13 `parseStream_complete`** — *Significance:* completeness —
  well-formed token streams parse successfully. *Risk if absent:*
  false rejections of valid YAML, an availability/interop failure as
  damaging as wrong output.
- **3.14 `soundness_completeness_compose`** — *Significance:* packages
  both directions into one statement. *Risk if absent:* no single
  handle on the sound-and-complete guarantee for downstream capstones.

---

## Group 4 — End-to-end correctness

Top-level guarantees on `parseYaml`. These are the public promises.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 4.1 | `parse_sound_shallow` (headline) — soundness: `parse s = .ok docs → ValidYamlProp s docs` | [`EndToEndCorrectness`](../L4YAML/Proofs/EndToEndCorrectness.lean) | ✅ |
| 4.1d | `parse_sound_deep` (headline) — soundness with explicit pipeline fibration and `ValidNode` witness | `EndToEndCorrectness` | ✅ |
| 4.2 | `parse_complete` (headline) — completeness: `ValidYamlProp s docs → parse s = .ok docs` | `EndToEndCorrectness` | ✅ |
| 4.3 | `parse_deterministic` (headline) — `parse` is a function | `EndToEndCorrectness` | ✅ |
| 4.4 | `parseYaml_implies_valid_token_stream` (bridge to Group 2) | `EndToEndCorrectness` | ✅ |

**Depends on**: Groups 1–3.

**Significance & risk**

- **4.1 `parse_sound_shallow`** *(headline)* — *Significance:* the
  core promise — if `parseYaml` returns `.ok docs`, then `docs` is a
  well-formed data model of the input. This is what makes "the parse
  succeeded" *mean* something. *Risk if absent:* success would carry
  no guarantee about the output at all; every consumer would have to
  re-validate the AST itself.
- **4.1d `parse_sound_deep`** *(headline)* — *Significance:*
  strengthens 4.1 to certify that *every* pipeline stage succeeded and
  produced a grammar-valid node, with an explicit fibration witness.
  *Risk if absent:* shallow soundness could hold while an internal
  stage quietly cut a corner — deep soundness rules out that fibration
  gap.
- **4.2 `parse_complete`** *(headline)* — *Significance:* every
  well-formed input is accepted; the parser never rejects valid YAML.
  *Risk if absent:* silent rejection of legitimate documents — a
  reliability failure for config loaders and data pipelines.
- **4.3 `parse_deterministic`** *(headline)* — *Significance:* `parse`
  is a genuine function: one input, one output. *Risk if absent:*
  nondeterministic parses — the same file yielding different results
  across runs or platforms, which is catastrophic for reproducible
  builds, configuration management, and flight-software determinism.
- **4.4 `parseYaml_implies_valid_token_stream`** — *Significance:*
  connects the top-level API back to the scanner-level guarantees of
  Group 2. *Risk if absent:* the end-to-end and lexical guarantees
  would be two disconnected islands.

---

## Group 5 — Value semantics (soundness at the runtime-value level)

The AST-to-value conversion faithfully implements the Core Schema.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 5.1 | `validYaml_construct` (headline) | [`Soundness`](../L4YAML/Proofs/Soundness.lean) | ✅ |
| 5.2 | `toYamlValue_correct` | `Soundness` | ✅ |
| 5.3 | `nodeToValue_total` | `Soundness` | ✅ |
| 5.4 | `nodeToValue_deterministic` | `Soundness` | ✅ |
| 5.5 | `scalar_content_preserved` | `Soundness` | ✅ |
| 5.6 | `isNull_*`, `isBool_*`, `isInt_*`, `isFloat_*` correctness (§10.3) | [`SchemaResolution`](../L4YAML/Proofs/Schema/SchemaResolution.lean) | ✅ |
| 5.7 | `resolveImplicit_complete` | `SchemaResolution` | ✅ |

**Depends on**: Group 3 (parser correctness).

**Change since April**: 5.2 was 🚧 (1 `sorry`); it is now ✅ —
`Soundness.lean` is `sorry`-free.

**Significance & risk**

- **5.1 `validYaml_construct`** *(headline)* — *Significance:* every
  successful parse produces a `ValidYaml` runtime value, so FFI
  consumers (C/Python/Rust) receive a value that satisfies the
  library's invariants. *Risk if absent:* downstream code could
  consume an "invalid" value → undefined behavior across the language
  bindings.
- **5.2 `toYamlValue_correct`** — *Significance:* the AST→value
  conversion is faithful — the value the application sees equals the
  document that was parsed. *Risk if absent:* silent data corruption
  at the schema boundary, where the bytes parse fine but the delivered
  value is wrong.
- **5.3 `nodeToValue_total`** — *Significance:* the conversion is
  total — it never crashes on an accepted node. *Risk if absent:*
  panics on some inputs that the parser happily accepted.
- **5.4 `nodeToValue_deterministic`** — *Significance:* one node
  converts to one value. *Risk if absent:* the same AST yielding
  different runtime values — nondeterminism re-introduced below the
  parser.
- **5.5 `scalar_content_preserved`** — *Significance:* scalar text is
  carried through conversion unaltered. *Risk if absent:* scalar
  mutation — content quietly changed between parse and use.
- **5.6 §10.3 implicit-type correctness** — *Significance:* `null →
  bool → int → float → str` resolution follows the spec's precedence
  exactly. *Risk if absent:* type confusion — the infamous YAML
  footguns (`yes`/`no` as booleans, the "Norway problem", `1.0` vs
  `"1.0"`) resolving against the spec rather than as ad-hoc surprises.
- **5.7 `resolveImplicit_complete`** — *Significance:* the implicit
  resolver is complete over the Core Schema tag set — every scalar
  gets a resolution. *Risk if absent:* unresolved scalars falling
  through into an undefined state.

---

## Group 6 — Round-trip properties  *(work-remaining frontier)*

`parseYaml ∘ emit` and `parseYaml ∘ dump` recover content-equivalent
values.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 6.1 | `universal_roundtrip` (headline) | [`EmitterScannability`](../L4YAML/Proofs/Output/EmitterScannability.lean) | 🚧 (5 `sorry`s) |
| 6.2 | `contentEq_refl` | [`RoundTrip`](../L4YAML/Proofs/RoundTrip/RoundTrip.lean) | ✅ |
| 6.3 | `contentEq_symm` | `RoundTrip` | ✅ |
| 6.4 | `contentEq_trans` | `RoundTrip` | ✅ |
| 6.5 | `emit_content_invariant` | [`ScannerEmitBridge`](../L4YAML/Proofs/Output/ScannerEmitBridge.lean) | ✅ |
| 6.6 | `escapeTag_roundtrip` | `RoundTrip` | ✅ |
| 6.7 | `resolve_eq_of_resolveEq` (mutual) | [`RoundTripComposition`](../L4YAML/Proofs/RoundTrip/RoundTripComposition.lean) | ✅ |
| 6.8 | `resolve_eq_of_contentEq_noTags` | `RoundTripComposition` | ✅ |
| 6.9 | `emit_roundtrip_content_eq` (canonical-emitter closure) | `EmitterScannability` | 🚧 (residual: the 5 `sorry`s) |
| 6.10 | `universal_roundtrip` — `∀ v, Grammable v false → ∃ docs, parseYaml (emit v) = .ok docs ∧ docs.size = 1 ∧ contentEq v docs[0]!.value = true` | `EmitterScannability` | 🚧 (now **declared** as 6.1; formerly aspirational) |
| 6.11 | `dumpTyped_*`, `contentRoundTrips_*` | [`SchemaDump`](../L4YAML/Proofs/Schema/SchemaDump.lean), [`DumpRoundTrip`](../L4YAML/Proofs/Output/DumpRoundTrip.lean) | ✅ for concrete instances |
| 6.12 | `resolve_toYaml_*`, `fromYaml_toYaml_*` type round-trips | [`SchemaComposition`](../L4YAML/Proofs/Schema/SchemaComposition.lean) | ✅ for concrete instances |
| 6.13 | `emit_parse_succeeds` — emitter output parses via `parseYamlRaw` (existence half of 6.10) | `EmitterScannability` | 🚧 (sorry-reachable via 6.9) |
| 6.14 | `emit_parseYaml_succeeds` — emitter output parses via `parseYaml` (existence half of 6.10, composed) | `EmitterScannability` | 🚧 (sorry-reachable via 6.9) |

**The gap (2026-07-01)**: capstone 6.1/6.10 `universal_roundtrip` is
now a **declared** theorem (`EmitterScannability.lean:1285`), but its
proof is `sorry`-reachable through 6.9's canonical-emitter closure.
The residual was exactly the **two `sorry`s** of the 2026-07-03 snapshot
(both now closed by the general-locality chain above),
split into two independent tracks:

- **Track A — `FlowSubrangesOk`** (every balanced flow subrange is
  well-formed), consumed by the sequence and mapping structure proofs
  (sites 1, 2). All of Track A bottoms out at the single R447
  navigator `seqBody_recseqbody_provider` (site 3, the **linchpin**);
  the assembler chain that lifts it to `FlowSubrangesOk` is already
  verified and waiting.
- **Track B — `parseNode` span-locality** (sites 4, 5): the parser's
  value output depends only on the tokens forward of its start
  position, for the non-all-scalar flow collections. The all-scalar
  branch already closes by canonical form.

**Depends on**: Group 4 (parse), Group 5 (values).

**Significance & risk**

- **6.1 / 6.10 `universal_roundtrip`** *(headline, 🚧)* —
  *Significance:* emitting any grammable value and re-parsing it
  recovers a content-equivalent value — the left-inverse law that
  makes the dumper trustworthy for read-modify-write workflows. *Risk
  if absent:* the dumper could silently produce YAML that re-parses to
  something different — a configuration file written back would not
  equal the one read in. **This is the single most consequential open
  guarantee**; until it closes, round-trip safety holds only for the
  scalar/all-scalar shapes and is `sorry`-gated for nested flow
  collections.
- **6.2–6.4 `contentEq` refl / symm / trans** — *Significance:*
  content-equivalence is a genuine equivalence relation, which is what
  gives "same content" a sound meaning. *Risk if absent:* every
  round-trip statement phrased in terms of `contentEq` would rest on
  an ill-defined notion.
- **6.5 `emit_content_invariant`** — *Significance:* `emit` preserves
  content — the emitter side of the round-trip. *Risk if absent:* the
  dumper could drop or alter content before parsing even enters the
  picture.
- **6.6 `escapeTag_roundtrip`** — *Significance:* tag escaping
  survives a round-trip. *Risk if absent:* explicit tags corrupted on
  dump — type information lost across a save.
- **6.7 / 6.8 `resolve_eq_*`** — *Significance:* alias resolution is
  stable under content-equivalence. *Risk if absent:* round-trip would
  break precisely on anchored/aliased documents.
- **6.9 `emit_roundtrip_content_eq`** *(🚧)* — *Significance:* the
  value-level canonical-emitter closure that 6.1 is built on; its
  residual *is* the five `sorry`s. *Risk if absent:* the closure gap
  means round-trip is proved only for leaf shapes, not for nested flow
  structure.
- **6.11 `dumpTyped_*` / `contentRoundTrips_*`** *(✅ concrete)* —
  *Significance:* typed dump-then-load round-trips for concrete types.
  *Risk if absent:* a derived `ToYaml`/`FromYaml` pair could fail to
  be mutually inverse for a specific type.
- **6.12 type round-trips** *(✅ concrete)* — *Significance:*
  `fromYaml ∘ toYaml = id` for concrete instances. *Risk if absent:*
  serialization could silently lose fields on the typed API.
- **6.13 / 6.14 `emit_parse_succeeds` / `emit_parseYaml_succeeds`**
  *(🚧)* — *Significance:* the existence half — emitter output at
  least *parses* (before asking whether it parses to the same
  content). *Risk if absent:* the dumper could emit YAML that no
  parser, including our own, accepts.

---

## Group 7 — Grammar-production derivations & acceptance strictness

Decomposes every scanner/parser acceptance as a full YAML 1.2.2
grammar derivation tree — the structural, strongest form of Group 2.2.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 7.1 | `parse_strict_proof` (headline) — parser acceptance implies `InYamlLanguage input` | [`DocumentProduction`](../L4YAML/Proofs/Production/DocumentProduction.lean) | ✅ |
| 7.2 | `scan_content_gives_stream_v2` (full SLYamlStream derivation) | [`StreamAccum`](../L4YAML/Proofs/Production/StreamAccum.lean) | ✅ |
| 7.3 | `scanLoop_grammar_prod` | `StreamAccum` | ✅ |
| 7.4 | Per-function `*_prod` theorems (flow/block/document start/end, anchor/alias, tag, directive) | [`StructureProduction`](../L4YAML/Proofs/Production/StructureProduction.lean) / [`DocumentProduction`](../L4YAML/Proofs/Production/DocumentProduction.lean) / [`ScalarProduction`](../L4YAML/Proofs/Production/ScalarProduction.lean) / [`NodeProduction`](../L4YAML/Proofs/Production/NodeProduction.lean) | ✅ |
| 7.5 | `parseYaml_implies_valid_token_stream` (bridge to Group 4) | `EndToEndCorrectness` | ✅ |
| 7.6 | `scan_strict_proof` — scanner acceptance implies `InYamlLanguage input` | `DocumentProduction` | ✅ |
| 7.7 | `parse_iff_grammar` **converse** — grammar completeness: `InYamlLanguage input → ∃ docs, parseYaml input = .ok docs` (closes the biconditional) | (target: `Production` / `Completeness`) | ⏳ not started |

**Change since April**: the whole forward direction (7.1–7.6) is now
✅. The "28 `sorry`s in `StreamAccum`" reported in April were docstring
artifacts, not tactics — `StreamAccum.lean` builds clean. `parse_strict_proof`
and `scan_strict_proof` were proved in v0.4.6.

**Note**: Group 7 is the *strongest* form of scanner/parser
correctness — not "output is well-formed" but "acceptance *is* a
specific derivation tree in the YAML 1.2.2 grammar."

**Depends on**: Group 2 (scanner), Group 8 (coupling).

**Significance & risk**

- **7.1 `parse_strict_proof`** *(headline, ✅)* — *Significance:*
  parser acceptance implies the input is in the formalized YAML
  language `InYamlLanguage` — we never accept a string outside the
  spec's surface language. *Risk if absent:* over-acceptance —
  accepting inputs that other conformant parsers reject, an interop
  and security divergence (the input means one thing to us, another to
  the next tool in the chain).
- **7.2 `scan_content_gives_stream_v2`** *(✅)* — *Significance:*
  scanned content is backed by a full `SLYamlStream` derivation, not
  just a well-formedness flag. *Risk if absent:* scanner acceptance
  with no grammatical justification.
- **7.3 `scanLoop_grammar_prod`** *(✅)* — *Significance:* the scan
  loop itself produces a grammar derivation at each step. *Risk if
  absent:* a hole in the middle of the derivation chain.
- **7.4 per-function `*_prod`** *(✅)* — *Significance:* each concrete
  construct (flow/block collections, document markers, anchors,
  aliases, tags, directives) maps to its named YAML 1.2.2 production.
  *Risk if absent:* individual constructs accepted with no spec
  production behind them.
- **7.5 `parseYaml_implies_valid_token_stream`** *(✅)* —
  *Significance:* carries strictness up to the top-level API. *Risk if
  absent:* the strictness result would not reach `parseYaml`.
- **7.6 `scan_strict_proof`** *(✅)* — *Significance:* the same
  strictness at the scanner level. *Risk if absent:* the scanner could
  admit non-language strings that the parser then trusts.
- **7.7 `parse_iff_grammar` converse** *(⏳ not started)* —
  *Significance:* the missing half of the biconditional — every string
  in the YAML language *is* accepted. Together with 7.1 it would prove
  the parser accepts **exactly** the language, no more and no less —
  the gold-standard parser-correctness statement. Requires first
  removing the two over-approximation constructors (`directiveDrop`,
  `scannerDrop`) that currently make `InYamlLanguage` strictly weaker
  than "parseable" ([`VERSION-0.4.8.md`](../VERSION-0.4.8.md)). *Risk
  if absent:* we have proved we do not *over*-accept (7.1) but not that
  we accept the *whole* language — a future scanner/parser refactor
  could silently narrow the set of accepted YAML and no proof would
  catch the regression.

---

## Group 8 — Surface coupling (character ↔ implementation)

Shows every scanner step's character-level behavior matches a
surface-syntax predicate.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 8.1 | `SIndent_*`, `GChar_*` character-level predicates (categoryCapstone; repr `SIndent_zero`) | [`SurfaceCoupling`](../L4YAML/Proofs/Coupling/SurfaceCoupling.lean) | ✅ |
| 8.2 | `scanFlowSequenceStart_corr`, `scanFlowSequenceEnd_corr`, `scanFlowMappingStart_corr`, `scanFlowMappingEnd_corr` | [`StructureCoupling`](../L4YAML/Proofs/Coupling/StructureCoupling.lean) | ✅ |
| 8.3 | `scanDirective_corr`, `scanAnchorOrAlias_corr`, `scanTag_corr` | `StructureCoupling` | ✅ |
| 8.4 | `scanBlockScalar_corr`, `collectDoubleQuotedLoop_corr`, `collectPlainScalarLoop_corr` | [`ScalarCoupling`](../L4YAML/Proofs/Coupling/ScalarCoupling.lean) | ✅ |
| 8.5 | `skipSpacesLoop_corr`, `consumeNewline` coupling | [`ScannerCoupling`](../L4YAML/Proofs/Coupling/ScannerCoupling.lean) | ✅ |

**Role**: the "bridge from characters to tokens" theorems — the
conscience of the scanner. `CouplingBridge.lean` (not a capstone row)
belongs to the same cluster.

**Significance & risk**

- **8.1 character-level predicates** *(categoryCapstone)* —
  *Significance:* the scanner's raw character handling (indentation
  counting, character-class legality) matches the surface-syntax
  predicates the grammar is stated over. *Risk if absent:* the
  foundation the entire strictness story (Group 7) rests on could
  drift from the spec — every higher guarantee would be built on sand.
- **8.2 flow-indicator coupling** — *Significance:* the `[`, `]`, `{`,
  `}` scanners behave exactly as their surface predicates say. *Risk
  if absent:* flow-collection framing bugs — mis-detected brackets
  reshaping structure.
- **8.3 directive / anchor / tag coupling** — *Significance:*
  node-property scanning matches the surface grammar. *Risk if
  absent:* anchors, aliases, or tags mis-scanned at the character
  level.
- **8.4 scalar-body coupling** — *Significance:* block, double-quoted,
  and plain scalar collection match their predicates — the most
  content-bearing scanners. *Risk if absent:* scalar-content drift,
  i.e. the actual data getting mis-read.
- **8.5 whitespace / newline coupling** — *Significance:* space
  skipping and newline consumption match the grammar. *Risk if
  absent:* whitespace/indentation handling drift — the root of most
  real-world YAML bugs.

---

## Decomposition: what is *not* a capstone

The following are **infrastructure**, not capstones. They exist to
support the theorems above and should be deletable if unused.

**Resolved since April 2026**: the `parser_fuel_mono_succ`
fuel-monotonicity machinery and its ~24 sub-theorems
(`_mono_step`, `_mono_zero`, `Parse*_succ`), together with
`parseNode_fuel_mono_succ`, `parseSinglePairMapping_fuel_mono_succ`,
the `parseEntry_in_flowMap` cluster, and `flow_parser_ok_of_structure`,
have been **deleted** (~3,200 LoC, all sorries removed) — a
`unified-dep-table --external-only` run proved zero out-of-namespace
callers. `grep -rn parser_fuel_mono_succ L4YAML/Proofs` now returns
nothing. This closes the deletion backlog that motivated the
blueprint and validates its founding observation: theorems were being
accumulated without a top-down anchor. See
[`VERSION-0.4.7.md`](../VERSION-0.4.7.md).

Still-standing infrastructure, kept because it genuinely contributes:

- All `_ag`, `_aar`, `_wfa` per-function lemmas in
  `ParserNodeProofs`, `ParserAnchorProofs`, `ParserWfaProofs` — the
  mutual-induction scaffolding for capstones 3.4, 3.5, 3.8. Keep.
- The `FlowSubrangesOk` assembler chain and the R447 navigator bricks
  in the `EmitterScannability/` subcluster — scaffolding for the open
  Group 6.1 round-trip. Kept, in active use.

---

## Adversarial-instantiation coverage

**Which capstones have a computational-check test in
[`Tests/AdversarialInstantiation.lean`](../Tests/AdversarialInstantiation.lean)?**

> ⚠ **This table reflects the April-2026 audit and needs its own
> re-run.** The fuel-monotonicity rows below (Priority 7) are now moot
> — that machinery was deleted (see above). The remaining rows are
> believed current but should be re-verified against the present test
> file before being relied on.

| Priority | Coverage | Capstones exercised |
| -------- | -------- | ------------------- |
| 1 | 9g, 9h filtered characterization | 6.9 partial |
| 2 | 9c, 9d emit round-trip content-eq | 6.5, 6.9 |
| 3 | 9a, 9b parser fuel sufficiency | 4.1 (indirect) |
| 4 | 9e scanner prefix invariant | 2.2, 8.* |
| 5 | BoundInv preservation | 2.5 |
| 6 | ScanChain_filtered_prefix, flow-parser helpers | 2.*, 3.* |
| ~~7~~ | ~~`handleBlockMappingKeyEntry_mono_step`~~ | ~~*no capstone*~~ — **removed with the fuel-mono deletion** |

**Gaps** (adversarial coverage worth adding, in priority order):
- No adversarial coverage for Group 4 (end-to-end) as a whole.
- No adversarial coverage for Group 5 (value semantics).
- Group 6.1 (`universal_roundtrip`): partial via Priorities 1–2; the
  non-all-scalar flow branches (the five open `sorry`s) are the
  natural next fixtures — see
  [`Tests/Reflections/NonAllScalarLocality.lean`](../Tests/Reflections/NonAllScalarLocality.lean).
- Group 7.7 (grammar completeness): none yet — natural, since the
  converse is not yet declared.

The discipline (adversarial instantiation *before* proof) is spelled
out in [`06-discipline.md`](06-discipline.md); it is what would have
caught the fuel-monotonicity unsoundness before it was written.
