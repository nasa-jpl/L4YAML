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
  [`README.md`](README.md); the full audit trail is in the retired
  `VERSION-0.4.7.md` campaign record, recoverable from git history).
- `StreamAccum.lean`'s "28 sorries" were **docstring artifacts**
  (narrative mentions of `sorry'd`), not tactics; the file builds
  clean.
- Group 2.2, 5.2, and all of Group 7's forward direction have
  **closed** since April.

**One converse theorem remains open** — it is the entire
work-remaining frontier:

1. **Grammar completeness** (Group 7.7, `parse_iff_grammar` converse)
   — **not yet declared**; blocked on removing the remaining
   over-approximation grammar constructor (`scannerDrop`;
   `directiveDrop` was removed by the Fix-B campaign on 2026-08-02)
   ([`DOCS.md` § Grammar completeness plan](../DOCS.md#grammar-completeness-plan)).
   *We accept **exactly** the YAML language, not merely a subset of
   well-formed inputs.*

**Universal round-trip** (Group 6.1, `universal_roundtrip`) closed on
2026-07-04 via Track B above — *emit-then-parse recovers content* is
now fully machine-checked (see the Group 6 tables below).

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
promoted from 🚧 to ✅ since April (2.2, 5.2, 7.1–7.6, and the Group-6
closure rows 6.1/6.9/6.10/6.13/6.14 flipped 2026-07-31) need matching
catalogue annotations — a follow-up tagging task, flagged in
[`README.md`](README.md) Initiative 2. In-repo, the same set is now
also marked at the declaration site via the `@[capstone]` attribute
and pinned in [`L4YAML/Capstones.lean`](../L4YAML/Capstones.lean).

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
| 3.5 | `parseNode_aliases_declared` (public wrapper over `ParserNodeProofs.parseNode_aliases_declared'`; indexed on the declaration set, YAML §7.1 — `parseNode_aliases_resolve` is the derived resolution reading under `DeclarationsBound`) | [`ParserAnchorProofs`](../L4YAML/Proofs/Parser/ParserAnchorProofs.lean) | ✅ |
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
- **3.5 `parseNode_aliases_declared`** — *Significance:* every `*alias`
  names an `&anchor` that has already occurred (YAML §7.1). Per node
  only this reading is available: `&x [*x]` is legal, and the anchored
  node's entry in the resolution table cannot exist before the node is
  complete; the resolution reading is derived from it at the document
  boundary (`AllAliasesResolve.of_declared`, rows 3.6/3.7). *Risk if
  absent:* dangling aliases resolving to undefined or arbitrary nodes —
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

## Group 6 — Round-trip properties  *(closed 2026-07-04)*

`parseYaml ∘ emit` and `parseYaml ∘ dump` recover content-equivalent
values.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 6.1 | `universal_roundtrip` (headline) | [`EmitterScannability`](../L4YAML/Proofs/Output/EmitterScannability.lean) | ✅ |
| 6.2 | `contentEq_refl` | [`RoundTrip`](../L4YAML/Proofs/RoundTrip/RoundTrip.lean) | ✅ |
| 6.3 | `contentEq_symm` | `RoundTrip` | ✅ |
| 6.4 | `contentEq_trans` | `RoundTrip` | ✅ |
| 6.5 | `emit_content_invariant` | [`ScannerEmitBridge`](../L4YAML/Proofs/Output/ScannerEmitBridge.lean) | ✅ |
| 6.6 | `escapeTag_roundtrip` | `RoundTrip` | ✅ |
| 6.7 | `resolve_eq_of_resolveEq` (mutual) | [`RoundTripComposition`](../L4YAML/Proofs/RoundTrip/RoundTripComposition.lean) | ✅ |
| 6.8 | `resolve_eq_of_contentEq_noTags` | `RoundTripComposition` | ✅ |
| 6.9 | `emit_roundtrip_content_eq` (canonical-emitter closure) | `EmitterScannability` | ✅ |
| 6.10 | `universal_roundtrip` — `∀ v, Grammable v false → ∃ docs, parseYaml (emit v) = .ok docs ∧ docs.size = 1 ∧ contentEq v docs[0]!.value = true` | `EmitterScannability` | ✅ (= 6.1, full statement) |
| 6.11 | `dumpTyped_*`, `contentRoundTrips_*` | [`SchemaDump`](../L4YAML/Proofs/Schema/SchemaDump.lean), [`DumpRoundTrip`](../L4YAML/Proofs/Output/DumpRoundTrip.lean) | ✅ for concrete instances |
| 6.12 | `resolve_toYaml_*`, `fromYaml_toYaml_*` type round-trips | [`SchemaComposition`](../L4YAML/Proofs/Schema/SchemaComposition.lean) | ✅ for concrete instances |
| 6.13 | `emit_parse_succeeds` — emitter output parses via `parseYamlRaw` (existence half of 6.10) | `EmitterScannability` | ✅ |
| 6.14 | `emit_parseYaml_succeeds` — emitter output parses via `parseYaml` (existence half of 6.10, composed) | `EmitterScannability` | ✅ |
| 6.15 | `canonical_roundtrip_conditional` — scanner-bridge round-trip, conditional form | [`ScannerEmitBridge`](../L4YAML/Proofs/Output/ScannerEmitBridge.lean) | ✅ |

**Closure (2026-07-04)**: capstone 6.1/6.10 `universal_roundtrip` is
fully machine-checked (`EmitterScannability.lean:1539`, no `sorryAx`
anywhere on the closed path — see the Status snapshot at the top).
The former residual split into two independent tracks, both closed:

- **Track A — `FlowSubrangesOk`** (every balanced flow subrange is
  well-formed): closed 2026-07-03 by the deep-family positional
  navigator (`DeepNavigator.lean`), which reads per-window body
  properties directly off the stored pair structure — no
  interior-separator carrier on the closed path.
- **Track B — `parseNode` span-locality** (the parser's value output
  depends only on the tokens forward of its start position, for
  non-all-scalar flow collections): closed 2026-07-04 by the
  general-locality chain (`TokVals`, `TokValsPin`, `ValueLocality`,
  `ValuePurity`, `StreamNodeWitness`, `GeneralLocality`).

**Depends on**: Group 4 (parse), Group 5 (values).

**Significance & risk**

- **6.1 / 6.10 `universal_roundtrip`** *(headline, ✅)* —
  *Significance:* emitting any grammable value and re-parsing it
  recovers a content-equivalent value — the left-inverse law that
  makes the dumper trustworthy for read-modify-write workflows. *Risk
  if absent:* the dumper could silently produce YAML that re-parses to
  something different — a configuration file written back would not
  equal the one read in. **This was the single most consequential
  open guarantee** until its 2026-07-04 closure; round-trip safety now
  covers nested flow collections, not just scalar/all-scalar shapes.
- **`Algebra/Value.lean` §7, `cleaned_resolveAliases_comm` and its helpers** (`Cleaned`, `cleaned_of_pipeline`, `cleaned_table_push`, `stripAnchors_resolveAliases`, `adaptForFlowContext_resolveAliases`) — *Chain (Rule 1, decided 2026-10-22: KEEP):* the specification of `addAnchor`'s clean-then-resolve order (`Parser/State.lean`, `Parser/ParseStateIx.lean`, both docstrings cite it): the stored value equals the one the resolve-then-clean order stored before, so every capstone that reads the anchor table — Group 3/4's `parse_sound_*`/`parse_complete` through `addAnchor_wfaS` and `cleaned_scannable_forall` (restated on the cleaned shape), and 6.1's alias path — holds for the linear-cost order by this lemma rather than by re-proving the table shape. It is a spec lemma, not a dependency of the proof terms: `#print axioms` of the capstones does not list it, and that is the point — the reorder changed the program, not the theorems. *Risk if absent:* the reorder would be a measured speed-up with no statement that the table is the same table.
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
- **6.9 `emit_roundtrip_content_eq`** *(✅)* — *Significance:* the
  value-level canonical-emitter closure that 6.1 is built on. *Risk if
  absent:* round-trip would be proved only for leaf shapes, not for
  nested flow structure.
- **6.11 `dumpTyped_*` / `contentRoundTrips_*`** *(✅ concrete)* —
  *Significance:* typed dump-then-load round-trips for concrete types.
  *Risk if absent:* a derived `ToYaml`/`FromYaml` pair could fail to
  be mutually inverse for a specific type.
- **6.12 type round-trips** *(✅ concrete)* — *Significance:*
  `fromYaml ∘ toYaml = id` for concrete instances. *Risk if absent:*
  serialization could silently lose fields on the typed API.
- **6.13 / 6.14 `emit_parse_succeeds` / `emit_parseYaml_succeeds`**
  *(✅)* — *Significance:* the existence half — emitter output at
  least *parses* (before asking whether it parses to the same
  content). *Risk if absent:* the dumper could emit YAML that no
  parser, including our own, accepts.
- **6.15 `canonical_roundtrip_conditional`** *(✅)* — *Significance:*
  the scanner-bridge round-trip in conditional form — the stepping
  stone between 6.5's emit-side invariance and the unconditional 6.1.
  *Risk if absent:* no bridge-level handle for reasoning about the
  emitter's token stream before the universal closure applies.

---

## Group 7 — Grammar-production derivations & acceptance strictness

Decomposes every scanner/parser acceptance as a full YAML 1.2.2
grammar derivation tree — the structural, strongest form of Group 2.2.

| # | Theorem | Module | Status |
| - | ------- | ------ | ------ |
| 7.1 | `parse_strict_proof` (headline) — parser acceptance implies `InYamlLanguage input`; **vacuous while `scannerDrop` stands** | [`DocumentProduction`](../L4YAML/Proofs/Production/DocumentProduction.lean) | ✅ |
| 7.2 | `scan_content_gives_stream_v2` (full SLYamlStream derivation) — its conclusion is `InYamlLanguage input` spelled out; **vacuous while `scannerDrop` stands** | [`StreamAccum`](../L4YAML/Proofs/Production/StreamAccum.lean) | ✅ |
| 7.3 | `scanLoop_grammar_prod` — statement restrictive, but the derivation it builds **routes through `scannerDrop`** | `StreamAccum` | ✅ |
| 7.4 | Per-function `*_prod` theorems (flow/block/document start/end, anchor/alias, tag, directive) | [`StructureProduction`](../L4YAML/Proofs/Production/StructureProduction.lean) / [`DocumentProduction`](../L4YAML/Proofs/Production/DocumentProduction.lean) / [`ScalarProduction`](../L4YAML/Proofs/Production/ScalarProduction.lean) / [`NodeProduction`](../L4YAML/Proofs/Production/NodeProduction.lean) | ✅ |
| 7.5 | `parseYaml_implies_valid_token_stream` (bridge to Group 4) | `EndToEndCorrectness` | ✅ |
| 7.6 | `scan_strict_proof` — scanner acceptance implies `InYamlLanguage input`; **vacuous while `scannerDrop` stands** | `DocumentProduction` | ✅ |
| 7.7 | `parse_iff_grammar` **converse** — grammar completeness: `InYamlLanguage input → ∃ docs, parseYaml input = .ok docs` (closes the biconditional) | (target: `Production` / `Completeness`); serialization stream S5(→): `L4YAML/Proofs/Serialization/ParseCheckFrom.lean` (`parse_ok_checkFrom`, `parseStream_ok_checkFrom`); S5(←) token side: `StreamCompleteness.parseStream_accepts` over `TokenStateOk ts := SerializationWellFormed (tokenEvents ts)` (slice 2) | ⏳ not started — the serialization stream S5 is complete in both directions: S5(→) slice 1 (`parse_ok_checkFrom`) and S5(←) slice 2 (`parseStream_accepts` over `TokenStateOk := SerializationWellFormed (tokenEvents ts)`); the surface direction (Step 6) is what remains (EVENTSOF-CONCEPT §9 S5) |

**Change since April**: the whole forward direction (7.1–7.6) is now
✅. The "28 `sorry`s in `StreamAccum`" reported in April were docstring
artifacts, not tactics — `StreamAccum.lean` builds clean. `parse_strict_proof`
and `scan_strict_proof` were proved in v0.4.6.

**Note**: Group 7 is the *strongest* form of scanner/parser
correctness — not "output is well-formed" but "acceptance *is* a
specific derivation tree in the YAML 1.2.2 grammar."

**Depends on**: Group 2 (scanner), Group 8 (coupling).

**What Group 7 does not yet establish.** `SLYamlStream.scannerDrop` relates a
source position to a target its premises never connect it to, which makes
`InYamlLanguage` hold of **every** string. 7.1, 7.2 and 7.6 are therefore true
independently of their hypotheses — `inYamlLanguage_everything` discharges all
three statements with the acceptance premise bound and unused
([`SuffixGapAudit.lean`](../Tests/Guards/Proofs/SuffixGapAudit.lean) §5,
[`FreeSurfaceCensus.lean`](../Tests/Guards/Proofs/FreeSurfaceCensus.lean) §2).
The ✅ is accurate: the proofs are real and carry no `sorry`. What they do not
yet carry is a restriction on the input. Seventeen of the library's 103
theorems about the top-level surface are free in this sense and fifteen of them
through that one arm; the count is re-derived at every build by
`FreeSurfaceCensus.lean`, and row 12's β.5 is what turns it into content.

**What β.5 costs Group 7.** Two proofs in the whole library build the arm, and
**twenty-six run through it** — four of Group 7's six ✅ rows among them: 7.2
and 7.3 on the chain, 7.1 and 7.6 at its end
([`DropDependents.lean`](../Tests/Guards/Proofs/DropDependents.lean)). That is a
different reading from the paragraph above: 7.3's statement is restrictive and
not free, and its derivation still rides the arm. Nothing in the library states
the constructor, and a theorem's consumers depend on its statement rather than
its proof, so the twenty-six do not all have to be rewritten — the repair
propagates only where a statement must change, and exactly two are candidates.
Both of the two are candidates because both are FALSE **in the environment that
deletes the arm and keeps `PendingNode.pendingFlow`**, and they are the only
library statements that are
([`DropFalsity.lean`](../Tests/Guards/Proofs/DropFalsity.lean)). `dropClose` is
the arm restated. `PendingNode.close_with_ssl` is restrictive in its
`PendingNode` premise, but restrictive in the scanner state and in nothing that
connects the park's two positions, so a park at a target the suffix law forbids
is buildable — from that park.

**Under β.5's own edit only ONE of the two is a restatement, and that is
measured rather than argued**
([`flip_beta5.py`](../scripts/flip_beta5.py), DOCS item 263). Row 12 retires
`pendingFlow` and deletes `scannerDrop` together, so the park the refutation
builds its witness from is gone with the arm. A flip that applies both
deletions for real and drives the build to a fixpoint leaves
`PendingNode.close_with_ssl` elaborating with its statement AND its proof
unchanged, on its standing axiom profile and no `sorry`. `dropClose` is the one
statement β.5 removes. **Thirteen proofs stop elaborating and not one other
statement in the tree changes** — seven in the library, all in
`Proofs/Production/StreamAccum.lean`, and six in the guard tree.

**What Group 7 actually owes, elaborated rather than forecast.** All four rows
that ride the arm still elaborate against the post-β.5 tree, and all four do so
on `sorryAx`: they are CARRIED by the thirteen proofs above, not free of them
and not restated. Three of the twenty-six come out free outright —
`eof_pending`, `preprocessing_eof_extends_stream` and
`scanNextToken_none_stream` — and the remaining twenty-one, Group 7's four
among them, land exactly when the thirteen land (DOCS item 263).

**Nothing in Group 7 is FALSE, and this is the first measurement that says so.**
All four of Group 7's rows that ride the arm conclude at end of input — 7.1 and
7.6 assert `InYamlLanguage`, 7.2 and 7.3 spell out `∃ sp_final, SLYamlStream …
∧ sp_final.chars = []` — and the law β.5 buys says of such a target only that
`[]` is a suffix of the input, which is true of every string. **β.5 owes Group 7
a reproof and not a restatement.** That is a stronger reading than "no statement
names the constructor": these statements do not contradict the law that replaces
it. It does not say the reproofs are easy — it says they are reproofs.

**Whether they are only reproofs is a CHOICE, and this is its price**
([`RepairChoice.lean`](../Tests/Guards/Proofs/RepairChoice.lean)). β.5 has to
repair `PendingNode.close_with_ssl`, and there are three repairs: a premise
connecting the park's two positions, that same connection as a field on
`PendingNode.pendingFlow`, or retiring that park. The three flips break 5, 1 and
7 definitions and travel three different edges, so the counts are not a ratio.
Only the premise changes `close_with_ssl`'s own type, and it then changes
nineteen statements above it — all four Group 7 rows among them — because no
statement on that closure holds a stream to the park's scan position and the
park provably cannot supply one. The other two change no consumer of
`close_with_ssl`, which is the question asked and not a claim that they are
free: the field repair relocates the connection onto the park's producer,
`block_dispatch_deferred`, which holds a correspondence at the scan position
and cannot derive a path from a point — the library derives a stream from a
`ScannerSurfCorr` at the stream's seed and nowhere else. That producer's own
closure is eighteen declarations, seven of them outside the twenty-six, and it
reaches all four Group 7 rows as well
([`ProducerDerivation.lean`](../Tests/Guards/Proofs/ProducerDerivation.lean)).
**So "not one changed character of a Group 7 statement" is a property of the
repair β.5 picks, and not of Group 7 — and of the two repairs measured
statement by statement, both reach Group 7.**

**And none of that price is the reproofs'**
([`DispatchPrice.lean`](../Tests/Guards/Proofs/DispatchPrice.lean)). The arm
relates a stream ending at one position to an `s-l-comments` starting at an
unrelated one, and identifying the two makes it redundant: `SLYamlStream a b`
and `SSLComments b c` give `SLYamlStream a c` through `implicitContinue` and
`SLDocumentPrefix.comments`, in three lines, and the same three hold in the
relation with the arm deleted. So the four Group 7 rows do not owe a new
grammar lemma — they owe the connection, which is what the nineteen and the
eighteen above are counting. The derivation spends `SSeparateInLine.startOfLine`,
which this library lets hold at every position rather than only at column 0, so
under the spec's own [66] it covers comment runs beginning at a line start.

The same instrument prices what a scanner step buys on its own: 294 statements
hold a dispatch equation, 28 hold one beside two correspondences, and **one**
carries a grammar path across the step. Of 72 distinct scanner step functions,
two carry one at all — preprocessing 6 times of its 186 holders and content
dispatch once of its 129 — and that one precedent is outside the twenty-six and
off both repair threads.

**And the connection is owed per call, not per row**
([`ParkGapCensus.lean`](../Tests/Guards/Proofs/ParkGapCensus.lean)). The arm is
applied at eleven sites, and at none of them are its two endpoints identified —
not syntactically, not up to reduction, not by an equation in scope and not by a
pair of correspondences. Five of the eleven hold a correspondence at the scan
position, all five at the park's own scanner state, and none holds one at the
block position: a park holding both would have absorbed no characters, so the
half that is missing is missing by construction. Six calls owe a span; the
twenty-four owe nothing until a supplier's statement changes.

**And each span is one character**
([`ParkGapWidth.lean`](../Tests/Guards/Proofs/ParkGapWidth.lean)). The gap is
fixed at the park's producer, whose twelve application sites read six at one
scanner step, one at two, and five with no scanner chain reaching the scan
position at all. The one step is a block-indicator dispatch, proved to be
exactly one `ScannerState.advance`, so the production owed is a single `GLit` —
`[184]`, `[190]` or `[6]`. The obligation is a literal, not an induction over a
flow collection. What keeps it unpaid is that the crossed function has
ninety-seven holders and no worked precedent: the one function in the library
that carries a production across a scanner step is at the site whose gap is two.

**And the character has no carrier**
([`ParkGapProduction.lean`](../Tests/Guards/Proofs/ParkGapProduction.lean)). The
six sites' grammar path is one edge of whitespace, so the indicator the dispatch
scans opens a construct rather than closing one. Thirty of the library's two
hundred and thirty-five production constructors end at a literal, twenty-three
of them at one of the three block indicators, and every one of the twenty-three
is a flow form; `-` ends no production at all. Those forms need a frame, and the
park is handed `BlockStack.nil` beside a depth-zero `FlowStackB`, both of which
force their two positions equal. Composed into the grammar's own entry
constructor the literal is premise two of `[183]`'s, whose conclusion ends where
the entry's content ends — so what the six owe is a block node, not a character.

**And the missing arm is honest, and cheap where it is read**
([`CarrierArmPrice.lean`](../Tests/Guards/Proofs/CarrierArmPrice.lean),
[`flip_carrier.py`](../scripts/flip_carrier.py)). The arm that would hold the
park's `-` — `s-indent(n)` then the indicator, `[183]`'s entry with its content
still owed — reaches its target from its source through its own two premises,
the reading under which `scannerDrop` is broken; the same reading over the
proof layer's arms names exactly two escapes, `scannerDrop` and the park
`pendingFlow`, which are the two deletions R3 names. Forty declarations mention
`BlockStack` and twenty-one name its `nil` — eighteen build it, three only read
it; the arm touches none of them. It touches the two absorptions whose match is
total on `nil`, and — both being false once an entry can be open — their five
readers. Two, then five: the carrier's price is where it is read, not where it
is carried.

**And the exits that carry the entry through are the ones that never absorbed it**
([`ExitHandoff.lean`](../Tests/Guards/Proofs/ExitHandoff.lean)). The five
readers and the seventeen builders they reach have sixty-one exits. Fifteen
re-emit the input carrier beside the input stream and carry an open entry
through unchanged — the flow-interior branches, where the carrier is never
absorbed. Forty-three build `nil`, thirty-seven at the input position, and by
position alone fifty-two would read as free; but a `nil` at the input position
is the absorption's residue — its package re-emits the absorbed stream beside
it — and every one of the forty-three hands the content to a route that
promises or demands the stream past it, which an open entry does not supply.
Twenty-six of them sit in fourteen lemmas outside the twenty-seven β.5 owes:
the arm's second wave is inside the bill, its third is not.

**And the promises those exits hand on are carried, not built**
([`RouteShapes.lean`](../Tests/Guards/Proofs/RouteShapes.lean)). The ten parks
carry fifty-four closures promising the stream from `sp_start`, thirty-nine
shapes when each is read as the spine of productions it consumes — the
premise's head with its context and indent shape, and the conclusion's kind —
against six when read by head alone. At the forty-three exits, the parks' two
hundred fifty-five closure slots carry the input park's own promise at one
hundred fifty-four, forward it at eight, punt at eighty-five, and build it from
the absorbed stream at eight, all in the two map openers. Over everything the
five reach, a promise is first built from the absorbed stream in eight lemmas,
at nine constructor slots and eight route hypotheses, and the shapes so built
are ten: threading the arm is ten re-routing lemmas spent where a promise is
first built, and the forty-three exits inherit the result.

**And each promise composes the stream one of fifteen ways**
([`StreamCompositions.lean`](../Tests/Guards/Proofs/StreamCompositions.lean)).
Traced from each producer's body root, the absorbed stream reaches a promise at
twenty-one build points in nine lemmas, the shapes so built are twelve, and the
stream enters the promise's conclusion under fifteen compositions: extended by
a bare document, by comments alone, by a document suffix, by a suffix and a
directive document, by an explicit document, or absorbed by the arm β.5
deletes, each also after an absorption of the block stack, and three of them
stacked where the content dispatcher closes a park and re-extends the closed
stream. Per shape that is twenty-one (shape, composition) pairs, eighteen once
the deleted arm's compositions go with it. The trace also corrects the leaf
reading above at five build points: an `obtain`ed closure, a `cases`-reverted
`have`, and a hypothesis a `subst` carries into a motive whose payload discards
it are what a reading through leaves cannot see.

**And one re-routing lemma covers seven of the eighteen**
([`OpenEntryRoute.lean`](../Tests/Guards/Proofs/OpenEntryRoute.lean)). Eight
of the eighteen pairs compose the stream by a bare document appended at the
landing, and under an open entry that stream does not exist. The twin of the
root route over the entry's closure lands the entry inside the entry's own
node, four constructors and no stream constructor, and needs the side
condition `n + 1 ≤ k` and the slot's comments to the landing in place of the
column and the stream. Read with the closure as the target it enters no
stream constructor, while the closed-first proof, the entry closed empty and
the stream re-derived, reads as the bare document appended, so the failure
mode is detected by the same reading. The twin substitutes at five pairs,
its entries-level twin at two more, and the eighth is a node route no mapping
twin reaches; at the producers it is a new landing arm, since neither opener
holds an open slot closure, threaded through the one funnel both openers
share.

**And the comment closes hold both numbers at eight of thirteen, compared at none**
([`CloseLandingWidth.lean`](../Tests/Guards/Proofs/CloseLandingWidth.lean)).
Six of the eleven pairs the twins leave are closes on comments at eight build
points, six of them through the park's close, whose open-entry arms close the
entry empty at whatever width follows, honest exactly when what follows stands
at the entry's width or left of it. Followed to where they are spent, the
closures are spent thirteen times on the comments and handed on seven times.
The landing's width is in hand at every spend, the park's index is nameable at
eight, and a comparison of the two stands beside none of the spends, only
beside hand-offs: the dedent, and the pack chain under its side condition.
Three build points hold both numbers at every own close and hand-off, four the
width alone, one neither. Of the eighteen empty-node constructors in the
reach, two are the park's own with no width beside them, and a comparison
stands beside four.

**And the eight that hold both numbers split on them beside one, punt on every miss, and the entry park's frames are dropped at the door**
([`CloseSplitFrames.lean`](../Tests/Guards/Proofs/CloseSplitFrames.lean)).
The eight closes feed four lemmas twice each: the landing funnel, the explicit
`:` opener and the two deferred-stamp escapes. The width-against-index decision
the honest close is made of stands beside one of them, the entry park's funnel
spend, where it decides the value-line chain and not the stream; a membership
of the width in a resume stack stands beside the two funnel spends, and each of
those decisions punts on the miss. The content park's lemma holds its resume
stack with the cover two options deep; the entry park's lemma holds none,
because the one producer binds the park's frames field and never hands it
across. The `-` arm's split is disjoint from all eight. The nested arm's
material is in hand at the entry park's four and void at the content park's
four, where the honest arm is the refusal it already pays; the dedent arm's
frame is in hand at the content park's four and dropped at the door at the
entry park's four.

**And the stack the content park's four receive carries a cover that is relayed, never paid, and paid at its one origin only when the funnel's floor is**
([`CloseStackCover.lean`](../Tests/Guards/Proofs/CloseStackCover.lean)).
Every position a cover can be paid at is read off the environment, and every
payment at every application is classified by following the position's type
to its cover option through the term. None of the eight receives a stack whose
cover is paid where the stack is built. All six producers of the content
park's stack forward a cover they were handed, three the entry park's field
and three the props park's entry face, and the tree behind them holds one
literal payment, made inside the landing funnel from the floor the parks pay
when they stand off column 0, and reached only through the mapping value
park, the close-then-block lemma's landed-`-` re-park and the content door.
The entry park's field is punted at six of its seven producers and relayed at
the seventh; the block door drops it and forgets five other cover faces; the
content door keeps all eight. At the eight no fact about the scanner's stack
is in hand, the top only as an upper bound at the entry park's four, and the
floor at none. At the runtime a landing between the open levels is refused as
trailing content.

**And five of the eleven producers that punt a park's stack hold a cover's inputs in full, while the floor any of them can name from its own stack is its own index, except at the root**
([`PuntCoverInputs.lean`](../Tests/Guards/Proofs/PuntCoverInputs.lean)).
The eleven are re-found off the previous walk, which hands every constructor
row its binder stack, and at each the stack is read against the payment's
signature by shape. Five hold monotonicity, the base, the preprocess, the
dispatch and a bound on the top: the compact fill, the content park's sibling
re-park and the entry park's sibling, nested and compact re-parks. The root
`-` lacks monotonicity and holds the seed's empty stack instead; the two
mapping value openers hold the top and lack monotonicity and the base; the
props park's three hold no bound on the top, two of them at index 0 where the
entry face has no witness. Eight can name their own index as a floor, the
root alone can name zero, and three hold a relay's floor beside their own. The
field shapes decide the own-index case: the entry park's frames are all below
its index, so an own-index payment needs no mapping level at the index, which
the top bound and monotonicity do not give, and the runtime accepts a sequence
at its key's own column. A cover floored at the park's own index is spendable
at no dedent width.

**And of the leaves of the two close-stack trees, one turns paid when the four payments in hand are made, and the payment that turns it is the root's**
([`PaidLeafDelta.lean`](../Tests/Guards/Proofs/PaidLeafDelta.lean)).
The previous walk runs unchanged and its four rows are rewritten in place —
the root's as a literal cover at floor zero, the three others as the relays
they would be — and the content and entry trees are re-resolved by the same
resolver under seven scenarios. With all four made, each tree reads two paid
leaves against one, nineteen punts against twenty-one and eighteen, and the
two trees become one component: the sibling re-park's relay forwards the
content park's stack into the entry park's field and closes a cycle. The
root's literal is the one leaf that turns paid and the one new origin; the
three relays turn none, because each forwards a source the trees already
hold — the compact fill's the mapping value park's one literal origin, the
sibling's the content tree's own root, the mapping value content's another
face of the same six producers, which adds two punts of its own. Of the
library's eighty floor witnesses, twelve are the index itself and none is a
closed term below it; the index is raised only by the nine applications of
`mono_index`, one of them on the compact fill's path and none on the mapping
value content's, so the cover that relay forwards into the props park's
entry face stands at that face's own index and is spendable at no dedent
width. The root's price is one parameter, monotonicity, which its caller
binds and it does not; the cover it pays follows from monotonicity and a
negative top in four lines.

**And with the six payments that can be made made, the two close-stack
trees read six paid leaves, fifteen punts and two cover-punts each, as one
component** ([`CloseStackCover.lean`](../Tests/Guards/Proofs/CloseStackCover.lean),
[`PaidLeafDelta.lean`](../Tests/Guards/Proofs/PaidLeafDelta.lean)). The root
`-` pays its resume frames with a literal cover at floor zero, from the seed's
negative top and the stack's monotonicity; the content park's sibling relays
the park's own frames into the entry park's field at the unchanged index; the
compact fill pays its frames with a literal from the slot's own top bound,
floored one column above the slot and below the fill's index, because the
stack it pushes onto is the slot's and no break was crossed; and the entry
park's two re-parks, the inline compact `- - a` and the nested landing
`-⏎  - a`, pay theirs with the same literal from the park's own top bound,
floored one column above the park and below each re-park's index — the
nested landing's bound is the old park's, and it survives the break because
preprocessing's unwind only pops; and the compact opener `- : v` / `- ? k`,
whose slot's own bound is at its index, pays the mapping value park's frames
from what its two callers hold — the stack's monotonicity and a bound below
the slot's index on the state before the dispatch — carried across the
indicator's step, whose opened level the top pinned from both sides names as
the slot's index
([`IndentStackCover.lean`](../L4YAML/Proofs/Scanner/IndentStackCover.lean)).
The relay the compact fill cannot make is the mapping value park's: that
closure awaits a block node read at the park's position, and the compact
fill's node is a compact sequence on the slot's own line. Of the five
positions that still hold the punt, two are the props router's entry-level
field at index 0, where the field's own equation `n = ne + 1` has no witness
and the field is vacuous; of the three punts, one holds no top bound and two
hold one at their own index. The explicit `:` opener's three callers hold the
stack's monotonicity, the base and the preprocess equation one hop back, so
its own-floor cover is fundable; what it lacks is the resume's bottom, which
the paid `:` openers take as a relay of the pack's resume and it does not
([`PuntCoverInputs.lean`](../Tests/Guards/Proofs/PuntCoverInputs.lean)). The
refused relay would add two positions and one punt to each tree and no paid
leaf. The carrier that would fund the bottom without that relay is a
value-line-then-tail twin of the `?` faces' packs: eleven constructor fields
and twenty-nine lemma parameters, every one a closure that ends at the stream
with no tail after the value, written at 151 positions of which 42 punt; of
the 69 that build, re-wrap or transport a pack, 11 hold a tail or a frames
face at a level they write
([`ValueLinePacks.lean`](../Tests/Guards/Proofs/ValueLinePacks.lean)).  Resolved to where each pack is born ([`ValueLineOrigins.lean`](../Tests/Guards/Proofs/ValueLineOrigins.lean)), the writers' chains reach 70 origin hypotheses at 38 rows, 40 of which hold the tail, and the eighteen positions of the `?` family reach exactly one, the `?` opener's dedent reading off the landing's value-line resume, which does not.

**Significance & risk**

- **7.1 `parse_strict_proof`** *(headline, ✅)* — *Significance:*
  parser acceptance implies the input is in the formalized YAML
  language `InYamlLanguage`. This is the right shape for "we never
  accept a string outside the spec's surface language", and it says
  that only once `InYamlLanguage` excludes something — see *What
  Group 7 does not yet establish* above. *Risk if absent:*
  over-acceptance —
  accepting inputs that other conformant parsers reject, an interop
  and security divergence (the input means one thing to us, another to
  the next tool in the chain).
- **7.2 `scan_content_gives_stream_v2`** *(✅)* — *Significance:*
  scanned content is backed by a full `SLYamlStream` derivation, not
  just a well-formedness flag. Its conclusion is `InYamlLanguage
  input` written out instead of named, so a search for the predicate
  does not reach it and it is free in exactly the same way 7.1 is.
  *Risk if absent:* scanner acceptance with no grammatical
  justification.
- **7.3 `scanLoop_grammar_prod`** *(✅)* — *Significance:* the scan
  loop itself produces a grammar derivation at each step. The statement
  is restrictive — unlike 7.1, 7.2 and 7.6 it is not free — but the
  derivation it builds passes through `scannerDrop`, so β.5 rebuilds it;
  see *What β.5 costs Group 7* above. *Risk if
  absent:* a hole in the middle of the derivation chain.
- **7.4 per-function `*_prod`** *(✅)* — *Significance:* each concrete
  construct (flow/block collections, document markers, anchors,
  aliases, tags, directives) maps to its named YAML 1.2.2 production.
  *Risk if absent:* individual constructs accepted with no spec
  production behind them.
- **7.5 `parseYaml_implies_valid_token_stream`** *(✅)* —
  *Significance:* carries strictness up to the top-level API. *Risk if
  absent:* the strictness result would not reach `parseYaml`.
- **7.6 `scan_strict_proof`** *(✅)* — *Significance:* the same shape
  of strictness at the scanner level, and it carries strictness only
  once `InYamlLanguage` excludes something — 7.1's caveat applies
  unchanged, see *What Group 7 does not yet establish* above. *Risk if
  absent:* the scanner could
  admit non-language strings that the parser then trusts.
- **7.7 `parse_iff_grammar` converse** *(⏳ not started)* —
  *Significance:* the missing half of the biconditional — every string
  in the YAML language *is* accepted. Together with 7.1 it would prove
  the parser accepts **exactly** the language, no more and no less —
  the gold-standard parser-correctness statement. Requires first
  removing the over-approximation constructors that make
  `InYamlLanguage` true of every string (`directiveDrop`
  removed 2026-08-02; `scannerDrop` remains, blocked on flow-collection
  accumulation)
  ([`DOCS.md` § Grammar completeness plan](../DOCS.md#grammar-completeness-plan)). *Risk
  if absent:* 7.1 has the shape of a non-over-acceptance proof and does
  not yet carry it, and we have not proved that we accept the *whole*
  language either — a future scanner/parser refactor
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
the `parseEntry_in_flowMap` cluster, and the original sorry'd
`flow_parser_ok_of_structure`, have been **deleted** (~3,200 LoC,
all sorries removed) — a `unified-dep-table --external-only` run
proved zero out-of-namespace callers.
`grep -rn parser_fuel_mono_succ L4YAML/Proofs` now returns nothing.
The flow-acceptance *results* were later re-landed, proven on a
sounder design: `flow_parser_ok_of_structure` at
`Proofs/Parser/FlowParserAcceptance.lean:883`, with
`ParseNodeFlowSeqOk` (`Proofs/Parser/ParserWellBehaved.lean:4180`)
and `parseFlowSequenceLoop_emitter_ok` (ibid.:4239), consumed by
`EmitterScannability.lean`. This closes the deletion backlog that
motivated the blueprint and validates its founding observation:
theorems were being accumulated without a top-down anchor. (Full
audit trail: the retired `VERSION-0.4.7.md` campaign record, in git
history.)

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
  non-all-scalar flow branches (closed 2026-07-04) still deserve
  dedicated round-trip fixtures — see
  [`Tests/Reflections/NonAllScalarLocality.lean`](../Tests/Reflections/NonAllScalarLocality.lean).
- Group 7.7 (grammar completeness): none yet — natural, since the
  converse is not yet declared.

The discipline (adversarial instantiation *before* proof) is spelled
out in [`06-discipline.md`](06-discipline.md); it is what would have
caught the fuel-monotonicity unsoundness before it was written.
