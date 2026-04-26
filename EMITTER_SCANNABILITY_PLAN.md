# EmitterScannability.lean Remaining Work

## Status: 7 sorry-using declarations remaining

(Build-authoritative: `lake build L4YAML.Proofs.Output.EmitterScannability`
flags warnings at lines 8716, 9213, 9309, 9392, 9610, 10326, 10365.
Line numbers shifted from the original 8170/8666/8758/8840/9058/9774/9813
after Tier 1 Turn 1 (+173 lines, directive helpers), Turn 2 (+63 lines,
`ScanChainGrew` strict track), and Turn 3 (+~370 lines, full
`EmitScansInFlow` family migration to `ScanChainGrew` plus file
reorganization) landed.)

### Remaining Sorries (7 declarations, grouped by difficulty)

#### Tier 1: Filtered Token Infrastructure (1 declaration remaining)
**Foundation for structure theorems**

**Status**: 1 sorry remaining at [`scanNextToken_filtered_grows`](L4YAML/Proofs/Output/EmitterScannability.lean#L8170)
(specifically the catch-all `sorry` at [:8206](L4YAML/Proofs/Output/EmitterScannability.lean#L8206)
covering the directive branch of structural dispatch).
[`ScanChain_filtered_grows`](L4YAML/Proofs/Output/EmitterScannability.lean#L8208)
is **already proven** — its `induction h_chain | step` case uses
`omega` once `scanNextToken_filtered_grows` is closed.

##### The Architectural Issue

The theorem [`scanNextToken_filtered_grows`](L4YAML/Proofs/Output/EmitterScannability.lean#L8170)
claims `(s'.tokens.filter p).size ≥ (s.tokens.filter p).size + 1`
unconditionally on a successful `scanNextToken s = .ok (some s')`. This is
**false in general**: when `scanDirective` runs the RESERVED branch
([Document.lean:260-261](L4YAML/Scanner/Document.lean#L260-L261)) for an
unknown directive name like `%FOO`, it returns successfully but emits no
filtered tokens (only `skipToEndOfLine` advances position, which doesn't
touch `tokens`).

**The conclusion is provable** for emitter-produced inputs because the
canonical emitter never emits `%FOO`-style directives — it only uses
`%YAML`/`%TAG` plus regular flow content. But the theorem statement
doesn't carry this restriction, and the catch-all `sorry` at
[:8206](L4YAML/Proofs/Output/EmitterScannability.lean#L8206) is the
escape valve.

A naive `(h_grew : s'.tokens.size > s.tokens.size)` precondition does NOT
cleanly rule out RESERVED, because preprocess may push 2 placeholder
tokens via `saveSimpleKey` in the same `scanNextToken` call — so a
RESERVED step can have `s'.tokens.size = s.tokens.size + 2` (raw growth)
while filtered count is unchanged. The honest hypothesis is per-step
**filtered** growth, which is essentially the conclusion at chain level.
The way out is a constructive predicate that carries the witness.

##### Migration Strategy: 5 Turns, Each Build-Green

The plan is to introduce a strict-variant track alongside the existing
loose-variant track, migrate consumers, and delete the loose variant
once the sorry is isolated. Every turn builds green and adds no new
sorrys; the final turn removes the line-8206 sorry without any
intermediate state of "more sorrys before fewer."

**Turn 1 — Self-contained directive helpers** ✅ DONE (commit `876779ea`, +173 lines)

Three lemmas landed near the dispatch helpers (above
`dispatchStructural_filtered_mono`, around new line ~7710):

- `scanYamlDirective_new_token_eq` — for `scanYamlDirective s s_after_ws startPos = .ok s'` with `s_after_ws.tokens = s.tokens`, the token at index `s.tokens.size` of `s'.tokens` has `val = .versionDirective major minor` (non-placeholder). Proven by unfolding to the `emitAt`/`Array.push` and computing through `skipWhitespace_preserves_tokens`, `collectVersion*Loop_preserves_tokens`.
- `scanTagDirective_new_token_eq` — analogous, with `.tagDirective handle prefix`.
- `scanDirective_filtered_grows (s s' : ScannerState) (h : scanDirective s = .ok s') (h_grew : s'.tokens.size > s.tokens.size) : ...` — uses `filtered_grows_of_any_new` with witness `s.tokens.size`; the YAML/TAG branches close via Turn-1's new-token-eq lemmas, the RESERVED branch derives `s'.tokens.size = s.tokens.size` (via `skipToEndOfLine_preserves_tokens` + `skipWhitespace_preserves_tokens` + `collectDirectiveNameLoop_preserves_tokens` + `advance_preserves_tokens`) and contradicts `h_grew`.

NB: `h_grew` is sound here even for the saveSimpleKey corner case,
because `scanDirective` itself does not invoke preprocess —
preprocess runs in `scanNextToken_preprocess` *before* the structural
dispatch. So at the level of `scanDirective`, the input state `s` is
already post-preprocess and `s'.tokens.size > s.tokens.size`
genuinely excludes RESERVED.

Lessons logged for Turn 3 onward:
- `apply Exists.intro` (×2) is more robust than `refine ⟨_, _, ?_⟩` for
  nested existentials with deeply-nested term witnesses — the explicit
  unfolding in Turn 1 needed the deferred-witness behavior of `apply`.
- `simp only [h_eq, Array.getElem_push_eq]` handles dependent-type
  rewrites where `rw [h_eq]` errors with "motive is not type correct"
  (the goal carries a hidden `s.size < s'.size` proof tied to the
  rewritten term).
- `rfl` closes constructor-inequality goals with free variables
  (`(.versionDirective M N != .placeholder) = true`) where `decide`
  fails with "expected type contains free variables".
- `collect*_preserves_tokens` and `scan*Directive_*` live in
  `ScannerCorrectness.ScanHelpers` (lines 1029–2867 of
  `ScannerCorrectness.lean`); only the primitives
  (`skipWhitespace_preserves_tokens`, `advance_preserves_tokens`,
  `skipToEndOfLine_preserves_tokens`) are at the top level.

**Turn 2 — Strict variants of scanNextToken/ScanChain** ✅ DONE (+63 lines, build green)

Landed immediately after `ScanChain_filtered_grows`:

- `ScanChainGrew p` inductive predicate, mirroring `ScanChain` with a
  per-step witness `(s_mid.tokens.filter p).size > (s.tokens.filter p).size`.
- `ScanChainGrew.toScanChain` — forgetful map; drops the per-step
  witness and yields a plain `ScanChain` (so any consumer that takes
  `ScanChain` accepts a strict chain).
- `ScanChainGrew.single` — single-step constructor.
- `ScanChainGrew.trans` — concatenation, mirroring `ScanChain.trans`.
- `ScanChainGrew_filtered_grows` — induction over the chain, each
  `step` contributes ≥1 filtered token; closed by `omega` on the
  per-step witness + IH.  Critically, this does **not** depend on
  `scanNextToken_filtered_grows` (the loose-track theorem with the
  line-8379 sorry).

Existing `scanNextToken_filtered_grows` and `ScanChain_filtered_grows`
unchanged — still in service for any callers we haven't migrated yet.

The strict track is purely additive at this point; no caller has been
migrated.  Sorry count unchanged at 7 (warnings shifted from
8170/8666/8758/8840/9058/9774/9813 to 8343/8902/8994/9076/9294/10010/10049).

**Turn 3 — Strengthen `EmitScansInFlow` and family** (~370 lines net, file reorganization + propagation) — ✅ **DONE**

This was the heaviest turn.  Strategy A (replacement) was chosen and
required a substantial file reorganization to make the filtered-growth
infrastructure available where the constructions live.  All four
`scanNextToken_preprocess_flow_ws1` call sites were updated to bind a
new `tokens = tokens` conjunct.

##### What landed

1. **File reorganization (~945 lines moved)**: the entire filtered-growth
   infrastructure block (lines 7457–8401: `Array_filter_prefix_of_raw_prefix`,
   `preprocess_filtered_mono`, `allowDir_ite_filter`, `filtered_grows_of_*`,
   `dispatch*_filtered_grows`, `scanBlockEntry/Key/Value_filtered_grows`,
   `dispatchContent_new_not_placeholder`, plus the three Turn 3-partial
   dispatch-level wrappers) was moved to before line 5611 (just before
   the `EmitScansInFlow` predicate definitions).  `emit_tokens_push` was
   forward-declared near the move's start since it's used inside the
   block.  The `ScanChainGrew` block (originally added in Turn 2 right
   after `ScanChain_filtered_grows`) was also moved to immediately
   before `EmitScansInFlow`.

2. **`scanNextToken_filtered_grows_in_flow`** (around new line ~6573,
   ~50 lines): the in-flow analogue of `scanNextToken_filtered_grows`.
   With `s.inFlow = true ∧ s.currentIndent < 0 ∧ s.col > 0` and the
   next character being non-whitespace,
   `dispatchStructural_none_flow` rules out the directive branch
   entirely, so the conclusion goes through unconditionally without a
   sorry.  Used at every `ScanChainGrew.single` construction site to
   produce the per-step witness.

3. **`ScanChainGrew_of_scanNextToken_eq`** helper next to the other
   `ScanChainGrew` lemmas: lifts a `ScanChainGrew p s₂ (n+1) s'` to
   `ScanChainGrew p s₁ (n+1) s'` given `scanNextToken s₁ = scanNextToken s₂`
   and `(s₁.tokens.filter p).size ≤ (s₂.tokens.filter p).size`.  Used
   to thread the strict witness through `scanNextToken_preprocess_flow_ws1`
   in `emitList_scans_nonempty` and `emitPairList_scans_nonempty`.

4. **Predicate migration**: `EmitScansInFlow`, `EmitListScansInFlow`,
   `EmitPairListScansInFlow` now produce
   `ScanChainGrew (fun t => t.val != .placeholder) s n s'` instead of
   `ScanChain s n s'`.

5. **Construction-site updates**:
   - `emitList_scans_empty`/`emitList_scans_nonempty` (singleton +
     multi-item composition with `ScanChainGrew.single h_snt₂ h_grew₂`
     for the comma step and `ScanChainGrew_of_scanNextToken_eq` for the
     preprocess-equality lift).
   - `emitPairList_scans_empty`/`emitPairList_scans_nonempty`
     (analogous, with two `ScanChainGrew.single` insertions for the
     `:` and `,` steps and two `ScanChainGrew_of_scanNextToken_eq`
     lifts).
   - `emit_scans_in_flow` for all three `Grammable` cases:
     - **scalar**: `ScanChainGrew.single h_snt h_grew` for the
       double-quoted scalar step.
     - **sequence**: `ScanChainGrew.single h_snt₁ h_grew₁` for `[`,
       composed with the IH chain and
       `ScanChainGrew.single h_snt₃ h_grew₃` for `]`.
     - **mapping**: analogous with `{`/`}`.

6. **Downstream consumers**:
   - `scanner_accepts_emit_main` (sequence and mapping): forgot the
     strict witness back to `ScanChain` via `.toScanChain` for the
     `scanFiltered_of_chain` consumer.
   - `emitList_body_filtered_characterization` and
     `emitPairList_body_filtered_characterization`: use
     `ScanChainGrew_filtered_grows` (from the strict track, sorry-free)
     instead of the loose `ScanChain_filtered_grows` (which depends on
     the line-8716 sorry).  Public boundary still returns `ScanChain`
     via `.toScanChain`.

##### Status after Turn 3

Sorry count unchanged at **7** (warnings now at 8716/9213/9309/9392/
9610/10326/10365).  Critically, `emitList_body_filtered_characterization`
(line 9213) and `emitPairList_body_filtered_characterization` (line
9309) — Tier 2 sorries — now use `ScanChainGrew_filtered_grows`
internally, decoupling them from the line-8716 sorry.  Turn 5 can now
delete the loose `scanNextToken_filtered_grows` and
`ScanChain_filtered_grows` once the four direct consumers in
`scanFiltered_emitSeq_nonempty_structure` and
`scanFiltered_emitMap_nonempty_structure` are migrated in Turn 4.

##### Original strategy notes (kept for context)

✅ **Earlier partial progress**: Three dispatch-level filtered-grows
wrappers landed just before `scanNextToken_filtered_grows` (~70 lines,
now at ~6519):

- `scanNextToken_via_flow_dispatch_filtered_grows` — given `h_pp` +
  `h_struct = .ok none` + `h_check` + `h_flow = .ok (some s')` (the
  five components produced by `scanNextToken_via_flow_dispatch`), composes
  `preprocess_filtered_mono` + `allowDir_ite_filter` +
  `dispatchFlowIndicators_filtered_grows` to give the `≥ +1` witness on
  filtered tokens.  Used for the comma path (`,`) and bracket/brace
  open/close (`[`, `]`, `{`, `}`).
- `scanNextToken_via_block_dispatch_filtered_grows` — analogous, using
  `dispatchBlockIndicators_filtered_grows`.  Used for the value
  indicator (`:`) which goes through block dispatch.
- `scanNextToken_via_content_dispatch_filtered_grows` — analogous, using
  `dispatchContent_filtered_grows`.  Used for the scalar path
  (`scanNextToken_flow_scanDoubleQuoted`).

These three wrappers are net-positive infrastructure that downstream
turns (Turn 4 and beyond) can use directly even if the EmitScansInFlow
strengthening lands via a different route.

⚠ **Blocker discovered**: the filtered-grows infrastructure (lines
7459–8400: `Array_filter_prefix_of_raw_prefix`, `preprocess_filtered_mono`,
`filtered_grows_of_extended_prefix`, `dispatchFlowIndicators_filtered_grows`,
`dispatchBlockIndicators_filtered_grows`, `dispatchContent_filtered_grows`,
plus the three new dispatch-level wrappers above) is defined **AFTER**
both the emitter helpers (`scanNextToken_flow_*` family at 3890–5400) and
the `EmitScansInFlow` predicates and constructions (5611–6739).

To strengthen the construction sites to produce `ScanChainGrew p s n s'`
(which requires per-step filtered-growth witnesses at each
`scanNextToken s = .ok (some s_mid)` step), the filtered-growth
infrastructure must be available where those constructions live.

##### Two sub-strategies:

- **Sub-strategy A (replacement)**: change `EmitScansInFlow` /
  `EmitListScansInFlow` /`EmitPairListScansInFlow` definitions to produce
  `ScanChainGrew` in place of `ScanChain`. Pros: clean. Cons: cascading
  changes through ~43 references; **requires reorganizing the file** to
  move ~400-900 lines of filtered-growth infrastructure earlier
  (currently 7459–8400, would need to land before 5611).

- **Sub-strategy B (parallel field)**: add `ScanChainGrew p s n s'` as
  an additional conjunct alongside the existing `ScanChain s n s'` in
  each predicate. Existing consumers see no change; new consumers can
  use the strict variant. Pros: incremental; no signature breakage.
  Cons: duplicate API surface during migration; **also requires
  filtered-growth infrastructure to be available at construction sites**
  (same topological problem).

- **Sub-strategy C (post-hoc upgrade)**: keep `EmitScansInFlow` etc.
  unchanged; introduce a NEW lemma `EmitScansInFlow_to_grew` defined
  AFTER all filtered-growth infrastructure that takes an existing
  `EmitScansInFlow v` and produces `ScanChainGrew p s n s'` by
  re-tracing the chain step-by-step.  This requires per-step witnesses
  that the original chain provides only via `scanNextToken s = .ok (some
  s_mid)`; the upgrade needs an in-flow filtered-growth lemma
  `scanNextToken_filtered_grows_in_flow` that closes the directive case
  via `dispatchStructural_none_flow`.  Cons: requires propagating
  inFlow + currentIndent < 0 + col > 0 invariants through the whole
  chain (FlowMonoChain only carries flowLevel), which may not hold if
  preprocess crosses a newline.

##### Recommended path forward:

Given the topology issue, **sub-strategy A with file reorganization** is
still the cleanest end state — the per-step witness is constructive at
each construction site once the infrastructure is available there.  The
reorganization is risky but mechanical.

Alternative: **defer the `ScanChainGrew` migration** and instead pursue a
**string-level "no RESERVED directive"** precondition on `scanFiltered`
inputs (the original "decision point" mentioned below).  For
emitter-produced inputs this is easily provable since the emitter only
produces `%YAML`/`%TAG` directives (and only at very specific positions,
none of which are in the EmitScansInFlow context).  This sidesteps the
chain-level migration entirely but couples `scanFiltered_emitSeq_*` and
`scanFiltered_emitMap_*` to a string-level invariant.

**Turn 4 — Migrate the 4 callers** (~50 lines)

Lines [8716](L4YAML/Proofs/Output/EmitterScannability.lean#L8716),
[8821](L4YAML/Proofs/Output/EmitterScannability.lean#L8821),
[8966](L4YAML/Proofs/Output/EmitterScannability.lean#L8966),
[9173](L4YAML/Proofs/Output/EmitterScannability.lean#L9173) — switch
from `ScanChain_filtered_grows h_chain` to
`ScanChainGrew_filtered_grows h_chain_grew`. The strengthened
`EmitScansInFlow` from Turn 3 produces `h_chain_grew` directly.

After this turn, the loose `scanNextToken_filtered_grows` and
`ScanChain_filtered_grows` have no callers in the file.

**Turn 5 — Cleanup and sorry removal** (~50 lines deleted)

- Verify no callers remain for the loose variants (grep across the
  workspace, not just EmitterScannability.lean).
- If clean: delete the loose `scanNextToken_filtered_grows` (containing
  the line-8206 sorry) and the loose `ScanChain_filtered_grows`.
- If external callers exist: keep them, but reroute their proof through
  the strict variant under an additional precondition (e.g., a string-
  level "no `%` at col 0" predicate proven once for emit outputs).
- **Result**: the sorry at line 8206 is gone. EmitterScannability.lean
  goes from 7 sorrys to 6 sorrys.

##### Total Estimated Effort

~600-800 lines of net change across 5 turns:
- Turn 1: +80 lines (helpers)
- Turn 2: +100 lines (predicate + strict variants)
- Turn 3: +300-500 lines (propagation through EmitScansInFlow family)
- Turn 4: ~50 lines changed (caller migration)
- Turn 5: -50 lines (delete obsolete loose variants)

##### Risks and Open Questions

- **Cascading change in Turn 3**: The 43 `EmitScansInFlow` references
  may not all need updating, but each must be audited. Some may live in
  proofs that don't construct chains, only consume them.
- **External callers of loose variants**: Need to grep beyond
  EmitterScannability.lean before deleting in Turn 5. If
  `scanNextToken_filtered_grows` is used elsewhere (e.g., in
  ScannerCorrectness or RoundTrip proofs), Turn 5 needs a different
  closure — most likely keeping the loose variant with a stronger
  precondition that its existing callers can discharge.
- **Per-scanner growth lemmas**: Turn 3 may surface up to ~10 new
  scanner-specific filtered-growth lemmas if none exist. Each is
  ~10-15 lines (apply `filtered_grows_of_any_new` + identify the new
  token via `scanX_preserves_prefix` + `scanX_adds_one_token`).

##### Decision Point Between Turns

After Turn 1 (helpers landed), reassess: if `scanDirective_filtered_grows`
proved more painful than estimated, reconsider whether the cleaner fix
is a string-level "no RESERVED" hypothesis on the input rather than the
chain-level migration. Decision should be informed by the actual cost
of Turn 1.

#### Tier 2: Body Token Characterization (2 declarations, 5 sorries total)
**Compositional tracking of body tokens**

After Tier 1 Turn 3 the two body-characterization theorems are scaffolded —
they obtain a `ScanChainGrew` from `emit{,Pair}List_scans_nonempty`, derive
`h_grows := ScanChainGrew_filtered_grows h_chain`, and discharge the
prefix-uniqueness / `n ≥ 1` boilerplate.  What remains is content
reasoning about which token sits at which filtered index, split across 5
sorries:

- [`emitList_body_filtered_characterization`](L4YAML/Proofs/Output/EmitterScannability.lean#L9213) — 2 sorries
  - line 9289: token at `old_sz` is a content start (scalar / flowSeqStart / flowMapStart)
  - line 9291: after every outer-level `.flowEntry`, next filtered token is a content start
- [`emitPairList_body_filtered_characterization`](L4YAML/Proofs/Output/EmitterScannability.lean#L9309) — 3 sorries
  - line 9377: `n ≥ 3` (key + value-indicator + value-content)
  - line 9383: first new filtered token is `.key`
  - line 9385: after every outer-level `.flowEntry`, next filtered token is `.key`

The cost driver is **missing infrastructure**: there are no per-scanner
"first filtered token" lemmas for `scanDoubleQuoted` /
`scanFlowSequenceStart` / `scanFlowMappingStart`, and the `.key`
retroactive promotion (`saveSimpleKey` saves placeholder → `scanValuePrepare`
rewrites to `.key`) needs an inversion lemma.  In addition,
`emitList_scans_nonempty` and `emitPairList_scans_nonempty` build their
chains compositionally but do not expose per-item / per-pair segment
witnesses — Tier 2 will either re-derive segments by induction in the
body characterization itself, or strengthen the scans theorems to return
segment information.

##### Turn Breakdown

###### Turn 1 — First-Filtered-Token Lemmas ✅ COMPLETE

Three lemmas characterize the first new filtered token after `scanNextToken`
in flow context, dispatched by the leading character (`"`, `[`, `{`).
Plus two helpers:

- [`scanNextToken_via_content_dispatch_error`](L4YAML/Proofs/Output/EmitterScannability.lean#L3868) —
  error-variant of the existing `scanNextToken_via_content_dispatch`, used
  to invert dispatch into a successful `dispatchContent` call.
- [`scanFlowSequenceStart_first_filtered_token`](L4YAML/Proofs/Output/EmitterScannability.lean#L5597) —
  `((s'.tokens.filter p)[old_sz]'h).val = .flowSequenceStart`.
- [`scanFlowMappingStart_first_filtered_token`](L4YAML/Proofs/Output/EmitterScannability.lean#L5656) —
  `((s'.tokens.filter p)[old_sz]'h).val = .flowMappingStart`.
- [`scanDoubleQuoted_tokens_push`](L4YAML/Proofs/Output/EmitterScannability.lean#L5715) —
  extracts `s'.tokens = s.tokens.push ⟨_, .scalar c .doubleQuoted, _⟩`
  from `scanDoubleQuoted s = .ok s'`.
- [`scanDoubleQuoted_first_filtered_token`](L4YAML/Proofs/Output/EmitterScannability.lean#L5745) —
  `∃ c sc, ((s'.tokens.filter p)[old_sz]'h).val = .scalar c sc`.

Each lemma re-runs the dispatch pipeline (preprocess → structural → flow →
block → content) and uses `Array.filter_push` after observing that
`saveSimpleKey_filter_placeholder` collapses the preprocess effect on
filtered tokens.

**Status**: lemmas in file, no new sorries (count unchanged at 9), build green.

###### Turn 2 — `emitList_body_filtered_characterization` (~150-200 lines)

Discharge the 2 sorries at lines 9289 and 9291.

**Part 1 (line 9289)** — token at `old_sz` is content start.
Strategy: `emitList` of `v :: tail` starts with `emit v`.  The first
character of `emit v` is dispatched by `EmitScansInFlow v` to one of
{`scanDoubleQuoted`, `scanFlowSequenceStart`, `scanFlowMappingStart`}.
Apply Turn 1's first-token lemma matching that dispatch.

**Part 2 (line 9291)** — outer-level flowEntry → next is content start.
Strategy: induct on `items`.  Each `, ` separator is scanned by
`scanFlowEntry`, after which the next call dispatches `emit v'` for the
next item — same content-start argument as Part 1.  The
`flowBracketBalance = 0` precondition rules out `.flowEntry`s emitted
inside nested `[...]` / `{...}` (which sit at balance > 0).

**Acceptance**: 2 sorries gone, build green, sorry count drops 9 → 7.

###### Turn 3 — `emitPairList` Part 1: `n ≥ 3` (~40 lines)

Discharge the sorry at line 9377.  This one is structural-counting only:
each pair runs `saveSimpleKey + emit k + ': ' + emit v`, which produces
at least 3 scanner steps regardless of `EmitScansInFlow` content.
Inspect the chain construction in `emitPairList_scans_nonempty` and
extract the step count directly, or re-do the count via induction on
`pairs`.  Cleanly separable from Turn 4.

**Acceptance**: 1 sorry gone, build green, sorry count drops 7 → 6.

###### Turn 4 — `emitPairList` Parts 2+3: `.key` characterization (~150-200 lines)

Discharge the 2 sorries at lines 9383 and 9385.

**Subtle bit**: `.key` does not arrive directly from `saveSimpleKey` —
that pushes a `.placeholder`.  When the scanner later sees `: ` and
calls `scanValuePrepare`, it retroactively rewrites the placeholder to
`.key`.  Need an inversion lemma:

```lean
theorem scanValuePrepare_promotes_simpleKey ... :
  -- if simpleKey was possible at index i, after scanValuePrepare
  -- (s'.tokens[i]'h).val = .key
```

**Part 2 (line 9383)** — first new filtered token is `.key`.  After
`saveSimpleKey + emit k + ': '` the placeholder at `old_sz` has been
promoted to `.key`.  This is the first non-placeholder token in
`s'.tokens.filter p`.

**Part 3 (line 9385)** — after outer-level flowEntry, next is `.key`.
Mirrors Part 2 inductively across pairs.  Same `flowBracketBalance = 0`
filter as emitList Part 2.

**Acceptance**: 2 sorries gone, build green, sorry count drops 6 → 4
(only Tier 3 + Tier 4 sorries remain).

##### Estimated Total

~420-560 lines across 4 turns:
- Turn 1: ~80-120 lines (3 first-token lemmas)
- Turn 2: ~150-200 lines (emitList characterization)
- Turn 3: ~40 lines (pair count)
- Turn 4: ~150-200 lines (pair .key characterization + promotion lemma)

##### Risks

- **Segment witnesses**: if reasoning about flowEntry positions cannot
  be done by re-inducting in the body theorem and instead requires
  segment witnesses from `emit{,Pair}List_scans_nonempty`, those scans
  theorems need restructuring — adding ~50-100 lines of bookkeeping
  upstream and shrinking Turn 2/4 by similar amount.
- **`scanValuePrepare` promotion lemma**: if `scanValuePrepare`'s
  current statement doesn't expose token-rewrite information, may need
  a small precursor lemma in `Scanner/` proofs (~30-50 lines).  Audit
  in Turn 1.
- **EmitScansInFlow first-token info**: the predicate's postcondition
  currently characterizes the *last* real token (via `lastRealTokenVal?`)
  but not the *first*.  If Turn 1's lemmas can only characterize the
  first scanner step (not the first filtered token of the entire `emit v`
  chain), Turn 2 Part 1 needs an additional step: show that the chain's
  first step's token survives subsequent steps unchanged.  This follows
  from `ScanChainGrew_filtered_grows` + array-prefix preservation.

#### Tier 3: Structure Theorems (2 declarations, ~150-300 lines each)
**Main token array structure proofs**

4. **Line 8840**: `scanFiltered_emitSeq_nonempty_structure`
   - For non-empty sequence: tokens = [streamStart, flowSequenceStart] ++ body ++ [flowSequenceEnd, streamEnd]
   - Proves 8 properties:
     1. tokens[0]!.val = .streamStart
     2. tokens[1]!.val = .flowSequenceStart
     3. tokens[tokens.size-2]!.val = .flowSequenceEnd
     4. tokens[tokens.size-1]!.val = .streamEnd
     5. tokens.size ≥ 6 (minimum tokens)
     6. Uniqueness: ∀ k < tokens.size-2, tokens[k]!.val ≠ .flowSequenceEnd
     7-8. Position and token properties
   - **Depends on**: Line 8666 (body characterization), filtered infrastructure
   - ~150-250 lines

5. **Line 9058**: `scanFiltered_emitMap_nonempty_structure`
   - Parallel to scanFiltered_emitSeq_nonempty_structure for mappings
   - Proves 7 similar properties with flowMappingStart/End
   - **Depends on**: Line 8758 (body characterization), filtered infrastructure
   - ~150-250 lines

#### Tier 4: Content Fidelity (2 declarations, ~150-300 lines each)
**Round-trip correctness for nested structures**

6. **Line 9774**: `emit_roundtrip_sequence_content_eq`
   - Non-empty case: parsed sequence items match originals
   - Proof: Structural decomposition + IH
   - Uses parseFlowSequence result analysis
   - **Depends on**: `ParseNodeFlowSeqOk` predicate at [ParserWellBehaved.lean:4123](L4YAML/Proofs/Parser/ParserWellBehaved.lean#L4123) (used at the `:= sorry` site at line 9052)
   - ~150-200 lines

7. **Line 9813**: `emit_roundtrip_mapping_content_eq`
   - Non-empty case: parsed mapping pairs match originals
   - Proof: Structural decomposition + IH
   - Parallel to sequence case
   - **Depends on**: `ParseNodeFlowSeqOk` predicate (used at the `:= sorry` site at line 9237)
   - ~150-200 lines

### Dependencies Between Layers

```
Tier 1: scanNextToken_filtered_grows (8170)
         ↓
       ScanChain_filtered_grows (8208) — already proven
         ↓
         ├─→ emitList_body_filtered_characterization (8666)
         │    ↓
         │   scanFiltered_emitSeq_nonempty_structure (8840)
         │    ↓
         │   emit_roundtrip_sequence_content_eq (9774)
         │
         └─→ emitPairList_body_filtered_characterization (8758)
              ↓
             scanFiltered_emitMap_nonempty_structure (9058)
              ↓
             emit_roundtrip_mapping_content_eq (9813)
```

### Cross-Module Dependencies

**EmitterScannability uses `ParseNodeFlowSeqOk` (predicate, not theorem).**
The two `:= sorry` sites at lines 9052 and 9237 instantiate
`L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2`
— i.e., they assume the parser succeeds on the body of an emitter-scanned
flow collection. The supporting theorems (`parseFlowSequenceLoop_emitter_ok`
at [:4171](L4YAML/Proofs/Parser/ParserWellBehaved.lean#L4171) and
`parseFlowMappingLoop_emitter_ok` at [:4465](L4YAML/Proofs/Parser/ParserWellBehaved.lean#L4465))
are proven; the gap is constructing the precondition bundle for them.

(The earlier plan referenced `parseNode_flowSeqStart_in_seq` at line 6017
and `parseNode_flowMapStart_in_seq` at line 6366 in ParserWellBehaved —
those names don't exist in the current codebase and the line numbers are
stale from before the dead-code cleanup that removed 3,233 LoC at commit
aa791e76. ParserWellBehaved is now 4,797 lines total.)

### Recommended Attack Order

**Phase A: Token Infrastructure (Tier 1)** (~600-800 lines across 5 turns,
see "Migration Strategy" above)
1. Turn 1 — directive helpers
2. Turn 2 — `ScanChainGrew` predicate + strict variants
3. Turn 3 — strengthen `EmitScansInFlow` family
4. Turn 4 — migrate 4 callers
5. Turn 5 — delete loose variants, sorry at line 8206 GONE
- Unlocks: All body characterization and structure theorems

**Phase B: Sequence Path (Tiers 2-3)** (~250-400 lines)
1. emitList_body_filtered_characterization (8666)
2. scanFiltered_emitSeq_nonempty_structure (8840)
- Unlocks: emit_roundtrip_sequence_content_eq

**Phase C: Mapping Path (Tiers 2-3)** (~250-400 lines)
1. emitPairList_body_filtered_characterization (8758)
2. scanFiltered_emitMap_nonempty_structure (9058)
- Unlocks: emit_roundtrip_mapping_content_eq

**Phase D: Content Fidelity (Tier 4)** (~300-400 lines)
1. emit_roundtrip_sequence_content_eq (9774)
2. emit_roundtrip_mapping_content_eq (9813)

**Estimated Total**: ~1450-2050 lines (Tier 1 alone is ~600-800 lines
across 5 turns)

### Alternative: Interleaved Approach

Could work on both EmitterScannability and ParserWellBehaved in parallel:
- EmitterScannability Phases A-C can proceed independently
- Phase D requires some ParserWellBehaved lemmas but the critical loop theorems are done

### Current Blocker Status

**No blockers for Phases A-C!**
- The loop theorems (`parseFlowSequenceLoop_emitter_ok`, `parseFlowMappingLoop_emitter_ok`) are PROVEN
- These are used in `parseStream_emitSequence` and `parseStream_emitMapping` which are also PROVEN
- Phase D (content fidelity) is the only part that may benefit from additional ParserWellBehaved lemmas

### Notes

- **Filtered token tracking**: Core pattern is showing `.filter` preserves structure through ScanChain
- **Body characterization**: Key insight is that nested brackets are consumed by sub-chains, so body tokens don't contain top-level closing brackets
- **Structure theorems**: Largest proofs, but mostly mechanical composition of infrastructure
- **Content fidelity**: Requires understanding both scanner and parser behavior together
