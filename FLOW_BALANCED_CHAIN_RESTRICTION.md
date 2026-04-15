# Flow-Balanced Chain Restriction

## Motivation

`ScanChain_filtered_prefix` (EmitterScannability.lean) asserts that through a scan chain,
the non-placeholder (filtered) token array of the initial state is preserved as a prefix.
The current precondition is `s.simpleKey.possible = false`, which adversarial testing
(1089/1089) confirms is correct. However, the proof requires a **flow-level balance
argument** that is missing from the current formalization.

### The gap

The proof needs to show that `setIfInBounds` (called by `scanValuePrepare` when `:` is
encountered) never writes at token positions below `s_init.tokens.size`. This holds when
every active `simpleKey.tokenIndex` during the chain is `≥ s_init.tokens.size`.

The current `simpleKey` satisfies this (from `sk.possible = false` at start + monotonic
`saveSimpleKey` growth). But the **simpleKeyStack** contains entries from BEFORE the chain
(pushed by the outer `scanFlowSequenceStart`/`scanFlowMappingStart`) with `tokenIndex < n₀`.
If a flow close operation restores such an entry, the invariant breaks.

This never happens in practice because the chain body is a flow-balanced sub-expression:
every `]`/`}` matches an inner `[`/`{`, so `flowLevel` never drops below the initial level,
and the stack is never popped below its initial height. But `ScanChain` carries no
flow-level information, so this argument cannot be formalized.

### The fix

Introduce `FlowMonoChain fl₀ : ScannerState → Nat → ScannerState → Prop`, a strengthening
of `ScanChain` that carries `s.flowLevel ≥ fl₀` at every step. Thread it through the
`EmitScansInFlow` interface. Use the flow-level bound to prove a local version of
`SimpleKeyAbove` that only constrains stack entries at indices ≥ the initial stack height,
then compose with `Array_filter_prefix_of_raw_prefix` for the filtered prefix result.

---

## Step 1: Define `FlowMonoChain` and basic operations

**Where:** EmitterScannability.lean, after `ScanChain` definition (~L1200)

**What:**
- `FlowMonoChain (fl₀ : Nat) : ScannerState → Nat → ScannerState → Prop` — inductive
  with same structure as `ScanChain` but carrying `h_fl : s.flowLevel ≥ fl₀` at each step
- `FlowMonoChain.toScanChain` — degradation to `ScanChain`
- `FlowMonoChain.single` — single-step constructor
- `FlowMonoChain.trans` — transitivity (chain concatenation)
- `FlowMonoChain.weaken` — relax the floor (`fl₁ ≥ fl₀ → FlowMonoChain fl₁ → FlowMonoChain fl₀`)
- `FlowMonoChain.flowLevel_ge` — extract flow level bound at start/end

**Impact:** Zero changes to existing code. Pure additive definitions.

***Step 1: Accomplishments***

1. **Defined `FlowMonoChain` inductive** (~10 LOC). Same structure as `ScanChain` (`zero`/`step`
   constructors) but carrying `h_fl : s.flowLevel ≥ fl₀` at each step. Placed in
   EmitterScannability.lean immediately after the `ScanChain` section (~L1300), before
   `scanFiltered_of_chain`.

2. **7 basic operations proven** (~50 LOC total):
   - `FlowMonoChain.toScanChain`: degradation to `ScanChain` by forgetting flow bounds
   - `FlowMonoChain.flowLevel_ge_start/end`: extract flow level bound from start/end state
   - `FlowMonoChain.single`: single-step constructor (requires flow bound at both endpoints)
   - `FlowMonoChain.trans`: chain concatenation (mirrors `ScanChain.trans`)
   - `FlowMonoChain.weaken`: relax the floor (`fl₀ ≤ fl₁ → FlowMonoChain fl₁ → FlowMonoChain fl₀`)
   - `FlowMonoChain.tokens_mono`: token array monotonicity (via per-step `scanNextToken_adds_tokens`)

3. **Build: 429/429 jobs, 11 sorry warnings (unchanged).** Pure additive definitions —
   no existing code modified. Zero impact on current proof architecture.

***Step 1: Reflections***

1. **`FlowMonoChain.trans` mirrors `ScanChain.trans` exactly** — same induction pattern
   with the `k + 1 + n₂ = (k + n₂) + 1` rewrite. The flow bound `h_fl` adds no difficulty
   since it's threaded unchanged through the induction.

2. **`tokens_mono` needed self-contained proof.** `ScanChain_tokens_mono` is defined later
   in the file (~L6681) and can't be referenced from the insertion point (~L1300). Used
   direct induction with `ScannerCorrectness.scanNextToken_adds_tokens` instead. This is
   fine — the `ScanChain_tokens_mono` proof uses the same approach internally.

3. **`weaken` is the key composition enabler.** For nested sequences, the body chain has
   flow floor `fl₀ + 1` (inner flow level) but needs to compose with open/close steps at
   floor `fl₀`. `weaken` bridges this gap without re-proving the body chain.

## Step 2: Thread `FlowMonoChain` through `EmitScansInFlow` interface

**Where:** EmitterScannability.lean

**What:**
- Add `∧ FlowMonoChain s.flowLevel s n s'` to postconditions of:
  - `EmitScansInFlow` (L4845)
  - `EmitListScansInFlow` (L4875)
  - `EmitPairListScansInFlow` (L5438)
- Update all 5 producer proofs:
  - `emit_scans_in_flow` (L5746) — 3 cases: scalar, sequence, mapping
  - `emitList_scans_empty` (L4900)
  - `emitList_scans_nonempty` (L4911)
  - `emitPairList_scans_empty` (L5462)
  - `emitPairList_scans_nonempty` (L5475)
- Update all consumer sites to destructure the extra field (can be `_`-ignored)

**Approach for producer proofs:**
- Scalar case: `FlowMonoChain.single h_snt (by omega) (by rw [h_fl']; omega)`
- Sequence case: Compose three sub-chains:
  1. Open bracket: `FlowMonoChain.single h_snt₁ h_fl (by rw [h_fl₁]; omega)` — fl ≥ fl₀ ✓
  2. Body chain: `FlowMonoChain (fl₀ + 1)` from `EmitListScansInFlow`, weakened to fl₀
  3. Close bracket: `FlowMonoChain.single h_snt₃ (by rw [h_fl₂, h_fl₁]; omega) (by ...)`
  Then `FlowMonoChain.trans` across all three.
- Mapping case: Analogous to sequence.
- List/PairList cases: Compose per-item/pair chains + comma/space steps via `.trans`.

**Impact:** ~3 definition changes, ~5 proof changes (mostly additive — constructing
the `FlowMonoChain` alongside the existing `ScanChain`), ~10-15 consumer destructuring
updates (add `_` for the new field).

**Risk:** MEDIUM. The producer proofs for the non-trivial cases (sequence, mapping,
emitList_nonempty, emitPairList_nonempty) need careful chain composition with `trans`
and `weaken`. The consumer updates are mechanical.

***Step 2: Accomplishments***

1. **Added `FlowMonoChain_of_scanNextToken_eq` utility** (~10 LOC). Analogous to
   `ScanChain_of_scanNextToken_eq` — lifts a FlowMonoChain through preprocessing when
   `scanNextToken s₁ = scanNextToken s₂` and `s₁.flowLevel ≥ fl₀`. Used in every non-trivial
   producer proof to bridge preprocessing steps (flow whitespace skip).

2. **Updated 3 interface definitions** to add `∧ FlowMonoChain s.flowLevel s n s'` as the
   final postcondition:
   - `EmitScansInFlow`: 15→16 postconditions
   - `EmitListScansInFlow`: 13→14 postconditions
   - `EmitPairListScansInFlow`: 13→14 postconditions

3. **Updated 5 producer proofs** to construct and return `FlowMonoChain`:
   - `emitList_scans_empty`: `.zero (Nat.le_refl _)` (trivial 0-step chain)
   - `emitPairList_scans_empty`: identical
   - `emitList_scans_nonempty`: singleton passthrough; multi-item composes emit+comma+recursive
     via `FlowMonoChain_of_scanNextToken_eq` + `.single` + `.trans`
   - `emitPairList_scans_nonempty`: singleton composes key+colon+value; multi-pair adds
     comma+recursive. Both use preprocessing lift.
   - `emit_scans_in_flow`: scalar uses `.single`; sequence/mapping use `.weaken` on body
     chain (floor fl+1→fl), then `.single`+`.trans` for open/close brackets.

4. **Updated 6 consumer destructuring sites** (mechanical `_` addition):
   - `emit_produces_valid_yaml` sequence/mapping cases
   - `parseStream_emitSequence` / `parseStream_emitMapping`

***Step 2: Reflections***

1. **`▸` direction matters in term mode.** `(h : a = b) ▸ e` finds `a` (LHS) in the expected
   type. When rewriting `FlowMonoChain s₃.flowLevel ...` to `FlowMonoChain s.flowLevel ...`,
   need `(show s.flowLevel = s₃.flowLevel from ...) ▸ h_fmc₃` (finds `s.flowLevel` in
   expected type), NOT `(show s₃.flowLevel = s.flowLevel ...) ▸ h_fmc₃`.

2. **`by rw [h₁, h₂]` does NOT close `≥` goals.** After chained rewrites, `rw` closes
   `a = a` via `rfl` but not `a ≥ a`. Use `by omega` instead for all `≥`/`≤` bounds.

3. **`weaken` already handles floor lowering.** For sequence/mapping cases, the original
   approach used `(show s₁.flowLevel = ... from h_fl₁) ▸ h_fmc₂.weaken (by omega)`, but
   the `▸` is unnecessary — `weaken (by omega)` infers the target floor from context.

4. **`by omega` is robust for all chain hypotheses.** Every `≥` proof in FlowMonoChain
   construction (single's 2nd/3rd args, FlowMonoChain_of_scanNextToken_eq's 2nd arg) can
   use `by omega`, which automatically finds the equality chain in context. No need for
   explicit `rw [h_fl₃, h_fl₂, h_fl₁]` for `≥` goals.

## Step 3: Define `SimpleKeyAboveFloor` and per-step preservation

**Where:** EmitterScannability.lean or ScannerCorrectness.lean

**What:**
- Define `SimpleKeyAboveFloor`:
  ```lean
  def SimpleKeyAboveFloor (s : ScannerState) (n : Nat) (stackFloor : Nat) : Prop :=
    (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
    (∀ j, stackFloor ≤ j → (h : j < s.simpleKeyStack.size) →
      s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ n) ∧
    (s.simpleKeyStack.size ≥ stackFloor)
  ```
- Prove per-step preservation: `scanNextToken s = .ok (some s') → s.flowLevel > fl₀ →
  SimpleKeyAboveFloor s n₀ stackFloor → SimpleKeyAboveFloor s' n₀ stackFloor`
  Note: requires `s.flowLevel > fl₀` (strictly above floor) at close-bracket steps, which
  is equivalent to `s.simpleKeyStack.size > stackFloor`. The `FlowMonoChain` gives us
  `s.flowLevel ≥ fl₀`; the close bracket dispatch requires `flowLevel > 0`. When `fl₀ ≥ 1`,
  `flowLevel ≥ fl₀ ≥ 1` is sufficient.

  Per-dispatch analysis:
  - `saveSimpleKey`: Creates `tokenIndex = current_tokens.size ≥ n₀` (from token monotonicity).
    Preserves stack. ✓
  - Flow open (`scanFlowSequence/MappingStart`): Pushes current simpleKey (which satisfies
    the invariant) to stack at index `stack.size ≥ stackFloor`. Clears simpleKey. ✓
  - Flow close (`scanFlowSequence/MappingEnd`): Restores simpleKey from `stack.back?`.
    Since `stack.size > stackFloor` (from flow level being above floor), the popped entry
    is at index `≥ stackFloor` and satisfies the invariant. Stack shrinks but stays
    `≥ stackFloor`. ✓
  - Other operations: Preserve or clear simpleKey. Preserve stack. ✓

**Impact:** ~30-50 LOC definition + ~100-200 LOC per-step proofs (reusing existing
`ScannerCorrectness` infrastructure for `saveSimpleKey`, `scanFlowStart/End` simpleKey
and stack properties).

**Risk:** MEDIUM-HIGH. Per-dispatch analysis touches every `scanNextToken` branch.
Can reuse `ScannerCorrectness.scanNextToken_preserves_prefix` infrastructure patterns.

***Step 3: Accomplishments***

***Step 3: Reflections***

## Step 4: Prove `FlowMonoChain_preserves_raw_prefix`

**Where:** EmitterScannability.lean

**What:**
- Key theorem:
  ```lean
  theorem FlowMonoChain_preserves_raw_prefix
      {s s' : ScannerState} {n fl₀ : Nat}
      (h_fmc : FlowMonoChain fl₀ s n s')
      (h_sk : s.simpleKey.possible = false)
      (h_fl₀ : fl₀ ≥ 1)
      (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
      (h_stack_floor : SimpleKeyAboveFloor s n₀ s.simpleKeyStack.size)
      (i : Nat) (hi : i < n₀) :
      s'.tokens[i]'(by ...) = s.tokens[i]'(by omega)
  ```
- Proof by induction on `FlowMonoChain`, threading `SimpleKeyAboveFloor`:
  - Base case (`zero`): trivial (same state)
  - Step case: Extract `h_fl : s.flowLevel ≥ fl₀`, use per-step `SimpleKeyAboveFloor`
    preservation (Step 3) to maintain the invariant. Use existing
    `ScannerCorrectness.scanNextToken_preserves_prefix` to preserve token positions
    below `n₀`, since the `SimpleKeyAboveFloor` invariant ensures `setIfInBounds` only
    writes at positions `≥ n₀`.

**Impact:** ~30-60 LOC. The induction is structurally identical to
`ScanChain_preserves_raw_prefix` but uses `SimpleKeyAboveFloor` instead of
`SimpleKeyAbove`.

**Risk:** LOW-MEDIUM. The proof structure mirrors the existing proven
`ScanChain_preserves_raw_prefix`; the only difference is the invariant being threaded.

***Step 4: Accomplishments***

***Step 4: Reflections***

## Step 5: Prove `ScanChain_filtered_prefix` (sorry elimination)

**Where:** EmitterScannability.lean

**What:**
- Change `ScanChain_filtered_prefix` to accept `FlowMonoChain` instead of `ScanChain`:
  ```lean
  theorem ScanChain_filtered_prefix {s s' : ScannerState} {n : Nat}
      (h_chain : FlowMonoChain s.flowLevel s n s')
      (h_sk : s.simpleKey.possible = false) :
      let p := fun (t : Positioned YamlToken) => t.val != .placeholder
      ∃ suffix, (s'.tokens.filter p).toList = (s.tokens.filter p).toList ++ suffix
  ```
  (Or keep accepting `ScanChain` + `FlowMonoChain` separately; design TBD.)
- Proof composition:
  1. `FlowMonoChain_preserves_raw_prefix` (Step 4) → raw prefix preserved
  2. `Array_filter_prefix_of_raw_prefix` → filtered prefix preserved
- Update both call sites (seq L7990, map L8199) to pass the `FlowMonoChain` from
  `EmitListScansInFlow`/`EmitPairListScansInFlow` postconditions

**Impact:** Sorry eliminated. Call site changes are mechanical (extract `FlowMonoChain`
from destructured postconditions).

**Risk:** LOW. Pure composition of proven components.

***Step 5: Accomplishments***

***Step 5: Reflections***

## Step 6: Build verification and VERSION-0.4.7.md update

**Where:** VERSION-0.4.7.md

**What:**
- Verify 429/429 build with sorry count reduced by 1 (11 → 10)
- Update Phase G section with accomplishments/reflections
- Run adversarial tests to confirm regression-free

***Step 6: Accomplishments***

***Step 6: Reflections***

---

## Dependency graph

```
Step 1: FlowMonoChain definition (additive, no impact)
  ↓
Step 2: Thread through EmitScansInFlow (interface change)
  ↓
Step 3: SimpleKeyAboveFloor + per-step preservation (new infrastructure)
  ↓
Step 4: FlowMonoChain_preserves_raw_prefix (key theorem)
  ↓
Step 5: ScanChain_filtered_prefix sorry elimination
  ↓
Step 6: Verification + documentation
```

Steps 1 and 3 are independent and can be developed in parallel.
Step 2 depends on Step 1.
Steps 4-5 depend on Steps 2 and 3.

## Estimated effort

| Step | LOC | Risk |
|------|-----|------|
| 1 | ~40 | LOW |
| 2 | ~100-150 (mostly mechanical) | MEDIUM |
| 3 | ~130-250 | MEDIUM-HIGH |
| 4 | ~30-60 | LOW-MEDIUM |
| 5 | ~10-20 | LOW |
| 6 | ~20 | LOW |
| **Total** | **~330-540** | |
