/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.StreamStart

/-! # `IndexedScannerCorrectness.OrderedDefs` — §8.1–§8.2

`ScanInvIx` / `AllKeysValidIx` definitions + monotonicity helpers
(both the full-token-equality `_mono` family and the
position-preserving `_mono_pos` family needed for `overwriteAtCursor`
chains in `scanValuePrepareIx`).

Split out of `IndexedScannerCorrectness.lean` (Reflection 112). -/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.ScannerCorrectness

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.WellBehaved
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ## §8  `ScanInvIx` + `AllKeysValidIx` infrastructure
(partial — `scanIx_positions_ordered_axiom` discharge scheduled for
`6f.3b3.primitives.ordered.compose.value` and downstream sub-steps)

Lays the foundation for porting the legacy `ScanInv` / `AllKeysValid`
compound-invariant chain (`ScannerCorrectness.lean:6520` / `:8781`)
and the loop induction `scanLoop_ordered`
(`ScannerCorrectness.lean:9405`). This file now lands:

  • §8.1 invariant definitions
  • §8.2–§8.3 primitive preservation
  • §8.4–§8.5 skipToContent / unwindIndents / saveSimpleKey ScanInvIx,
    skipToContent / unwindIndents AllKeysValidIx,
    push*IndentIx ScanInvIx
  • §8.6 `saveSimpleKeyIx_preserves_AllKeysValidIx`
  • §8.7.1 `flowStartIx` / `flowEndIx` AllKeysValidIx helpers
  • §8.7.2 5 flow indicator helpers × 2 invariants
  • §8.7.3 `scanBlockEntryIx` / `scanKeyIx` × 2 invariants
  • §8.7.4 `scanValueClearKeyIx` × ScanInvIx + SimpleKeyValidIx + AllKeysValidIx
  • §8.7.5 `scanDocumentStartIx` / `scanDocumentEndIx` AllKeysValidIx

The remaining `scanValuePrepareIx` / `scanValueIx` ScanInvIx +
AllKeysValidIx, `scanDocumentStart/End` ScanInvIx, directive +
anchor/tag helpers, all 5 dispatchers, top-level `scanNextTokenIx`
preservation, the `scanLoopIx_ordered` fuel induction, and the final
`scanIx_positions_ordered` discharge are scheduled for the next
sub-step (`6f.3b3.primitives.ordered.compose.value`).

The Reflection 110 budget revision documents the ~3× over-run pattern
observed across `6f.3b3.primitives.tractable` /
`6f.3b3.primitives.streamStart` / this session — porting per-dispatcher
preservation chains into the indexed substrate takes ~3× the LOC
estimate of corresponding legacy proofs (each helper now requires a
cursor/offset-bound proof IN ADDITION TO the prefix preservation that
the legacy proofs already had).

**Architecture** mirrors the legacy proof:

  1. `ScanInv'Ix tokens off` = positions ordered ∧ all start.offsets ≤ off.
     `ScanInvIx s := ScanInv'Ix s.tokens s.cursor.pos.offset`.
  2. `SimpleKeyValidIx` / `SimpleKeyStackValidIx` / `AllKeysValidIx`:
     when `simpleKey.possible = true`, the saved tokenIndex points at a
     pair of slots whose `.start = simpleKey.pos`. Required to handle
     `overwriteAtCursor` calls in `scanKeyIx` / `scanValueIx` (those
     overwrites only preserve `ScanInvIx` because the slot already had
     `.start = sk.pos`).
  3. Primitive preservation of these invariants under `emit`, `emitAt`,
     `advance`, field updates, and `setIfInBounds`.
  4. Per-helper preservation (delegating to the existing per-helper
     `_preserves_prefix` / `_offset_monotonic` bricks from
     `IndexedScannerPlainScalarValid` + `IndexedDispatch`).
  5. Per-dispatcher preservation (structural / flow / block / content).
  6. `scanNextTokenIx_preserves_ScanInvIx` and
     `scanNextTokenIx_preserves_AllKeysValidIx` (top-level composition).
  7. `scanLoopIx_ordered` by induction on fuel; `scanIx_positions_ordered`
     applied to the post-BOM initial state.

The invariants are propagated **as a pair** (ScanInv + AllKeysValid)
since `scanValueIx_preserves_ScanInvIx` depends on `SimpleKeyValidIx`
to bound the `overwriteAtCursor` slot's `.start` (legacy structure;
`ScannerCorrectness.lean:9364`). -/

/-! ### §8.1  Definitions: `ScanInv'Ix`, `ScanInvIx`, `SimpleKeyValidIx`,
`SimpleKeyStackValidIx`, `AllKeysValidIx`.

Indexed twins of legacy `ScanInv'` (`ScannerCorrectness.lean:6520`),
`ScanInv` (`:6525`), `SimpleKeyValid` (`:8627`), `SimpleKeyStackValid`
(`:8770`), `AllKeysValid` (`:8781`). Re-stated in terms of
`IxToken.start` rather than legacy `Positioned.pos`. -/

/-- Compound positional invariant on a token stream: positions are
    ordered AND all start offsets are ≤ `off`. Phrased over a raw
    `Indexed.TokenStream input` so that we can `rw` tokens/offset
    fields independently in preservation proofs. -/
def ScanInv'Ix {input : String} (tokens : Indexed.TokenStream input) (off : Nat) : Prop :=
  (∀ i j : Fin tokens.tokens.size, i.val < j.val →
    (tokens.tokens[i]).start.offset ≤ (tokens.tokens[j]).start.offset) ∧
  (∀ i : Fin tokens.tokens.size, (tokens.tokens[i]).start.offset ≤ off)

/-- State-level scanner positional invariant: tokens ordered, all bounded
    by the cursor's byte offset. Indexed twin of legacy `ScanInv`
    (`ScannerCorrectness.lean:6525`). -/
def ScanInvIx {input : String} (s : ScannerStateIx input) : Prop :=
  ScanInv'Ix s.tokens s.cursor.pos.offset

/-- Simple-key validity: when the simpleKey is `possible`, the saved
    `tokenIndex` and `tokenIndex+1` are in-bounds and the tokens at
    those positions carry `.start = simpleKey.pos`. Indexed twin of
    legacy `SimpleKeyValid` (`ScannerCorrectness.lean:8627`). -/
def SimpleKeyValidIx {input : String} (s : ScannerStateIx input) : Prop :=
  s.simpleKey.possible = true →
    s.simpleKey.tokenIndex < s.tokens.tokens.size ∧
    s.simpleKey.tokenIndex + 1 < s.tokens.tokens.size ∧
    (∀ (h1 : s.simpleKey.tokenIndex < s.tokens.tokens.size),
      (s.tokens.tokens[s.simpleKey.tokenIndex]).start = s.simpleKey.pos) ∧
    (∀ (h2 : s.simpleKey.tokenIndex + 1 < s.tokens.tokens.size),
      (s.tokens.tokens[s.simpleKey.tokenIndex + 1]).start = s.simpleKey.pos)

/-- Stack-side simple-key validity: every entry of `simpleKeyStack`
    that is `possible` has in-bounds `tokenIndex` and the saved tokens
    carry `.start = stackEntry.pos`. Indexed twin of legacy
    `SimpleKeyStackValid` (`ScannerCorrectness.lean:8770`). -/
def SimpleKeyStackValidIx {input : String} (s : ScannerStateIx input) : Prop :=
  ∀ j (h : j < s.simpleKeyStack.size),
    (s.simpleKeyStack[j]'h).possible = true →
    (s.simpleKeyStack[j]'h).tokenIndex < s.tokens.tokens.size ∧
    (s.simpleKeyStack[j]'h).tokenIndex + 1 < s.tokens.tokens.size ∧
    (∀ (h1 : (s.simpleKeyStack[j]'h).tokenIndex < s.tokens.tokens.size),
      (s.tokens.tokens[(s.simpleKeyStack[j]'h).tokenIndex]).start = (s.simpleKeyStack[j]'h).pos) ∧
    (∀ (h2 : (s.simpleKeyStack[j]'h).tokenIndex + 1 < s.tokens.tokens.size),
      (s.tokens.tokens[(s.simpleKeyStack[j]'h).tokenIndex + 1]).start = (s.simpleKeyStack[j]'h).pos)

/-- Combined simple-key validity for both current and stacked keys.
    Indexed twin of legacy `AllKeysValid`
    (`ScannerCorrectness.lean:8781`). -/
def AllKeysValidIx {input : String} (s : ScannerStateIx input) : Prop :=
  SimpleKeyValidIx s ∧ SimpleKeyStackValidIx s

/-! ### §8.2  Monotonicity helpers and trivial preservation lemmas

Indexed twins of legacy `SimpleKeyValid_mono` / `SimpleKeyStackValid_mono`
/ `AllKeysValid_mono` / `AllKeysValid_of_cleared_current` and the
`ScanInv` "cleared/identity" companions. -/

lemma SimpleKeyValidIx_of_not_possible {input : String}
    (s : ScannerStateIx input)
    (h : s.simpleKey.possible = false) : SimpleKeyValidIx s :=
  fun h_poss => absurd h_poss (by simp [h])

lemma SimpleKeyValidIx_mono {input : String} (s s' : ScannerStateIx input)
    (h_skv : SimpleKeyValidIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(by omega) = s.tokens.tokens[i]) :
    SimpleKeyValidIx s' := by
  intro h_poss
  rw [h_sk] at h_poss ⊢
  have ⟨hb1, hb2, hp1, hp2⟩ := h_skv h_poss
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h1; rw [h_pref _ hb1]; exact hp1 hb1
  · intro h2; rw [h_pref _ hb2]; exact hp2 hb2

lemma SimpleKeyStackValidIx_mono {input : String} (s s' : ScannerStateIx input)
    (h_ssv : SimpleKeyStackValidIx s)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(by omega) = s.tokens.tokens[i]) :
    SimpleKeyStackValidIx s' := by
  intro j hj h_poss
  have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj_s) := by
    simp [h_stack]
  rw [h_get] at h_poss ⊢
  have ⟨hb1, hb2, hp1, hp2⟩ := h_ssv j hj_s h_poss
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro h1; rw [h_pref _ hb1]; exact hp1 hb1
  · intro h2; rw [h_pref _ hb2]; exact hp2 hb2

lemma AllKeysValidIx_mono {input : String} (s s' : ScannerStateIx input)
    (h_akv : AllKeysValidIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(by omega) = s.tokens.tokens[i]) :
    AllKeysValidIx s' :=
  ⟨SimpleKeyValidIx_mono s s' h_akv.1 h_sk h_mono h_pref,
   SimpleKeyStackValidIx_mono s s' h_akv.2 h_stack h_mono h_pref⟩

lemma AllKeysValidIx_of_cleared {input : String} (s' : ScannerStateIx input)
    (h_poss : s'.simpleKey.possible = false)
    (h_ssv : SimpleKeyStackValidIx s')
    : AllKeysValidIx s' :=
  ⟨SimpleKeyValidIx_of_not_possible s' h_poss, h_ssv⟩

/-! ### §8.2'  Position-preserving mono helpers.

The `_mono` family above requires *full token equality* on the prefix
(`s'.tokens[i] = s.tokens[i]`). The `_mono_pos` family weakens that to
*`.start`-only equality* — sufficient for `SimpleKeyValidIx` /
`SimpleKeyStackValidIx`, which only mention `.start`, and necessary for
`overwriteAtCursor`-chained helpers like `scanValuePrepareIx` (which
*do* change the token's `.kind` field while preserving `.start`).

Indexed twin of legacy `SimpleKeyStackValid_mono_pos`
(`ScannerCorrectness.lean:8803`). -/

lemma SimpleKeyValidIx_mono_pos {input : String} (s s' : ScannerStateIx input)
    (h_skv : SimpleKeyValidIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref_start : ∀ i (h : i < s.tokens.tokens.size),
      (s'.tokens.tokens[i]'(by omega)).start = (s.tokens.tokens[i]).start) :
    SimpleKeyValidIx s' := by
  intro h_poss
  rw [h_sk] at h_poss ⊢
  have ⟨hb1, hb2, hp1, hp2⟩ := h_skv h_poss
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro _h1; rw [h_pref_start _ hb1]; exact hp1 hb1
  · intro _h2; rw [h_pref_start _ hb2]; exact hp2 hb2

lemma SimpleKeyStackValidIx_mono_pos {input : String} (s s' : ScannerStateIx input)
    (h_ssv : SimpleKeyStackValidIx s)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref_start : ∀ i (h : i < s.tokens.tokens.size),
      (s'.tokens.tokens[i]'(by omega)).start = (s.tokens.tokens[i]).start) :
    SimpleKeyStackValidIx s' := by
  intro j hj h_poss
  have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj_s) := by
    simp [h_stack]
  rw [h_get] at h_poss ⊢
  have ⟨hb1, hb2, hp1, hp2⟩ := h_ssv j hj_s h_poss
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro _h1; rw [h_pref_start _ hb1]; exact hp1 hb1
  · intro _h2; rw [h_pref_start _ hb2]; exact hp2 hb2

lemma AllKeysValidIx_mono_pos {input : String} (s s' : ScannerStateIx input)
    (h_akv : AllKeysValidIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref_start : ∀ i (h : i < s.tokens.tokens.size),
      (s'.tokens.tokens[i]'(by omega)).start = (s.tokens.tokens[i]).start) :
    AllKeysValidIx s' :=
  ⟨SimpleKeyValidIx_mono_pos s s' h_akv.1 h_sk h_mono h_pref_start,
   SimpleKeyStackValidIx_mono_pos s s' h_akv.2 h_stack h_mono h_pref_start⟩

/-- `ScanInvIx` is preserved by field updates that touch neither tokens
    nor the cursor offset. -/
lemma ScanInvIx_of_field_update {input : String} (s s' : ScannerStateIx input)
    (h : ScanInvIx s)
    (h_tok : s'.tokens = s.tokens)
    (h_off : s'.cursor.pos.offset = s.cursor.pos.offset) :
    ScanInvIx s' := by
  unfold ScanInvIx ScanInv'Ix
  rw [h_tok, h_off]; exact h

/-- `ScanInvIx` is preserved by field updates that only INCREASE
    `cursor.pos.offset` (and leave tokens unchanged). -/
lemma ScanInvIx_of_offset_ge {input : String} (s s' : ScannerStateIx input)
    (h : ScanInvIx s)
    (h_tok : s'.tokens = s.tokens)
    (h_off : s.cursor.pos.offset ≤ s'.cursor.pos.offset) :
    ScanInvIx s' := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix; rw [h_tok]
  refine ⟨h_ord, ?_⟩
  intro ⟨i, hi⟩
  exact Nat.le_trans (h_bnd ⟨i, hi⟩) h_off
end L4YAML.Proofs.Indexed.ScannerCorrectness
