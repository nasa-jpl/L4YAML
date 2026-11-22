/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-! # The completed-entry key layout, read by the accumulator (item 10)

The `scanValueValidate` T833 guard (line-independent since item 9r) rejects a
`:` whose pending simple key was reserved directly after a `.value` token —
the state a flow entry reaches when it is already complete (`k: v`).  The
emitter-scannability tower consumes the guard's PASSING direction
(`SavedKeyAtEntryBoundary`, `ScanSteps.lean`); this file supplies the FIRING
direction for the production-side accumulation invariant
(`Proofs/Production/StreamAccum.lean`): a state that carries the layout cannot
scan a `:`, which is what turns the `betweenEntries` and `.colon`-tailed cells
of the flow `:` step into refutations.

Three groups:

1. **`KeyAfterValueLayout`** — the facts that make the next `:` throw: the key
   is pending, its reservation slot has a `.value` directly below it, the key
   is strictly behind the cursor (so `scanValueClearKey` cannot clear it), and
   `simpleKeyAllowed` is off (so the next preprocessing cannot mask it with a
   fresh save — which is also why `skipToContentLoop` must not re-enable
   simple keys across breaks inside flow collections, the item-10 scanner
   change).

2. **Preprocessing transport** — in flow, `scanNextToken_preprocess` is
   `skipToContent` (which preserves `simpleKey`, `simpleKeyAllowed` (in flow),
   `explicitKeyLine`, `tokens` and is monotone on `offset`) followed by
   `saveSimpleKey` (identity when `simpleKeyAllowed` is off; a fresh
   reservation at `tokens.size` when it is on and no explicit key suppresses
   it).  The two field suites below are mechanical clones of the
   `_preserves_simpleKey` chain in `ScannerCorrectness.lean` — the originals
   are field-agnostic structural walks — except `skipToContentLoop`'s
   `simpleKeyAllowed` lemma, which is genuinely conditional on the flow level
   because the line-break re-enable is the one writer in the chain.

3. **The refutation** — `no_colon_scan_of_layout`: `scanValue` cannot return
   `.ok` on a state carrying the layout at dispatch time.  The accumulator
   assembles the layout there from the invariant via group 2.
-/

set_option maxHeartbeats 1000000

namespace L4YAML.Proofs.EntryBoundaryLayout

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML
open L4YAML.Scanner
open L4YAML.Proofs.ScannerCorrectness

/-- The pending simple key sits directly after a `.value` token, strictly
    behind the cursor, with fresh saves disabled: the layout a completed flow
    entry leaves behind, and exactly what makes the next `:` throw at
    `scanValueValidate`'s T833 guard. -/
def KeyAfterValueLayout (s : ScannerState) : Prop :=
  s.simpleKey.possible = true ∧
  0 < s.simpleKey.tokenIndex ∧
  (∃ tok, s.tokens[s.simpleKey.tokenIndex - 1]? = some tok ∧ tok.val = .value) ∧
  s.simpleKey.pos.offset < s.offset ∧
  s.simpleKeyAllowed = false ∧
  s.simpleKey.tokenIndex + 1 < s.tokens.size

/-- `flowLevel > 0` in `Bool` form. -/
lemma inFlow_true_of_pos {s : ScannerState} (h : 0 < s.flowLevel) :
    s.inFlow = true := by
  unfold ScannerState.inFlow; exact decide_eq_true h

/-! ## `explicitKeyLine` is preserved by the skip chain -/

lemma advance_preserves_explicitKeyLine (s : ScannerState) :
    s.advance.explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.advance; dsimp only []; split <;> (try split) <;> (try split) <;> rfl

lemma skipSpacesLoop_preserves_explicitKeyLine (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_explicitKeyLine _)
    · rfl

lemma skipWhitespaceLoop_preserves_explicitKeyLine (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_explicitKeyLine _)
      · rfl
    · rfl

lemma skipToEndOfLineLoop_preserves_explicitKeyLine (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_explicitKeyLine _)
    · rfl

lemma skipSpaces_preserves_explicitKeyLine (s : ScannerState) :
    (skipSpaces s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_explicitKeyLine s _

lemma skipWhitespace_preserves_explicitKeyLine (s : ScannerState) :
    (skipWhitespace s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_explicitKeyLine s _

lemma skipToContentWs_preserves_explicitKeyLine (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold skipToContentWs at h
  split at h
  · -- needIndentCheck = true
    simp only [] at h  -- reduce `let s1 := skipSpaces s`
    split at h
    · -- col ≤ currentIndent
      split at h
      · -- peek? = some '\t'
        split at h
        · -- probe.peek? = some '#'
          simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine, skipSpaces_preserves_explicitKeyLine]
        · -- probe.peek? = some c (not '#')
          split at h
          · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine, skipSpaces_preserves_explicitKeyLine]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine, skipSpaces_preserves_explicitKeyLine]
            · simp at h
        · -- probe.peek? = none
          simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine, skipSpaces_preserves_explicitKeyLine]
      · -- peek? ≠ some '\t'
        simp at h; rw [← h, skipSpaces_preserves_explicitKeyLine]
    · -- col > currentIndent
      simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine, skipSpaces_preserves_explicitKeyLine]
  · -- needIndentCheck = false
    simp at h; rw [← h, skipWhitespace_preserves_explicitKeyLine]

lemma skipToEndOfLine_preserves_explicitKeyLine (s : ScannerState) :
    (skipToEndOfLine s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_explicitKeyLine s _

/-- Helper: collectCommentTextLoop preserves explicitKeyLine. -/
lemma collectCommentTextLoop_preserves_explicitKeyLine (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_explicitKeyLine]
    · rfl

lemma skipToContentComment_preserves_explicitKeyLine (s : ScannerState) :
    (skipToContentComment s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_explicitKeyLine, advance_preserves_explicitKeyLine]
      · rfl
  · rfl

lemma consumeNewline_preserves_explicitKeyLine (s : ScannerState) :
    (consumeNewline s).explicitKeyLine = s.explicitKeyLine := by
  unfold consumeNewline
  split
  · exact advance_preserves_explicitKeyLine s
  · simp only []; split
    · exact advance_preserves_explicitKeyLine _
    · exact advance_preserves_explicitKeyLine _
  · rfl

lemma skipToContentLoop_preserves_explicitKeyLine (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · have := ih _ h; rw [this, consumeNewline_preserves_explicitKeyLine,
              skipToContentComment_preserves_explicitKeyLine]; exact skipToContentWs_preserves_explicitKeyLine s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_explicitKeyLine,
              skipToContentComment_preserves_explicitKeyLine]; exact skipToContentWs_preserves_explicitKeyLine s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_explicitKeyLine]
          exact skipToContentWs_preserves_explicitKeyLine s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_explicitKeyLine]
        exact skipToContentWs_preserves_explicitKeyLine s s1 hws

lemma skipToContent_preserves_explicitKeyLine (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.explicitKeyLine = s.explicitKeyLine := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_explicitKeyLine s s' _ h

/-! ## `simpleKeyAllowed` is preserved by the skip chain INSIDE a flow

The one writer in the chain is `skipToContentLoop`'s line-break re-enable,
gated on `!inFlow` (item 10); every other piece copies the flag through
record updates.  The loop induction transports the flow level through each
iteration to keep the gate closed. -/

lemma skipSpacesLoop_preserves_simpleKeyAllowed (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).simpleKeyAllowed = s.simpleKeyAllowed := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_simpleKeyAllowed _)
    · rfl

lemma skipWhitespaceLoop_preserves_simpleKeyAllowed (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).simpleKeyAllowed = s.simpleKeyAllowed := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_simpleKeyAllowed _)
      · rfl
    · rfl

lemma skipToEndOfLineLoop_preserves_simpleKeyAllowed (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).simpleKeyAllowed = s.simpleKeyAllowed := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_simpleKeyAllowed _)
    · rfl

lemma skipSpaces_preserves_simpleKeyAllowed (s : ScannerState) :
    (skipSpaces s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_simpleKeyAllowed s _

lemma skipWhitespace_preserves_simpleKeyAllowed (s : ScannerState) :
    (skipWhitespace s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_simpleKeyAllowed s _

lemma skipToContentWs_preserves_simpleKeyAllowed (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold skipToContentWs at h
  split at h
  · -- needIndentCheck = true
    simp only [] at h  -- reduce `let s1 := skipSpaces s`
    split at h
    · -- col ≤ currentIndent
      split at h
      · -- peek? = some '\t'
        split at h
        · -- probe.peek? = some '#'
          simp at h; rw [← h, skipWhitespace_preserves_simpleKeyAllowed, skipSpaces_preserves_simpleKeyAllowed]
        · -- probe.peek? = some c (not '#')
          split at h
          · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyAllowed, skipSpaces_preserves_simpleKeyAllowed]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyAllowed, skipSpaces_preserves_simpleKeyAllowed]
            · simp at h
        · -- probe.peek? = none
          simp at h; rw [← h, skipWhitespace_preserves_simpleKeyAllowed, skipSpaces_preserves_simpleKeyAllowed]
      · -- peek? ≠ some '\t'
        simp at h; rw [← h, skipSpaces_preserves_simpleKeyAllowed]
    · -- col > currentIndent
      simp at h; rw [← h, skipWhitespace_preserves_simpleKeyAllowed, skipSpaces_preserves_simpleKeyAllowed]
  · -- needIndentCheck = false
    simp at h; rw [← h, skipWhitespace_preserves_simpleKeyAllowed]

lemma skipToEndOfLine_preserves_simpleKeyAllowed (s : ScannerState) :
    (skipToEndOfLine s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_simpleKeyAllowed s _

/-- Helper: collectCommentTextLoop preserves simpleKeyAllowed. -/
lemma collectCommentTextLoop_preserves_simpleKeyAllowed (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.simpleKeyAllowed = s.simpleKeyAllowed := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_simpleKeyAllowed]
    · rfl

lemma skipToContentComment_preserves_simpleKeyAllowed (s : ScannerState) :
    (skipToContentComment s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKeyAllowed, advance_preserves_simpleKeyAllowed]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKeyAllowed, advance_preserves_simpleKeyAllowed]
      · rfl
  · rfl

lemma consumeNewline_preserves_simpleKeyAllowed (s : ScannerState) :
    (consumeNewline s).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold consumeNewline
  split
  · exact advance_preserves_simpleKeyAllowed s
  · simp only []; split
    · exact advance_preserves_simpleKeyAllowed _
    · exact advance_preserves_simpleKeyAllowed _
  · rfl


lemma skipToContentLoop_preserves_simpleKeyAllowed_inFlow (s s' : ScannerState)
    (fuel : Nat) (h_flow : 0 < s.flowLevel)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.simpleKeyAllowed = s.simpleKeyAllowed := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · -- line break: the `!inFlow` gate is closed, so the flag rides through
          split at h
          · -- gate branch `!inFlow = true`: contradicts the transported level
            rename_i hgate
            exfalso
            have h_fl1 : s1.flowLevel = s.flowLevel :=
              skipToContentWs_preserves_flowLevel s s1 hws
            have h_fl3 : (consumeNewline (skipToContentComment s1)).flowLevel
                = s.flowLevel := by
              rw [consumeNewline_preserves_flowLevel,
                  skipToContentComment_preserves_flowLevel, h_fl1]
            rw [Bool.not_eq_true'] at hgate
            unfold ScannerState.inFlow at hgate
            rw [h_fl3] at hgate
            simp at hgate
            omega
          · have h_fl3 : 0 < (consumeNewline (skipToContentComment s1)).flowLevel := by
              rw [consumeNewline_preserves_flowLevel,
                  skipToContentComment_preserves_flowLevel,
                  skipToContentWs_preserves_flowLevel s s1 hws]
              exact h_flow
            have := ih _ h_fl3 h
            rw [this, consumeNewline_preserves_simpleKeyAllowed,
                skipToContentComment_preserves_simpleKeyAllowed]
            exact skipToContentWs_preserves_simpleKeyAllowed s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_simpleKeyAllowed]
          exact skipToContentWs_preserves_simpleKeyAllowed s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_simpleKeyAllowed]
        exact skipToContentWs_preserves_simpleKeyAllowed s s1 hws

lemma skipToContent_preserves_simpleKeyAllowed_inFlow (s s' : ScannerState)
    (h_flow : 0 < s.flowLevel) (h : skipToContent s = .ok s') :
    s'.simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold skipToContent at h
  exact skipToContentLoop_preserves_simpleKeyAllowed_inFlow s s' _ h_flow h

/-! ## `saveSimpleKey`: the two shapes preprocessing hands the dispatch -/

/-- With fresh saves disabled, `saveSimpleKey` is the identity (the
    explicit-key suppression branch is one, too). -/
lemma saveSimpleKey_id_of_not_allowed {s : ScannerState}
    (h : s.simpleKeyAllowed = false) : saveSimpleKey s = s := by
  unfold saveSimpleKey
  split
  · rfl
  · rw [h]; simp

/-- With fresh saves enabled and no explicit key pending, `saveSimpleKey`
    reserves at the incoming array's end: the facts the dispatch-time state
    inherits, stated field-wise. -/
lemma saveSimpleKey_fresh_facts {s : ScannerState}
    (h_a : s.simpleKeyAllowed = true) (h_ek : s.explicitKeyLine = none) :
    (saveSimpleKey s).simpleKey.possible = true ∧
    (saveSimpleKey s).simpleKey.tokenIndex = s.tokens.size ∧
    (∀ i, i < s.tokens.size → (saveSimpleKey s).tokens[i]? = s.tokens[i]?) ∧
    (saveSimpleKey s).simpleKeyAllowed = s.simpleKeyAllowed ∧
    (saveSimpleKey s).offset = s.offset ∧
    (saveSimpleKey s).explicitKeyLine = s.explicitKeyLine ∧
    (saveSimpleKey s).flowLevel = s.flowLevel ∧
    (saveSimpleKey s).simpleKey.pos.offset = s.offset ∧
    (saveSimpleKey s).tokens.size = s.tokens.size + 2 := by
  unfold saveSimpleKey
  rw [h_ek, ite_eq_right (by simp), ite_eq_left h_a]
  refine ⟨rfl, rfl, ?_, rfl, rfl, rfl, rfl, rfl, by simp⟩
  intro i hi
  simp only []
  rw [Array.getElem?_push, Array.getElem?_push]
  simp only [Array.size_push]
  rw [ite_eq_right (by omega), ite_eq_right (by omega)]

/-! ## `scanValueClearKey` cannot clear a completed entry's key -/

/-- No explicit key pending: `scanValueClearKey` is the identity outright. -/
lemma scanValueClearKey_id_of_ekLine_none {s : ScannerState}
    (h : s.explicitKeyLine = none) : scanValueClearKey s = s := by
  unfold scanValueClearKey
  rw [h]

/-- In flow, a key strictly behind the cursor survives `scanValueClearKey`:
    branch (1) tests position equality and branch (2) is block-only. -/
lemma scanValueClearKey_id_of_inFlow_offset_ne {s : ScannerState}
    (h_flow : s.inFlow = true) (h_ne : s.simpleKey.pos.offset ≠ s.offset) :
    scanValueClearKey s = s := by
  unfold scanValueClearKey
  cases h_ek : s.explicitKeyLine with
  | none => rfl
  | some ekLine =>
    dsimp only []
    rw [ite_eq_right (by simp [h_ne]), ite_eq_right (by simp [h_flow])]

/-! ## The T833 guard fires -/

/-- `scanValueValidate` cannot succeed over a completed entry: whatever the
    earlier guards do, the T833 check throws.  (An earlier guard throwing is
    also a refutation — the lemma promises only "not ok".) -/
lemma scanValueValidate_not_ok_of_layout {s : ScannerState}
    (h_flow : s.inFlow = true)
    (h_poss : s.simpleKey.possible = true)
    (h_ti : 0 < s.simpleKey.tokenIndex)
    (h_slot : ∃ tok, s.tokens[s.simpleKey.tokenIndex - 1]? = some tok ∧
      tok.val = .value) :
    ∀ u, scanValueValidate s ≠ .ok u := by
  intro u h
  obtain ⟨tok, h_get, h_val⟩ := h_slot
  unfold scanValueValidate at h
  rw [h_flow] at h
  simp only [h_poss, Bool.not_true, Bool.and_false, Bool.true_and, Bool.false_and,
    ite_false, reduceCtorEq,
    show (decide (s.simpleKey.tokenIndex > 0)) = true from decide_eq_true h_ti,
    Bool.and_true, h_get] at h
  -- check 2 (flow-sequence multiline) is the one condition left: either way,
  -- the chain ends in a throw — check 2's own, or T833's.
  split at h <;> simp [h_val, bind, Except.bind] at h

/-- `scanValue` succeeding means `scanValueValidate` passed on the
    key-cleared state. -/
lemma scanValue_ok_validate_ok {s s' : ScannerState}
    (h : scanValue s = .ok s') :
    scanValueValidate (scanValueClearKey s) = .ok () := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  cases hv : scanValueValidate (scanValueClearKey s) with
  | ok u => cases u; rfl
  | error e => rw [hv] at h; simp at h

/-- **The refutation.**  `scanValue` cannot return `.ok` on a dispatch-time
    state whose pending simple key sits directly after a `.value`, is strictly
    behind the cursor or has no explicit key pending, and is in flow. -/
lemma no_colon_scan_of_layout {s s' : ScannerState}
    (h_flow : s.inFlow = true)
    (h_poss : s.simpleKey.possible = true)
    (h_ti : 0 < s.simpleKey.tokenIndex)
    (h_slot : ∃ tok, s.tokens[s.simpleKey.tokenIndex - 1]? = some tok ∧
      tok.val = .value)
    (h_clear : s.simpleKey.pos.offset ≠ s.offset ∨ s.explicitKeyLine = none)
    (h : scanValue s = .ok s') : False := by
  have h_id : scanValueClearKey s = s := by
    cases h_clear with
    | inl h_ne => exact scanValueClearKey_id_of_inFlow_offset_ne h_flow h_ne
    | inr h_ek => exact scanValueClearKey_id_of_ekLine_none h_ek
  have h_ok := scanValue_ok_validate_ok h
  rw [h_id] at h_ok
  exact scanValueValidate_not_ok_of_layout h_flow h_poss h_ti h_slot () h_ok

/-! ## Preprocessing transport into the dispatch state -/

/-- In flow, preprocessing that yields a character is `skipToContent` followed
    by `saveSimpleKey` — the indent unwind is block-only and the dedent error
    cannot fire on an unchanged stack. -/
lemma preprocess_inFlow_elim {sc s_prep : ScannerState} {c : Char}
    (h_flow : 0 < sc.flowLevel)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ s_skip, skipToContent sc = .ok s_skip ∧ s_prep = saveSimpleKey s_skip := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hsk : skipToContent sc with
  | error e => rw [hsk] at h; exact absurd h (by simp)
  | ok s_skip =>
    rw [hsk] at h
    dsimp only [] at h
    refine ⟨s_skip, rfl, ?_⟩
    have h_gate : (!s_skip.inFlow && s_skip.needIndentCheck) = false := by
      rw [inFlow_true_of_pos (s := s_skip)
        (by rw [skipToContent_preserves_flowLevel sc s_skip hsk]; omega)]
      rfl
    split at h
    · exact absurd h (by simp)
    · simp only [h_gate, Bool.false_eq_true, ite_false] at h
      rw [ite_eq_right (by simp)] at h
      split at h
      · exact absurd h (by simp)
      · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
        rw [← h.1, closeStaleExplicitKey_of_inFlow]
        simp [ScannerState.inFlow, ScannerCorrectness.saveSimpleKey_preserves_flowLevel,
          ScannerCorrectness.skipToContent_preserves_flowLevel sc s_skip hsk, h_flow]

/-- **Cells `.colon` × props and `.value` × `betweenEntries` (items 9n/9o's
    "one shared datum").**  A state carrying `KeyAfterValueLayout` cannot scan
    a `:`: fresh saves are off, so preprocessing hands the dispatch the SAME
    key; the key is strictly behind the (monotone) cursor, so
    `scanValueClearKey` keeps it; T833 fires.

    `s_ad` is the dispatch-time state; the four equalities are what the
    `allowDirectives` update between preprocessing and dispatch preserves
    (all of them, by `split <;> rfl` at the call site). -/
lemma no_colon_dispatch_of_layout {sc s_prep s_ad s' : ScannerState} {c : Char}
    (h_flow : 0 < sc.flowLevel)
    (h_layout : KeyAfterValueLayout sc)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_sk : s_ad.simpleKey = s_prep.simpleKey)
    (h_tk : s_ad.tokens = s_prep.tokens)
    (h_off : s_ad.offset = s_prep.offset)
    (h_fl : s_ad.flowLevel = s_prep.flowLevel)
    (h_sv : scanValue s_ad = .ok s') : False := by
  obtain ⟨h_poss, h_ti, h_slot, h_pos_off, h_allowed, h_rng⟩ := h_layout
  obtain ⟨s_skip, hsk, hsave⟩ := preprocess_inFlow_elim h_flow h_pre
  have h_sk_skip : s_skip.simpleKey = sc.simpleKey :=
    skipToContent_preserves_simpleKey sc s_skip hsk
  have h_al_skip : s_skip.simpleKeyAllowed = false :=
    (skipToContent_preserves_simpleKeyAllowed_inFlow sc s_skip h_flow hsk).trans h_allowed
  have h_id : saveSimpleKey s_skip = s_skip := saveSimpleKey_id_of_not_allowed h_al_skip
  have h_sk_prep : s_prep.simpleKey = sc.simpleKey := by
    rw [hsave, h_id, h_sk_skip]
  have h_tk_prep : s_prep.tokens = sc.tokens := by
    rw [hsave, h_id]; exact skipToContent_preserves_tokens sc s_skip hsk
  have h_off_prep : sc.offset ≤ s_prep.offset := by
    rw [hsave, h_id]; exact skipToContent_offset_ge sc s_skip hsk
  have h_fl_prep : s_prep.flowLevel = sc.flowLevel := by
    rw [hsave, h_id]; exact skipToContent_preserves_flowLevel sc s_skip hsk
  exact no_colon_scan_of_layout
    (inFlow_true_of_pos (s := s_ad) (by rw [h_fl, h_fl_prep]; omega))
    (by rw [h_sk, h_sk_prep]; exact h_poss)
    (by rw [h_sk, h_sk_prep]; exact h_ti)
    (by rw [h_sk, h_sk_prep, h_tk, h_tk_prep]; exact h_slot)
    (Or.inl (by rw [h_sk, h_sk_prep, h_off]; omega))
    h_sv


/-- **Cell `.colon` × white.**  A `:` scanned directly after a `.value` token
    with fresh saves enabled and no explicit key pending: preprocessing's
    fresh reservation lands directly above the `.value`, and T833 fires on the
    fresh key.  This is the same-line half of the strictening's scope
    (`[a: : b]`, `[: :]`, `{a: : b}`); the completed-entry half is
    `no_colon_dispatch_of_layout`. -/
lemma no_colon_dispatch_after_value_fresh {sc s_prep s_ad s' : ScannerState} {c : Char}
    (h_flow : 0 < sc.flowLevel)
    (h_a : sc.simpleKeyAllowed = true)
    (h_ek : sc.explicitKeyLine = none)
    (h_back : ∃ tok, sc.tokens[sc.tokens.size - 1]? = some tok ∧ tok.val = .value)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_sk : s_ad.simpleKey = s_prep.simpleKey)
    (h_tk : s_ad.tokens = s_prep.tokens)
    (h_ekad : s_ad.explicitKeyLine = s_prep.explicitKeyLine)
    (h_fl : s_ad.flowLevel = s_prep.flowLevel)
    (h_sv : scanValue s_ad = .ok s') : False := by
  obtain ⟨tok, h_get, h_val⟩ := h_back
  have h_sz : 0 < sc.tokens.size := by
    cases hsz : sc.tokens.size with
    | zero =>
      have hnone : sc.tokens[sc.tokens.size - 1]? = none :=
        Array.getElem?_eq_none (by omega)
      rw [hnone] at h_get
      exact absurd h_get (by simp)
    | succ n => omega
  obtain ⟨s_skip, hsk, hsave⟩ := preprocess_inFlow_elim h_flow h_pre
  have h_al_skip : s_skip.simpleKeyAllowed = true :=
    (skipToContent_preserves_simpleKeyAllowed_inFlow sc s_skip h_flow hsk).trans h_a
  have h_ek_skip : s_skip.explicitKeyLine = none :=
    (skipToContent_preserves_explicitKeyLine sc s_skip hsk).trans h_ek
  have h_tk_skip : s_skip.tokens = sc.tokens :=
    skipToContent_preserves_tokens sc s_skip hsk
  obtain ⟨hf_poss, hf_ti, hf_pref, _hf_al, _hf_off, hf_ek, hf_fl, _hf_pos, _hf_sz⟩ :=
    saveSimpleKey_fresh_facts h_al_skip h_ek_skip
  exact no_colon_scan_of_layout
    (inFlow_true_of_pos (s := s_ad) (by
      rw [h_fl, hsave, hf_fl, skipToContent_preserves_flowLevel sc s_skip hsk]; omega))
    (by rw [h_sk, hsave]; exact hf_poss)
    (by rw [h_sk, hsave, hf_ti, h_tk_skip]; omega)
    (by
      refine ⟨tok, ?_, h_val⟩
      rw [h_sk, h_tk, hsave, hf_ti, h_tk_skip,
          hf_pref (sc.tokens.size - 1) (by rw [h_tk_skip]; omega), h_tk_skip]
      exact h_get)
    (Or.inr (by rw [h_ekad, hsave, hf_ek]; exact h_ek_skip))
    h_sv

/-- The layout survives any step that keeps the pending key, preserves the
    slots below its reservation, does not retreat the cursor, and keeps fresh
    saves off — a property-run extension, for instance. -/
lemma KeyAfterValueLayout.transport {s s' : ScannerState}
    (h : KeyAfterValueLayout s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_pref : ∀ i, i < s.simpleKey.tokenIndex → s'.tokens[i]? = s.tokens[i]?)
    (h_off : s.offset ≤ s'.offset)
    (h_al : s'.simpleKeyAllowed = false)
    (h_size : s.tokens.size ≤ s'.tokens.size) :
    KeyAfterValueLayout s' := by
  obtain ⟨h1, h2, ⟨tok, h3, h4⟩, h5, _, h6⟩ := h
  refine ⟨by rw [h_sk]; exact h1, by rw [h_sk]; exact h2,
    ⟨tok, ?_, h4⟩, by rw [h_sk]; omega, h_al, by rw [h_sk]; omega⟩
  rw [h_sk, h_pref _ (by omega)]
  exact h3

/-! ## Property scans leave fresh saves off

Every `.ok` exit of `scanAnchorOrAlias` and `scanTag` is a record update with
`simpleKeyAllowed := false` — the other half of what keeps a completed
entry's layout alive under a held property run. -/

lemma scanAnchorOrAlias_simpleKeyAllowed_false {s s' : ScannerState}
    {isAnchor : Bool} (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.simpleKeyAllowed = false := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; rfl

lemma scanTag_simpleKeyAllowed_false {s s' : ScannerState}
    (hok : scanTag s = .ok s') : s'.simpleKeyAllowed = false := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [pure, Except.pure] at hok
      have h := Except.ok.inj hok; subst h; rfl
  · have h := Except.ok.inj hok; subst h; rfl
  · have h := Except.ok.inj hok; subst h; rfl

/-! ## In BLOCK context the save is the other way round (DOCS item 34)

Everything above is about keeping a key ALIVE across preprocessing, which is a
flow-context concern: inside a flow collection a break must not re-arm fresh
saves, or the reservation the entry boundary depends on gets masked.  Item 34
needs the opposite direction, and in block context it is unconditional.

`simpleKeyAllowed` only ever goes UP across the walk — `skipToContentLoop`
re-arms it on every break outside a flow and no piece of the walk ever clears
it — so a state that arrives at preprocessing with fresh saves enabled hands
`saveSimpleKey` a state with fresh saves enabled, whatever the step crossed.
And in block context `saveSimpleKey`'s suppression branch (`inFlow &&
explicitKeyLine == some line`) is closed outright, so the save happens: the
dispatch-time state carries a key AT the cursor.

That is what sends `scanValueIndentTabCheck`'s test to the run in front of the
`:` (`scanValue_tab_run_ne`, `PreprocessIndentStable`), and every block
indicator's scan leaves `simpleKeyAllowed := true` behind it — so a pending
parked at an indicator can carry the hypothesis as a field and spend it one
step later. -/

/-- The unwind writes `tokens` and `indents`. -/
lemma unwindIndentsLoop_preserves_simpleKeyAllowed (s : ScannerState) (col : Int)
    (fuel : Nat) :
    (unwindIndentsLoop s col fuel).simpleKeyAllowed = s.simpleKeyAllowed := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; simp [ScannerState.emit]
    · rfl

lemma unwindIndents_preserves_simpleKeyAllowed (s : ScannerState) (col : Int) :
    (unwindIndents s col).simpleKeyAllowed = s.simpleKeyAllowed := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_simpleKeyAllowed s col _

/-- **Fresh saves only go up across the walk.**  The block branch of the break
    sets the flag; every other piece of `skipToContentLoop` preserves it.  No
    flow hypothesis: this is the direction that holds on both sides. -/
lemma skipToContentLoop_simpleKeyAllowed_mono (s s' : ScannerState) (fuel : Nat)
    (h_a : s.simpleKeyAllowed = true) (h : skipToContentLoop s fuel = .ok s') :
    s'.simpleKeyAllowed = true := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]; exact h_a
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      have h_a1 : s1.simpleKeyAllowed = true :=
        (skipToContentWs_preserves_simpleKeyAllowed s s1 hws).trans h_a
      have h_a2 : (skipToContentComment s1).simpleKeyAllowed = true :=
        (skipToContentComment_preserves_simpleKeyAllowed s1).trans h_a1
      simp only [] at h
      split at h
      · split at h
        · split at h
          · exact ih _ rfl h
          · exact ih _ ((consumeNewline_preserves_simpleKeyAllowed _).trans h_a2) h
        · simp at h; rw [← h]; exact h_a2
      · simp at h; rw [← h]; exact h_a2

lemma skipToContent_simpleKeyAllowed_mono (s s' : ScannerState)
    (h_a : s.simpleKeyAllowed = true) (h : skipToContent s = .ok s') :
    s'.simpleKeyAllowed = true := by
  unfold skipToContent at h
  exact skipToContentLoop_simpleKeyAllowed_mono s s' _ h_a h

lemma saveSimpleKey_inFlow (s : ScannerState) :
    (saveSimpleKey s).inFlow = s.inFlow := by
  unfold saveSimpleKey ScannerState.inFlow
  split
  · rfl
  · split <;> rfl

/-- **The block save, without the `explicitKeyLine` side condition.**  The
    suppression branch is `inFlow &&  …`, so outside a flow the flag alone
    decides — and `? a : b`, where an explicit key IS pending, is precisely a
    shape that must still record its compact key. -/
lemma saveSimpleKey_fresh_block {s : ScannerState}
    (h_a : s.simpleKeyAllowed = true) (h_flow : s.inFlow = false) :
    (saveSimpleKey s).simpleKey.possible = true ∧
    (saveSimpleKey s).simpleKey.pos.offset = s.offset ∧
    (saveSimpleKey s).offset = s.offset := by
  unfold saveSimpleKey
  rw [ite_eq_right (by simp [h_flow]), ite_eq_left h_a]
  exact ⟨rfl, rfl, rfl⟩

/-- Preprocessing, in the shape the block context reads it: the walk, then the
    armed unwind or nothing, then the save, then the stale-register reset
    (item 333 — a projection-transparent wrapper, `closeStaleExplicitKey_*`). -/
lemma preprocess_save_elim {sc s_prep : ScannerState} {c : Char}
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ s_u s_skip, skipToContent sc = .ok s_skip ∧
      s_prep = closeStaleExplicitKey (saveSimpleKey s_u) ∧
      (s_u = s_skip ∨
        s_u = { unwindIndents s_skip s_skip.col with needIndentCheck := false }) := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hsk : skipToContent sc with
  | error e => rw [hsk] at h; exact absurd h (by simp)
  | ok s_skip =>
    rw [hsk] at h
    dsimp only [] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨_, s_skip, rfl, h.1.symm, Or.inr rfl⟩
      · split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            exact ⟨_, s_skip, rfl, h.1.symm, Or.inl rfl⟩

/-- **A key AT the cursor, from the flag alone** (item 34).  What the `:` scan's
    tab test needs, and what a pending parked at a block indicator can carry. -/
lemma preprocess_saved_key_at_cursor {sc s_prep : ScannerState} {c : Char}
    (h_a : sc.simpleKeyAllowed = true)
    (h_noflow : s_prep.inFlow = false)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKey.possible = true ∧
    s_prep.simpleKey.pos.offset = s_prep.offset := by
  obtain ⟨s_u, s_skip, hsk, h_save, h_cases⟩ := preprocess_save_elim h
  have h_al_skip : s_skip.simpleKeyAllowed = true :=
    skipToContent_simpleKeyAllowed_mono sc s_skip h_a hsk
  have h_al : s_u.simpleKeyAllowed = true := by
    rcases h_cases with rfl | rfl
    · exact h_al_skip
    · show (unwindIndents s_skip s_skip.col).simpleKeyAllowed = true
      rw [unwindIndents_preserves_simpleKeyAllowed]; exact h_al_skip
  have h_fl : s_u.inFlow = false := by
    rw [← saveSimpleKey_inFlow s_u, ← closeStaleExplicitKey_inFlow, ← h_save]; exact h_noflow
  obtain ⟨h_poss, h_pos, h_off⟩ := saveSimpleKey_fresh_block h_al h_fl
  exact ⟨by rw [h_save, closeStaleExplicitKey_simpleKey]; exact h_poss,
    by rw [h_save, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_offset, h_pos, h_off]⟩

/-- **The fresh save's whole position** (item 90) — `preprocess_saved_key_at_cursor`
    at the record rather than the offset.  This is the pair the implicit-key
    pack producers destructure, so the flag alone decides
    `preprocess_some_savedKey_shape`'s arm: outside a flow the save declines
    only with the flag down, and every pack producer's park carries it up. -/
lemma preprocess_saved_key_fresh {sc s_prep : ScannerState} {c : Char}
    (h_a : sc.simpleKeyAllowed = true)
    (h_noflow : s_prep.inFlow = false)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.simpleKey.possible = true ∧
    s_prep.simpleKey.pos = s_prep.currentPos := by
  obtain ⟨s_u, s_skip, hsk, h_save, h_cases⟩ := preprocess_save_elim h
  have h_al_skip : s_skip.simpleKeyAllowed = true :=
    skipToContent_simpleKeyAllowed_mono sc s_skip h_a hsk
  have h_al : s_u.simpleKeyAllowed = true := by
    rcases h_cases with rfl | rfl
    · exact h_al_skip
    · show (unwindIndents s_skip s_skip.col).simpleKeyAllowed = true
      rw [unwindIndents_preserves_simpleKeyAllowed]; exact h_al_skip
  have h_fl : s_u.inFlow = false := by
    rw [← saveSimpleKey_inFlow s_u, ← closeStaleExplicitKey_inFlow, ← h_save]; exact h_noflow
  rw [h_save, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_currentPos]
  unfold saveSimpleKey
  rw [ite_eq_right (by simp [h_fl]), ite_eq_left h_al]
  exact ⟨rfl, rfl⟩

end L4YAML.Proofs.EntryBoundaryLayout

end Blanket
