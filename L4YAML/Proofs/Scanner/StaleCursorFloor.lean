/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.ScalarWalkColFloor
public import L4YAML.Proofs.Scanner.FlowIndentStable
public import L4YAML.Proofs.Scanner.LineOpenGuard
public import L4YAML.Proofs.Scanner.PropsRunLineCoupling
public import L4YAML.Proofs.Scanner.EntryBoundaryLayout
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-! # The stale-cursor floor (DOCS item 123)

**A block-context cursor that carries a live simple-key candidate saved on an
earlier line stands strictly past `currentIndent`.**  This is item 122's
corrected U1, stated as one scanner-wide invariant over `scanNextToken`
boundary states and preserved by every step:

* the scalar walks — the only stale-live makers in block context — pay their
  own way: a cross-line exit clears the floor (`ScalarWalkColFloor`'s
  exports), and a same-line exit only moves the column right (`§3b` there);
* preprocessing cannot break it: a block break-crossing re-arms
  `simpleKeyAllowed` (`skipToContentLoop`) so `saveSimpleKey` overwrites the
  key AT the landing — same line, premise refuted — while a same-line pass
  only moves the column right and, under the floor itself, leaves the armed
  unwind with nothing to pop;
* a flow close that lands back in block context restores a stacked key, but
  the `]`/`}` it consumed cleared the structural dispatcher's own flow floor
  (`FlowIndentStable.structural_none_col_gt_of_inFlow`), which is the same
  bound one column earlier;
* everything else clears the key, saves fresh on the cursor's own line, or
  stays inside a flow, where the invariant claims nothing.

The consumer is `[197]`'s deferred pair at the stale-key `:` (item 104's
punt in `StreamAccum`): the pair's decidable half is a CURSOR fact —
`(col : Int) = currentIndent` — and this floor refutes it. -/

set_option autoImplicit false

namespace L4YAML.Proofs.StaleCursorFloor

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.ScannerCorrectness
open L4YAML.Proofs.ScalarWalkColFloor
open L4YAML.Proofs.FlowIndentStable
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.PropsRunLineCoupling
open L4YAML.Proofs.EntryBoundaryLayout
open L4YAML.Proofs.FlowAdjacency (peel_flowAdj)
open L4YAML.Proofs.BlockScalarFlowGuard (peel_blockScalarGuard)
open L4YAML.Proofs.ScalarProduction (consumeNewline_line_succ)

/-! ## §1  The invariant -/

/-- **The stale-cursor floor.**  In block context, a live saved key from an
    earlier line puts the cursor strictly past the enclosing block indent. -/
def StaleKeyCursorFloor (s : ScannerState) : Prop :=
  s.inFlow = false → s.simpleKey.possible = true →
    s.simpleKey.pos.line ≠ s.line → s.currentIndent < (s.col : Int)

/-- A cleared key satisfies the floor vacuously. -/
lemma StaleKeyCursorFloor.of_cleared {s : ScannerState}
    (h : s.simpleKey.possible = false) : StaleKeyCursorFloor s := by
  intro _ h_poss _
  rw [h] at h_poss; cases h_poss

/-- A key on the cursor's own line satisfies the floor vacuously. -/
lemma StaleKeyCursorFloor.of_key_line {s : ScannerState}
    (h : s.simpleKey.possible = true → s.simpleKey.pos.line = s.line) :
    StaleKeyCursorFloor s := by
  intro _ h_poss h_ne
  exact absurd (h h_poss) h_ne

/-- An established floor satisfies the invariant outright. -/
lemma StaleKeyCursorFloor.of_floor {s : ScannerState}
    (h : s.currentIndent < (s.col : Int)) : StaleKeyCursorFloor s :=
  fun _ _ _ => h

/-- A flow-interior state satisfies the floor vacuously. -/
lemma StaleKeyCursorFloor.of_inFlow {s : ScannerState}
    (h : s.inFlow = true) : StaleKeyCursorFloor s := by
  intro h_nf
  rw [h] at h_nf; cases h_nf

/-- The initial state: no key is live. -/
lemma StaleKeyCursorFloor.initial (input : String) :
    StaleKeyCursorFloor (ScannerState.mk' input) :=
  .of_cleared (by unfold ScannerState.mk'; rfl)

/-- Seed transfer: a step that touches neither the key, the cursor, the
    indents nor the flow level carries the floor (the `emit`/`consumeBOM`
    seeds). -/
lemma StaleKeyCursorFloor_of_fields_eq {s s' : ScannerState}
    (h : StaleKeyCursorFloor s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_line : s'.line = s.line) (h_col : s'.col = s.col)
    (h_ind : s'.indents = s.indents) (h_fl : s'.flowLevel = s.flowLevel) :
    StaleKeyCursorFloor s' := by
  intro h_nf h_poss h_ne
  have h_ci : s'.currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [h_ind]
  rw [h_ci, h_col]
  exact h (by unfold ScannerState.inFlow at h_nf ⊢; rw [← h_fl]; exact h_nf)
    (by rw [← h_sk]; exact h_poss)
    (by rw [← h_sk, ← h_line]; exact h_ne)

/-! ## §2  Preprocessing preserves the floor

`skipToContent` either stays on the line (column moves right, indents
untouched) or crosses a break — and a block break re-arms `simpleKeyAllowed`,
so the save that follows is FRESH at the landing.  The armed unwind, under
the floor itself, has nothing to pop. -/

/-- `s-space*` moves the column only. -/
private lemma skipSpacesLoop_col_ge (s : ScannerState) (fuel : Nat) :
    s.col ≤ (skipSpacesLoop s fuel).col := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · rename_i hpk
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpk (by decide)]; omega
        _ ≤ _ := ih s.advance
    · exact Nat.le_refl _

private lemma skipSpaces_col_ge (s : ScannerState) :
    s.col ≤ (skipSpaces s).col := by
  unfold skipSpaces; exact skipSpacesLoop_col_ge s _

/-- `c-nb-comment-text` admits no break: the collect moves the column only. -/
lemma collectCommentTextLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (text : String),
    s.col ≤ (collectCommentTextLoop s text fuel).2.col := by
  induction fuel with
  | zero => intro s text; unfold collectCommentTextLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · rename_i c hpk
      split
      · exact Nat.le_refl _
      · rename_i hnb
        calc s.col ≤ s.advance.col := by
              rw [advance_col_succ_of_peek hpk (by simpa using hnb)]; omega
          _ ≤ _ := ih s.advance (text.push c)
    · exact Nat.le_refl _

lemma skipToContentComment_col_ge (s : ScannerState) :
    s.col ≤ (skipToContentComment s).col := by
  unfold skipToContentComment
  split
  · rename_i hpk
    dsimp only []
    generalize h_c : collectCommentTextLoop s.advance ""
      (s.advance.inputEnd - s.advance.offset) = res
    have h_ge := collectCommentTextLoop_col_ge
      (s.advance.inputEnd - s.advance.offset) s.advance ""
    rw [h_c] at h_ge
    have h_adv : s.col ≤ s.advance.col := by
      rw [advance_col_succ_of_peek hpk (by decide)]; omega
    repeat' split
    all_goals first
      | exact Nat.le_trans h_adv h_ge
      | exact Nat.le_refl _
  · exact Nat.le_refl _

/-- The whitespace phase moves the column only. -/
lemma skipToContentWs_col_ge {s s' : ScannerState}
    (h : skipToContentWs s = .ok s') : s.col ≤ s'.col := by
  unfold skipToContentWs at h
  dsimp only [] at h
  repeat' split at h
  all_goals first
    | (injection h with h_eq; subst h_eq; first
        | exact Nat.le_trans (skipSpaces_col_ge s) (skipWhitespace_col_ge _)
        | exact skipSpaces_col_ge s
        | exact skipWhitespace_col_ge s)
    | injection h

/-- The whole skip never returns to an earlier line. -/
lemma skipToContentLoop_line_ge (fuel : Nat) :
    ∀ {s s' : ScannerState}, skipToContentLoop s fuel = .ok s' →
    s.line ≤ s'.line := by
  induction fuel with
  | zero =>
    intro s s' h
    unfold skipToContentLoop at h
    injection h with h_eq; subst h_eq; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s s' h
    unfold skipToContentLoop at h
    split at h
    · cases h
    · rename_i s1 hws
      have h_l1 : s1.line = s.line := skipToContentWs_preserves_line s s1 hws
      have h_l2 : (skipToContentComment s1).line = s1.line :=
        skipToContentComment_preserves_line s1
      dsimp only [] at h
      split at h
      · rename_i c hpk
        split at h
        · rename_i hlb
          have h_l3 := consumeNewline_line_succ (skipToContentComment s1) c hpk hlb
          split at h
          · have h_rec0 := ih h
            have h_rec : (consumeNewline (skipToContentComment s1)).line ≤ s'.line :=
              h_rec0
            omega
          · have h_rec := ih h
            omega
        · injection h with h_eq; subst h_eq; omega
      · injection h with h_eq; subst h_eq; omega

/-- A same-line skip only moves the column right. -/
lemma skipToContentLoop_col_ge_of_line_eq (fuel : Nat) :
    ∀ {s s' : ScannerState}, skipToContentLoop s fuel = .ok s' →
    s'.line = s.line → s.col ≤ s'.col := by
  induction fuel with
  | zero =>
    intro s s' h _
    unfold skipToContentLoop at h
    injection h with h_eq; subst h_eq; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s s' h h_line
    unfold skipToContentLoop at h
    split at h
    · cases h
    · rename_i s1 hws
      have h_l1 : s1.line = s.line := skipToContentWs_preserves_line s s1 hws
      have h_l2 : (skipToContentComment s1).line = s1.line :=
        skipToContentComment_preserves_line s1
      have h_c1 : s.col ≤ s1.col := skipToContentWs_col_ge hws
      have h_c2 : s1.col ≤ (skipToContentComment s1).col :=
        skipToContentComment_col_ge s1
      dsimp only [] at h
      split at h
      · rename_i c hpk
        split at h
        · -- a break: the landing line is strictly below — the same-line
          -- premise is contradicted
          rename_i hlb
          exfalso
          have h_l3 := consumeNewline_line_succ (skipToContentComment s1) c hpk hlb
          split at h
          · have h_rec0 := skipToContentLoop_line_ge fuel' h
            have h_rec : (consumeNewline (skipToContentComment s1)).line ≤ s'.line :=
              h_rec0
            omega
          · have h_rec := skipToContentLoop_line_ge fuel' h
            omega
        · injection h with h_eq; subst h_eq; omega
      · injection h with h_eq; subst h_eq; omega

/-- A block skip that changed the line re-armed the key flag: the break
    iteration sets it, and nothing downstream unsets it. -/
lemma skipToContentLoop_allowed_of_line_ne (fuel : Nat) :
    ∀ {s s' : ScannerState}, skipToContentLoop s fuel = .ok s' →
    s.inFlow = false → s'.line ≠ s.line → s'.simpleKeyAllowed = true := by
  induction fuel with
  | zero =>
    intro s s' h _ h_ne
    unfold skipToContentLoop at h
    injection h with h_eq; subst h_eq
    exact absurd rfl h_ne
  | succ fuel' ih =>
    intro s s' h h_nf h_ne
    unfold skipToContentLoop at h
    split at h
    · cases h
    · rename_i s1 hws
      have h_l1 : s1.line = s.line := skipToContentWs_preserves_line s s1 hws
      have h_l2 : (skipToContentComment s1).line = s1.line :=
        skipToContentComment_preserves_line s1
      have h_fl1 : s1.flowLevel = s.flowLevel :=
        skipToContentWs_preserves_flowLevel s s1 hws
      have h_fl2 : (skipToContentComment s1).flowLevel = s1.flowLevel :=
        skipToContentComment_preserves_flowLevel s1
      dsimp only [] at h
      split at h
      · rename_i c hpk
        split at h
        · rename_i hlb
          have h_fl3 : (consumeNewline (skipToContentComment s1)).flowLevel
              = (skipToContentComment s1).flowLevel :=
            consumeNewline_preserves_flowLevel _
          split at h
          · exact skipToContentLoop_simpleKeyAllowed_mono _ _ _ rfl h
          · -- the flow arm is refuted: the flow level rode along unchanged
            rename_i h_flow
            exfalso
            apply h_flow
            unfold ScannerState.inFlow at h_nf ⊢
            rw [h_fl3, h_fl2, h_fl1]
            simpa using h_nf
        · injection h with h_eq; subst h_eq
          exact absurd (h_l2.trans h_l1) h_ne
      · injection h with h_eq; subst h_eq
        exact absurd (h_l2.trans h_l1) h_ne

lemma skipToContent_col_ge_of_line_eq {s s' : ScannerState}
    (h : skipToContent s = .ok s') (h_line : s'.line = s.line) :
    s.col ≤ s'.col := by
  unfold skipToContent at h
  exact skipToContentLoop_col_ge_of_line_eq _ h h_line

lemma skipToContent_allowed_of_line_ne {s s' : ScannerState}
    (h : skipToContent s = .ok s') (h_nf : s.inFlow = false)
    (h_ne : s'.line ≠ s.line) : s'.simpleKeyAllowed = true := by
  unfold skipToContent at h
  exact skipToContentLoop_allowed_of_line_ne _ h h_nf h_ne

/-- With nothing above the landing column, the unwind is a no-op. -/
private lemma unwindIndentsLoop_noop_of_le (s : ScannerState) (col : Int)
    (fuel : Nat) (h : ¬ s.currentIndent > col) :
    unwindIndentsLoop s col fuel = s := by
  cases fuel with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' =>
    unfold unwindIndentsLoop
    rw [ite_eq_right (by
      simp only [Bool.and_eq_true, decide_eq_true_eq, not_and]
      intro hc
      exact absurd hc h)]

private lemma unwindIndents_noop_of_le (s : ScannerState) (col : Int)
    (h : ¬ s.currentIndent > col) : unwindIndents s col = s := by
  unfold unwindIndents; exact unwindIndentsLoop_noop_of_le s col _ h

/-- `saveSimpleKey`, read at the key's LINE: it inherits, or saves fresh on
    the cursor's own line. -/
lemma saveSimpleKey_key_line_shape (st : ScannerState) :
    (saveSimpleKey st).simpleKey = st.simpleKey ∨
    ((saveSimpleKey st).simpleKey.possible = true ∧
     (saveSimpleKey st).simpleKey.pos.line = st.line) := by
  unfold saveSimpleKey
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl

/-- An armed save outside a flow is a FRESH one, at the cursor's own line. -/
lemma saveSimpleKey_fresh_of_allowed {st : ScannerState}
    (h_nf : st.inFlow = false) (h_al : st.simpleKeyAllowed = true) :
    (saveSimpleKey st).simpleKey.possible = true ∧
    (saveSimpleKey st).simpleKey.pos.line = st.line := by
  unfold saveSimpleKey
  rw [ite_eq_right (by simp [h_nf]), ite_eq_left h_al]
  exact ⟨rfl, rfl⟩

set_option maxHeartbeats 400000 in
/-- **Preprocessing preserves the stale-cursor floor.** -/
lemma preprocess_preserves_StaleKeyCursorFloor {s s2 : ScannerState} {c : Char}
    (h : scanNextToken_preprocess s = .ok (some (s2, c)))
    (h_inv : StaleKeyCursorFloor s) : StaleKeyCursorFloor s2 := by
  intro h_nf2 h_poss h_kline
  have h_fl : s2.flowLevel = s.flowLevel :=
    L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s s2 c h
  have h_nf : s.inFlow = false := by
    unfold ScannerState.inFlow at h_nf2 ⊢
    rw [← h_fl]; exact h_nf2
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · rename_i s_skip h_skip
    have h_nf_skip : s_skip.inFlow = false := by
      unfold ScannerState.inFlow at h_nf ⊢
      rw [skipToContent_preserves_flowLevel s s_skip h_skip]; exact h_nf
    split at h
    · simp at h
    · split at h
      · -- armed unwind branch
        split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h_eq, -⟩ := h
            have h_line2 : s2.line = s_skip.line := by
              rw [← h_eq, closeStaleExplicitKey_line, saveSimpleKey_line]
              exact unwindIndents_preserves_line s_skip _
            have h_col2 : s2.col = s_skip.col := by
              rw [← h_eq, closeStaleExplicitKey_col, saveSimpleKey_col]
              exact unwindIndents_col s_skip _
            by_cases h_lq : s_skip.line = s.line
            · rcases saveSimpleKey_key_line_shape
                  { unwindIndents s_skip ↑s_skip.col with needIndentCheck := false }
                  with h_inh | ⟨h_pfresh, h_fresh⟩
              · -- inherited stale key: the entry floor transfers
                have h_sk_eq : s2.simpleKey = s.simpleKey := by
                  rw [← h_eq, closeStaleExplicitKey_simpleKey]
                  refine h_inh.trans ?_
                  show (unwindIndents s_skip ↑s_skip.col).simpleKey = s.simpleKey
                  rw [unwindIndents_preserves_simpleKey]
                  exact skipToContent_preserves_simpleKey s s_skip h_skip
                have h_floor := h_inv h_nf (by rw [← h_sk_eq]; exact h_poss)
                  (by rw [← h_sk_eq, ← h_lq, ← h_line2]; exact h_kline)
                have h_col_ge : s.col ≤ s_skip.col :=
                  skipToContent_col_ge_of_line_eq h_skip h_lq
                have h_ind_skip : s_skip.indents = s.indents :=
                  skipToContent_preserves_indents s s_skip h_skip
                have h_ci_skip : s_skip.currentIndent = s.currentIndent := by
                  unfold ScannerState.currentIndent; rw [h_ind_skip]
                have h_noop : unwindIndents s_skip ↑s_skip.col = s_skip :=
                  unwindIndents_noop_of_le s_skip _ (by push_cast; omega)
                have h_ind2 : s2.indents = s.indents := by
                  rw [← h_eq, closeStaleExplicitKey_indents, saveSimpleKey_preserves_indents]
                  show ({ unwindIndents s_skip ↑s_skip.col
                    with needIndentCheck := false } : ScannerState).indents = s.indents
                  rw [h_noop]
                  exact h_ind_skip
                have h_ci2 : s2.currentIndent = s.currentIndent := by
                  unfold ScannerState.currentIndent; rw [h_ind2]
                rw [h_ci2, h_col2]
                omega
              · -- fresh save: on the landing's own line — refuted
                refine absurd ?_ h_kline
                rw [← h_eq, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_line]
                exact h_fresh.trans ((saveSimpleKey_line _).symm)
            · -- the line changed: the flag is armed, the save is fresh — refuted
              have h_al := skipToContent_allowed_of_line_ne h_skip h_nf h_lq
              have h_nf_M : ({ unwindIndents s_skip ↑s_skip.col
                  with needIndentCheck := false } : ScannerState).inFlow = false := by
                unfold ScannerState.inFlow at h_nf_skip ⊢
                rw [unwindIndents_preserves_flowLevel]; exact h_nf_skip
              have h_al_M : ({ unwindIndents s_skip ↑s_skip.col
                  with needIndentCheck := false } : ScannerState).simpleKeyAllowed = true := by
                show (unwindIndents s_skip ↑s_skip.col).simpleKeyAllowed = true
                rw [unwindIndents_preserves_simpleKeyAllowed]; exact h_al
              obtain ⟨-, h_l⟩ := saveSimpleKey_fresh_of_allowed h_nf_M h_al_M
              refine absurd ?_ h_kline
              rw [← h_eq, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_line]
              exact h_l.trans ((saveSimpleKey_line _).symm)
      · -- no unwind
        split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h_eq, -⟩ := h
            have h_line2 : s2.line = s_skip.line := by
              rw [← h_eq, closeStaleExplicitKey_line]; exact saveSimpleKey_line s_skip
            have h_col2 : s2.col = s_skip.col := by
              rw [← h_eq, closeStaleExplicitKey_col]; exact saveSimpleKey_col s_skip
            by_cases h_lq : s_skip.line = s.line
            · rcases saveSimpleKey_key_line_shape s_skip with h_inh | ⟨h_pfresh, h_fresh⟩
              · have h_sk_eq : s2.simpleKey = s.simpleKey := by
                  rw [← h_eq, closeStaleExplicitKey_simpleKey]
                  exact h_inh.trans (skipToContent_preserves_simpleKey s s_skip h_skip)
                have h_floor := h_inv h_nf (by rw [← h_sk_eq]; exact h_poss)
                  (by rw [← h_sk_eq, ← h_lq, ← h_line2]; exact h_kline)
                have h_col_ge : s.col ≤ s_skip.col :=
                  skipToContent_col_ge_of_line_eq h_skip h_lq
                have h_ind2 : s2.indents = s.indents := by
                  rw [← h_eq, closeStaleExplicitKey_indents, saveSimpleKey_preserves_indents]
                  exact skipToContent_preserves_indents s s_skip h_skip
                have h_ci2 : s2.currentIndent = s.currentIndent := by
                  unfold ScannerState.currentIndent; rw [h_ind2]
                rw [h_ci2, h_col2]
                omega
              · refine absurd ?_ h_kline
                rw [← h_eq, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_line]
                exact h_fresh.trans ((saveSimpleKey_line _).symm)
            · have h_al := skipToContent_allowed_of_line_ne h_skip h_nf h_lq
              obtain ⟨-, h_l⟩ := saveSimpleKey_fresh_of_allowed h_nf_skip h_al
              refine absurd ?_ h_kline
              rw [← h_eq, closeStaleExplicitKey_simpleKey, closeStaleExplicitKey_line]
              exact h_l.trans ((saveSimpleKey_line _).symm)

/-! ## §3  The directive scan stays on its line and off the indent stack

`[82] l-directive` is a one-line production: every collect loop advances over
non-break characters only, `skipToEndOfLine` stops AT the break, and nothing
in the path touches `indents`. -/

/-- A non-break advance touches neither line nor indents. -/
private lemma advance_line_ind_of_nb {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false) :
    s.advance.line = s.line ∧ s.advance.indents = s.indents :=
  ⟨advance_preserves_line_of_ne_break s c hpk
      (by intro hc; rw [hc] at hnb; cases hnb)
      (by intro hc; rw [hc] at hnb; cases hnb),
    L4YAML.Proofs.EmitterScannability.advance_preserves_indents s⟩

/-- A break is not a printable `ns-char`, a digit, a word/URI char, or `!`. -/
private lemma nb_of_break_excluded {c : Char} (h : isLineBreakBool c = true) :
    c = '\n' ∨ c = '\r' := by
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
    Bool.or_eq_true, beq_iff_eq] at h
  exact h

private lemma collectDirectiveNameLoop_line_ind (fuel : Nat) :
    ∀ (s : ScannerState) (name : String),
    (collectDirectiveNameLoop s name fuel).2.line = s.line ∧
    (collectDirectiveNameLoop s name fuel).2.indents = s.indents := by
  induction fuel with
  | zero => intro s name; unfold collectDirectiveNameLoop; exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s name
    unfold collectDirectiveNameLoop
    split
    · rename_i c hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcls
          exact hcls.1.1.2
        obtain ⟨h_l, h_i⟩ := advance_line_ind_of_nb hpk hnb
        obtain ⟨h_l', h_i'⟩ := ih s.advance (name.push c)
        exact ⟨h_l'.trans h_l, h_i'.trans h_i⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private lemma collectVersionMajorLoop_line_ind (fuel : Nat) :
    ∀ (s : ScannerState) (major : String),
    (collectVersionMajorLoop s major fuel).2.line = s.line ∧
    (collectVersionMajorLoop s major fuel).2.indents = s.indents := by
  induction fuel with
  | zero => intro s major; unfold collectVersionMajorLoop; exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s major
    unfold collectVersionMajorLoop
    split
    · rename_i hpk
      exact advance_line_ind_of_nb hpk (by decide)
    · rename_i c _hne hpk
      split
      · rename_i hdig
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hdig (by decide)
        obtain ⟨h_l, h_i⟩ := advance_line_ind_of_nb hpk hnb
        obtain ⟨h_l', h_i'⟩ := ih s.advance (major.push c)
        exact ⟨h_l'.trans h_l, h_i'.trans h_i⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private lemma collectVersionMinorLoop_line_ind (fuel : Nat) :
    ∀ (s : ScannerState) (minor : String),
    (collectVersionMinorLoop s minor fuel).2.line = s.line ∧
    (collectVersionMinorLoop s minor fuel).2.indents = s.indents := by
  induction fuel with
  | zero => intro s minor; unfold collectVersionMinorLoop; exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s minor
    unfold collectVersionMinorLoop
    split
    · rename_i c hpk
      split
      · rename_i hdig
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hdig (by decide)
        obtain ⟨h_l, h_i⟩ := advance_line_ind_of_nb hpk hnb
        obtain ⟨h_l', h_i'⟩ := ih s.advance (minor.push c)
        exact ⟨h_l'.trans h_l, h_i'.trans h_i⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private lemma collectTagHandleDirectiveLoop_line_ind (fuel : Nat) :
    ∀ (s : ScannerState) (handle : String),
    (collectTagHandleDirectiveLoop s handle fuel).2.line = s.line ∧
    (collectTagHandleDirectiveLoop s handle fuel).2.indents = s.indents := by
  induction fuel with
  | zero => intro s handle; unfold collectTagHandleDirectiveLoop; exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s handle
    unfold collectTagHandleDirectiveLoop
    split
    · rename_i c hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hcls (by decide)
        obtain ⟨h_l, h_i⟩ := advance_line_ind_of_nb hpk hnb
        obtain ⟨h_l', h_i'⟩ := ih s.advance (handle.push c)
        exact ⟨h_l'.trans h_l, h_i'.trans h_i⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private lemma collectTagPrefixLoop_line_ind (fuel : Nat) :
    ∀ (s : ScannerState) (pfx : String),
    (collectTagPrefixLoop s pfx fuel).2.line = s.line ∧
    (collectTagPrefixLoop s pfx fuel).2.indents = s.indents := by
  induction fuel with
  | zero => intro s pfx; unfold collectTagPrefixLoop; exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s pfx
    unfold collectTagPrefixLoop
    split
    · rename_i c hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hcls (by decide)
        obtain ⟨h_l, h_i⟩ := advance_line_ind_of_nb hpk hnb
        obtain ⟨h_l', h_i'⟩ := ih s.advance (pfx.push c)
        exact ⟨h_l'.trans h_l, h_i'.trans h_i⟩
      · exact ⟨rfl, rfl⟩
    · exact ⟨rfl, rfl⟩

private lemma skipToEndOfLineLoop_line_ind (fuel : Nat) :
    ∀ (s : ScannerState),
    (skipToEndOfLineLoop s fuel).line = s.line ∧
    (skipToEndOfLineLoop s fuel).indents = s.indents := by
  induction fuel with
  | zero => intro s; unfold skipToEndOfLineLoop; exact ⟨rfl, rfl⟩
  | succ fuel' ih =>
    intro s
    unfold skipToEndOfLineLoop
    split
    · rename_i c hpk
      split
      · exact ⟨rfl, rfl⟩
      · rename_i hnb
        obtain ⟨h_l, h_i⟩ := advance_line_ind_of_nb hpk (by simpa using hnb)
        obtain ⟨h_l', h_i'⟩ := ih s.advance
        exact ⟨h_l'.trans h_l, h_i'.trans h_i⟩
    · exact ⟨rfl, rfl⟩

private lemma skipToEndOfLine_line_ind (s : ScannerState) :
    (skipToEndOfLine s).line = s.line ∧
    (skipToEndOfLine s).indents = s.indents := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_line_ind _ s

lemma skipWhitespace_line_ind (s : ScannerState) :
    (skipWhitespace s).line = s.line ∧
    (skipWhitespace s).indents = s.indents :=
  ⟨skipWhitespace_preserves_line s,
    L4YAML.Proofs.PreprocessIndentStable.skipWhitespace_preserves_indents s⟩

private lemma scanYamlDirective_line_ind {s s_ws s' : ScannerState}
    {startPos : YamlPos}
    (h : scanYamlDirective s s_ws startPos = .ok s') :
    s'.line = s_ws.line ∧ s'.indents = s_ws.indents := by
  unfold scanYamlDirective at h
  simp only [bind, Except.bind] at h
  obtain ⟨h_l1, h_i1⟩ := collectVersionMajorLoop_line_ind
    (s.inputEnd - s_ws.offset) s_ws ""
  obtain ⟨h_l2, h_i2⟩ := collectVersionMinorLoop_line_ind
    (s.inputEnd -
      (collectVersionMajorLoop s_ws "" (s.inputEnd - s_ws.offset)).2.offset)
    (collectVersionMajorLoop s_ws "" (s.inputEnd - s_ws.offset)).2 ""
  obtain ⟨h_l3, h_i3⟩ := skipWhitespace_line_ind
    (collectVersionMinorLoop
      (collectVersionMajorLoop s_ws "" (s.inputEnd - s_ws.offset)).2 ""
      (s.inputEnd -
        (collectVersionMajorLoop s_ws "" (s.inputEnd - s_ws.offset)).2.offset)).2
  repeat' split at h
  all_goals first
    | (subst h; exact ⟨h_l3.trans (h_l2.trans h_l1), h_i3.trans (h_i2.trans h_i1)⟩)
    | (injection h with h_eq; subst h_eq; exact ⟨h_l3.trans (h_l2.trans h_l1), h_i3.trans (h_i2.trans h_i1)⟩)
    | (rename_i h_ren; subst h_ren; exact ⟨h_l3.trans (h_l2.trans h_l1), h_i3.trans (h_i2.trans h_i1)⟩)
    | (rename_i h_ren; injection h_ren with h_eq; subst h_eq; exact ⟨h_l3.trans (h_l2.trans h_l1), h_i3.trans (h_i2.trans h_i1)⟩)
    | injection h
    | (rename_i h_ren; injection h_ren)
    | cases h

private lemma scanTagDirective_line_ind {s s_ws s' : ScannerState}
    {startPos : YamlPos}
    (h : scanTagDirective s s_ws startPos = .ok s') :
    s'.line = s_ws.line ∧ s'.indents = s_ws.indents := by
  unfold scanTagDirective at h
  simp only [bind, Except.bind] at h
  obtain ⟨h_l1, h_i1⟩ := collectTagHandleDirectiveLoop_line_ind
    (s.inputEnd - s_ws.offset) s_ws ""
  obtain ⟨h_l1b, h_i1b⟩ := skipWhitespace_line_ind
    (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).2
  obtain ⟨h_l2, h_i2⟩ := collectTagPrefixLoop_line_ind
    (s.inputEnd -
      (skipWhitespace
        (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).2).offset)
    (skipWhitespace
      (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).2) ""
  obtain ⟨h_l3, h_i3⟩ := skipWhitespace_line_ind
    (collectTagPrefixLoop
      (skipWhitespace
        (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).2) ""
      (s.inputEnd -
        (skipWhitespace
          (collectTagHandleDirectiveLoop s_ws "" (s.inputEnd - s_ws.offset)).2).offset)).2
  repeat' split at h
  all_goals first
    | (subst h; exact ⟨h_l3.trans (h_l2.trans (h_l1b.trans h_l1)), h_i3.trans (h_i2.trans (h_i1b.trans h_i1))⟩)
    | (injection h with h_eq; subst h_eq; exact ⟨h_l3.trans (h_l2.trans (h_l1b.trans h_l1)), h_i3.trans (h_i2.trans (h_i1b.trans h_i1))⟩)
    | (rename_i h_ren; subst h_ren; exact ⟨h_l3.trans (h_l2.trans (h_l1b.trans h_l1)), h_i3.trans (h_i2.trans (h_i1b.trans h_i1))⟩)
    | (rename_i h_ren; injection h_ren with h_eq; subst h_eq; exact ⟨h_l3.trans (h_l2.trans (h_l1b.trans h_l1)), h_i3.trans (h_i2.trans (h_i1b.trans h_i1))⟩)
    | injection h
    | (rename_i h_ren; injection h_ren)
    | cases h

/-- **`scanDirective` stays on its line and never touches the indent stack.** -/
lemma scanDirective_line_ind {s s' : ScannerState}
    (h_pk : s.peek? = some '%')
    (h : scanDirective s = .ok s') :
    s'.line = s.line ∧ s'.indents = s.indents := by
  unfold scanDirective at h
  split at h
  · cases h
  · dsimp only [] at h
    obtain ⟨h_lp, h_ip⟩ := advance_line_ind_of_nb h_pk (by decide)
    obtain ⟨h_ln, h_in⟩ := collectDirectiveNameLoop_line_ind
      (s.inputEnd - s.advance.offset) s.advance ""
    obtain ⟨h_lw, h_iw⟩ := skipWhitespace_line_ind
      (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2
    split at h
    · -- %YAML
      split at h
      · rename_i s_yaml h_yaml
        injection h with h_eq; subst h_eq
        obtain ⟨h_ly, h_iy⟩ := scanYamlDirective_line_ind h_yaml
        obtain ⟨h_le, h_ie⟩ := skipToEndOfLine_line_ind s_yaml
        constructor
        · rw [h_le, h_ly, h_lw, h_ln, h_lp]
        · rw [h_ie, h_iy, h_iw, h_in, h_ip]
      · cases h
    · split at h
      · -- %TAG
        split at h
        · rename_i s_tag h_tag
          injection h with h_eq; subst h_eq
          obtain ⟨h_lt, h_it⟩ := scanTagDirective_line_ind h_tag
          obtain ⟨h_le, h_ie⟩ := skipToEndOfLine_line_ind s_tag
          constructor
          · rw [h_le, h_lt, h_lw, h_ln, h_lp]
          · rw [h_ie, h_it, h_iw, h_in, h_ip]
        · cases h
      · -- reserved directive
        injection h with h_eq; subst h_eq
        obtain ⟨h_le, h_ie⟩ := skipToEndOfLine_line_ind
          (skipWhitespace
            (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2)
        constructor
        · show (skipToEndOfLine _).line = s.line
          rw [h_le, h_lw, h_ln, h_lp]
        · show (skipToEndOfLine _).indents = s.indents
          rw [h_ie, h_iw, h_in, h_ip]

/-! ## §4  Per-op cursor facts for the preserved-key dispatches

Anchors, tags and the block entry stay on their line and move the column
right; the flow closes spend exactly one column on the bracket.  Everything
here is block-context fuel: the flow cases of §5 are vacuous. -/

private lemma collectAnchorNameLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (name : String),
    s.col ≤ (collectAnchorNameLoop s name fuel).2.col := by
  induction fuel with
  | zero => intro s name; unfold collectAnchorNameLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s name
    unfold collectAnchorNameLoop
    split
    · rename_i c hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          simp only [Bool.and_eq_true, Bool.not_eq_eq_eq_not, Bool.not_true] at hcls
          exact hcls.1.1.2
        calc s.col ≤ s.advance.col := by
              rw [advance_col_succ_of_peek hpk hnb]; omega
          _ ≤ _ := ih s.advance (name.push c)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma collectVerbatimTagLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (uri : String),
    s.col ≤ (collectVerbatimTagLoop s uri fuel).2.2.col := by
  induction fuel with
  | zero => intro s uri; unfold collectVerbatimTagLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s uri
    unfold collectVerbatimTagLoop
    split
    · rename_i hpk
      rw [advance_col_succ_of_peek hpk (by decide)]; omega
    · rename_i c _hne hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hcls (by decide)
        calc s.col ≤ s.advance.col := by
              rw [advance_col_succ_of_peek hpk hnb]; omega
          _ ≤ _ := ih s.advance (uri.push c)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma collectTagSuffixLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (suffix : String),
    s.col ≤ (collectTagSuffixLoop s suffix fuel).2.col := by
  induction fuel with
  | zero => intro s suffix; unfold collectTagSuffixLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s suffix
    unfold collectTagSuffixLoop
    split
    · rename_i c hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hcls (by decide)
        calc s.col ≤ s.advance.col := by
              rw [advance_col_succ_of_peek hpk hnb]; omega
          _ ≤ _ := ih s.advance (suffix.push c)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma collectTagHandleLoop_col_ge (fuel : Nat) :
    ∀ (s : ScannerState) (chars : String),
    s.col ≤ (collectTagHandleLoop s chars fuel).2.2.col := by
  induction fuel with
  | zero => intro s chars; unfold collectTagHandleLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    intro s chars
    unfold collectTagHandleLoop
    split
    · rename_i hpk
      rw [advance_col_succ_of_peek hpk (by decide)]; omega
    · rename_i c _hne hpk
      split
      · rename_i hcls
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · rcases nb_of_break_excluded hlb with rfl | rfl <;>
              exact absurd hcls (by decide)
        calc s.col ≤ s.advance.col := by
              rw [advance_col_succ_of_peek hpk hnb]; omega
          _ ≤ _ := ih s.advance (chars.push c)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

/-- The anchor/alias scan: same line, column right, indents untouched. -/
lemma scanAnchorOrAlias_cursor {s s' : ScannerState} {b : Bool} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanAnchorOrAlias s b = .ok s') :
    s'.line = s.line ∧ s.col ≤ s'.col ∧ s'.indents = s.indents := by
  unfold scanAnchorOrAlias at hok
  dsimp only [] at hok
  obtain ⟨h_al, h_ai⟩ := advance_line_ind_of_nb hpk hnb
  have h_ac : s.advance.col = s.col + 1 := advance_col_succ_of_peek hpk hnb
  repeat' split at hok
  all_goals first
    | (injection hok with h_eq; subst h_eq
       exact ⟨((collectAnchorNameLoop_line_nic _ _ _).1).trans h_al,
         Nat.le_trans (by omega : s.col ≤ s.advance.col)
           (collectAnchorNameLoop_col_ge _ _ _),
         (collectAnchorNameLoop_preserves_indents _ _ _).trans h_ai⟩)
    | (rename_i h_ren; subst h_ren
       exact ⟨((collectAnchorNameLoop_line_nic _ _ _).1).trans h_al,
         Nat.le_trans (by omega : s.col ≤ s.advance.col)
           (collectAnchorNameLoop_col_ge _ _ _),
         (collectAnchorNameLoop_preserves_indents _ _ _).trans h_ai⟩)
    | (rename_i h_ren; injection h_ren with h_eq; subst h_eq
       exact ⟨((collectAnchorNameLoop_line_nic _ _ _).1).trans h_al,
         Nat.le_trans (by omega : s.col ≤ s.advance.col)
           (collectAnchorNameLoop_col_ge _ _ _),
         (collectAnchorNameLoop_preserves_indents _ _ _).trans h_ai⟩)
    | injection hok
    | (rename_i h_ren; injection h_ren)
    | cases hok

/-- The verbatim tag: same line, column right, indents untouched. -/
lemma scanVerbatimTag_cursor {s s' : ScannerState} {p : YamlPos}
    (hpk : s.peek? = some '<') (hok : scanVerbatimTag s p = .ok s') :
    s'.line = s.line ∧ s.col ≤ s'.col ∧ s'.indents = s.indents := by
  unfold scanVerbatimTag at hok
  dsimp only [] at hok
  obtain ⟨h_vl, h_vi⟩ := advance_line_ind_of_nb hpk (by decide)
  have h_vc := advance_col_succ_of_peek hpk (by decide)
  rcases h_loop : collectVerbatimTagLoop s.advance ""
      (p.offset + s.inputEnd - s.advance.offset) with ⟨uri, fc, s_u⟩
  have h_l := (collectVerbatimTagLoop_line_nic s.advance ""
    (p.offset + s.inputEnd - s.advance.offset)).1
  have h_c := collectVerbatimTagLoop_col_ge
    (p.offset + s.inputEnd - s.advance.offset) s.advance ""
  have h_i := collectVerbatimTagLoop_preserves_indents s.advance ""
    (p.offset + s.inputEnd - s.advance.offset)
  rw [h_loop] at hok h_l h_c h_i
  repeat' split at hok
  all_goals first
    | (injection hok with h_eq; subst h_eq
       exact ⟨h_l.trans h_vl,
         Nat.le_trans (by omega : s.col ≤ s.advance.col) h_c,
         h_i.trans h_vi⟩)
    | (rename_i h_ren; subst h_ren
       exact ⟨h_l.trans h_vl,
         Nat.le_trans (by omega : s.col ≤ s.advance.col) h_c,
         h_i.trans h_vi⟩)
    | (rename_i h_ren; injection h_ren with h_eq; subst h_eq
       exact ⟨h_l.trans h_vl,
         Nat.le_trans (by omega : s.col ≤ s.advance.col) h_c,
         h_i.trans h_vi⟩)
    | injection hok
    | (rename_i h_ren; injection h_ren)
    | cases hok

/-- The tag scan: same line, column right, indents untouched. -/
lemma scanTag_cursor {s s' : ScannerState}
    (hpk : s.peek? = some '!')
    (hok : scanTag s = .ok s') :
    s'.line = s.line ∧ s.col ≤ s'.col ∧ s'.indents = s.indents := by
  unfold scanTag at hok
  dsimp only [] at hok
  obtain ⟨h_al, h_ai⟩ := advance_line_ind_of_nb hpk (by decide)
  have h_ac : s.advance.col = s.col + 1 := advance_col_succ_of_peek hpk (by decide)
  split at hok
  · -- verbatim `!<uri>`
    rename_i hpk2
    simp only [bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i v h_v
      injection hok with h_eq
      subst h_eq
      obtain ⟨h_l, h_c, h_i⟩ := scanVerbatimTag_cursor hpk2 h_v
      exact ⟨h_l.trans h_al,
        Nat.le_trans (by omega : s.col ≤ s.advance.col) h_c,
        h_i.trans h_ai⟩
  · -- secondary `!!suffix`
    rename_i hpk2
    unfold scanSecondaryTag at hok
    dsimp only [] at hok
    obtain ⟨h_vl, h_vi⟩ := advance_line_ind_of_nb hpk2 (by decide)
    have h_vc : s.advance.advance.col = s.advance.col + 1 :=
      advance_col_succ_of_peek hpk2 (by decide)
    rcases h_loop : collectTagSuffixLoop s.advance.advance ""
        (s.currentPos.offset + s.advance.inputEnd - s.advance.advance.offset)
      with ⟨suffix, s_u⟩
    have h_l := (collectTagSuffixLoop_line_nic s.advance.advance ""
      (s.currentPos.offset + s.advance.inputEnd - s.advance.advance.offset)).1
    have h_c := collectTagSuffixLoop_col_ge
      (s.currentPos.offset + s.advance.inputEnd - s.advance.advance.offset)
      s.advance.advance ""
    have h_i := collectTagSuffixLoop_preserves_indents s.advance.advance ""
      (s.currentPos.offset + s.advance.inputEnd - s.advance.advance.offset)
    rw [h_loop] at hok h_l h_c h_i
    injection hok with h_eq
    subst h_eq
    exact ⟨h_l.trans (h_vl.trans h_al),
      Nat.le_trans (by omega : s.col ≤ s.advance.advance.col) h_c,
      h_i.trans (h_vi.trans h_ai)⟩
  · -- named/primary `!handle!suffix` / `!suffix` / `!`
    unfold scanNamedTag at hok
    dsimp only [] at hok
    rcases h_loop : collectTagHandleLoop s.advance "" (s.inputEnd - s.advance.offset)
      with ⟨chars, fb, s_h⟩
    have h_hl := (collectTagHandleLoop_line_nic s.advance ""
      (s.inputEnd - s.advance.offset)).1
    have h_hc := collectTagHandleLoop_col_ge (s.inputEnd - s.advance.offset)
      s.advance ""
    have h_hi := collectTagHandleLoop_preserves_indents s.advance ""
      (s.inputEnd - s.advance.offset)
    rw [h_loop] at hok h_hl h_hc h_hi
    dsimp only [] at hok h_hl h_hc h_hi
    rcases h_loop2 : collectTagSuffixLoop s_h
        (if fb = true then ("!" ++ chars ++ "!", "") else ("!", chars)).snd
        (s.inputEnd - s_h.offset)
      with ⟨sfx, s_sf⟩
    have h_sl := (collectTagSuffixLoop_line_nic s_h
      (if fb = true then ("!" ++ chars ++ "!", "") else ("!", chars)).snd
      (s.inputEnd - s_h.offset)).1
    have h_sc := collectTagSuffixLoop_col_ge (s.inputEnd - s_h.offset) s_h
      (if fb = true then ("!" ++ chars ++ "!", "") else ("!", chars)).snd
    have h_si := collectTagSuffixLoop_preserves_indents s_h
      (if fb = true then ("!" ++ chars ++ "!", "") else ("!", chars)).snd
      (s.inputEnd - s_h.offset)
    rw [h_loop2] at h_sl h_sc h_si
    rw [h_loop2] at hok <;> try skip
    repeat' split at hok
    all_goals first
      | (injection hok with h_eq; subst h_eq
         first
           | exact ⟨h_sl.trans (h_hl.trans h_al),
               Nat.le_trans (Nat.le_trans
                 (by omega : s.col ≤ s.advance.col) h_hc) h_sc,
               h_si.trans (h_hi.trans h_ai)⟩
           | exact ⟨h_hl.trans h_al,
               Nat.le_trans (by omega : s.col ≤ s.advance.col) h_hc,
               h_hi.trans h_ai⟩)
      | (rename_i h_ren; subst h_ren
         first
           | exact ⟨h_sl.trans (h_hl.trans h_al),
               Nat.le_trans (Nat.le_trans
                 (by omega : s.col ≤ s.advance.col) h_hc) h_sc,
               h_si.trans (h_hi.trans h_ai)⟩
           | exact ⟨h_hl.trans h_al,
               Nat.le_trans (by omega : s.col ≤ s.advance.col) h_hc,
               h_hi.trans h_ai⟩)
      | (rename_i h_ren; injection h_ren with h_eq; subst h_eq
         first
           | exact ⟨h_sl.trans (h_hl.trans h_al),
               Nat.le_trans (Nat.le_trans
                 (by omega : s.col ≤ s.advance.col) h_hc) h_sc,
               h_si.trans (h_hi.trans h_ai)⟩
           | exact ⟨h_hl.trans h_al,
               Nat.le_trans (by omega : s.col ≤ s.advance.col) h_hc,
               h_hi.trans h_ai⟩)
      | injection hok
      | (rename_i h_ren; injection h_ren)
      | cases hok

/-- `pushSequenceIndent` leaves the cursor and the lookahead alone. -/
lemma pushSequenceIndent_cursor (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).line = s.line ∧
    (pushSequenceIndent s col).col = s.col ∧
    (pushSequenceIndent s col).peek? = s.peek? := by
  unfold pushSequenceIndent ScannerState.emit ScannerState.peek?
  split <;> exact ⟨rfl, rfl, rfl⟩

/-- The pushed level, when it fires, is exactly the argument column. -/
lemma pushSequenceIndent_currentIndent_ub (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).currentIndent = col ∨
    (pushSequenceIndent s col).currentIndent = s.currentIndent := by
  unfold pushSequenceIndent
  split
  · left
    show ScannerState.currentIndent _ = col
    unfold ScannerState.currentIndent
    simp [Array.back?_push]
  · right; rfl

/-- The block entry: same line, one column. -/
lemma scanBlockEntry_line_col {s s' : ScannerState}
    (h_noflow : s.inFlow = false) (hpk : s.peek? = some '-')
    (hok : scanBlockEntry s = .ok s') :
    s'.line = s.line ∧ s'.col = s.col + 1 := by
  unfold scanBlockEntry at hok
  simp only [bind, Except.bind, h_noflow, Bool.not_false, ite_true] at hok
  obtain ⟨h_pl, h_pc, h_pp⟩ := pushSequenceIndent_cursor s ↑s.col
  have h_epk : ((pushSequenceIndent s ↑s.col).emit
      L4YAML.YamlToken.blockEntry).peek? = s.peek? := by
    rw [show ((pushSequenceIndent s ↑s.col).emit
      L4YAML.YamlToken.blockEntry).peek? = (pushSequenceIndent s ↑s.col).peek?
      from rfl, h_pp]
  split at hok
  · simp at hok
  · split at hok
    · simp at hok
    split at hok  -- `scanBlockEntryValidate` (item 134)
    · simp at hok
    simp only [Except.ok.injEq] at hok
    subst hok
    constructor
    · show ((pushSequenceIndent s ↑s.col).emit
          L4YAML.YamlToken.blockEntry).advance.line = s.line
      rw [advance_preserves_line_of_ne_break _ '-'
        (by rw [h_epk]; exact hpk) (by decide) (by decide)]
      exact h_pl
    · show ((pushSequenceIndent s ↑s.col).emit
          L4YAML.YamlToken.blockEntry).advance.col = s.col + 1
      rw [advance_col_succ_of_peek (c := '-') (by rw [h_epk]; exact hpk)
        (by decide)]
      rw [show ((pushSequenceIndent s ↑s.col).emit
        L4YAML.YamlToken.blockEntry).col = (pushSequenceIndent s ↑s.col).col
        from rfl, h_pc]

/-- A flow close spends one column on its bracket and stays on the line. -/
lemma scanFlowSequenceEnd_cursor {s : ScannerState}
    (hpk : s.peek? = some ']') :
    (scanFlowSequenceEnd s).line = s.line ∧
    (scanFlowSequenceEnd s).col = s.col + 1 := by
  unfold scanFlowSequenceEnd
  dsimp only []
  have h_epk : (s.emit L4YAML.YamlToken.flowSequenceEnd).peek? = s.peek? := rfl
  constructor
  · show (s.emit L4YAML.YamlToken.flowSequenceEnd).advance.line = s.line
    rw [advance_preserves_line_of_ne_break _ ']'
      (by rw [h_epk]; exact hpk) (by decide) (by decide)]
    rfl
  · show (s.emit L4YAML.YamlToken.flowSequenceEnd).advance.col = s.col + 1
    rw [advance_col_succ_of_peek (c := ']')
      (by rw [h_epk]; exact hpk) (by decide)]
    rfl

lemma scanFlowMappingEnd_cursor {s : ScannerState}
    (hpk : s.peek? = some '}') :
    (scanFlowMappingEnd s).line = s.line ∧
    (scanFlowMappingEnd s).col = s.col + 1 := by
  unfold scanFlowMappingEnd
  dsimp only []
  have h_epk : (s.emit L4YAML.YamlToken.flowMappingEnd).peek? = s.peek? := rfl
  constructor
  · show (s.emit L4YAML.YamlToken.flowMappingEnd).advance.line = s.line
    rw [advance_preserves_line_of_ne_break _ '}'
      (by rw [h_epk]; exact hpk) (by decide) (by decide)]
    rfl
  · show (s.emit L4YAML.YamlToken.flowMappingEnd).advance.col = s.col + 1
    rw [advance_col_succ_of_peek (c := '}')
      (by rw [h_epk]; exact hpk) (by decide)]
    rfl

/-! ## §5  The dispatch clones and the `scanNextToken` preservation

The skeleton is `scanNextToken_preserves_KeysBehindCursor`'s.  Each case
either clears the key (`of_cleared`), saves on the cursor's own line
(`of_key_line`), stays inside a flow (`of_inFlow`), establishes the floor
outright (`of_floor` — the flow closes and the cross-line walks), or
transfers the mid-state floor through a same-line, column-monotone,
indent-stable scan. -/

/-- The `inFlow` bit through a per-op `flowLevel` preservation. -/
lemma inFlow_eq_of_flowLevel {s t : ScannerState}
    (h : t.flowLevel = s.flowLevel) : t.inFlow = s.inFlow := by
  unfold ScannerState.inFlow; rw [h]

private lemma dispatchStructural_preserves_StaleFloor {s s' : ScannerState}
    {c : Char}
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (h_peek : s.peek? = some c)
    (h_inv : StaleKeyCursorFloor s) : StaleKeyCursorFloor s' := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · -- document start clears the key
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact .of_cleared (scanDocumentStart_clears_simpleKey s)
      · split at h
        · split at h
          · simp at h
          · -- document end clears the key
            simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            rename_i s_de h_de
            exact .of_cleared (scanDocumentEnd_clears_simpleKey s s_de h_de)
        · split at h
          · split at h
            · simp at h
            · -- directive: same line, no indent write, and its column is 0
              rename_i h_guard _ s_dir h_dir
              simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              have h_col0 : s.col = 0 := by
                simp only [Bool.and_eq_true, beq_iff_eq] at h_guard
                exact h_guard.2
              have h_pct : c = '%' := by
                simp only [Bool.and_eq_true, beq_iff_eq] at h_guard
                exact h_guard.1
              subst h_pct
              have h_sk := scanDirective_preserves_simpleKey s s_dir h_dir
              obtain ⟨h_l, h_i⟩ := scanDirective_line_ind h_peek h_dir
              intro h_nf' h_poss' h_ne'
              have h_nf : s.inFlow = false := by
                rw [← inFlow_eq_of_flowLevel
                  (scanDirective_preserves_flowLevel s s_dir h_dir)]
                exact h_nf'
              by_cases h_kl : s.simpleKey.pos.line = s.line
              · exact absurd (by rw [h_sk, h_kl, h_l]) h_ne'
              · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
                rw [currentIndent_of_indents_eq h_i]
                have h0 : (0 : Int) ≤ (s_dir.col : Int) := Int.natCast_nonneg _
                omega
          · simp at h

private lemma dispatchFlowIndicators_preserves_StaleFloor {s s' : ScannerState}
    {c : Char}
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (h_peek : s.peek? = some c)
    (h_floor_flow : s.inFlow = true → s.currentIndent < (s.col : Int)) :
    StaleKeyCursorFloor s' := by
  unfold scanNextToken_dispatchFlowIndicators at h
  replace h := peel_flowAdj h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- '[' opens: the current slot is cleared
    simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact .of_cleared (scanFlowSequenceStart_simpleKey_cleared s)
  · split at h
    · -- ']' closes: the bracket cleared the flow floor one column earlier
      rename_i h_c
      split at h
      · simp at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · rename_i h_fl0 _ _ _ _
            simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            have h_flow : s.inFlow = true := by
              unfold ScannerState.inFlow
              simp only [beq_iff_eq] at h_fl0
              simp only [decide_eq_true_eq]
              omega
            have h_cq : c = ']' := by simpa using h_c
            subst h_cq
            obtain ⟨h_l, h_col⟩ := scanFlowSequenceEnd_cursor h_peek
            refine .of_floor ?_
            rw [currentIndent_of_indents_eq
              (L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s),
              h_col]
            have := h_floor_flow h_flow
            push_cast
            omega
    · split at h
      · -- '{' opens: cleared
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact .of_cleared (scanFlowMappingStart_simpleKey_cleared s)
      · split at h
        · -- '}' closes
          rename_i h_c
          split at h
          · simp at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i h_fl0 _ _ _ _
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have h_flow : s.inFlow = true := by
                  unfold ScannerState.inFlow
                  simp only [beq_iff_eq] at h_fl0
                  simp only [decide_eq_true_eq]
                  omega
                have h_cq : c = '}' := by simpa using h_c
                subst h_cq
                obtain ⟨h_l, h_col⟩ := scanFlowMappingEnd_cursor h_peek
                refine .of_floor ?_
                rw [currentIndent_of_indents_eq
                  (L4YAML.Proofs.EmitterScannability.scanFlowMappingEnd_preserves_indents s),
                  h_col]
                have := h_floor_flow h_flow
                push_cast
                omega
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · -- ',' clears
                rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact .of_cleared (scanFlowEntry_clears_simpleKey s _ h_entry)
          · simp at h

private lemma dispatchBlockIndicators_preserves_StaleFloor {s s' : ScannerState}
    {c : Char}
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (h_peek : s.peek? = some c)
    (h_inv : StaleKeyCursorFloor s) : StaleKeyCursorFloor s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- '-': the entry pushes its own column, one short of the cursor
    rename_i h_c
    split at h
    · simp at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      rename_i s_be h_be
      have h_cq : c = '-' := by
        simp only [Bool.and_eq_true, beq_iff_eq] at h_c
        exact h_c.1.1
      subst h_cq
      by_cases h_fl : s.inFlow = true
      · exact .of_inFlow (by
          rw [inFlow_eq_of_flowLevel (scanBlockEntry_preserves_flowLevel s s_be h_be)]
          exact h_fl)
      · have h_nf : s.inFlow = false := by
          cases h0 : s.inFlow
          · rfl
          · exact absurd h0 h_fl
        have h_sk := scanBlockEntry_preserves_simpleKey s s_be h_be
        obtain ⟨h_l, h_col⟩ := scanBlockEntry_line_col h_nf h_peek h_be
        intro _ h_poss' h_ne'
        by_cases h_kl : s.simpleKey.pos.line = s.line
        · exact absurd (by rw [h_sk, h_kl, h_l]) h_ne'
        · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
          rw [currentIndent_of_indents_eq (scanBlockEntry_indents h_nf h_be), h_col]
          rcases pushSequenceIndent_currentIndent_ub s ↑s.col with h_ub | h_ub <;>
            rw [h_ub] <;> push_cast <;> omega
  · split at h
    · -- '?' clears
      split at h
      · simp at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        rename_i s_k h_k
        exact .of_cleared (scanKey_clears_simpleKey s _ h_k)
    · split at h
      · -- ':' clears
        split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          rename_i s_v h_v
          exact .of_cleared (scanValue_clears_simpleKey s _ h_v)
      · simp at h

set_option maxHeartbeats 800000 in
private lemma dispatchContent_preserves_StaleFloor {s s' : ScannerState}
    {c : Char}
    (h : scanNextToken_dispatchContent s c = .ok s')
    (h_peek : s.peek? = some c)
    (h_inv : StaleKeyCursorFloor s) : StaleKeyCursorFloor s' := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- '&': anchor, then the definedAnchors touch-up (cursor untouched)
    rename_i h_c
    split at h
    · simp at h
    split at h
    · simp at h
    · rename_i s_a h_anch
      simp only [Except.ok.injEq] at h; subst h
      have h_cq : c = '&' := by simpa using h_c
      subst h_cq
      by_cases h_fl : s.inFlow = true
      · refine .of_inFlow ?_
        show s_a.inFlow = true
        rw [inFlow_eq_of_flowLevel
          (scanAnchorOrAlias_preserves_flowLevel s true s_a h_anch)]
        exact h_fl
      · have h_nf : s.inFlow = false := by
          cases h0 : s.inFlow
          · rfl
          · exact absurd h0 h_fl
        have h_sk := scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch
        obtain ⟨h_l, h_col, h_i⟩ := scanAnchorOrAlias_cursor h_peek (by decide) h_anch
        intro _ h_poss' h_ne'
        by_cases h_kl : s.simpleKey.pos.line = s.line
        · refine absurd ?_ h_ne'
          show s_a.simpleKey.pos.line = s_a.line
          rw [h_sk, h_kl, h_l]
        · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
          show s_a.currentIndent < (s_a.col : Int)
          rw [currentIndent_of_indents_eq h_i]
          push_cast
          omega
  · split at h
    · -- '*': alias
      rename_i h_c
      split at h
      · simp at h
      split at h
      · simp at h
      · replace h := aliasArm_scan_ok h
        have h_cq : c = '*' := by simpa using h_c
        subst h_cq
        by_cases h_fl : s.inFlow = true
        · exact .of_inFlow (by
            rw [inFlow_eq_of_flowLevel
              (scanAnchorOrAlias_preserves_flowLevel s false s' h)]
            exact h_fl)
        · have h_nf : s.inFlow = false := by
            cases h0 : s.inFlow
            · rfl
            · exact absurd h0 h_fl
          have h_sk := scanAnchorOrAlias_preserves_simpleKey s false s' h
          obtain ⟨h_l, h_col, h_i⟩ := scanAnchorOrAlias_cursor h_peek (by decide) h
          intro _ h_poss' h_ne'
          by_cases h_kl : s.simpleKey.pos.line = s.line
          · exact absurd (by rw [h_sk, h_kl, h_l]) h_ne'
          · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
            rw [currentIndent_of_indents_eq h_i]
            push_cast
            omega
    · split at h
      · -- '!': tag
        rename_i h_c
        split at h
        · simp at h
        · have h_cq : c = '!' := by simpa using h_c
          subst h_cq
          by_cases h_fl : s.inFlow = true
          · exact .of_inFlow (by
              rw [inFlow_eq_of_flowLevel (scanTag_preserves_flowLevel s s' h)]
              exact h_fl)
          · have h_nf : s.inFlow = false := by
              cases h0 : s.inFlow
              · rfl
              · exact absurd h0 h_fl
            have h_sk := scanTag_preserves_simpleKey s s' h
            obtain ⟨h_l, h_col, h_i⟩ := scanTag_cursor h_peek h
            intro _ h_poss' h_ne'
            by_cases h_kl : s.simpleKey.pos.line = s.line
            · exact absurd (by rw [h_sk, h_kl, h_l]) h_ne'
            · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
              rw [currentIndent_of_indents_eq h_i]
              push_cast
              omega
      · split at h
        · -- '|' / '>': the block scalar clears
          replace h := peel_blockScalarGuard h
          exact .of_cleared (scanBlockScalar_clears_simpleKey s _ h)
        · split at h
          · -- '"': double quoted + endLine touch-up (cursor untouched)
            rename_i h_c
            split at h
            · simp at h
            · rename_i s_dq h_dq
              have h_cq : c = '"' := by simpa using h_c
              subst h_cq
              have h_sk := scanDoubleQuoted_preserves_simpleKey s s_dq h_dq
              have h_i :=
                L4YAML.Proofs.EmitterScannability.scanDoubleQuoted_preserves_indents
                  s s_dq h_dq
              have h_flq := scanDoubleQuoted_preserves_flowLevel s s_dq h_dq
              have h_core : StaleKeyCursorFloor s_dq := by
                by_cases h_fl : s.inFlow = true
                · exact .of_inFlow (by rw [inFlow_eq_of_flowLevel h_flq]; exact h_fl)
                · have h_nf : s.inFlow = false := by
                    cases h0 : s.inFlow
                    · rfl
                    · exact absurd h0 h_fl
                  by_cases h_lq : s_dq.line = s.line
                  · intro _ h_poss' h_ne'
                    by_cases h_kl : s.simpleKey.pos.line = s.line
                    · exact absurd (by rw [h_sk, h_kl, h_lq]) h_ne'
                    · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
                      have h_col := scanDoubleQuoted_sameline_col_ge h_peek h_dq h_lq
                      rw [currentIndent_of_indents_eq h_i]
                      push_cast
                      omega
                  · refine .of_floor ?_
                    rw [currentIndent_of_indents_eq h_i]
                    exact scanDoubleQuoted_crossline_col_floor h_peek h_dq h_lq
              split at h <;> (simp only [Except.ok.injEq] at h; subst h)
              · -- endLine touch-up: same possible/pos/cursor/indents/flow
                intro h_nf' h_poss' h_ne'
                exact h_core h_nf' h_poss' h_ne'
              · exact h_core
          · split at h
            · -- '\'': single quoted, same shape
              rename_i h_c
              split at h
              · simp at h
              · rename_i s_sq h_sq
                have h_cq : c = '\'' := by simpa using h_c
                subst h_cq
                have h_sk := scanSingleQuoted_preserves_simpleKey s s_sq h_sq
                have h_i := scanSingleQuoted_preserves_indents h_sq
                have h_flq := scanSingleQuoted_preserves_flowLevel s s_sq h_sq
                have h_core : StaleKeyCursorFloor s_sq := by
                  by_cases h_fl : s.inFlow = true
                  · exact .of_inFlow (by rw [inFlow_eq_of_flowLevel h_flq]; exact h_fl)
                  · have h_nf : s.inFlow = false := by
                      cases h0 : s.inFlow
                      · rfl
                      · exact absurd h0 h_fl
                    by_cases h_lq : s_sq.line = s.line
                    · intro _ h_poss' h_ne'
                      by_cases h_kl : s.simpleKey.pos.line = s.line
                      · exact absurd (by rw [h_sk, h_kl, h_lq]) h_ne'
                      · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
                        have h_col := scanSingleQuoted_sameline_col_ge h_peek h_sq h_lq
                        rw [currentIndent_of_indents_eq h_i]
                        push_cast
                        omega
                    · refine .of_floor ?_
                      rw [currentIndent_of_indents_eq h_i]
                      exact scanSingleQuoted_crossline_col_floor h_peek h_sq h_lq
                split at h <;> (simp only [Except.ok.injEq] at h; subst h)
                · intro h_nf' h_poss' h_ne'
                  exact h_core h_nf' h_poss' h_ne'
                · exact h_core
            · split at h
              · -- plain scalar
                have h_sk := scanPlainScalar_preserves_simpleKey s _ h
                have h_i := scanPlainScalar_preserves_indents h
                have h_flq := scanPlainScalar_preserves_flowLevel s s' h
                by_cases h_fl : s.inFlow = true
                · exact .of_inFlow (by rw [inFlow_eq_of_flowLevel h_flq]; exact h_fl)
                · have h_nf : s.inFlow = false := by
                    cases h0 : s.inFlow
                    · rfl
                    · exact absurd h0 h_fl
                  by_cases h_lq : s'.line = s.line
                  · intro _ h_poss' h_ne'
                    by_cases h_kl : s.simpleKey.pos.line = s.line
                    · exact absurd (by rw [h_sk, h_kl, h_lq]) h_ne'
                    · have h_floor := h_inv h_nf (by rw [← h_sk]; exact h_poss') h_kl
                      have h_col := scanPlainScalar_sameline_col_ge h_nf h h_lq
                      rw [currentIndent_of_indents_eq h_i]
                      push_cast
                      omega
                  · refine .of_floor ?_
                    rw [currentIndent_of_indents_eq h_i]
                    exact scanPlainScalar_crossline_col_floor h_nf h h_lq
              · simp at h

set_option maxHeartbeats 800000 in
/-- **`scanNextToken` preserves the stale-cursor floor.**  The skeleton is
    `scanNextToken_preserves_KeysBehindCursor`'s. -/
lemma scanNextToken_preserves_StaleKeyCursorFloor (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (h_inv : StaleKeyCursorFloor s) : StaleKeyCursorFloor s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  split at h
  · cases h
  · split at h
    · simp at h
    · rename_i sp c h_pre
      have h_inv2 := preprocess_preserves_StaleKeyCursorFloor h_pre h_inv
      have h_peek := preprocess_peek_eq s sp c h_pre
      -- §9.2 dangling-node check (item 133)
      split at h
      · cases h
      -- §8.1 flow-value floor (item 172)
      split at h
      · cases h
      split at h
      · cases h
      · split at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact dispatchStructural_preserves_StaleFloor ‹_› h_peek h_inv2
        · rename_i h_struct
          have h_floor_flow : sp.inFlow = true → sp.currentIndent < (sp.col : Int) :=
            fun h_fl => structural_none_col_gt_of_inFlow h_fl h_struct
          split at h
          · cases h
          -- §9.2 bare-document check (item 132)
          split at h
          · cases h
          · rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at h
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at h
              cases fi with
              | error => cases h
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  exact dispatchFlowIndicators_preserves_StaleFloor h_fi
                    h_peek h_floor_flow
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at h
                  cases bi with
                  | error => cases h
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      exact dispatchBlockIndicators_preserves_StaleFloor h_bi
                        h_peek h_inv2
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp c = av at h
                      cases av with
                      | error => cases h
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at h
                      cases dc with
                      | error => cases h
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                        exact dispatchContent_preserves_StaleFloor h_dc h_peek h_inv2
            · generalize h_sp2 : (({ sp with allowDirectives := false, documentEverStarted := true } : ScannerState)) = sp2 at h
              have h_peek2 : sp2.peek? = some c := by rw [← h_sp2]; exact h_peek
              have h_inv3 : StaleKeyCursorFloor sp2 := by rw [← h_sp2]; exact h_inv2
              have h_floor_flow2 : sp2.inFlow = true →
                  sp2.currentIndent < (sp2.col : Int) := by
                rw [← h_sp2]; exact h_floor_flow
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at h
              cases fi with
              | error => cases h
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  exact dispatchFlowIndicators_preserves_StaleFloor h_fi
                    h_peek2 h_floor_flow2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at h
                  cases bi with
                  | error => cases h
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      exact dispatchBlockIndicators_preserves_StaleFloor h_bi
                        h_peek2 h_inv3
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp2 c = av at h
                      cases av with
                      | error => cases h
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at h
                      cases dc with
                      | error => cases h
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                        exact dispatchContent_preserves_StaleFloor h_dc h_peek2 h_inv3

end L4YAML.Proofs.StaleCursorFloor

end Blanket
