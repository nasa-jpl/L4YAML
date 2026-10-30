/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module
public import L4YAML.Proofs.Scanner.PendingKeySound
public import L4YAML.Proofs.Scanner.StaleCursorFloor
public import L4YAML.Proofs.Scanner.ScalarWalkColFloor
public import L4YAML.Proofs.Scanner.LineOpenGuard
public import L4YAML.Proofs.Scanner.PropsRunLineCoupling
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
public import L4YAML.Proofs.Scanner.FlowIndentStable
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Scanner.AliasTrailingContent
public import L4YAML.Proofs.Production.PreprocessProduction
public import L4YAML.Proofs.Scanner.ScanStrictCoupling

@[expose] public section Blanket

/-!
# The cursor floor, carried at the token level (DOCS item 339)

Item 338 proved `PendingKeySound.Sound` through every `scanNextToken` arm but
left one premise STARVED: after preprocessing, the cursor sits at or right of
the current indent (`PreprocessFloor`).  The unwind supplies it when an indent
check was pending; when none was, it is a fact about the cursor the carrier
did not hold.  This module carries it:

* `ColFloor.floor` — `needIndentCheck = false → currentIndent ≤ col`, in both
  contexts.  Inside flow the scanner refuses under-indented content
  (`underIndentedFlowContent` in `scanNextToken_dispatchStructural`,
  `underIndentedScalar` in the scalar loops), so a flow close that returns to
  block level inherits a floor that already holds.
* `ColFloor.key` / `ColFloor.stack` — every saved simple key (the live one and
  the ones stacked by flow openers) sits BEHIND the cursor, lexicographically
  on (line, col).  The `:` arm spends it: `scanValuePrepare` opens a block
  mapping at the KEY's column, and the floor after the `:` needs that column
  at or left of the cursor.  (`KeysBehindCursor` is the same fact on offsets;
  the push reads columns.)

`preprocessFloor` is the bridge to item 338's premise; `scanNextToken_colfloor`
carries the structure through one token so `StreamAccum` can thread both.
-/


namespace L4YAML.Proofs.ColFloor

open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.IndentStackBase (SentinelBase)
open L4YAML.Proofs.PreprocessIndentStable (currentIndent_of_indents_eq)

/-! ## §1  Cursor order -/

/-- The cursor of `s'` is at or after the cursor of `s`, lexicographically. -/
def Forward (s s' : ScannerState) : Prop :=
  s.line < s'.line ∨ (s'.line = s.line ∧ s.col ≤ s'.col)

/-- A saved position sits at or behind the cursor. -/
def Behind (p : YamlPos) (s : ScannerState) : Prop :=
  p.line < s.line ∨ (p.line = s.line ∧ p.col ≤ s.col)

lemma Forward.refl (s : ScannerState) : Forward s s := Or.inr ⟨rfl, Nat.le_refl _⟩

lemma Forward.trans {s t u : ScannerState} (h1 : Forward s t) (h2 : Forward t u) :
    Forward s u := by
  unfold Forward at *; omega

lemma Forward.of_same_line {s s' : ScannerState} (hl : s'.line = s.line) (hc : s.col ≤ s'.col) :
    Forward s s' := Or.inr ⟨hl, hc⟩

lemma Forward.of_fields {s s' : ScannerState} (hl : s'.line = s.line) (hc : s'.col = s.col) :
    Forward s s' := Or.inr ⟨hl, hc ▸ Nat.le_refl _⟩

lemma Forward.col_le_of_line_eq {s s' : ScannerState} (hf : Forward s s') (hl : s'.line = s.line) :
    s.col ≤ s'.col := by
  unfold Forward at hf; omega

lemma Behind.mono {p : YamlPos} {s s' : ScannerState} (h : Behind p s) (hf : Forward s s') :
    Behind p s' := by
  unfold Behind Forward at *; omega

lemma Behind.of_pos (s : ScannerState) : Behind s.currentPos s :=
  Or.inr ⟨rfl, Nat.le_refl _⟩

lemma Forward.advance (s : ScannerState) : Forward s s.advance := by
  unfold Forward ScannerState.advance
  by_cases h : s.offset < s.inputEnd
  · simp only [h, ↓reduceIte]
    by_cases h1 : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\n') = true
    · simp [h1]
    · by_cases h2 : (String.Pos.Raw.get s.input ⟨s.offset⟩ == '\r') = true
      · simp [h1, h2]
      · simp [h1, h2]
  · simp [h]

lemma Forward.advanceNLoop (s : ScannerState) (n : Nat) : Forward s (s.advanceNLoop n) := by
  induction n generalizing s with
  | zero => exact Forward.refl s
  | succ n ih => exact (Forward.advance s).trans (ih s.advance)

lemma Forward.advanceN (s : ScannerState) (n : Nat) : Forward s (s.advanceN n) :=
  Forward.advanceNLoop s n

lemma Forward.emit (s : ScannerState) (t : YamlToken) : Forward s (s.emit t) :=
  Forward.of_fields rfl rfl

/-- One non-break character spends one column on its line. -/
lemma Forward.advance_of_nb {s : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hnb : isLineBreakBool c = false) : s.advance.line = s.line ∧ s.advance.col = s.col + 1 := by
  refine ⟨advance_preserves_line_of_ne_break s c hpk ?_ ?_,
    L4YAML.Proofs.ScalarWalkColFloor.advance_col_succ_of_peek hpk hnb⟩
  · rintro rfl; revert hnb; decide
  · rintro rfl; revert hnb; decide

/-! ## §2  The carrier -/

/-- **The cursor floor.** -/
structure ColFloor (s : ScannerState) : Prop where
  floor : s.needIndentCheck = false → s.currentIndent ≤ (s.col : Int)
  key : s.simpleKey.possible = true → Behind s.simpleKey.pos s
  stack : ∀ j (h : j < s.simpleKeyStack.size),
    s.simpleKeyStack[j].possible = true → Behind s.simpleKeyStack[j].pos s

/-- Transport along a step that keeps the keys and moves the cursor forward;
    the floor is the one obligation left to the caller. -/
lemma ColFloor.of_forward {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' where
  floor := hfloor
  key := by rw [hsk]; intro hp; exact (h.key hp).mono hf
  stack := by
    intro j hj hp
    simp only [hst] at hj hp ⊢
    exact (h.stack j hj hp).mono hf

/-- The same, with the live key cleared by the step. -/
lemma ColFloor.of_forward_cleared {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey.possible = false) (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' where
  floor := hfloor
  key := by intro hp; rw [hsk] at hp; cases hp
  stack := by
    intro j hj hp
    simp only [hst] at hj hp ⊢
    exact (h.stack j hj hp).mono hf

/-- Transport along a field touch-up that keeps the cursor, the indents, the
    key's `possible`/`pos` and the stack (the quoted arms' `endLine` write). -/
lemma ColFloor.of_touchup {s s' : ScannerState} (h : ColFloor s)
    (hnic : s'.needIndentCheck = s.needIndentCheck) (hind : s'.indents = s.indents)
    (hcol : s'.col = s.col) (hline : s'.line = s.line)
    (hp : s'.simpleKey.possible = s.simpleKey.possible) (hpos : s'.simpleKey.pos = s.simpleKey.pos)
    (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' where
  floor := by
    intro hn; rw [hnic] at hn
    rw [currentIndent_of_indents_eq hind, hcol]; exact h.floor hn
  key := by
    intro hk; rw [hp] at hk; rw [hpos]
    exact (h.key hk).mono (Forward.of_fields hline hcol)
  stack := by
    intro j hj hk
    simp only [hst] at hj hk ⊢
    exact (h.stack j hj hk).mono (Forward.of_fields hline hcol)

lemma ColFloor.of_forward_or {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey = s.simpleKey ∨ s'.simpleKey.possible = false)
    (hst : s'.simpleKeyStack = s.simpleKeyStack)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' := by
  rcases hsk with hsk | hsk
  · exact h.of_forward hf hsk hst hfloor
  · exact h.of_forward_cleared hf hsk hst hfloor

/-- A step that touches none of the fields the carrier reads. -/
lemma ColFloor.of_fields_eq {s s' : ScannerState} (h : ColFloor s)
    (hnic : s'.needIndentCheck = s.needIndentCheck) (hind : s'.indents = s.indents)
    (hcol : s'.col = s.col) (hline : s'.line = s.line)
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' :=
  h.of_forward (Forward.of_fields hline hcol) hsk hst (by
    rw [hnic, currentIndent_of_indents_eq hind, hcol]; exact h.floor)

/-- The floor on a same-line step that keeps the stack. -/
lemma floor_of_same_line {s s' : ScannerState} (hfl : s.currentIndent ≤ (s.col : Int))
    (hind : s'.indents = s.indents) (hline : s'.line = s.line) (hcol : s.col ≤ s'.col) :
    s'.currentIndent ≤ (s'.col : Int) := by
  rw [currentIndent_of_indents_eq hind]; have := hline; omega

lemma mk'_colfloor (input : String) : ColFloor (ScannerState.mk' input) where
  floor := by intro _; unfold ScannerState.mk' ScannerState.currentIndent; simp
  key := by intro h; unfold ScannerState.mk' at h; simp at h
  stack := by intro j hj; unfold ScannerState.mk' at hj; simp at hj

/-! ## §3  Preprocessing -/

lemma skipToContent_forward {s s' : ScannerState} (h : skipToContent s = .ok s') :
    Forward s s' := by
  have hl : s.line ≤ s'.line := by
    unfold skipToContent at h
    exact L4YAML.Proofs.StaleCursorFloor.skipToContentLoop_line_ge _ h
  rcases Nat.lt_or_eq_of_le hl with hlt | heq
  · exact Or.inl hlt
  · exact Or.inr ⟨heq.symm,
      L4YAML.Proofs.StaleCursorFloor.skipToContent_col_ge_of_line_eq h heq.symm⟩

lemma skipToContent_colfloor {s s' : ScannerState} (h : ColFloor s) (hok : skipToContent s = .ok s') :
    ColFloor s' :=
  h.of_forward (skipToContent_forward hok)
    (L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.skipToContent_preserves_simpleKeyStack s s' hok)
    (by
      intro hnic
      have hnic0 : s.needIndentCheck = false := by
        cases h0 : s.needIndentCheck
        · rfl
        · exact absurd (skipToContent_needIndentCheck_mono hok h0)
            (by rw [hnic]; decide)
      have hline := skipToContent_line_eq_of_needIndentCheck s s' hok hnic
      exact floor_of_same_line (h.floor hnic0)
        (L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s' hok) hline
        (L4YAML.Proofs.StaleCursorFloor.skipToContent_col_ge_of_line_eq hok hline))

lemma saveSimpleKey_key_shape (st : ScannerState) :
    (saveSimpleKey st).simpleKey = st.simpleKey ∨
    ((saveSimpleKey st).simpleKey.possible = true ∧
      (saveSimpleKey st).simpleKey.pos = st.currentPos) := by
  unfold saveSimpleKey
  split
  · exact Or.inl rfl
  · split
    · exact Or.inr ⟨rfl, rfl⟩
    · exact Or.inl rfl

lemma saveSimpleKey_colfloor {s : ScannerState} (h : ColFloor s) : ColFloor (saveSimpleKey s) where
  floor := by
    rw [L4YAML.Proofs.PropsRunLineCoupling.saveSimpleKey_needIndentCheck,
      currentIndent_of_indents_eq (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_preserves_indents s),
      L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col]
    exact h.floor
  key := by
    intro hp
    have hf : Forward s (saveSimpleKey s) := Forward.of_fields
      (L4YAML.Proofs.PropsRunLineCoupling.saveSimpleKey_line s)
      (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col s)
    rcases saveSimpleKey_key_shape s with heq | ⟨_, hpos⟩
    · rw [heq] at hp ⊢; exact (h.key hp).mono hf
    · rw [hpos]; exact (Behind.of_pos s).mono hf
  stack := by
    intro j hj hp
    have hf : Forward s (saveSimpleKey s) := Forward.of_fields
      (L4YAML.Proofs.PropsRunLineCoupling.saveSimpleKey_line s)
      (L4YAML.Proofs.PreprocessIndentStable.saveSimpleKey_col s)
    simp only [L4YAML.Proofs.ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack] at hj hp ⊢
    exact (h.stack j hj hp).mono hf

lemma closeStaleExplicitKey_colfloor {s : ScannerState} (h : ColFloor s) :
    ColFloor (closeStaleExplicitKey s) := by
  rcases L4YAML.Proofs.CloseStaleExplicitKey.closeStaleExplicitKey_cases s with heq | ⟨_, _, heq⟩
  · rw [heq]; exact h
  · rw [heq]
    exact h.of_fields_eq rfl rfl rfl rfl rfl rfl

lemma unwindIndents_colfloor_at_col {s : ScannerState} (h : ColFloor s) (hbase : SentinelBase s) :
    ColFloor { unwindIndents s s.col with needIndentCheck := false } := by
  have hf : Forward s { unwindIndents s s.col with needIndentCheck := false } :=
    Forward.of_fields (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_line s _)
      (L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col s _)
  refine h.of_forward hf (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_simpleKey s _)
    (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_simpleKeyStack s _) ?_
  intro _
  show (unwindIndents s s.col).currentIndent ≤ ((unwindIndents s s.col).col : Int)
  rw [L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col]
  exact L4YAML.Proofs.IndentStackCover.unwindIndents_top_le hbase (Int.natCast_nonneg _)

/-- **Preprocessing keeps the floor.** -/
lemma preprocess_colfloor {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (s', c))) (h : ColFloor s)
    (hbase : SentinelBase s) : ColFloor s' := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  split at hok
  · contradiction
  · rename_i s_skip h_skip
    have hS : ColFloor s_skip := skipToContent_colfloor h h_skip
    have hB : SentinelBase s_skip := by
      unfold SentinelBase
      rw [L4YAML.Proofs.PreprocessIndentStable.skipToContent_preserves_indents s s_skip h_skip]
      exact hbase
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact closeStaleExplicitKey_colfloor
              (saveSimpleKey_colfloor (unwindIndents_colfloor_at_col hS hB))
      · split at hok
        · contradiction
        · split at hok
          · simp at hok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at hok
            obtain ⟨rfl, rfl⟩ := hok
            exact closeStaleExplicitKey_colfloor (saveSimpleKey_colfloor hS)

/-- **The bridge to item 338's STARVED premise.** -/
lemma preprocessFloor {s : ScannerState} (h : ColFloor s) (hbase : SentinelBase s) :
    PendingKeySound.PreprocessFloor s := by
  intro sp c hok hnf
  have hfl := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sp c hok
  have hnf0 : s.inFlow = false := by
    first
      | simpa [ScannerState.inFlow, hfl] using hnf
      | simpa [ScannerState.inFlow, ← hfl] using hnf
  exact (preprocess_colfloor hok h hbase).floor
    (L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hnf0 hok)

/-- After preprocessing, the floor holds unconditionally once the structural
    dispatcher's flow check has passed (`underIndentedFlowContent`). -/
lemma dispatchStructural_floor {s : ScannerState} {c : Char} {r : Option ScannerState}
    (hok : scanNextToken_dispatchStructural s c = .ok r) (h : ColFloor s)
    (hnic : s.inFlow = false → s.needIndentCheck = false) :
    s.currentIndent ≤ (s.col : Int) := by
  by_cases hf : s.inFlow = true
  · unfold scanNextToken_dispatchStructural at hok
    simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
    split at hok
    · contradiction
    · rename_i hcond
      simp only [hf, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq] at hcond
      omega
  · have hnf : s.inFlow = false := by simpa using hf
    exact h.floor (hnic hnf)

/-! ## §4  Structural arms -/

lemma unwindIndents_neg_one_currentIndent {s : ScannerState} (hbase : SentinelBase s) :
    (unwindIndents s (-1)).currentIndent ≤ -1 := by
  rcases L4YAML.Proofs.PreprocessIndentStable.unwindIndents_terminal s (-1) with h1 | h2
  · exact h1
  · rw [(L4YAML.Proofs.IndentStackBase.unwindIndents_base s (-1) hbase).currentIndent_of_size_le_one h2]
    exact Int.le_refl _

lemma scanDocumentStart_colfloor {s : ScannerState} (h : ColFloor s) (hbase : SentinelBase s) :
    ColFloor (scanDocumentStart s) := by
  have hind : (scanDocumentStart s).indents = (unwindIndents s (-1)).indents := by
    unfold scanDocumentStart
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents]
  have h1 : Forward s (unwindIndents s (-1)) := Forward.of_fields
    (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_line s (-1))
    (L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col s (-1))
  have hf : Forward s (scanDocumentStart s) := by
    unfold scanDocumentStart
    exact h1.trans ((Forward.of_fields (s' := { unwindIndents s (-1) with
      simpleKey := { possible := false } }) rfl rfl).trans ((Forward.emit _ _).trans
        ((Forward.advanceN _ 3).trans (Forward.of_fields rfl rfl))))
  refine h.of_forward_cleared hf ?_
    (L4YAML.Proofs.ScannerCorrectness.scanDocumentStart_preserves_simpleKeyStack s) ?_
  · unfold scanDocumentStart
    simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_simpleKey,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKey]
  · intro _
    rw [currentIndent_of_indents_eq hind]
    have := unwindIndents_neg_one_currentIndent hbase
    omega

set_option maxHeartbeats 800000 in
lemma scanDocumentEnd_shape {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s') :
    s' = { (({ unwindIndents s (-1) with simpleKey := { possible := false } }).emit
              .documentEnd).advanceN 3 with
            simpleKeyAllowed := true
            allowDirectives := true
            directivesPresent := false
            definedAnchors := #[]
            explicitKeyLine := none
            explicitKeyCol := -1 } := by
  unfold scanDocumentEnd at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals exact (Except.ok.inj hok).symm

lemma scanDocumentEnd_colfloor {s s' : ScannerState} (hok : scanDocumentEnd s = .ok s')
    (h : ColFloor s) (hbase : SentinelBase s) : ColFloor s' := by
  have hst := L4YAML.Proofs.ScannerCorrectness.scanDocumentEnd_preserves_simpleKeyStack s s' hok
  have hshape := scanDocumentEnd_shape hok
  have h1 : Forward s (unwindIndents s (-1)) := Forward.of_fields
    (L4YAML.Proofs.ScannerCorrectness.unwindIndents_preserves_line s (-1))
    (L4YAML.Proofs.PreprocessIndentStable.unwindIndents_col s (-1))
  have hf : Forward s s' := by
    rw [hshape]
    exact h1.trans ((Forward.of_fields (s' := { unwindIndents s (-1) with
      simpleKey := { possible := false } }) rfl rfl).trans ((Forward.emit _ _).trans
        ((Forward.advanceN _ 3).trans (Forward.of_fields rfl rfl))))
  have hind : s'.indents = (unwindIndents s (-1)).indents := by
    rw [hshape]
    simp [L4YAML.Proofs.IndentStackBase.advanceN_preserves_indents]
  refine h.of_forward_cleared hf ?_ hst ?_
  · rw [hshape]
    simp [L4YAML.Proofs.ScannerCorrectness.advanceN_preserves_simpleKey,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKey]
  · intro _
    rw [currentIndent_of_indents_eq hind]
    have := unwindIndents_neg_one_currentIndent hbase
    omega

lemma scanDirective_colfloor {s s' : ScannerState} (hpk : s.peek? = some '%') (hcol0 : s.col = 0)
    (hok : scanDirective s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨hl, hi⟩ := L4YAML.Proofs.StaleCursorFloor.scanDirective_line_ind hpk hok
  refine h.of_forward (Forward.of_same_line hl (by rw [hcol0]; exact Nat.zero_le _))
    (L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanDirective_preserves_simpleKeyStack s s' hok) ?_
  intro _
  rw [currentIndent_of_indents_eq hi]
  rw [hcol0] at hfl
  have : (0 : Int) ≤ (s'.col : Int) := Int.natCast_nonneg _
  omega

lemma dispatchStructural_colfloor {s s' : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchStructural s c = .ok (some s')) (h : ColFloor s)
    (hbase : SentinelBase s) (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_colfloor h hbase
    | exact scanDocumentEnd_colfloor (by assumption) h hbase
    | (have hcond : (c == '%' && s.col == 0) = true := by assumption
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨hc, hc0⟩ := hcond
       subst hc
       exact scanDirective_colfloor hpk hc0 (by assumption) h hfl)

/-! ## §5  Flow arms -/

lemma emit_peek (s : ScannerState) (t : YamlToken) : (s.emit t).peek? = s.peek? := rfl

lemma emit_advance_cursor {s : ScannerState} {t : YamlToken} {c : Char} (hpk : s.peek? = some c)
    (hnb : isLineBreakBool c = false) :
    ((s.emit t).advance).line = s.line ∧ ((s.emit t).advance).col = s.col + 1 := by
  have := Forward.advance_of_nb (s := s.emit t) (c := c) (by rw [emit_peek]; exact hpk) hnb
  exact this

lemma scanFlowSequenceStart_colfloor {s : ScannerState} (hpk : s.peek? = some '[') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowSequenceStart s) := by
  have hf : Forward s (scanFlowSequenceStart s) := by
    unfold scanFlowSequenceStart
    exact (Forward.of_fields (s' := { s with simpleKey := { possible := false } }) rfl rfl).trans
      ((Forward.emit _ _).trans ((Forward.advance _).trans (Forward.of_fields rfl rfl)))
  have hline : (scanFlowSequenceStart s).line = s.line := by
    unfold scanFlowSequenceStart
    exact (Forward.advance_of_nb (s := ({ s with simpleKey := { possible := false } }).emit
      .flowSequenceStart) (c := '[') hpk (by decide)).1
  have hcol : s.col ≤ (scanFlowSequenceStart s).col := hf.col_le_of_line_eq hline
  have hst : (scanFlowSequenceStart s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
    unfold scanFlowSequenceStart
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowSequenceStart_preserves_indents s) hline hcol
  · intro hp
    rw [L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared] at hp; cases hp
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [Array.getElem_push] at hp ⊢
    split at hp
    · rename_i hlt
      simp only [hlt, ↓reduceDIte]
      exact (h.stack j hlt hp).mono hf
    · rename_i hge
      simp only [hge, ↓reduceDIte]
      exact (h.key hp).mono hf

lemma scanFlowMappingStart_colfloor {s : ScannerState} (hpk : s.peek? = some '{') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowMappingStart s) := by
  have hf : Forward s (scanFlowMappingStart s) := by
    unfold scanFlowMappingStart
    exact (Forward.of_fields (s' := { s with simpleKey := { possible := false } }) rfl rfl).trans
      ((Forward.emit _ _).trans ((Forward.advance _).trans (Forward.of_fields rfl rfl)))
  have hline : (scanFlowMappingStart s).line = s.line := by
    unfold scanFlowMappingStart
    exact (Forward.advance_of_nb (s := ({ s with simpleKey := { possible := false } }).emit
      .flowMappingStart) (c := '{') hpk (by decide)).1
  have hcol : s.col ≤ (scanFlowMappingStart s).col := hf.col_le_of_line_eq hline
  have hst : (scanFlowMappingStart s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
    unfold scanFlowMappingStart
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  refine ⟨?_, ?_, ?_⟩
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowMappingStart_preserves_indents s) hline hcol
  · intro hp
    rw [L4YAML.Proofs.ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared] at hp; cases hp
  · intro j hj hp
    simp only [hst] at hj hp ⊢
    rw [Array.getElem_push] at hp ⊢
    split at hp
    · rename_i hlt
      simp only [hlt, ↓reduceDIte]
      exact (h.stack j hlt hp).mono hf
    · rename_i hge
      simp only [hge, ↓reduceDIte]
      exact (h.key hp).mono hf

/-- A pop keeps the surviving entries behind the cursor; the restored key is
    the popped one. -/
lemma flowEnd_colfloor {s s' : ScannerState} (h : ColFloor s) (hf : Forward s s')
    (hsk : s'.simpleKey = s.simpleKeyStack.back?.getD {})
    (hst : s'.simpleKeyStack = s.simpleKeyStack.pop)
    (hfloor : s'.needIndentCheck = false → s'.currentIndent ≤ (s'.col : Int)) : ColFloor s' where
  floor := hfloor
  key := by
    intro hp
    rw [hsk, Array.back?_eq_getElem?] at hp ⊢
    cases hk : s.simpleKeyStack[s.simpleKeyStack.size - 1]? with
    | none => rw [hk] at hp; simp at hp
    | some k =>
      rw [hk] at hp
      simp only [Option.getD_some] at hp ⊢
      obtain ⟨hlt, hkk⟩ := Array.getElem?_eq_some_iff.mp hk
      rw [← hkk] at hp ⊢
      exact (h.stack _ hlt hp).mono hf
  stack := by
    intro j hj hp
    simp only [hst, Array.size_pop] at hj
    simp only [hst, Array.getElem_pop] at hp ⊢
    exact (h.stack j (by omega) hp).mono hf

lemma scanFlowSequenceEnd_colfloor {s : ScannerState} (hpk : s.peek? = some ']') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowSequenceEnd s) := by
  obtain ⟨hl, hc⟩ := L4YAML.Proofs.StaleCursorFloor.scanFlowSequenceEnd_cursor hpk
  refine flowEnd_colfloor h (Forward.of_same_line hl (by rw [hc]; exact Nat.le_succ _))
    (L4YAML.Proofs.ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s) ?_ ?_
  · unfold scanFlowSequenceEnd
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s) hl
      (by rw [hc]; exact Nat.le_succ _)

lemma scanFlowMappingEnd_colfloor {s : ScannerState} (hpk : s.peek? = some '}') (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor (scanFlowMappingEnd s) := by
  obtain ⟨hl, hc⟩ := L4YAML.Proofs.StaleCursorFloor.scanFlowMappingEnd_cursor hpk
  refine flowEnd_colfloor h (Forward.of_same_line hl (by rw [hc]; exact Nat.le_succ _))
    (L4YAML.Proofs.ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s) ?_ ?_
  · unfold scanFlowMappingEnd
    simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]
  · intro _
    exact floor_of_same_line hfl
      (L4YAML.Proofs.EmitterScannability.scanFlowMappingEnd_preserves_indents s) hl
      (by rw [hc]; exact Nat.le_succ _)

lemma scanFlowEntry_colfloor {s s' : ScannerState} (hpk : s.peek? = some ',')
    (hok : scanFlowEntry s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hst := L4YAML.Proofs.ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s s' hok
  have hind := L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hok
  have hcl := L4YAML.Proofs.ScannerCorrectness.scanFlowEntry_clears_simpleKey s s' hok
  have hcur := emit_advance_cursor (s := s) (t := .flowEntry) (c := ',') hpk (by decide)
  have hlc : s'.line = s.line ∧ s'.col = s.col + 1 := by
    unfold scanFlowEntry at hok
    simp only [bind, Except.bind] at hok
    repeat (any_goals (split at hok))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at hok; subst hok; exact hcur)
  exact h.of_forward_cleared (Forward.of_same_line hlc.1 (by rw [hlc.2]; exact Nat.le_succ _)) hcl hst
    (fun _ => floor_of_same_line hfl hind hlc.1 (by rw [hlc.2]; exact Nat.le_succ _))

lemma dispatchFlowIndicators_colfloor {s s' : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok))
  all_goals first
    | (have hc : (c == '[') = true := by assumption
       have hc' : c = '[' := by simpa using hc
       subst hc'; exact scanFlowSequenceStart_colfloor hpk h hfl)
    | (have hc : (c == '{') = true := by assumption
       have hc' : c = '{' := by simpa using hc
       subst hc'; exact scanFlowMappingStart_colfloor hpk h hfl)
    | (have hc : (c == ']') = true := by assumption
       have hc' : c = ']' := by simpa using hc
       subst hc'; exact scanFlowSequenceEnd_colfloor hpk h hfl)
    | (have hc : (c == '}') = true := by assumption
       have hc' : c = '}' := by simpa using hc
       subst hc'; exact scanFlowMappingEnd_colfloor hpk h hfl)
    | (have hc : (c == ',') = true := by assumption
       have hc' : c = ',' := by simpa using hc
       subst hc'; exact scanFlowEntry_colfloor hpk (by assumption) h hfl)
    | simp_all

/-! ## §6  Block arms -/

lemma pushMappingIndent_cursor (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).line = s.line ∧ (pushMappingIndent s col).col = s.col ∧
    (pushMappingIndent s col).peek? = s.peek? := by
  unfold pushMappingIndent ScannerState.emit ScannerState.peek?
  split <;> exact ⟨rfl, rfl, rfl⟩

lemma pushMappingIndent_currentIndent_ub (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).currentIndent = col ∨
    (pushMappingIndent s col).currentIndent = s.currentIndent := by
  unfold pushMappingIndent
  split
  · left
    simp [ScannerState.currentIndent, ScannerState.emit, Array.back?_push]
  · right; rfl

lemma scanBlockEntry_colfloor {s s' : ScannerState} (hnf : s.inFlow = false) (hpk : s.peek? = some '-')
    (hok : scanBlockEntry s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨hl, hc⟩ := L4YAML.Proofs.StaleCursorFloor.scanBlockEntry_line_col hnf hpk hok
  refine h.of_forward (Forward.of_same_line hl (by rw [hc]; exact Nat.le_succ _))
    (L4YAML.Proofs.ScannerCorrectness.scanBlockEntry_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanBlockEntry_preserves_simpleKeyStack s s' hok) ?_
  intro _
  rw [currentIndent_of_indents_eq
    (L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok), hc]
  rcases L4YAML.Proofs.StaleCursorFloor.pushSequenceIndent_currentIndent_ub s (s.col : Int) with h1 | h1
  · rw [h1]; push_cast; omega
  · rw [h1]; push_cast; omega

lemma scanKey_shape {s s' : ScannerState} (hok : scanKey s = .ok s') :
    ∃ m : ScannerState, (m = pushMappingIndent s (s.col : Int) ∨ m = s) ∧
      s'.line = ((m.emit .key).advance).line ∧ s'.col = ((m.emit .key).advance).col ∧
      s'.simpleKey.possible = false ∧ s'.simpleKeyStack = m.simpleKeyStack := by
  unfold scanKey at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals first
    | exact ⟨_, Or.inl rfl, rfl, rfl, rfl, by
        simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
          L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]⟩
    | exact ⟨_, Or.inr rfl, rfl, rfl, rfl, by
        simp [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
          L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack]⟩

lemma scanKey_colfloor {s s' : ScannerState} (hpk : s.peek? = some '?')
    (hok : scanKey s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨m, hm, hl, hc, hsk, hst⟩ := scanKey_shape hok
  have hmc : m.line = s.line ∧ m.col = s.col ∧ m.peek? = s.peek? ∧
      m.simpleKeyStack = s.simpleKeyStack := by
    rcases hm with rfl | rfl
    · obtain ⟨a, b, c⟩ := pushMappingIndent_cursor s (s.col : Int)
      exact ⟨a, b, c, L4YAML.Proofs.ScannerCorrectness.pushMappingIndent_preserves_simpleKeyStack s _⟩
    · exact ⟨rfl, rfl, rfl, rfl⟩
  obtain ⟨hml, hmcol, hmpk, hmst⟩ := hmc
  have hadv := Forward.advance_of_nb (s := m.emit .key) (c := '?') (by rw [emit_peek, hmpk]; exact hpk)
    (by decide)
  have hl' : s'.line = s.line :=
    ((hl.trans hadv.1).trans (show (m.emit .key).line = m.line from rfl)).trans hml
  have hc' : s'.col = s.col + 1 := by
    rw [hc, hadv.2]; exact congrArg (· + 1) ((show (m.emit .key).col = m.col from rfl).trans hmcol)
  refine h.of_forward_cleared (Forward.of_same_line hl' (by rw [hc']; exact Nat.le_succ _)) hsk
    (by rw [hst, hmst]) ?_
  intro _
  rw [hc']
  by_cases hf : s.inFlow = true
  · rw [currentIndent_of_indents_eq (L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow hf hok)]
    push_cast; omega
  · have hnf : s.inFlow = false := by simpa using hf
    rw [currentIndent_of_indents_eq (L4YAML.Proofs.PreprocessIndentStable.scanKey_indents hnf hok)]
    rcases pushMappingIndent_currentIndent_ub s (s.col : Int) with h1 | h1 <;> rw [h1] <;> push_cast <;> omega

lemma scanValueClearKey_fields (s : ScannerState) :
    (scanValueClearKey s).line = s.line ∧ (scanValueClearKey s).col = s.col ∧
    (scanValueClearKey s).peek? = s.peek? ∧
    (scanValueClearKey s).simpleKeyStack = s.simpleKeyStack ∧
    (scanValueClearKey s).inFlow = s.inFlow ∧
    ((scanValueClearKey s).simpleKey = s.simpleKey ∨ (scanValueClearKey s).simpleKey.possible = false) := by
  cases hek : s.explicitKeyLine with
  | none =>
    unfold scanValueClearKey; rw [hek]
    exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩
  | some ek =>
    unfold scanValueClearKey; rw [hek]
    dsimp only
    split
    · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
    · split
      · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inr rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, rfl, Or.inl rfl⟩

lemma scanValueValidate_key_line {s : ScannerState} {u : Unit} (hok : scanValueValidate s = .ok u)
    (hnf : s.inFlow = false) (hp : s.simpleKey.possible = true) : s.simpleKey.pos.line = s.line := by
  by_cases hl : s.simpleKey.pos.line = s.line
  · exact hl
  · exfalso
    unfold scanValueValidate at hok
    have hc : (s.simpleKey.possible && !s.inFlow && s.simpleKey.pos.line != s.line) = true := by
      simp [hp, hnf, hl]
    simp only [hc, ↓reduceIte] at hok
    simp [bind, Except.bind] at hok

lemma scanValuePrepare_fields (s : ScannerState) :
    (scanValuePrepare s).line = s.line ∧ (scanValuePrepare s).col = s.col ∧
    (scanValuePrepare s).peek? = s.peek? ∧
    (scanValuePrepare s).simpleKeyStack = s.simpleKeyStack ∧
    ((scanValuePrepare s).simpleKey.possible = false ∨ (scanValuePrepare s).simpleKey = s.simpleKey) := by
  unfold scanValuePrepare
  split
  · split
    · split
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
      · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
    · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
  · split
    · exact ⟨rfl, rfl, rfl, rfl, Or.inl rfl⟩
    · split
      · obtain ⟨a, b, c⟩ := pushMappingIndent_cursor s (s.col : Int)
        exact ⟨a, b, c, L4YAML.Proofs.ScannerCorrectness.pushMappingIndent_preserves_simpleKeyStack s _,
          Or.inr (L4YAML.Proofs.ScannerCorrectness.pushMappingIndent_preserves_simpleKey s _)⟩
      · exact ⟨rfl, rfl, rfl, rfl, Or.inr rfl⟩

/-- The `:` opener's floor: with a live key the block mapping opens at the
    KEY's column, which the carrier's key lane puts at or left of the cursor. -/
lemma scanValuePrepare_floor {s : ScannerState}
    (hk : s.inFlow = false → s.simpleKey.possible = true → (s.simpleKey.pos.col : Int) ≤ s.col)
    (hfl : s.currentIndent ≤ (s.col : Int)) :
    (scanValuePrepare s).currentIndent ≤ (s.col : Int) := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    split
    · rename_i hnf
      split
      · show ((_ : ScannerState)).currentIndent ≤ _
        simp only [ScannerState.currentIndent]
        rw [Array.back?_push]
        simp only []
        exact hk (by simpa using hnf) h_poss
      · exact hfl
    · exact hfl
  · split
    · exact hfl
    · split
      · exact L4YAML.Proofs.IndentStackCover.pushMappingIndent_top_le hfl
      · exact hfl

lemma scanValue_colfloor {s s' : ScannerState} (hpk : s.peek? = some ':')
    (hok : scanValue s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  obtain ⟨hkl, hkc, hkpk, hkst, hkf, hksk⟩ := scanValueClearKey_fields s
  obtain ⟨hpl, hpc, hppk, hpst, hpsk⟩ := scanValuePrepare_fields (scanValueClearKey s)
  have hkind := (PendingKeySound.scanValueClearKey_core s).1
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  have hval : ∃ u, scanValueValidate (scanValueClearKey s) = .ok u := by
    cases hx : scanValueValidate (scanValueClearKey s) with
    | error e => rw [hx] at hok; simp at hok
    | ok u => exact ⟨u, rfl⟩
  obtain ⟨u, hval⟩ := hval
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  have hok' := Except.ok.inj hok
  have hsl : s'.line = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.line := by
    rw [← hok']
  have hsc : s'.col = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.col := by
    rw [← hok']
  have hsi : s'.indents = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.indents := by
    rw [← hok']
  have hssk : s'.simpleKey = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.simpleKey := by
    rw [← hok']
  have hsst : s'.simpleKeyStack =
      ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.simpleKeyStack := by
    rw [← hok']
  have hadv := Forward.advance_of_nb (s := (scanValuePrepare (scanValueClearKey s)).emit .value)
    (c := ':') (by rw [emit_peek, hppk, hkpk]; exact hpk) (by decide)
  have hl' : s'.line = s.line := ((hsl.trans hadv.1).trans hpl).trans hkl
  have hc' : s'.col = s.col + 1 := by
    rw [hsc, hadv.2]; exact congrArg (· + 1) (hpc.trans hkc)
  have hf : Forward s s' := Forward.of_same_line hl' (by rw [hc']; exact Nat.le_succ _)
  have hkey_kc : (scanValueClearKey s).inFlow = false →
      (scanValueClearKey s).simpleKey.possible = true →
      ((scanValueClearKey s).simpleKey.pos.col : Int) ≤ (scanValueClearKey s).col := by
    intro hnf hp
    have hline := scanValueValidate_key_line hval hnf hp
    rcases hksk with heq | hcl
    · rw [heq] at hp hline ⊢
      rw [hkl] at hline
      have hb := h.key hp
      unfold Behind at hb
      rw [hkc]
      omega
    · rw [hcl] at hp; cases hp
  have hfl_kc : (scanValueClearKey s).currentIndent ≤ ((scanValueClearKey s).col : Int) := by
    rw [currentIndent_of_indents_eq hkind, hkc]; exact hfl
  have hpfl := scanValuePrepare_floor hkey_kc hfl_kc
  refine h.of_forward_or hf ?_ ?_ ?_
  · rw [hssk, L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKey,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKey]
    rcases hpsk with hcl | heq
    · exact Or.inr hcl
    · rw [heq]; exact hksk
  · rw [hsst, L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerCorrectness.emit_preserves_simpleKeyStack, hpst, hkst]
  · intro _
    rw [hc']
    have hind' : s'.indents = (scanValuePrepare (scanValueClearKey s)).indents := by
      rw [hsi, L4YAML.Proofs.ScannerLoopInvariant.advance_indents, L4YAML.Proofs.ScannerContracts.emit_indents]
    rw [currentIndent_of_indents_eq hind']
    rw [hkc] at hpfl
    push_cast; omega

lemma dispatchBlockIndicators_colfloor {s s' : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h : ColFloor s)
    (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals (first
    | (rename_i hcond _ _ hbe
       simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
       obtain ⟨⟨hc, hnf⟩, _⟩ := hcond
       subst hc
       exact scanBlockEntry_colfloor hnf hpk hbe h hfl)
    | (rename_i _ hcond _ _ hk
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨⟨⟨hc, _⟩, _⟩, _⟩ := hcond
       subst hc
       exact scanKey_colfloor hpk hk h hfl)
    | (rename_i _ _ hcond _ _ hv
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨hc, _⟩ := hcond
       subst hc
       exact scanValue_colfloor hpk hv h hfl))

/-! ## §7  Content arms -/

/-- A same-line step that moves the cursor right and keeps keys, stack and
    indents keeps the whole carrier (the floor is unconditional). -/
lemma ColFloor.of_cursor {s s' : ScannerState} (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int))
    (hl : s'.line = s.line) (hc : s.col ≤ s'.col) (hind : s'.indents = s.indents)
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' :=
  h.of_forward (Forward.of_same_line hl hc) hsk hst (fun _ => floor_of_same_line hfl hind hl hc)

/-- A scalar step: the cursor moves forward; on its entry line the column
    only grew, off it the cursor is strictly past the floor. -/
lemma ColFloor.of_scalar {s s' : ScannerState} (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int))
    (hline : s.line ≤ s'.line) (hsame : s'.line = s.line → s.col ≤ s'.col)
    (hcross : s'.line ≠ s.line → s.currentIndent < (s'.col : Int))
    (hind : s'.indents = s.indents)
    (hsk : s'.simpleKey = s.simpleKey) (hst : s'.simpleKeyStack = s.simpleKeyStack) : ColFloor s' := by
  have hf : Forward s s' := by
    rcases Nat.lt_or_eq_of_le hline with hlt | heq
    · exact Or.inl hlt
    · exact Or.inr ⟨heq.symm, hsame heq.symm⟩
  refine h.of_forward hf hsk hst ?_
  intro _
  rw [currentIndent_of_indents_eq hind]
  by_cases heq : s'.line = s.line
  · have := hsame heq; omega
  · exact Int.le_of_lt (hcross heq)

lemma scanDoubleQuoted_colfloor {s s' : ScannerState} (hpk : s.peek? = some '"')
    (hok : scanDoubleQuoted s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hline : s.line ≤ s'.line := by
    unfold scanDoubleQuoted at hok
    simp only [bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i res h_loop
      have h_fields : s'.line = res.2.line := by
        repeat (any_goals (split at hok))
        all_goals (try contradiction)
        all_goals (first
          | (rw [← Except.ok.inj hok]; done)
          | (rw [← Except.ok.inj hok]; simp only [ScannerState.emitAt]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; simp only [ScannerState.emitAt]))
      rw [h_fields]
      have h1 := L4YAML.Proofs.ScalarProduction.collectDoubleQuotedLoop_line_ge s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd 0 h_loop
      have h2 := (Forward.advance_of_nb hpk (by decide)).1
      omega
  exact h.of_scalar hfl hline
    (fun hl => L4YAML.Proofs.ScalarWalkColFloor.scanDoubleQuoted_sameline_col_ge hpk hok hl)
    (fun hne => L4YAML.Proofs.ScalarWalkColFloor.scanDoubleQuoted_crossline_col_floor hpk hok hne)
    (L4YAML.Proofs.EmitterScannability.scanDoubleQuoted_preserves_indents s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s s' hok)

lemma scanSingleQuoted_colfloor {s s' : ScannerState} (hpk : s.peek? = some '\'')
    (hok : scanSingleQuoted s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hline : s.line ≤ s'.line := by
    unfold scanSingleQuoted at hok
    simp only [bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i res h_loop
      have h_fields : s'.line = res.2.line := by
        repeat (any_goals (split at hok))
        all_goals (try contradiction)
        all_goals (first
          | (rw [← Except.ok.inj hok]; done)
          | (rw [← Except.ok.inj hok]; simp only [ScannerState.emitAt]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
          | (simp only [Except.ok.injEq] at hok; rw [← hok]; simp only [ScannerState.emitAt]))
      rw [h_fields]
      have h1 := L4YAML.Proofs.ScalarProduction.collectSingleQuotedLoop_line_ge s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd h_loop
      have h2 := (Forward.advance_of_nb hpk (by decide)).1
      omega
  exact h.of_scalar hfl hline
    (fun hl => L4YAML.Proofs.ScalarWalkColFloor.scanSingleQuoted_sameline_col_ge hpk hok hl)
    (fun hne => L4YAML.Proofs.ScalarWalkColFloor.scanSingleQuoted_crossline_col_floor hpk hok hne)
    (L4YAML.Proofs.FlowIndentStable.scanSingleQuoted_preserves_indents hok)
    (L4YAML.Proofs.ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s s' hok)
    (L4YAML.Proofs.ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s s' hok)

/-- **The flow plain-scalar loop keeps the cursor on its entry line (column
    grown) or strictly past the enclosing block floor** — the `[69]
    s-flow-line-prefix(n)` check on every folded continuation
    (`underIndentedScalar`), item 50 §8.1. -/
lemma collectPlainScalarLoop_flow_inv (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie l₀ c₀ : Nat) (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel true ci ie = .ok r →
    ((s.line = l₀ ∧ c₀ ≤ s.col) ∨ (l₀ < s.line ∧ s.currentIndent < (s.col : Int))) →
    (r.state.line = l₀ ∧ c₀ ≤ r.state.col) ∨
      (l₀ < r.state.line ∧ r.state.currentIndent < (r.state.col : Int)) := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie l₀ c₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    cases hok; exact hinv
  | succ fuel ih =>
    intro s content spaces ci ie l₀ c₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; exact hinv
    · rename_i c hpk
      split at hok
      · rename_i res hterm
        injection hok with h_eq; subst h_eq
        exact (L4YAML.Proofs.ScalarWalkColFloor.terminates?_state hterm) ▸ hinv
      · have hadv : ∀ s'' : ScannerState, s''.line = s.line → s.col ≤ s''.col → s''.indents = s.indents →
            (s''.line = l₀ ∧ c₀ ≤ s''.col) ∨ (l₀ < s''.line ∧ s''.currentIndent < (s''.col : Int)) := by
          intro s'' hl hc hi
          rw [hl, currentIndent_of_indents_eq hi]
          rcases hinv with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · exact Or.inl ⟨h1, Nat.le_trans h2 hc⟩
          · exact Or.inr ⟨h1, by omega⟩
        split at hok
        · -- line break, flow context: fold, floor check, recurse
          split at hok
          · generalize hfold : foldQuotedNewlines s = fr at hok
            cases fr with
            | error e => simp [bind, Except.bind] at hok
            | ok p =>
              obtain ⟨folded, s_f⟩ := p
              simp only [bind, Except.bind] at hok
              split at hok
              · injection hok with h_eq; subst h_eq; exact hinv
              · split at hok
                · simp [throw, throwThe, MonadExceptOf.throw] at hok
                · rename_i hcheck
                  simp only [Bool.and_eq_true, decide_eq_true_eq, not_and] at hcheck
                  have hlt := L4YAML.Proofs.ScalarProduction.foldQuotedNewlines_line_lt hpk (by assumption) hfold
                  have hinv_f : (s_f.line = l₀ ∧ c₀ ≤ s_f.col) ∨
                      (l₀ < s_f.line ∧ s_f.currentIndent < (s_f.col : Int)) := by
                    right
                    refine ⟨?_, ?_⟩
                    · rcases hinv with ⟨h1, _⟩ | ⟨h1, _⟩ <;> omega
                    · by_cases h0 : s_f.currentIndent ≥ 0
                      · have := hcheck h0; omega
                      · have : (0 : Int) ≤ (s_f.col : Int) := Int.natCast_nonneg _
                        omega
                  generalize h_loop :
                    collectPlainScalarLoop s_f (content ++ folded) "" fuel true ci ie = cont at hok
                  cases cont with
                  | ok inner =>
                    dsimp only at hok
                    split at hok
                    · injection hok with h_eq; subst h_eq; exact hinv
                    · have h_eq := Except.ok.inj hok; subst h_eq
                      exact ih _ _ _ _ _ _ _ _ h_loop hinv_f
                  | error e => simp at hok
          · rename_i hflow; exact absurd rfl hflow
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          split at hok
          · exact ih _ _ _ _ _ _ _ _ hok (hadv s.advance (Forward.advance_of_nb hpk hnb).1
              (by rw [(Forward.advance_of_nb hpk hnb).2]; exact Nat.le_succ _)
              (L4YAML.Proofs.ScannerLoopInvariant.advance_indents s))
          · split at hok
            · injection hok with h_eq; subst h_eq; exact hinv
            · exact ih _ _ _ _ _ _ _ _ hok (hadv s.advance (Forward.advance_of_nb hpk hnb).1
                (by rw [(Forward.advance_of_nb hpk hnb).2]; exact Nat.le_succ _)
                (L4YAML.Proofs.ScannerLoopInvariant.advance_indents s))

lemma scanPlainScalar_colfloor {s s' : ScannerState} (hok : scanPlainScalar s = .ok s')
    (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  have hind := L4YAML.Proofs.FlowIndentStable.scanPlainScalar_preserves_indents hok
  have hsk := L4YAML.Proofs.ScannerCorrectness.scanPlainScalar_preserves_simpleKey s s' hok
  have hst := L4YAML.Proofs.ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack s s' hok
  by_cases hf : s.inFlow = true
  · unfold scanPlainScalar at hok
    simp only [bind, Except.bind, hf, ↓reduceIte] at hok
    split at hok
    · cases hok
    · rename_i r h_loop
      have h_eq := Except.ok.inj hok
      have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
      have h_col : s'.col = r.state.col := by rw [← h_eq]; rfl
      have h_ind : r.state.indents = s.indents := by
        rw [← hind, ← h_eq]; rfl
      rcases collectPlainScalarLoop_flow_inv _ s "" "" s.col s.inputEnd s.line s.col r h_loop
        (Or.inl ⟨rfl, Nat.le_refl _⟩) with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact h.of_cursor hfl (by rw [h_line, h1]) (by rw [h_col]; exact h2) hind hsk hst
      · rw [currentIndent_of_indents_eq h_ind] at h2
        refine h.of_forward (Or.inl (by rw [h_line]; exact h1)) hsk hst ?_
        intro _
        rw [currentIndent_of_indents_eq hind, h_col]; exact Int.le_of_lt h2
  · have hnf : s.inFlow = false := by simpa using hf
    have hline : s.line ≤ s'.line := by
      unfold scanPlainScalar at hok
      simp only [bind, Except.bind, hnf, Bool.false_eq_true, ↓reduceIte] at hok
      split at hok
      · cases hok
      · rename_i r h_loop
        have h_eq := Except.ok.inj hok
        have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
        rw [h_line]
        exact L4YAML.Proofs.ScalarProduction.collectPlainScalarLoop_line_le s "" "" _ false _ s.inputEnd h_loop
    exact h.of_scalar hfl hline
      (fun hl => L4YAML.Proofs.ScalarWalkColFloor.scanPlainScalar_sameline_col_ge hnf hok hl)
      (fun hne => L4YAML.Proofs.ScalarWalkColFloor.scanPlainScalar_crossline_col_floor hnf hok hne)
      hind hsk hst

/-! ### Block scalars

The body walk never moves the cursor backwards (`Forward`), and it either
consumed the header's line break — after which `needIndentCheck` stays set
through the whole body (`collectBlockScalarLoop_nic_mono`) — or the header
ran into end-of-input on its own line, where the column only grew. -/

section BlockScalar
open L4YAML.Scanner L4YAML.Proofs.LineOpenGuard L4YAML.Proofs.IndentStackBase

lemma consumeNewline_forward (s : ScannerState) : Forward s (consumeNewline s) := by
  unfold consumeNewline
  split
  · exact Forward.advance s
  · refine (Forward.advance s).trans ?_
    (try dsimp only)
    split <;> exact Forward.of_fields rfl rfl
  · exact Forward.refl s

lemma consumeExactSpaces_forward (count : Nat) :
    ∀ s : ScannerState, Forward s (consumeExactSpaces s count).2 := by
  induction count with
  | zero => intro s; exact Forward.refl s
  | succ n ih =>
    intro s
    unfold consumeExactSpaces
    split
    · exact (Forward.advance s).trans (ih s.advance)
    · exact Forward.refl s

lemma collectLineContentLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (content : String), Forward s (collectLineContentLoop s content fuel).2 := by
  induction fuel with
  | zero => intro s content; exact Forward.refl s
  | succ n ih =>
    intro s content
    unfold collectLineContentLoop
    split
    · split
      · exact Forward.refl s
      · exact (Forward.advance s).trans (ih _ _)
    · exact Forward.refl s

lemma collectBlockScalarLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (raw : String) (ci ie : Nat),
    Forward s (collectBlockScalarLoop s raw fuel ci ie).2 := by
  induction fuel with
  | zero => intro s raw ci ie; exact Forward.refl s
  | succ n ih =>
    intro s raw ci ie
    unfold collectBlockScalarLoop
    split
    · exact Forward.refl s
    · split
      rename_i sp sa heq
      have h1 : Forward s sa := by
        have := consumeExactSpaces_forward ci s
        rw [heq] at this; exact this
      split
      · exact h1
      · split
        · exact h1.trans ((consumeNewline_forward _).trans (ih _ _ _ _))
        · split
          · exact Forward.refl s
          · (try dsimp only)
            have h2 := collectLineContentLoop_forward (ie - sa.offset + 1) sa ""
            split
            · split
              · exact h1.trans (h2.trans ((consumeNewline_forward _).trans (ih _ _ _ _)))
              · split
                · exact Forward.refl s
                · exact h1.trans h2
            · (try dsimp only)
              (try split) <;> exact h1.trans h2

lemma parseBlockHeaderLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (ch : ChompStyle) (m : Option Nat),
    Forward s (parseBlockHeaderLoop s ch m fuel).2.2 := by
  induction fuel with
  | zero => intro s ch m; exact Forward.refl s
  | succ n ih =>
    intro s ch m
    unfold parseBlockHeaderLoop
    split
    · exact (Forward.advance s).trans (ih _ _ _)
    · exact (Forward.advance s).trans (ih _ _ _)
    · split
      · exact (Forward.advance s).trans (ih _ _ _)
      · exact Forward.refl s
    · exact Forward.refl s

lemma parseBlockHeaderLoop_line (fuel : Nat) :
    ∀ (s : ScannerState) (ch : ChompStyle) (m : Option Nat),
    (parseBlockHeaderLoop s ch m fuel).2.2.line = s.line := by
  induction fuel with
  | zero => intro s ch m; unfold parseBlockHeaderLoop; rfl
  | succ n ih =>
    intro s ch m
    unfold parseBlockHeaderLoop
    have hpeek : ∀ c, peekBlockHeaderIndicator? s ch m = some c → s.peek? = some c := by
      intro c h; unfold peekBlockHeaderIndicator? at h
      split at h <;> (try split at h) <;> simp_all
    split
    · rename_i hpk
      rw [ih, advance_preserves_line_of_ne_break s '-' (hpeek _ hpk) (by decide) (by decide)]
    · rename_i hpk
      rw [ih, advance_preserves_line_of_ne_break s '+' (hpeek _ hpk) (by decide) (by decide)]
    · rename_i c _ _ hpk
      split
      · rename_i hd
        rw [ih, advance_preserves_line_of_ne_break s c (hpeek _ hpk)]
        · intro hc; subst hc; simp at hd
        · intro hc; subst hc; simp at hd
      · rfl
    · rfl

lemma collectCommentTextLoop_forward (fuel : Nat) :
    ∀ (s : ScannerState) (text : String), Forward s (collectCommentTextLoop s text fuel).2 := by
  induction fuel with
  | zero => intro s text; unfold collectCommentTextLoop; exact Forward.refl s
  | succ n ih =>
    intro s text
    unfold collectCommentTextLoop
    split
    · split
      · exact Forward.refl s
      · exact (Forward.advance s).trans (ih _ _)
    · exact Forward.refl s

lemma scanBlockScalarSkipComment_forward (s : ScannerState) :
    Forward s (scanBlockScalarSkipComment s) := by
  unfold scanBlockScalarSkipComment
  repeat (any_goals (first | (dsimp only; split) | split))
  all_goals (first
    | exact Forward.refl s
    | exact (Forward.advance s).trans
        ((collectCommentTextLoop_forward (s.advance.inputEnd - s.advance.offset) s.advance "").trans
          (Forward.of_fields rfl rfl)))

lemma scanBlockScalarSkipComment_line (s : ScannerState) :
    (scanBlockScalarSkipComment s).line = s.line := by
  unfold scanBlockScalarSkipComment
  split
  · rename_i hpk
    repeat (any_goals (first | (dsimp only; split) | split))
    all_goals (first
      | rfl
      | exact (collectCommentTextLoop_preserves_line s.advance "" (s.advance.inputEnd - s.advance.offset)).trans
          (advance_preserves_line_of_ne_break s '#' hpk (by decide) (by decide)))
  · rfl

lemma skipWhitespace_forward (s : ScannerState) : Forward s (skipWhitespace s) :=
  Forward.of_same_line (skipWhitespace_preserves_line s)
    (L4YAML.Proofs.ScalarWalkColFloor.skipWhitespace_col_ge s)

lemma scanBlockScalarBody_forward {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    Forward s_nl s' := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; (try dsimp only))
  all_goals (exact (collectBlockScalarLoop_forward _ s_nl "" _ _).trans (Forward.of_fields rfl rfl))

lemma scanBlockScalarBody_atEnd_line {s_orig s_nl s' : ScannerState} {chomp : ChompStyle}
    {expl : Option Nat} {isLit : Bool} {startPos : YamlPos}
    (hs : s_nl.peek? = none)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.line = s_nl.line := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; (try dsimp only))
  all_goals (rw [collectBlockScalarLoop_atEnd hs]; unfold ScannerState.emitAt; rfl)

lemma scanBlockScalar_colfloor {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanBlockScalar s = .ok s') (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) :
    ColFloor s' := by
  have hind := scanBlockScalar_preserves_indents hok
  have hsk := L4YAML.Proofs.ScannerCorrectness.scanBlockScalar_clears_simpleKey s s' hok
  have hst := L4YAML.Proofs.ScannerCorrectness.scanBlockScalar_preserves_simpleKeyStack s s' hok
  have hf_hdr : Forward s (scanBlockScalarSkipComment
      (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)) :=
    (Forward.advance s).trans ((parseBlockHeaderLoop_forward 2 _ _ _).trans
      ((skipWhitespace_forward _).trans (scanBlockScalarSkipComment_forward _)))
  have hl_hdr : (scanBlockScalarSkipComment
      (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)).line = s.line := by
    rw [scanBlockScalarSkipComment_line, skipWhitespace_preserves_line, parseBlockHeaderLoop_line,
      (Forward.advance_of_nb hpk hnb).1]
  unfold scanBlockScalar at hok
  dsimp only [] at hok
  split at hok
  · cases hok
  · rename_i s_nl hnl
    have hf_body : Forward s_nl s' := scanBlockScalarBody_forward hok
    have key : Forward (scanBlockScalarSkipComment
        (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)) s_nl ∧
        (s'.needIndentCheck = true ∨
          (s_nl.peek? = none ∧ (scanBlockScalarSkipComment
            (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).2.2)) = s_nl)) := by
      unfold scanBlockScalarConsumeNewline at hnl
      split at hnl
      · rename_i c₀ hpk₀
        split at hnl
        · rename_i hbr₀
          have := Except.ok.inj hnl; subst this
          exact ⟨consumeNewline_forward _, Or.inl (scanBlockScalarBody_nic_mono
            (consumeNewline_needIndentCheck_of_break _ c₀ hpk₀ hbr₀) hok)⟩
        · split at hnl
          · rename_i hnomore
            have hs_eq := Except.ok.inj hnl
            refine ⟨hs_eq ▸ Forward.refl _, Or.inr ⟨?_, hs_eq⟩⟩
            rw [← hs_eq]
            unfold ScannerState.peek?; rw [ite_eq_right]
            simp only [Bool.not_eq_true', ScannerState.hasMore,
              decide_eq_false_iff_not] at hnomore
            exact hnomore
          · cases hnl
      · rename_i hpk₀
        have hs_eq := Except.ok.inj hnl
        exact ⟨hs_eq ▸ Forward.refl _, Or.inr ⟨by rw [← hs_eq]; exact hpk₀, hs_eq⟩⟩
    refine h.of_forward_cleared (hf_hdr.trans (key.1.trans hf_body)) hsk hst ?_
    intro hnic
    rcases key.2 with hn | ⟨hpkn, hs_eq⟩
    · rw [hn] at hnic; cases hnic
    · rw [currentIndent_of_indents_eq hind, scanBlockScalarBody_atEnd hpkn hok, ← hs_eq]
      have := hf_hdr.col_le_of_line_eq hl_hdr
      omega

end BlockScalar

/-! ### The content dispatcher -/

open L4YAML.Proofs.StaleCursorFloor L4YAML.Proofs.ScannerCorrectness L4YAML.Proofs.BlockScalarFlowGuard L4YAML.Scanner in
lemma dispatchContent_colfloor {s s' : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (h : ColFloor s) (hfl : s.currentIndent ≤ (s.col : Int)) : ColFloor s' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '&': anchor, then the definedAnchors touch-up
    split at hok
    · simp at hok
    split at hok
    · simp at hok
    · rename_i s_a h_anch
      simp only [Except.ok.injEq] at hok; subst hok
      obtain ⟨hl, hc, hi⟩ := scanAnchorOrAlias_cursor hpk hnb h_anch
      exact (h.of_cursor hfl hl hc hi (scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
        (scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch)).of_fields_eq
        rfl rfl rfl rfl rfl rfl
  · split at hok
    · -- '*': alias
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · replace hok := aliasArm_scan_ok hok
        obtain ⟨hl, hc, hi⟩ := scanAnchorOrAlias_cursor hpk hnb hok
        exact h.of_cursor hfl hl hc hi (scanAnchorOrAlias_preserves_simpleKey s false s' hok)
          (scanAnchorOrAlias_preserves_simpleKeyStack s false s' hok)
    · split at hok
      · -- '!': tag
        rename_i h_c
        split at hok
        · simp at hok
        · have h_cq : c = '!' := by simpa using h_c
          subst h_cq
          obtain ⟨hl, hc, hi⟩ := scanTag_cursor hpk hok
          exact h.of_cursor hfl hl hc hi (scanTag_preserves_simpleKey s s' hok)
            (scanTag_preserves_simpleKeyStack s s' hok)
      · split at hok
        · -- '|' / '>'
          exact scanBlockScalar_colfloor hpk hnb (peel_blockScalarGuard hok) h hfl
        · split at hok
          · -- '"'
            rename_i h_c
            split at hok
            · simp at hok
            · rename_i s_dq h_dq
              have h_cq : c = '"' := by simpa using h_c
              subst h_cq
              have hcf := scanDoubleQuoted_colfloor hpk h_dq h hfl
              split at hok <;> (simp only [Except.ok.injEq] at hok; subst hok)
              · exact hcf.of_touchup rfl rfl rfl rfl rfl rfl rfl
              · exact hcf
          · split at hok
            · -- '\''
              rename_i h_c
              split at hok
              · simp at hok
              · rename_i s_sq h_sq
                have h_cq : c = '\'' := by simpa using h_c
                subst h_cq
                have hcf := scanSingleQuoted_colfloor hpk h_sq h hfl
                split at hok <;> (simp only [Except.ok.injEq] at hok; subst hok)
                · exact hcf.of_touchup rfl rfl rfl rfl rfl rfl rfl
                · exact hcf
            · split at hok
              · exact scanPlainScalar_colfloor hok h hfl
              · simp at hok

/-! ## §8  The token step and the seed -/

/-- The character preprocessing hands the dispatchers is never a line break
    (`skipToContent` consumes every break before stopping). -/
lemma preprocess_not_break {s sp : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (sp, c))) : isLineBreakBool c = false := by
  have hpeek := L4YAML.Proofs.ScannerCorrectness.preprocess_peek_eq s sp c hok
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    split at hok
    · simp at hok
    · have h_sc_peek : s_content.peek? = some c := by
        split at hok
        all_goals (
          split at hok
          <;> (try simp at hok)
          <;> (split at hok
            <;> (try simp at hok)
            <;> (obtain ⟨h1, _⟩ := hok; subst h1
                 first
                 | (rw [L4YAML.Proofs.PendingKeySound.closeStaleExplicitKey_peek, L4YAML.Proofs.ScanStrictCoupling.saveSimpleKey_peek] at hpeek
                    unfold ScannerState.peek? unwindIndents at hpeek
                    simp only [L4YAML.Proofs.ScanStrictCoupling.unwindIndentsLoop_offset, L4YAML.Proofs.ScanStrictCoupling.unwindIndentsLoop_inputEnd,
                      L4YAML.Proofs.ScanStrictCoupling.unwindIndentsLoop_input] at hpeek
                    exact hpeek)
                 | (rw [L4YAML.Proofs.PendingKeySound.closeStaleExplicitKey_peek, L4YAML.Proofs.ScanStrictCoupling.saveSimpleKey_peek] at hpeek
                    exact hpeek))))
      exact L4YAML.Proofs.PreprocessProduction.skipToContent_peek_not_break s s_content c h_skip h_sc_peek

/-- **`ColFloor` through one token** — the carrier the flip's premise is read
    off at every `scanLoop` boundary. -/
lemma scanNextToken_colfloor {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s')) (h : ColFloor s) (hbase : SentinelBase s) : ColFloor s' := by
  unfold scanNextToken at hok
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at hok
  split at hok
  · cases hok
  · split at hok
    · simp at hok
    · rename_i sp c h_pre
      have hcf : ColFloor sp := preprocess_colfloor h_pre h hbase
      have hpk : sp.peek? = some c := L4YAML.Proofs.ScannerCorrectness.preprocess_peek_eq s sp c h_pre
      have hnb : isLineBreakBool c = false := preprocess_not_break h_pre
      have hpb : SentinelBase sp := L4YAML.Proofs.IndentStackBase.preprocess_base h_pre hbase
      have hnic : sp.inFlow = false → sp.needIndentCheck = false := by
        intro hnf
        have hfl := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sp c h_pre
        have hnf0 : s.inFlow = false := by
          first
            | simpa [ScannerState.inFlow, hfl] using hnf
            | simpa [ScannerState.inFlow, ← hfl] using hnf
        exact L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hnf0 h_pre
      split at hok
      · cases hok
      split at hok
      · cases hok
      split at hok
      · cases hok
      · split at hok
        · rename_i s_ds h_ds
          simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
          exact dispatchStructural_colfloor hpk h_ds hcf hpb (dispatchStructural_floor h_ds hcf hnic)
        · rename_i h_ds
          have hfl : sp.currentIndent ≤ (sp.col : Int) := dispatchStructural_floor h_ds hcf hnic
          split at hok
          · cases hok
          split at hok
          · cases hok
          · rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at hok
            · generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_colfloor hpk h_fi hcf hfl
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_colfloor hpk h_bi hcf hfl
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_colfloor hpk hnb h_dc hcf hfl
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at hok
              have hcf2 : ColFloor sp2 := by
                rw [← h_sp2]; exact hcf.of_fields_eq rfl rfl rfl rfl rfl rfl
              have hpk2 : sp2.peek? = some c := by rw [← h_sp2]; exact hpk
              have hfl2 : sp2.currentIndent ≤ (sp2.col : Int) := by rw [← h_sp2]; exact hfl
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at hok
              cases fi with
              | error => cases hok
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                  exact dispatchFlowIndicators_colfloor hpk2 h_fi hcf2 hfl2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at hok
                  cases bi with
                  | error => cases hok
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                      exact dispatchBlockIndicators_colfloor hpk2 h_bi hcf2 hfl2
                    | none =>
                      generalize h_av : scanNextToken_checkAdjacentValue sp2 c = av at hok
                      cases av with
                      | error => cases hok
                      | ok _ =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at hok
                      cases dc with
                      | error => cases hok
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok
                        exact dispatchContent_colfloor hpk2 hnb h_dc hcf2 hfl2

/-- **The consumer item 338 left STARVED**: `scanNextToken_sound` with its
    `PreprocessFloor` premise paid by the carrier.  Both invariants ride one
    token step together. -/
lemma scanNextToken_sound_colfloor {s s' : ScannerState}
    (hok : scanNextToken s = .ok (some s'))
    (h : L4YAML.Proofs.PendingKeySound.Sound s) (hm : L4YAML.Proofs.IndentStackMono.Mono s) (hbase : SentinelBase s) (hcf : ColFloor s) :
    L4YAML.Proofs.PendingKeySound.Sound s' ∧ ColFloor s' :=
  ⟨L4YAML.Proofs.PendingKeySound.scanNextToken_sound hok h hm hbase (preprocessFloor hcf hbase),
   scanNextToken_colfloor hok hcf hbase⟩

/-! ### The `scan` seed: `mk'`, the `streamStart` emission, and §5.2's BOM -/

lemma seed_colfloor (input : String) :
    ColFloor ((ScannerState.mk' input).emit .streamStart) :=
  (mk'_colfloor input).of_fields_eq rfl rfl rfl rfl rfl rfl

lemma seed_bom_colfloor (input : String)
    (hpk : ((ScannerState.mk' input).emit .streamStart).peek? = some '\uFEFF') :
    ColFloor ((ScannerState.mk' input).emit .streamStart).consumeBOM := by
  refine (seed_colfloor input).of_forward_cleared ?_ ?_ ?_ ?_
  · exact Forward.of_same_line (Forward.advance_of_nb hpk (by decide)).1
      (by simp [ScannerState.emit, ScannerState.mk'])
  · show (((ScannerState.mk' input).emit .streamStart).advance).simpleKey.possible = false
    rw [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKey]
    simp [ScannerState.emit, ScannerState.mk']
  · exact L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack _
  · intro _
    show (((ScannerState.mk' input).emit .streamStart).advance).currentIndent ≤ ((0 : Nat) : Int)
    rw [currentIndent_of_indents_eq (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _)]
    simp [ScannerState.emit, ScannerState.mk', ScannerState.currentIndent]

lemma seed_sound (input : String) :
    L4YAML.Proofs.PendingKeySound.Sound ((ScannerState.mk' input).emit .streamStart) :=
  (L4YAML.Proofs.PendingKeySound.mk'_sound input).of_eq rfl rfl rfl rfl rfl rfl

lemma seed_bom_sound (input : String) :
    L4YAML.Proofs.PendingKeySound.Sound ((ScannerState.mk' input).emit .streamStart).consumeBOM :=
  (seed_sound input).of_eq (L4YAML.Proofs.PendingKeysStable.advance_preserves_pendingKeys _) (L4YAML.Proofs.ScannerLoopInvariant.advance_indents _)
    (L4YAML.Proofs.ScannerCorrectness.advance_preserves_flowLevel _) (L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyLine _)
    (L4YAML.Proofs.ExplicitKeyCoupling.advance_preserves_explicitKeyCol _) (L4YAML.Proofs.ScannerCorrectness.advance_preserves_explicitKeyStack _)


/-! ## §9  Item 402 — the live-key-top step

`LiveKeyTop` (item 401, `ScalarWalkColFloor`) rides one token step.  Five stages mirror
`StaleKeyCursorFloor`'s: the preprocess, then the structural, flow, block and content dispatchers.
The preprocess hands the dispatchers `PreLKT`; the fresh save's top is `dispatchStructural_floor`. -/

section StepOpen
open L4YAML.Proofs.EntryBoundaryLayout L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.ScannerCorrectness
open L4YAML.Scanner L4YAML.CharPredicates
open L4YAML.Proofs.ScalarWalkColFloor

/-- The space loop followed by the whitespace loop is the whitespace loop on the summed fuel. -/
lemma skipWhitespaceLoop_skipSpacesLoop (s : ScannerState) (f g : Nat) :
    skipWhitespaceLoop s (f + g) =
      skipWhitespaceLoop (skipSpacesLoop s f) (f + g - ((skipSpacesLoop s f).offset - s.offset)) := by
  induction f generalizing s with
  | zero => simp [skipSpacesLoop]
  | succ f ih =>
    rw [skipSpacesLoop]
    split
    · rename_i hpk
      have hoff : s.advance.offset = s.offset + 1 := by
        have hb : s.offset < s.inputEnd := by
          unfold ScannerState.peek? at hpk
          split at hpk <;> first | assumption | exact absurd hpk (by simp)
        have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = ' ' := by
          unfold ScannerState.peek? at hpk
          split at hpk <;> first | exact Option.some.inj hpk | exact absurd hpk (by simp)
        unfold ScannerState.advance
        simp [hb, hc, String.Pos.Raw.next] <;> decide
      have hge := L4YAML.Proofs.ScannerCorrectness.skipSpacesLoop_offset_ge s.advance f
      have hws : isWhiteSpaceBool ' ' = true := by decide
      have : skipWhitespaceLoop s (f + 1 + g) = skipWhitespaceLoop s.advance (f + g) := by
        rw [show f + 1 + g = (f + g) + 1 by omega, skipWhitespaceLoop, hpk]; simp [hws]
      rw [this, ih s.advance]
      congr 1
      rw [hoff]
      omega
    · simp

lemma skipWhitespace_skipSpaces (s : ScannerState) :
    skipWhitespace (skipSpaces s) = skipWhitespace s := by
  unfold skipWhitespace skipSpaces
  have h := skipWhitespaceLoop_skipSpacesLoop s (s.inputEnd - s.offset) 0
  rw [Nat.add_zero] at h
  rw [h]
  congr 1
  have h1 := L4YAML.Proofs.ScannerCorrectness.skipSpacesLoop_offset_ge s (s.inputEnd - s.offset)
  have h2 : (skipSpacesLoop s (s.inputEnd - s.offset)).inputEnd = s.inputEnd := skipSpaces_inputEnd s
  omega


lemma skipSpacesLoop_peek_ne_space (f : Nat) : ∀ s : ScannerState, s.inputEnd - s.offset ≤ f →
    (skipSpacesLoop s f).peek? ≠ some ' ' := by
  induction f with
  | zero =>
    intro s hf hpk
    unfold skipSpacesLoop at hpk
    unfold ScannerState.peek? at hpk
    split at hpk
    · omega
    · cases hpk
  | succ f ih =>
    intro s hf
    rw [skipSpacesLoop]
    split
    · rename_i hpk
      apply ih
      have hb : s.offset < s.inputEnd := by
        unfold ScannerState.peek? at hpk
        split at hpk <;> first | assumption | exact absurd hpk (by simp)
      have hie : s.advance.inputEnd = s.inputEnd := advance_inputEnd s
      have hlt := L4YAML.Proofs.ScannerCorrectness.advance_increases_offset s (by
        unfold ScannerState.hasMore; exact decide_eq_true hb)
      omega
    · assumption

lemma skipSpaces_peek_ne_space (s : ScannerState) : (skipSpaces s).peek? ≠ some ' ' :=
  skipSpacesLoop_peek_ne_space _ s (Nat.le_refl _)

lemma skipWhitespace_eq_of_peek_none {s : ScannerState} (hpk : s.peek? = none) :
    skipWhitespace s = s := by
  unfold skipWhitespace skipWhitespaceLoop
  split
  · rfl
  · rw [hpk]

/-- (L1) the whitespace step of `skipToContent` is `skipWhitespace` whenever it succeeds. -/
lemma skipToContentWs_ok_eq {s t : ScannerState} (h : skipToContentWs s = .ok t) :
    t = skipWhitespace s := by
  unfold skipToContentWs at h
  split at h
  · dsimp only at h
    simp only [skipWhitespace_skipSpaces] at h
    split at h
    · split at h
      · split at h
        · exact (Except.ok.inj h).symm
        · split at h
          · exact (Except.ok.inj h).symm
          · split at h
            · exact (Except.ok.inj h).symm
            · cases h
        · exact (Except.ok.inj h).symm
      · rename_i hnt
        have ht : t = skipSpaces s := (Except.ok.inj h).symm
        rw [ht, ← skipWhitespace_skipSpaces s]
        cases hp : (skipSpaces s).peek? with
        | none => exact (skipWhitespace_eq_of_peek_none hp).symm
        | some c =>
          have hns : c ≠ ' ' := fun hc => skipSpaces_peek_ne_space s (hc ▸ hp)
          have hnt' : c ≠ '\t' := fun hc => hnt (hc ▸ hp)
          refine (skipWhitespace_eq_of_not_ws hp ?_).symm
          simp [isWhiteSpaceBool, isSpaceBool, isTabBool, hns, hnt']
    · exact (Except.ok.inj h).symm
  · exact (Except.ok.inj h).symm


/-- The whitespace step is the identity on a cursor standing on content. -/
lemma skipToContentWs_id_of_content {s : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hws : isWhiteSpaceBool c = false) : skipToContentWs s = .ok s := by
  have hss : skipSpaces s = s := by
    unfold skipSpaces skipSpacesLoop
    split
    · rfl
    · rw [hpk]
      split
      · rename_i h
        have hc : c = ' ' := Option.some.inj h
        subst hc; simp [isWhiteSpaceBool, isSpaceBool] at hws
      · rfl
  have hsw : skipWhitespace s = s := skipWhitespace_eq_of_not_ws hpk hws
  unfold skipToContentWs
  split
  · dsimp only
    rw [hss, hsw]
    split
    · rw [hpk]
      split
      · rename_i h
        have hc : c = '\t' := Option.some.inj h
        subst hc; simp [isWhiteSpaceBool, isTabBool] at hws
      · rfl
    · rfl
  · rw [hsw]

/-- (L3) `skipToContent` is the identity on a state whose cursor stands on content. -/
lemma skipToContent_id_of_content {s t : ScannerState} {c : Char} (h : skipToContent s = .ok t)
    (hpk : s.peek? = some c) (hws : isWhiteSpaceBool c = false) (hcm : isCommentBool c = false)
    (hbr : isLineBreakBool c = false) : t = s := by
  have hcm' : skipToContentComment s = s := by
    unfold skipToContentComment
    rw [hpk]
    split
    · rename_i h
      have hc : c = '#' := Option.some.inj h
      subst hc; simp [isCommentBool] at hcm
    · rfl
  unfold skipToContent skipToContentLoop at h
  simp only [skipToContentWs_id_of_content hpk hws, hcm', hpk, hbr, Bool.false_eq_true,
    ite_false] at h
  exact (Except.ok.inj h).symm


/-- A comment walk with enough fuel stops at a break or at the end of input. -/
lemma collectCommentTextLoop_peek (fuel : Nat) : ∀ (s : ScannerState) (text : String),
    s.inputEnd - s.offset ≤ fuel →
    (collectCommentTextLoop s text fuel).2.peek? = none ∨
      ∃ c, (collectCommentTextLoop s text fuel).2.peek? = some c ∧ isLineBreakBool c = true := by
  induction fuel with
  | zero =>
    intro s text hf
    left
    unfold collectCommentTextLoop
    dsimp only
    unfold ScannerState.peek?
    split
    · omega
    · rfl
  | succ fuel ih =>
    intro s text hf
    rw [collectCommentTextLoop]
    split
    · rename_i c hpk
      split
      · right; exact ⟨c, hpk, by assumption⟩
      · apply ih
        have hb : s.offset < s.inputEnd := by
          unfold ScannerState.peek? at hpk
          split at hpk <;> first | assumption | exact absurd hpk (by simp)
        have hie : s.advance.inputEnd = s.inputEnd := advance_inputEnd s
        have hlt := L4YAML.Proofs.ScannerCorrectness.advance_increases_offset s (by
          unfold ScannerState.hasMore; exact decide_eq_true hb)
        omega
    · left; assumption


lemma advance_break_line {s : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hc : c = '\n' ∨ c = '\r') : s.advance.line = s.line + 1 := by
  have hb : s.offset < s.inputEnd := by
    unfold ScannerState.peek? at hpk
    split at hpk <;> first | assumption | exact absurd hpk (by simp)
  have hget : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at hpk
    split at hpk <;> first | exact Option.some.inj hpk | exact absurd hpk (by simp)
  unfold ScannerState.advance
  rcases hc with hc | hc <;> subst hc <;> simp [hb, hget]

lemma consumeNewline_line_gt {s : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hbr : isLineBreakBool c = true) : s.line < (consumeNewline s).line := by
  have hb : s.offset < s.inputEnd := by
    unfold ScannerState.peek? at hpk
    split at hpk <;> first | assumption | exact absurd hpk (by simp)
  have hget : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at hpk
    split at hpk <;> first | exact Option.some.inj hpk | exact absurd hpk (by simp)
  unfold consumeNewline
  rw [hpk]
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool, Bool.or_eq_true,
    beq_iff_eq] at hbr
  rcases hbr with hc | hc <;> subst hc
  · show s.line < ({ s.advance with needIndentCheck := true }).line
    dsimp only
    rw [advance_break_line hpk (Or.inl rfl)]; omega
  · have hadv := advance_break_line hpk (Or.inr rfl)
    show s.line < (match s.advance.peek? with
      | some '\n' => { s.advance with
          offset := (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx,
          needIndentCheck := true }
      | _ => { s.advance with needIndentCheck := true }).line
    split <;> dsimp only <;> rw [hadv] <;> omega

/-- The comment step either leaves the cursor alone or consumes a comment to a break or EOF. -/
lemma skipToContentComment_peek (u : ScannerState) :
    (skipToContentComment u).peek? = u.peek? ∨
      (u.peek? = some '#' ∧ ((skipToContentComment u).peek? = none ∨
        ∃ c, (skipToContentComment u).peek? = some c ∧ isLineBreakBool c = true)) := by
  unfold skipToContentComment
  split
  · rename_i hpk
    have hcp := collectCommentTextLoop_peek (u.advance.inputEnd - u.advance.offset) u.advance ""
      (Nat.le_refl _)
    split <;> dsimp only <;> split
    all_goals first
      | (left; rfl)
      | (right
         refine ⟨hpk, ?_⟩
         generalize hcl : collectCommentTextLoop u.advance "" (u.advance.inputEnd - u.advance.offset)
           = r at hcp ⊢
         obtain ⟨text, s'⟩ := r
         dsimp only at hcp ⊢
         rcases hcp with h | ⟨c, hc, hbr⟩
         · left; unfold ScannerState.peek? at h ⊢; exact h
         · right; exact ⟨c, by unfold ScannerState.peek? at hc ⊢; exact hc, hbr⟩)
  · left; rfl

/-- (L2) `skipToContent` that stays on its line reads the whitespace-skipped cursor's character,
    or swallowed a comment up to the end of input. -/
lemma skipToContent_same_line_peek {s t : ScannerState} (h : skipToContent s = .ok t)
    (hl : t.line = s.line) :
    t.peek? = (skipWhitespace s).peek? ∨
      ((skipWhitespace s).peek? = some '#' ∧ t.peek? = none) := by
  unfold skipToContent skipToContentLoop at h
  cases hws : skipToContentWs s with
  | error e => rw [hws] at h; exact absurd h (by simp)
  | ok s1 =>
    rw [hws] at h
    have hs1 : s1 = skipWhitespace s := skipToContentWs_ok_eq hws
    subst hs1
    have hl1 : (skipWhitespace s).line = s.line := skipWhitespace_preserves_line s
    have hl2 : (skipToContentComment (skipWhitespace s)).line = (skipWhitespace s).line :=
      skipToContentComment_preserves_line _
    dsimp only at h
    split at h
    · rename_i c hpk
      split at h
      · exfalso
        rename_i hbr
        have hgt := consumeNewline_line_gt hpk hbr
        have hge : ∀ {u : ScannerState}, skipToContentLoop u (s.inputEnd - s.offset) = .ok t →
            u.line ≤ t.line := fun hu => L4YAML.Proofs.StaleCursorFloor.skipToContentLoop_line_ge _ hu
        split at h <;> have := hge h <;> (try dsimp only at this) <;> omega
      · have ht : t = skipToContentComment (skipWhitespace s) := (Except.ok.inj h).symm
        subst ht
        rcases skipToContentComment_peek (skipWhitespace s) with h1 | ⟨h1, h2 | ⟨d, hd, hbd⟩⟩
        · left; exact h1
        · right; exact ⟨h1, h2⟩
        · exfalso; rw [hpk] at hd; have := Option.some.inj hd; subst this
          rename_i hnb; rw [hbd] at hnb; exact hnb rfl
    · have ht : t = skipToContentComment (skipWhitespace s) := (Except.ok.inj h).symm
      subst ht
      rcases skipToContentComment_peek (skipWhitespace s) with h1 | ⟨h1, h2 | ⟨d, hd, hbd⟩⟩
      · left; exact h1
      · right; exact ⟨h1, h2⟩
      · exfalso; rename_i hn; rw [hn] at hd; cases hd


/-- The unwind is the identity when the top indent is already at or left of the column. -/
lemma unwindIndents_id_of_le {s : ScannerState} {col : Int} (h : s.currentIndent ≤ col) :
    unwindIndents s col = s := by
  unfold unwindIndents unwindIndentsLoop
  split
  · rfl
  · have hng : ¬ (s.currentIndent > col) := Int.not_lt.mpr h
    simp [hng]


/-- `closeStaleExplicitKey` only rewrites the pending-key bookkeeping. -/
lemma closeStaleExplicitKey_shape (s : ScannerState) :
    ∃ pk el ec, closeStaleExplicitKey s =
      { s with pendingKeys := pk, explicitKeyLine := el, explicitKeyCol := ec } := by
  unfold closeStaleExplicitKey
  split
  · exact ⟨s.pendingKeys, s.explicitKeyLine, s.explicitKeyCol, rfl⟩
  · split
    · split
      · exact ⟨_, _, _, rfl⟩
      · exact ⟨s.pendingKeys, s.explicitKeyLine, s.explicitKeyCol, rfl⟩
    · exact ⟨s.pendingKeys, s.explicitKeyLine, s.explicitKeyCol, rfl⟩

/-- `saveSimpleKey` is the identity or a fresh save at the cursor touching only `tokens` and
    `simpleKey`. -/
lemma saveSimpleKey_shape (st : ScannerState) :
    (saveSimpleKey st = st ∧ (st.inFlow = false → st.simpleKeyAllowed = false)) ∨
      ∃ toks sk, sk.possible = true ∧ sk.pos = st.currentPos ∧
        saveSimpleKey st = { st with tokens := toks, simpleKey := sk } := by
  unfold saveSimpleKey
  split
  · left
    refine ⟨rfl, fun hnf => ?_⟩
    rename_i hc
    simp only [Bool.and_eq_true] at hc
    rw [hnf] at hc
    cases hc.1
  · split
    · right; exact ⟨_, _, rfl, rfl, rfl⟩
    · left
      refine ⟨rfl, fun _ => ?_⟩
      simpa using (show ¬ (st.simpleKeyAllowed = true) by assumption)

lemma skipWhitespaceLoop_peek_not_ws (f : Nat) : ∀ (s : ScannerState) (c : Char),
    s.inputEnd - s.offset ≤ f → (skipWhitespaceLoop s f).peek? = some c →
    isWhiteSpaceBool c = false := by
  induction f with
  | zero =>
    intro s c hf hpk
    unfold skipWhitespaceLoop ScannerState.peek? at hpk
    split at hpk
    · omega
    · exact absurd hpk (by simp)
  | succ f ih =>
    intro s c hf
    rw [skipWhitespaceLoop]
    split
    · rename_i d hpk
      split
      · intro hpk'
        apply ih _ _ _ hpk'
        have hb : s.offset < s.inputEnd := by
          unfold ScannerState.peek? at hpk
          split at hpk <;> first | assumption | exact absurd hpk (by simp)
        have hie : s.advance.inputEnd = s.inputEnd := advance_inputEnd s
        have hlt := L4YAML.Proofs.ScannerCorrectness.advance_increases_offset s (by
          unfold ScannerState.hasMore; exact decide_eq_true hb)
        omega
      · intro hpk'
        rw [hpk] at hpk'
        have := Option.some.inj hpk'
        subst this
        rename_i hnw
        exact Bool.eq_false_iff.mpr hnw
    · intro hpk'; rename_i hn; rw [hn] at hpk'; cases hpk'

lemma skipWhitespace_peek_not_ws {s : ScannerState} {c : Char}
    (hpk : (skipWhitespace s).peek? = some c) : isWhiteSpaceBool c = false :=
  skipWhitespaceLoop_peek_not_ws _ s c (Nat.le_refl _) hpk


/-- The unwind never moves the cursor: it only emits `blockEnd`s and pops indents. -/
lemma unwindIndentsLoop_cursor (f : Nat) : ∀ (s : ScannerState) (col : Int),
    (unwindIndentsLoop s col f).offset = s.offset ∧ (unwindIndentsLoop s col f).input = s.input ∧
    (unwindIndentsLoop s col f).inputEnd = s.inputEnd ∧ (unwindIndentsLoop s col f).col = s.col ∧
    (unwindIndentsLoop s col f).line = s.line := by
  induction f with
  | zero => intro s col; unfold unwindIndentsLoop; exact ⟨rfl, rfl, rfl, rfl, rfl⟩
  | succ f ih =>
    intro s col
    rw [unwindIndentsLoop]
    split
    · exact ih _ _
    · exact ⟨rfl, rfl, rfl, rfl, rfl⟩

lemma unwindIndents_peek (s : ScannerState) (col : Int) :
    (unwindIndents s col).peek? = s.peek? := by
  obtain ⟨h1, h2, h3, -, -⟩ := unwindIndentsLoop_cursor s.indents.size s col
  unfold unwindIndents at *
  unfold ScannerState.peek?
  rw [h1, h2, h3]

lemma unwindIndents_col (s : ScannerState) (col : Int) : (unwindIndents s col).col = s.col :=
  (unwindIndentsLoop_cursor s.indents.size s col).2.2.2.1

/-- Stage 1, core: the live-key-top facts after the save-and-close tail of the preprocess, from
    the state the skip (and optional unwind) produced. -/
lemma preprocess_LiveKeyTop_core {s s_u sp : ScannerState}
    (hsp : sp = closeStaleExplicitKey (saveSimpleKey s_u))
    (hkey : s_u.simpleKey = s.simpleKey) (hstk : s_u.simpleKeyStack = s.simpleKeyStack)
    (hfl : s_u.flowLevel = s.flowLevel) (hline : s.line ≤ s_u.line)
    (hcol : s_u.line = s.line → s.col ≤ s_u.col)
    (hci : s.currentIndent ≤ (s_u.col : Int) → s_u.currentIndent ≤ s.currentIndent)
    (htok : s.currentIndent ≤ (s_u.col : Int) → s_u.tokens = s.tokens)
    (hal : s.simpleKeyAllowed = true → s_u.simpleKeyAllowed = true)
    (hpeek : s_u.line = s.line →
      s_u.peek? = (skipWhitespace s).peek? ∨
        ((skipWhitespace s).peek? = some '#' ∧ s_u.peek? = none))
    (hinv : LiveKeyTop s) (hcf : ColFloor s) :
    (sp.simpleKey.possible = true → sp.simpleKey.pos.line = sp.line →
      sp.simpleKey.pos = sp.currentPos ∨
      (sp.currentIndent ≤ (sp.simpleKey.pos.col : Int) ∧ (sp.inFlow = false → KeyFollower sp))) ∧
    (∀ k ∈ sp.simpleKeyStack, k.possible = true → k.pos.line = sp.line →
      sp.currentIndent ≤ (k.pos.col : Int)) ∧
    sp.simpleKeyStack.size = sp.flowLevel ∧
    (sp.inFlow = false → sp.simpleKeyAllowed = true → sp.simpleKey.pos = sp.currentPos) := by
  obtain ⟨pk, el, ec, hcs⟩ := closeStaleExplicitKey_shape (saveSimpleKey s_u)
  have hstack : ∀ k ∈ s_u.simpleKeyStack, k.possible = true → k.pos.line = s_u.line →
      s_u.currentIndent ≤ (k.pos.col : Int) := by
    intro k hk hkp hkl
    rw [hstk] at hk
    obtain ⟨j, hj, hjk⟩ := Array.getElem_of_mem hk
    have hbeh := hcf.stack j hj (hjk ▸ hkp)
    rw [hjk] at hbeh
    have hsl : s_u.line = s.line := by
      rcases hbeh with hlt | ⟨heq, -⟩ <;> omega
    have hfl0 := hinv.2.1 k hk hkp (hkl.trans hsl)
    have hkc : k.pos.col ≤ s.col := by
      rcases hbeh with hlt | ⟨-, hle⟩ <;> omega
    have hc := hcol hsl
    exact Int.le_trans (hci (by omega)) hfl0
  have hsize : s_u.simpleKeyStack.size = s_u.flowLevel := by rw [hstk, hfl]; exact hinv.2.2
  rcases saveSimpleKey_shape s_u with ⟨hid, hna⟩ | ⟨toks, sk, hskp, hskpos, hfresh⟩
  · rw [hcs, hid] at hsp
    subst hsp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro hposs hline'
      change s_u.simpleKey.possible = true at hposs
      change s_u.simpleKey.pos.line = s_u.line at hline'
      right
      rw [hkey] at hposs hline'
      have hbeh := hcf.key hposs
      have hsl : s_u.line = s.line := by
        rcases hbeh with hlt | ⟨heq, -⟩ <;> omega
      obtain ⟨hfl0, hkf⟩ := hinv.1 hposs (hline'.trans hsl)
      have hkc : s.simpleKey.pos.col ≤ s.col := by
        rcases hbeh with hlt | ⟨-, hle⟩ <;> omega
      have hc := hcol hsl
      have hcib : s.currentIndent ≤ (s_u.col : Int) := by omega
      refine ⟨?_, ?_⟩
      · change s_u.currentIndent ≤ (s_u.simpleKey.pos.col : Int)
        rw [hkey]; exact Int.le_trans (hci hcib) hfl0
      · intro hflow
        change s_u.inFlow = false at hflow
        have hflow_s : s.inFlow = false := by
          unfold ScannerState.inFlow at hflow ⊢; rw [← hfl]; exact hflow
        have htk := htok hcib
        have hpl : ({ s_u with pendingKeys := pk, explicitKeyLine := el, explicitKeyCol := ec } :
            ScannerState).peek? = s_u.peek? := rfl
        have hsw : (skipWhitespace
            { s_u with pendingKeys := pk, explicitKeyLine := el, explicitKeyCol := ec }).peek? =
            s_u.peek? := by
          rcases hp : s_u.peek? with _ | d
          · rw [skipWhitespace_eq_of_peek_none (hpl.trans hp)]; exact hpl.trans hp
          · have hd : isWhiteSpaceBool d = false := by
              rcases hpeek hsl with h1 | ⟨-, h2⟩
              · exact skipWhitespace_peek_not_ws (h1.symm.trans hp)
              · rw [h2] at hp; cases hp
            rw [skipWhitespace_eq_of_not_ws (hpl.trans hp) hd]; exact hpl.trans hp
        unfold KeyFollower
        dsimp only
        rw [hsw, htk, hkey]
        rcases hkf hflow_s with h1 | ⟨t, ht, htv, htp, hta⟩ | h3 | ⟨c, hc3, hset⟩
        · left; rw [hsl]; exact h1
        · right; left; exact ⟨t, ht, htv, htp, hal hta⟩
        · right; right; left
          rcases hpeek hsl with h1 | ⟨h2, -⟩
          · rw [h1]; exact h3
          · rw [h2] at h3; cases h3
        · rcases hpeek hsl with h1 | ⟨h2, h4⟩
          · right; right; right; exact ⟨c, h1.trans hc3, hset⟩
          · right; right; left; exact h4
    · intro k hk hkp hkl
      exact hstack k hk hkp hkl
    · exact hsize
    · intro hnf hal
      exfalso
      change s_u.inFlow = false at hnf
      change s_u.simpleKeyAllowed = true at hal
      rw [hna hnf] at hal
      cases hal
  · rw [hcs, hfresh] at hsp
    subst hsp
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro _ _
      left
      exact hskpos
    · intro k hk hkp hkl
      exact hstack k hk hkp hkl
    · exact hsize
    · intro _ _
      exact hskpos

/-- Stage 1 (preprocess): the live-key-top facts survive the preprocess, the fresh save excepted,
    whose top the dispatcher supplies. -/
lemma preprocess_LiveKeyTop {s sp : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess s = .ok (some (sp, c)))
    (hinv : LiveKeyTop s) (hcf : ColFloor s) :
    (sp.simpleKey.possible = true → sp.simpleKey.pos.line = sp.line →
      sp.simpleKey.pos = sp.currentPos ∨
      (sp.currentIndent ≤ (sp.simpleKey.pos.col : Int) ∧ (sp.inFlow = false → KeyFollower sp))) ∧
    (∀ k ∈ sp.simpleKeyStack, k.possible = true → k.pos.line = sp.line →
      sp.currentIndent ≤ (k.pos.col : Int)) ∧
    sp.simpleKeyStack.size = sp.flowLevel ∧
    (sp.inFlow = false → sp.simpleKeyAllowed = true → sp.simpleKey.pos = sp.currentPos) := by
  obtain ⟨s_u, s_skip, hskip, hsp, hu⟩ := L4YAML.Proofs.EntryBoundaryLayout.preprocess_save_elim hok
  have hsk_key := skipToContent_preserves_simpleKey s s_skip hskip
  have hsk_stk := skipToContent_preserves_simpleKeyStack s s_skip hskip
  have hsk_fl := skipToContent_preserves_flowLevel s s_skip hskip
  have hsk_tok := skipToContent_preserves_tokens s s_skip hskip
  have hsk_ind := skipToContent_preserves_indents s s_skip hskip
  have hsk_line : s.line ≤ s_skip.line := by
    unfold skipToContent at hskip
    exact L4YAML.Proofs.StaleCursorFloor.skipToContentLoop_line_ge _ hskip
  have hsk_col : s_skip.line = s.line → s.col ≤ s_skip.col := fun hl =>
    L4YAML.Proofs.StaleCursorFloor.skipToContent_col_ge_of_line_eq hskip hl
  have hsk_ci : s_skip.currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [hsk_ind]
  have hsk_al : s.simpleKeyAllowed = true → s_skip.simpleKeyAllowed = true := fun ha =>
    skipToContent_simpleKeyAllowed_mono s s_skip ha hskip
  have hsk_peek : s_skip.line = s.line →
      s_skip.peek? = (skipWhitespace s).peek? ∨
        ((skipWhitespace s).peek? = some '#' ∧ s_skip.peek? = none) :=
    fun hl => skipToContent_same_line_peek hskip hl
  rcases hu with rfl | rfl
  · exact preprocess_LiveKeyTop_core hsp hsk_key hsk_stk hsk_fl hsk_line hsk_col
      (fun _ => Int.le_of_eq hsk_ci) (fun _ => hsk_tok) hsk_al hsk_peek hinv hcf
  · have hcol := unwindIndents_col s_skip s_skip.col
    have hpk := unwindIndents_peek s_skip s_skip.col
    have hidle : s.currentIndent ≤ (s_skip.col : Int) → unwindIndents s_skip s_skip.col = s_skip :=
      fun hle => unwindIndents_id_of_le (by rw [hsk_ci]; exact hle)
    refine preprocess_LiveKeyTop_core hsp ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ hinv hcf
    · show (unwindIndents s_skip s_skip.col).simpleKey = _
      rw [unwindIndents_preserves_simpleKey, hsk_key]
    · show (unwindIndents s_skip s_skip.col).simpleKeyStack = _
      rw [unwindIndents_preserves_simpleKeyStack, hsk_stk]
    · show (unwindIndents s_skip s_skip.col).flowLevel = _
      rw [unwindIndents_preserves_flowLevel, hsk_fl]
    · show s.line ≤ (unwindIndents s_skip s_skip.col).line
      rw [unwindIndents_preserves_line]; exact hsk_line
    · intro hl
      change (unwindIndents s_skip s_skip.col).line = s.line at hl
      rw [unwindIndents_preserves_line] at hl
      show s.col ≤ (unwindIndents s_skip s_skip.col).col
      rw [hcol]; exact hsk_col hl
    · intro hle
      change s.currentIndent ≤ ((unwindIndents s_skip s_skip.col).col : Int) at hle
      rw [hcol] at hle
      show (unwindIndents s_skip s_skip.col).currentIndent ≤ _
      rw [hidle hle, hsk_ci]
      exact Int.le_refl _
    · intro hle
      change s.currentIndent ≤ ((unwindIndents s_skip s_skip.col).col : Int) at hle
      rw [hcol] at hle
      show (unwindIndents s_skip s_skip.col).tokens = _
      rw [hidle hle, hsk_tok]
    · intro ha
      show (unwindIndents s_skip s_skip.col).simpleKeyAllowed = true
      rw [unwindIndents_preserves_simpleKeyAllowed]; exact hsk_al ha
    · intro hl
      change (unwindIndents s_skip s_skip.col).line = s.line at hl
      rw [unwindIndents_preserves_line] at hl
      have hpl : ({ unwindIndents s_skip s_skip.col with needIndentCheck := false } :
          ScannerState).peek? = s_skip.peek? := by
        show (unwindIndents s_skip s_skip.col).peek? = _
        exact hpk
      rw [hpl]; exact hsk_peek hl


/-! ### Whitespace-skip normalisation for the follower bridge -/

lemma skipWhitespaceLoop_stop (f : Nat) : ∀ (s : ScannerState) (g : Nat), f ≤ g →
    ((skipWhitespaceLoop s f).peek? = none ∨
      ∃ c, (skipWhitespaceLoop s f).peek? = some c ∧ isWhiteSpaceBool c = false) →
    skipWhitespaceLoop s g = skipWhitespaceLoop s f := by
  induction f with
  | zero =>
    intro s g _ hstop
    simp only [skipWhitespaceLoop] at hstop
    cases g with
    | zero => rfl
    | succ g =>
      simp only [skipWhitespaceLoop]
      split
      · rename_i c hpk
        split
        · rename_i hws
          exfalso
          rcases hstop with h | ⟨d, hd, hdw⟩
          · rw [hpk] at h; cases h
          · rw [hpk] at hd; have := Option.some.inj hd; subst this; rw [hws] at hdw; cases hdw
        · rfl
      · rfl
  | succ f ih =>
    intro s g hfg hstop
    cases g with
    | zero => omega
    | succ g =>
      simp only [skipWhitespaceLoop] at hstop ⊢
      cases hp : s.peek? with
      | none => simp only
      | some c =>
        simp only [hp] at hstop ⊢
        by_cases hws : isWhiteSpaceBool c = true
        · simp only [hws, ↓reduceIte] at hstop ⊢
          exact ih _ _ (Nat.le_of_succ_le_succ hfg) hstop
        · simp only [hws, Bool.false_eq_true, ↓reduceIte]

lemma skipWhitespaceLoop_saturate (s : ScannerState) (f : Nat) (hf : s.inputEnd - s.offset ≤ f) :
    skipWhitespaceLoop s f = skipWhitespace s := by
  unfold skipWhitespace
  apply skipWhitespaceLoop_stop _ s f hf
  cases hp : (skipWhitespaceLoop s (s.inputEnd - s.offset)).peek? with
  | none => left; rfl
  | some c => right; exact ⟨c, rfl, skipWhitespaceLoop_peek_not_ws _ s c (Nat.le_refl _) hp⟩

lemma skipTrailingSpaces_eq (f : Nat) : ∀ s : ScannerState,
    skipTrailingSpaces s f = skipWhitespaceLoop s f := by
  induction f with
  | zero => intro s; simp only [skipTrailingSpaces, skipWhitespaceLoop]
  | succ f ih =>
    intro s
    simp only [skipTrailingSpaces, skipWhitespaceLoop]
    split
    · rename_i c _
      have hc : (c == ' ' || c == '\t') = isWhiteSpaceBool c := by
        simp [isWhiteSpaceBool, isSpaceBool, isTabBool]
      rw [hc]
      split
      · exact ih _
      · rfl
    · rfl

lemma isWhiteSpaceBool_false_of_break {c : Char} (h : isLineBreakBool c = true) :
    isWhiteSpaceBool c = false := by
  simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool, Bool.or_eq_true,
    beq_iff_eq] at h
  rcases h with h | h <;> subst h <;> decide

/-- The trailing-content probe read through `skipWhitespace`: the two skips agree at the probe's
    stop because the stop character is never white space. -/
lemma TrailingFollower.skipWhitespace_peek {s : ScannerState} {ie : Nat} (h : TrailingFollower s ie) :
    (skipWhitespace s).peek? = none ∨
      ∃ c, (skipWhitespace s).peek? = some c ∧ (isLineBreakBool c = true ∨ c = '#' ∨ c = ':') := by
  unfold TrailingFollower at h
  rw [skipTrailingSpaces_eq] at h
  have hstop : (skipWhitespaceLoop s (ie - s.offset + 1)).peek? = none ∨
      ∃ c, (skipWhitespaceLoop s (ie - s.offset + 1)).peek? = some c ∧
        isWhiteSpaceBool c = false := by
    rcases h with h | ⟨c, hc, hset⟩
    · exact Or.inl h
    · right
      refine ⟨c, hc, ?_⟩
      rcases hset with hb | hb | hb
      · exact isWhiteSpaceBool_false_of_break hb
      · subst hb; decide
      · subst hb; decide
  rcases Nat.le_total (ie - s.offset + 1) (s.inputEnd - s.offset) with hle | hge
  · have := skipWhitespaceLoop_stop _ s _ hle hstop
    unfold skipWhitespace
    rw [this]; exact h
  · rw [← skipWhitespaceLoop_saturate s _ hge]; exact h

/-- `skipToEndOfLine` parks on a break or at the end of input. -/
lemma skipToEndOfLineLoop_peek (f : Nat) : ∀ s : ScannerState, s.inputEnd - s.offset ≤ f →
    (skipToEndOfLineLoop s f).peek? = none ∨
      ∃ c, (skipToEndOfLineLoop s f).peek? = some c ∧ isLineBreakBool c = true := by
  induction f with
  | zero =>
    intro s hf
    left
    unfold skipToEndOfLineLoop ScannerState.peek?
    split
    · omega
    · rfl
  | succ f ih =>
    intro s hf
    rw [skipToEndOfLineLoop]
    split
    · rename_i c hpk
      split
      · right; exact ⟨c, hpk, by assumption⟩
      · apply ih
        have hb : s.offset < s.inputEnd := by
          unfold ScannerState.peek? at hpk
          split at hpk <;> first | assumption | exact absurd hpk (by simp)
        have hie : s.advance.inputEnd = s.inputEnd := advance_inputEnd s
        have hlt := L4YAML.Proofs.ScannerCorrectness.advance_increases_offset s (by
          unfold ScannerState.hasMore; exact decide_eq_true hb)
        omega
    · left; assumption

lemma skipToEndOfLine_peek (s : ScannerState) :
    (skipToEndOfLine s).peek? = none ∨
      ∃ c, (skipToEndOfLine s).peek? = some c ∧ isLineBreakBool c = true :=
  skipToEndOfLineLoop_peek _ s (Nat.le_refl _)


/-! ### Node-property arms: the emitted property is the last real token on the line -/

lemma scanAnchorOrAlias_property_last {s s' : ScannerState}
    (hok : scanAnchorOrAlias s true = .ok s') :
    lastTokenIsNodePropertyOnLine s'.tokens s.line = true := by
  unfold scanAnchorOrAlias at hok
  dsimp only at hok
  generalize hcol : collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset) = r at hok
  obtain ⟨name, sa⟩ := r
  dsimp only at hok
  split at hok
  · cases hok
  · have hs' := Except.ok.inj hok
    subst hs'
    apply L4YAML.Proofs.PropsRunLineCoupling.lastTokenIsNodePropertyOnLine_of_last
      (t := { pos := s.currentPos, val := YamlToken.anchor name })
    · exact L4YAML.Proofs.PropsRunLineCoupling.lastRealToken_push (by simp)
    · rfl
    · rfl

lemma scanTag_property_last {s s' : ScannerState} (hok : scanTag s = .ok s') :
    lastTokenIsNodePropertyOnLine s'.tokens s.line = true := by
  unfold scanTag at hok
  dsimp only at hok
  split at hok
  · -- verbatim
    unfold scanVerbatimTag at hok
    dsimp only at hok
    generalize hcol : collectVerbatimTagLoop s.advance.advance ""
      (s.currentPos.offset + s.advance.inputEnd - s.advance.advance.offset) = r at hok
    obtain ⟨uri, foundClose, su⟩ := r
    dsimp only at hok
    split at hok
    · cases hok
    · split at hok
      · cases hok
      · simp only [bind, Except.bind, pure, Except.pure] at hok
        have hs' := Except.ok.inj hok
        subst hs'
        apply L4YAML.Proofs.PropsRunLineCoupling.lastTokenIsNodePropertyOnLine_of_last
          (t := { pos := s.currentPos, val := YamlToken.tag "" uri })
        · exact L4YAML.Proofs.PropsRunLineCoupling.lastRealToken_push (by simp)
        · rfl
        · rfl
  · -- secondary
    have hs' := Except.ok.inj hok
    subst hs'
    unfold scanSecondaryTag
    dsimp only
    generalize hcol : collectTagSuffixLoop s.advance.advance ""
      (s.currentPos.offset + s.advance.inputEnd - s.advance.advance.offset) = r
    obtain ⟨suffix, su⟩ := r
    dsimp only
    apply L4YAML.Proofs.PropsRunLineCoupling.lastTokenIsNodePropertyOnLine_of_last
      (t := { pos := s.currentPos, val := YamlToken.tag "!!" suffix })
    · exact L4YAML.Proofs.PropsRunLineCoupling.lastRealToken_push (by simp)
    · rfl
    · rfl
  · -- named
    have hs' := Except.ok.inj hok
    subst hs'
    unfold scanNamedTag
    dsimp only
    generalize hcol : collectTagHandleLoop s.advance "" (s.inputEnd - s.advance.offset) = r
    obtain ⟨chars, foundBang, sh⟩ := r
    dsimp only
    split <;> (
      generalize hcol2 : collectTagSuffixLoop sh _ (s.inputEnd - sh.offset) = r2
      obtain ⟨suffix, su⟩ := r2
      dsimp only
      apply L4YAML.Proofs.PropsRunLineCoupling.lastTokenIsNodePropertyOnLine_of_last
        (t := { pos := s.currentPos, val := YamlToken.tag _ suffix })
      · exact L4YAML.Proofs.PropsRunLineCoupling.lastRealToken_push (by simp)
      · rfl
      · rfl)


/-! ### Cursor facts for the dispatch arms -/

lemma scanDoubleQuoted_line_ge {s s' : ScannerState} (hpk : s.peek? = some '"')
    (hok : scanDoubleQuoted s = .ok s') : s.line ≤ s'.line := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    have h_fields : s'.line = res.2.line := by
      repeat (any_goals (split at hok))
      all_goals (try contradiction)
      all_goals (first
        | (rw [← Except.ok.inj hok]; done)
        | (rw [← Except.ok.inj hok]; simp only [ScannerState.emitAt]; done)
        | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
        | (simp only [Except.ok.injEq] at hok; rw [← hok]; simp only [ScannerState.emitAt]))
    rw [h_fields]
    have h1 := L4YAML.Proofs.ScalarProduction.collectDoubleQuotedLoop_line_ge s.advance "" _ s.currentPos
      s.inFlow s.currentIndent s.inputEnd 0 h_loop
    have h2 := (Forward.advance_of_nb hpk (by decide)).1
    omega

lemma scanSingleQuoted_line_ge {s s' : ScannerState} (hpk : s.peek? = some '\'')
    (hok : scanSingleQuoted s = .ok s') : s.line ≤ s'.line := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    have h_fields : s'.line = res.2.line := by
      repeat (any_goals (split at hok))
      all_goals (try contradiction)
      all_goals (first
        | (rw [← Except.ok.inj hok]; done)
        | (rw [← Except.ok.inj hok]; simp only [ScannerState.emitAt]; done)
        | (simp only [Except.ok.injEq] at hok; rw [← hok]; done)
        | (simp only [Except.ok.injEq] at hok; rw [← hok]; simp only [ScannerState.emitAt]))
    rw [h_fields]
    have h1 := L4YAML.Proofs.ScalarProduction.collectSingleQuotedLoop_line_ge s.advance "" _ s.currentPos
      s.inFlow s.currentIndent s.inputEnd h_loop
    have h2 := (Forward.advance_of_nb hpk (by decide)).1
    omega

lemma pushSequenceIndent_currentPos (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).currentPos = s.currentPos := by
  unfold pushSequenceIndent
  split <;> rfl

lemma scanBlockEntry_back {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanBlockEntry s = .ok s') :
    s'.tokens.back? = some { pos := s.currentPos, val := YamlToken.blockEntry } := by
  unfold scanBlockEntry at hok
  simp only [h_noflow, Bool.not_false, bind, Except.bind, ↓reduceIte] at hok
  split at hok
  · cases hok
  · split at hok
    · cases hok
    · cases hv : scanBlockEntryValidate s with
      | error e => rw [hv] at hok; cases hok
      | ok u =>
        rw [hv] at hok
        have hs' := Except.ok.inj hok
        subst hs'
        show (((pushSequenceIndent s (s.col : Int)).emit .blockEntry).advance).tokens.back? = _
        rw [advance_preserves_tokens]
        unfold ScannerState.emit
        dsimp only
        rw [Array.back?_push, pushSequenceIndent_currentPos]

lemma scanFlowEntry_line {s s' : ScannerState} (hpk : s.peek? = some ',')
    (hok : scanFlowEntry s = .ok s') : s'.line = s.line := by
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals
    have hs' := Except.ok.inj hok
    subst hs'
    exact (emit_advance_cursor hpk (by decide)).1

lemma scanKey_line {s s' : ScannerState} (hpk : s.peek? = some '?')
    (hok : scanKey s = .ok s') : s'.line = s.line := by
  obtain ⟨m, hm, hl, -, -, -⟩ := scanKey_shape hok
  have hmpk : m.peek? = some '?' := by
    rcases hm with rfl | rfl
    · rw [(pushMappingIndent_cursor s _).2.2]; exact hpk
    · exact hpk
  have hml : m.line = s.line := by
    rcases hm with rfl | rfl
    · exact (pushMappingIndent_cursor s _).1
    · rfl
  rw [hl, (emit_advance_cursor hmpk (by decide)).1, hml]


lemma scanValue_line {s s' : ScannerState} (hpk : s.peek? = some ':')
    (hok : scanValue s = .ok s') : s'.line = s.line := by
  obtain ⟨hkl, hkc, hkpk, -, -, -⟩ := scanValueClearKey_fields s
  obtain ⟨hpl, hpc, hppk, -, -⟩ := scanValuePrepare_fields (scanValueClearKey s)
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  have hval : ∃ u, scanValueValidate (scanValueClearKey s) = .ok u := by
    cases hx : scanValueValidate (scanValueClearKey s) with
    | error e => rw [hx] at hok; simp at hok
    | ok u => exact ⟨u, rfl⟩
  obtain ⟨u, hval⟩ := hval
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  split at hok <;> try contradiction
  have hok' := Except.ok.inj hok
  have hsl : s'.line = ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.line := by
    rw [← hok']
  have hadv := Forward.advance_of_nb (s := (scanValuePrepare (scanValueClearKey s)).emit .value)
    (c := ':') (by rw [emit_peek, hppk, hkpk]; exact hpk) (by decide)
  exact ((hsl.trans hadv.1).trans hpl).trans hkl

/-! ### The plain walk's column-0 exit is off its entry line -/

lemma collectPlainScalarLoop_sameline_eq (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat) (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    r.state.line = s.line → r.state.col = s.col → r.state = s := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie r hok _ _
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    rfl
  | succ fuel' ih =>
    intro s content spaces ci ie r hok h_line h_col
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; rfl
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        exact terminates?_state hterm'
      · split at hok
        · rename_i hlb
          split at hok
          · rename_i hflow; simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq; rfl
              · dsimp only [] at hok
                generalize h_loop :
                  collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq; rfl
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exfalso
                    have h1 := L4YAML.Proofs.ScalarProduction.handleBlockLineBreak_line_lt hpk hlb hblk
                    have h2 := L4YAML.Proofs.ScalarProduction.collectPlainScalarLoop_line_le s2 content' ""
                      fuel' false ci ie h_loop
                    omega
                | error e => simp at hok
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          have h_adv_line : s.advance.line = s.line :=
            L4YAML.Scanner.advance_preserves_line_of_ne_break s c hpk
              (by intro hc; rw [hc] at hnb; cases hnb)
              (by intro hc; rw [hc] at hnb; cases hnb)
          have h_adv_col : s.advance.col = s.col + 1 := advance_col_succ_of_peek hpk hnb
          split at hok
          · have := collectPlainScalarLoop_col_ge_of_line_eq _ s.advance content _ ci ie r hok
              (by rw [h_line, h_adv_line])
            omega
          · split at hok
            · injection hok with h_eq; subst h_eq; rfl
            · have := collectPlainScalarLoop_col_ge_of_line_eq _ s.advance _ "" ci ie r hok
                (by rw [h_line, h_adv_line])
              omega

lemma scanPlainScalar_sameline_samecol {s s' : ScannerState} (h_noflow : s.inFlow = false)
    (hok : scanPlainScalar s = .ok s') (h_line : s'.line = s.line) (h_col : s'.col = s.col) :
    s'.offset = s.offset ∧ s'.input = s.input ∧ s'.inputEnd = s.inputEnd := by
  unfold scanPlainScalar at hok
  simp only [h_noflow, bind, Except.bind, Bool.false_eq_true, ↓reduceIte] at hok
  split at hok
  · cases hok
  · rename_i r h_loop
    have h_eq := Except.ok.inj hok
    have hst := collectPlainScalarLoop_sameline_eq _ s "" "" _ _ r h_loop
      (by rw [← h_eq] at h_line; exact h_line) (by rw [← h_eq] at h_col; exact h_col)
    rw [← h_eq]
    show r.state.offset = s.offset ∧ r.state.input = s.input ∧ r.state.inputEnd = s.inputEnd
    rw [hst]; exact ⟨rfl, rfl, rfl⟩

lemma atDocumentBoundary_congr {s t : ScannerState} (ho : s.offset = t.offset)
    (hi : s.input = t.input) (he : s.inputEnd = t.inputEnd) (hc : s.col = t.col) :
    atDocumentBoundary s = atDocumentBoundary t := by
  simp only [atDocumentBoundary, atDocumentStart, atDocumentEnd, ScannerState.peekAt?, ho, hi, he, hc]

lemma dispatchStructural_none_not_boundary {s : ScannerState} {c : Char}
    (h : scanNextToken_dispatchStructural s c = .ok none) :
    (s.col == 0 && atDocumentBoundary s) = false := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  cases hne : (s.col == 0 && atDocumentBoundary s) with
  | false => rfl
  | true =>
    exfalso
    simp only [Bool.and_eq_true, beq_iff_eq, atDocumentBoundary, Bool.or_eq_true] at hne
    obtain ⟨hc0, hb⟩ := hne
    rcases hb with hb | hb <;> simp only [hc0, hb, beq_self_eq_true, Bool.true_and, Bool.and_true,
      Bool.true_or, Bool.or_true, ↓reduceIte] at h <;>
      repeat (any_goals (split at h)) <;> all_goals simp_all

/-! ### The pre-dispatch invariant and the shape lemmas -/

/-- What the dispatch stages know about the preprocessed state: the live same-line key stands at or
    right of the top and, in block context, is either the fresh save at the cursor or stands on a
    `KeyFollower`; stacked keys stand at or right of the top; the stack is in sync with the flow
    level; and in block context an enabled save IS the fresh save. -/
def PreLKT (sp : ScannerState) : Prop :=
  (sp.simpleKey.possible = true → sp.simpleKey.pos.line = sp.line →
    sp.currentIndent ≤ (sp.simpleKey.pos.col : Int) ∧
      (sp.inFlow = false → (sp.simpleKey.pos = sp.currentPos ∨ KeyFollower sp))) ∧
  (∀ k ∈ sp.simpleKeyStack, k.possible = true → k.pos.line = sp.line →
    sp.currentIndent ≤ (k.pos.col : Int)) ∧
  sp.simpleKeyStack.size = sp.flowLevel ∧
  (sp.inFlow = false → sp.simpleKeyAllowed = true → sp.simpleKey.pos = sp.currentPos)

lemma flowLevel_eq_zero_of_not_inFlow {s : ScannerState} (h : s.inFlow = false) : s.flowLevel = 0 := by
  unfold ScannerState.inFlow at h
  simp at h
  omega

lemma stack_empty_of_not_inFlow {s : ScannerState} (h : PreLKT s) (hnf : s.inFlow = false) :
    ∀ k, k ∈ s.simpleKeyStack → False := by
  intro k hk
  obtain ⟨j, hj, -⟩ := Array.getElem_of_mem hk
  have := h.2.2.1
  have := flowLevel_eq_zero_of_not_inFlow hnf
  omega

lemma scanDirective_peek {s s' : ScannerState} (hok : scanDirective s = .ok s') :
    s'.peek? = none ∨ ∃ c, s'.peek? = some c ∧ isLineBreakBool c = true := by
  unfold scanDirective at hok
  split at hok
  · cases hok
  · dsimp only at hok
    generalize hn : collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset) = r at hok
    obtain ⟨name, sn⟩ := r
    dsimp only at hok
    split at hok
    · split at hok
      · have := Except.ok.inj hok; subst this; exact skipToEndOfLine_peek _
      · cases hok
    · split at hok
      · split at hok
        · have := Except.ok.inj hok; subst this; exact skipToEndOfLine_peek _
        · cases hok
      · have := Except.ok.inj hok; subst this
        exact skipToEndOfLine_peek _

/-- A state parked at a break or the end of input is a `KeyFollower` state. -/
lemma KeyFollower.of_break_or_eof {s : ScannerState}
    (h : s.peek? = none ∨ ∃ c, s.peek? = some c ∧ isLineBreakBool c = true) : KeyFollower s := by
  rcases h with h | ⟨c, hc, hb⟩
  · right; right; left; rw [skipWhitespace_eq_of_peek_none h]; exact h
  · right; right; right
    refine ⟨c, ?_, Or.inr (Or.inr (Or.inl hb))⟩
    rw [skipWhitespace_eq_of_not_ws hc (isWhiteSpaceBool_false_of_break hb)]; exact hc

/-- A state whose trailing probe stops on a break, `#` or `:` (or the end of input) is a
    `KeyFollower` state. -/
lemma KeyFollower.of_trailing {s : ScannerState} {ie : Nat} (h : TrailingFollower s ie) :
    KeyFollower s := by
  rcases TrailingFollower.skipWhitespace_peek h with h | ⟨c, hc, hset⟩
  · right; right; left; exact h
  · right; right; right
    refine ⟨c, hc, ?_⟩
    rcases hset with h | h | h
    · exact Or.inr (Or.inr (Or.inl h))
    · exact Or.inr (Or.inl h)
    · exact Or.inl h

lemma scanDocumentStart_LiveKeyTop {sp : ScannerState} (h : PreLKT sp) (hnf : sp.inFlow = false) :
    LiveKeyTop (scanDocumentStart sp) := by
  refine ⟨fun hp => ?_, fun k hk => ?_, ?_⟩
  · rw [L4YAML.Proofs.LineOpenGuard.scanDocumentStart_simpleKey_false] at hp; cases hp
  · rw [scanDocumentStart_preserves_simpleKeyStack] at hk
    exact (stack_empty_of_not_inFlow h hnf k hk).elim
  · rw [scanDocumentStart_preserves_simpleKeyStack, scanDocumentStart_preserves_flowLevel]
    exact h.2.2.1

lemma scanDocumentEnd_LiveKeyTop {sp s' : ScannerState} (hok : scanDocumentEnd sp = .ok s')
    (h : PreLKT sp) (hnf : sp.inFlow = false) : LiveKeyTop s' := by
  refine ⟨fun hp => ?_, fun k hk => ?_, ?_⟩
  · rw [L4YAML.Proofs.LineOpenGuard.scanDocumentEnd_simpleKey_false hok] at hp; cases hp
  · rw [scanDocumentEnd_preserves_simpleKeyStack sp s' hok] at hk
    exact (stack_empty_of_not_inFlow h hnf k hk).elim
  · rw [scanDocumentEnd_preserves_simpleKeyStack sp s' hok, scanDocumentEnd_preserves_flowLevel sp s' hok]
    exact h.2.2.1

lemma scanDirective_LiveKeyTop {sp s' : ScannerState} (hpk : sp.peek? = some '%')
    (hok : scanDirective sp = .ok s') (h : PreLKT sp) : LiveKeyTop s' := by
  obtain ⟨hl, hind⟩ := L4YAML.Proofs.StaleCursorFloor.scanDirective_line_ind hpk hok
  have hci : s'.currentIndent = sp.currentIndent := currentIndent_of_indents_eq hind
  have hkey := scanDirective_preserves_simpleKey sp s' hok
  have hstk := scanDirective_preserves_simpleKeyStack sp s' hok
  have hfl := scanDirective_preserves_flowLevel sp s' hok
  refine ⟨fun hp hline => ?_, fun k hk hkp hkl => ?_, ?_⟩
  · rw [hkey] at hp hline ⊢
    rw [hl] at hline
    refine ⟨by rw [hci]; exact (h.1 hp hline).1, fun _ => ?_⟩
    exact KeyFollower.of_break_or_eof (scanDirective_peek hok)
  · rw [hstk] at hk; rw [hl] at hkl; rw [hci]; exact h.2.1 k hk hkp hkl
  · rw [hstk, hfl]; exact h.2.2.1


/-! ### Flow arms -/

lemma mem_of_mem_pop {α : Type} {a : Array α} {x : α} (h : x ∈ a.pop) : x ∈ a := by
  obtain ⟨i, hi, rfl⟩ := Array.getElem_of_mem h
  rw [Array.getElem_pop]
  exact Array.getElem_mem _

lemma scanFlowSequenceStart_fields {sp : ScannerState} (hpk : sp.peek? = some '[') :
    (scanFlowSequenceStart sp).simpleKeyStack = sp.simpleKeyStack.push sp.simpleKey ∧
    (scanFlowSequenceStart sp).line = sp.line ∧
    (scanFlowSequenceStart sp).indents = sp.indents := by
  have hcur := emit_advance_cursor (s := { sp with simpleKey := { possible := false } })
    (t := .flowSequenceStart) hpk (by decide)
  unfold scanFlowSequenceStart
  dsimp only
  refine ⟨?_, hcur.1, ?_⟩
  · rw [L4YAML.Proofs.ScannerContracts.advance_preserves_simpleKeyStack]; rfl
  · rw [L4YAML.Proofs.ScannerLoopInvariant.advance_indents]; rfl

lemma scanFlowMappingStart_fields {sp : ScannerState} (hpk : sp.peek? = some '{') :
    (scanFlowMappingStart sp).simpleKeyStack = sp.simpleKeyStack.push sp.simpleKey ∧
    (scanFlowMappingStart sp).line = sp.line ∧
    (scanFlowMappingStart sp).indents = sp.indents := by
  have hcur := emit_advance_cursor (s := { sp with simpleKey := { possible := false } })
    (t := .flowMappingStart) hpk (by decide)
  unfold scanFlowMappingStart
  dsimp only
  refine ⟨?_, hcur.1, ?_⟩
  · rw [L4YAML.Proofs.ScannerContracts.advance_preserves_simpleKeyStack]; rfl
  · rw [L4YAML.Proofs.ScannerLoopInvariant.advance_indents]; rfl

lemma scanFlowSequenceEnd_fields (sp : ScannerState) :
    (scanFlowSequenceEnd sp).simpleKeyStack = sp.simpleKeyStack.pop ∧
    (scanFlowSequenceEnd sp).indents = sp.indents := by
  unfold scanFlowSequenceEnd
  dsimp only
  constructor
  · rw [L4YAML.Proofs.ScannerContracts.advance_preserves_simpleKeyStack]; rfl
  · rw [L4YAML.Proofs.ScannerLoopInvariant.advance_indents]; rfl

lemma scanFlowMappingEnd_fields (sp : ScannerState) :
    (scanFlowMappingEnd sp).simpleKeyStack = sp.simpleKeyStack.pop ∧
    (scanFlowMappingEnd sp).indents = sp.indents := by
  unfold scanFlowMappingEnd
  dsimp only
  constructor
  · rw [L4YAML.Proofs.ScannerContracts.advance_preserves_simpleKeyStack]; rfl
  · rw [L4YAML.Proofs.ScannerLoopInvariant.advance_indents]; rfl

/-- A flow opener: the live key is pushed, the stack gains the top it had, the sync moves with it. -/
lemma flowStart_LiveKeyTop {sp s' : ScannerState} (h : PreLKT sp)
    (hkey : s'.simpleKey.possible = false)
    (hstk : s'.simpleKeyStack = sp.simpleKeyStack.push sp.simpleKey)
    (hl : s'.line = sp.line) (hind : s'.indents = sp.indents)
    (hfl : s'.flowLevel = sp.flowLevel + 1) : LiveKeyTop s' := by
  have hci : s'.currentIndent = sp.currentIndent := currentIndent_of_indents_eq hind
  refine ⟨fun hp => ?_, fun k hk hkp hkl => ?_, ?_⟩
  · rw [hkey] at hp; cases hp
  · rw [hstk] at hk; rw [hl] at hkl; rw [hci]
    rcases Array.mem_push.mp hk with hk | hk
    · exact h.2.1 k hk hkp hkl
    · subst hk; exact (h.1 hkp hkl).1
  · rw [hstk, hfl, Array.size_push]; exact congrArg (· + 1) h.2.2.1

/-- A flow close: the restored key is the stacked one, at or right of the top by the stack clause;
    back at block level the close's trailing probe is its follower. -/
lemma flowEnd_LiveKeyTop {sp s' : ScannerState} (h : PreLKT sp)
    (hkey : s'.simpleKey = sp.simpleKeyStack.back?.getD {})
    (hstk : s'.simpleKeyStack = sp.simpleKeyStack.pop)
    (hl : s'.line = sp.line) (hind : s'.indents = sp.indents)
    (hfl : s'.flowLevel = sp.flowLevel - 1)
    (hv : validateFlowClose s' = .ok ()) : LiveKeyTop s' := by
  have hci : s'.currentIndent = sp.currentIndent := currentIndent_of_indents_eq hind
  refine ⟨fun hp hline => ?_, fun k hk hkp hkl => ?_, ?_⟩
  · rw [hkey] at hp hline ⊢
    cases hb : sp.simpleKeyStack.back? with
    | none => rw [hb] at hp; simp at hp
    | some k =>
      rw [hb, Option.getD_some] at hp hline
      rw [Option.getD_some]
      have hk : k ∈ sp.simpleKeyStack := by
        rw [Array.back?_eq_getElem?] at hb; exact Array.mem_of_getElem? hb
      rw [hl] at hline
      refine ⟨by rw [hci]; exact h.2.1 k hk hp hline, fun hnf => ?_⟩
      exact KeyFollower.of_trailing (validateFlowClose_follower hv (flowLevel_eq_zero_of_not_inFlow hnf))
  · rw [hstk] at hk; rw [hl] at hkl; rw [hci]
    exact h.2.1 k (mem_of_mem_pop hk) hkp hkl
  · rw [hstk, hfl, Array.size_pop, h.2.2.1]

lemma scanFlowEntry_LiveKeyTop {sp s' : ScannerState} (hpk : sp.peek? = some ',')
    (hok : scanFlowEntry sp = .ok s') (h : PreLKT sp) : LiveKeyTop s' := by
  have hl := scanFlowEntry_line hpk hok
  have hci : s'.currentIndent = sp.currentIndent :=
    currentIndent_of_indents_eq (L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hok)
  have hstk := scanFlowEntry_preserves_simpleKeyStack sp s' hok
  have hfl := scanFlowEntry_preserves_flowLevel sp s' hok
  refine ⟨fun hp => ?_, fun k hk hkp hkl => ?_, ?_⟩
  · rw [scanFlowEntry_clears_simpleKey sp s' hok] at hp; cases hp
  · rw [hstk] at hk; rw [hl] at hkl; rw [hci]; exact h.2.1 k hk hkp hkl
  · rw [hstk, hfl]; exact h.2.2.1

lemma dispatchFlowIndicators_LiveKeyTop {sp s' : ScannerState} {c : Char} (hpk : sp.peek? = some c)
    (hok : scanNextToken_dispatchFlowIndicators sp c = .ok (some s')) (h : PreLKT sp) :
    LiveKeyTop s' := by
  unfold scanNextToken_dispatchFlowIndicators at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at hok; subst hok))
  all_goals first
    | (have hc : (c == '[') = true := by assumption
       have hc' : c = '[' := by simpa using hc
       subst hc'
       obtain ⟨h1, h2, h3⟩ := scanFlowSequenceStart_fields hpk
       exact flowStart_LiveKeyTop h (scanFlowSequenceStart_simpleKey_cleared sp) h1 h2 h3
         (L4YAML.Proofs.ScannerContracts.scanFlowSequenceStart_flowLevel sp))
    | (have hc : (c == '{') = true := by assumption
       have hc' : c = '{' := by simpa using hc
       subst hc'
       obtain ⟨h1, h2, h3⟩ := scanFlowMappingStart_fields hpk
       exact flowStart_LiveKeyTop h (scanFlowMappingStart_simpleKey_cleared sp) h1 h2 h3
         (L4YAML.Proofs.ScannerContracts.scanFlowMappingStart_flowLevel sp))
    | (have hc : (c == ']') = true := by assumption
       have hc' : c = ']' := by simpa using hc
       subst hc'
       have hpos : sp.flowLevel > 0 := by
         have hz : ¬ ((sp.flowLevel == 0) = true) := by assumption
         simp at hz; omega
       obtain ⟨h1, h3⟩ := scanFlowSequenceEnd_fields sp
       exact flowEnd_LiveKeyTop h (scanFlowSequenceEnd_simpleKey_restored sp) h1
         (L4YAML.Proofs.StaleCursorFloor.scanFlowSequenceEnd_cursor hpk).1 h3
         (L4YAML.Proofs.ScannerFlowCollection.scanFlowSequenceEnd_flowLevel_pos sp hpos) (by assumption))
    | (have hc : (c == '}') = true := by assumption
       have hc' : c = '}' := by simpa using hc
       subst hc'
       have hpos : sp.flowLevel > 0 := by
         have hz : ¬ ((sp.flowLevel == 0) = true) := by assumption
         simp at hz; omega
       obtain ⟨h1, h3⟩ := scanFlowMappingEnd_fields sp
       exact flowEnd_LiveKeyTop h (scanFlowMappingEnd_simpleKey_restored sp) h1
         (L4YAML.Proofs.StaleCursorFloor.scanFlowMappingEnd_cursor hpk).1 h3
         (L4YAML.Proofs.ScannerFlowCollection.scanFlowMappingEnd_flowLevel_pos sp hpos) (by assumption))
    | (have hc : (c == ',') = true := by assumption
       have hc' : c = ',' := by simpa using hc
       subst hc'; exact scanFlowEntry_LiveKeyTop hpk (by assumption) h)
    | simp_all


/-! ### Block arms -/

/-- The `-` case read off the follower alone (item 401's `dash_case`, without the invariant
    wrapper): a `-` dispatched on a live key's line means the key is the fresh save at the cursor. -/
lemma KeyFollower.dash_fresh {s : ScannerState} (hf : KeyFollower s)
    (hpk : s.peek? = some '-')
    (hnp : lastTokenIsNodePropertyOnLine s.tokens s.line = false)
    (hfresh : s.simpleKeyAllowed = true → s.simpleKey.pos = s.currentPos) :
    s.simpleKey.pos = s.currentPos := by
  have hid := skipWhitespace_eq_of_not_ws hpk (by decide)
  rcases hf with hp | ⟨t, -, -, -, hal⟩ | hn | ⟨c, hc, hset⟩
  · rw [hnp] at hp; cases hp
  · exact hfresh hal
  · rw [hid, hpk] at hn; cases hn
  · rw [hid, hpk] at hc
    have : c = '-' := (Option.some.inj hc).symm
    subst this
    exfalso
    rcases hset with h | h | h | h | h <;>
      first | cases h | (revert h; decide)

lemma scanBlockEntry_LiveKeyTop {sp s' : ScannerState} (hpk : sp.peek? = some '-')
    (hnf : sp.inFlow = false) (hok : scanBlockEntry sp = .ok s') (h : PreLKT sp) :
    LiveKeyTop s' := by
  have hkey := scanBlockEntry_preserves_simpleKey sp s' hok
  obtain ⟨hl, -⟩ := L4YAML.Proofs.StaleCursorFloor.scanBlockEntry_line_col hnf hpk hok
  have hind := L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_indents hnf hok
  have hal := L4YAML.Proofs.PreprocessIndentStable.scanBlockEntry_simpleKeyAllowed hok
  have hback := scanBlockEntry_back hnf hok
  have hnp := scanBlockEntry_not_property hok hnf
  have hstk := scanBlockEntry_preserves_simpleKeyStack sp s' hok
  have hfl := scanBlockEntry_preserves_flowLevel sp s' hok
  refine ⟨fun hp hline => ?_, fun k hk => ?_, ?_⟩
  · rw [hkey] at hp hline ⊢
    rw [hl] at hline
    obtain ⟨hfl0, hfol⟩ := h.1 hp hline
    have hposeq : sp.simpleKey.pos = sp.currentPos := by
      rcases hfol hnf with hfr | hkf
      · exact hfr
      · exact KeyFollower.dash_fresh hkf hpk hnp (h.2.2.2 hnf)
    have hcol : sp.simpleKey.pos.col = sp.col := by rw [hposeq]; rfl
    refine ⟨?_, fun _ => ?_⟩
    · rw [currentIndent_of_indents_eq hind, hcol]
      rcases L4YAML.Proofs.StaleCursorFloor.pushSequenceIndent_currentIndent_ub sp (sp.col : Int)
        with hub | hub
      · rw [hub]; exact Int.le_refl _
      · rw [hub, ← hcol]; exact hfl0
    · right; left
      refine ⟨_, hback, rfl, ?_, hal⟩
      show sp.currentPos = s'.simpleKey.pos
      rw [hkey, hposeq]
  · rw [hstk] at hk
    exact (stack_empty_of_not_inFlow h hnf k hk).elim
  · rw [hstk, hfl]; exact h.2.2.1

/-- A key-clearing indicator (`?`, `:`): the top clause is vacuous; stacked keys keep their top
    because in flow the indents are untouched and in block the stack is empty. -/
lemma cleared_LiveKeyTop {sp s' : ScannerState} (h : PreLKT sp)
    (hkey : s'.simpleKey.possible = false)
    (hstk : s'.simpleKeyStack = sp.simpleKeyStack) (hfl : s'.flowLevel = sp.flowLevel)
    (hl : s'.line = sp.line) (hind : sp.inFlow = true → s'.indents = sp.indents) : LiveKeyTop s' := by
  refine ⟨fun hp => ?_, fun k hk hkp hkl => ?_, ?_⟩
  · rw [hkey] at hp; cases hp
  · rw [hstk] at hk; rw [hl] at hkl
    cases hnf : sp.inFlow with
    | false => exact (stack_empty_of_not_inFlow h hnf k hk).elim
    | true => rw [currentIndent_of_indents_eq (hind hnf)]; exact h.2.1 k hk hkp hkl
  · rw [hstk, hfl]; exact h.2.2.1

lemma scanKey_LiveKeyTop {sp s' : ScannerState} (hpk : sp.peek? = some '?')
    (hok : scanKey sp = .ok s') (h : PreLKT sp) : LiveKeyTop s' :=
  cleared_LiveKeyTop h (scanKey_clears_simpleKey sp s' hok) (scanKey_preserves_simpleKeyStack sp s' hok)
    (scanKey_preserves_flowLevel sp s' hok) (scanKey_line hpk hok)
    (fun hf => L4YAML.Proofs.FlowIndentStable.scanKey_indents_of_inFlow hf hok)

lemma scanValue_LiveKeyTop {sp s' : ScannerState} (hpk : sp.peek? = some ':')
    (hok : scanValue sp = .ok s') (h : PreLKT sp) : LiveKeyTop s' :=
  cleared_LiveKeyTop h (scanValue_clears_simpleKey sp s' hok) (scanValue_preserves_simpleKeyStack sp s' hok)
    (scanValue_preserves_flowLevel sp s' hok) (scanValue_line hpk hok)
    (fun hf => L4YAML.Proofs.FlowIndentStable.scanValue_indents_of_inFlow hf hok)

lemma dispatchBlockIndicators_LiveKeyTop {sp s' : ScannerState} {c : Char} (hpk : sp.peek? = some c)
    (hok : scanNextToken_dispatchBlockIndicators sp c = .ok (some s')) (h : PreLKT sp) :
    LiveKeyTop s' := by
  unfold scanNextToken_dispatchBlockIndicators at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals (first
    | (rename_i hcond _ _ hbe
       simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hcond
       obtain ⟨⟨hc, hnf⟩, _⟩ := hcond
       subst hc
       exact scanBlockEntry_LiveKeyTop hpk hnf hbe h)
    | (rename_i _ hcond _ _ hk
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨⟨⟨hc, _⟩, _⟩, _⟩ := hcond
       subst hc
       exact scanKey_LiveKeyTop hpk hk h)
    | (rename_i _ _ hcond _ _ hv
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨hc, _⟩ := hcond
       subst hc
       exact scanValue_LiveKeyTop hpk hv h))


/-! ### Content arms -/

lemma content_LiveKeyTop {sp s' : ScannerState} (h : PreLKT sp) (hcf : ColFloor sp)
    (hkey : (s'.simpleKey.possible = sp.simpleKey.possible ∧ s'.simpleKey.pos = sp.simpleKey.pos) ∨
      s'.simpleKey.possible = false)
    (hstk : s'.simpleKeyStack = sp.simpleKeyStack) (hfl : s'.flowLevel = sp.flowLevel)
    (hline : sp.line ≤ s'.line) (hind : s'.indents = sp.indents)
    (hfol : s'.inFlow = false → s'.line = sp.line → s'.simpleKey.possible = true → KeyFollower s') :
    LiveKeyTop s' := by
  have hci : s'.currentIndent = sp.currentIndent := currentIndent_of_indents_eq hind
  refine ⟨fun hp hl => ?_, fun k hk hkp hkl => ?_, ?_⟩
  · rcases hkey with ⟨hpos, hp2⟩ | hfalse
    · have hp' : sp.simpleKey.possible = true := by rw [← hpos]; exact hp
      rw [hp2] at hl ⊢
      have hbeh := hcf.key hp'
      have hsl : s'.line = sp.line := by rcases hbeh with hlt | ⟨heq, -⟩ <;> omega
      rw [hsl] at hl
      exact ⟨by rw [hci]; exact (h.1 hp' hl).1, fun hnf => hfol hnf hsl hp⟩
    · rw [hfalse] at hp; cases hp
  · rw [hstk] at hk
    obtain ⟨j, hj, hjk⟩ := Array.getElem_of_mem hk
    have hbeh := hcf.stack j hj (hjk ▸ hkp)
    rw [hjk] at hbeh
    have hsl : s'.line = sp.line := by rcases hbeh with hlt | ⟨heq, -⟩ <;> omega
    rw [hsl] at hkl; rw [hci]; exact h.2.1 k hk hkp hkl
  · rw [hstk, hfl]; exact h.2.2.1

lemma cleared_block_LiveKeyTop {sp s' : ScannerState} (h : PreLKT sp) (hnf : sp.inFlow = false)
    (hkey : s'.simpleKey.possible = false)
    (hstk : s'.simpleKeyStack = sp.simpleKeyStack) (hfl : s'.flowLevel = sp.flowLevel) :
    LiveKeyTop s' := by
  refine ⟨fun hp => ?_, fun k hk => ?_, ?_⟩
  · rw [hkey] at hp; cases hp
  · rw [hstk] at hk; exact (stack_empty_of_not_inFlow h hnf k hk).elim
  · rw [hstk, hfl]; exact h.2.2.1

/-- Export (a)'s stop set is a `KeyFollower` away from the column-0 document boundary. -/
lemma PlainFollower.keyFollower {s : ScannerState} (hp : PlainFollower s)
    (hnb : ¬ (s.col = 0 ∧ atDocumentBoundary s = true)) : KeyFollower s := by
  rcases hp with h | ⟨c, hc, hset⟩ | ⟨hc0, hb⟩
  · right; right; left; rw [skipWhitespace_eq_of_peek_none h]; exact h
  · have hws : isWhiteSpaceBool c = false := by
      rcases hset with h | h | h | h | h
      · subst h; decide
      · subst h; decide
      · exact isWhiteSpaceBool_false_of_break h
      · cases hw : isWhiteSpaceBool c with
        | false => rfl
        | true =>
          exfalso
          simp only [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true, beq_iff_eq] at hw
          rcases hw with rfl | rfl <;> (revert h; decide)
      · subst h; decide
    right; right; right
    refine ⟨c, ?_, ?_⟩
    · rw [skipWhitespace_eq_of_not_ws hc hws]; exact hc
    · rcases hset with h | h | h | h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
      · exact Or.inr (Or.inr (Or.inr (Or.inl h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inr h)))
  · exact (hnb ⟨hc0, hb⟩).elim

lemma scanPlainScalar_LiveKeyTop {sp s' : ScannerState} (hok : scanPlainScalar sp = .ok s')
    (h : PreLKT sp) (hcf : ColFloor sp)
    (hnd : (sp.col == 0 && atDocumentBoundary sp) = false) : LiveKeyTop s' := by
  have hsk := scanPlainScalar_preserves_simpleKey sp s' hok
  have hst := scanPlainScalar_preserves_simpleKeyStack sp s' hok
  have hfl := scanPlainScalar_preserves_flowLevel sp s' hok
  have hind := L4YAML.Proofs.FlowIndentStable.scanPlainScalar_preserves_indents hok
  have hflow : s'.inFlow = sp.inFlow := by unfold ScannerState.inFlow; rw [hfl]
  have hline : sp.line ≤ s'.line := by
    unfold scanPlainScalar at hok
    simp only [bind, Except.bind] at hok
    split at hok
    · cases hok
    · rename_i r h_loop
      have h_eq := Except.ok.inj hok
      have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
      rw [h_line]
      exact L4YAML.Proofs.ScalarProduction.collectPlainScalarLoop_line_le sp "" "" _ sp.inFlow _
        sp.inputEnd h_loop
  refine content_LiveKeyTop h hcf (Or.inl ⟨by rw [hsk], by rw [hsk]⟩) hst hfl hline hind ?_
  intro hnf hl _
  rw [hflow] at hnf
  apply PlainFollower.keyFollower (scanPlainScalar_follower hok hnf)
  rintro ⟨hc0, hb⟩
  have hcge := scanPlainScalar_sameline_col_ge hnf hok hl
  have hcol : s'.col = sp.col := by omega
  have hc0' : sp.col = 0 := by omega
  obtain ⟨ho, hi, he⟩ := scanPlainScalar_sameline_samecol hnf hok hl hcol
  rw [atDocumentBoundary_congr ho hi he hcol] at hb
  simp [hc0', hb] at hnd

lemma quoted_LiveKeyTop {sp s' s'' : ScannerState} (h : PreLKT sp) (hcf : ColFloor sp)
    (hsk : s'.simpleKey = sp.simpleKey) (hst : s'.simpleKeyStack = sp.simpleKeyStack)
    (hfl : s'.flowLevel = sp.flowLevel) (hline : sp.line ≤ s'.line) (hind : s'.indents = sp.indents)
    (htf : sp.inFlow = false → TrailingFollower s' sp.inputEnd)
    (hs'' : s'' = (if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line } } else s')) :
    LiveKeyTop s'' := by
  have hfields : s''.simpleKey.possible = s'.simpleKey.possible ∧
      s''.simpleKey.pos = s'.simpleKey.pos ∧ s''.simpleKeyStack = s'.simpleKeyStack ∧
      s''.flowLevel = s'.flowLevel ∧ s''.line = s'.line ∧ s''.indents = s'.indents ∧
      s''.input = s'.input ∧ s''.offset = s'.offset ∧ s''.inputEnd = s'.inputEnd := by
    subst hs''; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := hfields
  have hflow : s''.inFlow = sp.inFlow := by unfold ScannerState.inFlow; rw [h4, hfl]
  refine content_LiveKeyTop h hcf (Or.inl ⟨by rw [h1, hsk], by rw [h2, hsk]⟩) (h3.trans hst)
    (h4.trans hfl) (by rw [h5]; exact hline) (h6.trans hind) ?_
  intro hnf _ _
  rw [hflow] at hnf
  exact KeyFollower.of_trailing ((htf hnf).congr h7.symm h8.symm h9.symm)

lemma property_LiveKeyTop {sp s' : ScannerState} (h : PreLKT sp) (hcf : ColFloor sp)
    (hsk : s'.simpleKey = sp.simpleKey) (hst : s'.simpleKeyStack = sp.simpleKeyStack)
    (hfl : s'.flowLevel = sp.flowLevel) (hl : s'.line = sp.line) (hind : s'.indents = sp.indents)
    (hprop : lastTokenIsNodePropertyOnLine s'.tokens sp.line = true) : LiveKeyTop s' :=
  content_LiveKeyTop h hcf (Or.inl ⟨by rw [hsk], by rw [hsk]⟩) hst hfl (Nat.le_of_eq hl.symm) hind
    (fun _ _ _ => Or.inl (by rw [hl]; exact hprop))

lemma dispatchContent_LiveKeyTop {sp s' : ScannerState} {c : Char}
    (hpk : sp.peek? = some c) (hnb : isLineBreakBool c = false)
    (hok : scanNextToken_dispatchContent sp c = .ok s')
    (h : PreLKT sp) (hcf : ColFloor sp)
    (hnd : (sp.col == 0 && atDocumentBoundary sp) = false) : LiveKeyTop s' := by
  unfold scanNextToken_dispatchContent at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · -- '&'
    split at hok
    · simp at hok
    split at hok
    · simp at hok
    · rename_i s_a h_anch
      simp only [Except.ok.injEq] at hok; subst hok
      obtain ⟨hl, -, hi⟩ := L4YAML.Proofs.StaleCursorFloor.scanAnchorOrAlias_cursor hpk hnb h_anch
      have e1 := scanAnchorOrAlias_preserves_simpleKey sp true s_a h_anch
      have e2 := scanAnchorOrAlias_preserves_simpleKeyStack sp true s_a h_anch
      have e3 := scanAnchorOrAlias_preserves_flowLevel sp true s_a h_anch
      have e4 := scanAnchorOrAlias_property_last h_anch
      refine property_LiveKeyTop h hcf ?_ ?_ ?_ ?_ ?_ ?_
      · exact e1
      · exact e2
      · exact e3
      · exact hl
      · exact hi
      · exact e4
  · split at hok
    · -- '*'
      split at hok
      · simp at hok
      split at hok
      · simp at hok
      · generalize h_al : scanAnchorOrAlias sp false = al at hok
        cases al with
        | error e => simp at hok
        | ok s_a =>
          have hv : validateAliasClose s_a = .ok () ∧ s_a = s' := by
            split at hok
            all_goals first
              | (rename_i u h_u
                 have hu : s_a = u := Except.ok.inj h_u
                 subst hu
                 split at hok
                 all_goals first
                   | (rename_i v h_v; exact ⟨by rw [h_v], Except.ok.inj hok⟩)
                   | cases hok)
              | cases hok
          obtain ⟨h_v, hs⟩ := hv
          subst hs
          · obtain ⟨hl, -, hi⟩ := L4YAML.Proofs.StaleCursorFloor.scanAnchorOrAlias_cursor hpk hnb h_al
            have hfl := scanAnchorOrAlias_preserves_flowLevel sp false s_a h_al
            have hflow : s_a.inFlow = sp.inFlow := by unfold ScannerState.inFlow; rw [hfl]
            refine content_LiveKeyTop h hcf (Or.inl ⟨?_, ?_⟩)
              (scanAnchorOrAlias_preserves_simpleKeyStack sp false s_a h_al) hfl
              (Nat.le_of_eq hl.symm) hi ?_
            · rw [scanAnchorOrAlias_preserves_simpleKey sp false s_a h_al]
            · rw [scanAnchorOrAlias_preserves_simpleKey sp false s_a h_al]
            · intro hnf _ _
              exact KeyFollower.of_trailing (validateAliasClose_follower h_v hnf)
    · split at hok
      · -- '!'
        rename_i h_c
        split at hok
        · simp at hok
        · have h_cq : c = '!' := by simpa using h_c
          subst h_cq
          obtain ⟨hl, -, hi⟩ := L4YAML.Proofs.StaleCursorFloor.scanTag_cursor hpk hok
          exact property_LiveKeyTop h hcf (scanTag_preserves_simpleKey sp s' hok)
            (scanTag_preserves_simpleKeyStack sp s' hok) (scanTag_preserves_flowLevel sp s' hok) hl hi
            (scanTag_property_last hok)
      · split at hok
        · -- '|' / '>'
          have hbs : sp.inFlow = false ∧ scanBlockScalar sp = .ok s' := by
            split at hok
            · simp at hok
            · rename_i hf
              exact ⟨by simpa using hf, hok⟩
          exact cleared_block_LiveKeyTop h hbs.1
            (L4YAML.Proofs.LineOpenGuard.scanBlockScalar_simpleKey_false hbs.2)
            (scanBlockScalar_preserves_simpleKeyStack sp s' hbs.2)
            (scanBlockScalar_preserves_flowLevel sp s' hbs.2)
        · split at hok
          · -- '"'
            rename_i h_c
            split at hok
            · simp at hok
            · rename_i s_dq h_dq
              have h_cq : c = '"' := by simpa using h_c
              subst h_cq
              have hs'' := (Except.ok.inj hok).symm
              exact quoted_LiveKeyTop h hcf (scanDoubleQuoted_preserves_simpleKey sp s_dq h_dq)
                (scanDoubleQuoted_preserves_simpleKeyStack sp s_dq h_dq)
                (scanDoubleQuoted_preserves_flowLevel sp s_dq h_dq) (scanDoubleQuoted_line_ge hpk h_dq)
                (L4YAML.Proofs.EmitterScannability.scanDoubleQuoted_preserves_indents sp s_dq h_dq)
                (fun hnf => scanDoubleQuoted_follower h_dq hnf) hs''
          · split at hok
            · -- '\''
              rename_i h_c
              split at hok
              · simp at hok
              · rename_i s_sq h_sq
                have h_cq : c = '\'' := by simpa using h_c
                subst h_cq
                have hs'' := (Except.ok.inj hok).symm
                exact quoted_LiveKeyTop h hcf (scanSingleQuoted_preserves_simpleKey sp s_sq h_sq)
                  (scanSingleQuoted_preserves_simpleKeyStack sp s_sq h_sq)
                  (scanSingleQuoted_preserves_flowLevel sp s_sq h_sq) (scanSingleQuoted_line_ge hpk h_sq)
                  (L4YAML.Proofs.FlowIndentStable.scanSingleQuoted_preserves_indents h_sq)
                  (fun hnf => scanSingleQuoted_follower h_sq hnf) hs''
            · split at hok
              · exact scanPlainScalar_LiveKeyTop hok h hcf hnd
              · simp at hok


/-! ### The step -/

lemma PreLKT.of_preprocess {sp : ScannerState}
    (h1 : (sp.simpleKey.possible = true → sp.simpleKey.pos.line = sp.line →
      sp.simpleKey.pos = sp.currentPos ∨
      (sp.currentIndent ≤ (sp.simpleKey.pos.col : Int) ∧ (sp.inFlow = false → KeyFollower sp))) ∧
    (∀ k ∈ sp.simpleKeyStack, k.possible = true → k.pos.line = sp.line →
      sp.currentIndent ≤ (k.pos.col : Int)) ∧
    sp.simpleKeyStack.size = sp.flowLevel ∧
    (sp.inFlow = false → sp.simpleKeyAllowed = true → sp.simpleKey.pos = sp.currentPos))
    (hfl : sp.currentIndent ≤ (sp.col : Int)) : PreLKT sp := by
  obtain ⟨ht, hs, hz, hf⟩ := h1
  refine ⟨fun hp hl => ?_, hs, hz, hf⟩
  rcases ht hp hl with hfr | ⟨hfl0, hkf⟩
  · refine ⟨?_, fun _ => Or.inl hfr⟩
    rw [hfr]; exact hfl
  · exact ⟨hfl0, fun hnf => Or.inr (hkf hnf)⟩

lemma advance_ad (s : ScannerState) :
    ({ s with allowDirectives := false, documentEverStarted := true } : ScannerState).advance =
      { s.advance with allowDirectives := false, documentEverStarted := true } := by
  unfold ScannerState.advance
  dsimp only
  split <;> (try split) <;> (try split) <;> rfl

lemma skipWhitespaceLoop_ad (f : Nat) : ∀ s : ScannerState,
    skipWhitespaceLoop { s with allowDirectives := false, documentEverStarted := true } f =
      { skipWhitespaceLoop s f with allowDirectives := false, documentEverStarted := true } := by
  induction f with
  | zero => intro s; simp only [skipWhitespaceLoop]
  | succ f ih =>
    intro s
    simp only [skipWhitespaceLoop]
    have hpk : ({ s with allowDirectives := false, documentEverStarted := true } :
        ScannerState).peek? = s.peek? := rfl
    rw [hpk]
    split
    · split
      · rw [advance_ad, ih]
      · rfl
    · rfl

lemma skipWhitespace_ad_peek (s : ScannerState) :
    (skipWhitespace { s with allowDirectives := false, documentEverStarted := true }).peek? =
      (skipWhitespace s).peek? := by
  unfold skipWhitespace
  show (skipWhitespaceLoop { s with allowDirectives := false, documentEverStarted := true }
    (s.inputEnd - s.offset)).peek? = _
  rw [skipWhitespaceLoop_ad]; rfl

lemma KeyFollower.ad {s : ScannerState} (h : KeyFollower s) :
    KeyFollower { s with allowDirectives := false, documentEverStarted := true } := by
  unfold KeyFollower at h ⊢
  dsimp only
  rw [skipWhitespace_ad_peek]
  exact h

lemma PreLKT.ad {s : ScannerState} (h : PreLKT s) :
    PreLKT { s with allowDirectives := false, documentEverStarted := true } := by
  obtain ⟨h1, h2, h3, h4⟩ := h
  refine ⟨fun hp hl => ?_, h2, h3, h4⟩
  obtain ⟨hf, hk⟩ := h1 hp hl
  exact ⟨hf, fun hnf => (hk hnf).elim Or.inl (fun hkf => Or.inr (KeyFollower.ad hkf))⟩

lemma dispatchStructural_LiveKeyTop {sp s' : ScannerState} {c : Char} (hpk : sp.peek? = some c)
    (hok : scanNextToken_dispatchStructural sp c = .ok (some s')) (h : PreLKT sp) :
    LiveKeyTop s' := by
  unfold scanNextToken_dispatchStructural at hok
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind] at hok
  repeat (any_goals (split at hok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (have hnf : sp.inFlow = false := by
         cases hf : sp.inFlow
         · rfl
         · exfalso; simp_all
       exact scanDocumentStart_LiveKeyTop h hnf)
    | (have hnf : sp.inFlow = false := by
         cases hf : sp.inFlow
         · rfl
         · exfalso; simp_all
       exact scanDocumentEnd_LiveKeyTop (by assumption) h hnf)
    | (have hcond : (c == '%' && sp.col == 0) = true := by assumption
       simp only [Bool.and_eq_true, beq_iff_eq] at hcond
       obtain ⟨hc, hc0⟩ := hcond
       subst hc
       exact scanDirective_LiveKeyTop hpk (by assumption) h)

/-- **Item 402 — the step.**  `LiveKeyTop` rides one token step (with `ColFloor` and the
    sentinel base, which `scanNextToken_colfloor` carries alongside). -/
lemma scanNextToken_preserves_LiveKeyTop (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (h_inv : LiveKeyTop s) (hcf : ColFloor s)
    (hbase : L4YAML.Proofs.IndentStackBase.SentinelBase s) : LiveKeyTop s' := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  split at h
  · cases h
  · split at h
    · simp at h
    · rename_i sp c h_pre
      have hcfp : ColFloor sp := preprocess_colfloor h_pre hcf hbase
      have hpk : sp.peek? = some c := preprocess_peek_eq s sp c h_pre
      have hnb : isLineBreakBool c = false := preprocess_not_break h_pre
      have hnic : sp.inFlow = false → sp.needIndentCheck = false := by
        intro hnf
        have hfl := L4YAML.Proofs.EmitterScannability.preprocess_preserves_flowLevel s sp c h_pre
        have hnf0 : s.inFlow = false := by
          first
            | simpa [ScannerState.inFlow, hfl] using hnf
            | simpa [ScannerState.inFlow, ← hfl] using hnf
        exact L4YAML.Proofs.PropsRunLineCoupling.preprocess_some_needIndentCheck_false hnf0 h_pre
      have hpre := preprocess_LiveKeyTop h_pre h_inv hcf
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
      · split at h
        · rename_i s_ds h_ds
          simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact dispatchStructural_LiveKeyTop hpk h_ds
            (PreLKT.of_preprocess hpre (dispatchStructural_floor h_ds hcfp hnic))
        · rename_i h_ds
          have hfl : sp.currentIndent ≤ (sp.col : Int) := dispatchStructural_floor h_ds hcfp hnic
          have hP : PreLKT sp := PreLKT.of_preprocess hpre hfl
          have hnd := dispatchStructural_none_not_boundary h_ds
          split at h
          · cases h
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
                  exact dispatchFlowIndicators_LiveKeyTop hpk h_fi hP
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at h
                  cases bi with
                  | error => cases h
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      exact dispatchBlockIndicators_LiveKeyTop hpk h_bi hP
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
                        exact dispatchContent_LiveKeyTop hpk hnb h_dc hP hcfp hnd
            · generalize h_sp2 :
                (({ sp with allowDirectives := false, documentEverStarted := true }
                  : ScannerState)) = sp2 at h
              have hP2 : PreLKT sp2 := by rw [← h_sp2]; exact hP.ad
              have hcf2 : ColFloor sp2 := by
                rw [← h_sp2]; exact hcfp.of_fields_eq rfl rfl rfl rfl rfl rfl
              have hpk2 : sp2.peek? = some c := by rw [← h_sp2]; exact hpk
              have hnd2 : (sp2.col == 0 && atDocumentBoundary sp2) = false := by
                rw [← h_sp2]; exact hnd
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at h
              cases fi with
              | error => cases h
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  exact dispatchFlowIndicators_LiveKeyTop hpk2 h_fi hP2
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at h
                  cases bi with
                  | error => cases h
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      exact dispatchBlockIndicators_LiveKeyTop hpk2 h_bi hP2
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
                        exact dispatchContent_LiveKeyTop hpk2 hnb h_dc hP2 hcf2 hnd2

/-! ### The `scan` seed carries `LiveKeyTop` (item 402): `mk'` saves no key, holds an
    empty key stack at flow level 0, and the `streamStart` emission and §5.2's BOM
    advance keep all three. -/

lemma seed_LiveKeyTop (input : String) :
    LiveKeyTop ((ScannerState.mk' input).emit .streamStart) := by
  refine ⟨fun h _ => absurd h ?_, fun k hk => absurd hk ?_, ?_⟩
  · simp [ScannerState.emit, ScannerState.mk']
  · simp [ScannerState.emit, ScannerState.mk']
  · simp [ScannerState.emit, ScannerState.mk']

lemma seed_bom_LiveKeyTop (input : String) :
    LiveKeyTop ((ScannerState.mk' input).emit .streamStart).consumeBOM := by
  refine ⟨fun h _ => absurd h ?_, fun k hk => absurd hk ?_, ?_⟩
  · show (((ScannerState.mk' input).emit .streamStart).advance).simpleKey.possible ≠ true
    rw [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKey]
    simp [ScannerState.emit, ScannerState.mk']
  · show k ∉ (((ScannerState.mk' input).emit .streamStart).advance).simpleKeyStack
    rw [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack]
    simp [ScannerState.emit, ScannerState.mk']
  · show (((ScannerState.mk' input).emit .streamStart).advance).simpleKeyStack.size =
      (((ScannerState.mk' input).emit .streamStart).advance).flowLevel
    rw [L4YAML.Proofs.ScannerCorrectness.advance_preserves_simpleKeyStack,
      L4YAML.Proofs.ScannerContracts.advance_preserves_flowLevel]
    simp [ScannerState.emit, ScannerState.mk']

end StepOpen

end L4YAML.Proofs.ColFloor
