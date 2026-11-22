/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Scanner.PreprocessIndentStable
public import L4YAML.Proofs.Scanner.BlockScalarFlowGuard
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Coupling.ScalarCoupling
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-!
# The indent stack stands still inside a flow collection (DOCS item 67)

`[137] c-flow-sequence(n,c)` and `[140] c-flow-mapping(n,c)` are read at ONE
index from the open to the close — the enclosing block context's — so the
accumulation's flow stack carries that index and every interior step has to
hand it back with its floor intact.  It can, and for a structural reason that
costs no induction over the token walk: **nothing inside a flow writes
`indents` at all.**  There are exactly three writers, and all three are
guarded by `!inFlow`:

* §6.1's `unwindIndents`, inside `scanNextToken_preprocess`;
* `[183]`'s `pushSequenceIndent`, inside `scanBlockEntry` — whose dispatch arm
  also tests `!s.inFlow`, so the `-` never reaches the scan;
* `[187]`'s `pushMappingIndent`, inside `scanKey` and inside
  `scanValuePrepare` (the implicit key's).

So the whole file is the same observation made once per dispatcher, over the
scans a flow interior can reach.  Item 66's `preprocess_indents_or_underIndent`
asked the harder question — what preprocessing does when the unwind DID pop —
and is not needed here: `skipToContent` neither opens nor closes a collection,
so the guard that is false at the step's start is false where the unwind reads
it, and the whole `if` is the identity.

The other export is a column fact rather than an indent one, and the interior
needs it in its own right: `scanNextToken_dispatchStructural`'s first check
refuses a flow-interior token at or left of `currentIndent`, so a fall-through
says the column CLEARED the floor — which is what puts the plain walk's
`contentIndent` (its own start column) above the floor its continuation lines
are measured against.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.FlowIndentStable

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML.Scanner
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.ScalarCoupling (terminates_state_eq)

/-! ## §1  The structural check, read as a column fact -/

/-- **A flow-interior token stands past the enclosing block indent.**
    `scanNextToken_dispatchStructural`'s FIRST test errors on
    `inFlow ∧ currentIndent ≥ 0 ∧ col ≤ currentIndent`, so a fall-through
    (`.ok none`) inside a flow says the column cleared the floor.  The
    `currentIndent < 0` case needs no check at all: a column is a `Nat`. -/
lemma structural_none_col_gt_of_inFlow {s : ScannerState} {c : Char}
    (h_flow : s.inFlow = true)
    (h : scanNextToken_dispatchStructural s c = .ok none) :
    s.currentIndent < (s.col : Int) := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hneg
    have hcol : (0 : Int) ≤ (s.col : Int) := Int.natCast_nonneg _
    have hneg' : ¬ (0 ≤ s.currentIndent ∧ (s.col : Int) ≤ s.currentIndent) := by
      intro hc
      refine hneg ?_
      simp only [h_flow, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, ge_iff_le]
      exact hc
    omega

/-- **Preprocessing writes no indent inside a flow.**  Its one writer is
    §6.1's armed unwind, whose guard is `!inFlow` — and `skipToContent` cannot
    change that, since it neither opens nor closes a collection. -/
lemma preprocess_indents_of_inFlow {sc s_prep : ScannerState} {c : Char}
    (h_flow : sc.inFlow = true)
    (h : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.indents = sc.indents := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · exact absurd h (by simp)
  · rename_i s_skip h_skip
    have h_ind_skip : s_skip.indents = sc.indents :=
      skipToContent_preserves_indents sc s_skip h_skip
    have h_flow_skip : s_skip.inFlow = true := by
      unfold ScannerState.inFlow at h_flow ⊢
      rw [ScannerCorrectness.skipToContent_preserves_flowLevel sc s_skip h_skip]
      exact h_flow
    have hcond : (!s_skip.inFlow && s_skip.needIndentCheck) = false := by
      simp [h_flow_skip]
    simp only [hcond, ite_eq_right Bool.false_ne_true] at h
    split at h
    · exact absurd h (by simp)
    · split at h
      · exact absurd h (by simp)
      · split at h
        · exact absurd h (by simp)
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, -⟩ := h
          exact (closeStaleExplicitKey_indents _).trans ((saveSimpleKey_preserves_indents s_skip).trans h_ind_skip)

/-! ## §2  The scans a flow interior can reach leave `indents` alone -/

/-- `scanSingleQuoted`'s twin of `scanDoubleQuoted_preserves_indents`. -/
lemma collectSingleQuotedLoop_preserves_indents (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (inputEnd : Nat) (result : String × ScannerState)
    (h : collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd
         = .ok result) : result.2.indents = s.indents := by
  induction fuel generalizing s content with
  | zero => unfold collectSingleQuotedLoop at h; contradiction
  | succ f ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · contradiction
    · simp only [] at h
      split at h
      · rw [ih _ _ h,
            L4YAML.Proofs.EmitterScannability.advance_preserves_indents s.advance,
            L4YAML.Proofs.EmitterScannability.advance_preserves_indents s]
      · injection h with h_eq; cases h_eq
        exact L4YAML.Proofs.EmitterScannability.advance_preserves_indents s
    · split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
            s (folded, s_fold) heq
          repeat' split at h
          all_goals (first | contradiction | rw [ih s_fold _ h, h_fold])
      · split at h <;> try contradiction
        rw [ih s.advance _ h, L4YAML.Proofs.EmitterScannability.advance_preserves_indents s]

/-- `scanSingleQuoted` writes tokens and key state, never `indents`. -/
lemma scanSingleQuoted_preserves_indents {s s' : ScannerState}
    (h : scanSingleQuoted s = .ok s') : s'.indents = s.indents := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i result heq
    have hres := collectSingleQuotedLoop_preserves_indents s.advance "" _ _ _ _ _ result heq
    split at h
    · split at h <;> try contradiction
      injection h with h_eq; subst h_eq
      simpa using hres.trans (L4YAML.Proofs.EmitterScannability.advance_preserves_indents s)
    · injection h with h_eq; subst h_eq
      simpa using hres.trans (L4YAML.Proofs.EmitterScannability.advance_preserves_indents s)

/-- The plain walk's blank-line skipper leaves the stack alone. -/
lemma skipBlankLinesLoop_preserves_indents (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).2.indents = s.indents := by
  induction fuel generalizing s cnt with
  | zero => rfl
  | succ f ih =>
    unfold skipBlankLinesLoop; dsimp only []
    split
    · split
      · -- item 100: the gate's arm keeps the stack
        split
        · rfl
        · rw [ih, L4YAML.Proofs.EmitterScannability.consumeNewline_preserves_indents,
              skipWhitespace_preserves_indents]
      · rfl
    · rfl

/-- Nor does the block line-break handler. -/
lemma handleBlockLineBreak_preserves_indents {s s' : ScannerState}
    {content content' : String} {contentIndent inputEnd : Nat}
    (h : collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd
         = some (content', s')) : s'.indents = s.indents := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      rw [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
          skipBlankLinesLoop_preserves_indents,
          L4YAML.Proofs.EmitterScannability.consumeNewline_preserves_indents]

/-- The plain collect loop leaves the stack alone in BOTH contexts. -/
lemma collectPlainScalarLoop_preserves_indents (s : ScannerState)
    (content spaces : String) (fuel : Nat) (inFlow : Bool)
    (contentIndent inputEnd : Nat) (result : PlainScalarResult)
    (h : collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd
         = .ok result) : result.state.indents = s.indents := by
  induction fuel generalizing s content spaces with
  | zero => simp only [collectPlainScalarLoop, Except.ok.injEq] at h; subst h; rfl
  | succ f ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · simp only [Except.ok.injEq] at h; subst h; rfl
    · split at h
      · rename_i r_term h_term
        simp only [Except.ok.injEq] at h; subst h
        rw [terminates_state_eq _ s content spaces inFlow r_term h_term]
      · split at h
        · split at h
          · -- flow break
            simp only [bind, Except.bind] at h
            split at h
            · exact absurd h (by simp)
            · rename_i fold_result hfold
              have hf := L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                s fold_result hfold
              split at h
              · simp only [Except.ok.injEq] at h; subst h; rfl
              · split at h
                · exact absurd h (by simp)
                · generalize h_loop : collectPlainScalarLoop fold_result.2
                      (content ++ fold_result.1) "" f inFlow contentIndent inputEnd = cont at h
                  cases cont with
                  | error e => simp at h
                  | ok inner =>
                    dsimp only [] at h
                    split at h
                    · simp only [Except.ok.injEq] at h; subst h; rfl
                    · simp only [Except.ok.injEq] at h; subst h
                      exact (ih _ _ _ h_loop).trans hf
          · -- block break
            split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · rename_i content' s_b hblk
              have hb := handleBlockLineBreak_preserves_indents hblk
              split at h
              · simp only [Except.ok.injEq] at h; subst h; rfl
              · generalize h_loop : collectPlainScalarLoop s_b content' "" f inFlow
                  contentIndent inputEnd = cont at h
                cases cont with
                | error e => simp at h
                | ok inner =>
                  dsimp only [] at h
                  split at h
                  · simp only [Except.ok.injEq] at h; subst h; rfl
                  · simp only [Except.ok.injEq] at h; subst h
                    exact (ih _ _ _ h_loop).trans hb
        · split at h
          · exact (ih _ _ _ h).trans
              (L4YAML.Proofs.EmitterScannability.advance_preserves_indents s)
          · split at h
            · simp only [Except.ok.injEq] at h; subst h; rfl
            · exact (ih _ _ _ h).trans
                (L4YAML.Proofs.EmitterScannability.advance_preserves_indents s)

/-- `scanPlainScalar` writes tokens and key state, never `indents`. -/
lemma scanPlainScalar_preserves_indents {s s' : ScannerState}
    (h : scanPlainScalar s = .ok s') : s'.indents = s.indents := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h
  · exact absurd h (by simp)
  · rename_i result hloop
    simp only [Except.ok.injEq] at h
    subst h
    simpa using collectPlainScalarLoop_preserves_indents s _ _ _ _ _ _ result hloop

/-- `scanValuePrepare`'s two `[187]` pushes are both `!inFlow`-guarded. -/
lemma scanValuePrepare_indents_of_inFlow {s : ScannerState} (h_flow : s.inFlow = true) :
    (scanValuePrepare s).indents = s.indents := by
  unfold scanValuePrepare
  split
  · rw [ite_eq_right (by simp [h_flow])]
  · split
    · rfl
    · rw [ite_eq_right (by simp [h_flow])]

/-- …so the `:` scan writes no indent inside a flow. -/
lemma scanValue_indents_of_inFlow {s s' : ScannerState}
    (h_flow : s.inFlow = true) (hok : scanValue s = .ok s') :
    s'.indents = s.indents := by
  have key : (((scanValuePrepare (scanValueClearKey s)).emit YamlToken.value).advance).indents
      = s.indents := by
    rw [L4YAML.Proofs.EmitterScannability.advance_preserves_indents, emit_indents,
        scanValuePrepare_indents_of_inFlow
          (by rw [(scanValueClearKey_fields s).2.2.1]; exact h_flow)]
    exact (scanValueClearKey_fields s).2.1
  unfold scanValue at hok
  simp only [bind, Except.bind] at hok
  repeat' split at hok
  all_goals first
    | contradiction
    | (simp only [Except.ok.injEq] at hok; subst hok; exact key)

/-- `scanKey`'s `[187]` push is `!inFlow`-guarded too. -/
lemma scanKey_indents_of_inFlow {s s' : ScannerState}
    (h_flow : s.inFlow = true) (hok : scanKey s = .ok s') :
    s'.indents = s.indents := by
  unfold scanKey at hok
  simp only [bind, Except.bind, h_flow, Bool.not_true, ite_eq_right Bool.false_ne_true] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]

/-! ## §3  The dispatchers -/

/-- The content dispatch never writes the indent stack: every arm is a scalar,
    an alias or a property scan, and the one arm that could push — a block
    scalar header — is `!inFlow`-refused before it is reached (and pushes
    nothing either way). -/
lemma dispatchContent_preserves_indents {s s' : ScannerState} {c : Char}
    (h_flow : s.inFlow = true)
    (h : scanNextToken_dispatchContent s c = .ok s') : s'.indents = s.indents := by
  obtain ⟨hnotPipe, hnotGt⟩ :=
    Proofs.BlockScalarFlowGuard.dispatchContent_not_blockScalar_of_inFlow h_flow h
  by_cases hc_amp : c = '&'
  · exact dispatchContent_props_indents (Or.inl hc_amp) h
  · by_cases hc_bang : c = '!'
    · exact dispatchContent_props_indents (Or.inr hc_bang) h
    · unfold scanNextToken_dispatchContent at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      rw [ite_eq_right (by simpa using hc_amp)] at h
      by_cases hc_star : c = '*'
      · subst hc_star
        rw [ite_eq_left (by simp)] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          replace h := aliasArm_scan_ok h
          generalize h_fn : scanAnchorOrAlias s false = res at h
          cases res with
          | error e => simp at h
          | ok s_a =>
            try dsimp only [] at h
            simp only [Except.ok.injEq] at h; subst h
            exact scanAnchorOrAlias_preserves_indents h_fn

      · rw [ite_eq_right (by simpa using hc_star), ite_eq_right (by simpa using hc_bang),
            ite_eq_right (by simp [hnotPipe, hnotGt])] at h
        by_cases hc_dq : c = '"'
        · subst hc_dq
          rw [ite_eq_left (by simp)] at h
          generalize h_fn : scanDoubleQuoted s = res at h
          cases res with
          | error e => simp at h
          | ok s_q =>
            have hq := L4YAML.Proofs.EmitterScannability.scanDoubleQuoted_preserves_indents
              s s_q h_fn
            dsimp only [] at h
            split at h <;>
              · simp only [Except.ok.injEq] at h; subst h; simpa using hq
        · rw [ite_eq_right (by simpa using hc_dq)] at h
          by_cases hc_sq : c = '\''
          · subst hc_sq
            rw [ite_eq_left (by simp)] at h
            generalize h_fn : scanSingleQuoted s = res at h
            cases res with
            | error e => simp at h
            | ok s_q =>
              have hq := scanSingleQuoted_preserves_indents h_fn
              dsimp only [] at h
              split at h <;>
                · simp only [Except.ok.injEq] at h; subst h; simpa using hq
          · rw [ite_eq_right (by simpa using hc_sq)] at h
            split at h
            · generalize h_fn : scanPlainScalar s = res at h
              cases res with
              | error e => simp at h
              | ok s_p =>
                simp only [Except.ok.injEq] at h; subst h
                exact scanPlainScalar_preserves_indents h_fn
            · exact absurd h (by simp)

/-- `[7] c-collect-entry` writes a token and clears the key. -/
lemma scanFlowEntry_preserves_indents {s s' : ScannerState}
    (hok : scanFlowEntry s = .ok s') : s'.indents = s.indents := by
  unfold scanFlowEntry at hok
  simp only [bind, Except.bind] at hok
  repeat (any_goals (split at hok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at hok; subst hok)
  all_goals simp [L4YAML.Proofs.EmitterScannability.advance_preserves_indents]

/-- The flow-indicator dispatch writes tokens and the flow stack, never the
    indent stack: `[137]`/`[140]`'s brackets are not block structure. -/
lemma dispatchFlowIndicators_preserves_indents {s s' : ScannerState} {c : Char}
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.indents = s.indents := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq] at h; subst h))
  all_goals first
    | rfl
    | exact L4YAML.Proofs.EmitterScannability.scanFlowSequenceStart_preserves_indents s
    | exact L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s
    | exact L4YAML.Proofs.EmitterScannability.scanFlowMappingStart_preserves_indents s
    | exact L4YAML.Proofs.EmitterScannability.scanFlowMappingEnd_preserves_indents s
    | exact scanFlowEntry_preserves_indents (by assumption)
    | simp_all

/-- The block-indicator dispatch never writes the indent stack inside a flow:
    the `-` arm's own guard tests `!inFlow`, and `scanKey`/`scanValue` push
    only in block context. -/
lemma dispatchBlockIndicators_preserves_indents {s s' : ScannerState} {c : Char}
    (h_flow : s.inFlow = true)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.indents = s.indents := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  repeat' split at h
  all_goals first
    | contradiction
    | (simp only [Except.ok.injEq, Option.some.injEq] at h
       subst h
       first
         | exact scanKey_indents_of_inFlow h_flow (by assumption)
         | exact scanValue_indents_of_inFlow h_flow (by assumption))
    | simp_all

end L4YAML.Proofs.FlowIndentStable

end Blanket
