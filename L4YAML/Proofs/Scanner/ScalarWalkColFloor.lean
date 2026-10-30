/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Production.ScalarProduction
import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-! # The scalar walks' cross-line column floor (DOCS item 122)

The three multi-line content walks are the only scans that can leave a LIVE
simple-key candidate saved on an earlier line than the cursor's — the plain
walk and the two quoted walks save at their start and then fold continuation
lines.  Item 121's `?`-line column bound (U1) needs exactly one fact about
each: **a walk that ends on a line other than its entry line ends with its
column strictly past `currentIndent`.**  Each walk enforces this itself:

* the BLOCK plain walk's continuation gate is its `contentIndent` parameter,
  which `scanPlainScalar` sets to `(max 0 (currentIndent + 1)).toNat` — every
  absorbed landing already clears the block floor STRICTLY, with no premise
  about the walk's own start column;
* both quoted folds throw `underIndentedScalar` on a landing at or left of
  the `currentIndent` parameter (`[69] s-flow-line-prefix(n)`'s `s-indent(n)`,
  §8.1), in BOTH contexts, so an `.ok` exit off the entry line sits strictly
  past it.

Stated per loop as a line-or-floor disjunction (the exit is on the entry
line, or its column clears the floor) and exported per scan in the form the
dispatch layer consumes.  The flow-side twin — a dispatched token inside a
flow sits past the floor — is `FlowIndentStable.structural_none_col_gt_of_inFlow`
already. -/

set_option autoImplicit false

namespace L4YAML.Proofs.ScalarWalkColFloor

open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScalarProduction

/-! ## §1  Column monotonicity of the walks' same-line helpers -/

/-- A non-break `advance` spends exactly one column. -/
lemma advance_col_succ_of_peek {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hnb : isLineBreakBool c = false) :
    s.advance.col = s.col + 1 := by
  unfold ScannerState.peek? at hpk
  split at hpk
  · rename_i hlt
    have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := Option.some.inj hpk
    simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
      Bool.or_eq_false_iff, beq_eq_false_iff_ne] at hnb
    exact advance_col_non_newline s hlt (by rw [hc]; simpa using hnb.1)
      (by rw [hc]; simpa using hnb.2)
  · cases hpk

/-- `s-white` is not `b-char`: the separation walk moves the column only. -/
lemma skipWhitespaceLoop_col_ge (s : ScannerState) (fuel : Nat) :
    s.col ≤ (skipWhitespaceLoop s fuel).col := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; exact Nat.le_refl _
  | succ fuel' ih =>
    unfold skipWhitespaceLoop
    split
    · rename_i c hpk
      split
      · rename_i hws
        have hnb : isLineBreakBool c = false := by
          simp only [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true,
            beq_iff_eq] at hws
          rcases hws with rfl | rfl <;> decide
        calc s.col ≤ s.advance.col := by rw [advance_col_succ_of_peek hpk hnb]; omega
          _ ≤ _ := ih s.advance
      · exact Nat.le_refl _
    · exact Nat.le_refl _

lemma skipWhitespace_col_ge (s : ScannerState) :
    s.col ≤ (skipWhitespace s).col :=
  skipWhitespaceLoop_col_ge s _

/-- `ns-hex-digit` is not `b-char` either: the escape body moves the column
    only (`collectHexDigitsLoop_line`'s column half). -/
private lemma collectHexDigitsLoop_col_ge (s : ScannerState) (hex : String) (n : Nat) :
    s.col ≤ (collectHexDigitsLoop s hex n).2.col := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; exact Nat.le_refl _
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · rename_i c hp
      split
      · rename_i hhex
        have hnb : isLineBreakBool c = false := by
          cases hlb : isLineBreakBool c
          · rfl
          · exfalso
            simp only [isLineBreakBool, isLineFeedBool, isCarriageReturnBool,
              Bool.or_eq_true, beq_iff_eq] at hlb
            rcases hlb with rfl | rfl <;> exact absurd hhex (by decide)
        calc s.col ≤ s.advance.col := by rw [advance_col_succ_of_peek hp hnb]; omega
          _ ≤ _ := ih s.advance (hex.push c)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

private lemma parseHexEscape_col_ge {s : ScannerState} {n : Nat} {ch : Char}
    {s' : ScannerState} (hok : parseHexEscape s n = .ok (ch, s')) :
    s.col ≤ s'.col := by
  unfold parseHexEscape at hok
  dsimp only [] at hok
  split at hok
  · simp at hok
  · split at hok
    · obtain ⟨-, rfl⟩ := hok
      exact collectHexDigitsLoop_col_ge s "" n
    · simp at hok

/-- `[62] c-ns-esc-char` admits no break, so the escape moves the column only
    (`processEscape_line`'s column half; the ESCAPED break is not routed here). -/
private lemma processEscape_col_ge {s : ScannerState} {ch : Char} {s' : ScannerState}
    (hproc : processEscape s = .ok (ch, s')) : s.col ≤ s'.col := by
  unfold processEscape at hproc
  split at hproc
  · simp at hproc
  · rename_i c_esc hpeek
    dsimp only [] at hproc
    split at hproc <;> (first
      | (obtain ⟨-, rfl⟩ := hproc; try subst_vars
         rw [advance_col_succ_of_peek hpeek (by decide)]; omega)
      | skip)
    · -- 'x': hex escape (n = 2)
      try subst_vars
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpeek (by decide)]; omega
        _ ≤ _ := parseHexEscape_col_ge hproc
    · -- 'u': hex escape (n = 4)
      try subst_vars
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpeek (by decide)]; omega
        _ ≤ _ := parseHexEscape_col_ge hproc
    · -- 'U': hex escape (n = 8)
      try subst_vars
      calc s.col ≤ s.advance.col := by
            rw [advance_col_succ_of_peek hpeek (by decide)]; omega
        _ ≤ _ := parseHexEscape_col_ge hproc
    · simp at hproc

/-- **The block fold's landing clears the walk's own gate**: a `some` return
    of `collectPlainScalar_handleBlockLineBreak` sits at or right of
    `contentIndent` — the under-indent test is `[63] s-indent`'s, and the
    `s-separate-in-line` run after it only moves right. -/
private lemma handleBlockLineBreak_col_ge {s s' : ScannerState}
    {content content' : String} {ci ie : Nat}
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s')) :
    ci ≤ s'.col := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only [] at h
  split at h
  · exact absurd h (by simp)
  · rename_i hcol
    split at h
    · exact absurd h (by simp)
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      exact Nat.le_trans (Nat.le_of_not_lt hcol) (skipWhitespace_col_ge _)

/-- The terminator results hand back the walk's CURRENT state. -/
lemma terminates?_state {c : Char} {s : ScannerState}
    {content spaces : String} {inFlow : Bool} {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.state = s := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; subst h; rfl
  · split at h
    · simp only [] at h
      split at h <;> split at h <;> first
        | (injection h with h; subst h; rfl)
        | cases h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · injection h with h; subst h; rfl
        · cases h

/-! ## §2  The walks, as line-or-floor disjunctions -/

/-- **The BLOCK plain walk exits on its entry line or past its gate.**  Every
    recursive step either spends a column on a non-break character or lands a
    fold at `contentIndent` or deeper; the stop paths return a state some
    earlier step certified. -/
lemma collectPlainScalarLoop_line_or_floor (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie l₀ : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    (s.line = l₀ ∨ ci ≤ s.col) →
    r.state.line = l₀ ∨ ci ≤ r.state.col := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie l₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    exact hinv
  | succ fuel' ih =>
    intro s content spaces ci ie l₀ r hok hinv
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq
      exact hinv
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        exact (terminates?_state hterm') ▸ hinv
      · split at hok
        · -- a break, block context
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact hinv
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact hinv
              · dsimp only [] at hok
                generalize h_loop :
                  collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact hinv
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie l₀ _ h_loop
                      (Or.inr (handleBlockLineBreak_col_ge hblk))
                | error e => simp at hok
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          have hstep : s.advance.line = l₀ ∨ ci ≤ s.advance.col := by
            rcases hinv with h | h
            · exact Or.inl ((advance_preserves_line_of_ne_break s c hpk
                (by intro hc; rw [hc] at hnb; cases hnb)
                (by intro hc; rw [hc] at hnb; cases hnb)).trans h)
            · exact Or.inr (by rw [advance_col_succ_of_peek hpk hnb]; omega)
          split at hok
          · exact ih s.advance content _ ci ie l₀ r hok hstep
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact hinv
            · exact ih s.advance _ "" ci ie l₀ r hok hstep

/-- **The double-quoted walk exits on its entry line or past the floor.**  The
    two folds re-establish the strict bound through their own
    `underIndentedScalar` gate; everything else is same-line. -/
private lemma collectDoubleQuotedLoop_line_or_floor (sc : ScannerState)
    (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd protectedLen : Nat) (l₀ : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd protectedLen = .ok (result_content, s'))
    (hinv : sc.line = l₀ ∨ currentIndent < (sc.col : Int)) :
    s'.line = l₀ ∨ currentIndent < (s'.col : Int) := by
  induction fuel generalizing sc content protectedLen with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote
      rename_i _ hpeek
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      rcases hinv with h | h
      · exact Or.inl ((advance_preserves_line_of_ne_break sc '"' hpeek
          (by decide) (by decide)).trans h)
      · exact Or.inr (by rw [advance_col_succ_of_peek hpeek (by decide)]; push_cast; omega)
    · -- backslash
      rename_i _ hpeek
      have hstep : sc.advance.line = l₀ ∨ currentIndent < (sc.advance.col : Int) := by
        rcases hinv with h | h
        · exact Or.inl ((advance_preserves_line_of_ne_break sc '\\' hpeek
            (by decide) (by decide)).trans h)
        · exact Or.inr (by rw [advance_col_succ_of_peek hpeek (by decide)]; push_cast; omega)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break: the landing runs through the fold's own gate
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · rename_i hcol_ok
                exact ih _ _ _ hok (Or.inr (by omega))
        · -- regular escape: same line, column only grows
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            refine ih _ _ _ hok ?_
            rcases hstep with h | h
            · exact Or.inl ((processEscape_line hproc).trans h)
            · exact Or.inr (by
                have := processEscape_col_ge hproc
                omega)
      · exact absurd hok (by simp)
    · -- regular character
      rename_i _opt c hne_dq hne_bs hpeek
      split at hok
      · -- line break: the fold's gate re-establishes the strict bound
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · rename_i hcol_ok
              exact ih _ _ _ hok (Or.inr (by omega))
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have hnb : isLineBreakBool c = false := by simpa using hne_lb
          refine ih _ _ _ hok ?_
          rcases hinv with h | h
          · exact Or.inl ((advance_preserves_line_of_ne_break sc c hpeek
              (by intro hc; rw [hc] at hnb; cases hnb)
              (by intro hc; rw [hc] at hnb; cases hnb)).trans h)
          · exact Or.inr (by rw [advance_col_succ_of_peek hpeek hnb]; push_cast; omega)

/-- `collectSingleQuotedLoop`'s twin of the above. -/
private lemma collectSingleQuotedLoop_line_or_floor (sc : ScannerState)
    (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd : Nat) (l₀ : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd = .ok (result_content, s'))
    (hinv : sc.line = l₀ ∨ currentIndent < (sc.col : Int)) :
    s'.line = l₀ ∨ currentIndent < (s'.col : Int) := by
  induction fuel generalizing sc content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- a quote: escaped pair, or the close
      rename_i _ hpeek
      have hstep : sc.advance.line = l₀ ∨ currentIndent < (sc.advance.col : Int) := by
        rcases hinv with h | h
        · exact Or.inl ((advance_preserves_line_of_ne_break sc '\'' hpeek
            (by decide) (by decide)).trans h)
        · exact Or.inr (by rw [advance_col_succ_of_peek hpeek (by decide)]; push_cast; omega)
      dsimp only [] at hok
      split at hok
      · -- escaped quote '': one more column
        rename_i hpeek2
        refine ih _ _ hok ?_
        rcases hstep with h | h
        · exact Or.inl ((advance_preserves_line_of_ne_break sc.advance '\'' hpeek2
            (by decide) (by decide)).trans h)
        · exact Or.inr (by rw [advance_col_succ_of_peek hpeek2 (by decide)]; push_cast; omega)
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        exact hstep
    · -- regular character
      rename_i _opt c hne_sq hpeek
      split at hok
      · -- line break: the fold's gate
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · rename_i hcol_ok
              exact ih _ _ hok (Or.inr (by omega))
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have hnb : isLineBreakBool c = false := by simpa using hne_lb
          refine ih _ _ hok ?_
          rcases hinv with h | h
          · exact Or.inl ((advance_preserves_line_of_ne_break sc c hpeek
              (by intro hc; rw [hc] at hnb; cases hnb)
              (by intro hc; rw [hc] at hnb; cases hnb)).trans h)
          · exact Or.inr (by rw [advance_col_succ_of_peek hpeek hnb]; push_cast; omega)

/-! ## §3  The per-scan exports: cross-line exit ⇒ strictly past the floor -/

/-- **A block-context plain scalar that ends off its entry line ends strictly
    past the block floor** — with no premise about its start column:
    `scanPlainScalar` gates continuation landings on
    `(max 0 (currentIndent + 1)).toNat` itself. -/
lemma scanPlainScalar_crossline_col_floor {s s' : ScannerState}
    (h_noflow : s.inFlow = false)
    (hok : scanPlainScalar s = .ok s')
    (h_ne : s'.line ≠ s.line) :
    s.currentIndent < (s'.col : Int) := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind, h_noflow, Bool.false_eq_true, ↓reduceIte] at hok
  split at hok
  · cases hok
  · rename_i r h_loop
    have h_eq := Except.ok.inj hok
    have h_line : s'.line = r.state.line := by rw [← h_eq]; rfl
    have h_col : s'.col = r.state.col := by rw [← h_eq]; rfl
    rcases collectPlainScalarLoop_line_or_floor _ s "" ""
        ((max 0 (s.currentIndent + 1)).toNat) s.inputEnd s.line r
        h_loop (Or.inl rfl) with h | h
    · exact absurd (h_line.trans h) h_ne
    · rw [h_col]; omega

/-- **A double-quoted scalar that ends off its entry line ends strictly past
    the block floor** (`[69] s-flow-line-prefix(n)`, both contexts). -/
lemma scanDoubleQuoted_crossline_col_floor {s s' : ScannerState}
    (h_pk : s.peek? = some '"')
    (hok : scanDoubleQuoted s = .ok s')
    (h_ne : s'.line ≠ s.line) :
    s.currentIndent < (s'.col : Int) := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    -- the trailing-content probe and the emit both leave the cursor alone
    have h_fields : s'.line = res.2.line ∧ s'.col = res.2.col := by
      split at hok
      · split at hok
        · cases hok
        · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
      · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
    rcases collectDoubleQuotedLoop_line_or_floor s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd 0 s.line h_loop
        (Or.inl (advance_preserves_line_of_ne_break s '"' h_pk
          (by decide) (by decide))) with h | h
    · exact absurd (h_fields.1.trans h) h_ne
    · rw [h_fields.2]; omega

/-- `scanSingleQuoted`'s twin. -/
lemma scanSingleQuoted_crossline_col_floor {s s' : ScannerState}
    (h_pk : s.peek? = some '\'')
    (hok : scanSingleQuoted s = .ok s')
    (h_ne : s'.line ≠ s.line) :
    s.currentIndent < (s'.col : Int) := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    have h_fields : s'.line = res.2.line ∧ s'.col = res.2.col := by
      split at hok
      · split at hok
        · cases hok
        · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
      · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
    rcases collectSingleQuotedLoop_line_or_floor s.advance "" _ s.currentPos
        s.inFlow s.currentIndent s.inputEnd s.line h_loop
        (Or.inl (advance_preserves_line_of_ne_break s '\'' h_pk
          (by decide) (by decide))) with h | h
    · exact absurd (h_fields.1.trans h) h_ne
    · rw [h_fields.2]; omega

/-! ## §2b  The walks' same-line exits, as column monotonicity (item 123)

The stale-cursor invariant's walk cases also need the OTHER exit: a walk that
ends ON its entry line only moved the column right.  The break arms cannot
produce such an exit — the folds land strictly below
(`handleBlockLineBreak_line_lt` / `foldQuotedNewlines_line_lt`) and the loops
never return to an earlier line (`collectPlainScalarLoop_line_le` /
`collect*QuotedLoop_line_ge`) — so each induction closes them by
contradiction and only the same-line steps carry weight. -/

/-- **A BLOCK plain walk that exits on its entry line only moved right.** -/
lemma collectPlainScalarLoop_col_ge_of_line_eq (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat)
      (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    r.state.line = s.line → s.col ≤ r.state.col := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie r hok _
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    exact Nat.le_refl _
  | succ fuel' ih =>
    intro s content spaces ci ie r hok h_line
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq
      exact Nat.le_refl _
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        rw [terminates?_state hterm']
        exact Nat.le_refl _
      · split at hok
        · -- a break, block context: a same-line exit is impossible past the fold
          rename_i hlb
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact Nat.le_refl _
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact Nat.le_refl _
              · dsimp only [] at hok
                generalize h_loop :
                  collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact Nat.le_refl _
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exfalso
                    have h1 := handleBlockLineBreak_line_lt hpk hlb hblk
                    have h2 := collectPlainScalarLoop_line_le s2 content' ""
                      fuel' false ci ie h_loop
                    omega
                | error e => simp at hok
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          have h_adv_line : s.advance.line = s.line :=
            advance_preserves_line_of_ne_break s c hpk
              (by intro hc; rw [hc] at hnb; cases hnb)
              (by intro hc; rw [hc] at hnb; cases hnb)
          have h_adv_col : s.advance.col = s.col + 1 :=
            advance_col_succ_of_peek hpk hnb
          split at hok
          · have := ih s.advance content _ ci ie r hok
              (by rw [h_line, h_adv_line])
            omega
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact Nat.le_refl _
            · have := ih s.advance _ "" ci ie r hok
                (by rw [h_line, h_adv_line])
              omega

/-- **A double-quoted walk that exits on its entry line only moved right.** -/
lemma collectDoubleQuotedLoop_col_ge_of_line_eq (sc : ScannerState)
    (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd protectedLen : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd protectedLen = .ok (result_content, s'))
    (h_line : s'.line = sc.line) : sc.col ≤ s'.col := by
  induction fuel generalizing sc content protectedLen with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote
      rename_i _ hpeek
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      rw [advance_col_succ_of_peek hpeek (by decide)]
      omega
    · -- backslash
      rename_i _ hpeek
      have h_adv_line : sc.advance.line = sc.line :=
        advance_preserves_line_of_ne_break sc '\\' hpeek (by decide) (by decide)
      have h_adv_col : sc.advance.col = sc.col + 1 :=
        advance_col_succ_of_peek hpeek (by decide)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break: the fold lands strictly below and the loop never returns
          rename_i hlb2
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i fold_res hfold
            split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · exfalso
                have h1 := foldQuotedNewlines_line_lt hpeek2 hlb2 hfold
                have h2 := collectDoubleQuotedLoop_line_ge _ _ fuel' startPos inFlow
                  currentIndent inputEnd _ hok
                omega
        · -- regular escape: same line, column only grows
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            have h_esc_line := processEscape_line hproc
            have h_esc_col := processEscape_col_ge hproc
            have := ih _ _ _ hok (by rw [h_line, ← h_adv_line, ← h_esc_line])
            omega
      · exact absurd hok (by simp)
    · -- regular character
      rename_i _opt c hne_dq hne_bs hpeek
      split at hok
      · -- line break: same reasoning as the escaped one
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_res hfold
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · exfalso
              have h1 := foldQuotedNewlines_line_lt hpeek hlb hfold
              have h2 := collectDoubleQuotedLoop_line_ge _ _ fuel' startPos inFlow
                currentIndent inputEnd _ hok
              omega
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have hnb : isLineBreakBool c = false := by simpa using hne_lb
          have h_a_line := advance_preserves_line_of_ne_break sc c hpeek
            (by intro hc; rw [hc] at hnb; cases hnb)
            (by intro hc; rw [hc] at hnb; cases hnb)
          have h_a_col := advance_col_succ_of_peek hpeek hnb
          have := ih _ _ _ hok (by rw [h_line, ← h_a_line])
          omega

/-- `collectSingleQuotedLoop`'s twin of the above. -/
lemma collectSingleQuotedLoop_col_ge_of_line_eq (sc : ScannerState)
    (content : String) (fuel : Nat) (startPos : YamlPos) (inFlow : Bool)
    (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hok : collectSingleQuotedLoop sc content fuel startPos inFlow currentIndent
             inputEnd = .ok (result_content, s'))
    (h_line : s'.line = sc.line) : sc.col ≤ s'.col := by
  induction fuel generalizing sc content with
  | zero => simp [collectSingleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- a quote: escaped pair, or the close
      rename_i _ hpeek
      have h_adv_line : sc.advance.line = sc.line :=
        advance_preserves_line_of_ne_break sc '\'' hpeek (by decide) (by decide)
      have h_adv_col : sc.advance.col = sc.col + 1 :=
        advance_col_succ_of_peek hpeek (by decide)
      dsimp only [] at hok
      split at hok
      · -- escaped quote '': two more columns
        rename_i hpeek2
        have h_adv2_line : sc.advance.advance.line = sc.advance.line :=
          advance_preserves_line_of_ne_break sc.advance '\'' hpeek2
            (by decide) (by decide)
        have h_adv2_col : sc.advance.advance.col = sc.advance.col + 1 :=
          advance_col_succ_of_peek hpeek2 (by decide)
        have := ih _ _ hok (by rw [h_line, ← h_adv_line, ← h_adv2_line])
        omega
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok
        obtain ⟨-, rfl⟩ := hok
        omega
    · -- regular character
      rename_i _opt c hne_sq hpeek
      split at hok
      · -- line break: the fold lands strictly below and the loop never returns
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_res hfold
          split at hok
          · simp at hok
          · split at hok
            · simp at hok
            · exfalso
              have h1 := foldQuotedNewlines_line_lt hpeek hlb hfold
              have h2 := collectSingleQuotedLoop_line_ge _ _ fuel' startPos inFlow
                currentIndent inputEnd hok
              omega
      · split at hok
        · simp at hok
        · rename_i hne_lb _
          have hnb : isLineBreakBool c = false := by simpa using hne_lb
          have h_a_line := advance_preserves_line_of_ne_break sc c hpeek
            (by intro hc; rw [hc] at hnb; cases hnb)
            (by intro hc; rw [hc] at hnb; cases hnb)
          have h_a_col := advance_col_succ_of_peek hpeek hnb
          have := ih _ _ hok (by rw [h_line, ← h_a_line])
          omega

/-! ## §3b  The per-scan same-line exports -/

/-- **A block-context plain scalar that ends on its entry line only moved the
    column right.** -/
lemma scanPlainScalar_sameline_col_ge {s s' : ScannerState}
    (h_noflow : s.inFlow = false)
    (hok : scanPlainScalar s = .ok s')
    (h_line : s'.line = s.line) : s.col ≤ s'.col := by
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind, h_noflow, Bool.false_eq_true, ↓reduceIte] at hok
  split at hok
  · cases hok
  · rename_i r h_loop
    have h_eq := Except.ok.inj hok
    have h_line' : s'.line = r.state.line := by rw [← h_eq]; rfl
    have h_col : s'.col = r.state.col := by rw [← h_eq]; rfl
    rw [h_col]
    exact collectPlainScalarLoop_col_ge_of_line_eq _ s "" ""
      ((max 0 (s.currentIndent + 1)).toNat) s.inputEnd r h_loop
      (by rw [← h_line', h_line])

/-- **A double-quoted scalar that ends on its entry line only moved the
    column right.** -/
lemma scanDoubleQuoted_sameline_col_ge {s s' : ScannerState}
    (h_pk : s.peek? = some '"')
    (hok : scanDoubleQuoted s = .ok s')
    (h_line : s'.line = s.line) : s.col ≤ s'.col := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    have h_fields : s'.line = res.2.line ∧ s'.col = res.2.col := by
      split at hok
      · split at hok
        · cases hok
        · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
      · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
    have h_adv_line : s.advance.line = s.line :=
      advance_preserves_line_of_ne_break s '"' h_pk (by decide) (by decide)
    have h_adv_col : s.advance.col = s.col + 1 :=
      advance_col_succ_of_peek h_pk (by decide)
    have h_ge := collectDoubleQuotedLoop_col_ge_of_line_eq s.advance "" _
      s.currentPos s.inFlow s.currentIndent s.inputEnd 0 h_loop
      (by rw [← h_fields.1, h_line, ← h_adv_line])
    omega

/-- `scanSingleQuoted`'s twin. -/
lemma scanSingleQuoted_sameline_col_ge {s s' : ScannerState}
    (h_pk : s.peek? = some '\'')
    (hok : scanSingleQuoted s = .ok s')
    (h_line : s'.line = s.line) : s.col ≤ s'.col := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · cases hok
  · rename_i res h_loop
    have h_fields : s'.line = res.2.line ∧ s'.col = res.2.col := by
      split at hok
      · split at hok
        · cases hok
        · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
      · exact ⟨by rw [← Except.ok.inj hok]; rfl, by rw [← Except.ok.inj hok]; rfl⟩
    have h_adv_line : s.advance.line = s.line :=
      advance_preserves_line_of_ne_break s '\'' h_pk (by decide) (by decide)
    have h_adv_col : s.advance.col = s.col + 1 :=
      advance_col_succ_of_peek h_pk (by decide)
    have h_ge := collectSingleQuotedLoop_col_ge_of_line_eq s.advance "" _
      s.currentPos s.inFlow s.currentIndent s.inputEnd h_loop
      (by rw [← h_fields.1, h_line, ← h_adv_line])
    omega

/-! ## Item 400 — the input-ahead exports

What the cursor stands on after a block-context token that may have saved a simple key.
The live-key-top invariant's `-` case (items 398/399) spends these: a block `-` is never
the follower of a same-line plain, quoted or alias token, and after a node property on the
line `scanBlockEntry` itself refuses. -/

/-- The stop set of a block-context plain walk: EOF, `:`, `#`, a break, a non-printable or the
    BOM (the `isPlainSafeBool` refusals), or the column-0 document boundary. -/
def PlainFollower (st : ScannerState) : Prop :=
  st.peek? = none ∨
  (∃ c, st.peek? = some c ∧
    (c = ':' ∨ c = '#' ∨ isLineBreakBool c = true ∨ isPrintableBool c = false ∨ c = '\uFEFF')) ∨
  (st.col = 0 ∧ atDocumentBoundary st = true)

/-- `validateTrailingContent`'s admitted set, read past the trailing spaces. -/
def TrailingFollower (s : ScannerState) (ie : Nat) : Prop :=
  (skipTrailingSpaces s (ie - s.offset + 1)).peek? = none ∨
  ∃ c, (skipTrailingSpaces s (ie - s.offset + 1)).peek? = some c ∧
    (isLineBreakBool c = true ∨ c = '#' ∨ c = ':')

/-- In block context the terminator test fires only at `#`, `:` or the column-0 boundary. -/
lemma terminates?_block_cases {c : Char} {s : ScannerState} {content spaces : String}
    {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces false = some r) :
    c = '#' ∨ c = ':' ∨ (s.col = 0 ∧ atDocumentBoundary s = true) := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    exact Or.inl hc.1
  · split at h
    · rename_i _ hc
      exact Or.inr (Or.inl (by simpa using hc))
    · split at h
      · rename_i hfl
        simp at hfl
      · split at h
        · rename_i hb
          simp only [Bool.and_eq_true, beq_iff_eq] at hb
          exact Or.inr (Or.inr hb)
        · cases h

/-- A block-context character the plain walk refuses, which is neither space nor break, is
    non-printable or the BOM. -/
lemma isPlainSafeBool_block_false {c : Char} (h : isPlainSafeBool c false = false)
    (hws : isWhiteSpaceBool c = false) (hnb : isLineBreakBool c = false) :
    isPrintableBool c = false ∨ c = '\uFEFF' := by
  simp only [isPlainSafeBool, Bool.false_eq_true, ite_false, hws, hnb, Bool.not_false,
    Bool.true_and, Bool.and_eq_false_iff, bne_eq_false_iff_eq] at h
  exact h

/-- **Export (a).**  A block-context plain walk that stops (`terminated = true`) stands on
    `PlainFollower` — in particular never on a block `-`. -/
lemma collectPlainScalarLoop_terminated_follower (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat) (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    r.terminated = true → PlainFollower r.state := by
  induction fuel with
  | zero =>
    intro s content spaces ci ie r hok hterm
    unfold collectPlainScalarLoop at hok
    injection hok with h_eq; subst h_eq
    simp at hterm
  | succ fuel' ih =>
    intro s content spaces ci ie r hok hterm
    unfold collectPlainScalarLoop at hok
    split at hok
    · rename_i hpk
      injection hok with h_eq; subst h_eq
      exact Or.inl hpk
    · rename_i c hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        rw [terminates?_state hterm']
        rcases terminates?_block_cases hterm' with hc | hc | hc
        · exact Or.inr (Or.inl ⟨c, hpk, Or.inr (Or.inl hc)⟩)
        · exact Or.inr (Or.inl ⟨c, hpk, Or.inl hc⟩)
        · exact Or.inr (Or.inr hc)
      · split at hok
        · rename_i hbr
          have hbrk : PlainFollower s :=
            Or.inr (Or.inl ⟨c, hpk, Or.inr (Or.inr (Or.inl hbr))⟩)
          split at hok
          · rename_i hflow
            simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq
              exact hbrk
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq
                exact hbrk
              · dsimp only [] at hok
                generalize h_loop :
                  collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq
                    exact hbrk
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    exact ih s2 content' "" ci ie _ h_loop hterm
                | error e => simp at hok
        · rename_i hbr
          have hnb : isLineBreakBool c = false := by simpa using hbr
          split at hok
          · exact ih s.advance content _ ci ie r hok hterm
          · rename_i hws
            have hws' : isWhiteSpaceBool c = false := by simpa using hws
            split at hok
            · rename_i hsafe
              injection hok with h_eq; subst h_eq
              have h1 : isPlainSafeBool c false = false := by simpa using hsafe
              rcases isPlainSafeBool_block_false h1 hws' hnb with h | h
              · exact Or.inr (Or.inl ⟨c, hpk, Or.inr (Or.inr (Or.inr (Or.inl h)))⟩)
              · exact Or.inr (Or.inl ⟨c, hpk, Or.inr (Or.inr (Or.inr (Or.inr h)))⟩)
            · exact ih s.advance _ "" ci ie r hok hterm

/-- **Exports (b)/(d), the core.**  A passing `validateTrailingContent` leaves the probe on
    EOF, a break, `#` or `:`. -/
lemma validateTrailingContent_follower {s : ScannerState} {ie : Nat}
    (h : validateTrailingContent s ie = .ok ()) : TrailingFollower s ie := by
  unfold validateTrailingContent at h
  dsimp only at h
  unfold TrailingFollower
  split at h
  · rename_i hc
    exact Or.inl hc
  · rename_i c hc
    split at h
    · rename_i hok
      refine Or.inr ⟨c, hc, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq] at hok
      rcases hok with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · cases h

/-- **Export (d).**  In block context the alias close is the trailing-content probe. -/
lemma validateAliasClose_follower {s : ScannerState} (h : validateAliasClose s = .ok ())
    (hflow : s.inFlow = false) : TrailingFollower s s.inputEnd := by
  unfold validateAliasClose at h
  rw [hflow] at h
  exact validateTrailingContent_follower (by simpa using h)

/-- **Export (c).**  A block `-` is never dispatched after a node property on its line:
    `scanBlockEntry` refuses by `lastTokenIsNodePropertyOnLine`. -/
lemma scanBlockEntry_not_property {s s' : ScannerState} (h : scanBlockEntry s = .ok s')
    (hflow : s.inFlow = false) :
    lastTokenIsNodePropertyOnLine s.tokens s.line = false := by
  cases hcase : lastTokenIsNodePropertyOnLine s.tokens s.line with
  | false => rfl
  | true =>
    exfalso
    unfold scanBlockEntry at h
    simp [hflow, hcase, bind, Except.bind] at h
    split at h <;> simp [throw, throwThe, MonadExceptOf.throw] at h

/-- `advance` moves the cursor by the input alone. -/
lemma advance_io_congr {s t : ScannerState} (hi : s.input = t.input) (ho : s.offset = t.offset)
    (he : s.inputEnd = t.inputEnd) :
    s.advance.input = t.advance.input ∧ s.advance.offset = t.advance.offset ∧
      s.advance.inputEnd = t.advance.inputEnd := by
  unfold ScannerState.advance
  simp only [hi, ho, he]
  split <;> (try split) <;> (try split) <;> simp [hi, ho, he]

/-- `peek?` reads only the input, offset and end. -/
lemma peek_congr {s t : ScannerState} (hi : s.input = t.input) (ho : s.offset = t.offset)
    (he : s.inputEnd = t.inputEnd) : s.peek? = t.peek? := by
  unfold ScannerState.peek?
  rw [hi, ho, he]

/-- `skipTrailingSpaces` reads only the input, offset and end — the token array and the
    flags a scalar's close updates do not move its probe. -/
lemma skipTrailingSpaces_peek_congr (fuel : Nat) :
    ∀ (s t : ScannerState), s.input = t.input → s.offset = t.offset → s.inputEnd = t.inputEnd →
    (skipTrailingSpaces s fuel).peek? = (skipTrailingSpaces t fuel).peek? := by
  induction fuel with
  | zero =>
    intro s t hi ho he
    simp only [skipTrailingSpaces]
    exact peek_congr hi ho he
  | succ fuel' ih =>
    intro s t hi ho he
    have hpk : s.peek? = t.peek? := peek_congr hi ho he
    unfold skipTrailingSpaces
    rw [hpk]
    split
    · split
      · obtain ⟨hi', ho', he'⟩ := advance_io_congr hi ho he
        exact ih _ _ hi' ho' he'
      · exact hpk
    · exact hpk

/-- The probe's verdict transports to any state with the same input, offset and end. -/
lemma TrailingFollower.congr {s t : ScannerState} {ie : Nat} (h : TrailingFollower s ie)
    (hi : s.input = t.input) (ho : s.offset = t.offset) (he : s.inputEnd = t.inputEnd) :
    TrailingFollower t ie := by
  unfold TrailingFollower at h ⊢
  rw [← ho, ← skipTrailingSpaces_peek_congr (ie - s.offset + 1) s t hi ho he]
  exact h

/-- **Export (b), double quotes.**  In block context the state a double-quoted scalar returns
    stands (past trailing spaces) on EOF, a break, `#` or `:`. -/
lemma scanDoubleQuoted_follower {s s' : ScannerState} (h : scanDoubleQuoted s = .ok s')
    (hflow : s.inFlow = false) : TrailingFollower s' s.inputEnd := by
  unfold scanDoubleQuoted at h
  simp only [hflow, Bool.not_false, ite_true, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i pr hloop
    obtain ⟨content, sac⟩ := pr
    dsimp only at h
    split at h
    · cases h
    · rename_i u hval
      have hs' := Except.ok.inj h; subst hs'
      have hv : validateTrailingContent sac s.inputEnd = .ok () := by cases u; exact hval
      exact (validateTrailingContent_follower hv).congr rfl rfl rfl

/-- **Export (b), single quotes.** -/
lemma scanSingleQuoted_follower {s s' : ScannerState} (h : scanSingleQuoted s = .ok s')
    (hflow : s.inFlow = false) : TrailingFollower s' s.inputEnd := by
  unfold scanSingleQuoted at h
  simp only [hflow, Bool.not_false, ite_true, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i pr hloop
    obtain ⟨content, sac⟩ := pr
    dsimp only at h
    split at h
    · cases h
    · rename_i u hval
      have hs' := Except.ok.inj h; subst hs'
      have hv : validateTrailingContent sac s.inputEnd = .ok () := by cases u; exact hval
      exact (validateTrailingContent_follower hv).congr rfl rfl rfl

/-! ### Item 401 — the fuel half of export (a)

`scanPlainScalar` hands the loop `2·(inputEnd − offset + 1)` units of fuel; every step that
does not stop consumes a byte of a cursor that was strictly before the end, so a result with
`terminated = false` would need `fuel ≤ inputEnd − offset`.  No `offset ≤ inputEnd` invariant
is needed: the bound is read off the LAST consuming step's source state. -/

/-- Every terminator result stops the walk. -/
lemma terminates?_terminated {c : Char} {s : ScannerState} {content spaces : String}
    {inFlow : Bool} {r : PlainScalarResult}
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some r) :
    r.terminated = true := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; subst h; rfl
  · split at h
    · simp only [] at h
      split at h <;> split at h <;> first
        | (injection h with h; subst h; rfl)
        | cases h
    · split at h
      · injection h with h; subst h; rfl
      · split at h
        · injection h with h; subst h; rfl
        · cases h

lemma peek_some_lt {s : ScannerState} {c : Char} (hpk : s.peek? = some c) :
    s.offset < s.inputEnd := by
  unfold ScannerState.peek? at hpk
  by_cases h : s.offset < s.inputEnd
  · exact h
  · rw [ite_eq_right h] at hpk; cases hpk

lemma advance_inputEnd (s : ScannerState) : s.advance.inputEnd = s.inputEnd := by
  unfold ScannerState.advance
  split <;> dsimp only <;> (try split) <;> (try split) <;> simp

lemma advance_offset_gt_of_peek {s : ScannerState} {c : Char} (hpk : s.peek? = some c) :
    s.offset < s.advance.offset :=
  L4YAML.Proofs.ScannerCorrectness.advance_increases_offset s (by
    unfold ScannerState.hasMore; simpa using peek_some_lt hpk)

lemma consumeNewline_inputEnd (s : ScannerState) :
    (consumeNewline s).inputEnd = s.inputEnd := by
  unfold consumeNewline
  split <;> dsimp only <;> (try split) <;> simp [advance_inputEnd]

lemma consumeNewline_offset_gt {s : ScannerState} {c : Char}
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true) :
    s.offset < (consumeNewline s).offset := by
  have hadv := advance_offset_gt_of_peek hpk
  unfold consumeNewline
  rw [hpk]
  split
  · exact hadv
  · dsimp only
    split
    · rename_i hpk2
      have h2 : s.advance.offset <
          (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx :=
        String.Pos.Raw.lt_next s.advance.input ⟨s.advance.offset⟩
      simp only
      omega
    · exact hadv
  · rename_i hn hr
    exfalso
    have : c = '\n' ∨ c = '\r' := by
      simp [isLineBreakBool, isLineFeedBool, isCarriageReturnBool] at hbr
      rcases hbr with h | h <;> simp [h]
    rcases this with h | h
    · exact hn (by rw [h])
    · exact hr (by rw [h])

lemma skipWhitespaceLoop_inputEnd (fuel : Nat) : ∀ s : ScannerState,
    (skipWhitespaceLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; simp [skipWhitespaceLoop]
  | succ fuel' ih =>
    intro s
    unfold skipWhitespaceLoop
    split
    · split
      · rw [ih, advance_inputEnd]
      · rfl
    · rfl

lemma skipWhitespace_inputEnd (s : ScannerState) : (skipWhitespace s).inputEnd = s.inputEnd := by
  unfold skipWhitespace; exact skipWhitespaceLoop_inputEnd _ s

lemma skipSpacesLoop_inputEnd (fuel : Nat) : ∀ s : ScannerState,
    (skipSpacesLoop s fuel).inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s; simp [skipSpacesLoop]
  | succ fuel' ih =>
    intro s
    unfold skipSpacesLoop
    split
    · rw [ih, advance_inputEnd]
    · rfl

lemma skipSpaces_inputEnd (s : ScannerState) : (skipSpaces s).inputEnd = s.inputEnd := by
  unfold skipSpaces; exact skipSpacesLoop_inputEnd _ s

lemma skipBlankLinesLoop_inputEnd (fuel : Nat) : ∀ (s : ScannerState) (cnt ie : Nat),
    (skipBlankLinesLoop s cnt fuel ie).snd.inputEnd = s.inputEnd := by
  induction fuel with
  | zero => intro s cnt ie; rfl
  | succ fuel' ih =>
    intro s cnt ie
    unfold skipBlankLinesLoop
    dsimp only
    split
    · split
      · split
        · rfl
        · rw [ih, consumeNewline_inputEnd, skipWhitespace_inputEnd]
      · rfl
    · rfl

/-- A block line break the plain walk folds over consumes at least the break. -/
lemma handleBlockLineBreak_progress {s s2 : ScannerState} {content content' : String}
    {ci ie : Nat} {c : Char}
    (h : collectPlainScalar_handleBlockLineBreak s content ci ie = some (content', s2))
    (hpk : s.peek? = some c) (hbr : isLineBreakBool c = true) :
    s.offset < s2.offset ∧ s2.inputEnd = s.inputEnd := by
  unfold collectPlainScalar_handleBlockLineBreak at h
  dsimp only at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨-, rfl⟩ := h
      refine ⟨?_, ?_⟩
      · have h1 := consumeNewline_offset_gt hpk hbr
        have h2 := L4YAML.Proofs.ScannerCorrectness.skipBlankLinesLoop_offset_ge (consumeNewline s) 0
          (ie - (consumeNewline s).offset + 1) ie
        have h3 := L4YAML.Proofs.ScannerCorrectness.skipSpaces_offset_ge (skipBlankLinesLoop (consumeNewline s) 0
          (ie - (consumeNewline s).offset + 1) ie).snd
        have h4 := L4YAML.Proofs.ScannerCorrectness.skipWhitespace_offset_ge (skipSpaces (skipBlankLinesLoop (consumeNewline s) 0
          (ie - (consumeNewline s).offset + 1) ie).snd)
        omega
      · rw [skipWhitespace_inputEnd, skipSpaces_inputEnd, skipBlankLinesLoop_inputEnd,
          consumeNewline_inputEnd]

/-- **The fuel bound.**  A block-context walk that runs out of fuel had at most
    `inputEnd − offset` units to begin with. -/
lemma collectPlainScalarLoop_fuel_le_of_not_terminated (fuel : Nat) :
    ∀ (s : ScannerState) (content spaces : String) (ci ie : Nat) (r : PlainScalarResult),
    collectPlainScalarLoop s content spaces fuel false ci ie = .ok r →
    r.terminated = false → fuel ≤ s.inputEnd - s.offset := by
  induction fuel with
  | zero => intros; exact Nat.zero_le _
  | succ fuel' ih =>
    intro s content spaces ci ie r hok hterm
    unfold collectPlainScalarLoop at hok
    split at hok
    · injection hok with h_eq; subst h_eq; simp at hterm
    · rename_i c hpk
      have hlt := peek_some_lt hpk
      split at hok
      · rename_i hterm'
        injection hok with h_eq; subst h_eq
        rw [terminates?_terminated hterm'] at hterm; cases hterm
      · split at hok
        · rename_i hbr
          split at hok
          · rename_i hflow; simp at hflow
          · split at hok
            · injection hok with h_eq; subst h_eq; simp at hterm
            · rename_i content' s2 hblk
              split at hok
              · injection hok with h_eq; subst h_eq; simp at hterm
              · dsimp only [] at hok
                generalize h_loop :
                  collectPlainScalarLoop s2 content' "" fuel' false ci ie = cont at hok
                cases cont with
                | ok inner =>
                  dsimp only [] at hok
                  split at hok
                  · injection hok with h_eq; subst h_eq; simp at hterm
                  · have h_eq := Except.ok.inj hok; subst h_eq
                    have hb := ih s2 content' "" ci ie _ h_loop hterm
                    obtain ⟨hoff, hie⟩ := handleBlockLineBreak_progress hblk hpk hbr
                    omega
                | error e => simp at hok
        · rename_i hbr
          have hadv := advance_offset_gt_of_peek hpk
          have hie := advance_inputEnd s
          split at hok
          · have hb := ih s.advance content _ ci ie r hok hterm
            omega
          · split at hok
            · injection hok with h_eq; subst h_eq; simp at hterm
            · have hb := ih s.advance _ "" ci ie r hok hterm
              omega

/-- `PlainFollower` reads the cursor and the column alone: the token array and the key flags
    a scalar's close updates do not move it. -/
lemma PlainFollower.congr {s t : ScannerState} (h : PlainFollower s) (hi : s.input = t.input)
    (ho : s.offset = t.offset) (he : s.inputEnd = t.inputEnd) (hc : s.col = t.col) :
    PlainFollower t := by
  unfold PlainFollower at h ⊢
  have hpk := peek_congr hi ho he
  have hdoc : atDocumentBoundary s = atDocumentBoundary t := by
    simp [atDocumentBoundary, atDocumentStart, atDocumentEnd, ScannerState.peekAt?, hi, ho, he, hc]
  rw [← hpk, ← hdoc, ← hc]
  exact h

/-- **Export (a), closed.**  A block-context plain scalar leaves the cursor on `PlainFollower`
    — the `terminated` hypothesis of `collectPlainScalarLoop_terminated_follower` discharged by
    the fuel bound. -/
lemma scanPlainScalar_follower {s s' : ScannerState} (h : scanPlainScalar s = .ok s')
    (hflow : s.inFlow = false) : PlainFollower s' := by
  unfold scanPlainScalar at h
  simp only [hflow, bind, Except.bind] at h
  split at h
  · cases h
  · rename_i r hloop
    have hs' := Except.ok.inj h; subst hs'
    cases hterm : r.terminated with
    | true =>
      exact (collectPlainScalarLoop_terminated_follower _ s "" "" _ _ r hloop hterm).congr
        rfl rfl rfl rfl
    | false =>
      exfalso
      have hb := collectPlainScalarLoop_fuel_le_of_not_terminated _ s "" "" _ _ r hloop hterm
      omega

/-! ### Item 401 — `LiveKeyTop`, the live-key-top invariant (item 391 §5) STATED

Sited here rather than beside `StaleKeyCursorFloor` because its follower conjunct is spent
from this file's exports (a)–(e); the step proof is item 402's. -/

/-- **Export (e).**  A flow close back at block level is the trailing-content probe. -/
lemma validateFlowClose_follower {s : ScannerState} (h : validateFlowClose s = .ok ())
    (hlvl : s.flowLevel = 0) : TrailingFollower s s.inputEnd := by
  unfold validateFlowClose at h
  simp only [hlvl, beq_self_eq_true, ite_true] at h
  unfold TrailingFollower
  split at h
  · rename_i hc; exact Or.inl hc
  · rename_i c hc
    split at h
    · rename_i hok
      refine Or.inr ⟨c, hc, ?_⟩
      simp only [Bool.or_eq_true, beq_iff_eq] at hok
      rcases hok with (h | h) | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr h)
    · simp at h

/-- What the cursor may stand on while a simple key saved on this line is live: a node
    property is the last token of the line; or the key is a block entry's own position (the
    `-` records itself, cleared or re-saved by the next token); or (past whitespace) a follower
    no block `-` is. -/
def KeyFollower (s : ScannerState) : Prop :=
  lastTokenIsNodePropertyOnLine s.tokens s.line = true ∨
  (∃ t, s.tokens.back? = some t ∧ t.val = .blockEntry ∧ t.pos = s.simpleKey.pos ∧
    s.simpleKeyAllowed = true) ∨
  (skipWhitespace s).peek? = none ∨
  ∃ c, (skipWhitespace s).peek? = some c ∧
    (c = ':' ∨ c = '#' ∨ isLineBreakBool c = true ∨ isPrintableBool c = false ∨ c = '\uFEFF')

/-- Item 391 §5: a live simple key saved on the current line stands at or right of the
    indentation top (in BOTH contexts — item 402's step needs the flow half, since a key saved
    inside a flow collection is pushed by a nested opener and restored at the close), and so does
    every stacked one; in block context the live key's cursor stands on a `KeyFollower`. -/
def LiveKeyTop (s : ScannerState) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.pos.line = s.line →
    s.currentIndent ≤ (s.simpleKey.pos.col : Int) ∧ (s.inFlow = false → KeyFollower s)) ∧
  (∀ k ∈ s.simpleKeyStack, k.possible = true → k.pos.line = s.line →
    s.currentIndent ≤ (k.pos.col : Int))

lemma LiveKeyTop.initial (input : String) : LiveKeyTop (ScannerState.mk' input) := by
  refine ⟨fun h _ => ?_, fun k hk => ?_⟩
  · exact absurd h (by unfold ScannerState.mk'; simp)
  · exact absurd hk (by unfold ScannerState.mk'; simp)

/-- `skipWhitespace` is the identity on a non-blank cursor. -/
lemma skipWhitespace_eq_of_not_ws {s : ScannerState} {c : Char} (hpk : s.peek? = some c)
    (hws : isWhiteSpaceBool c = false) : skipWhitespace s = s := by
  unfold skipWhitespace skipWhitespaceLoop
  split
  · rfl
  · rw [hpk]; simp [hws]

/-- **The `-` arm of the step, read from the conjunct (restated in item 402):** a block `-`
    dispatched while a key saved on its line is live means that key is the FRESH save at the
    cursor — an inherited key is refuted on every `KeyFollower` arm (the property arm by export
    (c), the block-entry arm because `simpleKeyAllowed` forces a fresh save, the follower arms
    because the cursor peeks `-`). -/
lemma LiveKeyTop.dash_case {s : ScannerState} (hinv : LiveKeyTop s) (hflow : s.inFlow = false)
    (hposs : s.simpleKey.possible = true) (hline : s.simpleKey.pos.line = s.line)
    (hpk : s.peek? = some '-') (hnp : lastTokenIsNodePropertyOnLine s.tokens s.line = false)
    (hfresh : s.simpleKeyAllowed = true → s.simpleKey.pos = s.currentPos) :
    s.simpleKey.pos = s.currentPos := by
  obtain ⟨-, hf⟩ := hinv.1 hposs hline
  have hid := skipWhitespace_eq_of_not_ws hpk (by decide)
  rcases hf hflow with hp | ⟨t, -, -, -, hal⟩ | hn | ⟨c, hc, hset⟩
  · rw [hnp] at hp; cases hp
  · exact hfresh hal
  · rw [hid, hpk] at hn; cases hn
  · rw [hid, hpk] at hc
    have : c = '-' := (Option.some.inj hc).symm
    subst this
    exfalso
    rcases hset with h | h | h | h | h <;> first | cases h | (revert h; decide)

end L4YAML.Proofs.ScalarWalkColFloor

end Blanket
