/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Production.FlowIndexLift
public import L4YAML.Proofs.Scanner.PreprocessIndentStable
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Coupling.LandingTab

@[expose] public section Blanket

/-! # Quoted-scalar readings at the pending's own index (DOCS item 53)

    `ScalarProduction` builds every quoted reading at index 0; the
    `FlowIndexLift` lifts (item 45) carry the single-line readings to any
    index and return the multi-line ones as `*Crossed` witnesses.  This file
    pays the multi-line readings themselves: the scanner's fold guards — the
    §6.1 tab gate, the document-marker check and the §8.1 under-indent check,
    which item 53's runtime edit extended to the escaped-break landing, and
    item 62's, which extended the §6.1 gate to the run's BLANK lines —
    guarantee every CONTENT landing clears `s-indent(n)` whenever
    `n ≤ currentIndent + 1`, so the same loop inductions that build the
    0-readings build the readings at `n`.

    The blank-line loop is total at `n` (`foldQuotedNewlinesLoop_prod_at`
    carries no disjunction), the fold's §6.1-gate-true branch returns the
    landing's under-floor COLUMN, which each caller's own §8.1 check refutes,
    and the escaped break's landing is the fold itself (item 87) — so the
    quoted loops and the flow-context plain walk read at `n` with NO
    disjunction (item 88).  The one residue is the plain walk's BLOCK arm,
    whose blank-line skipper carries no §6.1 gate; it is located as
    `inFlow = false`, which the flow faces refute off their own premise. -/

set_option autoImplicit false

namespace L4YAML.Proofs.ScalarFoldAt

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScannerCoupling
open L4YAML.Proofs.ScalarCoupling
open L4YAML.Proofs.ScalarProduction
open L4YAML.Proofs.FlowIndexLift
open L4YAML.Proofs.PreprocessIndentStable
open L4YAML.Proofs.LandingTab

/-! ## §0 Local plumbing -/

/-- Neither does the blank-line loop. -/
private lemma foldLoop_indents (s : ScannerState) (cnt fuel : Nat) :
    (foldQuotedNewlinesLoop s cnt fuel).1.indents = s.indents := by
  induction fuel generalizing s cnt with
  | zero => rfl
  | succ f ih =>
    unfold foldQuotedNewlinesLoop; dsimp only []
    split
    · split
      · split
        · rfl
        · rw [ih, consumeNewline_indents, skipWhitespace_preserves_indents]
      · rfl
    · rfl

/-- Nor does the plain walk's blank-line skipper. -/
private lemma skipBlankLines_indents (s : ScannerState) (cnt fuel inputEnd : Nat) :
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
        · rw [ih, consumeNewline_indents, skipWhitespace_preserves_indents]
      · rfl
    · rfl

/-- Nor does the block line-break handler: it consumes a break and skips
    blanks and whites, none of which touch the indent stack. -/
private lemma handleBlockLineBreak_indents {s s' : ScannerState} {content content' : String}
    {contentIndent inputEnd : Nat}
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
          skipBlankLines_indents, consumeNewline_indents]

/-- `skipWhitespace` is the identity where the cursor is not on an `s-white`. -/
private lemma skipWhitespace_id_of_not_white (s : ScannerState)
    (h : ∀ ch, s.peek? = some ch → isWhiteSpaceBool ch = false) :
    skipWhitespace s = s := by
  cases hpk : s.peek? with
  | none =>
    have hge : ¬ (s.offset < s.inputEnd) := by
      intro hlt
      unfold ScannerState.peek? at hpk
      rw [ite_eq_left hlt] at hpk
      exact absurd hpk (by simp)
    unfold skipWhitespace
    rw [show s.inputEnd - s.offset = 0 from by omega]
    simp [skipWhitespaceLoop]
  | some ch =>
    exact L4YAML.Proofs.EmitterScannability.skipWhitespace_of_not_ws s ch hpk (h ch hpk)
      (peek_some_hasMore s ch hpk)

/-! ## §1 `l-empty(n)` from a skipped blank line -/

/-- Every `[30] b-break` lands at column 0. -/
lemma SBBreak_col0 {sp sp' : SurfPos} (h : SBBreak sp sp') : sp'.col = 0 := by
  cases h <;> rfl

/-- **The one shape `[70] l-empty(n,c)` has no arm for**: a run of `j < n`
    spaces and then a TAB.  `[63] s-indent` is spaces (§6.1),
    `[69] s-flow-line-prefix(n)` admits a tab only past the `n`th space, and
    `[64] s-indent-lt(n)` takes its break immediately after its short run — so
    this is a scanner over-acceptance, not a missing derivation.  It is stated
    LOCATED (the index, and the tab's own position) precisely so that item 62's
    runtime gate can read it. -/
def BlankRunTabUnderFloor (n : Nat) (sp : SurfPos) : Prop :=
  ∃ j sx, j < n ∧ SIndent j sp sx ∧ sx.chars.head? = some '\t'

/-- A skipped blank line reads at `n`: its run splits as
    `s-flow-line-prefix(n)` when it clears the indent, as `s-indent(<n)`
    when it is a short pure-space run, and otherwise it is the located tab. -/
lemma slEmpty_flowIn_at (n : Nat) {sp sp₁ sp' : SurfPos}
    (hws : GStar SSWhite sp sp₁) (hbrk : SBBreak sp₁ sp') :
    SLEmpty n .flowIn sp sp' ∨ BlankRunTabUnderFloor n sp := by
  rcases gstar_white_take_sIndent n hws with ⟨sx, hind, hrest⟩ | ⟨j, sx, hj, hind, hrest, hend⟩
  · exact Or.inl (SLEmpty.flow n sp sp₁ sp' .flowIn (Or.inr rfl)
      (GOpt.some sp sp₁ (SFlowLinePrefix.mk n sp sx sp₁ hind
        (gstar_sswhite_to_gopt_sep hrest))) hbrk)
  · rcases hend with hend | htab
    · subst hend
      -- the whole run is `j < n` spaces: `s-indent(<n)`… once the residual
      -- star is nil.  It is: `sx = sp₁` says the run ended at the split.
      cases hrest with
      | nil => exact Or.inl (SLEmpty.flowLt n sp sx sp' .flowIn (Or.inr rfl)
          ⟨j, hj, hind⟩ hbrk)
      | cons _ _ _ hw hr =>
        -- a residual white AT the run's end would step past sp₁ — but the
        -- break starts there, and a break head is not a white.  Refute from
        -- the characters.
        cases hw with
        | space rest col => cases hbrk <;> simp_all
        | tab rest col => cases hbrk <;> simp_all
    · exact Or.inr ⟨j, sx, hj, hind, htab⟩

/-- **Item 62's gate refutes it.**  `blankLineTabUnderFloor` measures the blank
    line's own space run and the character that ends it; the located residue
    says that character is a tab at column `j < n ≤ currentIndent + 1`, which
    is exactly the gate's firing condition.  So a line the loop actually folds
    never carries the residue. -/
lemma not_blankRunTab_of_gate {n : Nat} {sc : ScannerState} {sp : SurfPos}
    (hcorr : ScannerSurfCorr sc sp) (hcol0 : sp.col = 0)
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1))
    (hgate : blankLineTabUnderFloor sc = false) :
    ¬ BlankRunTabUnderFloor n sp := by
  rintro ⟨j, sx, hj, hind, htab⟩
  obtain ⟨hpk, hcol⟩ := skipSpaces_lands_at_tab hcorr hind htab
  have hci : (skipSpaces sc).currentIndent = sc.currentIndent :=
    currentIndent_of_indents_eq (skipSpaces_preserves_indents sc)
  have hfire : blankLineTabUnderFloor sc = true := by
    unfold blankLineTabUnderFloor
    simp only [hpk, hci, hcol, hcol0, Nat.zero_add, beq_self_eq_true, Bool.true_and,
      decide_eq_true_eq]
    omega
  rw [hfire] at hgate
  exact Bool.noConfusion hgate

/-! ## §2 The blank-line loop at `n` -/

/-- `foldQuotedNewlinesLoop` at `n`: **every** line the loop skips is
    `SLEmpty n`.  Item 62's gate stops the run at the one shape `[70]` has no
    arm for, so nothing is left over.  The column fact rides along: a loop
    entered at a line start leaves at one. -/
lemma foldQuotedNewlinesLoop_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (cnt fuel : Nat) (hcorr : ScannerSurfCorr sc sp)
    (hcol0 : sp.col = 0)
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp', GStar (SLEmpty n .flowIn) sp sp' ∧
       ScannerSurfCorr (foldQuotedNewlinesLoop sc cnt fuel).1 sp' ∧
       sp'.col = 0 := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp only [foldQuotedNewlinesLoop]
    exact ⟨sp, GStar.nil _, hcorr, hcol0⟩
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop; dsimp only []
    obtain ⟨sp_ws, h_gstar, hcorr_ws⟩ := skipWhitespace_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipWhitespace sc) sp_ws c hcorr_ws hpeek hlb
        split
        · exact ⟨sp, GStar.nil _, hcorr, hcol0⟩
        · rename_i hgate
          have hgate' : blankLineTabUnderFloor sc = false := by simpa using hgate
          rcases slEmpty_flowIn_at n h_gstar h_sbreak with h_lempty | h_tab
          · have hci : (consumeNewline (skipWhitespace sc)).currentIndent
                = sc.currentIndent := by
              refine currentIndent_of_indents_eq ?_
              rw [consumeNewline_indents, skipWhitespace_preserves_indents]
            obtain ⟨sp_rest, h_gr, hc, hcol⟩ :=
              ih (consumeNewline (skipWhitespace sc)) sp_cn (cnt + 1) hcorr_cn
                (SBBreak_col0 h_sbreak) (by rw [hci]; exact hn)
            exact ⟨sp_rest, GStar.cons sp sp_cn sp_rest h_lempty h_gr, hc, hcol⟩
          · exact absurd h_tab (not_blankRunTab_of_gate hcorr hcol0 hn hgate')
      · exact ⟨sp, GStar.nil _, hcorr, hcol0⟩
    · exact ⟨sp, GStar.nil _, hcorr, hcol0⟩

/-! ## §3 The fold at `n` -/

/-- **The fold reads at `n`** whenever `n ≤ currentIndent + 1`: the guards make
    the landing's space run at least `n` long, so `s-flow-line-prefix(n)`
    splits off the run item 45 style.  The one branch that produces no reading
    is the §6.1-gate-true one, and it costs no domain: it hands back exactly
    the fact the CALLER's §8.1 check refuses — the landing sits at or below the
    floor. -/
lemma foldQuotedNewlines_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (c : Char)
    {content : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hfold : foldQuotedNewlines sc = .ok (content, s'))
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    (∃ sp₁ sp₂ sp'',
      SBBreak sp sp₁ ∧
      GStar (SLEmpty n .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix n sp₂ sp'' ∧
      ScannerSurfCorr s' sp'') ∨ ((s'.col : Int) ≤ sc.currentIndent) := by
  obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
    consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
  have h_ci_cn : (consumeNewline sc).currentIndent = sc.currentIndent :=
    currentIndent_of_indents_eq (consumeNewline_indents sc)
  obtain ⟨sp_loop, h_gstar_empty, hcorr_loop, hcol_loop⟩ :=
    foldQuotedNewlinesLoop_prod_at n (consumeNewline sc) sp_cn 0 _ hcorr_cn
      (SBBreak_col0 h_sbreak) (by rw [h_ci_cn]; exact hn)
  · obtain ⟨n_sk2, sp_sk2, h_indent2, hcorr_sk2⟩ :=
      skipSpaces_corr (loopResult sc).1 sp_loop hcorr_loop
    have h_ci_sk0 : (skipSpaces (loopResult sc).1).currentIndent
        = sc.currentIndent := by
      refine currentIndent_of_indents_eq ?_
      rw [skipSpaces_preserves_indents]
      show (loopResult sc).1.indents = sc.indents
      rw [show (loopResult sc).1.indents = (consumeNewline sc).indents from
            foldLoop_indents (consumeNewline sc) 0 _,
          consumeNewline_indents]
    unfold foldQuotedNewlines at hfold; dsimp only [] at hfold
    split at hfold
    · -- the gate-true branch: the landing is at or below the floor.  The tab
      -- half throws; the other half returns that very column, and the
      -- caller's §8.1 check refuses it.
      rename_i h_gate
      have h_gate' : ((skipSpaces (loopResult sc).1).col : Int)
          ≤ (skipSpaces (loopResult sc).1).currentIndent := by simpa using h_gate
      split at hfold
      · cases hfold
      · rename_i h_no_tab
        -- past the spaces the landing is neither space nor tab, so the
        -- trailing `s-white*` skip is the identity and the column stands.
        have h_id : skipWhitespace (skipSpaces (loopResult sc).1)
            = skipSpaces (loopResult sc).1 := by
          refine skipWhitespace_id_of_not_white _ (fun ch hch => ?_)
          have h_ns : ch ≠ ' ' := by
            intro hEq
            exact skipSpaces_peek_ne_space (loopResult sc).1 (by rw [hch, hEq])
          have h_nt : ch ≠ '\t' := by
            intro hEq
            exact h_no_tab (by rw [hch, hEq])
          simp [isWhiteSpaceBool, isSpaceBool, isTabBool, h_ns, h_nt]
        refine Or.inr ?_
        split at hfold <;>
          · have hinj := Except.ok.inj hfold
            obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
            rw [h_id, ← h_ci_sk0]
            exact h_gate'
    · -- gate-false: the landing's space run clears the indent, so it is at
      -- least `n` long and the prefix splits off it.
      rename_i h_gate
      obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
        skipWhitespace_corr _ sp_sk2 hcorr_sk2
      -- the run length: the loop lands at column 0, the spaces land at
      -- `n_sk2`, and the gate says that clears the indent.
      have hcol0 : sp_loop.col = 0 := hcol_loop
      have hcol_sk2 : sp_sk2.col = n_sk2 := by
        have := SIndent_col' h_indent2; omega
      have h_gate' : ¬ ((skipSpaces (loopResult sc).1).col : Int)
          ≤ (skipSpaces (loopResult sc).1).currentIndent := by
        simpa using h_gate
      have h_ci_sk : (skipSpaces (loopResult sc).1).currentIndent
          = sc.currentIndent := by
        refine currentIndent_of_indents_eq ?_
        rw [skipSpaces_preserves_indents]
        show (loopResult sc).1.indents = sc.indents
        rw [show (loopResult sc).1.indents = (consumeNewline sc).indents from
              foldLoop_indents (consumeNewline sc) 0 _,
            consumeNewline_indents]
      have h_col_state : ((skipSpaces (loopResult sc).1).col : Int) = (n_sk2 : Int) := by
        rw [hcorr_sk2.col_eq] at hcol_sk2
        exact_mod_cast hcol_sk2
      have hn_le : n ≤ n_sk2 := by
        rw [h_ci_sk] at h_gate'
        omega
      -- split the space run at `n`: indent + residual spaces, the residual
      -- and the trailing whites feeding the separation slot.
      have h_eq : n_sk2 = n + (n_sk2 - n) := by omega
      rw [h_eq] at h_indent2
      obtain ⟨sp_mid, h_ind_n, h_ind_rest⟩ := sindent_split h_indent2
      have h_seps : GStar SSWhite sp_mid sp_ws :=
        gstar_sswhite_append (sindent_to_gstar_sswhite h_ind_rest) h_gstar_ws
      have h_flp : SFlowLinePrefix n sp_loop sp_ws :=
        SFlowLinePrefix.mk n sp_loop sp_mid sp_ws h_ind_n
          (gstar_sswhite_to_gopt_sep h_seps)
      split at hfold
      · have hinj := Except.ok.inj hfold
        obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
        exact Or.inl ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩
      · have hinj := Except.ok.inj hfold
        obtain ⟨_, rfl⟩ := Prod.mk.inj hinj
        exact Or.inl ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty, h_flp, hcorr_ws⟩

/-! ## §4 The double-quoted body at `n` -/

/-- The prepend at `n` (the 0-version's proof, index-generic). -/
private lemma SNbDoubleMultiLine_prepend_at (n : Nat) (s s₁ s_end : SurfPos)
    (hchar : SNbDoubleChar s s₁)
    (hrest : SNbDoubleMultiLine n s₁ s_end) :
    SNbDoubleMultiLine n s s_end := by
  cases hrest with
  | single _ _ hline =>
    exact SNbDoubleMultiLine.single n s s_end (GStar.cons s s₁ s_end hchar hline)
  | multi _ s₁' s₂ s₃ _ hline hbreak hcont =>
    exact SNbDoubleMultiLine.multi n s s₁' s₂ s₃ s_end
      (GStar.cons s s₁ s₁' hchar hline) hbreak hcont

/-- **The double-quoted body reads at `n`** whenever `n ≤ currentIndent + 1`:
    the loop's own guards clear every landing — the fold's since item 50's
    neighbourhood, the escaped break's since item 87 made its landing the
    fold itself — so the reading carries no disjunction (item 88). -/
lemma collectDoubleQuotedLoop_prod_at (n : Nat) (sc0 : ScannerState) (sp0 : SurfPos)
    (content0 : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr0 : ScannerSurfCorr sc0 sp0)
    (hok0 : collectDoubleQuotedLoop sc0 content0 fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s'))
    (hci0 : sc0.currentIndent = currentIndent)
    (hn : (n : Int) ≤ max 0 (currentIndent + 1)) :
    ∃ sp_body sp_close,
      SNbDoubleMultiLine n sp0 sp_body ∧
      GLit '"' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close := by
  suffices H : ∀ (p : Nat) (sc : ScannerState) (sp : SurfPos) (content : String),
      ScannerSurfCorr sc sp →
      collectDoubleQuotedLoop sc content fuel startPos inFlow currentIndent inputEnd p
        = .ok (result_content, s') →
      sc.currentIndent = currentIndent →
      (∃ sp_body sp_close,
        SNbDoubleMultiLine n sp sp_body ∧
        GLit '"' sp_body sp_close ∧
        ScannerSurfCorr s' sp_close) by
    exact H 0 sc0 sp0 content0 hcorr0 hok0 hci0
  clear hok0 hcorr0 hci0
  intro p sc sp content hcorr hok hci
  induction fuel generalizing sc sp content p with
  | zero => simp [collectDoubleQuotedLoop] at hok
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at hok
    split at hok
    · exact absurd hok (by simp)
    · -- closing quote: the one-line reading is index-free.
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      simp only [Except.ok.injEq, Prod.mk.injEq] at hok
      obtain ⟨-, rfl⟩ := hok
      exact ⟨⟨'"' :: rest, sc.col⟩, ⟨rest, sc.col + 1⟩,
             SNbDoubleMultiLine.single n _ _ (GStar.nil _),
             GLit.mk rest sc.col,
             advance_non_newline_corr sc '"' rest hcorr
               (peek_some_has_more hpeek) (by decide) (by decide)⟩
    · -- backslash: escape sequence
      rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hcorr_adv :=
        advance_non_newline_corr sc '\\' rest hcorr
          (peek_some_has_more hpeek) (by decide) (by decide)
      dsimp only [] at hok
      split at hok
      · rename_i c2 hpeek2
        split at hok
        · -- escaped break — item 87: the landing IS a fold, so §3's reader
          -- hands the break, the blank lines (`[112]`'s own `l-empty*` slot,
          -- item 62's gate included) and the prefix, exactly as at the fold
          -- arm; the §6.1-gate-true branch returns the under-floor column
          -- this loop's own §8.1 check refuses.  No landing is deferred.
          rename_i hlb2
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i fold_result hfold
            have hci_adv : sc.advance.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci
              exact advance_indents sc
            have hn_sc : (n : Int) ≤ max 0 (sc.advance.currentIndent + 1) := by
              rw [hci_adv]; exact hn
            rcases foldQuotedNewlines_prod_at n sc.advance ⟨rest, sc.col + 1⟩ c2
                hcorr_adv hpeek2 hlb2 hfold hn_sc with ⟨sp_cn, sp_loop, sp_fold,
                  h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ | h_under
            · have hci' : fold_result.2.currentIndent = currentIndent := by
                refine (currentIndent_of_indents_eq ?_).trans hci_adv
                exact L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                  sc.advance fold_result hfold
              split at hok
              · simp at hok
              · split at hok
                · simp at hok
                · split at hok <;>
                    first
                      | (obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
                           ih _ _ sp_fold _ hcorr_fold hok hci'
                         refine ⟨sp_body, sp_close, ?_, h_glit, h_corr⟩
                         exact SNbDoubleMultiLine.multi n
                           ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
                           sp_fold ⟨[], 0⟩ sp_body
                           (GStar.nil _)
                           (SSDoubleBreak.escaped n _ _
                             (SSDoubleEscaped.mk n
                               ⟨'\\' :: rest, sc.col⟩ ⟨'\\' :: rest, sc.col⟩
                               ⟨rest, sc.col + 1⟩ sp_cn sp_loop sp_fold
                               (GStar.nil _) (GLit.mk rest sc.col) h_sbreak
                               h_gstar_empty h_flp))
                           h_body)
                      | simp at hok
            · -- the §6.1-gate-true landing sits at or below the floor, and
              -- this loop's own §8.1 check is what refuses it.
              split at hok
              · simp at hok
              · split at hok
                · simp at hok
                · rename_i h_not_under
                  exact absurd (hci_adv ▸ h_under) h_not_under
        · -- ordinary escape: index-free prepend.
          simp only [bind, Except.bind] at hok
          split at hok
          · exact absurd hok (by simp)
          · rename_i esc_result hproc
            obtain ⟨sp_esc, h_dq_char, hcorr_esc⟩ :=
              processEscape_prod sc.advance rest sc.col hcorr_adv hproc
            have hci' : esc_result.2.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci
              rw [L4YAML.Proofs.EmitterScannability.processEscape_preserves_indents
                    sc.advance esc_result hproc,
                  advance_indents]
            obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
              ih _ _ sp_esc _ hcorr_esc hok hci'
            exact ⟨sp_body, sp_close,
              SNbDoubleMultiLine_prepend_at n _ _ _ h_dq_char h_body, h_glit, h_corr⟩
      · exact absurd hok (by simp)
    · -- regular character or fold
      rename_i _opt c hne_dq hne_bs hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok
      · -- fold: the reading at `n` (§3), then the loop's own guards.
        rename_i hlb
        simp only [bind, Except.bind] at hok
        split at hok
        · exact absurd hok (by simp)
        · rename_i fold_result hfold
          have hn_sc : (n : Int) ≤ max 0 (sc.currentIndent + 1) := by rw [hci]; exact hn
          rcases foldQuotedNewlines_prod_at n sc ⟨c :: rest, sc.col⟩ c hcorr hpeek hlb
              hfold hn_sc with ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp,
                hcorr_fold⟩ | h_under
          · have hci' : fold_result.2.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci
              exact L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                sc fold_result hfold
            split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · split at hok <;>
                  first
                    | (obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
                         ih _ _ sp_fold _ hcorr_fold hok hci'
                       exact ⟨sp_body, sp_close,
                         SNbDoubleMultiLine.multi n
                           ⟨c :: rest, sc.col⟩ ⟨c :: rest, sc.col⟩
                           sp_fold ⟨[], 0⟩ _
                           (GStar.nil _)
                           (SSDoubleBreak.flowFold n _ sp_cn sp_loop _
                             h_sbreak h_gstar_empty h_flp)
                           h_body,
                         h_glit, h_corr⟩)
                    | simp at hok
          · -- item 62: the §6.1-gate-true landing sits at or below the floor,
            -- and this loop's own §8.1 check is what refuses it.
            split at hok
            · simp at hok
            · split at hok
              · simp at hok
              · rename_i h_not_under
                exact absurd (hci ▸ h_under) h_not_under
      · -- regular character: index-free prepend.
        split at hok
        · simp at hok
        · rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc c rest hcorr hmore h_not_nl h_not_cr
          have hci' : sc.advance.currentIndent = currentIndent := by
            refine (currentIndent_of_indents_eq ?_).trans hci
            exact advance_indents sc
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih _ sc.advance ⟨rest, sc.col + 1⟩ _ hcorr_adv hok hci'
          exact ⟨sp_body, sp_close,
            SNbDoubleMultiLine_prepend_at n _ _ _
              (SNbDoubleChar.plain c rest sc.col
                (not_lineBreak_bool_to_prop hne_lb) hne_bs hne_dq) h_body,
            h_glit, h_corr⟩

/-! ## §5 The single-quoted body at `n` -/

private lemma SNbSingleMultiLine_prepend_at (n : Nat) (s s₁ s_end : SurfPos)
    (hchar : SNbSingleChar s s₁)
    (hrest : SNbSingleMultiLine n s₁ s_end) :
    SNbSingleMultiLine n s s_end := by
  cases hrest with
  | single _ _ hline =>
    exact SNbSingleMultiLine.single n s s_end (GStar.cons s s₁ s_end hchar hline)
  | multi _ s₁' s₂ s₃ s₄ _ hline hbreak hgstar hflp hcont =>
    exact SNbSingleMultiLine.multi n s s₁' s₂ s₃ s₄ s_end
      (GStar.cons s s₁ s₁' hchar hline) hbreak hgstar hflp hcont

/-- The single-quoted twin of `collectDoubleQuotedLoop_prod_at` — no escaped
    break, so the fold is the only landing. -/
lemma collectSingleQuotedLoop_prod_at (n : Nat) (sc0 : ScannerState) (sp0 : SurfPos)
    (content0 : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    {result_content : String} {s' : ScannerState}
    (hcorr0 : ScannerSurfCorr sc0 sp0)
    (hok0 : collectSingleQuotedLoop sc0 content0 fuel startPos inFlow currentIndent inputEnd
           = .ok (result_content, s'))
    (hci0 : sc0.currentIndent = currentIndent)
    (hn : (n : Int) ≤ max 0 (currentIndent + 1)) :
    ∃ sp_body sp_close,
      SNbSingleMultiLine n sp0 sp_body ∧
      GLit '\'' sp_body sp_close ∧
      ScannerSurfCorr s' sp_close := by
  induction fuel generalizing sc0 sp0 content0 with
  | zero => simp [collectSingleQuotedLoop] at hok0
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at hok0
    split at hok0
    · exact absurd hok0 (by simp)
    · rename_i _ hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr0 hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      dsimp only [] at hok0
      split at hok0
      · -- escaped quote ''
        rename_i hpeek2
        have hcorr_adv :=
          advance_non_newline_corr sc0 '\'' rest hcorr0 hmore (by decide) (by decide)
        obtain ⟨rest2, hsp_adv⟩ := peek_some_sp hcorr_adv hpeek2
        injection hsp_adv with h_rest2 h_col2
        subst h_rest2
        rw [h_col2] at hcorr_adv
        have hmore2 := peek_some_has_more hpeek2
        have hcorr_adv2 :=
          advance_non_newline_corr sc0.advance '\'' rest2 hcorr_adv hmore2 (by decide) (by decide)
        rw [show sc0.advance.col + 1 = sc0.col + 2 from by omega] at hcorr_adv2
        have hci' : sc0.advance.advance.currentIndent = currentIndent := by
          refine (currentIndent_of_indents_eq ?_).trans hci0
          rw [advance_indents, advance_indents]
        obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
          ih sc0.advance.advance ⟨rest2, sc0.col + 2⟩ _ hcorr_adv2 hok0 hci'
        exact ⟨sp_body, sp_close,
          SNbSingleMultiLine_prepend_at n _ _ _
            (SNbSingleChar.escapedQuote rest2 sc0.col) h_body, h_glit, h_corr⟩
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at hok0
        obtain ⟨-, rfl⟩ := hok0
        exact ⟨⟨'\'' :: rest, sc0.col⟩, ⟨rest, sc0.col + 1⟩,
               SNbSingleMultiLine.single n _ _ (GStar.nil _),
               GLit.mk rest sc0.col,
               advance_non_newline_corr sc0 '\'' rest hcorr0 hmore (by decide) (by decide)⟩
    · rename_i c hne_sq hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr0 hpeek
      subst hsp_eq
      have hmore := peek_some_has_more hpeek
      split at hok0
      · -- fold at `n`
        rename_i hlb
        simp only [bind, Except.bind] at hok0
        split at hok0
        · exact absurd hok0 (by simp)
        · rename_i fold_result hfold
          have hn_sc : (n : Int) ≤ max 0 (sc0.currentIndent + 1) := by rw [hci0]; exact hn
          rcases foldQuotedNewlines_prod_at n sc0 ⟨c :: rest, sc0.col⟩ c hcorr0 hpeek hlb
              hfold hn_sc with ⟨sp_cn, sp_loop, sp_fold, h_sbreak, h_gstar_empty, h_flp,
                hcorr_fold⟩ | h_under
          · have hci' : fold_result.2.currentIndent = currentIndent := by
              refine (currentIndent_of_indents_eq ?_).trans hci0
              exact L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                sc0 fold_result hfold
            split at hok0
            · simp at hok0
            · split at hok0
              · simp at hok0
              · obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
                  ih _ sp_fold _ hcorr_fold hok0 hci'
                exact ⟨sp_body, sp_close,
                  SNbSingleMultiLine.multi n
                    ⟨c :: rest, sc0.col⟩ ⟨c :: rest, sc0.col⟩
                    sp_cn sp_loop sp_fold _
                    (GStar.nil _)
                    h_sbreak h_gstar_empty h_flp
                    h_body,
                  h_glit, h_corr⟩
          · -- item 62: the single-quoted twin of the same refutation.
            split at hok0
            · simp at hok0
            · split at hok0
              · simp at hok0
              · rename_i h_not_under
                exact absurd (hci0 ▸ h_under) h_not_under
      · split at hok0
        · simp at hok0
        · rename_i hne_lb hne_ctrl
          have h_not_nl : c ≠ '\n' := not_isLineBreak_not_newline c hne_lb
          have h_not_cr : c ≠ '\r' := not_isLineBreak_not_cr c hne_lb
          have hcorr_adv :=
            advance_non_newline_corr sc0 c rest hcorr0 hmore h_not_nl h_not_cr
          have hci' : sc0.advance.currentIndent = currentIndent := by
            refine (currentIndent_of_indents_eq ?_).trans hci0
            exact advance_indents sc0
          obtain ⟨sp_body, sp_close, h_body, h_glit, h_corr⟩ :=
            ih sc0.advance ⟨rest, sc0.col + 1⟩ _ hcorr_adv hok0 hci'
          exact ⟨sp_body, sp_close,
            SNbSingleMultiLine_prepend_at n _ _ _
              (SNbSingleChar.plain c rest sc0.col
                (not_lineBreak_bool_to_prop hne_lb) hne_sq) h_body,
            h_glit, h_corr⟩

/-! ## §6 The scan-level wrappers -/

/-- **`scanDoubleQuoted` reads at `n`** whenever `n ≤ currentIndent + 1`, in
    the block-node contexts (`SNbDoubleText` at `.blockIn`/`.blockOut`/
    `.flowIn`/`.flowOut` is the multi-line body). -/
lemma scanDoubleQuoted_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_dq : sc.peek? = some '"')
    (hok : scanDoubleQuoted sc = .ok s')
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp', SCDoubleQuoted n .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanDoubleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_dq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_dq
  have hcorr_adv :=
    advance_non_newline_corr sc '"' rest hcorr hmore (by decide) (by decide)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have hci_adv : sc.advance.currentIndent = sc.currentIndent :=
      currentIndent_of_indents_eq (advance_indents sc)
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ :=
      collectDoubleQuotedLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv hloop hci_adv hn
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨_,
               SCDoubleQuoted.mk n .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_body h_glit_close,
               corr_of_simpleKeyAllowed_needIndentCheck_update false false
                 (corr_of_emitAt _ _ hcorr_close)⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨_,
             SCDoubleQuoted.mk n .blockIn _ _ _ _
               (GLit.mk rest sc.col) h_body h_glit_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false
               (corr_of_emitAt _ _ hcorr_close)⟩

/-- The single-quoted wrapper (see `scanDoubleQuoted_prod_at`). -/
lemma scanSingleQuoted_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek_sq : sc.peek? = some '\'')
    (hok : scanSingleQuoted sc = .ok s')
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp', SCSingleQuoted n .blockIn sp sp' ∧ ScannerSurfCorr s' sp' := by
  unfold scanSingleQuoted at hok
  simp only [bind, Except.bind] at hok
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek_sq
  subst hsp_eq
  have hmore := peek_some_has_more hpeek_sq
  have hcorr_adv :=
    advance_non_newline_corr sc '\'' rest hcorr hmore (by decide) (by decide)
  split at hok
  · simp at hok
  · rename_i pair hloop
    obtain ⟨content, s_after_close⟩ := pair
    simp only [] at hloop hok
    have hci_adv : sc.advance.currentIndent = sc.currentIndent :=
      currentIndent_of_indents_eq (advance_indents sc)
    obtain ⟨sp_body, sp_close, h_body, h_glit_close, hcorr_close⟩ :=
      collectSingleQuotedLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ "" _ _ _ _ _
        hcorr_adv hloop hci_adv hn
    split at hok
    · split at hok
      · simp at hok
      · have h := Except.ok.inj hok; subst h
        exact ⟨_,
               SCSingleQuoted.mk n .blockIn _ _ _ _
                 (GLit.mk rest sc.col) h_body h_glit_close,
               corr_of_simpleKeyAllowed_needIndentCheck_update false false
                 (corr_of_emitAt _ _ hcorr_close)⟩
    · have h := Except.ok.inj hok; subst h
      exact ⟨_,
             SCSingleQuoted.mk n .blockIn _ _ _ _
               (GLit.mk rest sc.col) h_body h_glit_close,
             corr_of_simpleKeyAllowed_needIndentCheck_update false false
               (corr_of_emitAt _ _ hcorr_close)⟩

/-! ## §7 Context conversion (the quoted body is context-free off the keys) -/

/-- `nb-double-text` is the same multi-line body at all four non-key
    contexts, so the reading converts freely among them. -/
lemma SCDoubleQuoted_multiCtx {n : Nat} {s s' : SurfPos} (c' : L4YAML.YamlContext)
    (hc' : c' = .flowOut ∨ c' = .flowIn ∨ c' = .blockOut ∨ c' = .blockIn)
    (h : SCDoubleQuoted n .blockIn s s') : SCDoubleQuoted n c' s s' := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases hc' with rfl | rfl | rfl | rfl <;>
      exact SCDoubleQuoted.mk n _ _ _ _ _ hq1 hbody hq2

/-- The single-quoted twin. -/
lemma SCSingleQuoted_multiCtx {n : Nat} {s s' : SurfPos} (c' : L4YAML.YamlContext)
    (hc' : c' = .flowOut ∨ c' = .flowIn ∨ c' = .blockOut ∨ c' = .blockIn)
    (h : SCSingleQuoted n .blockIn s s') : SCSingleQuoted n c' s s' := by
  cases h with
  | mk _ _ _ hq1 hbody hq2 =>
    rcases hc' with rfl | rfl | rfl | rfl <;>
      exact SCSingleQuoted.mk n _ _ _ _ _ hq1 hbody hq2

/-! ## §8 The plain scalar at `n` (block context) -/

/-- `skipBlankLinesLoop` at `n` — the plain walk's blank-line skipper.

    **Item 100**: **every** line it skips is `SLEmpty n`, exactly as in the
    quoted twin (`foldQuotedNewlinesLoop_prod_at`).  The loop's own §6.1 gate
    stops the run at the one shape `[70]` has no arm for — fewer than `n`
    spaces and then a TAB — so `slEmpty_flowIn_at`'s residue is refuted line by
    line and the disjunction is gone.  The column fact rides along: a loop
    entered at a line start leaves at one. -/
lemma skipBlankLinesLoop_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (cnt fuel inputEnd : Nat) (hcorr : ScannerSurfCorr sc sp)
    (hcol0 : sp.col = 0)
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp', GStar (SLEmpty n .flowIn) sp sp' ∧
       ScannerSurfCorr (skipBlankLinesLoop sc cnt fuel inputEnd).2 sp' ∧
       sp'.col = 0 := by
  induction fuel generalizing sc sp cnt with
  | zero =>
    simp only [skipBlankLinesLoop]
    exact ⟨sp, GStar.nil _, hcorr, hcol0⟩
  | succ fuel' ih =>
    unfold skipBlankLinesLoop; dsimp only []
    obtain ⟨sp_ws, h_gstar, hcorr_sk⟩ := skipWhitespace_corr sc sp hcorr
    split
    · rename_i c hpeek; split
      · rename_i hlb
        obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
          consumeNewline_sbreak_corr (skipWhitespace sc) sp_ws c hcorr_sk hpeek hlb
        split
        · exact ⟨sp, GStar.nil _, hcorr, hcol0⟩
        · rename_i hgate
          have hgate' : blankLineTabUnderFloor sc = false := by simpa using hgate
          rcases slEmpty_flowIn_at n h_gstar h_sbreak with h_lempty | h_tab
          · have hci : (consumeNewline (skipWhitespace sc)).currentIndent
                = sc.currentIndent := by
              refine currentIndent_of_indents_eq ?_
              rw [consumeNewline_indents, skipWhitespace_preserves_indents]
            obtain ⟨sp_rest, h_gr, hc, hcol⟩ :=
              ih (consumeNewline (skipWhitespace sc)) sp_cn (cnt + 1) hcorr_cn
                (SBBreak_col0 h_sbreak) (by rw [hci]; exact hn)
            exact ⟨sp_rest, GStar.cons sp sp_cn sp_rest h_lempty h_gr, hc, hcol⟩
          · exact absurd h_tab (not_blankRunTab_of_gate hcorr hcol0 hn hgate')
      · exact ⟨sp, GStar.nil _, hcorr, hcol0⟩
    · exact ⟨sp, GStar.nil _, hcorr, hcol0⟩

/-- The BLOCK line-break handler at `n`: a `some` return passed the
    under-indent guard, so the landing's space run clears `n ≤ contentIndent`
    and reads as `s-flow-line-prefix(n)`.

    **Item 100**: the reading is TOTAL.  What used to ride the disjunction was
    the blank run's own residue, and the loop's §6.1 gate has refuted it —
    `hnci` is the index fact that gate is measured against. -/
lemma handleBlockLineBreak_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos) (c : Char)
    (content : String) (contentIndent inputEnd : Nat)
    {content' : String} {s' : ScannerState}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hlb : isLineBreakBool c = true)
    (hblk : collectPlainScalar_handleBlockLineBreak sc content contentIndent inputEnd
            = some (content', s'))
    (hn : n ≤ contentIndent)
    (hnci : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp₁ sp₂ sp',
      SBBreak sp sp₁ ∧
      GStar (SLEmpty n .flowIn) sp₁ sp₂ ∧
      SFlowLinePrefix n sp₂ sp' ∧
      ScannerSurfCorr s' sp' := by
  obtain ⟨sp_cn, h_sbreak, hcorr_cn⟩ :=
    consumeNewline_sbreak_corr sc sp c hcorr hpeek hlb
  have hci_cn : (consumeNewline sc).currentIndent = sc.currentIndent :=
    currentIndent_of_indents_eq (consumeNewline_indents sc)
  obtain ⟨sp_loop, h_gstar_empty, hcorr_loop, hcol_loop⟩ :=
    skipBlankLinesLoop_prod_at n (consumeNewline sc) sp_cn 0 _ inputEnd hcorr_cn
      (SBBreak_col0 h_sbreak) (by rw [hci_cn]; exact hnci)
  · obtain ⟨n_sk, sp_sk, h_indent, hcorr_sk⟩ :=
      skipSpaces_corr
        (skipBlankLinesLoop (consumeNewline sc) 0
          (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2
        sp_loop hcorr_loop
    obtain ⟨sp_ws, h_gstar_ws, hcorr_ws⟩ :=
      skipWhitespace_corr
        (skipSpaces (skipBlankLinesLoop (consumeNewline sc) 0
          (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2)
        sp_sk hcorr_sk
    unfold collectPlainScalar_handleBlockLineBreak at hblk
    dsimp only [] at hblk
    split at hblk
    · exact absurd hblk (by simp)
    · rename_i h_guard
      split at hblk
      · exact absurd hblk (by simp)
      · simp only [Option.some.injEq, Prod.mk.injEq] at hblk
        obtain ⟨-, rfl⟩ := hblk
        -- the guard's negation: the landing's space run clears the floor.
        have hcol0 : sp_loop.col = 0 := hcol_loop
        have hcol_sk : sp_sk.col = n_sk := by
          have := SIndent_col' h_indent; omega
        have h_state_col : (skipSpaces (skipBlankLinesLoop (consumeNewline sc) 0
            (inputEnd - (consumeNewline sc).offset + 1) inputEnd).2).col = n_sk := by
          rw [← hcorr_sk.col_eq]; exact hcol_sk
        have hn_le : n ≤ n_sk := by
          rw [h_state_col] at h_guard
          omega
        have h_ind' : SIndent (n + (n_sk - n)) sp_loop sp_sk := by
          rw [show n + (n_sk - n) = n_sk from by omega]; exact h_indent
        obtain ⟨sp_mid, h_ind_n, h_ind_rest⟩ := sindent_split h_ind'
        exact ⟨sp_cn, sp_loop, sp_ws, h_sbreak, h_gstar_empty,
          SFlowLinePrefix.mk n sp_loop sp_mid sp_ws h_ind_n
            (gstar_sswhite_to_gopt_sep
              (gstar_sswhite_append (sindent_to_gstar_sswhite h_ind_rest) h_gstar_ws)),
          hcorr_ws⟩

/-- The plain collect loop at `n`, in BOTH contexts.  The two line-break arms
    ask the same question of different floors: the block arm's landing must
    clear `contentIndent` (the scalar's own), the flow arm's must clear the
    ENCLOSING block indent (item 50's §8.1 check).  `n` is under both — the
    caller supplies `n ≤ contentIndent` for one and `n ≤ currentIndent + 1` for
    the other — so the same `s-flow-line-prefix(n)` split serves each.

    The residue is the BLOCK arm's alone (its blank-line skipper carries no
    §6.1 gate), so it is returned as `inFlow = false`: the flow consumers
    refute it off their own premise (item 88). -/
lemma collectPlainScalarLoop_prod_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    (content spaces : String) (fuel : Nat)
    (contentIndent inputEnd : Nat)
    (sp_ent : SurfPos) (inFlow : Bool) (ci : Int)
    (hcorr : ScannerSurfCorr sc sp)
    (h_ws : GStar SSWhite sp_ent sp)
    (h_sp : spaces.length = 0 → sp_ent = sp)
    (h_hash_col : sc.peek? = some '#' → spaces.length = 0 → sc.col > 0)
    (h_sp_len : spaces.length > 0 → sp_ent ≠ sp)
    (hci : sc.currentIndent = ci)
    (h_ie : sc.inputEnd ≤ inputEnd)
    {result : PlainScalarResult}
    (hok : collectPlainScalarLoop sc content spaces fuel inFlow contentIndent inputEnd
           = .ok result)
    (hn : n ≤ contentIndent)
    (hnci : (n : Int) ≤ max 0 (ci + 1))
    -- Item 100: in BLOCK context the continuation floor is above the block
    -- indent, so a blank line the fold's §6.1 gate stopped at is under-indented
    -- — the handler ended the scalar there rather than folding it.
    (hcin : inFlow = false → (ci : Int) < (contentIndent : Int)) :
    (∃ sp_entries sp_next sp_trail,
      GStar (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp_ent sp_entries ∧
      GStar (SSNsPlainNextLine n (ctxOfInFlow inFlow)) sp_entries sp_next ∧
      GStar SSWhite sp_next sp_trail ∧
      ScannerSurfCorr result.state sp_trail ∧
      (result.terminated = true → sp_next = sp_trail → result.state.peek? ≠ some '#') ∧
      ((∀ ch, sc.peek? = some ch →
          isWhiteSpaceBool ch = false ∧ isLineBreakBool ch = false) →
        content.length < result.content.length →
        GPlus (SNbNsPlainInLineEntry (ctxOfInFlow inFlow)) sp_ent sp_entries)) := by
  induction fuel generalizing sc sp content spaces sp_ent with
  | zero =>
    simp [collectPlainScalarLoop] at hok; subst hok
    exact ⟨sp_ent, sp_ent, sp, GStar.nil _, GStar.nil _, h_ws, hcorr,
      fun ht => absurd ht Bool.false_ne_true,
      fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at hok
    split at hok
    · have h := Except.ok.inj hok; subst h
      exact ⟨sp_ent, sp_ent, sp, GStar.nil _, GStar.nil _, h_ws, hcorr,
      (fun _ _ hpk => by
        have hnone : sc.peek? = none := by assumption
        simp [hnone] at hpk),
      fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
    · rename_i c hpeek
      obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
      have hmore := peek_some_has_more hpeek
      subst hsp_eq
      split at hok
      · rename_i r_term h_term
        have h := Except.ok.inj hok; subst h
        rw [terminates_state_eq c sc content spaces inFlow r_term h_term]
        exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
          GStar.nil _, h_ws, hcorr,
          (fun _ heq hpk => by
            simp only [hpeek, Option.some.injEq] at hpk; subst hpk
            exact h_sp_len (terminates_hash_spaces_pos sc content spaces inFlow r_term
              h_term (h_hash_col hpeek)) heq),
          fun _ hlen => absurd hlen (by
            rw [terminates_content_eq c sc content spaces inFlow r_term h_term]
            exact Nat.lt_irrefl _)⟩
      · rename_i h_term_none
        split at hok
        · -- line break
          split at hok
          · -- inFlow = true: the fold's reading at `n` (§3); the landing that
            -- under-runs is refused by this loop's OWN §8.1 check (item 50's).
            simp only [bind, Except.bind] at hok
            split at hok
            · exact absurd hok (by simp)
            · rename_i fold_result hfold
              split at hok
              · -- a `#` on the landing ends the walk before the fold
                have h := Except.ok.inj hok; subst h
                exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                  GStar.nil _, h_ws, hcorr,
                  (fun _ _ hpk => by
                    simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                    first
                    | (have hlb' : isLineBreakBool '#' = true := by assumption
                       exact absurd hlb' (by decide))
                    | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                       cases inFlow <;> exact absurd hps (by decide))),
                  fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
              · rename_i hnothash
                have hci_fold : fold_result.2.currentIndent = ci := by
                  rw [← hci]
                  exact currentIndent_of_indents_eq
                    (L4YAML.Proofs.EmitterScannability.foldQuotedNewlines_preserves_indents
                      sc fold_result hfold)
                split at hok
                · exact absurd hok (by simp)
                · rename_i h_not_under
                  generalize h_loop : collectPlainScalarLoop fold_result.2
                      (content ++ fold_result.1) "" fuel' inFlow contentIndent inputEnd
                      = cont_result at hok
                  cases cont_result with
                  | error e => simp at hok
                  | ok inner_result =>
                    dsimp only [] at hok
                    split at hok
                    · have h := Except.ok.inj hok; subst h
                      exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                        GStar.nil _, h_ws, hcorr,
                        (fun _ _ hpk => by
                          simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                          first
                          | (have hlb' : isLineBreakBool '#' = true := by assumption
                             exact absurd hlb' (by decide))
                          | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                             cases inFlow <;> exact absurd hps (by decide))),
                        fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
                    · rename_i h_grew
                      have h_eq := Except.ok.inj hok; subst h_eq
                      have hlb : isLineBreakBool c = true := by assumption
                      rcases foldQuotedNewlines_prod_at n sc ⟨c :: rest, sc.col⟩ c
                          hcorr hpeek hlb hfold (by rw [hci]; exact hnci) with
                        ⟨sp₁, sp₂, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩
                        | h_under
                      · rcases ih fold_result.2 sp_fold (content ++ fold_result.1) ""
                            sp_fold hcorr_fold (GStar.nil _)
                            (fun _ => rfl)
                            (fun hpk _ => absurd hpk hnothash) (fun h => by simp at h) hci_fold
                            (by rw [foldQuotedNewlines_inputEnd hfold]; exact h_ie)
                            h_loop with
                          ⟨sp_entries_ih, sp_next_ih, sp_trail_ih,
                           h_entries_ih, h_next_ih, h_ws_ih, hcorr_ih, h_hash_ih, h_plus_ih⟩
                        · exact ⟨sp_ent, sp_next_ih, sp_trail_ih,
                            GStar.nil _,
                            GStar.cons sp_ent sp_entries_ih sp_next_ih
                              (ssNsPlainNextLine_of_gplus n (ctxOfInFlow inFlow)
                                sp_ent ⟨c :: rest, sc.col⟩ sp₁ sp₂ sp_fold sp_entries_ih
                                h_ws h_sbreak h_gstar_empty h_flp hcorr_fold
                                (h_plus_ih (foldQuotedNewlines_landing hfold)
                                  (Nat.lt_of_not_le h_grew))
                                (foldQuotedNewlines_landing hfold) hnothash)
                              h_next_ih,
                            h_ws_ih, hcorr_ih, h_hash_ih,
                            fun hpre _ => by simp [(hpre c hpeek).2] at hlb⟩
                      · -- item 50's §8.1 check: the fold's under-floor landing is
                        -- exactly what this branch's own guard refuses.
                        exfalso
                        refine h_not_under ?_
                        have h1 : (fold_result.2.col : Int) ≤ fold_result.2.currentIndent := by
                          rw [hci_fold, ← hci]; exact h_under
                        have h2 : fold_result.2.currentIndent ≥ 0 := by
                          have : (0 : Int) ≤ (fold_result.2.col : Int) := Int.natCast_nonneg _
                          omega
                        simp [h1, h2]
          · -- inFlow = false: block line break at `n` — the arm's own split
            -- condition is the residue every punt below returns.
            rename_i h_notflow
            have h_nf : inFlow = false := by
              revert h_notflow; cases inFlow <;> simp
            split at hok
            · have h := Except.ok.inj hok; subst h
              exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                GStar.nil _, h_ws, hcorr,
                (fun _ _ hpk => by
                  simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                  first
                  | (have hlb' : isLineBreakBool '#' = true := by assumption
                     exact absurd hlb' (by decide))
                  | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                     cases inFlow <;> exact absurd hps (by decide))),
                fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
            · rename_i content' s' hblk
              split at hok
              · have h := Except.ok.inj hok; subst h
                exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                  GStar.nil _, h_ws, hcorr,
                  (fun _ _ hpk => by
                    simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                    first
                    | (have hlb' : isLineBreakBool '#' = true := by assumption
                       exact absurd hlb' (by decide))
                    | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                       cases inFlow <;> exact absurd hps (by decide))),
                  fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
              · rename_i hblkpeek
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow
                  contentIndent inputEnd = cont_result at hok
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at hok
                  split at hok
                  · have h := Except.ok.inj hok; subst h
                    exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                      GStar.nil _, h_ws, hcorr,
                      (fun _ _ hpk => by
                        simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                        first
                        | (have hlb' : isLineBreakBool '#' = true := by assumption
                           exact absurd hlb' (by decide))
                        | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                           cases inFlow <;> exact absurd hps (by decide))),
                      fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
                  · rename_i h_grew
                    have h_eq := Except.ok.inj hok; subst h_eq
                    have hlb : isLineBreakBool c = true := by assumption
                    obtain ⟨sp₁, sp₂, sp_fold, h_sbreak, h_gstar_empty, h_flp, hcorr_fold⟩ :=
                      handleBlockLineBreak_prod_at n sc ⟨c :: rest, sc.col⟩ c content
                        contentIndent inputEnd hcorr hpeek hlb hblk hn
                        (by rw [hci]; exact hnci)
                    · rcases ih s' sp_fold content' "" sp_fold hcorr_fold (GStar.nil _)
                          (fun _ => rfl)
                          (fun hpk _ => absurd hpk hblkpeek)
                          (fun h => by simp at h)
                          (by rw [← hci]
                              exact currentIndent_of_indents_eq
                                (handleBlockLineBreak_indents hblk))
                          (by rw [handleBlockLineBreak_inputEnd hblk]; exact h_ie)
                          h_loop with
                        ⟨sp_entries_ih, sp_next_ih, sp_trail_ih,
                         h_entries_ih, h_next_ih, h_ws_ih, hcorr_ih, h_hash_ih, h_plus_ih⟩
                      · exact ⟨sp_ent, sp_next_ih, sp_trail_ih,
                          GStar.nil _,
                          GStar.cons sp_ent sp_entries_ih sp_next_ih
                            (ssNsPlainNextLine_of_gplus n (ctxOfInFlow inFlow)
                              sp_ent ⟨c :: rest, sc.col⟩ sp₁ sp₂ sp_fold sp_entries_ih
                              h_ws h_sbreak h_gstar_empty h_flp hcorr_fold
                              (h_plus_ih
                                (handleBlockLineBreak_landing (by omega)
                                  (handleBlockLineBreak_gate_false
                                    (by rw [hci]; exact hcin h_nf) hblk) hblk)
                                (Nat.lt_of_not_le h_grew))
                              (handleBlockLineBreak_landing (by omega)
                                (handleBlockLineBreak_gate_false
                                  (by rw [hci]; exact hcin h_nf) hblk) hblk)
                              hblkpeek)
                            h_next_ih,
                          h_ws_ih, hcorr_ih, h_hash_ih,
                          fun hpre _ => by simp [(hpre c hpeek).2] at hlb⟩
                | error e => simp at hok
        · split at hok
          · -- whitespace
            have hws_char : isWhiteSpaceBool c = true := by assumption
            have hnl := isWhiteSpace_not_newline c hws_char
            have hcr := isWhiteSpace_not_cr c hws_char
            have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
            have hw : SSWhite ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ := by
              simp [isWhiteSpaceBool, isSpaceBool, isTabBool, Bool.or_eq_true,
                beq_iff_eq] at hws_char
              rcases hws_char with rfl | rfl
              · exact SSWhite.space rest sc.col
              · exact SSWhite.tab rest sc.col
            rcases ih sc.advance ⟨rest, sc.col + 1⟩ content (spaces.push c) sp_ent
                hcorr_adv (gstar_sswhite_append h_ws (GStar.cons _ _ _ hw (GStar.nil _)))
                (fun hlen => by simp [String.length_push] at hlen)
                (fun _ hlen => by simp [String.length_push] at hlen)
                (fun _ heq => by
                  have hle := gstar_sswhite_col_ge' sp_ent ⟨c :: rest, sc.col⟩ h_ws
                  rw [heq] at hle; dsimp only at hle; omega)
                (by rw [← hci]; exact currentIndent_of_indents_eq (advance_indents sc))
                (by rw [advance_inputEnd]; exact h_ie)
                hok with
              ⟨sp_entries_r, sp_next_r, sp_trail_r, h_ent_r, h_next_r, h_ws_r,
               hcorr_r, h_hash_r, -⟩
            · exact ⟨sp_entries_r, sp_next_r, sp_trail_r, h_ent_r, h_next_r,
                h_ws_r, hcorr_r, h_hash_r,
                fun hpre _ => by simp [(hpre c hpeek).1] at hws_char⟩
          · split at hok
            · have h := Except.ok.inj hok; subst h
              exact ⟨sp_ent, sp_ent, ⟨c :: rest, sc.col⟩, GStar.nil _,
                GStar.nil _, h_ws, hcorr,
                (fun _ _ hpk => by
                  simp only [hpeek, Option.some.injEq] at hpk; subst hpk
                  first
                  | (have hlb' : isLineBreakBool '#' = true := by assumption
                     exact absurd hlb' (by decide))
                  | (have hps : (!isPlainSafeBool '#' inFlow) = true := by assumption
                     cases inFlow <;> exact absurd hps (by decide))),
                fun _ hlen => absurd hlen (Nat.lt_irrefl _)⟩
            · -- content char: the 0-lemma's own construction, verbatim.
              have h_safe : isPlainSafeBool c inFlow = true := by
                cases hb : isPlainSafeBool c inFlow <;> simp_all
              have hnl := (isPlainSafe_not_newline h_safe).1
              have hcr := (isPlainSafe_not_newline h_safe).2
              have hcorr_adv := advance_non_newline_corr sc c rest hcorr hmore hnl hcr
              have h_entry : SNbNsPlainInLineEntry (ctxOfInFlow inFlow) sp_ent
                  ⟨rest, sc.col + 1⟩ := by
                by_cases hcolon : c = ':'
                · subst hcolon
                  obtain ⟨m, hpn, hnb, hfi, hprn, hbomn⟩ :=
                    colon_not_terminated_next sc content spaces inFlow h_term_none
                  unfold ScannerState.peekAt? at hpn
                  obtain ⟨pre, rest', hcs, hlen⟩ :=
                    peekAtLoop_some_chars hcorr.end_eq hpn (':' :: rest) hcorr.chars_from
                  have ⟨a, ha⟩ : ∃ a, pre = [a] := by
                    cases pre with
                    | nil => simp at hlen
                    | cons a as => cases as with
                      | nil => exact ⟨a, rfl⟩
                      | cons => simp at hlen
                  subst ha; simp at hcs
                  obtain ⟨ha', hrst⟩ := hcs; subst ha'; subst hrst
                  have h_ns_safe : isNsPlainSafe (ctxOfInFlow inFlow) m := by
                    cases inFlow with
                    | false => exact not_blank_to_nsChar hnb hprn hbomn
                    | true =>
                      exact ⟨not_blank_to_nsChar hnb hprn hbomn, fun hfp => by
                        have h1 := hfi rfl
                        have h2 := (isFlowIndicator_iff m).mpr hfp
                        simp [h1] at h2⟩
                  exact SNbNsPlainInLineEntry.mk _ sp_ent _ _ h_ws
                    (SNsPlainChar.colonSafe (ctxOfInFlow inFlow) '_' m rest' sc.col h_ns_safe)
                · by_cases hhash : c = '#'
                  · subst hhash
                    have h_sp_zero : spaces.length = 0 := by
                      suffices ¬(spaces.length > 0) by omega
                      intro h_pos
                      have h_dec : decide (spaces.length > 0) = true :=
                        decide_eq_true_eq.mpr h_pos
                      unfold collectPlainScalar_terminates? at h_term_none
                      simp [h_dec] at h_term_none
                    have h_ent := h_sp h_sp_zero
                    subst h_ent
                    exact SNbNsPlainInLineEntry.hash _ _ _ (GLit.mk rest sc.col)
                  · exact SNbNsPlainInLineEntry.mk _ sp_ent _ _ h_ws
                      (SNsPlainChar.safe (ctxOfInFlow inFlow) c rest sc.col
                        (isPlainSafe_to_nsPlainSafe h_safe) hcolon hhash)
              rcases ih sc.advance ⟨rest, sc.col + 1⟩ _ "" ⟨rest, sc.col + 1⟩
                  hcorr_adv (GStar.nil _)
                  (fun _ => rfl)
                  (fun _ _ => by
                    have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
                    omega)
                  (fun h => by simp at h)
                  (by rw [← hci]; exact currentIndent_of_indents_eq (advance_indents sc))
                  (by rw [advance_inputEnd]; exact h_ie)
                  hok with
                ⟨sp_entries, sp_next, sp_trail, h_ent_rest, h_next_rest,
                 h_ws_rest, hcorr_rest, h_hash_rest, -⟩
              · exact ⟨sp_entries, sp_next, sp_trail,
                  GStar.cons sp_ent ⟨rest, sc.col + 1⟩ sp_entries h_entry h_ent_rest,
                  h_next_rest, h_ws_rest, hcorr_rest, h_hash_rest,
                  fun _ _ =>
                    GPlus.mk sp_ent ⟨rest, sc.col + 1⟩ sp_entries h_entry h_ent_rest⟩

/-- **`scanPlainScalar` reads at `n`** in BLOCK context whenever
    `n ≤ minContentIndentOf` — the loop's own under-indent guard clears every
    continuation landing.

    **Item 100**: the reading is TOTAL.  The walk's one residue was the blank
    run's tab under the floor, and the loop's own §6.1 gate refutes it now.
    Stated at `[158] ns-flow-content` because that is what both faces wrap — a
    bare node is `SFlowNode.content`, a props run's is `SFlowNode.propsContent`
    (the flow twin below is stated the same way, and for the same reason). -/
lemma scanPlainScalar_to_flowContent_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s')
    (hinflow : sc.inFlow = false)
    (hn : n ≤ minContentIndentOf sc) :
    ∃ sp_gram sp', SFlowContent n .flowOut sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  have hrest_head : ∀ m, sc.peekAt? 1 = some m → ∃ rest', rest = m :: rest' := by
    intro m hm; unfold ScannerState.peekAt? at hm
    have hcorr' := hsp_eq ▸ hcorr
    obtain ⟨pre, rest', hcs, hlen⟩ :=
      peekAtLoop_some_chars hcorr'.end_eq hm (c :: rest) hcorr'.chars_from
    have ⟨a, ha⟩ : ∃ a, pre = [a] := by
      cases pre with
      | nil => simp at hlen
      | cons a as => cases as with
        | nil => exact ⟨a, rfl⟩
        | cons => simp at hlen
    subst ha; simp at hcs; obtain ⟨_, rfl⟩ := hcs; exact ⟨rest', rfl⟩
  rw [hsp_eq]; rw [hsp_eq] at hcorr
  have h_first : SNsPlainFirst (ctxOfInFlow sc.inFlow) ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) sc.inFlow hstart hrest_head
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i result hloop
    simp only [Except.ok.injEq] at hok; subst hok
    have h_term_none := canStartPlain_first_not_terminates c sc sc.inFlow hstart h_not_doc
    have h_safe := canStartPlain_implies_safe hstart
    have h_nws := canStartPlainScalar_not_ws hstart
    have h_nlb := canStartPlain_not_linebreak hstart
    have h_has_more := peek_some_has_more hpeek
    obtain ⟨fuel', h_fuel_eq⟩ : ∃ m, (sc.inputEnd - sc.offset + 1) * 2 = m + 1 :=
      ⟨(sc.inputEnd - sc.offset + 1) * 2 - 1, by omega⟩
    rw [h_fuel_eq] at hloop
    have hloop' := collectPlainScalarLoop_content_first_step
      hpeek h_term_none h_nlb h_nws h_safe hloop
    have hcorr_adv := advance_non_newline_corr sc c rest hcorr h_has_more
      (isPlainSafe_not_newline h_safe).1 (isPlainSafe_not_newline h_safe).2
    have hci_eq : (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat)
        = minContentIndentOf sc := by
      rw [hinflow]; rfl
    rw [hci_eq] at hloop'
    rcases collectPlainScalarLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ _ "" _ _ _
        ⟨rest, sc.col + 1⟩ sc.inFlow sc.currentIndent hcorr_adv (GStar.nil _)
        (fun _ => rfl)
        (fun _ _ => by
          have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
          omega)
        (fun h => by simp at h)
        (currentIndent_of_indents_eq (advance_indents sc))
        (by rw [advance_inputEnd]; exact Nat.le_refl _)
        hloop' hn
        (by unfold minContentIndentOf at hn; omega)
        (fun _ => by
          have hmin : minContentIndentOf sc = (max 0 (sc.currentIndent + 1)).toNat := by
            unfold minContentIndentOf; simp
          rw [hmin]; omega) with
      ⟨sp_entries, sp_next, sp_trail, h_entries, h_next_lines, h_trail, hcorr_result, h_hash, -⟩
    · exact ⟨sp_next, sp_trail,
        SFlowContent.plain n .flowOut _ _
          (SNsPlainMultiLine_ctxOfInFlow_to_flowOut
            (SNsPlainMultiLine.mk n (ctxOfInFlow sc.inFlow) _ _ sp_next
              (SNsPlainOneLine.mk (ctxOfInFlow sc.inFlow) _ ⟨rest, sc.col + 1⟩ sp_entries
                h_first h_entries)
              h_next_lines)),
        h_trail,
        fun heq hpk => h_hash
          (collectPlainScalarLoop_terminated_of_fuel _ sc "" "" sc.inFlow _ sc.inputEnd result hloop
            (by omega))
          heq hpk,
        corr_of_simpleKeyAllowed_needIndentCheck_update false false
          (corr_of_emitAt _ _ hcorr_result)⟩

/-- The NODE face: `[161] ns-flow-node` wraps the content the walk read. -/
lemma scanPlainScalar_to_flowNode_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s')
    (hinflow : sc.inFlow = false)
    (hn : n ≤ minContentIndentOf sc) :
    ∃ sp_gram sp', SFlowNode n .flowOut sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨sp_gram, sp'', h_content, h_tws, h_hash, hcorr'⟩ :=
    scanPlainScalar_to_flowContent_at n sc sp hcorr hpeek hstart h_not_doc hok hinflow hn
  exact ⟨sp_gram, sp'', SFlowNode.content n .flowOut _ _ h_content, h_tws, h_hash, hcorr'⟩

/-- **`scanPlainScalar` reads at `n` INSIDE a flow collection** — the flow
    share item 45 deferred and item 50 gave its check; the walk's block arm
    is refuted off `hinflow`, so the reading carries no disjunction
    (item 88).  Stated at `[158] ns-flow-content` because that is what both
    consumers wrap — a bare node is `SFlowNode.content`, a props run's is
    `SFlowNode.propsContent`.

    Two floors, one conclusion.  The walk measures its continuation lines
    against the enclosing BLOCK indent (`currentIndent`), not against its own
    start column, so `n ≤ currentIndent + 1` is what makes every landing clear
    `s-indent(n)`.  The scalar's own `contentIndent` is `sc.col`, which the
    interior's structural check has already put past `currentIndent`
    (`hcol`) — that is the whole use of the second hypothesis. -/
lemma scanPlainScalar_to_flowContent_flowIn_at (n : Nat) (sc : ScannerState) (sp : SurfPos)
    {s' : ScannerState} {c : Char}
    (hcorr : ScannerSurfCorr sc sp)
    (hpeek : sc.peek? = some c)
    (hstart : canStartPlainScalarBool c (sc.peekAt? 1) sc.inFlow = true)
    (h_not_doc : sc.col = 0 → atDocumentBoundary sc = false)
    (hok : scanPlainScalar sc = .ok s')
    (hinflow : sc.inFlow = true)
    (hcol : sc.currentIndent < (sc.col : Int))
    (hn : (n : Int) ≤ max 0 (sc.currentIndent + 1)) :
    ∃ sp_gram sp', SFlowContent n .flowIn sp sp_gram ∧
                   GStar SSWhite sp_gram sp' ∧
                   (sp_gram = sp' → s'.peek? ≠ some '#') ∧
                   ScannerSurfCorr s' sp' := by
  obtain ⟨rest, hsp_eq⟩ := peek_some_sp hcorr hpeek
  have hrest_head : ∀ m, sc.peekAt? 1 = some m → ∃ rest', rest = m :: rest' := by
    intro m hm; unfold ScannerState.peekAt? at hm
    have hcorr' := hsp_eq ▸ hcorr
    obtain ⟨pre, rest', hcs, hlen⟩ :=
      peekAtLoop_some_chars hcorr'.end_eq hm (c :: rest) hcorr'.chars_from
    have ⟨a, ha⟩ : ∃ a, pre = [a] := by
      cases pre with
      | nil => simp at hlen
      | cons a as => cases as with
        | nil => exact ⟨a, rfl⟩
        | cons => simp at hlen
    subst ha; simp at hcs; obtain ⟨_, rfl⟩ := hcs; exact ⟨rest', rfl⟩
  rw [hsp_eq]; rw [hsp_eq] at hcorr
  have h_first : SNsPlainFirst (ctxOfInFlow sc.inFlow) ⟨c :: rest, sc.col⟩ ⟨rest, sc.col + 1⟩ :=
    canStartPlainScalar_to_SNsPlainFirst c rest sc.col (sc.peekAt? 1) sc.inFlow hstart hrest_head
  unfold scanPlainScalar at hok
  simp only [bind, Except.bind] at hok
  split at hok
  · simp at hok
  · rename_i result hloop
    simp only [Except.ok.injEq] at hok; subst hok
    have h_term_none := canStartPlain_first_not_terminates c sc sc.inFlow hstart h_not_doc
    have h_safe := canStartPlain_implies_safe hstart
    have h_nws := canStartPlainScalar_not_ws hstart
    have h_nlb := canStartPlain_not_linebreak hstart
    have h_has_more := peek_some_has_more hpeek
    obtain ⟨fuel', h_fuel_eq⟩ : ∃ m, (sc.inputEnd - sc.offset + 1) * 2 = m + 1 :=
      ⟨(sc.inputEnd - sc.offset + 1) * 2 - 1, by omega⟩
    rw [h_fuel_eq] at hloop
    have hloop' := collectPlainScalarLoop_content_first_step
      hpeek h_term_none h_nlb h_nws h_safe hloop
    have hcorr_adv := advance_non_newline_corr sc c rest hcorr h_has_more
      (isPlainSafe_not_newline h_safe).1 (isPlainSafe_not_newline h_safe).2
    have hci_eq : (if sc.inFlow then sc.col else (max 0 (sc.currentIndent + 1)).toNat)
        = sc.col := by rw [hinflow]; rfl
    rw [hci_eq] at hloop'
    rcases collectPlainScalarLoop_prod_at n sc.advance ⟨rest, sc.col + 1⟩ _ "" _ _ _
        ⟨rest, sc.col + 1⟩ sc.inFlow sc.currentIndent hcorr_adv (GStar.nil _)
        (fun _ => rfl)
        (fun _ _ => by
          have h : sc.col + 1 = sc.advance.col := hcorr_adv.col_eq
          omega)
        (fun h => by simp at h)
        (currentIndent_of_indents_eq (advance_indents sc))
        (by rw [advance_inputEnd]; exact Nat.le_refl _)
        hloop' (by omega) hn
        (fun hnf => absurd hnf (by simp [hinflow])) with
      ⟨sp_entries, sp_next, sp_trail, h_entries, h_next_lines, h_trail, hcorr_result, h_hash, -⟩
    · have h_ml : SNsPlainMultiLine n (ctxOfInFlow sc.inFlow) ⟨c :: rest, sc.col⟩ sp_next :=
        SNsPlainMultiLine.mk n (ctxOfInFlow sc.inFlow) _ _ sp_next
          (SNsPlainOneLine.mk (ctxOfInFlow sc.inFlow) _ ⟨rest, sc.col + 1⟩ sp_entries
            h_first h_entries)
          h_next_lines
      rw [hinflow] at h_ml
      exact ⟨sp_next, sp_trail,
        SFlowContent.plain n .flowIn _ _ h_ml,
        h_trail,
        fun heq hpk => h_hash
          (collectPlainScalarLoop_terminated_of_fuel _ sc "" "" sc.inFlow _ sc.inputEnd result hloop
            (by omega))
          heq hpk,
        corr_of_simpleKeyAllowed_needIndentCheck_update false false
          (corr_of_emitAt _ _ hcorr_result)⟩

end L4YAML.Proofs.ScalarFoldAt

end Blanket
