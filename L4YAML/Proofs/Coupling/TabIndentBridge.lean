/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Proofs.Coupling.CouplingBridge
public import L4YAML.Proofs.Foundation.SurfaceSpan
public import L4YAML.Proofs.Scanner.ScanStrictCoupling
public import L4YAML.Proofs.Scanner.ScannerWhitespace
public import L4YAML.Proofs.Scanner.CloseStaleExplicitKey

@[expose] public section Blanket

/-!
# The located tab, and the scanner's backward scan (DOCS item 32)

`gstar_white_sIndent_or_tab` splits the whitespace run a step leaves in front
of a block indicator: either it is `[63] s-indent(k)` — spaces only — or it
carries a TAB, which `[63]` cannot derive.  Item 31 made the second arm
REFUTABLE by giving `?` and `:` the §6.1 backward scan `-` already had.  This
file is the refutation's other half: the arm's tab, LOCATED, is the same
character the scanner's own backward scan reads.

Three steps, none of which mentions the block indicators:

1. **Runs consume a prefix.**  Every production `[79] s-l-comments` is built
   from advances the surface position, so its end characters are a suffix of
   its start characters.  This is what puts the run inside `input.toList`
   rather than merely beside it — without it, a tab "in the run" and a tab
   "before the scanner's offset" are statements about different lists.
2. **The run, as characters.**  A `GStar SSWhite` walk from the landing to the
   indicator is a list of `s-white`s whose length is the indicator's column
   (the landing is at column 0), and the located disjunct puts a `'\t'` inside
   that list.
3. **The backward walks find it.**  `hasTabInPrecedingWhitespaceLoop` and
   `tabInLineIndentLoop` step `prev`/`get` exactly the way
   `peekBack_eq_last_prefix` does, one character at a time, so a run of whites
   ending at the scanner's offset is walked to its start.

The two loops differ in their stopping rule and so answer different questions:
the first reports the run it walked (`[66] s-separate-in-line`, which admits a
tab), the second walks the whole line and reports `false` if anything on it is
not a white (`[63] s-indent(n)`, which does not).  Both are `true` here,
because the landing IS the line start.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.TabIndentBridge

open L4YAML.Proofs.CloseStaleExplicitKey

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScanStrictCoupling
open L4YAML.Proofs.ScannerWhitespace
open L4YAML.Proofs.SurfaceSpan

/-! ## §1 Surface productions consume a prefix

The generic family — `[28] b-break` through `[79] s-l-comments` and the
combinator transports they are built from — moved to
`L4YAML/Proofs/Foundation/SurfaceSpan.lean` at item 229, where it sits beside
the other 63 productions of the same closure and imports only the grammar.
Only the scanner-side statement is local to this file. -/

/-- The scanner's own surface position is a suffix of its input. -/
lemma corr_chars_suffix {sc : ScannerState} {sp : SurfPos} (h : ScannerSurfCorr sc sp) :
    sp.chars <:+ sc.input.toList := by
  obtain ⟨pre, hsplit, _⟩ := h.input_prefix
  exact ⟨pre, hsplit.symm⟩

/-! ## §2 The run, as characters -/

/-- A `GStar SSWhite` walk is a list of `s-white`s, and it advances the column
    by its own length — `[66] s-separate-in-line` measured on the line. -/
lemma gstar_sswhite_run {s s' : SurfPos} (h : GStar SSWhite s s') :
    ∃ ws, s.chars = ws ++ s'.chars ∧ (∀ c ∈ ws, c = ' ' ∨ c = '\t') ∧
          s'.col = s.col + ws.length := by
  induction h with
  | nil s => exact ⟨[], by simp, by simp, by simp⟩
  | cons s₁ s₂ s₃ hw _ ih =>
    cases hw with
    | space rest col =>
      obtain ⟨ws, hch, hwh, hcol⟩ := ih
      refine ⟨' ' :: ws, by simpa using hch, ?_, by simp at hcol ⊢; omega⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inl rfl
      · exact hwh c hc
    | tab rest col =>
      obtain ⟨ws, hch, hwh, hcol⟩ := ih
      refine ⟨'\t' :: ws, by simpa using hch, ?_, by simp at hcol ⊢; omega⟩
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inr rfl
      · exact hwh c hc

/-- **The located disjunct, as a character fact.**  The point of locating the
    tab is exactly this: `'\t' ∈ ws`, where `ws` is the run in front of the
    indicator — and not `'\t' ∈ s.chars`, which almost every document
    satisfies and no runtime check can refute. -/
lemma located_tab_run {s s' : SurfPos}
    (h : ∃ sa sb, GStar SSWhite s sa ∧ SSWhite sa sb ∧ sa.chars.head? = some '\t' ∧
                  GStar SSWhite sb s') :
    ∃ ws, s.chars = ws ++ s'.chars ∧ (∀ c ∈ ws, c = ' ' ∨ c = '\t') ∧ '\t' ∈ ws := by
  obtain ⟨sa, sb, h1, h2, h3, h4⟩ := h
  have hsa : sa.chars = '\t' :: sb.chars := by
    cases h2 with
    | space rest col => simp at h3
    | tab rest col => rfl
  obtain ⟨ws0, hch0, hwh0, _⟩ := gstar_sswhite_run h1
  obtain ⟨ws1, hch1, hwh1, _⟩ := gstar_sswhite_run h4
  refine ⟨ws0 ++ '\t' :: ws1, ?_, ?_, ?_⟩
  · rw [hch0, hsa, hch1]; simp
  · intro c hc
    rcases List.mem_append.mp hc with hc | hc
    · exact hwh0 c hc
    · rcases List.mem_cons.mp hc with rfl | hc
      · exact Or.inr rfl
      · exact hwh1 c hc
  · exact List.mem_append_right _ (List.mem_cons_self ..)

/-! ## §3 The backward walks read the same characters -/

lemma listByteSize_length_le (l : List Char) : l.length ≤ listByteSize l := by
  induction l with
  | nil => simp [listByteSize]
  | cons c cs ih => have := Char.utf8Size_pos c; simp [listByteSize]; omega

/-- One backward step, at a known character boundary: `prev` lands on the
    start of the last character of the prefix and `get` recovers it.  The same
    pair of facts `peekBack_eq_last_prefix` takes, phrased for a prefix given
    as `pre ++ [c]`. -/
lemma prev_get_at_concat {input : String} {pre : List Char} {c : Char} {suf : List Char}
    (hsplit : input.toList = pre ++ c :: suf) :
    String.Pos.Raw.prev input ⟨listByteSize pre + c.utf8Size⟩ = ⟨listByteSize pre⟩ ∧
    String.Pos.Raw.get input ⟨listByteSize pre⟩ = c := by
  constructor
  · show String.Pos.Raw.utf8PrevAux input.toList 0 ⟨listByteSize pre + c.utf8Size⟩ =
      ⟨listByteSize pre⟩
    rw [hsplit]
    have h := utf8PrevAux_at_boundary pre c suf 0
    simpa using h
  · show String.Pos.Raw.utf8GetAux input.toList 0 ⟨listByteSize pre⟩ = c
    rw [hsplit]
    have h := utf8GetAux_at_boundary pre c suf (0 : String.Pos.Raw)
    simpa using h

/-- Peel the last character of a nonempty list. -/
private lemma exists_concat {l : List Char} (h : l ≠ []) : ∃ l' c, l = l' ++ [c] :=
  ⟨l.dropLast, l.getLast h, (List.dropLast_concat_getLast h).symm⟩

/-- **`[66]`'s walk finds the tab.**  Walking back from the end of a run of
    `s-white`s, the loop meets every one of them before it meets anything
    else, so a tab anywhere in the run is reported. -/
lemma hasTabLoop_of_run (input : String) :
    ∀ (fuel : Nat) (pre ws tail : List Char),
      input.toList = pre ++ ws ++ tail →
      (∀ c ∈ ws, c = ' ' ∨ c = '\t') → '\t' ∈ ws → ws.length ≤ fuel →
      ScannerState.hasTabInPrecedingWhitespaceLoop input
        (listByteSize (pre ++ ws)) fuel = true := by
  intro fuel
  induction fuel with
  | zero =>
    intro pre ws tail _ _ htab hlen
    have hnil : ws = [] := List.eq_nil_of_length_eq_zero (by omega)
    rw [hnil] at htab; simp at htab
  | succ n ih =>
    intro pre ws tail hsplit hwh htab hlen
    have hne : ws ≠ [] := by intro h; rw [h] at htab; simp at htab
    obtain ⟨ws', c, rfl⟩ := exists_concat hne
    have hcw : c = ' ' ∨ c = '\t' := hwh c (by simp)
    have hsplit' : input.toList = (pre ++ ws') ++ c :: tail := by
      rw [hsplit]; simp
    have hbs : listByteSize (pre ++ (ws' ++ [c])) = listByteSize (pre ++ ws') + c.utf8Size := by
      rw [← List.append_assoc, listByteSize_append, listByteSize_append]
      simp [listByteSize]
    obtain ⟨hprev, hget⟩ := prev_get_at_concat hsplit'
    rw [ScannerState.hasTabInPrecedingWhitespaceLoop, hbs]
    have hpos : ¬ (listByteSize (pre ++ ws') + c.utf8Size = 0) := by
      have := Char.utf8Size_pos c; omega
    simp only [beq_iff_eq, ite_eq_right hpos, hprev, hget]
    rcases hcw with rfl | rfl
    · -- a space: keep walking, and the tab is still in what is left
      have htab' : '\t' ∈ ws' := by
        rcases List.mem_append.mp htab with h | h
        · exact h
        · simp at h
      have hlen' : ws'.length ≤ n := by simp at hlen; omega
      simpa using ih pre ws' (' ' :: tail) (by simp [hsplit'])
        (fun x hx => hwh x (List.mem_append_left _ hx)) htab' hlen'
    · simp

/-- **`[63]`'s walk finds the tab too, and says more.**  It walks the whole
    line rather than the run, so `true` also certifies that nothing on the
    line precedes the token — which is what makes the run indentation. -/
lemma tabInLineIndentLoop_of_run (input : String) :
    ∀ (m : Nat) (pre ws tail : List Char) (sawTab : Bool),
      ws.length = m →
      input.toList = pre ++ ws ++ tail →
      (∀ c ∈ ws, c = ' ' ∨ c = '\t') → (sawTab = true ∨ '\t' ∈ ws) →
      ScannerState.tabInLineIndentLoop input (listByteSize (pre ++ ws)) m sawTab = true := by
  intro m
  induction m with
  | zero =>
    intro pre ws tail sawTab hm _ _ hdisj
    have hnil : ws = [] := List.eq_nil_of_length_eq_zero hm
    rw [ScannerState.tabInLineIndentLoop]
    rcases hdisj with h | h
    · exact h
    · rw [hnil] at h; simp at h
  | succ n ih =>
    intro pre ws tail sawTab hm hsplit hwh hdisj
    have hne : ws ≠ [] := by intro h; rw [h] at hm; simp at hm
    obtain ⟨ws', c, rfl⟩ := exists_concat hne
    have hcw : c = ' ' ∨ c = '\t' := hwh c (by simp)
    have hlen' : ws'.length = n := by simp at hm; omega
    have hsplit' : input.toList = (pre ++ ws') ++ c :: tail := by
      rw [hsplit]; simp
    have hbs : listByteSize (pre ++ (ws' ++ [c])) = listByteSize (pre ++ ws') + c.utf8Size := by
      rw [← List.append_assoc, listByteSize_append, listByteSize_append]
      simp [listByteSize]
    obtain ⟨hprev, hget⟩ := prev_get_at_concat hsplit'
    rw [ScannerState.tabInLineIndentLoop, hbs]
    have hpos : ¬ (listByteSize (pre ++ ws') + c.utf8Size = 0) := by
      have := Char.utf8Size_pos c; omega
    simp only [beq_iff_eq, ite_eq_right hpos, hprev, hget]
    have hwh' : ∀ x ∈ ws', x = ' ' ∨ x = '\t' :=
      fun x hx => hwh x (List.mem_append_left _ hx)
    rcases hcw with rfl | rfl
    · have hdisj' : sawTab = true ∨ '\t' ∈ ws' := by
        rcases hdisj with h | h
        · exact Or.inl h
        · rcases List.mem_append.mp h with h | h
          · exact Or.inr h
          · simp at h
      simpa using ih pre ws' (' ' :: tail) sawTab hlen' (by simp [hsplit']) hwh' hdisj'
    · simpa using ih pre ws' ('\t' :: tail) true hlen' (by simp [hsplit']) hwh'
        (Or.inl rfl)

/-! ## §4 Preprocessing does not change the input string

`ScannerSurfCorr` names `sc.input`, so a suffix fact carried on the state
BEFORE preprocessing speaks about a different `String` from the one the
preprocessed state's backward scan reads — unless the two are the same one.
They are: none of the five functions `skipToContent` descends through writes
`input`, and neither does `unwindIndents` or `saveSimpleKey`.  The same
mechanical descent `PreprocessIndentStable` makes for the indent stack. -/

lemma skipSpacesLoop_input (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).input = s.input := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' ih =>
    unfold skipSpacesLoop
    split
    · rw [ih, advance_input]
    · rfl

lemma skipSpaces_input (s : ScannerState) :
    (skipSpaces s).input = s.input := skipSpacesLoop_input s _

lemma collectCommentTextLoop_input (s : ScannerState) (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.input = s.input := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' ih =>
    unfold collectCommentTextLoop
    split
    · split
      · rfl
      · rw [ih, advance_input]
    · rfl

lemma skipToContentComment_input (s : ScannerState) :
    (skipToContentComment s).input = s.input := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_input, advance_input]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_input, advance_input]
      · rfl
  · rfl

lemma skipToContentWs_input (s s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.input = s.input := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h
          rw [← h, skipWhitespace_input, skipSpaces_input]
        · split at h
          · simp at h
            rw [← h, skipWhitespace_input, skipSpaces_input]
          · split at h
            · simp at h
              rw [← h, skipWhitespace_input, skipSpaces_input]
            · simp at h
        · simp at h
          rw [← h, skipWhitespace_input, skipSpaces_input]
      · simp at h
        rw [← h, skipSpaces_input]
    · simp at h
      rw [← h, skipWhitespace_input, skipSpaces_input]
  · simp at h
    rw [← h, skipWhitespace_input]

lemma skipToContentLoop_input (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.input = s.input := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · rw [ih _ h, consumeNewline_preserves_input, skipToContentComment_input]
            exact skipToContentWs_input s s1 hws
          · rw [ih _ h, consumeNewline_preserves_input, skipToContentComment_input]
            exact skipToContentWs_input s s1 hws
        · simp at h
          rw [← h, skipToContentComment_input]
          exact skipToContentWs_input s s1 hws
      · simp at h
        rw [← h, skipToContentComment_input]
        exact skipToContentWs_input s s1 hws

lemma skipToContent_input (s s' : ScannerState) (h : skipToContent s = .ok s') :
    s'.input = s.input := by
  unfold skipToContent at h
  exact skipToContentLoop_input s s' _ h

/-- **The string survives preprocessing.**  The three writers it composes — the
    walk, the armed unwind, and the key save — all leave `input` alone. -/
lemma preprocess_input {sc s_prep : ScannerState} {c : Char}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    s_prep.input = sc.input := by
  unfold scanNextToken_preprocess at hok
  simp only [bind, Except.bind, pure, Except.pure] at hok
  split at hok
  · simp at hok
  · rename_i s_content h_skip
    have h_c : s_content.input = sc.input := skipToContent_input sc s_content h_skip
    split at hok
    · simp at hok
    · split at hok
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            rw [closeStaleExplicitKey_input, saveSimpleKey_input]
            show (unwindIndents s_content ↑s_content.col).input = sc.input
            unfold unwindIndents
            rw [unwindIndentsLoop_input]; exact h_c
      · split at hok
        · simp at hok
        · split at hok
          · simp at hok
          · have h := Except.ok.inj hok; injection h with h
            obtain ⟨h1, h2⟩ := Prod.mk.inj h; subst h1; subst h2
            rw [closeStaleExplicitKey_input, saveSimpleKey_input]; exact h_c

/-! ## §5 The bridge -/

/-- The scanner's two backward scans, from a run of `s-white`s that ends at
    its offset and contains a tab.

    **The two are not equally available** (item 33).  `[66]`'s scan reads the
    run and nothing else, so it answers from the run alone; `[63]`'s reads the
    whole LINE in front of the offset, so it answers only when the run IS the
    line — `sc.col = ws.length`.  A COMPACT collection's run is not: the
    indicator that parked the pending is on the line in front of it.  The
    second conjunct is therefore stated as an implication rather than split
    into a second lemma, so that both callers share the one offset
    decomposition. -/
lemma tab_scans_of_run {sc : ScannerState} {sp_land sp_ind : SurfPos} {ws : List Char}
    (hcorr : ScannerSurfCorr sc sp_ind)
    (hsuf : sp_land.chars <:+ sc.input.toList)
    (hrun : sp_land.chars = ws ++ sp_ind.chars)
    (hwh : ∀ c ∈ ws, c = ' ' ∨ c = '\t') (htab : '\t' ∈ ws) :
    sc.hasTabInPrecedingWhitespace = true ∧
      (sc.col = ws.length → sc.tabInLineIndent = true) := by
  obtain ⟨pre, hsplit, hoff⟩ := hcorr.input_prefix
  obtain ⟨q, hq⟩ := hsuf
  have heq : pre ++ sp_ind.chars = (q ++ ws) ++ sp_ind.chars := by
    rw [← hsplit, ← hq, hrun, List.append_assoc]
  have hpre : pre = q ++ ws := List.append_cancel_right heq
  have hfull : sc.input.toList = q ++ ws ++ sp_ind.chars := by
    rw [hsplit, hpre, List.append_assoc]
  have hoff' : listByteSize (q ++ ws) = sc.offset := by rw [← hpre]; exact hoff
  have hlen : ws.length ≤ sc.offset := by
    rw [← hoff', listByteSize_append]
    have := listByteSize_length_le ws; omega
  refine ⟨?_, ?_⟩
  · unfold ScannerState.hasTabInPrecedingWhitespace
    have h := hasTabLoop_of_run sc.input sc.offset q ws sp_ind.chars hfull hwh htab hlen
    rwa [hoff'] at h
  · intro hcol
    unfold ScannerState.tabInLineIndent
    have h := tabInLineIndentLoop_of_run sc.input ws.length q ws sp_ind.chars false rfl hfull hwh
      (Or.inr htab)
    rw [hoff'] at h
    rw [hcol]; exact h

/-- **The refutation, packaged** (item 32).

    The landing is at column 0, the run from it to the indicator is
    `[66] s-white*` and the located disjunct puts a tab inside it — so both of
    the scanner's §6.1 scans answer `true`, and every block indicator that
    reads either of them refuses before the accumulation is reached. -/
lemma tabIndent_scans_of_located
    {sc : ScannerState} {sp_land sp_ind : SurfPos}
    (hcorr : ScannerSurfCorr sc sp_ind)
    (hsuf : sp_land.chars <:+ sc.input.toList)
    (hcol0 : sp_land.col = 0)
    (hws : GStar SSWhite sp_land sp_ind)
    (htab : ∃ sa sb, GStar SSWhite sp_land sa ∧ SSWhite sa sb ∧
              sa.chars.head? = some '\t' ∧ GStar SSWhite sb sp_ind) :
    sc.hasTabInPrecedingWhitespace = true ∧ sc.tabInLineIndent = true := by
  obtain ⟨ws, hrun, hwh, hmem⟩ := located_tab_run htab
  obtain ⟨ws2, hrun2, _, hcolrun⟩ := gstar_sswhite_run hws
  have hwseq : ws = ws2 := List.append_cancel_right (hrun.symm.trans hrun2)
  have hcol : sc.col = ws.length := by
    have h1 : sp_ind.col = sp_land.col + ws2.length := hcolrun
    rw [hcol0] at h1
    have h2 : sp_ind.col = sc.col := hcorr.col_eq
    subst hwseq
    omega
  obtain ⟨h1, h2⟩ := tab_scans_of_run hcorr hsuf hrun hwh hmem
  exact ⟨h1, h2 hcol⟩

/-- **The refutation one production down** (item 33): a tab inside the run in
    front of a COMPACT indicator.

    `[185] s-l+block-indented`'s `s-indent(m)` is spaces only for the same
    reason `[63]` is anywhere else, but the run is no longer the whole line —
    the `-` (or `?`, or `:`) that opened the entry sits in front of it — so
    `[63]`'s own backward walk stops on that indicator and answers `false`.
    What survives is `[66]`'s scan, which reads the run and nothing else, and
    that is enough for the two indicators that consult it unconditionally.  So
    this lemma is `tabIndent_scans_of_located` with the column-0 landing
    dropped AND the second conjunct with it — a strictly weaker package,
    which is exactly what the residue can pay for. -/
lemma tabRun_scan_of_located
    {sc : ScannerState} {sp_run sp_ind : SurfPos}
    (hcorr : ScannerSurfCorr sc sp_ind)
    (hsuf : sp_run.chars <:+ sc.input.toList)
    (htab : ∃ sa sb, GStar SSWhite sp_run sa ∧ SSWhite sa sb ∧
              sa.chars.head? = some '\t' ∧ GStar SSWhite sb sp_ind) :
    sc.hasTabInPrecedingWhitespace = true := by
  obtain ⟨ws, hrun, hwh, hmem⟩ := located_tab_run htab
  exact (tab_scans_of_run hcorr hsuf hrun hwh hmem).1

end L4YAML.Proofs.TabIndentBridge

end Blanket
