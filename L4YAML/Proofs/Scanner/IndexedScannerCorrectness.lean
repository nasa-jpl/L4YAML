/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.IndexedScannerPlainScalarValid

/-! # `IndexedScannerCorrectness` — Phase 3 Step 6f.3b2.main (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of the `filter_preserves_*` family in
`Proofs/Production/ScannerPlainScalarValid.lean` (lines 5197–5567).
Bridges `scan_flow_aware_psv_ix_axiom` /
`scan_flow_brackets_matched_ix_axiom` (which operate on
`Scanner.Indexed.ScannerStateIx.scanIx`, the unfiltered path) to
`scanFilteredIx` (which strips `.placeholder` tokens between the
scanner and the parser).

The structure mirrors the legacy file:

  - §1  List-level filter index correspondence
        (`list_filter_origIdx`, `list_filter_getElem_by_count`)
  - §2  Array wrapper (`array_filter_getElem_correspondence`)
  - §3  `flowNestingIx_go_filter_equiv`
  - §4  `filter_preserves_FlowContextPSVIx`,
        `filter_preserves_PlainScalarsValidIx`,
        `filter_preserves_FlowAwarePSVIx`,
        `filter_preserves_FlowBracketsMatchedIx`
  - §5  `scanFilteredIx_FlowAwarePSVIx`,
        `scanFilteredIx_FlowBracketsMatchedIx`
        (chain §4 with `scan_flow_aware_psv_ix_axiom` /
        `scan_flow_brackets_matched_ix_axiom`).

## Phase 3 Step 6f cutover

At cutover, this file is renamed to
`Proofs/Scanner/ScannerCorrectness.lean` (overwriting the legacy
file) and the namespace
`L4YAML.Proofs.Indexed.ScannerCorrectness` reverts to
`L4YAML.Proofs.ScannerCorrectness`. -/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.ScannerCorrectness

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.WellBehaved
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ## §1  List-level filter index correspondence

Generic `List α` lemmas (independent of the `IxToken` element type).
Copies of the legacy `list_filter_origIdx` /
`list_filter_getElem_by_count` from
`ScannerPlainScalarValid.lean:5201` / `:5236`. Re-stated locally so
this file does not depend on the legacy production file (which is
deleted at the 6f.6 cutover). -/

/-- Core List-level reverse direction: for every position `i` in a
    filtered list, there exists a canonical position `j` in the
    original list such that the filtered element equals the original,
    it satisfies the predicate, and `i` equals the count of satisfying
    elements before `j`. -/
theorem list_filter_origIdx
    {α : Type _} (l : List α) (p : α → Bool) (i : Nat)
    (hi : i < (l.filter p).length) :
    ∃ j, ∃ hj : j < l.length,
      (l.filter p)[i] = l[j] ∧
      p l[j] = true ∧
      i = ((l.take j).filter p).length := by
  induction l generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    by_cases hpx : p x = true
    · simp only [List.filter_cons_of_pos hpx] at hi
      cases i with
      | zero =>
        exact ⟨0, by simp,
          by simp [List.filter_cons_of_pos hpx],
          by simpa using hpx,
          by simp⟩
      | succ i' =>
        simp only [List.length_cons] at hi
        have hi' : i' < (xs.filter p).length := by omega
        obtain ⟨j', hj', val_eq, p_eq, count_eq⟩ := ih i' hi'
        refine ⟨j' + 1, by simp; omega, ?_, ?_, ?_⟩
        · simp only [List.filter_cons_of_pos hpx, List.getElem_cons_succ]; exact val_eq
        · simp only [List.getElem_cons_succ]; exact p_eq
        · simp only [List.take_succ_cons, List.filter_cons_of_pos hpx, List.length_cons]; omega
    · simp only [List.filter_cons_of_neg hpx] at hi
      obtain ⟨j', hj', val_eq, p_eq, count_eq⟩ := ih i hi
      refine ⟨j' + 1, by simp; omega, ?_, ?_, ?_⟩
      · simp only [List.filter_cons_of_neg hpx, List.getElem_cons_succ]; exact val_eq
      · simp only [List.getElem_cons_succ]; exact p_eq
      · simp only [List.take_succ_cons, List.filter_cons_of_neg hpx]; exact count_eq

/-- Core List-level forward direction: position `j` in a list with
    `p l[j] = true` maps to position `i = (l.take j |>.filter p).length`
    in the filtered list. -/
theorem list_filter_getElem_by_count
    {α : Type _} (l : List α) (p : α → Bool) (j : Nat) (hj : j < l.length)
    (h_sat : p l[j] = true) :
    ((l.take j).filter p).length < (l.filter p).length ∧
    ∀ (h : ((l.take j).filter p).length < (l.filter p).length),
      (l.filter p)[((l.take j).filter p).length] = l[j] := by
  induction l generalizing j with
  | nil => simp at hj
  | cons x xs ih =>
    cases j with
    | zero =>
      simp only [List.take, List.filter, List.getElem_cons_zero] at *
      exact ⟨by simp [h_sat], fun _ => by simp [h_sat]⟩
    | succ j' =>
      have hj' : j' < xs.length := by simp at hj; omega
      simp only [List.getElem_cons_succ] at h_sat
      have ih_result := ih j' hj' h_sat
      simp only [List.take_succ_cons]
      by_cases hpx : p x = true
      · simp only [List.filter_cons_of_pos hpx, List.length_cons, List.getElem_cons_succ]
        exact ⟨by omega, fun _ => ih_result.2 ih_result.1⟩
      · simp only [List.filter_cons_of_neg hpx]
        exact ih_result

/-! ## §2  Array wrapper -/

/-- The i-th element of a filtered array corresponds to the j-th
    element of the original array, where i counts elements satisfying
    the predicate before j. Indexed twin of legacy
    `array_filter_getElem_correspondence`; structurally identical
    (the element type is generic). -/
theorem array_filter_getElem_correspondence
    {α : Type _} (arr : Array α) (p : α → Bool) (j : Nat) (hj : j < arr.size)
    (h_sat : p arr[j] = true) :
    let filtered := arr.filter p
    let i := (arr.toList.take j).filter p |>.length
    ∃ (h : i < filtered.size), filtered[i] = arr[j] := by
  intro filtered i
  have hj_list : j < arr.toList.length := by simpa using hj
  have h_sat_list : p arr.toList[j] = true := by simpa [Array.getElem_toList] using h_sat
  have h_list := list_filter_getElem_by_count arr.toList p j hj_list h_sat_list
  have h_bound : i < filtered.size := by
    show ((arr.toList.take j).filter p).length < (arr.filter p).size
    rw [show (arr.filter p).size = (arr.filter p).toList.length from rfl,
        Array.toList_filter]
    exact h_list.1
  refine ⟨h_bound, ?_⟩
  have h_val := h_list.2 h_list.1
  show (arr.filter p).toList[i] = arr.toList[j]
  simp only [Array.toList_filter]
  exact h_val

/-! ## §3  `flowNestingIx.go` filter equivalence

Indexed twin of legacy `flowNesting_go_filter_equiv`
(`ScannerPlainScalarValid.lean:5287`). The proof structure mirrors
the legacy version exactly, modulo:

  - `Array (Positioned YamlToken)` → `Array (IxToken input)`
  - `flowNesting.go` → `flowNestingIx.go`
  - `flowNesting_go_step` → `flowNestingIx_go_step`
  - `t.val` → `t.token`

The predicate is `fun t => t.token != YamlToken.placeholder`
(the filter `scanFilteredIx` applies). -/

/-- `flowNestingIx.go` on the original array equals `flowNestingIx.go`
    on the filtered array, where the target in the filtered array is
    the count of non-placeholder tokens before position `j`. -/
theorem flowNestingIx_go_filter_equiv
    (all_tokens : Array (IxToken input))
    (j : Nat) (hj : j ≤ all_tokens.size)
    (depth : Nat) :
    let p := fun (t : IxToken input) => t.token != YamlToken.placeholder
    let filtered := all_tokens.filter p
    let i := (all_tokens.toList.take j).filter p |>.length
    flowNestingIx.go all_tokens 0 j depth =
    flowNestingIx.go filtered 0 i depth := by
  intro p filtered
  show flowNestingIx.go all_tokens 0 j depth =
    flowNestingIx.go filtered 0 ((all_tokens.toList.take j).filter p |>.length) depth
  induction j generalizing depth with
  | zero =>
    simp only [List.take_zero, List.filter_nil, List.length_nil]
    rw [flowNestingIx_go_ge_target _ _ _ _ (by omega : 0 ≥ 0),
        flowNestingIx_go_ge_target _ _ _ _ (by omega : 0 ≥ 0)]
  | succ j' ih =>
    rw [flowNestingIx_go_split all_tokens 0 j' (j' + 1) depth (by omega) (by omega)]
    rw [ih (by omega : j' ≤ all_tokens.size)]
    by_cases hj'_bound : j' < all_tokens.size
    · have hj'_list : j' < all_tokens.toList.length := by simpa using hj'_bound
      have h_take_split : all_tokens.toList.take (j' + 1) =
          all_tokens.toList.take j' ++ [all_tokens.toList[j']] :=
        List.take_succ_eq_append_getElem hj'_list
      by_cases h_ph : (all_tokens[j']).token = YamlToken.placeholder
      · rw [flowNestingIx_go_step all_tokens j' (j' + 1) _ hj'_bound (by omega)]
        simp [h_ph]
        rw [flowNestingIx_go_ge_target all_tokens (j' + 1) (j' + 1) _ (by omega)]
        congr 1
        show (List.filter p (List.take j' all_tokens.toList)).length =
             (List.filter p (List.take (j' + 1) all_tokens.toList)).length
        symm
        rw [h_take_split, List.filter_append, List.length_append]
        simp only [List.filter]
        have : p all_tokens.toList[j'] = false := by
          simp only [p, bne]
          rw [Array.getElem_toList hj'_bound, h_ph]
          decide
        rw [this]; simp
      · have h_p_true : p all_tokens[j'] = true := by
          simp only [p, bne, Bool.not_eq_true']
          exact decide_eq_false h_ph
        have h_p_list : p all_tokens.toList[j'] = true := by
          rwa [Array.getElem_toList hj'_bound]
        have h_len_succ : (List.filter p (List.take (j' + 1) all_tokens.toList)).length =
            (List.filter p (List.take j' all_tokens.toList)).length + 1 := by
          rw [h_take_split, List.filter_append, List.length_append]
          simp only [List.filter, h_p_list, List.length_cons, List.length_nil]
        obtain ⟨h_i_bound, h_filt_eq⟩ :=
          array_filter_getElem_correspondence all_tokens p j' hj'_bound h_p_true
        rw [h_len_succ]
        rw [flowNestingIx_go_split filtered 0
          ((List.filter p (List.take j' all_tokens.toList)).length)
          ((List.filter p (List.take j' all_tokens.toList)).length + 1)
          _ (by omega) (by omega)]
        rw [flowNestingIx_go_step all_tokens j' (j' + 1) _ hj'_bound (by omega)]
        rw [flowNestingIx_go_step filtered
          ((List.filter p (List.take j' all_tokens.toList)).length)
          ((List.filter p (List.take j' all_tokens.toList)).length + 1)
          _ h_i_bound (by omega)]
        simp only [flowNestingIx_go_ge_target _ _ _ _ (by omega : j' + 1 ≥ j' + 1),
                    flowNestingIx_go_ge_target _ _ _ _
                      (by omega : (List.filter p (List.take j' all_tokens.toList)).length + 1 ≥
                        (List.filter p (List.take j' all_tokens.toList)).length + 1)]
        have h_val_eq : (filtered[(List.filter p (List.take j' all_tokens.toList)).length]'h_i_bound).token =
               (all_tokens[j']'hj'_bound).token := by
          rw [h_filt_eq]
        rw [h_val_eq]
    · rw [flowNestingIx_go_oob all_tokens j' (j' + 1) _ (by omega)]
      congr 1
      show (List.filter p (List.take j' all_tokens.toList)).length =
           (List.filter p (List.take (j' + 1) all_tokens.toList)).length
      symm; congr 1
      have : all_tokens.toList.length ≤ j' := by simpa using hj'_bound
      rw [List.take_of_length_le this, List.take_of_length_le (by omega)]

/-! ## §4  Filter preserves indexed PSV / brackets

Bridges from `FlowAwarePSVIx (unfiltered tokens)` to
`FlowAwarePSVIx (filtered tokens)` and similarly for
`FlowBracketsMatchedIx`. The filter strips `.placeholder` tokens —
which are neither flow start/end nor plain scalars — so the
predicates' substantive content survives.

The `TokenStream input` wrapper around `Array (IxToken input)` makes
the predicate restatement direct: `flowNestingIx`'s definition
forwards to `flowNestingIx.go tokens.tokens`, and `tokens.size` is
`tokens.tokens.size` definitionally. -/

/-- Filtering placeholders preserves `PlainScalarsValidIx`.
    Indexed analogue of the (unstated-in-legacy)
    `filter_preserves_PlainScalarsValid`: the legacy
    `scanFiltered_plain_scalars_valid` is a thin wrapper over
    `scan_plain_scalar_valid` because legacy `scan_flow_aware_psv`
    already operates on `scanFiltered` output. In the indexed
    pipeline, `scan_flow_aware_psv_ix_axiom` operates on the
    *unfiltered* `scanIx`, so we need the explicit filter-preserves
    lemma here. -/
theorem filter_preserves_PlainScalarsValidIx
    (all_tokens : Indexed.TokenStream input)
    (h_psv : PlainScalarsValidIx all_tokens) :
    PlainScalarsValidIx
      (input := input)
      { tokens := all_tokens.tokens.filter fun t => t.token != YamlToken.placeholder } := by
  unfold PlainScalarsValidIx
  intro i hi
  let p := fun (t : IxToken input) => t.token != YamlToken.placeholder
  let filtered := all_tokens.tokens.filter p
  have hi_list : i < (all_tokens.tokens.toList.filter p).length := by
    have h_size : (Indexed.TokenStream.mk filtered).size = filtered.size := rfl
    rw [h_size] at hi
    rwa [← Array.toList_filter, show (all_tokens.tokens.filter p).toList.length =
      (all_tokens.tokens.filter p).size from rfl]
  obtain ⟨j, hj_lt, val_eq, _p_j, _count_eq⟩ :=
    list_filter_origIdx all_tokens.tokens.toList p i hi_list
  have hj_arr : j < all_tokens.size := by
    show j < all_tokens.tokens.size; simpa using hj_lt
  have val_eq_arr :
      ({ tokens := filtered } : Indexed.TokenStream input)[i]'hi =
      all_tokens[j]'hj_arr := by
    show (all_tokens.tokens.filter p)[i]'hi = all_tokens.tokens[j]'hj_arr
    have hi_list2 : i < (all_tokens.tokens.filter p).toList.length := by
      rwa [show (all_tokens.tokens.filter p).toList.length =
        (all_tokens.tokens.filter p).size from rfl]
    have hj_list2 : j < all_tokens.tokens.toList.length := by simpa using hj_arr
    show (all_tokens.tokens.filter p).toList[i]'hi_list2 = all_tokens.tokens.toList[j]'hj_list2
    simp only [Array.toList_filter]; exact val_eq
  exact val_eq_arr ▸ h_psv j hj_arr

/-- Filtering placeholders preserves `FlowContextPSVIx`. Indexed twin
    of legacy `filter_preserves_FlowContextPSV`
    (`ScannerPlainScalarValid.lean:5379`). -/
theorem filter_preserves_FlowContextPSVIx
    (all_tokens : Indexed.TokenStream input)
    (h_fpsv : FlowContextPSVIx all_tokens) :
    FlowContextPSVIx
      (input := input)
      { tokens := all_tokens.tokens.filter fun t => t.token != YamlToken.placeholder } := by
  unfold FlowContextPSVIx
  intro i hi h_flow
  let p := fun (t : IxToken input) => t.token != YamlToken.placeholder
  let filtered : Indexed.TokenStream input := { tokens := all_tokens.tokens.filter p }
  have hi_list : i < (all_tokens.tokens.toList.filter p).length := by
    have h_size : filtered.size = (all_tokens.tokens.filter p).size := rfl
    rw [h_size] at hi
    rwa [← Array.toList_filter, show (all_tokens.tokens.filter p).toList.length =
      (all_tokens.tokens.filter p).size from rfl]
  obtain ⟨j, hj_lt, val_eq, _p_j, count_eq⟩ :=
    list_filter_origIdx all_tokens.tokens.toList p i hi_list
  have hj_arr : j < all_tokens.size := by
    show j < all_tokens.tokens.size; simpa using hj_lt
  have val_eq_arr : filtered[i]'hi = all_tokens[j]'hj_arr := by
    show (all_tokens.tokens.filter p)[i]'hi = all_tokens.tokens[j]'hj_arr
    have hi_list2 : i < (all_tokens.tokens.filter p).toList.length := by
      rwa [show (all_tokens.tokens.filter p).toList.length =
        (all_tokens.tokens.filter p).size from rfl]
    have hj_list2 : j < all_tokens.tokens.toList.length := by simpa using hj_arr
    show (all_tokens.tokens.filter p).toList[i]'hi_list2 = all_tokens.tokens.toList[j]'hj_list2
    simp only [Array.toList_filter]; exact val_eq
  have h_nest_eq : flowNestingIx filtered i = flowNestingIx all_tokens j := by
    unfold flowNestingIx
    rw [count_eq]
    have hj_arr' : j ≤ all_tokens.tokens.size := Nat.le_of_lt (by
      show j < all_tokens.tokens.size; exact hj_arr)
    exact (flowNestingIx_go_filter_equiv all_tokens.tokens j hj_arr' 0).symm
  rw [h_nest_eq] at h_flow
  exact val_eq_arr ▸ h_fpsv j hj_arr h_flow

/-- Filtering placeholders preserves `FlowAwarePSVIx`. Combines
    `filter_preserves_PlainScalarsValidIx` and
    `filter_preserves_FlowContextPSVIx`. -/
theorem filter_preserves_FlowAwarePSVIx
    (all_tokens : Indexed.TokenStream input)
    (h_fapsv : FlowAwarePSVIx all_tokens) :
    FlowAwarePSVIx
      (input := input)
      { tokens := all_tokens.tokens.filter fun t => t.token != YamlToken.placeholder } :=
  ⟨filter_preserves_PlainScalarsValidIx all_tokens h_fapsv.1,
   filter_preserves_FlowContextPSVIx all_tokens h_fapsv.2⟩

/-- Filtering placeholders preserves `FlowBracketsMatchedIx`. Indexed
    twin of legacy `filter_preserves_FlowBracketsMatched`
    (`ScannerPlainScalarValid.lean:5546`). Uses
    `flowNestingIx_go_filter_equiv` with target = full array size. -/
theorem filter_preserves_FlowBracketsMatchedIx
    (all_tokens : Indexed.TokenStream input)
    (h_fbm : FlowBracketsMatchedIx all_tokens) :
    FlowBracketsMatchedIx
      (input := input)
      { tokens := all_tokens.tokens.filter fun t => t.token != YamlToken.placeholder } := by
  unfold FlowBracketsMatchedIx flowNestingIx at *
  have h_equiv := flowNestingIx_go_filter_equiv all_tokens.tokens
    all_tokens.tokens.size (Nat.le_refl _) 0
  simp only [] at h_equiv
  have h_take : List.take all_tokens.tokens.size all_tokens.tokens.toList =
      all_tokens.tokens.toList := by
    show List.take all_tokens.tokens.toList.length all_tokens.tokens.toList =
      all_tokens.tokens.toList
    exact List.take_length
  have h_target_eq : ∀ (p : IxToken input → Bool),
      (List.filter p (List.take all_tokens.tokens.size all_tokens.tokens.toList)).length =
      (all_tokens.tokens.filter p).size := by
    intro p
    rw [h_take]
    show (all_tokens.tokens.toList.filter p).length = (all_tokens.tokens.filter p).size
    rw [show (all_tokens.tokens.filter p).size = (all_tokens.tokens.filter p).toList.length from rfl,
        Array.toList_filter]
  simp only [h_target_eq] at h_equiv
  -- h_equiv : flowNestingIx.go all_tokens.tokens 0 all_tokens.tokens.size 0
  --         = flowNestingIx.go (all_tokens.tokens.filter ..) 0
  --             (all_tokens.tokens.filter ..).size 0
  -- h_fbm   : flowNestingIx.go all_tokens.tokens 0 all_tokens.size 0 = 0
  -- The wrapper `{ tokens := filter ..}.tokens` and `.size` reduce to
  -- `filter ..` and `(filter ..).size` definitionally, but omega
  -- treats syntactically distinct terms as opaque — rephrase the goal
  -- and hypothesis to match h_equiv's shape.
  show flowNestingIx.go (all_tokens.tokens.filter
    (fun t => t.token != YamlToken.placeholder)) 0
    (all_tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)).size 0 = 0
  have h_fbm' : flowNestingIx.go all_tokens.tokens 0 all_tokens.tokens.size 0 = 0 := h_fbm
  omega

/-! ## §5  Bridge `scanFilteredIx` to indexed PSV / brackets

Composes §4 with the §11k axioms
(`scan_flow_aware_psv_ix_axiom` / `scan_flow_brackets_matched_ix_axiom`
in `Proofs/Production/IndexedScannerPlainScalarValid.lean`). -/

/-- `scanFilteredIx` output satisfies `FlowAwarePSVIx`: the filter
    bridges `scan_flow_aware_psv_ix_axiom` (which proves the predicate
    on the unfiltered `scanIx` output) to the filtered token stream.
    Indexed twin of legacy `scanFiltered_flow_aware_psv`
    (`ParserWellBehaved.lean:304`) — except the legacy was a trivial
    wrapper because legacy `scan_flow_aware_psv` already operated on
    `scanFiltered`. -/
theorem scanFilteredIx_FlowAwarePSVIx
    (input : String) (tokens : Indexed.TokenStream input)
    (h_scan : scanFilteredIx input = .ok tokens) :
    FlowAwarePSVIx tokens := by
  unfold scanFilteredIx at h_scan
  split at h_scan
  · rename_i all_tokens h_scan_raw
    injection h_scan with h_eq
    subst h_eq
    exact filter_preserves_FlowAwarePSVIx all_tokens
      (scan_flow_aware_psv_ix_axiom all_tokens h_scan_raw)
  · contradiction

/-- `scanFilteredIx` output satisfies `FlowBracketsMatchedIx`. -/
theorem scanFilteredIx_FlowBracketsMatchedIx
    (input : String) (tokens : Indexed.TokenStream input)
    (h_scan : scanFilteredIx input = .ok tokens) :
    FlowBracketsMatchedIx tokens := by
  unfold scanFilteredIx at h_scan
  split at h_scan
  · rename_i all_tokens h_scan_raw
    injection h_scan with h_eq
    subst h_eq
    exact filter_preserves_FlowBracketsMatchedIx all_tokens
      (scan_flow_brackets_matched_ix_axiom all_tokens h_scan_raw)
  · contradiction

end L4YAML.Proofs.Indexed.ScannerCorrectness
