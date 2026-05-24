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

/-! ## §6  `ValidTokenStreamPropIx` and the four `scanIx_*` primitives

Indexed twin of legacy `ValidTokenStreamProp` (`Spec/Grammar.lean:419`)
and `scan_valid_token_stream` (`Proofs/Scanner/ScannerCorrectness.lean:9652`).

The four-conjunct shape is preserved verbatim. The legacy bound on token
positions (`pos.offset ≤ input.utf8ByteSize`) is implicit in the indexed
substrate via `IxToken.stopLEInput` (`start.offset ≤ stop.offset ≤
input.utf8ByteSize`) — that bound costs zero proof work. The four
`ValidTokenStreamProp` invariants (sizeGe2, streamStart, streamEnd,
positionsOrdered) still need explicit proofs.

**6f.3b3.primitives.tractable (this session)** discharges the two
*tractable* primitives — `scanIx_produces_at_least_two` and
`scanIx_last_is_streamEnd` — both proven directly from
`scanLoopIx_success_emits_streamEnd` (a new lightweight helper) plus
the existing `scanLoopIx_tokens_size_le` /
`unwindIndentsIx_tokens_size_le`. The two *intricate* primitives
(`scanIx_first_is_streamStart` and `scanIx_positions_ordered`) remain
as **narrower staging axioms** because each requires porting a
substantial scanner-state-invariant infrastructure
(`SimpleKeyAboveIx` + `scanLoopIx_preserves_tokens` for the first;
`ScanInvIx` + `AllKeysValidIx` + `scanLoopIx_ordered` for the second)
that is shared with the EmitterScannability migration's
`6f.3b3.internals` sub-step.

The composite theorem `scanIx_valid_token_stream` (replacing the
prior session's monolithic `scanIx_valid_token_stream_axiom` staging
axiom) is now a *theorem* composed of two discharged primitives plus
two narrower axioms — net reduction in staging-axiom surface from a
single coarse axiom to two precisely-scoped ones, mirroring the
6d.1e refactoring posture (Reflection 108). -/

/-- Indexed twin of `Spec/Grammar.lean:ValidTokenStreamProp`. The
    `input` parameter is implicit since `Indexed.TokenStream` carries
    it as a type-level dependency. The four conjuncts:
      1. `≥ 2` tokens (envelope: `streamStart` + `streamEnd`),
      2. First token is `streamStart`,
      3. Last token is `streamEnd`,
      4. Token start positions are monotonically non-decreasing. -/
def ValidTokenStreamPropIx {input : String} (tokens : Indexed.TokenStream input) : Prop :=
  tokens.tokens.size ≥ 2 ∧
  (∀ (h : 0 < tokens.tokens.size), (tokens.tokens[0]'h).token = YamlToken.streamStart) ∧
  (∀ (h : tokens.tokens.size - 1 < tokens.tokens.size),
      (tokens.tokens[tokens.tokens.size - 1]'h).token = YamlToken.streamEnd) ∧
  ∀ (i j : Fin tokens.tokens.size), i.val < j.val →
    (tokens.tokens[i]).start.offset ≤ (tokens.tokens[j]).start.offset

/-! ### §6.1  Helper: `scanLoopIx_success_emits_streamEnd`

Indexed twin of legacy `scanLoop_success_emits_streamEnd`
(`Proofs/Scanner/ScannerCorrectness.lean:316`). Every successful
`scanLoopIx` call returns a token stream of the form
`(s'.emit streamEnd).tokens` for some terminal state `s'` — because
the *only* success-returning arm of `scanLoopIx` is the terminal
`unwindIndentsIx + emit streamEnd` branch. -/

theorem scanLoopIx_success_emits_streamEnd {input : String} :
    ∀ (s : ScannerStateIx input) (fuel : Nat) (ts : Indexed.TokenStream input),
      scanLoopIx s fuel = .ok ts →
      ∃ (s' : ScannerStateIx input), ts = (s'.emit YamlToken.streamEnd).tokens := by
  intro s fuel
  induction fuel generalizing s with
  | zero =>
    intro ts h; unfold scanLoopIx at h; cases h
  | succ fuel' ih =>
    intro ts h
    unfold scanLoopIx at h
    cases hSc : scanNextTokenIx s with
    | error e => rw [hSc] at h; cases h
    | ok scRes =>
      rw [hSc] at h
      cases scRes with
      | none =>
        by_cases hFL : s.flowLevel > 0
        · rw [if_pos hFL] at h; cases h
        · rw [if_neg hFL] at h
          by_cases hDS : (s.directivesPresent && !s.documentEverStarted) = true
          · rw [if_pos hDS] at h; cases h
          · rw [if_neg hDS] at h
            cases h
            exact ⟨unwindIndentsIx s (-1), rfl⟩
      | some s'' => exact ih s'' ts h

/-! ### §6.2  Helper: `scanLoopIx_increases_tokens`

Strengthens `scanLoopIx_tokens_size_le` (`s.tokens.size ≤ ts.size`) to
`s.tokens.size + 1 ≤ ts.size`: the loop terminates with
`unwindIndentsIx + emit streamEnd`, and the `emit streamEnd` is
unconditional in the success arm — so at minimum +1 token is added,
regardless of how the recursive arms grew the stream. Indexed twin of
legacy `scanLoop_increases_tokens`
(`Proofs/Scanner/ScannerCorrectness.lean:6257`). -/

theorem scanLoopIx_increases_tokens {input : String}
    {s : ScannerStateIx input} {fuel : Nat} {ts : Indexed.TokenStream input}
    (h : scanLoopIx s fuel = .ok ts) :
    s.tokens.size + 1 ≤ ts.size := by
  induction fuel generalizing s with
  | zero => unfold scanLoopIx at h; cases h
  | succ fuel' ih =>
    unfold scanLoopIx at h
    cases hSc : scanNextTokenIx s with
    | error e => rw [hSc] at h; cases h
    | ok scRes =>
      rw [hSc] at h
      cases scRes with
      | none =>
        by_cases hFL : s.flowLevel > 0
        · rw [if_pos hFL] at h; cases h
        · rw [if_neg hFL] at h
          by_cases hDS : (s.directivesPresent && !s.documentEverStarted) = true
          · rw [if_pos hDS] at h; cases h
          · rw [if_neg hDS] at h
            cases h
            -- ts = ((unwindIndentsIx s (-1)).emit streamEnd).tokens
            show s.tokens.size + 1 ≤ _
            have h_unwind := unwindIndentsIx_tokens_size_le s (-1)
            -- (unwindIndentsIx s (-1)).emit streamEnd : push +1
            simp only [Indexed.TokenStream.size]
            show s.tokens.tokens.size + 1 ≤ ((unwindIndentsIx s (-1)).tokens.tokens.push _).size
            rw [Array.size_push]
            change _ ≤ _ at h_unwind
            simp only [Indexed.TokenStream.size] at h_unwind
            omega
      | some s'' =>
        have hStep := scanNextTokenIx_tokens_size_le hSc
        have hIH := ih h
        omega

/-! ### §6.3  Discharged primitive: `scanIx_produces_at_least_two`

Indexed twin of legacy `scan_produces_at_least_two`
(`Proofs/Scanner/ScannerCorrectness.lean:6304`). Composes
`scanLoopIx_increases_tokens` (the post-BOM state's `tokens.size + 1 ≤
tokens.size`) with the observation that the initial state after
`mk' |> emit streamStart` has `tokens.size = 1`. -/

theorem scanIx_produces_at_least_two {input : String}
    (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens) :
    tokens.tokens.size ≥ 2 := by
  unfold scanIx at h
  have h_inc := scanLoopIx_increases_tokens h
  -- Mirrors the legacy proof structure (`scan_produces_at_least_two`,
  -- `ScannerCorrectness.lean:6304`): `split` on the BOM match inside
  -- `h_inc`, then reduce each arm via `advance_tokens` + `emit_tokens_size`.
  show 2 ≤ tokens.tokens.size
  change _ ≤ tokens.size
  split at h_inc
  · -- some BOM arm: advance preserves tokens
    simp only [advance_tokens, emit_tokens_size] at h_inc
    exact h_inc
  · -- _ arm: tokens.size = ((mk').emit streamStart).tokens.size
    simp only [emit_tokens_size] at h_inc
    exact h_inc

/-! ### §6.3  Discharged primitive: `scanIx_last_is_streamEnd`

Indexed twin of legacy `scan_last_is_streamEnd`
(`Proofs/Scanner/ScannerCorrectness.lean:6413`). Composes
`scanLoopIx_success_emits_streamEnd` with `Array.getElem_push_eq`
(retrieving the last element of a pushed array). -/

theorem scanIx_last_is_streamEnd {input : String}
    (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens)
    (h_size : 0 < tokens.tokens.size) :
    (tokens.tokens[tokens.tokens.size - 1]'(by omega)).token = YamlToken.streamEnd := by
  unfold scanIx at h
  obtain ⟨s', h_tokens⟩ := scanLoopIx_success_emits_streamEnd _ _ _ h
  -- `subst` (not `rw`) so the dependent proof `h_size` is re-elaborated
  -- against `(s'.emit streamEnd).tokens.tokens.size` rather than left
  -- stranded with a stale `tokens` reference.
  subst h_tokens
  -- Mirrors legacy `scan_last_is_streamEnd` proof structure
  -- (`ScannerCorrectness.lean:6413`): `unfold emit`, then index = `size - 1`
  -- reduces via `Array.size_push`, then `Array.getElem_push` retrieves the
  -- pushed element whose `.token` is `streamEnd` by construction.
  -- Note: the indexed substrate inserts an extra `Indexed.TokenStream.push`
  -- between `emit` and the raw `Array.push`; unfolding `emit` alone leaves
  -- `(ts.push t).tokens.size` rather than `(ts.tokens.push t).size`. The
  -- first step is `rfl` (structural projection), so `show` (definitional)
  -- forces the goal into Array-level form before `Array.size_push` applies.
  unfold ScannerStateIx.emit
  show (((s'.tokens.tokens).push
          (IxToken.mk' (input := input) s'.cursor.pos YamlToken.streamEnd
            s'.cursor.pos (Nat.le_refl _) s'.cursor.posBound))[
        ((s'.tokens.tokens).push _).size - 1]'(by
          simp only [Array.size_push]; omega)).token = YamlToken.streamEnd
  simp only [Array.size_push]
  have h_idx : s'.tokens.tokens.size + 1 - 1 = s'.tokens.tokens.size := by omega
  simp [Array.getElem_push, h_idx]
  -- Remaining goal: the pushed `IxToken.mk' _ streamEnd _ _ _`'s `.token = streamEnd`.
  -- This is `rfl` since `IxToken.mk'` takes the second argument as the `.token` field.
  rfl

/-! ### §6.4  Staging axioms for the two intricate primitives

These two axioms scope precisely the work deferred to
`6f.3b3.primitives.streamStart` and `6f.3b3.primitives.ordered`
(see Blueprint). They replace the prior session's single coarse
`scanIx_valid_token_stream_axiom` with two precisely-scoped axioms
that each describe a *specific* conjunct of `ValidTokenStreamPropIx`.

The infrastructure each requires:

  - `scanIx_first_is_streamStart_axiom`: needs `SimpleKeyAboveIx`
    (indexed twin of legacy `SimpleKeyAbove`,
    `ScannerCorrectness.lean:6175`) and `scanLoopIx_preserves_tokens`
    (preservation of the first `n` tokens under simple-key-stack
    invariant).

  - `scanIx_positions_ordered_axiom`: needs `ScanInvIx` and
    `AllKeysValidIx` (indexed twins of legacy `ScanInv` /
    `AllKeysValid`, `ScannerCorrectness.lean:8745` / `:8983`) plus
    `scanLoopIx_ordered` (induction on fuel proving positionsOrdered
    through the loop).

Both infrastructures are also prerequisites for the EmitterScannability
indexed twin's per-step preservation lemmas — so the work is *amortized*
when ported at 6f.3b3.internals. See Reflection 108. -/

-- Note: the former `scanIx_first_is_streamStart_axiom` is now
-- *discharged* as a theorem in §7.9 below. The composite
-- `scanIx_valid_token_stream` (now in §7.10) references that theorem
-- directly. Only the positions-ordered axiom remains in §6.4.

/-- **Staging axiom** for the positions-monotonic-on-start.offset
    conjunct. Scheduled for discharge at
    `6f.3b3.primitives.ordered`. -/
axiom scanIx_positions_ordered_axiom
    {input : String} (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens) :
    ∀ (i j : Fin tokens.tokens.size), i.val < j.val →
      (tokens.tokens[i]).start.offset ≤ (tokens.tokens[j]).start.offset

/-! ### §6.5  Composite theorem `scanIx_valid_token_stream` (moved to §7.10)

The composite `scanIx_valid_token_stream` is defined in §7.10 below
(after `scanIx_first_is_streamStart` is discharged as a theorem in
§7.9). The downstream consumer in
`IndexedGrammable.parseYamlIx_implies_valid_token_stream` references
the §7.10 theorem. -/

/-! ## §7  `SimpleKeyAboveIx` and `scanIx_first_is_streamStart`

Discharges the §6.4 staging axiom `scanIx_first_is_streamStart_axiom`
by porting the legacy `SimpleKeyAbove` invariant and the chain
`scanLoop_preserves_tokens` from
`Proofs/Scanner/ScannerCorrectness.lean:6175–6401`.

### Strategy

`overwriteAtCursor i sk tok` is the *only* operation in the indexed
scanner that mutates an existing slot in `tokens.tokens` (everything
else only `push`es). It is invoked from `scanValuePrepareIx` at
positions `s.simpleKey.tokenIndex` and `s.simpleKey.tokenIndex + 1`.
Therefore, if every simple key (current or stacked) has
`tokenIndex ≥ n`, then no `overwriteAtCursor` writes below index `n`,
so the prefix below `n` is preserved through `scanLoopIx`. With
`n = 1`, that prefix is exactly `[streamStart]`.

The composition mirrors the §12l `AllKeysPlaceholderInvIx`
dispatcher chain in `IndexedScannerPlainScalarValid.lean`: the
per-helper `_preserves_simpleKey` / `_preserves_simpleKeyStack` /
`_clears_simpleKey` / `_simpleKey_restored` / `_stack_pushed` /
`_stack_popped` facts compose with `_preserves_prefix` to maintain
`SimpleKeyAboveIx`. Most helpers preserve the *entire* prefix
unconditionally (`emit`-only); only `scanValueIx` requires the
`tokenIndex ≥ n` bound (it calls `scanValuePrepareIx`). -/

/-! ### §7.1  Definition -/

/-- Simple-key invariant: every simple key (current or stacked) with
    `possible = true` has `tokenIndex ≥ n`. Indexed twin of legacy
    `SimpleKeyAbove` (`Proofs/Scanner/ScannerCorrectness.lean:81`).

    `SimpleKeyAboveIx` does not depend on `s.tokens` directly, only on
    `s.simpleKey` and `s.simpleKeyStack` — so mono / cleared / restored
    transfers are by destructured projection (no `tokens` precondition
    required). The `n ≤ s.tokens.size` precondition is threaded
    separately at the call sites that need it (`saveSimpleKeyIx` is
    the only operation that bumps `tokenIndex` from `tokens.size`). -/
def SimpleKeyAboveIx {input : String} (s : ScannerStateIx input) (n : Nat) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
  (∀ j (hj : j < s.simpleKeyStack.size),
    (s.simpleKeyStack[j]'hj).possible = true → (s.simpleKeyStack[j]'hj).tokenIndex ≥ n)

/-! ### §7.2  Mono helpers

`SimpleKeyAboveIx_mono` covers any state transition where `simpleKey`
and `simpleKeyStack` are both unchanged (only `tokens`, `cursor`, or
flag fields differ). `_of_cleared_mono` covers transitions where
`simpleKey.possible` becomes `false` and the stack is unchanged.
`_flowStart` / `_flowEnd` cover the flow-collection bracket
transitions that push/pop the stack. -/

theorem SimpleKeyAboveIx_mono {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => ?_, fun j hj h_poss_j => ?_⟩
  · rw [h_sk] at h_poss ⊢; exact h_inv.1 h_poss
  · have hj' : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
    have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj') := by simp [h_stack]
    rw [h_get] at h_poss_j ⊢
    exact h_inv.2 j hj' h_poss_j

theorem SimpleKeyAboveIx_of_cleared_mono {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_cleared : s'.simpleKey.possible = false)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => absurd h_poss (by simp [h_cleared]), fun j hj h_poss_j => ?_⟩
  have hj' : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj') := by simp [h_stack]
  rw [h_get] at h_poss_j ⊢
  exact h_inv.2 j hj' h_poss_j

/-- Flow start (`[`, `{`) clears current key and pushes old key onto
    the stack — both invariants transfer. -/
theorem SimpleKeyAboveIx_flowStart {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_cleared : s'.simpleKey.possible = false)
    (h_pushed : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => absurd h_poss (by simp [h_cleared]), fun j hj h_poss_j => ?_⟩
  have hj_sz : j < s.simpleKeyStack.size + 1 := by
    rw [h_pushed, Array.size_push] at hj; exact hj
  have hg_j : s'.simpleKeyStack[j]'hj =
      (s.simpleKeyStack.push s.simpleKey)[j]'(by rw [Array.size_push]; exact hj_sz) := by
    simp [h_pushed]
  rw [hg_j] at h_poss_j ⊢
  by_cases hlt : j < s.simpleKeyStack.size
  · rw [Array.getElem_push_lt hlt] at h_poss_j ⊢
    exact h_inv.2 j hlt h_poss_j
  · have hj_eq : j = s.simpleKeyStack.size := by omega
    subst hj_eq
    rw [Array.getElem_push_eq] at h_poss_j ⊢
    exact h_inv.1 h_poss_j

/-- Flow end (`]`, `}`) restores current key from stack top and pops.
    The restored key was on the stack, so its invariant was already
    established; the popped stack is a prefix of the old stack. -/
theorem SimpleKeyAboveIx_flowEnd {input : String} (s s' : ScannerStateIx input) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_restored : s'.simpleKey =
      s.simpleKeyStack.back?.getD { cursor := IxCursor.start input })
    (h_popped : s'.simpleKeyStack = s.simpleKeyStack.pop) :
    SimpleKeyAboveIx s' n := by
  refine ⟨fun h_poss => ?_, fun j hj h_poss_j => ?_⟩
  · rw [h_restored] at h_poss ⊢
    by_cases h_size : s.simpleKeyStack.size > 0
    · have h_bound : s.simpleKeyStack.size - 1 < s.simpleKeyStack.size := by omega
      have h_get_back :
          (s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }) =
          s.simpleKeyStack[s.simpleKeyStack.size - 1]'h_bound := by
        simp [Array.back?, h_bound]
      rw [h_get_back] at h_poss ⊢
      exact h_inv.2 (s.simpleKeyStack.size - 1) h_bound h_poss
    · have h_empty : s.simpleKeyStack.size = 0 := by omega
      simp [Array.back?, h_empty] at h_poss
  · have hj' : j < s.simpleKeyStack.size := by
      simp [h_popped, Array.size_pop] at hj; omega
    have hg_j : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj' := by
      simp [h_popped, Array.getElem_pop]
    rw [hg_j] at h_poss_j ⊢
    exact h_inv.2 j hj' h_poss_j

/-! ### §7.3  `saveSimpleKeyIx` maintains `SimpleKeyAboveIx`

`saveSimpleKeyIx` either returns `s` unchanged (case 1 of
`saveSimpleKeyIx_state_cases`) or pushes two placeholder tokens and
sets the new simple key to `{ possible := true, tokenIndex :=
s.tokens.size, ... }` (case 2). In the latter case,
`tokens.size ≥ n` (precondition) guarantees the new key's
`tokenIndex ≥ n`, and the stack is unchanged (`emit`-only). -/

theorem saveSimpleKeyIx_maintains_SimpleKeyAboveIx {input : String}
    (s : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n) :
    SimpleKeyAboveIx (saveSimpleKeyIx s) n := by
  rcases saveSimpleKeyIx_state_cases s with h_eq | h_eq
  · rw [h_eq]; exact h_inv
  · rw [h_eq]
    refine ⟨fun _h_poss => ?_, fun j hj h_poss_j => ?_⟩
    · -- new simpleKey.tokenIndex = s.tokens.size ≥ n
      exact h_n
    · -- stack unchanged: two emits, both `emit_preserves_simpleKeyStack`
      have h_stack_eq :
          ({ (s.emit YamlToken.placeholder).emit YamlToken.placeholder with
              simpleKey := { possible := true, tokenIndex := s.tokens.size,
                             cursor := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor,
                             endLine := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor.pos.line } }
                : ScannerStateIx input).simpleKeyStack = s.simpleKeyStack := by
        show ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack =
          s.simpleKeyStack
        rw [emit_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]
      have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack_eq]; exact hj
      have h_get :
          ({ (s.emit YamlToken.placeholder).emit YamlToken.placeholder with
              simpleKey := { possible := true, tokenIndex := s.tokens.size,
                             cursor := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor,
                             endLine := ((s.emit YamlToken.placeholder).emit
                               YamlToken.placeholder).cursor.pos.line } }
                : ScannerStateIx input).simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj_s := by
        simp
      rw [h_get] at h_poss_j ⊢
      exact h_inv.2 j hj_s h_poss_j

/-! ### §7.4  Preprocess maintains `SimpleKeyAboveIx`

`scanNextTokenIx_preprocess` does: `skipToContentS` → optional
`unwindIndentsIx` (under `needIndentCheck`) → `saveSimpleKeyIx`.
None of `skipToContentS` / `unwindIndentsIx` touch `simpleKey` or
`simpleKeyStack` (mono case); `saveSimpleKeyIx` requires the
`n ≤ tokens.size` bound, which is monotone through the preceding
steps. -/

theorem scanNextTokenIx_preprocess_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c)))
    (h_inv : SimpleKeyAboveIx s n) :
    SimpleKeyAboveIx s' n := by
  have h_inv_skip : SimpleKeyAboveIx s.skipToContentS n :=
    SimpleKeyAboveIx_mono s s.skipToContentS n h_inv
      (skipToContentS_preserves_simpleKey s) (skipToContentS_preserves_simpleKeyStack s)
  have h_n_skip : n ≤ s.skipToContentS.tokens.size := by
    rw [show s.skipToContentS.tokens.size = s.tokens.size from by simp [skipToContentS_tokens]]
    exact h_n
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- with indent check
      have h_unwind_sk :
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).simpleKey =
          s.skipToContentS.simpleKey := unwindIndentsIx_preserves_simpleKey _ _
      have h_unwind_stack :
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).simpleKeyStack =
          s.skipToContentS.simpleKeyStack := unwindIndentsIx_preserves_simpleKeyStack _ _
      have h_unwind_mono :
          s.skipToContentS.tokens.size ≤
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens.size :=
        unwindIndentsIx_tokens_size_le _ _
      have h_inv_unwind : SimpleKeyAboveIx
          { unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
              needIndentCheck := false } n :=
        SimpleKeyAboveIx_mono s.skipToContentS _ n h_inv_skip h_unwind_sk h_unwind_stack
      have h_n_unwind : n ≤
          ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
              needIndentCheck := false } : ScannerStateIx input).tokens.size := by
        show n ≤ (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens.size
        omega
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_maintains_SimpleKeyAboveIx _ n h_n_unwind h_inv_unwind
    · -- without indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_maintains_SimpleKeyAboveIx _ n h_n_skip h_inv_skip

/-! ### §7.5  Sub-dispatcher maintains lemmas

Each of the four `scanNextTokenIx_dispatch*` sub-dispatchers preserves
`SimpleKeyAboveIx` via the case-enumeration theorems in
`Proofs/Scanner/IndexedDispatch.lean` and the per-helper
`_preserves_simpleKey` / `_clears_simpleKey` / `_simpleKey_restored` /
`_stack_pushed` / `_stack_popped` facts in `IndexedScannerPlainScalarValid`. -/

theorem scanNextTokenIx_dispatchStructural_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ok with heq | hOk | hOk
  · subst heq
    exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanDocumentStartIx_clears_simpleKey s)
      (scanDocumentStartIx_preserves_simpleKeyStack s)
  · exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanDocumentEndIx_clears_simpleKey s s' hOk)
      (scanDocumentEndIx_preserves_simpleKeyStack s s' hOk)
  · exact SimpleKeyAboveIx_mono s _ n h_inv
      (scanDirectiveIx_preserves_simpleKey s s' hOk)
      (scanDirectiveIx_preserves_simpleKeyStack s s' hOk)

theorem scanNextTokenIx_dispatchFlowIndicators_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_ok with
    heq | heq | heq | heq | hOk
  · subst heq
    exact SimpleKeyAboveIx_flowStart s _ n h_inv
      (scanFlowSequenceStartIx_simpleKey_cleared s)
      (scanFlowSequenceStartIx_stack_pushed s)
  · subst heq
    exact SimpleKeyAboveIx_flowEnd s _ n h_inv
      (scanFlowSequenceEndIx_simpleKey_restored s)
      (scanFlowSequenceEndIx_stack_popped s)
  · subst heq
    exact SimpleKeyAboveIx_flowStart s _ n h_inv
      (scanFlowMappingStartIx_simpleKey_cleared s)
      (scanFlowMappingStartIx_stack_pushed s)
  · subst heq
    exact SimpleKeyAboveIx_flowEnd s _ n h_inv
      (scanFlowMappingEndIx_simpleKey_restored s)
      (scanFlowMappingEndIx_stack_popped s)
  · -- scanFlowEntryIx preserves simpleKey + simpleKeyStack (Step 6f.0)
    exact SimpleKeyAboveIx_mono s _ n h_inv
      (scanFlowEntryIx_preserves_simpleKey s s' hOk)
      (scanFlowEntryIx_preserves_simpleKeyStack s s' hOk)

theorem scanNextTokenIx_dispatchBlockIndicators_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_ok with hOk | hOk | hOk
  · -- scanBlockEntryIx: preserves
    exact SimpleKeyAboveIx_mono s _ n h_inv
      (scanBlockEntryIx_preserves_simpleKey s s' hOk)
      (scanBlockEntryIx_preserves_simpleKeyStack s s' hOk)
  · -- scanKeyIx: clears + preserves stack
    exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanKeyIx_clears_simpleKey s s' hOk)
      (scanKeyIx_preserves_simpleKeyStack s s' hOk)
  · -- scanValueIx: clears + preserves stack
    exact SimpleKeyAboveIx_of_cleared_mono s _ n h_inv
      (scanValueIx_clears_simpleKey s s' hOk)
      (scanValueIx_preserves_simpleKeyStack s s' hOk)

theorem scanNextTokenIx_dispatchContent_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s') :
    SimpleKeyAboveIx s' n := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '&': anchor
    generalize h_anch : scanAnchorOrAliasIx s true = anch_result at h_ok
    cases anch_result with
    | error e => simp at h_ok
    | ok s_anch =>
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact SimpleKeyAboveIx_mono s s_anch n h_inv
        (scanAnchorOrAliasIx_preserves_simpleKey s true s_anch h_anch)
        (scanAnchorOrAliasIx_preserves_simpleKeyStack s true s_anch h_anch)
  · split at h_ok
    · -- c == '*': alias
      generalize h_anch : scanAnchorOrAliasIx s false = anch_result at h_ok
      cases anch_result with
      | error e => simp at h_ok
      | ok s_anch =>
        dsimp only [] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact SimpleKeyAboveIx_mono s s_anch n h_inv
          (scanAnchorOrAliasIx_preserves_simpleKey s false s_anch h_anch)
          (scanAnchorOrAliasIx_preserves_simpleKeyStack s false s_anch h_anch)
    · split at h_ok
      · -- c == '!': tag
        generalize h_tag : scanTagIx s = tag_result at h_ok
        cases tag_result with
        | error e => simp at h_ok
        | ok s_tag =>
          dsimp only [] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact SimpleKeyAboveIx_mono s s_tag n h_inv
            (scanTagIx_preserves_simpleKey s s_tag h_tag)
            (scanTagIx_preserves_simpleKeyStack s s_tag h_tag)
      · split at h_ok
        · -- c == '|' || c == '>': block scalar (inline)
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok
            subst h_ok
            exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
          · simp at h_ok
        · split at h_ok
          · -- c == '"': double quoted
            split at h_ok
            · simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
            · simp at h_ok
          · split at h_ok
            · -- c == '\'': single quoted
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
              · simp at h_ok
            · split at h_ok
              · -- plain scalar
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact SimpleKeyAboveIx_mono s _ n h_inv (by simp) (by simp)
              · simp at h_ok

/-! ### §7.6  `scanNextTokenIx` maintains `SimpleKeyAboveIx`

Composes preprocess (§7.4) with the four sub-dispatcher maintains
lemmas (§7.5) and the `allowDirectives` record update (which
preserves both `simpleKey` and `simpleKeyStack` by mono). -/

theorem scanNextTokenIx_maintains_SimpleKeyAboveIx {input : String}
    (s s' : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    SimpleKeyAboveIx s' n := by
  unfold scanNextTokenIx at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h_ok
  cases pp_res with
  | error e => simp at h_ok
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h_ok
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_inv_pp : SimpleKeyAboveIx s_pp n :=
          scanNextTokenIx_preprocess_maintains_SimpleKeyAboveIx s s_pp c n h_n h_pp h_inv
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            exact scanNextTokenIx_dispatchStructural_maintains_SimpleKeyAboveIx
              s_pp s_str c n h_inv_pp h_ds
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_inv_dir : SimpleKeyAboveIx s_dir n := by
              rw [← h_dir_def]
              split
              · exact SimpleKeyAboveIx_mono s_pp _ n h_inv_pp rfl rfl
              · exact h_inv_pp
            generalize h_ck : scanNextTokenIx_checkBlockFlowIndent s_dir c = ck_res at h_ok
            cases ck_res with
            | error e => simp at h_ok
            | ok _ =>
              dsimp only [] at h_ok
              generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h_ok
              cases df_res with
              | error e => simp at h_ok
              | ok df_inner =>
                cases df_inner with
                | some s_flow =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                  subst h_ok
                  exact scanNextTokenIx_dispatchFlowIndicators_maintains_SimpleKeyAboveIx
                    s_dir s_flow c n h_inv_dir h_df
                | none =>
                  dsimp only [] at h_ok
                  generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h_ok
                  cases db_res with
                  | error e => simp at h_ok
                  | ok db_inner =>
                    cases db_inner with
                    | some s_blk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                      subst h_ok
                      exact scanNextTokenIx_dispatchBlockIndicators_maintains_SimpleKeyAboveIx
                        s_dir s_blk c n h_inv_dir h_db
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        exact scanNextTokenIx_dispatchContent_maintains_SimpleKeyAboveIx
                          s_dir s_ct c n h_inv_dir h_dc

/-! ### §7.7  Per-helper preserves-prefix-below-n

The existing `_preserves_prefix` lemmas in
`IndexedScannerPlainScalarValid.lean` are bound-by-`s.tokens.size`
(preserve the entire prefix unconditionally, or — for `scanValueIx` —
preserve below `n` given the simple-key bound). They use
`Indexed.TokenStream`'s `GetElem` instance (`s.tokens[i]`), which is
the form we adopt throughout §7.7–§7.9.

`scanNextTokenIx_dispatchContent` does not have a packaged
`_preserves_prefix` lemma in `IndexedScannerPlainScalarValid.lean`,
so we build it here by case-splitting through each `c` branch of the
dispatcher. Each content branch only `emit`-pushes a token (scalars,
anchors, tags) and so preserves the entire prefix. -/

theorem _inline_scalar_preserves_prefix {input : String}
    (s : ScannerStateIx input) (cAfter : IxCursor input)
    (startPos : YamlPos) (tok : YamlToken)
    (hBound : startPos.offset ≤ cAfter.pos.offset)
    (i : Nat) (h_bound : i < s.tokens.size) :
    ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
        simpleKeyAllowed := false } : ScannerStateIx input).tokens[i]'(by
          show i <
            (({ s with cursor := cAfter } : ScannerStateIx input).emitAt
              startPos tok hBound).tokens.size
          rw [ScannerPlainScalarValid.emitAt_tokens_size]
          have h_eq : ({ s with cursor := cAfter : ScannerStateIx input}).tokens.size =
            s.tokens.size := rfl
          omega) = s.tokens[i]'h_bound := by
  -- record-update on simpleKeyAllowed is rfl on .tokens; emitAt preserves prefix.
  show (({ s with cursor := cAfter } : ScannerStateIx input).emitAt
    startPos tok hBound).tokens[i]'_ = s.tokens[i]'h_bound
  show (({ s with cursor := cAfter } : ScannerStateIx input).tokens.tokens.push
    (IxToken.mk' startPos tok cAfter.pos hBound cAfter.posBound))[i]'_ =
      s.tokens.tokens[i]'h_bound
  exact Array.getElem_push_lt h_bound

theorem scanNextTokenIx_dispatchContent_preserves_prefix {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by
      have := scanNextTokenIx_dispatchContent_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '&'
    generalize h_anch : scanAnchorOrAliasIx s true = anch_result at h_ok
    cases anch_result with
    | error e => simp at h_ok
    | ok s_anch =>
      dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact scanAnchorOrAliasIx_preserves_prefix s true s_anch h_anch i h_bound
  · split at h_ok
    · -- c == '*'
      generalize h_anch : scanAnchorOrAliasIx s false = anch_result at h_ok
      cases anch_result with
      | error e => simp at h_ok
      | ok s_anch =>
        dsimp only [] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact scanAnchorOrAliasIx_preserves_prefix s false s_anch h_anch i h_bound
    · split at h_ok
      · -- c == '!'
        generalize h_tag : scanTagIx s = tag_result at h_ok
        cases tag_result with
        | error e => simp at h_ok
        | ok s_tag =>
          dsimp only [] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact scanTagIx_preserves_prefix s s_tag h_tag i h_bound
      · split at h_ok
        · -- block scalar
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok
            subst h_ok
            exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
          · simp at h_ok
        · split at h_ok
          · -- double quoted
            split at h_ok
            · simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
            · simp at h_ok
          · split at h_ok
            · -- single quoted
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
              · simp at h_ok
            · split at h_ok
              · -- plain scalar
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact _inline_scalar_preserves_prefix s _ _ _ _ i h_bound
              · simp at h_ok

/-! ### §7.7'  `scanNextTokenIx_preserves_prefix` (composed)

Combines preprocess prefix-preservation with the four sub-dispatcher
preserves-prefix lemmas. Most sub-dispatchers preserve the *entire*
prefix (their helpers only `emit`); only `scanValueIx` requires the
`SimpleKeyAboveIx` bound.

Spec uses `Indexed.TokenStream`'s `GetElem` instance, with the
original bound provided explicitly via `Nat.lt_of_lt_of_le` (omega
does not see through the `.size = .tokens.size` defeq). -/

theorem _preprocess_preserves_prefix {input : String}
    (s s' : ScannerStateIx input) (c : Char) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c)))
    (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
  -- skipToContentS preserves tokens (cursor-only update).
  have h_skip_tok : s.skipToContentS.tokens = s.tokens := skipToContentS_tokens s
  have h_i_skip : i < s.skipToContentS.tokens.size := by rw [h_skip_tok]; exact h_orig
  have h_skip_eq :
      s.skipToContentS.tokens[i]'h_i_skip = s.tokens[i]'h_orig := by
    have : ∀ (h : i < s.tokens.size),
        s.skipToContentS.tokens[i]'(h_skip_tok ▸ h) = s.tokens[i]'h := by
      intro h; congr 1
    exact this h_orig
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- branch 1: with indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          -- s_mid := { unwindIndentsIx ... with needIndentCheck := false }
          have h_mid_tok :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input).tokens =
              (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens := rfl
          have h_unwind_sz := unwindIndentsIx_tokens_size_le s.skipToContentS
            s.skipToContentS.cursor.pos.col
          have h_skip_sz_eq : s.skipToContentS.tokens.size = s.tokens.size := by
            rw [h_skip_tok]
          have h_i_mid : i <
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input).tokens.size := by
            rw [h_mid_tok]; omega
          have h_mid_eq :
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input).tokens[i]'h_i_mid =
              s.tokens[i]'h_orig := by
            rw [show
                ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                    needIndentCheck := false } : ScannerStateIx input).tokens[i]'h_i_mid =
                  (unwindIndentsIx s.skipToContentS
                    s.skipToContentS.cursor.pos.col).tokens[i]'(h_mid_tok ▸ h_i_mid) from
                by congr 1]
            rw [unwindIndentsIx_preserves_prefix s.skipToContentS
                  s.skipToContentS.cursor.pos.col i h_i_skip]
            exact h_skip_eq
          have h_save_sz := saveSimpleKeyIx_tokens_size_le
            ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                needIndentCheck := false } : ScannerStateIx input)
          have h_i_save : i < (saveSimpleKeyIx
              ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                  needIndentCheck := false } : ScannerStateIx input)).tokens.size := by omega
          refine ⟨h_i_save, ?_⟩
          rw [saveSimpleKeyIx_preserves_prefix
            ({ unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
                needIndentCheck := false } : ScannerStateIx input) i h_i_mid]
          exact h_mid_eq
    · -- branch 2: without indent check
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          have h_save_sz := saveSimpleKeyIx_tokens_size_le s.skipToContentS
          have h_i_save : i < (saveSimpleKeyIx s.skipToContentS).tokens.size := by omega
          refine ⟨h_i_save, ?_⟩
          rw [saveSimpleKeyIx_preserves_prefix s.skipToContentS i h_i_skip]
          exact h_skip_eq

theorem _dir_update_tokens {input : String} (s_pp : ScannerStateIx input) :
    (if s_pp.allowDirectives = true then
        { s_pp with allowDirectives := false, documentEverStarted := true }
      else s_pp).tokens = s_pp.tokens := by
  split <;> rfl

theorem scanNextTokenIx_preserves_prefix {input : String}
    (s s' : ScannerStateIx input) (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveIx s n)
    (h_ok : scanNextTokenIx s = .ok (some s'))
    (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < s'.tokens.size),
      s'.tokens[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
  unfold scanNextTokenIx at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  generalize h_pp : scanNextTokenIx_preprocess s = pp_res at h_ok
  cases pp_res with
  | error e => simp at h_ok
  | ok pp_inner =>
    cases pp_inner with
    | none => simp at h_ok
    | some pair =>
      cases pair with
      | mk s_pp c =>
        have h_inv_pp : SimpleKeyAboveIx s_pp n :=
          scanNextTokenIx_preprocess_maintains_SimpleKeyAboveIx s s_pp c n h_n h_pp h_inv
        obtain ⟨h_i_pp, h_pre_eq⟩ := _preprocess_preserves_prefix s s_pp c n h_n h_pp i h_i
        have h_n_pp : n ≤ s_pp.tokens.size :=
          Nat.le_trans h_n (scanNextTokenIx_preprocess_tokens_size_le h_pp)
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ds with heq | hOk | hOk
            · subst heq
              have h_pref := scanDocumentStartIx_preserves_prefix s_pp i h_i_pp
              have h_sz : i < (scanDocumentStartIx s_pp).tokens.size := by
                have := scanDocumentStartIx_tokens_size_le s_pp; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDocumentEndIx_preserves_prefix s_pp _ hOk i h_i_pp
              have h_sz : i < s_str.tokens.size := by
                have := scanDocumentEndIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
            · have h_pref := scanDirectiveIx_preserves_prefix s_pp _ hOk i h_i_pp
              have h_sz : i < s_str.tokens.size := by
                have := scanDirectiveIx_tokens_size_le hOk; omega
              exact ⟨h_sz, h_pref.trans h_pre_eq⟩
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_dir_tok : s_dir.tokens = s_pp.tokens := by
              rw [← h_dir_def]; exact _dir_update_tokens s_pp
            have h_i_dir : i < s_dir.tokens.size := by rw [h_dir_tok]; exact h_i_pp
            have h_dir_eq : s_dir.tokens[i]'h_i_dir = s_pp.tokens[i]'h_i_pp := by
              have : ∀ (h : i < s_pp.tokens.size),
                  s_dir.tokens[i]'(h_dir_tok ▸ h) = s_pp.tokens[i]'h := by
                intro h; congr 1
              exact this h_i_pp
            have h_inv_dir : SimpleKeyAboveIx s_dir n := by
              rw [← h_dir_def]
              split
              · exact SimpleKeyAboveIx_mono s_pp _ n h_inv_pp rfl rfl
              · exact h_inv_pp
            generalize h_ck : scanNextTokenIx_checkBlockFlowIndent s_dir c = ck_res at h_ok
            cases ck_res with
            | error e => simp at h_ok
            | ok _ =>
              dsimp only [] at h_ok
              generalize h_df : scanNextTokenIx_dispatchFlowIndicators s_dir c = df_res at h_ok
              cases df_res with
              | error e => simp at h_ok
              | ok df_inner =>
                cases df_inner with
                | some s_flow =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                  subst h_ok
                  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_df with
                    heq | heq | heq | heq | hOk
                  · subst heq
                    have h_pref := scanFlowSequenceStartIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowSequenceStartIx s_dir).tokens.size := by
                      have := scanFlowSequenceStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowSequenceEndIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowSequenceEndIx s_dir).tokens.size := by
                      have := scanFlowSequenceEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingStartIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowMappingStartIx s_dir).tokens.size := by
                      have := scanFlowMappingStartIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · subst heq
                    have h_pref := scanFlowMappingEndIx_preserves_prefix s_dir i h_i_dir
                    have h_sz : i < (scanFlowMappingEndIx s_dir).tokens.size := by
                      have := scanFlowMappingEndIx_tokens_size_le s_dir; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                  · have h_pref := scanFlowEntryIx_preserves_prefix s_dir s_flow hOk i h_i_dir
                    have h_sz : i < s_flow.tokens.size := by
                      have := scanFlowEntryIx_tokens_size_le hOk; omega
                    exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                | none =>
                  dsimp only [] at h_ok
                  generalize h_db : scanNextTokenIx_dispatchBlockIndicators s_dir c = db_res at h_ok
                  cases db_res with
                  | error e => simp at h_ok
                  | ok db_inner =>
                    cases db_inner with
                    | some s_blk =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                      subst h_ok
                      have h_n_dir : n ≤ s_dir.tokens.size := by rw [h_dir_tok]; exact h_n_pp
                      rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_db with
                        hOk | hOk | hOk
                      · have h_pref := scanBlockEntryIx_preserves_prefix s_dir s_blk hOk i h_i_dir
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanBlockEntryIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · have h_pref := scanKeyIx_preserves_prefix s_dir s_blk hOk i h_i_dir
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanKeyIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                      · -- scanValueIx: bounded form requires SimpleKeyAboveIx
                        have h_pref := scanValueIx_preserves_prefix s_dir s_blk hOk n h_n_dir
                          h_inv_dir.1 i h_i
                        have h_sz : i < s_blk.tokens.size := by
                          have := scanValueIx_tokens_size_le hOk; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        have h_pref :=
                          scanNextTokenIx_dispatchContent_preserves_prefix s_dir s_ct c h_dc i h_i_dir
                        have h_sz : i < s_ct.tokens.size := by
                          have := scanNextTokenIx_dispatchContent_tokens_size_le h_dc; omega
                        exact ⟨h_sz, h_pref.trans (h_dir_eq.trans h_pre_eq)⟩

/-! ### §7.8  `scanLoopIx_preserves_tokens` (fuel induction)

Indexed twin of legacy `scanLoop_preserves_tokens` (`Proofs/Scanner/
ScannerCorrectness.lean:6197`). Proven by induction on fuel:

  - Base (`fuel = 0`): `scanLoopIx` returns `.error`, contradicting `.ok`.
  - Recursive step (`fuel = fuel'+1`): split on `scanNextTokenIx`.
    - Terminal (`.ok none` branch into final `unwindIndentsIx + emit
      streamEnd`): use `unwindIndentsIx_preserves_prefix` + emit.
    - Recursive (`.ok (some s')`): combine
      `scanNextTokenIx_preserves_prefix` +
      `scanNextTokenIx_maintains_SimpleKeyAboveIx` + IH. -/

theorem scanLoopIx_preserves_tokens {input : String}
    (s : ScannerStateIx input) (fuel : Nat) (ts : Indexed.TokenStream input)
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAboveIx s n)
    (h : scanLoopIx s fuel = .ok ts) (i : Nat) (h_i : i < n) :
    ∃ (h_size : i < ts.size),
      ts[i]'h_size = s.tokens[i]'(Nat.lt_of_lt_of_le h_i h_n) := by
  have h_orig : i < s.tokens.size := Nat.lt_of_lt_of_le h_i h_n
  induction fuel generalizing s with
  | zero => unfold scanLoopIx at h; cases h
  | succ fuel' ih =>
    unfold scanLoopIx at h
    cases hSc : scanNextTokenIx s with
    | error e => rw [hSc] at h; cases h
    | ok scRes =>
      rw [hSc] at h
      cases scRes with
      | none =>
        by_cases hFL : s.flowLevel > 0
        · rw [if_pos hFL] at h; cases h
        · rw [if_neg hFL] at h
          by_cases hDS : (s.directivesPresent && !s.documentEverStarted) = true
          · rw [if_pos hDS] at h; cases h
          · rw [if_neg hDS] at h
            cases h
            -- ts = ((unwindIndentsIx s (-1)).emit streamEnd).tokens
            have h_unwind_sz := unwindIndentsIx_tokens_size_le s (-1)
            have h_i_unwind : i < (unwindIndentsIx s (-1)).tokens.size := by omega
            have h_emit_sz :
                ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens.size =
                (unwindIndentsIx s (-1)).tokens.size + 1 :=
              emit_tokens_size (unwindIndentsIx s (-1)) .streamEnd
            have h_i_emit : i <
                ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens.size := by
              rw [h_emit_sz]; omega
            refine ⟨h_i_emit, ?_⟩
            calc ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens[i]'h_i_emit
                = (unwindIndentsIx s (-1)).tokens[i]'h_i_unwind :=
                    emit_preserves_tokens_at (unwindIndentsIx s (-1)) .streamEnd i h_i_unwind
              _ = s.tokens[i]'h_orig :=
                    unwindIndentsIx_preserves_prefix s (-1) i h_orig
      | some s'' =>
        have h_step := scanNextTokenIx_tokens_size_le hSc
        have h_inv_step := scanNextTokenIx_maintains_SimpleKeyAboveIx s s'' n h_n h_inv hSc
        have h_n_step : n ≤ s''.tokens.size := by omega
        obtain ⟨h_i_step, h_pre_eq⟩ :=
          scanNextTokenIx_preserves_prefix s s'' n h_n h_inv hSc i h_i
        -- IH binds `i < s''.tokens.size` as an extra parameter after generalization
        -- (the existential's RHS bound depends on `h_n` which was generalized).
        have h_orig_step : i < s''.tokens.size := Nat.lt_of_lt_of_le h_i h_n_step
        obtain ⟨h_i_ts, h_ts_eq⟩ := ih s'' h_n_step h_inv_step h h_orig_step
        exact ⟨h_i_ts, h_ts_eq.trans h_pre_eq⟩

/-! ### §7.9  `scanIx_first_is_streamStart` — discharge of §6.4 axiom

After `(mk' input).emit streamStart`, `tokens.size = 1` and
`tokens[0].token = streamStart`. The optional BOM advance preserves
both. Both states satisfy `SimpleKeyAboveIx _ 1` vacuously
(`simpleKey.possible = false`, `simpleKeyStack` empty). Applying
`scanLoopIx_preserves_tokens` with `n = 1` and `i = 0` gives that
`tokens[0]` is preserved through the loop. -/

theorem scanIx_first_is_streamStart {input : String}
    (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens)
    (h_size : 0 < tokens.tokens.size) :
    (tokens.tokens[0]'h_size).token = YamlToken.streamStart := by
  -- Naming: s0 := (mk' input).emit streamStart; sB := BOM-handled s0.
  -- s0.tokens.size = 1, s0.tokens[0].token = streamStart.
  -- sB.tokens = s0.tokens, SimpleKeyAboveIx sB 1 holds vacuously.
  -- scanLoopIx_preserves_tokens with n=1, i=0 gives tokens[0] = sB.tokens[0] = s0.tokens[0].
  unfold scanIx at h
  have h_mk_sz : (ScannerStateIx.mk' input).tokens.tokens.size = 0 := rfl
  have h_s0_sz :
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size = 1 := by
    rw [emit_tokens_size]
    show (ScannerStateIx.mk' input).tokens.tokens.size + 1 = 1
    omega
  have h_s0_pos : 0 < ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size := by
    rw [h_s0_sz]; omega
  have h_s0_tok :
      (((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_s0_pos).token =
      YamlToken.streamStart := by
    show (((ScannerStateIx.mk' input).tokens.tokens.push
      (IxToken.mk' (ScannerStateIx.mk' input).cursor.pos YamlToken.streamStart
        (ScannerStateIx.mk' input).cursor.pos (Nat.le_refl _)
        (ScannerStateIx.mk' input).cursor.posBound))[0]'h_s0_pos).token =
        YamlToken.streamStart
    rw [Array.getElem_push]
    simp [h_mk_sz]
    rfl
  -- BOM step preserves tokens.
  have h_sB_tok : ∀ (s : ScannerStateIx input),
      (match s.peek? with | some '﻿' => s.advance | _ => s).tokens = s.tokens := by
    intro s; split <;> rfl
  have h_bom_eq : (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
      | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
      | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens := h_sB_tok _
  have h_sB_sz :
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size = 1 := by
    rw [h_bom_eq]; exact h_s0_sz
  have h_n_sB : 1 ≤ (match
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
      | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
      | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size := by
    rw [h_sB_sz]; omega
  -- Vacuous SimpleKeyAboveIx for the post-streamStart state.
  have h_inv_s0 :
      SimpleKeyAboveIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart) 1 := by
    refine ⟨?_, ?_⟩
    · intro h_poss
      exfalso; revert h_poss
      show ¬ ((ScannerStateIx.mk' input).emit YamlToken.streamStart).simpleKey.possible = true
      rw [emit_preserves_simpleKey]
      simp [ScannerStateIx.mk']
    · intro j hj
      exfalso; revert hj
      show ¬ j < ((ScannerStateIx.mk' input).emit YamlToken.streamStart).simpleKeyStack.size
      rw [emit_preserves_simpleKeyStack]
      simp [ScannerStateIx.mk']
  -- Vacuous SimpleKeyAboveIx for the BOM-handled state.
  have h_inv_sB : SimpleKeyAboveIx (match
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
      | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
      | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart) 1 := by
    split
    · exact SimpleKeyAboveIx_mono _ _ 1 h_inv_s0
        (by simp [advance_preserves_simpleKey]) (by simp [advance_preserves_simpleKeyStack])
    · exact h_inv_s0
  -- Apply scanLoopIx_preserves_tokens with n = 1, i = 0.
  obtain ⟨h_pos_ts, h_eq⟩ :=
    scanLoopIx_preserves_tokens _ ((input.utf8ByteSize + 1) * 4) tokens 1
      h_n_sB h_inv_sB h 0 (by omega)
  -- h_eq : tokens[0]'_ = bom.tokens[0]'_.
  have h_pos_bom : 0 <
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size := by
    rw [h_sB_sz]; omega
  have h_bom_tok0 :
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_pos_bom =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_s0_pos := by
    have : ∀ (h : 0 < ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.size),
        (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
          | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
          | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'(h_bom_eq ▸ h) =
        ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h := by
      intro h; congr 1
    exact this h_s0_pos
  -- Bridge: tokens.tokens[0] = tokens[0] (TokenStream GetElem rfl).
  have h_link :
      tokens[0]'h_pos_ts =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens[0]'h_s0_pos :=
    h_eq.trans h_bom_tok0
  -- The two access forms are definitionally equal (GetElem instance is rfl).
  have h_link' :
      tokens.tokens[0]'h_size =
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens.tokens[0]'h_s0_pos :=
    h_link
  rw [h_link']
  exact h_s0_tok

/-! ### §7.10  Final composite `scanIx_valid_token_stream` (theorem)

Replaces the old composite using the discharged `scanIx_first_is_streamStart`. -/

theorem scanIx_valid_token_stream
    {input : String} (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens) :
    ValidTokenStreamPropIx tokens := by
  have h_size : tokens.tokens.size ≥ 2 := scanIx_produces_at_least_two tokens h
  have h_pos : 0 < tokens.tokens.size := by omega
  refine ⟨h_size, ?_, ?_, ?_⟩
  · intro _; exact scanIx_first_is_streamStart tokens h h_pos
  · intro _; exact scanIx_last_is_streamEnd tokens h h_pos
  · exact scanIx_positions_ordered_axiom tokens h

/-! ## §8  `ScanInvIx` + `AllKeysValidIx` infrastructure
(partial — `scanIx_positions_ordered_axiom` discharge scheduled for
`6f.3b3.primitives.ordered.compose`)

Lays the foundation for porting the legacy `ScanInv` / `AllKeysValid`
compound-invariant chain (`ScannerCorrectness.lean:6520` / `:8781`)
and the loop induction `scanLoop_ordered`
(`ScannerCorrectness.lean:9405`). This session lands the *invariant
definitions* (§8.1) + the *primitive preservation lemmas* (§8.2–§8.3) +
*helper preservation lemmas* (§8.4–§8.5: skipToContent / unwindIndents
ScanInvIx & AllKeysValidIx, saveSimpleKeyIx ScanInvIx,
push*IndentIx ScanInvIx). The composition through `saveSimpleKeyIx`
AllKeysValidIx, the per-helper bricks for `scanDocumentStartIx` /
`scanFlowSequenceStartIx` / etc., the per-dispatcher compositions, and
the final `scanLoopIx_ordered` discharge are scheduled for the next
sub-step (`6f.3b3.primitives.ordered.compose`).

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

theorem SimpleKeyValidIx_of_not_possible {input : String}
    (s : ScannerStateIx input)
    (h : s.simpleKey.possible = false) : SimpleKeyValidIx s :=
  fun h_poss => absurd h_poss (by simp [h])

theorem SimpleKeyValidIx_mono {input : String} (s s' : ScannerStateIx input)
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

theorem SimpleKeyStackValidIx_mono {input : String} (s s' : ScannerStateIx input)
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

theorem AllKeysValidIx_mono {input : String} (s s' : ScannerStateIx input)
    (h_akv : AllKeysValidIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.tokens.size ≥ s.tokens.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.tokens.size),
      s'.tokens.tokens[i]'(by omega) = s.tokens.tokens[i]) :
    AllKeysValidIx s' :=
  ⟨SimpleKeyValidIx_mono s s' h_akv.1 h_sk h_mono h_pref,
   SimpleKeyStackValidIx_mono s s' h_akv.2 h_stack h_mono h_pref⟩

theorem AllKeysValidIx_of_cleared {input : String} (s' : ScannerStateIx input)
    (h_poss : s'.simpleKey.possible = false)
    (h_ssv : SimpleKeyStackValidIx s')
    : AllKeysValidIx s' :=
  ⟨SimpleKeyValidIx_of_not_possible s' h_poss, h_ssv⟩

/-- `ScanInvIx` is preserved by field updates that touch neither tokens
    nor the cursor offset. -/
theorem ScanInvIx_of_field_update {input : String} (s s' : ScannerStateIx input)
    (h : ScanInvIx s)
    (h_tok : s'.tokens = s.tokens)
    (h_off : s'.cursor.pos.offset = s.cursor.pos.offset) :
    ScanInvIx s' := by
  unfold ScanInvIx ScanInv'Ix
  rw [h_tok, h_off]; exact h

/-- `ScanInvIx` is preserved by field updates that only INCREASE
    `cursor.pos.offset` (and leave tokens unchanged). -/
theorem ScanInvIx_of_offset_ge {input : String} (s s' : ScannerStateIx input)
    (h : ScanInvIx s)
    (h_tok : s'.tokens = s.tokens)
    (h_off : s.cursor.pos.offset ≤ s'.cursor.pos.offset) :
    ScanInvIx s' := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix; rw [h_tok]
  refine ⟨h_ord, ?_⟩
  intro ⟨i, hi⟩
  exact Nat.le_trans (h_bnd ⟨i, hi⟩) h_off

/-! ### §8.3  Primitive preservation: `emit`, `emitAt`, `advance`,
`overwriteAtCursor`, `setIfInBounds`.

Each primitive carries the bound from the cursor's current offset to
the new state's cursor offset (which is the same for `emit`/`emitAt`/
`overwriteAtCursor` and ≥ for `advance`). -/

/-- The key positional fact for a single `Array.push`: positions of new
    array's indices equal the push value at the new slot, and old slot's
    value below. -/
private theorem push_start_offset_eq {input : String}
    (arr : Array (IxToken input)) (t : IxToken input)
    (k : Nat) (hk : k < (arr.push t).size) :
    ((arr.push t)[k]'hk).start.offset =
      if h : k < arr.size then (arr[k]'h).start.offset else t.start.offset := by
  by_cases hlt : k < arr.size
  · rw [Array.getElem_push_lt hlt]; simp [hlt]
  · have heq : k = arr.size := by
      have : k < arr.size + 1 := by rw [← Array.size_push]; exact hk
      omega
    subst heq
    rw [Array.getElem_push_eq]; simp [hlt]

/-- `emit tok` preserves `ScanInvIx`: the new token's start is
    `s.cursor.pos`, equal to all-old-bounds; cursor offset unchanged. -/
theorem emit_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (tok : YamlToken) (h : ScanInvIx s) : ScanInvIx (s.emit tok) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix
  have h_off : (s.emit tok).cursor.pos.offset = s.cursor.pos.offset := by
    rw [emit_cursor]
  rw [h_off]
  -- We reason via the underlying push.
  have h_get : ∀ k (hk : k < (s.emit tok).tokens.tokens.size),
      ((s.emit tok).tokens.tokens[k]'hk).start.offset =
        if h : k < s.tokens.tokens.size then (s.tokens.tokens[k]'h).start.offset
                                         else s.cursor.pos.offset := by
    intro k hk
    show ((s.tokens.tokens.push _)[k]'hk).start.offset = _
    rw [push_start_offset_eq]
    split <;> rfl
  have h_sz : (s.emit tok).tokens.tokens.size = s.tokens.tokens.size + 1 := by
    show (s.tokens.tokens.push _).size = _; exact Array.size_push ..
  refine ⟨?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    -- Reduce Fin.val
    have hij' : i < j := hij
    show ((s.emit tok).tokens.tokens[i]'hi).start.offset ≤
         ((s.emit tok).tokens.tokens[j]'hj).start.offset
    rw [h_get i hi, h_get j hj]
    split <;> rename_i hi_lt
    · split <;> rename_i hj_lt
      · exact h_ord ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ hij'
      · exact h_bnd ⟨i, hi_lt⟩
    · split <;> rename_i hj_lt
      · -- impossible: i ≥ size, j < size, i < j
        rw [h_sz] at hi
        omega
      · -- both ≥ size; from sizes, i = j = size, contradicts i < j
        rw [h_sz] at hi hj
        omega
  · intro ⟨i, hi⟩
    show ((s.emit tok).tokens.tokens[i]'hi).start.offset ≤ s.cursor.pos.offset
    rw [h_get i hi]
    split <;> rename_i hi_lt
    · exact h_bnd ⟨i, hi_lt⟩
    · exact Nat.le_refl _

/-- `emitAt startPos tok hOrder` preserves `ScanInvIx` provided that
    `startPos.offset ≥` all existing tokens' starts (the new token
    inserts at a position ≥ all current tokens). The hypothesis is
    typically discharged by `startPos = s.cursor.pos` at some earlier
    state composed with `ScanInvIx`. -/
theorem emitAt_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h : ScanInvIx s)
    (h_ge : ∀ i : Fin s.tokens.tokens.size,
      (s.tokens.tokens[i]).start.offset ≤ startPos.offset) :
    ScanInvIx (s.emitAt startPos tok hOrder) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix
  have h_off : (s.emitAt startPos tok hOrder).cursor.pos.offset =
      s.cursor.pos.offset := by rw [emitAt_cursor]
  rw [h_off]
  have h_sz : (s.emitAt startPos tok hOrder).tokens.tokens.size =
      s.tokens.tokens.size + 1 := by
    show (s.tokens.tokens.push _).size = _; exact Array.size_push ..
  have h_get : ∀ k (hk : k < (s.emitAt startPos tok hOrder).tokens.tokens.size),
      ((s.emitAt startPos tok hOrder).tokens.tokens[k]'hk).start.offset =
        if h : k < s.tokens.tokens.size then (s.tokens.tokens[k]'h).start.offset
                                         else startPos.offset := by
    intro k hk
    show ((s.tokens.tokens.push _)[k]'hk).start.offset = _
    rw [push_start_offset_eq]
    split <;> rfl
  refine ⟨?_, ?_⟩
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    have hij' : i < j := hij
    show ((s.emitAt startPos tok hOrder).tokens.tokens[i]'hi).start.offset ≤
         ((s.emitAt startPos tok hOrder).tokens.tokens[j]'hj).start.offset
    rw [h_get i hi, h_get j hj]
    split <;> rename_i hi_lt
    · split <;> rename_i hj_lt
      · exact h_ord ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ hij'
      · exact h_ge ⟨i, hi_lt⟩
    · split <;> rename_i hj_lt
      · rw [h_sz] at hi; omega
      · rw [h_sz] at hi hj; omega
  · intro ⟨i, hi⟩
    show ((s.emitAt startPos tok hOrder).tokens.tokens[i]'hi).start.offset ≤ s.cursor.pos.offset
    rw [h_get i hi]
    split <;> rename_i hi_lt
    · exact h_bnd ⟨i, hi_lt⟩
    · exact hOrder

/-- Specialised `emitAt` preservation: when `startPos.offset =
    s.cursor.pos.offset`, the `h_ge` precondition follows from
    `ScanInvIx`'s bound. -/
theorem emitAt_preserves_ScanInvIx_eq {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_eq : startPos.offset = s.cursor.pos.offset)
    (h : ScanInvIx s) :
    ScanInvIx (s.emitAt startPos tok hOrder) :=
  emitAt_preserves_ScanInvIx s startPos tok hOrder h
    (fun i => by rw [h_eq]; exact h.2 i)

/-- `advance` preserves `ScanInvIx`: tokens unchanged, cursor advances. -/
theorem advance_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (h : ScanInvIx s) : ScanInvIx s.advance := by
  apply ScanInvIx_of_offset_ge s s.advance h (by rfl) (advance_offset_monotonic s)

/-- `advanceN` preserves `ScanInvIx`. -/
theorem advanceN_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (n : Nat) (h : ScanInvIx s) : ScanInvIx (s.advanceN n) := by
  apply ScanInvIx_of_offset_ge s (s.advanceN n) h (by rfl) (advanceN_offset_monotonic s n)

/-- `overwriteAtCursor i sk tok` preserves `ScanInvIx` provided that
    `sk.pos.offset` matches the existing slot's `.start.offset`. -/
theorem overwriteAtCursor_preserves_ScanInvIx {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken)
    (h : ScanInvIx s)
    (h_match : ∀ (h_i : i < s.tokens.tokens.size),
      sk.pos.offset = (s.tokens.tokens[i]'h_i).start.offset) :
    ScanInvIx (s.overwriteAtCursor i sk tok) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInvIx ScanInv'Ix
  -- cursor unchanged
  have h_off : (s.overwriteAtCursor i sk tok).cursor.pos.offset =
      s.cursor.pos.offset := by
    show (s.cursor).pos.offset = _; rfl
  rw [h_off]
  -- size unchanged
  have h_sz : (s.overwriteAtCursor i sk tok).tokens.tokens.size =
      s.tokens.tokens.size := by
    show (s.tokens.tokens.setIfInBounds i _).size = _; exact Array.size_setIfInBounds ..
  -- The overwriting token's `.start.offset = sk.pos.offset` (definitionally
  -- from `IxToken.mk'`). Reduce via `setIfInBounds` definition + `Array.set`.
  have h_get : ∀ k (hk : k < (s.overwriteAtCursor i sk tok).tokens.tokens.size),
      ((s.overwriteAtCursor i sk tok).tokens.tokens[k]'hk).start.offset =
        if i = k then sk.pos.offset
                 else (s.tokens.tokens[k]'(by rw [h_sz] at hk; exact hk)).start.offset := by
    intro k hk
    have hk' : k < s.tokens.tokens.size := by rw [h_sz] at hk; exact hk
    show ((s.tokens.tokens.setIfInBounds i
        (IxToken.mk' (input := input) sk.pos tok sk.pos (Nat.le_refl _) sk.posBound))[k]'hk
      ).start.offset = _
    unfold Array.setIfInBounds
    by_cases hi : i < s.tokens.tokens.size
    · -- in-bounds: setIfInBounds = .set i v
      simp only [hi, dite_true]
      by_cases h_ik : i = k
      · subst h_ik
        rw [Array.getElem_set_self]
        simp [IxToken.mk']
      · rw [Array.getElem_set_ne (h := h_ik), if_neg h_ik]
    · -- out-of-bounds: setIfInBounds = id; i ≠ k since k < size and i ≥ size.
      simp only [hi, dite_false]
      have h_ne : i ≠ k := fun h => by subst h; exact hi hk'
      rw [if_neg h_ne]
  refine ⟨?_, ?_⟩
  · intro ⟨a, ha⟩ ⟨b, hb⟩ hab
    have hab' : a < b := hab
    have ha' : a < s.tokens.tokens.size := by rw [h_sz] at ha; exact ha
    have hb' : b < s.tokens.tokens.size := by rw [h_sz] at hb; exact hb
    show ((s.overwriteAtCursor i sk tok).tokens.tokens[a]'ha).start.offset ≤
         ((s.overwriteAtCursor i sk tok).tokens.tokens[b]'hb).start.offset
    rw [h_get a ha, h_get b hb]
    split <;> rename_i h_eq_a
    · split <;> rename_i h_eq_b
      · omega
      · show sk.pos.offset ≤ _
        subst h_eq_a; rw [h_match ha']
        exact h_ord ⟨i, ha'⟩ ⟨b, hb'⟩ hab'
    · split <;> rename_i h_eq_b
      · show _ ≤ sk.pos.offset
        subst h_eq_b; rw [h_match hb']
        exact h_ord ⟨a, ha'⟩ ⟨i, hb'⟩ hab'
      · exact h_ord ⟨a, ha'⟩ ⟨b, hb'⟩ hab'
  · intro ⟨k, hk⟩
    have hk' : k < s.tokens.tokens.size := by rw [h_sz] at hk; exact hk
    show ((s.overwriteAtCursor i sk tok).tokens.tokens[k]'hk).start.offset ≤ s.cursor.pos.offset
    rw [h_get k hk]
    split <;> rename_i h_eq
    · -- i = k: show sk.pos.offset ≤ s.cursor.pos.offset
      show sk.pos.offset ≤ _
      have hi_lt : i < s.tokens.tokens.size := h_eq ▸ hk'
      rw [h_match hi_lt]
      exact h_bnd ⟨i, hi_lt⟩
    · exact h_bnd ⟨k, hk'⟩

/-! ### §8.4  Helper preservation: `skipToContentS`, `unwindIndentsIx`,
`saveSimpleKeyIx`, `pushSequenceIndentIx`, `pushMappingIndentIx`.

These build on the §8.3 primitives via mono / offset_ge / emit-based
composition. -/

/-- `skipToContentS` preserves `ScanInvIx`: cursor advances, tokens
    unchanged. -/
theorem skipToContentS_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx s.skipToContentS := by
  apply ScanInvIx_of_offset_ge s s.skipToContentS h
  · exact skipToContentS_tokens s
  · exact skipToContentS_offset_monotonic s

/-- `unwindIndentsLoopIx` preserves `ScanInvIx`: emits `blockEnd` at
    cursor.pos in each iteration. -/
theorem unwindIndentsLoopIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (h : ScanInvIx s) : ScanInvIx (unwindIndentsLoopIx s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; exact h
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx
    split
    · -- emit blockEnd + pop indents + recurse
      have h_emit : ScanInvIx (s.emit YamlToken.blockEnd) := emit_preserves_ScanInvIx s _ h
      have h_pop : ScanInvIx { s.emit YamlToken.blockEnd with
          indents := (s.emit YamlToken.blockEnd).indents.pop } := by
        apply ScanInvIx_of_field_update _ _ h_emit rfl rfl
      exact ih _ h_pop
    · exact h

theorem unwindIndentsIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : ScanInvIx s) : ScanInvIx (unwindIndentsIx s col) := by
  unfold unwindIndentsIx
  exact unwindIndentsLoopIx_preserves_ScanInvIx s col s.indents.size h

theorem pushSequenceIndentIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : ScanInvIx s) : ScanInvIx (pushSequenceIndentIx s col) := by
  unfold pushSequenceIndentIx
  split
  · apply ScanInvIx_of_field_update _ _ (emit_preserves_ScanInvIx s _ h) rfl rfl
  · exact h

theorem pushMappingIndentIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : ScanInvIx s) : ScanInvIx (pushMappingIndentIx s col) := by
  unfold pushMappingIndentIx
  split
  · apply ScanInvIx_of_field_update _ _ (emit_preserves_ScanInvIx s _ h) rfl rfl
  · exact h

theorem saveSimpleKeyIx_preserves_ScanInvIx {input : String}
    (s : ScannerStateIx input) (h : ScanInvIx s) :
    ScanInvIx (saveSimpleKeyIx s) := by
  unfold saveSimpleKeyIx
  split
  · exact h
  · split
    · -- push 2 placeholders + update simpleKey/simpleKeyStack fields
      have h1 : ScanInvIx (s.emit YamlToken.placeholder) :=
        emit_preserves_ScanInvIx s _ h
      have h2 : ScanInvIx ((s.emit YamlToken.placeholder).emit YamlToken.placeholder) :=
        emit_preserves_ScanInvIx _ _ h1
      apply ScanInvIx_of_field_update _ _ h2 rfl rfl
    · exact h

/-! ### §8.5  Helper preservation for `AllKeysValidIx`.

The simpleKey/simpleKeyStack preservation lemmas
(`unwindIndentsIx_preserves_simpleKey`, etc.) from
`IndexedScannerPlainScalarValid` give us monotonicity inputs; combined
with the `_preserves_prefix` lemmas for full-token equality, we close
`AllKeysValidIx` preservation via `AllKeysValidIx_mono`. -/

theorem skipToContentS_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (h : AllKeysValidIx s) :
    AllKeysValidIx s.skipToContentS := by
  apply AllKeysValidIx_mono s s.skipToContentS h
    (skipToContentS_preserves_simpleKey s)
    (skipToContentS_preserves_simpleKeyStack s)
    (by simp [skipToContentS_tokens])
    (fun i hi => by simp [skipToContentS_tokens])

theorem unwindIndentsIx_preserves_AllKeysValidIx {input : String}
    (s : ScannerStateIx input) (col : Int)
    (h : AllKeysValidIx s) : AllKeysValidIx (unwindIndentsIx s col) := by
  apply AllKeysValidIx_mono s _ h
    (unwindIndentsIx_preserves_simpleKey s col)
    (unwindIndentsIx_preserves_simpleKeyStack s col)
    (unwindIndentsIx_tokens_size_le s col)
    (fun i hi => unwindIndentsIx_preserves_prefix s col i hi)

/-! ### §8.6  Status note on `saveSimpleKeyIx_preserves_AllKeysValidIx`
and the per-dispatcher composition

The `SimpleKeyValidIx` / `SimpleKeyStackValidIx` preservation lemmas for
`saveSimpleKeyIx` plus the per-helper `ScanInvIx` / `AllKeysValidIx`
bricks for `scanDocumentStartIx`, `scanFlowSequenceStartIx`, etc., plus
the per-dispatcher composition `scanNextTokenIx_preserves_ScanInvIx` +
`scanNextTokenIx_preserves_AllKeysValidIx`, plus `scanLoopIx_ordered` +
`scanIx_positions_ordered` are scheduled as the next sub-step
(`6f.3b3.primitives.ordered.compose`). The infrastructure landed in
§8.1–§8.5 (definitions + primitives + helpers for skipToContent /
unwindIndents / saveSimpleKey ScanInvIx + skipToContent / unwindIndents
AllKeysValidIx) is the foundation; the remaining ~1500–2000 LOC are
mechanical compositions following the legacy template
(`ScannerCorrectness.lean:6520`–`:9478`).

See Reflection 110 for the budget revision. -/

end L4YAML.Proofs.Indexed.ScannerCorrectness
