/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.IndexedScannerPlainScalarValid

/-! # `IndexedScannerCorrectness.Basic` — §1–§6

Filter index correspondence + `ValidTokenStreamPropIx` foundation.
Discharges `scanIx_produces_at_least_two` and `scanIx_last_is_streamEnd`;
exposes the two staging axioms (`scanIx_first_is_streamStart_axiom` —
discharged in `StreamStart.lean`, `scanIx_positions_ordered_axiom` —
discharged in `OrderedLoop.lean`).

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
lemma list_filter_origIdx
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
lemma list_filter_getElem_by_count
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
lemma array_filter_getElem_correspondence
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
lemma flowNestingIx_go_filter_equiv
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
lemma filter_preserves_PlainScalarsValidIx
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
    have hj_list2 : j < all_tokens.tokens.toList.length := by
      simpa [Indexed.TokenStream.size] using hj_arr
    show (all_tokens.tokens.filter p).toList[i]'hi_list2 = all_tokens.tokens.toList[j]'hj_list2
    simp only [Array.toList_filter]; exact val_eq
  exact val_eq_arr ▸ h_psv j hj_arr

/-- Filtering placeholders preserves `FlowContextPSVIx`. Indexed twin
    of legacy `filter_preserves_FlowContextPSV`
    (`ScannerPlainScalarValid.lean:5379`). -/
lemma filter_preserves_FlowContextPSVIx
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
    have hj_list2 : j < all_tokens.tokens.toList.length := by
      simpa [Indexed.TokenStream.size] using hj_arr
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
lemma filter_preserves_FlowAwarePSVIx
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
lemma filter_preserves_FlowBracketsMatchedIx
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
lemma scanFilteredIx_FlowAwarePSVIx
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
lemma scanFilteredIx_FlowBracketsMatchedIx
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

lemma scanLoopIx_success_emits_streamEnd {input : String} :
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
          by_cases hDS : s.directivesPresent = true
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

lemma scanLoopIx_increases_tokens {input : String}
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
          by_cases hDS : s.directivesPresent = true
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

lemma scanIx_produces_at_least_two {input : String}
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

lemma scanIx_last_is_streamEnd {input : String}
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
-- *discharged* as a theorem in §7.9 (StreamStart.lean). The former
-- `scanIx_positions_ordered_axiom` is now *discharged* as a theorem
-- in §8.11 (OrderedLoop.lean) as part of Step
-- `6f.3b3.primitives.ordered.compose.value.tail`. The composite
-- `scanIx_valid_token_stream` lives in §8.12 (OrderedLoop.lean).
-- This file no longer exposes any staging axiom for `scanIx`.

/-! ### §6.5  Composite theorem `scanIx_valid_token_stream` (moved to §8.12)

The composite `scanIx_valid_token_stream` is defined in
`OrderedLoop.lean` §8.12 (after `scanIx_positions_ordered` is
discharged as a theorem in §8.11). The downstream consumer in
`IndexedGrammable.parseYamlIx_implies_valid_token_stream` references
the §8.12 theorem. -/

end L4YAML.Proofs.Indexed.ScannerCorrectness
