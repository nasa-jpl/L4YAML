/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.FirstFiltered

/-! # `FilteredGrowth.Infra` — Phase 3 Step
`6f.3b3.filteredgrowth.infra`

**Sub-session 2 of `.filteredgrowth`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 5900–6070, ~170 LOC).

Filtered token array growth infrastructure. Every `scanNextTokenIx`
step adds at least one non-`.placeholder` token; the proof decomposes
into:
  1. Preprocessing (`skipToContentS`, `unwindIndentsIx`,
     `saveSimpleKeyIx`) preserves or grows filtered count
     — `preprocess_filtered_monoIx` below, built from
     `_preprocess_preserves_prefix` (StreamStart §7.7) and
     `scanNextTokenIx_preprocess_tokens_size_le` (FlowMonoChain
     `Basic.lean`) via `Array_filter_prefix_of_raw_prefix` from
     `FirstFiltered`.
  2. Each dispatch branch emits at least one non-`.placeholder` token
     — handled in `.perdispatch`.
  3. `setIfInBounds` with non-`.placeholder` replacement doesn't
     decrease filtered count (used by `scanValuePrepareIx`).

Ships:
  * **§1 `List_filter_set_length_monoIx`** — list helper for §2 (legacy
    5912).
  * **§2 `Array_setIfInBounds_filter_monoIx`** — `Array.setIfInBounds`
    with a filter-passing replacement preserves or grows filtered size
    (legacy 5929).
  * **§3 `preprocess_filtered_monoIx`** — `scanNextTokenIx_preprocess`
    monotonicity for filtered count (legacy 5945).
  * **§4 `allowDir_ite_filter_monoIx`** — the `allowDirectives`/`
    documentEverStarted` if-then-else preserves filtered token count
    (legacy 5958).
  * **§5 `List_filter_length_ge_oneIx`** — if a non-empty list's first
    element passes `p`, `(l.filter p).length ≥ 1` (legacy 5968).
  * **§6 `filtered_grows_of_extended_prefixIx`** — extending an array
    with a `p`-passing first new element grows `(filter p).size` by
    ≥ 1 (legacy 5980).
  * **§7 `filtered_grows_of_any_newIx`** — variant of §6 where the
    `p`-passing element is at some `j ≥ a.size`, not necessarily
    `a.size` itself (legacy 6025).

## Indexed simplification

The generic `Array α` / `List α` lemmas (§1, §2, §5, §6, §7) port
verbatim — no indexed substrate involved. The only true indexed lemma
is §3 `preprocess_filtered_monoIx`, which composes the indexed
`_preprocess_preserves_prefix` (StreamStart `§7.7'`) with the indexed
`scanNextTokenIx_preprocess_tokens_size_le` (`FlowMonoChain.Basic`
`§3.preprocess.monotonicity`) and the previously-landed
`Array_filter_prefix_of_raw_prefix` (FirstFiltered §6). The
`TokenStream`'s `GetElem` instance unfolds to `.tokens[i]`
definitionally, so the raw-array hypothesis demanded by
`Array_filter_prefix_of_raw_prefix` follows from the `TokenStream`-
level equality returned by `_preprocess_preserves_prefix` without any
rewriting.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.ScannerCorrectness
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

variable {input : String}

/-! ## §1  `List_filter_set_length_monoIx`

Replacing an element of a list with a value that passes the filter
does not decrease the filtered length. Verbatim port of legacy
`List_filter_set_length_mono` (line 5912). -/

lemma List_filter_set_length_monoIx {α : Type} (l : List α) (i : Nat) (v : α)
    (p : α → Bool) (hv : p v = true) :
    ((l.set i v).filter p).length ≥ (l.filter p).length := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons, hv, ite_true]
      split <;> simp <;> omega
    | succ j =>
      simp only [List.set_cons_succ, List.filter_cons]
      have := ih j
      split <;> simp <;> omega

/-! ## §2  `Array_setIfInBounds_filter_monoIx`

`Array.setIfInBounds` with a filter-passing replacement preserves or
grows the filtered array size. Verbatim port of legacy
`Array_setIfInBounds_filter_mono` (line 5929). -/

lemma Array_setIfInBounds_filter_monoIx {α : Type} (a : Array α) (i : Nat) (v : α)
    (p : α → Bool) (hv : p v = true) :
    ((a.setIfInBounds i v).filter p).size ≥ (a.filter p).size := by
  unfold Array.setIfInBounds
  split
  · -- i < a.size: use List_filter_set_length_monoIx
    next h_bound =>
    have : ((a.set i v h_bound).filter p).toList.length ≥ (a.filter p).toList.length := by
      rw [Array.toList_filter, Array.toList_filter, Array.toList_set]
      exact List_filter_set_length_monoIx a.toList i v p hv
    exact this
  · -- i ≥ a.size: identity
    omega

/-! ## §3  `preprocess_filtered_monoIx`

The filtered token count doesn't decrease through
`scanNextTokenIx_preprocess`. Indexed twin of legacy
`preprocess_filtered_mono` (line 5945). -/

lemma preprocess_filtered_monoIx (s s_pp : ScannerStateIx input) (c : Char)
    (h : scanNextTokenIx_preprocess s = .ok (some (s_pp, c))) :
    (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).size ≥
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size := by
  have h_mono : s.tokens.tokens.size ≤ s_pp.tokens.tokens.size :=
    scanNextTokenIx_preprocess_tokens_size_le s s_pp c h
  have h_pres : ∀ i (hi : i < s.tokens.tokens.size),
      s_pp.tokens.tokens[i]'(Nat.lt_of_lt_of_le hi h_mono) = s.tokens.tokens[i]'hi := by
    intro i hi
    obtain ⟨_, h_eq⟩ :=
      _preprocess_preserves_prefix s s_pp c s.tokens.tokens.size (Nat.le_refl _) h i hi
    exact h_eq
  obtain ⟨suffix, h_eq⟩ :=
    Array_filter_prefix_of_raw_prefix s.tokens.tokens s_pp.tokens.tokens
      (fun t => t.token != .placeholder) h_mono h_pres
  show (s_pp.tokens.tokens.filter (fun t => t.token != .placeholder)).toList.length ≥
       (s.tokens.tokens.filter (fun t => t.token != .placeholder)).toList.length
  rw [h_eq, List.length_append]; omega

/-! ## §4  `allowDir_ite_filter_monoIx`

The `allowDirectives = true` if-then-else (which sets
`allowDirectives := false` and `documentEverStarted := true`)
preserves filtered token count — both fields are non-token. Verbatim
port of legacy `allowDir_ite_filter` (line 5958). -/

lemma allowDir_ite_filter_monoIx (s : ScannerStateIx input) :
    let p := fun (t : IxToken input) => t.token != .placeholder
    ((if s.allowDirectives = true then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).tokens.tokens.filter p).size = (s.tokens.tokens.filter p).size := by
  split <;> rfl

/-! ## §5  `List_filter_length_ge_oneIx`

If a non-empty list's first element passes filter `p`, the filtered
list has length ≥ 1. Verbatim port of legacy `List_filter_length_ge_one`
(line 5968). -/

lemma List_filter_length_ge_oneIx {α : Type} (l : List α) (p : α → Bool)
    (h_len : l.length ≥ 1) (h_head : p (l[0]'(by omega)) = true) :
    (l.filter p).length ≥ 1 := by
  match l with
  | [] => simp at h_len
  | hd :: tl =>
    have h_hd : p hd = true := h_head
    rw [List.filter_cons_of_pos h_hd, List.length_cons]; omega

/-! ## §6  `filtered_grows_of_extended_prefixIx`

If array `b` extends array `a` (same elements at positions `< a.size`),
has at least one more element, and that element at position `a.size`
passes filter `p`, then `(b.filter p).size ≥ (a.filter p).size + 1`.
Verbatim port of legacy `filtered_grows_of_extended_prefix` (line 5980). -/

lemma filtered_grows_of_extended_prefixIx {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : b.size ≥ a.size + 1)
    (h_pres : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (h_new : p (b[a.size]'(by omega)) = true) :
    (b.filter p).size ≥ (a.filter p).size + 1 := by
  -- Convert to List level (Array.size = toList.length definitionally)
  show (b.filter p).toList.length ≥ (a.filter p).toList.length + 1
  simp only [Array.toList_filter]
  -- Goal: (b.toList.filter p).length ≥ (a.toList.filter p).length + 1
  have h_len_le : a.toList.length ≤ b.toList.length := by
    simp only [Array.length_toList]; omega
  -- Prefix equality via ext_getElem
  have h_take : b.toList.take a.toList.length = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro n hn₁ hn₂
      simp only [List.getElem_take, Array.getElem_toList]
      exact h_pres n (by simp only [Array.length_toList] at hn₂; exact hn₂)
  -- Split b.toList = a.toList ++ drop
  have h_split_eq : b.toList = a.toList ++ b.toList.drop a.toList.length := by
    have := List.take_append_drop a.toList.length b.toList
    rw [h_take] at this; exact this.symm
  -- Rewrite filter length as sum of parts
  have h_filter_eq : (b.toList.filter p).length =
      (a.toList.filter p).length + (b.toList.drop a.toList.length |>.filter p).length := by
    have := congrArg (fun l => (l.filter p).length) h_split_eq
    simp only [List.filter_append, List.length_append] at this
    exact this
  rw [h_filter_eq]
  -- Suffices: the drop's filter has ≥ 1 element
  suffices (b.toList.drop a.toList.length |>.filter p).length ≥ 1 by omega
  -- The drop has ≥ 1 element and its first element passes p
  have h_drop_len : (b.toList.drop a.toList.length).length ≥ 1 := by
    simp only [List.length_drop, Array.length_toList]; omega
  have h_head_p : p ((b.toList.drop a.toList.length)[0]'(by omega)) = true := by
    simp only [List.getElem_drop, Nat.add_zero, Array.getElem_toList]
    exact h_new
  exact List_filter_length_ge_oneIx _ _ h_drop_len h_head_p

/-! ## §7  `filtered_grows_of_any_newIx`

Variant of §6: if array `b` extends array `a`, has at least one more
element, and some element at position `j ≥ a.size` passes filter `p`,
then `(b.filter p).size ≥ (a.filter p).size + 1`. Used when we know
a specific NEW element (e.g. the last) is non-`.placeholder`, but
don't know the exact value at the first new position `a.size`.
Verbatim port of legacy `filtered_grows_of_any_new` (line 6025). -/

lemma filtered_grows_of_any_newIx {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : b.size ≥ a.size + 1)
    (h_pres : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (j : Nat) (hj_lo : a.size ≤ j) (hj_hi : j < b.size)
    (h_new : p (b[j]'hj_hi) = true) :
    (b.filter p).size ≥ (a.filter p).size + 1 := by
  show (b.filter p).toList.length ≥ (a.filter p).toList.length + 1
  simp only [Array.toList_filter]
  have h_len_le : a.toList.length ≤ b.toList.length := by
    simp only [Array.length_toList]; omega
  have h_take : b.toList.take a.toList.length = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro n hn₁ hn₂
      simp only [List.getElem_take, Array.getElem_toList]
      exact h_pres n (by simp only [Array.length_toList] at hn₂; exact hn₂)
  have h_split_eq : b.toList = a.toList ++ b.toList.drop a.toList.length := by
    have := List.take_append_drop a.toList.length b.toList
    rw [h_take] at this; exact this.symm
  have h_filter_eq : (b.toList.filter p).length =
      (a.toList.filter p).length + (b.toList.drop a.toList.length |>.filter p).length := by
    have := congrArg (fun l => (l.filter p).length) h_split_eq
    simp only [List.filter_append, List.length_append] at this
    exact this
  rw [h_filter_eq]
  suffices (b.toList.drop a.toList.length |>.filter p).length ≥ 1 by omega
  -- j - a.size is a valid index in the drop
  have h_j_drop : j - a.toList.length < (b.toList.drop a.toList.length).length := by
    simp only [List.length_drop, Array.length_toList]; omega
  -- The element at j-a.size in drop equals b[j]
  have h_drop_eq :
      (b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop = b[j]'hj_hi := by
    simp only [List.getElem_drop, Array.getElem_toList, Array.length_toList]
    congr 1; omega
  -- So it passes p
  have h_j_p : p ((b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop) = true := by
    rw [h_drop_eq]; exact h_new
  -- That element is in the filter
  have h_mem : (b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop ∈
      (b.toList.drop a.toList.length).filter p :=
    List.mem_filter.mpr ⟨List.getElem_mem h_j_drop, h_j_p⟩
  -- So the filter is non-empty, hence length ≥ 1
  cases h_cases : (b.toList.drop a.toList.length).filter p with
  | nil => rw [h_cases] at h_mem; simp at h_mem
  | cons => simp

end L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
