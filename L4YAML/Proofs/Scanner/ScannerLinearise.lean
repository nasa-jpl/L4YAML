/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.Linearise

/-!
# Linearisation correctness (Initiative 3 / Phase J.3.1 + J.3.2)

Proofs for the three foundational properties of `linearise` declared
in `L4YAML/Scanner/Linearise.lean`:

* `linearise_resolved` — output-size accounting.
* `linearise_append_unresolved` — pushing an unresolved pending entry
  is a no-op for the linearised output.
* `linearise_append_token` — append-monotonicity (the headline Path C
  property): pushing a real token to `tokens` only extends the
  linearised output rightward.

J.3.2 also adds these flow-aware bridge helpers (the `Preserves` suite),
consumed by `Proofs/Production/ScannerPlainScalarValid.lean`:

* `expandKind_val_neutral` — spliced `expandKind` tokens are never flow
  brackets and never plain scalars.
* `linearise_go_prefix` — `linearise.go` extends its accumulator (size
  monotone, prefix-equal).
* `linearise_go_get_at_acc_size` / `linearise_go_get_in_expand` —
  characterise the values of `linearise.go`'s output at the boundary
  positions used by the bridge proofs.

Auxiliary helpers (`pendingExpandSumFrom`, `linearise.go_size`,
`linearise_go_done`, `linearise_go_step_token`,
`linearise_go_tail_pks_invariant`) are re-used by downstream
re-discharges (J.3.2 onwards).  All declarations are public to remain
analysable from other proof files.

Discharged 2026-04-26.

See `Blueprint/07-initiative-3-append-only.md` §J.3.
-/

namespace L4YAML.Proofs.ScannerLinearise

open L4YAML
open L4YAML.Scanner

/-! ## Auxiliary: suffix-sum of pending-entry expansions

`pendingExpandSumFrom pks p` sums `(expandKind pks[i]).size` for
`i ∈ [p, pks.size)`.  Used to express `linearise.go`'s output-size
formula in a recursion-friendly form: each `linearise.go` step that
processes a pending entry decreases this sum by exactly the size
contributed at that index. -/
def pendingExpandSumFrom (pks : Array PendingKeyEntry) (p : Nat) : Nat :=
  if h : p < pks.size then
    (expandKind pks[p]).size + pendingExpandSumFrom pks (p + 1)
  else 0
termination_by pks.size - p

/-- Unfolding equation for the recursive-step case. -/
theorem pendingExpandSumFrom_succ
    (pks : Array PendingKeyEntry) (p : Nat) (h : p < pks.size) :
    pendingExpandSumFrom pks p
      = (expandKind pks[p]).size + pendingExpandSumFrom pks (p + 1) := by
  rw [pendingExpandSumFrom]
  simp [h]

/-- Unfolding equation for the base case. -/
theorem pendingExpandSumFrom_at_size (pks : Array PendingKeyEntry) :
    pendingExpandSumFrom pks pks.size = 0 := by
  rw [pendingExpandSumFrom]
  simp

/-- Beyond the array end: the suffix sum is also zero. -/
theorem pendingExpandSumFrom_ge_size
    (pks : Array PendingKeyEntry) (p : Nat) (h : pks.size ≤ p) :
    pendingExpandSumFrom pks p = 0 := by
  rw [pendingExpandSumFrom]
  have : ¬ p < pks.size := Nat.not_lt.mpr h
  simp [this]

/-! ## Generic helpers for partial-range `Array.foldl` -/

/-- Empty-range fold: `xs.foldl f init i i = init`. -/
theorem foldl_partial_empty {α : Type _} {β : Type _}
    (f : β → α → β) (init : β) (xs : Array α) (i : Nat) :
    xs.foldl f init i i = init := by
  rw [Array.foldl_eq_foldl_extract]
  rw [Array.extract_eq_empty_of_le (Nat.min_le_left _ _)]
  simp

/-- Step lemma for the prefix partial fold:
    `xs.foldl f init 0 (j+1) = f (xs.foldl f init 0 j) xs[j]` when `j < xs.size`. -/
theorem foldl_prefix_step {α : Type _} {β : Type _}
    (f : β → α → β) (init : β) (xs : Array α)
    (j : Nat) (h : j < xs.size) :
    xs.foldl f init 0 (j + 1) = f (xs.foldl f init 0 j) xs[j] := by
  rw [Array.foldl_eq_foldl_extract (start := 0) (stop := j + 1)]
  rw [Array.extract_succ_right (i := 0) (j := j) (Nat.zero_lt_succ j) h]
  rw [Array.foldl_push]
  rw [← Array.foldl_eq_foldl_extract (start := 0) (stop := j)]

/-! ## Bridge: `pendingExpandSumFrom` ↔ `Array.foldl` -/

/-- Invariant connecting the prefix `Array.foldl` to the suffix
    `pendingExpandSumFrom`: their sum is the full fold.

    Proof by reverse induction on `i` from `pks.size` down to `0`,
    parametrised by the gap `pks.size - i`. -/
theorem foldl_prefix_plus_pendingExpandSumFrom
    (pks : Array PendingKeyEntry) :
    ∀ (j : Nat) (i : Nat), i + j = pks.size →
      pks.foldl (fun n e => n + (expandKind e).size) 0 0 i
        + pendingExpandSumFrom pks i
        = pks.foldl (fun n e => n + (expandKind e).size) 0 := by
  intro j
  induction j with
  | zero =>
    intro i h
    have h_eq : i = pks.size := by omega
    subst h_eq
    rw [pendingExpandSumFrom_at_size]
    simp
  | succ j' ih =>
    intro i h
    have h_lt : i < pks.size := by omega
    have h_step : pks.foldl (fun n e => n + (expandKind e).size) 0 0 (i + 1)
                = pks.foldl (fun n e => n + (expandKind e).size) 0 0 i
                  + (expandKind pks[i]).size := by
      rw [foldl_prefix_step _ 0 pks i h_lt]
    have h_ih :
        pks.foldl (fun n e => n + (expandKind e).size) 0 0 (i + 1)
          + pendingExpandSumFrom pks (i + 1)
          = pks.foldl (fun n e => n + (expandKind e).size) 0 := by
      apply ih
      omega
    rw [pendingExpandSumFrom_succ pks i h_lt]
    rw [← h_ih, h_step]
    omega

/-- Specialisation: `Array.foldl` from index 0 equals
    `pendingExpandSumFrom pks 0`. -/
theorem pendingExpandSumFrom_zero_eq_foldl
    (pks : Array PendingKeyEntry) :
    pendingExpandSumFrom pks 0
      = pks.foldl (fun n e => n + (expandKind e).size) 0 := by
  have h := foldl_prefix_plus_pendingExpandSumFrom pks pks.size 0 (by omega)
  rw [foldl_partial_empty] at h
  omega

/-! ## Output-size accounting -/

/-- Helper: the size of `linearise.go tokens pks k p acc` is
    `acc.size + (tokens.size - k) + pendingExpandSumFrom pks p`.

    Proof by strong induction on the lex-measure
    `n = (tokens.size - k) + (pks.size - p)`. -/
theorem linearise_go_size
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry) :
    ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pendingKeys.size - p) = n →
      (linearise.go tokens pendingKeys k p acc).size
        = acc.size + (tokens.size - k) + pendingExpandSumFrom pendingKeys p := by
  intro n
  induction n with
  | zero =>
    intro k p acc h
    have h_p : pendingKeys.size ≤ p := by omega
    have h_k : tokens.size ≤ k := by omega
    rw [linearise.go]
    have h_p_neg : ¬ p < pendingKeys.size := Nat.not_lt.mpr h_p
    have h_k_neg : ¬ k < tokens.size := Nat.not_lt.mpr h_k
    simp [h_p_neg, h_k_neg]
    rw [pendingExpandSumFrom_ge_size pendingKeys p h_p]
    have : tokens.size - k = 0 := Nat.sub_eq_zero_of_le h_k
    omega
  | succ n ih =>
    intro k p acc h
    rw [linearise.go]
    by_cases hp : p < pendingKeys.size
    · simp only [hp, ↓reduceDIte]
      by_cases hsplice : pendingKeys[p].insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte]
        have h_meas : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
        rw [ih k (p + 1) (acc ++ expandKind pendingKeys[p]) h_meas]
        rw [pendingExpandSumFrom_succ pendingKeys p hp]
        simp [Array.size_append]
        omega
      · simp only [hsplice, ↓reduceIte]
        by_cases hk : k < tokens.size
        · simp only [hk, ↓reduceDIte]
          have h_meas : (tokens.size - (k + 1)) + (pendingKeys.size - p) = n := by omega
          rw [ih (k + 1) p (acc.push tokens[k]) h_meas]
          simp [Array.size_push]
          omega
        · simp only [hk, ↓reduceDIte]
          have h_meas : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
          rw [ih k (p + 1) (acc ++ expandKind pendingKeys[p]) h_meas]
          rw [pendingExpandSumFrom_succ pendingKeys p hp]
          simp [Array.size_append]
          omega
    · simp only [hp, ↓reduceDIte]
      have h_p_ge : pendingKeys.size ≤ p := Nat.le_of_not_lt hp
      by_cases hk : k < tokens.size
      · simp only [hk, ↓reduceDIte]
        have h_meas : (tokens.size - (k + 1)) + (pendingKeys.size - p) = n := by omega
        rw [ih (k + 1) p (acc.push tokens[k]) h_meas]
        simp [Array.size_push]
        omega
      · exfalso
        have h_k_ge : tokens.size ≤ k := Nat.le_of_not_lt hk
        omega

/-- **Output-size accounting**: linearise's output is exactly the
    original tokens plus the total expansion of all pending entries.
    Unresolved entries contribute zero, `keyOnly` contributes one,
    `blockMappingStartAndKey` contributes two — matching the legacy
    `placeholder` slot-reservation count.

    Discharges the J.1 statement of the same name in
    `L4YAML/Scanner/Linearise.lean`. -/
theorem linearise_resolved
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry) :
    (linearise tokens pendingKeys).size
      = tokens.size + pendingKeys.foldl (fun n e => n + (expandKind e).size) 0 := by
  unfold linearise
  rw [linearise_go_size tokens pendingKeys
        ((tokens.size - 0) + (pendingKeys.size - 0)) 0 0 #[] (by rfl)]
  rw [pendingExpandSumFrom_zero_eq_foldl]
  simp

/-! ## Append-only output: termination and "trapped-at-tail" invariants -/

/-- When both pending and token loops are exhausted, `linearise.go`
    returns its accumulator unchanged. -/
theorem linearise_go_done
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (k p : Nat) (acc : Array (Positioned YamlToken))
    (hk : tokens.size ≤ k) (hp : pks.size ≤ p) :
    linearise.go tokens pks k p acc = acc := by
  rw [linearise.go]
  simp [Nat.not_lt.mpr hk, Nat.not_lt.mpr hp]

/-- One-step unfolding when pendings are exhausted but tokens remain:
    `linearise.go` pushes `tokens[k]` and recurses with `k+1`. -/
theorem linearise_go_step_token
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (k p : Nat) (acc : Array (Positioned YamlToken))
    (hk : k < tokens.size) (hp : pks.size ≤ p) :
    linearise.go tokens pks k p acc
      = linearise.go tokens pks (k + 1) p (acc.push tokens[k]) := by
  rw [linearise.go]
  simp [Nat.not_lt.mpr hp, hk]

/-- Once `linearise.go`'s pending-loop is exhausted, only the token
    suffix matters for the output.  For two arbitrary pending arrays
    (potentially of different lengths), as long as both starting
    indices are at-or-past their respective ends, `linearise.go`
    produces the same output. -/
theorem linearise_go_tail_pks_invariant
    (tokens : Array (Positioned YamlToken))
    (pks1 pks2 : Array PendingKeyEntry) :
    ∀ (n k p1 p2 : Nat) (acc : Array (Positioned YamlToken)),
      tokens.size - k = n →
      pks1.size ≤ p1 → pks2.size ≤ p2 →
      linearise.go tokens pks1 k p1 acc
        = linearise.go tokens pks2 k p2 acc := by
  intro n
  induction n with
  | zero =>
    intro k p1 p2 acc h_n h1 h2
    have h_k : tokens.size ≤ k := by omega
    rw [linearise_go_done tokens pks1 k p1 acc h_k h1]
    rw [linearise_go_done tokens pks2 k p2 acc h_k h2]
  | succ n ih =>
    intro k p1 p2 acc h_n h1 h2
    have h_k : k < tokens.size := by omega
    have hp1 : ¬ p1 < pks1.size := Nat.not_lt.mpr h1
    have hp2 : ¬ p2 < pks2.size := Nat.not_lt.mpr h2
    rw [linearise.go]
    rw [linearise.go]
    simp only [hp1, hp2, h_k, ↓reduceDIte]
    apply ih (k + 1) p1 p2 (acc.push tokens[k]) (by omega) h1 h2

/-- **Unresolved-key invariance**: pushing an unresolved pending key is
    a no-op for the linearised output.  Equivalent to "placeholders
    don't appear in the user-facing token stream" in the legacy model,
    but established constructively here (no filter pass needed).

    Discharges the J.1 statement of the same name in
    `L4YAML/Scanner/Linearise.lean`. -/
theorem linearise_append_unresolved
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (e : PendingKeyEntry) (he : e.kind = .unresolved) :
    linearise tokens (pendingKeys.push e) = linearise tokens pendingKeys := by
  -- The key fact: e.kind = .unresolved means expandKind e = #[].
  have he' : expandKind e = #[] := by
    unfold expandKind
    rw [he]
  -- Strong helper.
  suffices h : ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pendingKeys.size - p) = n →
      p ≤ pendingKeys.size →
      linearise.go tokens (pendingKeys.push e) k p acc
        = linearise.go tokens pendingKeys k p acc by
    unfold linearise
    exact h _ 0 0 #[] rfl (Nat.zero_le _)
  intro n
  induction n with
  | zero =>
    intro k p acc h_n h_p_le
    have h_k : tokens.size ≤ k := by omega
    have h_p_eq : p = pendingKeys.size := by omega
    subst h_p_eq
    rw [linearise_go_done tokens pendingKeys k pendingKeys.size acc h_k (Nat.le_refl _)]
    rw [linearise.go]
    have hp_new : pendingKeys.size < (pendingKeys.push e).size := by
      simp [Array.size_push]
    have hk_neg : ¬ k < tokens.size := Nat.not_lt.mpr h_k
    simp only [hp_new, ↓reduceDIte]
    simp only [Array.getElem_push_eq]
    by_cases hsplice : e.insertBeforeIdx ≤ k
    · simp only [hsplice, ↓reduceIte, he', Array.append_empty]
      exact linearise_go_done _ _ _ _ _ h_k (by simp [Array.size_push])
    · simp only [hsplice, ↓reduceIte, hk_neg, ↓reduceDIte, he', Array.append_empty]
      exact linearise_go_done _ _ _ _ _ h_k (by simp [Array.size_push])
  | succ n ih =>
    intro k p acc h_n h_p_le
    by_cases hp : p < pendingKeys.size
    · rw [linearise.go]
      rw [linearise.go]
      have hp' : p < (pendingKeys.push e).size := by simp [Array.size_push]; omega
      simp only [hp, hp', ↓reduceDIte]
      simp only [Array.getElem_push_lt hp]
      by_cases hsplice : pendingKeys[p].insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte]
        have h_meas : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
        exact ih k (p + 1) (acc ++ expandKind pendingKeys[p]) h_meas (by omega)
      · simp only [hsplice, ↓reduceIte]
        by_cases hk : k < tokens.size
        · simp only [hk, ↓reduceDIte]
          have h_meas : (tokens.size - (k + 1)) + (pendingKeys.size - p) = n := by omega
          exact ih (k + 1) p (acc.push tokens[k]) h_meas h_p_le
        · simp only [hk, ↓reduceDIte]
          have h_meas : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
          exact ih k (p + 1) (acc ++ expandKind pendingKeys[p]) h_meas (by omega)
    · have h_p_eq : p = pendingKeys.size := by omega
      subst h_p_eq
      have h_k_lt : k < tokens.size := by omega
      rw [linearise.go]
      have hp_new : pendingKeys.size < (pendingKeys.push e).size := by
        simp [Array.size_push]
      simp only [hp_new, ↓reduceDIte]
      simp only [Array.getElem_push_eq]
      by_cases hsplice : e.insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte, he', Array.append_empty]
        exact linearise_go_tail_pks_invariant tokens (pendingKeys.push e) pendingKeys
          (tokens.size - k) k (pendingKeys.size + 1) pendingKeys.size acc rfl
          (by simp [Array.size_push]) (Nat.le_refl _)
      · simp only [hsplice, ↓reduceIte, h_k_lt, ↓reduceDIte]
        rw [linearise_go_step_token tokens pendingKeys k pendingKeys.size acc
              h_k_lt (Nat.le_refl _)]
        have h_meas :
            (tokens.size - (k + 1)) + (pendingKeys.size - pendingKeys.size) = n := by omega
        exact ih (k + 1) pendingKeys.size (acc.push tokens[k]) h_meas (Nat.le_refl _)

/-- **All-unresolved invariance**: when every pending entry is unresolved,
    `linearise tokens pendingKeys = tokens`.  Generalises
    `linearise_append_unresolved` (single push) to arbitrary unresolved
    pending arrays.

    Used by `Proofs/Output/EmitterScannability.lean` (Initiative 3 / J.3.7)
    to derive the linearised shape of `scanFiltered (emitScalar content)`,
    where the scanner's `saveSimpleKey` reservation never resolves (no `:`
    follows). -/
theorem linearise_all_unresolved
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (h_unres : ∀ e ∈ pendingKeys, e.kind = .unresolved) :
    linearise tokens pendingKeys = tokens := by
  -- Strong helper, in `toList` form (cleaner List.drop manipulation).
  -- For all (n, k, p, acc): when the lex-measure equals n and indices
  -- are in-bounds, `(linearise.go tokens pendingKeys k p acc).toList`
  -- equals `acc.toList ++ tokens.toList.drop k`.
  suffices h : ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pendingKeys.size - p) = n →
      k ≤ tokens.size → p ≤ pendingKeys.size →
      (linearise.go tokens pendingKeys k p acc).toList
        = acc.toList ++ tokens.toList.drop k by
    apply Array.toList_inj.mp
    unfold linearise
    rw [h ((tokens.size - 0) + (pendingKeys.size - 0)) 0 0 #[] rfl
          (Nat.zero_le _) (Nat.zero_le _)]
    simp
  intro n
  induction n with
  | zero =>
    intro k p acc h_meas h_k h_p
    have h_k_eq : k = tokens.size := by omega
    have h_p_eq : p = pendingKeys.size := by omega
    subst h_k_eq
    subst h_p_eq
    rw [linearise_go_done tokens pendingKeys tokens.size pendingKeys.size acc
          (Nat.le_refl _) (Nat.le_refl _)]
    have h_drop : tokens.toList.drop tokens.size = [] := by
      apply List.drop_eq_nil_of_le
      rw [Array.length_toList]; exact Nat.le_refl _
    rw [h_drop, List.append_nil]
  | succ n ih =>
    intro k p acc h_meas h_k h_p
    rw [linearise.go]
    by_cases hp : p < pendingKeys.size
    · simp only [hp, ↓reduceDIte]
      have h_e_unres : pendingKeys[p].kind = .unresolved :=
        h_unres _ (pendingKeys.getElem_mem hp)
      have h_expand : expandKind pendingKeys[p] = #[] := by
        unfold expandKind; rw [h_e_unres]
      by_cases hsplice : pendingKeys[p].insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte]
        have h_meas' : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
        rw [h_expand, Array.append_empty]
        exact ih k (p + 1) acc h_meas' h_k (by omega)
      · simp only [hsplice, ↓reduceIte]
        by_cases hk : k < tokens.size
        · simp only [hk, ↓reduceDIte]
          have h_meas' : (tokens.size - (k + 1)) + (pendingKeys.size - p) = n := by omega
          rw [ih (k + 1) p (acc.push tokens[k]) h_meas' (by omega) h_p]
          rw [Array.toList_push, List.append_assoc]
          congr 1
          have h_k_len : k < tokens.toList.length := by
            rw [Array.length_toList]; exact hk
          rw [List.drop_eq_getElem_cons h_k_len]
          rw [Array.getElem_toList]
          rfl
        · simp only [hk, ↓reduceDIte]
          have h_meas' : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
          rw [h_expand, Array.append_empty]
          exact ih k (p + 1) acc h_meas' h_k (by omega)
    · simp only [hp, ↓reduceDIte]
      have h_p_eq : p = pendingKeys.size := by omega
      subst h_p_eq
      by_cases hk : k < tokens.size
      · simp only [hk, ↓reduceDIte]
        have h_meas' : (tokens.size - (k + 1)) + (pendingKeys.size - pendingKeys.size) = n := by
          omega
        rw [ih (k + 1) pendingKeys.size (acc.push tokens[k]) h_meas'
              (by omega) (Nat.le_refl _)]
        rw [Array.toList_push, List.append_assoc]
        congr 1
        have h_k_len : k < tokens.toList.length := by
          rw [Array.length_toList]; exact hk
        rw [List.drop_eq_getElem_cons h_k_len]
        rw [Array.getElem_toList]
        rfl
      · exfalso; omega

/-- **Append-monotonicity** (the headline property of Path C).

    Pushing a new token to `tokens` extends `linearise`'s output
    rightward — the existing prefix is preserved, only a tail is
    appended.  This is the "filter monotonicity" property the legacy
    `setIfInBounds` model could not deliver: under the legacy scheme
    the same token push could trigger a placeholder rewrite that
    *changed* an earlier output position.

    The hypothesis `h` says every pending entry's `insertBeforeIdx` is
    at most `tokens.size` — i.e. all current pendings target a slot
    inside (or at the tail of) the existing token array.  Save-time
    monotonicity guarantees this throughout scanning.

    Discharges the J.1 statement of the same name in
    `L4YAML/Scanner/Linearise.lean`. -/
theorem linearise_append_token
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (t : Positioned YamlToken)
    (h : ∀ e ∈ pendingKeys, e.insertBeforeIdx ≤ tokens.size) :
    ∃ tail, linearise (tokens.push t) pendingKeys
              = linearise tokens pendingKeys ++ tail := by
  refine ⟨#[t], ?_⟩
  -- Strong helper: for all (k, p, acc) with k ≤ tokens.size and p ≤ pks.size,
  --   linearise.go (tokens.push t) pks k p acc = (linearise.go tokens pks k p acc).push t.
  -- Combined with `Array.push_eq_append`, this gives the tail = #[t] equation.
  suffices h' : ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pendingKeys.size - p) = n →
      k ≤ tokens.size → p ≤ pendingKeys.size →
      linearise.go (tokens.push t) pendingKeys k p acc
        = (linearise.go tokens pendingKeys k p acc).push t by
    unfold linearise
    rw [h' _ 0 0 #[] rfl (Nat.zero_le _) (Nat.zero_le _)]
    exact Array.push_eq_append
  intro n
  induction n with
  | zero =>
    intro k p acc h_n h_k_le h_p_le
    have h_k_eq : k = tokens.size := by omega
    have h_p_eq : p = pendingKeys.size := by omega
    subst h_k_eq
    subst h_p_eq
    rw [linearise_go_done tokens pendingKeys tokens.size pendingKeys.size acc
          (Nat.le_refl _) (Nat.le_refl _)]
    rw [linearise.go]
    have hp_neg : ¬ pendingKeys.size < pendingKeys.size := Nat.lt_irrefl _
    have hk_new : tokens.size < (tokens.push t).size := by
      simp [Array.size_push]
    simp only [hp_neg, hk_new, ↓reduceDIte]
    simp only [Array.getElem_push_eq]
    exact linearise_go_done (tokens.push t) pendingKeys (tokens.size + 1) pendingKeys.size
            (acc.push t) (by simp [Array.size_push]) (Nat.le_refl _)
  | succ n ih =>
    intro k p acc h_n h_k_le h_p_le
    by_cases hp : p < pendingKeys.size
    · rw [linearise.go, linearise.go]
      simp only [hp, ↓reduceDIte]
      by_cases hsplice : pendingKeys[p].insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte]
        have h_meas : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
        exact ih k (p + 1) (acc ++ expandKind pendingKeys[p]) h_meas
                h_k_le (by omega)
      · simp only [hsplice, ↓reduceIte]
        have h_e_ip : pendingKeys[p].insertBeforeIdx ≤ tokens.size :=
          h _ (pendingKeys.getElem_mem hp)
        have h_k_lt : k < tokens.size := by omega
        have h_k_lt_new : k < (tokens.push t).size := by
          simp [Array.size_push]; omega
        simp only [h_k_lt, h_k_lt_new, ↓reduceDIte]
        simp only [Array.getElem_push_lt h_k_lt]
        have h_meas : (tokens.size - (k + 1)) + (pendingKeys.size - p) = n := by omega
        exact ih (k + 1) p (acc.push tokens[k]) h_meas (by omega) h_p_le
    · have h_p_eq : p = pendingKeys.size := by omega
      subst h_p_eq
      have h_k_lt : k < tokens.size := by omega
      have h_k_lt_new : k < (tokens.push t).size := by
        simp [Array.size_push]; omega
      rw [linearise.go, linearise.go]
      have hp_neg : ¬ pendingKeys.size < pendingKeys.size := Nat.lt_irrefl _
      simp only [hp_neg, h_k_lt, h_k_lt_new, ↓reduceDIte]
      simp only [Array.getElem_push_lt h_k_lt]
      have h_meas :
          (tokens.size - (k + 1)) + (pendingKeys.size - pendingKeys.size) = n := by omega
      exact ih (k + 1) pendingKeys.size (acc.push tokens[k]) h_meas
              (by omega) (Nat.le_refl _)

/-! ## J.3.2 bridge helpers: spliced-token shape and prefix-stability

These helpers expose the structure of `linearise.go`'s output at the
indices that the flow-aware preservation proofs need to inspect.  They
are purely about `linearise.go` (no `flowNesting`); the consumers in
`Proofs/Production/ScannerPlainScalarValid.lean` combine them with the
existing `flowNesting_*` helpers to derive
`linearise_preserves_FlowContextPSV` and
`linearise_preserves_FlowBracketsMatched`. -/

/-- The token values produced by `expandKind` are always `.key` or
    `.blockMappingStart` — never flow brackets, never plain scalars. -/
theorem expandKind_val_neutral (e : PendingKeyEntry)
    (i : Nat) (h : i < (expandKind e).size) :
    (expandKind e)[i].val = .key ∨ (expandKind e)[i].val = .blockMappingStart := by
  unfold expandKind at *
  match _hk : e.kind, h with
  | .keyOnly, h =>
    simp at h
    have hi : i = 0 := by omega
    subst hi
    simp
  | .blockMappingStartAndKey, h =>
    simp at h
    have hi : i = 0 ∨ i = 1 := by omega
    rcases hi with rfl | rfl
    · simp
    · simp

/-- `linearise.go` is size-monotone: output size ≥ accumulator size. -/
theorem linearise_go_size_mono
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry) :
    ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pks.size - p) = n →
      acc.size ≤ (linearise.go tokens pks k p acc).size := by
  intro n k p acc h_meas
  rw [linearise_go_size tokens pks n k p acc h_meas]
  omega

/-- `linearise.go` extends its accumulator: the output equals
    `acc ++ tail` for some tail.  This is the cleanest prefix-stability
    statement, avoiding dependent-type issues with `[i]'h_size` proofs. -/
theorem linearise_go_extends
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry) :
    ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pks.size - p) = n →
      ∃ tail, linearise.go tokens pks k p acc = acc ++ tail := by
  intro n
  induction n with
  | zero =>
    intro k p acc h_meas
    have h_p : pks.size ≤ p := by omega
    have h_k : tokens.size ≤ k := by omega
    refine ⟨#[], ?_⟩
    rw [linearise_go_done tokens pks k p acc h_k h_p, Array.append_empty]
  | succ n ih =>
    intro k p acc h_meas
    rw [linearise.go]
    by_cases hp : p < pks.size
    · simp only [hp, ↓reduceDIte]
      by_cases hsplice : pks[p].insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte]
        have h_meas' : (tokens.size - k) + (pks.size - (p + 1)) = n := by omega
        obtain ⟨tail', h_tail'⟩ :=
          ih k (p + 1) (acc ++ expandKind pks[p]) h_meas'
        refine ⟨expandKind pks[p] ++ tail', ?_⟩
        rw [h_tail', Array.append_assoc]
      · simp only [hsplice, ↓reduceIte]
        by_cases hk : k < tokens.size
        · simp only [hk, ↓reduceDIte]
          have h_meas' : (tokens.size - (k + 1)) + (pks.size - p) = n := by omega
          obtain ⟨tail', h_tail'⟩ :=
            ih (k + 1) p (acc.push tokens[k]) h_meas'
          refine ⟨#[tokens[k]] ++ tail', ?_⟩
          rw [h_tail']
          show (acc ++ #[tokens[k]]) ++ tail' = acc ++ (#[tokens[k]] ++ tail')
          rw [Array.append_assoc]
        · simp only [hk, ↓reduceDIte]
          have h_meas' : (tokens.size - k) + (pks.size - (p + 1)) = n := by omega
          obtain ⟨tail', h_tail'⟩ :=
            ih k (p + 1) (acc ++ expandKind pks[p]) h_meas'
          refine ⟨expandKind pks[p] ++ tail', ?_⟩
          rw [h_tail', Array.append_assoc]
    · simp only [hp, ↓reduceDIte]
      by_cases hk : k < tokens.size
      · simp only [hk, ↓reduceDIte]
        have h_meas' : (tokens.size - (k + 1)) + (pks.size - p) = n := by omega
        obtain ⟨tail', h_tail'⟩ :=
          ih (k + 1) p (acc.push tokens[k]) h_meas'
        refine ⟨#[tokens[k]] ++ tail', ?_⟩
        rw [h_tail']
        show (acc ++ #[tokens[k]]) ++ tail' = acc ++ (#[tokens[k]] ++ tail')
        rw [Array.append_assoc]
      · exfalso; omega

/-- Top-level `linearise.go` extension: the output equals the
    accumulator concatenated with some tail. -/
theorem linearise_go_eq_acc_append
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (k p : Nat) (acc : Array (Positioned YamlToken)) :
    ∃ tail, linearise.go tokens pks k p acc = acc ++ tail :=
  linearise_go_extends tokens pks _ k p acc rfl

/-- Element-level prefix-stability: `(linearise.go tokens pks k p acc)[i] = acc[i]`
    for `i < acc.size`.  Derived from `linearise_go_eq_acc_append`. -/
theorem linearise_go_getElem_lt_acc
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (k p : Nat) (acc : Array (Positioned YamlToken))
    (i : Nat) (hi : i < acc.size)
    (h_size : i < (linearise.go tokens pks k p acc).size) :
    (linearise.go tokens pks k p acc)[i]'h_size = acc[i] := by
  obtain ⟨tail, h_eq⟩ := linearise_go_eq_acc_append tokens pks k p acc
  have h_size' : i < (acc ++ tail).size := h_eq ▸ h_size
  have : (linearise.go tokens pks k p acc)[i]'h_size = (acc ++ tail)[i]'h_size' := by
    congr 1
  rw [this, Array.getElem_append_left hi]

/-! ## J.3.3 helpers: ValidTokenStream-shape preservation under `linearise`

These lemmas lift the four `ValidTokenStream` invariants from `tokens`
to `linearise tokens pendingKeys`, given appropriate well-formedness
conditions on `pendingKeys`.  Consumed by
`scanFiltered_produces_valid_tokens` in
`Proofs/Scanner/ScannerCorrectness.lean`. -/

/-- `linearise` does not shrink the token array: output size ≥ input size. -/
theorem linearise_size_ge_tokens
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry) :
    (linearise tokens pendingKeys).size ≥ tokens.size := by
  rw [linearise_resolved]
  -- linearise_resolved gives an = with foldl; we want ≥, so show the foldl is ≥ 0.
  have h_foldl_ge :
      pendingKeys.foldl (fun n e => n + (Scanner.expandKind e).size) 0 ≥ 0 := Nat.zero_le _
  omega

/-- If every pending entry has `insertBeforeIdx ≥ 1` and `tokens` is
    nonempty, the first element of `linearise tokens pks` equals
    `tokens[0]`.

    Proof strategy: unfold one step of `linearise.go` from the initial
    `(k=0, p=0, acc=#[])` state.  Under the hypothesis no splice fires
    at index 0, so the first action is `acc.push tokens[0]`.  The
    resulting `acc'` has `tokens[0]` at index 0, and prefix-stability
    (`linearise_go_getElem_lt_acc`) carries this through the rest of
    the recursion. -/
theorem linearise_first_eq_tokens_first
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (h_size : tokens.size > 0)
    (h_pks : ∀ p (h : p < pks.size), 1 ≤ pks[p].insertBeforeIdx) :
    ∃ h_lin : 0 < (linearise tokens pks).size,
      (linearise tokens pks)[0]'h_lin = tokens[0]'h_size := by
  have h_lin_size : (linearise tokens pks).size > 0 :=
    Nat.lt_of_lt_of_le h_size (linearise_size_ge_tokens tokens pks)
  refine ⟨h_lin_size, ?_⟩
  -- Establish: linearise tokens pks = linearise.go tokens pks 1 0 (#[(tokens[0])])
  -- by stepping linearise.go once from k=0, p=0, acc=#[].
  have h_step : linearise tokens pks
        = linearise.go tokens pks 1 0 ((#[] : Array _).push (tokens[0]'h_size)) := by
    unfold linearise
    rw [show linearise.go tokens pks 0 0 #[]
        = linearise.go tokens pks 1 0 ((#[] : Array _).push (tokens[0]'h_size)) from ?_]
    rw [linearise.go]
    by_cases hp : 0 < pks.size
    · simp only [hp, ↓reduceDIte]
      have h_first_pks := h_pks 0 hp
      have h_not_splice : ¬ pks[0].insertBeforeIdx ≤ 0 := by omega
      simp only [h_not_splice, ↓reduceIte, h_size, ↓reduceDIte]
    · simp only [hp, ↓reduceDIte, h_size, ↓reduceDIte]
  -- Use prefix-stability on the stepped form.
  have h_lin_size' : 0 < (linearise.go tokens pks 1 0
      ((#[] : Array _).push (tokens[0]'h_size))).size := by
    have h_mono := linearise_go_size_mono tokens pks
      ((tokens.size - 1) + (pks.size - 0)) 1 0
      ((#[] : Array _).push (tokens[0]'h_size)) (by omega)
    have h_acc_size : ((#[] : Array _).push (tokens[0]'h_size)).size = 1 := by simp
    rw [h_acc_size] at h_mono
    omega
  have h_acc_at_0 : ((#[] : Array _).push (tokens[0]'h_size))[0]'(by simp)
      = tokens[0]'h_size := by simp
  have h_lin_at_0 :
      (linearise.go tokens pks 1 0 ((#[] : Array _).push (tokens[0]'h_size)))[0]'h_lin_size'
        = tokens[0]'h_size := by
    rw [linearise_go_getElem_lt_acc tokens pks 1 0
      ((#[] : Array _).push (tokens[0]'h_size)) 0 (by simp) h_lin_size']
    exact h_acc_at_0
  -- Transport along h_step
  have h_lin_at_0' : (linearise tokens pks)[0]'h_lin_size = tokens[0]'h_size := by
    have h_eq : (linearise tokens pks)[0]'h_lin_size
        = (linearise.go tokens pks 1 0 ((#[] : Array _).push (tokens[0]'h_size)))[0]'h_lin_size' := by
      congr 1 <;> exact h_step
    rw [h_eq]; exact h_lin_at_0
  exact h_lin_at_0'

/-- Equation form of `linearise_append_token`: pushing `t` extends the
    output by exactly `#[t]`.  This is the actual content of
    `linearise_append_token`'s proof body (which uses
    `refine ⟨#[t], ?_⟩`); restating it here lets us read off the
    last element of the result directly. -/
theorem linearise_append_token_eq
    (tokens : Array (Positioned YamlToken))
    (pendingKeys : Array PendingKeyEntry)
    (t : Positioned YamlToken)
    (h : ∀ e ∈ pendingKeys, e.insertBeforeIdx ≤ tokens.size) :
    linearise (tokens.push t) pendingKeys
      = linearise tokens pendingKeys ++ #[t] := by
  -- Strong helper: for all (k, p, acc) with k ≤ tokens.size and p ≤ pks.size,
  --   linearise.go (tokens.push t) pks k p acc = (linearise.go tokens pks k p acc).push t.
  -- Combined with `Array.push_eq_append`, this gives the equation.
  suffices h' : ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pendingKeys.size - p) = n →
      k ≤ tokens.size → p ≤ pendingKeys.size →
      linearise.go (tokens.push t) pendingKeys k p acc
        = (linearise.go tokens pendingKeys k p acc).push t by
    unfold linearise
    rw [h' _ 0 0 #[] rfl (Nat.zero_le _) (Nat.zero_le _)]
    exact Array.push_eq_append
  intro n
  induction n with
  | zero =>
    intro k p acc h_n h_k_le h_p_le
    have h_k_eq : k = tokens.size := by omega
    have h_p_eq : p = pendingKeys.size := by omega
    subst h_k_eq
    subst h_p_eq
    rw [linearise_go_done tokens pendingKeys tokens.size pendingKeys.size acc
          (Nat.le_refl _) (Nat.le_refl _)]
    rw [linearise.go]
    have hp_neg : ¬ pendingKeys.size < pendingKeys.size := Nat.lt_irrefl _
    have hk_new : tokens.size < (tokens.push t).size := by
      simp [Array.size_push]
    simp only [hp_neg, hk_new, ↓reduceDIte]
    simp only [Array.getElem_push_eq]
    exact linearise_go_done (tokens.push t) pendingKeys (tokens.size + 1) pendingKeys.size
            (acc.push t) (by simp [Array.size_push]) (Nat.le_refl _)
  | succ n ih =>
    intro k p acc h_n h_k_le h_p_le
    by_cases hp : p < pendingKeys.size
    · rw [linearise.go, linearise.go]
      simp only [hp, ↓reduceDIte]
      by_cases hsplice : pendingKeys[p].insertBeforeIdx ≤ k
      · simp only [hsplice, ↓reduceIte]
        have h_meas : (tokens.size - k) + (pendingKeys.size - (p + 1)) = n := by omega
        exact ih k (p + 1) (acc ++ expandKind pendingKeys[p]) h_meas
                h_k_le (by omega)
      · simp only [hsplice, ↓reduceIte]
        have h_e_ip : pendingKeys[p].insertBeforeIdx ≤ tokens.size :=
          h _ (pendingKeys.getElem_mem hp)
        have h_k_lt : k < tokens.size := by omega
        have h_k_lt_new : k < (tokens.push t).size := by
          simp [Array.size_push]; omega
        simp only [h_k_lt, h_k_lt_new, ↓reduceDIte]
        simp only [Array.getElem_push_lt h_k_lt]
        have h_meas : (tokens.size - (k + 1)) + (pendingKeys.size - p) = n := by omega
        exact ih (k + 1) p (acc.push tokens[k]) h_meas (by omega) h_p_le
    · have h_p_eq : p = pendingKeys.size := by omega
      subst h_p_eq
      have h_k_lt : k < tokens.size := by omega
      have h_k_lt_new : k < (tokens.push t).size := by
        simp [Array.size_push]; omega
      rw [linearise.go, linearise.go]
      have hp_neg : ¬ pendingKeys.size < pendingKeys.size := Nat.lt_irrefl _
      simp only [hp_neg, h_k_lt, h_k_lt_new, ↓reduceDIte]
      simp only [Array.getElem_push_lt h_k_lt]
      have h_meas :
          (tokens.size - (k + 1)) + (pendingKeys.size - pendingKeys.size) = n := by omega
      exact ih (k + 1) pendingKeys.size (acc.push tokens[k]) h_meas
              (by omega) (Nat.le_refl _)

/-- Round-trip: popping and pushing back the last element yields the
    original array.  Used by `linearise_last_eq_tokens_last`. -/
theorem array_pop_push_back_self
    {α : Type _} (xs : Array α) (h : xs.size > 0) :
    xs.pop.push (xs[xs.size - 1]'(by omega)) = xs := by
  apply Array.ext
  · simp; omega
  · intro i hi₁ hi₂
    by_cases hi : i < xs.size - 1
    · have hi_pop : i < xs.pop.size := by simp; omega
      rw [Array.getElem_push_lt hi_pop]
      simp [Array.getElem_pop]
    · -- i = xs.size - 1
      have hi_eq : i = xs.size - 1 := by
        have : i < xs.size := hi₂
        omega
      subst hi_eq
      have h_pop_size : xs.pop.size = xs.size - 1 := by simp
      simp [Array.getElem_push, h_pop_size]

/-- If every pending entry has `insertBeforeIdx ≤ tokens.size - 1` and
    `tokens` is nonempty, the last element of `linearise tokens pks`
    equals `tokens[tokens.size - 1]`.

    Proof strategy: split `tokens` as `tokens.pop.push tokens[size-1]`
    (via `array_pop_push_back_self`) and apply `linearise_append_token_eq`
    — the bound `insertBeforeIdx ≤ tokens.size - 1 = tokens.pop.size`
    is exactly the hypothesis the append-token lemma needs.  The
    resulting tail is `#[tokens[size-1]]`, so the last element of the
    linearise output equals `tokens[size-1]`. -/
theorem linearise_last_eq_tokens_last
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (h_size : tokens.size > 0)
    (h_pks_le : ∀ p (h : p < pks.size), pks[p].insertBeforeIdx ≤ tokens.size - 1) :
    ∃ h_lin : (linearise tokens pks).size > 0,
      (linearise tokens pks)[(linearise tokens pks).size - 1]'(by omega)
        = tokens[tokens.size - 1]'(by omega) := by
  have h_lin_size_ge : (linearise tokens pks).size ≥ tokens.size :=
    linearise_size_ge_tokens tokens pks
  have h_lin_size_pos : (linearise tokens pks).size > 0 := by omega
  refine ⟨h_lin_size_pos, ?_⟩
  -- Express tokens as tokens.pop.push tokens[size-1].
  have h_pop_push : tokens.pop.push (tokens[tokens.size - 1]'(by omega)) = tokens :=
    array_pop_push_back_self tokens h_size
  have h_pop_size : tokens.pop.size = tokens.size - 1 := by simp
  have h_pks_le_pop : ∀ e ∈ pks, e.insertBeforeIdx ≤ tokens.pop.size := by
    intro e h_mem
    rw [h_pop_size]
    obtain ⟨p, hp, h_eq⟩ := Array.getElem_of_mem h_mem
    rw [← h_eq]
    exact h_pks_le p hp
  -- Apply linearise_append_token_eq with tokens := tokens.pop, t := tokens[size-1].
  have h_eq :=
    linearise_append_token_eq tokens.pop pks (tokens[tokens.size - 1]'(by omega)) h_pks_le_pop
  -- LHS = linearise (tokens.pop.push tokens[size-1]) pks = linearise tokens pks (via h_pop_push).
  rw [h_pop_push] at h_eq
  -- So: linearise tokens pks = linearise tokens.pop pks ++ #[tokens[size-1]].
  -- The last element is therefore tokens[size-1].
  have h_lin_pop_size : (linearise tokens.pop pks).size + 1 = (linearise tokens pks).size := by
    rw [h_eq]; simp
  have h_idx : (linearise tokens pks).size - 1 = (linearise tokens.pop pks).size := by omega
  -- Strategy: rewrite via h_eq, then read off the last element of the append.
  have h_idx_app : (linearise tokens.pop pks).size <
      (linearise tokens.pop pks ++ #[tokens[tokens.size - 1]'(by omega)]).size := by
    simp
  -- The last element of the append is tokens[size-1].
  have h_append_last :
      (linearise tokens.pop pks ++
          #[tokens[tokens.size - 1]'(by omega)])[(linearise tokens.pop pks).size]'h_idx_app
        = tokens[tokens.size - 1]'(by omega) := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    simp
  -- Now combine: the LHS of the goal equals (append)[(linearise tokens.pop pks).size] via h_eq.
  rw [show (linearise tokens pks)[(linearise tokens pks).size - 1]'(by omega) =
      (linearise tokens.pop pks ++
          #[tokens[tokens.size - 1]'(by omega)])[(linearise tokens.pop pks).size]'h_idx_app from ?_]
  · exact h_append_last
  · -- Show the LHS equality using h_eq and h_idx.
    have h_eq_arr : linearise tokens pks
        = linearise tokens.pop pks ++ #[tokens[tokens.size - 1]'(by omega)] := h_eq
    -- Use h_eq_arr to convert LHS array, then h_idx to convert the index.
    have h_idx_via :
        (linearise tokens pks).size - 1 <
          (linearise tokens.pop pks ++ #[tokens[tokens.size - 1]'(by omega)]).size := by
      rw [← h_eq_arr]; omega
    have step1 :
        (linearise tokens pks)[(linearise tokens pks).size - 1]'(by omega)
          = (linearise tokens.pop pks ++
              #[tokens[tokens.size - 1]'(by omega)])[(linearise tokens pks).size - 1]'h_idx_via := by
      congr 1
    rw [step1]
    simp only [h_idx]

/-- Indexing helper: array equality + same index gives element equality. -/
theorem array_get_eq_of_eq {α : Type _} {a b : Array α}
    (h : a = b) (i : Nat) (h1 : i < a.size) (h2 : i < b.size) :
    a[i]'h1 = b[i]'h2 := by subst h; rfl

/-! ## J.3.3 step 8c: `linearise_positions_ordered`

The headline ordering theorem: under the well-formedness conditions
captured by the scanner-side `LineariseFit` invariant (tokens sorted +
pks sorted by `insertBeforeIdx` + pks sorted by `pos.offset` + I1 + I2),
the output of `linearise tokens pks` has non-decreasing `pos.offset`s.

Proof outline:
1. Strong induction on the lex measure `(tokens.size − k) + (pks.size − p)`
   of `linearise.go tokens pks k p acc`.
2. The inductive invariant on `acc`:
   * `acc` is sorted internally (step-1 case-analysis).
   * If `acc.size > 0`, `(acc.back).pos.offset ≤ tokens[k].pos.offset`
     for all `k' ≥ k` with `k' < tokens.size` (compressed to `k`-only
     by `tokens` sortedness).
   * Similarly for `pks` tail.
3. At each recursion step, both branches preserve the invariant:
   * **Splice step** (`pks[p].insertBeforeIdx ≤ k`): new tail has
     constant offset = `pks[p].pos`.  Bridge to old `acc.back` via the
     pks-side invariant; bridge forward via I2 (for tokens) and pks
     pos-sortedness.
   * **Token-push step** (`pks[p].insertBeforeIdx > k`, `k < tokens.size`):
     new last is `tokens[k]`.  Bridge to old `acc.back` via the
     tokens-side invariant; bridge forward via tokens sortedness and I1
     (for pks).
-/

/-- `expandKind` produces a constant-offset run: every token in
    `expandKind e` has `pos.offset = e.pos.offset`. -/
theorem expandKind_offset_const (e : PendingKeyEntry)
    (i : Nat) (hi : i < (Scanner.expandKind e).size) :
    ((Scanner.expandKind e)[i]'hi).pos.offset = e.pos.offset := by
  unfold Scanner.expandKind at *
  match _hk : e.kind, hi with
  | .keyOnly, hi =>
    simp at hi
    have h_i : i = 0 := by omega
    subst h_i
    simp
  | .blockMappingStartAndKey, hi =>
    simp at hi
    have h_i : i = 0 ∨ i = 1 := by omega
    rcases h_i with rfl | rfl
    · simp
    · simp

/-- Sorted-acc invariant for `linearise.go`. Recursion-friendly:
    captures internal sortedness plus the bridge to the next remaining
    `tokens[k]` and `pks[p].pos`. -/
def goSortedInv (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry) (k p : Nat)
    (acc : Array (Positioned YamlToken)) : Prop :=
  -- acc is sorted internally
  (∀ a b (ha : a < acc.size) (hb : b < acc.size), a < b →
    (acc[a]'ha).pos.offset ≤ (acc[b]'hb).pos.offset) ∧
  -- acc.last is bounded by tokens[k]
  (∀ (hk : k < tokens.size) (i : Nat) (hi : i < acc.size),
    (acc[i]'hi).pos.offset ≤ (tokens[k]'hk).pos.offset) ∧
  -- acc.last is bounded by pks[p].pos
  (∀ (hp : p < pks.size) (i : Nat) (hi : i < acc.size),
    (acc[i]'hi).pos.offset ≤ (pks[p]'hp).pos.offset)

/-- `linearise.go` preserves `goSortedInv`, lifting it to a Nat-indexed
    sortedness statement on the output. -/
theorem linearise_go_ordered_helper
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (h_tok_ord : ∀ a b (ha : a < tokens.size) (hb : b < tokens.size), a < b →
      (tokens[a]'ha).pos.offset ≤ (tokens[b]'hb).pos.offset)
    (h_pks_pos : ∀ a b (ha : a < pks.size) (hb : b < pks.size), a < b →
      (pks[a]'ha).pos.offset ≤ (pks[b]'hb).pos.offset)
    (h_lo : ∀ p (hp : p < pks.size) i (hi : i < tokens.size),
      i < (pks[p]'hp).insertBeforeIdx →
      (tokens[i]'hi).pos.offset ≤ (pks[p]'hp).pos.offset)
    (h_hi : ∀ p (hp : p < pks.size) i (hi : i < tokens.size),
      (pks[p]'hp).insertBeforeIdx ≤ i →
      (pks[p]'hp).pos.offset ≤ (tokens[i]'hi).pos.offset) :
    ∀ (n k p : Nat) (acc : Array (Positioned YamlToken)),
      (tokens.size - k) + (pks.size - p) = n →
      goSortedInv tokens pks k p acc →
      ∀ a b (ha : a < (linearise.go tokens pks k p acc).size)
            (hb : b < (linearise.go tokens pks k p acc).size), a < b →
        ((linearise.go tokens pks k p acc)[a]'ha).pos.offset
          ≤ ((linearise.go tokens pks k p acc)[b]'hb).pos.offset := by
  intro n
  induction n with
  | zero =>
    intro k p acc h_meas h_inv
    -- termination case: linearise.go = acc (no more steps)
    have h_k : tokens.size ≤ k := by omega
    have h_p : pks.size ≤ p := by omega
    have h_eq : linearise.go tokens pks k p acc = acc :=
      linearise_go_done tokens pks k p acc h_k h_p
    intro a b ha hb hab
    have ha' : a < acc.size := h_eq ▸ ha
    have hb' : b < acc.size := h_eq ▸ hb
    have h_at_a : (linearise.go tokens pks k p acc)[a]'ha = acc[a]'ha' :=
      array_get_eq_of_eq h_eq a ha ha'
    have h_at_b : (linearise.go tokens pks k p acc)[b]'hb = acc[b]'hb' :=
      array_get_eq_of_eq h_eq b hb hb'
    rw [h_at_a, h_at_b]
    exact h_inv.1 a b ha' hb' hab
  | succ n ih =>
    intro k p acc h_meas h_inv
    obtain ⟨h_acc_ord, h_acc_tok, h_acc_pks⟩ := h_inv
    -- Helper: invariant for the `acc ++ expandKind pks[p]` recursive case.
    have h_inv_splice : ∀ (hp : p < pks.size),
        pks[p].insertBeforeIdx ≤ k ∨ tokens.size ≤ k →
        goSortedInv tokens pks k (p + 1) (acc ++ Scanner.expandKind pks[p]) := by
      intro hp h_or
      refine ⟨?_, ?_, ?_⟩
      · intro a b ha hb hab
        simp only [Array.size_append] at ha hb
        by_cases ha' : a < acc.size
        · by_cases hb' : b < acc.size
          · rw [Array.getElem_append_left ha', Array.getElem_append_left hb']
            exact h_acc_ord a b ha' hb' hab
          · rw [Array.getElem_append_left ha']
            rw [Array.getElem_append_right (Nat.le_of_not_lt hb')]
            rw [expandKind_offset_const pks[p] (b - acc.size) (by omega)]
            exact h_acc_pks hp a ha'
        · have ha'' : acc.size ≤ a := Nat.le_of_not_lt ha'
          have hb'' : acc.size ≤ b := by omega
          rw [Array.getElem_append_right ha'']
          rw [Array.getElem_append_right hb'']
          rw [expandKind_offset_const pks[p] (a - acc.size) (by omega)]
          rw [expandKind_offset_const pks[p] (b - acc.size) (by omega)]
          omega
      · intro hk i hi
        simp only [Array.size_append] at hi
        by_cases h_in_acc : i < acc.size
        · rw [Array.getElem_append_left h_in_acc]
          exact h_acc_tok hk i h_in_acc
        · rw [Array.getElem_append_right (Nat.le_of_not_lt h_in_acc)]
          rw [expandKind_offset_const pks[p] (i - acc.size) (by omega)]
          rcases h_or with hsplice | hbeyond
          · exact h_hi p hp k hk hsplice
          · omega
      · intro hp1 i hi
        simp only [Array.size_append] at hi
        by_cases h_in_acc : i < acc.size
        · rw [Array.getElem_append_left h_in_acc]
          calc (acc[i]'h_in_acc).pos.offset
              ≤ (pks[p]'hp).pos.offset := h_acc_pks hp i h_in_acc
            _ ≤ (pks[p+1]'hp1).pos.offset := h_pks_pos p (p+1) hp hp1 (Nat.lt_succ_self _)
        · rw [Array.getElem_append_right (Nat.le_of_not_lt h_in_acc)]
          rw [expandKind_offset_const pks[p] (i - acc.size) (by omega)]
          exact h_pks_pos p (p+1) hp hp1 (Nat.lt_succ_self _)
    -- Helper: invariant for the `acc.push tokens[k]` recursive case.
    have h_inv_push : ∀ (hk : k < tokens.size),
        (∀ (hp : p < pks.size), k < pks[p].insertBeforeIdx) →
        goSortedInv tokens pks (k + 1) p (acc.push (tokens[k]'hk)) := by
      intro hk h_idx_gt
      refine ⟨?_, ?_, ?_⟩
      · intro a b ha hb hab
        simp only [Array.size_push] at ha hb
        by_cases ha' : a < acc.size
        · by_cases hb' : b < acc.size
          · rw [Array.getElem_push_lt ha', Array.getElem_push_lt hb']
            exact h_acc_ord a b ha' hb' hab
          · have hb_eq : b = acc.size := by omega
            rw [Array.getElem_push_lt ha']
            rw [show ((acc.push (tokens[k]'hk))[b]'(by simp [Array.size_push]; omega)) =
                ((acc.push (tokens[k]'hk))[acc.size]'(by simp [Array.size_push])) from by
              congr 1]
            rw [Array.getElem_push_eq]
            exact h_acc_tok hk a ha'
        · omega
      · intro hk1 i hi
        simp only [Array.size_push] at hi
        by_cases h_in_acc : i < acc.size
        · rw [Array.getElem_push_lt h_in_acc]
          calc (acc[i]'h_in_acc).pos.offset
              ≤ (tokens[k]'hk).pos.offset := h_acc_tok hk i h_in_acc
            _ ≤ (tokens[k+1]'hk1).pos.offset :=
                h_tok_ord k (k+1) hk hk1 (Nat.lt_succ_self _)
        · have hi_eq : i = acc.size := by omega
          subst hi_eq
          rw [Array.getElem_push_eq]
          exact h_tok_ord k (k+1) hk hk1 (Nat.lt_succ_self _)
      · intro hp i hi
        simp only [Array.size_push] at hi
        by_cases h_in_acc : i < acc.size
        · rw [Array.getElem_push_lt h_in_acc]
          exact h_acc_pks hp i h_in_acc
        · have hi_eq : i = acc.size := by omega
          subst hi_eq
          rw [Array.getElem_push_eq]
          exact h_lo p hp k hk (h_idx_gt hp)
    rw [linearise.go]
    by_cases hp : p < pks.size
    · simp only [hp, ↓reduceDIte]
      by_cases hsplice : pks[p].insertBeforeIdx ≤ k
      · -- Splice branch
        simp only [hsplice, ↓reduceIte]
        have h_meas' : (tokens.size - k) + (pks.size - (p + 1)) = n := by omega
        apply ih k (p + 1) (acc ++ Scanner.expandKind pks[p]) h_meas'
        exact h_inv_splice hp (Or.inl hsplice)
      · simp only [hsplice, ↓reduceIte]
        by_cases hk : k < tokens.size
        · -- Token-push branch
          simp only [hk, ↓reduceDIte]
          have h_meas' : (tokens.size - (k + 1)) + (pks.size - p) = n := by omega
          apply ih (k + 1) p (acc.push tokens[k]) h_meas'
          exact h_inv_push hk (fun _ => Nat.lt_of_not_le hsplice)
        · -- Splice-at-tail branch (k ≥ tokens.size)
          simp only [hk, ↓reduceDIte]
          have h_meas' : (tokens.size - k) + (pks.size - (p + 1)) = n := by omega
          apply ih k (p + 1) (acc ++ Scanner.expandKind pks[p]) h_meas'
          exact h_inv_splice hp (Or.inr (Nat.le_of_not_lt hk))
    · -- p ≥ pks.size: only tokens-push remaining or termination
      simp only [hp, ↓reduceDIte]
      by_cases hk : k < tokens.size
      · simp only [hk, ↓reduceDIte]
        have h_meas' : (tokens.size - (k + 1)) + (pks.size - p) = n := by omega
        apply ih (k + 1) p (acc.push tokens[k]) h_meas'
        exact h_inv_push hk (fun hp_lt => absurd hp_lt hp)
      · -- termination: linearise.go tokens pks k p acc = acc
        simp only [hk, ↓reduceDIte]
        intro a b ha hb hab
        exact h_acc_ord a b ha hb hab

/-- **Headline ordering theorem (J.3.3)**: `linearise tokens pks` is
    sorted in `pos.offset` provided `tokens` is sorted, `pks` is sorted
    in both `insertBeforeIdx` and `pos.offset`, and the I1/I2 fit
    conditions hold between tokens and pks. -/
theorem linearise_positions_ordered
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (h_tok_ord : ∀ a b (ha : a < tokens.size) (hb : b < tokens.size), a < b →
      (tokens[a]'ha).pos.offset ≤ (tokens[b]'hb).pos.offset)
    (h_pks_pos : ∀ a b (ha : a < pks.size) (hb : b < pks.size), a < b →
      (pks[a]'ha).pos.offset ≤ (pks[b]'hb).pos.offset)
    (h_lo : ∀ p (hp : p < pks.size) i (hi : i < tokens.size),
      i < (pks[p]'hp).insertBeforeIdx →
      (tokens[i]'hi).pos.offset ≤ (pks[p]'hp).pos.offset)
    (h_hi : ∀ p (hp : p < pks.size) i (hi : i < tokens.size),
      (pks[p]'hp).insertBeforeIdx ≤ i →
      (pks[p]'hp).pos.offset ≤ (tokens[i]'hi).pos.offset) :
    ∀ a b (ha : a < (linearise tokens pks).size) (hb : b < (linearise tokens pks).size),
      a < b →
      ((linearise tokens pks)[a]'ha).pos.offset ≤ ((linearise tokens pks)[b]'hb).pos.offset := by
  intro a b ha hb hab
  -- Initial accumulator is empty; goSortedInv holds vacuously.
  have h_init : goSortedInv tokens pks 0 0 #[] := by
    refine ⟨?_, ?_, ?_⟩
    · intro a b ha _ _; simp at ha
    · intro _ i hi; simp at hi
    · intro _ i hi; simp at hi
  exact linearise_go_ordered_helper tokens pks h_tok_ord h_pks_pos h_lo h_hi
    _ 0 0 #[] rfl h_init a b ha hb hab

/-! ## J.4 cascade helper

Bridge between the post-cutover `linearise` shape and the legacy
`tokens.filter (· != .placeholder)` shape used by Tier 1 derivations
in `Proofs/Output/EmitterScannability.lean`.  The bridge holds under
two pre-conditions:

* every pending entry is `.unresolved` (so `linearise` performs no
  splice, via `linearise_all_unresolved`); and
* `tokens` contains no `.placeholder` token (so `Array.filter_eq_self`
  collapses the filter to identity).

The all-unresolved hypothesis fails whenever a `:`-resolution has fired
during scanning — i.e. whenever the input contains a flow or block
mapping pair (`{k: v}`, `k: v`).  Consumers that need the bridge for
inputs containing flow maps must split on item shape and use direct
`linearise` positional reasoning (`linearise_first_eq_tokens_first`,
`linearise_last_eq_tokens_last`) for the resolved case. -/
theorem linearise_eq_filter_no_resolutions
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (h_unres : ∀ e ∈ pks, e.kind = .unresolved)
    (h_no_pl : ∀ t ∈ tokens, t.val ≠ .placeholder) :
    linearise tokens pks = tokens.filter (fun t => t.val != .placeholder) := by
  rw [linearise_all_unresolved tokens pks h_unres]
  symm
  apply (Array.filter_eq_self).mpr
  intro t h_mem
  have h_ne : t.val ≠ .placeholder := h_no_pl t h_mem
  simp [bne_iff_ne, h_ne]

/-! ## J.4.2 cascade infrastructure: linearise streamEnd push commutes

When a token is appended to `tokens` and every pending entry's
`insertBeforeIdx` is bounded by the original `tokens.size`, the linearised
output simply has the new token appended at the end.  This is the `.push`
form of `linearise_append_token_eq`, more convenient for cascade consumers
that want to peel off the trailing `streamEnd` token before applying
positional lemmas like `linearise_last_eq_tokens_last` to the inner
`linearise s.tokens s.pendingKeys`.

The bound `e.insertBeforeIdx ≤ tokens.size` matches the upper half of
`PendingKeysWellIndexed`, which is propagated through `scanLoopFull` by
`scanLoopFull_preserves_PendingKeysWellIndexed`.  Combined with that
propagation, this lemma lets cascade consumers extract clean structural
facts about `linearise (s.tokens.push streamEnd) s.pendingKeys` from the
chain hypotheses without needing a separate no-placeholder invariant. -/
theorem linearise_push_eq_push_linearise
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (t : Positioned YamlToken)
    (h : ∀ e ∈ pks, e.insertBeforeIdx ≤ tokens.size) :
    linearise (tokens.push t) pks = (linearise tokens pks).push t := by
  rw [linearise_append_token_eq tokens pks t h]
  exact Array.push_eq_append.symm

/-- If every pending entry has `insertBeforeIdx ≥ 2` and `tokens.size ≥ 2`,
    the second element of `linearise tokens pks` equals `tokens[1]`.

    Proof strategy: step `linearise.go` twice from `(k=0, p=0, acc=#[])`.
    The hypothesis `2 ≤ pks[p].insertBeforeIdx` ensures no splice fires at
    indices 0 or 1, so the first two actions are `acc.push tokens[0]` then
    `acc.push tokens[1]`.  The accumulator after two steps has `tokens[1]`
    at index 1, and prefix-stability (`linearise_go_getElem_lt_acc`) carries
    this through the rest of the recursion.

    At `scanFiltered`, the earliest `saveSimpleKey` registers a pending key
    only after `[streamStart, flowSequenceStart]` (or block analogue) have
    been emitted, i.e. when `s.tokens.size = 2`, so this hypothesis holds
    for every step downstream.  Used by the seq/map cascade consumers in
    `Proofs/Output/EmitterScannability.lean` to read off the
    `flowSequenceStart` / `blockMappingStart` token at index 1. -/
theorem linearise_second_eq_tokens_second
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (h_size : tokens.size ≥ 2)
    (h_pks : ∀ p (h : p < pks.size), 2 ≤ pks[p].insertBeforeIdx) :
    ∃ h_lin : 1 < (linearise tokens pks).size,
      (linearise tokens pks)[1]'h_lin = tokens[1]'h_size := by
  have h_size0 : 0 < tokens.size := by omega
  have h_size1 : 1 < tokens.size := by omega
  have h_lin_size_ge : (linearise tokens pks).size ≥ tokens.size :=
    linearise_size_ge_tokens tokens pks
  have h_lin_size : 1 < (linearise tokens pks).size := by omega
  refine ⟨h_lin_size, ?_⟩
  -- Step linearise.go twice from (0,0,#[]):
  --   (0,0,#[]) → (1,0,#[tokens[0]]) → (2,0,#[tokens[0], tokens[1]])
  have h_step : linearise tokens pks
        = linearise.go tokens pks 2 0
            (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1)) := by
    unfold linearise
    rw [linearise.go]
    by_cases hp : 0 < pks.size
    · simp only [hp, ↓reduceDIte]
      have h_pks0 := h_pks 0 hp
      have h_not_splice0 : ¬ pks[0].insertBeforeIdx ≤ 0 := by omega
      simp only [h_not_splice0, ↓reduceIte, h_size0, ↓reduceDIte]
      rw [linearise.go]
      simp only [hp, ↓reduceDIte]
      have h_not_splice1 : ¬ pks[0].insertBeforeIdx ≤ 1 := by omega
      simp only [h_not_splice1, ↓reduceIte, h_size1, ↓reduceDIte]
    · simp only [hp, ↓reduceDIte, h_size0, ↓reduceDIte]
      rw [linearise.go]
      simp only [hp, ↓reduceDIte, h_size1, ↓reduceDIte]
  -- Use prefix-stability on the stepped form: acc[1] = tokens[1]
  have h_acc_size :
      (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1)).size = 2 := by simp
  have h_acc_at_1 :
      (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1))[1]'(by simp)
        = tokens[1]'h_size1 := by simp
  have h_lin_size' : 1 < (linearise.go tokens pks 2 0
      (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1))).size := by
    have h_mono := linearise_go_size_mono tokens pks
      ((tokens.size - 2) + (pks.size - 0)) 2 0
      (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1)) (by omega)
    rw [h_acc_size] at h_mono
    omega
  have h_lin_at_1 :
      (linearise.go tokens pks 2 0
        (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1)))[1]'h_lin_size'
        = tokens[1]'h_size1 := by
    rw [linearise_go_getElem_lt_acc tokens pks 2 0
      (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1)) 1
      (by simp) h_lin_size']
    exact h_acc_at_1
  -- Transport along h_step
  have h_eq : (linearise tokens pks)[1]'h_lin_size
      = (linearise.go tokens pks 2 0
          (((#[] : Array _).push (tokens[0]'h_size0)).push (tokens[1]'h_size1)))[1]'h_lin_size' := by
    congr 1 <;> exact h_step
  rw [h_eq]; exact h_lin_at_1

/-- Second-to-last positional readout: when a trailing token `t` (typically
    `streamEnd`) is pushed onto `tokens` and every pending entry's
    `insertBeforeIdx` is bounded by `tokens.size - 1`, the second-to-last
    element of `linearise (tokens.push t) pks` equals `tokens[tokens.size - 1]`.

    Proof strategy: a one-step composition.  `linearise_push_eq_push_linearise`
    peels the trailing `t` push to expose `(linearise tokens pks).push t`, then
    `Array.getElem_push_lt` reads the second-to-last index as
    `(linearise tokens pks)[size - 1]`, which equals `tokens[tokens.size - 1]`
    by `linearise_last_eq_tokens_last`.  The `pks ≤ tokens.size - 1` bound
    feeds both: it implies the `≤ tokens.size` bound `linearise_push_eq_…`
    needs and is exactly what `linearise_last_eq_…` requires.

    Consumed by the seq/map cascade in `Proofs/Output/EmitterScannability.lean`
    to read `tokens[tokens.size - 2]` (the closing `flowSequenceEnd` /
    `blockMappingEnd`) on the post-`streamEnd` linearised output. -/
theorem linearise_secondLast_eq_tokens_last_inner
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (t : Positioned YamlToken)
    (h_size : tokens.size > 0)
    (h_pks_le : ∀ p (h : p < pks.size), pks[p].insertBeforeIdx ≤ tokens.size - 1) :
    ∃ h_lin : (linearise (tokens.push t) pks).size ≥ 2,
      (linearise (tokens.push t) pks)[(linearise (tokens.push t) pks).size - 2]'(by omega)
        = tokens[tokens.size - 1]'(by omega) := by
  -- The bound `≤ tokens.size - 1` implies the weaker `≤ tokens.size` that
  -- `linearise_push_eq_push_linearise` needs.
  have h_pks_le_size : ∀ e ∈ pks, e.insertBeforeIdx ≤ tokens.size := by
    intro e h_mem
    obtain ⟨p, hp, h_eq⟩ := Array.getElem_of_mem h_mem
    rw [← h_eq]
    have := h_pks_le p hp
    omega
  -- Peel the trailing push.
  have h_push : linearise (tokens.push t) pks = (linearise tokens pks).push t :=
    linearise_push_eq_push_linearise tokens pks t h_pks_le_size
  -- Inner last element via `linearise_last_eq_tokens_last`.
  obtain ⟨_h_lin_inner_pos, h_lin_inner_last⟩ :=
    linearise_last_eq_tokens_last tokens pks h_size h_pks_le
  -- Size facts.
  have h_inner_pos : (linearise tokens pks).size > 0 :=
    Nat.lt_of_lt_of_le h_size (linearise_size_ge_tokens tokens pks)
  have h_inner_lt : (linearise tokens pks).size - 1 < (linearise tokens pks).size := by omega
  have h_lin_size_ge : (linearise (tokens.push t) pks).size ≥ 2 := by
    rw [h_push]; simp; omega
  refine ⟨h_lin_size_ge, ?_⟩
  -- Dependent indices defeat `rw [h_push]`.  Sidestep by generalising over an
  -- array propositionally equal to the inner-push form, then `subst` makes the
  -- subsequent rewrites work without dependent-motive issues.
  suffices h_gen : ∀ (arr : Array (Positioned YamlToken))
      (h_eq : arr = (linearise tokens pks).push t)
      (h_arr_size : arr.size ≥ 2),
      arr[arr.size - 2]'(by omega) = tokens[tokens.size - 1]'(by omega) by
    exact h_gen (linearise (tokens.push t) pks) h_push h_lin_size_ge
  intro arr h_eq h_arr_size
  subst h_eq
  -- Goal: ((linearise tokens pks).push t)[((linearise tokens pks).push t).size - 2]'… = tokens[…]
  -- Apply `Array.getElem_push_lt` with the unreduced index, then simplify the
  -- inner array's index from `(inner.size + 1) - 2` to `inner.size - 1`.
  have h_idx_lt :
      ((linearise tokens pks).push t).size - 2 < (linearise tokens pks).size := by
    simp; omega
  rw [Array.getElem_push_lt h_idx_lt]
  -- Goal: (linearise tokens pks)[((linearise tokens pks).push t).size - 2]'_ = tokens[…]
  have h_idx_simpl : ((linearise tokens pks).push t).size - 2
      = (linearise tokens pks).size - 1 := by simp
  simp only [h_idx_simpl]
  exact h_lin_inner_last

/-- Prefix readout: for any `i ≤ tokens.size`, if every pending entry's
    `insertBeforeIdx` is at least `i` (no splice fires within the first
    `i` slots), then the first `i` elements of `linearise tokens pks` agree
    pointwise with the first `i` elements of `tokens`.

    Proof strategy: induct on `k` (the number of `linearise.go` steps already
    taken from the initial state).  At each step from `(k, 0, acc)` to
    `(k+1, 0, acc.push tokens[k])`, the splice test `pks[0].insertBeforeIdx ≤ k`
    is false (since `insertBeforeIdx ≥ i > k`), so `linearise.go` pushes
    `tokens[k]` and recurses.  After `i` such steps, prefix-stability
    (`linearise_go_getElem_lt_acc`) reads off `tokens[0]`, …, `tokens[i-1]`.

    Generalises `linearise_first_eq_tokens_first` (the `i = 1` case) and the
    index-1 readout from `linearise_second_eq_tokens_second` (the `i = 2`
    case).  Used by the seq/map cascade in `Proofs/Output/EmitterScannability`
    to read off boundary tokens (`streamStart`, `flowSequenceStart` /
    `blockMappingStart`, …) at multiple low indices uniformly. -/
theorem linearise_prefix_eq_tokens_prefix
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (i : Nat)
    (h_i : i ≤ tokens.size)
    (h_pks : ∀ p (h : p < pks.size), i ≤ pks[p].insertBeforeIdx) :
    ∃ (h_lin : i ≤ (linearise tokens pks).size),
      ∀ (j : Nat) (hj : j < i),
        (linearise tokens pks)[j]'(Nat.lt_of_lt_of_le hj h_lin)
          = tokens[j]'(Nat.lt_of_lt_of_le hj h_i) := by
  -- Inductive helper: for every `k ≤ i`, there is an accumulator of size `k`
  -- whose contents are the first `k` tokens, and such that
  -- `linearise tokens pks = linearise.go tokens pks k 0 acc`.  The size
  -- equality is exposed as a separate existential binder so that the
  -- agreement clause can index `acc[j]` with a derived proof.
  suffices h_step : ∀ (k : Nat) (h_k_le : k ≤ i),
      ∃ (acc : Array (Positioned YamlToken)) (h_acc_size : acc.size = k),
        (∀ (j : Nat) (hj : j < acc.size),
          acc[j]'hj = tokens[j]'(by omega)) ∧
        linearise tokens pks = linearise.go tokens pks k 0 acc by
    obtain ⟨acc, h_acc_size, h_acc_at, h_eq⟩ := h_step i (Nat.le_refl _)
    have h_mono := linearise_go_size_mono tokens pks
      ((tokens.size - i) + (pks.size - 0)) i 0 acc rfl
    rw [h_acc_size] at h_mono
    have h_lin_ge : i ≤ (linearise tokens pks).size := by rw [h_eq]; exact h_mono
    refine ⟨h_lin_ge, ?_⟩
    intro j hj
    have h_acc_lt : j < acc.size := by rw [h_acc_size]; exact hj
    have h_lin_size_ge : j < (linearise.go tokens pks i 0 acc).size := by omega
    have h_at_acc :
        (linearise.go tokens pks i 0 acc)[j]'h_lin_size_ge = acc[j]'h_acc_lt :=
      linearise_go_getElem_lt_acc tokens pks i 0 acc j h_acc_lt h_lin_size_ge
    have h_at_lin : (linearise tokens pks)[j]'(Nat.lt_of_lt_of_le hj h_lin_ge)
        = (linearise.go tokens pks i 0 acc)[j]'h_lin_size_ge := by
      congr 1 <;> exact h_eq
    rw [h_at_lin, h_at_acc]
    exact h_acc_at j h_acc_lt
  intro k h_k_le
  induction k with
  | zero =>
    refine ⟨#[], by simp, ?_, ?_⟩
    · intro j hj; simp at hj
    · unfold linearise; rfl
  | succ k ih =>
    obtain ⟨acc, h_acc_size, h_acc_at, h_eq⟩ := ih (by omega)
    have h_k_lt : k < tokens.size := by omega
    -- Step linearise.go from (k, 0, acc) to (k+1, 0, acc.push tokens[k]):
    -- since pks[0].insertBeforeIdx ≥ i > k, no splice fires at index k.
    have h_step_one : linearise.go tokens pks k 0 acc
        = linearise.go tokens pks (k+1) 0 (acc.push (tokens[k]'h_k_lt)) := by
      rw [linearise.go]
      by_cases hp : 0 < pks.size
      · simp only [hp, ↓reduceDIte]
        have h_pks_0 := h_pks 0 hp
        have h_not_splice : ¬ pks[0].insertBeforeIdx ≤ k := by omega
        simp only [h_not_splice, ↓reduceIte, h_k_lt, ↓reduceDIte]
      · simp only [hp, ↓reduceDIte, h_k_lt, ↓reduceDIte]
    refine ⟨acc.push (tokens[k]'h_k_lt), ?_, ?_, ?_⟩
    · simp [h_acc_size]
    · intro j hj
      have h_size_succ : (acc.push (tokens[k]'h_k_lt)).size = k + 1 := by
        simp [h_acc_size]
      have hj' : j < k + 1 := h_size_succ ▸ hj
      by_cases h_lt : j < k
      · have h_lt_acc : j < acc.size := by rw [h_acc_size]; exact h_lt
        rw [Array.getElem_push_lt h_lt_acc]
        exact h_acc_at j h_lt_acc
      · have h_eq_k : j = k := by omega
        subst h_eq_k
        have h_not_lt : ¬ j < acc.size := by rw [h_acc_size]; omega
        simp [Array.getElem_push, h_not_lt]
    · rw [h_eq, h_step_one]

/-- **Foundation A for J.4.2.b-2d-key (linearise-shape pair body, Part 2)**:
    when the first pending key entry is `.keyOnly` with
    `insertBeforeIdx = j ≤ tokens.size`, the linearised output has `.key`
    at index `j`.

    Proof sketch (adapted from `linearise_prefix_eq_tokens_prefix`):
    1. Walk `linearise.go` from `(0, 0, #[])` to `(j, 0, tokens[0..j])`
       without firing any splices: at each `k < j`, `pks[0].insertBeforeIdx
       = j > k`, so the splice test fails and `linearise.go` copies
       `tokens[k]`.
    2. At `(j, 0, tokens[0..j])`, the splice test `pks[0].insertBeforeIdx
       ≤ j` holds, so `linearise.go` recurses to `(j, 1, tokens[0..j] ++
       expandKind pks[0])`.  Since `pks[0].kind = .keyOnly`, `expandKind
       pks[0] = #[⟨pos, .key, pos⟩]`, so the new accumulator's index `j`
       is `.key`.
    3. Subsequent `linearise.go` iterations only push at indices `> j`,
       so prefix-stability (`linearise_go_getElem_lt_acc`) reads
       `linearise[j] = .key` off the post-splice accumulator.

    Used by the resolution-case body characterization
    (`emitPairList_body_linearise_characterization`) to discharge
    Part (2) (`linearise[old_sz].val = .key`) once chain-side accounting
    establishes that `s'.pendingKeys[0].kind = .keyOnly` and
    `s'.pendingKeys[0].insertBeforeIdx = s.tokens.size`. -/
theorem linearise_first_splice_keyonly
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (j : Nat)
    (h_j_le : j ≤ tokens.size)
    (h_pks_pos : 0 < pks.size)
    (h_first_idx : pks[0].insertBeforeIdx = j)
    (h_first_kind : pks[0].kind = .keyOnly) :
    ∃ (h_lin : j < (linearise tokens pks).size),
      ((linearise tokens pks)[j]'h_lin).val = .key := by
  -- Build acc of size j with prefix tokens[0..j] via the no-splice walk.
  suffices h_walk : ∃ (acc : Array (Positioned YamlToken)) (_ : acc.size = j),
      linearise tokens pks = linearise.go tokens pks j 0 acc by
    obtain ⟨acc, h_acc_size, h_eq⟩ := h_walk
    -- Step linearise.go once more: splice pks[0] (test fires since
    -- pks[0].insertBeforeIdx = j ≤ j).
    have h_splice_le : pks[0].insertBeforeIdx ≤ j :=
      h_first_idx ▸ Nat.le_refl _
    have h_step_splice :
        linearise.go tokens pks j 0 acc
          = linearise.go tokens pks j 1 (acc ++ expandKind pks[0]) := by
      rw [linearise.go]
      simp only [h_pks_pos, ↓reduceDIte, h_splice_le, ↓reduceIte]
    -- expandKind pks[0] = #[⟨pks[0].pos, .key, pks[0].pos⟩] since kind = .keyOnly.
    have h_expand_eq : expandKind pks[0]
        = (#[⟨pks[0].pos, .key, pks[0].pos⟩] : Array (Positioned YamlToken)) := by
      simp [expandKind, h_first_kind]
    -- (acc ++ expandKind pks[0]).size = j + 1.
    have h_expand_size : (expandKind pks[0]).size = 1 := by
      rw [h_expand_eq]; rfl
    have h_acc_ext_size : (acc ++ expandKind pks[0]).size = j + 1 := by
      rw [Array.size_append, h_acc_size, h_expand_size]
    have h_j_lt_acc_ext : j < (acc ++ expandKind pks[0]).size := by
      rw [h_acc_ext_size]; omega
    -- (acc ++ expandKind pks[0])[j].val = .key.
    have h_acc_ext_at_j : ((acc ++ expandKind pks[0])[j]'h_j_lt_acc_ext).val = .key := by
      have h_acc_le_j : acc.size ≤ j := h_acc_size ▸ Nat.le_refl _
      rw [Array.getElem_append_right h_acc_le_j]
      -- Now goal: (expandKind pks[0])[j - acc.size]'_.val = .key.
      have h_idx_zero : j - acc.size = 0 := by rw [h_acc_size]; omega
      simp only [h_idx_zero, h_expand_eq]
      rfl
    -- linearise.go from (j, 1, acc ++ expandKind pks[0]) is monotone; index j is preserved.
    have h_mono := linearise_go_size_mono tokens pks
      ((tokens.size - j) + (pks.size - 1)) j 1 (acc ++ expandKind pks[0]) rfl
    rw [h_acc_ext_size] at h_mono
    have h_j_lt_lin' :
        j < (linearise.go tokens pks j 1 (acc ++ expandKind pks[0])).size := h_mono
    have h_at_acc :
        (linearise.go tokens pks j 1 (acc ++ expandKind pks[0]))[j]'h_j_lt_lin'
          = (acc ++ expandKind pks[0])[j]'h_j_lt_acc_ext :=
      linearise_go_getElem_lt_acc tokens pks j 1 (acc ++ expandKind pks[0]) j
        h_j_lt_acc_ext h_j_lt_lin'
    -- Transport along h_eq + h_step_splice.
    have h_lin_eq : linearise tokens pks
        = linearise.go tokens pks j 1 (acc ++ expandKind pks[0]) := by
      rw [h_eq, h_step_splice]
    have h_j_lt_lin : j < (linearise tokens pks).size := by
      rw [h_lin_eq]; exact h_j_lt_lin'
    refine ⟨h_j_lt_lin, ?_⟩
    have h_lin_at_j : (linearise tokens pks)[j]'h_j_lt_lin
        = (linearise.go tokens pks j 1 (acc ++ expandKind pks[0]))[j]'h_j_lt_lin' := by
      congr 1 <;> exact h_lin_eq
    rw [h_lin_at_j, h_at_acc]
    exact h_acc_ext_at_j
  -- Walk linearise.go from (0, 0, #[]) to (j, 0, tokens[0..j]) without
  -- firing any splices.  Proof by induction on `k ≤ j`.
  suffices h_step : ∀ (k : Nat) (_ : k ≤ j),
      ∃ (acc : Array (Positioned YamlToken)) (_ : acc.size = k),
        linearise tokens pks = linearise.go tokens pks k 0 acc by
    exact h_step j (Nat.le_refl _)
  intro k h_k_le
  induction k with
  | zero =>
    refine ⟨#[], by simp, ?_⟩
    unfold linearise; rfl
  | succ k ih =>
    obtain ⟨acc, h_acc_size, h_eq⟩ := ih (by omega)
    have h_k_lt : k < tokens.size := by omega
    have h_step_one : linearise.go tokens pks k 0 acc
        = linearise.go tokens pks (k+1) 0 (acc.push (tokens[k]'h_k_lt)) := by
      rw [linearise.go]
      simp only [h_pks_pos, ↓reduceDIte]
      have h_not_splice : ¬ pks[0].insertBeforeIdx ≤ k := by
        rw [h_first_idx]; omega
      simp only [h_not_splice, ↓reduceIte, h_k_lt, ↓reduceDIte]
    refine ⟨acc.push (tokens[k]'h_k_lt), ?_, ?_⟩
    · simp [h_acc_size]
    · rw [h_eq, h_step_one]

/-- **Foundation B for J.4.2.b-2d-key (linearise-shape pair body, Part 3)**:
    when `linearise tokens pks` has reached state `(j, p, acc)` (witnessed
    by a transport equation `linearise tokens pks = linearise.go tokens pks j p acc`)
    and the next pending key splice fires with `.keyOnly` kind, position
    `acc.size` of the linearised output is `.key`.

    Companion to `linearise_first_splice_keyonly` (Foundation A): Foundation
    A indexes from the start (walks `(0, 0, #[]) → (j, 0, tokens[0..j])`
    internally, then fires `pks[0]`); Foundation B is the splice mechanic
    in isolation — it doesn't know how the walk reached `(j, p, acc)`,
    leaving that to chain-side accounting (J.4.2.b-2d-key-chain).

    Used by `emitPairList_body_linearise_characterization` Part (3) to
    discharge the after-flowEntry-key claim: chain-side accounting supplies
    the `(j, p, acc)` state with `acc.size = k + 1` (where `acc[k] =
    .flowEntry`) and the splice precondition (`pks[p].insertBeforeIdx ≤ j`,
    `pks[p].kind = .keyOnly`); Foundation B reads off `linearise[k+1] = .key`.

    Proof structure (mirrors the inner half of Foundation A):
    1. Step `linearise.go` once from `(j, p, acc)` to fire the splice:
       result is `linearise.go tokens pks j (p+1) (acc ++ expandKind pks[p])`.
    2. Since `pks[p].kind = .keyOnly`, `expandKind pks[p] = #[⟨pos, .key, pos⟩]`,
       so `(acc ++ expandKind pks[p])[acc.size].val = .key`.
    3. Prefix-stability (`linearise_go_getElem_lt_acc`) carries this to
       `(linearise.go tokens pks j (p+1) (acc ++ expandKind pks[p]))[acc.size]`.
    4. Transport via `h_eq` and the step equation gives the result on
       `linearise tokens pks`. -/
theorem linearise_splice_keyonly_at
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (j p : Nat)
    (acc : Array (Positioned YamlToken))
    (h_eq : linearise tokens pks = linearise.go tokens pks j p acc)
    (h_p : p < pks.size)
    (h_splice_fires : pks[p].insertBeforeIdx ≤ j)
    (h_kind : pks[p].kind = .keyOnly) :
    ∃ (h_lin : acc.size < (linearise tokens pks).size),
      ((linearise tokens pks)[acc.size]'h_lin).val = .key := by
  -- Step 1: fire the splice.
  have h_step_splice :
      linearise.go tokens pks j p acc
        = linearise.go tokens pks j (p + 1) (acc ++ expandKind pks[p]) := by
    rw [linearise.go]
    simp only [h_p, ↓reduceDIte, h_splice_fires, ↓reduceIte]
  -- Step 2: expandKind pks[p] = #[⟨pks[p].pos, .key, pks[p].pos⟩].
  have h_expand_eq : expandKind pks[p]
      = (#[⟨pks[p].pos, .key, pks[p].pos⟩] : Array (Positioned YamlToken)) := by
    simp [expandKind, h_kind]
  have h_expand_size : (expandKind pks[p]).size = 1 := by
    rw [h_expand_eq]; rfl
  have h_acc_ext_size : (acc ++ expandKind pks[p]).size = acc.size + 1 := by
    rw [Array.size_append, h_expand_size]
  have h_acc_lt_acc_ext : acc.size < (acc ++ expandKind pks[p]).size := by
    rw [h_acc_ext_size]; omega
  have h_acc_ext_at_acc :
      ((acc ++ expandKind pks[p])[acc.size]'h_acc_lt_acc_ext).val = .key := by
    rw [Array.getElem_append_right (Nat.le_refl _)]
    have h_idx_zero : acc.size - acc.size = 0 := Nat.sub_self _
    simp only [h_idx_zero, h_expand_eq]
    rfl
  -- Step 3: prefix-stability carries the readout through linearise.go from (j, p+1).
  have h_mono := linearise_go_size_mono tokens pks
    ((tokens.size - j) + (pks.size - (p + 1))) j (p + 1) (acc ++ expandKind pks[p]) rfl
  rw [h_acc_ext_size] at h_mono
  have h_lt_lin' :
      acc.size < (linearise.go tokens pks j (p + 1) (acc ++ expandKind pks[p])).size := h_mono
  have h_at_acc :
      (linearise.go tokens pks j (p + 1) (acc ++ expandKind pks[p]))[acc.size]'h_lt_lin'
        = (acc ++ expandKind pks[p])[acc.size]'h_acc_lt_acc_ext :=
    linearise_go_getElem_lt_acc tokens pks j (p + 1) (acc ++ expandKind pks[p]) acc.size
      h_acc_lt_acc_ext h_lt_lin'
  -- Step 4: transport along h_eq + h_step_splice.
  have h_lin_eq : linearise tokens pks
      = linearise.go tokens pks j (p + 1) (acc ++ expandKind pks[p]) := by
    rw [h_eq, h_step_splice]
  have h_lt_lin : acc.size < (linearise tokens pks).size := by
    rw [h_lin_eq]; exact h_lt_lin'
  refine ⟨h_lt_lin, ?_⟩
  have h_lin_at : (linearise tokens pks)[acc.size]'h_lt_lin
      = (linearise.go tokens pks j (p + 1) (acc ++ expandKind pks[p]))[acc.size]'h_lt_lin' := by
    congr 1 <;> exact h_lin_eq
  rw [h_lin_at, h_at_acc]
  exact h_acc_ext_at_acc

/-- Index-form corollary of Foundation B: the consumer typically knows
    `acc.size = k` for some target index `k` (e.g., `k + 1` after a
    flowEntry).  This form unifies the readout on `linearise[k]` directly,
    saving the consumer one transport step. -/
theorem linearise_splice_keyonly_at_index
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (j p k : Nat)
    (acc : Array (Positioned YamlToken))
    (h_eq : linearise tokens pks = linearise.go tokens pks j p acc)
    (h_acc_size : acc.size = k)
    (h_p : p < pks.size)
    (h_splice_fires : pks[p].insertBeforeIdx ≤ j)
    (h_kind : pks[p].kind = .keyOnly) :
    ∃ (h_lin : k < (linearise tokens pks).size),
      ((linearise tokens pks)[k]'h_lin).val = .key := by
  subst h_acc_size
  exact linearise_splice_keyonly_at tokens pks j p acc h_eq h_p h_splice_fires h_kind

end L4YAML.Proofs.ScannerLinearise
