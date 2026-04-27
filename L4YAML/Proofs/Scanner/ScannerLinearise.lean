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

end L4YAML.Proofs.ScannerLinearise
