/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedDispatch

/-! # `IndexedScannerCorrectness.OrderedLoop` — §8.9–§8.11

`scanNextTokenIx_preserves_ScanInvIx` / `_preserves_AllKeysValidIx`
(top-level composition over the dispatchers), `scanLoopIx_ordered`
(fuel induction), and the final `scanIx_positions_ordered` discharge
of the staging axiom exposed in `Basic.lean` (§6.4).

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

/-! ### §8.9  `scanNextTokenIx_preserves_*` — top-level per-iteration
preservation.

Composes preprocess + dispatchStructural OR
(allowDirectives field update + checkBlockFlowIndent + dispatchFlowIndicators
OR dispatchBlockIndicators OR dispatchContent). The field updates and
`checkBlockFlowIndent` (which returns Unit) preserve both invariants
trivially. -/

theorem scanNextTokenIx_preserves_ScanInvIx
    {s s' : ScannerStateIx input} (h : ScanInvIx s) (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx s = .ok (some s')) : ScanInvIx s' := by
  unfold scanNextTokenIx at h_ok
  simp only [Bind.bind, Except.bind] at h_ok
  cases hPre : scanNextTokenIx_preprocess s with
  | error e => rw [hPre] at h_ok; cases h_ok
  | ok preRes =>
    rw [hPre] at h_ok
    cases preRes with
    | none => cases h_ok
    | some sc =>
      obtain ⟨sp, c⟩ := sc
      have h_sp := scanNextTokenIx_preprocess_preserves_ScanInvIx h hPre
      have h_sp_akv := scanNextTokenIx_preprocess_preserves_AllKeysValidIx h_akv hPre
      simp only at h_ok
      cases hStr : scanNextTokenIx_dispatchStructural sp c with
      | error e => rw [hStr] at h_ok; cases h_ok
      | ok structRes =>
        rw [hStr] at h_ok
        cases structRes with
        | some s'' =>
          cases h_ok
          exact scanNextTokenIx_dispatchStructural_preserves_ScanInvIx h_sp hStr
        | none =>
          by_cases hAD : sp.allowDirectives = true
          · -- allowDirectives = true: sadj has the field updates
            rw [if_pos hAD] at h_ok
            let sadj : ScannerStateIx input :=
              { sp with allowDirectives := false, documentEverStarted := true }
            have h_sadj : ScanInvIx sadj :=
              ScanInvIx_of_field_update _ _ h_sp rfl rfl
            have h_sadj_akv : AllKeysValidIx sadj := by
              refine AllKeysValidIx_mono _ _ h_sp_akv rfl rfl ?_ ?_
              · exact Nat.le_refl _
              · intro i hi; rfl
            cases hChk : scanNextTokenIx_checkBlockFlowIndent sadj c with
            | error e => rw [hChk] at h_ok; cases h_ok
            | ok _ =>
              rw [hChk] at h_ok
              cases hFlow : scanNextTokenIx_dispatchFlowIndicators sadj c with
              | error e => rw [hFlow] at h_ok; cases h_ok
              | ok flowRes =>
                rw [hFlow] at h_ok
                cases flowRes with
                | some _ =>
                  cases h_ok
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_ScanInvIx h_sadj hFlow
                | none =>
                  cases hBlk : scanNextTokenIx_dispatchBlockIndicators sadj c with
                  | error e => rw [hBlk] at h_ok; cases h_ok
                  | ok blkRes =>
                    rw [hBlk] at h_ok
                    cases blkRes with
                    | some _ =>
                      cases h_ok
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_ScanInvIx
                        h_sadj h_sadj_akv hBlk
                    | none =>
                      cases hCon : scanNextTokenIx_dispatchContent sadj c with
                      | error e => rw [hCon] at h_ok; cases h_ok
                      | ok _ =>
                        rw [hCon] at h_ok
                        cases h_ok
                        exact scanNextTokenIx_dispatchContent_preserves_ScanInvIx h_sadj hCon
          · -- allowDirectives = false: sadj = sp
            rw [if_neg hAD] at h_ok
            cases hChk : scanNextTokenIx_checkBlockFlowIndent sp c with
            | error e => rw [hChk] at h_ok; cases h_ok
            | ok _ =>
              rw [hChk] at h_ok
              cases hFlow : scanNextTokenIx_dispatchFlowIndicators sp c with
              | error e => rw [hFlow] at h_ok; cases h_ok
              | ok flowRes =>
                rw [hFlow] at h_ok
                cases flowRes with
                | some _ =>
                  cases h_ok
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_ScanInvIx h_sp hFlow
                | none =>
                  cases hBlk : scanNextTokenIx_dispatchBlockIndicators sp c with
                  | error e => rw [hBlk] at h_ok; cases h_ok
                  | ok blkRes =>
                    rw [hBlk] at h_ok
                    cases blkRes with
                    | some _ =>
                      cases h_ok
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_ScanInvIx
                        h_sp h_sp_akv hBlk
                    | none =>
                      cases hCon : scanNextTokenIx_dispatchContent sp c with
                      | error e => rw [hCon] at h_ok; cases h_ok
                      | ok _ =>
                        rw [hCon] at h_ok
                        cases h_ok
                        exact scanNextTokenIx_dispatchContent_preserves_ScanInvIx h_sp hCon

theorem scanNextTokenIx_preserves_AllKeysValidIx
    {s s' : ScannerStateIx input} (h_akv : AllKeysValidIx s)
    (h_ok : scanNextTokenIx s = .ok (some s')) : AllKeysValidIx s' := by
  unfold scanNextTokenIx at h_ok
  simp only [Bind.bind, Except.bind] at h_ok
  cases hPre : scanNextTokenIx_preprocess s with
  | error e => rw [hPre] at h_ok; cases h_ok
  | ok preRes =>
    rw [hPre] at h_ok
    cases preRes with
    | none => cases h_ok
    | some sc =>
      obtain ⟨sp, c⟩ := sc
      have h_sp_akv := scanNextTokenIx_preprocess_preserves_AllKeysValidIx h_akv hPre
      simp only at h_ok
      cases hStr : scanNextTokenIx_dispatchStructural sp c with
      | error e => rw [hStr] at h_ok; cases h_ok
      | ok structRes =>
        rw [hStr] at h_ok
        cases structRes with
        | some s'' =>
          cases h_ok
          exact scanNextTokenIx_dispatchStructural_preserves_AllKeysValidIx h_sp_akv hStr
        | none =>
          by_cases hAD : sp.allowDirectives = true
          · rw [if_pos hAD] at h_ok
            let sadj : ScannerStateIx input :=
              { sp with allowDirectives := false, documentEverStarted := true }
            have h_sadj_akv : AllKeysValidIx sadj := by
              refine AllKeysValidIx_mono _ _ h_sp_akv rfl rfl ?_ ?_
              · exact Nat.le_refl _
              · intro i hi; rfl
            cases hChk : scanNextTokenIx_checkBlockFlowIndent sadj c with
            | error e => rw [hChk] at h_ok; cases h_ok
            | ok _ =>
              rw [hChk] at h_ok
              cases hFlow : scanNextTokenIx_dispatchFlowIndicators sadj c with
              | error e => rw [hFlow] at h_ok; cases h_ok
              | ok flowRes =>
                rw [hFlow] at h_ok
                cases flowRes with
                | some _ =>
                  cases h_ok
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_AllKeysValidIx h_sadj_akv hFlow
                | none =>
                  cases hBlk : scanNextTokenIx_dispatchBlockIndicators sadj c with
                  | error e => rw [hBlk] at h_ok; cases h_ok
                  | ok blkRes =>
                    rw [hBlk] at h_ok
                    cases blkRes with
                    | some _ =>
                      cases h_ok
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_AllKeysValidIx
                        h_sadj_akv hBlk
                    | none =>
                      cases hCon : scanNextTokenIx_dispatchContent sadj c with
                      | error e => rw [hCon] at h_ok; cases h_ok
                      | ok _ =>
                        rw [hCon] at h_ok
                        cases h_ok
                        exact scanNextTokenIx_dispatchContent_preserves_AllKeysValidIx h_sadj_akv hCon
          · rw [if_neg hAD] at h_ok
            cases hChk : scanNextTokenIx_checkBlockFlowIndent sp c with
            | error e => rw [hChk] at h_ok; cases h_ok
            | ok _ =>
              rw [hChk] at h_ok
              cases hFlow : scanNextTokenIx_dispatchFlowIndicators sp c with
              | error e => rw [hFlow] at h_ok; cases h_ok
              | ok flowRes =>
                rw [hFlow] at h_ok
                cases flowRes with
                | some _ =>
                  cases h_ok
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_AllKeysValidIx h_sp_akv hFlow
                | none =>
                  cases hBlk : scanNextTokenIx_dispatchBlockIndicators sp c with
                  | error e => rw [hBlk] at h_ok; cases h_ok
                  | ok blkRes =>
                    rw [hBlk] at h_ok
                    cases blkRes with
                    | some _ =>
                      cases h_ok
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_AllKeysValidIx
                        h_sp_akv hBlk
                    | none =>
                      cases hCon : scanNextTokenIx_dispatchContent sp c with
                      | error e => rw [hCon] at h_ok; cases h_ok
                      | ok _ =>
                        rw [hCon] at h_ok
                        cases h_ok
                        exact scanNextTokenIx_dispatchContent_preserves_AllKeysValidIx h_sp_akv hCon

/-! ### §8.10  `scanLoopIx_ordered` — fuel induction proving ScanInvIx
of the final TokenStream.

The induction mirrors `scanLoopIx_tokens_size_le`: at each step,
either we terminate via `unwindIndentsIx → emit streamEnd` (both
preserve `ScanInvIx`) or we recurse on `scanNextTokenIx`'s output
(which preserves both invariants by §8.9). -/

/-- ScanInv'Ix on the final TokenStream produced by `scanLoopIx`, given
    the input state satisfies the paired invariant. The bound is on
    the *final* state's cursor offset, not the input state's. Phrased
    as `ScanInv'Ix` rather than `ScanInvIx` since we lose the final
    state's structure (`scanLoopIx` returns the TokenStream alone). -/
theorem scanLoopIx_ordered {s : ScannerStateIx input} {fuel : Nat}
    {ts : Indexed.TokenStream input}
    (h : ScanInvIx s) (h_akv : AllKeysValidIx s)
    (h_ok : scanLoopIx s fuel = .ok ts) :
    ∀ i j : Fin ts.tokens.size, i.val < j.val →
      (ts.tokens[i]).start.offset ≤ (ts.tokens[j]).start.offset := by
  induction fuel generalizing s with
  | zero => unfold scanLoopIx at h_ok; cases h_ok
  | succ fuel' ih =>
    unfold scanLoopIx at h_ok
    cases hSc : scanNextTokenIx s with
    | error e => rw [hSc] at h_ok; cases h_ok
    | ok scRes =>
      rw [hSc] at h_ok
      cases scRes with
      | none =>
        by_cases hFL : s.flowLevel > 0
        · rw [if_pos hFL] at h_ok; cases h_ok
        · rw [if_neg hFL] at h_ok
          by_cases hDS : (s.directivesPresent && !s.documentEverStarted) = true
          · rw [if_pos hDS] at h_ok; cases h_ok
          · rw [if_neg hDS] at h_ok
            cases h_ok
            -- ts = ((unwindIndentsIx s (-1)).emit streamEnd).tokens
            -- Apply: unwindIndentsIx preserves ScanInvIx → emit preserves ScanInvIx → extract ordering.
            have h_unwind := unwindIndentsIx_preserves_ScanInvIx s (-1 : Int) h
            have h_emit := emit_preserves_ScanInvIx _ YamlToken.streamEnd h_unwind
            exact h_emit.1
      | some s'' =>
        have h_step := scanNextTokenIx_preserves_ScanInvIx h h_akv hSc
        have h_step_akv := scanNextTokenIx_preserves_AllKeysValidIx h_akv hSc
        exact ih h_step h_step_akv h_ok

/-! ### §8.11  `scanIx_positions_ordered` — the discharge of the §6.4
staging axiom.

Apply `scanLoopIx_ordered` to the initial post-BOM state. The initial
state (`(ScannerStateIx.mk' input).emit streamStart` then optional
advance for BOM) satisfies both `ScanInvIx` and `AllKeysValidIx`
vacuously (no simpleKey saved yet, simpleKeyStack empty, one token
with `.start = 0`). -/

theorem ScanInvIx_mk' (input : String) :
    ScanInvIx (ScannerStateIx.mk' input) := by
  refine ⟨?_, ?_⟩
  · -- tokens is empty
    intro ⟨i, hi⟩ ⟨j, hj⟩ _
    exact absurd hi (Nat.not_lt_zero i)
  · intro ⟨i, hi⟩
    exact absurd hi (Nat.not_lt_zero i)

theorem AllKeysValidIx_mk' (input : String) :
    AllKeysValidIx (ScannerStateIx.mk' input) := by
  refine ⟨?_, ?_⟩
  · intro h_poss
    -- mk' has simpleKey.possible = false (default)
    exfalso
    have : (ScannerStateIx.mk' input).simpleKey.possible = false := rfl
    rw [this] at h_poss
    exact Bool.false_ne_true h_poss
  · intro j hj _
    -- simpleKeyStack is empty in mk'
    exfalso
    have h_sz : (ScannerStateIx.mk' input).simpleKeyStack.size = 0 := rfl
    rw [h_sz] at hj
    exact Nat.not_lt_zero j hj

theorem scanIx_positions_ordered (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens) :
    ∀ (i j : Fin tokens.tokens.size), i.val < j.val →
      (tokens.tokens[i]).start.offset ≤ (tokens.tokens[j]).start.offset := by
  unfold scanIx at h
  -- s0 := (mk' input).emit streamStart; sB := BOM-handled s0.
  have h_mk : ScanInvIx (ScannerStateIx.mk' input) := ScanInvIx_mk' input
  have h_mk_akv : AllKeysValidIx (ScannerStateIx.mk' input) := AllKeysValidIx_mk' input
  have h_s0 : ScanInvIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
    emit_preserves_ScanInvIx _ _ h_mk
  have h_s0_akv : AllKeysValidIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
    emit_preserves_AllKeysValidIx _ _ h_mk_akv
  -- BOM step: cursor-only advance preserves both.
  have h_sB : ScanInvIx
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart) := by
    split
    · exact advance_preserves_ScanInvIx _ h_s0
    · exact h_s0
  have h_sB_akv : AllKeysValidIx
      (match ((ScannerStateIx.mk' input).emit YamlToken.streamStart).peek? with
        | some '﻿' => ((ScannerStateIx.mk' input).emit YamlToken.streamStart).advance
        | _ => (ScannerStateIx.mk' input).emit YamlToken.streamStart) := by
    split
    · exact advance_preserves_AllKeysValidIx _ h_s0_akv
    · exact h_s0_akv
  -- Apply scanLoopIx_ordered.
  exact scanLoopIx_ordered h_sB h_sB_akv h

/-! ### §8.12  Final composite `scanIx_valid_token_stream`.

Moved from `StreamStart.lean` §7.10 (now a status-note section)
because the composite needs `scanIx_positions_ordered` from §8.11
(this file). All three conjuncts are now real theorems — no staging
axioms remain in the `scanIx` chain. -/

theorem scanIx_valid_token_stream
    {input : String} (tokens : Indexed.TokenStream input)
    (h : scanIx input = .ok tokens) :
    ValidTokenStreamPropIx tokens := by
  have h_size : tokens.tokens.size ≥ 2 := scanIx_produces_at_least_two tokens h
  have h_pos : 0 < tokens.tokens.size := by omega
  refine ⟨h_size, ?_, ?_, ?_⟩
  · intro _; exact scanIx_first_is_streamStart tokens h h_pos
  · intro _; exact scanIx_last_is_streamEnd tokens h h_pos
  · exact scanIx_positions_ordered tokens h

end L4YAML.Proofs.Indexed.ScannerCorrectness
