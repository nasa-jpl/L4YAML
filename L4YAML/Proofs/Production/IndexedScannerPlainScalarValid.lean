/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Parser.IndexedWellBehaved
import L4YAML.Proofs.Scanner.IndexedDispatch

/-! # `IndexedScannerPlainScalarValid` — Phase 3 Step 6d.1e foundation (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit (Guardrail 1). Imports
`IndexedWellBehaved` (for the indexed predicates
`PlainScalarsValidIx` / `FlowAwarePSVIx` / `FlowBracketsMatchedIx`)
and `L4YAML.Proofs.Scanner.IndexedDispatch` (for the existing
indexed scanner monotonicity lemmas — `emit_tokens_size`,
`advance_tokens`, `unwindIndentsIx_tokens_size_le`, etc.).

## Scope of Step 6d.1e (this file)

This file is the indexed analogue of
`L4YAML/Proofs/Production/ScannerPlainScalarValid.lean` — the
scanner-side chain that proves the indexed scanner output satisfies
`FlowAwarePSVIx` and `FlowBracketsMatchedIx`. The eventual goal is
two proven theorems:

```
theorem scan_flow_aware_psv_ix :
    Scanner.Indexed.scanIx input = .ok tokens → FlowAwarePSVIx tokens
theorem scan_flow_brackets_matched_ix :
    Scanner.Indexed.scanIx input = .ok tokens → FlowBracketsMatchedIx tokens
```

These discharge (via the consumers in
`IndexedWellBehaved.indexed_scanner_*_axiom`) the obligation flagged
in §5c of `IndexedWellBehaved.lean`.

### Phase 3 sub-step 6d.1e.1 (foundation, prior commit)

**Foundation tier** — structural / algebraic building blocks landed
in 6d.1e.1: PSV propagation primitives (§1), `flowNestingIx` prefix
stability + push lemmas (§2), `FlowContextPSVIx` propagation
primitives (§3), `FlowNestingInvIx` bridge invariant (§4), the 2
staged axioms with tightened preconditions (§7 — relocated from
`IndexedWellBehaved.lean` §5c).

### Phase 3 sub-step 6d.1e.2 (prior commit) — Emit-step + indent stack

**§5 generic emit-step preservation**:

- `PlainScalarsValidIx_push_non_plain` — pushing a non-plain token
  preserves PSV (array-level helper, indexed twin of legacy
  `PlainScalarsValid_push_non_plain`);
- `emit_preserves_tokens_at` — non-flow `emit` preserves token
  values at low indices;
- `emit_new_token_token` — the token added by `emit tok` at the new
  position is `tok`;
- `emit_non_plain_preserves_PlainScalarsValidIx`,
  `emit_non_flow_preserves_FlowNestingInvIx`,
  `emit_non_flow_non_plain_preserves_FlowContextPSVIx`.

**§6 indent-stack preservation** — per-action lemmas for each of
the five indent-stack scanner ops:

- `unwindIndentsLoopIx` / `unwindIndentsIx`: `_preserves_prefix`,
  `_preserves_flowLevel`, `_new_tokens_not_plain`,
  `_new_tokens_not_flow`, `_preserves_FlowNestingInvIx`,
  `_preserves_PlainScalarsValidIx`, `_preserves_FlowContextPSVIx`;
- `pushSequenceIndentIx` / `pushMappingIndentIx`: `_preserves_prefix`,
  `_preserves_PlainScalarsValidIx`,
  `_preserves_FlowNestingInvIx`, `_preserves_FlowContextPSVIx`;
- `saveSimpleKeyIx`: `_preserves_prefix`, `_flowLevel`,
  `_new_tokens_not_plain`, `_new_tokens_not_flow`,
  `_preserves_PlainScalarsValidIx`, `_preserves_FlowNestingInvIx`,
  `_preserves_FlowContextPSVIx`.

### Phase 3 sub-step 6d.1e.3 (this commit) — Scalar scanners

**§7 scalar-scanner preservation** — per-action lemmas for the two
state-transforming scalar scanners (the other four scalar primitives
listed in the Blueprint — `scanDoubleQuotedIx` / `scanSingleQuotedIx`
/ `scanBlockScalarIx` / `scanPlainScalarIx` — return
`Option (String × IxCursor input)`, not a state transformation, so
their PSV reasoning lives in the dispatcher arm of
`scanNextTokenIx_dispatchContent` and is deferred to Step 6d.1e.6):

- **§7a `emitAt` building blocks** *(proven, ~120 LOC)*:
  `emitAt`-twins of §5 (the scalar scanners use `emitAt` rather
  than `emit`, since they need to carry the
  `startPos`-from-before-`advance` start position):
  `emitAt_tokens_size`, `emitAt_preserves_tokens_at`,
  `emitAt_new_token_token`,
  `emitAt_non_plain_preserves_PlainScalarsValidIx`,
  `emitAt_non_flow_preserves_FlowNestingInvIx`,
  `emitAt_non_flow_non_plain_preserves_FlowContextPSVIx`.
- **§7b `scanAnchorOrAliasIx` preservation** *(8 lemmas, 6 axioms
  + 2 proven theorems)*: see Reflection 70 for the
  record-update-opacity wall hit by direct proof attempts. The 6
  axioms (`_adds_one_token`, `_preserves_prefix`,
  `_preserves_flowLevel`, `_new_token_not_plain`,
  `_new_token_not_flow`, `_preserves_FlowNestingInvIx`) all carry
  real `(h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')`
  preconditions. The 2 proven theorems
  (`_preserves_PlainScalarsValidIx`, `_preserves_FlowContextPSVIx`)
  compose the 6 staged-as-axiom primitives with §1/§3
  prefix-and-new combinators.
- **§7c `scanTagIx` preservation** *(8 lemmas, same 6+2 split as
  §7b)*: identical-shape suite, with three-way case split on the
  verbatim/secondary/named tag branches.

**Phase 3 closure axiom count after Step 6d.1e.3**: **14 axioms** —
2 pre-existing (§8 top-level) + 12 new (6 each in §7b/§7c for the
state-transforming scalar scanners). The PSV/FlowContextPSVIx
preservation theorems (4 total: 2 per scanner) are *proven*, taking
the per-scanner adds_one_token / preserves_prefix /
new_token_not_plain axioms as inputs and composing them with the §1
and §3 propagation primitives.

### Phase 3 sub-steps 6d.1e.4+ (future commits)

**Remaining per-action preservation chain**: block-context
dispatchers (`scanBlockEntryIx`, `scanKeyIx`, `scanValueIx`, etc.),
flow-context dispatchers (flow seq/map start/end, flow entry),
document/directive layers + top-level dispatch composition. The
dispatcher-level proof in 6d.1e.6 will stage
`scanPlainScalarIx_content_valid` as a new axiom (or discharge it
inline, depending on the Layer F.4 integration cost). Final 6d.1e.7
discharges all axioms (the 2 §8 + the 12 §7 + any added in
6d.1e.4–6d.1e.6) with proven theorems built from this chain. See
Blueprint Reflections 68 + 70.

## What this file does NOT contain (yet)

- Dispatcher / document-directive scanner preservation lemmas
  (deferred to 6d.1e.4+).
- Direct proofs of the §7b/§7c scalar-scanner preservation
  primitives (staged as axioms — see Reflection 70).
- The two §8 top-level theorems' proofs (deferred to 6d.1e.7).

## Reflection 67 follow-up (Reflection 68)

The original ~700 LOC / 1-session estimate for §5c axiom discharge
was based on counting the API-surface theorems
(`scan_flow_aware_psv` + `scan_flow_brackets_matched` = 2 names) and
multiplying by an assumed-small dependency-chain factor. The actual
chain is ~80 per-action preservation lemmas spread across the 5,584
LOC of legacy `ScannerPlainScalarValid.lean` plus supporting
dependencies (`ScannerCorrectness.lean` at 10,637 LOC, etc.). The
rescoping into 6d.1e.1 (foundation, this commit) + 6d.1e.2+ (chain,
~5 future sessions) lets each commit stay `lake build` green per
Guardrail 1. See Blueprint Reflection 68. -/

namespace L4YAML.Proofs.Indexed.ScannerPlainScalarValid

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Indexed.WellBehaved

variable {input : String}

/-! ## §1  PSV propagation primitives -/

/-- An empty token stream is trivially `PlainScalarsValidIx`. Indexed
    twin of legacy `PlainScalarsValid_empty`. -/
theorem PlainScalarsValidIx_empty :
    PlainScalarsValidIx (input := input) (Indexed.TokenStream.empty input) :=
  fun _ hi => absurd hi (by simp [Indexed.TokenStream.size, Indexed.TokenStream.empty])

/-- Prefix preservation + new-tokens PSV ⟹ PSV for extended stream.
    Indexed twin of legacy `PlainScalarsValid_of_prefix_and_new`. -/
theorem PlainScalarsValidIx_of_prefix_and_new
    (old_tokens new_tokens : Indexed.TokenStream input)
    (h_old : PlainScalarsValidIx old_tokens)
    (h_mono : old_tokens.size ≤ new_tokens.size)
    (h_prefix : ∀ (i : Nat) (hi : i < old_tokens.size),
      new_tokens[i]'(by omega) = old_tokens[i])
    (h_new : ∀ j (hj : j < new_tokens.size), j ≥ old_tokens.size →
      match (new_tokens[j]'hj).token with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain, none, none, none⟩ false
      | _ => True) :
    PlainScalarsValidIx new_tokens := by
  intro i hi
  by_cases h : i < old_tokens.size
  · rw [h_prefix i h]; exact h_old i h
  · exact h_new i hi (by omega)

/-- The per-token PSV property. Indexed twin of legacy `psv_match`. -/
def psv_match_ix (tok : IxToken input) : Prop :=
  match tok.token with
  | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
  | _ => True

/-- When a token is provably not `.scalar _ .plain`, the PSV match is `True`.
    Indexed twin of legacy `psv_match_of_ne_plain`. -/
theorem psv_match_of_ne_plain_ix
    (tokens : Indexed.TokenStream input) (j : Nat) (hj : j < tokens.size)
    (h_ne : ∀ c, (tokens[j]'hj).token ≠ YamlToken.scalar c .plain) :
    match (tokens[j]'hj).token with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  generalize h_eq : (tokens[j]'hj).token = tok
  cases tok with
  | scalar content style =>
    cases style with
    | plain => exact absurd h_eq (h_ne content)
    | _ => trivial
  | _ => trivial

/-- If a token's `.token` is not `.scalar _ .plain`, the PSV match gives `True`.
    Indexed twin of legacy `psv_of_not_plain`. -/
theorem psv_of_not_plain_ix (tok : IxToken input)
    (h : match tok.token with | .scalar _ .plain => False | _ => True) :
    match tok.token with
    | .scalar content .plain => ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True := by
  cases tok with
  | mk start val stop hOrd hBnd =>
    cases val <;> simp_all
    rename_i content style; cases style <;> simp_all

/-! ## §2  flowNestingIx prefix stability and push lemmas -/

/-- `flowNestingIx.go` is stable under prefix-preserving array extension.
    Indexed twin of legacy `flowNesting_go_prefix_stable`. -/
theorem flowNestingIx_go_prefix_stable
    (old new : Array (IxToken input))
    (h_mono : old.size ≤ new.size)
    (h_prefix_val : ∀ j (hj : j < old.size),
      (new[j]'(by omega)).token = (old[j]).token)
    (pos target depth : Nat) (h_target : target ≤ old.size) :
    flowNestingIx.go new pos target depth = flowNestingIx.go old pos target depth := by
  generalize hn : target - pos = n
  induction n generalizing pos depth with
  | zero =>
    have hge : pos ≥ target := by omega
    simp only [flowNestingIx.go, hge, ↓reduceIte]
  | succ n ih =>
    by_cases hge : pos ≥ target
    · simp only [flowNestingIx.go, hge, ↓reduceIte]
    · have h_pos_old : pos < old.size := by omega
      have h_pos_new : pos < new.size := by omega
      have h_val_eq : (new[pos]'h_pos_new).token = (old[pos]'h_pos_old).token :=
        h_prefix_val pos h_pos_old
      unfold flowNestingIx.go
      simp only [eq_false (show ¬(pos ≥ target) by omega), ite_false,
        eq_true h_pos_new, eq_true h_pos_old, dite_true, h_val_eq]
      exact ih (pos + 1) _ (by omega)

/-- `flowNestingIx` at positions `≤ old.size` is unchanged by stream extension.
    Indexed twin of legacy `flowNesting_prefix_stable`. -/
theorem flowNestingIx_prefix_stable
    (old new : Indexed.TokenStream input)
    (h_mono : old.size ≤ new.size)
    (h_prefix_val : ∀ j (hj : j < old.size),
      (new[j]'(by omega)).token = (old[j]).token)
    (i : Nat) (hi : i ≤ old.size) :
    flowNestingIx new i = flowNestingIx old i := by
  unfold flowNestingIx
  have h_mono_arr : old.tokens.size ≤ new.tokens.size := h_mono
  have h_prefix_arr : ∀ j (hj : j < old.tokens.size),
      (new.tokens[j]'(by omega)).token = (old.tokens[j]).token := h_prefix_val
  exact flowNestingIx_go_prefix_stable old.tokens new.tokens h_mono_arr h_prefix_arr 0 i 0 hi

/-- Processing a single pushed token at the end of the array.
    Indexed twin of legacy `flowNesting_go_single_push`. -/
theorem flowNestingIx_go_single_push
    (tokens : Array (IxToken input)) (t : IxToken input)
    (depth : Nat) :
    flowNestingIx.go (tokens.push t) tokens.size (tokens.size + 1) depth =
    match t.token with
    | .flowSequenceStart | .flowMappingStart => depth + 1
    | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
    | _ => depth := by
  unfold flowNestingIx.go
  simp only [show ¬(tokens.size ≥ tokens.size + 1) by omega, ite_false,
    show tokens.size < (tokens.push t).size by simp [Array.size_push], dite_true,
    show (tokens.push t)[tokens.size] = t from Array.getElem_push_eq]
  unfold flowNestingIx.go
  simp only [show tokens.size + 1 ≥ tokens.size + 1 from Nat.le_refl _, ite_true]
  rfl

/-- How `flowNestingIx` on the underlying array changes when a single
    token is appended. Indexed twin of legacy `flowNesting_push`. -/
theorem flowNestingIx_push (tokens : Array (IxToken input)) (t : IxToken input) :
    flowNestingIx.go (tokens.push t) 0 (tokens.size + 1) 0 =
    match t.token with
    | .flowSequenceStart | .flowMappingStart =>
        flowNestingIx.go tokens 0 tokens.size 0 + 1
    | .flowSequenceEnd | .flowMappingEnd =>
        if flowNestingIx.go tokens 0 tokens.size 0 > 0
        then flowNestingIx.go tokens 0 tokens.size 0 - 1 else 0
    | _ => flowNestingIx.go tokens 0 tokens.size 0 := by
  rw [flowNestingIx_go_split (tokens.push t) 0 tokens.size (tokens.size + 1) 0
      (by omega) (by omega)]
  rw [flowNestingIx_go_prefix_stable tokens (tokens.push t)
      (by simp [Array.size_push])
      (fun j hj => by simp [Array.getElem_push, hj])
      0 tokens.size 0 (by omega)]
  exact flowNestingIx_go_single_push tokens t _

/-- Appending a non-flow token preserves `flowNestingIx` at the old size.
    Indexed twin of legacy `flowNesting_push_non_flow`. -/
theorem flowNestingIx_push_non_flow (tokens : Array (IxToken input))
    (t : IxToken input)
    (h1 : t.token ≠ .flowSequenceStart) (h2 : t.token ≠ .flowMappingStart)
    (h3 : t.token ≠ .flowSequenceEnd) (h4 : t.token ≠ .flowMappingEnd) :
    flowNestingIx.go (tokens.push t) 0 (tokens.size + 1) 0 =
    flowNestingIx.go tokens 0 tokens.size 0 := by
  rw [flowNestingIx_push]
  cases h : t.token <;> simp_all

/-- `flowNestingIx.go` on a range of non-flow tokens returns depth unchanged.
    Indexed twin of legacy `flowNesting_go_non_flow`. -/
theorem flowNestingIx_go_non_flow
    (tokens : Array (IxToken input)) (pos target depth : Nat)
    (h_nf : ∀ j, pos ≤ j → j < target → (hj : j < tokens.size) →
      (tokens[j]'hj).token ≠ .flowSequenceStart ∧
      (tokens[j]'hj).token ≠ .flowMappingStart ∧
      (tokens[j]'hj).token ≠ .flowSequenceEnd ∧
      (tokens[j]'hj).token ≠ .flowMappingEnd) :
    flowNestingIx.go tokens pos target depth = depth := by
  generalize hn : target - pos = n
  induction n generalizing pos depth with
  | zero => simp [flowNestingIx.go, show pos ≥ target by omega]
  | succ n ih =>
    have h_lt : pos < target := by omega
    by_cases h_pos : pos < tokens.size
    · rw [flowNestingIx_go_step tokens pos target depth h_pos h_lt]
      have ⟨h1, h2, h3, h4⟩ := h_nf pos (Nat.le_refl _) h_lt h_pos
      have h_eq : (match (tokens[pos]'h_pos).token with
        | .flowSequenceStart | .flowMappingStart => depth + 1
        | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
        | _ => depth) = depth := by
        generalize h_tok : (tokens[pos]'h_pos).token = tok
        cases tok <;> simp_all
      simp only
      exact ih (pos + 1) depth (fun j _ hlt hj => h_nf j (by omega) hlt hj) (by omega)
    · exact flowNestingIx_go_oob tokens pos target depth (by omega)

/-- Replacing a non-flow slot with another non-flow token preserves
    `flowNestingIx.go`. Indexed twin of legacy
    `flowNesting_go_setIfInBounds_non_flow`. -/
theorem flowNestingIx_go_setIfInBounds_non_flow
    (tokens : Array (IxToken input))
    (idx : Nat) (val : IxToken input)
    (h_val_nf : val.token ≠ .flowSequenceStart ∧ val.token ≠ .flowMappingStart ∧
                val.token ≠ .flowSequenceEnd ∧ val.token ≠ .flowMappingEnd)
    (h_orig_nf : ∀ (h : idx < tokens.size),
      (tokens[idx]'h).token ≠ .flowSequenceStart ∧
      (tokens[idx]'h).token ≠ .flowMappingStart ∧
      (tokens[idx]'h).token ≠ .flowSequenceEnd ∧
      (tokens[idx]'h).token ≠ .flowMappingEnd)
    (pos target depth : Nat) :
    flowNestingIx.go (tokens.setIfInBounds idx val) pos target depth =
    flowNestingIx.go tokens pos target depth := by
  generalize hn : target - pos = n
  induction n generalizing pos depth with
  | zero =>
    rw [flowNestingIx_go_ge_target _ _ _ _ (by omega),
        flowNestingIx_go_ge_target _ _ _ _ (by omega)]
  | succ n ih =>
    by_cases h_pos : pos < tokens.size
    · have h_pos' : pos < (tokens.setIfInBounds idx val).size := by
        rw [Array.size_setIfInBounds]; exact h_pos
      rw [flowNestingIx_go_step _ _ _ _ h_pos' (by omega),
          flowNestingIx_go_step _ _ _ _ h_pos (by omega)]
      by_cases h_eq : idx = pos
      · subst h_eq
        rcases h_val_nf with ⟨hv1, hv2, hv3, hv4⟩
        rcases h_orig_nf h_pos with ⟨ho1, ho2, ho3, ho4⟩
        have h_val_depth : (match val.token with
            | .flowSequenceStart | .flowMappingStart => depth + 1
            | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
            | _ => depth) = depth := by
          generalize val.token = v at hv1 hv2 hv3 hv4
          cases v <;> first | contradiction | rfl
        have h_orig_depth : (match (tokens[idx]'h_pos).token with
            | .flowSequenceStart | .flowMappingStart => depth + 1
            | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
            | _ => depth) = depth := by
          generalize (tokens[idx]'h_pos).token = w at ho1 ho2 ho3 ho4
          cases w <;> first | contradiction | rfl
        simp only [Array.getElem_setIfInBounds h_pos, ↓reduceIte]
        exact ih (idx + 1) _ (by omega)
      · simp only [Array.getElem_setIfInBounds h_pos, if_neg h_eq]
        exact ih (pos + 1) _ (by omega)
    · rw [flowNestingIx_go_oob (tokens.setIfInBounds idx val) pos target depth
            (by rw [Array.size_setIfInBounds]; omega),
          flowNestingIx_go_oob tokens pos target depth (by omega)]

/-- Replacing a non-flow token at `idx` with another non-flow token
    preserves `flowNestingIx`. Indexed twin of legacy
    `flowNesting_setIfInBounds_non_flow`. -/
theorem flowNestingIx_setIfInBounds_non_flow
    (tokens : Indexed.TokenStream input)
    (idx : Nat) (val : IxToken input)
    (h_val_nf : val.token ≠ .flowSequenceStart ∧ val.token ≠ .flowMappingStart ∧
                val.token ≠ .flowSequenceEnd ∧ val.token ≠ .flowMappingEnd)
    (h_orig_nf : ∀ (h : idx < tokens.size),
      (tokens[idx]'h).token ≠ .flowSequenceStart ∧
      (tokens[idx]'h).token ≠ .flowMappingStart ∧
      (tokens[idx]'h).token ≠ .flowSequenceEnd ∧
      (tokens[idx]'h).token ≠ .flowMappingEnd)
    (target : Nat) :
    flowNestingIx (tokens.setIfInBounds idx val) target = flowNestingIx tokens target := by
  unfold flowNestingIx
  exact flowNestingIx_go_setIfInBounds_non_flow tokens.tokens idx val h_val_nf h_orig_nf 0 target 0

/-! ## §3  FlowContextPSVIx propagation primitives -/

/-- An empty token stream trivially satisfies `FlowContextPSVIx`.
    Indexed twin of legacy `FlowContextPSV_empty`. -/
theorem FlowContextPSVIx_empty :
    FlowContextPSVIx (input := input) (Indexed.TokenStream.empty input) :=
  fun _ hi _ => absurd hi (by simp [Indexed.TokenStream.size, Indexed.TokenStream.empty])

/-- `FlowContextPSVIx` transfers through prefix-preserving array extension.
    Indexed twin of legacy `FlowContextPSV_of_prefix_and_new`. -/
theorem FlowContextPSVIx_of_prefix_and_new
    (old_tokens new_tokens : Indexed.TokenStream input)
    (h_old : FlowContextPSVIx old_tokens)
    (h_mono : old_tokens.size ≤ new_tokens.size)
    (h_prefix : ∀ (i : Nat) (hi : i < old_tokens.size),
      new_tokens[i]'(by omega) = old_tokens[i])
    (h_new : ∀ j (hj : j < new_tokens.size), j ≥ old_tokens.size →
      flowNestingIx new_tokens j > 0 →
      match (new_tokens[j]'hj).token with
      | .scalar content .plain =>
          ScalarScannable ⟨content, .plain, none, none, none⟩ true
      | _ => True) :
    FlowContextPSVIx new_tokens := by
  intro i hi h_flow
  by_cases h : i < old_tokens.size
  · have h_prefix_val : ∀ j (hj : j < old_tokens.size),
        (new_tokens[j]'(by omega)).token = (old_tokens[j]).token := by
      intro j hj; rw [h_prefix j hj]
    have h_fn := flowNestingIx_prefix_stable old_tokens new_tokens h_mono h_prefix_val i (by omega)
    rw [h_prefix i h]
    rw [h_fn] at h_flow
    exact h_old i h h_flow
  · exact h_new i hi (by omega) h_flow

/-- When a token is provably not `.scalar _ .plain`, the FlowContextPSVIx
    match is `True`. Indexed twin of legacy `fpsv_of_not_plain`. -/
theorem fpsv_of_not_plain_ix (tok : IxToken input)
    (h : match tok.token with | .scalar _ .plain => False | _ => True) :
    match tok.token with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ true
    | _ => True := by
  cases tok with
  | mk start val stop hOrd hBnd =>
    cases val <;> simp_all
    rename_i content style; cases style <;> simp_all

/-! ## §4  FlowNestingInvIx — scanner-state invariant

`FlowNestingInvIx s` says the token-array flow-nesting depth at the
end of the array equals the scanner's `flowLevel` field. This is the
bridge invariant between `flowNestingIx` (token-level computation) and
the scanner's `flowLevel` (running state). Preserved through every
non-flow-emitting scanner action. -/

/-- The scanner-state invariant bridging `flowNestingIx` to `flowLevel`.
    Indexed twin of legacy `FlowNestingInv`. -/
def FlowNestingInvIx {input : String} (s : ScannerStateIx input) : Prop :=
  flowNestingIx s.tokens s.tokens.size = s.flowLevel

/-! ## §5  Generic emit-step preservation building blocks

Unit lemmas — each says "emitting a token with a specific shape
preserves one of the three invariants" — used by the per-action
preservation chain (§6 indent-stack ops, and the scalar / dispatcher
families in Step 6d.1e.3+).

Landed in Step 6d.1e.2 alongside the indent-stack consumers below.

### Array-level helpers

The legacy `PlainScalarsValid_push_non_plain` operates on the array
directly; its indexed analogue threads through `TokenStream.push`.
Used by `pushSequenceIndentIx`, `pushMappingIndentIx` to discharge
the new-token obligation in one step. -/

/-- Pushing a non-plain token preserves `PlainScalarsValidIx`.
    Indexed twin of legacy `PlainScalarsValid_push_non_plain`. -/
theorem PlainScalarsValidIx_push_non_plain
    (tokens : Indexed.TokenStream input)
    (h_old : PlainScalarsValidIx tokens) (t : IxToken input)
    (h_np : match t.token with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValidIx (tokens.push t) := by
  intro i hi
  have hi_arr : i < (tokens.tokens.push t).size := hi
  by_cases h_lt : i < tokens.tokens.size
  · have h_eq : (tokens.push t)[i]'hi = tokens[i]'h_lt := by
      change (tokens.tokens.push t)[i]'hi_arr = tokens.tokens[i]'h_lt
      exact Array.getElem_push_lt ..
    rw [h_eq]; exact h_old i h_lt
  · have h_eq_idx : i = tokens.tokens.size := by
      rw [Array.size_push] at hi_arr; omega
    subst h_eq_idx
    have h_eq : (tokens.push t)[tokens.tokens.size]'hi = t := by
      change (tokens.tokens.push t)[tokens.tokens.size]'hi_arr = t
      exact Array.getElem_push_eq ..
    rw [h_eq]
    cases t with
    | mk start val stop hOrd hBnd =>
      cases val <;> simp_all
      rename_i content style; cases style <;> simp_all

/-! ### State-level emit lemmas

`emit_preserves_tokens_at` lets indent-stack proofs replace
`(s.emit tok).tokens[i]` with `s.tokens[i]` for in-bounds `i`. -/

/-- `emit` preserves token values at positions below the original size.
    Indexed twin of legacy `emit_preserves_tokens_at`. -/
theorem emit_preserves_tokens_at {input : String} (s : ScannerStateIx input)
    (tok : YamlToken) (i : Nat) (h : i < s.tokens.size) :
    (s.emit tok).tokens[i]'(by
        change i < (s.tokens.tokens.push _).size
        rw [Array.size_push]
        change i < s.tokens.tokens.size + 1 at *
        exact Nat.lt_succ_of_lt h) = s.tokens[i]'h := by
  change (s.tokens.tokens.push _)[i]'_ = s.tokens.tokens[i]'h
  exact Array.getElem_push_lt ..

/-- Emitting a non-plain token preserves `PlainScalarsValidIx`.
    Indexed analogue of the inline pattern used in legacy
    `pushSequenceIndent_preserves_PlainScalarsValid`. -/
theorem emit_non_plain_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken)
    (h_old : PlainScalarsValidIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValidIx (s.emit tok).tokens := by
  apply PlainScalarsValidIx_push_non_plain s.tokens h_old
  exact h_np

/-- Emitting a non-flow token preserves `FlowNestingInvIx`.
    Indexed twin of legacy `FlowNestingInv_emit_non_flow`. -/
theorem emit_non_flow_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken)
    (h_fni : FlowNestingInvIx s)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    FlowNestingInvIx (s.emit tok) := by
  unfold FlowNestingInvIx at *
  have h_fl : (s.emit tok).flowLevel = s.flowLevel := rfl
  rw [h_fl]
  change flowNestingIx.go (s.tokens.tokens.push _) 0
      (s.tokens.tokens.push _).size 0 = s.flowLevel
  rw [Array.size_push]
  rw [flowNestingIx_push_non_flow s.tokens.tokens _ h1 h2 h3 h4]
  exact h_fni

/-- Emitting a non-flow, non-plain token preserves `FlowContextPSVIx`.
    Composes `FlowContextPSVIx_of_prefix_and_new` (§3) with
    `flowNestingIx_push_non_flow` (§2) and `fpsv_of_not_plain_ix`
    on the single new token. -/
theorem emit_non_flow_non_plain_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken)
    (h_old : FlowContextPSVIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True)
    (_h1 : tok ≠ .flowSequenceStart) (_h2 : tok ≠ .flowMappingStart)
    (_h3 : tok ≠ .flowSequenceEnd) (_h4 : tok ≠ .flowMappingEnd) :
    FlowContextPSVIx (s.emit tok).tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens (s.emit tok).tokens h_old ?_ ?_ ?_
  · change s.tokens.tokens.size ≤ (s.tokens.tokens.push _).size
    rw [Array.size_push]; omega
  · intro i hi
    change (s.tokens.tokens.push _)[i]'(by
        rw [Array.size_push]; exact Nat.lt_succ_of_lt hi) = s.tokens.tokens[i]'hi
    exact Array.getElem_push_lt ..
  · intro j hj hge _h_flow
    have hj_arr : j < (s.tokens.tokens.push (IxToken.mk' s.cursor.pos tok s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound)).size := hj
    have h_size_eq : s.tokens.size = s.tokens.tokens.size := rfl
    have h_eq_idx : j = s.tokens.tokens.size := by
      rw [Array.size_push] at hj_arr
      rw [h_size_eq] at hge
      omega
    subst h_eq_idx
    have h_eq : (s.emit tok).tokens[s.tokens.tokens.size]'hj =
        IxToken.mk' s.cursor.pos tok s.cursor.pos (Nat.le_refl _) s.cursor.posBound := by
      change (s.tokens.tokens.push _)[s.tokens.tokens.size]'hj_arr = _
      exact Array.getElem_push_eq ..
    rw [h_eq]
    exact fpsv_of_not_plain_ix _ h_np

/-- The token added by `emit tok` at the new position is `tok`. Used by
    indent-stack `new_tokens_not_plain` / `new_tokens_not_flow` proofs
    to reduce the new-position match to a `cases` over `tok`. -/
theorem emit_new_token_token {input : String} (s : ScannerStateIx input)
    (tok : YamlToken)
    (h : s.tokens.size < (s.emit tok).tokens.size) :
    ((s.emit tok).tokens[s.tokens.size]'h).token = tok := by
  have h_get : (s.emit tok).tokens[s.tokens.size]'h =
      IxToken.mk' s.cursor.pos tok s.cursor.pos (Nat.le_refl _) s.cursor.posBound := by
    change (s.tokens.tokens.push _)[s.tokens.tokens.size]'h = _
    exact Array.getElem_push_eq ..
  rw [h_get]; rfl

/-! ## §6  Indent-stack preservation lemmas

Per-action preservation for the indent-stack scanner ops
(`unwindIndentsLoopIx`, `unwindIndentsIx`, `pushSequenceIndentIx`,
`pushMappingIndentIx`, `saveSimpleKeyIx`). Each action gets the
prefix / flowLevel / new-token / invariant-preservation lemmas the
per-dispatcher chain (Step 6d.1e.3+) will consume.

The legacy counterparts live in:

- `Proofs/Scanner/ScannerCorrectness.lean` — prefix / flowLevel /
  token-count side (lines ~200, ~263, ~280, ~379);
- `Proofs/Production/ScannerPlainScalarValid.lean` — invariant
  preservation (lines ~164, ~1081, ~1091, ~1699, ~1719). -/

/-! ### §6a  `emit .blockEnd` step combinator

`unwindIndentsLoopIx` emits `.blockEnd` tokens then pops the indent
stack. The pop is a record update on `indents` only and is invisible
to all our predicates. This subsection isolates the lemmas about the
single `.blockEnd` emit + pop step. -/

/-- After-emit-and-pop state shape used by `unwindIndentsLoopIx`. -/
abbrev emitBlockEndPop {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }

@[simp] private theorem emitBlockEndPop_tokens {input : String}
    (s : ScannerStateIx input) :
    (emitBlockEndPop s).tokens = (s.emit .blockEnd).tokens := rfl

@[simp] private theorem emitBlockEndPop_flowLevel {input : String}
    (s : ScannerStateIx input) :
    (emitBlockEndPop s).flowLevel = s.flowLevel := rfl

/-! ### §6b  `unwindIndentsLoopIx` preservation -/

/-- `unwindIndentsLoopIx` preserves the token prefix at low indices.
    Indexed twin of legacy `unwindIndentsLoop_preserves_prefix`. -/
theorem unwindIndentsLoopIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (i : Nat) (h_bound : i < s.tokens.size) :
    (unwindIndentsLoopIx s col fuel).tokens[i]'(by
        have := unwindIndentsLoopIx_tokens_size_le s col fuel; omega) =
    s.tokens[i]'h_bound := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx
    split
    · -- recurse on the popped state
      have h_emit_size : (s.emit .blockEnd).tokens.size = s.tokens.size + 1 :=
        emit_tokens_size s .blockEnd
      have h_i_lt_pop : i < (emitBlockEndPop s).tokens.size := by
        show i < (s.emit .blockEnd).tokens.size; rw [h_emit_size]; omega
      have h_ih := ih (emitBlockEndPop s) h_i_lt_pop
      show (unwindIndentsLoopIx (emitBlockEndPop s) col fuel').tokens[i]'_ =
        s.tokens[i]'h_bound
      rw [h_ih]
      show (s.emit .blockEnd).tokens[i]'h_i_lt_pop = s.tokens[i]'h_bound
      exact emit_preserves_tokens_at s .blockEnd i h_bound
    · rfl

/-- `unwindIndentsLoopIx` preserves `flowLevel`.
    Indexed twin of legacy `unwindIndentsLoop_preserves_flowLevel`. -/
theorem unwindIndentsLoopIx_preserves_flowLevel {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat) :
    (unwindIndentsLoopIx s col fuel).flowLevel = s.flowLevel := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx
    split
    · rw [ih]; rfl
    · rfl

/-- `unwindIndentsLoopIx` only emits `.blockEnd` tokens at new positions.
    Indexed twin of legacy `unwindIndentsLoop_new_tokens_not_plain`. -/
theorem unwindIndentsLoopIx_new_tokens_not_plain {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (j : Nat) (hj : j < (unwindIndentsLoopIx s col fuel).tokens.size)
    (hge : j ≥ s.tokens.size) :
    match ((unwindIndentsLoopIx s col fuel).tokens[j]'hj).token with
    | .scalar _ .plain => False
    | _ => True := by
  induction fuel generalizing s with
  | zero =>
    -- fuel = 0: result is `s`, but hge says j ≥ s.tokens.size — contradicts hj.
    unfold unwindIndentsLoopIx at hj; omega
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx at hj ⊢
    split at hj
    · -- emit-and-recurse branch
      rename_i h_cond
      simp only [h_cond, ↓reduceIte]
      have h_emit_size : (s.emit .blockEnd).tokens.size = s.tokens.size + 1 :=
        emit_tokens_size s .blockEnd
      by_cases hlt : j < s.tokens.size + 1
      · have h_jeq : j = s.tokens.size := by omega
        subst h_jeq
        have h_pop_sz : s.tokens.size < (emitBlockEndPop s).tokens.size := by
          show s.tokens.size < (s.emit .blockEnd).tokens.size; rw [h_emit_size]; omega
        have h_prefix := unwindIndentsLoopIx_preserves_prefix (emitBlockEndPop s) col fuel'
          s.tokens.size h_pop_sz
        show match ((unwindIndentsLoopIx (emitBlockEndPop s) col fuel').tokens[s.tokens.size]'hj).token with
          | .scalar _ .plain => False | _ => True
        rw [h_prefix]
        show match ((s.emit .blockEnd).tokens[s.tokens.size]'h_pop_sz).token with
          | .scalar _ .plain => False | _ => True
        rw [emit_new_token_token s .blockEnd h_pop_sz]
        trivial
      · have hge' : j ≥ (emitBlockEndPop s).tokens.size := by
          show j ≥ (s.emit .blockEnd).tokens.size; rw [h_emit_size]; omega
        exact ih (emitBlockEndPop s) hj hge'
    · -- identity branch: j ≥ s.tokens.size but also j < s.tokens.size — contradiction
      omega

/-- `unwindIndentsLoopIx` only emits non-flow tokens at new positions.
    Same shape as `_new_tokens_not_plain` but for the matched-brackets
    proof side (Step 6d.1e.7's `FlowBracketsMatchedIx` discharge). -/
theorem unwindIndentsLoopIx_new_tokens_not_flow {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (j : Nat) (hj : j < (unwindIndentsLoopIx s col fuel).tokens.size)
    (hge : j ≥ s.tokens.size) :
    ((unwindIndentsLoopIx s col fuel).tokens[j]'hj).token ≠ .flowSequenceStart ∧
    ((unwindIndentsLoopIx s col fuel).tokens[j]'hj).token ≠ .flowMappingStart ∧
    ((unwindIndentsLoopIx s col fuel).tokens[j]'hj).token ≠ .flowSequenceEnd ∧
    ((unwindIndentsLoopIx s col fuel).tokens[j]'hj).token ≠ .flowMappingEnd := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx at hj; omega
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx at hj ⊢
    split at hj
    · rename_i h_cond
      simp only [h_cond, ↓reduceIte]
      have h_emit_size : (s.emit .blockEnd).tokens.size = s.tokens.size + 1 :=
        emit_tokens_size s .blockEnd
      by_cases hlt : j < s.tokens.size + 1
      · have h_jeq : j = s.tokens.size := by omega
        subst h_jeq
        have h_pop_sz : s.tokens.size < (emitBlockEndPop s).tokens.size := by
          show s.tokens.size < (s.emit .blockEnd).tokens.size; rw [h_emit_size]; omega
        have h_prefix := unwindIndentsLoopIx_preserves_prefix (emitBlockEndPop s) col fuel'
          s.tokens.size h_pop_sz
        show ((unwindIndentsLoopIx (emitBlockEndPop s) col fuel').tokens[s.tokens.size]'hj).token ≠ _ ∧ _
        rw [h_prefix]
        show ((s.emit .blockEnd).tokens[s.tokens.size]'h_pop_sz).token ≠ _ ∧ _
        rw [emit_new_token_token s .blockEnd h_pop_sz]
        decide
      · have hge' : j ≥ (emitBlockEndPop s).tokens.size := by
          show j ≥ (s.emit .blockEnd).tokens.size; rw [h_emit_size]; omega
        exact ih (emitBlockEndPop s) hj hge'
    · omega

/-- `unwindIndentsLoopIx` preserves `FlowNestingInvIx`.
    Indexed twin of legacy `unwindIndentsLoop_preserves_FlowNestingInv`. -/
theorem unwindIndentsLoopIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (unwindIndentsLoopIx s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoopIx; exact h_fni
  | succ fuel' ih =>
    unfold unwindIndentsLoopIx
    split
    · -- emit .blockEnd then recurse; .blockEnd is non-flow.
      apply ih
      have h_emit_fni : FlowNestingInvIx (s.emit .blockEnd) :=
        emit_non_flow_preserves_FlowNestingInvIx s .blockEnd h_fni
          (by decide) (by decide) (by decide) (by decide)
      unfold FlowNestingInvIx at *
      show flowNestingIx (s.emit .blockEnd).tokens (s.emit .blockEnd).tokens.size = _
      exact h_emit_fni
    · exact h_fni

/-- `unwindIndentsLoopIx` preserves `PlainScalarsValidIx`.
    Composes `_of_prefix_and_new` (§1) with `_preserves_prefix`,
    `_tokens_size_le`, and `_new_tokens_not_plain`. -/
theorem unwindIndentsLoopIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (unwindIndentsLoopIx s col fuel).tokens := by
  refine PlainScalarsValidIx_of_prefix_and_new s.tokens
    (unwindIndentsLoopIx s col fuel).tokens h_old
    (unwindIndentsLoopIx_tokens_size_le s col fuel) ?_ ?_
  · intro i hi
    exact unwindIndentsLoopIx_preserves_prefix s col fuel i hi
  · intro j hj hge
    exact psv_of_not_plain_ix _
      (unwindIndentsLoopIx_new_tokens_not_plain s col fuel j hj hge)

/-- `unwindIndentsLoopIx` preserves `FlowContextPSVIx`.
    Composes `_of_prefix_and_new` (§3) with the same trio. -/
theorem unwindIndentsLoopIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat)
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (unwindIndentsLoopIx s col fuel).tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens
    (unwindIndentsLoopIx s col fuel).tokens h_old
    (unwindIndentsLoopIx_tokens_size_le s col fuel) ?_ ?_
  · intro i hi
    exact unwindIndentsLoopIx_preserves_prefix s col fuel i hi
  · intro j hj hge _h_flow
    exact fpsv_of_not_plain_ix _
      (unwindIndentsLoopIx_new_tokens_not_plain s col fuel j hj hge)

/-! ### §6c  `unwindIndentsIx` preservation — thin wrappers -/

/-- `unwindIndentsIx` preserves the token prefix. -/
theorem unwindIndentsIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (col : Int) (i : Nat) (h_bound : i < s.tokens.size) :
    (unwindIndentsIx s col).tokens[i]'(by
        have := unwindIndentsIx_tokens_size_le s col; omega) =
    s.tokens[i]'h_bound :=
  unwindIndentsLoopIx_preserves_prefix s col s.indents.size i h_bound

/-- `unwindIndentsIx` preserves `flowLevel`. -/
theorem unwindIndentsIx_preserves_flowLevel {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (unwindIndentsIx s col).flowLevel = s.flowLevel :=
  unwindIndentsLoopIx_preserves_flowLevel s col s.indents.size

/-- `unwindIndentsIx` only emits non-plain tokens at new positions. -/
theorem unwindIndentsIx_new_tokens_not_plain {input : String}
    (s : ScannerStateIx input) (col : Int)
    (j : Nat) (hj : j < (unwindIndentsIx s col).tokens.size)
    (hge : j ≥ s.tokens.size) :
    match ((unwindIndentsIx s col).tokens[j]'hj).token with
    | .scalar _ .plain => False
    | _ => True :=
  unwindIndentsLoopIx_new_tokens_not_plain s col s.indents.size j hj hge

/-- `unwindIndentsIx` only emits non-flow tokens at new positions. -/
theorem unwindIndentsIx_new_tokens_not_flow {input : String}
    (s : ScannerStateIx input) (col : Int)
    (j : Nat) (hj : j < (unwindIndentsIx s col).tokens.size)
    (hge : j ≥ s.tokens.size) :
    ((unwindIndentsIx s col).tokens[j]'hj).token ≠ .flowSequenceStart ∧
    ((unwindIndentsIx s col).tokens[j]'hj).token ≠ .flowMappingStart ∧
    ((unwindIndentsIx s col).tokens[j]'hj).token ≠ .flowSequenceEnd ∧
    ((unwindIndentsIx s col).tokens[j]'hj).token ≠ .flowMappingEnd :=
  unwindIndentsLoopIx_new_tokens_not_flow s col s.indents.size j hj hge

/-- `unwindIndentsIx` preserves `FlowNestingInvIx`. -/
theorem unwindIndentsIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (unwindIndentsIx s col) :=
  unwindIndentsLoopIx_preserves_FlowNestingInvIx s col s.indents.size h_fni

/-- `unwindIndentsIx` preserves `PlainScalarsValidIx`. -/
theorem unwindIndentsIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (unwindIndentsIx s col).tokens :=
  unwindIndentsLoopIx_preserves_PlainScalarsValidIx s col s.indents.size h_old

/-- `unwindIndentsIx` preserves `FlowContextPSVIx`. -/
theorem unwindIndentsIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (unwindIndentsIx s col).tokens :=
  unwindIndentsLoopIx_preserves_FlowContextPSVIx s col s.indents.size h_old

/-! ### §6d  `pushSequenceIndentIx` preservation -/

/-- `pushSequenceIndentIx` preserves the token prefix. -/
theorem pushSequenceIndentIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (col : Int) (i : Nat) (h_bound : i < s.tokens.size) :
    (pushSequenceIndentIx s col).tokens[i]'(by
        have := pushSequenceIndentIx_tokens_size_le s col; omega) =
    s.tokens[i]'h_bound := by
  unfold pushSequenceIndentIx
  split
  · -- emits `.blockSequenceStart`, then a record update on indents.
    show (s.emit .blockSequenceStart).tokens[i]'_ = s.tokens[i]'h_bound
    exact emit_preserves_tokens_at s .blockSequenceStart i h_bound
  · rfl

/-- `pushSequenceIndentIx` preserves `PlainScalarsValidIx`.
    Indexed twin of legacy `pushSequenceIndent_preserves_PlainScalarsValid`. -/
theorem pushSequenceIndentIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (pushSequenceIndentIx s col).tokens := by
  unfold pushSequenceIndentIx
  split
  · show PlainScalarsValidIx ({ (s.emit .blockSequenceStart) with indents := _ }.tokens)
    exact emit_non_plain_preserves_PlainScalarsValidIx s .blockSequenceStart h_old (by trivial)
  · exact h_old

/-- `pushSequenceIndentIx` preserves `FlowNestingInvIx`. -/
theorem pushSequenceIndentIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (pushSequenceIndentIx s col) := by
  unfold pushSequenceIndentIx
  split
  · -- emits `.blockSequenceStart` (non-flow) then record update on indents.
    unfold FlowNestingInvIx at *
    show flowNestingIx (s.emit .blockSequenceStart).tokens
      (s.emit .blockSequenceStart).tokens.size = _
    exact emit_non_flow_preserves_FlowNestingInvIx s .blockSequenceStart h_fni
      (by decide) (by decide) (by decide) (by decide)
  · exact h_fni

/-- `pushSequenceIndentIx` preserves `FlowContextPSVIx`. -/
theorem pushSequenceIndentIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (pushSequenceIndentIx s col).tokens := by
  unfold pushSequenceIndentIx
  split
  · show FlowContextPSVIx ({ (s.emit .blockSequenceStart) with indents := _ }.tokens)
    exact emit_non_flow_non_plain_preserves_FlowContextPSVIx s .blockSequenceStart h_old
      (by trivial) (by decide) (by decide) (by decide) (by decide)
  · exact h_old

/-! ### §6e  `pushMappingIndentIx` preservation -/

/-- `pushMappingIndentIx` preserves the token prefix. -/
theorem pushMappingIndentIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (col : Int) (i : Nat) (h_bound : i < s.tokens.size) :
    (pushMappingIndentIx s col).tokens[i]'(by
        have := pushMappingIndentIx_tokens_size_le s col; omega) =
    s.tokens[i]'h_bound := by
  unfold pushMappingIndentIx
  split
  · show (s.emit .blockMappingStart).tokens[i]'_ = s.tokens[i]'h_bound
    exact emit_preserves_tokens_at s .blockMappingStart i h_bound
  · rfl

/-- `pushMappingIndentIx` preserves `PlainScalarsValidIx`.
    Indexed twin of legacy `pushMappingIndent_preserves_PlainScalarsValid`. -/
theorem pushMappingIndentIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (pushMappingIndentIx s col).tokens := by
  unfold pushMappingIndentIx
  split
  · show PlainScalarsValidIx ({ (s.emit .blockMappingStart) with indents := _ }.tokens)
    exact emit_non_plain_preserves_PlainScalarsValidIx s .blockMappingStart h_old (by trivial)
  · exact h_old

/-- `pushMappingIndentIx` preserves `FlowNestingInvIx`. -/
theorem pushMappingIndentIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (pushMappingIndentIx s col) := by
  unfold pushMappingIndentIx
  split
  · unfold FlowNestingInvIx at *
    show flowNestingIx (s.emit .blockMappingStart).tokens
      (s.emit .blockMappingStart).tokens.size = _
    exact emit_non_flow_preserves_FlowNestingInvIx s .blockMappingStart h_fni
      (by decide) (by decide) (by decide) (by decide)
  · exact h_fni

/-- `pushMappingIndentIx` preserves `FlowContextPSVIx`. -/
theorem pushMappingIndentIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (col : Int) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (pushMappingIndentIx s col).tokens := by
  unfold pushMappingIndentIx
  split
  · show FlowContextPSVIx ({ (s.emit .blockMappingStart) with indents := _ }.tokens)
    exact emit_non_flow_non_plain_preserves_FlowContextPSVIx s .blockMappingStart h_old
      (by trivial) (by decide) (by decide) (by decide) (by decide)
  · exact h_old

/-! ### §6f  `saveSimpleKeyIx` preservation

`saveSimpleKeyIx` either leaves tokens unchanged or pushes two
`.placeholder` tokens. Both are non-plain and non-flow, so all the
preservation lemmas follow from §5. -/

/-- Abbreviation for the post-`saveSimpleKeyIx` state in its two-emit
    branch (no `simpleKey` record update — that is invisible to
    `tokens` / `flowLevel`). -/
abbrev twoPlaceholderEmits {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  (s.emit YamlToken.placeholder).emit YamlToken.placeholder

/-- `saveSimpleKeyIx` either leaves tokens unchanged or pushes two
    placeholder tokens. Eliminates the if-chain in `saveSimpleKeyIx`
    so downstream proofs case-split on this disjunction rather than
    unfolding the body. -/
theorem saveSimpleKeyIx_tokens_cases {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).tokens = s.tokens ∨
    (saveSimpleKeyIx s).tokens = (twoPlaceholderEmits s).tokens := by
  unfold saveSimpleKeyIx
  split
  · left; rfl
  · split
    · right; rfl
    · left; rfl

theorem saveSimpleKeyIx_flowLevel_eq {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).flowLevel = s.flowLevel := by
  unfold saveSimpleKeyIx
  split
  · rfl
  · split <;> rfl

/-- Two-emit prefix preservation, factored out for the `saveSimpleKeyIx`
    two-emit branch. -/
theorem twoPlaceholderEmits_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[i]'(by
        rw [emit_tokens_size, emit_tokens_size]; omega) =
    s.tokens[i]'h_bound := by
  have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
    emit_tokens_size s .placeholder
  have h_i_lt1 : i < (s.emit YamlToken.placeholder).tokens.size := by
    rw [h_size1]; omega
  have h_step1 : (s.emit YamlToken.placeholder).tokens[i]'h_i_lt1 = s.tokens[i]'h_bound :=
    emit_preserves_tokens_at s .placeholder i h_bound
  rw [emit_preserves_tokens_at (s.emit YamlToken.placeholder) .placeholder i h_i_lt1]
  exact h_step1

/-- `saveSimpleKeyIx` preserves the token prefix.
    Indexed twin of legacy `saveSimpleKey_preserves_prefix`. -/
theorem saveSimpleKeyIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (saveSimpleKeyIx s).tokens[i]'(by
        have := saveSimpleKeyIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  rcases saveSimpleKeyIx_tokens_cases s with h_eq | h_eq
  · -- identity branch
    simp only [h_eq]
  · -- two-emit branch
    simp only [h_eq]
    exact twoPlaceholderEmits_preserves_prefix s i h_bound

/-- `saveSimpleKeyIx` preserves `flowLevel`.
    Indexed twin of legacy `saveSimpleKey_preserves_flowLevel`. -/
@[simp] theorem saveSimpleKeyIx_flowLevel {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).flowLevel = s.flowLevel :=
  saveSimpleKeyIx_flowLevel_eq s

/-- The new-position token after two `.placeholder` emits is non-plain
    regardless of which of the two slots is queried. -/
theorem twoPlaceholderEmits_new_not_plain {input : String}
    (s : ScannerStateIx input) (j : Nat)
    (hj : j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size)
    (hge : j ≥ s.tokens.size) :
    match (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[j]'hj).token with
    | .scalar _ .plain => False
    | _ => True := by
  have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
    emit_tokens_size s .placeholder
  have h_size2 : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size =
      s.tokens.size + 2 := by rw [emit_tokens_size, h_size1]
  by_cases hlt : j < s.tokens.size + 1
  · have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    have h_pop_sz : s.tokens.size < (s.emit YamlToken.placeholder).tokens.size := by
      rw [h_size1]; omega
    have h_step : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size]'hj =
        (s.emit YamlToken.placeholder).tokens[s.tokens.size]'h_pop_sz :=
      emit_preserves_tokens_at (s.emit YamlToken.placeholder) .placeholder s.tokens.size h_pop_sz
    rw [h_step]
    rw [emit_new_token_token s .placeholder h_pop_sz]
    trivial
  · have h_jeq : j = (s.emit YamlToken.placeholder).tokens.size := by rw [h_size1]; omega
    have h_pop_sz : (s.emit YamlToken.placeholder).tokens.size <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [emit_tokens_size]; omega
    subst h_jeq
    have h_get := emit_new_token_token (s.emit YamlToken.placeholder) .placeholder h_pop_sz
    rw [h_get]; trivial

theorem twoPlaceholderEmits_new_not_flow {input : String}
    (s : ScannerStateIx input) (j : Nat)
    (hj : j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size)
    (hge : j ≥ s.tokens.size) :
    (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[j]'hj).token ≠
      .flowSequenceStart ∧
    (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[j]'hj).token ≠
      .flowMappingStart ∧
    (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[j]'hj).token ≠
      .flowSequenceEnd ∧
    (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[j]'hj).token ≠
      .flowMappingEnd := by
  have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
    emit_tokens_size s .placeholder
  have h_size2 : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size =
      s.tokens.size + 2 := by rw [emit_tokens_size, h_size1]
  by_cases hlt : j < s.tokens.size + 1
  · have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    have h_pop_sz : s.tokens.size < (s.emit YamlToken.placeholder).tokens.size := by
      rw [h_size1]; omega
    have h_step : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size]'hj =
        (s.emit YamlToken.placeholder).tokens[s.tokens.size]'h_pop_sz :=
      emit_preserves_tokens_at (s.emit YamlToken.placeholder) .placeholder s.tokens.size h_pop_sz
    rw [h_step]
    rw [emit_new_token_token s .placeholder h_pop_sz]
    decide
  · have h_jeq : j = (s.emit YamlToken.placeholder).tokens.size := by rw [h_size1]; omega
    have h_pop_sz : (s.emit YamlToken.placeholder).tokens.size <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [emit_tokens_size]; omega
    subst h_jeq
    have h_get := emit_new_token_token (s.emit YamlToken.placeholder) .placeholder h_pop_sz
    rw [h_get]; decide

/-- `saveSimpleKeyIx` only inserts `.placeholder` tokens at new positions.
    Indexed twin of legacy `saveSimpleKey_new_tokens_not_plain`. -/
theorem saveSimpleKeyIx_new_tokens_not_plain {input : String} (s : ScannerStateIx input)
    (j : Nat) (hj : j < (saveSimpleKeyIx s).tokens.size) (hge : j ≥ s.tokens.size) :
    match ((saveSimpleKeyIx s).tokens[j]'hj).token with
    | .scalar _ .plain => False
    | _ => True := by
  rcases saveSimpleKeyIx_tokens_cases s with h_eq | h_eq
  · -- identity branch: hj + hge contradicts via h_eq.
    have h_sz : (saveSimpleKeyIx s).tokens.size = s.tokens.size :=
      congrArg Indexed.TokenStream.size h_eq
    rw [h_sz] at hj; omega
  · -- two-emit branch: forward to the helper.
    simp only [h_eq] at hj ⊢
    exact twoPlaceholderEmits_new_not_plain s j hj hge

/-- `saveSimpleKeyIx` only inserts non-flow tokens at new positions. -/
theorem saveSimpleKeyIx_new_tokens_not_flow {input : String} (s : ScannerStateIx input)
    (j : Nat) (hj : j < (saveSimpleKeyIx s).tokens.size) (hge : j ≥ s.tokens.size) :
    ((saveSimpleKeyIx s).tokens[j]'hj).token ≠ .flowSequenceStart ∧
    ((saveSimpleKeyIx s).tokens[j]'hj).token ≠ .flowMappingStart ∧
    ((saveSimpleKeyIx s).tokens[j]'hj).token ≠ .flowSequenceEnd ∧
    ((saveSimpleKeyIx s).tokens[j]'hj).token ≠ .flowMappingEnd := by
  rcases saveSimpleKeyIx_tokens_cases s with h_eq | h_eq
  · have h_sz : (saveSimpleKeyIx s).tokens.size = s.tokens.size :=
      congrArg Indexed.TokenStream.size h_eq
    rw [h_sz] at hj; omega
  · simp only [h_eq] at hj ⊢
    exact twoPlaceholderEmits_new_not_flow s j hj hge

/-- `saveSimpleKeyIx` preserves `PlainScalarsValidIx`. -/
theorem saveSimpleKeyIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (saveSimpleKeyIx s).tokens := by
  refine PlainScalarsValidIx_of_prefix_and_new s.tokens (saveSimpleKeyIx s).tokens h_old
    (saveSimpleKeyIx_tokens_size_le s) ?_ ?_
  · intro i hi; exact saveSimpleKeyIx_preserves_prefix s i hi
  · intro j hj hge
    exact psv_of_not_plain_ix _ (saveSimpleKeyIx_new_tokens_not_plain s j hj hge)

/-- `saveSimpleKeyIx` preserves `FlowNestingInvIx`.
    Indexed twin of legacy `saveSimpleKey_preserves_FlowNestingInv`. -/
theorem saveSimpleKeyIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (saveSimpleKeyIx s) := by
  unfold saveSimpleKeyIx
  split
  · exact h_fni
  · split
    · -- two-emit branch: each emit is non-flow (.placeholder).
      have h_fni1 : FlowNestingInvIx (s.emit YamlToken.placeholder) :=
        emit_non_flow_preserves_FlowNestingInvIx s .placeholder h_fni
          (by decide) (by decide) (by decide) (by decide)
      have h_fni2 : FlowNestingInvIx ((s.emit YamlToken.placeholder).emit YamlToken.placeholder) :=
        emit_non_flow_preserves_FlowNestingInvIx _ .placeholder h_fni1
          (by decide) (by decide) (by decide) (by decide)
      -- The record update on simpleKey doesn't touch tokens or flowLevel.
      unfold FlowNestingInvIx at *
      show flowNestingIx ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size = s.flowLevel
      exact h_fni2
    · exact h_fni

/-- `saveSimpleKeyIx` preserves `FlowContextPSVIx`. -/
theorem saveSimpleKeyIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (saveSimpleKeyIx s).tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens (saveSimpleKeyIx s).tokens h_old
    (saveSimpleKeyIx_tokens_size_le s) ?_ ?_
  · intro i hi; exact saveSimpleKeyIx_preserves_prefix s i hi
  · intro j hj hge _h_flow
    exact fpsv_of_not_plain_ix _ (saveSimpleKeyIx_new_tokens_not_plain s j hj hge)

/-! ## §7  Scalar-scanner per-action preservation (Step 6d.1e.3)

State-transforming scalar scanners — `scanAnchorOrAliasIx` and
`scanTagIx`. Each gets the standard preservation suite:
`_adds_one_token`, `_preserves_prefix`, `_preserves_flowLevel`,
`_new_token_not_plain`, `_new_token_not_flow`,
`_preserves_PlainScalarsValidIx`, `_preserves_FlowNestingInvIx`,
`_preserves_FlowContextPSVIx`.

**Note on the four pure scalar primitives**: `scanDoubleQuotedIx`,
`scanSingleQuotedIx`, `scanBlockScalarIx`, and `scanPlainScalarIx`
do *not* return `ScannerStateIx input` — they return
`Option (String × IxCursor input)` (or the cursor-tuple variant).
Their PSV reasoning therefore lives at the dispatcher level
(`scanNextTokenIx_dispatchContent`, 6d.1e.6), where the dispatcher
arm calls the primitive and then `emitAt`s the resulting
`.scalar content style` token. The plain-scalar case will need the
`scanPlainScalarIx_content_valid` side condition from
`Proofs/Scanner/IndexedScalar.lean` Layer F.4 (8 branch-mapping
lemmas already in place) — staged in 6d.1e.6 either as a third axiom
or proven inline depending on the Layer F.4 integration cost. -/

/-! ### §7a  `emitAt` building blocks

`emitAt`-twins of the `emit` building blocks from §5. Both `emit`
and `emitAt` push exactly one `IxToken` and differ only in the start
position carried in the new token's `.start` field — irrelevant for
PSV / FlowNestingInv / FlowContextPSV, which all dispatch on
`.token`. -/

/-- Non-cursor record-update view of `emitAt`: tokens grow by one. -/
theorem emitAt_tokens_size {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok hOrder).tokens.size = s.tokens.size + 1 := by
  unfold ScannerStateIx.emitAt
  show (s.tokens.tokens.push _).size = s.tokens.tokens.size + 1
  exact Array.size_push ..

/-- `emitAt` preserves tokens at low indices.
    `emitAt`-twin of `emit_preserves_tokens_at`. -/
theorem emitAt_preserves_tokens_at {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (j : Nat) (h : j < s.tokens.size) :
    (s.emitAt startPos tok hOrder).tokens[j]'(by
        change j < (s.tokens.tokens.push _).size
        rw [Array.size_push]
        change j < s.tokens.tokens.size + 1 at *
        exact Nat.lt_succ_of_lt h) = s.tokens[j]'h := by
  change (s.tokens.tokens.push _)[j]'_ = s.tokens.tokens[j]'h
  exact Array.getElem_push_lt ..

/-- New-token characterization for `emitAt`. The token added at
    position `s.tokens.size` is exactly `tok`. -/
theorem emitAt_new_token_token {input : String} (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h : s.tokens.size < (s.emitAt startPos tok hOrder).tokens.size) :
    ((s.emitAt startPos tok hOrder).tokens[s.tokens.size]'h).token = tok := by
  have h_get : (s.emitAt startPos tok hOrder).tokens[s.tokens.size]'h =
      IxToken.mk' startPos tok s.cursor.pos hOrder s.cursor.posBound := by
    change (s.tokens.tokens.push _)[s.tokens.tokens.size]'h = _
    exact Array.getElem_push_eq ..
  rw [h_get]; rfl

/-- `emitAt` of a non-plain token preserves `PlainScalarsValidIx`. -/
theorem emitAt_non_plain_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_old : PlainScalarsValidIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValidIx (s.emitAt startPos tok hOrder).tokens := by
  refine PlainScalarsValidIx_of_prefix_and_new s.tokens
    (s.emitAt startPos tok hOrder).tokens h_old (by
      rw [emitAt_tokens_size]; omega) ?_ ?_
  · intro i hi; exact emitAt_preserves_tokens_at s startPos tok hOrder i hi
  · intro j hj hge
    have h_jeq : j = s.tokens.size := by
      rw [emitAt_tokens_size] at hj; omega
    subst h_jeq
    rw [emitAt_new_token_token s startPos tok hOrder hj]
    cases tok <;> simp_all
    rename_i content style; cases style <;> simp_all

/-- `emitAt` of a non-flow token preserves `FlowNestingInvIx`.
    Mirrors `emit_non_flow_preserves_FlowNestingInvIx`, because
    `flowNestingIx_push_non_flow` only looks at the new token's
    `.token` (not its `.start` / `.stop`). -/
theorem emitAt_non_flow_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_fni : FlowNestingInvIx s)
    (h_nfs : tok ≠ .flowSequenceStart) (h_nfe : tok ≠ .flowSequenceEnd)
    (h_nms : tok ≠ .flowMappingStart) (h_nme : tok ≠ .flowMappingEnd) :
    FlowNestingInvIx (s.emitAt startPos tok hOrder) := by
  unfold FlowNestingInvIx at h_fni ⊢
  unfold flowNestingIx at h_fni ⊢
  unfold ScannerStateIx.emitAt
  show flowNestingIx.go (s.tokens.tokens.push _) 0
    (s.tokens.tokens.push _).size 0 = s.flowLevel
  rw [Array.size_push]
  rw [flowNestingIx_push_non_flow s.tokens.tokens _ h_nfs h_nms h_nfe h_nme]
  exact h_fni

/-- `emitAt` of a non-flow, non-plain token preserves `FlowContextPSVIx`. -/
theorem emitAt_non_flow_non_plain_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_old : FlowContextPSVIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True) :
    FlowContextPSVIx (s.emitAt startPos tok hOrder).tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens
    (s.emitAt startPos tok hOrder).tokens h_old (by
      rw [emitAt_tokens_size]; omega) ?_ ?_
  · intro i hi; exact emitAt_preserves_tokens_at s startPos tok hOrder i hi
  · intro j hj hge _h_flow
    have h_jeq : j = s.tokens.size := by
      rw [emitAt_tokens_size] at hj; omega
    subst h_jeq
    have h_new : ((s.emitAt startPos tok hOrder).tokens[s.tokens.size]'hj).token = tok :=
      emitAt_new_token_token s startPos tok hOrder hj
    rw [h_new]
    cases tok <;> simp_all
    rename_i content style; cases style <;> simp_all

/-! ### §7b  `scanAnchorOrAliasIx` preservation — staged as axioms (Step 6d.1e.3)

`scanAnchorOrAliasIx s isAnchor` is `.ok` exactly when the anchor
name is non-empty; on `.ok`, the new token is `.anchor name` (if
`isAnchor`) or `.alias name` (otherwise). Neither is `.scalar _ .plain`
nor a flow bracket.

**Staging note**: these 8 axioms are pure scanner-side
preservation lemmas — they only require the legacy proof patterns
adapted through `change`/`show` bridging. Initial proof attempts
hit the "record-update opacity" wall (the outer
`{ sEmit with simpleKeyAllowed := false, definedAnchors := … }`
wrap doesn't let `Array.getElem_push_eq` fire via `rw` or `simp`
without additional structural lemmas — see Reflection 70). Landed
as **axioms with real `(_h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')`
preconditions** so downstream dispatchers (6d.1e.4+) can be built
on top; discharge moves to a dedicated 6d.1e.3b session (or rolled
into 6d.1e.7 alongside the §8 discharge). -/

theorem scanAnchorOrAliasIx_adds_one_token {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; simp

theorem scanAnchorOrAliasIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (i : Nat) (hi : i < s.tokens.size) :
    s'.tokens[i]'(by
      rw [scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok]
      exact Nat.lt_succ_of_lt hi) = s.tokens[i]'hi := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show (s.tokens.tokens.push _)[i]'_ = s.tokens.tokens[i]'hi
    exact Array.getElem_push_lt ..

theorem scanAnchorOrAliasIx_preserves_flowLevel {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; rfl

theorem scanAnchorOrAliasIx_new_token_not_plain {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    match (s'.tokens[s.tokens.size]'hj).token with
    | .scalar _ .plain => False
    | _ => True := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show (match ((s.tokens.tokens.push (IxToken.mk' s.cursor.pos
              (if isAnchor then YamlToken.anchor (collectAnchorNameLoopIx
                  s.advance.cursor "" (input.utf8ByteSize - s.advance.cursor.pos.offset)).fst
               else YamlToken.alias (collectAnchorNameLoopIx s.advance.cursor ""
                  (input.utf8ByteSize - s.advance.cursor.pos.offset)).fst)
              _ _ _))[s.tokens.tokens.size]'_).token with
          | .scalar _ .plain => False | _ => True)
    simp only [Array.getElem_push_eq, IxToken.mk']
    split
    · rename_i heq; split at heq <;> cases heq
    · trivial

theorem scanAnchorOrAliasIx_new_token_not_flow {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceEnd ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingEnd := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok
    subst h_ok
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (
      show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
        rw [Array.size_push]; omega)) : IxToken input).token ≠ _
      simp only [Array.getElem_push_eq, IxToken.mk']
      split <;> (intro h; cases h))

/-- `scanAnchorOrAliasIx` preserves `PlainScalarsValidIx` — proven
    using the (staged-as-axiom) prefix + new-token-not-plain lemmas,
    so this composition theorem itself is a real `theorem`. -/
theorem scanAnchorOrAliasIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  refine PlainScalarsValidIx_of_prefix_and_new s.tokens s'.tokens h_old
    (by rw [scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok]; omega) ?_ ?_
  · intro i hi; exact scanAnchorOrAliasIx_preserves_prefix s isAnchor s' h_ok i hi
  · intro j hj hge
    have h_size := scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok
    have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    exact psv_of_not_plain_ix _
      (scanAnchorOrAliasIx_new_token_not_plain s isAnchor s' h_ok hj)

/-- `scanAnchorOrAliasIx` preserves `FlowContextPSVIx` — proven
    using the staged-as-axiom prefix + new-token-not-plain lemmas. -/
theorem scanAnchorOrAliasIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens s'.tokens h_old
    (by rw [scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok]; omega) ?_ ?_
  · intro i hi; exact scanAnchorOrAliasIx_preserves_prefix s isAnchor s' h_ok i hi
  · intro j hj hge _h_flow
    have h_size := scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok
    have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    exact fpsv_of_not_plain_ix _
      (scanAnchorOrAliasIx_new_token_not_plain s isAnchor s' h_ok hj)

theorem scanAnchorOrAliasIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanAnchorOrAliasIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · simp at h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    split
    · exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
    · exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)

/-! ### §7c  `scanTagIx` preservation — staged as axioms (Step 6d.1e.3)

Same staging rationale as §7b: `scanTagIx s` has three success
branches all emitting `.tag _ _` tokens; the proof shape is the
legacy `scanTag_psv_match` adapted with `change`/`show` bridging,
but the same record-update opacity wall (Reflection 70) prevents
clean Lean 4 ports without additional structural lemmas. Discharged
in a dedicated 6d.1e.3b or as part of 6d.1e.7. -/

theorem scanTagIx_adds_one_token {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · -- some '<' branch
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok; simp
  · -- some '!' branch
    simp only [Except.ok.injEq] at h_ok; subst h_ok; simp
  · -- default branch
    simp only [Except.ok.injEq] at h_ok; subst h_ok; simp

theorem scanTagIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (i : Nat) (hi : i < s.tokens.size) :
    s'.tokens[i]'(by
      rw [scanTagIx_adds_one_token s s' h_ok]
      exact Nat.lt_succ_of_lt hi) = s.tokens[i]'hi := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · -- some '<' (verbatim tag)
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        show (s.tokens.tokens.push _)[i]'_ = s.tokens.tokens[i]'hi
        exact Array.getElem_push_lt ..
  · -- some '!' (secondary tag)
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    show (s.tokens.tokens.push _)[i]'_ = s.tokens.tokens[i]'hi
    exact Array.getElem_push_lt ..
  · -- default (named/primary tag)
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    show (s.tokens.tokens.push _)[i]'_ = s.tokens.tokens[i]'hi
    exact Array.getElem_push_lt ..

theorem scanTagIx_preserves_flowLevel {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok; rfl
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; rfl
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; rfl

theorem scanTagIx_new_token_not_plain {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    match (s'.tokens[s.tokens.size]'hj).token with
    | .scalar _ .plain => False
    | _ => True := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        show (match ((((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
                rw [Array.size_push]; omega)) : IxToken input).token) with
              | .scalar _ .plain => False | _ => True)
        simp only [Array.getElem_push_eq, IxToken.mk']
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    show (match ((((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
            rw [Array.size_push]; omega)) : IxToken input).token) with
          | .scalar _ .plain => False | _ => True)
    simp only [Array.getElem_push_eq, IxToken.mk']
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    show (match ((((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
            rw [Array.size_push]; omega)) : IxToken input).token) with
          | .scalar _ .plain => False | _ => True)
    simp only [Array.getElem_push_eq, IxToken.mk']

theorem scanTagIx_new_token_not_flow {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceEnd ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingEnd := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        refine ⟨?_, ?_, ?_, ?_⟩ <;> (
          show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
            rw [Array.size_push]; omega)) : IxToken input).token ≠ _
          simp only [Array.getElem_push_eq, IxToken.mk']
          intro h; cases h)
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (
      show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
        rw [Array.size_push]; omega)) : IxToken input).token ≠ _
      simp only [Array.getElem_push_eq, IxToken.mk']
      intro h; cases h)
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    refine ⟨?_, ?_, ?_, ?_⟩ <;> (
      show (((s.tokens.tokens.push _)[s.tokens.tokens.size]'(by
        rw [Array.size_push]; omega)) : IxToken input).token ≠ _
      simp only [Array.getElem_push_eq, IxToken.mk']
      intro h; cases h)

theorem scanTagIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  refine PlainScalarsValidIx_of_prefix_and_new s.tokens s'.tokens h_old
    (by rw [scanTagIx_adds_one_token s s' h_ok]; omega) ?_ ?_
  · intro i hi; exact scanTagIx_preserves_prefix s s' h_ok i hi
  · intro j hj hge
    have h_size := scanTagIx_adds_one_token s s' h_ok
    have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    exact psv_of_not_plain_ix _ (scanTagIx_new_token_not_plain s s' h_ok hj)

theorem scanTagIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens s'.tokens h_old
    (by rw [scanTagIx_adds_one_token s s' h_ok]; omega) ?_ ?_
  · intro i hi; exact scanTagIx_preserves_prefix s s' h_ok i hi
  · intro j hj hge _h_flow
    have h_size := scanTagIx_adds_one_token s s' h_ok
    have h_jeq : j = s.tokens.size := by omega
    subst h_jeq
    exact fpsv_of_not_plain_ix _ (scanTagIx_new_token_not_plain s s' h_ok hj)

theorem scanTagIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanTagIx at h_ok
  dsimp only [] at h_ok
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
          (by intro h; cases h) (by intro h; cases h)
          (by intro h; cases h) (by intro h; cases h)
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)


/-! ## §8  Block-context dispatcher preservation (Step 6d.1e.4)

Preservation suites for the block-indicator scanners
`scanBlockEntryIx` (`-`), `scanKeyIx` (`?`), `scanValueIx` (`:`),
their sub-stages `scanValueClearKeyIx` / `scanValuePrepareIx`, and
the umbrella dispatcher `scanNextTokenIx_dispatchBlockIndicators`.

Strategy. The block-indicator scanners compose four kinds of
state-transforming primitives:
1. **Pure record updates** (`scanValueClearKeyIx`, `simpleKeyAllowed`
   tweaks, etc.) — tokens unchanged, preservation by `rfl`-style
   reasoning;
2. **`pushSequenceIndentIx` / `pushMappingIndentIx`** (§6d/§6e) —
   emit a single non-plain non-flow indent-start token;
3. **`s.emit YamlToken.{blockEntry,key,value}`** — emit a single
   non-plain non-flow indicator token (§5 building blocks);
4. **`s.overwriteAtCursor i sk tok`** (only in `scanValuePrepareIx`)
   — `setIfInBounds` overwrite with `.blockMappingStart` or `.key`.

§8a sets up the `setIfInBounds` infrastructure (PSV side; the
FCPSV / FlowNestingInv side for `setIfInBounds` is staged as the
single per-dispatcher axiom on `scanValuePrepareIx` because the
non-flow-original requirement needs a token-stream invariant the
indexed proof chain has not yet propagated — see §8e Reflection 71).

§8b–§8d cover the per-scanner preservation suites; §8e wraps
`scanValuePrepareIx` (PSV proven; FCPSV / FlowNestingInv staged as
axioms); §8f composes the `scanValueIx` chain on top of §8a/§8e;
§8g case-splits the umbrella `scanNextTokenIx_dispatchBlockIndicators`
into its three `.ok (some _)` arms. -/

/-! ### §8a  `setIfInBounds` PSV / FCPSV preservation primitives -/

/-- Pushing/overwriting via `setIfInBounds` with a non-plain element
    preserves `PlainScalarsValidIx`. The replaced slot becomes the new
    `t`; non-plain ⇒ the PSV match at that index is vacuously `True`.
    Indexed twin of legacy `PlainScalarsValid_setIfInBounds_non_plain`. -/
theorem PlainScalarsValidIx_setIfInBounds_non_plain
    (tokens : Indexed.TokenStream input) (h_old : PlainScalarsValidIx tokens)
    (idx : Nat) (t : IxToken input)
    (h_np : match t.token with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValidIx (tokens.setIfInBounds idx t) := by
  intro i hi
  have hi_arr : i < (tokens.tokens.setIfInBounds idx t).size := hi
  have h_i_lt : i < tokens.tokens.size := by
    rw [Array.size_setIfInBounds] at hi_arr; exact hi_arr
  have h_eq : (tokens.setIfInBounds idx t)[i]'hi
      = (tokens.tokens.setIfInBounds idx t)[i]'hi_arr := rfl
  rw [h_eq, Array.getElem_setIfInBounds h_i_lt]
  by_cases h_eq_idx : idx = i
  · subst h_eq_idx; simp only [↓reduceIte]
    cases t with
    | mk start val stop hOrd hBnd =>
      cases val <;> simp_all
      rename_i content style; cases style <;> simp_all
  · simp only [h_eq_idx, ↓reduceIte]; exact h_old i h_i_lt

/-- `overwriteAtCursor` size invariance. The underlying `setIfInBounds`
    is size-preserving regardless of whether `i` is in bounds. -/
theorem overwriteAtCursor_tokens_size {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).tokens.size = s.tokens.size := by
  show (s.tokens.tokens.setIfInBounds i _).size = s.tokens.tokens.size
  exact Array.size_setIfInBounds ..

/-- `overwriteAtCursor` only rewrites a token slot, leaving `flowLevel` untouched.
    Definitionally `rfl`; provided as a `@[simp]` lemma because since Lean 4.31.0
    `simp`/`simpa` no longer reduce the record projection on its own. -/
@[simp] theorem overwriteAtCursor_flowLevel {input : String} (s : ScannerStateIx input)
    (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).flowLevel = s.flowLevel := rfl

/-- `overwriteAtCursor` with a non-plain token preserves
    `PlainScalarsValidIx`. -/
theorem overwriteAtCursor_non_plain_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input)
    (tok : YamlToken) (h_old : PlainScalarsValidIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValidIx (s.overwriteAtCursor i sk tok).tokens := by
  show PlainScalarsValidIx (s.tokens.setIfInBounds i _)
  exact PlainScalarsValidIx_setIfInBounds_non_plain s.tokens h_old i _ h_np

/-- `setIfInBounds` with a non-plain, non-flow replacement preserves
    `FlowContextPSVIx`, provided the original token at the modified
    position is also non-flow. Indexed twin of legacy
    `FlowContextPSV_setIfInBounds`. -/
theorem FlowContextPSVIx_setIfInBounds_non_flow
    (tokens : Indexed.TokenStream input) (h_old : FlowContextPSVIx tokens)
    (idx : Nat) (val : IxToken input)
    (h_np : match val.token with | .scalar _ .plain => False | _ => True)
    (h_val_nf : val.token ≠ .flowSequenceStart ∧ val.token ≠ .flowMappingStart ∧
                val.token ≠ .flowSequenceEnd ∧ val.token ≠ .flowMappingEnd)
    (h_orig_nf : ∀ (h : idx < tokens.size),
      (tokens[idx]'h).token ≠ .flowSequenceStart ∧
      (tokens[idx]'h).token ≠ .flowMappingStart ∧
      (tokens[idx]'h).token ≠ .flowSequenceEnd ∧
      (tokens[idx]'h).token ≠ .flowMappingEnd) :
    FlowContextPSVIx (tokens.setIfInBounds idx val) := by
  by_cases h_idx : idx < tokens.size
  · intro i hi h_flow
    have hi_arr : i < (tokens.tokens.setIfInBounds idx val).size := hi
    have h_i_lt : i < tokens.size := by
      rw [Array.size_setIfInBounds] at hi_arr; exact hi_arr
    have h_flow_eq :=
      flowNestingIx_setIfInBounds_non_flow tokens idx val h_val_nf h_orig_nf i
    rw [h_flow_eq] at h_flow
    have h_eq : (tokens.setIfInBounds idx val)[i]'hi
        = (tokens.tokens.setIfInBounds idx val)[i]'hi_arr := rfl
    rw [h_eq, Array.getElem_setIfInBounds h_i_lt]
    by_cases h_eq_idx : idx = i
    · subst h_eq_idx; simp only [↓reduceIte]
      exact fpsv_of_not_plain_ix val h_np
    · simp only [h_eq_idx, ↓reduceIte]; exact h_old i h_i_lt h_flow
  · have h_arr_eq : tokens.tokens.setIfInBounds idx val = tokens.tokens := by
      unfold Array.setIfInBounds
      simp [show ¬(idx < tokens.tokens.size) from h_idx]
    have h_eq : tokens.setIfInBounds idx val = tokens := by
      show ({ tokens := tokens.tokens.setIfInBounds idx val } : Indexed.TokenStream input) = tokens
      rw [h_arr_eq]
    rw [h_eq]; exact h_old

/-- `overwriteAtCursor` with a non-plain, non-flow token preserves
    `FlowContextPSVIx`, provided the original token at the modified
    position is non-flow. -/
theorem overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input)
    (tok : YamlToken) (h_old : FlowContextPSVIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True)
    (h_val_nf : tok ≠ .flowSequenceStart ∧ tok ≠ .flowMappingStart ∧
                tok ≠ .flowSequenceEnd ∧ tok ≠ .flowMappingEnd)
    (h_orig_nf : ∀ (h : i < s.tokens.size),
      (s.tokens[i]'h).token ≠ .flowSequenceStart ∧
      (s.tokens[i]'h).token ≠ .flowMappingStart ∧
      (s.tokens[i]'h).token ≠ .flowSequenceEnd ∧
      (s.tokens[i]'h).token ≠ .flowMappingEnd) :
    FlowContextPSVIx (s.overwriteAtCursor i sk tok).tokens := by
  show FlowContextPSVIx (s.tokens.setIfInBounds i _)
  exact FlowContextPSVIx_setIfInBounds_non_flow s.tokens h_old i _ h_np h_val_nf h_orig_nf

/-- `overwriteAtCursor` with a non-flow token preserves `FlowNestingInvIx`,
    provided the original token at the modified position is non-flow. -/
theorem overwriteAtCursor_non_flow_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input)
    (tok : YamlToken) (h_fni : FlowNestingInvIx s)
    (h_val_nf : tok ≠ .flowSequenceStart ∧ tok ≠ .flowMappingStart ∧
                tok ≠ .flowSequenceEnd ∧ tok ≠ .flowMappingEnd)
    (h_orig_nf : ∀ (h : i < s.tokens.size),
      (s.tokens[i]'h).token ≠ .flowSequenceStart ∧
      (s.tokens[i]'h).token ≠ .flowMappingStart ∧
      (s.tokens[i]'h).token ≠ .flowSequenceEnd ∧
      (s.tokens[i]'h).token ≠ .flowMappingEnd) :
    FlowNestingInvIx (s.overwriteAtCursor i sk tok) := by
  unfold FlowNestingInvIx at h_fni ⊢
  have h_fl : (s.overwriteAtCursor i sk tok).flowLevel = s.flowLevel := rfl
  have h_sz : (s.overwriteAtCursor i sk tok).tokens.size = s.tokens.size := by
    show (s.tokens.tokens.setIfInBounds i _).size = s.tokens.tokens.size
    exact Array.size_setIfInBounds ..
  rw [h_fl, h_sz]
  show flowNestingIx (s.tokens.setIfInBounds i _) s.tokens.size = s.flowLevel
  rw [flowNestingIx_setIfInBounds_non_flow s.tokens i _ h_val_nf h_orig_nf s.tokens.size]
  exact h_fni

/-! ### §8b  `scanValueClearKeyIx` preservation

`scanValueClearKeyIx` is a pure state-only update on the `simpleKey`
field — tokens are completely untouched. Every preservation lemma
reduces to `rfl` after `unfold; split`. -/

/-- `scanValueClearKeyIx` leaves the token stream unchanged. -/
@[simp] theorem scanValueClearKeyIx_tokens {input : String}
    (s : ScannerStateIx input) :
    (scanValueClearKeyIx s).tokens = s.tokens := by
  unfold scanValueClearKeyIx
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- `scanValueClearKeyIx` preserves `flowLevel` (no flow-level update). -/
@[simp] theorem scanValueClearKeyIx_flowLevel {input : String}
    (s : ScannerStateIx input) :
    (scanValueClearKeyIx s).flowLevel = s.flowLevel := by
  unfold scanValueClearKeyIx
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem scanValueClearKeyIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanValueClearKeyIx s).tokens := by
  rw [scanValueClearKeyIx_tokens]; exact h_old

theorem scanValueClearKeyIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanValueClearKeyIx s).tokens := by
  rw [scanValueClearKeyIx_tokens]; exact h_old

theorem scanValueClearKeyIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanValueClearKeyIx s) := by
  unfold FlowNestingInvIx at h_fni ⊢
  rw [scanValueClearKeyIx_tokens, scanValueClearKeyIx_flowLevel]; exact h_fni

/-! ### §8c  `scanBlockEntryIx` preservation

`scanBlockEntryIx s = .ok s'` iff either `s.inFlow` (no tab check
fires) or `!s.hasTabInPrecedingWhitespace`. In both cases:
`s'.tokens = ((pushSequenceIndentIx-or-id s).emit .blockEntry).tokens`
(`advance` and the outer `simpleKeyAllowed := true` update do not
touch tokens). Preservation composes §6d (`pushSequenceIndentIx`)
with §5 (`emit_non_plain` / `emit_non_flow`). -/

theorem scanBlockEntryIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanBlockEntryIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanBlockEntryIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h_ok
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h_ok; simp [Bind.bind, Except.bind] at h_ok
    · rw [if_neg ht] at h_ok
      simp only [] at h_ok
      rw [if_pos hi] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show PlainScalarsValidIx
        { ((pushSequenceIndentIx s s.cursor.pos.col).emit .blockEntry).advance
            with simpleKeyAllowed := true }.tokens
      simp only [advance_tokens]
      have h_step1 := pushSequenceIndentIx_preserves_PlainScalarsValidIx
        s s.cursor.pos.col h_old
      exact emit_non_plain_preserves_PlainScalarsValidIx
        (pushSequenceIndentIx s s.cursor.pos.col) .blockEntry h_step1 (by trivial)
  · rw [if_neg hi] at h_ok
    simp only [] at h_ok
    rw [if_neg hi] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show PlainScalarsValidIx { (s.emit .blockEntry).advance with simpleKeyAllowed := true }.tokens
    simp only [advance_tokens]
    exact emit_non_plain_preserves_PlainScalarsValidIx s .blockEntry h_old (by trivial)

theorem scanBlockEntryIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanBlockEntryIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanBlockEntryIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h_ok
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h_ok; simp [Bind.bind, Except.bind] at h_ok
    · rw [if_neg ht] at h_ok
      simp only [] at h_ok
      rw [if_pos hi] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show FlowContextPSVIx
        { ((pushSequenceIndentIx s s.cursor.pos.col).emit .blockEntry).advance
            with simpleKeyAllowed := true }.tokens
      simp only [advance_tokens]
      have h_step1 := pushSequenceIndentIx_preserves_FlowContextPSVIx
        s s.cursor.pos.col h_old
      exact emit_non_flow_non_plain_preserves_FlowContextPSVIx
        (pushSequenceIndentIx s s.cursor.pos.col) .blockEntry h_step1
        (by trivial) (by decide) (by decide) (by decide) (by decide)
  · rw [if_neg hi] at h_ok
    simp only [] at h_ok
    rw [if_neg hi] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show FlowContextPSVIx { (s.emit .blockEntry).advance with simpleKeyAllowed := true }.tokens
    simp only [advance_tokens]
    exact emit_non_flow_non_plain_preserves_FlowContextPSVIx s .blockEntry h_old
      (by trivial) (by decide) (by decide) (by decide) (by decide)

theorem scanBlockEntryIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanBlockEntryIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanBlockEntryIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h_ok
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h_ok; simp [Bind.bind, Except.bind] at h_ok
    · rw [if_neg ht] at h_ok
      simp only [] at h_ok
      rw [if_pos hi] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      have h_step1 := pushSequenceIndentIx_preserves_FlowNestingInvIx
        s s.cursor.pos.col h_fni
      have h_step2 := emit_non_flow_preserves_FlowNestingInvIx
        (pushSequenceIndentIx s s.cursor.pos.col) .blockEntry h_step1
        (by decide) (by decide) (by decide) (by decide)
      unfold FlowNestingInvIx at h_step2 ⊢
      simpa using h_step2
  · rw [if_neg hi] at h_ok
    simp only [] at h_ok
    rw [if_neg hi] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    have h_step1 := emit_non_flow_preserves_FlowNestingInvIx s .blockEntry h_fni
      (by decide) (by decide) (by decide) (by decide)
    unfold FlowNestingInvIx at h_step1 ⊢
    simpa using h_step1

/-! ### §8d  `scanKeyIx` preservation

`scanKeyIx s = .ok s'` iff the inner tab-after-`?` check does not
fire. In both context branches:
`s'.tokens = ((pushMappingIndentIx-or-id s).emit .key).tokens` (the
outer record-update on `simpleKeyAllowed`/`explicitKeyLine`/
`simpleKey` does not touch tokens, and `advance` is token-transparent).
Composes §6e (`pushMappingIndentIx`) with §5 (`emit_non_*`). -/

theorem scanKeyIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanKeyIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanKeyIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h_ok
    split at h_ok
    · simp [Bind.bind, Except.bind] at h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show PlainScalarsValidIx
        { ((pushMappingIndentIx s s.cursor.pos.col).emit .key).advance with .. }.tokens
      simp only [advance_tokens]
      have h_step1 := pushMappingIndentIx_preserves_PlainScalarsValidIx
        s s.cursor.pos.col h_old
      exact emit_non_plain_preserves_PlainScalarsValidIx
        (pushMappingIndentIx s s.cursor.pos.col) .key h_step1 (by trivial)
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show PlainScalarsValidIx { (s.emit .key).advance with .. }.tokens
    simp only [advance_tokens]
    exact emit_non_plain_preserves_PlainScalarsValidIx s .key h_old (by trivial)

theorem scanKeyIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanKeyIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanKeyIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h_ok
    split at h_ok
    · simp [Bind.bind, Except.bind] at h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show FlowContextPSVIx
        { ((pushMappingIndentIx s s.cursor.pos.col).emit .key).advance with .. }.tokens
      simp only [advance_tokens]
      have h_step1 := pushMappingIndentIx_preserves_FlowContextPSVIx
        s s.cursor.pos.col h_old
      exact emit_non_flow_non_plain_preserves_FlowContextPSVIx
        (pushMappingIndentIx s s.cursor.pos.col) .key h_step1
        (by trivial) (by decide) (by decide) (by decide) (by decide)
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show FlowContextPSVIx { (s.emit .key).advance with .. }.tokens
    simp only [advance_tokens]
    exact emit_non_flow_non_plain_preserves_FlowContextPSVIx s .key h_old
      (by trivial) (by decide) (by decide) (by decide) (by decide)

theorem scanKeyIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanKeyIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanKeyIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h_ok
    split at h_ok
    · simp [Bind.bind, Except.bind] at h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      have h_step1 := pushMappingIndentIx_preserves_FlowNestingInvIx
        s s.cursor.pos.col h_fni
      have h_step2 := emit_non_flow_preserves_FlowNestingInvIx
        (pushMappingIndentIx s s.cursor.pos.col) .key h_step1
        (by decide) (by decide) (by decide) (by decide)
      unfold FlowNestingInvIx at h_step2 ⊢
      simpa using h_step2
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    have h_step1 := emit_non_flow_preserves_FlowNestingInvIx s .key h_fni
      (by decide) (by decide) (by decide) (by decide)
    unfold FlowNestingInvIx at h_step1 ⊢
    simpa using h_step1

/-! ### §8e  `scanValuePrepareIx` preservation — all three landed (6d.1e.10)

`scanValuePrepareIx s` either (a) overwrites token slots
`simpleKey.tokenIndex` and `simpleKey.tokenIndex + 1` with non-plain
non-flow tokens (`.blockMappingStart`, `.key`), (b) leaves tokens
unchanged (record-only updates), or (c) delegates to
`pushMappingIndentIx`.

PSV preservation is proven via §8a (`setIfInBounds` non-plain) +
§6e (`pushMappingIndentIx_preserves_PlainScalarsValidIx`).

FCPSV / FlowNestingInv preservation also threads
`SimpleKeyPlaceholderInvIx` (defined just below): the
`overwriteAtCursor` branches need the original tokens at
`simpleKey.tokenIndex` (and `+1`) to be `.placeholder`, which is
non-flow, so `setIfInBounds_non_flow` discharges via §8a's
`overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx`
and `overwriteAtCursor_non_flow_preserves_FlowNestingInvIx`. The
invariant is established by `saveSimpleKeyIx` (§6f, two placeholder
emits at `simpleKey.tokenIndex`/`+1`) and threaded through the
dispatcher chain by the §11i↑ `scanNextTokenIx_preserves_*`
plumbing landed in 6d.1e.10. -/

/-- `SimpleKeyPlaceholderInvIx s` says: whenever `s.simpleKey.possible`
    is set, the token slots at `s.simpleKey.tokenIndex` and
    `s.simpleKey.tokenIndex + 1` exist (are in-bounds) and hold
    `.placeholder` — the markers `saveSimpleKeyIx` reserved. Threaded
    through the dispatcher chain; consumed by `scanValuePrepareIx` to
    discharge the `setIfInBounds_non_flow` original-token obligation.
    Indexed twin of legacy `SimpleKeyPlaceholderInv`. -/
def SimpleKeyPlaceholderInvIx {input : String} (s : ScannerStateIx input) : Prop :=
  s.simpleKey.possible = true →
    s.simpleKey.tokenIndex < s.tokens.size ∧
    s.simpleKey.tokenIndex + 1 < s.tokens.size ∧
    (∀ (h : s.simpleKey.tokenIndex < s.tokens.size),
      (s.tokens[s.simpleKey.tokenIndex]'h).token = YamlToken.placeholder) ∧
    (∀ (h : s.simpleKey.tokenIndex + 1 < s.tokens.size),
      (s.tokens[s.simpleKey.tokenIndex + 1]'h).token = YamlToken.placeholder)

/-- Vacuous when `possible = false`. -/
theorem SimpleKeyPlaceholderInvIx_of_not_possible {input : String}
    (s : ScannerStateIx input) (h : s.simpleKey.possible = false) :
    SimpleKeyPlaceholderInvIx s :=
  fun h_poss => absurd h_poss (by simp [h])

/-- Initial state satisfies the invariant — `mk'` sets
    `simpleKey.possible := false` (its default). -/
theorem mk'_SimpleKeyPlaceholderInvIx (input : String) :
    SimpleKeyPlaceholderInvIx (ScannerStateIx.mk' input) :=
  SimpleKeyPlaceholderInvIx_of_not_possible _ rfl

/-! ### §6e+  AllKeysPlaceholderInvIx — full 4-tuple invariant

Indexed mirror of legacy `AllKeysPlaceholderInv` (lines 4264-4326 in
`Proofs/Production/ScannerPlainScalarValid.lean`). The current-key
`SimpleKeyPlaceholderInvIx` (defined above) is just the first conjunct;
to thread the invariant through flow-start/flow-end scanners (which
push the current key to a stack and later restore it) we additionally
need:

- `SimpleKeyStackPlaceholderInvIx` — every stacked key with `possible
  = true` still has `.placeholder` at its `tokenIndex` and `+1`.
- `SimpleKeyTokenDisjointIx` — the current key's `tokenIndex` pair is
  strictly above every stacked key's pair, so `setIfInBounds` at the
  current key (in `scanValuePrepareIx`) cannot corrupt stacked
  placeholders.
- `SimpleKeyStackOrderingIx` — stacked keys are themselves ordered by
  `tokenIndex`, so popping the top preserves disjointness for the new
  top.

The combined `AllKeysPlaceholderInvIx` is what `scanLoopIx_preserves_*`
threads; `SimpleKeyPlaceholderInvIx` is `.1` of it and remains the
direct dependency of `scanValuePrepareIx_preserves_*`. -/

/-- Every stacked key with `possible = true` is in bounds and its
    `tokenIndex`/`+1` slots hold `.placeholder`. Indexed twin of legacy
    `SimpleKeyStackPlaceholderInv`. -/
def SimpleKeyStackPlaceholderInvIx {input : String} (s : ScannerStateIx input) : Prop :=
  ∀ j (hj : j < s.simpleKeyStack.size),
    (s.simpleKeyStack[j]'hj).possible = true →
    (s.simpleKeyStack[j]'hj).tokenIndex < s.tokens.size ∧
    (s.simpleKeyStack[j]'hj).tokenIndex + 1 < s.tokens.size ∧
    (∀ (h1 : (s.simpleKeyStack[j]'hj).tokenIndex < s.tokens.size),
      (s.tokens[(s.simpleKeyStack[j]'hj).tokenIndex]'h1).token = YamlToken.placeholder) ∧
    (∀ (h2 : (s.simpleKeyStack[j]'hj).tokenIndex + 1 < s.tokens.size),
      (s.tokens[(s.simpleKeyStack[j]'hj).tokenIndex + 1]'h2).token = YamlToken.placeholder)

/-- Stacked key token-index pairs are strictly below the current key
    pair. Indexed twin of legacy `SimpleKeyTokenDisjoint`. -/
def SimpleKeyTokenDisjointIx {input : String} (s : ScannerStateIx input) : Prop :=
  s.simpleKey.possible = true →
    ∀ j (hj : j < s.simpleKeyStack.size),
      (s.simpleKeyStack[j]'hj).possible = true →
      (s.simpleKeyStack[j]'hj).tokenIndex + 1 < s.simpleKey.tokenIndex

/-- Stacked keys are ordered by `tokenIndex`. Indexed twin of legacy
    `SimpleKeyStackOrdering`. -/
def SimpleKeyStackOrderingIx {input : String} (s : ScannerStateIx input) : Prop :=
  ∀ j (hj : j < s.simpleKeyStack.size),
    (s.simpleKeyStack[j]'hj).possible = true →
    ∀ k (hk : k < j),
      (s.simpleKeyStack[k]'(by omega)).possible = true →
      (s.simpleKeyStack[k]'(by omega)).tokenIndex + 1 <
        (s.simpleKeyStack[j]'hj).tokenIndex

/-- Combined invariant for the simple-key placeholder chain. Indexed
    twin of legacy `AllKeysPlaceholderInv`. -/
def AllKeysPlaceholderInvIx {input : String} (s : ScannerStateIx input) : Prop :=
  SimpleKeyPlaceholderInvIx s ∧
  SimpleKeyStackPlaceholderInvIx s ∧
  SimpleKeyTokenDisjointIx s ∧
  SimpleKeyStackOrderingIx s

/-- `SimpleKeyPlaceholderInvIx` mono: preserved when `simpleKey` is
    unchanged, tokens grow, and the existing prefix is preserved. -/
theorem SimpleKeyPlaceholderInvIx_mono {input : String} (s s' : ScannerStateIx input)
    (h_phi : SimpleKeyPlaceholderInvIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.size),
      (s'.tokens[i]'(by omega)) = s.tokens[i]) :
    SimpleKeyPlaceholderInvIx s' := by
  intro h_poss
  rw [h_sk] at h_poss ⊢
  have ⟨hb1, hb2, hp1, hp2⟩ := h_phi h_poss
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro _h1; rw [h_pref _ hb1]; exact hp1 hb1
  · intro _h2; rw [h_pref _ hb2]; exact hp2 hb2

/-- `SimpleKeyStackPlaceholderInvIx` mono: preserved when stack is
    unchanged, tokens grow, prefix preserved. -/
theorem SimpleKeyStackPlaceholderInvIx_mono {input : String}
    (s s' : ScannerStateIx input)
    (h_ssphi : SimpleKeyStackPlaceholderInvIx s)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.size),
      (s'.tokens[i]'(by omega)) = s.tokens[i]) :
    SimpleKeyStackPlaceholderInvIx s' := by
  intro j hj h_poss
  have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj_s) := by
    simp [h_stack]
  rw [h_get] at h_poss ⊢
  have ⟨hb1, hb2, hp1, hp2⟩ := h_ssphi j hj_s h_poss
  refine ⟨by omega, by omega, ?_, ?_⟩
  · intro _h1; rw [h_pref _ hb1]; exact hp1 hb1
  · intro _h2; rw [h_pref _ hb2]; exact hp2 hb2

/-- `SimpleKeyStackPlaceholderInvIx` vacuous when stack is empty. -/
theorem SimpleKeyStackPlaceholderInvIx_of_empty {input : String}
    (s : ScannerStateIx input) (h : s.simpleKeyStack.size = 0) :
    SimpleKeyStackPlaceholderInvIx s := by
  intro j hj
  exfalso; omega

/-- Disjoint is vacuous when current `possible = false`. -/
theorem SimpleKeyTokenDisjointIx_of_not_possible {input : String}
    (s : ScannerStateIx input) (h : s.simpleKey.possible = false) :
    SimpleKeyTokenDisjointIx s :=
  fun h_poss => absurd h_poss (by simp [h])

/-- Disjoint preserved when `simpleKey` and stack are both unchanged. -/
theorem SimpleKeyTokenDisjointIx_mono {input : String}
    (s s' : ScannerStateIx input)
    (h_d : SimpleKeyTokenDisjointIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack) :
    SimpleKeyTokenDisjointIx s' := by
  intro h_poss j hj h_poss_j
  have hj' : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  rw [h_sk] at h_poss ⊢
  have h_get : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj') := by
    simp [h_stack]
  rw [h_get] at h_poss_j ⊢
  exact h_d h_poss j hj' h_poss_j

/-- Stack ordering preserved when stack is unchanged. -/
theorem SimpleKeyStackOrderingIx_mono {input : String}
    (s s' : ScannerStateIx input)
    (h_o : SimpleKeyStackOrderingIx s)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack) :
    SimpleKeyStackOrderingIx s' := by
  intro j hj h_poss_j k hk h_poss_k
  have hj' : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have hk' : k < s.simpleKeyStack.size := by omega
  have hg_j : (s'.simpleKeyStack[j]'hj) = (s.simpleKeyStack[j]'hj') := by
    simp [h_stack]
  have hg_k : (s'.simpleKeyStack[k]'(by omega)) = (s.simpleKeyStack[k]'hk') := by
    simp [h_stack]
  rw [hg_j] at h_poss_j ⊢; rw [hg_k] at h_poss_k ⊢
  exact h_o j hj' h_poss_j k hk h_poss_k

/-- Combined `AllKeysPlaceholderInvIx` mono. -/
theorem AllKeysPlaceholderInvIx_mono {input : String} (s s' : ScannerStateIx input)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.size),
      (s'.tokens[i]'(by omega)) = s.tokens[i]) :
    AllKeysPlaceholderInvIx s' :=
  ⟨SimpleKeyPlaceholderInvIx_mono s s' h_akpi.1 h_sk h_mono h_pref,
   SimpleKeyStackPlaceholderInvIx_mono s s' h_akpi.2.1 h_stack h_mono h_pref,
   SimpleKeyTokenDisjointIx_mono s s' h_akpi.2.2.1 h_sk h_stack,
   SimpleKeyStackOrderingIx_mono s s' h_akpi.2.2.2 h_stack⟩

/-- Cleared current + supplied stack invariants. -/
theorem AllKeysPlaceholderInvIx_of_cleared_current {input : String}
    (s' : ScannerStateIx input)
    (h_poss : s'.simpleKey.possible = false)
    (h_ssphi : SimpleKeyStackPlaceholderInvIx s')
    (h_disjoint : SimpleKeyTokenDisjointIx s')
    (h_ordering : SimpleKeyStackOrderingIx s') :
    AllKeysPlaceholderInvIx s' :=
  ⟨SimpleKeyPlaceholderInvIx_of_not_possible s' h_poss, h_ssphi,
   h_disjoint, h_ordering⟩

/-- Combined: cleared current + stack preserved via mono. -/
theorem AllKeysPlaceholderInvIx_of_cleared_mono {input : String}
    (s s' : ScannerStateIx input)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_clears : s'.simpleKey.possible = false)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.size),
      (s'.tokens[i]'(by omega)) = s.tokens[i]) :
    AllKeysPlaceholderInvIx s' :=
  ⟨SimpleKeyPlaceholderInvIx_of_not_possible s' h_clears,
   SimpleKeyStackPlaceholderInvIx_mono s s' h_akpi.2.1 h_stack h_mono h_pref,
   SimpleKeyTokenDisjointIx_of_not_possible s' h_clears,
   SimpleKeyStackOrderingIx_mono s s' h_akpi.2.2.2 h_stack⟩

/-- Initial state satisfies `AllKeysPlaceholderInvIx`: current key has
    `possible = false`, stack is empty. -/
theorem mk'_AllKeysPlaceholderInvIx (input : String) :
    AllKeysPlaceholderInvIx (ScannerStateIx.mk' input) :=
  ⟨mk'_SimpleKeyPlaceholderInvIx input,
   SimpleKeyStackPlaceholderInvIx_of_empty _ rfl,
   SimpleKeyTokenDisjointIx_of_not_possible _ rfl,
   fun j hj _ _ _ _ => by
     have h_sz : (ScannerStateIx.mk' input).simpleKeyStack.size = 0 := rfl
     omega⟩

/-- `emit tok` preserves `SimpleKeyPlaceholderInvIx`: it grows the
    token stream by one and leaves `simpleKey` unchanged, so the
    placeholders at `simpleKey.tokenIndex`/`+1` remain in place. -/
theorem emit_preserves_SimpleKeyPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken)
    (h_inv : SimpleKeyPlaceholderInvIx s) :
    SimpleKeyPlaceholderInvIx (s.emit tok) := by
  intro h_poss
  have h_poss_s : s.simpleKey.possible = true := h_poss
  have ⟨hb1, hb2, hp1, hp2⟩ := h_inv h_poss_s
  have h_sz : (s.emit tok).tokens.size = s.tokens.size + 1 := emit_tokens_size s tok
  have h_sk_idx : (s.emit tok).simpleKey.tokenIndex = s.simpleKey.tokenIndex := rfl
  refine ⟨?_, ?_, ?_, ?_⟩
  · show s.simpleKey.tokenIndex < (s.emit tok).tokens.size
    rw [h_sz]; omega
  · show s.simpleKey.tokenIndex + 1 < (s.emit tok).tokens.size
    rw [h_sz]; omega
  · intro h_lt
    have h_lt_s : s.simpleKey.tokenIndex < s.tokens.size := hb1
    have h_get : ((s.emit tok).tokens[s.simpleKey.tokenIndex]'h_lt) =
        (s.tokens[s.simpleKey.tokenIndex]'h_lt_s) :=
      emit_preserves_tokens_at s tok s.simpleKey.tokenIndex h_lt_s
    show ((s.emit tok).tokens[s.simpleKey.tokenIndex]'h_lt).token = YamlToken.placeholder
    rw [h_get]; exact hp1 h_lt_s
  · intro h_lt
    have h_lt_s : s.simpleKey.tokenIndex + 1 < s.tokens.size := hb2
    have h_get : ((s.emit tok).tokens[s.simpleKey.tokenIndex + 1]'h_lt) =
        (s.tokens[s.simpleKey.tokenIndex + 1]'h_lt_s) :=
      emit_preserves_tokens_at s tok (s.simpleKey.tokenIndex + 1) h_lt_s
    show ((s.emit tok).tokens[s.simpleKey.tokenIndex + 1]'h_lt).token = YamlToken.placeholder
    rw [h_get]; exact hp2 h_lt_s

theorem scanValuePrepareIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanValuePrepareIx s).tokens := by
  unfold scanValuePrepareIx
  split
  · split
    · split
      · -- col > currentIndent: two overwriteAtCursor calls, then record-update
        show PlainScalarsValidIx
          { ((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor .blockMappingStart).overwriteAtCursor
              (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
        apply overwriteAtCursor_non_plain_preserves_PlainScalarsValidIx _ _ _ _ _ (by trivial)
        apply overwriteAtCursor_non_plain_preserves_PlainScalarsValidIx _ _ _ _ _ (by trivial)
        exact h_old
      · -- one overwrite with .key
        show PlainScalarsValidIx
          { (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
        exact overwriteAtCursor_non_plain_preserves_PlainScalarsValidIx s _ _ _ h_old (by trivial)
    · -- inFlow: one overwrite with .key
      show PlainScalarsValidIx
        { (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
      exact overwriteAtCursor_non_plain_preserves_PlainScalarsValidIx s _ _ _ h_old (by trivial)
  · split
    · -- explicitKeyLine.isSome: record-only update
      exact h_old
    · split
      · -- !inFlow: pushMappingIndentIx
        exact pushMappingIndentIx_preserves_PlainScalarsValidIx s s.cursor.pos.col h_old
      · -- inFlow: no change
        exact h_old

/-- `scanValuePrepareIx` preserves `FlowContextPSVIx` when the simple-key
    placeholder invariant holds. Discharged in 6d.1e.10 via the
    `overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx`
    helper from §8a, with the original-token-non-flow obligation
    discharged by `h_pl` (the placeholders are non-flow). -/
theorem scanValuePrepareIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens)
    (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowContextPSVIx (scanValuePrepareIx s).tokens := by
  unfold scanValuePrepareIx
  split
  · rename_i h_poss
    have ⟨hb1, hb2, hp1, hp2⟩ := h_pl h_poss
    split
    · split
      · -- col > currentIndent: two overwriteAtCursor calls, then record-update
        show FlowContextPSVIx
          { ((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor .blockMappingStart).overwriteAtCursor
              (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
        -- Outer overwriteAtCursor at (tokenIndex + 1) with .key
        apply overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx _ _ _ _ _ (by trivial)
          ⟨by nofun, by nofun, by nofun, by nofun⟩
        · intro h_lt
          -- After the first overwriteAtCursor, the size is unchanged so
          -- (tokenIndex + 1) is still in-bounds in s.tokens.
          have h_sz : (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
              YamlToken.blockMappingStart).tokens.size = s.tokens.size :=
            overwriteAtCursor_tokens_size s _ _ _
          have h_lt' : s.simpleKey.tokenIndex + 1 < s.tokens.size := h_sz ▸ h_lt
          show ((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
              YamlToken.blockMappingStart).tokens[s.simpleKey.tokenIndex + 1]'h_lt).token ≠
                .flowSequenceStart ∧ _ ∧ _ ∧ _
          -- The slot (tokenIndex + 1) is not the modified slot (tokenIndex),
          -- so it still holds the original token from s, which is a placeholder.
          have h_get : (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
              YamlToken.blockMappingStart).tokens[s.simpleKey.tokenIndex + 1]'h_lt =
              s.tokens[s.simpleKey.tokenIndex + 1]'h_lt' :=
            Array.getElem_setIfInBounds_ne (xs := s.tokens.tokens)
              (i := s.simpleKey.tokenIndex)
              (j := s.simpleKey.tokenIndex + 1) h_lt' (by omega)
          rw [h_get, hp2 h_lt']
          exact ⟨by nofun, by nofun, by nofun, by nofun⟩
        · -- Inner overwriteAtCursor at tokenIndex with .blockMappingStart
          apply overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx
            _ _ _ _ h_old (by trivial) ⟨by nofun, by nofun, by nofun, by nofun⟩
          intro h_lt
          rw [hp1 hb1]
          exact ⟨by nofun, by nofun, by nofun, by nofun⟩
      · -- col ≤ currentIndent: one overwriteAtCursor at (tokenIndex + 1) with .key
        show FlowContextPSVIx
          { (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
        apply overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx
          _ _ _ _ h_old (by trivial) ⟨by nofun, by nofun, by nofun, by nofun⟩
        intro h_lt
        rw [hp2 hb2]
        exact ⟨by nofun, by nofun, by nofun, by nofun⟩
    · -- inFlow: one overwriteAtCursor at (tokenIndex + 1) with .key
      show FlowContextPSVIx
        { (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
      apply overwriteAtCursor_non_plain_non_flow_preserves_FlowContextPSVIx
        _ _ _ _ h_old (by trivial) ⟨by nofun, by nofun, by nofun, by nofun⟩
      intro h_lt
      rw [hp2 hb2]
      exact ⟨by nofun, by nofun, by nofun, by nofun⟩
  · split
    · -- explicitKeyLine.isSome: record-only update
      exact h_old
    · split
      · -- !inFlow: pushMappingIndentIx
        exact pushMappingIndentIx_preserves_FlowContextPSVIx s s.cursor.pos.col h_old
      · -- inFlow: no change
        exact h_old

/-- `scanValuePrepareIx` preserves `FlowNestingInvIx` when the simple-key
    placeholder invariant holds. Companion of
    `scanValuePrepareIx_preserves_FlowContextPSVIx`. -/
theorem scanValuePrepareIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s)
    (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowNestingInvIx (scanValuePrepareIx s) := by
  unfold scanValuePrepareIx
  split
  · rename_i h_poss
    have ⟨hb1, hb2, hp1, hp2⟩ := h_pl h_poss
    split
    · split
      · -- col > currentIndent
        unfold FlowNestingInvIx at h_fni ⊢
        show flowNestingIx
          { ((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor .blockMappingStart).overwriteAtCursor
              (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
          _ = s.flowLevel
        have h_step1 := overwriteAtCursor_non_flow_preserves_FlowNestingInvIx
          s s.simpleKey.tokenIndex s.simpleKey.cursor .blockMappingStart h_fni
          ⟨by nofun, by nofun, by nofun, by nofun⟩
          (fun h_lt => by rw [hp1 hb1]; exact ⟨by nofun, by nofun, by nofun, by nofun⟩)
        have h_step2 := overwriteAtCursor_non_flow_preserves_FlowNestingInvIx
          (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor .blockMappingStart)
          (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key h_step1
          ⟨by nofun, by nofun, by nofun, by nofun⟩
          (fun h_lt => by
            have h_sz : (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).tokens.size = s.tokens.size :=
              overwriteAtCursor_tokens_size s _ _ _
            have h_lt' : s.simpleKey.tokenIndex + 1 < s.tokens.size := h_sz ▸ h_lt
            have h_get : (s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).tokens[s.simpleKey.tokenIndex + 1]'h_lt =
                s.tokens[s.simpleKey.tokenIndex + 1]'h_lt' :=
              Array.getElem_setIfInBounds_ne (xs := s.tokens.tokens)
                (i := s.simpleKey.tokenIndex)
                (j := s.simpleKey.tokenIndex + 1) h_lt' (by omega)
            rw [h_get, hp2 h_lt']
            exact ⟨by nofun, by nofun, by nofun, by nofun⟩)
        unfold FlowNestingInvIx at h_step2
        simpa using h_step2
      · -- col ≤ currentIndent: one overwriteAtCursor at (tokenIndex + 1) with .key
        unfold FlowNestingInvIx at h_fni ⊢
        show flowNestingIx
          { (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
          _ = s.flowLevel
        have h_step := overwriteAtCursor_non_flow_preserves_FlowNestingInvIx
          s (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key h_fni
          ⟨by nofun, by nofun, by nofun, by nofun⟩
          (fun h_lt => by rw [hp2 hb2]; exact ⟨by nofun, by nofun, by nofun, by nofun⟩)
        unfold FlowNestingInvIx at h_step
        simpa using h_step
    · -- inFlow: one overwriteAtCursor
      unfold FlowNestingInvIx at h_fni ⊢
      show flowNestingIx
        { (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key) with .. }.tokens
        _ = s.flowLevel
      have h_step := overwriteAtCursor_non_flow_preserves_FlowNestingInvIx
        s (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor .key h_fni
        ⟨by nofun, by nofun, by nofun, by nofun⟩
        (fun h_lt => by rw [hp2 hb2]; exact ⟨by nofun, by nofun, by nofun, by nofun⟩)
      unfold FlowNestingInvIx at h_step
      simpa using h_step
  · split
    · -- explicitKeyLine.isSome: record-only update
      exact h_fni
    · split
      · -- !inFlow: pushMappingIndentIx
        exact pushMappingIndentIx_preserves_FlowNestingInvIx s s.cursor.pos.col h_fni
      · -- inFlow: no change
        exact h_fni

/-! ### §8f  `scanValueIx` preservation

`scanValueIx s = .ok s'` iff `scanValueValidateIx` and
`scanValueTabCheckIx` both succeed. On success:
`s'.tokens = ((scanValuePrepareIx (scanValueClearKeyIx s)).emit .value).advance.tokens`
(modulo the outer `simpleKeyAllowed := true, explicitKeyLine := none`
record update). PSV / FCPSV / FNI all compose §8b (`scanValueClearKeyIx`)
+ §8e (`scanValuePrepareIx`) + §5 (`emit_non_*`). -/

theorem scanValueIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanValueIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · cases h_ok                       -- validate threw
  · split at h_ok
    · cases h_ok                     -- tab-check threw
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show PlainScalarsValidIx
        { ((scanValuePrepareIx (scanValueClearKeyIx s)).emit .value).advance with .. }.tokens
      simp only [advance_tokens]
      have h_ck := scanValueClearKeyIx_preserves_PlainScalarsValidIx s h_old
      have h_prep := scanValuePrepareIx_preserves_PlainScalarsValidIx
        (scanValueClearKeyIx s) h_ck
      exact emit_non_plain_preserves_PlainScalarsValidIx
        (scanValuePrepareIx (scanValueClearKeyIx s)) .value h_prep (by trivial)

/-- `scanValueClearKeyIx` preserves `SimpleKeyPlaceholderInvIx`: it
    either leaves the state unchanged or clears `simpleKey` to its
    default (`possible := false`), so the invariant either holds
    transparently or is vacuously satisfied. -/
theorem scanValueClearKeyIx_preserves_SimpleKeyPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (h_inv : SimpleKeyPlaceholderInvIx s) :
    SimpleKeyPlaceholderInvIx (scanValueClearKeyIx s) := by
  unfold scanValueClearKeyIx
  split
  · split
    · exact SimpleKeyPlaceholderInvIx_of_not_possible _ rfl
    · split
      · exact SimpleKeyPlaceholderInvIx_of_not_possible _ rfl
      · exact h_inv
  · exact h_inv

theorem scanValueIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanValueIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowContextPSVIx s'.tokens := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show FlowContextPSVIx
        { ((scanValuePrepareIx (scanValueClearKeyIx s)).emit .value).advance with .. }.tokens
      simp only [advance_tokens]
      have h_ck := scanValueClearKeyIx_preserves_FlowContextPSVIx s h_old
      have h_pl_ck := scanValueClearKeyIx_preserves_SimpleKeyPlaceholderInvIx s h_pl
      have h_prep := scanValuePrepareIx_preserves_FlowContextPSVIx
        (scanValueClearKeyIx s) h_ck h_pl_ck
      exact emit_non_flow_non_plain_preserves_FlowContextPSVIx
        (scanValuePrepareIx (scanValueClearKeyIx s)) .value h_prep
        (by trivial) (by decide) (by decide) (by decide) (by decide)

theorem scanValueIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanValueIx s = .ok s')
    (h_fni : FlowNestingInvIx s) (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      have h_ck := scanValueClearKeyIx_preserves_FlowNestingInvIx s h_fni
      have h_pl_ck := scanValueClearKeyIx_preserves_SimpleKeyPlaceholderInvIx s h_pl
      have h_prep := scanValuePrepareIx_preserves_FlowNestingInvIx
        (scanValueClearKeyIx s) h_ck h_pl_ck
      have h_emit := emit_non_flow_preserves_FlowNestingInvIx
        (scanValuePrepareIx (scanValueClearKeyIx s)) .value h_prep
        (by decide) (by decide) (by decide) (by decide)
      unfold FlowNestingInvIx at h_emit ⊢
      simpa using h_emit

/-! ### §8g  `scanNextTokenIx_dispatchBlockIndicators` preservation

The umbrella dispatcher returns `.ok (some s')` iff exactly one of
`scanBlockEntryIx`, `scanKeyIx`, `scanValueIx` succeeded. Case-split
on the dispatch arm and apply §8c / §8d / §8f. -/

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s'))
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact scanBlockEntryIx_preserves_PlainScalarsValidIx s _ (by assumption) h_old
  · split at h_ok
    · split at h_ok
      · cases h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanKeyIx_preserves_PlainScalarsValidIx s _ (by assumption) h_old
    · split at h_ok
      · split at h_ok
        · cases h_ok
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          exact scanValueIx_preserves_PlainScalarsValidIx s _ (by assumption) h_old
      · simp at h_ok

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s'))
    (h_old : FlowContextPSVIx s.tokens) (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowContextPSVIx s'.tokens := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact scanBlockEntryIx_preserves_FlowContextPSVIx s _ (by assumption) h_old
  · split at h_ok
    · split at h_ok
      · cases h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanKeyIx_preserves_FlowContextPSVIx s _ (by assumption) h_old
    · split at h_ok
      · split at h_ok
        · cases h_ok
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          exact scanValueIx_preserves_FlowContextPSVIx s _ (by assumption) h_old h_pl
      · simp at h_ok

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s'))
    (h_fni : FlowNestingInvIx s) (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanNextTokenIx_dispatchBlockIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact scanBlockEntryIx_preserves_FlowNestingInvIx s _ (by assumption) h_fni
  · split at h_ok
    · split at h_ok
      · cases h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanKeyIx_preserves_FlowNestingInvIx s _ (by assumption) h_fni
    · split at h_ok
      · split at h_ok
        · cases h_ok
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          exact scanValueIx_preserves_FlowNestingInvIx s _ (by assumption) h_fni h_pl
      · simp at h_ok


/-! ## §9  Top-level theorems — staged as axioms with tightened preconditions

These are the two top-level theorems that the per-action preservation
chain (Step 6d.1e.3+) will eventually establish. For now, they are
declared as **axioms with real `Scanner.Indexed.scanIx input = .ok tokens`
preconditions** (replacing the placeholder `(h_from_scanner : True)`
hypotheses staged in `IndexedWellBehaved.lean` Step 6d.1c).

**Phase 3 axiom budget**: these two top-level axioms plus the
scanner-side axioms staged in §7b/§7c (Step 6d.1e.3) and §8c/§8e
(Step 6d.1e.4). All scanner-side axioms must be discharged before
the §9 top-level axioms can be promoted to theorems; Step 6f cutover
gates on the §9 promotion.

**Consumers**: `parseStream_output_grammable` (legacy:
`Proofs/Parser/ParserGrammable.lean:71-72`; post-cutover: indexed
analogue in the renamed `ParserGrammable.lean`) will obtain
`FlowAwarePSVIx` and `FlowBracketsMatchedIx` for the parser-side
chain by applying these. -/

-- The two top-level theorems (`scan_flow_aware_psv_ix_axiom` and
-- `scan_flow_brackets_matched_ix_axiom`) were previously declared as
-- axioms here. Step 6d.1e.7 discharged them via §11j composition; the
-- proofs are now at the end of this file (§11k) under the same names.

/-! ## §10  Flow-context dispatcher preservation (Step 6d.1e.5)

Preservation suites for the flow-bracket scanners
`scanFlowSequenceStartIx` (`[`), `scanFlowSequenceEndIx` (`]`),
`scanFlowMappingStartIx` (`{`), `scanFlowMappingEndIx` (`}`),
`scanFlowEntryIx` (`,`), and the umbrella dispatcher
`scanNextTokenIx_dispatchFlowIndicators`.

Strategy. Unlike the block-context dispatchers in §8, the flow
scanners emit *flow tokens themselves*. PSV preservation still
follows the standard "emit non-plain" recipe (every flow bracket
is non-plain). FCPSV preservation needs a slight relaxation of
the §5 building block: `emit_non_flow_non_plain_preserves_FlowContextPSVIx`
forbids the new token from being a flow bracket, but the FCPSV
proof body never actually uses that hypothesis — the new-token
discharge goes through `fpsv_of_not_plain_ix`, which only cares
about non-plain. §10a adds the cleaner `emit_non_plain_preserves_FlowContextPSVIx`
variant.

FNI preservation is the genuinely new piece: the scanner's
`flowLevel` shifts by ±1 (open / close), and `flowNestingIx` on
the token-array side shifts in lockstep via `flowNestingIx_push`
(§2). For `.flowSequenceEnd` / `.flowMappingEnd`, the underflow
case (`s.flowLevel = 0`) is handled uniformly by `Nat` monus
(`0 - 1 = 0`) — the dispatcher's runtime check prevents this case
in practice, but the FNI lemma holds unconditionally.

§10a sets up the FCPSV emit building block; §10b–§10e cover the
four bracket scanners (each 3 lemmas: PSV / FCPSV / FNI); §10f
wraps `scanFlowEntryIx` on top of §8e (depends on the two §8e
axioms for FCPSV / FNI but produces a real theorem statement);
§10g case-splits the dispatcher into its five `.ok (some _)` arms. -/

/-! ### §10a  Generic emit-step preservation for flow brackets

`emit_non_flow_non_plain_preserves_FlowContextPSVIx` requires the
emitted token to *not* be a flow bracket — useful for block-context
scanners, useless for flow-bracket scanners. The proof body of that
lemma never consumes the non-flow hypotheses (they sit in
underscored arguments), so the FCPSV preservation is really a
non-plain-only fact. The variant below records that. -/

/-- Emitting a non-plain token preserves `FlowContextPSVIx`.
    Companion to `emit_non_flow_non_plain_preserves_FlowContextPSVIx`
    (§5) — drops the four non-flow hypotheses, which the proof body
    does not consume. Used by the flow-bracket scanner preservation
    suites in §10b–§10e. -/
theorem emit_non_plain_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken)
    (h_old : FlowContextPSVIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True) :
    FlowContextPSVIx (s.emit tok).tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens (s.emit tok).tokens h_old ?_ ?_ ?_
  · change s.tokens.tokens.size ≤ (s.tokens.tokens.push _).size
    rw [Array.size_push]; omega
  · intro i hi
    change (s.tokens.tokens.push _)[i]'(by
        rw [Array.size_push]; exact Nat.lt_succ_of_lt hi) = s.tokens.tokens[i]'hi
    exact Array.getElem_push_lt ..
  · intro j hj hge _h_flow
    have hj_arr : j < (s.tokens.tokens.push (IxToken.mk' s.cursor.pos tok s.cursor.pos
        (Nat.le_refl _) s.cursor.posBound)).size := hj
    have h_size_eq : s.tokens.size = s.tokens.tokens.size := rfl
    have h_eq_idx : j = s.tokens.tokens.size := by
      rw [Array.size_push] at hj_arr
      rw [h_size_eq] at hge
      omega
    subst h_eq_idx
    have h_eq : (s.emit tok).tokens[s.tokens.tokens.size]'hj =
        IxToken.mk' s.cursor.pos tok s.cursor.pos (Nat.le_refl _) s.cursor.posBound := by
      change (s.tokens.tokens.push _)[s.tokens.tokens.size]'hj_arr = _
      exact Array.getElem_push_eq ..
    rw [h_eq]
    exact fpsv_of_not_plain_ix _ h_np

/-! ### §10b  `scanFlowSequenceStartIx` preservation

`scanFlowSequenceStartIx s = { (s.emit .flowSequenceStart).advance with
  flowLevel := _ + 1, flowStack := _, simpleKeyStack := _, simpleKey := _,
  simpleKeyAllowed := true }`. The record-update touches `flowLevel` (the
FNI-relevant field) and several fields invisible to our predicates;
`.tokens` is unchanged by the record update, so `s'.tokens =
(s.emit .flowSequenceStart).tokens` (after `advance_tokens`). -/

theorem scanFlowSequenceStartIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanFlowSequenceStartIx s).tokens := by
  unfold scanFlowSequenceStartIx
  show PlainScalarsValidIx { (s.emit .flowSequenceStart).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_PlainScalarsValidIx s .flowSequenceStart h_old (by trivial)

theorem scanFlowSequenceStartIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanFlowSequenceStartIx s).tokens := by
  unfold scanFlowSequenceStartIx
  show FlowContextPSVIx { (s.emit .flowSequenceStart).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_FlowContextPSVIx s .flowSequenceStart h_old (by trivial)

theorem scanFlowSequenceStartIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanFlowSequenceStartIx s) := by
  unfold FlowNestingInvIx at h_fni ⊢
  unfold scanFlowSequenceStartIx
  show flowNestingIx ((s.emit .flowSequenceStart).advance).tokens
        ((s.emit .flowSequenceStart).advance).tokens.size
      = ((s.emit .flowSequenceStart).advance).flowLevel + 1
  simp only [advance_tokens, advance_flowLevel, emit_flowLevel]
  change flowNestingIx.go (s.tokens.tokens.push _) 0
      (s.tokens.tokens.push _).size 0 = s.flowLevel + 1
  rw [Array.size_push, flowNestingIx_push s.tokens.tokens _]
  change flowNestingIx s.tokens s.tokens.size + 1 = s.flowLevel + 1
  rw [h_fni]

/-! ### §10c  `scanFlowSequenceEndIx` preservation

Symmetric to §10b but for `]`: emits `.flowSequenceEnd`, advances,
and sets `flowLevel := _ - 1`. Note: `scanFlowSequenceEndIx`
itself does *not* check `s.flowLevel > 0` — that's the dispatcher's
job in §10g. The FNI lemma holds unconditionally because Nat
monus saturates at zero (`0 - 1 = 0`) and `flowNestingIx_push`
mirrors that exactly. -/

theorem scanFlowSequenceEndIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanFlowSequenceEndIx s).tokens := by
  unfold scanFlowSequenceEndIx
  show PlainScalarsValidIx { (s.emit .flowSequenceEnd).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_PlainScalarsValidIx s .flowSequenceEnd h_old (by trivial)

theorem scanFlowSequenceEndIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanFlowSequenceEndIx s).tokens := by
  unfold scanFlowSequenceEndIx
  show FlowContextPSVIx { (s.emit .flowSequenceEnd).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_FlowContextPSVIx s .flowSequenceEnd h_old (by trivial)

theorem scanFlowSequenceEndIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanFlowSequenceEndIx s) := by
  unfold FlowNestingInvIx at h_fni ⊢
  unfold scanFlowSequenceEndIx
  show flowNestingIx ((s.emit .flowSequenceEnd).advance).tokens
        ((s.emit .flowSequenceEnd).advance).tokens.size
      = ((s.emit .flowSequenceEnd).advance).flowLevel - 1
  simp only [advance_tokens, advance_flowLevel, emit_flowLevel]
  change flowNestingIx.go (s.tokens.tokens.push _) 0
      (s.tokens.tokens.push _).size 0 = s.flowLevel - 1
  rw [Array.size_push, flowNestingIx_push s.tokens.tokens _]
  change (if flowNestingIx s.tokens s.tokens.size > 0
          then flowNestingIx s.tokens s.tokens.size - 1
          else 0) = s.flowLevel - 1
  rw [h_fni]
  by_cases h : s.flowLevel > 0
  · simp [h]
  · have h_eq : s.flowLevel = 0 := by omega
    simp [h_eq]

/-! ### §10d  `scanFlowMappingStartIx` preservation

Same shape as §10b with `.flowMappingStart` in place of `.flowSequenceStart`.
The `flowNestingIx_push` match treats them identically (both depth + 1). -/

theorem scanFlowMappingStartIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanFlowMappingStartIx s).tokens := by
  unfold scanFlowMappingStartIx
  show PlainScalarsValidIx { (s.emit .flowMappingStart).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_PlainScalarsValidIx s .flowMappingStart h_old (by trivial)

theorem scanFlowMappingStartIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanFlowMappingStartIx s).tokens := by
  unfold scanFlowMappingStartIx
  show FlowContextPSVIx { (s.emit .flowMappingStart).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_FlowContextPSVIx s .flowMappingStart h_old (by trivial)

theorem scanFlowMappingStartIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanFlowMappingStartIx s) := by
  unfold FlowNestingInvIx at h_fni ⊢
  unfold scanFlowMappingStartIx
  show flowNestingIx ((s.emit .flowMappingStart).advance).tokens
        ((s.emit .flowMappingStart).advance).tokens.size
      = ((s.emit .flowMappingStart).advance).flowLevel + 1
  simp only [advance_tokens, advance_flowLevel, emit_flowLevel]
  change flowNestingIx.go (s.tokens.tokens.push _) 0
      (s.tokens.tokens.push _).size 0 = s.flowLevel + 1
  rw [Array.size_push, flowNestingIx_push s.tokens.tokens _]
  change flowNestingIx s.tokens s.tokens.size + 1 = s.flowLevel + 1
  rw [h_fni]

/-! ### §10e  `scanFlowMappingEndIx` preservation

Same shape as §10c with `.flowMappingEnd` in place of `.flowSequenceEnd`. -/

theorem scanFlowMappingEndIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanFlowMappingEndIx s).tokens := by
  unfold scanFlowMappingEndIx
  show PlainScalarsValidIx { (s.emit .flowMappingEnd).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_PlainScalarsValidIx s .flowMappingEnd h_old (by trivial)

theorem scanFlowMappingEndIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanFlowMappingEndIx s).tokens := by
  unfold scanFlowMappingEndIx
  show FlowContextPSVIx { (s.emit .flowMappingEnd).advance with .. }.tokens
  simp only [advance_tokens]
  exact emit_non_plain_preserves_FlowContextPSVIx s .flowMappingEnd h_old (by trivial)

theorem scanFlowMappingEndIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanFlowMappingEndIx s) := by
  unfold FlowNestingInvIx at h_fni ⊢
  unfold scanFlowMappingEndIx
  show flowNestingIx ((s.emit .flowMappingEnd).advance).tokens
        ((s.emit .flowMappingEnd).advance).tokens.size
      = ((s.emit .flowMappingEnd).advance).flowLevel - 1
  simp only [advance_tokens, advance_flowLevel, emit_flowLevel]
  change flowNestingIx.go (s.tokens.tokens.push _) 0
      (s.tokens.tokens.push _).size 0 = s.flowLevel - 1
  rw [Array.size_push, flowNestingIx_push s.tokens.tokens _]
  change (if flowNestingIx s.tokens s.tokens.size > 0
          then flowNestingIx s.tokens s.tokens.size - 1
          else 0) = s.flowLevel - 1
  rw [h_fni]
  by_cases h : s.flowLevel > 0
  · simp [h]
  · have h_eq : s.flowLevel = 0 := by omega
    simp [h_eq]

/-! ### §10f  `scanFlowEntryIx` preservation

After Step 6f.0, `scanFlowEntryIx s` is a `do`-block: it first checks
`lastRealTokenValIx? s.tokens` and throws `invalidFlowEntry` on a
leading or consecutive `,`; otherwise it succeeds with
`s' = { (s.emit .flowEntry).advance with simpleKeyAllowed := true }`.
The earlier accidental `scanValuePrepareIx s` call was removed (the
`,` boundary does not retroactively confirm the pending simple key).

`.flowEntry` is non-plain and non-flow-bracket, so the §5 `emit_non_*`
building blocks apply directly to `s` itself — no `scanValuePrepareIx`
composition needed. -/

theorem scanFlowEntryIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanFlowEntryIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanFlowEntryIx at h_ok
  simp only [bind, Except.bind] at h_ok
  -- The success state when no error is thrown.
  have h_psv_emit : PlainScalarsValidIx (s.emit YamlToken.flowEntry).tokens :=
    emit_non_plain_preserves_PlainScalarsValidIx s .flowEntry h_old (by trivial)
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · injection h_ok with h_ok
      subst h_ok
      show PlainScalarsValidIx
        { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }.tokens
      simp only [advance_tokens]
      exact h_psv_emit
  · injection h_ok with h_ok
    subst h_ok
    show PlainScalarsValidIx
      { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }.tokens
    simp only [advance_tokens]
    exact h_psv_emit

theorem scanFlowEntryIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanFlowEntryIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) (_h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowContextPSVIx s'.tokens := by
  unfold scanFlowEntryIx at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_fcpsv_emit : FlowContextPSVIx (s.emit YamlToken.flowEntry).tokens :=
    emit_non_flow_non_plain_preserves_FlowContextPSVIx
      s .flowEntry h_old (by trivial) (by decide) (by decide) (by decide) (by decide)
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · injection h_ok with h_ok
      subst h_ok
      show FlowContextPSVIx
        { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }.tokens
      simp only [advance_tokens]
      exact h_fcpsv_emit
  · injection h_ok with h_ok
    subst h_ok
    show FlowContextPSVIx
      { (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }.tokens
    simp only [advance_tokens]
    exact h_fcpsv_emit

theorem scanFlowEntryIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanFlowEntryIx s = .ok s')
    (h_fni : FlowNestingInvIx s) (_h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanFlowEntryIx at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_emit : FlowNestingInvIx (s.emit YamlToken.flowEntry) :=
    emit_non_flow_preserves_FlowNestingInvIx s .flowEntry h_fni
      (by decide) (by decide) (by decide) (by decide)
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · injection h_ok with h_ok
      subst h_ok
      unfold FlowNestingInvIx at h_emit ⊢
      simpa using h_emit
  · injection h_ok with h_ok
    subst h_ok
    unfold FlowNestingInvIx at h_emit ⊢
    simpa using h_emit

/-! ### §10g  `scanNextTokenIx_dispatchFlowIndicators` preservation

The umbrella dispatcher case-splits on `c ∈ { '[', ']', '{', '}', ',' }`,
each producing `.ok (some s')` via the corresponding §10b–§10f lemma
(with a `flowLevel == 0` runtime guard on `]` / `}` / `,`). The `none`
fall-through case (none of the five characters) returns `.ok none` and
is therefore inconsistent with the `.ok (some s')` hypothesis. -/

theorem scanNextTokenIx_dispatchFlowIndicators_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '['
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact scanFlowSequenceStartIx_preserves_PlainScalarsValidIx s h_old
  · split at h_ok
    · -- c == ']'
      split at h_ok
      · cases h_ok                       -- flowLevel == 0 error
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowSequenceEndIx_preserves_PlainScalarsValidIx s h_old
    · split at h_ok
      · -- c == '{'
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowMappingStartIx_preserves_PlainScalarsValidIx s h_old
      · split at h_ok
        · -- c == '}'
          split at h_ok
          · cases h_ok
          · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
            exact scanFlowMappingEndIx_preserves_PlainScalarsValidIx s h_old
        · split at h_ok
          · -- c == ','
            split at h_ok
            · cases h_ok
            · split at h_ok
              · cases h_ok               -- scanFlowEntryIx error (cannot happen)
              · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
                exact scanFlowEntryIx_preserves_PlainScalarsValidIx s _
                  (by assumption) h_old
          · cases h_ok                   -- fall-through .ok none

theorem scanNextTokenIx_dispatchFlowIndicators_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (h_old : FlowContextPSVIx s.tokens) (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowContextPSVIx s'.tokens := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact scanFlowSequenceStartIx_preserves_FlowContextPSVIx s h_old
  · split at h_ok
    · split at h_ok
      · cases h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowSequenceEndIx_preserves_FlowContextPSVIx s h_old
    · split at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowMappingStartIx_preserves_FlowContextPSVIx s h_old
      · split at h_ok
        · split at h_ok
          · cases h_ok
          · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
            exact scanFlowMappingEndIx_preserves_FlowContextPSVIx s h_old
        · split at h_ok
          · split at h_ok
            · cases h_ok
            · split at h_ok
              · cases h_ok
              · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
                exact scanFlowEntryIx_preserves_FlowContextPSVIx s _
                  (by assumption) h_old h_pl
          · cases h_ok

theorem scanNextTokenIx_dispatchFlowIndicators_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (h_fni : FlowNestingInvIx s) (h_pl : SimpleKeyPlaceholderInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanNextTokenIx_dispatchFlowIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact scanFlowSequenceStartIx_preserves_FlowNestingInvIx s h_fni
  · split at h_ok
    · split at h_ok
      · cases h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowSequenceEndIx_preserves_FlowNestingInvIx s h_fni
    · split at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowMappingStartIx_preserves_FlowNestingInvIx s h_fni
      · split at h_ok
        · split at h_ok
          · cases h_ok
          · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
            exact scanFlowMappingEndIx_preserves_FlowNestingInvIx s h_fni
        · split at h_ok
          · split at h_ok
            · cases h_ok
            · split at h_ok
              · cases h_ok
              · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
                exact scanFlowEntryIx_preserves_FlowNestingInvIx s _
                  (by assumption) h_fni h_pl
          · cases h_ok


/-! ## §11  Document/directive + top-level dispatch composition (Step 6d.1e.6)

Preservation suites for the document/directive layer plus the
`scanNextTokenIx` top-level dispatcher and the `scanLoopIx`
recursive loop.

**Staging strategy (Reflection 73, new this session)**. The full
preservation chain for the document/directive + content/preprocess
layers — and the `scanNextTokenIx` top-level composition itself — all
hit one of three structural walls:

1. **Reflection 70 (record-update opacity)**: the leaf scanners end
   with multi-field record updates over the post-emit state, blocking
   `rfl`/`simp` reductions through `.tokens` / `.flowLevel` accessors.

2. **`let`-binding wall**: dispatchers chain multiple `let` bindings
   around inner `if`/`match` that `split at h_ok` cannot peel through
   without an interposing `dsimp only []`, and even with `dsimp` the
   pair-destructure of preprocess's `.ok (some (s2, c))` output is
   ambiguous in Lean 4 (Lean greedily destructures `ScannerStateIx`'s
   15 fields when given an anonymous pair-pattern).

3. **Layer F.4 dependency**: `scanNextTokenIx_dispatchContent`'s
   plain-scalar arm needs `ScalarScannable` from
   `Proofs/Scanner/IndexedScalar.lean` (Reflection 72).

All three walls fall to the same 6d.1e.7 discharge effort, so
**every leaf, intermediate dispatcher, and the top-level
`scanNextTokenIx`** in §11a–§11i is staged as **axioms with real
`.ok` preconditions**, leaving **§11j (`scanLoopIx_preserves_*`)** —
the layer that finally produces the three closure invariants from
the `fuel`-recursion — as **real theorems**. The composition shape
is: 27 staged axioms + 3 real-theorem `scanLoopIx_preserves_*`
lemmas on top.

**Axiom budget update**: 6d.1e.6 lands **27 new axioms** on top of
the 16 staged in 6d.1e.3/6d.1e.4/6d.1e.5. **Total: 43 staged axioms**
to discharge in 6d.1e.7. The budget revision is justified because
all 27 of the new axioms fall to the same set of resolution
techniques (record-update opacity peeling, `let`-binding `dsimp`
chain unfolding, Layer F.4 `ScalarScannable` integration) — once
those substrate fixes land in 6d.1e.7, the 27 axioms discharge
in a single sweeping session.

§11a–§11h: 24 staged axioms (4 leaf scanners × 3 invariants +
4 dispatchers × 3 invariants).
§11i: 3 staged axioms (scanNextTokenIx).
§11j: 3 real theorems (scanLoopIx_preserves_*). -/

/-! ### §11a  `scanDocumentStartIx` preservation — proven

Per the Wall #1 probe (Reflection 70 discharge): the outer record
update on `simpleKeyAllowed`, `allowDirectives`, etc. is a pure
record update on non-tokens/non-flowLevel fields, so it's defeq
for both `.tokens` and `.flowLevel`. Combined with
`advanceN`-preserves-tokens-and-flowLevel (defeq) and the
`{ s with simpleKey := ... }`-preserves-tokens-and-flowLevel
(defeq), the function reduces to
`((unwindIndentsIx s (-1)).emit .documentStart)` for both
projections. PSV/FCPSV use the §5 `emit_*_preserves_*` chain;
FNI additionally uses `unwindIndentsIx_preserves_flowLevel` as a
rewrite (not a defeq). -/

theorem scanDocumentStartIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanDocumentStartIx s).tokens := by
  unfold scanDocumentStartIx
  exact emit_non_plain_preserves_PlainScalarsValidIx _ .documentStart
    (unwindIndentsIx_preserves_PlainScalarsValidIx s (-1) h_old) (by trivial)

theorem scanDocumentStartIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanDocumentStartIx s).tokens := by
  unfold scanDocumentStartIx
  exact emit_non_flow_non_plain_preserves_FlowContextPSVIx _ .documentStart
    (unwindIndentsIx_preserves_FlowContextPSVIx s (-1) h_old)
    (by trivial) (by decide) (by decide) (by decide) (by decide)

theorem scanDocumentStartIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanDocumentStartIx s) := by
  unfold scanDocumentStartIx
  exact emit_non_flow_preserves_FlowNestingInvIx _ .documentStart
    (unwindIndentsIx_preserves_FlowNestingInvIx s (-1) h_fni)
    (by decide) (by decide) (by decide) (by decide)

/-! ### §11b  `scanDocumentEndIx` preservation — proven

Mirrors the legacy `scanDocumentEnd_preserves_FlowNestingInv`
pattern: factor out the base preservation `h_base` for the
post-`emit .documentEnd` state, then case-split on the
trailing-content match (`probe.peek?` + `isLineBreakBool`); every
non-throwing arm produces the same `s'` so all reduce to `h_base`. -/

theorem scanDocumentEndIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_de : scanDocumentEndIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanDocumentEndIx at h_de
  simp only [bind, Except.bind] at h_de
  split at h_de
  · simp at h_de
  · have h_base : PlainScalarsValidIx
        ((unwindIndentsIx s (-1)).emit .documentEnd).tokens :=
      emit_non_plain_preserves_PlainScalarsValidIx _ .documentEnd
        (unwindIndentsIx_preserves_PlainScalarsValidIx s (-1) h_old) (by trivial)
    split at h_de
    · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
    · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
    · split at h_de
      · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
      · simp at h_de

theorem scanDocumentEndIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_de : scanDocumentEndIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanDocumentEndIx at h_de
  simp only [bind, Except.bind] at h_de
  split at h_de
  · simp at h_de
  · have h_base : FlowContextPSVIx
        ((unwindIndentsIx s (-1)).emit .documentEnd).tokens :=
      emit_non_flow_non_plain_preserves_FlowContextPSVIx _ .documentEnd
        (unwindIndentsIx_preserves_FlowContextPSVIx s (-1) h_old)
        (by trivial) (by decide) (by decide) (by decide) (by decide)
    split at h_de
    · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
    · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
    · split at h_de
      · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
      · simp at h_de

theorem scanDocumentEndIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_de : scanDocumentEndIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanDocumentEndIx at h_de
  simp only [bind, Except.bind] at h_de
  split at h_de
  · simp at h_de
  · have h_base : FlowNestingInvIx
        ((unwindIndentsIx s (-1)).emit .documentEnd) :=
      emit_non_flow_preserves_FlowNestingInvIx _ .documentEnd
        (unwindIndentsIx_preserves_FlowNestingInvIx s (-1) h_fni)
        (by decide) (by decide) (by decide) (by decide)
    split at h_de
    · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
    · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
    · split at h_de
      · simp only [Except.ok.injEq] at h_de; subst h_de; exact h_base
      · simp at h_de

/-! ### §11c  `scanYamlDirectiveIx` preservation — proven

`scanYamlDirectiveIx` either throws or produces an `.ok` state via
`emitAt startPos (.versionDirective major minor) hBound`, then wraps
with `{ ... with seenYamlDirective := true, directivesPresent := true }`.
For tokens/flowLevel, both the outer record update and the inner
`sAfter = { s with cursor := ... }` are defeq-transparent. The proof
mirrors §11b's structure: case-split on the two `if`s, base
preservation via §7a `emitAt_*_preserves_*` applied at `sAfter`. -/

theorem scanYamlDirectiveIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanYamlDirectiveIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact emitAt_non_plain_preserves_PlainScalarsValidIx _ _ _ _ h_old (by trivial)
    · simp at h_ok

theorem scanYamlDirectiveIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanYamlDirectiveIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact emitAt_non_flow_non_plain_preserves_FlowContextPSVIx _ _ _ _ h_old (by trivial)
    · simp at h_ok

theorem scanYamlDirectiveIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanYamlDirectiveIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
        (by intro h; cases h) (by intro h; cases h)
        (by intro h; cases h) (by intro h; cases h)
    · simp at h_ok

/-! ### §11d  `scanTagDirectiveIx` preservation — proven

Same structure as §11c but without the second `if` (the tag directive
emits unconditionally on the `.ok` path, since `collectTagHandleLoopIx`
and `collectTagSuffixLoopIx` always return — there's no empty-string
fail mode like the YAML major/minor parser). -/

theorem scanTagDirectiveIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanTagDirectiveIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  exact emitAt_non_plain_preserves_PlainScalarsValidIx _ _ _ _ h_old (by trivial)

theorem scanTagDirectiveIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanTagDirectiveIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  exact emitAt_non_flow_non_plain_preserves_FlowContextPSVIx _ _ _ _ h_old (by trivial)

theorem scanTagDirectiveIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanTagDirectiveIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
    (by intro h; cases h) (by intro h; cases h)
    (by intro h; cases h) (by intro h; cases h)

/-! ### §11e  `scanDirectiveIx` preservation — proven

Composition over §11c (YAML branch) / §11d (TAG branch) / identity
(default branch). The `let`-binding chain (Reflection 73 wall) is
peeled cleanly because `split at h_ok` operates on the inner
`if name == "YAML" then ... else if name == "TAG" then ... else
.ok ...` without needing to evaluate the intermediate lets — the
goal/hypothesis stays well-formed through each arm. -/

theorem scanDirectiveIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanDirectiveIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanDirectiveIx at h_ok
  split at h_ok
  · simp at h_ok
  · dsimp only [] at h_ok
    split at h_ok
    · exact scanYamlDirectiveIx_preserves_PlainScalarsValidIx _ _ _ _ _ h_ok h_old
    · split at h_ok
      · exact scanTagDirectiveIx_preserves_PlainScalarsValidIx _ _ _ _ _ h_ok h_old
      · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_old

theorem scanDirectiveIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanDirectiveIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanDirectiveIx at h_ok
  split at h_ok
  · simp at h_ok
  · dsimp only [] at h_ok
    split at h_ok
    · exact scanYamlDirectiveIx_preserves_FlowContextPSVIx _ _ _ _ _ h_ok h_old
    · split at h_ok
      · exact scanTagDirectiveIx_preserves_FlowContextPSVIx _ _ _ _ _ h_ok h_old
      · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_old

theorem scanDirectiveIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanDirectiveIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanDirectiveIx at h_ok
  split at h_ok
  · simp at h_ok
  · dsimp only [] at h_ok
    split at h_ok
    · exact scanYamlDirectiveIx_preserves_FlowNestingInvIx _ _ _ _ _ h_ok h_fni
    · split at h_ok
      · exact scanTagDirectiveIx_preserves_FlowNestingInvIx _ _ _ _ _ h_ok h_fni
      · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_fni

/-! ### §11f  `scanNextTokenIx_dispatchStructural` preservation — proven

Three success arms: `scanDocumentStartIx` (§11a), `scanDocumentEndIx`
(§11b), `scanDirectiveIx` (§11e). Each `if` early-throws or
short-circuits; the legacy
`repeat (any_goals (split at h_ok))` peeling pattern is replaced
here by explicit nested `split at h_ok` since each leaf composes
into a different sub-proof. -/

theorem scanNextTokenIx_dispatchStructural_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanNextTokenIx_dispatchStructural at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  repeat (any_goals (split at h_ok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h_ok)
  any_goals contradiction
  all_goals (try subst h_ok)
  all_goals first
    | exact scanDocumentStartIx_preserves_PlainScalarsValidIx s h_old
    | (rename_i s_de h_de; exact
        scanDocumentEndIx_preserves_PlainScalarsValidIx s s_de h_de h_old)
    | (rename_i s_dir h_dir; exact
        scanDirectiveIx_preserves_PlainScalarsValidIx s s_dir h_dir h_old)

theorem scanNextTokenIx_dispatchStructural_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanNextTokenIx_dispatchStructural at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  repeat (any_goals (split at h_ok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h_ok)
  any_goals contradiction
  all_goals (try subst h_ok)
  all_goals first
    | exact scanDocumentStartIx_preserves_FlowContextPSVIx s h_old
    | (rename_i s_de h_de; exact
        scanDocumentEndIx_preserves_FlowContextPSVIx s s_de h_de h_old)
    | (rename_i s_dir h_dir; exact
        scanDirectiveIx_preserves_FlowContextPSVIx s s_dir h_dir h_old)

theorem scanNextTokenIx_dispatchStructural_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanNextTokenIx_dispatchStructural at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  repeat (any_goals (split at h_ok))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at h_ok)
  any_goals contradiction
  all_goals (try subst h_ok)
  all_goals first
    | exact scanDocumentStartIx_preserves_FlowNestingInvIx s h_fni
    | (rename_i s_de h_de; exact
        scanDocumentEndIx_preserves_FlowNestingInvIx s s_de h_de h_fni)
    | (rename_i s_dir h_dir; exact
        scanDirectiveIx_preserves_FlowNestingInvIx s s_dir h_dir h_fni)

/-! ### §11g  `scanNextTokenIx_preprocess` preservation — staged as axioms

**Reflection 74 wall (new)**: even after `unfold`/`rw`, the `have`-encoded
inner let-bindings (`have savedIndentSize := ...; have s := ...`)
block `split at h_ok` from peeling deeper into the body's nested
`if` chain, and `dsimp only []` reports "no progress" because Lean
does not zeta-reduce `letFun`/`have`-encoded bindings by default in
hypothesis position. Staged for substrate-fix in a follow-up step
(`extract_lets at h_ok` or equivalent). The dispatcher chain (§11i)
takes these as axiomatic inputs. -/

/-- `skipToContentS` preserves `FlowNestingInvIx`: tokens and flowLevel are
    unchanged (the function only updates the cursor). -/
theorem skipToContentS_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s.skipToContentS := by
  unfold FlowNestingInvIx at h_fni ⊢
  rw [skipToContentS_tokens]
  show flowNestingIx s.tokens s.tokens.size = s.skipToContentS.flowLevel
  -- skipToContentS doesn't change flowLevel
  have : s.skipToContentS.flowLevel = s.flowLevel := by
    unfold ScannerStateIx.skipToContentS
    dsimp only
    split <;> rfl
  rw [this]; exact h_fni

theorem scanNextTokenIx_preprocess_preserves_PlainScalarsValidIx
    {input : String} (s s1 : ScannerStateIx input) (c : Char)
    (h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s1.tokens := by
  unfold scanNextTokenIx_preprocess at h_ok
  have h_psv_skip : PlainScalarsValidIx s.skipToContentS.tokens := by
    rw [skipToContentS_tokens]; exact h_old
  simp at h_ok
  repeat (any_goals (split at h_ok))
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq,
                              reduceCtorEq] at h_ok))
  all_goals (try (obtain ⟨hs, _⟩ := h_ok; subst hs))
  all_goals (
    apply saveSimpleKeyIx_preserves_PlainScalarsValidIx
    first
    | exact unwindIndentsIx_preserves_PlainScalarsValidIx _ _ h_psv_skip
    | exact h_psv_skip)

theorem scanNextTokenIx_preprocess_preserves_FlowContextPSVIx
    {input : String} (s s1 : ScannerStateIx input) (c : Char)
    (h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s1.tokens := by
  unfold scanNextTokenIx_preprocess at h_ok
  have h_fpsv_skip : FlowContextPSVIx s.skipToContentS.tokens := by
    rw [skipToContentS_tokens]; exact h_old
  simp at h_ok
  repeat (any_goals (split at h_ok))
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq,
                              reduceCtorEq] at h_ok))
  all_goals (try (obtain ⟨hs, _⟩ := h_ok; subst hs))
  all_goals (
    apply saveSimpleKeyIx_preserves_FlowContextPSVIx
    first
    | exact unwindIndentsIx_preserves_FlowContextPSVIx _ _ h_fpsv_skip
    | exact h_fpsv_skip)

/-- `FlowNestingInvIx` is preserved by the `needIndentCheck := false`
    setter (the record update doesn't change `tokens` or `flowLevel`).
    Added 6f.3b2.pre to bridge the `scanNextTokenIx_preprocess` unwind
    branch, where Step 6f.0's reshape now wraps the unwound state in
    `{ ... with needIndentCheck := false }`. -/
theorem FlowNestingInvIx_setNeedIndentCheck_false {input : String}
    {s : ScannerStateIx input} (h : FlowNestingInvIx s) :
    FlowNestingInvIx { s with needIndentCheck := false } := h

theorem scanNextTokenIx_preprocess_preserves_FlowNestingInvIx
    {input : String} (s s1 : ScannerStateIx input) (c : Char)
    (h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s1 := by
  unfold scanNextTokenIx_preprocess at h_ok
  have h_fni_skip : FlowNestingInvIx s.skipToContentS :=
    skipToContentS_preserves_FlowNestingInvIx s h_fni
  simp at h_ok
  repeat (any_goals (split at h_ok))
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq,
                              reduceCtorEq] at h_ok))
  all_goals (try (obtain ⟨hs, _⟩ := h_ok; subst hs))
  all_goals (
    apply saveSimpleKeyIx_preserves_FlowNestingInvIx
    first
    | exact FlowNestingInvIx_setNeedIndentCheck_false
              (unwindIndentsIx_preserves_FlowNestingInvIx _ _ h_fni_skip)
    | exact h_fni_skip)

/-! ### §11h  `scanNextTokenIx_dispatchContent` preservation — proven
(Step 6d.1e.11d, Reflection 88)

**Discharge strategy**: case-split on the 7 dispatcher arms following
the `scanNextTokenIx_dispatchContent_ok_monotonic` template:

- arms 1-2 (`&`, `*`): `scanAnchorOrAliasIx_preserves_*`
- arm 3 (`!`): `scanTagIx_preserves_*`
- arms 4-6 (`|`/`>`, `"`, `'`): `emitAt_non_plain_preserves_*` /
  `emitAt_non_flow_preserves_*` (the new tokens are
  `.scalar _ .literal|.folded|.doubleQuoted|.singleQuoted` —
  non-plain, non-flow)
- arm 7 (plain): the new token is `.scalar content .plain`. Use
  `scanPlainScalarIx_content_valid` (Layer F.5, discharged in
  6d.1e.11c) to derive `ScalarScannable content s.inFlow`, then:
  - for PSV (`_ false`): apply `ScalarScannable_any_implies_false`;
  - for FCPSV (`_ true` at flow-nesting positions): use
    `FlowNestingInvIx s` + `flowNestingIx_prefix_stable` to convert
    `flowNestingIx new_tokens (s.tokens.size) > 0` to `s.inFlow = true`,
    so `ScalarScannable content s.inFlow` IS `ScalarScannable content true`;
  - for FNI: the new token is non-flow (`.scalar ...`), so
    `emitAt_non_flow_preserves_FlowNestingInvIx` closes.

The plain arm requires:
1. `h_peek : s.cursor.peek? = some c` — threaded through §11i via
   the new `scanNextTokenIx_preprocess_peek_eq` helper;
2. `FlowNestingInvIx s` — added as a hypothesis to the FCPSV trio
   member and threaded through §11i/§11j FCPSV chains.

Both threading changes are scoped to this §11h trio + their direct
consumers in §11i and §11j FCPSV. -/

/-- Helper: `scanNextTokenIx_preprocess` returns `(s1, c)` exactly
    when `s1.cursor.peek? = some c`. The character `c` is the value
    matched by the final `match s.peek? with | some c => .ok (some (s, c))`
    arm, so the output state's cursor peeks at it. Used by the §11h
    dispatcher's plain arm to discharge the `canStart` witness for
    `scanPlainScalarIx_content_valid`. -/
theorem scanNextTokenIx_preprocess_peek_eq
    {input : String} {s s1 : ScannerStateIx input} {c : Char}
    (h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c))) :
    s1.cursor.peek? = some c := by
  unfold scanNextTokenIx_preprocess at h_ok
  simp at h_ok
  repeat (any_goals (split at h_ok))
  all_goals (try (simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq,
                              reduceCtorEq] at h_ok))
  all_goals (
    first
    | (obtain ⟨hs, hc⟩ := h_ok
       subst hs; subst hc
       rename_i hpk
       exact hpk)
    | (-- branches where h_ok contradicts (e.g., `.ok none = .ok (some _)`)
       exact absurd h_ok (by intro; contradiction)))

/-- Helper: the `if s.allowDirectives then ... else s` record update
    preserves `.cursor`. -/
theorem allowDirectives_update_cursor {input : String}
    (s : ScannerStateIx input) :
    (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).cursor = s.cursor := by
  split <;> rfl

/-- Helper: `scanBlockScalarIx` only emits `.literal` or `.folded`. -/
theorem scanBlockScalarIx_style_not_plain {input : String}
    {c : IxCursor input} {parentIndent : Nat}
    {content : String} {style : ScalarStyle} {cAfter : IxCursor input}
    (h : scanBlockScalarIx c parentIndent = some (content, style, cAfter)) :
    style ≠ .plain := by
  unfold scanBlockScalarIx at h
  split at h
  · split at h
    · simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨_, hs, _⟩ := h
      rw [← hs]
      split <;> decide
    · simp at h
  · simp at h

/-- `emitAt` of a `.scalar content .plain` token preserves
    `PlainScalarsValidIx` given a scannability witness for the
    content at `inFlow = false`. -/
theorem emitAt_plain_preserves_PlainScalarsValidIx_of_scannable
    {input : String} (s : ScannerStateIx input) (startPos : YamlPos)
    (content : String) (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_old : PlainScalarsValidIx s.tokens)
    (h_ss : ScalarScannable ⟨content, .plain, none, none, none⟩ false) :
    PlainScalarsValidIx
      (s.emitAt startPos (YamlToken.scalar content .plain) hOrder).tokens := by
  refine PlainScalarsValidIx_of_prefix_and_new s.tokens
    (s.emitAt startPos (YamlToken.scalar content .plain) hOrder).tokens h_old
    (by rw [emitAt_tokens_size]; omega) ?_ ?_
  · intro i hi
    exact emitAt_preserves_tokens_at s startPos
      (YamlToken.scalar content .plain) hOrder i hi
  · intro j hj hge
    have h_jeq : j = s.tokens.size := by
      rw [emitAt_tokens_size] at hj; omega
    subst h_jeq
    rw [emitAt_new_token_token s startPos
      (YamlToken.scalar content .plain) hOrder hj]
    exact h_ss

/-- `emitAt` of a `.scalar content .plain` token preserves
    `FlowContextPSVIx` given:
    1. `FlowNestingInvIx s` to bridge `flowNestingIx new_tokens j > 0`
       to `s.flowLevel > 0`;
    2. a conditional scannability witness for the content at `inFlow = true`. -/
theorem emitAt_plain_preserves_FlowContextPSVIx_of_scannable
    {input : String} (s : ScannerStateIx input) (startPos : YamlPos)
    (content : String) (hOrder : startPos.offset ≤ s.cursor.pos.offset)
    (h_old : FlowContextPSVIx s.tokens)
    (h_fni : FlowNestingInvIx s)
    (h_ss : s.flowLevel > 0 →
      ScalarScannable ⟨content, .plain, none, none, none⟩ true) :
    FlowContextPSVIx
      (s.emitAt startPos (YamlToken.scalar content .plain) hOrder).tokens := by
  refine FlowContextPSVIx_of_prefix_and_new s.tokens
    (s.emitAt startPos (YamlToken.scalar content .plain) hOrder).tokens h_old
    (by rw [emitAt_tokens_size]; omega) ?_ ?_
  · intro i hi
    exact emitAt_preserves_tokens_at s startPos
      (YamlToken.scalar content .plain) hOrder i hi
  · intro j hj hge h_flow_pos
    have h_jeq : j = s.tokens.size := by
      rw [emitAt_tokens_size] at hj; omega
    subst h_jeq
    rw [emitAt_new_token_token s startPos
      (YamlToken.scalar content .plain) hOrder hj]
    -- Use prefix stability to bridge h_flow_pos to s.flowLevel > 0
    have h_prefix_val : ∀ j (hj : j < s.tokens.size),
        ((s.emitAt startPos
              (YamlToken.scalar content .plain) hOrder).tokens[j]'(by
            rw [emitAt_tokens_size]; omega)).token =
        (s.tokens[j]'hj).token := by
      intro k hk
      congr 1
      exact emitAt_preserves_tokens_at s startPos
        (YamlToken.scalar content .plain) hOrder k hk
    have h_fn_eq : flowNestingIx
        (s.emitAt startPos (YamlToken.scalar content .plain) hOrder).tokens
        s.tokens.size =
        flowNestingIx s.tokens s.tokens.size :=
      flowNestingIx_prefix_stable s.tokens _
        (by rw [emitAt_tokens_size]; omega) h_prefix_val s.tokens.size (Nat.le_refl _)
    rw [h_fn_eq] at h_flow_pos
    rw [h_fni] at h_flow_pos
    exact h_ss h_flow_pos

/-- Dispatch-content preservation for `PlainScalarsValidIx`. (Step
    6d.1e.11d) — 7-arm case split on the dispatcher's `if c == X`
    cascade. Arms 1-6 (non-plain emits) discharge via
    `scanAnchorOrAliasIx_*` / `scanTagIx_*` / `emitAt_non_plain_*`.
    The plain arm composes `scanPlainScalarIx_content_valid` with
    `ScalarScannable_any_implies_false` to weaken to `_ false`. -/
theorem scanNextTokenIx_dispatchContent_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (h_peek : s.cursor.peek? = some c)
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h_ok
    try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h_ok; cases h_ok
    | ok v =>
      rw [hA] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact scanAnchorOrAliasIx_preserves_PlainScalarsValidIx s true v hA h_old
  · rw [if_neg hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h_ok
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h_ok; cases h_ok
      | ok v =>
        rw [hA] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact scanAnchorOrAliasIx_preserves_PlainScalarsValidIx s false v hA h_old
    · rw [if_neg hg2] at h_ok
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h_ok
        cases hT : scanTagIx s with
        | error e => rw [hT] at h_ok; cases h_ok
        | ok v =>
          rw [hT] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact scanTagIx_preserves_PlainScalarsValidIx s v hT h_old
      · rw [if_neg hg3] at h_ok
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h_ok
          split at h_ok
          · rename_i r hBS
            simp only [Except.ok.injEq] at h_ok
            subst h_ok
            -- Block scalar — style is .literal or .folded (non-plain)
            have h_style_ne_plain : r.2.1 ≠ .plain := scanBlockScalarIx_style_not_plain hBS
            exact emitAt_non_plain_preserves_PlainScalarsValidIx _ _ _ _ h_old (by
              cases r with
              | mk content rest => cases rest with
                | mk style _ =>
                  simp at h_style_ne_plain
                  show match (YamlToken.scalar content style) with
                    | .scalar _ .plain => False | _ => True
                  cases style <;> first | trivial | exact absurd rfl h_style_ne_plain)
          · cases h_ok
        · rw [if_neg hg4] at h_ok
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h_ok
            split at h_ok
            · rename_i r hDQ
              simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact emitAt_non_plain_preserves_PlainScalarsValidIx _ _ _ _ h_old (by trivial)
            · cases h_ok
          · rw [if_neg hg5] at h_ok
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h_ok
              split at h_ok
              · rename_i r hSQ
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact emitAt_non_plain_preserves_PlainScalarsValidIx _ _ _ _ h_old (by trivial)
              · cases h_ok
            · rw [if_neg hg6] at h_ok
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h_ok
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                -- Plain arm: prove the new token is ScalarScannable _ false.
                have h_ss_false : ScalarScannable
                    ⟨(scanPlainScalarIx s.cursor s.inFlow
                        (if s.inFlow then s.cursor.pos.col
                                      else (max 0 (s.currentIndent + 1)).toNat)).1,
                      .plain, none, none, none⟩ false := by
                  by_cases h_ne :
                      (scanPlainScalarIx s.cursor s.inFlow
                        (if s.inFlow then s.cursor.pos.col
                                      else (max 0 (s.currentIndent + 1)).toNat)).1 = ""
                  · -- Empty content: ScalarScannable holds vacuously
                    rw [h_ne]
                    intro _ h_len
                    simp at h_len
                  · have h_canStart : ∃ ch, s.cursor.peek? = some ch ∧
                        canStartPlainScalarBool ch (s.cursor.peekAt? 1) s.inFlow = true := by
                      refine ⟨c, h_peek, ?_⟩
                      exact hg7
                    have h_ss :=
                      scanPlainScalarIx_content_valid s.cursor s.inFlow _ h_canStart h_ne
                    exact ScalarScannable_any_implies_false _ s.inFlow h_ss
                exact emitAt_plain_preserves_PlainScalarsValidIx_of_scannable _ _ _ _ h_old h_ss_false
              · rw [if_neg hg7] at h_ok
                cases h_ok

set_option maxHeartbeats 4000000 in
/-- Dispatch-content preservation for `FlowContextPSVIx`. (Step
    6d.1e.11d) — requires `FlowNestingInvIx s` to bridge
    `flowNestingIx new_tokens (s.tokens.size) > 0` to `s.flowLevel > 0`
    in the plain arm. -/
theorem scanNextTokenIx_dispatchContent_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (h_peek : s.cursor.peek? = some c)
    (h_fni : FlowNestingInvIx s)
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h_ok
    try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h_ok; cases h_ok
    | ok v =>
      rw [hA] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact scanAnchorOrAliasIx_preserves_FlowContextPSVIx s true v hA h_old
  · rw [if_neg hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h_ok
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h_ok; cases h_ok
      | ok v =>
        rw [hA] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact scanAnchorOrAliasIx_preserves_FlowContextPSVIx s false v hA h_old
    · rw [if_neg hg2] at h_ok
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h_ok
        cases hT : scanTagIx s with
        | error e => rw [hT] at h_ok; cases h_ok
        | ok v =>
          rw [hT] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact scanTagIx_preserves_FlowContextPSVIx s v hT h_old
      · rw [if_neg hg3] at h_ok
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h_ok
          split at h_ok
          · rename_i r hBS
            simp only [Except.ok.injEq] at h_ok
            subst h_ok
            have h_style_ne_plain : r.2.1 ≠ .plain := scanBlockScalarIx_style_not_plain hBS
            exact emitAt_non_flow_non_plain_preserves_FlowContextPSVIx _ _ _ _ h_old (by
              cases r with
              | mk content rest => cases rest with
                | mk style _ =>
                  simp at h_style_ne_plain
                  show match (YamlToken.scalar content style) with
                    | .scalar _ .plain => False | _ => True
                  cases style <;> first | trivial | exact absurd rfl h_style_ne_plain)
          · cases h_ok
        · rw [if_neg hg4] at h_ok
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h_ok
            split at h_ok
            · rename_i r hDQ
              simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact emitAt_non_flow_non_plain_preserves_FlowContextPSVIx _ _ _ _ h_old (by trivial)
            · cases h_ok
          · rw [if_neg hg5] at h_ok
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h_ok
              split at h_ok
              · rename_i r hSQ
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact emitAt_non_flow_non_plain_preserves_FlowContextPSVIx _ _ _ _ h_old (by trivial)
              · cases h_ok
            · rw [if_neg hg6] at h_ok
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h_ok
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                -- Plain arm: conditional ScalarScannable at inFlow = true when flowLevel > 0
                have h_ss_cond : s.flowLevel > 0 →
                    ScalarScannable
                      ⟨(scanPlainScalarIx s.cursor s.inFlow
                          (if s.inFlow then s.cursor.pos.col
                                        else (max 0 (s.currentIndent + 1)).toNat)).1,
                        .plain, none, none, none⟩ true := by
                  intro h_flow_pos
                  by_cases h_ne :
                      (scanPlainScalarIx s.cursor s.inFlow
                        (if s.inFlow then s.cursor.pos.col
                                      else (max 0 (s.currentIndent + 1)).toNat)).1 = ""
                  · rw [h_ne]
                    intro _ h_len
                    simp at h_len
                  · -- s.inFlow = (s.flowLevel > 0) — so h_flow_pos gives s.inFlow = true
                    have h_inFlow : s.inFlow = true := by
                      unfold ScannerStateIx.inFlow
                      exact decide_eq_true h_flow_pos
                    have h_canStart : ∃ ch, s.cursor.peek? = some ch ∧
                        canStartPlainScalarBool ch (s.cursor.peekAt? 1) s.inFlow = true := by
                      refine ⟨c, h_peek, ?_⟩
                      exact hg7
                    have h_ss :=
                      scanPlainScalarIx_content_valid s.cursor s.inFlow _ h_canStart h_ne
                    -- h_ss : ScalarScannable _ s.inFlow; need ScalarScannable _ true
                    exact h_inFlow ▸ h_ss
                exact emitAt_plain_preserves_FlowContextPSVIx_of_scannable
                  _ _ _ _ h_old h_fni h_ss_cond
              · rw [if_neg hg7] at h_ok
                cases h_ok

/-- Dispatch-content preservation for `FlowNestingInvIx`. (Step
    6d.1e.11d) — all 7 dispatcher arms emit non-flow tokens. -/
theorem scanNextTokenIx_dispatchContent_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanNextTokenIx_dispatchContent at h_ok
  by_cases hg1 : (c == '&') = true
  · rw [if_pos hg1] at h_ok
    try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h_ok; cases h_ok
    | ok v =>
      rw [hA] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact scanAnchorOrAliasIx_preserves_FlowNestingInvIx s true v hA h_fni
  · rw [if_neg hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases hg2 : (c == '*') = true
    · rw [if_pos hg2] at h_ok
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h_ok; cases h_ok
      | ok v =>
        rw [hA] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact scanAnchorOrAliasIx_preserves_FlowNestingInvIx s false v hA h_fni
    · rw [if_neg hg2] at h_ok
      by_cases hg3 : (c == '!') = true
      · rw [if_pos hg3] at h_ok
        cases hT : scanTagIx s with
        | error e => rw [hT] at h_ok; cases h_ok
        | ok v =>
          rw [hT] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact scanTagIx_preserves_FlowNestingInvIx s v hT h_fni
      · rw [if_neg hg3] at h_ok
        by_cases hg4 : (c == '|' || c == '>') = true
        · rw [if_pos hg4] at h_ok
          split at h_ok
          · rename_i r hBS
            simp only [Except.ok.injEq] at h_ok
            subst h_ok
            -- s' = { sAfter.emitAt startPos (.scalar content style) hBound with simpleKeyAllowed := false }
            -- where sAfter = { s with cursor := r.2.2 } — cursor-only update preserves FNI.
            exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
              (by intro h; cases h) (by intro h; cases h)
              (by intro h; cases h) (by intro h; cases h)
          · cases h_ok
        · rw [if_neg hg4] at h_ok
          by_cases hg5 : (c == '"') = true
          · rw [if_pos hg5] at h_ok
            split at h_ok
            · rename_i r hDQ
              simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
                (by intro h; cases h) (by intro h; cases h)
                (by intro h; cases h) (by intro h; cases h)
            · cases h_ok
          · rw [if_neg hg5] at h_ok
            by_cases hg6 : (c == '\'') = true
            · rw [if_pos hg6] at h_ok
              split at h_ok
              · rename_i r hSQ
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
                  (by intro h; cases h) (by intro h; cases h)
                  (by intro h; cases h) (by intro h; cases h)
              · cases h_ok
            · rw [if_neg hg6] at h_ok
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · rw [if_pos hg7] at h_ok
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact emitAt_non_flow_preserves_FlowNestingInvIx _ _ _ _ h_fni
                  (by intro h; cases h) (by intro h; cases h)
                  (by intro h; cases h) (by intro h; cases h)
              · rw [if_neg hg7] at h_ok
                cases h_ok

/-! ### §11i  `scanNextTokenIx` preservation — proven (Step 6d.1e.9)

Top-level composition over preprocess + dispatchStructural +
dispatchFlowIndicators + dispatchBlockIndicators + dispatchContent
+ `allowDirectives`/`checkBlockFlowIndent` record updates.

**Discharge strategy** (Step 6d.1e.9, Reflection 77): chain
`generalize h_layer : f_layer s = res at h_ok` + `cases res with
| error => simp at h_ok | ok inner => cases inner with ...` per
dispatcher layer (preprocess → dispatchStructural → checkBlockFlowIndent →
dispatchFlowIndicators → dispatchBlockIndicators → dispatchContent).
`cases pair with | mk s_pp c` cleanly extracts pair components without
hitting Reflection 73's `ScannerStateIx` over-destructure. The
`if s_pp.allowDirectives then ... else s_pp` record update is
abstracted via a separate `generalize h_dir_def : ... = s_dir at h_ok`
because Lean 4 core lacks Mathlib's `set` tactic. The two helper
lemmas `allowDirectives_update_tokens` / `_flowLevel` then close the
preservation obligation for `s_dir`. Each step's error branch is
closed by `simp at h_ok` (iota-reduces the match then closes via
`reduceCtorEq`); each step's success branch carries the named
equation hypothesis into the corresponding §11e–§11h dispatcher
preservation lemma. -/

/-- Helper: the `if s.allowDirectives then ... else s` record update
    preserves `.tokens`. -/
theorem allowDirectives_update_tokens {input : String}
    (s : ScannerStateIx input) :
    (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).tokens = s.tokens := by
  split <;> rfl

/-- Helper: the `if s.allowDirectives then ... else s` record update
    preserves `flowLevel`. -/
theorem allowDirectives_update_flowLevel {input : String}
    (s : ScannerStateIx input) :
    (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).flowLevel = s.flowLevel := by
  split <;> rfl

/-- Helper: the `if s.allowDirectives then ... else s` record update
    preserves `simpleKey`. -/
theorem allowDirectives_update_simpleKey {input : String}
    (s : ScannerStateIx input) :
    (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).simpleKey = s.simpleKey := by
  split <;> rfl

/-- Helper: the `if s.allowDirectives then ... else s` record update
    preserves `SimpleKeyPlaceholderInvIx` (tokens and simpleKey are
    both unchanged). -/
theorem allowDirectives_update_SimpleKeyPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (h_inv : SimpleKeyPlaceholderInvIx s) :
    SimpleKeyPlaceholderInvIx
      (if s.allowDirectives then
          { s with allowDirectives := false, documentEverStarted := true }
        else s) := by
  unfold SimpleKeyPlaceholderInvIx
  rw [allowDirectives_update_simpleKey, allowDirectives_update_tokens]
  exact h_inv

/-! **Note (Step 6d.1e.12d)**: the two `SimpleKeyPlaceholderInvIx`-
    preservation axioms previously declared here (`_preprocess_preserves_*`
    and `scanNextTokenIx_preserves_*`) were discharged by routing
    the consumer chain (§11i `_FlowContextPSVIx`/`_FlowNestingInvIx`,
    §11j `scanLoopIx_preserves_*`, §11k top-level theorems) through
    the §12l `AllKeysPlaceholderInvIx` dispatcher composition. The
    refactored consumers live in §13 (after §12l, which they depend
    on); §11i below retains only `_PlainScalarsValidIx`. -/

theorem scanNextTokenIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    PlainScalarsValidIx s'.tokens := by
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
        have h_psv_pp : PlainScalarsValidIx s_pp.tokens :=
          scanNextTokenIx_preprocess_preserves_PlainScalarsValidIx s s_pp c h_pp h_old
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            exact scanNextTokenIx_dispatchStructural_preserves_PlainScalarsValidIx
              s_pp c s_str h_ds h_psv_pp
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_psv_dir : PlainScalarsValidIx s_dir.tokens := by
              rw [← h_dir_def, allowDirectives_update_tokens]; exact h_psv_pp
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
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_PlainScalarsValidIx
                    s_dir c s_flow h_df h_psv_dir
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
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_PlainScalarsValidIx
                        s_dir c s_blk h_db h_psv_dir
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        have h_peek_pp : s_pp.cursor.peek? = some c :=
                          scanNextTokenIx_preprocess_peek_eq h_pp
                        have h_peek_dir : s_dir.cursor.peek? = some c := by
                          rw [← h_dir_def, allowDirectives_update_cursor]; exact h_peek_pp
                        exact scanNextTokenIx_dispatchContent_preserves_PlainScalarsValidIx
                          s_dir c s_ct h_dc h_peek_dir h_psv_dir

/-! **Note (Step 6d.1e.12d)**: `scanNextTokenIx_preserves_FlowContextPSVIx`
    and `_FlowNestingInvIx` previously lived here as theorems taking
    `h_pl : SimpleKeyPlaceholderInvIx s`. They were refactored in 12d to
    take `h_akpi : AllKeysPlaceholderInvIx s` (the 4-tuple from §6e+,
    composed across the dispatcher chain in §12l) and moved to §13. -/

/-! ### §11j  `scanLoopIx_preserves_*` — real theorems via structural
induction on `fuel`, with a final-emit `.streamEnd` step preservation
lemma chained on top of §11i's `scanNextTokenIx_preserves_*`.

This is the **shape lemma** the Phase 3 closure (§9) needs: applied
at the post-`init` state with the initial-emit invariant established,
`scanLoopIx_preserves_FlowNestingInvIx` discharges
`scan_flow_brackets_matched_ix_axiom`, and the other two discharge
`scan_flow_aware_psv_ix_axiom`'s two conjuncts. -/

theorem finalEmit_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens) :=
  emit_non_plain_preserves_PlainScalarsValidIx _ .streamEnd
    (unwindIndentsIx_preserves_PlainScalarsValidIx s (-1) h_old) (by trivial)

theorem finalEmit_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).tokens) :=
  emit_non_flow_non_plain_preserves_FlowContextPSVIx _ .streamEnd
    (unwindIndentsIx_preserves_FlowContextPSVIx s (-1) h_old) (by trivial)
    (by decide) (by decide) (by decide) (by decide)

theorem finalEmit_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd) :=
  emit_non_flow_preserves_FlowNestingInvIx _ .streamEnd
    (unwindIndentsIx_preserves_FlowNestingInvIx s (-1) h_fni)
    (by decide) (by decide) (by decide) (by decide)

theorem scanLoopIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (fuel : Nat)
    (tokens : Indexed.TokenStream input)
    (h_old : PlainScalarsValidIx s.tokens)
    (h_ok : scanLoopIx s fuel = .ok tokens) :
    PlainScalarsValidIx tokens := by
  induction fuel generalizing s with
  | zero => simp [scanLoopIx] at h_ok
  | succ fuel' ih =>
    simp only [scanLoopIx] at h_ok
    split at h_ok
    · cases h_ok
    · split at h_ok
      · cases h_ok
      · split at h_ok
        · cases h_ok
        · simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact finalEmit_preserves_PlainScalarsValidIx s h_old
    · rename_i s' h_snt
      exact ih s'
        (scanNextTokenIx_preserves_PlainScalarsValidIx s s' h_old h_snt)
        h_ok

/-! **Note (Step 6d.1e.12d)**: `scanLoopIx_preserves_FlowContextPSVIx`
    and `_FlowNestingInvIx` were refactored to take
    `h_akpi : AllKeysPlaceholderInvIx s` (instead of `h_pl`) and moved
    to §13 (they depend on §12l's dispatcher composition). -/

/-! ## §11k  Initial-state invariants + §9 axiom discharge

Initial-state `mk'_*` lemmas live here; the top-level theorems
(`scan_flow_aware_psv_ix_axiom` / `scan_flow_brackets_matched_ix_axiom`)
were moved to §13 in Step 6d.1e.12d (they now establish
`AllKeysPlaceholderInvIx` at the initial state and thread it through
the refactored `scanLoopIx_preserves_*` chain). -/

theorem mk'_PlainScalarsValidIx (input : String) :
    PlainScalarsValidIx (ScannerStateIx.mk' input).tokens :=
  PlainScalarsValidIx_empty

theorem mk'_FlowContextPSVIx (input : String) :
    FlowContextPSVIx (ScannerStateIx.mk' input).tokens := by
  intro i hi
  have : (ScannerStateIx.mk' input).tokens.size = 0 := by
    show (Indexed.TokenStream.empty input).size = 0
    rfl
  omega

theorem mk'_FlowNestingInvIx (input : String) :
    FlowNestingInvIx (ScannerStateIx.mk' input) := by
  unfold FlowNestingInvIx
  show flowNestingIx (Indexed.TokenStream.empty input)
      (Indexed.TokenStream.empty input).size = 0
  unfold flowNestingIx
  show flowNestingIx.go _ 0 0 0 = 0
  unfold flowNestingIx.go
  rfl

/-! **Note (Step 6d.1e.12d)**: `streamStart_SimpleKeyPlaceholderInvIx`
    is subsumed by `streamStart_AllKeysPlaceholderInvIx` in §13, which
    powers the refactored top-level theorems `scan_flow_aware_psv_ix_axiom`
    and `scan_flow_brackets_matched_ix_axiom` (also moved to §13). -/

/-! ## §12  Per-scanner `simpleKey` / `simpleKeyStack` facts (Step 6d.1e.12b)

Indexed mirrors of the legacy `_preserves_simpleKey` /
`_preserves_simpleKeyStack` / `_clears_simpleKey` /
`_simpleKey_cleared` / `_simpleKey_restored` / `_stack_pushed` /
`_stack_popped` chain (legacy lives in `Proofs/Scanner/
ScannerCorrectness.lean` lines 2924–5870). These are pure
state-projection facts: most reduce to `rfl` because the indexed
operations `advance` / `emit` / `emitAt` / `advanceN` /
`overwriteAtCursor` / `skipToContentS` use record-update syntax
that preserves all non-mentioned fields definitionally. The
remaining helpers (`unwindIndentsLoopIx`, `saveSimpleKeyIx`, the
per-scanner facts) compose these primitives. Step 12c (next) uses
the per-scanner facts plus the `_mono` helpers from §6e+ to thread
`AllKeysPlaceholderInvIx` across the dispatcher composition. -/

/-! ### §12a  State-level primitives -/

@[simp] theorem advance_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) : s.advance.simpleKey = s.simpleKey := rfl

@[simp] theorem advance_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) : s.advance.simpleKeyStack = s.simpleKeyStack := rfl

@[simp] theorem advanceN_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (n : Nat) : (s.advanceN n).simpleKey = s.simpleKey := rfl

@[simp] theorem advanceN_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (n : Nat) :
    (s.advanceN n).simpleKeyStack = s.simpleKeyStack := rfl

@[simp] theorem emit_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).simpleKey = s.simpleKey := rfl

@[simp] theorem emit_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).simpleKeyStack = s.simpleKeyStack := rfl

@[simp] theorem emitAt_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).simpleKey = s.simpleKey := rfl

@[simp] theorem emitAt_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (startPos : YamlPos) (tok : YamlToken)
    (h : startPos.offset ≤ s.cursor.pos.offset) :
    (s.emitAt startPos tok h).simpleKeyStack = s.simpleKeyStack := rfl

@[simp] theorem overwriteAtCursor_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).simpleKey = s.simpleKey := rfl

@[simp] theorem overwriteAtCursor_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input) (tok : YamlToken) :
    (s.overwriteAtCursor i sk tok).simpleKeyStack = s.simpleKeyStack := rfl

@[simp] theorem skipToContentS_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) : s.skipToContentS.simpleKey = s.simpleKey := by
  unfold ScannerStateIx.skipToContentS
  dsimp only
  split <;> rfl

@[simp] theorem skipToContentS_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) :
    s.skipToContentS.simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerStateIx.skipToContentS
  dsimp only
  split <;> rfl

/-! ### §12b  Indent-stack helpers

`unwindIndentsLoopIx` recurses on fuel, emitting `blockEnd` and
popping `indents` — neither touches `simpleKey` / `simpleKeyStack`.
`pushSequenceIndentIx` / `pushMappingIndentIx` likewise only emit
and push to `indents`. -/

theorem unwindIndentsLoopIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat) :
    (unwindIndentsLoopIx s col fuel).simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold unwindIndentsLoopIx
    split
    · exact ih _
    · rfl

theorem unwindIndentsLoopIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (col : Int) (fuel : Nat) :
    (unwindIndentsLoopIx s col fuel).simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => rfl
  | succ n ih =>
    unfold unwindIndentsLoopIx
    split
    · exact ih _
    · rfl

theorem unwindIndentsIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (unwindIndentsIx s col).simpleKey = s.simpleKey :=
  unwindIndentsLoopIx_preserves_simpleKey s col _

theorem unwindIndentsIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (unwindIndentsIx s col).simpleKeyStack = s.simpleKeyStack :=
  unwindIndentsLoopIx_preserves_simpleKeyStack s col _

theorem pushSequenceIndentIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushSequenceIndentIx s col).simpleKey = s.simpleKey := by
  unfold pushSequenceIndentIx; split <;> rfl

theorem pushSequenceIndentIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushSequenceIndentIx s col).simpleKeyStack = s.simpleKeyStack := by
  unfold pushSequenceIndentIx; split <;> rfl

theorem pushMappingIndentIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).simpleKey = s.simpleKey := by
  unfold pushMappingIndentIx; split <;> rfl

theorem pushMappingIndentIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (col : Int) :
    (pushMappingIndentIx s col).simpleKeyStack = s.simpleKeyStack := by
  unfold pushMappingIndentIx; split <;> rfl

/-! ### §12c  `saveSimpleKeyIx` helpers

`saveSimpleKeyIx` either no-ops or emits two placeholders and sets
`simpleKey` with `possible := true`. In all branches `simpleKeyStack`
is unchanged. -/

theorem saveSimpleKeyIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack := by
  unfold saveSimpleKeyIx
  split
  · rfl
  · split
    · rfl
    · rfl

/-! ### §12d  Block-context scanner facts

`scanDocumentStartIx`, `scanDocumentEndIx`, `scanDirectiveIx`,
`scanBlockEntryIx`, `scanKeyIx`, `scanValueClearKeyIx`,
`scanValuePrepareIx`, `scanValueIx`, `scanAnchorOrAliasIx`, `scanTagIx`. -/

theorem scanDocumentStartIx_clears_simpleKey {input : String}
    (s : ScannerStateIx input) :
    (scanDocumentStartIx s).simpleKey.possible = false := by
  unfold scanDocumentStartIx; rfl

theorem scanDocumentStartIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) :
    (scanDocumentStartIx s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanDocumentStartIx
  show (unwindIndentsIx s (-1)).simpleKeyStack = s.simpleKeyStack
  exact unwindIndentsIx_preserves_simpleKeyStack s (-1)

theorem scanDocumentEndIx_clears_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanDocumentEndIx s = .ok s') :
    s'.simpleKey.possible = false := by
  unfold scanDocumentEndIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

theorem scanDocumentEndIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanDocumentEndIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanDocumentEndIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    show (unwindIndentsIx s (-1)).simpleKeyStack = s.simpleKeyStack
  all_goals exact unwindIndentsIx_preserves_simpleKeyStack s (-1)

theorem scanYamlDirectiveIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanYamlDirectiveIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

theorem scanYamlDirectiveIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanYamlDirectiveIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

theorem scanTagDirectiveIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanTagDirectiveIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input)
    (startPos : YamlPos) (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanTagDirectiveIx at h
  simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanDirectiveIx_preserves_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanDirectiveIx s = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanDirectiveIx at h
  split at h
  · simp at h
  · dsimp only [] at h
    split at h
    · exact (scanYamlDirectiveIx_preserves_simpleKey _ _ _ _ _ h).trans rfl
    · split at h
      · exact (scanTagDirectiveIx_preserves_simpleKey _ _ _ _ _ h).trans rfl
      · simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanDirectiveIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanDirectiveIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanDirectiveIx at h
  split at h
  · simp at h
  · dsimp only [] at h
    split at h
    · exact (scanYamlDirectiveIx_preserves_simpleKeyStack _ _ _ _ _ h).trans rfl
    · split at h
      · exact (scanTagDirectiveIx_preserves_simpleKeyStack _ _ _ _ _ h).trans rfl
      · simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanBlockEntryIx_preserves_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanBlockEntryIx s = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanBlockEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushSequenceIndentIx_preserves_simpleKey s s.cursor.pos.col
    | rfl

theorem scanBlockEntryIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanBlockEntryIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanBlockEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushSequenceIndentIx_preserves_simpleKeyStack s s.cursor.pos.col
    | rfl

theorem scanKeyIx_clears_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanKeyIx s = .ok s') :
    s'.simpleKey.possible = false := by
  unfold scanKeyIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

theorem scanKeyIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanKeyIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanKeyIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals
    first
    | exact pushMappingIndentIx_preserves_simpleKeyStack s s.cursor.pos.col
    | rfl

theorem scanValueClearKeyIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) :
    (scanValueClearKeyIx s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanValueClearKeyIx
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem scanValuePrepareIx_clears_simpleKey {input : String}
    (s : ScannerStateIx input) :
    (scanValuePrepareIx s).simpleKey.possible = false := by
  unfold scanValuePrepareIx
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · rw [pushMappingIndentIx_preserves_simpleKey]
        rename_i h_not_possible _ _; simp at h_not_possible; exact h_not_possible
      · rename_i h_not_possible _ _; simp at h_not_possible; exact h_not_possible

theorem scanValuePrepareIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) :
    (scanValuePrepareIx s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanValuePrepareIx
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndentIx_preserves_simpleKeyStack s s.cursor.pos.col
      · rfl

theorem scanValueIx_clears_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanValueIx s = .ok s') :
    s'.simpleKey.possible = false := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit
        YamlToken.value).advance.simpleKey.possible = false
  rw [advance_preserves_simpleKey, emit_preserves_simpleKey]
  exact scanValuePrepareIx_clears_simpleKey _

theorem scanValueIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanValueIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanValueIx at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit
        YamlToken.value).advance.simpleKeyStack = s.simpleKeyStack
  rw [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
      scanValuePrepareIx_preserves_simpleKeyStack,
      scanValueClearKeyIx_preserves_simpleKeyStack]

theorem scanAnchorOrAliasIx_preserves_simpleKey {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanAnchorOrAliasIx at h
  dsimp only [] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanAnchorOrAliasIx_preserves_simpleKeyStack {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanAnchorOrAliasIx at h
  dsimp only [] at h
  split at h
  · simp at h
  · simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanTagIx_preserves_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanTagIx s = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanTagIx at h
  dsimp only [] at h
  split at h
  · -- '<' verbatim tag branch
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
  · -- '!' secondary tag branch
    simp only [Except.ok.injEq] at h; subst h; rfl
  · -- default branch (named tag / primary handle)
    simp only [Except.ok.injEq] at h; subst h; rfl

theorem scanTagIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanTagIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanTagIx at h
  dsimp only [] at h
  split at h
  · -- '<' verbatim tag branch
    split at h
    · simp at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq] at h; subst h; rfl
  · -- '!' secondary tag branch
    simp only [Except.ok.injEq] at h; subst h; rfl
  · -- default branch
    simp only [Except.ok.injEq] at h; subst h; rfl

/-! ### §12e  Flow-context start/end facts

`scanFlowSequenceStartIx` / `scanFlowMappingStartIx` clear the
current `simpleKey` and push the old one onto `simpleKeyStack`.
`scanFlowSequenceEndIx` / `scanFlowMappingEndIx` restore the top
of the stack into `simpleKey` and pop. `scanFlowEntryIx` calls
`scanValuePrepareIx` (clears) + `emit` + `advance`. -/

theorem scanFlowSequenceStartIx_simpleKey_cleared {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).simpleKey.possible = false := by
  unfold scanFlowSequenceStartIx; rfl

theorem scanFlowSequenceStartIx_stack_pushed {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
  unfold scanFlowSequenceStartIx; rfl

theorem scanFlowMappingStartIx_simpleKey_cleared {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).simpleKey.possible = false := by
  unfold scanFlowMappingStartIx; rfl

theorem scanFlowMappingStartIx_stack_pushed {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
  unfold scanFlowMappingStartIx; rfl

theorem scanFlowSequenceEndIx_simpleKey_restored {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).simpleKey =
      s.simpleKeyStack.back?.getD { cursor := IxCursor.start input } := by
  unfold scanFlowSequenceEndIx; rfl

theorem scanFlowSequenceEndIx_stack_popped {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).simpleKeyStack = s.simpleKeyStack.pop := by
  unfold scanFlowSequenceEndIx; rfl

theorem scanFlowMappingEndIx_simpleKey_restored {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).simpleKey =
      s.simpleKeyStack.back?.getD { cursor := IxCursor.start input } := by
  unfold scanFlowMappingEndIx; rfl

theorem scanFlowMappingEndIx_stack_popped {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).simpleKeyStack = s.simpleKeyStack.pop := by
  unfold scanFlowMappingEndIx; rfl

/-- After Step 6f.0, `scanFlowEntryIx` preserves (does NOT clear)
    `simpleKey`: the `,` boundary doesn't retroactively confirm the
    pending simple key. Indexed twin of legacy
    `scanFlowEntry_preserves_simpleKey`. -/
theorem scanFlowEntryIx_preserves_simpleKey {input : String}
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKey, emit_preserves_simpleKey]

theorem scanFlowEntryIx_preserves_simpleKeyStack {input : String}
    (s s' : ScannerStateIx input) (h : scanFlowEntryIx s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanFlowEntryIx at h
  simp only [bind, Except.bind] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]

/-! ## §12f  Per-scanner `_tokens_eq` rfl-bridges (Step 6d.1e.12c-scout)

Indexed twins of legacy `scan*_preserves_prefix` infrastructure.
The full per-scanner `_preserves_prefix` Ix family encounters a
recurring **motive-not-type-correct** wall when Lean's
record-update notation (`{ unwindIndentsIx s c with simpleKey :=
… }`) elaborates as `let __src := …; { __src with … }` and the
`(stateExpr).tokens[i]'_` access carries the dependent bound
proof through the rewrite motive — `rw [scanX_tokens_eq]` and
`rw [emit_preserves_tokens_at …]` both fail with motive errors,
and `change` over the same patterns fails to unify across the
`__src` let-zeta.

The `_tokens_eq` rfl-bridges below establish that each scanner's
`.tokens` field equals a clean `(... .emit tok).tokens` form
modulo record-update opacity — these compile (verified) and are
the right primitives for §12c-dispatchers. The full
`_preserves_prefix` lemmas that turn these into indexed accesses
are deferred to a substrate-fix follow-up step (12c.1: prefix
infrastructure; 12c.2: dispatcher composition; 12c.3: discharge
the 2 staging axioms).

See Reflection 91 in the Blueprint for the substrate-fix detail. -/

theorem scanFlowSequenceStartIx_tokens_eq {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).tokens =
      (s.emit YamlToken.flowSequenceStart).tokens := rfl

theorem scanFlowSequenceEndIx_tokens_eq {input : String}
    (s : ScannerStateIx input) :
    (scanFlowSequenceEndIx s).tokens =
      (s.emit YamlToken.flowSequenceEnd).tokens := rfl

theorem scanFlowMappingStartIx_tokens_eq {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).tokens =
      (s.emit YamlToken.flowMappingStart).tokens := rfl

theorem scanFlowMappingEndIx_tokens_eq {input : String}
    (s : ScannerStateIx input) :
    (scanFlowMappingEndIx s).tokens =
      (s.emit YamlToken.flowMappingEnd).tokens := rfl

theorem scanDocumentStartIx_tokens_eq {input : String}
    (s : ScannerStateIx input) :
    (scanDocumentStartIx s).tokens =
      ((unwindIndentsIx s (-1)).emit YamlToken.documentStart).tokens := rfl

/-! ## §12g  Per-scanner `_preserves_prefix` — flow indicators
    (Step 6d.1e.12c.1)

The substrate fix for the `_preserves_prefix` family. Each lemma
mirrors the legacy `unwindIndentsLoopIx_preserves_prefix` /
`pushSequenceIndentIx_preserves_prefix` shape with both bound
proofs explicit, deriving the LHS bound from the matching
`_tokens_size_le` lemma (from `Proofs/Scanner/IndexedDispatch.lean`)
and closing the conclusion via `show` reshaping + the §5/§6 primitives
(`emit_preserves_tokens_at`, `emitAt_preserves_tokens_at`).

This deliberately avoids the `_tokens_eq` rfl-bridges from §12f and
the `rw [scanX_tokens_eq]` rewrite pattern that triggered the
motive-not-type-correct wall (Reflection 91). The `show` tactic
reshapes through definitional equality only — record-update
opacity and `let __src` zeta-reduction succeed silently. -/

theorem scanFlowSequenceStartIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (scanFlowSequenceStartIx s).tokens[i]'(by
        have := scanFlowSequenceStartIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  show (s.emit YamlToken.flowSequenceStart).tokens[i]'_ = s.tokens[i]'h_bound
  exact emit_preserves_tokens_at s YamlToken.flowSequenceStart i h_bound

theorem scanFlowSequenceEndIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (scanFlowSequenceEndIx s).tokens[i]'(by
        have := scanFlowSequenceEndIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  show (s.emit YamlToken.flowSequenceEnd).tokens[i]'_ = s.tokens[i]'h_bound
  exact emit_preserves_tokens_at s YamlToken.flowSequenceEnd i h_bound

theorem scanFlowMappingStartIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (scanFlowMappingStartIx s).tokens[i]'(by
        have := scanFlowMappingStartIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  show (s.emit YamlToken.flowMappingStart).tokens[i]'_ = s.tokens[i]'h_bound
  exact emit_preserves_tokens_at s YamlToken.flowMappingStart i h_bound

theorem scanFlowMappingEndIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (scanFlowMappingEndIx s).tokens[i]'(by
        have := scanFlowMappingEndIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  show (s.emit YamlToken.flowMappingEnd).tokens[i]'_ = s.tokens[i]'h_bound
  exact emit_preserves_tokens_at s YamlToken.flowMappingEnd i h_bound

/-! ## §12h  Per-scanner `_preserves_prefix` — block content scanners
    (Step 6d.1e.12c.1)

`scanBlockEntryIx` and `scanKeyIx` emit `.blockEntry` / `.key`
tokens, optionally after `pushSequenceIndentIx` / `pushMappingIndentIx`
in block context. Both `pushXIndentIx` already have
`_preserves_prefix` lemmas (§6d/§6e). -/

theorem scanBlockEntryIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanBlockEntryIx s = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by
      have := scanBlockEntryIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanBlockEntryIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · rw [if_pos hi] at h_ok
    by_cases ht : s.hasTabInPrecedingWhitespace = true
    · rw [if_pos ht] at h_ok
      simp [Bind.bind, Except.bind] at h_ok
    · rw [if_neg ht] at h_ok
      simp only [] at h_ok
      rw [if_pos hi] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show ((pushSequenceIndentIx s s.cursor.pos.col).emit YamlToken.blockEntry).tokens[i]'_ =
        s.tokens[i]'h_bound
      have h_push_sz := pushSequenceIndentIx_tokens_size_le s s.cursor.pos.col
      have h_i_lt : i < (pushSequenceIndentIx s s.cursor.pos.col).tokens.size := by omega
      exact (emit_preserves_tokens_at (pushSequenceIndentIx s s.cursor.pos.col)
              YamlToken.blockEntry i h_i_lt).trans
            (pushSequenceIndentIx_preserves_prefix s s.cursor.pos.col i h_bound)
  · rw [if_neg hi] at h_ok
    simp only [] at h_ok
    rw [if_neg hi] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show (s.emit YamlToken.blockEntry).tokens[i]'_ = s.tokens[i]'h_bound
    exact emit_preserves_tokens_at s YamlToken.blockEntry i h_bound

theorem scanKeyIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanKeyIx s = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by
      have := scanKeyIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanKeyIx at h_ok
  by_cases hi : (!s.inFlow) = true
  · simp only [if_pos hi, advance_inFlow, emit_inFlow,
      pushMappingIndentIx_inFlow] at h_ok
    split at h_ok
    · simp [Bind.bind, Except.bind] at h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      show ((pushMappingIndentIx s s.cursor.pos.col).emit YamlToken.key).tokens[i]'_ =
        s.tokens[i]'h_bound
      have h_push_sz := pushMappingIndentIx_tokens_size_le s s.cursor.pos.col
      have h_i_lt : i < (pushMappingIndentIx s s.cursor.pos.col).tokens.size := by omega
      exact (emit_preserves_tokens_at (pushMappingIndentIx s s.cursor.pos.col)
              YamlToken.key i h_i_lt).trans
            (pushMappingIndentIx_preserves_prefix s s.cursor.pos.col i h_bound)
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    show (s.emit YamlToken.key).tokens[i]'_ = s.tokens[i]'h_bound
    exact emit_preserves_tokens_at s YamlToken.key i h_bound

/-! ## §12i  Per-scanner `_preserves_prefix` — directive scanners
    (Step 6d.1e.12c.1)

`scanYamlDirectiveIx`, `scanTagDirectiveIx` emit at `startPos` via
`emitAt`, then update non-tokens fields. `scanDirectiveIx` delegates
to one of the above (or emits nothing in the reserved-directive
default arm). -/

theorem scanYamlDirectiveIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanYamlDirectiveIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanYamlDirectiveIx at h_ok
  by_cases hd : s.seenYamlDirective = true
  · rw [if_pos hd] at h_ok
    simp [Bind.bind, Except.bind] at h_ok
  · rw [if_neg hd] at h_ok
    simp only [] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      apply emitAt_preserves_tokens_at
    · simp at h_ok

theorem scanTagDirectiveIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset)
    (s' : ScannerStateIx input)
    (h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanTagDirectiveIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanTagDirectiveIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  apply emitAt_preserves_tokens_at

theorem scanDirectiveIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanDirectiveIx s = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanDirectiveIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanDirectiveIx at h_ok
  split at h_ok
  · simp at h_ok
  · simp only at h_ok
    split at h_ok
    · -- YAML branch: delegate to scanYamlDirectiveIx
      exact scanYamlDirectiveIx_preserves_prefix _ _ _ _ _ h_ok i h_bound
    · split at h_ok
      · -- TAG branch: delegate to scanTagDirectiveIx
        exact scanTagDirectiveIx_preserves_prefix _ _ _ _ _ h_ok i h_bound
      · -- reserved-directive default: `.ok { sAdv with cursor := cAfterWS }` — tokens unchanged
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        rfl

/-! ## §12j  Per-scanner `_preserves_prefix` — document markers
    (Step 6d.1e.12c.1)

`scanDocumentStartIx` and `scanDocumentEndIx` unwind indents, then
emit `.documentStart` / `.documentEnd`. Both compose through
`unwindIndentsIx_preserves_prefix` (§6c) + `emit_preserves_tokens_at`
(§5). -/

theorem scanDocumentStartIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (scanDocumentStartIx s).tokens[i]'(by
        have := scanDocumentStartIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  show ((unwindIndentsIx s (-1)).emit YamlToken.documentStart).tokens[i]'_ =
    s.tokens[i]'h_bound
  have h_unwind_sz := unwindIndentsIx_tokens_size_le s (-1)
  have h_i_lt : i < (unwindIndentsIx s (-1)).tokens.size := by omega
  exact (emit_preserves_tokens_at (unwindIndentsIx s (-1)) YamlToken.documentStart i h_i_lt).trans
        (unwindIndentsIx_preserves_prefix s (-1) i h_bound)

theorem scanDocumentEndIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanDocumentEndIx s = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanDocumentEndIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanDocumentEndIx at h_ok
  by_cases hd : (s.directivesPresent && !s.documentEverStarted) = true
  · rw [if_pos hd] at h_ok
    simp [Bind.bind, Except.bind] at h_ok
  · rw [if_neg hd] at h_ok
    try simp only [] at h_ok
    -- The post-emit state's `.tokens` is `((unwindIndentsIx s (-1)).emit .documentEnd).tokens`
    -- regardless of the probe-match arm (probe only affects the unit early-return chain;
    -- the eventual `.ok s` carries the post-emit state).
    have h_unwind_sz := unwindIndentsIx_tokens_size_le s (-1)
    have h_i_lt : i < (unwindIndentsIx s (-1)).tokens.size := by omega
    have h_step :
        ((unwindIndentsIx s (-1)).emit YamlToken.documentEnd).tokens[i]'(by
            have := emit_tokens_size (unwindIndentsIx s (-1)) YamlToken.documentEnd
            omega) = s.tokens[i]'h_bound :=
      (emit_preserves_tokens_at (unwindIndentsIx s (-1)) YamlToken.documentEnd i h_i_lt).trans
      (unwindIndentsIx_preserves_prefix s (-1) i h_bound)
    split at h_ok
    all_goals first
      | (simp only [Except.ok.injEq] at h_ok
         subst h_ok
         exact h_step)
      | (split at h_ok
         all_goals first
           | (simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact h_step)
           | (simp [Bind.bind, Except.bind] at h_ok))

/-! ## §12k  Per-scanner `_preserves_prefix` — bounded scanners
    (Step 6d.1e.12c.1)

`scanValueClearKeyIx` leaves tokens unchanged (no setIfInBounds).
`scanValuePrepareIx` / `scanValueIx` / `scanFlowEntryIx` overwrite
positions at `simpleKey.tokenIndex` and `simpleKey.tokenIndex + 1`
when `simpleKey.possible` is true — so they preserve a prefix of
length `n` only when `n ≤ simpleKey.tokenIndex` (the `h_inv`
hypothesis). This bounded signature mirrors the legacy
`scanValuePrepare_preserves_prefix`. -/

theorem scanValueClearKeyIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (i : Nat) (h_bound : i < s.tokens.size) :
    (scanValueClearKeyIx s).tokens[i]'(by
        have := scanValueClearKeyIx_tokens_size_le s; omega) =
    s.tokens[i]'h_bound := by
  simp only [scanValueClearKeyIx_tokens]

theorem scanValuePrepareIx_preserves_prefix {input : String}
    (s : ScannerStateIx input)
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : s.simpleKey.possible = true → n ≤ s.simpleKey.tokenIndex)
    (i : Nat) (h_bound : i < n) :
    (scanValuePrepareIx s).tokens[i]'(by
        have := scanValuePrepareIx_tokens_size_le s; omega) =
    s.tokens[i]'(by omega) := by
  have h_sz : s.tokens.size = s.tokens.tokens.size := rfl
  unfold scanValuePrepareIx
  split
  · rename_i h_poss
    have h_idx := h_inv h_poss
    split
    · split
      · -- col > currentIndent: two overwriteAtCursor at idx, idx+1
        have h_i_lt : i < s.tokens.tokens.size := by omega
        have h_i_lt1 : i < (s.tokens.tokens.setIfInBounds s.simpleKey.tokenIndex
            (IxToken.mk' s.simpleKey.cursor.pos YamlToken.blockMappingStart
              s.simpleKey.cursor.pos (Nat.le_refl _) s.simpleKey.cursor.posBound)).size := by
          rw [Array.size_setIfInBounds]; exact h_i_lt
        change (((s.overwriteAtCursor s.simpleKey.tokenIndex s.simpleKey.cursor
                YamlToken.blockMappingStart).overwriteAtCursor
              (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor YamlToken.key).tokens)[i]'_ =
          s.tokens[i]'(by omega)
        change (((s.tokens.tokens.setIfInBounds s.simpleKey.tokenIndex _).setIfInBounds
              (s.simpleKey.tokenIndex + 1) _))[i]'_ = s.tokens.tokens[i]'h_i_lt
        exact (Array.getElem_setIfInBounds_ne h_i_lt1
                (show s.simpleKey.tokenIndex + 1 ≠ i from by omega)).trans
              (Array.getElem_setIfInBounds_ne h_i_lt
                (show s.simpleKey.tokenIndex ≠ i from by omega))
      · -- col ≤ currentIndent: one overwriteAtCursor at idx+1
        have h_i_lt : i < s.tokens.tokens.size := by omega
        change (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
                YamlToken.key).tokens[i]'_ = s.tokens[i]'(by omega)
        change (s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1) _)[i]'_ =
          s.tokens.tokens[i]'h_i_lt
        exact Array.getElem_setIfInBounds_ne h_i_lt
              (show s.simpleKey.tokenIndex + 1 ≠ i from by omega)
    · -- inFlow: one overwriteAtCursor at idx+1
      have h_i_lt : i < s.tokens.tokens.size := by omega
      change (s.overwriteAtCursor (s.simpleKey.tokenIndex + 1) s.simpleKey.cursor
              YamlToken.key).tokens[i]'_ = s.tokens[i]'(by omega)
      change (s.tokens.tokens.setIfInBounds (s.simpleKey.tokenIndex + 1) _)[i]'_ =
        s.tokens.tokens[i]'h_i_lt
      exact Array.getElem_setIfInBounds_ne h_i_lt
            (show s.simpleKey.tokenIndex + 1 ≠ i from by omega)
  · split
    · -- explicitKeyLine.isSome: record-update on simpleKey only
      rfl
    · split
      · -- !inFlow: pushMappingIndentIx
        exact pushMappingIndentIx_preserves_prefix s s.cursor.pos.col i (by omega)
      · -- inFlow: identity
        rfl

theorem scanValueIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanValueIx s = .ok s')
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : s.simpleKey.possible = true → n ≤ s.simpleKey.tokenIndex)
    (i : Nat) (h_bound : i < n) :
    s'.tokens[i]'(by have := scanValueIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'(by omega) := by
  unfold scanValueIx at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · cases h_ok
  · split at h_ok
    · cases h_ok
    · simp only [Except.ok.injEq] at h_ok
      subst h_ok
      -- s' = ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).advance
      --        with simpleKeyAllowed := true, explicitKeyLine := none
      -- Chain: clearKey preserves (rfl), prepare preserves at idx+1, emit preserves, advance preserves.
      have h_ck := scanValueClearKeyIx_tokens s
      -- After scanValueClearKeyIx, simpleKey.possible / tokenIndex may shift; bridge via h_inv.
      have h_inv' : (scanValueClearKeyIx s).simpleKey.possible = true →
          n ≤ (scanValueClearKeyIx s).simpleKey.tokenIndex := by
        unfold scanValueClearKeyIx
        split
        · split
          · simp
          · split
            · simp
            · exact h_inv
        · exact h_inv
      have h_n' : n ≤ (scanValueClearKeyIx s).tokens.size := by
        rw [h_ck]; exact h_n
      have h_prep := scanValuePrepareIx_preserves_prefix (scanValueClearKeyIx s) n h_n' h_inv'
        i h_bound
      have h_prep_sz := scanValuePrepareIx_tokens_size_le (scanValueClearKeyIx s)
      have h_i_lt_prep : i < (scanValuePrepareIx (scanValueClearKeyIx s)).tokens.size := by
        rw [h_ck] at h_prep_sz; omega
      have h_emit := emit_preserves_tokens_at
        (scanValuePrepareIx (scanValueClearKeyIx s)) YamlToken.value i h_i_lt_prep
      show ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).tokens[i]'_ =
        s.tokens[i]'(by omega)
      calc ((scanValuePrepareIx (scanValueClearKeyIx s)).emit YamlToken.value).tokens[i]'_
          = (scanValuePrepareIx (scanValueClearKeyIx s)).tokens[i]'h_i_lt_prep := h_emit
        _ = (scanValueClearKeyIx s).tokens[i]'(by rw [h_ck]; omega) := h_prep
        _ = s.tokens[i]'(by omega) := by simp

/-- After Step 6f.0, `scanFlowEntryIx` no longer calls
    `scanValuePrepareIx`, so the prefix is preserved unconditionally
    (no `h_inv` simple-key boundary hypothesis needed). -/
theorem scanFlowEntryIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanFlowEntryIx s = .ok s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanFlowEntryIx_tokens_size_le h_ok; omega) =
    s.tokens[i]'h_bound := by
  unfold scanFlowEntryIx at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_emit := emit_preserves_tokens_at s YamlToken.flowEntry i h_bound
  repeat (any_goals (split at h_ok))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h_ok; subst h_ok)
  all_goals (
    show ({ (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }).tokens[i]'_ =
      s.tokens[i]'h_bound
    simp only [advance_tokens]
    exact h_emit)

/-! ## §12l  Dispatcher composition for `AllKeysPlaceholderInvIx` (Step 6d.1e.12c.2)

Indexed twin of legacy `saveSimpleKey_preserves_AllKeysPlaceholderInv`
through `dispatchContent_preserves_AllKeysPlaceholderInv` (lines
4430–4958 of `Proofs/Production/ScannerPlainScalarValid.lean`).
Composes the §12g–12k `_preserves_prefix` substrate (Step 6d.1e.12c.1)
with the §12c–12e `_preserves_simpleKey`/`_preserves_simpleKeyStack`/
`_clears_simpleKey`/`_simpleKey_cleared`/`_simpleKey_restored`/
`_stack_pushed`/`_stack_popped` facts and the per-scanner
`_tokens_size_le` library to derive eight dispatcher-level
`_preserves_AllKeysPlaceholderInvIx` theorems.

Branch shape:
- Mono scanners: `AllKeysPlaceholderInvIx_mono`.
- Cleared scanners: `AllKeysPlaceholderInvIx_of_cleared_mono`.
- Flow start/end: `flowStart`/`flowEnd_preserves_AllKeysPlaceholderInvIx`
  helpers (this section) packaged with `_simpleKey_cleared` /
  `_simpleKey_restored` / `_stack_pushed` / `_stack_popped`.
- `scanValueIx` arm: `AllKeysPlaceholderInvIx_of_cleared_current`
  with the bounded §12k `scanValueIx_preserves_prefix`. -/

/-- Full state-equation case enumeration of `saveSimpleKeyIx`: either
    identity (no-op branches) or push 2 placeholders + set `simpleKey`.
    Routes proofs around the let-bound state form that
    `unfold + split` produces (which `omega`/`simp` cannot reduce
    through). -/
theorem saveSimpleKeyIx_state_cases {input : String} (s : ScannerStateIx input) :
    saveSimpleKeyIx s = s ∨
    saveSimpleKeyIx s =
      { (s.emit YamlToken.placeholder).emit YamlToken.placeholder with
          simpleKey := { possible := true, tokenIndex := s.tokens.size,
                         cursor := ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).cursor,
                         endLine := ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).cursor.pos.line } } := by
  unfold saveSimpleKeyIx
  split
  · left; rfl
  · split
    · right; rfl
    · left; rfl

theorem saveSimpleKeyIx_preserves_AllKeysPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (h_akpi : AllKeysPlaceholderInvIx s) :
    AllKeysPlaceholderInvIx (saveSimpleKeyIx s) := by
  rcases saveSimpleKeyIx_state_cases s with h_eq | h_eq
  · rw [h_eq]; exact h_akpi
  · rw [h_eq]
    -- Bridging equalities for ((s.emit ph).emit ph).
    have h_size : ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size =
        s.tokens.size + 2 := by rw [emit_tokens_size, emit_tokens_size]
    have h_stack_eq :
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack = s.simpleKeyStack := by
      rw [emit_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]
    have h1_lt' : s.tokens.size <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [h_size]; omega
    have h2_lt : s.tokens.size + 1 <
        ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size := by
      rw [h_size]; omega
    -- First placeholder slot.
    have h_tok1 : (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size]'h1_lt').token =
        YamlToken.placeholder := by
      have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
        emit_tokens_size s .placeholder
      have h_first_lt : s.tokens.size < (s.emit YamlToken.placeholder).tokens.size := by
        rw [h_size1]; omega
      have h_step :
          ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size]'h1_lt' =
          (s.emit YamlToken.placeholder).tokens[s.tokens.size]'h_first_lt :=
        emit_preserves_tokens_at (s.emit YamlToken.placeholder) .placeholder s.tokens.size h_first_lt
      rw [h_step, emit_new_token_token s .placeholder h_first_lt]
    -- Second placeholder slot.
    have h_tok2 : (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[s.tokens.size + 1]'h2_lt).token =
        YamlToken.placeholder := by
      have h_size1 : (s.emit YamlToken.placeholder).tokens.size = s.tokens.size + 1 :=
        emit_tokens_size s .placeholder
      have h_at : ∀ (j : Nat) (hj : j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size)
          (_hge : j = (s.emit YamlToken.placeholder).tokens.size),
          (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[j]'hj).token = YamlToken.placeholder := by
        intro j hj hge
        subst hge
        exact emit_new_token_token (s.emit YamlToken.placeholder) .placeholder hj
      exact h_at (s.tokens.size + 1) h2_lt h_size1.symm
    refine ⟨?_, ?_, ?_, ?_⟩
    · -- SimpleKeyPlaceholderInvIx — new simpleKey has possible := true, tokenIndex := s.tokens.size.
      intro _h_poss
      change s.tokens.size < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size ∧
             s.tokens.size + 1 < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens.size ∧ _
      refine ⟨h1_lt', h2_lt, ?_, ?_⟩
      · intro _h; exact h_tok1
      · intro _h; exact h_tok2
    · -- SimpleKeyStackPlaceholderInvIx — stack unchanged; existing prefix preserved.
      intro j hj h_poss_j
      change j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack.size at hj
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).possible = true at h_poss_j
      have hj_s : j < s.simpleKeyStack.size := by rw [h_stack_eq] at hj; exact hj
      have h_get :
          ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj =
          s.simpleKeyStack[j]'hj_s := by simp
      rw [h_get] at h_poss_j
      have ⟨hb1, hb2, hp1, hp2⟩ := h_akpi.2.1 j hj_s h_poss_j
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).tokenIndex < _ ∧
             (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).tokenIndex + 1 < _ ∧ _
      rw [h_get]
      refine ⟨by rw [h_size]; omega, by rw [h_size]; omega, ?_, ?_⟩
      · intro _h1
        change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[
                  (s.simpleKeyStack[j]'hj_s).tokenIndex]'_).token = _
        rw [twoPlaceholderEmits_preserves_prefix s _ hb1]; exact hp1 hb1
      · intro _h2
        change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens[
                  (s.simpleKeyStack[j]'hj_s).tokenIndex + 1]'_).token = _
        rw [twoPlaceholderEmits_preserves_prefix s _ hb2]; exact hp2 hb2
    · -- SimpleKeyTokenDisjointIx — new simpleKey.tokenIndex = s.tokens.size; stacked + 1 < s.tokens.size.
      intro _h_poss j hj h_poss_j
      change j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack.size at hj
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).possible = true at h_poss_j
      have hj_s : j < s.simpleKeyStack.size := by rw [h_stack_eq] at hj; exact hj
      have h_get :
          ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj =
          s.simpleKeyStack[j]'hj_s := by simp
      rw [h_get] at h_poss_j
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).tokenIndex + 1 < s.tokens.size
      rw [h_get]
      have ⟨_, hb2, _, _⟩ := h_akpi.2.1 j hj_s h_poss_j
      exact hb2
    · -- SimpleKeyStackOrderingIx — stack unchanged.
      intro j hj h_poss_j k hk h_poss_k
      change j < ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack.size at hj
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).possible = true at h_poss_j
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[k]'(by omega)).possible = true at h_poss_k
      have hj_s : j < s.simpleKeyStack.size := by rw [h_stack_eq] at hj; exact hj
      have hk_s : k < s.simpleKeyStack.size := by omega
      have h_get_j :
          ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj =
          s.simpleKeyStack[j]'hj_s := by simp
      have h_get_k :
          (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[k]'(by omega)) =
          s.simpleKeyStack[k]'hk_s := by simp
      rw [h_get_j] at h_poss_j
      rw [h_get_k] at h_poss_k
      change (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[k]'(by omega)).tokenIndex + 1 <
             (((s.emit YamlToken.placeholder).emit YamlToken.placeholder).simpleKeyStack[j]'hj).tokenIndex
      rw [h_get_j, h_get_k]
      exact h_akpi.2.2.2 j hj_s h_poss_j k hk h_poss_k

/-- `scanNextTokenIx_preprocess` preserves `AllKeysPlaceholderInvIx`.
    Composes `skipToContentS` (cursor-only update) with the conditional
    `unwindIndentsIx` and the final `saveSimpleKeyIx`. -/
theorem scanNextTokenIx_preprocess_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_pre : scanNextTokenIx_preprocess s = .ok (some (s', c)))
    (h_akpi : AllKeysPlaceholderInvIx s) :
    AllKeysPlaceholderInvIx s' := by
  have h_skip_sk : s.skipToContentS.simpleKey = s.simpleKey := skipToContentS_preserves_simpleKey s
  have h_skip_stack : s.skipToContentS.simpleKeyStack = s.simpleKeyStack :=
    skipToContentS_preserves_simpleKeyStack s
  have h_skip_mono : s.skipToContentS.tokens.size ≥ s.tokens.size := by
    simp [skipToContentS_tokens]
  have h_skip_pref : ∀ i (h : i < s.tokens.size),
      s.skipToContentS.tokens[i]'(by omega) = s.tokens[i] := by
    intro i hi; simp [skipToContentS_tokens]
  have h_akpi_skip : AllKeysPlaceholderInvIx s.skipToContentS :=
    AllKeysPlaceholderInvIx_mono s s.skipToContentS h_akpi
      h_skip_sk h_skip_stack h_skip_mono h_skip_pref
  unfold scanNextTokenIx_preprocess at h_pre
  simp only at h_pre
  split at h_pre
  · simp at h_pre
  · split at h_pre
    · -- with indent check: s1 = { unwindIndentsIx s.skipToContentS _ with needIndentCheck := false }
      have h_unwind_sk :
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).simpleKey =
          s.skipToContentS.simpleKey := unwindIndentsIx_preserves_simpleKey _ _
      have h_unwind_stack :
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).simpleKeyStack =
          s.skipToContentS.simpleKeyStack := unwindIndentsIx_preserves_simpleKeyStack _ _
      have h_unwind_mono : s.skipToContentS.tokens.size ≤
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens.size :=
        unwindIndentsIx_tokens_size_le _ _
      have h_unwind_pref : ∀ i (h : i < s.skipToContentS.tokens.size),
          (unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col).tokens[i]'(by omega) =
          s.skipToContentS.tokens[i] := fun i hi =>
        unwindIndentsIx_preserves_prefix _ _ i hi
      have h_akpi_unwind : AllKeysPlaceholderInvIx
          { unwindIndentsIx s.skipToContentS s.skipToContentS.cursor.pos.col with
              needIndentCheck := false } :=
        AllKeysPlaceholderInvIx_mono s.skipToContentS _ h_akpi_skip
          h_unwind_sk h_unwind_stack h_unwind_mono h_unwind_pref
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_preserves_AllKeysPlaceholderInvIx _ h_akpi_unwind
    · -- without indent check: s1 = s.skipToContentS
      split at h_pre
      · simp at h_pre
      · split at h_pre
        · simp at h_pre
        · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_pre
          obtain ⟨hs, _⟩ := h_pre
          subst hs
          exact saveSimpleKeyIx_preserves_AllKeysPlaceholderInvIx _ h_akpi_skip

/-- `scanNextTokenIx_dispatchStructural` preserves `AllKeysPlaceholderInvIx`.
    Each of the three productions (`scanDocumentStartIx`,
    `scanDocumentEndIx`, `scanDirectiveIx`) either clears `possible`
    (vacuous) or preserves `simpleKey`+`simpleKeyStack`+prefix. -/
theorem scanNextTokenIx_dispatchStructural_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s')) :
    AllKeysPlaceholderInvIx s' := by
  rcases scanNextTokenIx_dispatchStructural_ok_some_cases h_ok with heq | hOk | hOk
  · subst heq
    exact AllKeysPlaceholderInvIx_of_cleared_mono s _ h_akpi
      (scanDocumentStartIx_clears_simpleKey s)
      (scanDocumentStartIx_preserves_simpleKeyStack s)
      (scanDocumentStartIx_tokens_size_le s)
      (fun i hi => scanDocumentStartIx_preserves_prefix s i hi)
  · exact AllKeysPlaceholderInvIx_of_cleared_mono s _ h_akpi
      (scanDocumentEndIx_clears_simpleKey s s' hOk)
      (scanDocumentEndIx_preserves_simpleKeyStack s s' hOk)
      (scanDocumentEndIx_tokens_size_le hOk)
      (fun i hi => scanDocumentEndIx_preserves_prefix s s' hOk i hi)
  · exact AllKeysPlaceholderInvIx_mono s _ h_akpi
      (scanDirectiveIx_preserves_simpleKey s s' hOk)
      (scanDirectiveIx_preserves_simpleKeyStack s s' hOk)
      (scanDirectiveIx_tokens_size_le hOk)
      (fun i hi => scanDirectiveIx_preserves_prefix s s' hOk i hi)

/-- Flow start preserves `AllKeysPlaceholderInvIx`. Pushes current key
    to stack, clears current. Indexed twin of legacy
    `flowStart_preserves_AllKeysPlaceholderInv`. -/
theorem flowStart_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_cleared : s'.simpleKey.possible = false)
    (h_pushed : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey)
    (h_mono : s.tokens.size ≤ s'.tokens.size)
    (h_pref : ∀ i (hi : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    AllKeysPlaceholderInvIx s' := by
  refine ⟨SimpleKeyPlaceholderInvIx_of_not_possible _ h_cleared, ?_,
          SimpleKeyTokenDisjointIx_of_not_possible _ h_cleared, ?_⟩
  · -- SimpleKeyStackPlaceholderInvIx: old stack + pushed current
    intro j hj h_poss_j
    have hj_sz : j < s.simpleKeyStack.size + 1 := by
      rw [h_pushed, Array.size_push] at hj; exact hj
    have hg_j : s'.simpleKeyStack[j]'hj =
        (s.simpleKeyStack.push s.simpleKey)[j]'(by rw [Array.size_push]; exact hj_sz) := by
      simp [h_pushed]
    rw [hg_j] at h_poss_j ⊢
    by_cases hlt : j < s.simpleKeyStack.size
    · rw [Array.getElem_push_lt hlt] at h_poss_j ⊢
      have ⟨hb1, hb2, hp1, hp2⟩ := h_akpi.2.1 j hlt h_poss_j
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro _h1; rw [h_pref _ hb1]; exact hp1 hb1
      · intro _h2; rw [h_pref _ hb2]; exact hp2 hb2
    · have hj_eq : j = s.simpleKeyStack.size := by omega
      subst hj_eq
      rw [Array.getElem_push_eq] at h_poss_j ⊢
      have ⟨hb1, hb2, hp1, hp2⟩ := h_akpi.1 h_poss_j
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro _h1; rw [h_pref _ hb1]; exact hp1 hb1
      · intro _h2; rw [h_pref _ hb2]; exact hp2 hb2
  · -- SimpleKeyStackOrderingIx: old ordering + pushed top
    intro j hj h_poss_j k hk h_poss_k
    have hj_sz : j < s.simpleKeyStack.size + 1 := by
      rw [h_pushed, Array.size_push] at hj; exact hj
    have hk_sz : k < s.simpleKeyStack.size + 1 := by omega
    have hg_j : s'.simpleKeyStack[j]'hj =
        (s.simpleKeyStack.push s.simpleKey)[j]'(by rw [Array.size_push]; exact hj_sz) := by
      simp [h_pushed]
    have hg_k : s'.simpleKeyStack[k]'(by omega) =
        (s.simpleKeyStack.push s.simpleKey)[k]'(by rw [Array.size_push]; exact hk_sz) := by
      simp [h_pushed]
    rw [hg_j] at h_poss_j ⊢
    rw [hg_k] at h_poss_k ⊢
    by_cases hlt_j : j < s.simpleKeyStack.size
    · rw [Array.getElem_push_lt hlt_j] at h_poss_j ⊢
      have hlt_k : k < s.simpleKeyStack.size := by omega
      rw [Array.getElem_push_lt hlt_k] at h_poss_k ⊢
      exact h_akpi.2.2.2 j hlt_j h_poss_j k hk h_poss_k
    · have hj_eq : j = s.simpleKeyStack.size := by omega
      subst hj_eq
      rw [Array.getElem_push_eq] at h_poss_j ⊢
      have hlt_k : k < s.simpleKeyStack.size := by omega
      rw [Array.getElem_push_lt hlt_k] at h_poss_k ⊢
      exact h_akpi.2.2.1 h_poss_j k hlt_k h_poss_k

/-- Flow end preserves `AllKeysPlaceholderInvIx`. Restores current key
    from stack top, pops stack. Indexed twin of legacy
    `flowEnd_preserves_AllKeysPlaceholderInv`. -/
theorem flowEnd_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_restored : s'.simpleKey =
      s.simpleKeyStack.back?.getD { cursor := IxCursor.start input })
    (h_popped : s'.simpleKeyStack = s.simpleKeyStack.pop)
    (h_mono : s.tokens.size ≤ s'.tokens.size)
    (h_pref : ∀ i (hi : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    AllKeysPlaceholderInvIx s' := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- SimpleKeyPlaceholderInvIx: restored from stack top
    intro h_poss
    rw [h_restored] at h_poss ⊢
    by_cases h_size : s.simpleKeyStack.size > 0
    · have h_bound : s.simpleKeyStack.size - 1 < s.simpleKeyStack.size := by omega
      have h_get_back :
          (s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }) =
          s.simpleKeyStack[s.simpleKeyStack.size - 1]'h_bound := by
        simp [Array.back?, h_bound]
      rw [h_get_back] at h_poss ⊢
      have ⟨hb1, hb2, hp1, hp2⟩ := h_akpi.2.1 (s.simpleKeyStack.size - 1) h_bound h_poss
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro _h1; rw [h_pref _ hb1]; exact hp1 hb1
      · intro _h2; rw [h_pref _ hb2]; exact hp2 hb2
    · have h_empty : s.simpleKeyStack.size = 0 := by omega
      simp [Array.back?, h_empty] at h_poss
  · -- SimpleKeyStackPlaceholderInvIx: popped stack
    intro j hj h_poss
    have hj' : j < s.simpleKeyStack.size := by
      simp [h_popped, Array.size_pop] at hj; omega
    have hg_j : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj' := by
      simp [h_popped, Array.getElem_pop]
    rw [hg_j] at h_poss ⊢
    have ⟨hb1, hb2, hp1, hp2⟩ := h_akpi.2.1 j hj' h_poss
    refine ⟨by omega, by omega, ?_, ?_⟩
    · intro _h1; rw [h_pref _ hb1]; exact hp1 hb1
    · intro _h2; rw [h_pref _ hb2]; exact hp2 hb2
  · -- SimpleKeyTokenDisjointIx: restored key vs popped stack
    intro h_poss j hj h_poss_j
    rw [h_restored] at h_poss ⊢
    by_cases h_size : s.simpleKeyStack.size > 0
    · have h_bound : s.simpleKeyStack.size - 1 < s.simpleKeyStack.size := by omega
      have h_get_back :
          (s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }) =
          s.simpleKeyStack[s.simpleKeyStack.size - 1]'h_bound := by
        simp [Array.back?, h_bound]
      rw [h_get_back] at h_poss ⊢
      have hj' : j < s.simpleKeyStack.size := by
        simp [h_popped, Array.size_pop] at hj; omega
      have hj_lt_top : j < s.simpleKeyStack.size - 1 := by
        simp [h_popped, Array.size_pop] at hj; omega
      have hg_j : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj' := by
        simp [h_popped, Array.getElem_pop]
      rw [hg_j] at h_poss_j ⊢
      exact h_akpi.2.2.2 (s.simpleKeyStack.size - 1) h_bound h_poss j hj_lt_top h_poss_j
    · have h_empty : s.simpleKeyStack.size = 0 := by omega
      simp [Array.back?, h_empty] at h_poss
  · -- SimpleKeyStackOrderingIx: popped stack is a prefix of old stack
    intro j hj h_poss_j k hk h_poss_k
    have hj' : j < s.simpleKeyStack.size := by
      simp [h_popped, Array.size_pop] at hj; omega
    have hk' : k < s.simpleKeyStack.size := by omega
    have hg_j : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj' := by
      simp [h_popped, Array.getElem_pop]
    have hg_k : s'.simpleKeyStack[k]'(by omega) = s.simpleKeyStack[k]'hk' := by
      simp [h_popped, Array.getElem_pop]
    rw [hg_j] at h_poss_j ⊢
    rw [hg_k] at h_poss_k ⊢
    exact h_akpi.2.2.2 j hj' h_poss_j k hk h_poss_k

/-- `scanNextTokenIx_dispatchFlowIndicators` preserves `AllKeysPlaceholderInvIx`.
    Flow start (`[`, `{`) pushes current key + clears; flow end (`]`, `}`)
    restores from top + pops; `,` (flow entry) clears + preserves stack. -/
theorem scanNextTokenIx_dispatchFlowIndicators_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s')) :
    AllKeysPlaceholderInvIx s' := by
  rcases scanNextTokenIx_dispatchFlowIndicators_ok_some_cases h_ok with
    heq | heq | heq | heq | hOk
  · subst heq
    exact flowStart_preserves_AllKeysPlaceholderInvIx s _ h_akpi
      (scanFlowSequenceStartIx_simpleKey_cleared s)
      (scanFlowSequenceStartIx_stack_pushed s)
      (scanFlowSequenceStartIx_tokens_size_le s)
      (fun i hi => scanFlowSequenceStartIx_preserves_prefix s i hi)
  · subst heq
    exact flowEnd_preserves_AllKeysPlaceholderInvIx s _ h_akpi
      (scanFlowSequenceEndIx_simpleKey_restored s)
      (scanFlowSequenceEndIx_stack_popped s)
      (scanFlowSequenceEndIx_tokens_size_le s)
      (fun i hi => scanFlowSequenceEndIx_preserves_prefix s i hi)
  · subst heq
    exact flowStart_preserves_AllKeysPlaceholderInvIx s _ h_akpi
      (scanFlowMappingStartIx_simpleKey_cleared s)
      (scanFlowMappingStartIx_stack_pushed s)
      (scanFlowMappingStartIx_tokens_size_le s)
      (fun i hi => scanFlowMappingStartIx_preserves_prefix s i hi)
  · subst heq
    exact flowEnd_preserves_AllKeysPlaceholderInvIx s _ h_akpi
      (scanFlowMappingEndIx_simpleKey_restored s)
      (scanFlowMappingEndIx_stack_popped s)
      (scanFlowMappingEndIx_tokens_size_le s)
      (fun i hi => scanFlowMappingEndIx_preserves_prefix s i hi)
  · -- scanFlowEntryIx (after Step 6f.0): mono — preserves simpleKey,
    -- simpleKeyStack, and adds one token (`.flowEntry`), so prefix is
    -- preserved by `emit_preserves_tokens_at`. The `,` boundary no
    -- longer calls `scanValuePrepareIx`, matching the legacy.
    exact AllKeysPlaceholderInvIx_mono s s' h_akpi
      (scanFlowEntryIx_preserves_simpleKey s s' hOk)
      (scanFlowEntryIx_preserves_simpleKeyStack s s' hOk)
      (scanFlowEntryIx_tokens_size_le hOk)
      (fun i hi => scanFlowEntryIx_preserves_prefix s s' hOk i hi)

/-- `scanNextTokenIx_dispatchBlockIndicators` preserves `AllKeysPlaceholderInvIx`.
    `scanBlockEntryIx` is mono; `scanKeyIx` clears + preserves stack;
    `scanValueIx` clears + preserves stack but overwrites at sk positions
    (use bounded `scanValueIx_preserves_prefix` from §12k). -/
theorem scanNextTokenIx_dispatchBlockIndicators_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s')) :
    AllKeysPlaceholderInvIx s' := by
  rcases scanNextTokenIx_dispatchBlockIndicators_ok_some_cases h_ok with hOk | hOk | hOk
  · -- scanBlockEntryIx: preserves simpleKey + stack + prefix.
    exact AllKeysPlaceholderInvIx_mono s _ h_akpi
      (scanBlockEntryIx_preserves_simpleKey s s' hOk)
      (scanBlockEntryIx_preserves_simpleKeyStack s s' hOk)
      (scanBlockEntryIx_tokens_size_le hOk)
      (fun i hi => scanBlockEntryIx_preserves_prefix s s' hOk i hi)
  · -- scanKeyIx: clears + preserves stack + prefix.
    exact AllKeysPlaceholderInvIx_of_cleared_mono s _ h_akpi
      (scanKeyIx_clears_simpleKey s s' hOk)
      (scanKeyIx_preserves_simpleKeyStack s s' hOk)
      (scanKeyIx_tokens_size_le hOk)
      (fun i hi => scanKeyIx_preserves_prefix s s' hOk i hi)
  · -- scanValueIx: clears + preserves stack + overwrites at sk positions.
    have h_clears := scanValueIx_clears_simpleKey s s' hOk
    have h_stack := scanValueIx_preserves_simpleKeyStack s s' hOk
    have h_mono := scanValueIx_tokens_size_le hOk
    refine AllKeysPlaceholderInvIx_of_cleared_current s' h_clears ?_ ?_ ?_
    · intro j hj h_poss_j
      have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
      have h_get : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj_s := by simp [h_stack]
      rw [h_get] at h_poss_j ⊢
      have ⟨hb1, hb2, hp1, hp2⟩ := h_akpi.2.1 j hj_s h_poss_j
      refine ⟨by omega, by omega, ?_, ?_⟩
      · intro _h1
        rw [scanValueIx_preserves_prefix s s' hOk
              ((s.simpleKeyStack[j]'hj_s).tokenIndex + 2) (by omega)
              (fun hp => by have := h_akpi.2.2.1 hp j hj_s h_poss_j; omega)
              (s.simpleKeyStack[j]'hj_s).tokenIndex (by omega)]
        exact hp1 hb1
      · intro _h2
        rw [scanValueIx_preserves_prefix s s' hOk
              ((s.simpleKeyStack[j]'hj_s).tokenIndex + 2) (by omega)
              (fun hp => by have := h_akpi.2.2.1 hp j hj_s h_poss_j; omega)
              ((s.simpleKeyStack[j]'hj_s).tokenIndex + 1) (by omega)]
        exact hp2 hb2
    · exact SimpleKeyTokenDisjointIx_of_not_possible _ h_clears
    · intro j hj h_poss_j k hk h_poss_k
      have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
      have hk_s : k < s.simpleKeyStack.size := by omega
      have h_get_j : s'.simpleKeyStack[j]'hj = s.simpleKeyStack[j]'hj_s := by simp [h_stack]
      have h_get_k : (s'.simpleKeyStack[k]'(by omega)) =
          s.simpleKeyStack[k]'hk_s := by simp [h_stack]
      rw [h_get_j] at h_poss_j ⊢
      rw [h_get_k] at h_poss_k ⊢
      exact h_akpi.2.2.2 j hj_s h_poss_j k hk h_poss_k

/-- Helper for the inline-scalar arms of `scanNextTokenIx_dispatchContent`.
    The post-state is `{ ({ s with cursor := cAfter }).emitAt startPos
    tok hBound with simpleKeyAllowed := false }` — only `cursor`,
    `tokens`, and `simpleKeyAllowed` change; `simpleKey`/`simpleKeyStack`
    are preserved. -/
theorem _inline_scalar_preserves_AllKeysPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (cAfter : IxCursor input)
    (startPos : YamlPos) (tok : YamlToken)
    (hBound : startPos.offset ≤ cAfter.pos.offset)
    (h_akpi : AllKeysPlaceholderInvIx s) :
    AllKeysPlaceholderInvIx
      { ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
          simpleKeyAllowed := false } := by
  have h_sk :
      ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
          simpleKeyAllowed := false } : ScannerStateIx input).simpleKey = s.simpleKey := by simp
  have h_stack :
      ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
          simpleKeyAllowed := false } : ScannerStateIx input).simpleKeyStack = s.simpleKeyStack := by
    simp
  have h_mono : s.tokens.size ≤
      ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
          simpleKeyAllowed := false } : ScannerStateIx input).tokens.size := by
    show s.tokens.size ≤
      (({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound).tokens.size
    rw [emitAt_tokens_size]
    have h_eq : ({ s with cursor := cAfter } : ScannerStateIx input).tokens.size = s.tokens.size := rfl
    omega
  have h_pref : ∀ i (h : i < s.tokens.size),
      ({ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound with
          simpleKeyAllowed := false } : ScannerStateIx input).tokens[i]'(by omega) = s.tokens[i] := by
    intro i hi
    show (({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos tok hBound).tokens[i]'_ =
      s.tokens[i]'hi
    exact emitAt_preserves_tokens_at ({ s with cursor := cAfter } : ScannerStateIx input)
      startPos tok hBound i hi
  exact AllKeysPlaceholderInvIx_mono s _ h_akpi h_sk h_stack h_mono h_pref

/-- `scanNextTokenIx_dispatchContent` preserves `AllKeysPlaceholderInvIx`.
    7 productions: `&`/`*` (anchor/alias via `scanAnchorOrAliasIx`),
    `!` (tag), `|`/`>` (block scalar), `"` (double-quoted),
    `'` (single-quoted), plain scalar. All preserve `simpleKey`+
    `simpleKeyStack` and add one token. -/
theorem scanNextTokenIx_dispatchContent_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input) (c : Char)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx_dispatchContent s c = .ok s') :
    AllKeysPlaceholderInvIx s' := by
  -- Peel the 7-way content dispatch one `if` at a time with `by_cases`/`rw`, mirroring the
  -- `split`-free skeleton of `scanNextTokenIx_dispatchContent_preserves_PlainScalarsValidIx`.
  -- (A single `split` over the whole dispatch exceeds `split`'s internal simp step budget
  -- under Lean 4.31.0; peeling keeps each `split` confined to a small inner `Except` match.)
  unfold scanNextTokenIx_dispatchContent at h_ok
  by_cases hg1 : (c == '&') = true
  · -- c == '&': anchor
    rw [if_pos hg1] at h_ok
    try simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    cases hA : scanAnchorOrAliasIx s true with
    | error e => rw [hA] at h_ok; cases h_ok
    | ok v =>
      rw [hA] at h_ok
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact AllKeysPlaceholderInvIx_mono s v h_akpi
        (scanAnchorOrAliasIx_preserves_simpleKey s true v hA)
        (scanAnchorOrAliasIx_preserves_simpleKeyStack s true v hA)
        (scanAnchorOrAliasIx_tokens_size_le hA)
        (fun i hi => scanAnchorOrAliasIx_preserves_prefix s true v hA i hi)
  · rw [if_neg hg1] at h_ok
    simp only [Bind.bind, Except.bind, Pure.pure, Except.pure] at h_ok
    by_cases hg2 : (c == '*') = true
    · -- c == '*': alias
      rw [if_pos hg2] at h_ok
      cases hA : scanAnchorOrAliasIx s false with
      | error e => rw [hA] at h_ok; cases h_ok
      | ok v =>
        rw [hA] at h_ok
        simp only [Except.ok.injEq] at h_ok
        subst h_ok
        exact AllKeysPlaceholderInvIx_mono s v h_akpi
          (scanAnchorOrAliasIx_preserves_simpleKey s false v hA)
          (scanAnchorOrAliasIx_preserves_simpleKeyStack s false v hA)
          (scanAnchorOrAliasIx_tokens_size_le hA)
          (fun i hi => scanAnchorOrAliasIx_preserves_prefix s false v hA i hi)
    · rw [if_neg hg2] at h_ok
      by_cases hg3 : (c == '!') = true
      · -- c == '!': tag
        rw [if_pos hg3] at h_ok
        cases hT : scanTagIx s with
        | error e => rw [hT] at h_ok; cases h_ok
        | ok v =>
          rw [hT] at h_ok
          simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact AllKeysPlaceholderInvIx_mono s v h_akpi
            (scanTagIx_preserves_simpleKey s v hT)
            (scanTagIx_preserves_simpleKeyStack s v hT)
            (scanTagIx_tokens_size_le hT)
            (fun i hi => scanTagIx_preserves_prefix s v hT i hi)
      · rw [if_neg hg3] at h_ok
        by_cases hg4 : (c == '|' || c == '>') = true
        · -- c == '|' || c == '>': block scalar (inline match)
          rw [if_pos hg4] at h_ok
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok
            subst h_ok
            exact _inline_scalar_preserves_AllKeysPlaceholderInvIx s _ _ _ _ h_akpi
          · cases h_ok
        · rw [if_neg hg4] at h_ok
          by_cases hg5 : (c == '"') = true
          · -- c == '"': double quoted
            rw [if_pos hg5] at h_ok
            split at h_ok
            · simp only [Except.ok.injEq] at h_ok
              subst h_ok
              exact _inline_scalar_preserves_AllKeysPlaceholderInvIx s _ _ _ _ h_akpi
            · cases h_ok
          · rw [if_neg hg5] at h_ok
            by_cases hg6 : (c == '\'') = true
            · -- c == '\'': single quoted
              rw [if_pos hg6] at h_ok
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact _inline_scalar_preserves_AllKeysPlaceholderInvIx s _ _ _ _ h_akpi
              · cases h_ok
            · rw [if_neg hg6] at h_ok
              by_cases hg7 : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true
              · -- plain scalar (always succeeds)
                rw [if_pos hg7] at h_ok
                simp only [Except.ok.injEq] at h_ok
                subst h_ok
                exact _inline_scalar_preserves_AllKeysPlaceholderInvIx s _ _ _ _ h_akpi
              · rw [if_neg hg7] at h_ok
                cases h_ok

/-! ## §13  `AllKeysPlaceholderInvIx`-threaded consumers (Step 6d.1e.12d)

This section discharges the two §11i staging axioms
(`scanNextTokenIx_preprocess_preserves_SimpleKeyPlaceholderInvIx` and
`scanNextTokenIx_preserves_SimpleKeyPlaceholderInvIx`) by refactoring
the §11i/§11j/§11k consumer chain to thread the **full 4-tuple**
`AllKeysPlaceholderInvIx` instead of just `SimpleKeyPlaceholderInvIx`.

The §12l dispatcher composition gives us
`scanNextTokenIx_preprocess_preserves_AllKeysPlaceholderInvIx` and four
dispatcher-level `_preserves_AllKeysPlaceholderInvIx` theorems. Using
these, we compose `scanNextTokenIx_preserves_AllKeysPlaceholderInvIx`
(the new induction-step lemma for `scanLoopIx`), then re-derive the
PSV / FlowNesting consumer theorems and the top-level theorems. Sites
that only need the current-key conjunct project `.1` of the 4-tuple.

**Phase 3 closure after 12d**: **0 staged axioms** in
`IndexedScannerPlainScalarValid.lean` (the two §11i axioms are
discharged; the §7b/§7c/§8c/§8d/§8e scanner-side axioms remain on the
ladder but are out of scope for 12d). -/

/-- `emit tok` preserves `AllKeysPlaceholderInvIx` — `emit` leaves
    `simpleKey`/`simpleKeyStack` unchanged and grows `tokens` by one
    appended cell, so all four conjuncts transfer via
    `AllKeysPlaceholderInvIx_mono`. -/
theorem emit_preserves_AllKeysPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (tok : YamlToken)
    (h_akpi : AllKeysPlaceholderInvIx s) :
    AllKeysPlaceholderInvIx (s.emit tok) := by
  refine AllKeysPlaceholderInvIx_mono s (s.emit tok) h_akpi rfl rfl ?_ ?_
  · rw [emit_tokens_size]; omega
  · intro i hi
    exact emit_preserves_tokens_at s tok i hi

/-- The `if s.allowDirectives then ... else s` record update preserves
    `AllKeysPlaceholderInvIx`. In both branches `simpleKey`,
    `simpleKeyStack`, and `tokens` are unchanged. -/
theorem allowDirectives_update_AllKeysPlaceholderInvIx {input : String}
    (s : ScannerStateIx input) (h_akpi : AllKeysPlaceholderInvIx s) :
    AllKeysPlaceholderInvIx
      (if s.allowDirectives then
          { s with allowDirectives := false, documentEverStarted := true }
        else s) := by
  split
  · refine AllKeysPlaceholderInvIx_mono s _ h_akpi rfl rfl ?_ ?_
    · exact Nat.le.refl
    · intros; rfl
  · exact h_akpi

/-- The initial state after `.streamStart` emit satisfies
    `AllKeysPlaceholderInvIx`: starts vacuous (`simpleKey.possible
    = false`, empty stack) and emit-preservation propagates through
    the streamStart token. -/
theorem streamStart_AllKeysPlaceholderInvIx (input : String) :
    AllKeysPlaceholderInvIx ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
  emit_preserves_AllKeysPlaceholderInvIx
    (ScannerStateIx.mk' input) .streamStart (mk'_AllKeysPlaceholderInvIx input)

/-- `scanNextTokenIx` preserves `AllKeysPlaceholderInvIx`. Composes
    `_preprocess_preserves_AllKeysPlaceholderInvIx` (§12l) with
    `allowDirectives_update_AllKeysPlaceholderInvIx` and the four
    dispatcher-level `_preserves_AllKeysPlaceholderInvIx` theorems
    (§12l). Replaces the §11i staging axiom
    `scanNextTokenIx_preserves_SimpleKeyPlaceholderInvIx` (whose
    consumers now thread the full 4-tuple). -/
theorem scanNextTokenIx_preserves_AllKeysPlaceholderInvIx {input : String}
    (s s' : ScannerStateIx input)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    AllKeysPlaceholderInvIx s' := by
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
        have h_akpi_pp : AllKeysPlaceholderInvIx s_pp :=
          scanNextTokenIx_preprocess_preserves_AllKeysPlaceholderInvIx s s_pp c h_pp h_akpi
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            exact scanNextTokenIx_dispatchStructural_preserves_AllKeysPlaceholderInvIx
              s_pp s_str c h_akpi_pp h_ds
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_akpi_dir : AllKeysPlaceholderInvIx s_dir := by
              rw [← h_dir_def]
              exact allowDirectives_update_AllKeysPlaceholderInvIx s_pp h_akpi_pp
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
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_AllKeysPlaceholderInvIx
                    s_dir s_flow c h_akpi_dir h_df
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
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_AllKeysPlaceholderInvIx
                        s_dir s_blk c h_akpi_dir h_db
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        exact scanNextTokenIx_dispatchContent_preserves_AllKeysPlaceholderInvIx
                          s_dir s_ct c h_akpi_dir h_dc

/-- Refactored §11i theorem (Step 6d.1e.12d): now threads
    `AllKeysPlaceholderInvIx` and projects `.1` for the sub-dispatcher
    arms that still consume `SimpleKeyPlaceholderInvIx`. -/
theorem scanNextTokenIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_old : FlowContextPSVIx s.tokens)
    (h_fni : FlowNestingInvIx s)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    FlowContextPSVIx s'.tokens := by
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
        have h_old_pp : FlowContextPSVIx s_pp.tokens :=
          scanNextTokenIx_preprocess_preserves_FlowContextPSVIx s s_pp c h_pp h_old
        have h_fni_pp : FlowNestingInvIx s_pp :=
          scanNextTokenIx_preprocess_preserves_FlowNestingInvIx s s_pp c h_pp h_fni
        have h_akpi_pp : AllKeysPlaceholderInvIx s_pp :=
          scanNextTokenIx_preprocess_preserves_AllKeysPlaceholderInvIx s s_pp c h_pp h_akpi
        have h_pl_pp : SimpleKeyPlaceholderInvIx s_pp := h_akpi_pp.1
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            exact scanNextTokenIx_dispatchStructural_preserves_FlowContextPSVIx
              s_pp c s_str h_ds h_old_pp
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_old_dir : FlowContextPSVIx s_dir.tokens := by
              rw [← h_dir_def, allowDirectives_update_tokens]; exact h_old_pp
            have h_fni_dir : FlowNestingInvIx s_dir := by
              rw [← h_dir_def]
              unfold FlowNestingInvIx at h_fni_pp ⊢
              rw [allowDirectives_update_tokens, allowDirectives_update_flowLevel]
              exact h_fni_pp
            have h_pl_dir : SimpleKeyPlaceholderInvIx s_dir := by
              rw [← h_dir_def]
              exact allowDirectives_update_SimpleKeyPlaceholderInvIx s_pp h_pl_pp
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
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_FlowContextPSVIx
                    s_dir c s_flow h_df h_old_dir h_pl_dir
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
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_FlowContextPSVIx
                        s_dir c s_blk h_db h_old_dir h_pl_dir
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        have h_peek_pp : s_pp.cursor.peek? = some c :=
                          scanNextTokenIx_preprocess_peek_eq h_pp
                        have h_peek_dir : s_dir.cursor.peek? = some c := by
                          rw [← h_dir_def, allowDirectives_update_cursor]; exact h_peek_pp
                        exact scanNextTokenIx_dispatchContent_preserves_FlowContextPSVIx
                          s_dir c s_ct h_dc h_peek_dir h_fni_dir h_old_dir

/-- Refactored §11i theorem (Step 6d.1e.12d): mirrors
    `_FlowContextPSVIx` above. -/
theorem scanNextTokenIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_fni : FlowNestingInvIx s)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanNextTokenIx s = .ok (some s')) :
    FlowNestingInvIx s' := by
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
        have h_fni_pp : FlowNestingInvIx s_pp :=
          scanNextTokenIx_preprocess_preserves_FlowNestingInvIx s s_pp c h_pp h_fni
        have h_akpi_pp : AllKeysPlaceholderInvIx s_pp :=
          scanNextTokenIx_preprocess_preserves_AllKeysPlaceholderInvIx s s_pp c h_pp h_akpi
        have h_pl_pp : SimpleKeyPlaceholderInvIx s_pp := h_akpi_pp.1
        dsimp only [] at h_ok
        generalize h_ds : scanNextTokenIx_dispatchStructural s_pp c = ds_res at h_ok
        cases ds_res with
        | error e => simp at h_ok
        | ok ds_inner =>
          cases ds_inner with
          | some s_str =>
            simp only [Except.ok.injEq, Option.some.injEq] at h_ok
            subst h_ok
            exact scanNextTokenIx_dispatchStructural_preserves_FlowNestingInvIx
              s_pp c s_str h_ds h_fni_pp
          | none =>
            dsimp only [] at h_ok
            generalize h_dir_def : (if s_pp.allowDirectives = true then
                { s_pp with allowDirectives := false, documentEverStarted := true }
              else s_pp) = s_dir at h_ok
            have h_fni_dir : FlowNestingInvIx s_dir := by
              rw [← h_dir_def]
              unfold FlowNestingInvIx at h_fni_pp ⊢
              rw [allowDirectives_update_tokens, allowDirectives_update_flowLevel]
              exact h_fni_pp
            have h_pl_dir : SimpleKeyPlaceholderInvIx s_dir := by
              rw [← h_dir_def]
              exact allowDirectives_update_SimpleKeyPlaceholderInvIx s_pp h_pl_pp
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
                  exact scanNextTokenIx_dispatchFlowIndicators_preserves_FlowNestingInvIx
                    s_dir c s_flow h_df h_fni_dir h_pl_dir
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
                      exact scanNextTokenIx_dispatchBlockIndicators_preserves_FlowNestingInvIx
                        s_dir c s_blk h_db h_fni_dir h_pl_dir
                    | none =>
                      dsimp only [] at h_ok
                      generalize h_dc : scanNextTokenIx_dispatchContent s_dir c = dc_res at h_ok
                      cases dc_res with
                      | error e => simp at h_ok
                      | ok s_ct =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h_ok
                        subst h_ok
                        exact scanNextTokenIx_dispatchContent_preserves_FlowNestingInvIx
                          s_dir c s_ct h_dc h_fni_dir

/-- Refactored §11j theorem (Step 6d.1e.12d): threads
    `AllKeysPlaceholderInvIx` through the induction step. The recursive
    call uses `scanNextTokenIx_preserves_AllKeysPlaceholderInvIx`
    (defined above) to maintain the invariant. -/
theorem scanLoopIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (fuel : Nat)
    (tokens : Indexed.TokenStream input)
    (h_old : FlowContextPSVIx s.tokens)
    (h_fni : FlowNestingInvIx s)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanLoopIx s fuel = .ok tokens) :
    FlowContextPSVIx tokens := by
  induction fuel generalizing s with
  | zero => simp [scanLoopIx] at h_ok
  | succ fuel' ih =>
    simp only [scanLoopIx] at h_ok
    split at h_ok
    · cases h_ok
    · split at h_ok
      · cases h_ok
      · split at h_ok
        · cases h_ok
        · simp only [Except.ok.injEq] at h_ok
          subst h_ok
          exact finalEmit_preserves_FlowContextPSVIx s h_old
    · rename_i s' h_snt
      exact ih s'
        (scanNextTokenIx_preserves_FlowContextPSVIx s s' h_old h_fni h_akpi h_snt)
        (scanNextTokenIx_preserves_FlowNestingInvIx s s' h_fni h_akpi h_snt)
        (scanNextTokenIx_preserves_AllKeysPlaceholderInvIx s s' h_akpi h_snt)
        h_ok

/-- Refactored §11j theorem (Step 6d.1e.12d): mirrors the
    `_FlowContextPSVIx` form above. -/
theorem scanLoopIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (fuel : Nat)
    (tokens : Indexed.TokenStream input)
    (h_fni : FlowNestingInvIx s)
    (h_akpi : AllKeysPlaceholderInvIx s)
    (h_ok : scanLoopIx s fuel = .ok tokens) :
    flowNestingIx tokens tokens.size = 0 := by
  induction fuel generalizing s with
  | zero => simp [scanLoopIx] at h_ok
  | succ fuel' ih =>
    simp only [scanLoopIx] at h_ok
    split at h_ok
    · cases h_ok
    · split at h_ok
      · cases h_ok
      · split at h_ok
        · cases h_ok
        · simp only [Except.ok.injEq] at h_ok
          subst h_ok
          rename_i h_flow0 _h_dirOK
          have h_flowEq0 : s.flowLevel = 0 := by
            simp only [Nat.not_lt, Nat.le_zero] at h_flow0
            exact h_flow0
          have h_final := finalEmit_preserves_FlowNestingInvIx s h_fni
          unfold FlowNestingInvIx at h_final
          rw [h_final]
          show ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).flowLevel = 0
          have h_fl_emit : ((unwindIndentsIx s (-1)).emit YamlToken.streamEnd).flowLevel =
              (unwindIndentsIx s (-1)).flowLevel := rfl
          rw [h_fl_emit, unwindIndentsIx_preserves_flowLevel s (-1), h_flowEq0]
    · rename_i s' h_snt
      exact ih s'
        (scanNextTokenIx_preserves_FlowNestingInvIx s s' h_fni h_akpi h_snt)
        (scanNextTokenIx_preserves_AllKeysPlaceholderInvIx s s' h_akpi h_snt)
        h_ok

/-- Refactored §11k top-level theorem (Step 6d.1e.12d): establishes
    `AllKeysPlaceholderInvIx` at the initial post-`streamStart` state
    via `streamStart_AllKeysPlaceholderInvIx`, then threads it through
    the refactored `scanLoopIx_preserves_*` chain. -/
theorem scan_flow_aware_psv_ix_axiom
    {input : String} (tokens : Indexed.TokenStream input)
    (h_scan : ScannerStateIx.scanIx input = .ok tokens) :
    FlowAwarePSVIx tokens := by
  unfold ScannerStateIx.scanIx at h_scan
  have h_psv_after_emit : PlainScalarsValidIx
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens :=
    emit_non_plain_preserves_PlainScalarsValidIx _ .streamStart
      (mk'_PlainScalarsValidIx input) (by trivial)
  have h_fpsv_after_emit : FlowContextPSVIx
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart).tokens :=
    emit_non_flow_non_plain_preserves_FlowContextPSVIx _ .streamStart
      (mk'_FlowContextPSVIx input) (by trivial)
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  have h_akpi_after_emit : AllKeysPlaceholderInvIx
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
    streamStart_AllKeysPlaceholderInvIx input
  have h_fni_after_emit : FlowNestingInvIx
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
    emit_non_flow_preserves_FlowNestingInvIx _ .streamStart
      (mk'_FlowNestingInvIx input)
      (by decide) (by decide) (by decide) (by decide)
  refine ⟨?_, ?_⟩
  · exact scanLoopIx_preserves_PlainScalarsValidIx _ _ tokens
      (by split <;> exact h_psv_after_emit) h_scan
  · exact scanLoopIx_preserves_FlowContextPSVIx _ _ tokens
      (by split <;> exact h_fpsv_after_emit)
      (by split <;> exact h_fni_after_emit)
      (by split <;> exact h_akpi_after_emit) h_scan

/-- Refactored §11k top-level theorem (Step 6d.1e.12d): companion to
    `scan_flow_aware_psv_ix_axiom`. -/
theorem scan_flow_brackets_matched_ix_axiom
    {input : String} (tokens : Indexed.TokenStream input)
    (h_scan : ScannerStateIx.scanIx input = .ok tokens) :
    FlowBracketsMatchedIx tokens := by
  unfold ScannerStateIx.scanIx at h_scan
  have h_fni_after_emit : FlowNestingInvIx
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
    emit_non_flow_preserves_FlowNestingInvIx _ .streamStart
      (mk'_FlowNestingInvIx input)
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  have h_akpi_after_emit : AllKeysPlaceholderInvIx
      ((ScannerStateIx.mk' input).emit YamlToken.streamStart) :=
    streamStart_AllKeysPlaceholderInvIx input
  unfold FlowBracketsMatchedIx
  exact scanLoopIx_preserves_FlowNestingInvIx _ _ tokens
    (by split <;> exact h_fni_after_emit)
    (by split <;> exact h_akpi_after_emit) h_scan

end L4YAML.Proofs.Indexed.ScannerPlainScalarValid
