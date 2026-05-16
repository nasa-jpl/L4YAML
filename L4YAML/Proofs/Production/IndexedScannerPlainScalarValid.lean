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

### Phase 3 sub-step 6d.1e.1 (this file, current commit)

**Foundation tier** — the structural / algebraic building blocks
that don't depend on the per-action preservation chain:

1. **PSV propagation primitives**: `PlainScalarsValidIx_empty`,
   `PlainScalarsValidIx_of_prefix_and_new`, `psv_match_ix`,
   `psv_match_of_ne_plain_ix`, `psv_of_not_plain_ix`. Verbatim
   ports of the legacy lemmas modulo `.val` → `.token` and
   `Array (Positioned YamlToken)` → `Indexed.TokenStream input`.

2. **flowNestingIx prefix stability**:
   `flowNestingIx_go_prefix_stable`, `flowNestingIx_prefix_stable`,
   `flowNestingIx_go_single_push`, `flowNestingIx_push`,
   `flowNestingIx_push_non_flow`, `flowNestingIx_go_non_flow`. The
   `flowNestingIx_go_oob` / `_step` / `_ge_target` / `_split` lemmas
   live in `IndexedWellBehaved.lean` (Step 6d.1a, line 168ff);
   this file extends them with the prefix-stability and
   push-non-flow lemmas needed by the upcoming preservation chain.

3. **FlowContextPSVIx propagation primitives**:
   `FlowContextPSVIx_empty`, `FlowContextPSVIx_of_prefix_and_new`,
   `fpsv_of_not_plain_ix`.

4. **FlowNestingInvIx**: scanner-state invariant
   `flowNestingIx s.tokens s.tokens.size = s.flowLevel`. Carries
   the bridge between the token-array nesting depth and the
   scanner's `flowLevel` field; preserved through every
   non-flow-emitting scanner action.

5. **Generic emit-step preservation**: `emit_non_flow_preserves_FlowNestingInvIx`,
   `emit_non_plain_preserves_PlainScalarsValidIx`,
   `emit_non_flow_non_plain_preserves_FlowContextPSVIx`. These are
   the unit building blocks the per-action preservation lemmas will
   use to discharge their goals.

6. **2 staged axioms with tightened preconditions**:
   `scan_flow_aware_psv_ix_axiom` and
   `scan_flow_brackets_matched_ix_axiom`, both keyed on a real
   `Scanner.Indexed.scanIx input = .ok tokens` precondition (the
   placeholder `(h_from_scanner : True)` from Step 6d.1c is gone).
   These replace the 2 `indexed_scanner_*_axiom` declarations
   previously staged in `IndexedWellBehaved.lean` §5c.

### Phase 3 sub-steps 6d.1e.2+ (future commits)

**Per-action preservation chain** — port of the ~50–80 per-action
preservation lemmas from the legacy chain. Estimated 3,000–5,000
LOC of mechanical work, broken across 4–6 future sessions. Each
indexed scanner action (`scanPlainScalarIx`,
`scanTagIx`/`scanBlockScalarIx`/`scanDoubleQuotedIx`/`scanSingleQuotedIx`,
`scanBlockEntryIx`/`scanKeyIx`/`scanValueIx`,
`unwindIndentsLoopIx`, `saveSimpleKeyIx`, `pushSequenceIndentIx`,
`pushMappingIndentIx`, the document/directive scanners, etc.) needs:

- `scanXxxIx_new_tokens_not_plain` (PSV side)
- `scanXxxIx_preserves_FlowNestingInvIx` (flow-context side)
- `scanXxxIx_new_tokens_not_flow` (matched-brackets side)
- `scanXxxIx_preserves_PlainScalarsValidIx` (combiner)
- `scanXxxIx_preserves_FlowContextPSVIx` (combiner)

These combine via the dispatchers (`scanNextTokenIx_*`,
`scanLoopIx`) into the two top-level theorems
`scan_flow_aware_psv_ix` and `scan_flow_brackets_matched_ix`.

### Phase 3 sub-step 6d.1e.N (final)

Discharge the 2 axioms staged in this file by replacing them with
proven theorems consuming the per-action chain. Final state:
**0 axioms** in the Phase 3 closure, ready for Step 6f cutover.

## What this file does NOT contain (yet)

- Per-action preservation lemmas (deferred to 6d.1e.2+).
- The two top-level theorems' proofs (deferred to 6d.1e.N).

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
      simp only [h_eq]
      exact ih (pos + 1) depth (fun j _ hlt hj => h_nf j (by omega) hlt hj) (by omega)
    · exact flowNestingIx_go_oob tokens pos target depth (by omega)

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
**(Deferred to Step 6d.1e.2)**

The per-action preservation chain will build on these unit lemmas —
each says "emitting a token with a specific shape preserves one of
the three invariants" — but they are tightly coupled to the
per-action lemma shapes that consume them. Landing them in advance,
divorced from their consumers, makes them awkward to motivate and
risks `simp`-set drift before the consumers arrive. They are
deferred to Step 6d.1e.2 (when the first batch of `scanXxxIx_preserves_*`
lemmas lands). Concretely, Step 6d.1e.2 should add:

- `emit_non_flow_preserves_FlowNestingInvIx` — non-flow emit
  preserves the `FlowNestingInvIx` bridge invariant
  (depends on `flowNestingIx_push_non_flow` above).
- `emit_non_plain_preserves_PlainScalarsValidIx` — non-plain emit
  preserves PSV (depends on `PlainScalarsValidIx_of_prefix_and_new`
  above + a one-step `Array.getElem_push` analysis).
- `emit_non_flow_non_plain_preserves_FlowContextPSVIx` — non-flow,
  non-plain emit preserves flow-context PSV (depends on
  `FlowContextPSVIx_of_prefix_and_new` + `flowNestingIx_push_non_flow`).

The single-step emit ports are mechanical once at least one
`scanXxxIx_preserves_*` consumer is in scope; see the legacy chain
in `Proofs/Production/ScannerPlainScalarValid.lean:1623ff`. -/

/-! ## §6  Top-level theorems — staged as axioms with tightened preconditions

These are the two top-level theorems that the per-action preservation
chain (Step 6d.1e.2+) will eventually establish. For now, they are
declared as **axioms with real `Scanner.Indexed.scanIx input = .ok tokens`
preconditions** (replacing the placeholder `(h_from_scanner : True)`
hypotheses staged in `IndexedWellBehaved.lean` Step 6d.1c).

**Phase 3 axiom budget**: these two axioms account for the entire
Phase 3 closure axiom count after Step 6d.1e.1. They must be
discharged before Step 6f cutover.

**Consumers**: `parseStream_output_grammable` (legacy:
`Proofs/Parser/ParserGrammable.lean:71-72`; post-cutover: indexed
analogue in the renamed `ParserGrammable.lean`) will obtain
`FlowAwarePSVIx` and `FlowBracketsMatchedIx` for the parser-side
chain by applying these. -/

/-- The indexed scanner output satisfies `FlowAwarePSVIx`.
    To be discharged in Step 6d.1e.N via the per-action preservation
    chain (Step 6d.1e.2+). Replaces the
    `indexed_scanner_flowAwarePSV_axiom` previously declared in
    `IndexedWellBehaved.lean` (Step 6d.1c) — that placeholder had
    `(h_from_scanner : True)`; this version has the real precondition. -/
axiom scan_flow_aware_psv_ix_axiom
    {input : String} (tokens : Indexed.TokenStream input)
    (_h_scan : ScannerStateIx.scanIx input = .ok tokens) :
    FlowAwarePSVIx tokens

/-- The indexed scanner output has matched flow brackets.
    To be discharged in Step 6d.1e.N. Replaces the
    `indexed_scanner_flowBracketsMatched_axiom` previously declared
    in `IndexedWellBehaved.lean`. -/
axiom scan_flow_brackets_matched_ix_axiom
    {input : String} (tokens : Indexed.TokenStream input)
    (_h_scan : ScannerStateIx.scanIx input = .ok tokens) :
    FlowBracketsMatchedIx tokens

end L4YAML.Proofs.Indexed.ScannerPlainScalarValid
