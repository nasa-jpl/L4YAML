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
private abbrev emitBlockEndPop {input : String} (s : ScannerStateIx input) :
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
private abbrev twoPlaceholderEmits {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  (s.emit YamlToken.placeholder).emit YamlToken.placeholder

/-- `saveSimpleKeyIx` either leaves tokens unchanged or pushes two
    placeholder tokens. Eliminates the if-chain in `saveSimpleKeyIx`
    so downstream proofs case-split on this disjunction rather than
    unfolding the body. -/
private theorem saveSimpleKeyIx_tokens_cases {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).tokens = s.tokens ∨
    (saveSimpleKeyIx s).tokens = (twoPlaceholderEmits s).tokens := by
  unfold saveSimpleKeyIx
  split
  · left; rfl
  · split
    · right; rfl
    · left; rfl

private theorem saveSimpleKeyIx_flowLevel_eq {input : String} (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).flowLevel = s.flowLevel := by
  unfold saveSimpleKeyIx
  split
  · rfl
  · split <;> rfl

/-- Two-emit prefix preservation, factored out for the `saveSimpleKeyIx`
    two-emit branch. -/
private theorem twoPlaceholderEmits_preserves_prefix {input : String}
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
private theorem twoPlaceholderEmits_new_not_plain {input : String}
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

private theorem twoPlaceholderEmits_new_not_flow {input : String}
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

axiom scanAnchorOrAliasIx_adds_one_token {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (_h_ok : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.tokens.size = s.tokens.size + 1

axiom scanAnchorOrAliasIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (i : Nat) (hi : i < s.tokens.size) :
    s'.tokens[i]'(by
      rw [scanAnchorOrAliasIx_adds_one_token s isAnchor s' h_ok]
      exact Nat.lt_succ_of_lt hi) = s.tokens[i]'hi

axiom scanAnchorOrAliasIx_preserves_flowLevel {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (_h_ok : scanAnchorOrAliasIx s isAnchor = .ok s') :
    s'.flowLevel = s.flowLevel

axiom scanAnchorOrAliasIx_new_token_not_plain {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (_h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    match (s'.tokens[s.tokens.size]'hj).token with
    | .scalar _ .plain => False
    | _ => True

axiom scanAnchorOrAliasIx_new_token_not_flow {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (_h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceEnd ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingEnd

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

axiom scanAnchorOrAliasIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (isAnchor : Bool) (s' : ScannerStateIx input)
    (_h_ok : scanAnchorOrAliasIx s isAnchor = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §7c  `scanTagIx` preservation — staged as axioms (Step 6d.1e.3)

Same staging rationale as §7b: `scanTagIx s` has three success
branches all emitting `.tag _ _` tokens; the proof shape is the
legacy `scanTag_psv_match` adapted with `change`/`show` bridging,
but the same record-update opacity wall (Reflection 70) prevents
clean Lean 4 ports without additional structural lemmas. Discharged
in a dedicated 6d.1e.3b or as part of 6d.1e.7. -/

axiom scanTagIx_adds_one_token {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (_h_ok : scanTagIx s = .ok s') :
    s'.tokens.size = s.tokens.size + 1

axiom scanTagIx_preserves_prefix {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (h_ok : scanTagIx s = .ok s')
    (i : Nat) (hi : i < s.tokens.size) :
    s'.tokens[i]'(by
      rw [scanTagIx_adds_one_token s s' h_ok]
      exact Nat.lt_succ_of_lt hi) = s.tokens[i]'hi

axiom scanTagIx_preserves_flowLevel {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (_h_ok : scanTagIx s = .ok s') :
    s'.flowLevel = s.flowLevel

axiom scanTagIx_new_token_not_plain {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (_h_ok : scanTagIx s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    match (s'.tokens[s.tokens.size]'hj).token with
    | .scalar _ .plain => False
    | _ => True

axiom scanTagIx_new_token_not_flow {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (_h_ok : scanTagIx s = .ok s')
    (hj : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingStart ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowSequenceEnd ∧
    (s'.tokens[s.tokens.size]'hj).token ≠ .flowMappingEnd

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

axiom scanTagIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (s' : ScannerStateIx input)
    (_h_ok : scanTagIx s = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'


/-! ## §8  Top-level theorems — staged as axioms with tightened preconditions

These are the two top-level theorems that the per-action preservation
chain (Step 6d.1e.3+) will eventually establish. For now, they are
declared as **axioms with real `Scanner.Indexed.scanIx input = .ok tokens`
preconditions** (replacing the placeholder `(h_from_scanner : True)`
hypotheses staged in `IndexedWellBehaved.lean` Step 6d.1c).

**Phase 3 axiom budget**: these two axioms account for the entire
Phase 3 closure axiom count after Step 6d.1e.3. They must be
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
