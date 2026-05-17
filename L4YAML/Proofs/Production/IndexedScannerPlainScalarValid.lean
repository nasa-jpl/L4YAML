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

/-- `overwriteAtCursor` with a non-plain token preserves
    `PlainScalarsValidIx`. -/
theorem overwriteAtCursor_non_plain_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (i : Nat) (sk : IxCursor input)
    (tok : YamlToken) (h_old : PlainScalarsValidIx s.tokens)
    (h_np : match tok with | .scalar _ .plain => False | _ => True) :
    PlainScalarsValidIx (s.overwriteAtCursor i sk tok).tokens := by
  show PlainScalarsValidIx (s.tokens.setIfInBounds i _)
  exact PlainScalarsValidIx_setIfInBounds_non_plain s.tokens h_old i _ h_np

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
      simp only [pure_bind] at h_ok
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
    simp only [pure_bind] at h_ok
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
      simp only [pure_bind] at h_ok
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
    simp only [pure_bind] at h_ok
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
      simp only [pure_bind] at h_ok
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
    simp only [pure_bind] at h_ok
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
    · simp only [pure_bind, Except.ok.injEq] at h_ok
      subst h_ok
      show PlainScalarsValidIx
        { ((pushMappingIndentIx s s.cursor.pos.col).emit .key).advance with .. }.tokens
      simp only [advance_tokens]
      have h_step1 := pushMappingIndentIx_preserves_PlainScalarsValidIx
        s s.cursor.pos.col h_old
      exact emit_non_plain_preserves_PlainScalarsValidIx
        (pushMappingIndentIx s s.cursor.pos.col) .key h_step1 (by trivial)
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h_ok
    simp only [pure_bind, Except.ok.injEq] at h_ok
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
    · simp only [pure_bind, Except.ok.injEq] at h_ok
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
    simp only [pure_bind, Except.ok.injEq] at h_ok
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
    · simp only [pure_bind, Except.ok.injEq] at h_ok
      subst h_ok
      have h_step1 := pushMappingIndentIx_preserves_FlowNestingInvIx
        s s.cursor.pos.col h_fni
      have h_step2 := emit_non_flow_preserves_FlowNestingInvIx
        (pushMappingIndentIx s s.cursor.pos.col) .key h_step1
        (by decide) (by decide) (by decide) (by decide)
      unfold FlowNestingInvIx at h_step2 ⊢
      simpa using h_step2
  · simp only [if_neg hi, advance_inFlow, emit_inFlow] at h_ok
    simp only [pure_bind, Except.ok.injEq] at h_ok
    subst h_ok
    have h_step1 := emit_non_flow_preserves_FlowNestingInvIx s .key h_fni
      (by decide) (by decide) (by decide) (by decide)
    unfold FlowNestingInvIx at h_step1 ⊢
    simpa using h_step1

/-! ### §8e  `scanValuePrepareIx` preservation — PSV proven, FCPSV/FNI staged

`scanValuePrepareIx s` either (a) overwrites token slots
`simpleKey.tokenIndex` and `simpleKey.tokenIndex + 1` with non-plain
non-flow tokens (`.blockMappingStart`, `.key`), (b) leaves tokens
unchanged (record-only updates), or (c) delegates to
`pushMappingIndentIx`.

PSV preservation is proven via §8a (`setIfInBounds` non-plain) +
§6e (`pushMappingIndentIx_preserves_PlainScalarsValidIx`).

FCPSV / FlowNestingInv preservation needs an additional invariant
the indexed proof chain has not yet propagated: the original token
at `simpleKey.tokenIndex` (resp. `+1`) must be non-flow. The legacy
chain establishes this via tracking `.placeholder` slots from
`saveSimpleKey`; the indexed analogue would require strengthening the
scanner-side invariant (e.g. carrying `SimpleKeyAbove`-style
side-conditions through the dispatcher chain).

Staged as **two axioms** with the eventual real signature; discharge
moves to a dedicated session (6d.1e.7 or earlier) alongside §7b/§7c
and §8e′. See Reflection 71 for the design analysis. -/

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

/-- `scanValuePrepareIx` preserves `FlowContextPSVIx`.
    **Staged as axiom (Step 6d.1e.4)**: the `setIfInBounds` branches
    need the original token at `simpleKey.tokenIndex` to be non-flow;
    establishing this requires a placeholder-tracking invariant the
    indexed chain has not yet propagated. See Reflection 71. -/
axiom scanValuePrepareIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanValuePrepareIx s).tokens

/-- `scanValuePrepareIx` preserves `FlowNestingInvIx`.
    **Staged as axiom (Step 6d.1e.4)** — see
    `scanValuePrepareIx_preserves_FlowContextPSVIx`. -/
axiom scanValuePrepareIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanValuePrepareIx s)

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

theorem scanValueIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanValueIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
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
      have h_prep := scanValuePrepareIx_preserves_FlowContextPSVIx
        (scanValueClearKeyIx s) h_ck
      exact emit_non_flow_non_plain_preserves_FlowContextPSVIx
        (scanValuePrepareIx (scanValueClearKeyIx s)) .value h_prep
        (by trivial) (by decide) (by decide) (by decide) (by decide)

theorem scanValueIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanValueIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
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
      have h_prep := scanValuePrepareIx_preserves_FlowNestingInvIx
        (scanValueClearKeyIx s) h_ck
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
    (h_old : FlowContextPSVIx s.tokens) :
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
          exact scanValueIx_preserves_FlowContextPSVIx s _ (by assumption) h_old
      · simp at h_ok

theorem scanNextTokenIx_dispatchBlockIndicators_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchBlockIndicators s c = .ok (some s'))
    (h_fni : FlowNestingInvIx s) :
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
          exact scanValueIx_preserves_FlowNestingInvIx s _ (by assumption) h_fni
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

`scanFlowEntryIx s = .ok { ((scanValuePrepareIx s).emit .flowEntry).advance
  with simpleKeyAllowed := true }`. Composes §8e (`scanValuePrepareIx`,
PSV proven + FCPSV / FNI staged) with §5 (`emit_non_*` for `.flowEntry`).
`.flowEntry` is non-plain and non-flow-bracket, so the §5 building
blocks apply directly. -/

theorem scanFlowEntryIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanFlowEntryIx s = .ok s')
    (h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens := by
  unfold scanFlowEntryIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  show PlainScalarsValidIx
    { ((scanValuePrepareIx s).emit .flowEntry).advance with simpleKeyAllowed := true }.tokens
  simp only [advance_tokens]
  have h_prep := scanValuePrepareIx_preserves_PlainScalarsValidIx s h_old
  exact emit_non_plain_preserves_PlainScalarsValidIx
    (scanValuePrepareIx s) .flowEntry h_prep (by trivial)

theorem scanFlowEntryIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanFlowEntryIx s = .ok s')
    (h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens := by
  unfold scanFlowEntryIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  show FlowContextPSVIx
    { ((scanValuePrepareIx s).emit .flowEntry).advance with simpleKeyAllowed := true }.tokens
  simp only [advance_tokens]
  have h_prep := scanValuePrepareIx_preserves_FlowContextPSVIx s h_old
  exact emit_non_flow_non_plain_preserves_FlowContextPSVIx
    (scanValuePrepareIx s) .flowEntry h_prep
    (by trivial) (by decide) (by decide) (by decide) (by decide)

theorem scanFlowEntryIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (h_ok : scanFlowEntryIx s = .ok s')
    (h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s' := by
  unfold scanFlowEntryIx at h_ok
  simp only [Except.ok.injEq] at h_ok
  subst h_ok
  have h_prep := scanValuePrepareIx_preserves_FlowNestingInvIx s h_fni
  have h_emit := emit_non_flow_preserves_FlowNestingInvIx
    (scanValuePrepareIx s) .flowEntry h_prep
    (by decide) (by decide) (by decide) (by decide)
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
    (h_old : FlowContextPSVIx s.tokens) :
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
                  (by assumption) h_old
          · cases h_ok

theorem scanNextTokenIx_dispatchFlowIndicators_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (h_ok : scanNextTokenIx_dispatchFlowIndicators s c = .ok (some s'))
    (h_fni : FlowNestingInvIx s) :
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
                  (by assumption) h_fni
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

/-! ### §11a  `scanDocumentStartIx` preservation — staged as axioms

Per Reflection 70 staging. Outer record update on `simpleKeyAllowed`,
`allowDirectives`, `seenYamlDirective`, `directivesPresent`,
`documentEverStarted`, `definedAnchors` blocks `rfl`/`simp`
reductions; `unwindIndentsIx_preserves_flowLevel` is a theorem
(not a defeq). Discharge in 6d.1e.7. -/

axiom scanDocumentStartIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx (scanDocumentStartIx s).tokens

axiom scanDocumentStartIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx (scanDocumentStartIx s).tokens

axiom scanDocumentStartIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx (scanDocumentStartIx s)

/-! ### §11b  `scanDocumentEndIx` preservation — staged as axioms

Same Reflection 70 staging; the trailing-content match adds branches
but does not affect the preservation argument. -/

axiom scanDocumentEndIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (_h_de : scanDocumentEndIx s = .ok s')
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens

axiom scanDocumentEndIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (_h_de : scanDocumentEndIx s = .ok s')
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens

axiom scanDocumentEndIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (_h_de : scanDocumentEndIx s = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §11c  `scanYamlDirectiveIx` preservation — staged as axioms -/

axiom scanYamlDirectiveIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (_h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens

axiom scanYamlDirectiveIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (_h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens

axiom scanYamlDirectiveIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (_h_ok : scanYamlDirectiveIx s cAfterWS startPos hStart = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §11d  `scanTagDirectiveIx` preservation — staged as axioms -/

axiom scanTagDirectiveIx_preserves_PlainScalarsValidIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (_h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens

axiom scanTagDirectiveIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (_h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens

axiom scanTagDirectiveIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) (s' : ScannerStateIx input)
    (_h_ok : scanTagDirectiveIx s cAfterWS startPos hStart = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §11e  `scanDirectiveIx` preservation — staged as axioms

`let`-binding wall (Reflection 73). Discharge in 6d.1e.7 alongside
§11c/§11d via case-split. -/

axiom scanDirectiveIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (_h_ok : scanDirectiveIx s = .ok s')
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens

axiom scanDirectiveIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (_h_ok : scanDirectiveIx s = .ok s')
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens

axiom scanDirectiveIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (_h_ok : scanDirectiveIx s = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §11f  `scanNextTokenIx_dispatchStructural` preservation —
staged as axioms (`let`-binding wall) -/

axiom scanNextTokenIx_dispatchStructural_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (_h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens

axiom scanNextTokenIx_dispatchStructural_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (_h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens

axiom scanNextTokenIx_dispatchStructural_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (_h_ok : scanNextTokenIx_dispatchStructural s c = .ok (some s'))
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §11g  `scanNextTokenIx_preprocess` preservation — staged as axioms -/

axiom scanNextTokenIx_preprocess_preserves_PlainScalarsValidIx
    {input : String} (s s1 : ScannerStateIx input) (c : Char)
    (_h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s1.tokens

axiom scanNextTokenIx_preprocess_preserves_FlowContextPSVIx
    {input : String} (s s1 : ScannerStateIx input) (c : Char)
    (_h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s1.tokens

axiom scanNextTokenIx_preprocess_preserves_FlowNestingInvIx
    {input : String} (s s1 : ScannerStateIx input) (c : Char)
    (_h_ok : scanNextTokenIx_preprocess s = .ok (some (s1, c)))
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s1

/-! ### §11h  `scanNextTokenIx_dispatchContent` preservation — staged as
axioms (Reflection 72 — plain-scalar arm requires Layer F.4) -/

axiom scanNextTokenIx_dispatchContent_preserves_PlainScalarsValidIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (_h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (_h_old : PlainScalarsValidIx s.tokens) :
    PlainScalarsValidIx s'.tokens

axiom scanNextTokenIx_dispatchContent_preserves_FlowContextPSVIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (_h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (_h_old : FlowContextPSVIx s.tokens) :
    FlowContextPSVIx s'.tokens

axiom scanNextTokenIx_dispatchContent_preserves_FlowNestingInvIx
    {input : String} (s : ScannerStateIx input) (c : Char)
    (s' : ScannerStateIx input)
    (_h_ok : scanNextTokenIx_dispatchContent s c = .ok s')
    (_h_fni : FlowNestingInvIx s) :
    FlowNestingInvIx s'

/-! ### §11i  `scanNextTokenIx` preservation — staged as axioms

Top-level composition over preprocess + dispatchStructural +
dispatchFlowIndicators + dispatchBlockIndicators + dispatchContent
+ `allowDirectives`/`checkBlockFlowIndent` record updates. Staged
because the case-split + variable-rename pattern over the
`.ok (some (s2, c))` pair-destructure hits the `obtain ⟨⟩`
over-destructuring wall in Lean 4. Discharge in 6d.1e.7. -/

axiom scanNextTokenIx_preserves_PlainScalarsValidIx {input : String}
    (s s' : ScannerStateIx input) (_h_old : PlainScalarsValidIx s.tokens)
    (_h_ok : scanNextTokenIx s = .ok (some s')) :
    PlainScalarsValidIx s'.tokens

axiom scanNextTokenIx_preserves_FlowContextPSVIx {input : String}
    (s s' : ScannerStateIx input) (_h_old : FlowContextPSVIx s.tokens)
    (_h_ok : scanNextTokenIx s = .ok (some s')) :
    FlowContextPSVIx s'.tokens

axiom scanNextTokenIx_preserves_FlowNestingInvIx {input : String}
    (s s' : ScannerStateIx input) (_h_fni : FlowNestingInvIx s)
    (_h_ok : scanNextTokenIx s = .ok (some s')) :
    FlowNestingInvIx s'

/-! ### §11j  `scanLoopIx_preserves_*` — real theorems via structural
induction on `fuel`, with a final-emit `.streamEnd` step preservation
lemma chained on top of §11i's `scanNextTokenIx_preserves_*` axioms.

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

theorem scanLoopIx_preserves_FlowContextPSVIx {input : String}
    (s : ScannerStateIx input) (fuel : Nat)
    (tokens : Indexed.TokenStream input)
    (h_old : FlowContextPSVIx s.tokens)
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
        (scanNextTokenIx_preserves_FlowContextPSVIx s s' h_old h_snt)
        h_ok

theorem scanLoopIx_preserves_FlowNestingInvIx {input : String}
    (s : ScannerStateIx input) (fuel : Nat)
    (tokens : Indexed.TokenStream input)
    (h_fni : FlowNestingInvIx s)
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
        (scanNextTokenIx_preserves_FlowNestingInvIx s s' h_fni h_snt)
        h_ok

end L4YAML.Proofs.Indexed.ScannerPlainScalarValid
