/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Spec.Grammar
import L4YAML.Parser.ParseStateIx
import L4YAML.Parser.FuelIx
import L4YAML.Parser.TokenParserIx
import L4YAML.Proofs.Production.ScannerPlainScalarValid
import L4YAML.Proofs.Composition
import L4YAML.Proofs.Parser.ParserSoundness
import L4YAML.Proofs.Parser.ParserGrammableBase

/-! # `IndexedWellBehaved` — Phase 3 Step 6d.1a indexed infrastructure (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit (Guardrail 1).

## Scope of Step 6d.1a (this commit)

This file currently lands **only** the indexed supporting predicates
and `flowNestingIx.go` step lemmas — the foundational infrastructure
that the indexed `ParseNodeWB` chain (~4,797 LOC, Step 6d.1b) will
rest on:

- `flowNestingIx tokens i` — indexed twin of
  `ScannerPlainScalarValid.flowNesting` over `Array (IxToken input)`.
- `PlainScalarsValidIx tokens` — indexed twin of
  `ScannerPlainScalarValid.PlainScalarsValid`.
- `FlowContextPSVIx` / `FlowAwarePSVIx` / `FlowBracketsMatchedIx` —
  indexed twins of their legacy counterparts.
- `flowNestingIx_go_oob` / `flowNestingIx_go_step` /
  `flowNestingIx_go_ge_target` / `flowNestingIx_go_split` — indexed
  twins of the legacy `flowNesting_go_*` step lemmas required by the
  `flowNestingIx_split_step` / `_after_flow_start_eq` / `_after_flow_end`
  bridge lemmas that Step 6d.1b will port from `ParserWellBehaved.lean`.

The predicates are structurally identical to the legacy
`Array (Positioned YamlToken)` versions; the only delta is the
token-kind accessor (`Positioned.val` → `IxToken.token`).

## Scope deferred to Step 6d.1b (next session)

The full ~4,797 LOC port of `ParserWellBehaved.lean` — §5 (Scannable
C2), §5a–§5g (sub-parser well-behavedness), §5f (position
monotonicity), and the flow-loop fuel sufficiency machinery — is
deferred to Step 6d.1b. Discovery during this session: the port is
not a pure mechanical substitution because

1. `Indexed.TokenStream input` is a *wrapper* around `Array (IxToken
   input)` (see `Indexed/TokenStream.lean`), so `ParseStateIx.tokens
   : Indexed.TokenStream input` needs a `.tokens` accessor (or a
   `GetElem` instance) to bridge with the `Array (IxToken input)`
   parameters that the supporting predicates take. Legacy
   `ParseState.tokens : Array (Positioned YamlToken)` had no such
   indirection.
2. The indexed `parseNode`'s `peek?` is implemented via
   `Option.map IxToken.token ps.peekIx?` (see `Parser/ParseStateIx.lean`),
   so the `peek_some_bounded` bridge lemma needs a different proof
   shape than the legacy `unfold ParseState.peek? at h; split at h; …`
   tactic. Mechanical substitution would not have been enough.
3. The §5 C2-bridge proofs invoke `scan_flow_aware_psv` (in
   `Proofs.Production.ScannerPlainScalarValid`), which is keyed on
   `Array (Positioned YamlToken)`. The indexed C2 proofs need an
   indexed scanner producer that emits `FlowAwarePSVIx` for
   `ts.tokens : Array (IxToken input)` — this is itself a scanner-side
   port that Step 6d.1b will need to either inline-bridge or front-load.

These three structural surprises (Reflection 64) reshape the scope.
Step 6d.1a (this commit) lands the foundational infrastructure
sorry-free; Step 6d.1b will tackle the bulk port with the bridging
strategy decided.

## Phase 3 Step 6f cutover

At cutover, `IndexedWellBehaved.lean` is renamed to
`ParserWellBehaved.lean` (overwriting the legacy file), the `Indexed`
suffix on the namespace and on the supporting predicates is dropped
(`flowNestingIx` → `flowNesting`, etc.). See Blueprint Step 6f. -/

namespace L4YAML.Proofs.Indexed.WellBehaved

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition

variable {input : String}

/-! ## Indexed supporting predicates

Twins of `flowNesting`, `PlainScalarsValid`, `FlowAwarePSV`,
`FlowContextPSV`, `FlowBracketsMatched` from
`ScannerPlainScalarValid.lean`, reparented onto `Array (IxToken
input)`. The token-kind access switches from `Positioned.val` to
`IxToken.token`; everything else is structurally identical to the
legacy definitions. -/

/-- Flow nesting depth at position `i` in an indexed token array.
    Mirrors `ScannerPlainScalarValid.flowNesting` exactly, replacing
    the legacy `Positioned YamlToken` element type with `IxToken input`
    and the `.val` token-kind accessor with `.token`. -/
def flowNestingIx (tokens : Array (IxToken input)) (i : Nat) : Nat :=
  go tokens 0 i 0
where
  go (tokens : Array (IxToken input)) (pos target depth : Nat) : Nat :=
    if pos ≥ target then depth
    else if h : pos < tokens.size then
      let depth' := match (tokens[pos]'h).token with
        | .flowSequenceStart | .flowMappingStart => depth + 1
        | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
        | _ => depth
      go tokens (pos + 1) target depth'
    else depth
  termination_by target - pos

/-- Every plain scalar token in an indexed token array satisfies
    `ScalarScannable _ false`. Indexed twin of
    `ScannerPlainScalarValid.PlainScalarsValid`. -/
def PlainScalarsValidIx (tokens : Array (IxToken input)) : Prop :=
  ∀ i (hi : i < tokens.size),
    match (tokens[i]'hi).token with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True

/-- Plain scalars at flow-nesting positions satisfy `ScalarScannable _ true`. -/
def FlowContextPSVIx (tokens : Array (IxToken input)) : Prop :=
  ∀ i (hi : i < tokens.size),
    flowNestingIx tokens i > 0 →
    match (tokens[i]'hi).token with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ true
    | _ => True

/-- Flow-aware extension of `PlainScalarsValidIx`. -/
def FlowAwarePSVIx (tokens : Array (IxToken input)) : Prop :=
  PlainScalarsValidIx tokens ∧ FlowContextPSVIx tokens

/-- All flow brackets are matched in the indexed token array. -/
def FlowBracketsMatchedIx (tokens : Array (IxToken input)) : Prop :=
  flowNestingIx tokens tokens.size = 0

/-! ### Indexed `flowNestingIx.go` step lemmas

Mechanical ports of `ScannerPlainScalarValid.flowNesting_go_oob` /
`_step` / `_ge_target` / `_split`. These four are the algebraic step
lemmas the §5a `flowNestingIx_split_step` / `_pos_after_flow_start` /
`_after_flow_start_eq` / `_after_flow_end` / `_non_flow_step` /
`_beyond_size` bridge lemmas — to be ported in Step 6d.1b — depend
on. Pre-landing them here keeps Step 6d.1b focused on the C2-chain
substitution rather than on the underlying algebraic facts. -/

theorem flowNestingIx_go_oob (tokens : Array (IxToken input))
    (pos target depth : Nat) (h : pos ≥ tokens.size) :
    flowNestingIx.go tokens pos target depth = depth := by
  generalize hk : target - pos = k
  induction k generalizing pos with
  | zero =>
    unfold flowNestingIx.go; simp [show pos ≥ target by omega]
  | succ k _ =>
    unfold flowNestingIx.go
    simp only [show ¬(pos ≥ target) by omega, ite_false,
      show ¬(pos < tokens.size) by omega, dite_false]

theorem flowNestingIx_go_step
    (tokens : Array (IxToken input))
    (pos target depth : Nat) (h_pos : pos < tokens.size) (h_tgt : pos < target) :
    flowNestingIx.go tokens pos target depth =
    flowNestingIx.go tokens (pos + 1) target
      (match (tokens[pos]'h_pos).token with
       | .flowSequenceStart | .flowMappingStart => depth + 1
       | .flowSequenceEnd | .flowMappingEnd => if depth > 0 then depth - 1 else 0
       | _ => depth) := by
  conv => lhs; unfold flowNestingIx.go
          simp only [eq_false (show ¬(pos ≥ target) by omega), ite_false,
            eq_true h_pos, dite_true]

theorem flowNestingIx_go_ge_target (tokens : Array (IxToken input))
    (pos target depth : Nat) (h : pos ≥ target) :
    flowNestingIx.go tokens pos target depth = depth := by
  unfold flowNestingIx.go; simp [h]

theorem flowNestingIx_go_split
    (tokens : Array (IxToken input))
    (pos mid target depth : Nat) (h1 : pos ≤ mid) (h2 : mid ≤ target) :
    flowNestingIx.go tokens pos target depth =
    flowNestingIx.go tokens mid target (flowNestingIx.go tokens pos mid depth) := by
  generalize hn : mid - pos = n
  induction n generalizing pos depth with
  | zero =>
    have : pos = mid := by omega
    subst this
    have h_inner : flowNestingIx.go tokens pos pos depth = depth := by
      unfold flowNestingIx.go; simp
    rw [h_inner]
  | succ n ih =>
    have h_lt_mid : pos < mid := by omega
    by_cases h_pos : pos < tokens.size
    · rw [flowNestingIx_go_step tokens pos target depth h_pos (by omega)]
      rw [flowNestingIx_go_step tokens pos mid depth h_pos (by omega)]
      exact ih (pos + 1) _ (by omega) (by omega)
    · simp only [flowNestingIx_go_oob tokens pos target depth (by omega),
                  flowNestingIx_go_oob tokens pos mid depth (by omega),
                  flowNestingIx_go_oob tokens mid target depth (by omega)]

end L4YAML.Proofs.Indexed.WellBehaved
