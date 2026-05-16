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

/-! # `IndexedWellBehaved` — Phase 3 Step 6d.1b indexed infrastructure (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit (Guardrail 1).

## Scope of Step 6d.1b (this commit)

This commit extends the Step 6d.1a infrastructure with the
loosely-coupled, pre-mutual-block sections of `ParserWellBehaved.lean`,
ported to the indexed substrate:

- **Foundation switchover** — supporting predicates
  (`flowNestingIx`, `PlainScalarsValidIx`, `FlowContextPSVIx`,
  `FlowAwarePSVIx`, `FlowBracketsMatchedIx`) reparented from
  `Array (IxToken input)` onto `Indexed.TokenStream input`. The
  `GetElem` instance on `TokenStream` (in `Indexed/TokenStream.lean`)
  lets `tokens[i]'h` continue to work uniformly.
- **§5 C2 Infrastructure** — `ScalarScannable_strengthen` (verbatim
  port — `Scalar`-only), `scalar_from_token_scannable_ix`,
  `scalar_from_flow_token_scannable_ix`, `empty_scalar_scannable`
  (verbatim — purely `YamlValue`-typed), and `peek_some_bounded_ix`
  (new proof shape — indexed `peek?` factors through `peekIx?`).
- **§5a flowNesting position step lemmas** —
  `flowNestingIx_split_step`, `_pos_after_flow_start`,
  `_after_flow_start_eq`, `_after_flow_end`, `_non_flow_step`,
  `_beyond_size` — characterize how `flowNestingIx` evolves under
  single-token advances. The proofs are mechanical re-targets of
  legacy lemmas at lines 189–251 of `ParserWellBehaved.lean`.
- **§5b Scannable monotonicity** — `Scannable_true_implies_false`,
  `Scannable_any_implies_false`. Verbatim ports (purely `YamlValue`-
  typed, no token-shape dependency).
- **§5d Scannable for tag/anchor modification** —
  `Scannable_attach_props`. Verbatim port (purely `YamlValue`-typed).
- **§5d′ applyNodeFinalization preservation** —
  `applyNodeFinalization_scannable`, `_tokens`, `_pos`,
  `_trackPositions`. Re-targeted onto indexed `applyNodeFinalization`
  (in `Parser/ParseStateIx.lean`).
- **§5e′ parseNodeProperties preservation** —
  `parseNodeProperties_tokens_ix`, `_flowNesting_ix`, plus the
  helper `advance_preserves_flowNestingIx`,
  `advance2_preserves_flowNestingIx` and the local-simp lemma
  `advance_tokens_eq_ix`. Uses a verbatim port of the
  legacy `unfold_loop_at` elaborator that unrolls the
  `for _ in [:2]` loop in `parseNodeProperties`.

## Scope deferred to Step 6d.1c (next session)

The **§5e mutual `ParseNodeWB` block** (~600 LOC) and **§5e″
sub-parser well-behavedness** (~1,500 LOC), the **§5e₂ token-array
preservation helpers** (~100 LOC), **§5f parseDocument scannability**
(~150 LOC), **§5g parseStream output scannability** (~150 LOC), and
the **§5f position monotonicity chain** (~1,500 LOC) are deferred to
Step 6d.1c. The mutual block is the structural core: porting it
requires a careful indexed `ParseNodeWB` predicate (matching the
indexed `parseNode`'s mutual definition shape in
`Parser/TokenParserIx.lean`) and 11 mutually-recursive sub-parser
well-behavedness theorems.

§5c (`scanFiltered_flow_aware_psv`) is also deferred — it bridges to
the scanner-side `scan_flow_aware_psv` which is keyed on the legacy
`Array (Positioned YamlToken)`. The indexed analogue needs either an
indexed scanner producer or a bridge lemma; this is a Phase 3 sub-task
of its own.

## Phase 3 Step 6f cutover

At cutover, `IndexedWellBehaved.lean` is renamed to
`ParserWellBehaved.lean` (overwriting the legacy file), the `Indexed`
suffix on the namespace and on the supporting predicates is dropped
(`flowNestingIx` → `flowNesting`, etc.), and the staging-prefixed
declarations (`peek_some_bounded_ix`, `advance_preserves_flowNestingIx`,
…) drop their `_ix` suffix. See Blueprint Step 6f. -/

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
`ScannerPlainScalarValid.lean`, reparented onto
`Indexed.TokenStream input`. The token-kind access switches from
`Positioned.val` to `IxToken.token`; structurally identical to the
legacy definitions modulo the wrapping `TokenStream` container.

The `GetElem (TokenStream input) Nat (IxToken input)` instance (in
`Indexed/TokenStream.lean`) lets `tokens[i]'h` resolve uniformly,
so the predicate bodies match the legacy bodies modulo `.val` →
`.token`. -/

/-- Flow nesting depth at position `i` in an indexed token stream.
    Mirrors `ScannerPlainScalarValid.flowNesting` exactly, replacing
    the legacy `Positioned YamlToken` element type with `IxToken input`
    and the `.val` token-kind accessor with `.token`. The internal
    helper `go` works on the underlying `Array (IxToken input)` to
    keep the algebraic step lemmas (`flowNestingIx_go_*`) simple. -/
def flowNestingIx (tokens : Indexed.TokenStream input) (i : Nat) : Nat :=
  go tokens.tokens 0 i 0
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

/-- Every plain scalar token in an indexed token stream satisfies
    `ScalarScannable _ false`. Indexed twin of
    `ScannerPlainScalarValid.PlainScalarsValid`. -/
def PlainScalarsValidIx (tokens : Indexed.TokenStream input) : Prop :=
  ∀ i (hi : i < tokens.size),
    match (tokens[i]'hi).token with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ false
    | _ => True

/-- Plain scalars at flow-nesting positions satisfy `ScalarScannable _ true`. -/
def FlowContextPSVIx (tokens : Indexed.TokenStream input) : Prop :=
  ∀ i (hi : i < tokens.size),
    flowNestingIx tokens i > 0 →
    match (tokens[i]'hi).token with
    | .scalar content .plain =>
        ScalarScannable ⟨content, .plain, none, none, none⟩ true
    | _ => True

/-- Flow-aware extension of `PlainScalarsValidIx`. -/
def FlowAwarePSVIx (tokens : Indexed.TokenStream input) : Prop :=
  PlainScalarsValidIx tokens ∧ FlowContextPSVIx tokens

/-- All flow brackets are matched in the indexed token stream. -/
def FlowBracketsMatchedIx (tokens : Indexed.TokenStream input) : Prop :=
  flowNestingIx tokens tokens.size = 0

/-! ### Indexed `flowNestingIx.go` step lemmas

Mechanical ports of `ScannerPlainScalarValid.flowNesting_go_oob` /
`_step` / `_ge_target` / `_split`. These four are the algebraic step
lemmas the §5a bridge lemmas depend on. They operate on the
underlying `Array (IxToken input)`, not on `TokenStream input`, so
the §5a bridge lemmas pass `tokens.tokens` to access them. -/

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

/-! ## §5  Parser Output is `Scannable` (C2) — Indexed

The indexed analogue of §5 in `ParserWellBehaved.lean`. The
docstring on §5 in the legacy file documents the C2 gap analysis;
that analysis carries over verbatim to the indexed substrate.

### C2 Infrastructure -/

/-- Strengthen `ScalarScannable _ false` to `_ true` given the two
    additional flow-context properties. Verbatim from
    `ParserWellBehaved.ScalarScannable_strengthen` — `Scalar` is not
    indexed by `input`. -/
theorem ScalarScannable_strengthen (s : Scalar)
    (h : ScalarScannable s false)
    (h_vpf : s.style = .plain → s.content.length > 0 →
      validPlainFirstProp s.content true)
    (h_nfi : s.style = .plain → s.content.length > 0 →
      noFlowIndicatorsProp s.content) :
    ScalarScannable s true := by
  intro hplain hlen
  have ⟨_, h2, h3, _⟩ := h hplain hlen
  exact ⟨h_vpf hplain hlen, h2, h3, fun _ => h_nfi hplain hlen⟩

/-! ### C2 Bridge Lemmas — Indexed -/

/-- A scalar `YamlValue` constructed from an indexed token satisfying
    `PlainScalarsValidIx` is `Scannable` at block context. Indexed twin
    of legacy `scalar_from_token_scannable`. -/
theorem scalar_from_token_scannable_ix
    (tokens : Indexed.TokenStream input)
    (h_psv : PlainScalarsValidIx tokens)
    (i : Nat) (hi : i < tokens.size)
    (content : String) (style : ScalarStyle)
    (h_tok : (tokens[i]'hi).token = .scalar content style)
    (tag anchor : Option String) :
    Scannable (.scalar ⟨content, style, tag, anchor, none⟩) false := by
  apply Scannable.scalar
  intro hplain hlen
  have h_match := h_psv i hi
  rw [h_tok] at h_match
  cases style with
  | plain => exact h_match hplain hlen
  | _ => contradiction

/-- A scalar from an indexed flow-context token satisfying
    `FlowAwarePSVIx` is `Scannable` at any flow context. Indexed twin
    of legacy `scalar_from_flow_token_scannable`. -/
theorem scalar_from_flow_token_scannable_ix
    (tokens : Indexed.TokenStream input)
    (h_fpsv : FlowAwarePSVIx tokens)
    (i : Nat) (hi : i < tokens.size)
    (content : String) (style : ScalarStyle)
    (h_tok : (tokens[i]'hi).token = .scalar content style)
    (h_flow : flowNestingIx tokens i > 0)
    (tag anchor : Option String) (inFlow : Bool) :
    Scannable (.scalar ⟨content, style, tag, anchor, none⟩) inFlow := by
  apply Scannable.scalar
  intro hplain hlen
  cases inFlow with
  | false =>
    have h_match := h_fpsv.1 i hi
    rw [h_tok] at h_match
    cases style with
    | plain => exact h_match hplain hlen
    | _ => contradiction
  | true =>
    have h_match := h_fpsv.2 i hi h_flow
    rw [h_tok] at h_match
    cases style with
    | plain => exact h_match hplain hlen
    | _ => contradiction

/-- Empty content scalar is trivially `Scannable` at any flow context.
    Verbatim port — no token dependency. -/
theorem empty_scalar_scannable (tag anchor : Option String) (inFlow : Bool) :
    Scannable (.scalar ⟨"", .plain, tag, anchor, none⟩) inFlow := by
  apply Scannable.scalar; intro _ hlen; simp at hlen

/-- When `peek? ps = some tok`, `ps.pos` is in bounds and the bounded
    access `(ps.tokens[ps.pos]'h).token` equals `tok`. Indexed twin of
    legacy `peek_some_bounded`.

    The legacy proof unfolds `ParseState.peek?` (which is
    `tokens[pos]?.map (·.val)`) and applies `getElem!_pos`. The indexed
    `peek?` factors through `peekIx?` and `TokenStream.get?`, so the
    proof unfolds two more layers before reaching the underlying
    `Array.get?`. -/
theorem peek_some_bounded_ix (ps : ParseStateIx input) (tok : YamlToken)
    (h : ps.peek? = some tok) :
    ps.pos < ps.tokens.size ∧
    ∀ (h_lt : ps.pos < ps.tokens.size), (ps.tokens[ps.pos]'h_lt).token = tok := by
  unfold ParseStateIx.peek? ParseStateIx.peekIx? Indexed.TokenStream.get? at h
  simp only [Option.map_eq_some_iff] at h
  obtain ⟨t, h_get, h_eq⟩ := h
  have h_lt : ps.pos < ps.tokens.size := by
    have := Array.getElem?_eq_some_iff.mp h_get
    exact this.1
  refine ⟨h_lt, ?_⟩
  intro h_lt'
  have h_eq2 : ps.tokens.tokens[ps.pos]? = some t := h_get
  rw [Array.getElem?_eq_getElem h_lt'] at h_eq2
  simp only [Option.some.injEq] at h_eq2
  -- h_eq2 : ps.tokens.tokens[ps.pos] = t
  -- h_eq : t.token = tok
  show (ps.tokens.tokens[ps.pos]'h_lt').token = tok
  rw [h_eq2]; exact h_eq

/-! ### §5a  flowNesting position step lemmas — Indexed

`flowNestingIx tokens i` counts unmatched flow-start tokens before
position `i`. These lemmas characterize how `flowNestingIx` changes
when advancing one token. Indexed twins of legacy
`flowNesting_split_step` / `_pos_after_flow_start` / `_after_flow_start_eq` /
`_after_flow_end` / `_non_flow_step` / `_beyond_size`. -/

/-- `flowNestingIx tokens (i+1)` factors as go-step from
    `flowNestingIx tokens i`. -/
theorem flowNestingIx_split_step (tokens : Indexed.TokenStream input)
    (i : Nat) (_hi : i < tokens.size) :
    flowNestingIx tokens (i + 1) =
    flowNestingIx.go tokens.tokens i (i + 1) (flowNestingIx tokens i) := by
  show flowNestingIx.go tokens.tokens 0 (i + 1) 0 =
    flowNestingIx.go tokens.tokens i (i + 1) (flowNestingIx.go tokens.tokens 0 i 0)
  exact flowNestingIx_go_split tokens.tokens 0 i (i + 1) 0 (by omega) (by omega)

/-- After consuming a flow-start token, `flowNestingIx` is positive. -/
theorem flowNestingIx_pos_after_flow_start (tokens : Indexed.TokenStream input)
    (i : Nat) (hi : i < tokens.size)
    (h : (tokens[i]'hi).token = .flowSequenceStart ∨
         (tokens[i]'hi).token = .flowMappingStart) :
    flowNestingIx tokens (i + 1) > 0 := by
  have hi' : i < tokens.tokens.size := hi
  -- Normalize h to use the underlying Array's getElem (same as goal after rw chain).
  have h_bridge : (tokens[i]'hi) = (tokens.tokens[i]'hi') :=
    Indexed.TokenStream.getElem_eq_tokens_getElem tokens i hi
  rw [flowNestingIx_split_step tokens i hi,
      flowNestingIx_go_step tokens.tokens i (i + 1) _ hi' (by omega),
      flowNestingIx_go_ge_target tokens.tokens (i + 1) (i + 1) _ (by omega)]
  rw [h_bridge] at h
  rcases h with h | h <;> simp [h] <;> omega

/-- After consuming a flow-start token, `flowNestingIx` increases by exactly 1. -/
theorem flowNestingIx_after_flow_start_eq (tokens : Indexed.TokenStream input)
    (i : Nat) (hi : i < tokens.size)
    (h : (tokens[i]'hi).token = .flowSequenceStart ∨
         (tokens[i]'hi).token = .flowMappingStart) :
    flowNestingIx tokens (i + 1) = flowNestingIx tokens i + 1 := by
  have hi' : i < tokens.tokens.size := hi
  have h_bridge : (tokens[i]'hi) = (tokens.tokens[i]'hi') :=
    Indexed.TokenStream.getElem_eq_tokens_getElem tokens i hi
  rw [flowNestingIx_split_step tokens i hi,
      flowNestingIx_go_step tokens.tokens i (i + 1) _ hi' (by omega),
      flowNestingIx_go_ge_target tokens.tokens (i + 1) (i + 1) _ (by omega)]
  rw [h_bridge] at h
  rcases h with h | h <;> simp [h]

/-- After consuming a flow-end token, `flowNestingIx` decreases by 1 (saturating). -/
theorem flowNestingIx_after_flow_end (tokens : Indexed.TokenStream input)
    (i : Nat) (hi : i < tokens.size)
    (h : (tokens[i]'hi).token = .flowSequenceEnd ∨
         (tokens[i]'hi).token = .flowMappingEnd)
    (h_pos : flowNestingIx tokens i > 0) :
    flowNestingIx tokens (i + 1) = flowNestingIx tokens i - 1 := by
  have hi' : i < tokens.tokens.size := hi
  have h_bridge : (tokens[i]'hi) = (tokens.tokens[i]'hi') :=
    Indexed.TokenStream.getElem_eq_tokens_getElem tokens i hi
  rw [flowNestingIx_split_step tokens i hi,
      flowNestingIx_go_step tokens.tokens i (i + 1) _ hi' (by omega),
      flowNestingIx_go_ge_target tokens.tokens (i + 1) (i + 1) _ (by omega)]
  rw [h_bridge] at h
  rcases h with h | h <;> simp [h, h_pos]

/-- Advancing past a non-flow-boundary token preserves `flowNestingIx`. -/
theorem flowNestingIx_non_flow_step (tokens : Indexed.TokenStream input)
    (i : Nat) (hi : i < tokens.size)
    (h1 : (tokens[i]'hi).token ≠ .flowSequenceStart)
    (h2 : (tokens[i]'hi).token ≠ .flowMappingStart)
    (h3 : (tokens[i]'hi).token ≠ .flowSequenceEnd)
    (h4 : (tokens[i]'hi).token ≠ .flowMappingEnd) :
    flowNestingIx tokens (i + 1) = flowNestingIx tokens i := by
  have hi' : i < tokens.tokens.size := hi
  have h_bridge : (tokens[i]'hi) = (tokens.tokens[i]'hi') :=
    Indexed.TokenStream.getElem_eq_tokens_getElem tokens i hi
  rw [flowNestingIx_split_step tokens i hi,
      flowNestingIx_go_step tokens.tokens i (i + 1) _ hi' (by omega),
      flowNestingIx_go_ge_target tokens.tokens (i + 1) (i + 1) _ (by omega)]
  rw [h_bridge] at h1 h2 h3 h4
  generalize (tokens.tokens[i]'hi').token = tok at *
  cases tok <;> simp_all

/-- `flowNestingIx` is constant for positions `≥ tokens.size`. -/
theorem flowNestingIx_beyond_size (tokens : Indexed.TokenStream input)
    (i : Nat) (hi : i ≥ tokens.size) :
    flowNestingIx tokens (i + 1) = flowNestingIx tokens i := by
  have hi' : i ≥ tokens.tokens.size := hi
  show flowNestingIx.go tokens.tokens 0 (i + 1) 0 = flowNestingIx.go tokens.tokens 0 i 0
  rw [flowNestingIx_go_split tokens.tokens 0 i (i + 1) 0 (by omega) (by omega)]
  rw [flowNestingIx_go_oob tokens.tokens i (i + 1) (flowNestingIx.go tokens.tokens 0 i 0) hi']

/-! ### §5b  Scannable monotonicity — Indexed

`Scannable v true → Scannable v false`. Verbatim ports — these
lemmas are purely on `YamlValue` and `Scannable`; no token-shape
dependency. -/

/-- Flow-context scannability implies block-context scannability. -/
theorem Scannable_true_implies_false :
    (v : YamlValue) → Scannable v true → Scannable v false
  | .scalar s, .scalar _ _ h_ss =>
    .scalar s false (ScalarScannable_true_implies_false s h_ss)
  | .alias name, .alias _ _ =>
    .alias name false
  | .sequence .flow items tag anchor, .sequence _ _ _ _ _ h_items =>
    .sequence .flow items tag anchor false h_items
  | .sequence .block items tag anchor, .sequence _ _ _ _ _ h_items =>
    .sequence .block items tag anchor false fun i =>
      Scannable_true_implies_false items[i] (h_items i)
  | .mapping .flow pairs tag anchor, .mapping _ _ _ _ _ hk hv =>
    .mapping .flow pairs tag anchor false hk hv
  | .mapping .block pairs tag anchor, .mapping _ _ _ _ _ hk hv =>
    .mapping .block pairs tag anchor false
      (fun i => Scannable_true_implies_false pairs[i].1 (hk i))
      (fun i => Scannable_true_implies_false pairs[i].2 (hv i))
termination_by v => sizeOf v
decreasing_by
  all_goals simp_wf
  all_goals
    first
    | omega
    | (have := L4YAML.Proofs.ParserSoundness.array_sizeOf_getElem_lt items i.val i.isLt; omega)
    | (have h1 := L4YAML.Proofs.ParserSoundness.array_sizeOf_getElem_lt pairs i.val i.isLt
       have h2 := L4YAML.Proofs.ParserSoundness.prod_fst_sizeOf_lt (pairs[i.val])
       omega)
    | (have h1 := L4YAML.Proofs.ParserSoundness.array_sizeOf_getElem_lt pairs i.val i.isLt
       have h2 := L4YAML.Proofs.ParserSoundness.prod_snd_sizeOf_lt (pairs[i.val])
       omega)

/-- `Scannable` at any `inFlow` implies `Scannable` at `false`. -/
theorem Scannable_any_implies_false (v : YamlValue) (b : Bool) :
    Scannable v b → Scannable v false := by
  cases b with
  | false => exact id
  | true => exact Scannable_true_implies_false v

/-! ### §5d  Scannable for tag/anchor modification — Indexed

Adding or changing `tag`/`anchor` fields preserves `Scannable`. Verbatim
port — purely on `YamlValue`. -/

/-- Attaching properties (tag, anchor) to a collection preserves `Scannable`. -/
theorem Scannable_attach_props (val : YamlValue) (inFlow : Bool)
    (tag : Option String) (anchor : Option String)
    (h : Scannable val inFlow) :
    Scannable (match val with
      | .sequence style items none none => .sequence style items tag anchor
      | .mapping style pairs none none => .mapping style pairs tag anchor
      | other => other) inFlow := by
  match val, h with
  | .scalar _, h => exact h
  | .alias _, h => exact h
  | .sequence _ _ (.some _) _, h => exact h
  | .sequence _ _ none (.some _), h => exact h
  | .sequence style items none none, .sequence _ _ _ _ _ h_items =>
    exact .sequence style items tag anchor inFlow h_items
  | .mapping _ _ (.some _) _, h => exact h
  | .mapping _ _ none (.some _), h => exact h
  | .mapping style pairs none none, .mapping _ _ _ _ _ hk hv =>
    exact .mapping style pairs tag anchor inFlow hk hv

/-! ### §5d′  applyNodeFinalization preserves Scannable — Indexed

`applyNodeFinalization` (in `Parser/ParseStateIx.lean`) is the pure
tail of `parseNode` after content dispatch. It applies tag/anchor
properties, registers the anchor, and records G5c position. None of
these operations affect `val`'s scannability or the token stream. -/

/-- The value produced by `applyNodeFinalization` is `Scannable` whenever
    the raw content value is `Scannable`. Indexed twin of legacy
    `applyNodeFinalization_scannable`. -/
theorem applyNodeFinalization_scannable_ix
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) (inFlow : Bool)
    (h : Scannable val inFlow) :
    Scannable (applyNodeFinalization val ps props nodeStartPos).1 inFlow := by
  match val, h with
  | .scalar _, h => simp [applyNodeFinalization]; exact h
  | .alias _, h => simp [applyNodeFinalization]; exact h
  | .sequence _ _ (.some _) _, h => simp [applyNodeFinalization]; exact h
  | .sequence _ _ none (.some _), h => simp [applyNodeFinalization]; exact h
  | .sequence style items none none, .sequence _ _ _ _ _ h_items =>
    simp [applyNodeFinalization]
    exact .sequence style items props.tag props.anchor inFlow h_items
  | .mapping _ _ (.some _) _, h => simp [applyNodeFinalization]; exact h
  | .mapping _ _ none (.some _), h => simp [applyNodeFinalization]; exact h
  | .mapping style pairs none none, .mapping _ _ _ _ _ hk hv =>
    simp [applyNodeFinalization]
    exact .mapping style pairs props.tag props.anchor inFlow hk hv

/-- `applyNodeFinalization` does not modify the token stream. -/
theorem applyNodeFinalization_tokens_ix
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.tokens = ps.tokens := by
  simp only [applyNodeFinalization, ParseStateIx.addAnchor]
  split <;> simp_all
  all_goals (split <;> simp_all)

/-- `applyNodeFinalization` preserves the parse position. -/
theorem applyNodeFinalization_pos_ix
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.pos = ps.pos := by
  simp only [applyNodeFinalization, ParseStateIx.addAnchor]
  split <;> simp_all
  all_goals (split <;> simp_all)

/-- `applyNodeFinalization` preserves `trackPositions`. -/
theorem applyNodeFinalization_trackPositions_ix
    (val : YamlValue) (ps : ParseStateIx input) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.trackPositions = ps.trackPositions := by
  simp only [applyNodeFinalization, ParseStateIx.addAnchor]
  split <;> simp_all
  all_goals (split <;> simp_all)

/-! ### §5e′  parseNodeProperties preservation lemmas — Indexed

Indexed twins of legacy `parseNodeProperties_tokens` and
`parseNodeProperties_flowNesting`. The `unfold_loop_at` elaborator
unrolls the `for _ in [:2]` loop in `parseNodeProperties`; verbatim
port from `ParserWellBehaved.lean` lines 396–422. -/

-- Custom tactic: unfold all `*.loop*` constants in a hypothesis.
-- Used to unroll `for _ in [:n]` loops in Except-monad proofs.
open Lean Lean.Meta Lean.Elab.Tactic in
elab "unfold_loop_at_ix" h:ident : tactic => do
  let mvarId ← getMainGoal
  mvarId.withContext do
    let fvarId ← getFVarId h
    let ldecl ← fvarId.getDecl
    let ty := ldecl.type
    let namesRef ← IO.mkRef (∅ : NameSet)
    let _ ← Lean.Meta.transform ty (pre := fun e => do
      let fn := e.getAppFn
      if fn.isConst then
        let name := fn.constName!
        let leaf := if name.isStr then name.getString! else ""
        let parentLeaf := if name.getPrefix.isStr then name.getPrefix.getString! else ""
        if leaf == "loop" || parentLeaf == "loop" then
          namesRef.modify (·.insert name)
      return .continue)
    let names ← namesRef.get
    if names.isEmpty then throwError "no loop constants found"
    let mut currentTy := ty
    for name in names do
      let result ← Lean.Meta.unfold currentTy name
      currentTy := result.expr
    if ty == currentTy then throwError "no change"
    let mvarId ← mvarId.replaceLocalDeclDefEq fvarId currentTy
    replaceMainGoal [mvarId]

/-- `ps.advance` does not change the token stream. File-local @[simp].
    Defined here rather than in `Parser/ParseStateIx.lean` to mirror the
    legacy `ParserWellBehaved.ParseState.advance_tokens` placement.
    File-local name (`WB.` prefix) to avoid collision with the
    `L4YAML.TokenParser.Indexed.ParseStateIx` structure namespace. -/
@[simp] theorem advance_tokens_eq_ix (ps : ParseStateIx input) :
    ps.advance.tokens = ps.tokens := rfl

-- `parseNodeProperties` preserves the token stream. Indexed twin of
-- legacy `parseNodeProperties_tokens`.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
set_option linter.unusedSimpArgs false in
theorem parseNodeProperties_tokens_ix
    (ps : ParseStateIx input) (props : NodeProperties) (ps' : ParseStateIx input)
    (h : parseNodeProperties ps = .ok (props, ps')) :
    ps'.tokens = ps.tokens := by
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at_ix h
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  split at h
  · contradiction
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_hfst, rfl⟩ := h
    rename_i heq
    split at heq
    · contradiction
    · rename_i v heq_first
      cases v with
      | done x =>
        simp (config := { iota := true }) only [] at heq
        simp only [Except.ok.injEq] at heq; subst heq
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (try contradiction)
        all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq] at heq_first)
        all_goals (try cases heq_first)
        all_goals (try subst heq_first)
        all_goals (first | rfl | simp [advance_tokens_eq_ix])
      | yield x =>
        simp (config := { iota := true }) only [] at heq
        split at heq
        · contradiction
        · rename_i v2 heq_second
          cases v2 with
          | done y =>
            simp (config := { iota := true }) only [] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (first | rfl | simp [advance_tokens_eq_ix])
          | yield y =>
            simp only [dite_false] at heq
            simp only [Except.ok.injEq] at heq
            subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (first | rfl | simp [advance_tokens_eq_ix])

/-- Advancing past a non-flow-boundary token preserves `flowNestingIx`.
    Indexed twin of legacy `advance_preserves_flowNesting`. -/
theorem advance_preserves_flowNestingIx
    (tokens : Indexed.TokenStream input) (ps : ParseStateIx input) {tok : YamlToken}
    (h_peek : ps.peek? = some tok) (h_eq : ps.tokens = tokens)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos := by
  have ⟨h_lt, h_val⟩ := peek_some_bounded_ix ps tok h_peek
  simp only [ParseStateIx.advance]
  subst h_eq
  exact flowNestingIx_non_flow_step ps.tokens ps.pos h_lt
    (by rw [h_val h_lt]; exact h1) (by rw [h_val h_lt]; exact h2)
    (by rw [h_val h_lt]; exact h3) (by rw [h_val h_lt]; exact h4)

/-- Advancing past two non-flow-boundary tokens preserves `flowNestingIx`.
    Indexed twin of legacy `advance2_preserves_flowNesting`. -/
theorem advance2_preserves_flowNestingIx
    (tokens : Indexed.TokenStream input) (ps : ParseStateIx input)
    {tok1 tok2 : YamlToken}
    (h_peek1 : ps.peek? = some tok1) (h_peek2 : ps.advance.peek? = some tok2)
    (h_eq : ps.tokens = tokens)
    (h1a : tok1 ≠ .flowSequenceStart) (h1b : tok1 ≠ .flowMappingStart)
    (h1c : tok1 ≠ .flowSequenceEnd) (h1d : tok1 ≠ .flowMappingEnd)
    (h2a : tok2 ≠ .flowSequenceStart) (h2b : tok2 ≠ .flowMappingStart)
    (h2c : tok2 ≠ .flowSequenceEnd) (h2d : tok2 ≠ .flowMappingEnd) :
    flowNestingIx tokens ps.advance.advance.pos = flowNestingIx tokens ps.pos := by
  have h_eq' : ps.advance.tokens = tokens := by
    simp [advance_tokens_eq_ix]; exact h_eq
  calc flowNestingIx tokens ps.advance.advance.pos
      = flowNestingIx tokens ps.advance.pos :=
        advance_preserves_flowNestingIx tokens ps.advance h_peek2 h_eq' h2a h2b h2c h2d
    _ = flowNestingIx tokens ps.pos :=
        advance_preserves_flowNestingIx tokens ps h_peek1 h_eq h1a h1b h1c h1d

-- `parseNodeProperties` preserves flow nesting — anchor/tag tokens are
-- non-flow. Indexed twin of legacy `parseNodeProperties_flowNesting`.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
set_option linter.unusedSimpArgs false in
theorem parseNodeProperties_flowNesting_ix
    (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input) (props : NodeProperties) (ps' : ParseStateIx input)
    (h : parseNodeProperties ps = .ok (props, ps'))
    (h_eq : ps.tokens = tokens) :
    flowNestingIx tokens ps'.pos = flowNestingIx tokens ps.pos := by
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at_ix h
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  split at h
  · contradiction
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_hfst, rfl⟩ := h
    rename_i heq
    split at heq
    · contradiction
    · rename_i v heq_first
      cases v with
      | done x =>
        simp (config := { iota := true }) only [] at heq
        simp only [Except.ok.injEq] at heq; subst heq
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (try contradiction)
        all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq] at heq_first)
        all_goals (try cases heq_first)
        all_goals (try subst heq_first)
        all_goals rfl
      | yield x =>
        simp (config := { iota := true }) only [] at heq
        split at heq
        · contradiction
        · rename_i v2 heq_second
          cases v2 with
          | done y =>
            simp (config := { iota := true }) only [] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (apply advance_preserves_flowNestingIx <;> first | assumption | rfl | (intro h; cases h))
          | yield y =>
            simp only [dite_false] at heq
            simp only [Except.ok.injEq] at heq
            subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (apply advance2_preserves_flowNestingIx <;> first | assumption | rfl | exact h_eq | (intro h; cases h))

/-! ### §5e″ tryConsume preservation helpers — Indexed

`tryConsume` either advances past a matched token or leaves the state
unchanged. Both branches preserve the token stream; the advancing
branch preserves `flowNestingIx` when the matched token is not a
flow-bracket. These are the workhorse helpers used throughout §5e″.

The `_with_path_*` variants thread through the
`{ ps with currentPath := … }` struct update that the parser uses to
push the node path before delegating to a sub-parser. They reduce to
the un-pathed forms because `currentPath` doesn't affect `peek?` or
`advance`. -/

/-- `tryConsume` preserves the token stream. -/
theorem tryConsume_tokens_ix (ps : ParseStateIx input) (tok : YamlToken) :
    (ps.tryConsume tok).2.tokens = ps.tokens := by
  unfold ParseStateIx.tryConsume
  split
  · split
    · simp [advance_tokens_eq_ix]
    · rfl
  · rfl

/-- `tryConsume` preserves `flowNestingIx` for non-flow-bracket tokens. -/
theorem tryConsume_flowNesting_ix (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input) (tok : YamlToken)
    (h_eq : ps.tokens = tokens)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    flowNestingIx tokens (ps.tryConsume tok).2.pos = flowNestingIx tokens ps.pos := by
  unfold ParseStateIx.tryConsume
  split
  · rename_i t h_peek
    split
    · have h_teq : t = tok := eq_of_beq (by assumption)
      subst h_teq
      exact advance_preserves_flowNestingIx tokens ps h_peek h_eq h1 h2 h3 h4
    · rfl
  · rfl

/-- `tryConsume` on a currentPath-modified state preserves the original
    state's tokens (currentPath is independent of `peek?`/`advance`). -/
theorem tryConsume_with_path_tokens_ix (ps : ParseStateIx input)
    (p : YamlPath) (tok : YamlToken) :
    ({ ps with currentPath := p }.tryConsume tok).2.tokens = ps.tokens := by
  unfold ParseStateIx.tryConsume
  split
  · split <;> simp [advance_tokens_eq_ix]
  · rfl

/-- `tryConsume` on a currentPath-modified state preserves `flowNestingIx`. -/
theorem tryConsume_with_path_fn_ix (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input) (p : YamlPath) (tok : YamlToken)
    (h_eq : ps.tokens = tokens)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    flowNestingIx tokens ({ ps with currentPath := p }.tryConsume tok).2.pos =
    flowNestingIx tokens ps.pos :=
  tryConsume_flowNesting_ix tokens { ps with currentPath := p } tok h_eq h1 h2 h3 h4

/-! ### §5e₂  Helper lemmas: token-stream preservation through sub-operations — Indexed

`tryConsume`, `parseDirectives`, and `parseNode` all preserve the token
stream. These facts are used by `parseDocument_tokens_preserved_ix`. -/

/-- `parseDirectives` preserves the token stream. -/
theorem parseDirectives_tokens_ix (ps : ParseStateIx input) :
    (parseDirectives ps).2.tokens = ps.tokens := by
  unfold parseDirectives
  simp only [Id.run]
  generalize ps.tokens.size - ps.pos = fuel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
             Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize List.range' 0 fuel 1 = ls
  suffices h : ∀ (acc : MProd (Array Directive) (ParseStateIx input)),
      acc.2.tokens = ps.tokens →
      (Id.run (do
          let r ← @forIn Id (List Nat) Nat _ _ ls acc (fun _ r =>
            match r.snd.peek? with
            | some (.versionDirective major minor) => do
              pure PUnit.unit
              pure (ForInStep.yield (MProd.mk (r.fst.push (.yaml (toString major ++ "." ++ toString minor))) r.snd.advance))
            | some (.tagDirective handle tagPrefix) => do
              pure PUnit.unit
              pure (ForInStep.yield (MProd.mk (r.fst.push (.tag handle tagPrefix)) r.snd.advance))
            | _ => pure (ForInStep.done (MProd.mk r.fst r.snd)))
          pure (r.fst, r.snd))).snd.tokens = ps.tokens by
    exact h (MProd.mk #[] ps) rfl
  intro acc h_inv
  induction ls generalizing acc with
  | nil =>
    simp only [Id.run, List.forIn'_nil, ForIn.forIn, bind, pure]
    exact h_inv
  | cons _ xs ih =>
    simp only [ForIn.forIn, List.forIn'_cons, Id.run, bind, pure] at ih ⊢
    split
    · rename_i _ heq
      revert heq; split
      · intro heq; contradiction
      · intro heq; contradiction
      · intro heq
        have := ForInStep.done.inj heq
        subst this; exact h_inv
    · rename_i _ heq
      apply ih; revert heq; split
      · intro heq
        have := ForInStep.yield.inj heq
        subst this; simp [advance_tokens_eq_ix, h_inv]
      · intro heq
        have := ForInStep.yield.inj heq
        subst this; simp [advance_tokens_eq_ix, h_inv]
      · intro heq; contradiction

/-! ## §5e  Parser scannability — mutual induction — Indexed

Indexed `ParseNodeWB` is the conjunctive well-behavedness property for
`parseNode`, parameterised by the token stream and an upper fuel bound.
The 4 conjuncts are:

1. block-context scannability (always),
2. flow-context scannability (when `flowNestingIx tokens ps.pos > 0`),
3. flowNesting preservation,
4. token stream preservation.

The strong induction in `parseNode_wb_all_ix` peels fuel one step at a
time and uses the IH for every recursive call inside the parseNode
mutual block. -/

/-- Conjunctive well-behavedness property for `parseNode` at fuel `≤ n`. -/
def ParseNodeWBIx (tokens : Indexed.TokenStream input) (n : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat) (val : YamlValue) (ps' : ParseStateIx input),
    m ≤ n →
    ps.tokens = tokens →
    parseNode ps m = .ok (val, ps') →
    (Scannable val false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable val true) ∧
    (flowNestingIx tokens ps'.pos = flowNestingIx tokens ps.pos) ∧
    (ps'.tokens = tokens)

/-- Application variant of `ParseNodeWBIx` that accepts a non-destructured
    pair (matching how `split at h_ok` produces `parseNode` hypotheses). -/
theorem parseNodeWBIx_apply {tokens : Indexed.TokenStream input} {n : Nat}
    (h_ih : ParseNodeWBIx tokens n)
    {ps : ParseStateIx input} {m : Nat} {v : YamlValue × ParseStateIx input}
    (h_tok : ps.tokens = tokens)
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n := by omega) :
    (Scannable v.1 false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable v.1 true) ∧
    (flowNestingIx tokens v.2.pos = flowNestingIx tokens ps.pos) ∧
    (v.2.tokens = tokens) :=
  h_ih ps m v.1 v.2 h_le h_tok h_ok

/-- Single-projection extractor for the block-context Scannable conjunct. -/
theorem parseNode_scannable_false_ix {tokens : Indexed.TokenStream input} {n : Nat}
    (h_ih : ParseNodeWBIx tokens n)
    {ps : ParseStateIx input} {m : Nat} {v : YamlValue × ParseStateIx input}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    Scannable v.1 false :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).1

/-- Single-projection extractor for the flow-context Scannable conjunct. -/
theorem parseNode_scannable_true_ix {tokens : Indexed.TokenStream input} {n : Nat}
    (h_ih : ParseNodeWBIx tokens n)
    {ps : ParseStateIx input} {m : Nat} {v : YamlValue × ParseStateIx input}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    flowNestingIx tokens ps.pos > 0 → Scannable v.1 true :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).2.1

/-- Single-projection extractor for the flowNesting preservation conjunct. -/
theorem parseNode_flowNesting_ix {tokens : Indexed.TokenStream input} {n : Nat}
    (h_ih : ParseNodeWBIx tokens n)
    {ps : ParseStateIx input} {m : Nat} {v : YamlValue × ParseStateIx input}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    flowNestingIx tokens v.2.pos = flowNestingIx tokens ps.pos :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).2.2.1

/-- Single-projection extractor for the token preservation conjunct. -/
theorem parseNode_tokens_ix {tokens : Indexed.TokenStream input} {n : Nat}
    (h_ih : ParseNodeWBIx tokens n)
    {ps : ParseStateIx input} {m : Nat} {v : YamlValue × ParseStateIx input}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    v.2.tokens = tokens :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).2.2.2

/-! ### §5e″  Sub-parser well-behavedness (fuel-inductive hypotheses) — Indexed

Indexed twins of the legacy §5e″ block. Each sub-parser theorem
assumes `ParseNodeWBIx tokens n` (the induction hypothesis from
`parseNode_wb_all_ix`) and concludes well-behavedness for the
sub-parser. The proofs are verbatim ports modulo the
state-type substitutions:

- `Array (Positioned YamlToken)` → `Indexed.TokenStream input`
- `ParseState` → `ParseStateIx input`
- `flowNesting` → `flowNestingIx`
- `FlowAwarePSV` → `FlowAwarePSVIx`
- `FlowBracketsMatched` → `FlowBracketsMatchedIx`
- `advance_preserves_flowNesting` → `advance_preserves_flowNestingIx`
- `peek_some_bounded` → `peek_some_bounded_ix`
- `tryConsume_*` → `tryConsume_*_ix`
- `parseNodeProperties_tokens` → `parseNodeProperties_tokens_ix`
- `parseNodeProperties_flowNesting` → `parseNodeProperties_flowNesting_ix`
- `applyNodeFinalization_*` → `applyNodeFinalization_*_ix`
- `parseNodeWB_apply` → `parseNodeWBIx_apply`
- `parseNodeContent_wb` → `parseNodeContent_wb_ix`
- per-sub-parser `_wb` → `_wb_ix`
- `parseDirectives_tokens` → `parseDirectives_tokens_ix` -/

/-- Helper: pushing a Scannable value onto an all-Scannable array
    preserves the all-Scannable property. Verbatim port. -/
theorem push_all_scannable {items : Array YamlValue} {x : YamlValue}
    {inFlow : Bool}
    (h_items : ∀ i : Fin items.size, Scannable items[i] inFlow)
    (h_x : Scannable x inFlow) :
    ∀ i : Fin (items.push x).size, Scannable (items.push x)[i] inFlow := by
  intro ⟨i, hi⟩
  show Scannable (items.push x)[i] inFlow
  rw [Array.getElem_push]
  split
  · exact h_items ⟨i, by assumption⟩
  · exact h_x

/-- Helper: pushing a pair onto an all-Scannable pair array preserves the
    Scannable property for both projections. Verbatim port. -/
theorem push_pair_scannable {pairs : Array (YamlValue × YamlValue)}
    {kv : YamlValue × YamlValue} {inFlow : Bool}
    (h_pairs : ∀ i : Fin pairs.size, Scannable pairs[i].1 inFlow ∧ Scannable pairs[i].2 inFlow)
    (h_kv : Scannable kv.1 inFlow ∧ Scannable kv.2 inFlow) :
    ∀ i : Fin (pairs.push kv).size,
      Scannable (pairs.push kv)[i].1 inFlow ∧ Scannable (pairs.push kv)[i].2 inFlow := by
  intro ⟨i, hi⟩
  constructor
  · show Scannable (pairs.push kv)[i].1 inFlow
    rw [Array.getElem_push]; split
    · exact (h_pairs ⟨i, by assumption⟩).1
    · exact h_kv.1
  · show Scannable (pairs.push kv)[i].2 inFlow
    rw [Array.getElem_push]; split
    · exact (h_pairs ⟨i, by assumption⟩).2
    · exact h_kv.2

/-- Loop invariant for `parseBlockSequenceLoop`: accumulated items remain
    Scannable, flowNesting is preserved, and tokens unchanged. -/
theorem parseBlockSequenceLoop_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (_h_fpsv : FlowAwarePSVIx tokens)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (items : Array YamlValue)
    (result : Array YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_items_false : ∀ i : Fin items.size, Scannable items[i] false)
    (h_items_true : flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin items.size, Scannable items[i] true)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok result) :
    (∀ i : Fin result.1.size, Scannable result.1[i] false) ∧
    (flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin result.1.size, Scannable result.1[i] true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    exact ⟨h_items_false, h_items_true, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next h_peek =>
      have h_adv_tok : ps.advance.tokens = tokens := by
        simp [advance_tokens_eq_ix, h_eq]
      have h_fn : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
        advance_preserves_flowNestingIx tokens ps h_peek h_eq
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      split at h_ok
      all_goals try
        have h_wb := ih_fuel (by omega) ps.advance (items.push emptyNode)
            h_adv_tok
            (push_all_scannable h_items_false (empty_scalar_scannable none none false))
            (fun h_flow => push_all_scannable
              (h_items_true (by rw [← h_fn]; exact h_flow))
              (empty_scalar_scannable none none true))
            h_ok
        refine ⟨h_wb.1,
               fun h_flow => h_wb.2.1 (by rw [h_fn]; exact h_flow),
               ?_, h_wb.2.2.2⟩
        exact h_wb.2.2.1.trans h_fn
      next =>
        split at h_ok
        next => simp at h_ok
        next pn_result heq_pn =>
          obtain ⟨val, ps₃⟩ := pn_result
          dsimp only [] at h_ok
          have h_ps2_tok : ({ ps.advance with
              currentPath := ps.advance.currentPath.push
                (.index items.size) } : ParseStateIx input).tokens = tokens := by
            simp [advance_tokens_eq_ix, h_eq]
          have h_node := h_ih _ k val ps₃ (by omega) h_ps2_tok heq_pn
          have h_ps3_fn : flowNestingIx tokens ps₃.pos =
              flowNestingIx tokens ps.advance.pos := by
            have := h_node.2.2.1; simp at this; exact this
          have h_ps3_tok : ps₃.tokens = tokens := h_node.2.2.2
          have h_push_f := push_all_scannable h_items_false h_node.1
          have h_push_t : flowNestingIx tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseStateIx input).pos > 0 →
              ∀ i : Fin (items.push val).size,
              Scannable (items.push val)[i] true := by
            intro h_flow_ps4
            simp only [] at h_flow_ps4
            have h_flow_adv : flowNestingIx tokens ps.advance.pos > 0 := by
              rw [← h_ps3_fn]; exact h_flow_ps4
            have h_flow_ps : flowNestingIx tokens ps.pos > 0 := by
              rw [← h_fn]; exact h_flow_adv
            exact push_all_scannable (h_items_true h_flow_ps)
              (h_node.2.1 h_flow_adv)
          have h_ps4_tok : ({ ps₃ with currentPath :=
              ps.advance.currentPath } : ParseStateIx input).tokens = tokens := by
            simp [h_ps3_tok]
          have h_wb := ih_fuel (by omega)
              ({ ps₃ with currentPath := ps.advance.currentPath } : ParseStateIx input)
              (items.push val) h_ps4_tok h_push_f h_push_t h_ok
          have h_ps4_fn : flowNestingIx tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseStateIx input).pos =
              flowNestingIx tokens ps.pos := by
            simp only []; rw [h_ps3_fn, h_fn]
          refine ⟨h_wb.1,
                 fun h_flow => h_wb.2.1 (by rw [h_ps4_fn]; exact h_flow),
                 ?_, h_wb.2.2.2⟩
          exact h_wb.2.2.1.trans h_ps4_fn
    next =>
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact ⟨h_items_false, h_items_true, rfl, h_eq⟩

/-- `parseBlockSequence` well-behaved given parseNode IH. -/
theorem parseBlockSequence_wb_ix (tokens : Indexed.TokenStream input)
    (fuel : Nat) (h_fpsv : FlowAwarePSVIx tokens) (h_ih : ParseNodeWBIx tokens fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .blockSequenceStart)
    (h_ok : parseBlockSequence ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_fn_adv : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
    advance_preserves_flowNestingIx tokens ps h_peek h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_result heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_adv_tok : ps.advance.tokens = tokens := by
        simp [advance_tokens_eq_ix, h_eq]
      have h_empty_f : ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : flowNestingIx tokens ps.advance.pos > 0 →
          ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] true := by
        intro _ ⟨_, hi⟩; simp at hi
      have h_loop := parseBlockSequenceLoop_wb_ix tokens (k + 1) k (by omega)
          h_fpsv h_ih ps.advance #[] (items_arr, ps_loop) h_adv_tok
          h_empty_f h_empty_t heq_loop
      have h_loop_fn : flowNestingIx tokens ps_loop.pos =
          flowNestingIx tokens ps.advance.pos := h_loop.2.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2.2
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      constructor
      · exact Scannable.sequence .block items_arr none none false h_loop.1
      constructor
      · intro h_flow
        exact Scannable.sequence .block items_arr none none true
          (fun i => h_loop.2.1 (by rw [h_fn_adv]; exact h_flow) i)
      constructor
      · simp only []
        split
        · rename_i h_peek_end
          have h_fn_end := advance_preserves_flowNestingIx tokens ps_loop
              h_peek_end h_loop_tok
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          exact h_fn_end.trans (h_loop_fn.trans h_fn_adv)
        · exact h_loop_fn.trans h_fn_adv
      · simp only []
        split
        · simp only [advance_tokens_eq_ix]; exact h_loop.2.2.2
        · exact h_loop.2.2.2

/-- Well-behavedness of `parseBlockMappingEntryValue`. -/
theorem parseBlockMappingEntryValue_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (keyHasContent : Bool) (keyLine keyCol : Nat)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok result) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  have h_tc_tok : (ps.tryConsume .value).2.tokens = tokens :=
    (tryConsume_tokens_ix ps .value).trans h_eq
  have h_tc_fn : flowNestingIx tokens (ps.tryConsume .value).2.pos = flowNestingIx tokens ps.pos :=
    tryConsume_flowNesting_ix tokens ps .value h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  split at h_ok
  · -- consumed = true: peel through valueLine match + for-loop + content match
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- emptyNode cases first (preferred over parseNode application)
    all_goals (try (
      obtain ⟨rfl, rfl⟩ := h_ok
      exact ⟨empty_scalar_scannable none none false,
             fun _ => empty_scalar_scannable none none true,
             h_tc_fn, h_tc_tok⟩))
    -- parseNode cases — h_ok : parseNode ps' fuel = .ok result
    all_goals (
      have h_wb := parseNodeWBIx_apply h_ih h_tc_tok h_ok (by omega)
      exact ⟨h_wb.1, fun h_flow => h_wb.2.1 (h_tc_fn ▸ h_flow),
             h_wb.2.2.1.trans h_tc_fn, h_wb.2.2.2⟩)
  · obtain ⟨rfl, rfl⟩ := h_ok
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h_tc_fn, h_tc_tok⟩

/-- Alias for `parseBlockMappingEntryValue_wb_ix` (used by
    `handleBlockMappingKeyEntry_wb_ix`). -/
theorem bevWBIx (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    {ps : ParseStateIx input} {kc : Bool} {kl kcol : Nat}
    {result : YamlValue × ParseStateIx input}
    (h_ok : parseBlockMappingEntryValue ps fuel kc kl kcol = .ok result)
    (h_eq : ps.tokens = tokens) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens :=
  parseBlockMappingEntryValue_wb_ix tokens n fuel h_fuel h_ih
      ps kc kl kcol result h_eq h_ok

/-- Well-behavedness of the `.key` branch entry handler. -/
theorem handleBlockMappingKeyEntry_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (pairIdx : Nat)
    (result : YamlValue × YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .key)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok result) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    Scannable result.2.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.2.1 true) ∧
    flowNestingIx tokens result.2.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.2.tokens = tokens := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_adv_tok : ps.advance.tokens = tokens := by
    simp [advance_tokens_eq_ix, h_eq]
  have h_adv_fn : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
    advance_preserves_flowNestingIx tokens ps h_peek h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  split at h_ok <;> first | contradiction | skip
  all_goals (try (simp only [emptyNode] at h_ok))
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (rw [← h_ok])
  all_goals (try (dsimp only [Prod.fst, Prod.snd]))
  -- emptyNode key goals
  all_goals (try (
    have h_bev := by
      apply bevWBIx tokens n fuel h_fuel h_ih
      · assumption
      · exact h_adv_tok
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h_bev.1,
           fun h_flow => h_bev.2.1 (Eq.mpr (congrArg (· > 0) h_adv_fn) h_flow),
           h_bev.2.2.1.trans h_adv_fn,
           h_bev.2.2.2⟩))
  -- parseNode key goals
  all_goals (
    have h_key_wb := parseNodeWBIx_apply h_ih h_adv_tok (by assumption) (by omega)
    have h_k_tok := h_key_wb.2.2.2
    have h_k_fn := h_key_wb.2.2.1
    have h_bev := by
      apply bevWBIx tokens n fuel h_fuel h_ih
      · assumption
      · exact h_k_tok
    exact ⟨h_key_wb.1,
           fun h_flow => h_key_wb.2.1 (h_adv_fn ▸ h_flow),
           h_bev.1,
           fun h_flow => h_bev.2.1
             (Eq.mpr (congrArg (· > 0) (h_k_fn.trans h_adv_fn)) h_flow),
           h_bev.2.2.1.trans (h_k_fn.trans h_adv_fn),
           h_bev.2.2.2⟩)

/-- Well-behavedness of the `.value` branch entry handler (implicit key). -/
theorem handleBlockMappingValueEntry_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (pairIdx : Nat)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .value)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok result) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_adv_tok : ps.advance.tokens = tokens := by
    simp [advance_tokens_eq_ix, h_eq]
  have h_adv_fn : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
    advance_preserves_flowNestingIx tokens ps h_peek h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  split at h_ok
  -- emptyNode cases
  all_goals (try (
    simp only [Except.ok.injEq] at h_ok
    rw [← h_ok]; dsimp only [Prod.fst, Prod.snd]
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h_adv_fn, h_adv_tok⟩))
  -- parseNode case
  split at h_ok
  · simp at h_ok
  · rename_i pn_result heq_pn
    obtain ⟨val, ps'⟩ := pn_result
    simp only [Except.ok.injEq] at h_ok
    rw [← h_ok]; dsimp only [Prod.fst, Prod.snd]
    have h_ps2_tok : ({ ps.advance with
        currentPath := ps.advance.currentPath.push
          (.key s!"{pairIdx}") } : ParseStateIx input).tokens = tokens := by
      simp [advance_tokens_eq_ix, h_eq]
    have h_wb := parseNodeWBIx_apply h_ih h_ps2_tok heq_pn (by omega)
    have h_fn2 : flowNestingIx tokens ps'.pos = flowNestingIx tokens ps.advance.pos := by
      have := h_wb.2.2.1; simp at this; exact this
    exact ⟨h_wb.1,
           fun h_flow => h_wb.2.1 (by simp only [] at *; rw [h_adv_fn]; exact h_flow),
           h_fn2.trans h_adv_fn,
           h_wb.2.2.2⟩

/-- Recursion helper for `parseBlockMappingLoop_wb_ix`. -/
theorem mapping_recurse_ix (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin pairs.size,
        Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (key val : YamlValue) (ps_rec : ParseStateIx input) (k : Nat)
    (h_kf : Scannable key false) (h_vf : Scannable val false)
    (h_kt : flowNestingIx tokens ps.pos > 0 → Scannable key true)
    (h_vt : flowNestingIx tokens ps.pos > 0 → Scannable val true)
    (h_fn_rec : flowNestingIx tokens ps_rec.pos = flowNestingIx tokens ps.pos)
    (h_tok_rec : ps_rec.tokens = tokens)
    (h_rec : parseBlockMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseStateIx input) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (flowNestingIx tokens ps'.pos > 0 →
        ∀ i : Fin pairs'.size,
          Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseBlockMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (flowNestingIx tokens ps'.pos > 0 →
        ∀ i : Fin result.1.size,
          Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_wb := ih_fuel ps_rec (pairs.push (key, val)) h_tok_rec
      (push_pair_scannable h_pairs_false ⟨h_kf, h_vf⟩)
      (fun h_flow_rec => push_pair_scannable
        (h_pairs_true (by rw [h_fn_rec] at h_flow_rec; exact h_flow_rec))
        ⟨h_kt (by rw [h_fn_rec] at h_flow_rec; exact h_flow_rec),
         h_vt (by rw [h_fn_rec] at h_flow_rec; exact h_flow_rec)⟩) h_rec
  refine ⟨h_wb.1, fun h_flow => h_wb.2.1 ?_,
         h_wb.2.2.1.trans h_fn_rec, h_wb.2.2.2⟩
  rw [h_fn_rec]; exact h_flow

/-- Loop invariant for `parseBlockMappingLoop`. -/
theorem parseBlockMappingLoop_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin pairs.size,
        Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok result) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next h_peek_key =>
      split at h_ok
      · simp at h_ok
      · rename_i kv_ps heq_handle
        have h_wb := handleBlockMappingKeyEntry_wb_ix tokens n k (by omega)
            h_ih ps pairs.size kv_ps h_eq h_peek_key heq_handle
        exact mapping_recurse_ix tokens ps pairs result
            h_pairs_false h_pairs_true
            kv_ps.1 kv_ps.2.1 kv_ps.2.2 k h_wb.1 h_wb.2.2.1 h_wb.2.1 h_wb.2.2.2.1
            h_wb.2.2.2.2.1 h_wb.2.2.2.2.2 h_ok (ih_fuel (by omega))
    next h_peek_val =>
      split at h_ok
      · simp at h_ok
      · rename_i kv_ps heq_handle
        have h_wb := handleBlockMappingValueEntry_wb_ix tokens n k (by omega)
            h_ih ps pairs.size kv_ps h_eq h_peek_val heq_handle
        exact mapping_recurse_ix tokens ps pairs result
            h_pairs_false h_pairs_true
            emptyNode kv_ps.1 kv_ps.2 k
            (empty_scalar_scannable none none false) h_wb.1
            (fun _ => empty_scalar_scannable none none true) h_wb.2.1
            h_wb.2.2.1 h_wb.2.2.2 h_ok (ih_fuel (by omega))
    next =>
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩

/-- `parseBlockMapping` well-behaved given parseNode IH. -/
theorem parseBlockMapping_wb_ix (tokens : Indexed.TokenStream input)
    (fuel : Nat) (h_ih : ParseNodeWBIx tokens fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .blockMappingStart)
    (h_ok : parseBlockMapping ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_adv_tok : ps.advance.tokens = tokens := by
    simp [advance_tokens_eq_ix, h_eq]
  have h_fn_adv : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
    advance_preserves_flowNestingIx tokens ps h_peek h_eq
      (fun h => nomatch h) (fun h => nomatch h)
      (fun h => nomatch h) (fun h => nomatch h)
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k_map
    split at h_ok
    · simp at h_ok
    · rename_i loop_result heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_empty_f : ∀ i : Fin (#[] : Array (YamlValue × YamlValue)).size,
          Scannable (#[] : Array (YamlValue × YamlValue))[i].1 false ∧
          Scannable (#[] : Array (YamlValue × YamlValue))[i].2 false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : flowNestingIx tokens ps.advance.pos > 0 →
          ∀ i : Fin (#[] : Array (YamlValue × YamlValue)).size,
          Scannable (#[] : Array (YamlValue × YamlValue))[i].1 true ∧
          Scannable (#[] : Array (YamlValue × YamlValue))[i].2 true := by
        intro _ ⟨_, hi⟩; simp at hi
      have h_loop := parseBlockMappingLoop_wb_ix tokens (k_map + 1) k_map (by omega)
          h_ih ps.advance #[] (pairs_arr, ps_loop)
          h_adv_tok h_empty_f h_empty_t heq_loop
      have h_loop_fn : flowNestingIx tokens ps_loop.pos =
          flowNestingIx tokens ps.advance.pos := h_loop.2.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2.2
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      constructor
      · exact Scannable.mapping .block pairs_arr none none false
          (fun i => (h_loop.1 i).1) (fun i => (h_loop.1 i).2)
      constructor
      · intro h_flow
        exact Scannable.mapping .block pairs_arr none none true
          (fun i => (h_loop.2.1 (by rw [h_fn_adv]; exact h_flow) i).1)
          (fun i => (h_loop.2.1 (by rw [h_fn_adv]; exact h_flow) i).2)
      constructor
      · simp only []
        split
        · rename_i h_peek_end
          have h_fn_end := advance_preserves_flowNestingIx tokens ps_loop
              h_peek_end h_loop_tok
              (fun h => nomatch h) (fun h => nomatch h)
              (fun h => nomatch h) (fun h => nomatch h)
          exact h_fn_end.trans (h_loop_fn.trans h_fn_adv)
        · exact h_loop_fn.trans h_fn_adv
      · simp only []
        split
        · simp only [advance_tokens_eq_ix]; exact h_loop.2.2.2
        · exact h_loop.2.2.2

/-- Loop invariant for `parseImplicitBlockSequenceLoop`. -/
theorem parseImplicitBlockSequenceLoop_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (items : Array YamlValue)
    (result : Array YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_items_false : ∀ i : Fin items.size, Scannable items[i] false)
    (h_items_true : flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin items.size, Scannable items[i] true)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok result) :
    (∀ i : Fin result.1.size, Scannable result.1[i] false) ∧
    (flowNestingIx tokens ps.pos > 0 →
      ∀ i : Fin result.1.size, Scannable result.1[i] true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    subst h_ok
    exact ⟨h_items_false, h_items_true, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next h_peek =>
      have h_adv_tok : ps.advance.tokens = tokens := by
        simp [advance_tokens_eq_ix, h_eq]
      have h_fn : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
        advance_preserves_flowNestingIx tokens ps h_peek h_eq
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      split at h_ok
      all_goals try
        have h_wb := ih_fuel (by omega) ps.advance (items.push emptyNode)
            h_adv_tok
            (push_all_scannable h_items_false (empty_scalar_scannable none none false))
            (fun h_flow => push_all_scannable
              (h_items_true (by rw [← h_fn]; exact h_flow))
              (empty_scalar_scannable none none true))
            h_ok
        refine ⟨h_wb.1,
               fun h_flow => h_wb.2.1 (by rw [h_fn]; exact h_flow),
               ?_, h_wb.2.2.2⟩
        exact h_wb.2.2.1.trans h_fn
      next =>
        split at h_ok
        next => simp at h_ok
        next pn_result heq_pn =>
          obtain ⟨val, ps₃⟩ := pn_result
          dsimp only [] at h_ok
          have h_ps2_tok : ({ ps.advance with
              currentPath := ps.advance.currentPath.push
                (.index items.size) } : ParseStateIx input).tokens = tokens := by
            simp [advance_tokens_eq_ix, h_eq]
          have h_node := h_ih _ k val ps₃ (by omega) h_ps2_tok heq_pn
          have h_ps3_fn : flowNestingIx tokens ps₃.pos =
              flowNestingIx tokens ps.advance.pos := by
            have := h_node.2.2.1; simp at this; exact this
          have h_ps3_tok : ps₃.tokens = tokens := h_node.2.2.2
          have h_push_f := push_all_scannable h_items_false h_node.1
          have h_push_t : flowNestingIx tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseStateIx input).pos > 0 →
              ∀ i : Fin (items.push val).size,
              Scannable (items.push val)[i] true := by
            intro h_flow_ps4
            simp only [] at h_flow_ps4
            have h_flow_adv : flowNestingIx tokens ps.advance.pos > 0 := by
              rw [← h_ps3_fn]; exact h_flow_ps4
            have h_flow_ps : flowNestingIx tokens ps.pos > 0 := by
              rw [← h_fn]; exact h_flow_adv
            exact push_all_scannable (h_items_true h_flow_ps)
              (h_node.2.1 h_flow_adv)
          have h_ps4_tok : ({ ps₃ with currentPath :=
              ps.advance.currentPath } : ParseStateIx input).tokens = tokens := by
            simp [h_ps3_tok]
          have h_wb := ih_fuel (by omega)
              ({ ps₃ with currentPath := ps.advance.currentPath } : ParseStateIx input)
              (items.push val) h_ps4_tok h_push_f h_push_t h_ok
          have h_ps4_fn : flowNestingIx tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseStateIx input).pos =
              flowNestingIx tokens ps.pos := by
            simp only []; rw [h_ps3_fn, h_fn]
          refine ⟨h_wb.1,
                 fun h_flow => h_wb.2.1 (by rw [h_ps4_fn]; exact h_flow),
                 ?_, h_wb.2.2.2⟩
          exact h_wb.2.2.1.trans h_ps4_fn
    next =>
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact ⟨h_items_false, h_items_true, rfl, h_eq⟩

/-- `parseImplicitBlockSequence` well-behaved given parseNode IH. -/
theorem parseImplicitBlockSequence_wb_ix (tokens : Indexed.TokenStream input)
    (fuel : Nat) (h_ih : ParseNodeWBIx tokens fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    split at h_ok
    · simp at h_ok
    · rename_i loop_result heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_empty_f : ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : flowNestingIx tokens ps.pos > 0 →
          ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] true := by
        intro _ ⟨_, hi⟩; simp at hi
      have h_loop := parseImplicitBlockSequenceLoop_wb_ix tokens (k + 1) k (by omega)
          h_ih ps #[] (items_arr, ps_loop) h_eq
          h_empty_f h_empty_t heq_loop
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact ⟨Scannable.sequence .block items_arr none none false h_loop.1,
             fun h_flow => Scannable.sequence .block items_arr none none true
               (fun i => h_loop.2.1 h_flow i),
             h_loop.2.2.1, h_loop.2.2.2⟩

set_option maxHeartbeats 800000 in
/-- `parseSinglePairMapping` well-behaved given parseNode IH. -/
theorem parseSinglePairMapping_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (_h_fpsv : FlowAwarePSVIx tokens) (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .key)
    (h_flow : flowNestingIx tokens ps.pos > 0)
    (h_ok : parseSinglePairMapping ps fuel = .ok result) :
    Scannable result.1 true ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_adv_tok : ps.advance.tokens = tokens := by
      simp [advance_tokens_eq_ix, h_eq]
    have h_adv_fn : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
      advance_preserves_flowNestingIx tokens ps h_peek h_eq
        (by exact fun h => nomatch h) (by exact fun h => nomatch h)
        (by exact fun h => nomatch h) (by exact fun h => nomatch h)
    simp only [emptyNode] at h_ok
    split at h_ok
    -- Cases 1-3: key = emptyNode
    all_goals (try (
      have h_tc_tok := fun p => (tryConsume_with_path_tokens_ix ps.advance p .value).trans h_adv_tok
      have h_tc_fn := fun p => tryConsume_with_path_fn_ix tokens ps.advance p .value h_adv_tok
        (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun h => nomatch h)
      generalize hg : ParseStateIx.tryConsume _ _ = tc at h_ok
      have h_tcr_tok : tc.2.tokens = tokens := hg ▸ h_tc_tok _
      have h_tcr_fn : flowNestingIx tokens tc.2.pos = flowNestingIx tokens ps.advance.pos :=
        hg ▸ h_tc_fn _
      split at h_ok
      · split at h_ok <;> first | contradiction | skip
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        all_goals (try (
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true)
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
            h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩))
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        all_goals (
          have h_vwb := parseNodeWBIx_apply h_ih h_tcr_tok (by assumption) (by omega)
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true)
              (fun ⟨0, _⟩ => h_vwb.2.1 (by rw [h_tcr_fn, h_adv_fn]; exact h_flow)),
            h_vwb.2.2.1.trans (h_tcr_fn.trans h_adv_fn),
            h_vwb.2.2.2⟩)
      · simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
        exact ⟨.mapping .flow _ none none true
            (fun ⟨0, _⟩ => empty_scalar_scannable none none true)
            (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
          h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩))
    -- Case 4: key = parseNode
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (
      have h_kwb := parseNodeWBIx_apply h_ih h_adv_tok (by assumption) (by omega)
      have h_k_fn := h_kwb.2.2.1
      have h_k_tok := h_kwb.2.2.2
      have h_k_true := h_kwb.2.1 (h_adv_fn ▸ h_flow)
      have h_tc_tok := fun p => (tryConsume_with_path_tokens_ix _ p .value).trans h_k_tok
      have h_tc_fn := fun p => tryConsume_with_path_fn_ix tokens _ p .value h_k_tok
        (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun h => nomatch h)
      generalize hg : ParseStateIx.tryConsume _ _ = tc at h_ok
      have h_tcr_tok : tc.2.tokens = tokens := hg ▸ h_tc_tok _
      have h_tcr_fn : flowNestingIx tokens tc.2.pos = flowNestingIx tokens ps.advance.pos :=
        hg ▸ (h_tc_fn _).trans h_k_fn
      split at h_ok
      · split at h_ok <;> first | contradiction | skip
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        all_goals (try (
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => h_k_true)
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
            h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩))
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        all_goals (
          have h_vwb := parseNodeWBIx_apply h_ih h_tcr_tok (by assumption) (by omega)
          have h_v_true := h_vwb.2.1 (by rw [h_tcr_fn, h_adv_fn]; exact h_flow)
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => h_k_true)
              (fun ⟨0, _⟩ => h_v_true),
            h_vwb.2.2.1.trans (h_tcr_fn.trans h_adv_fn),
            h_vwb.2.2.2⟩)
      · simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
        exact ⟨.mapping .flow _ none none true
            (fun ⟨0, _⟩ => h_k_true)
            (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
          h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩)

set_option maxHeartbeats 800000 in
/-- Loop invariant for `parseFlowSequenceLoop`. -/
theorem parseFlowSequenceLoop_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_fpsv : FlowAwarePSVIx tokens) (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (items : Array YamlValue)
    (result : Array YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_flow : flowNestingIx tokens ps.pos > 0)
    (h_items : ∀ i : Fin items.size, Scannable items[i] true)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok result) :
    (∀ i : Fin result.1.size, Scannable result.1[i] true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨h_items, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    next =>
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ⟨h_items, rfl, h_eq⟩
    next =>
      split at h_ok
      · split at h_ok
        next h_sep =>
          have h_adv_tok : ps.advance.tokens = tokens := by
            simp [advance_tokens_eq_ix, h_eq]
          have h_adv_fn : flowNestingIx tokens ps.advance.pos = flowNestingIx tokens ps.pos :=
            advance_preserves_flowNestingIx tokens ps h_sep h_eq
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          have h_flow_adv : flowNestingIx tokens ps.advance.pos > 0 := by
            rw [h_adv_fn]; exact h_flow
          split at h_ok
          next h_pk =>
            split at h_ok
            next => simp at h_ok
            next spm_res heq_spm =>
              obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
              have h_ptok : ({ ps.advance with currentPath := ps.advance.currentPath.push (.index items.size) } : ParseStateIx input).tokens = tokens := by
                simp [advance_tokens_eq_ix, h_eq]
              have h_spm := parseSinglePairMapping_wb_ix tokens n k (by omega) h_fpsv h_ih _ _ h_ptok h_pk (by exact h_flow_adv) heq_spm
              have h_spm_tok : ps3.tokens = tokens := by have := h_spm.2.2; simp at this; exact this
              have h4fn : flowNestingIx tokens ({ ps3 with currentPath := ps.advance.currentPath } : ParseStateIx input).pos = flowNestingIx tokens ps.pos := by
                simp only []; have := h_spm.2.1; simp at this; rw [this, h_adv_fn]
              have h_wb := ih_fuel (by omega) _ _ (by simp [h_spm_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_spm.1) h_ok
              exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩
          next =>
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            exact ⟨h_items, h_adv_fn, h_adv_tok⟩
          next =>
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
              have h_ptok : ({ ps.advance with currentPath := ps.advance.currentPath.push (.index items.size) } : ParseStateIx input).tokens = tokens := by
                simp [advance_tokens_eq_ix, h_eq]
              have h_node := parseNodeWBIx_apply h_ih h_ptok heq_pn (by omega)
              have h_node_tok : ps3.tokens = tokens := by have := h_node.2.2.2; simp at this; exact this
              have h_vt := h_node.2.1 h_flow_adv
              have h4fn : flowNestingIx tokens ({ ps3 with currentPath := ps.advance.currentPath } : ParseStateIx input).pos = flowNestingIx tokens ps.pos := by
                simp only []
                have := h_node.2.2.1
                simp at this
                rw [this, h_adv_fn]
              have h_wb := ih_fuel (by omega) _ _ (by simp [h_node_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_vt) h_ok
              exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩
        next =>
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact ⟨h_items, rfl, h_eq⟩
      · split at h_ok
        next h_pk =>
          split at h_ok
          next => simp at h_ok
          next spm_res heq_spm =>
            obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
            have h_ptok : ({ ps with currentPath := ps.currentPath.push (.index items.size) } : ParseStateIx input).tokens = tokens := by simp [h_eq]
            have h_spm := parseSinglePairMapping_wb_ix tokens n k (by omega) h_fpsv h_ih _ _ h_ptok h_pk h_flow heq_spm
            have h_spm_tok : ps3.tokens = tokens := by have := h_spm.2.2; simp at this; exact this
            have h4fn : flowNestingIx tokens ({ ps3 with currentPath := ps.currentPath } : ParseStateIx input).pos = flowNestingIx tokens ps.pos := by
              simp only []; have := h_spm.2.1; simp at this; exact this
            have h_wb := ih_fuel (by omega) _ _ (by simp [h_spm_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_spm.1) h_ok
            exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩
        next =>
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact ⟨h_items, rfl, h_eq⟩
        next =>
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
            have h_ptok : ({ ps with currentPath := ps.currentPath.push (.index items.size) } : ParseStateIx input).tokens = tokens := by simp [h_eq]
            have h_node := parseNodeWBIx_apply h_ih h_ptok heq_pn (by omega)
            have h_node_tok : ps3.tokens = tokens := by have := h_node.2.2.2; simp at this; exact this
            have h_vt := h_node.2.1 h_flow
            have h4fn : flowNestingIx tokens ({ ps3 with currentPath := ps.currentPath } : ParseStateIx input).pos = flowNestingIx tokens ps.pos := by
              simp only []; have := h_node.2.2.1; simp at this; exact this
            have h_wb := ih_fuel (by omega) _ _ (by simp [h_node_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_vt) h_ok
            exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩

/-- `parseFlowSequence` well-behaved given parseNode IH. -/
theorem parseFlowSequence_wb_ix (tokens : Indexed.TokenStream input)
    (fuel : Nat) (h_fpsv : FlowAwarePSVIx tokens) (h_ih : ParseNodeWBIx tokens fuel)
    (h_matched : FlowBracketsMatchedIx tokens)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (h_ok : parseFlowSequence ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_adv_tok : ps.advance.tokens = tokens := by
      simp [advance_tokens_eq_ix, h_eq]
    have ⟨h_lt, h_val⟩ := peek_some_bounded_ix ps .flowSequenceStart h_peek
    have h_adv_fn_eq : flowNestingIx tokens ps.advance.pos =
        flowNestingIx tokens ps.pos + 1 := by
      simp only [ParseStateIx.advance]; subst h_eq
      exact flowNestingIx_after_flow_start_eq ps.tokens ps.pos h_lt
        (Or.inl (h_val h_lt))
    have h_flow_adv : flowNestingIx tokens ps.advance.pos > 0 := by
      rw [h_adv_fn_eq]; omega
    split at h_ok
    · simp at h_ok
    · rename_i loop_result heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_empty : ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] true := by
        intro ⟨_, hi⟩; simp at hi
      have h_loop := parseFlowSequenceLoop_wb_ix tokens (k + 1) k (by omega)
          h_fpsv h_ih ps.advance #[] (items_arr, ps_loop) h_adv_tok
          h_flow_adv h_empty heq_loop
      have h_loop_fn : flowNestingIx tokens ps_loop.pos =
          flowNestingIx tokens ps.advance.pos := h_loop.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2
      have h_items_true := h_loop.1
      split at h_ok
      · rename_i h_peek_end
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        have ⟨h_lt_end, h_val_end⟩ := peek_some_bounded_ix ps_loop
            .flowSequenceEnd h_peek_end
        have h_end_fn : flowNestingIx tokens ps_loop.advance.pos =
            flowNestingIx tokens ps_loop.pos - 1 := by
          simp only [ParseStateIx.advance]; rw [← h_loop_tok]
          exact flowNestingIx_after_flow_end ps_loop.tokens ps_loop.pos h_lt_end
            (Or.inl (h_val_end h_lt_end))
            (by rw [h_loop_tok, h_loop_fn, h_adv_fn_eq]; omega)
        have h_net_fn : flowNestingIx tokens ps_loop.advance.pos =
            flowNestingIx tokens ps.pos := by
          rw [h_end_fn, h_loop_fn, h_adv_fn_eq]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Scannable.sequence .flow items_arr none none false h_items_true
        · intro _
          exact Scannable.sequence .flow items_arr none none true h_items_true
        · simp only [ParseStateIx.advance]; exact h_net_fn
        · simp only [ParseStateIx.advance]; exact h_loop_tok
      · simp at h_ok

/-- Well-behavedness of `parseFlowMappingValue`. -/
theorem parseFlowMappingValue_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (savedPath : YamlPath) (keyContent : String)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok result) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  have h1_tok : ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tokens = tokens :=
    (tryConsume_with_path_tokens_ix ps (savedPath.push (.key keyContent)) .key).trans h_eq
  have h1_fn : flowNestingIx tokens ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.pos =
      flowNestingIx tokens ps.pos :=
    tryConsume_with_path_fn_ix tokens ps (savedPath.push (.key keyContent)) .key h_eq
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  generalize hg1 : ParseStateIx.tryConsume
    { ps with currentPath := savedPath.push (.key keyContent) }
    YamlToken.key = tc1 at h_ok
  have h1r_tok : tc1.2.tokens = tokens := hg1 ▸ h1_tok
  have h1r_fn : flowNestingIx tokens tc1.2.pos = flowNestingIx tokens ps.pos := hg1 ▸ h1_fn
  have h2_tok : (tc1.2.tryConsume .value).2.tokens = tokens :=
    (tryConsume_tokens_ix tc1.2 .value).trans h1r_tok
  have h2_fn0 : flowNestingIx tokens (tc1.2.tryConsume .value).2.pos = flowNestingIx tokens tc1.2.pos :=
    tryConsume_flowNesting_ix tokens tc1.2 .value h1r_tok
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  generalize hg2 : ParseStateIx.tryConsume tc1.2 YamlToken.value = tc2 at h_ok
  have h2r_tok : tc2.2.tokens = tokens := hg2 ▸ h2_tok
  have h2r_fn : flowNestingIx tokens tc2.2.pos = flowNestingIx tokens ps.pos := by
    exact (hg2 ▸ h2_fn0).trans h1r_fn
  split at h_ok
  · split at h_ok
    · simp only [Except.ok.injEq] at h_ok
      rw [← h_ok]
      exact ⟨empty_scalar_scannable none none false,
             fun _ => empty_scalar_scannable none none true,
             h2r_fn, h2r_tok⟩
    · simp only [Except.ok.injEq] at h_ok
      rw [← h_ok]
      exact ⟨empty_scalar_scannable none none false,
             fun _ => empty_scalar_scannable none none true,
             h2r_fn, h2r_tok⟩
    · simp only [Except.ok.injEq] at h_ok
      rw [← h_ok]
      exact ⟨empty_scalar_scannable none none false,
             fun _ => empty_scalar_scannable none none true,
             h2r_fn, h2r_tok⟩
    · split at h_ok
      · simp at h_ok
      · rename_i pn_result heq_pn
        obtain ⟨val, ps'⟩ := pn_result
        have h_wb := parseNodeWBIx_apply h_ih h2r_tok heq_pn (by omega)
        simp only [Except.ok.injEq] at h_ok
        rw [← h_ok]
        exact ⟨h_wb.1,
               fun h_flow => h_wb.2.1 (by rw [h2r_fn]; exact h_flow),
               h_wb.2.2.1.trans h2r_fn,
               h_wb.2.2.2⟩
  · simp only [Except.ok.injEq] at h_ok
    rw [← h_ok]
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h2r_fn, h2r_tok⟩

/-- Token preservation for `parseFlowMappingValue`. -/
theorem parseFlowMappingValue_tokens_preserved_ix (tokens : Indexed.TokenStream input)
    (n : Nat) (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (savedPath : YamlPath) (keyContent : String)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok result) :
    result.2.tokens = tokens := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  have h1_tok : ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tokens = tokens :=
    (tryConsume_with_path_tokens_ix ps (savedPath.push (.key keyContent)) .key).trans h_eq
  generalize hg1 : ParseStateIx.tryConsume
    { ps with currentPath := savedPath.push (.key keyContent) }
    YamlToken.key = tc1 at h_ok
  have h1r : tc1.2.tokens = tokens := hg1 ▸ h1_tok
  have h2_tok : (tc1.2.tryConsume .value).2.tokens = tokens :=
    (tryConsume_tokens_ix tc1.2 .value).trans h1r
  generalize hg : ParseStateIx.tryConsume tc1.2 .value = tc at h_ok
  have h_tcr_tok : tc.2.tokens = tokens := hg ▸ h2_tok
  split at h_ok
  · split at h_ok
    all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_tcr_tok))
    split at h_ok <;> first | (simp at h_ok; done) | skip
    have h_wb := parseNodeWBIx_apply h_ih h_tcr_tok (by assumption) (by omega)
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_wb.2.2.2
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_tcr_tok

/-- Token preservation for `parseExplicitKey`. -/
theorem parseExplicitKey_tokens_preserved_ix (tokens : Indexed.TokenStream input)
    (n : Nat) (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseExplicitKey ps fuel = .ok result) :
    result.2.tokens = tokens := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_eq))
  exact (parseNodeWBIx_apply h_ih h_eq h_ok (by omega)).2.2.2

/-- Well-behavedness of `parseExplicitKey`. -/
theorem parseExplicitKey_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseExplicitKey ps fuel = .ok result) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true, rfl, h_eq⟩
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true, rfl, h_eq⟩
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true, rfl, h_eq⟩
  · exact parseNodeWBIx_apply h_ih h_eq h_ok (by omega)

set_option maxHeartbeats 800000 in
/-- Token preservation: `parseFlowMappingLoop` never mutates the token stream. -/
theorem parseFlowMappingLoop_tokens_preserved_ix (tokens : Indexed.TokenStream input)
    (n : Nat)
    (_h_fpsv : FlowAwarePSVIx tokens)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    result.2.tokens = tokens := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_eq
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_eq
    · all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals (try (simp at h_ok))
      all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_eq))
      all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only [advance_tokens_eq_ix]; exact h_eq))
      all_goals (try (subst h_ok; exact h_eq))
      all_goals (try (subst h_ok; simp only [advance_tokens_eq_ix]; exact h_eq))
      all_goals (try (
        rename_i v_ek heq_ek _ v_pFMV heq_pFMV
        have h_kt := parseExplicitKey_tokens_preserved_ix tokens n h_ih _ k
          (by omega) v_ek (by simp only [advance_tokens_eq_ix]; exact h_eq) heq_ek
        have h_vt := parseFlowMappingValue_tokens_preserved_ix tokens n h_ih _ k
          (by omega) _ _ v_pFMV h_kt heq_pFMV
        exact ih_fuel _ (by omega) _ h_vt h_ok))
      all_goals (try (
        rename_i v_node heq_node _ v_pFMV heq_pFMV
        have h_nt := (parseNodeWBIx_apply h_ih
          (by simp only [advance_tokens_eq_ix]; exact h_eq)
          heq_node (by omega)).2.2.2
        have h_vt := parseFlowMappingValue_tokens_preserved_ix tokens n h_ih _ k
          (by omega) _ _ v_pFMV h_nt heq_pFMV
        exact ih_fuel _ (by omega) _ h_vt h_ok))
      rename_i v_node heq_node _ v_pFMV heq_pFMV
      have h_nt := (parseNodeWBIx_apply h_ih h_eq heq_node (by omega)).2.2.2
      have h_vt := parseFlowMappingValue_tokens_preserved_ix tokens n h_ih _ k
        (by omega) _ _ v_pFMV h_nt heq_pFMV
      exact ih_fuel _ (by omega) _ h_vt h_ok

/-- Recursion helper for `parseFlowMappingLoop_wb_ix`. -/
theorem flow_mapping_recurse_ix (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_flow : flowNestingIx tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (key val : YamlValue) (ps_rec : ParseStateIx input) (k : Nat)
    (h_kf : Scannable key false) (h_vf : Scannable val false)
    (h_kt : Scannable key true) (h_vt : Scannable val true)
    (h_fn_rec : flowNestingIx tokens ps_rec.pos = flowNestingIx tokens ps.pos)
    (h_tok_rec : ps_rec.tokens = tokens)
    (h_rec : parseFlowMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseStateIx input) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      flowNestingIx tokens ps'.pos > 0 →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseFlowMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_flow_rec : flowNestingIx tokens ps_rec.pos > 0 := by rw [h_fn_rec]; exact h_flow
  have h_wb := ih_fuel ps_rec (pairs.push (key, val)) h_tok_rec h_flow_rec
      (push_pair_scannable h_pairs_false ⟨h_kf, h_vf⟩)
      (push_pair_scannable h_pairs_true ⟨h_kt, h_vt⟩) h_rec
  exact ⟨h_wb.1, h_wb.2.1, h_wb.2.2.1.trans h_fn_rec, h_wb.2.2.2⟩

/-- Helper: parseExplicitKey + parseFlowMappingValue + recurse. -/
theorem explicitKey_val_recurse_ix (tokens : Indexed.TokenStream input)
    (n : Nat) (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_flow : flowNestingIx tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (ps_ek : ParseStateIx input) (k : Nat) (h_kn : k ≤ n)
    (key : YamlValue) (ps_key : ParseStateIx input)
    (h_ek_tok : ps_ek.tokens = tokens)
    (h_ek_fn : flowNestingIx tokens ps_ek.pos = flowNestingIx tokens ps.pos)
    (heq_ek : parseExplicitKey ps_ek k = .ok (key, ps_key))
    (keyContent : String)
    (val : YamlValue) (ps_rec : ParseStateIx input)
    (heq_val : parseFlowMappingValue ps_key k ps_key.currentPath keyContent = .ok (val, ps_rec))
    (h_ok : parseFlowMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseStateIx input) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      flowNestingIx tokens ps'.pos > 0 →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseFlowMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_ek_flow : flowNestingIx tokens ps_ek.pos > 0 := by rw [h_ek_fn]; exact h_flow
  have h_kwb := parseExplicitKey_wb_ix tokens n k h_kn h_ih ps_ek (key, ps_key) h_ek_tok heq_ek
  have h_key_flow : flowNestingIx tokens ps_key.pos > 0 := by
    rw [h_kwb.2.2.1]; exact h_ek_flow
  have h_vwb := parseFlowMappingValue_wb_ix tokens n k h_kn h_ih ps_key ps_key.currentPath
    keyContent (val, ps_rec) h_kwb.2.2.2 heq_val
  exact flow_mapping_recurse_ix tokens ps pairs result h_flow
    h_pairs_false h_pairs_true
    key val ps_rec k
    h_kwb.1 h_vwb.1
    (h_kwb.2.1 h_ek_flow) (h_vwb.2.1 h_key_flow)
    (h_vwb.2.2.1.trans (h_kwb.2.2.1.trans h_ek_fn)) h_vwb.2.2.2 h_ok ih_fuel

/-- Helper: parseNode + parseFlowMappingValue + recurse (implicit key). -/
theorem implicitKey_val_recurse_ix (tokens : Indexed.TokenStream input)
    (n : Nat) (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_flow : flowNestingIx tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (ps_pn : ParseStateIx input) (k : Nat) (h_kn : k ≤ n)
    (key : YamlValue) (ps_key : ParseStateIx input)
    (h_pn_tok : ps_pn.tokens = tokens)
    (h_pn_fn : flowNestingIx tokens ps_pn.pos = flowNestingIx tokens ps.pos)
    (heq_pn : parseNode ps_pn k = .ok (key, ps_key))
    (keyContent : String)
    (val : YamlValue) (ps_rec : ParseStateIx input)
    (heq_val : parseFlowMappingValue ps_key k ps_key.currentPath keyContent = .ok (val, ps_rec))
    (h_ok : parseFlowMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseStateIx input) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      flowNestingIx tokens ps'.pos > 0 →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseFlowMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_kwb := parseNodeWBIx_apply h_ih h_pn_tok heq_pn (by omega)
  have h_key_flow : flowNestingIx tokens ps_pn.pos > 0 := by rw [h_pn_fn]; exact h_flow
  have h_ps_key_flow : flowNestingIx tokens ps_key.pos > 0 := by
    rw [h_kwb.2.2.1]; exact h_key_flow
  have h_vwb := parseFlowMappingValue_wb_ix tokens n k h_kn h_ih ps_key ps_key.currentPath
    keyContent (val, ps_rec) h_kwb.2.2.2 heq_val
  exact flow_mapping_recurse_ix tokens ps pairs result h_flow
    h_pairs_false h_pairs_true
    key val ps_rec k
    h_kwb.1 h_vwb.1
    (h_kwb.2.1 h_key_flow) (h_vwb.2.1 h_ps_key_flow)
    (h_vwb.2.2.1.trans (h_kwb.2.2.1.trans h_pn_fn)) h_vwb.2.2.2 h_ok ih_fuel

set_option maxHeartbeats 800000 in
/-- Loop invariant for `parseFlowMappingLoop`. -/
theorem parseFlowMappingLoop_wb_ix
    (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWBIx tokens n)
    (ps : ParseStateIx input) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_flow : flowNestingIx tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩
    · all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals first
        | (simp only [Except.ok.injEq] at h_ok; subst h_ok;
           exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩)
        | (simp only [Except.ok.injEq] at h_ok; cases h_ok;
           exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩)
        | (simp only [Except.ok.injEq] at h_ok; cases h_ok;
           have h_sep : ps.peek? = some YamlToken.flowEntry := by assumption;
           have h_adv_fn := advance_preserves_flowNestingIx tokens ps h_sep h_eq
             (by exact fun h => nomatch h) (by exact fun h => nomatch h)
             (by exact fun h => nomatch h) (by exact fun h => nomatch h);
           exact ⟨h_pairs_false, h_pairs_true, h_adv_fn,
                  by simp [advance_tokens_eq_ix, h_eq]⟩)
        | skip
      all_goals first
        | (rename_i v_ek heq_ek _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_ek;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact explicitKey_val_recurse_ix tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true _ k (by omega) key ps_key
             (by simp [advance_tokens_eq_ix, h_eq]) (by
               have h_sep : ps.peek? = some YamlToken.flowEntry := by assumption
               have h_adv_fn := advance_preserves_flowNestingIx tokens ps h_sep h_eq
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               have h_key_peek : ps.advance.peek? = some YamlToken.key := by assumption
               have h_key_fn := advance_preserves_flowNestingIx tokens ps.advance h_key_peek
                 (by simp [advance_tokens_eq_ix, h_eq])
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               rw [h_key_fn, h_adv_fn])
             heq_ek _ val ps_rec heq_val h_ok (ih_fuel (by omega)))
        | (rename_i v_ek heq_ek _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_ek;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact explicitKey_val_recurse_ix tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true _ k (by omega) key ps_key
             (by simp [advance_tokens_eq_ix, h_eq]) (by
               have h_key_peek : ps.peek? = some YamlToken.key := by assumption
               have h_key_fn := advance_preserves_flowNestingIx tokens ps h_key_peek h_eq
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               exact h_key_fn)
             heq_ek _ val ps_rec heq_val h_ok (ih_fuel (by omega)))
        | skip
      all_goals first
        | (rename_i v_node heq_node _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_node;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact implicitKey_val_recurse_ix tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true _ k (by omega) key ps_key
             (by simp [advance_tokens_eq_ix, h_eq]) (by
               have h_sep : ps.peek? = some YamlToken.flowEntry := by assumption
               have h_adv_fn := advance_preserves_flowNestingIx tokens ps h_sep h_eq
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               exact h_adv_fn)
             heq_node _ val ps_rec heq_val h_ok (ih_fuel (by omega)))
        | (rename_i v_node heq_node _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_node;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact implicitKey_val_recurse_ix tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true ps k (by omega) key ps_key
             h_eq rfl heq_node _ val ps_rec heq_val h_ok (ih_fuel (by omega)))

/-- `parseFlowMapping` well-behaved given parseNode IH. -/
theorem parseFlowMapping_wb_ix (tokens : Indexed.TokenStream input)
    (fuel : Nat) (h_fpsv : FlowAwarePSVIx tokens) (h_ih : ParseNodeWBIx tokens fuel)
    (h_matched : FlowBracketsMatchedIx tokens)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .flowMappingStart)
    (h_ok : parseFlowMapping ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_adv_tok : ps.advance.tokens = tokens := by
      simp [advance_tokens_eq_ix, h_eq]
    have ⟨h_lt, h_val⟩ := peek_some_bounded_ix ps .flowMappingStart h_peek
    have h_adv_fn_eq : flowNestingIx tokens ps.advance.pos =
        flowNestingIx tokens ps.pos + 1 := by
      simp only [ParseStateIx.advance]; subst h_eq
      exact flowNestingIx_after_flow_start_eq ps.tokens ps.pos h_lt
        (Or.inr (h_val h_lt))
    have h_flow_adv : flowNestingIx tokens ps.advance.pos > 0 := by
      rw [h_adv_fn_eq]; omega
    split at h_ok
    · simp at h_ok
    · rename_i loop_result heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_empty_f : ∀ i : Fin (#[] : Array (YamlValue × YamlValue)).size,
          Scannable (#[] : Array (YamlValue × YamlValue))[i].1 false ∧
          Scannable (#[] : Array (YamlValue × YamlValue))[i].2 false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : ∀ i : Fin (#[] : Array (YamlValue × YamlValue)).size,
          Scannable (#[] : Array (YamlValue × YamlValue))[i].1 true ∧
          Scannable (#[] : Array (YamlValue × YamlValue))[i].2 true := by
        intro ⟨_, hi⟩; simp at hi
      have h_loop := parseFlowMappingLoop_wb_ix tokens (k + 1) k (by omega)
          h_ih ps.advance #[] (pairs_arr, ps_loop) h_adv_tok
          h_flow_adv h_empty_f h_empty_t heq_loop
      have h_loop_fn : flowNestingIx tokens ps_loop.pos =
          flowNestingIx tokens ps.advance.pos := h_loop.2.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2.2
      have h_pairs_false := h_loop.1
      have h_pairs_true := h_loop.2.1
      split at h_ok
      · rename_i h_peek_end
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        have ⟨h_lt_end, h_val_end⟩ := peek_some_bounded_ix ps_loop
            .flowMappingEnd h_peek_end
        have h_end_fn : flowNestingIx tokens ps_loop.advance.pos =
            flowNestingIx tokens ps_loop.pos - 1 := by
          simp only [ParseStateIx.advance]; rw [← h_loop_tok]
          exact flowNestingIx_after_flow_end ps_loop.tokens ps_loop.pos h_lt_end
            (Or.inr (h_val_end h_lt_end))
            (by rw [h_loop_tok, h_loop_fn, h_adv_fn_eq]; omega)
        have h_net_fn : flowNestingIx tokens ps_loop.advance.pos =
            flowNestingIx tokens ps.pos := by
          rw [h_end_fn, h_loop_fn, h_adv_fn_eq]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Scannable.mapping .flow pairs_arr none none false
            (fun i => (h_pairs_true i).1) (fun i => (h_pairs_true i).2)
        · intro _
          exact Scannable.mapping .flow pairs_arr none none true
            (fun i => (h_pairs_true i).1) (fun i => (h_pairs_true i).2)
        · simp only [ParseStateIx.advance]; exact h_net_fn
        · simp only [ParseStateIx.advance]; exact h_loop_tok
      · simp at h_ok

/-- Base case: at fuel 0, `parseNode` always returns error, so
    `ParseNodeWBIx tokens 0` is vacuously true. -/
theorem parseNode_wb_zero_ix (tokens : Indexed.TokenStream input) :
    ParseNodeWBIx tokens 0 := by
  intro ps m val ps' hm h_eq h_ok
  have : m = 0 := by omega
  subst this
  unfold parseNode at h_ok
  simp at h_ok

/-- Well-behavedness of `parseNodeContent`. -/
theorem parseNodeContent_wb_ix (tokens : Indexed.TokenStream input)
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_fpsv : FlowAwarePSVIx tokens) (h_ih : ParseNodeWBIx tokens n)
    (h_matched : FlowBracketsMatchedIx tokens)
    (ps : ParseStateIx input) (props : NodeProperties)
    (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseNodeContent ps fuel props = .ok result) :
    Scannable result.1 false ∧
    (flowNestingIx tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos ∧
    result.2.tokens = tokens := by
  have h_ih_fuel : ParseNodeWBIx tokens fuel :=
    fun ps' m val ps'' hm htok hok => h_ih ps' m val ps'' (Nat.le_trans hm h_fuel) htok hok
  unfold parseNodeContent at h_ok
  split at h_ok
  -- scalar
  · rename_i content style heq_peek
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    have ⟨h_lt, h_val⟩ := peek_some_bounded_ix ps (.scalar content style) heq_peek
    have h_lt_tok : ps.pos < tokens.size := by rw [← h_eq]; exact h_lt
    have h_tok : (tokens[ps.pos]'h_lt_tok).token = .scalar content style := by
      have h1 := h_val h_lt
      simp only [h_eq] at h1
      exact h1
    exact ⟨scalar_from_token_scannable_ix tokens h_fpsv.1 ps.pos h_lt_tok content style
             h_tok props.tag props.anchor,
           fun h_flow => scalar_from_flow_token_scannable_ix tokens h_fpsv ps.pos h_lt_tok
             content style h_tok h_flow props.tag props.anchor true,
           advance_preserves_flowNestingIx tokens ps heq_peek h_eq
             (fun h => nomatch h) (fun h => nomatch h)
             (fun h => nomatch h) (fun h => nomatch h),
           by simp [advance_tokens_eq_ix, h_eq]⟩
  · rename_i heq_peek
    exact parseBlockSequence_wb_ix tokens fuel h_fpsv h_ih_fuel ps result h_eq heq_peek h_ok
  · rename_i heq_peek
    exact parseBlockMapping_wb_ix tokens fuel h_ih_fuel ps result h_eq heq_peek h_ok
  · exact parseImplicitBlockSequence_wb_ix tokens fuel h_ih_fuel ps result h_eq h_ok
  · rename_i heq_peek
    exact parseFlowSequence_wb_ix tokens fuel h_fpsv h_ih_fuel h_matched ps result h_eq heq_peek h_ok
  · rename_i heq_peek
    exact parseFlowMapping_wb_ix tokens fuel h_fpsv h_ih_fuel h_matched ps result h_eq heq_peek h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨empty_scalar_scannable props.tag props.anchor false,
           fun _ => empty_scalar_scannable props.tag props.anchor true,
           rfl, h_eq⟩

/-- W1: Alias branch of `parseNode` preserves tokens. -/
theorem parseNode_alias_tokens_ix (ps : ParseStateIx input) (fuel : Nat) (name : String)
    (h_peek : ps.peek? = some (.alias name))
    (result : YamlValue × ParseStateIx input)
    (h_ok : parseNode ps (fuel + 1) = .ok result) :
    result.2.tokens = ps.tokens := by
  unfold parseNode at h_ok
  simp only [h_peek, bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · contradiction
  · split at h_ok <;> {
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨-, rfl⟩ := h_ok; simp [advance_tokens_eq_ix]
    }

/-- W2: Alias branch preserves flowNestingIx. -/
theorem parseNode_alias_flowNesting_ix (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input) (fuel : Nat) (name : String)
    (h_peek : ps.peek? = some (.alias name))
    (h_eq : ps.tokens = tokens)
    (result : YamlValue × ParseStateIx input)
    (h_ok : parseNode ps (fuel + 1) = .ok result) :
    flowNestingIx tokens result.2.pos = flowNestingIx tokens ps.pos := by
  unfold parseNode at h_ok
  simp only [h_peek, bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · contradiction
  · split at h_ok <;> {
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨-, rfl⟩ := h_ok
      simp only [ParseStateIx.advance]
      exact advance_preserves_flowNestingIx tokens ps h_peek h_eq
        (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun h => nomatch h)
    }

/-- **Key lemma**: `parseNode` is well-behaved at every fuel level.
    Proved by strong induction on fuel using all the sub-parser
    well-behavedness lemmas. -/
theorem parseNode_wb_all_ix (tokens : Indexed.TokenStream input)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens) :
    ∀ n, ParseNodeWBIx tokens n := by
  intro n
  induction n with
  | zero => exact parseNode_wb_zero_ix tokens
  | succ n ih =>
    intro ps m val ps' hm h_eq h_ok
    by_cases hm0 : m = 0
    · subst hm0; unfold parseNode at h_ok; simp at h_ok
    · obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hk : k ≤ n := by omega
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      split at h_ok
      · rename_i name heq_peek
        split at h_ok
        · contradiction
        · split at h_ok
          · simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
            exact ⟨.alias name false,
                   fun _ => .alias name true,
                   advance_preserves_flowNestingIx tokens ps heq_peek h_eq
                     (fun h => nomatch h) (fun h => nomatch h)
                     (fun h => nomatch h) (fun h => nomatch h),
                   by simp [advance_tokens_eq_ix, h_eq]⟩
          · simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
            exact ⟨.alias name false,
                   fun _ => .alias name true,
                   advance_preserves_flowNestingIx tokens ps heq_peek h_eq
                     (fun h => nomatch h) (fun h => nomatch h)
                     (fun h => nomatch h) (fun h => nomatch h),
                   by simp [advance_tokens_eq_ix, h_eq]⟩
      · split at h_ok
        · contradiction
        · rename_i v_props heq_props
          split at h_ok
          · contradiction
          · split at h_ok
            · contradiction
            · rename_i v_content heq_content
              simp only [Except.ok.injEq] at h_ok
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
              have h_props_tok : v_props.2.tokens = tokens :=
                (parseNodeProperties_tokens_ix ps v_props.1 v_props.2
                  heq_props).trans h_eq
              have h_props_fn : flowNestingIx tokens v_props.2.pos = flowNestingIx tokens ps.pos :=
                parseNodeProperties_flowNesting_ix tokens ps v_props.1 v_props.2
                  heq_props h_eq
              have h_content := parseNodeContent_wb_ix tokens n k hk h_fpsv ih h_matched
                v_props.2 v_props.1 v_content h_props_tok heq_content
              have h_fin_pos := applyNodeFinalization_pos_ix
                v_content.1 v_content.2 v_props.1
                (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
              have h_fin_tok := applyNodeFinalization_tokens_ix
                v_content.1 v_content.2 v_props.1
                (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
              exact ⟨
                applyNodeFinalization_scannable_ix
                  v_content.1 v_content.2 v_props.1
                  (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
                  false h_content.1,
                fun h_flow =>
                  applyNodeFinalization_scannable_ix v_content.1 v_content.2 v_props.1
                    (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
                    true (h_content.2.1 (by rw [h_props_fn]; exact h_flow)),
                show flowNestingIx tokens (applyNodeFinalization v_content.1 v_content.2 v_props.1
                  (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos =
                  flowNestingIx tokens ps.pos from by
                  rw [h_fin_pos, h_content.2.2.1, h_props_fn],
                show (applyNodeFinalization v_content.1 v_content.2 v_props.1
                  (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.tokens = tokens from by
                  rw [h_fin_tok]; exact h_content.2.2.2⟩

/-- `parseNode` preserves the token stream. -/
theorem parseNode_tokens_preserved_ix
    (tokens : Indexed.TokenStream input)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens)
    (ps : ParseStateIx input) (fuel : Nat) (result : YamlValue × ParseStateIx input)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseNode ps fuel = .ok result) :
    result.2.tokens = ps.tokens := by
  have h_wb := parseNode_wb_all_ix tokens h_fpsv h_matched fuel
    ps fuel result.1 result.2 (Nat.le.refl) h_eq
    (by rw [Prod.eta]; exact h_ok)
  rw [h_wb.2.2.2, h_eq]

/-! ### §5f  parseDocument output scannability — Indexed -/

/-- `prepareDocumentState` preserves the token stream. -/
theorem prepareDocumentState_tokens_preserved_ix
    (ps : ParseStateIx input) (dirs : Array Directive) (ps' : ParseStateIx input)
    (h_ok : prepareDocumentState ps = .ok (dirs, ps')) :
    ps'.tokens = ps.tokens := by
  have h_tok :
      ({ (parseDirectives ps).2 with
          tagHandles := (parseDirectives ps).1.filterMap fun
            | Directive.tag handle tagPrefix => some (handle, tagPrefix)
            | _ => none }.tryConsume .documentStart).2.tokens = ps.tokens := by
    calc
      ({ (parseDirectives ps).2 with
          tagHandles := (parseDirectives ps).1.filterMap fun
            | Directive.tag handle tagPrefix => some (handle, tagPrefix)
            | _ => none }.tryConsume .documentStart).2.tokens
          = ({ (parseDirectives ps).2 with
                tagHandles := (parseDirectives ps).1.filterMap fun
                  | Directive.tag handle tagPrefix => some (handle, tagPrefix)
                  | _ => none }).tokens :=
              tryConsume_tokens_ix _ _
      _ = (parseDirectives ps).2.tokens := rfl
      _ = ps.tokens := parseDirectives_tokens_ix ps
  unfold prepareDocumentState at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  all_goals (first | split at h_ok | skip)
  all_goals (first | split at h_ok | skip)
  all_goals (first | split at h_ok | skip)
  all_goals (first | split at h_ok | skip)
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok)
  all_goals (
    obtain ⟨_, rfl⟩ := h_ok
    exact h_tok)

/-- `parseDocument` preserves the token stream. -/
theorem parseDocument_tokens_preserved_ix
    (ps : ParseStateIx input) (doc : YamlDocument) (ps' : ParseStateIx input)
    (h_fpsv : FlowAwarePSVIx ps.tokens)
    (h_matched : FlowBracketsMatchedIx ps.tokens)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    ps'.tokens = ps.tokens := by
  unfold parseDocument at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i prep_result h_prep
    obtain ⟨dirs, ps1⟩ := prep_result
    dsimp only [] at h_ok
    have h_prep_tok : ps1.tokens = ps.tokens :=
      prepareDocumentState_tokens_preserved_ix ps dirs ps1 h_prep
    split at h_ok
    all_goals (try (
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨_, rfl⟩ := h_ok
      exact h_prep_tok))
    split at h_ok
    · simp at h_ok
    · rename_i node_result h_pn
      obtain ⟨val, ps2⟩ := node_result
      dsimp only [] at h_ok
      have h_node_tok : ps2.tokens = ps.tokens :=
        (parseNode_tokens_preserved_ix ps.tokens (h_prep_tok ▸ h_fpsv)
          (h_prep_tok ▸ h_matched) ps1 (4 * ps1.tokens.size + 4)
          (val, ps2) h_prep_tok h_pn).trans h_prep_tok
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨_, rfl⟩ := h_ok
      exact h_node_tok

/-- Factoring: `parseDocument`'s root value is either `emptyNode` or
    the result of `parseNode` on a state with preserved tokens. -/
theorem parseDocument_value_cases_ix
    (ps : ParseStateIx input) (doc : YamlDocument) (ps' : ParseStateIx input)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    (doc.value = emptyNode) ∨
    (∃ ps_inner ps_after : ParseStateIx input,
      ps_inner.tokens = ps.tokens ∧
      parseNode ps_inner (4 * ps.tokens.size + 4) = .ok (doc.value, ps_after)) := by
  unfold parseDocument at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i prep_result h_prep
    obtain ⟨dirs, ps1⟩ := prep_result
    dsimp only [] at h_ok
    have h_prep_tok : ps1.tokens = ps.tokens :=
      prepareDocumentState_tokens_preserved_ix ps dirs ps1 h_prep
    split at h_ok
    all_goals (try (
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨h_doc, _⟩ := h_ok
      subst h_doc; left; rfl))
    split at h_ok
    · simp at h_ok
    · rename_i node_result h_pn
      obtain ⟨val, ps2⟩ := node_result
      dsimp only [] at h_ok
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨h_doc, _⟩ := h_ok
      right
      subst h_doc
      exact ⟨ps1, ps2, h_prep_tok, by rw [h_prep_tok] at h_pn; exact h_pn⟩

/-- C2a·core: A document produced by `parseDocument` has a `Scannable` root. -/
theorem parseDocument_scannable_ix
    (tokens : Indexed.TokenStream input)
    (ps : ParseStateIx input) (doc : YamlDocument) (ps' : ParseStateIx input)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    Scannable doc.value false := by
  rcases parseDocument_value_cases_ix ps doc ps' h_ok with
    h_empty | ⟨ps_inner, ps_after, h_eq_inner, h_pn⟩
  · rw [h_empty]
    exact empty_scalar_scannable none none false
  · have h_tok : ps_inner.tokens = tokens := by rw [h_eq_inner, h_eq]
    let fuel := 4 * ps.tokens.size + 4
    have h_wb := parseNode_wb_all_ix tokens h_fpsv h_matched fuel
    exact (h_wb ps_inner fuel doc.value ps_after (by omega) h_tok h_pn).1

/-! ### §5g  parseStream loop decomposition — Indexed -/

/-- `ParseStateIx.expect` preserves the token stream. -/
theorem expect_tokens_ix (ps ps' : ParseStateIx input) (tok : YamlToken) (desc : String)
    (h : ps.expect tok desc = .ok ps') : ps'.tokens = ps.tokens := by
  unfold ParseStateIx.expect at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [advance_tokens_eq_ix]
    · simp at h
  · simp at h

/-- Every document in `parseStreamLoop`'s output was either already in the
    accumulator or produced by `parseDocument` with the same token stream. -/
theorem parseStreamLoop_docs_from_parseDocument_ix
    (tokens : Indexed.TokenStream input)
    (h_fpsv : FlowAwarePSVIx tokens) (h_matched : FlowBracketsMatchedIx tokens)
    (ps : ParseStateIx input) (docs : Array YamlDocument)
    (streamState : StreamState) (fuel : Nat)
    (result : Array YamlDocument)
    (h_eq : ps.tokens = tokens)
    (h_acc : ∀ doc ∈ docs.toList, ∃ ps_d ps_d' : ParseStateIx input,
        ps_d.tokens = tokens ∧ parseDocument ps_d = .ok (doc, ps_d'))
    (h_ok : parseStreamLoop ps docs streamState fuel = .ok result) :
    ∀ doc ∈ result.toList, ∃ ps_d ps_d' : ParseStateIx input,
        ps_d.tokens = tokens ∧ parseDocument ps_d = .ok (doc, ps_d') := by
  induction fuel generalizing ps docs streamState with
  | zero =>
    simp only [parseStreamLoop] at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
  | succ fuel ih =>
    unfold parseStreamLoop at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · rename_i tok
      split at h_ok
      · simp at h_ok
      · dsimp only [] at h_ok
        generalize h_pd : parseDocument ps = pd_result at h_ok
        cases pd_result with
        | error e => simp at h_ok
        | ok val =>
          obtain ⟨doc_new, ps'⟩ := val
          dsimp only [] at h_ok
          have h_pd_tok : ps'.tokens = tokens :=
            (parseDocument_tokens_preserved_ix ps doc_new ps'
              (h_eq ▸ h_fpsv) (h_eq ▸ h_matched) h_pd).trans h_eq
          let ps_reset : ParseStateIx input :=
            { ps' with anchors := #[], nodePositions := #[], currentPath := #[] }
          have h_next_tok : (ps_reset.tryConsume .documentEnd).2.tokens = tokens :=
            (tryConsume_tokens_ix _ _).trans h_pd_tok
          have h_acc' : ∀ doc ∈ (docs.push doc_new).toList,
              ∃ ps_d ps_d' : ParseStateIx input,
              ps_d.tokens = tokens ∧ parseDocument ps_d = .ok (doc, ps_d') := by
            intro d hd
            rw [Array.toList_push] at hd
            simp only [List.mem_append, List.mem_singleton] at hd
            rcases hd with hd_old | rfl
            · exact h_acc d hd_old
            · exact ⟨ps, ps', h_eq, h_pd⟩
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc'
          · exact ih _ _ _ h_next_tok h_acc' h_ok

/-- Every document in `parseStreamIx`'s output was produced by `parseDocument`
    with the same token stream. -/
theorem parseStream_doc_from_parseDocument_ix
    (tokens : Indexed.TokenStream input)
    (h_fpsv : FlowAwarePSVIx tokens) (h_matched : FlowBracketsMatchedIx tokens)
    (docs : Array YamlDocument)
    (h_parse : parseStreamIx tokens = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ ps ps' : ParseStateIx input,
      ps.tokens = tokens ∧ parseDocument ps = .ok (doc, ps') := by
  unfold parseStreamIx at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  · simp at h_parse
  · rename_i ps_start h_expect
    have h_tok : ps_start.tokens = tokens :=
      (expect_tokens_ix _ _ _ _ h_expect).trans (by simp)
    exact parseStreamLoop_docs_from_parseDocument_ix tokens h_fpsv h_matched
      ps_start #[] .initial tokens.size docs h_tok
      (by intro d hd; simp at hd) h_parse

/-- **C2a (indexed)**: Every document produced by `parseStreamIx` from scanner
    tokens has a `Scannable` value tree. -/
theorem parseStream_output_scannable_ix
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_fpsv : FlowAwarePSVIx tokens)
    (h_matched : FlowBracketsMatchedIx tokens)
    (h_parse : parseStreamIx tokens = .ok docs) :
    ∀ doc ∈ docs.toList, Scannable doc.value false := by
  intro doc hdoc
  obtain ⟨ps, ps', h_eq, h_ok⟩ :=
    parseStream_doc_from_parseDocument_ix tokens h_fpsv h_matched docs h_parse doc hdoc
  exact parseDocument_scannable_ix tokens ps doc ps' h_fpsv h_matched h_eq h_ok

/-! ### §5f  Parser position monotonicity — Indexed

Every successfully-parsed call to `parseNode` (and its sub-parsers) returns
a state whose `.pos` is ≥ the input `.pos`. No parser function ever
*decreases* the parse position.

Indexed twin of the legacy §5f position monotonicity block. The proof
structure mirrors the legacy block; the only divergence is that the
indexed substrate uses `tokens.get?` (returning `Option`) for random
access (see Reflection 66), which adds extra `Option.match` layers to
peel inside `parseBlockMappingEntryValue` and a few other sub-parsers. -/

/-- Position monotonicity property for indexed `parseNode` at fuel ≤ n. -/
def ParseNodePosMonoIx (n : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat) (val : YamlValue) (ps' : ParseStateIx input),
    m ≤ n → parseNode ps m = .ok (val, ps') → ps'.pos ≥ ps.pos

/-- Projection helper for `ParseNodePosMonoIx`. -/
theorem parseNodePosMonoIx_apply {n : Nat} (h_ih : ParseNodePosMonoIx (input := input) n)
    {ps : ParseStateIx input} {m : Nat} {v : YamlValue × ParseStateIx input}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n := by omega) :
    v.2.pos ≥ ps.pos :=
  h_ih ps m v.1 v.2 h_le h_ok

/-- `tryConsume` doesn't decrease position. -/
theorem tryConsume_pos_mono_ix (ps : ParseStateIx input) (tok : YamlToken) :
    (ps.tryConsume tok).2.pos ≥ ps.pos := by
  unfold ParseStateIx.tryConsume
  split
  · split
    · simp [ParseStateIx.advance]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

-- `parseNodeProperties` doesn't decrease position.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
set_option linter.unusedSimpArgs false in
theorem parseNodeProperties_pos_mono_ix (ps : ParseStateIx input)
    (props : NodeProperties) (ps' : ParseStateIx input)
    (h : parseNodeProperties ps = .ok (props, ps')) :
    ps'.pos ≥ ps.pos := by
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at_ix h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at_ix h
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_hfst, rfl⟩ := h
    rename_i heq
    split at heq
    · contradiction
    · rename_i v heq_first
      cases v with
      | done x =>
        simp (config := { iota := true }) only [] at heq
        simp only [Except.ok.injEq] at heq; subst heq
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (try contradiction)
        all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq] at heq_first)
        all_goals (try cases heq_first)
        all_goals (try subst heq_first)
        all_goals (simp; try omega)
      | yield x =>
        simp (config := { iota := true }) only [] at heq
        split at heq
        · contradiction
        · rename_i v2 heq_second
          cases v2 with
          | done y =>
            simp (config := { iota := true }) only [] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp at *)
            all_goals (try subst_vars)
            try all_goals (simp [ParseStateIx.advance]; try omega)
          | yield y =>
            simp only [dite_false] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            all_goals (try simp at *)
            all_goals (try subst_vars)
            all_goals (simp [ParseStateIx.advance]; try omega)

/-! #### Block sequence position monotonicity — Indexed -/

theorem parseBlockSequenceLoop_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (items : Array YamlValue)
    (result : Array YamlValue × ParseStateIx input)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next => -- peek? = some .blockEntry
      split at h_ok
      all_goals {
        first
        | { have h_rec := ih_fuel h_ih_k ps.advance _ h_ok
            simp [ParseStateIx.advance] at h_rec; omega }
        | { split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨val, ps₃⟩ := pn_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
              have h_rec := ih_fuel h_ih_k
                { ps₃ with currentPath := _ } _ h_ok
              simp [ParseStateIx.advance] at h_rec h_pn; omega } }
    next => -- peek? ≠ blockEntry
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseBlockSequence_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_ok : parseBlockSequence ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseBlockSequenceLoop_pos_mono_ix k h_ih_k ps.advance #[] _ heq_loop
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      split <;> simp [ParseStateIx.advance] at h_loop ⊢ <;> omega

/-! #### Implicit block sequence position monotonicity — Indexed -/

theorem parseImplicitBlockSequenceLoop_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (items : Array YamlValue)
    (result : Array YamlValue × ParseStateIx input)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next =>
      split at h_ok
      all_goals {
        first
        | { have h_rec := ih_fuel h_ih_k ps.advance _ h_ok
            simp [ParseStateIx.advance] at h_rec; omega }
        | { split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨val, ps₃⟩ := pn_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
              have h_rec := ih_fuel h_ih_k
                { ps₃ with currentPath := _ } _ h_ok
              simp [ParseStateIx.advance] at h_rec h_pn; omega } }
    next =>
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseImplicitBlockSequence_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact parseImplicitBlockSequenceLoop_pos_mono_ix k h_ih_k ps #[] _ heq_loop

/-! #### Block mapping position monotonicity — Indexed

The indexed `parseBlockMappingEntryValue` uses `tokens.get?` (Option-returning)
for random access at three sites (Reflection 66), adding extra `Option.match`
layers. The proof scales up the legacy split count from ~12 to ~18 to peel
all wrappers. -/

set_option maxHeartbeats 1600000 in
theorem parseBlockMappingEntryValue_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (keyHasContent : Bool) (keyLine keyCol : Nat)
    (result : YamlValue × ParseStateIx input)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok result) :
    result.2.pos ≥ ps.pos := by
  have h_tc := tryConsume_pos_mono_ix ps .value
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- consumed = true
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- emptyNode branches
    all_goals (try {
      simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only []; omega })
    -- throw-else-parseNode
    all_goals (try {
      split at h_ok
      · contradiction
      · have h_pn := parseNodePosMonoIx_apply h_ih h_ok; simp only [] at h_pn; omega })
    -- Direct parseNode branch
    all_goals (try { have h_pn := parseNodePosMonoIx_apply h_ih h_ok; simp only [] at h_pn; omega })
  · -- consumed = false → emptyNode
    simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only []; omega

set_option maxHeartbeats 1600000 in
theorem handleBlockMappingKeyEntry_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (pairIdx : Nat)
    (result : YamlValue × YamlValue × ParseStateIx input)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok result) :
    result.2.2.pos ≥ ps.pos := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> first | contradiction | skip
  all_goals (try (simp only [emptyNode] at h_ok))
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (subst h_ok; simp only [])
  all_goals (try {
    have h_bev := parseBlockMappingEntryValue_pos_mono_ix fuel h_ih
      _ _ _ _ _ (by assumption)
    simp [ParseStateIx.advance] at h_bev ⊢; omega })
  all_goals {
    have h_key := parseNodePosMonoIx_apply h_ih (by assumption)
    have h_bev := parseBlockMappingEntryValue_pos_mono_ix fuel h_ih
      _ _ _ _ _ (by assumption)
    simp [ParseStateIx.advance] at h_key h_bev ⊢; omega }

theorem handleBlockMappingValueEntry_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (pairIdx : Nat)
    (result : YamlValue × ParseStateIx input)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  all_goals try {
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    simp [ParseStateIx.advance] }
  next =>
    split at h_ok
    next => simp at h_ok
    next pn_res heq_pn =>
      obtain ⟨val, ps'⟩ := pn_res; try dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
      simp [ParseStateIx.advance] at h_pn ⊢; omega

theorem parseBlockMappingLoop_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨key, val, ps_entry⟩ := entry_res; try dsimp only [] at h_ok
        have h_entry := handleBlockMappingKeyEntry_pos_mono_ix k h_ih_k ps _ _ heq_entry
        have h_rec := ih_fuel h_ih_k ps_entry _ h_ok
        simp only [] at h_entry; omega
    · split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨val, ps_entry⟩ := entry_res; try dsimp only [] at h_ok
        have h_entry := handleBlockMappingValueEntry_pos_mono_ix k h_ih_k ps _ _ heq_entry
        have h_rec := ih_fuel h_ih_k ps_entry _ h_ok
        simp only [] at h_entry; omega
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseBlockMapping_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_ok : parseBlockMapping ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseBlockMappingLoop_pos_mono_ix k h_ih_k ps.advance #[] _ heq_loop
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      split <;> simp [ParseStateIx.advance] at h_loop ⊢ <;> omega

/-! #### Flow mapping helpers position monotonicity — Indexed -/

set_option maxHeartbeats 1600000 in
theorem parseFlowMappingValue_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (savedPath : YamlPath) (keyContent : String)
    (result : YamlValue × ParseStateIx input)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  generalize h_ps1_def : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseStateIx input) = ps1 at h_ok
  have h_ps1_pos : ps1.pos = ps.pos := by rw [← h_ps1_def]
  generalize h_tc1 : ps1.tryConsume .key = tc1 at h_ok
  have h_tc1_pos := tryConsume_pos_mono_ix ps1 .key
  rw [h_tc1] at h_tc1_pos
  generalize h_tc2 : tc1.2.tryConsume .value = tc2 at h_ok
  have h_tc2_pos := tryConsume_pos_mono_ix tc1.2 .value
  rw [h_tc2] at h_tc2_pos
  split at h_ok <;> first | contradiction | skip
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  all_goals (try {
    simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only []; omega })
  all_goals (try {
    have h_pn := parseNodePosMonoIx_apply h_ih h_ok
    simp only [] at h_pn; omega })
  all_goals {
    try dsimp only [] at h_ok
    try simp only [Except.ok.injEq] at h_ok
    try (split at h_ok <;> first | contradiction | skip)
    try dsimp only [] at h_ok
    try simp only [Except.ok.injEq] at h_ok
    subst h_ok; try simp only []
    first | omega | { simp only [ParseStateIx.advance]; omega }
          | { try simp only [] at h_tc1_pos h_tc2_pos h_ps1_pos
              try simp only [ParseStateIx.advance] at h_tc1_pos h_tc2_pos h_ps1_pos
              omega }
          | { have h_pn := parseNodePosMonoIx_apply h_ih (by assumption)
              try simp only [] at h_tc1_pos h_tc2_pos h_ps1_pos h_pn
              omega } }

theorem parseExplicitKey_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input)
    (result : YamlValue × ParseStateIx input)
    (h_ok : parseExplicitKey ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals try {
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _ }
  next => exact parseNodePosMonoIx_apply h_ih h_ok

set_option maxHeartbeats 3200000 in
theorem parseSinglePairMapping_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_ok : parseSinglePairMapping ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    simp only [emptyNode] at h_ok
    split at h_ok <;> first | contradiction | skip
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals try {
      generalize h_tc : ParseStateIx.tryConsume _ YamlToken.value = tc at h_ok
      obtain ⟨tc_consumed, tc_ps⟩ := tc
      have h_tc_pos : tc_ps.pos ≥ ps.pos := by
        show (tc_consumed, tc_ps).snd.pos ≥ ps.pos
        rw [← h_tc]
        apply Nat.le_trans _ (tryConsume_pos_mono_ix _ .value)
        try simp only []
        first
          | { simp only [ParseStateIx.advance]; omega }
          | omega
          | { have := parseNodePosMonoIx_apply h_ih_k (by assumption)
              simp only [ParseStateIx.advance] at this; omega }
          | { try simp only [ParseStateIx.advance]
              try { have := parseNodePosMonoIx_apply h_ih_k (by assumption)
                    try simp only [ParseStateIx.advance] at this }
              omega }
    }
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals try {
      generalize h_tc : ParseStateIx.tryConsume _ YamlToken.value = tc at h_ok
      have h_tc_pos : tc.snd.pos ≥ ps.pos := by
        rw [← h_tc]
        apply Nat.le_trans _ (tryConsume_pos_mono_ix _ .value)
        try simp only []
        first
          | { simp only [ParseStateIx.advance]; omega }
          | omega
          | { have := parseNodePosMonoIx_apply h_ih_k (by assumption)
              simp only [ParseStateIx.advance] at this; omega }
    }
    all_goals {
      try dsimp only [] at h_ok
      first
      | { simp only [Except.ok.injEq] at h_ok; rw [← h_ok]; simp only []
          first
            | omega
            | { have := parseNodePosMonoIx_apply h_ih_k (by assumption)
                simp only [ParseStateIx.advance] at *; omega }
            | { simp only [ParseStateIx.tryConsume, ParseStateIx.advance]
                split <;> (try split)
                all_goals { simp only []; first | omega | { have := parseNodePosMonoIx_apply h_ih_k (by assumption); simp only [ParseStateIx.advance] at this; omega } } }
            | { have h1 := parseNodePosMonoIx_apply h_ih_k (by assumption)
                apply Nat.le_trans _ h1
                apply Nat.le_trans _ (tryConsume_pos_mono_ix _ .value)
                try simp only []
                simp only [ParseStateIx.advance]; omega } }
      | { split at h_ok <;> first | contradiction | skip
          all_goals try dsimp only [] at h_ok
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals {
            try simp only [] at h_tc_pos
            simp only [Except.ok.injEq] at h_ok; rw [← h_ok]; simp only []
            first
              | omega
              | { exact h_tc_pos }
              | { have := parseNodePosMonoIx_apply h_ih_k (by assumption)
                  try simp only [ParseStateIx.advance] at this
                  try simp only [] at h_tc_pos
                  omega }
              | { apply Nat.le_trans _ (parseNodePosMonoIx_apply h_ih_k (by assumption))
                  apply Nat.le_trans _ (tryConsume_pos_mono_ix _ .value)
                  simp only []
                  apply Nat.le_trans _ (parseNodePosMonoIx_apply h_ih_k (by assumption))
                  simp only [ParseStateIx.advance]; omega }
              | { simp only [ParseStateIx.tryConsume, ParseStateIx.advance]
                  split <;> (try split)
                  all_goals (try simp only [])
                  all_goals {
                    first
                      | omega
                      | { have := parseNodePosMonoIx_apply h_ih_k (by assumption)
                          try simp only [ParseStateIx.advance] at this
                          omega } } }
              | { have h1 := parseNodePosMonoIx_apply h_ih_k (by assumption)
                  apply Nat.le_trans _ h1
                  apply Nat.le_trans _ (tryConsume_pos_mono_ix _ .value)
                  try simp only []
                  try simp only [ParseStateIx.advance]
                  omega }
              | { apply Nat.le_trans _ (tryConsume_pos_mono_ix _ .value)
                  try simp only []
                  have h1 := parseNodePosMonoIx_apply h_ih_k (by assumption)
                  try simp only [ParseStateIx.advance] at h1
                  omega } } } }

/-! #### Flow sequence position monotonicity — Indexed -/

set_option maxHeartbeats 1600000 in
theorem parseFlowSequenceLoop_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (items : Array YamlValue)
    (result : Array YamlValue × ParseStateIx input)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
    · split at h_ok
      · split at h_ok
        · split at h_ok
          · split at h_ok
            · simp at h_ok
            · rename_i spm_res heq_spm
              obtain ⟨mapVal, ps_spm⟩ := spm_res; try dsimp only [] at h_ok
              have h_spm := parseSinglePairMapping_pos_mono_ix k h_ih_k _ _ heq_spm
              have h_rec := ih_fuel h_ih_k
                { ps_spm with currentPath := _ } _ h_ok
              simp [ParseStateIx.advance] at h_rec h_spm; omega
          · simp only [Except.ok.injEq] at h_ok; subst h_ok
            simp [ParseStateIx.advance]
          · split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
              have h_rec := ih_fuel h_ih_k
                { ps_pn with currentPath := _ } _ h_ok
              simp [ParseStateIx.advance] at h_rec h_pn; omega
        · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
      · split at h_ok
        · split at h_ok
          · simp at h_ok
          · rename_i spm_res heq_spm
            obtain ⟨mapVal, ps_spm⟩ := spm_res; try dsimp only [] at h_ok
            have h_spm := parseSinglePairMapping_pos_mono_ix k h_ih_k _ _ heq_spm
            have h_rec := ih_fuel h_ih_k
              { ps_spm with currentPath := _ } _ h_ok
            simp at h_rec h_spm ⊢; omega
        · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
        · split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
            have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
            have h_rec := ih_fuel h_ih_k
              { ps_pn with currentPath := _ } _ h_ok
            simp at h_rec h_pn ⊢; omega

theorem parseFlowSequence_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_ok : parseFlowSequence ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseFlowSequenceLoop_pos_mono_ix k h_ih_k ps.advance #[] _ heq_loop
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        simp [ParseStateIx.advance] at h_loop ⊢; omega
      · simp at h_ok

/-! #### Flow mapping position monotonicity — Indexed -/

set_option maxHeartbeats 1600000 in
theorem parseFlowMappingLoop_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
    · split at h_ok
      · split at h_ok
        · split at h_ok
          · simp only [Except.ok.injEq] at h_ok; subst h_ok
            simp [ParseStateIx.advance]
          · split at h_ok
            · simp at h_ok
            · rename_i ek_res heq_ek
              obtain ⟨key_val, ps_ek⟩ := ek_res; try dsimp only [] at h_ok
              split at h_ok
              · simp at h_ok
              · rename_i fmv_res heq_fmv
                obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
                have h_ek := parseExplicitKey_pos_mono_ix k h_ih_k _ _ heq_ek
                have h_fmv := parseFlowMappingValue_pos_mono_ix k h_ih_k _ _ _ _ heq_fmv
                have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
                simp [ParseStateIx.advance] at h_ek h_fmv ⊢; omega
          · split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨key_val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
              split at h_ok
              · simp at h_ok
              · rename_i fmv_res heq_fmv
                obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
                have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
                have h_fmv := parseFlowMappingValue_pos_mono_ix k h_ih_k _ _ _ _ heq_fmv
                have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
                simp [ParseStateIx.advance] at h_pn h_fmv ⊢; omega
        · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
      · split at h_ok
        · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
        · split at h_ok
          · simp at h_ok
          · rename_i ek_res heq_ek
            obtain ⟨key_val, ps_ek⟩ := ek_res; try dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i fmv_res heq_fmv
              obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
              have h_ek := parseExplicitKey_pos_mono_ix k h_ih_k _ _ heq_ek
              have h_fmv := parseFlowMappingValue_pos_mono_ix k h_ih_k _ _ _ _ heq_fmv
              have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
              simp [ParseStateIx.advance] at h_ek h_fmv ⊢; omega
        · split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨key_val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i fmv_res heq_fmv
              obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMonoIx_apply h_ih heq_pn
              have h_fmv := parseFlowMappingValue_pos_mono_ix k h_ih_k _ _ _ _ heq_fmv
              have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
              simp at h_pn h_fmv ⊢; omega

theorem parseFlowMapping_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (result : YamlValue × ParseStateIx input)
    (h_ok : parseFlowMapping ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMonoIx (input := input) k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseFlowMappingLoop_pos_mono_ix k h_ih_k ps.advance #[] _ heq_loop
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        simp [ParseStateIx.advance] at h_loop ⊢; omega
      · simp at h_ok

/-! #### Content dispatch and main induction — Indexed -/

theorem parseNodeContent_pos_mono_ix (fuel : Nat)
    (h_ih : ParseNodePosMonoIx (input := input) fuel)
    (ps : ParseStateIx input) (props : NodeProperties)
    (result : YamlValue × ParseStateIx input)
    (h_ok : parseNodeContent ps fuel props = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; simp [ParseStateIx.advance]
  · exact parseBlockSequence_pos_mono_ix fuel h_ih ps result h_ok
  · exact parseBlockMapping_pos_mono_ix fuel h_ih ps result h_ok
  · exact parseImplicitBlockSequence_pos_mono_ix fuel h_ih ps result h_ok
  · exact parseFlowSequence_pos_mono_ix fuel h_ih ps result h_ok
  · exact parseFlowMapping_pos_mono_ix fuel h_ih ps result h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseNode_pos_mono_all_ix : ∀ n, ParseNodePosMonoIx (input := input) n := by
  intro n
  induction n with
  | zero =>
    intro ps m val ps' h_le h_ok
    have : m = 0 := by omega
    subst this
    unfold parseNode at h_ok
    simp at h_ok
  | succ k ih =>
    intro ps m val ps' h_le h_ok
    by_cases h_eq : m = k + 1
    · subst h_eq
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      split at h_ok
      · split at h_ok
        · simp at h_ok
        · simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
          split <;> simp_all [ParseStateIx.advance] <;> omega
      · split at h_ok
        · simp at h_ok
        · rename_i props_res heq_props
          obtain ⟨props, ps_props⟩ := props_res
          try dsimp only [] at h_ok
          split at h_ok
          · simp at h_ok
          · try dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i content_res heq_content
              obtain ⟨content_val, ps_content⟩ := content_res
              try dsimp only [] at h_ok
              simp only [Except.ok.injEq] at h_ok
              have h_props := parseNodeProperties_pos_mono_ix ps props ps_props heq_props
              have h_content := parseNodeContent_pos_mono_ix k ih ps_props props _ heq_content
              have h_ps := congrArg Prod.snd h_ok
              simp only [] at h_ps
              rw [show ps'.pos = ps_content.pos from by rw [← h_ps]; exact applyNodeFinalization_pos_ix ..]
              simp only [] at h_content h_props
              omega
    · exact ih ps m val ps' (by omega) h_ok

/-! #### Emitter-specific strict position advancement — Indexed

`parseNode` strictly advances position when applied to one of the
emitter-produced "content-start" tokens: a double-quoted scalar, a
flow sequence start, or a flow mapping start.  This is the predicate
discharged at the loop body in
`parseFlowSequenceLoop_emitter_ok` / `parseFlowMappingLoop_emitter_ok`. -/

set_option maxHeartbeats 1600000 in
theorem parseNode_emitter_advances_ix (ps : ParseStateIx input) (fuel : Nat)
    (val : YamlValue) (ps' : ParseStateIx input)
    (h_ok : parseNode ps (fuel + 1) = .ok (val, ps'))
    (h_emit_tok : (∃ s, ps.peek? = some (.scalar s .doubleQuoted)) ∨
                  ps.peek? = some .flowSequenceStart ∨
                  ps.peek? = some .flowMappingStart) :
    ps'.pos > ps.pos := by
  unfold parseNode at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · rename_i h_peek_alias
    rcases h_emit_tok with ⟨s, h_s⟩ | h_fs | h_fm
    · simp [h_peek_alias] at h_s
    · simp [h_peek_alias] at h_fs
    · simp [h_peek_alias] at h_fm
  · split at h_ok
    · simp at h_ok
    · rename_i props_res heq_props
      obtain ⟨props, ps_props⟩ := props_res
      try dsimp only [] at h_ok
      have h_props_pos := parseNodeProperties_pos_mono_ix ps props ps_props heq_props
      split at h_ok
      · simp at h_ok
      · try dsimp only [] at h_ok
        split at h_ok
        · simp at h_ok
        · rename_i content_res heq_content
          obtain ⟨content_val, ps_content⟩ := content_res
          try dsimp only [] at h_ok
          simp only [Except.ok.injEq] at h_ok
          have h_val := congrArg Prod.fst h_ok
          have h_ps := congrArg Prod.snd h_ok
          simp only [] at h_val h_ps
          rw [show ps'.pos = ps_content.pos from by rw [← h_ps]; exact applyNodeFinalization_pos_ix ..]
          unfold parseNodeContent at heq_content
          split at heq_content
          · simp only [Except.ok.injEq] at heq_content
            obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
            simp [ParseStateIx.advance]; omega
          · unfold parseBlockSequence at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨items, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseBlockSequenceLoop_pos_mono_ix _ (parseNode_pos_mono_all_ix _) ps_props.advance #[] _ heq_loop
                simp only [Except.ok.injEq] at heq_content
                obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                split <;> simp [ParseStateIx.advance] at h_loop ⊢ <;> omega
          · unfold parseBlockMapping at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨pairs, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseBlockMappingLoop_pos_mono_ix _ (parseNode_pos_mono_all_ix _) ps_props.advance #[] _ heq_loop
                simp only [Except.ok.injEq] at heq_content
                obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                split <;> simp [ParseStateIx.advance] at h_loop ⊢ <;> omega
          · -- blockEntry → implicit block sequence (contradicts emit tokens)
            rcases Nat.lt_or_ge ps.pos ps_props.pos with h_strict | h_le
            · have h_ibs := parseImplicitBlockSequence_pos_mono_ix fuel (parseNode_pos_mono_all_ix fuel) ps_props _ heq_content
              simp only [] at h_ibs; omega
            · have h_eq_pos : ps_props.pos = ps.pos := by omega
              have h_tok := parseNodeProperties_tokens_ix ps props ps_props heq_props
              have h_peek_eq : ps_props.peek? = ps.peek? := by
                simp only [ParseStateIx.peek?, ParseStateIx.peekIx?]
                rw [h_tok, h_eq_pos]
              rename_i h_peek_be _
              rcases h_emit_tok with ⟨s, h_s⟩ | h_fs | h_fm
              · rw [← h_peek_eq] at h_s; simp_all
              · rw [← h_peek_eq] at h_fs; simp_all
              · rw [← h_peek_eq] at h_fm; simp_all
          · unfold parseFlowSequence at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨items, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseFlowSequenceLoop_pos_mono_ix _ (parseNode_pos_mono_all_ix _) ps_props.advance #[] _ heq_loop
                split at heq_content
                · simp only [Except.ok.injEq] at heq_content
                  obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                  simp [ParseStateIx.advance] at h_loop ⊢; omega
                · simp at heq_content
          · unfold parseFlowMapping at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨pairs, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseFlowMappingLoop_pos_mono_ix _ (parseNode_pos_mono_all_ix _) ps_props.advance #[] _ heq_loop
                split at heq_content
                · simp only [Except.ok.injEq] at heq_content
                  obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                  simp [ParseStateIx.advance] at h_loop ⊢; omega
                · simp at heq_content
          · -- empty node: contradicts emitter tokens
            simp only [Except.ok.injEq] at heq_content
            obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
            suffices h_gt : ps_props.pos > ps.pos by omega
            rcases Nat.lt_or_ge ps.pos ps_props.pos with h_lt | h_le
            · exact h_lt
            · exfalso
              have h_eq_pos : ps_props.pos = ps.pos := by omega
              have h_tok := parseNodeProperties_tokens_ix ps props ps_props heq_props
              have h_peek_eq : ps_props.peek? = ps.peek? := by
                simp only [ParseStateIx.peek?, ParseStateIx.peekIx?]
                rw [h_tok, h_eq_pos]
              rename_i h_not_scalar h_not_bss h_not_bms h_not_be h_not_fss h_not_fms
              rcases h_emit_tok with ⟨s, h_s⟩ | h_fs | h_fm
              all_goals { rw [← h_peek_eq] at *; simp_all }

/-! ### §5d₃ Wadler "theorems for free" for `parseFlowMappingLoop` — Indexed -/

set_option maxHeartbeats 800000 in
/-- Monotonicity: indexed `parseFlowMappingLoop` never shrinks the pairs array.
    Indexed twin of legacy `parseFlowMappingLoop_pairs_grow`. -/
theorem parseFlowMappingLoop_pairs_grow_ix
    (ps : ParseStateIx input) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseStateIx input)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    result.1.size ≥ pairs.size := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    cases h_ok; simp
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok
      cases h_ok; simp
    · all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try contradiction)
      all_goals (try (simp at h_ok))
      all_goals (first
        | (cases h_ok; simp)
        | (simp only [Except.ok.injEq] at h_ok; cases h_ok; simp)
        | (have h_rec := ih_fuel _ _ h_ok
           simp [Array.size_push] at h_rec ⊢
           omega))

/-! ### §5f Flow loop emitter-acceptance bridge lemmas — Indexed

These lemmas mirror the legacy emitter-bridge block at
`ParserWellBehaved.lean` lines 4095–4673. At Step 6f cutover the
`_ix` suffix drops and `EmitterScannability.lean` consumes them via
the legacy names (`peek_some_val`, `ParseNodeFlowSeqOk`,
`parseFlowSequenceLoop_emitter_ok`, `ParseEntryFlowMapOk`,
`parseFlowMappingLoop_emitter_ok`). -/

/-- Flow bracket balance over an indexed token stream from position
    `lo` to `hi` (exclusive). Indexed twin of
    `ParserGrammableBase.flowBracketBalance`. -/
def flowBracketBalanceIx (tokens : Indexed.TokenStream input) (lo hi : Nat) : Int :=
  if lo ≥ hi then 0
  else
    let slice := tokens.tokens.toList.drop lo |>.take (hi - lo)
    slice.foldl (fun acc t => acc + flowBracketDelta t.token) 0

theorem flowBracketBalanceIx_compose (tokens : Indexed.TokenStream input)
    (lo mid hi : Nat) (h_lm : lo ≤ mid) (h_mh : mid ≤ hi) :
    flowBracketBalanceIx tokens lo hi =
      flowBracketBalanceIx tokens lo mid + flowBracketBalanceIx tokens mid hi := by
  by_cases h1 : lo = mid
  · subst h1; simp [flowBracketBalanceIx]
  · by_cases h2 : mid = hi
    · subst h2; simp [flowBracketBalanceIx]
    · have h_lo_lt_hi : ¬(lo ≥ hi) := by omega
      have h_lo_lt_mid : ¬(lo ≥ mid) := by omega
      have h_mid_lt_hi : ¬(mid ≥ hi) := by omega
      simp only [flowBracketBalanceIx, h_lo_lt_hi, h_lo_lt_mid, h_mid_lt_hi, ↓reduceIte]
      have h_eq : hi - lo = (mid - lo) + (hi - mid) := by omega
      rw [h_eq, List.take_add, List.foldl_append, foldl_add_shift]
      congr 1
      rw [List.drop_drop, show lo + (mid - lo) = mid from by omega]

theorem flowBracketBalanceIx_single (tokens : Indexed.TokenStream input)
    (i : Nat) (h : i < tokens.tokens.toList.length) :
    flowBracketBalanceIx tokens i (i + 1) = flowBracketDelta tokens.tokens.toList[i].token := by
  simp only [flowBracketBalanceIx, show ¬(i ≥ i + 1) from by omega, ↓reduceIte,
             show i + 1 - i = 1 from by omega]
  rw [List.drop_eq_getElem_cons h]
  simp [List.foldl]

theorem flowBracketBalanceIx_compose_zero (tokens : Indexed.TokenStream input)
    (body_start pos pos_after : Nat)
    (h_bs_pos : body_start ≤ pos)
    (h_pos_bound : pos < tokens.tokens.toList.length)
    (h_pos_after : pos + 1 ≤ pos_after)
    (h_bal : flowBracketBalanceIx tokens body_start pos = 0)
    (h_delta : flowBracketDelta tokens.tokens.toList[pos].token = 0)
    (h_tail : flowBracketBalanceIx tokens (pos + 1) pos_after = 0) :
    flowBracketBalanceIx tokens body_start pos_after = 0 := by
  rw [flowBracketBalanceIx_compose tokens body_start (pos + 1) pos_after (by omega) h_pos_after,
      flowBracketBalanceIx_compose tokens body_start pos (pos + 1) h_bs_pos (by omega),
      h_bal, h_tail, flowBracketBalanceIx_single _ _ h_pos_bound, h_delta]; omega

/-- The indexed twin of `peek_some_val`: if `ps.peek? = some tok`,
    then `ps.pos < ps.tokens.size` and the token at `ps.pos` carries
    that value. Replaces legacy `.val` with indexed `.token`. -/
theorem peek_some_val_ix {ps : ParseStateIx input} {tok : YamlToken}
    (h_peek : ps.peek? = some tok) :
    ps.pos < ps.tokens.size ∧ (ps.tokens.tokens[ps.pos]!).token = tok := by
  unfold ParseStateIx.peek? ParseStateIx.peekIx? at h_peek
  simp only [Indexed.TokenStream.get?, Option.map_eq_some_iff] at h_peek
  obtain ⟨t, h_t_eq, h_tok_eq⟩ := h_peek
  have h_lt : ps.pos < ps.tokens.tokens.size := by
    by_cases h_lt : ps.pos < ps.tokens.tokens.size
    · exact h_lt
    · exfalso
      have h_ge' : ps.tokens.tokens.size ≤ ps.pos := Nat.le_of_not_lt h_lt
      have h_none : ps.tokens.tokens[ps.pos]? = none := Array.getElem?_eq_none h_ge'
      rw [h_none] at h_t_eq
      cases h_t_eq
  have h_size : ps.tokens.tokens.size = ps.tokens.size := rfl
  refine ⟨by rw [← h_size]; exact h_lt, ?_⟩
  have h_pos : ps.tokens.tokens[ps.pos]? = some ps.tokens.tokens[ps.pos] :=
    Array.getElem?_eq_getElem h_lt
  rw [h_t_eq] at h_pos
  have h_pos' : ps.tokens.tokens[ps.pos] = t := by
    have := h_pos.symm
    simpa using this
  have h_eq : ps.tokens.tokens[ps.pos]! = t := by
    rw [getElem!_pos ps.tokens.tokens ps.pos h_lt]
    exact h_pos'
  rw [h_eq, h_tok_eq]

/-- The indexed twin of `peek_of_pos_val`: if `ps.pos = k`, position
    `k` is in bounds, and the token at `k` has value `tok`, then
    `ps.peek? = some tok`. -/
theorem peek_of_pos_val_ix {ps : ParseStateIx input} {k : Nat} {tok : YamlToken}
    (h_pos : ps.pos = k) (h_bound : k < ps.tokens.size)
    (h_val : (ps.tokens.tokens[k]!).token = tok) :
    ps.peek? = some tok := by
  unfold ParseStateIx.peek? ParseStateIx.peekIx?
  simp only [Indexed.TokenStream.get?, h_pos]
  have h_lt : k < ps.tokens.tokens.size := h_bound
  rw [Array.getElem?_eq_getElem h_lt]
  simp only [Option.map_some]
  rw [← getElem!_pos ps.tokens.tokens k h_lt]
  exact congrArg some h_val

/-- The indexed twin of `ParseNodeFlowSeqOk`. -/
def ParseNodeFlowSeqOkIx (tokens : Indexed.TokenStream input)
    (endPos : Nat) (fuel : Nat) (body_start : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat),
    ps.tokens = tokens → 0 < m → m ≤ fuel →
    ps.pos < endPos →
    body_start ≤ ps.pos →
    flowBracketBalanceIx tokens body_start ps.pos = 0 →
    ((∃ c s, ps.peek? = some (.scalar c s)) ∨
     ps.peek? = some .flowSequenceStart ∨
     ps.peek? = some .flowMappingStart) →
    ∃ val ps', parseNode ps m = .ok (val, ps') ∧
              ps'.pos > ps.pos ∧ ps'.pos ≤ endPos ∧
              ps'.tokens = tokens ∧
              ps'.trackPositions = ps.trackPositions ∧
              (ps'.peek? = some .flowEntry ∨
               (ps'.peek? = some .flowSequenceEnd ∧ ps'.pos = endPos)) ∧
              flowBracketBalanceIx tokens ps.pos ps'.pos = 0

theorem ParseNodeFlowSeqOkIx.mono {tokens : Indexed.TokenStream input}
    {endPos fuel fuel' body_start}
    (h : ParseNodeFlowSeqOkIx (input := input) tokens endPos fuel body_start)
    (h_le : fuel' ≤ fuel) :
    ParseNodeFlowSeqOkIx (input := input) tokens endPos fuel' body_start :=
  fun ps m h_tok h_pos_m h_m h_pos h_bs h_depth h_cs =>
    let ⟨v, ps', hok, hadv, hbound, htok, htp, hpeek, hbal⟩ :=
      h ps m h_tok h_pos_m (Nat.le_trans h_m h_le) h_pos h_bs h_depth h_cs
    ⟨v, ps', hok, hadv, hbound, htok, htp, hpeek, hbal⟩

set_option maxHeartbeats 3200000 in
theorem parseFlowSequenceLoop_emitter_ok_ix (fuel : Nat)
    (ps : ParseStateIx input) (items_acc : Array YamlValue) (endPos : Nat)
    (body_start : Nat)
    (h_pn : ParseNodeFlowSeqOkIx (input := input) ps.tokens endPos fuel body_start)
    (h_fuel : fuel > endPos - ps.pos)
    (h_pos : ps.pos ≤ endPos)
    (h_end_pos : endPos < ps.tokens.size)
    (h_end_tok : (ps.tokens.tokens[endPos]!).token = .flowSequenceEnd)
    (h_at_end : ps.peek? = some .flowSequenceEnd → ps.pos = endPos)
    (h_entry : items_acc.size > 0 →
               ps.peek? = some .flowEntry ∨ ps.peek? = some .flowSequenceEnd)
    (h_content_start : ps.pos < endPos → items_acc.size = 0 →
        (∃ c s, ps.peek? = some (.scalar c s)) ∨
        ps.peek? = some .flowSequenceStart ∨
        ps.peek? = some .flowMappingStart)
    (h_after_fe : ∀ k : Nat, ps.pos ≤ k → k < endPos →
                  (ps.tokens.tokens[k]!).token = .flowEntry →
                  flowBracketBalanceIx ps.tokens body_start k = 0 →
                  k + 1 ≤ endPos ∧
                  ((∃ c s, (ps.tokens.tokens[k + 1]!).token = .scalar c s) ∨
                   (ps.tokens.tokens[k + 1]!).token = .flowSequenceStart ∨
                   (ps.tokens.tokens[k + 1]!).token = .flowMappingStart))
    (h_bal : flowBracketBalanceIx ps.tokens body_start ps.pos = 0)
    (h_bs : body_start ≤ ps.pos)
    : ∃ items ps', parseFlowSequenceLoop ps fuel items_acc = .ok (items, ps') ∧
                   ps'.peek? = some .flowSequenceEnd ∧
                   ps'.pos = endPos ∧
                   ps'.tokens = ps.tokens ∧
                   ps'.trackPositions = ps.trackPositions := by
  induction fuel generalizing ps items_acc with
  | zero =>
    have h_eq : ps.pos = endPos := by omega
    unfold parseFlowSequenceLoop
    refine ⟨items_acc, ps, rfl, ?_, h_eq, rfl, rfl⟩
    exact peek_of_pos_val_ix h_eq (by omega) h_end_tok
  | succ n ih =>
    unfold parseFlowSequenceLoop
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · exact ⟨items_acc, ps, rfl, ‹_›, h_at_end ‹_›, rfl, rfl⟩
    · rename_i h_outer_not_end
      have h_lt : ps.pos < endPos := by
        rcases Nat.eq_or_lt_of_le h_pos with h_eq | h_lt
        · exfalso; exact h_outer_not_end (peek_of_pos_val_ix h_eq (by omega) h_end_tok)
        · exact h_lt
      split
      · -- items_acc.size > 0
        split
        · -- flowEntry → advance
          split
          · -- key after separator → contradiction
            rename_i h_adv_key
            exfalso
            have ⟨_, h_val⟩ := peek_some_val_ix h_adv_key
            simp [ParseStateIx.advance] at h_val
            have h_fe_val : (ps.tokens.tokens[ps.pos]!).token = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val_ix h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) (by omega) h_fe_val h_bal
            rcases h_afe.2 with ⟨c, s, hcs⟩ | hcs | hcs <;> rw [h_val] at hcs <;> cases hcs
          · -- flowSequenceEnd after separator → contradiction
            rename_i h_adv_end
            exfalso
            have h_fe_val : (ps.tokens.tokens[ps.pos]!).token = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val_ix h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) (by omega) h_fe_val h_bal
            have ⟨_, h_val⟩ := peek_some_val_ix h_adv_end
            simp [ParseStateIx.advance] at h_val
            rcases h_afe.2 with ⟨c, s, hcs⟩ | hcs | hcs <;> rw [h_val] at hcs <;> cases hcs
          · -- other → parseNode + recurse
            rename_i h_adv_not_key h_adv_not_end
            have h_fe_val : (ps.tokens.tokens[ps.pos]!).token = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val_ix h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) (by omega) h_fe_val h_bal
            have h_adv_pos_lt : ps.pos + 1 < endPos := by
              rcases Nat.eq_or_lt_of_le h_afe.1 with heq | hlt
              · exfalso; apply h_adv_not_end
                show ps.advance.peek? = some .flowSequenceEnd
                apply peek_of_pos_val_ix (ps := ps.advance) (k := endPos)
                · simp [ParseStateIx.advance]; exact heq
                · exact h_end_pos
                · simp [ParseStateIx.advance]; exact h_end_tok
              · exact hlt
            generalize hPsX : ({ ps.advance with
              currentPath := Array.push ps.advance.currentPath
                (PathSegment.index items_acc.size) } : ParseStateIx input) = psX
            have h_psX_tok : psX.tokens = ps.tokens := by
              rw [← hPsX]; simp [ParseStateIx.advance]
            have h_psX_pos : psX.pos = ps.pos + 1 := by
              rw [← hPsX]; simp [ParseStateIx.advance]
            have h_psX_peek : psX.peek? = ps.advance.peek? := by
              rw [← hPsX]; simp [ParseStateIx.advance, ParseStateIx.peek?, ParseStateIx.peekIx?]
            have h_psX_tp : psX.trackPositions = ps.trackPositions := by
              rw [← hPsX]; simp [ParseStateIx.advance]
            have h_cs : (∃ c s, psX.peek? = some (.scalar c s)) ∨
                psX.peek? = some .flowSequenceStart ∨
                psX.peek? = some .flowMappingStart := by
              rw [h_psX_peek]
              have h_bound : ps.pos + 1 < ps.tokens.size := by omega
              have h_bound' : ps.pos + 1 < ps.tokens.tokens.size := h_bound
              have h_adv_peek : ps.advance.peek? = some (ps.tokens.tokens[ps.pos + 1]!).token := by
                apply peek_of_pos_val_ix (ps := ps.advance) (k := ps.pos + 1)
                · simp [ParseStateIx.advance]
                · exact h_bound
                · simp [ParseStateIx.advance]
              rcases h_afe.2 with ⟨c, s, hcs⟩ | hcs | hcs
              · exact .inl ⟨c, s, by rw [h_adv_peek, hcs]⟩
              · exact .inr (.inl (by rw [h_adv_peek, hcs]))
              · exact .inr (.inr (by rw [h_adv_peek, hcs]))
            have h_depth_at_adv : flowBracketBalanceIx ps.tokens body_start (ps.pos + 1) = 0 := by
              have h_pos_bound : ps.pos < ps.tokens.tokens.toList.length := by
                show ps.pos < ps.tokens.size; omega
              rw [flowBracketBalanceIx_compose ps.tokens body_start ps.pos (ps.pos + 1) h_bs (by omega),
                  h_bal, flowBracketBalanceIx_single _ _ h_pos_bound]
              have h_eq : (ps.tokens.tokens.toList[ps.pos]'h_pos_bound).token = YamlToken.flowEntry := by
                show (ps.tokens.tokens[ps.pos]'(show ps.pos < ps.tokens.size by omega)).token = YamlToken.flowEntry
                rw [← getElem!_pos ps.tokens.tokens ps.pos (show ps.pos < ps.tokens.size by omega)]
                exact h_fe_val
              rw [h_eq]; decide
            obtain ⟨val, ps_after, h_ok, h_pos_adv, h_pos_bound, h_tok_eq, h_tp_eq, h_peek_after, h_pn_bal⟩ :=
              h_pn psX n h_psX_tok (by omega) (by omega)
                (by rw [h_psX_pos]; exact h_adv_pos_lt)
                (by rw [h_psX_pos]; omega)
                (by rw [h_psX_pos]; exact h_depth_at_adv)
                h_cs
            rw [h_ok]; dsimp only []
            have h_rec_tok : ({ ps_after with
              currentPath := ps.advance.currentPath } : ParseStateIx input).tokens =
              ps.tokens := h_tok_eq
            obtain ⟨items_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res, h_tp_res⟩ :=
              ih { ps_after with currentPath := ps.advance.currentPath }
                (items_acc.push val)
                (by rw [h_rec_tok]; exact h_pn.mono (by omega))
                (by dsimp only []; omega)
                (by exact h_pos_bound)
                (by rw [h_rec_tok]; exact h_end_pos)
                (by rw [h_rec_tok]; exact h_end_tok)
                (by intro h_end
                    rcases h_peek_after with h_fe | ⟨_, h_pos_eq⟩
                    · have : ps_after.peek? = some .flowSequenceEnd := h_end
                      rw [h_fe] at this; cases this
                    · exact h_pos_eq)
                (by intro _; exact h_peek_after.imp id And.left)
                (by intro h_sz h_empty; simp [Array.size_push] at h_empty)
                (by intro k hk1 hk2 hval h_depth; dsimp only [] at hk1 h_depth;
                    rw [h_tok_eq] at h_depth; rw [h_rec_tok] at hval ⊢;
                    exact h_after_fe k (by omega) hk2 hval h_depth)
                (by rw [h_rec_tok]
                    have h_pn_bal' : flowBracketBalanceIx ps.tokens psX.pos ps_after.pos = 0 :=
                      h_psX_tok ▸ h_pn_bal
                    rw [h_psX_pos] at h_pn_bal'
                    exact flowBracketBalanceIx_compose_zero ps.tokens body_start ps.pos ps_after.pos
                      h_bs (by show ps.pos < ps.tokens.size; omega) (by omega) h_bal
                      (by show flowBracketDelta (ps.tokens.tokens[ps.pos]'(show ps.pos < ps.tokens.size by omega)).token = 0
                          rw [(getElem!_pos ps.tokens.tokens ps.pos (show ps.pos < ps.tokens.size by omega)).symm, h_fe_val]
                          decide)
                      h_pn_bal')
                (by dsimp only []; omega)
            exact ⟨items_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_tok_eq, h_tp_res.trans (h_tp_eq.trans h_psX_tp)⟩
        · -- no separator
          have h_acc_pos : items_acc.size > 0 := by assumption
          have h_not_fe : ps.peek? ≠ some .flowEntry := by assumption
          have h_sep := h_entry h_acc_pos
          rcases h_sep with h_fe | h_end
          · exfalso; exact h_not_fe h_fe
          · exact ⟨items_acc, ps, rfl, h_end, h_at_end h_end, rfl, rfl⟩
      · -- items_acc.size = 0
        split
        · -- key at start → contradiction
          rename_i h_peek_key
          exfalso
          have h_cs := h_content_start h_lt (by omega)
          rw [h_peek_key] at h_cs
          rcases h_cs with ⟨c, s, hcs⟩ | hcs | hcs <;> cases hcs
        · -- flowSequenceEnd → return ok
          rename_i h_peek_end
          exact ⟨items_acc, ps, rfl, h_peek_end, h_at_end h_peek_end, rfl, rfl⟩
        · -- other → parseNode + recurse
          rename_i h_not_key h_not_end
          have h_cs := h_content_start h_lt (by omega)
          generalize hPsX : ({ ps with
            currentPath := ps.currentPath.push (.index items_acc.size) } : ParseStateIx input) = psX
          obtain ⟨val, ps_after, h_ok, h_pos_adv, h_pos_bound, h_tok_eq, h_tp_eq, h_peek_after, h_pn_bal⟩ :=
            h_pn psX n
              (by subst hPsX; rfl)
              (by omega) (by omega)
              (by subst hPsX; exact h_lt)
              (by subst hPsX; exact h_bs)
              (by subst hPsX; exact h_bal)
              (by subst hPsX; exact h_cs)
          rw [h_ok]; dsimp only []
          have h_psX_pos : psX.pos = ps.pos := by subst hPsX; rfl
          have h_psX_tp : psX.trackPositions = ps.trackPositions := by subst hPsX; rfl
          have h_rec_tok : ({ ps_after with currentPath := ps.currentPath } : ParseStateIx input).tokens = ps.tokens := h_tok_eq
          obtain ⟨items_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res, h_tp_res⟩ :=
            ih { ps_after with currentPath := ps.currentPath } (items_acc.push val)
              (by rw [h_rec_tok]; exact h_pn.mono (by omega))
              (by dsimp only []; omega)
              (by exact h_pos_bound)
              (by rw [h_rec_tok]; exact h_end_pos)
              (by rw [h_rec_tok]; exact h_end_tok)
              (by intro h_end
                  rcases h_peek_after with h_fe | ⟨_, h_pos_eq⟩
                  · have : ps_after.peek? = some .flowSequenceEnd := h_end
                    rw [h_fe] at this; cases this
                  · exact h_pos_eq)
              (by intro _; exact h_peek_after.imp id And.left)
              (by intro h_sz h_empty; simp [Array.size_push] at h_empty)
              (by intro k hk1 hk2 hval h_depth; dsimp only [] at hk1 h_depth;
                  rw [h_tok_eq] at h_depth; rw [h_rec_tok] at hval ⊢;
                  exact h_after_fe k (by omega) hk2 hval h_depth)
              (by rw [h_rec_tok]
                  have h_pn_bal' : flowBracketBalanceIx ps.tokens ps.pos ps_after.pos = 0 := by
                    rw [show ps.pos = psX.pos from h_psX_pos.symm]; exact h_pn_bal
                  rw [flowBracketBalanceIx_compose ps.tokens body_start ps.pos ps_after.pos h_bs (by omega),
                      h_bal, h_pn_bal']; simp)
              (by dsimp only []; omega)
          exact ⟨items_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_tok_eq, h_tp_res.trans (h_tp_eq.trans h_psX_tp)⟩

/-! #### Flow mapping loop emitter acceptance — Indexed -/

/-- Indexed twin of `ParseEntryFlowMapOk`. -/
def ParseEntryFlowMapOkIx (tokens : Indexed.TokenStream input)
    (endPos : Nat) (fuel : Nat) (body_start : Nat) : Prop :=
  ∀ (ps : ParseStateIx input) (m : Nat),
    ps.tokens = tokens → 0 < m → m ≤ fuel →
    ps.pos < endPos →
    body_start ≤ ps.pos →
    flowBracketBalanceIx tokens body_start ps.pos = 0 →
    ps.peek? = some .key →
    ∃ key_val key_ps,
      parseExplicitKey ps.advance m = .ok (key_val, key_ps) ∧
      key_ps.pos > ps.pos ∧ key_ps.pos ≤ endPos ∧
      key_ps.tokens = tokens ∧
      key_ps.trackPositions = ps.trackPositions ∧
      ∀ (savedPath : YamlPath) (keyContent : String),
        ∃ val_val val_ps,
          parseFlowMappingValue key_ps m savedPath keyContent = .ok (val_val, val_ps) ∧
          val_ps.pos > ps.pos ∧ val_ps.pos ≤ endPos ∧
          val_ps.tokens = tokens ∧
          val_ps.trackPositions = ps.trackPositions ∧
          (val_ps.peek? = some .flowEntry ∨
           (val_ps.peek? = some .flowMappingEnd ∧ val_ps.pos = endPos)) ∧
          flowBracketBalanceIx tokens ps.pos val_ps.pos = 0

theorem ParseEntryFlowMapOkIx.mono {tokens : Indexed.TokenStream input}
    {endPos fuel fuel' body_start}
    (h : ParseEntryFlowMapOkIx (input := input) tokens endPos fuel body_start)
    (h_le : fuel' ≤ fuel) :
    ParseEntryFlowMapOkIx (input := input) tokens endPos fuel' body_start :=
  fun ps m h_tok h_pos_m h_m h_pos h_bs h_depth h_key =>
    let ⟨kv, kps, hek, hadv, hbound, htok, htp, hfmv⟩ :=
      h ps m h_tok h_pos_m (Nat.le_trans h_m h_le) h_pos h_bs h_depth h_key
    ⟨kv, kps, hek, hadv, hbound, htok, htp, hfmv⟩

set_option maxHeartbeats 6400000 in
theorem parseFlowMappingLoop_emitter_ok_ix (fuel : Nat)
    (ps : ParseStateIx input) (pairs_acc : Array (YamlValue × YamlValue)) (endPos : Nat)
    (body_start : Nat)
    (h_entry : ParseEntryFlowMapOkIx (input := input) ps.tokens endPos fuel body_start)
    (h_fuel : fuel > endPos - ps.pos)
    (h_pos : ps.pos ≤ endPos)
    (h_end_pos : endPos < ps.tokens.size)
    (h_end_tok : (ps.tokens.tokens[endPos]!).token = .flowMappingEnd)
    (h_at_end : ps.peek? = some .flowMappingEnd → ps.pos = endPos)
    (h_sep : pairs_acc.size > 0 →
             ps.peek? = some .flowEntry ∨ ps.peek? = some .flowMappingEnd)
    (h_start : ps.pos < endPos → pairs_acc.size = 0 →
               ps.peek? = some .key)
    (h_after_fe : ∀ k : Nat, ps.pos ≤ k → k < endPos →
                  (ps.tokens.tokens[k]!).token = .flowEntry →
                  flowBracketBalanceIx ps.tokens body_start k = 0 →
                  k + 1 ≤ endPos ∧ (ps.tokens.tokens[k + 1]!).token = .key)
    (h_bal : flowBracketBalanceIx ps.tokens body_start ps.pos = 0)
    (h_bs : body_start ≤ ps.pos)
    : ∃ pairs ps', parseFlowMappingLoop ps fuel pairs_acc = .ok (pairs, ps') ∧
                   ps'.peek? = some .flowMappingEnd ∧
                   ps'.pos = endPos ∧
                   ps'.tokens = ps.tokens ∧
                   ps'.trackPositions = ps.trackPositions := by
  induction fuel generalizing ps pairs_acc with
  | zero =>
    have h_eq : ps.pos = endPos := by omega
    unfold parseFlowMappingLoop
    refine ⟨pairs_acc, ps, rfl, ?_, h_eq, rfl, rfl⟩
    exact peek_of_pos_val_ix h_eq (by omega) h_end_tok
  | succ n ih =>
    unfold parseFlowMappingLoop
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · exact ⟨pairs_acc, ps, rfl, ‹_›, h_at_end ‹_›, rfl, rfl⟩
    · rename_i h_outer_not_end
      have h_lt : ps.pos < endPos := by
        rcases Nat.eq_or_lt_of_le h_pos with h_eq | h_lt
        · exfalso; exact h_outer_not_end (peek_of_pos_val_ix h_eq (by omega) h_end_tok)
        · exact h_lt
      split
      · -- pairs_acc.size > 0
        split
        · -- flowEntry
          split
          · -- flowMappingEnd after sep → contradiction
            rename_i h_adv_end
            exfalso
            have h_fe_val : (ps.tokens.tokens[ps.pos]!).token = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val_ix h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) h_lt h_fe_val h_bal
            have ⟨_, h_val⟩ := peek_some_val_ix h_adv_end
            simp [ParseStateIx.advance] at h_val
            exact absurd (h_afe.2.symm.trans h_val) (by decide)
          · -- key after separator → full entry parse + recurse
            rename_i h_adv_not_end h_adv_key
            have h_fe_val : (ps.tokens.tokens[ps.pos]!).token = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val_ix h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) h_lt h_fe_val h_bal
            have h_adv_pos : ps.advance.pos = ps.pos + 1 := by
              simp [ParseStateIx.advance]
            have h_adv_pos_lt : ps.pos + 1 < endPos := by
              rcases Nat.eq_or_lt_of_le h_afe.1 with heq | hlt
              · exfalso
                have h_peek_end := peek_of_pos_val_ix (ps := ps.advance) rfl
                  (show ps.advance.pos < ps.advance.tokens.size by
                    simp [ParseStateIx.advance]; show ps.pos + 1 < ps.tokens.size; omega)
                  (show (ps.advance.tokens.tokens[ps.advance.pos]!).token = .flowMappingEnd by
                    simp [ParseStateIx.advance]; rw [heq]; exact h_end_tok)
                rw [h_adv_key] at h_peek_end; cases h_peek_end
              · exact hlt
            have h_depth_at_adv : flowBracketBalanceIx ps.tokens body_start (ps.pos + 1) = 0 := by
              have h_pos_bound : ps.pos < ps.tokens.tokens.toList.length := by
                show ps.pos < ps.tokens.size; omega
              rw [flowBracketBalanceIx_compose ps.tokens body_start ps.pos (ps.pos + 1) h_bs (by omega),
                  h_bal, flowBracketBalanceIx_single _ _ h_pos_bound]
              have h_eq : (ps.tokens.tokens.toList[ps.pos]'h_pos_bound).token = YamlToken.flowEntry := by
                show (ps.tokens.tokens[ps.pos]'(show ps.pos < ps.tokens.size by omega)).token = YamlToken.flowEntry
                rw [← getElem!_pos ps.tokens.tokens ps.pos (show ps.pos < ps.tokens.size by omega)]
                exact h_fe_val
              rw [h_eq]; decide
            obtain ⟨key_val, key_ps, h_ek_ok, h_ek_adv, h_ek_bound, h_ek_tok, h_ek_tp, h_fmv_univ⟩ :=
              h_entry ps.advance n
                (by simp [ParseStateIx.advance])
                (by omega) (by omega)
                h_adv_pos_lt
                (by omega)
                (by show flowBracketBalanceIx ps.tokens body_start (ps.pos + 1) = 0
                    exact h_depth_at_adv)
                h_adv_key
            rw [h_ek_ok]; dsimp only []
            split
            · rename_i err heq_err
              exfalso
              obtain ⟨_, _, h_ok, _⟩ := h_fmv_univ _ _
              exact absurd (heq_err.symm.trans h_ok) (by simp)
            · rename_i fmv_res heq_fmv
              obtain ⟨val_val, val_ps, h_fmv_ok, h_fmv_adv, h_fmv_bound, h_fmv_tok, h_fmv_tp, h_fmv_peek, h_entry_bal⟩ :=
                h_fmv_univ _ _
              have h_eq := Except.ok.inj (heq_fmv.symm.trans h_fmv_ok)
              obtain ⟨fmv_v, fmv_ps⟩ := fmv_res
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq.symm
              obtain ⟨pairs_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res, h_tp_res⟩ :=
                ih val_ps (pairs_acc.push (key_val, val_val))
                  (by rw [h_fmv_tok]; exact h_entry.mono (by omega))
                  (by omega)
                  h_fmv_bound
                  (by rw [h_fmv_tok]; exact h_end_pos)
                  (by rw [h_fmv_tok]; exact h_end_tok)
                  (by intro h_end
                      rcases h_fmv_peek with h_fe | ⟨_, h_pos_eq⟩
                      · have : val_ps.peek? = some .flowMappingEnd := h_end
                        rw [h_fe] at this; cases this
                      · exact h_pos_eq)
                  (by intro _; exact h_fmv_peek.imp id And.left)
                  (by intro _ h; simp [Array.size_push] at h)
                  (by intro k hk1 hk2 hval h_depth; rw [h_fmv_tok] at hval h_depth ⊢;
                      exact h_after_fe k (by omega) hk2 hval h_depth)
                  (by rw [h_fmv_tok]
                      rw [show ps.advance.pos = ps.pos + 1 from h_adv_pos] at h_entry_bal
                      exact flowBracketBalanceIx_compose_zero ps.tokens body_start ps.pos val_ps.pos
                        h_bs (by show ps.pos < ps.tokens.size; omega) (by omega) h_bal
                        (by show flowBracketDelta (ps.tokens.tokens[ps.pos]'(show ps.pos < ps.tokens.size by omega)).token = 0
                            rw [(getElem!_pos ps.tokens.tokens ps.pos (show ps.pos < ps.tokens.size by omega)).symm, h_fe_val]
                            decide)
                        h_entry_bal)
                  (by omega)
              exact ⟨pairs_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_fmv_tok, h_tp_res.trans h_fmv_tp⟩
          · -- wildcard after separator → contradiction
            rename_i h_adv_not_end h_adv_not_key
            exfalso
            have h_fe_val : (ps.tokens.tokens[ps.pos]!).token = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val_ix h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) h_lt h_fe_val h_bal
            exact h_adv_not_key (peek_of_pos_val_ix (ps := ps.advance) rfl
              (show ps.advance.pos < ps.advance.tokens.size by
                simp [ParseStateIx.advance]; show ps.pos + 1 < ps.tokens.size; omega)
              (show (ps.advance.tokens.tokens[ps.advance.pos]!).token = .key by
                simp [ParseStateIx.advance]; exact h_afe.2))
        · -- no separator → early return
          have h_acc_pos : pairs_acc.size > 0 := by assumption
          have h_not_fe : ps.peek? ≠ some .flowEntry := by assumption
          rcases h_sep h_acc_pos with h_fe | h_end
          · exfalso; exact h_not_fe h_fe
          · exact ⟨pairs_acc, ps, rfl, h_end, h_at_end h_end, rfl, rfl⟩
      · -- pairs_acc.size = 0
        split
        · -- flowMappingEnd → return ok
          rename_i h_peek_end
          exact ⟨pairs_acc, ps, rfl, h_peek_end, h_at_end h_peek_end, rfl, rfl⟩
        · -- key → full entry parse + recurse
          rename_i h_not_end h_peek_key
          obtain ⟨key_val, key_ps, h_ek_ok, h_ek_adv, h_ek_bound, h_ek_tok, h_ek_tp, h_fmv_univ⟩ :=
            h_entry ps n rfl (by omega) (by omega) h_lt h_bs h_bal h_peek_key
          rw [h_ek_ok]; dsimp only []
          split
          · rename_i err heq_err
            exfalso
            obtain ⟨_, _, h_ok, _⟩ := h_fmv_univ _ _
            exact absurd (heq_err.symm.trans h_ok) (by simp)
          · rename_i fmv_res heq_fmv
            obtain ⟨val_val, val_ps, h_fmv_ok, h_fmv_adv, h_fmv_bound, h_fmv_tok, h_fmv_tp, h_fmv_peek, h_entry_bal⟩ :=
              h_fmv_univ _ _
            have h_eq := Except.ok.inj (heq_fmv.symm.trans h_fmv_ok)
            obtain ⟨fmv_v, fmv_ps⟩ := fmv_res
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq.symm
            obtain ⟨pairs_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res, h_tp_res⟩ :=
              ih val_ps (pairs_acc.push (key_val, val_val))
                (by rw [h_fmv_tok]; exact h_entry.mono (by omega))
                (by omega)
                h_fmv_bound
                (by rw [h_fmv_tok]; exact h_end_pos)
                (by rw [h_fmv_tok]; exact h_end_tok)
                (by intro h_end
                    rcases h_fmv_peek with h_fe | ⟨_, h_pos_eq⟩
                    · have : val_ps.peek? = some .flowMappingEnd := h_end
                      rw [h_fe] at this; cases this
                    · exact h_pos_eq)
                (by intro _; exact h_fmv_peek.imp id And.left)
                (by intro h_lt_end h_empty; simp [Array.size_push] at h_empty)
                (by intro k hk1 hk2 hval h_depth; rw [h_fmv_tok] at hval h_depth ⊢;
                    exact h_after_fe k (by omega) hk2 hval h_depth)
                (by rw [h_fmv_tok,
                        flowBracketBalanceIx_compose ps.tokens body_start ps.pos val_ps.pos h_bs (by omega),
                        h_bal, h_entry_bal]; simp)
                (by omega)
            exact ⟨pairs_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_fmv_tok, h_tp_res.trans h_fmv_tp⟩
        · -- wildcard
          rename_i h_not_end h_not_key
          exfalso
          have h_acc_zero : pairs_acc.size = 0 := by omega
          have hk := h_start h_lt h_acc_zero
          exact h_not_key hk

/-! ### §5c  Scanner-side bridge — relocated to `IndexedScannerPlainScalarValid.lean`

The §5c forward references — the indexed scanner output is flow-aware
PSV and has matched flow brackets — were previously staged here as
two placeholder axioms with `(h_from_scanner : True)` preconditions.
In Step 6d.1e.1 they were relocated to
`L4YAML/Proofs/Production/IndexedScannerPlainScalarValid.lean`
(`scan_flow_aware_psv_ix_axiom` + `scan_flow_brackets_matched_ix_axiom`)
with **tightened preconditions** keyed on
`Scanner.Indexed.scanIx input = .ok tokens` instead of the placeholder
`True`. The new file imports `IndexedWellBehaved.lean` (for the
`FlowAwarePSVIx` / `FlowBracketsMatchedIx` predicates) and the indexed
scanner.

**Net effect on `IndexedWellBehaved.lean`**: this file is now
**0 axioms / 0 sorries** locally. The Phase 3 closure still has 2
axioms (in the sister file), which the per-action preservation chain
(Step 6d.1e.2+) will discharge. See Blueprint Step 6d.1e ladder and
Reflection 68. -/

end L4YAML.Proofs.Indexed.WellBehaved
