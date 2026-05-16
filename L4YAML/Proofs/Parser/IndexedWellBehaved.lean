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

end L4YAML.Proofs.Indexed.WellBehaved
