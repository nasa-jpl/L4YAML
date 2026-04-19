import L4YAML.Grammar
import L4YAML.TokenParser
import L4YAML.Proofs.ScannerPlainScalarValid
import L4YAML.Proofs.Composition
import L4YAML.Proofs.ParserSoundness
import L4YAML.Proofs.ParserGrammableBase

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition

/-! ## §5  Parser Output is `Scannable` (C2)

The parser constructs `YamlValue` trees from token arrays. Each scalar
node's `content` and `style` come directly from a `YamlToken.scalar`
token. By B3.5, every plain scalar token satisfies `ScalarScannable _ false`.
Non-plain scalars satisfy `ScalarScannable` vacuously (`style ≠ .plain`).
Aliases satisfy `Scannable.alias` trivially.

### Gap Analysis

Three distinct barriers prevent full discharge of the C2 sorries:

1. **Flow context gap** (`parseStream_output_scannable`):
   `Scannable (.sequence .flow items ...) false` requires
   `∀ i, Scannable items[i] true` because
   `(false || .flow == .flow) = true`. And `Scannable (.scalar s) true`
   requires `ScalarScannable s true`, which includes `noFlowIndicators`
   and `validPlainFirstProp _ true`. But `PlainScalarsValid` only gives
   `ScalarScannable _ false` (no flow indicator check). The scanner DOES
   guarantee `ScalarScannable _ true` for flow-context tokens (B3.4 gives
   `ScalarScannable _ s.inFlow`), but B3.5's universal weakening via
   `ScalarScannable_any_implies_false` discards per-token flow context.

   **Fix**: Extend B3.5 to also prove `FlowAwarePSV` (defined below).
   This requires showing scanner `flowLevel > 0 ↔ flowNesting > 0` in the
   token stream, and threading `ScalarScannable _ true` for flow-context
   tokens through the scanner dispatch chain.

2. **Alias ordering invariant** (`parseStream_output_aliases_resolve`):
   The parser's `parseNode` produces `.alias name` from `.alias name` tokens
   without validating that a prior `.anchor name` token exists. The scanner's
   `scanAnchorOrAlias` similarly just emits tokens. Proving
   `AllAliasesResolve` requires a scanner-level invariant that every
   `*name` token has a prior `&name` token (YAML §7.1), plus a parser
   invariant that `ps.addAnchor` accumulations cover all processed anchors.

3. **Cross-context semantic gap** (`parseStream_output_anchors_wellformed`):
   `WellFormedAnchors` requires `∀ inFlow, Grammable val.stripAnchors inFlow`.
   But block-context plain scalars like `value{key}` satisfy
   `ScalarScannable _ false` (vacuous flow indicator check) but NOT
   `ScalarScannable _ true` (flow indicators present). If such values are
   anchored, the `∀ inFlow` quantifier is genuinely unsatisfiable.
   This is a YAML spec corner case (§7.1 cross-context aliasing), not a
   proof gap. Options: weaken to `NoFlowIndicatorsInBlockAnchors`
   precondition, or restrict to single-context documents.
-/

/-! ### C2 Infrastructure

Helper lemmas and definitions that narrow the gap between B3.5's
token-level `PlainScalarsValid` and C2's tree-level `Scannable`. -/

/-- Strengthen `ScalarScannable _ false` to `_ true` given the two
    additional flow-context properties.

    From `ScalarScannable s false` we already have `noColonSpace` and
    `noSpaceHash`. To reach `_ true` we additionally need
    `validPlainFirstProp _ true` and `noFlowIndicators`.

    This is the bridge that `FlowAwarePSV` fills: flow-context tokens
    have these properties by scanner construction (B3.4). -/
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

/-! ### Flow Nesting and FlowAwarePSV

`flowNesting`, `FlowContextPSV`, `FlowAwarePSV`, and `FlowNestingInv`
are defined in `ScannerPlainScalarValid.lean` to avoid circular imports
(the FlowAwarePSV proof chain lives there alongside B3.5).

`FlowAwarePSV tokens ≡ PlainScalarsValid tokens ∧ FlowContextPSV tokens`

Proved by `scan_flow_aware_psv` (B3.5+ chain). -/

/-! ### C2 Bridge Lemmas

These connect B3.5's token-level `PlainScalarsValid` to the tree-level
`Scannable` predicate for scalar base cases. -/

/-- A scalar YamlValue constructed from a token satisfying PlainScalarsValid
    is Scannable at block context. -/
theorem scalar_from_token_scannable
    (tokens : Array (Positioned YamlToken))
    (h_psv : PlainScalarsValid tokens)
    (i : Nat) (hi : i < tokens.size)
    (content : String) (style : ScalarStyle)
    (h_tok : (tokens[i]'hi).val = .scalar content style)
    (tag anchor : Option String) :
    Scannable (.scalar ⟨content, style, tag, anchor, none⟩) false := by
  apply Scannable.scalar
  intro hplain hlen
  have h_match := h_psv i hi
  rw [h_tok] at h_match
  cases style with
  | plain => exact h_match hplain hlen
  | _ => contradiction

/-- A scalar from a flow-context token satisfying FlowAwarePSV is
    Scannable at any flow context. -/
theorem scalar_from_flow_token_scannable
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (i : Nat) (hi : i < tokens.size)
    (content : String) (style : ScalarStyle)
    (h_tok : (tokens[i]'hi).val = .scalar content style)
    (h_flow : flowNesting tokens i > 0)
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

/-- Empty content scalar (parser empty node) is trivially Scannable
    at any flow context. -/
theorem empty_scalar_scannable (tag anchor : Option String) (inFlow : Bool) :
    Scannable (.scalar ⟨"", .plain, tag, anchor, none⟩) inFlow := by
  apply Scannable.scalar; intro _ hlen; simp at hlen

/-- When `peek? ps = some tok`, `ps.pos` is in bounds and the bounded
    access `(ps.tokens[ps.pos]'h).val` equals `tok`.
    Bridges the `Array.getElem!` in `peek?` to the bounded `getElem` used
    in proofs like `flowNesting_non_flow_step`. -/
theorem peek_some_bounded (ps : ParseState) (tok : YamlToken)
    (h : ps.peek? = some tok) :
    ps.pos < ps.tokens.size ∧
    ∀ (h_lt : ps.pos < ps.tokens.size), (ps.tokens[ps.pos]'h_lt).val = tok := by
  unfold ParseState.peek? at h
  split at h
  · rename_i h_lt
    constructor
    · exact h_lt
    · intro h_lt'
      simp at h
      -- h : ps.tokens[ps.pos]!.val = tok
      -- getElem!_pos (simp lemma): c[i]! = c[i]'h when i < c.size
      rw [getElem!_pos ps.tokens ps.pos h_lt'] at h
      exact h
  · simp at h

/-! ### §5a  flowNesting position step lemmas

`flowNesting tokens i` counts unmatched flow-start tokens before position `i`.
These lemmas characterize how `flowNesting` changes when advancing one token.
Used by the mutual scannability induction to maintain `flowNesting > 0`
inside flow collections. -/

/-- Helper: `flowNesting tokens (i+1)` factors as go-step from `flowNesting tokens i`. -/
theorem flowNesting_split_step (tokens : Array (Positioned YamlToken))
    (i : Nat) (_hi : i < tokens.size) :
    flowNesting tokens (i + 1) =
    flowNesting.go tokens i (i + 1) (flowNesting tokens i) := by
  show flowNesting.go tokens 0 (i + 1) 0 =
    flowNesting.go tokens i (i + 1) (flowNesting.go tokens 0 i 0)
  exact flowNesting_go_split tokens 0 i (i + 1) 0 (by omega) (by omega)

/-- After consuming a flow-start token, `flowNesting` is positive. -/
theorem flowNesting_pos_after_flow_start (tokens : Array (Positioned YamlToken))
    (i : Nat) (hi : i < tokens.size)
    (h : (tokens[i]'hi).val = .flowSequenceStart ∨
         (tokens[i]'hi).val = .flowMappingStart) :
    flowNesting tokens (i + 1) > 0 := by
  rw [flowNesting_split_step tokens i hi,
      flowNesting_go_step tokens i (i + 1) _ hi (by omega),
      flowNesting_go_ge_target tokens (i + 1) (i + 1) _ (by omega)]
  rcases h with h | h <;> simp [h] <;> omega

/-- After consuming a flow-start token, `flowNesting` increases by exactly 1. -/
theorem flowNesting_after_flow_start_eq (tokens : Array (Positioned YamlToken))
    (i : Nat) (hi : i < tokens.size)
    (h : (tokens[i]'hi).val = .flowSequenceStart ∨
         (tokens[i]'hi).val = .flowMappingStart) :
    flowNesting tokens (i + 1) = flowNesting tokens i + 1 := by
  rw [flowNesting_split_step tokens i hi,
      flowNesting_go_step tokens i (i + 1) _ hi (by omega),
      flowNesting_go_ge_target tokens (i + 1) (i + 1) _ (by omega)]
  rcases h with h | h <;> simp [h]

/-- After consuming a flow-end token, `flowNesting` decreases by 1 (saturating). -/
theorem flowNesting_after_flow_end (tokens : Array (Positioned YamlToken))
    (i : Nat) (hi : i < tokens.size)
    (h : (tokens[i]'hi).val = .flowSequenceEnd ∨
         (tokens[i]'hi).val = .flowMappingEnd)
    (h_pos : flowNesting tokens i > 0) :
    flowNesting tokens (i + 1) = flowNesting tokens i - 1 := by
  rw [flowNesting_split_step tokens i hi,
      flowNesting_go_step tokens i (i + 1) _ hi (by omega),
      flowNesting_go_ge_target tokens (i + 1) (i + 1) _ (by omega)]
  rcases h with h | h <;> simp [h, h_pos]

/-- Advancing past a non-flow-boundary token preserves `flowNesting`. -/
theorem flowNesting_non_flow_step (tokens : Array (Positioned YamlToken))
    (i : Nat) (hi : i < tokens.size)
    (h1 : (tokens[i]'hi).val ≠ .flowSequenceStart)
    (h2 : (tokens[i]'hi).val ≠ .flowMappingStart)
    (h3 : (tokens[i]'hi).val ≠ .flowSequenceEnd)
    (h4 : (tokens[i]'hi).val ≠ .flowMappingEnd) :
    flowNesting tokens (i + 1) = flowNesting tokens i := by
  rw [flowNesting_split_step tokens i hi,
      flowNesting_go_step tokens i (i + 1) _ hi (by omega),
      flowNesting_go_ge_target tokens (i + 1) (i + 1) _ (by omega)]
  generalize (tokens[i]'hi).val = tok at *
  cases tok <;> simp_all

/-- `flowNesting` is constant for positions `≥ tokens.size`. -/
theorem flowNesting_beyond_size (tokens : Array (Positioned YamlToken))
    (i : Nat) (hi : i ≥ tokens.size) :
    flowNesting tokens (i + 1) = flowNesting tokens i := by
  unfold flowNesting
  rw [flowNesting_go_split tokens 0 i (i + 1) 0 (by omega) (by omega)]
  rw [flowNesting_go_oob tokens i (i + 1) (flowNesting.go tokens 0 i 0) hi]

/-! ### §5b  Scannable monotonicity

`Scannable v true → Scannable v false`: flow-context scannability is
stronger than block-context scannability.  This allows us to prove
`Scannable val true` inside flow collections and then weaken to
`Scannable val false` at the document root. -/

/-- Flow-context scannability implies block-context scannability. -/
theorem Scannable_true_implies_false :
    (v : YamlValue) → Scannable v true → Scannable v false
  | .scalar s, .scalar _ _ h_ss =>
    .scalar s false (ScalarScannable_true_implies_false s h_ss)
  | .alias name, .alias _ _ =>
    .alias name false
  | .sequence .flow items tag anchor, .sequence _ _ _ _ _ h_items =>
    -- (false || .flow == .flow) = true, same as hypothesis
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

/-- Scannable at any `inFlow` implies Scannable at `false`. -/
theorem Scannable_any_implies_false (v : YamlValue) (b : Bool) :
    Scannable v b → Scannable v false := by
  cases b with
  | false => exact id
  | true => exact Scannable_true_implies_false v

/-! ### §5c  scanFiltered preserves FlowAwarePSV -/

/-- `scanFiltered` output satisfies `FlowAwarePSV`: both `PlainScalarsValid`
    and `FlowContextPSV` (flow-context scalars satisfy `ScalarScannable _ true`). -/
theorem scanFiltered_flow_aware_psv (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    FlowAwarePSV tokens :=
  scan_flow_aware_psv input tokens h

/-! ### §5d  Scannable for tag/anchor modification

Adding or changing `tag`/`anchor` fields preserves `Scannable`, because
`Scannable` only constrains scalar `content`/`style` (via `ScalarScannable`)
and collection item scannability. -/

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
  | .sequence style items (.some _) _, h => exact h
  | .sequence style items none (.some _), h => exact h
  | .sequence style items none none, .sequence _ _ _ _ _ h_items =>
    exact .sequence style items tag anchor inFlow h_items
  | .mapping style pairs (.some _) _, h => exact h
  | .mapping style pairs none (.some _), h => exact h
  | .mapping style pairs none none, .mapping _ _ _ _ _ hk hv =>
    exact .mapping style pairs tag anchor inFlow hk hv

/-! ### §5d′  applyNodeFinalization preserves Scannable

`applyNodeFinalization` is the pure tail of `parseNode` after content dispatch.
It applies tag/anchor properties, registers the anchor, and records G5c position.
None of these operations affect `val`'s scannability or the token array. -/

/-- The value produced by `applyNodeFinalization` is `Scannable` whenever
    the raw content value is `Scannable`. -/
theorem applyNodeFinalization_scannable
    (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (nodeStartPos : YamlPos) (inFlow : Bool)
    (h : Scannable val inFlow) :
    Scannable (applyNodeFinalization val ps props nodeStartPos).1 inFlow := by
  match val, h with
  | .scalar _, h => simp [applyNodeFinalization]; exact h
  | .alias _, h => simp [applyNodeFinalization]; exact h
  | .sequence style items (.some _) _, h => simp [applyNodeFinalization]; exact h
  | .sequence style items none (.some _), h => simp [applyNodeFinalization]; exact h
  | .sequence style items none none, .sequence _ _ _ _ _ h_items =>
    simp [applyNodeFinalization]
    exact .sequence style items props.tag props.anchor inFlow h_items
  | .mapping style pairs (.some _) _, h => simp [applyNodeFinalization]; exact h
  | .mapping style pairs none (.some _), h => simp [applyNodeFinalization]; exact h
  | .mapping style pairs none none, .mapping _ _ _ _ _ hk hv =>
    simp [applyNodeFinalization]
    exact .mapping style pairs props.tag props.anchor inFlow hk hv

/-- `applyNodeFinalization` does not modify the token array.
    (It only touches `anchors`, `nodePositions`, `currentPath`.) -/
theorem applyNodeFinalization_tokens
    (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.tokens = ps.tokens := by
  simp only [applyNodeFinalization, ParseState.addAnchor]
  split <;> simp_all
  all_goals (split <;> simp_all)

/-- `applyNodeFinalization` preserves the parse position (`.pos`).
    Properties application, anchor registration, and G5c tracking never advance. -/
theorem applyNodeFinalization_pos
    (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.pos = ps.pos := by
  simp only [applyNodeFinalization, ParseState.addAnchor]
  split <;> simp_all
  all_goals (split <;> simp_all)

/-- `applyNodeFinalization` preserves `trackPositions`. -/
theorem applyNodeFinalization_trackPositions
    (val : YamlValue) (ps : ParseState) (props : NodeProperties)
    (nodeStartPos : YamlPos) :
    (applyNodeFinalization val ps props nodeStartPos).2.trackPositions = ps.trackPositions := by
  simp only [applyNodeFinalization, ParseState.addAnchor]
  split <;> simp_all
  all_goals (split <;> simp_all)

/-! ### §5e′  parseNodeProperties preservation lemmas -/

-- Custom tactic: unfold all `*.loop*` constants in a hypothesis.
-- Used to unroll `for _ in [:n]` loops in Except-monad proofs.
open Lean Lean.Meta Lean.Elab.Tactic in
elab "unfold_loop_at" h:ident : tactic => do
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

@[simp] theorem ParseState.advance_tokens (ps : ParseState) :
    ps.advance.tokens = ps.tokens := rfl

-- `parseNodeProperties` preserves the token array — only `.pos` changes.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
set_option linter.unusedSimpArgs false in
theorem parseNodeProperties_tokens (ps : ParseState) (props : NodeProperties) (ps' : ParseState)
    (h : parseNodeProperties ps = .ok (props, ps')) :
    ps'.tokens = ps.tokens := by
  -- Unroll the for-loop (2 iterations + termination check)
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at h
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  -- Split outermost Except (final result)
  split at h
  · contradiction
  · -- ok case: extract ps'
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨_hfst, rfl⟩ := h
    -- Split continuation Except
    rename_i heq
    split at heq
    · contradiction
    · -- ForInStep.rec on first iteration result
      rename_i v heq_first
      cases v with
      | done x =>
        -- First iteration done (wildcard/break)
        simp (config := { iota := true }) only [] at heq
        simp only [Except.ok.injEq] at heq; subst heq
        -- Split first iteration body
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (first | contradiction | split at heq_first | skip)
        all_goals (try contradiction)
        -- Close: inject equalities, substitute, simplify
        all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq] at heq_first)
        all_goals (try cases heq_first)
        all_goals (try subst heq_first)
        all_goals (first | rfl | simp [ParseState.advance_tokens])
      | yield x =>
        -- First iteration yielded → second iteration
        simp (config := { iota := true }) only [] at heq
        -- Split second iteration outer Except
        split at heq
        · contradiction
        · rename_i v2 heq_second
          cases v2 with
          | done y =>
            -- Second iteration done
            simp (config := { iota := true }) only [] at heq
            simp only [Except.ok.injEq] at heq; subst heq
            -- Split second iter body
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (first | contradiction | split at heq_second | skip)
            all_goals (try contradiction)
            -- Split first iter body
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (first | contradiction | split at heq_first | skip)
            all_goals (try contradiction)
            -- Handle impossible ForInStep constructor mismatches
            all_goals (try cases heq_first)
            all_goals (try cases heq_second)
            -- Close
            all_goals (try simp only [Except.ok.injEq, ForInStep.done.injEq, ForInStep.yield.injEq] at *)
            all_goals (try subst_vars)
            all_goals (first | rfl | simp [ParseState.advance_tokens])
          | yield y =>
            -- Both iterations yielded; loop terminates
            simp only [dite_false] at heq
            simp only [Except.ok.injEq] at heq
            subst heq
            -- Split both iter bodies
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
            all_goals (first | rfl | simp [ParseState.advance_tokens])

-- Helper: advancing past a non-flow-boundary token preserves flowNesting
theorem advance_preserves_flowNesting
    (tokens : Array (Positioned YamlToken)) (ps : ParseState) {tok : YamlToken}
    (h_peek : ps.peek? = some tok) (h_eq : ps.tokens = tokens)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos := by
  have ⟨h_lt, h_val⟩ := peek_some_bounded ps tok h_peek
  simp only [ParseState.advance]
  subst h_eq
  exact flowNesting_non_flow_step ps.tokens ps.pos h_lt
    (by rw [h_val h_lt]; exact h1) (by rw [h_val h_lt]; exact h2)
    (by rw [h_val h_lt]; exact h3) (by rw [h_val h_lt]; exact h4)

theorem advance2_preserves_flowNesting
    (tokens : Array (Positioned YamlToken)) (ps : ParseState) {tok1 tok2 : YamlToken}
    (h_peek1 : ps.peek? = some tok1) (h_peek2 : ps.advance.peek? = some tok2)
    (h_eq : ps.tokens = tokens)
    (h1a : tok1 ≠ .flowSequenceStart) (h1b : tok1 ≠ .flowMappingStart)
    (h1c : tok1 ≠ .flowSequenceEnd) (h1d : tok1 ≠ .flowMappingEnd)
    (h2a : tok2 ≠ .flowSequenceStart) (h2b : tok2 ≠ .flowMappingStart)
    (h2c : tok2 ≠ .flowSequenceEnd) (h2d : tok2 ≠ .flowMappingEnd) :
    flowNesting tokens ps.advance.advance.pos = flowNesting tokens ps.pos := by
  have h_eq' : ps.advance.tokens = tokens := by simp [ParseState.advance_tokens]; exact h_eq
  calc flowNesting tokens ps.advance.advance.pos
      = flowNesting tokens ps.advance.pos :=
        advance_preserves_flowNesting tokens ps.advance h_peek2 h_eq' h2a h2b h2c h2d
    _ = flowNesting tokens ps.pos :=
        advance_preserves_flowNesting tokens ps h_peek1 h_eq h1a h1b h1c h1d

-- `parseNodeProperties` preserves flow nesting — anchor/tag tokens are non-flow.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
set_option linter.unusedSimpArgs false in
theorem parseNodeProperties_flowNesting (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (props : NodeProperties) (ps' : ParseState)
    (h : parseNodeProperties ps = .ok (props, ps'))
    (h_eq : ps.tokens = tokens) :
    flowNesting tokens ps'.pos = flowNesting tokens ps.pos := by
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at h
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
            all_goals (apply advance_preserves_flowNesting <;> first | assumption | rfl | (intro h; cases h))
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
            all_goals (apply advance2_preserves_flowNesting <;> first | assumption | rfl | exact h_eq | (intro h; cases h))

/-! ### §5e  Parser scannability — mutual induction

The 12 mutually recursive parser functions all decrease `fuel` by 1 at each
entry.  We prove scannability + flow-nesting preservation by strong induction
on fuel, assuming the property for all functions at smaller fuel.

**Combined property** (`ParseNodeWB` — "well-behaved"):
For `parseNode ps m = .ok (val, ps')` with `m ≤ n` and `ps.tokens = tokens`:

1. `Scannable val false`  (block-context scannability — always)
2. `flowNesting tokens ps.pos > 0 → Scannable val true`  (flow-context)
3. `flowNesting tokens ps'.pos = flowNesting tokens ps.pos`  (preservation)

Property (3) ensures that matched flow-start/end pairs in parseFlowSequence
and parseFlowMapping net to zero change, so the flow loop can maintain
`flowNesting > 0` across iterations. -/

/-- Combined scannability + flow-nesting property for `parseNode` at fuel `≤ n`. -/
def ParseNodeWB (tokens : Array (Positioned YamlToken)) (n : Nat) : Prop :=
  ∀ (ps : ParseState) (m : Nat) (val : YamlValue) (ps' : ParseState),
    m ≤ n →
    ps.tokens = tokens →
    parseNode ps m = .ok (val, ps') →
    (Scannable val false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable val true) ∧
    (flowNesting tokens ps'.pos = flowNesting tokens ps.pos) ∧
    (ps'.tokens = tokens)

/-- Variant of `ParseNodeWB` application that accepts a non-destructured
    pair result (matching how `split at h_ok` produces `parseNode` hypotheses).
    Takes `h_ok` before `h_le` so `m` is determined before omega needs it. -/
theorem parseNodeWB_apply {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWB tokens n)
    {ps : ParseState} {m : Nat} {v : YamlValue × ParseState}
    (h_tok : ps.tokens = tokens)
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n := by omega) :
    (Scannable v.1 false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable v.1 true) ∧
    (flowNesting tokens v.2.pos = flowNesting tokens ps.pos) ∧
    (v.2.tokens = tokens) :=
  h_ih ps m v.1 v.2 h_le h_tok h_ok

/-- Single-projection helpers for parseNodeWB.
    Parameter order: h_ok FIRST (so assumption determines ps, m, v),
    then h_le (omega, now m is known), then h_tok LAST (assumption finds
    the right token proof by definitional reduction of struct projections). -/
theorem parseNode_scannable_false {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWB tokens n)
    {ps : ParseState} {m : Nat} {v : YamlValue × ParseState}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    Scannable v.1 false :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).1

theorem parseNode_scannable_true {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWB tokens n)
    {ps : ParseState} {m : Nat} {v : YamlValue × ParseState}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    flowNesting tokens ps.pos > 0 → Scannable v.1 true :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).2.1

theorem parseNode_flowNesting {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWB tokens n)
    {ps : ParseState} {m : Nat} {v : YamlValue × ParseState}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    flowNesting tokens v.2.pos = flowNesting tokens ps.pos :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).2.2.1

theorem parseNode_tokens {tokens : Array (Positioned YamlToken)} {n : Nat}
    (h_ih : ParseNodeWB tokens n)
    {ps : ParseState} {m : Nat} {v : YamlValue × ParseState}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n)
    (h_tok : ps.tokens = tokens) :
    v.2.tokens = tokens :=
  (h_ih ps m v.1 v.2 h_le h_tok h_ok).2.2.2

/-! ### §5e″  Sub-parser well-behavedness (fuel-inductive hypotheses)

These sorry'd lemmas capture the well-behavedness of each
content-dispatch sub-parser, assuming `ParseNodeWB tokens fuel`
(the induction hypothesis from the strong induction in `parseNode_wb_all`).

Together with the scalar and empty base cases, they close all content
dispatch branches. Each will be proved separately once the overall
structure is established. -/

/-- Helper: pushing a Scannable value onto an all-Scannable array
    preserves the all-Scannable property. -/
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

/-- Helper: pushing a pair onto an all-Scannable pair array
    preserves the Scannable property for both projections. -/
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

/-- `tryConsume` preserves the token array. -/
theorem tryConsume_tokens (ps : ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.tokens = ps.tokens := by
  unfold ParseState.tryConsume
  split
  · split
    · simp [ParseState.advance]
    · rfl
  · rfl

/-- `tryConsume` preserves flowNesting for non-flow tokens. -/
theorem tryConsume_flowNesting (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (tok : YamlToken)
    (h_eq : ps.tokens = tokens)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    flowNesting tokens (ps.tryConsume tok).2.pos = flowNesting tokens ps.pos := by
  unfold ParseState.tryConsume
  split
  · rename_i t h_peek
    split
    · have h_teq : t = tok := eq_of_beq (by assumption)
      subst h_teq
      exact advance_preserves_flowNesting tokens ps h_peek h_eq h1 h2 h3 h4
    · rfl
  · rfl

/-- `tryConsume` on a currentPath-modified state preserves tokens of
    the original state.  (currentPath doesn't affect peek?/advance.) -/
theorem tryConsume_with_path_tokens (ps : ParseState) (p : YamlPath) (tok : YamlToken) :
    ({ ps with currentPath := p }.tryConsume tok).2.tokens = ps.tokens := by
  unfold ParseState.tryConsume
  split
  · split <;> simp [ParseState.advance]
  · rfl

/-- `tryConsume` on a currentPath-modified state preserves flowNesting
    of the original state.  (currentPath doesn't affect peek?/advance.) -/
theorem tryConsume_with_path_fn (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (p : YamlPath) (tok : YamlToken)
    (h_eq : ps.tokens = tokens)
    (h1 : tok ≠ .flowSequenceStart) (h2 : tok ≠ .flowMappingStart)
    (h3 : tok ≠ .flowSequenceEnd) (h4 : tok ≠ .flowMappingEnd) :
    flowNesting tokens ({ ps with currentPath := p }.tryConsume tok).2.pos =
    flowNesting tokens ps.pos :=
  tryConsume_flowNesting tokens { ps with currentPath := p } tok h_eq h1 h2 h3 h4

/-- Loop invariant for `parseBlockSequenceLoop`: all accumulated items remain
    Scannable, flowNesting is preserved, and the token array is unchanged. -/
theorem parseBlockSequenceLoop_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (_h_fpsv : FlowAwarePSV tokens) -- TODO: should we remove this unused hypothesis?
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (items : Array YamlValue) (result : Array YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_items_false : ∀ i : Fin items.size, Scannable items[i] false)
    (h_items_true : flowNesting tokens ps.pos > 0 →
      ∀ i : Fin items.size, Scannable items[i] true)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok result) :
    (∀ i : Fin result.1.size, Scannable result.1[i] false) ∧
    (flowNesting tokens ps.pos > 0 →
      ∀ i : Fin result.1.size, Scannable result.1[i] true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
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
      -- peek? = some .blockEntry
      have h_adv_tok : ps.advance.tokens = tokens := by
        simp [ParseState.advance, h_eq]
      have h_fn : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
        advance_preserves_flowNesting tokens ps h_peek h_eq
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      split at h_ok
      -- Handle empty-entry cases (blockEntry/blockEnd/none)
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
      -- Non-empty entry: parseNode bind then recurse
      next =>
        split at h_ok
        next => simp at h_ok  -- parseNode = .error → contradiction
        next pn_result heq_pn =>
          -- parseNode = .ok (val, ps₃)
          obtain ⟨val, ps₃⟩ := pn_result
          dsimp only [] at h_ok
          -- Get ParseNodeWB properties
          have h_ps2_tok : ({ ps.advance with
              currentPath := ps.advance.currentPath.push
                (.index items.size) } : ParseState).tokens = tokens := by
            simp [ParseState.advance, h_eq]
          have h_node := h_ih _ k val ps₃ (by omega) h_ps2_tok heq_pn
          -- flowNesting chain: ps₃.pos → ps.advance.pos → ps.pos
          have h_ps3_fn : flowNesting tokens ps₃.pos =
              flowNesting tokens ps.advance.pos := by
            have := h_node.2.2.1; simp at this; exact this
          have h_ps3_tok : ps₃.tokens = tokens := h_node.2.2.2
          -- Build items.push val Scannable
          have h_push_f := push_all_scannable h_items_false h_node.1
          have h_push_t : flowNesting tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseState).pos > 0 →
              ∀ i : Fin (items.push val).size,
              Scannable (items.push val)[i] true := by
            intro h_flow_ps4
            simp only [] at h_flow_ps4
            have h_flow_adv : flowNesting tokens ps.advance.pos > 0 := by
              rw [← h_ps3_fn]; exact h_flow_ps4
            have h_flow_ps : flowNesting tokens ps.pos > 0 := by
              rw [← h_fn]; exact h_flow_adv
            exact push_all_scannable (h_items_true h_flow_ps)
              (h_node.2.1 h_flow_adv)
          have h_ps4_tok : ({ ps₃ with currentPath :=
              ps.advance.currentPath } : ParseState).tokens = tokens := by
            simp [h_ps3_tok]
          have h_wb := ih_fuel (by omega)
              ({ ps₃ with currentPath := ps.advance.currentPath } : ParseState)
              (items.push val) h_ps4_tok h_push_f h_push_t h_ok
          have h_ps4_fn : flowNesting tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseState).pos =
              flowNesting tokens ps.pos := by
            simp only []; rw [h_ps3_fn, h_fn]
          refine ⟨h_wb.1,
                 fun h_flow => h_wb.2.1 (by rw [h_ps4_fn]; exact h_flow),
                 ?_, h_wb.2.2.2⟩
          exact h_wb.2.2.1.trans h_ps4_fn
    next =>
      -- peek? ≠ .blockEntry → return (items, ps)
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact ⟨h_items_false, h_items_true, rfl, h_eq⟩

/-- `parseBlockSequence` well-behaved given parseNode IH.
    Requires `h_peek` because the function unconditionally advances past
    `blockSequenceStart` and we need the token to be non-flow. -/
theorem parseBlockSequence_wb (tokens : Array (Positioned YamlToken))
    (fuel : Nat) (h_fpsv : FlowAwarePSV tokens) (h_ih : ParseNodeWB tokens fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .blockSequenceStart)
    (h_ok : parseBlockSequence ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  -- Advance past blockSequenceStart preserves flowNesting
  have h_fn_adv : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
    advance_preserves_flowNesting tokens ps h_peek h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- fuel = 0 → error
    simp at h_ok
  · -- fuel = k + 1
    rename_i k
    -- Split on parseBlockSequenceLoop result
    split at h_ok
    · simp at h_ok  -- loop returned error → contradiction
    · -- loop returned .ok (items, ps_loop)
      rename_i loop_result heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      -- Get loop properties
      have h_adv_tok : ps.advance.tokens = tokens := by
        simp [ParseState.advance, h_eq]
      have h_empty_f : ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : flowNesting tokens ps.advance.pos > 0 →
          ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] true := by
        intro _ ⟨_, hi⟩; simp at hi
      have h_loop := parseBlockSequenceLoop_wb tokens (k + 1) k (by omega)
          h_fpsv h_ih ps.advance #[] (items_arr, ps_loop) h_adv_tok
          h_empty_f h_empty_t heq_loop
      have h_loop_fn : flowNesting tokens ps_loop.pos =
          flowNesting tokens ps.advance.pos := h_loop.2.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2.2
      -- Combine loop result with outer structure
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      constructor
      · -- Scannable (.sequence .block items_arr) false
        exact Scannable.sequence .block items_arr none none false h_loop.1
      constructor
      · -- flow context → Scannable (.sequence .block items_arr) true
        intro h_flow
        exact Scannable.sequence .block items_arr none none true
          (fun i => h_loop.2.1 (by rw [h_fn_adv]; exact h_flow) i)
      constructor
      · -- flowNesting preservation (through optional blockEnd advance)
        simp only []
        split
        · rename_i h_peek_end
          have h_fn_end := advance_preserves_flowNesting tokens ps_loop
              h_peek_end h_loop_tok
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          exact h_fn_end.trans (h_loop_fn.trans h_fn_adv)
        · exact h_loop_fn.trans h_fn_adv
      · -- tokens preservation
        simp only []
        split
        · simp only [ParseState.advance]; exact h_loop.2.2.2
        · exact h_loop.2.2.2

/-- Well-behavedness of `parseBlockMappingEntryValue`:
    the returned value is Scannable, and the output state
    preserves flowNesting and tokens.
    Extracted for use by `handleBlockMappingKeyEntry_wb`. -/
theorem parseBlockMappingEntryValue_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (keyHasContent : Bool) (keyLine keyCol : Nat)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok result) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- Split on whether .value was consumed
  have h_tc_tok : (ps.tryConsume .value).2.tokens = tokens :=
    (tryConsume_tokens ps .value).trans h_eq
  have h_tc_fn : flowNesting tokens (ps.tryConsume .value).2.pos = flowNesting tokens ps.pos :=
    tryConsume_flowNesting tokens ps .value h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  split at h_ok
  · -- consumed = true: validation loop + content dispatch
    -- The for loop is a pure validation (only throws or breaks, no state mutation).
    -- After peeling through it, we reach the content dispatch match.
    -- Use repeated split to peel through the for-loop desugaring and error checks.
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
    -- After peeling, remaining goals are either emptyNode or parseNode results
    -- emptyNode goals
    all_goals (try (
      obtain ⟨rfl, rfl⟩ := h_ok
      exact ⟨empty_scalar_scannable none none false,
             fun _ => empty_scalar_scannable none none true,
             h_tc_fn, h_tc_tok⟩))
    -- parseNode goals: h_ok should be `parseNode ps' fuel = .ok result`
    all_goals (
      have h_wb := parseNodeWB_apply h_ih h_tc_tok h_ok (by omega)
      exact ⟨h_wb.1, fun h_flow => h_wb.2.1 (h_tc_fn ▸ h_flow),
             h_wb.2.2.1.trans h_tc_fn, h_wb.2.2.2⟩)
  · -- consumed = false: result = (emptyNode, ps)
    obtain ⟨rfl, rfl⟩ := h_ok
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h_tc_fn, h_tc_tok⟩

/-- Variant of `parseBlockMappingEntryValue_wb` with h_ok before h_eq,
    so that `ps` is inferred from the `h_ok` hypothesis. -/
theorem bevWB (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    {ps : ParseState} {kc : Bool} {kl kcol : Nat}
    {result : YamlValue × ParseState}
    (h_ok : parseBlockMappingEntryValue ps fuel kc kl kcol = .ok result)
    (h_eq : ps.tokens = tokens) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
    result.2.tokens = tokens :=
  parseBlockMappingEntryValue_wb tokens n fuel h_fuel h_ih
      ps kc kl kcol result h_eq h_ok

/-- Well-behavedness of the `.key` branch entry handler:
    the returned key and value are Scannable, and the output state
    preserves flowNesting and tokens. -/
theorem handleBlockMappingKeyEntry_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (pairIdx : Nat)
    (result : YamlValue × YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .key)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok result) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    Scannable result.2.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.2.1 true) ∧
    flowNesting tokens result.2.2.pos = flowNesting tokens ps.pos ∧
    result.2.2.tokens = tokens := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_adv_tok : ps.advance.tokens = tokens := by
    simp [ParseState.advance, h_eq]
  have h_adv_fn : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
    advance_preserves_flowNesting tokens ps h_peek h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  -- Peel through all match/if/bind structures in h_ok
  split at h_ok <;> first | contradiction | skip
  -- Resolve `match emptyNode with .scalar ...` if present
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
  -- After all peeling, h_ok is a final .ok equation
  -- Extract the result and reduce tuple projections
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (rw [← h_ok])
  all_goals (try (dsimp only [Prod.fst, Prod.snd]))
  -- emptyNode key goals
  all_goals (try (
    have h_bev := by
      apply bevWB tokens n fuel h_fuel h_ih
      · assumption  -- h_ok: determines ps from BEV hypothesis
      · exact h_adv_tok  -- h_eq: ps resolved, matches via def-eq
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h_bev.1,
           fun h_flow => h_bev.2.1 (Eq.mpr (congrArg (· > 0) h_adv_fn) h_flow),
           h_bev.2.2.1.trans h_adv_fn,
           h_bev.2.2.2⟩))
  -- parseNode key goals
  all_goals (
    have h_key_wb := parseNodeWB_apply h_ih h_adv_tok (by assumption) (by omega)
    have h_k_tok := h_key_wb.2.2.2
    have h_k_fn := h_key_wb.2.2.1
    have h_bev := by
      apply bevWB tokens n fuel h_fuel h_ih
      · assumption  -- h_ok
      · exact h_k_tok  -- h_eq
    exact ⟨h_key_wb.1,
           fun h_flow => h_key_wb.2.1 (h_adv_fn ▸ h_flow),
           h_bev.1,
           fun h_flow => h_bev.2.1
             (Eq.mpr (congrArg (· > 0) (h_k_fn.trans h_adv_fn)) h_flow),
           h_bev.2.2.1.trans (h_k_fn.trans h_adv_fn),
           h_bev.2.2.2⟩)

/-- Well-behavedness of the `.value` branch entry handler (implicit key):
    the returned value is Scannable, and the output state preserves
    flowNesting and tokens. -/
theorem handleBlockMappingValueEntry_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (pairIdx : Nat)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .value)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok result) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  have h_adv_tok : ps.advance.tokens = tokens := by
    simp [ParseState.advance, h_eq]
  have h_adv_fn : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
    advance_preserves_flowNesting tokens ps h_peek h_eq
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      (by exact fun h => nomatch h) (by exact fun h => nomatch h)
  -- Split on the peek? match after advance
  split at h_ok
  -- emptyNode cases: .key, .blockEnd, none
  all_goals (try (
    simp only [Except.ok.injEq] at h_ok
    rw [← h_ok]; dsimp only [Prod.fst, Prod.snd]
    exact ⟨empty_scalar_scannable none none false,
           fun _ => empty_scalar_scannable none none true,
           h_adv_fn, h_adv_tok⟩))
  -- parseNode case
  split at h_ok
  · simp at h_ok  -- error → contradiction
  · rename_i pn_result heq_pn
    obtain ⟨val, ps'⟩ := pn_result
    simp only [Except.ok.injEq] at h_ok
    rw [← h_ok]; dsimp only [Prod.fst, Prod.snd]
    have h_ps2_tok : ({ ps.advance with
        currentPath := ps.advance.currentPath.push
          (.key s!"{pairIdx}") } : ParseState).tokens = tokens := by
      simp [ParseState.advance, h_eq]
    have h_wb := parseNodeWB_apply h_ih h_ps2_tok heq_pn (by omega)
    have h_fn2 : flowNesting tokens ps'.pos = flowNesting tokens ps.advance.pos := by
      have := h_wb.2.2.1; simp at this; exact this
    exact ⟨h_wb.1,
           fun h_flow => h_wb.2.1 (by simp only [] at *; rw [h_adv_fn]; exact h_flow),
           h_fn2.trans h_adv_fn,
           h_wb.2.2.2⟩

/-- Given key/val with Scannable properties and a parse state with
    flowNesting/tokens preservation, plus the IH for the recursive call,
    close the mapping-loop conclusion.  Extracted from the inductive step
    of `parseBlockMappingLoop_wb` to keep elaboration lightweight. -/
theorem mapping_recurse
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : flowNesting tokens ps.pos > 0 →
      ∀ i : Fin pairs.size,
        Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (key val : YamlValue) (ps_rec : ParseState) (k : Nat)
    (h_kf : Scannable key false) (h_vf : Scannable val false)
    (h_kt : flowNesting tokens ps.pos > 0 → Scannable key true)
    (h_vt : flowNesting tokens ps.pos > 0 → Scannable val true)
    (h_fn_rec : flowNesting tokens ps_rec.pos = flowNesting tokens ps.pos)
    (h_tok_rec : ps_rec.tokens = tokens)
    (h_rec : parseBlockMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseState) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (flowNesting tokens ps'.pos > 0 →
        ∀ i : Fin pairs'.size,
          Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseBlockMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (flowNesting tokens ps'.pos > 0 →
        ∀ i : Fin result.1.size,
          Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNesting tokens result.2.pos = flowNesting tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (flowNesting tokens ps.pos > 0 →
      ∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
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

/-- Loop invariant for `parseBlockMappingLoop`: all accumulated pairs remain
    Scannable (both projections), flowNesting is preserved, and the token
    array is unchanged. -/
theorem parseBlockMappingLoop_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : flowNesting tokens ps.pos > 0 →
      ∀ i : Fin pairs.size,
        Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok result) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (flowNesting tokens ps.pos > 0 →
      ∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
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
      -- peek? = some .key → handleBlockMappingKeyEntry
      split at h_ok
      · simp at h_ok  -- error case
      · rename_i kv_ps heq_handle
        have h_wb := handleBlockMappingKeyEntry_wb tokens n k (by omega)
            h_ih ps pairs.size kv_ps h_eq h_peek_key heq_handle
        exact mapping_recurse tokens ps pairs result
            h_pairs_false h_pairs_true
            kv_ps.1 kv_ps.2.1 kv_ps.2.2 k
            h_wb.1 h_wb.2.2.1 h_wb.2.1 h_wb.2.2.2.1
            h_wb.2.2.2.2.1 h_wb.2.2.2.2.2
            h_ok (ih_fuel (by omega))
    next h_peek_val =>
      -- peek? = some .value → handleBlockMappingValueEntry
      split at h_ok
      · simp at h_ok  -- error case
      · rename_i v_ps heq_handle
        have h_wb := handleBlockMappingValueEntry_wb tokens n k (by omega)
            h_ih ps pairs.size v_ps h_eq h_peek_val heq_handle
        exact mapping_recurse tokens ps pairs result
            h_pairs_false h_pairs_true
            emptyNode v_ps.1 v_ps.2 k
            (empty_scalar_scannable none none false)
            h_wb.1
            (fun _ => empty_scalar_scannable none none true)
            h_wb.2.1
            h_wb.2.2.1 h_wb.2.2.2
            h_ok (ih_fuel (by omega))
    next =>
      -- wildcard: return (pairs, ps)
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩

/-- `parseBlockMapping` well-behaved given parseNode IH.
    Requires `h_peek` because the function unconditionally advances past
    `blockMappingStart` and we need the token to be non-flow. -/
theorem parseBlockMapping_wb (tokens : Array (Positioned YamlToken))
    (fuel : Nat) (h_ih : ParseNodeWB tokens fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .blockMappingStart)
    (h_ok : parseBlockMapping ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_adv_tok : ps.advance.tokens = tokens := by
    simp [ParseState.advance, h_eq]
  have h_fn_adv : flowNesting tokens ps.advance.pos =
      flowNesting tokens ps.pos :=
    advance_preserves_flowNesting tokens ps h_peek h_eq
      (fun h => nomatch h) (fun h => nomatch h)
      (fun h => nomatch h) (fun h => nomatch h)
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- fuel = 0 → error
    simp at h_ok
  · -- fuel = k + 1
    rename_i k_map
    split at h_ok
    · simp at h_ok  -- loop returned error
    · rename_i loop_result heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_empty_f : ∀ i : Fin (#[] : Array (YamlValue × YamlValue)).size,
          Scannable (#[] : Array (YamlValue × YamlValue))[i].1 false ∧
          Scannable (#[] : Array (YamlValue × YamlValue))[i].2 false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : flowNesting tokens ps.advance.pos > 0 →
          ∀ i : Fin (#[] : Array (YamlValue × YamlValue)).size,
          Scannable (#[] : Array (YamlValue × YamlValue))[i].1 true ∧
          Scannable (#[] : Array (YamlValue × YamlValue))[i].2 true := by
        intro _ ⟨_, hi⟩; simp at hi
      have h_loop := parseBlockMappingLoop_wb tokens (k_map + 1) k_map (by omega)
          h_ih ps.advance #[] (pairs_arr, ps_loop)
          h_adv_tok h_empty_f h_empty_t heq_loop
      have h_loop_fn : flowNesting tokens ps_loop.pos =
          flowNesting tokens ps.advance.pos := h_loop.2.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2.2
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      constructor
      · -- Scannable (.mapping .block pairs_arr) false
        exact Scannable.mapping .block pairs_arr none none false
          (fun i => (h_loop.1 i).1) (fun i => (h_loop.1 i).2)
      constructor
      · intro h_flow
        exact Scannable.mapping .block pairs_arr none none true
          (fun i => (h_loop.2.1 (by rw [h_fn_adv]; exact h_flow) i).1)
          (fun i => (h_loop.2.1 (by rw [h_fn_adv]; exact h_flow) i).2)
      constructor
      · -- flowNesting preservation (through optional blockEnd advance)
        simp only []
        split
        · rename_i h_peek_end
          have h_fn_end := advance_preserves_flowNesting tokens ps_loop
              h_peek_end h_loop_tok
              (fun h => nomatch h) (fun h => nomatch h)
              (fun h => nomatch h) (fun h => nomatch h)
          exact h_fn_end.trans (h_loop_fn.trans h_fn_adv)
        · exact h_loop_fn.trans h_fn_adv
      · -- tokens preservation
        simp only []
        split
        · simp only [ParseState.advance]; exact h_loop.2.2.2
        · exact h_loop.2.2.2

/-- Loop invariant for `parseImplicitBlockSequenceLoop`: analogous to
    `parseBlockSequenceLoop_wb` but for the implicit block sequence loop. -/
theorem parseImplicitBlockSequenceLoop_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (items : Array YamlValue) (result : Array YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_items_false : ∀ i : Fin items.size, Scannable items[i] false)
    (h_items_true : flowNesting tokens ps.pos > 0 →
      ∀ i : Fin items.size, Scannable items[i] true)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok result) :
    (∀ i : Fin result.1.size, Scannable result.1[i] false) ∧
    (flowNesting tokens ps.pos > 0 →
      ∀ i : Fin result.1.size, Scannable result.1[i] true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
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
      -- peek? = some .blockEntry
      have h_adv_tok : ps.advance.tokens = tokens := by
        simp [ParseState.advance, h_eq]
      have h_fn : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
        advance_preserves_flowNesting tokens ps h_peek h_eq
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          (by exact fun h => nomatch h) (by exact fun h => nomatch h)
      split at h_ok
      -- Empty-entry cases: blockEntry/blockEnd/key/none
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
      -- Non-empty entry: parseNode bind then recurse
      next =>
        split at h_ok
        next => simp at h_ok  -- parseNode = .error → contradiction
        next pn_result heq_pn =>
          obtain ⟨val, ps₃⟩ := pn_result
          dsimp only [] at h_ok
          have h_ps2_tok : ({ ps.advance with
              currentPath := ps.advance.currentPath.push
                (.index items.size) } : ParseState).tokens = tokens := by
            simp [ParseState.advance, h_eq]
          have h_node := h_ih _ k val ps₃ (by omega) h_ps2_tok heq_pn
          have h_ps3_fn : flowNesting tokens ps₃.pos =
              flowNesting tokens ps.advance.pos := by
            have := h_node.2.2.1; simp at this; exact this
          have h_ps3_tok : ps₃.tokens = tokens := h_node.2.2.2
          have h_push_f := push_all_scannable h_items_false h_node.1
          have h_push_t : flowNesting tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseState).pos > 0 →
              ∀ i : Fin (items.push val).size,
              Scannable (items.push val)[i] true := by
            intro h_flow_ps4
            simp only [] at h_flow_ps4
            have h_flow_adv : flowNesting tokens ps.advance.pos > 0 := by
              rw [← h_ps3_fn]; exact h_flow_ps4
            have h_flow_ps : flowNesting tokens ps.pos > 0 := by
              rw [← h_fn]; exact h_flow_adv
            exact push_all_scannable (h_items_true h_flow_ps)
              (h_node.2.1 h_flow_adv)
          have h_ps4_tok : ({ ps₃ with currentPath :=
              ps.advance.currentPath } : ParseState).tokens = tokens := by
            simp [h_ps3_tok]
          have h_wb := ih_fuel (by omega)
              ({ ps₃ with currentPath := ps.advance.currentPath } : ParseState)
              (items.push val) h_ps4_tok h_push_f h_push_t h_ok
          have h_ps4_fn : flowNesting tokens
              ({ ps₃ with currentPath :=
                  ps.advance.currentPath } : ParseState).pos =
              flowNesting tokens ps.pos := by
            simp only []; rw [h_ps3_fn, h_fn]
          refine ⟨h_wb.1,
                 fun h_flow => h_wb.2.1 (by rw [h_ps4_fn]; exact h_flow),
                 ?_, h_wb.2.2.2⟩
          exact h_wb.2.2.1.trans h_ps4_fn
    next =>
      -- peek? ≠ .blockEntry → return (items, ps)
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact ⟨h_items_false, h_items_true, rfl, h_eq⟩

/-- `parseImplicitBlockSequence` well-behaved given parseNode IH. -/
theorem parseImplicitBlockSequence_wb (tokens : Array (Positioned YamlToken))
    (fuel : Nat) (h_ih : ParseNodeWB tokens fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- fuel = 0 → error
    simp at h_ok
  · -- fuel = k + 1
    rename_i k
    split at h_ok
    · simp at h_ok  -- loop returned error → contradiction
    · rename_i loop_result heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      have h_empty_f : ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] false := by
        intro ⟨_, hi⟩; simp at hi
      have h_empty_t : flowNesting tokens ps.pos > 0 →
          ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] true := by
        intro _ ⟨_, hi⟩; simp at hi
      have h_loop := parseImplicitBlockSequenceLoop_wb tokens (k + 1) k (by omega)
          h_ih ps #[] (items_arr, ps_loop) h_eq
          h_empty_f h_empty_t heq_loop
      simp only [Except.ok.injEq] at h_ok
      subst h_ok
      exact ⟨Scannable.sequence .block items_arr none none false h_loop.1,
             fun h_flow => Scannable.sequence .block items_arr none none true
               (fun i => h_loop.2.1 h_flow i),
             h_loop.2.2.1, h_loop.2.2.2⟩

set_option maxHeartbeats 800000 in
/-- `parseSinglePairMapping` well-behaved given parseNode IH.
    Returns `.mapping .flow #[(key, val)]` — both key and val are Scannable,
    flowNesting preserved, tokens preserved.
    Requires `flowNesting > 0` because `.mapping .flow` forces children to
    `Scannable _ true` regardless of the outer context (see BRIDGING.md,
    parseSinglePairMapping_wb Reflections). -/
theorem parseSinglePairMapping_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (_h_fpsv : FlowAwarePSV tokens) (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .key)
    (h_flow : flowNesting tokens ps.pos > 0)
    (h_ok : parseSinglePairMapping ps fuel = .ok result) :
    Scannable result.1 true ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok  -- fuel = 0 → error
  · rename_i k
    have h_adv_tok : ps.advance.tokens = tokens := by
      simp [ParseState.advance, h_eq]
    have h_adv_fn : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
      advance_preserves_flowNesting tokens ps h_peek h_eq
        (by exact fun h => nomatch h) (by exact fun h => nomatch h)
        (by exact fun h => nomatch h) (by exact fun h => nomatch h)
    simp only [emptyNode] at h_ok
    -- Split on key match: emptyNode branches vs parseNode
    split at h_ok
    -- ---- Case 1-3: key = emptyNode (peek? = .value | .flowEntry | .flowSequenceEnd) ----
    all_goals (try (
      -- In all emptyNode cases: key = .scalar ⟨"", .plain,...⟩, keyContent = ""
      -- Establish tryConsume facts BEFORE peeling the consumed/value dispatch
      have h_tc_tok := fun p => (tryConsume_with_path_tokens ps.advance p .value).trans h_adv_tok
      have h_tc_fn := fun p => tryConsume_with_path_fn tokens ps.advance p .value h_adv_tok
        (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun h => nomatch h)
      -- Generalize tryConsume BEFORE consumed split to prevent WHNF from exposing
      -- the internal peek?/if matches inside the tryConsume call
      generalize hg : ParseState.tryConsume _ _ = tc at h_ok
      have h_tcr_tok : tc.2.tokens = tokens := hg ▸ h_tc_tok _
      have h_tcr_fn : flowNesting tokens tc.2.pos = flowNesting tokens ps.advance.pos :=
        hg ▸ h_tc_fn _
      -- Now split on consumed flag (tc.fst — opaque, so split finds the if cleanly)
      split at h_ok
      -- Subcase: consumed = true → split on value peek?
      · split at h_ok <;> first | contradiction | skip
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        -- emptyNode-val goals
        all_goals (try (
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true)
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
            h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩))
        -- parseNode-val goals: split on parseNode match (reachable since tc is opaque)
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        all_goals (
          have h_vwb := parseNodeWB_apply h_ih h_tcr_tok (by assumption) (by omega)
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true)
              (fun ⟨0, _⟩ => h_vwb.2.1 (by rw [h_tcr_fn, h_adv_fn]; exact h_flow)),
            h_vwb.2.2.1.trans (h_tcr_fn.trans h_adv_fn),
            h_vwb.2.2.2⟩)
      -- Subcase: consumed = false → val = emptyNode
      · simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
        exact ⟨.mapping .flow _ none none true
            (fun ⟨0, _⟩ => empty_scalar_scannable none none true)
            (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
          h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩))
    -- ---- Case 4: key = parseNode (catch-all peek?) ----
    -- parseNode returns (v✝.fst, v✝.snd); split on keyContent match
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- After keyContent split, establish tryConsume facts
    -- v✝.snd is the post-parseNode state; the struct modification only changes currentPath
    all_goals (
      have h_kwb := parseNodeWB_apply h_ih h_adv_tok (by assumption) (by omega)
      have h_k_fn := h_kwb.2.2.1
      have h_k_tok := h_kwb.2.2.2
      have h_k_true := h_kwb.2.1 (h_adv_fn ▸ h_flow)
      have h_tc_tok := fun p => (tryConsume_with_path_tokens _ p .value).trans h_k_tok
      have h_tc_fn := fun p => tryConsume_with_path_fn tokens _ p .value h_k_tok
        (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun h => nomatch h)
      -- Generalize tryConsume BEFORE consumed split to prevent WHNF from exposing
      -- the internal peek?/if matches inside the tryConsume call
      generalize hg : ParseState.tryConsume _ _ = tc at h_ok
      have h_tcr_tok : tc.2.tokens = tokens := hg ▸ h_tc_tok _
      have h_tcr_fn : flowNesting tokens tc.2.pos = flowNesting tokens ps.advance.pos :=
        hg ▸ (h_tc_fn _).trans h_k_fn
      -- Split on consumed flag (tc.fst — opaque, so split finds the if cleanly)
      split at h_ok
      -- Subcase: consumed = true → split on value peek?
      · split at h_ok <;> first | contradiction | skip
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        -- emptyNode-val goals
        all_goals (try (
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => h_k_true)
              (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
            h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩))
        -- parseNode-val goals: split on parseNode match (reachable since tc is opaque)
        all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
        all_goals (
          have h_vwb := parseNodeWB_apply h_ih h_tcr_tok (by assumption) (by omega)
          have h_v_true := h_vwb.2.1 (by rw [h_tcr_fn, h_adv_fn]; exact h_flow)
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
          exact ⟨.mapping .flow _ none none true
              (fun ⟨0, _⟩ => h_k_true)
              (fun ⟨0, _⟩ => h_v_true),
            h_vwb.2.2.1.trans (h_tcr_fn.trans h_adv_fn),
            h_vwb.2.2.2⟩)
      -- Subcase: consumed = false → val = emptyNode
      · simp only [Except.ok.injEq] at h_ok; rw [← h_ok]
        exact ⟨.mapping .flow _ none none true
            (fun ⟨0, _⟩ => h_k_true)
            (fun ⟨0, _⟩ => empty_scalar_scannable none none true),
          h_tcr_fn.trans h_adv_fn, h_tcr_tok⟩)

set_option maxHeartbeats 800000 in
/-- Loop invariant for `parseFlowSequenceLoop`: all accumulated items
    are `Scannable _ true` (flow context), `flowNesting` is preserved, and
    the token array is unchanged.
    Requires `flowNesting > 0` at entry so that `parseSinglePairMapping_wb`
    and `parseNode` return `Scannable _ true`. -/
theorem parseFlowSequenceLoop_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_fpsv : FlowAwarePSV tokens) (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (items : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_flow : flowNesting tokens ps.pos > 0)
    (h_items : ∀ i : Fin items.size, Scannable items[i] true)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok result) :
    (∀ i : Fin result.1.size, Scannable result.1[i] true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨h_items, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    -- First match: peek? = flowSequenceEnd vs other
    split at h_ok
    -- peek? = some .flowSequenceEnd
    next =>
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ⟨h_items, rfl, h_eq⟩
    -- peek? other
    next =>
      split at h_ok
      · -- items.size > 0
        split at h_ok
        next h_sep =>
          -- flowEntry → advance separator then content dispatch
          have h_adv_tok : ps.advance.tokens = tokens := by
            simp [ParseState.advance, h_eq]
          have h_adv_fn : flowNesting tokens ps.advance.pos = flowNesting tokens ps.pos :=
            advance_preserves_flowNesting tokens ps h_sep h_eq
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
              (by exact fun h => nomatch h) (by exact fun h => nomatch h)
          have h_flow_adv : flowNesting tokens ps.advance.pos > 0 := by
            rw [h_adv_fn]; exact h_flow
          -- Content dispatch on ps.advance.peek?
          split at h_ok
          -- key → parseSinglePairMapping
          next h_pk =>
            split at h_ok
            next => simp at h_ok
            next spm_res heq_spm =>
              obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
              have h_ptok : ({ ps.advance with currentPath := ps.advance.currentPath.push (.index items.size) } : ParseState).tokens = tokens := by simp [ParseState.advance, h_eq]
              have h_spm := parseSinglePairMapping_wb tokens n k (by omega) h_fpsv h_ih _ _ h_ptok h_pk (by exact h_flow_adv) heq_spm
              have h_spm_tok : ps3.tokens = tokens := by have := h_spm.2.2; simp at this; exact this
              have h4fn : flowNesting tokens ({ ps3 with currentPath := ps.advance.currentPath } : ParseState).pos = flowNesting tokens ps.pos := by simp only []; have := h_spm.2.1; simp at this; rw [this, h_adv_fn]
              have h_wb := ih_fuel (by omega) _ _ (by simp [h_spm_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_spm.1) h_ok
              exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩
          -- flowSequenceEnd (second check after separator)
          next =>
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            exact ⟨h_items, h_adv_fn, h_adv_tok⟩
          -- catch-all → parseNode
          next =>
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
              have h_ptok : ({ ps.advance with currentPath := ps.advance.currentPath.push (.index items.size) } : ParseState).tokens = tokens := by
                simp [ParseState.advance, h_eq]
              have h_node := parseNodeWB_apply h_ih h_ptok heq_pn (by omega)
              have h_node_tok : ps3.tokens = tokens := by have := h_node.2.2.2; simp at this; exact this
              have h_vt := h_node.2.1 h_flow_adv
              have h4fn : flowNesting tokens ({ ps3 with currentPath := ps.advance.currentPath } : ParseState).pos = flowNesting tokens ps.pos := by
                simp only []
                have := h_node.2.2.1
                simp at this
                rw [this, h_adv_fn]
              have h_wb := ih_fuel (by omega) _ _ (by simp [h_node_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_vt) h_ok
              exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩
        -- not flowEntry → early return (no separator)
        next =>
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact ⟨h_items, rfl, h_eq⟩
      · -- items.size = 0: content dispatch on ps
        split at h_ok
        -- key → parseSinglePairMapping
        next h_pk =>
          split at h_ok
          next => simp at h_ok
          next spm_res heq_spm =>
            obtain ⟨mv, ps3⟩ := spm_res; dsimp only [] at h_ok
            have h_ptok : ({ ps with currentPath := ps.currentPath.push (.index items.size) } : ParseState).tokens = tokens := by simp [h_eq]
            have h_spm := parseSinglePairMapping_wb tokens n k (by omega) h_fpsv h_ih _ _ h_ptok h_pk h_flow heq_spm
            have h_spm_tok : ps3.tokens = tokens := by have := h_spm.2.2; simp at this; exact this
            have h4fn : flowNesting tokens ({ ps3 with currentPath := ps.currentPath } : ParseState).pos = flowNesting tokens ps.pos := by simp only []; have := h_spm.2.1; simp at this; exact this
            have h_wb := ih_fuel (by omega) _ _ (by simp [h_spm_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_spm.1) h_ok
            exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩
        -- flowSequenceEnd
        next =>
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact ⟨h_items, rfl, h_eq⟩
        -- catch-all → parseNode
        next =>
          split at h_ok
          next => simp at h_ok
          next pn_res heq_pn =>
            obtain ⟨v, ps3⟩ := pn_res; dsimp only [] at h_ok
            have h_ptok : ({ ps with currentPath := ps.currentPath.push (.index items.size) } : ParseState).tokens = tokens := by simp [h_eq]
            have h_node := parseNodeWB_apply h_ih h_ptok heq_pn (by omega)
            have h_node_tok : ps3.tokens = tokens := by have := h_node.2.2.2; simp at this; exact this
            have h_vt := h_node.2.1 h_flow
            have h4fn : flowNesting tokens ({ ps3 with currentPath := ps.currentPath } : ParseState).pos = flowNesting tokens ps.pos := by simp only []; have := h_node.2.2.1; simp at this; exact this
            have h_wb := ih_fuel (by omega) _ _ (by simp [h_node_tok]) (by rw [h4fn]; exact h_flow) (push_all_scannable h_items h_vt) h_ok
            exact ⟨h_wb.1, h_wb.2.1.trans h4fn, h_wb.2.2⟩

/-- `parseFlowSequence` well-behaved given parseNode IH.
    Requires `h_peek` so we know the advance consumes `flowSequenceStart`,
    enabling exact flowNesting accounting (+1 at start, −1 at end).
    The else-branch (missing `flowSequenceEnd`) is trivially closed because
    the code returns `.error`, contradicting `h_ok`. -/
theorem parseFlowSequence_wb (tokens : Array (Positioned YamlToken))
    (fuel : Nat) (h_fpsv : FlowAwarePSV tokens) (h_ih : ParseNodeWB tokens fuel)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .flowSequenceStart)
    (h_ok : parseFlowSequence ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- fuel = 0 → error
    simp at h_ok
  · -- fuel = k + 1
    rename_i k
    -- Advance past flowSequenceStart
    have h_adv_tok : ps.advance.tokens = tokens := by
      simp [ParseState.advance, h_eq]
    have ⟨h_lt, h_val⟩ := peek_some_bounded ps .flowSequenceStart h_peek
    have h_adv_fn_eq : flowNesting tokens ps.advance.pos =
        flowNesting tokens ps.pos + 1 := by
      simp only [ParseState.advance]; subst h_eq
      exact flowNesting_after_flow_start_eq ps.tokens ps.pos h_lt
        (Or.inl (h_val h_lt))
    have h_flow_adv : flowNesting tokens ps.advance.pos > 0 := by
      rw [h_adv_fn_eq]; omega
    -- Split on loop result
    split at h_ok
    · simp at h_ok
    · rename_i loop_result heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_result
      dsimp only [] at h_ok
      -- Loop invariant
      have h_empty : ∀ i : Fin (#[] : Array YamlValue).size,
          Scannable (#[] : Array YamlValue)[i] true := by
        intro ⟨_, hi⟩; simp at hi
      have h_loop := parseFlowSequenceLoop_wb tokens (k + 1) k (by omega)
          h_fpsv h_ih ps.advance #[] (items_arr, ps_loop) h_adv_tok
          h_flow_adv h_empty heq_loop
      have h_loop_fn : flowNesting tokens ps_loop.pos =
          flowNesting tokens ps.advance.pos := h_loop.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2
      have h_items_true := h_loop.1
      -- Handle optional flowSequenceEnd advance
      split at h_ok
      · -- peek? = some .flowSequenceEnd → advance
        rename_i h_peek_end
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        have ⟨h_lt_end, h_val_end⟩ := peek_some_bounded ps_loop
            .flowSequenceEnd h_peek_end
        have h_end_fn : flowNesting tokens ps_loop.advance.pos =
            flowNesting tokens ps_loop.pos - 1 := by
          simp only [ParseState.advance]; rw [← h_loop_tok]
          exact flowNesting_after_flow_end ps_loop.tokens ps_loop.pos h_lt_end
            (Or.inl (h_val_end h_lt_end))
            (by rw [h_loop_tok, h_loop_fn, h_adv_fn_eq]; omega)
        have h_net_fn : flowNesting tokens ps_loop.advance.pos =
            flowNesting tokens ps.pos := by
          rw [h_end_fn, h_loop_fn, h_adv_fn_eq]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Scannable.sequence .flow items_arr none none false h_items_true
        · intro _
          exact Scannable.sequence .flow items_arr none none true h_items_true
        · simp only [ParseState.advance]; exact h_net_fn
        · simp only [ParseState.advance]; exact h_loop_tok
      · -- peek? ≠ flowSequenceEnd → code returns .error, contradicts h_ok
        simp at h_ok

/-! ### §5d₃  Wadler-style "theorems for free" for `parseFlowMappingLoop`

These structural properties follow from the type signature and
accumulator pattern of `parseFlowMappingLoop`, independently of
its content-dispatch logic. They serve as regression guards:
after refactoring `parseFlowMappingLoop` (Pattern 4 mitigation),
re-proving these ensures behavioral preservation.

Note: Even these simple structural theorems exhibit Pattern 4 —
the monolithic loop body forces proofs to split through the full
Cartesian product of cases. `_pairs_grow` and `_prefix_preserved`
are stated with `sorry` as motivation for the refactoring:
after extracting `parseFlowMappingValue`, they become tractable.

See INTERACTIONS.md §Wadler-Style "Theorems for Free" as Refactoring Guards. -/

/-- Well-behavedness of `parseFlowMappingValue`:
    the returned value is Scannable, and the output state preserves
    flowNesting and tokens. -/
theorem parseFlowMappingValue_wb
    (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (savedPath : YamlPath) (keyContent : String)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok result) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
    result.2.tokens = tokens := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  have h1_tok : ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tokens = tokens :=
    (tryConsume_with_path_tokens ps (savedPath.push (.key keyContent)) .key).trans h_eq
  have h1_fn : flowNesting tokens ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.pos =
      flowNesting tokens ps.pos :=
    tryConsume_with_path_fn tokens ps (savedPath.push (.key keyContent)) .key h_eq
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  generalize hg1 : ParseState.tryConsume
    { ps with currentPath := savedPath.push (.key keyContent) }
    YamlToken.key = tc1 at h_ok
  have h1r_tok : tc1.2.tokens = tokens := hg1 ▸ h1_tok
  have h1r_fn : flowNesting tokens tc1.2.pos = flowNesting tokens ps.pos := hg1 ▸ h1_fn
  have h2_tok : (tc1.2.tryConsume .value).2.tokens = tokens :=
    (tryConsume_tokens tc1.2 .value).trans h1r_tok
  have h2_fn0 : flowNesting tokens (tc1.2.tryConsume .value).2.pos = flowNesting tokens tc1.2.pos :=
    tryConsume_flowNesting tokens tc1.2 .value h1r_tok
      (by intro h; cases h) (by intro h; cases h)
      (by intro h; cases h) (by intro h; cases h)
  generalize hg2 : ParseState.tryConsume tc1.2 YamlToken.value = tc2 at h_ok
  have h2r_tok : tc2.2.tokens = tokens := hg2 ▸ h2_tok
  have h2r_fn : flowNesting tokens tc2.2.pos = flowNesting tokens ps.pos := by
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
        have h_wb := parseNodeWB_apply h_ih h2r_tok heq_pn (by omega)
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

/-- Token preservation for `parseFlowMappingValue`: the token array is unchanged.
    Helper for `parseFlowMappingLoop_tokens_preserved`. -/
theorem parseFlowMappingValue_tokens_preserved
    (tokens : Array (Positioned YamlToken))
    (n : Nat) (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (savedPath : YamlPath) (keyContent : String)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok result) :
    result.2.tokens = tokens := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Token preservation chain: path → tryConsume .key → tryConsume .value
  have h1_tok : ({ ps with currentPath := savedPath.push (.key keyContent) }.tryConsume .key).2.tokens = tokens :=
    (tryConsume_with_path_tokens ps (savedPath.push (.key keyContent)) .key).trans h_eq
  generalize hg1 : ParseState.tryConsume
    { ps with currentPath := savedPath.push (.key keyContent) }
    YamlToken.key = tc1 at h_ok
  have h1r : tc1.2.tokens = tokens := hg1 ▸ h1_tok
  have h2_tok : (tc1.2.tryConsume .value).2.tokens = tokens :=
    (tryConsume_tokens tc1.2 .value).trans h1r
  generalize hg : ParseState.tryConsume tc1.2 .value = tc at h_ok
  have h_tcr_tok : tc.2.tokens = tokens := hg ▸ h2_tok
  split at h_ok
  · -- consumed = true → match peek?
    split at h_ok
    -- flowEntry | flowMappingEnd | none → emptyNode
    all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_tcr_tok))
    -- parseNode (remaining goal)
    split at h_ok <;> first | (simp at h_ok; done) | skip
    have h_wb := parseNodeWB_apply h_ih h_tcr_tok (by assumption) (by omega)
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_wb.2.2.2
  · -- consumed = false → emptyNode
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_tcr_tok

/-- Token preservation for `parseExplicitKey`: the token array is unchanged. -/
theorem parseExplicitKey_tokens_preserved
    (tokens : Array (Positioned YamlToken))
    (n : Nat) (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseExplicitKey ps fuel = .ok result) :
    result.2.tokens = tokens := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_eq))
  exact (parseNodeWB_apply h_ih h_eq h_ok (by omega)).2.2.2

/-- Well-behavedness of `parseExplicitKey`:
    the returned key is Scannable, flowNesting preserved, tokens preserved.
    Dispatches emptyNode (for `.value`/`.flowEntry`/`.flowMappingEnd`) or parseNode. -/
theorem parseExplicitKey_wb
    (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseExplicitKey ps fuel = .ok result) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
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
  · exact parseNodeWB_apply h_ih h_eq h_ok (by omega)

set_option maxHeartbeats 800000 in
/-- Token preservation: `parseFlowMappingLoop` never mutates the token array.
    Free theorem from the state-threading type.
    Proved via induction on fuel, using `parseFlowMappingValue_tokens_preserved`
    for the extracted value-dispatch and `parseExplicitKey_tokens_preserved`
    for explicit key dispatch. -/
theorem parseFlowMappingLoop_tokens_preserved
    (tokens : Array (Positioned YamlToken))
    (n : Nat)
    (_h_fpsv : FlowAwarePSV tokens) -- should this unused hypothesis be removed?
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≤ n)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
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
    · -- Exhaustively split all match/if in h_ok
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      -- Phase 1: Close error goals
      all_goals (try contradiction)
      all_goals (try (simp at h_ok))
      -- Phase 2: Close base case goals (both Except.ok wrapped and unwrapped)
      all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_eq))
      all_goals (try (simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only [ParseState.advance_tokens]; exact h_eq))
      all_goals (try (subst h_ok; exact h_eq))
      all_goals (try (subst h_ok; simp only [ParseState.advance_tokens]; exact h_eq))
      -- Phase 3: Recursive calls — explicit key (parseExplicitKey) or implicit key (parseNode)
      -- Explicit key paths: parseExplicitKey ps.advance k → parseFlowMappingValue → recurse
      all_goals (try (
        rename_i v_ek heq_ek _ v_pFMV heq_pFMV
        have h_kt := parseExplicitKey_tokens_preserved tokens n h_ih _ k
          (by omega) v_ek (by simp only [ParseState.advance_tokens]; exact h_eq) heq_ek
        have h_vt := parseFlowMappingValue_tokens_preserved tokens n h_ih _ k
          (by omega) _ _ v_pFMV h_kt heq_pFMV
        exact ih_fuel _ (by omega) _ h_vt h_ok))
      -- Implicit key paths: parseNode ps.advance k → parseFlowMappingValue → recurse
      all_goals (try (
        rename_i v_node heq_node _ v_pFMV heq_pFMV
        have h_nt := (parseNodeWB_apply h_ih
          (by simp only [ParseState.advance_tokens]; exact h_eq)
          heq_node (by omega)).2.2.2
        have h_vt := parseFlowMappingValue_tokens_preserved tokens n h_ih _ k
          (by omega) _ _ v_pFMV h_nt heq_pFMV
        exact ih_fuel _ (by omega) _ h_vt h_ok))
      -- Remaining: direct proof for parseNode ps k (no advance, h_eq direct)
      rename_i v_node heq_node _ v_pFMV heq_pFMV
      have h_nt := (parseNodeWB_apply h_ih h_eq heq_node (by omega)).2.2.2
      have h_vt := parseFlowMappingValue_tokens_preserved tokens n h_ih _ k
        (by omega) _ _ v_pFMV h_nt heq_pFMV
      exact ih_fuel _ (by omega) _ h_vt h_ok

/-- Monotonicity: `parseFlowMappingLoop` never shrinks the pairs array.
    Free theorem from the push-only accumulator pattern. -/
theorem parseFlowMappingLoop_pairs_grow
    (ps : ParseState) (fuel : Nat)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    result.1.size ≥ pairs.size := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok
    cases h_ok
    simp
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok
      cases h_ok
      simp
    · -- Exhaustively split all match/if in h_ok
      all_goals (try (split at h_ok))
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
      -- Close all goals: direct returns or recursive push branches
      all_goals (first
        | (cases h_ok; simp)
        | (simp only [Except.ok.injEq] at h_ok; cases h_ok; simp)
        | (have h_rec := ih_fuel _ _ h_ok
           simp [Array.size_push] at h_rec ⊢
           omega))

/-- Flow-version recursion helper for `parseFlowMappingLoop_wb`.
    Threads scannable / flowNesting / token facts through the recursive tail. -/
theorem flow_mapping_recurse
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_flow : flowNesting tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (key val : YamlValue) (ps_rec : ParseState) (k : Nat)
    (h_kf : Scannable key false) (h_vf : Scannable val false)
    (h_kt : Scannable key true) (h_vt : Scannable val true)
    (h_fn_rec : flowNesting tokens ps_rec.pos = flowNesting tokens ps.pos)
    (h_tok_rec : ps_rec.tokens = tokens)
    (h_rec : parseFlowMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseState) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      flowNesting tokens ps'.pos > 0 →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseFlowMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNesting tokens result.2.pos = flowNesting tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_flow_rec : flowNesting tokens ps_rec.pos > 0 := by rw [h_fn_rec]; exact h_flow
  have h_wb := ih_fuel ps_rec (pairs.push (key, val)) h_tok_rec h_flow_rec
      (push_pair_scannable h_pairs_false ⟨h_kf, h_vf⟩)
      (push_pair_scannable h_pairs_true ⟨h_kt, h_vt⟩) h_rec
  exact ⟨h_wb.1, h_wb.2.1, h_wb.2.2.1.trans h_fn_rec, h_wb.2.2.2⟩

/-- Helper: close a goal with parseExplicitKey ok + parseFlowMappingValue ok + recurse.
    Combines `parseExplicitKey_wb` + `parseFlowMappingValue_wb` + `flow_mapping_recurse`. -/
theorem explicitKey_val_recurse
    (tokens : Array (Positioned YamlToken))
    (n : Nat) (h_ih : ParseNodeWB tokens n)
    (ps : ParseState)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_flow : flowNesting tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (ps_ek : ParseState) (k : Nat) (h_kn : k ≤ n)
    (key : YamlValue) (ps_key : ParseState)
    (h_ek_tok : ps_ek.tokens = tokens)
    (h_ek_fn : flowNesting tokens ps_ek.pos = flowNesting tokens ps.pos)
    (heq_ek : parseExplicitKey ps_ek k = .ok (key, ps_key))
    (keyContent : String)
    (val : YamlValue) (ps_rec : ParseState)
    (heq_val : parseFlowMappingValue ps_key k ps_key.currentPath keyContent = .ok (val, ps_rec))
    (h_ok : parseFlowMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseState) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      flowNesting tokens ps'.pos > 0 →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseFlowMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNesting tokens result.2.pos = flowNesting tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_ek_flow : flowNesting tokens ps_ek.pos > 0 := by rw [h_ek_fn]; exact h_flow
  have h_kwb := parseExplicitKey_wb tokens n k h_kn h_ih ps_ek (key, ps_key) h_ek_tok heq_ek
  have h_key_flow : flowNesting tokens ps_key.pos > 0 := by
    rw [h_kwb.2.2.1]; exact h_ek_flow
  have h_vwb := parseFlowMappingValue_wb tokens n k h_kn h_ih ps_key ps_key.currentPath
    keyContent (val, ps_rec) h_kwb.2.2.2 heq_val
  exact flow_mapping_recurse tokens ps pairs result h_flow
    h_pairs_false h_pairs_true
    key val ps_rec k
    h_kwb.1 h_vwb.1
    (h_kwb.2.1 h_ek_flow) (h_vwb.2.1 h_key_flow)
    (h_vwb.2.2.1.trans (h_kwb.2.2.1.trans h_ek_fn)) h_vwb.2.2.2 h_ok ih_fuel

/-- Helper: close a goal with parseNode ok + parseFlowMappingValue ok + recurse.
    Used for implicit-key branches where parseNode is called directly. -/
theorem implicitKey_val_recurse
    (tokens : Array (Positioned YamlToken))
    (n : Nat) (h_ih : ParseNodeWB tokens n)
    (ps : ParseState)
    (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_flow : flowNesting tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (ps_pn : ParseState) (k : Nat) (h_kn : k ≤ n)
    (key : YamlValue) (ps_key : ParseState)
    (h_pn_tok : ps_pn.tokens = tokens)
    (h_pn_fn : flowNesting tokens ps_pn.pos = flowNesting tokens ps.pos)
    (heq_pn : parseNode ps_pn k = .ok (key, ps_key))
    (keyContent : String)
    (val : YamlValue) (ps_rec : ParseState)
    (heq_val : parseFlowMappingValue ps_key k ps_key.currentPath keyContent = .ok (val, ps_rec))
    (h_ok : parseFlowMappingLoop ps_rec k (pairs.push (key, val)) = .ok result)
    (ih_fuel : ∀ (ps' : ParseState) (pairs' : Array (YamlValue × YamlValue)),
      ps'.tokens = tokens →
      flowNesting tokens ps'.pos > 0 →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 false ∧ Scannable pairs'[i].2 false) →
      (∀ i : Fin pairs'.size,
        Scannable pairs'[i].1 true ∧ Scannable pairs'[i].2 true) →
      parseFlowMappingLoop ps' k pairs' = .ok result →
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
      (∀ i : Fin result.1.size,
        Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
      (flowNesting tokens result.2.pos = flowNesting tokens ps'.pos) ∧
      (result.2.tokens = tokens)) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  have h_kwb := parseNodeWB_apply h_ih h_pn_tok heq_pn (by omega)
  have h_key_flow : flowNesting tokens ps_pn.pos > 0 := by rw [h_pn_fn]; exact h_flow
  have h_ps_key_flow : flowNesting tokens ps_key.pos > 0 := by
    rw [h_kwb.2.2.1]; exact h_key_flow
  have h_vwb := parseFlowMappingValue_wb tokens n k h_kn h_ih ps_key ps_key.currentPath
    keyContent (val, ps_rec) h_kwb.2.2.2 heq_val
  exact flow_mapping_recurse tokens ps pairs result h_flow
    h_pairs_false h_pairs_true
    key val ps_rec k
    h_kwb.1 h_vwb.1
    (h_kwb.2.1 h_key_flow) (h_vwb.2.1 h_ps_key_flow)
    (h_vwb.2.2.1.trans (h_kwb.2.2.1.trans h_pn_fn)) h_vwb.2.2.2 h_ok ih_fuel

set_option maxHeartbeats 800000 in
/-- Loop invariant for `parseFlowMappingLoop`: accumulated pairs remain
    Scannable in both block and flow contexts, flowNesting is preserved,
    and the token array is unchanged.

    After extracting `parseExplicitKey`, the loop has only 2 content branches
    (explicit key via `parseExplicitKey`, implicit key via `parseNode`) × 2
    separator paths = 4 recursive goals, closed by the helper theorems. -/
theorem parseFlowMappingLoop_wb
    (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_ih : ParseNodeWB tokens n)
    (ps : ParseState) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_flow : flowNesting tokens ps.pos > 0)
    (h_pairs_false : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 false ∧ Scannable pairs[i].2 false)
    (h_pairs_true : ∀ i : Fin pairs.size,
      Scannable pairs[i].1 true ∧ Scannable pairs[i].2 true)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 false ∧ Scannable result.1[i].2 false) ∧
    (∀ i : Fin result.1.size,
      Scannable result.1[i].1 true ∧ Scannable result.1[i].2 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩
  | succ k ih_fuel =>
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    -- First match: peek? = flowMappingEnd vs other
    split at h_ok
    · -- flowMappingEnd → return (pairs, ps)
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩
    · -- not flowMappingEnd → separator handling then content dispatch
      -- Exhaustively split all remaining match/if in h_ok
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      all_goals (try (split at h_ok))
      -- Phase 1: Close error / contradiction goals
      all_goals (try contradiction)
      -- Phase 2: Close direct-return and advance-return goals
      all_goals first
        | (simp only [Except.ok.injEq] at h_ok; subst h_ok;
           exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩)
        | (simp only [Except.ok.injEq] at h_ok; cases h_ok;
           exact ⟨h_pairs_false, h_pairs_true, rfl, h_eq⟩)
        | (simp only [Except.ok.injEq] at h_ok; cases h_ok;
           have h_sep : ps.peek? = some YamlToken.flowEntry := by assumption;
           have h_adv_fn := advance_preserves_flowNesting tokens ps h_sep h_eq
             (by exact fun h => nomatch h) (by exact fun h => nomatch h)
             (by exact fun h => nomatch h) (by exact fun h => nomatch h);
           exact ⟨h_pairs_false, h_pairs_true, h_adv_fn,
                  by simp [ParseState.advance, h_eq]⟩)
        | skip
      -- Phase 3: Explicit key (parseExplicitKey) + parseFlowMappingValue + recurse
      all_goals first
        | (rename_i v_ek heq_ek _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_ek;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact explicitKey_val_recurse tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true _ k (by omega) key ps_key
             (by simp [ParseState.advance, h_eq]) (by
               have h_sep : ps.peek? = some YamlToken.flowEntry := by assumption
               have h_adv_fn := advance_preserves_flowNesting tokens ps h_sep h_eq
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               have h_key_peek : ps.advance.peek? = some YamlToken.key := by assumption
               have h_key_fn := advance_preserves_flowNesting tokens ps.advance h_key_peek
                 (by simp [ParseState.advance, h_eq])
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               rw [h_key_fn, h_adv_fn])
             heq_ek _ val ps_rec heq_val h_ok (ih_fuel (by omega)))
        | (rename_i v_ek heq_ek _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_ek;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact explicitKey_val_recurse tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true _ k (by omega) key ps_key
             (by simp [ParseState.advance, h_eq]) (by
               have h_key_peek : ps.peek? = some YamlToken.key := by assumption
               have h_key_fn := advance_preserves_flowNesting tokens ps h_key_peek h_eq
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               exact h_key_fn)
             heq_ek _ val ps_rec heq_val h_ok (ih_fuel (by omega)))
        | skip
      -- Phase 4: Implicit key (parseNode) + parseFlowMappingValue + recurse
      all_goals first
        | (rename_i v_node heq_node _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_node;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact implicitKey_val_recurse tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true _ k (by omega) key ps_key
             (by simp [ParseState.advance, h_eq]) (by
               have h_sep : ps.peek? = some YamlToken.flowEntry := by assumption
               have h_adv_fn := advance_preserves_flowNesting tokens ps h_sep h_eq
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
                 (by exact fun h => nomatch h) (by exact fun h => nomatch h)
               exact h_adv_fn)
             heq_node _ val ps_rec heq_val h_ok (ih_fuel (by omega)))
        | (rename_i v_node heq_node _ v_val heq_val;
           obtain ⟨key, ps_key⟩ := v_node;
           obtain ⟨val, ps_rec⟩ := v_val;
           dsimp only [] at h_ok;
           exact implicitKey_val_recurse tokens n h_ih ps pairs result h_flow
             h_pairs_false h_pairs_true ps k (by omega) key ps_key
             h_eq rfl heq_node _ val ps_rec heq_val h_ok (ih_fuel (by omega)))

/-- `parseFlowMapping` well-behaved given parseNode IH.
    Requires `h_matched` for the same reason as `parseFlowSequence_wb`:
    the else-branch (missing `flowMappingEnd`) has an off-by-one
    flowNesting that needs bracket-matching to rule out. -/
theorem parseFlowMapping_wb (tokens : Array (Positioned YamlToken))
    (fuel : Nat) (h_fpsv : FlowAwarePSV tokens) (h_ih : ParseNodeWB tokens fuel)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_peek : ps.peek? = some .flowMappingStart)
    (h_ok : parseFlowMapping ps fuel = .ok result) :
    (Scannable result.1 false) ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    (flowNesting tokens result.2.pos = flowNesting tokens ps.pos) ∧
    (result.2.tokens = tokens) := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_adv_tok : ps.advance.tokens = tokens := by
      simp [ParseState.advance, h_eq]
    have ⟨h_lt, h_val⟩ := peek_some_bounded ps .flowMappingStart h_peek
    have h_adv_fn_eq : flowNesting tokens ps.advance.pos =
        flowNesting tokens ps.pos + 1 := by
      simp only [ParseState.advance]; subst h_eq
      exact flowNesting_after_flow_start_eq ps.tokens ps.pos h_lt
        (Or.inr (h_val h_lt))
    have h_flow_adv : flowNesting tokens ps.advance.pos > 0 := by
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
      have h_loop := parseFlowMappingLoop_wb tokens (k + 1) k (by omega)
          h_ih ps.advance #[] (pairs_arr, ps_loop) h_adv_tok
          h_flow_adv h_empty_f h_empty_t heq_loop
      have h_loop_fn : flowNesting tokens ps_loop.pos =
          flowNesting tokens ps.advance.pos := h_loop.2.2.1
      have h_loop_tok : ps_loop.tokens = tokens := h_loop.2.2.2
      have h_pairs_false := h_loop.1
      have h_pairs_true := h_loop.2.1
      split at h_ok
      · rename_i h_peek_end
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        have ⟨h_lt_end, h_val_end⟩ := peek_some_bounded ps_loop
            .flowMappingEnd h_peek_end
        have h_end_fn : flowNesting tokens ps_loop.advance.pos =
            flowNesting tokens ps_loop.pos - 1 := by
          simp only [ParseState.advance]; rw [← h_loop_tok]
          exact flowNesting_after_flow_end ps_loop.tokens ps_loop.pos h_lt_end
            (Or.inr (h_val_end h_lt_end))
            (by rw [h_loop_tok, h_loop_fn, h_adv_fn_eq]; omega)
        have h_net_fn : flowNesting tokens ps_loop.advance.pos =
            flowNesting tokens ps.pos := by
          rw [h_end_fn, h_loop_fn, h_adv_fn_eq]; omega
        refine ⟨?_, ?_, ?_, ?_⟩
        · exact Scannable.mapping .flow pairs_arr none none false
            (fun i => (h_pairs_true i).1) (fun i => (h_pairs_true i).2)
        · intro _
          exact Scannable.mapping .flow pairs_arr none none true
            (fun i => (h_pairs_true i).1) (fun i => (h_pairs_true i).2)
        · simp only [ParseState.advance]; exact h_net_fn
        · simp only [ParseState.advance]; exact h_loop_tok
      · simp at h_ok

/-- Base case: at fuel 0, `parseNode` always returns error, so `ParseNodeWB`
    is vacuously true. -/
theorem parseNode_wb_zero (tokens : Array (Positioned YamlToken)) :
    ParseNodeWB tokens 0 := by
  intro ps m val ps' hm h_eq h_ok
  have : m = 0 := by omega
  subst this
  -- parseNode ps 0 returns Except.error, contradicting h_ok : ... = .ok ...
  unfold parseNode at h_ok
  simp at h_ok

/-- Well-behavedness of `parseNodeContent`:
    the returned value is Scannable, and the output state preserves
    flowNesting and tokens.
    Extracted for use by `parseNode_wb_all`. -/
theorem parseNodeContent_wb (tokens : Array (Positioned YamlToken))
    (n fuel : Nat) (h_fuel : fuel ≤ n)
    (h_fpsv : FlowAwarePSV tokens) (h_ih : ParseNodeWB tokens n)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (props : NodeProperties)
    (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseNodeContent ps fuel props = .ok result) :
    Scannable result.1 false ∧
    (flowNesting tokens ps.pos > 0 → Scannable result.1 true) ∧
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos ∧
    result.2.tokens = tokens := by
  -- Derive ParseNodeWB at fuel level (sub-parsers receive fuel, not n)
  have h_ih_fuel : ParseNodeWB tokens fuel :=
    fun ps' m val ps'' hm htok hok => h_ih ps' m val ps'' (Nat.le_trans hm h_fuel) htok hok
  unfold parseNodeContent at h_ok
  split at h_ok
  -- Case: scalar token → construct scalar value and advance
  · rename_i content style heq_peek
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    have ⟨h_lt, h_val⟩ := peek_some_bounded ps (.scalar content style) heq_peek
    have h_lt_tok : ps.pos < tokens.size := by rw [← h_eq]; exact h_lt
    have h_tok : (tokens[ps.pos]'h_lt_tok).val = .scalar content style := by
      have h1 := h_val h_lt; simp only [h_eq] at h1; exact h1
    exact ⟨scalar_from_token_scannable tokens h_fpsv.1 ps.pos h_lt_tok content style
             h_tok props.tag props.anchor,
           fun h_flow => scalar_from_flow_token_scannable tokens h_fpsv ps.pos h_lt_tok
             content style h_tok h_flow props.tag props.anchor true,
           advance_preserves_flowNesting tokens ps heq_peek h_eq
             (fun h => nomatch h) (fun h => nomatch h)
             (fun h => nomatch h) (fun h => nomatch h),
           by simp [ParseState.advance, h_eq]⟩
  -- Case: blockSequenceStart
  · rename_i heq_peek
    exact parseBlockSequence_wb tokens fuel h_fpsv h_ih_fuel ps result h_eq heq_peek h_ok
  -- Case: blockMappingStart
  · rename_i heq_peek
    exact parseBlockMapping_wb tokens fuel h_ih_fuel ps result h_eq heq_peek h_ok
  -- Case: blockEntry → implicit block sequence
  · exact parseImplicitBlockSequence_wb tokens fuel h_ih_fuel ps result h_eq h_ok
  -- Case: flowSequenceStart
  · rename_i heq_peek
    exact parseFlowSequence_wb tokens fuel h_fpsv h_ih_fuel h_matched ps result h_eq heq_peek h_ok
  -- Case: flowMappingStart
  · rename_i heq_peek
    exact parseFlowMapping_wb tokens fuel h_fpsv h_ih_fuel h_matched ps result h_eq heq_peek h_ok
  -- Case: empty content (no token or non-content token)
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact ⟨empty_scalar_scannable props.tag props.anchor false,
           fun _ => empty_scalar_scannable props.tag props.anchor true,
           rfl, h_eq⟩

/-! ### Wadler guards for `parseNode` (Pattern 4b regression tests)

W1: The alias branch of `parseNode` preserves the token array.
W2: The alias branch preserves flowNesting.

These serve as refactoring guards — if `parseNode` is restructured
(e.g., extracting `validateNodeProps`), these theorems must continue to
hold on the new implementation. -/

-- `validateNodeProps` returns Unit on success and never modifies the parse state.
-- After `Except.bind (validateNodeProps ps p props) (fun () => k ps)`, the
-- continuation receives the SAME `ps`.
theorem validateNodeProps_ok (ps : ParseState) (prePropPos : Nat)
    (props : NodeProperties)
    (_ : validateNodeProps ps prePropPos props = .ok ()) :
    True := trivial

-- W1: Alias branch preserves tokens
theorem parseNode_alias_tokens (ps : ParseState) (fuel : Nat) (name : String)
    (h_peek : ps.peek? = some (.alias name))
    (result : YamlValue × ParseState)
    (h_ok : parseNode ps (fuel + 1) = .ok result) :
    result.2.tokens = ps.tokens := by
  unfold parseNode at h_ok
  simp only [h_peek, bind, Except.bind, pure, Except.pure] at h_ok
  -- Split on the §7.1 alias validation check
  split at h_ok
  · contradiction  -- undefinedAlias error branch
  · split at h_ok <;> {
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨-, rfl⟩ := h_ok; simp [ParseState.advance]
    }

-- W2: Alias branch preserves flowNesting
theorem parseNode_alias_flowNesting (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (fuel : Nat) (name : String)
    (h_peek : ps.peek? = some (.alias name))
    (h_eq : ps.tokens = tokens)
    (result : YamlValue × ParseState)
    (h_ok : parseNode ps (fuel + 1) = .ok result) :
    flowNesting tokens result.2.pos = flowNesting tokens ps.pos := by
  unfold parseNode at h_ok
  simp only [h_peek, bind, Except.bind, pure, Except.pure] at h_ok
  -- Split on the §7.1 alias validation check
  split at h_ok
  · contradiction  -- undefinedAlias error branch
  · -- After simplification, the if-then-else on trackPositions remains
    split at h_ok <;> {
      simp only [Except.ok.injEq] at h_ok
      obtain ⟨-, rfl⟩ := h_ok
      -- Both branches: pos = ps.advance.pos (nodePositions/currentPath don't affect pos)
      simp only [ParseState.advance]
      exact advance_preserves_flowNesting tokens ps h_peek h_eq
        (fun h => nomatch h) (fun h => nomatch h)
        (fun h => nomatch h) (fun h => nomatch h)
    }

/-- **Key lemma**: `parseNode` is well-behaved at every fuel level.

    The proof is by strong induction on `n`. At fuel `n + 1`, `parseNode`
    dispatches to 10 sub-functions (all at fuel `≤ n`), which in turn
    call `parseNode` at fuel `≤ n`. The induction hypothesis `ParseNodeWB tokens n`
    covers all these calls.

    **Sub-function scannability** (each case of parseNode):
    - Alias: `Scannable (.alias name) inFlow` trivially.
    - Scalar: `scalar_from_token_scannable` or `scalar_from_flow_token_scannable`.
    - Empty: `empty_scalar_scannable`.
    - Block seq/map/implicit: items from `parseNode` at fuel `n`, Scannable false by IH.
    - Flow seq/map: items from `parseNode` at fuel `n` at `flowNesting > 0`,
      Scannable true by IH. Requires `flowNesting_pos_after_flow_start` and
      flow-nesting preservation across `parseNode` calls.
    - `parseSinglePairMapping`: key/value from `parseNode` in flow context.

    **Flow nesting preservation** (property 3):
    - Non-flow tokens (scalar, alias, anchor, tag, key, value, block*):
      `flowNesting_non_flow_step`.
    - Flow start+end pairs: net zero change (start +1, end −1).
    - Properties (anchor, tag): non-flow tokens, preserved. -/
theorem parseNode_wb_all (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens) :
    ∀ n, ParseNodeWB tokens n := by
  intro n
  induction n with
  | zero => exact parseNode_wb_zero tokens
  | succ n ih =>
    intro ps m val ps' hm h_eq h_ok
    -- m ≤ n + 1, so m = 0 (handled) or m = k + 1 for some k ≤ n
    by_cases hm0 : m = 0
    · subst hm0; unfold parseNode at h_ok; simp at h_ok
    · -- m = k + 1
      obtain ⟨k, rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
      have hk : k ≤ n := by omega
      -- Unfold parseNode at fuel k + 1
      unfold parseNode at h_ok
      simp only [bind, Except.bind, pure, Except.pure] at h_ok
      -- Split on ps.peek? for alias check
      split at h_ok
      · -- Alias branch: some (.alias name) → return
        rename_i name heq_peek
        -- Split on the §7.1 alias validation check
        split at h_ok
        · contradiction  -- undefinedAlias error branch
        · -- The alias branch has an if-then-else on trackPositions
          split at h_ok
          · -- trackPositions = true
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
            exact ⟨.alias name false,
                   fun _ => .alias name true,
                   advance_preserves_flowNesting tokens ps heq_peek h_eq
                     (fun h => nomatch h) (fun h => nomatch h)
                     (fun h => nomatch h) (fun h => nomatch h),
                   by simp [ParseState.advance, h_eq]⟩
          · -- trackPositions = false
            simp only [Except.ok.injEq] at h_ok
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
            exact ⟨.alias name false,
                   fun _ => .alias name true,
                   advance_preserves_flowNesting tokens ps heq_peek h_eq
                     (fun h => nomatch h) (fun h => nomatch h)
                     (fun h => nomatch h) (fun h => nomatch h),
                   by simp [ParseState.advance, h_eq]⟩
      · -- Non-alias branch: _ => pure (), then chain through
        -- Split on parseNodeProperties result
        split at h_ok
        · contradiction  -- parseNodeProperties error
        · rename_i v_props heq_props
          -- Split on validateNodeProps
          split at h_ok
          · contradiction  -- validateNodeProps error
          · -- validateNodeProps ok → Unit, continuation gets same ps
            -- Split on parseNodeContent
            split at h_ok
            · contradiction  -- parseNodeContent error
            · rename_i v_content heq_content
              simp only [Except.ok.injEq] at h_ok
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_ok
              -- Chain the preservation lemmas
              -- parseNodeProperties preserves tokens and flowNesting
              have h_props_tok : v_props.2.tokens = tokens :=
                (parseNodeProperties_tokens ps v_props.1 v_props.2
                  heq_props).trans h_eq
              have h_props_fn : flowNesting tokens v_props.2.pos = flowNesting tokens ps.pos :=
                parseNodeProperties_flowNesting tokens ps v_props.1 v_props.2
                  heq_props h_eq
              -- parseNodeContent well-behavedness
              have h_content := parseNodeContent_wb tokens n k hk h_fpsv ih h_matched
                v_props.2 v_props.1 v_content h_props_tok heq_content
              -- applyNodeFinalization results (opaque form)
              have h_fin_pos := applyNodeFinalization_pos
                v_content.1 v_content.2 v_props.1
                (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
              have h_fin_tok := applyNodeFinalization_tokens
                v_content.1 v_content.2 v_props.1
                (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
              -- Goal has applyNodeFinalization expanded (rfl subst reduces it).
              -- Use `exact` with opaque-form proofs; Lean matches by defeq.
              exact ⟨
                applyNodeFinalization_scannable
                  v_content.1 v_content.2 v_props.1
                  (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
                  false h_content.1,
                fun h_flow =>
                  applyNodeFinalization_scannable v_content.1 v_content.2 v_props.1
                    (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })
                    true (h_content.2.1 (by rw [h_props_fn]; exact h_flow)),
                show flowNesting tokens (applyNodeFinalization v_content.1 v_content.2 v_props.1
                  (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos =
                  flowNesting tokens ps.pos from by
                  rw [h_fin_pos, h_content.2.2.1, h_props_fn],
                show (applyNodeFinalization v_content.1 v_content.2 v_props.1
                  (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.tokens = tokens from by
                  rw [h_fin_tok]; exact h_content.2.2.2⟩

/-! ### §5e₂  Helper lemmas: token-array preservation through sub-operations

`tryConsume`, `parseDirectives`, and `parseNode` all preserve the
token array. These facts are used by `parseDocument_tokens_preserved`.
-/

/-- `parseDirectives` preserves the token array. -/
theorem parseDirectives_tokens (ps : ParseState) :
    (parseDirectives ps).2.tokens = ps.tokens := by
  unfold parseDirectives
  simp only [Id.run]
  generalize ps.tokens.size - ps.pos = fuel
  simp only [Std.Legacy.Range.forIn_eq_forIn_range', Std.Legacy.Range.size,
             Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize List.range' 0 fuel 1 = ls
  suffices h : ∀ (acc : MProd (Array Directive) ParseState),
      acc.2.tokens = ps.tokens →
      (Id.run (do
          let r ← @forIn Id (List Nat) Nat _ _ ls acc (fun x r =>
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
  | cons x xs ih =>
    simp only [ForIn.forIn, List.forIn'_cons, Id.run, bind, pure] at ih ⊢
    split
    · rename_i b heq
      revert heq; split
      · intro heq; contradiction
      · intro heq; contradiction
      · intro heq
        have := ForInStep.done.inj heq
        subst this; exact h_inv
    · rename_i b heq
      apply ih; revert heq; split
      · intro heq
        have := ForInStep.yield.inj heq
        subst this; simp [ParseState.advance, h_inv]
      · intro heq
        have := ForInStep.yield.inj heq
        subst this; simp [ParseState.advance, h_inv]
      · intro heq; contradiction

/-- `parseNode` preserves the token array: the output state has the
    same tokens as the input state. Follows from the 4th conjunct of
    `parseNode_wb_all` (the `ParseNodeWB` inductive well-behavedness). -/
theorem parseNode_tokens_preserved
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (fuel : Nat) (result : YamlValue × ParseState)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseNode ps fuel = .ok result) :
    result.2.tokens = ps.tokens := by
  have h_wb := parseNode_wb_all tokens h_fpsv h_matched fuel
    ps fuel result.1 result.2 (Nat.le.refl) h_eq
    (by rw [Prod.eta]; exact h_ok)
  rw [h_wb.2.2.2, h_eq]

/-! ### §5f  parseDocument output scannability

`parseDocument` constructs a document by calling `parseDirectives`,
optionally consuming `documentStart`, running error checks, and then
dispatching to either `emptyNode` or `parseNode`.

The root node value is either `emptyNode` (trivially Scannable at any
flow context — empty plain scalar) or the result of `parseNode ps fuel`
where `fuel = 4 * ps.tokens.size + 4` and `ps.tokens = tokens`.

By `parseNode_wb_all`, the root value satisfies `Scannable _ false`.

**Key invariant**: `parseDirectives`, tag handle assignment, and
`tryConsume .documentStart` do not modify `ps.tokens`. Only `ps.pos`,
`ps.tagHandles`, and similar metadata change.
-/

/-- `prepareDocumentState` preserves the token array. -/
theorem prepareDocumentState_tokens_preserved
    (ps : ParseState) (dirs : Array Directive) (ps' : ParseState)
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
              tryConsume_tokens _ _
      _ = (parseDirectives ps).2.tokens := rfl
      _ = ps.tokens := parseDirectives_tokens ps
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

/-- `parseDocument` preserves the token array — only metadata changes.
    Uses `prepareDocumentState_tokens_preserved` and `parseNode_tokens_preserved`. -/
theorem parseDocument_tokens_preserved
    (ps : ParseState) (doc : YamlDocument) (ps' : ParseState)
    (h_fpsv : FlowAwarePSV ps.tokens)
    (h_matched : FlowBracketsMatched ps.tokens)
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
      prepareDocumentState_tokens_preserved ps dirs ps1 h_prep
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
        (parseNode_tokens_preserved ps.tokens h_fpsv h_matched ps1 (4 * ps1.tokens.size + 4)
          (val, ps2) h_prep_tok h_pn).trans h_prep_tok
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨_, rfl⟩ := h_ok
      exact h_node_tok

/-- **Factoring lemma**: `parseDocument`'s root value is either `emptyNode`
    or the result of `parseNode` at some state with `tokens` preserved.

    `parseDocument` only calls `parseNode` with:
    - `ps_inner.tokens = ps.tokens` (directives/tryConsume don't modify tokens)
    - `fuel = 4 * ps.tokens.size + 4` (the fuel bound from parseDocument)

    This lemma captures the essential content-dispatch structure without
    requiring full do-notation reasoning. -/
theorem parseDocument_value_cases
    (ps : ParseState) (doc : YamlDocument) (ps' : ParseState)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    (doc.value = emptyNode) ∨
    (∃ ps_inner ps_after,
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
      prepareDocumentState_tokens_preserved ps dirs ps1 h_prep
    split at h_ok
    -- documentEnd, streamEnd, none → emptyNode
    all_goals (try (
      simp only [Except.ok.injEq, Prod.mk.injEq] at h_ok
      obtain ⟨h_doc, _⟩ := h_ok
      subst h_doc; left; rfl))
    -- else → parseNode
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

/-- **C2a·core**: A document produced by `parseDocument` has a `Scannable` root value.

    This is the core argument connecting parse-tree construction to the
    `Scannable` predicate. `parseStream_output_scannable` follows from
    this plus the stream-level loop decomposition.

    **Proof**: By `parseDocument_value_cases`, `doc.value` is either
    `emptyNode` (trivially Scannable via `empty_scalar_scannable`) or
    the result of `parseNode` at fuel `4 * tokens.size + 4` with
    `ps_inner.tokens = tokens`. By `parseNode_wb_all`, the latter
    satisfies `Scannable doc.value false`. -/
theorem parseDocument_scannable
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (doc : YamlDocument) (ps' : ParseState)
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (h_eq : ps.tokens = tokens)
    (h_ok : parseDocument ps = .ok (doc, ps')) :
    Scannable doc.value false := by
  rcases parseDocument_value_cases ps doc ps' h_ok with
    h_empty | ⟨ps_inner, ps_after, h_eq_inner, h_pn⟩
  · -- emptyNode case: empty plain scalar is trivially Scannable
    rw [h_empty]
    exact empty_scalar_scannable none none false
  · -- parseNode case: apply parseNode_wb_all
    have h_tok : ps_inner.tokens = tokens := by rw [h_eq_inner, h_eq]
    let fuel := 4 * ps.tokens.size + 4
    have h_wb := parseNode_wb_all tokens h_fpsv h_matched fuel
    exact (h_wb ps_inner fuel doc.value ps_after (by omega) h_tok h_pn).1

/-! ### §5g  parseStream loop decomposition

`parseStream` calls `parseStreamLoop`, which iterates `parseDocument`
via structural recursion on fuel.

The loop invariant has two parts:
1. `ps.tokens = tokens` — preserved because `parseDocument` preserves
   tokens (§5f) and the stream-level mutations (anchor reset,
   tryConsume documentEnd) only touch metadata.
2. Every doc in the accumulator was produced by `parseDocument` with
   `ps.tokens = tokens` — new docs satisfy this by construction,
   and the accumulator is monotonically extended.

After the loop, the result docs = final accumulator, and the invariant
gives the desired conclusion.
-/

/-- `ParseState.expect` preserves the token array. -/
theorem expect_tokens (ps ps' : ParseState) (tok : YamlToken) (desc : String)
    (h : ps.expect tok desc = .ok ps') : ps'.tokens = ps.tokens := by
  unfold ParseState.expect at h
  split at h
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; simp [ParseState.advance]
    · simp at h
  · simp at h

/-- **Loop lemma**: every document in `parseStreamLoop`'s output was either
    already in the accumulator or produced by `parseDocument` with the
    same token array.

    This is the core inductive structure that makes `parseStream_doc_from_parseDocument`
    tractable after extracting `parseStreamLoop`. -/
theorem parseStreamLoop_docs_from_parseDocument
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens) (h_matched : FlowBracketsMatched tokens)
    (ps : ParseState) (docs : Array YamlDocument)
    (streamState : StreamState) (fuel : Nat)
    (result : Array YamlDocument)
    (h_eq : ps.tokens = tokens)
    (h_acc : ∀ doc ∈ docs.toList, ∃ ps_d ps_d',
        ps_d.tokens = tokens ∧ parseDocument ps_d = .ok (doc, ps_d'))
    (h_ok : parseStreamLoop ps docs streamState fuel = .ok result) :
    ∀ doc ∈ result.toList, ∃ ps_d ps_d',
        ps_d.tokens = tokens ∧ parseDocument ps_d = .ok (doc, ps_d') := by
  induction fuel generalizing ps docs streamState with
  | zero =>
    simp only [parseStreamLoop] at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
  | succ fuel ih =>
    unfold parseStreamLoop at h_ok
    -- Split on ps.peek?
    split at h_ok
    · -- streamEnd → result = docs
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · -- none → result = docs
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc
    · -- some tok → validation + parseDocument + recurse
      rename_i tok
      split at h_ok
      · simp at h_ok  -- validation failure → error, contradiction
      · -- validation passed
        -- Clear `let savedPos := ps.pos` so we can see the parseDocument match
        dsimp only [] at h_ok
        -- Case-analyze the parseDocument result
        generalize h_pd : parseDocument ps = pd_result at h_ok
        cases pd_result with
        | error e => simp at h_ok
        | ok val =>
          obtain ⟨doc_new, ps'⟩ := val
          -- Reduce the Except.ok match and remaining let bindings
          dsimp only [] at h_ok
          -- Tokens preserved through parseDocument
          have h_pd_tok : ps'.tokens = tokens :=
            (parseDocument_tokens_preserved ps doc_new ps'
              (h_eq ▸ h_fpsv) (h_eq ▸ h_matched) h_pd).trans h_eq
          -- Tokens preserved through struct update + tryConsume
          let ps_reset : ParseState :=
            { ps' with anchors := #[], nodePositions := #[], currentPath := #[] }
          have h_next_tok : (ps_reset.tryConsume .documentEnd).2.tokens = tokens :=
            (tryConsume_tokens _ _).trans h_pd_tok
          -- The accumulator grows by one doc
          have h_acc' : ∀ doc ∈ (docs.push doc_new).toList, ∃ ps_d ps_d',
              ps_d.tokens = tokens ∧ parseDocument ps_d = .ok (doc, ps_d') := by
            intro d hd
            rw [Array.toList_push] at hd
            simp only [List.mem_append, List.mem_singleton] at hd
            rcases hd with hd_old | rfl
            · exact h_acc d hd_old
            · exact ⟨ps, ps', h_eq, h_pd⟩
          -- Stuck check: if stuck, result = docs.push doc_new
          split at h_ok
          · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact h_acc'
          · -- Recurse
            exact ih _ _ _ h_next_tok h_acc' h_ok

/-- **Loop decomposition**: every document in `parseStream`'s output was
    produced by `parseDocument` with the same token array.

    This captures the essential structure of the `parseStreamLoop`
    recursion: each iteration calls `parseDocument` on a `ParseState` whose
    `.tokens` field is the original `tokens` (since only `.pos`, `.anchors`,
    `.nodePositions`, `.currentPath`, `.tagHandles` change). -/
theorem parseStream_doc_from_parseDocument
    (tokens : Array (Positioned YamlToken))
    (h_fpsv : FlowAwarePSV tokens) (h_matched : FlowBracketsMatched tokens)
    (docs : Array YamlDocument)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ ps ps',
      ps.tokens = tokens ∧ parseDocument ps = .ok (doc, ps') := by
  unfold parseStream at h_parse
  simp only [bind, Except.bind] at h_parse
  split at h_parse
  · simp at h_parse
  · rename_i ps_start h_expect
    have h_tok : ps_start.tokens = tokens :=
      (expect_tokens _ _ _ _ h_expect).trans (by simp)
    exact parseStreamLoop_docs_from_parseDocument tokens h_fpsv h_matched
      ps_start #[] .initial tokens.size docs h_tok
      (by intro d hd; simp at hd) h_parse

/-- C2a: Every document produced by `parseStream` from scanner tokens
    has a `Scannable` value tree.

    **Proof**: By `parseStream_doc_from_parseDocument`, each document
    was produced by `parseDocument` with `ps.tokens = tokens`. By
    `parseDocument_scannable`, the root value is `Scannable _ false`. -/
theorem parseStream_output_scannable
    (tokens : Array (Positioned YamlToken))
    (docs : Array YamlDocument)
    (h_fpsv : FlowAwarePSV tokens)
    (h_matched : FlowBracketsMatched tokens)
    (h_parse : parseStream tokens = .ok docs) :
    ∀ doc ∈ docs.toList, Scannable doc.value false := by
  intro doc hdoc
  obtain ⟨ps, ps', h_eq, h_ok⟩ :=
    parseStream_doc_from_parseDocument tokens h_fpsv h_matched docs h_parse doc hdoc
  exact parseDocument_scannable tokens ps doc ps' h_fpsv h_matched h_eq h_ok


/-! ### §5f  Parser position monotonicity

Every successfully-parsed call to `parseNode` (and its sub-parsers) returns
a state whose `.pos` is ≥ the input `.pos`. No parser function ever
*decreases* the parse position.

This is needed for fuel-sufficiency arguments: each iteration of a flow
loop advances position by ≥1 token, so the loop terminates within
`tokens.size` iterations.

The proof is by strong induction on fuel, mirroring `parseNode_wb_all`. -/

/-- Position monotonicity property for `parseNode` at fuel ≤ n. -/
def ParseNodePosMono (n : Nat) : Prop :=
  ∀ (ps : ParseState) (m : Nat) (val : YamlValue) (ps' : ParseState),
    m ≤ n → parseNode ps m = .ok (val, ps') → ps'.pos ≥ ps.pos

/-- Projection helper for `ParseNodePosMono`. -/
theorem parseNodePosMono_apply {n : Nat} (h_ih : ParseNodePosMono n)
    {ps : ParseState} {m : Nat} {v : YamlValue × ParseState}
    (h_ok : parseNode ps m = .ok v)
    (h_le : m ≤ n := by omega) :
    v.2.pos ≥ ps.pos :=
  h_ih ps m v.1 v.2 h_le h_ok

/-- `tryConsume` doesn't decrease position. -/
theorem tryConsume_pos_mono (ps : ParseState) (tok : YamlToken) :
    (ps.tryConsume tok).2.pos ≥ ps.pos := by
  unfold ParseState.tryConsume
  split
  · split
    · simp [ParseState.advance]
    · exact Nat.le_refl _
  · exact Nat.le_refl _

-- `parseNodeProperties` doesn't decrease position.
set_option maxRecDepth 10000 in
set_option maxHeartbeats 800000000 in
theorem parseNodeProperties_pos_mono (ps : ParseState)
    (props : NodeProperties) (ps' : ParseState)
    (h : parseNodeProperties ps = .ok (props, ps')) :
    ps'.pos ≥ ps.pos := by
  -- parseNodeProperties only modifies pos via advance (for anchor/tag tokens).
  -- The loop runs 0–2 iterations, each advancing 0 or 1 times.
  -- Reuse the token-preservation proof structure.
  unfold parseNodeProperties at h
  unfold ForIn.forIn instForInOfForIn' at h
  unfold ForIn'.forIn' Std.Legacy.Range.instForIn'NatInferInstanceMembershipOfMonad at h
  unfold Std.Legacy.Range.forIn' at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [] at h
  try unfold_loop_at h
  simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure, dite_true] at h
  try unfold_loop_at h
  try simp (config := { decide := true, iota := false }) only [
    bind, Except.bind, pure, Except.pure] at h
  -- Split outermost Except (final result)
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
        -- break on first iteration — no advance or 0 advances
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
            try all_goals (simp [ParseState.advance]; try omega)
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
            all_goals (simp [ParseState.advance]; try omega)


/-! #### Block sequence position monotonicity -/

theorem parseBlockSequenceLoop_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (items : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseBlockSequenceLoop ps fuel items = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next => -- peek? = some .blockEntry
      split at h_ok
      -- All arms handled uniformly
      all_goals {
        first
        | { -- OR-pattern arms: direct recurse with ps.advance
            have h_rec := ih_fuel h_ih_k ps.advance _ h_ok
            simp [ParseState.advance] at h_rec; omega }
        | { -- Default arm: parseNode then recurse
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨val, ps₃⟩ := pn_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMono_apply h_ih heq_pn
              have h_rec := ih_fuel h_ih_k
                { ps₃ with currentPath := _ } _ h_ok
              simp [ParseState.advance] at h_rec h_pn; omega } }
    next => -- peek? ≠ blockEntry
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseBlockSequence_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_ok : parseBlockSequence ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok  -- fuel = 0
  · rename_i k
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok  -- loop error
    · rename_i loop_res heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseBlockSequenceLoop_pos_mono k h_ih_k ps.advance #[] _ heq_loop
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      split <;> simp [ParseState.advance] at h_loop ⊢ <;> omega

/-! #### Implicit block sequence position monotonicity -/

theorem parseImplicitBlockSequenceLoop_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (items : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseImplicitBlockSequenceLoop ps fuel items = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseImplicitBlockSequenceLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    next => -- peek? = some .blockEntry
      split at h_ok
      -- All arms handled uniformly
      all_goals {
        first
        | { -- OR-pattern arms: direct recurse with ps.advance
            have h_rec := ih_fuel h_ih_k ps.advance _ h_ok
            simp [ParseState.advance] at h_rec; omega }
        | { -- Default arm: parseNode then recurse
            split at h_ok
            next => simp at h_ok
            next pn_res heq_pn =>
              obtain ⟨val, ps₃⟩ := pn_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMono_apply h_ih heq_pn
              have h_rec := ih_fuel h_ih_k
                { ps₃ with currentPath := _ } _ h_ok
              simp [ParseState.advance] at h_rec h_pn; omega } }
    next => -- peek? ≠ blockEntry
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseImplicitBlockSequence_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_ok : parseImplicitBlockSequence ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseImplicitBlockSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok  -- fuel = 0
  · rename_i k
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok  -- loop error
    · rename_i loop_res heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact parseImplicitBlockSequenceLoop_pos_mono k h_ih_k ps #[] _ heq_loop

/-! #### Block mapping position monotonicity -/

theorem parseBlockMappingEntryValue_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (keyHasContent : Bool) (keyLine keyCol : Nat)
    (result : YamlValue × ParseState)
    (h_ok : parseBlockMappingEntryValue ps fuel keyHasContent keyLine keyCol = .ok result) :
    result.2.pos ≥ ps.pos := by
  have h_tc := tryConsume_pos_mono ps .value
  unfold parseBlockMappingEntryValue at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- consumed = true: for-loop validation + content dispatch
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
      · have h_pn := parseNodePosMono_apply h_ih h_ok; simp only [] at h_pn; omega })
    -- Direct parseNode branch
    all_goals (try { have h_pn := parseNodePosMono_apply h_ih h_ok; simp only [] at h_pn; omega })
  · -- consumed = false → emptyNode
    simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only []; omega

theorem handleBlockMappingKeyEntry_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (pairIdx : Nat)
    (result : YamlValue × YamlValue × ParseState)
    (h_ok : handleBlockMappingKeyEntry ps fuel pairIdx = .ok result) :
    result.2.2.pos ≥ ps.pos := by
  unfold handleBlockMappingKeyEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Peel through all match/if/bind structures
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
  -- After all peeling, h_ok is a final .ok equation
  all_goals (simp only [Except.ok.injEq] at h_ok)
  all_goals (subst h_ok; simp only [])
  -- The result .pos is ps_bev.pos (struct update on currentPath preserves pos)
  -- h_bev hypotheses from split give parseBlockMappingEntryValue ... = .ok _
  -- h_key hypotheses from split give parseNode ... = .ok _ (when key is parsed)
  -- emptyNode key + parseBlockMappingEntryValue
  all_goals (try {
    have h_bev := parseBlockMappingEntryValue_pos_mono fuel h_ih
      _ _ _ _ _ (by assumption)
    simp [ParseState.advance] at h_bev ⊢; omega })
  -- parseNode key + parseBlockMappingEntryValue
  all_goals {
    have h_key := parseNodePosMono_apply h_ih (by assumption)
    have h_bev := parseBlockMappingEntryValue_pos_mono fuel h_ih
      _ _ _ _ _ (by assumption)
    simp [ParseState.advance] at h_key h_bev ⊢; omega }

theorem handleBlockMappingValueEntry_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (pairIdx : Nat)
    (result : YamlValue × ParseState)
    (h_ok : handleBlockMappingValueEntry ps fuel pairIdx = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold handleBlockMappingValueEntry at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Match on peek after advance: 3 OR-pattern arms + default
  split at h_ok
  -- OR-pattern arms (key/blockEnd/none) → emptyNode
  all_goals try {
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    simp [ParseState.advance] }
  -- Default arm → parseNode
  next =>
    split at h_ok
    next => simp at h_ok
    next pn_res heq_pn =>
      obtain ⟨val, ps'⟩ := pn_res; try dsimp only [] at h_ok
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h_pn := parseNodePosMono_apply h_ih heq_pn
      simp [ParseState.advance] at h_pn ⊢; omega

theorem parseBlockMappingLoop_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseBlockMappingLoop ps fuel pairs = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseBlockMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseBlockMappingLoop at h_ok
    simp only [bind, Except.bind] at h_ok
    split at h_ok
    · -- peek = some .key → handleBlockMappingKeyEntry + recurse
      split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨key, val, ps_entry⟩ := entry_res; try dsimp only [] at h_ok
        have h_entry := handleBlockMappingKeyEntry_pos_mono k h_ih_k ps _ _ heq_entry
        have h_rec := ih_fuel h_ih_k ps_entry _ h_ok
        simp only [] at h_entry; omega
    · -- peek = some .value → handleBlockMappingValueEntry + recurse
      split at h_ok
      · simp at h_ok
      · rename_i entry_res heq_entry
        obtain ⟨val, ps_entry⟩ := entry_res; try dsimp only [] at h_ok
        have h_entry := handleBlockMappingValueEntry_pos_mono k h_ih_k ps _ _ heq_entry
        have h_rec := ih_fuel h_ih_k ps_entry _ h_ok
        simp only [] at h_entry; omega
    · -- other → identity
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseBlockMapping_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_ok : parseBlockMapping ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseBlockMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseBlockMappingLoop_pos_mono k h_ih_k ps.advance #[] _ heq_loop
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      split <;> simp [ParseState.advance] at h_loop ⊢ <;> omega

/-! #### Flow mapping helpers (needed before flow sequence loop) -/

theorem parseFlowMappingValue_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (savedPath : YamlPath) (keyContent : String)
    (result : YamlValue × ParseState)
    (h_ok : parseFlowMappingValue ps fuel savedPath keyContent = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseFlowMappingValue at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Name the tryConsume intermediate states before peeling
  generalize h_ps1_def : ({ ps with currentPath := savedPath.push (.key keyContent) } : ParseState) = ps1 at h_ok
  have h_ps1_pos : ps1.pos = ps.pos := by rw [← h_ps1_def]
  generalize h_tc1 : ps1.tryConsume .key = tc1 at h_ok
  have h_tc1_pos := tryConsume_pos_mono ps1 .key
  rw [h_tc1] at h_tc1_pos
  generalize h_tc2 : tc1.2.tryConsume .value = tc2 at h_ok
  have h_tc2_pos := tryConsume_pos_mono tc1.2 .value
  rw [h_tc2] at h_tc2_pos
  -- h_ok now has tc2.1 (consumed) and tc2.2 (state) instead of tryConsume chains
  -- Peel the remaining bind (if/match)
  split at h_ok <;> first | contradiction | skip
  all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
  -- emptyNode branches
  all_goals (try {
    simp only [Except.ok.injEq] at h_ok; subst h_ok; simp only []; omega })
  -- parseNode branches
  all_goals (try {
    have h_pn := parseNodePosMono_apply h_ih h_ok
    simp only [] at h_pn; omega })
  -- Remaining: consumed=false emptyNode branch
  all_goals {
    try dsimp only [] at h_ok
    try simp only [Except.ok.injEq] at h_ok
    try (split at h_ok <;> first | contradiction | skip)
    try dsimp only [] at h_ok
    try simp only [Except.ok.injEq] at h_ok
    subst h_ok; try simp only []
    first | omega | { simp only [ParseState.advance]; omega }
          | { try simp only [] at h_tc1_pos h_tc2_pos h_ps1_pos
              try simp only [ParseState.advance] at h_tc1_pos h_tc2_pos h_ps1_pos
              omega }
          | { have h_pn := parseNodePosMono_apply h_ih (by assumption)
              try simp only [] at h_tc1_pos h_tc2_pos h_ps1_pos h_pn
              omega } }

theorem parseExplicitKey_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState)
    (result : YamlValue × ParseState)
    (h_ok : parseExplicitKey ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseExplicitKey at h_ok
  split at h_ok
  all_goals try {
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _ }
  next => exact parseNodePosMono_apply h_ih h_ok

set_option maxHeartbeats 1600000 in
theorem parseSinglePairMapping_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_ok : parseSinglePairMapping ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseSinglePairMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok  -- fuel = 0
  · rename_i k
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    simp only [emptyNode] at h_ok
    -- Peel through key dispatch layers
    split at h_ok <;> first | contradiction | skip
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- After round 3: test if generalize can find tryConsume
    all_goals try {
      generalize h_tc : ParseState.tryConsume _ YamlToken.value = tc at h_ok
      obtain ⟨tc_consumed, tc_ps⟩ := tc
      have h_tc_pos : tc_ps.pos ≥ ps.pos := by
        show (tc_consumed, tc_ps).snd.pos ≥ ps.pos
        rw [← h_tc]
        apply Nat.le_trans _ (tryConsume_pos_mono _ .value)
        try simp only []
        first
          | { simp only [ParseState.advance]; omega }
          | omega
          | { have := parseNodePosMono_apply h_ih_k (by assumption)
              simp only [ParseState.advance] at this; omega }
          | { try simp only [ParseState.advance]
              try { have := parseNodePosMono_apply h_ih_k (by assumption)
                    try simp only [ParseState.advance] at this }
              omega }
    }
    all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
    -- After round 4: parseNode key paths have keyContent resolved, exposing one tryConsume.
    all_goals try {
      generalize h_tc : ParseState.tryConsume _ YamlToken.value = tc at h_ok
      have h_tc_pos : tc.snd.pos ≥ ps.pos := by
        rw [← h_tc]
        apply Nat.le_trans _ (tryConsume_pos_mono _ .value)
        try simp only []
        first
          | { simp only [ParseState.advance]; omega }
          | omega
          | { have := parseNodePosMono_apply h_ih_k (by assumption)
              simp only [ParseState.advance] at this; omega }
    }
    -- Name the tryConsume result before further peeling (skipped for over-peeled goals)
    all_goals {
      -- Close or peel value dispatch
      -- Reduce product destructure so split can see the if/match
      try dsimp only [] at h_ok
      first
      | { -- Already resolved: close directly
          simp only [Except.ok.injEq] at h_ok; rw [← h_ok]; simp only []
          first
            | omega
            | { have := parseNodePosMono_apply h_ih_k (by assumption)
                simp only [ParseState.advance] at *; omega }
            | { -- tryConsume opaque in goal: unfold it
                simp only [ParseState.tryConsume, ParseState.advance]
                split <;> (try split)
                all_goals { simp only []; first | omega | { have := parseNodePosMono_apply h_ih_k (by assumption); simp only [ParseState.advance] at this; omega } } }
            | { -- Chain: result ≥ parseNode_input ≥ tryConsume_input ≥ ps
                have h1 := parseNodePosMono_apply h_ih_k (by assumption)
                apply Nat.le_trans _ h1
                apply Nat.le_trans _ (tryConsume_pos_mono _ .value)
                try simp only []
                simp only [ParseState.advance]; omega } }
      | { -- Needs more peeling for value dispatch
          split at h_ok <;> first | contradiction | skip
          all_goals try dsimp only [] at h_ok
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          all_goals (first | (split at h_ok <;> first | contradiction | skip) | skip)
          -- Close all goals
          all_goals {
            try simp only [] at h_tc_pos  -- reduce tc.snd to destructured variable
            simp only [Except.ok.injEq] at h_ok; rw [← h_ok]; simp only []
            first
              | omega
              | { exact h_tc_pos }
              | { have := parseNodePosMono_apply h_ih_k (by assumption)
                  try simp only [ParseState.advance] at this
                  try simp only [] at h_tc_pos
                  omega }
              | { -- Normalize all pair projections, gather bounds
                  -- Multi-hop: result ≥ parseNode2_input ≥ tryConsume_input ≥ parseNode1_input ≥ ps
                  apply Nat.le_trans _ (parseNodePosMono_apply h_ih_k (by assumption))
                  apply Nat.le_trans _ (tryConsume_pos_mono _ .value)
                  simp only []
                  apply Nat.le_trans _ (parseNodePosMono_apply h_ih_k (by assumption))
                  simp only [ParseState.advance]; omega }
              | { simp only [ParseState.tryConsume, ParseState.advance]
                  split <;> (try split)
                  all_goals (try simp only [])
                  all_goals {
                    first
                      | omega
                      | { have := parseNodePosMono_apply h_ih_k (by assumption)
                          try simp only [ParseState.advance] at this
                          omega } } }
              | { have h1 := parseNodePosMono_apply h_ih_k (by assumption)
                  apply Nat.le_trans _ h1
                  apply Nat.le_trans _ (tryConsume_pos_mono _ .value)
                  try simp only []
                  try simp only [ParseState.advance]
                  omega }
              | { apply Nat.le_trans _ (tryConsume_pos_mono _ .value)
                  try simp only []
                  have h1 := parseNodePosMono_apply h_ih_k (by assumption)
                  try simp only [ParseState.advance] at h1
                  omega } } } }
/-! #### Flow sequence position monotonicity -/

theorem parseFlowSequenceLoop_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (items : Array YamlValue)
    (result : Array YamlValue × ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel items = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps items with
  | zero =>
    unfold parseFlowSequenceLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseFlowSequenceLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · -- flowSequenceEnd → identity
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
    · -- other tokens
      split at h_ok
      · -- items.size > 0: match peek for flowEntry separator
        split at h_ok
        · -- flowEntry → advance, then dispatch
          split at h_ok
          · -- key → parseSinglePairMapping + recurse
            split at h_ok
            · simp at h_ok
            · rename_i spm_res heq_spm
              obtain ⟨mapVal, ps_spm⟩ := spm_res; try dsimp only [] at h_ok
              have h_spm := parseSinglePairMapping_pos_mono k h_ih_k _ _ heq_spm
              have h_rec := ih_fuel h_ih_k
                { ps_spm with currentPath := _ } _ h_ok
              simp [ParseState.advance] at h_rec h_spm; omega
          · -- flowSequenceEnd → identity
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            simp [ParseState.advance]
          · -- other → parseNode + recurse
            split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMono_apply h_ih heq_pn
              have h_rec := ih_fuel h_ih_k
                { ps_pn with currentPath := _ } _ h_ok
              simp [ParseState.advance] at h_rec h_pn; omega
        · -- no separator → return
          simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
      · -- items.size = 0: dispatch directly
        split at h_ok
        · -- key → parseSinglePairMapping + recurse
          split at h_ok
          · simp at h_ok
          · rename_i spm_res heq_spm
            obtain ⟨mapVal, ps_spm⟩ := spm_res; try dsimp only [] at h_ok
            have h_spm := parseSinglePairMapping_pos_mono k h_ih_k _ _ heq_spm
            have h_rec := ih_fuel h_ih_k
              { ps_spm with currentPath := _ } _ h_ok
            simp at h_rec h_spm ⊢; omega
        · -- flowSequenceEnd → identity
          simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
        · -- other → parseNode + recurse
          split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
            have h_pn := parseNodePosMono_apply h_ih heq_pn
            have h_rec := ih_fuel h_ih_k
              { ps_pn with currentPath := _ } _ h_ok
            simp at h_rec h_pn ⊢; omega

theorem parseFlowSequence_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_ok : parseFlowSequence ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseFlowSequence at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨items_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseFlowSequenceLoop_pos_mono k h_ih_k ps.advance #[] _ heq_loop
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        simp [ParseState.advance] at h_loop ⊢; omega
      · simp at h_ok

/-! #### Flow mapping position monotonicity -/

theorem parseFlowMappingLoop_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (pairs : Array (YamlValue × YamlValue))
    (result : Array (YamlValue × YamlValue) × ParseState)
    (h_ok : parseFlowMappingLoop ps fuel pairs = .ok result) :
    result.2.pos ≥ ps.pos := by
  induction fuel generalizing ps pairs with
  | zero =>
    unfold parseFlowMappingLoop at h_ok
    simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
  | succ k ih_fuel =>
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    unfold parseFlowMappingLoop at h_ok
    simp only [bind, Except.bind, pure, Except.pure] at h_ok
    split at h_ok
    · -- flowMappingEnd → identity
      simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
    · -- other
      split at h_ok
      · -- pairs.size > 0: match peek for flowEntry
        split at h_ok
        · -- flowEntry → advance, then dispatch
          split at h_ok
          · -- flowMappingEnd → identity
            simp only [Except.ok.injEq] at h_ok; subst h_ok
            simp [ParseState.advance]
          · -- key → advance + parseExplicitKey + parseFlowMappingValue + recurse
            split at h_ok
            · simp at h_ok
            · rename_i ek_res heq_ek
              obtain ⟨key_val, ps_ek⟩ := ek_res; try dsimp only [] at h_ok
              split at h_ok
              · simp at h_ok
              · rename_i fmv_res heq_fmv
                obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
                have h_ek := parseExplicitKey_pos_mono k h_ih_k _ _ heq_ek
                have h_fmv := parseFlowMappingValue_pos_mono k h_ih_k _ _ _ _ heq_fmv
                have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
                simp [ParseState.advance] at h_ek h_fmv ⊢; omega
          · -- other → parseNode + parseFlowMappingValue + recurse
            split at h_ok
            · simp at h_ok
            · rename_i pn_res heq_pn
              obtain ⟨key_val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
              split at h_ok
              · simp at h_ok
              · rename_i fmv_res heq_fmv
                obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
                have h_pn := parseNodePosMono_apply h_ih heq_pn
                have h_fmv := parseFlowMappingValue_pos_mono k h_ih_k _ _ _ _ heq_fmv
                have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
                simp [ParseState.advance] at h_pn h_fmv ⊢; omega
        · -- no separator → return
          simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
      · -- pairs.size = 0: dispatch directly
        split at h_ok
        · -- flowMappingEnd → identity
          simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _
        · -- key → advance + parseExplicitKey + parseFlowMappingValue + recurse
          split at h_ok
          · simp at h_ok
          · rename_i ek_res heq_ek
            obtain ⟨key_val, ps_ek⟩ := ek_res; try dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i fmv_res heq_fmv
              obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
              have h_ek := parseExplicitKey_pos_mono k h_ih_k _ _ heq_ek
              have h_fmv := parseFlowMappingValue_pos_mono k h_ih_k _ _ _ _ heq_fmv
              have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
              simp [ParseState.advance] at h_ek h_fmv ⊢; omega
        · -- other → parseNode + parseFlowMappingValue + recurse
          split at h_ok
          · simp at h_ok
          · rename_i pn_res heq_pn
            obtain ⟨key_val, ps_pn⟩ := pn_res; try dsimp only [] at h_ok
            split at h_ok
            · simp at h_ok
            · rename_i fmv_res heq_fmv
              obtain ⟨fmv_val, ps_fmv⟩ := fmv_res; try dsimp only [] at h_ok
              have h_pn := parseNodePosMono_apply h_ih heq_pn
              have h_fmv := parseFlowMappingValue_pos_mono k h_ih_k _ _ _ _ heq_fmv
              have h_rec := ih_fuel h_ih_k ps_fmv _ h_ok
              simp at h_pn h_fmv ⊢; omega

theorem parseFlowMapping_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (result : YamlValue × ParseState)
    (h_ok : parseFlowMapping ps fuel = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseFlowMapping at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i k
    have h_ih_k : ParseNodePosMono k := fun ps' m v ps'' h_le h_pn =>
      h_ih ps' m v ps'' (by omega) h_pn
    split at h_ok
    · simp at h_ok
    · rename_i loop_res heq_loop
      obtain ⟨pairs_arr, ps_loop⟩ := loop_res; try dsimp only [] at h_ok
      have h_loop := parseFlowMappingLoop_pos_mono k h_ih_k ps.advance #[] _ heq_loop
      split at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        simp [ParseState.advance] at h_loop ⊢; omega
      · simp at h_ok

/-! #### Content dispatch and main induction -/

theorem parseNodeContent_pos_mono (fuel : Nat)
    (h_ih : ParseNodePosMono fuel)
    (ps : ParseState) (props : NodeProperties)
    (result : YamlValue × ParseState)
    (h_ok : parseNodeContent ps fuel props = .ok result) :
    result.2.pos ≥ ps.pos := by
  unfold parseNodeContent at h_ok
  split at h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; simp [ParseState.advance]
  · exact parseBlockSequence_pos_mono fuel h_ih ps result h_ok
  · exact parseBlockMapping_pos_mono fuel h_ih ps result h_ok
  · exact parseImplicitBlockSequence_pos_mono fuel h_ih ps result h_ok
  · exact parseFlowSequence_pos_mono fuel h_ih ps result h_ok
  · exact parseFlowMapping_pos_mono fuel h_ih ps result h_ok
  · simp only [Except.ok.injEq] at h_ok; subst h_ok; exact Nat.le_refl _

theorem parseNode_pos_mono_all : ∀ n, ParseNodePosMono n := by
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
      -- alias check
      split at h_ok
      · -- alias: advance (or throw)
        split at h_ok
        · simp at h_ok
        · simp only [Except.ok.injEq] at h_ok
          obtain ⟨_, rfl⟩ := Prod.mk.inj h_ok
          split <;> simp_all [ParseState.advance] <;> omega
      · -- not alias
        split at h_ok
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
              have h_props := parseNodeProperties_pos_mono ps props ps_props heq_props
              have h_content := parseNodeContent_pos_mono k ih ps_props props _ heq_content
              -- Extract ps' = (applyNodeFinalization ...).2 without expanding
              have h_ps := congrArg Prod.snd h_ok
              simp only [] at h_ps  -- reduces (val', ps').2 to ps'
              rw [show ps'.pos = ps_content.pos from by rw [← h_ps]; exact applyNodeFinalization_pos ..]
              simp only [] at h_content h_props  -- reduce (x, y).snd to y
              omega
    · exact ih ps m val ps' (by omega) h_ok

/-! #### Emitter-specific strict position advancement -/

theorem parseNode_emitter_advances (ps : ParseState) (fuel : Nat)
    (val : YamlValue) (ps' : ParseState)
    (h_ok : parseNode ps (fuel + 1) = .ok (val, ps'))
    (h_emit_tok : (∃ s, ps.peek? = some (.scalar s .doubleQuoted)) ∨
                  ps.peek? = some .flowSequenceStart ∨
                  ps.peek? = some .flowMappingStart) :
    ps'.pos > ps.pos := by
  unfold parseNode at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- alias branch: contradicts h_emit_tok
  split at h_ok
  · rename_i h_peek_alias
    rcases h_emit_tok with ⟨s, h_s⟩ | h_fs | h_fm
    · simp [h_peek_alias] at h_s
    · simp [h_peek_alias] at h_fs
    · simp [h_peek_alias] at h_fm
  · -- non-alias
    split at h_ok
    · simp at h_ok
    · rename_i props_res heq_props
      obtain ⟨props, ps_props⟩ := props_res
      try dsimp only [] at h_ok
      have h_props_pos := parseNodeProperties_pos_mono ps props ps_props heq_props
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
          rw [show ps'.pos = ps_content.pos from by rw [← h_ps]; exact applyNodeFinalization_pos ..]
          -- Now show ps_content.pos > ps.pos via content dispatch
          unfold parseNodeContent at heq_content
          split at heq_content
          · -- scalar → advance
            simp only [Except.ok.injEq] at heq_content
            obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
            simp [ParseState.advance]; omega
          · -- blockSequenceStart
            unfold parseBlockSequence at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨items, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseBlockSequenceLoop_pos_mono _ (parseNode_pos_mono_all _) ps_props.advance #[] _ heq_loop
                simp only [Except.ok.injEq] at heq_content
                obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                split <;> simp [ParseState.advance] at h_loop ⊢ <;> omega
          · -- blockMappingStart
            unfold parseBlockMapping at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨pairs, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseBlockMappingLoop_pos_mono _ (parseNode_pos_mono_all _) ps_props.advance #[] _ heq_loop
                simp only [Except.ok.injEq] at heq_content
                obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                split <;> simp [ParseState.advance] at h_loop ⊢ <;> omega
          · -- blockEntry (implicit block sequence): contradicts emitter tok
            rcases Nat.lt_or_ge ps.pos ps_props.pos with h_strict | h_le
            · have h_ibs := parseImplicitBlockSequence_pos_mono fuel (parseNode_pos_mono_all fuel) ps_props _ heq_content
              simp only [] at h_ibs; omega
            · have h_eq_pos : ps_props.pos = ps.pos := by omega
              have h_tok := parseNodeProperties_tokens ps props ps_props heq_props
              have h_peek_eq : ps_props.peek? = ps.peek? := by
                simp only [ParseState.peek?]; rw [h_tok, h_eq_pos]
              rename_i h_peek_be _
              rcases h_emit_tok with ⟨s, h_s⟩ | h_fs | h_fm
              · rw [← h_peek_eq] at h_s; simp_all
              · rw [← h_peek_eq] at h_fs; simp_all
              · rw [← h_peek_eq] at h_fm; simp_all
          · -- flowSequenceStart
            unfold parseFlowSequence at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨items, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseFlowSequenceLoop_pos_mono _ (parseNode_pos_mono_all _) ps_props.advance #[] _ heq_loop
                split at heq_content
                · simp only [Except.ok.injEq] at heq_content
                  obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                  simp [ParseState.advance] at h_loop ⊢; omega
                · simp at heq_content
          · -- flowMappingStart
            unfold parseFlowMapping at heq_content
            simp only [bind, Except.bind] at heq_content
            split at heq_content
            · simp at heq_content
            · split at heq_content
              · simp at heq_content
              · rename_i loop_res heq_loop
                obtain ⟨pairs, ps_loop⟩ := loop_res; try dsimp only [] at heq_content
                have h_loop := parseFlowMappingLoop_pos_mono _ (parseNode_pos_mono_all _) ps_props.advance #[] _ heq_loop
                split at heq_content
                · simp only [Except.ok.injEq] at heq_content
                  obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
                  simp [ParseState.advance] at h_loop ⊢; omega
                · simp at heq_content
          · -- empty node: contradicts emitter tok
            simp only [Except.ok.injEq] at heq_content
            obtain ⟨_, rfl⟩ := Prod.mk.inj heq_content
            suffices h_gt : ps_props.pos > ps.pos by omega
            rcases Nat.lt_or_ge ps.pos ps_props.pos with h_lt | h_le
            · exact h_lt
            · exfalso
              have h_eq_pos : ps_props.pos = ps.pos := by omega
              have h_tok := parseNodeProperties_tokens ps props ps_props heq_props
              have h_peek_eq : ps_props.peek? = ps.peek? := by
                simp only [ParseState.peek?]; rw [h_tok, h_eq_pos]
              rename_i h_not_scalar h_not_bss h_not_bms h_not_be h_not_fss h_not_fms
              rcases h_emit_tok with ⟨s, h_s⟩ | h_fs | h_fm
              all_goals { rw [← h_peek_eq] at *; simp_all }

/-! #### Flow sequence/mapping loop success on emitter-like token streams

Sub-phase 4.4.C: These theorems show that `parseFlowSequenceLoop` and
`parseFlowMappingLoop` succeed (return `.ok`) and reach the terminating bracket
(`flowSequenceEnd` / `flowMappingEnd`) when called on emitter-produced token
streams. The key assumptions:

1. `ParseNodeFlowSeqOk` / `ParseNodeFlowMapOk`: each `parseNode` call within
   the loop succeeds, advances position, stays within bounds, preserves the
   token array, and leaves peek at a separator or end bracket.

2. No `.key` tokens appear (emitter never produces implicit key markers in
   flow sequences).

3. Separators (`flowEntry`) appear between items — ensured by the scanner
   processing emitter output `emit.emitList` / `emit.emitPairList`.

These are used by sub-phase 4.4.D to close the Layer 2 parser acceptance
sorrys in `EmitterScannability.lean`. -/

-- parseNode succeeds on content-start tokens at bracket depth 0 within
-- a flow sequence body [body_start, endPos):
-- returns ok, advances position, stays ≤ endPos, preserves tokens,
-- and the result peeks at flowEntry or flowSequenceEnd.
-- Content-start tokens are: scalar, flowSequenceStart, flowMappingStart.
-- The bracket depth 0 restriction (flowBracketBalance = 0) ensures we only
-- claim success at positions the loop actually visits. Positions at depth > 0
-- are consumed by recursive parseNode calls within bracket groups.
def ParseNodeFlowSeqOk (tokens : Array (Positioned YamlToken))
    (endPos : Nat) (fuel : Nat) (body_start : Nat) : Prop :=
  ∀ (ps : ParseState) (m : Nat),
    ps.tokens = tokens → 0 < m → m ≤ fuel →
    ps.pos < endPos →
    body_start ≤ ps.pos →
    flowBracketBalance tokens body_start ps.pos = 0 →
    ((∃ c s, ps.peek? = some (.scalar c s)) ∨
     ps.peek? = some .flowSequenceStart ∨
     ps.peek? = some .flowMappingStart) →
    ∃ val ps', parseNode ps m = .ok (val, ps') ∧
              ps'.pos > ps.pos ∧ ps'.pos ≤ endPos ∧
              ps'.tokens = tokens ∧
              ps'.trackPositions = ps.trackPositions ∧
              (ps'.peek? = some .flowEntry ∨
               (ps'.peek? = some .flowSequenceEnd ∧ ps'.pos = endPos)) ∧
              flowBracketBalance tokens ps.pos ps'.pos = 0

-- Fuel monotonicity: ParseNodeFlowSeqOk at fuel implies it at fuel' ≤ fuel
-- (the fuel parameter only restricts m ≤ fuel, so larger fuel is weaker).
theorem ParseNodeFlowSeqOk.mono {tokens endPos fuel fuel' body_start}
    (h : ParseNodeFlowSeqOk tokens endPos fuel body_start)
    (h_le : fuel' ≤ fuel) : ParseNodeFlowSeqOk tokens endPos fuel' body_start :=
  fun ps m h_tok h_pos_m h_m h_pos h_bs h_depth h_cs =>
    let ⟨v, ps', hok, hadv, hbound, htok, htp, hpeek, hbal⟩ :=
      h ps m h_tok h_pos_m (Nat.le_trans h_m h_le) h_pos h_bs h_depth h_cs
    ⟨v, ps', hok, hadv, hbound, htok, htp, hpeek, hbal⟩

-- Helper: if ps.peek? = some tok and ps.pos < ps.tokens.size,
-- then (ps.tokens[ps.pos]).val = tok
theorem peek_some_val {ps : ParseState} {tok : YamlToken}
    (h_peek : ps.peek? = some tok) :
    ps.pos < ps.tokens.size ∧ ps.tokens[ps.pos]!.val = tok := by
  unfold ParseState.peek? at h_peek
  split at h_peek
  · rename_i h_lt
    exact ⟨h_lt, by simp at h_peek; exact h_peek⟩
  · simp at h_peek

-- Helper: if ps.pos = k and k < ps.tokens.size and (ps.tokens[k]).val = tok,
-- then ps.peek? = some tok
theorem peek_of_pos_val {ps : ParseState} {k : Nat} {tok : YamlToken}
    (h_pos : ps.pos = k) (h_bound : k < ps.tokens.size)
    (h_val : ps.tokens[k]!.val = tok) :
    ps.peek? = some tok := by
  simp only [ParseState.peek?, h_pos, h_bound, ↓reduceIte, h_val]

set_option maxHeartbeats 1600000 in
theorem parseFlowSequenceLoop_emitter_ok (fuel : Nat)
    (ps : ParseState) (items_acc : Array YamlValue) (endPos : Nat)
    (body_start : Nat)
    (h_pn : ParseNodeFlowSeqOk ps.tokens endPos fuel body_start)
    (h_fuel : fuel > endPos - ps.pos)
    (h_pos : ps.pos ≤ endPos)
    (h_end_pos : endPos < ps.tokens.size)
    (h_end_tok : ps.tokens[endPos]!.val = .flowSequenceEnd)
    (h_at_end : ps.peek? = some .flowSequenceEnd → ps.pos = endPos)
    (h_entry : items_acc.size > 0 →
               ps.peek? = some .flowEntry ∨ ps.peek? = some .flowSequenceEnd)
    (h_content_start : ps.pos < endPos → items_acc.size = 0 →
        (∃ c s, ps.peek? = some (.scalar c s)) ∨
        ps.peek? = some .flowSequenceStart ∨
        ps.peek? = some .flowMappingStart)
    (h_after_fe : ∀ k : Nat, ps.pos ≤ k → k < endPos →
                  ps.tokens[k]!.val = .flowEntry →
                  flowBracketBalance ps.tokens body_start k = 0 →
                  k + 1 ≤ endPos ∧
                  ((∃ c s, ps.tokens[k + 1]!.val = .scalar c s) ∨
                   ps.tokens[k + 1]!.val = .flowSequenceStart ∨
                   ps.tokens[k + 1]!.val = .flowMappingStart))
    (h_bal : flowBracketBalance ps.tokens body_start ps.pos = 0)
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
    exact peek_of_pos_val h_eq (by omega) h_end_tok
  | succ n ih =>
    unfold parseFlowSequenceLoop
    simp only [bind, Except.bind, pure, Except.pure]
    -- 1. Outer match on ps.peek?: flowSequenceEnd vs wildcard
    split
    · -- flowSequenceEnd → immediate return
      exact ⟨items_acc, ps, rfl, ‹_›, h_at_end ‹_›, rfl, rfl⟩
    · -- wildcard → continue
      rename_i h_outer_not_end
      have h_lt : ps.pos < endPos := by
        rcases Nat.eq_or_lt_of_le h_pos with h_eq | h_lt
        · exfalso; exact h_outer_not_end (peek_of_pos_val h_eq (by omega) h_end_tok)
        · exact h_lt
      -- 2. if items_acc.size > 0
      split
      · -- items_acc.size > 0 → separator check
        -- 3. Separator match: flowEntry vs wildcard
        split
        · -- flowEntry → advance, dispatch on advance.peek?
          -- 4. Inner dispatch: key / flowSequenceEnd / wildcard
          split
          · -- key after separator → contradiction with h_after_fe (content start)
            rename_i h_adv_key
            exfalso
            have ⟨_, h_val⟩ := peek_some_val h_adv_key
            simp [ParseState.advance] at h_val
            have h_fe_val : ps.tokens[ps.pos]!.val = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) (by omega) h_fe_val h_bal
            rcases h_afe.2 with ⟨c, s, hcs⟩ | hcs | hcs <;> rw [h_val] at hcs <;> cases hcs
          · -- flowSequenceEnd after separator → contradiction (h_after_fe content start)
            rename_i h_adv_end
            exfalso
            have h_fe_val : ps.tokens[ps.pos]!.val = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) (by omega) h_fe_val h_bal
            have ⟨_, h_val⟩ := peek_some_val h_adv_end
            simp [ParseState.advance] at h_val
            rcases h_afe.2 with ⟨c, s, hcs⟩ | hcs | hcs <;> rw [h_val] at hcs <;> cases hcs
          · -- other → parseNode + recurse
            rename_i h_adv_not_key h_adv_not_end
            -- The separator split gave us: ps.peek? = some .flowEntry
            have h_fe_val : ps.tokens[ps.pos]!.val = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) (by omega) h_fe_val h_bal
            have h_adv_pos_lt : ps.pos + 1 < endPos := by
              rcases Nat.eq_or_lt_of_le h_afe.1 with heq | hlt
              · exfalso; apply h_adv_not_end
                show ps.advance.peek? = some .flowSequenceEnd
                simp only [ParseState.peek?, ParseState.advance, heq, h_end_pos, ↓reduceIte, h_end_tok]
              · exact hlt
            -- Generalize parseNode struct in goal
            generalize hPsX : ({ ps.advance with
              currentPath := Array.push ps.advance.currentPath
                (PathSegment.index items_acc.size) } : ParseState) = psX
            -- Derive helper equalities about psX (using rw to avoid let __src issues)
            have h_psX_tok : psX.tokens = ps.tokens := by
              rw [← hPsX]; simp [ParseState.advance]
            have h_psX_pos : psX.pos = ps.pos + 1 := by
              rw [← hPsX]; simp [ParseState.advance]
            have h_psX_peek : psX.peek? = ps.advance.peek? := by
              rw [← hPsX]; simp [ParseState.advance, ParseState.peek?]
            have h_psX_tp : psX.trackPositions = ps.trackPositions := by
              rw [← hPsX]; simp [ParseState.advance]
            -- Lift h_after_fe content classification to peek? level for h_pn
            have h_cs : (∃ c s, psX.peek? = some (.scalar c s)) ∨
                psX.peek? = some .flowSequenceStart ∨
                psX.peek? = some .flowMappingStart := by
              rw [h_psX_peek]
              have h_bound : ps.pos + 1 < ps.tokens.size := by omega
              have h_adv_peek : ps.advance.peek? = some ps.tokens[ps.pos + 1]!.val := by
                simp only [ParseState.advance, ParseState.peek?, h_bound, ↓reduceIte]
              rcases h_afe.2 with ⟨c, s, hcs⟩ | hcs | hcs
              · exact .inl ⟨c, s, by rw [h_adv_peek, hcs]⟩
              · exact .inr (.inl (by rw [h_adv_peek, hcs]))
              · exact .inr (.inr (by rw [h_adv_peek, hcs]))
            -- Bracket depth proof for h_pn call
            have h_depth_at_adv : flowBracketBalance ps.tokens body_start (ps.pos + 1) = 0 := by
              have h_pos_bound : ps.pos < ps.tokens.toList.length := by
                show ps.pos < ps.tokens.size; omega
              rw [flowBracketBalance_compose ps.tokens body_start ps.pos (ps.pos + 1) h_bs (by omega),
                  h_bal, flowBracketBalance_single _ _ h_pos_bound]
              have h_eq : (ps.tokens.toList[ps.pos]'h_pos_bound).val = YamlToken.flowEntry := by
                show (ps.tokens[ps.pos]'(by omega)).val = YamlToken.flowEntry
                rw [← getElem!_pos ps.tokens ps.pos (by omega)]; exact h_fe_val
              rw [h_eq]; decide
            -- Get parseNode success from h_pn
            obtain ⟨val, ps_after, h_ok, h_pos_adv, h_pos_bound, h_tok_eq, h_tp_eq, h_peek_after, h_pn_bal⟩ :=
              h_pn psX n h_psX_tok (by omega) (by omega)
                (by rw [h_psX_pos]; exact h_adv_pos_lt)
                (by rw [h_psX_pos]; omega)
                (by rw [h_psX_pos]; exact h_depth_at_adv)
                h_cs
            -- Rewrite parseNode result in goal
            rw [h_ok]; dsimp only []
            -- Apply IH
            have h_rec_tok : ({ ps_after with
              currentPath := ps.advance.currentPath } : ParseState).tokens =
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
                (by -- h_bal: fbb(body_start, ps_after.pos) = 0
                    rw [h_rec_tok]
                    have h_pn_bal' : flowBracketBalance ps.tokens psX.pos ps_after.pos = 0 :=
                      h_psX_tok ▸ h_pn_bal
                    rw [h_psX_pos] at h_pn_bal'
                    have h_tl : ps.tokens.toList.length = ps.tokens.size := rfl
                    exact flowBracketBalance_compose_zero ps.tokens body_start ps.pos ps_after.pos
                      h_bs (by omega) (by omega) h_bal
                      (by show flowBracketDelta (ps.tokens[ps.pos]'(by omega)).val = 0
                          rw [(getElem!_pos ps.tokens ps.pos (by omega)).symm, h_fe_val]; decide)
                      h_pn_bal')
                (by have : ps.tokens.toList.length = ps.tokens.size := rfl; dsimp only []; omega)
            exact ⟨items_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_tok_eq, h_tp_res.trans (h_tp_eq.trans h_psX_tp)⟩
        · -- no separator → early return .ok (items_acc, ps)
          -- h_entry: peek = flowEntry ∨ flowSeqEnd. Separator split says peek ≠ flowEntry.
          -- So peek = flowSeqEnd, and the early return is fine.
          have h_acc_pos : items_acc.size > 0 := by assumption
          have h_not_fe : ps.peek? ≠ some .flowEntry := by assumption
          have h_sep := h_entry h_acc_pos
          rcases h_sep with h_fe | h_end
          · exfalso; exact h_not_fe h_fe
          · exact ⟨items_acc, ps, rfl, h_end, h_at_end h_end, rfl, rfl⟩
      · -- items_acc.size = 0 → dispatch directly (no separator check)
        -- 6. Inner dispatch: key / flowSequenceEnd / wildcard
        split
        · -- key at start → contradiction with h_content_start
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
          -- Generalize the parseNode struct to match goal and h_ok
          generalize hPsX : ({ ps with
            currentPath := ps.currentPath.push (.index items_acc.size) } : ParseState) = psX
          obtain ⟨val, ps_after, h_ok, h_pos_adv, h_pos_bound, h_tok_eq, h_tp_eq, h_peek_after, h_pn_bal⟩ :=
            h_pn psX n
              (by subst hPsX; rfl)
              (by omega) (by omega)
              (by subst hPsX; exact h_lt)
              (by subst hPsX; exact h_bs)
              (by subst hPsX; exact h_bal)
              (by subst hPsX; exact h_cs)
          -- Rewrite parseNode result in goal and reduce the match
          rw [h_ok]; dsimp only []
          -- Derive psX.pos and psX.trackPositions for omega and trans
          have h_psX_pos : psX.pos = ps.pos := by subst hPsX; rfl
          have h_psX_tp : psX.trackPositions = ps.trackPositions := by subst hPsX; rfl
          -- Apply IH via obtain to handle tokens mismatch
          have h_rec_tok : ({ ps_after with currentPath := ps.currentPath } : ParseState).tokens = ps.tokens := h_tok_eq
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
              (by -- h_bal: fbb(body_start, ps_after.pos) = 0
                  rw [h_rec_tok]
                  have h_pn_bal' : flowBracketBalance ps.tokens ps.pos ps_after.pos = 0 := by
                    rw [show ps.pos = psX.pos from h_psX_pos.symm]; exact h_pn_bal
                  rw [flowBracketBalance_compose ps.tokens body_start ps.pos ps_after.pos h_bs (by omega),
                      h_bal, h_pn_bal']; simp)
              (by dsimp only []; omega)
          exact ⟨items_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_tok_eq, h_tp_res.trans (h_tp_eq.trans h_psX_tp)⟩

/-! #### Flow mapping loop fuel sufficiency

For emitter-produced flow mappings, each entry has the token pattern:
  `key, <key_tokens...>, value, <value_tokens...>`
terminated by `flowEntry` (separator) or `flowMappingEnd` (end bracket).

The `some .key` branch of `parseFlowMappingLoop` consumes:
1. The key token (`ps.advance`)
2. Key content via `parseExplicitKey` (calls `parseNode` for non-empty keys)
3. Value content via `parseFlowMappingValue` (consumes `value` token, calls `parseNode`)
4. Recurses with `pairs.push (key, val)`

Because each entry consumes ≥2 tokens (key + at least one value/content token),
the loop terminates within `tokens.size / 2` iterations.

The predicate `ParseEntryFlowMapOk` captures per-entry success: given that ps.peek?
is `some .key` and ps.pos < endPos, the full chain parseExplicitKey + parseFlowMappingValue
succeeds on ps.advance, advances position strictly, stays ≤ endPos, preserves tokens,
and the result peeks at `flowEntry` or `flowMappingEnd`. -/

-- Per-entry predicate for flow mapping loop: the full key+value chain succeeds.
-- parseExplicitKey doesn't depend on savedPath/keyContent; the ∀ quantifier on those
-- lets us instantiate parseFlowMappingValue with the exact keyContent the loop uses.
-- The bracket depth 0 restriction (flowBracketBalance = 0) ensures we only claim
-- success at positions the loop actually visits.
def ParseEntryFlowMapOk (tokens : Array (Positioned YamlToken))
    (endPos : Nat) (fuel : Nat) (body_start : Nat) : Prop :=
  ∀ (ps : ParseState) (m : Nat),
    ps.tokens = tokens → 0 < m → m ≤ fuel →
    ps.pos < endPos →
    body_start ≤ ps.pos →
    flowBracketBalance tokens body_start ps.pos = 0 →
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
          flowBracketBalance tokens ps.pos val_ps.pos = 0

theorem ParseEntryFlowMapOk.mono {tokens endPos fuel fuel' body_start}
    (h : ParseEntryFlowMapOk tokens endPos fuel body_start)
    (h_le : fuel' ≤ fuel) : ParseEntryFlowMapOk tokens endPos fuel' body_start :=
  fun ps m h_tok h_pos_m h_m h_pos h_bs h_depth h_key =>
    let ⟨kv, kps, hek, hadv, hbound, htok, htp, hfmv⟩ :=
      h ps m h_tok h_pos_m (Nat.le_trans h_m h_le) h_pos h_bs h_depth h_key
    ⟨kv, kps, hek, hadv, hbound, htok, htp, hfmv⟩

/-- **Fuel monotonicity for parseFlowSequenceLoop**: If the loop succeeds with fuel N
    producing result (items, ps'), then it also succeeds with any fuel N+1 producing
    the same result. The loop is deterministic: once enough fuel exists to reach
    the termination condition, extra fuel doesn't change the outcome. -/
theorem parseFlowSequenceLoop_fuel_mono_succ
    (ps : ParseState) (items_acc : Array YamlValue) (fuel : Nat)
    (items : Array YamlValue) (ps' : ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel items_acc = .ok (items, ps')) :
    parseFlowSequenceLoop ps (fuel + 1) items_acc = .ok (items, ps') := by
  sorry

/-- **Fuel monotonicity (general)**: Extends fuel_mono_succ to arbitrary fuel' ≥ fuel.
    Uses repeated application of the successor case. -/
theorem parseFlowSequenceLoop_fuel_mono
    (ps : ParseState) (items_acc : Array YamlValue)
    (fuel fuel' : Nat)
    (h_le : fuel ≤ fuel')
    (items : Array YamlValue) (ps' : ParseState)
    (h_ok : parseFlowSequenceLoop ps fuel items_acc = .ok (items, ps')) :
    parseFlowSequenceLoop ps fuel' items_acc = .ok (items, ps') := by
  sorry

set_option maxHeartbeats 3200000 in
theorem parseFlowMappingLoop_emitter_ok (fuel : Nat)
    (ps : ParseState) (pairs_acc : Array (YamlValue × YamlValue)) (endPos : Nat)
    (body_start : Nat)
    (h_entry : ParseEntryFlowMapOk ps.tokens endPos fuel body_start)
    (h_fuel : fuel > endPos - ps.pos)
    (h_pos : ps.pos ≤ endPos)
    (h_end_pos : endPos < ps.tokens.size)
    (h_end_tok : ps.tokens[endPos]!.val = .flowMappingEnd)
    (h_at_end : ps.peek? = some .flowMappingEnd → ps.pos = endPos)
    (h_sep : pairs_acc.size > 0 →
             ps.peek? = some .flowEntry ∨ ps.peek? = some .flowMappingEnd)
    (h_start : ps.pos < endPos → pairs_acc.size = 0 →
               ps.peek? = some .key)
    (h_after_fe : ∀ k : Nat, ps.pos ≤ k → k < endPos →
                  ps.tokens[k]!.val = .flowEntry →
                  flowBracketBalance ps.tokens body_start k = 0 →
                  k + 1 ≤ endPos ∧ ps.tokens[k + 1]!.val = .key)
    (h_bal : flowBracketBalance ps.tokens body_start ps.pos = 0)
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
    exact peek_of_pos_val h_eq (by omega) h_end_tok
  | succ n ih =>
    unfold parseFlowMappingLoop
    simp only [bind, Except.bind, pure, Except.pure]
    -- 1. Outer match on ps.peek?: flowMappingEnd vs wildcard
    split
    · -- flowMappingEnd → immediate return
      exact ⟨pairs_acc, ps, rfl, ‹_›, h_at_end ‹_›, rfl, rfl⟩
    · -- wildcard → continue
      rename_i h_outer_not_end
      have h_lt : ps.pos < endPos := by
        rcases Nat.eq_or_lt_of_le h_pos with h_eq | h_lt
        · exfalso; exact h_outer_not_end (peek_of_pos_val h_eq (by omega) h_end_tok)
        · exact h_lt
      -- 2. if pairs_acc.size > 0
      split
      · -- pairs_acc.size > 0 → separator check
        split
        · -- flowEntry → advance, then inner dispatch
          split
          · -- flowMappingEnd after separator → contradiction (h_after_fe says next = key)
            rename_i h_adv_end
            exfalso
            have h_fe_val : ps.tokens[ps.pos]!.val = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) h_lt h_fe_val h_bal
            have ⟨_, h_val⟩ := peek_some_val h_adv_end
            simp [ParseState.advance] at h_val
            exact absurd (h_afe.2.symm.trans h_val) (by decide)
          · -- key after separator → full entry parse + recurse
            rename_i h_adv_not_end h_adv_key
            have h_fe_val : ps.tokens[ps.pos]!.val = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) h_lt h_fe_val h_bal
            have h_adv_pos : ps.advance.pos = ps.pos + 1 := by
              simp [ParseState.advance]
            have h_adv_pos_lt : ps.pos + 1 < endPos := by
              rcases Nat.eq_or_lt_of_le h_afe.1 with heq | hlt
              · exfalso
                have h_peek_end := peek_of_pos_val (ps := ps.advance) rfl
                  (show ps.advance.pos < ps.advance.tokens.size by
                    simp [ParseState.advance]; omega)
                  (show ps.advance.tokens[ps.advance.pos]!.val = .flowMappingEnd by
                    simp [ParseState.advance]; rw [heq]; exact h_end_tok)
                rw [h_adv_key] at h_peek_end; cases h_peek_end
              · exact hlt
            -- Apply h_entry
            have h_depth_at_adv : flowBracketBalance ps.tokens body_start (ps.pos + 1) = 0 := by
              have h_pos_bound : ps.pos < ps.tokens.toList.length := by
                show ps.pos < ps.tokens.size; omega
              rw [flowBracketBalance_compose ps.tokens body_start ps.pos (ps.pos + 1) h_bs (by omega),
                  h_bal, flowBracketBalance_single _ _ h_pos_bound]
              have h_eq : (ps.tokens.toList[ps.pos]'h_pos_bound).val = YamlToken.flowEntry := by
                show (ps.tokens[ps.pos]'(by omega)).val = YamlToken.flowEntry
                rw [← getElem!_pos ps.tokens ps.pos (by omega)]; exact h_fe_val
              rw [h_eq]; decide
            obtain ⟨key_val, key_ps, h_ek_ok, h_ek_adv, h_ek_bound, h_ek_tok, h_ek_tp, h_fmv_univ⟩ :=
              h_entry ps.advance n
                (by simp [ParseState.advance])
                (by omega) (by omega)
                h_adv_pos_lt
                (by omega)
                (by show flowBracketBalance ps.tokens body_start (ps.pos + 1) = 0
                    exact h_depth_at_adv)
                h_adv_key
            rw [h_ek_ok]; dsimp only []
            -- Split on the parseFlowMappingValue result match
            split
            · -- error case: contradicts h_fmv_univ (which says it always succeeds)
              rename_i err heq_err
              exfalso
              obtain ⟨_, _, h_ok, _⟩ := h_fmv_univ _ _
              exact absurd (heq_err.symm.trans h_ok) (by simp)
            · -- ok case: equate with h_fmv_univ result via determinism
              rename_i fmv_res heq_fmv
              obtain ⟨val_val, val_ps, h_fmv_ok, h_fmv_adv, h_fmv_bound, h_fmv_tok, h_fmv_tp, h_fmv_peek, h_entry_bal⟩ :=
                h_fmv_univ _ _
              have h_eq := Except.ok.inj (heq_fmv.symm.trans h_fmv_ok)
              obtain ⟨fmv_v, fmv_ps⟩ := fmv_res
              obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq.symm
              -- Apply IH
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
                  (by -- h_bal: fbb(body_start, val_ps.pos) = 0
                      rw [h_fmv_tok]
                      rw [show ps.advance.pos = ps.pos + 1 from h_adv_pos] at h_entry_bal
                      have h_tl : ps.tokens.toList.length = ps.tokens.size := rfl
                      exact flowBracketBalance_compose_zero ps.tokens body_start ps.pos val_ps.pos
                        h_bs (by omega) (by omega) h_bal
                        (by show flowBracketDelta (ps.tokens[ps.pos]'(by omega)).val = 0
                            rw [(getElem!_pos ps.tokens ps.pos (by omega)).symm, h_fe_val]; decide)
                        h_entry_bal)
                  (by omega)
              exact ⟨pairs_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_fmv_tok, h_tp_res.trans h_fmv_tp⟩
          · -- wildcard after separator (not flowMappingEnd, not key) → contradiction
            rename_i h_adv_not_end h_adv_not_key
            exfalso
            have h_fe_val : ps.tokens[ps.pos]!.val = .flowEntry := by
              have h_peek_fe : ps.peek? = some .flowEntry := by assumption
              exact (peek_some_val h_peek_fe).2
            have h_afe := h_after_fe ps.pos (Nat.le_refl _) h_lt h_fe_val h_bal
            exact h_adv_not_key (peek_of_pos_val (ps := ps.advance) rfl
              (show ps.advance.pos < ps.advance.tokens.size by
                simp [ParseState.advance]; omega)
              (show ps.advance.tokens[ps.advance.pos]!.val = .key by
                simp [ParseState.advance]; exact h_afe.2))
        · -- no separator → early return
          have h_acc_pos : pairs_acc.size > 0 := by assumption
          have h_not_fe : ps.peek? ≠ some .flowEntry := by assumption
          rcases h_sep h_acc_pos with h_fe | h_end
          · exfalso; exact h_not_fe h_fe
          · exact ⟨pairs_acc, ps, rfl, h_end, h_at_end h_end, rfl, rfl⟩
      · -- pairs_acc.size = 0 → dispatch directly
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
          · -- error case: contradicts h_fmv_univ
            rename_i err heq_err
            exfalso
            obtain ⟨_, _, h_ok, _⟩ := h_fmv_univ _ _
            exact absurd (heq_err.symm.trans h_ok) (by simp)
          · -- ok case
            rename_i fmv_res heq_fmv
            obtain ⟨val_val, val_ps, h_fmv_ok, h_fmv_adv, h_fmv_bound, h_fmv_tok, h_fmv_tp, h_fmv_peek, h_entry_bal⟩ :=
              h_fmv_univ _ _
            have h_eq := Except.ok.inj (heq_fmv.symm.trans h_fmv_ok)
            obtain ⟨fmv_v, fmv_ps⟩ := fmv_res
            obtain ⟨rfl, rfl⟩ := Prod.mk.inj h_eq.symm
            -- Apply IH
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
                (by -- h_bal: fbb(body_start, val_ps.pos) = 0
                    rw [h_fmv_tok,
                        flowBracketBalance_compose ps.tokens body_start ps.pos val_ps.pos h_bs (by omega),
                        h_bal, h_entry_bal]; simp)
                (by omega)
            exact ⟨pairs_res, ps_res, h_loop, h_peek_res, h_pos_res, h_tok_res.trans h_fmv_tok, h_tp_res.trans h_fmv_tp⟩
        · -- wildcard (not flowMappingEnd, not key) → contradiction
          rename_i h_not_end h_not_key
          exfalso
          have h_acc_zero : pairs_acc.size = 0 := by omega
          have hk := h_start h_lt h_acc_zero
          exact h_not_key hk

/-! #### §5f  Flow parser acceptance from structural properties

Phase I infrastructure: prove `ParseNodeFlowSeqOk` and `ParseEntryFlowMapOk`
from `FlowSubrangesOk`, by strong induction on span.  The key insight is that
nested bracket bodies have strictly smaller span, so the inductive hypothesis
covers inner bodies.  The universal quantification in `FlowSubrangesOk` over
all `(lo, hi)` subranges provides the structural properties for each level.

These theorems are designed to be **sorry-free** — all the difficulty is
pushed to proving `FlowSubrangesOk` (Phase J). -/


-- When `parseNodeProperties` sees a non-anchor/tag token, it returns
-- immediately with empty properties and unchanged state.
-- The `for _ in [:2] do` loop breaks on the first iteration because
-- `peek?` matches `| _ => break`.
set_option maxHeartbeats 3200000 in
theorem parseNodeProperties_skip (ps : ParseState)
    (h : match ps.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True) :
    parseNodeProperties ps = .ok ({}, ps) := by
  unfold parseNodeProperties
  dsimp only []
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
             Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
             show List.range' 0 2 1 = 0 :: List.range' 1 1 1 from by decide,
             List.forIn_cons, bind, Except.bind, pure, Except.pure]
  cases hpk : ps.peek?
  case none => simp_all
  case some tok => cases tok <;> simp_all

/-! ### Precondition structures for loop theorems

These structures bundle the preconditions needed by `parseFlowSequenceLoop_emitter_ok`
and `parseFlowMappingLoop_emitter_ok`. They factor out the repetitive mechanical setup
that appears in each nested bracket helper lemma. -/

/-- Bundle of 11 preconditions for `parseFlowSequenceLoop_emitter_ok`.

This structure captures all the conditions needed to invoke the flow sequence loop theorem
at `ps.advance` (after consuming `[`) with ending position `j` (matching `]`). -/
structure LoopSeqPreconditions
    (tokens : Array (Positioned YamlToken))
    (ps_advance : ParseState)
    (j body_start : Nat)
    (fuel : Nat) : Prop where
  /-- ParseNodeFlowSeqOk for the inner body -/
  h_pn : ParseNodeFlowSeqOk tokens j fuel body_start
  /-- Fuel suffices for the span -/
  h_fuel : fuel > j - ps_advance.pos
  /-- Current position is within the body -/
  h_pos : ps_advance.pos ≤ j
  /-- End position is in bounds -/
  h_end_pos : j < ps_advance.tokens.size
  /-- Token at end position is flowSequenceEnd -/
  h_end_tok : ps_advance.tokens[j]!.val = .flowSequenceEnd
  /-- If we're at flowSequenceEnd, we're at the end position -/
  h_at_end : ps_advance.peek? = some .flowSequenceEnd → ps_advance.pos = j
  /-- If we have accumulated items, next token is separator or end -/
  h_entry : (#[] : Array YamlValue).size > 0 →
            ps_advance.peek? = some .flowEntry ∨
            ps_advance.peek? = some .flowSequenceEnd
  /-- If starting empty and not at end, first token is content.
      Guard `ps_advance.pos < j` excludes empty body case where peek? = flowSequenceEnd. -/
  h_content_start : ps_advance.pos < j → (#[] : Array YamlValue).size = 0 →
                    (∃ c s, ps_advance.peek? = some (.scalar c s)) ∨
                    ps_advance.peek? = some .flowSequenceStart ∨
                    ps_advance.peek? = some .flowMappingStart
  /-- After flowEntry at depth 0, there's content -/
  h_after_fe : ∀ k : Nat, ps_advance.pos ≤ k → k < j →
               ps_advance.tokens[k]!.val = .flowEntry →
               flowBracketBalance ps_advance.tokens body_start k = 0 →
               k + 1 ≤ j ∧
               ((∃ c s, ps_advance.tokens[k + 1]!.val = .scalar c s) ∨
                ps_advance.tokens[k + 1]!.val = .flowSequenceStart ∨
                ps_advance.tokens[k + 1]!.val = .flowMappingStart)
  /-- Bracket balance at start position is 0 -/
  h_bal : flowBracketBalance ps_advance.tokens body_start ps_advance.pos = 0
  /-- Body start is at or before current position -/
  h_bs : body_start ≤ ps_advance.pos

/-- Bundle of preconditions for `parseFlowMappingLoop_emitter_ok`.

Similar to `LoopSeqPreconditions` but for flow mapping bodies. The structure is analogous
but uses `ParseEntryFlowMapOk` and `.flowMappingEnd` instead of sequence variants. -/
structure LoopMapPreconditions
    (tokens : Array (Positioned YamlToken))
    (ps_advance : ParseState)
    (j body_start : Nat)
    (fuel : Nat) : Prop where
  /-- ParseEntryFlowMapOk for the inner body -/
  h_pn : ParseEntryFlowMapOk tokens j fuel body_start
  /-- Fuel suffices for the span -/
  h_fuel : fuel > j - ps_advance.pos
  /-- Current position is within the body -/
  h_pos : ps_advance.pos ≤ j
  /-- End position is in bounds -/
  h_end_pos : j < ps_advance.tokens.size
  /-- Token at end position is flowMappingEnd -/
  h_end_tok : ps_advance.tokens[j]!.val = .flowMappingEnd
  /-- If we're at flowMappingEnd, we're at the end position -/
  h_at_end : ps_advance.peek? = some .flowMappingEnd → ps_advance.pos = j
  /-- If we have accumulated pairs, next token is separator or end -/
  h_entry : (#[] : Array (YamlValue × YamlValue)).size > 0 →
            ps_advance.peek? = some .flowEntry ∨
            ps_advance.peek? = some .flowMappingEnd
  /-- If starting empty and not at end, first token is a key.
      Guard `ps_advance.pos < j` excludes empty body case where peek? = flowMappingEnd. -/
  h_key_start : ps_advance.pos < j → (#[] : Array (YamlValue × YamlValue)).size = 0 →
                ps_advance.peek? = some .key
  /-- After flowEntry at depth 0, there's a key -/
  h_after_fe : ∀ k : Nat, ps_advance.pos ≤ k → k < j →
               ps_advance.tokens[k]!.val = .flowEntry →
               flowBracketBalance ps_advance.tokens body_start k = 0 →
               k + 1 < j ∧ ps_advance.tokens[k + 1]!.val = .key
  /-- Bracket balance at start position is 0 -/
  h_bal : flowBracketBalance ps_advance.tokens body_start ps_advance.pos = 0
  /-- Body start is at or before current position -/
  h_bs : body_start ≤ ps_advance.pos

/-! ### Helper lemmas to construct loop preconditions

These lemmas mechanically construct `LoopSeqPreconditions` and `LoopMapPreconditions`
from the bracket matching results and inner body properties. They factor out the ~105 lines
of repetitive precondition setup that appears in each nested bracket proof. -/

/-- Construct loop preconditions for a flow sequence body from bracket matching results.

Given:
- `ps` at a `[` token (flowSequenceStart)
- `j` is the matching `]` position (from `SeqBodyProps.bracket_seq`)
- `h_inner_sbp` captures the structural properties of the inner body `[ps.pos+1, j)`
- `h_inner_pnok` gives ParseNodeFlowSeqOk for the inner body

This lemma mechanically derives all 11 preconditions needed by `parseFlowSequenceLoop_emitter_ok`
to be called at `ps.advance` (after consuming the `[`). -/
theorem mk_loop_seq_preconditions
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState)
    (j : Nat)
    (fuel : Nat)
    (h_tok : ps.tokens = tokens)
    (h_pos_bound : ps.pos < tokens.size)
    (h_j_gt : ps.pos < j)
    (h_j_bound : j < tokens.size)
    (h_j_val : tokens[j]!.val = .flowSequenceEnd)
    (h_inner_sbp : SeqBodyProps tokens (ps.pos + 1) j)
    (h_inner_pnok : ParseNodeFlowSeqOk tokens j fuel (ps.pos + 1))
    (h_fuel_bound : fuel > j - (ps.pos + 1)) :
    LoopSeqPreconditions tokens ps.advance j (ps.pos + 1) fuel := by
  constructor
  · -- h_pn: ParseNodeFlowSeqOk tokens j fuel (ps.pos + 1)
    exact h_inner_pnok
  · -- h_fuel: fuel > j - ps.advance.pos
    have : ps.advance.tokens.size = tokens.size := by simp [ParseState.advance_tokens, h_tok]
    simp [ParseState.advance]
    exact h_fuel_bound
  · -- h_pos: ps.advance.pos ≤ j
    simp [ParseState.advance]; omega
  · -- h_end_pos: j < ps.advance.tokens.size
    rw [ParseState.advance_tokens, h_tok]; exact h_j_bound
  · -- h_end_tok: ps.advance.tokens[j]!.val = .flowSequenceEnd
    rw [ParseState.advance_tokens, h_tok]; exact h_j_val
  · -- h_at_end: ps.advance.peek? = some .flowSequenceEnd → ps.advance.pos = j
    intro h_peek_end
    have h_peek_val := peek_some_val h_peek_end
    simp [ParseState.advance, h_tok] at h_peek_val
    obtain ⟨_, h_val_end⟩ := h_peek_val
    by_cases h_eq : ps.pos + 1 = j
    · simp [ParseState.advance, h_eq]
    · -- Contradiction: content_start says it's content, but we have flowSequenceEnd
      have h_cs := h_inner_sbp.content_start (by omega)
      rw [h_val_end] at h_cs
      rcases h_cs with ⟨c, s, hcs⟩ | hcs | hcs <;> cases hcs
  · -- h_entry: vacuous (empty array)
    intro h_size; simp at h_size
  · -- h_content_start: from inner SeqBodyProps.content_start
    intro h_not_at_end _
    -- With the guard ps.advance.pos < j, we know the body is non-empty
    simp [ParseState.advance] at h_not_at_end
    have h_lt : ps.pos + 1 < j := h_not_at_end
    have h_cs := h_inner_sbp.content_start h_lt
    unfold isFlowContentStart at h_cs
    have h_peek_eq : ps.advance.peek? =
      if ps.pos + 1 < tokens.size then some tokens[ps.pos + 1]!.val else none := by
      simp [ParseState.advance, ParseState.peek?, h_tok]
    rw [h_peek_eq]
    have h_bound : ps.pos + 1 < tokens.size := by omega
    simp [h_bound]
    rcases h_cs with ⟨c, s, hcs⟩ | hcs | hcs
    · left; refine ⟨c, s, ?_⟩; rw [← getElem!_pos tokens (ps.pos + 1) h_bound]; exact hcs
    · right; left; rw [← getElem!_pos tokens (ps.pos + 1) h_bound]; exact hcs
    · right; right; rw [← getElem!_pos tokens (ps.pos + 1) h_bound]; exact hcs
  · -- h_after_fe: from inner SeqBodyProps.after_fe
    intro k h_pos_k h_k_lt h_fe h_bal_k
    rw [ParseState.advance_tokens, h_tok] at h_fe h_bal_k ⊢
    simp [ParseState.advance] at h_pos_k
    have h_after := h_inner_sbp.after_fe k h_pos_k h_k_lt h_bal_k h_fe
    obtain ⟨h_le, h_content⟩ := h_after
    constructor
    · exact Nat.le_of_lt h_le
    · unfold isFlowContentStart at h_content
      exact h_content
  · -- h_bal: flowBracketBalance at empty range
    rw [ParseState.advance_tokens, h_tok]
    simp [ParseState.advance]
    unfold flowBracketBalance
    simp
  · -- h_bs: body_start ≤ ps.advance.pos
    simp [ParseState.advance]

/-- Construct loop preconditions for a flow mapping body from bracket matching results.

Given:
- `ps` at a `{` token (flowMappingStart)
- `j` is the matching `}` position (from `MapBodyProps.bracket_map`)
- `h_inner_mbp` captures the structural properties of the inner body `[ps.pos+1, j)`
- `h_inner_peok` gives ParseEntryFlowMapOk for the inner body

This lemma mechanically derives all 10 preconditions needed by `parseFlowMappingLoop_emitter_ok`
to be called at `ps.advance` (after consuming the `{`). -/
theorem mk_loop_map_preconditions
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState)
    (j : Nat)
    (fuel : Nat)
    (h_tok : ps.tokens = tokens)
    (h_pos_bound : ps.pos < tokens.size)
    (h_j_gt : ps.pos < j)
    (h_j_bound : j < tokens.size)
    (h_j_val : tokens[j]!.val = .flowMappingEnd)
    (h_inner_mbp : MapBodyProps tokens (ps.pos + 1) j)
    (h_inner_peok : ParseEntryFlowMapOk tokens j fuel (ps.pos + 1))
    (h_fuel_bound : fuel > j - (ps.pos + 1)) :
    LoopMapPreconditions tokens ps.advance j (ps.pos + 1) fuel := by
  constructor
  · -- h_pe: ParseEntryFlowMapOk tokens j fuel (ps.pos + 1)
    exact h_inner_peok
  · -- h_fuel: fuel > j - ps.advance.pos
    have : ps.advance.tokens.size = tokens.size := by simp [ParseState.advance_tokens, h_tok]
    simp [ParseState.advance]
    exact h_fuel_bound
  · -- h_pos: ps.advance.pos ≤ j
    simp [ParseState.advance]; omega
  · -- h_end_pos: j < ps.advance.tokens.size
    rw [ParseState.advance_tokens, h_tok]; exact h_j_bound
  · -- h_end_tok: ps.advance.tokens[j]!.val = .flowMappingEnd
    rw [ParseState.advance_tokens, h_tok]; exact h_j_val
  · -- h_at_end: ps.advance.peek? = some .flowMappingEnd → ps.advance.pos = j
    intro h_peek_end
    have h_peek_val := peek_some_val h_peek_end
    simp [ParseState.advance, h_tok] at h_peek_val
    obtain ⟨_, h_val_end⟩ := h_peek_val
    by_cases h_eq : ps.pos + 1 = j
    · simp [ParseState.advance, h_eq]
    · -- Contradiction: key_start says it's .key, but we have flowMappingEnd
      have h_ks := h_inner_mbp.key_start (by omega)
      rw [h_val_end] at h_ks
      cases h_ks
  · -- h_entry: vacuous (empty array)
    intro h_size; simp at h_size
  · -- h_key_start: from inner MapBodyProps.key_start
    intro h_not_at_end _
    -- With the guard ps.advance.pos < j, we know the body is non-empty
    simp [ParseState.advance] at h_not_at_end
    have h_lt : ps.pos + 1 < j := h_not_at_end
    have h_ks := h_inner_mbp.key_start h_lt
    have h_peek_eq : ps.advance.peek? =
      if ps.pos + 1 < tokens.size then some tokens[ps.pos + 1]!.val else none := by
      simp [ParseState.advance, ParseState.peek?, h_tok]
    rw [h_peek_eq]
    have h_bound : ps.pos + 1 < tokens.size := by omega
    simp [h_bound]
    rw [← getElem!_pos tokens (ps.pos + 1) h_bound]
    exact h_ks
  · -- h_after_fe: from inner MapBodyProps.after_fe
    intro k h_pos_k h_k_lt h_fe h_bal_k
    rw [ParseState.advance_tokens, h_tok] at h_fe h_bal_k ⊢
    simp [ParseState.advance] at h_pos_k
    have h_after := h_inner_mbp.after_fe k h_pos_k h_k_lt h_bal_k h_fe
    obtain ⟨h_le, h_key⟩ := h_after
    constructor
    · -- Need to strengthen k+1 ≤ j to k+1 < j
      by_cases h_eq : k + 1 = j
      · -- If k+1 = j, then tokens[k+1] = flowMappingEnd, contradicting h_key : tokens[k+1] = .key
        rw [h_eq] at h_key
        rw [h_j_val] at h_key
        cases h_key
      · omega
    · exact h_key
  · -- h_bal: flowBracketBalance at empty range
    rw [ParseState.advance_tokens, h_tok]
    simp [ParseState.advance]
    unfold flowBracketBalance
    simp
  · -- h_bs: body_start ≤ ps.advance.pos
    simp [ParseState.advance]

/-! ### Helper lemmas for flow_parser_ok_of_structure

We break the long proof into smaller lemmas for each case.

## Proof notes for nested bracket lemmas

The nested bracket lemmas (flowSeqStart, flowMapStart, entry in map) require coordinating:

**1. parseNode call chain:**
   - parseNode (m+1 fuel case, not alias)
   - parseNodeProperties → returns ({}, ps) for flowSequenceStart (no props before [)
   - validateNodeProps → passes (flowSequenceStart is valid content)
   - parseNodeContent → dispatches to parseFlowSequence
   - parseFlowSequence → advances past [, calls parseFlowSequenceLoop, checks ]
   - applyNodeFinalization → constructs result, preserves tokens

**2. Key hypotheses from strong induction setup:**
   - `h_sbp.bracket_seq`: finds matching ] at j with inner balance
   - `h_sub.seq`: constructs SeqBodyProps for inner body (ps.pos+1, j)
   - `ih_seq`: ParseNodeFlowSeqOk for inner body (smaller span)

**3. Loop theorem (parseFlowSequenceLoop_emitter_ok) preconditions (11 total):**
   - h_pn: ParseNodeFlowSeqOk tokens j fuel (ps.pos+1)  ← from ih_seq
   - h_fuel: fuel > j - ps.advance.pos  ← arithmetic: 4*N+3 > j-ps.pos-1 < endPos
   - h_pos: ps.advance.pos ≤ j  ← ps.advance.pos = ps.pos+1 ≤ j
   - h_end_pos: j < tokens.size  ← from bracket_seq + endPos bound
   - h_end_tok: tokens[j]!.val = .flowSequenceEnd  ← from bracket_seq
   - h_at_end: peek = flowSeqEnd → pos = j  ← from SeqBodyProps.content_start
   - h_entry: items > 0 → peek = flowEntry ∨ flowSeqEnd  ← vacuous (items = #[])
   - h_content_start: items = 0 → isFlowContentStart  ← from SeqBodyProps.content_start
   - h_after_fe: ∀k, after flowEntry is content  ← from SeqBodyProps.after_fe
   - h_bal: flowBracketBalance tokens (ps.pos+1) ps.advance.pos = 0  ← [ at ps.pos has delta +1, but balance from ps.pos+1 to ps.pos+1 is 0
   - h_bs: ps.pos+1 ≤ ps.advance.pos  ← ps.advance.pos = ps.pos+1

**4. Existential witness:** val = YamlValue.sequence .flow items, ps' at j+1

**5. Pattern for flowMapStart:** Use bracket_map, MapBodyProps, ih_map, parseFlowMappingLoop_emitter_ok

-/

/-- **Helper Lemma 1**: parseExplicitKey on scalar succeeds, advances by 1 position.

    Given ps at a scalar token, parseExplicitKey calls parseNode which consumes the scalar
    and advances by 1. Factors out scalar key parsing pattern used in all map entry proofs. -/
theorem parseExplicitKey_scalar
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (m : Nat)
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_pos_bound : ps.pos < tokens.size)
    (c : String) (s : ScalarStyle)
    (h_scalar : tokens[ps.pos]!.val = .scalar c s) :
    ∃ key_val key_ps,
      parseExplicitKey ps m = .ok (key_val, key_ps) ∧
      key_ps.pos = ps.pos + 1 ∧
      key_ps.tokens = tokens ∧
      key_ps.trackPositions = ps.trackPositions := by
  -- parseExplicitKey on scalar dispatches to parseNode
  have h_peek : ps.peek? = some (.scalar c s) := by
    unfold ParseState.peek?
    have h_bound : ps.pos < ps.tokens.size := by rw [h_tok]; exact h_pos_bound
    rw [if_pos h_bound]
    rw [h_tok, h_scalar]

  -- parseExplicitKey is not emptyNode case (scalar ≠ .value/.flowEntry/.flowMappingEnd)
  have h_explicit_eq : parseExplicitKey ps m = parseNode ps m := by
    unfold parseExplicitKey
    rw [h_peek]

  -- Fuel decomposition: m = m' + 1
  obtain ⟨m', h_m'⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩

  -- parseNodeProperties skip on scalar
  have h_pnp : parseNodeProperties ps = .ok ({}, ps) := by
    exact parseNodeProperties_skip ps (by rw [h_peek]; trivial)

  -- parseNode result
  have h_node_eq : parseNode ps (m' + 1) =
      .ok (applyNodeFinalization
        (.scalar { content := c, style := s, tag := none, anchor := none })
        ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
    unfold parseNode
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · rename_i h_alias; rw [h_peek] at h_alias; cases h_alias
    · rw [h_pnp]; simp
      unfold validateNodeProps
      rw [h_peek]; simp only [pure, Except.pure, bind, Except.bind]
      unfold parseNodeContent
      rw [h_peek]; simp

  -- Build witness
  refine ⟨(applyNodeFinalization
    (.scalar { content := c, style := s, tag := none, anchor := none })
    ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).1,
   (applyNodeFinalization
    (.scalar { content := c, style := s, tag := none, anchor := none })
    ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2,
   ?_, ?_, ?_, ?_⟩

  · -- parseExplicitKey result
    rw [h_explicit_eq, h_m', h_node_eq]

  · -- key_ps.pos = ps.pos + 1
    rw [applyNodeFinalization_pos]
    simp [ParseState.advance]

  · -- key_ps.tokens = tokens
    rw [applyNodeFinalization_tokens, ParseState.advance_tokens, h_tok]

  · -- key_ps.trackPositions = ps.trackPositions
    rw [applyNodeFinalization_trackPositions]
    simp [ParseState.advance]

/-- **Helper Lemma 2**: parseExplicitKey on [ succeeds, advances to after ].
    Factors out bracket key parsing pattern. Requires IH for inner bracket body. -/
theorem parseExplicitKey_flowSeq
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (m : Nat)
    (j : Nat)  -- Position of matching ]
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_m_fuel : 4 * tokens.size + 6 ≤ m)
    (h_pos_bound : ps.pos < tokens.size)
    (h_fss : tokens[ps.pos]!.val = .flowSequenceStart)
    (h_j_bound : j < tokens.size)
    (h_j_tok : tokens[j]!.val = .flowSequenceEnd)
    (h_j_bal : flowBracketBalance tokens (ps.pos + 1) j = 0)
    -- IH provides ParseNodeFlowSeqOk for inner body
    (h_inner : ParseNodeFlowSeqOk tokens j (4 * tokens.size + 4) (ps.pos + 1)) :
    ∃ key_val key_ps,
      parseExplicitKey ps m = .ok (key_val, key_ps) ∧
      key_ps.pos = j + 1 ∧
      key_ps.tokens = tokens ∧
      key_ps.trackPositions = ps.trackPositions := by
  -- STRATEGIC SORRY: This requires detailed reasoning about parseNode on [
  --
  -- Proof sketch:
  -- 1. parseExplicitKey dispatches to parseNode ([ is not emptyNode case)
  -- 2. parseNode calls parseFlowSequence which calls parseFlowSequenceLoop
  -- 3. Use h_inner (ParseNodeFlowSeqOk) to show loop succeeds
  -- 4. Loop returns at position j with items array
  -- 5. parseFlowSequence verifies flowSequenceEnd token and advances
  -- 6. applyNodeFinalization is called, returning final position j + 1
  --
  -- Implementation requires:
  -- - Fuel monotonicity: h_inner has fuel 4*N+4, but we have m ≥ 4*N+6
  -- - Need parseNode_flowSeqStart_in_seq-like reasoning
  -- - Or extract from completed parseNode_flowSeqStart_in_seq proof
  --
  -- ~40 lines implementation
  sorry

/-- **Helper Lemma 3**: parseExplicitKey on { succeeds, advances to after }.
    Factors out bracket key parsing pattern. Requires IH for inner bracket body. -/
theorem parseExplicitKey_flowMap
    (tokens : Array (Positioned YamlToken))
    (ps : ParseState) (m : Nat)
    (j : Nat)  -- Position of matching }
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_m_fuel : 4 * tokens.size + 6 ≤ m)
    (h_pos_bound : ps.pos < tokens.size)
    (h_fms : tokens[ps.pos]!.val = .flowMappingStart)
    (h_j_bound : j < tokens.size)
    (h_j_tok : tokens[j]!.val = .flowMappingEnd)
    (h_j_bal : flowBracketBalance tokens (ps.pos + 1) j = 0)
    -- IH provides ParseEntryFlowMapOk for inner body
    (h_inner : ParseEntryFlowMapOk tokens j (4 * tokens.size + 4) (ps.pos + 1)) :
    ∃ key_val key_ps,
      parseExplicitKey ps m = .ok (key_val, key_ps) ∧
      key_ps.pos = j + 1 ∧
      key_ps.tokens = tokens ∧
      key_ps.trackPositions = ps.trackPositions := by
  -- STRATEGIC SORRY: Symmetric with parseExplicitKey_flowSeq
  --
  -- Proof sketch:
  -- 1. parseExplicitKey dispatches to parseNode ({ is not emptyNode case)
  -- 2. parseNode calls parseFlowMapping which calls parseFlowMappingLoop
  -- 3. Use h_inner (ParseEntryFlowMapOk) to show loop succeeds
  -- 4. Loop returns at position j with pairs array
  -- 5. parseFlowMapping verifies flowMappingEnd token and advances
  -- 6. applyNodeFinalization is called, returning final position j + 1
  --
  -- Implementation identical structure to parseExplicitKey_flowSeq
  -- ~40 lines implementation
  sorry

/-- **Helper Lemma 3.5**: ParseNode on scalars preserves ParseState fields.

    When parseNode processes a scalar token (no properties), the resulting
    ParseState preserves anchors, tagHandles, and trackPositions from the
    input state (after accounting for the advance operation).

    This lemma isolates the field preservation logic needed for proving
    parseFlowMappingValue_ok, avoiding the need to inline applyNodeFinalization
    reasoning in multiple places. -/
theorem parseNode_scalar_fields :
  ∀ (ps : ParseState) (c : String) (s : ScalarStyle) (fuel : Nat),
    ps.peek? = some (.scalar c s) →
    fuel > 0 →
    ∃ (val : YamlValue) (ps' : ParseState),
      parseNode ps fuel = .ok (val, ps') ∧
      val = .scalar { content := c, style := s } ∧
      ps'.pos = ps.pos + 1 ∧
      ps'.tokens = ps.tokens ∧
      ps'.anchors = ps.advance.anchors ∧
      ps'.tagHandles = ps.advance.tagHandles ∧
      ps'.trackPositions = ps.advance.trackPositions := by
  intro ps c s fuel h_peek h_fuel

  -- Extract fuel successor
  obtain ⟨fuel', h_fuel_eq⟩ : ∃ k, fuel = k + 1 := ⟨fuel - 1, by omega⟩
  rw [h_fuel_eq]

  -- Unfold parseNode computation
  unfold parseNode

  -- Since peek? = scalar, the alias check doesn't match
  rw [h_peek]
  simp only [Bind.bind, Except.bind, pure, Except.pure]

  -- parseNodeProperties returns empty props
  have h_pnp : parseNodeProperties ps = .ok ({}, ps) := by
    apply parseNodeProperties_skip
    rw [h_peek]
    trivial
  rw [h_pnp]
  simp

  -- validateNodeProps succeeds
  have h_vnp : validateNodeProps ps ps.pos {} = .ok () := by
    unfold validateNodeProps
    rw [h_peek]
    rfl
  rw [h_vnp]
  simp

  -- parseNodeContent returns scalar and advances
  have h_pnc : parseNodeContent ps fuel' {} =
               .ok (.scalar { content := c, style := s }, ps.advance) := by
    unfold parseNodeContent
    rw [h_peek]
  rw [h_pnc]
  simp

  -- applyNodeFinalization with empty props
  -- Unfold to show field preservation
  unfold applyNodeFinalization

  -- Empty props means no anchor/tag
  have h_anchor_none : ({} : NodeProperties).anchor = none := rfl
  have h_tag_none : ({} : NodeProperties).tag = none := rfl

  -- Scalar matches 'other => other' case, so val unchanged
  simp

  -- The result depends on trackPositions
  -- We need to construct the witness based on whether ps.advance.trackPositions = true or false
  cases h_tp : ps.advance.trackPositions

  case false =>
    -- trackPositions = false, so no nodePositions update
    -- Result is (.scalar ..., ps.advance)
    refine ⟨.scalar { content := c, style := s }, ps.advance, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Equality: ite false returns ps.advance
      simp
    · rfl
    · simp [ParseState.advance]
    · rfl
    · rfl
    · rfl
    · exact h_tp

  case true =>
    -- trackPositions = true, so nodePositions updated
    let nodeStartPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
    let nodeEndPos := ps.advance.lastPos?.getD nodeStartPos
    let ps_final := { ps.advance with nodePositions := ps.advance.nodePositions.push (ps.advance.currentPath, nodeStartPos, nodeEndPos) }

    refine ⟨.scalar { content := c, style := s }, ps_final, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · -- Equality: ite true updates nodePositions
      simp [h_tp, ps_final, nodeStartPos, nodeEndPos]
    · rfl
    · simp [ps_final, ParseState.advance]
    · simp [ps_final]
    · simp [ps_final]
    · simp [ps_final]
    · simp [ps_final]; exact h_tp

/-- **Helper Lemma 4**: parseFlowMappingValue succeeds when positioned at .value token.

    This is the common second half of all 3 key cases. After parseExplicitKey succeeds
    and positions at .value, this lemma handles parsing the value content.

    Key insight: parseFlowMappingValue internally handles all value content types
    (scalar/[/{) through its call to parseNode, so we don't need separate value helpers.

    Takes original_pos explicitly since key_ps.pos - 2 doesn't work for bracket cases. -/
theorem parseFlowMappingValue_ok
    (tokens : Array (Positioned YamlToken))
    (endPos body_start : Nat)
    (span_bound : Nat)
    (original_pos : Nat)  -- Position of original .key token
    (key_ps : ParseState) (m : Nat)
    (h_tok : key_ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_m_fuel : 4 * tokens.size + 6 ≤ m)
    (h_endPos_bound : endPos < tokens.size)
    (h_span_bound : endPos - body_start ≤ span_bound + 1)
    (h_pos : key_ps.pos < endPos)
    (h_bs : body_start ≤ original_pos)
    (h_orig_lt : original_pos < key_ps.pos)
    (h_depth_orig : flowBracketBalance tokens body_start original_pos = 0)
    (h_depth : flowBracketBalance tokens body_start key_ps.pos = 0)
    (h_value_tok : tokens[key_ps.pos]!.val = .value)
    (h_value_peek : key_ps.peek? = some .value)
    -- Content follows .value (from MapBodyProps.value_content)
    (h_content_bound : key_ps.pos + 1 < endPos)
    (h_content : isFlowContentStart tokens[key_ps.pos + 1]!.val)
    -- Need MapBodyProps and IH for nested brackets in value
    (h_mbp : MapBodyProps tokens body_start endPos)
    (h_sub : FlowSubrangesOk tokens)
    -- IH for nested brackets (sequences and maps)
    (ih_seq : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowSequenceEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseNodeFlowSeqOk tokens j fuel lo)
    (ih_map : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowMappingEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseEntryFlowMapOk tokens j fuel lo) :
    ∀ (savedPath : YamlPath) (keyContent : String),
      ∃ val_val val_ps,
        parseFlowMappingValue key_ps m savedPath keyContent = .ok (val_val, val_ps) ∧
        val_ps.pos > original_pos ∧  -- Advances past original .key position
        val_ps.pos ≤ endPos ∧
        val_ps.tokens = tokens ∧
        val_ps.trackPositions = key_ps.trackPositions ∧
        (val_ps.peek? = some .flowEntry ∨
         (val_ps.peek? = some .flowMappingEnd ∧ val_ps.pos = endPos)) ∧
        flowBracketBalance tokens original_pos val_ps.pos = 0 := by
  intro savedPath keyContent
  -- Strategy: parseFlowMappingValue updates path, tryConsumes .key (fails),
  -- tryConsumes .value (succeeds, advances), then calls parseNode on content.
  -- We case-split on content type (scalar/[/{) and use appropriate parseNode lemma.

  -- Step 1: Establish bounds and properties
  have h_key_bound : key_ps.pos < tokens.size := by
    calc key_ps.pos < endPos := h_pos
    _ < tokens.size := h_endPos_bound

  -- After consuming .value, position is key_ps.pos + 1
  have h_after_value_bound : key_ps.pos + 1 < tokens.size := by
    calc key_ps.pos + 1 < endPos + 1 := by omega
    _ ≤ tokens.size := by omega

  -- Step 2: Show tryConsume .key fails (no retroactive key marker)
  -- This is immediate since key_ps.peek? = some .value ≠ some .key
  have h_no_key : key_ps.tryConsume .key = (false, key_ps) := by
    unfold ParseState.tryConsume
    rw [h_value_peek]
    simp

  -- Step 3: Show tryConsume .value succeeds
  have h_consume_value : key_ps.tryConsume .value = (true, key_ps.advance) := by
    unfold ParseState.tryConsume
    rw [h_value_peek]
    simp

  let ps_after_value := key_ps.advance
  have h_after_tok : ps_after_value.tokens = tokens := by
    simp [ps_after_value, ParseState.advance_tokens, h_tok]
  have h_after_pos : ps_after_value.pos = key_ps.pos + 1 := by
    simp [ps_after_value, ParseState.advance]

  -- Step 4: Content token is flow content start
  have h_content_tok : tokens[ps_after_value.pos]!.val = tokens[key_ps.pos + 1]!.val := by
    rw [h_after_pos]

  -- Step 5: Case split on content type (scalar, [, or {)
  have h_content_peek : ps_after_value.peek? = some tokens[key_ps.pos + 1]!.val := by
    unfold ParseState.peek?
    rw [h_after_tok, h_after_pos]
    simp only [h_after_value_bound, ↓reduceIte]

  -- Step 6: Case split on content type using isFlowContentStart
  rcases h_content with ⟨c, s, h_scalar⟩ | h_fss | h_fms

  · -- Scalar value: parseNode → scalar → advances to key_ps.pos + 2
    -- Use MapBodyProps.value_scalar_succ to get FE/mapEnd at key_ps.pos + 2
    have h_scalar' : ∃ c s, tokens[key_ps.pos + 1]!.val = .scalar c s := ⟨c, s, h_scalar⟩
    have h_bs_ps : body_start ≤ key_ps.pos := by omega
    have ⟨h_succ_bound, h_succ_peek⟩ :=
      h_mbp.value_scalar_succ key_ps.pos h_bs_ps h_pos h_depth h_value_tok h_scalar'

    -- Unfold parseFlowMappingValue structure:
    -- let ps := { key_ps with currentPath := savedPath.push (.key keyContent) }
    -- let (_, ps) := ps.tryConsume .key  -- fails
    -- let (consumed, ps) := ps.tryConsume .value  -- succeeds → ps_after_value
    -- let (val, ps) ← parseNode ps m
    -- return (val, { ps with currentPath := savedPath })

    -- Step 1: After path update and tryConsumes, we're at ps_after_value
    let ps_with_path := { key_ps with currentPath := savedPath.push (.key keyContent) }

    -- Step 2: ps_after_value.peek? = scalar, so parseNode will succeed
    have h_scalar_peek : ps_after_value.peek? = some (.scalar c s) := by
      rw [h_content_peek, h_scalar]

    -- Step 3: parseNode on scalar advances by 1
    -- parseNode: no alias → empty props → parseNodeContent (scalar) → advance → finalize
    -- Result: ps_after_value.advance
    let ps_final := ps_after_value.advance
    have h_final_pos : ps_final.pos = key_ps.pos + 2 := by
      calc ps_final.pos = ps_after_value.advance.pos := rfl
        _ = ps_after_value.pos + 1 := rfl
        _ = (key_ps.pos + 1) + 1 := by rw [h_after_pos]
        _ = key_ps.pos + 2 := by omega

    -- Step 4: Final position properties
    have h_final_gt : ps_final.pos > original_pos := by
      rw [h_final_pos]; omega

    have h_final_le : ps_final.pos ≤ endPos := by
      rw [h_final_pos]; omega

    have h_final_tok : ps_final.tokens = tokens := by
      simp only [ps_final, ParseState.advance, ps_after_value]
      exact h_after_tok

    have h_final_tp : ps_final.trackPositions = key_ps.trackPositions := by
      simp only [ps_final, ParseState.advance, ps_after_value]

    -- Step 5: Final peek is FE or mapEnd
    have h_final_peek : ps_final.peek? = some .flowEntry ∨
                        (ps_final.peek? = some .flowMappingEnd ∧ ps_final.pos = endPos) := by
      unfold ParseState.peek?
      rw [h_final_tok, h_final_pos]
      simp only [if_pos (by omega : key_ps.pos + 2 < tokens.size)]
      rcases h_succ_peek with h_fe | ⟨h_me, h_eq⟩
      · left; simp [h_fe]
      · right
        constructor
        · simp [h_me]
        · calc ps_final.pos = key_ps.pos + 2 := h_final_pos
            _ = endPos := h_eq

    -- Step 6: Balance from original_pos to final position is 0
    have h_final_bal : flowBracketBalance tokens original_pos ps_final.pos = 0 := by
      rw [h_final_pos]

      -- Decompose: balance[original_pos, key_ps.pos+2]
      --           = balance[original_pos, key_ps.pos] + balance[key_ps.pos, key_ps.pos+1] + balance[key_ps.pos+1, key_ps.pos+2]
      --
      -- From h_depth_orig and h_depth via composition:
      --   balance[body_start, key_ps.pos] = balance[body_start, original_pos] + balance[original_pos, key_ps.pos]
      --   0 = 0 + balance[original_pos, key_ps.pos]
      --   So: balance[original_pos, key_ps.pos] = 0
      have h_bal_to_value : flowBracketBalance tokens original_pos key_ps.pos = 0 := by
        have h_compose := flowBracketBalance_compose tokens body_start original_pos key_ps.pos
          (by omega) (by omega)
        rw [h_depth_orig, h_depth] at h_compose
        omega

      -- Token at key_ps.pos is .value (delta = 0)
      have h_value_single : flowBracketBalance tokens key_ps.pos (key_ps.pos + 1) = 0 := by
        rw [flowBracketBalance_single tokens key_ps.pos (by simp; omega)]
        show flowBracketDelta tokens.toList[key_ps.pos].val = 0
        simp only [flowBracketDelta]
        -- tokens.toList[i].val is definitionally tokens[i].val (both use getElem)
        have h_bound : key_ps.pos < tokens.size := by omega
        have : tokens.toList[key_ps.pos].val = (tokens[key_ps.pos]'h_bound).val := rfl
        rw [this]
        have : (tokens[key_ps.pos]'h_bound).val = tokens[key_ps.pos]!.val := by
          rw [getElem!_pos]
        rw [this, h_value_tok]

      -- Token at key_ps.pos+1 is .scalar (delta = 0)
      have h_scalar_single : flowBracketBalance tokens (key_ps.pos + 1) (key_ps.pos + 2) = 0 := by
        rw [flowBracketBalance_single tokens (key_ps.pos + 1) (by simp; omega)]
        show flowBracketDelta tokens.toList[key_ps.pos + 1].val = 0
        simp only [flowBracketDelta]
        have h_bound : key_ps.pos + 1 < tokens.size := by omega
        have : tokens.toList[key_ps.pos + 1].val = (tokens[key_ps.pos + 1]'h_bound).val := rfl
        rw [this]
        have : (tokens[key_ps.pos + 1]'h_bound).val = tokens[key_ps.pos + 1]!.val := by
          rw [getElem!_pos]
        rw [this, h_scalar]

      -- Compose all three regions
      rw [flowBracketBalance_compose tokens original_pos key_ps.pos (key_ps.pos + 2) (by omega) (by omega),
          flowBracketBalance_compose tokens key_ps.pos (key_ps.pos + 1) (key_ps.pos + 2) (by omega) (by omega)]
      simp [h_bal_to_value, h_value_single, h_scalar_single]

    -- Construct witness by computing what parseFlowMappingValue actually returns
    -- (not pre-defining val_ps, to avoid nodePositions mismatch)

    -- Setup for parseNode computation
    let ps_path := { key_ps with currentPath := savedPath.push (.key keyContent) }
    have h_ps_path_tok : ps_path.tokens = key_ps.tokens := rfl
    have h_ps_path_pos : ps_path.pos = key_ps.pos := rfl

    have h_ps_path_peek : ps_path.peek? = some .value := by
      have : ps_path.peek? = key_ps.peek? := by
        unfold ParseState.peek?
        simp [ps_path]
      rw [this, h_value_peek]

    have h_ps_path_adv_tok : ps_path.advance.tokens = key_ps.advance.tokens := by
      simp [ParseState.advance, ps_path]
    have h_ps_path_adv_pos : ps_path.advance.pos = key_ps.advance.pos := by
      simp [ParseState.advance, ps_path]

    have h_ps_path_adv_peek : ps_path.advance.peek? = some (.scalar c s) := by
      unfold ParseState.peek?
      rw [h_ps_path_adv_tok, h_ps_path_adv_pos]
      simp [ParseState.advance]
      constructor
      · rw [h_tok]; omega
      · rw [h_tok]; exact h_scalar

    obtain ⟨m', h_m_eq⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩

    -- Use parseNode_scalar_fields to get what parseNode returns
    have h_scalar_fields := parseNode_scalar_fields ps_path.advance c s (m' + 1) h_ps_path_adv_peek (by omega)
    -- Extract the parts we need
    have ⟨pn_val, pn_ps, h_pn_eq_full⟩ := h_scalar_fields
    have h_pn_eq := h_pn_eq_full.1
    have h_pn_val_eq := h_pn_eq_full.2.1
    have h_pn_pos_eq := h_pn_eq_full.2.2.1
    have h_pn_tok_eq := h_pn_eq_full.2.2.2.1
    have h_pn_anc_eq := h_pn_eq_full.2.2.2.2.1
    have h_pn_tagh_eq := h_pn_eq_full.2.2.2.2.2.1
    have h_pn_tp_eq := h_pn_eq_full.2.2.2.2.2.2

    -- The witness is (pn_val, { pn_ps with currentPath := savedPath })
    refine ⟨pn_val, { pn_ps with currentPath := savedPath }, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

    -- (1) parseFlowMappingValue key_ps m savedPath keyContent = .ok (pn_val, { pn_ps with currentPath := savedPath })
    · -- Systematic unfolding of parseFlowMappingValue
      unfold parseFlowMappingValue

      -- Use properties already established
      have h_ps_path_peek' : ps_path.peek? = some .value := h_ps_path_peek
      have h_trykey : ps_path.tryConsume .key = (false, ps_path) := by
        unfold ParseState.tryConsume
        rw [h_ps_path_peek']
        simp [beq_iff_eq]
      have h_tryval : ps_path.tryConsume .value = (true, ps_path.advance) := by
        unfold ParseState.tryConsume
        rw [h_ps_path_peek']
        simp

      -- Unfold the do-block
      simp only [Bind.bind, Except.bind]
      rw [h_trykey]
      simp
      rw [h_tryval]
      simp only [ite_true]
      rw [h_ps_path_adv_peek]
      simp

      -- parseNode is called on ps_path.advance with fuel m
      rw [h_m_eq, h_pn_eq]

    -- Now prove the remaining 6 properties about { pn_ps with currentPath := savedPath }

    -- (2) original_pos < { pn_ps with currentPath := savedPath }.pos
    · simp only [h_pn_pos_eq, h_ps_path_adv_pos]
      show ps_path.advance.pos + 1 > original_pos
      calc ps_path.advance.pos + 1
        = key_ps.advance.pos + 1 := by simp [ParseState.advance, ps_path]
        _ = (key_ps.pos + 1) + 1 := rfl
        _ = key_ps.pos + 2 := by omega
        _ > original_pos := h_final_gt

    -- (3) { pn_ps with currentPath := savedPath }.pos ≤ endPos
    · simp only [h_pn_pos_eq, h_ps_path_adv_pos]
      show ps_path.advance.pos + 1 ≤ endPos
      have : ps_path.advance.pos + 1 = key_ps.pos + 2 := by simp [ParseState.advance, ps_path]
      rw [this]; exact h_final_le

    -- (4) { pn_ps with currentPath := savedPath }.tokens = tokens
    · simp only [h_pn_tok_eq, h_ps_path_adv_tok]
      calc ps_path.advance.tokens
        = key_ps.advance.tokens := by simp [ParseState.advance, ps_path]
        _ = key_ps.tokens := rfl
        _ = tokens := h_tok

    -- (5) { pn_ps with currentPath := savedPath }.trackPositions = key_ps.trackPositions
    · simp only [h_pn_tp_eq]
      show ps_path.advance.advance.trackPositions = key_ps.trackPositions
      simp [ParseState.advance, ps_path]

    -- (6) { pn_ps with currentPath := savedPath }.peek? = some .flowEntry ∨
    --     ({ pn_ps with currentPath := savedPath }.peek? = some .flowMappingEnd ∧ { pn_ps with currentPath := savedPath }.pos = endPos)
    · unfold ParseState.peek?
      simp only [h_pn_tok_eq, h_ps_path_adv_tok, h_pn_pos_eq, h_ps_path_adv_pos]
      -- Now goal is: (if key_ps.advance.pos + 1 < key_ps.advance.tokens.size ...) = ...
      have h_adv_pos : key_ps.advance.pos + 1 = key_ps.pos + 2 := by simp [ParseState.advance]
      have h_adv_tok : key_ps.advance.tokens = tokens := by simp [h_tok]
      simp only [h_adv_tok, h_adv_pos]
      rw [if_pos (by omega : key_ps.pos + 2 < tokens.size)]
      rcases h_succ_peek with h_fe | ⟨h_me, h_eq⟩
      · left; simp [h_fe]
      · right; constructor
        · simp [h_me]
        · exact h_eq

    -- (7) flowBracketBalance tokens original_pos { pn_ps with currentPath := savedPath }.pos = 0
    · simp only [h_pn_pos_eq, h_ps_path_adv_pos]
      show flowBracketBalance tokens original_pos (ps_path.advance.pos + 1) = 0
      have : ps_path.advance.pos + 1 = key_ps.pos + 2 := by simp [ParseState.advance, ps_path]
      rw [this]; exact h_final_bal

  · -- flowSequenceStart value: parseNode → [ → loop → ] → advances past ]
    -- Use MapBodyProps.value_bracket_succ to find matching ] and FE/mapEnd after
    have h_bracket : tokens[key_ps.pos + 1]!.val = .flowSequenceStart ∨
                     tokens[key_ps.pos + 1]!.val = .flowMappingStart := Or.inl h_fss
    have h_bs_ps : body_start ≤ key_ps.pos := by omega
    have ⟨j, h_j_gt, h_j_lt, h_j_match, h_j_bal, h_j_succ_bound, h_j_succ_tok⟩ :=
      h_mbp.value_bracket_succ key_ps.pos h_bs_ps h_pos h_depth h_value_tok h_bracket

    -- Extract bracket info
    have ⟨h_fss_match, h_j_end⟩ : tokens[key_ps.pos + 1]!.val = .flowSequenceStart ∧
                                    tokens[j]!.val = .flowSequenceEnd := by
      rcases h_j_match with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
      · rw [h_fss] at h1; cases h1

    -- Use FlowSubrangesOk and IH to show parseNode succeeds on nested [...]
    -- Strategy: Similar to parseNode_flowSeqStart_in_seq (lines 5566-5860)
    --   1. Establish span bound: j - (key_ps.pos + 2) ≤ span_bound
    --   2. Apply ih_seq to get ParseNodeFlowSeqOk for inner body
    --   3. Unfold parseFlowMappingValue:
    --      - Update path, tryConsume .key (fails), tryConsume .value (succeeds)
    --      - Call parseNode ps_after_value m
    --   4. Unfold parseNode:
    --      - Skip alias, parseNodeProperties returns ({}, ps_after_value)
    --      - parseNodeContent matches flowSequenceStart
    --      - parseFlowSequence → parseFlowSequenceLoop (use loop theorem with ih_seq)
    --      - applyNodeFinalization wraps result
    --   5. Path restoration gives final witness
    --   6. Balance: compose [original_pos, key_ps.pos], [key_ps.pos, key_ps.pos+1] (.value),
    --               [key_ps.pos+1, j+1] (bracket pair), all = 0
    have h_j_bound : j < tokens.size := by omega
    have h_span : j - (key_ps.pos + 2) ≤ span_bound := by
      -- j < endPos, key_ps.pos ≥ body_start
      -- So j - (key_ps.pos + 2) < endPos - body_start ≤ span_bound + 1
      -- Therefore j - (key_ps.pos + 2) ≤ span_bound (since for Nat, x < n+1 ↔ x ≤ n)
      omega
    have h_inner_seq : ParseNodeFlowSeqOk tokens j (4 * tokens.size + 4) (key_ps.pos + 2) :=
      ih_seq j (key_ps.pos + 2) (4 * tokens.size + 4)
        h_j_bound (by omega) h_span h_j_end h_j_bal (by omega)

    -- Witness construction parallel to parseNode_flowSeqStart_in_seq (lines 5641-5927)
    -- Key difference: we prove parseFlowMappingValue instead of parseNode directly
    --
    -- Structure (with line references to template):
    -- 1. parseFlowMappingValue unfolds to:
    --    a. Path update: ps_path := { key_ps with currentPath := savedPath.push (.key keyContent) }
    --    b. tryConsume .key: returns (false, ps_path) since peek? = .value
    --    c. tryConsume .value: returns (true, ps_path.advance)
    --    d. Since consumed ∧ peek? = flowSequenceStart (not flowEntry/flowMappingEnd/none),
    --       parseNode is called on ps_path.advance with fuel m
    --
    -- 2. parseNode ps_path.advance m follows template (lines 5714-5895):
    --    - Fuel: m = m'+1 = m''+1+1 where m'' ≥ 4*N+4
    --    - Not alias: peek? = flowSequenceStart (lines 5726-5728)
    --    - parseNodeProperties: returns ({}, ps_path.advance) [has sorry in template]
    --    - validateNodeProps: succeeds (lines 5762-5778)
    --    - parseNodeContent: dispatches to parseFlowSequence (lines 5786-5802)
    --
    -- 3. parseFlowSequence ps_path.advance (m''+1) (lines 5806-5895):
    --    - Advances to ps_path.advance.advance (= key_ps.pos + 2)
    --    - Calls parseFlowSequenceLoop on inner body [key_ps.pos+2, j)
    --    - Uses h_inner_seq via loop theorem (lines 5838-5867)
    --    - Returns (.sequence .flow items, ps_at_j.advance) where ps_at_j.pos = j
    --
    -- 4. applyNodeFinalization wraps result (lines 5898-5901)
    --
    -- 5. Path restoration: { result.snd with currentPath := savedPath }
    --
    -- 6. Witness properties (lines 5903-5927):
    --    - pos > original_pos: j + 1 > key_ps.pos > original_pos
    --    - pos ≤ endPos: j + 1 ≤ endPos from h_j_succ_bound
    --    - tokens/trackPositions preserved: applyNodeFinalization properties
    --    - peek? postcondition: use h_j_succ_tok for tokens[j+1]
    --    - bracket balance = 0: compose [original_pos, key_ps.pos] + [key_ps.pos, key_ps.pos+1] (.value)
    --                                  + [key_ps.pos+1, j+1] (bracket pair)
    --
    -- Setup ps_path for parseFlowMappingValue
    let ps_path := { key_ps with currentPath := savedPath.push (.key keyContent) }

    have h_ps_path_tok : ps_path.tokens = key_ps.tokens := rfl
    have h_ps_path_pos : ps_path.pos = key_ps.pos := rfl

    have h_ps_path_peek : ps_path.peek? = some .value := by
      have : ps_path.peek? = key_ps.peek? := by unfold ParseState.peek?; simp [ps_path]
      rw [this, h_value_peek]

    have h_ps_path_adv_tok : ps_path.advance.tokens = key_ps.advance.tokens := by
      simp [ParseState.advance, ps_path]
    have h_ps_path_adv_pos : ps_path.advance.pos = key_ps.advance.pos := by
      simp [ParseState.advance, ps_path]

    have h_ps_path_adv_peek : ps_path.advance.peek? = some .flowSequenceStart := by
      unfold ParseState.peek?
      rw [h_ps_path_adv_tok, h_ps_path_adv_pos]
      simp [ParseState.advance, h_tok]
      constructor
      · omega
      · exact h_fss

    -- Fuel decomposition: m = m'+1 = m''+1+1
    obtain ⟨m', h_m'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
    obtain ⟨m'', h_m''⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    have h_m''_fuel : 4 * tokens.size + 4 ≤ m'' := by omega

    -- Unfold parseFlowMappingValue and show tryConsume behavior
    have h_trykey : ps_path.tryConsume .key = (false, ps_path) := by
      unfold ParseState.tryConsume
      rw [h_ps_path_peek]
      simp [beq_iff_eq]

    have h_tryval : ps_path.tryConsume .value = (true, ps_path.advance) := by
      unfold ParseState.tryConsume
      rw [h_ps_path_peek]
      simp

    -- Apply parseNode_flowSeqStart_in_seq to get parseNode result
    -- Need to establish preconditions for ps_path.advance
    have h_adv_tok : ps_path.advance.tokens = tokens := by
      simp [ParseState.advance, ps_path, h_tok]

    have h_adv_pos_bound : ps_path.advance.pos < endPos := by
      simp [ParseState.advance, ps_path]
      omega

    have h_adv_bs : body_start ≤ ps_path.advance.pos := by
      simp [ParseState.advance, ps_path]
      omega

    have h_adv_depth : flowBracketBalance tokens body_start ps_path.advance.pos = 0 := by
      simp [ParseState.advance, ps_path]
      -- Balance from body_start to key_ps.pos+1
      -- = balance[body_start, key_ps.pos] + balance[key_ps.pos, key_ps.pos+1]
      have h_compose := flowBracketBalance_compose tokens body_start key_ps.pos (key_ps.pos + 1)
        (by omega) (by omega)
      rw [h_depth] at h_compose
      -- Balance for .value token is 0
      have h_value_delta : flowBracketBalance tokens key_ps.pos (key_ps.pos + 1) = 0 := by
        rw [flowBracketBalance_single tokens key_ps.pos (by omega)]
        show flowBracketDelta tokens.toList[key_ps.pos].val = 0
        simp only [flowBracketDelta]
        have h_bound : key_ps.pos < tokens.size := by omega
        have h1 : tokens.toList[key_ps.pos].val = (tokens[key_ps.pos]'h_bound).val := rfl
        have h2 : (tokens[key_ps.pos]'h_bound).val = tokens[key_ps.pos]!.val := by rw [getElem!_pos]
        rw [h1, h2, h_value_tok]
      simp [h_value_delta] at h_compose
      exact h_compose

    -- We'll construct a witness based on what we know:
    -- - parseNode ps_path.advance (m'+1) should return a sequence value
    -- - The final position should be j+1
    -- - After restoring path, we have the witness for parseFlowMappingValue

    -- Construct witness directly
    -- We know: j is the matching ], j+1 is the position after ]
    -- The witness will be: (some_sequence_value, state_at_j_plus_1_with_savedPath)

    -- For now, use an abstract witness since the proof requires unfolding
    -- parseNodeProperties with forIn behavior (has sorries in template)

    have h_witness : ∃ seq_val ps_result,
        parseNode ps_path.advance (m' + 1) = .ok (seq_val, ps_result) ∧
        ps_result.pos = j + 1 ∧
        ps_result.tokens = tokens ∧
        ps_result.trackPositions = ps_path.advance.trackPositions ∧
        (ps_result.peek? = some .flowEntry ∨
         ps_result.peek? = some .flowMappingEnd ∧ ps_result.pos = endPos) := by
      -- This requires the full parseNode unfolding with parseNodeProperties sorries
      sorry

    obtain ⟨seq_val, ps_result, h_pn_eq, h_result_pos, h_result_tok, h_result_tp, h_result_peek⟩ := h_witness

    -- Build final witness with path restoration
    let final_ps := { ps_result with currentPath := savedPath }
    refine ⟨seq_val, final_ps, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

    -- (1) parseFlowMappingValue key_ps m savedPath keyContent = .ok (seq_val, final_ps)
    · unfold parseFlowMappingValue
      simp only [Bind.bind, Except.bind]
      rw [h_trykey]; simp
      rw [h_tryval]; simp only [ite_true]
      -- Now peek? = flowSequenceStart, which doesn't match flowEntry/flowMappingEnd/none
      rw [h_ps_path_adv_peek]
      simp
      subst h_m'
      rw [h_pn_eq]

    -- (2) original_pos < final_ps.pos
    · simp [final_ps, h_result_pos]
      omega

    -- (3) final_ps.pos ≤ endPos
    · simp [final_ps, h_result_pos]
      exact h_j_succ_bound

    -- (4) final_ps.tokens = tokens
    · simp [final_ps, h_result_tok]

    -- (5) final_ps.trackPositions = key_ps.trackPositions
    · simp [final_ps, h_result_tp]
      simp [ParseState.advance, ps_path]

    -- (6) peek? postcondition
    · simp [final_ps]
      -- ps_result.peek? already satisfies the postcondition from h_result_peek
      -- We just need to verify it's preserved through the path change
      exact h_result_peek

    -- (7) bracket balance = 0
    · simp [final_ps, h_result_pos]
      -- Compose: [original_pos, key_ps.pos] + [key_ps.pos, key_ps.pos+1] + [key_ps.pos+1, j+1]
      have h_compose1 := flowBracketBalance_compose tokens original_pos key_ps.pos (j + 1)
        (by omega) (by omega)
      rw [h_compose1]
      have h_bal_to_value : flowBracketBalance tokens original_pos key_ps.pos = 0 := by
        have := flowBracketBalance_compose tokens body_start original_pos key_ps.pos
          (by omega) (by omega)
        rw [h_depth_orig, h_depth] at this
        omega
      simp [h_bal_to_value]
      -- Balance from key_ps.pos to j+1
      have h_compose2 := flowBracketBalance_compose tokens key_ps.pos (key_ps.pos + 1) (j + 1)
        (by omega) (by omega)
      rw [h_compose2]
      -- Balance for .value token is 0
      have h_value_delta : flowBracketBalance tokens key_ps.pos (key_ps.pos + 1) = 0 := by
        rw [flowBracketBalance_single tokens key_ps.pos (by omega)]
        show flowBracketDelta tokens.toList[key_ps.pos].val = 0
        simp only [flowBracketDelta]
        have h_bound : key_ps.pos < tokens.size := by omega
        have h1 : tokens.toList[key_ps.pos].val = (tokens[key_ps.pos]'h_bound).val := rfl
        have h2 : (tokens[key_ps.pos]'h_bound).val = tokens[key_ps.pos]!.val := by rw [getElem!_pos]
        rw [h1, h2, h_value_tok]
      simp [h_value_delta]
      -- Balance from key_ps.pos+1 to j+1 (bracket pair)
      sorry  -- Bracket pair [key_ps.pos+1, j+1) balances to 0

  · -- flowMappingStart value: symmetric with above
    have h_bracket : tokens[key_ps.pos + 1]!.val = .flowSequenceStart ∨
                     tokens[key_ps.pos + 1]!.val = .flowMappingStart := Or.inr h_fms
    have ⟨j, h_j_gt, h_j_lt, h_j_match, h_j_bal, h_j_succ_bound, h_j_succ_tok⟩ :=
      h_mbp.value_bracket_succ key_ps.pos (by omega) h_pos h_depth h_value_tok h_bracket

    have ⟨h_fms_match, h_j_end⟩ : tokens[key_ps.pos + 1]!.val = .flowMappingStart ∧
                                    tokens[j]!.val = .flowMappingEnd := by
      rcases h_j_match with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h_fms] at h1; cases h1
      · exact ⟨h1, h2⟩

    -- Use FlowSubrangesOk and IH to show parseNode succeeds on nested {...}
    -- Strategy: Parallel to flowSequenceStart case above
    --   1. Establish span bound: j - (key_ps.pos + 2) ≤ span_bound
    --   2. Apply ih_map to get ParseEntryFlowMapOk for inner body
    --   3. Unfold parseFlowMappingValue → parseNode → parseNodeContent
    --   4. parseFlowMapping → parseFlowMappingLoop (use loop theorem with ih_map)
    --   5. applyNodeFinalization + path restoration
    --   6. Balance composition as above
    have h_j_bound : j < tokens.size := by omega
    have h_span : j - (key_ps.pos + 2) ≤ span_bound := by
      -- j < endPos, key_ps.pos ≥ body_start
      -- So j - (key_ps.pos + 2) < endPos - body_start ≤ span_bound + 1
      -- Therefore j - (key_ps.pos + 2) ≤ span_bound (since for Nat, x < n+1 ↔ x ≤ n)
      omega
    have h_inner_map : ParseEntryFlowMapOk tokens j (4 * tokens.size + 4) (key_ps.pos + 2) :=
      ih_map j (key_ps.pos + 2) (4 * tokens.size + 4)
        h_j_bound (by omega) h_span h_j_end h_j_bal (by omega)
    sorry  -- ~100 lines: detailed unfolding parallel to parseNode_flowMapStart_in_seq

/-- Scalar case: parseNode succeeds on a scalar token in a flow sequence body. -/
theorem parseNode_scalar_in_seq
    (tokens : Array (Positioned YamlToken))
    (endPos body_start : Nat)
    (h_endPos_bound : endPos < tokens.size)
    (h_sbp : SeqBodyProps tokens body_start endPos)
    (ps : ParseState) (m : Nat)
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_pos : ps.pos < endPos)
    (h_bs : body_start ≤ ps.pos)
    (h_depth : flowBracketBalance tokens body_start ps.pos = 0)
    (c : String) (sc : ScalarStyle)
    (h_scalar : ps.peek? = some (.scalar c sc)) :
    ∃ val ps', parseNode ps m = .ok (val, ps') ∧
              ps'.pos > ps.pos ∧ ps'.pos ≤ endPos ∧
              ps'.tokens = tokens ∧
              ps'.trackPositions = ps.trackPositions ∧
              (ps'.peek? = some .flowEntry ∨
               (ps'.peek? = some .flowSequenceEnd ∧ ps'.pos = endPos)) ∧
              flowBracketBalance tokens ps.pos ps'.pos = 0 := by
  -- Extract position-level info from peek
  have ⟨h_pos_bound, h_peek_val⟩ := peek_some_val h_scalar
  have h_scalar_tok : ∃ c₁ s₁, tokens[ps.pos]!.val = .scalar c₁ s₁ := by
    rw [h_tok] at h_peek_val; exact ⟨c, sc, h_peek_val⟩
  -- Scalar successor from SeqBodyProps
  obtain ⟨h_succ_le, h_succ_tok⟩ := h_sbp.scalar_succ ps.pos h_bs h_pos h_depth h_scalar_tok
  -- Fuel > 0
  obtain ⟨m', rfl⟩ : ∃ k, m = k + 1 := ⟨m - 1, by omega⟩
  -- parseNodeProperties is noop on scalar peek
  have h_np : parseNodeProperties ps = .ok ({}, ps) := by
    exact parseNodeProperties_skip ps (by rw [h_scalar]; trivial)
  -- Compute parseNode result
  have h_node_eq : parseNode ps (m' + 1) =
      .ok (applyNodeFinalization
        (.scalar { content := c, style := sc, tag := none, anchor := none })
        ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
    unfold parseNode
    simp only [bind, Except.bind, pure, Except.pure]
    split
    · rename_i h_alias; rw [h_scalar] at h_alias; cases h_alias
    · rw [h_np]; simp
      unfold validateNodeProps
      rw [h_scalar]; simp only [pure, Except.pure, bind, Except.bind]
      unfold parseNodeContent
      rw [h_scalar]; simp
  -- Build the existential witness
  refine ⟨(.scalar { content := c, style := sc, tag := none, anchor := none }),
          (applyNodeFinalization
            (.scalar { content := c, style := sc, tag := none, anchor := none })
            ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2,
          h_node_eq, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ps'.pos > ps.pos
    show (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos > ps.pos
    rw [applyNodeFinalization_pos]; simp [ParseState.advance]
  · -- ps'.pos ≤ endPos
    show (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos ≤ endPos
    rw [applyNodeFinalization_pos]; simp [ParseState.advance]; exact h_succ_le
  · -- tokens preserved
    show (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.tokens = tokens
    rw [applyNodeFinalization_tokens, ParseState.advance_tokens, h_tok]
  · -- trackPositions preserved
    show (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.trackPositions = ps.trackPositions
    rw [applyNodeFinalization_trackPositions]; simp [ParseState.advance]
  · -- peek' = FE or seqEnd at endPos
    have h_ps'_pos : (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos = ps.pos + 1 := by
      rw [applyNodeFinalization_pos]; simp [ParseState.advance]
    have h_ps'_tok : (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.tokens = tokens := by
      rw [applyNodeFinalization_tokens, ParseState.advance_tokens, h_tok]
    rcases h_succ_tok with h_fe | ⟨h_se, h_eq⟩
    · left
      apply peek_of_pos_val h_ps'_pos (by rw [h_ps'_tok]; omega)
      rw [h_ps'_tok]; exact h_fe
    · right
      constructor
      · apply peek_of_pos_val h_ps'_pos (by rw [h_ps'_tok]; omega)
        rw [h_ps'_tok]; exact h_se
      · rw [h_ps'_pos]; exact h_eq
  · -- bracket balance 0
    have h_ps'_pos : (applyNodeFinalization
      (.scalar { content := c, style := sc, tag := none, anchor := none })
      ps.advance {} (ps.peekPos?.getD { offset := 0, line := 0, col := 0 })).2.pos = ps.pos + 1 := by
      rw [applyNodeFinalization_pos]; simp [ParseState.advance]
    rw [h_ps'_pos]
    have h_ps_bound : ps.pos < tokens.size := by rw [←h_tok]; exact h_pos_bound
    have h_list_bound : ps.pos < tokens.toList.length := by show ps.pos < tokens.size; exact h_ps_bound
    rw [flowBracketBalance_single tokens ps.pos h_list_bound]
    obtain ⟨c₁, s₁, hcs⟩ := h_scalar_tok
    -- Show flowBracketDelta for scalar is 0
    have h_eq : (tokens.toList[ps.pos]'h_list_bound).val = .scalar c₁ s₁ := by
      show (tokens[ps.pos]'h_ps_bound).val = .scalar c₁ s₁
      rw [← getElem!_pos tokens ps.pos h_ps_bound]; exact hcs
    rw [h_eq]
    rfl

/-- Nested flowSequenceStart case: uses IH for the inner body. -/
theorem parseNode_flowSeqStart_in_seq
    (tokens : Array (Positioned YamlToken))
    (endPos body_start : Nat)
    (span_bound : Nat)
    (h_endPos_bound : endPos < tokens.size)
    (h_span_bound : endPos - body_start ≤ span_bound + 1)
    (h_sub : FlowSubrangesOk tokens)
    (h_sbp : SeqBodyProps tokens body_start endPos)
    -- IH matching flow_parser_ok_of_structure signature
    (ih_seq : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowSequenceEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseNodeFlowSeqOk tokens j fuel lo)
    (ih_map : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowMappingEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseEntryFlowMapOk tokens j fuel lo)
    (ps : ParseState) (m : Nat)
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_m_fuel : 4 * tokens.size + 6 ≤ m)
    (h_pos : ps.pos < endPos)
    (h_bs : body_start ≤ ps.pos)
    (h_depth : flowBracketBalance tokens body_start ps.pos = 0)
    (h_fss : ps.peek? = some .flowSequenceStart) :
    ∃ val ps', parseNode ps m = .ok (val, ps') ∧
              ps'.pos > ps.pos ∧ ps'.pos ≤ endPos ∧
              ps'.tokens = tokens ∧
              ps'.trackPositions = ps.trackPositions ∧
              (ps'.peek? = some .flowEntry ∨
               (ps'.peek? = some .flowSequenceEnd ∧ ps'.pos = endPos)) ∧
              flowBracketBalance tokens ps.pos ps'.pos = 0 := by
  -- Strategy: parseNode → parseNodeProperties → validateNodeProps → parseNodeContent
  -- → parseFlowSequence → parseFlowSequenceLoop (using IH) → applyNodeFinalization

  -- Step 1: Establish ps.pos bound and token value
  have h_ps_bound : ps.pos < tokens.size := by
    subst h_tok; omega
  have h_fss_val : tokens[ps.pos]!.val = .flowSequenceStart := by
    subst h_tok
    unfold ParseState.peek? at h_fss
    simp only [h_ps_bound, ↓reduceIte] at h_fss
    injection h_fss

  -- Step 2: Find matching ] using SeqBodyProps.bracket_seq
  have ⟨j, h_j_gt, h_j_lt, h_j_tok, h_j_bal, h_j_succ, h_j_after⟩ :=
    h_sbp.bracket_seq ps.pos (by omega) h_pos h_depth h_fss_val

  -- j is the matching ] position, with balance (ps.pos+1) j = 0
  -- Now j < endPos and tokens[j] = flowSequenceEnd
  have h_j_bound : j < tokens.size := by omega

  -- Step 3: Compute span for IH
  have h_span : j - (ps.pos + 1) ≤ span_bound := by
    -- j < endPos and ps.pos ≥ body_start
    -- So: j - (ps.pos + 1) < j - body_start < endPos - body_start ≤ span_bound + 1
    -- Therefore: j - (ps.pos + 1) ≤ span_bound (since for Nat, x < n+1 ↔ x ≤ n)
    omega

  -- Step 4: Apply ih_seq to inner body [ps.pos+1, j)
  have h_inner_pn : ParseNodeFlowSeqOk tokens j (4 * tokens.size + 4) (ps.pos + 1) :=
    ih_seq j (ps.pos + 1) (4 * tokens.size + 4)
      h_j_bound (by omega) h_span h_j_tok h_j_bal (by omega)

  -- Step 5: Fuel decomposition m = m'+1 = m''+1+1
  obtain ⟨m', h_m'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
  obtain ⟨m'', h_m''⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩

  -- m'' ≥ 4*N+4 for loop theorem
  have h_m''_fuel : 4 * tokens.size + 4 ≤ m'' := by omega

  -- Step 6: Unfold parseNode (m = m''+1+1)
  subst h_m' h_m''
  unfold parseNode

  -- Show not alias case: h_fss says peek? = some .flowSequenceStart
  have h_not_alias : ∀ name, ps.peek? ≠ some (.alias name) := by
    intro name h_contra
    rw [h_fss] at h_contra
    cases h_contra

  -- Split on alias case (will be false)
  split
  · rename_i h_alias_case
    exfalso
    exact h_not_alias _ h_alias_case

  -- Now in the non-alias branch: do-block with parseNodeProperties
  simp only [Bind.bind, Except.bind]

  -- Step 7: parseNodeProperties result
  -- For flowSequenceStart with no anchor/tag, returns ({}, ps)
  generalize h_pnp : parseNodeProperties ps = pnp_result
  cases pnp_result with
  | error e =>
    -- parseNodeProperties is a for-loop that breaks on non-anchor/non-tag tokens
    -- The only error path is undeclared tag handle (line 221 in TokenParser.lean)
    -- Since peek? = flowSequenceStart (not .tag), we never enter the tag branch
    -- Therefore parseNodeProperties returns .ok, not .error
    -- This requires a dedicated lemma about forIn behavior on flowSequenceStart
    exfalso
    sorry  -- Need: parseNodeProperties with peek? = flowSequenceStart returns .ok (~5 lines)
  | ok res =>
    obtain ⟨props, ps_after_props⟩ := res
    simp

    -- Show ps_after_props = ps (parseNodeProperties doesn't advance for flowSequenceStart)
    have h_ps_props_eq : ps_after_props = ps := by
      -- parseNodeProperties loops checking for anchor/tag
      -- Since peek? = flowSequenceStart (neither anchor nor tag), loop breaks with done
      -- done returns (props, ps) without advancing
      sorry  -- Need forIn lemma: breaks on flowSequenceStart → ps unchanged

    have h_props_empty : props = {} := by
      -- parseNodeProperties starts with props = {}, advances only on anchor/tag
      -- Since we break immediately on flowSequenceStart, props stays {}
      sorry  -- Need forIn lemma: breaks immediately → props = initial value = {}

    -- Step 8: validateNodeProps with prePropPos = ps.pos
    generalize h_saved_pos : ps.pos = prePropPos
    generalize h_vnp : validateNodeProps ps_after_props prePropPos props = vnp_result
    cases vnp_result with
    | error e =>
      -- validateNodeProps checks: (1) block alignment (only for blockSequenceStart/blockMappingStart)
      -- (2) duplicate anchors (only if props.hadDuplicateAnchor = true)
      -- We have: peek? = flowSequenceStart (flow, not block), props = {} (no duplicate)
      -- Therefore validateNodeProps cannot fail
      exfalso
      subst h_ps_props_eq h_props_empty h_saved_pos
      unfold validateNodeProps at h_vnp
      -- After unfolding, peek? = flowSequenceStart means first check passes (not block)
      simp only [h_fss] at h_vnp
      -- h_vnp now says: pure PUnit.unit = Except.error e, which is absurd
      -- pure PUnit.unit = Except.ok PUnit.unit ≠ Except.error e
      cases h_vnp
    | ok _ =>
      simp

      -- Step 9: parseNodeContent dispatches on peek?
      have h_props_peek : ps_after_props.peek? = some .flowSequenceStart := by
        subst h_ps_props_eq; exact h_fss

      -- Step 10: Show parseNodeContent = parseFlowSequence
      have h_pnc_eq : parseNodeContent ps_after_props (m'' + 1) props =
                      parseFlowSequence ps_after_props (m'' + 1) := by
        unfold parseNodeContent
        simp only [h_props_peek]

      -- Step 11: Show parseFlowSequence succeeds
      -- Strategy: unfold, invoke loop theorem, check closing ]

      have h_ps_props_tok : ps_after_props.tokens = tokens := by
        subst h_ps_props_eq; exact h_tok

      -- Now show parseNodeContent = parseFlowSequence and it succeeds
      have h_pnc_pfs : parseNodeContent ps_after_props (m'' + 1) props =
                       parseFlowSequence ps_after_props (m'' + 1) := by
        unfold parseNodeContent
        subst h_ps_props_eq
        simp only [h_fss]

      -- Show parseFlowSequence succeeds and build witness
      -- Unfold parseFlowSequence: checks fuel, advances past [, calls loop, checks ]
      unfold parseFlowSequence at h_pnc_pfs

      -- After advance, we're at ps.pos + 1 (inner body start)
      have h_adv_tok : ps_after_props.advance.tokens = tokens := by
        subst h_ps_props_eq; exact h_tok

      have h_adv_pos : ps_after_props.advance.pos = ps.pos + 1 := by
        subst h_ps_props_eq h_tok
        simp [ParseState.advance]

      -- Construct loop preconditions and invoke loop theorem

      -- First, get SeqBodyProps for inner body [ps.pos+1, j)
      have h_inner_sbp : SeqBodyProps tokens (ps.pos + 1) j := by
        have := h_sub.seq (ps.pos + 1) j (by omega) h_j_bound h_j_tok h_j_bal
        exact this

      -- Use h_ps_props_eq to simplify
      have h_ps_props_tok_eq : ps_after_props.tokens = tokens := by
        rw [h_ps_props_eq]; exact h_tok
      have h_ps_props_bound : ps_after_props.pos < tokens.size := by
        rw [h_ps_props_eq]; exact h_ps_bound
      have h_ps_props_j_gt : ps_after_props.pos < j := by
        rw [h_ps_props_eq]; exact h_j_gt
      have h_inner_sbp' : SeqBodyProps tokens (ps_after_props.pos + 1) j := by
        rw [h_ps_props_eq]; exact h_inner_sbp

      -- Convert h_inner_pn to use ps_after_props.pos (keep same fuel value literally)
      have h_inner_pn' : ParseNodeFlowSeqOk tokens j (4 * tokens.size + 4) (ps_after_props.pos + 1) := by
        rw [h_ps_props_eq]; exact h_inner_pn

      -- Construct loop preconditions with literal fuel value
      have h_loop_precond := mk_loop_seq_preconditions
        tokens ps_after_props j (4 * tokens.size + 4)
        h_ps_props_tok_eq h_ps_props_bound h_ps_props_j_gt
        h_j_bound h_j_tok h_inner_sbp' h_inner_pn'
        (by omega)

      -- Invoke parseFlowSequenceLoop_emitter_ok with 4*N+4 fuel
      have ⟨items, ps_at_j, h_loop_ok, h_peek_j, h_at_j_pos, h_tok_j_eq, h_tp_j⟩ :=
        parseFlowSequenceLoop_emitter_ok (4 * tokens.size + 4)
          ps_after_props.advance #[] j (ps_after_props.pos + 1)
          (by rw [ParseState.advance_tokens, h_ps_props_tok_eq]; exact h_loop_precond.h_pn)
          h_loop_precond.h_fuel h_loop_precond.h_pos
          h_loop_precond.h_end_pos h_loop_precond.h_end_tok h_loop_precond.h_at_end
          h_loop_precond.h_entry h_loop_precond.h_content_start h_loop_precond.h_after_fe
          h_loop_precond.h_bal h_loop_precond.h_bs

      -- Extract key properties from loop result
      have h_at_j_tok : ps_at_j.tokens = tokens := by
        rw [h_tok_j_eq, ParseState.advance_tokens, h_ps_props_tok_eq]

      -- Step 12: Build witness
      -- Use fuel monotonicity to convert h_loop_ok from 4*N+4 fuel to m'' fuel
      have h_loop_ok_m'' : parseFlowSequenceLoop ps_after_props.advance m'' #[] =
                           .ok (items, ps_at_j) :=
        parseFlowSequenceLoop_fuel_mono
          ps_after_props.advance #[]
          (4 * tokens.size + 4) m''
          h_m''_fuel
          items ps_at_j
          h_loop_ok

      -- parseNodeContent succeeds (use h_pnc_pfs which already expanded parseFlowSequence)
      have h_pnc_ok : parseNodeContent ps_after_props (m'' + 1) props =
                      .ok (.sequence .flow items, ps_at_j.advance) := by
        rw [h_pnc_pfs]
        -- The goal is: (have ps := ps_after_props.advance; do ...)
        -- The have binding shadows ps with ps_after_props.advance
        -- Then the do-block calls parseFlowSequenceLoop ps m'' #[]
        -- We have h_loop_ok_m'': parseFlowSequenceLoop ps_after_props.advance m'' #[] = .ok (items, ps_at_j)
        show (have ps := ps_after_props.advance;
              do let ⟨items, ps⟩ ← parseFlowSequenceLoop ps m'' #[]
                 match ps.peek? with
                 | some .flowSequenceEnd => .ok (YamlValue.sequence .flow items, ps.advance)
                 | _ => .error (.expectedToken "']'" ps.currentLine none)) =
             .ok (YamlValue.sequence .flow items, ps_at_j.advance)
        -- Now unfold the have and substitute
        show (do let ⟨items', ps'⟩ ← parseFlowSequenceLoop ps_after_props.advance m'' #[]
                 match ps'.peek? with
                 | some .flowSequenceEnd => .ok (YamlValue.sequence .flow items', ps'.advance)
                 | _ => .error (.expectedToken "']'" ps'.currentLine none)) =
             .ok (YamlValue.sequence .flow items, ps_at_j.advance)
        rw [h_loop_ok_m'']
        -- Now we have: do let ⟨items', ps'⟩ ← .ok (items, ps_at_j); ...
        -- Simplify the bind
        simp only [Bind.bind, Except.bind]
        -- Now the match reduces: items' = items, ps' = ps_at_j
        rw [h_peek_j]

      -- Final witness construction
      -- Build existential witness using applyNodeFinalization result directly
      let nodeStartPos := ps.peekPos?.getD { offset := 0, line := 0, col := 0 }
      refine ⟨(applyNodeFinalization (.sequence .flow items) ps_at_j.advance props nodeStartPos).1,
              (applyNodeFinalization (.sequence .flow items) ps_at_j.advance props nodeStartPos).2,
              ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩

      -- (1) parseNode ps (m''+1+1) = .ok (val_final, ps_final)
      · -- The goal is the do-block body after alias split and bind simplification
        -- Step 1: Simplify pure () = .ok () and reduce the match
        simp only [pure, Except.pure]
        -- Step 2: Rewrite parseNodeContent using h_pnc_ok
        rw [h_pnc_ok]

      -- (2) prePropPos < ps_final.pos (i.e., ps.pos < ps_final.pos)
      · sorry  -- ps_final.pos = j + 1 > ps.pos

      -- (3) ps_final.pos ≤ endPos
      · sorry  -- ps_final.pos = j + 1 ≤ endPos

      -- (4) ps_final.tokens = tokens
      · sorry  -- applyNodeFinalization preserves tokens

      -- (5) ps_final.trackPositions = ps.trackPositions
      · sorry  -- applyNodeFinalization preserves trackPositions

      -- (6) peek? postcondition
      · sorry  -- Use h_j_after: tokens[j+1] determines peek? at position j+1

      -- (7) bracket balance = 0
      · sorry  -- Combine: [ps.pos, ps.pos+1) = +1, [ps.pos+1, j) = 0, [j, j+1) = -1

/-- Nested flowMappingStart case: uses IH for the inner body. -/
theorem parseNode_flowMapStart_in_seq
    (tokens : Array (Positioned YamlToken))
    (endPos body_start : Nat)
    (span_bound : Nat)
    (h_endPos_bound : endPos < tokens.size)
    (h_span_bound : endPos - body_start ≤ span_bound + 1)
    (h_sub : FlowSubrangesOk tokens)
    (h_sbp : SeqBodyProps tokens body_start endPos)
    -- IH matching flow_parser_ok_of_structure signature
    (ih_seq : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowSequenceEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseNodeFlowSeqOk tokens j fuel lo)
    (ih_map : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowMappingEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseEntryFlowMapOk tokens j fuel lo)
    (ps : ParseState) (m : Nat)
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_m_fuel : 4 * tokens.size + 6 ≤ m)
    (h_pos : ps.pos < endPos)
    (h_bs : body_start ≤ ps.pos)
    (h_depth : flowBracketBalance tokens body_start ps.pos = 0)
    (h_fms : ps.peek? = some .flowMappingStart) :
    ∃ val ps', parseNode ps m = .ok (val, ps') ∧
              ps'.pos > ps.pos ∧ ps'.pos ≤ endPos ∧
              ps'.tokens = tokens ∧
              ps'.trackPositions = ps.trackPositions ∧
              (ps'.peek? = some .flowEntry ∨
               (ps'.peek? = some .flowSequenceEnd ∧ ps'.pos = endPos)) ∧
              flowBracketBalance tokens ps.pos ps'.pos = 0 := by
  -- Strategy: Similar to parseNode_flowSeqStart_in_seq but for flow mappings
  -- parseNode → parseNodeProperties → validateNodeProps → parseNodeContent
  -- → parseFlowMapping → parseFlowMappingLoop (using IH) → applyNodeFinalization

  -- Step 1: Establish ps.pos bound and token value
  have h_ps_bound : ps.pos < tokens.size := by
    subst h_tok; omega
  have h_fms_val : tokens[ps.pos]!.val = .flowMappingStart := by
    subst h_tok
    unfold ParseState.peek? at h_fms
    simp only [h_ps_bound, ↓reduceIte] at h_fms
    injection h_fms

  -- Step 2: Find matching } using SeqBodyProps.bracket_map
  have ⟨j, h_j_gt, h_j_lt, h_j_tok, h_j_bal, h_j_succ, h_j_after⟩ :=
    h_sbp.bracket_map ps.pos (by omega) h_pos h_depth h_fms_val

  have h_j_bound : j < tokens.size := by omega

  -- Step 3: Compute span for IH
  have h_span : j - (ps.pos + 1) ≤ span_bound := by
    calc j - (ps.pos + 1)
        ≤ j - body_start      := by omega
      _ ≤ endPos - body_start := by omega
      _ ≤ span_bound          := by sorry  -- Need precondition: endPos - body_start ≤ span_bound

  -- Step 4: Apply ih_map to inner body [ps.pos+1, j)
  have h_inner_entry : ParseEntryFlowMapOk tokens j (4 * tokens.size + 4) (ps.pos + 1) :=
    ih_map j (ps.pos + 1) (4 * tokens.size + 4)
      h_j_bound (by omega) h_span h_j_tok h_j_bal (by omega)

  -- Remaining steps: parseNode chain, loop theorem, witness construction
  -- Structure parallel to parseNode_flowSeqStart_in_seq
  sorry

/-- Map body case: parseExplicitKey + parseFlowMappingValue in a flow mapping body.
    Uses IH for nested bracket structures in keys and values. -/
theorem parseEntry_in_flowMap
    (tokens : Array (Positioned YamlToken))
    (endPos body_start : Nat)
    (span_bound : Nat)
    (h_endPos_bound : endPos < tokens.size)
    (h_span_bound : endPos - body_start ≤ span_bound + 1)
    (h_sub : FlowSubrangesOk tokens)
    (h_mbp : MapBodyProps tokens body_start endPos)
    -- IH matching flow_parser_ok_of_structure signature
    (ih_seq : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowSequenceEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseNodeFlowSeqOk tokens j fuel lo)
    (ih_map : ∀ j lo fuel, j < tokens.size → lo ≤ j → j - lo ≤ span_bound →
              tokens[j]!.val = .flowMappingEnd →
              flowBracketBalance tokens lo j = 0 →
              4 * tokens.size + 4 ≤ fuel →
              ParseEntryFlowMapOk tokens j fuel lo)
    (ps : ParseState) (m : Nat)
    (h_tok : ps.tokens = tokens)
    (h_m_pos : 0 < m)
    (h_m_fuel : 4 * tokens.size + 6 ≤ m)
    (h_pos : ps.pos < endPos)
    (h_bs : body_start ≤ ps.pos)
    (h_depth : flowBracketBalance tokens body_start ps.pos = 0)
    (h_key : ps.peek? = some .key) :
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
          flowBracketBalance tokens ps.pos val_ps.pos = 0 := by
  -- Strategy: Sequential key → value parsing (unlike loop-based parseNode lemmas)
  -- 1. Advance past .key token
  -- 2. Parse key content (scalar/[/{) using IH for nested brackets
  -- 3. Result at .value token
  -- 4. Parse value content using IH for nested brackets
  -- 5. Construct nested existential witness

  -- Step 1: Establish ps.pos bound and token value
  have h_ps_bound : ps.pos < tokens.size := by
    subst h_tok; omega
  have h_key_val : tokens[ps.pos]!.val = .key := by
    subst h_tok
    unfold ParseState.peek? at h_key
    simp only [h_ps_bound, ↓reduceIte] at h_key
    injection h_key

  -- Step 2: After .key, content-start follows (from MapBodyProps.key_content)
  have ⟨h_key_content_bound, h_key_content⟩ :=
    h_mbp.key_content ps.pos (by omega) h_pos h_depth h_key_val

  -- ps.advance is at ps.pos + 1 (the key content)
  have h_after_key_pos : ps.advance.pos = ps.pos + 1 := by
    simp [ParseState.advance]

  have h_after_key_bound : ps.advance.pos < tokens.size := by
    rw [h_after_key_pos]; omega

  -- Step 4: Fuel decomposition m ≥ 4*N+6, sufficient for key and value parsing
  obtain ⟨m', h_m'⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩

  -- After key, we'll be at .value token from MapBodyProps
  -- Key content is at ps.advance (ps.pos + 1)

  -- Step 5: Case split on key content type
  -- parseExplicitKey dispatches: emptyNode if separator, else parseNode
  -- From MapBodyProps.key_content: isFlowContentStart at ps.pos + 1

  have h_after_key_tok : ps.advance.tokens = tokens := by
    simp [ParseState.advance]; exact h_tok

  -- Case split based on what isFlowContentStart allows: scalar, [, or {
  rcases h_key_content with ⟨c, s, h_scalar⟩ | h_fss | h_fms

  · -- Scalar key case: .key → scalar → .value → value_content → result
    -- Use MapBodyProps.key_scalar_value to show .value at ps.pos + 2
    have ⟨h_value_bound, h_value_tok⟩ :=
      h_mbp.key_scalar_value ps.pos (by omega) h_pos h_depth h_key_val ⟨c, s, h_scalar⟩

    -- Apply helper: parseExplicitKey on scalar
    have ⟨key_val, key_ps, h_key_ok, h_key_pos, h_key_tok, h_key_tp⟩ :=
      parseExplicitKey_scalar tokens ps.advance m h_after_key_tok (by omega) h_after_key_bound c s h_scalar

    -- Build witness
    refine ⟨key_val, key_ps, ?_, ?_, ?_, ?_, ?_, ?_⟩

    · -- parseExplicitKey result
      exact h_key_ok

    · -- key_ps.pos > ps.pos
      rw [h_key_pos]; omega

    · -- key_ps.pos ≤ endPos
      rw [h_key_pos]; omega

    · -- key_ps.tokens = tokens
      exact h_key_tok

    · -- key_ps.trackPositions = ps.trackPositions
      rw [h_key_tp]; subst h_tok; rfl

    · -- ∀ savedPath keyContent, parseFlowMappingValue succeeds
      intro savedPath keyContent

      -- Verify key_ps is at .value token
      have h_key_ps_pos_eq : key_ps.pos = ps.pos + 2 := by
        rw [h_key_pos, h_after_key_pos]

      have h_key_ps_value_tok : tokens[key_ps.pos]!.val = .value := by
        rw [h_key_ps_pos_eq]; exact h_value_tok

      have h_key_ps_value_peek : key_ps.peek? = some .value := by
        unfold ParseState.peek?
        rw [h_key_tok, if_pos (by rw [h_key_ps_pos_eq]; omega)]
        rw [h_key_ps_value_tok]

      -- Get value content info from MapBodyProps
      have h_depth_at_value : flowBracketBalance tokens body_start (ps.pos + 2) = 0 := by
        sorry  -- Balance preserved through .key and .scalar (non-bracket tokens)

      have ⟨h_val_content_bound, h_val_content⟩ :=
        h_mbp.value_content (ps.pos + 2) (by omega) (by omega) h_depth_at_value h_value_tok

      have h_val_content_bound' : key_ps.pos + 1 < endPos := by
        rw [h_key_ps_pos_eq]; exact h_val_content_bound

      have h_val_content' : isFlowContentStart tokens[key_ps.pos + 1]!.val := by
        rw [h_key_ps_pos_eq]; exact h_val_content

      -- Apply helper: parseFlowMappingValue at .value (pass ps.pos as original_pos)
      have h_depth_at_key_ps : flowBracketBalance tokens body_start key_ps.pos = 0 := by
        rw [h_key_ps_pos_eq]; exact h_depth_at_value

      have ⟨val_val, val_ps, h_val_ok, h_val_pos_gt, h_val_pos_le, h_val_tok_eq, h_val_tp, h_val_peek, h_val_bal⟩ :=
        (parseFlowMappingValue_ok tokens endPos body_start span_bound ps.pos key_ps m
          h_key_tok (by omega) h_m_fuel h_endPos_bound h_span_bound
          (by rw [h_key_ps_pos_eq]; omega)
          h_bs
          (by rw [h_key_ps_pos_eq]; omega)
          h_depth
          h_depth_at_key_ps h_key_ps_value_tok h_key_ps_value_peek
          h_val_content_bound' h_val_content'
          h_mbp h_sub ih_seq ih_map) savedPath keyContent

      refine ⟨val_val, val_ps, h_val_ok, h_val_pos_gt, h_val_pos_le, h_val_tok_eq, ?_, h_val_peek, h_val_bal⟩
      rw [h_val_tp, h_key_tp]; subst h_tok; rfl

  · -- Key is flowSequenceStart: .key → [ → ... → ] → .value → value_content → result
    -- Use MapBodyProps.key_bracket_value to find matching ] and .value after it
    have ⟨j, h_j_gt, h_j_lt, h_j_match, h_j_bal, h_j_value_bound, h_j_value_tok⟩ :=
      h_mbp.key_bracket_value ps.pos (by omega) h_pos h_depth h_key_val (Or.inl h_fss)

    -- Extract bracket info
    have ⟨h_fss_match, h_j_end⟩ : tokens[ps.pos + 1]!.val = .flowSequenceStart ∧
                                    tokens[j]!.val = .flowSequenceEnd := by
      rcases h_j_match with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · exact ⟨h1, h2⟩
      · rw [h_fss] at h1; cases h1

    have h_j_bound : j < tokens.size := by omega

    -- Show span for IH
    have h_span : j - (ps.pos + 2) ≤ span_bound := by
      sorry  -- j < endPos, endPos - body_start ≤ span_bound + 1

    -- Apply ih_seq for inner bracket body
    have h_inner_seq : ParseNodeFlowSeqOk tokens j (4 * tokens.size + 4) (ps.pos + 2) :=
      ih_seq j (ps.pos + 2) (4 * tokens.size + 4)
        h_j_bound (by omega) h_span h_j_end h_j_bal (by omega)

    -- Apply helper: parseExplicitKey on [
    have ⟨key_val, key_ps, h_key_ok, h_key_pos, h_key_tok, h_key_tp⟩ :=
      parseExplicitKey_flowSeq tokens ps.advance m j
        h_after_key_tok (by omega) h_m_fuel h_after_key_bound
        h_fss h_j_bound h_j_end h_j_bal h_inner_seq

    -- Build witness (similar to scalar case)
    refine ⟨key_val, key_ps, ?_, ?_, ?_, ?_, ?_, ?_⟩

    · exact h_key_ok
    · rw [h_key_pos]; omega  -- j + 1 > ps.pos since j > ps.pos + 1
    · rw [h_key_pos]; omega
    · exact h_key_tok
    · rw [h_key_tp]; subst h_tok; rfl

    · -- ∀ savedPath keyContent, parseFlowMappingValue succeeds
      intro savedPath keyContent

      have h_key_ps_pos_eq : key_ps.pos = j + 1 := h_key_pos

      have h_key_ps_value_tok : tokens[key_ps.pos]!.val = .value := by
        rw [h_key_ps_pos_eq]; exact h_j_value_tok

      have h_key_ps_value_peek : key_ps.peek? = some .value := by
        unfold ParseState.peek?
        rw [h_key_tok, if_pos (by rw [h_key_ps_pos_eq]; omega)]
        rw [h_key_ps_value_tok]

      have h_depth_at_value : flowBracketBalance tokens body_start (j + 1) = 0 := by
        sorry  -- Balance preserved

      have ⟨h_val_content_bound, h_val_content⟩ :=
        h_mbp.value_content (j + 1) (by omega) (by omega) h_depth_at_value h_j_value_tok

      have h_val_content_bound' : key_ps.pos + 1 < endPos := by
        rw [h_key_ps_pos_eq]; exact h_val_content_bound

      have h_val_content' : isFlowContentStart tokens[key_ps.pos + 1]!.val := by
        rw [h_key_ps_pos_eq]; exact h_val_content

      have h_depth_at_key_ps : flowBracketBalance tokens body_start key_ps.pos = 0 := by
        rw [h_key_ps_pos_eq]; exact h_depth_at_value

      -- Apply helper: parseFlowMappingValue (pass ps.pos as original_pos)
      have ⟨val_val, val_ps, h_val_ok, h_val_pos_gt, h_val_pos_le, h_val_tok_eq, h_val_tp, h_val_peek, h_val_bal⟩ :=
        (parseFlowMappingValue_ok tokens endPos body_start span_bound ps.pos key_ps m
          h_key_tok (by omega) h_m_fuel h_endPos_bound h_span_bound
          (by rw [h_key_ps_pos_eq]; omega)
          h_bs
          (by rw [h_key_ps_pos_eq]; omega)
          h_depth
          h_depth_at_key_ps h_key_ps_value_tok h_key_ps_value_peek
          h_val_content_bound' h_val_content'
          h_mbp h_sub ih_seq ih_map) savedPath keyContent

      refine ⟨val_val, val_ps, h_val_ok, ?_, ?_, ?_, ?_, ?_, ?_⟩

      · exact h_val_pos_gt
      · exact h_val_pos_le
      · exact h_val_tok_eq
      · rw [h_val_tp, h_key_tp]; subst h_tok; rfl
      · exact h_val_peek
      · exact h_val_bal

  · -- Key is flowMappingStart: .key → { → ... → } → .value → value_content → result
    -- Use MapBodyProps.key_bracket_value to find matching } and .value after it
    have ⟨j, h_j_gt, h_j_lt, h_j_match, h_j_bal, h_j_value_bound, h_j_value_tok⟩ :=
      h_mbp.key_bracket_value ps.pos (by omega) h_pos h_depth h_key_val (Or.inr h_fms)

    -- Extract bracket info
    have ⟨h_fms_match, h_j_end⟩ : tokens[ps.pos + 1]!.val = .flowMappingStart ∧
                                    tokens[j]!.val = .flowMappingEnd := by
      rcases h_j_match with ⟨h1, h2⟩ | ⟨h1, h2⟩
      · rw [h_fms] at h1; cases h1
      · exact ⟨h1, h2⟩

    have h_j_bound : j < tokens.size := by omega

    -- Show span for IH
    have h_span : j - (ps.pos + 2) ≤ span_bound := by
      sorry  -- j < endPos, endPos - body_start ≤ span_bound + 1

    -- Apply ih_map for inner bracket body
    have h_inner_map : ParseEntryFlowMapOk tokens j (4 * tokens.size + 4) (ps.pos + 2) :=
      ih_map j (ps.pos + 2) (4 * tokens.size + 4)
        h_j_bound (by omega) h_span h_j_end h_j_bal (by omega)

    -- Apply helper: parseExplicitKey on {
    have ⟨key_val, key_ps, h_key_ok, h_key_pos, h_key_tok, h_key_tp⟩ :=
      parseExplicitKey_flowMap tokens ps.advance m j
        h_after_key_tok (by omega) h_m_fuel h_after_key_bound
        h_fms h_j_bound h_j_end h_j_bal h_inner_map

    -- Build witness (symmetric with [ case)
    refine ⟨key_val, key_ps, ?_, ?_, ?_, ?_, ?_, ?_⟩

    · exact h_key_ok
    · rw [h_key_pos]; omega  -- j + 1 > ps.pos since j > ps.pos + 1
    · rw [h_key_pos]; omega
    · exact h_key_tok
    · rw [h_key_tp]; subst h_tok; rfl

    · -- ∀ savedPath keyContent, parseFlowMappingValue succeeds (same pattern as [ case)
      intro savedPath keyContent

      have h_key_ps_pos_eq : key_ps.pos = j + 1 := h_key_pos

      have h_key_ps_value_tok : tokens[key_ps.pos]!.val = .value := by
        rw [h_key_ps_pos_eq]; exact h_j_value_tok

      have h_key_ps_value_peek : key_ps.peek? = some .value := by
        unfold ParseState.peek?
        rw [h_key_tok, if_pos (by rw [h_key_ps_pos_eq]; omega)]
        rw [h_key_ps_value_tok]

      have h_depth_at_value : flowBracketBalance tokens body_start (j + 1) = 0 := by
        sorry  -- Balance preserved

      have ⟨h_val_content_bound, h_val_content⟩ :=
        h_mbp.value_content (j + 1) (by omega) (by omega) h_depth_at_value h_j_value_tok

      have h_val_content_bound' : key_ps.pos + 1 < endPos := by
        rw [h_key_ps_pos_eq]; exact h_val_content_bound

      have h_val_content' : isFlowContentStart tokens[key_ps.pos + 1]!.val := by
        rw [h_key_ps_pos_eq]; exact h_val_content

      have h_depth_at_key_ps : flowBracketBalance tokens body_start key_ps.pos = 0 := by
        rw [h_key_ps_pos_eq]; exact h_depth_at_value

      -- Apply helper: parseFlowMappingValue (pass ps.pos as original_pos)
      have ⟨val_val, val_ps, h_val_ok, h_val_pos_gt, h_val_pos_le, h_val_tok_eq, h_val_tp, h_val_peek, h_val_bal⟩ :=
        (parseFlowMappingValue_ok tokens endPos body_start span_bound ps.pos key_ps m
          h_key_tok (by omega) h_m_fuel h_endPos_bound h_span_bound
          (by rw [h_key_ps_pos_eq]; omega)
          h_bs
          (by rw [h_key_ps_pos_eq]; omega)
          h_depth
          h_depth_at_key_ps h_key_ps_value_tok h_key_ps_value_peek
          h_val_content_bound' h_val_content'
          h_mbp h_sub ih_seq ih_map) savedPath keyContent

      refine ⟨val_val, val_ps, h_val_ok, ?_, ?_, ?_, ?_, ?_, ?_⟩

      · exact h_val_pos_gt
      · exact h_val_pos_le
      · exact h_val_tok_eq
      · rw [h_val_tp, h_key_tp]; subst h_tok; rfl
      · exact h_val_peek
      · exact h_val_bal

/-- Combined theorem: `FlowSubrangesOk tokens` implies both `ParseNodeFlowSeqOk`
    and `ParseEntryFlowMapOk` for any valid body range.

    Proved by strong induction on `endPos - body_start`.  For inner bracket
    bodies (flowSeqStart / flowMapStart at depth 0), the matching bracket end
    is at `j < endPos`, so the inner body has span `j - (k+1) < endPos - body_start`.
    The IH then provides inner ParseNodeFlowSeqOk / ParseEntryFlowMapOk. -/
theorem flow_parser_ok_of_structure
    (tokens : Array (Positioned YamlToken))
    (h_sub : FlowSubrangesOk tokens) :
    -- For all valid seq bodies:
    (∀ endPos body_start fuel,
      endPos < tokens.size →
      tokens[endPos]!.val = .flowSequenceEnd →
      flowBracketBalance tokens body_start endPos = 0 →
      4 * tokens.size + 4 ≤ fuel →
      body_start ≤ endPos →
      ParseNodeFlowSeqOk tokens endPos fuel body_start) ∧
    -- For all valid map bodies:
    (∀ endPos body_start fuel,
      endPos < tokens.size →
      tokens[endPos]!.val = .flowMappingEnd →
      flowBracketBalance tokens body_start endPos = 0 →
      4 * tokens.size + 4 ≤ fuel →
      body_start ≤ endPos →
      ParseEntryFlowMapOk tokens endPos fuel body_start) := by
  -- Strong induction on span (endPos - body_start)
  suffices ∀ n,
    (∀ endPos body_start fuel,
      endPos < tokens.size → body_start ≤ endPos → endPos - body_start ≤ n →
      tokens[endPos]!.val = .flowSequenceEnd →
      flowBracketBalance tokens body_start endPos = 0 →
      4 * tokens.size + 4 ≤ fuel →
      ParseNodeFlowSeqOk tokens endPos fuel body_start) ∧
    (∀ endPos body_start fuel,
      endPos < tokens.size → body_start ≤ endPos → endPos - body_start ≤ n →
      tokens[endPos]!.val = .flowMappingEnd →
      flowBracketBalance tokens body_start endPos = 0 →
      4 * tokens.size + 4 ≤ fuel →
      ParseEntryFlowMapOk tokens endPos fuel body_start) by
    constructor
    · intro endPos body_start fuel h_hi h_end_tok h_bal h_fuel h_bs_ep
      obtain ⟨h_seq, _⟩ := this (endPos - body_start)
      exact h_seq endPos body_start fuel h_hi h_bs_ep (Nat.le_refl _) h_end_tok h_bal h_fuel
    · intro endPos body_start fuel h_hi h_end_tok h_bal h_fuel h_bs_ep
      obtain ⟨_, h_map⟩ := this (endPos - body_start)
      exact h_map endPos body_start fuel h_hi h_bs_ep (Nat.le_refl _) h_end_tok h_bal h_fuel
  -- Induction on n
  intro n
  induction n with
  | zero =>
    constructor
    · intro endPos body_start fuel h_hi h_bs_ep h_span h_end_tok h_bal h_fuel
      intro ps m h_tok h_m_pos h_m_le h_pos h_bs h_depth h_cs
      -- span = 0 means body_start = endPos, but ps.pos < endPos and body_start ≤ ps.pos
      omega
    · intro endPos body_start fuel h_hi h_bs_ep h_span h_end_tok h_bal h_fuel
      intro ps m h_tok h_m_pos h_m_le h_pos h_bs h_depth h_key
      omega
  | succ n ih =>
    obtain ⟨ih_seq, ih_map⟩ := ih
    constructor
    · -- Sequence case
      intro endPos body_start fuel h_hi h_bs_ep h_span h_end_tok h_bal h_fuel
      intro ps m h_tok h_m_pos h_m_le h_pos h_bs h_depth h_cs
      have h_sbp : SeqBodyProps tokens body_start endPos :=
        h_sub.seq body_start endPos h_bs_ep h_hi h_end_tok h_bal
      -- Case split on content type
      rcases h_cs with ⟨c, sc, h_scalar⟩ | h_fss | h_fms
      · -- Scalar case: use helper lemma
        exact parseNode_scalar_in_seq tokens endPos body_start h_hi h_sbp ps m
          h_tok h_m_pos h_pos h_bs h_depth c sc h_scalar
      · -- Nested flowSequenceStart: check fuel sufficiency
        by_cases h_m_suff : 4 * tokens.size + 6 ≤ m
        · -- Sufficient fuel: use helper
          exact parseNode_flowSeqStart_in_seq tokens endPos body_start n h_hi h_span
            h_sub h_sbp ih_seq ih_map ps m h_tok h_m_pos h_m_suff h_pos h_bs h_depth h_fss
        · -- Insufficient fuel: show this leads to error or handle inline
          -- When 4*N+4 ≤ fuel < 4*N+6 and m ≤ fuel, we have m < 4*N+6
          -- For well-formed structures, parseNode might fail with nestingDepthExceeded
          -- or we need inline proof for small m case
          sorry
      · -- Nested flowMappingStart: check fuel sufficiency
        by_cases h_m_suff : 4 * tokens.size + 6 ≤ m
        · -- Sufficient fuel: use helper
          exact parseNode_flowMapStart_in_seq tokens endPos body_start n h_hi h_span
            h_sub h_sbp ih_seq ih_map ps m h_tok h_m_pos h_m_suff h_pos h_bs h_depth h_fms
        · -- Insufficient fuel: show this leads to error or handle inline
          sorry
    · -- Mapping case
      intro endPos body_start fuel h_hi h_bs_ep h_span h_end_tok h_bal h_fuel
      intro ps m h_tok h_m_pos h_m_le h_pos h_bs h_depth h_key
      have h_mbp : MapBodyProps tokens body_start endPos :=
        h_sub.map body_start endPos h_bs_ep h_hi h_end_tok h_bal
      -- Use parseEntry_in_flowMap helper: check fuel sufficiency
      by_cases h_m_suff : 4 * tokens.size + 6 ≤ m
      · -- Sufficient fuel: use helper
        exact parseEntry_in_flowMap tokens endPos body_start n h_hi h_span
          h_sub h_mbp ih_seq ih_map ps m h_tok h_m_pos h_m_suff h_pos h_bs h_depth h_key
      · -- Insufficient fuel: show this leads to error or handle inline
        sorry

end L4YAML.Proofs.ParserGrammable
