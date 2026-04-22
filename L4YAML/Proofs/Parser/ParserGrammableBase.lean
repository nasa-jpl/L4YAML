import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Proofs.Production.ScannerPlainScalarValid
import L4YAML.Proofs.Composition

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Phase C Base: Composition Layer (ParserGrammableBase)

Algebraic/compositional proofs for the scanner+parser grammability chain.
Defines `AllAliasesResolve`, `WellFormedAnchors`, and proves C1
(`compose_grammable`): if a value is `Scannable`, aliases resolve, and
anchor values are well-formed, then `compose` produces `Grammable` output.

Split from `ParserGrammable.lean` for modularity — this file contains
§1–§4 of the original.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition

/-! ## §1  ScalarScannable Metadata Independence

`ScalarScannable` depends only on `Scalar.content` and `Scalar.style`.
The `tag`, `anchor`, and `blockMeta` fields are irrelevant.
-/

/-- `ScalarScannable` depends only on `content` and `style`. -/
theorem ScalarScannable_eq_of_content_style_eq
    (c : String) (st : ScalarStyle)
    (t1 t2 : Option String) (a1 a2 : Option String)
    (b1 b2 : Option BlockScalarMeta) (inFlow : Bool) :
    ScalarScannable ⟨c, st, t1, a1, b1⟩ inFlow ↔
      ScalarScannable ⟨c, st, t2, a2, b2⟩ inFlow := by
  constructor <;> (intro h hplain hlen; exact h hplain hlen)

/-- Clearing the anchor field preserves `ScalarScannable`. -/
theorem ScalarScannable_strip_anchor (s : Scalar) (inFlow : Bool) :
    ScalarScannable s inFlow ↔
      ScalarScannable { s with anchor := none } inFlow := by
  constructor <;> (intro h hplain hlen; exact h hplain hlen)

/-- Non-plain scalars trivially satisfy `ScalarScannable`. -/
theorem ScalarScannable_of_nonplain (s : Scalar) (inFlow : Bool)
    (h : s.style ≠ .plain) :
    ScalarScannable s inFlow :=
  fun hplain _ => absurd hplain h

/-! ## §2  `stripAnchors` Preserves `Grammable`

`YamlValue.stripAnchors` only clears anchor fields. Since `Grammable`
does not constrain anchor fields and `ScalarScannable` is metadata-
independent, `Grammable` is preserved.
-/

/-- `stripAnchors` on a `.scalar` node preserves `Grammable`. -/
theorem stripAnchors_scalar_grammable (s : Scalar) (inFlow : Bool)
    (h : Grammable (.scalar s) inFlow) :
    Grammable (.scalar { s with anchor := none }) inFlow := by
  cases h with
  | scalar _ _ h_ss =>
    exact .scalar { s with anchor := none } inFlow
      ((ScalarScannable_strip_anchor s inFlow).mp h_ss)

/-- The `stripList` where-clause helper equals `List.map stripAnchors`. -/
theorem stripList_eq_map (l : List YamlValue) :
    YamlValue.stripAnchors.stripList l = l.map YamlValue.stripAnchors := by
  induction l with
  | nil => simp [YamlValue.stripAnchors.stripList]
  | cons v vs ih => simp [YamlValue.stripAnchors.stripList, ih]

/-- The `stripPairs` where-clause helper equals `List.map` over pairs. -/
theorem stripPairs_eq_map (l : List (YamlValue × YamlValue)) :
    YamlValue.stripAnchors.stripPairs l =
      l.map (fun (k, v) => (k.stripAnchors, v.stripAnchors)) := by
  induction l with
  | nil => simp [YamlValue.stripAnchors.stripPairs]
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp [YamlValue.stripAnchors.stripPairs, ih]

set_option maxHeartbeats 2400000 in
/-- `stripAnchors` preserves `Grammable` for any value.

The proof is by induction on the `Grammable` derivation. The scalar
case uses metadata independence. The sequence/mapping cases use the
`stripList_eq_map`/`stripPairs_eq_map` lemmas to reduce where-clause
mutual recursion to `List.map`, then apply the IH element-wise. -/
theorem stripAnchors_preserves_Grammable (v : YamlValue) (inFlow : Bool) :
    Grammable v inFlow → Grammable v.stripAnchors inFlow := by
  intro h
  induction h with
  | scalar s inFlow h_ss =>
    exact .scalar { s with anchor := none } inFlow
      (fun hplain hlen => h_ss hplain hlen)
  | sequence style items tag anchor inFlow h_items ih_items =>
    show Grammable (.sequence style (YamlValue.stripAnchors.stripList items.toList).toArray tag none) inFlow
    rw [stripList_eq_map]
    apply Grammable.sequence
    intro ⟨i, hi⟩
    simp at hi ⊢
    exact ih_items ⟨i, hi⟩
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    show Grammable (.mapping style (YamlValue.stripAnchors.stripPairs pairs.toList).toArray tag none) inFlow
    rw [stripPairs_eq_map]
    apply Grammable.mapping
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_k ⟨i, hi⟩
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_v ⟨i, hi⟩

/-! ## §3  `Scannable` → `Grammable` for Alias-Free Values

When a value has no `.alias` nodes, `Scannable` and `Grammable` coincide
(modulo the `.alias` constructor that `Scannable` allows).
-/

/-- A `YamlValue` contains no alias nodes. -/
inductive AliasFree : YamlValue → Prop where
  | scalar (s : Scalar) : AliasFree (.scalar s)
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String)
      (h : ∀ i : Fin items.size, AliasFree items[i]) :
      AliasFree (.sequence style items tag anchor)
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String)
      (hk : ∀ i : Fin pairs.size, AliasFree pairs[i].1)
      (hv : ∀ i : Fin pairs.size, AliasFree pairs[i].2) :
      AliasFree (.mapping style pairs tag anchor)

/-- Alias-free `Scannable` implies `Grammable`. -/
theorem Scannable_aliasFree_to_Grammable (v : YamlValue) (inFlow : Bool) :
    Scannable v inFlow → AliasFree v → Grammable v inFlow := by
  intro h_scan h_af
  induction h_scan with
  | scalar s _ h_ss => exact .scalar s _ h_ss
  | alias _ _ => cases h_af
  | sequence style items tag anchor inFlow h_items ih_items =>
    cases h_af with
    | sequence _ _ _ _ h_af_items =>
      apply Grammable.sequence
      intro ⟨i, hi⟩
      exact ih_items ⟨i, hi⟩ (h_af_items ⟨i, hi⟩)
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    cases h_af with
    | mapping _ _ _ _ h_afk h_afv =>
      apply Grammable.mapping
      · intro ⟨i, hi⟩
        exact ih_k ⟨i, hi⟩ (h_afk ⟨i, hi⟩)
      · intro ⟨i, hi⟩
        exact ih_v ⟨i, hi⟩ (h_afv ⟨i, hi⟩)

/-! ## §4  Compose: `Scannable` → `Grammable` (C1)

### Preconditions

`compose_value_grammable` requires:
1. The pre-compose value satisfies `Scannable v inFlow`
2. All aliases in `v` resolve through the anchor map (`AllAliasesResolve`)
3. Resolved anchor values are themselves `Grammable` at every flow context
   (`WellFormedAnchors`)

The third precondition handles cross-context aliasing: an anchor defined
in block context may be aliased into flow context, so the resolved value
must be `Grammable` at any flow context it might appear in.

### Why `∀ ctx` in WellFormedAnchors

A plain scalar like `value{key}` scanned in block context satisfies
`ScalarScannable _ false` but NOT `ScalarScannable _ true` (due to
flow indicators `{` and `}`). If this value is aliased into flow context,
`Grammable _ true` requires `ScalarScannable _ true`, which fails.

The `∀ ctx` precondition excludes such cross-context aliasing scenarios.
In practice, most YAML documents don't alias block-context plain scalars
with flow indicators into flow context.
-/

/-- All alias nodes in a value resolve through the anchor map. -/
inductive AllAliasesResolve : YamlValue → Array (String × YamlValue) → Prop where
  | scalar (s : Scalar) (anchors : Array (String × YamlValue)) :
      AllAliasesResolve (.scalar s) anchors
  | alias (name : String) (anchors : Array (String × YamlValue))
      (h : (anchors.findSome? (fun (n, _) => if n == name then some () else none)).isSome) :
      AllAliasesResolve (.alias name) anchors
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String)
      (anchors : Array (String × YamlValue))
      (h : ∀ i : Fin items.size, AllAliasesResolve items[i] anchors) :
      AllAliasesResolve (.sequence style items tag anchor) anchors
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String)
      (anchors : Array (String × YamlValue))
      (hk : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].1 anchors)
      (hv : ∀ i : Fin pairs.size, AllAliasesResolve pairs[i].2 anchors) :
      AllAliasesResolve (.mapping style pairs tag anchor) anchors

/-- Anchor values are well-formed: after stripping, they are `Grammable`
    at every flow context. -/
def WellFormedAnchors (anchors : Array (String × YamlValue)) : Prop :=
  ∀ (name : String) (val : YamlValue),
    anchors.findSome? (fun (n, v) => if n == name then some v else none) = some val →
      ∀ inFlow, Grammable val.stripAnchors inFlow

/-! ### adaptForFlowContext: bridging + grammability lifting

These lemmas prove that `YamlValue.adaptForFlowContext` makes any
`Grammable v b` value universally grammable (at every flow context).
This is the core tool for discharging `parseStream_output_anchors_wellformed`. -/

/-- `hasFlowIndicator cs = false` implies no flow indicators (Prop).
    Each char-level check in `hasFlowIndicator` exactly matches `isFlowIndicatorProp`,
    so `hasFlowIndicator cs = false` means no char in `cs` is a flow indicator. -/
theorem hasFlowIndicator_false_noFlowIndicators (content : String)
    (h : hasFlowIndicator content.toList = false) :
    noFlowIndicatorsProp content := by
  unfold noFlowIndicatorsProp
  suffices ∀ (cs : List Char), hasFlowIndicator cs = false →
      ∀ c ∈ cs, ¬isFlowIndicatorProp c by exact this content.toList h
  intro cs
  induction cs with
  | nil => intro _ c hc; nomatch hc
  | cons x xs ih =>
    intro h_fi c hc hfi
    simp only [hasFlowIndicator, Bool.or_eq_false_iff] at h_fi
    obtain ⟨h_char, h_rest⟩ := h_fi
    rcases List.mem_cons.mp hc with rfl | hmem
    · simp only [beq_eq_false_iff_ne] at h_char
      obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h_char
      unfold isFlowIndicatorProp at hfi
      cases hfi with
      | head => exact h1 rfl
      | tail _ hfi => cases hfi with
        | head => exact h2 rfl
        | tail _ hfi => cases hfi with
          | head => exact h3 rfl
          | tail _ hfi => cases hfi with
            | head => exact h4 rfl
            | tail _ hfi => cases hfi with
              | head => exact h5 rfl
              | tail _ hfi => nomatch hfi
    · exact ih h_rest c hmem hfi

/-- If `ScalarScannable s false` and content has no flow indicators,
    then `ScalarScannable s true`.

    The only difference between `false` and `true` contexts is that
    exception chars (-, ?, :) with a next char add `¬isFlowIndicatorProp n`
    in flow context, which follows from `noFlowIndicatorsProp`. -/
theorem ScalarScannable_false_to_true_noFI (s : Scalar)
    (h : ScalarScannable s false)
    (h_nfi : noFlowIndicatorsProp s.content) :
    ScalarScannable s true := by
  intro hplain hlen
  have ⟨hvpf, hcs, hsh, _⟩ := h hplain hlen
  refine ⟨?_, hcs, hsh, fun _ => h_nfi⟩
  -- Upgrade validPlainFirstProp from false → true.
  -- The only inFlow-dependent part is exception chars with a next char.
  unfold validPlainFirstProp at hvpf ⊢
  generalize hcl : s.content.toList = cl at hvpf ⊢
  match cl with
  | [] => trivial
  | [c] =>
    -- Reduce match [c] in both hvpf and goal
    dsimp only [] at hvpf ⊢
    -- if exception then True else canStartPlainScalarProp c none inFlow
    split
    · trivial
    · split at hvpf
      · contradiction
      · -- canStartPlainScalarProp c none false → true: inFlow-independent for none
        unfold canStartPlainScalarProp at hvpf ⊢
        dsimp only [] at hvpf ⊢
        exact hvpf
  | c :: n :: rest =>
    -- Reduce match (c :: n :: rest) in both hvpf and goal
    dsimp only [] at hvpf ⊢
    -- canStartPlainScalarProp c (some n) false → true
    unfold canStartPlainScalarProp at hvpf ⊢
    dsimp only [] at hvpf ⊢
    -- Both: if exc then (¬ws ∧ ¬lb ∧ (inFlow=true → ¬fi)) else (¬ind ∧ ¬ws ∧ ¬lb)
    split at hvpf
    · -- Exception branch in hvpf
      split
      · -- Exception in goal: upgrade ∧-conjunction with h_nfi
        have h_n_mem : n ∈ s.content.toList := by
          rw [hcl]; exact .tail _ (.head _)
        exact ⟨hvpf.1, hvpf.2.1, fun _ => h_nfi n h_n_mem⟩
      · contradiction
    · -- Non-exception branch in hvpf: identical for both inFlow values
      split
      · contradiction
      · exact hvpf

/-- The `adaptList` where-clause helper equals `List.map adaptForFlowContext`. -/
theorem adaptList_eq_map (l : List YamlValue) :
    YamlValue.adaptForFlowContext.adaptList l =
      l.map YamlValue.adaptForFlowContext := by
  induction l with
  | nil => simp [YamlValue.adaptForFlowContext.adaptList]
  | cons v vs ih => simp [YamlValue.adaptForFlowContext.adaptList, ih]

/-- The `adaptPairs` where-clause helper equals `List.map` over pairs. -/
theorem adaptPairs_eq_map (l : List (YamlValue × YamlValue)) :
    YamlValue.adaptForFlowContext.adaptPairs l =
      l.map (fun (k, v) => (k.adaptForFlowContext, v.adaptForFlowContext)) := by
  induction l with
  | nil => simp [YamlValue.adaptForFlowContext.adaptPairs]
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp [YamlValue.adaptForFlowContext.adaptPairs, ih]

-- **Core lifting lemma**: `adaptForFlowContext` makes any `Grammable` value
--     universally grammable.
--
--     If `Grammable v b` for some flow context `b`, then
--     `Grammable v.adaptForFlowContext inFlow` for every `inFlow`.
--
--     - Plain scalars with flow indicators → `.doubleQuoted` (vacuously scannable)
--     - Plain scalars without flow indicators → unchanged (scannable at both contexts)
--     - Non-plain scalars → unchanged (vacuously scannable)
--     - Collections → recursive
set_option maxHeartbeats 800000 in
theorem adaptForFlowContext_grammable_forall (v : YamlValue) (b : Bool)
    (h : Grammable v b) : ∀ inFlow, Grammable v.adaptForFlowContext inFlow := by
  induction h with
  | scalar s b h_ss =>
    intro inFlow
    show Grammable (if s.style == .plain && hasFlowIndicator s.content.toList
      then .scalar { s with style := .doubleQuoted } else .scalar s) inFlow
    split
    · -- s.style == .plain && hasFlowIndicator → doubleQuoted (vacuously scannable)
      exact .scalar { s with style := .doubleQuoted } inFlow
        (fun h_plain => by dsimp only [] at h_plain; contradiction)
    · -- else: s unchanged
      rename_i h_neg
      simp only [Bool.and_eq_true] at h_neg
      by_cases hplain : s.style = .plain
      · -- plain but no flow indicators
        have h_no_fi : hasFlowIndicator s.content.toList = false := by
          cases h_fi : hasFlowIndicator s.content.toList with
          | false => rfl
          | true =>
            have h_beq : (s.style == ScalarStyle.plain) = true := by rw [hplain]; decide
            exact absurd ⟨h_beq, h_fi⟩ h_neg
        have h_nfi := hasFlowIndicator_false_noFlowIndicators s.content h_no_fi
        have h_false := ScalarScannable_any_implies_false s b h_ss
        cases inFlow with
        | false => exact .scalar s false h_false
        | true =>
          exact .scalar s true (ScalarScannable_false_to_true_noFI s h_false h_nfi)
      · -- non-plain: vacuously scannable
        exact .scalar s inFlow (fun h_eq => absurd h_eq hplain)
  | sequence style items tag anchor b h_items ih_items =>
    intro inFlow
    show Grammable (.sequence style
      (YamlValue.adaptForFlowContext.adaptList items.toList).toArray tag anchor) inFlow
    rw [adaptList_eq_map]
    apply Grammable.sequence
    intro ⟨i, hi⟩
    simp at hi ⊢
    exact ih_items ⟨i, hi⟩ _
  | mapping style pairs tag anchor b hk hv ih_k ih_v =>
    intro inFlow
    show Grammable (.mapping style
      (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray tag anchor) inFlow
    rw [adaptPairs_eq_map]
    apply Grammable.mapping
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_k ⟨i, hi⟩ _
    · intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_v ⟨i, hi⟩ _

/-- If `findSome?` with unit-returning predicate succeeds, then
    `findSome?` with value-returning predicate also succeeds. -/
theorem findSome_unit_to_val (arr : Array (String × YamlValue)) (name : String)
    (h : (arr.findSome? (fun (n, _) => if n == name then some () else none)).isSome) :
    ∃ val, arr.findSome? (fun (n, v) => if n == name then some v else none) = some val := by
  simp only [Option.isSome_iff_exists] at h
  obtain ⟨_, h_find⟩ := h
  rw [Array.findSome?_eq_some_iff] at h_find
  obtain ⟨ys, a, zs, h_split, h_fa, h_prefix⟩ := h_find
  have h_beq : (a.1 == name) = true := by
    revert h_fa
    split
    · intro _; assumption
    · intro h_abs; simp at h_abs
  exact ⟨a.2, Array.findSome?_eq_some_iff.mpr
    ⟨ys, a, zs, h_split, by simp [h_beq], fun x hx => by
      have h_unit := h_prefix x hx
      by_cases h_eq : x.1 == name
      · simp [h_eq] at h_unit
      · simp [h_eq]⟩⟩

/-- The `resolveList` where-clause helper equals `List.map resolveAliases`. -/
theorem resolveList_eq_map (l : List YamlValue) (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliases.resolveList l anchors =
      l.map (fun v => v.resolveAliases anchors) := by
  induction l with
  | nil => simp [YamlValue.resolveAliases.resolveList]
  | cons v vs ih => simp [YamlValue.resolveAliases.resolveList, ih]

/-- The `resolvePairs` where-clause helper equals `List.map` over pairs. -/
theorem resolvePairs_eq_map (l : List (YamlValue × YamlValue))
    (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliases.resolvePairs l anchors =
      l.map (fun (k, v) => (k.resolveAliases anchors, v.resolveAliases anchors)) := by
  induction l with
  | nil => simp [YamlValue.resolveAliases.resolvePairs]
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    simp [YamlValue.resolveAliases.resolvePairs, ih]

set_option maxHeartbeats 4000000 in
/-- C1: Composing a `Scannable` value produces a `Grammable` value,
    provided all aliases resolve and anchor values are well-formed.

    `doc.compose.value = (doc.value.resolveAliases doc.anchors).stripAnchors`

    The proof is by induction on the `Scannable` derivation:
    - **scalar**: resolveAliases is identity on scalars; use metadata independence.
    - **alias**: Use `findSome_unit_to_val` to resolve the alias lookup,
      then apply `WellFormedAnchors`.
    - **sequence/mapping**: Rewrite where-clause recursion using
      `resolveList_eq_map`/`resolvePairs_eq_map` and
      `stripList_eq_map`/`stripPairs_eq_map`, then apply IH element-wise. -/
theorem compose_value_grammable
    (v : YamlValue) (anchors : Array (String × YamlValue)) (inFlow : Bool)
    (h_scan : Scannable v inFlow)
    (h_resolve : AllAliasesResolve v anchors)
    (h_anchors : WellFormedAnchors anchors) :
    Grammable (v.resolveAliases anchors).stripAnchors inFlow := by
  induction h_scan with
  | scalar s inFlow h_ss =>
    exact .scalar { s with anchor := none } inFlow
      ((ScalarScannable_strip_anchor s inFlow).mp h_ss)
  | alias name inFlow =>
    cases h_resolve with
    | alias _ _ h_res =>
      obtain ⟨resolved, h_val⟩ := findSome_unit_to_val anchors name h_res
      have h_eq : (YamlValue.alias name).resolveAliases anchors =
        (match anchors.findSome? (fun (n, v) => if n == name then some v else none) with
         | some v => v | none => .alias name) := rfl
      rw [h_eq, h_val]
      exact h_anchors name resolved h_val inFlow
  | sequence style items tag anchor inFlow h_items ih_items =>
    cases h_resolve with
    | sequence _ _ _ _ _ h_resolve_items =>
      show Grammable (.sequence style
        (YamlValue.stripAnchors.stripList
          (YamlValue.resolveAliases.resolveList items.toList anchors).toArray.toList).toArray
        tag none) inFlow
      rw [List.toList_toArray, stripList_eq_map, resolveList_eq_map]
      apply Grammable.sequence
      intro ⟨i, hi⟩
      simp at hi ⊢
      exact ih_items ⟨i, hi⟩ (h_resolve_items ⟨i, hi⟩)
  | mapping style pairs tag anchor inFlow hk hv ih_k ih_v =>
    cases h_resolve with
    | mapping _ _ _ _ _ hk_resolve hv_resolve =>
      show Grammable (.mapping style
        (YamlValue.stripAnchors.stripPairs
          (YamlValue.resolveAliases.resolvePairs pairs.toList anchors).toArray.toList).toArray
        tag none) inFlow
      rw [List.toList_toArray, stripPairs_eq_map, resolvePairs_eq_map]
      apply Grammable.mapping
      · intro ⟨i, hi⟩
        simp at hi ⊢
        exact ih_k ⟨i, hi⟩ (hk_resolve ⟨i, hi⟩)
      · intro ⟨i, hi⟩
        simp at hi ⊢
        exact ih_v ⟨i, hi⟩ (hv_resolve ⟨i, hi⟩)

/-- C1 applied to `YamlDocument.compose`. -/
theorem compose_grammable (doc : YamlDocument)
    (h_scan : Scannable doc.value false)
    (h_resolve : AllAliasesResolve doc.value doc.anchors)
    (h_anchors : WellFormedAnchors doc.anchors) :
    Grammable doc.compose.value false := by
  simp only [YamlDocument.compose]
  exact compose_value_grammable doc.value doc.anchors false h_scan h_resolve h_anchors

/-! ## Flow bracket nesting utilities

Used by emitter scannability theorems and parser loop fuel sufficiency proofs
to distinguish outer-level flowEntries (bracket balance = 0) from inner ones
(balance > 0) inside nested bracket groups. -/

/-- Flow bracket delta for a YamlToken: +1 for flow open brackets,
    -1 for flow close brackets, 0 for everything else. -/
def flowBracketDelta : YamlToken → Int
  | .flowSequenceStart | .flowMappingStart => 1
  | .flowSequenceEnd | .flowMappingEnd => -1
  | _ => 0

/-- Flow bracket balance of the token array from position `lo` to `hi`
    (exclusive at `hi`). Returns the cumulative opening − closing bracket count.
    Used to distinguish outer-level flowEntries (balance = 0) from inner ones
    (balance > 0) when characterizing emitter-produced token patterns. -/
def flowBracketBalance (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Int :=
  if lo ≥ hi then 0
  else
    let slice := tokens.toList.drop lo |>.take (hi - lo)
    slice.foldl (fun acc t => acc + flowBracketDelta t.val) 0

-- Helper: foldl of additive function shifts the init out
theorem foldl_add_shift {α : Type _} (l : List α) (f : α → Int) (init : Int) :
    l.foldl (fun acc t => acc + f t) init = init + l.foldl (fun acc t => acc + f t) 0 := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih, ih (0 + f hd)]
    omega

/-- Bracket balance composition: splitting a range at a midpoint yields additive
    balance values. -/
theorem flowBracketBalance_compose (tokens : Array (Positioned YamlToken))
    (lo mid hi : Nat) (h_lm : lo ≤ mid) (h_mh : mid ≤ hi) :
    flowBracketBalance tokens lo hi = flowBracketBalance tokens lo mid + flowBracketBalance tokens mid hi := by
  by_cases h1 : lo = mid
  · subst h1; simp [flowBracketBalance]
  · by_cases h2 : mid = hi
    · subst h2; simp [flowBracketBalance]
    · -- lo < mid < hi — all three ranges are non-trivial
      have h_lo_lt_hi : ¬(lo ≥ hi) := by omega
      have h_lo_lt_mid : ¬(lo ≥ mid) := by omega
      have h_mid_lt_hi : ¬(mid ≥ hi) := by omega
      simp only [flowBracketBalance, h_lo_lt_hi, h_lo_lt_mid, h_mid_lt_hi, ↓reduceIte]
      -- Decompose: take (hi-lo) (drop lo l) = take (mid-lo) (drop lo l) ++ take (hi-mid) (drop mid l)
      -- via List.take_add + List.drop_drop
      have h_eq : hi - lo = (mid - lo) + (hi - mid) := by omega
      rw [h_eq]
      rw [List.take_add]
      rw [List.foldl_append]
      rw [foldl_add_shift]
      congr 1
      rw [List.drop_drop, show lo + (mid - lo) = mid from by omega]

/-- Appending a token to the array does not affect bracket balance for ranges
    within the original array bounds. -/
theorem flowBracketBalance_push (tokens : Array (Positioned YamlToken))
    (tok : Positioned YamlToken) (lo hi : Nat) (h : hi ≤ tokens.size) :
    flowBracketBalance (tokens.push tok) lo hi = flowBracketBalance tokens lo hi := by
  simp only [flowBracketBalance]
  split
  · rfl
  · congr 1
    have h_sz : tokens.toList.length = tokens.size := rfl
    simp only [Array.toList_push, List.drop_append,
               show lo - tokens.toList.length = 0 from by omega,
               List.take_append, List.length_drop,
               show (hi - lo) - (tokens.toList.length - lo) = 0 from by omega,
               List.take_zero, List.drop_zero, List.append_nil]

/-- The bracket balance of a single token equals its bracket delta. -/
theorem flowBracketBalance_single (tokens : Array (Positioned YamlToken))
    (i : Nat) (h : i < tokens.toList.length) :
    flowBracketBalance tokens i (i + 1) = flowBracketDelta tokens.toList[i].val := by
  simp only [flowBracketBalance, show ¬(i ≥ i + 1) from by omega, ↓reduceIte,
             show i + 1 - i = 1 from by omega]
  rw [List.drop_eq_getElem_cons h]
  simp [List.foldl]

/-- Composing a zero-balance prefix, a single non-bracket token, and a zero-balance suffix
    yields zero total balance. Used for flowEntry + parseNode compositions. -/
theorem flowBracketBalance_compose_zero (tokens : Array (Positioned YamlToken))
    (body_start pos pos_after : Nat)
    (h_bs_pos : body_start ≤ pos)
    (h_pos_bound : pos < tokens.toList.length)
    (h_pos_after : pos + 1 ≤ pos_after)
    (h_bal : flowBracketBalance tokens body_start pos = 0)
    (h_delta : flowBracketDelta tokens.toList[pos].val = 0)
    (h_tail : flowBracketBalance tokens (pos + 1) pos_after = 0) :
    flowBracketBalance tokens body_start pos_after = 0 := by
  rw [flowBracketBalance_compose tokens body_start (pos + 1) pos_after (by omega) h_pos_after,
      flowBracketBalance_compose tokens body_start pos (pos + 1) h_bs_pos (by omega),
      h_bal, h_tail, flowBracketBalance_single _ _ h_pos_bound, h_delta]; omega

/-! ### §6  Structural predicates for flow body subranges

These predicates capture the token-level structural properties that
`flow_parser_ok_of_structure` needs to prove `ParseNodeFlowSeqOk` and
`ParseEntryFlowMapOk` by mutual strong induction on span.

The universal quantification over all (lo, hi) subranges handles
nesting automatically: inner bracket bodies satisfy the same predicates,
so the inductive hypothesis applies.

**Phase I infrastructure**: These predicates are sorry'd conclusions of
the body characterization theorems; the proofs that emitter output
satisfies them is deferred to Phase J. -/

/-- A content-start token is one that `parseNodeContent` dispatches
    to `parseNode` (scalar) or to `parseFlowSequence`/`parseFlowMapping`. -/
def isFlowContentStart (tok : YamlToken) : Prop :=
  (∃ c s, tok = .scalar c s) ∨ tok = .flowSequenceStart ∨ tok = .flowMappingStart

/-- Structural properties of a well-formed flow SEQUENCE body `[lo, hi)`.

    Assumed: `tokens[hi]!.val = .flowSequenceEnd` and
    `flowBracketBalance tokens lo hi = 0`.

    Properties:
    - S1: content-start at `lo` (when non-empty)
    - S2: scalar at depth 0 → FE or seqEnd successor
    - S3: FE at depth 0 → content-start at next position
    - S4: flowSeqStart at depth 0 → matching seqEnd with balanced inner body + successor
    - S5: flowMapStart at depth 0 → matching mapEnd with balanced inner body + successor -/
structure SeqBodyProps (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  content_start : lo < hi → isFlowContentStart tokens[lo]!.val
  scalar_succ : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    (∃ c s, tokens[k]!.val = .scalar c s) →
    k + 1 ≤ hi ∧
    (tokens[k+1]!.val = .flowEntry ∨
     (tokens[k+1]!.val = .flowSequenceEnd ∧ k + 1 = hi))
  after_fe : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowEntry →
    k + 1 < hi ∧ isFlowContentStart tokens[k+1]!.val
  bracket_seq : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowSequenceStart →
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowSequenceEnd ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi))
  bracket_map : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowMappingStart →
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowMappingEnd ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi))

/-- Structural properties of a well-formed flow MAPPING body `[lo, hi)`.

    Assumed: `tokens[hi]!.val = .flowMappingEnd` and
    `flowBracketBalance tokens lo hi = 0`.

    The mapping body token pattern at depth 0 is:
    `.key, key_content, .value, val_content, (.flowEntry | .flowMappingEnd), ...`

    Properties M1–M10 capture what `parseExplicitKey` and `parseFlowMappingValue`
    need for acceptance. -/
structure MapBodyProps (tokens : Array (Positioned YamlToken)) (lo hi : Nat) : Prop where
  /-- M1: `.key` at start (when non-empty). -/
  key_start : lo < hi → tokens[lo]!.val = .key
  /-- M2: FE at depth 0 → `.key` follows. -/
  after_fe : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowEntry →
    k + 1 ≤ hi ∧ tokens[k+1]!.val = .key
  /-- M3: After `.key` at depth 0, content-start follows. -/
  key_content : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .key →
    k + 1 < hi ∧ isFlowContentStart tokens[k+1]!.val
  /-- M4: After `.key` + scalar, `.value` follows. -/
  key_scalar_value : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .key →
    (∃ c s, tokens[k+1]!.val = .scalar c s) →
    k + 2 < hi ∧ tokens[k+2]!.val = .value
  /-- M5: After `.key` + bracket start, matching end exists and `.value` after it. -/
  key_bracket_value : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .key →
    (tokens[k+1]!.val = .flowSequenceStart ∨ tokens[k+1]!.val = .flowMappingStart) →
    ∃ j, k + 1 < j ∧ j < hi ∧
      ((tokens[k+1]!.val = .flowSequenceStart ∧ tokens[j]!.val = .flowSequenceEnd) ∨
       (tokens[k+1]!.val = .flowMappingStart ∧ tokens[j]!.val = .flowMappingEnd)) ∧
      flowBracketBalance tokens (k+2) j = 0 ∧
      j + 1 < hi ∧ tokens[j+1]!.val = .value
  /-- M6: After `.value` at depth 0, content-start follows. -/
  value_content : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .value →
    k + 1 < hi ∧ isFlowContentStart tokens[k+1]!.val
  /-- M7: After `.value` + scalar, FE or mapEnd follows. -/
  value_scalar_succ : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .value →
    (∃ c s, tokens[k+1]!.val = .scalar c s) →
    k + 2 ≤ hi ∧
    (tokens[k+2]!.val = .flowEntry ∨
     (tokens[k+2]!.val = .flowMappingEnd ∧ k + 2 = hi))
  /-- M8: After `.value` + bracket start, matching end and FE/mapEnd after. -/
  value_bracket_succ : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .value →
    (tokens[k+1]!.val = .flowSequenceStart ∨ tokens[k+1]!.val = .flowMappingStart) →
    ∃ j, k + 1 < j ∧ j < hi ∧
      ((tokens[k+1]!.val = .flowSequenceStart ∧ tokens[j]!.val = .flowSequenceEnd) ∨
       (tokens[k+1]!.val = .flowMappingStart ∧ tokens[j]!.val = .flowMappingEnd)) ∧
      flowBracketBalance tokens (k+2) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowMappingEnd ∧ j + 1 = hi))
  /-- M9: Bracket matching for flowSeqStart at depth 0 (needed for inner body IH). -/
  bracket_seq : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowSequenceStart →
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowSequenceEnd ∧
      flowBracketBalance tokens (k+1) j = 0
  /-- M10: Bracket matching for flowMapStart at depth 0. -/
  bracket_map : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowMappingStart →
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowMappingEnd ∧
      flowBracketBalance tokens (k+1) j = 0

/-- Universal structural properties: all valid flow body subranges
    in the token array satisfy `SeqBodyProps` (for seq bodies) or
    `MapBodyProps` (for map bodies). -/
structure FlowSubrangesOk (tokens : Array (Positioned YamlToken)) : Prop where
  seq : ∀ lo hi, lo ≤ hi → hi < tokens.size →
    tokens[hi]!.val = .flowSequenceEnd →
    flowBracketBalance tokens lo hi = 0 →
    SeqBodyProps tokens lo hi
  map : ∀ lo hi, lo ≤ hi → hi < tokens.size →
    tokens[hi]!.val = .flowMappingEnd →
    flowBracketBalance tokens lo hi = 0 →
    MapBodyProps tokens lo hi

end L4YAML.Proofs.ParserGrammable
