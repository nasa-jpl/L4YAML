module

public import L4YAML.Spec.Grammar
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Production.ScannerPlainScalarValid
public import L4YAML.Proofs.Composition

@[expose] public section Blanket

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
lemma ScalarScannable_eq_of_content_style_eq
    (c : String) (st : ScalarStyle)
    (t1 t2 : Option String) (a1 a2 : Option String)
    (b1 b2 : Option BlockScalarMeta) (inFlow : Bool) :
    ScalarScannable ⟨c, st, t1, a1, b1⟩ inFlow ↔
      ScalarScannable ⟨c, st, t2, a2, b2⟩ inFlow := by
  constructor <;> (intro h hplain hlen; exact h hplain hlen)

/-- Clearing the anchor field preserves `ScalarScannable`. -/
lemma ScalarScannable_strip_anchor (s : Scalar) (inFlow : Bool) :
    ScalarScannable s inFlow ↔
      ScalarScannable { s with anchor := none } inFlow := by
  constructor <;> (intro h hplain hlen; exact h hplain hlen)

/-- Non-plain scalars trivially satisfy `ScalarScannable`. -/
lemma ScalarScannable_of_nonplain (s : Scalar) (inFlow : Bool)
    (h : s.style ≠ .plain) :
    ScalarScannable s inFlow :=
  fun hplain _ => absurd hplain h

/-! ## §2  `stripAnchors` Preserves `Grammable`

`YamlValue.stripAnchors` only clears anchor fields. Since `Grammable`
does not constrain anchor fields and `ScalarScannable` is metadata-
independent, `Grammable` is preserved.
-/

/-- `stripAnchors` on a `.scalar` node preserves `Grammable`. -/
lemma stripAnchors_scalar_grammable (s : Scalar) (inFlow : Bool)
    (h : Grammable (.scalar s) inFlow) :
    Grammable (.scalar { s with anchor := none }) inFlow := by
  cases h with
  | scalar _ _ h_ss =>
    exact .scalar { s with anchor := none } inFlow
      ((ScalarScannable_strip_anchor s inFlow).mp h_ss)

/-- The `stripList` where-clause helper equals `List.map stripAnchors`. -/
lemma stripList_eq_map (l : List YamlValue) :
    YamlValue.stripAnchors.stripList l = l.map YamlValue.stripAnchors := by
  induction l with
  | nil => simp [YamlValue.stripAnchors.stripList]
  | cons v vs ih => simp [YamlValue.stripAnchors.stripList, ih]

/-- The `stripPairs` where-clause helper equals `List.map` over pairs. -/
lemma stripPairs_eq_map (l : List (YamlValue × YamlValue)) :
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
lemma stripAnchors_preserves_Grammable (v : YamlValue) (inFlow : Bool) :
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
lemma Scannable_aliasFree_to_Grammable (v : YamlValue) (inFlow : Bool) :
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

/-- `name` is BOUND in an anchor table: the leaf condition
    `AllAliasesResolve` imposes, named so that both readings of the obligation
    can be stated against it. -/
def AnchorBound (anchors : Array (String × YamlValue)) (name : String) : Prop :=
  (anchors.findSome? (fun (n, _) => if n == name then some () else none)).isSome

/-- Being bound survives anchor growth: a table that embeds another answers
    every lookup the smaller one answered. -/
lemma AnchorBound.mono {a1 a2 : Array (String × YamlValue)} {name : String}
    (h_emb : ∀ i : Fin a1.size, ∃ j : Fin a2.size, a2[j] = a1[i])
    (h : AnchorBound a1 name) : AnchorBound a2 name := by
  unfold AnchorBound at h ⊢
  rw [Array.findSome?_isSome_iff] at h ⊢
  obtain ⟨x, hx, hfx⟩ := h
  rw [Array.mem_iff_getElem] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  obtain ⟨j, hj⟩ := h_emb ⟨i, hi⟩
  exact ⟨a2[j], Array.getElem_mem j.isLt, hj ▸ hfx⟩

/-- The name an anchor table was just extended with is bound in it. -/
lemma AnchorBound.push_self (anchors : Array (String × YamlValue)) (name : String)
    (v : YamlValue) : AnchorBound (anchors.push (name, v)) name := by
  unfold AnchorBound
  rw [Array.findSome?_isSome_iff]
  exact ⟨(name, v), Array.mem_push.mpr (Or.inr rfl), by simp⟩

/-- **§7.1's reading of the same obligation**: every alias node in a value names
    an anchor that has *previously occurred*.

    The index is the DECLARATION set — the names a `&` node property has
    introduced — rather than the resolution table, and the two differ exactly
    where a node has itself as a descendant: a collection's anchor occurs at its
    start event (§3.2.2.2) while its entry in the resolution table exists only
    once its items are complete, because that entry stores a value.  `&x [*x]`
    is that case, and §7.1's only error is an anchor that does not previously
    OCCUR.

    This is the predicate the parser's own guard decides, and it is the reading
    that holds per NODE.  `AllAliasesResolve.of_declared` upgrades it to the
    resolution reading wherever the declared names are known to be bound, which
    is what a document boundary supplies. -/
inductive AllAliasesDeclared : YamlValue → Array String → Prop where
  | scalar (s : Scalar) (names : Array String) :
      AllAliasesDeclared (.scalar s) names
  | alias (name : String) (names : Array String) (h : name ∈ names) :
      AllAliasesDeclared (.alias name) names
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String) (names : Array String)
      (h : ∀ i : Fin items.size, AllAliasesDeclared items[i] names) :
      AllAliasesDeclared (.sequence style items tag anchor) names
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String) (names : Array String)
      (hk : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].1 names)
      (hv : ∀ i : Fin pairs.size, AllAliasesDeclared pairs[i].2 names) :
      AllAliasesDeclared (.mapping style pairs tag anchor) names

/-- The declaration set only grows, and the §7.1 reading only weakens as it
    does. -/
lemma AllAliasesDeclared.mono {v : YamlValue} {d1 d2 : Array String}
    (h_sub : ∀ nm, nm ∈ d1 → nm ∈ d2) (h : AllAliasesDeclared v d1) :
    AllAliasesDeclared v d2 := by
  induction h with
  | scalar s _ => exact .scalar s _
  | alias name _ h_mem => exact .alias name _ (h_sub name h_mem)
  | sequence style items tag anchor _ _ ih =>
    exact .sequence style items tag anchor _ (fun i => ih i h_sub)
  | mapping style pairs tag anchor _ _ _ ihk ihv =>
    exact .mapping style pairs tag anchor _ (fun i => ihk i h_sub) (fun i => ihv i h_sub)

/-- **The bridge between the two readings of the alias obligation.**

    The §7.1 reading is about occurrence and the resolution reading is about
    binding, so one upgrades to the other exactly when every declared name is
    bound.  That is false inside a node — a collection's own anchor is declared
    and not yet bound while its items are parsed — and true at a document
    boundary, where the parser has finalized every node it declared an anchor
    for.  The capstones use it there. -/
lemma AllAliasesResolve.of_declared {v : YamlValue} {names : Array String}
    {anchors : Array (String × YamlValue)}
    (h_bound : ∀ nm, nm ∈ names → AnchorBound anchors nm)
    (h : AllAliasesDeclared v names) :
    AllAliasesResolve v anchors := by
  induction h with
  | scalar s _ => exact .scalar s _
  | alias name _ h_mem => exact .alias name _ (h_bound name h_mem)
  | sequence style items tag anchor _ _ ih =>
    exact .sequence style items tag anchor _ (fun i => ih i h_bound)
  | mapping style pairs tag anchor _ _ _ ihk ihv =>
    exact .mapping style pairs tag anchor _ (fun i => ihk i h_bound) (fun i => ihv i h_bound)

/-- The parser's §7.1 guard is `Array.any` over the declaration set and
    `AllAliasesDeclared` is membership in it; this is the one step between
    them. -/
lemma mem_of_any_beq {names : Array String} {name : String}
    (h : names.any (fun n => n == name) = true) : name ∈ names := by
  rw [Array.any_eq_true] at h
  obtain ⟨i, hi, hp⟩ := h
  have h_eq : names[i] = name := by simpa using hp
  exact h_eq ▸ Array.getElem_mem hi

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
lemma hasFlowIndicator_false_noFlowIndicators (content : String)
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
lemma ScalarScannable_false_to_true_noFI (s : Scalar)
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
        exact ⟨hvpf.1, hvpf.2.1, fun _ => h_nfi n h_n_mem,
               hvpf.2.2.2.1, hvpf.2.2.2.2⟩
      · contradiction
    · -- Non-exception branch in hvpf: identical for both inFlow values
      split
      · contradiction
      · exact hvpf

/-- The `adaptList` where-clause helper equals `List.map adaptForFlowContext`. -/
lemma adaptList_eq_map (l : List YamlValue) :
    YamlValue.adaptForFlowContext.adaptList l =
      l.map YamlValue.adaptForFlowContext := by
  induction l with
  | nil => simp [YamlValue.adaptForFlowContext.adaptList]
  | cons v vs ih => simp [YamlValue.adaptForFlowContext.adaptList, ih]

/-- The `adaptPairs` where-clause helper equals `List.map` over pairs. -/
lemma adaptPairs_eq_map (l : List (YamlValue × YamlValue)) :
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
lemma adaptForFlowContext_grammable_forall (v : YamlValue) (b : Bool)
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
lemma findSome_unit_to_val (arr : Array (String × YamlValue)) (name : String)
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
lemma resolveList_eq_map (l : List YamlValue) (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliases.resolveList l anchors =
      l.map (fun v => v.resolveAliases anchors) := by
  induction l with
  | nil => simp [YamlValue.resolveAliases.resolveList]
  | cons v vs ih => simp [YamlValue.resolveAliases.resolveList, ih]

/-- The `resolvePairs` where-clause helper equals `List.map` over pairs. -/
lemma resolvePairs_eq_map (l : List (YamlValue × YamlValue))
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
lemma compose_value_grammable
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

/-! ### Order-aware compose grammability (J2)

`YamlDocument.compose` resolves aliases with `resolveAliasesOrdered` — each
alias binds to the most recent *preceding* definition of its anchor name
(§7.1) — so the C1 grammability bridge must thread the binding environment
the walk accumulates.  The induction below carries a JOINT conclusion (the
resolved value is grammable AND the threaded environment stays well-formed):
bindings made inside an earlier sibling are consumed by later siblings, so
neither conjunct is provable alone. -/

/-- `stripAnchors` is idempotent. -/
lemma stripAnchors_stripAnchors (v : YamlValue) :
    v.stripAnchors.stripAnchors = v.stripAnchors := by
  match v with
  | .scalar s => rfl
  | .alias _ => rfl
  | .sequence style items tag anchor =>
    simp only [YamlValue.stripAnchors]
    simp only [YamlValue.sequence.injEq, true_and, and_true]
    rw [stripList_eq_map, List.toList_toArray, stripList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun x hx => stripAnchors_stripAnchors x)
  | .mapping style pairs tag anchor =>
    simp only [YamlValue.stripAnchors]
    simp only [YamlValue.mapping.injEq, true_and, and_true]
    rw [stripPairs_eq_map, List.toList_toArray, stripPairs_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun ⟨k, w⟩ hkw =>
      Prod.ext (stripAnchors_stripAnchors k) (stripAnchors_stripAnchors w))
termination_by v
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem hx
    cases items; simp_all [Array.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hkw
    cases pairs; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hkw
    cases pairs; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega

/-- `stripAnchors` commutes with `adaptForFlowContext`: adaptation only
    restyles scalars (the adapt condition reads `style`/`content`, which
    stripping never touches), and stripping only clears anchor fields
    (which adaptation never touches). -/
lemma adaptForFlowContext_stripAnchors (v : YamlValue) :
    v.adaptForFlowContext.stripAnchors = v.stripAnchors.adaptForFlowContext := by
  match v with
  | .scalar s =>
    simp only [YamlValue.adaptForFlowContext, YamlValue.stripAnchors]
    split <;> simp only [YamlValue.stripAnchors] <;> split <;> simp_all
  | .alias _ => rfl
  | .sequence style items tag anchor =>
    simp only [YamlValue.adaptForFlowContext, YamlValue.stripAnchors]
    simp only [YamlValue.sequence.injEq, true_and, and_true]
    rw [adaptList_eq_map, List.toList_toArray, stripList_eq_map, List.map_map,
        stripList_eq_map, List.toList_toArray, adaptList_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun x hx => adaptForFlowContext_stripAnchors x)
  | .mapping style pairs tag anchor =>
    simp only [YamlValue.adaptForFlowContext, YamlValue.stripAnchors]
    simp only [YamlValue.mapping.injEq, true_and, and_true]
    rw [adaptPairs_eq_map, List.toList_toArray, stripPairs_eq_map, List.map_map,
        stripPairs_eq_map, List.toList_toArray, adaptPairs_eq_map, List.map_map]
    congr 1
    exact List.map_congr_left (fun ⟨k, w⟩ hkw =>
      Prod.ext (adaptForFlowContext_stripAnchors k) (adaptForFlowContext_stripAnchors w))
termination_by v
decreasing_by
  all_goals simp_wf
  · have := List.sizeOf_lt_of_mem hx
    cases items; simp_all [Array.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hkw
    cases pairs; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega
  · have := List.sizeOf_lt_of_mem hkw
    cases pairs; simp_all [Array.mk.sizeOf_spec, Prod.mk.sizeOf_spec]; omega

/-- Environment bindings are well-formed: after stripping, bound values are
    `Grammable` at every flow context.  The `List` counterpart of
    `WellFormedAnchors`, for the environment `resolveAliasesOrdered` threads. -/
def WellFormedEnv (env : List (String × YamlValue)) : Prop :=
  ∀ (name : String) (val : YamlValue),
    env.findSome? (fun (n, v) => if n == name then some v else none) = some val →
      ∀ inFlow, Grammable val.stripAnchors inFlow

/-- The empty environment is well-formed. -/
lemma wellFormedEnv_nil : WellFormedEnv [] := fun _ _ h => nomatch h

/-- Extending a well-formed environment with a binding whose value is
    universally grammable after stripping preserves well-formedness. -/
lemma WellFormedEnv.cons {env : List (String × YamlValue)}
    (h_env : WellFormedEnv env) (a : String) (val : YamlValue)
    (h_val : ∀ inFlow, Grammable val.stripAnchors inFlow) :
    WellFormedEnv ((a, val) :: env) := by
  intro name w h_find inFlow
  simp only [List.findSome?_cons] at h_find
  cases hcond : (a == name) with
  | true =>
    simp only [hcond] at h_find
    cases h_find
    exact h_val inFlow
  | false =>
    simp only [hcond] at h_find
    exact h_env name w h_find inFlow

/-- Joint contract for `goList`: threading over a list whose every element
    satisfies the element-level (grammable ∧ well-formed-env) contract keeps
    every resolved element grammable after stripping and the final
    environment well-formed. -/
lemma goList_grammable_ordered
    (anchors : Array (String × YamlValue)) (ctx : Bool)
    (l : List YamlValue)
    (H : ∀ v ∈ l, ∀ env, WellFormedEnv env →
      Grammable ((v.resolveAliasesOrdered anchors env).fst).stripAnchors ctx ∧
      WellFormedEnv (v.resolveAliasesOrdered anchors env).snd) :
    ∀ env, WellFormedEnv env →
      (∀ w ∈ (YamlValue.resolveAliasesOrdered.goList anchors l env).fst,
        Grammable w.stripAnchors ctx) ∧
      WellFormedEnv (YamlValue.resolveAliasesOrdered.goList anchors l env).snd := by
  induction l with
  | nil =>
    intro env h_env
    simp only [YamlValue.resolveAliasesOrdered.goList]
    exact ⟨(fun w hw => nomatch hw), h_env⟩
  | cons v vs ih =>
    intro env h_env
    have hv := H v List.mem_cons_self env h_env
    have hrest := ih (fun w hw => H w (List.mem_cons_of_mem _ hw))
      ((v.resolveAliasesOrdered anchors env).snd) hv.2
    simp only [YamlValue.resolveAliasesOrdered.goList]
    refine ⟨fun w hw => ?_, hrest.2⟩
    rcases List.mem_cons.mp hw with h_eq | h_mem
    · exact h_eq ▸ hv.1
    · exact hrest.1 w h_mem

/-- Joint contract for `goPairs`: the key/value analog of
    `goList_grammable_ordered` (key resolved before value before the rest,
    each step re-arming the environment invariant). -/
lemma goPairs_grammable_ordered
    (anchors : Array (String × YamlValue)) (ctx : Bool)
    (l : List (YamlValue × YamlValue))
    (Hk : ∀ p ∈ l, ∀ env, WellFormedEnv env →
      Grammable ((p.1.resolveAliasesOrdered anchors env).fst).stripAnchors ctx ∧
      WellFormedEnv (p.1.resolveAliasesOrdered anchors env).snd)
    (Hv : ∀ p ∈ l, ∀ env, WellFormedEnv env →
      Grammable ((p.2.resolveAliasesOrdered anchors env).fst).stripAnchors ctx ∧
      WellFormedEnv (p.2.resolveAliasesOrdered anchors env).snd) :
    ∀ env, WellFormedEnv env →
      (∀ q ∈ (YamlValue.resolveAliasesOrdered.goPairs anchors l env).fst,
        Grammable q.1.stripAnchors ctx ∧ Grammable q.2.stripAnchors ctx) ∧
      WellFormedEnv (YamlValue.resolveAliasesOrdered.goPairs anchors l env).snd := by
  induction l with
  | nil =>
    intro env h_env
    simp only [YamlValue.resolveAliasesOrdered.goPairs]
    exact ⟨(fun q hq => nomatch hq), h_env⟩
  | cons p rest ih =>
    intro env h_env
    obtain ⟨k, v⟩ := p
    have hk := Hk (k, v) List.mem_cons_self env h_env
    have hv := Hv (k, v) List.mem_cons_self
      ((k.resolveAliasesOrdered anchors env).snd) hk.2
    have hrest := ih (fun q hq => Hk q (List.mem_cons_of_mem _ hq))
      (fun q hq => Hv q (List.mem_cons_of_mem _ hq))
      ((v.resolveAliasesOrdered anchors (k.resolveAliasesOrdered anchors env).snd).snd) hv.2
    simp only [YamlValue.resolveAliasesOrdered.goPairs]
    refine ⟨fun q hq => ?_, hrest.2⟩
    rcases List.mem_cons.mp hq with h_eq | h_mem
    · exact h_eq ▸ ⟨hk.1, hv.1⟩
    · exact hrest.1 q h_mem

/-! ### Order-aware compose grammability, via the alias-free identity

`YamlDocument.compose` resolves with `resolveAliasesOrdered`, which substitutes
only at an alias node (§3.2.2.2 resolves against the ordered environment and
nothing else).  On a tree with no alias node there is therefore nothing to
substitute, and the walk rebuilds each node from its own resolved children —
so it is the identity on values.  That turns compose-grammability into
`Scannable_aliasFree_to_Grammable` composed with `stripAnchors_preserves_Grammable`,
and no induction over the resolver is needed.
-/

/-- The list-level half of the identity below. -/
lemma goList_fst_of_aliasFree (anchors : Array (String × YamlValue))
    (l : List YamlValue)
    (H : ∀ w ∈ l, ∀ env, (w.resolveAliasesOrdered anchors env).fst = w) :
    ∀ env, (YamlValue.resolveAliasesOrdered.goList anchors l env).fst = l := by
  induction l with
  | nil => intro env; rfl
  | cons w ws ih =>
    intro env
    have hw := H w (List.mem_cons_self ..)
    have hws := ih (fun x hx => H x (List.mem_cons_of_mem _ hx))
    simp only [YamlValue.resolveAliasesOrdered.goList, hw env,
      hws (w.resolveAliasesOrdered anchors env).snd]

/-- The pair-level half. -/
lemma goPairs_fst_of_aliasFree (anchors : Array (String × YamlValue))
    (l : List (YamlValue × YamlValue))
    (Hk : ∀ p ∈ l, ∀ env, (p.1.resolveAliasesOrdered anchors env).fst = p.1)
    (Hv : ∀ p ∈ l, ∀ env, (p.2.resolveAliasesOrdered anchors env).fst = p.2) :
    ∀ env, (YamlValue.resolveAliasesOrdered.goPairs anchors l env).fst = l := by
  induction l with
  | nil => intro env; rfl
  | cons p ps ih =>
    intro env
    have hk := Hk p (List.mem_cons_self ..)
    have hv := Hv p (List.mem_cons_self ..)
    have hrest := ih (fun x hx => Hk x (List.mem_cons_of_mem _ hx))
                     (fun x hx => Hv x (List.mem_cons_of_mem _ hx))
    simp only [YamlValue.resolveAliasesOrdered.goPairs, hk env,
      hv (p.1.resolveAliasesOrdered anchors env).snd,
      hrest (p.2.resolveAliasesOrdered anchors
        (p.1.resolveAliasesOrdered anchors env).snd).snd]

/-- **On an alias-free tree the order-aware walk is the identity on values.**
    §3.2.2.2 substitutes only at an alias node, and there is none. -/
lemma resolveAliasesOrdered_fst_of_aliasFree (v : YamlValue) (h_af : AliasFree v)
    (anchors : Array (String × YamlValue)) :
    ∀ env, (v.resolveAliasesOrdered anchors env).fst = v := by
  induction h_af with
  | scalar s => intro env; rfl
  | sequence style items tag anchor h ih =>
    intro env
    have H : ∀ w ∈ items.toList, ∀ env', (w.resolveAliasesOrdered anchors env').fst = w := by
      intro w hw
      obtain ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
      have hi' : i < items.size := by rwa [Array.length_toList] at hi
      have h_w : w = items[i] := by rw [← h_eq, Array.getElem_toList]
      subst h_w; exact ih ⟨i, hi'⟩
    simp only [YamlValue.resolveAliasesOrdered,
      goList_fst_of_aliasFree anchors items.toList H env, Array.toArray_toList]
  | mapping style pairs tag anchor hk hv ihk ihv =>
    intro env
    have mem : ∀ p ∈ pairs.toList, ∃ i : Fin pairs.size, p = pairs[i.val] := by
      intro p hp
      obtain ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have hi' : i < pairs.size := by rwa [Array.length_toList] at hi
      exact ⟨⟨i, hi'⟩, by rw [← h_eq, Array.getElem_toList]⟩
    have Hk : ∀ p ∈ pairs.toList, ∀ env', (p.1.resolveAliasesOrdered anchors env').fst = p.1 := by
      intro p hp; obtain ⟨i, rfl⟩ := mem p hp; exact ihk i
    have Hv : ∀ p ∈ pairs.toList, ∀ env', (p.2.resolveAliasesOrdered anchors env').fst = p.2 := by
      intro p hp; obtain ⟨i, rfl⟩ := mem p hp; exact ihv i
    simp only [YamlValue.resolveAliasesOrdered,
      goPairs_fst_of_aliasFree anchors pairs.toList Hk Hv env, Array.toArray_toList]

/-- C1 applied to `YamlDocument.compose`: an alias-free `Scannable` document
    value composes to a `Grammable` one.  `compose` is
    `(resolveAliasesOrdered …).fst.stripAnchors`, the walk is the identity here,
    and the two bridges close the rest. -/
lemma compose_grammable (doc : YamlDocument)
    (h_scan : Scannable doc.value false)
    (h_af : AliasFree doc.value) :
    Grammable doc.compose.value false := by
  show Grammable ((doc.value.resolveAliasesOrdered doc.anchors []).fst).stripAnchors false
  rw [resolveAliasesOrdered_fst_of_aliasFree doc.value h_af doc.anchors []]
  exact stripAnchors_preserves_Grammable _ false
    (Scannable_aliasFree_to_Grammable doc.value false h_scan h_af)

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
lemma foldl_add_shift {α : Type _} (l : List α) (f : α → Int) (init : Int) :
    l.foldl (fun acc t => acc + f t) init = init + l.foldl (fun acc t => acc + f t) 0 := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl]
    rw [ih, ih (0 + f hd)]
    omega

/-- Bracket balance composition: splitting a range at a midpoint yields additive
    balance values. -/
lemma flowBracketBalance_compose (tokens : Array (Positioned YamlToken))
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
lemma flowBracketBalance_push (tokens : Array (Positioned YamlToken))
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
lemma flowBracketBalance_single (tokens : Array (Positioned YamlToken))
    (i : Nat) (h : i < tokens.toList.length) :
    flowBracketBalance tokens i (i + 1) = flowBracketDelta tokens.toList[i].val := by
  simp only [flowBracketBalance, show ¬(i ≥ i + 1) from by omega, ↓reduceIte,
             show i + 1 - i = 1 from by omega]
  rw [List.drop_eq_getElem_cons h]
  simp [List.foldl]

/-- Composing a zero-balance prefix, a single non-bracket token, and a zero-balance suffix
    yields zero total balance. Used for flowEntry + parseNode compositions. -/
lemma flowBracketBalance_compose_zero (tokens : Array (Positioned YamlToken))
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

/-- The bracket delta of any token is at least `-1` (only the two close brackets
    contribute `-1`; everything else is `0` or `+1`). -/
lemma flowBracketDelta_ge_neg_one (t : YamlToken) : -1 ≤ flowBracketDelta t := by
  unfold flowBracketDelta
  split <;> decide

/-- The bracket delta of any token is at most `+1` (only the two open brackets
    contribute `+1`; everything else is `0` or `-1`). The upper companion of
    `flowBracketDelta_ge_neg_one`: together they pin every delta to `{-1, 0, 1}`, which the
    backward opener locator needs to classify the scanned token as opener/neutral/closer. -/
lemma flowBracketDelta_le_one (t : YamlToken) : flowBracketDelta t ≤ 1 := by
  unfold flowBracketDelta
  split <;> decide

/-- **Bracket-matching locator (Dyck).**  In a flow range `[lo, hi)` that is
    *well-bracketed* — total balance `0` and every prefix balance `≥ 0` — a depth-0
    open bracket at position `k` (balance `lo..k = 0`, `tokens[k]` an opener) has a
    matching close at some `j` with `k < j < hi`, `tokens[j]` a closer, and the
    enclosed body `(k+1, j)` itself balanced.

    This is the pure-combinatorial core every nested-bracket conjunct of
    `SeqBodyProps`/`MapBodyProps` rests on: it converts the flat Dyck condition the
    emitter stream satisfies (`WellBracketed`) into the matching-bracket structure
    `flow_parser_ok_of_structure` consumes by span induction.  The *which* bracket
    (`]` vs `}`) and the successor token are emitter facts layered on top; this lemma
    supplies the position `j` and the inner balance.

    No Mathlib, so the "first return to balance 0 after `k`" is found by an explicit
    fuel scan (`find`) rather than `Nat.find`. -/
lemma flowBracketBalance_matching_close (tokens : Array (Positioned YamlToken))
    (lo k hi : Nat) (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : flowBracketDelta tokens[k]!.val = 1)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) :
    ∃ j, k < j ∧ j < hi ∧
      flowBracketDelta tokens[j]!.val = -1 ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      (∀ i, k < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) := by
  -- One-step recurrence for the running balance.
  have step : ∀ i, lo ≤ i → i < tokens.size →
      flowBracketBalance tokens lo (i+1) =
        flowBracketBalance tokens lo i + flowBracketDelta tokens[i]!.val := by
    intro i h_lo_i h_sz
    rw [flowBracketBalance_compose tokens lo i (i+1) h_lo_i (by omega)]
    have hlen : i < tokens.toList.length := by rw [Array.length_toList]; exact h_sz
    rw [flowBracketBalance_single tokens i hlen]
    have h1 : tokens.toList[i]'hlen = tokens[i] := Array.getElem_toList h_sz
    have h2 : tokens[i] = tokens[i]! := (getElem!_pos tokens i h_sz).symm
    rw [h1, h2]
  -- Balance just after the opener is 1.
  have h_f_k1 : flowBracketBalance tokens lo (k+1) = 1 := by
    have hs := step k h_lo_k (by omega)
    rw [h_k_depth, h_k_open] at hs; omega
  -- Scan forward from `start` (kept at depth `≥ 1`) for the first return to 0.
  -- `find` threads the running invariant `∀ i ∈ (k, start], balance lo i ≥ 1`
  -- (the depth never drops below 1 anywhere strictly between the opener and the
  -- first return to 0), and hands it back for the whole interior `(k, j]`.
  have find : ∀ (f start : Nat), start + f = hi → k < start →
      flowBracketBalance tokens lo start ≥ 1 →
      (∀ i, k < i → i ≤ start → flowBracketBalance tokens lo i ≥ 1) →
      ∃ j, k < j ∧ j < hi ∧
        flowBracketDelta tokens[j]!.val = -1 ∧
        flowBracketBalance tokens (k+1) j = 0 ∧
        (∀ i, k < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) := by
    intro f
    induction f with
    | zero =>
      intro start h_sf h_ks h_bal _
      have h_eq : start = hi := by omega
      rw [h_eq, h_total] at h_bal; omega
    | succ f ih =>
      intro start h_sf h_ks h_bal hinv
      have h_start_lt : start < hi := by omega
      have h_start_sz : start < tokens.size := by omega
      have hs := step start (by omega) h_start_sz
      by_cases h0 : flowBracketBalance tokens lo (start+1) = 0
      · -- `start` is the matching close; `j = start` and `hinv` is the interior invariant.
        rw [h0] at hs
        have h_delta_ge := flowBracketDelta_ge_neg_one tokens[start]!.val
        have h_bs1 : flowBracketBalance tokens lo start = 1 := by omega
        have h_d : flowBracketDelta tokens[start]!.val = -1 := by omega
        refine ⟨start, h_ks, h_start_lt, h_d, ?_, hinv⟩
        have hcomp := flowBracketBalance_compose tokens lo (k+1) start (by omega) (by omega)
        rw [h_bs1, h_f_k1] at hcomp; omega
      · -- Still inside the bracket: recurse one step further, extending the invariant to `start+1`.
        have h_next_ge1 : flowBracketBalance tokens lo (start+1) ≥ 1 := by
          have h_ge0 := h_dyck (start+1) (by omega) (by omega)
          omega
        refine ih (start+1) (by omega) (by omega) h_next_ge1 ?_
        intro i h_ki h_i_s1
        rcases Nat.lt_or_ge i (start+1) with h | h
        · exact hinv i h_ki (by omega)
        · have : i = start + 1 := by omega
          rw [this]; exact h_next_ge1
  exact find (hi - (k+1)) (k+1) (by omega) (by omega) (by omega)
    (by
      intro i h_ki h_i
      have hi_eq : i = k + 1 := by omega
      have : flowBracketBalance tokens lo i = 1 := hi_eq ▸ h_f_k1
      omega)

/-- **Matching close of a NESTED opener (depth-general)** — R482.  Generalizes
    `flowBracketBalance_matching_close` from a DEPTH-0 opener (`flowBracketBalance tokens lo k = 0`)
    to an opener `k` at ARBITRARY depth `d = flowBracketBalance tokens lo k ≥ 0` inside the balanced,
    Dyck-floored window `[lo, hi)`.  The `h_k_depth : balance lo k = 0` hypothesis is DROPPED; the
    located close `j` and the interior floor are stated RELATIVE TO the opener
    (`flowBracketBalance tokens (k+1) j = 0`, `flowBracketBalance tokens (k+1) i ≥ 0`), so the
    statement is itself depth-free.

    **Why this is the missing primitive (R482 discovery).**  The seq carrier
    `seqLocalCarrier_of_widthEnc` locates, at every gated window `[a, b)`, its INNERMOST enclosing
    opener `p` (`seqEnclosingOpener_of_gate`) and asks `enclosingLocate`/`h_widthEnc` for `p`'s full
    bracket span `[p, hiE)`.  For a DEEPLY-NESTED gated window the innermost encloser `p` sits at depth
    ≥ 1 in the body window, so `seqClose_of_located_and_enclosing_within`'s `h_p_depth : balance lo p =
    0` (and `flowBracketBalance_matching_close_seq`'s `h_k_depth`) is FALSE — the depth-0 close locator
    cannot find a nested opener's close.  This is the depth-general BALANCE core that unblocks it: the
    matching-close scan is purely RELATIVE to the opener's own depth, so threading the interior floor
    against `flowBracketBalance tokens lo k` (rather than the literal `0`) generalizes the proof
    mechanically — the return level becomes `balance lo k`, the just-after-opener level
    `balance lo k + 1`, and the global Dyck floor `≥ 0` is now needed ONLY to pin the opener's own
    depth `d ≥ 0` (the recurse step uses the threaded interior invariant, not the global floor).

    Verified-but-unconsumed until the typed seq/map close locators are re-based onto it; references no
    sorry site, frontier sorry count unchanged at 4; axiom-clean. -/
lemma flowBracketBalance_matching_close_nested (tokens : Array (Positioned YamlToken))
    (lo k hi : Nat) (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_open : flowBracketDelta tokens[k]!.val = 1)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) :
    ∃ j, k < j ∧ j < hi ∧
      flowBracketDelta tokens[j]!.val = -1 ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      (∀ i, k < i → i ≤ j → flowBracketBalance tokens (k+1) i ≥ 0) := by
  -- The opener's own depth is `≥ 0` (it is a position of the Dyck-floored window).
  have h_d_ge : flowBracketBalance tokens lo k ≥ 0 := h_dyck k h_lo_k (by omega)
  -- One-step recurrence for the running balance.
  have step : ∀ i, lo ≤ i → i < tokens.size →
      flowBracketBalance tokens lo (i+1) =
        flowBracketBalance tokens lo i + flowBracketDelta tokens[i]!.val := by
    intro i h_lo_i h_sz
    rw [flowBracketBalance_compose tokens lo i (i+1) h_lo_i (by omega)]
    have hlen : i < tokens.toList.length := by rw [Array.length_toList]; exact h_sz
    rw [flowBracketBalance_single tokens i hlen]
    have h1 : tokens.toList[i]'hlen = tokens[i] := Array.getElem_toList h_sz
    have h2 : tokens[i] = tokens[i]! := (getElem!_pos tokens i h_sz).symm
    rw [h1, h2]
  -- Balance just after the opener is one ABOVE the opener's own depth.
  have h_f_k1 : flowBracketBalance tokens lo (k+1) = flowBracketBalance tokens lo k + 1 := by
    have hs := step k h_lo_k (by omega)
    rw [h_k_open] at hs; omega
  -- Scan forward from `start` (kept STRICTLY above the opener's depth) for the first RETURN to it.
  -- The threaded invariant `∀ i ∈ (k, start], balance lo i ≥ balance lo k + 1` (the depth never drops
  -- back to the opener's level strictly inside) is handed back for the whole interior `(k, j]`.
  have find : ∀ (f start : Nat), start + f = hi → k < start →
      flowBracketBalance tokens lo start ≥ flowBracketBalance tokens lo k + 1 →
      (∀ i, k < i → i ≤ start →
        flowBracketBalance tokens lo i ≥ flowBracketBalance tokens lo k + 1) →
      ∃ j, k < j ∧ j < hi ∧
        flowBracketDelta tokens[j]!.val = -1 ∧
        flowBracketBalance tokens (k+1) j = 0 ∧
        (∀ i, k < i → i ≤ j →
          flowBracketBalance tokens lo i ≥ flowBracketBalance tokens lo k + 1) := by
    intro f
    induction f with
    | zero =>
      intro start h_sf h_ks h_bal _
      have h_eq : start = hi := by omega
      rw [h_eq, h_total] at h_bal; omega
    | succ f ih =>
      intro start h_sf h_ks h_bal hinv
      have h_start_lt : start < hi := by omega
      have h_start_sz : start < tokens.size := by omega
      have hs := step start (by omega) h_start_sz
      by_cases h0 : flowBracketBalance tokens lo (start+1) = flowBracketBalance tokens lo k
      · -- `start` is the matching close; `j = start`, and `hinv` is the interior floor.
        rw [h0] at hs
        have h_delta_ge := flowBracketDelta_ge_neg_one tokens[start]!.val
        have h_bs1 : flowBracketBalance tokens lo start = flowBracketBalance tokens lo k + 1 := by omega
        have h_d : flowBracketDelta tokens[start]!.val = -1 := by omega
        refine ⟨start, h_ks, h_start_lt, h_d, ?_, hinv⟩
        have hcomp := flowBracketBalance_compose tokens lo (k+1) start (by omega) (by omega)
        rw [h_bs1, h_f_k1] at hcomp; omega
      · -- Still inside the bracket: recurse, extending the interior floor to `start+1`.
        have h_next_ge1 :
            flowBracketBalance tokens lo (start+1) ≥ flowBracketBalance tokens lo k + 1 := by
          have h_delta_ge := flowBracketDelta_ge_neg_one tokens[start]!.val
          omega
        refine ih (start+1) (by omega) (by omega) h_next_ge1 ?_
        intro i h_ki h_i_s1
        rcases Nat.lt_or_ge i (start+1) with h | h
        · exact hinv i h_ki (by omega)
        · have : i = start + 1 := by omega
          rw [this]; exact h_next_ge1
  obtain ⟨j, hkj, hjhi, hjdelta, hinner, hfloor_abs⟩ :=
    find (hi - (k+1)) (k+1) (by omega) (by omega) (by omega)
      (by
        intro i h_ki h_i
        have hi_eq : i = k + 1 := by omega
        have hb : flowBracketBalance tokens lo i = flowBracketBalance tokens lo k + 1 := hi_eq ▸ h_f_k1
        omega)
  -- Re-base the absolute interior floor `balance lo i ≥ balance lo k + 1` onto the opener
  -- (`balance (k+1) i ≥ 0`), the depth-free form the child-bracket constructors consume.
  refine ⟨j, hkj, hjhi, hjdelta, hinner, ?_⟩
  intro i h_ki h_ij
  have hcomp := flowBracketBalance_compose tokens lo (k+1) i (by omega) (by omega)
  have hf := hfloor_abs i h_ki h_ij
  rw [h_f_k1] at hcomp
  omega

/-- **Dyck origin shift (local Dyck of a depth-floor subrange).**  The local Dyck of a subrange
    `[s, hi)` whose start `s` is a *depth-floor* — the running balance from `lo` never drops below
    its value `d` at `s` — is exactly the global Dyck re-based at `s`.  By additivity
    (`flowBracketBalance_compose`), `balance lo p = d + balance s p`, so the floor
    `balance lo p ≥ d` *is* the local Dyck `balance s p ≥ 0`.

    This is the combinatorial core of the `(d-dyck)` brick: `WellTyped_subrange` (in
    `WellBracketed.lean`) consumes a per-subrange local Dyck that `FlowSubrangesOk`'s hypotheses do
    not supply; this lemma manufactures it from the global Dyck for any subrange that begins at a
    local depth-minimum. -/
lemma flowBracketBalance_dyck_shift (tokens : Array (Positioned YamlToken))
    (lo s hi : Nat) (d : Int) (h_lo_s : lo ≤ s)
    (h_s_depth : flowBracketBalance tokens lo s = d)
    (h_floor : ∀ p, s ≤ p → p ≤ hi → flowBracketBalance tokens lo p ≥ d) :
    ∀ p, s ≤ p → p ≤ hi → flowBracketBalance tokens s p ≥ 0 := by
  intro p h_sp h_ph
  have hcomp := flowBracketBalance_compose tokens lo s p h_lo_s h_sp
  have hfloor := h_floor p h_sp h_ph
  omega

/-- **Matched-bracket interior is locally Dyck.**  The interior `(k+1, j)` of a depth-0 opener at
    `k` (matching close at `j`) is locally Dyck: `flowBracketBalance (k+1) p ≥ 0` for every
    `k+1 ≤ p ≤ j`.  The depth just after the opener is `1` (`flowBracketBalance_single`), and the
    matching-close locator's interior invariant (`balance lo i ≥ 1` over `(k, j]`, the fifth
    conjunct of `flowBracketBalance_matching_close`) is exactly the depth-`1` floor that
    `flowBracketBalance_dyck_shift` re-bases to `0`.  This is the concrete **local Dyck input**
    `WellTyped_subrange` consumes for a nested subrange — the `(d-dyck)` residual, ready to feed at
    assembly alongside the typed matching close. -/
lemma flowBracketBalance_interior_dyck (tokens : Array (Positioned YamlToken))
    (lo k j : Nat) (h_lo_k : lo ≤ k) (h_k_sz : k < tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : flowBracketDelta tokens[k]!.val = 1)
    (h_pos : ∀ i, k < i → i ≤ j → flowBracketBalance tokens lo i ≥ 1) :
    ∀ p, k + 1 ≤ p → p ≤ j → flowBracketBalance tokens (k+1) p ≥ 0 := by
  have h_step : flowBracketBalance tokens lo (k+1) = 1 := by
    rw [flowBracketBalance_compose tokens lo k (k+1) h_lo_k (by omega)]
    have hlen : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
    rw [flowBracketBalance_single tokens k hlen]
    have h1 : tokens.toList[k]'hlen = tokens[k] := Array.getElem_toList h_k_sz
    have h2 : tokens[k] = tokens[k]! := (getElem!_pos tokens k h_k_sz).symm
    rw [h1, h2]
    omega
  refine flowBracketBalance_dyck_shift tokens lo (k+1) j 1 (by omega) h_step ?_
  intro p h_sp h_ph
  exact h_pos p (by omega) h_ph

/-- **Per-descend inner-floor provider** — the parser-contract Dyck floor's *self-propagation* step.
    Composes the two pre-existing combinatorial bricks into the single descend the floor-guarded
    `FlowSubrangesOk` redirect (R435) needs at every nested bracket:

    * `flowBracketBalance_matching_close` (the forward first-return locator, built for the parser
      span-induction) yields the matching close `j` *and* the depth-`1` interior invariant
      `balance lo i ≥ 1` over `(k, j]` (its fifth conjunct);
    * `flowBracketBalance_interior_dyck` (built to feed `WellTyped_subrange`) re-bases that depth-`1`
      floor to the *local* depth-`0` Dyck floor `balance (k+1) p ≥ 0` of the interior `[k+1, j)`.

    So: an OUTER window `[lo, hi)` carrying its own Dyck floor (`h_dyck`) plus a depth-`0` opener at `k`
    *manufactures* the INNER window's own Dyck floor — exactly the floor a floor-guarded
    `FlowSubrangesOk.{seq,map}` query demands at the inner `.seq`/`.map` descend.  The floor is therefore
    **self-propagating** and its descent lemma was already built (twice, for two sibling consumers); this
    lemma only wires them, introducing no new combinatorics.

    Crucially, the floor must be EXPOSED on the bracket-matching output fields (`SeqBodyProps.bracket_seq`
    etc.) for the parser to read it off: the fields currently publish only `balance (k+1) j = 0`, which
    does NOT pin `j` as the first-return (a cross-matched inner `j` also balances), so the consumer cannot
    re-derive the inner floor at the handed-in `j` ([[ref-reconstruct-in-place-over-relocate]], one level
    down).  The PRODUCER (which knows the genuine structure) supplies the inner floor via THIS lemma; the
    consumer reads it off the augmented field. -/
lemma flowBracketBalance_inner_floor (tokens : Array (Positioned YamlToken))
    (lo k hi : Nat) (h_lo_k : lo ≤ k) (h_k_hi : k < hi) (h_hi_sz : hi ≤ tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_k_open : flowBracketDelta tokens[k]!.val = 1)
    (h_total : flowBracketBalance tokens lo hi = 0)
    (h_dyck : ∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) :
    ∃ j, k < j ∧ j < hi ∧
      flowBracketDelta tokens[j]!.val = -1 ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      (∀ p, k + 1 ≤ p → p ≤ j → flowBracketBalance tokens (k+1) p ≥ 0) := by
  obtain ⟨j, h_kj, h_j_hi, h_j_close, h_inner_bal, h_pos⟩ :=
    flowBracketBalance_matching_close tokens lo k hi h_lo_k h_k_hi h_hi_sz
      h_k_depth h_k_open h_total h_dyck
  refine ⟨j, h_kj, h_j_hi, h_j_close, h_inner_bal, ?_⟩
  exact flowBracketBalance_interior_dyck tokens lo k j h_lo_k (by omega) h_k_depth h_k_open h_pos

/-- **A matched bracket pair is depth-transparent.**  A complete bracket value — opener at `k`
    (`flowBracketDelta = 1`), matching close at `j` (`flowBracketDelta = -1`), balanced interior
    `(k+1, j)` — contributes net `0` to the running balance, so the balance just *after* the pair
    equals the balance just *before* the opener:
    `flowBracketBalance tokens lo (j+1) = flowBracketBalance tokens lo k`.
    By `flowBracketBalance_compose` the span `[k, j+1)` splits as opener (`+1`) + interior (`0`) +
    close (`-1`), and `flowBracketBalance_single` reads the two endpoint deltas. -/
lemma flowBracketBalance_bracket_pair_skip (tokens : Array (Positioned YamlToken))
    (lo k j : Nat) (h_lo_k : lo ≤ k) (h_k_j : k < j) (h_j_sz : j < tokens.size)
    (h_open : flowBracketDelta tokens[k]!.val = 1)
    (h_close : flowBracketDelta tokens[j]!.val = -1)
    (h_inner : flowBracketBalance tokens (k+1) j = 0) :
    flowBracketBalance tokens lo (j+1) = flowBracketBalance tokens lo k := by
  have h_k_sz : k < tokens.size := Nat.lt_trans h_k_j h_j_sz
  -- balance lo (j+1) = balance lo k + balance k (j+1)
  rw [flowBracketBalance_compose tokens lo k (j+1) h_lo_k (by omega)]
  -- balance k (j+1) = balance k (k+1) + balance (k+1) j + balance j (j+1)
  rw [flowBracketBalance_compose tokens k (k+1) (j+1) (by omega) (by omega),
      flowBracketBalance_compose tokens (k+1) j (j+1) (by omega) (by omega)]
  -- endpoint deltas via `flowBracketBalance_single`
  have hlk : k < tokens.toList.length := by rw [Array.length_toList]; exact h_k_sz
  have hlj : j < tokens.toList.length := by rw [Array.length_toList]; exact h_j_sz
  rw [flowBracketBalance_single tokens k hlk, flowBracketBalance_single tokens j hlj]
  -- bridge `tokens.toList[·]` to `tokens[·]!`
  have hk1 : tokens.toList[k]'hlk = tokens[k] := Array.getElem_toList h_k_sz
  have hk2 : tokens[k] = tokens[k]! := (getElem!_pos tokens k h_k_sz).symm
  have hj1 : tokens.toList[j]'hlj = tokens[j] := Array.getElem_toList h_j_sz
  have hj2 : tokens[j] = tokens[j]! := (getElem!_pos tokens j h_j_sz).symm
  rw [hk1, hk2, hj1, hj2, h_open, h_close, h_inner]
  omega

/-- **Depth-0 corollary.**  When the opener `k` sits at relative depth `0`
    (`flowBracketBalance lo k = 0`), the position `j + 1` immediately after the matching close is
    again at relative depth `0`.  This is the precondition that lets the bracket conjuncts' successor
    half reuse the *same* "after a complete value, the next depth-0 token is `.flowEntry` or the body
    close" fact that the scalar successor uses — the bracketed value is depth-transparent. -/
lemma flowBracketBalance_after_bracket_pair_zero (tokens : Array (Positioned YamlToken))
    (lo k j : Nat) (h_lo_k : lo ≤ k) (h_k_j : k < j) (h_j_sz : j < tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_open : flowBracketDelta tokens[k]!.val = 1)
    (h_close : flowBracketDelta tokens[j]!.val = -1)
    (h_inner : flowBracketBalance tokens (k+1) j = 0) :
    flowBracketBalance tokens lo (j+1) = 0 := by
  rw [flowBracketBalance_bracket_pair_skip tokens lo k j h_lo_k h_k_j h_j_sz
      h_open h_close h_inner]
  exact h_k_depth

/-- **Backward bracket-opener locator (Dyck — the backward mirror of
    `flowBracketBalance_matching_close`).**  If at least one bracket is open at position `a`
    (`flowBracketBalance tokens 0 a ≥ 1`, with `a ≤ tokens.size`), there is an *innermost* enclosing
    opener at some `p < a`: `tokens[p]` is an open bracket (`flowBracketDelta = 1`) and the body it
    opens reaches `a` at its own top level (`flowBracketBalance tokens (p+1) a = 0`).  Thus
    `loS := p + 1` is the body start of the bracket enclosing `a`, with `loS ≤ a` and
    `flowBracketBalance tokens loS a = 0` — exactly the `h_loS_a`/`h_bal0` inputs that the
    enclosing-facts provider's FROM-LOCATED assembler (`seqEnclosingFacts_provider_of_located`)
    consumes for nested gated windows.

    Where `flowBracketBalance_matching_close` scans FORWARD for the first return to depth `0` after an
    opener, this scans BACKWARD for the last opener still unmatched at `a`.  No standalone
    backward-matching-open primitive is needed: the `Nat.strongRecOn` on `a` recovers it inline.  The
    last token of the prefix (index `a - 1`) is opener, neutral, or closer:

    * **opener** (`delta = +1`): `a - 1` is itself the innermost opener; `balance (a) a = 0`;
    * **neutral** (`delta = 0`): the innermost opener at `a - 1` still encloses `a` (IH at `a - 1`);
    * **closer** (`delta = -1`): the IH at `a - 1` locates that closer's matching opener `p'`, then
      `flowBracketBalance_bracket_pair_skip` jumps the matched block (`balance 0 a = balance 0 p'`)
      and the IH at `p'` continues outward to the enclosing opener.

    Pure balance: no `SafeBodyUnit`, no `btFold`, no structural recursion.  The seq-vs-map *type* of
    the located opener (`tokens[p] = .flowSequenceStart`) and the matching *close* `hiS` are layered
    on by the consumer (the gate's `btFold`-top and the forward `flowBracketBalance_matching_close`).
    `#guard`-de-risked on `[[1, 2], 9]` (`Tests/Guards/Proofs/SeqDescentLocatorProbe.lean`) and the
    deeper `[[[1]], 2]`: the located `p`, the balance, and the matched-block skip hold at every nested
    gated window.

    **The interior FLOOR `∀ i ∈ [p+1, a], balance (p+1) i ≥ 0` (R311).**  R309 first sized this
    deliverable to its only consumer then (the rebase assembler, which reads only `loS`, `loS ≤ a`,
    `balance loS a = 0`) and DROPPED the floor.  A minimal-pair probe for the *next* consumer
    (`seqOpenerType_of_located_and_gate`, the opener-TYPE brick) showed the bare three facts are
    INSUFFICIENT: on `[{}, ["9"]]` at `a = 6` BOTH `p = 5` (the true innermost `[`) AND `p = 2`
    (a spurious `{`, with `balance 3 6 = -1 + 0 + 1 = 0`) satisfy `p < a ∧ delta = 1 ∧
    balance (p+1) a = 0`, yet `tokens[2]` is a `{` while the gate-top is `some true` — so the
    opener-type conclusion is FALSE on the bare existential.  The floor SEPARATES the pair
    (`balance 6 6 = 0 ≥ 0` for `p = 5`; `balance 3 4 = -1 < 0` for `p = 2`), pinning innermost-ness —
    the head of the typed stack at `a` is the bracket opened at `p` exactly because `p` is never popped
    over `(p, a]`.  The floor is INDEPENDENT of the three facts and of the gate, so it must be
    delivered HERE (the locator's construction is the only source of innermost-ness), not re-derived at
    the consume site.  Threading it costs only composition of the two IH floors (closer case): the
    enclosing opener `p'` stays at depth `≥ 0` across its whole matched span `[p', a]` because its
    interior floor (first IH) plus `balance p' p' = 0` and `balance p' a = 0` bracket it, and
    `balance (p+1) i = balance (p+1) p' + balance p' i = 0 + (≥ 0)` over `[p', a]`. -/
lemma flowBracketBalance_backward_open_locate (tokens : Array (Positioned YamlToken)) (a : Nat)
    (h_a_sz : a ≤ tokens.size) (h_open : flowBracketBalance tokens 0 a ≥ 1) :
    ∃ p, p < a ∧ flowBracketDelta tokens[p]!.val = 1 ∧
      flowBracketBalance tokens (p + 1) a = 0 ∧
      (∀ i, p + 1 ≤ i → i ≤ a → flowBracketBalance tokens (p + 1) i ≥ 0) := by
  -- Single-token balance read, bridging `tokens.toList[i]` to `tokens[i]!`.
  have single' : ∀ i, i < tokens.size →
      flowBracketBalance tokens i (i + 1) = flowBracketDelta tokens[i]!.val := by
    intro i hi
    have hlen : i < tokens.toList.length := by rw [Array.length_toList]; exact hi
    rw [flowBracketBalance_single tokens i hlen]
    have h1 : tokens.toList[i]'hlen = tokens[i] := Array.getElem_toList hi
    have h2 : tokens[i] = tokens[i]! := (getElem!_pos tokens i hi).symm
    rw [h1, h2]
  revert h_a_sz h_open
  induction a using Nat.strongRecOn with
  | ind a IH =>
    intro h_a_sz h_open
    -- `a = 0` is impossible: the balance there is `0`.
    rcases Nat.eq_zero_or_pos a with rfl | ha_pos
    · have : flowBracketBalance tokens 0 0 = 0 := by simp [flowBracketBalance]
      omega
    -- The last token of the prefix sits at index `a - 1`.
    have ha1_sz : a - 1 < tokens.size := by omega
    have hsa : flowBracketBalance tokens (a - 1) a = flowBracketDelta tokens[a - 1]!.val := by
      have h := single' (a - 1) ha1_sz
      rwa [show a - 1 + 1 = a from by omega] at h
    have hca : flowBracketBalance tokens 0 a
        = flowBracketBalance tokens 0 (a - 1) + flowBracketBalance tokens (a - 1) a :=
      flowBracketBalance_compose tokens 0 (a - 1) a (by omega) (by omega)
    by_cases hd1 : flowBracketDelta tokens[a - 1]!.val = 1
    · -- opener: `a - 1` is the innermost enclosing opener.
      refine ⟨a - 1, by omega, hd1, ?_, ?_⟩
      · rw [show a - 1 + 1 = a from by omega]
        simp [flowBracketBalance]
      · -- the floor is the single point `i = a`, where `balance a a = 0`.
        intro i hi1 hi2
        have he : a - 1 + 1 = a := by omega
        rw [he, show i = a from by omega]
        have h0 : flowBracketBalance tokens a a = 0 := by simp [flowBracketBalance]
        omega
    · by_cases hd0 : flowBracketDelta tokens[a - 1]!.val = 0
      · -- non-bracket: the innermost opener at `a - 1` still encloses `a`.
        have hbal_prev : flowBracketBalance tokens 0 (a - 1) ≥ 1 := by
          rw [hsa, hd0] at hca; omega
        obtain ⟨p, hp_lt, hp_open, hp_bal, hp_floor⟩ := IH (a - 1) (by omega) (by omega) hbal_prev
        have hpa : flowBracketBalance tokens (p + 1) a = 0 := by
          have hc := flowBracketBalance_compose tokens (p + 1) (a - 1) a (by omega) (by omega)
          rw [hp_bal, hsa, hd0] at hc; omega
        refine ⟨p, by omega, hp_open, hpa, ?_⟩
        intro i hi1 hi2
        rcases Nat.lt_or_ge i a with hlt | hge
        · exact hp_floor i hi1 (by omega)
        · rw [show i = a from by omega]; omega
      · -- closer: skip the matched block, then continue outward.
        have hdneg : flowBracketDelta tokens[a - 1]!.val = -1 := by
          have hge := flowBracketDelta_ge_neg_one tokens[a - 1]!.val
          have hle := flowBracketDelta_le_one tokens[a - 1]!.val
          omega
        have hbal_prev : flowBracketBalance tokens 0 (a - 1) ≥ 1 := by
          rw [hsa, hdneg] at hca; omega
        obtain ⟨p', hp'_lt, hp'_open, hp'_bal, hp'_floor⟩ :=
          IH (a - 1) (by omega) (by omega) hbal_prev
        -- Jump the matched pair `(p', a - 1)`: `balance 0 a = balance 0 p'`.
        have hskip := flowBracketBalance_bracket_pair_skip tokens 0 p' (a - 1)
          (by omega) hp'_lt ha1_sz hp'_open hdneg hp'_bal
        rw [show a - 1 + 1 = a from by omega] at hskip
        have hbal_p' : flowBracketBalance tokens 0 p' ≥ 1 := by rw [← hskip]; omega
        obtain ⟨p, hp_lt, hp_open, hp_bal, hp_floor⟩ := IH p' (by omega) (by omega) hbal_p'
        -- `balance (p+1) a = balance (p+1) p' + balance p' a = 0 + 0`.
        have hp'a : flowBracketBalance tokens p' a = 0 := by
          have hc2 := flowBracketBalance_compose tokens 0 p' a (by omega) (by omega)
          omega
        have hpa : flowBracketBalance tokens (p + 1) a = 0 := by
          have hc := flowBracketBalance_compose tokens (p + 1) p' a (by omega) (by omega)
          rw [hp_bal, hp'a] at hc; omega
        -- The enclosing opener `p'` stays at depth `≥ 0` across its whole matched span `[p', a]`:
        -- its interior floor (first IH) plus `balance p' p' = 0` and `balance p' a = 0` bracket it.
        have hp'_floor_full : ∀ i, p' ≤ i → i ≤ a → flowBracketBalance tokens p' i ≥ 0 := by
          intro i hi1 hi2
          rcases Nat.lt_or_ge i (p' + 1) with h | h
          · rw [show i = p' from by omega]
            have h0 : flowBracketBalance tokens p' p' = 0 := by simp [flowBracketBalance]
            omega
          · rcases Nat.lt_or_ge i a with hlt | hge'
            · -- interior of `p'`'s matched block: `balance p' i = 1 + balance (p'+1) i ≥ 1`.
              have hc4 := flowBracketBalance_compose tokens p' (p' + 1) i (by omega) (by omega)
              have hd_p' : flowBracketBalance tokens p' (p' + 1) = 1 := by
                have hs := single' p' (by omega); rw [hs, hp'_open]
              have hfl := hp'_floor i h (by omega)
              omega
            · rw [show i = a from by omega]; omega
        refine ⟨p, by omega, hp_open, hpa, ?_⟩
        intro i hi1 hi2
        rcases Nat.lt_or_ge i (p' + 1) with hlt | hge
        · exact hp_floor i hi1 (by omega)
        · have hc3 := flowBracketBalance_compose tokens (p + 1) p' i (by omega) (by omega)
          have hff := hp'_floor_full i (by omega) hi2
          rw [hp_bal] at hc3; omega

/-- **(d-shape) — the bracket-successor IS the scalar-successor (sequence body).**
    The successor half of `SeqBodyProps.bracket_seq`/`bracket_map` — `j+1 ≤ hi ∧ (FE ∨ (seqEnd ∧
    j+1=hi))` after a complete bracket value (opener at depth-0 `k`, matching close at `j`, balanced
    interior) — is exactly the conclusion `scalar_succ` produces at `k+1`, only at `j+1`.  The
    bracketed value is depth-transparent (`flowBracketBalance_after_bracket_pair_zero`: `j+1` is at
    relative depth `0`), so the *single* "next depth-0 token after a complete value is `.flowEntry`
    or the body close" emitter fact — here the hypothesis `h_succ`, keyed on the same depth-0 proviso
    the scalar case discharges — supplies the conjunct.  This collapses the per-position shape work
    for the bracket conjuncts onto the one scalar fact: `(d-shape)` reduces to a single emitter
    obligation per body kind. -/
lemma seq_bracket_succ_reduce (tokens : Array (Positioned YamlToken))
    (lo hi k j : Nat) (h_lo_k : lo ≤ k) (h_k_j : k < j) (h_j_sz : j < tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_open : flowBracketDelta tokens[k]!.val = 1)
    (h_close : flowBracketDelta tokens[j]!.val = -1)
    (h_inner : flowBracketBalance tokens (k+1) j = 0)
    (h_succ : flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi))) :
    j + 1 ≤ hi ∧
    (tokens[j+1]!.val = .flowEntry ∨
     (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi)) :=
  h_succ (flowBracketBalance_after_bracket_pair_zero tokens lo k j h_lo_k h_k_j h_j_sz
    h_k_depth h_open h_close h_inner)

/-- **(d-shape) — the value-bracket-successor IS the value-scalar-successor (mapping body, M8).**
    Mapping-body analogue of `seq_bracket_succ_reduce`: the successor half of
    `MapBodyProps.value_bracket_succ` (`j+1 ≤ hi ∧ (FE ∨ (mapEnd ∧ j+1=hi))`) after a complete
    bracketed *value* equals the conclusion `value_scalar_succ` produces, only at `j+1`.  Same
    depth-transparency reduction: the matched pair makes `j+1` depth-0, the single emitter fact
    fires. -/
lemma map_value_bracket_succ_reduce (tokens : Array (Positioned YamlToken))
    (lo hi k j : Nat) (h_lo_k : lo ≤ k) (h_k_j : k < j) (h_j_sz : j < tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_open : flowBracketDelta tokens[k]!.val = 1)
    (h_close : flowBracketDelta tokens[j]!.val = -1)
    (h_inner : flowBracketBalance tokens (k+1) j = 0)
    (h_succ : flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowMappingEnd ∧ j + 1 = hi))) :
    j + 1 ≤ hi ∧
    (tokens[j+1]!.val = .flowEntry ∨
     (tokens[j+1]!.val = .flowMappingEnd ∧ j + 1 = hi)) :=
  h_succ (flowBracketBalance_after_bracket_pair_zero tokens lo k j h_lo_k h_k_j h_j_sz
    h_k_depth h_open h_close h_inner)

/-- **(d-shape) — after a bracketed key, `.value` follows (mapping body, M5).**
    The successor of `MapBodyProps.key_bracket_value` (`j+1 < hi ∧ tokens[j+1] = .value`) after a
    complete bracketed *key* — opener at depth-0 `k` (the caller passes the key's bracket start,
    which sits at depth `0` since the preceding `.key` has delta `0`), matching close at `j` — is the
    same `.value` the scalar-key case (`key_scalar_value`, M4) produces.  Depth-transparency again
    bases `j+1` at relative depth `0`, so the single "what follows a complete key" emitter fact
    fires. -/
lemma map_key_bracket_value_reduce (tokens : Array (Positioned YamlToken))
    (lo hi k j : Nat) (h_lo_k : lo ≤ k) (h_k_j : k < j) (h_j_sz : j < tokens.size)
    (h_k_depth : flowBracketBalance tokens lo k = 0)
    (h_open : flowBracketDelta tokens[k]!.val = 1)
    (h_close : flowBracketDelta tokens[j]!.val = -1)
    (h_inner : flowBracketBalance tokens (k+1) j = 0)
    (h_succ : flowBracketBalance tokens lo (j+1) = 0 →
      j + 1 < hi ∧ tokens[j+1]!.val = .value) :
    j + 1 < hi ∧ tokens[j+1]!.val = .value :=
  h_succ (flowBracketBalance_after_bracket_pair_zero tokens lo k j h_lo_k h_k_j h_j_sz
    h_k_depth h_open h_close h_inner)

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
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi)) ∧
      (∀ p, k + 1 ≤ p → p ≤ j → flowBracketBalance tokens (k+1) p ≥ 0)
  bracket_map : ∀ k, lo ≤ k → k < hi →
    flowBracketBalance tokens lo k = 0 →
    tokens[k]!.val = .flowMappingStart →
    ∃ j, k < j ∧ j < hi ∧
      tokens[j]!.val = .flowMappingEnd ∧
      flowBracketBalance tokens (k+1) j = 0 ∧
      j + 1 ≤ hi ∧
      (tokens[j+1]!.val = .flowEntry ∨
       (tokens[j+1]!.val = .flowSequenceEnd ∧ j + 1 = hi)) ∧
      (∀ p, k + 1 ≤ p → p ≤ j → flowBracketBalance tokens (k+1) p ≥ 0)

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
      j + 1 < hi ∧ tokens[j+1]!.val = .value ∧
      (∀ p, k + 2 ≤ p → p ≤ j → flowBracketBalance tokens (k+2) p ≥ 0)
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
       (tokens[j+1]!.val = .flowMappingEnd ∧ j + 1 = hi)) ∧
      (∀ p, k + 2 ≤ p → p ≤ j → flowBracketBalance tokens (k+2) p ≥ 0)
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

/-- Universal structural properties: every valid flow body subrange
    in the token array satisfies `SeqBodyProps` (for seq bodies) or
    `MapBodyProps` (for map bodies).

    **Body-start guard** (`tokens[lo - 1]!.val = .flowSequenceStart` / `.flowMappingStart`):
    without it the universal would be FALSE.  A balanced subrange `[lo, hi)` ending in a close
    bracket need NOT be a genuine body: e.g. for `[a, b]` the subrange starting on the depth-0
    `.flowEntry` (the `,`) is balanced and ends in `.flowSequenceEnd`, yet `tokens[lo]` is `.flowEntry`,
    not a content-start, so `SeqBodyProps.content_start` fails.  The guard restricts `lo` to a real
    interior-start — immediately preceded by the matching opener — which is exactly where the
    dispatcher `flow_parser_ok_of_structure` projects these fields (every projection site has
    `tokens[lo-1]` = the opener), and exactly where the emitter's structure (and
    `seqBodyProps_assemble`/`mapBodyProps_assemble`'s `content_start` input) holds.  This is what
    makes the producer obligation (Phase J) provable rather than false. -/
structure FlowSubrangesOk (tokens : Array (Positioned YamlToken)) : Prop where
  seq : ∀ lo hi, lo ≤ hi → hi < tokens.size →
    tokens[hi]!.val = .flowSequenceEnd →
    flowBracketBalance tokens lo hi = 0 →
    tokens[lo - 1]!.val = .flowSequenceStart →
    (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
    SeqBodyProps tokens lo hi
  map : ∀ lo hi, lo ≤ hi → hi < tokens.size →
    tokens[hi]!.val = .flowMappingEnd →
    flowBracketBalance tokens lo hi = 0 →
    tokens[lo - 1]!.val = .flowMappingStart →
    (∀ i, lo ≤ i → i ≤ hi → flowBracketBalance tokens lo i ≥ 0) →
    MapBodyProps tokens lo hi

end L4YAML.Proofs.ParserGrammable

end Blanket
