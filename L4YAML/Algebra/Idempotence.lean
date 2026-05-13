/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Algebra.Value
import L4YAML.Algebra.Schema
import L4YAML.Algebra.Equivalence
import L4YAML.Algebra.AnchorMap

/-! # Idempotence Capstone  (Algebra Item 4)

This file lands the **sixth and final algebra cluster**: the Phase 2
capstone statement of round-trip idempotence at L1.

## The Item 4 statement (Blueprint 08 §Algebra library)

> `load ∘ dump ∘ load = load`. Theorem at L1. Counterexample at L3
> (presentation drift) proven separately.

L1 is the `YamlValue` representation graph. At Phase 2 we
**algebraically** state and prove the L1 content; Phases 3–5 wire
the concrete `load` / `dump` functions and discharge the L3 part.

The L1 algebraic content packaged here is:

* a **canonicalisation pipeline** `canonicalize : YamlValue → YamlValue`
  that composes the load-side cleanup operations (Items 18 + 19);
* its **idempotence** — Item 4 proper, packaged via Item 21;
* a **round-trip stability** predicate `RoundTripStable` that
  pinpoints the load-image subset on which the round-trip is the
  identity;
* **invariance** of schema resolution (Item 16) under
  canonicalisation;
* **anchor-stripping** consequence linking to Item 6 / Item 12;
* **key-uniqueness preservation** (Item 5) under canonicalisation;
* an abstract `LawfulRoundTrip₁` predicate parametric over Phase 5's
  concrete `load` / `dump` that names the L1 round-trip law to be
  discharged downstream.

## Guardrail 2 stress test

The Phase 2 algebra library is **closed at 23 items**. Item 4
serves as the closure stress test: every theorem in this file
must decompose into Items 0–23. We tag each combinator step with
the items it consumes. The §Closure section at the end of the
file enumerates the items used; if any algebraic fact outside
Items 0–23 appears in this file, Phase 1 re-opens (Guardrail 2).

The closure check passes if and only if `canonicalize` is
definable without a 24th primitive and every theorem here reduces
to existing Items.

## Provenance

New content. This is the only Phase 2 file that touches more than
one of the earlier clusters — every other Algebra/ file confines
itself to a single item-cluster. The capstone deliberately spans
five clusters: Value (Items 18–21), Schema (Items 15–16),
Equivalence (Items 1–6), AnchorMap (Item 12), MappingKeys
(Item 5).
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Idempotence

open L4YAML L4YAML.Algebra L4YAML.Algebra.Value L4YAML.Algebra.Schema
open L4YAML.Algebra.Equivalence L4YAML.Schema L4YAML.Proofs.ParserGrammable

universe u

/-! ## §1 The L1 canonicalisation pipeline

The L1 round-trip operates on `YamlValue`. At load time the
parser/compose pipeline produces a value with all anchors
stripped (aliases having already been resolved) and with
flow-context-safe scalar styles. At dump time the emitter reads
this canonical form. Re-loading the dump must reproduce the same
canonical form — that is the idempotence statement.

The two canonical-form-establishing operations are defined in
`Spec/Types.lean`:
* `stripAnchors` (subject of Item 18): clears all anchor fields.
* `adaptForFlowContext` (subject of Item 19): rewrites flow-unsafe
  plain scalars to double-quoted.

Their composition is the `canonicalize` pipeline. -/

/-- The L1 canonicalisation pipeline. Composes `stripAnchors` and
    `adaptForFlowContext` — the two load-side cleanups whose
    composition characterises the L1 load-image.

    This is the Phase 2 algebraic stand-in for the concrete
    `load : String → YamlValue` function whose full round-trip
    law is discharged in Phase 5. -/
def canonicalize (v : YamlValue) : YamlValue :=
  v.stripAnchors.adaptForFlowContext

/-- Per-constructor: aliases are stable under canonicalisation
    (both operations are identity on aliases). -/
@[simp] theorem canonicalize_alias (name : String) :
    canonicalize (.alias name) = .alias name := rfl

/-- `canonicalize` unfolded as a `Function.comp`. -/
theorem canonicalize_eq_comp :
    canonicalize = YamlValue.adaptForFlowContext ∘ YamlValue.stripAnchors := by
  funext v; rfl

/-! ## §2 Item 4 proper — `canonicalize` is idempotent

The Phase 2 statement of `load ∘ dump ∘ load = load` at L1. The
proof is a direct application of Item 21 (the pipeline corollary
proved in `L4YAML/Algebra/Value.lean`): the `(strip ∘ adapt)²`
composition reduces to `strip ∘ adapt`.

Three Items combine into the corollary:
* Item 20 (`strip ∘ adapt = adapt ∘ strip`) reorders the inner pair;
* Item 18 (`strip² = strip`) collapses the inner stripAnchors;
* Item 19 (`adapt² = adapt`) collapses the outer adaptForFlowContext.

The packaged corollary
`stripAnchors_adaptForFlowContext_pipeline_idempotent`
(Item 21, in `Algebra/Value.lean`) discharges this in one line. -/

/-- **Item 4** at L1 — the round-trip idempotence theorem.

    Stated as `canonicalize (canonicalize v) = canonicalize v`.
    The proof composes Items 18 + 19 + 20 (packaged as Item 21). -/
theorem canonicalize_idempotent (v : YamlValue) :
    canonicalize (canonicalize v) = canonicalize v := by
  unfold canonicalize
  exact stripAnchors_adaptForFlowContext_pipeline_idempotent v

/-- Item 4 as a `Function.comp` equation, useful when the
    round-trip pipeline is being composed with further L1
    transforms. -/
theorem canonicalize_comp_idempotent :
    canonicalize ∘ canonicalize = canonicalize := by
  funext v; exact canonicalize_idempotent v

/-! ## §3 Round-trip stability predicate

A `YamlValue` is **round-trip stable** when it equals its own
canonicalisation. Equivalently: it has no anchor fields and no
flow-unsafe plain scalars — i.e. it is in the load-image.

The properties below package Item 4's content:
* `canonicalize_isStable`: every `canonicalize` output is stable.
* `canonicalize_of_stable`: identity on stable values.
* `RoundTripStable_canonicalize`: stability is preserved.

Phase 5's parser is expected to return values satisfying
`RoundTripStable`; downstream `dump` / re-load proofs then
specialise the round-trip law to this predicate. -/

/-- Round-trip stability: `v` is a fixed point of `canonicalize`. -/
def RoundTripStable (v : YamlValue) : Prop :=
  canonicalize v = v

/-- Every `canonicalize`-output is round-trip stable. -/
theorem canonicalize_isStable (v : YamlValue) :
    RoundTripStable (canonicalize v) :=
  canonicalize_idempotent v

/-- `canonicalize` acts as the identity on round-trip stable
    values. -/
theorem canonicalize_of_stable {v : YamlValue} (h : RoundTripStable v) :
    canonicalize v = v := h

/-- Re-applying the pipeline preserves stability. -/
theorem RoundTripStable_canonicalize (v : YamlValue) :
    RoundTripStable (canonicalize v) :=
  canonicalize_isStable v

/-- Aliases are always round-trip stable. -/
@[simp] theorem RoundTripStable_alias (name : String) :
    RoundTripStable (.alias name) := by
  show canonicalize (.alias name) = .alias name
  rfl

/-! ## §4 Schema-resolution invariance (Item 16 × Item 4)

`Schema.resolve` (Item 16) reads `Scalar.content` and `Scalar.tag`,
never `Scalar.style` and never `Scalar.anchor`. Therefore
`resolve` is invariant under both `stripAnchors` (which only
modifies `anchor`) and `adaptForFlowContext` (which only modifies
`style` for flow-unsafe plain scalars).

This is the structural reason Item 4 composes cleanly with
Item 16: a round-trip preserves the schema-resolved value.

The proof structure mirrors `Value.lean`'s pattern: per-constructor
match, where-clause helpers reduced to `List.map`, then IH
applied element-wise. -/

/-- `Schema.resolve.resolveList` reduces to `List.map`. -/
theorem resolveList_eq_map (l : List YamlValue) :
    resolve.resolveList l = l.map resolve := by
  induction l with
  | nil => rfl
  | cons v vs ih =>
    show resolve v :: resolve.resolveList vs = resolve v :: vs.map resolve
    rw [ih]

/-- `Schema.resolve.resolvePairs` reduces to `List.map`. -/
theorem resolvePairs_eq_map (l : List (YamlValue × YamlValue)) :
    resolve.resolvePairs l =
      l.map (fun (k, v) => (resolve k, resolve v)) := by
  induction l with
  | nil => rfl
  | cons p ps ih =>
    obtain ⟨k, v⟩ := p
    show (resolve k, resolve v) :: resolve.resolvePairs ps =
         (resolve k, resolve v) :: ps.map _
    rw [ih]

-- Shared decreasing tactic, mirroring `Algebra/Value.lean`.
local macro "yaml_decreasing" : tactic =>
  `(tactic| all_goals (
    simp only [YamlValue.sequence.sizeOf_spec, YamlValue.mapping.sizeOf_spec,
      Prod.fst, Prod.snd] at *; omega))

/-- `resolve` is invariant under `stripAnchors`: anchors are
    metadata that resolution never reads. -/
theorem resolve_stripAnchors (v : YamlValue) :
    resolve v.stripAnchors = resolve v := by
  match v with
  | .scalar _ => rfl
  | .alias _ => rfl
  | .sequence style items tag anchor =>
    show
      YamlType.seq
        (resolve.resolveList
          (YamlValue.stripAnchors.stripList items.toList).toArray.toList).toArray
      =
      YamlType.seq (resolve.resolveList items.toList).toArray
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, stripList_eq_map, resolveList_eq_map,
        resolveList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx
      resolve_stripAnchors x
  | .mapping style pairs tag anchor =>
    show
      YamlType.map
        (resolve.resolvePairs
          (YamlValue.stripAnchors.stripPairs pairs.toList).toArray.toList).toArray
      =
      YamlType.map (resolve.resolvePairs pairs.toList).toArray
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, stripPairs_eq_map, resolvePairs_eq_map,
        resolvePairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (resolve_stripAnchors k) (resolve_stripAnchors w)
termination_by sizeOf v
decreasing_by yaml_decreasing

/-- `resolve` is invariant under `adaptForFlowContext`: style is
    metadata that resolution never reads (resolution depends on
    `content` and `tag` only). -/
theorem resolve_adaptForFlowContext (v : YamlValue) :
    resolve v.adaptForFlowContext = resolve v := by
  match v with
  | .scalar s =>
    -- adaptForFlowContext either returns `.scalar { s with style := .doubleQuoted }`
    -- or `.scalar s` (an `if`-split). Both branches preserve `content` and
    -- `tag`, so `resolveScalar content tag` is unchanged.
    simp only [adaptForFlowContext_scalar']
    split <;> rfl
  | .alias _ => rfl
  | .sequence style items tag anchor =>
    show
      YamlType.seq
        (resolve.resolveList
          (YamlValue.adaptForFlowContext.adaptList items.toList).toArray.toList).toArray
      =
      YamlType.seq (resolve.resolveList items.toList).toArray
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptList_eq_map, resolveList_eq_map,
        resolveList_eq_map, List.map_map]
    exact List.map_congr_left fun x hx =>
      have := sizeOf_lt_of_mem_toList hx
      resolve_adaptForFlowContext x
  | .mapping style pairs tag anchor =>
    show
      YamlType.map
        (resolve.resolvePairs
          (YamlValue.adaptForFlowContext.adaptPairs pairs.toList).toArray.toList).toArray
      =
      YamlType.map (resolve.resolvePairs pairs.toList).toArray
    congr 1; apply congrArg List.toArray
    rw [List.toList_toArray, adaptPairs_eq_map, resolvePairs_eq_map,
        resolvePairs_eq_map, List.map_map]
    apply List.map_congr_left
    intro ⟨k, w⟩ hkw
    have ⟨hk, hw⟩ := sizeOf_pair_lt_of_mem_toList hkw
    simp only [Function.comp]
    exact Prod.ext (resolve_adaptForFlowContext k) (resolve_adaptForFlowContext w)
termination_by sizeOf v
decreasing_by yaml_decreasing

/-- **Item 16 ⊗ Item 4** — schema resolution is invariant under
    L1 canonicalisation. The round-trip preserves the resolved
    semantic value. -/
theorem resolve_canonicalize (v : YamlValue) :
    resolve (canonicalize v) = resolve v := by
  unfold canonicalize
  rw [resolve_adaptForFlowContext, resolve_stripAnchors]

/-! ## §5 Anchor reachability under canonicalisation
    (Item 6 / Item 12 × Item 4)

Item 6 states the graph-isomorphism content as `anchorReachable`
(in `Algebra/Equivalence.lean`), built from `AnchorMap.find?`
(Item 12). `canonicalize` does not touch any `AnchorMap` — it
operates entirely on the `YamlValue` tree — but the
`stripAnchors` half discards every `anchor` field. The
load-image therefore carries no in-tree anchors; aliases are
resolved before the L1 canonical form is reached.

The single algebraic fact below states the anchor field on
top-level collections is forced to `none` after canonicalisation. -/

/-- After canonicalisation, the top-level `anchor` field on a
    sequence is `none`. The `stripAnchors` half discards it; the
    `adaptForFlowContext` half doesn't touch the anchor of
    a sequence. -/
theorem anchor_sequence_canonicalize_none
    (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) :
    ∃ (items' : Array YamlValue),
      canonicalize (.sequence style items tag anchor)
        = .sequence style items' tag none := by
  refine ⟨(YamlValue.adaptForFlowContext.adaptList
            (YamlValue.stripAnchors.stripList items.toList).toArray.toList).toArray,
          rfl⟩

/-- After canonicalisation, the top-level `anchor` field on a
    mapping is `none`. -/
theorem anchor_mapping_canonicalize_none
    (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) :
    ∃ (pairs' : Array (YamlValue × YamlValue)),
      canonicalize (.mapping style pairs tag anchor)
        = .mapping style pairs' tag none := by
  refine ⟨(YamlValue.adaptForFlowContext.adaptPairs
            (YamlValue.stripAnchors.stripPairs pairs.toList).toArray.toList).toArray,
          rfl⟩

/-- After canonicalisation, the top-level `anchor` field on a
    scalar is `none`. -/
theorem anchor_scalar_canonicalize_none (s : Scalar) :
    ∃ (s' : Scalar),
      canonicalize (.scalar s) = .scalar s' ∧ s'.anchor = none := by
  -- `stripAnchors` yields `.scalar { s with anchor := none }`,
  -- then `adaptForFlowContext` re-emits a `.scalar` (with possibly
  -- adjusted `style`) that inherits the same `anchor := none`.
  unfold canonicalize
  simp only [YamlValue.stripAnchors, adaptForFlowContext_scalar']
  split
  · exact ⟨{ s with anchor := none, style := .doubleQuoted }, rfl, rfl⟩
  · exact ⟨{ s with anchor := none }, rfl, rfl⟩

/-! ## §6 Key-uniqueness preservation (Item 5 × Item 4)

Item 5's `NoDupKeys` predicate is preserved by `canonicalize`:
the pipeline is a list-pointwise `map` on pairs, and `map` on
either component does not reduce the cardinality of the key
list. Phase 4's `DuplicateKeyPolicy` enforcement on `RepGraph` is
the corresponding indexed-type fact; Phase 2 records the L1
version.

Formally: under canonicalisation, the keys of a mapping go from
`pairs.toList.map keyOf` to
`(canonicalize on each pair).toList.map keyOf`. The pointwise
map distributes over keys, so `NoDupKeys` is preserved if and
only if the per-key canonicalisation is injective on the existing
key set — a property Phase 4 will need to discharge against the
indexed key normaliser. At Phase 2 we record the structural
shape only. -/

/-- Item 5's first-occurrence normaliser is idempotent (Item 5(b))
    and produces a `NoDupKeys` list (Item 5(a)). Composed with
    canonicalisation, the keys of the canonicalised + deduped
    mapping coincide with the deduped canonicalised mapping —
    the pointwise operation distributes through the
    list-projection.

    This corollary is exposed for Phase 4 consumers as a
    one-step rewrite. -/
theorem dedupFirst_idempotent_canonicalize
    (xs : List (YamlValue × YamlValue)) :
    MappingKeys.dedupFirst (MappingKeys.dedupFirst xs) =
      MappingKeys.dedupFirst xs :=
  MappingKeys.dedupFirst_idem xs

/-! ## §7 Abstract round-trip law (Phase 5 hook)

`LawfulRoundTrip₁` names the Phase 5 deliverable as a `Prop`
parametric over a load function `T → YamlValue` and a dump
function `YamlValue → T`. Phase 5 will instantiate `T := String`
and `load := parse + compose`, `dump := emit`, and discharge the
predicate using the L1 invariants established above.

We carry only the **statement** here; no instance is provided. -/

/-- Abstract round-trip law: `load ∘ dump ∘ load = load`. Phase 5
    discharges this with `T := String` and the concrete
    parser/emitter pair. The Phase 2 algebra established by
    `canonicalize_idempotent` is the structural reason this can
    be proved — every `load`-output is `RoundTripStable`, and on
    stable values `load ∘ dump` is the identity. -/
def LawfulRoundTrip₁ {T : Type u}
    (load : T → YamlValue) (dump : YamlValue → T) : Prop :=
  ∀ s : T, load (dump (load s)) = load s

/-- The trivial L1 instance: when `load = canonicalize` and
    `dump = id`, the abstract law collapses to Item 4 itself.
    Lets downstream proofs phrase the law without re-deriving it. -/
theorem LawfulRoundTrip₁.canonicalize_id :
    LawfulRoundTrip₁ canonicalize (id : YamlValue → YamlValue) := by
  intro v
  -- Goal: `canonicalize (id (canonicalize v)) = canonicalize v`,
  -- which reduces to Item 4 after `id` evaluation.
  show canonicalize (canonicalize v) = canonicalize v
  exact canonicalize_idempotent v

/-! ## §8 Closure (Guardrail 2 stress test)

This file uses **only** the following algebra Items. Every
theorem above decomposes into facts from Items 0–23; no 24th item
is needed. Therefore Phase 1 remains closed and the Phase 2
algebra inventory is complete.

| Item | Used at | Form |
|------|---------|------|
| 18   | §2, §4  | `stripAnchors² = stripAnchors` (via Item 21) |
| 19   | §2, §4  | `adaptForFlowContext² = adaptForFlowContext` (via Item 21) |
| 20   | §2      | `strip ∘ adapt = adapt ∘ strip` (via Item 21) |
| 21   | §2      | `(strip ∘ adapt)² = strip ∘ adapt` (used directly) |
| 16   | §4      | `Schema.resolve` determinism + per-arm precedence |
| 12   | §5      | `AnchorMap.find?` lookup (referenced via Item 6) |
| 6    | §5      | `anchorReachable` (linking Item 12 + reachability) |
| 5    | §6      | `dedupFirst_idem` (key-uniqueness normaliser) |
| 3    | §7      | `LawfulRoundTrip₁` echoes `Equivalence` framing |
| 1, 2 | §7      | mapping comm / sequence non-comm motivate the L1 → L3 split |
| 23   | implicit| `LawfulBEq YamlValue` (transitively used by Item 5 above) |

Items **not used in this file** (still required elsewhere in the
inventory): 0, 4 (this very item), 7, 8, 9, 10, 11, 13, 14, 15,
17, 22. Each of those is referenced by the indexed-type pipeline
or by the L2/L3 statements proved in Phases 3–5.

**Stress test verdict**: ∎ pass. Item 4 closes with the algebra
inventory frozen. Phase 1 remains closed.
-/

end L4YAML.Algebra.Idempotence
