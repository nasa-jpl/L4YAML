/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Algebra.AnchorMap
import L4YAML.Algebra.LawfulBEq
import L4YAML.Config.LoadConfig

/-! # Equivalence + Collection Laws  (Algebra Items 1, 2, 3, 5, 6)

This file lands the **third algebra cluster**: the `≈` equivalence
relation on `YamlValue` and the collection-key uniqueness laws.

## Item map

* **Item 3** — `YamlEquiv : YamlValue → YamlValue → Prop` with an
  `Equivalence` / `Setoid` instance. The relation extends `=` with
  mapping commutativity.
* **Item 1** — mapping commutativity is a constructor of
  `YamlEquiv` and is also exposed as a top-level theorem
  `mapping_comm` for `rw`-style use.
* **Item 2** — sequence non-commutativity is the dual: a concrete
  counterexample witnesses that no analogous `sequence_perm`
  constructor can be admitted *under `=`*. The counterexample is a
  two-element sequence whose two orderings are not `=`.
* **Item 5** — key-uniqueness for mappings: predicate `NoDupKeys`
  plus first-occurrence normalisation `dedupFirst`. The two
  algebraic facts are `noDup_dedupFirst` and `dedupFirst_idem`.
* **Item 6** — graph isomorphism as a `Bisimulation` typeclass
  (D3 resolution) plus an `AnchorMap`-based reachability relation.
  Per the Phase 1 design (Blueprint 08 §D3), the typeclass shape is
  the deliverable; concrete instances land in Phase 4 with the
  indexed `RepGraph`.

## Cycle handling and `EqMode`

`YamlValue` is itself a finite tree — no internal references, no
cycles. The `EqMode` parameter in `LoadConfig` only becomes
load-bearing when alias resolution targets a cyclic
`RepGraph input range` (Phase 4). Phase 2's `YamlEquiv` is the
**acyclic-tree** part of the `≈` story; `EqMode.bisim` is the
extension point for the cyclic case via the `Bisimulation`
typeclass introduced below.

## Closure (Guardrail 2)

This file introduces no new algebra beyond Items 1, 2, 3, 5, 6.
The `Bisimulation` typeclass is the **statement** of D3; no
instance is provided here.

## Provenance

New content. Depends on Item 12 (`AnchorMap`) for the Item 6
reachability relation, Item 23 (`LawfulBEq YamlValue`) for
key-equality comparisons used in `dedupFirst`, and
`L4YAML.Config.LoadConfig` for the `DuplicateKeyPolicy` enum that
indexes which normalisation function is in play.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Equivalence

open L4YAML L4YAML.Algebra L4YAML.Config

universe u

/-! ## Item 3 — The `YamlEquiv` relation and `Equivalence` instance

`YamlEquiv` is an inductive `Prop` relation on `YamlValue` with
four constructors: `refl`, `symm`, `trans` (which together make it
an equivalence relation by definition) and `mapping_perm` (which
encodes Item 1's mapping commutativity).

Sequence and scalar congruence are derivable from `refl` + `symm`
+ `trans` once the children are already related by `=`, so they
are not separate constructors. Future extensions (e.g. lifting
`YamlEquiv` through sequence/mapping congruence) can be added as
admissibility lemmas without growing the constructor set.
-/

/-- The L1 equivalence relation `≈` on `YamlValue`. Extends `=`
    with mapping commutativity (`mapping_perm`) and is closed under
    `refl`/`symm`/`trans` by construction. -/
inductive YamlEquiv : YamlValue → YamlValue → Prop where
  /-- Reflexivity: every value is `≈`-equivalent to itself. -/
  | refl (v : YamlValue) : YamlEquiv v v
  /-- Symmetry. -/
  | symm {a b : YamlValue} : YamlEquiv a b → YamlEquiv b a
  /-- Transitivity. -/
  | trans {a b c : YamlValue} : YamlEquiv a b → YamlEquiv b c → YamlEquiv a c
  /-- **Mapping commutativity** (Item 1): two mappings whose pair
      lists are permutations of each other are `≈`-equivalent. -/
  | mapping_perm (style : CollectionStyle) (tag anchor : Option String)
      (pairs₁ pairs₂ : Array (YamlValue × YamlValue)) :
      pairs₁.toList.Perm pairs₂.toList →
      YamlEquiv (.mapping style pairs₁ tag anchor)
                (.mapping style pairs₂ tag anchor)

namespace YamlEquiv

/-- `YamlEquiv` is an `Equivalence`. Trivial because the
    constructors `refl`/`symm`/`trans` are literally the
    three Equivalence laws. -/
theorem is_equivalence : Equivalence YamlEquiv :=
  ⟨YamlEquiv.refl, YamlEquiv.symm, YamlEquiv.trans⟩

end YamlEquiv

/-- `HasEquiv` instance making `≈` notation refer to `YamlEquiv`. -/
instance : HasEquiv YamlValue := ⟨YamlEquiv⟩

/-- `Setoid` instance: `YamlValue` is a setoid under `≈`. -/
instance instSetoidYamlValue : Setoid YamlValue where
  r := YamlEquiv
  iseqv := YamlEquiv.is_equivalence

/-! ## Item 1 — Mapping commutativity (theorem form)

The constructor `YamlEquiv.mapping_perm` is the algebraic content.
This top-level alias makes Item 1 quotable without spelling out
the full constructor name.
-/

/-- **Item 1**: two mappings with permuted pair lists are
    `≈`-equivalent. Stated as a theorem for `rw`-style use. -/
theorem mapping_comm {style : CollectionStyle} {tag anchor : Option String}
    {pairs₁ pairs₂ : Array (YamlValue × YamlValue)}
    (h : pairs₁.toList.Perm pairs₂.toList) :
    YamlEquiv (.mapping style pairs₁ tag anchor)
              (.mapping style pairs₂ tag anchor) :=
  YamlEquiv.mapping_perm style tag anchor pairs₁ pairs₂ h

/-! ## Item 2 — Sequence non-commutativity

The dual of Item 1: sequences are *not* invariant under permutation
of their elements **under `=`** (and intentionally also not under
`≈`, because the `YamlEquiv` relation lacks a `sequence_perm`
constructor by design).

We prove the strong form: there exist two `=`-distinct sequences
whose underlying lists are permutations of each other. The
witnesses use `.alias` constructors with distinct string names
because string inequality is `decide`-able.
-/

/-- **Item 2** — counterexample: there exist two sequences with
    permuted-but-distinct item arrays. Witnesses that no
    `sequence_perm` constructor is admissible *under `=`*. -/
theorem sequence_not_comm :
    ∃ (style : CollectionStyle) (tag anchor : Option String)
      (items₁ items₂ : Array YamlValue),
      items₁.toList.Perm items₂.toList ∧
      YamlValue.sequence style items₁ tag anchor
        ≠ YamlValue.sequence style items₂ tag anchor := by
  refine ⟨.block, none, none,
          #[.alias "a", .alias "b"],
          #[.alias "b", .alias "a"], ?_, ?_⟩
  · -- Underlying lists: ["alias a", "alias b"] ~ ["alias b", "alias a"]
    -- via List.Perm.swap.
    have hSwap :
        ([YamlValue.alias "a", YamlValue.alias "b"]).Perm
        ([YamlValue.alias "b", YamlValue.alias "a"]) :=
      List.Perm.swap (YamlValue.alias "b") (YamlValue.alias "a") []
    exact hSwap
  · intro h
    -- Extract the array-equality from the sequence-constructor equality.
    have harr :
        (#[YamlValue.alias "a", YamlValue.alias "b"] :
          Array YamlValue)
        = #[YamlValue.alias "b", YamlValue.alias "a"] := by
      injection h
    have hlist :
        [YamlValue.alias "a", YamlValue.alias "b"]
          = [YamlValue.alias "b", YamlValue.alias "a"] := by
      injection harr
    -- First element equal ⇒ "a" = "b", contradiction.
    have : YamlValue.alias "a" = YamlValue.alias "b" := by
      injection hlist
    have hab : "a" = "b" := by injection this
    exact absurd hab (by decide)

/-! ## Item 5 — Key-uniqueness on mappings

The `NoDupKeys` predicate states that a mapping's key list has no
duplicates (as `YamlValue`s under `LawfulBEq`). The function
`dedupFirst` realises the `.first` normalisation policy: keep the
first binding for each key.

`dedupLast` (`.last` policy) and `dedupMerge` (`.merge` policy)
are deferred to Phase 4 — `dedupLast` is `reverse ∘ dedupFirst ∘ reverse`
modulo bookkeeping, and `dedupMerge` requires the parser-supplied
combinator which lives in `RepGraph input range` (Phase 4's
indexed type).

The two algebraic facts proved below are:

* `noDup_dedupFirst` — `(dedupFirst xs)` is duplicate-free.
* `dedupFirst_idem` — `dedupFirst` is idempotent.
-/

namespace MappingKeys

/-- Project the key out of a `(key, value)` pair. -/
@[inline] def keyOf (p : YamlValue × YamlValue) : YamlValue := p.1

/-- The list of keys of a pair array. -/
@[inline] def keysOf (pairs : Array (YamlValue × YamlValue)) : List YamlValue :=
  pairs.toList.map keyOf

/-- `NoDupKeys pairs` — no key appears twice in `pairs`. -/
def NoDupKeys (pairs : Array (YamlValue × YamlValue)) : Prop :=
  (keysOf pairs).Nodup

/-- First-occurrence normalisation on a `(key, value)` list. Keep
    the head, recurse on the tail, and filter the recursive result
    to drop any later pair sharing the head's key. -/
def dedupFirst : List (YamlValue × YamlValue) → List (YamlValue × YamlValue)
  | []            => []
  | (k, v) :: rest =>
    (k, v) :: (dedupFirst rest).filter (fun p => !(p.1 == k))

/-- Filtering preserves `Nodup` of the projection. -/
private theorem nodup_filter {p : YamlValue × YamlValue → Bool}
    (xs : List (YamlValue × YamlValue))
    (h : (xs.map keyOf).Nodup) :
    ((xs.filter p).map keyOf).Nodup := by
  induction xs with
  | nil => simp [List.filter]
  | cons head tail ih =>
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hHead, hTail⟩ := h
    simp only [List.filter_cons]
    split
    · simp only [List.map_cons, List.nodup_cons]
      refine ⟨?_, ih hTail⟩
      intro hmem
      apply hHead
      rw [List.mem_map] at hmem ⊢
      obtain ⟨x, hxmem, hxk⟩ := hmem
      refine ⟨x, ?_, hxk⟩
      exact (List.mem_filter.mp hxmem).1
    · exact ih hTail

/-- The head's key does not occur in `(dedupFirst rest).filter (·.1 ≠ k)`. -/
private theorem not_mem_keys_filter (k : YamlValue) (rest : List (YamlValue × YamlValue)) :
    k ∉ ((dedupFirst rest).filter (fun p => !(p.1 == k))).map keyOf := by
  intro hmem
  rw [List.mem_map] at hmem
  obtain ⟨⟨k', v'⟩, hmem', heq⟩ := hmem
  -- `heq : keyOf (k', v') = k`. Reduce `keyOf` and rewrite `k'` to `k`.
  have hk' : k' = k := heq
  -- After substituting `k' := k`, the filter predicate becomes `!(k == k)`.
  cases hk'
  have hfilt := (List.mem_filter.mp hmem').2
  -- After `cases`, `k'` was unified with `k`; the filter predicate is `!(k == k)`.
  simp only [Bool.not_eq_true'] at hfilt
  have hRefl : (k == k) = true := beq_self_eq_true k
  exact absurd (hRefl.symm.trans hfilt) (by decide)

/-- **Item 5(a)** — `dedupFirst` produces a `Nodup` key list. -/
theorem noDup_dedupFirst (xs : List (YamlValue × YamlValue)) :
    ((dedupFirst xs).map keyOf).Nodup := by
  induction xs with
  | nil => simp [dedupFirst]
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [dedupFirst, List.map_cons, List.nodup_cons]
    refine ⟨?_, ?_⟩
    · exact not_mem_keys_filter k rest
    · exact nodup_filter (dedupFirst rest) ih

/-- A pair list whose key projection is `Nodup` is fixed by `dedupFirst`. -/
private theorem dedupFirst_of_noDup (xs : List (YamlValue × YamlValue))
    (h : (xs.map keyOf).Nodup) :
    dedupFirst xs = xs := by
  induction xs with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k, v⟩ := p
    simp only [List.map_cons, List.nodup_cons] at h
    obtain ⟨hHead, hTail⟩ := h
    simp only [dedupFirst]
    have hRec : dedupFirst rest = rest := ih hTail
    rw [hRec]
    -- Filter is identity because k ∉ rest's keys.
    congr 1
    apply List.filter_eq_self.mpr
    intro ⟨k', v'⟩ hmem
    have hkey : k' ∈ rest.map keyOf := List.mem_map.mpr ⟨(k', v'), hmem, rfl⟩
    have hne : k' ≠ k := fun heq => hHead (heq ▸ hkey)
    simp only [Bool.not_eq_true']
    exact beq_eq_false_iff_ne.mpr hne

/-- **Item 5(b)** — `dedupFirst` is idempotent. -/
theorem dedupFirst_idem (xs : List (YamlValue × YamlValue)) :
    dedupFirst (dedupFirst xs) = dedupFirst xs :=
  dedupFirst_of_noDup (dedupFirst xs) (noDup_dedupFirst xs)

end MappingKeys

/-! ## Item 6 — Graph isomorphism via `AnchorMap` + `Bisimulation`

Item 6's algebraic content is the `AnchorMap` insert/find/empty
laws (already in `L4YAML/Algebra/AnchorMap.lean`). What remains
is the *interface* by which the Phase 4 parser will request alias
resolution under cyclic-graph equivalence: the `Bisimulation`
typeclass, settled by D3.

The typeclass is parameterised by the carrier type `α` so that
Phase 4 can instantiate it at `RepGraph input range`. For Phase 2
we provide only the shape; instances are Phase 4's deliverable.

Reachability through an `AnchorMap` (`anchorReachable`) is the
small concrete fact that any `Bisimulation` instance will compose
with: it says "anchor `name` in map `m` resolves to value `v`"
and inherits all the algebraic content of Item 12.
-/

/-- Reachability through an `AnchorMap`: holds iff `m.find? name = some v`.
    The single concrete fact about reachability that Item 6 needs from
    Item 12; algebraic content (insert/find/empty laws) lives in
    `L4YAML/Algebra/AnchorMap.lean`. -/
def anchorReachable (m : AnchorMap) (name : String) (v : YamlValue) : Prop :=
  m.find? name = some v

/-- **Item 6 / D3** — the `Bisimulation` typeclass: client-supplied
    witness for `EqMode.bisim` cycle handling. An instance picks a
    bisimulation relation on its carrier type plus the symmetry law
    (the transitivity / reflexivity laws follow once the relation
    is composed with `YamlEquiv`).

    Phase 4 will provide the canonical instance on
    `RepGraph input range`; user-supplied instances let clients
    use their own equality discipline for the cyclic case. -/
class Bisimulation (α : Type u) where
  /-- The bisimulation relation. Two `α`-values are bisimilar iff
      `isBisim a b` holds; the typeclass extends this to the
      cyclic-graph equivalence that `EqMode.bisim` demands. -/
  isBisim : α → α → Prop
  /-- Bisimulation is symmetric — the only **required** law at the
      typeclass level. Reflexivity / transitivity are *derivable*
      facts about specific instances. -/
  symm : ∀ {a b : α}, isBisim a b → isBisim b a

/-- **Reachability is an `AnchorMap` lookup** — restated as a `rfl`
    for downstream rewriting. -/
@[simp] theorem anchorReachable_iff (m : AnchorMap) (name : String) (v : YamlValue) :
    anchorReachable m name v ↔ m.find? name = some v := Iff.rfl

end L4YAML.Algebra.Equivalence
