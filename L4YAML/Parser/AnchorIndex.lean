/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import Std.Data.HashMap
public import Std.Data.HashSet
public import L4YAML.Spec.Types

@[expose] public section Blanket

/-!
# Anchor Indexes

Hash indexes over the two anchor tables a parse state carries, so that
the per-alias work in `parseNode` (§7.1's "does this anchor occur?") and
in `addAnchor` (`resolveAliases`' first-match lookup) is O(1) instead of a
scan of the whole table.

Both indexes are proof-carrying structures: the hash structure is bundled
with the proof that it agrees with the `Array` it indexes.  The arrays stay
the source of truth — every existing proof keeps reading `ps.declaredAnchors`
and `ps.anchors` — and the index is a derived view that cannot drift,
because the only constructors (`empty`, `push`) rebuild the agreement
proof.  The operations are `@[irreducible]` so that `rfl`/`simp` on parser
states never unfold hash-map internals; proofs go through `contains_eq_any`
and `resolveAliasesWith_find?` instead.

- `DeclaredIndex names`: a `HashSet` with `contains n ↔ n ∈ names`.
- `AnchorIndex anchors`: a `HashMap` from a name to the index of its
  *first* binding, with `lookup = anchors.findSome? …` — exactly the
  lookup `YamlValue.resolveAliases` performs.
- `YamlValue.resolveAliasesWith`: `resolveAliases` over an abstract
  lookup function; `resolveAliasesWith_anchorsLookup` shows it is the
  same function when the lookup is the array's first-match scan.
-/

namespace L4YAML

/-! ## Declared-anchor index -/

/-- A `HashSet` of anchor names that agrees with the array `names`. -/
structure DeclaredIndex (names : Array String) where
  set : Std.HashSet String
  mem_iff : ∀ n, set.contains n = true ↔ n ∈ names

/-- The index of the empty declaration set. -/
@[irreducible] def DeclaredIndex.empty : DeclaredIndex #[] := ⟨∅, by simp⟩

/-- Index the declaration `names.push name`. -/
@[irreducible] def DeclaredIndex.push {names : Array String} (idx : DeclaredIndex names)
    (name : String) : DeclaredIndex (names.push name) :=
  ⟨idx.set.insert name, fun n => by
    rw [Std.HashSet.contains_insert, Array.mem_push, Bool.or_eq_true, idx.mem_iff n, beq_iff_eq]
    exact ⟨fun h => h.elim (fun h => Or.inr h.symm) Or.inl,
           fun h => h.elim Or.inr (fun h => Or.inl h.symm)⟩⟩

instance {names : Array String} : Repr (DeclaredIndex names) :=
  ⟨fun idx n => reprPrec idx.set n⟩

/-- Membership through the index; equals `names.any (· == n)` by `DeclaredIndex.contains_iff`. -/
@[irreducible] def DeclaredIndex.contains {names : Array String} (idx : DeclaredIndex names) (n : String) : Bool :=
  idx.set.contains n

lemma DeclaredIndex.contains_iff {names : Array String} (idx : DeclaredIndex names) (n : String) :
    idx.contains n = true ↔ n ∈ names := by
  unfold DeclaredIndex.contains; exact idx.mem_iff n

/-- The index answers exactly the scan `parseNode` used to perform. -/
lemma DeclaredIndex.contains_eq_any {names : Array String} (idx : DeclaredIndex names) (n : String) :
    idx.contains n = names.any (fun m => m == n) := by
  have key : (names.any fun m => m == n) = true ↔ n ∈ names := by
    rw [Array.any_eq_true, Array.mem_iff_getElem]; simp
  cases h : names.any (fun m => m == n)
  · exact Bool.eq_false_iff.mpr (fun hc => by
      have := key.mpr ((idx.contains_iff n).mp hc); simp [h] at this)
  · exact (idx.contains_iff n).mpr (key.mp h)

/-! ## Anchor-value index -/

/-- The first-match scan `YamlValue.resolveAliases` performs over an anchor table. -/
def anchorsLookup (anchors : Array (String × YamlValue)) (name : String) : Option YamlValue :=
  anchors.findSome? (fun (n, val) => if n == name then some val else none)

/-- Lookup through a name → index map, reading the value back from the array. -/
def AnchorIndex.lookup (m : Std.HashMap String Nat) (anchors : Array (String × YamlValue))
    (name : String) : Option YamlValue :=
  (m[name]? : Option Nat).bind fun i => anchors[i]?.map (·.2)

/-- A `HashMap` from anchor name to the position of its first binding in
    `anchors`, bundled with the proof that reading through it is the
    array's first-match scan. -/
structure AnchorIndex (anchors : Array (String × YamlValue)) where
  map : Std.HashMap String Nat
  bound : ∀ (n : String) (i : Nat), map[n]? = some i → i < anchors.size
  agree : ∀ n, AnchorIndex.lookup map anchors n = anchorsLookup anchors n

instance {anchors : Array (String × YamlValue)} : Repr (AnchorIndex anchors) :=
  ⟨fun idx n => reprPrec idx.map n⟩

/-- The index of the empty anchor table. -/
@[irreducible] def AnchorIndex.empty : AnchorIndex #[] :=
  ⟨∅, by simp, by simp [AnchorIndex.lookup, anchorsLookup]⟩

/-- The invariant survives pushing `(name, v)` when the map keeps a bound
    name and binds a new one to `anchors.size`. -/
lemma AnchorIndex.push_inv (m : Std.HashMap String Nat) (anchors : Array (String × YamlValue))
    (name : String) (v : YamlValue)
    (hbound : ∀ (n : String) (i : Nat), m[n]? = some i → i < anchors.size)
    (hlook : ∀ n, AnchorIndex.lookup m anchors n = anchorsLookup anchors n) :
    let m' := if m.contains name then m else m.insert name anchors.size
    (∀ (n : String) (i : Nat), m'[n]? = some i → i < (anchors.push (name, v)).size) ∧
    ∀ n, AnchorIndex.lookup m' (anchors.push (name, v)) n
        = anchorsLookup (anchors.push (name, v)) n := by
  intro m'
  by_cases hc : m.contains name = true
  · simp only [m', hc, ↓reduceIte]
    refine ⟨fun n i h => by rw [Array.size_push]; exact Nat.lt_succ_of_lt (hbound n i h),
            fun n => ?_⟩
    have hl := hlook n
    unfold AnchorIndex.lookup anchorsLookup at hl ⊢
    rw [Array.findSome?_push, ← hl]
    cases hn : m[n]? with
    | none =>
      simp only [Option.bind_none, Option.none_or]
      by_cases hnn : name = n
      · subst hnn
        rw [Std.HashMap.contains_eq_isSome_getElem?, hn] at hc
        simp at hc
      · simp [hnn]
    | some i =>
      have hi : i < anchors.size := hbound n i hn
      simp [Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]
  · simp only [m', hc, Bool.false_eq_true, ↓reduceIte]
    have hnone : m[name]? = none := by
      rw [Std.HashMap.contains_eq_isSome_getElem?] at hc
      simpa using hc
    refine ⟨fun n i h => ?_, fun n => ?_⟩
    · rw [Std.HashMap.getElem?_insert] at h
      split at h
      · simp only [Option.some.injEq] at h; rw [Array.size_push]; omega
      · rw [Array.size_push]; exact Nat.lt_succ_of_lt (hbound n i h)
    · have hl := hlook n
      unfold AnchorIndex.lookup anchorsLookup at hl ⊢
      rw [Array.findSome?_push, ← hl, Std.HashMap.getElem?_insert]
      by_cases hnn : name = n
      · subst hnn
        simp [hnone]
      · have hne : (name == n) = false := by simpa using hnn
        simp only [hne, Bool.false_eq_true, ↓reduceIte, Option.or_none]
        cases hn : m[n]? with
        | none => rfl
        | some i =>
          have hi : i < anchors.size := hbound n i hn
          simp [Array.getElem?_push_lt hi, Array.getElem?_eq_getElem hi]

/-- Index `anchors.push (name, v)`: a name already bound keeps its first
    position; a new name maps to the position just appended. -/
@[irreducible] def AnchorIndex.push {anchors : Array (String × YamlValue)} (idx : AnchorIndex anchors)
    (name : String) (v : YamlValue) : AnchorIndex (anchors.push (name, v)) :=
  ⟨if idx.map.contains name then idx.map else idx.map.insert name anchors.size,
   (AnchorIndex.push_inv idx.map anchors name v idx.bound idx.agree).1,
   (AnchorIndex.push_inv idx.map anchors name v idx.bound idx.agree).2⟩

/-- Resolve a name through the index. -/
@[irreducible] def AnchorIndex.find? {anchors : Array (String × YamlValue)} (idx : AnchorIndex anchors)
    (name : String) : Option YamlValue :=
  AnchorIndex.lookup idx.map anchors name

lemma AnchorIndex.find?_eq {anchors : Array (String × YamlValue)} (idx : AnchorIndex anchors)
    (name : String) : idx.find? name = anchorsLookup anchors name := by
  unfold AnchorIndex.find?; exact idx.agree name

/-! ## `resolveAliases` over an abstract lookup -/

/-- `YamlValue.resolveAliases` with the anchor-table scan abstracted into
    `lookup`.  Same recursion, same unresolved-alias behaviour. -/
def YamlValue.resolveAliasesWith (v : YamlValue) (lookup : String → Option YamlValue) : YamlValue :=
  match v with
  | .scalar _ => v
  | .sequence style items tag anchor =>
    .sequence style (resolveListWith items.toList lookup).toArray tag anchor
  | .mapping style pairs tag anchor =>
    .mapping style (resolvePairsWith pairs.toList lookup).toArray tag anchor
  | .alias name =>
    match lookup name with
    | some val => val
    | none => v
where
  /-- Resolve aliases in a list of values. -/
  resolveListWith : List YamlValue → (String → Option YamlValue) → List YamlValue
    | [], _ => []
    | v :: vs, lookup => v.resolveAliasesWith lookup :: resolveListWith vs lookup
  /-- Resolve aliases in a list of key-value pairs. -/
  resolvePairsWith : List (YamlValue × YamlValue) → (String → Option YamlValue)
      → List (YamlValue × YamlValue)
    | [], _ => []
    | (k, v) :: rest, lookup =>
      (k.resolveAliasesWith lookup, v.resolveAliasesWith lookup) :: resolvePairsWith rest lookup

mutual
/-- With the array's own first-match scan as the lookup, `resolveAliasesWith`
    *is* `resolveAliases`. -/
lemma YamlValue.resolveAliasesWith_anchorsLookup (v : YamlValue)
    (anchors : Array (String × YamlValue)) :
    v.resolveAliasesWith (anchorsLookup anchors) = v.resolveAliases anchors := by
  match v with
  | .scalar _ => rfl
  | .sequence style items tag anchor =>
    simp only [YamlValue.resolveAliasesWith, YamlValue.resolveAliases]
    rw [resolveListWith_anchorsLookup]
  | .mapping style pairs tag anchor =>
    simp only [YamlValue.resolveAliasesWith, YamlValue.resolveAliases]
    rw [resolvePairsWith_anchorsLookup]
  | .alias name => rfl

lemma YamlValue.resolveListWith_anchorsLookup (vs : List YamlValue)
    (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliasesWith.resolveListWith vs (anchorsLookup anchors)
      = YamlValue.resolveAliases.resolveList vs anchors := by
  match vs with
  | [] => rfl
  | v :: vs =>
    simp only [YamlValue.resolveAliasesWith.resolveListWith, YamlValue.resolveAliases.resolveList]
    rw [resolveAliasesWith_anchorsLookup, resolveListWith_anchorsLookup]

lemma YamlValue.resolvePairsWith_anchorsLookup (ps : List (YamlValue × YamlValue))
    (anchors : Array (String × YamlValue)) :
    YamlValue.resolveAliasesWith.resolvePairsWith ps (anchorsLookup anchors)
      = YamlValue.resolveAliases.resolvePairs ps anchors := by
  match ps with
  | [] => rfl
  | (k, v) :: rest =>
    simp only [YamlValue.resolveAliasesWith.resolvePairsWith, YamlValue.resolveAliases.resolvePairs]
    rw [resolveAliasesWith_anchorsLookup, resolveAliasesWith_anchorsLookup,
        resolvePairsWith_anchorsLookup]
end

/-- Resolving through an `AnchorIndex` is resolving against its array. -/
@[simp] lemma YamlValue.resolveAliasesWith_find? (v : YamlValue)
    {anchors : Array (String × YamlValue)} (idx : AnchorIndex anchors) :
    v.resolveAliasesWith idx.find? = v.resolveAliases anchors := by
  have h : idx.find? = anchorsLookup anchors := funext idx.find?_eq
  rw [h, YamlValue.resolveAliasesWith_anchorsLookup]

end L4YAML

end Blanket
