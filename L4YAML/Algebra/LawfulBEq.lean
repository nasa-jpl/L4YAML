/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Completeness

/-!
# LawfulBEq Instances  (Algebra Item 23)

Proves `LawfulBEq` for the YAML AST type hierarchy:

1. **Enums**: `ScalarStyle`, `ChompStyle`, `CollectionStyle` — by `decide`
2. **Structs**: `BlockScalarMeta`, `Scalar` — field-wise `eq_of_beq`
3. **`YamlValue`**: structural recursion with `where`-clause list helpers,
   matching the pattern of `decEqYamlValue` in `Completeness.lean`

## Why Explicit BEq Definitions?

Both `Scalar` and `YamlValue` use explicit `BEq` definitions
(`beqScalar` / `beqYamlValue` in `Types.lean`) instead of `deriving BEq`:

- **`YamlValue`**: Auto-derived BEq for recursive inductives with `Array`
  fields generates an **opaque** function, blocking all proof tactics.
- **`Scalar`**: Auto-derived BEq uses `Decidable.rec` for `String` field
  comparison, which blocks `cases` tactic with dependent elimination failures.

The explicit definitions compute the same results but remain **transparent**,
enabling the equational lemmas and structural proofs below.

## Equational Lemmas

Since `beqYamlValue` compiles via `brecOn` (no auto-generated equational
theorems), we provide manual `@[simp]` lemmas for each constructor pair,
all proved by `rfl`.

## Provenance

Migrated from `L4YAML/Proofs/Foundation/LawfulBEq.lean` during
Initiative 4 Phase 2 (D4: one file per item-cluster). No semantic
change; namespace move only — the namespace changes from
`L4YAML.Proofs.LawfulBEq` to `L4YAML.Algebra.LawfulBEq`.
-/

namespace L4YAML.Algebra.LawfulBEq

open L4YAML

/-! ## §1  Enum LawfulBEq Instances -/

instance : LawfulBEq ScalarStyle where
  rfl {a} := by cases a <;> decide
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

instance : LawfulBEq ChompStyle where
  rfl {a} := by cases a <;> decide
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

instance : LawfulBEq CollectionStyle where
  rfl {a} := by cases a <;> decide
  eq_of_beq {a b} h := by
    cases a <;> cases b <;> first | rfl | exact absurd h (by decide)

/-! ## §2  Struct LawfulBEq Instances -/

instance : LawfulBEq BlockScalarMeta where
  rfl {a} := by
    cases a; unfold BEq.beq
    dsimp [instBEqBlockScalarMeta, instBEqBlockScalarMeta.beq]; simp
  eq_of_beq {a b} h := by
    cases a; cases b; unfold BEq.beq at h
    dsimp [instBEqBlockScalarMeta, instBEqBlockScalarMeta.beq] at h
    simp only [Bool.and_eq_true] at h
    have h1 := eq_of_beq h.1; have h2 := eq_of_beq h.2
    subst h1; subst h2; rfl

instance : LawfulBEq Scalar where
  rfl {a} := by
    cases a; show beqScalar _ _ = true; unfold beqScalar; simp
  eq_of_beq {a b} h := by
    cases a; cases b
    change beqScalar _ _ = true at h
    unfold beqScalar at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
    have := eq_of_beq h1; have := eq_of_beq h2; have := eq_of_beq h3
    have := eq_of_beq h4; have := eq_of_beq h5
    subst_vars; rfl

/-! ## §3  Equational Lemmas for `beqYamlValue`

Since `beqYamlValue` compiles via `brecOn`, Lean does not auto-generate
equational theorems. These manual `@[simp]` lemmas (all `rfl`) serve as
the basis for the `LawfulBEq YamlValue` proofs below.
-/

-- Same-constructor reductions
@[simp] theorem beqYamlValue_scalar (s₁ s₂ : Scalar) :
    beqYamlValue (.scalar s₁) (.scalar s₂) = (s₁ == s₂) := rfl

@[simp] theorem beqYamlValue_alias (n₁ n₂ : String) :
    beqYamlValue (.alias n₁) (.alias n₂) = (n₁ == n₂) := rfl

@[simp] theorem beqYamlValue_sequence (st₁ st₂ : CollectionStyle)
    (items₁ items₂ : Array YamlValue) (tag₁ tag₂ anc₁ anc₂ : Option String) :
    beqYamlValue (.sequence st₁ items₁ tag₁ anc₁) (.sequence st₂ items₂ tag₂ anc₂)
    = (st₁ == st₂ && beqYamlValue.beqList items₁.toList items₂.toList
       && tag₁ == tag₂ && anc₁ == anc₂) := rfl

@[simp] theorem beqYamlValue_mapping (st₁ st₂ : CollectionStyle)
    (pairs₁ pairs₂ : Array (YamlValue × YamlValue))
    (tag₁ tag₂ anc₁ anc₂ : Option String) :
    beqYamlValue (.mapping st₁ pairs₁ tag₁ anc₁) (.mapping st₂ pairs₂ tag₂ anc₂)
    = (st₁ == st₂ && beqYamlValue.beqPairList pairs₁.toList pairs₂.toList
       && tag₁ == tag₂ && anc₁ == anc₂) := rfl

-- Cross-constructor reductions (all `false`)
@[simp] theorem beqYV_sc_sq (s st items tag anc) :
    beqYamlValue (.scalar s) (.sequence st items tag anc) = false := rfl
@[simp] theorem beqYV_sc_mp (s st pairs tag anc) :
    beqYamlValue (.scalar s) (.mapping st pairs tag anc) = false := rfl
@[simp] theorem beqYV_sc_al (s n) :
    beqYamlValue (.scalar s) (.alias n) = false := rfl
@[simp] theorem beqYV_sq_sc (st items tag anc s) :
    beqYamlValue (.sequence st items tag anc) (.scalar s) = false := rfl
@[simp] theorem beqYV_sq_mp (st₁ items tag₁ anc₁ st₂ pairs tag₂ anc₂) :
    beqYamlValue (.sequence st₁ items tag₁ anc₁) (.mapping st₂ pairs tag₂ anc₂) = false := rfl
@[simp] theorem beqYV_sq_al (st items tag anc n) :
    beqYamlValue (.sequence st items tag anc) (.alias n) = false := rfl
@[simp] theorem beqYV_mp_sc (st pairs tag anc s) :
    beqYamlValue (.mapping st pairs tag anc) (.scalar s) = false := rfl
@[simp] theorem beqYV_mp_sq (st₁ pairs tag₁ anc₁ st₂ items tag₂ anc₂) :
    beqYamlValue (.mapping st₁ pairs tag₁ anc₁) (.sequence st₂ items tag₂ anc₂) = false := rfl
@[simp] theorem beqYV_mp_al (st pairs tag anc n) :
    beqYamlValue (.mapping st pairs tag anc) (.alias n) = false := rfl
@[simp] theorem beqYV_al_sc (n s) :
    beqYamlValue (.alias n) (.scalar s) = false := rfl
@[simp] theorem beqYV_al_sq (n st items tag anc) :
    beqYamlValue (.alias n) (.sequence st items tag anc) = false := rfl
@[simp] theorem beqYV_al_mp (n st pairs tag anc) :
    beqYamlValue (.alias n) (.mapping st pairs tag anc) = false := rfl

-- List helper reductions
@[simp] theorem beqList_nil :
    beqYamlValue.beqList [] [] = true := rfl
@[simp] theorem beqList_cons (a b : YamlValue) (as bs : List YamlValue) :
    beqYamlValue.beqList (a :: as) (b :: bs)
    = (beqYamlValue a b && beqYamlValue.beqList as bs) := rfl
@[simp] theorem beqList_nil_cons (b : YamlValue) (bs : List YamlValue) :
    beqYamlValue.beqList [] (b :: bs) = false := rfl
@[simp] theorem beqList_cons_nil (a : YamlValue) (as : List YamlValue) :
    beqYamlValue.beqList (a :: as) [] = false := rfl

-- Pair-list helper reductions
@[simp] theorem beqPairList_nil :
    beqYamlValue.beqPairList [] [] = true := rfl
@[simp] theorem beqPairList_cons (k₁ v₁ : YamlValue)
    (rest₁ : List (YamlValue × YamlValue))
    (k₂ v₂ : YamlValue) (rest₂ : List (YamlValue × YamlValue)) :
    beqYamlValue.beqPairList ((k₁, v₁) :: rest₁) ((k₂, v₂) :: rest₂)
    = (beqYamlValue k₁ k₂ && beqYamlValue v₁ v₂
       && beqYamlValue.beqPairList rest₁ rest₂) := rfl
@[simp] theorem beqPairList_nil_cons
    (p : YamlValue × YamlValue) (ps : List (YamlValue × YamlValue)) :
    beqYamlValue.beqPairList [] (p :: ps) = false := rfl
@[simp] theorem beqPairList_cons_nil
    (p : YamlValue × YamlValue) (ps : List (YamlValue × YamlValue)) :
    beqYamlValue.beqPairList (p :: ps) [] = false := rfl

/-! ## §4  `LawfulBEq YamlValue`

Uses structural recursion with `where`-clause list/pair-list helpers,
following the same mutual-recursion pattern as `decEqYamlValue`.

The `induction` tactic cannot be used directly because `YamlValue` is
a nested inductive (the `Array` fields make it so), hence we write
explicit pattern matches with recursive calls.
-/

-- `beq_self_eq_true` (a.k.a. `@[simp] ReflBEq.rfl`)
theorem beqYamlValue_rfl : ∀ (v : YamlValue), beqYamlValue v v = true
  | .scalar _ => by simp [beqYamlValue_scalar]
  | .alias _ => by simp [beqYamlValue_alias]
  | .sequence _ items _ _ => by
      simp only [beqYamlValue_sequence, beq_self_eq_true, Bool.true_and,
                  Bool.and_true]
      exact beqYamlValue_rfl.beqList_rfl items.toList
  | .mapping _ pairs _ _ => by
      simp only [beqYamlValue_mapping, beq_self_eq_true, Bool.true_and,
                  Bool.and_true]
      exact beqYamlValue_rfl.beqPairList_rfl pairs.toList
where
  beqList_rfl : ∀ (l : List YamlValue), beqYamlValue.beqList l l = true
    | [] => rfl
    | a :: as => by simp [beqList_cons, beqYamlValue_rfl a, beqList_rfl as]
  beqPairList_rfl : ∀ (l : List (YamlValue × YamlValue)),
      beqYamlValue.beqPairList l l = true
    | [] => rfl
    | (k, v) :: rest => by
        simp [beqPairList_cons, beqYamlValue_rfl k, beqYamlValue_rfl v,
              beqPairList_rfl rest]

-- `eq_of_beq` via structural case analysis on all constructor pairs
theorem beqYamlValue_eq : ∀ (a b : YamlValue),
    beqYamlValue a b = true → a = b
  | .scalar s₁, .scalar s₂, h => by
      simp [beqYamlValue_scalar] at h; exact congrArg _ h
  | .scalar _, .sequence .., h => by simp at h
  | .scalar _, .mapping .., h => by simp at h
  | .scalar _, .alias _, h => by simp at h
  | .alias n₁, .alias n₂, h => by
      simp [beqYamlValue_alias] at h; exact congrArg _ h
  | .alias _, .scalar _, h => by simp at h
  | .alias _, .sequence .., h => by simp at h
  | .alias _, .mapping .., h => by simp at h
  | .sequence st₁ items₁ tag₁ anc₁, .sequence st₂ items₂ tag₂ anc₂, h => by
      simp only [beqYamlValue_sequence, Bool.and_eq_true] at h
      obtain ⟨⟨⟨h_st, h_items⟩, h_tag⟩, h_anc⟩ := h
      have h_st := eq_of_beq h_st
      have h_tag := eq_of_beq h_tag
      have h_anc := eq_of_beq h_anc
      subst h_st; subst h_tag; subst h_anc; congr 1
      have h_list := beqYamlValue_eq.beqList_eq items₁.toList items₂.toList h_items
      cases items₁; cases items₂; exact congrArg Array.mk h_list
  | .sequence .., .scalar _, h => by simp at h
  | .sequence .., .mapping .., h => by simp at h
  | .sequence .., .alias _, h => by simp at h
  | .mapping st₁ pairs₁ tag₁ anc₁, .mapping st₂ pairs₂ tag₂ anc₂, h => by
      simp only [beqYamlValue_mapping, Bool.and_eq_true] at h
      obtain ⟨⟨⟨h_st, h_pairs⟩, h_tag⟩, h_anc⟩ := h
      have h_st := eq_of_beq h_st
      have h_tag := eq_of_beq h_tag
      have h_anc := eq_of_beq h_anc
      subst h_st; subst h_tag; subst h_anc; congr 1
      have h_list :=
        beqYamlValue_eq.beqPairList_eq pairs₁.toList pairs₂.toList h_pairs
      cases pairs₁; cases pairs₂; exact congrArg Array.mk h_list
  | .mapping .., .scalar _, h => by simp at h
  | .mapping .., .sequence .., h => by simp at h
  | .mapping .., .alias _, h => by simp at h
where
  beqList_eq : ∀ (as bs : List YamlValue),
      beqYamlValue.beqList as bs = true → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by simp at h
    | _ :: _, [], h => by simp at h
    | a :: as, b :: bs, h => by
        simp [beqList_cons, Bool.and_eq_true] at h
        have hab := beqYamlValue_eq a b h.1
        have habs := beqList_eq as bs h.2
        subst hab; subst habs; rfl
  beqPairList_eq : ∀ (as bs : List (YamlValue × YamlValue)),
      beqYamlValue.beqPairList as bs = true → as = bs
    | [], [], _ => rfl
    | [], _ :: _, h => by simp at h
    | _ :: _, [], h => by simp at h
    | (k₁, v₁) :: rest₁, (k₂, v₂) :: rest₂, h => by
        simp [beqPairList_cons, Bool.and_eq_true] at h
        obtain ⟨⟨hk, hv⟩, hrest⟩ := h
        have := beqYamlValue_eq k₁ k₂ hk
        have := beqYamlValue_eq v₁ v₂ hv
        have := beqPairList_eq rest₁ rest₂ hrest
        subst_vars; rfl

instance : LawfulBEq YamlValue where
  rfl := beqYamlValue_rfl _
  eq_of_beq h := beqYamlValue_eq _ _ h

end L4YAML.Algebra.LawfulBEq
