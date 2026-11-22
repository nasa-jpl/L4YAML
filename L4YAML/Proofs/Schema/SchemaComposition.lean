module

public import L4YAML.Schema.Schema

public meta import L4YAML.Schema.Schema
public import L4YAML.Schema.FromToYaml
public import L4YAML.Spec.Types

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Schema Composition Proofs (Phase 7.5)

Proves round-trip properties for the composed schema layer:
1. `resolve ∘ toYaml` — schema resolution correctly recovers type information
2. `fromYaml? ∘ toYaml` — the full type conversion round-trips

## Key Results

### §1: `resolve ∘ toYaml` Primitive Correctness
For each primitive `ToYaml` instance, `resolve (toYaml a)` produces
the expected `YamlType` constructor. All primitive `ToYaml` instances
produce plain scalars with no tag, so resolution goes through
`resolveImplicit`.

### §2: `resolve ∘ toYaml` Collection Structure
Collections preserve their shape through `resolve ∘ toYaml`.

### §3: `fromYamlType?` Inversion Lemmas
Each `FromYamlType` instance correctly inverts its `YamlType` constructor.

### §4: `fromYaml? ∘ toYaml` Round-Trip
For types with both `ToYaml` and `FromYaml` (via `FromYamlType`),
`fromYaml? (toYaml a) = .ok a`.

### §5: String Schema-Safety
Strings require a precondition: the content must not be implicitly
typed as null/bool/int/float by Core Schema §10.3.2 precedence.

### §6: Int/Nat Round-Trip
Generic round-trip for `Int` and `Nat` with `isInt (toString n)`
precondition, plus concrete instances via `native_decide`.

### §7: `#guard` Compile-Time Composition Checks

## Zero Axioms

All theorems are machine-checked. No `sorry`, no `axiom`, no `partial`.
-/

namespace L4YAML.Proofs.SchemaComposition

open L4YAML
open L4YAML.Schema

/-! ## §1: `resolve ∘ toYaml` Primitive Correctness

The non-string primitive `ToYaml` instances produce plain scalars carrying the
Core Schema tag of their type (`coreScalar "!!bool" "true"`), so `resolve`
dispatches to `resolveScalar content (some (normalizeTag "!!bool"))`.  The tag
shorthands expand to the URIs `resolveScalar` matches on: -/

@[simp] lemma normalizeTag_null : normalizeTag "!!null" = "tag:yaml.org,2002:null" := by
  native_decide
@[simp] lemma normalizeTag_bool : normalizeTag "!!bool" = "tag:yaml.org,2002:bool" := by
  native_decide
@[simp] lemma normalizeTag_int : normalizeTag "!!int" = "tag:yaml.org,2002:int" := by
  native_decide
@[simp] lemma normalizeTag_float : normalizeTag "!!float" = "tag:yaml.org,2002:float" := by
  native_decide

/-- `resolve` of a tagged plain scalar is `resolveScalar` under the expanded tag. -/
lemma resolve_coreScalar (tag content : String) :
    resolve (coreScalar tag content) = resolveScalar content (some (normalizeTag tag)) := rfl

/-- Bool: `resolve (toYaml b) = .bool b` for all `b : Bool`. -/
lemma resolve_toYaml_bool (b : Bool) : resolve (toYaml b) = .bool b := by
  cases b
  · show resolveScalar "false" (some (normalizeTag "!!bool")) = .bool false
    rw [normalizeTag_bool]; rfl
  · show resolveScalar "true" (some (normalizeTag "!!bool")) = .bool true
    rw [normalizeTag_bool]; rfl

/-- Unit: `resolve (toYaml ()) = .null`. -/
lemma resolve_toYaml_unit : resolve (toYaml ()) = .null := by
  show resolveScalar "null" (some (normalizeTag "!!null")) = .null
  rw [normalizeTag_null]; rfl

/-! ## §2: `resolve ∘ toYaml` Collection Structure

Collections preserve their structural shape through `resolve ∘ toYaml`:
sequences remain sequences, mappings remain mappings. -/

/-- Array: `resolve (toYaml arr)` is a sequence. -/
lemma resolve_toYaml_array_isSeq {α : Type} [ToYaml α] (arr : Array α) :
    (resolve (toYaml arr)).isSeq = true := by rfl

/-- List: `resolve (toYaml list)` is a sequence (via Array coercion). -/
lemma resolve_toYaml_list_isSeq {α : Type} [ToYaml α] (list : List α) :
    (resolve (toYaml list)).isSeq = true := by rfl

/-- Option none: `resolve (toYaml none) = .null`. -/
lemma resolve_toYaml_option_none {α : Type} [ToYaml α] :
    resolve (toYaml (none : Option α)) = .null := by
  show resolveScalar "null" (some (normalizeTag "!!null")) = .null
  rw [normalizeTag_null]; rfl

/-- Option some: `resolve (toYaml (some a))` delegates to `resolve (toYaml a)`. -/
lemma resolve_toYaml_option_some {α : Type} [ToYaml α] (a : α) :
    resolve (toYaml (some a)) = resolve (toYaml a) := by rfl

/-- Option some Bool: concrete composition. -/
lemma resolve_toYaml_option_some_bool (b : Bool) :
    resolve (toYaml (some b)) = .bool b :=
  resolve_toYaml_bool b

/-! ## §3: `fromYamlType?` Inversion Lemmas

Each `FromYamlType` instance correctly inverts its `YamlType` constructor,
forming the second half of the round-trip chain. -/

/-- `fromYamlType? (.bool b)` recovers `b`. -/
lemma fromYamlType_bool (b : Bool) :
    (fromYamlType? (.bool b) : Except SchemaError Bool) = .ok b := by rfl

/-- `fromYamlType? .null` recovers `()`. -/
lemma fromYamlType_unit :
    (fromYamlType? .null : Except SchemaError Unit) = .ok () := by rfl

/-- `fromYamlType? (.int n)` recovers `n` as `Int`. -/
lemma fromYamlType_int (n : Int) :
    (fromYamlType? (.int n) : Except SchemaError Int) = .ok n := by rfl

/-- `fromYamlType? (.str s)` recovers `s`. -/
lemma fromYamlType_str (s : String) :
    (fromYamlType? (.str s) : Except SchemaError String) = .ok s := by rfl

/-! ## §4: `fromYaml? ∘ toYaml` Round-Trip

The complete chain: `toYaml a` → `resolve` → `fromYamlType?` → `.ok a`.
Combines §1 (`resolve ∘ toYaml`) with §3 (`fromYamlType?` inversion). -/

/-- Bool: `fromYaml? (toYaml b) = .ok b` for all `b : Bool`. -/
lemma fromYaml_toYaml_bool (b : Bool) :
    (fromYaml? (toYaml b) : Except SchemaError Bool) = .ok b := by
  show fromYamlType? (resolve (toYaml b)) = .ok b
  rw [resolve_toYaml_bool]; rfl

/-- Unit: `fromYaml? (toYaml ()) = .ok ()`. -/
lemma fromYaml_toYaml_unit :
    (fromYaml? (toYaml ()) : Except SchemaError Unit) = .ok () := by
  show fromYamlType? (resolve (toYaml ())) = .ok ()
  rw [resolve_toYaml_unit]; rfl

/-- Option none: `fromYaml? (toYaml none) = .ok none` for optional types. -/
lemma fromYaml_toYaml_option_none {α : Type} [ToYaml α] [FromYamlType α] :
    (fromYaml? (toYaml (none : Option α)) : Except SchemaError (Option α)) = .ok none := by
  show fromYamlType? (resolve (toYaml (none : Option α))) = .ok none
  rw [resolve_toYaml_option_none]; rfl

/-! ## §5: String Schema-Safety

Under Core Schema §10.3.2, plain scalars are implicitly typed:
`null` → bool → int → float → string.  The `toYaml String` instance
emits a plain scalar only when implicit resolution of the content is
already a string, and a double-quoted scalar otherwise — and a quoted
scalar is a string under §10.3.2 whatever it spells.  So every string
resolves to itself, with no schema-safety precondition. -/

/-- `resolve (toYaml s) = .str s` for every string `s`. -/
lemma resolve_toYaml_str (s : String) : resolve (toYaml s) = .str s := by
  show scalarType ⟨s, if (resolveImplicit s).isStr then .plain else .doubleQuoted,
                   none, none, none⟩ = .str s
  have hdq : (ScalarStyle.doubleQuoted == ScalarStyle.plain) = false := rfl
  have hpp : (ScalarStyle.plain == ScalarStyle.plain) = true := rfl
  cases h : (resolveImplicit s).isStr
  · simp [scalarType, hdq]
  · simp [scalarType, hpp]
    unfold resolveImplicit at h ⊢
    cases hn : isNull s <;> cases hb : isBool s <;> cases hi : isInt s <;>
      cases hf : isFloat s <;> simp_all [YamlType.isStr]

/-- Historical name: the schema-safety precondition is no longer needed. -/
lemma resolve_toYaml_str_safe (s : String) : resolve (toYaml s) = .str s :=
  resolve_toYaml_str s

/-- `fromYaml? (toYaml s) = .ok s` for every string `s`. -/
lemma fromYaml_toYaml_str (s : String) :
    (fromYaml? (toYaml s) : Except SchemaError String) = .ok s := by
  show fromYamlType? (resolve (toYaml s)) = .ok s
  rw [resolve_toYaml_str]; rfl

/-- Historical name: the schema-safety precondition is no longer needed. -/
lemma fromYaml_toYaml_str_safe (s : String) :
    (fromYaml? (toYaml s) : Except SchemaError String) = .ok s :=
  fromYaml_toYaml_str s

/-! ## §6: Int/Nat Round-Trip

Int and Nat require `isInt (toString n) = some n` as a precondition
since the `isInt` parser is not kernel-reducible. Concrete instances
are proved by discharging the precondition via `native_decide`.  (The
`!!int` tag the instances carry means null/bool are never consulted.) -/

/-- Generic Int round-trip with `isInt` precondition. -/
lemma resolve_toYaml_int (n : Int)
    (h3 : isInt (toString n) = some n) :
    resolve (toYaml n) = .int n := by
  show resolveScalar (toString n) (some (normalizeTag "!!int")) = .int n
  rw [normalizeTag_int]
  have h3' : isInt n.repr = some n := h3
  simp [resolveScalar, h3']

/-- Generic Int `fromYaml? ∘ toYaml` round-trip. -/
lemma fromYaml_toYaml_int (n : Int)
    (h3 : isInt (toString n) = some n) :
    (fromYaml? (toYaml n) : Except SchemaError Int) = .ok n := by
  have h_resolve := resolve_toYaml_int n h3
  show fromYamlType? (resolve (toYaml n)) = .ok n
  rw [h_resolve]; rfl

/-- Generic Nat `resolve ∘ toYaml`. -/
lemma resolve_toYaml_nat (n : Nat)
    (h3 : isInt (toString n) = some (Int.ofNat n)) :
    resolve (toYaml n) = .int (Int.ofNat n) := by
  show resolveScalar (toString n) (some (normalizeTag "!!int")) = .int (Int.ofNat n)
  rw [normalizeTag_int]
  have h3' : isInt (Nat.repr n) = some (Int.ofNat n) := h3
  simp [resolveScalar, h3']

/-- Concrete: `resolve (toYaml 42) = .int 42`. -/
lemma resolve_toYaml_nat_42 : resolve (toYaml (42 : Nat)) = .int 42 :=
  resolve_toYaml_nat 42 (by native_decide)

/-- Concrete: `resolve (toYaml 0) = .int 0`. -/
lemma resolve_toYaml_nat_0 : resolve (toYaml (0 : Nat)) = .int 0 :=
  resolve_toYaml_nat 0 (by native_decide)

/-- Concrete: `resolve (toYaml 100) = .int 100`. -/
lemma resolve_toYaml_int_100 : resolve (toYaml (100 : Int)) = .int 100 :=
  resolve_toYaml_int 100 (by native_decide)

/-- Concrete: `resolve (toYaml (-7)) = .int (-7)`. -/
lemma resolve_toYaml_int_neg7 : resolve (toYaml (-7 : Int)) = .int (-7) :=
  resolve_toYaml_int (-7) (by native_decide)

/-- Concrete: `fromYaml? (toYaml 42) = .ok 42` (Int). -/
lemma fromYaml_toYaml_int_42 :
    (fromYaml? (toYaml (42 : Int)) : Except SchemaError Int) = .ok 42 :=
  fromYaml_toYaml_int 42 (by native_decide)

/-- Concrete: `fromYaml? (toYaml 100) = .ok 100` (Int). -/
lemma fromYaml_toYaml_int_100 :
    (fromYaml? (toYaml (100 : Int)) : Except SchemaError Int) = .ok 100 :=
  fromYaml_toYaml_int 100 (by native_decide)

/-- Concrete: `fromYaml? (toYaml (-7)) = .ok (-7)` (Int). -/
lemma fromYaml_toYaml_int_neg7 :
    (fromYaml? (toYaml (-7 : Int)) : Except SchemaError Int) = .ok (-7) :=
  fromYaml_toYaml_int (-7) (by native_decide)

/-- Concrete: `fromYaml? (toYaml "hello") = .ok "hello"`. -/
lemma fromYaml_toYaml_hello :
    (fromYaml? (toYaml "hello") : Except SchemaError String) = .ok "hello" :=
  fromYaml_toYaml_str_safe "hello"

/-- Concrete: `fromYaml? (toYaml "world") = .ok "world"`. -/
lemma fromYaml_toYaml_world :
    (fromYaml? (toYaml "world") : Except SchemaError String) = .ok "world" :=
  fromYaml_toYaml_str_safe "world"

/-! ## §7: Helper Definitions for Compile-Time Checks -/

/-- Check that `resolve (toYaml a)` equals the expected `YamlType` (BEq-based). -/
def resolvesTo {α : Type} [ToYaml α] (a : α) (expected : YamlType) : Bool :=
  resolve (toYaml a) == expected

/-- Check that `fromYaml? (toYaml a)` round-trips to `.ok a` (BEq-based). -/
def schemaRoundTrips {α : Type} [ToYaml α] [FromYaml α] [BEq α] (a : α) : Bool :=
  match (fromYaml? (toYaml a) : Except SchemaError α) with
  | .ok v => v == a
  | .error _ => false

/-! ## §8: `#guard` Compile-Time Composition Checks

Moved to `Tests/Guards/Proofs/SchemaComposition.lean`.
-/

end L4YAML.Proofs.SchemaComposition

end Blanket
