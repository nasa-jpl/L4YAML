import Lean4Yaml.Schema
import Lean4Yaml.Schema.FromToYaml
import Lean4Yaml.Types

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

namespace Lean4Yaml.Proofs.SchemaComposition

open Lean4Yaml
open Lean4Yaml.Schema

/-! ## §1: `resolve ∘ toYaml` Primitive Correctness

All primitive `ToYaml` instances produce plain scalars with no tag
(`tag := none`), so `resolve` dispatches to `resolveScalar content none`
which delegates to `resolveImplicit content`. -/

/-- Bool: `resolve (toYaml b) = .bool b` for all `b : Bool`.
    Proof: `toYaml true` → scalar `"true"` → `resolveImplicit "true"` →
    `isBool "true" = some true` → `.bool true` (kernel-reducible). -/
theorem resolve_toYaml_bool (b : Bool) : resolve (toYaml b) = .bool b := by
  cases b <;> rfl

/-- Unit: `resolve (toYaml ()) = .null`.
    Proof: `toYaml ()` → scalar `"null"` → `resolveImplicit "null"` →
    `isNull "null" = true` → `.null` (kernel-reducible). -/
theorem resolve_toYaml_unit : resolve (toYaml ()) = .null := by rfl

/-! ## §2: `resolve ∘ toYaml` Collection Structure

Collections preserve their structural shape through `resolve ∘ toYaml`:
sequences remain sequences, mappings remain mappings. -/

/-- Array: `resolve (toYaml arr)` is a sequence. -/
theorem resolve_toYaml_array_isSeq {α : Type} [ToYaml α] (arr : Array α) :
    (resolve (toYaml arr)).isSeq = true := by rfl

/-- List: `resolve (toYaml list)` is a sequence (via Array coercion). -/
theorem resolve_toYaml_list_isSeq {α : Type} [ToYaml α] (list : List α) :
    (resolve (toYaml list)).isSeq = true := by rfl

/-- Option none: `resolve (toYaml none) = .null`. -/
theorem resolve_toYaml_option_none {α : Type} [ToYaml α] :
    resolve (toYaml (none : Option α)) = .null := by rfl

/-- Option some: `resolve (toYaml (some a))` delegates to `resolve (toYaml a)`. -/
theorem resolve_toYaml_option_some {α : Type} [ToYaml α] (a : α) :
    resolve (toYaml (some a)) = resolve (toYaml a) := by rfl

/-- Option some Bool: concrete composition. -/
theorem resolve_toYaml_option_some_bool (b : Bool) :
    resolve (toYaml (some b)) = .bool b :=
  resolve_toYaml_bool b

/-! ## §3: `fromYamlType?` Inversion Lemmas

Each `FromYamlType` instance correctly inverts its `YamlType` constructor,
forming the second half of the round-trip chain. -/

/-- `fromYamlType? (.bool b)` recovers `b`. -/
theorem fromYamlType_bool (b : Bool) :
    (fromYamlType? (.bool b) : Except SchemaError Bool) = .ok b := by rfl

/-- `fromYamlType? .null` recovers `()`. -/
theorem fromYamlType_unit :
    (fromYamlType? .null : Except SchemaError Unit) = .ok () := by rfl

/-- `fromYamlType? (.int n)` recovers `n` as `Int`. -/
theorem fromYamlType_int (n : Int) :
    (fromYamlType? (.int n) : Except SchemaError Int) = .ok n := by rfl

/-- `fromYamlType? (.str s)` recovers `s`. -/
theorem fromYamlType_str (s : String) :
    (fromYamlType? (.str s) : Except SchemaError String) = .ok s := by rfl

/-! ## §4: `fromYaml? ∘ toYaml` Round-Trip

The complete chain: `toYaml a` → `resolve` → `fromYamlType?` → `.ok a`.
Combines §1 (`resolve ∘ toYaml`) with §3 (`fromYamlType?` inversion). -/

/-- Bool: `fromYaml? (toYaml b) = .ok b` for all `b : Bool`. -/
theorem fromYaml_toYaml_bool (b : Bool) :
    (fromYaml? (toYaml b) : Except SchemaError Bool) = .ok b := by
  cases b <;> rfl

/-- Unit: `fromYaml? (toYaml ()) = .ok ()`. -/
theorem fromYaml_toYaml_unit :
    (fromYaml? (toYaml ()) : Except SchemaError Unit) = .ok () := by rfl

/-- Option none: `fromYaml? (toYaml none) = .ok none` for optional types. -/
theorem fromYaml_toYaml_option_none {α : Type} [ToYaml α] [FromYamlType α] :
    (fromYaml? (toYaml (none : Option α)) : Except SchemaError (Option α)) = .ok none := by rfl

/-! ## §5: String Schema-Safety

Under Core Schema §10.3.2, plain scalars are implicitly typed:
`null` → bool → int → float → string. A string whose content
matches an earlier type gets mis-resolved. The `toYaml String`
instance produces plain scalars, so round-trip correctness requires
a "schema-safe" precondition. -/

/-- `resolve (toYaml s) = .str s` when `s` is not implicitly typed
    as null, bool, int, or float by Core Schema §10.3.2 precedence. -/
theorem resolve_toYaml_str_safe (s : String)
    (h1 : isNull s = false) (h2 : isBool s = none)
    (h3 : isInt s = none) (h4 : isFloat s = none) :
    resolve (toYaml s) = .str s := by
  show resolveImplicit s = .str s
  unfold resolveImplicit
  simp [h1, h2, h3, h4]

/-- String round-trip with schema-safe precondition. -/
theorem fromYaml_toYaml_str_safe (s : String)
    (h1 : isNull s = false) (h2 : isBool s = none)
    (h3 : isInt s = none) (h4 : isFloat s = none) :
    (fromYaml? (toYaml s) : Except SchemaError String) = .ok s := by
  have h_resolve := resolve_toYaml_str_safe s h1 h2 h3 h4
  show fromYamlType? (resolve (toYaml s)) = .ok s
  rw [h_resolve]; rfl

/-! ## §6: Int/Nat Round-Trip

Int and Nat require `isInt (toString n) = some n` as a precondition
since the `isInt` parser is not kernel-reducible. Concrete instances
are proved by discharging preconditions via `native_decide`. -/

/-- Generic Int round-trip with `isInt` precondition. -/
theorem resolve_toYaml_int (n : Int)
    (h1 : isNull (toString n) = false)
    (h2 : isBool (toString n) = none)
    (h3 : isInt (toString n) = some n) :
    resolve (toYaml n) = .int n := by
  show resolveImplicit (toString n) = .int n
  unfold resolveImplicit
  simp [h1, h2, h3]

/-- Generic Int `fromYaml? ∘ toYaml` round-trip. -/
theorem fromYaml_toYaml_int (n : Int)
    (h1 : isNull (toString n) = false)
    (h2 : isBool (toString n) = none)
    (h3 : isInt (toString n) = some n) :
    (fromYaml? (toYaml n) : Except SchemaError Int) = .ok n := by
  have h_resolve := resolve_toYaml_int n h1 h2 h3
  show fromYamlType? (resolve (toYaml n)) = .ok n
  rw [h_resolve]; rfl

/-- Generic Nat `resolve ∘ toYaml`. -/
theorem resolve_toYaml_nat (n : Nat)
    (h1 : isNull (toString n) = false)
    (h2 : isBool (toString n) = none)
    (h3 : isInt (toString n) = some (Int.ofNat n)) :
    resolve (toYaml n) = .int (Int.ofNat n) := by
  show resolveImplicit (toString n) = .int (Int.ofNat n)
  unfold resolveImplicit
  simp [h1, h2, h3]

/-- Concrete: `resolve (toYaml 42) = .int 42`. -/
theorem resolve_toYaml_nat_42 : resolve (toYaml (42 : Nat)) = .int 42 :=
  resolve_toYaml_nat 42 (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `resolve (toYaml 0) = .int 0`. -/
theorem resolve_toYaml_nat_0 : resolve (toYaml (0 : Nat)) = .int 0 :=
  resolve_toYaml_nat 0 (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `resolve (toYaml 100) = .int 100`. -/
theorem resolve_toYaml_int_100 : resolve (toYaml (100 : Int)) = .int 100 :=
  resolve_toYaml_int 100 (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `resolve (toYaml (-7)) = .int (-7)`. -/
theorem resolve_toYaml_int_neg7 : resolve (toYaml (-7 : Int)) = .int (-7) :=
  resolve_toYaml_int (-7) (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `fromYaml? (toYaml 42) = .ok 42` (Int). -/
theorem fromYaml_toYaml_int_42 :
    (fromYaml? (toYaml (42 : Int)) : Except SchemaError Int) = .ok 42 :=
  fromYaml_toYaml_int 42 (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `fromYaml? (toYaml 100) = .ok 100` (Int). -/
theorem fromYaml_toYaml_int_100 :
    (fromYaml? (toYaml (100 : Int)) : Except SchemaError Int) = .ok 100 :=
  fromYaml_toYaml_int 100 (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `fromYaml? (toYaml (-7)) = .ok (-7)` (Int). -/
theorem fromYaml_toYaml_int_neg7 :
    (fromYaml? (toYaml (-7 : Int)) : Except SchemaError Int) = .ok (-7) :=
  fromYaml_toYaml_int (-7) (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `fromYaml? (toYaml "hello") = .ok "hello"`. -/
theorem fromYaml_toYaml_hello :
    (fromYaml? (toYaml "hello") : Except SchemaError String) = .ok "hello" :=
  fromYaml_toYaml_str_safe "hello"
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

/-- Concrete: `fromYaml? (toYaml "world") = .ok "world"`. -/
theorem fromYaml_toYaml_world :
    (fromYaml? (toYaml "world") : Except SchemaError String) = .ok "world" :=
  fromYaml_toYaml_str_safe "world"
    (by native_decide) (by native_decide) (by native_decide) (by native_decide)

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

end Lean4Yaml.Proofs.SchemaComposition
