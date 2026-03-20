/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Schema
import Lean4Yaml.Schema.FromToYaml
import Lean4Yaml.Schema.Struct

/-!
# Error Type Properties

Formal properties of the structured error types `ScanError`, `SchemaError`,
and `YamlError` introduced in the v0.2.0 exception refactoring.

These theorems were impossible with the prior `Except String` API because
string equality is opaque — there is no way to prove that a scanner error
string can never equal a schema error string.  With algebraic error types,
these properties follow directly from constructor disjointness.

## Sections

1. **Error Lifting** — coercion preserves `toString`
2. **Discriminability** — scanner ≠ schema at the `YamlError` level
3. **Injectivity** — `YamlError` constructors are injective
4. **Error Coverage** — exact error characterisation for `getMapping`, `getString`,
   `fromYamlType?` instances
-/

namespace Lean4Yaml.Proofs.ErrorProperties

open Lean4Yaml
open Lean4Yaml.Schema

/-! ## §1  Error Lifting Lemmas

The `Coe ScanError YamlError` and `Coe SchemaError YamlError` instances
wrap errors in `YamlError.scanError` / `YamlError.schemaError`.  These
lemmas confirm that `toString` round-trips through the coercion.
-/

/-- Coercing a `ScanError` to `YamlError` preserves its string representation. -/
theorem coe_scan_error_toString (e : ScanError) :
    (e : YamlError).toString = e.toString := rfl

/-- Coercing a `SchemaError` to `YamlError` preserves its string representation. -/
theorem coe_schema_error_toString (e : SchemaError) :
    (e : YamlError).toString = e.toString := rfl

/-! ## §2  Discriminability

Scanner and schema errors occupy disjoint constructors of `YamlError`.
-/

/-- A scan error wrapped in `YamlError` is never equal to a schema error. -/
theorem scan_error_ne_schema_error (se : ScanError) (sce : SchemaError) :
    YamlError.scanError se ≠ YamlError.schemaError sce := by
  intro h; cases h

/-! ## §3  Constructor Injectivity -/

/-- `YamlError.scanError` is injective. -/
theorem yaml_error_scan_injective {e₁ e₂ : ScanError} :
    YamlError.scanError e₁ = YamlError.scanError e₂ → e₁ = e₂ := by
  intro h; cases h; rfl

/-- `YamlError.schemaError` is injective. -/
theorem yaml_error_schema_injective {e₁ e₂ : SchemaError} :
    YamlError.schemaError e₁ = YamlError.schemaError e₂ → e₁ = e₂ := by
  intro h; cases h; rfl

/-! ## §4  Error Coverage — Struct Helpers

Exact characterisation of the errors produced by the struct helper functions
in `Schema/Struct.lean`.  Each theorem proves that the function can only
produce the specific `SchemaError` constructor(s) visible in its definition.
-/

/-- `getMapping` only produces `.notAMapping`: if it errors, the error is exactly `.notAMapping v`. -/
theorem getMapping_error {v : YamlValue} {e : SchemaError}
    (h : getMapping v = .error e) : e = .notAMapping v := by
  cases v <;> simp_all [getMapping]

/-- `getString` only produces `.notAScalar`: if it errors, the error is exactly `.notAScalar v`. -/
theorem getString_error {v : YamlValue} {e : SchemaError}
    (h : getString v = .error e) : e = .notAScalar v := by
  cases v <;> simp_all [getString]

/-! ## §5  Error Coverage — FromYamlType Instances

Each primitive `FromYamlType` instance maps a narrow set of `YamlType` constructors
to success and reports a unique error constructor for everything else.
-/

/-- `fromYamlType? Unit` only produces `.expectedNull`. -/
theorem fromYamlType_unit_error {t : Schema.YamlType} {e : SchemaError} :
    (fromYamlType? t : Except SchemaError Unit) = .error e → e = .expectedNull t := by
  intro h; cases t <;> simp_all [fromYamlType?, FromYamlType.fromYamlType?]

/-- `fromYamlType? Bool` only produces `.expectedBoolean`. -/
theorem fromYamlType_bool_error {t : Schema.YamlType} {e : SchemaError} :
    (fromYamlType? t : Except SchemaError Bool) = .error e → e = .expectedBoolean t := by
  intro h; cases t <;> simp_all [fromYamlType?, FromYamlType.fromYamlType?]

/-- `fromYamlType? Int` only produces `.expectedInteger`. -/
theorem fromYamlType_int_error {t : Schema.YamlType} {e : SchemaError} :
    (fromYamlType? t : Except SchemaError Int) = .error e → e = .expectedInteger t := by
  intro h; cases t <;> simp_all [fromYamlType?, FromYamlType.fromYamlType?]

/-- `fromYamlType? String` only produces `.expectedString`. -/
theorem fromYamlType_string_error {t : Schema.YamlType} {e : SchemaError} :
    (fromYamlType? t : Except SchemaError String) = .error e → e = .expectedString t := by
  intro h; cases t <;> simp_all [fromYamlType?, FromYamlType.fromYamlType?]

/-- `fromYamlType? Nat` produces exactly `.expectedInteger` or `.negativeNat`. -/
theorem fromYamlType_nat_error {t : Schema.YamlType} {e : SchemaError} :
    (fromYamlType? t : Except SchemaError Nat) = .error e →
    e = .expectedInteger t ∨ ∃ n : Int, t = .int n ∧ n < 0 ∧ e = .negativeNat n := by
  intro h
  cases t with
  | int n =>
    simp only [fromYamlType?, FromYamlType.fromYamlType?] at h
    split at h
    · cases h
    · right
      refine ⟨n, rfl, by omega, ?_⟩
      cases h; rfl
  | _ => left; simp_all [fromYamlType?, FromYamlType.fromYamlType?]

end Lean4Yaml.Proofs.ErrorProperties
