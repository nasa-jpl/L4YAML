import L4YAML.Schema
import L4YAML.Types

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Schema Resolution Proofs

Formal verification of Core Schema (YAML 1.2.2 §10.3) resolution properties.

## Proof Inventory

### §1 — `isNull` / `isBool` / `isInt` / `isFloat` specifications
Concrete correctness theorems linking each resolution function to its
specification in the YAML 1.2.2 standard.

### §2 — `resolveImplicit` completeness and determinism
Every string resolves to exactly one `YamlType`.

### §3 — `resolve` structural preservation
Collection shape is preserved through resolution.

### §4 — `resolveScalar` explicit-tag dispatch
Explicit tags override implicit resolution.

### §5 — Compile-time `#guard` checks for concrete values
-/

namespace L4YAML.Schema.Proofs

open L4YAML.Schema
open L4YAML

/-! ## §1 — Resolution Function Specifications -/

/-- `isNull ""` — empty string is null per §10.3.2 -/
theorem isNull_empty : isNull "" = true := by native_decide

/-- `isNull "null"` — the word "null" is null -/
theorem isNull_null : isNull "null" = true := by native_decide

/-- `isNull "Null"` — title case "Null" is null -/
theorem isNull_Null : isNull "Null" = true := by native_decide

/-- `isNull "NULL"` — upper case "NULL" is null -/
theorem isNull_NULL : isNull "NULL" = true := by native_decide

/-- `isNull "~"` — tilde is null -/
theorem isNull_tilde : isNull "~" = true := by native_decide

/-- `isNull "hello"` — ordinary string is not null -/
theorem isNull_hello : isNull "hello" = false := by native_decide

/-- `isBool "true"` — lowercase true -/
theorem isBool_true : isBool "true" = some true := by native_decide

/-- `isBool "True"` — title case true -/
theorem isBool_True : isBool "True" = some true := by native_decide

/-- `isBool "TRUE"` — upper case true -/
theorem isBool_TRUE : isBool "TRUE" = some true := by native_decide

/-- `isBool "false"` — lowercase false -/
theorem isBool_false : isBool "false" = some false := by native_decide

/-- `isBool "False"` — title case false -/
theorem isBool_False : isBool "False" = some false := by native_decide

/-- `isBool "FALSE"` — upper case false -/
theorem isBool_FALSE : isBool "FALSE" = some false := by native_decide

/-- `isBool "yes"` — "yes" is NOT boolean in YAML 1.2.2 Core Schema (was in 1.1) -/
theorem isBool_yes : isBool "yes" = none := by native_decide

/-- `isBool "hello"` — ordinary string is not boolean -/
theorem isBool_hello : isBool "hello" = none := by native_decide

/-- `isInt "42"` — simple decimal integer -/
theorem isInt_42 : isInt "42" = some 42 := by native_decide

/-- `isInt "-17"` — negative integer -/
theorem isInt_neg17 : isInt "-17" = some (-17) := by native_decide

/-- `isInt "0"` — zero -/
theorem isInt_zero : isInt "0" = some 0 := by native_decide

/-- `isInt "0xFF"` — hexadecimal -/
theorem isInt_hex_ff : isInt "0xFF" = some 255 := by native_decide

/-- `isInt "0o17"` — octal -/
theorem isInt_octal_17 : isInt "0o17" = some 15 := by native_decide

/-- `isInt "hello"` — non-numeric string -/
theorem isInt_hello : isInt "hello" = none := by native_decide

/-- `isFloat ".inf"` — positive infinity -/
theorem isFloat_inf : isFloat ".inf" = some (.inf true) := by rfl

/-- `isFloat "-.inf"` — negative infinity -/
theorem isFloat_neg_inf : isFloat "-.inf" = some (.inf false) := by rfl

/-- `isFloat ".nan"` — not a number -/
theorem isFloat_nan : isFloat ".nan" = some .nan := by rfl

/-! ## §2 — `resolveImplicit` Completeness & Determinism -/

/-- `resolveImplicit` always produces a result — exhaustive coverage.
    This is trivially true since the function always reaches `.str s` fallback,
    but the theorem documents the contract. -/
theorem resolveImplicit_complete (s : String) :
    (resolveImplicit s).isNull || (resolveImplicit s).isBool ||
    (resolveImplicit s).isInt || (resolveImplicit s).isFloat ||
    (resolveImplicit s).isStr = true := by
  simp only [resolveImplicit]
  split
  · rfl  -- isNull
  · split
    · rfl  -- isBool = some b
    · split
      · rfl  -- isInt = some i
      · split
        · rfl  -- isFloat = some f
        · rfl  -- str fallback

/-- Null has highest precedence: null strings never resolve to bool/int/float/str. -/
theorem resolveImplicit_null_precedence (s : String) (h : isNull s = true) :
    resolveImplicit s = .null := by
  unfold resolveImplicit; simp [h]

/-- Concrete: `resolveImplicit "null"` = `.null` (kernel-reducible). -/
theorem resolveImplicit_null : resolveImplicit "null" = .null := by rfl

/-- Concrete: `resolveImplicit "true"` = `.bool true` (kernel-reducible). -/
theorem resolveImplicit_true : resolveImplicit "true" = .bool true := by rfl

/-! ## §3 — `resolve` Structural Preservation -/

/-- Resolving a sequence preserves the collection shape (it's still a seq). -/
theorem resolve_sequence_is_seq (style : CollectionStyle) (items : Array YamlValue)
    (tag : Option String) (anchor : Option String) :
    (resolve (.sequence style items tag anchor)).isSeq = true := by
  rfl

/-- Resolving a mapping preserves the collection shape (it's still a map). -/
theorem resolve_mapping_is_map (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag : Option String) (anchor : Option String) :
    (resolve (.mapping style pairs tag anchor)).isMap = true := by
  rfl

/-- `resolveScalar` always returns a leaf type (not seq/map).
    Proven by case-splitting on the tag then on implicit branches. -/
theorem resolveScalar_not_seq (content : String) (tag? : Option String) :
    (resolveScalar content tag?).isSeq = false := by
  simp only [resolveScalar]
  split
  · rfl  -- null tag
  · split <;> rfl  -- bool tag
  · split <;> rfl  -- int tag
  · split <;> rfl  -- float tag
  · rfl  -- str tag
  · rfl  -- unknown tag
  · -- none => resolveImplicit content
    simp only [resolveImplicit]
    split
    · rfl  -- isNull
    · split
      · rfl  -- isBool = some b
      · split
        · rfl  -- isInt = some i
        · split <;> rfl  -- isFloat = some f | str fallback

theorem resolveScalar_not_map (content : String) (tag? : Option String) :
    (resolveScalar content tag?).isMap = false := by
  simp only [resolveScalar]
  split
  · rfl  -- null tag
  · split <;> rfl  -- bool tag
  · split <;> rfl  -- int tag
  · split <;> rfl  -- float tag
  · rfl  -- str tag
  · rfl  -- unknown tag
  · -- none => resolveImplicit content
    simp only [resolveImplicit]
    split
    · rfl  -- isNull
    · split
      · rfl  -- isBool = some b
      · split
        · rfl  -- isInt = some i
        · split <;> rfl  -- isFloat = some f | str fallback

/-- Resolving a scalar produces a leaf type (corollary of the above). -/
theorem resolve_scalar_is_leaf (s : Scalar) :
    (resolve (.scalar s)).isSeq = false ∧ (resolve (.scalar s)).isMap = false :=
  ⟨resolveScalar_not_seq s.content s.tag, resolveScalar_not_map s.content s.tag⟩

/-! ## §4 — `resolveScalar` Explicit Tag Dispatch -/

/-- Explicit `!!str` tag always produces `.str`, regardless of content. -/
theorem resolveScalar_str_tag (content : String) :
    resolveScalar content (some "tag:yaml.org,2002:str") = .str content := by
  simp [resolveScalar]

/-- Explicit `!!null` tag always produces `.null`, regardless of content. -/
theorem resolveScalar_null_tag (content : String) :
    resolveScalar content (some "tag:yaml.org,2002:null") = .null := by
  simp [resolveScalar]

/-- No tag delegates to `resolveImplicit`. -/
theorem resolveScalar_no_tag (content : String) :
    resolveScalar content none = resolveImplicit content := by
  simp [resolveScalar]

/-! ## §5 — `#guard` Compile-Time Schema Resolution Checks

`YamlType` does not derive `DecidableEq` (due to `Float`), so concrete
resolution correctness is verified via `#guard` (which uses `BEq`) rather
than `native_decide` (which requires `Decidable`).

Moved to `Tests/Guards/Proofs/SchemaResolution.lean`.
-/


end L4YAML.Schema.Proofs
