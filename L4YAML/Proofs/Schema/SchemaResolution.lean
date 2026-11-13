module

public import L4YAML.Schema.Schema

public meta import L4YAML.Schema.Schema
public import L4YAML.Spec.Types
public import L4YAML.Spec.CoreSchema
public import L4YAML.Proofs.Schema.CoreRecognizerBridge

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Schema Resolution Proofs

Formal verification of Core Schema (YAML 1.2.2 §10.3) resolution properties.

## Proof Inventory

### §1 — `isNull` / `isBool` / `isInt` / `isFloat` specifications
Concrete correctness theorems for selected YAML 1.2.2 spellings. These do not
by themselves establish equivalence with the complete Core Schema table.

### §2 — `resolveImplicit` completeness and determinism
Every string resolves to exactly one `YamlType`.

### §3 — `resolve` structural preservation
Collection shape is preserved through resolution.

### §4 — `resolveScalar` explicit-tag dispatch
Explicit tags override implicit resolution.

### §5 — Compile-time `#guard` checks for concrete values
-/

namespace L4YAML.Proofs.SchemaResolution

open L4YAML.Schema
open L4YAML

/-! ## The external Core Schema correspondence obligation

`Spec.CoreSchema.tag` transcribes the ordered §10.3.2 regex table independently
of the implementation's numeric value converters. `scalarTag?` deliberately
forgets the value: conformance of numerical *values* is a different requirement.

The proof separates recognition, converter success, and output tagging.
`CoreRecognizerBridge` proves universal success of integer and float parsing
on every allowed spelling, while numeric **value** fidelity remains separate.
-/

/-- The tag of a constructed scalar, absent for collections. -/
def scalarTag? : YamlType → Option Spec.CoreSchema.Tag
  | .null => some .null
  | .bool _ => some .bool
  | .int _ => some .int
  | .float _ => some .float
  | .str _ => some .str
  | .seq _ | .map _ => none

/-- The per-input assurance obligation for a plain, implicitly tagged scalar. -/
def coreTagCorrespondence (s : String) : Prop :=
  scalarTag? (resolveImplicit s) = some (Spec.CoreSchema.tag s)

lemma coreNullRecognizer_matches_spec (s : String) :
    isNull s = Spec.CoreSchema.nullSpelling s := by
  simp [isNull, Spec.CoreSchema.nullSpelling, Bool.or_comm, Bool.or_left_comm]

lemma coreBoolRecognizer_matches_spec (s : String) :
    (isBool s).isSome = Spec.CoreSchema.boolSpelling s := by
  unfold isBool
  split <;> simp_all [Spec.CoreSchema.boolSpelling]

/-- Compositional bridge for the external §10.3.2 table; numeric converter
    success is supplied by `CoreRecognizerBridge` in the capstone below. -/
lemma coreTagCorrespondence_at_of_recognizers (s : String)
    (hint : Spec.CoreSchema.integerSpelling s = true → (isInt s).isSome = true)
    (hfloat : Spec.CoreSchema.floatSpelling s = true → (isFloat s).isSome = true) :
    coreTagCorrespondence s := by
  have hnull := coreNullRecognizer_matches_spec s
  have hbool := coreBoolRecognizer_matches_spec s
  have hi : (isInt s).isSome = Spec.CoreSchema.integerSpelling s := by
    cases h : Spec.CoreSchema.integerSpelling s with
    | false => simp [isInt, h]
    | true => exact hint h
  have hf : (isFloat s).isSome = Spec.CoreSchema.floatSpelling s := by
    cases h : Spec.CoreSchema.floatSpelling s with
    | false => simp [isFloat, h]
    | true => exact hfloat h
  cases hn : Spec.CoreSchema.nullSpelling s <;>
    cases hb : isBool s <;>
    cases hi' : isInt s <;>
    cases hf' : isFloat s <;>
    simp_all [coreTagCorrespondence, scalarTag?, resolveImplicit,
      Spec.CoreSchema.tag, Option.isSome]

/-- Intermediate lemma: universal tag correspondence reduces to the two
    successful-conversion premises. -/
lemma coreTagCorrespondenceAll_of_recognizers
    (hint : ∀ s : String, Spec.CoreSchema.integerSpelling s = true → (isInt s).isSome = true)
    (hfloat : ∀ s : String, Spec.CoreSchema.floatSpelling s = true → (isFloat s).isSome = true) :
    ∀ s : String, coreTagCorrespondence s := by
  intro s
  exact coreTagCorrespondence_at_of_recognizers s (hint s) (hfloat s)

/-- For every implicitly tagged plain scalar, `resolveImplicit` chooses the
    first matching YAML 1.2.2 Core Schema §10.3.2 tag. This does not claim
    correctly rounded numeric values or fidelity at an FFI boundary. -/
@[capstone]
theorem coreTagCorrespondenceAll : ∀ s : String, coreTagCorrespondence s := by
  exact coreTagCorrespondenceAll_of_recognizers
    CoreRecognizerBridge.int_some_of_integerSpelling
    CoreRecognizerBridge.float_some_of_floatSpelling

/-! ## §1 — Resolution Function Specifications -/

/-- `isNull ""` — empty string is null per §10.3.2 -/
lemma isNull_empty : isNull "" = true := by native_decide

/-- `isNull "null"` — the word "null" is null -/
lemma isNull_null : isNull "null" = true := by native_decide

/-- `isNull "Null"` — title case "Null" is null -/
lemma isNull_Null : isNull "Null" = true := by native_decide

/-- `isNull "NULL"` — upper case "NULL" is null -/
lemma isNull_NULL : isNull "NULL" = true := by native_decide

/-- `isNull "~"` — tilde is null -/
lemma isNull_tilde : isNull "~" = true := by native_decide

/-- `isNull "hello"` — ordinary string is not null -/
lemma isNull_hello : isNull "hello" = false := by native_decide

/-- `isBool "true"` — lowercase true -/
lemma isBool_true : isBool "true" = some true := by native_decide

/-- `isBool "True"` — title case true -/
lemma isBool_True : isBool "True" = some true := by native_decide

/-- `isBool "TRUE"` — upper case true -/
lemma isBool_TRUE : isBool "TRUE" = some true := by native_decide

/-- `isBool "false"` — lowercase false -/
lemma isBool_false : isBool "false" = some false := by native_decide

/-- `isBool "False"` — title case false -/
lemma isBool_False : isBool "False" = some false := by native_decide

/-- `isBool "FALSE"` — upper case false -/
lemma isBool_FALSE : isBool "FALSE" = some false := by native_decide

/-- `isBool "yes"` — "yes" is NOT boolean in YAML 1.2.2 Core Schema (was in 1.1) -/
lemma isBool_yes : isBool "yes" = none := by native_decide

/-- `isBool "hello"` — ordinary string is not boolean -/
lemma isBool_hello : isBool "hello" = none := by native_decide

/-- `isInt "42"` — simple decimal integer -/
lemma isInt_42 : isInt "42" = some 42 := by native_decide

/-- `isInt "-17"` — negative integer -/
lemma isInt_neg17 : isInt "-17" = some (-17) := by native_decide

/-- `isInt "0"` — zero -/
lemma isInt_zero : isInt "0" = some 0 := by native_decide

/-- `isInt "0xFF"` — hexadecimal -/
lemma isInt_hex_ff : isInt "0xFF" = some 255 := by native_decide

/-- `isInt "0o17"` — octal -/
lemma isInt_octal_17 : isInt "0o17" = some 15 := by native_decide

/-- `isInt "hello"` — non-numeric string -/
lemma isInt_hello : isInt "hello" = none := by native_decide

/-- `isFloat ".inf"` — positive infinity -/
lemma isFloat_inf : isFloat ".inf" = some (.inf true) := by rfl

/-- `isFloat "-.inf"` — negative infinity -/
lemma isFloat_neg_inf : isFloat "-.inf" = some (.inf false) := by rfl

/-- `isFloat ".nan"` — not a number -/
lemma isFloat_nan : isFloat ".nan" = some .nan := by rfl

/-! ## §2 — `resolveImplicit` Completeness & Determinism -/

/-- `resolveImplicit` always produces a result — exhaustive coverage.
    This is trivially true since the function always reaches `.str s` fallback,
    but the theorem documents the contract. -/
lemma resolveImplicit_complete (s : String) :
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
lemma resolveImplicit_null_precedence (s : String) (h : isNull s = true) :
    resolveImplicit s = .null := by
  unfold resolveImplicit; simp [h]

/-- Concrete: `resolveImplicit "null"` = `.null` (kernel-reducible). -/
lemma resolveImplicit_null : resolveImplicit "null" = .null := by rfl

/-- Concrete: `resolveImplicit "true"` = `.bool true` (kernel-reducible). -/
lemma resolveImplicit_true : resolveImplicit "true" = .bool true := by rfl

/-! ## §3 — `resolve` Structural Preservation -/

/-- Resolving a sequence preserves the collection shape (it's still a seq). -/
lemma resolve_sequence_is_seq (style : CollectionStyle) (items : Array YamlValue)
    (tag : Option String) (anchor : Option String) :
    (resolve (.sequence style items tag anchor)).isSeq = true := by
  rfl

/-- Resolving a mapping preserves the collection shape (it's still a map). -/
lemma resolve_mapping_is_map (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag : Option String) (anchor : Option String) :
    (resolve (.mapping style pairs tag anchor)).isMap = true := by
  rfl

/-- `resolveScalar` always returns a leaf type (not seq/map).
    Proven by case-splitting on the tag then on implicit branches. -/
lemma resolveScalar_not_seq (content : String) (tag? : Option String) :
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

lemma resolveScalar_not_map (content : String) (tag? : Option String) :
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

/-- `scalarType` always returns a leaf type: the tagged arm is `resolveScalar`,
    the untagged arm is `resolveImplicit` (= `resolveScalar _ none`) or `.str`. -/
lemma scalarType_not_seq (s : Scalar) : (scalarType s).isSeq = false := by
  unfold scalarType
  split
  · exact resolveScalar_not_seq _ _
  · split
    · have h := resolveScalar_not_seq s.content none
      simpa [resolveScalar] using h
    · rfl

lemma scalarType_not_map (s : Scalar) : (scalarType s).isMap = false := by
  unfold scalarType
  split
  · exact resolveScalar_not_map _ _
  · split
    · have h := resolveScalar_not_map s.content none
      simpa [resolveScalar] using h
    · rfl

/-- Resolving a scalar produces a leaf type (corollary of the above). -/
lemma resolve_scalar_is_leaf (s : Scalar) :
    (resolve (.scalar s)).isSeq = false ∧ (resolve (.scalar s)).isMap = false :=
  ⟨scalarType_not_seq s, scalarType_not_map s⟩

/-- Without a tag, a quoted or block scalar is a string whatever it spells (§10.3.2). -/
lemma scalarType_nonplain_str (s : Scalar) (ht : s.tag = none) (hp : s.style ≠ .plain) :
    scalarType s = .str s.content := by
  have h : (s.style == ScalarStyle.plain) = false := by
    cases hs : s.style <;> first | rfl | exact absurd hs hp
  unfold scalarType
  simp [ht, h]

/-- Without a tag, a plain scalar is implicitly resolved. -/
lemma scalarType_plain (s : Scalar) (ht : s.tag = none) (hp : s.style = .plain) :
    scalarType s = resolveImplicit s.content := by
  have h : (s.style == ScalarStyle.plain) = true := by rw [hp]; rfl
  unfold scalarType
  simp [ht, h]

/-! ## §4 — `resolveScalar` Explicit Tag Dispatch -/

/-- Explicit `!!str` tag always produces `.str`, regardless of content. -/
lemma resolveScalar_str_tag (content : String) :
    resolveScalar content (some "tag:yaml.org,2002:str") = .str content := by
  simp [resolveScalar]

/-- Explicit `!!null` tag always produces `.null`, regardless of content. -/
lemma resolveScalar_null_tag (content : String) :
    resolveScalar content (some "tag:yaml.org,2002:null") = .null := by
  simp [resolveScalar]

/-- No tag delegates to `resolveImplicit`. -/
lemma resolveScalar_no_tag (content : String) :
    resolveScalar content none = resolveImplicit content := by
  simp [resolveScalar]

/-! ## §5 — `#guard` Compile-Time Schema Resolution Checks

`YamlType` does not derive `DecidableEq` (due to `Float`), so concrete
resolution correctness is verified via `#guard` (which uses `BEq`) rather
than `native_decide` (which requires `Decidable`).

Moved to `Tests/Guards/Proofs/SchemaResolution.lean`.
-/


end L4YAML.Proofs.SchemaResolution

end Blanket
