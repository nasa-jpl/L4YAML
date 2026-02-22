/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML Value Types

Core AST types for representing YAML documents.

These types are intentionally identical to `LeanYaml.YamlValue` from lean4-yaml,
enabling the Schema/FromToYaml/Deriving/Emitter layers to be shared between
the original (unverified) and verified parser implementations.
-/

namespace Lean4Yaml

/-! ## Scalar Styles -/

/--
The five scalar styles defined in YAML 1.2.2
§7 (https://yaml.org/spec/1.2.2/#chapter-7-flow-style-productions) and
§8 (https://yaml.org/spec/1.2.2/#chapter-8-block-style-productions).

- **Plain**: Unquoted scalars determined by context
- **Single-quoted**: Literal strings with `''` escape only
- **Double-quoted**: Strings with full escape sequence support
- **Literal**: Block scalar preserving line breaks (`|`)
- **Folded**: Block scalar folding line breaks to spaces (`>`)
-/
inductive ScalarStyle where
  | plain
  | singleQuoted
  | doubleQuoted
  | literal
  | folded
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/--
A YAML scalar with style information.

We preserve style to support round-trip serialization.
The `tag` field supports explicit typing (e.g., `!!str`, `!!int`).
-/
structure Scalar where
  content : String
  style : ScalarStyle
  tag : Option String := none
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Collection Styles -/

/--
Block vs flow style for collections.

- **Block**: Indentation-based (`- item` or `key: value`)
- **Flow**: Bracketed JSON-like (`[item]` or `{key: value}`)
-/
inductive CollectionStyle where
  | block
  | flow
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/-! ## Core YAML Values -/

/--
Core YAML value types.

YAML 1.2.2 §3.2.1 (https://yaml.org/spec/1.2.2/#3211-nodes) defines three node kinds:
- **Scalar**: Opaque data (strings, numbers, booleans, null, etc.)
- **Sequence**: Ordered collection of nodes
- **Mapping**: Collection of key-value pairs

Each node can carry an optional tag for explicit type annotation.
-/
inductive YamlValue where
  | scalar (s : Scalar)
  | sequence (style : CollectionStyle) (items : Array YamlValue) (tag : Option String := none)
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue)) (tag : Option String := none)
  deriving Repr, BEq, Inhabited

/-! ## Directives -/

/-- YAML directives: `%YAML 1.2` and `%TAG !handle! prefix` -/
inductive Directive where
  | yaml (version : String)
  | tag (handle : String) (tagPrefix : String)
  deriving Repr, BEq, DecidableEq

/-! ## Documents -/

/--
A YAML document with optional directives.

YAML streams can contain multiple documents separated by `---` markers.
-/
structure YamlDocument where
  value : YamlValue
  directives : Array Directive := #[]
  deriving Repr, BEq

/-! ## Convenience Constructors -/

/-- Create a plain scalar value -/
def YamlValue.plainScalar (content : String) : YamlValue :=
  .scalar { content, style := .plain }

/-- Create a quoted scalar value -/
def YamlValue.quotedScalar (content : String) (style : ScalarStyle := .doubleQuoted) : YamlValue :=
  .scalar { content, style }

/-- Create a flow sequence -/
def YamlValue.flowSequence (items : Array YamlValue) : YamlValue :=
  .sequence .flow items

/-- Create a block sequence -/
def YamlValue.blockSequence (items : Array YamlValue) : YamlValue :=
  .sequence .block items

/-- Create a flow mapping -/
def YamlValue.flowMapping (pairs : Array (YamlValue × YamlValue)) : YamlValue :=
  .mapping .flow pairs

/-- Create a block mapping -/
def YamlValue.blockMapping (pairs : Array (YamlValue × YamlValue)) : YamlValue :=
  .mapping .block pairs

/-- Create the null value -/
def YamlValue.null : YamlValue :=
  .scalar { content := "", style := .plain, tag := some "!!null" }

/-! ## Value Inspection -/

/-- Check if a value is a scalar -/
def YamlValue.isScalar : YamlValue → Bool
  | .scalar _ => true
  | _ => false

/-- Check if a value is a sequence -/
def YamlValue.isSequence : YamlValue → Bool
  | .sequence .. => true
  | _ => false

/-- Check if a value is a mapping -/
def YamlValue.isMapping : YamlValue → Bool
  | .mapping .. => true
  | _ => false

/-- Extract scalar content if value is a scalar -/
def YamlValue.asString? : YamlValue → Option String
  | .scalar s => some s.content
  | _ => none

/-- Extract sequence items if value is a sequence -/
def YamlValue.asArray? : YamlValue → Option (Array YamlValue)
  | .sequence _ items _ => some items
  | _ => none

/-- Extract mapping pairs if value is a mapping -/
def YamlValue.asPairs? : YamlValue → Option (Array (YamlValue × YamlValue))
  | .mapping _ pairs _ => some pairs
  | _ => none

/--
Apply a tag to any YAML value.

Sets the `tag` field on scalars, sequences, and mappings.
Used by the tag parser to annotate parsed values.
-/
def YamlValue.withTag (v : YamlValue) (tag : String) : YamlValue :=
  match v with
  | .scalar s => .scalar { s with tag := some tag }
  | .sequence style items _ => .sequence style items (some tag)
  | .mapping style pairs _ => .mapping style pairs (some tag)

/-- Look up a key in a mapping by string content -/
def YamlValue.lookup? (v : YamlValue) (key : String) : Option YamlValue :=
  match v with
  | .mapping _ pairs _ =>
    pairs.findSome? fun (k, v) =>
      match k with
      | .scalar s => if s.content == key then some v else none
      | _ => none
  | _ => none

/-! ## Anchor Map

An association-list map from anchor names to their resolved `YamlValue`s.
Represented as `Array (String × YamlValue)` for proof-friendliness —
all operations reduce to well-supported `Array` combinators (`filter`,
`push`, `findSome?`).

### Algebraic contracts (Layer 2 proof targets)

1. **Get-after-set** (`find?_insert`): `(m.insert k v).find? k = some v`
2. **Non-interference** (`find?_insert_ne`): `k ≠ k' → (m.insert k v).find? k' = m.find? k'`
3. **Empty** (`find?_empty`): `empty.find? k = none`

These three laws fully specify the map's observable behaviour and are
sufficient for composing with alias-resolution proofs: an alias `*name`
succeeds iff some prior `&name value` executed `insert`, and the value
returned equals the stored one.
-/

/-- Anchor map: associates anchor names with their resolved values.
    `abbrev` so `Array` methods (`filter`, `push`, `findSome?`) resolve
    without manual coercion, keeping both code and proofs short. -/
abbrev AnchorMap := Array (String × YamlValue)

namespace AnchorMap

/-- The empty anchor map. -/
def empty : AnchorMap := #[]

/-- Insert or replace a binding.
    Removes any prior binding for `name`, then appends `(name, val)`,
    maintaining the unique-key invariant. -/
def insert (m : AnchorMap) (name : String) (val : YamlValue) : AnchorMap :=
  (m.filter (fun (n, _) => n != name)).push (name, val)

/-- Look up an anchor by name.
    Returns the value if the anchor is defined, `none` otherwise. -/
def find? (m : AnchorMap) (name : String) : Option YamlValue :=
  m.findSome? (fun (n, v) => if n == name then some v else none)

/-! ### Algebraic Laws

These theorem statements document the essential contracts that
verification proofs will use. They are the specification of
`AnchorMap` — any correct implementation must satisfy them.
-/

/-- Auxiliary: filtering by `n != name` preserves `findSome?` for `name' ≠ name`.
    Elements removed by the filter have `n = name ≠ name'`, so `f` returns
    `none` for them and the `findSome?` result is unchanged. -/
private theorem list_findSome?_filter_preserves
    (xs : List (String × YamlValue)) (name name' : String)
    (hne : name ≠ name') :
    List.findSome? (fun (n, v) => if n == name' then some v else none)
      (xs.filter (fun (n, _) => n != name))
    = List.findSome? (fun (n, v) => if n == name' then some v else none) xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    obtain ⟨n, v⟩ := x
    simp only [List.filter_cons]
    split
    · -- filter keeps element: (n != name) = true
      simp only [List.findSome?_cons]
      split
      · rfl
      · exact ih
    · -- filter drops element: n = name
      next hdrop =>
      have hEqName : n = name := by
        simp only [bne_iff_ne, ne_eq, Decidable.not_not] at hdrop; exact hdrop
      have hNe : (n == name') = false := by
        rw [hEqName]; exact beq_eq_false_iff_ne.mpr hne
      simp only [List.findSome?_cons, hNe, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- **Get-after-set**: looking up a just-inserted key returns the inserted value. -/
theorem find?_insert (m : AnchorMap) (name : String) (val : YamlValue) :
    AnchorMap.find? (AnchorMap.insert m name val) name = some val := by
  simp only [AnchorMap.find?, AnchorMap.insert]
  rw [Array.findSome?_push]
  simp only [beq_self_eq_true, ↓reduceIte]
  -- Show filter part = none, then none.or (some val) = some val
  suffices h : Array.findSome? _ (Array.filter _ m) = none by
    rw [h, Option.none_or]
  rw [← Array.findSome?_toList, Array.toList_filter, List.findSome?_eq_none_iff]
  intro ⟨n, v⟩ hmem
  have hfilt := (List.mem_filter.mp hmem).2
  simp only [bne_iff_ne, ne_eq, beq_iff_eq] at hfilt ⊢
  exact if_neg hfilt

/-- **Non-interference**: inserting under `k` does not affect lookups for `k' ≠ k`. -/
theorem find?_insert_ne (m : AnchorMap) (name name' : String) (val : YamlValue)
    (h : name ≠ name') :
    AnchorMap.find? (AnchorMap.insert m name val) name' = AnchorMap.find? m name' := by
  simp only [AnchorMap.find?, AnchorMap.insert]
  rw [Array.findSome?_push]
  -- The pushed element (name, val) doesn't match name'
  have hpush : (fun (n, v) => if n == name' then some v else none) (name, val) = none := by
    simp [beq_eq_false_iff_ne.mpr h]
  simp only [hpush, Option.or_none]
  -- Filtering by n != name preserves findSome? for name' ≠ name
  rw [← Array.findSome?_toList, Array.toList_filter, ← Array.findSome?_toList]
  exact list_findSome?_filter_preserves m.toList name name' h

/-- **Empty**: no key is found in an empty map. -/
theorem find?_empty (name : String) :
    AnchorMap.find? AnchorMap.empty name = none := by
  rfl

end AnchorMap

end Lean4Yaml
