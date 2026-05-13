/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import L4YAML.Schema.Schema
import L4YAML.Schema.FromToYaml

/-! # Schema Algebra  (Algebra Items 15 + 16)

This file names the equational laws of Core-Schema resolution
(`resolveImplicit` / `resolveScalar` / `resolve`) and states the
typeclass law for `ToYaml` / `FromYaml` round-tripping.

## Item 16 — Schema resolution determinism

`resolveImplicit`, `resolveScalar`, and `resolve` are total Lean
functions, hence deterministic by construction: the function arrow
is the determinism statement. The interesting content is the
**precedence**: Core-Schema implicit resolution tries
`null → bool → int → float → str` in that order, and `resolveScalar`
adds tag-precedence over implicit resolution.

We expose the precedence as five elimination-style lemmas — one per
arm of the `if let` chain. Downstream proofs `rfl`-rewrite a
specific `isNull` / `isBool` / `isInt` / `isFloat` hypothesis into
the matching `resolveImplicit` form rather than re-unfolding the
match by hand.

## Item 15 — ToYaml / FromYaml round-trip law

The Phase 2 statement of Item 15 is the `LawfulRoundTrip` typeclass
itself. Per **D2** (resolved during Phase 1, see Blueprint 08), the
round-trip law is carried as a *separate* typeclass rather than
folded into `ToYaml` or `FromYaml` — the typeclasses describe
conversion, the law describes correctness of an instance pair.

Per-instance discharges (e.g. `LawfulRoundTrip Int`) are Phase 5's
deliverable, not Phase 2's. Phase 2 only states the law and the
single structural bridge that every `[FromYamlType α]` instance
factors through (`fromYaml? = fromYamlType? ∘ resolve`).

## Closure (Guardrail 2)

This file introduces no new algebra beyond Items 15 and 16. The
`LawfulRoundTrip` typeclass is the **statement** of Item 15; no
instance is provided here. The resolution-precedence lemmas are
direct unfoldings of the existing definitions in
`L4YAML/Schema/Schema.lean`.

## Provenance

New content. The functions `resolveImplicit` / `resolveScalar` /
`resolve` are defined in `L4YAML/Schema/Schema.lean:245–305`; the
`ToYaml` / `FromYaml` / `FromYamlType` typeclasses and the bridge
instance live in `L4YAML/Schema/FromToYaml.lean:42–64`. This file
consumes both namespaces and adds only equational content.
-/

set_option autoImplicit false

namespace L4YAML.Algebra.Schema

open L4YAML.Schema

universe u

/-! ## Item 16(a) — `resolveImplicit` precedence

Five elimination lemmas, one per arm of the resolution chain.
Each lemma states: *given the hypotheses that excluded all earlier
arms, the value of `resolveImplicit` is determined by the matched
arm*. Together they characterise `resolveImplicit` completely.
-/

/-- **Null arm**: a string the `isNull` predicate accepts resolves to `.null`. -/
theorem resolveImplicit_of_isNull {s : String} (h : isNull s = true) :
    resolveImplicit s = .null := by
  unfold resolveImplicit
  rw [h]; rfl

/-- **Bool arm**: when `isNull` fails and `isBool` produces `some b`,
    `resolveImplicit` produces `.bool b`. -/
theorem resolveImplicit_of_isBool {s : String} {b : Bool}
    (h_null : isNull s = false) (h_bool : isBool s = some b) :
    resolveImplicit s = .bool b := by
  unfold resolveImplicit
  rw [h_null]
  simp only [Bool.false_eq_true, if_false, h_bool]

/-- **Int arm**: when `isNull` and `isBool` both fail and `isInt`
    produces `some i`, `resolveImplicit` produces `.int i`. -/
theorem resolveImplicit_of_isInt {s : String} {i : Int}
    (h_null : isNull s = false) (h_bool : isBool s = none)
    (h_int : isInt s = some i) :
    resolveImplicit s = .int i := by
  unfold resolveImplicit
  rw [h_null]
  simp only [Bool.false_eq_true, if_false, h_bool, h_int]

/-- **Float arm**: when `isNull`/`isBool`/`isInt` all fail and
    `isFloat` produces `some f`, `resolveImplicit` produces `.float f`. -/
theorem resolveImplicit_of_isFloat {s : String} {f : FloatValue}
    (h_null : isNull s = false) (h_bool : isBool s = none)
    (h_int : isInt s = none) (h_float : isFloat s = some f) :
    resolveImplicit s = .float f := by
  unfold resolveImplicit
  rw [h_null]
  simp only [Bool.false_eq_true, if_false, h_bool, h_int, h_float]

/-- **Str fallback**: when every classifier fails, `resolveImplicit`
    falls through to `.str s`. -/
theorem resolveImplicit_str {s : String}
    (h_null : isNull s = false) (h_bool : isBool s = none)
    (h_int : isInt s = none) (h_float : isFloat s = none) :
    resolveImplicit s = .str s := by
  unfold resolveImplicit
  rw [h_null]
  simp only [Bool.false_eq_true, if_false, h_bool, h_int, h_float]

/-! ## Item 16(b) — `resolveScalar` tag precedence

`resolveScalar` is a deterministic case-split on the optional tag.
The two non-trivial behaviours are: explicit tags `null`/`str`
short-circuit (they never look at the content); explicit
`bool`/`int`/`float` parse the content with the classifier and
fall back to `.str content` on failure. An absent tag delegates to
`resolveImplicit`.

The lemmas are stated as `rfl` where the right-hand side is a
literal datatype constructor, and as `simp`-driven unfoldings
otherwise.
-/

/-- **Explicit null tag**: short-circuits to `.null` independent of content. -/
@[simp] theorem resolveScalar_tag_null (content : String) :
    resolveScalar content (some "tag:yaml.org,2002:null") = .null := rfl

/-- **Explicit str tag**: short-circuits to `.str content`. -/
@[simp] theorem resolveScalar_tag_str (content : String) :
    resolveScalar content (some "tag:yaml.org,2002:str") = .str content := rfl

/-- **Explicit bool tag with parseable content**. -/
theorem resolveScalar_tag_bool_some {content : String} {b : Bool}
    (h : isBool content = some b) :
    resolveScalar content (some "tag:yaml.org,2002:bool") = .bool b := by
  show (match isBool content with | some b => YamlType.bool b | none => YamlType.str content) = .bool b
  rw [h]

/-- **Explicit bool tag with unparseable content** falls back to `.str`. -/
theorem resolveScalar_tag_bool_none {content : String}
    (h : isBool content = none) :
    resolveScalar content (some "tag:yaml.org,2002:bool") = .str content := by
  show (match isBool content with | some b => YamlType.bool b | none => YamlType.str content) = .str content
  rw [h]

/-- **Explicit int tag with parseable content**. -/
theorem resolveScalar_tag_int_some {content : String} {i : Int}
    (h : isInt content = some i) :
    resolveScalar content (some "tag:yaml.org,2002:int") = .int i := by
  show (match isInt content with | some i => YamlType.int i | none => YamlType.str content) = .int i
  rw [h]

/-- **Explicit int tag with unparseable content** falls back to `.str`. -/
theorem resolveScalar_tag_int_none {content : String}
    (h : isInt content = none) :
    resolveScalar content (some "tag:yaml.org,2002:int") = .str content := by
  show (match isInt content with | some i => YamlType.int i | none => YamlType.str content) = .str content
  rw [h]

/-- **Explicit float tag with parseable content**. -/
theorem resolveScalar_tag_float_some {content : String} {f : FloatValue}
    (h : isFloat content = some f) :
    resolveScalar content (some "tag:yaml.org,2002:float") = .float f := by
  show (match isFloat content with | some f => YamlType.float f | none => YamlType.str content) = .float f
  rw [h]

/-- **Explicit float tag with unparseable content** falls back to `.str`. -/
theorem resolveScalar_tag_float_none {content : String}
    (h : isFloat content = none) :
    resolveScalar content (some "tag:yaml.org,2002:float") = .str content := by
  show (match isFloat content with | some f => YamlType.float f | none => YamlType.str content) = .str content
  rw [h]

/-- **No tag**: delegate to implicit resolution. -/
@[simp] theorem resolveScalar_none (content : String) :
    resolveScalar content none = resolveImplicit content := rfl

/-! ## Item 16(c) — `resolve` constructor unfoldings

`resolve` is structural recursion on `YamlValue`. The four
unfoldings below state the value of `resolve` on each constructor.
They are `rfl` and tagged `@[simp]` so downstream proofs that walk
a `YamlValue` rewrite-by-constructor without the `unfold resolve`
overhead.

The `sequence` / `mapping` cases recurse via the auxiliary
`resolveList` / `resolvePairs`, which themselves admit the
standard `nil` / `cons` unfoldings shown below.
-/

@[simp] theorem resolve_scalar (s : Scalar) :
    resolve (.scalar s) = resolveScalar s.content s.tag := rfl

@[simp] theorem resolve_alias (name : String) :
    resolve (.alias name) = .null := rfl

@[simp] theorem resolveList_nil :
    resolve.resolveList [] = [] := rfl

@[simp] theorem resolveList_cons (v : YamlValue) (vs : List YamlValue) :
    resolve.resolveList (v :: vs) = resolve v :: resolve.resolveList vs := rfl

@[simp] theorem resolvePairs_nil :
    resolve.resolvePairs [] = [] := rfl

@[simp] theorem resolvePairs_cons (k v : YamlValue) (rest : List (YamlValue × YamlValue)) :
    resolve.resolvePairs ((k, v) :: rest)
      = (resolve k, resolve v) :: resolve.resolvePairs rest := rfl

/-! ## Item 15 — `LawfulRoundTrip` typeclass

The round-trip law `fromYaml? ∘ toYaml = .ok` is carried by a
**separate typeclass** rather than folded into `ToYaml` / `FromYaml`
(per **D2**, Blueprint 08 §What this document settles).

Stating the law as its own class:
- Lets `ToYaml` / `FromYaml` instances be written without proof
  obligation — useful for partial / not-yet-verified types.
- Gives Phase 5's derivation generator a clear target: produce a
  pair of instances **plus** a `LawfulRoundTrip` instance.
- Avoids polluting downstream `[ToYaml α]` constraints with the
  law in contexts that don't need it.

No instances are provided here. Phase 5's `FromToYaml` cutover
discharges them per instance starting from `Int`.
-/

/-- The round-trip law: serialising a value and parsing it back
    yields the original value via the `Except` happy path.

    Phase 5 deliverable: prove `LawfulRoundTrip α` for every
    primitive instance in `Schema/FromToYaml.lean` and extend the
    derivation generator (`Schema/Deriving.lean`) to produce this
    instance alongside `ToYaml` / `FromYaml`. -/
class LawfulRoundTrip (α : Type u) [ToYaml α] [FromYaml α] : Prop where
  /-- `fromYaml? (toYaml a) = .ok a` for every `a : α`. -/
  fromYaml_toYaml : ∀ (a : α), fromYaml? (toYaml a) = .ok a

/-! ## Item 15 — Bridge: `fromYaml?` factors through `resolve`

The default `FromYaml` instance for any `FromYamlType` factors
through schema resolution. This is the **structural reason** the
Phase 5 per-instance round-trip proofs all share the same shape:
each one reduces to `fromYamlType? (resolve (toYaml a)) = .ok a`.
-/

/-- **Bridge**: the default `FromYaml` instance is `fromYamlType?`
    composed with `resolve`. This is the structural decomposition
    that every Phase 5 per-instance round-trip proof rewrites with
    on its first step. -/
theorem fromYaml_via_resolve {α : Type u} [FromYamlType α] (v : YamlValue) :
    @fromYaml? α (instFromYamlOfFromYamlType) v = fromYamlType? (resolve v) := rfl

end L4YAML.Algebra.Schema
