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

/-! ## Chomp Style -/

/--
Chomping behavior for block scalars.

**YAML 1.2.2**: [160] c-chomping-indicator(t)
(§8.1.1.2, https://yaml.org/spec/1.2.2/#8112-block-chomping-indicator)

- **Strip** (`-`): remove all trailing newlines
- **Clip** (default): keep one trailing newline
- **Keep** (`+`): keep all trailing newlines

Canonical definition — imported by both `Grammar.lean` and `Parser/Scalar.lean`.
-/
inductive ChompStyle where
  | strip
  | clip
  | keep
  deriving Repr, BEq, Hashable, Inhabited, DecidableEq

/--
Block scalar header metadata, preserved for round-trip serialization.

Stores the chomping indicator and optional explicit indentation level
from the block scalar header (`|2-`, `>+`, etc.).
Only meaningful when `ScalarStyle` is `.literal` or `.folded`.
-/
structure BlockScalarMeta where
  /-- Chomping behavior: strip, clip (default), or keep -/
  chomp : ChompStyle := .clip
  /-- Explicit indentation indicator (`1`–`9`), or `none` for auto-detect -/
  explicitIndent : Option Nat := none
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Comments -/

/--
Relative position of a comment with respect to its associated node.

Used for round-trip preservation — the serializer emits comments
at the same relative position where they were parsed.
-/
inductive CommentPosition where
  /-- Comment on a line before the node -/
  | before
  /-- Comment at the end of the same line as the node -/
  | inline
  /-- Comment on a line after the node -/
  | after
  deriving Repr, BEq, Inhabited, DecidableEq

/--
A YAML comment captured during parsing.

YAML 1.2.2 §6.6 / §3.2.3.3: comments are presentation details with
no effect on the serialization tree. We preserve them for round-trip
fidelity: `parse → serialize` can reconstruct comments at their
original positions.
-/
structure Comment where
  /-- The comment text (excluding the leading `#` and any whitespace) -/
  text : String
  /-- Where the comment appeared relative to the associated node -/
  position : CommentPosition
  deriving Repr, BEq, Inhabited, DecidableEq

/-! ## Stream Position

Position in a YAML stream, used by the tokenized parser pipeline.
Relocated from `Stream.lean` during P10.6 (old parser deletion) so that
position tracking survives without the lean4-parser dependency.
-/

/--
Position in a YAML stream.

Tracks byte offset (for efficient save/restore), line number, and column number.
Line and column are 0-based to match YAML spec conventions.
-/
structure YamlPos where
  /-- Byte offset into the source string -/
  offset : Nat
  /-- Current line number (0-based) -/
  line : Nat
  /-- Current column number (0-based) -/
  col : Nat
  deriving Repr, BEq, Inhabited, Hashable, DecidableEq

instance : Ord YamlPos where
  compare a b := compare a.offset b.offset

instance : LT YamlPos where
  lt a b := a.offset < b.offset

instance : LE YamlPos where
  le a b := a.offset ≤ b.offset

/--
A YAML scalar with style information.

We preserve style to support round-trip serialization.
The `tag` field supports explicit typing (e.g., `!!str`, `!!int`).
The `anchor` field preserves the anchor name (`&name`) for round-trip.
The `blockMeta` field preserves chomp/indent for literal/folded scalars.
-/
structure Scalar where
  content : String
  style : ScalarStyle
  tag : Option String := none
  anchor : Option String := none
  blockMeta : Option BlockScalarMeta := none
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
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String := none) (anchor : Option String := none)
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String := none) (anchor : Option String := none)
  | alias (name : String)
  deriving Repr, BEq, Inhabited

/-! ## Directives -/

/-- YAML directives: `%YAML 1.2` and `%TAG !handle! prefix` -/
inductive Directive where
  | yaml (version : String)
  | tag (handle : String) (tagPrefix : String)
  deriving Repr, BEq, DecidableEq

/-! ## YamlPath — Tree-addressed value navigation (Phase G5b)

A path from the document root to a node in the value tree,
analogous to jq/yq selectors: `.servers[0].port` ≈
`#[.key "servers", .index 0, .key "port"]`.
-/

/-- A single step in a path through a YAML value tree. -/
inductive PathSegment where
  /-- Index into a sequence: `.[i]` -/
  | index (i : Nat)
  /-- Key lookup in a mapping: `.key` -/
  | key (k : String)
  deriving Repr, BEq, DecidableEq, Inhabited

/-- A path from the document root to a node in the value tree. -/
abbrev YamlPath := Array PathSegment

/-! ## Documents -/

/--
A YAML document with optional directives and anchor map.

YAML streams can contain multiple documents separated by `---` markers.

The `anchors` field captures the document's anchor map from the parse phase.
This enables the **Compose** step (YAML 1.2.2 §3.1) to resolve alias nodes.
-/
structure YamlDocument where
  value : YamlValue
  directives : Array Directive := #[]
  anchors : Array (String × YamlValue) := #[]
  /-- Comments collected during scanning (side-channel, §6.6).
      Each entry pairs the source position of the `#` with the comment struct. -/
  comments : Array (YamlPos × Comment) := #[]
  /-- Source span of each node, keyed by path from root (G5c).
      Each entry is `(path, startPos, endPos)` where the positions
      delimit the node's token span in the source. -/
  nodePositions : Array (YamlPath × YamlPos × YamlPos) := #[]
  deriving Repr, BEq, Inhabited

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

/-- Check if a value is an alias -/
def YamlValue.isAlias : YamlValue → Bool
  | .alias _ => true
  | _ => false

/-- Extract scalar content if value is a scalar -/
def YamlValue.asString? : YamlValue → Option String
  | .scalar s => some s.content
  | _ => none

/-- Extract sequence items if value is a sequence -/
def YamlValue.asArray? : YamlValue → Option (Array YamlValue)
  | .sequence _ items .. => some items
  | _ => none

/-- Extract mapping pairs if value is a mapping -/
def YamlValue.asPairs? : YamlValue → Option (Array (YamlValue × YamlValue))
  | .mapping _ pairs .. => some pairs
  | _ => none

/--
Apply a tag to any YAML value.

Sets the `tag` field on scalars, sequences, and mappings.
Used by the tag parser to annotate parsed values.
-/
def YamlValue.withTag (v : YamlValue) (tag : String) : YamlValue :=
  match v with
  | .scalar s => .scalar { s with tag := some tag }
  | .sequence style items _ anchor => .sequence style items (some tag) anchor
  | .mapping style pairs _ anchor => .mapping style pairs (some tag) anchor
  | .alias name => .alias name  -- aliases refer to anchored node; tag is on that node

/--
Attach an anchor name to any YAML value.

Sets the `anchor` field on scalars, sequences, and mappings.
Used by the parser to preserve `&name` annotations for round-trip.
-/
def YamlValue.withAnchor (v : YamlValue) (name : String) : YamlValue :=
  match v with
  | .scalar s => .scalar { s with anchor := some name }
  | .sequence style items tag _ => .sequence style items tag (some name)
  | .mapping style pairs tag _ => .mapping style pairs tag (some name)
  | .alias n => .alias n  -- aliases don't carry their own anchor

/-- Look up a key in a mapping by string content -/
def YamlValue.lookup? (v : YamlValue) (key : String) : Option YamlValue :=
  match v with
  | .mapping _ pairs .. =>
    pairs.findSome? fun (k, v) =>
      match k with
      | .scalar s => if s.content == key then some v else none
      | _ => none
  | _ => none

/--
Resolve a path against a value tree, returning the addressed sub-value.

Structural recursion on the path segment list. `.index i` indexes into
sequence items, `.key k` looks up in mapping pairs by scalar content.
Returns `none` for type mismatches, out-of-bounds, or unresolvable aliases.
-/
def YamlValue.resolve (v : YamlValue) (path : YamlPath) : Option YamlValue :=
  go v path.toList
where
  go : YamlValue → List PathSegment → Option YamlValue
    | v, [] => some v
    | .sequence _ items .., .index i :: rest =>
      match items[i]? with
      | some child => go child rest
      | none => none
    | .mapping _ pairs .., .key k :: rest =>
      match pairs.findSome? (fun (key, val) =>
        match key with
        | .scalar s => if s.content == k then some val else none
        | _ => none) with
      | some child => go child rest
      | none => none
    | _, _ :: _ => none

/--
Resolve all alias nodes by substituting the anchored value.

Walks the tree, replacing each `.alias name` with the corresponding
value from the anchor map. Unresolved aliases are left as-is.
-/
def YamlValue.resolveAliases (v : YamlValue) (anchors : Array (String × YamlValue)) : YamlValue :=
  match v with
  | .scalar _ => v
  | .sequence style items tag anchor =>
    .sequence style (resolveList items.toList anchors).toArray tag anchor
  | .mapping style pairs tag anchor =>
    .mapping style (resolvePairs pairs.toList anchors).toArray tag anchor
  | .alias name =>
    match anchors.findSome? (fun (n, val) => if n == name then some val else none) with
    | some val => val
    | none => v  -- unresolved alias: preserve as-is
where
  /-- Resolve aliases in a list of values. -/
  resolveList : List YamlValue → Array (String × YamlValue) → List YamlValue
    | [], _ => []
    | v :: vs, anchors => v.resolveAliases anchors :: resolveList vs anchors
  /-- Resolve aliases in a list of key-value pairs. -/
  resolvePairs : List (YamlValue × YamlValue) → Array (String × YamlValue)
      → List (YamlValue × YamlValue)
    | [], _ => []
    | (k, v) :: rest, anchors =>
      (k.resolveAliases anchors, v.resolveAliases anchors) :: resolvePairs rest anchors

/--
Strip all anchor annotations from a `YamlValue` tree.

Clears the `anchor` field on scalars, sequences, and mappings.
Alias nodes are left unchanged (they have no anchor field).

This converts serialization-level anchor metadata into the clean
representation graph form expected by YAML 1.2.2 §3.1.
-/
def YamlValue.stripAnchors (v : YamlValue) : YamlValue :=
  match v with
  | .scalar s => .scalar { s with anchor := none }
  | .sequence style items tag _ =>
    .sequence style (stripList items.toList).toArray tag none
  | .mapping style pairs tag _ =>
    .mapping style (stripPairs pairs.toList).toArray tag none
  | .alias _ => v
where
  /-- Strip anchors in a list of values. -/
  stripList : List YamlValue → List YamlValue
    | [] => []
    | v :: vs => v.stripAnchors :: stripList vs
  /-- Strip anchors in a list of key-value pairs. -/
  stripPairs : List (YamlValue × YamlValue) → List (YamlValue × YamlValue)
    | [] => []
    | (k, v) :: rest =>
      (k.stripAnchors, v.stripAnchors) :: stripPairs rest

/--
**Compose**: resolve aliases and strip anchor annotations.

This is the "Compose" step from YAML 1.2.2 §3.1
(https://yaml.org/spec/1.2.2/#31-processes).

Takes a serialization tree (with `.alias` nodes and `anchor` fields)
and produces a representation graph (all aliases resolved, no anchors).

The `anchors` parameter is the document's anchor map, captured during
the Parse phase.
-/
def YamlDocument.compose (doc : YamlDocument) : YamlDocument :=
  { doc with
    value := (doc.value.resolveAliases doc.anchors).stripAnchors
    anchors := #[] }

/-- Strip all comments from a document (§6.6: comments are presentation detail). -/
def YamlDocument.stripComments (doc : YamlDocument) : YamlDocument :=
  { doc with comments := #[] }

/-- Strip node positions (presentation detail, like comments). -/
def YamlDocument.stripPositions (doc : YamlDocument) : YamlDocument :=
  { doc with nodePositions := #[] }

/-- Find all comments whose source position falls within the span of
    the node at `path`. Returns an empty array if the path is not in
    the position map. -/
def YamlDocument.commentsFor (doc : YamlDocument) (path : YamlPath) : Array Comment :=
  match doc.nodePositions.find? (fun (p, _, _) => p == path) with
  | some (_, startPos, endPos) =>
    doc.comments.filterMap fun (pos, c) =>
      if startPos.offset ≤ pos.offset && pos.offset ≤ endPos.offset then some c else none
  | none => #[]

/-- Extract all comment text strings from a document, ignoring positions.
    Useful for position-independent comment round-trip comparisons. -/
def YamlDocument.commentTexts (doc : YamlDocument) : Array String :=
  doc.comments.map fun (_, c) => c.text

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
theorem list_findSome?_filter_preserves
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
