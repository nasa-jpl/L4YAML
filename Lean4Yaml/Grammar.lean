/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Token
import Lean4Yaml.YamlSpec
import Lean4Yaml.CharPredicates

/-!
# Formal YAML Grammar

Inductive propositions characterizing valid YAML documents.

This module defines what it means for a string to be valid YAML, independent
of any parser implementation. It serves as the **specification** against which
the parser's correctness is proven.

## Approach

We define the grammar in layers matching the YAML 1.2.2 spec structure:

1. **Character classifications** (§5: https://yaml.org/spec/1.2.2/#chapter-5-character-productions)
2. **Indentation** (§6.1: https://yaml.org/spec/1.2.2/#61-indentation-spaces)
3. **Scalars** (§7.3: https://yaml.org/spec/1.2.2/#73-flow-scalar-styles)
4. **Collections** (§7.4: https://yaml.org/spec/1.2.2/#74-flow-collection-styles, §8: https://yaml.org/spec/1.2.2/#chapter-8-block-style-productions)
5. **Documents** (§9: https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)

Each layer builds on the previous, and the final `ValidYaml` proposition
ties everything together.

## Design Decisions

- We specify the **supported subset** of YAML 1.2.2, not the full spec.
  The spec itself is ~120 grammar productions; we start with the most
  commonly used features and extend incrementally.

- Grammar rules reference YAML 1.2.2 section numbers with URLs for traceability.

- We use `Prop` (not `Bool`) to allow for non-computable specifications
  where needed, while keeping `Decidable` instances where possible for
  `native_decide` proofs.
-/

namespace Lean4Yaml.Grammar

open Lean4Yaml.CharPredicates

-- Re-export CharPredicates names so that `open Grammar` makes them available
export Lean4Yaml.CharPredicates (
  isPrintableProp isPrintableBool isPrintable_iff
  isLineBreakProp isLineBreakBool isLineBreak_iff
  isWhiteSpaceProp isWhiteSpaceBool isWhiteSpace_iff
  isFlowIndicatorProp isFlowIndicatorBool isFlowIndicator_iff
  isIndicatorProp isIndicatorBool isIndicator_iff
  isIndentCharProp isIndentCharBool isIndentChar_iff
  isBlankProp isBlankBool isBlank_iff
  canStartPlainScalarProp canStartPlainScalarBool canStartPlainScalar_iff
  isPlainSafeProp isPlainSafeBool isPlainSafe_iff
  validPlainFirstProp validPlainFirstBool validPlainFirst_iff
  noColonSpaceProp noColonSpaceBool noColonSpace_iff
  noSpaceHashProp noSpaceHashBool noSpaceHash_iff
  noFlowIndicatorsProp noFlowIndicatorsBool noFlowIndicators_iff
  hasAdjacentChars hasAdjacentChars_iff
  not_bool_iff_not
)

/-! ## Character Classifications

Character predicates (`isPrintableProp`, `isLineBreakProp`, `isWhiteSpaceProp`,
`isFlowIndicatorProp`, `isIndentCharProp`, etc.) are defined in
`CharPredicates.lean` and re-exported above.
-/

-- NOTE: The old 1-argument `canStartPlainScalar` has been removed.
-- Use `canStartPlainScalarProp` (3-arg) from CharPredicates.lean instead.

/-! ## Indentation (YAML 1.2.2 §6.1: https://yaml.org/spec/1.2.2/#61-indentation-spaces) -/

/--
An indentation of `n` spaces at the start of a line.

**YAML 1.2.2**: [63] s-indent(n) (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)

This is the core proposition for block-style YAML. A line is indented
at level `n` if it starts with exactly `n` space characters.
-/
@[yaml_spec "6.1" 63 "s-indent(n)"]
inductive Indented : Nat → List Char → Prop where
  /-- Zero indentation: any content -/
  | zero (cs : List Char) : Indented 0 cs
  /-- Positive indentation: space followed by rest -/
  | space (n : Nat) (cs : List Char) : Indented n cs → Indented (n + 1) (' ' :: cs)

instance decideIndented (n : Nat) (cs : List Char) : Decidable (Indented n cs) :=
  match n, cs with
  | 0, cs => .isTrue (.zero cs)
  | _ + 1, [] => .isFalse (fun h => by cases h)
  | n + 1, c :: rest =>
    if hc : c = ' ' then
      hc ▸ match decideIndented n rest with
      | .isTrue h => .isTrue (.space n rest h)
      | .isFalse h => .isFalse (fun | .space _ _ h' => h h')
    else
      .isFalse (fun h => by cases h; exact hc rfl)

/--
A line has indentation of **at least** `n` spaces.

**YAML 1.2.2**: [65] s-indent(≤n) (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)

Used for block scalar content lines.
-/
@[yaml_spec "6.1" 65 "s-indent(≤n)"]
def IndentedAtLeast (n : Nat) (cs : List Char) : Prop :=
  ∃ m, m ≥ n ∧ Indented m cs

theorem indented_weaken {n m : Nat} {cs : List Char}
    (h : Indented m cs) (hle : n ≤ m) : Indented n cs := by
  induction n generalizing m cs with
  | zero => exact .zero cs
  | succ k ih =>
    cases h with
    | zero => omega
    | space m' rest h' => exact .space k rest (ih h' (by omega))

instance (n : Nat) (cs : List Char) : Decidable (IndentedAtLeast n cs) :=
  match decideIndented n cs with
  | .isTrue h => .isTrue ⟨n, Nat.le.refl, h⟩
  | .isFalse h => .isFalse (fun ⟨_, hge, hind⟩ => h (indented_weaken hind hge))

/-- IndentedAtLeast 0 is trivially satisfied by any input. -/
theorem indentedAtLeast_zero (cs : List Char) : IndentedAtLeast 0 cs :=
  ⟨0, Nat.le_refl 0, Indented.zero cs⟩

/-! ## c-forbidden Content (YAML 1.2.2 §9.1.2: https://yaml.org/spec/1.2.2/#912-document-markers)

Document markers `---` and `...` at column 0 followed by whitespace,
line break, or end-of-input are c-forbidden content (production [206]).
These terminate document content — encountering them inside a quoted
scalar means the scalar was never closed. -/

/--
Check if a character list continues a document marker.

A document marker (`---` or `...`) at column 0 is complete (c-forbidden)
when followed by whitespace, line break, or end-of-input.
-/
def isMarkerFollower : List Char → Bool
  | [] => true
  | c :: _ => c == ' ' || c == '\t' || c == '\n' || c == '\r'

/--
c-forbidden content detection.

**YAML 1.2.2**: [200] c-forbidden (§9.1.2, https://yaml.org/spec/1.2.2/#912-document-markers)

A character sequence at column 0 is c-forbidden if it begins with
`---` ([197] c-directives-end) or `...` ([198] c-document-end) followed
by whitespace, line break, or end-of-input.
This is the pure specification of the parser's `atDocumentBoundary` check.
-/
@[yaml_spec "9.1.2" 200 "c-forbidden"]
def isCForbiddenPrefix : List Char → Bool
  | '-' :: '-' :: '-' :: rest => isMarkerFollower rest
  | '.' :: '.' :: '.' :: rest => isMarkerFollower rest
  | _ => false

/--
Characters that the fold operation appends to the accumulator.

YAML line folding (§6.5) replaces line breaks with either a single
space (fold) or preserved newlines (blank lines). The fold operation
only appends these two characters — it never introduces content characters.
-/
def isFoldAppendChar (c : Char) : Prop :=
  c = ' ' ∨ c = '\n'

instance (c : Char) : Decidable (isFoldAppendChar c) := by
  unfold isFoldAppendChar; infer_instance

/-! ## Scalar Grammar (YAML 1.2.2 §7.3: https://yaml.org/spec/1.2.2/#73-flow-scalar-styles) -/

/-! ### Escape Sequences (YAML 1.2.2 §5.7: https://yaml.org/spec/1.2.2/#57-escaped-characters) -/

/--
Pure specification of YAML named escape sequence resolution.

Maps the character *after* `\` to its resolved character value.
Returns `none` for characters that are not named escapes (i.e.,
characters that would require `\xHH`, `\uHHHH`, or `\UHHHHHHHH`
hex escapes, or are unknown/invalid).

This is the specification against which the parser's `processEscape`
function (in `Parser/Scalar.lean`) is verified. The 18 named escapes
follow YAML 1.2.2 §5.7 Table 5.13 exactly.
-/
@[yaml_spec "5.7" 61 "c-ns-esc-char"]
def resolveNamedEscape : Char → Option Char
  | '0'  => some '\x00'   -- [42] ns-esc-null
  | 'a'  => some '\x07'   -- [43] ns-esc-bell
  | 'b'  => some '\x08'   -- [44] ns-esc-backspace
  | 't'  => some '\t'     -- [45] ns-esc-horizontal-tab
  | '\t' => some '\t'     -- [46] ns-esc-horizontal-tab (literal)
  | 'n'  => some '\n'     -- [47] ns-esc-line-feed
  | 'v'  => some '\x0b'   -- [48] ns-esc-vertical-tab
  | 'f'  => some '\x0c'   -- [49] ns-esc-form-feed
  | 'r'  => some '\r'     -- [50] ns-esc-carriage-return
  | 'e'  => some '\x1b'   -- [51] ns-esc-escape
  | ' '  => some ' '      -- [52] ns-esc-space
  | '"'  => some '"'      -- [53] ns-esc-double-quote
  | '/'  => some '/'      -- [54] ns-esc-slash
  | '\\' => some '\\'     -- [55] ns-esc-backslash
  | 'N'  => some '\x85'   -- [56] ns-esc-next-line
  | '_'  => some '\xa0'   -- [57] ns-esc-non-breaking-space
  | 'x'  => none          -- [58] ns-esc-8-bit (hex, not named)
  | 'u'  => none          -- [59] ns-esc-16-bit (hex, not named)
  | 'U'  => none          -- [60] ns-esc-32-bit (hex, not named)
  | _    => none           -- unknown escape

/-- The set of named escape input characters (§5.7 Table 5.13). -/
def isNamedEscapeChar (c : Char) : Prop :=
  resolveNamedEscape c ≠ none

instance (c : Char) : Decidable (isNamedEscapeChar c) := by
  unfold isNamedEscapeChar; infer_instance

/-! ### Plain Scalar Content Predicates (§7.3.3)

Character-level constraints that plain scalar content must satisfy.
These predicates are used as proof obligations in `ValidNode` constructors
to tie the grammar specification to the actual YAML production rules.
-/

-- NOTE: The old 1-argument `validPlainFirst` has been removed.
-- Use `validPlainFirstProp` (2-arg, with `inFlow : Bool`) from CharPredicates.lean instead.

-- `hasAdjacentChars` and `hasAdjacentChars_iff` are re-exported from CharPredicates above.

/-- Backward-compatible alias for `noColonSpaceProp` (YAML 1.2.2 §7.3.3 [127]). -/
abbrev noColonSpace := noColonSpaceProp

/-- Backward-compatible alias for `noSpaceHashProp` (YAML 1.2.2 §7.3.3 [127]). -/
abbrev noSpaceHash := noSpaceHashProp

/-- Backward-compatible alias for `noFlowIndicatorsProp` (YAML 1.2.2 §7.3.3 [126]). -/
abbrev noFlowIndicators := noFlowIndicatorsProp

/-! ## Node Grammar

Combines scalars (§7.3: https://yaml.org/spec/1.2.2/#73-flow-scalar-styles),
flow collections (§7.4: https://yaml.org/spec/1.2.2/#74-flow-collection-styles),
and block collections (§8: https://yaml.org/spec/1.2.2/#chapter-8-block-style-productions). -/

/--
A valid YAML node — the top-level grammar production.

**YAML 1.2.2**: [192] s-l+block-node(n,c) / [157] ns-flow-node(n,c)

A node is any valid YAML value: scalar, sequence, or mapping,
in either block or flow style. Defined as a single inductive to
avoid mutual recursion between structures.
-/
@[yaml_spec "8.2.3" 196 "s-l+block-node(n,c)", yaml_spec "7.5" 157 "ns-flow-node(n,c)"]
inductive ValidNode where
  /-- [128] ns-plain(n,BLOCK-KEY/BLOCK-OUT) — Plain scalar in block context.
      Carries character-level production-rule constraints:
      [123] ns-plain-first, [127] no `: ` or ` #`. -/
  | plainScalarBlock (content : String) (nonempty : content.length > 0)
      (firstValid : validPlainFirstProp content false)
      (noCS : noColonSpace content) (noSH : noSpaceHash content)
  /-- [128] ns-plain(n,FLOW-OUT/FLOW-IN) — Plain scalar in flow context.
      Additionally [126] no flow-indicator characters. -/
  | plainScalarFlow (content : String) (nonempty : content.length > 0)
      (firstValid : validPlainFirstProp content true)
      (noCS : noColonSpace content) (noSH : noSpaceHash content)
      (noFlow : noFlowIndicators content)
  /-- [118] c-single-quoted(n,c) (§7.3.2) — Single-quoted scalar -/
  | singleQuoted (content : String)
  /-- [107] c-double-quoted(n,c) (§7.3.1) — Double-quoted scalar -/
  | doubleQuoted (content : String)
  /-- [170] c-l+literal(n) (§8.1.2) — Literal block scalar -/
  | literalScalar (content : String) (indent : Nat) (chomp : ChompStyle)
  /-- [175] c-l+folded(n) (§8.1.3) — Folded block scalar -/
  | foldedScalar (content : String) (indent : Nat) (chomp : ChompStyle)
  /-- [180] l+block-sequence(n) (§8.2.1) — Block sequence -/
  | blockSeq (indent : Nat) (items : List ValidNode)
  /-- [184] l+block-mapping(n) (§8.2.2) — Block mapping -/
  | blockMap (indent : Nat) (entries : List (ValidNode × ValidNode))
  /-- [134] c-flow-sequence(n,c) (§7.4.1) — Flow sequence -/
  | flowSeq (items : List ValidNode)
  /-- [137] c-flow-mapping(n,c) (§7.4.2) — Flow mapping -/
  | flowMap (entries : List (ValidNode × ValidNode))
  /-- [72] e-node (§7.2.1) — Empty node (implicit null).
      YAML 1.2.2: `e-node ::= e-scalar`, `e-scalar ::= /* empty */`.
      The parser produces this for absent values (e.g., empty block entries). -/
  | emptyNode

/-! ## Document Grammar (YAML 1.2.2 §9: https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions) -/

/--
A valid YAML document.

**YAML 1.2.2**: [204] l-any-document (§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)
- [201] l-bare-document: implicit document
- [202] l-explicit-document: `---` prefixed document
- [203] l-directive-document: directives + `---` prefixed document

Documents may optionally start with `---` and end with `...`.

**Phase F decision (kept)**: Specification-level structure for multi-document
stream support. Not yet referenced by proof files — bridge theorems will
connect when full stream-level parsing proofs are developed.
-/
@[yaml_spec "9" 204 "l-any-document"]
structure ValidDocument where
  /-- The document content -/
  content : ValidNode
  /-- Optional YAML directive version -/
  yamlVersion : Option String := none

/--
A valid YAML stream — one or more documents.

**YAML 1.2.2**: [205] l-yaml-stream (§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)

**Phase F decision (kept)**: Top-level specification type. Not yet referenced
by proofs — `checkValidStream` in ScannerCorrectness.lean is a Bool utility
that shares the name but not the type. Full stream proofs are future work.
-/
@[yaml_spec "9" 205 "l-yaml-stream"]
structure ValidStream where
  documents : List ValidDocument
  nonempty : documents.length > 0

/-! ## Token Stream Contract

`ValidTokenStream` relates an input string to the token array produced
by scanning it. This is the bridge between the string-level grammar
(`ValidNode`) and the token-level parser (`TokenParser`).

The scanner's correctness theorem (future work) will state:
```
theorem scan_valid (input : String) (tokens : Array (Positioned YamlToken))
    (h : Scanner.scan input = .ok tokens) : ValidTokenStream input tokens
```
-/

/--
Valid token stream: structural contract between the scanner and the token parser.

Captures the invariants that `TokenParser` relies on when consuming tokens:
- Stream boundary tokens bracket the array (`streamStart` … `streamEnd`)
- Token positions are monotonically non-decreasing

**YAML 1.2.2**: §3.1 Processes — this corresponds to the
Presentation → Serialization boundary.
-/
structure ValidTokenStream where
  /-- The input string that was scanned -/
  input : String
  /-- The resulting token array -/
  tokens : Array (Positioned YamlToken)
  /-- At least two tokens (streamStart + streamEnd) -/
  sizeGe2 : tokens.size ≥ 2
  /-- First token is streamStart -/
  firstIsStreamStart : (tokens[0]'(by omega)).val = .streamStart
  /-- Last token is streamEnd -/
  lastIsStreamEnd : (tokens[tokens.size - 1]'(by omega)).val = .streamEnd
  /-- Token positions are monotonically non-decreasing -/
  positionsOrdered : ∀ (i j : Fin tokens.size), i.val < j.val →
    (tokens[i]).pos.offset ≤ (tokens[j]).pos.offset

/--
Propositional twin of `ValidTokenStream`. Flattens the structure into a
conjunction so that `theorem`s mentioning it are visible to the
doc-verification-bridge (which traces `Prop`-level names, not structure
constructors classified as `computationalOperation`).
-/
def ValidTokenStreamProp (tokens : Array (Positioned YamlToken)) : Prop :=
  tokens.size ≥ 2 ∧
  (∀ (h : 0 < tokens.size), (tokens[0]'h).val = .streamStart) ∧
  (∀ (h : tokens.size - 1 < tokens.size), (tokens[tokens.size - 1]'h).val = .streamEnd) ∧
  ∀ (i j : Fin tokens.size), i.val < j.val →
    (tokens[i]).pos.offset ≤ (tokens[j]).pos.offset

/-! ## Top-Level Specification -/

/--
Correspondence between grammar nodes and YAML values.

This bridges the specification (grammar) and the implementation (YamlValue AST).
-/
inductive NodeToValue : ValidNode → YamlValue → Prop where
  | plainScalarBlock (content : String) (h : content.length > 0)
      (hfirst : validPlainFirstProp content false)
      (hnoCS : noColonSpace content) (hnoSH : noSpaceHash content) :
      NodeToValue
        (.plainScalarBlock content h hfirst hnoCS hnoSH)
        (.scalar ⟨content, .plain, none, none, none⟩)
  | plainScalarFlow (content : String) (h : content.length > 0)
      (hfirst : validPlainFirstProp content true)
      (hnoCS : noColonSpace content) (hnoSH : noSpaceHash content)
      (hnoFlow : noFlowIndicators content) :
      NodeToValue
        (.plainScalarFlow content h hfirst hnoCS hnoSH hnoFlow)
        (.scalar ⟨content, .plain, none, none, none⟩)
  | singleQuoted (content : String) :
      NodeToValue
        (.singleQuoted content)
        (.scalar ⟨content, .singleQuoted, none, none, none⟩)
  | doubleQuoted (content : String) :
      NodeToValue
        (.doubleQuoted content)
        (.scalar ⟨content, .doubleQuoted, none, none, none⟩)
  | literalScalar (content : String) (indent : Nat) (chomp : ChompStyle) :
      NodeToValue
        (.literalScalar content indent chomp)
        (.scalar ⟨content, .literal, none, none, some ⟨chomp, some indent⟩⟩)
  | foldedScalar (content : String) (indent : Nat) (chomp : ChompStyle) :
      NodeToValue
        (.foldedScalar content indent chomp)
        (.scalar ⟨content, .folded, none, none, some ⟨chomp, some indent⟩⟩)
  | blockSeq (indent : Nat) (nodes : List ValidNode) (vals : List YamlValue)
      (hlen : nodes.length = vals.length)
      (hcorr : ∀ i (hi : i < nodes.length),
        NodeToValue (nodes.get ⟨i, hi⟩) (vals.get ⟨i, by omega⟩)) :
      NodeToValue
        (.blockSeq indent nodes)
        (.sequence .block (vals.toArray) none)
  | blockMap (indent : Nat)
      (entries : List (ValidNode × ValidNode))
      (pairs : List (YamlValue × YamlValue))
      (hlen : entries.length = pairs.length)
      (hkeys : ∀ i (hi : i < entries.length),
        NodeToValue (entries.get ⟨i, hi⟩).1 (pairs.get ⟨i, by omega⟩).1)
      (hvals : ∀ i (hi : i < entries.length),
        NodeToValue (entries.get ⟨i, hi⟩).2 (pairs.get ⟨i, by omega⟩).2) :
      NodeToValue
        (.blockMap indent entries)
        (.mapping .block (pairs.toArray) none)
  | flowSeq (nodes : List ValidNode) (vals : List YamlValue)
      (hlen : nodes.length = vals.length)
      (hcorr : ∀ i (hi : i < nodes.length),
        NodeToValue (nodes.get ⟨i, hi⟩) (vals.get ⟨i, by omega⟩)) :
      NodeToValue
        (.flowSeq nodes)
        (.sequence .flow (vals.toArray) none)
  | flowMap
      (entries : List (ValidNode × ValidNode))
      (pairs : List (YamlValue × YamlValue))
      (hlen : entries.length = pairs.length)
      (hkeys : ∀ i (hi : i < entries.length),
        NodeToValue (entries.get ⟨i, hi⟩).1 (pairs.get ⟨i, by omega⟩).1)
      (hvals : ∀ i (hi : i < entries.length),
        NodeToValue (entries.get ⟨i, hi⟩).2 (pairs.get ⟨i, by omega⟩).2) :
      NodeToValue
        (.flowMap entries)
        (.mapping .flow (pairs.toArray) none)
  /-- [72] e-node — empty node maps to the null plain scalar. -/
  | emptyNode :
      NodeToValue .emptyNode (.scalar ⟨"", .plain, none, none, none⟩)

/--
**The specification**: a string `s` is valid YAML producing value `v`.

This is the proposition that the parser's soundness proof targets:
```
theorem parse_sound : parse s = .ok v → ValidYaml s v
```

And completeness (if desired):
```
theorem parse_complete : ValidYaml s v → parse s = .ok v
```
-/
structure ValidYaml where
  /-- The input string -/
  input : String
  /-- The resulting YAML value -/
  value : YamlValue
  /-- The input parses according to the grammar -/
  grammar : ValidNode
  /-- The grammar node corresponds to the value -/
  corresponds : NodeToValue grammar value

/-! ## Computable Specification Function

`toYamlValue` is the computable witness of `NodeToValue`: it maps
every `ValidNode` to the unique `YamlValue` prescribed by the relation.
This makes the relation **total** and **deterministic** by construction.
-/

/--
Compute the `YamlValue` corresponding to a `ValidNode`.

This is the "specification function" that the parser's output must match.
Structural recursion on `ValidNode` terminates because `List ValidNode`
sub-lists are structurally smaller.
-/
def toYamlValue : ValidNode → YamlValue
  | .plainScalarBlock content .. => .scalar ⟨content, .plain, none, none, none⟩
  | .plainScalarFlow content .. => .scalar ⟨content, .plain, none, none, none⟩
  | .singleQuoted content => .scalar ⟨content, .singleQuoted, none, none, none⟩
  | .doubleQuoted content => .scalar ⟨content, .doubleQuoted, none, none, none⟩
  | .literalScalar content indent chomp =>
      .scalar ⟨content, .literal, none, none, some ⟨chomp, some indent⟩⟩
  | .foldedScalar content indent chomp =>
      .scalar ⟨content, .folded, none, none, some ⟨chomp, some indent⟩⟩
  | .blockSeq _ items => .sequence .block (toYamlValueList items).toArray none
  | .blockMap _ entries =>
      .mapping .block (toYamlValuePairs entries).toArray none
  | .flowSeq items => .sequence .flow (toYamlValueList items).toArray none
  | .flowMap entries =>
      .mapping .flow (toYamlValuePairs entries).toArray none
  | .emptyNode => .scalar ⟨"", .plain, none, none, none⟩
where
  /-- Map a list of nodes to a list of values. -/
  toYamlValueList : List ValidNode → List YamlValue
    | [] => []
    | n :: ns => toYamlValue n :: toYamlValueList ns
  /-- Map a list of node pairs to a list of value pairs. -/
  toYamlValuePairs : List (ValidNode × ValidNode) → List (YamlValue × YamlValue)
    | [] => []
    | (k, v) :: rest => (toYamlValue k, toYamlValue v) :: toYamlValuePairs rest

/-! ## Annotation Stripping

`stripAnnotations` removes all non-semantic metadata (tags, anchors,
block-scalar metadata) from a `YamlValue`, keeping only the content
and style.  This bridges the parser output (which carries tags/anchors
from node properties) to the `toYamlValue` output (which produces
values with `none` for those fields).

Structurally recursive via list helpers, mirroring `toYamlValue`.
-/

/--
Strip tags, anchors, and block-scalar metadata from a `YamlValue`.

Preserves only the **semantic core**: scalar content + style,
collection style + recursive structure.  Alias nodes are left as-is
(they carry no annotations).
-/
def stripAnnotations : YamlValue → YamlValue
  | .scalar s => .scalar ⟨s.content, s.style, none, none, none⟩
  | .sequence style items _ _ =>
      .sequence style (stripAnnotationsList items.toList).toArray
  | .mapping style pairs _ _ =>
      .mapping style (stripAnnotationsPairs pairs.toList).toArray
  | .alias name => .alias name
where
  /-- Strip annotations from a list of values. -/
  stripAnnotationsList : List YamlValue → List YamlValue
    | [] => []
    | v :: vs => stripAnnotations v :: stripAnnotationsList vs
  /-- Strip annotations from a list of value pairs. -/
  stripAnnotationsPairs : List (YamlValue × YamlValue) → List (YamlValue × YamlValue)
    | [] => []
    | (k, v) :: rest =>
        (stripAnnotations k, stripAnnotations v) :: stripAnnotationsPairs rest

/-! ## Scalar Scannability and Grammable Predicate

The scanner guarantees that plain scalar tokens satisfy character-level
constraints from YAML 1.2.2 §7.3.3. `ScalarScannable` captures these
constraints, parameterized by the flow context (`inFlow : Bool`).

`Grammable` is the tree-level predicate: a `YamlValue` is grammable when
it contains no alias nodes and every nested scalar satisfies `ScalarScannable`
at the appropriate flow context. This is the precondition for recovering a
`ValidNode` witness — it captures the *scanner contract* that the parser
relies on.
-/

/--
Scanner contract: per-scalar character constraints in flow context.

A scalar satisfies `ScalarScannable s inFlow` when:
- Non-plain scalars: trivially satisfied (no character constraints)
- Empty plain scalars: trivially satisfied
- Non-empty plain scalars: first character can start a plain scalar,
  no `: ` or ` #` sequences, and (in flow context) no flow indicators.

**YAML 1.2.2**: §7.3.3 [123] ns-plain-first, [127] ns-plain-char,
[126] ns-plain-safe(FLOW-IN)
-/
def ScalarScannable (s : Scalar) (inFlow : Bool) : Prop :=
  s.style = .plain → s.content.length > 0 →
    validPlainFirstProp s.content inFlow ∧ noColonSpace s.content ∧ noSpaceHash s.content
    ∧ (inFlow = true → noFlowIndicators s.content)

/--
A `YamlValue` is **grammable** if:
1. It contains no `YamlValue.alias` nodes (aliases must be resolved first).
2. Every nested plain scalar with non-empty content satisfies
   `ScalarScannable` at the appropriate flow context.

The `inFlow` parameter threads the flow context through the tree:
- Top-level documents start at `inFlow = false`
- Flow collections (`style = .flow`) set `inFlow = true` for descendants
- Block collections inherit the parent's `inFlow`

**YAML 1.2.2**: Flow context is inherited (§3.2.3.1).
-/
inductive Grammable : YamlValue → Bool → Prop where
  | scalar (s : Scalar) (inFlow : Bool)
      (h : ScalarScannable s inFlow) :
      Grammable (.scalar s) inFlow
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String) (inFlow : Bool)
      (h : ∀ i : Fin items.size, Grammable items[i] (inFlow || style == .flow)) :
      Grammable (.sequence style items tag anchor) inFlow
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String) (inFlow : Bool)
      (hk : ∀ i : Fin pairs.size, Grammable pairs[i].1 (inFlow || style == .flow))
      (hv : ∀ i : Fin pairs.size, Grammable pairs[i].2 (inFlow || style == .flow)) :
      Grammable (.mapping style pairs tag anchor) inFlow

/--
Pre-compose tree validity: the **scanner contract**.

`Scannable` is the pre-compose counterpart of `Grammable`. It threads
flow context (`inFlow : Bool`) exactly like `Grammable`, but additionally
allows `.alias` nodes — because alias resolution happens during
composition, and the raw parser output (serialization tree) may contain
unresolved aliases.

The bridging theorem `compose_scannable_to_grammable` (Phase C1) will
prove that alias resolution + anchor stripping transforms a `Scannable`
tree into a `Grammable` tree.

**YAML 1.2.2**: §3.2.2 — the serialization tree may contain alias nodes;
the representation graph (post-compose) does not.
-/
inductive Scannable : YamlValue → Bool → Prop where
  | scalar (s : Scalar) (inFlow : Bool)
      (h : ScalarScannable s inFlow) :
      Scannable (.scalar s) inFlow
  | alias (name : String) (inFlow : Bool) :
      Scannable (.alias name) inFlow
  | sequence (style : CollectionStyle) (items : Array YamlValue)
      (tag : Option String) (anchor : Option String) (inFlow : Bool)
      (h : ∀ i : Fin items.size, Scannable items[i] (inFlow || style == .flow)) :
      Scannable (.sequence style items tag anchor) inFlow
  | mapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
      (tag : Option String) (anchor : Option String) (inFlow : Bool)
      (hk : ∀ i : Fin pairs.size, Scannable pairs[i].1 (inFlow || style == .flow))
      (hv : ∀ i : Fin pairs.size, Scannable pairs[i].2 (inFlow || style == .flow)) :
      Scannable (.mapping style pairs tag anchor) inFlow

/-! ## Quoted Scalar Fold Result Type

  Relocated from `Parser/Scalar.lean` in P10.3 so that proof files
  (`StringProperties.lean`, `Validation.lean`, `FoldNewlines.lean`)
  can reference it without importing the old char-level parser.
-/

/--
Result of folding newlines in a quoted scalar continuation line.

YAML 1.2.2 §9.1.2 production [206] defines `c-forbidden`: the sequences
`--- ` and `... ` at column 0 (start-of-line) followed by whitespace,
line break, or end-of-input are document boundary markers that terminate
document content. Inside a quoted scalar, encountering `c-forbidden` on
a continuation line means the scalar was never closed — this is
definitively invalid YAML.

Without an explicit result type, backtracking would swallow the error
and some enclosing combinator might silently accept part of the input.
-/
inductive FoldResult where
  /-- Successfully folded the continuation. `result` is the accumulated
      string with the fold applied (space or preserved newlines). -/
  | folded (result : String)
  /-- Found a `c-forbidden` document boundary indicator (`---` or `...`)
      at column 0 on a continuation line. The quoted scalar is unterminated.
      This is definitively invalid — not a backtracking opportunity. -/
  | forbidden (msg : String)
  deriving Repr, Nonempty

/-! ## Block Scalar Header Character Classification
  (YAML 1.2.2 §8.1.1, https://yaml.org/spec/1.2.2/#811-block-scalar-headers)

  The header after `|`/`>` may contain at most two indicator characters:
  - Chomp indicator: `-` (strip) or `+` (keep)
  - Indentation indicator: digit `1`–`9`

  Everything else belongs to the content stream and must NOT be consumed
  by the header parser. This predicate makes the boundary between
  "header characters" and "content characters" machine-checkable.
-/

/--
A character is a valid block scalar header indicator character.

**YAML 1.2.2**: [158] c-b-block-header(m,t) (§8.1.1, https://yaml.org/spec/1.2.2/#811-block-scalar-headers)
- [159] c-indentation-indicator(m): digit `1`–`9`
- [160] c-chomping-indicator(t): `-` (strip) or `+` (keep)

This is the formal specification of which characters `blockScalarHeader`
is allowed to consume as indicator characters (before trailing
whitespace/comment/newline).

**Decidable**: used both in proofs and runtime assertions.
-/
@[yaml_spec "8.1.1" 158 "c-b-block-header(m,t)"]
def isBlockScalarHeaderChar (c : Char) : Bool :=
  c == '-' || c == '+' || (c >= '1' && c <= '9')

instance : DecidablePred (fun c => isBlockScalarHeaderChar c = true) :=
  fun c => inferInstanceAs (Decidable (isBlockScalarHeaderChar c = true))

/--
Pure specification: extract the header indicator portion from a character list.

Given the characters immediately after `|`/`>`, returns the prefix
that consists of valid header characters (at most 2, in any order)
and the remaining characters.

This is the reference implementation against which the parser's
`blockScalarHeader` is contracted.
-/
def extractHeaderChars : List Char → List Char × List Char
  | c :: rest =>
    if isBlockScalarHeaderChar c then
      let (hdr, tail) := extractHeaderChars rest
      (c :: hdr, tail)
    else
      ([], c :: rest)
  | [] => ([], [])

/--
The header extracts at most 2 indicator characters.

Even though `extractHeaderChars` is defined recursively, a valid
YAML header has at most one chomp indicator and one indentation
indicator, so the prefix has length ≤ 2.
-/
def validHeaderLength (cs : List Char) : Prop :=
  (extractHeaderChars cs).1.length ≤ 2

instance (cs : List Char) : Decidable (validHeaderLength cs) := by
  unfold validHeaderLength; infer_instance

/--
A character that is NOT a header indicator belongs to the content stream.
This is the key negative specification: consuming such a character in the
header parser violates the contract.
-/
def isContentChar (c : Char) : Prop :=
  isBlockScalarHeaderChar c = false

instance (c : Char) : Decidable (isContentChar c) := by
  unfold isContentChar; infer_instance

end Lean4Yaml.Grammar
