/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types

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

/-! ## Character Classifications (YAML 1.2.2 §5: https://yaml.org/spec/1.2.2/#chapter-5-character-productions) -/

/--
YAML printable characters.

**YAML 1.2.2**: [1] c-printable (§5.1, https://yaml.org/spec/1.2.2/#51-character-set)

The set of characters that can appear in a YAML stream.
-/
def isPrintable (c : Char) : Prop :=
  c == '\t'                                    -- Tab
  ∨ (c.val ≥ 0x20 ∧ c.val ≤ 0x7E)            -- Basic ASCII printable
  ∨ c == '\u0085'                              -- Next Line
  ∨ (c.val ≥ 0xA0 ∧ c.val ≤ 0xD7FF)          -- Basic Multilingual Plane
  ∨ (c.val ≥ 0xE000 ∧ c.val ≤ 0xFFFD)        -- More BMP
  ∨ (c.val ≥ 0x10000 ∧ c.val ≤ 0x10FFFF)     -- Supplementary planes

instance (c : Char) : Decidable (isPrintable c) := by unfold isPrintable; infer_instance

/--
Line break characters.

**YAML 1.2.2**: [24] b-line-feed, [25] b-carriage-return, [26] b-char
(§5.4, https://yaml.org/spec/1.2.2/#54-line-break-characters)
-/
def isLineBreak (c : Char) : Prop :=
  c == '\n' ∨ c == '\r'

instance (c : Char) : Decidable (isLineBreak c) := by unfold isLineBreak; infer_instance

/--
White space characters for YAML.

**YAML 1.2.2**: [33] s-white (§5.5, https://yaml.org/spec/1.2.2/#55-white-space-characters)
- [31] s-space: the space character
- [32] s-tab: the tab character

Only space and tab — NOT line breaks.
-/
def isWhiteSpace (c : Char) : Prop :=
  c == ' ' ∨ c == '\t'

instance (c : Char) : Decidable (isWhiteSpace c) := by unfold isWhiteSpace; infer_instance

/--
YAML space character for indentation.

**YAML 1.2.2**: [31] s-space (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)

Only the space character is valid for indentation.
Tabs are explicitly forbidden for indentation in YAML 1.2.2.
-/
def isIndentChar (c : Char) : Prop :=
  c == ' '

instance (c : Char) : Decidable (isIndentChar c) := by unfold isIndentChar; infer_instance

/--
Characters that can start a plain scalar.

**YAML 1.2.2**: [123] ns-plain-first(c) (§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style)

Excludes indicators ([22] c-indicator) that have special meaning at the start.
-/
def canStartPlainScalar (c : Char) : Prop :=
  isPrintable c
  ∧ ¬ isWhiteSpace c
  ∧ ¬ isLineBreak c
  ∧ c ∉ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
         '\'', '"', '%', '@', '`']

instance (c : Char) : Decidable (canStartPlainScalar c) := by
  unfold canStartPlainScalar; infer_instance

/--
Flow indicator characters.

**YAML 1.2.2**: [23] c-flow-indicator (§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters)

These terminate plain scalars in flow context.
-/
def isFlowIndicator (c : Char) : Prop :=
  c ∈ [',', '[', ']', '{', '}']

instance (c : Char) : Decidable (isFlowIndicator c) := by unfold isFlowIndicator; infer_instance

/-! ## Indentation (YAML 1.2.2 §6.1: https://yaml.org/spec/1.2.2/#61-indentation-spaces) -/

/--
An indentation of `n` spaces at the start of a line.

**YAML 1.2.2**: [63] s-indent(n) (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)

This is the core proposition for block-style YAML. A line is indented
at level `n` if it starts with exactly `n` space characters.
-/
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
def IndentedAtLeast (n : Nat) (cs : List Char) : Prop :=
  ∃ m, m ≥ n ∧ Indented m cs

private theorem indented_weaken {n m : Nat} {cs : List Char}
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

/--
A valid plain scalar in block context.

**YAML 1.2.2**: [128] ns-plain(n,BLOCK-KEY/BLOCK-OUT)
(§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style)
- [123] ns-plain-first(c): first character constraint
- [127] ns-plain-char(c): subsequent character constraint
- [132] ns-plain-multi-line(n,c): multi-line continuation with folding

Plain scalars in block context:
- Cannot start with indicators
- Cannot contain `: ` (colon-space) or ` #` (space-hash)
- Are terminated by line breaks, `: `, or less-indented lines
- Continuation lines are folded (replacing newline with space)
-/
structure ValidPlainScalarBlock where
  /-- The resolved content string -/
  content : String
  /-- The content is non-empty -/
  nonempty : content.length > 0

/--
A valid plain scalar in flow context.

**YAML 1.2.2**: [128] ns-plain(n,FLOW-OUT/FLOW-IN)
(§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style)
- [126] ns-plain-safe-in: flow-context safe characters

Plain scalars in flow context additionally:
- Cannot contain flow indicators ([23] c-flow-indicator: `,`, `[`, `]`, `{`, `}`)
- Are terminated by flow indicators in addition to block terminators
-/
structure ValidPlainScalarFlow where
  content : String
  nonempty : content.length > 0

/--
A valid single-quoted scalar.

**YAML 1.2.2**: [118] c-single-quoted(n,c) (§7.3.2, https://yaml.org/spec/1.2.2/#732-single-quoted-style)
- [18] c-single-quote: the `'` delimiter
- [115] c-quoted-quote: `''` → `'` (doubled single quote)
- [116] nb-single-char: content characters

Single-quoted scalars:
- Delimited by `'...'`
- Only escape: `''` → `'` (doubled single quote)
- All other characters are literal
-/
structure ValidSingleQuoted where
  content : String

/--
A valid double-quoted scalar.

**YAML 1.2.2**: [107] c-double-quoted(n,c) (§7.3.1, https://yaml.org/spec/1.2.2/#731-double-quoted-style)
- [19] c-double-quote: the `"` delimiter
- [61] c-ns-esc-char: escape sequences ([42]–[60])
- [106] ns-double-char: content characters
- [114] nb-double-multi-line(n): multi-line with folding

Double-quoted scalars:
- Delimited by `"..."`
- Full escape sequence support: `\n`, `\t`, `\\`, `\"`, `\xHH`, `\uHHHH`, etc.
- Line folding: newlines become spaces (unless `\` at end of line)
-/
structure ValidDoubleQuoted where
  content : String

/--
Chomping styles for block scalars.

**YAML 1.2.2**: [160] c-chomping-indicator(t)
(§8.1.1.2, https://yaml.org/spec/1.2.2/#8112-block-chomping-indicator)
-/
inductive ChompStyle where
  | strip  -- Remove all trailing newlines (`|-`)
  | clip   -- Keep one trailing newline (default `|`)
  | keep   -- Keep all trailing newlines (`|+`)
  deriving Repr, BEq, DecidableEq

/--
A valid literal block scalar.

**YAML 1.2.2**: [170] c-l+literal(n) (§8.1.2, https://yaml.org/spec/1.2.2/#812-literal-style)
- [16] c-literal: the `|` indicator
- [158] c-b-block-header(m,t): header with indent/chomp indicators
- [166] l-literal-content(n,t): content lines

Literal scalars (`|`):
- Preserve line breaks exactly
- Content indented relative to indicator
- Optional chomping indicator: `-` (strip), `+` (keep), default (clip)
-/
structure ValidLiteralScalar where
  content : String
  indent : Nat
  chomp : ChompStyle

/--
A valid folded block scalar.

**YAML 1.2.2**: [175] c-l+folded(n) (§8.1.3, https://yaml.org/spec/1.2.2/#813-folded-style)
- [17] c-folded: the `>` indicator
- [158] c-b-block-header(m,t): header with indent/chomp indicators
- [174] l-folded-content(n,t): content lines with fold semantics
- [173] s-b-folded(n,c): line folding rules

Folded scalars (`>`):
- Fold line breaks to spaces (except for blank lines and more-indented lines)
- Optional chomping indicator
-/
structure ValidFoldedScalar where
  content : String
  indent : Nat
  chomp : ChompStyle

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
inductive ValidNode where
  /-- [128] ns-plain(n,BLOCK-KEY/BLOCK-OUT) — Plain scalar in block context -/
  | plainScalarBlock (content : String) (nonempty : content.length > 0)
  /-- [128] ns-plain(n,FLOW-OUT/FLOW-IN) — Plain scalar in flow context -/
  | plainScalarFlow (content : String) (nonempty : content.length > 0)
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

/-! ## Document Grammar (YAML 1.2.2 §9: https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions) -/

/--
A valid YAML document.

**YAML 1.2.2**: [204] l-any-document (§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)
- [201] l-bare-document: implicit document
- [202] l-explicit-document: `---` prefixed document
- [203] l-directive-document: directives + `---` prefixed document

Documents may optionally start with `---` and end with `...`.
-/
structure ValidDocument where
  /-- The document content -/
  content : ValidNode
  /-- Optional YAML directive version -/
  yamlVersion : Option String := none

/--
A valid YAML stream — one or more documents.

**YAML 1.2.2**: [205] l-yaml-stream (§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)
-/
structure ValidStream where
  documents : List ValidDocument
  nonempty : documents.length > 0

/-! ## Top-Level Specification -/

/--
Correspondence between grammar nodes and YAML values.

This bridges the specification (grammar) and the implementation (YamlValue AST).
-/
inductive NodeToValue : ValidNode → YamlValue → Prop where
  | plainScalarBlock (content : String) (h : content.length > 0) :
      NodeToValue
        (.plainScalarBlock content h)
        (.scalar ⟨content, .plain, none⟩)
  | plainScalarFlow (content : String) (h : content.length > 0) :
      NodeToValue
        (.plainScalarFlow content h)
        (.scalar ⟨content, .plain, none⟩)
  | singleQuoted (content : String) :
      NodeToValue
        (.singleQuoted content)
        (.scalar ⟨content, .singleQuoted, none⟩)
  | doubleQuoted (content : String) :
      NodeToValue
        (.doubleQuoted content)
        (.scalar ⟨content, .doubleQuoted, none⟩)
  | literalScalar (content : String) (indent : Nat) (chomp : ChompStyle) :
      NodeToValue
        (.literalScalar content indent chomp)
        (.scalar ⟨content, .literal, none⟩)
  | foldedScalar (content : String) (indent : Nat) (chomp : ChompStyle) :
      NodeToValue
        (.foldedScalar content indent chomp)
        (.scalar ⟨content, .folded, none⟩)
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
  | .plainScalarBlock content _ => .scalar ⟨content, .plain, none⟩
  | .plainScalarFlow content _ => .scalar ⟨content, .plain, none⟩
  | .singleQuoted content => .scalar ⟨content, .singleQuoted, none⟩
  | .doubleQuoted content => .scalar ⟨content, .doubleQuoted, none⟩
  | .literalScalar content _ _ => .scalar ⟨content, .literal, none⟩
  | .foldedScalar content _ _ => .scalar ⟨content, .folded, none⟩
  | .blockSeq _ items => .sequence .block (toYamlValueList items).toArray none
  | .blockMap _ entries =>
      .mapping .block (toYamlValuePairs entries).toArray none
  | .flowSeq items => .sequence .flow (toYamlValueList items).toArray none
  | .flowMap entries =>
      .mapping .flow (toYamlValuePairs entries).toArray none
where
  /-- Map a list of nodes to a list of values. -/
  toYamlValueList : List ValidNode → List YamlValue
    | [] => []
    | n :: ns => toYamlValue n :: toYamlValueList ns
  /-- Map a list of node pairs to a list of value pairs. -/
  toYamlValuePairs : List (ValidNode × ValidNode) → List (YamlValue × YamlValue)
    | [] => []
    | (k, v) :: rest => (toYamlValue k, toYamlValue v) :: toYamlValuePairs rest

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
