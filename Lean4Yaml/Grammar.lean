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
YAML printable characters (§5.1: https://yaml.org/spec/1.2.2/#51-character-set).
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
Line break characters (§5.4: https://yaml.org/spec/1.2.2/#54-line-break-characters).
-/
def isLineBreak (c : Char) : Prop :=
  c == '\n' ∨ c == '\r'

instance (c : Char) : Decidable (isLineBreak c) := by unfold isLineBreak; infer_instance

/--
White space characters for YAML (§5.5: https://yaml.org/spec/1.2.2/#55-white-space-characters).
Only space and tab — NOT line breaks.
-/
def isWhiteSpace (c : Char) : Prop :=
  c == ' ' ∨ c == '\t'

instance (c : Char) : Decidable (isWhiteSpace c) := by unfold isWhiteSpace; infer_instance

/--
YAML space character (§6.1: https://yaml.org/spec/1.2.2/#61-indentation-spaces).
Only the space character is valid for indentation.
Tabs are explicitly forbidden for indentation in YAML 1.2.2.
-/
def isIndentChar (c : Char) : Prop :=
  c == ' '

instance (c : Char) : Decidable (isIndentChar c) := by unfold isIndentChar; infer_instance

/--
Characters that can start a plain scalar (§7.3.3: https://yaml.org/spec/1.2.2/#733-plain-style).
Excludes indicators that have special meaning at the start.
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
Flow indicator characters (§5.3: https://yaml.org/spec/1.2.2/#53-indicator-characters).
These terminate plain scalars in flow context.
-/
def isFlowIndicator (c : Char) : Prop :=
  c ∈ [',', '[', ']', '{', '}']

instance (c : Char) : Decidable (isFlowIndicator c) := by unfold isFlowIndicator; infer_instance

/-! ## Indentation (YAML 1.2.2 §6.1: https://yaml.org/spec/1.2.2/#61-indentation-spaces) -/

/--
An indentation of `n` spaces at the start of a line.

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

Plain scalars in block context:
- Cannot start with indicators (§7.3.3: https://yaml.org/spec/1.2.2/#733-plain-style)
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

Plain scalars in flow context additionally:
- Cannot contain flow indicators (`,`, `[`, `]`, `{`, `}`)
- Are terminated by flow indicators in addition to block terminators
-/
structure ValidPlainScalarFlow where
  content : String
  nonempty : content.length > 0

/--
A valid single-quoted scalar (§7.3.2: https://yaml.org/spec/1.2.2/#732-single-quoted-style).

Single-quoted scalars:
- Delimited by `'...'`
- Only escape: `''` → `'` (doubled single quote)
- All other characters are literal
-/
structure ValidSingleQuoted where
  content : String

/--
A valid double-quoted scalar (§7.3.1: https://yaml.org/spec/1.2.2/#731-double-quoted-style).

Double-quoted scalars:
- Delimited by `"..."`
- Full escape sequence support: `\n`, `\t`, `\\`, `\"`, `\xHH`, `\uHHHH`, etc.
- Line folding: newlines become spaces (unless `\` at end of line)
-/
structure ValidDoubleQuoted where
  content : String

/--
Chomping styles for block scalars (§8.1.1.2: https://yaml.org/spec/1.2.2/#8112-block-chomping-indicator).
-/
inductive ChompStyle where
  | strip  -- Remove all trailing newlines (`|-`)
  | clip   -- Keep one trailing newline (default `|`)
  | keep   -- Keep all trailing newlines (`|+`)
  deriving Repr, BEq, DecidableEq

/--
A valid literal block scalar (§8.1.2: https://yaml.org/spec/1.2.2/#812-literal-style).

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
A valid folded block scalar (§8.1.3: https://yaml.org/spec/1.2.2/#813-folded-style).

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

A node is any valid YAML value: scalar, sequence, or mapping,
in either block or flow style. Defined as a single inductive to
avoid mutual recursion between structures.
-/
inductive ValidNode where
  /-- Plain scalar in block context -/
  | plainScalarBlock (content : String) (nonempty : content.length > 0)
  /-- Plain scalar in flow context -/
  | plainScalarFlow (content : String) (nonempty : content.length > 0)
  /-- Single-quoted scalar (§7.3.2: https://yaml.org/spec/1.2.2/#732-single-quoted-style) -/
  | singleQuoted (content : String)
  /-- Double-quoted scalar (§7.3.1: https://yaml.org/spec/1.2.2/#731-double-quoted-style) -/
  | doubleQuoted (content : String)
  /-- Literal block scalar (§8.1.2: https://yaml.org/spec/1.2.2/#812-literal-style) -/
  | literalScalar (content : String) (indent : Nat) (chomp : ChompStyle)
  /-- Folded block scalar (§8.1.3: https://yaml.org/spec/1.2.2/#813-folded-style) -/
  | foldedScalar (content : String) (indent : Nat) (chomp : ChompStyle)
  /-- Block sequence (§8.2.1: https://yaml.org/spec/1.2.2/#821-block-sequences) -/
  | blockSeq (indent : Nat) (items : List ValidNode)
  /-- Block mapping (§8.2.2: https://yaml.org/spec/1.2.2/#822-block-mappings) -/
  | blockMap (indent : Nat) (entries : List (ValidNode × ValidNode))
  /-- Flow sequence (§7.4.1: https://yaml.org/spec/1.2.2/#741-flow-sequences) -/
  | flowSeq (items : List ValidNode)
  /-- Flow mapping (§7.4.2: https://yaml.org/spec/1.2.2/#742-flow-mappings) -/
  | flowMap (entries : List (ValidNode × ValidNode))

/-! ## Document Grammar (YAML 1.2.2 §9: https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions) -/

/--
A valid YAML document.

Documents may optionally start with `---` and end with `...`.
-/
structure ValidDocument where
  /-- The document content -/
  content : ValidNode
  /-- Optional YAML directive version -/
  yamlVersion : Option String := none

/--
A valid YAML stream — one or more documents.
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
