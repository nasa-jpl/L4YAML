/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.YamlSpec

/-!
# Character Predicates (Shared Module)

Bool + Prop + iff coupling for every character/string predicate used
by both the Scanner (Bool) and the Grammar specification (Prop).

This module is the **anti-drift mechanism**: if a predicate changes in the
Bool version without a matching Prop update (or vice versa), the iff
theorem breaks → build fails → drift caught immediately.

## Naming Convention

- `xyzBool`: runtime Bool function, used by Scanner
- `xyzProp`: specification Prop, used by Grammar
- `xyz_iff`: coupling theorem `xyzBool ... = true ↔ xyzProp ...`

## Imports

This module imports only `YamlSpec` (for `@[yaml_spec]` traceability
attributes). No domain types, no Scanner, no Grammar.
-/

namespace Lean4Yaml.CharPredicates

/-! ## Helper Lemma -/

/-- Negate both sides of a Bool↔Prop correspondence. -/
theorem not_bool_iff_not {b : Bool} {p : Prop} (h : b = true ↔ p) :
    (!b) = true ↔ ¬p := by
  cases b <;> simp_all

/-- `!(b₁ && b₂) = true ↔ (b₁ = true → ¬p)` given `b₂ = true ↔ p`. -/
theorem not_and_bool_iff_imp_not {b₁ b₂ : Bool} {p : Prop}
    (h : b₂ = true ↔ p) :
    (!(b₁ && b₂)) = true ↔ (b₁ = true → ¬p) := by
  cases b₁ <;> cases b₂ <;> simp_all

/-! ## Line Break Characters

YAML 1.2.2: [24] b-line-feed, [25] b-carriage-return, [26] b-char
(§5.4, https://yaml.org/spec/1.2.2/#54-line-break-characters)
-/

/-- `[26] b-char`: line feed or carriage return (Bool). -/
@[yaml_spec "5.4" 24 "b-line-feed", yaml_spec "5.4" 25 "b-carriage-return", yaml_spec "5.4" 26 "b-char"]
def isLineBreakBool (c : Char) : Bool := c == '\n' || c == '\r'

/-- `[26] b-char`: line feed or carriage return (Prop). -/
@[yaml_spec "5.4" 24 "b-line-feed", yaml_spec "5.4" 25 "b-carriage-return", yaml_spec "5.4" 26 "b-char"]
def isLineBreakProp (c : Char) : Prop := c == '\n' ∨ c == '\r'

theorem isLineBreak_iff (c : Char) : isLineBreakBool c = true ↔ isLineBreakProp c := by
  simp only [isLineBreakBool, isLineBreakProp, Bool.or_eq_true]

instance (c : Char) : Decidable (isLineBreakProp c) := by
  unfold isLineBreakProp; infer_instance

/-! ## White Space Characters

YAML 1.2.2: [33] s-white (§5.5, https://yaml.org/spec/1.2.2/#55-white-space-characters)
-/

/-- `[33] s-white`: space or tab (Bool). -/
@[yaml_spec "5.5" 31 "s-space", yaml_spec "5.5" 32 "s-tab", yaml_spec "5.5" 33 "s-white"]
def isWhiteSpaceBool (c : Char) : Bool := c == ' ' || c == '\t'

/-- `[33] s-white`: space or tab (Prop). -/
@[yaml_spec "5.5" 31 "s-space", yaml_spec "5.5" 32 "s-tab", yaml_spec "5.5" 33 "s-white"]
def isWhiteSpaceProp (c : Char) : Prop := c == ' ' ∨ c == '\t'

theorem isWhiteSpace_iff (c : Char) : isWhiteSpaceBool c = true ↔ isWhiteSpaceProp c := by
  simp only [isWhiteSpaceBool, isWhiteSpaceProp, Bool.or_eq_true]

instance (c : Char) : Decidable (isWhiteSpaceProp c) := by
  unfold isWhiteSpaceProp; infer_instance

/-! ## Blank (White Space or Line Break) -/

/-- Blank: whitespace or line break (Bool). -/
def isBlankBool (c : Char) : Bool := isWhiteSpaceBool c || isLineBreakBool c

/-- Blank: whitespace or line break (Prop). -/
def isBlankProp (c : Char) : Prop := isWhiteSpaceProp c ∨ isLineBreakProp c

theorem isBlank_iff (c : Char) : isBlankBool c = true ↔ isBlankProp c := by
  simp only [isBlankBool, isBlankProp, Bool.or_eq_true, isWhiteSpace_iff, isLineBreak_iff]

instance (c : Char) : Decidable (isBlankProp c) := by
  unfold isBlankProp; infer_instance

/-! ## Flow Indicator Characters

YAML 1.2.2: [23] c-flow-indicator (§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters)
-/

/-- `[23] c-flow-indicator`: `,`, `[`, `]`, `{`, `}` (Bool). -/
@[yaml_spec "5.3" 7 "c-collect-entry",
  yaml_spec "5.3" 8 "c-sequence-start",
  yaml_spec "5.3" 9 "c-sequence-end",
  yaml_spec "5.3" 10 "c-mapping-start",
  yaml_spec "5.3" 11 "c-mapping-end",
  yaml_spec "5.3" 23 "c-flow-indicator"]
def isFlowIndicatorBool (c : Char) : Bool := c ∈ [',', '[', ']', '{', '}']

/-- `[23] c-flow-indicator`: `,`, `[`, `]`, `{`, `}` (Prop). -/
@[yaml_spec "5.3" 7 "c-collect-entry",
  yaml_spec "5.3" 8 "c-sequence-start",
  yaml_spec "5.3" 9 "c-sequence-end",
  yaml_spec "5.3" 10 "c-mapping-start",
  yaml_spec "5.3" 11 "c-mapping-end",
  yaml_spec "5.3" 23 "c-flow-indicator"]
def isFlowIndicatorProp (c : Char) : Prop := c ∈ [',', '[', ']', '{', '}']

theorem isFlowIndicator_iff (c : Char) :
    isFlowIndicatorBool c = true ↔ isFlowIndicatorProp c := by
  simp [isFlowIndicatorBool, isFlowIndicatorProp, List.mem_cons, Bool.or_eq_true]

instance (c : Char) : Decidable (isFlowIndicatorProp c) := by
  unfold isFlowIndicatorProp; infer_instance

/-! ## Indicator Characters

YAML 1.2.2: [22] c-indicator (§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters)
-/

/-- `[22] c-indicator`: all YAML indicator characters (Bool). -/
@[yaml_spec "5.3" 4 "c-sequence-entry",
  yaml_spec "5.3" 5 "c-mapping-key",
  yaml_spec "5.3" 6 "c-mapping-value",
  yaml_spec "5.3" 7 "c-collect-entry",
  yaml_spec "5.3" 8 "c-sequence-start",
  yaml_spec "5.3" 9 "c-sequence-end",
  yaml_spec "5.3" 10 "c-mapping-start",
  yaml_spec "5.3" 11 "c-mapping-end",
  yaml_spec "5.3" 12 "c-comment",
  yaml_spec "5.3" 13 "c-anchor",
  yaml_spec "5.3" 14 "c-alias",
  yaml_spec "5.3" 15 "c-tag",
  yaml_spec "5.3" 16 "c-literal",
  yaml_spec "5.3" 17 "c-folded",
  yaml_spec "5.3" 18 "c-single-quote",
  yaml_spec "5.3" 19 "c-double-quote",
  yaml_spec "5.3" 20 "c-directive",
  yaml_spec "5.3" 21 "c-reserved",
  yaml_spec "5.3" 22 "c-indicator"]
def isIndicatorBool (c : Char) : Bool :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
       '\'', '"', '%', '@', '`']

/-- `[22] c-indicator`: all YAML indicator characters (Prop). -/
@[yaml_spec "5.3" 4 "c-sequence-entry",
  yaml_spec "5.3" 5 "c-mapping-key",
  yaml_spec "5.3" 6 "c-mapping-value",
  yaml_spec "5.3" 7 "c-collect-entry",
  yaml_spec "5.3" 8 "c-sequence-start",
  yaml_spec "5.3" 9 "c-sequence-end",
  yaml_spec "5.3" 10 "c-mapping-start",
  yaml_spec "5.3" 11 "c-mapping-end",
  yaml_spec "5.3" 12 "c-comment",
  yaml_spec "5.3" 13 "c-anchor",
  yaml_spec "5.3" 14 "c-alias",
  yaml_spec "5.3" 15 "c-tag",
  yaml_spec "5.3" 16 "c-literal",
  yaml_spec "5.3" 17 "c-folded",
  yaml_spec "5.3" 18 "c-single-quote",
  yaml_spec "5.3" 19 "c-double-quote",
  yaml_spec "5.3" 20 "c-directive",
  yaml_spec "5.3" 21 "c-reserved",
  yaml_spec "5.3" 22 "c-indicator"]
def isIndicatorProp (c : Char) : Prop :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
       '\'', '"', '%', '@', '`']

theorem isIndicator_iff (c : Char) :
    isIndicatorBool c = true ↔ isIndicatorProp c := by
  simp [isIndicatorBool, isIndicatorProp, List.mem_cons, Bool.or_eq_true]

instance (c : Char) : Decidable (isIndicatorProp c) := by
  unfold isIndicatorProp; infer_instance

/-! ## Printable Characters

YAML 1.2.2: [1] c-printable (§5.1, https://yaml.org/spec/1.2.2/#51-character-set)
-/

/-- `[1] c-printable`: characters that can appear in a YAML stream (Prop). -/
@[yaml_spec "5.1" 1 "c-printable"]
def isPrintableProp (c : Char) : Prop :=
  c == '\t'                                    -- Tab
  ∨ (c.val ≥ 0x20 ∧ c.val ≤ 0x7E)            -- Basic ASCII printable
  ∨ c == '\u0085'                              -- Next Line
  ∨ (c.val ≥ 0xA0 ∧ c.val ≤ 0xD7FF)          -- Basic Multilingual Plane
  ∨ (c.val ≥ 0xE000 ∧ c.val ≤ 0xFFFD)        -- More BMP
  ∨ (c.val ≥ 0x10000 ∧ c.val ≤ 0x10FFFF)     -- Supplementary planes

instance (c : Char) : Decidable (isPrintableProp c) := by
  unfold isPrintableProp; infer_instance

/-- `[1] c-printable`: characters that can appear in a YAML stream (Bool). -/
@[yaml_spec "5.1" 1 "c-printable"]
def isPrintableBool (c : Char) : Bool := decide (isPrintableProp c)

theorem isPrintable_iff (c : Char) : isPrintableBool c = true ↔ isPrintableProp c := by
  simp [isPrintableBool, decide_eq_true_eq]

/-! ## JSON Characters

YAML 1.2.2: [2] nb-json (§5.1, https://yaml.org/spec/1.2.2/#51-character-set)

`nb-json` = `#x09 | [#x20-#x10FFFF]` — tab plus all non-control Unicode.
Referenced by `[107] nb-double-char` and `[118] nb-single-char`.
-/

/-- `[2] nb-json`: `#x09 | [#x20-#x10FFFF]` (Prop).
    Note: `c.val ≤ 0x10FFFF` is always true for Lean `Char`, but included
    for spec-faithful correspondence with the YAML 1.2.2 production. -/
@[yaml_spec "5.1" 2 "nb-json"]
def isNbJsonProp (c : Char) : Prop :=
  c == '\t' ∨ (c.val ≥ 0x20 ∧ c.val ≤ 0x10FFFF)

instance (c : Char) : Decidable (isNbJsonProp c) := by
  unfold isNbJsonProp; infer_instance

/-- `[2] nb-json`: `#x09 | [#x20-#x10FFFF]` (Bool). -/
@[yaml_spec "5.1" 2 "nb-json"]
def isNbJsonBool (c : Char) : Bool := decide (isNbJsonProp c)

theorem isNbJson_iff (c : Char) : isNbJsonBool c = true ↔ isNbJsonProp c := by
  simp [isNbJsonBool, decide_eq_true_eq]

/-! ## Indent Character

YAML 1.2.2: [31] s-space (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)
-/

/-- `[31] s-space`: only the space character is valid for indentation (Bool). -/
@[yaml_spec "6.1" 31 "s-space"]
def isIndentCharBool (c : Char) : Bool := c == ' '

/-- `[31] s-space`: only the space character is valid for indentation (Prop). -/
@[yaml_spec "6.1" 31 "s-space"]
def isIndentCharProp (c : Char) : Prop := c == ' '

theorem isIndentChar_iff (c : Char) :
    isIndentCharBool c = true ↔ isIndentCharProp c := by
  simp [isIndentCharBool, isIndentCharProp]

instance (c : Char) : Decidable (isIndentCharProp c) := by
  unfold isIndentCharProp; infer_instance

/-! ## Miscellaneous Character Classes

YAML 1.2.2 §5.6: [37] ns-ascii-letter, [38] ns-word-char,
[39] ns-uri-char, [40] ns-tag-char
(https://yaml.org/spec/1.2.2/#56-miscellaneous-characters)
-/

/-- `[37] ns-ascii-letter`: `[#x41-#x5A] | [#x61-#x7A]` (A-Z | a-z) (Prop). -/
@[yaml_spec "5.6" 37 "ns-ascii-letter"]
def isAsciiLetterProp (c : Char) : Prop :=
  (c.val ≥ 0x41 ∧ c.val ≤ 0x5A) ∨ (c.val ≥ 0x61 ∧ c.val ≤ 0x7A)

instance (c : Char) : Decidable (isAsciiLetterProp c) := by
  unfold isAsciiLetterProp; infer_instance

/-- `[37] ns-ascii-letter`: `[#x41-#x5A] | [#x61-#x7A]` (A-Z | a-z) (Bool). -/
@[yaml_spec "5.6" 37 "ns-ascii-letter"]
def isAsciiLetterBool (c : Char) : Bool := decide (isAsciiLetterProp c)

theorem isAsciiLetter_iff (c : Char) : isAsciiLetterBool c = true ↔ isAsciiLetterProp c := by
  simp [isAsciiLetterBool, decide_eq_true_eq]

/-- `[38] ns-word-char`: `ns-dec-digit | ns-ascii-letter | '-'` (Prop). -/
@[yaml_spec "5.6" 35 "ns-dec-digit",
  yaml_spec "5.6" 38 "ns-word-char"]
def isWordCharProp (c : Char) : Prop :=
  (c.val ≥ 0x30 ∧ c.val ≤ 0x39)  -- [35] ns-dec-digit
  ∨ isAsciiLetterProp c             -- [37] ns-ascii-letter
  ∨ c = '-'

instance (c : Char) : Decidable (isWordCharProp c) := by
  unfold isWordCharProp; infer_instance

/-- `[38] ns-word-char`: `ns-dec-digit | ns-ascii-letter | '-'` (Bool). -/
@[yaml_spec "5.6" 35 "ns-dec-digit",
  yaml_spec "5.6" 38 "ns-word-char"]
def isWordCharBool (c : Char) : Bool := decide (isWordCharProp c)

theorem isWordChar_iff (c : Char) : isWordCharBool c = true ↔ isWordCharProp c := by
  simp [isWordCharBool, decide_eq_true_eq]

/-- `[39] ns-uri-char`: word-char plus URI-special characters and `%` (Prop).

    The spec production `'%' ns-hex-digit ns-hex-digit` is a multi-character
    sequence; at the single-character level we accept `%` and leave hex-digit
    validation to the enclosing loop. -/
@[yaml_spec "5.6" 39 "ns-uri-char"]
def isUriCharProp (c : Char) : Prop :=
  isWordCharProp c
  ∨ c ∈ ['%', '#', ';', '/', '?', ':', '@', '&', '=', '+', '$', ',',
          '_', '.', '!', '~', '*', '\'', '(', ')']

instance (c : Char) : Decidable (isUriCharProp c) := by
  unfold isUriCharProp; infer_instance

/-- `[39] ns-uri-char`: word-char plus URI-special characters and `%` (Bool). -/
@[yaml_spec "5.6" 39 "ns-uri-char"]
def isUriCharBool (c : Char) : Bool := decide (isUriCharProp c)

theorem isUriChar_iff (c : Char) : isUriCharBool c = true ↔ isUriCharProp c := by
  simp [isUriCharBool, decide_eq_true_eq]

/-- `[40] ns-tag-char`: `ns-uri-char - '!' - c-flow-indicator` (Prop). -/
@[yaml_spec "5.6" 40 "ns-tag-char"]
def isTagCharProp (c : Char) : Prop :=
  isUriCharProp c ∧ c ≠ '!' ∧ ¬isFlowIndicatorProp c

instance (c : Char) : Decidable (isTagCharProp c) := by
  unfold isTagCharProp; infer_instance

/-- `[40] ns-tag-char`: `ns-uri-char - '!' - c-flow-indicator` (Bool). -/
@[yaml_spec "5.6" 40 "ns-tag-char"]
def isTagCharBool (c : Char) : Bool := decide (isTagCharProp c)

theorem isTagChar_iff (c : Char) : isTagCharBool c = true ↔ isTagCharProp c := by
  simp [isTagCharBool, decide_eq_true_eq]

/-! ## Plain Scalar First Character

YAML 1.2.2: [126] ns-plain-first(c) (§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style)

3-argument version matching the full YAML spec: `-`, `?`, `:` are allowed
when followed by a safe character (non-blank, and in flow context additionally
non-flow-indicator).
-/

/-- `[126] ns-plain-first(c)`: can character start a plain scalar? (Bool). -/
@[yaml_spec "7.3.3" 126 "ns-plain-first"]
def canStartPlainScalarBool (c : Char) (next : Option Char) (inFlow : Bool) : Bool :=
  if c = '-' ∨ c = '?' ∨ c = ':' then
    match next with
    | some n => !isWhiteSpaceBool n && !isLineBreakBool n && !(inFlow && isFlowIndicatorBool n)
    | none => false
  else
    !isIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c

/-- `[126] ns-plain-first(c)`: can character start a plain scalar? (Prop). -/
@[yaml_spec "7.3.3" 126 "ns-plain-first"]
def canStartPlainScalarProp (c : Char) (next : Option Char) (inFlow : Bool) : Prop :=
  if c = '-' ∨ c = '?' ∨ c = ':' then
    match next with
    | some n => ¬isWhiteSpaceProp n ∧ ¬isLineBreakProp n
                ∧ (inFlow = true → ¬isFlowIndicatorProp n)
    | none => False
  else
    ¬isIndicatorProp c ∧ ¬isWhiteSpaceProp c ∧ ¬isLineBreakProp c

instance (c : Char) (next : Option Char) (inFlow : Bool) :
    Decidable (canStartPlainScalarProp c next inFlow) := by
  unfold canStartPlainScalarProp
  split
  · cases next with
    | none => exact instDecidableFalse
    | some n => infer_instance
  · infer_instance

theorem canStartPlainScalar_iff (c : Char) (next : Option Char) (inFlow : Bool) :
    canStartPlainScalarBool c next inFlow = true ↔
    canStartPlainScalarProp c next inFlow := by
  simp only [canStartPlainScalarBool, canStartPlainScalarProp]
  split
  · -- exception branch: c is -, ?, or :
    cases next with
    | none => simp
    | some n =>
      simp only [Bool.and_eq_true,
        not_bool_iff_not (isWhiteSpace_iff n),
        not_bool_iff_not (isLineBreak_iff n)]
      constructor
      · rintro ⟨⟨h1, h2⟩, h3⟩
        exact ⟨h1, h2, (not_and_bool_iff_imp_not (isFlowIndicator_iff n)).mp h3⟩
      · rintro ⟨h1, h2, h3⟩
        exact ⟨⟨h1, h2⟩, (not_and_bool_iff_imp_not (isFlowIndicator_iff n)).mpr h3⟩
  · -- regular branch
    simp only [Bool.and_eq_true,
      not_bool_iff_not (isIndicator_iff c),
      not_bool_iff_not (isWhiteSpace_iff c),
      not_bool_iff_not (isLineBreak_iff c)]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩,
           fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩

/-! ## Plain Safe Character

YAML 1.2.2: [127] ns-plain-safe(c) (§7.3.3)

In block context: not whitespace, not line break.
In flow context: additionally not a flow indicator.
-/

/-- `[127] ns-plain-safe(c)`: safe continuation character for plain scalars (Bool). -/
@[yaml_spec "7.3.3" 127 "ns-plain-safe",
  yaml_spec "7.3.3" 128 "ns-plain-safe-out",
  yaml_spec "7.3.3" 129 "ns-plain-safe-in"]
def isPlainSafeBool (c : Char) (inFlow : Bool) : Bool :=
  if inFlow then
    !isWhiteSpaceBool c && !isLineBreakBool c && !isFlowIndicatorBool c
  else
    !isWhiteSpaceBool c && !isLineBreakBool c

/-- `[127] ns-plain-safe(c)`: safe continuation character for plain scalars (Prop). -/
@[yaml_spec "7.3.3" 127 "ns-plain-safe",
  yaml_spec "7.3.3" 128 "ns-plain-safe-out",
  yaml_spec "7.3.3" 129 "ns-plain-safe-in"]
def isPlainSafeProp (c : Char) (inFlow : Bool) : Prop :=
  if inFlow then
    ¬isWhiteSpaceProp c ∧ ¬isLineBreakProp c ∧ ¬isFlowIndicatorProp c
  else
    ¬isWhiteSpaceProp c ∧ ¬isLineBreakProp c

instance (c : Char) (inFlow : Bool) : Decidable (isPlainSafeProp c inFlow) := by
  unfold isPlainSafeProp; infer_instance

theorem isPlainSafe_iff (c : Char) (inFlow : Bool) :
    isPlainSafeBool c inFlow = true ↔ isPlainSafeProp c inFlow := by
  simp only [isPlainSafeBool, isPlainSafeProp]
  split
  · -- flow context
    simp only [Bool.and_eq_true,
      not_bool_iff_not (isWhiteSpace_iff c),
      not_bool_iff_not (isLineBreak_iff c),
      not_bool_iff_not (isFlowIndicator_iff c)]
    exact ⟨fun ⟨⟨h1, h2⟩, h3⟩ => ⟨h1, h2, h3⟩,
           fun ⟨h1, h2, h3⟩ => ⟨⟨h1, h2⟩, h3⟩⟩
  · -- block context
    simp only [Bool.and_eq_true,
      not_bool_iff_not (isWhiteSpace_iff c),
      not_bool_iff_not (isLineBreak_iff c)]

/-! ## Valid Plain First (String-Level)

YAML 1.2.2: [126] ns-plain-first(c) applied to the first character(s) of
a string. 2-argument version with flow context.
-/

/-- First character(s) can start a plain scalar (Bool).

    **YAML 1.2.2 §7.3.3 [126]**: Exception chars (`-`, `?`, `:`) require a
    following `ns-plain-safe` character in the INPUT context. When the content
    is a single exception char (the safe char was consumed by a terminator),
    the scanner already validated the input context, so we accept it. -/
@[yaml_spec "7.3.3" 126 "ns-plain-first"]
def validPlainFirstBool (content : String) (inFlow : Bool) : Bool :=
  match content.toList with
  | c :: n :: _ => canStartPlainScalarBool c (some n) inFlow
  | [c] => if c = '-' ∨ c = '?' ∨ c = ':' then true
            else canStartPlainScalarBool c none inFlow
  | [] => true

/-- First character(s) can start a plain scalar (Prop).

    **YAML 1.2.2 §7.3.3 [126]**: Exception chars (`-`, `?`, `:`) require a
    following `ns-plain-safe` character in the INPUT context. When the content
    is a single exception char (the safe char was consumed by a terminator),
    the scanner already validated the input context, so we accept it. -/
@[yaml_spec "7.3.3" 126 "ns-plain-first"]
def validPlainFirstProp (content : String) (inFlow : Bool) : Prop :=
  match content.toList with
  | c :: n :: _ => canStartPlainScalarProp c (some n) inFlow
  | [c] => if c = '-' ∨ c = '?' ∨ c = ':' then True
            else canStartPlainScalarProp c none inFlow
  | [] => True

instance (content : String) (inFlow : Bool) : Decidable (validPlainFirstProp content inFlow) := by
  unfold validPlainFirstProp
  cases content.toList with
  | nil => exact .isTrue trivial
  | cons c rest =>
    cases rest with
    | nil => exact inferInstance
    | cons n _ => exact inferInstance

theorem validPlainFirst_iff (content : String) (inFlow : Bool) :
    validPlainFirstBool content inFlow = true ↔ validPlainFirstProp content inFlow := by
  unfold validPlainFirstBool validPlainFirstProp
  split
  · exact canStartPlainScalar_iff _ _ _
  · split <;> simp_all [canStartPlainScalar_iff]
  · simp

/-! ## Adjacent Characters Helper

Used by `noColonSpace` and `noSpaceHash` to check for forbidden adjacent
character pairs in plain scalar content.
-/

/-- Check if a list contains adjacent characters `a` then `b`. -/
def hasAdjacentChars (a b : Char) : List Char → Bool
  | c₁ :: c₂ :: rest => (c₁ == a && c₂ == b) || hasAdjacentChars a b (c₂ :: rest)
  | _ => false

theorem hasAdjacentChars_true_implies (a b : Char) (cs : List Char)
    (h : hasAdjacentChars a b cs = true) :
    ∃ i, cs[i]? = some a ∧ cs[i + 1]? = some b := by
  induction cs with
  | nil => simp [hasAdjacentChars] at h
  | cons c₁ rest ih =>
    match rest, ih with
    | [], _ => simp [hasAdjacentChars] at h
    | c₂ :: rest', ih =>
      simp [hasAdjacentChars] at h
      cases h with
      | inl h =>
        obtain ⟨h₁, h₂⟩ := h
        subst h₁; subst h₂
        exact ⟨0, by simp, by simp⟩
      | inr h =>
        have ⟨i, hi₁, hi₂⟩ := ih h
        exact ⟨i + 1, by simp [hi₁], by simp [hi₂]⟩

theorem hasAdjacentChars_true_of (a b : Char) (cs : List Char)
    (h : ∃ i, cs[i]? = some a ∧ cs[i + 1]? = some b) :
    hasAdjacentChars a b cs = true := by
  induction cs with
  | nil => obtain ⟨i, h₁, _⟩ := h; simp at h₁
  | cons c₁ rest ih =>
    match rest with
    | [] =>
      obtain ⟨i, h₁, h₂⟩ := h
      cases i with
      | zero => simp at h₂
      | succ j => simp at h₁
    | c₂ :: rest' =>
      obtain ⟨i, h₁, h₂⟩ := h
      simp [hasAdjacentChars]
      cases i with
      | zero =>
        left
        simp at h₁ h₂
        exact ⟨h₁, h₂⟩
      | succ j =>
        right
        simp at h₁ h₂
        exact ih ⟨j, h₁, h₂⟩

theorem hasAdjacentChars_iff (a b : Char) (cs : List Char) :
    hasAdjacentChars a b cs = true ↔ ∃ i, cs[i]? = some a ∧ cs[i + 1]? = some b :=
  ⟨hasAdjacentChars_true_implies a b cs, hasAdjacentChars_true_of a b cs⟩

/-! ## Adjacent Characters: Append Decomposition

Lemmas for reasoning about `hasAdjacentChars` over concatenated and
extended lists. These underpin the `noColonSpace` and `noSpaceHash`
preservation lemmas needed for B3.
-/

/-- `hasAdjacentChars` is false on a singleton list. -/
theorem hasAdjacentChars_singleton (a b : Char) (c : Char) :
    hasAdjacentChars a b [c] = false := by
  rfl

/-- Pushing a character: `hasAdjacentChars a b (xs ++ [c])` iff it already
    holds in `xs`, or the last char of `xs` is `a` and `c` is `b`. -/
theorem hasAdjacentChars_append_singleton (a b : Char) (xs : List Char) (c : Char) :
    hasAdjacentChars a b (xs ++ [c]) = true ↔
    hasAdjacentChars a b xs = true ∨ (xs.getLast? = some a ∧ c = b) := by
  induction xs with
  | nil => simp [hasAdjacentChars]
  | cons x₁ rest ih =>
    match rest with
    | [] =>
      simp [hasAdjacentChars, List.getLast?, beq_iff_eq]
    | x₂ :: rest' =>
      simp only [List.cons_append, hasAdjacentChars, Bool.or_eq_true,
                  List.getLast?_cons_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · rcases ih.mp h with h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr h'
      · rintro (h | h)
        · rcases h with h | h
          · exact Or.inl h
          · exact Or.inr (ih.mpr (Or.inl h))
        · exact Or.inr (ih.mpr (Or.inr h))

/-- Negative form: no adjacent `a b` in `xs ++ [c]` iff no adjacent `a b`
    in `xs` AND NOT (last of xs is `a` and `c` is `b`). -/
theorem not_hasAdjacentChars_append_singleton (a b : Char) (xs : List Char) (c : Char) :
    hasAdjacentChars a b (xs ++ [c]) = false ↔
    hasAdjacentChars a b xs = false ∧ ¬(xs.getLast? = some a ∧ c = b) := by
  rw [Bool.eq_false_iff, Bool.eq_false_iff]
  constructor
  · intro h
    exact ⟨fun h1 => h ((hasAdjacentChars_append_singleton a b xs c).mpr (Or.inl h1)),
           fun h2 => h ((hasAdjacentChars_append_singleton a b xs c).mpr (Or.inr h2))⟩
  · rintro ⟨h1, h2⟩ h3
    rcases (hasAdjacentChars_append_singleton a b xs c).mp h3 with h | h
    · exact h1 h
    · exact h2 h

/-- `hasAdjacentChars` over concatenation: holds iff it holds in the left part,
    the right part, or across the boundary (last of left = a, first of right = b). -/
theorem hasAdjacentChars_append (a b : Char) (xs ys : List Char) :
    hasAdjacentChars a b (xs ++ ys) = true ↔
    hasAdjacentChars a b xs = true ∨ hasAdjacentChars a b ys = true
    ∨ (xs.getLast? = some a ∧ ys.head? = some b) := by
  induction xs with
  | nil => simp [hasAdjacentChars]
  | cons x₁ rest ih =>
    match rest with
    | [] =>
      simp only [List.cons_append, List.getLast?_singleton, List.nil_append]
      cases ys with
      | nil => simp [hasAdjacentChars]
      | cons y₁ ys' =>
        simp only [hasAdjacentChars, Bool.or_eq_true, List.head?_cons]
        constructor
        · rintro (h | h)
          · obtain ⟨h1, h2⟩ := Bool.and_eq_true_iff.mp h
            rw [beq_iff_eq] at h1 h2
            exact Or.inr (Or.inr ⟨by rw [h1], by rw [h2]⟩)
          · exact Or.inr (Or.inl h)
        · rintro (h | h | h)
          · simp at h
          · exact Or.inr h
          · obtain ⟨h1, h2⟩ := h
            left
            rw [Bool.and_eq_true_iff, beq_iff_eq, beq_iff_eq]
            exact ⟨Option.some.inj h1, Option.some.inj h2⟩
    | x₂ :: rest' =>
      simp only [List.cons_append, hasAdjacentChars, Bool.or_eq_true,
                  List.getLast?_cons_cons]
      constructor
      · rintro (h | h)
        · exact Or.inl (Or.inl h)
        · rcases ih.mp h with h' | h' | h'
          · exact Or.inl (Or.inr h')
          · exact Or.inr (Or.inl h')
          · exact Or.inr (Or.inr h')
      · rintro ((h | h) | (h | h))
        · exact Or.inl h
        · exact Or.inr (ih.mpr (Or.inl h))
        · exact Or.inr (ih.mpr (Or.inr (Or.inl h)))
        · exact Or.inr (ih.mpr (Or.inr (Or.inr h)))

/-! ## No Colon-Space

YAML 1.2.2: [130] ns-plain-char(c) (§7.3.3) — colon may appear in a
plain scalar only when NOT followed by an `s-white` character.
-/

/-- Content does not contain `: ` (Bool). -/
@[yaml_spec "7.3.3" 130 "ns-plain-char"]
def noColonSpaceBool (content : String) : Bool :=
  !hasAdjacentChars ':' ' ' content.toList

/-- Content does not contain `: ` (Prop). -/
@[yaml_spec "7.3.3" 130 "ns-plain-char"]
def noColonSpaceProp (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ':' ∧ content.toList[i + 1]? = some ' '

instance (content : String) : Decidable (noColonSpaceProp content) :=
  match h : hasAdjacentChars ':' ' ' content.toList with
  | false => .isTrue (fun hex =>
      absurd ((hasAdjacentChars_iff ':' ' ' content.toList).mpr hex) (by simp [h]))
  | true => .isFalse (fun hn =>
      absurd ((hasAdjacentChars_iff ':' ' ' content.toList).mp h) hn)

theorem noColonSpace_iff (content : String) :
    noColonSpaceBool content = true ↔ noColonSpaceProp content :=
  not_bool_iff_not (hasAdjacentChars_iff ':' ' ' content.toList)

/-! ## No Space-Hash

YAML 1.2.2: [130] ns-plain-char(c) (§7.3.3) — `#` may appear in a
plain scalar only when NOT preceded by an `s-white` character.
-/

/-- Content does not contain ` #` (Bool). -/
@[yaml_spec "7.3.3" 130 "ns-plain-char"]
def noSpaceHashBool (content : String) : Bool :=
  !hasAdjacentChars ' ' '#' content.toList

/-- Content does not contain ` #` (Prop). -/
@[yaml_spec "7.3.3" 130 "ns-plain-char"]
def noSpaceHashProp (content : String) : Prop :=
  ¬ ∃ i, content.toList[i]? = some ' ' ∧ content.toList[i + 1]? = some '#'

instance (content : String) : Decidable (noSpaceHashProp content) :=
  match h : hasAdjacentChars ' ' '#' content.toList with
  | false => .isTrue (fun hex =>
      absurd ((hasAdjacentChars_iff ' ' '#' content.toList).mpr hex) (by simp [h]))
  | true => .isFalse (fun hn =>
      absurd ((hasAdjacentChars_iff ' ' '#' content.toList).mp h) hn)

theorem noSpaceHash_iff (content : String) :
    noSpaceHashBool content = true ↔ noSpaceHashProp content :=
  not_bool_iff_not (hasAdjacentChars_iff ' ' '#' content.toList)

/-! ## No Flow Indicators

YAML 1.2.2: [127] ns-plain-safe(FLOW-IN) (§7.3.3) — in flow context,
plain scalars additionally cannot contain flow indicator characters.
-/

/-- Content contains no flow indicators (Bool). -/
@[yaml_spec "7.3.3" 127 "ns-plain-safe"]
def noFlowIndicatorsBool (content : String) : Bool :=
  content.toList.all (fun c => !isFlowIndicatorBool c)

/-- Content contains no flow indicators (Prop). -/
@[yaml_spec "7.3.3" 127 "ns-plain-safe"]
def noFlowIndicatorsProp (content : String) : Prop :=
  ∀ c ∈ content.toList, ¬isFlowIndicatorProp c

instance (content : String) : Decidable (noFlowIndicatorsProp content) := by
  unfold noFlowIndicatorsProp
  exact List.decidableBAll _ content.toList

theorem noFlowIndicators_iff (content : String) :
    noFlowIndicatorsBool content = true ↔ noFlowIndicatorsProp content := by
  constructor
  · intro h c hc hfi
    simp only [noFlowIndicatorsBool, List.all_eq_true] at h
    have hval := h c hc
    have := (not_bool_iff_not (isFlowIndicator_iff c)).mp hval
    exact this hfi
  · intro h
    simp only [noFlowIndicatorsBool, List.all_eq_true]
    intro c hc
    exact (not_bool_iff_not (isFlowIndicator_iff c)).mpr (h c hc)

/-! ## String Property Preservation Lemmas (B3.0)

Append/push/prefix preservation for `noColonSpace`, `noSpaceHash`,
`noFlowIndicators`, and `validPlainFirst`. These are the building blocks
for the `PlainContentInv` loop invariant in Phase B3.3.
-/

/-! ### noColonSpace preservation -/

/-- `noColonSpace` for the empty string. -/
theorem noColonSpaceProp_empty : noColonSpaceProp "" := by
  intro ⟨i, h1, _⟩; simp at h1

/-- Pushing a character preserves `noColonSpace` when the push doesn't
    introduce a `: ` pair at the boundary. -/
theorem noColonSpaceProp_push (content : String) (c : Char)
    (h : noColonSpaceProp content)
    (h_boundary : ¬(content.toList.getLast? = some ':' ∧ c = ' ')) :
    noColonSpaceProp (content.push c) := by
  rw [noColonSpaceProp] at h ⊢
  rw [String.toList_push]
  intro ⟨i, h1, h2⟩
  have := (hasAdjacentChars_append_singleton ':' ' ' content.toList c).mpr
  have h_adj : hasAdjacentChars ':' ' ' (content.toList ++ [c]) = true :=
    (hasAdjacentChars_iff ':' ' ' (content.toList ++ [c])).mpr ⟨i, h1, h2⟩
  rcases (hasAdjacentChars_append_singleton ':' ' ' content.toList c).mp h_adj with h' | h'
  · exact h ((hasAdjacentChars_iff ':' ' ' content.toList).mp h')
  · exact h_boundary h'

/-- Appending two strings preserves `noColonSpace` when both parts are
    clean and the boundary is safe. -/
theorem noColonSpaceProp_append (s t : String)
    (hs : noColonSpaceProp s) (ht : noColonSpaceProp t)
    (h_boundary : ¬(s.toList.getLast? = some ':' ∧ t.toList.head? = some ' ')) :
    noColonSpaceProp (s ++ t) := by
  rw [noColonSpaceProp] at hs ht ⊢
  simp only [String.toList_append]
  intro ⟨i, h1, h2⟩
  have h_adj := (hasAdjacentChars_iff ':' ' ' (s.toList ++ t.toList)).mpr ⟨i, h1, h2⟩
  rcases (hasAdjacentChars_append ':' ' ' s.toList t.toList).mp h_adj with h | h | h
  · exact hs ((hasAdjacentChars_iff ':' ' ' s.toList).mp h)
  · exact ht ((hasAdjacentChars_iff ':' ' ' t.toList).mp h)
  · exact h_boundary h

/-! ### noSpaceHash preservation -/

/-- `noSpaceHash` for the empty string. -/
theorem noSpaceHashProp_empty : noSpaceHashProp "" := by
  intro ⟨i, h1, _⟩; simp at h1

/-- Pushing a character preserves `noSpaceHash` when the push doesn't
    introduce a ` #` pair at the boundary. -/
theorem noSpaceHashProp_push (content : String) (c : Char)
    (h : noSpaceHashProp content)
    (h_boundary : ¬(content.toList.getLast? = some ' ' ∧ c = '#')) :
    noSpaceHashProp (content.push c) := by
  rw [noSpaceHashProp] at h ⊢
  rw [String.toList_push]
  intro ⟨i, h1, h2⟩
  have h_adj := (hasAdjacentChars_iff ' ' '#' (content.toList ++ [c])).mpr ⟨i, h1, h2⟩
  rcases (hasAdjacentChars_append_singleton ' ' '#' content.toList c).mp h_adj with h' | h'
  · exact h ((hasAdjacentChars_iff ' ' '#' content.toList).mp h')
  · exact h_boundary h'

/-- Appending two strings preserves `noSpaceHash` when both parts are
    clean and the boundary is safe. -/
theorem noSpaceHashProp_append (s t : String)
    (hs : noSpaceHashProp s) (ht : noSpaceHashProp t)
    (h_boundary : ¬(s.toList.getLast? = some ' ' ∧ t.toList.head? = some '#')) :
    noSpaceHashProp (s ++ t) := by
  rw [noSpaceHashProp] at hs ht ⊢
  simp only [String.toList_append]
  intro ⟨i, h1, h2⟩
  have h_adj := (hasAdjacentChars_iff ' ' '#' (s.toList ++ t.toList)).mpr ⟨i, h1, h2⟩
  rcases (hasAdjacentChars_append ' ' '#' s.toList t.toList).mp h_adj with h | h | h
  · exact hs ((hasAdjacentChars_iff ' ' '#' s.toList).mp h)
  · exact ht ((hasAdjacentChars_iff ' ' '#' t.toList).mp h)
  · exact h_boundary h

/-! ### noFlowIndicators preservation -/

/-- `noFlowIndicators` for the empty string. -/
theorem noFlowIndicatorsProp_empty : noFlowIndicatorsProp "" := by
  intro c hc; simp at hc

/-- Pushing a non-flow-indicator character preserves `noFlowIndicators`. -/
theorem noFlowIndicatorsProp_push (content : String) (c : Char)
    (h : noFlowIndicatorsProp content)
    (hc : ¬isFlowIndicatorProp c) :
    noFlowIndicatorsProp (content.push c) := by
  intro x hx
  rw [String.toList_push] at hx
  rcases List.mem_append.mp hx with hx' | hx'
  · exact h x hx'
  · simp at hx'; rw [hx']; exact hc

/-- Appending preserves `noFlowIndicators` when both parts are clean. -/
theorem noFlowIndicatorsProp_append (s t : String)
    (hs : noFlowIndicatorsProp s) (ht : noFlowIndicatorsProp t) :
    noFlowIndicatorsProp (s ++ t) := by
  intro c hc
  simp only [String.toList_append] at hc
  rcases List.mem_append.mp hc with hc' | hc'
  · exact hs c hc'
  · exact ht c hc'

/-! ### validPlainFirst preservation -/

/-- `validPlainFirst` is vacuously true for the empty string. -/
theorem validPlainFirstProp_empty (inFlow : Bool) :
    validPlainFirstProp "" inFlow := by
  simp [validPlainFirstProp]

/-- `validPlainFirst` depends only on the first 1–2 characters.
    Pushing a character onto a string with ≥2 characters preserves it. -/
theorem validPlainFirstProp_push_of_nonempty (content : String) (c : Char)
    (inFlow : Bool) (h : validPlainFirstProp content inFlow)
    (hlen : ∃ x y rest, content.toList = x :: y :: rest) :
    validPlainFirstProp (content.push c) inFlow := by
  obtain ⟨x, y, rest, hxs⟩ := hlen
  simp only [validPlainFirstProp, String.toList_push, hxs, List.cons_append] at h ⊢
  exact h

/-- `validPlainFirst` for appending to a string with ≥2 characters. -/
theorem validPlainFirstProp_append_of_nonempty (s t : String)
    (inFlow : Bool) (h : validPlainFirstProp s inFlow)
    (hlen : ∃ x y rest, s.toList = x :: y :: rest) :
    validPlainFirstProp (s ++ t) inFlow := by
  obtain ⟨x, y, rest, hxs⟩ := hlen
  simp only [validPlainFirstProp, String.toList_append, hxs, List.cons_append] at h ⊢
  exact h

/-! ### Boundary helpers for scanner loop proofs -/

/-- Extract list membership from a `getElem?` hit. -/
theorem mem_of_getElemQ_some {l : List Char} {a : Char} {i : Nat}
    (h : l[i]? = some a) : a ∈ l := by
  induction l generalizing i with
  | nil => exact absurd h (by simp)
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h; exact List.mem_cons_self
    | succ n =>
      have : xs[n]? = some a := by simpa using h
      exact List.mem_cons_of_mem x (ih this)

/-- A non-whitespace, non-line-break character is not ' '. -/
theorem not_space_of_plainSafe (c : Char) (inFlow : Bool)
    (h : isPlainSafeProp c inFlow) : c ≠ ' ' := by
  intro heq; rw [heq] at h
  simp [isPlainSafeProp, isWhiteSpaceProp] at h

/-- Whitespace chars have `getLast? = some ' '` or `some '\t'`. -/
theorem whitespace_getLast?_cases (spaces : String)
    (h : ∀ c ∈ spaces.toList, isWhiteSpaceProp c) (hne : spaces.toList ≠ []) :
    spaces.toList.getLast? = some ' ' ∨ spaces.toList.getLast? = some '\t' := by
  have hLast := List.getLast?_eq_some_getLast hne
  rw [hLast]
  have hMem := List.getLast_mem hne
  have hws := h _ hMem
  simp only [isWhiteSpaceProp, beq_iff_eq] at hws
  rcases hws with h1 | h1 <;> simp [h1]

/-- A string of pure whitespace has no colon-space pattern. -/
theorem noColonSpaceProp_of_whitespace (s : String)
    (h : ∀ c ∈ s.toList, isWhiteSpaceProp c) : noColonSpaceProp s := by
  intro ⟨i, h1, _⟩
  have hMem := mem_of_getElemQ_some h1
  have hws := h ':' hMem
  simp [isWhiteSpaceProp] at hws

/-- A string of pure whitespace has no space-hash pattern. -/
theorem noSpaceHashProp_of_whitespace (s : String)
    (h : ∀ c ∈ s.toList, isWhiteSpaceProp c) : noSpaceHashProp s := by
  intro ⟨i, _, h2⟩
  have hMem := mem_of_getElemQ_some h2
  have hws := h '#' hMem
  simp [isWhiteSpaceProp] at hws

/-- A string of pure whitespace has no flow indicators. -/
theorem noFlowIndicatorsProp_of_whitespace (s : String)
    (h : ∀ c ∈ s.toList, isWhiteSpaceProp c) : noFlowIndicatorsProp s := by
  intro c hc hfi
  have := h c hc
  simp only [isWhiteSpaceProp, beq_iff_eq] at this
  rcases this with rfl | rfl <;> simp [isFlowIndicatorProp] at hfi

end Lean4Yaml.CharPredicates
