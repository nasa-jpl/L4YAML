/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Spec.YamlSpec

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

namespace L4YAML.CharPredicates

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

Each production is its own function for spec traceability: `b-char` is
defined as the disjunction `b-line-feed | b-carriage-return`, mirroring
the grammar.
-/

/-- `[24] b-line-feed ::= #xA`: the line-feed character (Bool). -/
@[yaml_spec "5.4" 24 "b-line-feed"]
def isLineFeedBool (c : Char) : Bool := c == '\n'

/-- `[24] b-line-feed ::= #xA`: the line-feed character (Prop). -/
@[yaml_spec "5.4" 24 "b-line-feed"]
def isLineFeedProp (c : Char) : Prop := c == '\n'

theorem isLineFeed_iff (c : Char) : isLineFeedBool c = true ↔ isLineFeedProp c := by
  simp [isLineFeedBool, isLineFeedProp]

instance (c : Char) : Decidable (isLineFeedProp c) := by
  unfold isLineFeedProp; infer_instance

/-- `[25] b-carriage-return ::= #xD`: the carriage-return character (Bool). -/
@[yaml_spec "5.4" 25 "b-carriage-return"]
def isCarriageReturnBool (c : Char) : Bool := c == '\r'

/-- `[25] b-carriage-return ::= #xD`: the carriage-return character (Prop). -/
@[yaml_spec "5.4" 25 "b-carriage-return"]
def isCarriageReturnProp (c : Char) : Prop := c == '\r'

theorem isCarriageReturn_iff (c : Char) :
    isCarriageReturnBool c = true ↔ isCarriageReturnProp c := by
  simp [isCarriageReturnBool, isCarriageReturnProp]

instance (c : Char) : Decidable (isCarriageReturnProp c) := by
  unfold isCarriageReturnProp; infer_instance

/-- `[26] b-char ::= b-line-feed | b-carriage-return` (Bool). -/
@[yaml_spec "5.4" 26 "b-char"]
def isLineBreakBool (c : Char) : Bool := isLineFeedBool c || isCarriageReturnBool c

/-- `[26] b-char ::= b-line-feed | b-carriage-return` (Prop). -/
@[yaml_spec "5.4" 26 "b-char"]
def isLineBreakProp (c : Char) : Prop := isLineFeedProp c ∨ isCarriageReturnProp c

theorem isLineBreak_iff (c : Char) : isLineBreakBool c = true ↔ isLineBreakProp c := by
  simp only [isLineBreakBool, isLineBreakProp, Bool.or_eq_true,
             isLineFeed_iff, isCarriageReturn_iff]

instance (c : Char) : Decidable (isLineBreakProp c) := by
  unfold isLineBreakProp; infer_instance

/-! ## White Space Characters

YAML 1.2.2: [31] s-space, [32] s-tab, [33] s-white
(§5.5, https://yaml.org/spec/1.2.2/#55-white-space-characters)

Each production is its own function for spec traceability: `s-white` is
defined as the disjunction `s-space | s-tab`, mirroring the grammar.
-/

/-- `[31] s-space ::= #x20`: the space character (Bool). -/
@[yaml_spec "5.5" 31 "s-space"]
def isSpaceBool (c : Char) : Bool := c == ' '

/-- `[31] s-space ::= #x20`: the space character (Prop). -/
@[yaml_spec "5.5" 31 "s-space"]
def isSpaceProp (c : Char) : Prop := c == ' '

theorem isSpace_iff (c : Char) : isSpaceBool c = true ↔ isSpaceProp c := by
  simp [isSpaceBool, isSpaceProp]

instance (c : Char) : Decidable (isSpaceProp c) := by
  unfold isSpaceProp; infer_instance

/-- `[32] s-tab ::= #x9`: the tab character (Bool). -/
@[yaml_spec "5.5" 32 "s-tab"]
def isTabBool (c : Char) : Bool := c == '\t'

/-- `[32] s-tab ::= #x9`: the tab character (Prop). -/
@[yaml_spec "5.5" 32 "s-tab"]
def isTabProp (c : Char) : Prop := c == '\t'

theorem isTab_iff (c : Char) : isTabBool c = true ↔ isTabProp c := by
  simp [isTabBool, isTabProp]

instance (c : Char) : Decidable (isTabProp c) := by
  unfold isTabProp; infer_instance

/-- `[33] s-white ::= s-space | s-tab` (Bool). -/
@[yaml_spec "5.5" 33 "s-white"]
def isWhiteSpaceBool (c : Char) : Bool := isSpaceBool c || isTabBool c

/-- `[33] s-white ::= s-space | s-tab` (Prop). -/
@[yaml_spec "5.5" 33 "s-white"]
def isWhiteSpaceProp (c : Char) : Prop := isSpaceProp c ∨ isTabProp c

theorem isWhiteSpace_iff (c : Char) : isWhiteSpaceBool c = true ↔ isWhiteSpaceProp c := by
  simp only [isWhiteSpaceBool, isWhiteSpaceProp, Bool.or_eq_true, isSpace_iff, isTab_iff]

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

/-! ## Individual Indicator Characters

YAML 1.2.2 §5.3 — single-character indicators with their own productions.
Each predicate tests a single role and carries the corresponding
`@[yaml_spec]` traceability annotation, so the scanner never compares
against a bare char literal except inside these definitions.
(§5.3, https://yaml.org/spec/1.2.2/#53-indicator-characters)
-/

/-- `[4] c-sequence-entry ::= "-"` (Bool). -/
@[yaml_spec "5.3" 4 "c-sequence-entry"]
def isSequenceEntryBool (c : Char) : Bool := c == '-'

/-- `[4] c-sequence-entry ::= "-"` (Prop). -/
@[yaml_spec "5.3" 4 "c-sequence-entry"]
def isSequenceEntryProp (c : Char) : Prop := c == '-'

theorem isSequenceEntry_iff (c : Char) :
    isSequenceEntryBool c = true ↔ isSequenceEntryProp c := by
  simp [isSequenceEntryBool, isSequenceEntryProp]

instance (c : Char) : Decidable (isSequenceEntryProp c) := by
  unfold isSequenceEntryProp; infer_instance

/-- `[6] c-mapping-value ::= ":"` (Bool). -/
@[yaml_spec "5.3" 6 "c-mapping-value"]
def isMappingValueBool (c : Char) : Bool := c == ':'

/-- `[6] c-mapping-value ::= ":"` (Prop). -/
@[yaml_spec "5.3" 6 "c-mapping-value"]
def isMappingValueProp (c : Char) : Prop := c == ':'

theorem isMappingValue_iff (c : Char) :
    isMappingValueBool c = true ↔ isMappingValueProp c := by
  simp [isMappingValueBool, isMappingValueProp]

instance (c : Char) : Decidable (isMappingValueProp c) := by
  unfold isMappingValueProp; infer_instance

/-- `[12] c-comment ::= "#"` (Bool). -/
@[yaml_spec "5.3" 12 "c-comment"]
def isCommentBool (c : Char) : Bool := c == '#'

/-- `[12] c-comment ::= "#"` (Prop). -/
@[yaml_spec "5.3" 12 "c-comment"]
def isCommentProp (c : Char) : Prop := c == '#'

theorem isComment_iff (c : Char) :
    isCommentBool c = true ↔ isCommentProp c := by
  simp [isCommentBool, isCommentProp]

instance (c : Char) : Decidable (isCommentProp c) := by
  unfold isCommentProp; infer_instance

/-- `[16] c-literal ::= "|"` (Bool). -/
@[yaml_spec "5.3" 16 "c-literal"]
def isLiteralBool (c : Char) : Bool := c == '|'

/-- `[16] c-literal ::= "|"` (Prop). -/
@[yaml_spec "5.3" 16 "c-literal"]
def isLiteralProp (c : Char) : Prop := c == '|'

theorem isLiteral_iff (c : Char) :
    isLiteralBool c = true ↔ isLiteralProp c := by
  simp [isLiteralBool, isLiteralProp]

instance (c : Char) : Decidable (isLiteralProp c) := by
  unfold isLiteralProp; infer_instance

/-- `[17] c-folded ::= ">"` (Bool). -/
@[yaml_spec "5.3" 17 "c-folded"]
def isFoldedBool (c : Char) : Bool := c == '>'

/-- `[17] c-folded ::= ">"` (Prop). -/
@[yaml_spec "5.3" 17 "c-folded"]
def isFoldedProp (c : Char) : Prop := c == '>'

theorem isFolded_iff (c : Char) :
    isFoldedBool c = true ↔ isFoldedProp c := by
  simp [isFoldedBool, isFoldedProp]

instance (c : Char) : Decidable (isFoldedProp c) := by
  unfold isFoldedProp; infer_instance

/-- `[18] c-single-quote ::= "'"` (Bool). -/
@[yaml_spec "5.3" 18 "c-single-quote"]
def isSingleQuoteBool (c : Char) : Bool := c == '\''

/-- `[18] c-single-quote ::= "'"` (Prop). -/
@[yaml_spec "5.3" 18 "c-single-quote"]
def isSingleQuoteProp (c : Char) : Prop := c == '\''

theorem isSingleQuote_iff (c : Char) :
    isSingleQuoteBool c = true ↔ isSingleQuoteProp c := by
  simp [isSingleQuoteBool, isSingleQuoteProp]

instance (c : Char) : Decidable (isSingleQuoteProp c) := by
  unfold isSingleQuoteProp; infer_instance

/-- `[19] c-double-quote ::= '"'` (Bool). -/
@[yaml_spec "5.3" 19 "c-double-quote"]
def isDoubleQuoteBool (c : Char) : Bool := c == '"'

/-- `[19] c-double-quote ::= '"'` (Prop). -/
@[yaml_spec "5.3" 19 "c-double-quote"]
def isDoubleQuoteProp (c : Char) : Prop := c == '"'

theorem isDoubleQuote_iff (c : Char) :
    isDoubleQuoteBool c = true ↔ isDoubleQuoteProp c := by
  simp [isDoubleQuoteBool, isDoubleQuoteProp]

instance (c : Char) : Decidable (isDoubleQuoteProp c) := by
  unfold isDoubleQuoteProp; infer_instance

/-! ## Escape Indicators

YAML 1.2.2 §5.7 — the backslash and the single-character escape
selectors that may follow it in double-quoted scalars.
(§5.7, https://yaml.org/spec/1.2.2/#57-escaped-characters)
-/

/-- `[41] c-escape ::= "\\"` (Bool). -/
@[yaml_spec "5.7" 41 "c-escape"]
def isEscapeBool (c : Char) : Bool := c == '\\'

/-- `[41] c-escape ::= "\\"` (Prop). -/
@[yaml_spec "5.7" 41 "c-escape"]
def isEscapeProp (c : Char) : Prop := c == '\\'

theorem isEscape_iff (c : Char) :
    isEscapeBool c = true ↔ isEscapeProp c := by
  simp [isEscapeBool, isEscapeProp]

instance (c : Char) : Decidable (isEscapeProp c) := by
  unfold isEscapeProp; infer_instance

/-- `[42] ns-esc-null ::= "0"` selector char (Bool). -/
@[yaml_spec "5.7" 42 "ns-esc-null"]
def isNsEscNullBool (c : Char) : Bool := c == '0'

/-- `[42] ns-esc-null ::= "0"` selector char (Prop). -/
@[yaml_spec "5.7" 42 "ns-esc-null"]
def isNsEscNullProp (c : Char) : Prop := c == '0'

theorem isNsEscNull_iff (c : Char) :
    isNsEscNullBool c = true ↔ isNsEscNullProp c := by
  simp [isNsEscNullBool, isNsEscNullProp]

instance (c : Char) : Decidable (isNsEscNullProp c) := by
  unfold isNsEscNullProp; infer_instance

/-- `[43] ns-esc-bell ::= "a"` selector char (Bool). -/
@[yaml_spec "5.7" 43 "ns-esc-bell"]
def isNsEscBellBool (c : Char) : Bool := c == 'a'

/-- `[43] ns-esc-bell ::= "a"` selector char (Prop). -/
@[yaml_spec "5.7" 43 "ns-esc-bell"]
def isNsEscBellProp (c : Char) : Prop := c == 'a'

theorem isNsEscBell_iff (c : Char) :
    isNsEscBellBool c = true ↔ isNsEscBellProp c := by
  simp [isNsEscBellBool, isNsEscBellProp]

instance (c : Char) : Decidable (isNsEscBellProp c) := by
  unfold isNsEscBellProp; infer_instance

/-- `[44] ns-esc-backspace ::= "b"` selector char (Bool). -/
@[yaml_spec "5.7" 44 "ns-esc-backspace"]
def isNsEscBackspaceBool (c : Char) : Bool := c == 'b'

/-- `[44] ns-esc-backspace ::= "b"` selector char (Prop). -/
@[yaml_spec "5.7" 44 "ns-esc-backspace"]
def isNsEscBackspaceProp (c : Char) : Prop := c == 'b'

theorem isNsEscBackspace_iff (c : Char) :
    isNsEscBackspaceBool c = true ↔ isNsEscBackspaceProp c := by
  simp [isNsEscBackspaceBool, isNsEscBackspaceProp]

instance (c : Char) : Decidable (isNsEscBackspaceProp c) := by
  unfold isNsEscBackspaceProp; infer_instance

/-- `[45] ns-esc-horizontal-tab ::= "t" | #x9` letter selector (Bool).
    The `#x9` alternative is recognised by `isTabBool`. -/
@[yaml_spec "5.7" 45 "ns-esc-horizontal-tab"]
def isNsEscHorizontalTabBool (c : Char) : Bool := c == 't'

/-- `[45] ns-esc-horizontal-tab ::= "t" | #x9` letter selector (Prop). -/
@[yaml_spec "5.7" 45 "ns-esc-horizontal-tab"]
def isNsEscHorizontalTabProp (c : Char) : Prop := c == 't'

theorem isNsEscHorizontalTab_iff (c : Char) :
    isNsEscHorizontalTabBool c = true ↔ isNsEscHorizontalTabProp c := by
  simp [isNsEscHorizontalTabBool, isNsEscHorizontalTabProp]

instance (c : Char) : Decidable (isNsEscHorizontalTabProp c) := by
  unfold isNsEscHorizontalTabProp; infer_instance

/-- `[46] ns-esc-line-feed ::= "n"` selector char (Bool). -/
@[yaml_spec "5.7" 46 "ns-esc-line-feed"]
def isNsEscLineFeedBool (c : Char) : Bool := c == 'n'

/-- `[46] ns-esc-line-feed ::= "n"` selector char (Prop). -/
@[yaml_spec "5.7" 46 "ns-esc-line-feed"]
def isNsEscLineFeedProp (c : Char) : Prop := c == 'n'

theorem isNsEscLineFeed_iff (c : Char) :
    isNsEscLineFeedBool c = true ↔ isNsEscLineFeedProp c := by
  simp [isNsEscLineFeedBool, isNsEscLineFeedProp]

instance (c : Char) : Decidable (isNsEscLineFeedProp c) := by
  unfold isNsEscLineFeedProp; infer_instance

/-- `[47] ns-esc-vertical-tab ::= "v"` selector char (Bool). -/
@[yaml_spec "5.7" 47 "ns-esc-vertical-tab"]
def isNsEscVerticalTabBool (c : Char) : Bool := c == 'v'

/-- `[47] ns-esc-vertical-tab ::= "v"` selector char (Prop). -/
@[yaml_spec "5.7" 47 "ns-esc-vertical-tab"]
def isNsEscVerticalTabProp (c : Char) : Prop := c == 'v'

theorem isNsEscVerticalTab_iff (c : Char) :
    isNsEscVerticalTabBool c = true ↔ isNsEscVerticalTabProp c := by
  simp [isNsEscVerticalTabBool, isNsEscVerticalTabProp]

instance (c : Char) : Decidable (isNsEscVerticalTabProp c) := by
  unfold isNsEscVerticalTabProp; infer_instance

/-- `[48] ns-esc-form-feed ::= "f"` selector char (Bool). -/
@[yaml_spec "5.7" 48 "ns-esc-form-feed"]
def isNsEscFormFeedBool (c : Char) : Bool := c == 'f'

/-- `[48] ns-esc-form-feed ::= "f"` selector char (Prop). -/
@[yaml_spec "5.7" 48 "ns-esc-form-feed"]
def isNsEscFormFeedProp (c : Char) : Prop := c == 'f'

theorem isNsEscFormFeed_iff (c : Char) :
    isNsEscFormFeedBool c = true ↔ isNsEscFormFeedProp c := by
  simp [isNsEscFormFeedBool, isNsEscFormFeedProp]

instance (c : Char) : Decidable (isNsEscFormFeedProp c) := by
  unfold isNsEscFormFeedProp; infer_instance

/-- `[49] ns-esc-carriage-return ::= "r"` selector char (Bool). -/
@[yaml_spec "5.7" 49 "ns-esc-carriage-return"]
def isNsEscCarriageReturnBool (c : Char) : Bool := c == 'r'

/-- `[49] ns-esc-carriage-return ::= "r"` selector char (Prop). -/
@[yaml_spec "5.7" 49 "ns-esc-carriage-return"]
def isNsEscCarriageReturnProp (c : Char) : Prop := c == 'r'

theorem isNsEscCarriageReturn_iff (c : Char) :
    isNsEscCarriageReturnBool c = true ↔ isNsEscCarriageReturnProp c := by
  simp [isNsEscCarriageReturnBool, isNsEscCarriageReturnProp]

instance (c : Char) : Decidable (isNsEscCarriageReturnProp c) := by
  unfold isNsEscCarriageReturnProp; infer_instance

/-- `[50] ns-esc-escape ::= "e"` selector char (Bool). -/
@[yaml_spec "5.7" 50 "ns-esc-escape"]
def isNsEscEscapeBool (c : Char) : Bool := c == 'e'

/-- `[50] ns-esc-escape ::= "e"` selector char (Prop). -/
@[yaml_spec "5.7" 50 "ns-esc-escape"]
def isNsEscEscapeProp (c : Char) : Prop := c == 'e'

theorem isNsEscEscape_iff (c : Char) :
    isNsEscEscapeBool c = true ↔ isNsEscEscapeProp c := by
  simp [isNsEscEscapeBool, isNsEscEscapeProp]

instance (c : Char) : Decidable (isNsEscEscapeProp c) := by
  unfold isNsEscEscapeProp; infer_instance

/-- `[53] ns-esc-slash ::= "/"` selector char (Bool). -/
@[yaml_spec "5.7" 53 "ns-esc-slash"]
def isNsEscSlashBool (c : Char) : Bool := c == '/'

/-- `[53] ns-esc-slash ::= "/"` selector char (Prop). -/
@[yaml_spec "5.7" 53 "ns-esc-slash"]
def isNsEscSlashProp (c : Char) : Prop := c == '/'

theorem isNsEscSlash_iff (c : Char) :
    isNsEscSlashBool c = true ↔ isNsEscSlashProp c := by
  simp [isNsEscSlashBool, isNsEscSlashProp]

instance (c : Char) : Decidable (isNsEscSlashProp c) := by
  unfold isNsEscSlashProp; infer_instance

/-- `[55] ns-esc-next-line ::= "N"` selector char (Bool). -/
@[yaml_spec "5.7" 55 "ns-esc-next-line"]
def isNsEscNextLineBool (c : Char) : Bool := c == 'N'

/-- `[55] ns-esc-next-line ::= "N"` selector char (Prop). -/
@[yaml_spec "5.7" 55 "ns-esc-next-line"]
def isNsEscNextLineProp (c : Char) : Prop := c == 'N'

theorem isNsEscNextLine_iff (c : Char) :
    isNsEscNextLineBool c = true ↔ isNsEscNextLineProp c := by
  simp [isNsEscNextLineBool, isNsEscNextLineProp]

instance (c : Char) : Decidable (isNsEscNextLineProp c) := by
  unfold isNsEscNextLineProp; infer_instance

/-- `[56] ns-esc-non-breaking-space ::= "_"` selector char (Bool). -/
@[yaml_spec "5.7" 56 "ns-esc-non-breaking-space"]
def isNsEscNbspBool (c : Char) : Bool := c == '_'

/-- `[56] ns-esc-non-breaking-space ::= "_"` selector char (Prop). -/
@[yaml_spec "5.7" 56 "ns-esc-non-breaking-space"]
def isNsEscNbspProp (c : Char) : Prop := c == '_'

theorem isNsEscNbsp_iff (c : Char) :
    isNsEscNbspBool c = true ↔ isNsEscNbspProp c := by
  simp [isNsEscNbspBool, isNsEscNbspProp]

instance (c : Char) : Decidable (isNsEscNbspProp c) := by
  unfold isNsEscNbspProp; infer_instance

/-- `[57] ns-esc-line-separator ::= "L"` selector char (Bool). -/
@[yaml_spec "5.7" 57 "ns-esc-line-separator"]
def isNsEscLineSeparatorBool (c : Char) : Bool := c == 'L'

/-- `[57] ns-esc-line-separator ::= "L"` selector char (Prop). -/
@[yaml_spec "5.7" 57 "ns-esc-line-separator"]
def isNsEscLineSeparatorProp (c : Char) : Prop := c == 'L'

theorem isNsEscLineSeparator_iff (c : Char) :
    isNsEscLineSeparatorBool c = true ↔ isNsEscLineSeparatorProp c := by
  simp [isNsEscLineSeparatorBool, isNsEscLineSeparatorProp]

instance (c : Char) : Decidable (isNsEscLineSeparatorProp c) := by
  unfold isNsEscLineSeparatorProp; infer_instance

/-- `[58] ns-esc-paragraph-separator ::= "P"` selector char (Bool). -/
@[yaml_spec "5.7" 58 "ns-esc-paragraph-separator"]
def isNsEscParagraphSeparatorBool (c : Char) : Bool := c == 'P'

/-- `[58] ns-esc-paragraph-separator ::= "P"` selector char (Prop). -/
@[yaml_spec "5.7" 58 "ns-esc-paragraph-separator"]
def isNsEscParagraphSeparatorProp (c : Char) : Prop := c == 'P'

theorem isNsEscParagraphSeparator_iff (c : Char) :
    isNsEscParagraphSeparatorBool c = true ↔ isNsEscParagraphSeparatorProp c := by
  simp [isNsEscParagraphSeparatorBool, isNsEscParagraphSeparatorProp]

instance (c : Char) : Decidable (isNsEscParagraphSeparatorProp c) := by
  unfold isNsEscParagraphSeparatorProp; infer_instance

/-- `[59] ns-esc-8-bit` introducer char `"x"` (Bool). -/
@[yaml_spec "5.7" 59 "ns-esc-8-bit"]
def isNsEsc8BitBool (c : Char) : Bool := c == 'x'

/-- `[59] ns-esc-8-bit` introducer char `"x"` (Prop). -/
@[yaml_spec "5.7" 59 "ns-esc-8-bit"]
def isNsEsc8BitProp (c : Char) : Prop := c == 'x'

theorem isNsEsc8Bit_iff (c : Char) :
    isNsEsc8BitBool c = true ↔ isNsEsc8BitProp c := by
  simp [isNsEsc8BitBool, isNsEsc8BitProp]

instance (c : Char) : Decidable (isNsEsc8BitProp c) := by
  unfold isNsEsc8BitProp; infer_instance

/-- `[60] ns-esc-16-bit` introducer char `"u"` (Bool). -/
@[yaml_spec "5.7" 60 "ns-esc-16-bit"]
def isNsEsc16BitBool (c : Char) : Bool := c == 'u'

/-- `[60] ns-esc-16-bit` introducer char `"u"` (Prop). -/
@[yaml_spec "5.7" 60 "ns-esc-16-bit"]
def isNsEsc16BitProp (c : Char) : Prop := c == 'u'

theorem isNsEsc16Bit_iff (c : Char) :
    isNsEsc16BitBool c = true ↔ isNsEsc16BitProp c := by
  simp [isNsEsc16BitBool, isNsEsc16BitProp]

instance (c : Char) : Decidable (isNsEsc16BitProp c) := by
  unfold isNsEsc16BitProp; infer_instance

/-- `[61] ns-esc-32-bit` introducer char `"U"` (Bool). -/
@[yaml_spec "5.7" 61 "ns-esc-32-bit"]
def isNsEsc32BitBool (c : Char) : Bool := c == 'U'

/-- `[61] ns-esc-32-bit` introducer char `"U"` (Prop). -/
@[yaml_spec "5.7" 61 "ns-esc-32-bit"]
def isNsEsc32BitProp (c : Char) : Prop := c == 'U'

theorem isNsEsc32Bit_iff (c : Char) :
    isNsEsc32BitBool c = true ↔ isNsEsc32BitProp c := by
  simp [isNsEsc32BitBool, isNsEsc32BitProp]

instance (c : Char) : Decidable (isNsEsc32BitProp c) := by
  unfold isNsEsc32BitProp; infer_instance

/-! ## Block-Scalar Header Indicators

YAML 1.2.2 §8.1.1.2 [164] c-chomping-indicator. The `strip` case is the
sequence-entry character (already covered by `isSequenceEntryBool`);
the `keep` case has its own dedicated predicate below.
(§8.1.1.2, https://yaml.org/spec/1.2.2/#8112-block-chomping-indicator)
-/

/-- `[164] c-chomping-indicator(keep) ::= "+"` (Bool). -/
@[yaml_spec "8.1.1.2" 164 "c-chomping-indicator"]
def isChompKeepBool (c : Char) : Bool := c == '+'

/-- `[164] c-chomping-indicator(keep) ::= "+"` (Prop). -/
@[yaml_spec "8.1.1.2" 164 "c-chomping-indicator"]
def isChompKeepProp (c : Char) : Prop := c == '+'

theorem isChompKeep_iff (c : Char) :
    isChompKeepBool c = true ↔ isChompKeepProp c := by
  simp [isChompKeepBool, isChompKeepProp]

instance (c : Char) : Decidable (isChompKeepProp c) := by
  unfold isChompKeepProp; infer_instance

/-! ## Document-End Marker Character

YAML 1.2.2 §9.1.4 [203] c-document-end ::= "..." — the dot character
has no single-character production of its own; the predicate below is
introduced for spec traceability of the three-dot marker check.
(§9.1.4, https://yaml.org/spec/1.2.2/#914-explicit-document-end-marker)
-/

/-- Dot character `"."` used in [203] c-document-end (Bool). -/
@[yaml_spec "9.1.4" 203 "c-document-end"]
def isDocEndDotBool (c : Char) : Bool := c == '.'

/-- Dot character `"."` used in [203] c-document-end (Prop). -/
@[yaml_spec "9.1.4" 203 "c-document-end"]
def isDocEndDotProp (c : Char) : Prop := c == '.'

theorem isDocEndDot_iff (c : Char) :
    isDocEndDotBool c = true ↔ isDocEndDotProp c := by
  simp [isDocEndDotBool, isDocEndDotProp]

instance (c : Char) : Decidable (isDocEndDotProp c) := by
  unfold isDocEndDotProp; infer_instance

/-! ## Spec-Level Character Constants

Concrete `Char` values for characters that the scanner emits (rather
than tests against input). Each constant carries the `@[yaml_spec]`
annotation pointing to the spec production whose literal it realises,
so even output characters remain traceable to the spec.
-/

/-- `#xA`: line-feed character emitted for [24] b-line-feed. -/
@[yaml_spec "5.4" 24 "b-line-feed"]
def lineFeedChar : Char := '\n'

/-- `#xD`: carriage-return character emitted for [25] b-carriage-return. -/
@[yaml_spec "5.4" 25 "b-carriage-return"]
def carriageReturnChar : Char := '\r'

/-- `#x20`: space character emitted for [31] s-space. -/
@[yaml_spec "5.5" 31 "s-space"]
def spaceChar : Char := ' '

/-- `#x9`: tab character emitted for [32] s-tab. -/
@[yaml_spec "5.5" 32 "s-tab"]
def tabChar : Char := '\t'

/-- `#x27`: single-quote character emitted for [18] c-single-quote. -/
@[yaml_spec "5.3" 18 "c-single-quote"]
def singleQuoteChar : Char := '\''

/-- `#x22`: double-quote character emitted for [19] c-double-quote
    and [52] ns-esc-double-quote. -/
@[yaml_spec "5.3" 19 "c-double-quote",
  yaml_spec "5.7" 52 "ns-esc-double-quote"]
def doubleQuoteChar : Char := '"'

/-- `#x5C`: backslash character emitted for [41] c-escape and
    [54] ns-esc-backslash. -/
@[yaml_spec "5.7" 41 "c-escape",
  yaml_spec "5.7" 54 "ns-esc-backslash"]
def backslashChar : Char := '\\'

/-- `#x2F`: forward-slash character emitted for [53] ns-esc-slash. -/
@[yaml_spec "5.7" 53 "ns-esc-slash"]
def slashChar : Char := '/'

/-! ### Escape-Result Characters (§5.7)

The values the scanner emits when it decodes a `c-ns-esc-char` escape
sequence. Each is the unicode code point named by the corresponding
`ns-esc-*` production.
-/

/-- `#x00`: result of [42] ns-esc-null escape. -/
@[yaml_spec "5.7" 42 "ns-esc-null"]
def nsEscNullChar : Char := '\x00'

/-- `#x07`: result of [43] ns-esc-bell escape. -/
@[yaml_spec "5.7" 43 "ns-esc-bell"]
def nsEscBellChar : Char := '\x07'

/-- `#x08`: result of [44] ns-esc-backspace escape. -/
@[yaml_spec "5.7" 44 "ns-esc-backspace"]
def nsEscBackspaceChar : Char := '\x08'

/-- `#x0B`: result of [47] ns-esc-vertical-tab escape. -/
@[yaml_spec "5.7" 47 "ns-esc-vertical-tab"]
def nsEscVerticalTabChar : Char := '\x0B'

/-- `#x0C`: result of [48] ns-esc-form-feed escape. -/
@[yaml_spec "5.7" 48 "ns-esc-form-feed"]
def nsEscFormFeedChar : Char := '\x0C'

/-- `#x1B`: result of [50] ns-esc-escape escape. -/
@[yaml_spec "5.7" 50 "ns-esc-escape"]
def nsEscEscapeChar : Char := '\x1B'

/-- `#x85`: result of [55] ns-esc-next-line escape. -/
@[yaml_spec "5.7" 55 "ns-esc-next-line"]
def nsEscNextLineChar : Char := '\x85'

/-- `#xA0`: result of [56] ns-esc-non-breaking-space escape. -/
@[yaml_spec "5.7" 56 "ns-esc-non-breaking-space"]
def nsEscNbspChar : Char := '\xA0'

/-- `#x2028`: result of [57] ns-esc-line-separator escape. -/
@[yaml_spec "5.7" 57 "ns-esc-line-separator"]
def nsEscLineSeparatorChar : Char := Char.ofNat 0x2028

/-- `#x2029`: result of [58] ns-esc-paragraph-separator escape. -/
@[yaml_spec "5.7" 58 "ns-esc-paragraph-separator"]
def nsEscParagraphSeparatorChar : Char := Char.ofNat 0x2029

/-! ## Printable Characters

YAML 1.2.2: [1] c-printable (§5.1, https://yaml.org/spec/1.2.2/#51-character-set)
-/

/-- `[1] c-printable`: characters that can appear in a YAML stream (Prop). -/
@[yaml_spec "5.1" 1 "c-printable"]
def isPrintableProp (c : Char) : Prop :=
  c == '\t'                                  -- Tab
  ∨ (c.val ≥ 0x20 ∧ c.val ≤ 0x7E)            -- Printable ASCII
  ∨ c == '\u0085'                            -- Next Line
  ∨ (c.val ≥ 0xA0 ∧ c.val ≤ 0xD7FF)          -- Basic Multilingual Plane (BMP)
  ∨ (c.val ≥ 0xE000 ∧ c.val ≤ 0xFFFD)        -- Additional Unicode Areas
  ∨ (c.val ≥ 0x10000 ∧ c.val ≤ 0x10FFFF)     -- 32-bit Unicode

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
@[yaml_spec "5.5" 31 "s-space"]
def isIndentCharBool (c : Char) : Bool := c == ' '

/-- `[31] s-space`: only the space character is valid for indentation (Prop). -/
@[yaml_spec "5.5" 31 "s-space"]
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
  yaml_spec "5.6" 37 "ns-ascii-letter",
  yaml_spec "5.6" 38 "ns-word-char"]
def isWordCharProp (c : Char) : Prop :=
  (c.val ≥ 0x30 ∧ c.val ≤ 0x39)  -- [35] ns-dec-digit
  ∨ isAsciiLetterProp c          -- [37] ns-ascii-letter
  ∨ c = '-'

instance (c : Char) : Decidable (isWordCharProp c) := by
  unfold isWordCharProp; infer_instance

/-- `[38] ns-word-char`: `ns-dec-digit | ns-ascii-letter | '-'` (Bool). -/
@[yaml_spec "5.6" 35 "ns-dec-digit",
  yaml_spec "5.6" 37 "ns-ascii-letter",
  yaml_spec "5.6" 38 "ns-word-char"]
def isWordCharBool (c : Char) : Bool := decide (isWordCharProp c)

theorem isWordChar_iff (c : Char) : isWordCharBool c = true ↔ isWordCharProp c := by
  simp [isWordCharBool, decide_eq_true_eq]

/-- `[39] ns-uri-char`: word-char plus URI-special characters and `%` (Prop).

    The spec production `'%' ns-hex-digit ns-hex-digit` is a multi-character
    sequence; at the single-character level we accept `%` and leave hex-digit
    validation to the enclosing loop. -/
@[yaml_spec "5.6" 36 "ns-hex-digit",
  yaml_spec "5.6" 38 "ns-word-char",
  yaml_spec "5.6" 39 "ns-uri-char"]
def isUriCharProp (c : Char) : Prop :=
  isWordCharProp c
  ∨ c ∈ ['%', '#', ';', '/', '?', ':', '@', '&', '=', '+', '$', ',',
          '_', '.', '!', '~', '*', '\'', '(', ')', '[', ']']

instance (c : Char) : Decidable (isUriCharProp c) := by
  unfold isUriCharProp; infer_instance

/-- `[39] ns-uri-char`: word-char plus URI-special characters and `%` (Bool). -/
@[yaml_spec "5.6" 36 "ns-hex-digit",
  yaml_spec "5.6" 38 "ns-word-char",
  yaml_spec "5.6" 39 "ns-uri-char"]
def isUriCharBool (c : Char) : Bool := decide (isUriCharProp c)

theorem isUriChar_iff (c : Char) : isUriCharBool c = true ↔ isUriCharProp c := by
  simp [isUriCharBool, decide_eq_true_eq]

/-- `[40] ns-tag-char`: `ns-uri-char - '!' - c-flow-indicator` (Prop). -/
@[yaml_spec "5.6" 39 "ns-uri-char",
  yaml_spec "5.6" 40 "ns-tag-char"]
def isTagCharProp (c : Char) : Prop :=
  isUriCharProp c ∧ c ≠ '!' ∧ ¬isFlowIndicatorProp c

instance (c : Char) : Decidable (isTagCharProp c) := by
  unfold isTagCharProp; infer_instance

/-- `[40] ns-tag-char`: `ns-uri-char - '!' - c-flow-indicator` (Bool). -/
@[yaml_spec "5.6" 39 "ns-uri-char",
  yaml_spec "5.6" 40 "ns-tag-char"]
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
@[yaml_spec "5.5" 34 "ns-char",
  yaml_spec "5.3" 5 "c-mapping-key",
  yaml_spec "5.3" 6 "c-mapping-value",
  yaml_spec "5.3" 4 "c-sequence-entry",
  yaml_spec "7.3.3" 126 "ns-plain-first"]
def canStartPlainScalarBool (c : Char) (next : Option Char) (inFlow : Bool) : Bool :=
  if c = '-' ∨ c = '?' ∨ c = ':' then
    match next with
    | some n => !isWhiteSpaceBool n && !isLineBreakBool n && !(inFlow && isFlowIndicatorBool n)
    | none => false
  else
    !isIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c

/-- `[126] ns-plain-first(c)`: can character start a plain scalar? (Prop). -/
@[yaml_spec "5.5" 34 "ns-char",
  yaml_spec "5.3" 5 "c-mapping-key",
  yaml_spec "5.3" 6 "c-mapping-value",
  yaml_spec "5.3" 4 "c-sequence-entry",
  yaml_spec "7.3.3" 126 "ns-plain-first"]
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

/-- `[127] ns-plain-safe(c)`: safe continuation character for plain scalars (Bool).

    The spec dispatches on `c : YamlContext` with four cases:
      `[127] ns-plain-safe(FLOW-OUT)  ::= ns-plain-safe-out`
      `[127] ns-plain-safe(FLOW-IN)   ::= ns-plain-safe-in`
      `[127] ns-plain-safe(BLOCK-KEY) ::= ns-plain-safe-out`
      `[127] ns-plain-safe(FLOW-KEY)  ::= ns-plain-safe-in`
    These collapse into two equivalence classes, captured here by the
    Bool parameter `inFlow`:
      `inFlow = false` ↔ FLOW-OUT, BLOCK-KEY (→ ns-plain-safe-out)
      `inFlow = true`  ↔ FLOW-IN,  FLOW-KEY  (→ ns-plain-safe-in)
    The spec does not define [127] for BLOCK-OUT / BLOCK-IN; callers in those
    contexts are out of spec for this production. -/
@[yaml_spec "7.3.3" 127 "ns-plain-safe",
  yaml_spec "7.3.3" 128 "ns-plain-safe-out",
  yaml_spec "7.3.3" 129 "ns-plain-safe-in"]
def isPlainSafeBool (c : Char) (inFlow : Bool) : Bool :=
  if inFlow then
    !isWhiteSpaceBool c && !isLineBreakBool c && !isFlowIndicatorBool c
  else
    !isWhiteSpaceBool c && !isLineBreakBool c

/-- `[127] ns-plain-safe(c)`: safe continuation character for plain scalars (Prop).

    Bool parameter `inFlow` encodes the spec's 4→2 partition (see
    `isPlainSafeBool` for details):
      `inFlow = false` ↔ FLOW-OUT, BLOCK-KEY
      `inFlow = true`  ↔ FLOW-IN,  FLOW-KEY -/
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
@[yaml_spec "5.5" 34 "ns-char",
  yaml_spec "5.3" 5 "c-mapping-key",
  yaml_spec "5.3" 6 "c-mapping-value",
  yaml_spec "5.3" 4 "c-sequence-entry",
  yaml_spec "7.3.3" 126 "ns-plain-first"]
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
@[yaml_spec "5.5" 34 "ns-char",
  yaml_spec "5.3" 5 "c-mapping-key",
  yaml_spec "5.3" 6 "c-mapping-value",
  yaml_spec "5.3" 4 "c-sequence-entry",
  yaml_spec "7.3.3" 126 "ns-plain-first"]
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
  simp [isPlainSafeProp, isWhiteSpaceProp, isSpaceProp, isTabProp] at h

/-- Whitespace chars have `getLast? = some ' '` or `some '\t'`. -/
theorem whitespace_getLast?_cases (spaces : String)
    (h : ∀ c ∈ spaces.toList, isWhiteSpaceProp c) (hne : spaces.toList ≠ []) :
    spaces.toList.getLast? = some ' ' ∨ spaces.toList.getLast? = some '\t' := by
  have hLast := List.getLast?_eq_some_getLast hne
  rw [hLast]
  have hMem := List.getLast_mem hne
  have hws := h _ hMem
  simp only [isWhiteSpaceProp, isSpaceProp, isTabProp, beq_iff_eq] at hws
  rcases hws with h1 | h1 <;> simp [h1]

/-- A string of pure whitespace has no colon-space pattern. -/
theorem noColonSpaceProp_of_whitespace (s : String)
    (h : ∀ c ∈ s.toList, isWhiteSpaceProp c) : noColonSpaceProp s := by
  intro ⟨i, h1, _⟩
  have hMem := mem_of_getElemQ_some h1
  have hws := h ':' hMem
  simp [isWhiteSpaceProp, isSpaceProp, isTabProp] at hws

/-- A string of pure whitespace has no space-hash pattern. -/
theorem noSpaceHashProp_of_whitespace (s : String)
    (h : ∀ c ∈ s.toList, isWhiteSpaceProp c) : noSpaceHashProp s := by
  intro ⟨i, _, h2⟩
  have hMem := mem_of_getElemQ_some h2
  have hws := h '#' hMem
  simp [isWhiteSpaceProp, isSpaceProp, isTabProp] at hws

/-- A string of pure whitespace has no flow indicators. -/
theorem noFlowIndicatorsProp_of_whitespace (s : String)
    (h : ∀ c ∈ s.toList, isWhiteSpaceProp c) : noFlowIndicatorsProp s := by
  intro c hc hfi
  have := h c hc
  simp only [isWhiteSpaceProp, isSpaceProp, isTabProp, beq_iff_eq] at this
  rcases this with rfl | rfl <;> simp [isFlowIndicatorProp] at hfi

end L4YAML.CharPredicates
