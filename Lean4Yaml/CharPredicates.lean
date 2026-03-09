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
private theorem not_and_bool_iff_imp_not {b₁ b₂ : Bool} {p : Prop}
    (h : b₂ = true ↔ p) :
    (!(b₁ && b₂)) = true ↔ (b₁ = true → ¬p) := by
  cases b₁ <;> cases b₂ <;> simp_all

/-! ## Line Break Characters

YAML 1.2.2: [24] b-line-feed, [25] b-carriage-return, [26] b-char
(§5.4, https://yaml.org/spec/1.2.2/#54-line-break-characters)
-/

/-- `[26] b-char`: line feed or carriage return (Bool). -/
def isLineBreakBool (c : Char) : Bool := c == '\n' || c == '\r'

/-- `[26] b-char`: line feed or carriage return (Prop). -/
@[yaml_spec "5.4" 26 "b-char"]
def isLineBreakProp (c : Char) : Prop := c == '\n' ∨ c == '\r'

theorem isLineBreak_iff (c : Char) : isLineBreakBool c = true ↔ isLineBreakProp c := by
  simp only [isLineBreakBool, isLineBreakProp, Bool.or_eq_true]

instance (c : Char) : Decidable (isLineBreakProp c) := by
  unfold isLineBreakProp; infer_instance

/-! ## White Space Characters

YAML 1.2.2: [33] s-white (§5.5, https://yaml.org/spec/1.2.2/#55-white-space-characters)
-/

/-- `[33] s-white`: space or tab (Bool). -/
def isWhiteSpaceBool (c : Char) : Bool := c == ' ' || c == '\t'

/-- `[33] s-white`: space or tab (Prop). -/
@[yaml_spec "5.5" 33 "s-white"]
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
def isFlowIndicatorBool (c : Char) : Bool := c ∈ [',', '[', ']', '{', '}']

/-- `[23] c-flow-indicator`: `,`, `[`, `]`, `{`, `}` (Prop). -/
@[yaml_spec "5.3" 23 "c-flow-indicator"]
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
def isIndicatorBool (c : Char) : Bool :=
  c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
       '\'', '"', '%', '@', '`']

/-- `[22] c-indicator`: all YAML indicator characters (Prop). -/
@[yaml_spec "5.3" 22 "c-indicator"]
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
def isPrintableBool (c : Char) : Bool := decide (isPrintableProp c)

theorem isPrintable_iff (c : Char) : isPrintableBool c = true ↔ isPrintableProp c := by
  simp [isPrintableBool, decide_eq_true_eq]

/-! ## Indent Character

YAML 1.2.2: [31] s-space (§6.1, https://yaml.org/spec/1.2.2/#61-indentation-spaces)
-/

/-- `[31] s-space`: only the space character is valid for indentation (Bool). -/
def isIndentCharBool (c : Char) : Bool := c == ' '

/-- `[31] s-space`: only the space character is valid for indentation (Prop). -/
@[yaml_spec "6.1" 31 "s-space"]
def isIndentCharProp (c : Char) : Prop := c == ' '

theorem isIndentChar_iff (c : Char) :
    isIndentCharBool c = true ↔ isIndentCharProp c := by
  simp [isIndentCharBool, isIndentCharProp]

instance (c : Char) : Decidable (isIndentCharProp c) := by
  unfold isIndentCharProp; infer_instance

/-! ## Plain Scalar First Character

YAML 1.2.2: [123] ns-plain-first(c) (§7.3.3, https://yaml.org/spec/1.2.2/#733-plain-style)

3-argument version matching the full YAML spec: `-`, `?`, `:` are allowed
when followed by a safe character (non-blank, and in flow context additionally
non-flow-indicator).
-/

/-- `[123] ns-plain-first(c)`: can character start a plain scalar? (Bool). -/
def canStartPlainScalarBool (c : Char) (next : Option Char) (inFlow : Bool) : Bool :=
  if c = '-' ∨ c = '?' ∨ c = ':' then
    match next with
    | some n => !isWhiteSpaceBool n && !isLineBreakBool n && !(inFlow && isFlowIndicatorBool n)
    | none => false
  else
    !isIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c

/-- `[123] ns-plain-first(c)`: can character start a plain scalar? (Prop). -/
@[yaml_spec "7.3.3" 123 "ns-plain-first(c)"]
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

YAML 1.2.2: [126] ns-plain-safe(c) (§7.3.3)

In block context: not whitespace, not line break.
In flow context: additionally not a flow indicator.
-/

/-- `[126] ns-plain-safe(c)`: safe continuation character for plain scalars (Bool). -/
def isPlainSafeBool (c : Char) (inFlow : Bool) : Bool :=
  if inFlow then
    !isWhiteSpaceBool c && !isLineBreakBool c && !isFlowIndicatorBool c
  else
    !isWhiteSpaceBool c && !isLineBreakBool c

/-- `[126] ns-plain-safe(c)`: safe continuation character for plain scalars (Prop). -/
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

YAML 1.2.2: [123] ns-plain-first(c) applied to the first character(s) of
a string. 2-argument version with flow context.
-/

/-- First character(s) can start a plain scalar (Bool). -/
def validPlainFirstBool (content : String) (inFlow : Bool) : Bool :=
  match content.toList with
  | c :: n :: _ => canStartPlainScalarBool c (some n) inFlow
  | [c] => canStartPlainScalarBool c none inFlow
  | [] => true

/-- First character(s) can start a plain scalar (Prop). -/
def validPlainFirstProp (content : String) (inFlow : Bool) : Prop :=
  match content.toList with
  | c :: n :: _ => canStartPlainScalarProp c (some n) inFlow
  | [c] => canStartPlainScalarProp c none inFlow
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
  simp only [validPlainFirstBool, validPlainFirstProp]
  cases content.toList with
  | nil => simp
  | cons c rest =>
    cases rest with
    | nil => exact canStartPlainScalar_iff c none inFlow
    | cons n _ => exact canStartPlainScalar_iff c (some n) inFlow

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

/-! ## No Colon-Space

YAML 1.2.2: [127] ns-plain-char(c) (§7.3.3) — colon may appear in a
plain scalar only when NOT followed by an `s-white` character.
-/

/-- Content does not contain `: ` (Bool). -/
def noColonSpaceBool (content : String) : Bool :=
  !hasAdjacentChars ':' ' ' content.toList

/-- Content does not contain `: ` (Prop). -/
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

YAML 1.2.2: [127] ns-plain-char(c) (§7.3.3) — `#` may appear in a
plain scalar only when NOT preceded by an `s-white` character.
-/

/-- Content does not contain ` #` (Bool). -/
def noSpaceHashBool (content : String) : Bool :=
  !hasAdjacentChars ' ' '#' content.toList

/-- Content does not contain ` #` (Prop). -/
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

YAML 1.2.2: [126] ns-plain-safe(FLOW-IN) (§7.3.3) — in flow context,
plain scalars additionally cannot contain flow indicator characters.
-/

/-- Content contains no flow indicators (Bool). -/
def noFlowIndicatorsBool (content : String) : Bool :=
  content.toList.all (fun c => !isFlowIndicatorBool c)

/-- Content contains no flow indicators (Prop). -/
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

end Lean4Yaml.CharPredicates
