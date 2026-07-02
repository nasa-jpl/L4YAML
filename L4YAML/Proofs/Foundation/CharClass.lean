import L4YAML.Spec.Grammar
import L4YAML.Scanner.Scanner
import L4YAML.Spec.CharPredicates

/-!
# Character Classification Correspondence Proofs (Layer 1c)

This module proves that the `Prop`-valued character classifiers in
`CharPredicates.lean` correspond exactly to the `Bool`-valued classifiers.

Each theorem states: `XProp c ↔ XBool c = true`.

This is the formal version of the 32 runtime tests in
`Tests/Verification.lean` (categories: Grammar↔Combinators isLineBreak,
isWhiteSpace, isFlowIndicator, isIndentChar, canStartPlainScalar).

## Strategy

The Grammar definitions use `Prop` connectives (`∨`, `∧`, `¬`, `∈`) over
`BEq Char` comparisons. The Parser definitions use the corresponding `Bool`
operators (`||`, `&&`, `!`, `∈` on `List`). Since `Char` has `DecidableEq`
and all operations are computable, the proofs use `simp` lemmas connecting
`Prop`-level and `Bool`-level operations, primarily `Bool.or_eq_true`.
-/

namespace L4YAML.Proofs.CharClass

open L4YAML.CharPredicates

/-! ## isLineBreak: isLineBreakProp ↔ isLineBreakBool -/

/--
The Prop specification of line breaks matches the Bool implementation.

- Prop: `isLineFeedProp c ∨ isCarriageReturnProp c`
- Bool: `isLineFeedBool c || isCarriageReturnBool c`
-/
theorem isLineBreak_correspondence (c : Char) :
    isLineBreakProp c ↔ isLineBreakBool c = true := by
  simp only [isLineBreakProp, isLineBreakBool, isLineFeedProp, isLineFeedBool,
             isCarriageReturnProp, isCarriageReturnBool, Bool.or_eq_true]

/-! ## isWhiteSpace: isWhiteSpaceProp ↔ isWhiteSpaceBool -/

/--
The Prop specification of white space matches the Bool implementation.

- Prop: `isSpaceProp c ∨ isTabProp c`
- Bool: `isSpaceBool c || isTabBool c`
-/
theorem isWhiteSpace_correspondence (c : Char) :
    isWhiteSpaceProp c ↔ isWhiteSpaceBool c = true := by
  simp only [isWhiteSpaceProp, isWhiteSpaceBool, isSpaceProp, isSpaceBool,
             isTabProp, isTabBool, Bool.or_eq_true]

/-! ## isIndentChar: isIndentCharProp ↔ (c == ' ') -/

/--
The Prop specification of indentation characters matches the parser check.

- Prop: `c == ' '`
- Parser: uses inline `c == ' '` checks (no dedicated Bool function)

We prove the definition is equivalent to `(c == ' ') = true`.
-/
theorem isIndentChar_iff (c : Char) :
    isIndentCharProp c ↔ (c == ' ') = true := by
  simp only [isIndentCharProp]

/-! ## isFlowIndicator: isFlowIndicatorProp ↔ isFlowIndicatorBool -/

/--
The Prop specification of flow indicators matches the Bool implementation.

Both use `c ∈ [',', '[', ']', '{', '}']`.
-/
theorem isFlowIndicator_correspondence (c : Char) :
    isFlowIndicatorProp c ↔ isFlowIndicatorBool c = true := by
  unfold isFlowIndicatorProp isFlowIndicatorBool
  simp [List.mem_cons, Bool.or_eq_true]

/-! ## isIndicator: Grammar indicators ↔ isIndicatorBool -/

/--
The full indicator list used in `canStartPlainScalar` matches
`isIndicatorBool`. Both expand to `List.elem` on the same character list.
-/
theorem isIndicator_equiv (c : Char) :
    (c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
          '\'', '"', '%', '@', '`'] : Prop) ↔
    isIndicatorBool c = true := by
  unfold isIndicatorBool
  simp [List.mem_cons, Bool.or_eq_true]

/-! ## canStartPlainScalar: Grammar.canStartPlainScalar (1-arg) → canStartPlainScalarBool (3-arg)

The Grammar Prop captures the base exclusion rule (YAML §7.3.3 [123]).
The Scanner Bool `canStartPlainScalar` captures the full rule including
the exception for `-`/`?`/`:` followed by a safe character, and the
flow-context restriction on flow indicators.

We prove:
1. **Base**: non-exceptional characters — Grammar implies Scanner (universal over `inFlow`).
2. **Exception (block)**: `-`/`?`/`:` followed by non-blank → Scanner accepts.
3. **Exception (flow)**: same, but additionally requires non-flow-indicator.
4. **Exception (none)**: no following character → Scanner rejects (universal over `inFlow`).
-/

/--
For non-exceptional characters (not `-`, `?`, `:`), if a character is printable,
not whitespace, not a line break, and not an indicator, then
`canStartPlainScalarBool c next inFlow = true` for any `next` and `inFlow`.

The `else` branch of `canStartPlainScalarBool` is context-independent:
`!isIndicator c && !isWhiteSpace c && !isLineBreak c`.
-/
theorem canStartPlainScalar_base (c : Char) (next : Option Char) (inFlow : Bool)
    (hDash : c ≠ '-') (hQ : c ≠ '?') (hColon : c ≠ ':') :
    isPrintableProp c ∧ ¬ isWhiteSpaceProp c ∧ ¬ isLineBreakProp c ∧ ¬ isIndicatorProp c →
    canStartPlainScalarBool c next inFlow = true := by
  intro ⟨_, hNotWs, hNotLb, hNotInd⟩
  unfold canStartPlainScalarBool
  have hNot : ¬(c = '-' ∨ c = '?' ∨ c = ':') := by
    rintro (rfl | rfl | rfl)
    · exact hDash rfl
    · exact hQ rfl
    · exact hColon rfl
  simp only [hNot, ite_false]
  -- Goal: (!isIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c) = true
  have hNotIndBool : isIndicatorBool c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotInd ((isIndicator_equiv c).mpr h)
  have hNotWsBool : isWhiteSpaceBool c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotWs ((isWhiteSpace_correspondence c).mpr h)
  have hNotLbBool : isLineBreakBool c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotLb ((isLineBreak_correspondence c).mpr h)
  simp [hNotIndBool, hNotWsBool, hNotLbBool]

/-! ## canStartPlainScalar (exception for `-`, `?`, `:`)

YAML §7.3.3: `-`, `?`, `:` can start plain scalars if followed by a
non-whitespace, non-line-break character (`ns-plain-safe`).
In flow context, the following character must also not be a flow indicator.
-/

/--
Exception characters in block context: accepted when the following character
is not whitespace and not a line break.
-/
theorem canStartPlainScalar_exception (c : Char) (n : Char)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':')
    (hNotWs : isWhiteSpaceBool n = false)
    (hNotLb : isLineBreakBool n = false) :
    canStartPlainScalarBool c (some n) false = true := by
  unfold canStartPlainScalarBool
  rcases hExc with rfl | rfl | rfl <;> simp [hNotWs, hNotLb]

/--
Exception characters in flow context: additionally requires the following
character is not a flow indicator.
-/
theorem canStartPlainScalar_exception_flow (c : Char) (n : Char)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':')
    (hNotWs : isWhiteSpaceBool n = false)
    (hNotLb : isLineBreakBool n = false)
    (hNotFlow : isFlowIndicatorBool n = false) :
    canStartPlainScalarBool c (some n) true = true := by
  unfold canStartPlainScalarBool
  rcases hExc with rfl | rfl | rfl <;> simp [hNotWs, hNotLb, hNotFlow]

/--
Exception characters with no following character are rejected in any context.
-/
theorem canStartPlainScalar_exception_none (c : Char) (inFlow : Bool)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':') :
    canStartPlainScalarBool c none inFlow = false := by
  unfold canStartPlainScalarBool
  rcases hExc with rfl | rfl | rfl <;> simp

end L4YAML.Proofs.CharClass
