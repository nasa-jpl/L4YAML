import Lean4Yaml.Grammar
import Lean4Yaml.Scanner

/-!
# Character Classification Correspondence Proofs (Layer 1c)

This module proves that the `Prop`-valued character classifiers in
`Grammar.lean` correspond exactly to the `Bool`-valued classifiers
in `Scanner.lean`.

Each theorem states: `Grammar.X c ↔ Scanner.X c = true`.

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

namespace Lean4Yaml.Proofs.CharClass

/-! ## isLineBreak: Grammar.isLineBreak ↔ Scanner.isLineBreak -/

/--
The Grammar specification of line breaks matches the scanner implementation.

- Grammar (Prop): `c == '\n' ∨ c == '\r'`
- Scanner (Bool):  `c == '\n' || c == '\r'`
-/
theorem isLineBreak_correspondence (c : Char) :
    Grammar.isLineBreak c ↔ Scanner.isLineBreak c = true := by
  simp only [Grammar.isLineBreak, Scanner.isLineBreak, Bool.or_eq_true]

/-! ## isWhiteSpace: Grammar.isWhiteSpace ↔ Scanner.isWhiteSpace -/

/--
The Grammar specification of white space matches the scanner implementation.

- Grammar (Prop): `c == ' ' ∨ c == '\t'`
- Scanner (Bool):  `c == ' ' || c == '\t'`
-/
theorem isWhiteSpace_correspondence (c : Char) :
    Grammar.isWhiteSpace c ↔ Scanner.isWhiteSpace c = true := by
  simp only [Grammar.isWhiteSpace, Scanner.isWhiteSpace, Bool.or_eq_true]

/-! ## isIndentChar: Grammar.isIndentChar ↔ (c == ' ') -/

/--
The Grammar specification of indentation characters matches the parser check.

- Grammar (Prop): `c == ' '`
- Parser: uses inline `c == ' '` checks (no dedicated Bool function)

We prove the Grammar definition is equivalent to `(c == ' ') = true`.
-/
theorem isIndentChar_iff (c : Char) :
    Grammar.isIndentChar c ↔ (c == ' ') = true := by
  simp only [Grammar.isIndentChar]

/-! ## isFlowIndicator: Grammar.isFlowIndicator ↔ Scanner.isFlowIndicator -/

/--
The Grammar specification of flow indicators matches the scanner implementation.

Both use `c ∈ [',', '[', ']', '{', '}']`. Since both Grammar and Scanner
definitions expand to the same `List.elem` check, `Iff.rfl` closes the goal
after unfolding.
-/
theorem isFlowIndicator_correspondence (c : Char) :
    Grammar.isFlowIndicator c ↔ Scanner.isFlowIndicator c = true := by
  unfold Grammar.isFlowIndicator Scanner.isFlowIndicator
  simp [List.mem_cons, Bool.or_eq_true]

/-! ## isIndicator: Grammar indicators ↔ Scanner.isIndicator -/

/--
The full indicator list used in `Grammar.canStartPlainScalar` matches
`Scanner.isIndicator`. Both expand to `List.elem` on the same character list.
-/
theorem isIndicator_equiv (c : Char) :
    (c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
          '\'', '"', '%', '@', '`'] : Prop) ↔
    Scanner.isIndicator c = true := by
  unfold Scanner.isIndicator
  simp [List.mem_cons, Bool.or_eq_true]

/-! ## canStartPlainScalar: Grammar.canStartPlainScalar ↔ Scanner.canStartPlainScalar

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
For non-exceptional characters (not `-`, `?`, `:`), `Grammar.canStartPlainScalar`
implies `Scanner.canStartPlainScalar c next inFlow = true` for any `next` and `inFlow`.

The `else` branch of `Scanner.canStartPlainScalar` is context-independent:
`!isIndicator c && !isWhiteSpace c && !isLineBreak c`.
-/
theorem canStartPlainScalar_base (c : Char) (next : Option Char) (inFlow : Bool)
    (hDash : c ≠ '-') (hQ : c ≠ '?') (hColon : c ≠ ':') :
    Grammar.canStartPlainScalar c →
    Scanner.canStartPlainScalar c next inFlow = true := by
  intro ⟨_, hNotWs, hNotLb, hNotInd⟩
  unfold Scanner.canStartPlainScalar
  have h1 : (c == '-') = false := Bool.eq_false_iff.mpr (by simpa using hDash)
  have h2 : (c == '?') = false := Bool.eq_false_iff.mpr (by simpa using hQ)
  have h3 : (c == ':') = false := Bool.eq_false_iff.mpr (by simpa using hColon)
  simp only [h1, h2, h3, Bool.false_or]
  -- Goal: (!Scanner.isIndicator c && !Scanner.isWhiteSpace c && !Scanner.isLineBreak c) = true
  have hNotIndBool : Scanner.isIndicator c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotInd ((isIndicator_equiv c).mpr h)
  have hNotWsBool : Scanner.isWhiteSpace c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotWs ((isWhiteSpace_correspondence c).mpr h)
  have hNotLbBool : Scanner.isLineBreak c = false := by
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
    (hNotWs : Scanner.isWhiteSpace n = false)
    (hNotLb : Scanner.isLineBreak n = false) :
    Scanner.canStartPlainScalar c (some n) false = true := by
  unfold Scanner.canStartPlainScalar
  rcases hExc with rfl | rfl | rfl <;> simp [hNotWs, hNotLb]

/--
Exception characters in flow context: additionally requires the following
character is not a flow indicator.
-/
theorem canStartPlainScalar_exception_flow (c : Char) (n : Char)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':')
    (hNotWs : Scanner.isWhiteSpace n = false)
    (hNotLb : Scanner.isLineBreak n = false)
    (hNotFlow : Scanner.isFlowIndicator n = false) :
    Scanner.canStartPlainScalar c (some n) true = true := by
  unfold Scanner.canStartPlainScalar
  rcases hExc with rfl | rfl | rfl <;> simp [hNotWs, hNotLb, hNotFlow]

/--
Exception characters with no following character are rejected in any context.
-/
theorem canStartPlainScalar_exception_none (c : Char) (inFlow : Bool)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':') :
    Scanner.canStartPlainScalar c none inFlow = false := by
  unfold Scanner.canStartPlainScalar
  rcases hExc with rfl | rfl | rfl <;> simp

end Lean4Yaml.Proofs.CharClass
