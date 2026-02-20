import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators

/-!
# Character Classification Correspondence Proofs (Layer 1c)

This module proves that the `Prop`-valued character classifiers in
`Grammar.lean` correspond exactly to the `Bool`-valued classifiers
in `Parser/Combinators.lean`.

Each theorem states: `Grammar.X c ↔ Parse.X c = true`.

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

/-! ## isLineBreak: Grammar.isLineBreak ↔ Parse.isLineBreak -/

/--
The Grammar specification of line breaks matches the parser implementation.

- Grammar (Prop): `c == '\n' ∨ c == '\r'`
- Parser (Bool):  `c == '\n' || c == '\r'`
-/
theorem isLineBreak_correspondence (c : Char) :
    Grammar.isLineBreak c ↔ Parse.isLineBreak c = true := by
  simp only [Grammar.isLineBreak, Parse.isLineBreak, Bool.or_eq_true]

/-! ## isWhiteSpace: Grammar.isWhiteSpace ↔ Parse.isWhiteSpace -/

/--
The Grammar specification of white space matches the parser implementation.

- Grammar (Prop): `c == ' ' ∨ c == '\t'`
- Parser (Bool):  `c == ' ' || c == '\t'`
-/
theorem isWhiteSpace_correspondence (c : Char) :
    Grammar.isWhiteSpace c ↔ Parse.isWhiteSpace c = true := by
  simp only [Grammar.isWhiteSpace, Parse.isWhiteSpace, Bool.or_eq_true]

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

/-! ## isFlowIndicator: Grammar.isFlowIndicator ↔ Parse.isFlowIndicator -/

/--
The Grammar specification of flow indicators matches the parser implementation.

Both use `c ∈ [',', '[', ']', '{', '}']`. Since both Grammar and Parser
definitions expand to the same `List.elem` check, `Iff.rfl` closes the goal
after unfolding.
-/
theorem isFlowIndicator_correspondence (c : Char) :
    Grammar.isFlowIndicator c ↔ Parse.isFlowIndicator c = true := by
  unfold Grammar.isFlowIndicator Parse.isFlowIndicator
  simp [List.mem_cons, Bool.or_eq_true]

/-! ## isIndicator: Grammar indicators ↔ Parse.isIndicator -/

/--
The full indicator list used in `Grammar.canStartPlainScalar` matches
`Parse.isIndicator`. Both expand to `List.elem` on the same character list.
-/
theorem isIndicator_equiv (c : Char) :
    (c ∈ ['-', '?', ':', ',', '[', ']', '{', '}', '#', '&', '*', '!', '|', '>',
          '\'', '"', '%', '@', '`'] : Prop) ↔
    Parse.isIndicator c = true := by
  unfold Parse.isIndicator
  simp [List.mem_cons, Bool.or_eq_true]

/-! ## canStartPlainScalar (base condition)

The Grammar version captures the base exclusion rule. The Parser version
adds the `-`/`?`/`:` exception with context. We prove the base case:
when `c` is not one of the three exception characters, Grammar implies Parser.
-/

/--
For non-exceptional characters (not `-`, `?`, `:`), `Grammar.canStartPlainScalar`
implies `Parse.canStartPlainScalar c next = true` for any `next`.
-/
theorem canStartPlainScalar_base (c : Char) (next : Option Char)
    (hDash : c ≠ '-') (hQ : c ≠ '?') (hColon : c ≠ ':') :
    Grammar.canStartPlainScalar c →
    Parse.canStartPlainScalar c next = true := by
  intro ⟨_, hNotWs, hNotLb, hNotInd⟩
  unfold Parse.canStartPlainScalar
  have h1 : (c == '-') = false := Bool.eq_false_iff.mpr (by simpa using hDash)
  have h2 : (c == '?') = false := Bool.eq_false_iff.mpr (by simpa using hQ)
  have h3 : (c == ':') = false := Bool.eq_false_iff.mpr (by simpa using hColon)
  simp only [h1, h2, h3, Bool.false_or]
  -- Goal: (!Parse.isIndicator c && !Parse.isWhiteSpace c && !Parse.isLineBreak c) = true
  have hNotIndBool : Parse.isIndicator c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotInd ((isIndicator_equiv c).mpr h)
  have hNotWsBool : Parse.isWhiteSpace c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotWs ((isWhiteSpace_correspondence c).mpr h)
  have hNotLbBool : Parse.isLineBreak c = false := by
    rw [Bool.eq_false_iff]
    intro h
    exact hNotLb ((isLineBreak_correspondence c).mpr h)
  simp [hNotIndBool, hNotWsBool, hNotLbBool]

end Lean4Yaml.Proofs.CharClass
