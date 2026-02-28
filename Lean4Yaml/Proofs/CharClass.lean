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

/-! ## canStartPlainScalar (base condition)

The Grammar version captures the base exclusion rule. The Scanner version
uses the same character checks in its plain scalar scanning logic.
We prove both cases:
1. **Base**: non-exceptional characters — Grammar implies Scanner.
2. **Exception**: `-`/`?`/`:` followed by a safe character — Scanner accepts.

Note: The scanner does not expose a standalone `canStartPlainScalar` function;
it inlines this logic in `scanPlainScalar`. We define a local Bool predicate
`canStartPlainScalarBool` matching the scanner's inline logic to state the
correspondence theorems.
-/

/--
Bool predicate matching the scanner's inline plain scalar start logic.
A character can start a plain scalar if:
- It is not an indicator, not whitespace, not a line break, OR
- It is `-`, `?`, or `:` followed by a non-blank character.
-/
def canStartPlainScalarBool (c : Char) (next : Option Char) : Bool :=
  if c == '-' || c == '?' || c == ':' then
    match next with
    | some n => !Scanner.isWhiteSpace n && !Scanner.isLineBreak n
    | none => false
  else
    !Scanner.isIndicator c && !Scanner.isWhiteSpace c && !Scanner.isLineBreak c

/--
For non-exceptional characters (not `-`, `?`, `:`), `Grammar.canStartPlainScalar`
implies `canStartPlainScalarBool c next = true` for any `next`.
-/
theorem canStartPlainScalar_base (c : Char) (next : Option Char)
    (hDash : c ≠ '-') (hQ : c ≠ '?') (hColon : c ≠ ':') :
    Grammar.canStartPlainScalar c →
    canStartPlainScalarBool c next = true := by
  intro ⟨_, hNotWs, hNotLb, hNotInd⟩
  unfold canStartPlainScalarBool
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
This is the Parser-side rule that extends beyond the Grammar's base condition.
-/

/--
For the exception characters (`-`, `?`, `:`), `canStartPlainScalarBool c (some n) = true`
when the following character `n` is not whitespace and not a line break.
-/
theorem canStartPlainScalar_exception (c : Char) (n : Char)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':')
    (hNotWs : Scanner.isWhiteSpace n = false)
    (hNotLb : Scanner.isLineBreak n = false) :
    canStartPlainScalarBool c (some n) = true := by
  unfold canStartPlainScalarBool
  rcases hExc with rfl | rfl | rfl <;> simp [hNotWs, hNotLb]

/--
Exception characters with no following character are rejected.
-/
theorem canStartPlainScalar_exception_none (c : Char)
    (hExc : c = '-' ∨ c = '?' ∨ c = ':') :
    canStartPlainScalarBool c none = false := by
  unfold canStartPlainScalarBool
  rcases hExc with rfl | rfl | rfl <;> simp

end Lean4Yaml.Proofs.CharClass
