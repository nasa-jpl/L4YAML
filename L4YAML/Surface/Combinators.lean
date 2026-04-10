/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Grammar Combinators for Surface Syntax

Generic combinators for composing YAML surface syntax productions.
Each production is a relation `SurfPos → SurfPos → Prop` where `SurfPos`
carries the remaining input characters and the current column number.

Column tracking is essential for YAML's indentation-sensitive grammar:
- Line breaks reset column to 0
- Each consumed character increments column by 1
- `s-indent(n)` requires consuming `n` spaces at column 0 → n
- `c-forbidden` requires `---`/`...` at column 0
-/

set_option autoImplicit false

namespace L4YAML.Surface

/-- Surface syntax position: remaining characters + current column (0-indexed).
    Column resets to 0 after line breaks, increments by 1 per character consumed. -/
structure SurfPos where
  chars : List Char
  col : Nat
  deriving Repr, Inhabited

/-- Match a single character satisfying predicate `p`. Column increments by 1. -/
inductive GChar (p : Char → Prop) : SurfPos → SurfPos → Prop where
  | mk (c : Char) (rest : List Char) (col : Nat) (h : p c) :
      GChar p ⟨c :: rest, col⟩ ⟨rest, col + 1⟩

/-- Match a specific literal character. Column increments by 1. -/
inductive GLit (ch : Char) : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) (col : Nat) :
      GLit ch ⟨ch :: rest, col⟩ ⟨rest, col + 1⟩

/-- Sequential composition: match P then Q. -/
inductive GSeq (P Q : SurfPos → SurfPos → Prop) : SurfPos → SurfPos → Prop where
  | mk (s₁ s₂ s₃ : SurfPos) : P s₁ s₂ → Q s₂ s₃ → GSeq P Q s₁ s₃

/-- Three-way sequential composition. -/
inductive GSeq3 (P Q R : SurfPos → SurfPos → Prop) : SurfPos → SurfPos → Prop where
  | mk (s₁ s₂ s₃ s₄ : SurfPos) : P s₁ s₂ → Q s₂ s₃ → R s₃ s₄ → GSeq3 P Q R s₁ s₄

/-- Alternative: match P or Q. -/
inductive GAlt (P Q : SurfPos → SurfPos → Prop) : SurfPos → SurfPos → Prop where
  | left  (s s' : SurfPos) : P s s' → GAlt P Q s s'
  | right (s s' : SurfPos) : Q s s' → GAlt P Q s s'

/-- Zero or more repetitions of P. -/
inductive GStar (P : SurfPos → SurfPos → Prop) : SurfPos → SurfPos → Prop where
  | nil  (s : SurfPos) : GStar P s s
  | cons (s₁ s₂ s₃ : SurfPos) : P s₁ s₂ → GStar P s₂ s₃ → GStar P s₁ s₃

/-- One or more repetitions of P. -/
inductive GPlus (P : SurfPos → SurfPos → Prop) : SurfPos → SurfPos → Prop where
  | mk (s₁ s₂ s₃ : SurfPos) : P s₁ s₂ → GStar P s₂ s₃ → GPlus P s₁ s₃

/-- Optional: match P or nothing (epsilon). -/
inductive GOpt (P : SurfPos → SurfPos → Prop) : SurfPos → SurfPos → Prop where
  | none (s : SurfPos) : GOpt P s s
  | some (s s' : SurfPos) : P s s' → GOpt P s s'

/-- Epsilon: zero-width match. -/
inductive GEps : SurfPos → SurfPos → Prop where
  | mk (s : SurfPos) : GEps s s

/-- End of input assertion. -/
def atEnd (s : SurfPos) : Prop := s.chars = []

/-- Consume all remaining characters (used at stream end). -/
inductive GConsumeAll : SurfPos → SurfPos → Prop where
  | nil (col : Nat) : GConsumeAll ⟨[], col⟩ ⟨[], col⟩
  | cons (c : Char) (rest : List Char) (col : Nat) (s' : SurfPos) :
      GConsumeAll ⟨rest, col + 1⟩ s' → GConsumeAll ⟨c :: rest, col⟩ s'

/-- Negative lookahead: P does not match at this position. -/
def GNot (P : SurfPos → SurfPos → Prop) (s : SurfPos) : Prop :=
  ∀ s' : SurfPos, ¬ P s s'

end L4YAML.Surface
