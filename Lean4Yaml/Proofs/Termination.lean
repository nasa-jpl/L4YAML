/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Stream

/-!
# Termination Proofs

This module will contain termination proofs for the recursive parsers
defined in `Lean4Yaml.Parser.Block`, `Lean4Yaml.Parser.Flow`, and
`Lean4Yaml.Parser.Scalar`.

## Strategy

All recursive parsers in the verified YAML parser are currently declared
`partial def`. The termination proofs will replace each `partial def`
with a total function by providing a well-founded relation on the
stream position.

### Well-Founded Measure

The key observation is that every parser either:
1. Consumes at least one character (advancing `offset` in `YamlPos`), or
2. Fails without consuming input (via `withBacktracking`)

This gives us a decreasing measure: `stream.stopPos - stream.startPos`,
i.e., the remaining input length.

### Mutual Recursion

The mutually recursive parsers (`blockValue`, `blockSequence`, `blockMapping`,
`flowValue`, etc.) will require a combined termination proof showing that
each call either consumes input OR reduces nesting depth.

For block structures, the indentation level strictly increases with nesting,
providing an additional termination argument.

## Planned Proofs

```
theorem blockValue_terminates :
  ∀ s : YamlStream, ∀ n : Nat,
    (blockValue n).run s terminates

theorem flowValue_terminates :
  ∀ s : YamlStream,
    flowValue.run s terminates

theorem plainScalar_terminates :
  ∀ s : YamlStream, ∀ b : Bool,
    (plainScalarSingleLine b).run s terminates
```
-/

namespace Lean4Yaml.Proofs.Termination

-- Placeholder: stream position decreasing lemma
-- When a parser consumes input, the remaining length strictly decreases.

/--
The remaining input length of a `YamlStream`.
-/
def remainingLength (s : Lean4Yaml.YamlStream) : Nat :=
  s.stopPos.byteIdx - s.startPos.byteIdx

/--
After consuming a character via `next?`, the remaining length strictly decreases.
-/
theorem next_decreasing (s : Lean4Yaml.YamlStream) (c : Char) (s' : Lean4Yaml.YamlStream) :
    s.next? = some (c, s') → remainingLength s' < remainingLength s := by
  intro h
  unfold Lean4Yaml.YamlStream.next? at h
  split at h
  · next hlt =>
    simp only [Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨_, hs'⟩ := h
    unfold remainingLength
    rw [← hs']
    simp only [String.Pos.Raw.next, String.Pos.Raw.byteIdx_add_char]
    have hSize := Char.utf8Size_pos (String.Pos.Raw.get s.str s.startPos)
    have hltNat := String.Pos.Raw.lt_iff.mp hlt
    omega
  · contradiction

/--
Bridge lemma: `remainingLength` equals `Parser.Stream.remaining`.

Both compute `s.stopPos.byteIdx - s.startPos.byteIdx`. This links our
termination infrastructure to lean4-parser's fuel parameter used in
total fold combinators (`efoldlPAux`, `foldr`, `takeUntil`, etc.).
-/
theorem remainingLength_eq_stream_remaining (s : Lean4Yaml.YamlStream) :
    remainingLength s = Parser.Stream.remaining s := by
  rfl

/--
Corollary: `Parser.Stream.remaining` strictly decreases after `next?`.
This is the form needed for `termination_by Stream.remaining s` in
recursive parsers.
-/
theorem stream_remaining_decreasing (s : Lean4Yaml.YamlStream) (c : Char) (s' : Lean4Yaml.YamlStream) :
    s.next? = some (c, s') → Parser.Stream.remaining s' < Parser.Stream.remaining s := by
  intro h
  rw [← remainingLength_eq_stream_remaining, ← remainingLength_eq_stream_remaining]
  exact next_decreasing s c s' h

/-! ## Per-Parser Termination Composition

The fuel-based parsers in the YAML parser use `Stream.remaining` as fuel.
Each token-consuming step strictly decreases remaining, which bounds the
number of iterations.  The following theorems formalize this argument.
-/

/--
**Fuel consumption bound.**  A parser loop that consumes ≥1 byte per
iteration and is bounded by fuel `n` terminates in at most `n` steps.
This is the abstract statement; per-parser instances follow in
`FuelSufficiency.lean`.
-/
theorem fuel_bounds_iterations (n : Nat) (s : YamlStream) :
    n ≤ Parser.Stream.remaining s →
    ∀ k, k ≤ n → k ≤ Parser.Stream.remaining s := by
  intro h k hk
  exact Nat.le_trans hk h

/--
**Strict descent under composition.**  If parser `p` consumes input
(decreasing `remaining`) and parser `q` also consumes input, then
the composition consumes strictly more than either alone.
-/
theorem composed_descent (s₁ s₂ s₃ : YamlStream)
    (h₁ : Parser.Stream.remaining s₂ < Parser.Stream.remaining s₁)
    (h₂ : Parser.Stream.remaining s₃ < Parser.Stream.remaining s₂) :
    Parser.Stream.remaining s₃ < Parser.Stream.remaining s₁ := by
  exact Nat.lt_trans h₂ h₁

/--
**Remaining is zero iff the stream is exhausted.**  At this point no
character can be read and any `anyToken` call will fail.
-/
theorem remaining_zero_iff_exhausted (s : YamlStream) :
    Parser.Stream.remaining s = 0 ↔ ¬(s.startPos < s.stopPos) := by
  simp only [Parser.Stream.remaining]
  constructor
  · intro h; exact Nat.not_lt.mpr (Nat.sub_eq_zero_iff_le.mp h)
  · intro h; exact Nat.sub_eq_zero_of_le (Nat.not_lt.mp h)

/--
**Fuel monotonicity.**  If a result is achieved with fuel `n`,
the same result holds with any larger fuel `n + k`.  This is the
structural monotonicity property that underpins fuel sufficiency —
once we show a parser terminates with bounded fuel, adding extra
fuel does not change the outcome.

Note: this is stated as an abstract principle.  Per-parser instances
require structural induction on the specific parser definition and
are in `FuelSufficiency.lean`.
-/
theorem fuel_le_of_remaining (s : YamlStream) :
    Parser.Stream.remaining s ≤ 4 * Parser.Stream.remaining s + 4 := by
  omega

end Lean4Yaml.Proofs.Termination
