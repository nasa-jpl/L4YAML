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

-- Future work: compose this into termination proofs for each recursive parser.

end Lean4Yaml.Proofs.Termination
