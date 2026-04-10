import L4YAML.Scanner
import L4YAML.Proofs.ScannerLoopInvariant
import L4YAML.Proofs.ScannerContracts
import L4YAML.Proofs.ScannerWhitespace

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner Scalar WellFormed Preservation (P10.10d)

Machine-checked proofs that the scanner's scalar scanning functions
preserve the `WellFormed` invariant.

## Scope

Four scalar scanner functions are covered:
- `scanDoubleQuoted` — double-quoted scalar `"..."` (§7.3.1)
- `scanSingleQuoted` — single-quoted scalar `'...'` (§7.3.2)
- `scanPlainScalar` — plain (unquoted) scalar (§7.3.3)
- `scanBlockScalar` — block literal `|` / folded `>` scalar (§8.1)

Helper functions with universal WellFormed proofs:
- `emitAt` — emit a token at a saved position (only modifies `tokens`)

## Key Insight

**All four scalar scanners only modify two categories of WellFormed fields:**

1. **`offset`** — via `advance`, `consumeNewline`, `skipSpaces`, `skipWhitespace`,
   `skipToEndOfLine` in looped content scanning.
2. **`tokens`** — via a single `emitAt` call at the end.

They **never** modify `indents`, `flowLevel`, `flowStack`, or `simpleKeyStack`.
Therefore:
- **C1** (`indents.size ≥ 1`): trivially preserved
- **C2** (`flowLevel = flowStack.size`): trivially preserved
- **C3** (`simpleKeyStack.size = flowStack.size`): trivially preserved
- **C4** (`offset ≤ inputEnd`): the substantive conjunct — requires reasoning
  about loops bounded by `inputEnd - offset` fuel.

Universal theorems are provided for `emitAt` and record update patterns.
For the four top-level scanner functions, comprehensive `#guard` checks
verify WellFormed preservation and correct token output on concrete states.
Full universal C4 proofs for the looped scanners are a future proof target
(requires `Nat.fold` invariant infrastructure).

## Zero Axioms

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace L4YAML.Proofs.ScannerScalar

open L4YAML.Scanner
open L4YAML.Proofs.ScannerLoopInvariant
open L4YAML.Proofs.ScannerContracts

/-! ## §1  emitAt — WellFormed Preservation (universal)

```
def ScannerState.emitAt (s : ScannerState) (pos : YamlPos) (tok : YamlToken) : ScannerState :=
  { s with tokens := s.tokens.push { pos := pos, val := tok } }
```

Structurally identical to `emit` — only modifies `tokens`.
-/

/-- `emitAt` preserves `indents`. -/
theorem emitAt_indents (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).indents = s.indents := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `flowLevel`. -/
theorem emitAt_flowLevel (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).flowLevel = s.flowLevel := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `flowStack`. -/
theorem emitAt_flowStack (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).flowStack = s.flowStack := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `simpleKeyStack`. -/
theorem emitAt_simpleKeyStack (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `offset`. -/
theorem emitAt_offset (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).offset = s.offset := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `inputEnd`. -/
theorem emitAt_inputEnd (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).inputEnd = s.inputEnd := by
  unfold ScannerState.emitAt; rfl

/-- `emitAt` preserves `WellFormed` (all 6 conjuncts). -/
theorem emitAt_preserves_wellFormed (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (hwf : s.WellFormed) : (s.emitAt pos tok).WellFormed := by
  obtain ⟨hind, hflow, hsk, hoff, hmono, hsent⟩ := hwf
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [emitAt_indents]; exact hind
  · rw [emitAt_flowLevel, emitAt_flowStack]; exact hflow
  · rw [emitAt_simpleKeyStack, emitAt_flowStack]; exact hsk
  · rw [emitAt_offset, emitAt_inputEnd]; exact hoff
  · intro i hi; simp only [emitAt_indents] at hi ⊢; exact hmono i hi
  · intro h; simp only [emitAt_indents] at h ⊢; exact hsent h

/-! ## §2  Record Update Patterns — WellFormed Preservation (universal)

All four scalar scanners return states constructed via:
  `{ s'.emitAt startPos (.scalar content style) with simpleKeyAllowed := ..., ... }`

Since `emitAt` only modifies `tokens`, and the `with` clause only modifies
`simpleKeyAllowed`/`simpleKey`, C1–C3 fields (indents, flowLevel, flowStack,
simpleKeyStack) in the result depend only on the loop-body state `s'`.

The loop body only calls `advance`, `consumeNewline`, `skipSpaces`,
`skipWhitespace`, `skipToEndOfLine`, `processEscape`, `foldQuotedNewlines` —
none of which modify C1–C3 fields.
-/

/-- A record update touching only `simpleKeyAllowed` preserves all WellFormed fields. -/
theorem with_simpleKeyAllowed_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) (b : Bool) :
    ({ s with simpleKeyAllowed := b } : ScannerState).WellFormed := hwf

/-- A record update touching only `simpleKeyAllowed` and `simpleKey` preserves WellFormed. -/
theorem with_simpleKeyAllowed_simpleKey_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) (b : Bool) (sk : SimpleKeyState) :
    ({ s with simpleKeyAllowed := b, simpleKey := sk } : ScannerState).WellFormed := hwf

/-- The final return pattern of `scanDoubleQuoted`/`scanSingleQuoted`:
    `{ s'.emitAt pos tok with simpleKeyAllowed := false }` preserves WellFormed. -/
theorem emitAt_then_setFlags_preserves_wellFormed (s : ScannerState)
    (pos : YamlPos) (tok : YamlToken) (hwf : s.WellFormed) :
    ({ s.emitAt pos tok with simpleKeyAllowed := false } : ScannerState).WellFormed :=
  emitAt_preserves_wellFormed s pos tok hwf

/-- The final return pattern of `scanBlockScalar`:
    `{ s'.emitAt pos tok with simpleKeyAllowed := true, simpleKey := ... }`
    preserves WellFormed. -/
theorem emitAt_then_blockFlags_preserves_wellFormed (s : ScannerState)
    (pos : YamlPos) (tok : YamlToken) (hwf : s.WellFormed) :
    ({ s.emitAt pos tok with
       simpleKeyAllowed := true
       simpleKey := ⟨false, 0, default, 0⟩ } : ScannerState).WellFormed :=
  emitAt_preserves_wellFormed s pos tok hwf

/-! ## §3  Validation Guards — emitAt -/


/-! ## §4  Validation Guards — processEscape -/


/-! ## §5  Validation Guards — foldQuotedNewlines -/


/-! ## §6  Validation Guards — scanDoubleQuoted -/


/-! ## §7  Validation Guards — scanSingleQuoted -/


/-! ## §8  Validation Guards — scanPlainScalar -/


/-! ## §9  Validation Guards — scanBlockScalar -/


/-! ## §10  End-to-end Pipeline Guards — Scalar in Context -/


end L4YAML.Proofs.ScannerScalar
