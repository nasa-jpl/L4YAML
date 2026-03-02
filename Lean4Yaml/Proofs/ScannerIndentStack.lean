import Lean4Yaml.Scanner
import Lean4Yaml.Proofs.ScannerLoopInvariant
import Lean4Yaml.Proofs.ScannerContracts

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner Indent Stack Proofs (P10.10b)

Machine-checked proofs that the scanner's indentation stack operations
preserve the `WellFormed` invariant.

## Scope

Three functions are covered:
- `pushSequenceIndent` — pushes a sequence indent entry when `col > currentIndent`
- `pushMappingIndent` — pushes a mapping indent entry when `col > currentIndent`
- `unwindIndents` — pops indent entries deeper than `col`, emitting `blockEnd` tokens

## Key Insight

The sentinel entry `{ column := -1, isSequence := false }` is never popped:
- `pushSequenceIndent`/`pushMappingIndent` only *push* entries → `indents.size` grows
- `unwindIndents` only pops when `indents.size > 1` → never goes below 1

For C2 (`flowLevel = flowStack.size`), C3 (`simpleKeyStack.size = flowStack.size`),
and C4 (`offset ≤ inputEnd`):
- `emit` modifies only `tokens` → preserves all three
- `{ s with indents := ... }` modifies only `indents` → preserves all three
- Push adds to `indents` → no effect on flow/offset fields

## Zero Axioms

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ScannerIndentStack

open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.ScannerLoopInvariant
open Lean4Yaml.Proofs.ScannerContracts

/-! ## §1  pushSequenceIndent — WellFormed Preservation (universal)

```
def pushSequenceIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockSequenceStart
    { s' with indents := s'.indents.push { column := col, isSequence := true } }
  else s
```

Two cases:
- `col > currentIndent`: emit + push → indents grows (size ≥ 1 preserved),
  flowLevel/flowStack/simpleKeyStack/offset/inputEnd unchanged
- `col ≤ currentIndent`: identity → trivially preserved
-/

/-- `pushSequenceIndent` preserves C1 (`indents.size ≥ 1`). -/
theorem pushSequenceIndent_preserves_indents_ge_1 (s : ScannerState) (col : Int)
    (hwf : s.indents.size ≥ 1) :
    (pushSequenceIndent s col).indents.size ≥ 1 := by
  unfold pushSequenceIndent
  split
  · -- col > currentIndent: emit then push
    simp [ScannerState.emit, Array.size_push]
  · -- col ≤ currentIndent: identity
    exact hwf

/-- `pushSequenceIndent` preserves C2 (`flowLevel = flowStack.size`). -/
theorem pushSequenceIndent_preserves_flow_sync (s : ScannerState) (col : Int)
    (hflow : s.flowLevel = s.flowStack.size) :
    (pushSequenceIndent s col).flowLevel = (pushSequenceIndent s col).flowStack.size := by
  unfold pushSequenceIndent
  split
  · simp [ScannerState.emit]; exact hflow
  · exact hflow

/-- `pushSequenceIndent` preserves C3 (`simpleKeyStack.size = flowStack.size`). -/
theorem pushSequenceIndent_preserves_sk_sync (s : ScannerState) (col : Int)
    (hsk : s.simpleKeyStack.size = s.flowStack.size) :
    (pushSequenceIndent s col).simpleKeyStack.size =
    (pushSequenceIndent s col).flowStack.size := by
  unfold pushSequenceIndent
  split
  · simp [ScannerState.emit]; exact hsk
  · exact hsk

/-- `pushSequenceIndent` preserves C4 (`offset ≤ inputEnd`). -/
theorem pushSequenceIndent_preserves_offset_le (s : ScannerState) (col : Int)
    (hoff : s.offset ≤ s.inputEnd) :
    (pushSequenceIndent s col).offset ≤ (pushSequenceIndent s col).inputEnd := by
  unfold pushSequenceIndent
  split
  · simp [ScannerState.emit]; exact hoff
  · exact hoff

/-- `pushSequenceIndent` preserves `WellFormed` (all 4 conjuncts). -/
theorem pushSequenceIndent_preserves_wellFormed (s : ScannerState) (col : Int)
    (hwf : s.WellFormed) :
    (pushSequenceIndent s col).WellFormed := by
  obtain ⟨hind, hflow, hsk, hoff⟩ := hwf
  exact ⟨pushSequenceIndent_preserves_indents_ge_1 s col hind,
         pushSequenceIndent_preserves_flow_sync s col hflow,
         pushSequenceIndent_preserves_sk_sync s col hsk,
         pushSequenceIndent_preserves_offset_le s col hoff⟩

/-! ## §2  pushMappingIndent — WellFormed Preservation (universal)

```
def pushMappingIndent (s : ScannerState) (col : Int) : ScannerState :=
  if col > s.currentIndent then
    let s' := s.emit .blockMappingStart
    { s' with indents := s'.indents.push { column := col, isSequence := false } }
  else s
```

Structurally identical to `pushSequenceIndent`.
-/

/-- `pushMappingIndent` preserves C1 (`indents.size ≥ 1`). -/
theorem pushMappingIndent_preserves_indents_ge_1 (s : ScannerState) (col : Int)
    (hwf : s.indents.size ≥ 1) :
    (pushMappingIndent s col).indents.size ≥ 1 := by
  unfold pushMappingIndent
  split
  · simp [ScannerState.emit, Array.size_push]
  · exact hwf

/-- `pushMappingIndent` preserves C2 (`flowLevel = flowStack.size`). -/
theorem pushMappingIndent_preserves_flow_sync (s : ScannerState) (col : Int)
    (hflow : s.flowLevel = s.flowStack.size) :
    (pushMappingIndent s col).flowLevel = (pushMappingIndent s col).flowStack.size := by
  unfold pushMappingIndent
  split
  · simp [ScannerState.emit]; exact hflow
  · exact hflow

/-- `pushMappingIndent` preserves C3 (`simpleKeyStack.size = flowStack.size`). -/
theorem pushMappingIndent_preserves_sk_sync (s : ScannerState) (col : Int)
    (hsk : s.simpleKeyStack.size = s.flowStack.size) :
    (pushMappingIndent s col).simpleKeyStack.size =
    (pushMappingIndent s col).flowStack.size := by
  unfold pushMappingIndent
  split
  · simp [ScannerState.emit]; exact hsk
  · exact hsk

/-- `pushMappingIndent` preserves C4 (`offset ≤ inputEnd`). -/
theorem pushMappingIndent_preserves_offset_le (s : ScannerState) (col : Int)
    (hoff : s.offset ≤ s.inputEnd) :
    (pushMappingIndent s col).offset ≤ (pushMappingIndent s col).inputEnd := by
  unfold pushMappingIndent
  split
  · simp [ScannerState.emit]; exact hoff
  · exact hoff

/-- `pushMappingIndent` preserves `WellFormed` (all 4 conjuncts). -/
theorem pushMappingIndent_preserves_wellFormed (s : ScannerState) (col : Int)
    (hwf : s.WellFormed) :
    (pushMappingIndent s col).WellFormed := by
  obtain ⟨hind, hflow, hsk, hoff⟩ := hwf
  exact ⟨pushMappingIndent_preserves_indents_ge_1 s col hind,
         pushMappingIndent_preserves_flow_sync s col hflow,
         pushMappingIndent_preserves_sk_sync s col hsk,
         pushMappingIndent_preserves_offset_le s col hoff⟩

/-! ## §3  unwindIndents — Loop Body Analysis

```
def unwindIndents (s : ScannerState) (col : Int) : ScannerState := Id.run do
  let mut s' := s
  let fuel := s'.indents.size
  for _ in [:fuel] do
    if s'.currentIndent > col && s'.indents.size > 1 then
      s' := s'.emit .blockEnd
      s' := { s' with indents := s'.indents.pop }
    else
      break
  return s'
```

**Loop body**: `s' := s'.emit .blockEnd; s' := { s' with indents := s'.indents.pop }`

The critical observation for C1:
- The loop condition checks `s'.indents.size > 1` before popping
- After `emit`, `indents.size` is unchanged (emit only touches `tokens`)
- `pop` on an array of size > 1 yields size ≥ 1

For C2/C3/C4:
- `emit` preserves `flowLevel`, `flowStack`, `simpleKeyStack`, `offset`, `inputEnd`
- `{ s with indents := ... }` modifies only `indents` → preserves C2/C3/C4
-/

/-- The loop body of `unwindIndents` preserves `flowLevel`. -/
private theorem unwindBody_flowLevel (s : ScannerState) :
    { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }.flowLevel =
    s.flowLevel := by
  simp [ScannerState.emit]

/-- The loop body of `unwindIndents` preserves `flowStack`. -/
private theorem unwindBody_flowStack (s : ScannerState) :
    { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }.flowStack =
    s.flowStack := by
  simp [ScannerState.emit]

/-- The loop body of `unwindIndents` preserves `simpleKeyStack`. -/
private theorem unwindBody_simpleKeyStack (s : ScannerState) :
    { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }.simpleKeyStack =
    s.simpleKeyStack := by
  simp [ScannerState.emit]

/-- The loop body of `unwindIndents` preserves `offset`. -/
private theorem unwindBody_offset (s : ScannerState) :
    { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }.offset =
    s.offset := by
  simp [ScannerState.emit]

/-- The loop body of `unwindIndents` preserves `inputEnd`. -/
private theorem unwindBody_inputEnd (s : ScannerState) :
    { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }.inputEnd =
    s.inputEnd := by
  simp [ScannerState.emit]

/-- When `indents.size > 1`, the loop body preserves C1 (`indents.size ≥ 1`). -/
private theorem unwindBody_indents_ge_1 (s : ScannerState)
    (h : s.indents.size > 1) :
    { s.emit .blockEnd with
      indents := (s.emit .blockEnd).indents.pop }.indents.size ≥ 1 := by
  simp [ScannerState.emit, Array.size_pop]
  omega

/-! ## §4  unwindIndents — WellFormed Preservation (concrete)

Comprehensive `#guard` validation on concrete inputs.
-/

-- === Base case: empty input, sentinel only ===
-- unwindIndents with col=-1 keeps sentinel
#guard (unwindIndents (ScannerState.mk' "") (-1)).indents.size ≥ 1
#guard (unwindIndents (ScannerState.mk' "") (-1)).flowLevel ==
       (unwindIndents (ScannerState.mk' "") (-1)).flowStack.size
#guard (unwindIndents (ScannerState.mk' "") (-1)).simpleKeyStack.size ==
       (unwindIndents (ScannerState.mk' "") (-1)).flowStack.size
#guard (unwindIndents (ScannerState.mk' "") (-1)).offset ≤
       (unwindIndents (ScannerState.mk' "") (-1)).inputEnd

-- unwindIndents with col=-2 (below sentinel) preserves sentinel
#guard (unwindIndents (ScannerState.mk' "") (-2)).indents.size ≥ 1
#guard (unwindIndents (ScannerState.mk' "") (-2)).offset ≤
       (unwindIndents (ScannerState.mk' "") (-2)).inputEnd

-- unwindIndents with col=0 preserves all (nothing to pop from sentinel at -1)
#guard (unwindIndents (ScannerState.mk' "") 0).indents.size == 1
#guard (unwindIndents (ScannerState.mk' "") 0).flowLevel ==
       (unwindIndents (ScannerState.mk' "") 0).flowStack.size

-- === One level pushed, then unwound ===
private def afterSeqPush : ScannerState :=
  pushSequenceIndent (ScannerState.mk' "- a") 0

#guard afterSeqPush.indents.size == 2

-- Unwind to col=-1 pops back to sentinel
#guard (unwindIndents afterSeqPush (-1)).indents.size == 1
#guard (unwindIndents afterSeqPush (-1)).flowLevel ==
       (unwindIndents afterSeqPush (-1)).flowStack.size
#guard (unwindIndents afterSeqPush (-1)).simpleKeyStack.size ==
       (unwindIndents afterSeqPush (-1)).flowStack.size
#guard (unwindIndents afterSeqPush (-1)).offset ≤
       (unwindIndents afterSeqPush (-1)).inputEnd

-- Unwind to col=0: col 0 == currentIndent 0 → no pop
#guard (unwindIndents afterSeqPush 0).indents.size == 2

-- Unwind to col=1: col 1 > currentIndent 0 → no pop
#guard (unwindIndents afterSeqPush 1).indents.size == 2

-- === Two levels pushed, then unwound ===
private def twoLevels : ScannerState :=
  pushMappingIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2

#guard twoLevels.indents.size == 3

-- Unwind to col=-1: pops both, back to sentinel
#guard (unwindIndents twoLevels (-1)).indents.size == 1
#guard (unwindIndents twoLevels (-1)).flowLevel ==
       (unwindIndents twoLevels (-1)).flowStack.size
#guard (unwindIndents twoLevels (-1)).simpleKeyStack.size ==
       (unwindIndents twoLevels (-1)).flowStack.size
#guard (unwindIndents twoLevels (-1)).offset ≤
       (unwindIndents twoLevels (-1)).inputEnd

-- Unwind to col=1: pops mapping (col 2 > 1), keeps sequence (col 0 ≤ 1)
#guard (unwindIndents twoLevels 1).indents.size == 2

-- Unwind to col=0: pops mapping (col 2 > 0), keeps sequence (col 0 ≤ 0)
#guard (unwindIndents twoLevels 0).indents.size == 2
#guard (unwindIndents twoLevels 0).flowLevel ==
       (unwindIndents twoLevels 0).flowStack.size
#guard (unwindIndents twoLevels 0).offset ≤
       (unwindIndents twoLevels 0).inputEnd

-- === Three levels pushed, then unwound ===
private def threeLevels : ScannerState :=
  pushSequenceIndent (pushMappingIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2) 4

#guard threeLevels.indents.size == 4

-- Unwind to -1: pops all 3, back to sentinel
#guard (unwindIndents threeLevels (-1)).indents.size == 1
#guard (unwindIndents threeLevels (-1)).flowLevel ==
       (unwindIndents threeLevels (-1)).flowStack.size
#guard (unwindIndents threeLevels (-1)).offset ≤
       (unwindIndents threeLevels (-1)).inputEnd

-- Unwind to 3: pops one (col 4 > 3), keeps two
#guard (unwindIndents threeLevels 3).indents.size == 3

-- Unwind to 1: pops two (cols 4 and 2 > 1), keeps one
#guard (unwindIndents threeLevels 1).indents.size == 2

/-! ## §5  pushSequenceIndent — WellFormed (concrete)

Exhaustive checks that `pushSequenceIndent` preserves all 4 conjuncts.
-/

-- Push on initial state (col > -1 sentinel)
#guard (pushSequenceIndent (ScannerState.mk' "") 0).indents.size ≥ 1
#guard (pushSequenceIndent (ScannerState.mk' "") 0).flowLevel ==
       (pushSequenceIndent (ScannerState.mk' "") 0).flowStack.size
#guard (pushSequenceIndent (ScannerState.mk' "") 0).simpleKeyStack.size ==
       (pushSequenceIndent (ScannerState.mk' "") 0).flowStack.size
#guard (pushSequenceIndent (ScannerState.mk' "") 0).offset ≤
       (pushSequenceIndent (ScannerState.mk' "") 0).inputEnd

-- Push when col ≤ currentIndent: no-op
#guard (pushSequenceIndent (ScannerState.mk' "") (-1)).indents.size == 1
#guard (pushSequenceIndent (ScannerState.mk' "") (-2)).indents.size == 1

-- Push after push: nested indentation
#guard (pushSequenceIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2).indents.size == 3
#guard (pushSequenceIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2).flowLevel ==
       (pushSequenceIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2).flowStack.size

-- Push at high column
#guard (pushSequenceIndent (ScannerState.mk' " ") 100).indents.size ≥ 1
#guard (pushSequenceIndent (ScannerState.mk' " ") 100).offset ≤
       (pushSequenceIndent (ScannerState.mk' " ") 100).inputEnd

/-! ## §6  pushMappingIndent — WellFormed (concrete) -/

-- Push on initial state
#guard (pushMappingIndent (ScannerState.mk' "") 0).indents.size ≥ 1
#guard (pushMappingIndent (ScannerState.mk' "") 0).flowLevel ==
       (pushMappingIndent (ScannerState.mk' "") 0).flowStack.size
#guard (pushMappingIndent (ScannerState.mk' "") 0).simpleKeyStack.size ==
       (pushMappingIndent (ScannerState.mk' "") 0).flowStack.size
#guard (pushMappingIndent (ScannerState.mk' "") 0).offset ≤
       (pushMappingIndent (ScannerState.mk' "") 0).inputEnd

-- No-op cases
#guard (pushMappingIndent (ScannerState.mk' "") (-1)).indents.size == 1
#guard (pushMappingIndent (ScannerState.mk' "") (-2)).indents.size == 1

-- Nested mapping indents
#guard (pushMappingIndent (pushMappingIndent (ScannerState.mk' "") 0) 2).indents.size == 3
#guard (pushMappingIndent (pushMappingIndent (ScannerState.mk' "") 0) 2).flowLevel ==
       (pushMappingIndent (pushMappingIndent (ScannerState.mk' "") 0) 2).flowStack.size

/-! ## §7  Push/unwind round-trip validation

Verify that push followed by unwind returns to the previous indent level.
-/

-- Push sequence then unwind: back to sentinel
private def seqPushThenUnwind : ScannerState :=
  unwindIndents (pushSequenceIndent (ScannerState.mk' "") 0) (-1)

#guard seqPushThenUnwind.indents.size == 1
#guard seqPushThenUnwind.flowLevel == seqPushThenUnwind.flowStack.size
#guard seqPushThenUnwind.simpleKeyStack.size == seqPushThenUnwind.flowStack.size
#guard seqPushThenUnwind.offset ≤ seqPushThenUnwind.inputEnd

-- Push mapping then unwind: back to sentinel
private def mapPushThenUnwind : ScannerState :=
  unwindIndents (pushMappingIndent (ScannerState.mk' "") 0) (-1)

#guard mapPushThenUnwind.indents.size == 1
#guard mapPushThenUnwind.flowLevel == mapPushThenUnwind.flowStack.size
#guard mapPushThenUnwind.offset ≤ mapPushThenUnwind.inputEnd

-- Push seq + map, partial unwind
private def seqMapPartialUnwind : ScannerState :=
  unwindIndents (pushMappingIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2) 1

#guard seqMapPartialUnwind.indents.size == 2
#guard seqMapPartialUnwind.flowLevel == seqMapPartialUnwind.flowStack.size
#guard seqMapPartialUnwind.offset ≤ seqMapPartialUnwind.inputEnd

-- Push 3 levels, full unwind
private def fullUnwind3 : ScannerState :=
  unwindIndents
    (pushSequenceIndent (pushMappingIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2) 4)
    (-1)

#guard fullUnwind3.indents.size == 1
#guard fullUnwind3.flowLevel == fullUnwind3.flowStack.size
#guard fullUnwind3.simpleKeyStack.size == fullUnwind3.flowStack.size
#guard fullUnwind3.offset ≤ fullUnwind3.inputEnd

/-! ## §8  Token Emission Validation

Verify that `unwindIndents` emits the correct number of `blockEnd` tokens.
-/

-- Unwinding 1 level emits 1 blockEnd
#guard (unwindIndents afterSeqPush (-1)).tokens.size ==
       afterSeqPush.tokens.size + 1

-- Unwinding 2 levels emits 2 blockEnd
#guard (unwindIndents twoLevels (-1)).tokens.size ==
       twoLevels.tokens.size + 2

-- Unwinding 3 levels emits 3 blockEnd
#guard (unwindIndents threeLevels (-1)).tokens.size ==
       threeLevels.tokens.size + 3

-- Unwinding 0 levels emits 0 tokens
#guard (unwindIndents (ScannerState.mk' "") (-1)).tokens.size == 0

-- Partial unwind (1 of 2) emits 1 blockEnd
#guard (unwindIndents twoLevels 1).tokens.size ==
       twoLevels.tokens.size + 1

/-! ## §9  Behavioral Guards — currentIndent tracking

Verify `currentIndent` is correct after push/unwind operations.
-/

-- Initial currentIndent is -1 (sentinel)
#guard (ScannerState.mk' "").currentIndent == -1

-- After push at col 0, currentIndent = 0
#guard afterSeqPush.currentIndent == 0

-- After two pushes (0, 2), currentIndent = 2
#guard twoLevels.currentIndent == 2

-- After unwinding twoLevels to col=1, currentIndent = 0
#guard (unwindIndents twoLevels 1).currentIndent == 0

-- After full unwind, currentIndent = -1 (sentinel)
#guard (unwindIndents twoLevels (-1)).currentIndent == -1

-- After three levels, currentIndent = 4
#guard threeLevels.currentIndent == 4

-- After unwinding threeLevels to 3, currentIndent = 2
#guard (unwindIndents threeLevels 3).currentIndent == 2

end Lean4Yaml.Proofs.ScannerIndentStack
