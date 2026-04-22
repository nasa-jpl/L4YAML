import L4YAML.Proofs.Scanner.ScannerIndentStack

namespace L4YAML.Proofs.ScannerIndentStack

open L4YAML.Scanner
open L4YAML.Proofs.ScannerLoopInvariant
open L4YAML.Proofs.ScannerContracts

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

end L4YAML.Proofs.ScannerIndentStack
