import Lean4Yaml.Proofs.ScannerContracts

namespace Lean4Yaml.Proofs.ScannerContracts

open Lean4Yaml.Scanner

-- Flow end: flowLevel decrements correctly from 1
#guard (scanFlowSequenceEnd (scanFlowSequenceStart (ScannerState.mk' "[]"))).flowLevel == 0
#guard (scanFlowMappingEnd (scanFlowMappingStart (ScannerState.mk' "{}"))).flowLevel == 0

-- Flow end: flowStack.size matches flowLevel after close
#guard (scanFlowSequenceEnd (scanFlowSequenceStart (ScannerState.mk' "[]"))).flowStack.size == 0
#guard (scanFlowMappingEnd (scanFlowMappingStart (ScannerState.mk' "{}"))).flowStack.size == 0

-- Nested flow: 2 opens then 1 close → level 1
private def nestedFlow : ScannerState :=
  scanFlowMappingStart (scanFlowSequenceStart (ScannerState.mk' "[{"))

#guard nestedFlow.flowLevel == 2
#guard nestedFlow.flowStack.size == 2
#guard nestedFlow.simpleKeyStack.size == 2
#guard nestedFlow.flowLevel == nestedFlow.flowStack.size
#guard nestedFlow.simpleKeyStack.size == nestedFlow.flowStack.size

private def afterOneClose : ScannerState :=
  scanFlowMappingEnd nestedFlow

#guard afterOneClose.flowLevel == 1
#guard afterOneClose.flowStack.size == 1
#guard afterOneClose.simpleKeyStack.size == 1
#guard afterOneClose.flowLevel == afterOneClose.flowStack.size
#guard afterOneClose.simpleKeyStack.size == afterOneClose.flowStack.size

private def afterBothClose : ScannerState :=
  scanFlowSequenceEnd afterOneClose

#guard afterBothClose.flowLevel == 0
#guard afterBothClose.flowStack.size == 0
#guard afterBothClose.simpleKeyStack.size == 0
#guard afterBothClose.flowLevel == afterBothClose.flowStack.size
#guard afterBothClose.simpleKeyStack.size == afterBothClose.flowStack.size
#guard afterBothClose.inFlow == false
-- unwindIndents with col = -1 (stream level) preserves sentinel
#guard (unwindIndents (ScannerState.mk' "") (-1)).indents.size == 1

-- unwindIndents with col = -2 (below sentinel) still preserves sentinel
#guard (unwindIndents (ScannerState.mk' "") (-2)).indents.size == 1

-- pushSequenceIndent grows stack
private def afterSeqPush : ScannerState :=
  pushSequenceIndent (ScannerState.mk' "- a") 0

#guard afterSeqPush.indents.size == 2
#guard afterSeqPush.currentIndent == 0

-- pushMappingIndent grows stack
private def afterMapPush : ScannerState :=
  pushMappingIndent (ScannerState.mk' "a: b") 0

#guard afterMapPush.indents.size == 2
#guard afterMapPush.currentIndent == 0

-- Pushing at same/lower indent doesn't grow
#guard (pushSequenceIndent (ScannerState.mk' "") (-1)).indents.size == 1
#guard (pushMappingIndent (ScannerState.mk' "") (-2)).indents.size == 1

-- Push then unwind back to sentinel
#guard (unwindIndents afterSeqPush (-1)).indents.size == 1

-- Push two levels, unwind back to sentinel
private def twoLevels : ScannerState :=
  pushMappingIndent (pushSequenceIndent (ScannerState.mk' "") 0) 2

#guard twoLevels.indents.size == 3
#guard (unwindIndents twoLevels (-1)).indents.size == 1

-- Unwind to intermediate level
#guard (unwindIndents twoLevels 1).indents.size == 2
-- Each digit maps to the expected value
#guard digitOffset '1' == 1
#guard digitOffset '2' == 2
#guard digitOffset '3' == 3
#guard digitOffset '4' == 4
#guard digitOffset '5' == 5
#guard digitOffset '6' == 6
#guard digitOffset '7' == 7
#guard digitOffset '8' == 8
#guard digitOffset '9' == 9

-- Range verification: all valid offset values are in [1, 9]
#guard (List.range 9).map (fun i => digitOffset (Char.ofNat (49 + i))) == [1, 2, 3, 4, 5, 6, 7, 8, 9]

-- '0' is excluded: c-indentation-indicator is `ns-dec-digit \ "0"`
#guard digitOffset '0' == 0

-- Each valid digit satisfies the range [1, 9]
#guard (digitOffset '1' ≥ 1 && digitOffset '1' ≤ 9) == true
#guard (digitOffset '5' ≥ 1 && digitOffset '5' ≤ 9) == true
#guard (digitOffset '9' ≥ 1 && digitOffset '9' ≤ 9) == true

-- All 9 valid digits satisfy the range
#guard (List.range 9).all (fun i =>
  let m := digitOffset (Char.ofNat (49 + i))
  m ≥ 1 && m ≤ 9)
private def scanBlockScalarContent (input : String) : Option String :=
  match scanFiltered input with
  | .ok tokens =>
    let scalars := tokens.toList.filterMap fun pt =>
      match pt.val with
      | .scalar s _ => some s
      | _ => none
    scalars.head?
  | .error _ => none

-- §8.1.3 explicit offset: parent at column 0, auto-detect → contentIndent = 2
#guard scanBlockScalarContent "|\n  hello\n" == some "hello\n"
-- §8.1.3 explicit offset with digit: `|4` at top level → contentIndent = max(0, -1 + 4) = 3
#guard scanBlockScalarContent "|4\n    deep\n" == some " deep\n"
-- §8.1.3 auto-detect: first non-empty line at column 2
#guard scanBlockScalarContent "|\n  auto\n" == some "auto\n"
-- §8.1.3 auto-detect with leading blank lines
#guard scanBlockScalarContent "|\n\n  first\n" == some "\nfirst\n"
-- Folded scalar: newlines between same-indent lines are folded to spaces
#guard scanBlockScalarContent ">\n  hello\n  world\n" == some "hello world"
-- Literal scalar: newlines preserved
#guard scanBlockScalarContent "|\n  hello\n  world\n" == some "hello\nworld\n"
-- Strip chomp: no trailing newline
#guard scanBlockScalarContent "|-\n  stripped\n" == some "stripped"
-- Keep chomp: all trailing newlines preserved
#guard scanBlockScalarContent "|+\n  kept\n\n\n" == some "kept\n\n\n"
-- Clip chomp (default): single trailing newline
#guard scanBlockScalarContent "|\n  clipped\n\n\n" == some "clipped\n"

-- §8.1.3 auto-detect in nested context (mapping value)
private def scanNestedBlockScalar (input : String) : Option String :=
  match scanFiltered input with
  | .ok tokens =>
    let scalars := tokens.toList.filterMap fun pt =>
      match pt.val with
      | .scalar s .literal => some s
      | .scalar s .folded => some s
      | _ => none
    scalars.head?
  | .error _ => none

#guard scanNestedBlockScalar "key: |\n  nested\n" == some "nested\n"
#guard scanNestedBlockScalar "key: |2\n  two\n" == some "two\n"
-- Base state: flowLevel = 0, not in flow
#guard (ScannerState.mk' "").flowLevel == 0
#guard (ScannerState.mk' "").inFlow == false

-- After `[`: in flow
#guard (scanFlowSequenceStart (ScannerState.mk' "[")).flowLevel == 1
#guard (scanFlowSequenceStart (ScannerState.mk' "[")).inFlow == true

-- After `{`: in flow
#guard (scanFlowMappingStart (ScannerState.mk' "{")).flowLevel == 1
#guard (scanFlowMappingStart (ScannerState.mk' "{")).inFlow == true

-- WellFormed invariant: flowLevel = flowStack.size across operations
#guard (ScannerState.mk' "").flowLevel == (ScannerState.mk' "").flowStack.size
#guard (scanFlowSequenceStart (ScannerState.mk' "[")).flowLevel ==
       (scanFlowSequenceStart (ScannerState.mk' "[")).flowStack.size
#guard afterOneClose.flowLevel == afterOneClose.flowStack.size
#guard afterBothClose.flowLevel == afterBothClose.flowStack.size

-- WellFormed invariant: simpleKeyStack.size = flowStack.size across operations
#guard (ScannerState.mk' "").simpleKeyStack.size == (ScannerState.mk' "").flowStack.size
#guard (scanFlowSequenceStart (ScannerState.mk' "[")).simpleKeyStack.size ==
       (scanFlowSequenceStart (ScannerState.mk' "[")).flowStack.size
#guard afterOneClose.simpleKeyStack.size == afterOneClose.flowStack.size
#guard afterBothClose.simpleKeyStack.size == afterBothClose.flowStack.size

end Lean4Yaml.Proofs.ScannerContracts
