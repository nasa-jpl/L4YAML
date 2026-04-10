import L4YAML.Proofs.ScannerSimpleKey

namespace L4YAML.Proofs.ScannerSimpleKey

open L4YAML.Scanner
open L4YAML.Proofs.ScannerLoopInvariant
open L4YAML.Proofs.ScannerContracts
open L4YAML.Proofs.ScannerIndentStack

-- saveSimpleKey preserves WellFormed on mk' states (block context, simpleKeyAllowed)
#guard (saveSimpleKey (ScannerState.mk' "key: value")).indents.size ≥ 1
#guard (saveSimpleKey (ScannerState.mk' "key: value")).flowLevel ==
       (saveSimpleKey (ScannerState.mk' "key: value")).flowStack.size
#guard (saveSimpleKey (ScannerState.mk' "key: value")).simpleKeyStack.size ==
       (saveSimpleKey (ScannerState.mk' "key: value")).flowStack.size
#guard (saveSimpleKey (ScannerState.mk' "key: value")).offset ≤
       (saveSimpleKey (ScannerState.mk' "key: value")).inputEnd

-- saveSimpleKey on initial state: simpleKeyAllowed is true, not in flow → saves
#guard (saveSimpleKey (ScannerState.mk' "test")).simpleKey.possible == true
#guard (saveSimpleKey (ScannerState.mk' "test")).simpleKey.tokenIndex == 0

-- saveSimpleKey with simpleKeyAllowed = false → identity
private def stateNoSave : ScannerState :=
  { ScannerState.mk' "test" with simpleKeyAllowed := false }
#guard (saveSimpleKey stateNoSave).simpleKey.possible == false

-- saveSimpleKey in flow context: sequence start puts us in flow
private def flowState : ScannerState :=
  scanFlowSequenceStart (ScannerState.mk' "[a")
#guard flowState.inFlow == true
#guard flowState.simpleKeyAllowed == true
#guard (saveSimpleKey flowState).simpleKey.possible == true

-- saveSimpleKey preserves WellFormed in flow context
#guard (saveSimpleKey flowState).indents.size ≥ 1
#guard (saveSimpleKey flowState).flowLevel ==
       (saveSimpleKey flowState).flowStack.size
#guard (saveSimpleKey flowState).simpleKeyStack.size ==
       (saveSimpleKey flowState).flowStack.size
#guard (saveSimpleKey flowState).offset ≤
       (saveSimpleKey flowState).inputEnd

-- saveSimpleKey with explicitKeyLine == some line in BLOCK context → saves
-- (compact mapping on ?-line is allowed; guard only applies in flow context)
private def explicitKeyState : ScannerState :=
  { ScannerState.mk' "? key" with explicitKeyLine := some 0 }
#guard (saveSimpleKey explicitKeyState).simpleKey.possible == true

-- saveSimpleKey with explicitKeyLine == some line in FLOW context → identity
private def explicitKeyFlowState : ScannerState :=
  { ScannerState.mk' "? key" with explicitKeyLine := some 0, flowStack := #[false], flowLevel := 1 }
#guard (saveSimpleKey explicitKeyFlowState).simpleKey.possible == false

-- saveSimpleKey preserves WellFormed with explicit key
#guard (saveSimpleKey explicitKeyState).indents.size ≥ 1
#guard (saveSimpleKey explicitKeyState).flowLevel ==
       (saveSimpleKey explicitKeyState).flowStack.size
-- scanKey in block context: pushes mapping indent + emits key
#guard (scanKey (ScannerState.mk' "? key")).isOk == true

-- scanKey result preserves WellFormed (concrete check)
private def scanKeyResult : ScannerState :=
  match scanKey (ScannerState.mk' "? key") with
  | .ok s => s
  | .error _ => ScannerState.mk' ""

#guard scanKeyResult.indents.size ≥ 1
#guard scanKeyResult.flowLevel == scanKeyResult.flowStack.size
#guard scanKeyResult.simpleKeyStack.size == scanKeyResult.flowStack.size
#guard scanKeyResult.offset ≤ scanKeyResult.inputEnd

-- scanKey sets simpleKeyAllowed to true
#guard scanKeyResult.simpleKeyAllowed == true
-- scanKey invalidates simple key
#guard scanKeyResult.simpleKey.possible == false
-- scanKey sets explicitKeyLine
#guard scanKeyResult.explicitKeyLine == some 0

-- scanKey in flow context: no pushMappingIndent
private def scanKeyFlowResult : ScannerState :=
  let fs := scanFlowMappingStart (ScannerState.mk' "{? key")
  match scanKey fs with
  | .ok s => s
  | .error _ => ScannerState.mk' ""

#guard scanKeyFlowResult.indents.size ≥ 1
#guard scanKeyFlowResult.flowLevel == scanKeyFlowResult.flowStack.size
#guard scanKeyFlowResult.simpleKeyStack.size == scanKeyFlowResult.flowStack.size
#guard scanKeyFlowResult.offset ≤ scanKeyFlowResult.inputEnd

-- scanKey with tab after ? triggers error
private def tabAfterKey : Except ScanError ScannerState :=
  scanKey (ScannerState.mk' "?\tvalue")
#guard tabAfterKey.isOk == false
-- scanValue with an explicit key pending (simple path)
private def explicitKeyForValue : ScannerState :=
  match scanKey (ScannerState.mk' "? key\n: value") with
  | .ok s =>
    -- Advance past "key\n" to the ":" on line 1.
    -- We need to manually position the scanner at ':'
    -- For guard purposes we just test what scanValue does with a well-set-up state
    s
  | .error _ => ScannerState.mk' ""

-- scanValue on initial state: starts implicit mapping
-- The initial state has simpleKeyAllowed but no simpleKey.possible set.
-- After saveSimpleKey + some content, simpleKey.possible would be true.
-- For testing, construct a state where simpleKey.possible is true.
private def stateWithSimpleKey : ScannerState :=
  let s := ScannerState.mk' "key: value"
  let s := saveSimpleKey s  -- saves simpleKey with possible=true
  -- Advance past "key" to position at ":"
  let s := s.advance.advance.advance
  s

-- Verify the setup
#guard stateWithSimpleKey.simpleKey.possible == true

-- scanValue should succeed with a pending simple key
private def scanValueResult : Option ScannerState :=
  match scanValue stateWithSimpleKey with
  | .ok s => some s
  | .error _ => none

#guard scanValueResult.isSome == true

-- WellFormed preserved through scanValue (concrete check)
private def scanValueState : ScannerState :=
  match scanValue stateWithSimpleKey with
  | .ok s => s
  | .error _ => ScannerState.mk' ""

#guard scanValueState.indents.size ≥ 1
#guard scanValueState.flowLevel == scanValueState.flowStack.size
#guard scanValueState.simpleKeyStack.size == scanValueState.flowStack.size
#guard scanValueState.offset ≤ scanValueState.inputEnd

-- scanValue sets simpleKeyAllowed
#guard scanValueState.simpleKeyAllowed == true
-- scanValue clears explicit key line
#guard scanValueState.explicitKeyLine == none
-- scanValue clears simple key
#guard scanValueState.simpleKey.possible == false

-- scanValue in flow context with pending simple key
private def flowWithSimpleKey : ScannerState :=
  let s := scanFlowMappingStart (ScannerState.mk' "{key: value}")
  -- In flow, after {, simpleKeyAllowed is true
  let s := saveSimpleKey s  -- saves simple key
  let s := s.advance.advance.advance  -- advance past "key"
  s

#guard flowWithSimpleKey.simpleKey.possible == true
#guard flowWithSimpleKey.inFlow == true

private def scanValueFlowResult : Option ScannerState :=
  match scanValue flowWithSimpleKey with
  | .ok s => some s
  | .error _ => none

-- WellFormed preserved for flow context scanValue
private def scanValueFlowState : ScannerState :=
  match scanValue flowWithSimpleKey with
  | .ok s => s
  | .error _ => ScannerState.mk' ""

-- Only check WellFormed if scanValue succeeded
#guard scanValueFlowResult.isSome == false ||
       scanValueFlowState.indents.size ≥ 1
#guard scanValueFlowResult.isSome == false ||
       scanValueFlowState.flowLevel == scanValueFlowState.flowStack.size
#guard scanValueFlowResult.isSome == false ||
       scanValueFlowState.simpleKeyStack.size == scanValueFlowState.flowStack.size
#guard scanValueFlowResult.isSome == false ||
       scanValueFlowState.offset ≤ scanValueFlowState.inputEnd

-- scanValue without simple key and without explicit key: pushMappingIndent path
private def noKeyState : ScannerState :=
  let s := ScannerState.mk' ": value"
  { s with simpleKeyAllowed := false, simpleKey := { possible := false } }

private def scanValueNoKeyResult : Option ScannerState :=
  match scanValue noKeyState with
  | .ok s => some s
  | .error _ => none

private def scanValueNoKeyState : ScannerState :=
  match scanValue noKeyState with
  | .ok s => s
  | .error _ => ScannerState.mk' ""

#guard scanValueNoKeyResult.isSome == true
#guard scanValueNoKeyState.indents.size ≥ 1
#guard scanValueNoKeyState.flowLevel == scanValueNoKeyState.flowStack.size
#guard scanValueNoKeyState.simpleKeyStack.size == scanValueNoKeyState.flowStack.size
#guard scanValueNoKeyState.offset ≤ scanValueNoKeyState.inputEnd

-- scanValue with tab after ':' at indent level triggers error
-- The tab check fires when (s.col : Int) ≤ s.currentIndent.
-- Default currentIndent is -1 (sentinel), so col=0 > -1 skips the check.
-- We need a state where col ≤ currentIndent, e.g., after pushing an indent.
-- The scanner must be AT ':' so that scanValue's advance moves past it to '\t'.
private def stateAtIndent : ScannerState :=
  let s := pushMappingIndent (ScannerState.mk' "k:\n:\tvalue") 0
  -- After pushMappingIndent col 0, currentIndent = 0
  -- Advance past "k:\n" (3 chars) to reach ":" at offset 3
  let s := s.advance.advance.advance
  { s with simpleKeyAllowed := false, simpleKey := { possible := false },
           col := 0 }  -- col=0 ≤ currentIndent=0

private def tabAfterValue : Except ScanError ScannerState :=
  scanValue stateAtIndent

-- Verify the setup: col ≤ currentIndent ensures tab check fires
#guard (stateAtIndent.col : Int) ≤ stateAtIndent.currentIndent
#guard stateAtIndent.peek? == some ':'
#guard tabAfterValue.isOk == false
-- Full scan pipeline: simple mapping
private def scanTokenTypes (input : String) : Option (List YamlToken) :=
  match scanFiltered input with
  | .ok tokens => some (tokens.toList.map (·.val))
  | .error _ => none

-- Basic block mapping: implicit key + value
#guard scanTokenTypes "key: value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Explicit key mapping
#guard scanTokenTypes "? key\n: value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Multiple implicit keys
#guard scanTokenTypes "a: 1\nb: 2" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "a" .plain, .value,
  .scalar "1" .plain, .key,
  .scalar "b" .plain, .value,
  .scalar "2" .plain, .blockEnd, .streamEnd]

-- Flow mapping with implicit keys
#guard scanTokenTypes "{a: 1, b: 2}" == some [
  .streamStart, .flowMappingStart, .key,
  .scalar "a" .plain, .value,
  .scalar "1" .plain, .flowEntry, .key,
  .scalar "b" .plain, .value,
  .scalar "2" .plain, .flowMappingEnd, .streamEnd]

-- Nested block mapping
#guard scanTokenTypes "outer:\n  inner: value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "outer" .plain, .value,
  .blockMappingStart, .key,
  .scalar "inner" .plain, .value,
  .scalar "value" .plain, .blockEnd, .blockEnd, .streamEnd]

-- Block sequence with mapping entries
#guard scanTokenTypes "- a: 1\n- b: 2" == some [
  .streamStart, .blockSequenceStart, .blockEntry,
  .blockMappingStart, .key, .scalar "a" .plain,
  .value, .scalar "1" .plain, .blockEnd, .blockEntry,
  .blockMappingStart, .key, .scalar "b" .plain,
  .value, .scalar "2" .plain, .blockEnd, .blockEnd, .streamEnd]

-- Value-only (empty key)
#guard scanTokenTypes ": value" == some [
  .streamStart, .blockMappingStart, .key, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Flow sequence with colon (value in flow)
#guard scanTokenTypes "[a: 1]" == some [
  .streamStart, .flowSequenceStart, .key,
  .scalar "a" .plain, .value,
  .scalar "1" .plain, .flowSequenceEnd, .streamEnd]

-- Double-quoted key
#guard scanTokenTypes "\"key\": value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .doubleQuoted, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Single-quoted key
#guard scanTokenTypes "'key': value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .singleQuoted, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Empty value
#guard scanTokenTypes "key:" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value, .blockEnd, .streamEnd]

-- Explicit key with empty value
#guard scanTokenTypes "? key\n:" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value, .blockEnd, .streamEnd]

end L4YAML.Proofs.ScannerSimpleKey
