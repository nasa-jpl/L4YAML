import L4YAML.Proofs.Scanner.ScannerFlowCollection

namespace L4YAML.Proofs.ScannerFlowCollection

open L4YAML
open L4YAML.Scanner
open L4YAML.Emit
open L4YAML.Proofs.ScannerLoopInvariant

#guard (scanFlowSequenceStart (ScannerState.mk' "[")).tokens.back!.val == .flowSequenceStart
#guard (scanFlowMappingStart (ScannerState.mk' "{")).tokens.back!.val == .flowMappingStart
#guard (scanFlowSequenceEnd (ScannerState.mk' "]")).tokens.back!.val == .flowSequenceEnd
#guard (scanFlowMappingEnd (ScannerState.mk' "}")).tokens.back!.val == .flowMappingEnd

-- Leading comma rejected after flow open
private def stateAfterSeqOpen : ScannerState := scanFlowSequenceStart (ScannerState.mk' "[,")
#guard stateAfterSeqOpen.tokens.back!.val == .flowSequenceStart
#guard (scanFlowEntry stateAfterSeqOpen).isOk == false

private def stateAfterMapOpen : ScannerState := scanFlowMappingStart (ScannerState.mk' "{,")
#guard stateAfterMapOpen.tokens.back!.val == .flowMappingStart
#guard (scanFlowEntry stateAfterMapOpen).isOk == false

-- Comma succeeds after a scalar token
private def stateInSeq : ScannerState :=
  let s := scanFlowSequenceStart (ScannerState.mk' "[\"a\",")
  s.emit (.scalar "a" .doubleQuoted)
#guard (scanFlowEntry stateInSeq).isOk == true
private def scanTokenTypes (input : String) : Option (List YamlToken) :=
  match scanFiltered input with
  | .ok tokens => some (tokens.toList.map (·.val))
  | .error _ => none

-- Empty flow sequence
#guard scanTokenTypes "[]" == some [.streamStart, .flowSequenceStart, .flowSequenceEnd, .streamEnd]
-- Empty flow mapping
#guard scanTokenTypes "{}" == some [.streamStart, .flowMappingStart, .flowMappingEnd, .streamEnd]
-- Sequence with one DQ scalar
#guard scanTokenTypes "[\"a\"]" == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowSequenceEnd, .streamEnd]
-- Sequence with two DQ scalars
#guard scanTokenTypes "[\"a\", \"b\"]" == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowEntry, .scalar "b" .doubleQuoted, .flowSequenceEnd, .streamEnd]
-- Mapping with one pair
#guard scanTokenTypes "{\"k\": \"v\"}" == some [.streamStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .scalar "v" .doubleQuoted, .flowMappingEnd, .streamEnd]
-- Nested: sequence in mapping
#guard scanTokenTypes "{\"k\": [\"a\"]}" == some [.streamStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowSequenceEnd, .flowMappingEnd, .streamEnd]
-- Nested: mapping in sequence
#guard scanTokenTypes "[{\"k\": \"v\"}]" == some [.streamStart, .flowSequenceStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .scalar "v" .doubleQuoted, .flowMappingEnd, .flowSequenceEnd, .streamEnd]
private def mkScalar (s : String) : YamlValue := .scalar { content := s, style := .doubleQuoted }
private def emptySeq : YamlValue := .sequence .flow #[]
private def emptyMap : YamlValue := .mapping .flow #[]

#guard emit emptySeq == "[]"
#guard scanTokenTypes (emit emptySeq) == some [.streamStart, .flowSequenceStart, .flowSequenceEnd, .streamEnd]
#guard emit emptyMap == "{}"
#guard scanTokenTypes (emit emptyMap) == some [.streamStart, .flowMappingStart, .flowMappingEnd, .streamEnd]

-- Single-element sequence
private def singleSeq : YamlValue := .sequence .flow #[mkScalar "hello"]
#guard emit singleSeq == "[\"hello\"]"
#guard scanTokenTypes (emit singleSeq) == some [.streamStart, .flowSequenceStart, .scalar "hello" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Two-element sequence
private def twoSeq : YamlValue := .sequence .flow #[mkScalar "a", mkScalar "b"]
#guard emit twoSeq == "[\"a\", \"b\"]"
#guard scanTokenTypes (emit twoSeq) == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowEntry, .scalar "b" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Three-element sequence
private def threeSeq : YamlValue := .sequence .flow #[mkScalar "a", mkScalar "b", mkScalar "c"]
#guard emit threeSeq == "[\"a\", \"b\", \"c\"]"
#guard scanTokenTypes (emit threeSeq) == some [.streamStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowEntry, .scalar "b" .doubleQuoted, .flowEntry, .scalar "c" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Single-pair mapping
private def singleMap : YamlValue := .mapping .flow #[(mkScalar "k", mkScalar "v")]
#guard emit singleMap == "{\"k\": \"v\"}"
#guard scanTokenTypes (emit singleMap) == some [.streamStart, .flowMappingStart, .key, .scalar "k" .doubleQuoted, .value, .scalar "v" .doubleQuoted, .flowMappingEnd, .streamEnd]

-- Two-pair mapping
private def twoMap : YamlValue := .mapping .flow #[(mkScalar "a", mkScalar "1"), (mkScalar "b", mkScalar "2")]
#guard emit twoMap == "{\"a\": \"1\", \"b\": \"2\"}"
#guard scanTokenTypes (emit twoMap) == some [.streamStart, .flowMappingStart, .key, .scalar "a" .doubleQuoted, .value, .scalar "1" .doubleQuoted, .flowEntry, .key, .scalar "b" .doubleQuoted, .value, .scalar "2" .doubleQuoted, .flowMappingEnd, .streamEnd]

-- Nested: seq with seqs
private def nestedSeq : YamlValue := .sequence .flow #[.sequence .flow #[mkScalar "a"], .sequence .flow #[mkScalar "b"]]
#guard emit nestedSeq == "[[\"a\"], [\"b\"]]"
#guard scanTokenTypes (emit nestedSeq) == some [.streamStart, .flowSequenceStart, .flowSequenceStart, .scalar "a" .doubleQuoted, .flowSequenceEnd, .flowEntry, .flowSequenceStart, .scalar "b" .doubleQuoted, .flowSequenceEnd, .flowSequenceEnd, .streamEnd]

-- Map containing sequence value
private def mapWithSeq : YamlValue := .mapping .flow #[(mkScalar "items", .sequence .flow #[mkScalar "x", mkScalar "y"])]
#guard scanTokenTypes (emit mapWithSeq) == some [.streamStart, .flowMappingStart, .key, .scalar "items" .doubleQuoted, .value, .flowSequenceStart, .scalar "x" .doubleQuoted, .flowEntry, .scalar "y" .doubleQuoted, .flowSequenceEnd, .flowMappingEnd, .streamEnd]

-- Deeply nested
private def deepNest : YamlValue := .sequence .flow #[.mapping .flow #[(mkScalar "a", .sequence .flow #[mkScalar "b", mkScalar "c"])]]
#guard scanTokenTypes (emit deepNest) == some [.streamStart, .flowSequenceStart, .flowMappingStart, .key, .scalar "a" .doubleQuoted, .value, .flowSequenceStart, .scalar "b" .doubleQuoted, .flowEntry, .scalar "c" .doubleQuoted, .flowSequenceEnd, .flowMappingEnd, .flowSequenceEnd, .streamEnd]

-- Escaped content in flow collections
private def seqWithEscapes : YamlValue := .sequence .flow #[mkScalar "line1\nline2", mkScalar "tab\there"]
#guard scanTokenTypes (emit seqWithEscapes) == some [.streamStart, .flowSequenceStart, .scalar "line1\nline2" .doubleQuoted, .flowEntry, .scalar "tab\there" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- UTF-8 content in flow collections
private def seqWithUtf8 : YamlValue := .sequence .flow #[mkScalar "αβ", mkScalar "日本"]
#guard scanTokenTypes (emit seqWithUtf8) == some [.streamStart, .flowSequenceStart, .scalar "αβ" .doubleQuoted, .flowEntry, .scalar "日本" .doubleQuoted, .flowSequenceEnd, .streamEnd]

-- Mapping with escape chars in keys and values
private def mapWithEscapes : YamlValue := .mapping .flow #[(mkScalar "key\n1", mkScalar "val\t1")]
#guard scanTokenTypes (emit mapWithEscapes) == some [.streamStart, .flowMappingStart, .key, .scalar "key\n1" .doubleQuoted, .value, .scalar "val\t1" .doubleQuoted, .flowMappingEnd, .streamEnd]

end L4YAML.Proofs.ScannerFlowCollection
