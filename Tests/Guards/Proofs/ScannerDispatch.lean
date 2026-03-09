import Lean4Yaml.Proofs.ScannerDispatch

namespace Lean4Yaml.Proofs.ScannerDispatch

open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.ScannerLoopInvariant
open Lean4Yaml.Proofs.ScannerContracts
open Lean4Yaml.Proofs.ScannerIndentStack
open Lean4Yaml.Proofs.ScannerScalar
open Lean4Yaml.Proofs.ScannerDocument

-- Full WellFormed preservation for flow-open (concrete)
private def checkFlowOpenWF (f : ScannerState → ScannerState) (input : String) : Bool :=
  let s := f (ScannerState.mk' input)
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd

#guard checkFlowOpenWF scanFlowSequenceStart "[a]"
#guard checkFlowOpenWF scanFlowSequenceStart "[]"
#guard checkFlowOpenWF scanFlowSequenceStart "[hello]"
#guard checkFlowOpenWF scanFlowMappingStart "{a: b}"
#guard checkFlowOpenWF scanFlowMappingStart "{}"
#guard checkFlowOpenWF scanFlowMappingStart "{key: value}"
-- scanFlowSequenceEnd WellFormed preservation (concrete)
private def checkFlowSeqEndWF (input : String) : Bool :=
  let s := scanFlowSequenceStart (ScannerState.mk' input)
  let s' := scanFlowSequenceEnd s
  s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
  && s'.simpleKeyStack.size == s'.flowStack.size
  && s'.offset ≤ s'.inputEnd

#guard checkFlowSeqEndWF "[a]"
#guard checkFlowSeqEndWF "[]"
#guard checkFlowSeqEndWF "[hello, world]"

-- scanFlowMappingEnd WellFormed preservation (concrete)
private def checkFlowMapEndWF (input : String) : Bool :=
  let s := scanFlowMappingStart (ScannerState.mk' input)
  let s' := scanFlowMappingEnd s
  s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
  && s'.simpleKeyStack.size == s'.flowStack.size
  && s'.offset ≤ s'.inputEnd

#guard checkFlowMapEndWF "{a}"
#guard checkFlowMapEndWF "{}"
#guard checkFlowMapEndWF "{key: value}"

-- Nested flow: open seq, open map, close map, close seq
private def nestedFlowWF : Bool :=
  let s := scanFlowSequenceStart (ScannerState.mk' "[{test}]")
  let s := scanFlowMappingStart s
  let s := scanFlowMappingEnd s
  let s := scanFlowSequenceEnd s
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd
#guard nestedFlowWF

-- Double nested
private def doubleNestedFlowWF : Bool :=
  let s := scanFlowSequenceStart (ScannerState.mk' "[[a]]")
  let s := scanFlowSequenceStart s
  let s := scanFlowSequenceEnd s
  let s := scanFlowSequenceEnd s
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd
#guard doubleNestedFlowWF
-- scanFlowEntry C1 preservation (concrete)
private def checkFlowEntryC1 (tokens : Array (Positioned YamlToken))
    (input : String) : Bool :=
  let s : ScannerState := { ScannerState.mk' input with tokens := tokens }
  match scanFlowEntry s with
  | .ok s' => s'.indents.size ≥ 1
  | .error _ => true

-- With prior scalar token (normal case)
#guard checkFlowEntryC1 #[⟨default, .scalar "a" .plain⟩] ", b]"
-- With prior key token
#guard checkFlowEntryC1 #[⟨default, .key⟩] ", v}"

-- scanFlowEntry C2 preservation (concrete)
private def checkFlowEntryC2 (tokens : Array (Positioned YamlToken))
    (input : String) : Bool :=
  let s0 := ScannerState.mk' input
  let s : ScannerState := { scanFlowSequenceStart s0 with tokens :=
    (scanFlowSequenceStart s0).tokens ++ tokens }
  match scanFlowEntry s with
  | .ok s' => s'.flowLevel == s'.flowStack.size
  | .error _ => true

#guard checkFlowEntryC2 #[⟨default, .scalar "a" .plain⟩] "[a, b]"

-- scanFlowEntry C3 preservation (concrete)
private def checkFlowEntryC3 (tokens : Array (Positioned YamlToken))
    (input : String) : Bool :=
  let s0 := ScannerState.mk' input
  let s : ScannerState := { scanFlowSequenceStart s0 with tokens :=
    (scanFlowSequenceStart s0).tokens ++ tokens }
  match scanFlowEntry s with
  | .ok s' => s'.simpleKeyStack.size == s'.flowStack.size
  | .error _ => true

#guard checkFlowEntryC3 #[⟨default, .scalar "a" .plain⟩] "[a, b]"

-- scanFlowEntry WellFormed (concrete)
private def checkFlowEntryWF (input : String) : Bool :=
  let s := scanFlowSequenceStart (ScannerState.mk' input)
  -- Emit a scalar so comma is not immediately after flow-open
  let s := { s.emitAt default (.scalar "a" .plain) with simpleKeyAllowed := false }
  match scanFlowEntry s with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true

#guard checkFlowEntryWF "[a, b]"
#guard checkFlowEntryWF "[x, y, z]"
-- scanBlockEntry WellFormed (concrete)
private def checkBlockEntryWF (input : String) : Bool :=
  match scanBlockEntry (ScannerState.mk' input) with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true

#guard checkBlockEntryWF "- "
#guard checkBlockEntryWF "- value"
#guard checkBlockEntryWF "- \n"
#guard checkBlockEntryWF "-\n"

-- Multiple block entries
private def multiBlockEntryWF : Bool :=
  let s0 := ScannerState.mk' "- a\n- b\n"
  match scanBlockEntry s0 with
  | .ok s1 => s1.indents.size ≥ 1 && s1.flowLevel == s1.flowStack.size
              && s1.simpleKeyStack.size == s1.flowStack.size
              && s1.offset ≤ s1.inputEnd
  | .error _ => true
#guard multiBlockEntryWF
-- scanKey WellFormed
private def checkKeyWF (input : String) : Bool :=
  match scanKey (ScannerState.mk' input) with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true

#guard checkKeyWF "? "
#guard checkKeyWF "? value"
#guard checkKeyWF "?\n"

-- scanKey in flow context
private def checkKeyFlowWF (input : String) : Bool :=
  let s := scanFlowMappingStart (ScannerState.mk' ("{" ++ input))
  match scanKey s with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true

#guard checkKeyFlowWF "? key}"
#guard checkKeyFlowWF "? key: value}"

-- scanValue WellFormed
private def checkValueWF (input : String) : Bool :=
  match scanValue (ScannerState.mk' input) with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true

#guard checkValueWF ": "
#guard checkValueWF ": value"
#guard checkValueWF ":\n"
private def checkSkipToContentWF (input : String) : Bool :=
  match skipToContent (ScannerState.mk' input) with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true

-- Empty input
#guard checkSkipToContentWF ""
-- Just spaces
#guard checkSkipToContentWF "   content"
-- Spaces and tabs
#guard checkSkipToContentWF " \t content"
-- Comment line
#guard checkSkipToContentWF "# comment\ncontent"
-- Multiple comment lines
#guard checkSkipToContentWF "# line1\n# line2\ncontent"
-- Blank lines
#guard checkSkipToContentWF "\n\n\ncontent"
-- Spaces + blank lines + comment
#guard checkSkipToContentWF "  \n  # comment\n  content"
-- No whitespace at all
#guard checkSkipToContentWF "content"
-- Just newlines
#guard checkSkipToContentWF "\n\n"
-- Tab in non-indentation position (allowed)
#guard checkSkipToContentWF "\t"
-- CRLF line endings
#guard checkSkipToContentWF "\r\ncontent"
-- Mixed whitespace and content
#guard checkSkipToContentWF "   # comment\n   \n   value"
-- Helper: check WellFormed after scanNextToken
private def checkNextTokenWF (input : String) : Bool :=
  match scanNextToken (ScannerState.mk' input) with
  | .ok (some s') => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
                     && s'.simpleKeyStack.size == s'.flowStack.size
                     && s'.offset ≤ s'.inputEnd
  | .ok none => true  -- input exhausted
  | .error _ => true  -- error paths

-- === Document markers ===
#guard checkNextTokenWF "---\n"
#guard checkNextTokenWF "--- rest"
#guard checkNextTokenWF "...\n"
#guard checkNextTokenWF "... rest"
#guard checkNextTokenWF "..."

-- === Directives ===
#guard checkNextTokenWF "%YAML 1.2\n"
#guard checkNextTokenWF "%TAG !! tag:yaml.org,2002:\n"

-- === Flow collection start/end ===
#guard checkNextTokenWF "[rest"
#guard checkNextTokenWF "{rest"

-- === Flow entry ===
-- (comma requires being inside flow — tested via full scan below)

-- === Block entry ===
#guard checkNextTokenWF "- value"
#guard checkNextTokenWF "- "
#guard checkNextTokenWF "-\n"

-- === Key indicator ===
#guard checkNextTokenWF "? "
#guard checkNextTokenWF "? value"

-- === Value indicator ===
#guard checkNextTokenWF ": "
#guard checkNextTokenWF ": value"

-- === Anchor/Alias ===
#guard checkNextTokenWF "&anchor rest"
#guard checkNextTokenWF "*alias rest"

-- === Tag ===
#guard checkNextTokenWF "!!str rest"
#guard checkNextTokenWF "!<uri> rest"
#guard checkNextTokenWF "!local rest"

-- === Block scalar ===
#guard checkNextTokenWF "|\n  content\n"
#guard checkNextTokenWF ">\n  content\n"

-- === Quoted scalars ===
#guard checkNextTokenWF "\"hello\" rest"
#guard checkNextTokenWF "'hello' rest"

-- === Plain scalar ===
#guard checkNextTokenWF "hello rest"
#guard checkNextTokenWF "value"

-- === Empty/EOF ===
#guard checkNextTokenWF ""

-- === Whitespace before content ===
#guard checkNextTokenWF "  hello"
#guard checkNextTokenWF "\nhello"
#guard checkNextTokenWF "  \nhello"
#guard checkNextTokenWF "# comment\nhello"
-- Helper: check scan succeeds
private def scanOk (input : String) : Bool := (scan input).isOk

-- Helper: extract token types from scan
private def scanTokens (input : String) : Option (List YamlToken) :=
  match scanFiltered input with
  | .ok tokens => some (tokens.toList.map Positioned.val)
  | .error _ => none

-- === Basic pipeline ===
#guard scanOk ""
#guard scanOk "value"
#guard scanOk "key: value"
#guard scanOk "- item1\n- item2"
#guard scanOk "---\nvalue"
#guard scanOk "...\n---\nvalue"

-- === StreamStart/StreamEnd envelope ===
#guard scanTokens "" == some [.streamStart, .streamEnd]
#guard scanTokens "value" == some [.streamStart, .scalar "value" .plain, .streamEnd]

-- === Document markers in pipeline ===
#guard scanTokens "---\nvalue" == some [
  .streamStart, .documentStart,
  .scalar "value" .plain, .streamEnd]

#guard scanTokens "value\n..." == some [
  .streamStart, .scalar "value" .plain,
  .documentEnd, .streamEnd]

#guard scanTokens "---\nvalue\n..." == some [
  .streamStart, .documentStart,
  .scalar "value" .plain,
  .documentEnd, .streamEnd]

-- === Multi-document ===
#guard scanTokens "---\nfirst\n---\nsecond" == some [
  .streamStart, .documentStart,
  .scalar "first" .plain, .documentStart,
  .scalar "second" .plain, .streamEnd]

#guard scanTokens "---\nfirst\n...\n---\nsecond" == some [
  .streamStart, .documentStart,
  .scalar "first" .plain, .documentEnd,
  .documentStart,
  .scalar "second" .plain, .streamEnd]

-- === Directives + document ===
#guard scanTokens "%YAML 1.2\n---\nvalue" == some [
  .streamStart, .versionDirective 1 2, .documentStart,
  .scalar "value" .plain, .streamEnd]

-- === Flow collections ===
#guard scanTokens "[]" == some [
  .streamStart, .flowSequenceStart, .flowSequenceEnd, .streamEnd]

#guard scanTokens "{}" == some [
  .streamStart, .flowMappingStart, .flowMappingEnd, .streamEnd]

#guard scanTokens "[a, b]" == some [
  .streamStart, .flowSequenceStart,
  .scalar "a" .plain, .flowEntry,
  .scalar "b" .plain, .flowSequenceEnd, .streamEnd]

#guard scanTokens "{k: v}" == some [
  .streamStart, .flowMappingStart, .key,
  .scalar "k" .plain, .value,
  .scalar "v" .plain, .flowMappingEnd, .streamEnd]

-- Nested flow
#guard scanTokens "[{a: b}]" == some [
  .streamStart, .flowSequenceStart,
  .flowMappingStart, .key,
  .scalar "a" .plain, .value,
  .scalar "b" .plain,
  .flowMappingEnd, .flowSequenceEnd, .streamEnd]

#guard scanTokens "{k: [a, b]}" == some [
  .streamStart, .flowMappingStart, .key,
  .scalar "k" .plain, .value,
  .flowSequenceStart,
  .scalar "a" .plain, .flowEntry,
  .scalar "b" .plain, .flowSequenceEnd,
  .flowMappingEnd, .streamEnd]

-- === Block structures ===
#guard scanTokens "- a\n- b" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .scalar "a" .plain,
  .blockEntry, .scalar "b" .plain,
  .blockEnd, .streamEnd]

#guard scanTokens "key: value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain,
  .blockEnd, .streamEnd]

-- === Anchor/Alias in pipeline ===
#guard scanTokens "- &a val\n- *a" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .anchor "a", .scalar "val" .plain,
  .blockEntry, .alias "a",
  .blockEnd, .streamEnd]

-- === Tags in pipeline ===
#guard scanTokens "!!str value" == some [
  .streamStart, .tag "!!" "str",
  .scalar "value" .plain, .streamEnd]

-- === Block scalars in pipeline ===
#guard scanTokens "|\n  content\n" == some [
  .streamStart, .scalar "content\n" .literal, .streamEnd]

#guard scanTokens ">\n  folded\n  content\n" == some [
  .streamStart, .scalar "folded content" .folded, .streamEnd]

-- === Quoted scalars in pipeline ===
#guard scanTokens "\"hello\"" == some [
  .streamStart, .scalar "hello" .doubleQuoted, .streamEnd]

#guard scanTokens "'hello'" == some [
  .streamStart, .scalar "hello" .singleQuoted, .streamEnd]

-- === Explicit key/value ===
#guard scanTokens "? key\n: value" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain,
  .blockEnd, .streamEnd]

-- === Complex nested structures ===
#guard scanTokens "a:\n  b:\n    c: d" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "a" .plain, .value,
  .blockMappingStart, .key,
  .scalar "b" .plain, .value,
  .blockMappingStart, .key,
  .scalar "c" .plain, .value,
  .scalar "d" .plain,
  .blockEnd, .blockEnd, .blockEnd, .streamEnd]

#guard scanTokens "- a:\n  - b\n  - c" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .blockMappingStart, .key,
  .scalar "a" .plain, .value,
  .blockEntry, .scalar "b" .plain,
  .blockEntry, .scalar "c" .plain,
  .blockEnd, .blockEnd, .streamEnd]

-- === UTF-8 content ===
#guard scanOk "key: αβγ"
#guard scanOk "キー: 値"
#guard scanOk "🎉: party"

-- === BOM handling ===
#guard scanOk "\uFEFFkey: value"
#guard scanTokens "\uFEFFvalue" == some [
  .streamStart, .scalar "value" .plain, .streamEnd]
-- Unterminated flow collection
#guard (scan "[").isOk == false
#guard (scan "{").isOk == false
#guard (scan "[a, b").isOk == false

-- Flow end outside flow
#guard (scan "]").isOk == false
#guard (scan "}").isOk == false

-- Comma outside flow
#guard (scan ",").isOk == false

-- Unterminated quoted scalar
#guard (scan "\"unterminated").isOk == false
#guard (scan "'unterminated").isOk == false

-- Invalid escape
#guard (scan "\"bad\\q\"").isOk == false

-- Unexpected character (@)
#guard (scan "@").isOk == false
-- Backtick
#guard (scan "`").isOk == false

-- Document markers in flow are treated as plain scalars (valid YAML)
#guard (scan "[---]").isOk == true
#guard (scan "[...]").isOk == true

-- Directive without document
#guard (scan "%YAML 1.2\n...").isOk == false

-- Duplicate YAML directive
#guard (scan "%YAML 1.2\n%YAML 1.1\n---").isOk == false
-- All flow indicators produce tokens
#guard scanOk "[a]"
#guard scanOk "{a: b}"
#guard scanOk "[a, b]"

-- Block indicators
#guard scanOk "- item"
#guard scanOk "? key\n: value"
#guard scanOk "key: value"

-- Anchor/alias/tag
#guard scanOk "&anchor value"
#guard scanOk "*alias"
#guard scanOk "!!str value"
#guard scanOk "!<uri> value"
#guard scanOk "!local value"

-- Scalar starts: letters, digits, special plain-start chars
#guard scanOk "abc"
#guard scanOk "123"
#guard scanOk "true"
#guard scanOk "null"
#guard scanOk "~"

-- Block scalars
#guard scanOk "|\n  literal\n"
#guard scanOk ">\n  folded\n"

-- Quoted scalars
#guard scanOk "\"double\""
#guard scanOk "'single'"

-- Document markers
#guard scanOk "---"
#guard scanOk "..."
#guard scanOk "---\n..."

-- Directives
#guard scanOk "%YAML 1.2\n---"
#guard scanOk "%TAG !! tag:\n---"

-- Whitespace-only inputs
#guard scanOk " "
#guard scanOk "  "
#guard scanOk "\n"
#guard scanOk "\t"
#guard scanOk " \n "

-- Comment-only inputs
#guard scanOk "# comment"
#guard scanOk "# line1\n# line2"
-- Each token advances offset
private def offsetAdvances (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanNextToken s with
  | .ok (some s') => s'.offset > s.offset
  | .ok none => true  -- EOF
  | .error _ => true  -- error

#guard offsetAdvances "value"
#guard offsetAdvances "- item"
#guard offsetAdvances "key: value"
#guard offsetAdvances "---\n"
#guard offsetAdvances "...\n"
#guard offsetAdvances "&anchor"
#guard offsetAdvances "*alias"
#guard offsetAdvances "!!str"
#guard offsetAdvances "\"hello\""
#guard offsetAdvances "'hello'"
#guard offsetAdvances "|\n  content\n"
#guard offsetAdvances ">\n  content\n"
#guard offsetAdvances "? key"
#guard offsetAdvances ": value"
#guard offsetAdvances "[rest"
#guard offsetAdvances "{rest"

-- Verify multiple iterations advance cumulatively
private def multiStepProgress : Bool :=
  let s0 := ScannerState.mk' "a: b"
  match scanNextToken s0 with
  | .ok (some s1) =>
    match scanNextToken s1 with
    | .ok (some s2) => s2.offset > s1.offset && s1.offset > s0.offset
    | _ => true
  | _ => true
#guard multiStepProgress

-- Full scan completes (doesn't exhaust fuel) for various inputs
#guard scanOk "a: b\nc: d\ne: f"
#guard scanOk "- a\n- b\n- c\n- d\n- e"
#guard scanOk "[a, b, c, d, e]"
#guard scanOk "{a: 1, b: 2, c: 3}"
#guard scanOk "---\na: 1\n...\n---\nb: 2\n..."
-- Mixed block and flow
#guard scanTokens "key:\n  - [a, b]\n  - {c: d}" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .blockSequenceStart,
  .blockEntry, .flowSequenceStart,
  .scalar "a" .plain, .flowEntry,
  .scalar "b" .plain, .flowSequenceEnd,
  .blockEntry, .flowMappingStart, .key,
  .scalar "c" .plain, .value,
  .scalar "d" .plain, .flowMappingEnd,
  .blockEnd, .blockEnd, .streamEnd]

-- All scalar types in one document
#guard scanTokens "plain: value\ndq: \"double\"\nsq: 'single'\nlit: |\n  literal\n" == some [
  .streamStart, .blockMappingStart,
  .key, .scalar "plain" .plain, .value, .scalar "value" .plain,
  .key, .scalar "dq" .plain, .value, .scalar "double" .doubleQuoted,
  .key, .scalar "sq" .plain, .value, .scalar "single" .singleQuoted,
  .key, .scalar "lit" .plain, .value, .scalar "literal\n" .literal,
  .blockEnd, .streamEnd]

-- Document lifecycle: directive → start → content → end → restart
#guard scanTokens "%YAML 1.2\n---\nfirst\n...\n---\nsecond\n..." == some [
  .streamStart, .versionDirective 1 2, .documentStart,
  .scalar "first" .plain, .documentEnd,
  .documentStart,
  .scalar "second" .plain, .documentEnd, .streamEnd]

-- Anchors and aliases with tags
#guard scanTokens "- &a !!str value\n- *a" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .anchor "a", .tag "!!" "str", .scalar "value" .plain,
  .blockEntry, .alias "a",
  .blockEnd, .streamEnd]

-- Deeply nested blocks
#guard scanTokens "a:\n  b:\n    - c\n    - d:\n        e: f" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "a" .plain, .value,
  .blockMappingStart, .key,
  .scalar "b" .plain, .value,
  .blockSequenceStart,
  .blockEntry, .scalar "c" .plain,
  .blockEntry, .blockMappingStart, .key,
  .scalar "d" .plain, .value,
  .blockMappingStart, .key,
  .scalar "e" .plain, .value,
  .scalar "f" .plain,
  .blockEnd, .blockEnd, .blockEnd, .blockEnd, .blockEnd, .streamEnd]

-- Empty document
#guard scanTokens "---\n..." == some [
  .streamStart, .documentStart, .documentEnd, .streamEnd]

-- Multiple empty documents
#guard scanTokens "---\n...\n---\n..." == some [
  .streamStart, .documentStart, .documentEnd,
  .documentStart, .documentEnd, .streamEnd]

-- Flow in flow
#guard scanTokens "[[1, 2], [3, 4]]" == some [
  .streamStart, .flowSequenceStart,
  .flowSequenceStart,
  .scalar "1" .plain, .flowEntry,
  .scalar "2" .plain, .flowSequenceEnd, .flowEntry,
  .flowSequenceStart,
  .scalar "3" .plain, .flowEntry,
  .scalar "4" .plain, .flowSequenceEnd,
  .flowSequenceEnd, .streamEnd]

-- Mapping of sequences
#guard scanTokens "a:\n  - 1\n  - 2\nb:\n  - 3" == some [
  .streamStart, .blockMappingStart,
  .key, .scalar "a" .plain, .value,
  .blockSequenceStart,
  .blockEntry, .scalar "1" .plain,
  .blockEntry, .scalar "2" .plain,
  .blockEnd,
  .key, .scalar "b" .plain, .value,
  .blockSequenceStart,
  .blockEntry, .scalar "3" .plain,
  .blockEnd, .blockEnd, .streamEnd]

-- Sequence of mappings
#guard scanTokens "- a: 1\n  b: 2\n- c: 3" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .blockMappingStart,
  .key, .scalar "a" .plain, .value, .scalar "1" .plain,
  .key, .scalar "b" .plain, .value, .scalar "2" .plain,
  .blockEnd,
  .blockEntry, .blockMappingStart,
  .key, .scalar "c" .plain, .value, .scalar "3" .plain,
  .blockEnd, .blockEnd, .streamEnd]

end Lean4Yaml.Proofs.ScannerDispatch
