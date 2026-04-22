import L4YAML.Proofs.Scanner.ScannerProgress

namespace L4YAML.Proofs.ScannerProgress

open L4YAML.Scanner
open L4YAML.Proofs.ScannerLoopInvariant
open L4YAML.Proofs.ScannerContracts
open L4YAML.Proofs.ScannerScalar

-- scanFlowEntry: (s.emit .flowEntry).advance
private def checkFlowEntryProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanFlowEntry s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkFlowEntryProgress ", rest"
#guard checkFlowEntryProgress ","
#guard checkFlowEntryProgress ",\n"

-- scanBlockEntry: (pushSequenceIndent? then emit .blockEntry).advance
private def checkBlockEntryProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanBlockEntry s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkBlockEntryProgress "- rest"
#guard checkBlockEntryProgress "- "
#guard checkBlockEntryProgress "-\n"

-- scanKey: (pushMappingIndent? then emit .key).advance
private def checkKeyProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanKey s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkKeyProgress "? rest"
#guard checkKeyProgress "? "
#guard checkKeyProgress "?\n"
private def checkValueProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanValue s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkValueProgress ": "
#guard checkValueProgress ": value"
#guard checkValueProgress ":\n"

-- scanValue in flow context (simple key resolution path)
private def checkValueFlowProgress (input : String) : Bool :=
  let s0 := ScannerState.mk' ("{" ++ input)
  let s := scanFlowMappingStart s0
  -- Simulate having scanned a key
  let s := { s with simpleKey := {
    possible := true,
    tokenIndex := s.tokens.size,
    endLine := s.line,
    pos := s.currentPos
  }}
  match scanValue s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkValueFlowProgress ": val}"
#guard checkValueFlowProgress ":}"
private def checkSkipToContentMonotone (input : String) : Bool :=
  let s := ScannerState.mk' input
  match skipToContent s with
  | .ok s' => s'.offset ≥ s.offset
  | .error _ => true

-- No-op: first char is content
#guard checkSkipToContentMonotone "content"
#guard checkSkipToContentMonotone "abc"
-- Advances: spaces before content
#guard checkSkipToContentMonotone "   content"
-- Advances: newlines
#guard checkSkipToContentMonotone "\ncontent"
#guard checkSkipToContentMonotone "\n\ncontent"
-- Advances: comment lines
#guard checkSkipToContentMonotone "# comment\ncontent"
-- Advances: mixed
#guard checkSkipToContentMonotone "  # comment\n  content"
-- Advances: just whitespace (to EOF)
#guard checkSkipToContentMonotone "   "
#guard checkSkipToContentMonotone ""
private def checkDocStartProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  (scanDocumentStart s).offset > s.offset

#guard checkDocStartProgress "---\n"
#guard checkDocStartProgress "--- content"
#guard checkDocStartProgress "---"

private def checkDocEndProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanDocumentEnd s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkDocEndProgress "...\n"
#guard checkDocEndProgress "..."
#guard checkDocEndProgress "... "
private def checkDirectiveProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanDirective s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkDirectiveProgress "%YAML 1.2\n"
#guard checkDirectiveProgress "%TAG !! tag:\n"
#guard checkDirectiveProgress "%UNKNOWN\n"
-- scanDoubleQuoted: consumes at least `""`
private def checkDQProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanDoubleQuoted s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkDQProgress "\"hello\""
#guard checkDQProgress "\"\""
#guard checkDQProgress "\"multi\nline\""

-- scanSingleQuoted: consumes at least `''`
private def checkSQProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanSingleQuoted s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkSQProgress "'hello'"
#guard checkSQProgress "''"
#guard checkSQProgress "'multi\nline'"

-- scanPlainScalar: consumes at least first char
private def checkPlainProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanPlainScalar s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkPlainProgress "hello"
#guard checkPlainProgress "value rest"
#guard checkPlainProgress "123"

-- scanBlockScalar: consumes at least `|` or `>`
private def checkBlockScalarProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanBlockScalar s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkBlockScalarProgress "|\n  content\n"
#guard checkBlockScalarProgress ">\n  content\n"
#guard checkBlockScalarProgress "|\n"
-- scanAnchorOrAlias
private def checkAnchorProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanAnchorOrAlias s true with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

private def checkAliasProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanAnchorOrAlias s false with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkAnchorProgress "&anchor rest"
#guard checkAnchorProgress "&a "
#guard checkAliasProgress "*alias rest"
#guard checkAliasProgress "*a "

-- scanTag
private def checkTagProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanTag s with
  | .ok s' => s'.offset > s.offset
  | .error _ => true

#guard checkTagProgress "!!str rest"
#guard checkTagProgress "!<uri> rest"
#guard checkTagProgress "!local rest"
#guard checkTagProgress "! rest"
-- Helper: check that scanNextToken advances offset
private def nextTokenProgress (input : String) : Bool :=
  let s := ScannerState.mk' input
  match scanNextToken s with
  | .ok (some s') => s'.offset > s.offset
  | .ok none => true  -- EOF: no progress needed
  | .error _ => true  -- error: no progress needed

-- === Document markers ===
#guard nextTokenProgress "---\n"
#guard nextTokenProgress "--- rest"
#guard nextTokenProgress "...\n"
#guard nextTokenProgress "... rest"
#guard nextTokenProgress "..."

-- === Directives ===
#guard nextTokenProgress "%YAML 1.2\n"
#guard nextTokenProgress "%TAG !! tag:\n"

-- === Flow collection indicators ===
#guard nextTokenProgress "[rest"
#guard nextTokenProgress "{rest"

-- === Block entry ===
#guard nextTokenProgress "- value"
#guard nextTokenProgress "- "
#guard nextTokenProgress "-\n"

-- === Key indicator ===
#guard nextTokenProgress "? "
#guard nextTokenProgress "? value"
#guard nextTokenProgress "?\n"

-- === Value indicator ===
#guard nextTokenProgress ": "
#guard nextTokenProgress ": value"
#guard nextTokenProgress ":\n"

-- === Anchor/Alias ===
#guard nextTokenProgress "&anchor rest"
#guard nextTokenProgress "*alias rest"

-- === Tag ===
#guard nextTokenProgress "!!str rest"
#guard nextTokenProgress "!<uri> rest"
#guard nextTokenProgress "!local rest"

-- === Block scalar ===
#guard nextTokenProgress "|\n  content\n"
#guard nextTokenProgress ">\n  content\n"

-- === Quoted scalars ===
#guard nextTokenProgress "\"hello\" rest"
#guard nextTokenProgress "'hello' rest"
#guard nextTokenProgress "\"\""
#guard nextTokenProgress "''"

-- === Plain scalar ===
#guard nextTokenProgress "hello rest"
#guard nextTokenProgress "value"
#guard nextTokenProgress "123"
#guard nextTokenProgress "true"

-- === Whitespace before content ===
-- skipToContent advances, then dispatch advances further
#guard nextTokenProgress "  hello"
#guard nextTokenProgress "\nhello"
#guard nextTokenProgress "  \nhello"
#guard nextTokenProgress "# comment\nhello"

-- === Multi-token progress (each token advances) ===
private def multiTokenProgress (input : String) (n : Nat) : Bool :=
  Id.run do
    let mut s := ScannerState.mk' input
    for _ in [:n] do
      let prevOffset := s.offset
      match scanNextToken s with
      | .ok (some s') =>
        if s'.offset <= prevOffset then return false
        s := s'
      | .ok none => return true
      | .error _ => return true
    return true

#guard multiTokenProgress "a: b" 3
#guard multiTokenProgress "- a\n- b" 4
#guard multiTokenProgress "[a, b]" 5
#guard multiTokenProgress "{k: v}" 5
#guard multiTokenProgress "---\nvalue\n..." 3
private def scanCompletes (input : String) : Bool :=
  (scan input).isOk

-- Basic inputs
#guard scanCompletes ""
#guard scanCompletes "value"
#guard scanCompletes "key: value"
#guard scanCompletes "- a\n- b\n- c"

-- Multi-document
#guard scanCompletes "---\nfirst\n...\n---\nsecond\n..."

-- Complex nested structures
#guard scanCompletes "a:\n  b:\n    c:\n      d: e"
#guard scanCompletes "- a:\n    b: c\n- d:\n    e: f"
#guard scanCompletes "[[[a, b], [c, d]], [[e, f]]]"
#guard scanCompletes "{a: {b: {c: d}}, e: {f: g}}"

-- All scalar types
#guard scanCompletes "plain: value\ndq: \"double\"\nsq: 'single'\nlit: |\n  literal\nfold: >\n  folded\n"

-- Directives
#guard scanCompletes "%YAML 1.2\n---\nvalue"
#guard scanCompletes "%TAG !! tag:\n---\nvalue"

-- Anchors/aliases/tags
#guard scanCompletes "- &a value\n- *a\n- !!str tagged"

-- Long inputs (stress fuel)
#guard scanCompletes (String.join (List.replicate 50 "- item\n"))
#guard scanCompletes (String.join (List.replicate 20 "key: value\n"))

-- UTF-8 multi-byte
#guard scanCompletes "αβγ: δεζ"
#guard scanCompletes "キー: 値\nキー2: 値2"
#guard scanCompletes "🎉: party\n🎊: celebration"

-- BOM
#guard scanCompletes "\uFEFFkey: value"

-- Whitespace-heavy
#guard scanCompletes "  \n  \n  # comment\n  \n  value"
-- Token positions are monotonically non-decreasing
private def tokenPositionsMonotone (input : String) : Bool :=
  match scanFiltered input with
  | .ok tokens =>
    let offsets := tokens.toList.map (fun t => t.pos.offset)
    (offsets.zip offsets.tail).all (fun (a, b) => a ≤ b)
  | .error _ => true

#guard tokenPositionsMonotone ""
#guard tokenPositionsMonotone "value"
#guard tokenPositionsMonotone "key: value"
#guard tokenPositionsMonotone "- a\n- b\n- c"
#guard tokenPositionsMonotone "[a, b, c]"
#guard tokenPositionsMonotone "{a: 1, b: 2}"
#guard tokenPositionsMonotone "---\na: b\n..."
#guard tokenPositionsMonotone "a:\n  b:\n    c: d"

-- Full multi-document lifecycle
#guard tokenPositionsMonotone "%YAML 1.2\n---\n- &a value\n- *a\n...\n---\nkey: !!str tagged\n..."

end L4YAML.Proofs.ScannerProgress
