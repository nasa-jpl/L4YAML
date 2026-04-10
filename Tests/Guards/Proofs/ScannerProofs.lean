import L4YAML.Proofs.ScannerProofs

namespace L4YAML.Proofs.ScannerProofs

open L4YAML
open L4YAML.Scanner

-- YAML 1.2.2 §5.13 named escapes
#guard scannerEscapeChar '0'  == some '\x00'      -- \0  → U+0000 (null)
#guard scannerEscapeChar 'a'  == some '\x07'      -- \a  → U+0007 (bell)
#guard scannerEscapeChar 'b'  == some '\x08'      -- \b  → U+0008 (backspace)
#guard scannerEscapeChar 't'  == some '\t'        -- \t  → U+0009 (tab)
#guard scannerEscapeChar '\t' == some '\t'        -- \<TAB> → U+0009 (tab)
#guard scannerEscapeChar 'n'  == some '\n'        -- \n  → U+000A (line feed)
#guard scannerEscapeChar 'v'  == some '\x0B'      -- \v  → U+000B (vertical tab)
#guard scannerEscapeChar 'f'  == some '\x0C'      -- \f  → U+000C (form feed)
#guard scannerEscapeChar 'r'  == some '\r'        -- \r  → U+000D (carriage return)
#guard scannerEscapeChar 'e'  == some '\x1B'      -- \e  → U+001B (escape)
#guard scannerEscapeChar ' '  == some ' '         -- \   → U+0020 (space)
#guard scannerEscapeChar '"'  == some '"'         -- \"  → U+0022 (double quote)
#guard scannerEscapeChar '/'  == some '/'         -- \/  → U+002F (slash)
#guard scannerEscapeChar '\\' == some '\\'        -- \\  → U+005C (backslash)
#guard scannerEscapeChar 'N'  == some '\x85'      -- \N  → U+0085 (next line)
#guard scannerEscapeChar '_'  == some '\xA0'      -- \_  → U+00A0 (NBSP)
#guard scannerEscapeChar 'L'  == some (Char.ofNat 0x2028)  -- \L → U+2028 (line separator)
#guard scannerEscapeChar 'P'  == some (Char.ofNat 0x2029)  -- \P → U+2029 (paragraph separator)

-- Hex escape indicators return none (handled separately)
#guard scannerEscapeChar 'x'  == none
#guard scannerEscapeChar 'u'  == none
-- Note: 'U' goes to hex path, not none — it calls parseHexEscape with 8 digits
-- On a 1-char input, parseHexEscape fails (not enough digits), returning error.
-- So scannerEscapeChar 'U' is also none.
#guard scannerEscapeChar 'U'  == none
-- Advance on concrete inputs
#guard (ScannerState.mk' "a").advance.col == 1
#guard (ScannerState.mk' "a").advance.line == 0
#guard (ScannerState.mk' "ab").advance.advance.col == 2
#guard (ScannerState.mk' "\n").advance.col == 0
#guard (ScannerState.mk' "\n").advance.line == 1
#guard (ScannerState.mk' "a\nb").advance.advance.col == 0
#guard (ScannerState.mk' "a\nb").advance.advance.line == 1
#guard (ScannerState.mk' "a\nb").advance.advance.advance.col == 1
-- Concrete indentation stack checks
#guard (pushSequenceIndent (ScannerState.mk' "- a") 0).indents.size == 2
#guard (pushMappingIndent (ScannerState.mk' "a: b") 0).indents.size == 2
-- Pushing at same or lower indent doesn't grow
#guard (pushSequenceIndent (ScannerState.mk' "") (-1)).indents.size == 1
#guard (pushMappingIndent (ScannerState.mk' "") (-2)).indents.size == 1
private def scanOk (input : String) : Bool :=
  match scanFiltered input with
  | .ok _ => true
  | .error _ => false
private def scanFirst (input : String) : Option YamlToken :=
  match scanFiltered input with
  | .ok tokens => if tokens.size > 0 then some tokens[0]!.val else none
  | .error _ => none
private def scanLast (input : String) : Option YamlToken :=
  match scanFiltered input with
  | .ok tokens => if tokens.size > 0 then some tokens[tokens.size - 1]!.val else none
  | .error _ => none
private def scanSize (input : String) : Option Nat :=
  match scanFiltered input with
  | .ok tokens => some tokens.size
  | .error _ => none

-- All scans succeed
#guard scanOk ""
#guard scanOk "hello"
#guard scanOk "key: value"
#guard scanOk "- item1\n- item2"
#guard scanOk "---\nhello\n..."
#guard scanOk "{ a: 1, b: 2 }"

-- First token is always streamStart
#guard scanFirst "" == some .streamStart
#guard scanFirst "hello" == some .streamStart
#guard scanFirst "key: value" == some .streamStart
#guard scanFirst "- item1\n- item2" == some .streamStart
#guard scanFirst "---\nhello\n..." == some .streamStart
#guard scanFirst "{ a: 1, b: 2 }" == some .streamStart

-- Last token is always streamEnd
#guard scanLast "" == some .streamEnd
#guard scanLast "hello" == some .streamEnd
#guard scanLast "key: value" == some .streamEnd
#guard scanLast "- item1\n- item2" == some .streamEnd
#guard scanLast "---\nhello\n..." == some .streamEnd
#guard scanLast "{ a: 1, b: 2 }" == some .streamEnd

-- Empty input produces exactly 2 tokens (streamStart + streamEnd)
#guard scanSize "" == some 2

-- Token count sanity checks
#guard match scanSize "hello" with | some n => n > 2 | none => false
#guard match scanSize "key: value" with | some n => n > 2 | none => false
#guard match scanSize "- a\n- b" with | some n => n > 4 | none => false

end L4YAML.Proofs.ScannerProofs
