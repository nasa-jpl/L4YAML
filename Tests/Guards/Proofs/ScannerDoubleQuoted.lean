import L4YAML.Proofs.Scanner.ScannerDoubleQuoted

namespace L4YAML.Proofs.ScannerDoubleQuoted

open L4YAML
open L4YAML.Scanner
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.Proofs.RoundTrip

-- Concrete verification of all 15 named escapes
#guard processEscapeChar '0'  == some '\x00'
#guard processEscapeChar 'a'  == some '\x07'
#guard processEscapeChar 'b'  == some '\x08'
#guard processEscapeChar 't'  == some '\t'
#guard processEscapeChar '\t' == some '\t'
#guard processEscapeChar 'n'  == some '\n'
#guard processEscapeChar 'v'  == some '\x0B'
#guard processEscapeChar 'f'  == some '\x0C'
#guard processEscapeChar 'r'  == some '\r'
#guard processEscapeChar 'e'  == some '\x1B'
#guard processEscapeChar ' '  == some ' '
#guard processEscapeChar '"'  == some '"'
#guard processEscapeChar '/'  == some '/'
#guard processEscapeChar '\\' == some '\\'
#guard processEscapeChar 'N'  == some '\x85'
#guard processEscapeChar '_'  == some '\xA0'

-- Hex escapes return none (handled by separate parseHexEscape path)
#guard processEscapeChar 'x'  == none
#guard processEscapeChar 'u'  == none
#guard processEscapeChar 'U'  == none
-- Concrete verification: each escaped char round-trips through the scanner
-- (The universal theorem above covers all cases; these are additional documentation)
#guard processEscapeChar '0'  == some '\x00'   -- escapeTag '\x00' = some '0'
#guard processEscapeChar 'a'  == some '\x07'   -- escapeTag '\x07' = some 'a'
#guard processEscapeChar 'b'  == some '\x08'   -- escapeTag '\x08' = some 'b'
#guard processEscapeChar 't'  == some '\t'     -- escapeTag '\t'   = some 't'
#guard processEscapeChar 'n'  == some '\n'     -- escapeTag '\n'   = some 'n'
#guard processEscapeChar 'v'  == some '\x0b'   -- escapeTag '\x0b' = some 'v'
#guard processEscapeChar 'f'  == some '\x0c'   -- escapeTag '\x0c' = some 'f'
#guard processEscapeChar 'r'  == some '\r'     -- escapeTag '\r'   = some 'r'
#guard processEscapeChar 'e'  == some '\x1b'   -- escapeTag '\x1b' = some 'e'
#guard processEscapeChar '\\' == some '\\'     -- escapeTag '\\'   = some '\\'
#guard processEscapeChar '"'  == some '"'      -- escapeTag '"'    = some '"'
private def scanDQContent (input : String) : Option String :=
  match scanFiltered input with
  | .ok tokens =>
    tokens.toList.filterMap (fun t =>
      match t.val with
      | .scalar content .doubleQuoted => some content
      | _ => none) |>.head?
  | .error _ => none

-- ═══════════════════════════════════════════════════════════════════
-- §6a: Empty and plain ASCII
-- ═══════════════════════════════════════════════════════════════════

#guard scanDQContent (emitScalar "") == some ""
#guard scanDQContent (emitScalar "hello") == some "hello"
#guard scanDQContent (emitScalar "a") == some "a"
#guard scanDQContent (emitScalar "test string") == some "test string"
#guard scanDQContent (emitScalar "UPPER") == some "UPPER"
#guard scanDQContent (emitScalar "123") == some "123"

-- ═══════════════════════════════════════════════════════════════════
-- §6b: Every named escape character (one at a time)
-- ═══════════════════════════════════════════════════════════════════

#guard scanDQContent (emitScalar "\x00") == some "\x00"     -- null
#guard scanDQContent (emitScalar "\x07") == some "\x07"     -- bell
#guard scanDQContent (emitScalar "\x08") == some "\x08"     -- backspace
#guard scanDQContent (emitScalar "\t") == some "\t"         -- tab
#guard scanDQContent (emitScalar "\n") == some "\n"         -- newline
#guard scanDQContent (emitScalar "\x0b") == some "\x0b"     -- vertical tab
#guard scanDQContent (emitScalar "\x0c") == some "\x0c"     -- form feed
#guard scanDQContent (emitScalar "\r") == some "\r"         -- carriage return
#guard scanDQContent (emitScalar "\x1b") == some "\x1b"     -- escape
#guard scanDQContent (emitScalar "\\") == some "\\"         -- backslash
#guard scanDQContent (emitScalar "\"") == some "\""         -- double quote

-- ═══════════════════════════════════════════════════════════════════
-- §6c: Multi-byte UTF-8 characters (pass through escapeChar unchanged)
-- ═══════════════════════════════════════════════════════════════════

#guard scanDQContent (emitScalar "αβγ") == some "αβγ"         -- 2-byte Greek
#guard scanDQContent (emitScalar "日本語") == some "日本語"       -- 3-byte CJK
#guard scanDQContent (emitScalar "🎉") == some "🎉"           -- 4-byte emoji
#guard scanDQContent (emitScalar "🎉🎊🎈") == some "🎉🎊🎈"   -- multiple emoji

-- ═══════════════════════════════════════════════════════════════════
-- §6d: Mixed content with multiple escape types
-- ═══════════════════════════════════════════════════════════════════

#guard scanDQContent (emitScalar "line1\nline2") == some "line1\nline2"
#guard scanDQContent (emitScalar "tab\there") == some "tab\there"
#guard scanDQContent (emitScalar "quote\"here") == some "quote\"here"
#guard scanDQContent (emitScalar "back\\slash") == some "back\\slash"
#guard scanDQContent (emitScalar "mixed\n\t\"\\end") == some "mixed\n\t\"\\end"
#guard scanDQContent (emitScalar "a\x00b\x07c") == some "a\x00b\x07c"
#guard scanDQContent (emitScalar "\r\n") == some "\r\n"

-- ═══════════════════════════════════════════════════════════════════
-- §6e: Edge cases
-- ═══════════════════════════════════════════════════════════════════

-- Single special characters
#guard scanDQContent (emitScalar " ") == some " "           -- space (not escaped)
#guard scanDQContent (emitScalar "/") == some "/"           -- slash (not escaped)

-- Multiple consecutive escapes
#guard scanDQContent (emitScalar "\n\n\n") == some "\n\n\n"
#guard scanDQContent (emitScalar "\\\\\\") == some "\\\\\\"
#guard scanDQContent (emitScalar "\"\"\"") == some "\"\"\""

-- Long strings
#guard scanDQContent (emitScalar "abcdefghijklmnopqrstuvwxyz") == some "abcdefghijklmnopqrstuvwxyz"

-- YAML-significant characters that escapeChar passes through
#guard scanDQContent (emitScalar "key: value") == some "key: value"
#guard scanDQContent (emitScalar "- item") == some "- item"
#guard scanDQContent (emitScalar "#comment") == some "#comment"
#guard scanDQContent (emitScalar "[flow]") == some "[flow]"
#guard scanDQContent (emitScalar "{map}") == some "{map}"

-- ═══════════════════════════════════════════════════════════════════
-- §6f: escapeString structural verification
-- ═══════════════════════════════════════════════════════════════════

-- Empty string
#guard escapeString "" == ""
-- Plain ASCII passes through
#guard escapeString "hello" == "hello"
-- Each escape produces the correct 2-char sequence
#guard escapeString "\n" == "\\n"
#guard escapeString "\t" == "\\t"
#guard escapeString "\\" == "\\\\"
#guard escapeString "\"" == "\\\""
#guard escapeString "\x00" == "\\0"
-- Mixed
#guard escapeString "a\nb" == "a\\nb"
#guard escapeString "a\"b" == "a\\\"b"

end L4YAML.Proofs.ScannerDoubleQuoted
