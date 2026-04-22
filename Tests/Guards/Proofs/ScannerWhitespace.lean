import L4YAML.Proofs.Scanner.ScannerWhitespace

namespace L4YAML.Proofs.ScannerWhitespace

open L4YAML.Scanner
open L4YAML.Proofs.ScannerLoopInvariant

-- LF at start
#guard (consumeNewline (ScannerState.mk' "\nabc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\nabc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "\nabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\nabc")).simpleKeyStack.size ==
       (consumeNewline (ScannerState.mk' "\nabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\nabc")).offset ≤
       (consumeNewline (ScannerState.mk' "\nabc")).inputEnd

-- CR at start
#guard (consumeNewline (ScannerState.mk' "\rabc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\rabc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "\rabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\rabc")).offset ≤
       (consumeNewline (ScannerState.mk' "\rabc")).inputEnd

-- CRLF at start
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "\r\nabc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).offset ≤
       (consumeNewline (ScannerState.mk' "\r\nabc")).inputEnd

-- Non-newline: identity
#guard (consumeNewline (ScannerState.mk' "abc")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "abc")).flowLevel ==
       (consumeNewline (ScannerState.mk' "abc")).flowStack.size
#guard (consumeNewline (ScannerState.mk' "abc")).offset ≤
       (consumeNewline (ScannerState.mk' "abc")).inputEnd

-- Empty: identity
#guard (consumeNewline (ScannerState.mk' "")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "")).offset ≤
       (consumeNewline (ScannerState.mk' "")).inputEnd

-- LF only (no content after)
#guard (consumeNewline (ScannerState.mk' "\n")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\n")).offset ≤
       (consumeNewline (ScannerState.mk' "\n")).inputEnd

-- CR only (no content after)
#guard (consumeNewline (ScannerState.mk' "\r")).indents.size ≥ 1
#guard (consumeNewline (ScannerState.mk' "\r")).offset ≤
       (consumeNewline (ScannerState.mk' "\r")).inputEnd
-- C1: indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "  ")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "  abc")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "\t\t")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' " \t abc")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "abc")).indents.size ≥ 1
#guard (skipWhitespace (ScannerState.mk' "\t日本")).indents.size ≥ 1

-- C2: flowLevel == flowStack.size
#guard (skipWhitespace (ScannerState.mk' "")).flowLevel ==
       (skipWhitespace (ScannerState.mk' "")).flowStack.size
#guard (skipWhitespace (ScannerState.mk' "  abc")).flowLevel ==
       (skipWhitespace (ScannerState.mk' "  abc")).flowStack.size
#guard (skipWhitespace (ScannerState.mk' "\t\tabc")).flowLevel ==
       (skipWhitespace (ScannerState.mk' "\t\tabc")).flowStack.size

-- C3: simpleKeyStack.size == flowStack.size
#guard (skipWhitespace (ScannerState.mk' "")).simpleKeyStack.size ==
       (skipWhitespace (ScannerState.mk' "")).flowStack.size
#guard (skipWhitespace (ScannerState.mk' "  abc")).simpleKeyStack.size ==
       (skipWhitespace (ScannerState.mk' "  abc")).flowStack.size

-- C4: offset ≤ inputEnd
#guard (skipWhitespace (ScannerState.mk' "")).offset ≤
       (skipWhitespace (ScannerState.mk' "")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "  abc")).offset ≤
       (skipWhitespace (ScannerState.mk' "  abc")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "  ")).offset ≤
       (skipWhitespace (ScannerState.mk' "  ")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "\t\t\tabc")).offset ≤
       (skipWhitespace (ScannerState.mk' "\t\t\tabc")).inputEnd
#guard (skipWhitespace (ScannerState.mk' "\t日本")).offset ≤
       (skipWhitespace (ScannerState.mk' "\t日本")).inputEnd

-- Stops at newline (newline is not s-white)
#guard (skipWhitespace (ScannerState.mk' "  \nabc")).offset ==
       (ScannerState.mk' "  \nabc").advance.advance.offset
-- C1: indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "   ")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "  abc")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' "abc")).indents.size ≥ 1
#guard (skipSpaces (ScannerState.mk' " \tab")).indents.size ≥ 1

-- C2: flowLevel == flowStack.size
#guard (skipSpaces (ScannerState.mk' "")).flowLevel ==
       (skipSpaces (ScannerState.mk' "")).flowStack.size
#guard (skipSpaces (ScannerState.mk' "  abc")).flowLevel ==
       (skipSpaces (ScannerState.mk' "  abc")).flowStack.size

-- C3: simpleKeyStack.size == flowStack.size
#guard (skipSpaces (ScannerState.mk' "")).simpleKeyStack.size ==
       (skipSpaces (ScannerState.mk' "")).flowStack.size
#guard (skipSpaces (ScannerState.mk' "  abc")).simpleKeyStack.size ==
       (skipSpaces (ScannerState.mk' "  abc")).flowStack.size

-- C4: offset ≤ inputEnd
#guard (skipSpaces (ScannerState.mk' "")).offset ≤
       (skipSpaces (ScannerState.mk' "")).inputEnd
#guard (skipSpaces (ScannerState.mk' "  abc")).offset ≤
       (skipSpaces (ScannerState.mk' "  abc")).inputEnd
#guard (skipSpaces (ScannerState.mk' "   ")).offset ≤
       (skipSpaces (ScannerState.mk' "   ")).inputEnd
#guard (skipSpaces (ScannerState.mk' " \tab")).offset ≤
       (skipSpaces (ScannerState.mk' " \tab")).inputEnd

-- Stops at tab
#guard (skipSpaces (ScannerState.mk' " \tabc")).offset ==
       (ScannerState.mk' " \tabc").advance.offset
-- C1: indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).indents.size ≥ 1
#guard (skipToEndOfLine (ScannerState.mk' "日本\n語")).indents.size ≥ 1

-- C2: flowLevel == flowStack.size
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).flowLevel ==
       (skipToEndOfLine (ScannerState.mk' "abc\ndef")).flowStack.size
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).flowLevel ==
       (skipToEndOfLine (ScannerState.mk' "abcdef")).flowStack.size

-- C3: simpleKeyStack.size == flowStack.size
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).simpleKeyStack.size ==
       (skipToEndOfLine (ScannerState.mk' "abc\ndef")).flowStack.size

-- C4: offset ≤ inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "abc\ndef")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "abcdef")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "\nabc")).inputEnd
#guard (skipToEndOfLine (ScannerState.mk' "日本\n語")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "日本\n語")).inputEnd

-- Immediate newline: no movement
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).offset == 0

-- CR
#guard (skipToEndOfLine (ScannerState.mk' "abc\rdef")).offset ≤
       (skipToEndOfLine (ScannerState.mk' "abc\rdef")).inputEnd
-- advanceN 0 is identity
#guard ((ScannerState.mk' "abc").advanceN 0).indents.size ≥ 1
#guard ((ScannerState.mk' "abc").advanceN 0).offset ≤
       ((ScannerState.mk' "abc").advanceN 0).inputEnd

-- advanceN within bounds
#guard ((ScannerState.mk' "abcdef").advanceN 3).indents.size ≥ 1
#guard ((ScannerState.mk' "abcdef").advanceN 3).flowLevel ==
       ((ScannerState.mk' "abcdef").advanceN 3).flowStack.size
#guard ((ScannerState.mk' "abcdef").advanceN 3).simpleKeyStack.size ==
       ((ScannerState.mk' "abcdef").advanceN 3).flowStack.size
#guard ((ScannerState.mk' "abcdef").advanceN 3).offset ≤
       ((ScannerState.mk' "abcdef").advanceN 3).inputEnd

-- advanceN past end: clamped
#guard ((ScannerState.mk' "ab").advanceN 10).indents.size ≥ 1
#guard ((ScannerState.mk' "ab").advanceN 10).offset ≤
       ((ScannerState.mk' "ab").advanceN 10).inputEnd

-- Multi-byte
#guard ((ScannerState.mk' "αβγ").advanceN 2).indents.size ≥ 1
#guard ((ScannerState.mk' "αβγ").advanceN 2).offset ≤
       ((ScannerState.mk' "αβγ").advanceN 2).inputEnd

-- Across newlines
#guard ((ScannerState.mk' "a\nb\nc").advanceN 4).indents.size ≥ 1
#guard ((ScannerState.mk' "a\nb\nc").advanceN 4).offset ≤
       ((ScannerState.mk' "a\nb\nc").advanceN 4).inputEnd
-- skipWhitespace advances past all s-white characters
#guard (skipWhitespace (ScannerState.mk' "  abc")).col == 2
#guard (skipWhitespace (ScannerState.mk' "\t abc")).col == 2
#guard (skipWhitespace (ScannerState.mk' "abc")).col == 0

-- skipSpaces advances past spaces only (stops at tab)
#guard (skipSpaces (ScannerState.mk' "  abc")).col == 2
#guard (skipSpaces (ScannerState.mk' " \tabc")).col == 1
#guard (skipSpaces (ScannerState.mk' "\tabc")).col == 0

-- skipToEndOfLine advances to line break
#guard (skipToEndOfLine (ScannerState.mk' "abc\ndef")).col == 3
#guard (skipToEndOfLine (ScannerState.mk' "\nabc")).col == 0
#guard (skipToEndOfLine (ScannerState.mk' "abcdef")).col == 6

-- consumeNewline line tracking (YAML §5.4 [28]: \n, \r\n, \r are all line terminators)
-- LF: line+1, col=0
#guard (consumeNewline (ScannerState.mk' "\nabc")).line == 1
#guard (consumeNewline (ScannerState.mk' "\nabc")).col == 0
-- CRLF: line+1 (not +2), col=0
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).line == 1
#guard (consumeNewline (ScannerState.mk' "\r\nabc")).col == 0
-- Lone CR: line+1, col=0 (per YAML §5.4 [28])
#guard (consumeNewline (ScannerState.mk' "\rabc")).line == 1
#guard (consumeNewline (ScannerState.mk' "\rabc")).col == 0
-- Non-newline: identity
#guard (consumeNewline (ScannerState.mk' "abc")).line == 0
#guard (consumeNewline (ScannerState.mk' "abc")).col == 0

-- Advance line/col tracking for each line break form
-- `advance` on \n → line+1, col=0
#guard (ScannerState.mk' "\nabc").advance.line == 1
#guard (ScannerState.mk' "\nabc").advance.col == 0
-- `advance` on \r → line+1, col=0
#guard (ScannerState.mk' "\rabc").advance.line == 1
#guard (ScannerState.mk' "\rabc").advance.col == 0
-- `advance` on regular char → line=0, col+1
#guard (ScannerState.mk' "abc").advance.line == 0
#guard (ScannerState.mk' "abc").advance.col == 1

-- After all three break forms, 'b' is at line=1 col=0 → advance to col=1
-- "a\nb": advance past 'a' → (0,1), advance past '\n' → (1,0), advance past 'b' → (1,1)
#guard (ScannerState.mk' "a\nb").advance.advance.line == 1
#guard (ScannerState.mk' "a\nb").advance.advance.col == 0
-- "a\r\nb": advance past 'a' → (0,1), advance past '\r' → (1,0), skip '\n' via consumeNewline
#guard (consumeNewline (ScannerState.mk' "a\r\nb").advance).line == 1
#guard (consumeNewline (ScannerState.mk' "a\r\nb").advance).col == 0
-- "a\rb": advance past 'a' → (0,1), advance past '\r' → (1,0)
#guard (ScannerState.mk' "a\rb").advance.advance.line == 1
#guard (ScannerState.mk' "a\rb").advance.advance.col == 0

-- advanceN position tracking
#guard ((ScannerState.mk' "abcdef").advanceN 3).col == 3
#guard ((ScannerState.mk' "abcdef").advanceN 3).offset == 3
#guard ((ScannerState.mk' "ab").advanceN 10).offset == 2

end L4YAML.Proofs.ScannerWhitespace
