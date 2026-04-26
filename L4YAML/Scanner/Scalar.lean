/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State
import L4YAML.Scanner.Whitespace
import L4YAML.Scanner.Document

/-!
# Scanner — Scalars and Escapes

All scalar-style scanners: escape sequences (§5.7), quoted scalars
(§7.3.1 double / §7.3.2 single), plain scalars (§7.3.3), and block
scalars (§8.1 literal / folded), plus the line-folding utilities that
support them.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2.

## Scope

- **Escapes** (§5.7): `collectHexDigitsLoop`, `parseHexEscape`, `processEscape`.
- **Line folding in quoted scalars** (§6.5): `trimTrailingWS`,
  `foldQuotedNewlinesLoop`, `foldQuotedNewlines`.
- **Quoted scalars** (§7.3.1, §7.3.2): `validateTrailingContent`,
  `collectDoubleQuotedLoop`, `scanDoubleQuoted`,
  `collectSingleQuotedLoop`, `scanSingleQuoted`.
- **Plain scalars** (§7.3.3): `skipBlankLinesLoop`, `PlainScalarResult`,
  `collectPlainScalar_terminates?`, `collectPlainScalar_handleBlockLineBreak`,
  `collectPlainScalarLoop`, `scanPlainScalar`.
- **Block scalars** (§8.1): `FoldState`, `foldBlockContent`,
  `autoDetectBlockScalarIndent*`, `consumeExactSpaces`,
  `collectLineContentLoop`, `collectBlockScalarLoop`,
  `parseBlockHeaderLoop`, `scanBlockScalarSkipComment`,
  `scanBlockScalarConsumeNewline`, `scanBlockScalarBody`, `scanBlockScalar`.
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Escape Sequence Processing -/

/-- Helper for parseHexEscape: collect up to `n` hex digits using structural recursion. -/
@[yaml_spec "5.6" 36 "ns-hex-digit"]
def collectHexDigitsLoop (s : ScannerState) (hex : String) (n : Nat) : String × ScannerState :=
  match n with
  | 0 => (hex, s)
  | n' + 1 =>
    match s.peek? with
    | some c =>
      if c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F') then
        collectHexDigitsLoop s.advance (hex.push c) n'
      else (hex, s)
    | none => (hex, s)

/-- Parse `n` hexadecimal digits and convert to a character.

    **Implements** (YAML 1.2.2 §5.7):
    - `[59] ns-esc-8-bit`  when `n = 2` (→ `\xHH`)
    - `[60] ns-esc-16-bit` when `n = 4` (→ `\uHHHH`)
    - `[61] ns-esc-32-bit` when `n = 8` (→ `\UHHHHHHHH`)

    **Pre**: Scanner positioned after `\x`, `\u`, or `\U`.
    **Post**: Advances past `n` hex digits, returns the decoded character.
    **Error**: `invalidHexEscape` (fewer than `n` hex digits available),
    `unicodeOutOfRange` (value ≥ U+110000). -/
@[yaml_spec "5.7" 59 "ns-esc-8-bit",
  yaml_spec "5.7" 60 "ns-esc-16-bit",
  yaml_spec "5.7" 61 "ns-esc-32-bit"]
def parseHexEscape (s : ScannerState) (n : Nat) : Except ScanError (Char × ScannerState) := do
  let (hex, s') := collectHexDigitsLoop s "" n
  if hex.length != n then
    .error (.invalidHexEscape n hex.length s'.line)
  else
    let val := hex.foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0
    if val < 0x110000 then
      .ok (Char.ofNat val, s')
    else
      .error (.unicodeOutOfRange s'.line)

/-- Process a single escape sequence after `\`.

    **Implements** (YAML 1.2.2 §5.7):
    - `[62] c-ns-esc-char` = `"\\" ( ns-esc-null | ... | ns-esc-32-bit )`
    - `[41] c-escape` = `"\\"`
    - `[42]`–`[61]` individual escape characters

    Supports all 20 named escapes (`\0`, `\a`, `\b`, `\t`, `\n`, `\v`, `\f`,
    `\r`, `\e`, `\ `, `\"`, `\/`, `\\`, `\N`, `\_`, `\L`, `\P`)
    plus the three hex escapes (`\x`, `\u`, `\U`).

    **Pre**: Scanner positioned at the character AFTER `\`.
    **Post**: Returns the decoded character and scanner advanced past the escape.
    **Error**: `unterminatedEscape` (EOF after `\`), `unknownEscape` (unrecognized escape character). -/
@[yaml_spec "5.7" 62 "c-ns-esc-char", yaml_spec "5.7" 41 "c-escape",
  yaml_spec "5.7" 42 "ns-esc-null", yaml_spec "5.7" 43 "ns-esc-bell",
  yaml_spec "5.7" 44 "ns-esc-backspace", yaml_spec "5.7" 45 "ns-esc-horizontal-tab",
  yaml_spec "5.7" 46 "ns-esc-line-feed", yaml_spec "5.7" 47 "ns-esc-vertical-tab",
  yaml_spec "5.7" 48 "ns-esc-form-feed", yaml_spec "5.7" 49 "ns-esc-carriage-return",
  yaml_spec "5.7" 50 "ns-esc-escape", yaml_spec "5.7" 51 "ns-esc-space",
  yaml_spec "5.7" 52 "ns-esc-double-quote", yaml_spec "5.7" 53 "ns-esc-slash",
  yaml_spec "5.7" 54 "ns-esc-backslash", yaml_spec "5.7" 55 "ns-esc-next-line",
  yaml_spec "5.7" 56 "ns-esc-non-breaking-space", yaml_spec "5.7" 57 "ns-esc-line-separator",
  yaml_spec "5.7" 58 "ns-esc-paragraph-separator", yaml_spec "5.7" 59 "ns-esc-8-bit",
  yaml_spec "5.7" 60 "ns-esc-16-bit", yaml_spec "5.7" 61 "ns-esc-32-bit"]
def processEscape (s : ScannerState) : Except ScanError (Char × ScannerState) := do
  match s.peek? with
  | none => .error (.unterminatedEscape s.line)
  | some c =>
    let s' := s.advance
    match c with
    | '0'  => .ok ('\x00', s')
    | 'a'  => .ok ('\x07', s')
    | 'b'  => .ok ('\x08', s')
    | 't'  => .ok ('\t', s')
    | '\t' => .ok ('\t', s')
    | 'n'  => .ok ('\n', s')
    | 'v'  => .ok ('\x0B', s')
    | 'f'  => .ok ('\x0C', s')
    | 'r'  => .ok ('\r', s')
    | 'e'  => .ok ('\x1B', s')
    | ' '  => .ok (' ', s')
    | '"'  => .ok ('"', s')
    | '/'  => .ok ('/', s')
    | '\\' => .ok ('\\', s')
    | 'N'  => .ok ('\x85', s')
    | '_'  => .ok ('\xA0', s')
    | 'L'  => .ok (Char.ofNat 0x2028, s')
    | 'P'  => .ok (Char.ofNat 0x2029, s')
    | 'x'  => parseHexEscape s' 2
    | 'u'  => parseHexEscape s' 4
    | 'U'  => parseHexEscape s' 8
    | _    => .error (.unknownEscape c s.line)

/-! ## Scalar Scanning -/

/-- Trim trailing space/tab characters (YAML §6.5 flow line folding). -/
@[yaml_spec "6.5"]
def trimTrailingWS (s : String) : String :=
  String.ofList ((s.toList.reverse.dropWhile (fun c => c == ' ' || c == '\t')).reverse)

/-- Helper for foldQuotedNewlines: count consecutive empty lines using structural recursion.

    Skips blank lines (spaces followed by line break), counting them.
    Returns on first non-blank line content or EOF.

    **Termination**: Structurally recursive on `fuel`. -/
@[yaml_spec "6.4" 70 "l-empty(n,c)"]
def foldQuotedNewlinesLoop (s : ScannerState) (emptyCount : Nat) (fuel : Nat) :
    ScannerState × Nat :=
  match fuel with
  | 0 => (s, emptyCount)
  | fuel' + 1 =>
    let saved := s
    let s_skipped := skipSpaces s
    match s_skipped.peek? with
    | some c =>
      if isLineBreakBool c then
        foldQuotedNewlinesLoop (consumeNewline s_skipped) (emptyCount + 1) fuel'
      else (saved, emptyCount)
    | none => (s, emptyCount)

/-- Fold a newline in a quoted scalar (double or single) per YAML flow folding.

    **Implements** (YAML 1.2.2 §6.5):
    - `[73]  b-l-folded(n,c)` = `b-l-trimmed(n,c) | b-as-space`
    - `[74]  s-flow-folded(n)` = `s-separate-in-line? b-l-folded(n,FLOW-IN) s-flow-line-prefix(n)`
    - `[69]  b-l-trimmed(n,c)` = `b-non-content l-empty(n,c)+`
    - `[70]  b-as-space` = `b-break`

    A single newline becomes a space; consecutive empty lines produce `\n` each
    (the first is the `b-non-content` silent break).

    **Pre**: Scanner at a line break character inside a quoted scalar.
    **Post**: Consumes newline + blank lines + leading spaces on continuation line.
    Returns the folded replacement string (`" "` or `"\n"*`).
    **Error**: `tabInIndentation` if tab found in indentation zone of continuation line (§6.1). -/
@[yaml_spec "6.5" 73 "b-l-folded",
  yaml_spec "6.5" 74 "s-flow-folded",
  yaml_spec "6.5" 71 "b-l-trimmed(n,c)",
  yaml_spec "6.5" 72 "b-as-space",
  yaml_spec "6.3" 69 "s-flow-line-prefix(n)"]
def foldQuotedNewlines (s : ScannerState) : Except ScanError (String × ScannerState) := do
  let s' := consumeNewline s
  let (s', emptyCount) := foldQuotedNewlinesLoop s' 0 (s.inputEnd - s'.offset + 1)
  -- Consume indentation spaces (s-indent [63]), then any remaining
  -- tabs/spaces as s-separate-in-line [66].  Quoted scalar continuations
  -- use s-flow-line-prefix(n) [69] = s-indent(n) s-separate-in-line?.
  -- §6.1: After consuming empty lines and leading spaces on the continuation
  -- line, check for tab-as-indentation.  If we haven't advanced past the
  -- current block indent level, a tab here is in the indentation zone.
  let s' := skipSpaces s'
  if !s'.inFlow && (s'.col : Int) ≤ s'.currentIndent then
    if let some '\t' := s'.peek? then
      throw (.tabInIndentation s'.line s'.col)
  let s' := skipWhitespace s'
  if emptyCount > 0 then
    return (String.ofList (List.replicate emptyCount '\n'), s')
  else
    return (" ", s')

-- Helper: Validate trailing content after closing quote (block context only)
@[yaml_spec "7.5"]
def validateTrailingContent (s : ScannerState) (inputEnd : Nat) : Except ScanError Unit := do
  let probe := skipTrailingSpaces s (inputEnd - s.offset + 1)
  match probe.peek? with
  | none => pure ()
  | some c =>
    if isLineBreakBool c || c == '#' || c == ':' then
      pure ()
    else
      throw (.trailingContent probe.line probe.col)

-- Helper: Collect double-quoted content using structural recursion
@[yaml_spec "7.3.1" 107 "nb-double-char",
  yaml_spec "7.3.1" 108 "ns-double-char",
  yaml_spec "7.3.1" 110 "nb-double-text",
  yaml_spec "7.3.1" 111 "nb-double-one-line",
  yaml_spec "7.3.1" 112 "s-double-escaped",
  yaml_spec "7.3.1" 113 "s-double-break",
  yaml_spec "7.3.1" 114 "nb-ns-double-in-line",
  yaml_spec "7.3.1" 115 "s-double-next-line(n)",
  yaml_spec "7.3.1" 116 "nb-double-multi-line(n)",
  yaml_spec "5.1" 2 "nb-json"]
def collectDoubleQuotedLoop (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    Except ScanError (String × ScannerState) :=
  match fuel with
  | 0 => .error (.unterminatedScalar .doubleQuoted startPos.line)
  | fuel' + 1 =>
    match s.peek? with
    | none => .error (.unterminatedScalar .doubleQuoted startPos.line)
    | some '"' =>
      -- Closing quote found
      .ok (content, s.advance)
    | some '\\' =>
      -- Escape sequence
      let s_after_backslash := s.advance
      match s_after_backslash.peek? with
      | some c =>
        if isLineBreakBool c then do
          -- Escaped line break: consume and skip whitespace
          let s_after_newline := consumeNewline s_after_backslash
          let s_after_ws := skipWhitespace s_after_newline
          collectDoubleQuotedLoop s_after_ws content fuel' startPos inFlow currentIndent inputEnd
        else do
          -- Regular escape sequence
          let (ch, s_after_escape) ← processEscape s_after_backslash
          let content' := content.push ch
          collectDoubleQuotedLoop s_after_escape content' fuel' startPos inFlow currentIndent inputEnd
      | none => .error (.unterminatedEscape s_after_backslash.line)
    | some c =>
      if isLineBreakBool c then do
        -- Line break: fold newlines
        let content_trimmed := trimTrailingWS content
        let (folded, s') ← foldQuotedNewlines s
        -- Validation: document markers at col 0 terminate
        if atDocumentStart s' || atDocumentEnd s' then
          throw (.documentMarkerInScalar .doubleQuoted startPos.line)
        -- Validation: continuation line must be indented past block level
        if (s'.col : Int) ≤ currentIndent then
          throw (.underIndentedScalar .doubleQuoted s'.line)
        let content' := content_trimmed ++ folded
        collectDoubleQuotedLoop s' content' fuel' startPos inFlow currentIndent inputEnd
      else if !isNbJsonBool c then
        -- C0 control character — [2] nb-json violation (§5.1)
        .error (.invalidControlChar c .doubleQuoted s.line s.col)
      else
        -- Regular character (nb-json minus '"' minus '\')
        let content' := content.push c
        collectDoubleQuotedLoop s.advance content' fuel' startPos inFlow currentIndent inputEnd

/-- Scan a double-quoted scalar.

    **Implements** (YAML 1.2.2 §7.3.1):
    - `[109] c-double-quoted(n,c)` = `'"' nb-double-text(n,c) '"'`
    - `[19]  c-double-quote` = `'"'`

    Content-level productions (`[107] nb-double-char`, `[108] ns-double-char`,
    `[110] nb-double-text`, `[111]`–`[113]`) are implemented in `collectDoubleQuotedLoop`.
    Escape sequences (`[62] c-ns-esc-char`) are in `processEscape`.
    Line folding (`[73] b-l-folded`) is in `foldQuotedNewlines`.

    **Pre**: Scanner at opening `"`.
    **Post**: Advances past closing `"`, emits `.scalar content .doubleQuoted`.
    Sets `simpleKeyAllowed := false`.
    **Error**: `unterminatedScalar` (EOF/fuel before closing `"`),
    `documentMarkerInScalar` (document marker at col 0 inside scalar §9.1.2),
    `underIndentedScalar` (continuation line below current block indent §8.1),
    `trailingContent` (non-whitespace/comment/`:` after closing `"` in block context §7.3.2). -/
@[yaml_spec "7.3.1" 109 "c-double-quoted",
  yaml_spec "7.3.1" 19 "c-double-quote"]
def scanDoubleQuoted (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let s_after_open := s.advance
  let fuel := s.inputEnd - s_after_open.offset + 1
  let (content, s_after_close) ← collectDoubleQuotedLoop s_after_open "" fuel startPos s.inFlow s.currentIndent s.inputEnd
  -- §7.3.2: In block context, validate trailing content
  if !s.inFlow then
    validateTrailingContent s_after_close s.inputEnd
  let s_with_token := s_after_close.emitAt startPos (.scalar content .doubleQuoted)
  .ok { s_with_token with simpleKeyAllowed := false }

-- Helper: Collect single-quoted content using structural recursion
@[yaml_spec "7.3.2" 117 "c-quoted-quote",
  yaml_spec "7.3.2" 118 "nb-single-char",
  yaml_spec "7.3.2" 119 "ns-single-char",
  yaml_spec "7.3.2" 121 "nb-single-text",
  yaml_spec "7.3.2" 122 "nb-single-one-line",
  yaml_spec "7.3.2" 123 "nb-ns-single-in-line",
  yaml_spec "7.3.2" 124 "s-single-next-line(n)",
  yaml_spec "7.3.2" 125 "nb-single-multi-line(n)",
  yaml_spec "5.1" 2 "nb-json"]
def collectSingleQuotedLoop (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    Except ScanError (String × ScannerState) :=
  match fuel with
  | 0 => .error (.unterminatedScalar .singleQuoted startPos.line)
  | fuel' + 1 =>
    match s.peek? with
    | none => .error (.unterminatedScalar .singleQuoted startPos.line)
    | some '\'' =>
      let s_after_quote := s.advance
      match s_after_quote.peek? with
      | some '\'' =>
        -- Escaped quote: ''
        let content' := content.push '\''
        collectSingleQuotedLoop s_after_quote.advance content' fuel' startPos inFlow currentIndent inputEnd
      | _ =>
        -- Closing quote found
        .ok (content, s_after_quote)
    | some c =>
      if isLineBreakBool c then do
        -- Line break: fold newlines
        let content_trimmed := trimTrailingWS content
        let (folded, s') ← foldQuotedNewlines s
        -- Validation: document markers at col 0 terminate
        if atDocumentStart s' || atDocumentEnd s' then
          throw (.documentMarkerInScalar .singleQuoted startPos.line)
        -- Validation: continuation line must be indented past block level
        if (s'.col : Int) ≤ currentIndent then
          throw (.underIndentedScalar .singleQuoted s'.line)
        let content' := content_trimmed ++ folded
        collectSingleQuotedLoop s' content' fuel' startPos inFlow currentIndent inputEnd
      else if !isNbJsonBool c then
        -- C0 control character — [2] nb-json violation (§5.1)
        .error (.invalidControlChar c .singleQuoted s.line s.col)
      else
        -- Regular character (nb-json minus "'")
        let content' := content.push c
        collectSingleQuotedLoop s.advance content' fuel' startPos inFlow currentIndent inputEnd

/-- Scan a single-quoted scalar.

    **Implements** (YAML 1.2.2 §7.3.2):
    - `[120] c-single-quoted(n,c)` = `"'" nb-single-text(n,c) "'"`
    - `[18]  c-single-quote` = `"'"`

    Content-level productions (`[117] c-quoted-quote`, `[118] nb-single-char`,
    `[121] nb-single-text`) are implemented in `collectSingleQuotedLoop`.
    Line folding (`[73] b-l-folded`) is in `foldQuotedNewlines`.

    **Pre**: Scanner at opening `'`.
    **Post**: Advances past closing `'`, emits `.scalar content .singleQuoted`.
    Sets `simpleKeyAllowed := false`.
    **Error**: `unterminatedScalar`, `documentMarkerInScalar`, `underIndentedScalar`,
    `trailingContent` (same conditions as `scanDoubleQuoted`). -/
@[yaml_spec "7.3.2" 120 "c-single-quoted",
  yaml_spec "7.3.2" 18 "c-single-quote"]
def scanSingleQuoted (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let s_after_open := s.advance
  let fuel := s.inputEnd - s_after_open.offset + 1
  let (content, s_after_close) ← collectSingleQuotedLoop s_after_open "" fuel startPos s.inFlow s.currentIndent s.inputEnd
  -- §7.3.2: In block context, validate trailing content
  if !s.inFlow then
    validateTrailingContent s_after_close s.inputEnd
  let s_with_token := s_after_close.emitAt startPos (.scalar content .singleQuoted)
  .ok { s_with_token with simpleKeyAllowed := false }

/-! ### Plain Scalar Character Predicates

    `canStartPlainScalarBool` and `isPlainSafeBool` are imported from
    `CharPredicates.lean` via `open L4YAML.CharPredicates`.
-/

-- Helper: Skip blank lines and count them (for plain scalar block context)
@[yaml_spec "6.4" 70 "l-empty(n,c)"]
def skipBlankLinesLoop (s : ScannerState) (cnt : Nat) (fuel : Nat) (inputEnd : Nat) :
    Nat × ScannerState :=
  match fuel with
  | 0 => (cnt, s)
  | fuel' + 1 =>
    let saved := s
    let s_after_spaces := skipSpaces s
    match s_after_spaces.peek? with
    | some c =>
      if isLineBreakBool c then
        let s_after_newline := consumeNewline s_after_spaces
        skipBlankLinesLoop s_after_newline (cnt + 1) fuel' inputEnd
      else
        (cnt, saved)
    | none => (cnt, s)

-- Result type for plain scalar collection
structure PlainScalarResult where
  content : String
  spaces : String
  state : ScannerState
  terminated : Bool

/-- Check if the current character terminates a plain scalar.
    Returns `some result` to terminate, `none` to continue scanning.

    Covers YAML 1.2.2 §7.3.3 termination conditions:
    - ` #` (comment after whitespace)
    - `: ` or `:` at EOF (value indicator)
    - Flow indicators in flow context
    - Document boundary (`---`/`...`) at column 0 -/
@[yaml_spec "7.3.3" 131 "ns-plain",
  yaml_spec "7.3.3" 126 "ns-plain-safe(c)",
  yaml_spec "7.3.3" 129 "ns-plain-char(c)"]
def collectPlainScalar_terminates? (c : Char) (s : ScannerState)
    (content spaces : String) (inFlow : Bool) : Option PlainScalarResult :=
  if c == '#' && spaces.length > 0 then
    some { content, spaces, state := s, terminated := true }
  else if c == ':' then
    let next := s.peekAt? 1
    let terminates := match next with
      | some n => isBlankBool n || (inFlow && isFlowIndicatorBool n)
      | none => true
    if terminates then
      some { content, spaces, state := s, terminated := true }
    else
      none
  else if inFlow && isFlowIndicatorBool c then
    some { content, spaces, state := s, terminated := true }
  else if s.col == 0 && atDocumentBoundary s then
    some { content, spaces, state := s, terminated := true }
  else
    none

/-- Handle a block-context line break during plain scalar collection.
    Returns `none` to terminate (under-indented or document boundary),
    or `some (content', s')` with folded content and new state to continue.

    Implements YAML 1.2.2 §7.3.3 block-context line folding:
    - Consume newline and skip blank lines
    - Check continuation indent and document boundaries
    - Fold: single empty line → space, multiple → newlines -/
@[yaml_spec "7.3.3" 134 "s-ns-plain-next-line(n,c)",
  yaml_spec "7.3.3" 135 "ns-plain-multi-line(n,c)"]
def collectPlainScalar_handleBlockLineBreak (s : ScannerState)
    (content : String) (contentIndent : Nat) (inputEnd : Nat) :
    Option (String × ScannerState) :=
  let s_after_newline := consumeNewline s
  let bfuel := inputEnd - s_after_newline.offset + 1
  let (emptyCount, s_after_blanks) := skipBlankLinesLoop s_after_newline 0 bfuel inputEnd
  let s_after_spaces := skipSpaces s_after_blanks
  if s_after_spaces.col < contentIndent then
    none
  else if atDocumentBoundary s_after_spaces then
    none
  else
    let content' := if emptyCount > 0 then
      content ++ String.ofList (List.replicate emptyCount '\n')
    else
      content ++ " "
    some (content', s_after_spaces)

-- Helper: Collect plain scalar content using structural recursion
@[yaml_spec "7.3.3" 132 "nb-ns-plain-in-line(c)",
  yaml_spec "7.3.3" 133 "ns-plain-one-line(c)",
  yaml_spec "7.3.3" 134 "s-ns-plain-next-line(n,c)",
  yaml_spec "7.3.3" 135 "ns-plain-multi-line(n,c)"]
def collectPlainScalarLoop (s : ScannerState) (content : String) (spaces : String) (fuel : Nat)
    (inFlow : Bool) (contentIndent : Nat) (inputEnd : Nat) :
    Except ScanError PlainScalarResult :=
  match fuel with
  | 0 => .ok { content, spaces, state := s, terminated := false }
  | fuel' + 1 =>
    match s.peek? with
    | none => .ok { content, spaces, state := s, terminated := true }
    | some c =>
      match collectPlainScalar_terminates? c s content spaces inFlow with
      | some result => .ok result
      | none =>
        if isLineBreakBool c then
          if inFlow then do
            let (folded, s_after_fold) ← foldQuotedNewlines s
            match s_after_fold.peek? with
            | some '#' =>
              .ok { content, spaces, state := s, terminated := true }
            | _ =>
              let content' := content ++ folded
              let prevLen := content'.length
              match collectPlainScalarLoop s_after_fold content' "" fuel' inFlow contentIndent inputEnd with
              | .ok result =>
                if result.content.length ≤ prevLen then
                  .ok { content, spaces, state := s, terminated := true }
                else .ok result
              | .error e => .error e
          else
            match collectPlainScalar_handleBlockLineBreak s content contentIndent inputEnd with
            | none =>
              .ok { content, spaces, state := s, terminated := true }
            | some (content', s') =>
              match s'.peek? with
              | some '#' =>
                .ok { content, spaces, state := s, terminated := true }
              | _ =>
                let prevLen := content'.length
                match collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd with
                | .ok result =>
                  if result.content.length ≤ prevLen then
                    .ok { content, spaces, state := s, terminated := true }
                  else .ok result
                | .error e => .error e
        else if isWhiteSpaceBool c then
          collectPlainScalarLoop s.advance content (spaces.push c) fuel' inFlow contentIndent inputEnd
        else
          if !isPlainSafeBool c inFlow then
            .ok { content, spaces, state := s, terminated := true }
          else
            let content' := content ++ spaces ++ (String.singleton c)
            collectPlainScalarLoop s.advance content' "" fuel' inFlow contentIndent inputEnd

/-- Scan a plain (unquoted) scalar.

    **Implements** (YAML 1.2.2 §7.3.3):
    - `[131] ns-plain(n,c)` = plain scalar content across potentially multiple lines
    - `[123] ns-plain-first(c)` — first character restrictions (via `canStartPlainScalarBool`)
    - `[126] ns-plain-safe(c)` — safe continuation characters (via `isPlainSafeBool`)
    - `[129] ns-plain-char(c)` — `:` and `#` context-sensitive handling
    - `[133] ns-plain-multi-line(c)` — continuation lines must be indented past block level

    Terminators: ` #` (comment), `: ` (value indicator), flow indicators (in flow),
    document boundaries (`---`/`...` at col 0), under-indented continuation.

    **Variable classification:**
    | Variable         | Kind     | Description |
    |------------------|----------|-------------|
    | `contentIndent`  | Position | Floor column for continuation lines |
    | `startPos`       | Pos      | Position for token attribution |

    **Pre**: Scanner at a character satisfying `canStartPlainScalarBool`.
    **Post**: Advances past all plain scalar content (including folded continuations),
    emits `.scalar content .plain`. Sets `simpleKeyAllowed := false`.
    **Error**: None directly (terminates by breaking). -/
@[yaml_spec "7.3.3" 131 "ns-plain"]
def scanPlainScalar (s : ScannerState) : Except ScanError ScannerState := do
  let startPos := s.currentPos
  let inFlow := s.inFlow
  -- §7.3.3: Continuation lines must be indented past the current block level.
  let contentIndent := if inFlow then s.col
    else (max 0 (s.currentIndent + 1)).toNat
  let fuel := (s.inputEnd - s.offset + 1) * 2
  let result ← collectPlainScalarLoop s "" "" fuel inFlow contentIndent s.inputEnd
  -- Trim trailing whitespace: plain scalars never have trailing WS per §7.3.3
  let content_trimmed := trimTrailingWS result.content
  let s_with_token := result.state.emitAt startPos (.scalar content_trimmed .plain)
  .ok { s_with_token with simpleKeyAllowed := false }

/-- States for folded block scalar newline processing (YAML 1.2.2 §8.1.3).

    The YAML spec distinguishes four contexts that determine how a newline
    is folded:

    - `start`   — before any content has been accumulated
    - `content` — after a normal content line (`s-nb-folded-text` [171]);
                   a following single newline is folded to a space
    - `empty`   — after a blank line (`b-l-trimmed` [170]);
                   newline is preserved (becomes `\n`)
    - `more`    — after a more-indented line (`s-nb-spaced-text` [173]);
                   newline is preserved (becomes `\n`)

    Defining these as an inductive rather than encoding in a `Bool` makes
    each case a named constructor for pattern matching in proofs. -/
inductive FoldState where
  | start   : FoldState
  | content : FoldState
  | empty   : FoldState
  | more    : FoldState
  deriving Repr, BEq

/-- Fold newlines in block scalar content per YAML 1.2.2 §8.1.3.

    **Implements** (folding pass for `[174] c-l+folded(n)`):
    - `[171] s-nb-folded-text(n)` — normal content line → fold newline to space
    - `[172] b-l-spaced(n)`       — more-indented line  → preserve newline
    - `[173] s-nb-spaced-text(n)` — more-indented line content
    - `[170] b-l-trimmed(n,c)`    — blank line           → preserve newline

    Input `raw` has already had indentation stripped by `scanBlockScalar`;
    lines at column 0 are content, lines starting with a space are
    more-indented.

    **State machine** (`FoldState`):
    - `start`   — initial state, no pending newline
    - `content` — in a normal content line; a pending newline folds to space
    - `empty`   — saw at least one blank line; pending newlines preserved
    - `more`    — in/after a more-indented line; pending newlines preserved

    On `\n`: don't emit yet — record blank lines in `pendingNL` count.
    On first non-`\n` char of a new line: emit pending newlines based on
    state and line classification (space-leading → more, otherwise → content). -/
@[yaml_spec "8.1.3" 174 "c-l+folded",
  yaml_spec "8.1.3" 175 "s-nb-folded-text(n)",
  yaml_spec "8.1.3" 176 "l-nb-folded-lines(n)",
  yaml_spec "8.1.3" 177 "s-nb-spaced-text(n)",
  yaml_spec "8.1.3" 178 "b-l-spaced(n)",
  yaml_spec "8.1.3" 179 "l-nb-spaced-lines(n)",
  yaml_spec "8.1.3" 180 "l-nb-same-lines(n)",
  yaml_spec "8.1.3" 181 "l-nb-diff-lines(n)",
  yaml_spec "8.1.3" 182 "l-folded-content(n,t)"]
def foldBlockContent (raw : String) : String :=
  go raw.toList "" .start 0
where
  appendNewlines (acc : String) : Nat → String
    | 0 => acc
    | n + 1 => appendNewlines (acc.push '\n') n
  go : List Char → String → FoldState → Nat → String
    -- End of input: don't emit trailing newlines (chomping handles them)
    | [], acc, _, _ => acc
    -- Newline: don't emit yet, increment pending count
    | '\n' :: rest, acc, st, pending =>
      go rest acc st (pending + 1)
    -- First non-newline char after line boundary (pending > 0):
    -- Decide what to emit for the pending newline(s).
    -- `pending + 1` is the total number of `\n` chars seen since last content.
    | c :: rest, acc, st, pending + 1 =>
      -- Classify this new line: space-leading → more-indented [173]
      let isMore := c == ' '
      let newSt := if isMore then FoldState.more else .content
      -- Emit pending newline(s) based on previous line state.
      -- The rules derive from YAML 1.2.2 productions [170]-[181]:
      --   content→1→content : b-as-space [176] → fold to ` `
      --   content→1→more    : b-as-line-feed [177] → `\n`
      --   content→N>1→content : b-non-content + (N-1) l-empty → (N-1) `\n`s
      --   content→N>1→more   : b-as-line-feed + (N-1) l-empty → N `\n`s
      --   more→N→any         : b-as-line-feed + (N-1) l-empty → N `\n`s
      --   start→N→any        : l-empty × N → N `\n`s
      let acc := match st with
        | .start => appendNewlines acc (pending + 1)
        | .content =>
          if pending == 0 && !isMore then
            -- Single newline between two content lines → fold to space
            acc.push ' '
          else if pending == 0 && isMore then
            -- Single newline, content → more → preserve as line-feed
            acc.push '\n'
          else if isMore then
            -- Multiple newlines, next is more → all preserved
            appendNewlines acc (pending + 1)
          else
            -- Multiple newlines, next is content → first is b-non-content (silent)
            appendNewlines acc pending
        | .more => appendNewlines acc (pending + 1)
        | .empty => appendNewlines acc (pending + 1)  -- shouldn't occur in practice
      go rest (acc.push c) newSt 0
    -- Normal character within a line (pending == 0)
    | c :: rest, acc, st, 0 =>
      let newSt := match st with
        | .start => if c == ' ' then FoldState.more else .content
        | s => s
      go rest (acc.push c) newSt 0

-- Helper: Auto-detect block scalar content indentation
@[yaml_spec "8.1" 163 "c-indentation-indicator"]
def autoDetectBlockScalarIndentLoop (probe : ScannerState) (maxWSCol maxWSLine : Nat)
    (minContentIndent : Nat) (fuel : Nat) (inputEnd : Nat) :
    Nat × Nat × ScannerState × Option ScanError :=
  match fuel with
  | 0 =>
    -- No content found. Use max whitespace column as indent
    if maxWSCol > minContentIndent then
      (maxWSCol, maxWSLine, probe, none)
    else
      (minContentIndent, maxWSLine, probe, none)
  | fuel' + 1 =>
    let probe_after_spaces := skipSpaces probe
    match probe_after_spaces.peek? with
    | some c =>
      -- Tab in indentation zone
      if c == '\t' && probe_after_spaces.col < minContentIndent then
        (0, maxWSLine, probe, some (.tabInIndentation probe_after_spaces.line probe_after_spaces.col))
      else if isLineBreakBool c then
        -- Whitespace-only line: track max column
        let maxWSCol' := if probe_after_spaces.col > maxWSCol then probe_after_spaces.col else maxWSCol
        let maxWSLine' := if probe_after_spaces.col > maxWSCol then probe_after_spaces.line else maxWSLine
        let probe' := consumeNewline probe_after_spaces
        autoDetectBlockScalarIndentLoop probe' maxWSCol' maxWSLine' minContentIndent fuel' inputEnd
      else
        -- First non-empty line: set contentIndent
        let detectedIndent := max minContentIndent probe_after_spaces.col
        -- Validate preceding whitespace-only lines
        if maxWSCol > detectedIndent then
          (0, maxWSLine, probe, some (.blockScalarIndentMismatch maxWSLine maxWSCol))
        else
          (detectedIndent, maxWSLine, probe, none)
    | none =>
      -- No more content
      if maxWSCol > minContentIndent then
        (maxWSCol, maxWSLine, probe, none)
      else
        (minContentIndent, maxWSLine, probe, none)

@[yaml_spec "8.1" 163 "c-indentation-indicator"]
def autoDetectBlockScalarIndent (s : ScannerState) (minContentIndent : Nat) (inputEnd : Nat) :
    Nat × Option ScanError :=
  let fuel := inputEnd - s.offset + 1
  let (indent, _, _, err) := autoDetectBlockScalarIndentLoop s 0 0 minContentIndent fuel inputEnd
  (indent, err)

-- Helper: Consume exactly `count` spaces (for s-indent in block scalars)
@[yaml_spec "6.1" 63 "s-indent(n)"]
def consumeExactSpaces (s : ScannerState) (count : Nat) : Nat × ScannerState :=
  match count with
  | 0 => (0, s)
  | count' + 1 =>
    match s.peek? with
    | some ' ' =>
      let (consumed, s') := consumeExactSpaces s.advance count'
      (consumed + 1, s')
    | _ => (0, s)

-- Helper: Collect content characters until line break
@[yaml_spec "8.1.2" 171 "l-nb-literal-text",
  yaml_spec "5.4" 27 "nb-char"]
def collectLineContentLoop (s : ScannerState) (content : String) (fuel : Nat) :
    String × ScannerState :=
  match fuel with
  | 0 => (content, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if isLineBreakBool c then
        (content, s)
      else
        collectLineContentLoop s.advance (content.push c) fuel'
    | none => (content, s)

-- Helper: Collect block scalar raw content using structural recursion
@[yaml_spec "8.1.2" 172 "b-nb-literal-next(n)",
  yaml_spec "8.1.2" 173 "l-literal-content(n,t)"]
def collectBlockScalarLoop (s : ScannerState) (rawContent : String) (fuel : Nat)
    (contentIndent : Nat) (inputEnd : Nat) :
    String × ScannerState :=
  match fuel with
  | 0 => (rawContent, s)
  | fuel' + 1 =>
    -- Check for document boundary
    if s.col == 0 && atDocumentBoundary s then
      (rawContent, s)
    else
      -- Try to consume s-indent(contentIndent): exactly contentIndent spaces
      let (spacesConsumed, s_after_spaces) := consumeExactSpaces s contentIndent
      match s_after_spaces.peek? with
      | none => (rawContent, s_after_spaces)
      | some c =>
        if isLineBreakBool c then
          -- l-empty line: fewer than contentIndent spaces followed by line break
          let rawContent' := rawContent.push '\n'
          let s' := consumeNewline s_after_spaces
          collectBlockScalarLoop s' rawContent' fuel' contentIndent inputEnd
        else if spacesConsumed < contentIndent && !isLineBreakBool c then
          -- Less-indented non-empty line: end of block scalar content
          (rawContent, s)
        else
          -- nb-char+: content characters until line break
          let innerFuel := inputEnd - s_after_spaces.offset + 1
          let (lineContent, s_after_line) := collectLineContentLoop s_after_spaces "" innerFuel
          let rawContent' := rawContent ++ lineContent
          -- Consume line break if present
          match s_after_line.peek? with
          | some c' =>
            if isLineBreakBool c' then
              let rawContent'' := rawContent'.push '\n'
              let s' := consumeNewline s_after_line
              collectBlockScalarLoop s' rawContent'' fuel' contentIndent inputEnd
            else
              collectBlockScalarLoop s_after_line rawContent' fuel' contentIndent inputEnd
          | none => (rawContent', s_after_line)

/-- Helper for scanBlockScalar header parsing using structural recursion.

    Parses up to `fuel` header characters: chomp indicator (`-`/`+`) and
    indentation indicator (digit 1-9) in either order per YAML §8.1 [162].

    **Termination**: Structurally recursive on `fuel`. -/
@[yaml_spec "8.1" 162 "c-b-block-header"]
def parseBlockHeaderLoop (s : ScannerState) (chomp : ChompStyle) (explicitOffset : Option Nat)
    (fuel : Nat) : ChompStyle × Option Nat × ScannerState :=
  match fuel with
  | 0 => (chomp, explicitOffset, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '-' => parseBlockHeaderLoop s.advance .strip explicitOffset fuel'
    | some '+' => parseBlockHeaderLoop s.advance .keep explicitOffset fuel'
    | some c =>
      if c.isDigit && c != '0' then
        parseBlockHeaderLoop s.advance chomp (some (c.toNat - '0'.toNat)) fuel'
      else (chomp, explicitOffset, s)
    | none => (chomp, explicitOffset, s)

/-- Skip optional comment after block-scalar header whitespace.

    **Implements** part of `s-b-comment` (§6.7 / production [77]):
    `c-nb-comment-text` requires `#` preceded by whitespace.

    **Decomposed for provability**: 3 branch points (peek?, peekBack?, commentOk).
    Extracted from `scanBlockScalar` so proofs unfold only this piece. -/
@[yaml_spec "6.7" 77 "s-b-comment",
  yaml_spec "6.6" 75 "c-nb-comment-text",
  yaml_spec "5.4" 27 "nb-char"]
def scanBlockScalarSkipComment (s : ScannerState) : ScannerState :=
  match s.peek? with
  | some '#' =>
    -- Check raw input: # must be preceded by whitespace (not at start-of-line here)
    let commentOk := match s.peekBack? with
      | some c => isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF'  -- BOM is transparent (§5.2)
      | none => false
    if commentOk then
      let commentPos := s.currentPos
      let s_after_hash := s.advance  -- skip '#'
      let fuel := s_after_hash.inputEnd - s_after_hash.offset
      let (text, s') := collectCommentTextLoop s_after_hash "" fuel
      { s' with comments := s'.comments.push (commentPos, text) }
    else s  -- `#` without preceding whitespace — not a comment
  | _ => s

/-- Consume required newline (or EOF) after block-scalar header.

    **Implements** `b-comment` (§6.7 / production [76]):
    expects a line break or end-of-input after the header line.

    **Decomposed for provability**: 3 branch points (peek?, isLineBreakBool, hasMore).
    Extracted from `scanBlockScalar` so proofs unfold only this piece. -/
@[yaml_spec "6.6" 76 "b-comment",
  yaml_spec "5.4" 30 "b-non-content"]
def scanBlockScalarConsumeNewline (s : ScannerState) : Except ScanError ScannerState :=
  match s.peek? with
  | some c =>
    if isLineBreakBool c then .ok (consumeNewline s)
    else if !s.hasMore then .ok s
    else .error (.expectedNewline s.line)
  | none => .ok s

/-- Collect block-scalar body: detect indentation, collect content, apply chomp/fold, emit token.

    **Implements** (YAML 1.2.2 §8.1):
    - `[163] c-indentation-indicator(m)` — explicit or auto-detect
    - `[171] l-nb-literal-text(n)` / folded content
    - `[164] c-chomping-indicator(t)` — strip / clip / keep

    **Decomposed for provability**: ~5 branch points but most are pure string
    computation (chomp, fold) that don't affect scanner-state fields used in proofs.
    Extracted from `scanBlockScalar` so proofs for `simpleKey`, `simpleKeyStack`,
    `tokens` need only unfold this smaller definition.

    **Pre**: `s_after_newline` is past the header line; `s_orig` provides `currentIndent` and `inputEnd`.
    **Post**: Emits `.scalar content style`, clears simpleKey. -/
@[yaml_spec "8.1" 163 "c-indentation-indicator",
  yaml_spec "8.1" 171 "l-nb-literal-text",
  yaml_spec "8.1" 164 "c-chomping-indicator",
  yaml_spec "8.1.1" 165 "b-chomped-last(t)",
  yaml_spec "8.1.1" 166 "l-chomped-empty(n,t)",
  yaml_spec "8.1.1" 167 "l-strip-empty(n)",
  yaml_spec "8.1.1" 168 "l-keep-empty(n)",
  yaml_spec "8.1.1" 169 "l-trail-comments(n)"]
def scanBlockScalarBody (s_orig : ScannerState) (s_after_newline : ScannerState)
    (chomp : ChompStyle) (explicitOffset : Option Nat) (isLiteral : Bool) (startPos : YamlPos) :
    Except ScanError ScannerState :=
  let parentIndent : Int := s_orig.currentIndent
  let minContentIndent : Nat := (max 0 (parentIndent + 1)).toNat
  let (contentIndent, autoDetectErr?) := match explicitOffset with
    | some m =>
      ((max 0 (parentIndent + (m : Int))).toNat, (none : Option ScanError))
    | none =>
      autoDetectBlockScalarIndent s_after_newline minContentIndent s_orig.inputEnd
  match autoDetectErr? with
  | some err => .error err
  | none =>
    let fuel := s_orig.inputEnd - s_after_newline.offset + 1
    let (rawContent, s_after_content) := collectBlockScalarLoop s_after_newline "" fuel contentIndent s_orig.inputEnd
    let stripTrailingNewlines (str : String) : String :=
      String.ofList (str.toList.reverse.dropWhile (· == '\n') |>.reverse)
    let content := match chomp with
      | .strip => stripTrailingNewlines rawContent
      | .clip =>
        let stripped := stripTrailingNewlines rawContent
        if rawContent.endsWith "\n" then stripped ++ "\n" else stripped
      | .keep => rawContent
    let content := if isLiteral then content else foldBlockContent content
    let style := if isLiteral then ScalarStyle.literal else ScalarStyle.folded
    let s_with_token := s_after_content.emitAt startPos (.scalar content style)
    -- J.2 dual-write: also clear `pendingKeyActive`.  Block scalars
    -- emit on a fresh line so any active reservation belongs to a
    -- previous (already-resolved or now-stale) candidate.
    .ok { s_with_token with simpleKeyAllowed := true,
                            simpleKey := { possible := false },
                            pendingKeyActive := none }

/-- Scan a block scalar (literal `|` or folded `>`).

    **Implements** (YAML 1.2.2 §8.1):
    - `[170] c-l+literal(n)` = `"|" c-b-block-header(t,m) l-literal-content(n+m,t)`
    - `[174] c-l+folded(n)`  = `">" c-b-block-header(t,m) l-folded-content(n+m,t)`
    - `[162] c-b-block-header(t,m)` = `(c-indentation-indicator(m) c-chomping-indicator(t) | ...) s-b-comment`
    - `[163] c-indentation-indicator(m)` = `ns-dec-digit` (explicit) | `ε` (auto-detect)
    - `[164] c-chomping-indicator(t)` = `"-"` (STRIP) | `"+"` (KEEP) | `ε` (CLIP)
    - `[171] l-nb-literal-text(n)` = `l-empty(n,BLOCK-IN)* s-indent(n) nb-char+`
    - `[63]  s-indent(n)` = `s-space × n`  ← **spaces only**

    **Decomposed for provability**: Comment handling (`scanBlockScalarSkipComment`,
    3 branches), newline consumption (`scanBlockScalarConsumeNewline`, 3 branches),
    and body processing (`scanBlockScalarBody`, ≤5 branches) are each extracted.
    This wrapper has only 1 branch point (match on newline result), eliminating
    the need for `set_option maxHeartbeats 400000` in proofs.

    **Pre**: Scanner at `|` or `>`. `s.col` = `n` (parent indent level).
    **Post**: Scanner past block scalar content. Emits `.scalar content style`.
    **Error**: Missing newline after header. -/
@[yaml_spec "8.1" 170 "c-l+literal",
  yaml_spec "8.1" 174 "c-l+folded",
  yaml_spec "8.1" 162 "c-b-block-header",
  yaml_spec "8.1" 163 "c-indentation-indicator",
  yaml_spec "8.1" 164 "c-chomping-indicator",
  yaml_spec "8.1" 171 "l-nb-literal-text",
  yaml_spec "8.1" 63 "s-indent",
  yaml_spec "8.1.2" 172 "b-nb-literal-next(n)",
  yaml_spec "8.1.2" 173 "l-literal-content(n,t)"]
def scanBlockScalar (s : ScannerState) : Except ScanError ScannerState :=
  let header := parseBlockHeaderLoop s.advance .clip none 2
  let s_after_comment := scanBlockScalarSkipComment (skipWhitespace header.2.2)
  match scanBlockScalarConsumeNewline s_after_comment with
  | .error e => .error e
  | .ok s_after_newline =>
    scanBlockScalarBody s s_after_newline header.1 header.2.1 (s.peek? == some '|') s.currentPos

end L4YAML.Scanner
