/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State

/-!
# Scanner — Whitespace, Comments, and Line Prefixes

Whitespace consumption (`s-space*`, `s-white*`), newline handling
(`b-break`, `b-non-content`), and comment collection / line-prefix skipping
for the scanner.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2.

## YAML 1.2.2 distinctions

- `[31] s-space` = `#x20` (space only)
- `[32] s-tab`  = `#x09` (tab only)
- `[33] s-white` = `s-space | s-tab`

Indentation ([63] `s-indent(n)` = `s-space × n`) uses **spaces only**.
Separation ([66] `s-separate-in-line` = `s-white+`) allows **spaces + tabs**.

- `skipSpaces`      — matches `s-space*`  (for `s-indent`)
- `skipWhitespace`  — matches `s-white*`  (for `s-separate-in-line`)
- `skipToContent`   — composite line-prefix + comment consumer (`s-l-comments`)
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Whitespace Consumption -/

/-- Check whether any TAB character appears in the contiguous whitespace
    (spaces + tabs) immediately before the current offset.  Scans backward
    without consuming anything.  Used by `scanBlockEntry` to enforce YAML §6.1:
    tabs must not be used in indentation.  Because `skipToContent` consumes
    whitespace (including tabs) on same-line continuations without checking,
    this backward scan detects tabs that slipped through as indentation before
    the block entry indicator.

    Handles `-\t-`, `- \t-`, `-\t -`, etc. — any tab in the preceding
    whitespace run means a tab contributed to the indentation of this token. -/
@[yaml_spec "6.1"]
def ScannerState.hasTabInPrecedingWhitespaceLoop (input : String) (pos : Nat) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    if pos == 0 then false
    else
      let prevPos := (String.Pos.Raw.prev input ⟨pos⟩).byteIdx
      let c := String.Pos.Raw.get input ⟨prevPos⟩
      if c == '\t' then true
      else if c == ' ' then ScannerState.hasTabInPrecedingWhitespaceLoop input prevPos fuel'
      else false  -- non-whitespace character: stop scanning

@[yaml_spec "6.1"]
def ScannerState.hasTabInPrecedingWhitespace (s : ScannerState) : Bool :=
  ScannerState.hasTabInPrecedingWhitespaceLoop s.input s.offset s.offset

/-- Helper for skipWhitespace using structural recursion.

    **Termination**: Structurally recursive on `fuel`. -/
@[yaml_spec "6.2" 66 "s-separate-in-line"]
def skipWhitespaceLoop (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c => if isWhiteSpaceBool c then skipWhitespaceLoop s.advance fuel' else s
    | none => s
termination_by fuel

/-- Skip zero or more `s-white` characters (spaces + tabs).
    Implements `s-white*` — use for `s-separate-in-line` ([66]) contexts.
    **Not** for indentation. See `skipSpaces` for `s-indent`. -/
@[yaml_spec "6.2" 66 "s-separate-in-line"]
def skipWhitespace (s : ScannerState) : ScannerState :=
  skipWhitespaceLoop s (s.inputEnd - s.offset)

/-- Helper for skipSpaces using structural recursion.

    **Termination**: Structurally recursive on `fuel`. -/
@[yaml_spec "6.1" 63 "s-indent(n)"]
def skipSpacesLoop (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some ' ' => skipSpacesLoop s.advance fuel'
    | _ => s
termination_by fuel

/-- Skip zero or more `s-space` characters (spaces only, no tabs).
    Implements `s-space*` — use for `s-indent(n)` ([63]) contexts.
    YAML §6.1: "tab characters must not be used in indentation". -/
@[yaml_spec "6.1" 63 "s-indent(n)"]
def skipSpaces (s : ScannerState) : ScannerState :=
  skipSpacesLoop s (s.inputEnd - s.offset)

/-- Helper for skipToEndOfLine using structural recursion.

    **Termination**: Structurally recursive on `fuel`. -/
def skipToEndOfLineLoop (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c => if isLineBreakBool c then s else skipToEndOfLineLoop s.advance fuel'
    | none => s
termination_by fuel

/-- Skip to the end of the current line (stop before line break).
    Implements `nb-char*` lookahead used by `%YAML` / `%TAG` directive
    trailing-content handling (§6.8). -/
@[yaml_spec "5.4" 27 "nb-char"]
def skipToEndOfLine (s : ScannerState) : ScannerState :=
  skipToEndOfLineLoop s (s.inputEnd - s.offset)

/-- Consume a newline (LF, CR, or CRLF), setting `needIndentCheck := true`
    so the next `scanNextToken` processes indentation.
    For CRLF, the `\r` advance handles line counting; the `\n` byte is
    skipped by raw offset increment to avoid double-counting the line. -/
@[yaml_spec "5.4" 28 "b-break",
  yaml_spec "5.4" 29 "b-as-line-feed"]
def consumeNewline (s : ScannerState) : ScannerState :=
  match s.peek? with
  | some '\n' => { s.advance with needIndentCheck := true }
  | some '\r' =>
    let s' := s.advance
    match s'.peek? with
    | some '\n' =>
      -- CRLF: skip the \n byte without calling advance (which would
      -- double-count the line, since \r already incremented it).
      { s' with
        offset := (String.Pos.Raw.next s'.input ⟨s'.offset⟩).byteIdx,
        needIndentCheck := true }
    | _ => { s' with needIndentCheck := true }
  | _ => s

/-- Phase 1: Skip indentation and whitespace, returning the updated state.

    Returns `.ok s'` with the whitespace-consumed state, or `.error` on
    tab-as-indentation violations.

    Refactored from `do`+`mut` to explicit state threading so that `unfold`
    exposes proof-tractable structure (no monadic join points). -/
@[yaml_spec "6.1",
  yaml_spec "6.3" 67 "s-line-prefix(n,c)",
  yaml_spec "6.3" 68 "s-block-line-prefix(n)"]
def skipToContentWs (s : ScannerState) : Except ScanError ScannerState :=
  -- After a newline, use skipSpaces for indentation (s-indent [63]: spaces only).
  -- Then check for tab-as-indentation, using currentIndent to determine the
  -- boundary between indentation territory and separation territory.
  if s.needIndentCheck then
    let s1 := skipSpaces s
    -- Key insight: once col > currentIndent, we've consumed enough spaces
    -- to be inside the current block's content area. Any tabs here are
    -- s-separate-in-line [66] (legal separation), not indentation.
    -- Special case: when currentIndent < 0 (stream level, before any block
    -- is opened), col > currentIndent is trivially true for all col ≥ 0,
    -- so we must check explicitly for tabs that act as block indentation.
    -- Exception: in flow context, tabs are valid s-separate-in-line [66],
    -- even at stream level (s-indent(0) = 0 spaces, then tabs are separation).
    if (!s1.inFlow && s1.currentIndent < 0) || (s1.col : Int) ≤ s1.currentIndent then
      -- Still at or below the current block's indent level (or stream level).
      -- A tab here would extend into indentation territory — §6.1 violation.
      match s1.peek? with
      | some '\t' =>
        -- Peek past tabs/spaces to see what follows
        let probe := skipWhitespace s1
        match probe.peek? with
        | some '#' => .ok (skipWhitespace s1)      -- tab before comment: allowed
        | some c =>
          if isLineBreakBool c then .ok (skipWhitespace s1)  -- tab on blank line: allowed
          -- At stream level (currentIndent < 0), tabs before flow indicators
          -- are valid s-separate-in-line [66] for s-l+flow-in-block [197].
          -- §6.1 only constrains s-indent(n), not s-separate-in-line.
          -- Covers: flow openers {[, closers }], quotes "', and
          -- node properties/alias !&* — all unambiguously flow content.
          else if s1.currentIndent < 0 &&
            (c == '{' || c == '[' || c == '}' || c == ']' ||
             c == '"' || c == '\'' || c == '!' || c == '&' || c == '*')
            then .ok (skipWhitespace s1)
          else
            -- Tab followed by block content: tab used as indentation — §6.1
            .error (.tabInIndentation s1.line s1.col)
        | none => .ok (skipWhitespace s1)           -- tab before EOF: allowed
      | _ => .ok s1
    else
      -- Past indentation boundary or in flow context: tabs are legal separation
      .ok (skipWhitespace s1)
  else
    .ok (skipWhitespace s)

/-- Helper: collect comment text characters until end-of-line or EOF.

    Structurally recursive on `fuel`.  Advances the scanner past each
    collected character while accumulating the text string. -/
@[yaml_spec "6.6" 75 "c-nb-comment-text",
  yaml_spec "5.4" 27 "nb-char"]
def collectCommentTextLoop (s : ScannerState) (text : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (text, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c => if isLineBreakBool c then (text, s)
                else collectCommentTextLoop s.advance (text.push c) fuel'
    | none => (text, s)
termination_by fuel

/-- Phase 2: Skip optional comment (from `#` to end of line).

    §6.7: `c-nb-comment-text` (#) requires preceding `s-separate-in-line`.
    `s-separate-in-line` = `s-white+` | `start-of-line`.
    Check raw input: `#` must be preceded by whitespace or be at column 0.

    Comments are collected into `ScannerState.comments` as a side-channel
    (§6.6: comments have no effect on the serialization tree). -/
@[yaml_spec "6.6" 75 "c-nb-comment-text",
  yaml_spec "6.6" 77 "s-b-comment",
  yaml_spec "5.4" 27 "nb-char"]
def skipToContentComment (s : ScannerState) : ScannerState :=
  match s.peek? with
  | some '#' =>
    let commentOk := s.col == 0 || match s.peekBack? with
      | some c => isWhiteSpaceBool c || isLineBreakBool c || c == '\uFEFF'  -- BOM is transparent (§5.2)
      | none => true   -- start of input
    if commentOk then
      let commentPos := s.currentPos
      let s_after_hash := s.advance  -- skip '#'
      let fuel := s_after_hash.inputEnd - s_after_hash.offset
      let (text, s') := collectCommentTextLoop s_after_hash "" fuel
      { s' with comments := s'.comments.push (commentPos, text) }
    else s
  | _ => s

/-- Structural-recursive loop for `skipToContent`.

    Each iteration: (1) skip whitespace/indentation via `skipToContentWs`,
    (2) skip optional comment via `skipToContentComment`,
    (3) if line break: consume it and recurse; otherwise stop.

    **Proof-friendly design**: no `do`-notation, no `mut`, no monadic bind.
    Every intermediate state is an explicit `let`-binding, making `unfold`
    expose simple `match`/`if` trees that `split` can decompose. -/
@[yaml_spec "6.7" 79 "s-l-comments"]
def skipToContentLoop (s : ScannerState) (fuel : Nat) : Except ScanError ScannerState :=
  match fuel with
  | 0 => .ok s
  | fuel' + 1 =>
    match skipToContentWs s with
    | .error e => .error e
    | .ok s1 =>
      let s2 := skipToContentComment s1
      match s2.peek? with
      | some c =>
        if isLineBreakBool c then
          let s3 := consumeNewline s2
          -- §7.4.2: In flow sequences, implicit keys are restricted to a
          -- single line.  Don't re-enable simple keys on newline so that
          -- `saveSimpleKey` preserves (rather than overwrites) the pending
          -- key, allowing `scanValue` to detect the line mismatch.
          if !s3.isInFlowSequence then
            skipToContentLoop { s3 with simpleKeyAllowed := true } fuel'
          else
            skipToContentLoop s3 fuel'
        else .ok s2
      | none => .ok s2
termination_by fuel

/-- Advance past whitespace, comments, and line breaks to the next content character.

    **Implements**: `s-l-comments` ([79]) and parts of `l-comment` ([78]).

    Each iteration of the outer loop handles one "line" of skippable content:
    1. Skip indentation spaces (`s-indent`, [63]): `s-space*` via `skipSpaces`.
    2. Tab-as-indentation check (§6.1), guarded by `currentIndent`:
       - `col > currentIndent` → past indentation → tabs are `s-separate-in-line` [66] (legal)
       - `col ≤ currentIndent` → in indentation zone → tabs before content are an error
       - Flow context → no indentation significance → tabs always legal
    3. Skip remaining `s-separate-in-line` whitespace (spaces + tabs) via `skipWhitespace`.
    4. Skip optional comment: if `#`, consume to end of line.
    5. If line break: consume it, set `simpleKeyAllowed`, continue to next line.
    6. Otherwise: we've reached content — stop.

    **Error**: Tab character used as indentation (before content on a new line). -/
@[yaml_spec "6.6" 79 "s-l-comments",
  yaml_spec "6.6" 78 "l-comment",
  yaml_spec "6.7" 80 "s-separate(n,c)",
  yaml_spec "6.7" 81 "s-separate-lines(n)"]
def skipToContent (s : ScannerState) : Except ScanError ScannerState :=
  skipToContentLoop s (s.inputEnd - s.offset + 1)

/-- Skip trailing `s-white` (spaces + tabs) using structural recursion.
    General-purpose helper used by `validateFlowClose`, `validateTrailingContent`,
    and `scanDocumentEnd`. -/
@[yaml_spec "6.2" 66 "s-separate-in-line"]
def skipTrailingSpaces (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if c == ' ' || c == '\t' then
        skipTrailingSpaces s.advance fuel'
      else
        s
    | none => s

end L4YAML.Scanner
