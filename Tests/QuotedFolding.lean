import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Quoted Scalar Folding Tests

Tests for `foldQuotedNewlines` (§6.5, §7.3.1, §7.3.2) and escaped line
breaks (`\` + newline, §5.7 [112]).

Covers the 5 algorithmic bugs fixed in step 6b (ANALYSIS.md §2.F):
- **Bug A**: Mandatory `newline` after `skipHWhitespace` removed
- **Bug B**: Off-by-one in empty line counting fixed
- **Bug C**: Trailing whitespace trimming added
- **Bug D**: `skipSpaces` → `skipHWhitespace` (tabs handled)
- **Bug E**: `\` + newline (escaped line break / line continuation) added
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser

namespace Tests.QuotedFolding

/-! ## Helpers -/

/-- Run a parser on input and return the result. -/
def runParser {α : Type} (p : YamlParser α) (input : String) : Except String α :=
  let stream := YamlStream.ofString input
  match Parser.run p stream with
  | .ok _ v => .ok v
  | .error _ err => .error (toString err)

/-- Extract scalar content from a YamlValue, or return an error string. -/
def getContent (result : Except String YamlValue) : Except String String :=
  match result with
  | .ok v =>
    match v.asString? with
    | some s => .ok s
    | none => .error s!"expected scalar, got {repr v}"
  | .error e => .error e

/-- Test that a parser produces a specific scalar content string. -/
def expectContent (label : String) (p : YamlParser YamlValue) (input : String)
    (expected : String) : IO Unit := do
  IO.print s!"  {label}: "
  match getContent (runParser p input) with
  | .ok content =>
    if content == expected then
      IO.println "✓"
    else
      IO.println s!"✗ expected {repr expected}, got {repr content}"
  | .error e => IO.println s!"✗ parse error: {e}"

/-- Test that a parser fails on the given input. -/
def expectFailure (label : String) (p : YamlParser YamlValue) (input : String) : IO Unit := do
  IO.print s!"  {label}: "
  match runParser p input with
  | .ok v => IO.println s!"✗ expected failure, got {repr v}"
  | .error _ => IO.println "✓"

/-! ## Bug A: Simple fold (single newline → space)

`foldQuotedNewlines` previously required a mandatory `newline` after
`skipHWhitespace`, crashing on the simplest fold case where the next
line has content (not a blank line).

YAML spec §6.5: A line break followed by content on the next line
folds to a single space.
-/

def testBugA_SimpleFold : IO Unit := do
  IO.println "--- Bug A: Simple fold (newline → space) ---"
  -- "hello\n world" → "hello world"  (basic fold, content on next line)
  expectContent "dq basic fold"
    doubleQuotedScalar "\"hello\n world\"" "hello world"
  -- "foo\nbar" → "foo bar"  (no leading whitespace on continuation)
  expectContent "dq no leading ws"
    doubleQuotedScalar "\"foo\nbar\"" "foo bar"
  -- Single-quoted equivalent
  expectContent "sq basic fold"
    singleQuotedScalar "'hello\n world'" "hello world"
  expectContent "sq no leading ws"
    singleQuotedScalar "'foo\nbar'" "foo bar"

/-! ## Bug B: Empty line counting (preserved newlines)

The off-by-one meant blank lines inside quoted scalars produced the
wrong number of newlines. YAML §6.5: empty lines (a line break
followed by another line break) are preserved as literal newlines.
One empty line = one `\n`, two empty lines = two `\n`s, etc.
-/

def testBugB_EmptyLines : IO Unit := do
  IO.println "--- Bug B: Empty line counting (preserved newlines) ---"
  -- "a\n\nb" → "a\nb"  (one empty line = one preserved newline)
  expectContent "dq one empty line"
    doubleQuotedScalar "\"a\n\nb\"" "a\nb"
  -- "a\n\n\nb" → "a\n\nb"  (two empty lines = two newlines)
  expectContent "dq two empty lines"
    doubleQuotedScalar "\"a\n\n\nb\"" "a\n\nb"
  -- "a\n\n\n\nb" → "a\n\n\nb"  (three empty lines = three newlines)
  expectContent "dq three empty lines"
    doubleQuotedScalar "\"a\n\n\n\nb\"" "a\n\n\nb"
  -- Single-quoted equivalents
  expectContent "sq one empty line"
    singleQuotedScalar "'a\n\nb'" "a\nb"
  expectContent "sq two empty lines"
    singleQuotedScalar "'a\n\n\nb'" "a\n\nb"

/-! ## Bug C: Trailing whitespace trimming

YAML §7.3.1: "All leading and trailing white space characters on each
line are excluded from the content." Before folding, trailing spaces
and tabs on the line before the break must be trimmed.
-/

def testBugC_TrailingWsTrim : IO Unit := do
  IO.println "--- Bug C: Trailing whitespace trimming ---"
  -- "hello   \n world" → "hello world"  (trailing spaces trimmed)
  expectContent "dq trailing spaces"
    doubleQuotedScalar "\"hello   \n world\"" "hello world"
  -- "hello\t\n world" → "hello world"  (trailing tab trimmed)
  expectContent "dq trailing tab"
    doubleQuotedScalar "\"hello\t\n world\"" "hello world"
  -- "hello \t \n world" → "hello world"  (mixed trailing ws trimmed)
  expectContent "dq trailing mixed ws"
    doubleQuotedScalar "\"hello \t \n world\"" "hello world"
  -- Single-quoted equivalent
  expectContent "sq trailing spaces"
    singleQuotedScalar "'hello   \n world'" "hello world"

/-! ## Bug D: Tab handling on continuation lines

`skipSpaces` only handled `' '` (space), not `'\t'` (tab).
Tabs on continuation lines leaked into output. Now uses
`skipHWhitespace` which handles both spaces and tabs.
-/

def testBugD_TabsOnContinuation : IO Unit := do
  IO.println "--- Bug D: Tab handling on continuation lines ---"
  -- "hello\n\tworld" → "hello world"  (tab on continuation = leading ws)
  expectContent "dq tab continuation"
    doubleQuotedScalar "\"hello\n\tworld\"" "hello world"
  -- "hello\n\t world" → "hello world"  (tab+space on continuation)
  expectContent "dq tab+space continuation"
    doubleQuotedScalar "\"hello\n\t world\"" "hello world"
  -- "a\n\n\tb" → "a\nb"  (tab on continuation after blank line)
  expectContent "dq tab after blank"
    doubleQuotedScalar "\"a\n\n\tb\"" "a\nb"
  -- Single-quoted equivalent
  expectContent "sq tab continuation"
    singleQuotedScalar "'hello\n\tworld'" "hello world"

/-! ## Bug E: Escaped line breaks (line continuation)

In double-quoted scalars, `\` + newline is an escaped line break
(YAML §5.7 [112]). It means "continue the string on the next line"
— the backslash, newline, and leading whitespace on the next line
are all consumed, emitting nothing to the output. Trailing whitespace
before the backslash is also trimmed.
-/

def testBugE_EscapedLineBreak : IO Unit := do
  IO.println "--- Bug E: Escaped line breaks (line continuation) ---"
  -- "hello \\\n  world" → "helloworld"  (line continuation)
  -- The \ is preceded by no trailing ws to trim (the space before \
  -- is before the backslash, which was already consumed by anyToken;
  -- the acc at escape point is "hello " but trimTrailingWs removes
  -- trailing spaces before the escape consumes the newline)
  -- Actually, per YAML §5.7 [112]: "an escaped line break followed
  -- by whitespace" — the backslash consumes trailing ws from acc.
  expectContent "dq escaped newline"
    doubleQuotedScalar "\"hello \\\n  world\"" "helloworld"
  -- "foo\\\nbar" → "foobar"  (no trailing ws, no leading ws)
  expectContent "dq escaped bare"
    doubleQuotedScalar "\"foo\\\nbar\"" "foobar"
  -- "foo \\\n  bar" → "foobar"
  -- Per YAML spec §5.7: escaped line break trims trailing ws from acc,
  -- consumes newline + leading ws — emits nothing.
  expectContent "dq escaped with trailing"
    doubleQuotedScalar "\"foo \\\n  bar\"" "foobar"
  -- "a\\\n\\\nb" → "ab"  (two consecutive escaped line breaks)
  expectContent "dq double escaped"
    doubleQuotedScalar "\"a\\\n\\\nb\"" "ab"

/-! ## Combined: Fold + trim + tabs together

These test multiple fixes working together, matching the YAML test
suite cases that originally failed (4CQQ, 4ZYM, 5GBF, etc.).
-/

def testCombinedFolding : IO Unit := do
  IO.println "--- Combined folding tests ---"
  -- Multi-line double quoted with fold + trim + continuation whitespace
  -- " foo \n bar \n baz " → " foo bar baz "
  -- Leading ws on the opening line is content (part of the scalar).
  -- Trailing ws before each fold IS trimmed. Leading ws on continuation
  -- lines is consumed by foldQuotedNewlines. But leading/trailing content
  -- within quotes on the first/last lines is preserved.
  expectContent "dq multi-line fold"
    doubleQuotedScalar "\" foo \n bar \n baz \"" " foo bar baz "
  -- Fold then blank line
  -- "a \n\n b" → "a\nb"  (trailing ws trimmed, blank = preserved newline)
  expectContent "dq fold then blank"
    doubleQuotedScalar "\"a \n\n b\"" "a\nb"
  -- Blank line then fold
  -- "a\n\nb\n c" → "a\nb c"  (blank preserved, then fold to space)
  expectContent "dq blank then fold"
    doubleQuotedScalar "\"a\n\nb\n c\"" "a\nb c"
  -- Multiple folds in sequence
  -- "a\nb\nc" → "a b c"
  expectContent "dq triple fold"
    doubleQuotedScalar "\"a\nb\nc\"" "a b c"

/-! ## CRLF handling

Ensure line folding works with CRLF (`\r\n`) line endings
in addition to LF (`\n`).
-/

def testCRLFFolding : IO Unit := do
  IO.println "--- CRLF folding ---"
  -- "hello\r\n world" → "hello world"
  expectContent "dq CRLF fold"
    doubleQuotedScalar "\"hello\r\n world\"" "hello world"
  -- "a\r\n\r\nb" → "a\nb"  (CRLF blank line)
  expectContent "dq CRLF blank"
    doubleQuotedScalar "\"a\r\n\r\nb\"" "a\nb"
  -- Single-quoted CRLF
  expectContent "sq CRLF fold"
    singleQuotedScalar "'hello\r\n world'" "hello world"

/-! ## Edge cases -/

def testEdgeCases : IO Unit := do
  IO.println "--- Edge cases ---"
  -- No folding: single-line scalars unchanged
  expectContent "dq no fold"
    doubleQuotedScalar "\"hello world\"" "hello world"
  expectContent "sq no fold"
    singleQuotedScalar "'hello world'" "hello world"
  -- Empty quoted scalars
  expectContent "dq empty"
    doubleQuotedScalar "\"\"" ""
  expectContent "sq empty"
    singleQuotedScalar "''" ""
  -- Fold at end: "hello\n " → "hello "
  -- (trailing fold produces trailing space)
  expectContent "dq fold at end"
    doubleQuotedScalar "\"hello\n \"" "hello "
  -- Only whitespace on continuation line after fold
  -- "a\n   \nb" → "a\nb"  (whitespace-only line = blank line)
  expectContent "dq ws-only blank"
    doubleQuotedScalar "\"a\n   \nb\"" "a\nb"

/-! ## Test runner -/

def runTests : IO Unit := do
  IO.println "=== Quoted Scalar Folding Tests ===\n"
  testBugA_SimpleFold
  IO.println ""
  testBugB_EmptyLines
  IO.println ""
  testBugC_TrailingWsTrim
  IO.println ""
  testBugD_TabsOnContinuation
  IO.println ""
  testBugE_EscapedLineBreak
  IO.println ""
  testCombinedFolding
  IO.println ""
  testCRLFFolding
  IO.println ""
  testEdgeCases
  IO.println ""
  IO.println "=== Done ==="

end Tests.QuotedFolding

def main : IO Unit := Tests.QuotedFolding.runTests
