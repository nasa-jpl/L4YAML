import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document
import Tests.VerifiedResult

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

Produces a `VerifiedSuiteResult` for structured reporting.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser
open Tests

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

/-- Check that a parser produces a specific scalar content string. -/
def expectContent (state : IO.Ref TestCollector) (label : String)
    (p : YamlParser YamlValue) (input : String) (expected : String) : IO Unit := do
  match getContent (runParser p input) with
  | .ok content =>
    if content == expected then check state label true
    else check state label false (message := s!"expected {repr expected}, got {repr content}")
  | .error e => check state label false (message := s!"parse error: {e}")

/-- Check that a parser fails on the given input. -/
def expectFailure (state : IO.Ref TestCollector) (label : String)
    (p : YamlParser YamlValue) (input : String) : IO Unit := do
  match runParser p input with
  | .ok v => check state label false (message := s!"expected failure, got {repr v}")
  | .error _ => check state label true

/-! ## Bug A: Simple fold (single newline → space)

`foldQuotedNewlines` previously required a mandatory `newline` after
`skipHWhitespace`, crashing on the simplest fold case where the next
line has content (not a blank line).

YAML spec §6.5: A line break followed by content on the next line
folds to a single space.
-/

def testBugA_SimpleFold (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Bug A: Simple fold (newline → space)"
  expectContent state "dq basic fold"
    doubleQuotedScalar "\"hello\n world\"" "hello world"
  expectContent state "dq no leading ws"
    doubleQuotedScalar "\"foo\nbar\"" "foo bar"
  expectContent state "sq basic fold"
    singleQuotedScalar "'hello\n world'" "hello world"
  expectContent state "sq no leading ws"
    singleQuotedScalar "'foo\nbar'" "foo bar"

/-! ## Bug B: Empty line counting (preserved newlines)

The off-by-one meant blank lines inside quoted scalars produced the
wrong number of newlines. YAML §6.5: empty lines (a line break
followed by another line break) are preserved as literal newlines.
One empty line = one `\n`, two empty lines = two `\n`s, etc.
-/

def testBugB_EmptyLines (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Bug B: Empty line counting (preserved newlines)"
  expectContent state "dq one empty line"
    doubleQuotedScalar "\"a\n\nb\"" "a\nb"
  expectContent state "dq two empty lines"
    doubleQuotedScalar "\"a\n\n\nb\"" "a\n\nb"
  expectContent state "dq three empty lines"
    doubleQuotedScalar "\"a\n\n\n\nb\"" "a\n\n\nb"
  expectContent state "sq one empty line"
    singleQuotedScalar "'a\n\nb'" "a\nb"
  expectContent state "sq two empty lines"
    singleQuotedScalar "'a\n\n\nb'" "a\n\nb"

/-! ## Bug C: Trailing whitespace trimming

YAML §7.3.1: "All leading and trailing white space characters on each
line are excluded from the content." Before folding, trailing spaces
and tabs on the line before the break must be trimmed.
-/

def testBugC_TrailingWsTrim (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Bug C: Trailing whitespace trimming"
  expectContent state "dq trailing spaces"
    doubleQuotedScalar "\"hello   \n world\"" "hello world"
  expectContent state "dq trailing tab"
    doubleQuotedScalar "\"hello\t\n world\"" "hello world"
  expectContent state "dq trailing mixed ws"
    doubleQuotedScalar "\"hello \t \n world\"" "hello world"
  expectContent state "sq trailing spaces"
    singleQuotedScalar "'hello   \n world'" "hello world"

/-! ## Bug D: Tab handling on continuation lines

`skipSpaces` only handled `' '` (space), not `'\t'` (tab).
Tabs on continuation lines leaked into output. Now uses
`skipHWhitespace` which handles both spaces and tabs.
-/

def testBugD_TabsOnContinuation (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Bug D: Tab handling on continuation lines"
  expectContent state "dq tab continuation"
    doubleQuotedScalar "\"hello\n\tworld\"" "hello world"
  expectContent state "dq tab+space continuation"
    doubleQuotedScalar "\"hello\n\t world\"" "hello world"
  expectContent state "dq tab after blank"
    doubleQuotedScalar "\"a\n\n\tb\"" "a\nb"
  expectContent state "sq tab continuation"
    singleQuotedScalar "'hello\n\tworld'" "hello world"

/-! ## Bug E: Escaped line breaks (line continuation)

In double-quoted scalars, `\` + newline is an escaped line break
(YAML §5.7 [112]). It means "continue the string on the next line"
— the backslash, newline, and leading whitespace on the next line
are all consumed, emitting nothing to the output. Trailing whitespace
before the backslash is also trimmed.
-/

def testBugE_EscapedLineBreak (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Bug E: Escaped line breaks (line continuation)"
  -- "hello \\\n  world" → "helloworld"  (line continuation)
  -- The \ is preceded by no trailing ws to trim (the space before \
  -- is before the backslash, which was already consumed by anyToken;
  -- the acc at escape point is "hello " but trimTrailingWs removes
  -- trailing spaces before the escape consumes the newline)
  -- Actually, per YAML §5.7 [112]: "an escaped line break followed
  -- by whitespace" — the backslash consumes trailing ws from acc.
  expectContent state "dq escaped newline"
    doubleQuotedScalar "\"hello \\\n  world\"" "helloworld"
  expectContent state "dq escaped bare"
    doubleQuotedScalar "\"foo\\\nbar\"" "foobar"
  expectContent state "dq escaped with trailing"
    doubleQuotedScalar "\"foo \\\n  bar\"" "foobar"
  expectContent state "dq double escaped"
    doubleQuotedScalar "\"a\\\n\\\nb\"" "ab"

/-! ## Combined: Fold + trim + tabs together

These test multiple fixes working together, matching the YAML test
suite cases that originally failed (4CQQ, 4ZYM, 5GBF, etc.).
-/

def testCombinedFolding (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Combined folding tests"
  -- Multi-line double quoted with fold + trim + continuation whitespace
  -- " foo \n bar \n baz " → " foo bar baz "
  -- Leading ws on the opening line is content (part of the scalar).
  -- Trailing ws before each fold IS trimmed. Leading ws on continuation
  -- lines is consumed by foldQuotedNewlines. But leading/trailing content
  -- within quotes on the first/last lines is preserved.
  expectContent state "dq multi-line fold"
    doubleQuotedScalar "\" foo \n bar \n baz \"" " foo bar baz "
  expectContent state "dq fold then blank"
    doubleQuotedScalar "\"a \n\n b\"" "a\nb"
  expectContent state "dq blank then fold"
    doubleQuotedScalar "\"a\n\nb\n c\"" "a\nb c"
  expectContent state "dq triple fold"
    doubleQuotedScalar "\"a\nb\nc\"" "a b c"

/-! ## CRLF handling

Ensure line folding works with CRLF (`\r\n`) line endings
in addition to LF (`\n`).
-/

def testCRLFFolding (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "CRLF folding"
  expectContent state "dq CRLF fold"
    doubleQuotedScalar "\"hello\r\n world\"" "hello world"
  expectContent state "dq CRLF blank"
    doubleQuotedScalar "\"a\r\n\r\nb\"" "a\nb"
  expectContent state "sq CRLF fold"
    singleQuotedScalar "'hello\r\n world'" "hello world"

/-! ## Edge cases -/

def testEdgeCases (state : IO.Ref TestCollector) : IO Unit := do
  setCategory state "Edge cases"
  expectContent state "dq no fold"
    doubleQuotedScalar "\"hello world\"" "hello world"
  expectContent state "sq no fold"
    singleQuotedScalar "'hello world'" "hello world"
  expectContent state "dq empty"
    doubleQuotedScalar "\"\"" ""
  expectContent state "sq empty"
    singleQuotedScalar "''" ""
  expectContent state "dq fold at end"
    doubleQuotedScalar "\"hello\n \"" "hello "
  expectContent state "dq ws-only blank"
    doubleQuotedScalar "\"a\n   \nb\"" "a\nb"

/-- Collect all quoted folding test results as structured data. -/
def collectTests : IO VerifiedSuiteResult := do
  let state ← IO.mkRef ({} : TestCollector)
  testBugA_SimpleFold state
  testBugB_EmptyLines state
  testBugC_TrailingWsTrim state
  testBugD_TabsOnContinuation state
  testBugE_EscapedLineBreak state
  testCombinedFolding state
  testCRLFFolding state
  testEdgeCases state
  let results ← finish state
  return { name := "quotedfolding", label := "Quoted Folding Tests", sourceFile := "Tests/QuotedFolding.lean", tests := results }

end Tests.QuotedFolding
