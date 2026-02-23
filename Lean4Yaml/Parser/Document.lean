/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.YamlSpec

/-!
# YAML Document Parsers

Parsers for YAML documents and multi-document streams.

**YAML 1.2.2**: [197]-[205] (§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)
- [197] c-directives-end (`---`)
- [198] c-document-end (`...`)
- [199]-[200] l-document-prefix / c-forbidden
- [201] l-bare-document / [202] l-explicit-document / [203] l-directive-document
- [204] l-any-document / [205] l-yaml-stream

## Structure

A YAML stream consists of:
1. Optional BOM (byte order mark)
2. Zero or more documents, each preceded by optional directives

Documents can be:
- **Bare documents**: no explicit markers
- **Explicit documents**: preceded by `---` and optionally ended by `...`

## Directives

YAML 1.2.2 §6.8 (https://yaml.org/spec/1.2.2/#68-directives)
–§6.9 (https://yaml.org/spec/1.2.2/#69-node-tags):
- `%YAML 1.2` — version directive
- `%TAG !handle! prefix` — tag shorthand directive
-/

namespace Lean4Yaml.Parse

open Parser
open Parser.Char
open Lean4Yaml

-- Bridge instance: help Lean reduce Parser.Stream.Position YamlStream to YamlPos
instance : Repr (Parser.Stream.Position YamlStream) := inferInstanceAs (Repr YamlPos)

instance : Inhabited YamlDocument := ⟨{ value := .null, directives := #[] }⟩

/--
Result of attempting to parse one document from the stream.

This makes the document parser's contract explicit — the caller can
distinguish "parsed content" from "nothing left" from "input present
but not parseable" without comparing stream positions externally.

Follows the same explicit-result-type pattern as `DispatchResult`
(three-valued dispatch) and `ContinuationCheck` (scalar continuation).
-/
inductive DocumentResult where
  /-- Successfully parsed a document. Invariant: consumed input.
      `hadDocEnd` indicates whether a `...` document end marker was consumed. -/
  | parsed (doc : YamlDocument) (hadDocEnd : Bool := false)
  /-- No remaining input after blank lines. Stream is complete. -/
  | endOfStream
  /-- Non-blank input remains but could not be parsed as a document.
      Carries the position where parsing stalled for error reporting. -/
  | stalled (pos : YamlPos)
  deriving Repr

/-! ## Byte Order Mark -/

/--
Skip an optional BOM (byte order mark) at the start of input.

**YAML 1.2.2**: [3] c-byte-order-mark (§5.2, https://yaml.org/spec/1.2.2/#52-character-encodings)

The BOM (U+FEFF) is allowed at the start of a stream.
-/
@[yaml_spec "5.2" 3 "c-byte-order-mark"]
def skipBOM : YamlParser Unit := do
  let _ ← option? (token '\uFEFF')

/-! ## Directives
  **YAML 1.2.2**: [82] l-directive (§6.8, https://yaml.org/spec/1.2.2/#68-directives)
  - [83] ns-yaml-directive / [84] ns-yaml-version
  - [85] ns-tag-directive / [86]-[88] tag handles -/

/--
Parse a YAML directive.

**YAML 1.2.2**: [82] l-directive (§6.8)
- [83] ns-yaml-directive: `%YAML 1.2`
- [85] ns-tag-directive: `%TAG !handle! prefix`
- [81] ns-reserved-directive: unknown directives

Directives start with `%` and end at the next line break.
-/
@[yaml_spec "6.8" 82 "l-directive"]
def directive : YamlParser Directive :=
  withErrorMessage "expected directive" do
    let _ ← char '%'
    let name ← takeMany1 (tokenFilter fun c => !isWhiteSpace c && !isLineBreak c)
      let nameStr := String.ofList name.toList
    match nameStr with
    | "YAML" =>
      skipHWhitespace
      let version ← takeMany1 (tokenFilter fun c => !isWhiteSpace c && !isLineBreak c)
      let versionStr := String.ofList version.toList
      -- P7 fix (MUS6): §6.7 — `#` embedded in version string means the `#`
      -- was not preceded by whitespace.  `%YAML 1.1#...` gives version
      -- `1.1#...` (takeMany1 consumes `#` since it's not whitespace/linebreak).
      if versionStr.any (· == '#') then
        setValidationError "invalid '#' in %YAML version (§6.7)"
      -- NOTE: H7TQ wants `%YAML 1.2 foo` to fail, but ZYU8 wants
      -- `%YAML 1.1 1.2` to pass.  These conflict — leave as-is.
      -- Consume rest of directive line: any extra parameters/content after the
      -- version are silently consumed (ns-reserved-directive semantics).
      -- This prevents leftover content from blocking `---` detection.
      skipTrailing
      dropMany (tokenFilter (fun c => !isLineBreak c))
      let _ ← option? newline
      return .yaml versionStr
    | "TAG" =>
      skipHWhitespace
      let handle ← takeMany1 (tokenFilter fun c => !isWhiteSpace c && !isLineBreak c)
      skipHWhitespace
      let tagPrefix ← takeMany1 (tokenFilter fun c => !isWhiteSpace c && !isLineBreak c)
      skipTrailing
      let _ ← option? newline
      return .tag (String.ofList handle.toList) (String.ofList tagPrefix.toList)
    | _ =>
      -- Unknown/reserved directive: skip entire line to end of line.
      -- P7 fix: consume all parameters, not just whitespace+comment,
      -- so that `%YAM 1.1\n---` doesn't leave `1.1\n` in the stream.
      skipTrailing
      dropMany (tokenFilter (fun c => !isLineBreak c))
      let _ ← option? newline
      -- Unknown directives are ignored per spec
      return .yaml "unknown"

/--
Parse all directives before a document.
-/
def directives : YamlParser (Array Directive) := do
  let fuel := Stream.remaining (← getStream)
  let mut dirs := #[]
  for _ in [:fuel] do
    skipBlankLines
    match ← option? (lookAhead (char '%')) with
    | some _ =>
      let dir ← directive
      dirs := dirs.push dir
    | none =>
      break
  -- P7 fix (SF5V): §6.8.1 — duplicate %YAML directives are forbidden.
  let yamlCount := dirs.filter (fun d => match d with | .yaml _ => true | .tag _ _ => false) |>.size
  if yamlCount > 1 then
    setValidationError "duplicate %YAML directive"
  return dirs

/-! ## Document Structure
  **YAML 1.2.2**: [197]-[205] (§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions) -/

/--
Parse the document start marker `---`.

**YAML 1.2.2**: [197] c-directives-end (§9.1.2)

The marker must be followed by whitespace, a newline, or EOF.
Returns `true` if the marker was found.
-/
@[yaml_spec "9" 197 "-", yaml_spec "9.1.2" 197 "c-directives-end"]
def documentStartMarker : YamlParser Unit :=
  withErrorMessage "expected '---'" do
    let _ ← chars "---"
    -- Must be followed by whitespace, newline, or EOF
    match ← option? (lookAhead anyToken) with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c && c != '#' then
        -- `---xxx` is not a valid document start marker.
        -- Record validation error; the `---` is already consumed.
        setValidationError
          s!"'---' must be followed by whitespace or newline, got '{c}'"
    | none => pure ()  -- EOF is fine
    skipTrailing
    let _ ← option? newline

/--
Parse the document end marker `...`.

**YAML 1.2.2**: [198] c-document-end (§9.1.3)

The marker must be followed by whitespace, a newline, or EOF.
P5 fix: also validate that no non-whitespace/non-comment content
remains on the line after `...` (catches `... invalid` in 3HFZ).
-/
@[yaml_spec "9.1.3" 198 "c-document-end"]
def documentEndMarker : YamlParser Unit :=
  withErrorMessage "expected '...'" do
    let _ ← chars "..."
    match ← option? (lookAhead anyToken) with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c && c != '#' then
        setValidationError
          s!"'...' must be followed by whitespace or newline, got '{c}'"
    | none => pure ()
    skipTrailing
    -- P5 fix: after consuming whitespace/comment, verify no content remains
    -- on the same line.  `... invalid` leaves `invalid` here.
    match ← option? (lookAhead anyToken) with
    | some c =>
      if !isLineBreak c then
        setValidationError
          s!"invalid trailing content '{c}' after document end marker"
    | none => pure ()
    let _ ← option? newline

/--
Parse a single YAML document, returning a `DocumentResult`.

**YAML 1.2.2**: [204] l-any-document (§9.2)
- [201] l-bare-document: no markers
- [202] l-explicit-document: preceded by `---`
- [203] l-directive-document: preceded by directives + `---`

A document can be:
1. An explicit document (preceded by `---`)
2. A bare document (no preceding markers)

Returns:
- `DocumentResult.parsed doc` — successfully parsed, consumed input
- `DocumentResult.endOfStream` — no remaining input after blank lines
- `DocumentResult.stalled pos` — input present but could not be parsed

The `stalled` result eliminates the need for callers to compare stream
positions before/after the call. The document parser itself knows whether
it consumed content, and communicates this through the result type.
-/
@[yaml_spec "9.2" 204 "l-any-document"]
def document (prevHadDocEnd : Bool := true) : YamlParser DocumentResult := do
  -- Reset anchor map for this document scope (§3.2.2.2).
  -- Anchors from a previous document must not leak into the next one.
  resetAnchorMap
  skipBlankLines
  -- Check for end of stream before attempting anything
  let atEnd ← test endOfInput
  if atEnd then return .endOfStream
  -- Record position before content parsing begins.
  -- This is used to detect whether blockValue consumed any input,
  -- converting the implicit "no progress" state into an explicit result.
  let posBefore ← currentPos
  -- Parse optional directives
  let dirs ← directives
  skipBlankLines
  -- Check for explicit document start
  let docStartLine ← currentLine
  let hadExplicitStart ← do
    match ← option? documentStartMarker with
    | some _ => pure true
    | none => pure false
  -- P7 fix (9MMA, B63P, 9HCY): §6.8.1 — directives may only precede
  -- a document that begins with a document start marker `---`.
  -- If directives were parsed but no `---` follows, this is invalid.
  if dirs.size > 0 && !hadExplicitStart then
    setValidationError "directives must be followed by document start marker '---'"
  -- P10 fix (9HCY): §9.2 — directives (`%TAG`, `%YAML`) before a document
  -- require that the previous document ended with `...` (document end marker).
  -- Without `...`, the stream is still "inside" the previous bare document,
  -- so encountering a directive is invalid.
  if dirs.size > 0 && !prevHadDocEnd then
    setValidationError "directives require document end marker '...' before them"
  -- P10 fix (QLJ7): §6.8.2 — tag shorthand handles are scoped to the
  -- document where they are declared.  Build the handle registry from
  -- this document's %TAG directives + the always-available defaults.
  let mut handles := #["!", "!!"]  -- defaults: §6.8.2.2, §6.8.2.3
  for d in dirs do
    match d with
    | .tag handle _ => handles := handles.push handle
    | _ => pure ()
  setTagHandles handles
  skipBlankLines
  -- P7 pre-check (9KBC, CXX2): §9.1.2 — block collections cannot start
  -- on the same line as the document start marker `---`.
  -- `--- key: value` and `--- - item` are invalid; the block content must
  -- start on the next line.  Scalars and flow collections are fine inline.
  if hadExplicitStart then
    let contentLine ← currentLine
    if contentLine == docStartLine then
      -- Content is on the `---` line; check for block collections
      let isMK ← lookAhead (detectMappingKey (inFlow := false))
      if isMK then
        setValidationError "block mapping cannot start on the document start line"
      else
        let isSeqIndicator ← lookAhead do
          match ← option? (char '-') with
          | some _ =>
            match ← option? anyToken with
            | some c => return (isWhiteSpace c || isLineBreak c)
            | none => return true
          | none => return false
        if isSeqIndicator then
          setValidationError "block sequence cannot start on the document start line"
  -- Parse document content
  -- Check for immediate document end or empty document
  let atEnd' ← test endOfInput
  if atEnd' then
    return .parsed (hadDocEnd := false) { value := YamlValue.null, directives := dirs }
  let atDocEnd ← atDocumentEnd
  if atDocEnd then
    let _ ← option? documentEndMarker
    return .parsed (hadDocEnd := true) { value := YamlValue.null, directives := dirs }
  let bv ← blockValue 0
  let value := bv.getD .null
  let posAfter ← currentPos
  -- If no input was consumed, blockValue backtracked on an unrecognized
  -- construct (anchor, tag, explicit key, etc.) and returned null.
  -- Report this as stalled rather than returning a phantom document.
  if posAfter == posBefore then
    return .stalled posBefore
  -- Check for trailing non-whitespace content on the current line.
  -- After blockValue, the only valid continuations on the same line are:
  -- whitespace, comments (`#`), or end of line/input.
  -- Any other content indicates invalid trailing material (e.g., extra `]`,
  -- content after a flow collection, trailing text after a quoted scalar).
  -- This catches tests: 4H7K, 62EZ, KS4U, P2EQ, JY7Z, Q4CL, SU5Z.
  let trailCol ← currentCol
  skipHWhitespace
  let afterTrailCol ← currentCol
  match ← option? (lookAhead anyToken) with
  | some c =>
    -- §6.7: `#` is only a comment if preceded by whitespace.
    -- If no horizontal whitespace was consumed before `#`, it is NOT
    -- a valid comment start — it's invalid trailing content.
    let isValidComment := c == '#' && (afterTrailCol != trailCol || afterTrailCol == 0)
    if !isLineBreak c && !isValidComment then
      -- Check if it's a document end/start marker (which is valid)
      let isDocMarker ← lookAhead do
        match ← option? (chars "---" <|> chars "...") with
        | some _ =>
          match ← option? anyToken with
          | some c' => pure (isWhiteSpace c' || isLineBreak c')
          | none => pure true
        | none => pure false
      if !isDocMarker then
        setValidationError
          s!"unexpected trailing content '{c}' after document value"
  | none => pure ()  -- EOF is fine
  -- Check for validation errors detected during this document.
  -- The error survives backtracking and is returned at the top level.
  let valErr ← getValidationError
  if valErr.isSome then
    return .stalled posBefore
  skipBlankLines
  -- Optionally consume document end marker.
  -- P5 fix: track whether `...` was consumed — after a document end marker,
  -- bare content is valid (§9.2 `l-document-suffix+ l-any-document?`).
  let hadDocEnd ← match ← option? documentEndMarker with
    | some _ => pure true
    | none => pure false

  -- §9.1.4/§9.2: After a document WITHOUT a document end marker (`...`),
  -- subsequent content must begin with `---` or `...`.
  -- Bare content (not preceded by a document marker) is invalid.
  -- This catches:
  --   KS4U: `---\n[\n...\n]\ninvalid item\n`
  --   BS4K: `word1  # comment\nword2` (two consecutive bare documents)
  -- With `...`, bare documents are allowed per §9.2.
  if !hadDocEnd then do
    skipBlankLines
    let atEnd'' ← test endOfInput
    if !atEnd'' then do
      let atNextDoc ← lookAhead do
        match ← option? (chars "---" <|> chars "...") with
        | some _ =>
          match ← option? anyToken with
          | some c' => pure (isWhiteSpace c' || isLineBreak c')
          | none => pure true
        | none => pure false
      if !atNextDoc then do
        let c ← option? (lookAhead anyToken)
        let ch := match c with | some ch => s!"{ch}" | none => "EOF"
        setValidationError
          s!"unexpected content '{ch}' after explicit document; expected '---' or '...'"
        return .stalled posBefore
  let anchors ← getAnchorMap
  return .parsed (hadDocEnd := hadDocEnd) { value, directives := dirs, anchors }

/--
Parse a YAML stream: zero or more documents.

**YAML 1.2.2**: [205] l-yaml-stream (§9.2, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions)
- [199] l-document-prefix
- [204] l-any-document

A YAML stream consists of zero or more documents.

Uses `DocumentResult` to distinguish successful parse from end-of-stream
from stalled input, without needing external position comparison.
-/
@[yaml_spec "9.2" 205 "l-yaml-stream"]
def yamlStream : YamlParser (Array YamlDocument) := do
  skipBOM
  let fuel := Stream.remaining (← getStream)
  let mut docs := #[]
  let mut prevDocEnd := true  -- first document doesn't need `...` before it
  for _ in [:fuel] do
    skipBlankLines
    match ← document (prevHadDocEnd := prevDocEnd) with
    | .parsed doc hadDocEnd =>
      docs := docs.push doc
      prevDocEnd := hadDocEnd
      skipBlankLines
    | .endOfStream =>
      break
    | .stalled pos =>
      -- Input present but not parseable as a document.
      -- Record validation error and stop the loop.
      let c ← option? anyToken
      let msg := match c with
        | some ch => s!"unhandled construct '{ch}' at line {pos.line}, column {pos.col}"
        | none => s!"stuck at line {pos.line}, column {pos.col}"
      setValidationError msg
      break
  return docs

/-! ## Top-Level Parse Functions -/

/-! ## Top-Level Parse Functions

YAML 1.2.2 §3.1 defines **Load** as the composition of two processes:
- **Parse**: character stream → serialization event tree
- **Compose**: serialization event tree → representation node graph

The *Raw* variants return the serialization tree (anchors + aliases preserved).
The standard variants apply Compose for backward compatibility.
-/

/--
Parse a YAML string into an array of documents (**serialization tree**).

Returns documents with `.alias name` nodes and `anchor` fields preserved.
This is the **Parse** step from YAML 1.2.2 §3.1.

Each `YamlDocument` includes an `anchors` map that can be used by
`YamlDocument.compose` to resolve aliases.

**Post-condition**: returns `.ok docs` only if ALL of:
  1. The parser produced a valid document array.
  2. No validation error was recorded in the stream.
-/
def parseYamlRaw (input : String) : Except String (Array YamlDocument) :=
  let stream := YamlStream.ofString input
  match Parser.run yamlStream stream with
  | .ok stream' docs =>
    -- Check for validation errors that survived backtracking.
    match stream'.validationError with
    | some msg => .error msg
    | none => .ok docs
  | .error stream' err =>
    -- If both a parse error and a validation error exist,
    -- prefer the validation error (more specific).
    match stream'.validationError with
    | some msg => .error msg
    | none => .error (toString err)

/--
Parse a YAML string into an array of documents (**representation graph**).

This is the full **Load** step from YAML 1.2.2 §3.1:
Parse (→ serialization tree) + Compose (→ representation graph).

Aliases are resolved and anchor annotations are stripped.
This is the main entry point for most use cases.
-/
def parseYaml (input : String) : Except String (Array YamlDocument) :=
  match parseYamlRaw input with
  | .ok docs => .ok (docs.map YamlDocument.compose)
  | .error e => .error e

/--
Parse a YAML string expecting exactly one document (**serialization tree**).

Returns the raw document with `.alias` nodes and `anchor` fields preserved.
-/
def parseYamlSingleRaw (input : String) : Except String YamlDocument :=
  match parseYamlRaw input with
  | .ok docs =>
    if docs.size == 0 then .ok { value := YamlValue.null }
    else if docs.size == 1 then .ok docs[0]!
    else .error s!"expected single document, found {docs.size}"
  | .error e => .error e

/--
Parse a YAML string expecting exactly one document (**representation graph**).

Returns the value of the single document with aliases resolved and
anchor annotations stripped.
-/
def parseYamlSingle (input : String) : Except String YamlValue :=
  match parseYaml input with
  | .ok docs =>
    if docs.size == 0 then .ok YamlValue.null
    else if docs.size == 1 then .ok docs[0]!.value
    else .error s!"expected single document, found {docs.size}"
  | .error e => .error e

end Lean4Yaml.Parse
