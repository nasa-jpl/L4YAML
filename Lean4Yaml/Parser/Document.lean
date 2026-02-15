/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block

/-!
# YAML Document Parsers

Parsers for YAML documents and multi-document streams
(§9, https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions).

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

/-! ## Byte Order Mark -/

/--
Skip an optional BOM (byte order mark) at the start of input.

YAML 1.2.2 §5.2 (https://yaml.org/spec/1.2.2/#52-character-encodings):
The BOM (U+FEFF) is allowed at the start of a stream.
-/
def skipBOM : YamlParser Unit := do
  let _ ← option? (token '\uFEFF')

/-! ## Directives
  §6.8 (https://yaml.org/spec/1.2.2/#68-directives) -/

/--
Parse a YAML directive.

Directives start with `%` and end at the next line break.
-/
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
      skipTrailing
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
      -- Unknown directive: skip to end of line
      skipTrailing
      let _ ← option? newline
      -- Unknown directives are ignored per spec
      return .yaml "unknown"

/--
Parse all directives before a document.
-/
partial def directives : YamlParser (Array Directive) := do
  let mut dirs := #[]
  let mut continue' := true
  while continue' do
    skipBlankLines
    match ← option? (lookAhead (char '%')) with
    | some _ =>
      let dir ← directive
      dirs := dirs.push dir
    | none =>
      continue' := false
  return dirs

/-! ## Document Structure
  §9 (https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions) -/

/--
Parse the document start marker `---`.

The marker must be followed by whitespace, a newline, or EOF.
Returns `true` if the marker was found.
-/
def documentStartMarker : YamlParser Unit :=
  withErrorMessage "expected '---'" do
    let _ ← chars "---"
    -- Must be followed by whitespace, newline, or EOF
    match ← option? (lookAhead anyToken) with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c && c != '#' then
        Parser.throwUnexpectedWithMessage
          (msg := s!"'---' must be followed by whitespace or newline, got '{c}'")
    | none => pure ()  -- EOF is fine
    skipTrailing
    let _ ← option? newline

/--
Parse the document end marker `...`.

The marker must be followed by whitespace, a newline, or EOF.
-/
def documentEndMarker : YamlParser Unit :=
  withErrorMessage "expected '...'" do
    let _ ← chars "..."
    match ← option? (lookAhead anyToken) with
    | some c =>
      if !isWhiteSpace c && !isLineBreak c && c != '#' then
        Parser.throwUnexpectedWithMessage
          (msg := s!"'...' must be followed by whitespace or newline, got '{c}'")
    | none => pure ()
    skipTrailing
    let _ ← option? newline

/--
Parse a single YAML document.

A document can be:
1. An explicit document (preceded by `---`)
2. A bare document (no preceding markers)

The document content is a single block value.
-/
partial def document : YamlParser YamlDocument := do
  skipBlankLines
  -- Parse optional directives
  let dirs ← directives
  skipBlankLines
  -- Check for explicit document start
  let _ ← option? documentStartMarker
  skipBlankLines
  -- Parse document content
  -- Check for immediate document end or empty document
  let atEnd ← test endOfInput
  if atEnd then
    return { value := YamlValue.null, directives := dirs }
  let atDocEnd ← atDocumentEnd
  if atDocEnd then
    let _ ← option? documentEndMarker
    return { value := YamlValue.null, directives := dirs }
  let value ← blockValue 0
  skipBlankLines
  -- Optionally consume document end marker
  let _ ← option? documentEndMarker
  return { value, directives := dirs }

/--
Parse a YAML stream: zero or more documents.

YAML 1.2.2 §9 (https://yaml.org/spec/1.2.2/#chapter-9-document-stream-productions):
A YAML stream consists of zero or more documents.
-/
partial def yamlStream : YamlParser (Array YamlDocument) := do
  skipBOM
  let mut docs := #[]
  let mut continue' := true
  while continue' do
    skipBlankLines
    let atEnd ← test endOfInput
    if atEnd then
      continue' := false
    else
      let doc ← document
      docs := docs.push doc
      skipBlankLines
  return docs

/-! ## Top-Level Parse Functions -/

/--
Parse a YAML string into an array of documents.

This is the main entry point for the parser.
-/
def parseYaml (input : String) : Except String (Array YamlDocument) :=
  let stream := YamlStream.ofString input
  match Parser.run yamlStream stream with
  | .ok _ docs => .ok docs
  | .error _ err => .error (toString err)

/--
Parse a YAML string expecting exactly one document.

Returns the value of the single document, or an error if
there are zero or more than one documents.
-/
def parseYamlSingle (input : String) : Except String YamlValue :=
  match parseYaml input with
  | .ok docs =>
    if docs.size == 0 then .ok YamlValue.null
    else if docs.size == 1 then .ok docs[0]!.value
    else .error s!"expected single document, found {docs.size}"
  | .error e => .error e

end Lean4Yaml.Parse
