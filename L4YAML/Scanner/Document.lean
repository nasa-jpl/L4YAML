/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State
import L4YAML.Scanner.Whitespace
import L4YAML.Scanner.Indent

/-!
# Scanner — Document Boundaries and Directives

Document-start / document-end markers (`---`, `...`) and YAML directives
(`%YAML`, `%TAG`, reserved) — everything at §6.8 and §9.1.2 of the spec.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2.

## Scope

- Boundary detection: `atDocumentStart`, `atDocumentEnd`, `atDocumentBoundary`.
- Directive parsing helpers: `collectDirectiveNameLoop`,
  `collectVersionMajorLoop`, `collectVersionMinorLoop`,
  `collectTagHandleDirectiveLoop`, `collectTagPrefixLoop`.
- Directive scanners: `scanYamlDirective`, `scanTagDirective`, `scanDirective`.
- Marker scanners: `scanDocumentStart`, `scanDocumentEnd`,
  `skipDocEndWhitespace`.
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Document Boundary Detection -/

/-- Check if the scanner is at a document-start marker (`---`).

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[203] c-directives-end` = `"---"`

    The marker must be at column 0 and followed by a blank character or EOF.

    **Pre**: Any scanner position.
    **Post**: Pure predicate — scanner state unchanged. -/
@[yaml_spec "9.1.2" 203 "c-directives-end"]
def atDocumentStart (s : ScannerState) : Bool :=
  s.col == 0
  && s.peekAt? 0 == some '-'
  && s.peekAt? 1 == some '-'
  && s.peekAt? 2 == some '-'
  && match s.peekAt? 3 with
     | none => true
     | some c => isBlankBool c

/-- Check if the scanner is at a document-end marker (`...`).

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[204] c-document-end` = `"..."`

    The marker must be at column 0 and followed by a blank character or EOF.

    **Pre**: Any scanner position.
    **Post**: Pure predicate — scanner state unchanged. -/
@[yaml_spec "9.1.2" 204 "c-document-end"]
def atDocumentEnd (s : ScannerState) : Bool :=
  s.col == 0
  && s.peekAt? 0 == some '.'
  && s.peekAt? 1 == some '.'
  && s.peekAt? 2 == some '.'
  && match s.peekAt? 3 with
     | none => true
     | some c => isBlankBool c

/-- Check if the scanner is at any document boundary (`---` or `...`).

    **Implements** (YAML 1.2.2 §9.1.2): `[206] c-forbidden` detection.
    A document marker at column 0 followed by blank/EOF is forbidden
    inside block content. -/
@[yaml_spec "9.1.2" 206 "c-forbidden"]
def atDocumentBoundary (s : ScannerState) : Bool :=
  atDocumentStart s || atDocumentEnd s

/-! ## Directive Scanning -/

-- Helper: Collect directive name (non-whitespace, non-linebreak characters).
@[yaml_spec "6.8" 84 "ns-directive-name",
  yaml_spec "5.5" 34 "ns-char"]
def collectDirectiveNameLoop (s : ScannerState) (name : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (name, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isWhiteSpaceBool c && !isLineBreakBool c then
        collectDirectiveNameLoop s.advance (name.push c) fuel'
      else
        (name, s)
    | none => (name, s)

-- Helper: Collect version major digits until '.'.
@[yaml_spec "6.8.1" 87 "ns-yaml-version",
  yaml_spec "5.6" 35 "ns-dec-digit"]
def collectVersionMajorLoop (s : ScannerState) (major : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (major, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '.' => (major, s.advance)
    | some c =>
      if c.isDigit then
        collectVersionMajorLoop s.advance (major.push c) fuel'
      else
        (major, s)
    | none => (major, s)

-- Helper: Collect version minor digits.
@[yaml_spec "5.6" 35 "ns-dec-digit"]
def collectVersionMinorLoop (s : ScannerState) (minor : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (minor, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if c.isDigit then
        collectVersionMinorLoop s.advance (minor.push c) fuel'
      else
        (minor, s)
    | none => (minor, s)

-- Helper: Collect TAG directive handle: '!' delimiters + ns-word-char [38] per [89]-[92].
@[yaml_spec "6.8.2" 89 "c-tag-handle",
  yaml_spec "5.6" 38 "ns-word-char"]
def collectTagHandleDirectiveLoop (s : ScannerState) (handle : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (handle, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if isWordCharBool c || c == '!' then
        collectTagHandleDirectiveLoop s.advance (handle.push c) fuel'
      else
        (handle, s)
    | none => (handle, s)

-- Helper: Collect TAG directive prefix using ns-uri-char [39] per [93]-[95].
@[yaml_spec "6.8.2" 93 "ns-tag-prefix",
  yaml_spec "6.8.2" 94 "c-ns-local-tag-prefix",
  yaml_spec "6.8.2" 95 "ns-global-tag-prefix"]
def collectTagPrefixLoop (s : ScannerState) (pfx : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (pfx, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if isUriCharBool c then
        collectTagPrefixLoop s.advance (pfx.push c) fuel'
      else
        (pfx, s)
    | none => (pfx, s)

/-- Handle `%YAML` directive: parse version, validate trailing content, emit token.

    **Implements** (YAML 1.2.2 §6.8.1):
    - `[86]  ns-yaml-directive` = `"YAML" s-separate-in-line ns-yaml-version`
    - `[88]  ns-yaml-version`  = `ns-dec-digit+ "." ns-dec-digit+`

    **Pre**: `s` is state after `%YAML` + whitespace skip; `startPos` is position of `%`.
    **Post**: Emits `.versionDirective major minor`, sets `seenYamlDirective`.
    **Error**: `duplicateYamlDirective`, `directiveTrailingContent`. -/
@[yaml_spec "6.8.1" 86 "ns-yaml-directive", yaml_spec "6.8.1" 87 "ns-yaml-version"]
def scanYamlDirective (s : ScannerState) (s_after_ws : ScannerState) (startPos : YamlPos) :
    Except ScanError ScannerState := do
  if s.seenYamlDirective then
    throw (.duplicateYamlDirective s.line)
  let fuel_major := s.inputEnd - s_after_ws.offset
  let (major, s_after_dot) := collectVersionMajorLoop s_after_ws "" fuel_major
  let fuel_minor := s.inputEnd - s_after_dot.offset
  let (minor, s_after_version) := collectVersionMinorLoop s_after_dot "" fuel_minor
  let colBeforeWs := s_after_version.col
  let s_validated := skipWhitespace s_after_version
  match s_validated.peek? with
  | some '#' =>
    if s_validated.col == colBeforeWs then
      throw (.directiveTrailingContent s_validated.line s_validated.col)
  | some c => if !isLineBreakBool c then throw (.directiveTrailingContent s_validated.line s_validated.col)
  | none => pure ()
  let s_with_token := s_validated.emitAt startPos (.versionDirective major.toNat! minor.toNat!)
  .ok { s_with_token with seenYamlDirective := true, directivesPresent := true }

/-- Handle `%TAG` directive: parse handle and prefix, emit token.

    **Implements** (YAML 1.2.2 §6.8.2):
    - `[88]  ns-tag-directive` = `"TAG" s-separate-in-line c-tag-handle s-separate-in-line ns-tag-prefix`

    **Pre**: `s_after_ws` is state after `%TAG` + whitespace skip; `startPos` is position of `%`.
    **Post**: Emits `.tagDirective handle prefix`, sets `directivesPresent`.
    **Error**: `directiveTrailingContent` (non-comment content after prefix). -/
@[yaml_spec "6.8.2" 88 "ns-tag-directive",
  yaml_spec "6.8.2" 89 "c-tag-handle",
  yaml_spec "6.8.2" 93 "ns-tag-prefix"]
def scanTagDirective (s : ScannerState) (s_after_ws : ScannerState) (startPos : YamlPos) :
    Except ScanError ScannerState := do
  let fuel_handle := s.inputEnd - s_after_ws.offset
  let result := collectTagHandleDirectiveLoop s_after_ws "" fuel_handle
  let handle := result.1
  let s_after_handle := result.2
  let s_after_ws2 := skipWhitespace s_after_handle
  let fuel_prefix := s.inputEnd - s_after_ws2.offset
  let result2 := collectTagPrefixLoop s_after_ws2 "" fuel_prefix
  let tagPrefix := result2.1
  let s_after_prefix := result2.2
  -- Validate trailing content (match scanYamlDirective behavior)
  let colBeforeWs := s_after_prefix.col
  let s_validated := skipWhitespace s_after_prefix
  match s_validated.peek? with
  | some '#' =>
    if s_validated.col == colBeforeWs then
      throw (.directiveTrailingContent s_validated.line s_validated.col)
  | some c => if !isLineBreakBool c then throw (.directiveTrailingContent s_validated.line s_validated.col)
  | none => pure ()
  let s_with_token := s_validated.emitAt startPos (.tagDirective handle tagPrefix)
  .ok { s_with_token with directivesPresent := true }

/-- Scan a directive (`%YAML` or `%TAG`).

    **Implements** (YAML 1.2.2 §6.8):
    - `[82]  l-directive` = `"%" ( ns-yaml-directive | ns-tag-directive | ns-reserved-directive ) s-l-comments`
    - `[20]  c-directive` = `"%"`

    **Decomposed for provability**: YAML and TAG handling are in
    `scanYamlDirective` and `scanTagDirective` respectively, each with ≤ 6
    branch points. This wrapper has only 3 branch points.

    **Pre**: Scanner at `%` at column 0, `allowDirectives` is true.
    **Post**: Emits `.versionDirective major minor` or `.tagDirective handle prefix`.
    Sets `seenYamlDirective`, `directivesPresent` as appropriate.
    **Error**: `directiveAfterContent` (directive after document content without `...`),
    `duplicateYamlDirective` (second `%YAML` in same document),
    `directiveTrailingContent` (content after version string). -/
@[yaml_spec "6.8" 82 "l-directive",
  yaml_spec "6.8" 20 "c-directive",
  yaml_spec "6.8" 83 "ns-reserved-directive",
  yaml_spec "6.8" 85 "ns-directive-parameter"]
def scanDirective (s : ScannerState) : Except ScanError ScannerState :=
  if !s.allowDirectives then
    .error (.directiveAfterContent s.line)
  else
    let startPos := s.currentPos
    let s_after_percent := s.advance
    let fuel := s.inputEnd - s_after_percent.offset
    let (name, s_after_name) := collectDirectiveNameLoop s_after_percent "" fuel
    let s_after_ws := skipWhitespace s_after_name
    if name == "YAML" then
      match scanYamlDirective s s_after_ws startPos with
      | .ok s' => .ok (skipToEndOfLine s')
      | .error e => .error e
    else if name == "TAG" then
      match scanTagDirective s s_after_ws startPos with
      | .ok s' => .ok (skipToEndOfLine s')
      | .error e => .error e
    else
      .ok (skipToEndOfLine s_after_ws)

/-! ## Document Marker Scanning -/

/-- Scan a document-start marker `---`.

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[203] c-directives-end` = `"---"`

    **Pre**: Scanner at `---` at column 0.
    **Post**: Unwinds all indents (emits `blockEnd` tokens), emits `documentStart`,
    advances past `---`. Resets `allowDirectives := false`, `simpleKeyAllowed := true`,
    `documentEverStarted := true`. -/
@[yaml_spec "9.1.2" 203 "c-directives-end"]
def scanDocumentStart (s : ScannerState) : ScannerState :=
  let s_unwound := unwindIndents s (-1)
  let s_key_disabled := { s_unwound with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .documentStart
  let s_advanced := s_with_token.advanceN 3
  { s_advanced with
    simpleKeyAllowed := true
    allowDirectives := false
    seenYamlDirective := false
    directivesPresent := false
    documentEverStarted := true
    definedAnchors := #[] }

/-- Helper: skip whitespace (spaces + tabs) using structural recursion.
    Used by scanDocumentEnd for trailing content validation. -/
@[yaml_spec "6.2" 66 "s-separate-in-line"]
def skipDocEndWhitespace (s : ScannerState) (fuel : Nat) : ScannerState :=
  match fuel with
  | 0 => s
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if c == ' ' || c == '\t' then skipDocEndWhitespace s.advance fuel'
      else s
    | none => s

/-- Scan a document-end marker `...`.

    **Implements** (YAML 1.2.2 §9.1.2):
    - `[204] c-document-end` = `"..."`
    - `[205] l-document-suffix` = `c-document-end s-l-comments`

    **Pre**: Scanner at `...` at column 0.
    **Post**: Unwinds all indents, emits `documentEnd`, advances past `...`.
    Sets `allowDirectives := true` (re-enables directives for next document).
    **Error**: `directiveWithoutDocument` (if directives were present but no `---` followed),
    `trailingContentAfterDocEnd` (non-comment content on same line after `...`). -/
@[yaml_spec "9.1.2" 204 "c-document-end",
  yaml_spec "9.1.2" 205 "l-document-suffix"]
def scanDocumentEnd (s : ScannerState) : Except ScanError ScannerState := do
  -- §9.1.2: Document end marker `...` requires an open document.
  -- If directives were present but no `---` followed, the `...` cannot
  -- close a document that was never opened.
  if s.directivesPresent && !s.documentEverStarted then
    throw (.directiveWithoutDocument s.line)
  let s_unwound := unwindIndents s (-1)
  let s_key_disabled := { s_unwound with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .documentEnd
  let s_advanced := s_with_token.advanceN 3
  let result := { s_advanced with
    simpleKeyAllowed := true
    allowDirectives := true
    directivesPresent := false
    definedAnchors := #[] }
  -- §9.1.2: After `...`, only s-l-comments (whitespace + optional comment) allowed.
  -- Skip whitespace on the same line (structural recursion via skipDocEndWhitespace)
  let s'' := skipDocEndWhitespace result (s.inputEnd - result.offset + 1)
  -- After whitespace, must be comment (#), newline, or EOF
  match s''.peek? with
  | none => pure ()  -- EOF is fine
  | some '#' => pure ()  -- comment is fine
  | some c =>
    if isLineBreakBool c then pure ()  -- newline is fine
    else throw (.trailingContentAfterDocEnd s''.line s''.col)
  .ok result

end L4YAML.Scanner
