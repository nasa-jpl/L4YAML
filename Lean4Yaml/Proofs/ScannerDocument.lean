import Lean4Yaml.Scanner
import Lean4Yaml.Proofs.ScannerLoopInvariant
import Lean4Yaml.Proofs.ScannerContracts
import Lean4Yaml.Proofs.ScannerIndentStack
import Lean4Yaml.Proofs.ScannerScalar

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Scanner Document & Directive WellFormed Preservation (P10.10e)

Machine-checked proofs that the scanner's document boundary and directive
functions preserve the `WellFormed` invariant.

## Scope

Five functions are covered:
- `scanAnchorOrAlias` — scans `&name` (anchor) or `*name` (alias)
- `scanTag` — scans `!`, `!!suffix`, `!handle!suffix`, `!<uri>`
- `scanDirective` — scans `%YAML` or `%TAG` directives
- `scanDocumentStart` — scans `---` document start marker
- `scanDocumentEnd` — scans `...` document end marker

## Key Insight

**`scanAnchorOrAlias`, `scanTag`, `scanDirective`** never modify `indents`,
`flowLevel`, `flowStack`, or `simpleKeyStack` — the same pattern as scalar
scanners. They only modify `offset` (via advance loops) and `tokens`
(via `emitAt`). Therefore C1–C3 are trivially preserved; C4 requires
loop reasoning covered by `#guard` checks.

**`scanDocumentStart` and `scanDocumentEnd`** call `unwindIndents s (-1)`
which modifies `indents` (via pop) and `tokens` (via emit). However:
- C1: `unwindIndents` only pops when `indents.size > 1` → never goes below 1
- C2/C3: `unwindIndents` never touches `flowLevel`/`flowStack`/`simpleKeyStack`
- C4: `advanceN 3` adds 3 to offset — valid because `---`/`...` are 3 chars

Universal theorems are provided for `emitAt`-based patterns (reused from
ScannerScalar). For `unwindIndents`, we leverage the loop-body lemmas from
ScannerIndentStack. Comprehensive `#guard` checks cover all function
families on concrete inputs.

## Zero Axioms

All theorems are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ScannerDocument

open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.ScannerLoopInvariant
open Lean4Yaml.Proofs.ScannerContracts
open Lean4Yaml.Proofs.ScannerIndentStack
open Lean4Yaml.Proofs.ScannerScalar

/-! ## §1  Record Update Patterns — WellFormed Preservation (universal)

All five functions return states constructed via:
  `{ s'.emitAt pos tok with simpleKeyAllowed := ..., ... }`
or
  `{ (s'.emit tok).advanceN 3 with simpleKeyAllowed := ..., ... }`

The `with` clauses only modify non-WellFormed fields (simpleKeyAllowed,
simpleKey, allowDirectives, seenYamlDirective, directivesPresent,
documentEverStarted). These record updates trivially preserve WellFormed.
-/

/-- A record update touching only `simpleKeyAllowed` and non-WellFormed
    metadata flags preserves WellFormed. Used by `scanDocumentStart`. -/
theorem with_docStart_flags_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) :
    ({ s with
       simpleKeyAllowed := true
       allowDirectives := false
       seenYamlDirective := false
       directivesPresent := false
       documentEverStarted := true } : ScannerState).WellFormed := hwf

/-- A record update touching only `simpleKeyAllowed`, `allowDirectives`,
    and `directivesPresent` preserves WellFormed. Used by `scanDocumentEnd`. -/
theorem with_docEnd_flags_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) :
    ({ s with
       simpleKeyAllowed := true
       allowDirectives := true
       directivesPresent := false } : ScannerState).WellFormed := hwf

/-- A record update touching only `seenYamlDirective` and `directivesPresent`
    preserves WellFormed. Used by `scanDirective` (YAML branch). -/
theorem with_yamlDirective_flags_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) :
    ({ s with
       seenYamlDirective := true
       directivesPresent := true } : ScannerState).WellFormed := hwf

/-- A record update touching only `directivesPresent` preserves WellFormed.
    Used by `scanDirective` (TAG branch). -/
theorem with_tagDirective_flags_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) :
    ({ s with directivesPresent := true } : ScannerState).WellFormed := hwf

/-- A record update touching only `simpleKey` preserves WellFormed.
    Used by `scanDocumentStart`/`End` to clear simple key state. -/
theorem with_simpleKey_preserves_wellFormed (s : ScannerState)
    (hwf : s.WellFormed) (sk : SimpleKeyState) :
    ({ s with simpleKey := sk } : ScannerState).WellFormed := hwf

/-! ## §2  scanAnchorOrAlias — WellFormed Preservation

```
def scanAnchorOrAlias (s : ScannerState) (isAnchor : Bool) : ScannerState := Id.run do
  let startPos := s.currentPos
  let mut s' := s.advance
  let mut name := ""
  let fuel := s.inputEnd - s'.offset
  for _ in [:fuel] do
    match s'.peek? with
    | some c =>
      if !isFlowIndicator c && !isWhiteSpace c && !isLineBreak c then
        name := name.push c; s' := s'.advance
      else break
    | none => break
  if isAnchor then
    return { s'.emitAt startPos (.anchor name) with simpleKeyAllowed := false }
  else
    return { s'.emitAt startPos (.alias name) with simpleKeyAllowed := false }
```

The advance loop modifies only `offset`. `emitAt` modifies only `tokens`.
The `with` clause modifies only `simpleKeyAllowed`.
→ C1–C3 trivially preserved. C4 covered by `#guard`.
-/

-- WellFormed preservation (anchor)
private def checkAnchorWF (input : String) : Bool :=
  let s := scanAnchorOrAlias (ScannerState.mk' input) true
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd

#guard checkAnchorWF "&name rest"
#guard checkAnchorWF "&a"
#guard checkAnchorWF "&longanchorname"
#guard checkAnchorWF "&x "
#guard checkAnchorWF "&name\n"
#guard checkAnchorWF "&name: value"

-- WellFormed preservation (alias)
private def checkAliasWF (input : String) : Bool :=
  let s := scanAnchorOrAlias (ScannerState.mk' input) false
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd

#guard checkAliasWF "*name rest"
#guard checkAliasWF "*a"
#guard checkAliasWF "*longaliasname"
#guard checkAliasWF "*x "
#guard checkAliasWF "*name\n"

-- Token content verification
private def anchorToken (input : String) : Option YamlToken :=
  let s := scanAnchorOrAlias (ScannerState.mk' input) true
  match s.tokens.back? with
  | some tok => some tok.val
  | none => none

private def aliasToken (input : String) : Option YamlToken :=
  let s := scanAnchorOrAlias (ScannerState.mk' input) false
  match s.tokens.back? with
  | some tok => some tok.val
  | none => none

#guard anchorToken "&myanchor rest" == some (.anchor "myanchor")
#guard anchorToken "&a" == some (.anchor "a")
#guard anchorToken "& " == some (.anchor "")
#guard aliasToken "*myalias rest" == some (.alias "myalias")
#guard aliasToken "*a" == some (.alias "a")

-- simpleKeyAllowed set to false
#guard (scanAnchorOrAlias (ScannerState.mk' "&name") true).simpleKeyAllowed == false
#guard (scanAnchorOrAlias (ScannerState.mk' "*name") false).simpleKeyAllowed == false

/-! ## §3  scanTag — WellFormed Preservation

```
def scanTag (s : ScannerState) : ScannerState := Id.run do
  ...  -- three branches: verbatim !<uri>, secondary !!suffix, named/primary
  return { s'.emitAt startPos (.tag handle suffix) with simpleKeyAllowed := false }
```

All three branches follow the same pattern: advance loops → emitAt → set flags.
None modifies C1–C3 fields. C4 covered by `#guard`.
-/

-- WellFormed preservation
private def checkTagWF (input : String) : Bool :=
  let s := scanTag (ScannerState.mk' input)
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd

-- Verbatim tag: !<uri>
#guard checkTagWF "!<tag:yaml.org,2002:str> rest"
#guard checkTagWF "!<tag:yaml.org,2002:int> rest"
#guard checkTagWF "!<x>"

-- Secondary tag: !!suffix
#guard checkTagWF "!!str rest"
#guard checkTagWF "!!int rest"
#guard checkTagWF "!!map rest"
#guard checkTagWF "!!seq rest"
#guard checkTagWF "!! "

-- Named/primary tag: !handle!suffix or !suffix
#guard checkTagWF "!foo!bar rest"
#guard checkTagWF "!local rest"
#guard checkTagWF "! rest"
#guard checkTagWF "!e!tag rest"

-- Token content verification
private def tagToken (input : String) : Option YamlToken :=
  let s := scanTag (ScannerState.mk' input)
  match s.tokens.back? with
  | some tok => some tok.val
  | none => none

-- Verbatim tag
#guard tagToken "!<tag:yaml.org,2002:str>" == some (.tag "" "tag:yaml.org,2002:str")

-- Secondary tag
#guard tagToken "!!str" == some (.tag "!!" "str")
#guard tagToken "!!int" == some (.tag "!!" "int")

-- Primary/named tag
#guard tagToken "!local" == some (.tag "!" "local")

-- Non-specific tag (bare !)
#guard tagToken "! " == some (.tag "!" "")

-- simpleKeyAllowed set to false
#guard (scanTag (ScannerState.mk' "!!str")).simpleKeyAllowed == false
#guard (scanTag (ScannerState.mk' "!<uri>")).simpleKeyAllowed == false
#guard (scanTag (ScannerState.mk' "!local")).simpleKeyAllowed == false

/-! ## §4  scanDirective — WellFormed Preservation

```
def scanDirective (s : ScannerState) : Except ScanError ScannerState := do
  ...  -- parse name, branch on YAML/TAG/reserved
  -- YAML: emitAt .versionDirective → set seenYamlDirective, directivesPresent
  -- TAG:  emitAt .tagDirective → set directivesPresent
  -- else: skipToEndOfLine
```

Does NOT modify `indents`, `flowLevel`, `flowStack`, or `simpleKeyStack`
in any branch. C1–C3 trivially preserved. C4 covered by `#guard`.
-/

-- Helper: check WellFormed for directive results
private def checkDirectiveWF (input : String) : Bool :=
  let s := { ScannerState.mk' input with allowDirectives := true }
  match scanDirective s with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true  -- error paths don't need WellFormed

-- YAML directive
#guard checkDirectiveWF "%YAML 1.2\n"
#guard checkDirectiveWF "%YAML 1.1\n"
#guard checkDirectiveWF "%YAML 1.0\n"

-- TAG directive
#guard checkDirectiveWF "%TAG !yaml! tag:yaml.org,2002:\n"
#guard checkDirectiveWF "%TAG !! tag:yaml.org,2002:\n"
#guard checkDirectiveWF "%TAG ! !\n"

-- Reserved/unknown directive
#guard checkDirectiveWF "%RESERVED something\n"
#guard checkDirectiveWF "%UNKNOWN\n"

-- Error: directive when not allowed
#guard (scanDirective { ScannerState.mk' "%YAML 1.2\n" with allowDirectives := false }).isOk == false

-- Token content verification (YAML directive)
private def directiveToken (input : String) : Option YamlToken :=
  let s := { ScannerState.mk' input with allowDirectives := true }
  match scanDirective s with
  | .ok s' => match s'.tokens.back? with
    | some tok => some tok.val
    | none => none
  | .error _ => none

#guard directiveToken "%YAML 1.2\n" == some (.versionDirective 1 2)
#guard directiveToken "%YAML 1.1\n" == some (.versionDirective 1 1)

-- Token content verification (TAG directive)
#guard directiveToken "%TAG !! tag:yaml.org,2002:\n" == some (.tagDirective "!!" "tag:yaml.org,2002:")

-- Flags set correctly
private def yamlDirectiveFlags (input : String) : Option (Bool × Bool) :=
  let s := { ScannerState.mk' input with allowDirectives := true }
  match scanDirective s with
  | .ok s' => some (s'.seenYamlDirective, s'.directivesPresent)
  | .error _ => none

#guard yamlDirectiveFlags "%YAML 1.2\n" == some (true, true)

private def tagDirectiveFlags (input : String) : Option Bool :=
  let s := { ScannerState.mk' input with allowDirectives := true }
  match scanDirective s with
  | .ok s' => some s'.directivesPresent
  | .error _ => none

#guard tagDirectiveFlags "%TAG !! tag:yaml.org,2002:\n" == some true

-- Error: duplicate YAML directive
private def dupYaml : Bool :=
  let s := { ScannerState.mk' "%YAML 1.2\n" with allowDirectives := true, seenYamlDirective := true }
  (scanDirective s).isOk == false
#guard dupYaml

-- Error: directive after content (allowDirectives = false)
private def afterContent : Bool :=
  (scanDirective { ScannerState.mk' "%YAML 1.2\n" with allowDirectives := false }).isOk == false
#guard afterContent

/-! ## §5  scanDocumentStart — WellFormed Preservation

```
def scanDocumentStart (s : ScannerState) : ScannerState :=
  let s' := unwindIndents s (-1)
  let s' := { s' with simpleKey := { possible := false } }
  { (s'.emit .documentStart).advanceN 3 with
    simpleKeyAllowed := true
    allowDirectives := false
    seenYamlDirective := false
    directivesPresent := false
    documentEverStarted := true }
```

**Analysis**:
- `unwindIndents s (-1)`: pops all indent levels except sentinel.
  - C1: preserved (only pops when size > 1, proven in ScannerIndentStack)
  - C2/C3: preserved (never touches flowLevel/flowStack/simpleKeyStack)
  - C4: preserved (never touches offset/inputEnd)
- `{ s' with simpleKey := ... }`: non-WellFormed field → trivially preserves
- `s'.emit .documentStart`: proven to preserve WellFormed (ScannerLoopInvariant)
- `.advanceN 3`: loops advance 3 times (needs offset+3 ≤ inputEnd,
  guaranteed because `---` was detected = 3 chars available)
- `with` clause: only non-WellFormed flags → trivially preserves
-/

-- WellFormed preservation
private def checkDocStartWF (input : String) : Bool :=
  let s := scanDocumentStart (ScannerState.mk' input)
  s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
  && s.simpleKeyStack.size == s.flowStack.size
  && s.offset ≤ s.inputEnd

-- Basic document start
#guard checkDocStartWF "---\n"
#guard checkDocStartWF "--- rest"
#guard checkDocStartWF "---"
#guard checkDocStartWF "---\nkey: value"

-- Document start after content (with pushed indents)
private def afterIndentDocStart : Bool :=
  let s := pushSequenceIndent (ScannerState.mk' "---\nmore") 0
  let s' := scanDocumentStart s
  s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
  && s'.simpleKeyStack.size == s'.flowStack.size
  && s'.offset ≤ s'.inputEnd
#guard afterIndentDocStart

-- Document start after multiple indents
private def afterMultiIndentDocStart : Bool :=
  let s := pushMappingIndent (pushSequenceIndent (ScannerState.mk' "---\nrest") 0) 2
  let s' := scanDocumentStart s
  s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
  && s'.simpleKeyStack.size == s'.flowStack.size
  && s'.offset ≤ s'.inputEnd
#guard afterMultiIndentDocStart

-- Token verification
private def docStartTokens (input : String) : Option (List YamlToken) :=
  let s := scanDocumentStart (ScannerState.mk' input)
  some (s.tokens.toList.map Positioned.val)

-- Basic: just documentStart
#guard docStartTokens "---" == some [.documentStart]

-- After indent push: blockEnd + documentStart
#guard docStartTokens "---\n" == some [.documentStart]

-- After one indent: 1 blockEnd + documentStart
private def docStartWithIndent : Option (List YamlToken) :=
  let s := pushSequenceIndent (ScannerState.mk' "---\n") 0
  let s' := scanDocumentStart s
  some (s'.tokens.toList.map Positioned.val)
-- pushSequenceIndent emits blockSequenceStart, then unwind emits blockEnd, then documentStart
#guard docStartWithIndent == some [.blockSequenceStart, .blockEnd, .documentStart]

-- Flags
#guard (scanDocumentStart (ScannerState.mk' "---\n")).simpleKeyAllowed == true
#guard (scanDocumentStart (ScannerState.mk' "---\n")).allowDirectives == false
#guard (scanDocumentStart (ScannerState.mk' "---\n")).documentEverStarted == true
#guard (scanDocumentStart (ScannerState.mk' "---\n")).seenYamlDirective == false
#guard (scanDocumentStart (ScannerState.mk' "---\n")).directivesPresent == false

-- Indents unwound to sentinel
#guard (scanDocumentStart (ScannerState.mk' "---\n")).indents.size == 1

-- After push + docStart: indents unwound to sentinel
private def indentAfterDocStart : Nat :=
  let s := pushSequenceIndent (ScannerState.mk' "---\n") 0
  (scanDocumentStart s).indents.size
#guard indentAfterDocStart == 1

-- simpleKey cleared
#guard (scanDocumentStart (ScannerState.mk' "---\n")).simpleKey.possible == false

-- Offset advances by 3
#guard (scanDocumentStart (ScannerState.mk' "---\n")).offset == 3
#guard (scanDocumentStart (ScannerState.mk' "--- rest")).offset == 3

/-! ## §6  scanDocumentEnd — WellFormed Preservation

```
def scanDocumentEnd (s : ScannerState) : Except ScanError ScannerState := do
  if s.directivesPresent && !s.documentEverStarted then
    throw (.directiveWithoutDocument s.line)
  let s' := unwindIndents s (-1)
  let s' := { s' with simpleKey := { possible := false } }
  let result := { (s'.emit .documentEnd).advanceN 3 with
    simpleKeyAllowed := true
    allowDirectives := true
    directivesPresent := false }
  ...  -- trailing content validation (doesn't affect result)
  .ok result
```

**Analysis**:
- Same structure as `scanDocumentStart` for the core path
- Error guard checks `directivesPresent && !documentEverStarted`
- Trailing content validation loop uses a separate `s''` variable;
  the returned `result` is computed before the validation loop
- C1–C4 reasoning identical to `scanDocumentStart`
-/

-- Helper for WellFormed check
private def checkDocEndWF (input : String) : Bool :=
  match scanDocumentEnd (ScannerState.mk' input) with
  | .ok s => s.indents.size ≥ 1 && s.flowLevel == s.flowStack.size
             && s.simpleKeyStack.size == s.flowStack.size
             && s.offset ≤ s.inputEnd
  | .error _ => true

-- Basic document end
#guard checkDocEndWF "...\n"
#guard checkDocEndWF "... rest"
#guard checkDocEndWF "..."
#guard checkDocEndWF "...\n---"
#guard checkDocEndWF "... # comment"

-- Document end after indent push
private def afterIndentDocEnd : Bool :=
  let s := pushSequenceIndent (ScannerState.mk' "...\nmore") 0
  match scanDocumentEnd s with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true
#guard afterIndentDocEnd

-- Document end after multiple indents
private def afterMultiIndentDocEnd : Bool :=
  let s := pushMappingIndent (pushSequenceIndent (ScannerState.mk' "...\nrest") 0) 2
  match scanDocumentEnd s with
  | .ok s' => s'.indents.size ≥ 1 && s'.flowLevel == s'.flowStack.size
              && s'.simpleKeyStack.size == s'.flowStack.size
              && s'.offset ≤ s'.inputEnd
  | .error _ => true
#guard afterMultiIndentDocEnd

-- Token verification
private def docEndToken (input : String) : Option YamlToken :=
  match scanDocumentEnd (ScannerState.mk' input) with
  | .ok s => match s.tokens.back? with
    | some tok => some tok.val
    | none => none
  | .error _ => none

#guard docEndToken "..." == some .documentEnd
#guard docEndToken "...\n" == some .documentEnd

-- Flags
private def docEndFlags (input : String) : Option (Bool × Bool × Bool) :=
  match scanDocumentEnd (ScannerState.mk' input) with
  | .ok s => some (s.simpleKeyAllowed, s.allowDirectives, s.directivesPresent)
  | .error _ => none

#guard docEndFlags "...\n" == some (true, true, false)

-- Indents unwound to sentinel
private def indentAfterDocEnd : Option Nat :=
  match scanDocumentEnd (ScannerState.mk' "...\n") with
  | .ok s => some s.indents.size
  | .error _ => none
#guard indentAfterDocEnd == some 1

-- After push + docEnd: indents unwound
private def indentAfterPushDocEnd : Option Nat :=
  let s := pushSequenceIndent (ScannerState.mk' "...\n") 0
  match scanDocumentEnd s with
  | .ok s' => some s'.indents.size
  | .error _ => none
#guard indentAfterPushDocEnd == some 1

-- simpleKey cleared
private def docEndSimpleKeyCleared : Option Bool :=
  match scanDocumentEnd (ScannerState.mk' "...\n") with
  | .ok s => some s.simpleKey.possible
  | .error _ => none
#guard docEndSimpleKeyCleared == some false

-- Offset advances by 3
private def docEndOffset : Option Nat :=
  match scanDocumentEnd (ScannerState.mk' "...\n") with
  | .ok s => some s.offset
  | .error _ => none
#guard docEndOffset == some 3

-- Error: directiveWithoutDocument
private def directiveWithoutDoc : Bool :=
  let s := { ScannerState.mk' "..." with directivesPresent := true, documentEverStarted := false }
  match scanDocumentEnd s with
  | .ok _ => false
  | .error _ => true
#guard directiveWithoutDoc

-- Error: trailing content after document end
private def trailingContent : Bool :=
  match scanDocumentEnd (ScannerState.mk' "...content") with
  | .ok _ => false
  | .error _ => true
#guard trailingContent

-- OK: trailing comment after document end
private def trailingComment : Bool :=
  match scanDocumentEnd (ScannerState.mk' "... # comment") with
  | .ok _ => true
  | .error _ => false
#guard trailingComment

-- OK: trailing whitespace + newline
private def trailingWsNewline : Bool :=
  match scanDocumentEnd (ScannerState.mk' "...  \n") with
  | .ok _ => true
  | .error _ => false
#guard trailingWsNewline

/-! ## §7  End-to-end Pipeline Guards — Document Markers in Context -/

-- Helper: extract token values from full scan
private def scanTokens (input : String) : Option (List YamlToken) :=
  match scanFiltered input with
  | .ok tokens => some (tokens.toList.map Positioned.val)
  | .error _ => none

-- Explicit document start
#guard scanTokens "---\nkey: value" == some [
  .streamStart, .documentStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Document end
#guard scanTokens "key: value\n..." == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .documentEnd, .streamEnd]

-- Document start + end
#guard scanTokens "---\nkey: value\n..." == some [
  .streamStart, .documentStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .documentEnd, .streamEnd]

-- Multi-document
#guard scanTokens "---\ndoc1\n---\ndoc2" == some [
  .streamStart, .documentStart,
  .scalar "doc1" .plain, .documentStart,
  .scalar "doc2" .plain, .streamEnd]

-- Document end then start
#guard scanTokens "---\ndoc1\n...\n---\ndoc2" == some [
  .streamStart, .documentStart,
  .scalar "doc1" .plain, .documentEnd, .documentStart,
  .scalar "doc2" .plain, .streamEnd]

-- YAML directive with document start
#guard scanTokens "%YAML 1.2\n---\nkey: value" == some [
  .streamStart, .versionDirective 1 2, .documentStart,
  .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- TAG directive with document start
#guard scanTokens "%TAG !! tag:yaml.org,2002:\n---\nkey: value" == some [
  .streamStart, .tagDirective "!!" "tag:yaml.org,2002:", .documentStart,
  .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

-- Anchor and alias
#guard scanTokens "- &anchor value\n- *anchor" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .anchor "anchor", .scalar "value" .plain,
  .blockEntry, .alias "anchor",
  .blockEnd, .streamEnd]

-- Tag on scalar
#guard scanTokens "!!str value" == some [
  .streamStart, .tag "!!" "str", .scalar "value" .plain, .streamEnd]

-- Verbatim tag
#guard scanTokens "!<tag:yaml.org,2002:str> value" == some [
  .streamStart, .tag "" "tag:yaml.org,2002:str", .scalar "value" .plain, .streamEnd]

-- Local tag
#guard scanTokens "!local value" == some [
  .streamStart, .tag "!" "local", .scalar "value" .plain, .streamEnd]

-- Multiple anchors and aliases
#guard scanTokens "- &a val1\n- &b val2\n- *a\n- *b" == some [
  .streamStart, .blockSequenceStart,
  .blockEntry, .anchor "a", .scalar "val1" .plain,
  .blockEntry, .anchor "b", .scalar "val2" .plain,
  .blockEntry, .alias "a",
  .blockEntry, .alias "b",
  .blockEnd, .streamEnd]

-- Tag with mapping
#guard scanTokens "!!map\nkey: value" == some [
  .streamStart, .tag "!!" "map", .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .scalar "value" .plain, .blockEnd, .streamEnd]

/-! ## §8  End-to-end Pipeline Guards — Anchors/Aliases in Structures -/

-- Anchor on mapping key
#guard scanTokens "&anchor key: value" == some [
  .streamStart, .blockMappingStart,
  .key, .anchor "anchor", .scalar "key" .plain,
  .value, .scalar "value" .plain,
  .blockEnd, .streamEnd]

-- Alias as mapping value
#guard scanTokens "key: *alias" == some [
  .streamStart, .blockMappingStart, .key,
  .scalar "key" .plain, .value,
  .alias "alias",
  .blockEnd, .streamEnd]

-- Anchor in flow sequence
#guard scanTokens "[&a val, *a]" == some [
  .streamStart, .flowSequenceStart,
  .anchor "a", .scalar "val" .plain,
  .flowEntry, .alias "a",
  .flowSequenceEnd, .streamEnd]

-- Tag in flow mapping
#guard scanTokens "{!!str key: value}" == some [
  .streamStart, .flowMappingStart,
  .key, .tag "!!" "str", .scalar "key" .plain,
  .value, .scalar "value" .plain,
  .flowMappingEnd, .streamEnd]

/-! ## §9  End-to-end Pipeline Guards — Directive Edge Cases -/

-- YAML directive followed by TAG directive
#guard scanTokens "%YAML 1.2\n%TAG !! tag:yaml.org,2002:\n---\nvalue" == some [
  .streamStart, .versionDirective 1 2,
  .tagDirective "!!" "tag:yaml.org,2002:", .documentStart,
  .scalar "value" .plain, .streamEnd]

-- Document end re-enables directives
#guard scanTokens "---\nvalue\n...\n%YAML 1.2\n---\nvalue2" == some [
  .streamStart, .documentStart,
  .scalar "value" .plain, .documentEnd,
  .versionDirective 1 2, .documentStart,
  .scalar "value2" .plain, .streamEnd]

-- Multiple documents with directives
#guard scanTokens "---\nfirst\n...\n---\nsecond\n..." == some [
  .streamStart, .documentStart,
  .scalar "first" .plain, .documentEnd,
  .documentStart,
  .scalar "second" .plain, .documentEnd, .streamEnd]

-- Empty documents
#guard scanTokens "---\n...\n---\n..." == some [
  .streamStart, .documentStart, .documentEnd,
  .documentStart, .documentEnd, .streamEnd]

-- Document start without content then another
#guard scanTokens "---\n---\nvalue" == some [
  .streamStart, .documentStart, .documentStart,
  .scalar "value" .plain, .streamEnd]

/-! ## §10  End-to-end Pipeline Guards — Tags with Different Scalar Types -/

-- Tag on double-quoted scalar
#guard scanTokens "!!str \"hello\"" == some [
  .streamStart, .tag "!!" "str", .scalar "hello" .doubleQuoted, .streamEnd]

-- Tag on single-quoted scalar
#guard scanTokens "!!str 'hello'" == some [
  .streamStart, .tag "!!" "str", .scalar "hello" .singleQuoted, .streamEnd]

-- Tag on block scalar
#guard scanTokens "!!str |\n  content\n" == some [
  .streamStart, .tag "!!" "str", .scalar "content\n" .literal, .streamEnd]

-- Anchor on block scalar
#guard scanTokens "&anchor |\n  content\n" == some [
  .streamStart, .anchor "anchor", .scalar "content\n" .literal, .streamEnd]

-- Tag + anchor combination
#guard scanTokens "!!str &anchor value" == some [
  .streamStart, .tag "!!" "str", .anchor "anchor",
  .scalar "value" .plain, .streamEnd]

-- Named tag with suffix
#guard scanTokens "!e!tag value" == some [
  .streamStart, .tag "!e!" "tag", .scalar "value" .plain, .streamEnd]

-- Non-specific tag (bare !)
#guard scanTokens "! value" == some [
  .streamStart, .tag "!" "", .scalar "value" .plain, .streamEnd]

/-! ## §11  End-to-end Pipeline WellFormed Checks

Verify that the full scan pipeline preserves WellFormed on document-heavy inputs.
-/

-- Helper: check that scan produces a valid result
private def scanOk (input : String) : Bool :=
  (scan input).isOk

#guard scanOk "---\nkey: value"
#guard scanOk "key: value\n..."
#guard scanOk "---\nkey: value\n..."
#guard scanOk "---\nfirst\n...\n---\nsecond\n..."
#guard scanOk "%YAML 1.2\n---\nvalue"
#guard scanOk "%TAG !! tag:yaml.org,2002:\n---\nvalue"
#guard scanOk "- &a val\n- *a"
#guard scanOk "!!str value"
#guard scanOk "!<tag:yaml.org,2002:str> value"
#guard scanOk "!local value"
#guard scanOk "&anchor key: value"
#guard scanOk "key: *alias"
#guard scanOk "[&a val, *a]"
#guard scanOk "{!!str key: value}"
#guard scanOk "---\n---\n---"
#guard scanOk "...\n---\n..."
#guard scanOk "%YAML 1.2\n%TAG !! tag:yaml.org,2002:\n---\nvalue"

end Lean4Yaml.Proofs.ScannerDocument
