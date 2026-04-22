/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State

/-!
# Scanner — Node Properties (Anchors, Aliases, Tags)

Anchor (`&name`), alias (`*name`), and tag (`!`, `!!suffix`,
`!handle!suffix`, `!<uri>`) scanning.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2, into
its own submodule because YAML 1.2.2 §6.9 groups these as the
**node properties** of a node (`[96] c-ns-properties(n,c)`).

## Spec mapping

- `[96]  c-ns-properties(n,c)` — the combination of anchor + tag that
  can prefix any node.
- `[101] c-ns-anchor-property`, `[102] ns-anchor-char`, `[103] ns-anchor-name`.
- `[104] c-ns-alias-node`.
- `[97]  c-ns-tag-property`, `[98] c-verbatim-tag`, `[99] c-ns-shorthand-tag`,
  `[100] c-non-specific-tag`.
- `[89]–[92]` tag-handle handles (primary, secondary, named).

## Scope

- `collectAnchorNameLoop`, `scanAnchorOrAlias`.
- `collectVerbatimTagLoop`, `collectTagSuffixLoop`, `collectTagHandleLoop`.
- `scanVerbatimTag`, `scanSecondaryTag`, `scanNamedTag`, `scanTag`.
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Anchor and Alias Scanning -/

/-- Scan an anchor (`&name`) or alias (`*name`) indicator.

    **Implements** (YAML 1.2.2 §6.9):
    - `[101] c-ns-anchor-property` = `"&" ns-anchor-name`
    - `[104] c-ns-alias-node`      = `"*" ns-anchor-name`
    - `[102] ns-anchor-char`       = `ns-char - c-flow-indicator`
    - `[103] ns-anchor-name`       = `ns-anchor-char+`
    - `[13]  c-anchor` = `"&"` / `[14] c-alias` = `"*"`

    **Pre**: Scanner at `&` (anchor) or `*` (alias).
    **Post**: Advances past indicator + name characters, emits `.anchor name`
    or `.alias name`. Sets `simpleKeyAllowed := false`. -/
-- Helper: Collect anchor/alias name characters using structural recursion.
@[yaml_spec "6.9" 101 "c-ns-anchor-property", yaml_spec "6.9" 104 "c-ns-alias-node", yaml_spec "6.9" 102 "ns-anchor-char", yaml_spec "6.9" 103 "ns-anchor-name", yaml_spec "6.9" 13 "c-anchor", yaml_spec "6.9" 14 "c-alias"]
def collectAnchorNameLoop (s : ScannerState) (name : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (name, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if !isFlowIndicatorBool c && !isWhiteSpaceBool c && !isLineBreakBool c then
        collectAnchorNameLoop s.advance (name.push c) fuel'
      else
        (name, s)
    | none => (name, s)

@[yaml_spec "6.9" 101 "c-ns-anchor-property",
  yaml_spec "6.9" 104 "c-ns-alias-node"]
def scanAnchorOrAlias (s : ScannerState) (isAnchor : Bool) : Except ScanError ScannerState :=
  let startPos := s.currentPos
  let s_after_marker := s.advance
  let fuel := s.inputEnd - s_after_marker.offset
  let (name, s_after_name) := collectAnchorNameLoop s_after_marker "" fuel
  if name.isEmpty then
    .error (.emptyAnchorName startPos.line startPos.col)
  else
    let token := if isAnchor then YamlToken.anchor name else YamlToken.alias name
    let s_with_token := s_after_name.emitAt startPos token
    .ok { s_with_token with simpleKeyAllowed := false }

/-! ## Tag Scanning -/

-- Helper: Collect verbatim tag URI until '>', accepting only ns-uri-char [39].
-- Returns (uri, foundClose, state) where foundClose is true iff '>' was consumed.
@[yaml_spec "5.6" 39 "ns-uri-char"]
def collectVerbatimTagLoop (s : ScannerState) (uri : String) (fuel : Nat) : String × Bool × ScannerState :=
  match fuel with
  | 0 => (uri, false, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '>' => (uri, true, s.advance)
    | some c =>
      if isUriCharBool c then
        collectVerbatimTagLoop s.advance (uri.push c) fuel'
      else
        (uri, false, s)
    | none => (uri, false, s)

-- Helper: Collect tag suffix characters using ns-tag-char [40].
@[yaml_spec "5.6" 39 "ns-uri-char",
  yaml_spec "5.6" 40 "ns-tag-char"]
def collectTagSuffixLoop (s : ScannerState) (suffix : String) (fuel : Nat) : String × ScannerState :=
  match fuel with
  | 0 => (suffix, s)
  | fuel' + 1 =>
    match s.peek? with
    | some c =>
      if isTagCharBool c then
        collectTagSuffixLoop s.advance (suffix.push c) fuel'
      else
        (suffix, s)
    | none => (suffix, s)

-- Helper: Collect tag handle characters until '!' or invalid char.
-- Between the opening and closing '!', only ns-word-char [38] is valid per [92].
-- Returns (chars_before_bang, found_second_bang, state).
@[yaml_spec "5.6" 38 "ns-word-char"]
def collectTagHandleLoop (s : ScannerState) (chars : String) (fuel : Nat) : String × Bool × ScannerState :=
  match fuel with
  | 0 => (chars, false, s)
  | fuel' + 1 =>
    match s.peek? with
    | some '!' => (chars, true, s.advance)
    | some c =>
      if isWordCharBool c then
        collectTagHandleLoop s.advance (chars.push c) fuel'
      else
        (chars, false, s)
    | none => (chars, false, s)

/-- Scan a verbatim tag `!<uri>`.  Pre: scanner after first `!`, peek = `<`. -/
@[yaml_spec "6.9" 98 "c-verbatim-tag"]
def scanVerbatimTag (s : ScannerState) (startPos : YamlPos) : Except ScanError ScannerState :=
  let s_after_open := s.advance
  let fuel := startPos.offset + s.inputEnd - s_after_open.offset  -- conservative fuel
  let (uri, foundClose, s_after_uri) := collectVerbatimTagLoop s_after_open "" fuel
  if !foundClose then
    .error (.unterminatedVerbatimTag startPos.line startPos.col)
  else if uri.isEmpty then
    .error (.emptyVerbatimTagURI startPos.line startPos.col)
  else
    .ok (s_after_uri.emitAt startPos (.tag "" uri))

/-- Scan a secondary tag `!!suffix`.  Pre: scanner after first `!`, peek = `!`. -/
@[yaml_spec "6.8.2" 91 "c-secondary-tag-handle",
  yaml_spec "6.9" 99 "c-ns-shorthand-tag"]
def scanSecondaryTag (s : ScannerState) (startPos : YamlPos) : ScannerState :=
  let s_after_second_bang := s.advance
  let fuel := startPos.offset + s.inputEnd - s_after_second_bang.offset
  let (suffix, s_after_suffix) := collectTagSuffixLoop s_after_second_bang "" fuel
  s_after_suffix.emitAt startPos (.tag "!!" suffix)

/-- Scan a named/primary tag `!handle!suffix` or `!suffix`.
    Pre: scanner after first `!`, peek ≠ `<` and ≠ `!`. -/
@[yaml_spec "6.8.2" 90 "c-primary-tag-handle",
  yaml_spec "6.8.2" 92 "c-named-tag-handle",
  yaml_spec "6.9" 99 "c-ns-shorthand-tag",
  yaml_spec "6.9" 100 "c-non-specific-tag"]
def scanNamedTag (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) : ScannerState :=
  let fuel := inputEnd - s.offset
  let (chars, foundBang, s_after_handle) := collectTagHandleLoop s "" fuel
  let (handle, suffix_or_chars) :=
    if foundBang then
      ("!" ++ chars ++ "!", "")
    else
      ("!", chars)
  let (suffix, s_after_suffix) :=
    if foundBang then
      let fuel' := inputEnd - s_after_handle.offset
      collectTagSuffixLoop s_after_handle "" fuel'
    else
      (suffix_or_chars, s_after_handle)
  s_after_suffix.emitAt startPos (.tag handle suffix)

/-- Scan a tag property (`!`, `!!suffix`, `!handle!suffix`, `!<uri>`).
    Dispatches to `scanVerbatimTag`, `scanSecondaryTag`, or `scanNamedTag`. -/
@[yaml_spec "6.9" 97 "c-ns-tag-property"]
def scanTag (s : ScannerState) : Except ScanError ScannerState :=
  let startPos := s.currentPos
  let s_after_bang := s.advance  -- consume `!`
  match s_after_bang.peek? with
  | some '<' => do
    let s_inner ← scanVerbatimTag s_after_bang startPos
    return { s_inner with simpleKeyAllowed := false }
  | some '!' =>
    let s_inner := scanSecondaryTag s_after_bang startPos
    .ok { s_inner with simpleKeyAllowed := false }
  | _ =>
    let s_inner := scanNamedTag s_after_bang startPos s.inputEnd
    .ok { s_inner with simpleKeyAllowed := false }

end L4YAML.Scanner
