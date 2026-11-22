/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.IndexedState
public import L4YAML.Proofs.Scanner.IndexedWhitespace
public import L4YAML.Proofs.Scanner.IndexedScalar

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-! # `IndexedDispatch` — Phase 3 top-level scanner

This file ties the per-rule recognisers from
`L4YAML/Scanner/IndexedScanner.lean` to a top-level scanner over
`ScannerStateIx input`, producing a `TokenStream input`. The shape
mirrors the legacy `L4YAML/Scanner/{SimpleKey,Document,NodeProperties,
Scanner}.lean` family, threaded over `IxCursor input` instead of the
un-indexed offset triple.

## Layout

1. Helper recogniser loops (`collect*Ix`, `skipDocEndWhitespaceIx`).
2. Helper-loop offset-monotonicity lemmas (Step 5b.1a).
3. `ScannerStateIx`-namespaced dispatchers: simple-key save/resolve,
   block indicators, document markers, directives, anchor/alias, tag,
   flow indicators, the five-way `scanNextTokenIx_*` dispatch family,
   `scanLoopIx`, and the top-level `scanIx`.

## Scope

- **Step 5a** landed the dispatcher skeleton + state, with the per-
  rule recognisers from `IndexedScanner.lean` wired in. The
  validation chain inside `scanValueIx` was simplified relative to
  the legacy four-stage split; the tab-in-indentation hardening on
  `scanBlockEntryIx` / `scanKeyIx` was deferred.
- **Step 5b.1a** added the eight helper-loop monotonicity lemmas
  (between sections 1 and 3), replaced the ten `emitAtSafe` use
  sites with `emitAt` + inline proofs, threaded an `hStart`
  parameter through `scanYamlDirectiveIx` / `scanTagDirectiveIx`,
  and deleted `emitAtSafe`.
- **Step 5b.1b–5b.8** (planned, Blueprint 08): per-dispatcher
  monotonicity lemmas; `scanValueIx` validation chain split;
  tab-in-indentation hardening; hex-escape value-correctness;
  `autoDetectBlockScalarIndentLoopIx` correctness; block-scalar
  fold/chomp correctness; quoted multi-line correctness; plain
  multi-line correctness.
-/

namespace L4YAML.Scanner.Indexed

open L4YAML L4YAML.Indexed L4YAML.CharPredicates

/-! ## Helper recognisers carried over from legacy

These mirror small named-tag / verbatim-tag / anchor-name loops from
`Scanner/NodeProperties.lean` and `Scanner/Document.lean`.
Each is structurally recursive on `fuel`. -/

/-- Collect anchor-name characters (§6.9 [102] `ns-anchor-char`+). -/
def collectAnchorNameLoopIx {input : String} (c : IxCursor input)
    (name : String) : Nat → String × IxCursor input
  | 0 => (name, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if !isFlowIndicatorBool ch && !isWhiteSpaceBool ch && !isLineBreakBool ch
          && isPrintableBool ch && ch != '﻿' then
        collectAnchorNameLoopIx c.advance (name.push ch) fuel
      else (name, c)
    | none => (name, c)

/-- Collect tag-handle characters (`ns-word-char`+, terminated by `!`).
    Returns (handle-chars, found-second-bang, cursor-after-handle). -/
def collectTagHandleLoopIx {input : String} (c : IxCursor input)
    (chars : String) : Nat → String × Bool × IxCursor input
  | 0 => (chars, false, c)
  | fuel + 1 =>
    match c.peek? with
    | some '!' => (chars, true, c.advance)
    | some ch =>
      if isWordCharBool ch then
        collectTagHandleLoopIx c.advance (chars.push ch) fuel
      else (chars, false, c)
    | none => (chars, false, c)

/-- Collect tag-suffix characters (`ns-tag-char`+). -/
def collectTagSuffixLoopIx {input : String} (c : IxCursor input)
    (suffix : String) : Nat → String × IxCursor input
  | 0 => (suffix, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isTagCharBool ch then
        collectTagSuffixLoopIx c.advance (suffix.push ch) fuel
      else (suffix, c)
    | none => (suffix, c)

/-- Collect TAG-directive handle characters (`ns-word-char` or `!`),
    mirroring the legacy `collectTagHandleDirectiveLoop` ([89]-[92]):
    the leading and trailing `!` are part of the handle. -/
def collectTagHandleDirectiveLoopIx {input : String} (c : IxCursor input)
    (handle : String) : Nat → String × IxCursor input
  | 0 => (handle, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isWordCharBool ch || ch == '!' then
        collectTagHandleDirectiveLoopIx c.advance (handle.push ch) fuel
      else (handle, c)
    | none => (handle, c)

/-- Collect TAG-directive prefix characters (`ns-uri-char`+ per [93]-[95]),
    mirroring the legacy `collectTagPrefixLoop`. Broader than
    `collectTagSuffixLoopIx`: URI chars include `!`, `,` and flow
    indicators, which tag-suffix chars exclude. -/
def collectTagPrefixLoopIx {input : String} (c : IxCursor input)
    (pfx : String) : Nat → String × IxCursor input
  | 0 => (pfx, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isUriCharBool ch then
        collectTagPrefixLoopIx c.advance (pfx.push ch) fuel
      else (pfx, c)
    | none => (pfx, c)

/-- Skip to the end of the current line (stop before the line break),
    mirroring the legacy `skipToEndOfLineLoop`. Used by directive
    scanning to discard the validated remainder of a directive line. -/
def skipToEndOfLineLoopIx {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0 => c
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if isLineBreakBool ch then c else skipToEndOfLineLoopIx c.advance fuel
    | none => c

/-- Skip to end of line (fuel wrapper), mirroring `skipToEndOfLine`. -/
def skipToEndOfLineIx {input : String} (c : IxCursor input) : IxCursor input :=
  skipToEndOfLineLoopIx c (input.utf8ByteSize - c.pos.offset)

/-- Collect a verbatim tag URI body until `>`. Returns
    (uri, found-close, cursor-after). -/
def collectVerbatimTagLoopIx {input : String} (c : IxCursor input)
    (uri : String) : Nat → String × Bool × IxCursor input
  | 0 => (uri, false, c)
  | fuel + 1 =>
    match c.peek? with
    | some '>' => (uri, true, c.advance)
    | some ch =>
      if isUriCharBool ch then
        collectVerbatimTagLoopIx c.advance (uri.push ch) fuel
      else (uri, false, c)
    | none => (uri, false, c)

/-- Collect a directive-name run (non-whitespace, non-linebreak). -/
def collectDirectiveNameLoopIx {input : String} (c : IxCursor input)
    (name : String) : Nat → String × IxCursor input
  | 0 => (name, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if !isWhiteSpaceBool ch && !isLineBreakBool ch
          && isPrintableBool ch && ch != '﻿' then
        collectDirectiveNameLoopIx c.advance (name.push ch) fuel
      else (name, c)
    | none => (name, c)

/-- Collect digit characters terminated by `.`; returns
    (digits-before-dot, cursor-after-dot). -/
def collectVersionMajorLoopIx {input : String} (c : IxCursor input)
    (major : String) : Nat → String × IxCursor input
  | 0 => (major, c)
  | fuel + 1 =>
    match c.peek? with
    | some '.' => (major, c.advance)
    | some ch =>
      if ch.isDigit then
        collectVersionMajorLoopIx c.advance (major.push ch) fuel
      else (major, c)
    | none => (major, c)

/-- Collect digit characters. -/
def collectVersionMinorLoopIx {input : String} (c : IxCursor input)
    (minor : String) : Nat → String × IxCursor input
  | 0 => (minor, c)
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if ch.isDigit then
        collectVersionMinorLoopIx c.advance (minor.push ch) fuel
      else (minor, c)
    | none => (minor, c)

/-- Skip a contiguous run of spaces/tabs on a single line — used by
    `scanDocumentEndIx` to validate trailing content. -/
def skipDocEndWhitespaceIx {input : String} (c : IxCursor input) :
    Nat → IxCursor input
  | 0 => c
  | fuel + 1 =>
    match c.peek? with
    | some ch =>
      if ch == ' ' || ch == '\t' then skipDocEndWhitespaceIx c.advance fuel
      else c
    | none => c

/-! ## Helper-loop offset monotonicity (Step 5b.1a)

Each `collect*Ix` helper consumes characters left-to-right and either
recurses on `c.advance` or returns the input cursor unchanged. Hence
every helper's output cursor sits at a byte offset `≥` the input
cursor's offset. These lemmas discharge the bound obligation when the
dispatcher functions construct indexed tokens spanning from a saved
`startPos` to the cursor returned by the helper.

The proofs follow the pattern used by `skipSpacesLoop_offset_monotonic`
in `Proofs/Scanner/IndexedWhitespace.lean`: induction on `fuel`,
`unfold` the loop, then `split` on each branching `match` / `if`. The
recursive branch chains `advance_offset_monotonic` with the IH. -/

lemma collectAnchorNameLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (name : String) (fuel : Nat) :
    c.pos.offset ≤ (collectAnchorNameLoopIx c name fuel).2.pos.offset := by
  induction fuel generalizing c name with
  | zero => unfold collectAnchorNameLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectAnchorNameLoopIx
    split
    · -- some ch
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectTagHandleLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (chars : String) (fuel : Nat) :
    c.pos.offset ≤ (collectTagHandleLoopIx c chars fuel).2.2.pos.offset := by
  induction fuel generalizing c chars with
  | zero => unfold collectTagHandleLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectTagHandleLoopIx
    split
    · -- some '!': returns (chars, true, c.advance)
      exact IxCursor.advance_offset_monotonic c
    · -- some ch (other)
      split
      · -- isWordCharBool ch: recurse on c.advance
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · -- not word char: returns (chars, false, c)
        exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectTagSuffixLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (suffix : String) (fuel : Nat) :
    c.pos.offset ≤ (collectTagSuffixLoopIx c suffix fuel).2.pos.offset := by
  induction fuel generalizing c suffix with
  | zero => unfold collectTagSuffixLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectTagSuffixLoopIx
    split
    · -- some ch
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectTagHandleDirectiveLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (handle : String) (fuel : Nat) :
    c.pos.offset ≤ (collectTagHandleDirectiveLoopIx c handle fuel).2.pos.offset := by
  induction fuel generalizing c handle with
  | zero => unfold collectTagHandleDirectiveLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectTagHandleDirectiveLoopIx
    split
    · -- some ch
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectTagPrefixLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (pfx : String) (fuel : Nat) :
    c.pos.offset ≤ (collectTagPrefixLoopIx c pfx fuel).2.pos.offset := by
  induction fuel generalizing c pfx with
  | zero => unfold collectTagPrefixLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectTagPrefixLoopIx
    split
    · -- some ch
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma skipToEndOfLineLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (fuel : Nat) :
    c.pos.offset ≤ (skipToEndOfLineLoopIx c fuel).pos.offset := by
  induction fuel generalizing c with
  | zero => unfold skipToEndOfLineLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipToEndOfLineLoopIx
    split
    · -- some ch
      split
      · exact Nat.le_refl _
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance)
    · -- none
      exact Nat.le_refl _

lemma skipToEndOfLineIx_offset_monotonic {input : String}
    (c : IxCursor input) :
    c.pos.offset ≤ (skipToEndOfLineIx c).pos.offset :=
  skipToEndOfLineLoopIx_offset_monotonic c _

lemma collectVerbatimTagLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (uri : String) (fuel : Nat) :
    c.pos.offset ≤ (collectVerbatimTagLoopIx c uri fuel).2.2.pos.offset := by
  induction fuel generalizing c uri with
  | zero => unfold collectVerbatimTagLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectVerbatimTagLoopIx
    split
    · -- some '>': returns (uri, true, c.advance)
      exact IxCursor.advance_offset_monotonic c
    · -- some ch (other)
      split
      · -- isUriCharBool ch: recurse on c.advance
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · -- not uri char: returns (uri, false, c)
        exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectDirectiveNameLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (name : String) (fuel : Nat) :
    c.pos.offset ≤ (collectDirectiveNameLoopIx c name fuel).2.pos.offset := by
  induction fuel generalizing c name with
  | zero => unfold collectDirectiveNameLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectDirectiveNameLoopIx
    split
    · -- some ch
      split
      · exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectVersionMajorLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (major : String) (fuel : Nat) :
    c.pos.offset ≤ (collectVersionMajorLoopIx c major fuel).2.pos.offset := by
  induction fuel generalizing c major with
  | zero => unfold collectVersionMajorLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectVersionMajorLoopIx
    split
    · -- some '.': returns (major, c.advance)
      exact IxCursor.advance_offset_monotonic c
    · -- some ch (other)
      split
      · -- digit: recurse on c.advance
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · -- non-digit: returns (major, c)
        exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma collectVersionMinorLoopIx_offset_monotonic {input : String}
    (c : IxCursor input) (minor : String) (fuel : Nat) :
    c.pos.offset ≤ (collectVersionMinorLoopIx c minor fuel).2.pos.offset := by
  induction fuel generalizing c minor with
  | zero => unfold collectVersionMinorLoopIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold collectVersionMinorLoopIx
    split
    · -- some ch
      split
      · -- digit: recurse on c.advance
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance _)
      · -- non-digit: returns (minor, c)
        exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

lemma skipDocEndWhitespaceIx_offset_monotonic {input : String}
    (c : IxCursor input) (fuel : Nat) :
    c.pos.offset ≤ (skipDocEndWhitespaceIx c fuel).pos.offset := by
  induction fuel generalizing c with
  | zero => unfold skipDocEndWhitespaceIx; exact Nat.le_refl _
  | succ fuel ih =>
    unfold skipDocEndWhitespaceIx
    split
    · -- some ch
      split
      · -- space or tab: recurse on c.advance
        exact Nat.le_trans (IxCursor.advance_offset_monotonic c) (ih c.advance)
      · -- other: returns c
        exact Nat.le_refl _
    · -- none
      exact Nat.le_refl _

namespace ScannerStateIx

/-! ## Simple-key save

`saveSimpleKeyIx` reserves two placeholder slots in the token stream;
`scanValuePrepareIx` overwrites them with `blockMappingStart` + `key`
when a `:` retroactively confirms the simple key. -/

/-- Item 333, indexed twin of `closeStaleExplicitKey` (see its docstring): a
    sibling entry at or left of the `?`'s column ends the pending explicit key. -/
@[yaml_spec "8.2.2"]
def closeStaleExplicitKeyIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  if s.inFlow then s
  else match s.explicitKeyLine, s.peek? with
    | some _, some c =>
      if PendingKeys.staleGate (s.cursor.pos.col : Int) s.explicitKeyCol c (s.peekAt? 1) then
        (s.closeStaleAt c).readPendingKey
      else s
    | _, _ => s

/-- Reserve placeholder slots and record the current cursor as a
    potential implicit key. -/
def saveSimpleKeyIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  if s.inFlow && s.explicitKeyLine == some s.cursor.pos.line then s
  else if s.simpleKeyAllowed then
    let idx := s.tokens.size
    let s := s.emit YamlToken.placeholder
    let s := s.emit YamlToken.placeholder
    { s with
        simpleKey := {
          possible := true,
          tokenIndex := idx,
          cursor := s.cursor,
          endLine := s.cursor.pos.line } }
  else s

/-! ## Candidate predicates (block indicator lookahead) -/

/-- Whether `-` at the current cursor is a block-entry indicator. -/
def isBlockEntryCandidateIx {input : String} (s : ScannerStateIx input) : Bool :=
  match s.peekAt? 1 with
  | some n => isBlankBool n
  | none => true

/-- Whether `?` at the current cursor is an explicit-key indicator. -/
def isKeyCandidateIx {input : String} (s : ScannerStateIx input) : Bool :=
  match s.peekAt? 1 with
  | some n => isBlankBool n || (s.inFlow && isFlowIndicatorBool n)
  | none => true

/-- Whether a token is a JSON-like flow node end (§7.5 [160]). -/
def isJsonNodeTokenIx (tok : YamlToken) : Bool :=
  match tok with
  | .scalar _ .doubleQuoted => true
  | .scalar _ .singleQuoted => true
  | .flowSequenceEnd => true
  | .flowMappingEnd => true
  | _ => false

/-- Indexed twin of `flowGluedCollectionValue` (§7.4.2 [147]/[149]). -/
def flowGluedCollectionValueIx {input : String} (s : ScannerStateIx input) : Bool :=
  s.inFlow
    && (match s.peekAt? 1 with
        | some n => n == '[' || n == '{'
        | none => false)
    && !(match (if s.simpleKey.possible
                    && s.simpleKey.cursor.pos.offset == s.cursor.pos.offset
                then s.tokens.tokens[s.simpleKey.tokenIndex - 1]?
                else s.tokens.tokens[s.tokens.size - 1]?) with
         | some t => isJsonNodeTokenIx t.token
         | none => false)

/-- Whether `:` at the current cursor is a value indicator. -/
def isValueCandidateIx {input : String} (s : ScannerStateIx input) : Bool :=
  if s.inFlow && s.simpleKey.possible then
    if s.simpleKey.cursor.pos.offset != s.cursor.pos.offset then
      let isJsonKey := match s.tokens.tokens[s.tokens.size - 1]? with
        | some t => isJsonNodeTokenIx t.token
        | none => false
      if isJsonKey then true
      else match s.peekAt? 1 with
        | some n => isBlankBool n || isFlowIndicatorBool n
        | none => true
    else
      let jsonAdjacent := match s.tokens.tokens[s.simpleKey.tokenIndex - 1]? with
        | some t => isJsonNodeTokenIx t.token
        | none => false
      if jsonAdjacent then true
      else match s.peekAt? 1 with
        | some n => isBlankBool n || isFlowIndicatorBool n
        | none => true
  else match s.peekAt? 1 with
    | some n => isBlankBool n || (s.inFlow && isFlowIndicatorBool n)
    | none => true

/-! ## Block-indicator scanners

`scanBlockEntryIx` (`-`), `scanKeyIx` (`?`), `scanValueIx` (`:`).
All three carry the legacy tab-in-indentation check (§6.1 [187] hardening —
`-` landed in Step 5b.2, `?` and `:` with DOCS item 31, which found that the
whitespace in front of a block indicator was only checked for the `-`).  DOCS
item 32 added `:`'s second reading, `tabInLineIndent`: when the whole line in
front of the `:` is whitespace there is no key on it, so the run IS
`[63] s-indent(n)` — the same verdict, taken from the line rather than from
where a key happens to have been recorded. -/

/-- Look back through trailing `.placeholder` reservation slots to find
    the last real token value (indexed twin of
    `L4YAML.Scanner.lastRealTokenVal?`). Returns `none` if the stream
    contains no real token yet. -/
def lastRealTokenValIx? {input : String} (ts : Indexed.TokenStream input) :
    Option YamlToken :=
  let arr := ts.tokens
  if arr.size > 0 then
    let lastIdx := arr.size - 1
    let tok1 := arr[lastIdx]!.token
    if tok1 == YamlToken.placeholder && lastIdx > 0 then
      let tok2 := arr[lastIdx - 1]!.token
      if tok2 == YamlToken.placeholder && lastIdx > 1 then
        some arr[lastIdx - 2]!.token
      else some tok2
    else some tok1
  else none

/-- Index of the token `lastRealTokenValIx?` reads (indexed twin of
    `L4YAML.Scanner.lastRealTokenIdx?`). -/
def lastRealTokenIdxIx? {input : String} (ts : Indexed.TokenStream input) :
    Option Nat :=
  let arr := ts.tokens
  if arr.size > 0 then
    let lastIdx := arr.size - 1
    if arr[lastIdx]!.token == YamlToken.placeholder && lastIdx > 0 then
      if arr[lastIdx - 1]!.token == YamlToken.placeholder && lastIdx > 1 then
        some (lastIdx - 2)
      else some (lastIdx - 1)
    else some lastIdx
  else none

/-- The real token *before* the one `lastRealTokenValIx?` reads (indexed twin of
    `L4YAML.Scanner.penultRealTokenVal?`). -/
def penultRealTokenValIx? {input : String} (ts : Indexed.TokenStream input) :
    Option YamlToken :=
  match lastRealTokenIdxIx? ts with
  | some i => lastRealTokenValIx? { tokens := ts.tokens.extract 0 i }
  | none => none

/-- Trailing run of node-property tokens, most recent first (indexed twin of
    `L4YAML.Scanner.trailingPropertyRun`). -/
def trailingPropertyRunIx {input : String} (ts : Indexed.TokenStream input) :
    List YamlToken :=
  match lastRealTokenValIx? ts with
  | some t1 =>
    if t1.isNodeProperty then
      match penultRealTokenValIx? ts with
      | some t2 => if t2.isNodeProperty then [t1, t2] else [t1]
      | none => [t1]
    else []
  | none => []

/-- The last real token itself, not just its value (indexed twin of
    `L4YAML.Scanner.lastRealToken?`). -/
def lastRealTokenIx? {input : String} (ts : Indexed.TokenStream input) :
    Option (Indexed.IxToken input) :=
  let arr := ts.tokens
  if arr.size > 0 then
    let lastIdx := arr.size - 1
    let tok1 := arr[lastIdx]!
    if tok1.token == YamlToken.placeholder && lastIdx > 0 then
      let tok2 := arr[lastIdx - 1]!
      if tok2.token == YamlToken.placeholder && lastIdx > 1 then
        some arr[lastIdx - 2]!
      else some tok2
    else some tok1
  else none

/-- Indexed twin of `L4YAML.Scanner.penultRealToken?`. -/
def penultRealTokenIx? {input : String} (ts : Indexed.TokenStream input) :
    Option (Indexed.IxToken input) :=
  match lastRealTokenIdxIx? ts with
  | some i => lastRealTokenIx? { tokens := ts.tokens.extract 0 i }
  | none => none

/-- The trailing property run truncated at a line change (indexed twin of
    `L4YAML.Scanner.trailingPropertyRunOnLine`; see it for why a same-line run
    is a sound reading in block context). -/
def trailingPropertyRunOnLineIx {input : String} (ts : Indexed.TokenStream input)
    (line : Nat) : List YamlToken :=
  match lastRealTokenIx? ts with
  | some t1 =>
    if t1.token.isNodeProperty && t1.start.line == line then
      match penultRealTokenIx? ts with
      | some t2 =>
        if t2.token.isNodeProperty && t2.start.line == line then [t1.token, t2.token]
        else [t1.token]
      | none => [t1.token]
    else []
  | none => []

/-- Indexed twin of `L4YAML.Scanner.lastTokenIsNodePropertyOnLine`. -/
def lastTokenIsNodePropertyOnLineIx {input : String} (ts : Indexed.TokenStream input)
    (line : Nat) : Bool :=
  match lastRealTokenIx? ts with
  | some t => t.token.isNodeProperty && t.start.line == line
  | none => false

/-- Indexed twin of `L4YAML.Scanner.prevRealIdx?`. -/
def prevRealIdxIx? {input : String} (ts : Indexed.TokenStream input) :
    Nat → Option Nat
  | 0 => none
  | i + 1 =>
    if ts.tokens[i]!.token == .placeholder then prevRealIdxIx? ts i else some i

/-- Indexed twin of `L4YAML.Scanner.slotHolderIdx?`. -/
@[yaml_spec "6.9" 96 "c-ns-properties"]
def slotHolderIdxIx? {input : String} (ts : Indexed.TokenStream input) : Option Nat :=
  match prevRealIdxIx? ts ts.tokens.size with
  | none => none
  | some i =>
    if ts.tokens[i]!.token.isNodeProperty then
      match prevRealIdxIx? ts i with
      | none => none
      | some j =>
        if ts.tokens[j]!.token.isNodeProperty then prevRealIdxIx? ts j else some j
    else some i

/-- Indexed twin of `L4YAML.Scanner.nodeSlotAwaited`. -/
@[yaml_spec "8.2.2" 187 "l+block-mapping",
  yaml_spec "8.2.1" 183 "l+block-sequence"]
def nodeSlotAwaitedIx {input : String} (ts : Indexed.TokenStream input) : Bool :=
  match slotHolderIdxIx? ts with
  | some i => ts.tokens[i]!.token.offersNodeSlot
  | none => false

/-- Indexed twin of `L4YAML.Scanner.sameIndentSequenceOpenLoop`. -/
@[yaml_spec "8.2.1" 183 "l+block-sequence"]
def sameIndentSequenceOpenLoopIx {input : String} (ts : Indexed.TokenStream input)
    (c : Int) : Nat → Bool
  | 0 => false
  | j + 1 =>
    let t := ts.tokens[j]!
    if t.token == .blockEntry && (t.start.col : Int) == c then true
    else if (t.token == .key || t.token == .value) && (t.start.col : Int) <= c then false
    else sameIndentSequenceOpenLoopIx ts c j

/-- Indexed twin of `L4YAML.Scanner.sameIndentSequenceOpen`. -/
@[yaml_spec "8.2.1" 183 "l+block-sequence"]
def sameIndentSequenceOpenIx {input : String} (ts : Indexed.TokenStream input)
    (c : Int) : Bool :=
  sameIndentSequenceOpenLoopIx ts c ts.tokens.size

/-- Indexed twin of `L4YAML.Scanner.atMappingIndent`. -/
def atMappingIndentIx {input : String} (s : ScannerStateIx input) : Bool :=
  match s.indents.back? with
  | some top => !top.isSequence && ((s.cursor.pos.col : Int) == top.column)
  | none => false

/-- Indexed twin of `L4YAML.Scanner.scanBlockEntryValidate`. -/
@[yaml_spec "9.2" 211 "l-yaml-stream",
  yaml_spec "8.2.1" 183 "l+block-sequence",
  yaml_spec "8.2.1" 185 "s-l+block-indented"]
def scanBlockEntryValidateIx {input : String} (s : ScannerStateIx input) :
    Except ScanError Unit :=
  if atMappingIndentIx s && !nodeSlotAwaitedIx s.tokens
      && !sameIndentSequenceOpenIx s.tokens (s.cursor.pos.col : Int) then
    .error (.invalidBareDocument s.cursor.pos.line s.cursor.pos.col)
  else
    .ok ()

/-- Scan `-` block-entry indicator.

    Throws `tabInIndentation` if a tab appears in the contiguous
    whitespace immediately before the cursor — `skipToContent` runs
    in same-line continuations consume tabs without checking, so this
    backward scan catches tabs that slipped through as indentation
    for this block entry (handles `-\t-`, `- \t-`, `-\t -`, etc.). -/
def scanBlockEntryIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  if !s.inFlow then
    -- Full `else`-chain, for the reason `scanBlockEntry` gives: with a check
    -- after them the statement form desugars through `__do_jp` join points.
    if s.hasTabInPrecedingWhitespace then
      throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
    -- Item 48: mirror of the legacy same-line check — see `scanBlockEntry`.
    else if s.implicitValueLine == some s.cursor.pos.line
        || lastTokenIsNodePropertyOnLineIx s.tokens s.cursor.pos.line
        || s.markerOnLine then
      throw (.sameLineBlockCollection s.cursor.pos.line s.cursor.pos.col)
    -- §9.2 [211] (item 134): mirror of the legacy check — see
    -- `scanBlockEntryValidate`.
    else
      scanBlockEntryValidateIx s
  let s := if !s.inFlow then pushSequenceIndentIx s s.cursor.pos.col else s
  let s := s.emit YamlToken.blockEntry
  let s := s.advance
  .ok { s with simpleKeyAllowed := true }

/-- Indexed twin of `L4YAML.Scanner.atSequenceIndent`. -/
def atSequenceIndentIx {input : String} (s : ScannerStateIx input) : Bool :=
  match s.indents.back? with
  | some top => top.isSequence && ((s.cursor.pos.col : Int) == top.column)
  | none => false

/-- Indexed twin of `L4YAML.Scanner.scanKeyValidate`. -/
@[yaml_spec "8.2.2"]
def scanKeyValidateIx {input : String} (s : ScannerStateIx input) :
    Except ScanError Unit := do
  if s.hasTabInPrecedingWhitespace then
    throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
  -- Item 48: mirror of the legacy same-line check — see `scanKey`.
  if s.implicitValueLine == some s.cursor.pos.line
      || lastTokenIsNodePropertyOnLineIx s.tokens s.cursor.pos.line
      || s.markerOnLine then
    throw (.sameLineBlockCollection s.cursor.pos.line s.cursor.pos.col)
  -- §8.2.1: mirror of the legacy check — see `scanKey`.
  if atSequenceIndentIx s then
    throw (.trailingContent s.cursor.pos.line s.cursor.pos.col)

/-- Scan `?` explicit-key indicator.

    Throws `tabInIndentation` if a tab appears in the contiguous whitespace
    immediately before the `?` — in block context the indicator stands directly
    after `[63] s-indent(n)`, which is spaces only — or if a tab character
    immediately follows it, which would be indentation for the key content
    (§6.1) — or `trailingContent` if the `?` stands at a block sequence's own
    indent (§8.2.1, `atSequenceIndentIx`). -/
def scanKeyIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  if !s.inFlow then
    scanKeyValidateIx s
  let s := if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s
  let line := s.cursor.pos.line
  let col := s.cursor.pos.col
  let s := s.emit YamlToken.key
  let s := s.advance
  if !s.inFlow then
    if let some '\t' := s.peek? then
      throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
  .ok { s with simpleKeyAllowed := true,
                explicitKeyLine := some line,
                explicitKeyCol := (col : Int),
                simpleKey := { cursor := IxCursor.start input },
                pendingKeys := if s.inFlow then s.pendingKeys
                  else s.pendingKeys.set! (s.indents.size - 1) (some line) }

/-- Clear a spurious simple-key when an explicit `?` key is pending.
    Pure state transformation — never modifies the token array.

    Indexed analogue of `L4YAML.Scanner.scanValueClearKey`.
    See `Scanner/SimpleKey.lean` for the case analysis. -/
@[yaml_spec "8.2.2"]
def scanValueClearKeyIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  match s.explicitKeyLine with
  | some ekLine =>
    if s.simpleKey.possible
        && s.simpleKey.cursor.pos.offset == s.cursor.pos.offset
        && s.cursor.pos.line != ekLine then
      { s with simpleKey := { cursor := IxCursor.start input } }
    else if s.simpleKey.possible
        && s.simpleKey.cursor.pos.line == ekLine
        && s.cursor.pos.line != ekLine && !s.inFlow then
      { s with simpleKey := { cursor := IxCursor.start input } }
    else s
  | none => s

/-- Validate pre-conditions for `:` as a value indicator.
    Returns `Unit` on success, throws on violation. Does **not**
    modify the scanner state — only inspects it.

    Indexed analogue of `L4YAML.Scanner.scanValueValidate`. -/
@[yaml_spec "8.2.2"]
def scanValueValidateIx {input : String} (s : ScannerStateIx input) :
    Except ScanError Unit := do
  -- §7.4: block-context multiline implicit key
  if s.simpleKey.possible && !s.inFlow
      && s.simpleKey.cursor.pos.line != s.cursor.pos.line then
    throw (.invalidImplicitKey s.cursor.pos.line)
  -- §7.4.2: flow-sequence multiline implicit key
  if s.simpleKey.possible && s.isInFlowSequence && s.explicitKeyLine.isNone
      && s.simpleKey.endLine != s.cursor.pos.line then
    throw (.invalidImplicitKey s.cursor.pos.line)
  -- §8.2.1: key at same indent as block sequence
  if s.simpleKey.possible && !s.inFlow then
    let keyCol : Int := s.simpleKey.cursor.pos.col
    if keyCol <= s.currentIndent then
      if let some top := s.indents.back? then
        if top.isSequence && keyCol == top.column then
          throw (.trailingContent s.simpleKey.cursor.pos.line s.simpleKey.cursor.pos.col)
  -- T833: missing comma in flow mapping (item 9r: line-independent).
  -- Mirrors the legacy strictening (`Scanner/SimpleKey.lean`): the
  -- reservation at `simpleKey.tokenIndex` is the entry's start, and a
  -- `.value` in the slot directly below it means the previous entry was
  -- already complete (`k: v`) — this `:` continues it with no separator,
  -- invalid whatever the line. Rejects `[a: b: c]`, `{a: : b}`, `[: :]`,
  -- `[a: &x : b]` and their neighbours at the scanner, closing the
  -- deliberate legacy↔indexed divergence pinned in
  -- `Tests/Guards/Proofs/ScannerFlowPropsColon.lean` §4.
  if s.simpleKey.possible && s.inFlow && s.simpleKey.tokenIndex > 0 then
    if let some prevTok := s.tokens.tokens[s.simpleKey.tokenIndex - 1]? then
      if prevTok.token == .value then
        throw (.invalidFlowEntry s.cursor.pos.line s.cursor.pos.col)
  -- §8.2.2 [197]: explicit value `:` must be at mapping indent level
  if let some ekLine := s.explicitKeyLine then
    if !s.simpleKey.possible && !s.inFlow then
      if s.cursor.pos.line == ekLine then
        throw (.sameLineExplicitValue s.cursor.pos.line s.cursor.pos.col)
      else if (s.cursor.pos.col : Int) != s.currentIndent then
        throw (.misindentedExplicitValue s.cursor.pos.line s.cursor.pos.col s.currentIndent)
  -- Item 48: mirror of the legacy same-line checks — see `scanValueValidate`.
  if !s.inFlow && s.implicitValueLine == some s.cursor.pos.line then
    throw (.nestedMappingOnLine s.cursor.pos.line s.cursor.pos.col)
  if !s.inFlow && s.markerOnLine then
    throw (.contentOnDocumentStartLine s.cursor.pos.line s.cursor.pos.col)
  -- §7.4.2 [147]: mirror of the legacy glued-collection-value refusal.
  if flowGluedCollectionValueIx s then
    throw (.unseparatedValue s.cursor.pos.line s.cursor.pos.col)

/-- Resolve a pending simple key by overwriting placeholders at
    `simpleKey.tokenIndex`. Pure state update on the token stream
    and indent stack. -/
def scanValuePrepareIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  if s.simpleKey.possible then
    let idx := s.simpleKey.tokenIndex
    let sk := s.simpleKey.cursor
    if !s.inFlow then
      if (s.simpleKey.cursor.pos.col : Int) > s.currentIndent then
        let s := s.overwriteAtCursor idx sk YamlToken.blockMappingStart
        let s := s.overwriteAtCursor (idx + 1) sk YamlToken.key
        { s with
            indents := s.indents.push { column := (s.simpleKey.cursor.pos.col : Int),
                                         isSequence := false },
            pendingKeys := s.pendingKeys.push none,
            simpleKey := { cursor := IxCursor.start input } }
      else
        let s := s.overwriteAtCursor (idx + 1) sk YamlToken.key
        { s with simpleKey := { cursor := IxCursor.start input } }
    else
      let s := s.overwriteAtCursor (idx + 1) sk YamlToken.key
      { s with simpleKey := { cursor := IxCursor.start input } }
  else if s.explicitKeyLine.isSome then
    { s with simpleKey := { cursor := IxCursor.start input } }
  else
    if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s

/-- §6.1 for the `:` indicator: the whitespace run in front of the ENTRY must
    carry no tab, and the entry starts at the implicit KEY when there is one —
    the run between key and `:` is `[154]`'s own trailing `s-separate-in-line?`,
    where a tab is legal.  With no key (`[192]`'s `e-node`, or the explicit value) the entry starts at the `:` and its own run is the indentation.

    Indexed analogue of `L4YAML.Scanner.scanValueIndentTabCheck`; see there for
    why following the entry start is what keeps `a:⏎␣␣→[1, 2]` legal. -/
@[yaml_spec "6.1", yaml_spec "8.2.2" 187 "l+block-mapping"]
def scanValueIndentTabCheckIx {input : String} (s : ScannerStateIx input) :
    Except ScanError Unit :=
  if s.inFlow then .ok ()
  else if s.tabInLineIndent then
    throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
  else if s.simpleKey.possible then
    if ScannerStateIx.hasTabInPrecedingWhitespaceLoop
        input s.simpleKey.cursor.pos.offset s.simpleKey.cursor.pos.offset then
      throw (.tabInIndentation s.simpleKey.cursor.pos.line s.simpleKey.cursor.pos.col)
    else .ok ()
  else if s.hasTabInPrecedingWhitespace then
    throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
  else .ok ()

/-- §6.1 tab-after-`:` check: if the explicit value was at or below
    the current indent level and is in block context, the character
    immediately after the consumed `:` must not be a tab.

    Indexed analogue of `L4YAML.Scanner.scanValueTabCheck`. -/
@[yaml_spec "6.1"]
def scanValueTabCheckIx {input : String} (origCol : Int) (origIndent : Int)
    (s_adv : ScannerStateIx input) : Except ScanError Unit :=
  if origCol ≤ origIndent && !s_adv.inFlow then
    if let some '\t' := s_adv.peek? then
      throw (.tabInIndentation s_adv.cursor.pos.line s_adv.cursor.pos.col)
    else .ok ()
  else .ok ()

/-- Step 4 (item 335): does the pending explicit key survive this `:`?  In flow
    never; in block a dead register has nothing to close, and a live one
    survives an implicit `:` deeper than the key's column (the `:` is inside the
    key's own content).  Named so proofs can split on it by name. -/
def scanValueKeySurvivesIx {input : String} (s s_kc : ScannerStateIx input) : Bool :=
  let explicitValue : Bool :=
    s_kc.explicitKeyLine.isSome && !s_kc.simpleKey.possible
      && (s.inFlow || (s.cursor.pos.col : Int) == s_kc.explicitKeyCol)
  !s.inFlow && (!s_kc.explicitKeyLine.isSome || !explicitValue
    && (if s_kc.simpleKey.possible then (s_kc.simpleKey.cursor.pos.col : Int)
        else (s.cursor.pos.col : Int)) > s_kc.explicitKeyCol)

/-- Scan `:` value indicator. Mirrors the legacy five-stage chain
    `scanValueClearKey` / `scanValueValidate` / `scanValueIndentTabCheck` /
    `scanValuePrepare` / `scanValueTabCheck` so each stage carries a single
    provable property. -/
@[yaml_spec "8.2.2" 6 "c-mapping-value"]
def scanValueIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  let s_kc := scanValueClearKeyIx s
  scanValueValidateIx s_kc
  scanValueIndentTabCheckIx s_kc
  let s_prepared := scanValuePrepareIx s_kc
  let s_with_token := s_prepared.emit YamlToken.value
  let s_after_advance := s_with_token.advance
  scanValueTabCheckIx (s.cursor.pos.col : Int) s.currentIndent s_after_advance
  -- Item 48: mirror of the legacy implicit-value recording and the pending
  -- `?`'s survival through its key's own compact entries — see `scanValue`.
  -- Item 51: the explicit value line is selected only AT the key's column
  -- (`[197]`'s `s-indent(n)` is exact); any other live column stamps, and
  -- a deeper entry (keyed or empty-key) keeps the `?` alive — see `scanValue`.
  let explicitValue : Bool :=
    s_kc.explicitKeyLine.isSome && !s_kc.simpleKey.possible
      && (s.inFlow || (s.cursor.pos.col : Int) == s_kc.explicitKeyCol)
  let ivl : Option Nat :=
    if s.inFlow || explicitValue then
      s_after_advance.implicitValueLine
    else some s.cursor.pos.line
  let survives : Bool := scanValueKeySurvivesIx s s_kc
  let settle : Array (Option Nat) × Option Nat × Int :=
    if s.inFlow then (s_after_advance.pendingKeys, none, -1)
    else if survives then
      (s_after_advance.pendingKeys, s_kc.explicitKeyLine,
        if s_kc.explicitKeyLine.isSome then s_kc.explicitKeyCol else -1)
    else PendingKeys.close s_after_advance.indentColumns s_after_advance.pendingKeys s_kc.explicitKeyCol
  .ok { s_after_advance with
        simpleKeyAllowed := true
        explicitKeyLine := settle.2.1
        explicitKeyCol := settle.2.2
        pendingKeys := settle.1
        implicitValueLine := ivl }

/-! ## Document-marker scanners -/

/-- Scan `---` document-start marker. -/
def scanDocumentStartIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := unwindIndentsIx s (-1)
  let s := { s with simpleKey := { cursor := IxCursor.start input } }
  let s := s.emit YamlToken.documentStart
  let s := s.advanceN 3
  { s with
      simpleKeyAllowed := true,
      allowDirectives := false,
      seenYamlDirective := false,
      directivesPresent := false,
      documentEverStarted := true,
      definedAnchors := #[],
      -- Item 299: the marker's line, for §9.1.1's three block checks.
      docStartLine := some s.cursor.pos.line,
      -- Item 317: the marker ends the `?` frame and its register (see `scanDocumentStart`).
      explicitKeyLine := none,
      explicitKeyCol := -1 }

/-- Scan `...` document-end marker. -/
def scanDocumentEndIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  if s.directivesPresent then
    throw (.directiveWithoutDocument s.cursor.pos.line)
  let s := unwindIndentsIx s (-1)
  let s := { s with simpleKey := { cursor := IxCursor.start input } }
  let s := s.emit YamlToken.documentEnd
  let s := s.advanceN 3
  let s := { s with
      simpleKeyAllowed := true,
      allowDirectives := true,
      directivesPresent := false,
      definedAnchors := #[],
      -- Item 317: as at `scanDocumentStartIx` — the register dies with the frame.
      explicitKeyLine := none,
      explicitKeyCol := -1 }
  let probe := skipDocEndWhitespaceIx s.cursor (input.utf8ByteSize + 1)
  match probe.peek? with
  | none => pure ()
  | some '#' => pure ()
  | some ch =>
    if isLineBreakBool ch then pure ()
    else throw (.trailingContentAfterDocEnd probe.pos.line probe.pos.col)
  .ok s

/-! ## Directives -/

/-- Scan a `%YAML major.minor` directive. The caller supplies
    `hStart : startPos.offset ≤ cAfterWS.pos.offset` so that the
    constructed `versionDirective` token's bound is discharged
    without a runtime check (Step 5b.1a). -/
def scanYamlDirectiveIx {input : String} (s : ScannerStateIx input)
    (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) :
    Except ScanError (ScannerStateIx input) := do
  if s.seenYamlDirective then
    throw (.duplicateYamlDirective s.cursor.pos.line)
  let fuelM := input.utf8ByteSize - cAfterWS.pos.offset
  let rMaj := collectVersionMajorLoopIx cAfterWS "" fuelM
  let major := rMaj.1
  let cAfterDot := rMaj.2
  let fuelN := input.utf8ByteSize - cAfterDot.pos.offset
  let rMin := collectVersionMinorLoopIx cAfterDot "" fuelN
  let minor := rMin.1
  let cAfterVer := rMin.2
  let colBeforeWs := cAfterVer.pos.col
  let cAfterTW := skipWhitespace cAfterVer
  -- Trailing-content validation (mirrors legacy `scanYamlDirective`):
  -- after the version only whitespace, a separated comment, a line
  -- break, or EOF may follow.
  match cAfterTW.peek? with
  | some '#' =>
    if cAfterTW.pos.col == colBeforeWs then
      throw (.directiveTrailingContent cAfterTW.pos.line cAfterTW.pos.col)
  | some ch =>
    if !isLineBreakBool ch then
      throw (.directiveTrailingContent cAfterTW.pos.line cAfterTW.pos.col)
  | none => pure ()
  if major.isEmpty || minor.isEmpty then
    throw (.directiveTrailingContent cAfterTW.pos.line cAfterTW.pos.col)
  let sAfter : ScannerStateIx input := { s with cursor := cAfterTW }
  let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
    show startPos.offset ≤ cAfterTW.pos.offset
    have h2 : cAfterWS.pos.offset ≤ rMaj.2.pos.offset :=
      collectVersionMajorLoopIx_offset_monotonic cAfterWS "" fuelM
    have h3 : cAfterDot.pos.offset ≤ rMin.2.pos.offset :=
      collectVersionMinorLoopIx_offset_monotonic cAfterDot "" fuelN
    have h4 : cAfterVer.pos.offset ≤ cAfterTW.pos.offset :=
      skipWhitespace_offset_monotonic cAfterVer
    exact Nat.le_trans hStart (Nat.le_trans h2 (Nat.le_trans h3 h4))
  let sEmit := sAfter.emitAt startPos
    (YamlToken.versionDirective major.toNat! minor.toNat!) hBound
  .ok { sEmit with seenYamlDirective := true, directivesPresent := true }

/-- Scan a `%TAG !handle! prefix` directive. As with
    `scanYamlDirectiveIx`, the caller supplies the start-pos bound. -/
def scanTagDirectiveIx {input : String} (s : ScannerStateIx input)
    (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) :
    Except ScanError (ScannerStateIx input) := do
  let fuelH := input.utf8ByteSize - cAfterWS.pos.offset
  let r := collectTagHandleDirectiveLoopIx cAfterWS "" fuelH
  let handle := r.1
  let cAfterHandle := r.2
  -- [89] c-tag-handle (twin of `scanTagDirective`)
  if !isTagHandleShaped handle then
    throw (.invalidTagHandle handle cAfterWS.pos.line cAfterWS.pos.col)
  let cAfterWS2 := skipWhitespace cAfterHandle
  let fuelP := input.utf8ByteSize - cAfterWS2.pos.offset
  let r2 := collectTagPrefixLoopIx cAfterWS2 "" fuelP
  let tagPrefix := r2.1
  let cAfterPrefix := r2.2
  let colBeforeWs := cAfterPrefix.pos.col
  let cAfterTW := skipWhitespace cAfterPrefix
  -- Trailing-content validation (mirrors legacy `scanTagDirective`).
  match cAfterTW.peek? with
  | some '#' =>
    if cAfterTW.pos.col == colBeforeWs then
      throw (.directiveTrailingContent cAfterTW.pos.line cAfterTW.pos.col)
  | some ch =>
    if !isLineBreakBool ch then
      throw (.directiveTrailingContent cAfterTW.pos.line cAfterTW.pos.col)
  | none => pure ()
  let sAfter : ScannerStateIx input := { s with cursor := cAfterTW }
  let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
    show startPos.offset ≤ cAfterTW.pos.offset
    have h2 : cAfterWS.pos.offset ≤ cAfterHandle.pos.offset :=
      collectTagHandleDirectiveLoopIx_offset_monotonic cAfterWS "" fuelH
    have h3 : cAfterHandle.pos.offset ≤ cAfterWS2.pos.offset :=
      skipWhitespace_offset_monotonic cAfterHandle
    have h4 : cAfterWS2.pos.offset ≤ r2.2.pos.offset :=
      collectTagPrefixLoopIx_offset_monotonic cAfterWS2 "" fuelP
    have h5 : cAfterPrefix.pos.offset ≤ cAfterTW.pos.offset :=
      skipWhitespace_offset_monotonic cAfterPrefix
    exact Nat.le_trans hStart
      (Nat.le_trans h2 (Nat.le_trans h3 (Nat.le_trans h4 h5)))
  let sEmit := sAfter.emitAt startPos
    (YamlToken.tagDirective handle tagPrefix) hBound
  .ok { sEmit with directivesPresent := true }

/-- Scan a `%`-introduced directive (YAML/TAG/reserved). -/
def scanDirectiveIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) :=
  if !s.allowDirectives then
    .error (.directiveAfterContent s.cursor.pos.line)
  else
    let startPos := s.cursor.pos
    let sAdv := s.advance
    let fuel := input.utf8ByteSize - sAdv.cursor.pos.offset
    let rName := collectDirectiveNameLoopIx sAdv.cursor "" fuel
    let name := rName.1
    let cAfterName := rName.2
    let cAfterWS := skipWhitespace cAfterName
    have hStart : startPos.offset ≤ cAfterWS.pos.offset := by
      show s.cursor.pos.offset ≤ cAfterWS.pos.offset
      have h1 : s.cursor.pos.offset ≤ sAdv.cursor.pos.offset :=
        IxCursor.advance_offset_monotonic s.cursor
      have h2 : sAdv.cursor.pos.offset ≤ cAfterName.pos.offset :=
        collectDirectiveNameLoopIx_offset_monotonic sAdv.cursor "" fuel
      have h3 : cAfterName.pos.offset ≤ cAfterWS.pos.offset :=
        skipWhitespace_offset_monotonic cAfterName
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    if name == "YAML" then
      match scanYamlDirectiveIx ({ sAdv with cursor := cAfterName } : ScannerStateIx input)
        cAfterWS startPos hStart with
      | .ok s' => .ok { s' with cursor := skipToEndOfLineIx s'.cursor }
      | .error e => .error e
    else if name == "TAG" then
      match scanTagDirectiveIx ({ sAdv with cursor := cAfterName } : ScannerStateIx input)
        cAfterWS startPos hStart with
      | .ok s' => .ok { s' with cursor := skipToEndOfLineIx s'.cursor }
      | .error e => .error e
    else
      -- [83] ns-reserved-directive: skip its free-form parameters to end
      -- of line and record the pending directive (mirrors legacy).
      .ok ({ sAdv with
              cursor := skipToEndOfLineIx cAfterWS,
              directivesPresent := true } : ScannerStateIx input)

/-! ## Node properties — anchors, aliases, tags -/

/-- Scan `&name` (anchor) or `*name` (alias). -/
def scanAnchorOrAliasIx {input : String} (s : ScannerStateIx input)
    (isAnchor : Bool) : Except ScanError (ScannerStateIx input) :=
  let startPos := s.cursor.pos
  let sAdv := s.advance
  let fuel := input.utf8ByteSize - sAdv.cursor.pos.offset
  let r := collectAnchorNameLoopIx sAdv.cursor "" fuel
  let name := r.1
  let cAfterName := r.2
  if name.isEmpty then
    .error (.emptyAnchorName startPos.line startPos.col)
  else
    let token := if isAnchor then YamlToken.anchor name else YamlToken.alias name
    let sAfter : ScannerStateIx input := { sAdv with cursor := cAfterName }
    let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
      show s.cursor.pos.offset ≤ r.2.pos.offset
      have h1 : s.cursor.pos.offset ≤ sAdv.cursor.pos.offset :=
        IxCursor.advance_offset_monotonic s.cursor
      have h2 : sAdv.cursor.pos.offset ≤ r.2.pos.offset :=
        collectAnchorNameLoopIx_offset_monotonic sAdv.cursor "" fuel
      exact Nat.le_trans h1 h2
    let sEmit := sAfter.emitAt startPos token hBound
    let anchors :=
      if isAnchor then sEmit.definedAnchors.push name
      else sEmit.definedAnchors
    .ok { sEmit with simpleKeyAllowed := false, definedAnchors := anchors }

/-- Scan a tag property (`!`, `!!suffix`, `!handle!suffix`, `!<uri>`). -/
def scanTagIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) :=
  let startPos := s.cursor.pos
  let sAdv := s.advance
  match sAdv.peek? with
  | some '<' =>
    let s2 := sAdv.advance
    let fuel := input.utf8ByteSize - s2.cursor.pos.offset
    let rVerb := collectVerbatimTagLoopIx s2.cursor "" fuel
    let uri := rVerb.1
    let foundClose := rVerb.2.1
    let cAfter := rVerb.2.2
    if !foundClose then
      .error (.unterminatedVerbatimTag startPos.line startPos.col)
    else if uri.isEmpty then
      .error (.emptyVerbatimTagURI startPos.line startPos.col)
    else
      let sAfter : ScannerStateIx input := { s2 with cursor := cAfter }
      let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
        show s.cursor.pos.offset ≤ rVerb.2.2.pos.offset
        have h1 : s.cursor.pos.offset ≤ sAdv.cursor.pos.offset :=
          IxCursor.advance_offset_monotonic s.cursor
        have h2 : sAdv.cursor.pos.offset ≤ s2.cursor.pos.offset :=
          IxCursor.advance_offset_monotonic sAdv.cursor
        have h3 : s2.cursor.pos.offset ≤ rVerb.2.2.pos.offset :=
          collectVerbatimTagLoopIx_offset_monotonic s2.cursor "" fuel
        exact Nat.le_trans h1 (Nat.le_trans h2 h3)
      let sEmit := sAfter.emitAt startPos (YamlToken.tag "" uri) hBound
      .ok { sEmit with simpleKeyAllowed := false }
  | some '!' =>
    let s2 := sAdv.advance
    let fuel := input.utf8ByteSize - s2.cursor.pos.offset
    let rSec := collectTagSuffixLoopIx s2.cursor "" fuel
    let suffix := rSec.1
    let cAfter := rSec.2
    let sAfter : ScannerStateIx input := { s2 with cursor := cAfter }
    let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
      show s.cursor.pos.offset ≤ rSec.2.pos.offset
      have h1 : s.cursor.pos.offset ≤ sAdv.cursor.pos.offset :=
        IxCursor.advance_offset_monotonic s.cursor
      have h2 : sAdv.cursor.pos.offset ≤ s2.cursor.pos.offset :=
        IxCursor.advance_offset_monotonic sAdv.cursor
      have h3 : s2.cursor.pos.offset ≤ rSec.2.pos.offset :=
        collectTagSuffixLoopIx_offset_monotonic s2.cursor "" fuel
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    let sEmit := sAfter.emitAt startPos (YamlToken.tag "!!" suffix) hBound
    .ok { sEmit with simpleKeyAllowed := false }
  | _ =>
    let fuel := input.utf8ByteSize - sAdv.cursor.pos.offset
    let r := collectTagHandleLoopIx sAdv.cursor "" fuel
    let chars := r.1
    let foundBang := r.2.1
    let cAfterHandle := r.2.2
    let (handle, suffix0) :=
      if foundBang then ("!" ++ chars ++ "!", "") else ("!", chars)
    let rSuf :=
      let fuel' := input.utf8ByteSize - cAfterHandle.pos.offset
      collectTagSuffixLoopIx cAfterHandle suffix0 fuel'
    let suffix := rSuf.1
    let cAfter := rSuf.2
    let sAfter : ScannerStateIx input := { sAdv with cursor := cAfter }
    let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
      show s.cursor.pos.offset ≤ rSuf.2.pos.offset
      have h1 : s.cursor.pos.offset ≤ sAdv.cursor.pos.offset :=
        IxCursor.advance_offset_monotonic s.cursor
      have h2 : sAdv.cursor.pos.offset ≤ cAfterHandle.pos.offset :=
        collectTagHandleLoopIx_offset_monotonic sAdv.cursor "" fuel
      have h3 : cAfterHandle.pos.offset ≤ rSuf.2.pos.offset :=
        collectTagSuffixLoopIx_offset_monotonic cAfterHandle suffix0 _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    let sEmit := sAfter.emitAt startPos (YamlToken.tag handle suffix) hBound
    .ok { sEmit with simpleKeyAllowed := false }

/-! ## Flow indicators -/

/-- Scan `[` flow-sequence start. -/
def scanFlowSequenceStartIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowSequenceStart
  let s := s.advance
  -- Item 98: the explicit-key stamp is per-flow-level state — save the outer
  -- pair and clear it for the interior; mirror of `scanFlowSequenceStart`.
  { s with
      flowLevel := s.flowLevel + 1,
      flowStack := s.flowStack.push true,
      simpleKeyStack := s.simpleKeyStack.push s.simpleKey,
      simpleKey := { cursor := IxCursor.start input },
      simpleKeyAllowed := true,
      explicitKeyStack := s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol),
      explicitKeyLine := none,
      explicitKeyCol := -1 }

/-- Scan `]` flow-sequence end. -/
def scanFlowSequenceEndIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowSequenceEnd
  let s := s.advance
  let restored := s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }
  -- Item 98: restore the outer explicit-key stamp — see `scanFlowSequenceStartIx`.
  let restoredEk := s.explicitKeyStack.back?.getD (none, -1)
  -- Item 47: the collection's interior breaks are the token's own — mirror of
  -- the legacy `scanFlowSequenceEnd`.
  { s with
      flowLevel := s.flowLevel - 1,
      flowStack := s.flowStack.pop,
      simpleKeyStack := s.simpleKeyStack.pop,
      simpleKey := restored,
      simpleKeyAllowed := false,
      needIndentCheck := false,
      explicitKeyLine := restoredEk.1,
      explicitKeyCol := restoredEk.2,
      explicitKeyStack := s.explicitKeyStack.pop }

/-- Scan `{` flow-mapping start. -/
def scanFlowMappingStartIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowMappingStart
  let s := s.advance
  -- Item 98: save + clear the explicit-key stamp — see `scanFlowSequenceStartIx`.
  { s with
      flowLevel := s.flowLevel + 1,
      flowStack := s.flowStack.push false,
      simpleKeyStack := s.simpleKeyStack.push s.simpleKey,
      simpleKey := { cursor := IxCursor.start input },
      simpleKeyAllowed := true,
      explicitKeyStack := s.explicitKeyStack.push (s.explicitKeyLine, s.explicitKeyCol),
      explicitKeyLine := none,
      explicitKeyCol := -1 }

/-- Scan `}` flow-mapping end. -/
def scanFlowMappingEndIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowMappingEnd
  let s := s.advance
  let restored := s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }
  -- Item 98: restore the outer explicit-key stamp — see `scanFlowSequenceStartIx`.
  let restoredEk := s.explicitKeyStack.back?.getD (none, -1)
  -- Item 47: interior breaks are the token's own — see `scanFlowSequenceEndIx`.
  { s with
      flowLevel := s.flowLevel - 1,
      flowStack := s.flowStack.pop,
      simpleKeyStack := s.simpleKeyStack.pop,
      simpleKey := restored,
      simpleKeyAllowed := false,
      needIndentCheck := false,
      explicitKeyLine := restoredEk.1,
      explicitKeyCol := restoredEk.2,
      explicitKeyStack := s.explicitKeyStack.pop }



/-- §6.9 [96]: does the property run ending at the cursor already carry an
    anchor?  (Indexed twin of `L4YAML.Scanner.propertyRunHasAnchor`; see its
    docstring for the two contexts in which token adjacency means "same
    node".) -/
def propertyRunHasAnchorIx {input : String} (s : ScannerStateIx input) : Bool :=
  (s.inFlow && (trailingPropertyRunIx s.tokens).any YamlToken.isAnchorProperty) ||
    (trailingPropertyRunOnLineIx s.tokens s.cursor.pos.line).any YamlToken.isAnchorProperty

/-- §6.9 [96]: does the property run ending at the cursor already carry a tag?
    (Indexed twin of `L4YAML.Scanner.propertyRunHasTag`.) -/
def propertyRunHasTagIx {input : String} (s : ScannerStateIx input) : Bool :=
  (s.inFlow && (trailingPropertyRunIx s.tokens).any YamlToken.isTagProperty) ||
    (trailingPropertyRunOnLineIx s.tokens s.cursor.pos.line).any YamlToken.isTagProperty

/-- §6.9 [96]: is the property run ending at the cursor already FULL — two
    tokens, which is all `[96]` derives?  (Indexed twin of
    `L4YAML.Scanner.propertyRunFull`; see its docstring for why the length
    decides alone in a flow while block context also asks the run's TAIL to
    share the cursor's line — a tail that closed on an earlier line may be a
    parent node's completed run, 9KAX's shape.) -/
def propertyRunFullIx {input : String} (s : ScannerStateIx input) : Bool :=
  match prevRealIdxIx? s.tokens s.tokens.tokens.size with
  | none => false
  | some i =>
    s.tokens.tokens[i]!.token.isNodeProperty &&
      (match prevRealIdxIx? s.tokens i with
       | none => false
       | some j =>
         s.tokens.tokens[j]!.token.isNodeProperty &&
           (s.inFlow ||
             (s.tokens.tokens[i]!.start.line == s.cursor.pos.line &&
              s.tokens.tokens[j]!.start.line == s.tokens.tokens[i]!.start.line)))

/-- §6.9 [104]: is the cursor directly after a node property?  (Indexed twin of
    `L4YAML.Scanner.lastTokenIsNodeProperty`.) -/
def lastTokenIsNodePropertyIx {input : String} (s : ScannerStateIx input) : Bool :=
  (s.inFlow &&
    (match lastRealTokenValIx? s.tokens with
     | some t => t.isNodeProperty
     | none => false)) ||
    lastTokenIsNodePropertyOnLineIx s.tokens s.cursor.pos.line

/-- §7.5 [161] (item 9f): the characters that may directly follow a node property
    or an alias.  (Indexed twin of `L4YAML.Scanner.propertyFollowerOk`; see it for
    why this one needs no `s.inFlow` gate.) -/
def propertyFollowerOkIx {input : String} (c : IxCursor input) : Bool :=
  match c.peek? with
  | none => true
  | some ch =>
    isWhiteSpaceBool ch || isLineBreakBool ch || ch == ',' || ch == ']' || ch == '}'

/-- `propertyFollowerOkIx` read off the state a property scan produced; vacuous on
    a failed scan.  (Twin of `L4YAML.Scanner.propertyScanFollowerOk`.) -/
def propertyScanFollowerOkIx {input : String}
    (r : Except ScanError (ScannerStateIx input)) : Bool :=
  match r with
  | .ok s' => propertyFollowerOkIx s'.cursor
  | .error _ => true

/-- Where an anchor or alias name ends, without emitting anything — the same
    `collectAnchorNameLoopIx` walk `scanAnchorOrAliasIx` runs.  (Twin of
    `L4YAML.Scanner.anchorNameEnd`.) -/
def anchorNameEndIx {input : String} (s : ScannerStateIx input) : IxCursor input :=
  (collectAnchorNameLoopIx s.advance.cursor ""
    (input.utf8ByteSize - s.advance.cursor.pos.offset)).2

/-- §7.4 [150] (item 9g): inside a flow collection, is the cursor at an entry
    boundary, where a `?` may open an `ns-flow-pair`?  (Indexed twin of
    `L4YAML.Scanner.flowKeyPredecessorOk`; see it for the derivation argument
    and for why the test rides on the dispatch condition.) -/
@[yaml_spec "7.4.1" 150 "ns-flow-pair(n,c)",
  yaml_spec "7.4.1" 138 "ns-s-flow-seq-entries(n,c)",
  yaml_spec "7.4.2" 141 "ns-s-flow-map-entries(n,c)"]
def flowKeyPredecessorOkIx {input : String} (s : ScannerStateIx input) : Bool :=
  !s.inFlow ||
    (match lastRealTokenValIx? s.tokens with
     | some t => t.opensFlowEntry
     | none => false)

/-- §7.4.1 [150] (item 9j): inside a flow collection, is the `?` followed by the
    `s-separate` its production requires?  (Indexed twin of
    `L4YAML.Scanner.flowKeyFollowerOk`; see it for the derivation argument.) -/
@[yaml_spec "7.4.1" 150 "ns-flow-pair(n,c)",
  yaml_spec "6.7" 81 "s-separate-lines(n)"]
def flowKeyFollowerOkIx {input : String} (s : ScannerStateIx input) : Bool :=
  !s.inFlow ||
    (match s.peekAt? 1 with
     | some n => isBlankBool n
     | none => true)

/-- Scan `,` flow entry separator. Mirrors `L4YAML.Scanner.scanFlowEntry`:
    emits `.flowEntry` and sets `simpleKeyAllowed := true` so the next
    item can start a fresh implicit key.

    Does **not** call `scanValuePrepareIx` — that is the `:` (value)
    boundary's job. A `,` does not retroactively confirm the pending
    simple key; any pending reservation slots stay as `.placeholder`
    and are stripped by `scanFilteredIx`. (Step 6f.0 removed an
    accidental `scanValuePrepareIx` call here that was overwriting
    `placeholder` slots with `.key` tokens after `[` / `,`, producing
    spurious `key` tokens in flow sequences with multiple entries.)

    §7.4: a leading comma after a flow-open indicator (`[`, `{`) or a
    consecutive comma is invalid; this raises `invalidFlowEntry`. -/
def scanFlowEntryIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  if let some lastTok := lastRealTokenValIx? s.tokens then
    if lastTok == YamlToken.flowSequenceStart
        || lastTok == YamlToken.flowMappingStart
        || lastTok == YamlToken.flowEntry then
      throw (.invalidFlowEntry s.cursor.pos.line s.cursor.pos.col)
  let s_with_token := s.emit YamlToken.flowEntry
  let s_after_advance := s_with_token.advance
  -- §7.4.1 [150] (item 9l): the `,` ENDS the explicit-key entry, so the `?`'s
  -- line no longer suppresses simple-key reservation — see `scanFlowEntry`.
  -- Item 9q: the pending simple key is dead here and clearing it is
  -- behaviour-preserving — see `scanFlowEntry` for the argument.
  .ok { s_after_advance with
        simpleKeyAllowed := true
        explicitKeyLine := none
        simpleKey := { possible := false } }

/-! ## Dispatcher

Mirrors `Scanner/Scanner.lean::scanNextToken_*` over `ScannerStateIx
input`. The function family is intentionally split into the same
five sub-dispatches as the legacy so that monotonicity proofs
remain tractable (≤ 7 branch points each). -/

/-- Preprocessing: skip whitespace/comments, unwind indents, save
    simple key, peek next character. Returns `none` at EOF. -/
def scanNextTokenIx_preprocess {input : String} (s : ScannerStateIx input) :
    Except ScanError (Option (ScannerStateIx input × Char)) :=
  -- §6.1 / §6.6 strictness: the cursor-level `skipToContent` has no
  -- error channel, so the legacy skip-time rejections (tab as
  -- indentation; `#` without preceding `s-separate-in-line`) are
  -- reproduced by a read-only walker over the same region (4EJS,
  -- Y79Y/003, 9JBA, CVW2, SU5Z).
  match skipToContentErrIx s.cursor s.inFlow s.currentIndent s.needIndentCheck with
  | some e => .error e
  | none =>
  let s := s.skipToContentS
  if !s.hasMore then .ok none
  else
    let savedIndentSize := s.indents.size
    let s := if !s.inFlow && s.needIndentCheck then
      let s' := unwindIndentsIx s s.cursor.pos.col
      { s' with needIndentCheck := false }
    else s
    if s.indents.size < savedIndentSize && (s.cursor.pos.col : Int) > s.currentIndent then
      .error (.trailingContent s.cursor.pos.line s.cursor.pos.col)
    else
      let s := saveSimpleKeyIx s
      let s := closeStaleExplicitKeyIx s
      match s.peek? with
      | none => .ok none
      | some c => .ok (some (s, c))

/-- Structural dispatch: under-indent guard, document markers,
    directives. Returns `some s'` if handled, `none` to fall through. -/
def scanNextTokenIx_dispatchStructural {input : String} (s : ScannerStateIx input)
    (c : Char) : Except ScanError (Option (ScannerStateIx input)) := do
  -- Item 50: `]`/`}` clear the same floor — the old exemption was an
  -- over-acceptance (see `scanNextToken_dispatchStructural`).
  if s.inFlow && s.currentIndent >= 0 && (s.cursor.pos.col : Int) <= s.currentIndent then
    throw (.underIndentedFlowContent s.cursor.pos.line s.cursor.pos.col)
  if s.cursor.pos.col == 0 && s.inFlow
      && (atDocumentStartIx s.cursor || atDocumentEndIx s.cursor) then
    throw (.documentMarkerInFlow s.cursor.pos.line)
  if s.cursor.pos.col == 0 && atDocumentStartIx s.cursor then
    return some (scanDocumentStartIx s)
  if s.cursor.pos.col == 0 && atDocumentEndIx s.cursor then
    let s' ← scanDocumentEndIx s
    return some s'
  if c == '%' && s.cursor.pos.col == 0 then
    let s' ← scanDirectiveIx s
    return some s'
  return none

/-- §7.4 [137]/[140]: flow-entry adjacency guard.  Indexed twin of
    `scanNextToken_checkFlowAdjacency`.  Inside a flow collection, a new
    node may not immediately follow a completed value
    (`YamlToken.completesFlowValue`) without a `,`/`:` separator or the
    matching close (`]`/`}`).  Called at the entry of
    `scanNextTokenIx_dispatchFlowIndicators`.

    Item 9d: the `:` exemption is conditional on `isValueCandidateIx` — a
    `:` that is not a value indicator falls through to content dispatch and
    starts a plain scalar, so it is a node start.  See the legacy docstring
    for the spec argument and the `[a #c⏎ :b]` counterexample. -/
def scanNextTokenIx_checkFlowAdjacency {input : String}
    (s : ScannerStateIx input) (c : Char) : Except ScanError Unit :=
  if s.inFlow then
    match lastRealTokenValIx? s.tokens with
    | some lastTok =>
      if lastTok.completesFlowValue
          && c != ',' && !(c == ':' && isValueCandidateIx s) && c != ']' && c != '}' then
        .error (.invalidFlowEntry s.cursor.pos.line s.cursor.pos.col)
      else .ok ()
    | none => .ok ()
  else .ok ()

/-- Flow indicator dispatch: `[`, `]`, `{`, `}`, `,`. -/
def scanNextTokenIx_dispatchFlowIndicators {input : String}
    (s : ScannerStateIx input) (c : Char) :
    Except ScanError (Option (ScannerStateIx input)) := do
  -- §7.4 [137]/[140]: reject separator-less adjacent flow entries.
  scanNextTokenIx_checkFlowAdjacency s c
  if c == '[' then return some (scanFlowSequenceStartIx s)
  if c == ']' then
    -- Full `else`-chain (not early-exit statements) so the desugaring is a
    -- plain nested `ite` with closed branches — no `__do_jp` join points,
    -- keeping both `split`- and `rw [if_pos/if_neg]`-style proofs workable.
    if s.flowLevel == 0 then
      throw (.flowEndOutsideFlow ']' s.cursor.pos.line s.cursor.pos.col)
    -- §7.4 [137]: `]` must close the innermost open, which must be a
    -- sequence (`flowStack` top pushed `true` by `[`) — rejects `{a]`.
    else if s.flowStack.back? != some true then
      throw (.mismatchedFlowClose ']' s.cursor.pos.line s.cursor.pos.col)
    else
      return some (scanFlowSequenceEndIx s)
  if c == '{' then return some (scanFlowMappingStartIx s)
  if c == '}' then
    -- Full `else`-chain for the same join-point-free desugaring as `]`.
    if s.flowLevel == 0 then
      throw (.flowEndOutsideFlow '}' s.cursor.pos.line s.cursor.pos.col)
    -- §7.4 [140]: `}` must close the innermost open, which must be a
    -- mapping (`flowStack` top pushed `false` by `{`) — rejects `[a}`.
    else if s.flowStack.back? != some false then
      throw (.mismatchedFlowClose '}' s.cursor.pos.line s.cursor.pos.col)
    else
      return some (scanFlowMappingEndIx s)
  if c == ',' then
    if s.flowLevel == 0 then
      throw (.flowEndOutsideFlow ',' s.cursor.pos.line s.cursor.pos.col)
    let s' ← scanFlowEntryIx s
    return some s'
  return none

/-- Block indicator dispatch: `-`, `?`, `:`. -/
def scanNextTokenIx_dispatchBlockIndicators {input : String}
    (s : ScannerStateIx input) (c : Char) :
    Except ScanError (Option (ScannerStateIx input)) := do
  if c == '-' && !s.inFlow && isBlockEntryCandidateIx s then
    let s' ← scanBlockEntryIx s
    return some s'
  -- §7.4 [150] (item 9g): the `?` opens a flow entry, so it stands only after
  -- `[`, `{` or `,` — see `flowKeyPredecessorOkIx`.
  -- §7.4.1 [150] (item 9j): …and its `s-separate` is mandatory — see
  -- `flowKeyFollowerOkIx`.
  if c == '?' && isKeyCandidateIx s && flowKeyPredecessorOkIx s && flowKeyFollowerOkIx s then
    let s' ← scanKeyIx s
    return some s'
  if c == ':' && isValueCandidateIx s then
    let s' ← scanValueIx s
    return some s'
  return none

/-- Pre-`scanBlockScalarIx` rejections for a `|`/`>` header, in the order
    legacy `scanNextToken_dispatchContent` applies them:

* **§8.1 [170]/[174] — DOCS item 9c.**  `c-l+literal` and `c-l+folded` are
  reachable only through `s-l+block-node` [196]; `ns-flow-content` [158] offers
  plain, flow-seq, flow-map, single- and double-quoted only.  A block-scalar
  header inside a flow collection therefore has no derivation.
* **§6.7 [76] `b-comment`.**  The header line must end in a line break or EOF —
  see `blockScalarHeaderEndsLineIx` (mirrors legacy
  `scanBlockScalarConsumeNewline`'s `expectedNewline` throw).

Folded into **one** guard rather than two consecutive `if … then throw`
statements.  Each early-exit statement in a `do` block duplicates the block's
continuation into both branches; a second one puts four copies of the
block-scalar body in the elaborated term, and `split`'s `simp` then exceeds its
step limit in every downstream inversion proof.  One guard keeps the arm's
`split` sequence exactly as it was before item 9c. -/
def blockScalarPreErrIx {input : String} (s : ScannerStateIx input) (c : Char) :
    Option ScanError :=
  if s.inFlow then
    some (.blockScalarInFlow c s.cursor.pos.line s.cursor.pos.col)
  else if !blockScalarHeaderEndsLineIx s.cursor then
    some (.expectedNewline s.cursor.pos.line)
  else
    none

/-- §7.1 [104] (item 9h): cursor-level twin of legacy `validateAliasClose`.

    `[104] c-ns-alias-node` is a complete node, so in BLOCK context what follows
    it on the line must end that node: a line break, a `#` comment, or the `:`
    that makes the alias an implicit key.  Same allow-list as legacy
    `validateTrailingContent`, and `skipWhitespace` is the cursor twin of
    `skipTrailingSpaces` (both are `s-white` [33] = space or tab).

    Inside a flow collection this is a no-op — `.alias` completes a flow value,
    so `scanNextTokenIx_checkFlowAdjacency` (item 9b) has already rejected
    `[*a *b]`. -/
def aliasTrailingErrIx {input : String} (s : ScannerStateIx input) :
    Option ScanError :=
  if s.inFlow then none
  else
    let probe := skipWhitespace s.cursor
    match probe.peek? with
    | none => none
    | some ch =>
      if isLineBreakBool ch || ch == '#' || ch == ':' then none
      else some (.trailingContent probe.pos.line probe.pos.col)

/-- Content dispatch: scalars + anchors + tags.

    Wires scalars to the per-rule recognisers in
    `IndexedScanner.lean`. For plain scalars in block context, the
    `contentIndent` floor is approximated as `max 0 (currentIndent +
    1)`; the parent-indent for block scalars is `max 0
    currentIndent`. Step 5b tightens this to a per-rule audit. -/
def scanNextTokenIx_dispatchContent {input : String} (s : ScannerStateIx input)
    (c : Char) : Except ScanError (ScannerStateIx input) := do
  if c == '&' then
    -- Item 9e (§6.9 [96]): one anchor per node.  Full `else`-chain, as for the
    -- `|`/`>` guard below — no `__do_jp` join points.
    -- Item 9f (§7.5 [161]): and the anchor is delimited — `&a[b]`.  Same `if`,
    -- so the dispatcher's shape is unchanged (Reflection 613).
    -- Item 165 (§6.9 [96]): and the run is at most two properties long.
    if propertyRunHasAnchorIx s || propertyRunFullIx s ||
        !propertyFollowerOkIx (anchorNameEndIx s) then
      .error (.invalidNodeProperties c s.cursor.pos.line s.cursor.pos.col)
    else do
      let s' ← scanAnchorOrAliasIx s true
      return s'
  if c == '*' then
    -- Item 9e (§6.9 [104]): an alias node carries no properties.
    -- Item 9f (§7.5 [161]/[104]): and it is delimited — `*a[b]`.
    if lastTokenIsNodePropertyIx s || !propertyFollowerOkIx (anchorNameEndIx s) then
      .error (.invalidNodeProperties c s.cursor.pos.line s.cursor.pos.col)
    else do
      let s' ← scanAnchorOrAliasIx s false
      -- §7.1 [104] (item 9h) — see `aliasTrailingErrIx`.
      if let some e := aliasTrailingErrIx s' then throw e
      return s'
  if c == '!' then
    -- Item 9e (§6.9 [96]): one tag per node.
    -- Item 9f (§7.5 [161]): and the tag is delimited — `!t"x"`, `!t[b]`.
    if propertyRunHasTagIx s || propertyRunFullIx s ||
        !propertyScanFollowerOkIx (scanTagIx s) then
      .error (.invalidNodeProperties c s.cursor.pos.line s.cursor.pos.col)
    else do
      let s' ← scanTagIx s
      return s'
  if c == '|' || c == '>' then
    -- Item 9c (§8.1) then §6.7 [76], in legacy's order — see
    -- `blockScalarPreErrIx`.  ONE guard, not two consecutive ones.
    if let some e := blockScalarPreErrIx s c then
      throw e
    -- The *indent floor*, not the clamped parent column: at top level
    -- `currentIndent = -1` and zero-indented content is legal (DK3J, FP8R).
    -- See `scanBlockScalarIx`'s docstring.
    let indentFloor := (max 0 (s.currentIndent + 1)).toNat
    -- §6.1 / §8.1.3 strictness: the auto-detect probe's legacy error
    -- channel (tab in the indentation zone — Y79Y/000; whitespace-only
    -- line wider than the detected content indent — 5LLU, S98Z, W9L4)
    -- is reproduced by `blockScalarBodyErrIx`; the cursor-level
    -- recogniser cannot throw.
    if let some e := blockScalarBodyErrIx s.cursor indentFloor then
      throw e
    -- §6.1 / §8.1.1 strictness: a spaces-then-TAB line at the collection
    -- loop's stop — no arm of `l-chomped-empty` derives it.  Twin of the
    -- legacy gate in `scanBlockScalarBody`.
    if let some e := blockScalarTabStopErrIx s.cursor indentFloor then
      throw e
    let startPos := s.cursor.pos
    match hBS : scanBlockScalarIx s.cursor indentFloor with
    | some r =>
      let content := r.1
      let style := r.2.1
      let cAfter := r.2.2
      let sAfter : ScannerStateIx input := { s with cursor := cAfter }
      let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
        show s.cursor.pos.offset ≤ r.2.2.pos.offset
        exact scanBlockScalarIx_offset_monotonic s.cursor indentFloor hBS
      let sEmit := sAfter.emitAt startPos (YamlToken.scalar content style) hBound
      -- A block scalar always ends at the start of a line, so the next line may
      -- open a fresh simple key, and any key pending from before this scalar is
      -- finished. Mirrors the legacy post-state, which `scanBlockScalarBody`
      -- (Scanner/Scalar.lean) sets and the legacy dispatcher returns untouched.
      -- `simpleKeyAllowed := false` — right for every *inline* scalar branch
      -- below — left the pending key live here, so `a: |⏎  x⏎b: 1` was rejected
      -- with `invalidImplicitKey` (DOCS.md § Indexed-pipeline parity gap, D3).
      -- `needIndentCheck := true` — the block scalar is the one scalar that
      -- consumes its terminating line breaks *inside* the cursor-level
      -- recogniser (legacy sets the flag in `consumeNewline`, but `IxCursor`
      -- carries no flags), so the next `scanNextTokenIx_preprocess` must
      -- re-run the indent unwind.  Without it, a sibling after a block scalar
      -- ending a nested mapping got no `blockEnd`/`blockMappingStart` and was
      -- swallowed (D5: RZT7, KK5P; `- k: 1⏎  c: |⏎    x⏎- k: 2`).
      return { sEmit with simpleKeyAllowed := true,
                          simpleKey := { cursor := IxCursor.start input },
                          needIndentCheck := true }
    | none =>
      throw (.unexpectedChar c s.cursor.pos.line s.cursor.pos.col)
  if c == '"' then
    -- §6.1 / §8.1 / §9.1.2 strictness: legacy fold-time checks
    -- (document marker at col 0 — 5TRB, 9MQT/01; under-indented
    -- continuation — QB6E; tab-indented continuation — DK95/01) are
    -- reproduced by `quotedScalarErrIx`; the cursor-level recogniser
    -- cannot throw.
    if let some e := quotedScalarErrIx s.cursor true s.inFlow s.currentIndent then
      throw e
    let startPos := s.cursor.pos
    match hDQ : scanDoubleQuotedIx s.cursor with
    | some r =>
      let content := r.1
      let cAfter := r.2
      let sAfter : ScannerStateIx input := { s with cursor := cAfter }
      let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
        show s.cursor.pos.offset ≤ r.2.pos.offset
        exact Nat.le_of_lt (scanDoubleQuotedIx_offset_lt s.cursor hDQ)
      let sEmit := sAfter.emitAt startPos
        (YamlToken.scalar content ScalarStyle.doubleQuoted) hBound
      return { sEmit with simpleKeyAllowed := false }
    | none =>
      throw (.unterminatedScalar ScalarStyle.doubleQuoted s.cursor.pos.line)
  if c == '\'' then
    -- Same strictness walker as the `"` arm (single-quoted rules:
    -- document marker — RXY3; under-indent; tab-indented continuation).
    if let some e := quotedScalarErrIx s.cursor false s.inFlow s.currentIndent then
      throw e
    let startPos := s.cursor.pos
    match hSQ : scanSingleQuotedIx s.cursor with
    | some r =>
      let content := r.1
      let cAfter := r.2
      let sAfter : ScannerStateIx input := { s with cursor := cAfter }
      let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
        show s.cursor.pos.offset ≤ r.2.pos.offset
        exact Nat.le_of_lt (scanSingleQuotedIx_offset_lt s.cursor hSQ)
      let sEmit := sAfter.emitAt startPos
        (YamlToken.scalar content ScalarStyle.singleQuoted) hBound
      return { sEmit with simpleKeyAllowed := false }
    | none =>
      throw (.unterminatedScalar ScalarStyle.singleQuoted s.cursor.pos.line)
  if canStartPlainScalarBool c (s.peekAt? 1) s.inFlow then
    -- Item 50: legacy's flow fold throws inside `collectPlainScalarLoop`;
    -- reproduce with the strictness walker before the pure collection.
    if let some e := plainScalarErrIx s.cursor s.inFlow s.currentIndent then
      throw e
    let startPos := s.cursor.pos
    let contentIndent := if s.inFlow then s.cursor.pos.col
                          else (max 0 (s.currentIndent + 1)).toNat
    let rP := scanPlainScalarIx s.cursor s.inFlow contentIndent
    let content := rP.1
    let cAfter := rP.2
    let sAfter : ScannerStateIx input := { s with cursor := cAfter }
    let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
      show s.cursor.pos.offset ≤ rP.2.pos.offset
      exact scanPlainScalarIx_offset_monotonic s.cursor s.inFlow contentIndent
    let sEmit := sAfter.emitAt startPos
      (YamlToken.scalar content ScalarStyle.plain) hBound
    return { sEmit with simpleKeyAllowed := false }
  throw (.unexpectedChar c s.cursor.pos.line s.cursor.pos.col)

/-- §9.1.5 [209]: pending directives require `---` before content.
    Indexed twin of `scanNextToken_checkNoPendingDirectives`. -/
def scanNextTokenIx_checkNoPendingDirectives {input : String}
    (s : ScannerStateIx input) : Except ScanError Unit :=
  if s.directivesPresent then
    .error (.directiveWithoutDocument s.cursor.pos.line)
  else
    .ok ()

/-- Indexed twin of `L4YAML.Scanner.flowOpenIdxLoop`. -/
def flowOpenIdxLoopIx {input : String} (ts : Indexed.TokenStream input) (d : Nat) :
    Nat → Option Nat
  | 0 => none
  | j + 1 =>
    let t := ts.tokens[j]!.token
    if t.isFlowClose then flowOpenIdxLoopIx ts (d + 1) j
    else if t.isFlowOpen then
      match d with
      | 0 => some j
      | d' + 1 => flowOpenIdxLoopIx ts d' j
    else flowOpenIdxLoopIx ts d j

/-- Indexed twin of `L4YAML.Scanner.flowOpenIdx?`. -/
def flowOpenIdxIx? {input : String} (ts : Indexed.TokenStream input) (i : Nat) :
    Option Nat :=
  flowOpenIdxLoopIx ts 0 i

/-- Indexed twin of `L4YAML.Scanner.propsRunStart`. -/
def propsRunStartIx {input : String} (ts : Indexed.TokenStream input) (i : Nat) : Nat :=
  match prevRealIdxIx? ts i with
  | some j =>
    if ts.tokens[j]!.token.isNodeProperty then
      match prevRealIdxIx? ts j with
      | some k => if ts.tokens[k]!.token.isNodeProperty then k else j
      | none => j
    else i
  | none => i

/-- Indexed twin of `L4YAML.Scanner.trailingNodeRun?`, item 159's flow arm
    included. -/
def trailingNodeRunIx? {input : String} (ts : Indexed.TokenStream input) :
    Option (Nat × Option Nat) :=
  match prevRealIdxIx? ts ts.tokens.size with
  | none => none
  | some i =>
    let t := ts.tokens[i]!.token
    if t.isNodeProperty then
      let st := match prevRealIdxIx? ts i with
                | some j => if ts.tokens[j]!.token.isNodeProperty then j else i
                | none => i
      some (st, prevRealIdxIx? ts st)
    else if t.isNodeBody then
      let st := match prevRealIdxIx? ts i with
                | some j =>
                  if ts.tokens[j]!.token.isNodeProperty then
                    match prevRealIdxIx? ts j with
                    | some k => if ts.tokens[k]!.token.isNodeProperty then k else j
                    | none => j
                  else i
                | none => i
      some (st, prevRealIdxIx? ts st)
    else if t.isFlowClose then
      match flowOpenIdxIx? ts i with
      | none => none
      | some o =>
        let st := propsRunStartIx ts o
        some (st, prevRealIdxIx? ts st)
    else none

/-- Indexed twin of `L4YAML.Scanner.propsBlockScanLoop` (item 180). -/
@[yaml_spec "6.9" 96 "c-ns-properties"]
def propsBlockScanLoopIx {input : String} (ts : Indexed.TokenStream input) :
    Nat → Bool × Bool × Option Nat
  | 0 => (false, false, none)
  | j + 1 =>
    let t := ts.tokens[j]!.token
    if t == .placeholder then propsBlockScanLoopIx ts j
    else if t.isNodeProperty then
      let (a, tg, e) := propsBlockScanLoopIx ts j
      let e' := match e with
        | some k => some k
        | none =>
          if t.isAnchorProperty && a then some j
          else if t.isTagProperty && tg then some j
          else none
      (a || t.isAnchorProperty, tg || t.isTagProperty, e')
    else (false, false, none)

/-- Indexed twin of `L4YAML.Scanner.crossedPropsExcessIdx?` (item 180). -/
@[yaml_spec "6.9" 96 "c-ns-properties", yaml_spec "9.2" 211 "l-yaml-stream"]
def crossedPropsExcessIdxIx? {input : String} (ts : Indexed.TokenStream input) :
    Option Nat :=
  match prevRealIdxIx? ts ts.tokens.size with
  | none => none
  | some i =>
    let t := ts.tokens[i]!.token
    if t.isNodeProperty then (propsBlockScanLoopIx ts (i + 1)).2.2
    else if t.isNodeBody then (propsBlockScanLoopIx ts i).2.2
    else if t.isFlowClose then
      match flowOpenIdxIx? ts i with
      | none => none
      | some o => (propsBlockScanLoopIx ts o).2.2
    else none

/-- Indexed twin of `L4YAML.Scanner.crossedPropsExcessPos?` (item 180). -/
@[yaml_spec "6.9" 96 "c-ns-properties", yaml_spec "9.2" 211 "l-yaml-stream"]
def crossedPropsExcessPosIx? {input : String} (ts : Indexed.TokenStream input) :
    Option YamlPos :=
  match crossedPropsExcessIdxIx? ts with
  | some j => some ts.tokens[j]!.start
  | none => none

/-- Indexed twin of `L4YAML.Scanner.propsBlockLineCrossLoop` (item 182). -/
@[yaml_spec "6.7" 80 "s-separate(n,c)", yaml_spec "6.9" 96 "c-ns-properties"]
def propsBlockLineCrossLoopIx {input : String} (ts : Indexed.TokenStream input) :
    Nat → Option YamlPos
  | 0 => none
  | j + 1 =>
    let t := ts.tokens[j]!.token
    if t == .placeholder then propsBlockLineCrossLoopIx ts j
    else if t.isNodeProperty then
      match propsBlockLineCrossLoopIx ts j with
      | some q => some q
      | none =>
        match prevRealIdxIx? ts j with
        | some p =>
          if ts.tokens[p]!.token.isNodeProperty &&
              ts.tokens[p]!.start.line < ts.tokens[j]!.start.line then
            some ts.tokens[j]!.start
          else none
        | none => none
    else none

/-- Indexed twin of `L4YAML.Scanner.runLineCrossPos?` (item 182). -/
@[yaml_spec "6.7" 80 "s-separate(n,c)", yaml_spec "9.2" 211 "l-yaml-stream"]
def runLineCrossPosIx? {input : String} (ts : Indexed.TokenStream input) :
    Option YamlPos :=
  match prevRealIdxIx? ts ts.tokens.size with
  | none => none
  | some i =>
    let t := ts.tokens[i]!.token
    if t.isNodeProperty then propsBlockLineCrossLoopIx ts (i + 1)
    else if t.isNodeBody then
      match propsBlockLineCrossLoopIx ts i with
      | some q => some q
      | none =>
        match prevRealIdxIx? ts i with
        | some p =>
          if ts.tokens[p]!.token.isNodeProperty &&
              ts.tokens[p]!.start.line < ts.tokens[i]!.start.line then
            some ts.tokens[i]!.start
          else none
        | none => none
    else if t.isFlowClose then
      match flowOpenIdxIx? ts i with
      | none => none
      | some o => propsBlockLineCrossLoopIx ts o
    else none

/-- Indexed twin of `L4YAML.Scanner.runLineCrossDanglingPos?` (item 182). -/
@[yaml_spec "6.7" 80 "s-separate(n,c)", yaml_spec "9.2" 211 "l-yaml-stream"]
def runLineCrossDanglingPosIx? {input : String} (ts : Indexed.TokenStream input)
    (indents : Array IndentEntryIx) : Option YamlPos :=
  match runLineCrossPosIx? ts with
  | some q => if indents.any (fun e => e.column == (q.col : Int)) then some q else none
  | none => none

/-- Indexed twin of `L4YAML.Scanner.danglingNodePos?`, item 180's crossed
    over-full property block and item 182's break-crossing run included — the
    legacy docstring has the five readings. -/
def danglingNodePosIx? {input : String} (s : ScannerStateIx input) :
    Option YamlPos :=
  if s.inFlow then none
  else
    match trailingNodeRunIx? s.tokens with
    | none => none
    | some (st, pred) =>
      let offered := match pred with
        | some j => s.tokens.tokens[j]!.token.offersNodeSlot
        | none => false
      if offered && !(s.tokens.tokens[st]!.token.isNodeBody)
          && !(s.tokens.tokens[st]!.token.isNodeProperty) then none
      else
        let p := s.tokens.tokens[st]!.start
        if s.indents.any (fun e => e.column == (p.col : Int)) then some p
        else
          match crossedPropsExcessPosIx? s.tokens with
          | some q => some q
          | none => runLineCrossDanglingPosIx? s.tokens s.indents

/-- §9.2 [211] mid-stream: indexed twin of
    `scanNextToken_checkDanglingNode`, including item 140's two states — the
    run is read off the state the landing ARRIVED with, because preprocessing's
    unwind emits `blockEnd` and pops the level the run stands at. -/
def scanNextTokenIx_checkDanglingNode {input : String}
    (s_run s_land : ScannerStateIx input) : Except ScanError Unit :=
  if s_land.simpleKeyAllowed then
    match danglingNodePosIx? s_run with
    | some p => .error (.invalidBareDocument p.line p.col)
    | none => .ok ()
  else .ok ()

/-- §9.2 [211] at the end of input: indexed twin of
    `scanLoop_checkDanglingNode`. -/
def scanLoopIx_checkDanglingNode {input : String}
    (s : ScannerStateIx input) : Except ScanError Unit :=
  match danglingNodePosIx? s with
  | some p => .error (.invalidBareDocument p.line p.col)
  | none => .ok ()

/-- Indexed twin of `L4YAML.Scanner.underIndentedFlowValuePos?` (item 172):
    §8.1's flow-collection floor, read at the CLOSE — the trailing flow node
    standing in an AWAITED slot whose open sits at an open level's own column.
    See the legacy docstring for the reading. -/
def underIndentedFlowValuePosIx? {input : String} (s : ScannerStateIx input) :
    Option YamlPos :=
  if s.inFlow then none
  else
    match prevRealIdxIx? s.tokens s.tokens.tokens.size with
    | none => none
    | some i =>
      if !(s.tokens.tokens[i]!.token.isFlowClose) then none
      else
        match flowOpenIdxIx? s.tokens i with
        | none => none
        | some o =>
          let st := propsRunStartIx s.tokens o
          let offered := match prevRealIdxIx? s.tokens st with
            | some j => s.tokens.tokens[j]!.token.offersNodeSlot
            | none => false
          let p := s.tokens.tokens[o]!.start
          if offered && s.indents.any (fun e => e.column == (p.col : Int)) then
            some p
          else none

/-- §8.1's floor mid-stream: indexed twin of
    `scanNextToken_checkFlowValueIndent`, including item 140's two states —
    the break off `s_land`, the run off `s_run` before the unwind. -/
def scanNextTokenIx_checkFlowValueIndent {input : String}
    (s_run s_land : ScannerStateIx input) : Except ScanError Unit :=
  if s_land.simpleKeyAllowed then
    match underIndentedFlowValuePosIx? s_run with
    | some p => .error (.underIndentedFlowContent p.line p.col)
    | none => .ok ()
  else .ok ()

/-- §8.1's floor at the end of input: indexed twin of
    `scanLoop_checkFlowValueIndent`. -/
def scanLoopIx_checkFlowValueIndent {input : String}
    (s : ScannerStateIx input) : Except ScanError Unit :=
  match underIndentedFlowValuePosIx? s with
  | some p => .error (.underIndentedFlowContent p.line p.col)
  | none => .ok ()

/-- §9.2 [211]: a completed node and content on a later line at a column no
    open level stands at, with no marker between them, is a second bare
    document.  Indexed twin of `scanNextToken_checkBareDocument` — see its
    docstring for the reading. -/
def scanNextTokenIx_checkBareDocument {input : String}
    (s : ScannerStateIx input) : Except ScanError Unit :=
  if !s.inFlow && s.simpleKeyAllowed
      && !(s.indents.any (fun e => e.column == (s.cursor.pos.col : Int)))
      && (match lastRealTokenValIx? s.tokens with
          | some t => t.completesFlowValue
          | none => false) then
    .error (.invalidBareDocument s.cursor.pos.line s.cursor.pos.col)
  else
    .ok ()

/-- §8.2.2 [194] / §7.5: a `:` that failed `isValueCandidateIx` while a
    completed node's stale simple key is recorded starts a second node in a
    one-node slot (`"a" :b`, `[1]:b`, `*x :b`).  Indexed twin of
    `scanNextToken_checkAdjacentValue` — see its docstring for the reading. -/
def scanNextTokenIx_checkAdjacentValue {input : String}
    (s : ScannerStateIx input) (c : Char) : Except ScanError Unit :=
  if !s.inFlow && c == ':' && !s.simpleKeyAllowed
      && (match lastRealTokenValIx? s.tokens with
          | some t => t.completesFlowValue
          | none => false) then
    .error (.unseparatedValue s.cursor.pos.line s.cursor.pos.col)
  else
    .ok ()

/-- Scan one token (the per-iteration dispatcher). Returns `none`
    at EOF, `some s'` on a successful token, or an error. -/
def scanNextTokenIx {input : String} (s_run : ScannerStateIx input) :
    Except ScanError (Option (ScannerStateIx input)) := do
  match ← scanNextTokenIx_preprocess s_run with
  | none => return none
  | some (s, c) =>
    -- §9.2 [211] (item 133): the dangling node run, before the structural
    -- dispatch — the dangler dies at a `...`/`---` too.  Item 140: the run off
    -- `s_run`, the break off `s`.
    scanNextTokenIx_checkDanglingNode s_run s
    -- §8.1 (item 172): the awaited flow node's under-indented open, at the
    -- same gate — the slot-offered complement of the dangling run.
    scanNextTokenIx_checkFlowValueIndent s_run s
    match ← scanNextTokenIx_dispatchStructural s c with
    | some s' => return some s'
    | none =>
      scanNextTokenIx_checkNoPendingDirectives s
      scanNextTokenIx_checkBareDocument s
      let s := if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s
      match ← scanNextTokenIx_dispatchFlowIndicators s c with
      | some s' => return some s'
      | none =>
        match ← scanNextTokenIx_dispatchBlockIndicators s c with
        | some s' => return some s'
        | none =>
          -- §8.2.2 [194] (item 47): mirror of the legacy check.
          scanNextTokenIx_checkAdjacentValue s c
          let s' ← scanNextTokenIx_dispatchContent s c
          return some s'

/-- Structurally recursive scan loop with fuel parameter. -/
def scanLoopIx {input : String} (s : ScannerStateIx input) (fuel : Nat) :
    Except ScanError (Indexed.TokenStream input) :=
  match fuel with
  | 0 => .error (.fuelExhausted s.cursor.pos.line s.cursor.pos.col)
  | fuel' + 1 =>
    match scanNextTokenIx s with
    | .error e => .error e
    | .ok none =>
      if s.flowLevel > 0 then
        .error (.unterminatedFlowCollection '[' s.cursor.pos.line)
      else if s.directivesPresent then
        .error (.directiveWithoutDocument s.cursor.pos.line)
      else
        -- §9.2 [211] (item 133): the dangling run the stream itself ended.
        match scanLoopIx_checkDanglingNode s with
        | .error e => .error e
        | .ok _ =>
        -- §8.1 (item 172): the awaited flow node's under-indented open,
        -- with the stream itself as the entry's end.
        match scanLoopIx_checkFlowValueIndent s with
        | .error e => .error e
        | .ok _ =>
        let s := unwindIndentsIx s (-1)
        let s := s.emit YamlToken.streamEnd
        .ok s.tokens
    | .ok (some s') => scanLoopIx s' fuel'
termination_by fuel

/-- Top-level scanner entry point: produce a `TokenStream input` (or
    a `ScanError`) from an input string. Mirrors
    `L4YAML.Scanner.scan`. -/
def scanIx (input : String) : Except ScanError (Indexed.TokenStream input) :=
  let s := ScannerStateIx.mk' input
  let s := s.emit YamlToken.streamStart
  let s := match s.peek? with
    | some '﻿' => s.consumeBOM
    | _ => s
  let fuel := input.utf8ByteSize + 1
  scanLoopIx s (fuel * 4)

/-- Like `scanIx` but drops internal `.placeholder` tokens from the
    emitted stream. Indexed twin of `L4YAML.Scanner.scanFiltered`.

    `.placeholder` tokens are emitted by simple-key reservation
    (`saveSimpleKey`) and remain in the stream when a candidate
    simple key is rejected. Downstream consumers (parser, presenter,
    user-facing inspection) never need to see them; this helper
    strips them in a single pass after the main scan completes.

    The indexed parser (`TokenParser.Indexed.parseStreamIx`) does
    *not* skip `.placeholder` internally — its `validNextToken`
    predicate at the directive-prelude boundary returns `true` on
    `.placeholder`, but the parser never *consumes* (advances past)
    such a token, so an unfiltered stream stalls or mis-routes
    through the `_` fallback in `parseNodeContent`. The legacy
    `scanFiltered` was the boundary that stripped placeholders before
    the parser saw them; `scanFilteredIx` restores that boundary for
    the indexed pipeline. -/
def scanFilteredIx (input : String) : Except ScanError (Indexed.TokenStream input) :=
  match scanIx input with
  | .ok ts => .ok { tokens := ts.tokens.filter fun t => t.token != YamlToken.placeholder }
  | .error e => .error e

/-! ## Comment-preserving scan path

Parallel scan path that uses `skipToContentSWithComments` (capturing
each `#`-introduced comment's `(position, text)` pair into the state's
`comments` field) and returns the final state — both tokens and
captured comments — to support `parseYamlWithCommentsIx`.

The non-comment-preserving entry point `scanIx`/`scanFilteredIx` is
unchanged; existing proofs about it remain valid. -/

/-- Comment-preserving preprocessing: same as
    `scanNextTokenIx_preprocess`, but uses `skipToContentSWithComments`
    so any `#`-introduced comment text encountered between tokens is
    appended to `s.comments`. -/
def scanNextTokenIx_preprocessWC {input : String} (s : ScannerStateIx input) :
    Except ScanError (Option (ScannerStateIx input × Char)) :=
  -- Same §6.1/§6.6 strictness walker as `scanNextTokenIx_preprocess`
  -- (the comment-preserving pipeline must reject identically).
  match skipToContentErrIx s.cursor s.inFlow s.currentIndent s.needIndentCheck with
  | some e => .error e
  | none =>
  let s := s.skipToContentSWithComments
  if !s.hasMore then .ok none
  else
    let savedIndentSize := s.indents.size
    let s := if !s.inFlow && s.needIndentCheck then
      let s' := unwindIndentsIx s s.cursor.pos.col
      { s' with needIndentCheck := false }
    else s
    if s.indents.size < savedIndentSize && (s.cursor.pos.col : Int) > s.currentIndent then
      .error (.trailingContent s.cursor.pos.line s.cursor.pos.col)
    else
      let s := saveSimpleKeyIx s
      let s := closeStaleExplicitKeyIx s
      match s.peek? with
      | none => .ok none
      | some c => .ok (some (s, c))

/-- Comment-preserving per-iteration dispatcher. Identical to
    `scanNextTokenIx` except it routes through `_preprocessWC`. -/
def scanNextTokenIxWC {input : String} (s_run : ScannerStateIx input) :
    Except ScanError (Option (ScannerStateIx input)) := do
  match ← scanNextTokenIx_preprocessWC s_run with
  | none => return none
  | some (s, c) =>
    -- §9.2 [211] (item 133): the dangling node run, before the structural
    -- dispatch — the dangler dies at a `...`/`---` too.  Item 140: the run off
    -- `s_run`, the break off `s`.
    scanNextTokenIx_checkDanglingNode s_run s
    -- §8.1 (item 172): the awaited flow node's under-indented open, at the
    -- same gate — the slot-offered complement of the dangling run.
    scanNextTokenIx_checkFlowValueIndent s_run s
    match ← scanNextTokenIx_dispatchStructural s c with
    | some s' => return some s'
    | none =>
      scanNextTokenIx_checkNoPendingDirectives s
      scanNextTokenIx_checkBareDocument s
      let s := if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s
      match ← scanNextTokenIx_dispatchFlowIndicators s c with
      | some s' => return some s'
      | none =>
        match ← scanNextTokenIx_dispatchBlockIndicators s c with
        | some s' => return some s'
        | none =>
          -- §8.2.2 [194] (item 47): mirror of the legacy check.
          scanNextTokenIx_checkAdjacentValue s c
          let s' ← scanNextTokenIx_dispatchContent s c
          return some s'

/-- Comment-preserving scan loop. Returns the final state (not just
    the token stream) so callers can extract both `tokens` and
    `comments`.

    On EOF, re-runs `skipToContentSWithComments` to capture any
    trailing comments that `scanNextTokenIx_preprocessWC` consumed
    just before returning `none` (the updated state is discarded by
    the `.ok none` path of `_preprocess`). Mirrors the legacy
    `Scanner.scanLoopFull`'s re-run trick (Scanner.lean:558-563). -/
def scanLoopIxWC {input : String} (s : ScannerStateIx input) (fuel : Nat) :
    Except ScanError (ScannerStateIx input) :=
  match fuel with
  | 0 => .error (.fuelExhausted s.cursor.pos.line s.cursor.pos.col)
  | fuel' + 1 =>
    match scanNextTokenIxWC s with
    | .error e => .error e
    | .ok none =>
      if s.flowLevel > 0 then
        .error (.unterminatedFlowCollection '[' s.cursor.pos.line)
      else if s.directivesPresent then
        .error (.directiveWithoutDocument s.cursor.pos.line)
      else
        match scanLoopIx_checkDanglingNode s with
        | .error e => .error e
        | .ok _ =>
        match scanLoopIx_checkFlowValueIndent s with
        | .error e => .error e
        | .ok _ =>
        let s := s.skipToContentSWithComments
        let s := unwindIndentsIx s (-1)
        let s := s.emit YamlToken.streamEnd
        .ok s
    | .ok (some s') => scanLoopIxWC s' fuel'
termination_by fuel

/-- Comment-preserving scan entry point: produces both the filtered
    token stream (`.placeholder` stripped, matching `scanFilteredIx`)
    and the collected side-channel comments. Indexed twin of
    `L4YAML.Scanner.scanWithComments`.

    Used by `parseYamlWithCommentsIx` to support comment-preserving
    round-trip (`emitWithComments → parseYamlWithComments`). -/
def scanWithCommentsIx (input : String) :
    Except ScanError (Indexed.TokenStream input × Array (YamlPos × String)) :=
  let s := ScannerStateIx.mk' input
  let s := s.emit YamlToken.streamStart
  let s := match s.peek? with
    | some '﻿' => s.consumeBOM
    | _ => s
  let fuel := input.utf8ByteSize + 1
  match scanLoopIxWC s (fuel * 4) with
  | .ok final =>
    let filtered : Indexed.TokenStream input :=
      { tokens := final.tokens.tokens.filter fun t => t.token != YamlToken.placeholder }
    .ok (filtered, final.comments)
  | .error e => .error e

end ScannerStateIx

end L4YAML.Scanner.Indexed

end Blanket
