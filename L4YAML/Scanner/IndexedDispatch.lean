/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.IndexedState
import L4YAML.Proofs.Scanner.IndexedWhitespace
import L4YAML.Proofs.Scanner.IndexedScalar

/-! # `IndexedDispatch` — Phase 3 top-level scanner (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 cutover commit (Step 6).

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
      if !isFlowIndicatorBool ch && !isWhiteSpaceBool ch && !isLineBreakBool ch then
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
      if !isWhiteSpaceBool ch && !isLineBreakBool ch then
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

theorem collectAnchorNameLoopIx_offset_monotonic {input : String}
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

theorem collectTagHandleLoopIx_offset_monotonic {input : String}
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

theorem collectTagSuffixLoopIx_offset_monotonic {input : String}
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

theorem collectVerbatimTagLoopIx_offset_monotonic {input : String}
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

theorem collectDirectiveNameLoopIx_offset_monotonic {input : String}
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

theorem collectVersionMajorLoopIx_offset_monotonic {input : String}
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

theorem collectVersionMinorLoopIx_offset_monotonic {input : String}
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

theorem skipDocEndWhitespaceIx_offset_monotonic {input : String}
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
Both `scanBlockEntryIx` and `scanKeyIx` carry the legacy tab-in-
indentation check (§6.1 [187] hardening — landed in Step 5b.2). -/

/-- Scan `-` block-entry indicator.

    Throws `tabInIndentation` if a tab appears in the contiguous
    whitespace immediately before the cursor — `skipToContent` runs
    in same-line continuations consume tabs without checking, so this
    backward scan catches tabs that slipped through as indentation
    for this block entry (handles `-\t-`, `- \t-`, `-\t -`, etc.). -/
def scanBlockEntryIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  if !s.inFlow then
    if s.hasTabInPrecedingWhitespace then
      throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
  let s := if !s.inFlow then pushSequenceIndentIx s s.cursor.pos.col else s
  let s := s.emit YamlToken.blockEntry
  let s := s.advance
  .ok { s with simpleKeyAllowed := true }

/-- Scan `?` explicit-key indicator.

    Throws `tabInIndentation` if a tab character immediately follows
    the `?` indicator in block context — that tab would be
    indentation for the key content (§6.1). -/
def scanKeyIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  let s := if !s.inFlow then pushMappingIndentIx s s.cursor.pos.col else s
  let line := s.cursor.pos.line
  let s := s.emit YamlToken.key
  let s := s.advance
  if !s.inFlow then
    if let some '\t' := s.peek? then
      throw (.tabInIndentation s.cursor.pos.line s.cursor.pos.col)
  .ok { s with simpleKeyAllowed := true,
                explicitKeyLine := some line,
                simpleKey := { cursor := IxCursor.start input } }

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

/-- Scan `:` value indicator. Validation is simplified (Step 5b
    hardens this to match the legacy `scanValueValidate` chain). -/
def scanValueIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) :=
  let s := scanValuePrepareIx s
  let s := s.emit YamlToken.value
  let s := s.advance
  .ok { s with simpleKeyAllowed := true, explicitKeyLine := none }

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
      definedAnchors := #[] }

/-- Scan `...` document-end marker. -/
def scanDocumentEndIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) := do
  if s.directivesPresent && !s.documentEverStarted then
    throw (.directiveWithoutDocument s.cursor.pos.line)
  let s := unwindIndentsIx s (-1)
  let s := { s with simpleKey := { cursor := IxCursor.start input } }
  let s := s.emit YamlToken.documentEnd
  let s := s.advanceN 3
  let s := { s with
      simpleKeyAllowed := true,
      allowDirectives := true,
      directivesPresent := false,
      definedAnchors := #[] }
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
  let cAfterTW := skipWhitespace cAfterVer
  let sAfter : ScannerStateIx input := { s with cursor := cAfterTW }
  if !major.isEmpty && !minor.isEmpty then
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
  else
    throw (.directiveTrailingContent sAfter.cursor.pos.line sAfter.cursor.pos.col)

/-- Scan a `%TAG !handle! prefix` directive. As with
    `scanYamlDirectiveIx`, the caller supplies the start-pos bound. -/
def scanTagDirectiveIx {input : String} (s : ScannerStateIx input)
    (cAfterWS : IxCursor input) (startPos : YamlPos)
    (hStart : startPos.offset ≤ cAfterWS.pos.offset) :
    Except ScanError (ScannerStateIx input) := do
  let fuelH := input.utf8ByteSize - cAfterWS.pos.offset
  let r := collectTagHandleLoopIx cAfterWS "" fuelH
  let handle := r.1
  let cAfterHandle := r.2.2
  let cAfterWS2 := skipWhitespace cAfterHandle
  let fuelP := input.utf8ByteSize - cAfterWS2.pos.offset
  let r2 := collectTagSuffixLoopIx cAfterWS2 "" fuelP
  let tagPrefix := r2.1
  let cAfterPrefix := r2.2
  let cAfterTW := skipWhitespace cAfterPrefix
  let sAfter : ScannerStateIx input := { s with cursor := cAfterTW }
  let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
    show startPos.offset ≤ cAfterTW.pos.offset
    have h2 : cAfterWS.pos.offset ≤ cAfterHandle.pos.offset :=
      collectTagHandleLoopIx_offset_monotonic cAfterWS "" fuelH
    have h3 : cAfterHandle.pos.offset ≤ cAfterWS2.pos.offset :=
      skipWhitespace_offset_monotonic cAfterHandle
    have h4 : cAfterWS2.pos.offset ≤ r2.2.pos.offset :=
      collectTagSuffixLoopIx_offset_monotonic cAfterWS2 "" fuelP
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
      scanYamlDirectiveIx ({ sAdv with cursor := cAfterName } : ScannerStateIx input)
        cAfterWS startPos hStart
    else if name == "TAG" then
      scanTagDirectiveIx ({ sAdv with cursor := cAfterName } : ScannerStateIx input)
        cAfterWS startPos hStart
    else
      .ok ({ sAdv with cursor := cAfterWS } : ScannerStateIx input)

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
    let rSuf := if foundBang then
        let fuel' := input.utf8ByteSize - cAfterHandle.pos.offset
        collectTagSuffixLoopIx cAfterHandle "" fuel'
      else (suffix0, cAfterHandle)
    let suffix := rSuf.1
    let cAfter := rSuf.2
    let sAfter : ScannerStateIx input := { sAdv with cursor := cAfter }
    let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
      show s.cursor.pos.offset ≤ rSuf.2.pos.offset
      have h1 : s.cursor.pos.offset ≤ sAdv.cursor.pos.offset :=
        IxCursor.advance_offset_monotonic s.cursor
      have h2 : sAdv.cursor.pos.offset ≤ cAfterHandle.pos.offset :=
        collectTagHandleLoopIx_offset_monotonic sAdv.cursor "" fuel
      have h3 : cAfterHandle.pos.offset ≤ rSuf.2.pos.offset := by
        show cAfterHandle.pos.offset ≤
            (if foundBang then
                let fuel' := input.utf8ByteSize - cAfterHandle.pos.offset
                collectTagSuffixLoopIx cAfterHandle "" fuel'
              else (suffix0, cAfterHandle)).2.pos.offset
        split
        · exact collectTagSuffixLoopIx_offset_monotonic cAfterHandle "" _
        · exact Nat.le_refl _
      exact Nat.le_trans h1 (Nat.le_trans h2 h3)
    let sEmit := sAfter.emitAt startPos (YamlToken.tag handle suffix) hBound
    .ok { sEmit with simpleKeyAllowed := false }

/-! ## Flow indicators -/

/-- Scan `[` flow-sequence start. -/
def scanFlowSequenceStartIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowSequenceStart
  let s := s.advance
  { s with
      flowLevel := s.flowLevel + 1,
      flowStack := s.flowStack.push true,
      simpleKeyStack := s.simpleKeyStack.push s.simpleKey,
      simpleKey := { cursor := IxCursor.start input },
      simpleKeyAllowed := true }

/-- Scan `]` flow-sequence end. -/
def scanFlowSequenceEndIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowSequenceEnd
  let s := s.advance
  let restored := s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }
  { s with
      flowLevel := s.flowLevel - 1,
      flowStack := s.flowStack.pop,
      simpleKeyStack := s.simpleKeyStack.pop,
      simpleKey := restored,
      simpleKeyAllowed := false }

/-- Scan `{` flow-mapping start. -/
def scanFlowMappingStartIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowMappingStart
  let s := s.advance
  { s with
      flowLevel := s.flowLevel + 1,
      flowStack := s.flowStack.push false,
      simpleKeyStack := s.simpleKeyStack.push s.simpleKey,
      simpleKey := { cursor := IxCursor.start input },
      simpleKeyAllowed := true }

/-- Scan `}` flow-mapping end. -/
def scanFlowMappingEndIx {input : String} (s : ScannerStateIx input) :
    ScannerStateIx input :=
  let s := s.emit YamlToken.flowMappingEnd
  let s := s.advance
  let restored := s.simpleKeyStack.back?.getD { cursor := IxCursor.start input }
  { s with
      flowLevel := s.flowLevel - 1,
      flowStack := s.flowStack.pop,
      simpleKeyStack := s.simpleKeyStack.pop,
      simpleKey := restored,
      simpleKeyAllowed := false }

/-- Scan `,` flow entry separator. -/
def scanFlowEntryIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (ScannerStateIx input) :=
  let s := scanValuePrepareIx s
  let s := s.emit YamlToken.flowEntry
  let s := s.advance
  .ok { s with simpleKeyAllowed := true }

/-! ## Dispatcher

Mirrors `Scanner/Scanner.lean::scanNextToken_*` over `ScannerStateIx
input`. The function family is intentionally split into the same
five sub-dispatches as the legacy so that monotonicity proofs
remain tractable (≤ 7 branch points each). -/

/-- Preprocessing: skip whitespace/comments, unwind indents, save
    simple key, peek next character. Returns `none` at EOF. -/
def scanNextTokenIx_preprocess {input : String} (s : ScannerStateIx input) :
    Except ScanError (Option (ScannerStateIx input × Char)) :=
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
      match s.peek? with
      | none => .ok none
      | some c => .ok (some (s, c))

/-- Structural dispatch: under-indent guard, document markers,
    directives. Returns `some s'` if handled, `none` to fall through. -/
def scanNextTokenIx_dispatchStructural {input : String} (s : ScannerStateIx input)
    (c : Char) : Except ScanError (Option (ScannerStateIx input)) := do
  if s.inFlow && s.currentIndent >= 0 && (s.cursor.pos.col : Int) <= s.currentIndent then
    if c != ']' && c != '}' then
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

/-- Flow indicator dispatch: `[`, `]`, `{`, `}`, `,`. -/
def scanNextTokenIx_dispatchFlowIndicators {input : String}
    (s : ScannerStateIx input) (c : Char) :
    Except ScanError (Option (ScannerStateIx input)) := do
  if c == '[' then return some (scanFlowSequenceStartIx s)
  if c == ']' then
    if s.flowLevel == 0 then
      throw (.flowEndOutsideFlow ']' s.cursor.pos.line s.cursor.pos.col)
    return some (scanFlowSequenceEndIx s)
  if c == '{' then return some (scanFlowMappingStartIx s)
  if c == '}' then
    if s.flowLevel == 0 then
      throw (.flowEndOutsideFlow '}' s.cursor.pos.line s.cursor.pos.col)
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
  if c == '?' && isKeyCandidateIx s then
    let s' ← scanKeyIx s
    return some s'
  if c == ':' && isValueCandidateIx s then
    let s' ← scanValueIx s
    return some s'
  return none

/-- Content dispatch: scalars + anchors + tags.

    Wires scalars to the per-rule recognisers in
    `IndexedScanner.lean`. For plain scalars in block context, the
    `contentIndent` floor is approximated as `max 0 (currentIndent +
    1)`; the parent-indent for block scalars is `max 0
    currentIndent`. Step 5b tightens this to a per-rule audit. -/
def scanNextTokenIx_dispatchContent {input : String} (s : ScannerStateIx input)
    (c : Char) : Except ScanError (ScannerStateIx input) := do
  if c == '&' then
    let s' ← scanAnchorOrAliasIx s true
    return s'
  if c == '*' then
    let s' ← scanAnchorOrAliasIx s false
    return s'
  if c == '!' then
    let s' ← scanTagIx s
    return s'
  if c == '|' || c == '>' then
    let parentIndent := (max 0 s.currentIndent).toNat
    let startPos := s.cursor.pos
    match hBS : scanBlockScalarIx s.cursor parentIndent with
    | some r =>
      let content := r.1
      let style := r.2.1
      let cAfter := r.2.2
      let sAfter : ScannerStateIx input := { s with cursor := cAfter }
      let hBound : startPos.offset ≤ sAfter.cursor.pos.offset := by
        show s.cursor.pos.offset ≤ r.2.2.pos.offset
        exact scanBlockScalarIx_offset_monotonic s.cursor parentIndent hBS
      let sEmit := sAfter.emitAt startPos (YamlToken.scalar content style) hBound
      return { sEmit with simpleKeyAllowed := false }
    | none =>
      throw (.unexpectedChar c s.cursor.pos.line s.cursor.pos.col)
  if c == '"' then
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

/-- Flow-collection start indent guard (§8.1 [187]). -/
def scanNextTokenIx_checkBlockFlowIndent {input : String}
    (s : ScannerStateIx input) (c : Char) : Except ScanError Unit :=
  if !s.inFlow && s.currentIndent >= 0 && (s.cursor.pos.col : Int) <= s.currentIndent
      && (c == '[' || c == '{') then
    .error (.underIndentedFlowContent s.cursor.pos.line s.cursor.pos.col)
  else
    .ok ()

/-- Scan one token (the per-iteration dispatcher). Returns `none`
    at EOF, `some s'` on a successful token, or an error. -/
def scanNextTokenIx {input : String} (s : ScannerStateIx input) :
    Except ScanError (Option (ScannerStateIx input)) := do
  match ← scanNextTokenIx_preprocess s with
  | none => return none
  | some (s, c) =>
    match ← scanNextTokenIx_dispatchStructural s c with
    | some s' => return some s'
    | none =>
      let s := if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s
      scanNextTokenIx_checkBlockFlowIndent s c
      match ← scanNextTokenIx_dispatchFlowIndicators s c with
      | some s' => return some s'
      | none =>
        match ← scanNextTokenIx_dispatchBlockIndicators s c with
        | some s' => return some s'
        | none =>
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
      else if s.directivesPresent && !s.documentEverStarted then
        .error (.directiveWithoutDocument s.cursor.pos.line)
      else
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
    | some '﻿' => s.advance
    | _ => s
  let fuel := input.utf8ByteSize + 1
  scanLoopIx s (fuel * 4)

end ScannerStateIx

end L4YAML.Scanner.Indexed
