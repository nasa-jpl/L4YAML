/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.State
import L4YAML.Scanner.Whitespace
import L4YAML.Scanner.Indent

/-!
# Scanner — Simple Keys, Block Entries, and Value Indicators

The machinery that YAML 1.2.2 §7.4 / §8.2 collectively calls "simple
keys": a plain scalar (or flow node) that might retroactively become
the key of a mapping once a `:` is seen on the same line.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2.

## Scope

- Block indicator scanners: `scanBlockEntry` (`-`, §8.2.1),
  `scanKey` (`?`, §8.2.2).
- Value indicator (`:`, §8.2.2, §7.4) decomposed into four helpers
  + `scanValue`: `scanValueClearKey`, `scanValueValidate`,
  `scanValuePrepare`, `scanValueTabCheck`.
- Implicit-key tracking: `saveSimpleKey`.
- Candidate-lookahead predicates: `isBlockEntryCandidate`,
  `isKeyCandidate`, `isJsonNodeToken`, `isValueCandidate`.
- Post-flow-close validation: `validateFlowClose`.

## Why one file

The simple-key resolution state machine crosses `?` (explicit key),
`:` (value indicator / implicit-key confirmation), `-` (block entry,
which clears any pending simple key), and the `saveSimpleKey` save
hook called at the start of each token dispatch.  All of these
manipulate `simpleKey` / `simpleKeyAllowed` / `simpleKeyStack` /
`explicitKeyLine` — keeping them colocated makes the state machine
inspectable in one read.
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Block Entry, Explicit Key, and Value Indicator Scanning -/

/-- Scan a block entry indicator `-`.

    **Implements** (YAML 1.2.2 §8.2.1):
    - `[186] l+block-sequence(n)` = `(s-indent(n+m) c-l-block-seq-entry(n+m))+ for some fixed auto-detected m > 0`
    - `[187] c-l-block-seq-entry(n)` = `"-" s-l+block-indented(n,BLOCK-IN)`
    - `[4]   c-sequence-entry` = `"-"`

    **Pre**: Scanner at `-` followed by blank/EOF, in block context.
    **Post**: Pushes sequence indent if needed, emits `blockEntry`, advances past `-`,
    sets `simpleKeyAllowed := true`.
    **Error**: `tabInIndentation` if tab is found in preceding whitespace (§6.1).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "8.2.1" 184 "c-l-block-seq-entry"]
def scanBlockEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §6.1: Tab in indentation before block entry.
  -- Scan backward through whitespace consumed by skipToContent to detect any
  -- tab used as indentation for this block entry — forbidden.
  -- Handles `-\t-`, `- \t-`, `-\t -`, etc.
  if !s.inFlow then
    if s.hasTabInPrecedingWhitespace then
      throw (.tabInIndentation s.line s.col)
  let s_with_indent := if !s.inFlow then pushSequenceIndent s s.col else s
  let s_with_token := s_with_indent.emit .blockEntry
  let s_after_advance := s_with_token.advance
  .ok { s_after_advance with simpleKeyAllowed := true }

/-- Scan an explicit key indicator `?`.

    **Implements** (YAML 1.2.2 §8.2.2):
    - `[188] l+block-mapping(n)` = `(s-indent(n+m) ns-l-block-map-entry(n+m))+ for some fixed auto-detected m > 0`
    - `[189] ns-l-block-map-entry(n)` = `c-l-block-map-explicit-entry(n) | ...`
    - `[190] c-l-block-map-explicit-entry(n)` = `c-l-block-map-explicit-key(n) ...`
    - `[191] c-l-block-map-explicit-key(n)` = `"?" s-l+block-indented(n,BLOCK-OUT)`
    - `[5]   c-mapping-key` = `"?"`

    **Pre**: Scanner at `?` followed by blank/EOF (or flow indicator in flow context).
    **Post**: Pushes mapping indent if needed, emits `key`, advances past `?`,
    sets `simpleKeyAllowed := true`, `explicitKeyLine := some s.line`.
    **Error**: `tabInIndentation` if tab immediately follows `?` in block context (§6.1).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "8.2.2" 190 "c-l-block-map-explicit-key"]
def scanKey (s : ScannerState) : Except ScanError ScannerState := do
  let s_with_indent := if !s.inFlow then pushMappingIndent s s.col else s
  let s_with_token := s_with_indent.emit .key
  let s_after_advance := s_with_token.advance
  -- §6.1: Tab immediately after `?` indicator in block context is
  -- indentation for the key content — forbidden.
  if !s_after_advance.inFlow then
    if let some '\t' := s_after_advance.peek? then
      throw (.tabInIndentation s_after_advance.line s_after_advance.col)
  -- Invalidate any pending simple key.  The `?` has already emitted an
  -- explicit `key` token; the next `:` is this key's value indicator,
  -- not confirmation of a new implicit key.
  .ok { s_after_advance with simpleKeyAllowed := true, explicitKeyLine := some s.line,
                              simpleKey := { possible := false } }

/-! ### scanValue — value indicator `:` (§8.2.2, §7.4)

Scan a value indicator `:`.

**Implements** (YAML 1.2.2 §8.2.2, §7.4):
- `[192] ns-l-block-map-implicit-entry(n)`
- `[193] c-l-block-map-implicit-value(n)` = `":" ...`
- `[6]   c-mapping-value` = `":"`

**Refactored for verification**: Decomposed into four helper functions
(`scanValueClearKey`, `scanValueValidate`, `scanValuePrepare`,
`scanValueTabCheck`) so that each piece has a simple provable property
and the composed proof chains them with `omega`.
-/

/-- Clear a spurious simple-key when an explicit `?` key is pending.
    Pure state transformation — never modifies the token array. -/
@[yaml_spec "8.2.2"]
def scanValueClearKey (s : ScannerState) : ScannerState :=
  if let some ekLine := s.explicitKeyLine then
    -- (1) Clear phantom simple key: saved AT the `:` position itself,
    --     but only when `:` is on a DIFFERENT line from `?`.
    --     On the same line, `:` is the value indicator for a nested empty
    --     implicit key inside the explicit key's content per §8.2.2 [196]:
    --     `? : x` → explicit key is the compact mapping {"":"x"}.
    if s.simpleKey.possible && s.simpleKey.pos.offset == s.offset
        && s.line != ekLine then
      { s with simpleKey := { possible := false } }
    -- (2) Clear cross-line simple key from the `?` line: content on the
    --     `?` line is the explicit key's node, not an implicit key to be
    --     resolved by `:` on a subsequent line (§8.2.2 [197]).
    else if s.simpleKey.possible && s.simpleKey.pos.line == ekLine
        && s.line != ekLine && !s.inFlow then
      { s with simpleKey := { possible := false } }
    else s
  else s

/-- Validate pre-conditions for `:` as a value indicator.
    Returns `Unit` on success, throws on violation.
    Does **not** modify the scanner state — only inspects it. -/
@[yaml_spec "8.2.2"]
def scanValueValidate (s : ScannerState) : Except ScanError Unit := do
  -- §7.4: block-context multiline implicit key
  if s.simpleKey.possible && !s.inFlow && s.simpleKey.pos.line != s.line then
    throw (.invalidImplicitKey s.line)
  -- §7.4.2: flow-sequence multiline implicit key
  if s.simpleKey.possible && s.isInFlowSequence && s.explicitKeyLine.isNone
      && s.simpleKey.endLine != s.line then
    throw (.invalidImplicitKey s.line)
  -- §8.2.1: key at same indent as block sequence
  if s.simpleKey.possible && !s.inFlow then
    let keyCol : Int := s.simpleKey.pos.col
    if keyCol <= s.currentIndent then
      if let some top := s.indents.back? then
        if top.isSequence && keyCol == top.column then
          throw (.trailingContent s.simpleKey.pos.line s.simpleKey.pos.col)
  -- T833: missing comma in flow mapping
  if s.simpleKey.possible && s.inFlow && s.simpleKey.tokenIndex > 0 then
    if let some prevTok := s.tokens[s.simpleKey.tokenIndex - 1]? then
      if prevTok.val == .value && prevTok.pos.line != s.line then
        throw (.invalidFlowEntry s.line s.col)
  -- §8.2.2 [197]: explicit value `:` must be at mapping indent level.
  -- l-block-map-explicit-value(n) = s-indent(n) ":" ...
  -- Two sub-checks:
  --   (a) Same line as `?` with no implicit key → reject: the `l-` prefix
  --       means `:` as explicit value must start on its own line.
  --   (b) Different line from `?` → check s-indent(n): column must match.
  if let some ekLine := s.explicitKeyLine then
    if !s.simpleKey.possible && !s.inFlow then
      if s.line == ekLine then
        throw (.sameLineExplicitValue s.line s.col)
      else if (s.col : Int) != s.currentIndent then
        throw (.misindentedExplicitValue s.line s.col s.currentIndent)

/-- Build the prepared state: resolve a pending simple key by overwriting
    placeholder slots (via `Array.setIfInBounds`), optionally pushing indent
    for block mappings, or start a new mapping if no simple key.
    Tokens are preserved or grown (never shifted).

    **Note**: `let` bindings are inlined across `if` boundaries so that
    `split` can discharge each branch independently in proofs. -/
@[yaml_spec "8.2.2"]
def scanValuePrepare (s : ScannerState) : ScannerState :=
  if s.simpleKey.possible then
    let idx := s.simpleKey.tokenIndex
    if !s.inFlow then
      if (s.simpleKey.pos.col : Int) > s.currentIndent then
        let tokens := s.tokens.setIfInBounds idx ⟨s.simpleKey.pos, .blockMappingStart, s.simpleKey.pos⟩
                      |>.setIfInBounds (idx + 1) ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩
        { s with
          tokens := tokens
          indents := s.indents.push { column := (s.simpleKey.pos.col : Int), isSequence := false }
          simpleKey := { possible := false } }
      else
        let tokens := s.tokens.setIfInBounds (idx + 1) ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩
        { s with tokens := tokens, simpleKey := { possible := false } }
    else
      let tokens := s.tokens.setIfInBounds (idx + 1) ⟨s.simpleKey.pos, .key, s.simpleKey.pos⟩
      { s with tokens := tokens, simpleKey := { possible := false } }
  else if s.explicitKeyLine.isSome then
    { s with simpleKey := { possible := false } }
  else
    if !s.inFlow then pushMappingIndent s s.col else s

/-- Check for illegal tab after explicit `:` at or below indent level (§6.1).
    `origCol`/`origIndent` come from the *original* state (before emit/advance);
    the peek is on the *advanced* state. -/
@[yaml_spec "6.1"]
def scanValueTabCheck (origCol : Int) (origIndent : Int) (s_adv : ScannerState) : Except ScanError Unit :=
  if origCol ≤ origIndent && !s_adv.inFlow then
    if let some '\t' := s_adv.peek? then
      throw (.tabInIndentation s_adv.line s_adv.col)
    else .ok ()
  else .ok ()

@[yaml_spec "8.2.2" 6 "c-mapping-value"]
def scanValue (s : ScannerState) : Except ScanError ScannerState := do
  let s_kc := scanValueClearKey s
  scanValueValidate s_kc
  let s_prepared := scanValuePrepare s_kc
  let s_with_token := s_prepared.emit .value
  let s_after_advance := s_with_token.advance
  scanValueTabCheck s.col s.currentIndent s_after_advance
  .ok { s_after_advance with simpleKeyAllowed := true, explicitKeyLine := none }

/-! ## Simple-Key Tracking and Candidate Predicates -/

/-- Record the current position as a potential implicit key.

    **Implements**: Part of YAML 1.2.2 §7.4 (implicit key tracking).
    - `[154] ns-s-implicit-yaml-key(c)` — the key is only confirmed later by `:`.

    If `simpleKeyAllowed` is true, saves the current token index and position.
    This saved key is resolved retroactively when `scanValue` encounters `:`.

    **Pre**: Called after `skipToContent` and indent check, before character dispatch.
    **Post**: Updates `simpleKey` if allowed, otherwise no-op. -/
@[yaml_spec "7.4" 154 "ns-s-implicit-yaml-key"]
def saveSimpleKey (st : ScannerState) : ScannerState :=
  -- §7.4.2: In flow context, content on the `?` line is the explicit
  -- key's node; `?` already emitted a `.key` token so saving content
  -- as a simple key would produce a duplicate key token.
  -- In block context, content on the `?` line CAN form a compact
  -- mapping (e.g., `? a : b` → `{a: b}` as key), so saving IS allowed.
  if st.inFlow && st.explicitKeyLine == some st.line then st
  else if st.simpleKeyAllowed then
    -- Reserve 2 placeholder slots for potential .blockMappingStart + .key
    -- (block context) or .key + spare (flow context).
    let idx := st.tokens.size
    let ph : Positioned YamlToken := ⟨st.currentPos, .placeholder, st.currentPos⟩
    let st := { st with tokens := st.tokens.push ph |>.push ph }
    { st with simpleKey := {
        possible := true
        tokenIndex := idx
        pos := st.currentPos
        endLine := st.line } }
  else st

/-- Check whether a block-entry indicator (`-`) is followed by a blank or EOF.
    Lookahead predicate for `[184] c-l-block-seq-entry(n)` dispatch. -/
@[yaml_spec "8.2.1" 184 "c-l-block-seq-entry"]
def isBlockEntryCandidate (s : ScannerState) : Bool :=
  match s.peekAt? 1 with
  | some n => isBlankBool n
  | none => true

/-- Check whether a key indicator (`?`) is followed by a blank, flow indicator, or EOF.
    Lookahead predicate for `[191] c-l-block-map-explicit-key(n)` dispatch. -/
@[yaml_spec "8.2.2" 191 "c-l-block-map-explicit-key"]
def isKeyCandidate (s : ScannerState) : Bool :=
  match s.peekAt? 1 with
  | some n => isBlankBool n || (s.inFlow && isFlowIndicatorBool n)
  | none => true

/-- Check whether a token is a JSON-like node end (§7.5 [160] c-flow-json-node).
    JSON nodes are: quoted scalars (single/double), flow sequence end `]`,
    and flow mapping end `}`.  Used by `isValueCandidate` to allow adjacent
    `:` per [148]/[149]. -/
@[yaml_spec "7.5" 160 "c-flow-json-node"]
def isJsonNodeToken (tok : YamlToken) : Bool :=
  match tok with
  | .scalar _ .doubleQuoted => true
  | .scalar _ .singleQuoted => true
  | .flowSequenceEnd => true
  | .flowMappingEnd => true
  | _ => false

/-- Check whether a value indicator (`:`) should be recognized.
    §7.4.2 [147]: For YAML keys in flow context, `:` requires NOT-followed-by
    ns-plain-safe (blank, flow indicator, or EOF after `:`) — `s-separate`.
    §7.4.2 [148]/[149]: For JSON keys (quoted scalars, flow collections),
    `:` may be adjacent (no blank required) — `c-ns-flow-map-adjacent-value`.
    In block context, `:` requires blank or EOF after (§8.2.2). -/
@[yaml_spec "7.4.2" 147 "c-ns-flow-map-separate-value",
  yaml_spec "7.4.2" 148 "c-ns-flow-map-json-key-entry"]
def isValueCandidate (s : ScannerState) : Bool :=
  if s.inFlow && s.simpleKey.possible then
    -- Key was saved at a different position (the key content precedes `:`)
    if s.simpleKey.pos.offset != s.offset then
      -- Check if the key's last token was a JSON node.
      -- After saveSimpleKey (at key pos), placeholders are at tokenIndex
      -- and tokenIndex+1; the key token(s) follow.  The last emitted
      -- token is the key's end.
      let isJsonKey := match s.tokens[s.tokens.size - 1]? with
        | some tok => isJsonNodeToken tok.val
        | none => false
      if isJsonKey then true  -- [148]/[149]: adjacent value OK
      else match s.peekAt? 1 with
        | some n => isBlankBool n || isFlowIndicatorBool n  -- [147]: separate value
        | none => true
    else
      -- Simple key was saved at current `:` position (by saveSimpleKey after
      -- a newline reset simpleKeyAllowed).  Check if a JSON node token
      -- immediately precedes the placeholder slots — if so, this `:` is
      -- an adjacent value indicator for that node (§7.4.2 [155]/[157]).
      -- Otherwise fall through to standard next-char check.
      let jsonAdjacentValue := match s.tokens[s.simpleKey.tokenIndex - 1]? with
        | some tok => isJsonNodeToken tok.val
        | none => false
      if jsonAdjacentValue then true
      else match s.peekAt? 1 with
        | some n => isBlankBool n || isFlowIndicatorBool n
        | none => true
  else match s.peekAt? 1 with
  | some n => isBlankBool n || (s.inFlow && isFlowIndicatorBool n)
  | none => true

/-- §7.5: After a flow collection close returns us to block context,
    validate that only whitespace, comments, `:`, or end-of-line follow
    on the same line. -/
@[yaml_spec "7.5"]
def validateFlowClose (s' : ScannerState) : Except ScanError Unit := do
  if s'.flowLevel == 0 then
    let probe := skipTrailingSpaces s' (s'.inputEnd - s'.offset + 1)
    match probe.peek? with
    | none => pure ()
    | some pc =>
      if isLineBreakBool pc || pc == '#' || pc == ':' then pure ()
      else return ← .error (.trailingContent probe.line probe.col)

end L4YAML.Scanner
