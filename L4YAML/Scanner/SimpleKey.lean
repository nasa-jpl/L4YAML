/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.State
public import L4YAML.Scanner.Whitespace
public import L4YAML.Scanner.Indent
public import L4YAML.Scanner.TokenQueries

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-!
# Scanner — Simple Keys, Block Entries, and Value Indicators

The machinery that YAML 1.2.2 §7.4 / §8.2 collectively calls "simple
keys": a plain scalar (or flow node) that might retroactively become
the key of a mapping once a `:` is seen on the same line.

Split from `Scanner.lean` during Blueprint Initiative 1 Phase 2.

## Scope

- Block indicator scanners: `scanBlockEntry` (`-`, §8.2.1),
  `scanKey` (`?`, §8.2.2).
- Value indicator (`:`, §8.2.2, §7.4) decomposed into five helpers
  + `scanValue`: `scanValueClearKey`, `scanValueValidate`,
  `scanValueIndentTabCheck`, `scanValuePrepare`, `scanValueTabCheck`.
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

/-- **The cursor stands at a block MAPPING's own indent** (§8.2.2).

    `atSequenceIndent`'s twin, and the two are exclusive by construction: the
    stack's top is `currentIndent`, so at most one of them can hold. -/
def atMappingIndent (s : ScannerState) : Bool :=
  match s.indents.back? with
  | some top => !top.isSequence && ((s.col : Int) == top.column)
  | none => false

/-- **What a `-` owes at a block mapping's own indent** (§9.2 [211]) — the third
    of the raised-flag danglers, after the completed root document and the
    dangling node run.

    A `-` at a column strictly right of the enclosing collection opens a
    sequence (`pushSequenceIndent`'s guard).  A `-` at a MAPPING's own column
    opens nothing: `[183] l+block-sequence(n)` is reached from
    `[185] s-l+block-indented(n,c)` with the auto-detected `m` allowed to be 0,
    so a zero-indented sequence is legal exactly where a NODE is expected, and
    nowhere else.  Two things expect one:

    * the slot the previous indicator opened is still empty — `:` awaiting its
      value, `?` awaiting its key, `-` awaiting its entry, with at most a
      `[96]` property run standing in between (`nodeSlotAwaited`);
    * a zero-indented sequence at this very column is already open, and this is
      its next entry (`sameIndentSequenceOpen` — a BACKWARD walk, because the
      previous entry of a zero-indented sequence is separated from this one by
      every token of the collections nested inside it).

    Otherwise the mapping entry is complete, the mapping is over, and what
    follows is a second bare document with no `---` in front of it — which is
    the reading the PARSER already takes, at this very line and column
    (`.invalidBareDocument`).  DOCS item 119 mapped the family; this is its
    third mechanism.

    Returns `Unit` on success and never modifies the state. -/
@[yaml_spec "9.2" 211 "l-yaml-stream",
  yaml_spec "8.2.1" 183 "l+block-sequence",
  yaml_spec "8.2.1" 185 "s-l+block-indented"]
def scanBlockEntryValidate (s : ScannerState) : Except ScanError Unit :=
  if atMappingIndent s && !nodeSlotAwaited s.tokens
      && !sameIndentSequenceOpen s.tokens (s.col : Int) then
    .error (.invalidBareDocument s.line s.col)
  else
    .ok ()

/-- Scan a block entry indicator `-`.

    **Implements** (YAML 1.2.2 §8.2.1):
    - `[183] l+block-sequence(n)` = `(s-indent(n+m) c-l-block-seq-entry(n+m))+ for some fixed auto-detected m > 0`
    - `[187] c-l-block-seq-entry(n)` = `"-" s-l+block-indented(n,BLOCK-IN)`
    - `[4]   c-sequence-entry` = `"-"`

    **Pre**: Scanner at `-` followed by blank/EOF, in block context.
    **Post**: Pushes sequence indent if needed, emits `blockEntry`, advances past `-`,
    sets `simpleKeyAllowed := true`.
    **Error**: `tabInIndentation` if tab is found in preceding whitespace (§6.1);
    `sameLineBlockCollection` if a `---`, an implicit `:` or a property run
    shares the line (item 48); `invalidBareDocument` if the `-` stands at a
    block mapping's own column with the entry complete (§9.2 [211],
    `scanBlockEntryValidate`).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "8.2.1" 184 "c-l-block-seq-entry"]
def scanBlockEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §6.1: Tab in indentation before block entry.
  -- Scan backward through whitespace consumed by skipToContent to detect any
  -- tab used as indentation for this block entry — forbidden.
  -- Handles `-\t-`, `- \t-`, `-\t -`, etc.
  if !s.inFlow then
    -- Full `else`-chain (not early-exit statements): with a check AFTER them
    -- the statement form desugars through `__do_jp` join points, which no
    -- `rw [if_pos/if_neg]` or `split` in the ladders below can see through.
    if s.hasTabInPrecedingWhitespace then
      throw (.tabInIndentation s.line s.col)
    -- Item 48: `[194]`'s implicit value has no compact alternative, `[200]`
    -- separates properties from their collection with `s-l-comments`, and no
    -- block collection opens on the `---` line — so a `-` never shares a line
    -- with an implicit `:` (`k: - a`), a property run (`&a - b`), or a
    -- document marker (`--- - a`).  The explicit `:`/`?`/`-` predecessors
    -- (compact collections, `[185]`/`[192]`/`[201]`) set none of the three.
    else if s.implicitValueLine == some s.line
        || lastTokenIsNodePropertyOnLine s.tokens s.line
        || s.markerOnLine then
      throw (.sameLineBlockCollection s.line s.col)
    -- §9.2 [211] (item 134): the `-` at a block mapping's own column with the
    -- entry complete — see `scanBlockEntryValidate`.
    else
      scanBlockEntryValidate s
  let s_with_indent := if !s.inFlow then pushSequenceIndent s s.col else s
  let s_with_token := s_with_indent.emit .blockEntry
  let s_after_advance := s_with_token.advance
  .ok { s_after_advance with simpleKeyAllowed := true }

/-- **The cursor stands at a block sequence's own indent** (§8.2.1).

    A sequence level reaches the indent stack only when it stands strictly
    right of the collection that owns it — `pushSequenceIndent`'s guard is
    `col > currentIndent` — so a sequence AT its parent mapping's own column is
    never pushed, and a column that equals a stacked sequence level's is a
    column no mapping is open at.  An entry indicator there ends the sequence
    and has nothing to belong to.

    `scanValueValidate` tests this of the SAVED KEY's column, at the `:` that
    closes the entry; `scanKey` tests it of the cursor, at the `?` that opens
    one.  The stack's top is `currentIndent` by definition, so equality with
    the top's column is the whole test. -/
def atSequenceIndent (s : ScannerState) : Bool :=
  match s.indents.back? with
  | some top => top.isSequence && ((s.col : Int) == top.column)
  | none => false

/-- **What a `?` owes in block context** — the `:`'s `scanValueValidate`, for
    the indicator that OPENS an entry instead of the one that closes its key.
    Returns `Unit` on success and never modifies the state.

    The first two checks are `scanBlockEntry`'s, verbatim; the third is not,
    and the asymmetry is the point.  A `-` at a block sequence's own indent is
    that sequence's next entry; a `?` there is not, and neither is an implicit
    key, which is why `scanValueValidate` refuses one. -/
@[yaml_spec "8.2.2"]
def scanKeyValidate (s : ScannerState) : Except ScanError Unit := do
  -- §6.1: same check, same reason as `scanBlockEntry`.  In block context a `?`
  -- stands directly after `[63] s-indent(n)` — as `[191]`'s own entry, or as
  -- `[185] s-l+block-indented`'s `s-indent(m)` when compact — and `s-indent` is
  -- spaces only, so ANY tab in the run in front of it was used as indentation.
  if s.hasTabInPrecedingWhitespace then
    throw (.tabInIndentation s.line s.col)
  -- Item 48: `scanBlockEntry`'s same-line check, for the `?` — `k: ? a`,
  -- `&a ? b` and `--- ? a` have no derivation for the same three reasons.
  if s.implicitValueLine == some s.line
      || lastTokenIsNodePropertyOnLine s.tokens s.line
      || s.markerOnLine then
    throw (.sameLineBlockCollection s.line s.col)
  -- §8.2.1: the `?` at a block sequence's own indent, the check
  -- `scanValueValidate` has always run for the `:`.
  if atSequenceIndent s then
    throw (.trailingContent s.line s.col)

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
    **Error**: `tabInIndentation` if a tab sits in the whitespace run *before*
    the `?`, or immediately follows it, in block context (§6.1);
    `trailingContent` if the `?` stands at a block sequence's own indent
    (§8.2.1, `atSequenceIndent`).

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "8.2.2" 190 "c-l-block-map-explicit-key"]
def scanKey (s : ScannerState) : Except ScanError ScannerState := do
  if !s.inFlow then
    scanKeyValidate s
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
                              explicitKeyCol := (s.col : Int),
                              simpleKey := { possible := false },
                              pendingKeys := if s.inFlow then s_after_advance.pendingKeys
                                else s_after_advance.pendingKeys.set!
                                  (s_after_advance.indents.size - 1) (some s.line) }

/-! ### scanValue — value indicator `:` (§8.2.2, §7.4)

Scan a value indicator `:`.

**Implements** (YAML 1.2.2 §8.2.2, §7.4):
- `[192] ns-l-block-map-implicit-entry(n)`
- `[193] c-l-block-map-implicit-value(n)` = `":" ...`
- `[6]   c-mapping-value` = `":"`

**Refactored for verification**: Decomposed into five helper functions
(`scanValueClearKey`, `scanValueValidate`, `scanValueIndentTabCheck`,
`scanValuePrepare`, `scanValueTabCheck`) so that each piece has a simple
provable property and the composed proof chains them with `omega`.
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

/-- §7.4.2 [147]/[149]: in flow context a `:` glued to a `[`/`{` value is legal only after a
    JSON-like key (`c-ns-flow-map-adjacent-value`); after a plain key `[147]` demands
    `s-separate`.  The JSON test mirrors `isValueCandidate`'s two reservation branches. -/
@[yaml_spec "7.4.2" 147 "c-ns-flow-map-separate-value",
  yaml_spec "7.4.2" 149 "c-ns-flow-map-adjacent-value"]
def flowGluedCollectionValue (s : ScannerState) : Bool :=
  s.inFlow
    && (match s.peekAt? 1 with
        | some n => n == '[' || n == '{'
        | none => false)
    && !(match (if s.simpleKey.possible && s.simpleKey.pos.offset == s.offset
                then s.tokens[s.simpleKey.tokenIndex - 1]?
                else s.tokens[s.tokens.size - 1]?) with
         | some tok => isJsonNodeToken tok.val
         | none => false)

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
  -- T833: missing comma in flow mapping (item 9r: line-independent).
  -- The reservation at `simpleKey.tokenIndex` is the entry's start.  If the
  -- slot immediately below it is a `.value`, the previous entry was already
  -- complete (`k: v`) and this `:` continues it with no separator — invalid
  -- whatever the line.  The guard used to fire only across a line break
  -- (`prevTok.pos.line != s.line`), which left the same-line shapes
  -- (`{a: b: c}`, `[a: b: c]`, `{a: b: }`, …) to be rejected downstream by the
  -- parser rather than here; dropping the line test rejects them at the
  -- scanner and makes `simpleKey.tokenIndex` a usable ENTRY BOUNDARY for the
  -- accumulator (see `SavedKeyAtEntryBoundary` in `ScanSteps.lean`).  All 351
  -- `yaml-test-suite` sources are byte-identical under the change in both
  -- pipelines.
  if s.simpleKey.possible && s.inFlow && s.simpleKey.tokenIndex > 0 then
    if let some prevTok := s.tokens[s.simpleKey.tokenIndex - 1]? then
      if prevTok.val == .value then
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
  -- Item 48: §8.2.2 [194] — an implicit value is `s-l+block-node`, which has
  -- no same-line mapping, so a SECOND block-context value indicator on an
  -- implicit `:`'s line has no derivation (`k: v : w`, `k: v: w`,
  -- `k: &a : b`).  The explicit value never set the field, which is what
  -- keeps `? a⏎: b: c` — `[192]`'s compact mapping — served.
  if !s.inFlow && s.implicitValueLine == some s.line then
    throw (.nestedMappingOnLine s.line s.col)
  -- Item 48: §9.1.1 — the `---` line admits one same-line NODE, not a
  -- same-line mapping entry, so a block-context `:` with the marker still on
  -- the line has no derivation (`--- : a`, `--- k: v`, `--- "a": b`).
  -- Item 299: read off the `docStartLine` field, which `scanDocumentStart`
  -- alone writes, in place of a walk over the line's tokens.
  if !s.inFlow && s.markerOnLine then
    throw (.contentOnDocumentStartLine s.line s.col)
  -- §7.4.2 [147]: `{a:[1]}` — a flow value glued to `[`/`{` after a non-JSON key.
  if flowGluedCollectionValue s then
    throw (.unseparatedValue s.line s.col)

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
          indents := s.indents.push { column := (s.simpleKey.pos.col : Int), isSequence := false },
          pendingKeys := s.pendingKeys.push none
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

/-- **§6.1 for the `:` indicator: the run in front of the ENTRY, not in front
    of the colon.**

    A block-mapping entry is `s-indent(n) ns-l-block-map-entry(n)`
    (`[187] l+block-mapping`), and `[63] s-indent` is spaces only — so the
    whitespace run in front of the entry's first character must carry no tab.
    Where that first character is depends on the entry:

    * with an implicit key (`[192]`'s `[193] ns-s-block-map-implicit-key`), the entry
      starts at the KEY, and the run between the key and this `:` is
      `[154] ns-s-implicit-yaml-key`'s own trailing `s-separate-in-line?`,
      where `[66]`'s `s-white` admits a tab — `a\t: b` is legal, and it is the
      key's own indentation that must be clean;
    * with no key — `[192]`'s `e-node` alternative, or the explicit
      value — the entry starts AT the `:`, and its own run is the indentation.

    So the check follows the entry start, and that is what makes it exact: a
    tab-indented line whose content turns out to be a FLOW node is legal
    (`[197] s-l+flow-in-block` reaches it through `s-separate-lines`, whose
    `[69] s-flow-line-prefix` is `s-indent(n) s-separate-in-line?`), and only
    the constructs that demand a bare `s-indent` reject it.  `a:⏎␣␣→[1, 2]` and
    `a:⏎␣␣→foo` stand; `a:⏎␣␣→: b`, `a:⏎␣␣→k: v` and `a:⏎␣␣→"k": v` do not.

    The first test asks the entry-start question DIRECTLY, without consulting
    the simple-key state machine at all: if the whole of the line in front of
    this `:` is whitespace then nothing on the line can be a key, so the entry
    starts here and its run IS `[63] s-indent(n)`.  It decides exactly the
    shapes the two tests below decide — the save `scanNextToken_preprocess`
    makes at the indicator's own position sends the second test to this same
    run — but it decides them from the LINE, which is the coordinate `[187]`
    names, rather than from where a key happens to have been recorded. -/
@[yaml_spec "6.1", yaml_spec "8.2.2" 187 "l+block-mapping"]
def scanValueIndentTabCheck (s : ScannerState) : Except ScanError Unit :=
  if s.inFlow then .ok ()
  else if s.tabInLineIndent then
    throw (.tabInIndentation s.line s.col)
  else if s.simpleKey.possible then
    if ScannerState.hasTabInPrecedingWhitespaceLoop
        s.input s.simpleKey.pos.offset s.simpleKey.pos.offset then
      throw (.tabInIndentation s.simpleKey.pos.line s.simpleKey.pos.col)
    else .ok ()
  else if s.hasTabInPrecedingWhitespace then
    throw (.tabInIndentation s.line s.col)
  else .ok ()

/-- Step 4 (item 335): does the pending explicit key survive this `:`?  In flow
    never; in block a dead register has nothing to close, and a live one
    survives an implicit `:` deeper than the key's column (the `:` is inside the
    key's own content).  Named so proofs can split on it by name. -/
def scanValueKeySurvives (s s_kc : ScannerState) : Bool :=
  let explicitValue : Bool :=
    s_kc.explicitKeyLine.isSome && !s_kc.simpleKey.possible
      && (s.inFlow || (s.col : Int) == s_kc.explicitKeyCol)
  !s.inFlow && (!s_kc.explicitKeyLine.isSome || !explicitValue
    && (if s_kc.simpleKey.possible then (s_kc.simpleKey.pos.col : Int)
        else (s.col : Int)) > s_kc.explicitKeyCol)

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
  scanValueIndentTabCheck s_kc
  let s_prepared := scanValuePrepare s_kc
  let s_with_token := s_prepared.emit .value
  let s_after_advance := s_with_token.advance
  scanValueTabCheck s.col s.currentIndent s_after_advance
  -- Item 48: record the IMPLICIT value's line (`[194]`); the explicit value
  -- leaves the field alone, as does a flow-context `:`.
  -- Item 51: in block context the `:` is the pending `?`'s value line only AT
  -- the key's own column — `[197] l-block-map-explicit-value`'s `s-indent(n)`
  -- is exact.  A keyless `:` at any other live column is an ordinary implicit
  -- `:`: deeper, it is an empty-key entry INSIDE the key's content
  -- (`? earth: blue⏎  : x`); shallower, the `?` entry has ended and the `:`
  -- opens an empty-key entry at the outer level (`k:⏎  ? a⏎: v`).  Both
  -- stamp, so a same-line collection there is refused (§8.2.2 [194]).
  let explicitValue : Bool :=
    s_kc.explicitKeyLine.isSome && !s_kc.simpleKey.possible
      && (s.inFlow || (s.col : Int) == s_kc.explicitKeyCol)
  let ivl : Option Nat :=
    if s.inFlow || explicitValue then
      s_after_advance.implicitValueLine
    else some s.line
  -- Item 48: the pending `?` survives an implicit `:` INSIDE the explicit
  -- key's own content — an entry deeper than the mapping's indent
  -- (spec 8.19's `? earth: blue⏎: moon: white`) — and is consumed by its
  -- explicit value or killed by a sibling entry at the mapping's level.
  -- Item 51: the surviving entry's start is the resolved KEY when one is
  -- saved and the `:` itself otherwise (an empty-key entry survives too).
  -- Step 4 (item 335): the register is the innermost pending level's.  In
  -- flow the `:` ends any pending key; in block an implicit `:` deeper than
  -- the key's column leaves it; the key's own value, or a shallower `:`, closes
  -- the LEVEL's pending key and the register is re-read off the stack — so an
  -- outer `?` survives an inner one's value (`?⏎  ? y⏎  : z⏎: w: x`).
  let survives : Bool := scanValueKeySurvives s s_kc
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

/-! ## Simple-Key Tracking and Candidate Predicates -/

/-- Item 333: a SIBLING entry ends the pending explicit key.  In block context a
    token that starts a line at or left of the `?`'s column and is not `:` (the
    explicit value, [197]), `-` (a compact sequence continuing the key node,
    item 320) or `?` (the next explicit key, which `scanKey` re-arms) is the next
    entry of the ENCLOSING collection — `? a⏎[1]: b` is `{a: null, [1]: b}` —
    so the register is stale: the `?` already has its empty value.  Until now
    the register survived to the entry's own `:` (where `scanValue` dropped it
    for the same reason), so a flow collection opening the sibling parked a
    live pair on `explicitKeyStack`.  On the reference inputs (items 317/320/325,
    yaml-test-suite) acceptance is unchanged — the state now says what the
    readers already decided; the one family that moves is `- ? a⏎- X⏎…` (the
    `?` inside a sequence entry), where the stale register either admitted
    `: Y` at column 0 (libyaml refuses) or refused `- : Y` (libyaml's verdict
    there is the pre-existing `- : a` divergence).  Runs after the simple-key save (whose
    register read is flow-only, so the order is immaterial to behaviour and lets
    the proofs peel it off the outside).  Pure state transformation — never
    modifies the token array. -/
@[yaml_spec "8.2.2"]
def closeStaleExplicitKey (s : ScannerState) : ScannerState :=
  if s.inFlow then s
  else match s.explicitKeyLine, s.peek? with
    | some _, some c =>
      if PendingKeys.staleGate (s.col : Int) s.explicitKeyCol c (s.peekAt? 1) then
        (s.closeStaleAt c).readPendingKey
      else s
    | _, _ => s

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

end Blanket
