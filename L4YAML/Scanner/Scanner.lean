/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.State
public import L4YAML.Scanner.Whitespace
public import L4YAML.Scanner.Indent
public import L4YAML.Scanner.TokenQueries
public import L4YAML.Scanner.Document
public import L4YAML.Scanner.NodeProperties
public import L4YAML.Scanner.Scalar
public import L4YAML.Scanner.ScalarFast
public import L4YAML.Scanner.SimpleKey

public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-!
# YAML Scanner (Tokenizer) — Dispatch Umbrella

Phase 9: Character stream → Token stream.

The scanner implements the 132 lexical-layer (L) productions from YAML 1.2.2,
converting a character stream into an array of positioned `YamlToken` values.
The grammar parser (S-layer) then operates on tokens, never on raw characters.

## Architecture

```
String ──→ scan ──→ Array (Positioned YamlToken) ──→ [Grammar Parser] ──→ YamlValue
```

The scanner is a **pure function** `String → Except ScanError (Array (Positioned YamlToken))`.
Internally it uses `ScannerState` to track:
- Current position (offset, line, col)
- Indentation stack (for virtual BLOCK-START/BLOCK-END generation)
- Flow nesting level (flow vs. block context)
- Simple key tracking

## Design Decisions

1. **Batch scanning** (not lazy/on-demand like libyaml). The entire input is
   scanned to a token array before parsing begins. Pure function, easy to verify.

2. **Indentation stack** generates virtual tokens: `blockSequenceStart`,
   `blockMappingStart`, `blockEnd` — analogous to Python's INDENT/DEDENT.

3. **Scalar content is fully resolved**: escapes expanded, line folding applied,
   chomp style applied. The grammar parser receives clean strings.

4. **Context-sensitive.** The same character sequence may tokenize differently
   depending on indentation level, flow/block context, and scalar style.

## Submodule Organization (Blueprint Initiative 1 Phase 2)

The scanner was monolithic (~2761 LoC in one file).  It is now split into
role-named submodules, with this file as the dispatch umbrella:

- [`Scanner.State`](State.lean) — `ScannerState`, `WellFormed`, accessors.
- [`Scanner.Whitespace`](Whitespace.lean) — `skipWhitespace`, `skipSpaces`,
  `consumeNewline`, `skipToContent`, comments (§6.1–§6.7).
- [`Scanner.Indent`](Indent.lean) — virtual `BLOCK-*` generation via
  `unwindIndents`, `pushSequenceIndent`, `pushMappingIndent`.
- [`Scanner.Document`](Document.lean) — `---` / `...` markers, `%YAML` /
  `%TAG` directives (§6.8, §9.1.2).
- [`Scanner.NodeProperties`](NodeProperties.lean) — anchors, aliases,
  tags (§6.9).
- [`Scanner.Scalar`](Scalar.lean) — escape sequences, quoted/plain/block
  scalars, line folding (§5.7, §6.5, §7.3, §8.1).
- [`Scanner.SimpleKey`](SimpleKey.lean) — simple-key resolution,
  `scanBlockEntry` / `scanKey` / `scanValue`, candidate predicates
  (§7.4, §8.2).

This file owns the flow-collection indicator scanners (`[`, `]`, `{`,
`}`, `,`) and the `scanNextToken` dispatch / `scanLoop` / `scan` /
`scanFiltered` main loop.

## Production Rule Contracts

Each scanning function documents which YAML 1.2.2 production(s) it implements
and the contract governing its variables and state transitions.

### Variable Classification

Every numeric variable in the scanner has exactly one of these roles:

- **Position** (absolute column, 0-based): the column where something is or
  must be. Indentation levels are positions. Examples: `parentIndent`,
  `contentIndent`, `s.col`, `currentIndent`.

- **Distance** (character count): how many characters of a particular kind.
  Always non-negative. Examples: `explicitIndent` (the `m` in `s-indent(m)`),
  `spacesConsumed`.

- **Pos** (`YamlPos`): a full (offset, line, col) triple for token attribution.
  Examples: `startPos`, `simpleKey.pos`.

The fundamental relationship: `Position = Position + Distance`.
Never add two Positions or use a Distance where a Position is expected.

### Pre/Post-Condition Style

Each scanning function specifies:

- **Implements**: YAML 1.2.2 production number(s) and section.
- **Pre**: Required scanner state at entry (position, context, expectations).
- **Post**: Scanner state at exit (position advanced past matched content,
  token(s) emitted, flags set).
- **Error**: Conditions under which `Except.error` is returned.

## References

- libyaml `scanner.c` (~2800 lines)
- YAML 1.2.2 §5–§8 (character, lexical, block/flow productions)
- `YAML_PRODUCTIONS.md` §Token–Grammar Layer Analysis
-/

namespace L4YAML.Scanner

open L4YAML
open L4YAML.CharPredicates

/-! ## Flow-Collection Indicator Scanning -/

/-- Scan a flow sequence start indicator `[`.

    **Implements** (YAML 1.2.2 §7.4.1):
    - `[137] c-flow-sequence(n,c)` = `"[" s-separate(n,c)? ...`
    - `[8]   c-sequence-start` = `"["`

    **Pre**: Scanner at `[`.
    **Post**: Emits `flowSequenceStart`, advances past `[`, increments `flowLevel`,
    pushes `true` onto `flowStack` (= sequence), sets `simpleKeyAllowed := true`.

    **Refactored for verification**: Uses explicit variable names (no shadowing)
    to make token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.1" 137 "c-flow-sequence",
  yaml_spec "7.4.1" 8 "c-sequence-start"]
def scanFlowSequenceStart (s : ScannerState) : ScannerState :=
  -- Save the outer simple key so it survives flow nesting.
  -- Example: `[a, b]: value` — the simple key saved before `[` must
  -- still be pending after `]` for `:` to confirm it.
  let savedKey := s.simpleKey
  -- Item 98: the explicit-key stamp is per-flow-level state — save the outer
  -- pair and clear it for the interior, so a pending `?` neither leaks into
  -- the nested collection (`? [a: b]⏎: v`'s pair may reserve its key) nor is
  -- consumed by the nested collection's own `,`/`:` (`? [1, 2]⏎: - w`'s
  -- landed `:` is still `[197]`'s explicit value after the close).
  let savedEk := (s.explicitKeyLine, s.explicitKeyCol)
  let s_key_disabled := { s with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .flowSequenceStart
  let s_after_advance := s_with_token.advance
  { s_after_advance with
      flowLevel := s_after_advance.flowLevel + 1,
      simpleKeyAllowed := true,
      flowStack := s_after_advance.flowStack.push true,
      simpleKeyStack := s_after_advance.simpleKeyStack.push savedKey,
      explicitKeyStack := s_after_advance.explicitKeyStack.push savedEk,
      explicitKeyLine := none,
      explicitKeyCol := -1 }

/-- Scan a flow sequence end indicator `]`.

    **Implements** (YAML 1.2.2 §7.4.1):
    - `[9]  c-sequence-end` = `"]"`

    **Pre**: Scanner at `]` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowSequenceEnd`, advances past `]`, decrements `flowLevel`,
    pops `flowStack`, sets `simpleKeyAllowed := false`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.1" 9 "c-sequence-end"]
def scanFlowSequenceEnd (s : ScannerState) : ScannerState :=
  let s_with_token := s.emit .flowSequenceEnd
  let s_after_advance := s_with_token.advance
  -- Restore the outer simple key saved by the matching flow-open.
  let restored := s_with_token.simpleKeyStack.back?.getD {}
  -- Item 98: restore the outer explicit-key stamp — see `scanFlowSequenceStart`.
  let restoredEk := s_with_token.explicitKeyStack.back?.getD (none, -1)
  -- Item 47: the collection's interior breaks are the TOKEN's own, not
  -- structure — §7.5 stops the rest of the line at the node's tail, so no
  -- block outdent can begin before the next structural break sets the flag
  -- again.  (The indexed pipeline's cursor-level recognisers already read
  -- token-interior breaks this way.)
  { s_after_advance with
      flowLevel := if s_after_advance.flowLevel > 0 then s_after_advance.flowLevel - 1 else 0,
      simpleKeyAllowed := false,
      needIndentCheck := false,
      flowStack := s_after_advance.flowStack.pop,
      simpleKey := restored,
      simpleKeyStack := s_after_advance.simpleKeyStack.pop,
      explicitKeyLine := restoredEk.1,
      explicitKeyCol := restoredEk.2,
      explicitKeyStack := s_after_advance.explicitKeyStack.pop }

/-- Scan a flow mapping start indicator `{`.

    **Implements** (YAML 1.2.2 §7.4.2):
    - `[140] c-flow-mapping(n,c)` = `"{" s-separate(n,c)? ...`
    - `[10]  c-mapping-start` = `"{"`

    **Pre**: Scanner at `{`.
    **Post**: Emits `flowMappingStart`, advances past `{`, increments `flowLevel`,
    pushes `false` onto `flowStack` (= mapping), sets `simpleKeyAllowed := true`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.2" 140 "c-flow-mapping", yaml_spec "7.4.2" 10 "c-mapping-start"]
def scanFlowMappingStart (s : ScannerState) : ScannerState :=
  -- Save the outer simple key so it survives flow nesting.
  -- Example: `{a: b}: value` — the simple key saved before `{` must
  -- still be pending after `}` for `:` to confirm it.
  let savedKey := s.simpleKey
  -- Item 98: save + clear the explicit-key stamp — see `scanFlowSequenceStart`.
  let savedEk := (s.explicitKeyLine, s.explicitKeyCol)
  let s_key_disabled := { s with simpleKey := { possible := false } }
  let s_with_token := s_key_disabled.emit .flowMappingStart
  let s_after_advance := s_with_token.advance
  { s_after_advance with
      flowLevel := s_after_advance.flowLevel + 1,
      simpleKeyAllowed := true,
      flowStack := s_after_advance.flowStack.push false,
      simpleKeyStack := s_after_advance.simpleKeyStack.push savedKey,
      explicitKeyStack := s_after_advance.explicitKeyStack.push savedEk,
      explicitKeyLine := none,
      explicitKeyCol := -1 }

/-- Scan a flow mapping end indicator `}`.

    **Implements** (YAML 1.2.2 §7.4.2):
    - `[11] c-mapping-end` = `"}"`

    **Pre**: Scanner at `}` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowMappingEnd`, advances past `}`, decrements `flowLevel`,
    pops `flowStack`, sets `simpleKeyAllowed := false`.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4.2" 11 "c-mapping-end"]
def scanFlowMappingEnd (s : ScannerState) : ScannerState :=
  let s_with_token := s.emit .flowMappingEnd
  let s_after_advance := s_with_token.advance
  -- Restore the outer simple key saved by the matching flow-open.
  let restored := s_with_token.simpleKeyStack.back?.getD {}
  -- Item 98: restore the outer explicit-key stamp — see `scanFlowSequenceStart`.
  let restoredEk := s_with_token.explicitKeyStack.back?.getD (none, -1)
  -- Item 47: interior breaks are the token's own — see `scanFlowSequenceEnd`.
  { s_after_advance with
      flowLevel := if s_after_advance.flowLevel > 0 then s_after_advance.flowLevel - 1 else 0,
      simpleKeyAllowed := false,
      needIndentCheck := false,
      flowStack := s_after_advance.flowStack.pop,
      simpleKey := restored,
      simpleKeyStack := s_after_advance.simpleKeyStack.pop,
      explicitKeyLine := restoredEk.1,
      explicitKeyCol := restoredEk.2,
      explicitKeyStack := s_after_advance.explicitKeyStack.pop }



/-- Does the property run ending at the cursor already carry an anchor?  A
    second `[101] c-ns-anchor-property` on the same node has no derivation.
    Read over the whole run inside a flow (item 9e), over the current line's
    run outside one (item 9k). -/
def propertyRunHasAnchor (s : ScannerState) : Bool :=
  (s.inFlow && (trailingPropertyRun s.tokens).any YamlToken.isAnchorProperty) ||
    (trailingPropertyRunOnLine s.tokens s.line).any YamlToken.isAnchorProperty

/-- Does the property run ending at the cursor already carry a tag?  A second
    `[97] c-ns-tag-property` on the same node has no derivation. -/
def propertyRunHasTag (s : ScannerState) : Bool :=
  (s.inFlow && (trailingPropertyRun s.tokens).any YamlToken.isTagProperty) ||
    (trailingPropertyRunOnLine s.tokens s.line).any YamlToken.isTagProperty

/-- **Is the property run ending at the cursor already FULL?** (item 165;
    narrowed at item 170)

    `[96] c-ns-properties` is one optional `[101] c-ns-anchor-property` and one
    optional `[97] c-ns-tag-property`, so a run is at most TWO tokens long and a
    THIRD has no derivation whatever its kind.  The two guards above decide by
    KIND, and outside a flow they read the current line's run — which is exactly
    right for `&a !t &b` (refused on the line) and blind to `&a⏎!t &b`, where
    the run crosses a break and the line-filtered reading sees one token.  This
    one decides by LENGTH.

    **In block context the run's TAIL must share the cursor's line.**  A full
    run whose tail closed on an EARLIER line may belong to a PARENT node whose
    block mapping's first implicit key carries the incoming property —
    `&a4 !!map⏎&a5 !!str key5: v` (9KAX) is `[96]`-valid twice over, and the
    two runs stand adjacent in the token array because `l+block-mapping` puts
    no token between them.  A tail on the CURRENT line has no such reading:
    `[187]`'s entries each start a line, so a property following a same-line
    full run joins that run and a third has no derivation.  In a FLOW every
    node stands behind a structural token (`[`/`{`/`,`/`:`/`?`), so adjacent
    property tokens are one node's run wherever their breaks fall, and the
    length alone decides.

    What this refuses `TokenParser` also refuses one stage later; the
    cross-line block shapes it now defers (`&a !t⏎&b x`) are the parser's,
    exactly as `&a⏎!t &b x` was before item 165. -/
@[yaml_spec "6.9" 96 "c-ns-properties"]
def propertyRunFull (s : ScannerState) : Bool :=
  match prevRealIdx? s.tokens s.tokens.size with
  | none => false
  | some i =>
    s.tokens[i]!.val.isNodeProperty &&
      (match prevRealIdx? s.tokens i with
       | none => false
       | some j =>
         s.tokens[j]!.val.isNodeProperty &&
           (s.inFlow ||
             (s.tokens[i]!.pos.line == s.line &&
              s.tokens[j]!.pos.line == s.tokens[i]!.pos.line)))

/-- Is the cursor directly after a node property?  `[104] c-ns-alias-node` is an
    *alternative* to the properties-bearing form of `[161] ns-flow-node`, never
    its content, so `[&a *x]` and `&a *x` have no derivation. -/
def lastTokenIsNodeProperty (s : ScannerState) : Bool :=
  (s.inFlow &&
    (match lastRealTokenVal? s.tokens with
     | some t => t.isNodeProperty
     | none => false)) ||
    lastTokenIsNodePropertyOnLine s.tokens s.line

/-! ### §7.5 [161]: a node property is delimited (item 9f)

    `[161] ns-flow-node(n,c)` reads `c-ns-properties` followed by EITHER
    `s-separate(n,c)` and `ns-flow-content` OR nothing at all (`e-scalar`); [104]
    `c-ns-alias-node` is likewise a whole node.  There is no third arm, so the
    character directly after a property (or alias) token is separation, an entry
    or collection boundary, or end of input — never the first character of
    content.

    Unlike the three tests above this one does NOT need the `s.inFlow` gate:
    it looks only FORWARD, at the character the same token's own walk stopped on,
    so no virtual block opening can sit between the two (Reflection 615).

    The character classes differ sharply between the two property forms, which is
    why so little reaches this test on the anchor side: `[102] ns-anchor-char` is
    `ns-char - c-flow-indicator`, so `&a"x"`, `&a*x`, `&a&b` and `&a:b` are each
    ONE anchor with a funny name, and only `,[]{}` end the token.  `[153]
    ns-tag-char` also subtracts everything outside `ns-uri-char`, so a tag stops
    at `"` — which is how `[!t"x"]` scanned clean before this. -/

/-- The characters that may directly follow a node property or an alias:
    separation (§6.1 `s-white`, §5.4 `b-break`), an entry or collection boundary
    (the node ended with `e-scalar`), or end of input. -/
def propertyFollowerOk (s : ScannerState) : Bool :=
  match s.peek? with
  | none => true
  | some ch =>
    isWhiteSpaceBool ch || isLineBreakBool ch || ch == ',' || ch == ']' || ch == '}'

/-- `propertyFollowerOk` read off the state a property scan produced.  A failed
    scan reports its own error, so the test is vacuous there — which is what
    keeps item 9e's error precedence unchanged when the two guards share an
    `if`. -/
def propertyScanFollowerOk (r : Except ScanError ScannerState) : Bool :=
  match r with
  | .ok s' => propertyFollowerOk s'
  | .error _ => true

/-- Where an anchor or alias name ends, without emitting anything: the same
    `collectAnchorNameLoop` walk `scanAnchorOrAlias` runs, so the follower this
    reports is exactly the one the emitted token stops before. -/
def anchorNameEnd (s : ScannerState) : ScannerState :=
  (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).snd

/-! ### §7.4 [150]: a flow `?` opens an entry (item 9g)

    `[150] ns-flow-pair(n,c)` is `"?" s-separate ns-flow-map-explicit-entry`, and
    a `ns-flow-pair` is an *entry* of `[138] ns-s-flow-seq-entries` /
    `[141] ns-s-flow-map-entries`.  So a `?` may only stand where the collection
    is about to read a fresh entry: directly after its own `[`/`{`, or directly
    after a `,`.

    Every other predecessor has no derivation, and the scanner used to accept
    all of them:

    | input | tokens | why there is no derivation |
    |---|---|---|
    | `[? ? a]` | `key key …` | the explicit entry's key is an `ns-flow-yaml-node`, and `? ` starts no node |
    | `[: ?]` | `key value key` | the empty-key entry's value is an `ns-flow-node`, and `? ` starts none |
    | `[&a ? b]` | `anchor key …` | `[161]`'s properties are followed by `ns-flow-content`, and `? ` is not content |

    The three predecessors that *do* complete a value (`scalar`, `alias`, `]`,
    `}`) are already rejected one dispatcher earlier by
    `scanNextToken_checkFlowAdjacency`, so what this adds is exactly the
    `key` / `value` / property cases — the tokens that are neither an entry
    boundary nor a completed value.

    Placed as a third conjunct on the `?` arm's existing dispatch condition
    rather than as a new `if`: a `?` that fails it falls through to
    `scanNextToken_dispatchContent`, where `canStartPlainScalarBool` is false
    for every character `isKeyCandidate` admits (blank, or a flow indicator —
    neither is `ns-plain-safe`), so the fall-through is always
    `.unexpectedChar`.  The dispatcher gains no `if` and no join point
    (Reflection 613). -/

/-- Inside a flow collection, is the cursor at an entry boundary, where a `?`
    may open an `[150] ns-flow-pair`?  Vacuously true in block context, where
    `[191] c-l-block-map-explicit-key` is governed by indentation instead. -/
@[yaml_spec "7.4.1" 150 "ns-flow-pair(n,c)",
  yaml_spec "7.4.1" 138 "ns-s-flow-seq-entries(n,c)",
  yaml_spec "7.4.2" 141 "ns-s-flow-map-entries(n,c)"]
def flowKeyPredecessorOk (s : ScannerState) : Bool :=
  !s.inFlow ||
    (match lastRealTokenVal? s.tokens with
     | some t => t.opensFlowEntry
     | none => false)

/-! ### §7.4.1 [150]: a flow `?` is DELIMITED (item 9j)

    Item 9g pinned the `?`'s *predecessor*; this pins its *successor*, and it is
    the same production read left to right:

        [150] ns-flow-pair(n,c) ::= ( "?" s-separate(n,c)
                                       ns-flow-map-explicit-entry(n,c) )
                                  | ns-flow-pair-entry(n,c)

    The `s-separate` after the `?` is **mandatory** — inside a flow collection it
    is `s-separate-lines(n)`, whose only zero-width arm is `/* Start of line */`,
    which a `?` sitting mid-line cannot take.  So the character directly after
    the indicator is blank or a break, never a flow indicator.

    `isKeyCandidate` admits a flow indicator (`isBlankBool n || (s.inFlow &&
    isFlowIndicatorBool n)`) — that second disjunct is what let

        [?]        [?,a]       {?}       {?,a}

    scan clean in BOTH pipelines.  None of the four has a derivation: `[142]
    c-ns-flow-map-explicit-entry` can be `( e-node e-node )`, so an EMPTY explicit
    entry is legal (`[? ]`, `[? , a]` are accepted and stay accepted), but the
    `s-separate` before it is not optional.  Nor can the `?` be a plain scalar:
    `[131] ns-plain-first` admits a leading `?` only when the next character is
    `ns-plain-safe(c)`, and in flow context `ns-plain-safe-in` subtracts exactly
    `c-flow-indicator`.

    Like 9g this rides on the `?` arm's dispatch condition rather than adding an
    `if` (Reflection 613), so a `?` that fails it falls through to
    `scanNextToken_dispatchContent`; and by the same argument as 9g the
    fall-through is always `.unexpectedChar`, since the follower that got it here
    is a flow indicator and so not `ns-plain-safe`. -/

/-- §7.4.1 [150] (item 9j): inside a flow collection, is the `?` followed by the
    `s-separate` its production requires?  `none` (end of input) is left to the
    later `unterminatedFlowCollection` check, which owns that error. -/
@[yaml_spec "7.4.1" 150 "ns-flow-pair(n,c)",
  yaml_spec "6.7" 81 "s-separate-lines(n)"]
def flowKeyFollowerOk (s : ScannerState) : Bool :=
  !s.inFlow ||
    (match s.peekAt? 1 with
     | some n => isBlankBool n
     | none => true)

/-- Scan a flow entry separator `,`.

    **Implements** (YAML 1.2.2 §7.4):
    - `[7] c-collect-entry` = `","`

    **Pre**: Scanner at `,` inside a flow collection (`flowLevel > 0`).
    **Post**: Emits `flowEntry`, advances past `,`, sets `simpleKeyAllowed := true`
    and clears `explicitKeyLine`.
    **Error**: `invalidFlowEntry` if comma immediately follows a flow-open indicator
    (`[`, `{`) or another comma — catching leading/consecutive commas.

    **The `,` ENDS the explicit-key entry (item 9l).**  `scanKey` records
    `explicitKeyLine := some line` so that content on the `?`'s line is read as
    the explicit key's own node rather than as a fresh implicit key — the guard
    in `saveSimpleKey` and branch (1) of `scanValueClearKey`.  That scope is the
    ENTRY, not the line: `[150] ns-flow-pair`'s explicit alternative is one
    `ns-flow-seq-entry`, and `[138]`/`[141]`'s `","` starts the next one.
    Leaving the line set made every later entry on that line unable to reserve a
    simple key, so

        [? a, b: c]        [? a, : b]        [? a, : ]

    — all valid, all handled correctly by the flow-MAPPING parser — were
    REJECTED in a flow sequence (`expected ']' but reached end of tokens`): the
    retroactive `.key` token was never written, and `parseFlowSequenceLoop`
    dispatches on exactly that token.  The clear reaches exactly the entries of
    the `,`'s OWN collection (item 98): an enclosing `?`'s stamp is parked on
    `explicitKeyStack` by the flow open and restored by the matching close, so
    the block explicit key whose node contains a flow collection
    (`? [a, b]⏎: - w`) still resolves its landed `:` as `[197]`'s explicit
    value.

    **Refactored for verification**: Uses explicit variable names to make
    token tracking clearer for formal proofs. -/
@[yaml_spec "7.4" 7 "c-collect-entry",
  yaml_spec "7.4.1" 150 "ns-flow-pair(n,c)"]
def scanFlowEntry (s : ScannerState) : Except ScanError ScannerState := do
  -- §7.4: Leading comma (after flow-open) or consecutive commas are invalid.
  if let some lastTok := lastRealTokenVal? s.tokens then
    if lastTok == .flowSequenceStart || lastTok == .flowMappingStart ||
       lastTok == .flowEntry then
      throw (.invalidFlowEntry s.line s.col)
  let s_with_token := s.emit .flowEntry
  let s_after_advance := s_with_token.advance
  -- §7.4.1 [150] (item 9l): the `,` ends the explicit-key entry.
  -- The pending simple key is DEAD here (item 9q): the `,` re-enables simple-key
  -- reservation, so preprocessing's `saveSimpleKey` overwrites `simpleKey`
  -- before any dispatcher can read it.  Leaving it set is therefore
  -- unobservable, but it points at the PREVIOUS entry's reservation — below the
  -- incoming token array's end — which falsifies `SimpleKeyAboveFloor`, the
  -- premise every prefix-preservation lemma in the emitter-scannability tower
  -- goes through.  Clearing it is behaviour-preserving (verified: all 351
  -- `yaml-test-suite` sources byte-identical in both pipelines) and is what
  -- lets a flow pair list carry its entry boundary across the `,`.
  .ok { s_after_advance with
        simpleKeyAllowed := true
        explicitKeyLine := none
        simpleKey := { possible := false } }

/-- §7.4 [137]/[140]: inside a flow collection every value must be
    separated from the next by `,` (entry separator) or `:` (value
    indicator).  If the previous real token completed a value
    (`YamlToken.completesFlowValue`) and the next character starts a new
    node rather than a separator or the matching close (`]`/`}`), the
    entries are adjacent with no separator — invalid YAML (`[[a][b]]`,
    `[[a]b]`, `["a""b"]`).  Fires only on spec-invalid input (the emitter
    never produces separator-less flow entries), so it does not change
    `parseYaml` behaviour on any input the parser accepts.

    Called at the entry of `scanNextToken_dispatchFlowIndicators` — the
    first per-character dispatcher, which runs for *every* character
    before falling through to block/content dispatch — so the guard
    uniformly covers flow-indicator starts (`[`, `{`) and content starts
    (scalars, quotes, `*`, `&`, `!`) alike.

    **The `:` exemption is conditional (item 9d).**  `:` is exempt only
    when it will actually be consumed as a value indicator, i.e. when
    `isValueCandidate` holds — precisely the guard on the `:` arm of
    `scanNextToken_dispatchBlockIndicators`, which runs on the same state
    immediately after this dispatcher falls through.  A `:` that fails
    that test is not a separator at all: it falls through to
    `scanNextToken_dispatchContent` and starts a *plain scalar*
    (`[126] ns-plain-first` admits `:` followed by `ns-plain-safe`), so it
    is a node start and must be treated like one.  An unconditional
    exemption admitted `[a #c⏎ :b]` and `{a #c⏎ :b}` — a comment ends the
    plain scalar `a`, and `:b` then opens a second entry with no `,`
    between them, which `[138] ns-s-flow-seq-entries` and
    `[141] ns-s-flow-map-entries` require. -/
@[yaml_spec "7.4" 137 "c-flow-sequence",
  yaml_spec "7.4" 140 "c-flow-mapping",
  yaml_spec "7.4.1" 138 "ns-s-flow-seq-entries",
  yaml_spec "7.4.2" 141 "ns-s-flow-map-entries"]
def scanNextToken_checkFlowAdjacency (s : ScannerState) (c : Char) :
    Except ScanError Unit :=
  if s.inFlow then
    match lastRealTokenVal? s.tokens with
    | some lastTok =>
      if lastTok.completesFlowValue
          && c != ',' && !(c == ':' && isValueCandidate s) && c != ']' && c != '}' then
        .error (.invalidFlowEntry s.line s.col)
      else .ok ()
    | none => .ok ()
  else .ok ()

/-! ## Main Scanner Loop -/

/-- Preprocessing phase of `scanNextToken`.

    Skips whitespace/comments, handles block indentation unwind,
    saves simple key position, and peeks at the next character.

    Returns `none` if input is exhausted, or `some (s', c)` where
    `s'` is the preprocessed state and `c` is the peeked character. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanNextToken_preprocess (s : ScannerState) :
    Except ScanError (Option (ScannerState × Char)) := do
  let s ← skipToContent s
  if !s.hasMore then return none
  let savedIndentSize := s.indents.size
  let s := if !s.inFlow && s.needIndentCheck then
    let s := unwindIndents s s.col
    { s with needIndentCheck := false }
  else s
  if s.indents.size < savedIndentSize && (s.col : Int) > s.currentIndent then
    return ← .error (.trailingContent s.line s.col)
  let s := saveSimpleKey s
  let s := closeStaleExplicitKey s
  match s.peek? with
  | none => return none
  | some c => return some (s, c)

/-- Structural dispatch: validation checks, document markers, and directives.

    Returns `some s'` if a document marker or directive was processed,
    `none` to indicate fallthrough to indicator/content dispatch. -/
@[yaml_spec "9.1.2" 203 "c-directives-end",
  yaml_spec "9.1.2" 204 "c-document-end",
  yaml_spec "6.8" 82 "l-directive"]
def scanNextToken_dispatchStructural (s : ScannerState) (c : Char) :
    Except ScanError (Option ScannerState) := do
  -- §8.1 / §7.5: Flow content inside a block structure must be more
  -- indented than the enclosing block collection.  Item 50: the closing
  -- bracket is content of the same node — `[137]`/`[140]` sit inside
  -- `s-l+flow-in-block(n)`'s `ns-flow-node(n+1,flow-out)`, so `]`/`}` clear
  -- the same floor and the old exemption was an over-acceptance.
  if s.inFlow && s.currentIndent >= 0 && (s.col : Int) <= s.currentIndent then
    return ← .error (.underIndentedFlowContent s.line s.col)
  -- §5.4: Document markers are forbidden inside flow collections.
  if s.col == 0 && s.inFlow && (atDocumentStart s || atDocumentEnd s) then
    return ← .error (.documentMarkerInFlow s.line)
  if s.col == 0 && atDocumentStart s then return some (scanDocumentStart s)
  if s.col == 0 && atDocumentEnd s then
    let s' ← scanDocumentEnd s
    return some s'
  if c == '%' && s.col == 0 then
    let s' ← scanDirective s
    return some s'
  return none

/-- Flow indicator dispatch: `[`, `]`, `{`, `}`, `,`.

    Returns `some s'` if a flow indicator was processed,
    `none` to indicate fallthrough. -/
@[yaml_spec "7.4.1" 137 "c-flow-sequence",
  yaml_spec "7.4.2" 140 "c-flow-mapping",
  yaml_spec "7.4" 7 "c-collect-entry"]
def scanNextToken_dispatchFlowIndicators (s : ScannerState) (c : Char) :
    Except ScanError (Option ScannerState) := do
  -- §7.4 [137]/[140]: reject separator-less adjacent flow entries.
  scanNextToken_checkFlowAdjacency s c
  if c == '[' then return some (scanFlowSequenceStart s)
  if c == ']' then
    -- Full `else`-chain (not early-exit statements) so the desugaring is a
    -- plain nested `ite` with closed branches — no `__do_jp` join points,
    -- keeping both `split`- and `rw [if_pos/if_neg]`-style proofs workable.
    if s.flowLevel == 0 then
      .error (.flowEndOutsideFlow ']' s.line s.col)
    -- §7.4 [137]: `]` must close the innermost open, which must be a
    -- sequence (`flowStack` top pushed `true` by `[`) — rejects `{a]`.
    else if s.flowStack.back? != some true then
      .error (.mismatchedFlowClose ']' s.line s.col)
    else do
      let s' := scanFlowSequenceEnd s
      validateFlowClose s'
      return some s'
  if c == '{' then return some (scanFlowMappingStart s)
  if c == '}' then
    -- Full `else`-chain for the same join-point-free desugaring as `]`.
    if s.flowLevel == 0 then
      .error (.flowEndOutsideFlow '}' s.line s.col)
    -- §7.4 [140]: `}` must close the innermost open, which must be a
    -- mapping (`flowStack` top pushed `false` by `{`) — rejects `[a}`.
    else if s.flowStack.back? != some false then
      .error (.mismatchedFlowClose '}' s.line s.col)
    else do
      let s' := scanFlowMappingEnd s
      validateFlowClose s'
      return some s'
  if c == ',' then
    if s.flowLevel == 0 then return ← .error (.flowEndOutsideFlow ',' s.line s.col)
    let s' ← scanFlowEntry s
    return some s'
  return none

/-- Block indicator dispatch: `-`, `?`, `:`.

    Returns `some s'` if a block indicator was processed,
    `none` to indicate fallthrough. -/
@[yaml_spec "8.2.1" 184 "c-l-block-seq-entry",
  yaml_spec "8.2.2" 190 "c-l-block-map-explicit-key",
  yaml_spec "8.2.2" 6 "c-mapping-value"]
def scanNextToken_dispatchBlockIndicators (s : ScannerState) (c : Char) :
    Except ScanError (Option ScannerState) := do
  if c == '-' && !s.inFlow && isBlockEntryCandidate s then
    let s' ← scanBlockEntry s
    return some s'
  -- §7.4 [150] (item 9g): the `?` opens a flow entry, so it stands only after
  -- `[`, `{` or `,` — see `flowKeyPredecessorOk`.
  -- §7.4.1 [150] (item 9j): …and its `s-separate` is mandatory, so a flow
  -- indicator may not follow it directly — see `flowKeyFollowerOk`.  Both ride
  -- on this one `if`, so the dispatcher keeps its shape (Reflection 613).
  if c == '?' && isKeyCandidate s && flowKeyPredecessorOk s && flowKeyFollowerOk s then
    let s' ← scanKey s
    return some s'
  if c == ':' && isValueCandidate s then
    let s' ← scanValue s
    return some s'
  return none

/-! ### §7.1 [104]: an alias node ends its node (item 9h)

`[104] c-ns-alias-node ::= "*" ns-anchor-name` is a complete node — an
`ns-flow-node` [161] and, through `s-l+block-node` [196], a complete block node.
So in BLOCK context whatever follows it on the same line would have to be a
SECOND node in a slot that admits exactly one, and there is no derivation.

Every other block-context node terminator already says so, with one shared
allow-list — a line break, a `#` comment, or the `:` that makes the node an
implicit key:

* quoted scalars ([109]/[120]) — `validateTrailingContent`, called inside
  `scanDoubleQuoted` / `scanSingleQuoted`;
* a `]`/`}` that returns to block context ([137]/[140]) — `validateFlowClose`.

The alias arm had neither, and

    k: *a [b]   k: *a {b: c}   k: *a "x"   k: *a 'x'
    k: *a *a    k: *a plain    k: *a &b x  k: *a !t x   k: *a |

all scanned clean in BOTH pipelines (the parser rejects them later, with
`bareDocumentContent`, so this was never a shipped over-acceptance — but the
accumulation step could not refute them).  `validateAliasClose` closes it by
reusing the quoted-scalar sibling's own helper, so the allow-list is shared by
construction rather than restated.

**Why it is gated on `!inFlow`.**  Inside a flow collection the same job is
already done one dispatcher earlier: `.alias` is in `YamlToken.completesFlowValue`,
so `scanNextToken_checkFlowAdjacency` (item 9b) rejects `[*a *b]` before content
dispatch is reached.

**Why the plain, block-scalar, anchor and tag arms need nothing.**  A plain
scalar in block context ABSORBS what follows (`ns-plain-safe-out` is `ns-char`,
so `k: foo [a]` is the one scalar `foo [a]`); a block scalar runs to the end of
its lines; and `&a`/`!t` are `c-ns-properties` [96], which are *supposed* to be
followed by content on the same line (`&a [b]` is one anchored node). -/

/-- §7.1 [104] (item 9h): validate what follows an alias node.  A no-op inside a
    flow collection — see the section note above. -/
@[yaml_spec "7.1" 104 "c-ns-alias-node"]
def validateAliasClose (s : ScannerState) : Except ScanError Unit :=
  if s.inFlow then .ok () else validateTrailingContent s s.inputEnd

/-- Content token dispatch: anchors, tags, scalars, and error.

    Handles `&`, `*`, `!`, `|`/`>`, `"`, `'`, plain scalars.
    Always either processes a token or returns an error. -/
@[yaml_spec "6.9" 96 "c-ns-properties",
  yaml_spec "7.3" 105 "c-flow-scalar",
  yaml_spec "8.1" 161 "c-l-block-scalar"]
def scanNextToken_dispatchContent (s : ScannerState) (c : Char) :
    Except ScanError ScannerState := do
  if c == '&' then
    -- §6.9 [96]: one anchor per node.  Full `else`-chain (not an early-exit
    -- statement) so the desugaring stays a plain `ite` with closed branches —
    -- no `__do_jp` join points; same discipline as the `|`/`>` guard below.
    -- §7.5 [161] (item 9f): and the anchor is delimited — `&a[b]` has no
    -- derivation.  Both tests share the SAME `if`, so the dispatcher gains no
    -- `if` and no join point (Reflection 613).
    -- Item 165: …and the run is at most two properties long, whatever kinds
    -- they are and wherever its breaks fall.  A third disjunct on the SAME
    -- `if`, so the dispatcher's shape is unchanged.
    if propertyRunHasAnchor s || propertyRunFull s ||
        !propertyFollowerOk (anchorNameEnd s) then
      .error (.invalidNodeProperties c s.line s.col)
    else do
      let s' ← scanAnchorOrAlias s true
      let name := (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).fst
      return { s' with definedAnchors := s'.definedAnchors.push name }
  if c == '*' then
    -- §6.9 [104]: an alias node carries no properties.
    -- §7.5 [161]/[104] (item 9f): and the alias node is delimited — `*a[b]`.
    if lastTokenIsNodeProperty s || !propertyFollowerOk (anchorNameEnd s) then
      .error (.invalidNodeProperties c s.line s.col)
    else
      let name := (collectAnchorNameLoop s.advance "" (s.inputEnd - s.advance.offset)).fst
      if !(s.definedAnchors.any (· == name)) then
        .error (.undefinedAlias name s.currentPos.line s.currentPos.col)
      else do
        let s' ← scanAnchorOrAlias s false
        -- §7.1 [104] (item 9h): the alias node is the whole node, so in block
        -- context what follows it on the line must end that node.  One
        -- statement, so the dispatcher gains no `if` and no join point
        -- (Reflection 613).
        validateAliasClose s'
        return s'
  if c == '!' then
    -- §6.9 [96]: one tag per node.
    -- §7.5 [161] (item 9f): and the tag is delimited — `!t"x"`, `!t[b]`.  The
    -- four `[97]` tag forms stop on four different character classes, so the
    -- token's extent is only available from the scan itself; running it in the
    -- guard keeps both tests on one `if` (and so the dispatcher's shape), and
    -- `propertyScanFollowerOk` is vacuous on `.error`, so a failing scan still
    -- reports its own error exactly as before.
    if propertyRunHasTag s || propertyRunFull s ||
        !propertyScanFollowerOk (scanTag s) then
      .error (.invalidNodeProperties c s.line s.col)
    else do
      let s' ← scanTag s
      return s'
  if c == '|' || c == '>' then
    -- §8.1 [170]/[174]: `c-l+literal` and `c-l+folded` are reachable only
    -- through `s-l+block-node` [196]; `ns-flow-content` [158] offers plain,
    -- flow-seq, flow-map, single- and double-quoted only.  So a block-scalar
    -- header inside a flow collection (`[a, |⏎ x⏎]`, `{k: |⏎ x⏎}`) has no
    -- derivation and must be rejected here.  Full `else`-chain (not an
    -- early-exit statement) so the desugaring is a plain `ite` with closed
    -- branches — no `__do_jp` join points, keeping both `split`- and
    -- `rw [if_pos/if_neg]`-style proofs workable.
    if s.inFlow then
      .error (.blockScalarInFlow c s.line s.col)
    else do
      let s' ← scanBlockScalar s
      return s'
  if c == '"' then
    let s' ← scanDoubleQuoted s
    -- §7.4: Quoted scalars can span lines; update simpleKey.endLine
    -- so scanValue can check key-end-line vs `:` line.
    let s' := if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line } }
    else s'
    return s'
  if c == '\'' then
    let s' ← scanSingleQuoted s
    let s' := if s'.simpleKey.possible then
      { s' with simpleKey := { s'.simpleKey with endLine := s'.line } }
    else s'
    return s'
  if canStartPlainScalarBool c (s.peekAt? 1) s.inFlow then
    let s' ← scanPlainScalar s; return s'
  .error (.unexpectedChar c s.line s.col)

/-- §8.1's flow-collection floor, read at the CLOSE (item 172): the trailing
    flow node standing in an AWAITED slot whose open sits at an open level's
    own column.

    `[196] s-l+block-node` reaches a flow node through `s-l+flow-in-block(n)`,
    whose `s-separate(n+1)` demands `s-indent(n+1)` across a break — so a flow
    collection landing AT the awaiting level's column has no derivation as the
    VALUE.  But the same open can head an implicit KEY of a sibling entry
    (`[155] c-s-implicit-json-key` is `c-flow-json-node(n/a, block-key)` — no
    indent parameter), and key-vs-value is not decidable at the open: `k:⏎[1]: b`
    is `{k: null, [1]: b}` while `k:⏎[1, 2]` derives nothing.  Item 159 measured
    the same undecidability for the dangling run (`a: 1⏎&p [b]: c` parses), and
    this reading defers the same way: the key half is resolved by the same-line
    `:` after the close (`scanValue`, through the simple key the close restores),
    and what this reports is the half no `:` resolved.

    The reading is `danglingNodePos?`'s complement on the SLOT: that check fires
    where the slot holder COMPLETES a node (the run belongs to nothing), this one
    where it OFFERS one (`YamlToken.offersNodeSlot` — the run would be the
    offered node, and stands at a column the offer cannot reach).  The two are
    mutually exclusive by that test.  The run must end in a flow CLOSE — the
    scalar at the same column is Finding A's block face, refused by
    `danglingNodePos?`'s own floor (item 177), and the two readings stay
    disjoint by the run's tail.  The column and the reported position
    are the OPEN's: a `[96]` run in front of the open belongs to the node, but
    its column is Finding A's props face (`k:⏎&p [1, 2]` completes at the
    scanner today), so the open's own landing is what this floor reads —
    `k:⏎&p⏎[1, 2]` refuses at the open, where the old open-side check refused
    it. -/
@[yaml_spec "8.1", yaml_spec "8.2.2" 196 "s-l+block-node"]
def underIndentedFlowValuePos? (s : ScannerState) : Option YamlPos :=
  if s.inFlow then none
  else
    match prevRealIdx? s.tokens s.tokens.size with
    | none => none
    | some i =>
      if !(s.tokens[i]!.val.isFlowClose) then none
      else
        match flowOpenIdx? s.tokens i with
        | none => none
        | some o =>
          let st := propsRunStart s.tokens o
          let offered := match prevRealIdx? s.tokens st with
            | some j => s.tokens[j]!.val.offersNodeSlot
            | none => false
          let p := s.tokens[o]!.pos
          if offered && s.indents.any (fun e => e.column == (p.col : Int)) then
            some p
          else none

/-- §8.1's floor mid-stream: the awaited flow node's under-indented open, once
    a line break has ended the entry it could have keyed.  The same two-state
    discipline as `scanNextToken_checkDanglingNode` (item 140): the break is
    `s_land`'s flag, the run is read on `s_run` before preprocessing's unwind
    pops the level the open sits at.  A same-line follower cannot reach this
    check wrongly: `validateFlowClose` admits only `:`, comment, or the break
    after an outermost close, and the `:` resolves the key before any landing
    is armed. -/
@[yaml_spec "8.1"]
def scanNextToken_checkFlowValueIndent (s_run s_land : ScannerState) :
    Except ScanError Unit :=
  if s_land.simpleKeyAllowed then
    match underIndentedFlowValuePos? s_run with
    | some p => .error (.underIndentedFlowContent p.line p.col)
    | none => .ok ()
  else .ok ()

/-- §8.1's floor at the end of input: the same reading, with no break to
    require — the stream itself ended the entry (`k:⏎[1, 2]`).  Runs beside
    `scanLoop_checkDanglingNode`. -/
@[yaml_spec "8.1"]
def scanLoop_checkFlowValueIndent (s : ScannerState) : Except ScanError Unit :=
  match underIndentedFlowValuePos? s with
  | some p => .error (.underIndentedFlowContent p.line p.col)
  | none => .ok ()

/-- §9.1.5 [209]: directives must be followed by `c-directives-end` (`---`).
    If directives are pending (`directivesPresent`) and ordinary content
    arrives instead of `---`/`...`/another directive, the directives are
    orphaned — a scan error.  Factored out (like
    `scanNextToken_checkFlowValueIndent`) so `unfold scanNextToken` exposes
    a single extra bind-split to the proof engine. -/
@[yaml_spec "9.1.5" 209 "l-directive-document"]
def scanNextToken_checkNoPendingDirectives (s : ScannerState) :
    Except ScanError Unit :=
  if s.directivesPresent then
    .error (.directiveWithoutDocument s.line)
  else
    .ok ()

/-- §9.2 [211]: a bare document may only be the stream's first, or follow a
    `...`.  A node that is already complete, and content on a LATER line at a
    column NO OPEN LEVEL stands at, is a second bare document — `l-yaml-stream`
    offers no production for it.

    The three conjuncts are the whole reading, and each is a state field the
    scanner already maintains:

    * the landing column is not one of the open indent levels, so the content
      belongs to no collection the stream has started: it is neither the
      enclosing mapping's next key nor any indicator's content, and the
      collection it would roll in stands in a slot the completed node already
      fills.  A stack holding the sentinel alone is this condition's special
      case, since every landing column is `≥ 0` and the sentinel's is `-1`.  A
      dangling node AT an open level's own column is the complementary
      violation and belongs to its own check;
    * the last real token COMPLETES a node — `YamlToken.completesFlowValue`,
      the same set `scanNextToken_checkFlowAdjacency` reads: a scalar of any
      style, an alias, or a flow close.  Node properties and the indicators
      are excluded because they precede or separate nodes rather than
      finishing one;
    * `simpleKeyAllowed` is up, which is exactly "a line break intervened".
      Every completing scan clears the flag and only a break re-arms it, so
      the same-line readings this must not touch (`[1, 2]: v` and `"x": 1`,
      where the completed node is an implicit KEY) are excluded by the flag
      rather than by a position comparison — the completing token's `endPos`
      is not populated for scalars, so a line test on the TOKEN would read a
      multi-line scalar's start.

    Runs after the structural dispatch, so `---`, `...` and directives are
    reached first and stay legal; a plain scalar absorbs its own continuation
    lines, so the completed-node state is reachable for that style only where
    the walk stops (a comment line, `hello⏎# c⏎world`).

    The parser refuses the same inputs one layer down
    (`StreamState.validNextToken`), at the same position and with this same
    error, so the check moves the refusal without moving any output.  That holds
    at an indented landing as much as at the sentinel: in `k:⏎␣␣"x"⏎␣␣b: 2` the
    scanner would roll a second `blockMappingStart` in at column 2, which the
    first document's reading has no slot for, and both refuse at `2,2`. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanNextToken_checkBareDocument (s : ScannerState) :
    Except ScanError Unit :=
  if !s.inFlow && s.simpleKeyAllowed
      && !(s.indents.any (fun e => e.column == (s.col : Int)))
      && (match lastRealTokenVal? s.tokens with
          | some t => t.completesFlowValue
          | none => false) then
    .error (.invalidBareDocument s.line s.col)
  else
    .ok ()

/-- §9.2 [211]: the DANGLING node run.  A trailing `[96]* (scalar|alias)?` whose
    start sits at an OPEN indent level's own column, and whose structural
    predecessor offers it no slot, belongs to nothing: the level it sits at is
    already occupied by the collection that opened it, and the run is neither
    that collection's next key nor any indicator's content.  §9.2 has no
    production for it, and the parser refuses it as `invalidBareDocument`.

    The three predecessors that DO offer a slot are `YamlToken.offersNodeSlot`'s
    — `:`, `?` and `-` — but the slot they offer cannot reach the level's own
    column either: every alternative of `[196] s-l+block-node(n,c)` and `[185]
    s-l+block-indented(n,c)` that a scalar or alias can head spends
    `s-separate(n+1)`, whose line-crossing branch demands `s-indent(n+1)`, one
    more than the column the level itself stands at (**Finding A**, item 177 —
    the runtime half of `SBlockNode`'s `m = 0` over-approximation, item 107).
    So a props-less scalar or alias run at the column refuses whether a slot is
    offered or not — `a:⏎b`, `?⏎b⏎: v`, `-⏎b`, `k:⏎|⏎ x`.  A `[96]`-headed run
    at the column refuses for the same reason (item 178): the properties
    themselves sit inside the same alternatives, behind the same
    `s-separate(n+1)`, so `k:⏎&x a`, `-⏎&x a`, `?⏎&x a` and the props-headed
    flow tail `k:⏎&x [1]⏎: b` have no derivation either — the first held the
    parser's trailing-content refusal, the `-`/`?` faces were accepted
    outright, and all of them are refused by PyYAML's scanner.  The exemption
    keeps only the run shape another reading owns: the props-less flow-close
    tail (`k:⏎[1, 2]`, `underIndentedFlowValuePos?`'s floor, item 172, and the
    sibling flow key `k:⏎[1]: b`, which no break-ended run ever presents).  What
    stays legal is the strictly deeper landing (`a:⏎ b` is `{a: b}`) and the
    seq-spaces entries, which arrive as `-` indicators rather than as runs
    (`a:⏎- b`).  What never had a slot is a run behind a finished one
    (`a: 1⏎b`), behind a flow close (`k: [1, 2]⏎b`) or behind another dangler.

    The position reported is the RUN's start, not the cursor's, because that is
    where the offending node begins and where the parser reports.

    **The fourth reading is the crossed over-full property block** (item 180):
    a trailing run whose ADJACENT property block holds two anchors or two tags
    is not one `[96]` run, and at a line end the collection split that could
    have licensed it (`&a⏎!t &b x: 1`, the key resolved on its own line) is no
    longer available — so `&a⏎!t &b x` and its `-`-less kin have no derivation
    at ANY column, the sentinel included.  The parser refuses the same inputs
    one layer down at the EXCESS property — the first token, in token order,
    whose kind repeats in the block — and `crossedPropsExcessIdx?` reports
    exactly that index, so the refusal moves without moving its position
    (`&a⏎!t &b x` at `1,3`; the anchor-anchor pair `&p⏎&q b`, which the parser
    called `duplicateAnchor`, now reads `invalidBareDocument` at the second
    anchor — recorded, item 180).  The clause is checked AFTER the at-level
    reading, so every position this function reported before item 180 is
    unchanged.

    **The fifth reading is the run that crosses a break BELOW its start**
    (item 182).  The first three readings are taken at the run's START, and a
    run may start where no level stands and cross the break INSIDE itself: in
    `k: &x⏎a` the `&x` sits legally at column 3 and it is the CONTENT that
    lands at the mapping's own column.  `[96]`'s properties and the content
    they decorate are separated by the same `s-separate(n+1)` the first
    readings spend, so the token that starts the run's second line has no
    derivation at an open level's own column either — `k: &x⏎a`, `- &x⏎a`,
    `? &x⏎a`, `k: !t⏎a`, and the tag-headed suite case H7J7
    (`key: &x⏎!!map⏎␣␣a: b`), whose refusal moves from the parser's
    `trailingContent` to here, at the same position.  `runLineCrossPos?`
    reports that token's own position, which is where PyYAML's scanner reports
    the same inputs; the block-scalar form `k: &x⏎|⏎␣x` is refused here and
    accepted there, item 177's one named PyYAML gap read one step over.  The
    clause is checked LAST, so every position this function reported before
    item 182 is unchanged.  What keeps `k: &x⏎b: 2` is the check's own gate:
    the run has not been ended by a break while its `:` is still to come, and
    `simpleKeyAllowed` is down there — the same gate that keeps `a: 1⏎b: 2`.

    This reads the token array alone.  A property run's placeholders are never
    rewritten while the run is unresolved, so the run is visible there and no
    new state field is needed. -/
def danglingNodePos? (s : ScannerState) : Option YamlPos :=
  if s.inFlow then none
  else
    match trailingNodeRun? s.tokens with
    | none => none
    | some (st, pred) =>
      let offered := match pred with
        | some j => s.tokens[j]!.val.offersNodeSlot
        | none => false
      if offered && !(s.tokens[st]!.val.isNodeBody)
          && !(s.tokens[st]!.val.isNodeProperty) then none
      else
        let p := s.tokens[st]!.pos
        if s.indents.any (fun e => e.column == (p.col : Int)) then some p
        else
          match crossedPropsExcessPos? s.tokens with
          | some q => some q
          | none => runLineCrossDanglingPos? s.tokens s.indents

/-- §9.2 [211] mid-stream: the dangling run, once a line break has ended it.

    `simpleKeyAllowed` is that break, exactly as in
    `scanNextToken_checkBareDocument`: a run still on its own line may yet be
    resolved by a `:` (`a: 1⏎b: 2` — `b` becomes a key), and the flag is down
    there.  Runs BEFORE the structural dispatch, because a dangler dies at a
    `...`/`---` too (`a: 1⏎b⏎...`) and the marker would otherwise consume the
    step.

    **The two states are the landing's two halves, and they are not the same
    state** (item 140).  `s_land` is the landing — its flag is the break this
    check requires.  `s_run` is the state the landing ARRIVED with, and the run
    has to be read there: `scanNextToken_preprocess` unwinds the indent stack
    before it returns, and the unwind EMITS `blockEnd` and POPS the level, so a
    run whose own level the landing dedents past is no longer trailing and no
    longer sits at any open column.  Read at the landing alone, `k:⏎␣␣a: 1⏎␣␣b⏎c: 2`
    scans clean and only `TokenParser`'s `validNextToken` refuses it — at the
    same position, which is what says the two are the same refusal read at two
    depths.  `scanLoop_checkDanglingNode` below has always read the pre-unwind
    array (its own `unwindIndents s (-1)` comes after), so this makes the
    mid-stream check the end-of-input check's exact mid-stream twin.

    `skipToContent` writes neither tokens nor indents, so `s_run` may be the
    state `scanNextToken` was called with: the only writer between the two is
    the unwind, and the save's placeholders are what `prevRealIdx?` skips. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanNextToken_checkDanglingNode (s_run s_land : ScannerState) :
    Except ScanError Unit :=
  if s_land.simpleKeyAllowed then
    match danglingNodePos? s_run with
    | some p => .error (.invalidBareDocument p.line p.col)
    | none => .ok ()
  else .ok ()

/-- §9.2 [211] at the end of input: the same run, with no break to require —
    the stream itself ended it (`a: 1⏎b`).  Runs beside `scanLoop`'s other two
    final validations. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanLoop_checkDanglingNode (s : ScannerState) : Except ScanError Unit :=
  match danglingNodePos? s with
  | some p => .error (.invalidBareDocument p.line p.col)
  | none => .ok ()

/-- §8.2.2 [194] / §7.5: a `:` that reaches CONTENT dispatch while a completed
    node's simple key is still recorded starts a second node in a one-node slot.

    The validators after a quoted scalar, alias, or flow close admit a `:` on
    the node's line because `[154]`/`[194]` make the node an implicit key — but
    that reading requires the `:` to BE the value indicator.  A `:` whose
    follower is not blank fails `isValueCandidate`, falls through the block
    dispatch, and would be read as a `[126]` plain-scalar head (`:b`) — a
    SECOND node after the completed one, which no production derives
    (`"a" :b`, `[1]:b`, `*x :b`).

    The recorded key separates the two `:`-as-plain families: at a genuine
    node-head position the key was saved fresh AT this character
    (`saveSimpleKey`, so `pos.offset = offset` — `k: :b`, `- :b`, `:b`), while
    after a completed node the save is the STALE one made at the node's own
    head (`pos.offset < offset`; the completed scan cleared
    `simpleKeyAllowed`, and only a line break re-arms it).  The
    `completesFlowValue` guard keeps property runs out: after `&a`/`!t` the
    stale save is the run's own head and `&x :b` is one anchored scalar.

    A flow close is refused on the TOKEN alone: `scanFlowSequenceEnd` restores
    the key saved at the matching open, and no invariant here couples that
    stack entry to the line — but after a `]`/`}` a `:` that is not the value
    indicator can never head a node (`[1]:b` glues, `[1]⏎:b` puts a bare
    document after another without `...`), so `t == .flowSequenceEnd`/`.flowMappingEnd`
    fires without consulting the key at all.

    Runs between the block-indicator and content dispatches, so a `:` that IS
    a value indicator never reaches it. -/
@[yaml_spec "8.2.2" 194 "c-l-block-map-implicit-value", yaml_spec "7.5"]
def scanNextToken_checkAdjacentValue (s : ScannerState) (c : Char) :
    Except ScanError Unit :=
  if !s.inFlow && c == ':' && !s.simpleKeyAllowed
      && (match lastRealTokenVal? s.tokens with
          | some t => t.completesFlowValue
          | none => false) then
    .error (.unseparatedValue s.line s.col)
  else
    .ok ()

/-- Scan the next token from the input.

    **Implements**: Main dispatch loop for YAML token recognition.
    Called repeatedly by `scan` until input is exhausted.

    **Decomposed for provability**: Preprocessing and character dispatch are
    split into helper functions (`scanNextToken_preprocess`,
    `scanNextToken_dispatchStructural`, `scanNextToken_dispatchFlowIndicators`,
    `scanNextToken_dispatchBlockIndicators`, `scanNextToken_dispatchContent`)
    each with ≤ 7 branch points, keeping individual proofs tractable.

    Flow:
    1. `scanNextToken_preprocess` — skip whitespace, indent check, peek char
    2. `scanNextToken_dispatchStructural` — validation, document markers, directives
       (then the §9.1.5 and §9.2 stream-structure checks, which markers escape)
    3. `scanNextToken_dispatchFlowIndicators` — `[`, `]`, `{`, `}`, `,`
    4. `scanNextToken_dispatchBlockIndicators` — `-`, `?`, `:`
    5. `scanNextToken_dispatchContent` — `&`, `*`, `!`, `|`/`>`, `"`, `'`, plain

    **Pre**: Scanner state from previous token (or initial state).
    **Post**: Scanner past one token. Token emitted. State updated.
    **Error**: Unexpected character at current position; orphaned directives
    (§9.1.5); a second bare document (§9.2, `scanNextToken_checkBareDocument`);
    an under-indented flow open (§8.1); an unseparated `:` after a completed
    node (§8.2.2). -/
@[yaml_spec "9.2"]
def scanNextToken (s_run : ScannerState) : Except ScanError (Option ScannerState) := do
  match ← scanNextToken_preprocess s_run with
  | none => return none
  | some (s, c) =>
    -- §9.2 [211] (item 133): a dangling node run at an open level's own
    -- column, ended by the break this landing crossed.  BEFORE the structural
    -- dispatch, because the dangler dies at a `...`/`---` too.  The run is read
    -- off `s_run` and the break off `s`, because preprocessing's unwind
    -- displaces the run from the array it would be read in (item 140).
    scanNextToken_checkDanglingNode s_run s
    -- §8.1 (item 172): the AWAITED flow node's under-indented open, at the
    -- same gate — the slot-offered complement of the dangling run, read at
    -- the close because the open can head an implicit key instead.
    scanNextToken_checkFlowValueIndent s_run s
    match ← scanNextToken_dispatchStructural s c with
    | some s' => return some s'
    | none =>
      -- §9.1.5 [209]: pending directives with no `---` before content
      -- are orphaned — error (spec-exact since the nb-char/ns-char era).
      scanNextToken_checkNoPendingDirectives s
      -- §9.2 [211] (item 132): a completed ROOT node and content on a later
      -- line, with no `---`/`...` between them, is a second bare document.
      scanNextToken_checkBareDocument s
      -- Any non-directive, non-document-marker content means we're in a document.
      -- Disallow directives until the next `...` document-end marker.
      let s := if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true }
      else s
      match ← scanNextToken_dispatchFlowIndicators s c with
      | some s' => return some s'
      | none =>
        match ← scanNextToken_dispatchBlockIndicators s c with
        | some s' => return some s'
        | none =>
          -- §8.2.2 [194] (item 47): a `:` that failed `isValueCandidate` while
          -- a completed node's stale key is recorded has no plain reading.
          scanNextToken_checkAdjacentValue s c
          let s' ← scanNextToken_dispatchContent s c
          return some s'

/-- Structurally recursive helper for scan.

    Processes tokens one at a time using `scanNextToken`, with fuel decreasing
    on each iteration. Returns when either:
    - `scanNextToken` returns `none` (normal completion)
    - fuel is exhausted (error)

    **Design for provability**: Uses structural recursion on fuel parameter,
    enabling standard induction tactics for theorem proving. This replaces
    the imperative `for` loop in the original implementation.

    **Implements**: Core scanning loop with termination checking.
    **Post**: Same as `scan` - returns tokens starting with `streamStart`,
    ending with `streamEnd`.
    **Error**: Same error conditions as `scan`. -/
@[yaml_spec "9.2"]
def scanLoop (s : ScannerState) (fuel : Nat) :
    Except ScanError (Array (Positioned YamlToken)) :=
  match fuel with
  | 0 =>
    -- Fuel exhausted without scanner signaling completion
    .error (.fuelExhausted s.line s.col)
  | fuel' + 1 =>
    match scanNextToken s with
    | .error e =>
      -- Propagate scanner error
      .error e
    | .ok none =>
      -- Scanner signals completion (no more tokens to process)
      -- Perform final validation and emit streamEnd
      if s.flowLevel > 0 then
        -- §7.4: Unclosed flow collections are an error
        .error (.unterminatedFlowCollection '[' s.line)
      else if s.directivesPresent then
        -- §9.1.5 [209]: directives with no following `---` are an error.
        -- (`directivesPresent` is reset by both `---` and `...`, so a bare
        -- check is exact; the old `&& !documentEverStarted` conjunct let
        -- orphan directives in second documents slip through.)
        .error (.directiveWithoutDocument s.line)
      else
        -- §9.2 [211] (item 133): the dangling run the stream itself ended.
        match scanLoop_checkDanglingNode s with
        | .error e => .error e
        | .ok _ =>
        -- §8.1 (item 172): the awaited flow node's under-indented open,
        -- with the stream itself as the entry's end.
        match scanLoop_checkFlowValueIndent s with
        | .error e => .error e
        | .ok _ =>
        -- Close all remaining block contexts and emit final token
        let final := unwindIndents s (-1)
        let final := final.emit .streamEnd
        .ok final.tokens
    | .ok (some s') =>
      -- Scanner produced a new state, continue with remaining fuel
      scanLoop s' fuel'
termination_by fuel

/-- Run the scanner on an input string, producing a token array.

    **Implements**: Complete YAML tokenization pipeline.
    Wraps `scanNextToken` in a fuel-bounded loop (via `scanLoop`), bookended by
    `streamStart`/`streamEnd` tokens.

    **Refactored for provability**: Now uses structurally recursive `scanLoop`
    instead of imperative `for` loop, enabling formal verification via induction.

    **Post**: Token array starts with `streamStart`, ends with `streamEnd`.
    All block collections are properly closed via `unwindIndents`.
    **Error**: `unterminatedFlowCollection` (unclosed `[`/`{`),
    `directiveWithoutDocument` (orphan directives), `fuelExhausted`. -/
@[yaml_spec "9.2" 211 "l-yaml-stream",
  yaml_spec "5.2" 3 "c-byte-order-mark",
  yaml_spec "9.1.1" 202 "l-document-prefix"]
def scan (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  let s := ScannerState.mk' input
  let s := s.emit .streamStart
  -- Handle BOM (Byte Order Mark)
  let s := match s.peek? with
    | some '\uFEFF' => s.consumeBOM
    | _ => s
  -- Calculate fuel: 4x input size should be more than enough
  let fuel := input.utf8ByteSize + 1
  scanLoop s (fuel * 4)

/-- Like `scan` but filters out internal placeholder tokens.
    Use this for all user-facing output and tests. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanFiltered (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  match scan input with
  | .ok tokens => .ok (tokens.filter fun t => t.val != .placeholder)
  | .error e => .error e

/-- Like `scanLoop` but returns the full final `ScannerState` (including
    collected comments) rather than just the token array. -/
@[yaml_spec "9.2" 211 "l-yaml-stream"]
def scanLoopFull (s : ScannerState) (fuel : Nat) : Except ScanError ScannerState :=
  match fuel with
  | 0 => .error (.fuelExhausted s.line s.col)
  | fuel' + 1 =>
    match scanNextToken s with
    | .error e => .error e
    | .ok none =>
      if s.flowLevel > 0 then
        .error (.unterminatedFlowCollection '[' s.line)
      else if s.directivesPresent then
        .error (.directiveWithoutDocument s.line)
      else
        -- Re-run skipToContent to collect trailing comments that
        -- scanNextToken_preprocess discarded when returning none.
        -- scanNextToken calls skipToContent internally, but returns
        -- none (discarding the updated state) when end-of-input is
        -- reached after comment/whitespace consumption.
        match scanLoop_checkDanglingNode s with
        | .error e => .error e
        | .ok _ =>
        match scanLoop_checkFlowValueIndent s with
        | .error e => .error e
        | .ok _ =>
        let s := match skipToContent s with | .ok s' => s' | .error _ => s
        let final := unwindIndents s (-1)
        let final := final.emit .streamEnd
        .ok final
    | .ok (some s') => scanLoopFull s' fuel'
termination_by fuel

/-- Scan with comment preservation.

    Returns both the filtered token array and the collected comments
    (each as position × text). Comments are collected as a side-channel
    during scanning — they do not appear in the token array.

    The token array is identical to `scanFiltered`; comments are the
    additional information. -/
@[yaml_spec "9.2" 211 "l-yaml-stream",
  yaml_spec "6.6" 75 "c-nb-comment-text"]
def scanWithComments (input : String) :
    Except ScanError (Array (Positioned YamlToken) × Array (YamlPos × String)) :=
  let s := ScannerState.mk' input
  let s := s.emit .streamStart
  let s := match s.peek? with
    | some '\uFEFF' => s.consumeBOM
    | _ => s
  let fuel := input.utf8ByteSize + 1
  match scanLoopFull s (fuel * 4) with
  | .ok final =>
    let tokens := final.tokens.filter fun t => t.val != .placeholder
    .ok (tokens, final.comments)
  | .error e => .error e

end L4YAML.Scanner

end Blanket
