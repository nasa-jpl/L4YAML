/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.State


public meta import L4YAML.Spec.YamlSpec
@[expose] public section Blanket

/-!
# Scanner — Token-Stream Queries

Read-only queries over the emitted token array: the last/penultimate REAL
(non-placeholder) token, the trailing `[96] c-ns-properties` run, and the
same-line structural predicates the indicator scanners consult (item 48
moved these out of `Scanner.lean` so `SimpleKey.lean` can read them — same
`L4YAML.Scanner` namespace, so every downstream reference and proof is
unchanged).
-/

namespace L4YAML.Scanner

open L4YAML

/-- Find the last non-placeholder token value, skipping reservation slots.
    Returns `none` if there are no real tokens. -/
def lastRealTokenVal? (tokens : Array (Positioned YamlToken)) : Option YamlToken :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    let tok1 := tokens[lastIdx]!.val
    if tok1 == .placeholder && lastIdx > 0 then
      let tok2 := tokens[lastIdx - 1]!.val
      if tok2 == .placeholder && lastIdx > 1 then
        some (tokens[lastIdx - 2]!.val)
      else some tok2
    else some tok1
  else none

/-- The index of the token `lastRealTokenVal?` reads, or `none` when there is no
    real token.  Split out so `penultRealTokenVal?` can restart the same
    placeholder skip from strictly before it. -/
def lastRealTokenIdx? (tokens : Array (Positioned YamlToken)) : Option Nat :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    if tokens[lastIdx]!.val == .placeholder && lastIdx > 0 then
      if tokens[lastIdx - 1]!.val == .placeholder && lastIdx > 1 then
        some (lastIdx - 2)
      else some (lastIdx - 1)
    else some lastIdx
  else none

/-- The real token *before* the one `lastRealTokenVal?` reads, skipping
    placeholder reservation slots the same way.  `none` if there is no second
    real token. -/
def penultRealTokenVal? (tokens : Array (Positioned YamlToken)) : Option YamlToken :=
  match lastRealTokenIdx? tokens with
  | some i => lastRealTokenVal? (tokens.extract 0 i)
  | none => none

/-- `lastRealTokenVal?`'s positioned twin: the whole token, not just its value.
    Added by item 9k, whose test is about *where* the token sits. -/
def lastRealToken? (tokens : Array (Positioned YamlToken)) :
    Option (Positioned YamlToken) :=
  if tokens.size > 0 then
    let lastIdx := tokens.size - 1
    let tok1 := tokens[lastIdx]!
    if tok1.val == .placeholder && lastIdx > 0 then
      let tok2 := tokens[lastIdx - 1]!
      if tok2.val == .placeholder && lastIdx > 1 then
        some tokens[lastIdx - 2]!
      else some tok2
    else some tok1
  else none

/-- `penultRealTokenVal?`'s positioned twin. -/
def penultRealToken? (tokens : Array (Positioned YamlToken)) :
    Option (Positioned YamlToken) :=
  match lastRealTokenIdx? tokens with
  | some i => lastRealToken? (tokens.extract 0 i)
  | none => none

/-- The trailing run of node-property tokens, most recent first.

    §6.9 [96] `c-ns-properties` admits at most one anchor and one tag, so a
    *legal* run is at most two tokens long; the run is therefore read with two
    lookbacks and capped there.  A third property is rejected by the same test
    applied at the second — `&a !t &b` fails because the run `[!t, &a]` visible
    at `&b` already carries an anchor. -/
def trailingPropertyRun (tokens : Array (Positioned YamlToken)) : List YamlToken :=
  match lastRealTokenVal? tokens with
  | some t1 =>
    if t1.isNodeProperty then
      match penultRealTokenVal? tokens with
      | some t2 => if t2.isNodeProperty then [t1, t2] else [t1]
      | none => [t1]
    else []
  | none => []

/-! ### The trailing node run (§9.2's dangling node) -/

/-- The previous REAL token's index, strictly before `i`, skipping the
    reservation placeholders `saveSimpleKey` pushes.

    `lastRealTokenVal?` above skips at most two, which is exactly one save's
    reservation and is all its callers need.  This walk is unbounded because a
    RUN's start can sit behind an arbitrary number of them, and it is
    structurally recursive on `i`, so it is total. -/
def prevRealIdx? (tokens : Array (Positioned YamlToken)) : Nat → Option Nat
  | 0 => none
  | i + 1 => if tokens[i]!.val == .placeholder then prevRealIdx? tokens i else some i

/-- Walking the token array BACKWARD from `j`, the index of the flow OPEN that
    matches a close, with `d` further closes still to balance (item 159).

    A complete `[137] c-flow-sequence` / `[140] c-flow-mapping` is a NODE whose
    body is every token from its open to its close, so a run that ends in a
    close has to be read back across the whole collection — `prevRealIdx?`
    alone reaches only the element in front of the `]`.  The array is balanced
    by construction at block level (`scanNextToken_dispatchFlowIndicators`
    refuses a close with nothing open and a close that does not match the
    innermost open), so the walk always finds its partner; `none` is the
    unreachable arm.

    Structurally recursive on the index, so it is total — the same shape, and
    for the same reason, as `sameIndentSequenceOpenLoop`. -/
@[yaml_spec "7.4.1" 137 "c-flow-sequence",
  yaml_spec "7.4.2" 140 "c-flow-mapping"]
def flowOpenIdxLoop (tokens : Array (Positioned YamlToken)) (d : Nat) :
    Nat → Option Nat
  | 0 => none
  | j + 1 =>
    let t := tokens[j]!.val
    if t.isFlowClose then flowOpenIdxLoop tokens (d + 1) j
    else if t.isFlowOpen then
      match d with
      | 0 => some j
      | d' + 1 => flowOpenIdxLoop tokens d' j
    else flowOpenIdxLoop tokens d j

/-- `flowOpenIdxLoop` started just before the close at index `i`. -/
def flowOpenIdx? (tokens : Array (Positioned YamlToken)) (i : Nat) : Option Nat :=
  flowOpenIdxLoop tokens 0 i

/-- The `[96]` run standing in front of index `i`, as the index that run STARTS
    at — `i` itself when the token in front of it is not a property.  §6.9
    admits at most one anchor and one tag, so the walk-back is capped at two:
    the same cap, for the same reason, as `trailingPropertyRun`'s two
    lookbacks. -/
@[yaml_spec "6.9" 96 "c-ns-properties"]
def propsRunStart (tokens : Array (Positioned YamlToken)) (i : Nat) : Nat :=
  match prevRealIdx? tokens i with
  | some j =>
    if tokens[j]!.val.isNodeProperty then
      match prevRealIdx? tokens j with
      | some k => if tokens[k]!.val.isNodeProperty then k else j
      | none => j
    else i
  | none => i

/-- The trailing `[96]* ns-flow-content?` run at the end of the token array: the
    index it STARTS at, paired with the index of the real token before it.
    `none` when the array does not end in a node run at all.

    §6.9 admits at most one anchor and one tag, so the property walk-back is
    capped at two — the same cap, for the same reason, as
    `trailingPropertyRun`'s two lookbacks.

    **The third arm is a flow COLLECTION** (item 159).  `[161] ns-flow-node`
    offers `ns-flow-content`, and that is a flow collection as readily as a
    scalar — but a collection is not one token, so a run whose body is one ends
    the array in a `]`/`}` and the first two arms report no run at all.  That is
    why `a: 1⏎&p [b]` scanned clean while `a: 1⏎&p b` did not, and only
    `TokenParser`'s `validNextToken` refused it, at the run's start.  The close
    is read back to its own open (`flowOpenIdx?`) and the property walk-back
    continues from there, so the run this reports starts where the parser
    reports: at `&p`. -/
@[yaml_spec "7.1" 161 "ns-flow-node"]
def trailingNodeRun? (tokens : Array (Positioned YamlToken)) :
    Option (Nat × Option Nat) :=
  match prevRealIdx? tokens tokens.size with
  | none => none
  | some i =>
    let t := tokens[i]!.val
    if t.isNodeProperty then
      -- A property run with no body of its own (`&p`, `&p !t`).
      let st := match prevRealIdx? tokens i with
                | some j => if tokens[j]!.val.isNodeProperty then j else i
                | none => i
      some (st, prevRealIdx? tokens st)
    else if t.isNodeBody then
      let st := match prevRealIdx? tokens i with
                | some j =>
                  if tokens[j]!.val.isNodeProperty then
                    match prevRealIdx? tokens j with
                    | some k => if tokens[k]!.val.isNodeProperty then k else j
                    | none => j
                  else i
                | none => i
      some (st, prevRealIdx? tokens st)
    else if t.isFlowClose then
      match flowOpenIdx? tokens i with
      | none => none
      | some o =>
        let st := propsRunStart tokens o
        some (st, prevRealIdx? tokens st)
    else none

/-! ### The crossed over-full property block (§9.2's fourth dangler, item 180)

    `[96] c-ns-properties` admits at most one anchor and one tag, so an
    ADJACENT block of property tokens holding two of one kind is never one
    run.  It can still be TWO runs — `[200] s-l+block-collection`'s optional
    properties, a break, then the first KEY's own run (`&a⏎!t &b x: 1` is
    `+MAP &a` with the key decorated `!t &b`) — but that split requires the
    excess run to resolve as an implicit key ON ITS OWN LINE, because a
    block-key context admits no break.  So at a line END the discrimination
    is over: a trailing run whose adjacent property block duplicates a kind
    has no derivation, whatever follows (measured against PyYAML 6.x at
    `yaml.parse` level, item 180's battery).  The same-line thirds never get
    this far — the push guards (`propertyRunHasAnchor`/`propertyRunHasTag`,
    items 9e/9k) refuse them at the character — so what this walk catches is
    exactly the block whose internal separation CROSSED a break.  That is the
    configuration the proof side used to carry a second stream route for, and
    reading it here is what retired the route (item 181).

    The walk is uncapped, unlike `trailingPropertyRun`'s two lookbacks: the
    cap there is the LEGAL run's arity, and this reader exists to see past
    it.  It is structurally recursive on the index, so it is total. -/

/-- Scanning DOWN the adjacent property block that ends just below index `i`
    (placeholders skipped, ended by the first real non-property):
    `(hasAnchor, hasTag, excess)` where `excess` is the LOWEST-then-first
    index whose property kind already occurs below it — the first token, in
    token order, at which the block stops being one `[96]` run.  That is the
    position `TokenParser.validNextToken` reports for these inputs. -/
@[yaml_spec "6.9" 96 "c-ns-properties"]
def propsBlockScanLoop (tokens : Array (Positioned YamlToken)) :
    Nat → Bool × Bool × Option Nat
  | 0 => (false, false, none)
  | j + 1 =>
    let t := tokens[j]!.val
    if t == .placeholder then propsBlockScanLoop tokens j
    else if t.isNodeProperty then
      let (a, tg, e) := propsBlockScanLoop tokens j
      let e' := match e with
        | some k => some k
        | none =>
          if t.isAnchorProperty && a then some j
          else if t.isTagProperty && tg then some j
          else none
      (a || t.isAnchorProperty, tg || t.isTagProperty, e')
    else (false, false, none)

/-- The excess property of the TRAILING run's adjacent block, if any: the
    block is read behind a property tail, behind a one-token body, or behind
    a flow close's own OPEN (the same three arms as `trailingNodeRun?`, item
    159's reading of `[161] ns-flow-node`).  `none` wherever the trailing
    block is one `[96]` run — one anchor and one tag at most, in either
    order, across any breaks (`!t⏎&q b` stays a single decorated scalar). -/
@[yaml_spec "6.9" 96 "c-ns-properties", yaml_spec "9.2" 211 "l-yaml-stream"]
def crossedPropsExcessIdx? (tokens : Array (Positioned YamlToken)) : Option Nat :=
  match prevRealIdx? tokens tokens.size with
  | none => none
  | some i =>
    let t := tokens[i]!.val
    if t.isNodeProperty then (propsBlockScanLoop tokens (i + 1)).2.2
    else if t.isNodeBody then (propsBlockScanLoop tokens i).2.2
    else if t.isFlowClose then
      match flowOpenIdx? tokens i with
      | none => none
      | some o => (propsBlockScanLoop tokens o).2.2
    else none

/-- `crossedPropsExcessIdx?` read as the POSITION the refusal reports — the
    excess property's own, which is where `TokenParser.validNextToken` reports
    the same inputs.  Named so the verdict's congruence lemmas can speak about
    the clause as one reading. -/
@[yaml_spec "6.9" 96 "c-ns-properties", yaml_spec "9.2" 211 "l-yaml-stream"]
def crossedPropsExcessPos? (tokens : Array (Positioned YamlToken)) : Option YamlPos :=
  match crossedPropsExcessIdx? tokens with
  | some j => some tokens[j]!.pos
  | none => none

/-! ### The run that crosses a break BELOW its start (§9.2's fifth dangler,
    item 182)

    Items 177 and 178 read Finding A at the run's START: a scalar, alias or
    `[96]`-headed run standing at an open level's own column has no
    derivation, because every alternative of `[196] s-l+block-node(n,c)` and
    `[185] s-l+block-indented(n,c)` it can head spends `s-separate(n+1)`,
    whose line-crossing branch demands `s-indent(n+1)`.

    The same separator sits INSIDE the run, between `[96]`'s properties and
    the content they decorate — and a run may start legally and cross there:
    in `k: &x⏎a` the `&x` is at column 3, where no level stands, and it is the
    CONTENT that lands at the mapping's own column 0.  The run-start reading
    cannot see it; this one reads the first token of the run that STARTS a
    line, which is where the crossed `s-separate(n+1)` is spent. -/

/-- Scanning DOWN the adjacent property block that ends just below index `i`
    (placeholders skipped, ended by the first real non-property): the position
    of the FIRST property, in token order, whose own real predecessor is a
    property on an EARLIER line.  That is `[96]`'s internal separation spent
    across a break, and the walk needs no block boundary of its own — the
    predecessor test ends it. -/
@[yaml_spec "6.7" 80 "s-separate(n,c)", yaml_spec "6.9" 96 "c-ns-properties"]
def propsBlockLineCrossLoop (tokens : Array (Positioned YamlToken)) :
    Nat → Option YamlPos
  | 0 => none
  | j + 1 =>
    let t := tokens[j]!.val
    if t == .placeholder then propsBlockLineCrossLoop tokens j
    else if t.isNodeProperty then
      match propsBlockLineCrossLoop tokens j with
      | some q => some q
      | none =>
        match prevRealIdx? tokens j with
        | some p =>
          if tokens[p]!.val.isNodeProperty && tokens[p]!.pos.line < tokens[j]!.pos.line then
            some tokens[j]!.pos
          else none
        | none => none
    else none

/-- The trailing run's own break crossing: the position of the first token, in
    token order, that starts a line the run did not start on.  The three arms
    are `crossedPropsExcessIdx?`'s — a property tail, a one-token body, a flow
    close read back to its own open — because the block this reads is the same
    block, and reading it at the CLOSE is what keeps the park's verdict and
    the close's the same one.

    The block's internal crossing comes first, in token order; the body's own
    crossing is the second reading and belongs to the body arm alone.  A flow
    collection's INTERIOR is not read here: §8.1's floor owns it
    (`underIndentedFlowContent`, item 172), and a flow node standing in an
    awaited slot is that reading's too. -/
@[yaml_spec "6.7" 80 "s-separate(n,c)", yaml_spec "9.2" 211 "l-yaml-stream"]
def runLineCrossPos? (tokens : Array (Positioned YamlToken)) : Option YamlPos :=
  match prevRealIdx? tokens tokens.size with
  | none => none
  | some i =>
    let t := tokens[i]!.val
    if t.isNodeProperty then propsBlockLineCrossLoop tokens (i + 1)
    else if t.isNodeBody then
      match propsBlockLineCrossLoop tokens i with
      | some q => some q
      | none =>
        match prevRealIdx? tokens i with
        | some p =>
          if tokens[p]!.val.isNodeProperty && tokens[p]!.pos.line < tokens[i]!.pos.line then
            some tokens[i]!.pos
          else none
        | none => none
    else if t.isFlowClose then
      match flowOpenIdx? tokens i with
      | none => none
      | some o => propsBlockLineCrossLoop tokens o
    else none

/-- `runLineCrossPos?` read as the POSITION the refusal reports: the crossing
    token's own, kept only where it lands at an open level's own column —
    which is where `s-indent(n+1)` fails and where PyYAML's scanner reports
    the same inputs.  Named so the verdict's `none` lemmas can speak about the
    clause as one reading, the way `crossedPropsExcessPos?` is. -/
@[yaml_spec "6.7" 80 "s-separate(n,c)", yaml_spec "9.2" 211 "l-yaml-stream"]
def runLineCrossDanglingPos? (tokens : Array (Positioned YamlToken))
    (indents : Array IndentEntry) : Option YamlPos :=
  match runLineCrossPos? tokens with
  | some q => if indents.any (fun e => e.column == (q.col : Int)) then some q else none
  | none => none

/-! ### The `-` at a block mapping's own column (§9.2's third dangler) -/

/-- The index of the real token that HOLDS THE SLOT the trailing node run would
    fill: the last real token, read past a `[96] c-ns-properties` run of at most
    two.  `none` when the array is nothing but properties, or empty.

    §6.9 admits one anchor and one tag, so the walk-back is capped at two — the
    same cap, for the same reason, as `trailingPropertyRun`'s two lookbacks. -/
@[yaml_spec "6.9" 96 "c-ns-properties"]
def slotHolderIdx? (tokens : Array (Positioned YamlToken)) : Option Nat :=
  match prevRealIdx? tokens tokens.size with
  | none => none
  | some i =>
    if tokens[i]!.val.isNodeProperty then
      match prevRealIdx? tokens i with
      | none => none
      | some j => if tokens[j]!.val.isNodeProperty then prevRealIdx? tokens j else some j
    else some i

/-- A node is still AWAITED: the slot holder offers one.

    `YamlToken.offersNodeSlot` is item 133's — the three indicators followed by
    `s-l+block-node` / `s-l+block-indented` — and it is the same predicate for
    the same reason here: after `:`, after `?`, and after `-`, the node that
    fills the slot may be a zero-indented block sequence (`[185]`'s
    `s-l+block-indented(n,c)` reaches `[183] l+block-sequence(n)` with the
    detected `m` allowed to be 0 at a mapping's own indent — suite 6PBE). -/
@[yaml_spec "8.2.2" 187 "l+block-mapping",
  yaml_spec "8.2.1" 183 "l+block-sequence"]
def nodeSlotAwaited (tokens : Array (Positioned YamlToken)) : Bool :=
  match slotHolderIdx? tokens with
  | some i => tokens[i]!.val.offersNodeSlot
  | none => false

/-- Walking the token array BACKWARD from `i`: does a `.blockEntry` at exactly
    column `c` stand before any `.key` / `.value` at a column ≤ `c`?

    That is the question "is a same-indent sequence still open here?", and it is
    the one §9.2 mechanism whose test is a WALK rather than a predicate on the
    array's tail: a zero-indented sequence's entries are interleaved with the
    entries of the collections nested inside them, so the previous entry of THIS
    sequence can sit arbitrarily far back.  The walk is bounded on the other
    side by the mapping level's own opener: `pushMappingIndent` runs at the
    column of a `.key` (or of the `.value` that opens a keyless entry), so a
    `.key`/`.value` at a column ≤ `c` is always reached, and everything before
    it belongs to a collection this `-` cannot continue.

    Structurally recursive on `i`, so it is total. -/
@[yaml_spec "8.2.1" 183 "l+block-sequence"]
def sameIndentSequenceOpenLoop (tokens : Array (Positioned YamlToken)) (c : Int) :
    Nat → Bool
  | 0 => false
  | j + 1 =>
    let t := tokens[j]!
    if t.val == .blockEntry && (t.pos.col : Int) == c then true
    else if (t.val == .key || t.val == .value) && (t.pos.col : Int) <= c then false
    else sameIndentSequenceOpenLoop tokens c j

/-- `sameIndentSequenceOpenLoop` from the end of the array. -/
@[yaml_spec "8.2.1" 183 "l+block-sequence"]
def sameIndentSequenceOpen (tokens : Array (Positioned YamlToken)) (c : Int) : Bool :=
  sameIndentSequenceOpenLoop tokens c tokens.size

/-! ### When token adjacency means "same property run" (items 9e and 9k)

    Token adjacency means "same node" only when nothing that emits no token can
    intervene.  Two contexts guarantee that, and the three tests below are the
    disjunction of them.

    **Inside a flow collection** (item 9e).  `[137]`/`[140]` admit
    `ns-flow-node` only, so no block collection can open between two tokens, and
    two adjacent property tokens necessarily belong to one node — at any
    distance, across as many lines as the collection spans.

    **On one line** (item 9k).  In block context the flow argument fails: a
    block collection opens without a token of its own, so adjacent property
    tokens can belong to different nodes.

    ```yaml
    &mapping
    &key [ &item a, b, c ]: value    # 26DV / suite: &mapping is on the MAPPING
    top3: &node3
      *alias1 : scalar3              # &node3 is on the nested mapping, not on *alias1
    ```

    Both are valid, and both put an `anchor` directly before an `anchor`/`alias`
    in the token stream — so the tests may not be ungated.  But both also put
    the two tokens on DIFFERENT lines, and that is not an accident: `[200]
    s-l+block-collection(n,c)` reads its properties then `s-l-comments`, whose
    `[77] s-b-comment` is `b-non-content` or end of input.  A block collection's
    properties are therefore *always* separated from its content by a break, so
    a property token and a property token on the SAME line cannot be split by a
    block opening.

    Same-line adjacency is a sound approximation, not an exact one: a run
    already broken across lines is not read (`&a⏎!t &b c` keeps only `!t`), so
    the block-context tests under-reject rather than over-reject.  The flow
    disjunct keeps the unrestricted run, which is why widening costs the
    in-flow case nothing. -/

/-- `trailingPropertyRun`, truncated at a line change: the same two-token
    lookback, keeping only tokens that start on `line`.  This is the run the
    BLOCK-context half of the three tests below reads. -/
@[yaml_spec "6.9" 96 "c-ns-properties",
  yaml_spec "8.2.3" 200 "s-l+block-collection(n,c)",
  yaml_spec "6.6" 77 "s-b-comment"]
def trailingPropertyRunOnLine (tokens : Array (Positioned YamlToken)) (line : Nat) :
    List YamlToken :=
  match lastRealToken? tokens with
  | some t1 =>
    if t1.val.isNodeProperty && t1.pos.line == line then
      match penultRealToken? tokens with
      | some t2 =>
        if t2.val.isNodeProperty && t2.pos.line == line then [t1.val, t2.val] else [t1.val]
      | none => [t1.val]
    else []
  | none => []

/-- Is the last real token a node property that starts on `line`? -/
def lastTokenIsNodePropertyOnLine (tokens : Array (Positioned YamlToken)) (line : Nat) :
    Bool :=
  match lastRealToken? tokens with
  | some t => t.val.isNodeProperty && t.pos.line == line
  | none => false

end L4YAML.Scanner

end Blanket
