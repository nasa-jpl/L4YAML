# Initiative 3 — Append-Only Token Stream

**Status**: Phase J.0/J.1/J.2 complete; **Phase J.3 in progress
(started 2026-04-26)** on branch `feature/append-only`.  Main stays
in a usable state until the feature branch merges back.
**Driver**: Tier 2 emitter-scannability work hit a structural blocker
that traces to a deliberate architectural choice (`02-architecture.md`
§Append-only token stream).  This initiative revises that choice.

## Motivating defect

`saveSimpleKey` reserves two slots in `tokens` and records the
`tokenIndex`.  When `:` is later seen, `scanValuePrepare` mutates one
of those slots in place via `setIfInBounds`, promoting `.placeholder`
to `.key`.  This in-place mutation has two proof-engineering costs:

1. **Filter is non-monotone.**  A `scanNextToken` step that runs
   `scanValuePrepare` increases `tokens.filter (·.val != .placeholder)`
   by *more than 1* — the promoted placeholder gains, plus any new
   content tokens gain.  Every prefix-preservation lemma
   (`SimpleKeyAboveFloor`, `ScanChain_filtered_prefix`, …) exists to
   defend the prefix against this retroactive promotion.

2. **No invariant captures forward-looking stability.**  For
   `emitList` chains, the spare placeholder slot at `simpleKey.tokenIndex
   + 1` is *never* promoted (no top-level `:`), but proving this
   requires structural induction over emitter output — exactly the
   work that Tier 2 Turn 2 surfaced.

The original architecture choice (`02-architecture.md` §Append-only)
optimised for **raw-index stability** (no `Array.insertAt`-induced
shifts), trading away **filter monotonicity**.  This initiative
preserves both.

## Proposed architecture

`tokens` becomes strictly append-only — no `setIfInBounds`, no
`Array.insertAt`.  Pending key reservations move to a parallel
side-channel.  The final type (refined by Q2 below) is:

```lean
inductive ResolutionKind where
  | unresolved   -- discarded if line ends without `:`
  | keyOnly      -- flow context; or block with col ≤ currentIndent
  | blockMappingStartAndKey  -- block context with col > currentIndent
deriving Repr, BEq, Inhabited

structure PendingKeyEntry where
  insertBeforeIdx : Nat   -- linearisation slot: synthetic key(s) splice
                          -- immediately before `tokens[insertBeforeIdx]`
  pos : YamlPos
  endLine : Nat
  kind : ResolutionKind
deriving Repr, BEq, Inhabited

structure ScannerState where
  tokens : Array (Positioned YamlToken)        -- APPEND-ONLY
  pendingKeys : Array PendingKeyEntry          -- APPEND-ONLY (kind flips in place)
  -- removed: simpleKey, simpleKeyStack
  pendingKeyActive : Option Nat               -- index into pendingKeys for current candidate
  pendingKeyStack : Array (Option Nat)         -- saved actives across flow nesting
  ...
```

`saveSimpleKey` appends a new `PendingKeyEntry` with
`kind := .unresolved` and `insertBeforeIdx := tokens.size` (snapshot
*before* the scalar emit, so the synthetic key splices immediately
before the scalar's slot).  `scanValuePrepare` flips
`pendingKeys[active].kind` to `.keyOnly` or
`.blockMappingStartAndKey` based on the same column-vs-indent test
the current code uses.  At `scanFiltered` linearisation time,
non-`unresolved` entries are spliced into the output stream at their
`insertBeforeIdx` positions, producing the parser's expected token
order.

### Properties this delivers

- **Filter monotonicity**: each `scanNextToken` step appends to
  `tokens` and/or `pendingKeys`.  `setIfInBounds` is gone; the only
  in-place writes are to `pendingKeys[i].resolved`, which doesn't
  shift indices in either array.
- **Linearised view is a function** of the pair `(tokens,
  pendingKeys)`, computed once at output time.  All parser-facing
  proofs reason about the linearised view; scanner-internal proofs
  reason about the underlying pair.
- **`Array.insertAt` is still avoided** in the hot path — splicing
  happens once per `scanFiltered` call, not per scanner step.

### Open design questions for Phase J.0

The four questions below were resolved in a 2026-04-26 review of
`L4YAML/Spec/Grammar.lean`, `L4YAML/Token/Token.lean`,
`L4YAML/Scanner/Indent.lean`, and `L4YAML/Scanner/Scanner.lean`.  The
spec evidence makes Path C cheaper than the initial estimate suggested.

#### Q1 — Linearisation incrementality

**Resolved: one-shot at `scanFiltered` is sufficient.**

Spec evidence:
- `Spec/Grammar.lean` §Token Stream Contract — `ValidTokenStream`
  states two structural constraints (boundary tokens, monotone
  positions); neither requires online linearisation.
- `Scanner/Scanner.lean` `scanFiltered` is already the natural seam:
  it's a one-shot post-pass over the result of `scan`.  Today it
  filters placeholders; in the new model it splices pendingKeys.

Internal scanner lookbacks (`lastRealTokenVal?`, see Q4) are answered
correctly by reading raw `tokens` because pendingKeys are virtual
until linearisation — see Q4 for why.

Implication: `pendingKeys` does not need an ordering invariant beyond
"`insertBeforeIdx` values cover a strict subset of `[0, tokens.size]`".

#### Q2 — Block-context double-token expansion

**Resolved: one `PendingKeyEntry` with a resolution-kind field;
linearisation expands.**

Spec evidence:
- `Token/Token.lean` documents `.blockMappingStart` as a *virtual*
  token (no character representation) generated by the scanner from
  indentation tracking, distinct from `.key` (production [5]
  `c-mapping-key`).  Two distinct token types, but always emitted
  together at the same source position when block-mapping-start is
  implicit.
- The current `scanValuePrepare` decides `.blockMappingStart + .key`
  vs `.key`-alone based on `simpleKey.pos.col > currentIndent` — a
  *resolve-time* decision.  In the new model this becomes the kind
  flag on the entry.
- `Spec/Grammar.lean` `ValidTokenStream.positionsOrdered` uses `≤`
  (tied positions allowed), so emitting two tokens at the same
  source offset is spec-compliant.

Recommended type: see the `ResolutionKind` / `PendingKeyEntry` block
in §Proposed architecture above (the resolution of this question is
what justified that final form).  Linearisation walks `tokens` in
order and, before emitting `tokens[k]`, checks whether any pendingKey
has `insertBeforeIdx = k` and a non-`unresolved` kind, splicing
accordingly.

#### Q3 — `unwindIndents` interaction

**Resolved: no refactor needed — already append-only.**

Spec evidence: `Scanner/Indent.lean` `unwindIndentsLoop` calls
`s.emit .blockEnd` (= pure `tokens.push`) and `indents.pop` (a
separate stack).  No `setIfInBounds`, no insertion, no interaction
with `simpleKey`.

Same applies to `pushSequenceIndent` / `pushMappingIndent` (both
pure `emit + indents.push`).  The entire indentation-management
module is already aligned with Path C's invariants and survives the
refactor unchanged.

This is a meaningful scope reduction: virtual block tokens
(`blockSequenceStart`, `blockMappingStart` *from indent push*,
`blockEnd`) are already structural pushes to `tokens`; only the
`scanValuePrepare`-driven `.blockMappingStart + .key` pair (the
*implicit* block-mapping-start from a simple key) goes through
pendingKeys.

#### Q4 — `lastRealTokenVal?` and similar lookbacks

**Resolved: lookbacks read raw `tokens`; the function simplifies.**

Spec evidence: `lastRealTokenVal?` (`Scanner/Scanner.lean` line ~225)
exists *because* placeholders pollute the token array — it skips up
to two trailing placeholders to find the last "real" token.  In the
new model placeholders never enter `tokens`, so the function
collapses to `tokens.back?.map (·.val)`.

The single call site (`scanFlowEntry`) checks "is the previous token
`[`, `{`, or `,`?" — this question is correctly answered by reading
raw `tokens`, because:
- A pendingKey is virtual until linearisation; it represents a
  *future* `.key` insertion, not a past committed token.
- The scanner only validates against committed tokens (what's
  actually been emitted as real characters in the input stream).
- A resolved pendingKey at `insertBeforeIdx = tokens.size` would
  splice `.key` after the last token in linearised view — but the
  scanner-internal "what did I just emit?" question is about the
  most recently appended raw token, which is correct.

Implication: rename `lastRealTokenVal?` to `lastTokenVal?` (lose the
"Real" qualifier — there are no fake tokens anymore) and simplify
its body.  All existing call-site reasoning carries through.

### Other findings

- **`Positioned` already carries `endPos`** (`Token/Token.lean` line
  60) — every token has a span, not just a start.  PendingKey
  entries can set `endPos = pos` (zero-width) like other virtual
  tokens.
- **Virtual tokens are an established category** in the type system
  (`YamlToken.isVirtual`).  Adding a side-channel for one more
  virtual category (pending-then-resolved keys) is consistent with
  existing design.
- **Spec only constrains source-position monotonicity**, not
  array-index order.  This means linearisation has freedom in how it
  orders tied-position tokens, as long as the parser's downstream
  expectations are met.

## Linearisation algorithm

`linearise : Array (Positioned YamlToken) → Array PendingKeyEntry →
Array (Positioned YamlToken)` is invoked once by `scanFiltered`.
Pseudo-Lean:

```lean
def expandKind (e : PendingKeyEntry) : Array (Positioned YamlToken) :=
  match e.kind with
  | .unresolved              => #[]
  | .keyOnly                 =>
      #[⟨e.pos, e.pos, .key⟩]
  | .blockMappingStartAndKey =>
      #[⟨e.pos, e.pos, .blockMappingStart⟩,
        ⟨e.pos, e.pos, .key⟩]

def linearise (tokens : Array (Positioned YamlToken))
              (pendingKeys : Array PendingKeyEntry)
              : Array (Positioned YamlToken) := Id.run do
  let mut out : Array (Positioned YamlToken) := #[]
  let mut p : Nat := 0
  for k in [0 : tokens.size] do
    while h : p < pendingKeys.size ∧ pendingKeys[p].insertBeforeIdx = k do
      out := out ++ expandKind pendingKeys[p]
      p := p + 1
    out := out.push tokens[k]
  -- Pending keys with insertBeforeIdx = tokens.size (rare: candidate at end of input
  -- with no follow-up) are flushed after the loop.
  while p < pendingKeys.size do
    out := out ++ expandKind pendingKeys[p]
    p := p + 1
  return out
```

### Invariants enforced by construction

1. **Strict-monotone insertion points.**  `pendingKeys.map
   (·.insertBeforeIdx)` is strictly monotone, because every
   `saveSimpleKey` snapshots `tokens.size` and is *immediately*
   followed by a scalar emit that bumps `tokens.size`.  No two
   pendingKeys share an `insertBeforeIdx`.  Consequence: the simple
   linear walk above is unambiguous; no sort needed.
2. **In-bounds.**  `e.insertBeforeIdx ≤ tokens.size` for every entry,
   because the snapshot is taken at `tokens.size` and `tokens` only
   grows.
3. **No double-resolution.**  At most one transition per entry:
   `.unresolved → .keyOnly` or `.unresolved → .blockMappingStartAndKey`.
   The `pendingKeyActive` discipline (set at `saveSimpleKey`, cleared
   at `scanValuePrepare` / line-end / flow-nesting boundary) ensures
   only the active entry is mutable.
4. **Spec-faithful position order.**  `expandKind` emits synthetic
   tokens at `e.pos = e.endPos`, immediately before
   `tokens[insertBeforeIdx]` (whose position is ≥ `e.pos`).  Combined
   with `Spec/Grammar.lean`'s `≤` ordering on positions, the output
   satisfies `ValidTokenStream.positionsOrdered`.

These four invariants are the J.3 proof targets that make
`ScanChain_filtered_prefix` and friends fall out trivially: filter is
no longer a runtime predicate over a mutated array but a
compile-time-correct splice.

## Worked example: `{a: [1, 2], b: c}`

Single-line input, offsets `0..16` inclusive.  All positions are
`(line=0, col=offset, offset=offset)`; abbreviated `@n` below.

### Scanner trace

| # | Event                          | tokens delta            | pendingKeys delta                                   | active |
|---|--------------------------------|-------------------------|------------------------------------------------------|--------|
| 0 | start of input                 | push `streamStart@0`    | —                                                    | none   |
| 1 | `{` at col 0                   | push `flowMappingStart@0` | —                                                  | none   |
| 2 | `a` at col 1: `saveSimpleKey`  | (snapshot size = 2)     | append `{ibi=2, pos=1, kind=unresolved}` (idx 0)     | some 0 |
| 2'| emit scalar                    | push `scalar("a")@1`    | —                                                    | some 0 |
| 3 | `:` at col 2: `scanValuePrepare` | push `valueIndicator@2` | flip `pendingKeys[0].kind := keyOnly`             | none   |
| 4 | `[` at col 4 (flow-seq start)  | push `flowSequenceStart@4` | — (push `none` to `pendingKeyStack`)              | none   |
| 5 | `1` at col 5: `saveSimpleKey`  | (snapshot size = 5)     | append `{ibi=5, pos=5, kind=unresolved}` (idx 1)     | some 1 |
| 5'| emit scalar                    | push `scalar("1")@5`    | —                                                    | some 1 |
| 6 | `,` at col 6 (flow-entry)      | push `flowEntry@6`      | — (idx 1 stays unresolved; will be filtered)         | none   |
| 7 | `2` at col 8: `saveSimpleKey`  | (snapshot size = 7)     | append `{ibi=7, pos=8, kind=unresolved}` (idx 2)     | some 2 |
| 7'| emit scalar                    | push `scalar("2")@8`    | —                                                    | some 2 |
| 8 | `]` at col 9 (flow-seq end)    | push `flowSequenceEnd@9` | — (pop `pendingKeyStack`; idx 2 stays unresolved)   | none   |
| 9 | `,` at col 10                  | push `flowEntry@10`     | —                                                    | none   |
|10 | `b` at col 12: `saveSimpleKey` | (snapshot size = 10)    | append `{ibi=10, pos=12, kind=unresolved}` (idx 3)   | some 3 |
|10'| emit scalar                    | push `scalar("b")@12`   | —                                                    | some 3 |
|11 | `:` at col 13: `scanValuePrepare` | push `valueIndicator@13` | flip `pendingKeys[3].kind := keyOnly`            | none   |
|12 | `c` at col 15: `saveSimpleKey` | (snapshot size = 12)    | append `{ibi=12, pos=15, kind=unresolved}` (idx 4)   | some 4 |
|12'| emit scalar                    | push `scalar("c")@15`   | —                                                    | some 4 |
|13 | `}` at col 16 (flow-map end)   | push `flowMappingEnd@16` | — (pop; idx 4 stays unresolved)                     | none   |
|14 | end of input                   | push `streamEnd@17`     | —                                                    | none   |

### Final state

```
tokens = [
   0: streamStart@0,
   1: flowMappingStart@0,
   2: scalar("a")@1,
   3: valueIndicator@2,
   4: flowSequenceStart@4,
   5: scalar("1")@5,
   6: flowEntry@6,
   7: scalar("2")@8,
   8: flowSequenceEnd@9,
   9: flowEntry@10,
  10: scalar("b")@12,
  11: valueIndicator@13,
  12: scalar("c")@15,
  13: flowMappingEnd@16,
  14: streamEnd@17
]   -- size 15, append-only throughout

pendingKeys = [
  0: { ibi=2,  pos=1,  kind=keyOnly    },   -- "a" → key
  1: { ibi=5,  pos=5,  kind=unresolved },   -- "1" → discarded
  2: { ibi=7,  pos=8,  kind=unresolved },   -- "2" → discarded
  3: { ibi=10, pos=12, kind=keyOnly    },   -- "b" → key
  4: { ibi=12, pos=15, kind=unresolved }    -- "c" → discarded
]
```

Note `pendingKeys.insertBeforeIdx` is `[2, 5, 7, 10, 12]` — strictly
monotone (invariant 1).

### Linearised output

`linearise tokens pendingKeys` produces:

```
streamStart@0
flowMappingStart@0
key@1                 ← spliced from pendingKeys[0] before tokens[2]
scalar("a")@1
valueIndicator@2
flowSequenceStart@4
scalar("1")@5
flowEntry@6
scalar("2")@8
flowSequenceEnd@9
flowEntry@10
key@12                ← spliced from pendingKeys[3] before tokens[10]
scalar("b")@12
valueIndicator@13
scalar("c")@15
flowMappingEnd@16
streamEnd@17
```

This is byte-for-byte the same stream the parser sees today after
`scanFiltered` filters out unresolved placeholders — except produced
without a single in-place token mutation.

### Comparison with the current model

The current scanner, on the same input, would produce a `tokens`
array with **10 placeholder slots** interleaved (2 reserved per
`saveSimpleKey`, 5 saves total).  Two of those slots get promoted to
`.key` via `setIfInBounds`; the remaining eight are filtered out by
`scanFiltered`.  The two promotions are exactly the events that
break filter-monotonicity in the proof corpus.

In the new model: zero placeholder slots, zero in-place token writes,
five appends to `pendingKeys` (a separate array), and two
`kind`-field flips on a structure that doesn't participate in the
output stream until the one-shot `linearise` call.

## Phased migration plan

### Branching strategy

All J.1+ work lands on `feature/append-only`, branched from `main`
at the J.0-approval point.  `main` stays buildable and proof-clean
throughout.  The feature branch carries the type migration, the
proof corpus rewrite, and any temporary sorry inflation; it merges
back only at J.4 once the validation gate is green (sorry count
strictly less than pre-initiative).

J.0 deliverables (this doc) commit on `feature/append-only` so the
plan and the implementation share a single history.  Cherry-picking
the doc back to `main` is acceptable if the design needs to be
visible there before the merge.

### Phase J.0 — Design [✓ completed 2026-04-26 `a199cae4`]

**Deliverable**: `Blueprint/07-initiative-3-append-only.md` (this
doc) updated with concrete answers to the open design questions
(§Q1–Q4), the linearisation algorithm spec with its four invariants
(§Linearisation algorithm), and a worked example through
`{a: [1, 2], b: c}` showing the new `(tokens, pendingKeys)` pair at
every scanner step plus the linearised output (§Worked example).

**Status**: approved 2026-04-26.  Execution proceeds on
`feature/append-only` starting at Phase J.1.

**Validation gate** (✓ satisfied 2026-04-26): principal verifier
reviewed and approved `ResolutionKind` / `PendingKeyEntry`, the
`linearise` algorithm, and the `{a: [1, 2], b: c}` worked example.
Code changes proceed on `feature/append-only`.

### Phase J.1 — Type definitions and stub [✓ completed 2026-04-26 `f1d089bd`]

**Deliverable**: New `ScannerState` definition compiles.  All
existing scanner submodule signatures updated.  Bodies are `sorry` /
`stub` placeholders.  Linearisation function defined with proofs of
its basic properties (`linearise_append`, `linearise_resolved`).

**Validation gate**: project compiles with stubs; type-check passes.
Existing proof files don't yet build.

**Status**: ✓ satisfied at commit `f1d089bd` ("Initiative 3 J.1:
pendingKeys side channel + linearise scaffolding").
`PendingKeyEntry` / `ResolutionKind` defined; `ScannerState` extended
with `pendingKeys` / `pendingKeyActive` / `pendingKeyStack`;
`linearise` function implemented with three property lemmas
(`linearise_append_token`, `linearise_append_unresolved`,
`linearise_resolved`) carrying `sorry` against J.3.

### Phase J.2 — Scanner submodule migration [✓ completed 2026-04-26]

Port submodules in dependency order:

1. `Scanner/State.lean` — accessors, `peek?`, `advance`, `emit`.
2. `Scanner/SimpleKey.lean` — `saveSimpleKey`, `scanValuePrepare`
   (the heart of the change).
3. `Scanner/Whitespace.lean`, `Indent.lean`, `Comment.lean`, …
4. `Scanner/Scalar.lean`, `Scanner/Scanner.lean` — the dispatch
   pipeline.
5. `scanFiltered` — invoke linearisation.

Each submodule lands with its previous `ScannerCorrectness` proofs
ported (or re-stubbed with sorries to be discharged in J.3).

**Validation gate per submodule**: file builds; no new sorries
beyond a documented manifest.

**Status (as of 2026-04-26)**:

| Step | Description | Status | Commit |
|---|---|---|---|
| 1 | `Scanner/State.lean` (accessors, helpers) | ✓ done | `f1d089bd` (with J.1) |
| 2 | `Scanner/SimpleKey.lean` (dual-write) | ✓ done | `909b8870` |
| 2.5 | `Scanner/Scanner.lean` flow open/close + endLine sync | ✓ done | `9acea6e6` |
| 3 | `Scanner/Document.lean` + `Scanner/Scalar.lean` leaf clears | ✓ done | `09fc3ec7` |
| 4 | `lastRealTokenVal?` → `lastTokenVal?` rename | ✓ done | `00bca3ee` |
| 5 | `scanFiltered` cutover (see substitution plan below) | ✓ done | `a212cdc2`, `71a86eee`, this |

Steps 1–4 are *additive* (dual-write / rename only); the cutover
itself is concentrated in step 5, sequenced into 5.0/5.1/5.2 below.

#### Phase J.2 step 5 — `scanFiltered` cutover (substitution plan)

Step 5 is the disruption point.  Steps 1–4 are additive: the
`pendingKeys` side-channel is dual-written in lockstep with every
legacy `simpleKey` / placeholder / `setIfInBounds` mutation.  Step 5
drops the legacy half wholesale and routes `scanFiltered` through
`linearise`.  The proof corpus is rebuilt against the new shape; some
lemmas vanish, some simplify, a small core gets re-proved against
`linearise`'s property lemmas.

The break is intentionally concentrated in this single step so that
J.2 steps 1–4 land against a green tree (the dual-write is
information-preserving) and J.3 starts from a single, well-defined
"all classical placeholder/setIfInBounds machinery is gone" baseline.

**Plan structure**: §5.a/§5.b/§5.c/§5.d/§5.e are *sub-sections of
this plan* (code edits / breakage cascade / sub-substep sequencing /
sorry manifest / validation gate).  §5.c then defines the *commit
sequence* as 5.0/5.1/5.2.

**Status (as of 2026-04-26)**:

| Sub-step | Description | Status | Commit |
|---|---|---|---|
| 5.0 | Code cutover (§5.a edits) — single red commit | ✓ done | `a212cdc2` |
| 5.1 | Discharge Categories A + B (§5.b) — restore green | ✓ done | `71a86eee` |
| 5.2 | yaml-test-suite golden parity (runtime check) | ✓ done | this commit |

##### 5.a Code edits (Scanner-side) [✓ landed by 5.0 `a212cdc2`]

1. **`saveSimpleKey`** — drop the two `tokens.push placeholder` calls.
   The `pendingKeys.push { …, kind := .unresolved }` survives, and
   `insertBeforeIdx := tokens.size` already points at the next
   real-token slot in the no-placeholder world (the dual-write captured
   the pre-placeholder size for exactly this reason).  The legacy
   `simpleKey := { … }` field write is *kept* — its consumers
   (`scanValueValidate`, `isValueCandidate`, scanner endLine sync) still
   read `.possible` / `.tokenIndex` / `.pos` / `.endLine`.  Removing
   them is J.4 work after every consumer is ported to `pendingKeys`.

2. **`scanValuePrepare`** — drop the three `setIfInBounds` calls.  Only
   `setPendingKeyKind` survives.  The legacy `simpleKey :=
   { possible := false }` clear stays for the same reason as above.
   The function reduces to "flip the active reservation's kind, push
   block-mapping indent if applicable, advance simpleKey state" — pure
   bookkeeping with no `tokens` mutation.

3. **`lastTokenVal?`** — body simplifies to
   `tokens.back?.map (·.val)`.  The two-deep placeholder skip is dead
   code post-cutover.  The function name picked in step 4 was chosen
   for this exact moment.

4. **`scanFiltered`** — replace
   `tokens.filter (· != .placeholder)` with
   `linearise final.tokens final.pendingKeys`.  Same edit in
   `scanWithComments`.  The `scan` function itself stays unchanged;
   linearisation is `scanFiltered`'s responsibility, exactly mirroring
   the legacy `.filter` step.

5. **No edit needed**: `Scanner/State.lean` (the new types, helpers,
   and accessors all already in place from J.1/J.2 steps 1–4); the
   yaml-test-suite golden harness; FFI / Surface / Schema layers
   (they consume `scanFiltered`'s public output and never observed
   placeholders).

##### 5.b Proof breakage cascade — three categories [Cat A+B ✓ discharged by 5.1 `71a86eee`; Cat C sorry'd → J.3]

**Category A — vacuous post-cutover** (delete or replace with `nofun`)
Hypothesis no longer holdable; the theorem statement is still true
but the original purpose is gone.

* `Proofs/Production/ScannerPlainScalarValid.lean::saveSimpleKey_new_tokens_not_plain`
  — quantifies over indices `≥ s.tokens.size` newly added by
  `saveSimpleKey`.  Post-cutover `saveSimpleKey` adds zero tokens, so
  the hypothesis is unsatisfiable; replace with `False.elim` /
  `nomatch` and update the two callers.
* `Proofs/Output/EmitterScannability.lean::lastTokenVal_push_two_ph`
  — disjunct `t = .placeholder` becomes vacuous; the lemma still types
  but every caller can drop the disjunct.

**Category B — mechanical updates** (one-line proof tweak)
Statement intact; tactic body shrinks because branches collapse.

* `lastTokenVal_push_non_ph` and friends — RHS proven by `rfl` after
  the body simplification rather than multi-branch case split.
* `Proofs/Output/EmitterScannability.lean::saveSimpleKey_filter_placeholder`
  — RHS reduces from "all but the last 2 placeholders" to "all"; in
  the post-cutover world the lemma's RHS is just `s.tokens`.
* `scanFlowSequenceEnd_lastTokenVal` / `scanFlowMappingEnd_lastTokenVal`
  — proof shrinks (no placeholder-skipping argument needed).

**Category C — structurally new proofs** (sorry'd at cutover, J.3
re-discharges)
Old proof depended on `setIfInBounds`-non-plain or
filter-preserves-shape; new proof depends on `linearise`'s property
lemmas (currently `sorry` in `Scanner/Linearise.lean` from J.1).

* `Proofs/Production/ScannerPlainScalarValid.lean`:
  - `scanValuePrepare_preserves_PlainScalarsValid` — old: case-split on
    `setIfInBounds` writes; new: `tokens` unchanged, lemma reduces to
    `h_old`.
  - `PlainScalarsValid_setIfInBounds_non_plain`,
    `flowNesting_setIfInBounds_non_flow`,
    `FlowContextPSV_setIfInBounds` — orphaned helper lemmas; delete
    when no callers remain.
* `Proofs/Output/EmitterScannability.lean`:
  - `scanFiltered`-shape lemmas (those that pattern-match on
    `tokens.filter (· != .placeholder)`) — re-derive against
    `linearise`'s shape.
  - The seven pre-existing Tier 2 sorries (the motivating gap) — these
    *should* be discharged in J.3 as a demonstration that the new
    invariants make Tier 2 tractable; that's the §"Tier 2 stance"
    decision (still open in J.0).
* `Scanner/Linearise.lean` (J.1 stubs, structurally enabling
  Category C):
  - `linearise_append_token` (the headline filter-monotonicity).
  - `linearise_append_unresolved`.
  - `linearise_resolved`.

##### 5.c Sub-substep sequencing

The cutover is staged into three sub-commits so each landing has a
focused diff and a clear "is this gate satisfied" question.

* **5.0 — Code cutover** [✓ `a212cdc2`]: edits 5.a.1–5.a.4 in one
  commit.  Build is red.  This is the *only* commit on
  `feature/append-only` where the build is allowed to be red; all
  later commits restore green.  Outcome: 27 errors, all in
  `Proofs/Scanner/ScannerCorrectness.lean` (Lake short-circuited at
  the first downstream failure; `ScannerPlainScalarValid` and
  `EmitterScannability` errors surfaced incrementally during 5.1).
* **5.1 — Discharge Category A + B** [✓ `71a86eee`]: ~30–40 sites
  across `ScannerCorrectness.lean`, `ScannerPlainScalarValid.lean`,
  `EmitterScannability.lean`, plus 1 each in `DocumentProduction.lean`
  and `EndToEndCorrectness.lean`.  Restores green build with sorries
  only at Category C sites.  Actual new-sorry count: **14** (post-hoc
  re-count after the commit; lands exactly at the §5.d lower bound
  of the 14–17 cap, +4 over the looser per-5.1 "~10" forecast).
  The +4 over-forecast is driven primarily by the `*PlaceholderInv`
  invariant family being structurally tied to the legacy placeholder
  model rather than by `scanFiltered`-shape proofs (those would have
  been cheaper).
* **5.2 — yaml-test-suite golden parity** [✓ this commit]: ran the
  YAML 1.2 test suite against the cutover scanner via `suiterunner
  --json`; **3681/3681 verified**, every stage 100% correctRate, 0
  failed / 0 timeout / 0 unexpectedPass.  Compared the resulting
  `coverage-summary.json` to the pre-cutover baseline at
  `docs/reports/coverage-summary.json` (committed `01a6decd`,
  reflecting source `8bdf4dfd` — the first Initiative 3 commit, before
  any code changes).  After stripping the `date` field and the `name`
  strings, the two JSONs are byte-identical: same per-stage pass /
  fail / skip counts, same per-test status across all 358 applicable
  yaml-test-suite cases, and same overall (358/358 correct, 263
  passed, 95 expectedFail, 48 skipped, 0 failed/timeout/unexpectedPass).
  The *only* differences are in the Adversarial Instantiation suite's
  "prefix preserved (k steps, n∈[1,X])" test names, where the upper
  bound `X` shrinks (e.g. `n∈[1,4]` → `n∈[1,2]`).  This is the
  expected, *intended* effect of the cutover: with placeholders
  removed, k authoring steps now produce exactly k tokens instead of
  up to 2k, so the natural prefix-bound is correspondingly tighter.
  The *test outcome* (every prefix-preserved assertion still passes)
  is unchanged.  Runtime correctness gate satisfied; J.2 is now fully
  green at HEAD.

##### 5.d Sorry-on-stub manifest at end of step 5

Each `sorry` carried into J.3 gets a `-- J.3 manifest 5.d:` comment
in the source pointing back to this section.

**Pre-existing baseline** (untouched by step 5; verified
declaration-level against `f0ce18d3` — the cutover's parent commit):

| Site | Source | Note |
|---|---|---|
| `linearise_append_token` | `Scanner/Linearise.lean` | J.1 stub; J.3 main proof. |
| `linearise_append_unresolved` | `Scanner/Linearise.lean` | J.1 stub; trivial after J.3. |
| `linearise_resolved` | `Scanner/Linearise.lean` | J.1 stub; J.3 size-accounting. |
| `scanNextToken_filtered_grows` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — filtered-token monotonicity; J.3 re-derives via `linearise`'s shape lemmas. |
| `emitList_body_filtered_characterization` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — emitter-shape characterization; multi-sorry body. |
| `emitPairList_body_filtered_characterization` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — emitter-shape characterization; multi-sorry body. |
| `scanFiltered_emitSeq_nonempty_structure` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — non-empty sequence structure preservation. |
| `scanFiltered_emitMap_nonempty_structure` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — non-empty mapping structure preservation. |
| `emit_roundtrip_sequence_content_eq` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — roundtrip content equivalence (sequence). |
| `emit_roundtrip_mapping_content_eq` | `Proofs/Output/EmitterScannability.lean` | Tier 2 — roundtrip content equivalence (mapping). |

Pre-existing total: **10 declarations** using `sorry` (3 Linearise +
7 Tier 2 EmitterScannability).  These are the motivating gap; J.3
demonstrates the new model resolves them.

(N.B. — earlier drafts of this manifest stated "5 × Tier 2 sorries"
without enumerating; the principal verifier recount against
`f0ce18d3` corrected the Tier 2 declaration count to 7.  The
"5 vs 7" discrepancy was a token-count vs declaration-count confusion
in the original draft, not a change in the underlying work.)

**New Category C sorries introduced by 5.0/5.1** (commit `71a86eee`):
all carry the `-- J.3 manifest 5.d:` comment.

| Site | File | Why |
|---|---|---|
| `saveSimpleKey_preserves_SimpleKeyValid` | `Proofs/Scanner/ScannerCorrectness.lean` | Invariant requires `tokenIndex < tokens.size` at save time; false post-cutover until next emit.  Needs conditional/pendingKeys-flavoured re-statement. |
| `scanFiltered_produces_valid_tokens` | `Proofs/Scanner/ScannerCorrectness.lean` | Pre-cutover used `List.filter_sublist`; J.3 re-derives via `linearise`'s shape lemmas. |
| `saveSimpleKey_preserves_AllKeysPlaceholderInv` | `Proofs/Production/ScannerPlainScalarValid.lean` | Whole `*PlaceholderInv` family is tied to the placeholder model; needs pendingKeys-flavoured replacement. |
| `scan_plain_scalar_valid` | `Proofs/Production/ScannerPlainScalarValid.lean` | Pattern-matches on `tokens.filter` shape of `scanFiltered`. |
| `scan_flow_context_psv` | `Proofs/Production/ScannerPlainScalarValid.lean` | Same shape problem — needs `linearise_preserves_FlowContextPSV` bridge. |
| `scan_flow_brackets_matched` | `Proofs/Production/ScannerPlainScalarValid.lean` | Same shape problem — needs `linearise_preserves_FlowBracketsMatched` bridge. |
| `parse_strict_proof` | `Proofs/Production/DocumentProduction.lean` | Needs `scanFiltered_ok_implies_scan_ok` bridge. |
| `parseYaml_implies_valid_token_stream` | `Proofs/EndToEndCorrectness.lean` | Same bridge as above. |
| `scanFiltered_of_chain` | `Proofs/Output/EmitterScannability.lean` | Pre-cutover threaded `scanLoop`; needs `scanLoopFull`-flavoured analogue. |
| `scanFiltered_of_chain_eq` | `Proofs/Output/EmitterScannability.lean` | Same.  Also: RHS shifts from `tokens.filter ...` to `linearise tokens pendingKeys`. |
| `scan_accepts_emitScalar` | `Proofs/Output/EmitterScannability.lean` | Replace `scanLoop` with `scanLoopFull` throughout; mechanical re-work. |
| `scanFiltered_emitScalar_content` | `Proofs/Output/EmitterScannability.lean` | Golden-shape lemma; depends on `tokens.filter` form. |
| `scanFiltered_emitScalar_vals` | `Proofs/Output/EmitterScannability.lean` | Same. |
| `scanFiltered_boundary_tokens` | `Proofs/Output/EmitterScannability.lean` | Boundary-token (streamStart/End) lemma; depends on `tokens.filter` form. |

**Per-file count of new Category C sorries** (re-counted with
`grep -c sorry` against `71a86eee`):

| File | New sorries |
|---|---|
| `Proofs/Scanner/ScannerCorrectness.lean` | 2 |
| `Proofs/Production/ScannerPlainScalarValid.lean` | 4 |
| `Proofs/Production/DocumentProduction.lean` | 1 |
| `Proofs/EndToEndCorrectness.lean` | 1 |
| `Proofs/Output/EmitterScannability.lean` | +6 above the 7 pre-existing Tier 2 |
| **Total new** | **14** |

**Total sorry-using declarations at HEAD (post-5.2)**: 10
(pre-existing) + 14 (new Category C) = **24** (matches the live
`lake build L4YAML` warning count: 3 in `Linearise.lean`, 13 in
`EmitterScannability.lean`, 4 in `ScannerPlainScalarValid.lean`, 2 in
`ScannerCorrectness.lean`, 1 in `DocumentProduction.lean`, 1 in
`EndToEndCorrectness.lean`).  Lands at the lower bound of the
original 14–17 new-sorries forecast.  All 14 new carry the `-- J.3
manifest 5.d:` comment; J.3 clears them.

**Verifier re-count notes**:

* Commit `71a86eee`'s message states +15 new; the verifier re-count
  after the fact came back at 14.  The discrepancy was a miscounted
  `*PlaceholderInv` site conflated with another during
  commit-message drafting; the source is authoritative.
* Earlier drafts gave the post-5.1 total as 22.  The 22 figure used
  "5 × Tier 2 sorries" for the pre-existing EmitterScannability
  baseline; the actual declaration-level count at `f0ce18d3` is 7
  (enumerated in the pre-existing baseline table above), so the
  correct total is **24**.  The 14 new-Category-C count is unchanged
  — only the pre-existing baseline differs from the earlier draft.

##### 5.e Validation gate for step 5

* `lake build L4YAML` green.
  — **Status**: ✓ satisfied at `71a86eee`.
* Net new sorries within budget (forecast 14–17 in §5.d).
  — **Status**: ✓ 14 new sorries, exact lower bound.
* Each new `sorry` carries a `-- J.3 manifest 5.d:` comment matching an
  entry in §5.d.
  — **Status**: ✓ all 14 tagged.
* yaml-test-suite golden parity: scanner output is byte-identical
  pre/post cutover for every `tests/data/*.yaml` fixture.
  — **Status**: ✓ satisfied at `abe092a6` (3681/3681 verified;
  per-stage and per-test pass/fail status byte-identical to the
  pre-cutover baseline at `docs/reports/coverage-summary.json`).
* `Blueprint/07` §J.2 step 5 manifest updated to reflect the actual
  sorry set (drift between this manifest and the source is the failure
  mode to avoid).
  — **Status**: ✓ §5.d table above reconciled against `lake build
  L4YAML` warnings at HEAD (24 sorry-using declarations: 10
  pre-existing + 14 new Category C).

### Phase J.3 — Proof migration (4-6 weeks) [in progress, started 2026-04-26]

Re-discharge the corpus.  Many existing lemmas simplify drastically:

- `ScanChain_filtered_prefix` becomes near-trivial (filter is
  monotone by construction).
- `SimpleKeyAboveFloor` and `SimpleKeyAbove` are removed entirely;
  their consumers either don't need them or use a much simpler
  invariant.
- `preserves_simpleKey`, `preserves_simpleKeyStack`, etc. — replaced
  by `preserves_pendingKeys` lemmas with simpler statements.
- Token-shape lemmas (`scanFlowSequenceStart_tokens_eq`, etc.) carry
  through unchanged in spirit; the right-hand side becomes
  `tokens.push X`.

**Validation gate**: `lake build` passes with sorry count strictly
less than pre-initiative.  Tier 2 Turn 2 (`emitList_body_filtered_
characterization` Parts 1+2) discharged in this phase as
demonstration.

#### J.3 substep manifest

The 17 non-Tier-2 sorries decompose along the dependency graph
rooted at `Scanner/Linearise.lean`:

| Substep | Scope | Sorries cleared | Files touched | Status |
|---|---|---|---|---|
| J.3.1 | Linearise foundations | 3 | `Scanner/Linearise.lean` → `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-04-26 |
| J.3.2 | Bridge lemmas | 0 (new infrastructure) | `Proofs/Scanner/ScannerLinearise.lean`, `Proofs/Scanner/ScannerCorrectness.lean`, `Proofs/Production/ScannerPlainScalarValid.lean` | ✓ done 2026-04-26 |
| J.3.3 | ScannerCorrectness consumers | 1/2 | `Proofs/Scanner/ScannerCorrectness.lean`, `Proofs/Scanner/ScannerLinearise.lean` | partial 2026-04-26 |
| J.3.4 | ScannerPlainScalarValid consumers | 4 | `Proofs/Production/ScannerPlainScalarValid.lean` | ✓ done 2026-04-28 |
| J.3.5 | Production+EndToEnd bridges | 2 | `Proofs/Production/DocumentProduction.lean`, `Proofs/EndToEndCorrectness.lean` | ✓ done 2026-04-28 |
| J.3.6 | EmitterScannability Cat C — chain-bridge subset | 3 | `Proofs/Output/EmitterScannability.lean` (`scanFiltered_boundary_tokens`, `scanFiltered_of_chain`, `scan_accepts_emitScalar`); supporting bridges in `Proofs/Scanner/ScannerCorrectness.lean` | ✓ done 2026-04-29 |
| J.3.7 | EmitterScannability Cat C — emitScalar filter-shape pair | 2 | `Proofs/Output/EmitterScannability.lean` (`scanFiltered_emitScalar_content`, `scanFiltered_emitScalar_vals`); supporting `linearise_all_unresolved` in `Proofs/Scanner/ScannerLinearise.lean`; strengthened `scanNextToken_emitScalar_init` + new `scanLoopFull_eof_eq` / `ScanChain.to_scanLoopFull` / `skipToContent_eq_self_of_peek_none` helpers | ✓ done 2026-04-29 |
| J.3.8 | EmitterScannability Cat C — `scanFiltered_of_chain_eq` re-state in linearise terms | 1 cleared, 2 cascade exposed | `Proofs/Output/EmitterScannability.lean` (`scanFiltered_of_chain_eq`, `scanFiltered_tokens_eq_of_chain_short_stack`, `scanFiltered_emitSeq_nonempty_structure`, `scanFiltered_emitMap_nonempty_structure`) | ✓ done 2026-04-29 |
| J.4   | EmitterScannability Tier 2 + seq/map structure linearise rewrite | 7 + 2 cascade | `Proofs/Output/EmitterScannability.lean` (Tier 2 declarations + seq/map consumer Tier 1 derivations) | in progress |
| J.4.1 | Bridge helper `linearise_eq_filter_no_resolutions` (all-unresolved + no-placeholder ⟹ linearise = filter) | 0 (new infrastructure) | `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-04-29 |
| J.4.2.c-prep | Bridge helper `linearise_push_eq_push_linearise` (clean `.push` form of `linearise_append_token_eq`) | 0 (new infrastructure) | `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-04-29 |
| J.4.2.c-pos1 | Positional lemma `linearise_second_eq_tokens_second` (index-1 readout for `flowSequenceStart` / `blockMappingStart`) | 0 (new infrastructure) | `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-04-29 |
| J.4.2.b-pkwi | Chain-side `PendingKeysWellIndexed` helpers (`PendingKeysWellIndexed_init`, `ScanChain.preserves_PendingKeysWellIndexed`, `PendingKeysWellIndexed_of_chain_from_init`, `PendingKeysWellIndexed_emit_streamEnd`) | 0 (new infrastructure) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.c-pos2 | Positional lemma `linearise_secondLast_eq_tokens_last_inner` (second-to-last readout for `flowSequenceEnd` / `blockMappingEnd` after `streamEnd` push) | 0 (new infrastructure) | `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-04-30 |
| J.4.2.c-prefix | Positional lemma `linearise_prefix_eq_tokens_prefix` (arbitrary-prefix readout under "no early splice"; subsumes `linearise_first_eq_tokens_first` and the index-1 readout from `linearise_second_eq_tokens_second`) | 0 (new infrastructure) | `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2a | `AllUnresolved` predicate + Class A/B/C preservation lemmas (`AllUnresolved_mono`, `AllUnresolved_push_unresolved`, `AllUnresolved_field_update`, `setPendingKeyKind_unresolved_preserves_AllUnresolved`, `saveSimpleKey_preserves_AllUnresolved`) | 0 (new infrastructure) | `Proofs/Scanner/ScannerCorrectness.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2a-chain | Chain-side `AllUnresolved` propagation: `AllUnresolved_init`, parametric `ScanChain.preserves_AllUnresolved`, `AllUnresolved_of_chain_from_init`, `AllUnresolved_emit_streamEnd` | 0 (new infrastructure) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2a-discharge | Per-action `AllUnresolved` preservation discharging the parametric `h_step` for the no-`:`-pair sub-class: `setPendingKeyEndLine_kind`, `setPendingKeyEndLine_wrap_preserves_AllUnresolved`, `scanValueClearKey_no_key`, `scanValuePrepare_no_key_preserves_pendingKeys`, `scanValue_{no_key_preserves_pendingKeys, preserves_AllUnresolved}`, the four per-dispatcher `*_preserves_AllUnresolved` lemmas, `preprocess_preserves_AllUnresolved`, `allowDir_ite_preserves_AllUnresolved`, `scanNextToken_preserves_AllUnresolved` | 0 (new infrastructure) | `Proofs/Scanner/ScannerCorrectness.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2b | `NoPlaceholders` predicate + Class A/B preservation lemmas (`NoPlaceholders_mono`, `NoPlaceholders_emit`, `NoPlaceholders_emitAt`) and chain-side propagation (`NoPlaceholders_init`, parametric `ScanChain.preserves_NoPlaceholders`, `NoPlaceholders_of_chain_from_init`, `NoPlaceholders_emit_streamEnd`) | 0 (new infrastructure) | `Proofs/Scanner/ScannerCorrectness.lean`, `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2b-discharge | Per-action `NoPlaceholders` preservation discharging the parametric `h_step` (unconditional — no sub-class hypothesis): `NoPlaceholders_extension` / `NoPlaceholders_extension_one` generic helpers; primitive Class A leaves (`advance_preserves_NoPlaceholders`, `advanceN_preserves_NoPlaceholders`, `skipToContent_preserves_NoPlaceholders`, `saveSimpleKey_preserves_{tokens,NoPlaceholders}`, `scanValueClearKey_preserves_NoPlaceholders`); indent helpers (`pushSequenceIndent_preserves_NoPlaceholders`, `pushMappingIndent_preserves_NoPlaceholders`, `unwindIndentsLoop_preserves_NoPlaceholders`, `unwindIndents_preserves_NoPlaceholders`); per-scanner `*_preserves_NoPlaceholders` for `scanFlow{SequenceStart, SequenceEnd, MappingStart, MappingEnd, Entry}`, `scanBlockEntry`, `scanKey`, `scanValuePrepare`, `scanValue`, `scanDocumentStart`, `scanDocumentEnd`, `scanAnchorOrAlias`, `scanTag`, `scanBlockScalar`, `scanDoubleQuoted`, `scanSingleQuoted`, `scanPlainScalar`, `scanDirective`; supporting `*_new_token_not_placeholder` helpers (canonical `_new_token_not_plain` style) for the content scanners + `scanVerbatimTag` / `scanSecondaryTag` / `scanNamedTag` / `scanBlockScalarBody` / `scanYamlDirective` / `scanTagDirective`; the four per-dispatcher `*_preserves_NoPlaceholders` lemmas; `preprocess_preserves_NoPlaceholders`, `allowDir_ite_preserves_NoPlaceholders`, top-level `scanNextToken_preserves_NoPlaceholders` | 0 (new infrastructure) | `Proofs/Scanner/ScannerCorrectness.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2c | Linearise-shape variant of `emitList_body_filtered_characterization` for the no-resolution sub-class: `emitList_body_linearise_characterization` wraps the filter-shape body characterization, derives `AllUnresolved s'` (parametric in `h_step_unres` — caller plugs in `scanNextToken_preserves_AllUnresolved` from J.4.2.b-2a-discharge under the no-`:`-pair sub-class) and `NoPlaceholders s'` (unconditional via `scanNextToken_preserves_NoPlaceholders` from J.4.2.b-2b-discharge), then bridges `linearise s'.tokens s'.pendingKeys = s'.tokens.filter p` via `linearise_eq_filter_no_resolutions` (J.4.1) | 0 (new infrastructure) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2d-stub | Stub-level linearise-shape variant of `emitPairList_body_filtered_characterization` for the resolution case: `emitPairList_body_linearise_characterization` wraps the filter-shape body characterization, carries the chain + 13 invariants + `n ≥ 3` from filter-shape, derives `NoPlaceholders s'` (unconditional via `scanNextToken_preserves_NoPlaceholders` from J.4.2.b-2b-discharge); states linearise-shape Part (2) (`linearise[old_sz].val = .key`) and Part (3) (`linearise[k+1].val = .key` after outer-level flowEntry) on `linearise s'.tokens s'.pendingKeys` directly (no `linearise = filter` bridge — fails when `:` resolutions fire); both linearise-shape parts SORRY'd as J.4.2.b-2d-key follow-up | +2 (sorry stubs for the linearise-shape parts; chain + invariants + `n ≥ 3` + `NoPlaceholders s'` proven) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2d-key-foundation-A | Foundation A for the 2d-key splice mechanic: `linearise_first_splice_keyonly` (in `Proofs/Scanner/ScannerLinearise.lean`, after `linearise_prefix_eq_tokens_prefix`).  Given `pks.size > 0`, `pks[0].kind = .keyOnly`, `pks[0].insertBeforeIdx = j ≤ tokens.size`, derives `(linearise tokens pks)[j].val = .key`.  Proof: walk `linearise.go` from `(0, 0, #[])` to `(j, 0, tokens[0..j])` without firing splices (induction adapted from `linearise_prefix_eq_tokens_prefix`), step once to fire the `pks[0]` splice (`expandKind .keyOnly = #[⟨pos, .key, pos⟩]`), read off `.key` at index `j` via `linearise_go_getElem_lt_acc`.  Reshapes Part (2) of `emitPairList_body_linearise_characterization` to consume Foundation A — splice analysis fully discharged; remaining sorry narrowed to chain-side accounting (J.4.2.b-2d-key-chain) | 0 (Part (2) splice-analysis sorry replaced by chain-side accounting sorry — same count, narrowed shape) | `Proofs/Scanner/ScannerLinearise.lean`, `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2d-key-foundation-B | Foundation B for the 2d-key splice mechanic at general `(j, p, acc)` state: `linearise_splice_keyonly_at` + index-form corollary `linearise_splice_keyonly_at_index` (in `Proofs/Scanner/ScannerLinearise.lean`, after `linearise_first_splice_keyonly`).  Given a transport equation `linearise tokens pks = linearise.go tokens pks j p acc` and splice-fire preconditions (`p < pks.size`, `pks[p].insertBeforeIdx ≤ j`, `pks[p].kind = .keyOnly`), derives `(linearise tokens pks)[acc.size].val = .key`.  Companion to Foundation A: A walks from the start internally and fires `pks[0]`; B is the splice mechanic in isolation, parameterized on a general `(j, p, acc)` state — chain-side accounting supplies the transport equation (J.4.2.b-2d-key-chain).  Proof structure (mirrors the inner half of Foundation A): step once to fire splice; `expandKind .keyOnly = #[⟨pos, .key, pos⟩]` gives `.key` at the new acc's index `acc.size`; prefix-stability (`linearise_go_getElem_lt_acc`) propagates to final result; transport via `h_eq` + step equation.  Reshapes Part (3) of `emitPairList_body_linearise_characterization` to consume Foundation B (index form, with `acc.size = k + 1` for the after-flowEntry position) — splice analysis fully discharged; remaining sorry narrowed to chain-side accounting (J.4.2.b-2d-key-chain extended to all outer pairs) | 0 (Part (3) splice-analysis sorry replaced by chain-side accounting sorry — same count, narrowed shape) | `Proofs/Scanner/ScannerLinearise.lean`, `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2d-key-prep | Pre-step toward chain-side accounting: (i) added `h_pks_empty : s.pendingKeys = #[]` precondition to `emitPairList_body_linearise_characterization` — needed to make Foundation A's `[0]`-index semantically aligned with "first new pendingKey from the body" (without it, `pks[0]` could be an outer-scope leftover with smaller `insertBeforeIdx`); (ii) discharged the trivial token-monotonicity sub-fact `(s.tokens.filter p).size ≤ s'.tokens.size` directly from `ScanChain_tokens_mono` + `Array.size_filter_le`, no longer bundled in the chain-side sorry; (iii) decomposed remaining 2d-key-chain into `-Part2` (first-key splice shape: `0 < s'.pendingKeys.size ∧ s'.pendingKeys[0].insertBeforeIdx = (s.tokens.filter p).size ∧ s'.pendingKeys[0].kind = .keyOnly`) and `-Part3` (after-flowEntry splice: for each outer-level flowEntry at position `k`, supply `(j, p, acc)` with `acc.size = k + 1` and the splice fire preconditions).  At the eventual call site (`scanFiltered_emitMap_nonempty_structure` from `scanNextToken_flow_open_mapping_init`), `s₁.pendingKeys = #[]` is structurally true (init scanner state has empty pendingKeys; `{` scan only emits `.flowMappingStart` — no save).  Exposing this fact at `scanNextToken_flow_open_mapping_init`'s output is part of cascade stitching (item 3), not 2d-key-chain itself | 0 (precondition refinement + trivial sub-fact discharged; same chain-side accounting count, narrower shape) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2d-key-chain-Part2-stub | Stub-level extraction of the chain-side accounting for the first resolved pendingKey: introduced freestanding theorem `emitPairList_chain_first_pkShape` (in `Proofs/Output/EmitterScannability.lean`, just before `emitPairList_body_linearise_characterization`) with the precise signature for the first-key chain-side facts (`0 < s'.pendingKeys.size ∧ s'.pendingKeys[0].insertBeforeIdx = s.tokens.size ∧ s'.pendingKeys[0].kind = .keyOnly`), parameterized on the chain `ScanChain s n s'` and the same hypotheses as `emitPairList_scans_nonempty` plus `h_pks_empty : s.pendingKeys = #[]`.  The stub's body is `sorry`, but the wrapper theorem `emitPairList_body_linearise_characterization` Part (2) now consumes the stub cleanly (replacing the inline sorry with a call + filter-identity transport via `h_filter_eq_s`).  Investigation showed the body discharge requires deeper infrastructure than initially scoped in 1 cadence step: strengthening (a) `EmitScansInFlow` (or per-leaf scalar/coll variants) to expose pendingKey shape after key scan, (b) `scanNextToken_flow_value` to expose the resolution effect on the active pendingKey, (c) `EmitScansInFlow` preservation through the value scan.  Refined estimate: 2-3 cadence steps for the body discharge (Part2 body proper) | 0 (named extraction; Part2 inline sorry replaced by stub sorry — same count, structurally cleaner with reusable signature) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-04-30 |
| J.4.2.b-2d-key-chain-Part2-body-A1 | Foundational lemma `saveSimpleKey_pkPush_when_allowed` (in `Proofs/Output/EmitterScannability.lean`, after `saveSimpleKey_id_of_flow_ska_false_ek_none`): exact pendingKey effect of `saveSimpleKey` when the push branch fires — under `simpleKeyAllowed = true ∧ explicitKeyLine = none`, conclude `(saveSimpleKey s).pendingKeys = s.pendingKeys.push <unresolved at s.tokens.size>`, `(saveSimpleKey s).pendingKeyActive = some s.pendingKeys.size`, `(saveSimpleKey s).simpleKey.possible = true`.  Companion to the existing identity-branch lemma.  Investigation showed Part2-body-A genuinely decomposes into A1 (this) + A2 (per-leaf scalar) + A3 (per-leaf seq) + A4 (per-leaf map) + final `EmitScansInFlow` def strengthening.  This step lands the foundational ingredient consumed by all per-leaf theorems and potentially Part2-body-B (`:`-resolution exposure on `scanNextToken_flow_value`) | 0 (foundational lemma fully proven, no sorry) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-A2 | Per-leaf scalar pkPush theorem `scanNextToken_flow_scanDoubleQuoted_pkPush` (in `Proofs/Output/EmitterScannability.lean`, immediately after `scanNextToken_flow_scanDoubleQuoted`).  Parallel to the base theorem under additional hypotheses `s.simpleKeyAllowed = true ∧ s.explicitKeyLine = none`; conclusion adds three pendingKey-tracking conjuncts on top of the existing 13: `s'.pendingKeys.size = s.pendingKeys.size + 1`, `s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size`, `s'.pendingKeys[s.pendingKeys.size].kind = .unresolved`.  Proof composes A1 (`saveSimpleKey_pkPush_when_allowed`) for the push, `ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeys` for the inner scan, and `ScannerCorrectness.setPendingKeyEndLine_{size,insertBeforeIdx,kind}` for the dispatchContent J.2 dual-write wrap (which only touches the active entry's `endLine` field, preserving size + insertBeforeIdx + kind per-entry).  Implementation chose parallel-proof copy (~150 lines) over in-place augmentation since the base theorem has only one in-tree caller (`emit_scans_in_flow`) which would need re-threading anyway when `EmitScansInFlow` is strengthened (Part2-body-A4-and-final-def step) | 0 (per-leaf theorem fully proven, no sorry) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-A3 | Per-leaf flow-sequence-open pkPush theorem `scanNextToken_flow_open_nested_pkPush` (in `Proofs/Output/EmitterScannability.lean`, immediately after `scanNextToken_flow_open_nested`).  Parallel to the base theorem under the same additional hypotheses as A2 (`s.simpleKeyAllowed = true ∧ s.explicitKeyLine = none`); conclusion adds the same three pendingKey-tracking conjuncts on top of the existing 12.  Simpler than A2 since the `[` flow path is dispatched via flow indicators (not content) — no `setPendingKeyEndLine` wrap, just A1 (`saveSimpleKey_pkPush_when_allowed`) + `ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys` (Class A pure preservation).  Covers ONLY the `[` open step; full body+close emerges from recursive composition through other per-leaf lemmas, with the outer entry untouched by inner scans (they push at fresh indices > `s.pendingKeys.size`).  A4 (mapping `{` open) is now narrowed to a mechanical mirror of A3 with `scanFlowMappingStart_preserves_pendingKeys` (~0.5 cadence step, refined down from the original 1-2 estimate) | 0 (per-leaf theorem fully proven on first try, no sorry) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-A4 | Per-leaf flow-mapping-open pkPush theorem `scanNextToken_flow_open_mapping_nested_pkPush` (in `Proofs/Output/EmitterScannability.lean`, immediately after `scanNextToken_flow_open_mapping_nested`).  Mechanical mirror of A3 with `[` → `{`, `scanFlowSequenceStart` → `scanFlowMappingStart`, `dispatchFlowIndicators_bracket` → `dispatchFlowIndicators_brace`, `ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys` → `ScannerCorrectness.scanFlowMappingStart_preserves_pendingKeys`.  Same hypotheses (`s.simpleKeyAllowed = true ∧ s.explicitKeyLine = none`) and same 12 + 3 conjunct shape.  No `setPendingKeyEndLine` wrap (the `{` flow path also skips `dispatchContent`).  Covers ONLY the `{` open step; inner pair scans (key/`:`/value bodies) push new entries at later indices and do not touch the outer entry recorded by the outer `saveSimpleKey`.  Completes the per-leaf chain A1-A4; next step is `EmitScansInFlow` def strengthening + `emit_scans_in_flow` re-prove (~0.5 cadence step) | 0 (per-leaf theorem fully proven on first try, no sorry) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-B | Per-`:`-step pkResolve theorem `scanNextToken_flow_value_pkResolve` (in `Proofs/Output/EmitterScannability.lean`, immediately after `scanNextToken_flow_value`).  Strengthens the existing 13-conjunct surface theorem with 3 pkResolve conjuncts (size preservation, `(s'.pendingKeys[i]).kind = .keyOnly` together with `insertBeforeIdx` preservation at the active index `i`, and unchanged-elsewhere `j ≠ i`) under the additional preconditions `s.simpleKeyAllowed = false ∧ s.simpleKey.possible = true ∧ s.pendingKeyActive = some i ∧ i < s.pendingKeys.size`.  The `simpleKeyAllowed = false` precondition is essential: it makes `saveSimpleKey s = s` (via the existing `saveSimpleKey_id_of_flow_ska_false_ek_none`) so the pre-existing active reservation flows unchanged into `scanValuePrepare`'s flow branch, where it is consumed by `setPendingKeyKind … .keyOnly`.  Foundational helper `scanValuePrepare_pendingKeys_flow_resolve` (added next to `saveSimpleKey_pkPush_when_allowed` / `scanValueValidate_ok_of_not_possible_ek_none`) gives the pure characterization.  Proof uses the existing `scanNextToken_flow_value` for surface conjuncts plus a re-derivation of the canonical `s_final` chain to identify `s'` via determinism, tracks pendingKeys through `saveSimpleKey` (identity) → `s_ad` (allowDirectives passthrough) → `scanValueClearKey` (identity since `ek = none`) → `scanValuePrepare` flow branch → `emit`/`advance`/final record-update (Class A passthroughs).  Per-entry pkResolve facts derived via `Array.getElem_setIfInBounds_self` / `Array.getElem_setIfInBounds_ne`.  Together with A1-A4 this completes Part2-body's leaf and `:`-step machinery; remaining for full 2d discharge: Part2-body-C composition (~0.5 step) and Part3 splice locator (separate track) | 0 (theorem fully proven, no sorry) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-Aseq/Amap | Preserves-prior strengthening on A3 (`scanNextToken_flow_open_nested_pkPush`) and A4 (`scanNextToken_flow_open_mapping_nested_pkPush`): under existing hypotheses, additionally conclude `∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size), s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj`.  Investigation during the cadence revealed body-C requires `pendingKeyActive = some s.pendingKeys.size`, `simpleKey.possible = true`, AND preserves-prior conjuncts at the post-key state — none of which A1-A4 currently expose.  This step lands the easiest of those (preserves-prior) on A3/A4.  Proof: the flow-open path (`scanNextToken_dispatchFlowIndicators`) skips `dispatchContent`, so `s'.pendingKeys = s.pendingKeys.push <new>` directly and preservation follows from `Array.getElem_push_lt` after `simp only [h_fss_pks_full]` (resp. `h_fms_pks_full`).  Body-C decomposed into four sub-steps in the open-bullet section: **C-foundation-Aseq/Amap** (this step), **C-foundation-Ascalar** (extend A2 — needs new `*_preserves_pendingKeyActive` chain in `Proofs/Scanner/ScannerCorrectness.lean` because `dispatchContent`'s `setPendingKeyEndLine` wrap requires knowing the active index, ~0.5 step), **C-foundation-EmitScansInFlow** (uniform preserves-prior + first-key gated conjunct on the `EmitScansInFlow` family, with seq/map cases threading the `simpleKeyStack` / `pendingKeyStack` pop on `]` / `}`, ~1 step), **C-compose** (singleton/cons walk in `emitPairList_chain_first_pkShape` plus `scanNextToken_flow_comma_pkPreserve`, ~0.5–1 step).  Cleaner cadence sizing than the original "~0.5 step" estimate on body-C as a single unit | 0 (no new sorries; A3/A4 each gain one conjunct without breaking existing 15-conjunct shape) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-Ascalar | A2 (`scanNextToken_flow_scanDoubleQuoted_pkPush`) extended with three new conjuncts at the post-key state: `s'.pendingKeyActive = some s.pendingKeys.size`, `s'.simpleKey.possible = true`, and preserves-prior on `pendingKeys` (`∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size), s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj`).  Tricky because `dispatchContent` wraps via `setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line` — to discharge preserves-prior we must know `s_dq.pendingKeyActive = some s.pendingKeys.size` so the `setIfInBounds` write index lands at `s.pendingKeys.size > j`.  Required (a) a new `*_preserves_pendingKeyActive` chain in `Proofs/Scanner/ScannerCorrectness.lean` mirroring the existing `*_preserves_pendingKeys` chain (advance/emit/emitAt + skipSpacesLoop/skipSpaces/skipWhitespaceLoop/skipWhitespace + consumeNewline + collectHexDigitsLoop/parseHexEscape/processEscape + foldQuotedNewlinesLoop/foldQuotedNewlines + collectDoubleQuotedLoop + scanDoubleQuoted) — none of these touch `pendingKeyActive`, so all proofs are pure passthroughs structurally identical to their `_preserves_pendingKeys` counterparts; (b) two new helpers `setPendingKeyEndLine_decomp_some` (specialization of the existing decomp that exposes the active index `j`) and `setPendingKeyEndLine_some_at_other_unchanged` (record-level "at index `i ≠ j`, the wrap is the identity" via `Array.getElem_setIfInBounds_ne`).  A2's conclusion now exposes 17 conjuncts (was 15) with no break to the existing `emit_scans_in_flow` consumer (it ignores the new conjuncts).  Completes the per-leaf foundation for body-C; remaining for body-C: **C-foundation-EmitScansInFlow** (uniform preserves-prior + gated active/possible on the `EmitScansInFlow` family, ~1 step) and **C-compose** (singleton/cons walk in `emitPairList_chain_first_pkShape` + `scanNextToken_flow_comma_pkPreserve`, ~0.5–1 step) | 0 (theorem fully proven; ScannerCorrectness chain fully proven; sorry count unchanged at 9 — locations shifted by +53 lines from prior baseline due to the new chain insertion) | `Proofs/Output/EmitterScannability.lean`, `Proofs/Scanner/ScannerCorrectness.lean` | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove | Size-mono + pkRec preservation conjuncts added to the three `EmitScansInFlow{,List,PairList}` definitions in `Proofs/Output/EmitterScannability.lean`.  Each conjunct shape is `s.pendingKeys.size ≤ s'.pendingKeys.size ∧ ∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size), s'.pendingKeys[j].insertBeforeIdx = s.pendingKeys[j].insertBeforeIdx ∧ s'.pendingKeys[j].kind = s.pendingKeys[j].kind`.  Two new composition helpers introduced: (a) `pkRec_size_compose` chains two consecutive (size-mono + pkRec-preservation) witnesses through an intermediate state — the workhorse for chaining helper-level pkRec preservation across multi-step paths (key + colon + value + comma + recurse); (b) `pkRec_size_of_pks_eq` lifts a `pendingKeys` equality to (size-mono + pkRec-preservation) — used to bridge through `scanNextToken_preprocess_flow_ws1` (which preserves `pendingKeys` exactly).  Consumers re-proved: `emitList_scans_empty/nonempty` (composition through key + comma + space-preprocess + recursive emitList; both singleton and multi-item cases discharge cleanly); `emitPairList_scans_empty` (zero-chain identity); `emitPairList_scans_nonempty` (singleton + cons cases use the shared sorry'd helper `emitPairList_body_size_pkRec_through_colon_sorry` for size+pkRec — see below); `emit_scans_in_flow` (scalar via `scanNextToken_flow_scanDoubleQuoted`'s witness; sequence via open + EmitListScansInFlow body + close composition; mapping via open + EmitPairListScansInFlow body + close composition).  Downstream destructures updated: `emitList_body_filtered_characterization`, `emitPairList_body_filtered_characterization`, and 6+ EmitScansInFlow destructures (singleton/multi-item key+value pairs in emitList/emitPairList) extended to bind `_h_size…`/`_h_pkRec…`.  Net regression: +1 sorry — the body-C colon-step (size + pkRec) preservation through `scanNextToken_flow_value` is captured in a single sorry'd helper `emitPairList_body_size_pkRec_through_colon_sorry` (line 3436), used at both call sites of `emitPairList_scans_nonempty` (singleton + cons).  The consumer-side scenario ensures `pendingKeyActive ≥ s.pendingKeys.size` (the body's initial size, set by the key's `saveSimpleKey` push), so pkRec preservation at `j < s.pendingKeys.size` holds — but the precise discharge needs the **gated** sub-step's analysis of `scanNextToken_flow_value`'s effect on `pendingKeys`.  Sorry count: 9 → 10 (single new sorry, factored into reusable helper) | 0 (build clean; +1 sorry net via shared helper; ~210-line addition) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-preservation-chain | Discharged the `scanDoubleQuoted_preserves_pendingKeyStack_sorry` placeholder by building the parallel `_preserves_pendingKeyStack` chain through the quoted-scalar machinery, mechanically mirroring the existing `_preserves_simpleKeyStack` chain.  ScannerCorrectness additions (in the pendingKeyStack section, immediately after `skipToContent_preserves_pendingKeyStack`): `emitAt_preserves_pendingKeyStack`, `collectHexDigitsLoop_preserves_pendingKeyStack`, `parseHexEscape_preserves_pendingKeyStack`, `processEscape_preserves_pendingKeyStack`, `skipBlankLinesLoop_preserves_pendingKeyStack`, `foldQuotedNewlinesLoop_preserves_pendingKeyStack`, `foldQuotedNewlines_preserves_pendingKeyStack`, `collectDoubleQuotedLoop_preserves_pendingKeyStack`, `scanDoubleQuoted_preserves_pendingKeyStack` — 9 lemmas, all structurally identical to their `_preserves_simpleKeyStack` counterparts (Class A passthroughs: none of the quoted-scalar machinery touches `pendingKeyStack`; the proofs follow the exact same case decomposition + advance/emit composition pattern).  EmitterScannability changes: removed the 18-line sorry'd helper `scanDoubleQuoted_preserves_pendingKeyStack_sorry` + its docstring; updated the call site at `scanNextToken_flow_scanDoubleQuoted` to use `ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeyStack` directly; refreshed the surrounding comments to drop "sorry'd" language.  Independent of the body-C cadence (clean orthogonal cleanup).  Sorry count: 10 → 9 | 0 (build clean across 453 jobs; -1 sorry net via the new chain; ~155-line addition in ScannerCorrectness, ~22-line removal in EmitterScannability) | `Proofs/Scanner/ScannerCorrectness.lean`, `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon | Discharged the `emitPairList_body_size_pkRec_through_colon_sorry` placeholder (size-mono + pkRec preservation + pendingKeyStack equality through the body-C colon-step chain).  Mechanism: (a) added `s.simpleKeyAllowed = true` precondition to `EmitPairListScansInFlow` (the body's first key must be eligible for `saveSimpleKey`'s push branch to register an `.unresolved` reservation that the colon's `scanValuePrepare` then resolves to `.keyOnly`); (b) extended `scanNextToken_flow_open_mapping_nested` and `scanNextToken_flow_open_mapping_init` with `s'.simpleKeyAllowed = true` (record-update on `scanFlowMappingStart` sets it directly) so the gate threads from the outer state through `{` into `EmitPairListScansInFlow`'s precondition; (c) extended `scanNextToken_flow_comma` with `s'.simpleKeyAllowed = true` (scanFlowEntry's record-update sets it) and `scanNextToken_preprocess_flow_ws1` with `s₁.simpleKeyAllowed = s.simpleKeyAllowed` (skipToContent passthrough; needs an inline `advance_preserves_simpleKeyAllowed` step) so the gate threads through `s_v → s_c → s_pp` in the cons recursive case to satisfy the IH's new precondition; (d) extended `scanNextToken_flow_value_pkResolve` with `s'.pendingKeyStack = s.pendingKeyStack` (chain-through advance/emit/scanValuePrepare/s_ad/saveSimpleKey, none touch pendingKeyStack) so the colon step's pendingKeyStack preservation is exposed.  Inline discharges in `emitPairList_scans_nonempty` (singleton + cons): re-call `scanNextToken_flow_value_pkResolve` on s₁ under the gated facts (h_lt_pk_s1, h_pka_eq, h_skp_eq from `_h_gated₁ h_ska`) + `h_ska₁ : s₁.simpleKeyAllowed = false` (from the unconditional EmitScansInFlow postcondition) to derive a parallel `s₂_pk` that resolves the entry at `i = s.pendingKeys.size`; identify with the existing `s₂` via `scanNextToken` determinism + `subst`; for `j < s.pendingKeys.size`, `j ≠ i` so `h_pks_other_pk` gives `s₂[j] = s₁[j]`, composing with `_h_pkRec₁` to lift preservation through the colon step.  Then `pkRec_size_compose` chains through ws1 (preserves pendingKeys) → value (EmitScansInFlow) → in cons case also comma (scanNextToken_flow_comma) → ws1 → recursive IH.  pendingKeyStack preservation chain: `_h_pks₁` (key) → `h_pks_pk_pkr` (colon, new) → `h_pks_pp₃` (ws1) → `_h_pks₃`/`_h_pks_v` (value) → in cons also `_h_pks_c` (comma) → `_h_pks_pp_stk` (ws1) → `h_pks_r` (IH).  Cascading consumer updates: `EmitPairListScansInFlow` precondition added at all callers (emit_scans_in_flow mapping case via `h_ska₁` from open-mapping-nested; scanFiltered_exists_emit_aux mapping case via `h_ska₁` from open-mapping-init; downstream `emitPairList_body_filtered_characterization`, `emitPairList_chain_first_pkShape`, `emitPairList_body_linearise_characterization` each gain `h_ska` precondition threaded through to `emitPairList_scans_nonempty`).  Removed the 8-line sorry'd placeholder + its docstring.  Sorry count: 11 → 10 | 0 (build clean across 453 jobs; -1 sorry net via inline discharges; ~150-line addition for new conjuncts + inline discharges, offsetting the ≈30 lines of removed placeholder) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated-discharge | Discharged the two `emit_scans_in_flow_{seq,map}_gated_sorry` placeholders introduced by the **gated** sub-step.  Mechanism: extended `scanNextToken_flow_open_nested_pkPush` (`[`) and `scanNextToken_flow_open_mapping_nested_pkPush` (`{`) with two new conjuncts each — (i) `s'.pendingKeyStack = s.pendingKeyStack.push (some s.pendingKeys.size)` (push-shape: scanFlowSequenceStart/MappingStart push the prior `pendingKeyActive` onto `pendingKeyStack`, and saveSimpleKey under the gate sets `pendingKeyActive = some s.pendingKeys.size`); (ii) `(s'.simpleKeyStack.back?.getD {}).possible = true` (top-of-stack: scanFlowSequenceStart/MappingStart push `s_ad.simpleKey` onto `simpleKeyStack`, and saveSimpleKey under the gate sets `simpleKey.possible = true`).  Both proven inline in each `_pkPush` variant via the existing `_stack_pushed` / `_pendingKeyStack_pushed` lemmas + `Array.back?_push` + `saveSimpleKey_pkPush_when_allowed`'s pkActive/skPossible parts.  Inline discharges in `emit_scans_in_flow` seq/map: re-call the open `_pkPush` variant under the gate to extract the new push-shape facts, identify the resulting state with the existing `s₁` via `scanNextToken` determinism (h_snt₁ vs h_snt_pk) + `subst`, then chain through body `pks` / `stack` preservation (h_pks₂ for pendingKeyStack, h_stack₂ for simpleKeyStack) and close-side restore (_h_pka_restore₃ for pendingKeyActive, _h_sk_restore₃ for simpleKey).  The first-key entry in the existential is recovered via `pkRec_size_compose h_size₂ h_size₃ h_pkRec₂ h_pkRec₃` lifted from the s₁ pkPush witness through s₂ → s₃.  No changes to consumer destructure patterns (the gated conjunct shape is unchanged — only the discharge moved from sorry to inline).  Removed the two sorry'd placeholders and their docstring (≈55 lines).  Sorry count: 13 → 11 | 0 (build clean across 453 jobs; -2 sorries net via inline discharges; ~80-line addition for pkPush extensions + ~50-line addition for inline discharges, offsetting the ≈55 lines of removed placeholders) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated | Gated first-key conjunct added to `EmitScansInFlow` (only — not List/PairList) under a `s.simpleKeyAllowed = true` gate.  New conjunct shape: `s.simpleKeyAllowed = true → (∃ (h : s.pendingKeys.size < s'.pendingKeys.size), s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size ∧ s'.pendingKeys[s.pendingKeys.size].kind = .unresolved) ∧ s'.pendingKeyActive = some s.pendingKeys.size ∧ s'.simpleKey.possible = true`.  Note: the duplicate "preserves-prior at j < s.pendingKeys.size" was dropped from the gated branch since the unconditional kind+insertBeforeIdx conjunct already covers it (the eventual colon-step discharge needs that weaker form, not entry-equality, and dropping it avoids needing to strengthen the body's preserves-prior to full record equality).  Scalar case discharged inline by calling `scanNextToken_flow_scanDoubleQuoted_pkPush` in parallel under the gate and using determinism of `scanNextToken` to identify the s' from the unconditional + pkPush variants — ~14 lines of inline code in `emit_scans_in_flow` scalar.  Seq/map cases deferred via two named sorry'd helpers `emit_scans_in_flow_seq_gated_sorry` and `emit_scans_in_flow_map_gated_sorry`, since the proper discharge requires either (a) extending `_pkPush` open helpers with `simpleKeyStack`/`pendingKeyStack` push-shape conjuncts (so close's restore lemmas can compute the back-of-stack values) or (b) inline reasoning about `scanFlowSequenceStart`/`MappingStart`'s effect on stacks via `_pushed` lemmas + `back?_push` (≈40-60 lines per case) — split out as its own focused **gated-discharge** sub-step.  Consumer destructure patterns updated to bind the new gated conjunct (`_h_gated…` placeholders) at 4 call sites: `emitList_scans_nonempty` singleton+cons, `emitPairList_scans_nonempty` singleton+cons.  The body-C colon-step sorry'd helper `emitPairList_body_size_pkRec_through_colon_sorry` remains as is; its discharge is split out as a separate **discharge-colon** sub-step since it needs the seq/map gated discharges to be proper (not sorry'd) for the gated facts to flow into `pkResolve`.  Net regression: +2 sorries (seq + map gated placeholders), sorry count: 11 → 13 | 0 (build clean across 453 jobs; +2 sorries net via factored seq/map placeholders; ~50-line addition) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore | Close-side stack-restore lemmas + body-side `pendingKeyStack` preservation conjunct, completing the framework needed by the **gated** sub-step.  ScannerCorrectness additions: (a) `advance_preserves_pendingKeyStack` + `emit_preserves_pendingKeyStack` — base ops don't touch pendingKeyStack; (b) `saveSimpleKey_preserves_pendingKeyStack` — saveSimpleKey is push-or-id on `pendingKeys` only; (c) `scanFlowSequenceEnd_pendingKeyActive_restored` (= `s.pendingKeyStack.back?.getD none`) and `scanFlowSequenceEnd_pendingKeyStack_popped` (= `s.pendingKeyStack.pop`) — close pops both stacks in tandem (J.2 dual-write mirror of simpleKey/Stack restore); (d) `scanFlowMappingEnd_…` analogs; (e) `scanFlowSequenceStart_pendingKeyStack_pushed` / `scanFlowMappingStart_…` — open pushes prior `pendingKeyActive` onto stack; (f) full `_preserves_pendingKeyStack` chain through `skipToContent` (skipSpaces/skipWhitespace/Loop variants, collectCommentTextLoop, skipToContentWs/Comment, consumeNewline, skipToContentLoop) mirroring the existing simpleKeyStack chain (≈12 lemmas, all mechanical).  EmitterScannability additions: (1) `scanNextToken_flow_close_seq_nested` extended with three new conjuncts `s'.simpleKey = s.simpleKeyStack.back?.getD {}`, `s'.pendingKeyActive = s.pendingKeyStack.back?.getD none`, `s'.pendingKeyStack = s.pendingKeyStack.pop`; (2) `scanNextToken_flow_close_mapping_nested` analog; (3) `scanNextToken_flow_open_nested` extended with `s'.pendingKeyStack.pop = s.pendingKeyStack` (mirror of existing simpleKeyStack pop); (4) `scanNextToken_flow_open_mapping_nested` analog; (5) `scanNextToken_flow_comma` extended with `s'.pendingKeyStack = s.pendingKeyStack` (Class A passthrough — scanFlowEntry doesn't touch stack); (6) `scanNextToken_preprocess_flow_ws1` extended with `s'.pendingKeyStack = s.pendingKeyStack` (skipToContent passthrough); (7) `scanNextToken_flow_scanDoubleQuoted` extended with `s'.pendingKeyStack = s.pendingKeyStack` — discharged via new sorry'd helper `scanDoubleQuoted_preserves_pendingKeyStack_sorry` because the proper proof requires a parallel `_preserves_pendingKeyStack` chain through `collectDoubleQuotedLoop` / `processEscape` / `parseHexEscape` etc. (≈30 lemmas mirroring the `_preserves_simpleKeyStack` chain), which is mechanically uniform but fills its own cadence step (a follow-on "preservation-chain" sub-step is the cleanest place to discharge this); (8) `EmitScansInFlow` (main) extended with `s'.pendingKeyStack = s.pendingKeyStack` conjunct; (9) `EmitListScansInFlow` / `EmitPairListScansInFlow` extended with same; (10) `emitPairList_body_size_pkRec_through_colon_sorry` placeholder extended to also bundle `s'.pendingKeyStack = s.pendingKeyStack` (no new sorry — the helper is already sorry'd, and `pendingKeyStack` preservation through the colon step holds for the same reason as size+pkRec).  Consumers re-proved: `emit_scans_in_flow` scalar (via scanDoubleQuoted's new conjunct), seq (via open `pop` + body preservation + close `pop` cancellation), map (analog); `emitList_scans_empty/nonempty` (singleton via EmitScansInFlow's conjunct; multi-item via comma + preprocess + recursive emitList chain); `emitPairList_scans_empty/nonempty` (empty trivial; singleton+cons use the extended sorry'd colon-step helper).  Net regression: +1 sorry — `scanDoubleQuoted_preserves_pendingKeyStack_sorry`, factored into a single helper with a documented discharge path (parallel preservation chain).  Sorry count: 10 → 11 | 0 (build clean across 453 jobs; +1 sorry net via factored scalar-helper placeholder; ~250-line addition between the two files) | `Proofs/Output/EmitterScannability.lean`, `Proofs/Scanner/ScannerCorrectness.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-consumers | Folded into **defns-prove**: the downstream destructure updates (10+ patterns binding `_h_size…`/`_h_pkRec…` at consumer sites) landed mechanically alongside `defns-prove` since the consumer changes were uniform pattern extensions, not standalone work.  Tracked here for cadence-completeness | 0 (no separate code change; folded into defns-prove) | `Blueprint/07-initiative-3-append-only.md` (only) | ✓ done 2026-05-02 (folded) |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-helpers-size | Size monotonicity (`s.pendingKeys.size ≤ s'.pendingKeys.size`) added to all 6 scanner-helper theorems used inside `emit_scans_in_flow` and `emit{List,PairList}_scans_*` proofs.  Foundational lemma `saveSimpleKey_pendingKeys_size_ge` introduced (`saveSimpleKey` is push-or-id, so size grows or preserves).  Helper theorems strengthened: `scanNextToken_flow_scanDoubleQuoted` (inner `h_content` existential extended; size discharge in both `simpleKey.possible = true/false` branches via `setPendingKeyEndLine_size` + `saveSimpleKey_pendingKeys_size_ge`), `scanNextToken_flow_open_nested` (`scanFlowSequenceStart_preserves_pendingKeys` chain), `scanNextToken_flow_close_seq_nested` (`scanFlowSequenceEnd_preserves_pendingKeys` chain), `scanNextToken_flow_open_mapping_nested` (`scanFlowMappingStart_preserves_pendingKeys`), `scanNextToken_flow_close_mapping_nested` (`scanFlowMappingEnd_preserves_pendingKeys`), `scanNextToken_flow_comma` (advance + emit + saveSimpleKey).  Each discharge re-uses each helper's existing inner pendingKeys-equation chain (already proved for the pkRec preservation conjunct in sub-step 1), then composes with `saveSimpleKey_pendingKeys_size_ge`.  `scanNextToken_preprocess_flow_ws1` already exposes full `pendingKeys = pendingKeys` equality, so size mono is trivially derivable via `Nat.le_refl`.  No consumer destructure updates needed: the new conjunct gets right-associatively bundled with the existing pkRec conjunct in callers' anonymous `_h_pks…` binders.  Sorry count unchanged at 9 — locations shifted by ~+90 lines from prior baseline due to helper additions, no new sorries | 0 (sorry count unchanged at 9; 90-line addition; build clean) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-scope-discovery | Scope investigation on the `defns` sub-step (no code change, baseline preserved).  Original "~1 step" estimate on `defns` was based on adding pkRec preservation conjunct to the three `EmitScansInFlow{,List,PairList}` definitions and re-proving consumers.  Implementation attempt revealed an additional infrastructure dependency: chain proofs through helpers require intermediate `j < intermediate.pendingKeys.size` bounds, derivable only from size monotonicity (`s.pendingKeys.size ≤ s'.pendingKeys.size`); the helpers from sub-step 1 (`helpers`) expose pkRec preservation but NOT size monotonicity.  Without size-mono, given outer hypothesis `j < s.pendingKeys.size` and `j < s_end.pendingKeys.size`, we can't derive `j < s_intermediate.pendingKeys.size` to apply each step's pkRec conjunct.  Refined sizing: ~2.5 steps for `defns`, decomposed into `defns-helpers-size` (extend 6 helpers with size-mono conjunct + new `saveSimpleKey_pendingKeys_size_ge` foundational lemma; `_preprocess_flow_ws1` already provides full pendingKeys equality), `defns-prove` (add size-mono + pkRec to 3 definitions, re-prove consumers), `defns-consumers` (update downstream destructures in `body_filtered_characterization` callers).  Partial implementation explored (extended `EmitScansInFlow{,List,PairList}` definitions and 2 of 6 helpers — `_comma`, `_open_nested` — plus added `saveSimpleKey_pendingKeys_size_ge`); reverted to keep baseline clean since the work spans more than one cadence step.  See open-bullet section's body-C decomposition for refined plan.  Baseline preserved exactly: 9 sorries, no edits committed | 0 (no code change; sorry count unchanged at 9; baseline preserved) | `Blueprint/07-initiative-3-append-only.md` (only) | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers | Helper-level pkRec (insertBeforeIdx + kind) preservation conjuncts on 7 of 8 scanner-helper theorems used inside `emit_scans_in_flow` and `emit{List,PairList}_scans_*` proofs.  Each conjunct is `∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size), s'.pendingKeys[j].insertBeforeIdx = s.pendingKeys[j].insertBeforeIdx ∧ s'.pendingKeys[j].kind = s.pendingKeys[j].kind`.  Foundational helper `saveSimpleKey_preserves_pkRec_prior` introduced (next to `saveSimpleKey_pkPush_when_allowed`) — under any preconditions, `saveSimpleKey` preserves prior-pkRec (push-or-id at the underlying pendingKeys array, preserves `insertBeforeIdx + kind` of all entries < initial size via `Array.getElem_push_lt`).  Helper theorems strengthened: (1) `scanNextToken_preprocess_flow_ws1` — full `s₁.pendingKeys = s.pendingKeys` (skipToContent doesn't touch pendingKeys, via `ScannerCorrectness.skipToContent_preserves_pendingKeys`); (2) `scanNextToken_flow_comma` — saveSimpleKey + scanFlowEntry chain (scanFlowEntry preserves pendingKeys); (3) `scanNextToken_flow_open_nested` (`[`) — saveSimpleKey + scanFlowSequenceStart chain; (4) `scanNextToken_flow_close_seq_nested` (`]`) — saveSimpleKey + scanFlowSequenceEnd chain; (5) `scanNextToken_flow_open_mapping_nested` (`{`) — saveSimpleKey + scanFlowMappingStart chain; (6) `scanNextToken_flow_close_mapping_nested` (`}`) — saveSimpleKey + scanFlowMappingEnd chain; (7) `scanNextToken_flow_scanDoubleQuoted` — saveSimpleKey + scanDoubleQuoted + dispatchContent wrap (uses existing `setPendingKeyEndLine_insertBeforeIdx` and `setPendingKeyEndLine_kind` lemmas — the wrap modifies only endLine).  Deferred to a follow-up sub-step: `scanNextToken_flow_value` — needs gated treatment because `scanValuePrepare`'s flow branch fires `setPendingKeyKind` at the active index, which can land at j < initial-size if the active was pre-set (this is the `:`-resolve path covered by Part2-body-B; the helper-style preservation needs an active-index gate).  All caller destructure patterns at consumer sites updated to bind the new conjunct as `_h_pks…` (10 callers across `emit_scans_in_flow` and `emit{List,PairList}_scans_nonempty`) | 0 (sorry count unchanged at 9 — locations shifted by ~+150 lines from prior baseline due to helper additions, no new sorries) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-compose | Discharged the body-C umbrella's final sub-step by extending `EmitPairListScansInFlow` with a first-pair resolved-key conjunct and using it to remove the sorry'd stub `emitPairList_chain_first_pkShape`.  Mechanism: (a) added a new conjunct to `EmitPairListScansInFlow` of shape `pairs ≠ [] → ∃ (h : s.pendingKeys.size < s'.pendingKeys.size), s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size ∧ s'.pendingKeys[s.pendingKeys.size].kind = .keyOnly` (gated on `pairs ≠ []` since the empty-pairs body returns the input state with no pendingKey resolution); (b) re-proved `emitPairList_scans_nonempty` (singleton + cons cases) by binding the previously-discarded resolved-entry conjunct from `scanNextToken_flow_value_pkResolve` (slot 15 of 17) and the previously-discarded insertBeforeIdx-equality from the gated A1 push (`_h_gated₁ h_ska`'s inner `⟨h_lt_pk_s1, h_ib_s1, _⟩`), then chaining the `(insertBeforeIdx, kind)` preservation through ws1 (preserves pendingKeys) → value (`_h_pkRec₃`/`_h_pkRec_v` at j = s.pendingKeys.size < s₃.size) → in cons also comma (`_h_pkRec_c`) → ws1 → recursive IH (`h_pkRec_r` at j < s_pp.size); (c) discharged `emitPairList_scans_empty`'s new conjunct vacuously (the precondition `[] ≠ []` is false); (d) threaded the new conjunct through `emitPairList_body_filtered_characterization`'s conclusion as a new Part (4) (no precondition gate needed since `h_ne` is already a hypothesis); (e) used the new Part (4) conjunct directly in `emitPairList_body_linearise_characterization` Part (2) — under `h_pks_empty : s.pendingKeys = #[]`, specialize the conjunct's index `s.pendingKeys.size` to `0` (via type-level `▸ rewrite`) to align with Foundation A's `[0]`-index splice; (f) **removed** the entire `emitPairList_chain_first_pkShape` sorry'd stub theorem (≈42 lines of signature + sorry'd body + docstring) since the wrapper now consumes the conjunct directly.  Cascading consumer updates: 4 destructures of `emitPairList_scans_nonempty` (recursive IH at line ~9787 `_h_first_r`; `emit_scans_in_flow` mapping at line ~10295 `_h_first₂`; `scanFiltered_exists_emit_aux` mapping at line ~10518 trailing `_`; `emitPairList_body_filtered_characterization` at line ~11865 `h_first` followed by `h_first h_ne` at the refine).  This **closes the body-C umbrella**: all 10 sub-steps under `J.4.2.b-2d-key-chain-Part2-body-C` are now ✓ done.  Sorry count: 9 → 8 | 0 (build clean across 453 jobs; -1 sorry net via stub removal; ≈100-line addition for the new conjunct + discharges, ≈42-line removal of the stub) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-scope-investigation | Scope investigation cadence (no code change, baseline preserved).  Original "~1 cadence step" estimate on `C-foundation-EmitScansInFlow` was based on adding a single `preserves-prior` conjunct + first-key gated conjuncts to the three `EmitScansInFlow{,List,PairList}` definitions and re-proving consumers.  Investigation revealed: (a) the FULL preserves-prior (record equality at indices < initial size) is NOT unconditional under the existing `EmitScansInFlow` precondition list — `dispatchContent`'s `setPendingKeyEndLine` wrap modifies `endLine` at the original active when `simpleKeyAllowed` is false at scan start, so endLine-preservation requires gating; (b) a WEAKER preserves-prior on (`insertBeforeIdx`, `kind`) only IS uniform (insertBeforeIdx is never mutated; kind is mutated only by `setPendingKeyKind` in `scanValuePrepare` flow branch, which fires at fresh-pushed indices ≥ initial size during `emit_scans_in_flow` body scans); (c) the consumers of these strengthenings (`emit_scans_in_flow` scalar/seq/map cases + `emit{List,PairList}_scans_{empty,nonempty}` family + `emitPairList_chain_first_pkShape` discharge) need pkRec preservation threaded through 8+ helper theorems (`scanNextToken_flow_scanDoubleQuoted`, `_open_nested`, `_close_seq_nested`, `_open_mapping_nested`, `_close_mapping_nested`, `_comma`, `_value`, `_preprocess_flow_ws1`); (d) seq/map cases of `emit_scans_in_flow` additionally need stack-restore lemmas for `scanFlowSequenceEnd` / `scanFlowMappingEnd` (`s'.simpleKey = s.simpleKeyStack.back?.getD {}` and `s'.pendingKeyActive = s.pendingKeyStack.back?.getD none`) plus `pendingKeyStack` preservation conjuncts on `EmitListScansInFlow` / `EmitPairListScansInFlow` (mirrors existing `simpleKeyStack` preservation).  Refined sizing: ~3-4 cadence steps to fully discharge `C-foundation-EmitScansInFlow`, decomposed into `helpers` (8 helper-theorem strengthenings) → `defns` (3 def strengthenings + helper re-proofs) → `stack-restore` (close-side restore lemmas + body-side stack preservation) → `gated` (first-key gated conjuncts on `EmitScansInFlow` under `h_ska` precondition).  See open-bullet section's body-C decomposition for full details.  Baseline preserved exactly: 9 sorries, no edits committed.  This entry tracks the cadence as honest scope investigation rather than failed implementation | 0 (no code change; sorry count unchanged at 9; baseline preserved) | `Blueprint/07-initiative-3-append-only.md` (only) | ✓ done 2026-05-01 |
| J.4.2.b-2d-key-chain-Part3-scope-investigation | Scope investigation cadence (no code change, baseline preserved at 8 sorries).  Original "~1–2 cadence steps" estimate on `Part3` was based on the assumption that Part3 would mirror C-compose's first-pair conjunct extension to all pairs and feed Foundation B (`linearise_splice_keyonly_at_index`) for the discharge.  Investigation revealed three distinct technical challenges that push the work to a multi-cadence cascade: **(a) Non-contiguous outer pendingKey indices.**  Pair `i`'s resolved `.keyOnly` entry sits at index `q_i = s_(i,pre).pendingKeys.size` in `s'.pendingKeys`, where `s_(i,pre)` is the state just before pair `i`'s key emit.  These `q_i` indices are NOT predictable as `s.pendingKeys.size + i` — they depend on the dynamic structure of values: if pair 0's value is a complex flow seq/map, it pushes its own pendingKeys at indices > `s.pendingKeys.size`, so `q_1 = q_0 + 1 + (nested pushes from pair 0's value)`.  The C-compose extension only exposed `q_0 = s.pendingKeys.size`; the per-pair extension must existentialize the entire `(q_0, ..., q_{n-1})` sequence with its order/properties.  **(b) Filtered → linearise position mapping.**  The Part (3) hypothesis is on the LINEARISE output (`linearise[k] = .flowEntry`, `flowBracketBalance ... = 0`), but chain-side facts speak about `s'.tokens` positions (in particular `pks[p].insertBeforeIdx`, which is a token-space position).  The linearise output has `.key` splices interleaved at every `.keyOnly` entry's `insertBeforeIdx`, so the `i`-th outer `.flowEntry` token sits at filtered position `f_i` (where `f_i = (s.tokens.filter p).size + (offset within body)` ) but linearise position `k_i = f_i + (number of .keyOnly entries with ib ≤ f_i)`.  Inner nested values contribute their own splices, complicating the count.  **(c) Walk-state construction at outer flowEntries.**  Foundation B requires a transport equation `linearise s'.tokens s'.pendingKeys = linearise.go s'.tokens s'.pendingKeys j p acc` with `acc.size = k + 1`, `pks[p].insertBeforeIdx ≤ j`, `pks[p].kind = .keyOnly`.  Constructing this `(j, p, acc)` requires a NEW foundation lemma (analogous to Foundation A's prefix-walk but with the walk state stopping just AFTER the `i`-th outer flowEntry copy): given a transport equation at state 0 and the per-pair locator, derive an intermediate transport equation at state `(j_i, q_i + 1, acc_i)`.  This walk-locator foundation is genuinely new infrastructure in `Proofs/Scanner/ScannerLinearise.lean`.  Subsidiary observation: `emitPairList_body_filtered_characterization` Parts (1)/(2)/(3) are sorry'd and currently UNUSED by the linearise wrapper (consumers underscore `_h_body_key, _h_body_fe_next` and only use `h_first_key` from Part (4)).  In particular Part (2)/(3) state `filtered[…] = .key`, but `.key` tokens are only emitted by `scanKey` (the `?` indicator) — not by `:`-resolution — so the filtered claims as currently stated are NOT provable for `emit.emitPairList` output.  These dead Parts (2)/(3) on the filtered char will likely need restating (e.g., to expose per-pair pendingKey shape) or removing as part of Part3.  Refined sizing: ~5–6 cadence steps to fully discharge `Part3`, decomposed into the open-bullet sub-steps below.  Baseline preserved exactly: 8 sorries, no edits committed.  This entry tracks the cadence as honest scope investigation rather than failed implementation | 0 (no code change; sorry count unchanged at 8; baseline preserved) | `Blueprint/07-initiative-3-append-only.md` (only) | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-locator-shape | Design-decision cadence (no code change, baseline preserved at 8 sorries).  Settles the precise per-pair locator shape for the new conjunct on `EmitPairListScansInFlow` (open-bullet sub-step 2 of the Part3 cascade).  **Candidates considered:** (i) array form `∃ (qs : Array Nat), qs.size = pairs.length ∧ qs[0] = s.pendingKeys.size ∧ ∀ i, ⟨qs[i] < s'.pendingKeys.size, kind = .keyOnly⟩ ∧ strict-monotone-qs`; (ii) recursive sigma-list shape mirroring the cons induction's structure; (iii) per-i existential `∀ i ∈ [0, pairs.length), ∃ q, ⟨properties⟩`.  **Decision: (i) array form.**  Rationale: (ii) is unworkable because the cons-induction's intermediate state `s_pp` (between the head pair's recursive ws-step and the IH's tail body) is NOT visible from the predicate signature `(s, s')`, so a recursive shape can't reference the per-pair anchor `s_(i,pre).pendingKeys.size` symbolically; (iii) lacks a natural way to express strict monotonicity across `i` without an explicit array witness, and the consumer in sub-step 5 (`Part3-walk-locator-foundation`) wants a fixed array to walk over — re-extracting the array from a per-`i` existential each time would re-introduce the same complexity (i) avoids upfront.  Cons-case construction for (i): `qs = #[s.pendingKeys.size] ++ qs_tail` where `qs_tail` is the IH's array on the tail (under state `s_pp`).  Strict monotonicity at the seam `qs[0] < qs[1]` follows from `s.pendingKeys.size < s_pp.pendingKeys.size` (the head pair's gated A1 push at s→s₁, preserved through `:`/value/comma/ws₁ to s_pp); the rest follows from the IH's monotonicity on `qs_tail`.  Singleton case: `qs = #[s.pendingKeys.size]`.  **Final conjunct shape (added in sub-step 3):** under `pairs ≠ []`, `∃ (qs : Array Nat) (h_size : qs.size = pairs.length) (h_pos : 0 < qs.size), qs[0]'h_pos = s.pendingKeys.size ∧ (∀ i (h : i < qs.size), ∃ (h_lt : qs[i]'h < s'.pendingKeys.size), (s'.pendingKeys[qs[i]]'h_lt).kind = .keyOnly) ∧ (∀ i j (hi : i < qs.size) (hj : j < qs.size), i < j → qs[i]'hi < qs[j]'hj)`.  **`insertBeforeIdx` deferred:** the conjunct does NOT include per-pair `insertBeforeIdx` info.  Foundation B's splice-firing precondition `pks[p].insertBeforeIdx ≤ j` will be discharged in sub-step 5 from the SCANNER-LEVEL fact that `pks` insertBeforeIdx is monotonic in pendingKey-index (a saveSimpleKey invariant: each push records `insertBeforeIdx = current tokens.size`, which only grows over the chain).  If sub-step 5 uncovers a gap, the conjunct can be extended in sub-step 3 to also expose the per-pair `insertBeforeIdx` array.  **Existing first-key conjunct retained:** the existing `pairs ≠ [] → ∃ h, pks[s.pendingKeys.size].(insertBeforeIdx,kind) = (s.tokens.size, .keyOnly)` conjunct (added by C-compose) is KEPT alongside the new array conjunct rather than subsumed.  Reason: the existing conjunct is consumed at three sites (linearise wrapper at line ~12036 via `h_first_key`; recursive IH destructure at line ~9816 via `_h_first_r`; mapping consumers at lines ~10295/~10518) — subsuming would require refactoring all three sites and provide no information not already implied by `qs[0] = s.pendingKeys.size` ∧ `pks[qs[0]].kind = .keyOnly`.  The redundancy is cheap (one `∃` + a few conjuncts).  **Open question for sub-step 3:** does the `qs` array's `Array.append`-construction in the cons case need a Lean-prelude lemma about `(#[x] ++ a).size = 1 + a.size` and `(#[x] ++ a)[0] = x`?  These are standard `Array` / `Array.append` lemmas; expect `Array.size_append`, `Array.getElem_append_left` (for `i = 0`), and `Array.getElem_append_right` (for `i ≥ 1`) to suffice.  Baseline preserved exactly: 8 sorries, no edits committed.  This entry tracks the design decision before mechanical extension lands in sub-step 3 | 0 (no code change; sorry count unchanged at 8; baseline preserved) | `Blueprint/07-initiative-3-append-only.md` (only) | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-extend-EmitPairListScansInFlow-per-pair | Mechanical extension of `EmitPairListScansInFlow` with the per-pair locator conjunct chosen in `Part3-locator-shape` (sub-step 3 of the Part3 cascade).  **Definition extension:** added a second gated conjunct to `EmitPairListScansInFlow` of shape `pairs ≠ [] → ∃ (qs : Array Nat) (_h_size : qs.size = pairs.length) (h_pos : 0 < qs.size), qs[0]'h_pos = s.pendingKeys.size ∧ (∀ i (h : i < qs.size), ∃ (h_lt : qs[i]'h < s'.pendingKeys.size), (s'.pendingKeys[qs[i]'h]'h_lt).kind = .keyOnly) ∧ strict-monotone-qs`, retaining the existing C-compose first-key conjunct alongside.  **`emitPairList_scans_empty`:** vacuous discharge `fun h_ne => absurd rfl h_ne`, mirroring the existing first-key conjunct's empty-case discharge.  **`emitPairList_scans_nonempty` singleton case:** `qs = #[s.pendingKeys.size]`; per-i (only `i = 0`) reuses the first-key conjunct's resolution-chain pre-derivation; strict-mono vacuous (single element).  **Cons case:** `qs = #[s.pendingKeys.size] ++ qs_tail` where `qs_tail` is the IH's array on the tail under state `s_pp`; per-i splits on `i = 0` (head pair facts) vs `i = j+1` (IH's `h_per_i_t j` after `Array.getElem_append_right` rewrite); strict-mono splits on `(a = 0, b = b'+1)` (uses `h_lt_s_spp : s.pendingKeys.size < s_pp.pendingKeys.size` plus IH's `h_strict_t 0 b'`) vs `(a = a'+1, b = b'+1)` (direct IH `h_strict_t a' b'`).  **Restructuring:** both non-empty branches were restructured to PRE-DERIVE the shared first-pair facts (`h_lt_s_send : s.pendingKeys.size < s_end.pendingKeys.size`, `h_kd_s_end`, `h_ib_s_end`) BEFORE the trailing `refine ⟨h_size_all, h_pkRec_all, ?_, ?_, ?_⟩`, so the new Part3 bullet can reuse them alongside the existing first-key bullet (Lean's `refine`-bullet scoping isolates per-bullet `have`s, so without pre-derivation each bullet would have to redo the chain).  **Destructure sites:** updated 3 explicit-name sites (recursive IH `_h_first_r⟩` → `_h_first_r, h_first_qs_r⟩` at line ~9816, used by the cons-case discharge to bind the IH's qs_tail; `emit_scans_in_flow` mapping `_h_first₂⟩` → `_h_first₂, _h_first_qs₂⟩` at line ~10295; `emitPairList_body_filtered_characterization` `h_first⟩` → `h_first, _h_first_qs⟩` at line ~11873); the 4th candidate site (`scanFiltered_exists_emit_aux` ~10518) uses anonymous-`_` placeholders that auto-absorb the new conjunct via the trailing residual conjunction (no edit needed).  **Lean idiom snag:** `decide` on `0 < (#[s.pendingKeys.size] : Array Nat).size` fails with "Expected type must not contain free variables" because Lean's `Decidable` evaluator refuses to fully reduce `Array.size #[x]` when `x` is opaque — the `Decidable.isTrue` constructor can't be synthesized symbolically.  Worked around via `h_size_one ▸ Nat.zero_lt_one` (where `h_size_one : (#[s.pendingKeys.size] : Array Nat).size = 1 := rfl` — `rfl` works because definitional equality doesn't require constructor evaluation).  Lemma usage: `Array.size_append`, `Array.getElem_append_left` (i = 0), `Array.getElem_append_right` (i ≥ 1) — all standard Lean prelude, no new infrastructure needed.  Sorry count unchanged at 8 (build replays 78/453 EmitterScannability jobs; total 453 jobs green) | 0 (build clean across 453 jobs; ≈100-line addition net for the new conjunct + discharges; no sorry change) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-thread-body-filtered-char | Mechanical threading of the per-pair locator conjunct (added by `Part3-extend-EmitPairListScansInFlow-per-pair`) through `emitPairList_body_filtered_characterization`'s conclusion as Part (5) (sub-step 4 of the Part3 cascade, ~0.5 step estimated, ~0.3 step actual since destructure binding was already in place).  **Conjunct shape:** identical to the `EmitPairListScansInFlow` Part3 conjunct (re-stated at the body-characterization layer rather than wrapped, so consumers like the linearise wrapper and Tier 1 stitching don't need to re-invoke `emitPairList_scans_nonempty` to access the per-pair locator).  Under `pairs ≠ []`: `∃ (qs : Array Nat) (_h_size : qs.size = pairs.length) (h_pos : 0 < qs.size), qs[0]'h_pos = s.pendingKeys.size ∧ ⟨per-i keyOnly readout⟩ ∧ strict-monotone-qs`.  Note absence of `pairs ≠ [] →` precondition gate at this layer: the body characterization already takes `h_ne : pairs ≠ []` as a hypothesis, so the ungated form is correct.  **Discharge:** the destructure of `h_scan := emitPairList_scans_nonempty …` at line ~11997 already exposed `_h_first_qs` from the `Part3-extend` sub-step's binding contract; the only proof edit was renaming `_h_first_qs` → `h_first_qs` and appending `h_first_qs h_ne` to the closing `refine ⟨…, h_first h_ne, h_first_qs h_ne⟩` anonymous constructor (no proof body change beyond the binding rename).  **Destructure sites updated (2):** (a) `emitPairList_body_linearise_characterization` ~12120 — added slot `_h_first_qs` after `h_first_key` (unused at this layer; reserved for sub-step 6 `Part3-final-discharge`); (b) `scanFiltered_emitMap_nonempty_structure` ~12459 — added slot `_h_body_first_qs` after `_h_body_first` (unused at this layer; the Tier 1 stitching is downstream of the linearise wrapper so it consumes the linearise wrapper's sorry'd Part (3) directly rather than re-walking the locator).  Sorry count unchanged at 8 (8 sorries at lines 11325, 11734, 11943, 12088, 12222, 12445, 13167, 13206; 57/57 EmitterScannability jobs green) | 0 (build clean across 57 EmitterScannability jobs; ≈40-line addition for the Part (5) conjunct + 1-line `refine` extension + 2 destructure-site `_`-prefixed slots; no sorry change) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6a | Chain-side cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6a (split: 6a chain-side now, 6b linearise-side + lift-discharge next).  **Goal:** expose, in the cons case of `emitPairList_scans_nonempty`, the predecessor-flowEntry fact so that the linearise-side bridge (sub-step 6b) can invert the walk-locator and identify which outer flowEntry sits at a given linearise position.  **Predicate extension:** added a fourth sub-conjunct to `EmitPairListScansInFlow`'s per-pair locator (under `pairs ≠ []`): `∀ i (hi : i < qs.size) (_h_pos_i : 0 < i), ∃ (h_lt : qs[i]'hi < s'.pendingKeys.size) (_h_ib_pos : 0 < (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx) (h_pred_lt : (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx - 1 < s'.tokens.size), (s'.tokens[(s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx - 1]'h_pred_lt).val = .flowEntry`.  **`emitPairList_scans_empty`:** vacuous via the existing `pairs ≠ []` gate (the `absurd rfl h_ne` already in tree).  **Singleton case (`pairs = [p]`):** vacuous — `qs = #[s.pendingKeys.size]` has only `i = 0`, so `0 < i` is false.  **Cons case:** decomposes the new conjunct on `i = j + 1`, `j < qs_tail.size`.  For `j ≥ 1`: applies the IH's predecessor-flowEntry conjunct (`h_pred_t j h_j (by omega)`) directly via `qs[j+1] = qs_tail[j]` (cons-append rewrite).  For `j = 0` (outer `i = 1`): the predecessor index is `qs_tail[0] = s_pp.pendingKeys.size`, and the IH's first-pair conjunct (C-compose) gives `pks[s_pp.pendingKeys.size].insertBeforeIdx = s_pp.tokens.size = s_c.tokens.size = s_v.tokens.size + 1` (via `h_toks_pp` + the comma push).  The token at index `s_v.tokens.size` in `s_c.tokens` is `.flowEntry` (newly exposed by `scanNextToken_flow_comma`'s extension; see below).  **Sub-task 6a-i1-lift sorry'd at line 9543:** lifting the `.flowEntry` fact from `s_c.tokens` (or `s_pp.tokens`) to `s_end.tokens` requires `FlowMonoChain_preserves_raw_prefix` which needs `SimpleKeyAboveFloor s_pp s_pp.tokens.size s_pp.flowLevel` — depending on tracing `s_pp.simpleKey`/`simpleKeyStack` state through the comma + ws1 sequence (out of scope for 6a; deferred to 6b).  **`scanNextToken_flow_comma` extension:** added one extra conjunct `(s'.tokens.size = s.tokens.size + 1) ∧ (∀ (h_lt : s.tokens.size < s'.tokens.size), (s'.tokens[s.tokens.size]'h_lt).val = .flowEntry)` to expose the comma's flowEntry push.  Proof: chase tokens through `advance` (preserves), `record-update` (preserves), `emit .flowEntry` (`s.tokens.push ⟨s.currentPos, .flowEntry, s.currentPos⟩`), `allowDirectives if-update` (both branches preserve tokens), `saveSimpleKey` (preserves tokens via `saveSimpleKey_preserves_tokens`).  The dependent `[size]'h_lt` indexing in the proof needed a `generalize`+`subst` pattern to substitute the underlying array via the equation lemma before applying `Array.getElem_push_eq`.  **Threading:** the new conjunct propagated through `emitPairList_body_filtered_characterization`'s conclusion as part of the per-pair existential (Part 5) — single `∃` binding so consumer destructure sites (recursive IH ~9914, mapping ~10528, filtered-char ~12015, Tier 1 emitMap ~12598) auto-absorb the new sub-conjunct without edit.  Two `scanNextToken_flow_comma` callers (line ~8627 in singleton emitList comma + line ~9883 in cons emitPairList comma) updated with one extra `_`/named slot each.  **Sorry count: 8 → 9** (+1 from the 6a-i1-lift sub-task, to be discharged in 6b).  Build green (453/453 jobs) | +1 (build clean across 453 jobs; ~110-line addition for the new conjunct + comma extension + cons discharge; +1 sorry from 6a-i1-lift) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2c | Scalar discharge cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-ii-γ-2c (third of γ-2's four sub-steps; discharges the bundled `(balance = 0 ∧ no-outer-flowEntry)` conjunct in the scalar branch of `emit_scans_in_flow`).  **Lower-level strengthening:** `scanDoubleQuoted_flow_ok` (in `Proofs/Output/EmitterScannability.lean`, line ~3275) gained a bundled token-push conjunct `(s'.tokens.size = sc.tokens.size + 1 ∧ ∀ h_lt, s'.tokens[sc.tokens.size].val = .scalar content .doubleQuoted)`.  Discharge: the proof already builds `s_result := { (s_after.emitAt sc.currentPos (.scalar content .doubleQuoted)) with simpleKeyAllowed := false }` and has `h_tok_pres : s_after.tokens = sc.tokens` — combining gives `s_result.tokens = sc.tokens.push ⟨sc.currentPos, .scalar content .doubleQuoted, sc.currentPos⟩`.  Used the standard `generalize`+`subst` motive-shielding pattern for the dependent indexing.  **Outer strengthening:** `scanNextToken_flow_scanDoubleQuoted` (line ~4686) propagates the conjunct through (a) `saveSimpleKey` + `allowDirectives` wrappers (introduced explicit `h_ad_tokens : s_ad.tokens = s.tokens`), (b) the inner `scanDoubleQuoted` push, (c) the `dispatchContent` simpleKey.possible branch — both branches preserve tokens (the `simpleKey.possible = true` branch wraps with `setPendingKeyEndLine`, which only mutates pendingKeys).  Uses `change` to coerce the structural-update-record to the canonical form needed for `congr 1` on the index.  **Caller updates:** the secondary `scanNextToken_flow_scanDoubleQuoted_pkPush` at line ~5063 added an `_h_dq_token_push` slot (discarded; pkPush variant doesn't need it).  The scalar-case caller in `emit_scans_in_flow` at line ~11136 binds the new conjunct as `h_token_push'` and threads it into the bundled discharge.  **Discharge in `emit_scans_in_flow`'s scalar branch:** the bundled goal splits into two parts.  Balance over `[s_state.tokens.size, s'.tokens.size) = [n, n+1)` reduces to `flowBracketDelta` of the single token via `flowBracketBalance_single`; the token is `.scalar`, which falls through to `flowBracketDelta`'s catch-all `_ => 0` arm.  No-outer-flowEntry: the only valid `kk` in range is `s_state.tokens.size`, where the token is `.scalar`, contradicting `.val = .flowEntry`.  **Lean-tactic notes:** `decide` fails on `flowBracketDelta (.scalar s.content ...) = 0` because the `s.content` is a free variable that prevents whnf normalisation; use `rfl` instead (the `_ => 0` catch-all arm reduces definitionally).  Same issue with `(.scalar s.content ... = .flowEntry)`: use `nofun` (matches all constructors and refutes the equality) instead of `(by decide)`.  For the dependent indexing `s_dq.tokens[s.tokens.size]'h_lt`, the `congr 1` after a `have h_size_eq : s_ad.tokens.size = s.tokens.size` lets us bridge between equal-sized arrays without triggering motive-not-type-correct errors (the equality of `Nat`-valued sizes is enough to justify the `getElem` rewriting).  **Sorry count: 11 → 10** (-1 from `emit_scans_in_flow` scalar; raw sorry count drops from 15 to 14 inline occurrences; declaration count: 9 → 9 since `emit_scans_in_flow` still has sequence + mapping sorrys remaining).  Build green (453/453 jobs).  **Why this scope:** smallest unit of progress on γ-2's four sub-steps, mirrors γ-2b's chain-side discharge structure.  Cascade after γ-2c: 10 → 8 (γ-2d: seq/map) → 7 (γ-3). | -1 (build clean across 453 jobs; ~70-line addition for the bundled conjunct in `scanDoubleQuoted_flow_ok` + propagation through `scanNextToken_flow_scanDoubleQuoted`'s two simpleKey branches + scalar-case discharge in `emit_scans_in_flow`; -1 sorry) | `Proofs/Output/EmitterScannability.lean`, `Blueprint/07-initiative-3-append-only.md` | ✓ done 2026-05-03 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2b | Chain-side γ-1 discharge cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-ii-γ-2b (consumer-half of γ-2: discharges the two chain-side outer-flowEntry exhaustiveness sorrys in `emitPairList_scans_nonempty` introduced by γ-1, using the bundled `EmitScansInFlow` conjunct landed in γ-2a).  **Helper lemma added (~30 lines):** `flowBracketBalance_FlowMonoChain` — bracket balance over `[lo, hi)` is preserved through any `FlowMonoChain` when `hi ≤ s.tokens.size` (chain's initial state).  Proof: the slice `tokens.toList.drop lo |>.take (hi - lo)` is the same in both states (each chain step preserves the prefix elementwise via `FlowMonoChain_preserves_existing_tokens`), so the foldl computing balance is identical.  Uses `List.drop_take` to convert between the two equivalent slice forms.  **`scanNextToken_flow_value` strengthened:** added bundled conjunct `(s'.tokens.size = s.tokens.size + 1 ∧ ∀ h_lt, s'.tokens[s.tokens.size].val = .value)` mirroring `scanNextToken_flow_comma`'s comma-push conjunct.  Proof chases tokens through `s.advance` ← `s_tok.advance` ← `s_prep.emit .value` ← `scanValuePrepare s_ad` (all preserve except the `emit .value` which appends one token); uses `generalize`+`subst` pattern for the dependent indexing `Array.getElem_push_eq`.  Two callers updated (singleton at line ~9748, cons at line ~9990) to bind the new conjunct as `h_colon_push_singleton`/`h_colon_push_cons`; `scanNextToken_flow_value_pkResolve` discards the conjunct (its callers don't need it directly — the singleton/cons γ-1 discharges call the underlying `scanNextToken_flow_value` first, which already exposes the push fact).  **Singleton discharge (line ~9755):** chain `s → s_end` is `emit(p.1) → ":" → ws1 → emit(p.2)`.  Case-split on `kk`: (1) `kk < s₁.size` — token + balance preservation via FMC `s₁ → s_end`, contradict via `h_balfacts_k_singleton.exh`; (2) `kk = s₁.size` — the colon's `.value` token, contradicts `s_end.tokens[kk].val = .flowEntry` via FMC preservation + `h_colon_push_singleton`; (3) `s₁.size < kk < s₂.size` — empty (`s₂.size = s₁.size + 1`); (4) `s₂.size ≤ kk < s₃.size` — empty (ws1 preserves tokens); (5) `s₃.size ≤ kk < s_end.size` — apply `h_balfacts_v_singleton.exh` directly (over `s_end.tokens`); compose balance `bal s_end s.size kk = bal s_end s.size s₃.size + bal s_end s₃.size kk` with the first piece = 0 (via key + colon-delta-0 + ws1 sub-balances).  Goal becomes `False` (`qs.size = 1` excludes `0 < i < 1`).  **Cons discharge (line ~10581):** chain has 7 segments (key/colon/ws1/value/comma/ws_pp/IH).  Three sub-FMCs extracted (`h_fmc_s1_send`, `h_fmc_sv_send`, `h_fmc_s2_send`) and six sub-balances proven 0 (key + colon-`.value` + ws1 + value + comma-`.flowEntry` + ws_pp; `.value` and `.flowEntry` both have `flowBracketDelta = 0`).  Composed `bal s_end s.size s_pp.size = 0`.  Case-split on `kk`: cases 1–4 (in `[s.size, s_v.size)`) contradict via key/value bundled exhaustiveness conjuncts; case 5 (`kk = s_v.size`) is the comma's flowEntry, witness construction via `qs[1] = qs_tail[0] = s_pp.pendingKeys.size` (using `h_q0_t` + `h_first_r`'s `h_ib_pp = s_pp.tokens.size`); case 6 (empty); case 7 (`kk ≥ s_pp.size`) lifts to IH's exhaustiveness `_h_exh_t` after composing `bal s_end s_pp.size kk = 0` from premise + `h_bal_s_pp_zero`, witness is `i_tail + 1`.  **Lean-tactic notes:** dependent-motive issues with `(#[s.pendingKeys.size] ++ qs_tail)[i]'h_lt` indexing inside `s_end.pendingKeys[...]'h_lt2` resolved by collapsing the trailing `refine ⟨h_lt, eq⟩` into a single `?_` slot before the `rw` (existential quantifier shields the motive); for the `Array.getElem_append_right`-derived equality, used `rw` on the standalone-form goal (`∃ h_lt, kk + 1 = (...).insertBeforeIdx`) where the dependent bound is hidden behind the `∃`.  `Nat.le.trans` does not exist in this Lean version; use `Nat.le_trans` explicitly.  After chained `rw [bal_compose, ..., h_bal_*]` ending at `0 + (0 + 0 + ...) = 0`, `rfl` may fail to fully reduce — use `decide` instead.  **Sorry count: 13 → 11** (-2 chain-side γ-1 sorrys at lines 9963/10567; no intermediate stubs added).  Build green (453/453 jobs).  **Why this scope:** consumer-half of γ-2 — the predicate strengthening from γ-2a is now usable, but the predicate's discharge in `emit_scans_in_flow` (γ-2c/d) is independent and still pending.  Cascade: 13 → 11 ✓ → 10 (γ-2c) → 8 (γ-2d) → 7 (γ-3). | -2 (build clean across 453 jobs; ~280-line addition for the helper lemma + scanNextToken_flow_value strengthening + singleton/cons discharges; -2 sorrys) | `Proofs/Output/EmitterScannability.lean`, `Blueprint/07-initiative-3-append-only.md` | ✓ done 2026-05-03 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2a | EmitScansInFlow strengthening cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-ii-γ-2a (predicate-level half of γ-2, after γ-2 was further decomposed into γ-2a (predicate strengthening), γ-2b (chain-side γ-1 sorry discharge), γ-2c (scalar discharge in `emit_scans_in_flow`), γ-2d (sequence/mapping discharge) — decomposition driven by scope discovery during this cadence).  **Insight:** discharging γ-1's chain-side sorrys requires a strengthened `EmitScansInFlow` invariant ("no outer-level `.flowEntry` pushed during emit body" + "balance returns to 0").  **Predicate extension:** added a single bundled conjunct to `EmitScansInFlow`: `(flowBracketBalance s'.tokens s.tokens.size s'.tokens.size = 0 ∧ ∀ (kk : Nat) (h_kk_lt : kk < s'.tokens.size) (_h_kk_ge : s.tokens.size ≤ kk), s'.tokens[kk].val = .flowEntry → flowBracketBalance s'.tokens s.tokens.size kk ≥ 1)`.  Bundled (rather than two separate `∧`s) so each `refine ⟨…, ?_⟩` site adds only ONE new slot.  **Destructure plumbing:** updated 6 destructure sites in `emitList_scans_nonempty` (singleton + cons) and `emitPairList_scans_nonempty` (singleton key/value, cons key/value) to extract `h_balfacts_*` from the bundled conjunct.  **`emit_scans_in_flow` plumbing:** updated all 3 cases (scalar/sequence/mapping) to provide the bundled conjunct via a new `?_` slot, with a `refine ⟨?_, ?_⟩`-prefixed split inside the existing `pendingKeyStack`/`gated` discharge bullet for sequence/mapping (scalar adds slot at end of refine).  **Discharge sorry'd at 3 sites:** scalar (line ~10566) — needs token-push lemma exposing scalar's `+1` token + `.scalar` val; sequence (line ~10800) and mapping (line ~10950) — need bracket-push lemmas + body-balance facts (cascades into `EmitListScansInFlow`/`EmitPairListScansInFlow` strengthening).  **Empty cases:** `emitList_scans_empty` and `emitPairList_scans_empty` — *not yet updated* in this cadence; they're 0-step chains where balance/no-outer should be trivially 0/vacuous, but the predicate now requires them and they need explicit construction.  **Architectural finding (recorded in in-tree comment):** full discharge requires (i) per-leaf token-push lemmas (currently absent), and (ii) a `flowBracketBalance` chain-extension lemma (also absent).  **Sorry count: 10 → 13** (+3 from 3 emit_scans_in_flow case sorrys; chain-side γ-1 sorrys at lines 9714/10546 retained — to be discharged in γ-2b).  Build green (57/57 EmitterScannability jobs).  **In-tree Part (3) comment updated** to refine γ-2 into γ-2a/2b/2c/2d.  **Why this scope:** the simplest unit of work that lays the architectural foundation; γ-2b (chain-side discharge using new conjunct) follows.  Final sorry count over the cascade: 10 → 13 (γ-2a) → 11 (γ-2b: −2 chain-side) → 10 (γ-2c: scalar) → 8 (γ-2d: seq/map) → 7 (γ-3: Part (3)). | +3 (build clean across 57 EmitterScannability jobs; ≈120-line addition for the bundled conjunct + threaded plumbing + 3 inline sorry stubs in `emit_scans_in_flow`; +3 sorry stubs total) | `Proofs/Output/EmitterScannability.lean`, `Blueprint/07-initiative-3-append-only.md` | ✓ done 2026-05-03 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-1 | Ghost-predicate strengthening cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-ii-γ (decomposed into γ-1/γ-2/γ-3 after scope investigation revealed the chain-side `qs` enumeration lacks an *exhaustiveness* fact needed to invert `k → i`).  **Insight (user-driven):** the missing fact is a ghost-predicate gap, not a proof-bookkeeping issue — the chain knows the only outer-level `.flowEntry` tokens above `s.tokens.size` are pair separators, but the predicate doesn't expose this.  Right architectural move: lift the fact into `EmitPairListScansInFlow` rather than work around it.  **Predicate extension:** added a fifth sub-conjunct to `EmitPairListScansInFlow`'s qs-locator existential (under `pairs ≠ []`): `∀ (kk : Nat) (h_kk_lt : kk < s'.tokens.size) (_h_kk_ge : s.tokens.size ≤ kk), s'.tokens[kk].val = .flowEntry → flowBracketBalance s'.tokens s.tokens.size kk = 0 → ∃ (i : Nat) (hi : i < qs.size) (_h_pos_i : 0 < i) (h_lt : qs[i] < s'.pendingKeys.size), kk + 1 = pks[qs[i]].insertBeforeIdx`.  Together with the `Part3-final-discharge-bridge-6a` predecessor-flowEntry conjunct (forward direction), this gives a bidirectional bijection between outer-level `.flowEntry` tokens and pair indices `i ≥ 1`.  **`emitPairList_scans_empty`:** vacuous via the existing `pairs ≠ []` gate.  **Singleton case discharge sorry'd (sub-task 6c-ii-γ-2):** the chain `s → s_end` consists of `emit p.1 + ":" + ws + emit p.2` (no comma push); proving "no outer-level `.flowEntry`" requires a strengthened `EmitScansInFlow` invariant ("no outer-level `.flowEntry` pushed during emit body").  **Cons case discharge sorry'd (sub-task 6c-ii-γ-2):** the chain decomposes into key/value emit segments (no outer `.flowEntry` by EmitScansInFlow strengthening) + comma push (matches `qs[1]`) + ws + IH on tail (uses tail's exhaustiveness conjunct).  **Threading:** the new conjunct propagated through `emitPairList_body_filtered_characterization`'s conclusion as a sub-conjunct of the per-pair existential (Part 5) — single `∃` binding, so consumer destructure sites (linearise wrapper ~12953, Tier 1 emitMap ~13340) auto-absorb without edit.  Body-characterization discharge unchanged (it just forwards `h_first_qs h_ne` from the now-strengthened `EmitPairListScansInFlow`).  **Sorry count: 8 → 10** (+2 from singleton + cons stub discharges; both narrow precisely to the "no outer-level `.flowEntry` pushed by EmitScansInFlow" sub-claim, to be discharged in 6c-ii-γ-2).  Build green (453/453 jobs).  **In-tree Part (3) comment updated** to document the γ→γ-1/γ-2/γ-3 decomposition.  **Why this cadence:** smallest unit of work that delivers the architectural strengthening; γ-2 (chain-side discharge) and γ-3 (linearise-side Part (3) discharge) follow.  Sorry count over the cascade: 8 → 10 → 8 → 7 (γ-3 discharges Part (3) sorry, γ-2 discharges γ-1's two stubs, possibly +1 from EmitScansInFlow strengthening intermediate). | +2 (build clean across 453 jobs; ~80-line addition for the predicate conjunct + threading + 2 inline sorry stubs; +2 sorry stubs in `emitPairList_scans_nonempty`) | `Proofs/Output/EmitterScannability.lean`, `Blueprint/07-initiative-3-append-only.md` | ✓ done 2026-05-03 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-β | Bracket-balance preservation cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-ii-β (consuming 6c-ii-α's algebra helpers; reusable infrastructure for 6c-ii-γ's inversion enumeration).  **Goal:** prove the parallel induction `linearise_go_walk_flowBracketBalance` over `linearise.go`'s lex-measure: the walk from `(j, p, acc)` to `(j', p', acc')` produces an `acc' = acc ++ extra` whose bracket balance over `[acc.size, acc.size + extra.size)` matches `flowBracketBalance tokens j j'`.  **New theorems (~280 lines total) added to `Proofs/Output/EmitterScannability.lean` (right after 6c-ii-α's helpers):** (a) `flowBracketBalance_append_left` — bracket balance is unchanged when appending an array, provided the range is fully inside the original (`hi ≤ xs.size`).  Generalises `flowBracketBalance_push` from a single-element extension to an arbitrary array extension via the same `Array.toList_append` / `List.drop_append` / `List.take_append` simp dance.  (b) `linearise_go_walk_flowBracketBalance` — the main lemma, existential form `∃ extra, linearise.go ... j p acc = linearise.go ... j' p' (acc ++ extra) ∧ flowBracketBalance (acc ++ extra) acc.size (acc.size + extra.size) = flowBracketBalance tokens j j'`.  Walk premises mirror `linearise_go_walk_eq` (in-range firings + barrier).  Proof by induction on the lex-measure `(j' - j) + (p' - p) = n`.  **Cases:** (n=0) `extra = #[]`, both sides trivially zero (`flowBracketBalance` is `0` when `lo ≥ hi`); (splice step) `extra := expandKind pks[p] ++ extra'` from IH; reshape `acc ++ (expandKind pks[p] ++ extra') = (acc ++ expandKind pks[p]) ++ extra'` via `Array.append_assoc.symm`; split balance at mid `(acc ++ expandKind pks[p]).size` via `flowBracketBalance_compose`; prefix piece reduces to 0 via `flowBracketBalance_append_left` + `flowBracketBalance_splice_unchanged` (zero balance over splice tokens); suffix matches IH's balance via two h_bal rewrites — convert `(acc ++ expandKind pks[p]).size + extra'.size → ((acc ++ expandKind pks[p]) ++ extra').size` (`Array.size_append.symm`) and `(acc ++ expandKind pks[p]).size → acc.size + (expandKind pks[p]).size` (`Array.size_append`); (copy step) `extra := #[tokens[j]] ++ extra'`; reshape `acc ++ (#[tokens[j]] ++ extra') = (acc.push tokens[j]) ++ extra'` via `Array.push_eq_append + Array.append_assoc`; split at mid `(acc.push tokens[j]).size`; prefix reduces to `flowBracketDelta tokens[j].val` via `flowBracketBalance_append_left` + `flowBracketBalance_push_extend` (with `(acc.push tokens[j]).size = acc.size + 1` rewrite); suffix matches IH's balance via two h_bal rewrites; RHS expanded via `flowBracketBalance_compose tokens j (j+1) j' + flowBracketBalance_single`; (p ≥ pks.size case) duplicates the copy case but uses `linearise_go_step_token` instead of `_step_copy`.  (c) `linearise_go_walk_flowBracketBalance_top` — convenience wrapper absorbing the lex-measure argument, mirroring `linearise_go_walk_eq_top`'s API.  **Lean-tactic notes:** `Array.append_assoc` and `Array.size_append` are no-arg theorems (all implicit args), not functions — the `_ _` / `_ _ _` application form fails (e.g., `(Array.size_append _ _).symm` triggers "Function expected at Array.size_append"); use bare `Array.append_assoc.symm` and `Array.size_append.symm`.  Trailing `rfl` after `flowBracketBalance_single tokens j _` bridges `tokens[j].val` ↔ `tokens.toList[j].val` definitional equality (these are `rfl`-equal but Lean's `rw` doesn't auto-close).  In-context the goal/h_bal both contain `(acc.push tok).size` (or `(acc ++ expandKind e).size`) at multiple positions (prefix hi, suffix lo, suffix hi); rewrite ordering matters because every `rw [show .size = +-form ...]` fires across all occurrences — careful sequencing avoids partial rewrites that leave the goal/h_bal mismatched.  **Sorry count unchanged at 8** (preservation lemma is reusable infrastructure consumed in 6c-ii-γ; the in-tree Part (3) sorry comment was updated to document 6c-ii-β's landing).  Build green (453/453 jobs) | 0 (build clean across 453 jobs; ~280-line addition for one helper + main lemma + top wrapper; no sorry change) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-α | Bracket-balance algebra cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-ii-α (decomposing 6c-ii into α/β/γ: α=algebra helpers now, β=preservation lemma next, γ=inversion enumeration + Part (3) discharge after).  **Goal:** add three reusable `flowBracketBalance` algebra helpers to `Proofs/Output/EmitterScannability.lean` (right before the J.4.2.b-2d section header), establishing the foundational facts for the upcoming bracket-balance preservation lemma (`linearise_go_walk_flowBracketBalance` in 6c-ii-β).  **New lemmas (~80 lines total):** (a) `expandKind_flowBracketDelta_zero` — splice tokens (`.key`, `.blockMappingStart`) have `flowBracketDelta = 0`.  Trivial corollary of `expandKind_val_neutral`: `rcases` on the disjunction, then `rfl` since `.key`/`.blockMappingStart` fall into `flowBracketDelta`'s catch-all `_ ⇒ 0` arm.  (b) `flowBracketBalance_push_extend` — pushing one token to `acc` and extending the balance range by 1 picks up the new token's `flowBracketDelta`: `flowBracketBalance (acc.push tok) lo (acc.size + 1) = flowBracketBalance acc lo acc.size + flowBracketDelta tok.val` for `lo ≤ acc.size`.  Proof: decompose `[lo, acc.size + 1]` via `flowBracketBalance_compose`; left piece unchanged by `flowBracketBalance_push`; right piece `[acc.size, acc.size + 1]` reduces to `flowBracketDelta` via `flowBracketBalance_single` + `Array.getElem_push_eq`.  Used `have h_idx_eq : (acc.push tok).toList[acc.size]'h_lt = tok` as a helper to bridge `.toList[i]` and `[i]` indexing without triggering motive-not-type-correct errors from `rw [Array.toList_push]`.  (c) `flowBracketBalance_splice_unchanged` — appending `expandKind e` to `acc` leaves bracket balance unchanged: `flowBracketBalance (acc ++ expandKind e) lo (acc.size + (expandKind e).size) = flowBracketBalance acc lo acc.size`.  Proof by case analysis on `e.kind`: `.unresolved` (empty array, range trivially unchanged); `.keyOnly` (one `.key` push, delta = 0); `.blockMappingStartAndKey` (two pushes, both delta = 0; required `Array.size_push` rewrite between the two `flowBracketBalance_push_extend` applications).  **Why these now:** the eventual inversion direction (6c-ii-γ) needs to translate the outer-level condition `flowBracketBalance (linearise tokens pks) old_sz k = 0` to a corresponding condition on `s'.tokens`; the bridge is preservation through `linearise.go` (6c-ii-β), which inducts over the walk's lex-measure with `flowBracketBalance_splice_unchanged` for splice steps and `flowBracketBalance_push_extend` for copy steps.  Landing the helpers separately keeps each cadence step bounded (~80 lines vs ~150 for the full induction) and gives the preservation proof a clean foundation.  **Lean-tactic notes:** `Array.append_empty` is `_ ++ #[] = _` (no-arg theorem), not a function — the `from Array.append_empty _` form fails; use bare `from Array.append_empty`.  Two-element array literal `#[bms, key]` matches `(acc.push bms).push key` after `acc ++ ...` definitionally, but extracting the size as `+ 2` requires intermediate rewrites via `Array.size_push`.  **Sorry count unchanged at 8** (helpers are reusable infrastructure consumed in 6c-ii-β/γ; the in-tree Part (3) sorry comment was updated to document 6c-ii-α's landing and the α/β/γ decomposition).  Build green (57/57 EmitterScannability jobs) | 0 (build clean across 57 EmitterScannability jobs; ~80-line addition for three helpers; no sorry change) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-i | Forward walk lemma cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6c-i (split: 6c-i forward walk lemma now, 6c-ii bracket-balance inversion + Part (3) discharge next).  **Goal:** add a reusable `ScannerLinearise` lemma that reads off the linearise output's predecessor token at the position immediately before each `.keyOnly` splice, complementing the existing `linearise_walk_at_kth_resolved_splice` (which reads `.key` at the splice's POST-fire position).  **New lemma `linearise_walk_at_kth_predecessor_token`:** under save-time strict monotonicity of `pks` at the prefix `[0, q)` (i.e., `∀ r < q, pks[r].insertBeforeIdx + 1 ≤ pks[q].insertBeforeIdx` — reflecting the at-least-one-token-between-saves invariant), `linearise tokens pks` has element `tokens[pks[q].insertBeforeIdx - 1]` at position `pks[q].insertBeforeIdx - 1 + (pks.foldl 0 0 q)`.  **Why strict monotonicity matters (vs the non-strict `h_idx_mono` of the splice-readout sibling):** if some `pks[r]` for `r < q` had the same `insertBeforeIdx` as `pks[q]`, then at the j-cursor reaching `pks[q].insertBeforeIdx` both `r` and `q` would be ready to splice — the walk loop fires `r` first, so the LAST push to `acc` before reaching state `(j, q, acc)` would be a splice (`.key` or empty), not a token copy.  Strict monotonicity rules this out, ensuring the predecessor in `acc` is exactly `tokens[pks[q].insertBeforeIdx - 1]`.  **Proof structure (~120 lines):** (a) walk from `(0, 0, #[])` to `(pks[q].insertBeforeIdx - 1, q, acc')` via `linearise_go_walk_eq_top` — in-range condition holds by strict monotonicity, barrier by `(j-1) ≤ j` reflexivity; (b) take a single token-copy step (`linearise_go_step_copy`) advancing to `(pks[q].insertBeforeIdx, q, acc'.push tokens[j-1])`; (c) pin `acc'.size = (j-1) + foldlSum_q` via `linearise_go_walk_size` + the existing `pendingExpandSumFrom`-foldl bridge; (d) apply `linearise_go_getElem_lt_acc` to read off the predecessor token at `acc'.size`.  **Forward bridge structure now in tree:** combining 6c-i with `linearise_walk_at_kth_resolved_splice` and the chain-side `tokens[pks[qs[i]].insertBeforeIdx - 1] = .flowEntry` (from `h_first_qs`'s predecessor-flowEntry conjunct — landed in 6a, lifted in 6b) yields the structural pattern `.flowEntry → .key` at consecutive linearise positions for each pair `i ≥ 1`.  **Inverse direction (6c-ii) deferred:** identifying which pair index `i` corresponds to a given outer-level flowEntry's linearise position requires bracket-balance accounting on linearise — leveraging the fact that spliced tokens (`.key`, `.blockMappingStart`) have `flowBracketDelta = 0`, so flow bracket balance on linearise corresponds 1:1 with flow bracket balance on `s'.tokens` modulo splice-position shifts.  **Lean-tactic notes:** `set ... with` is not in scope here (no Mathlib import); used `let` + a small inline `h_get_eq_idx` helper for index-equality rewriting under GetElem (the bound-proof argument is propositionally irrelevant in Lean 4, but `subst` requires a free variable on one side of the equality, hence the helper).  **Sorry count unchanged at 8** (forward lemma is reusable infrastructure consumed in 6c-ii's discharge; the in-tree Part (3) sorry comment was updated to document 6c-i's progress).  Build green (453/453 jobs) | 0 (build clean across 453 jobs; ~120-line addition; no sorry change) | `Proofs/Scanner/ScannerLinearise.lean`, `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6b | i1-lift discharge cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 6b (revised scope: 6b discharges only the i1-lift; the linearise-side bridge inversion is split out into a new sub-step 6c).  **Goal:** discharge the 6a-i1-lift sorry at line 9543 (cons-case `j = 0`, outer `i = 1` predecessor-flowEntry conjunct).  **Original plan:** establish `SimpleKeyAboveFloor s_pp s_pp.tokens.size s_pp.flowLevel` and apply `FlowMonoChain_preserves_raw_prefix` to the IH chain.  **Issue with original plan:** at `s_pp` (post-comma + ws1), `simpleKey.tokenIndex = s_v.tokens.size = s_pp.tokens.size - 1`, so `SimpleKeyAboveFloor s_pp s_pp.tokens.size _` would FAIL conjunct (1) (`tokenIndex ≥ s_pp.tokens.size`).  Tracing simpleKey/simpleKeyStack state through comma + ws1 to find a different floor `n₀` that works would require non-trivial state analysis.  **Revised approach (cleaner):** added a Path C **unconditional** strict prefix preservation lemma — leveraging the fact that post-cutover scanner is append-only on `tokens` (no `setIfInBounds`), prefix preservation holds without any simpleKey hypothesis.  **Helper lemmas added in `Proofs/Output/EmitterScannability.lean`:** (a) `dispatchBlockIndicators_preserves_prefix_strict` — mirrors the legacy `ScanHelpers.dispatchBlockIndicators_preserves_prefix` but routes the `:` (scanValue) case through `scanValue_preserves_prefix_strict` (already discharged in `ScannerCorrectness`), dropping the h_inv requirement; scanBlockEntry/scanKey are unconditional already.  (b) `scanNextToken_preserves_prefix_strict` — mirrors `scanNextToken_preserves_prefix_of_skFloor` but uses the strict block dispatch, dropping the `SimpleKeyAboveFloor` h_sk hypothesis.  (c) `FlowMonoChain_preserves_existing_tokens` — chain version: takes only `FlowMonoChain fl₀ s n s'` (and `i < s.tokens.size`), inducts using the strict per-step lemma; cleaner signature than `FlowMonoChain_preserves_raw_prefix`.  **6a-i1-lift discharge:** at `j = 0`, qs_tail[0] = s_pp.pendingKeys.size (h_q0_t).  IH's first-key fact (h_first_r) gives `pks[s_pp.pendingKeys.size].insertBeforeIdx = s_pp.tokens.size`.  Combined with the comma push (`s_c.tokens.size = s_v.tokens.size + 1`, `s_c.tokens[s_v.tokens.size].val = .flowEntry`) and ws1 (`h_toks_pp : s_pp.tokens = s_c.tokens`), we get `s_pp.tokens[s_v.tokens.size].val = .flowEntry`.  `FlowMonoChain_preserves_existing_tokens h_fmc_r s_v.tokens.size h_sv_lt_pp` lifts this through the IH chain to `s_end.tokens[s_v.tokens.size].val = .flowEntry`, which equals the predecessor at `pks[s_pp.pendingKeys.size].insertBeforeIdx - 1`.  Used a `generalize`+`subst` pattern for the dependent indexing in `s_pp.tokens = s_c.tokens` substitution.  **Linearise-side bridge inversion deferred to 6c:** the Part (3) sorry in `emitPairList_body_linearise_characterization` (line ~12535) requires inverting from arbitrary outer-level flowEntry positions `k` to specific pair indices `i ≥ 1` — this needs bracket-balance accounting to enumerate outer-level flowEntries and is a separate substantial proof artifact.  Documented in-place at the Part (3) sorry comment.  **Sorry count: 9 → 8** (closes 6a-i1-lift; Part (3) deferred).  Build green (453/453 jobs) | -1 (build clean across 453 jobs; ~150-line addition for the strict prefix preservation suite + ~50-line discharge of the 6a-i1-lift; -1 sorry from 6a-i1-lift) | `Proofs/Output/EmitterScannability.lean` | ✓ done 2026-05-02 |
| J.4.2.b-2d-key-chain-Part3-walk-locator-foundation | Foundation cadence for the J.4.2.b-2d-key Part3 cascade's sub-step 5: added `linearise_walk_at_kth_resolved_splice` and four supporting declarations to `Proofs/Scanner/ScannerLinearise.lean` (~190 net lines).  **Sub-lemmas added:** (a) `linearise_go_step_splice` / `linearise_go_step_copy` — one-step unfoldings of `linearise.go` for the splice-fires and token-copy cases (companions to the existing `linearise_go_step_token`).  (b) `linearise_go_walk_eq` — the workhorse: from a transport equation at state `(j, p, acc)` to `(j', p', acc')` given the **in-range** condition (`pks[r].insertBeforeIdx ≤ j'` for `r ∈ [p, p')`) and **barrier** condition (`pks[p'].insertBeforeIdx ≥ j'` if `p' < pks.size`).  Proof: induction on the lex-measure `(j' - j) + (p' - p)`; each `linearise.go` step either fires `pks[p]` or copies `tokens[j]`, decreasing the measure by 1.  Three branches in the recursive case (splice fires, token copy, pendings-exhausted token copy) plus a base case at measure 0.  (c) `linearise_go_walk_eq_top` — top-level wrapper absorbing the lex-measure argument.  (d) `linearise_go_walk_size` — derives `acc'.size + (tokens.size - j') + pendingExpandSumFrom pks p' = acc.size + (tokens.size - j) + pendingExpandSumFrom pks p` from the walk equation, by equating `linearise_go_size` on both sides.  **Main lemma `linearise_walk_at_kth_resolved_splice`:** per `i < qs.size`, the linearised output has `.key` at position `pks[qs[i]].insertBeforeIdx + (pks.foldl (fun n e => n + (expandKind e).size) 0 0 qs[i])`.  **Hypotheses:** `h_qs_lt`, `h_qs_kind`, `h_qs_mono` (from EmitPairListScansInFlow's Part3 conjunct), plus `h_idx_mono` (save-time monotonicity of `pks` insertBeforeIdx) and `h_idx_le` (every insertBeforeIdx ≤ tokens.size) — both expected from the chain endpoint invariant.  **Key design choice (better than the originally-sketched induction-on-i):** the walk-state equation lets us jump *directly* from `(0, 0, #[])` to `(j_i, qs[i], acc)` for any `i` — no induction over `i` needed in the main lemma itself.  The induction is implicit in `linearise_go_walk_eq` (over the lex-measure).  The "subsidiary lemma about `.unresolved` having zero expansion" mentioned in the original plan is also unnecessary: `linearise_go_walk_eq` handles all kinds uniformly, and the position formula uses the cumulative `expandKind` sum (foldl), so `.unresolved` contributions are correctly counted as 0 without a special case.  **Bridge to nested mappings:** the `prefixSum_i = pks.foldl 0 0 qs[i]` term accommodates inner-mapping `.keyOnly` entries between outer pairs — no "non-`qs` are `.unresolved`" hypothesis required (which would have failed for nested flow values).  Estimate was 1.5–2 cadence steps; actual ≈1 step because the foldl-based position formula obviated the induction.  Sorry count unchanged at 8 (build clean: 8/8 ScannerLinearise + 57/57 EmitterScannability jobs green; ~190 net lines of new proof code) | 0 (no sorry change; ~190 net lines proof code added; build clean) | `Proofs/Scanner/ScannerLinearise.lean` | ✓ done 2026-05-02 |

**J.3.1 — Linearise foundations** [✓ completed 2026-04-26]:

1. `linearise_resolved` (size accounting; pure structural induction
   over `linearise.go`).  Output cardinality equals
   `tokens.size + Σ (expandKind e).size`.
2. `linearise_append_unresolved` (no-op-ness of pushing an
   `.unresolved` pending entry).  Falls out of `expandKind` reducing
   to `#[]` on `.unresolved`.
3. `linearise_append_token` (Path C's headline append-monotonicity).
   Pushing a token to `tokens` extends `linearise`'s output rightward;
   the existing prefix is preserved.  Hypothesis: every pending
   entry's `insertBeforeIdx ≤ tokens.size`.

These are independently useful and consumed by every downstream
substep.  Gate satisfied: `lake build L4YAML` green; sorry count
24 → 21; the 3 `J.3 manifest 5.d` Linearise markers cleared.

**J.3.1 file layout** (per maintainer convention "all theorems
public, proofs separated from source"):

* `L4YAML/Scanner/Linearise.lean` — `expandKind`, `linearise.go`,
  `linearise` (function definitions only; no theorems).
* `L4YAML/Proofs/Scanner/ScannerLinearise.lean` (new file) — all
  proofs and helpers (`pendingExpandSumFrom`, the foldl bridges,
  `linearise_go_size`, `linearise_go_done`, `linearise_go_step_token`,
  `linearise_go_tail_pks_invariant`, and the three discharged
  theorems).  Namespace: `L4YAML.Proofs.ScannerLinearise`.  All
  declarations public — no `private` modifiers.

**J.3.2 — Bridge lemmas** [✓ completed 2026-04-26]: introduced
`scanFiltered_ok_implies_scan_ok`, `linearise_preserves_FlowContextPSV`,
`linearise_preserves_FlowBracketsMatched`.  Pure infrastructure; sorry
count unchanged at 21.

* **`scanFiltered_ok_implies_scan_ok`** in
  `Proofs/Scanner/ScannerCorrectness.lean` — `scanFiltered.ok →
  ∃ tokens, scan.ok`.  Routes through a new helper
  `scanLoopFull_ok_implies_scanLoop_ok`; the two loops share control
  flow and differ only in `scanLoopFull`'s extra trailing
  `skipToContent` (which preserves tokens/flowLevel and so doesn't
  affect success).
* **`linearise_preserves_FlowBracketsMatched`** in
  `Proofs/Production/ScannerPlainScalarValid.lean` — direct corollary
  of new `linearise_flowNesting_eq` (total flow nesting unchanged
  under linearise, since spliced `.key` / `.blockMappingStart` are
  flow-neutral).
* **`linearise_preserves_FlowContextPSV`** in same file — strong
  induction on `linearise.go` maintaining (i) `FCPSV(acc)`, (ii)
  `flowNesting acc acc.size = flowNesting tokens k`.  Splice branch
  uses `FlowContextPSV_of_prefix_and_new` (spliced tokens are
  flow-neutral non-scalars); push branch dispatches the new element's
  FCPSV obligation to `h_global` at index `k` via depth matching.
* **Helpers added** to `Proofs/Scanner/ScannerLinearise.lean`:
  `expandKind_val_neutral`, `linearise_go_size_mono`,
  `linearise_go_extends`, `linearise_go_eq_acc_append`,
  `linearise_go_getElem_lt_acc`.

**J.3.3 — ScannerCorrectness consumers** [partial 2026-04-26, 1/2]:

* **`saveSimpleKey_preserves_SimpleKeyValid`** [✓ discharged 2026-04-26]:
  obstructed because, post-cutover, `saveSimpleKey` records
  `simpleKey.tokenIndex := s.tokens.size` (limbo state) rather than
  pushing two placeholder slots — the legacy 4-conjunct
  `SimpleKeyValid` invariant is therefore false at the `saveSimpleKey`
  return.  Resolved per the manifest's first option: re-stated
  `SimpleKeyValid` and `SimpleKeyStackValid` as **bound-only**
  invariants (`simpleKey.possible = true → tokenIndex ≤ tokens.size`),
  dropping the position-equality conjuncts.  The position equalities
  were no longer load-bearing post-cutover — every consumer
  (`scanValuePrepare_preserves_ScanInv`, `scanValue_preserves_ScanInv`,
  `dispatchBlockIndicators_preserves_ScanInv`,
  `scanValue_preserves_all_pos`) had its `h_sk`/`h_skv` argument
  silenced under the J.2-cutover comment.  The `SimpleKeyValid_mono`,
  `SimpleKeyStackValid_mono(_pos)`, `flowStart_preserves_AllKeysValid`,
  `flowEnd_preserves_AllKeysValid` proofs simplify to one-line
  `omega` discharges.  `h_pref` / `h_skv` arguments retained on the
  signatures (renamed to `_h_*`) for J.4 cleanup.
* **`scanFiltered_produces_valid_tokens`** [pending — substantial
  infrastructure required]:
  Discharging this requires four classes of lemma:
  (a) `scanLoopFull_*` mirrors of `scanLoop_*` (envelope/ordering
  facts about `final.tokens`); (b) linearise preservation of each
  `ValidTokenStream` field; (c) well-indexedness invariants on
  `final.pendingKeys` (`1 ≤ insertBeforeIdx ≤ tokens.size`); (d)
  position-fit invariants for spliced tokens.  J.3.3 added (a) in full
  and started (b):
  - `scanLoopFull_increases_tokens`, `scanLoopFull_preserves_tokens`,
    `scanLoopFull_success_emits_streamEnd`, `scanLoopFull_ordered` —
    each mirrors the corresponding `scanLoop_*` lemma, with the
    completion-branch's extra `skipToContent` discharged via
    `skipToContent_preserves_tokens` / `skipToContent_preserves_ScanInv`.
  - `linearise_size_ge_tokens`, `linearise_first_eq_tokens_first`,
    `linearise_append_token_eq` (equation form of
    `linearise_append_token` for direct rewriting),
    `linearise_last_eq_tokens_last`
    (in `Proofs/Scanner/ScannerLinearise.lean`).
  Remaining work plan, organised around the algebraic structure of
  how scanner ops affect `pendingKeys`:

  **Three operation classes** (derived from `grep` for `pendingKeys :=`
  in `L4YAML/Scanner/`):

  * **Class A — passthrough**: `(op s).pendingKeys = s.pendingKeys`.
    Every operation outside of `saveSimpleKey` / `setPendingKeyKind` /
    `setPendingKeyEndLine`: `advance`, `emit`, `skipToContent`,
    `unwindIndents`, all the `scan*` content scanners, all dispatchers'
    non-key paths.  Mirrors the existing `_preserves_simpleKeyStack`
    chain (~280 instances).

  * **Class B — append-with-bounded-entry**: `saveSimpleKey` only.
    Either returns `s` unchanged (guard fails) or appends exactly one
    entry whose `insertBeforeIdx = s.tokens.size` and `pos = s.currentPos`.

  * **Class C — element field-update at active index**:
    `setPendingKeyKind` (modifies `kind` only), `setPendingKeyEndLine`
    (modifies `endLine` only).  Both preserve `pendingKeys.size`,
    `[i].insertBeforeIdx`, and `[i].pos` for every `i`.

  **Invariant**: `PendingKeysWellIndexed s := s.tokens.size ≥ 1 ∧
  ∀ p, 1 ≤ s.pendingKeys[p].insertBeforeIdx ≤ s.tokens.size`.  Plus
  `PendingKeysPosBounded s := ∀ p, s.pendingKeys[p].pos.offset ≤ s.offset`.

  **Generic mono lemma** (the workhorse):
  ```
  PendingKeysWellIndexed_mono :
    s'.pendingKeys = s.pendingKeys → s'.tokens.size ≥ s.tokens.size →
    PendingKeysWellIndexed s → PendingKeysWellIndexed s'
  ```
  Discharges every Class A op in one application, given the existing
  `_adds_tokens` / `_preserves_pendingKeys` lemmas.

  **Steps**:
  1. ✓ Define `PendingKeysWellIndexed` and prove generic mono lemma
     for Class A passthroughs.
  2. ✓ Class A passthrough micro-lemmas for `advance`, `emit`,
     `emitAt` (`*_preserves_pendingKeys`).
  3. ✓ Class B (`saveSimpleKey_preserves_PendingKeysWellIndexed`):
     direct case analysis on the three branches.
  4. ✓ Class C decomp + size + `insertBeforeIdx`-pointwise for
     `setPendingKeyKind` and `setPendingKeyEndLine`.  Direct unfold
     hits Lean's dependent-index limitation; the decomp lemmas
     factor out the existential cleanly so the pointwise fact reduces
     to `Array.getElem_setIfInBounds_*`.
  5. ✓ Add remaining Class A passthrough micro-lemmas for ops in the
     `scanNextToken` chain (~30 lemmas, mostly `rfl` or one-line
     proofs that mirror the existing `*_preserves_simpleKeyStack`
     shapes).  Note: only `scanValuePrepare` (uses `setPendingKeyKind`)
     and the double/single-quoted branches in
     `scanNextToken_dispatchContent` (use `setPendingKeyEndLine`)
     are non-Class A — everything else passes through.
  6. ✓ Compose dispatcher-level preservation lemmas
     (`preprocess_preserves_PendingKeysWellIndexed`,
     `dispatch{Structural,FlowIndicators,BlockIndicators,Content}_preserves_…`,
     `scanNextToken_preserves_…`) — mechanical mirror of the
     AllKeysValid chain (~60 LOC).
  7. ✓ `scanLoopFull_preserves_PendingKeysWellIndexed` by induction (~30 LOC).
  8. ✓ `linearise_positions_ordered` with pendingKey position-fit
     hypotheses (~120 LOC).
  9. Compose into `scanFiltered_produces_valid_tokens` (~50 LOC).

  Status (2026-04-28): Steps 1-9 ✓ done.  Step 8b closed: 25 per-op
  leaves landed (Class A passthroughs, single-emit emit-class,
  push-indent + emit chain, emitAt-class scalars/anchors/tags, indent
  / whitespace standalones, the Class C `scanValue` composition, both
  multi-emit document markers, and the three-branch `scanDirective`),
  plus the 4 dispatchers + `preprocess` + `scanNextToken` +
  `scanLoopFull` composition theorems.  Step 9 closed:
  `scanFiltered_produces_valid_tokens` discharged (no sorry); J.3.3
  is now sorry-free for its primary deliverable.
  Eight prior commits (~2434 LOC): `c6bfab0a` saveSimpleKey discharge,
  `1e6b4741` Class A/B/C foundation, `de7610d9` Blueprint update,
  `c4dc838a` ~30 Class A *_preserves_pendingKeys leaves, `fbd330d4`
  dispatcher composition + scanNextToken preservation, `cbba890e`
  scanLoopFull preservation, `a5aa58e8` LineariseFit invariant +
  mono/field/save core lemmas (~423 LOC), `ca29c9b2`
  linearise_positions_ordered (~261 LOC).

  Step 8a (`a5aa58e8`) defines `LineariseFit` bundling ScanInv +
  PendingKeysWellIndexed + (pks sorted by idx and pos) + I1 (tokens
  before insertBeforeIdx ≤ pos) + I2 (tokens at/after insertBeforeIdx ≥
  pos) + I4 (pos ≤ offset).  Discharges 4 workhorse mono lemmas
  (`LineariseFit_no_token_change`, `LineariseFit_emit_one`,
  `LineariseFit_field_update`, `saveSimpleKey_preserves_LineariseFit`).
  Uses Nat-indexed bounds throughout (`pendingKeys[p]'hp` style) +
  helper `array_get_eq_of_array_eq` to handle dependent-indexing
  cleanly across array equality rewrites.

  Step 8c (`ca29c9b2`) discharges `linearise_positions_ordered`: the
  output of `linearise tokens pks` has non-decreasing `pos.offset`s,
  given the LineariseFit hypotheses.  Proof by strong induction on
  `(tokens.size − k) + (pks.size − p)` with inductive invariant
  `goSortedInv` on the `(k, p, acc)` recursion state.  Helper
  `expandKind_offset_const` shows expandKind produces a constant-offset
  run.

  **Step 8b — per-op `*_preserves_LineariseFit` leaves (in progress)**

  *Mono lemma infrastructure (commits `807b91df`, `ef90bd62`,
  `b83e8252`, `6cbc43d6`):*
  - `LineariseFit_extend` — unified Class A mono (preserves pks, allows
    token append + offset mono).
  - `LineariseFit_via_no_change` — Class A passthrough wrapper.
  - `LineariseFit_via_first_new` — multi-emit; only the FIRST new
    token's offset bound needs proof, subsequent tokens inherit via
    ScanInv tokens-sorted at s'.
  - `LineariseFit_via_first_new_strict` — auto-derives off_mono for ops
    that always add ≥ 1 token (via ScanInv tokens_le_offset at s').
  - `LineariseFit_extend_field_update` — Class C generalisation of
    `LineariseFit_extend` (per-entry idx/pos preservation rather than
    full pks array equality), required for `scanValue`.
  - `first_new_pos_emitAt` — extracts pos for emitAt-class ops via
    index alignment under `subst`.
  - `offset_mono_via_first_new` — derives s.offset ≤ s'.offset from
    first_new bound + ScanInv at s'.

  *Per-op leaves landed (25 total, in dependency order):*
  - **Class A passthroughs** (`0ec064a7`): `advance`, `skipSpaces`,
    `skipWhitespace`, `skipToEndOfLine`, `consumeNewline`.
  - **Single-emit Class A** (`f35a04ac`, `4af1fc1a`, `ef90bd62`):
    `emit`, `scanFlowSequenceStart/End`, `scanFlowMappingStart/End`,
    `scanFlowEntry`.
  - **Push-indent + emit chain** (`bdd27512`): `scanBlockEntry`,
    `scanKey` via private helpers `pushSequenceIndent_emit_first_new_offset` /
    `pushMappingIndent_emit_first_new_offset`.
  - **emitAt-class scalar/anchor/tag** (`d41f13b4`, `aaa5cc1e`):
    `scanAnchorOrAlias`, `scanTag` (verbatim/secondary/named),
    `scanDoubleQuoted`, `scanSingleQuoted`, `scanPlainScalar`,
    `scanBlockScalar`.  The original "fuel-parameter mismatch"
    diagnosis was incorrect: it was a tactical issue (rw vs simp_only
    through `{state with simpleKeyAllowed := false}` defeq), not
    architectural — `rw [first_new_pos_emitAt …]` correctly unifies
    through the record-update wrapper.
  - **Indent / whitespace standalones** (`4c664b58`, `067a6e35`):
    `pushSequenceIndent`, `pushMappingIndent`, `skipToContent`,
    `unwindIndents`.
  - **Class C composition** (`1a8c8f0f`): `scanValue` —
    field-updates `pendingKeys` via `setPendingKeyKind` AND emits ≥ 1
    token (always trailing `.value`, optionally preceded by
    `.blockMappingStart` from prepare's pushMappingIndent branch).
  - **Multi-emit composition** (`811622ca`, `81391a63`):
    `scanDocumentStart` — `unwindIndents s (-1)` (variable `.blockEnd`
    count) → field-update of `simpleKey` / `pendingKeyActive` →
    `.emit .documentStart` → `.advanceN 3` → outer record update.
    `scanDocumentEnd` — same shape inside an `Except` chain (one
    early `directiveWithoutDocument` exit and a trailing
    `skipDocEndWhitespace` + content-validation tail that doesn't
    affect the returned state).
  - **Three-branch directive** (`743a9e6a`): `scanDirective` —
    YAML / TAG / reserved.  Reserved adds no token, so uses non-strict
    `LineariseFit_via_first_new` (rather than `_strict`) with explicit
    `scanDirective_offset_ge`.  YAML/TAG branches each emit a single
    `emitAt startPos` token at `s.currentPos`.

  *Class C building blocks landed (commit `6cbc43d6`):*
  - `setPendingKeyKind_pos`, `setPendingKeyEndLine_pos` — siblings to
    the existing `*_insertBeforeIdx` lemmas (per-entry pos preserved
    under field-update via `setIfInBounds`).
  - `scanValuePrepare_pendingKeys_pos`, `scanValue_pendingKeys_pos` —
    chain through `scanValueClearKey → scanValuePrepare → emit →
    advance` to give the LineariseFit_extend_field_update prerequisites.
  - `LineariseFit_extend_field_update` mono lemma (above).

  *unwindIndents currentPos preservation landed (commit `9d1146a1`):*
  - `unwindIndents_{line,col,currentPos}_eq` — sibling to the existing
    `unwindIndents_offset_eq`.  Together they establish unwindIndents
    preserves (offset, line, col), needed so emits AFTER unwindIndents
    in scanDocumentStart/End/Directive happen at `s.currentPos`.

  *`scanValue_preserves_LineariseFit` landed (commit `1a8c8f0f`):*
  - `LineariseFit_via_first_new_field_update` — combines Class C
    field-update prerequisites with the first-new-token shortcut.
  - `pushMappingIndent_{line,col,currentPos}_eq`, `svck_{line,col,currentPos}`,
    `svp_{line,col,currentPos}` — line/col chains so emitted tokens
    reduce to `s.currentPos`.
  - `pushMappingIndent_first_new_pos`, `scanValuePrepare_tokens_or`,
    `scanValuePrepare_first_new_pos` — branch-by-branch first-new-token
    derivation.
  - `scanValue_first_new_pos_offset`, `scanValue_preserves_prefix_strict`
    — bridge through `{emit .value → advance → record-update}` using
    `array_get_eq_of_array_eq` to dodge `rw` motive issues under
    dependent indexing.

  *`scanDocumentStart_preserves_LineariseFit` landed (commit `811622ca`):*
  - `scanDocumentStart_first_new_pos` — case-splits on whether
    `unwindIndents s (-1)` fires.  Bridges via `array_get_eq_of_array_eq`
    against the equality `(scanDocumentStart s).tokens =
    (s_kd.emit .documentStart).tokens` (advanceN-preserves-tokens +
    outer record update).  Branch 1: unwindIndents didn't fire — the
    push lands at index s.tokens.size, pos = s_kd.currentPos which
    collapses to s.currentPos via `unwindIndents_currentPos_eq`.
    Branch 2: unwindIndents fired — index s.tokens.size lies below the
    push and inside the unwound prefix, pos given by
    `unwindIndents_first_new_pos`.
  - Composes via `LineariseFit_via_first_new_strict` threading the
    pre-existing `scanDocumentStart_preserves_{ScanInv,pendingKeys}`
    and `ScanHelpers.scanDocumentStart_{adds_tokens,preserves_prefix}`.

  *`scanDocumentEnd_preserves_LineariseFit` landed (commit `81391a63`):*
  - `scanDocumentEnd_first_new_pos` — parallel to the scanDocumentStart
    helper.  All success branches of the Except chain (validation
    `none` / `'#'` / newline) collapse to the same `result`, so the
    canonical equality `s'.tokens = (s_kd.emit .documentEnd).tokens`
    is extracted via `repeat (any_goals (split at h)) … all_goals
    subst` followed by `dsimp only []; rw [advanceN_preserves_tokens]`.
    Same case-split (`unwindIndents` fired vs not) closes the proof.
    The trailing `skipDocEndWhitespace` and content-validation match
    don't affect the returned state, so no separate
    `skipDocEndWhitespace_preserves_LineariseFit` micro-leaf was
    needed.
  - Composes via `LineariseFit_via_first_new_strict` threading the
    pre-existing `scanDocumentEnd_preserves_{ScanInv,pendingKeys}` and
    `ScanHelpers.scanDocumentEnd_{adds_tokens,preserves_prefix}`.

  *`scanDirective_preserves_LineariseFit` landed (commit `743a9e6a`):*
  - `scanYamlDirective_first_new_pos`, `scanTagDirective_first_new_pos`
    — pin the (single) emitted token to `startPos = s.currentPos`
    after unfolding the inner Except chain via
    `repeat (any_goals (split at h)) … all_goals subst` followed by
    `refine first_new_pos_emitAt _ startPos _ s.tokens.size ?_ h_lt`
    and a `rw` chain through the `_preserves_tokens` helpers
    (skipWhitespace + collectVersion{Major,Minor}Loop or
    skipWhitespace + collectTag{Handle,Prefix}Loop).
  - `scanDirective_offset_ge` — chain through advance +
    collectDirectiveNameLoop + skipWhitespace + sub-scanner +
    skipToEndOfLine, used to discharge `h_off_mono` for the
    non-strict `LineariseFit_via_first_new` (since the reserved
    branch adds no tokens, `_strict`'s auto-derivation can't fire).
  - `scanDirective_first_new_pos` — composes the two sub-scanner
    helpers via `array_get_eq_of_array_eq` to bridge the
    `skipToEndOfLine s_inner` wrap; reserved branch derives a
    contradiction from `h_lt` (no token added).
  - `scanYamlDirective_offset_ge'` and `scanTagDirective_offset_ge'`
    relocated from §5.3 to just before the LineariseFit subsection
    so `scanDirective_offset_ge` can reach them without forward
    reference.

  *Dispatcher composition + `scanLoopFull` landed (commits
  `c1fce4cd`, `2c43b328`):*
  - `setPendingKeyEndLine_wrap_preserves_LineariseFit` — Class C
    helper for the double/single-quoted `endLine` field-update.
    Authored with `refine LineariseFit_field_update s _ ?_ ?_ ?_ ?_
    rfl rfl h` rather than `apply` — `apply` left `?s'` as a
    metavariable that simp on `setPendingKeyEndLine_size` couldn't
    constrain (the simp lemma's LHS pattern `(setPendingKeyEndLine
    _ _ _).size` doesn't match `?s'.pendingKeys.size`), so the
    metavariable defaulted to `?s' = s` and the subsequent `hp'`
    parameters got the wrong bound type.  The `refine` form forces
    `s'` to be unified from the goal first, fixing all downstream
    types.
  - `definedAnchors_push_preserves_LineariseFit` — Class A
    field-update helper for the trailing `definedAnchors.push name`
    in the `&` branch of `dispatchContent`.
  - `dispatchStructural_preserves_LineariseFit`,
    `dispatchFlowIndicators_preserves_LineariseFit` — automated by
    the `repeat (any_goals (split at h)); all_goals subst_vars;
    all_goals first | … | …` pattern over the per-op
    `*_preserves_LineariseFit` leaves.
  - `dispatchBlockIndicators_preserves_LineariseFit` — explicit
    three-way case-split on `-` / `?` / `:`; threads the
    `(scanValueClearKey s).simpleKey.{possible,tokenIndex}` `h_sk`
    precondition required by `scanValue_preserves_LineariseFit`.
  - `dispatchContent_preserves_LineariseFit` — six-way case-split;
    the double/single-quoted branches go through the
    `setPendingKeyEndLine_wrap` helper.
  - `preprocess_preserves_LineariseFit` — composes
    `skipToContent` (A) + `unwindIndents` (A) + needIndentCheck
    field-update (A) + `saveSimpleKey` (B).
  - `allowDir_ite_preserves_LineariseFit` — the directive-allowance
    toggle (Class A field-update).
  - `scanNextToken_preserves_LineariseFit` — final dispatcher
    composition; shape mirrors
    `scanNextToken_preserves_PendingKeysWellIndexed`.
  - `scanLoopFull_preserves_LineariseFit` — fuel induction.
    Recursive arm threads `AllKeysValid` for the `SimpleKeyValid`
    precondition of `scanNextToken_preserves_LineariseFit`.
    Completion arm: `skipToContent` + `unwindIndents` + emit
    `.streamEnd` (all Class A).

  **Step 9 — `scanFiltered_produces_valid_tokens` landed**

  Discharged the surviving sorry (previously at line 12932) by
  composing the Step-8 `scanLoopFull_preserves_LineariseFit` chain
  with the four `linearise_*` shape lemmas:
  - **`scanFiltered_produces_at_least_two`** — composes
    `scanLoopFull_increases_tokens` (final.size ≥ post_bom.size + 1)
    with `linearise_size_ge_tokens` (linearise.size ≥ tokens.size).
    Proof uses `split at h_full` on the BOM `match` to expose
    `post_bom.tokens.size = 1` per branch, sidestepping a Lean
    alpha-rename quirk where the helper-form `| _ =>` and the
    unfolded form `| x =>` are not unified by `rw`/`simp`/`omega`.
  - **`scanFiltered_first_is_streamStart`** — uses
    `linearise_first_eq_tokens_first` (needs `1 ≤ insertBeforeIdx`
    from `LineariseFit final`'s `PendingKeysWellIndexed` lower bound)
    + `scanLoopFull_preserves_tokens` (n=1) to carry the post-BOM
    streamStart token through to `final.tokens[0]`.
  - **`scanFiltered_last_is_streamEnd`** — needs the *strict* bound
    `insertBeforeIdx < final.tokens.size` (added as
    `scanLoopFull_pendingKeys_lt_tokens_size`, ~50 LOC).  The
    looser `≤ tokens.size` from `PendingKeysWellIndexed` is
    insufficient because `linearise_last_eq_tokens_last` requires
    `≤ tokens.size − 1`.  Strictness is "free" in `scanLoopFull`:
    the completion arm always emits `.streamEnd` last, and `emit`
    adds a token without changing `pendingKeys`, so the post-emit
    `tokens.size` strictly exceeds every saved index.
  - **`scanFiltered_positions_ordered`** — extracts the four
    LineariseFit conjuncts (tokens-sorted via ScanInv,
    pks-pos-sorted, I1, I2) and feeds them into
    `linearise_positions_ordered`.  Uses `subst h_eq` to substitute
    `ftokens` with `linearise final.tokens final.pendingKeys`, so
    Fin indices refer to the linearise array directly (avoids
    dependent-rewrite motive issues).

  Five private setup helpers establish `LineariseFit` and
  `AllKeysValid` at the post-BOM state of `scanFiltered`'s prefix:
  `scanFiltered_post_bom_pendingKeys_empty` (rfl-level: mk' has
  empty pks, emit/advance preserve), `scanFiltered_post_bom_tokens_size_eq_one`,
  `scanFiltered_post_bom_tokens_eq` (post-BOM tokens = post-streamStart
  tokens), `scanFiltered_post_bom_ScanInv` /
  `scanFiltered_post_bom_AllKeysValid` (inlined from
  `scan_positions_ordered`'s setup), and
  `scanFiltered_post_bom_LineariseFit` (composes the above via
  `LineariseFit_of_empty_pendingKeys`).

  Required `import L4YAML.Proofs.Scanner.ScannerLinearise` +
  `open L4YAML.Proofs.ScannerLinearise` at the top of
  `ScannerCorrectness.lean` to surface the four `linearise_*` lemmas.

  Build status (2026-04-28 evening): full project (453/453) green;
  0 sorry, 0 warnings in `ScannerCorrectness.lean`.

  *Cumulative session log (2026-04-27 → 2026-04-28):* 21 commits
  including `807b91df`, `0ec064a7`, `f35a04ac`, `4af1fc1a`, `ef90bd62`,
  `bdd27512`, `b83e8252`, `7046048b`, `8133ab94`, `d41f13b4`,
  `aaa5cc1e`, `4c664b58`, `067a6e35`, `6cbc43d6`, `9d1146a1`,
  `1a8c8f0f`, `811622ca`, `81391a63`, `743a9e6a`, `c1fce4cd`,
  `2c43b328`, plus the Step 9 commit (`scanFiltered_produces_valid_tokens`
  + four field theorems + strict-bound lemma + post-BOM helpers
  + `LineariseFit_of_empty_pendingKeys` + import/open additions).
  Build green throughout; sorry count for this file: **1 → 0**.

  **J.3.4 landed (2026-04-28 evening) — `ScannerPlainScalarValid`
  consumers cleared**

  The four `J.3 manifest 5.d` Category C sorries in
  `Proofs/Production/ScannerPlainScalarValid.lean` (`scan_plain_scalar_valid`,
  `saveSimpleKey_preserves_AllKeysPlaceholderInv`,
  `scan_flow_context_psv`, `scan_flow_brackets_matched`) all dropped.
  Sorry count for this file: **4 → 0**; full project sorry count:
  **19 → 15**.

  *AKPI dead-code removal (closes the 4364 sorry).*  Post-cutover
  `saveSimpleKey` reserves `tokenIndex = tokens.size` without pushing
  the legacy two-placeholder slot pair, so `SimpleKeyPlaceholderInv`
  (which requires `tokenIndex < tokens.size` and `tokens[tokenIndex] = .placeholder`)
  is structurally false at the save site.  Tracing the consumer
  chain showed the family was *already* dead weight: the only live
  use-site, `dispatchBlockIndicators_preserves_FlowInv`, threaded
  `h_phi` solely to feed `scanValuePrepare_preserves_FlowContextPSV/FlowNestingInv`,
  whose post-cutover bodies ignored the placeholder hypothesis (`let _ := h_ph`
  with no further use).  J.3.4 dropped the parameter from each
  link in the chain (`scanValuePrepare_preserves_*` →
  `scanValue_preserves_*` → `dispatchBlockIndicators_preserves_FlowInv`
  → `scanNextToken_preserves_FlowInv` → `scanLoop_preserves_FlowInv`,
  `scanLoop_FlowBracketsMatched`, and the corresponding initialiser
  block in `scan_FlowBracketsMatched`), then removed the orphan
  `*_preserves_AllKeysPlaceholderInv` family wholesale (8 lemmas
  including the sorry'd `saveSimpleKey_preserves_AllKeysPlaceholderInv`,
  ~503 lines).  The `AllKeysPlaceholderInv` definition and its
  `_mono`/`_of_*` helpers stay (orphan, no sorry exposure) for a J.4
  cleanup pass.

  *Three consumer sorries dispatched via paired `scanLoopFull` +
  `linearise` bridges.*

  - **`linearise_preserves_PlainScalarsValid`** (J.3.4 bridge,
    mirror of `linearise_preserves_FlowContextPSV` from J.3.2 but
    simpler — PSV is unconditional, no flow-tracking invariant).
    Strong induction on the lex measure `(tokens.size - k) + (pks.size - p)`;
    splice branch uses `expandKind_not_plain_scalar` (`.key` /
    `.blockMappingStart` are non-plain), push branch reads the new
    element from the input via `h_global k hk`.  Closed via
    `linearise_go_preserves_PlainScalarsValid` then `acc = #[]`,
    `k = 0`, `p = 0`.
  - **`scanLoopFull_preserves_PlainScalarsValid`**,
    **`scanLoopFull_preserves_FlowContextPSV`**, and
    **`scanLoopFull_FlowBracketsMatched`** — `scanLoop_*` mirrors
    diverging only in the completion branch's extra `skipToContent`
    (which preserves `tokens` per `skipToContent_preserves_tokens`
    and `flowLevel` per `skipToContent_preserves_flowLevel`, hence
    preserves all three invariants).
  - **Three post-BOM helpers** (`scanFiltered_post_bom_PlainScalarsValid`,
    `scanFiltered_post_bom_FlowContextPSV`,
    `scanFiltered_post_bom_FlowNestingInv`) establish each invariant
    at the post-BOM state where `tokens.size = 1` (just `.streamStart`)
    via `array_get_eq_of_array_eq` to fold the BOM `match` to the
    pre-BOM token.
  - **`scan_plain_scalar_valid`** / **`scan_flow_context_psv`** /
    **`scan_flow_brackets_matched`** — each composes the post-BOM
    helper, the `scanLoopFull_*` mirror, and the `linearise_*`
    bridge.  Pattern: `unfold scanFiltered; simp; split` on the
    `scanLoopFull` result, `injection h with h_eq; subst h_eq` to
    substitute `linearise final.tokens final.pendingKeys` for the
    output `tokens`, then chain the three preservation lemmas.

  *File restructure.*  Moved `expandKind_not_plain_scalar` (10 LOC)
  and the J.3.4 PSV bridge block (`linearise_go_preserves_PlainScalarsValid`
  + `linearise_preserves_PlainScalarsValid`, ~91 LOC) above
  `scan_plain_scalar_valid` so the discharge has access to the bridge
  in scope (the FCPSV/FBM bridges, defined for J.3.2, were already
  positioned correctly relative to their consumers).

  Build status (2026-04-28 evening, J.3.4 commit pending): full
  project (453/453) green; **15 sorries remaining** (1 DocumentProduction
  + 1 EndToEndCorrectness for J.3.5; 6 Cat C + 7 Tier 2 in
  EmitterScannability for J.3.6 / J.4).

  **J.3.5 landed (2026-04-28 late evening) — `DocumentProduction` /
  `EndToEndCorrectness` consumers cleared**

  The two `J.3 manifest 5.d` Category C sorries in
  `Proofs/Production/DocumentProduction.lean:245` (`parse_strict_proof`)
  and `Proofs/EndToEndCorrectness.lean:313`
  (`parseYaml_implies_valid_token_stream`) both dropped.  Sorry count
  for these files: **2 → 0**; full project sorry count: **15 → 13**
  (all remaining sorries now confined to
  `Proofs/Output/EmitterScannability.lean`).

  *Direct routing through the J.3.2 bridge.*  Both consumers extract
  `scanFiltered.ok` from `parseYaml.ok` by the same standard
  unfolding pattern (`unfold parseYaml; split; rename_i raw_docs h_raw;
  unfold parseYamlRaw at h_raw; split; rename_i ftokens h_scanf`),
  then route through `scanFiltered_ok_implies_scan_ok` (J.3.2
  bridge, `Proofs/Scanner/ScannerCorrectness.lean:12905`) to recover
  `∃ tokens, scan input = .ok tokens`.  From there:

  - **`parse_strict_proof`** applies `scan_strict_proof input tokens
    h_scan` (the existing scan-strictness theorem in the same file)
    to get `InYamlLanguage input`.
  - **`parseYaml_implies_valid_token_stream`** packages `tokens`
    with `h_scan` and `scan_valid_token_stream input tokens h_scan`
    (`Proofs/Scanner/ScannerCorrectness.lean:12943`) into the
    triple `⟨tokens, scan.ok, ValidTokenStreamProp⟩`.

  No new lemmas needed — both proofs are pure plumbing through
  pre-existing bridges.  `ScannerCorrectness` was already
  transitively imported into `DocumentProduction.lean` via
  `ScalarProduction → StructureProduction → NodeProduction` (no
  import-graph changes); `EndToEndCorrectness.lean` already imports
  it directly and opens its namespace.

  Build status (2026-04-28 late evening): full project (453/453)
  green; **13 sorries remaining**, all in
  `Proofs/Output/EmitterScannability.lean` (6 Cat C for J.3.6/J.3.7,
  7 Tier 2 for J.4).

  **J.3.6 landed (2026-04-29) — `EmitterScannability` chain-bridge
  subset**

  Three of the six `J.3 manifest 5.d` Category C sorries in
  `Proofs/Output/EmitterScannability.lean` discharged:

  - **`scanFiltered_boundary_tokens`**: routes directly through the
    J.3.2 field theorems (`scanFiltered_produces_at_least_two`,
    `scanFiltered_first_is_streamStart`,
    `scanFiltered_last_is_streamEnd`) — pure repackaging into the
    plain-conjunction shape downstream consumers want.
  - **`scanFiltered_of_chain`**: existential bridge from a `ScanChain`
    + EOF + flow/directives invariants to `∃ tokens, scanFiltered
    input = .ok tokens`.  Now composes the existing
    `scanLoop_eof_eq` + `ScanChain.to_scanLoop` machinery with the
    new J.3.6 reverse bridge.
  - **`scan_accepts_emitScalar`**: the scalar leaf of
    `emit_produces_valid_yaml`.  Builds the one-step chain from
    `scanNextToken_emitScalar_init`, closes the loop via
    `scanNextToken_eof`, and applies `scanFiltered_of_chain`.

  Sorry count drop: **13 → 10**.

  *New infrastructure added in `Proofs/Scanner/ScannerCorrectness.lean`*:

  - **`scanLoop_ok_implies_scanLoopFull_ok`** — symmetric mirror of
    the J.3.2 `scanLoopFull_ok_implies_scanLoop_ok`.  `scanLoop` and
    `scanLoopFull` step in lock-step on `scanNextToken`; the only
    difference is the `.ok none` arm where `scanLoopFull` runs an
    extra `skipToContent` whose inline match falls back to the input
    state on error.  That fallback never produces a new error, so
    any input that lets `scanLoop` close into `.ok _` also lets
    `scanLoopFull` close into `.ok _`.
  - **`scan_ok_implies_scanFiltered_ok`** — lifts the loop bridge
    across the shared BOM-handling prefix.  Used here by
    `scanFiltered_of_chain` to convert a `scan` success
    constructed from a `ScanChain` into a `scanFiltered` success.

  These two reverse bridges are the natural twins of the J.3.2
  forward bridges and unblock any remaining emitter-side proof that
  builds a `scanLoop`-flavoured witness but needs to conclude at the
  `scanFiltered` layer.

  Build status (2026-04-29): full project (453/453) green; **10
  sorries remaining**, all in `Proofs/Output/EmitterScannability.lean`
  (3 Cat C for J.3.7/J.3.8, 7 Tier 2 for J.4).

  **J.3.7 landed (2026-04-29) — `EmitterScannability` `emitScalar`
  filter-shape pair**

  Two of the three remaining `J.3 manifest 5.d` Category C sorries
  discharged through a `linearise = tokens` bridge for emitter-output
  pendingKeys (no resolved entries) plus a stronger one-step chain
  characterization:

  - **`scanFiltered_emitScalar_vals`**: concrete shape `tokens.size =
    3 ∧ tokens[0]!.val = .streamStart ∧ tokens[1]!.val = .scalar
    content .doubleQuoted ∧ tokens[2]!.val = .streamEnd`.  Walks
    `scanFiltered (emitScalar content)` directly: BOM identity
    (`peek? = some '"' ≠ BOM`) → one-step `ScanChain` from
    strengthened `scanNextToken_emitScalar_init` → `scanLoopFull`
    closes via new `scanLoopFull_eof_eq` + `ScanChain.to_scanLoopFull`
    + `unwindIndents` identity at `indents.size ≤ 1` →
    `linearise_all_unresolved` collapses `linearise` to `tokens` (all
    pendingKeys carry `.unresolved`).  Final shape is
    `s₁.tokens.push streamEnd-pos`, with `s₁.tokens.toList = [a, b]`
    where `a.val = .streamStart` and `b.val = .scalar content
    .doubleQuoted` (extracted from the strengthened init's
    `tokens.map (·.val)` clause).
  - **`scanFiltered_emitScalar_content`**: a one-line corollary that
    selects index 1 from `_vals`'s shape.

  Sorry count drop: **13 → 11**.

  *New infrastructure added in `Proofs/Scanner/ScannerLinearise.lean`*:

  - **`linearise_all_unresolved`** — generalises
    `linearise_append_unresolved` to arbitrary unresolved pending
    arrays: `(∀ e ∈ pendingKeys, e.kind = .unresolved) → linearise
    tokens pendingKeys = tokens`.  Proven via a strong
    `toList`-shape helper (`linearise.go` walks `tokens` copying onto
    `acc`, so the result is `acc.toList ++ tokens.toList.drop k`)
    using `List.drop_eq_getElem_cons` for the per-step token splice.
    Reusable for any emitter-shape proof that needs to bypass
    `linearise`'s splice machinery.

  *New infrastructure added in `Proofs/Output/EmitterScannability.lean`*:

  - **`skipToContent_eq_self_of_peek_none`** — factors the inline
    EOF identity from `scanNextToken_eof` into a reusable lemma.
  - **`scanLoopFull_eof_eq`** — equality form of `scanLoopFull` at
    EOF (mirrors `scanLoop_eof_eq`).  `scanLoopFull s fuel = .ok
    ((unwindIndents s_skipped (-1)).emit .streamEnd)` given
    `scanNextToken s = .ok none`, `flowLevel = 0`, `directivesPresent
    = false`, and an explicit `skipToContent s = .ok s_skipped`.
  - **`ScanChain.to_scanLoopFull`** — composition for `scanLoopFull`
    (mirrors `ScanChain.to_scanLoop`).  Fuel adds the chain length to
    propagate the closure to the chain's start state.
  - **Strengthened `scanNextToken_emitScalar_init`**: existential
    augmented with two J.3.7 clauses — `s₁.tokens.map (·.val) =
    #[.streamStart, .scalar content .doubleQuoted]` (concrete
    unfiltered shape — post-cutover the scanner pushes no
    `.placeholder`, so the filter-and-map shape coincides with the
    plain map shape) and `(∀ e ∈ s₁.pendingKeys, e.kind =
    .unresolved)` (one `saveSimpleKey` reservation, never resolved
    because the input has no following `:`).  Pendingkey-kind
    preservation through `scanDoubleQuoted` re-uses the existing
    `scanDoubleQuoted_preserves_pendingKeys` from
    `Proofs/Scanner/ScannerCorrectness.lean` (line 10343); the
    `setPendingKeyEndLine` post-step preserves `.kind` (only updates
    `.endLine`), tracked inline.

  Build status (2026-04-29): full project (453/453) green; **11
  sorries remaining** prior to J.3.8, all in
  `Proofs/Output/EmitterScannability.lean`.

  **J.3.8 landed (2026-04-29) — `EmitterScannability`
  `scanFiltered_of_chain_eq` re-stated in linearise terms**

  - **`scanFiltered_of_chain_eq`** is now stated in post-cutover
    form: RHS is `Scanner.linearise (...).tokens (...).pendingKeys`
    instead of the legacy `tokens.filter (· != .placeholder)`.  An
    extra `s_skipped` parameter + `h_skip : skipToContent s_final
    = .ok s_skipped` hypothesis surface the inline `skipToContent`
    fallback in `scanLoopFull`'s EOF arm.  Proof composes the J.3.7
    helpers `scanLoopFull_eof_eq` and `ScanChain.to_scanLoopFull`,
    then walks the `scanFiltered` definition (BOM identity +
    `scanLoopFull` reduction + `linearise` post-step) using the
    same `show ... = Except.ok ...` reshape pattern from
    `scanFiltered_emitScalar_vals`.

  - **`scanFiltered_tokens_eq_of_chain_short_stack`** updated
    in lockstep: takes `h_peek_eof : s_final.peek? = none`,
    discharges `h_skip` via
    `skipToContent_eq_self_of_peek_none`, returns the linearise
    RHS.  No sorry change at this layer.

  - **Seq/map consumer cascade** (`scanFiltered_emitSeq_nonempty_structure`,
    `scanFiltered_emitMap_nonempty_structure`): the post-cutover
    bridge yields `linearise` shape, but the existing Tier 1
    derivations (e.g. `tokens[k]!.val = .key`,
    `tokens[k]!.val = .scalar c s`) consume the legacy
    `(s₃.emit .streamEnd).tokens.filter p` shape via
    `(s₂.tokens.filter p)`-shaped body characterizations.
    Bridging `linearise` → legacy filter shape requires
    `linearise_all_unresolved` (only valid when no `pendingKeys`
    are resolved) plus a no-`.placeholder` invariant on `tokens`.
    The unresolved hypothesis fails for items containing flow
    maps (`{k: v}`-style with `:`-resolution).  Rather than push
    additional hypotheses or introduce a partially-true bridge,
    the `h_tok_eq` step in each of the two consumers is now
    `sorry`'d with a J.4-cascade marker — exposing what was
    previously masked behind the `scanFiltered_of_chain_eq` sorry.
    The consumer Tier 1 derivations (≥ 200 lines each) need
    re-stating in `linearise` terms; J.4 will rewrite them around
    `linearise.go` step-induction + `expandKind` cases for
    `.keyOnly` and `.unresolved`.

  Sorry-count accounting: line 2168 sorry cleared (-1); two
  cascade sorries exposed in seq/map consumers (+2); net **11
  → 12** raw sorry count.  Declarations using `sorry` go from 8
  to 7, since both consumers already used `sorry` for `h_pnok`
  (`ParseNodeFlowSeqOk` / `ParseEntryFlowMapOk`); the new bridge
  sorries fall under the same declarations.

  Build status (2026-04-29): full project (453/453) green; **12
  sorries remaining**, all in `Proofs/Output/EmitterScannability.lean`
  (2 Cat C cascade for J.4, 10 Tier 2/cleanup for J.4).

**J.3.5 landed**: `DocumentProduction` / `EndToEndCorrectness`
consumers re-discharged via direct `scanFiltered_ok_implies_scan_ok`
plumbing.

**J.3.6 landed**: `EmitterScannability` chain-bridge subset (3
sorries) discharged via new `scan_ok_implies_scanFiltered_ok` and
`scanLoop_ok_implies_scanLoopFull_ok` reverse bridges.

**J.3.7 landed**: `EmitterScannability` `emitScalar` filter-shape
pair (2 sorries) discharged via new `linearise_all_unresolved`
(`Proofs/Scanner/ScannerLinearise.lean`) + new `scanLoopFull_eof_eq`,
`ScanChain.to_scanLoopFull`, `skipToContent_eq_self_of_peek_none`
helpers + strengthened `scanNextToken_emitScalar_init`.

**J.3.8 landed**: `scanFiltered_of_chain_eq` re-stated in
linearise terms (post-cutover RHS); the `_short_stack` companion
follows.  Seq/map consumer Tier 1 derivations remain on legacy
filter shape, with the bridge step `sorry`'d for J.4 cascade
rewrite.  Net sorry count 11 → 12 (one bridge cleared, two
cascade sorries exposed); declarations using `sorry` 8 → 7.

**J.4.1 landed (2026-04-29)**: `linearise_eq_filter_no_resolutions`
in `Proofs/Scanner/ScannerLinearise.lean`.  Statement:

```
linearise tokens pks = tokens.filter (fun t => t.val != .placeholder)
```

under the conjunction `(∀ e ∈ pks, e.kind = .unresolved)` ∧
`(∀ t ∈ tokens, t.val ≠ .placeholder)`.  Proof composes the existing
`linearise_all_unresolved` (linearise = tokens when all unresolved)
with `Array.filter_eq_self.mpr` (filter = tokens when predicate
holds universally).  Sorry count unchanged (12); this is pure
infrastructure for J.4.2/J.4.3.

**Empirical verification (2026-04-29)**: a `tryscan`-style probe
on `[{k: v}]` confirms `scanFiltered` produces
`#[streamStart, flowSeqStart, flowMapStart, .key, scalar k, value,
scalar v, flowMapEnd, flowSeqEnd, streamEnd]` — size 10 with
`flowSeqEnd` at position 8 = size − 2.  The `_structure` theorem
positional claims (`tokens[size-2]!.val = .flowSequenceEnd`,
`tokens[1]!.val = .flowSequenceStart`, `tokens[2]` content-start
disjunction) are therefore **true post-cutover** for inputs with
flow maps inside; only the *proof technique* (`tokens.filter p`
shape) is broken, not the conclusions.  This rules out approach
(c) "restrict structure theorem signature" — keep the conclusions,
swap the proof.

**J.4.2.c-prep landed (2026-04-29)**: `linearise_push_eq_push_linearise`
in `Proofs/Scanner/ScannerLinearise.lean`.  Statement:

```
linearise (tokens.push t) pks = (linearise tokens pks).push t
  given (∀ e ∈ pks, e.insertBeforeIdx ≤ tokens.size)
```

Proof is one-line: `rw [linearise_append_token_eq] ; exact Array.push_eq_append.symm`.
Sorry count unchanged (12); pure infrastructure for J.4.2.b consumer
refactor.  The lemma's hypothesis matches the upper half of
`PendingKeysWellIndexed`, which is already propagated through
`scanLoopFull` by `scanLoopFull_preserves_PendingKeysWellIndexed`
(in `Proofs/Scanner/ScannerCorrectness.lean` line ≈10936).

**Strategic re-evaluation of J.4.2.a (2026-04-29)**: After surveying
existing scanner infrastructure, the no-placeholder global invariant
(originally posed as a J.4.2 prerequisite) is **not actually required**
for the cascade discharge.  The bridge helper `linearise_eq_filter_no_resolutions`
(J.4.1) does need it, but the helper itself is unusable for general
inputs (the `all-unresolved` clause fails on any input with a `:`-resolution).
The remaining viable path — refactor consumers to use direct linearise
positional reasoning — depends on `linearise_append_token_eq` +
`PendingKeysWellIndexed` (both already in tree) plus
`linearise_push_eq_push_linearise` (J.4.2.c-prep, just landed).

J.4.2.a is therefore reclassified as **optional follow-up infrastructure**
(useful for future consumers that want to manipulate `tokens.filter p`
shapes directly), not a blocker for J.4.2.b cascade discharge.

**J.4.2.c-pos1 landed (2026-04-29)**: `linearise_second_eq_tokens_second`
in `Proofs/Scanner/ScannerLinearise.lean`.  Statement:

```
∃ h_lin : 1 < (linearise tokens pks).size,
  (linearise tokens pks)[1]'h_lin = tokens[1]'h_size
  given tokens.size ≥ 2 and ∀ p (h : p < pks.size), 2 ≤ pks[p].insertBeforeIdx
```

Proof mirrors `linearise_first_eq_tokens_first`: step `linearise.go`
twice from `(0, 0, #[])` to `(2, 0, #[tokens[0], tokens[1]])` (the
`insertBeforeIdx ≥ 2` hypothesis ensures no splice fires at indices 0
or 1), then prefix-stability via `linearise_go_getElem_lt_acc` carries
`tokens[1]` at index 1 through the rest of the recursion.  The bound
`2 ≤ pks[p].insertBeforeIdx` always holds at `scanFiltered` because
the earliest `saveSimpleKey` registers a pending key only after
`[streamStart, flowSequenceStart]` (or block analogue) have been
emitted, i.e. when `s.tokens.size = 2`.

Sorry count unchanged (12); pure infrastructure for J.4.2.b consumer
refactor.  Build green (453 jobs), proof compiled clean on first
attempt (~75 lines including docstring).

**J.4.2.b-pkwi landed (2026-04-30)**: chain-side `PendingKeysWellIndexed`
helpers in `Proofs/Output/EmitterScannability.lean`:

```
PendingKeysWellIndexed_init (input : String) :
    PendingKeysWellIndexed ((ScannerState.mk' input).emit .streamStart)

ScanChain.preserves_PendingKeysWellIndexed
    {s s' : ScannerState} {n : Nat} (h_chain : ScanChain s n s')
    (h_inv : PendingKeysWellIndexed s) : PendingKeysWellIndexed s'

PendingKeysWellIndexed_of_chain_from_init
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_chain : ScanChain s₀ n s_final) :
    PendingKeysWellIndexed s_final

PendingKeysWellIndexed_emit_streamEnd (s : ScannerState) (tok : YamlToken)
    (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed (s.emit tok)
```

Mechanism: the initial state has empty `pendingKeys` and `tokens.size = 1`
after the `streamStart` emit, so the invariant holds vacuously; chain
preservation is induction over `ScanChain` applying
`scanNextToken_preserves_PendingKeysWellIndexed` at each step (mirroring
the existing `scanLoopFull_preserves_PendingKeysWellIndexed` on the
loop side); the final `emit .streamEnd` step preserves via
`PendingKeysWellIndexed_mono` (emit only adds tokens, does not touch
pending keys).

These four lemmas together discharge the chain-endpoint
`PendingKeysWellIndexed` precondition needed by step 2 of the cascade
skeleton below — specifically the `h_pks_bound : ∀ p (h : p < pks.size),
pks[p].insertBeforeIdx ≤ s₃.tokens.size` precondition of
`linearise_push_eq_push_linearise`.  Sorry count unchanged (12);
infrastructure landing.  Build green (453 jobs); ~70 lines including
docstrings.

**J.4.2.c-pos2 landed (2026-04-30)**: second-to-last positional readout
in `Proofs/Scanner/ScannerLinearise.lean`:

```
linearise_secondLast_eq_tokens_last_inner
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (t : Positioned YamlToken)
    (h_size : tokens.size > 0)
    (h_pks_le : ∀ p (h : p < pks.size), pks[p].insertBeforeIdx ≤ tokens.size - 1) :
    ∃ h_lin : (linearise (tokens.push t) pks).size ≥ 2,
      (linearise (tokens.push t) pks)[(linearise (tokens.push t) pks).size - 2]
        = tokens[tokens.size - 1]
```

Mechanism: peel the trailing `t` push via
`linearise_push_eq_push_linearise` (the `≤ tokens.size - 1` bound
implies the weaker `≤ tokens.size` that lemma needs), then read the
prefix element via `Array.getElem_push_lt` and compose with
`linearise_last_eq_tokens_last`.  The dependent index of
`linearise (tokens.push t) pks` is sidestepped via a `suffices`/`subst`
generalisation pattern.

This closes the J.4.2.c positional family at `{0, 1, size-2, size-1}`
plus the streamEnd push-peel — the four index readouts the seq/map
cascade consumers need to pin down `streamStart` / `flowSequenceStart`
(or `blockMappingStart`) / `flowSequenceEnd` (or `blockMappingEnd`) /
`streamEnd` on the post-`streamEnd` linearised output.  Sorry count
unchanged (12); infrastructure landing.  Build green (453 jobs); ~69
lines including docstring.

**J.4.2.c-prefix landed (2026-04-30)**: arbitrary-prefix readout in
`Proofs/Scanner/ScannerLinearise.lean`:

```
linearise_prefix_eq_tokens_prefix
    (tokens : Array (Positioned YamlToken))
    (pks : Array PendingKeyEntry)
    (i : Nat)
    (h_i : i ≤ tokens.size)
    (h_pks : ∀ p (h : p < pks.size), i ≤ pks[p].insertBeforeIdx) :
    ∃ (h_lin : i ≤ (linearise tokens pks).size),
      ∀ (j : Nat) (hj : j < i),
        (linearise tokens pks)[j] = tokens[j]
```

Mechanism: induct on `k` (number of `linearise.go` steps already taken)
to build an accumulator of size `k` whose contents are `(tokens[0], …,
tokens[k-1])`.  At each step the splice test `pks[0].insertBeforeIdx ≤
k` is false (since `insertBeforeIdx ≥ i > k` by hypothesis), so
`linearise.go` pushes `tokens[k]` and recurses to `(k+1, 0, acc.push
tokens[k])`.  After `i` steps prefix-stability
(`linearise_go_getElem_lt_acc`) reads off `tokens[0..i)`.  Implemented
via a `suffices` / nested existential to expose the size-equality
`acc.size = k` so the per-index proof obligation `j < acc.size` can be
discharged uniformly.

This generalises both `linearise_first_eq_tokens_first` (the `i = 1`
specialisation) and the index-1 readout from
`linearise_second_eq_tokens_second` (the `i = 2` specialisation), so
future cascade work can read off any number of leading boundary tokens
in a single `linearise_prefix_eq_tokens_prefix` call rather than chaining
per-position lemmas.  Sorry count unchanged (12); infrastructure
landing.  Build green (453 jobs); ~93 lines including docstring.

**J.4.2.b-2a landed (2026-04-30)**: `AllUnresolved` predicate +
algebraic-class preservation lemmas in
`Proofs/Scanner/ScannerCorrectness.lean`:

```
def AllUnresolved (s : ScannerState) : Prop :=
  ∀ e ∈ s.pendingKeys, e.kind = .unresolved

AllUnresolved_mono                              -- Class A passthrough
AllUnresolved_push_unresolved                   -- Class B append-.unresolved
AllUnresolved_field_update                      -- Class C kind-preserving
setPendingKeyKind_unresolved_preserves_AllUnresolved
                                                -- Class C variant for
                                                --   setPendingKeyKind .unresolved
saveSimpleKey_preserves_AllUnresolved           -- Class B specialisation
```

Mechanism: parallels the `PendingKeysWellIndexed` algebraic-class
machinery established in J.3.3.  Class A (passthrough) is the
trivial mono lemma.  Class B (append) uses
`Array.mem_push.rcases`; the appended entry from `saveSimpleKey`
always has `kind := .unresolved`.  Class C (field update) uses
`Array.mem_iff_getElem` plus a kind-equality hypothesis on every
kept entry.  The `setPendingKeyKind` variant uses the existing
`setPendingKeyKind_decomp` (identity ∨ `setIfInBounds`) and
`Array.mem_or_eq_of_mem_setIfInBounds` to dispatch over membership in
the post-update array — when the kind being written is
`.unresolved`, both arms preserve the predicate.

Single operation that breaks the predicate: `setPendingKeyKind active
<non-.unresolved>` fired by `scanValuePrepare` to confirm a
`:`-resolution.  Inputs that never trigger that path (no
`:`-bearing pairs) keep `AllUnresolved` through the chain — exactly
the syntactic sub-class 2c will exploit.  Sorry count unchanged
(12); infrastructure landing.  Build green (453 jobs); ~103 lines
including docstring.

**J.4.2.b-2a-chain landed (2026-04-30)**: chain-side companion to the
per-action `AllUnresolved` lemmas in
`Proofs/Output/EmitterScannability.lean`:

```
AllUnresolved_init                              -- vacuous on initial state
ScanChain.preserves_AllUnresolved               -- parametric chain induction
AllUnresolved_of_chain_from_init                -- combined helper from init
AllUnresolved_emit_streamEnd                    -- final emit step
```

Mechanism: mirrors the four-theorem PKWI chain-side block
(`PendingKeysWellIndexed_init` / `ScanChain.preserves_PendingKeysWellIndexed`
/ `PendingKeysWellIndexed_of_chain_from_init` /
`PendingKeysWellIndexed_emit_streamEnd`).  The key shape difference
is that `ScanChain.preserves_AllUnresolved` takes a **parametric**
per-action preservation hypothesis

```
h_step : ∀ {sa sb : ScannerState},
           AllUnresolved sa →
           scanNextToken sa = .ok sb →
           AllUnresolved sb
```

rather than relying on an unconditional `scanNextToken_preserves_*`
lemma.  This reflects the J.4.2.b-2a observation that
`AllUnresolved` is broken by `setPendingKeyKind active <non-.unresolved>`
fired in `scanValuePrepare`, so the per-action discharge depends on
the input sub-class (no `:`-bearing pairs).  Cascade consumers in
2c/2d will discharge `h_step` step-by-step via the Class A/B/C
machinery, scoped to the sub-class they target.

The `_emit_streamEnd` companion is unconditional — `emit` only pushes
a token and leaves `pendingKeys` unchanged, so `AllUnresolved`
survives the final `streamEnd` push that
`linearise_eq_filter_no_resolutions` operates on.  Sorry count
unchanged (12); infrastructure landing.  Build green (453 jobs); +86
lines including docstring.

**J.4.2.b-2a-discharge landed (2026-04-30)**: per-action preservation
discharging the parametric `h_step` of
`ScanChain.preserves_AllUnresolved` for the no-`:`-pair sub-class.
Lands in `Proofs/Scanner/ScannerCorrectness.lean`:

```
-- Class C ingredients (quoted-scalar wrappers):
setPendingKeyEndLine_kind                          -- kind preserved by endLine update
setPendingKeyEndLine_wrap_preserves_AllUnresolved  -- "/'  arms

-- scanValue sub-class (`simpleKey.possible = false` → Class A):
scanValueClearKey_no_key                                 -- identity result
scanValuePrepare_no_key_preserves_pendingKeys            -- Class A on pendingKeys
scanValue_no_key_preserves_pendingKeys                   -- full chain Class A
scanValue_preserves_AllUnresolved                        -- with sub-class hyp

-- Per-dispatcher AllUnresolved preservation:
dispatchStructural_preserves_AllUnresolved          -- Class A (mono lift)
dispatchFlowIndicators_preserves_AllUnresolved      -- Class A (mono lift)
dispatchBlockIndicators_preserves_AllUnresolved     -- with `c = ':' → ¬ simpleKey.possible`
dispatchContent_preserves_AllUnresolved             -- Class A + " /' Class C
preprocess_preserves_AllUnresolved                  -- A + Class B (saveSimpleKey)
allowDir_ite_preserves_AllUnresolved                -- pure projection

-- Top-level (parametric sub-class hypothesis):
scanNextToken_preserves_AllUnresolved
```

Mechanism: mirrors the `*_preserves_PendingKeysWellIndexed` chain
exactly, with each Class A action's preservation lifted from the
existing `*_preserves_pendingKeys` lemma via `AllUnresolved_mono`.
The single break path — `scanValuePrepare`'s `simpleKey.possible =
true` arm — is sealed off by carrying `s.simpleKey.possible = false`
through `scanValueClearKey` (no-op when not possible),
`scanValuePrepare` (skips the breaking branch, falls through to
`pushMappingIndent` / identity), `emit`, `advance`, and the final
`with simpleKeyAllowed, explicitKeyLine` projection — all of which
leave `pendingKeys` unchanged.  Quoted-scalar arms in
`dispatchContent` apply the Class C field-update via
`setPendingKeyEndLine_kind`, which leaves every entry's `kind`
fixed.  `preprocess` re-uses `saveSimpleKey_preserves_AllUnresolved`
(Class B, push of `.unresolved`) from J.4.2.b-2a.

The top-level lemma signature:

```
scanNextToken_preserves_AllUnresolved :
    ∀ (s s' : ScannerState),
      AllUnresolved s →
      scanNextToken s = .ok (some s') →
      (∀ s_pre c,
        scanNextToken_preprocess s = .ok (some (s_pre, c)) →
        c = ':' → s_pre.simpleKey.possible = false) →
      AllUnresolved s'
```

The hypothesis bridges the post-`allowDir_ite` state by an inline
`split <;> rfl` projection over `simpleKey.possible` (the
`allowDir_ite` mutation only touches `allowDirectives` /
`documentEverStarted`).  For the no-`:`-pair sub-class (flow seqs of
scalars; nested flow seqs), the hypothesis collapses to `c ≠ ':'`
at every preprocess output, trivially discharged by induction on
the input shape.  Sorry count unchanged (12); infrastructure
landing.  Build green (453 jobs); +350 lines.

**J.4.2.b-2b landed (2026-04-30)**: placeholder-free invariant
predicate plus chain-side propagation, the second of the two
hypotheses of `linearise_eq_filter_no_resolutions` (J.4.1).
Companion to J.4.2.b-2a/-2a-chain (`AllUnresolved`); together
they bridge the post-cutover `linearise` shape to the legacy
`tokens.filter (· != .placeholder)` shape used by Tier 1 emitter
derivations.

Lands in `Proofs/Scanner/ScannerCorrectness.lean` (predicate +
abstract preservation classes) and `Proofs/Output/EmitterScannability.lean`
(chain-side propagation):

```
-- Predicate + abstract preservation classes:
NoPlaceholders                                  -- ∀ t ∈ s.tokens, t.val ≠ .placeholder
NoPlaceholders_mono                             -- Class A (tokens equality)
NoPlaceholders_emit                             -- Class B (push non-.placeholder)
NoPlaceholders_emitAt                           -- Class B' (emitAt at fixed position)

-- Chain-side propagation (parametric in per-action `h_step`):
NoPlaceholders_init                             -- post-`streamStart` initial state
ScanChain.preserves_NoPlaceholders              -- chain induction
NoPlaceholders_of_chain_from_init               -- combined helper
NoPlaceholders_emit_streamEnd                   -- final `streamEnd` emit
```

The chain induction signature:

```
ScanChain.preserves_NoPlaceholders :
    ∀ {s s' : ScannerState} {n : Nat},
      ScanChain s n s' →
      (∀ {sa sb : ScannerState},
        NoPlaceholders sa →
        scanNextToken sa = .ok sb →
        NoPlaceholders sb) →
      NoPlaceholders s →
      NoPlaceholders s'
```

Mechanism: unlike `AllUnresolved`'s break path
(`scanValuePrepare`'s `:`-resolution arm flips a pending entry's
`kind` from `.unresolved`), `NoPlaceholders` has *no* break path
post-cutover.  J.2 step 5 removed every legacy `placeholder` push
from the scanner; the only mutations to `tokens` are now `emit`/
`emitAt` calls that always use a concrete YAML token
(`.streamStart`, `.flowSequenceStart`, `.scalar _ _`, etc.) — never
`.placeholder`.  No `setIfInBounds` on `tokens` either: the J.2
dual-write moved retroactive rewrites to `pendingKeys` only.  So
the predicate holds *unconditionally* through every scanner action
— the consumer discharges the parametric `h_step` without an input
sub-class restriction (in contrast to the no-`:`-pair restriction
on `AllUnresolved`).  Class C is absent from the algebraic
breakdown for the same reason: `tokens` is append-only, so no
field-update class is needed.

The parametric form mirrors `ScanChain.preserves_AllUnresolved` for
uniform consumer ergonomics — the cascade body characterizations
(2c/2d) take both `h_step` parameters together and discharge them
at the same place.  Per-action discharge (`scanNextToken_preserves_NoPlaceholders`)
is split out into the forthcoming **J.4.2.b-2b-discharge** landing,
mirroring the J.4.2.b-2a → J.4.2.b-2a-chain → J.4.2.b-2a-discharge
split.

Sorry count unchanged (12); infrastructure landing.  Build green
(453 jobs); +154 lines.

**J.4.2.b-2b-discharge landed (2026-04-30)**: per-action discharge of
the parametric `h_step` parameter of `ScanChain.preserves_NoPlaceholders`
(J.4.2.b-2b chain).  Mirrors the J.4.2.b-2a-discharge structure but is
**unconditional** — no sub-class hypothesis on the input is required,
since post-cutover every scanner action either preserves `tokens`
(Class A passthrough) or pushes a single concrete non-`.placeholder`
token (Class B).

Lands in `Proofs/Scanner/ScannerCorrectness.lean` (after
`scanNextToken_preserves_AllUnresolved`):

```
-- Generic helpers (extension via _adds_one_token + _preserves_prefix
-- + _new_token_not_placeholder):
NoPlaceholders_extension                        -- generic _size + _prefix + _new
NoPlaceholders_extension_one                    -- specialisation for single-push functions

-- Class A leaves:
advance_preserves_NoPlaceholders
advanceN_preserves_NoPlaceholders
skipToContent_preserves_NoPlaceholders
saveSimpleKey_preserves_tokens                  -- post-cutover identity on `tokens`
saveSimpleKey_preserves_NoPlaceholders
scanValueClearKey_preserves_NoPlaceholders

-- Indent helpers (Class B with .blockEnd / .blockSequenceStart /
-- .blockMappingStart):
pushSequenceIndent_preserves_NoPlaceholders
pushMappingIndent_preserves_NoPlaceholders
unwindIndentsLoop_preserves_NoPlaceholders      -- recursive on fuel
unwindIndents_preserves_NoPlaceholders

-- Flow indicator scanners:
scanFlow{SequenceStart,SequenceEnd,MappingStart,MappingEnd,Entry}_preserves_NoPlaceholders

-- Block indicator scanners:
scanBlockEntry_preserves_NoPlaceholders
scanKey_preserves_NoPlaceholders
scanValuePrepare_preserves_NoPlaceholders
scanValue_preserves_NoPlaceholders

-- Document/directive scanners:
scanDocumentStart_preserves_NoPlaceholders
scanDocumentEnd_preserves_NoPlaceholders
scanYamlDirective_new_token_not_placeholder    -- helper
scanTagDirective_new_token_not_placeholder     -- helper
scanDirective_preserves_NoPlaceholders

-- Content scanners (mirror canonical `_new_token_not_plain` helpers):
scanAnchorOrAlias_{new_token_not_placeholder, preserves_NoPlaceholders}
scanVerbatimTag_new_token_not_placeholder       -- helper
scanSecondaryTag_new_token_not_placeholder      -- helper
scanNamedTag_new_token_not_placeholder          -- helper
scanTag_{new_token_not_placeholder, preserves_NoPlaceholders}
scanBlockScalarBody_new_token_not_placeholder   -- helper
scanBlockScalar_{new_token_not_placeholder, preserves_NoPlaceholders}
scanDoubleQuoted_{new_token_not_placeholder, preserves_NoPlaceholders}
scanSingleQuoted_{new_token_not_placeholder, preserves_NoPlaceholders}
scanPlainScalar_{new_token_not_placeholder, preserves_NoPlaceholders}

-- Per-dispatcher:
dispatchStructural_preserves_NoPlaceholders
dispatchFlowIndicators_preserves_NoPlaceholders
dispatchBlockIndicators_preserves_NoPlaceholders
dispatchContent_preserves_NoPlaceholders

-- Top-level:
preprocess_preserves_NoPlaceholders
allowDir_ite_preserves_NoPlaceholders
scanNextToken_preserves_NoPlaceholders          -- ∀ s s', NoPlaceholders s →
                                                --   scanNextToken s = .ok (some s') →
                                                --   NoPlaceholders s'
                                                -- (NO sub-class hypothesis)
```

Mechanism: each per-function lemma reduces to one of two forms:

* **Class A** (e.g., `skipToContent`, `saveSimpleKey`, `scanValueClearKey`):
  apply `NoPlaceholders_mono` to the existing `_preserves_tokens` lemma.
* **Class B** (single-emit scanners): apply `NoPlaceholders_extension_one`
  with the existing `_adds_one_token` and `_preserves_prefix` lemmas plus
  a new `_new_token_not_placeholder` helper.  Each helper mirrors the
  canonical `_new_token_not_plain` proof from
  `Proofs/Production/ScannerPlainScalarValid` (substituting
  `.placeholder` for `.scalar _ .plain`): unfold the scanner function,
  resolve Except cases, reduce the new-token slot via
  `Array.getElem_push_eq` plus the appropriate `_preserves_tokens`
  chain, and close with `nofun` (token constructor mismatch).

Per-dispatcher lemmas mirror the existing
`*_preserves_PendingKeysWellIndexed` chain: `repeat (any_goals (split at h_ok))`
+ `all_goals first | exact ... | (simp_all; done)`.

Top-level `scanNextToken_preserves_NoPlaceholders` chains through
`preprocess_preserves_NoPlaceholders` and the four dispatcher
lemmas, structured identically to
`scanNextToken_preserves_AllUnresolved` but **without** the parametric
`h_no_resolve : ∀ s_pre c, ... → c = ':' → s_pre.simpleKey.possible = false`
sub-class hypothesis — all four dispatcher arms preserve
`NoPlaceholders` unconditionally.

This closes the J.4.2.b-2b chain symmetrically with the
J.4.2.b-2a chain (`AllUnresolved`):

| Predicate            | Predicate + Class A/B/C    | Chain induction        | Per-action discharge        |
| -------------------- | -------------------------- | ---------------------- | --------------------------- |
| `AllUnresolved`      | J.4.2.b-2a                 | J.4.2.b-2a-chain       | J.4.2.b-2a-discharge        |
|                      |                            |                        | (sub-class restricted)      |
| `NoPlaceholders`     | J.4.2.b-2b                 | J.4.2.b-2b (chain      | J.4.2.b-2b-discharge        |
|                      |                            |  in `EmitterScannability`) | (unconditional)         |

Sorry count unchanged (7 build / 12 logical); infrastructure landing.
Build green (453 jobs); +485 lines.

**Next concrete step (J.4.2.b — consumer refactor)**

The `_structure` consumers' `h_tok_eq` bridge is FALSE in general
(linearise output strictly larger than `(s₃.emit .streamEnd).tokens.filter p`
for any input containing a flow/block map pair), so it cannot be
discharged at the layer where it currently sits.  Replace each consumer's
`h_tok_eq` by `h_tok_lin : Scanner.scanFiltered input = .ok
(linearise (s₃.emit .streamEnd).tokens (s₃.emit .streamEnd).pendingKeys)`
(already true via `scanFiltered_of_chain_eq`), then re-derive the Tier 1
positional facts.

Skeleton of the cascade derivation (seq case; map is symmetric):

```
-- 1. Bridge to linearise form (replaces h_tok_eq, uses J.3.8 result):
have h_tok_lin : Scanner.scanFiltered input = .ok
    (linearise (s₃.emit .streamEnd).tokens (s₃.emit .streamEnd).pendingKeys) :=
  scanFiltered_of_chain_eq input s₀ s₃ s₃ (n+2) ... -- chain composition

-- 2. Decompose streamEnd push (uses J.4.2.c-prep + J.4.2.b-pkwi):
have h_pkwi_s₃ : PendingKeysWellIndexed s₃ :=
  PendingKeysWellIndexed_of_chain_from_init input _ s₃ (n+2) rfl h_chain_all
have h_pks_bound : ∀ p (h : p < s₃.pendingKeys.size),
    s₃.pendingKeys[p].insertBeforeIdx ≤ s₃.tokens.size :=
  fun p hp => (h_pkwi_s₃.2 p hp).2
have h_emit_se_pks : (s₃.emit .streamEnd).pendingKeys = s₃.pendingKeys := rfl
have h_lin_decomp : linearise (s₃.emit .streamEnd).tokens (s₃.emit .streamEnd).pendingKeys
    = (linearise s₃.tokens s₃.pendingKeys).push { pos := s₃.currentPos, val := .streamEnd } := by
  rw [show (s₃.emit .streamEnd).tokens = s₃.tokens.push _ from rfl, h_emit_se_pks]
  exact linearise_push_eq_push_linearise s₃.tokens s₃.pendingKeys _ h_pks_bound

-- 3. Last element via Array.getElem_push_eq:
-- tokens[size-1] = .streamEnd  ← from push of streamEnd

-- 4. Second-last via linearise_secondLast_eq_tokens_last_inner (J.4.2.c-pos2):
-- tokens[size-2] = s₃.tokens[s₃.tokens.size - 1]   (one-step composition: peels
--                                                    the streamEnd push and
--                                                    applies linearise_last on
--                                                    the inner array; needs
--                                                    pks ≤ s₃.tokens.size - 1,
--                                                    derivable since flowSeqEnd
--                                                    close doesn't register a
--                                                    new pendingKey)
--                = .flowSequenceEnd   (closure step)

-- 5. First element via linearise_first_eq_tokens_first:
-- tokens[0] = s₃.tokens[0] = .streamStart  (initial emit)

-- 6. Position 1 (flowSequenceStart): via linearise_second_eq_tokens_second
--    (J.4.2.c-pos1, just landed; needs ∀ pk, insertBeforeIdx ≥ 2,
--    always true at scanFiltered since earliest saveSimpleKey happens
--    at s₁.tokens.size = 2 after [streamStart, flowSequenceStart] emit)
```

Positional lemma status (in `Proofs/Scanner/ScannerLinearise.lean`):

- ✓ **`linearise_first_eq_tokens_first`** (pre-existing) — index 0 readout.
- ✓ **`linearise_last_eq_tokens_last`** (pre-existing) — last-index readout.
- ✓ **`linearise_push_eq_push_linearise`** (J.4.2.c-prep) — peel trailing
  `streamEnd` push.
- ✓ **`linearise_second_eq_tokens_second`** (J.4.2.c-pos1) — index 1 readout.
- ✓ **`linearise_secondLast_eq_tokens_last_inner`** (J.4.2.c-pos2) —
  second-to-last via push-decomp + last-on-inner; composes
  `linearise_push_eq_push_linearise` and `linearise_last_eq_tokens_last`.
  Reads `tokens[tokens.size - 2]` (closing `flowSequenceEnd` /
  `blockMappingEnd`) on the post-`streamEnd` linearised output.
- ✓ **`linearise_prefix_eq_tokens_prefix`** (J.4.2.c-prefix) —
  arbitrary-prefix readout: for any `i ≤ tokens.size`, if every pending
  entry's `insertBeforeIdx ≥ i`, the first `i` slots of `linearise tokens
  pks` equal the first `i` slots of `tokens` pointwise.  Subsumes
  `linearise_first_eq_tokens_first` (`i = 1`) and the index-1 readout
  from `linearise_second_eq_tokens_second` (`i = 2`).  Used to read off
  any number of leading boundary tokens uniformly.

Remaining J.4.2.b work:

1. ✓ **Done (J.4.2.b-pkwi, 2026-04-30)**: chain-endpoint
   `PendingKeysWellIndexed` derivation — landed as
   `PendingKeysWellIndexed_of_chain_from_init` (chain-side companion to
   `scanLoopFull_preserves_PendingKeysWellIndexed`) plus
   `PendingKeysWellIndexed_init` (initial state),
   `ScanChain.preserves_PendingKeysWellIndexed` (chain induction), and
   `PendingKeysWellIndexed_emit_streamEnd` (final emit step).  Step 2 of
   the cascade skeleton above now uses these directly.
2. **Linearise-shape body characterizations (the bulk)** — substantial
   multi-day leg.  The bulk task is now broken into smaller cadence-sized
   substeps:
   - ✓ **Done (J.4.2.b-2a, 2026-04-30)**: `AllUnresolved` predicate +
     Class A/B/C preservation lemmas (`AllUnresolved_mono`,
     `AllUnresolved_push_unresolved`, `AllUnresolved_field_update`,
     `setPendingKeyKind_unresolved_preserves_AllUnresolved`,
     `saveSimpleKey_preserves_AllUnresolved`) in
     `Proofs/Scanner/ScannerCorrectness.lean`.  The predicate captures
     "no `:`-resolution has fired" as a named definition, with
     algebraic-class preservation lemmas mirroring the
     `PendingKeysWellIndexed` machinery.
   - ✓ **Done (J.4.2.b-2a-chain, 2026-04-30)**: chain-side propagation
     of `AllUnresolved` (`AllUnresolved_init`,
     `ScanChain.preserves_AllUnresolved`,
     `AllUnresolved_of_chain_from_init`,
     `AllUnresolved_emit_streamEnd`) in
     `Proofs/Output/EmitterScannability.lean`.  The chain induction is
     **parametric** in a per-action preservation hypothesis (`h_step :
     AllUnresolved sa → scanNextToken sa = .ok sb → AllUnresolved
     sb`), reflecting the observation that `setPendingKeyKind active
     <non-.unresolved>` from `scanValuePrepare` is the single break
     path.  Cascade consumers in 2c/2d discharge `h_step` step-by-step
     via the Class A/B/C machinery from 2a, scoped to the no-`:`-pair
     sub-class they target.  The `_emit_streamEnd` companion is
     unconditional.
   - ✓ **Done (J.4.2.b-2a-discharge, 2026-04-30)**: per-action
     preservation discharging the parametric `h_step` of
     `ScanChain.preserves_AllUnresolved` for the no-`:`-pair
     sub-class.  Lands the full `*_preserves_AllUnresolved` chain
     mirroring `*_preserves_PendingKeysWellIndexed`: Class C
     ingredients (`setPendingKeyEndLine_kind`,
     `setPendingKeyEndLine_wrap_preserves_AllUnresolved`); the
     `scanValue` sub-class triple
     (`scanValueClearKey_no_key`,
     `scanValuePrepare_no_key_preserves_pendingKeys`,
     `scanValue_no_key_preserves_pendingKeys`,
     `scanValue_preserves_AllUnresolved`); per-dispatcher
     preservation (`dispatchStructural`, `dispatchFlowIndicators`,
     `dispatchBlockIndicators` with `c = ':' → simpleKey.possible
     = false`, `dispatchContent`, `preprocess`, `allowDir_ite`); and
     the top-level `scanNextToken_preserves_AllUnresolved`
     parametric in a sub-class hypothesis on the post-preprocess
     state.  For the no-`:`-pair sub-class the hypothesis collapses
     to `c ≠ ':'` at every dispatch point.  Cascade consumers (2c)
     plug this directly into `ScanChain.preserves_AllUnresolved`
     (J.4.2.b-2a-chain) after sub-class specialization.
   - ✓ **Done (J.4.2.b-2b, 2026-04-30)**: placeholder-free invariant
     predicate plus chain-side propagation.  `NoPlaceholders s := ∀
     t ∈ s.tokens, t.val ≠ .placeholder` lands in
     `Proofs/Scanner/ScannerCorrectness.lean` with Class A
     (`NoPlaceholders_mono`) + Class B (`NoPlaceholders_emit`,
     `NoPlaceholders_emitAt`); chain-side
     `NoPlaceholders_init` / parametric
     `ScanChain.preserves_NoPlaceholders` /
     `NoPlaceholders_of_chain_from_init` /
     `NoPlaceholders_emit_streamEnd` land in
     `Proofs/Output/EmitterScannability.lean`.  No break path
     post-cutover (the J.2 step 5 cutover removed every legacy
     `.placeholder` push), so the chain induction's parametric
     `h_step` is dischargeable unconditionally — open follow-up
     work tracked under 2b-discharge below.
   - ✓ **Done (J.4.2.b-2b-discharge, 2026-04-30)**: per-action discharge
     of the parametric `h_step` parameter of
     `ScanChain.preserves_NoPlaceholders`.  `scanNextToken_preserves_NoPlaceholders`
     proves `∀ s s', NoPlaceholders s → scanNextToken s = .ok (some s') →
     NoPlaceholders s'` **unconditionally** (no sub-class hypothesis):
     post-cutover every scanner action is either Class A passthrough
     (`*_preserves_tokens` lemmas) or Class B push of a concrete
     non-`.placeholder` token (`NoPlaceholders_emit` /
     `NoPlaceholders_emitAt`, with `_new_token_not_placeholder` helpers
     mirroring the canonical `_new_token_not_plain` proofs from
     `Proofs/Production/ScannerPlainScalarValid`).  Per-dispatcher
     proofs follow the `*_preserves_PendingKeysWellIndexed` template.
     Closes the J.4.2.b-2b chain symmetrically with the
     J.4.2.b-2a → 2a-chain → 2a-discharge pattern.
   - ✓ **Done (J.4.2.b-2c, 2026-04-30)**: linearise-shape variant of
     `emitList_body_filtered_characterization` for the no-resolution
     sub-class.  `emitList_body_linearise_characterization` wraps the
     filter-shape body characterization with three additional outputs:
     (i) `AllUnresolved s'` derived via `ScanChain.preserves_AllUnresolved`
     (J.4.2.b-2a-chain), parametric in a per-action `h_step_unres`
     hypothesis discharged by `scanNextToken_preserves_AllUnresolved`
     (J.4.2.b-2a-discharge) under the no-`:`-pair sub-class; (ii)
     `NoPlaceholders s'` derived via `ScanChain.preserves_NoPlaceholders`
     (J.4.2.b-2b-chain), discharged unconditionally by
     `scanNextToken_preserves_NoPlaceholders` (J.4.2.b-2b-discharge);
     (iii) the bridge equality `linearise s'.tokens s'.pendingKeys =
     s'.tokens.filter p` via `linearise_eq_filter_no_resolutions` (J.4.1).
     Parts (1) and (2) of the conclusion are restated on `linearise
     s'.tokens s'.pendingKeys` instead of `s'.tokens.filter p`, transported
     via `rw [h_lin_eq]`.  Cascade consumers in
     `scanFiltered_emitSeq_nonempty_structure` can now read body content
     tokens off the linearise-shape post-cutover bridge target using the
     J.4.2.c positional family (`-pos1`, `-pos2`, `-prefix`) and the
     `linearise_push_eq_push_linearise` (J.4.2.c-prep) `streamEnd` peeler.
   - ✓ **Done at stub level (J.4.2.b-2d-stub, 2026-04-30)**: linearise-shape
     variant of `emitPairList_body_filtered_characterization` for the
     resolution case.  `emitPairList_body_linearise_characterization` wraps
     the filter-shape body characterization, carries the chain + 13
     invariants + `n ≥ 3` from the filter-shape result, and derives
     `NoPlaceholders s'` (unconditional via `scanNextToken_preserves_NoPlaceholders`
     from J.4.2.b-2b-discharge).  States linearise-shape Part (2)
     (`linearise[old_sz].val = .key`) and Part (3) (`linearise[k+1].val
     = .key` after every outer-level flowEntry) on `linearise s'.tokens
     s'.pendingKeys` directly — no `linearise = filter` bridge, since the
     `:` resolutions splice `.key` tokens not present in the filter shape.
     Note: `AllUnresolved s'` does NOT carry through (resolutions are by
     design here), so the 2c transport pattern (`rw [h_lin_eq]`) cannot be
     reused.  Sorry count delta: +2 (one sorry per linearise-shape part,
     stubbed as **J.4.2.b-2d-key** follow-up).
   - ✓ **Done (J.4.2.b-2d-key-foundation-A, 2026-04-30)**: Foundation A
     for the 2d-key splice mechanic — `linearise_first_splice_keyonly`
     in `Proofs/Scanner/ScannerLinearise.lean` (after
     `linearise_prefix_eq_tokens_prefix`).  Closes the splice-mechanic
     half of Part (2): given `pks.size > 0`, `pks[0].kind = .keyOnly`,
     and `pks[0].insertBeforeIdx = j ≤ tokens.size`, derives
     `(linearise tokens pks)[j].val = .key`.  Proof structure: walk
     `linearise.go` from `(0, 0, #[])` to `(j, 0, tokens[0..j])` without
     firing splices (induction adapted from
     `linearise_prefix_eq_tokens_prefix`), step once more to fire the
     `pks[0]` splice (`expandKind .keyOnly = #[⟨pos, .key, pos⟩]`), then
     read off `.key` at index `j` via `linearise_go_getElem_lt_acc`.
     Reshapes Part (2) of `emitPairList_body_linearise_characterization`
     to consume Foundation A: the splice analysis is fully discharged;
     only the chain-side facts remain as **J.4.2.b-2d-key-chain**.  Sorry
     count delta: 0 (the Part (2) splice-analysis sorry is replaced by
     the chain-side accounting sorry, same shape narrowed to a concrete
     fact about `s'.pendingKeys[0]`).  Foundation A is now also a reusable
     building block for the analogous `.blockMappingStartAndKey` splice
     case if needed downstream.
   - ✓ **Done (J.4.2.b-2d-key-foundation-B, 2026-04-30)**: Foundation B
     for the 2d-key splice mechanic at general `(j, p, acc)` state —
     `linearise_splice_keyonly_at` (and index-form corollary
     `linearise_splice_keyonly_at_index`) in
     `Proofs/Scanner/ScannerLinearise.lean` (after Foundation A).  Closes
     the splice-mechanic half of Part (3): given a transport equation
     `linearise tokens pks = linearise.go tokens pks j p acc` and
     splice-fire preconditions (`p < pks.size`,
     `pks[p].insertBeforeIdx ≤ j`, `pks[p].kind = .keyOnly`), derives
     `(linearise tokens pks)[acc.size].val = .key`.  Companion to
     Foundation A: A indexes from the start (walks `(0, 0, #[]) → (j, 0,
     tokens[0..j])` internally, then fires `pks[0]`); B is the splice
     mechanic in isolation, parameterized on a general `(j, p, acc)`
     state — chain-side accounting supplies the transport equation.
     Proof structure (mirrors the inner half of Foundation A): step once
     to fire splice; `expandKind .keyOnly = #[⟨pos, .key, pos⟩]` gives
     `.key` at the new acc's index `acc.size`; prefix-stability
     (`linearise_go_getElem_lt_acc`) propagates to final result;
     transport via `h_eq` + step equation.  Reshapes Part (3) of
     `emitPairList_body_linearise_characterization` to consume Foundation B
     (index form, with `acc.size = k + 1` for the after-flowEntry
     position): the splice analysis is fully discharged; only the
     chain-side facts remain as **J.4.2.b-2d-key-chain** (extended).
     Sorry count delta: 0 (Part (3) splice-analysis sorry replaced by
     chain-side accounting sorry, same shape narrowed to a concrete
     fact about `s'.pendingKeys[p]`).
   - ✓ **Done (J.4.2.b-2d-key-prep, 2026-04-30)**: pre-step toward
     chain-side accounting.  Added `h_pks_empty : s.pendingKeys = #[]`
     precondition to `emitPairList_body_linearise_characterization` —
     needed to make Foundation A's `[0]`-index semantically aligned
     with "first new pendingKey from the body" (without it, `pks[0]`
     could be an outer-scope leftover with smaller `insertBeforeIdx`).
     Discharged the trivial token-monotonicity sub-fact
     `(s.tokens.filter p).size ≤ s'.tokens.size` directly from
     `ScanChain_tokens_mono` + `Array.size_filter_le`, no longer
     bundled in the chain-side sorry — only the genuine
     pendingKey-shape facts remain.  At the eventual call site
     (`scanFiltered_emitMap_nonempty_structure` from
     `scanNextToken_flow_open_mapping_init`), `s₁.pendingKeys = #[]`
     is structurally true: `mk' input` initializes with empty
     pendingKeys, and the `{` scan emits `.flowMappingStart` only —
     no `saveSimpleKey`.  Exposing this at
     `scanNextToken_flow_open_mapping_init`'s output is a small
     cascade-stitching task (item 3), not part of 2d-key-chain itself.
     Sorry count delta: 0 (precondition refinement + trivial sub-fact
     discharge; same chain-side accounting count, narrower shape).
   - ✓ **Done (J.4.2.b-2d-key-chain-Part2-stub, 2026-04-30)**: extracted
     the first-key chain-side accounting into a freestanding stub
     theorem `emitPairList_chain_first_pkShape` (in
     `Proofs/Output/EmitterScannability.lean`, just before the
     wrapper).  Signature accepts the chain `ScanChain s n s'` plus
     the standard hypotheses + `h_pks_empty`, produces
     `0 < s'.pendingKeys.size ∧ s'.pendingKeys[0].insertBeforeIdx
       = s.tokens.size ∧ s'.pendingKeys[0].kind = .keyOnly`.  Body is
     `sorry`; wrapper Part (2) now calls the stub cleanly (filter
     identity transports `s.tokens.size ↔ (s.tokens.filter p).size`
     via `h_filter_eq_s`).  Sorry count delta: 0 (Part (2) inline
     sorry replaced by stub sorry — same count, structurally cleaner).
   - **2d-key-chain-Part2-body (proof body for the first-key stub)**:
     discharge `emitPairList_chain_first_pkShape`'s body.  Investigation
     showed this requires deeper infrastructure than initially scoped:
     `EmitScansInFlow`'s current conclusion does NOT expose pendingKey
     shape after the key scan.  Refined plan (2-3 cadence steps):
     1. **2d-key-chain-Part2-body-A (`EmitScansInFlow` strengthening)**:
        add a conjunct exposing the post-scan pendingKey shape — under
        precondition `s.simpleKeyAllowed = true ∧ s.pendingKeys = #[]`
        (or generalize via "extends s.pendingKeys with one new
        unresolved entry at `insertBeforeIdx = s.tokens.size`"),
        conclude `s'.pendingKeys.size = s.pendingKeys.size + 1`,
        `s'.pendingKeys[s.pendingKeys.size].kind = .unresolved`,
        `s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size`,
        `s'.pendingKeyActive = some s.pendingKeys.size`,
        `s'.simpleKey.possible = true`.  Investigation showed this
        decomposes naturally into 4 sub-steps:
        - ✓ **A1 (`saveSimpleKey_pkPush_when_allowed` foundational
          lemma)** [done 2026-05-01]: exact pendingKey effect of
          `saveSimpleKey` under the push branch —
          `(saveSimpleKey s).pendingKeys = s.pendingKeys.push
          <unresolved at s.tokens.size>`, `pendingKeyActive = some
          s.pendingKeys.size`, `simpleKey.possible = true`.  Companion
          to the existing `saveSimpleKey_id_of_flow_ska_false_ek_none`
          (identity branch).  Consumed by A2/A3/A4 and potentially
          Part2-body-B (`:`-resolution).  Lives in
          `Proofs/Output/EmitterScannability.lean` after the existing
          identity-branch lemma.
        - ✓ **A2 (per-leaf scalar
          `scanNextToken_flow_scanDoubleQuoted_pkPush`)**
          [done 2026-05-01]: parallel theorem next to
          `scanNextToken_flow_scanDoubleQuoted` (in
          `Proofs/Output/EmitterScannability.lean`) under additional
          hypotheses `s.simpleKeyAllowed = true ∧ s.explicitKeyLine
          = none`.  Conclusion adds three pendingKey-tracking
          conjuncts on top of the existing 13: A1 (pkPush), then
          `scanDoubleQuoted_preserves_pendingKeys`, then the
          `dispatchContent` `setPendingKeyEndLine` wrap (preserves
          size + insertBeforeIdx + kind per-entry; only endLine
          changes).  Yields `s'.pendingKeys.size = s.pendingKeys.size
          + 1`, `s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx
          = s.tokens.size`, `s'.pendingKeys[s.pendingKeys.size].kind
          = .unresolved`.  Implementation uses parallel-proof copy
          (not in-place augmentation) since the existing theorem has
          only one in-tree caller (`emit_scans_in_flow`) which would
          eventually need re-threading anyway.
        - ✓ **A3 (per-leaf flow-sequence open
          `scanNextToken_flow_open_nested_pkPush`)**
          [done 2026-05-01]: parallel theorem next to
          `scanNextToken_flow_open_nested` (in
          `Proofs/Output/EmitterScannability.lean`) under the same
          additional hypotheses as A2 (`s.simpleKeyAllowed = true ∧
          s.explicitKeyLine = none`).  Conclusion adds the same three
          pendingKey-tracking conjuncts on top of the existing 12:
          A1 (pkPush) + `scanFlowSequenceStart_preserves_pendingKeys`
          (Class A — pure preservation, NO `setPendingKeyEndLine` wrap
          since `[` is dispatched via flow indicators, not content).
          Yields `s'.pendingKeys.size = s.pendingKeys.size + 1`,
          `s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx =
          s.tokens.size`, `s'.pendingKeys[s.pendingKeys.size].kind =
          .unresolved`.  Note: A3 covers ONLY the `[` open step (not
          full body+close); body content is handled by recursion
          through other per-leaf lemmas, and the outer entry is not
          touched by inner scans (they push new entries at fresh
          indices without disturbing index `s.pendingKeys.size`).
          Simpler than A2 since the `[` flow path skips
          `dispatchContent` entirely.
        - ✓ **A4 (per-leaf flow-mapping open
          `scanNextToken_flow_open_mapping_nested_pkPush`)**
          [done 2026-05-01]: mechanical mirror of A3 with `[` → `{`,
          `scanFlowSequenceStart` → `scanFlowMappingStart`,
          `dispatchFlowIndicators_bracket` → `dispatchFlowIndicators_brace`,
          using `scanFlowMappingStart_preserves_pendingKeys` (Class A —
          pure preservation, NO `setPendingKeyEndLine` wrap since `{`
          is dispatched via flow indicators, not content).  Same 12
          existing conjuncts + 3 pendingKey conjuncts as A3.  The outer
          mapping's pendingKey is recorded by the outer `saveSimpleKey`;
          inner content scans (body of the mapping including any `:`
          resolutions for inner pairs) push new entries at later indices
          and do not touch the outer entry.  Landed in
          `Proofs/Output/EmitterScannability.lean` next to
          `scanNextToken_flow_open_mapping_nested`.

        After A1-A4: add the gated conjunct to `EmitScansInFlow`
        definition; re-prove `emit_scans_in_flow` cases scalar/seq/map
        using the per-leaf lemmas.  Estimate: ~0.5 cadence step.
     2. ✓ **2d-key-chain-Part2-body-B (`scanNextToken_flow_value`
        strengthening, theorem `scanNextToken_flow_value_pkResolve`)**
        [done 2026-05-01]: under preconditions `s.simpleKeyAllowed =
        false ∧ s.simpleKey.possible = true ∧ s.pendingKeyActive = some
        i ∧ i < s.pendingKeys.size` (the `simpleKeyAllowed = false`
        precondition makes `saveSimpleKey s = s` so the active pending
        index flows unchanged into `scanValuePrepare`'s flow branch),
        the `:` step's `scanValuePrepare` flow branch resolves the
        entry at index `i` to `.keyOnly` via `setPendingKeyKind`.
        Concludes the existing 13 surface conjuncts of
        `scanNextToken_flow_value` plus 3 pkResolve conjuncts:
        `s'.pendingKeys.size = s.pendingKeys.size`,
        `(s'.pendingKeys[i]).kind = .keyOnly` together with
        `insertBeforeIdx` preservation at `i`, and `s'.pendingKeys[j]
        = s.pendingKeys[j]` for all `j ≠ i`.  Foundational helper
        `scanValuePrepare_pendingKeys_flow_resolve` (in flow with
        `simpleKey.possible = true`, the prepare's pendingKeys equals
        `setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly`)
        sits next to `saveSimpleKey_pkPush_when_allowed` /
        `scanValueValidate_ok_of_not_possible_ek_none`.  Proof reuses
        the existing `scanNextToken_flow_value` to discharge surface
        conjuncts, then re-derives the canonical `s_final` chain to
        identify `s'` via determinism and tracks pendingKeys through
        `saveSimpleKey` (identity) → `s_ad` (allowDirectives doesn't
        touch pendingKeys/pendingKeyActive) → `scanValueClearKey`
        (identity since `ek = none`) → `scanValuePrepare` flow branch
        (the `setPendingKeyKind` write) → `emit`/`advance`/final
        record-update (Class A passthroughs).  Per-entry pkResolve
        conjuncts derived via `Array.getElem_setIfInBounds_self` /
        `Array.getElem_setIfInBounds_ne`.  Landed in
        `Proofs/Output/EmitterScannability.lean` next to
        `scanNextToken_flow_value`.
     3. ✓ **2d-key-chain-Part2-body-C (compose + dispatch in
        `emitPairList_chain_first_pkShape`)** [done 2026-05-02; all
        10 sub-steps below ✓]: walked the singleton/cons induction
        structure of `emitPairList_scans_nonempty` using the
        strengthened conclusions.  After `EmitScansInFlow p.1` from
        `s.pendingKeys = #[]`, `s₁.pendingKeys = #[<unresolved at
        s.tokens.size>]`, `s₁.pendingKeyActive = some 0`,
        `s₁.simpleKey.possible = true`.  After `:` step (saveSimpleKey
        is identity since `simpleKeyAllowed = false` at `s₁`),
        `scanValuePrepare`'s flow branch resolves index 0 to
        `.keyOnly`.  Subsequent value scan and IH on tail only push
        new entries / resolve later indices, preserving `[0]`.

        **Status snapshot (as of 2026-05-02, sorry count 8):**
        body-C is **fully discharged**.  The body-C umbrella's
        proof landed in the **C-compose** sub-step by extending
        `EmitPairListScansInFlow` with a first-pair resolved-key
        conjunct (under `pairs ≠ []`), threading it through
        `emitPairList_body_filtered_characterization` as Part (4),
        and using it directly in
        `emitPairList_body_linearise_characterization` Part (2) —
        which let us **remove** the sorry'd stub
        `emitPairList_chain_first_pkShape` entirely.

        On closer look during the 2026-05-01 cadence, body-C decomposes
        into multiple sub-steps because per-leaf A2/A3/A4's existing
        conclusions only expose `pendingKeys.size + pkPush entry shape`
        — body-C also requires `pendingKeyActive = some s.pendingKeys.size`,
        `simpleKey.possible = true`, and `preserves-prior` (entries at
        `j < s.pendingKeys.size` unchanged) at the post-key state.
        Decomposed sub-steps (cadence-sized):
        * ✓ **C-foundation-Aseq/Amap (preserves-prior on A3/A4)**
          [done 2026-05-01]: extend `scanNextToken_flow_open_nested_pkPush`
          (A3) and `scanNextToken_flow_open_mapping_nested_pkPush` (A4)
          with `∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj`.  Proof: the
          flow-open path skips `dispatchContent`, so
          `s'.pendingKeys = s.pendingKeys.push <new>` directly; preservation
          via `Array.getElem_push_lt`.  No `pendingKeyActive` chain
          needed since there is no `setPendingKeyEndLine` wrap.  Sorry
          count unchanged at 9.
        * ✓ **C-foundation-Ascalar (preserves-prior + active + possible
          on A2)** [done 2026-05-01]: extended
          `scanNextToken_flow_scanDoubleQuoted_pkPush` (A2) with three
          new conjuncts at the post-key state — `s'.pendingKeyActive
          = some s.pendingKeys.size`, `s'.simpleKey.possible = true`,
          and `preserves-prior` (`∀ j (hj : j < s.pendingKeys.size)
          (hj' : j < s'.pendingKeys.size), s'.pendingKeys[j]'hj' =
          s.pendingKeys[j]'hj`).  The `setPendingKeyEndLine` wrap in
          `dispatchContent` was the trickier piece: needed a new
          `*_preserves_pendingKeyActive` chain in
          `Proofs/Scanner/ScannerCorrectness.lean` (advance, emit,
          emitAt, skipSpacesLoop/skipSpaces, skipWhitespaceLoop/
          skipWhitespace, consumeNewline, collectHexDigitsLoop,
          parseHexEscape, processEscape, foldQuotedNewlinesLoop/
          foldQuotedNewlines, collectDoubleQuotedLoop, scanDoubleQuoted)
          to thread `pendingKeyActive` through the scalar scan body
          unchanged.  Two new helpers `setPendingKeyEndLine_decomp_some`
          and `setPendingKeyEndLine_some_at_other_unchanged` expose the
          active index in the decomposition so preserves-prior at
          `j < s.pendingKeys.size = active` can be discharged via
          `Array.getElem_setIfInBounds_ne`.  Sorry count unchanged at 9.
        * **C-foundation-EmitScansInFlow** — scope investigation
          (2026-05-01) revealed this is bigger than the original "~1
          cadence step" estimate.  Decomposed into 4 sub-steps:
          1. ✓ **C-foundation-EmitScansInFlow-helpers** (landed
             2026-05-02): pkRec preservation conjunct
             (insertBeforeIdx + kind preserved at indices < initial
             size, NOT endLine — which is mutated by
             `setPendingKeyEndLine` under `dispatchContent`'s wrap)
             added to 7 of 8 helper theorems used in the
             `emit_scans_in_flow` cases:
             `scanNextToken_preprocess_flow_ws1`,
             `scanNextToken_flow_comma`,
             `scanNextToken_flow_open_nested`,
             `scanNextToken_flow_close_seq_nested`,
             `scanNextToken_flow_open_mapping_nested`,
             `scanNextToken_flow_close_mapping_nested`,
             `scanNextToken_flow_scanDoubleQuoted`.  Foundational
             helper `saveSimpleKey_preserves_pkRec_prior` introduced
             — under any preconditions, `saveSimpleKey` preserves
             `(insertBeforeIdx, kind)` of all entries < initial
             size (push-or-id; via `Array.getElem_push_lt`).  The
             8th helper, `scanNextToken_flow_value`, is deferred to
             a follow-up sub-step because `scanValuePrepare`'s flow
             branch fires `setPendingKeyKind` at `pendingKeyActive`,
             which can land at j < initial-size when the active was
             pre-set (the `:`-resolve path covered by
             Part2-body-B).  This needs a gated formulation
             ("active = some i with i ≥ initial size" or
             "simpleKey.possible = false ∧ pendingKeyActive = none"
             at scan start).  Sorry count unchanged at 9.
          2. ✓ **C-foundation-EmitScansInFlow-defns** (~2.5 steps,
             revised from ~1 after scope investigation 2026-05-02;
             all four sub-steps landed 2026-05-02):
             add the pkRec preservation conjunct **plus** size
             monotonicity (`s.pendingKeys.size ≤ s'.pendingKeys.size`)
             to the three `EmitScansInFlow{,List,PairList}`
             definitions; re-prove `emit_scans_in_flow` (scalar/seq/map)
             and the `emit{List,PairList}_scans_{empty,nonempty}`
             family.
             Scope finding: chain proofs through helpers require
             intermediate `j < intermediate.pendingKeys.size`
             bounds, derivable only from size monotonicity; the
             helpers from sub-step 1 expose pkRec preservation but
             NOT size monotonicity, so the defns work needs to
             extend each helper with a size-mono conjunct first.
             Decomposition:
             - ✓ **defns-helpers-size** (landed 2026-05-02 as
               `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-helpers-size`):
               extended the 6 scanner helpers
               (`scanNextToken_flow_scanDoubleQuoted`,
               `_open_nested`, `_close_seq_nested`,
               `_open_mapping_nested`, `_close_mapping_nested`,
               `_comma`) with `s.pendingKeys.size ≤ s'.pendingKeys.size`
               conjunct.  Foundational lemma
               `saveSimpleKey_pendingKeys_size_ge` introduced.
               No consumer destructure updates needed (right-assoc
               `∧` bundles the new conjunct with existing pkRec in
               callers' anonymous `_h_pks…` binders).
             - ✓ **defns-prove** (landed 2026-05-02 as
               `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove`):
               extended the three `EmitScansInFlow{,List,PairList}`
               definitions with size-mono + pkRec conjuncts.  Composed
               proofs through helpers via two new composition lemmas
               (`pkRec_size_compose`, `pkRec_size_of_pks_eq`).
               `emitList_scans_empty/nonempty` and
               `emitPairList_scans_empty` proved cleanly.
               `emit_scans_in_flow` proved cleanly for scalar/sequence/mapping
               (mapping case composes through the EmitPairListScansInFlow
               sorry'd witness).  Discharged downstream destructure updates
               at all consumer sites (10+ destructure patterns updated to
               bind the new conjuncts as `_h_size…`/`_h_pkRec…`).  Net
               regression: +1 sorry — the body-C colon-step (size + pkRec)
               preservation through `scanNextToken_flow_value` is captured
               in a single sorry'd helper
               `emitPairList_body_size_pkRec_through_colon_sorry`, used at
               both call sites of `emitPairList_scans_nonempty` (singleton
               + cons).  This factors cleanly to the **gated** sub-step,
               which extends `scanNextToken_flow_value` with the active-index
               pkRec analysis needed to discharge the helper.
             - ✓ **defns-consumers** (folded into defns-prove,
               landed 2026-05-02): downstream destructure updates
               landed alongside defns-prove since they were
               mechanical (10+ destructure patterns updated to bind
               the new `_h_size…`/`_h_pkRec…` conjuncts).
             - ✓ **stack-restore** (landed 2026-05-02 as
               `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore`):
               close-side restore lemmas
               `scanFlowSequenceEnd_pendingKeyActive_restored` /
               `_pendingKeyStack_popped` and mapping analogs in
               ScannerCorrectness; extended
               `scanNextToken_flow_close_seq_nested` and
               `_close_mapping_nested` to expose
               `s'.simpleKey = s.simpleKeyStack.back?.getD {}`,
               `s'.pendingKeyActive = s.pendingKeyStack.back?.getD none`,
               `s'.pendingKeyStack = s.pendingKeyStack.pop`; extended
               open helpers (`scanNextToken_flow_open_nested` /
               `_open_mapping_nested`) with
               `s'.pendingKeyStack.pop = s.pendingKeyStack` (mirror
               of the existing simpleKeyStack pop); extended
               `scanNextToken_flow_comma`,
               `scanNextToken_preprocess_flow_ws1` with
               `s'.pendingKeyStack = s.pendingKeyStack` (Class A
               passthroughs); added `pendingKeyStack` preservation
               conjunct to `EmitScansInFlow` (main),
               `EmitListScansInFlow`, `EmitPairListScansInFlow`;
               re-proved `emit_scans_in_flow` (scalar/seq/map),
               `emitList_scans_*`, `emitPairList_scans_*`.  Net
               regression: +1 sorry —
               `scanDoubleQuoted_preserves_pendingKeyStack_sorry`
               in the scalar leg, deferred to a follow-on
               "preservation-chain" sub-step (mechanical mirror of
               the existing `_preserves_simpleKeyStack` chain
               through `collectDoubleQuotedLoop` / `processEscape` /
               `parseHexEscape` etc., ≈30 lemmas).  Sorry count:
               10 → 11.
          3. ✓ **C-foundation-EmitScansInFlow-gated** (landed
             2026-05-02 as
             `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated`):
             added the gated first-key conjunct to `EmitScansInFlow`
             (only — not List/PairList) under a
             `s.simpleKeyAllowed = true` gate, exposing the
             three first-key facts at the post-state: existential
             of strict-grew + entry kind/insertBeforeIdx, plus
             `pendingKeyActive = some s.pendingKeys.size` and
             `simpleKey.possible = true`.  The duplicate
             "preserves-prior at j < s.pendingKeys.size" was
             dropped from the gated branch since the unconditional
             kind+insertBeforeIdx conjunct already covers it (the
             colon-step discharge needs that weaker form, not
             entry-equality).  Scalar case discharged inline by
             calling `scanNextToken_flow_scanDoubleQuoted_pkPush`
             in parallel under the gate and using determinism of
             `scanNextToken` to identify the s' from the
             unconditional + pkPush variants.  Seq/map cases
             deferred via two named sorry'd helpers
             `emit_scans_in_flow_seq_gated_sorry` and
             `emit_scans_in_flow_map_gated_sorry`, since the
             proper discharge requires either (a) extending
             `_pkPush` open helpers with `simpleKeyStack`/
             `pendingKeyStack` push-shape conjuncts (so close's
             restore lemmas can compute the back-of-stack values)
             or (b) inline reasoning about
             `scanFlowSequenceStart`/`MappingStart`'s effect on
             stacks via `_pushed` lemmas + `back?_push` (≈40-60
             lines per case) — split out as its own focused
             sub-step.  Consumer destructures updated to bind the
             new gated conjunct (`_h_gated…` placeholders) at 4
             call sites: `emitList_scans_nonempty` singleton+cons,
             `emitPairList_scans_nonempty` singleton+cons.  The
             body-C colon-step sorry'd helper
             `emitPairList_body_size_pkRec_through_colon_sorry`
             remains; its discharge is split out as a separate
             sub-step (see **discharge-colon** below) since it
             needs the seq/map gated discharges to be proper
             (not sorry'd) for the gated facts to flow into
             `pkResolve`.  Net regression: +2 sorries
             (seq + map gated placeholders), sorry count:
             11 → 13.  Build clean across 453 jobs.
          4. ✓ **C-foundation-EmitScansInFlow-gated-discharge**
             (landed 2026-05-02, manifest entry
             `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated-discharge`):
             discharged `emit_scans_in_flow_seq_gated_sorry` and
             `emit_scans_in_flow_map_gated_sorry` by extending
             `scanNextToken_flow_open_nested_pkPush` and
             `scanNextToken_flow_open_mapping_nested_pkPush`
             with two new conjuncts each: `s'.pendingKeyStack =
             s.pendingKeyStack.push (some s.pendingKeys.size)`
             (push-shape) and `(s'.simpleKeyStack.back?.getD {}).possible
             = true` (top-of-stack possible).  Inline discharges
             in `emit_scans_in_flow` seq/map: re-call the pkPush
             variant under the gate, identify with the existing
             `s₁` via `scanNextToken` determinism + `subst`, then
             chain through body `pks` / `stack` preservation
             (h_pks₂ / h_stack₂) and close-side restore
             (_h_pka_restore₃ / _h_sk_restore₃).  Two sorry'd
             helpers `emit_scans_in_flow_{seq,map}_gated_sorry`
             removed.  Sorry count: 13 → 11.
          5. ✓ **C-foundation-EmitScansInFlow-discharge-colon**
             (landed 2026-05-02 as
             `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon`):
             discharged `emitPairList_body_size_pkRec_through_colon_sorry`
             via inline `pkResolve` + determinism + `pkRec_size_compose`
             chain.  Added `s.simpleKeyAllowed = true` precondition to
             `EmitPairListScansInFlow`; extended
             `scanNextToken_flow_open_mapping_nested` and
             `_init` with `s'.simpleKeyAllowed = true` (post-`{`
             record-update); extended `scanNextToken_flow_comma`
             with `s'.simpleKeyAllowed = true` (post-`,`
             scanFlowEntry record-update);
             extended `scanNextToken_preprocess_flow_ws1` with
             `s₁.simpleKeyAllowed = s.simpleKeyAllowed`
             (skipToContent passthrough); extended
             `scanNextToken_flow_value_pkResolve` with
             `s'.pendingKeyStack = s.pendingKeyStack`.  Inline
             discharges in `emitPairList_scans_nonempty` (singleton
             + cons): re-call pkResolve under gated facts (h_lt_pk_s1,
             h_pka_eq, h_skp_eq from `_h_gated₁ h_ska`) +
             `h_ska₁ : s₁.simpleKeyAllowed = false`, identify
             with the existing s₂ via determinism + `subst`, use
             `h_pks_other_pk` (j ≠ i) + `_h_pkRec₁` for prefix
             preservation, compose via `pkRec_size_compose` chain
             through ws1 → value (→ comma → ws1 → IH in cons).
             Cascading consumer updates: `emitPairList_body_filtered_characterization`,
             `emitPairList_chain_first_pkShape`,
             `emitPairList_body_linearise_characterization` each
             gain `h_ska` threaded through.  Sorry count: 11 → 10.
          6. ✓ **C-foundation-EmitScansInFlow-preservation-chain**
             (landed 2026-05-02 as
             `J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-preservation-chain`):
             discharged `scanDoubleQuoted_preserves_pendingKeyStack_sorry`
             by building the parallel `_preserves_pendingKeyStack`
             chain through the quoted-scalar machinery
             (`emitAt`, `collectHexDigitsLoop`, `parseHexEscape`,
             `processEscape`, `skipBlankLinesLoop`,
             `foldQuotedNewlinesLoop`, `foldQuotedNewlines`,
             `collectDoubleQuotedLoop`, `scanDoubleQuoted` — 9
             new lemmas in `Proofs/Scanner/ScannerCorrectness.lean`),
             mechanically mirroring the existing
             `_preserves_simpleKeyStack` chain.  Removed the
             sorry'd helper + docstring in EmitterScannability;
             updated the call site at `scanNextToken_flow_scanDoubleQuoted`
             to use `ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeyStack`
             directly.  Sorry count: 10 → 9.
          The original "~1 step" estimate (now refined to 6
          sub-steps in body-C foundation: defns-helpers-size +
          defns-prove + stack-restore + gated + gated-discharge
          + discharge-colon + preservation-chain) underestimated
          the helper-level preservation work plus the stack-restore
          machinery.  With **discharge-colon** and
          **preservation-chain** landed (sorry count 9), the
          body-C foundation is fully discharged; **C-compose**
          (~0.5–1 step, mechanical) is now unblocked.
        * ✓ **C-compose (body-C composition)** [done 2026-05-02 as
          `J.4.2.b-2d-key-chain-Part2-body-C-compose`]: extended
          `EmitPairListScansInFlow` with a first-pair resolved-key
          conjunct of shape `pairs ≠ [] → ∃ (h : s.pendingKeys.size <
          s'.pendingKeys.size), s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx
          = s.tokens.size ∧ s'.pendingKeys[s.pendingKeys.size].kind
          = .keyOnly`.  Re-proved `emitPairList_scans_nonempty`
          (singleton + cons cases) by binding the resolved-entry
          conjunct from `scanNextToken_flow_value_pkResolve` (slot
          15) and the insertBeforeIdx-equality from the gated A1
          push, then chaining `(insertBeforeIdx, kind)` preservation
          through ws1 → value → in cons also comma → ws1 → IH.
          No new helper `scanNextToken_flow_comma_pkPreserve`
          needed: the existing `scanNextToken_flow_comma`'s pkRec
          conjunct already covers preservation at j < s_v.size.
          Threaded the conjunct through
          `emitPairList_body_filtered_characterization` as Part (4)
          and consumed it directly in
          `emitPairList_body_linearise_characterization` Part (2),
          specializing the index to `0` via type-level `▸` rewrite
          under `h_pks_empty`.  **Removed** the
          `emitPairList_chain_first_pkShape` sorry'd stub entirely.
          Sorry count: 9 → 8.  This **closes the body-C umbrella**.
   - **2d-key-chain-Part3 (after-flowEntry splice locator)**: for each
     outer-level flowEntry at position `k` in
     `linearise s'.tokens s'.pendingKeys`, supply
     `(j, p, acc)` with `acc.size = k + 1`,
     `linearise s'.tokens s'.pendingKeys
       = linearise.go s'.tokens s'.pendingKeys j p acc`,
     `pks[p].insertBeforeIdx ≤ j`, and `pks[p].kind = .keyOnly`.

     **Status snapshot (as of 2026-05-02, sorry count 8):** Part3 is
     **scope-investigated and decomposed** into a multi-cadence
     cascade.  Original "~1–2 cadence steps" estimate underestimated
     three distinct technical challenges (see manifest entry
     `J.4.2.b-2d-key-chain-Part3-scope-investigation`):
     (a) Non-contiguous outer pendingKey indices `q_i =
     s_(i,pre).pendingKeys.size` (depends on dynamic value structure,
     not predictable as `s.pendingKeys.size + i`);
     (b) Filtered → linearise position mapping with nested-value
     splice contributions;
     (c) Walk-state construction at outer flowEntries — needs a NEW
     foundation lemma in `Proofs/Scanner/ScannerLinearise.lean`
     analogous to Foundation A's prefix-walk but stopping
     intermediately at each outer flowEntry copy.

     Decomposed sub-steps (cadence-sized; refined estimate ~5–6
     cadence steps total):

     1. ✓ **Part3-scope-investigation** [done 2026-05-02 as
        `J.4.2.b-2d-key-chain-Part3-scope-investigation`]: documented
        the three challenges (a-c) above + identified that
        `emitPairList_body_filtered_characterization` Parts (1)/(2)/(3)
        sorries are dead/incorrect (filtered claims `.key` tokens but
        `.key` is only produced by `scanKey`/`?` indicator, not
        `:`-resolution), proposed the per-pair locator shape, and
        sized the cascade.  Sorry count unchanged at 8.

     2. ✓ **Part3-locator-shape** [done 2026-05-02 as
        `J.4.2.b-2d-key-chain-Part3-locator-shape`]: chose **option (i)
        array form** for the new per-pair locator conjunct on
        `EmitPairListScansInFlow`.  Final shape (added by sub-step 3
        below): under `pairs ≠ []`,
        `∃ (qs : Array Nat) (h_size : qs.size = pairs.length)
          (h_pos : 0 < qs.size),
          qs[0]'h_pos = s.pendingKeys.size
          ∧ (∀ i (h : i < qs.size),
              ∃ (h_lt : qs[i]'h < s'.pendingKeys.size),
                (s'.pendingKeys[qs[i]]'h_lt).kind = .keyOnly)
          ∧ (∀ i j (hi : i < qs.size) (hj : j < qs.size),
              i < j → qs[i]'hi < qs[j]'hj)`.
        Cons-case construction: `qs = #[s.pendingKeys.size] ++
        qs_tail` (IH's array on the tail under `s_pp`); singleton:
        `qs = #[s.pendingKeys.size]`.  `insertBeforeIdx` is NOT in
        the conjunct (sub-step 5 derives `pks[qs[i]].insertBeforeIdx
        ≤ j_i` from the saveSimpleKey monotonicity invariant); the
        existing first-key conjunct (added by C-compose) is RETAINED
        alongside (avoids refactoring 3 consumer sites).
        See manifest for the rejected (ii)/(iii) candidates and the
        rationale.  Sorry count unchanged at 8.

     3. ✓ **Part3-extend-EmitPairListScansInFlow-per-pair** [done
        2026-05-02 as `J.4.2.b-2d-key-chain-Part3-extend-EmitPairListScansInFlow-per-pair`]:
        extended the `EmitPairListScansInFlow` predicate with the
        per-pair locator conjunct (option (i) array form), gated on
        `pairs ≠ []`.  Re-proved `emitPairList_scans_empty` (vacuous
        discharge: `fun h_ne => absurd rfl h_ne`) and
        `emitPairList_scans_nonempty` (singleton: `qs =
        #[s.pendingKeys.size]`; cons: `qs = #[s.pendingKeys.size] ++
        qs_tail` from IH on the tail under `s_pp`).  Restructured both
        non-empty branches to pre-derive shared facts
        (`h_lt_s_send`, `h_kd_s_end`, `h_ib_s_end`) BEFORE the trailing
        `refine`, so the new Part3 conjunct's bullet can reuse them
        alongside the existing first-key conjunct's bullet (without
        bullet-scope variable shadowing).  Cons-case strict-monotonicity:
        seam `qs[0] < qs[1]` from `h_lt_s_spp : s.pendingKeys.size <
        s_pp.pendingKeys.size` (head pair's gated A1 push, preserved
        through `:`/value/comma/ws₁ to `s_pp`); within `qs_tail` from
        IH's strict-mono.  Index manipulation via standard
        `Array.size_append`, `Array.getElem_append_left` (i = 0),
        `Array.getElem_append_right` (i ≥ 1).  Updated 3 destructure
        sites (recursive IH ~9816, mapping ~10295, filtered-char
        ~11873); the 4th candidate (`scanFiltered_exists_emit_aux`
        ~10518) uses anonymous-`_` placeholders that auto-absorb the
        new conjunct via residual conjunction.  `decide` on
        `0 < (#[s.pendingKeys.size]).size` fails ("free variables")
        because Lean refuses to fully reduce `Array.size #[x]` when
        `x` is opaque; worked around via `h_size_one ▸ Nat.zero_lt_one`
        (the `(#[x] : Array Nat).size = 1 := rfl` equation rewrites the
        target to `0 < 1`).  Sorry count unchanged at 8 (build
        replays 78/453 EmitterScannability jobs; total 453).

     4. ✓ **Part3-thread-body-filtered-char** [done 2026-05-02 as
        `J.4.2.b-2d-key-chain-Part3-thread-body-filtered-char`]:
        threaded the new per-pair conjunct through
        `emitPairList_body_filtered_characterization`'s conclusion
        as Part (5) (after the existing Part (4) from C-compose).
        **Conjunct shape:** identical to the
        `EmitPairListScansInFlow` Part3 conjunct (re-stated rather
        than wrapped, so consumers don't need to re-invoke
        `emitPairList_scans_nonempty`); under `pairs ≠ []`,
        `∃ (qs : Array Nat) (_h_size : qs.size = pairs.length)
        (h_pos : 0 < qs.size), qs[0]'h_pos = s.pendingKeys.size ∧
        ⟨per-i keyOnly readout⟩ ∧ strict-monotone-qs`.  **Discharge:**
        the destructure of `h_scan` already exposed `_h_first_qs`
        from the J.4.2.b-2d-key-chain-Part3-extend Sub-step (3); the
        only edit was renaming `_h_first_qs` → `h_first_qs` and
        appending `h_first_qs h_ne` to the closing `refine`'s
        anonymous constructor (no proof body change beyond binding
        rename).  **Destructure sites updated:**
        `emitPairList_body_linearise_characterization` ~12120 (added
        slot `_h_first_qs` after `h_first_key`); Tier 1
        `scanFiltered_emitMap_nonempty_structure` ~12459 (added slot
        `_h_body_first_qs` after `_h_body_first`).  Both are unused
        at this layer — sub-step 6 (Part3-final-discharge) is what
        consumes them via the linearise wrapper's Part (3) sorry.
        Sorry count unchanged at 8 (8 sorries at lines 11325, 11734,
        11943, 12088, 12222, 12445, 13167, 13206; 57/57 EmitterScannability
        jobs green).

     5. ✓ **Part3-walk-locator-foundation** [done 2026-05-02 as
        `J.4.2.b-2d-key-chain-Part3-walk-locator-foundation`]: added five
        new declarations in `Proofs/Scanner/ScannerLinearise.lean`:
        - `linearise_go_step_splice` / `linearise_go_step_copy` (one-step
          unfoldings of `linearise.go`, companions to the existing
          `linearise_go_step_token`).
        - `linearise_go_walk_eq` (workhorse): given a transport equation
          at state `(j, p, acc)` and a target `(j', p', acc')` with the
          two key conditions — **in-range** (`pks[r].insertBeforeIdx ≤ j'`
          for all `r ∈ [p, p')`) and **barrier** (`pks[p'].insertBeforeIdx
          ≥ j'` if `p' < pks.size`) — derives the transport equation at
          `(j', p', acc')`.  Proof: induction on the lex-measure
          `(j' - j) + (p' - p)`; each `linearise.go` step either fires a
          splice or copies a token, decreasing the measure by 1.
        - `linearise_go_walk_eq_top` (top-level wrapper, absorbs the
          lex-measure argument).
        - `linearise_go_walk_size`: derives `acc'.size + (tokens.size - j')
          + pendingExpandSumFrom pks p' = acc.size + (tokens.size - j)
          + pendingExpandSumFrom pks p` from the walk equation, by
          equating `linearise_go_size` on both sides.
        - `linearise_walk_at_kth_resolved_splice` (the Blueprint's named
          lemma): per `i < qs.size`, the linearised output has `.key` at
          position `pks[qs[i]].insertBeforeIdx + (pks.foldl ... 0 0
          qs[i])`.  The `prefixSum_i = pks.foldl 0 0 qs[i]` term accounts
          for *all* prior pending-entry expansions — including nested
          inner-mapping `.keyOnly` keys — without restricting the kinds
          of non-`qs` entries.  This makes the lemma directly usable in
          the consumer (sub-step 6) without the nested-mapping complication
          flagged in the original plan.

        **Key design choice (better than the originally-sketched
        induction):** the walk-state equation lets us jump *directly*
        from `(0, 0, #[])` to `(j_i, qs[i], acc)` for any `i`, without
        visiting intermediate splices.  No induction-on-`i` is needed
        in `linearise_walk_at_kth_resolved_splice` itself — the
        induction is implicit in `linearise_go_walk_eq` (over the
        lex-measure).  The "subsidiary lemma about `.unresolved` having
        zero expansion" is also unnecessary: `linearise_go_walk_eq`
        handles all kinds uniformly, and the position formula uses the
        cumulative `expandKind` sum (foldl), so `.unresolved`
        contributions are correctly counted as 0 without a special case.

        **Hypotheses required for the consumer:**
        - `h_qs_lt`, `h_qs_kind`, `h_qs_mono` (already established in
          `EmitPairListScansInFlow`'s Part3 conjunct).
        - `h_idx_mono`: save-time monotonicity of `pks` (chain-side
          invariant — likely needs to be exposed via a strengthened
          chain endpoint statement).
        - `h_idx_le`: every `pks[p].insertBeforeIdx ≤ tokens.size`
          (chain-side invariant — likely already exposed via Path C
          monotonicity).

        Sorry count unchanged at 8 (8 sorries at lines 11325, 11734,
        11943, 12088, 12222, 12445, 13167, 13206; 57/57 EmitterScannability
        jobs green).

     6. **Part3-final-discharge** (split into 6a + 6b — bridge sub-cadence
        flagged in original plan materialised; 6a in tree as of 2026-05-02):
        - 6a. ✓ **Part3-final-discharge-bridge-6a (chain-side)** [done
          2026-05-02]: extended `EmitPairListScansInFlow`'s per-pair conjunct
          with the predecessor-flowEntry fact (for each `i ≥ 1`,
          `s'.tokens[pks[qs[i]].insertBeforeIdx - 1].val = .flowEntry`).
          Re-proved `emitPairList_scans_empty` (vacuous) and
          `emitPairList_scans_nonempty`'s singleton (vacuous: only `i = 0`).
          Cons case decomposes the new conjunct on `i = j + 1`, `j < qs_tail.size`:
          for `j ≥ 1` the IH's predecessor-flowEntry conjunct discharges directly;
          for `j = 0` (outer `i = 1`) the predecessor is the `.flowEntry` pushed
          by the comma step (`s_v → s_c`), persisted through ws1
          (`s_pp.tokens = s_c.tokens`) and lifted across the IH chain
          (`s_pp → s_end`).  Extended `scanNextToken_flow_comma`'s output
          with `(s'.tokens.size = s.tokens.size + 1) ∧
          (∀ h_lt, (s'.tokens[s.tokens.size]'h_lt).val = .flowEntry)`
          (proof: chase tokens through advance/record-update/emit/saveSimpleKey/
          allowDirectives wrappers, all preserve tokens except the single
          `.flowEntry` push).  Threaded through
          `emitPairList_body_filtered_characterization`'s conclusion (Part 5
          extended in-place, no new conjunct shape).  Two existing
          `scanNextToken_flow_comma` callers updated with one extra `_`
          slot each.  Three existing per-pair-conjunct destructure sites
          (recursive IH ~9914, mapping ~10528, filtered-char ~12015,
          Tier 1 emitMap ~12598) auto-absorb the new sub-conjunct (single
          `∃` binding).  **Sub-task 6a-i1-lift sorry'd at line 9543** in
          the cons case `j = 0` branch: the lift through the IH chain
          requires `SimpleKeyAboveFloor s_pp s_pp.tokens.size s_pp.flowLevel`
          (precondition for `FlowMonoChain_preserves_raw_prefix`), which
          depends on tracing `s_pp.simpleKey`/`simpleKeyStack` state through
          comma + ws1 — deferred to 6b alongside the linearise-side bridge.
          Sorry count: 8 → 9 (+1 from 6a-i1-lift).  Build green
          (453/453 jobs).
        - 6b. ✓ **Part3-final-discharge-bridge-6b (i1-lift discharge)** [partial,
          done 2026-05-02]: discharged the 6a-i1-lift sorry via a different
          route than originally planned.  Instead of establishing
          `SimpleKeyAboveFloor s_pp ... s_pp.flowLevel` (which would require
          tracing `s_pp.simpleKey`/`simpleKeyStack` state through comma + ws1),
          we added a Path C **unconditional** strict prefix preservation lemma
          (`scanNextToken_preserves_prefix_strict` + chain version
          `FlowMonoChain_preserves_existing_tokens`) leveraging the fact that
          post-cutover scanner is append-only on `tokens` (no `setIfInBounds`).
          The chain version takes only the `FlowMonoChain` itself (no
          `SimpleKeyAboveFloor` needed) — a strictly cleaner signature than
          `FlowMonoChain_preserves_raw_prefix`.  Cons case `j = 0` discharge:
          the comma's `.flowEntry` push (h_comma_push) is preserved through
          ws1 (`s_pp.tokens = s_c.tokens`) and lifted across the IH chain
          (`s_pp → s_end`) via `FlowMonoChain_preserves_existing_tokens` at
          index `s_v.tokens.size`.  Used a `generalize`+`subst` pattern to
          handle the dependent indexing in `s_pp.tokens[i]'h` substitution.
          Helper proofs: `dispatchBlockIndicators_preserves_prefix_strict`
          (mirror of legacy version, routing `:` through
          `scanValue_preserves_prefix_strict`) +
          `scanNextToken_preserves_prefix_strict` (mirror of
          `scanNextToken_preserves_prefix_of_skFloor`, dropping h_inv).
          **Sub-task 6b-bridge-inversion (sorry'd, deferred)**: discharging
          Part (3) of `emitPairList_body_linearise_characterization` requires
          inverting from an arbitrary outer-level flowEntry's linearise
          position `k` to a pair index `i ≥ 1` such that `k + 1 =
          pks[qs[i]].insertBeforeIdx + (pks.foldl 0 0 qs[i])`.  This needs
          bracket-balance accounting to enumerate all outer-level flowEntries
          and rule out inner-flow contributions.  Documented in-place at the
          Part (3) sorry comment (line ~12535).  Sorry count: 9 → 8 (closes
          6a-i1-lift; Part (3) deferred).  Build green (453/453 jobs).
        - 6c-i. ✓ **Part3-final-discharge-bridge-6c-i (forward walk lemma)**
          [done 2026-05-02]: added
          `linearise_walk_at_kth_predecessor_token` to
          `ScannerLinearise.lean` — under save-time strict monotonicity of
          `pks` at the prefix `[0, q)` (i.e., every preceding entry has
          `insertBeforeIdx + 1 ≤ pks[q].insertBeforeIdx`, reflecting at-
          least-one-token-between-saves), the linearise output's element
          at position `pks[q].insertBeforeIdx - 1 + (pks.foldl 0 0 q)`
          equals `tokens[pks[q].insertBeforeIdx - 1]`.  Companion to the
          existing `linearise_walk_at_kth_resolved_splice` (which reads
          `.key` at the splice's POST-fire position): combining the two
          with the chain-side `tokens[pks[qs[i]].insertBeforeIdx - 1] =
          .flowEntry` (from `h_first_qs`'s predecessor-flowEntry conjunct)
          yields the structural pattern `.flowEntry → .key` at consecutive
          linearise positions, the forward direction of Part (3)'s bridge.
          Proof: walk to `(pks[q].insertBeforeIdx - 1, q, acc')` via
          `linearise_go_walk_eq_top` (in-range from strict-monotonicity,
          barrier from `j-1 ≤ j` reflexivity); take a copy step
          (`linearise_go_step_copy`) advancing to `(pks[q].insertBeforeIdx,
          q, acc'.push tokens[..])`; pin `acc'.size = (j-1) + foldlSum_q`
          via `linearise_go_walk_size`; apply `linearise_go_getElem_lt_acc`
          to read off the predecessor token at `acc'.size`.  Build green
          (453/453 jobs).  Sorry count unchanged (forward lemma is
          reusable infrastructure; consumed in 6c-ii's discharge).
        - 6c-ii. **Part3-final-discharge-bridge-inversion** — decomposed
          across α/β/γ:
          - 6c-ii-α. ✓ **bracket-balance algebra helpers** [done
            2026-05-02]: added three reusable infrastructure lemmas to
            `EmitterScannability.lean` (right before the J.4.2.b-2d
            section header):
            * `expandKind_flowBracketDelta_zero` — splice tokens
              (`.key`, `.blockMappingStart`) have `flowBracketDelta =
              0`.  Trivial corollary of `expandKind_val_neutral`.
            * `flowBracketBalance_push_extend` — pushing one token to
              `acc` and extending the balance range by 1 picks up the
              new token's `flowBracketDelta`.  Built on
              `flowBracketBalance_compose` + `_push` + `_single`.
            * `flowBracketBalance_splice_unchanged` — appending
              `expandKind e` to `acc` leaves bracket balance unchanged
              over the extended range.  Proof by case analysis on
              `e.kind`, applying `flowBracketBalance_push_extend` 0/1/2
              times.
            These are the building blocks for 6c-ii-β's preservation
            induction.  Build green (453/453 jobs).  Sorry count
            unchanged at 8 (helpers are reusable infrastructure;
            consumed in 6c-ii-β).
          - 6c-ii-β. ✓ **bracket-balance preservation lemma** [done
            2026-05-02]: proved the parallel induction
            `linearise_go_walk_flowBracketBalance` over `linearise.go`'s
            lex-measure (in `EmitterScannability.lean`, right after
            6c-ii-α's algebra helpers).  Existential form ("∃ extra,
            walk-eq ∧ balance-eq"): the walk from `(j, p, acc)` to
            `(j', p', acc ++ extra)` produces an `extra` whose bracket
            balance over `[acc.size, acc.size + extra.size)` matches
            `flowBracketBalance tokens j j'`.  Cases mirror
            `linearise_go_walk_eq`: (n=0) `extra = #[]`, both sides
            zero; (splice step) `flowBracketBalance_splice_unchanged`
            keeps the splice piece at zero (via
            `flowBracketBalance_compose` + `flowBracketBalance_append_left`
            on the `(acc ++ expandKind pks[p]) ++ extra'` reshape), IH
            absorbs the rest; (copy step) `flowBracketBalance_push_extend`
            picks up `flowBracketDelta tokens[j].val`, matched on the
            RHS by `flowBracketBalance_compose tokens j (j+1) j' +
            flowBracketBalance_single`; (p ≥ pks.size case) duplicate
            of copy with `linearise_go_step_token` instead of `_step_copy`.
            Required new helper `flowBracketBalance_append_left` (general
            append-left invariance, generalises `_push`) plus a
            `linearise_go_walk_flowBracketBalance_top` wrapper that
            absorbs the lex-measure argument.  See manifest entry
            `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-β`
            for tactic notes (Array.append_assoc / Array.size_append are
            no-arg theorems, not functions; the trailing `rfl` after
            `flowBracketBalance_single` bridges `tokens[j].val` ↔
            `tokens.toList[j].val` defeq).  Build green (453/453 jobs).
            Sorry count unchanged at 8 (preservation lemma is reusable
            infrastructure consumed in 6c-ii-γ).
          - 6c-ii-γ. **inversion enumeration + Part (3) discharge** —
            *further decomposed* into three sub-steps after scope
            investigation revealed that the chain-side `qs` enumeration
            currently exposed by `EmitPairListScansInFlow` lacks the
            *exhaustiveness* fact needed to invert `k → i`.  This is a
            ghost-predicate gap, not just a proof-bookkeeping issue:
            the chain knows that the only outer-level `.flowEntry`
            tokens above `s.tokens.size` are pair separators, but the
            predicate doesn't expose this.  Decomposed:
            - 6c-ii-γ-1. ✓ **ghost-predicate strengthening** [done
              2026-05-03]: extended `EmitPairListScansInFlow`'s qs-
              locator existential (and the threaded conjunct in
              `emitPairList_body_filtered_characterization`) with an
              *outer-flowEntry exhaustiveness* sub-claim — for every
              `kk` in `[s.tokens.size, s'.tokens.size)` with
              `s'.tokens[kk] = .flowEntry` at outer level, there
              exists `0 < i < qs.size` with `kk + 1 =
              pks[qs[i]].insertBeforeIdx`.  Discharge in
              `emitPairList_scans_nonempty` (singleton + cons cases)
              sorry'd pending 6c-ii-γ-2.  Build green (453/453 jobs).
              Sorry count: 8 → 10 (+2 from chain-side stub
              discharges).  See manifest entry
              `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-1`.
            - 6c-ii-γ-2a. ✓ **EmitScansInFlow strengthening (predicate-
              level)** [done 2026-05-03]: added a single bundled conjunct
              `(flowBracketBalance s'.tokens s.tokens.size s'.tokens.size
              = 0 ∧ ∀ kk in [s.tokens.size, s'.tokens.size), s'.tokens[kk]
              = .flowEntry → balance ≥ 1)` to `EmitScansInFlow`.
              Updated all 6 destructure sites in `emitList_scans_nonempty`
              + `emitPairList_scans_nonempty` to extract the bundled
              hypothesis.  Updated all 3 cases in `emit_scans_in_flow`
              (scalar/sequence/mapping) to provide the bundled conjunct
              via `refine ⟨..., ?_⟩` slots; **discharge sorry'd** as
              sub-tasks 6c-ii-γ-2c (scalar) + 6c-ii-γ-2d (sequence/
              mapping).  Build green (453/453 jobs).  Sorry count:
              10 → 13 (+3 from emit_scans_in_flow case sorrys; chain-side
              sorrys at lines 9940/10542 *not yet discharged* — see
              6c-ii-γ-2b).  See manifest entry
              `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2a`.
              **Architectural finding**: the discharge in `emit_scans_in_flow`
              requires (i) per-leaf token-push lemmas exposing
              `s'.tokens.size = s.tokens.size + 1` and the new token's
              `val` for scalar (and similarly for `[`/`]`/`{`/`}`), and
              (ii) a `flowBracketBalance` chain-extension lemma showing
              that appending tokens past `hi` preserves balance over
              `[lo, hi)`.  These foundational pieces are missing and
              motivate the γ-2c/d split.
            - 6c-ii-γ-2b. ✓ **discharge chain-side γ-1 sorrys using new
              conjunct** done 2026-05-03: in `emitPairList_scans_
              nonempty`, both singleton (line ~9963) and cons (line ~10567)
              chain-side γ-1 sorrys discharged.  Singleton: chain `s →
              s_end` is `emit(p.1) → ":" → ws → emit(p.2)`; case-split on
              `kk` (key range / colon / ws / value range), each case
              contradicts the outer-balance-zero premise via the bundled
              `h_balfacts_*` exhaustiveness conjunct or the colon's
              `.value ≠ .flowEntry`.  Cons: same per-segment decomposition
              + comma push at `kk = s_v.tokens.size` matches `qs[1] =
              qs_tail[0] = s_pp.pendingKeys.size` (with `pks[qs[1]]
              .insertBeforeIdx = s_pp.tokens.size = kk + 1`), and tail-
              range `kk ≥ s_pp.tokens.size` applies IH's `_h_exh_t`.
              **Helper added:** `flowBracketBalance_FlowMonoChain` (balance
              preserved when chain extends array past `hi`; proven via
              `List.drop_take` slice-equality + `FlowMonoChain_preserves_
              existing_tokens`; ~30 lines, inline proof, no sorry).
              **`scanNextToken_flow_value` strengthened** to expose
              `s'.tokens.size = s.tokens.size + 1` and `s'.tokens[s.tokens.
              size].val = .value` (mirrors `scanNextToken_flow_comma`'s
              comma-push conjunct).  **Sorry count: 13 → 11** (-2 chain-
              side, no intermediate stubs added).  See manifest entry
              `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2b`.
            - 6c-ii-γ-2c. ✓ **discharge scalar case in `emit_scans_in_flow`**
              [done 2026-05-03]: strengthened `scanDoubleQuoted_flow_ok` and
              `scanNextToken_flow_scanDoubleQuoted` with bundled
              `(s'.tokens.size = sc.tokens.size + 1 ∧ ∀ h_lt,
              s'.tokens[sc.tokens.size].val = .scalar content .doubleQuoted)`
              conjunct, threaded through the inner `s_after.emitAt
              sc.currentPos (.scalar ...)` push and the surrounding
              `setPendingKeyEndLine` wrap (tokens-preserving).  Discharged
              the scalar sorry in `emit_scans_in_flow` via the chain
              `s_state.tokens → s_ad.tokens (preserved) → s_dq.tokens
              (push)` pattern.  Balance: single `.scalar` token has
              `flowBracketDelta = 0` (proved by `flowBracketBalance_single`
              + `rfl`).  No-outer-flowEntry: the only valid `kk` in range
              is `s_state.tokens.size`, where the token is `.scalar`,
              contradicting `.val = .flowEntry` (proved by `nofun`).
              **Lean-tactic notes:** `decide` fails on
              `flowBracketDelta (.scalar s.content ...)` due to free
              variable `s.content`; use `rfl` (the catch-all `_ => 0` arm
              reduces definitionally).  Similar issue with
              `(.scalar ... = .flowEntry)`: use `nofun` instead of
              `(by decide)`.  Sorry count: 11 → 10.  Build green
              (453/453 jobs).  See manifest entry
              `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2c`.
            - 6c-ii-γ-2d. ✓ **discharge sequence + mapping cases**
              [done 2026-05-03]: strengthened `EmitListScansInFlow` and
              `EmitPairListScansInFlow` with bundled (balance = 0 ∧
              flowEntry → ≥ 0) conjuncts; strengthened the 4 nested
              open/close theorems (`scanNextToken_flow_open_nested`,
              `scanNextToken_flow_close_seq_nested`,
              `scanNextToken_flow_open_mapping_nested`,
              `scanNextToken_flow_close_mapping_nested`) with token-push
              facts (`s'.tokens.size = s.tokens.size + 1` + value at
              index `s.tokens.size` = `.flowSequenceStart`/End/MappingStart/End).
              Discharge in `emit_scans_in_flow`'s sequence + mapping
              cases via `flowBracketBalance_compose` of `[` push
              (delta +1) + body (= 0) + `]` push (delta -1) = 0;
              outer flowEntry → ≥ 1 from `[`/`{` push (+1) + body's
              flowEntry → ≥ 0.  Re-proved `emitList_scans_empty`/
              `_nonempty` (full discharge) + `emitPairList_scans_empty`/
              `_nonempty` singleton (full discharge); cons-case
              bundled balance for `emitPairList_scans_nonempty` is the
              **intermediate stub** allowed by Blueprint (deferred to
              follow-up γ-2d-ii).  Sorry count: 10 → 9 (-2 outer
              discharges, +1 emitPairList cons stub).  Build green
              (453/453 jobs).  See manifest entry
              `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6c-ii-γ-2d`.
            - 6c-ii-γ-3. **discharge Part (3) using strengthened
              predicate**: translate the linearise outer-level
              condition to `s'.tokens` via 6c-ii-β; apply the new
              exhaustiveness conjunct to identify pair index `i ≥ 1`;
              walk to the matching `(j, p, acc)` state; conclude
              via `linearise_splice_keyonly_at_index`.  Sorry count:
              8 (or 9) → 7 (or 8).

     This **closes 2d-stub** — no further wrap needed once Part3-final
     lands.  Filtered-shape Parts (2)/(3) sorries (lines 11903, 11905
     in `emitPairList_body_filtered_characterization`) and Part (1)
     sorry (line 11897) remain as separate cleanup; since they're
     unused by the linearise wrapper (which consumes only Part (4)),
     they may be restated to expose per-pair pendingKey facts (folded
     into Part3-thread sub-step 4 if convenient) or simply removed.
3. **Stitch the cascade** into `scanFiltered_emitSeq_nonempty_structure`
   (currently line 9844 sorry) and `scanFiltered_emitMap_nonempty_structure`
   (currently line 10070 sorry), discharging both Tier 1 cascade sorries
   using the J.4.2.c family of positional lemmas + the J.4.2.b-pkwi
   chain-endpoint invariant + the linearise-shape body characterizations
   from item (2).  Sequencing: the seq-side cascade can land as soon as
   2c is in tree (already done); the map-side cascade requires
   2d-key-chain-Part2-body + 2d-key-chain-Part3 (the final discharge of
   Parts (2)/(3) inside the 2d-stub theorem, now that Foundations A and
   B + the 2d-key-prep precondition refinement + the 2d-key-chain-Part2
   stub are in tree) to be in tree first.  The map-side cascade also
   needs to expose `s'.pendingKeys = #[]` from
   `scanNextToken_flow_open_mapping_init`'s output (a small structural
   fact about the post-`{` state) to satisfy the wrapper's
   `h_pks_empty` precondition.  Estimate: 1-2 cadence steps once
   (2c, 2d-key-chain-Part2-body, 2d-key-chain-Part3) are in tree.

The remaining chunk (items 2 + 3) is the substantial leg of J.4 — but
the breakdown above lets each substep land in cadence-size, with the
positional family (J.4.2.c-prefix / -pos1 / -pos2) and the chain-endpoint
invariant (J.4.2.b-pkwi) already in place to support them.

**Concrete next steps (in order, as of 2026-05-03, sorry count 9):**

1. **2d-key-chain-Part3** (after-flowEntry splice locator; refined
   ~14–15 cadence steps; scope-investigation done 2026-05-02,
   locator-shape done 2026-05-02, extend-per-pair done 2026-05-02,
   thread-body-filtered-char done 2026-05-02, walk-locator-foundation
   done 2026-05-02, final-discharge-bridge-6a done 2026-05-02,
   final-discharge-bridge-6b/i1-lift done 2026-05-02,
   final-discharge-bridge-6c-i/forward-walk-lemma done 2026-05-02,
   final-discharge-bridge-6c-ii-α/bracket-balance-algebra-helpers done
   2026-05-02, final-discharge-bridge-6c-ii-β/bracket-balance-preservation
   done 2026-05-02, final-discharge-bridge-6c-ii-γ-1/ghost-predicate-
   strengthening done 2026-05-03, final-discharge-bridge-6c-ii-γ-2a/
   EmitScansInFlow-strengthening done 2026-05-03,
   final-discharge-bridge-6c-ii-γ-2b/chain-side-γ-1-discharge done
   2026-05-03, final-discharge-bridge-6c-ii-γ-2c/scalar-discharge done
   2026-05-03, final-discharge-bridge-6c-ii-γ-2d/seq+map-outer-discharge
   done 2026-05-03 with emitPairList cons stub) — Part3 is now decomposed
   into 16 cadence-sized sub-steps (sub-steps 1–5 + 6a + 6b + 6c-i +
   6c-ii-α + 6c-ii-β + 6c-ii-γ-1 + 6c-ii-γ-2a + 6c-ii-γ-2b + 6c-ii-γ-2c
   + 6c-ii-γ-2d ✓ done; 6c-ii-γ-2d-ii (emitPairList cons stub
   discharge) + 6c-ii-γ-3 remaining):
   - 2. ✓ **Part3-locator-shape** [done 2026-05-02]: chose option (i)
     array form `∃ (qs : Array Nat) (_h_size : qs.size = pairs.length)
     (h_pos : 0 < qs.size), qs[0] = s.pendingKeys.size ∧ ⟨per-i
     keyOnly⟩ ∧ strict-monotone-qs`, gated on `pairs ≠ []`.  Existing
     first-key conjunct retained (no consumer-site refactor).
     `insertBeforeIdx` deferred to sub-step 5.  See manifest entry
     `J.4.2.b-2d-key-chain-Part3-locator-shape` for the full shape +
     rejected (ii)/(iii) candidates.
   - 3. ✓ **Part3-extend-EmitPairListScansInFlow-per-pair** [done
     2026-05-02]: extended the predicate with the array conjunct
     and re-proved `emitPairList_scans_empty` (vacuous) and
     `emitPairList_scans_nonempty` (singleton + cons) under the
     new shape.  Restructured both non-empty branches to pre-derive
     shared first-pair facts before the trailing `refine` so the
     new bullet can reuse them alongside the existing first-key
     bullet.  Updated 3 explicit destructure sites (recursive IH
     ~9816, mapping ~10295, filtered-char ~11873); the
     `scanFiltered_exists_emit_aux` ~10518 site uses anonymous-`_`
     placeholders that auto-absorbed the new conjunct.  Build
     replays 78/453 EmitterScannability jobs.  Sorry count
     unchanged at 8.
   - 4. ✓ **Part3-thread-body-filtered-char** [done 2026-05-02]:
     threaded the new per-pair conjunct through
     `emitPairList_body_filtered_characterization`'s conclusion as
     Part (5).  Re-stated (not wrapped) so consumers don't need to
     re-invoke `emitPairList_scans_nonempty`.  Closing `refine`
     extended via existing destructure binding (`h_first_qs h_ne`);
     two consumer destructures updated (linearise wrapper ~12120
     and Tier 1 emitMap ~12459, both with `_`-prefixed unused
     slots).  Sorry count unchanged at 8.  See manifest entry
     `J.4.2.b-2d-key-chain-Part3-thread-body-filtered-char`.
   - 5. ✓ **Part3-walk-locator-foundation** [done 2026-05-02]:
     added `linearise_walk_at_kth_resolved_splice` to
     `Proofs/Scanner/ScannerLinearise.lean` along with five supporting
     declarations (`linearise_go_step_splice`,
     `linearise_go_step_copy`, `linearise_go_walk_eq`,
     `linearise_go_walk_eq_top`, `linearise_go_walk_size`).  Sub-step
     came in lighter than the original 1.5–2 step estimate because
     the walk-state equation lets us jump *directly* from `(0, 0,
     #[])` to `(j_i, qs[i], acc)` for any `i` — no induction-on-`i`
     needed.  The position formula uses `pks.foldl 0 0 qs[i]` to
     accommodate nested inner-mapping `.keyOnly` entries (no
     "non-`qs` are `.unresolved`" hypothesis required).  See manifest
     entry `J.4.2.b-2d-key-chain-Part3-walk-locator-foundation`.
     Sorry count unchanged at 8.
   - 6a. ✓ **Part3-final-discharge-bridge-6a (chain-side)** [done
     2026-05-02]: extended `EmitPairListScansInFlow`'s per-pair conjunct
     with a predecessor-flowEntry fact (for `i ≥ 1`,
     `s'.tokens[pks[qs[i]].insertBeforeIdx - 1].val = .flowEntry`),
     re-proved both the empty/singleton (vacuous) and cons cases.  Cons
     `j ≥ 1` discharges via the IH directly; cons `j = 0` lifts the
     comma's flowEntry push through ws1 + the IH chain — the lift is
     sorry'd (sub-task 6a-i1-lift) pending 6b's `SimpleKeyAboveFloor`
     trace.  Extended `scanNextToken_flow_comma`'s output with the
     comma push token equation; threaded through
     `emitPairList_body_filtered_characterization`.  Sorry count 8 → 9.
     See manifest entry `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6a`.
   - 6b. ✓ **Part3-final-discharge-bridge-6b (i1-lift discharge)**
     [done 2026-05-02]: discharged 6a-i1-lift via Path C unconditional
     prefix preservation (`scanNextToken_preserves_prefix_strict` +
     `FlowMonoChain_preserves_existing_tokens`), simpler than the
     originally-planned `SimpleKeyAboveFloor` route.  Sorry count 9 → 8.
     Linearise-side bridge inversion deferred to 6c.  See manifest entry
     `J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6b`.
   - 6c. **Part3-final-discharge-bridge-inversion** (~1-2 steps) ← *current
     next step*: build the forward walk lemma in `ScannerLinearise.lean`
     combining the walk-locator with the predecessor-flowEntry fact, then
     build the bracket-balance inversion that identifies, for every
     outer-level flowEntry at linearise position `k`, the unique pair
     index `i ≥ 1` such that `k + 1 = pks[qs[i]].insertBeforeIdx +
     (pks.foldl 0 0 qs[i])`.  Combine to discharge the Part (3) sorry
     in `emitPairList_body_linearise_characterization` (line ~12535).
     Sorry count 8 → 7.

   See open-bullet section's body decomposition (just above this
   "Concrete next steps") for full details on each sub-step.  This
   **closes 2d-stub** — no further wrap needed once Part3-final lands.

2. **Cascade stitching** (~1–2 cadence steps once Part3-final is in
   tree): discharge the seq-side cascade
   (`scanFiltered_emitSeq_nonempty_structure`) and the map-side
   cascade (`scanFiltered_emitMap_nonempty_structure`) using the
   J.4.2.c positional family + J.4.2.b-pkwi chain-endpoint invariant
   + the linearise-shape body characterizations.  Map-side also
   needs `s'.pendingKeys = #[]` exposed from
   `scanNextToken_flow_open_mapping_init`.  Sorry count 7 → 5 (or
   lower depending on how the remaining EmitterScannability declarations
   compose).  This **closes J.4** (the substantial leg).
3. **Remaining EmitterScannability sorries** (7 ↦ 0; cadence-sized
   sub-steps): the remaining sorries (`emitList_body_filtered_characterization`
   Parts 1/2/3; `emitPairList_body_filtered_characterization` Parts
   1/2/3 — likely restated or removed, see Part3 cascade notes; two
   `ParseFlowSeqOk`/`ParseEntryFlowMapOk` body characterizations;
   etc.) are independent of the body-C/Part3 chain and can land
   in any order once their respective parser-acceptance fuel
   bounds are in tree.

**J.3 final gate**: `lake build` green; sorry count 19 → 12
(2 cascade Cat C for J.4 cleanup + 10 Tier 2 EmitterScannability
declarations deferred to J.4 — line counts in the actual file may
report more depending on how nested-let/sorry occurrences are
counted by `grep`).  J.4.1 (helper) landed 2026-04-29 with sorry
count unchanged at 12 (infrastructure, no discharge).
J.4.2.c-prep (`linearise_push_eq_push_linearise`) landed 2026-04-29
with sorry count unchanged at 12 (infrastructure, no discharge).
J.4.2.c-pos1 (`linearise_second_eq_tokens_second`) landed 2026-04-29
with sorry count unchanged at 12 (infrastructure, no discharge).
J.4.2.b-pkwi (chain-endpoint `PendingKeysWellIndexed` helpers) landed
2026-04-30 with sorry count unchanged at 12 (infrastructure for the
cascade discharge, no sorry cleared).
J.4.2.c-pos2 (`linearise_secondLast_eq_tokens_last_inner`) landed
2026-04-30 with sorry count unchanged at 12 (infrastructure for the
cascade discharge, no sorry cleared).  This closes the J.4.2.c
positional family — index 0, 1, size-2, size-1 readouts on the
post-`streamEnd` linearised output are all in tree.
J.4.2.c-prefix (`linearise_prefix_eq_tokens_prefix`) landed 2026-04-30
with sorry count unchanged at 12 (infrastructure for the cascade
discharge, no sorry cleared).  Generalises `linearise_first_eq_tokens_first`
and the index-1 readout from `linearise_second_eq_tokens_second` into
a single arbitrary-prefix readout, so future cascade work can read off
any number of leading tokens uniformly.
J.4.2.b-2a (`AllUnresolved` predicate + Class A/B/C preservation
lemmas) landed 2026-04-30 with sorry count unchanged at 12
(infrastructure for the cascade discharge, no sorry cleared).
Establishes the "no resolutions fired" predicate as a named
definition with the algebraic-class machinery mirroring
`PendingKeysWellIndexed`, ready for chain-side propagation in 2a-chain
or 2c.
J.4.2.b-2a-chain (chain-side `AllUnresolved` propagation:
`AllUnresolved_init`, parametric `ScanChain.preserves_AllUnresolved`,
`AllUnresolved_of_chain_from_init`, `AllUnresolved_emit_streamEnd`)
landed 2026-04-30 with sorry count unchanged at 12 (infrastructure
for the cascade discharge, no sorry cleared).  Mirrors the PKWI
chain-side block; the chain induction is parametric in a per-action
preservation hypothesis to reflect that `scanValuePrepare`'s
`:`-resolution is the single break path — cascade consumers
discharge it scoped to the no-`:`-pair sub-class they target.
J.4.2.b-2a-discharge (per-action `AllUnresolved` preservation:
`scanValue_preserves_AllUnresolved` with sub-class hypothesis +
the four per-dispatcher `*_preserves_AllUnresolved` lemmas +
`preprocess_preserves_AllUnresolved` +
`scanNextToken_preserves_AllUnresolved`) landed 2026-04-30 with
sorry count unchanged at 12 (infrastructure for the cascade
discharge, no sorry cleared).  Discharges the parametric `h_step`
of `ScanChain.preserves_AllUnresolved` for the no-`:`-pair
sub-class — cascade consumers in 2c plug it in after sub-class
specialization (the hypothesis collapses to `c ≠ ':'` at every
preprocess output for flow seqs of scalars / nested flow seqs).
Closes the J.4.2.b-2a chain (predicate → chain induction →
per-action discharge); 2b/2c/2d remain.
J.4.2.b-2b (placeholder-free invariant: `NoPlaceholders` predicate
+ Class A/B preservation lemmas + chain-side propagation
`NoPlaceholders_init` / parametric `ScanChain.preserves_NoPlaceholders`
/ `NoPlaceholders_of_chain_from_init` /
`NoPlaceholders_emit_streamEnd`) landed 2026-04-30 with sorry
count unchanged at 12 (infrastructure for the cascade discharge,
no sorry cleared).  Companion to J.4.2.b-2a/-2a-chain — provides
the second of the two hypotheses of
`linearise_eq_filter_no_resolutions` (the no-placeholder
hypothesis on `tokens`).  Unlike `AllUnresolved`'s break path, no
input sub-class restriction is needed: the J.2 step 5 cutover
removed every legacy `.placeholder` push, so the chain induction's
parametric `h_step` is dischargeable unconditionally — the
follow-up J.4.2.b-2b-discharge landing will provide the per-action
`scanNextToken_preserves_NoPlaceholders` that mirrors
`scanNextToken_preserves_AllUnresolved` (without the sub-class
hypothesis).
J.4.2.b-2b-discharge (per-action `NoPlaceholders` preservation:
generic `NoPlaceholders_extension` / `NoPlaceholders_extension_one`
helpers, primitive Class A leaves, indent helpers, per-scanner
`*_preserves_NoPlaceholders` lemmas + supporting
`*_new_token_not_placeholder` helpers, the four per-dispatcher
lemmas, `preprocess_preserves_NoPlaceholders`,
`allowDir_ite_preserves_NoPlaceholders`, top-level
`scanNextToken_preserves_NoPlaceholders`) landed 2026-04-30 with
sorry count unchanged at 12 (infrastructure for the cascade
discharge, no sorry cleared).  Closes the J.4.2.b-2b chain
symmetrically with J.4.2.b-2a → 2a-chain → 2a-discharge.
`scanNextToken_preserves_NoPlaceholders` is **unconditional** — no
sub-class hypothesis on the input character, since post-cutover
every scanner action either preserves `tokens` (Class A) or pushes
a single concrete non-`.placeholder` token (Class B).  Cascade
consumers in 2c plug `scanNextToken_preserves_NoPlaceholders`
directly into `ScanChain.preserves_NoPlaceholders` for any input
(no sub-class specialisation needed).  2c / 2d remain.
J.4.2.b-2c (linearise-shape variant of body characterization for the
no-resolution sub-class: `emitList_body_linearise_characterization`
in `Proofs/Output/EmitterScannability.lean`) landed 2026-04-30 with
sorry count unchanged at 12 (infrastructure for the cascade discharge,
no sorry cleared).  Wraps `emitList_body_filtered_characterization`
with three additional outputs: `AllUnresolved s'` (parametric in the
per-action discharge — caller plugs in
`scanNextToken_preserves_AllUnresolved` from J.4.2.b-2a-discharge under
the no-`:`-pair sub-class), `NoPlaceholders s'` (unconditional via
`scanNextToken_preserves_NoPlaceholders`), and the bridge equality
`linearise s'.tokens s'.pendingKeys = s'.tokens.filter p` from
`linearise_eq_filter_no_resolutions` (J.4.1).  Parts (1) and (2) of the
characterization are restated on `linearise s'.tokens s'.pendingKeys`
instead of `s'.tokens.filter p`, transported via `rw [h_lin_eq]` from
the filter-shape body characterization.  Cascade consumers in
`scanFiltered_emitSeq_nonempty_structure` can now read body content
tokens off the linearise-shape post-cutover bridge target using the
J.4.2.c positional family (`-pos1`, `-pos2`, `-prefix`) and the
`linearise_push_eq_push_linearise` (J.4.2.c-prep) `streamEnd` peeler.
Closes the linearise-shape seq-body sub-task; 2d (linearise-shape pair
body) and the cascade stitching (item 3) remain.
J.4.2.b-2d-stub (stub-level linearise-shape variant of body characterization
for the resolution case: `emitPairList_body_linearise_characterization`
in `Proofs/Output/EmitterScannability.lean`) landed 2026-04-30 with sorry
count **+2 in EmitterScannability** (11 → 13 raw `grep` occurrences;
in declaration-count terms: +1 new sorry-using declaration carrying two
stub sorries — first stub for Part (2) `linearise[old_sz].val = .key`,
second stub for Part (3) `linearise[k+1].val = .key` after outer-level
flowEntry).  The chain + 13 invariants + `n ≥ 3` + `NoPlaceholders s'`
are proven by wrapping `emitPairList_body_filtered_characterization` —
this is the first J.4.2.b landing that does NOT keep sorry count
unchanged, because the 2c transport pattern (`linearise = filter` bridge)
fails for the resolution case and the linearise-shape parts must be
proven directly (deferred to J.4.2.b-2d-key).  Carries the
chain side and structural invariants from the filter-shape body
characterization, derives `NoPlaceholders s'` unconditionally via
`scanNextToken_preserves_NoPlaceholders` (J.4.2.b-2b-discharge); states
linearise-shape Part (2) (`linearise[old_sz].val = .key`) and Part (3)
(`linearise[k+1].val = .key` after every outer-level flowEntry) on
`linearise s'.tokens s'.pendingKeys` directly.  No `linearise = filter`
bridge — the 2c transport pattern fails here because the `:` resolutions
splice `.key` tokens that are absent in the filter shape.  `AllUnresolved
s'` does NOT carry through (resolutions are by design here), so the
J.4.2.b-2a-chain propagation cannot be plugged in either.  The two
linearise-shape parts are sorry'd as the J.4.2.b-2d-key follow-up;
discharging them requires resolved-key splice analysis using the J.4.2.c
positional family + new pendingKey-aware linearise lemmas characterising
the position of the first `.keyOnly` splice and the post-flowEntry
splice, plus chain-side accounting of the post-execution
pendingKey extension shape (one `.keyOnly` per pair).  This sets up the
cascade-ready toolkit slot for `scanFiltered_emitMap_nonempty_structure`
to consume in item 3 of the cascade work.
J.4.2.b-2d-key-foundation-A (Foundation A for the splice mechanic:
`linearise_first_splice_keyonly` in `Proofs/Scanner/ScannerLinearise.lean`)
landed 2026-04-30 with sorry count **unchanged** in EmitterScannability
(the Part (2) splice-analysis sorry is replaced by a chain-side
accounting sorry of the same count but narrower shape; Foundation A
itself adds 0 sorries in `ScannerLinearise.lean`).  Foundation A closes
the splice mechanic of Part (2) by adapting the no-splice walk from
`linearise_prefix_eq_tokens_prefix`, then stepping `linearise.go` once
to fire the first `.keyOnly` splice (`expandKind .keyOnly = #[⟨pos, .key,
pos⟩]`), and reading off `.key` at index `j` via prefix-stability
(`linearise_go_getElem_lt_acc`).  The wrapper `emitPairList_body_linearise_characterization`
is reshaped to consume Foundation A: Part (2) is now reduced to a single
named obligation **J.4.2.b-2d-key-chain** (chain-side accounting
of `s'.pendingKeys[0]`'s shape: `0 < s'.pendingKeys.size`,
`s'.pendingKeys[0].insertBeforeIdx = s.tokens.size`,
`s'.pendingKeys[0].kind = .keyOnly`, plus the token-monotonicity
bound `s.tokens.size ≤ s'.tokens.size`).  Part (3) remains sorry'd
as **J.4.2.b-2d-key-wrap** (blocked on **J.4.2.b-2d-key-foundation-B**
— a companion linearise lemma for splices at after-flowEntry positions
— and **J.4.2.b-2d-key-chain** extended to all pairs).  Net effect:
this cadence step does not reduce sorry count but converts an opaque
splice-analysis sorry into a concrete chain-side accounting obligation
that's amenable to the existing `AllUnresolved`/`NoPlaceholders`
chain-propagation infrastructure.
J.4.2.b-2d-key-foundation-B (Foundation B for the splice mechanic at
general `(j, p, acc)` state: `linearise_splice_keyonly_at` and index-form
corollary `linearise_splice_keyonly_at_index` in
`Proofs/Scanner/ScannerLinearise.lean`) landed 2026-04-30 with sorry
count **unchanged** in EmitterScannability (the Part (3) splice-analysis
sorry is replaced by a chain-side accounting sorry of the same count
but narrower shape; Foundation B itself adds 0 sorries in
`ScannerLinearise.lean`).  Foundation B closes the splice mechanic of
Part (3) by isolating the splice fire from the start-of-walk: given a
transport equation `linearise tokens pks = linearise.go tokens pks j p acc`
(supplied by chain-side accounting) and splice-fire preconditions
(`p < pks.size`, `pks[p].insertBeforeIdx ≤ j`, `pks[p].kind = .keyOnly`),
it derives `(linearise tokens pks)[acc.size].val = .key` by stepping
`linearise.go` once to push `expandKind .keyOnly = #[⟨pos, .key, pos⟩]`
into the accumulator and propagating via prefix-stability
(`linearise_go_getElem_lt_acc`).  The wrapper
`emitPairList_body_linearise_characterization` is reshaped to consume
Foundation B (index form, with `acc.size = k + 1` for the after-flowEntry
position): Part (3) is now reduced to a single named obligation
**J.4.2.b-2d-key-chain** (extended to all outer pairs — supplying
`(j, p, acc)` with the right shape for each outer-level flowEntry index
`k`).  Foundations A and B together close the splice mechanic for both
Parts (2) and (3); the remaining work to discharge the 2d-stub theorem
is the chain-side accounting itself.  This dissolves the previous
**J.4.2.b-2d-key-wrap** sub-task — once **J.4.2.b-2d-key-chain** lands
covering both first-key and after-flowEntry-key shapes, the 2d-stub
theorem is fully discharged with no further wrapping needed.  Net effect:
this cadence step does not reduce sorry count but converts the second of
two opaque splice-analysis sorries into a concrete chain-side accounting
obligation, completing the splice-mechanic toolkit for Initiative 3.
J.4.2.b-2d-key-prep (pre-step toward chain-side accounting in
`emitPairList_body_linearise_characterization`) landed 2026-04-30 with
sorry count **unchanged** in EmitterScannability.  Two refinements:
(i) added the `h_pks_empty : s.pendingKeys = #[]` precondition to the
wrapper, which is needed to make Foundation A's `[0]`-index semantically
correct — without it, `pks[0]` could be an outer-scope leftover with a
smaller `insertBeforeIdx` than the body's first new pendingKey, breaking
the consumer's claim that `linearise[old_sz].val = .key` reads off the
just-spliced key for pair 1; (ii) discharged the trivial token-monotonicity
sub-fact `(s.tokens.filter p).size ≤ s'.tokens.size` directly from
`ScanChain_tokens_mono` + `Array.size_filter_le`, no longer bundled in
the chain-side sorry.  The remaining 2d-key-chain obligation is now
narrower (only the genuine pendingKey-shape facts) and split into two
named follow-ups: **2d-key-chain-Part2** (first-key splice shape) and
**2d-key-chain-Part3** (after-flowEntry splice locator).  The
`h_pks_empty` precondition is structurally true at the eventual call
site (`scanFiltered_emitMap_nonempty_structure` from
`scanNextToken_flow_open_mapping_init` — `mk' input` initializes empty
pendingKeys, and the `{` scan only emits `.flowMappingStart`); exposing
this fact at `scanNextToken_flow_open_mapping_init`'s output is a small
cascade-stitching task (item 3), not 2d-key-chain itself.  Net effect:
contract refinement + trivial sub-fact discharged + named decomposition,
no sorry count change.
J.4.2.b-2d-key-chain-Part2-body-A1 (foundational lemma
`saveSimpleKey_pkPush_when_allowed`) landed 2026-05-01 with sorry count
**unchanged** in EmitterScannability.  Adds a one-line foundational
lemma in `Proofs/Output/EmitterScannability.lean` (next to the existing
identity-branch lemma `saveSimpleKey_id_of_flow_ska_false_ek_none`)
exposing the exact pendingKey effect of `saveSimpleKey` under the push
branch (`simpleKeyAllowed = true ∧ explicitKeyLine = none`):
`(saveSimpleKey s).pendingKeys = s.pendingKeys.push <unresolved at
s.tokens.size>`, `pendingKeyActive = some s.pendingKeys.size`,
`simpleKey.possible = true`.  Investigation showed Part2-body-A
genuinely decomposes into A1 (this lemma) + A2 (per-leaf scalar) + A3
(per-leaf seq) + A4 (per-leaf map) + final `EmitScansInFlow` def
strengthening — Blueprint substep manifest updated with the refined
A1-A4 plan.  Net effect: foundational ingredient in tree, ready for
consumption by the per-leaf theorems landing in the next cadence steps.
Sorry count unchanged (no discharge, just infrastructure).
J.4.2.b-2d-key-chain-Part2-body-A2 (per-leaf scalar pkPush theorem
`scanNextToken_flow_scanDoubleQuoted_pkPush`) landed 2026-05-01 with
sorry count **unchanged** in EmitterScannability.  Parallel theorem
sits immediately after `scanNextToken_flow_scanDoubleQuoted` in
`Proofs/Output/EmitterScannability.lean`; under additional hypotheses
`s.simpleKeyAllowed = true ∧ s.explicitKeyLine = none` it produces the
existing 13 conjuncts plus three new pendingKey-tracking conjuncts
(`s'.pendingKeys.size = s.pendingKeys.size + 1`,
`s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size`,
`s'.pendingKeys[s.pendingKeys.size].kind = .unresolved`).  The proof
composes A1 (`saveSimpleKey_pkPush_when_allowed`),
`ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeys`, and
`ScannerCorrectness.setPendingKeyEndLine_{size,insertBeforeIdx,kind}`
for the dispatchContent J.2 dual-write wrap.  Implementation chose
parallel-proof copy (~150 lines) over in-place augmentation since the
base theorem has only one in-tree caller (`emit_scans_in_flow`) which
needs re-threading anyway when `EmitScansInFlow` is eventually
strengthened (Part2-body-A4-and-final-def step).  Net effect:
double-quoted scalar leg of the per-leaf strengthening landed; sequence
(A3) and mapping (A4) per-leaf theorems remain.  Sorry count unchanged
(no discharge, just infrastructure).
J.4.2.b-2d-key-chain-Part2-body-A3 (per-leaf flow-sequence-open pkPush
theorem `scanNextToken_flow_open_nested_pkPush`) landed 2026-05-01 with
sorry count **unchanged** in EmitterScannability.  Parallel theorem
sits immediately after `scanNextToken_flow_open_nested`; under the same
additional hypotheses as A2 (`s.simpleKeyAllowed = true ∧
s.explicitKeyLine = none`) it produces the existing 12 conjuncts plus
the same three pendingKey-tracking conjuncts as A2
(`s'.pendingKeys.size = s.pendingKeys.size + 1`,
`s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size`,
`s'.pendingKeys[s.pendingKeys.size].kind = .unresolved`).  Strictly
simpler than A2 since the `[` flow path is dispatched via
`scanNextToken_dispatchFlowIndicators` (not content) — there is NO
`setPendingKeyEndLine` wrap to thread through.  Proof composes A1
(`saveSimpleKey_pkPush_when_allowed`) for the push and
`ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys`
(Class A — pure preservation) for the flow-sequence open scan;
remaining body mirrors `scanNextToken_flow_open_nested` line-for-line.
Theorem covers the `[` open step only — full body+close emerges from
recursive composition through other per-leaf lemmas, with the outer
entry untouched by inner scans (they push at fresh indices > the
outer's index).  A3's structural simplicity refines the A4 (mapping
`{` open) estimate down from 1-2 cadence steps to ~0.5 (mechanical
mirror with `scanFlowMappingStart_preserves_pendingKeys`).  Net effect:
flow-sequence-open leg of the per-leaf strengthening landed; A4 +
final `EmitScansInFlow` def strengthening remain.  Sorry count
unchanged (no discharge, just infrastructure).
J.4.2.b-2d-key-chain-Part2-body-A4 (per-leaf flow-mapping-open pkPush
theorem `scanNextToken_flow_open_mapping_nested_pkPush`) landed
2026-05-01 with sorry count **unchanged** in EmitterScannability —
proof went through on the first try as predicted, confirming the ~0.5
cadence-step refined estimate.  Theorem sits immediately after
`scanNextToken_flow_open_mapping_nested`; under the same additional
hypotheses as A2/A3 (`s.simpleKeyAllowed = true ∧ s.explicitKeyLine =
none`) it produces the existing 12 conjuncts plus the same three
pendingKey-tracking conjuncts (`s'.pendingKeys.size = s.pendingKeys.size
+ 1`, `s'.pendingKeys[s.pendingKeys.size].insertBeforeIdx = s.tokens.size`,
`s'.pendingKeys[s.pendingKeys.size].kind = .unresolved`).  Mechanical
mirror of A3 with `[` → `{`, `scanFlowSequenceStart` →
`scanFlowMappingStart`, `dispatchFlowIndicators_bracket` →
`dispatchFlowIndicators_brace`, and
`ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys` →
`ScannerCorrectness.scanFlowMappingStart_preserves_pendingKeys`.  No
`setPendingKeyEndLine` wrap (the `{` flow path also skips
`dispatchContent`).  Theorem covers the `{` open step only; inner pair
scans (key, `:`-resolution, value bodies) push new entries at later
indices and do not touch the outer entry recorded by the outer
`saveSimpleKey`.  Net effect: per-leaf chain A1-A4 complete; only the
final `EmitScansInFlow` def strengthening + `emit_scans_in_flow`
re-prove (~0.5 cadence step) remains before Part2-body-B's `:`
resolution exposure can compose against the strengthened conclusions.
Sorry count unchanged (no discharge, just infrastructure).
J.4.2.b-2d-key-chain-Part2-body-B (per-`:`-step pkResolve theorem
`scanNextToken_flow_value_pkResolve`) landed 2026-05-01 with sorry
count **unchanged** in EmitterScannability — landed in one cadence
step matching the original 1-step estimate.  Theorem sits immediately
after `scanNextToken_flow_value`; signature accepts the existing 9
preconditions plus three new hypotheses (`s.simpleKeyAllowed = false`,
`s.simpleKey.possible = true`, and `s.pendingKeyActive = some i` with
`i < s.pendingKeys.size`) and concludes the existing 13 surface
conjuncts plus 3 pkResolve conjuncts: size preservation
(`s'.pendingKeys.size = s.pendingKeys.size`), per-active-index
resolution (`(s'.pendingKeys[i]).kind = .keyOnly` together with
`insertBeforeIdx` preservation at `i`), and unchanged-elsewhere
(`s'.pendingKeys[j] = s.pendingKeys[j]` for all `j ≠ i`).  The
`simpleKeyAllowed = false` precondition is the linchpin — it makes
`saveSimpleKey s = s` (via the already-tree
`saveSimpleKey_id_of_flow_ska_false_ek_none`) so the
pre-existing active reservation flows unchanged into
`scanValuePrepare`'s flow branch where `setPendingKeyKind … .keyOnly`
fires.  Foundational helper `scanValuePrepare_pendingKeys_flow_resolve`
(added next to `saveSimpleKey_pkPush_when_allowed` /
`scanValueValidate_ok_of_not_possible_ek_none`) gives the pure
characterization: `(scanValuePrepare s).pendingKeys =
setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly` under
`s.inFlow = true ∧ s.simpleKey.possible = true`.  Proof reuses the
existing `scanNextToken_flow_value` to discharge surface conjuncts,
then re-derives the canonical `s_final` chain to identify the
existential `s'` via determinism of `scanNextToken`, and tracks
pendingKeys through the chain (`saveSimpleKey` identity → `s_ad`
allowDirectives passthrough → `scanValueClearKey` identity → flow
branch's `setPendingKeyKind` write → `emit`/`advance`/final
record-update Class A passthroughs).  Per-entry pkResolve facts
derived via `Array.getElem_setIfInBounds_self` (for the active
index) and `Array.getElem_setIfInBounds_ne` (for the unchanged
indices).  Net effect: Part2-body's leaf and `:`-step machinery
complete (A1-A4 + B); only Part2-body-C composition (~0.5 step)
remains for the cons-side recursion in `emitPairList_chain_first_pkShape`,
plus the orthogonal `EmitScansInFlow` def strengthening (the natural
seal on A1-A4).  Sorry count unchanged (no discharge, just
infrastructure).
J.4.2.b-2d-key-chain-Part2-body-C-foundation-Aseq/Amap (preserves-prior
strengthening on A3/A4) landed 2026-05-01 with sorry count **unchanged**.
Body-C investigation revealed that beyond A1-A4's existing
`pendingKeys.size + pkPush entry shape` conjuncts, the composition
also requires `pendingKeyActive = some s.pendingKeys.size`,
`simpleKey.possible = true`, and `preserves-prior` (entries at
`j < s.pendingKeys.size` unchanged) at the post-key state — none
of which are exposed by the current per-leaf signatures.  This step
adds the easiest of those (preserves-prior) to A3 and A4: under the
existing hypotheses, conclude `∀ j (hj : j < s.pendingKeys.size)
(hj' : j < s'.pendingKeys.size), s'.pendingKeys[j]'hj' =
s.pendingKeys[j]'hj`.  Proof is direct: the flow-open path
(`scanNextToken_dispatchFlowIndicators`) skips `dispatchContent`, so
`s'.pendingKeys = s.pendingKeys.push <new>` and preservation follows
from `Array.getElem_push_lt`.  No `pendingKeyActive` chain needed
(the chain is needed for A2 because `dispatchContent`'s
`setPendingKeyEndLine` wrap acts on the active index — for A3/A4
there is no wrap).  Body-C is now decomposed into four sub-steps
in the open-bullet section: **C-foundation-Aseq/Amap** (this step),
**C-foundation-Ascalar** (extend A2 with active + possible +
preserves-prior; needs the `pendingKeyActive` preservation chain in
`Proofs/Scanner/ScannerCorrectness.lean` — ~0.5 step), **C-foundation-EmitScansInFlow**
(uniform preserves-prior + first-key gated conjunct on
`EmitScansInFlow` family; re-prove `emit_scans_in_flow` and
`emit{List,PairList}_scans_*`; for seq/map cases, the gated
`pendingKeyActive` and `simpleKey.possible` follow from the
`simpleKeyStack` / `pendingKeyStack` pop on `]` / `}` —
~1 step), and **C-compose** (singleton/cons walk in
`emitPairList_chain_first_pkShape`, plus a
`scanNextToken_flow_comma_pkPreserve` variant — ~0.5–1 step).
Cleaner cadence sizing than the original "~0.5 step" estimate
on body-C as a single unit.

J.4.2.b-2d-key-chain-Part2-body-C-foundation-Ascalar (the per-leaf
scalar foundation for body-C) landed 2026-05-01 with sorry count
**unchanged at 9**.  A2 (`scanNextToken_flow_scanDoubleQuoted_pkPush`)
now exposes 17 conjuncts (was 15), adding `s'.pendingKeyActive =
some s.pendingKeys.size`, `s'.simpleKey.possible = true`, and
preserves-prior on `pendingKeys`.  The two infrastructure additions
that made this possible: (a) a parallel `*_preserves_pendingKeyActive`
chain in `Proofs/Scanner/ScannerCorrectness.lean`, mirroring the
existing `*_preserves_pendingKeys` chain for the operations called
by `scanDoubleQuoted` (advance/emit/emitAt + skipSpacesLoop/skipSpaces
+ skipWhitespaceLoop/skipWhitespace + consumeNewline +
collectHexDigitsLoop/parseHexEscape/processEscape +
foldQuotedNewlinesLoop/foldQuotedNewlines + collectDoubleQuotedLoop +
scanDoubleQuoted) — none of these helpers touch `pendingKeyActive`,
so all proofs are pure passthroughs structurally identical to the
`_preserves_pendingKeys` versions; (b) two new helpers
`setPendingKeyEndLine_decomp_some` (specialization of the existing
decomp that exposes the active index `j` directly) and
`setPendingKeyEndLine_some_at_other_unchanged` (record-level "at index
`i ≠ j`, the `(some j)` wrap is the identity") — together these
discharge preserves-prior under `dispatchContent`'s
`setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line`
J.2 dual-write wrap, since `s_dq.pendingKeyActive = some s.pendingKeys.size`
threaded by the new chain means the wrap's write index is
`s.pendingKeys.size > j`, never colliding with prior indices.  Only
the `emit_scans_in_flow` consumer references A2 in tree, and it ignores
the new conjuncts — no consumer rewiring needed.  Sorry locations
shifted by +53 lines from the prior baseline due to the new chain
insertion in ScannerCorrectness.lean.  Body-C remaining: **C-foundation-EmitScansInFlow**
(~1 step) and **C-compose** (~0.5–1 step), in that order.
J.4.2.b-2d-key-chain-Part2-stub (named extraction of the first-key
chain-side accounting) landed 2026-04-30 with sorry count **unchanged**
in EmitterScannability.  Introduced freestanding theorem
`emitPairList_chain_first_pkShape` just before
`emitPairList_body_linearise_characterization`; signature accepts the
chain `ScanChain s n s'` plus the `emitPairList_scans_nonempty`
hypotheses + `h_pks_empty`, produces the first-key chain-side facts
(`0 < s'.pendingKeys.size ∧ s'.pendingKeys[0].insertBeforeIdx = s.tokens.size
∧ s'.pendingKeys[0].kind = .keyOnly`).  Body is `sorry`; wrapper Part (2)
now calls the stub cleanly with filter-identity transport.  Investigation
showed the body discharge requires deeper infrastructure than initially
scoped: `EmitScansInFlow`'s current conclusion does not expose
post-scan pendingKey shape, so a 2-3 cadence-step plan was added —
**Part2-body-A** (strengthen `EmitScansInFlow` to expose the post-scan
pendingKey push), **Part2-body-B** (strengthen `scanNextToken_flow_value`
to expose the active-key resolution to `.keyOnly`), **Part2-body-C**
(compose along the singleton/cons structure of `emitPairList_scans_nonempty`
to discharge the stub).  Net effect: clean named obligation in tree
with the precise signature, replacing the inline Part (2) sorry —
sorry count unchanged, structure improved with reusable signature
that the body discharge can plug into without further wrapper edits.

### Phase J.4 — Cleanup and follow-on (1-2 weeks)

- Delete dead lemmas (the ~600 lines of `SimpleKeyAboveFloor`
  infrastructure).
- Update `02-architecture.md` §Append-only to reflect the new
  reality (rename to "side-channel pending keys" or similar).
- Update `01-terminology.md` for `PendingKeyEntry`, `linearise`.
- Remediate any consumer code that read raw `tokens` and now needs
  the linearised view.

**Validation gate**: full build green, sorry count reduced by ≥ N
(target N = 6: the 2 Tier 2 sorries + 4 in `_structure` theorems
that depend on them), Blueprint docs consistent.

(Cross-reference to §5.d: the current sorry-using-declaration count
at HEAD is **24** — 3 Linearise + 7 EmitterScannability Tier 2 + 14
new Category C.  J.3's target is to clear all 17 non-Tier-2 sorries
(3 Linearise + 14 Category C); J.4's N=6 target then bites against
the residual 7 Tier 2 declarations.  Post-J.4, the natural ceiling is
≤1 declaration, with the stretch target being 0.)

## Estimated total effort

**Initial estimate**: 10–14 weeks single-contributor.

**Revised after spec review (2026-04-26)**: 7–10 weeks
single-contributor.  The Q3 finding (indent management is already
append-only) cuts a substantial chunk from Phase J.2.  Submodules
that touch `simpleKey`/`scanValuePrepare` are the actual surface
area:
- `Scanner/SimpleKey.lean` (heart of the change)
- `Scanner/Scanner.lean` (`scanFlowEntry` rename of lookback;
  `scanFiltered` linearisation invocation)
- `Scanner/State.lean` (`emit` unchanged; new `registerPendingKey` /
  `resolvePendingKey` operations)

`Indent.lean`, `Whitespace.lean`, `Comment.lean`, `Scalar.lean` —
mostly pass-through with type-signature updates only.

Parallelisable: Phase J.2 submodules can be split across contributors
if multiple verifiers are available.

## Risks

- **Linearisation correctness**: the splice operation must produce
  the exact token order the parser expects.  Mitigation: §Worked
  example pins the expected output for one non-trivial input;
  Phase J.2 adds a golden-file test against current scanner output
  for a corpus of YAML inputs before flipping the production path.
- **Proof regression**: re-discharging the existing proof corpus may
  surface unexpected dependencies.  Mitigation: Phase J.3 has explicit
  sorry-budget; if exceeded, pause and reassess.
- **Scanner-progress proof** (`ScannerProgress.lean`): currently
  relies on `setIfInBounds`'s no-shift property.  In the new model,
  monotonic-progress is provable from append-only-ness directly
  (`tokens.size` and `pendingKeys.size` both grow weakly per step,
  strictly per scanner-event), but the proof needs reworking.

## Open decisions during J.1+

1. **Tier 2 in the meantime.**  Two options:
   - (a) Pause Tier 2; reach it as the J.3 demonstration.
   - (b) Discharge Tier 2 with `Path A` (PlaceholderStable invariant)
     on `main` as throwaway scaffolding, then delete it during J.4.
   Option (a) is cleaner if J fits the schedule; (b) is insurance
   if the feature branch slips and `main` needs the Tier 2 result
   sooner.
2. **Resource allocation.**  7–10 weeks single-threaded (revised
   estimate after the Q3 finding) is the working budget.  If
   Phase J.2's per-submodule sorry-budget is breached, pause and
   reassess before committing further weeks.
3. **Sync cadence with `main`.**  The feature branch should rebase
   on `main` at least at every phase boundary (end of J.1, J.2, J.3)
   to keep the eventual merge tractable.  If `main` lands a major
   scanner-touching change during J, escalate to a mid-phase rebase.
