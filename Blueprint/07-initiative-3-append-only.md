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
| J.3.4 | ScannerPlainScalarValid consumers | 4 | `Proofs/Production/ScannerPlainScalarValid.lean` | pending |
| J.3.5 | Production+EndToEnd bridges | 2 | `Proofs/Production/DocumentProduction.lean`, `Proofs/EndToEndCorrectness.lean` | pending |
| J.3.6 | EmitterScannability Cat C | 6 | `Proofs/Output/EmitterScannability.lean` (Cat C only; 7 Tier 2 deferred to J.4) | pending |

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
  8. `linearise_positions_ordered` with pendingKey position-fit
     hypotheses (~120 LOC).
  9. Compose into `scanFiltered_produces_valid_tokens` (~50 LOC).

  Status (2026-04-27): Steps 1-7, 8a, 8c ✓ done (~2434 LOC across eight
  commits: `c6bfab0a` saveSimpleKey discharge, `1e6b4741` Class A/B/C
  foundation, `de7610d9` Blueprint update, `c4dc838a` ~30 Class A
  *_preserves_pendingKeys leaves, `fbd330d4` dispatcher composition +
  scanNextToken preservation, `cbba890e` scanLoopFull preservation,
  `a5aa58e8` LineariseFit invariant + mono/field/save core lemmas
  (~423 LOC), `ca29c9b2` linearise_positions_ordered (~261 LOC)).

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

  Remaining: Step 8b (per-op `*_preserves_LineariseFit` chain through
  scanLoopFull, mirroring the existing PendingKeysWellIndexed chain;
  ~500-800 LOC) and Step 9 (compose `scanFiltered_produces_valid_tokens`
  using `linearise_size_ge_tokens`, `linearise_first_eq_tokens_first`,
  `linearise_last_eq_tokens_last`, `linearise_positions_ordered`;
  ~50 LOC).  Folds naturally into J.3.4 since
  `ScannerPlainScalarValid` consumers need the same invariants.

**J.3.4–J.3.6**: re-discharge consumers in dependency order, each
substep removing its sorry-using declarations and the matching
`-- J.3 manifest 5.d:` markers.

**J.3 final gate**: `lake build` green; sorry count 24 → 7 (only
the 7 Tier 2 EmitterScannability declarations remain, deferred to
J.4).

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
