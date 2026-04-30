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
   - **2b (placeholder-free invariant)**: prove the global invariant that
     `s.tokens` contains no `.placeholder` at the chain endpoint when no
     resolutions have fired (stronger version of the per-position
     invariant).  Feeds the no-placeholder hypothesis of
     `linearise_eq_filter_no_resolutions`.  Estimate: 1 cadence step.
   - **2c (linearise-shape seq body)**: produce a linearise-shape variant
     of `emitList_body_filtered_characterization` for the all-scalar /
     no-resolution case, using 2a + 2b as the bridge.  Estimate: 1-2
     cadence steps.
   - **2d (linearise-shape pair body)**: produce a linearise-shape variant
     of `emitPairList_body_filtered_characterization`, which is harder
     because `:` resolutions DO fire — needs richer linearise-aware
     reasoning over the resolved-key splices, not just the no-resolution
     bridge.  This is the largest remaining sub-task.  Estimate: 2-3
     cadence steps (or one multi-day landing).
3. **Stitch the cascade** into `scanFiltered_emitSeq_nonempty_structure`
   (currently line 9844 sorry) and `scanFiltered_emitMap_nonempty_structure`
   (currently line 10070 sorry), discharging both Tier 1 cascade sorries
   using the J.4.2.c family of positional lemmas + the J.4.2.b-pkwi
   chain-endpoint invariant + the linearise-shape body characterizations
   from item (2).  Estimate: 1-2 cadence steps once (2c, 2d) are in tree.

The remaining chunk (items 2 + 3) is the substantial leg of J.4 — but
the breakdown above lets each substep land in cadence-size, with the
positional family (J.4.2.c-prefix / -pos1 / -pos2) and the chain-endpoint
invariant (J.4.2.b-pkwi) already in place to support them.

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
