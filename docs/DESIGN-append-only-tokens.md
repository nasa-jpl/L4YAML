# Design: Append-Only Token Array via Reservation Slots

**Author**: P10.11a verification effort  
**Date**: 2026-03-06  
**Status**: Design — pending implementation  
**Affects**: Scanner.lean, Token.lean, ScannerCorrectness.lean, ScannerSimpleKey.lean

## 1  Motivation

The YAML scanner maintains a token array that grows as it processes input.
Most operations (`emit`, `emitAt`, `unwindIndents`) are **append-only**:
they push tokens to the end of the array. One operation is not —
`ScannerState.insertAt` — which splices a token at an arbitrary earlier
index, shifting all subsequent elements right.

This single non-append operation makes three correctness theorems
**unprovable** in their natural form, blocking completion of P10.11a
(`scan_produces_valid_tokens`).

## 2  Background: Implicit Key Resolution in YAML

YAML allows implicit mapping keys:

```yaml
foo: bar
```

When the scanner sees `foo`, it doesn't know whether `foo` is a key or a
standalone scalar. Only upon encountering `:` does the scanner confirm
"that was a mapping key." The YAML 1.2.2 spec (§7.4) calls this mechanism
**simple key tracking**.

The token parser expects tokens in this order:

```
blockMappingStart  key  scalar("foo")  value  scalar("bar")  blockEnd
```

The `.key` token must appear **before** the key content. But the scanner
discovers the key role **after** the content is already tokenized. The
current implementation resolves this contradiction via retroactive
insertion:

1. `saveSimpleKey` records `tokenIndex := tokens.size` (current end)
2. Content gets tokenized → tokens appended after the saved index
3. `scanValuePrepare` calls `insertAt(tokenIndex, .key)` → splices `.key`
   before the content, shifting subsequent tokens right by 1 (or 2 when
   `.blockMappingStart` is also needed)

## 3  Why `insertAt` Breaks Proofs

### 3.1  The False Theorem Problem

The natural theorem for prefix preservation states:

```lean
theorem scanNextToken_preserves_prefix (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i] = s.tokens[i]
```

This is **false**. When `scanValue` fires the `insertAt` path, an element
at index `i ≥ tokenIndex` shifts to index `i+1`. The old `tokens[i]` is
now at `tokens[i+1]`, and `tokens[i]` is the newly inserted `.key`.

This isn't "too hard to prove" — it's a false statement about the
program's behavior. No amount of proof engineering can rescue a theorem
that claims something the code doesn't do.

### 3.2  The Downstream Cascade

Three of the four remaining `sorry` obligations are blocked:

| Theorem | Why Blocked |
|---------|-------------|
| `scanNextToken_preserves_prefix` | **False** — `insertAt` shifts indices |
| `scanLoop_preserves_tokens` (recursive case) | Depends on prefix preservation via induction |
| `scan_positions_ordered` | `insertAt` inserts tokens with past positions amid later tokens |

The first sorry (`scanNextToken_adds_tokens`) was proven by a different
route (token count monotonicity), but the other three all require
reasoning about the *identity* or *ordering* of individual array elements
— exactly what `insertAt` disrupts.

### 3.3  The "Strong Theorem" Trap

It is counter-intuitive that a "stronger" theorem can be useless. In
informal mathematics, strengthening a conclusion makes a theorem more
powerful. But in verification, "too strong" means the statement claims
something **the code doesn't actually guarantee**. It's not a theorem at
all — it's a false conjecture.

The appropriate response is to either:

- **(A)** Weaken the theorem to match reality (prove only what the code
  actually does), or
- **(B)** Strengthen the code to match the theorem (refactor so the
  theorem becomes true).

Option (A) would mean proving targeted invariants like "tokens[0] is
preserved" instead of full prefix preservation. This is possible but
brittle — every consumer of prefix preservation would need a specialized
lemma, and position ordering would still require reasoning about
`insertAt`'s position-preserving properties.

Option (B) — this design — eliminates the structural obstacle. The
natural theorems become true statements about the code, and the proofs
follow naturally from the code's structure.

### 3.4  The General Principle

**A data structure operation that violates the invariants you want to
prove forces every downstream proof to work around the violation.**

`insertAt` violates three natural invariants simultaneously:
- **Prefix stability**: existing elements don't move
- **Append-only growth**: new elements appear only at the end
- **Position monotonicity**: positions increase with array index

Every proof that touches the token array must now account for the
possibility that `insertAt` was called somewhere upstream, branching on
whether indices shifted. This "proof tax" compounds: each theorem in the
chain must thread the exception through, until the proof structure becomes
dominated by bookkeeping for a single edge case.

The refactoring eliminates this tax at the source.

## 4  Design: Reservation Slots

### 4.1  Core Idea

Replace retroactive insertion with **upfront reservation**:

1. When the scanner identifies a potential simple key, immediately
   **reserve placeholder slots** at the current end of the token array.
2. When the key is confirmed (`:` encountered), **overwrite** the
   placeholders in-place with the actual tokens.
3. When the key is invalidated, the placeholders remain.
4. Before returning the final token stream, **filter out** unresolved
   placeholders.

The token array is now strictly append-only during scanning. Overwriting
an existing slot doesn't change the array length or shift any indices.

### 4.2  Token Type Change

Add a `placeholder` variant to `YamlToken`:

```lean
inductive YamlToken where
  | streamStart
  | streamEnd
  | placeholder    -- ← NEW: reserved slot for potential simple key
  | versionDirective (major minor : Nat)
  | tagDirective (handle tagPrefix : String)
  | documentStart
  | documentEnd
  -- ... rest unchanged
```

The `placeholder` token is a scanner-internal mechanism. It never appears
in the final token stream returned to the parser.

### 4.3  Slot Count: Always Reserve 2

The number of tokens inserted at resolve time varies:

| Path | Tokens Inserted |
|------|----------------|
| Block context, new indent (`col > currentIndent`) | `.blockMappingStart` + `.key` |
| Block context, same indent | `.key` only |
| Flow context | `.key` only |

Since the decision between 1 and 2 tokens depends on indent level at
**resolve time** (not save time), we always reserve the maximum: **2 slots**.

At resolve time:
- **2 needed**: overwrite both with `.blockMappingStart` and `.key`
- **1 needed**: overwrite one with `.key`, leave the other as `.placeholder`

At invalidation time:
- Both remain `.placeholder`

### 4.4  Modified Functions

**`saveSimpleKey`** — previously a pure metadata update, now also appends:

```lean
def saveSimpleKey (st : ScannerState) : ScannerState :=
  if st.explicitKeyLine == some st.line then st
  else if st.simpleKeyAllowed then
    let idx := st.tokens.size
    -- Reserve two slots for potential key + blockMappingStart
    let st := { st with tokens := st.tokens.push ⟨st.currentPos, .placeholder⟩ }
    let st := { st with tokens := st.tokens.push ⟨st.currentPos, .placeholder⟩ }
    { st with simpleKey := {
        possible := true
        tokenIndex := idx
        pos := st.currentPos
        endLine := st.line } }
  else st
```

**`scanValuePrepare`** — replaces `insertAt` with `Array.set`:

```lean
def scanValuePrepare (s : ScannerState) : ScannerState :=
  if s.simpleKey.possible then
    let idx := s.simpleKey.tokenIndex
    if !s.inFlow then
      if (s.simpleKey.pos.col : Int) > s.currentIndent then
        -- Need both blockMappingStart and key
        let s := { s with tokens := s.tokens.set ⟨idx, by ...⟩ ⟨s.simpleKey.pos, .blockMappingStart⟩ }
        let s := { s with tokens := s.tokens.set ⟨idx+1, by ...⟩ ⟨s.simpleKey.pos, .key⟩ }
        { s with
          indents := s.indents.push { column := s.simpleKey.pos.col, isSequence := false }
          simpleKey := { possible := false } }
      else
        -- Only key (leave slot[idx] as placeholder)
        { s with
          tokens := s.tokens.set ⟨idx+1, by ...⟩ ⟨s.simpleKey.pos, .key⟩
          simpleKey := { possible := false } }
    else
      { s with
        tokens := s.tokens.set ⟨idx+1, by ...⟩ ⟨s.simpleKey.pos, .key⟩
        simpleKey := { possible := false } }
  else if s.explicitKeyLine.isSome then
    { s with simpleKey := { possible := false } }
  else
    if !s.inFlow then pushMappingIndent s s.col else s
```

**`scan`** — filters placeholders before returning:

```lean
def scan (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  -- ... existing setup ...
  let rawTokens ← scanLoop s (fuel * 4)
  .ok (rawTokens.filter (·.val != .placeholder))
```

**`ScannerState.insertAt`** — deleted entirely.

### 4.5  Validation Reference Check

The `scanValueValidate` function currently reads:

```lean
if let some prevTok := s.tokens[s.simpleKey.tokenIndex - 1]? then
```

After the refactoring, `tokenIndex` points to the first placeholder slot.
The token at `tokenIndex - 1` is the one emitted *before* the
placeholders — same logical token as before. This check is unaffected.

### 4.6  Impact on Existing Proofs

**Proofs that simplify or become trivial:**

| Proof | Before | After |
|-------|--------|-------|
| `insertAt_tokens_size` | 12 lines (extract+append arithmetic) | Deleted |
| `insertAt_preserves_wellFormed` (4 conjuncts) | ~35 lines | Deleted |
| `scanValuePrepare_tokens_monotonic` | Chains 1–2 `insertAt_tokens_size` | `Array.size_set` rewrites |
| `scanNextToken_preserves_prefix` | **False** | **True and provable** |
| `scanLoop_preserves_tokens` (recursive case) | Blocked | Follows from prefix preservation + IH |
| `scan_positions_ordered` | Blocked by `insertAt` position reasoning | Natural induction on loop |

**Proofs that need minor adjustment:**

| Proof | Change Needed |
|-------|--------------|
| `saveSimpleKey_preserves_tokens` | No longer true — now adds 2 tokens. Replace with `saveSimpleKey_adds_two_tokens` |
| `preprocess_tokens_mono` | Account for `saveSimpleKey` adding 2 tokens instead of 0 |
| All dispatch `*_tokens_mono` theorems | Already correct (dispatch is after preprocessing) |
| `scanNextToken_adds_tokens` | Adjust preprocessing step; dispatch unchanged |

**Proofs unaffected:**

All proofs for `emit`, `emitAt`, `advance`, `unwindIndents`, `skipToContent`,
`collectAnchorNameLoop`, flow open/close functions, scalar scanning functions,
`scanKey`, document start/end, directive scanning — none of these touch
`insertAt` or `saveSimpleKey`.

## 5  Why the Refactoring Enables Clean Proofs

### 5.1  Append-Only as a Structural Invariant

With the refactoring, every token array operation satisfies:

> For all `i < s.tokens.size`, after any scanner operation producing `s'`:
> `s'.tokens[i] = s.tokens[i]`

This is now a **structural property of the code**, not an invariant that
must be painstakingly threaded through proofs. Each function preserves it
automatically because no function modifies existing array elements.

(Overwriting placeholders is the one exception, and it only changes the
*content* of a slot created by the same simple-key lifecycle, not a slot
created by a different operation.)

With the append-only invariant, prefix preservation becomes:

```lean
theorem scanNextToken_preserves_prefix (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i] = s.tokens[i]
```

This is now **true** and follows directly from the structure of each
branch: every branch either appends (preserving existing elements) or
overwrites only placeholder slots (which were created within the same
`scanNextToken` call and are thus at indices `≥ s.tokens.size`).

### 5.2  Position Monotonicity Becomes Natural

Without `insertAt`, position ordering follows a clean inductive argument:

1. **Base case**: After `emit streamStart`, array has 1 token. Ordering
   is vacuous.
2. **Inductive step**: Scanner advances through input (increasing offset).
   Each new token's position ≥ scanner's current offset ≥ all previous
   tokens' positions. Since new tokens are only appended, ordering is
   preserved.

Placeholders get the position of `saveSimpleKey` (which is the current
scanner position at save time). When later tokens are appended, they have
positions ≥ the save position. The reserved slots already exist in the
array at indices ≤ any later token's index, and their positions are ≤ any
later token's position. Ordering is maintained.

The overwriting step (at resolve time) replaces `.placeholder` with `.key`
or `.blockMappingStart` at the **same position** — the ordering invariant
is trivially preserved since only the token value changes, not its position.

### 5.3  The Proof Engineering Principle

**Design the data structures so that the properties you want to prove are
structural consequences of the code, not accidental invariants that must
be maintained by convention.**

The original `insertAt` design treated the token array as a mutable buffer
with arbitrary access — natural for imperative C code (libyaml), but
hostile to formal verification. Every operation could potentially disturb
any element in the array, and each proof had to rule out that possibility
case by case.

The reservation-slot design makes the token array a **monotone structure**:
once an index is occupied, its positional identity is fixed. The only
mutation is filling placeholder content, which changes the token value but
not its position or existence. This is a much weaker form of mutation that
doesn't disturb any of the three key invariants (prefix stability,
append-only growth, position monotonicity).

**The key insight: in verified programming, the cost of a clever
imperative trick is paid not at runtime but at proof time — and the
interest compounds across every dependent theorem.**

`insertAt` saved a few lines in the scanner implementation (compared to
pre-reserving slots). But it imposed a proof tax on every theorem about
token array structure: prefix preservation, loop invariants, position
ordering. Each of these is individually manageable but collectively they
form a chain where each link must account for the same exception. The
reservation-slot approach eliminates the tax entirely.

### 5.4  Verification-Aware Design Patterns

This refactoring illustrates several patterns for writing code that is
amenable to formal verification:

1. **Append-only data structures**: If you need to prove properties about
   array elements at fixed indices, don't allow operations that shift
   indices. Reserve space upfront and fill in later.

2. **Separate content mutation from structural mutation**: Overwriting a
   value at a fixed index is much easier to reason about than inserting
   or deleting elements (which change the meaning of every subsequent
   index).

3. **Make loop invariants structural**: If every iteration of a loop
   should preserve certain properties, design the operations so that
   preservation is a consequence of the type structure, not a proof
   obligation at each step.

4. **Pay the cost at the source**: Adding `.placeholder` and filtering it
   out is a small runtime cost. But it eliminates O(N) proof obligations
   that would otherwise be needed at every site that reasons about the
   token array.

5. **Match abstraction level to the specification**: The `ValidTokenStream`
   specification talks about token identity at fixed indices
   (`tokens[0].val = streamStart`, `tokens[size-1].val = streamEnd`).
   The implementation should support reasoning at the same abstraction
   level — fixed-index access — rather than requiring proofs to account
   for index-shifting operations.

## 6  Implementation Plan

### Phase 1: Token Type (Token.lean)
- Add `| placeholder` to `YamlToken`
- Update derived instances if needed

### Phase 2: Scanner Core (Scanner.lean)
- Modify `saveSimpleKey` to push 2 placeholder tokens
- Rewrite `scanValuePrepare` to use `Array.set` instead of `insertAt`
- Add placeholder filtering to `scan` before returning
- Delete `ScannerState.insertAt`
- Update `scanValueValidate` if needed (adjust index references)

### Phase 3: Proof Updates (ScannerSimpleKey.lean, ScannerCorrectness.lean)
- Delete `insertAt_*` theorems
- Add `saveSimpleKey_adds_two_tokens` (or similar)
- Update `preprocess_tokens_mono` for new `saveSimpleKey` behavior
- Update `scanValuePrepare_tokens_monotonic`
- Re-derive `scanNextToken_adds_tokens` (may change slightly)

### Phase 4: New Proofs
- Prove `scanNextToken_preserves_prefix` (now true)
- Prove `scanLoop_preserves_tokens` recursive case
- Prove `scan_positions_ordered`
- Verify `scan_produces_valid_tokens` compiles with 0 sorry

### Phase 5: Validation
- `lake build` — 191/191 jobs
- Test suite — 869/869 tests
- Confirm 0 sorry warnings

## 7  Risks and Mitigations

| Risk | Mitigation |
|------|-----------|
| Placeholder tokens leak to parser | Filter in `scan` before return; add `#guard` that no placeholders in output |
| `Array.set` bounds proof obligations | `saveSimpleKey` records `tokenIndex` s.t. `idx + 1 < tokens.size` after push |
| `saveSimpleKey` token count change breaks `preprocess_tokens_mono` | Strengthen to account for +2; dispatch helpers unaffected |
| Filter changes final token array size | `scan_produces_at_least_two` must account for filtering; streamStart/streamEnd are never placeholders |
| Performance regression from filtering | O(N) filter on return — negligible vs. scanning cost; `insertAt` was also O(N) per call |
| `scanValueValidate` reads `tokens[tokenIndex - 1]` | After refactoring, `tokenIndex` points to first placeholder; `tokenIndex - 1` is still the preceding real token |

## 8  Relationship to libyaml

The original `insertAt` approach mirrors libyaml's `yaml_insert_token`
function, which performs the same retroactive insertion for implicit keys.
C/C++ scanners use this pattern because array insertion is a well-understood
O(N) operation and correctness is validated by testing.

The reservation-slot approach diverges from libyaml's implementation
strategy but preserves the same **token protocol** — the parser sees
identical token sequences (`.key` before content). The divergence is
purely in how the scanner constructs that sequence internally.

This is an example of a general principle in verified programming:
**the specification constrains what the code must produce, not how it
produces it.** We are free to choose an implementation strategy that
makes correctness easier to prove, as long as the observable behavior
(the token stream) is identical.

## 9  Hindsight: Implementation Reflections

This section was written after completing the refactoring (191/191 builds,
869/869 tests, sorry count reduced from 5 to 4). The design in §1–8 was
written before implementation; these reflections record what surprised us,
what simplified, and what Lean 4 idioms we learned the hard way.

### 9.1  The Prediction That Didn't Hold

Section 5.1 claimed:

> `scanNextToken_preserves_prefix` is now **true** and follows directly
> from the structure of each branch.

This was **overconfident**. The theorem as stated — without preconditions
on the incoming state — is still not provable. The issue is *stale simple
keys*.

The design correctly identified that `setIfInBounds` only overwrites
placeholder slots created "within the same `scanNextToken` call." But
`scanNextToken` operates on a state threaded from the *previous*
iteration. If a prior iteration called `saveSimpleKey` (reserving
placeholders at index `k`), and subsequent iterations appended tokens past
`k`, then on the current call `simpleKey.tokenIndex = k < s.tokens.size`.
Now `scanValuePrepare` overwrites `tokens[k]` — which is in the
"preserved prefix" range.

The overwritten slot *is* a placeholder, so the token stream is still
correct. But the theorem `s'.tokens[i] = s.tokens[i]` is false at
`i = k`, because `s.tokens[k].val = .placeholder` and
`s'.tokens[k].val = .blockMappingStart`.

**The fix** requires an explicit invariant threaded through the induction:

```lean
¬s.simpleKey.possible ∨ s.simpleKey.tokenIndex ≥ s.tokens.size
```

This holds at the base case (`scanInit` has `simpleKey.possible = false`)
and is maintained inductively (any `saveSimpleKey` sets `tokenIndex` to
the current `tokens.size`, which grows monotonically). The corrected
theorem would add this as a precondition, or the `scanLoop` proof would
carry it as a strengthened IH.

**Lesson**: *Append-only is necessary but not sufficient.* The refactoring
eliminated the *structural* obstacle (`insertAt` shifting indices), but
revealed a *lifecycle* obstacle: reasoning about cross-iteration state
requires an invariant about when simple keys were created relative to the
current token count. The design's §5.1 analysis was correct about what
happens *within* a single `scanNextToken` call but missed the
cross-iteration interaction.

### 9.2  `Array.set` vs `Array.setIfInBounds`

The design (§4.4) specified `Array.set` with in-bounds proofs:

```lean
s.tokens.set ⟨idx, by ...⟩ ⟨s.simpleKey.pos, .blockMappingStart⟩
```

In practice we used `Array.setIfInBounds` instead, which performs the
set only when in-bounds and is a no-op otherwise:

```lean
s.tokens.setIfInBounds idx ⟨s.simpleKey.pos, .blockMappingStart⟩
```

This was a pragmatic choice. Generating the in-bounds proof for
`Array.set` would require carrying a proof that `saveSimpleKey` was
previously called with `tokenIndex < tokens.size` — the same lifecycle
invariant discussed in §9.1. Using `setIfInBounds` defers this concern:
the function returns unchanged tokens if out-of-bounds, and Lean's
`Array.size_setIfInBounds` lemma gives `size_eq` unconditionally.

For monotonicity proofs (`scanValuePrepare_tokens_monotonic`) this was a
clean win — `simp [Array.size_setIfInBounds]` closes the goal. For prefix
preservation, the key library lemma is:

```
Array.getElem_setIfInBounds : (a.setIfInBounds i v)[j] = if i = j then v else a[j]
```

This `if i = j` branch is exactly where the stale-key invariant matters:
we need `i ≠ j` to conclude the prefix is unchanged, which requires
`idx ≥ s.tokens.size > j`.

### 9.3  Where the Filter Lives: `scanFiltered`, Not `scan`

The design (§4.4) placed the placeholder filter inside `scan`:

```lean
def scan (input : String) :=
  let rawTokens ← scanLoop s (fuel * 4)
  .ok (rawTokens.filter (·.val != .placeholder))
```

We initially implemented this, and it **broke 9 proof files**. Every
existing proof pattern-matches on `scan input`:

```lean
match scanFiltered input with
| .ok tokens => ...
```

Changing `scan`'s return type from raw tokens to filtered tokens meant
every `scanLoop` lemma (which talks about raw tokens) required a bridging
lemma to relate raw and filtered arrays. The cascade was extensive —
monotonicity, prefix preservation, size bounds all needed filter-aware
variants.

The solution was to leave `scan` unchanged (returning raw tokens) and
introduce a **wrapper function** `scanFiltered`:

```lean
def scanFiltered (input : String) :=
  match scan input with
  | .ok tokens => .ok (tokens.filter (fun t => t.val != .placeholder))
  | .error e => .error e
```

All callers that *consume* the token stream (parser, tests, `#guard`
helpers) use `scanFiltered`. All *proofs* reason about `scan` directly.
The bridge between the two is a thin composition layer in
`ScannerEmitBridge.lean`.

**Lesson**: *Separate the verification interface from the consumption
interface.* Proofs want to reason about the raw data structure (append-
only array with placeholders). Consumers want the clean stream. These are
different APIs and should be different functions.

### 9.4  The Unforeseen `lastRealTokenVal?` Helper

The design's risk table (§7) included "Placeholder tokens leak to parser"
but missed a subtler interaction: **the scanner itself reads the last
token** for flow-entry comma detection.

`scanFlowEntry` checks whether the last token is a leading comma or a
consecutive comma:

```lean
let lastTok := s.tokens.back?
if lastTok matches some t && (t.val == .flowSequenceStart || ...) then
  -- leading comma error
```

After the refactoring, `saveSimpleKey` pushes 2 placeholders at the end
of the array. When `scanFlowEntry` runs, `tokens.back?` returns a
`.placeholder`, not the last *real* token. This caused 2 test failures
(9MAG:0 "leading comma" and CTN5:0 "consecutive commas") — the scanner
silently accepted invalid input.

The fix was a small helper:

```lean
def lastRealTokenVal? (s : ScannerState) : Option YamlToken :=
  let n := s.tokens.size
  -- Skip up to 2 trailing placeholders
  if h : n > 0 then
    let last := s.tokens[n - 1]
    if last.val != .placeholder then some last.val
    else if h2 : n > 1 then
      let prev := s.tokens[n - 2]
      if prev.val != .placeholder then some prev.val
      else none
    else none
  else none
```

**Lesson**: *A refactoring that changes array contents can break any code
that reads from the array, not just code that writes to it.* The design
focused on write-side changes (saveSimpleKey, scanValuePrepare) and
missed read-side consumers within the scanner itself.

### 9.5  Branch Merging Simplified Proofs

The original `saveSimpleKey` had 4 branches: `explicitKeyLine` (identity),
`simpleKeyAllowed && inFlow` (push 2 + flow metadata), `simpleKeyAllowed
&& !inFlow` (push 2 + block metadata), and default (identity). During
implementation we noticed the flow and non-flow branches are **identical**
at the token level — both push the same 2 placeholders with the same
`tokenIndex` calculation. Only `simpleKeyStack` handling differs, which
we removed earlier in the project.

Merging to 3 branches (`explicitKeyLine → rfl`, `simpleKeyAllowed →
push 2`, `else → rfl`) reduced WellFormed proof obligations from
`split <;> simp_all` ×3 to ×2, and made `saveSimpleKey_preserves_prefix`
cleaner: only one non-trivial branch instead of two identical ones.

**Lesson**: *Before proving properties of branching code, check whether
branches can be merged.* A proof over N branches costs O(N); merging
identical branches is free simplification.

### 9.6  Lean 4 Idioms Learned the Hard Way

#### Dependent array rewriting

`rw [h]` where `h : v.tokens = s.tokens` **fails** when the goal contains
array indexing `v.tokens[i]'proof`. The error is "motive is not type
correct" — Lean can't construct the rewrite motive because the index
bound proof depends on the array being rewritten.

Two workarounds:

- **`simp only [h]`**: Works because `simp` handles dependent types
  more carefully than `rw`.
- **`obtain ⟨rfl, _⟩ := h`**: Substitutes `v` for `s` everywhere,
  including in proof terms. The `rfl` pattern triggers `subst` which
  handles dependent types correctly.

The `rw`/`simp` distinction bit us repeatedly. A typical pattern:

```lean
-- FAILS: rw [h_skip]
-- where h_skip : v.tokens = s.tokens
-- and goal contains v.tokens[i]'(by omega)

-- WORKS:
simp only [h_skip]
```

#### `split` only peels the outermost `if`

When `saveSimpleKey` had nested `if`s:

```lean
if explicitKeyLine then ...
else if simpleKeyAllowed then ...   -- pushes tokens
else ...
```

A single `split` only case-splits on `explicitKeyLine`. To reach the
inner `simpleKeyAllowed` branch, we needed a second `split` inside the
`else` case. The proof structure:

```lean
unfold saveSimpleKey
split
· rfl                                     -- explicitKeyLine
· split
  · dsimp only []                         -- simpleKeyAllowed: the interesting case
    rw [Array.getElem_push, dif_pos ...]
    rw [Array.getElem_push, dif_pos ...]
  · rfl                                   -- default
```

#### `simp only [lemma]` has stealth dsimp effects

In `preprocess_tokens_mono`, the proof includes:

```lean
have h_sk := saveSimpleKey_tokens_monotonic
  { unwindIndents v v.col with needIndentCheck := false }
simp only [needIndentCheck_update_tokens] at h_sk
```

The `needIndentCheck_update_tokens` lemma proves
`{ s with needIndentCheck := b }.tokens = s.tokens`, and `simp` rewrites
through the `with` record update. Removing this `simp` (even though the
linter flags the lemma as "unused") causes the subsequent `omega` to fail.

The reason: `simp` also performs definitional simplification as a side
effect. Without it, `h_sk` talks about
`(saveSimpleKey { ... needIndentCheck := false ... }).tokens.size` and
`omega` can't relate it to `(unwindIndents v v.col).tokens.size`. The
`simp` normalizes the record literal so omega sees the connection.

This is a case where the linter is technically right (the named lemma
doesn't fire as a rewrite rule) but the `simp` call is load-bearing.

#### `congrArg Array.size h` for safe size extraction

When `h : s1 = expr` and we need `s1.tokens.size = expr.tokens.size`,
`congrArg Array.size` doesn't work because `h` equates `ScannerState`s,
not `Array`s. Instead:

```lean
have := congrArg (·.tokens.size) h  -- fails: elaboration issues with dot notation
```

The working pattern is to first get `h_skip : v.tokens = s.tokens` via
a dedicated lemma, then `congrArg Array.size h_skip`.

### 9.7  The Proof That Wrote Itself

Once `preprocess_preserves_prefix` was proven, `scanLoop_preserves_tokens`
(the recursive case) became **three lines**:

```lean
rename_i s' h_next
have h_s_mono := scanNextToken_adds_tokens s s' h_next
have h_i_lt_s' : i < s'.tokens.size := by omega
have ⟨h_i_lt_tokens, h_eq_s'⟩ := IH s' tokens h i h_i_lt_s'
have h_prefix := scanNextToken_preserves_prefix s s' h_next i h_bound
exact ⟨h_i_lt_tokens, h_eq_s'.trans h_prefix⟩
```

This validates the design's core thesis: once the structural obstacle is
removed, proofs compose naturally. `scanLoop` is an inductive fold over
`scanNextToken` calls; the proof is the obvious composition of the
single-step lemma with the induction hypothesis.

The sorry in `scanNextToken_preserves_prefix` doesn't block this
compositionality — it's a localized gap that, when filled, will close
both `scanLoop_preserves_tokens` and its downstream consumers
automatically.

### 9.8  Score-Keeping: Design Predictions vs Reality

| Design Prediction (§4.6) | Outcome |
|---------------------------|---------|
| `insertAt_tokens_size`: deleted | ✅ Deleted |
| `insertAt_preserves_wellFormed`: deleted | ✅ Deleted |
| `scanValuePrepare_tokens_monotonic`: simplified | ✅ `simp [Array.size_setIfInBounds]` |
| `scanNextToken_preserves_prefix`: "true and provable" | ⚠️ True but needs invariant precondition |
| `scanLoop_preserves_tokens`: "follows from IH" | ✅ 6-line proof (modulo sorry in prereq) |
| `scan_positions_ordered`: "natural induction" | ❌ Not yet attempted |
| `saveSimpleKey_preserves_tokens` → `adds_two_tokens` | ✅ Now `saveSimpleKey_tokens_monotonic` (≥) |
| `preprocess_tokens_mono`: adjust for +2 | ✅ Adjusted |
| Placeholder filtering in `scan` | ⚠️ Moved to `scanFiltered` wrapper |
| No mention of scanner-internal reads | ❌ Required `lastRealTokenVal?` |

**Batting average**: 6 correct, 2 partially correct, 2 missed entirely.
The misses were both about *where the abstraction boundary falls* — the
design assumed the scanner only *writes* to the token array, but it also
*reads* from it (scanFlowEntry) and *carries state across calls* (stale
simple keys).

### 9.9  What We Would Do Differently

1. **Carry the invariant from the start.** The `simpleKey.tokenIndex ≥
   tokens.size` invariant should have been part of the `ScannerState`
   well-formedness definition from the beginning, not discovered during
   proof attempt. This would have made `scanNextToken_preserves_prefix`
   provable immediately.

2. **Audit all reads, not just writes.** Before predicting proof outcomes,
   `grep` for every site that reads from `tokens` — not just those that
   modify it. The `scanFlowEntry` issue could have been anticipated with
   a 30-second search.

3. **Prototype the hard proof first.** We proved all the "easy" lemmas
   (monotonicity, base cases) before attempting prefix preservation.
   Attempting `scanNextToken_preserves_prefix` first would have surfaced
   the stale-key issue earlier and informed the design of the invariant.

4. **Use `setIfInBounds` from the start.** The design specified
   `Array.set` with proofs; we switched to `setIfInBounds` during
   implementation. Starting with the weaker operation would have saved
   a round of proof refactoring.
