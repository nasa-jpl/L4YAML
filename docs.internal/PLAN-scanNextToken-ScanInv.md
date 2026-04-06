# Plan: Proving `scanNextToken_preserves_ScanInv`

## Goal

Convert the private axiom at `ScannerCorrectness.lean:5038` into a theorem:

```lean
private axiom scanNextToken_preserves_ScanInv :
    ∀ (s s' : ScannerState),
      ScanInv s → scanNextToken s = .ok (some s') → ScanInv s'
```

where `ScanInv s` = tokens ordered by offset ∧ all token offsets ≤ `s.offset`.

## Invariant reminder

```lean
private def ScanInv' (tokens : Array (Positioned YamlToken)) (offset : Nat) : Prop :=
  (∀ i j : Fin tokens.size, i.val < j.val →
    tokens[i].pos.offset ≤ tokens[j].pos.offset) ∧
  (∀ i : Fin tokens.size, tokens[i].pos.offset ≤ offset)

private def ScanInv (s : ScannerState) : Prop := ScanInv' s.tokens s.offset
```

Both parts are needed:
- **Ordered**: new tokens must sort after (or equal to) existing tokens
- **Bounded**: all token offsets must be ≤ the final `s'.offset`

## Architecture of `scanNextToken`

```
scanNextToken s
  ├── scanNextToken_preprocess s
  │     ├── skipToContent s           -- tokens unchanged, offset increases
  │     ├── unwindIndents s col       -- emits blockEnd tokens at s.offset
  │     └── saveSimpleKey s           -- pushes 2 placeholders at s.offset
  │
  ├── scanNextToken_dispatchStructural s c
  │     ├── scanDocumentStart s       -- unwindIndents + emit documentStart
  │     ├── scanDocumentEnd s         -- unwindIndents + emit documentEnd
  │     └── scanDirective s           -- emit versionDirective or tagDirective
  │
  ├── scanNextToken_dispatchFlowIndicators s c
  │     ├── scanFlowSequenceStart s   -- emit flowSequenceStart + advance
  │     ├── scanFlowSequenceEnd s     -- emit flowSequenceEnd + advance
  │     ├── scanFlowMappingStart s    -- emit flowMappingStart + advance
  │     ├── scanFlowMappingEnd s      -- emit flowMappingEnd + advance
  │     └── scanFlowEntry s           -- emit flowEntry + advance
  │
  ├── scanNextToken_dispatchBlockIndicators s c
  │     ├── scanBlockEntry s          -- emit blockSequenceStart? + blockEntry
  │     ├── scanKey s                 -- emit blockMappingStart? + key
  │     └── scanValue s               -- setIfInBounds placeholders + emit value
  │
  └── scanNextToken_dispatchContent s c
        ├── scanAnchorOrAlias s       -- emitAt startPos (anchor/alias)
        ├── scanTag s                 -- emitAt startPos (tag)
        ├── scanBlockScalar s         -- emitAt startPos (scalar)
        ├── scanDoubleQuoted s        -- emitAt startPos (scalar)
        ├── scanSingleQuoted s        -- emitAt startPos (scalar)
        └── scanPlainScalar s         -- emitAt startPos (scalar)
```

## Token mutation taxonomy

There are exactly 4 ways tokens are modified in the scanner:

| Operation | What it does | Offset of new/changed token |
|-----------|-------------|---------------------------|
| `emit tok` | `tokens.push {pos := s.currentPos, val := tok}` | `s.offset` (= `s.currentPos.offset`) |
| `emitAt pos tok` | `tokens.push {pos := pos, val := tok}` | `pos.offset` (saved `startPos` ≤ `s.offset`) |
| `saveSimpleKey` | `tokens.push ph \|>.push ph` (2 placeholders) | `s.offset` (= `s.currentPos.offset`) |
| `setIfInBounds idx v` | `tokens[idx] := v` (overwrite placeholder) | `s.simpleKey.pos.offset` (= save-time offset) |

**Key insight**: ALL new token offsets are either `s.offset` at call time or a previously-saved
`startPos.offset ≤ s.offset` (because the scanner only advances forward). `setIfInBounds`
only overwrites tokens that were placeholders created at the same offset.

## Existing proof infrastructure

### Already proven ScanInv preservation (in ScannerCorrectness.lean)

| Theorem | Line | What it covers |
|---------|------|---------------|
| `emit_preserves_ScanInv` | ~4950 | `ScanInv s → ScanInv (s.emit tok)` |
| `advance_preserves_ScanInv` | ~4983 | `ScanInv s → ScanInv s.advance` |
| `field_update_preserves_ScanInv` | ~4994 | `s'.tokens = s.tokens → s'.offset = s.offset → ScanInv s'` |
| `unwindIndentsLoop_preserves_ScanInv` | ~5008 | Induction on fuel |
| `unwindIndents_preserves_ScanInv` | ~5016 | Wrapper || `emitAt_preserves_ScanInv` | ~5028 | Phase 1 ✅ — `emitAt` with `h_pos` + `h_ge` |
| `emitAt_preserves_ScanInv_eq` | ~5075 | Phase 1 ✅ — simplified when `pos.offset = s.offset` |
| `saveSimpleKey_preserves_ScanInv` | ~5083 | Phase 1 ✅ — 3-branch: no-op / 2×emit / no-op |
| `setIfInBounds_preserves_ScanInv'` | ~5106 | Phase 1 ✅ — single replacement, same offset |
| `setIfInBounds_twice_preserves_ScanInv'` | ~5144 | Phase 1 ✅ — double replacement, different indices |
| `scanValuePrepare_preserves_ScanInv` | ~5166 | Phase 1 ✅ — 6 branches with `h_sk` hypothesis |
### Offset preservation (in ScannerProgress.lean)

| Theorem | What it proves |
|---------|---------------|
| `advance_offset_ge` | `s.advance.offset ≥ s.offset` |
| `emit_offset` | `(s.emit tok).offset = s.offset` |
| `saveSimpleKey_offset` | `(saveSimpleKey s).offset = s.offset` |
| `pushSequenceIndent_offset` | `(pushSequenceIndent s col).offset = s.offset` |
| `pushMappingIndent_offset` | `(pushMappingIndent s col).offset = s.offset` |

### Token preservation (in ScannerCorrectness.lean)

| Theorem | What it proves |
|---------|---------------|
| `advance_preserves_tokens` | `s.advance.tokens = s.tokens` |
| `skipToContent_preserves_tokens` | `(skipToContent s).tokens = s.tokens` (through all sub-loops) |
| `saveSimpleKey_tokens_monotonic` | `s.tokens.size ≤ (saveSimpleKey s).tokens.size` |
| `scanValuePrepare_tokens_monotonic` | Only uses `setIfInBounds` (no push) |
| `emitAt_preserves_tokens_at` | Existing tokens at indices < size preserved |
| `emit_preserves_tokens_at` | Same for `emit` |

### Prefix preservation (`_preserves_prefix` family — 30 theorems)

Every scan function has `X_preserves_prefix`: tokens below index `n` are unchanged.
This proves the ordering sub-invariant is preserved for existing tokens.

## Proof strategy

### Phase 1: New primitive lemmas — ✅ COMPLETE (7 theorems, ~200 lines)

These are the missing building blocks needed before composing per-function proofs.

> **Status**: All 7 theorems proven and verified. 191/191 build, 869/869 tests, 0 sorry, 0 warnings.
> See [Phase 1 Reflections](#phase-1-reflections) for lessons learned.

#### 1a. `emitAt_preserves_ScanInv` — ✅

**Actual signature** (3 hypotheses, not 2 as initially sketched):
```lean
theorem emitAt_preserves_ScanInv (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (h : ScanInv s) (h_pos : pos.offset ≤ s.offset)
    (h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ pos.offset) :
    ScanInv (s.emitAt pos tok)
```

**Approach**: Mirror `emit_preserves_ScanInv`. The structure is identical — `emitAt` is just
`emit` with an explicit position. Need to prove:
- Ordering: existing `emitAt_preserves_tokens_at` + `h_pos` (the new token's offset ≤ all
  future tokens since it's ≤ s.offset ≤ s'.offset). Actually ordering requires the new
  token offset ≥ all existing token offsets. This holds because `h_pos : pos.offset ≤ s.offset`
  and from `h.2` we have `∀ i, tokens[i].offset ≤ s.offset`, **but we also need
  `pos.offset ≥ tokens[last].offset`**. This IS guaranteed because `pos` was saved from
  `s.currentPos` at some earlier state whose offset was ≥ all tokens at that time (by ScanInv).
  However, new tokens may have been added since then (by `saveSimpleKey`), so we need to
  be careful.

**Refined approach**: `emitAt_preserves_ScanInv` needs an additional hypothesis:
```lean
(h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ pos.offset)
```
This can be derived from the compound invariant at the time `startPos` was saved, plus
the fact that tokens added between save and emit also have offset ≤ pos.offset (because
`saveSimpleKey` pushes at the same offset, and no other tokens are added before `emitAt`).

**Alternative (simpler)**: Since `emitAt startPos` always happens after `saveSimpleKey` (which
adds placeholders at the same offset as `startPos`), and no additional tokens are pushed
between `saveSimpleKey` and `emitAt`, ALL token offsets ≤ `startPos.offset` ≤ `s.offset`.
So we can use the same proof structure as `emit_preserves_ScanInv` with `pos.offset` in place
of `s.offset`, provided we also prove `pos.offset` ≥ all existing token offsets.

Actually, the cleanest approach is:
```lean
theorem emitAt_preserves_ScanInv (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (h : ScanInv s) (h_pos : pos.offset ≤ s.offset)
    (h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ pos.offset) :
    ScanInv (s.emitAt pos tok)
```

This is direct and mirrors the `emit` proof.

#### 1b. `saveSimpleKey_preserves_ScanInv` — ✅

```lean
theorem saveSimpleKey_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (saveSimpleKey s)
```

**Approach**: `saveSimpleKey` either:
- Returns `s` unchanged (if `explicitKeyLine` matches or `!simpleKeyAllowed`) → trivial
- Pushes 2 placeholders at `s.currentPos` (= `s.offset`) → like 2 consecutive `emit`s

For the push case:
- Ordering: new tokens at `s.offset` ≥ all existing (by `h.2`)
- Bounded: new tokens at `s.offset` = `s.offset` (by `saveSimpleKey_offset`)
- Use `emit_preserves_ScanInv` twice, or prove directly

#### 1c. `setIfInBounds_preserves_ScanInv'` — ✅

**Actual signature** (simpler than planned — direct index bound, not `Option`):
```lean
theorem setIfInBounds_preserves_ScanInv' (tokens : Array (Positioned YamlToken))
    (offset : Nat) (idx : Nat) (v : Positioned YamlToken)
    (h : ScanInv' tokens offset)
    (h_idx : idx < tokens.size)
    (h_off : v.pos.offset = tokens[idx].pos.offset) :
    ScanInv' (tokens.setIfInBounds idx v) offset
```

**Bonus**: `setIfInBounds_twice_preserves_ScanInv'` (not in original plan) for
two consecutive replacements at different indices:
```lean
theorem setIfInBounds_twice_preserves_ScanInv' (tokens : Array (Positioned YamlToken))
    (offset : Nat) (idx1 idx2 : Nat) (v1 v2 : Positioned YamlToken)
    (h : ScanInv' tokens offset)
    (h_idx1 : idx1 < tokens.size) (h_idx2 : idx2 < tokens.size)
    (h_off1 : v1.pos.offset = tokens[idx1].pos.offset)
    (h_off2 : v2.pos.offset = tokens[idx2].pos.offset)
    (h_ne : idx1 ≠ idx2) :
    ScanInv' (tokens.setIfInBounds idx1 v1 |>.setIfInBounds idx2 v2) offset
```

**Approach**: `setIfInBounds` overwrites `tokens[idx]` with `v` which has the same
`.pos.offset` as the original placeholder (since `s.simpleKey.pos = st.currentPos` from
save time, same as the placeholder's pos). Since the offset doesn't change, both ordering
and boundedness are preserved.

**Note**: We actually need to prove that `scanValuePrepare` preserves `ScanInv`, which is
more specific. The `setIfInBounds` call uses `s.simpleKey.pos` as the position, and the
original placeholder was also at that position. The key fact is:
`(tokens.setIfInBounds idx v).size = tokens.size` (from stdlib) and
if `idx < tokens.size`: `(tokens.setIfInBounds idx v)[i] = if i = idx then v else tokens[i]`.
Since `v.pos.offset = tokens[idx].pos.offset`, ordering is preserved.

#### 1d. `scanValuePrepare_preserves_ScanInv` — ✅

**Actual signature** (takes explicit `h_sk` hypothesis, not hypothesis-free as initially sketched):
```lean
theorem scanValuePrepare_preserves_ScanInv (s : ScannerState) (h : ScanInv s)
    (h_sk : s.simpleKey.possible = true →
      s.simpleKey.tokenIndex < s.tokens.size ∧
      s.simpleKey.tokenIndex + 1 < s.tokens.size ∧
      (∀ (h1 : s.simpleKey.tokenIndex < s.tokens.size),
        s.tokens[s.simpleKey.tokenIndex].pos = s.simpleKey.pos) ∧
      (∀ (h2 : s.simpleKey.tokenIndex + 1 < s.tokens.size),
        s.tokens[s.simpleKey.tokenIndex + 1].pos = s.simpleKey.pos)) :
    ScanInv (scanValuePrepare s)
```

**Approach**: `scanValuePrepare` uses `setIfInBounds` to overwrite placeholder positions,
but the replacement values use `s.simpleKey.pos` — the same position as the placeholder.
Need to show that after `setIfInBounds`, the token offsets are unchanged at every index.

This requires a **SimpleKey invariant**: the placeholder at `s.simpleKey.tokenIndex` has
position `s.simpleKey.pos`. We would either need to carry this as part of `ScanInv` or
prove it from the construction chain.

**Alternative (weaker but sufficient)**: Prove that `scanValuePrepare` doesn't increase
`tokens.size` (already `scanValuePrepare_tokens_monotonic` exists) and that it preserves
the offset at every index. Since `setIfInBounds` only writes the same offset value,
all token offsets are preserved.

### Phase 2: Per-dispatcher ScanInv theorems (~5 theorems)

#### 2a. `preprocess_preserves_ScanInv`

```lean
theorem preprocess_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) (s' : ScannerState) (c : Char)
    (h_pre : scanNextToken_preprocess s = .ok (some (s', c))) :
    ScanInv s'
```

**Approach**: `preprocess` does:
1. `skipToContent s` → tokens unchanged, offset increases → `field_update_preserves_ScanInv`
   (with `skipToContent_preserves_tokens` and `skipToContent_offset_ge` — need to verify
   latter exists or prove it)
2. `unwindIndents s col` → already proven via `unwindIndents_preserves_ScanInv`
3. `saveSimpleKey s` → from Phase 1b
4. Field updates → `field_update_preserves_ScanInv`

Compose these sequentially.

**Missing lemma**: `skipToContent_offset_ge : (skipToContent s).offset ≥ s.offset`.
This should follow from `skipToContent` only advancing the scanner position. Need to check
if this exists in ScannerProgress.lean or needs to be proven.

#### 2b. `dispatchStructural_preserves_ScanInv`

```lean
theorem dispatchStructural_preserves_ScanInv (s : ScannerState) (c : Char)
    (h : ScanInv s) (s' : ScannerState)
    (h_dispatch : scanNextToken_dispatchStructural s c = .ok (some s')) :
    ScanInv s'
```

**Sub-cases**:
- `scanDocumentStart`: `unwindIndents` (proven) + `emit documentStart` (proven) +
  `advanceN 3` (proven) + field updates (proven)
- `scanDocumentEnd`: Same pattern
- `scanDirective`: `emit versionDirective/tagDirective` via `emitAt` + advances

Each requires composing existing lemmas. The `emitAt` cases need Phase 1a.

#### 2c. `dispatchFlowIndicators_preserves_ScanInv`

All 5 flow indicator functions follow the same pattern:
- `emit` (one token) + `advance` (one char) + field updates

Direct composition of `emit_preserves_ScanInv`, `advance_preserves_ScanInv`,
`field_update_preserves_ScanInv`.

#### 2d. `dispatchBlockIndicators_preserves_ScanInv`

- `scanBlockEntry`: `pushSequenceIndent` (field update) + `emit blockEntry` + `advance`
- `scanKey`: `pushMappingIndent` (field update) + `emit key` + `advance`
- `scanValue`: `scanValuePrepare` (Phase 1d) + `emit value` + `advance`

#### 2e. `dispatchContent_preserves_ScanInv`

All scanner functions save `startPos := s.currentPos`, then advance through content,
then `emitAt startPos tok`. Pattern:
1. `startPos.offset = s.offset` (at save time)
2. Scanner advances → `s'.offset ≥ s.offset ≥ startPos.offset`
3. `emitAt startPos` → needs Phase 1a with `h_pos : startPos.offset ≤ s'.offset`

The `h_ge` hypothesis (all existing token offsets ≤ `startPos.offset`) holds because:
- At save time, `ScanInv` gives `∀ i, tokens[i].offset ≤ s.offset = startPos.offset`
- Between save and `emitAt`, only `saveSimpleKey` may add tokens (at same offset)
- All intermediate operations preserve this

### Phase 3: Compose into `scanNextToken_preserves_ScanInv` (~1 theorem)

```lean
theorem scanNextToken_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_next : scanNextToken s = .ok (some s')) : ScanInv s'
```

**Approach**:
1. Unfold `scanNextToken`
2. Split on `preprocess` result → use Phase 2a for the intermediate state
3. Split on `dispatchStructural` → use Phase 2b or fall through
4. `allowDirectives` update → `field_update_preserves_ScanInv`
5. Split on `dispatchFlowIndicators` → Phase 2c
6. Split on `dispatchBlockIndicators` → Phase 2d
7. `dispatchContent` → Phase 2e

## Dependency graph

```
scanNextToken_preserves_ScanInv
  ├── preprocess_preserves_ScanInv
  │     ├── skipToContent_preserves_ScanInv (NEW: from skipToContent_preserves_tokens + offset_ge)
  │     ├── unwindIndents_preserves_ScanInv (EXISTS)
  │     └── saveSimpleKey_preserves_ScanInv ✅
  │
  ├── dispatchStructural_preserves_ScanInv
  │     ├── scanDocumentStart_preserves_ScanInv (NEW)
  │     │     ├── unwindIndents_preserves_ScanInv (EXISTS)
  │     │     ├── emit_preserves_ScanInv (EXISTS)
  │     │     └── advance_preserves_ScanInv (EXISTS)
  │     ├── scanDocumentEnd_preserves_ScanInv (NEW)
  │     └── scanDirective_preserves_ScanInv (NEW)
  │           └── emitAt_preserves_ScanInv ✅
  │
  ├── dispatchFlowIndicators_preserves_ScanInv
  │     └── 5× (emit + advance + field_update) — all EXISTS
  │
  ├── dispatchBlockIndicators_preserves_ScanInv
  │     ├── scanBlockEntry_preserves_ScanInv (NEW)
  │     ├── scanKey_preserves_ScanInv (NEW)
  │     └── scanValue_preserves_ScanInv (NEW)
  │           └── scanValuePrepare_preserves_ScanInv ✅
  │                 ├── setIfInBounds_preserves_ScanInv' ✅
  │                 └── setIfInBounds_twice_preserves_ScanInv' ✅
  │
  └── dispatchContent_preserves_ScanInv
        └── 7× emitAt_preserves_ScanInv ✅
              ├── scanAnchorOrAlias_preserves_ScanInv
              ├── scanTag_preserves_ScanInv (+ 3 sub-tag variants)
              ├── scanBlockScalar_preserves_ScanInv
              ├── scanDoubleQuoted_preserves_ScanInv
              ├── scanSingleQuoted_preserves_ScanInv
              └── scanPlainScalar_preserves_ScanInv
```

## Estimated theorem count

| Phase | New theorems | Approach |
|-------|-------------|----------|
| **1a** `emitAt_preserves_ScanInv` | ~~1~~ 2 ✅ | + `emitAt_preserves_ScanInv_eq` convenience wrapper |
| **1b** `saveSimpleKey_preserves_ScanInv` | 1 ✅ | 3-way split: unchanged / 2× `emit` at `s.offset` |
| **1c** `setIfInBounds_preserves_ScanInv'` | ~~1~~ 2 ✅ | + `setIfInBounds_twice_preserves_ScanInv'` for double replacement |
| **1d** `scanValuePrepare_preserves_ScanInv` | 2 ✅ | 6 branches; `h_sk` hypothesis; compose `setIfInBounds` + field updates |
| **2a** `preprocess_preserves_ScanInv` | 2 | `skipToContent + offset_ge` lemma + composition |
| **2b** structural dispatchers | 3 | `scanDocumentStart/End`, `scanDirective` |
| **2c** flow indicator dispatchers | 1 | Single theorem, 5 cases all emit+advance+field |
| **2d** block indicator dispatchers | 3 | `scanBlockEntry`, `scanKey`, `scanValue` |
| **2e** content dispatchers | 7–10 | Per-scanner + sub-tag variants |
| **3** composition | 1 | Top-level unfold + split |
| **Phase 1 subtotal** | **7 ✅** | |
| **Total** | **~24–28** (revised) | |

## Risk assessment

### Low risk (mechanical composition)

- **Flow indicators** (Phase 2c): All 5 follow emit+advance+field pattern. Proven primitives
  compose directly.
- **`saveSimpleKey_preserves_ScanInv`** (Phase 1b): 2 pushes at `s.offset` = 2× `emit`.
- **`advance`/`field_update`** compositions: Already proven.

### Medium risk (need careful offset tracking)

- **`emitAt_preserves_ScanInv`** (Phase 1a): Requires proving the saved `startPos.offset`
  ≥ all existing token offsets. This is true by ScanInv at save time, BUT we need to
  thread this through `saveSimpleKey` (which adds tokens at the same offset).
- **`scanValuePrepare_preserves_ScanInv`** (Phase 1d): Need to show `setIfInBounds`
  replaces placeholders with tokens having the same `.pos.offset`. This requires tracking
  that `s.simpleKey.pos` equals the placeholder's position. May need a **SimpleKey position
  invariant** as an additional hypothesis.
- **Content scanners** (Phase 2e): Each saves `startPos`, then calls internal loops
  (`collectAnchorNameLoop`, `scanDoubleQuotedBody`, etc.) that advance the offset. Need
  to show these loops don't add tokens (most have `_preserves_tokens` already proven).

### High risk (complex internal structure)

- **`scanBlockScalar`**: 5-phase pipeline with internal loops. Already has
  `scanBlockScalar_preserves_prefix` proven, but ScanInv needs the offset bound too.
  The `emitAt startPos` happens at the end, with `startPos` saved before all the
  header parsing and content collection.
- **`scanDirective`**: Three sub-functions (`scanYamlDirective`, `scanTagDirective`,
  wrapper). Each uses `emitAt startPos`. Need to compose through the helper chain.
  Already has `_monotonic` theorems.
- **`scanDocumentEnd`**: Contains a `skipToEndOfLine` check plus error validation
  after the `unwindIndents + emit` sequence. Need to track ScanInv through the
  validation branch.

## Recommended execution order

1. ~~**Phase 1a**: `emitAt_preserves_ScanInv` — unlocks all content scanner proofs~~ ✅
2. ~~**Phase 1b**: `saveSimpleKey_preserves_ScanInv` — unlocks preprocess proof~~ ✅
3. **Phase 2c**: `dispatchFlowIndicators_preserves_ScanInv` — easiest, builds confidence
4. **Phase 2a**: `preprocess_preserves_ScanInv` — needs 1b + skipToContent offset lemma
5. **Phase 2b**: `dispatchStructural_preserves_ScanInv` — needs 1a for directive emitAt
6. ~~**Phase 1c–1d**: `setIfInBounds` + `scanValuePrepare` — needed for scanValue~~ ✅
7. **Phase 2d**: `dispatchBlockIndicators_preserves_ScanInv` — needs 1d
8. **Phase 2e**: `dispatchContent_preserves_ScanInv` — needs 1a, most sub-theorems
9. **Phase 3**: Final composition

## Open questionsls 

1. **SimpleKey position invariant**: Do we need to thread
   `s.simpleKey.pos = s.tokens[s.simpleKey.tokenIndex].pos` through `ScanInv`? This
   is needed for `scanValuePrepare_preserves_ScanInv` to show `setIfInBounds` writes
   the same offset. Alternative: prove it locally from the `saveSimpleKey` construction.

2. **`skipToContent` offset monotonicity**: Is `(skipToContent s).ok.offset ≥ s.offset`
   already proven? If not, it needs to be added to ScannerProgress.lean (should follow
   from the whitespace-skipping loops only advancing).

3. **Error branches**: `scanNextToken` may return `.error` on some paths. We only need
   the `.ok (some s')` case, so errors are handled by contradiction (`simp at h_next`).
   But within dispatchers, some sub-calls return `Except` — need to split on those.

4. **`do` notation desugaring**: The dispatcher functions use `do` notation with monadic
   bind. Proof tactic is: `simp only [bind, Except.bind]` then `split`. This is the
   same pattern used in existing `_preserves_prefix` proofs.

---

## Phase 1 Reflections

Phase 1 delivered 7 theorems (vs. the estimated ~4–8) across ~200 lines of proof,
verified with 0 sorry, 0 warnings (191/191 build, 869/869 tests). This section records
unexpected challenges, simplifications, and idioms discovered.

### What the plan got right

- **`emitAt_preserves_ScanInv` signature**: The plan correctly anticipated needing the
  extra `h_ge` hypothesis (all existing token offsets ≤ `pos.offset`). The proof structure
  did mirror `emit_preserves_ScanInv` as predicted.
- **`saveSimpleKey` three-branch structure**: Straightforward — the push case reduced to
  two applications of `emit_preserves_ScanInv` exactly as planned.
- **SimpleKey position invariant as hypothesis**: The plan's Open Question #1 asked whether
  `h_sk` should be threaded through `ScanInv` or proven locally. We resolved it by making
  `scanValuePrepare_preserves_ScanInv` take an explicit `h_sk` hypothesis. This keeps
  `ScanInv` simple and pushes the burden to callers (Phase 2d: `scanValue`).

### What the plan missed

- **`setIfInBounds_twice_preserves_ScanInv'`**: The plan listed a single
  `setIfInBounds_preserves_ScanInv` theorem. In practice, `scanValuePrepare` does two
  consecutive `setIfInBounds` at different indices, requiring a separate composition
  lemma with an `h_ne : idx1 ≠ idx2` hypothesis. The intermediate array's element at
  `idx2` must be shown unchanged (via `if_neg`) before applying the single-step lemma
  a second time.
- **`emitAt_preserves_ScanInv_eq` convenience wrapper**: A common case where
  `pos.offset = s.offset` (e.g., `saveSimpleKey` placeholders, `emitAt s.currentPos`)
  needed a simpler signature without the `h_ge` hypothesis. The `h_ge` proof reduces
  to `Nat.le_of_lt_succ` from the `ScanInv` bound.
- **`ScanInv'` as the proof target**: Proofs targeting `ScanInv { s with tokens := ... }`
  hit Lean 4's struct elaboration limits. Working with `ScanInv' tokens offset` directly
  (via `show ScanInv' _ s.offset`) was essential. This pattern will recur in Phase 2.

### Unexpected challenges

1. **`Fin` vs `Nat` index mismatch in `setIfInBounds`**: `Array.getElem_setIfInBounds`
   takes `(hj : j < xs.size)` (bound against the *original* array size), but proof goals
   have `j < (xs.setIfInBounds i a).size`. Required an explicit `getElem_helper` lemma
   that rewrites via `Array.size_setIfInBounds` to bridge the gap. This will recur
   anywhere `setIfInBounds` is used.

2. **`omega` failure with `Fin.val` coercions**: Lean's `omega` tactic cannot reason
   through `Fin.val` coercions. Fix: extract raw `Nat` inequalities with
   `have hij' : i < j := hij` before invoking `omega`.

3. **Namespace scoping for `emitAt_preserves_tokens_at`**: This theorem lives inside
   the `ScanHelpers` namespace (ScannerCorrectness.lean L716–2279) and is inaccessible
   from Phase 1's location (outside that section). Rather than reorganizing the file,
   the proof uses direct unfolding: `unfold ScannerState.emitAt; simp only [Array.getElem_push]`.

4. **`simp [Ne.symm h_ne]` no-progress on `ite`**: When simplifying
   `if idx1 = idx2 then v1 else tokens[idx2]` with `h_ne : idx1 ≠ idx2`,
   `simp [Ne.symm h_ne]` fails. The working pattern is `if_neg h_ne` (or `exact if_neg h_ne`
   for the full equation), which directly collapses `if p then a else b` when `¬p` holds.

5. **5 build-fix cycles**: Despite careful planning, 5 iterations were needed. The main
   culprits were array indexing mechanics (challenges 1–2 above) and `show`/struct
   elaboration issues. Budget 2–3 build cycles per non-trivial theorem in later phases.

### Simplifications discovered

- **`saveSimpleKey` = two `emit`s**: The push-two-placeholders branch produces exactly
  `(s.emit .placeholder).emit .placeholder`. The proof is `emit_preserves_ScanInv` applied
  twice, then `show ScanInv' _ s.offset; exact h2` to match the struct shape. ~5 lines.
- **`emitAt` offset preservation is `rfl`**: `(s.emitAt pos tok).offset = s.offset` holds
  definitionally — no lemma needed (unlike `emit_offset` which exists but is also `rfl`).
- **`scanValuePrepare` false branches are trivial**: When `simpleKey.possible = false`,
  three sub-branches collapse to `field_update_preserves_ScanInv`, `emit_preserves_ScanInv`,
  or `exact h` (identity). Only the `possible = true` branches need `setIfInBounds` machinery.

### Idioms for Phase 2

These patterns should be applied systematically going forward:

| Pattern | When to use | Example |
|---------|-------------|---------|
| `show ScanInv' _ s.offset` | Goal is `ScanInv { s with tokens := ... }` | All `setIfInBounds`, `saveSimpleKey` proofs |
| `unfold Foo; simp only [Array.getElem_push]` | Need token access after `emit`/`emitAt` but helper is out of scope | `emitAt_preserves_ScanInv` |
| `if_neg h` over `simp [Ne.symm h]` | Collapsing `if p then a else b` with `¬p` | `setIfInBounds_twice` |
| `have hi' : i < xs.size := by rw [Array.size_setIfInBounds] at hi; exact hi` | Bridging `Fin` bounds across `setIfInBounds` | `setIfInBounds_preserves_ScanInv'` |
| `have hij' : i < j := hij` | Extracting `Nat` from `Fin` before `omega` | Any `Fin`-indexed ordering proof |
| `field_update_preserves_ScanInv _ _ h rfl rfl` | Struct update that only changes non-token/offset fields | `scanValuePrepare` false branches |

### Revised estimates for Phase 2

Based on Phase 1 experience:

- **Phase 2c** (flow indicators): Still low risk. Pure `emit + advance + field_update`
  composition. Expect 1 theorem, ~20 lines, 1 build cycle.
- **Phase 2a** (preprocess): Medium risk. Need `skipToContent_offset_ge` (new).
  Composition of 3 steps. Expect 2 theorems, ~40 lines, 2 build cycles.
- **Phase 2d** (block indicators): Medium risk. `scanValue` needs to provide `h_sk` —
  must trace `saveSimpleKey` placeholder positions through to `scanValuePrepare`. This
  is where Open Question #1 becomes concrete. Expect 3–4 theorems, ~80 lines, 3 cycles.
- **Phase 2b** (structural): Medium risk. `scanDirective` has 3 sub-functions with
  `emitAt`. Expect 3–4 theorems, ~60 lines, 2 cycles.
- **Phase 2e** (content): Highest risk. 7 scanner functions, each with internal loops.
  The `h_ge` hypothesis for `emitAt_preserves_ScanInv` must be threaded through
  `saveSimpleKey` + loop bodies. Expect 7–10 theorems, ~150 lines, 5+ cycles.

### Open questions resolved

1. **SimpleKey position invariant** (was Open Question #1): Resolved as an explicit
   `h_sk` hypothesis on `scanValuePrepare_preserves_ScanInv`. Not added to `ScanInv`.
   Phase 2d callers must prove it from `saveSimpleKey` construction.

### New open questions

5. **`h_sk` discharge in Phase 2d**: How to prove that `saveSimpleKey` establishes the
   `h_sk` precondition? The placeholders are pushed at `s.currentPos`, so
   `tokens[tokenIndex].pos = s.currentPos = simpleKey.pos`. Need to verify that no
   operation between `saveSimpleKey` and `scanValuePrepare` modifies those placeholder
   indices. Likely requires a `saveSimpleKey_placeholder_pos` lemma.

6. **`h_ge` discharge in Phase 2e**: For content scanners, `emitAt startPos` happens
   after `saveSimpleKey` adds tokens at `startPos.offset`. The `h_ge` hypothesis
   (`∀ i, tokens[i].offset ≤ startPos.offset`) must hold for the *post-saveSimpleKey*
   token array. This holds because `saveSimpleKey` pushes at `s.offset = startPos.offset`,
   but needs an explicit `saveSimpleKey_tokens_offset_le` lemma (or derive from
   `emit_preserves_ScanInv` intermediate states).

---

## Phase 2 Reflections

Phases 2a–2e collectively proved the remaining per-dispatcher ScanInv preservation
theorems. This section records the key challenges and patterns discovered.

### What the Phase 1 idioms bought us

The patterns documented in Phase 1 Reflections (especially the `show ScanInv' _ s.offset`
idiom, `Fin`-to-`Nat` extraction for `omega`, and the `field_update_preserves_ScanInv`
shortcut) applied without modification across all Phase 2 sub-proofs. The biggest
productivity gain was knowing to work with `ScanInv'` directly rather than through
the `ScanInv` struct wrapper.

### `split at h_ok` follows source pattern order

A critical discovery: when `split` branches on a `match` result from a `do`-notation
function, the goals appear in **source pattern order** (the order branches appear in
the Lean source), NOT in constructor order (`.ok` before `.error`). Mismatching the
branch order causes proofs to target the wrong goal. Diagnosis technique: insert
`exact h_ok` into a branch to see the actual goal type and match against it.

### `AllKeysValid` vs `SimpleKeyValid`

Initially attempted to track only `SimpleKeyValid` (single simple-key invariant),
but `scanNextToken` dispatches through `saveSimpleKey` which updates both the
current simple key AND the simple-key stack. The correct compound invariant is
`AllKeysValid` = `SimpleKeyValid ∧ SimpleKeyStackValid`, which tracks that all
token indices in both the current key and the stack remain within bounds. This
was the most significant design insight of Phase 2.

### `Except.map` requires `unfold`, not `simp`

`simp only [Except.map]` produces no progress; the function must be unfolded
with `unfold Except.map`. This pattern recurred across all dispatcher proofs
that use `Except.map` for pure post-processing after monadic scanner calls.

### Open questions resolved (from Phase 1)

- **Question 5 (`h_sk` discharge)**: Resolved by proving `saveSimpleKey_placeholder_pos`
  compositionally — the placeholder position equals `s.currentPos` at push time, and no
  operation between `saveSimpleKey` and `scanValuePrepare` modifies the placeholder indices.
- **Question 6 (`h_ge` discharge)**: Resolved by deriving from `ScanInv` at save time:
  since `emit` at `s.offset` preserves the bound and `saveSimpleKey` only pushes at
  `s.offset`, the post-save token array satisfies `h_ge` for the saved `startPos`.

---

## Phase 3 Reflections

Phase 3 replaced the last `private axiom scanNextToken_preserves_ScanInv` with a
proved theorem, achieving **0 axioms, 0 sorry** across the full 191-module build.

### Final composition structure

The top-level theorem unfolds `scanNextToken` into `preprocess → dispatch`, then
`split`s on each dispatcher result. Each branch delegates to the corresponding
Phase 2 theorem. The proof is ~30 lines of structured `case` analysis — mechanical
once all sub-theorems exist.

### Why the axiom was necessary during development

The axiom allowed proving downstream theorems (scanner correctness, token stream
validity) while the sub-proofs were under construction. Without it, the entire
proof chain would have been blocked by incomplete intermediate results. This
"axiom-as-interface" pattern is effective for large proof developments where the
leaf theorems require the most effort.

### Key metric

| Metric | Before Phase 3 | After Phase 3 |
|--------|---------------|---------------|
| Axioms | 1 | 0 |
| Sorry | 0 | 0 |
| Build modules | 191/191 | 191/191 |
| Tests | 869/869 | 869/869 |

---

## Phase 4 Reflections

Phase 4 extracted all 1917 `#guard` checks from the `Lean4Yaml/` library into
`Tests/Guards/`, separating proof artifacts from build-time regression tests.

### Motivation

`#guard` checks are kernel-evaluated at build time — they verify concrete computations
but are not part of the library's logical content (theorems, definitions, types). Moving
them to a separate test directory:
1. Keeps the library focused on specifications and proofs
2. Allows independent iteration on test coverage
3. Reduces recompilation when adding new guards
4. Makes the proof/test boundary explicit

### Structure

- **32 files** under `Tests/Guards/` mirroring the `Lean4Yaml/` directory structure
- **7 guard-only files** (SuiteGuards/\*, TestSuite.lean) moved wholesale
- **25 mixed files** had guards and guard-only private defs extracted
- **`Tests/Guards.lean`** hub file imports all 32 sub-modules
- **`Tests.Guards`** lean\_lib entry added to lakefile.toml

### Challenges

1. **Orphaned doc comments**: Extracting guard blocks left behind `/-- ... -/` doc
   comments that previously preceded guard-only private defs. In Lean 4, a doc comment
   MUST be followed by a declaration — orphaned ones cause `unexpected token` errors.
   Similarly, `/-! section header -/` comments with no content after them, and unclosed
   `/-!` blocks whose closing `-/` was part of the extracted text. Required manual review
   of ~10 source files.

2. **`open ... in` prefix lines**: The extraction script removed guard-only private defs
   but left behind `open Foo in` / `open Bar in` lines that scoped into the removed def.
   These `open ... in` constructs require a following command, so orphaned ones also
   cause syntax errors.

3. **Private def accessibility**: When a `private def` is used by BOTH guards AND theorems,
   it stays in the source file but becomes inaccessible from the guard file (since
   `private` is file-scoped in Lean 4). Fix: remove `private` from 5 such defs
   (`scannerEscapeChar`, `canonicalRoundTrips`, `digitOffset`, `twoLevels`, `threeLevels`).

4. **Missing `open` statements in guard files**: Guard-only private defs often referenced
   functions via scoped `open ... in` in the original source. The extraction script
   captured the namespace but not all `open` statements. Fix: add `open Lean4Yaml.TokenParser`
   to 4 guard files that use `parseYamlSingle`.

5. **Lake lean\_lib module discovery**: Initially used `name = "Tests.GuardChecks"` for the
   hub file, but the `Tests/Guards/*.lean` sub-modules were not in the `Tests.GuardChecks`
   namespace and Lake couldn't discover them. Fix: renamed hub to `Tests/Guards.lean` with
   `name = "Tests.Guards"` so sub-modules are properly scoped.

### Key metrics

| Metric | Before Phase 4 | After Phase 4 |
|--------|---------------|---------------|
| Build modules | 191/191 | 211/211 (+32 guard modules, −7 deleted) |
| `#guard` in Lean4Yaml/ | 1917 | 0 |
| `#guard` in Tests/Guards/ | 0 | 1917 |
| Tests | 869/869 | 869/869 |
| Sorry | 0 | 0 |
| Axioms | 0 | 0 |
