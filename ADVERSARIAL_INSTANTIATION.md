# Adversarial Instantiation — Application to L4YAML

Application of the [Adversarial Instantiation methodology](../../.claude/ADVERSARIAL_INSTANTIATION.md)
to the lean4-yaml-verified.iterators project (v0.4.7).

## Triage: When to Audit vs. When to Prove Directly

Not every sorry'd theorem warrants adversarial instantiation. The decision is a 2×2 matrix
of **statement risk** (could the theorem be false?) and **proof cost** (how hard to prove?):

```
                        Proof Cost
                    LOW              HIGH
                ┌────────────┬─────────────────┐
Statement  LOW  │  PROVE     │  PROVE          │
Risk            │  directly  │ (audit optional)│
                ├────────────┼─────────────────┤
           HIGH │  AUDIT     │  AUDIT          │
                │  then      │  first, then    │
                │  PROVE     │  PROVE          │
                └────────────┴─────────────────┘
```

High statement risk + low proof cost → audit is cheap insurance, do both.
Low statement risk + high proof cost → proof effort is the bottleneck, skip audit.
High statement risk + high proof cost → **audit is critical** — don't invest weeks in
proving a false statement.

### Statement Risk Indicators (fast to assess: ~30 seconds each)

| Indicator | Risk level | How to check |
|-----------|-----------|--------------|
| `∀` over positions/indices in arrays | **HIGH** | Scan for `∀ k, lo ≤ k → k < hi → P tokens[k]` |
| `∀` over scanner/parser states | **HIGH** | Universal over `ScannerState` or `ParseState` |
| Postcondition strengthened recently | **HIGH** | Was a field added to the predicate without a matching hypothesis? |
| Existential in conclusion | **MEDIUM** | `∃ s', f s = ok s' ∧ P s'` — the existence claim itself could fail |
| Pure arithmetic on list/array folds | **LOW** | `fbb(lo,hi) = fbb(lo,mid) + fbb(mid,hi)` — correct by construction |
| Single-function unfold | **LOW** | `scanBlockEntry s = ok s' → P s'` — one function, no composition |

### Proof Cost Indicators (fast to assess: ~30 seconds each)

| Indicator | Cost level | How to check |
|-----------|-----------|--------------|
| Estimated ≤ 25 LOC | **LOW** | See Est. LOC in sorry inventory |
| No loops in the function | **LOW** | Direct unfold + field access |
| Single dispatch branch | **LOW** | One function, no case explosion |
| Requires loop invariant | **HIGH** | `skipToContent`, `unwindIndents`, scalar loops |
| Requires recursive/inductive reasoning | **HIGH** | Nested collections, fuel sufficiency |
| Depends on 2+ sorry'd lemmas | **HIGH** | Blocked until dependencies are cleared |

### Decision rule

1. Check statement risk indicators (~30 sec). If ≥ 1 HIGH indicator → **AUDIT**.
2. If no HIGH risk indicators, check proof cost. If LOW → **PROVE directly** (skip audit).
3. If HIGH proof cost + MEDIUM risk → **AUDIT** (cheap insurance before expensive proof).
4. If LOW proof cost + HIGH risk → **AUDIT then PROVE** (audit catches bugs fast, proof is easy).

**Time budget**: Adversarial instantiation should take ≤ 30 minutes per theorem (writing
`#eval`/`#guard` checks). If it takes longer, the theorem's predicates may not be
computationally tractable for testing — fall back to careful manual review of the
statement.

## Current Sorry Inventory: Triage Results (21 sorrys)

### Category 1: PROVE directly (11 theorems, ~$250 LOC)

These are low-risk, low-to-medium cost. Skip adversarial instantiation.

| # | Theorem | Why PROVE | Est. LOC |
|---|---------|-----------|----------|
| 9i | `flowBracketBalance_compose` | Pure list fold arithmetic. Partition foldl. | 15–25 |
| 9j | `flowBracketBalance_push` | Pure array push doesn't affect prior slice. | 15–25 |
| 9k | `parseFlowSequenceLoop_emitter_ok` h_bal (×2) | Direct corollary of `_compose`. `rw; ring`. | 10–20 |
| 9l | `parseFlowMappingLoop_emitter_ok` h_bal (×2) | Same pattern. | 10–20 |
| — | `scanBlockEntry_filtered_grows` | Single function, one `emit .blockEntry`. | 15–25 |
| — | `scanKey_filtered_grows` | Single function, one `emit .key`. | 15–25 |
| — | `scanValue_filtered_grows` | Single function + `setIfInBounds`. | 20–30 |
| — | `dispatchContent_filtered_grows` | Dispatch + per-function composition. | 30–50 |
| — | `scanNextToken_filtered_grows` (structural case) | `scanDirective` branch; vacuous for emitter output. | 10–20 |
| — | `dispatchFlowIndicators_preserves_bound` | One branch (flowEntry), injection + field access. | 10–20 |
| — | `scanValue_BoundInv` | No loops, field updates + advance. | 40–80 |

#### Category 1 accomplishments

All 11 Category 1 theorems have been addressed:

| # | Theorem | Status | Notes |
|---|---------|--------|-------|
| 9i | `flowBracketBalance_compose` | **PROVEN** | List fold partition via `List.take_append_drop` |
| 9j | `flowBracketBalance_push` | **PROVEN** | Array push doesn't affect prior slice |
| 9k | `parseFlowSequenceLoop_emitter_ok` h_bal (×2) | **PROVEN** | Corollary of `_compose` |
| 9l | `parseFlowMappingLoop_emitter_ok` h_bal (×2) | **PROVEN** | Same pattern |
| — | `scanBlockEntry_filtered_grows` | **PROVEN** | `filtered_grows_of_any_new` + `emit_tokens_push` |
| — | `scanKey_filtered_grows` | **PROVEN** | Same pattern |
| — | `scanValue_filtered_grows` | **PROVEN** | Complex: `setIfInBounds` + `Array_setIfInBounds_filter_mono` |
| — | `dispatchContent_filtered_grows` | **PROVEN** | Used helper `dispatchContent_new_not_placeholder` |
| — | `scanNextToken_filtered_grows` (directive case) | **→ Cat 2** | Reclassified: unknown directives emit 0 tokens |
| — | `dispatchFlowIndicators_preserves_bound` | **PROVEN** | Injection + field access |
| — | `scanValue_BoundInv` | **PROVEN** | No loops, field updates + advance |

10 of 11 proven. 1 reclassified to Category 2 (the directive case in `scanNextToken_filtered_grows`
requires knowing that emitter-produced inputs don't contain unknown `%RESERVED` directives).

#### Category 1 reflections

**What worked:**
- The `filtered_grows_of_any_new` lemma pattern was highly reusable across all `*_filtered_grows` proofs.
- Per-scanner `_adds_one_token` and `_preserves_prefix` lemmas from ScannerCorrectness.lean composed cleanly.
- `Array_setIfInBounds_filter_mono` handled the `scanValue` case where a `.placeholder` token is overwritten.

**What didn't:**
- `simp only [Except.ok.injEq] at h` inside `<;>` blocks can fail when `h` has already been simplified in a prior step. The `<;>` combinator applies to post-split goals where `h` may no longer contain `Except.ok`.
- `simp only [bind, Except.bind]` vs `simp only [Bind.bind, Except.bind]` — both work in isolation but can fail inside large proofs where the hypothesis has already been modified by earlier simp steps. The root cause was the `<;>` combinator, not the simp lemma choice.
- `dsimp only []` after `unfold scanNamedTag` in a goal context: `scanNamedTag` has nested `let` bindings that `simp only []` can't handle but `dsimp only []` reduces correctly.

**Lessons:**
1. When using `split at h <;> (tactic_seq)`, ensure `tactic_seq` is idempotent — it runs on each branch independently, so tactics that already succeeded (like `simp [Except.ok.injEq]`) must not fail when re-run on the post-split state.
2. The `dispatchContent_new_not_placeholder` helper (proving the newly-added token is non-placeholder) was the hardest single theorem — it required unfolding 7 different content scanners through their `emitAt` calls to extract the actual token value.

### Category 2: AUDIT then PROVE (10 theorems, ~$1500 LOC)

These have universal quantifiers over states/positions/values and/or complex invariants.
Adversarial instantiation should be applied **before** investing proof effort.

| # | Theorem | Risk factor | Audit approach | Est. LOC |
|---|---------|-------------|----------------|----------|
| 9e | `scanNextToken_prefix_and_sk_inv` | `∀ s` × disjunctive invariant | Run `scanNextToken` on states with various `sk/ek` configs, check prefix + invariant | 50–100 |
| 9g | `emitList_body_filtered_characterization` | `∀ positions` (ALREADY CAUGHT BUG) | Re-test with 3-level nesting after bracketBalance fix | 40–80 |
| 9h | `emitPairList_body_filtered_characterization` | `∀ positions` (same class) | Re-test with nested maps-in-seqs, seqs-in-maps | 40–80 |
| 9a | `parseStream_emitSequence` (h_pnok sorry) | Parser succeeds on all content-start tokens | `#eval` parseNode at each content-start position in scanned emitter output | 200–400 |
| 9b | `parseStream_emitMapping` (h_pnok sorry) | Same for mappings | Same approach | 200–400 |
| 9c | `emit_roundtrip_sequence_content_eq` | End-to-end content fidelity, `∀ items` | `#eval parseYamlRaw (emit [nested, mixed, values])` and check equality | 150–300 |
| 9d | `emit_roundtrip_mapping_content_eq` | End-to-end for mappings | Same | 150–300 |
| — | `preprocess_preserves_bound` | Loops (`skipToContent`, `unwindIndents`) | Construct states with deep indent stacks, check BoundInv | 80–120 |
| — | `dispatchStructural_preserves_bound` | `scanDirective` loops | Test with ≥5 %YAML/%TAG directives | 60–80 |
| — | `dispatchContent_preserves_bound` | ALL scalar scanner loops | Run each scalar scanner on long/edge-case strings, check BoundInv | 100–150 |

## Adversarial Test Suite Design

### Priority 1: Theorems 9g, 9h (previously caught bug)

These are the highest-value audit targets — we already found one false statement here.
Re-verify after the `flowBracketBalance` fix:

**Inputs:**
```
-- Flat (should pass): ["a", "b", "c"]
-- 1-level nesting: [["a", "b"], "c"]
-- 2-level nesting: [[["a"]]]
-- Mixed: [{"k": "v"}, ["a"]]
-- Map-in-map: {"a": {"b": "c"}}
-- Previously-failing: [{"k1": "v1", "k2": "v2"}]
```

**Check:** For each `flowEntry` at `flowBracketBalance = 0`, verify the next filtered token
is a content-start (scalar/flowSeqStart/flowMapStart) for sequences, or `.key` for mappings.

### Priority 1: Accomplishments

**Test suite:** `Tests/AdversarialInstantiation.lean` — 188 checks, all passing.
Integrated into CI via `lakefile.toml` (`adversarialinstantiation` target) and
the suite runner's verified test suites.

**Test coverage (9g — `emitList_body_filtered_characterization`):**
- Flat sequences: 1, 2, 3 items
- 1-level nesting: `[["a","b"],"c"]`, `[{"k":"v"},"c"]`
- 2-level nesting: `[[["a"]]]`, `[[["a"]],"b"]`
- Mixed: `[{"k":"v"},["a"]]`, `["plain",["a","b"],{"x":"y"}]`
- Previously-failing: `[{"k1":"v1","k2":"v2"}]`, `[{"k1":"v1","k2":"v2"},"after"]`
- Deep: `[[[[deep]]]]`, `[{"a":[{"b":"c"}]}]`
- Edge cases: empty scalar, special chars with escapes, 6-item list

**Test coverage (9h — `emitPairList_body_filtered_characterization`):**
- Single/multi pair: 1, 2, 3 pairs
- Nested values: sequences in values, mappings in values, sequences as keys
- Mixed: `{"items":["x","y"],"count":"2"}`, `{"data":[{"id":"1"},{"id":"2"}],"meta":{"ver":"1.0"}}`
- Deep: `{"k":[[["deep"]]]}`, `{"a":[["1"]],"b":{"c":{"d":"e"}}}`
- Edge cases: empty key, empty value, special chars, 6-pair mapping

**Key verification points:**
1. First body token is content-start (9g) or `.key` (9h) — verified for all inputs
2. Outer-level `flowEntry` (bracketBalance = 0) is always followed by content-start (9g) or `.key` (9h)
3. Inner `flowEntry` tokens (bracketBalance > 0, inside nested brackets) are correctly excluded
4. The `flowBracketBalance` computation correctly distinguishes nesting levels

**Tokens observed (representative):**
- `[{"k1":"v1","k2":"v2"},"after"]` → `streamStart [ { key scalar(k1) : scalar(v1) , key scalar(k2) : scalar(v2) } , scalar(after) ] streamEnd`
  - Inner `,` at position 8 has bal=1 (inside `{}`), correctly skipped
  - Outer `,` at position 12 has bal=0, next is `scalar(after)` ✓

### Priority 1: Reflections

**Confidence level:** HIGH. The test suite covers the exact input patterns that previously
triggered a false statement (nested mappings inside sequences where inner `flowEntry` tokens
at non-zero bracket balance were incorrectly required to be followed by content-start). The
`flowBracketBalance` fix (theorems 9i–9l, now proven) correctly distinguishes inner vs outer
commas.

**What was verified:**
- The `flowBracketBalance` predicate accurately identifies outer-level commas
- All 7 content scanner types (scalar variants, nested `[`, nested `{`) produce the expected
  first filtered token
- The `, ` separator between items produces exactly one `.flowEntry` token at the right
  nesting level

**Residual risk:** LOW. The adversarial inputs include the previously-failing case and several
more complex nesting patterns. No new failures discovered. The theorem statements align with
observed scanner behavior.

### Priority 2: Theorems 9c, 9d (end-to-end round-trip)

These are directly checkable via `emit → scanFiltered → parseYamlRaw → contentEq`:

**Inputs:**
```
-- Scalars: "hello", "with \"escape\"", ""
-- Sequences: ["a"], ["a", "b"], [["nested"]]
-- Mappings: {"k": "v"}, {"k1": "v1", "k2": "v2"}
-- Nested: [{"k": ["a", "b"]}, "c"]
-- Deep: [[[[["deep"]]]]]
```

**Check:** `contentEq (parseYamlRaw (emit v)).get! v = true`

### Priority 2: Accomplishments

### Priority 2: Reflections

### Priority 3: Theorems 9a, 9b (parser fuel sufficiency)

The claim `4 * tokens.size + 4` as fuel bound is testable:

**Check:** `parseFlowSequence tokens 0 (4 * tokens.size + 4)` returns `.ok` for scanned
emitter output. Also test with `4 * tokens.size + 3` (one less) to verify tightness.

### Priority 3: Accomplishments

### Priority 3: Reflections

### Priority 4: Theorem 9e (scanner prefix invariant)

**Inputs:** Construct `ScannerState` values with:
- `simpleKey.possible = true, tokenIndex < n` (restored from flowStack)
- `explicitKeyLine = some _` (after scanValue)
- Both conditions false (normal flow)

**Check:** After `scanNextToken`, verify prefix preserved AND disjunctive condition maintained.

### Priority 4: Accomplishments

### Priority 4: Reflections

### Priority 5: ScannerBound theorems (preprocess, structural, content)

**Inputs:** States with:
- 10+ indent stack entries (deep `unwindIndents`)
- Multi-line scalars (long scanner loops)
- UTF-8 multi-byte characters (byte offset arithmetic)

**Check:** `BoundInv` fields (offset ≤ utf8ByteSize, isValidPos, etc.) after processing.

## Implementation Plan

All adversarial instantiation tests live in `Tests/AdversarialInstantiation.lean` and are
integrated into CI:

- **Build target:** `adversarialinstantiation` (in `lakefile.toml` `defaultTargets`)
- **Standalone runner:** `Tests/AdversarialInstantiation/Runner.lean` → `.lake/build/bin/adversarialinstantiation`
- **Suite runner:** Included via `Tests.AdversarialInstantiation.collectTests` in `Tests/SuiteRunner/Main.lean`
- **Report:** Appears in HTML/JSON reports as "Adversarial Instantiation Tests (sorry audit)"

For each priority:
1. Add test functions (`test9g`, `test9h`, ...) and register in `collectTests`
2. Use `TestCollector` + `check`/`checkM` macros for VerifiedSuiteResult integration
3. Any check failure → investigate and fix the theorem statement before proving
4. All checks pass → proceed to proof with increased confidence

**Status:** Priority 1 complete (188/188). Priorities 2–5 to be added incrementally.

### Priority 5: Accomplishments

### Priority 5: Reflections
