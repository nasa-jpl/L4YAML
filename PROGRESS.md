2026-03-17

## Current State

**Build:** 322/322 ✔, **5 sorry warnings** (all in ParserGrammable.lean C2 chain).
**Guards:** 362 active (65 Advanced + 83 Block + 16 Document + 96 Error + 44 Flow + 58 Scalar), 3 commented out (scanner colon-chain bug: 58MP, 5T43, DBG4).
**Test suite:** 857 passed, 12 failed (same 3 tests × 4 stages), 151 skipped.

## Recently Proved (since last update)

- `parseFlowSequence_wb` — proved via Pattern 5 resolution (else-branch returns `.error`, closed by `simp at h_ok`)
- `parseFlowSequenceLoop_wb` — loop invariant for flow sequence
- `parseImplicitBlockSequence_wb` — proved (same structure as `parseBlockSequence_wb`)
- `parseImplicitBlockSequenceLoop_wb` — loop invariant for implicit block sequence
- `FlowAwarePSV` hypothesis removed from entire block mapping chain (unused)
- `parseFlowMappingValue_wb` — value-side well-behavedness
- `parseExplicitKey_wb` — key-side well-behavedness (2nd-order Pattern 4 extraction)
- `parseFlowMappingLoop_wb` — flow mapping loop invariant (4 recursive goals via extracted helpers)
- `parseFlowMapping_wb` — wrapper theorem mirroring `parseFlowSequence_wb`
- `parseNodeContent_wb` — dispatches to 6 sub-parser `_wb` lemmas; added `h_matched : FlowBracketsMatched tokens` parameter

## New Findings (2026-03-16, 2nd investigation)

- First direct attempt at `parseFlowMapping_wb` was reverted; the file is back to a clean state with only the intended `sorry`s.
- The failed attempt confirmed that `parseFlowMapping_wb` wants the same proof shape as `parseFlowSequence_wb`, but the current file is missing two intermediate lemmas:
	- `parseFlowMappingValue_wb`
	- `parseFlowMappingLoop_wb`
- `parseFlowMappingValue_wb` is now proved and compiles cleanly. It establishes:
	- returned value is `Scannable` in block context
	- returned value is `Scannable` in flow context when `flowNesting > 0`
	- `flowNesting` is preserved
	- tokens are preserved
- Second pass on `parseFlowMappingLoop_wb` was also reverted after diagnostics. The blocker is now clearer:
	- the explicit-key branch is not a simple binary split
	- after consuming `.key`, the loop has three empty-key branches (`.value`, `.flowEntry`, `.flowMappingEnd`) plus the parsed-key branch
	- trying to treat that subtree as one branch causes `parseNodeWB_apply` to be fed equalities for `parseFlowMappingValue` instead of `parseNode`
	- the wrapper/helper design still looks right, but the loop proof needs those four post-key branches handled explicitly or via a dedicated local dispatch lemma
- The wrapper statement likely also wants an explicit
	`h_peek : ps.peek? = some .flowMappingStart`, exactly like `parseFlowSequence_wb`.
	Without that hypothesis, the `+1` flow-nesting step from the initial advance is awkward to recover from `h_ok` alone.
- Recommended second pass:
	1. Keep `parseFlowMappingValue_wb` as the stable helper.
	2. Re-attempt `parseFlowMappingLoop_wb` with a small local recurse lemma and explicit handling of the four post-key cases.
	3. Prove `parseFlowMapping_wb` as a thin wrapper mirroring `parseFlowSequence_wb`.

## Remaining Sorrys — Priority Order

| # | Sorry | Line | Approach | Difficulty |
|---|-------|------|----------|------------|
| 1 | `prepareDocumentState_tokens_preserved` | L2565 | Unfold `prepareDocumentState` (directives + tryConsume chain). Mechanical do-notation unfolding. | ✅ Proved |
| 2 | `parseDocument_tokens_preserved` | L2573 | Chain `prepareDocumentState_tokens_preserved` + `parseNode_tokens_preserved`. Depends on #1. | ✅ Proved |
| 3 | `parseFlowMapping_wb` | L2773 | ✅ Proved. Extracted `parseExplicitKey` (2nd-order Pattern 4 mitigation), then proved loop + wrapper. Added `h_peek` hypothesis. | ✅ Proved |
| 4 | `parseNodeContent_wb` | L2859 | ✅ Proved. Dispatches to 6 sub-parser `_wb` lemmas + scalar/empty cases. Added `h_matched` parameter. | ✅ Proved |
| 5 | `parseNode_wb_all` | L2933 | ✅ Proved. Wadler-style extraction of `validateNodeProps`, then `show`-based defeq matching to handle applyNodeFinalization expansion in goal. | ✅ Proved |
| 6 | `parseDocument_value_cases` | L2589 | Do-notation decomposition — identify emptyNode vs parseNode branch. | **Medium** |
| 7 | `parseStream_doc_from_parseDocument` | L2651 | `Range.forIn` loop invariant. Lean 4 for-loop reasoning is non-trivial. | **Hard** |
| 8 | `parseStream_output_aliases_resolve` | L2698 | Scanner doesn't validate alias ordering (§7.1). Needs scanner-level invariant. | **Hard / spec gap** |
| 9 | `parseStream_output_anchors_wellformed` | L2731 | `∀ inFlow` in `WellFormedAnchors` is unsatisfiable for cross-context aliasing. Semantic gap. | **Hard / spec gap** |

## Sub-parser WB Status

| Sub-parser | Status |
|------------|--------|
| `parseBlockSequence_wb` | ✅ Proved (loop invariant) |
| `parseBlockSequenceLoop_wb` | ✅ Proved |
| `parseBlockMapping_wb` | ✅ Proved (all sub-cases) |
| `parseBlockMappingLoop_wb` | ✅ Proved |
| `handleBlockMappingKeyEntry_wb` | ✅ Proved |
| `handleBlockMappingValueEntry_wb` | ✅ Proved |
| `parseFlowSequence_wb` | ✅ Proved (Pattern 5 resolution) |
| `parseFlowSequenceLoop_wb` | ✅ Proved |
| `parseImplicitBlockSequence_wb` | ✅ Proved |
| `parseImplicitBlockSequenceLoop_wb` | ✅ Proved |
| `parseSinglePairMapping_wb` | ✅ Proved |
| `parseFlowMapping_wb` | ✅ Proved (2nd-order Pattern 4 extraction) |
| `parseFlowMappingLoop_wb` | ✅ Proved |
| `parseFlowMappingValue_wb` | ✅ Proved |
| `parseExplicitKey_wb` | ✅ Proved |
| `parseNodeContent_wb` | ✅ Proved (dispatches to all sub-parser `_wb` lemmas) |
| `parseNode_wb_all` | ✅ Proved (Wadler-style validateNodeProps extraction + `show` defeq) |

**Recommended path:** #6, which would reduce sorrys from 4 to 3 (+ the 2 semantic spec-gap sorrys #8–#9). All sub-parser WB theorems, `parseNodeContent_wb`, and `parseNode_wb_all` are now proved.

