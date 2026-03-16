2026-03-15

## Current State

**Build:** 322/322 ✔, **9 sorry warnings** (all in ParserGrammable.lean C2 chain).
**Guards:** 122/125 passing (3 commented out — scanner colon-chain bug: 58MP, 5T43, DBG4).
**Test suite:** 857 passed, 12 failed (same 3 tests × 4 stages), 151 skipped.

## Remaining Sorrys — Priority Order

| # | Sorry | Approach | Difficulty |
|---|-------|----------|------------|
| 1 | `prepareDocumentState_tokens_preserved` | Unfold `prepareDocumentState` (directives + tryConsume chain). Mechanical do-notation unfolding. | **Easy** |
| 2 | `parseDocument_tokens_preserved` | Chain `prepareDocumentState_tokens_preserved` + `parseNode_tokens_preserved`. Depends on #1. | **Easy** |
| 3 | `parseFlowMapping_wb` | Mirrors `parseFlowSequence_wb` (proved). Same structure: advance past `flowMappingStart`, loop invariant, advance past `flowMappingEnd`, net-zero flowNesting. | **Medium** |
| 4 | `parseNodeContent_wb` | Dispatches to the 5 proved `_wb` lemmas + scalar/alias/empty cases. Monadic unfolding of `parseNodeContent`. | **Medium** |
| 5 | `parseImplicitBlockSequence_wb` | Block-level loop with `parseNode` IH. Similar pattern to `parseBlockSequence_wb` (proved). | **Medium** |
| 6 | `parseDocument_value_cases` | Do-notation decomposition — identify emptyNode vs parseNode branch. | **Medium** |
| 7 | `parseNode_wb_all` | Strong induction. Fills in once `parseNodeContent_wb` + flow WB lemmas are proved. | **Easy once deps done** |
| 8 | `parseStream_doc_from_parseDocument` | `Range.forIn` loop invariant. Lean 4 for-loop reasoning is non-trivial. | **Hard** |
| 9 | `parseStream_output_aliases_resolve` | Scanner doesn't validate alias ordering (§7.1). Needs scanner-level invariant. | **Hard / spec gap** |
| 10 | `parseStream_output_anchors_wellformed` | `∀ inFlow` in `WellFormedAnchors` is unsatisfiable for cross-context aliasing. Semantic gap. | **Hard / spec gap** |

**Recommended path:** #1 → #2 → #3 → #4 → #5 → #7 → #6, which would reduce sorrys from 9 to 2 (+ the 2 semantic spec-gap sorrys).

