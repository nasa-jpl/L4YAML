/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain

/-! # `IndexedEmitterScannability.FilteredGrowth` — Phase 3 Step 6f.3b3 staging

**Status**: staging file (skeleton). Populated incrementally as the
filter-monotonicity / first-filtered-token / dispatch-level filtered
growth lemmas are ported to the indexed substrate.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **First-filtered-token lemmas for flow-content scanners** (legacy
    lines 5587–5899, ~313 LOC). Tier-2-Turn-1 lemmas connecting per-
    scanner first-filtered-token shapes to the dispatch-level
    classification (used by `scanFiltered_emitScalar_content` and
    siblings).

  - **Filtered token array growth infrastructure** (legacy lines
    5900–6070, ~170 LOC). `Array_setIfInBounds_filter_mono`,
    `preprocess_filtered_mono`, `allowDir_ite_filter_mono`,
    `List_filter_length_ge_one`, `filtered_grows_of_extended_prefix`,
    `filtered_grows_of_any_new`.

  - **Per-dispatch-layer filtered growth lemmas** (legacy lines
    6071–6758, ~688 LOC). `scanDocumentStart_filtered_grows`,
    `scanDocumentEnd_filtered_grows`, `scanYamlDirective_new_token_eq`,
    `scanTagDirective_new_token_eq`, `scanDirective_filtered_grows`,
    `dispatchStructural_filtered_mono`,
    `dispatchFlowIndicators_filtered_grows`,
    `scanBlockEntry_filtered_grows`, `scanKey_filtered_grows`,
    `scanValue_filtered_grows`, `dispatchBlockIndicators_filtered_grows`,
    `dispatchContent_new_not_placeholder`,
    `dispatchContent_filtered_grows`.

  - **Dispatch-level filtered growth (Turn 3)** (legacy lines
    6759–6908, ~150 LOC).
    `scanNextToken_via_flow_dispatch_filtered_grows`,
    `scanNextToken_via_block_dispatch_filtered_grows`,
    `scanNextToken_via_content_dispatch_filtered_grows`,
    `scanNextToken_filtered_grows_in_flow`.

These lemmas establish that the filtered (placeholder-stripped) token
array grows monotonically through scanner stages — a prerequisite for
proving `scanFiltered (emit v)` produces non-empty / structurally
correct token sequences.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

namespace L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

-- (content to be added incrementally in 6f.3b3.filteredgrowth sub-step)

end L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
