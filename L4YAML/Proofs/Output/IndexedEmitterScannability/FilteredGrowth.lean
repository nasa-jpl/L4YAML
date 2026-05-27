/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.FirstFiltered
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.Infra
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.PerDispatch

/-! # `IndexedEmitterScannability.FilteredGrowth` — re-export shim

The `FilteredGrowth` machinery is split into one file per sub-session
under `FilteredGrowth/`. Importing this module pulls in everything;
importing sub-files directly is also fine. The namespace
`L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth` is
preserved.

## Sub-sessions (Phase 3 Step 6f.3b3.filteredgrowth)

  - `FilteredGrowth/FirstFiltered.lean` — first-filtered-token lemmas
    for flow-content scanners (legacy lines 5587–5899). Ships
    `scanFlowSequenceStartIx_first_filtered_token`,
    `scanFlowMappingStartIx_first_filtered_token`,
    `scanDoubleQuotedIx_first_filtered_token`, plus emitter shape
    helpers (`emit_first_char`, `emitList_first_char`,
    `emitList_toList_ne_nil`), `emit_tokens_pushIx`, and the generic
    `Array_filter_prefix_of_raw_prefix` array lemma.
  - `FilteredGrowth/Infra.lean` — filtered token array growth
    infrastructure (legacy lines 5900–6070). Ships
    `List_filter_set_length_monoIx`, `Array_setIfInBounds_filter_monoIx`,
    `preprocess_filtered_monoIx`, `allowDir_ite_filter_monoIx`,
    `List_filter_length_ge_oneIx`,
    `filtered_grows_of_extended_prefixIx`, `filtered_grows_of_any_newIx`.
  - `FilteredGrowth/PerDispatch.lean` — re-export shim for per-
    dispatch-layer filtered growth, sub-split under
    `FilteredGrowth/PerDispatch/` (Step 6f.3b3.filteredgrowth.perdispatch).
    Currently ships:
      * `PerDispatch/StructFlow.lean` *(legacy 6071–6362)* —
        structural + flow-indicator dispatch lemmas
        (`scanDocumentStart_filtered_growsIx`,
        `scanDocumentEnd_filtered_growsIx`,
        `scanYamlDirective_new_token_eqIx`,
        `scanTagDirective_new_token_eqIx`,
        `scanDirective_filtered_growsIx`,
        `dispatchStructural_filtered_monoIx`,
        `dispatchFlowIndicators_filtered_growsIx`).

Remaining sub-sessions (to be added incrementally):

  - **`.perdispatch.blockcontent`** *(legacy 6364–6757, ~395 LOC)* —
    block-indicator + content per-dispatch filtered growth
    (`scanBlockEntry_filtered_growsIx`, `scanKey_filtered_growsIx`,
    `scanValue_filtered_growsIx`,
    `dispatchBlockIndicators_filtered_growsIx`,
    `dispatchContent_new_not_placeholderIx`,
    `dispatchContent_filtered_growsIx`).
  - **`.turn3`** *(legacy 6759–6908, ~150 LOC)* — dispatch-level
    filtered growth: `scanNextToken_via_flow_dispatch_filtered_growsIx`
    and three siblings.

See `Basic.lean` for the directory-wide cutover plan.
-/
