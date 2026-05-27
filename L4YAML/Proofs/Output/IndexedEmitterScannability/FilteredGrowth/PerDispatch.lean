/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.PerDispatch.StructFlow
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.PerDispatch.BlockContent

/-! # `FilteredGrowth.PerDispatch` — re-export shim

The `.perdispatch` material is split into one file per sub-session
under `FilteredGrowth/PerDispatch/`. Importing this module pulls in
everything; importing sub-files directly is also fine. The
namespace `L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth`
is preserved.

## Sub-sessions (Phase 3 Step 6f.3b3.filteredgrowth.perdispatch)

  - `PerDispatch/StructFlow.lean` — structural + flow-indicator
    per-dispatch filtered growth (legacy lines 6071–6362). Ships
    `scanDocumentStart_filtered_growsIx`,
    `scanDocumentEnd_filtered_growsIx`,
    `scanYamlDirective_new_token_eqIx`,
    `scanTagDirective_new_token_eqIx`,
    `scanDirective_filtered_growsIx`,
    `dispatchStructural_filtered_monoIx`,
    `dispatchFlowIndicators_filtered_growsIx`.
  - `PerDispatch/BlockContent.lean` — block-indicator + content
    per-dispatch filtered growth (legacy lines 6364–6757). Ships
    `scanBlockEntry_filtered_growsIx`, `scanKey_filtered_growsIx`,
    `scanValue_filtered_growsIx`,
    `dispatchBlockIndicators_filtered_growsIx`,
    `dispatchContent_new_not_placeholderIx`,
    `dispatchContent_filtered_growsIx` (plus the §0 shape helpers
    `scanBlockEntryIx_tokens_eq` / `scanKeyIx_tokens_eq`).

With both sub-files landed, `.perdispatch` closes: 2/2 sub-sessions.

See `Basic.lean` for the directory-wide cutover plan.
-/
