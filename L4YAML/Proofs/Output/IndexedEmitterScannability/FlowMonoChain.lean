/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.ScanChain

/-! # `IndexedEmitterScannability.FlowMonoChain` — Phase 3 Step 6f.3b3 staging

**Status**: staging file (skeleton). Populated incrementally as
`Proofs/Output/EmitterScannability.lean`'s §3 `FlowMonoChain` core is
ported to the indexed substrate. **This is the largest sub-file
(~3800 LOC target)** — it carries the bulk of the legacy proof's
flow-level state propagation infrastructure.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **`FlowMonoChain` inductive + helpers** (legacy lines 1319–1388,
    ~70 LOC). `FlowMonoChain fl₀ s n s'` (a `ScanChain` where every
    intermediate state has `flowLevel ≥ fl₀`), `.toScanChain`,
    `.flowLevel_ge_start` / `_end`, `.single`, `.trans`, `.weaken`,
    `.tokens_mono`.

  - **`SimpleKeyAboveFloor` predicate + maintenance** (legacy lines
    1388–1805, ~420 LOC). Flow-level-aware simple-key invariant.
    Constructors (`SimpleKeyAboveFloor_of_cleared_preserved`,
    `_of_preserved`, `_of_endLine_update`, `_of_flow_open`,
    `_of_flow_close`); preprocess + dispatch maintenance
    (`preprocess_preserves_flowLevel`, `preprocess_maintains_SKAF`,
    `dispatchStructural_maintains_SKAF`,
    `dispatchFlowIndicators_maintains_SKAF`,
    `dispatchBlockIndicators_maintains_SKAF`,
    `dispatchContent_maintains_SKAF`); `scanNextToken_maintains_SKAF`.

  - **FlowMonoChain prefix preservation** (legacy lines 1806–5586,
    ~3780 LOC — the *single biggest section* of the legacy file).
    Per-stage `_preserves_dp`, `_preserves_indents`, sync proofs,
    Step-4 prefix preservation: `scanNextToken_preserves_prefix_of_SKAF`,
    `scanNextToken_prefix_and_SKAF_inv`,
    `dispatchFlowIndicators_preserves_sync`,
    `scanNextToken_preserves_sync`,
    `FlowMonoChain_preserves_raw_prefix`, `scanFiltered_of_chain`,
    `scanFiltered_of_chain_eq`, etc.

## Why this sub-file is the largest

The flow-monotonic-chain machinery is the proof framework's most
complex single concern: it tracks scanner state through arbitrarily
long sequences of `scanNextToken` calls while preserving multiple
simultaneous invariants (flow level, simple-key stack floor,
emitted-token prefix, indent stack, dispatch-presence). Splitting it
further would fragment a cohesive proof skeleton (each preservation
lemma chains into the next via shared invariant accumulators), but
the indexed port may sub-divide once the structure is concrete —
e.g. `FlowMonoChain/Preserve.lean` (~1500 LOC),
`FlowMonoChain/Maintenance.lean` (~1100 LOC),
`FlowMonoChain/Sync.lean` (~1200 LOC).

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

-- (content to be added incrementally in 6f.3b3.flowmono sub-step)

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
