/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth

/-! # `IndexedEmitterScannability.EmitScans` — Phase 3 Step 6f.3b3 staging

**Status**: staging file (skeleton). Populated incrementally as the
`ScanChainGrew` strict-variant track + the `EmitScansInFlow` main
theorem family are ported to the indexed substrate.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **`ScanChainGrew` inductive (strict-variant track)** (legacy lines
    6909–7002, ~95 LOC). `ScanChainGrew p s n s'` (a `ScanChain` plus
    a witness that *at least one* `p`-satisfying token was added).
    Helpers: `.toScanChain`, `.single`, `.trans`,
    `ScanChainGrew_filtered_grows`, `ScanChainGrew_of_scanNextToken_eq`.

  - **`EmitScansInFlow` predicate + per-value-form lemmas** (legacy
    lines 7003–7625, ~623 LOC). The main predicate
    `EmitScansInFlow v`: scanning `emit v` (inside a flow context)
    produces a non-empty `ScanChainGrew`. Body lemmas:
    `emit_list_scans_in_flow` family — `emitList_scans_empty`,
    `emitList_scans_nonempty`, `emitPairList_first_char`,
    `isValueCandidate_of_peekAt_blank`,
    `scanNextToken_flow_value` (the dispatcher's flow-value entry
    point).

  - **`EmitPairListScansInFlow` + main proof** (legacy lines
    7626–8013, ~388 LOC). The dual predicate for key-value pair
    lists; `emitPairList_scans_empty`, `emitPairList_scans_nonempty`,
    and the main theorem `emit_scans_in_flow` (induction over
    `Grammable v inFlow`).

  - **`emit_produces_valid_yaml`** (legacy lines 8281–8399, ~120 LOC).
    Top-level composition: `scanFiltered (emit v)` succeeds and
    produces a valid token stream.

This sub-file is the heart of the emitter-scannability proof — it
shows that the canonical emitter's output is exactly what the
scanner accepts.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

namespace L4YAML.Proofs.Indexed.EmitterScannability.EmitScans

-- (content to be added incrementally in 6f.3b3.emitscans sub-step)

end L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
