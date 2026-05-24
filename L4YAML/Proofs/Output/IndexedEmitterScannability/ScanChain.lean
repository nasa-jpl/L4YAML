/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.Basic

/-! # `IndexedEmitterScannability.ScanChain` — Phase 3 Step 6f.3b3 staging

**Status**: staging file (skeleton). Populated incrementally as
`Proofs/Output/EmitterScannability.lean`'s §3 prelude (scanner-state
utility lemmas + `ScanChain` inductive machinery) is ported to the
indexed substrate.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§3 prelude — scanner-state utility lemmas** (legacy lines
    842–1300, ~460 LOC). Per-stage forward-step lemmas
    (`scanLoop_two_iter`, `scanLoop_step_eq`, `scanLoop_step`,
    `scanLoop_fuel_mono`, `scanLoop_eof`, `scanLoop_eof_eq`),
    `dispatchContent_quote`, scalar-source preservation lemmas,
    `CharsFromOffset_length_le`, `scanDoubleQuoted_emitScalar_ok`,
    `scanNextToken_eof`, `peek_none_of_empty_surf`,
    `ScannerSurfCorr_transfer`, `emitScalar_toList`,
    `emitScalar_utf8ByteSize_ge`, etc.

  - **`ScanChain` inductive** (legacy lines 1185–1306, ~120 LOC).
    `ScanChain s n s'` (a fueled chain of `scanNextToken` successes),
    transitivity, single-step, `to_scanLoop` / `to_scanLoop_exists`,
    `scanNextToken_preserves_bound`, `bound_invariant`, `fuel_bound`.

The `ScanChain` inductive is the centerpiece — it lets emitter-side
proofs reason about scanner runs as composable proof objects (rather
than fuel-recursion gymnastics). The indexed twin's inductive is
keyed on `ScannerStateIx input` (input-indexed scanner states), so
chains over different input strings have distinct types.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

namespace L4YAML.Proofs.Indexed.EmitterScannability.ScanChain

-- (content to be added incrementally in 6f.3b3.scanchain sub-step)

end L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
