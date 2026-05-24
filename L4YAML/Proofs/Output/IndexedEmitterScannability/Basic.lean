/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness

/-! # `IndexedEmitterScannability.Basic` — Phase 3 Step 6f.3b3 staging

**Status**: staging file (skeleton). Populated incrementally as
`Proofs/Output/EmitterScannability.lean`'s value-level §1 + §2 lemmas
are ported to the indexed substrate.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§1 Escape Character Properties** (legacy lines 76–139, ~64 LOC).
    Pure value-level facts about `escapeChar c` —
    `escapeChar_passthrough_is_valid`, `escapeChar_output_nbJson`. No
    scanner state involved; ports verbatim (namespace only).

  - **§2 Emitter Output Properties** (legacy lines 140–841, ~700 LOC).
    Properties of `emit v` / `escapeString` outputs needed for scanner
    acceptance: `emit_nonempty`, `escapeString_foldl_shift`,
    `escapeString_nil`, `escapeString_cons`, first-character
    properties (`escapeChar_head_not_quote`,
    `escapeChar_head_not_linebreak`), `escapeString_all_nbJson`,
    `escapeString_no_linebreak`, hex-escape mechanics
    (`scannerHexCheck`, `hexNibble_*`, `hex_two_foldl_bound`,
    `escapeChar_hex_structure`), and the
    `collectDoubleQuotedLoop_escapeString_succeeds` core loop lemma.

These lemmas are scanner-substrate-independent; the indexed twin is
mostly a namespace + import update rather than a re-proof. The
section break here matches the legacy file's `§1` / `§2` markers
exactly so cross-references remain readable.

## Phase 3 Step 6f cutover

At cutover (6f.3c), this directory + aggregator is renamed
`Proofs/Output/EmitterScannability/` (overwriting the legacy single-
file `EmitterScannability.lean`) and the namespace
`L4YAML.Proofs.Indexed.EmitterScannability` reverts to
`L4YAML.Proofs.EmitterScannability`.

## Multi-file decomposition rationale

See Blueprint Reflection 108 — the legacy 10741-LOC monolith is split
across `Basic / ScanChain / FlowMonoChain / FilteredGrowth /
EmitScans / ParseStream / RoundTrip`, with each file scoped to one
architectural concern (escape-character primitives / chain inductive
machinery / flow-monotonic chain reasoning / filter-growth lemmas /
emit-scan acceptance / emit-parse pipeline / round-trip + universal
roundtrip). The largest sub-file (`FlowMonoChain.lean`, ~3800 LOC
target) is still substantial but ~3× more navigable than the legacy
monolith.
-/

namespace L4YAML.Proofs.Indexed.EmitterScannability.Basic

-- (content to be added incrementally in 6f.3b3.basic sub-step)

end L4YAML.Proofs.Indexed.EmitterScannability.Basic
