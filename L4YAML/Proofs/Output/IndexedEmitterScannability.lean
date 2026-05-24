/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.Basic
import L4YAML.Proofs.Output.IndexedEmitterScannability.ScanChain
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth
import L4YAML.Proofs.Output.IndexedEmitterScannability.EmitScans
import L4YAML.Proofs.Output.IndexedEmitterScannability.ParseStream
import L4YAML.Proofs.Output.IndexedEmitterScannability.RoundTrip

/-! # `IndexedEmitterScannability` — Phase 3 Step 6f.3b3 staging aggregator

**Status**: staging aggregator. Imports the seven indexed-twin sub-files
that will collectively replace the legacy 10741-LOC
`Proofs/Output/EmitterScannability.lean` at the 6f.3c cutover commit.

## Multi-file decomposition (Reflection 108)

The migration is organized across seven sub-files under
`Proofs/Output/IndexedEmitterScannability/` rather than mirroring the
legacy file's monolithic shape. The split is by *architectural
concern*, not by line count:

  | Sub-file                | Legacy lines | LOC est. | Concern                                          |
  |-------------------------|--------------|----------|--------------------------------------------------|
  | `Basic.lean`            |    76–841    |   ~700   | Escape char / string properties (value-level)   |
  | `ScanChain.lean`        |   842–1300   |   ~460   | `ScanChain` inductive + helpers                  |
  | `FlowMonoChain.lean`    |  1714–5586   |  ~3800   | `FlowMonoChain` + `SimpleKeyAboveFloor` (biggest)|
  | `FilteredGrowth.lean`   |  5587–6908   |  ~1320   | Per-stage `_filtered_grows` lemmas               |
  | `EmitScans.lean`        |  6909–8399   |  ~1490   | `ScanChainGrew` + `EmitScansInFlow` main thread  |
  | `ParseStream.lean`      |  8400–8874   |   ~440   | Emit → Scan → Parse pipeline + scalar content    |
  | `RoundTrip.lean`        |  8875–10741  |  ~1870   | Content fidelity + `universal_roundtrip`         |

Each sub-file imports its predecessor in the dependency chain
(`Basic → ScanChain → FlowMonoChain → FilteredGrowth → EmitScans →
ParseStream → RoundTrip`), so each can be developed against the
already-landed indexed proof infrastructure of the previous file.

At cutover (6f.3c), this aggregator is renamed
`Proofs/Output/EmitterScannability.lean` (overwriting the legacy
file), the sub-directory is renamed
`Proofs/Output/EmitterScannability/`, and namespaces lose the
`Indexed` qualifier.
-/
