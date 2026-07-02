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

/-! # `IndexedEmitterScannability` — parked parallel indexed track

**Status (2026-05-31): PARKED parallel track — cutover deferred.** This was
originally a staging aggregator for a "6f.3c cutover" that would rename these
indexed-twin sub-files over the legacy `Proofs/Output/EmitterScannability.lean`.
That plan predates two developments that make it stale:

  1. The legacy file is no longer a 10741-LOC monolith — after the keystone-
     reduction modularization it is ~950 LOC + a foundation chain under
     `Proofs/Output/EmitterScannability/`.
  2. The strategic decision (see Reflection 193) is **Option 2**: finish the
     non-indexed keystone (`universal_roundtrip`, 5 remaining sorries) to a
     0-sorry proof first. Reflection 157 established there is *no transport*
     between `ScannerStateIx`/`ParseStateIx` (indexed) and
     `ScannerState`/`ParseState` (concrete), so this track is a full parallel
     universe (indexed scanner **and** parser), not a drop-in.

This track is sorry-free but incomplete: it tops out at the body-token
characterization (`..._characterizationIx_part1`) and has no
`nonempty_structureIx` / loop-emitter-ok / `universal_roundtripIx`. It is kept
in the build as a reference substrate. The keep/migrate/retire call is deferred
until a concrete need for intrinsic input-range correspondence (precise error
spans, incremental parse) justifies re-walking the keystone path on indexed
types. See Reflection 193 in the blueprint for the full assessment.

## Multi-file decomposition (Reflection 108)

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
