/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.Basic
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.StreamStart
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedDefs
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedPrims
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedDispatch
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedLoop

/-! # `IndexedScannerCorrectness` — Phase 3 Step 6f.3b3 staging aggregator

**Status**: staging aggregator. Imports the six indexed-twin sub-files
that collectively port the legacy `Proofs/Scanner/ScannerCorrectness.lean`
to the indexed scanner.

## Multi-file decomposition (Reflection 112)

The original `IndexedScannerCorrectness.lean` was split during
`6f.3b3.primitives.ordered.compose.value` to keep `Ordered` work
modular as the ordered-discharge ladder grew past 2700 LOC.

  | Sub-file                 | Sections      | Concern                                         |
  |--------------------------|---------------|-------------------------------------------------|
  | `Basic.lean`             | §1–§6         | Filter index correspondence + `ValidTokenStreamPropIx` foundation; exposes the two staging axioms |
  | `StreamStart.lean`       | §7            | `SimpleKeyAboveIx` + `scanIx_first_is_streamStart` discharge + §7.10 composite |
  | `OrderedDefs.lean`       | §8.1–§8.2     | `ScanInvIx` / `AllKeysValidIx` definitions + mono helpers (both `_mono` and `_mono_pos`) |
  | `OrderedPrims.lean`      | §8.3–§8.6     | `emit`/`emitAt`/`advance`/`overwriteAtCursor` + `skipToContentS`/`unwindIndentsIx`/`saveSimpleKeyIx` preservation |
  | `OrderedDispatch.lean`   | §8.7–§8.8     | Per-helper bricks (all leaf `scan*Ix` helpers) + per-dispatcher composition |
  | `OrderedLoop.lean`       | §8.9–§8.11    | `scanNextTokenIx_preserves_*` + `scanLoopIx_ordered` fuel induction + final discharge |

Each sub-file imports its predecessor in the dependency chain
(`Basic → StreamStart → OrderedDefs → OrderedPrims → OrderedDispatch →
OrderedLoop`).

## Phase 3 Step 6f cutover

At cutover, this aggregator is renamed
`Proofs/Scanner/ScannerCorrectness.lean` (overwriting the legacy
file), the sub-directory is renamed
`Proofs/Scanner/ScannerCorrectness/`, and namespaces lose the
`Indexed` qualifier. -/
