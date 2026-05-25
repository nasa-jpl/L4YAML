/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness.OrderedDispatch

/-! # `IndexedScannerCorrectness.OrderedLoop` — §8.9–§8.11

`scanNextTokenIx_preserves_ScanInvIx` / `_preserves_AllKeysValidIx`
(top-level composition over the dispatchers), `scanLoopIx_ordered`
(fuel induction), and the final `scanIx_positions_ordered` discharge
of the staging axiom exposed in `Basic.lean` (§6.4).

Split out of `IndexedScannerCorrectness.lean` (Reflection 112).
Initially empty — populated by `6f.3b3.primitives.ordered.compose.value`. -/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.ScannerCorrectness

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.WellBehaved
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

-- Populated by `6f.3b3.primitives.ordered.compose.value` next.

end L4YAML.Proofs.Indexed.ScannerCorrectness
