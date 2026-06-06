import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Dispatch-partition probe (de-risk for `(i'-b-recursion-driver / ii-merge)` part (a))

A CONCRETE-emitter probe, run while authoring `seqInteriorSeparators_of_safebody_and_descent`
(the per-window dispatcher), per `ref-probe-provider-satisfiable-before-assembler`.  The dispatcher
case-splits each gated sub-window `[a,b)` of a seq window `[lo,hi)` on the **top-level discriminator**
`flowBracketBalance tokens lo a`:

* `= 0` — `a` is at `[lo,hi)`'s OWN top level, enclosing seq is `[lo,hi)` itself (own-body branch,
  satisfied directly from the window's `SafeBodyUnit`);
* `≠ 0` — `a` is nested strictly deeper, enclosing seq is an inner bracket (descent branch,
  `seqDescent_provider_of_located`).

This probe confirms the partition is **clean and non-vacuous** on the two witnesses that exercise the
two ways the driver reaches an inner enclosing opener:

* `[[1, 2], 9]` — the gated window `[3, 6)` is NESTED (`balance 2 3 = 1 ≠ 0` ⇒ descent branch), and
  the gated window `[7, 9)` is TOP-LEVEL (`balance 2 7 = 0` ⇒ own-body branch);
* `[1, [2, 3]]` — the gated window `[5, 8)` is NESTED (`balance 2 5 = 1 ≠ 0` ⇒ descent), and the
  gated window `[2, 4)` is TOP-LEVEL (`balance 2 2 = 0` ⇒ own-body), reached after the advance past
  the first entry.

Each window passes the gate (`SeqTypedInterior`: balance-0, seq-enclosed `btFold`-top, local floor),
so both branches are genuinely populated and the dispatch is exhaustive on real output.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqDispatchPartitionProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The seq-vs-map mark read off `btFold`: head of the typed stack after the prefix `[0, a)`. -/
def enclosingMark (T : Array (Positioned YamlToken)) (a : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take a)).bind (·.head?)

/-- The gate `SeqTypedInterior` evaluated as a `Bool` (the three window-absolute conjuncts). -/
def gateOK (T : Array (Positioned YamlToken)) (a b : Nat) : Bool :=
  (flowBracketBalance T a b == 0) &&
  (enclosingMark T a == some true) &&
  (List.range (b + 1)).all (fun i => if a ≤ i then decide (flowBracketBalance T a i ≥ 0) else true)

-- ════════════════════ Witness N := `[[1, 2], 9]` (lo = 2, hi = 9) ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE
#guard N.size == 11

-- NESTED gated window [3, 6) → descent branch (`balance 2 3 ≠ 0`):
#guard gateOK N 3 6 == true
#guard flowBracketBalance N 2 3 == 1            -- discriminator ≠ 0 ⇒ descent
#guard !(flowBracketBalance N 2 3 == 0)

-- TOP-LEVEL gated window [7, 9) → own-body branch (`balance 2 7 = 0`):
#guard gateOK N 7 9 == true
#guard flowBracketBalance N 2 7 == 0            -- discriminator = 0 ⇒ own body

-- the own-body enclosing seq IS the outer window [2, 9): its close at depth 0 is index 9,
-- and the whole body [2, 9) is balanced (so a `SafeBodyUnit` on the window covers [7, 9)).
#guard flowBracketBalance N 2 9 == 0

-- ════════════════════ Witness T := `[1, [2, 3]]` (lo = 2, hi = 9) ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE
#guard T.size == 11

-- TOP-LEVEL gated window [2, 4) → own-body branch (`balance 2 2 = 0`):
#guard gateOK T 2 4 == true
#guard flowBracketBalance T 2 2 == 0            -- discriminator = 0 ⇒ own body

-- NESTED gated window [5, 8) → descent branch (`balance 2 5 ≠ 0`):
#guard gateOK T 5 8 == true
#guard flowBracketBalance T 2 5 == 1            -- discriminator ≠ 0 ⇒ descent
#guard !(flowBracketBalance T 2 5 == 0)

-- the advance is genuine: the inner enclosing opener p = 4 is at depth 0 of the outer window
-- (`balance 2 4 = 0`) but is NOT the outer head (`tokens[2] = "1"` is content, delta 0).
#guard flowBracketBalance T 2 4 == 0
#guard flowBracketDelta T[2]!.val == 0
#guard flowBracketDelta T[4]!.val == 1

end L4YAML.Proofs.EmitterScannability.SeqDispatchPartitionProbe
