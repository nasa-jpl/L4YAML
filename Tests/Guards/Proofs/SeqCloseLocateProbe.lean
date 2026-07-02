import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Forward-CLOSE locate probe (de-risk for `(i'-b-locator-glue-close)`)

A CONCRETE-emitter probe, run while authoring `seqClose_of_located_and_enclosing`
(per `ref-probe-deferred-universal-before-producing`). It confirms the matching-close call's
hypotheses hold at the located enclosing opener `p`, and that the resulting matching close `j`
satisfies the two floor-contradiction bounds (`a ≤ j` from the locator floor, `b ≤ j` from the
GATE floor) that the brick needs to deliver `b ≤ hiS` to `seqEnclosingFacts_provider_of_located`.

The brick uses `flowBracketBalance_matching_close_seq` (WellBracketed.lean) at base `lo` (the
ENCLOSING recursion window), `k := p` (the located opener), which packages matching-close AND the
typed close `tokens[j]!.val = .flowSequenceEnd` in one call. Its hypotheses, verified below:
`lo ≤ p`, `p < hi`, `hi ≤ size`, `balance lo p = 0` (discriminator), `tokens[p]! = .flowSequenceStart`,
`balance lo hi = 0` (enclosing total), the window Dyck floor over `[lo, hi]`, and `WellTyped` of the
enclosing window slice. The output `j` then yields `a ≤ j` / `b ≤ j` by the two floor contradictions.

Witnesses: `[[1, 2], 9]` (one nested seq) and `[[1], [2]]` (two sibling nested seqs — the R313
cross-sibling case; the GATE floor now restricts the carrier to genuine entry windows).
-/

namespace L4YAML.Proofs.EmitterScannability.SeqCloseLocateProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- ════════════════════ Witness N := `[[1, 2], 9]` ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:streamStart 1:`[` 2:`[` 3:"1" 4:`,` 5:"2" 6:`]` 7:`,` 8:"9" 9:`]` 10:streamEnd
#guard N.size == 11
#guard N[2]!.val == .flowSequenceStart        -- inner opener p = 2
#guard N[6]!.val == .flowSequenceEnd          -- inner matching close j = 6

-- The enclosing recursion window of the inner seq is the OUTER seq body [lo, hi) = [2, 9).
-- Matching-close call hypotheses at base lo = 2, k = p = 2:
#guard flowBracketBalance N 2 2 == 0          -- balance lo p = 0 (discriminator; p = lo here)
#guard flowBracketBalance N 2 9 == 0          -- balance lo hi = 0 (enclosing total)
#guard (List.range 8).all fun i =>            -- window Dyck floor over [2, 9]
  if 2 ≤ i then decide (flowBracketBalance N 2 i ≥ 0) else true
-- the located opener is a seq start, p < hi, hi ≤ size:
#guard decide (2 < 9) && decide (9 ≤ N.size)

-- The matching close is j = 6 (first return to 0 from base 2 after the opener):
#guard flowBracketBalance N 2 7 == 0          -- balance lo (j+1) = 0  ⇒  j = 6 is the close
#guard flowBracketBalance N 3 6 == 0          -- balance (p+1) j = 0   (the inner body balances)
#guard flowBracketDelta N[6]!.val == -1       -- the close delta is -1

-- For a genuine gated window [a, b) = [3, 5) inside the inner seq:
--   a ≤ j (else the locator floor at j+1 underflows), b ≤ j (else the GATE floor at j+1 underflows).
#guard decide (3 ≤ 6) && decide (5 ≤ 6)       -- a ≤ j ∧ b ≤ j  ✓
#guard flowBracketBalance N 3 7 == -1         -- balance (p+1) (j+1) = -1  (locator-floor contradiction)
-- a DEEPER gated window [a, b) = [5, 6) (a = 5 > p+1 = 3) exercises the GATE floor separately:
#guard flowBracketBalance N 3 5 == 0          -- balance (p+1) a = 0 at a = 5  (locator re-seats a)
#guard flowBracketBalance N 5 6 == 0          -- balance a j = 0  (re-based by composition)
#guard flowBracketBalance N 5 7 == -1         -- balance a (j+1) = -1  (GATE-floor contradiction)

-- ════════════════════ Witness T := `[[1], [2]]` (R313 cross-sibling case) ════════════════════
def twoSibVal : YamlValue :=
  .sequence .flow #[.sequence .flow #[sc "1"], .sequence .flow #[sc "2"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit twoSibVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:streamStart 1:`[` 2:`[` 3:"1" 4:`]` 5:`,` 6:`[` 7:"2" 8:`]` 9:`]` 10:streamEnd
#guard T.size == 11
#guard T[2]!.val == .flowSequenceStart        -- first inner opener p = 2
#guard T[4]!.val == .flowSequenceEnd          -- first inner matching close j = 4
#guard T[6]!.val == .flowSequenceStart        -- second inner opener p' = 6
#guard T[8]!.val == .flowSequenceEnd          -- second inner matching close j' = 8

-- First inner seq: enclosing window = outer body [lo, hi) = [2, 9), opener p = 2.
#guard flowBracketBalance T 2 2 == 0          -- balance lo p = 0
#guard flowBracketBalance T 2 9 == 0          -- balance lo hi = 0
#guard (List.range 8).all fun i =>            -- window Dyck floor over [2, 9]
  if 2 ≤ i then decide (flowBracketBalance T 2 i ≥ 0) else true
#guard flowBracketBalance T 2 5 == 0          -- balance lo (j+1) = 0  ⇒  j = 4
#guard flowBracketBalance T 3 4 == 0          -- balance (p+1) j = 0  (first inner body balances)
#guard flowBracketDelta T[4]!.val == -1

-- For the genuine gated entry window [a, b) = [3, 4) inside the first inner seq: a ≤ j ∧ b ≤ j.
#guard decide (3 ≤ 4) && decide (4 ≤ 4)       -- a = 3 ≤ j = 4, b = 4 ≤ j = 4  ✓
#guard flowBracketBalance T 3 5 == -1         -- balance (p+1) (j+1) = -1  (locator-floor contradiction)

-- Second inner seq mirrors at p' = 6, j' = 8:
#guard flowBracketBalance T 6 6 == 0
#guard flowBracketBalance T 6 9 == 0
#guard flowBracketBalance T 7 8 == 0
#guard flowBracketDelta T[8]!.val == -1

end L4YAML.Proofs.EmitterScannability.SeqCloseLocateProbe
