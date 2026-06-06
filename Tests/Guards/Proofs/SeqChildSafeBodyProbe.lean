import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Child-`SafeBodyUnit` probe (de-risk for `(i'-b-child-safebodyunit)`)

A CONCRETE-emitter probe, run while authoring `seqChild_safeBodyUnit`
(per `ref-probe-provider-satisfiable-before-assembler`). Brick (4) feeds
`recseqentry_seqbracket_oracle` (with the enclosing window `[p, hi)` and the width-recursion IH) the
located close `j`'s facts and projects the resulting `RecSeqBody ((take j).drop (p+1))` to the
windowed `SafeBodyUnit ContentStartTok` via `RecSeqBody.toSafeBodyUnit`.

The oracle's WITNESS-DEPENDENT hypotheses (the matching-close locator's own output, the part not
fixed by the guards) are: the typed close `tokens[j]! = .flowSequenceEnd`, the interior balance
`balance (p+1) j = 0`, and the matched-bracket interior floor `∀ i ∈ (p, j], balance p i ≥ 1`. This
probe confirms those hold at the located children, so the wrapper is not vacuous.

Witnesses: `[[1, 2], 9]` (one nested seq, inner body `[3, 6)`) and `[[1], [2]]` (two sibling nested
seqs, inner bodies `[3, 4)` / `[7, 8)`).
-/

namespace L4YAML.Proofs.EmitterScannability.SeqChildSafeBodyProbe

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
-- Inner seq: opener p = 2, matching close j = 6; enclosing recursion window [p, hi) = [2, 9).
#guard N.size == 11
#guard N[2]!.val == .flowSequenceStart        -- opener at the window head p = 2
#guard N[6]!.val == .flowSequenceEnd          -- typed close at j = 6

-- The oracle's witness-dependent hypotheses at (p, hi, j) = (2, 9, 6):
#guard flowBracketDelta N[6]!.val == -1       -- close delta -1 (⇒ typed close consistent)
#guard flowBracketBalance N 3 6 == 0          -- balance (p+1) j = 0  (inner body balances)
#guard decide (2 < 6) && decide (6 < 9)       -- p < j ∧ j < hi
-- the matched-bracket interior floor `∀ i ∈ (2, 6], balance 2 i ≥ 1`:
#guard (List.range 7).all fun i =>
  if 2 < i then decide (flowBracketBalance N 2 i ≥ 1) else true
-- it is a GENUINE floor ≥ 1, NOT merely ≥ 0 (the opener pushes the running balance to 1):
#guard flowBracketBalance N 2 3 == 1          -- just past the opener: depth 1

-- ════════════════════ Witness T := `[[1], [2]]` (two sibling children) ════════════════════
def twoSibVal : YamlValue :=
  .sequence .flow #[.sequence .flow #[sc "1"], .sequence .flow #[sc "2"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit twoSibVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:streamStart 1:`[` 2:`[` 3:"1" 4:`]` 5:`,` 6:`[` 7:"2" 8:`]` 9:`]` 10:streamEnd
#guard T.size == 11

-- First inner seq: opener p = 2, close j = 4; enclosing window [2, 9).
#guard T[2]!.val == .flowSequenceStart
#guard T[4]!.val == .flowSequenceEnd
#guard flowBracketDelta T[4]!.val == -1
#guard flowBracketBalance T 3 4 == 0          -- balance (p+1) j = 0
#guard (List.range 5).all fun i =>            -- interior floor `∀ i ∈ (2, 4], balance 2 i ≥ 1`
  if 2 < i then decide (flowBracketBalance T 2 i ≥ 1) else true

-- Second inner seq: opener p' = 6, close j' = 8; enclosing window [2, 9) (after advancing past `,`).
#guard T[6]!.val == .flowSequenceStart
#guard T[8]!.val == .flowSequenceEnd
#guard flowBracketDelta T[8]!.val == -1
#guard flowBracketBalance T 7 8 == 0          -- balance (p'+1) j' = 0
#guard (List.range 9).all fun i =>            -- interior floor `∀ i ∈ (6, 8], balance 6 i ≥ 1`
  if 6 < i then decide (flowBracketBalance T 6 i ≥ 1) else true

end L4YAML.Proofs.EmitterScannability.SeqChildSafeBodyProbe
