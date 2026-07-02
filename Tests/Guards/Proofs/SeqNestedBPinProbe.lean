import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `b`-pinning probe — the window END is NOT pinned by `SeqTypedInterior`'s balance-0 (R356)

The PROBE the R355-corrected wrapper interface demanded BEFORE authoring
`nestedSeq_recseqentry_locate`.  R355 settled that the LEAF arm needs the window's own enclosure
(`SeqEnclosed tokens a`, not the carried base path) to exclude a map head.  Its **Next-step pointer**
then attributed the leaf's other obligation — `h_b : b = off + e.length - 1` (the window's right edge
IS the head entry's structural close) — to *"`b` pinned to the head edge by `SeqTypedInterior`'s
balance-0."*  This probe finds that attribution **FALSE**, on real emitted tokens.

THE SETTING.  `SeqTypedInterior tokens a b` is three window-ABSOLUTE conditions: balance-0
(`flowBracketBalance tokens a b = 0`), seq-enclosure (`btFold`-top `= some true` after `[0,a)`), and
the local-Dyck floor (`flowBracketBalance tokens a i ≥ 0` for `a ≤ i ≤ b`).  NONE of the three reads
`tokens[b]` — they constrain the window's INTERIOR balance, never the token AT the end.  So a window
ending at an interior `.flowEntry` separator (balance back to 0, floor intact) passes the gate exactly
as the one ending at the matching close does.  An END-FREE gate ([[ref-end-free-gate-underdetermines-close]])
underdetermines the close.

THE MINIMAL TRIPLE.  `[[1,2,3]]` — the inner seq of THREE elements has two interior separators (at 4
and 6) plus the matching close (at 8).  From the fixed interior start `a = 3`, `SeqTypedInterior B 3 b`
holds for b ∈ {4, 6, 8} (all balance-0, all floored), but only b = 8 is a `.flowSequenceEnd`.  So
balance-0 + floor admit THREE values of `b`; they cannot pin it.

THE DISCRIMINATOR.  The deliverable-producing consumer `seqWindowRecSeqBody`
(`SeqInteriorSeparators.lean:1606`) carries, as the FOURTH conjunct of its width-recursion guard `G`,
`tokens[hi]!.val = .flowSequenceEnd` — an explicit CLOSE hypothesis at the window's right edge.  THAT
(not balance) is what pins the wrapper's `b`.  So the wrapper's signature must take the close hypothesis
`tokens[b]!.val = .flowSequenceEnd`; the leaf's `h_b` is derived by MATCHING that typed close to the
head entry's structural close (the unique depth-0 seq-close from `a`), never by balance uniqueness.

THE TRANSFERABLE RULE.  An end-free interior gate (balance/floor, blind to `tokens[b]`) cannot pin a
window's closing edge; a producer that must read the close off `b` needs an explicit close hypothesis
from its consumer, not the interior gate.  Probe a window whose end is an interior separator (balance-0,
floor intact, but `tokens[b] ≠ close`) before crediting the gate with the bound.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqNestedBPinProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- `[[1,2,3]]` — inner seq of three elements → two interior `,` separators (at 4, 6) and the matching
    close (at 8). -/
def Bval : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2", sc "3"]]
def B : Array (Positioned YamlToken) :=
  match scanFiltered (emit Bval) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:, 7:"3" 8:] 9:] 10:SE  (root body off = 2)
-- head entry `[1,2,3]` spans [2,8], close at 8; interior window starts a = off+1 = 3.
#guard B.size == 11
#guard B[2]!.val == .flowSequenceStart    -- head opener at off = 2
#guard B[8]!.val == .flowSequenceEnd       -- head close at 8 (the ONLY valid window end)
#guard B[4]!.val == .flowEntry             -- interior separator (a candidate end with balance 0)
#guard B[6]!.val == .flowEntry             -- interior separator (a candidate end with balance 0)

/-- `SeqEnclosed`-style top-of-stack projection at `a` (the gate's 2nd conjunct). -/
def topTrue (tokens : Array (Positioned YamlToken)) (a : Nat) : Bool :=
  match (btFold (some []) (tokens.toList.take a)).bind (·.head?) with | some true => true | _ => false

/-- The local-Dyck floor over `[a,b]` as a Bool (the gate's 3rd conjunct). -/
def floorOk (tokens : Array (Positioned YamlToken)) (a b : Nat) : Bool :=
  (List.range (b - a + 1)).all (fun d => decide (flowBracketBalance tokens a (a + d) ≥ 0))

-- a = 3 is seq-enclosed (immediately inside the inner `[`) — the gate's 2nd conjunct holds:
#guard topTrue B 3 == true

-- THE NEGATIVE: balance-0 (1st conjunct) holds at b = 4 (sep), b = 6 (sep), AND b = 8 (close):
#guard decide (flowBracketBalance B 3 4 == 0)
#guard decide (flowBracketBalance B 3 6 == 0)
#guard decide (flowBracketBalance B 3 8 == 0)

-- the floor (3rd conjunct) ALSO holds at all three b — so SeqTypedInterior B 3 b holds for b ∈ {4,6,8}:
#guard floorOk B 3 4 == true
#guard floorOk B 3 6 == true
#guard floorOk B 3 8 == true

-- DECISIVE: balance-0 + floor + enclosure do NOT pin b; the close hypothesis is the discriminator.
-- Only b = 8 is a `.flowSequenceEnd` — the fact `seqWindowRecSeqBody`'s `G` carries explicitly.
#guard B[4]!.val != .flowSequenceEnd
#guard B[6]!.val != .flowSequenceEnd
#guard B[8]!.val == .flowSequenceEnd

end L4YAML.Proofs.EmitterScannability.SeqNestedBPinProbe
