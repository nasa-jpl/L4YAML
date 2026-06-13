import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `h_seq_rec` GATE-STRENGTH probe — the narrow-gate locator's `SeqPathAllSeq` is too strong

The de-risk mandated BEFORE choosing the `h_seq_rec` producer for `flowSubrangesOk_of_window_producers`
(`(i'-b-B2c-(d)-seq-rec)`), per [[ref-probe-deferred-universal-before-producing]] /
[[ref-minimal-pair-extracts-the-gate]].  The assembler demands a per-window producer

```
h_seq_rec : 2 ≤ lo → lo < hi → hi ≤ size-2 → hi < size →
            tokens[hi]! = .flowSequenceEnd → flowBracketBalance lo hi = 0 →
            tokens[lo-1]! = .flowSequenceStart → RecSeqBody ((take hi).drop lo)
```

— a WEAK, bracket-only window guard.  The landed nested-seq locator `nestedSeq_recseqbody_of_locator`
DOES produce `RecSeqBody`, but its gate carries the EXTRA precondition `SeqPathAllSeq tokens (lo-1)`
(the WHOLE enclosure stack all-seq), needed because it NAVIGATES the root `RecSeqBody` tree and a
`RecSeqEntry.map` edge is SEVERED (`SeqMapPathNestedProbe` / R335 / [[ref-severed-edge-bounds-navigator-domain]]).
**Question:** does that locator APPLY as `h_seq_rec`?  Answer (this probe): **NO — `SeqPathAllSeq` is
strictly stronger than the weak guard supplies.**  `h_seq_rec` quantifies over EVERY seq-opener-headed,
seq-closed, balance-0 window — including a seq nested inside a MAP — where `SeqPathAllSeq` is FALSE.

The MINIMAL PAIR (one differing structural feature isolates the over-restriction) on real scanned output:

* **Window A — all-seq path.**  `[[1,2],9]`, the inner seq `[1,2]`'s body window `[3,6)`, opener at 2.
  `pathStack 2 = [true]`, `pathStack 3 = [true,true]`.  Both the gate's `SeqEnclosed` (top-of-stack) AND
  the locator's `SeqPathAllSeq` (whole-stack) HOLD.
* **Window B — map-enclosed path.**  `[{a: [b]}]`, the inner seq `[b]`'s body window `[7,8)`, opener at
  6.  `pathStack 6 = [false,true]`, `pathStack 7 = [true,false,true]`.  The path crosses the map `{` at
  position 2, so the stack carries a `false`.  `SeqEnclosed` STILL HOLDS (top is the inner `[`'s `true`,
  so the GATE admits the window), but `SeqPathAllSeq` FAILS.

Both windows pass the WEAK bracket guard, so BOTH are in `h_seq_rec`'s domain.  The gate's `SeqEnclosed`
conjunct SEPARATES NOTHING (it is path-blind — holds on both); the discriminator between A and B is
EXACTLY the whole-path `SeqPathAllSeq`, which the locator demands and B lacks.

**Conclusion.**  `nestedSeq_recseqbody_of_locator` is NOT a total `h_seq_rec` producer — Window B is a
window it cannot inhabit.  The right `h_seq_rec` producer is a FRESH, ENCLOSURE-BLIND `RecSeqBody`
builder driven by the R411 opener-adjacency provider (content-start-after-opener survives map nesting —
why `GlobalFlowSeqOpenerAdj` was made axis-uniform) + the global `WellTyped` interior, with NO
`SeqPathAllSeq`.  Surfacing this BEFORE authoring averts a doomed wiring that would wall at the
map-enclosed window with no sorry-free discharge.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqHseqRecGateProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The typed-bracket stack after the prefix `[0, lo)`. -/
def pathStack (T : Array (Positioned YamlToken)) (lo : Nat) : Option (List Bool) :=
  btFold (some []) (T.toList.take lo)

/-- `SeqPathAllSeq` as a Bool: the WHOLE stack is nonempty and all-`true` (every enclosing frame seq). -/
def pathAllSeq (T : Array (Positioned YamlToken)) (lo : Nat) : Bool :=
  match pathStack T lo with
  | some s => !s.isEmpty && s.all (· == true)
  | none => false

/-- `SeqEnclosed` as a Bool: the TOP of the stack is seq (the gate's path-BLIND conjunct). -/
def enclosed (T : Array (Positioned YamlToken)) (lo : Nat) : Bool :=
  (pathStack T lo).bind (·.head?) == some true

/-- The WEAK bracket-only window guard `h_seq_rec` is quantified over, as a Bool. -/
def weakGuard (T : Array (Positioned YamlToken)) (lo hi : Nat) : Bool :=
  (2 ≤ lo) && (lo < hi) && (hi ≤ T.size - 2) && (hi < T.size) &&
  (T[hi]!.val == .flowSequenceEnd) && (flowBracketBalance T lo hi == 0) &&
  (T[lo-1]!.val == .flowSequenceStart)

-- ════════════════ Window A — all-seq path: `[[1,2],9]`, inner `[1,2]` window [3,6) ════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]
-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE

#guard N.size == 11
-- (A1) the window is in `h_seq_rec`'s domain: it passes the WEAK bracket guard.
#guard weakGuard N 3 6
-- (A2) the gate's path-blind `SeqEnclosed` holds …
#guard enclosed N 3
-- (A3) … and so does the locator's whole-path `SeqPathAllSeq`, at BOTH keyings (opener `lo-1`, inside `lo`).
#guard pathAllSeq N 2
#guard pathAllSeq N 3

-- ════════════════ Window B — map-enclosed path: `[{a: [b]}]`, inner `[b]` window [7,8) ════════════════
def mapVal : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b"])]]
def M : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal) with | .ok ts => ts | .error _ => #[]
-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:[ 7:"b" 8:] 9:} 10:] 11:SE

#guard M.size == 12
-- (B1) the window is ALSO in `h_seq_rec`'s domain: it passes the SAME weak bracket guard.
#guard weakGuard M 7 8
-- (B2) the gate's path-blind `SeqEnclosed` STILL HOLDS — so the GATE admits this window …
#guard enclosed M 7
-- (B3) … but the locator's whole-path `SeqPathAllSeq` FAILS at BOTH keyings — the map `{` severs it.
#guard pathAllSeq M 6 == false
#guard pathAllSeq M 7 == false

-- ════════════════ The discriminator: `SeqEnclosed` separates NOTHING; `SeqPathAllSeq` separates A from B.
#guard enclosed N 3 && enclosed M 7                       -- gate conjunct holds on BOTH (path-blind)
#guard pathAllSeq N 3 && (pathAllSeq M 7 == false)        -- locator's extra precondition holds on A, FAILS on B
#guard weakGuard N 3 6 && weakGuard M 7 8                 -- yet BOTH are in `h_seq_rec`'s weak-guard domain

end L4YAML.Proofs.EmitterScannability.SeqHseqRecGateProbe
