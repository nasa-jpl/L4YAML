import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Seq carrier domain vs all-seq locator reach — `(i'-b-B2c-(d) — STEP D: the map-mirror entanglement)`

R448 de-risk PROBE.  The seq ROOT CARRIER `SeqInteriorSeparators tokens 2 (size-2)` is the last seq
residual.  Its definition (`SeqInteriorSeparators.lean:96`) is a UNIVERSAL over a domain predicate:

    SeqInteriorSeparators tokens lo hi :=
      ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → SeqTypedInterior tokens a b →
        bodySuccFact tokens a b ∧ noTrailingSepFact tokens a b

The domain is every `SeqTypedInterior tokens a b` sub-window — `flowBracketBalance a b = 0`,
`(btFold (take a)).bind (·.head?) = some true` (TOP frame `[`), and the Dyck floor.  The TOP-frame
condition is path-BLIND: it admits a seq reached through a MAP (`[{a:[b]}]`'s `[b]`).

The R447 plan sourced the co-construction's per-window `h_safe : SafeBodyUnit` from the all-seq locator
`nestedSeq_safeBodyUnit_of_locator`, gated by `SeqPathAllSeq tokens (a-1)` (the WHOLE ancestor path `[`).
This probe settles the consequence: the carrier's domain (`SeqTypedInterior`) is STRICTLY WIDER than the
locator's reach (`SeqPathAllSeq`).  The gap is exactly the MAP-NESTED seqs — in the carrier's domain
(separator facts owed) but UNREACHABLE by the all-seq locator.

Why unreachable, structurally: the all-seq locator walks the root `RecSeqBody` spine via `RecSeqEntry.seq`'s
stored `h_rec : RecSeqBody interior`.  But `RecSeqEntry.map` stores only `h_wb : WellBracketed interior`
(NonemptyStructure.lean:~500) — the recursive witness is SEVERED at the map.  So the seq spine cannot
descend into a map's values.  A map-nested seq's `RecSeqBody` lives behind `RecMapBody`/`RecMapPair`
(whose value field re-enters `RecSeqEntry`), reachable only by a MAP-PATH locator (the map mirror).

Conclusion: the seq root carrier is NOT seq-side-completable — its `h_safe` source splits THREE ways by
path: root (flat `seqRoot_safeBodyUnit`), all-seq-path nested (`nestedSeq_safeBodyUnit_of_locator`, R447),
and MAP-path nested (the deferred map mirror).  R447's 2-way dispatch `seqWindow_safeBodyUnit` is
necessary but INSUFFICIENT; the map mirror is on the seq root carrier's CRITICAL PATH, not a separate
downstream concern.  Sorry-free.

Two witnesses:
* `[[1,2],9]` (N): the all-seq window `[3,6)` (`[1,2]`) — in `SeqTypedInterior` AND `SeqPathAllSeq`
  (locator-reachable).
* `[{a:[b]}]` (M): the map-nested window `[7,8)` (`[b]`) — in `SeqTypedInterior` (carrier owes its
  separator facts) but NOT `SeqPathAllSeq` (the map's `false` deeper; locator cannot reach it).
-/

namespace L4YAML.Proofs.EmitterScannability.SeqCarrierMapNestedDomainProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-! ## All-seq witness N = `[[1,2],9]`: the nested window `[3,6)` is in BOTH domains (locator-reachable). -/

def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

#guard N.size == 11
-- `SeqTypedInterior N 3 6` (the inner `[1,2]` window): balance-0, top `[`, floor ≥ 0.
#guard flowBracketBalance N 3 6 == 0
#guard (btFold (some []) (N.toList.take 3)).bind (·.head?) == some true
#guard decide (flowBracketBalance N 3 3 ≥ 0 && flowBracketBalance N 3 4 ≥ 0
  && flowBracketBalance N 3 5 ≥ 0 && flowBracketBalance N 3 6 ≥ 0)            -- Dyck floor
-- `SeqPathAllSeq N 2` (the ancestor path before the inner opener): all-`[`, nonempty ⇒ LOCATOR-REACHABLE.
#guard btFold (some []) (N.toList.take 2) == some [true]
#guard (btFold (some []) (N.toList.take 2)).map (fun s => s != [] && s.all (· == true)) == some true

/-! ## Map-nested witness M = `[{a:[b]}]`: the window `[7,8)` is in the carrier domain but NOT reachable. -/

def mapVal : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b"])]]
def M : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal) with | .ok ts => ts | .error _ => #[]

#guard M.size == 12
#guard M[2]!.val == .flowMappingStart        -- the map frame: the `false` that severs the seq spine
#guard M[6]!.val == .flowSequenceStart        -- the map-nested seq `[b]` opener; window `[7,8)`
#guard M[8]!.val == .flowSequenceEnd

-- `SeqTypedInterior M 7 8` (the `[b]` window) HOLDS ⇒ it is IN the root carrier's quantification domain,
-- so the carrier OWES `bodySuccFact`/`noTrailingSepFact` here.
#guard flowBracketBalance M 7 8 == 0
#guard (btFold (some []) (M.toList.take 7)).bind (·.head?) == some true        -- TOP frame `[`
#guard decide (flowBracketBalance M 7 7 ≥ 0 && flowBracketBalance M 7 8 ≥ 0)   -- Dyck floor

-- `SeqPathAllSeq M 6` (the ancestor path before `[b]`'s opener) FAILS: the map's `false` is deeper.
-- So the all-seq locator CANNOT reach `[b]` — its separator facts need the MAP MIRROR.
#guard btFold (some []) (M.toList.take 6) == some [false, true]
#guard (btFold (some []) (M.toList.take 6)).map (fun s => s != [] && s.all (· == true)) == some false

/-! ## The contrast in one line: both windows are in the carrier domain, only one is locator-reachable. -/

-- Both `[3,6)`@N and `[7,8)`@M are `SeqTypedInterior` (carrier domain): top frame `[` for both.
#guard ((btFold (some []) (N.toList.take 3)).bind (·.head?)
        == (btFold (some []) (M.toList.take 7)).bind (·.head?))           -- both `some true`
-- But the ancestor PATHS differ on all-`[`: N's reachable, M's not (the severed map edge).
#guard decide (((btFold (some []) (N.toList.take 2)).map (·.all (· == true)))
        ≠ ((btFold (some []) (M.toList.take 6)).map (·.all (· == true))))

end L4YAML.Proofs.EmitterScannability.SeqCarrierMapNestedDomainProbe
