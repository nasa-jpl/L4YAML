import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `SeqPathAllSeq` gate probe — `(i'-b-B2c-(d) — STEP D: the within-window circularity `h_safe` source)`

R447 de-risk PROBE.  The R446 blueprint Next step queued, as the joint induction's FIRST sub-task,
"find/build the NESTED analog — the per-nested-seq-value emission-flat `SafeBodyUnit` producer".  Reading
the landed code, that producer ALREADY EXISTS — `nestedSeq_safeBodyUnit_of_locator`
(`SeqInteriorSeparators.lean:5379`) projects `RecSeqBody → SafeBodyUnit ((take b).drop a)` at any nested
seq window `[a,b)` straight from emission, NO carrier.  But it routes through the forward locator
`nestedSeq_recseqentry_locate`, which walks an all-seq bracket SPINE — so it inherits the locator's
hypothesis `h_path : SeqPathAllSeq tokens (a - 1)` (the entire enclosing bracket stack is `[`-typed).

This probe settles whether that `SeqPathAllSeq` gate is (a) the *real* obstruction — NOT derivable from
the joint-induction window guard (`FlowBodyWindow ∧ FlowBodyContentDeep ∧ SeqEnclosed ∧ close`) — and so
must be *threaded* through the induction, and (b) where it holds vs fails.  `SeqEnclosed tokens lo`
(`= (btFold (take lo)).bind (·.head?) = some true`, the TOP frame is `[`) is in the guard; `SeqPathAllSeq
tokens (lo-1)` (`= ∃ s, btFold (take (lo-1)) = some s ∧ s ≠ [] ∧ s.all (· == true) = true`, EVERY frame is
`[`) is strictly stronger — it sees the whole stack, not just the top.

`btStep` pushes the TOP at the list HEAD: `.flowSequenceStart ↦ true :: s`, `.flowMappingStart ↦ false :: s`
(`WellBracketed.lean:1538`).  So a seq reached through a map carries a `false` deeper in the stack: its
TOP is still `true` (`SeqEnclosed` holds) but `s.all = true` FAILS (`SeqPathAllSeq` fails).  That is the
counterexample proving the gate is *not* a projection of `SeqEnclosed`.

Three witnesses, `#guard`-confirmed below:

* `[[1,2],9]` (N) — the all-seq nested window `[3,6)` (inner `[1,2]`, opener at 2): `SeqPathAllSeq N 2`
  HOLDS (stack `[true]`).  And the ROOT window `[2,9)` (lo-1 = 1): `SeqPathAllSeq N 1` FAILS (stack `[]` —
  empty before the outer `[`), so the root is NOT served by the locator — it uses the flat
  `seqRoot_safeBodyUnit` (the root-vs-nested dispatch, `ref-root-seed-discriminator-not-from-gate`).
* `[{a:[b]}]` (M) — the MAP-nested seq window `[7,8)` (inner `[b]`, opener at 6): `SeqEnclosed M 7` HOLDS
  (top `true`) but `SeqPathAllSeq M 6` FAILS (stack `[false, true]` — the map's `false` deeper).  This is
  the counterexample: the gate is strictly stronger than `SeqEnclosed`, so it cannot be derived from the
  joint guard and must be threaded.

Conclusion: the R447 `h_safe` source is the EXISTING `nestedSeq_safeBodyUnit_of_locator`, with the
`SeqPathAllSeq tokens (lo-1)` gate as a NEW guard conjunct the joint induction must carry; the root window
is the sole exception, fed flat.  (All-seq descent is sound: the seq recursion only ever descends `[`→`[`,
so every window it visits is all-seq-path, `SeqPathAllSeq` true.)  Sorry-free.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqPathAllSeqGateProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-! ## Witness N = `[[1,2],9]` — all-seq nested window holds; root window fails. -/

def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

#guard N.size == 11
-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE
#guard N[1]!.val == .flowSequenceStart        -- outer seq opener (root)
#guard N[2]!.val == .flowSequenceStart        -- inner seq opener (nested)

-- The all-seq nested window `[3,6)` (lo = 3, lo-1 = 2): stack `[true]` — `SeqPathAllSeq N 2` HOLDS.
#guard btFold (some []) (N.toList.take 2) == some [true]
#guard (btFold (some []) (N.toList.take 2)).map (fun s => s != [] && s.all (· == true)) == some true

-- The ROOT window `[2,9)` (lo = 2, lo-1 = 1): stack `[]` — `SeqPathAllSeq N 1` FAILS (empty).
#guard btFold (some []) (N.toList.take 1) == some []
#guard (btFold (some []) (N.toList.take 1)).map (fun s => s != []) == some false

/-! ## Witness M = `[{a:[b]}]` — map-nested seq window: `SeqEnclosed` holds, `SeqPathAllSeq` fails. -/

def mapVal : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b"])]]
def M : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal) with | .ok ts => ts | .error _ => #[]

#guard M.size == 12
#guard M[1]!.val == .flowSequenceStart        -- outer seq `[`
#guard M[2]!.val == .flowMappingStart         -- map `{`  ← the `false` deeper in the stack
#guard M[6]!.val == .flowSequenceStart        -- inner seq opener (map-nested), window `[7,8)`

-- `SeqEnclosed M 7`: TOP of stack at lo = 7 is `true` (the inner `[`). HOLDS — it is in the joint guard.
#guard btFold (some []) (M.toList.take 7) == some [true, false, true]
#guard (btFold (some []) (M.toList.take 7)).bind (·.head?) == some true

-- `SeqPathAllSeq M 6` (lo-1 = 6): stack `[false, true]` — the map's `false` deeper. FAILS.
-- Same top `true` as a genuine all-seq window, but `s.all = true` is false ⇒ NOT derivable from SeqEnclosed.
#guard btFold (some []) (M.toList.take 6) == some [false, true]
#guard (btFold (some []) (M.toList.take 6)).map (fun s => s != [] && s.all (· == true)) == some false
#guard (btFold (some []) (M.toList.take 6)).bind (·.head?) == some false   -- SeqEnclosed M 6 also fails

/-! ## The gate's necessity in one line: same TOP frame, different `all`. -/

-- The map-nested window and a genuine all-seq window can share the SAME enclosing-top (`some true`),
-- yet differ on `s.all` — so `SeqEnclosed` (top only) cannot decide `SeqPathAllSeq` (whole stack).
#guard ((btFold (some []) (N.toList.take 2)).bind (·.head?)
        == (btFold (some []) (M.toList.take 7)).bind (·.head?))         -- tops agree (some true)
#guard decide (((btFold (some []) (N.toList.take 2)).map (·.all (· == true)))
        ≠ ((btFold (some []) (M.toList.take 6)).map (·.all (· == true)))) -- but whole-stack differs

end L4YAML.Proofs.EmitterScannability.SeqPathAllSeqGateProbe
