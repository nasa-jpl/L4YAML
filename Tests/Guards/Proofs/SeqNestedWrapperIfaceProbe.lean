import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Emission-spine-walk WRAPPER interface probe — `(i'-b-B2c-nested-fbc-emission-locator-wrapper-interface)`

The PROBE the blueprint queued after R353.  The three SLICE bricks of `nestedSeq_recseqentry_locate`
(leaf R351, descend + advance R353) are landed; the WRAPPER (`Nat.strongRecOn` on `body.length`) is NOT a
fourth slice brick (Reflection 353) — it carries a DOMAIN INVARIANT + a termination measure, and its
DESCEND arm must exclude a MAP head that the pure-arithmetic trichotomy would wrongly descend into.  This
probe settles ONE interface question before authoring: **which domain hypothesis does the wrapper carry —
the TOP-of-stack enclosure `SeqEnclosed` (= `SeqTypedInterior`'s 2nd conjunct, what the `desc` consumer
hands it), or the WHOLE-PATH `SeqPathAllSeq` (R336)?**

THE MINIMAL PAIR (`ref-minimal-pair-extracts-the-gate`).  Both witnesses contain the SAME nested seq
`[1, 2]`; they differ only in the PATH from the root to it:

* **POSITIVE** `[[1,2]]`     — `[1,2]` at interior start `a = 3`, reached through all `[` (all-seq path).
  Layout `0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:] 8:SE`; stack at `take 3` = `[true, true]`.
* **NEGATIVE** `[{x:[1,2]}]` — `[1,2]` at interior start `a = 7`, reached through a `{` (map in path).
  Layout `0:SS 1:[ 2:{ 3:key 4:"x" 5:value 6:[ 7:"1" 8:, 9:"2" 10:] 11:} 12:] 13:SE`; stack at `take 7`
  = `[true, false, true]`.

THE DECISIVE FINDING — **the wrapper must carry `SeqPathAllSeq`, NOT `SeqEnclosed`/`SeqTypedInterior`.**
The negative window's stack-TOP is `true` (the inner `[` is the immediate enclosure), so it PASSES
`SeqEnclosed` / `SeqTypedInterior`'s 2nd conjunct — the very hypothesis the `desc` consumer provides.  Yet
its WHOLE stack is `[true, false, true]` (not all-`true`), so it FAILS `SeqPathAllSeq`.  The two windows
are INDISTINGUISHABLE by the top-projection (`topTrue P 3 = topTrue N 7 = true`) but SEPARATED by the
whole-path invariant (`allTrue P 3 ≠ allTrue N 7`).  So `SeqTypedInterior` — what `desc` hands the wrapper
— canNOT exclude a nested seq sitting inside a map, which the wrapper's DESCEND arm structurally MUST
reject (a `RecSeqEntry.map` has no `h_rec : RecSeqBody interior` to descend into).  Only `SeqPathAllSeq`
excludes it (`seqPathAllSeq_map_push_breaks`, SeqInteriorSeparators.lean:1359).

INTERFACE DECISION (read off this probe):
* The wrapper's CARRIED domain hypothesis is `SeqPathAllSeq tokens off` at the current base, threaded
  across DESCEND by `seqPathAllSeq_descend` (a seq opener pushes `true`, preserving all-`true`); the map
  head is excluded by `seqPathAllSeq_map_push_breaks` (a map opener pushes `false`, breaking it).  The
  ROOT base `off = 2` seeds it trivially (`take 2` = `[SS, root-[]` → `[true]`, all-`true`).
* The typed↔structural BRIDGE in the `desc` assembly does NOT manufacture `SeqPathAllSeq` from
  `SeqTypedInterior` (this probe shows that is FALSE — the negative is a counterexample).  It supplies
  `SeqPathAllSeq` from the OUTER seq recursion's own descent discipline: `seqWindowRecSeqBody` descends
  ONLY through seq openers (R338 — it STOPS at map leaves), so every window it asks the seed about is
  all-seq-path BY CONSTRUCTION.

This RE-OPENS R339's "`SeqPathAllSeq` is vestigial" claim in a precise, consumer-relative way
(`ref-downstream-derisk-restores-upstream`): `SeqPathAllSeq` IS vestigial for the gate-driven FLAT
producer `seqWindowRecSeqBody` (which reads only the TOP-projection `SeqEnclosed`, handed free by the
gate), but it is LOAD-BEARING for the emission-spine NAVIGATOR (which walks the TYPED `RecSeqBody` and
must not descend into a map entry).  A projection sufficient for the value-blind producer is insufficient
for the structure-walking navigator.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqNestedWrapperIfaceProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.EmitterScannability (btFold btStep)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- ════════════ POSITIVE: `[[1,2]]` — nested seq `[1,2]` reached through all `[` ════════════
def Pval : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"]]
def P : Array (Positioned YamlToken) :=
  match scanFiltered (emit Pval) with | .ok ts => ts | .error _ => #[]

-- ════════════ NEGATIVE: `[{x:[1,2]}]` — same `[1,2]`, reached through a `{` ════════════
def Nval : YamlValue := .sequence .flow #[.mapping .flow #[(sc "x", .sequence .flow #[sc "1", sc "2"])]]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit Nval) with | .ok ts => ts | .error _ => #[]

/-- The stack-TOP enclosure projection = `SeqEnclosed tokens a` = `SeqTypedInterior`'s 2nd conjunct. -/
def topTrue (tokens : Array (Positioned YamlToken)) (a : Nat) : Bool :=
  match (btFold (some []) (tokens.toList.take a)).bind (·.head?) with
  | some true => true | _ => false

/-- The WHOLE-path all-seq invariant = `SeqPathAllSeq tokens a`'s stack predicate
    (nonempty stack, every frame `true`). -/
def allTrue (tokens : Array (Positioned YamlToken)) (a : Nat) : Bool :=
  match btFold (some []) (tokens.toList.take a) with
  | some s => !s.isEmpty && s.all (· == true)
  | none => false

-- layouts confirmed: P has 9 tokens, N has 14
#guard P.size == 9
#guard N.size == 14

-- POSITIVE (all-seq path, a = 3): BOTH the top-projection and the whole-path invariant hold.
#guard topTrue P 3 == true
#guard allTrue P 3 == true

-- NEGATIVE (map in path, a = 7): the top-projection HOLDS, the whole-path invariant FAILS.
#guard topTrue N 7 == true
#guard allTrue N 7 == false

-- THE DISCRIMINATOR.  The top-projection (what `SeqTypedInterior` / the `desc` consumer carries) is
-- EQUAL across the pair, so it CANNOT exclude the negative; the whole-path invariant `SeqPathAllSeq`
-- DIFFERS, so it is the necessary discriminator the wrapper's DESCEND arm needs.
#guard topTrue P 3 == topTrue N 7      -- projection equal ⇒ SeqTypedInterior insufficient
#guard allTrue P 3 != allTrue N 7      -- whole-path differs ⇒ SeqPathAllSeq is load-bearing

end L4YAML.Proofs.EmitterScannability.SeqNestedWrapperIfaceProbe
