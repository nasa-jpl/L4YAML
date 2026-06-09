import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `rec_seq_body_nested_project` DOMAIN-COVERAGE probe — the map-PATH-nested seq window

The mandated FIRST de-risk before authoring the seq driver `rec_seq_body_nested_project`
(Phase J, `(i'-b-B2c-nested-project, the DRIVER fixpoint)`), per
`ref-probe-deferred-universal-before-producing` / `ref-probe-provider-head-blind-gate`:
the driver projects the ROOT emission `RecSeqBody ((tokens.toList.take (size-2)).drop 2)`
(seed `seqRoot_recseqbody`, LANDED) DOWN to a located nested seq window, navigating the
`RecSeqBody`/`RecSeqEntry` STRUCTURE, and is wired through `seqSeparatorFacts_of_recseqbody`
into `seqRoot_seqInteriorSeparators`'s `desc` — so it must produce `RecSeqBody` at EVERY
gated seq window `desc` is invoked on.

The three landed-arm probes (`SeqNestedProjectProbe`, `SeqDescentProviderProbe`,
`SeqDispatchPartitionProbe`) all use ALL-SEQ witnesses (`[[1,2],9]`, `[1,[2,3]]`, `[[[1,2]]]`),
where every nested seq window is reachable by walking the root `RecSeqBody`'s `.seq` interiors.
This probe exercises the UNPROBED complement: a seq window whose path from the root passes
through a `.map` entry.

**Witness `[{a: [b]}]`** — a flow sequence whose lone entry is a flow MAPPING whose value is a
flow sequence.  Token layout (size 12):

```
0:SS  1:[  2:{  3:key  4:"a"  5:value  6:[  7:"b"  8:]  9:}  10:]  11:SE
```

The inner seq `[b]`'s body window is `[7, 8)` (just the scalar `"b"`).  The probe pins TWO facts
that together expose the gap:

* **The window IS in `desc`'s domain.**  It is gated SEQ-typed — `flowBracketBalance 7 8 = 0`
  (gate conjunct 1), and the typed-bracket stack after `take 7` has top `true` (gate conjunct 2:
  the inner `[` at position 6 pushes `true`, so the window is enclosed by a SEQUENCE, not a
  mapping) — AND it is nested — `flowBracketBalance 2 7 = 2 ≠ 0`.  So
  `seqInteriorSeparators_of_safebody_and_descent`'s dispatch routes it to the `desc` branch
  (`flowBracketBalance tokens 2 a ≠ 0`), exactly like the all-seq nested windows.

* **The window is NOT reachable by `RecSeqBody`-navigation.**  The root body window `[2, 10)`
  is a SINGLE entry whose head at position 2 is `.flowMappingStart` — a `RecSeqEntry.map`, which
  stores its interior as `h_wb : WellBracketed interior` only (NonemptyStructure.lean:466–469),
  with NO `h_rec : RecSeqBody` field.  So the inner seq `[b]`'s `RecSeqBody` is buried in an
  opaque `WellBracketed` and CANNOT be extracted by descending the root `RecSeqBody`
  (`recseqbody_descend` / `recseqentry_seq_extract` both require a `.flowSequenceStart` head and
  read the `.seq` constructor's `h_rec`; a `.flowMappingStart` head has no `RecSeqBody` to read).

**Conclusion (`ref-probe-provider-head-blind-gate` / `ref-downstream-derisk-restores-upstream`).**
`desc`'s domain (all gated seq windows) STRICTLY contains what root-`RecSeqBody`-projection can
serve (all-seq-PATH windows only).  `rec_seq_body_nested_project` as specced — a recursion over
the root `RecSeqBody` bottoming at `recseqbody_head_seq_project` — is therefore NOT a total `desc`
provider: a `.flowMappingStart` head in its DESCEND branch is a window it cannot inhabit, and the
map mirror does not rescue it (the located window is seq-TYPED, so it is the seq carrier's
responsibility, not the map carrier's).  The driver's domain must be RESTRICTED to all-seq-path
windows (carrying the path-is-all-seq fact as a hypothesis), and map-path-nested seq windows need
a SEPARATE provider — most cheaply the FLAT one, since such a window is itself a genuine emitted
seq body whose `SafeBodyUnit` comes straight off emission (`seqRoot_safeBodyUnit`-style), no
recursion through the not-yet-built `RecSeqBody` tree.  Surfacing this BEFORE authoring averts a
doomed fixpoint that would wall at the map-head DESCEND with no sorry-free discharge.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqMapPathNestedProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- Witness `[{a: [b]}]`: a flow seq whose lone entry is a flow MAP whose value is a flow seq.
def mapVal : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b"])]]
def M : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:[ 7:"b" 8:] 9:} 10:] 11:SE
#guard M.size == 12

-- ── The inner seq `[b]`: opener p = 6, close j = 8, body window [7, 8). ──
#guard M[6]!.val == .flowSequenceStart        -- inner seq opener p = 6
#guard M[8]!.val == .flowSequenceEnd          -- inner seq close  j = 8

-- ── (A) The window [7, 8) IS in `desc`'s domain — gated SEQ-typed AND nested. ──
-- gate conjunct 1: the body is depth-0 balanced.
#guard flowBracketBalance M 7 8 == 0
-- gate conjunct 2: the typed-bracket stack after `take 7` has top `true` — SEQ-enclosed
-- (the inner `[` at position 6 pushes `true`), so the window is the SEQ carrier's responsibility.
#guard (btFold (some []) (M.toList.take 7)).bind (·.head?) == some true
-- nested: balance from the root base 2 is non-zero, so the dispatch takes the `desc` branch.
#guard flowBracketBalance M 2 7 == 2
#guard decide (flowBracketBalance M 2 7 ≠ 0)

-- ── (B) The window is NOT reachable by root-`RecSeqBody`-navigation. ──
-- The root body window [2, 10) is a SINGLE entry whose head is a `.flowMappingStart` —
-- a `RecSeqEntry.map`, which stores `WellBracketed interior` only (no `RecSeqBody` field).
#guard M[2]!.val == .flowMappingStart
-- the opener delta is +1 (it IS an opener — the recursion's DESCEND guard fires), but the
-- type is mapping, not sequence: `recseqbody_descend`'s `h_lo_open : … = .flowSequenceStart`
-- is FALSE here, so the seq DESCEND arm does not apply and there is no `h_rec` to read.
#guard flowBracketDelta M[2]!.val == 1
#guard decide (M[2]!.val ≠ .flowSequenceStart)

-- Contrast: in the all-seq witness `[[[1,2]]]` the root head IS a `.flowSequenceStart` (a
-- `RecSeqEntry.seq` carrying `h_rec : RecSeqBody`), so its DESCEND reads the stored interior.
def deepVal : YamlValue :=
  .sequence .flow #[.sequence .flow #[.sequence .flow #[sc "1", sc "2"]]]
def D : Array (Positioned YamlToken) :=
  match scanFiltered (emit deepVal) with | .ok ts => ts | .error _ => #[]
#guard D[2]!.val == .flowSequenceStart        -- all-seq path: head IS a seq ⇒ `h_rec` readable

end L4YAML.Proofs.EmitterScannability.SeqMapPathNestedProbe
