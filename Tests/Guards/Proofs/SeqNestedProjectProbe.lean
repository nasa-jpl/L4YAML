import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `rec_seq_body_nested_project` measure + offset-rebasing probe

A CONCRETE-emitter probe, run BEFORE authoring `rec_seq_body_nested_project` (Phase J,
`(i'-b-B2c-nested-project)`), per `ref-probe-deferred-universal-before-producing` /
`ref-metric-bridge-is-composition`.  `rec_seq_body_nested_project` projects the ROOT emission
`RecSeqBody ((tokens.toList.take (size-2)).drop 2)` (seed `seqRoot_recseqbody`, LANDED) DOWN to a
located nested seq window `RecSeqBody ((tokens.toList.take j).drop (p+1))`, descending the
`RecSeqBody`/`RecSeqEntry` structure one bracket level per step, with the matched-entry leaf
`recseqentry_seq_extract` (LANDED) at each descent bottom.

This probe settles the recursion's **well-founded measure** and its **per-descend offset
re-basing** on three witnesses BEFORE committing to the fixpoint:

* the structural extraction calls a THEOREM (`recseqentry_seq_extract`) whose result is opaque to
  the structural-recursion checker, so the recursion CANNOT be structural on the `RecSeqBody`
  argument — it must be `termination_by body.length` with a trivial `decreasing_by`;
* the measure decrease and the slice re-basing must compose with the located window's
  token-coordinate interior `(toList.take j).drop (p+1)`.

The three recursion MOVES, each exercised by a witness:

* `[[1, 2], 9]` — **direct head**: the root body head entry IS the located seq (`p = 2` heads the
  first entry of the root window `[2, 9)`); one terminal extract, no spine-walk, no descent;
* `[1, [2, 3]]` — **advance-then-head**: the located opener `p = 4` is the head of the SECOND
  entry, so the recursion advances past entry "1" (onto `rest`) before the head extract;
* `[[[1, 2]]]` — **descend-into-interior**: the located opener `p = 3` lies strictly INSIDE the
  root head entry's interior, so the recursion descends into that entry's stored interior
  `RecSeqBody` (a depth-2 located window) before the head extract.

The KEY facts the probe pins per move:

* **measure**: each recursive call's body slice is strictly shorter than its parent's
  (`rest.length < body.length` on advance; `interior.length < body.length` on descend);
* **offset re-basing**: the located interior `(toList.take j).drop (p+1)` equals the slice reached
  by peeling the parent window `B := (toList.take H).drop lo` — `B.take e.length` is the head entry,
  `(B.take e.length).drop 1 |>.dropLast` is its interior — confirming the spine-walk's
  peel-and-extract lands EXACTLY the deliverable's token-coordinate slice;
* **entry selection**: the located opener `p` sits at `flowBracketBalance = 0` from the active base
  (it is an entry head at that nesting level), the `SafeBody_flowEntry_zero_balance` /
  `flowBracketBalance_eq_pbalance` template selecting that entry.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqNestedProjectProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- ════════════════════ Witness N := `[[1, 2], 9]` — DIRECT HEAD ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE
-- root body window [lo, H) = [2, 9); located seq opener p = 2, close j = 6; interior [3, 6).
#guard N.size == 11
#guard N[2]!.val == .flowSequenceStart        -- located opener p = 2
#guard N[6]!.val == .flowSequenceEnd          -- located close  j = 6

-- entry selection: p = 2 sits at balance 0 from the root base lo = 2 (it heads the first entry).
#guard flowBracketBalance N 2 2 == 0
#guard flowBracketDelta N[2]!.val == 1        -- opener delta (the head entry is a seq)

-- the root body window slice B and the located interior I:
#guard ((N.toList.take 9).drop 2).length == 7                       -- B.length
#guard ((N.toList.take 6).drop 3).length == 3                       -- I.length
-- measure: the terminal extract's interior is strictly shorter than the root body.
#guard decide (((N.toList.take 6).drop 3).length < ((N.toList.take 9).drop 2).length)

-- offset re-basing: I equals the head-entry interior peeled from B (head entry length = 5).
-- B.take 5 = head entry `[ "1" , "2" ]`; .drop 1 |>.dropLast = its interior `"1" , "2"` = I.
#guard (((N.toList.take 6).drop 3).map (·.val))
        == ((((N.toList.take 9).drop 2).take 5).drop 1).dropLast.map (·.val)
-- and I is exactly tokens 3,4,5:
#guard (((N.toList.take 6).drop 3).map (·.val)) == [N[3]!.val, N[4]!.val, N[5]!.val]

-- ════════════════════ Witness T := `[1, [2, 3]]` — ADVANCE-THEN-HEAD ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE
-- root body window [2, 9); located seq opener p = 4, close j = 8; interior [5, 8).
#guard T.size == 11
#guard T[4]!.val == .flowSequenceStart        -- located opener p = 4 (SECOND entry head)
#guard T[8]!.val == .flowSequenceEnd          -- located close  j = 8

-- entry selection: p = 4 sits at balance 0 from the root base lo = 2 (advance past entry "1"+`,`).
#guard flowBracketBalance T 2 4 == 0
#guard flowBracketDelta T[2]!.val == 0        -- first entry head is content (not the opener)
#guard T[3]!.val == .flowEntry                -- the separator the advance steps over

-- the root body window B and the advance tail `rest` (B.drop 2, past entry "1" + separator):
#guard ((T.toList.take 9).drop 2).length == 7                       -- B.length
#guard (((T.toList.take 9).drop 2).drop 2).length == 5              -- rest.length (after advance)
#guard ((T.toList.take 8).drop 5).length == 3                       -- I.length
-- measure: advance shrinks (5 < 7), then the extract interior shrinks (3 < 5).
#guard decide ((((T.toList.take 9).drop 2).drop 2).length < ((T.toList.take 9).drop 2).length)
#guard decide (((T.toList.take 8).drop 5).length < (((T.toList.take 9).drop 2).drop 2).length)

-- offset re-basing: rest = B.drop 2 sits at base lo+2 = 4; its head entry `[ "2" , "3" ]` has
-- length 5, and (rest.take 5).drop 1 |>.dropLast is its interior `"2" , "3"` = I.
#guard (((T.toList.take 8).drop 5).map (·.val))
        == (((((T.toList.take 9).drop 2).drop 2).take 5).drop 1).dropLast.map (·.val)
#guard (((T.toList.take 8).drop 5).map (·.val)) == [T[5]!.val, T[6]!.val, T[7]!.val]

-- ════════════════════ Witness D := `[[[1, 2]]]` — DESCEND-INTO-INTERIOR ════════════════════
def deepVal : YamlValue := .sequence .flow #[.sequence .flow #[.sequence .flow #[sc "1", sc "2"]]]
def D : Array (Positioned YamlToken) :=
  match scanFiltered (emit deepVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:[ 4:"1" 5:, 6:"2" 7:] 8:] 9:] 10:SE
-- root body window [2, 9); deepest located seq opener p = 3, close j = 7; interior [4, 7).
#guard D.size == 11
#guard D[2]!.val == .flowSequenceStart        -- root head entry opener (the descend target)
#guard D[3]!.val == .flowSequenceStart        -- located opener p = 3 (INSIDE the root head entry)
#guard D[7]!.val == .flowSequenceEnd          -- located close  j = 7

-- entry selection: p = 3 is NOT at the root base (it sits one level deep); after descending into
-- the root head entry's interior (new base 3), p = 3 sits at balance 0 from that base.
#guard flowBracketBalance D 2 3 == 1          -- p = 3 is strictly inside the root head entry
#guard flowBracketBalance D 3 3 == 0          -- after descend (base 3), p heads the entry

-- the root body window B, the root head entry's interior, and the located interior I:
#guard ((D.toList.take 9).drop 2).length == 7                       -- B.length
#guard ((D.toList.take 8).drop 3).length == 5                       -- root head entry interior len
#guard ((D.toList.take 7).drop 4).length == 3                       -- I.length
-- measure: descend shrinks (5 < 7), then the extract interior shrinks (3 < 5).
#guard decide (((D.toList.take 8).drop 3).length < ((D.toList.take 9).drop 2).length)
#guard decide (((D.toList.take 7).drop 4).length < ((D.toList.take 8).drop 3).length)

-- offset re-basing across the descend: the root head entry is B.take 7 (the whole body, one entry);
-- its interior (B.take 7).drop 1 |>.dropLast = `[ "1" , "2" ]` is the depth-1 window, whose own
-- head entry's interior `"1" , "2"` = I.
#guard (((D.toList.take 8).drop 3).map (·.val))                     -- depth-1 interior = root entry int
        == ((((D.toList.take 9).drop 2).take 7).drop 1).dropLast.map (·.val)
#guard (((D.toList.take 7).drop 4).map (·.val)) == [D[4]!.val, D[5]!.val, D[6]!.val]

end L4YAML.Proofs.EmitterScannability.SeqNestedProjectProbe
