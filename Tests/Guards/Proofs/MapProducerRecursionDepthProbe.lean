import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Map-producer recursion-depth probe — `(i'-b-B2c-recursive-map — STEP D, producer-side probe)`

The PRODUCER-SIDE probe the blueprint queued after R449.  R449's `MapPathLocatorMoveProbe` settled the
map mirror's single-step shape (`map_move_trichotomy`) and found the severance RECURSES: the map mirror
over the CURRENT `RecSeqEntry.map`-stores-flat-`WellBracketed` deliverable serves only map-depth ≤ 1.
The fix is the FULLY-RECURSIVE map interior (`RecSeqEntry.map` additively storing `RecMapBody`).

This probe answers item (2) of the R450 plan: **`#guard`-confirm that, given the recursive field, the
map descent REACHES the inner `[b]`'s seq window at map-depth 2** — the target R449 found unreachable.
It walks the move arithmetic TWICE on the actual `[{a:{x:[b]}}]` token layout, one DESCEND-VALUE per
map level, landing on the inner seq opener.  (The producer-citation-cycle half of the finding — why the
additive field forces a `mutual theorem` refactor of the value+saved-key producers — is modelled core-
Lean in `Tests/Reflections/AdditiveFieldForcesProducerMutualRecursion.lean`.)

## The two-level descent (M3 `[{a:{x:[b]}}]`).

Layout: `0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:{ 7:key 8:"x" 9:value 10:[ 11:"b" 12:] 13:} 14:} 15:] 16:SE`.

* **Level-1 map** body off = 3.  Head pair `key "a" value {…}` : `K = |block_k| = 1` (`"a"`@4),
  `V = |block_v| = 8` (the inner map `{…}`@`[6,13]`).  Target opener `op = 6` (the inner `{`):
  DESCEND-VALUE region `off+K+2 = 6 ≤ op ≤ off+K+V+1 = 13` — fires, landing on the inner map entry.
* **Level-2 map** body off = 7.  Head pair `key "x" value […]` : `K = 1` (`"x"`@8), `V = 3` (the seq
  `[b]`@`[10,12]`).  Target opener `op = 10` (the inner `[`): DESCEND-VALUE region
  `off+K+2 = 10 ≤ op ≤ off+K+V+1 = 12` — fires, landing on the inner SEQ opener.

So the inner `[b]`'s window `[11,12)` (the depth-2 target) is reached by TWO `map_move_trichotomy`
DESCEND-VALUE steps — provided each level's `RecSeqEntry.map` STORES its `RecMapBody` so the navigator
can take the second step.  With the current flat-`WellBracketed` storage the FIRST DESCEND-VALUE lands
on a `RecSeqEntry.map` whose body is unstored, dead-ending before the second step (the R449 severance).
The recursive field is exactly what unblocks step two.  Sorry-free.
-/

namespace L4YAML.Proofs.EmitterScannability.MapProducerRecursionDepthProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)
open L4YAML.Proofs.EmitterScannability (btFold)

/-- The map move's DESCEND-VALUE predicate (the middle disjunct of R449's `map_move_trichotomy`): a
    target opener `op` lands in the value `RecSeqEntry` of a `RecMapBody` head pair at base offset `off`
    with key length `K`, value length `V`.  Pure length arithmetic — no balance call. -/
def descendValue (off K V op : Nat) : Prop := off + K + 2 ≤ op ∧ op ≤ off + K + V + 1

instance (off K V op : Nat) : Decidable (descendValue off K V op) := by
  unfold descendValue; exact inferInstance

/-- **The depth-2 descent is two DESCEND-VALUE steps.**  At the level-1 map (`off=3, K=1, V=8`) the
    inner-map opener `op=6` is a DESCEND-VALUE; at the level-2 map (`off=7, K=1, V=3`) the inner-seq
    opener `op=10` is a DESCEND-VALUE — so the navigator reaches the inner seq by composing two moves,
    each decided by `omega` on the stored block lengths.  This is the concrete depth-2 reach R449's
    `MapPathLocatorMoveProbe` found UNREACHABLE under the flat deliverable. -/
theorem two_level_descend_reaches_inner_seq :
    descendValue 3 1 8 6 ∧ descendValue 7 1 3 10 := by
  constructor <;> (unfold descendValue; omega)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- M3 := `[{a:{x:[b]}}]` — two map levels, inner seq `[b]` the depth-2 target.
def m3 : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .mapping .flow #[(sc "x", .sequence .flow #[sc "b"])])]]
def M3 : Array (Positioned YamlToken) :=
  match scanFiltered (emit m3) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:{ 7:key 8:"x" 9:value 10:[ 11:"b" 12:] 13:} 14:} 15:] 16:SE
#guard M3.size == 17

-- ── Level-1 map: body off = 3; the head pair's value region begins at off+K+2 = 6. ──
#guard M3[2]!.val == .flowMappingStart        -- level-1 `{`; body off = 3
#guard M3[3]!.val == .key                      -- kt@3
#guard M3[5]!.val == .value                    -- vt@5  (K = |block_k| = 1, "a"@4)
-- value block = the inner map `{…}` @ [6,13] ⇒ V = 8.  DESCEND-VALUE op = 6 (the inner `{`).
#guard M3[6]!.val == .flowMappingStart         -- DESCEND-VALUE lands on a NESTED MAP (a RecSeqEntry.map)
#guard decide (descendValue 3 1 8 6)           -- step 1 fires
-- the level-1 value block is positions [6,13]: 8 tokens (V = 8).
#guard (((M3.toList.take 14).drop 6)).length == 8

-- ── Level-2 map: the inner map's body off = 7; its value region begins at off+K+2 = 10. ──
#guard M3[6]!.val == .flowMappingStart         -- inner `{` @ 6; inner body off = 7
#guard M3[7]!.val == .key                      -- kt'@7
#guard M3[9]!.val == .value                    -- vt'@9  (K' = 1, "x"@8)
#guard M3[10]!.val == .flowSequenceStart       -- DESCEND-VALUE lands on the inner SEQ opener
#guard decide (descendValue 7 1 3 10)          -- step 2 fires
-- the level-2 value block is positions [10,12]: 3 tokens (V' = 3).
#guard (((M3.toList.take 13).drop 10)).length == 3

-- ── The depth-2 target window `[11,12)` (the inner `[b]`), in the seq carrier's path-blind domain. ──
#guard M3[10]!.val == .flowSequenceStart
#guard M3[12]!.val == .flowSequenceEnd
#guard flowBracketBalance M3 11 12 == 0                                      -- balanced body
#guard (btFold (some []) (M3.toList.take 11)).bind (·.head?) == some true    -- top frame `[`
-- ancestor stack at the inner `[`: `[ { { [` ⇒ TWO `{` deep — the depth-2 nest the navigator must cross.
#guard btFold (some []) (M3.toList.take 11) == some [true, false, false, true]

/-! ## The contrast (R449, restated): the FIRST DESCEND-VALUE lands on a `.map`, not a `.seq`, so under
    the flat deliverable the descent dead-ends BEFORE step two; the recursive `RecMapBody` field is
    exactly what lets step two fire. -/
#guard decide (M3[6]!.val == .flowMappingStart)    -- step-1 landing is a map ⇒ needs RecMapBody to continue
#guard decide (M3[10]!.val == .flowSequenceStart)  -- step-2 landing is the seq ⇒ the depth-2 deliverable

end L4YAML.Proofs.EmitterScannability.MapProducerRecursionDepthProbe
