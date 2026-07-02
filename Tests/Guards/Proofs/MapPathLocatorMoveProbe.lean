import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Map-path locator single-step probe — `(i'-b-B2c-map-mirror — STEP D)`

The PROBE the blueprint queued after R448.  R448 established the seq ROOT CARRIER
`SeqInteriorSeparators tokens 2 (size-2)` is NOT seq-side-completable: its domain (`SeqTypedInterior`,
path-blind top frame `[`) admits MAP-nested seqs the all-seq locator (`SeqPathAllSeq` reach) cannot
reach (the seq spine severs at `RecSeqEntry.map`'s flat `WellBracketed`).  The deferred MAP-PATH
locator (the map mirror) is on the carrier's critical path.

This probe settles the map mirror's **single-step shape** BEFORE authoring — the map analog of R350's
seq `SeqNestedEntryLocateProbe` (`move_trichotomy`).  It also surfaces the DECISIVE finding for the
route decision: **the severance RECURSES by map-nesting depth**.

## The map move decision — pure LENGTH ARITHMETIC (the map analog of R350's `move_trichotomy`).

The map navigator walks `RecMapBody body` with the absolute base offset `off` of `body`.  The head
pair `p = kt :: (block_k ++ vt :: block_v)` occupies `[off, off + P - 1]` where
`P = p.length = 1 + K + 1 + V` (`K = block_k.length`, `V = block_v.length`).  Inside the pair:

* `kt` (the `.key` marker) at `off`;
* `block_k` (the key `RecSeqEntry`) at `[off+1, off+K]` — opener (if seq/map) at `off+1`;
* `vt` (the `.value` marker) at `off+1+K`;
* `block_v` (the value `RecSeqEntry`) at `[off+2+K, off+1+K+V]` — opener at `off+2+K`;
* (cons) `.flowEntry` at `off+P`; `rest` (the next `RecMapBody`) at `off+P+1`.

A target seq-window OPENER `op` (the `[` of the target) selects the move by comparing `op` against the
key/value regions and the pair end ALONE — `map_move_trichotomy`, pure `omega`:

* `off+1   ≤ op ≤ off+K`       → **DESCEND-KEY** into the key `RecSeqEntry` (offset `off+1`);
* `off+K+2 ≤ op ≤ off+K+V+1`   → **DESCEND-VALUE** into the value `RecSeqEntry` (offset `off+K+2`);
* `off+K+V+3 ≤ op`             → **ADVANCE** to `rest` (new `off' = off+K+V+3 = off+P+1`).

(`op = off` is the `.key` marker, `op = off+K+1` the `.value` marker, `op = off+K+V+2` the `.flowEntry`
separator — none a seq opener, so the trichotomy is exhaustive on valid openers.)  Like R350, NO
balance call inside the recursion — the descend/advance selector is pure length arithmetic.

Once DESCEND-KEY/VALUE reaches a key/value `RecSeqEntry`, the EXISTING seq machinery takes over: if
that entry is `.seq`, read its stored `h_rec : RecSeqBody interior` and hand to the seq locator
(`nestedSeq_recseqentry_locate`) — the key/value split is the only genuinely-map part; below it the
deliverable is the seq one already in hand.

## The DECISIVE finding — the severance RECURSES; the map mirror over the CURRENT `RecMapBody` reaches
## exactly ONE map level.

`RecSeqEntry.map` (NonemptyStructure.lean:500-503) stores only `h_wb : WellBracketed interior` — NO
recursive `RecMapBody`, exactly as it stores no `RecSeqBody` (the seq severance R448 found).  So the
MAP navigator dead-ends at a NESTED map precisely as the SEQ navigator dead-ends at a map:

* **M1 `[{a:[b]}]`, M2 `[{a:[b,c]}]`** — one map level: the target seq is the map VALUE itself
  (`block_v` a `RecSeqEntry.seq`).  DESCEND-VALUE reaches it; REACHABLE by the map mirror.
* **M3 `[{a:{x:[b]}}]`** — two map levels: the map value `{x:[b]}` is a `RecSeqEntry.map` (stores only
  `WellBracketed`).  DESCEND-VALUE reaches THAT map entry, but its `RecMapBody` is not stored, so the
  inner `[b]` is UNREACHABLE — a SECOND severance, the mirror of the first.

Yet all three windows (`[b]`@M1 `[7,8)`, `[b,c]`@M2 `[7,10)`, `[b]`@M3 `[11,12)`) are in the seq
carrier's path-blind domain `SeqTypedInterior` (top frame `[`, balance-0, floor).  So the carrier owes
their facts but the map mirror over the CURRENT depth-bounded deliverable serves only the first two.

**Conclusion.**  The map mirror is necessary but the `RecSeqEntry.map`-stores-flat-`WellBracketed`
choice bounds it to ONE map level.  Closing the whole `SeqTypedInterior` domain (arbitrary map/seq
nesting, e.g. M3) needs the FULLY-RECURSIVE map interior — `RecSeqEntry.map` storing a recursive
`RecMapBody` — so the seq/map navigators MUTUALLY recurse to any depth (the doc's deferred "fully-
recursive map interior").  The route decision (item 3): a SEPARATE map navigator over `RecMapBody`
(the key/value split has no seq analog), but it shares the seq `RecSeqEntry`/`RecSeqBody` substrate
below the key/value descent, and full coverage requires making `RecSeqEntry.map` recursive.  Sorry-free.
-/

namespace L4YAML.Proofs.EmitterScannability.MapPathLocatorMoveProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)
open L4YAML.Proofs.EmitterScannability (btFold)

/-! ## The map move decision is length arithmetic (the map analog of R350's `move_trichotomy`). -/

/-- **The map-path move trichotomy is decided by LENGTH ARITHMETIC alone** — a target seq-window opener
    `op` against the key region `[off+1, off+K]`, the value region `[off+K+2, off+K+V+1]`, and the pair
    end.  For any valid opener that is not a marker / separator position, exactly one of descend-key /
    descend-value / advance fires.  Pure `omega`: the map navigator's branch selector is length
    arithmetic on the stored block lengths `K`, `V` — no balance front end (R350's (a) finding, map
    side). -/
theorem map_move_trichotomy (off K V op : Nat)
    (h_pos : off + 1 ≤ op)         -- past the `.key` marker at `off`
    (h_nval : op ≠ off + K + 1)    -- not the `.value` marker
    (h_nsep : op ≠ off + K + V + 2) : -- not the `.flowEntry` separator
    (off + 1 ≤ op ∧ op ≤ off + K)                       -- DESCEND-KEY
    ∨ (off + K + 2 ≤ op ∧ op ≤ off + K + V + 1)         -- DESCEND-VALUE
    ∨ (off + K + V + 3 ≤ op) := by                      -- ADVANCE
  omega

/-- The three map moves are mutually exclusive — the recursion's dispatch is unambiguous, again by
    `omega` on the same length data. -/
theorem map_move_exclusive (off K V op : Nat) :
    ¬ ((off + 1 ≤ op ∧ op ≤ off + K) ∧ (off + K + 2 ≤ op ∧ op ≤ off + K + V + 1)) ∧
    ¬ ((off + 1 ≤ op ∧ op ≤ off + K) ∧ (off + K + V + 3 ≤ op)) ∧
    ¬ ((off + K + 2 ≤ op ∧ op ≤ off + K + V + 1) ∧ (off + K + V + 3 ≤ op)) := by
  omega

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

-- ════════════ M1 := `[{a:[b]}]` — DESCEND-VALUE, value seq REACHABLE (one map level) ════════════
def m1 : YamlValue := .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b"])]]
def M1 : Array (Positioned YamlToken) :=
  match scanFiltered (emit m1) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:[ 7:"b" 8:] 9:} 10:] 11:SE
#guard M1.size == 12
#guard M1[2]!.val == .flowMappingStart       -- the map; map body off = 3
#guard M1[3]!.val == .key                     -- kt at off = 3
#guard M1[5]!.val == .value                   -- vt at off+K+1 = 5  (K = block_k.length = 1)
#guard M1[6]!.val == .flowSequenceStart       -- value seq opener at off+K+2 = 6
#guard M1[8]!.val == .flowSequenceEnd
-- the head pair `key "a" value [ "b" ]` = (map body).take 6, so P = 6, V = P-K-2 = 3.
#guard (((M1.toList.take 9).drop 3).take 6).length == 6
-- MOVE: op = 6, off = 3, K = 1, V = 3 → off+K+2 = 6 ≤ op ≤ off+K+V+1 = 8 → DESCEND-VALUE.
#guard decide (3 + 1 + 2 ≤ (6 : Nat) ∧ (6 : Nat) ≤ 3 + 1 + 3 + 1)   -- descend-value fires
#guard decide (¬ (3 + 1 + 2 ≤ (6 : Nat) ∧ (6 : Nat) ≤ 3 + 1))        -- descend-key does NOT fire
-- the located VALUE entry is a `.seq` (REACHABLE) — its window identity `op :: (interior ++ [cl])`
-- at lo = off+K+2 = 6, b = 8.
#guard ((M1.toList.take 9).drop 6).map (·.val)
        == [.flowSequenceStart, .scalar "b" .doubleQuoted, .flowSequenceEnd]
-- and the target window `[7,8)` IS in the seq carrier's domain `SeqTypedInterior` (facts owed here).
#guard flowBracketBalance M1 7 8 == 0
#guard (btFold (some []) (M1.toList.take 7)).bind (·.head?) == some true   -- top frame `[`

-- ════════════ M2 := `[{a:[b,c]}]` — DESCEND-VALUE, two-element value seq (one map level) ════════════
def m2 : YamlValue := .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b", sc "c"])]]
def M2 : Array (Positioned YamlToken) :=
  match scanFiltered (emit m2) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:[ 7:"b" 8:, 9:"c" 10:] 11:} 12:] 13:SE
#guard M2.size == 14
#guard M2[6]!.val == .flowSequenceStart       -- value seq opener at off+K+2 = 6 (off=3, K=1)
#guard M2[10]!.val == .flowSequenceEnd
-- head pair `key "a" value [ "b" , "c" ]` = (map body).take 8, P = 8, V = 5.
#guard (((M2.toList.take 11).drop 3).take 8).length == 8
-- MOVE: op = 6, off = 3, K = 1, V = 5 → off+K+2 = 6 ≤ op ≤ off+K+V+1 = 10 → DESCEND-VALUE.
#guard decide (3 + 1 + 2 ≤ (6 : Nat) ∧ (6 : Nat) ≤ 3 + 1 + 5 + 1)
-- value entry is a `.seq` with interior `[7,10)` (`"b" , "c"`); window identity at lo = 6, b = 10.
#guard ((M2.toList.take 11).drop 6).map (·.val)
        == [.flowSequenceStart, .scalar "b" .doubleQuoted, .flowEntry,
            .scalar "c" .doubleQuoted, .flowSequenceEnd]
#guard flowBracketBalance M2 7 10 == 0
#guard (btFold (some []) (M2.toList.take 7)).bind (·.head?) == some true   -- top frame `[`

-- ════════════ M3 := `[{a:{x:[b]}}]` — DESCEND-VALUE reaches a NESTED MAP ⇒ SECOND SEVERANCE ════════════
def m3 : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .mapping .flow #[(sc "x", .sequence .flow #[sc "b"])])]]
def M3 : Array (Positioned YamlToken) :=
  match scanFiltered (emit m3) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:{ 7:key 8:"x" 9:value 10:[ 11:"b" 12:] 13:} 14:} 15:] 16:SE
#guard M3.size == 17
-- (A) The level-1 map body off = 3.  The head pair's VALUE region begins at off+K+2 = 6.  DESCEND-VALUE
--     reaches position 6 — but it is a `.flowMappingStart`, a `RecSeqEntry.map` (NOT a `.seq`).
#guard M3[6]!.val == .flowMappingStart        -- the value is a NESTED MAP, not a seq
-- (B) The actual target seq `[b]` opener is DEEPER, at 10 — inside the nested map's value.
#guard M3[10]!.val == .flowSequenceStart
#guard M3[12]!.val == .flowSequenceEnd
-- (C) The SECOND severance: `RecSeqEntry.map` stores only `WellBracketed interior`, NO `RecMapBody`.
--     So after DESCEND-VALUE lands on the nested map entry, there is no map-body to recurse into —
--     the map navigator dead-ends, mirroring the seq navigator's dead-end at a map (R448).  The inner
--     `[b]`'s `RecSeqBody` is buried in the nested map's opaque `WellBracketed`.
#guard decide (M3[6]!.val ≠ .flowSequenceStart)   -- not a seq ⇒ no `h_rec` to read
#guard decide (M3[6]!.val == .flowMappingStart)   -- a map ⇒ only `h_wb`, the severance
-- (D) Yet the inner `[b]` window `[11,12)` IS in the seq carrier's path-blind domain `SeqTypedInterior`
--     — facts owed, but UNREACHABLE by the map mirror over the current depth-1 deliverable.
#guard flowBracketBalance M3 11 12 == 0
#guard (btFold (some []) (M3.toList.take 11)).bind (·.head?) == some true   -- top frame `[`
-- the ancestor path before `[b]`'s opener is `[ { { [`  ⇒ stack `[true,false,false,true]` (head `[`),
-- two `{` deep: NOT all-seq (severs the all-seq locator) AND two map levels (severs the map mirror).
#guard btFold (some []) (M3.toList.take 11) == some [true, false, false, true]

/-! ## The contrast in one line: depth-1 map-nested seqs are reachable; depth-2 are not — the second
    severance is the mirror of the first. -/

-- M1's `[b]` (depth-1): the map VALUE itself is a seq ⇒ DESCEND-VALUE lands on a `.seq` (reachable).
#guard decide (M1[6]!.val == .flowSequenceStart)
-- M3's matching position (depth-1 of a depth-2 nest): the map VALUE is a map ⇒ DESCEND-VALUE lands on a
-- `.map` (severs); the seq is one level deeper, behind the nested map's unstored `RecMapBody`.
#guard decide (M3[6]!.val == .flowMappingStart)

end L4YAML.Proofs.EmitterScannability.MapPathLocatorMoveProbe
