module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The sequence lane gets frames, and then a cover (DOCS item 155)

Items 152 and 153 named three fields as the last residue of the cover's work —
`pendingProps.h_closeFE`, `pendingBlockContent.h_closeF` and
`pendingBlock.h_closeF`, "one chain carrying widths alone".  Adding a cover
conjunct to the three of them is what this item was recorded as.

**Measuring first showed that would have bought nothing.**  A cover is spent by
popping the frames to the landing's width, and `ResumeFrames.resumeAt` gates on
`FrameLevel.map j ∈ ks`: a landing can only resume at a width the frames NAME.  Flipping
`pendingBlock.h_closeF`'s escape from `True` to `False` reports six punts of
seven producers, and the seventh pays `ks = []`.  So the lane's frames were
empty wherever they existed at all, and a cover over an empty list is spendable
nowhere.  The residue was never the cover.  It was the frames.

**Where a non-empty list exists is the mapping value the sequence fills.**  A
landed `-` on a `pendingMapValue` opens the collection that becomes the awaited
node, and the mapping level the park stands in is still open underneath it —
which is exactly what that park's `h_closeF` has said since item 108, cover
included.  `accum_block_on_closeThenBlock` closes the park before the `-` arm
runs, so this item carries that reading past the close as a parameter, and the
sequence park's frames become `FrameLevel.map nv :: ks` instead of `[]`.

§1 is the gate that made the recorded item vacuous.  §2 is the census, by the
compiler.  §3 is the payment and its side condition.  §4 is the cover, and the
one hop the index-bounded floor unlocked.  §5 walks the corpus — and corrects
which corpus item 154 measured.  §6 is what still does not pay.  §7 is the
price. -/

namespace L4YAML.Tests.Guards.SeqLaneFramesSpent

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.CouplingBridge

/-! ## §1  A cover over an empty list is spendable nowhere

The landing's hop is `ResumeFrames.resumeAt`, and its premise is membership. -/

example {P : SurfPos → Prop} {sp : SurfPos} {ks : List FrameLevel} {j : Nat}
    (h : ResumeFrames P ks sp) (hmem : FrameLevel.map j ∈ ks) :
    ∃ ks', ResumeWidths ks ks' j ∧
      (∀ sp_end, SCompactMapTail j sp sp_end → ResumeFrames P ks' sp_end) :=
  h.resumeAt hmem

-- …and `[]` has no members, so the one payment the lane carried before this
-- item could fund no landing at all.  `resumectx_of_landing` takes the same
-- gate (`by_cases hmem : FrameLevel.map k ∈ ks`) and returns the punt on its negative side.
example {j : Nat} : FrameLevel.map j ∉ ([] : List FrameLevel) := List.not_mem_nil

/-! ## §2  The census, by the compiler

Flipping a field's `∨ True` escape to `∨ False` turns every PUNT into an error
and leaves every payer compiling — the same instrument as the `[210]` flip.

* `pendingBlock.h_closeF`, before this item: **six punts of seven producers**
  (StreamAccum 15112, 15353, 16065, 16285, 16349, 16513), and the seventh —
  `accum_block_on_closeThenBlock`'s landed `-` — pays `ks = []`.
* `h_valF`, the parameter this item adds: **nine punts and two payers** of
  eleven callers, distinguished by the argument each error names (`trivial` at
  a punt, `h_closeF155` at a payer).  The two payers are the two branches of
  `accum_block_pending`'s `pendingMapValue` arm, which is the only park that
  awaits a node when a block indicator lands on it.
* The cover conjunct, flipped on both the field and the local that pays it:
  **two errors, and they are exactly the two `ks = []` fallbacks**.  So the
  cover is present precisely where the frames are non-empty. -/

/-! ## §3  The payment, and the side condition

`[199] s-l+block-collection` puts the landing's comments in front of the
entries, so the collection the `-` opens IS the awaited node — `nestedBlockSeq`
at the park's own index, with the landing's own `SSLComments` inside it. -/

example {sp_start sp_scan sp_mid : SurfPos} {nv k : Nat} {ks : List FrameLevel}
    (hnv : nv < k)
    (h_ssl : SSLComments sp_scan sp_mid)
    (closeF : ∀ sp_m : SurfPos, SBlockNode nv .blockIn sp_scan sp_m →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map nv :: ks) sp_m) :
    ∀ sp_end : SurfPos, SBlockSeqEntries k sp_mid sp_end →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map nv :: ks) sp_end :=
  fun sp_end h_entries => closeF sp_end (nestedBlockSeq (Nat.le_of_lt hnv) h_ssl h_entries)

/-- The side condition is `[183]`'s `m` read as a bound: the frames are
    strictly decreasing, so the level the collection FILLS has to sit strictly
    left of the collection's own index. -/
example {nv k : Nat} {ks : List FrameLevel} (hnv : nv < k) (h_lt : ∀ fr ∈ ks, fr.width < nv) :
    ∀ fr ∈ FrameLevel.map nv :: ks, fr.width < k := fun fr hfr => by
  rcases List.mem_cons.mp hfr with rfl | h'
  · exact hnv
  · exact Nat.lt_trans (h_lt fr h') hnv

/-! ## §4  The cover, bounded at the field's own index

Items 152/153 left the index existential, because their payers bounded their
lists at levels the consumer could not name and `Floor.pop_to` spends the widths
half alone.  This lane's payer knows its index — `nv < k` gives it — so the
field states the floor AT the index, and that is what lets the hop below run. -/

example {lo nv k : Nat} {ks : List FrameLevel} (hnv : nv < k) (h : Floor lo nv (FrameLevel.map nv :: ks)) :
    Floor lo k (FrameLevel.map nv :: ks) := h.mono_index (Nat.le_of_lt hnv)

/-- The hop the index bought: the pack's NESTED branch conses the park's own
    level onto the carried frames, and an existential index could not have said
    the floor was at or below it.  Six punts in the entry-key-pack relays (items
    148 and 149, three sites, two faces each) close on this one line. -/
example {sc : ScannerState} {lo n : Nat} {ks : List FrameLevel}
    (h_fl : Floor lo n ks) (h_cv : Covered lo ks sc) :
    Floor lo n (FrameLevel.map n :: ks) ∧ Covered lo (FrameLevel.map n :: ks) sc :=
  ⟨h_fl.cons h_fl.1, h_cv.cons n⟩

/-! ## §5  The corpus — and which corpus

**Item 154's sweep measured the wrong files, and its numbers are restated
here.**  `yaml-test-suite/src/*.yaml` are not YAML payloads; they are test
DESCRIPTORS, each a root sequence of mappings, and walking them reads 8661
states across exactly THREE indent-stack shapes.  The payloads live in the
`yaml: |` blocks, and `Tests.SuiteRunner.parseTestFile` is what extracts them.

Walked over the payloads, 351 files give **406 cases and 3262 states** in
**23** distinct stack shapes.  Item 154's claim survives the correction:
**489 states at column 0, all 489 armed, 2 facing a real dedent, both floored,
and 0 with the flag down.**  The support is thinner than the descriptor sweep
suggested (2 real dedents, not 52) but it is not vacuous.

This item's own population is the states whose stack top is a SEQUENCE with a
MAPPING still open below it: **120**, of which **19** face a pop at the next
step and **18** land exactly on that mapping's width.  Those 18 are the landings
that now resume the level instead of re-opening at the root.  The gap between
120 and 19 is not a miss: a key at the sequence's own indentation is
`trailingContent`, refused by the scanner before any dispatch runs (§5's last
control). -/

private def seqOverMap (s : ScannerState) : Option Nat :=
  match s.indents.back? with
  | some top =>
      if top.isSequence then
        let below := s.indents.toList.filter (fun (e : IndentEntry) =>
          !e.isSequence && 0 ≤ e.column && e.column < top.column)
        match below.reverse.head? with
        | some m => some m.column.toNat
        | none => none
      else none
  | none => none

private def factsS (s : ScannerState) : Nat × Nat × Nat :=
  match seqOverMap s with
  | none => (0, 0, 0)
  | some w =>
    match scanNextToken_preprocess s with
    | .ok (some (s', _)) =>
        let pop := s'.indents.size < s.indents.size
        (1, if pop then 1 else 0, if pop && s'.col == w then 1 else 0)
    | _ => (1, 0, 0)

private def walkS (s : ScannerState) : Nat → Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, a, b, c) =>
    let (a', b', c') := factsS s
    let acc := (seen + 1, a + a', b + b', c + c')
    match scanNextToken s with
    | .ok (some s') => walkS s' fuel acc
    | _ => acc

private def censusS (inputs : List String) : Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkS (ScannerState.mk' i) 400 acc) (0, 0, 0, 0)

-- The tuple is: states seen / stack top a SEQUENCE over a MAPPING / of those,
-- facing a pop / of those, landing ON the mapping's own width.
--
-- **46** states, **11** with the shape, **2** facing a pop, both landing on the
-- mapping.  The two are the two inputs the item is for; the four controls
-- contribute the zeros that keep the count from being an artifact.
#guard censusS
  ["k:\n  - a\nb: 2\n",
   "k:\n  - a\n  - b\nc: d\n",
   "k:\n- a\nb: 2\n",
   "- a\n- b\n",
   "k: v\nb: 2\n",
   "k:\n  - a\n  - b\n  c: d\n"] == (46, 11, 2, 2)

-- The flagship, alone: `k:` opens the mapping at 0, `- a` the sequence at 2,
-- and `b: 2` lands back at 0 — `nv = 0 < 2 = k`, so the frames are `[0]` and
-- the landing pops to a width they name.
#guard walkS (ScannerState.mk' "k:\n  - a\nb: 2\n") 400 (0,0,0,0) == (8, 2, 1, 1)
#guard walkS (ScannerState.mk' "k:\n  - a\n  - b\nc: d\n") 400 (0,0,0,0) == (10, 4, 1, 1)

-- **The shape that cannot pay is the shape that cannot reach the premise.**
-- `seq-spaces` lets a block sequence sit at its key's own column, and there the
-- `-` pushes no level at all — the stack stays `[0M]`, `nv < k` would be
-- `0 < 0`, and the state never has the shape the payment asks about.  Item
-- 154's `"k: |"` had the same structure.
#guard walkS (ScannerState.mk' "k:\n- a\nb: 2\n") 400 (0,0,0,0) == (8, 0, 0, 0)
#guard (match Events.streamToEvents "k:\n- a\nb: 2\n" with | .ok s => s | .error _ => "")
  == "+STR\n+DOC\n+MAP\n=VAL :k\n+SEQ\n=VAL :a\n-SEQ\n=VAL :b\n=VAL :2\n-MAP\n-DOC\n-STR\n"

-- …and the events of the two paying inputs, so the census is anchored to a
-- parse rather than to a walk alone.
#guard (match Events.streamToEvents "k:\n  - a\nb: 2\n" with | .ok s => s | .error _ => "")
  == "+STR\n+DOC\n+MAP\n=VAL :k\n+SEQ\n=VAL :a\n-SEQ\n=VAL :b\n=VAL :2\n-MAP\n-DOC\n-STR\n"

-- The refusal that explains the gap between 120 and 19: a key at the sequence's
-- own indentation never reaches a dispatch.
#guard (match Events.streamToEvents "k:\n  - a\n  - b\n  c: d\n" with
        | .ok _ => "ok" | .error e => toString (repr e))
  == "L4YAML.ScanError.trailingContent 3 2"

/-! ## §6  What still does not pay

* **The `ks = []` fallbacks.**  Two of `h_seqFrames`' three branches keep item
  99's bottomed reading: a park that awaited no node, and a landing at the
  awaited level's own column.  Neither is a missing derivation — the first has
  nothing open below by construction, and the second is the `seq-spaces` shape
  §5 shows never reaching the premise.
* **The nine punting `h_valF` callers.**  Eight close a park that awaits no
  node at all (the two markers, the flow park, the props park, the content
  parks); the ninth is `accum_block_on_pendingBlock`'s dedent fallback, where
  the inner collection ends and the outer frame is what the park does not carry
  (item 30's split).
* **The membership split**, still declined for item 150's reason: paying it
  needs a payload on `KeyPackPunt`, a change to the constructor and to every
  consumer. -/

/-! ## §7  The price

**No new declaration.**  One parameter on `accum_block_on_closeThenBlock`, two
on `accum_content_on_pendingBlock_indented`, a cover conjunct on each of the
three recorded fields, and two `have`s.  Everything the payment is built from —
`nestedBlockSeq`, `Floor.mono_index`, `Floor.cons`, `Covered.cons`,
`scanBlockEntry_cover`, `landing_floor_of_arm`, `dedent_cover_of_floor` — was
already in the library, including the `-`'s own cover step, which existed
because the frames record mapping levels and a sequence push is exempt. -/

end L4YAML.Tests.Guards.SeqLaneFramesSpent

end Blanket
