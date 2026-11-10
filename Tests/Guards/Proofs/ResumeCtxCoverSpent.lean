module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The resuming key context carries the landing's cover (DOCS item 151)

Items 148–150 gave both lanes a cover and taught the dedent landing to spend it,
and both items closed naming the same gap: `ResumeKeyCtx` — the context a landed
SIBLING key is handed when the park that closed under it kept its frames — had
no slot for one on either lane.  A landing that resumed through it therefore
dropped what the relay was holding, at the one relay that holds both.  This item
gives the context a slot on each lane, pays them where the evidence stands, and
spends them into the two pack fields the dispatch builds.

**The context's floor index is the PACK's, on both lanes.**  That is where the
value lane stops mirroring its parks.  A park's value-line frames exclude the
`?`'s own level, so their cover stands one column above the park (item 150); the
key this landing heads is a mapping level of EITHER stack, so nothing is
excluded here and `Floor lo k (FrameLevel.map k :: ks)` is what both faces carry.

**The index on the way IN is forgotten.**  The two incoming faces are bounded at
different indices — `n` on the stream lane, `n + 1` on the value lane — and the
hop reads neither, because `IndentStackCover.Floor.pop_to` spends the WIDTHS
half alone.  So one payer argument serves both.

§1 is the slot and its index.  §2 is `dedent_cover_of_floor`, the item's one new
declaration, and what it takes out of item 149's lemma.  §3 is the payment
composed, from the face to the pack field.  §4 walks the lane against the
scanner.  §5 is what still does not pay.  §6 is the price. -/

namespace L4YAML.Tests.Guards.ResumeCtxCoverSpent

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.CouplingBridge

/-! ## §1  The slot, and why its index is the pack's

The landing this context describes stands INSIDE an explicit key: the `?` opened
a mapping level, a key opened another, and the sibling that lands resumes the
inner one.  Item 150's seed excluded the `?`'s own level from the value-line
frames; the key's level is excluded from neither stack, and that is the whole
difference between the two floors. -/

/-- A `?` at column 0 with a key at column 2 inside it: three entries, the
    sentinel and two mapping levels. -/
private def inKey : ScannerState :=
  { ScannerState.mk' "" with
    indents := #[{ column := -1, isSequence := false },
                 { column := 0, isSequence := false },
                 { column := 2, isSequence := false }] }

example : inKey.currentIndent = 2 := by
  show (match inKey.indents.back? with | some e => e.column | none => -1) = 2
  rfl

/-- **The key's own level is NOT exempt on the value lane.**  At the `?`'s floor
    plus one, the empty list no longer covers: the key at 2 is an open mapping
    level and nothing names it.  So the list the pack carries has to be
    `FrameLevel.map k :: ks`, which is exactly the shape `ResumeKeyCtx` states. -/
example : ¬ Covered 1 [] inKey := by
  intro h
  have hm : ({ column := 2, isSequence := false } : IndentEntry) ∈ inKey.indents := by
    simp [inKey, ScannerState.mk']
  exact absurd (h _ hm rfl (by decide)) (by simp)

/-- …and with it named, the value lane's cover stands at the PACK's index. -/
example : Covered 1 [FrameLevel.map 2] inKey := by
  intro e he _ hlo
  have : e = { column := -1, isSequence := false } ∨
      e = { column := 0, isSequence := false } ∨
      e = { column := 2, isSequence := false } := by
    simpa [inKey, ScannerState.mk'] using he
  rcases this with rfl | rfl | rfl
  · exact absurd hlo (by decide)
  · exact absurd hlo (by decide)
  · simp

example : Floor 1 2 [FrameLevel.map 2] :=
  ⟨by omega, fun k' hk' => by simp at hk'; subst hk'; decide⟩

/-- The stream lane reads the same stack from the bottom, so its floor is 0 and
    its list names the `?`'s level too — the two lanes agree on the INDEX here
    and differ, as they always have, in what they are bottomed at. -/
example : Covered 0 [FrameLevel.map 0, FrameLevel.map 2] inKey := by
  intro e he _ hlo
  have : e = { column := -1, isSequence := false } ∨
      e = { column := 0, isSequence := false } ∨
      e = { column := 2, isSequence := false } := by
    simpa [inKey, ScannerState.mk'] using he
  rcases this with rfl | rfl | rfl
  · exact absurd hlo (by decide)
  · simp
  · simp

/-! ## §2  `dedent_cover_of_floor` — the hop with the escapes taken out

Item 149's `dedent_cover_of_landing` answers with a DISJUNCTION, because two of
its premises are escapes rather than facts: a caller that cannot measure its
stack, and a park at a line start whose walk armed no unwind.  A caller that has
discharged both wants the payment itself, and this lemma is that payment. -/

/-- The hop, at its own type: no disjunct to case on, and the floor VALUE
    travels unchanged — `w` was one of the frames, so the bound already reached
    it. -/
example {s : ScannerState} {lo n w : Nat} {ks ks' : List FrameLevel}
    (h_mono : Mono s) (h_top : s.currentIndent ≤ (w : Int))
    (h_fl : Floor lo n ks) (h_cv : Covered lo ks s)
    (hmem : FrameLevel.map w ∈ ks) (h_w' : ResumeWidths ks ks' w) :
    ∃ lo : Nat, Floor lo w (FrameLevel.map w :: ks') ∧ Covered lo (FrameLevel.map w :: ks') s :=
  dedent_cover_of_floor h_mono h_top h_fl h_cv hmem h_w'

/-- **The index on the incoming face is forgotten.**  The same conclusion
    follows from a face bounded at the park's index and from one bounded a
    column above it, which is why ONE payer serves the stream lane and the value
    lane whose floors item 150 deliberately staggered. -/
example {s : ScannerState} {lo n w : Nat} {ks ks' : List FrameLevel}
    (h_mono : Mono s) (h_top : s.currentIndent ≤ (w : Int))
    (h_cv : Covered lo ks s) (hmem : FrameLevel.map w ∈ ks) (h_w' : ResumeWidths ks ks' w)
    (h_stream : Floor lo n ks) (h_value : Floor lo (n + 1) ks) :
    (∃ lo : Nat, Floor lo w (FrameLevel.map w :: ks') ∧ Covered lo (FrameLevel.map w :: ks') s) ∧
    (∃ lo : Nat, Floor lo w (FrameLevel.map w :: ks') ∧ Covered lo (FrameLevel.map w :: ks') s) :=
  ⟨dedent_cover_of_floor h_mono h_top h_stream h_cv hmem h_w',
   dedent_cover_of_floor h_mono h_top h_value h_cv hmem h_w'⟩

/-- Run at a stack, so the payment is a value and not only a type: a landing at
    width 2 off a stack popped to it, with the frames `[4, 2]` the park carried.
    The floor comes out at 1 and the list at `[2]`.  (2026-11-10, item 473: the
    stack is written in its own order — the wider level above — because the
    positional `ResumeWidths` names what a landing at 2 leaves of it, `[]`, and
    has no reading for the ill-ordered `[2, 4]`.) -/
example : ∃ lo : Nat, Floor lo 2 [FrameLevel.map 2] ∧ Covered lo [FrameLevel.map 2] inKey := by
  refine dedent_cover_of_floor (s := inKey) (lo := 1) (n := 5) (ks := [FrameLevel.map 4, FrameLevel.map 2]) ?_ ?_ ?_ ?_
    (by simp) ?_
  · -- `Mono` on a stack whose columns increase: three entries, two steps.
    intro i hi
    have hs : inKey.indents.size = 3 := by simp [inKey, ScannerState.mk']
    rw [hs] at hi
    rcases i with _ | _ | i
    · simp [inKey, ScannerState.mk']
    · simp [inKey, ScannerState.mk']
    · omega
  · show inKey.currentIndent ≤ ((2 : Nat) : Int)
    show (match inKey.indents.back? with | some x => x.column | none => -1) ≤ 2
    decide
  · exact ⟨by omega, fun k' hk' => by simp at hk'; rcases hk' with rfl | rfl <;> decide⟩
  · intro e he _ hlo
    have : e = { column := -1, isSequence := false } ∨
        e = { column := 0, isSequence := false } ∨
        e = { column := 2, isSequence := false } := by
      simpa [inKey, ScannerState.mk'] using he
    rcases this with rfl | rfl | rfl
    · exact absurd hlo (by decide)
    · exact absurd hlo (by decide)
    · simp
  · exact ⟨fun _ h => absurd h (List.not_mem_nil), [FrameLevel.map 4], FrameLevel.map 2, rfl, rfl,
      fun fr h => by simp at h; subst h; decide⟩

/-- **The escapes are about REACHING the floor, not about the hop.**
    `dedent_cover_of_landing` is this lemma behind `landing_floor_of_arm`, and a
    caller that has the arm and the base derives the top's bound rather than
    punting on it. -/
example {sc s_prep : ScannerState} {c : Char} {sp_scan : SurfPos} {w : Nat}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_col : sp_scan.col ≠ 0) (h_base : SentinelBase sc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_scol : s_prep.col = w) :
    s_prep.currentIndent ≤ (w : Int) := by
  rw [← h_scol]; exact landing_floor_of_arm h_noflow h_larm h_col h_base h_preprocess

/-! ## §3  The payment, composed

Three hops carry the park's cover into the pack the dispatch builds: the
landing's, which pops the widths; the context, which holds the result; and the
dispatch's, which moves it from the landing's state to the park's. -/

/-- The lift.  A content dispatch writes no indent level, so the two states'
    stacks are equal and the cover is carried by that equation alone. -/
example {s_prep s' : ScannerState} {c : Char} {lo : Nat} {ks : List FrameLevel}
    (h_dispatch : scanNextToken_dispatchContent s_prep c = .ok s')
    (h : Covered lo ks s_prep) : Covered lo ks s' :=
  dispatchContent_cover h_dispatch h

/-- **The context's informative side is inhabitable with a REAL cover.**  A
    `∨ True` cannot be interrogated after the fact, so what a guard can check is
    that the paying disjunct is reachable from exactly the data a paying park
    has: the landing's line start, `[63]`'s spaces, a fresh at-position save, a
    stack whose widths include the landing's — and now the cover over them. -/
-- 2026-11-10 (item 473, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sp_start sp_land sp_prep : SurfPos} {k lo : Nat} {ks : List FrameLevel}
    {s_prep : ScannerState}
    (hcol0 : sp_land.col = 0) (h_ind : SIndent k sp_land sp_prep)
    (h_fr : ResumeFrames (SLYamlStream sp_start) ks sp_land) (hmem : FrameLevel.map k ∈ ks)
    (h_mono : Mono s_prep) (h_top : s_prep.currentIndent ≤ (k : Int))
    (h_fl : Floor lo k ks) (h_cv : Covered lo ks s_prep)
    (h_poss : s_prep.simpleKey.possible = true)
    (h_pos : s_prep.simpleKey.pos = s_prep.currentPos) 
    (h_alt : PackAlt s_prep) :
    ResumeKeyCtx s_prep sp_start sp_prep :=
  match h_fr.resumeAt hmem with
  | ⟨ks', h_w, cont⟩ =>
      -- Item 374: the framed lane is the context's first disjunct.
      Or.inl (Or.inl ⟨⟨k, ks', sp_land, hcol0, h_ind, h_w.le,
        Or.inl (dedent_cover_of_floor h_mono h_top h_fl h_cv hmem h_w),
        cont, Or.inr h_alt,
        -- Item 168: the sequence face is the third lane and punts here.
        Or.inr trivial⟩, h_poss, h_pos⟩)

/-! ## §4  The lane, walked against the scanner

The relay that pays is the mapping-value park's dedent: the awaited value never
arrived, the entry closes on `[72]`'s empty node, and the landed key parks off
the closed prefix with the landing's `s-indent(j)` as its context.  What the
payment needs from the scanner is the landing's own floor, and what the
DERIVATION needs besides is the park to be off a line start — which is item
147's residue, and the one thing the corpus below discriminates on. -/

private def landingFactsR (s : ScannerState) : Nat × Nat × Nat :=
  match scanNextToken_preprocess s with
  | .ok (some (s', _)) =>
      if s'.indents.size < s.indents.size then
        (1, if s'.currentIndent ≤ (s'.col : Int) then 1 else 0,
            if s.col ≠ 0 then 1 else 0)
      else (0, 0, 0)
  | _ => (0, 0, 0)

/-- States seen; pops; pops with the landing's own floor; pops off a park that
    is not at a line start. -/
private def walkR (s : ScannerState) : Nat → Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, pops, floored, offStart) =>
    let (p, f, o) := landingFactsR s
    let acc := (seen + 1, pops + p, floored + f, offStart + o)
    match scanNextToken s with
    | .ok (some s') => walkR s' fuel acc
    | _ => acc

private def censusR (inputs : List String) : Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkR (ScannerState.mk' i) 200 acc) (0, 0, 0, 0)

-- Item 99's own dedent, three of its deeper twins, and two whose park is a
-- BLOCK SCALAR — which ends past a break, so the park sits at a line start.
-- **68** states, **7** pops, all **7** with the landing's own floor, and **5**
-- of the 7 off a line start.  The two that are not are where the derivation
-- punts, and the split is the point: the scanner establishes the floor at all
-- seven, so item 147's escape is about what the PROOF can reach and not about
-- what the landing does.
#guard censusR
  ["k:\n  :\nb: 2\n",
   "k:\n  a:\nb: 2\n",
   "k:\n  a:\n    b:\nc: 2\n",
   "a:\n  b:\n    c: 1\n  d: 2\n",
   "k:\n  a:\n    b:\n  c: 2\n",
   "a:\n  b:\n    c: |\n      x\n  d: 2\n",
   "a:\n  b:\n    c: >\n      x\nd: 2\n"] == (68, 7, 7, 5)

-- Item 99's own input, read alone: one pop, floored, off a line start.
#guard walkR (ScannerState.mk' "k:\n  :\nb: 2\n") 200 (0, 0, 0, 0) == (7, 1, 1, 1)

-- …and the block-scalar park, which is the same pop with the same floor and no
-- derivation to reach it.
#guard walkR (ScannerState.mk' "a:\n  b:\n    c: |\n      x\n  d: 2\n") 200 (0, 0, 0, 0)
  == (11, 1, 1, 0)

/-! ## §5  What still does not pay

Three sites hand the new slot its punt, and each names a different missing
thing rather than a different input.

* **The sequence park.**  `accum_content_on_pendingBlock_indented` relays
  `pendingBlock.h_closeF`, which carries the widths alone, and the relay has
  neither of the stack's two readings to pay a cover with.  Both the
  constructor field and the relay's `Mono`/`SentinelBase` thread are what a
  payment costs there.
* ~~**The skeleton's two parks.**  `pendingContent.h_framesS` / `.h_framesV` and
  `pendingBlockContent.h_closeF` are the faces `h_defer_split` passes, and none
  of the three has a cover conjunct.~~  **Item 152 paid the first two**, and
  the skeleton now states the landing's payment once in its break-crossed arm;
  `pendingBlockContent.h_closeF` still punts, and so does the column-0 arm.
  See `ContentParkCoverSpent`.
* **The park at a line start**, item 147's residue, measured above.

The context accepts the punt on either lane, which is what lets those three
sites keep compiling while the slot exists. -/

example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_scan sp_mid sp_prep : SurfPos} {ks : List FrameLevel}
    (hcol_mid : sp_mid.col = 0)
    (h_ws : GStar SSWhite sp_mid sp_prep)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (fS : ∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m) 
    (h_alt : PackAlt sc)
    -- Item 374: the sentinel base, for the sequence-top face the declined resume now carries.
    (h_base : SentinelBase sc) :
    ResumeKeyCtx s_prep sp_start sp_prep :=
  resumectx_of_landing (h_base := h_base) hcol_mid h_ws h_ssl h_preprocess hcorr_prep
    (Or.inl ⟨ks, Or.inr trivial, fS⟩) (Or.inr h_alt)
    (fun _ _ _ _ _ _ _ => Or.inr trivial)
    -- Item 168: the sequence face punts; this guard is about the COVER.
    (Or.inr trivial)

/-! ## §6  The price

One new declaration, `dedent_cover_of_floor`, which item 149's lemma now calls
as well — so the hop is authored once and the escapes stay where they belong.
`ResumeKeyCtx` gains two conjuncts, `resumectx_of_landing` two arguments and a
payer, `content_dispatch_routed` one lift and two spends, and the seven relays
that build a resuming context pass the payer they can.

What is left of the cover's own work after this item is the three faces §5
names: `pendingBlock.h_closeF`, and `pendingContent`'s two.  All three are
CONSTRUCTOR fields, which is why none of them is a line in this item — each
costs its own producers, and the sequence park costs its relay a `Mono` and a
`SentinelBase` besides.

**Item 152 took `pendingContent`'s two**, at the cost that sentence predicted
and no more: an `Or.imp` at each of the five producers that already held a
cover.  It also found a field that list did not name — `pendingProps`'s own two
frames faces, which fund five further `pendingContent` producers and are one
level further up the same chain.

**Item 153 took those**, and at the same price: three mapping producers hand
over a cover they already hold, two run extensions step one they already carry,
and the props arm's landing — the one site where the payer was never the
obstacle — spends it.  What the list has left is the SEQUENCE chain:
`pendingProps.h_closeFE`, `pendingBlockContent.h_closeF` and
`pendingBlock.h_closeF`, three fields on one lane. -/

end L4YAML.Tests.Guards.ResumeCtxCoverSpent

end Blanket
