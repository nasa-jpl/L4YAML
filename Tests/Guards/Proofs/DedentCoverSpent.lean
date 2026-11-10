module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The dedent landing spends the cover (DOCS item 149)

Item 148 carried a cover from a root down an unbounded chain of nested implicit
keys and left ONE branch punting: `entryKeyPack_of_dispatch`'s dedent, where the
landing pops to a level below the park's own.  The reason it named was a
mismatch of lists — the park's cover is over the whole of `ks`, the pack the
landing opens carries `FrameLevel.map w :: ks'`, and `ks'` drops every width above `w`.

The mismatch is real and it is not a list fact.  What reads the one list as the
other is the landing's own FLOOR: preprocessing's unwind stopped at `w`, so the
stack it hands the dispatch has nothing above `w` left to name.  Three things
had to be true at once; item 148 named all three, and one of them one half
short:

* `ResumeFrames.resumeAt` had to say WHICH widths survive, not just that they
  are below `w`.  The bound is satisfied by the empty list, and so is the
  SUBLIST reading item 148 named — that one is half the answer (it is what the
  floor spends), and the half the cover spends is COMPLETENESS: nothing strictly
  below the landing was dropped (§1).
* `Mono` had to reach the content lane, because the floor bounds the TOP and
  the cover asks about every entry (§2).
* The floor itself had to be measured, which is `landing_floor_of_arm` off the
  landed arm the pack lemma already destructures (§3).

Two of the three cost no new scanner reading at all: `resumeAt`'s own recursion
already visits the strict decrease it needed, and the floor is item 147's lemma
applied to an arm the branch already had in hand.  The third is a premise, and
`Mono` rides the accumulation down beside item 146's base.

§1 is what `resumeAt` reports.  §2 is the two hops and what each needs.  §3 is
the payment composed, with the punts removed.  §4 checks the floor against the
scanner.  §5 is the price and what still does not pay. -/

namespace L4YAML.Tests.Guards.DedentCoverSpent

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.IndentStackBase

/-! ## §1  What `resumeAt` reports

A landing at `j` closes the levels above it and keeps the rest.  Which rest is
the question the surface never had to ask and the scanner cannot do without. -/

/-- The widths, named. -/
example (ks ks' : List FrameLevel) (j : Nat) :
    ResumeWidths ks ks' j ↔
      ((∀ fr ∈ ks', fr.width ≤ j) ∧
        ∃ (pre : List FrameLevel) (e : FrameLevel), ks = pre ++ e :: ks' ∧ e.width = j ∧
          ∀ fr ∈ pre, j ≤ fr.width) := Iff.rfl

/-- A landing at 2 on a three-level stack keeps exactly the level at 0. -/
example : ResumeWidths [FrameLevel.map 4, FrameLevel.map 2, FrameLevel.map 0] [FrameLevel.map 0] 2 :=
  ⟨fun fr h => by simp at h; subst h; decide,
   [FrameLevel.map 4], FrameLevel.map 2, rfl, rfl, fun fr h => by simp at h; subst h; decide⟩

/-- **The bound alone cannot say that**: `∀ fr ∈ ks', fr.width < j` is satisfied by
    the EMPTY list, so a caller holding it knows nothing about which frames
    survived. -/
example : ∀ fr ∈ ([] : List FrameLevel), fr.width < 2 := by simp

/-- **Nor can a SUBLIST** — the reading item 148 named, which is one of the two
    halves and not the one that was missing.  A sublist IS what the floor spends
    (`Floor.pop_to`: every surviving width was a frame the park had already
    bounded); the half the COVER spends is completeness, and a sublist cannot
    supply it, since `[]` is a sublist of every list. -/
example : ([] : List FrameLevel).Sublist [FrameLevel.map 4, FrameLevel.map 2, FrameLevel.map 0] := by simp

/-- The named form refuses both: level 0 is below the landing, so it is
    still a frame and the empty list is not what the landing leaves. -/
example : ¬ ResumeWidths [FrameLevel.map 4, FrameLevel.map 2, FrameLevel.map 0] [] 2 := fun h =>
  absurd (h.keep (FrameLevel.map 0) (by simp) (by decide)) (List.not_mem_nil)

/-- The two projections the payment spends: what survived was a frame
    already… -/
example {ks ks' : List FrameLevel} {j : Nat} (h : ResumeWidths ks ks' j) :
    ∀ fr ∈ ks', fr ∈ ks := h.sub

/-- …and nothing below the landing was dropped. -/
example {ks ks' : List FrameLevel} {j : Nat} (h : ResumeWidths ks ks' j) :
    ∀ fr ∈ ks, fr.width < j → fr ∈ ks' := h.keep

/-! ## §2  The two hops

The frames' bound travels for free; the stack's cover does not. -/

/-- **The floor does not move.**  `w` is one of the frames the park already
    bounded, and so is every width the landing keeps — so the bound the park
    carried reaches the whole of the new list without being re-measured.

    Note which half of `Floor` does the work: the WIDTHS half, `∀ k' ∈ ks,
    lo ≤ k'`, which is the one item 148 added.  The index half `lo ≤ n` is
    carried across this hop and never read — it is the NESTED branch that
    spends it (`Floor.mono_index`), and the two branches of the key dispatch
    are what make both halves live. -/
example {lo n w : Nat} {ks ks' : List FrameLevel}
    (h : Floor lo n ks) (hmem : FrameLevel.map w ∈ ks) (hsub : ∀ fr ∈ ks', fr ∈ ks) :
    Floor lo w (FrameLevel.map w :: ks') := h.pop_to hmem hsub

/-- **The cover is re-listed, and that needs the machine.**  The landing's floor
    bounds the TOP; monotonicity turns that into a bound on every entry; and the
    entries at or left of `w` are the frames the landing kept. -/
example {lo w : Nat} {ks ks' : List FrameLevel} {s : ScannerState}
    (h_mono : Mono s) (h_top : s.currentIndent ≤ (w : Int))
    (h_keep : ∀ fr ∈ ks, fr.width < w → fr ∈ ks')
    (h : Covered lo ks s) : Covered lo (FrameLevel.map w :: ks') s :=
  h.pop_to h_mono h_top h_keep

/-- A stack that is NOT monotone, for the refutation below: the top is at 1
    while an entry at 5 stands under it. -/
private def unsorted : ScannerState :=
  { ScannerState.mk' "" with
    indents := #[{ column := -1, isSequence := false },
                 { column := 5, isSequence := false },
                 { column := 1, isSequence := false }] }

example : unsorted.currentIndent = 1 := by
  simp [unsorted, ScannerState.currentIndent]

example : Covered 0 [FrameLevel.map 5, FrameLevel.map 1] unsorted := by
  intro e he _ hnn
  simp [unsorted] at he
  rcases he with rfl | rfl | rfl <;> simp_all

example : ¬ Covered 0 [FrameLevel.map 1] unsorted := by
  intro h
  have := h { column := 5, isSequence := false } (by simp [unsorted]) rfl (by simp)
  simp at this

/-- **`Mono` is load-bearing, not decoration.**  Drop it and the same three
    remaining hypotheses hold of `unsorted` at `w = 1` — the top is at 1, and
    no frame of `[5, 1]` is strictly below 1 — while the conclusion is false. -/
example : ¬ (∀ (lo w : Nat) (ks ks' : List FrameLevel) (s : ScannerState),
    s.currentIndent ≤ (w : Int) → (∀ fr ∈ ks, fr.width < w → fr ∈ ks') →
    Covered lo ks s → Covered lo (FrameLevel.map w :: ks') s) := by
  intro h
  refine absurd (h 0 1 [FrameLevel.map 5, FrameLevel.map 1] [] unsorted
    (by simp [unsorted, ScannerState.currentIndent])
    (by intro k' hk' hlt; simp at hk'; rcases hk' with rfl | rfl <;> (dsimp only at hlt; omega))
    (by
      intro e he _ hnn
      simp [unsorted] at he
      rcases he with rfl | rfl | rfl <;> simp_all)) ?_
  intro hc
  have := hc { column := 5, isSequence := false } (by simp [unsorted]) rfl (by simp)
  simp at this

/-! ## §3  The payment, composed

This is `dedent_cover_of_landing`'s body with all three of its escapes removed —
the caller's stack readings, the park's carried cover, and the line-start park —
so what it produces is the LEFT disjunct rather than the field's `∨ True`. -/

example {sc s_prep s' : ScannerState} {c : Char} {sp_scan : SurfPos}
    {n w lo : Nat} {ks ks' : List FrameLevel}
    (h_mono : Mono sc) (h_base : SentinelBase sc)
    (h_fl : Floor lo n ks) (h_cv : Covered lo ks sc) (hmem : FrameLevel.map w ∈ ks)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (hc0 : sp_scan.col ≠ 0) (h_scol : s_prep.col = w)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_ind_eq : s'.indents = s_prep.indents)
    (h_noflow : s_prep.inFlow = false)
    (h_step : ∀ (lo : Nat) (ks : List FrameLevel), Covered lo ks sc → Covered lo ks s')
    (h_w : ResumeWidths ks ks' w) :
    Floor lo w (FrameLevel.map w :: ks') ∧ Covered lo (FrameLevel.map w :: ks') s' :=
  ⟨h_fl.pop_to hmem h_w.sub,
   (h_step lo ks h_cv).pop_to
     ((preprocess_mono h_pre h_mono).of_indents_eq h_ind_eq)
     (by
       rw [L4YAML.Proofs.PreprocessIndentStable.currentIndent_of_indents_eq h_ind_eq, ← h_scol]
       exact landing_floor_of_arm h_noflow h_larm hc0 h_base h_pre)
     h_w.keep⟩

/-- The lemma both pack lemmas actually call, at its type.  The escapes are
    `h_cov` (a caller that cannot measure its stack), `h_dcov` (a park whose
    frames carry no cover), and the park's own column — and nothing else: every
    other premise is discharged from what the accumulation already threads. -/
example {sc s_prep s' : ScannerState} {c : Char} {sp_scan : SurfPos}
    {n w : Nat} {ks : List FrameLevel}
    (h_cov : (Mono sc ∧ SentinelBase sc) ∨ True)
    (h_dcov : (∃ lo : Nat, Floor lo n ks ∧ Covered lo ks sc) ∨ True)
    (hmem : FrameLevel.map w ∈ ks)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_scol : s_prep.col = w)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_ind_eq : s'.indents = s_prep.indents)
    (h_noflow : s_prep.inFlow = false)
    (h_step : ∀ (lo : Nat) (ks : List FrameLevel), Covered lo ks sc → Covered lo ks s')
    {ks' : List FrameLevel} (h_w : ResumeWidths ks ks' w) :
    (∃ lo : Nat, Floor lo w (FrameLevel.map w :: ks') ∧ Covered lo (FrameLevel.map w :: ks') s') ∨ True :=
  dedent_cover_of_landing h_cov h_dcov hmem h_larm h_scol h_pre h_ind_eq
    h_noflow h_step ks' h_w

/-- And the field it lands in: the pack the dedent branch returns carries the
    cover over the widths the landing resumed on. -/
-- 2026-11-10 (item 473, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sc : ScannerState} {sp_start sp_scan : SurfPos}
    (h : ImplicitKeyPack sc sp_start sp_scan) :
    ∃ (k : Nat) (sp_key : SurfPos),
      ((∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width ≤ k) ∧
        ((∃ lo : Nat, Floor lo k (FrameLevel.map k :: ks) ∧ Covered lo (FrameLevel.map k :: ks) sc) ∨ True) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        ResumeFrames (SLYamlStream sp_start) ks sp_e) ∨ True) := by
  obtain ⟨k, sp_key, _, _, _, _, _, _, h_resF, _⟩ := h
  exact ⟨k, sp_key, h_resF⟩

/-! ## §4  The floor, against the scanner

`landing_floor_of_arm` says a landing that crossed a break has its floor — the
top at or left of the column it unwound to — unless the stack popped all the way
to the sentinel.  The walk below checks that on every step whose preprocessing
actually POPPED, and counts those steps so a future change cannot make the check
vacuous by never reaching one.  It also counts the parks the payment declines:
a park AT a line start, whose walk crossed nothing and so armed no unwind. -/

private def landingFacts (s : ScannerState) : Nat × Nat × Nat × Nat :=
  match scanNextToken_preprocess s with
  | .ok (some (s', _)) =>
      if s'.indents.size < s.indents.size then
        let floored := decide (s'.currentIndent ≤ (s'.col : Int))
        let sentinel := decide (s'.indents.size ≤ 1)
        (1, if floored then 1 else 0,
            if s.col == 0 then 1 else 0,
            if floored || sentinel then 0 else 1)
      else (0, 0, 0, 0)
  | _ => (0, 0, 0, 0)

/-- States seen; steps whose preprocessing popped the stack; those with the
    landing's own floor; those whose PARK stood at a line start (the payment's
    declined case); and those with neither the floor nor the sentinel — the
    shape `landing_floor_of_arm` says cannot occur off an armed walk. -/
private def walkLandings (s : ScannerState) : Nat → Nat × Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, pops, floored, atcol0, bad) =>
    let (p, f, c0, b) := landingFacts s
    let acc := (seen + 1, pops + p, floored + f, atcol0 + c0, bad + b)
    match scanNextToken s with
    | .ok (some s') => walkLandings s' fuel acc
    | _ => acc

private def census (inputs : List String) : Nat × Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkLandings (ScannerState.mk' i) 200 acc) (0, 0, 0, 0, 0)

-- The same eighteen inputs items 146–148 walk, so the state count is a
-- cross-check as well: 121 states, TWO of them a step whose preprocessing
-- popped the stack, both with the landing's own floor, neither at a line-start
-- park, and none unfloored.
#guard census
  ["a: 1\nb: 2\n", "k:\n  a: 1\n  b: 2\n", "- a\n- b\n", "k:\n  - a\n  - b\n",
   "? \"a\"\n: v\n", "k: [1, 2]\nb: 2\n", "k: |\n  x\nb: 2\n", "k:\n  a: 1\nb: 2\n",
   "k:\n  \"x\"\n  b: 2\n", "k:\n  \"a\"\n  [1, 2]\n", "k:\n  a\n  : v\n",
   "\"x\"\nb: 2\n", "a\n# c\nb: 2\n", "[1, 2]\nb: 2\n",
   "a:\n  b:\n    c: 1\nd: 2\n", "{a: 1, b: [2, 3]}\n", "k: >\n  folded\n",
   "---\na: 1\n...\n---\nb: 2\n"] == (121, 2, 2, 0, 0)

-- TWO pops in eighteen inputs is a thin check, so the dedent families this item
-- pays at are walked on their own: single and double dedents, a dedent to a
-- MIDDLE level, one inside an explicit key, one across a blank line and a
-- comment, and item 99's own `k:⏎  :⏎b: 2`.  **115** states, **13** pops, all
-- **13** with the landing's own floor, **0** at a line-start park and **0**
-- unfloored.
#guard census
  ["a:\n  b: 1\nc: 2\n",
   "a:\n  b:\n    c: 1\nd: 2\n",
   "a:\n  b:\n    c: 1\n  d: 2\ne: 3\n",
   "a:\n  b:\n    c:\n      d: 1\n  e: 2\n",
   "k:\n  :\nb: 2\n",
   "?\n  a: b\n  c: d\n: - w\n",
   "a:\n  - x\n  - y\nb: 2\n",
   "a:\n  b: 1\n\n  # c\nc: 2\n",
   "?\n  a:\n    b:\n  c: 2\n: - w\n",
   "a:\n  b:\n    c: 1\n\nd: 2\ne:\n  f: 3\ng: 4\n"] == (115, 13, 13, 0, 0)

-- And the two simplest, read alone: `a:⏎  b: 1⏎c: 2` pops one level;
-- `a:⏎  b:⏎    c: 1⏎d: 2` pops two at once, which is the landing that reaches
-- PAST a frame — the case `ResumeWidths` exists to name.
#guard walkLandings (ScannerState.mk' "a:\n  b: 1\nc: 2\n") 200 (0, 0, 0, 0, 0)
  == (9, 1, 1, 0, 0)
#guard walkLandings (ScannerState.mk' "a:\n  b:\n    c: 1\nd: 2\n") 200 (0, 0, 0, 0, 0)
  == (11, 1, 1, 0, 0)

/-! ## §5  The price, and what still does not pay

**The price.**  Seven new declarations: `ResumeWidths` with its three
projections and `dedent_cover_of_landing` — the payment, written once for both
pack lemmas — in `StreamAccum`, and `Floor.pop_to` with `Covered.pop_to` in
`IndentStackCover`.  `ResumeFrames.resumeAt`'s conclusion is restated and its
thirteen consumers migrated (ten needed a textual change; the three that already
projected the bound away with `_` did not).  Six declarations gain a premise:
`h_dframes`' cover conjunct and `h_cov` at both pack lemmas, and `Mono` with
`SentinelBase` threading down the content lane beside item 146's base.  At the
twelve pack-lemma call sites the bundle is real at the six `pendingMapValue`
parks and a punt at the other six, and six of the seven places item 147's field
was projected down to its widths now pass it through unchanged.

**What still does not pay.**

* ~~**The membership split.**  The branch still runs `by_cases hmem : FrameLevel.map w ∈ ks` and
  punts when the landing names no frame.  `preprocess_landing_mem_or_seq` derives
  that membership from the cover it now has in hand — but it wants the park's
  `SentinelBase`, `s_prep.indents ≠ sc.indents`, and a refutation of the SEQUENCE
  disjunct, which `IndentStackCover.landing_mem_of_value` settles a step LATER at
  the `:` and the pack cannot.~~  **Item 150: that reading is wrong, and the
  derivation would buy nothing.**  `KeyPackPunt.dedent` takes no argument, so the
  punt disjunct is inhabited at every state and the branch already returns the
  pack at exactly the inputs where `FrameLevel.map w ∈ ks` holds — a derivation of `FrameLevel.map w ∈ ks` can
  only re-prove what the split decided.  What moves the domain is a PAYLOAD on
  the constructor.  There is also a fourth requirement this list did not name:
  `preprocess_landing_mem_or_seq` wants the landing at or right of the cover's
  floor, and a dedent lands strictly left of the park's index.  Both are
  machine-checked in `ValueLineCoverSpent`'s §5.  Item 297 deletes `dedent`:
  the `FrameLevel.map w ∉ ks` exit keys a fresh document at the landing, row 19's
  over-approximation.
* **A park at a line start.**  The walk that reached the landing crossed nothing,
  so preprocessing armed no unwind and there is no floor to measure — item 147's
  own residue, at the indicator lane's payers as well.
* ~~**The value-line stack.**  `h_dframesV` carries no cover at all; the `?` frame's
  levels are a different stack and nothing measures it yet.~~  **Item 150 gives it
  one** — at a floor one column above the park, because the `?`'s own level is
  not one of its frames.
* **Sequence parks.**  `pendingBlock`'s two faces carry no cover on either side,
  so their dedent hop has none to spend — the same stop item 148 recorded. -/

end L4YAML.Tests.Guards.DedentCoverSpent

end Blanket
