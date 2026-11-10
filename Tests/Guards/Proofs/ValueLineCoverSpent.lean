module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The value-line stack carries its cover (DOCS item 150)

Items 147–149 gave the STREAM lane a cover and taught the dedent landing to
spend it.  The value-line lane — the frames an open `[186]` explicit key leaves
standing, bottomed at the `?`'s own unpaid value line rather than at the
finished stream — carried none, on either face.  This item gives it one, and
the dedent's value-line landing pays it with item 149's lemma verbatim.

**The one thing that does not mirror is the floor.**  The stream faces bottom
at the stream and carry `Floor lo n ks`; these bottom at the `?`, and the `?`'s
own level is deliberately NOT one of their frames — resuming there is the
entry's unpaid value line, not a sibling.  So a cover over these frames cannot
stand at the `?`'s floor: at `ks = []` it would have to name a level that is on
the stack.  One column above, it is the EMPTY cover, and that is a statement
about the stack rather than a vacuity — the `?`'s push put the top at `k`, so
nothing stands at or right of `k + 1`.  Hence `Floor lo (n + 1) ks` on the park
and premise faces, and `IndentStackCover.covered_nil_of_top_le` as the seed.

§1 is the floor's index, and why `n` is payable by nobody.  §2 is the two hops.
§3 is the payment composed and the pack field it lands in.  §4 walks the dedent
families the value lane is live on.  §5 is the membership split, which item 149
named as the next punt and which is not one.  §6 is the price. -/

namespace L4YAML.Tests.Guards.ValueLineCoverSpent

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.IndentStackBase

/-! ## §1  The floor's index

A `?` at column 0 pushes a mapping level there, and the value-line frames below
it are EMPTY.  A cover over that empty list is false at floor 0 and true at
floor 1 — so the index the `Floor` conjunct is stated at decides whether the
seed exists at all. -/

private def qPushed : ScannerState :=
  { ScannerState.mk' "" with
    indents := #[{ column := -1, isSequence := false },
                 { column := 0, isSequence := false }] }

example : qPushed.currentIndent = 0 := by
  show (match qPushed.indents.back? with | some e => e.column | none => -1) = 0
  rfl

/-- At the `?`'s own floor the empty cover is FALSE: the level it just pushed is
    an open mapping level at column 0, and the frames do not name it. -/
example : ¬ Covered 0 [] qPushed := by
  intro h
  have hm : ({ column := 0, isSequence := false } : IndentEntry) ∈ qPushed.indents := by
    simp [qPushed, ScannerState.mk']
  exact absurd (h _ hm rfl (by decide)) (by simp)

/-- One column above it is TRUE, and it is not vacuous — it says the push left
    nothing at or right of 1. -/
example : Covered 1 [] qPushed := by
  intro e he _ hlo
  have : e = { column := -1, isSequence := false } ∨
      e = { column := 0, isSequence := false } := by
    simpa [qPushed, ScannerState.mk'] using he
  rcases this with rfl | rfl <;> exact absurd hlo (by decide)

/-- And the floor conjunct itself only closes at `n + 1`: `Floor lo n []` at the
    `?`'s own index would demand `1 ≤ 0`. -/
example : Floor 1 (0 + 1) ([] : List FrameLevel) :=
  ⟨Nat.le_refl _, fun _ h => absurd h (List.not_mem_nil)⟩

example : ¬ Floor 1 0 ([] : List FrameLevel) := fun h => absurd h.1 (by omega)

/-- The seed at its own type.  `Mono` is load-bearing here for the same reason
    it is in `Covered.pop_to`: the push bounds the TOP. -/
example {s : ScannerState} {c : Nat} (h_mono : Mono s)
    (h_top : s.currentIndent ≤ (c : Int)) : Covered (c + 1) [] s :=
  covered_nil_of_top_le h_mono h_top

/-- Without `Mono` it is false — the same `[-1, 5, 1]` stack item 149 refutes
    `Covered.pop_to` on, whose top is 1 and whose entry at 5 is unnamed. -/
private def unsorted : ScannerState :=
  { ScannerState.mk' "" with
    indents := #[{ column := -1, isSequence := false },
                 { column := 5, isSequence := false },
                 { column := 1, isSequence := false }] }

example : ¬ (∀ (c : Nat) (s : ScannerState),
    s.currentIndent ≤ (c : Int) → Covered (c + 1) [] s) := by
  intro h
  have htop : unsorted.currentIndent ≤ ((1 : Nat) : Int) := by
    show (match unsorted.indents.back? with | some e => e.column | none => -1) ≤ 1
    decide
  have hm : ({ column := 5, isSequence := false } : IndentEntry) ∈ unsorted.indents := by
    simp [unsorted, ScannerState.mk']
  exact absurd (h 1 unsorted htop _ hm rfl (by decide)) (by simp)

/-! ## §2  The two hops

The chain's hop climbs the index by one and leaves the floor where it is; the
dedent's hop is item 149's, unchanged — `dedent_cover_of_landing` reads
`Floor`'s WIDTHS half and never its index, which is why the lane's higher index
rides through it untouched. -/

/-- The chain: a key at `k` inside the `?` conses its own width, and the park it
    opens carries the index one above itself. -/
example {lo k : Nat} {ks : List FrameLevel} {s s' : ScannerState}
    (hb : Floor lo k (FrameLevel.map k :: ks)) (hc : Covered lo (FrameLevel.map k :: ks) s)
    (h_step : Covered lo (FrameLevel.map k :: ks) s → Covered lo (FrameLevel.map k :: ks) s') :
    Floor lo (k + 1) (FrameLevel.map k :: ks) ∧ Covered lo (FrameLevel.map k :: ks) s' :=
  ⟨hb.mono_index (Nat.le_succ k), h_step hc⟩

/-- The nested branch: a landing strictly deeper than the park conses its width,
    and `n < w` carries the higher index across. -/
example {lo n w : Nat} {ks : List FrameLevel} (hb : Floor lo (n + 1) ks) (hlt : n < w) :
    Floor lo w (FrameLevel.map w :: ks) :=
  (hb.mono_index hlt).cons (Nat.le_trans hb.1 hlt)

/-- The dedent branch: item 149's hop, at the value lane's index. -/
example {lo n w : Nat} {ks ks' : List FrameLevel}
    (h : Floor lo (n + 1) ks) (hmem : FrameLevel.map w ∈ ks) (hsub : ∀ fr ∈ ks', fr ∈ ks) :
    Floor lo w (FrameLevel.map w :: ks') :=
  h.pop_to hmem hsub

/-! ## §3  The payment, composed

The value lane's landing calls `dedent_cover_of_landing` — item 149's lemma, at
`n + 1` — and the result lands in the pack field item 108 opened and item 99
had always punted. -/

example {sc s_prep s' : ScannerState} {c : Char} {sp_scan : SurfPos}
    {n w : Nat} {ksV : List FrameLevel}
    (h_cov : (Mono sc ∧ SentinelBase sc) ∨ True)
    (h_covV : (∃ lo : Nat, Floor lo (n + 1) ksV ∧ Covered lo ksV sc) ∨ True)
    (hmemV : FrameLevel.map w ∈ ksV)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (h_scol : s_prep.col = w)
    (h_pre : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_ind_eq : s'.indents = s_prep.indents)
    (h_noflow : s_prep.inFlow = false)
    (h_step : ∀ (lo : Nat) (ks : List FrameLevel), Covered lo ks sc → Covered lo ks s')
    {ksV' : List FrameLevel} (h_wV : ResumeWidths ksV ksV' w) :
    (∃ lo : Nat, Floor lo w (FrameLevel.map w :: ksV') ∧ Covered lo (FrameLevel.map w :: ksV') s') ∨ True :=
  dedent_cover_of_landing h_cov h_covV hmemV h_larm h_scol h_pre h_ind_eq
    h_noflow h_step ksV' h_wV

/-- The field it lands in — the pack's value-line resume twin, cover included.
    Beside it, the stream twin item 148 gave one: two lists, two covers, and
    neither readable as the other. -/
-- 2026-11-10 (item 471, option (A)): the level constructors' bound and the park faces read `≤` (the root frame
-- stands under a column-0 opener's own level), `ResumeWidths` names the survivors positionally and `ResumeWidths.lt`
-- is `ResumeWidths.le`; the rows below restate the faces they mirror — a shape move, no obligation changed.
example {sc : ScannerState} {sp_start sp_scan : SurfPos}
    (h : ImplicitKeyPack sc sp_start sp_scan) :
    ∃ (k : Nat) (sp_key : SurfPos),
      ((∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width ≤ k) ∧
        ((∃ lo : Nat, Floor lo k (FrameLevel.map k :: ks) ∧ Covered lo (FrameLevel.map k :: ks) sc) ∨ True) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_key sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        KeyFrames (ExplValueLine sp_start nv) ks sp_e) ∨ PackAlt sc) := by
  obtain ⟨k, sp_key, _, _, _, _, _, _, _, h_resFV, _⟩ := h
  exact ⟨k, sp_key, h_resFV⟩

/-- …and the props-headed twin carries the same field. -/
example {sc : ScannerState} {sp_start sp_p sp_scan : SurfPos}
    (h : PropsKeyPack sc sp_start sp_p sp_scan) :
    ∃ k : Nat,
      ((∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width ≤ k) ∧
        ((∃ lo : Nat, Floor lo k (FrameLevel.map k :: ks) ∧ Covered lo (FrameLevel.map k :: ks) sc) ∨ True) ∧
        ∀ sp_v : SurfPos, SBlockMapEntry k sp_p sp_v →
        ∀ sp_e : SurfPos, SCompactMapTail k sp_v sp_e →
        KeyFrames (ExplValueLine sp_start nv) ks sp_e) ∨ PackAlt sc) := by
  obtain ⟨⟨k, _, _, _, _, h_resFV⟩, _⟩ := h
  exact ⟨k, h_resFV⟩

/-! ## §4  The lane, against the scanner

The value-line cover reaches a landing that stays INSIDE the outermost open
level — below that the `?` itself has been closed and the stream lane is the
one that answers.  The walk counts pops, pops with the landing's own floor, and
pops whose landing column is strictly right of the outermost non-sentinel
level, which is the reach.  Counting all three is what keeps the check from
passing vacuously on a corpus with no dedent in it. -/

/-- The outermost non-sentinel level, or the sentinel where there is none. -/
private def outerCol (s : ScannerState) : Int :=
  match s.indents[1]? with
  | some e => e.column
  | none => -1

private def landingFactsV (s : ScannerState) : Nat × Nat × Nat :=
  match scanNextToken_preprocess s with
  | .ok (some (s', _)) =>
      if s'.indents.size < s.indents.size then
        (1, if s'.currentIndent ≤ (s'.col : Int) then 1 else 0,
            if outerCol s < (s'.col : Int) then 1 else 0)
      else (0, 0, 0)
  | _ => (0, 0, 0)

/-- States seen; pops; pops with the landing's own floor; pops that stayed
    inside the outermost open level. -/
private def walkV (s : ScannerState) : Nat → Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, pops, floored, inside) =>
    let (p, f, i) := landingFactsV s
    let acc := (seen + 1, pops + p, floored + f, inside + i)
    match scanNextToken s with
    | .ok (some s') => walkV s' fuel acc
    | _ => acc

private def censusV (inputs : List String) : Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkV (ScannerState.mk' i) 200 acc) (0, 0, 0, 0)

-- Item 108's own examples, plus the explicit-key dedents items 99/115 name:
-- a sibling inside a `?` key, a sibling two levels in, a props-headed one, and
-- the `?` whose key is a sequence.  **60** states, **8** pops, all **8** with
-- the landing's own floor — and only **3** of the 8 inside the outermost level.
-- The other five are the `:` line closing the `?` itself, which is the STREAM
-- lane's landing and not this one's; reporting the split rather than the total
-- is what keeps the number from reading as five payments it is not.
#guard censusV
  ["?\n  a:\n    b:\n  c: 2\n: - w\n",
   "?\n  a: b\n  c: d\n: - w\n",
   "?\n  a:\n    b:\n      c: 1\n  d: 2\n: - w\n",
   "?\n  a:\n    b: 1\n  &p c: 2\n: - w\n",
   "?\n  - x\n  - y\n: v\n"] == (60, 8, 8, 3)

-- The item's own example, read alone: two pops, one of them the sibling `c`
-- landing back on `a`'s level with the `?` still open, and one the `:` line.
#guard walkV (ScannerState.mk' "?\n  a:\n    b:\n  c: 2\n: - w\n") 200 (0, 0, 0, 0)
  == (12, 2, 2, 1)

-- …and its three-level twin, where the sibling pops PAST a frame.
#guard walkV (ScannerState.mk' "?\n  a:\n    b:\n      c: 1\n  d: 2\n: - w\n") 200
  (0, 0, 0, 0) == (15, 2, 2, 1)

-- A `?` whose key holds no nested mapping has no landing this lane answers at
-- all — its single pop is the `:` line's.  Guarding it is what says the
-- distinction above is a real one and not an artifact of the corpus.
#guard walkV (ScannerState.mk' "?\n  a: b\n  c: d\n: - w\n") 200 (0, 0, 0, 0)
  == (11, 1, 1, 0)

/-! ## §5  The membership split is not a punt the cover can remove

Item 149 named it as the next one: `entryKeyPack_of_dispatch`'s dedent runs
`by_cases hmem : FrameLevel.map w ∈ ks` and returns `KeyPackPunt.dedent` when the landing names
no frame, and `preprocess_landing_mem_or_seq` derives that membership from the
cover the branch now holds.  Deriving it would change nothing, and the reason is
one line of Lean.

`KeyPackPunt.dedent` takes no argument, so the punt disjunct is inhabited for
EVERY state.  The branch therefore already returns the pack at exactly the
inputs where `FrameLevel.map w ∈ ks` holds, and a derivation of `FrameLevel.map w ∈ ks` from other facts
cannot add an input to that set — it can only re-prove what the split already
decided.  What would move the domain is the opposite change: a PAYLOAD on the
constructor, so that a consumer holding the cover can refute the punt instead of
the producer deriving around it.  That is the shape the `tab` and
`implicitValue` reasons already have, and the shape `noFrame` had before it was
deleted.

**Item 297 deletes `dedent`.**  The `FrameLevel.map w ∉ ks` exit keys a fresh document at the
landing (items 296/297, row 19's over-approximation), so the constructor has no
production.  The exhibit below stands on `noKeyContext`, the nullary reason
that remains. -/

example (s : ScannerState) : KeyPackPunt s := KeyPackPunt.noKeyContext

/-- The derivation also stops short of total, and of a requirement item 149 did
    not name: `preprocess_landing_mem_or_seq` wants the landing at or right of
    the cover's floor, and a dedent lands strictly LEFT of the park's index —
    `Floor`'s index half says nothing there. -/
example : ¬ (∀ (lo n w : Nat) (ks : List FrameLevel), Floor lo n ks → w < n → lo ≤ w) := by
  intro h
  exact absurd (h 2 3 1 [] ⟨by omega, fun _ hx => absurd hx (List.not_mem_nil)⟩ (by omega))
    (by omega)

/-- The lemma that WOULD settle it, at its type — and its three premises, of
    which the park's `SentinelBase` is the only one the branch holds today. -/
example {sc s_prep : ScannerState} {c : Char} {lo : Nat} {ks : List FrameLevel}
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_pop : s_prep.indents ≠ sc.indents)
    (h_base : SentinelBase sc)
    (h_floor : lo ≤ s_prep.col)
    (h_cov : Covered lo ks sc) :
    FrameLevel.map s_prep.col ∈ ks ∨
      ∃ e, s_prep.indents.back? = some e ∧ e.isSequence = true ∧
        e.column = (s_prep.col : Int) :=
  preprocess_landing_mem_or_seq hok h_pop h_base h_floor h_cov

/-! ## §6  The price, and what still does not pay

ONE new lemma — `IndentStackCover.covered_nil_of_top_le`, the seed — and one
conclusion widened: `indicator_cover_at_col` now reports the top's two readings
instead of one, which is where the `?` producer's payment comes from.  Sixteen
field shapes gain the cover conjunct, ten of them at `n + 1` (the park, premise
and relay faces) and six at the pack's own index.  `question_open_map` gains a
premise, and the four faces its producer pays go from `ks = []` with no stack to
`ks = []` with the stack that makes it true.

What still does not pay: the col-0 park (item 147's residue, at three lanes
now), the sequence parks, whose two faces carry no cover on either side, and
~~`ResumeKeyCtx`, which has no cover slot on either lane~~ — so a landing that
resumes through it projects both covers away, which is the one projection of
each that item 149 kept and this item matches.

**Item 151 gave `ResumeKeyCtx` a slot on each lane** (`ResumeCtxCoverSpent`) and
**item 152 paid it from the completed content park** (`ContentParkCoverSpent`),
so of the three named above only the col-0 park and the sequence parks stand. -/

end L4YAML.Tests.Guards.ValueLineCoverSpent

end Blanket
