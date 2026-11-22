module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The property park carries the cover, at both faces (DOCS item 153)

Item 152 gave `pendingContent`'s two frames fields a cover slot and paid it at
`accum_content_pending`'s shared landing skeleton.  Five of that park's
producers could not fill the slot, and the reason was one level up the same
chain: they ride `pendingProps`'s `h_closeF`/`h_closeFV`, which carried widths
alone.  Item 152 named that residue — a field its own "three constructor fields
and nothing else" census had not, because that census listed the punt sites'
IMMEDIATE inputs.

This item pays it.  The two props fields gain the same existential-index cover
conjunct, the three mapping producers that already hold one hand it over, the
two run EXTENSIONS step it across the property scan, and both consumers spend
it: the five `pendingContent` producers and the props arm's own landing.

**The column-0 escape cannot arise on this lane.**  Item 152's consumer had a
residue — a park AT a line start crossed no break, so `landing_floor_of_arm` has
no arm to read and item 147's escape stands (two of eight landings, measured
there).  A props park has `h_col0 : 0 < sp_scan.col` as an UNCONDITIONAL
constructor field: a `[96]` run is at least one character wide, so the park is
never at a line start and the payment's premise is the park's own datum rather
than something the consumer must derive.  §5 measures that: eight held runs in
the corpus, none of them at a line start.

§1 is the slot and the stagger it absorbs.  §2 is the producer census and the
disjointness that makes the entry-face preference free.  §3 is the step, at the
extension and at the decorated value.  §4 is the payment.  §5 walks the corpus.
§6 is what still does not pay.  §7 is the price. -/

namespace L4YAML.Tests.Guards.PropsParkCoverSpent

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.CouplingBridge

/-! ## §1  One slot, two floors

`pendingMapValue` bounds its two faces at different levels on purpose (item
150's stagger): the transport face runs to the entry's own index and the value
face bottoms one column above the `?`.  Both land in the props park's single
slot, because what that slot states about the index is only that there IS one —
`IndentStackCover.Floor.pop_to` spends the widths half alone. -/

-- The stream face, floored at the entry's own level …
example {sc : ScannerState} {sp_start sp_node : SurfPos} {n lo : Nat} {ks : List FrameLevel}
    (h_fl : Floor lo n (FrameLevel.map n :: ks)) (h_cv : Covered lo (FrameLevel.map n :: ks) sc)
    (closeF : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_m) :
    (∃ ks : List FrameLevel,
      ((∃ lo m : Nat, Floor lo m ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m) ∨ True :=
  Or.inl ⟨FrameLevel.map n :: ks, Or.inl ⟨lo, n, h_fl, h_cv⟩, closeF⟩

-- … and the value face, floored one column above the `?`, in the SAME shape.
example {sc : ScannerState} {sp_start sp_node : SurfPos} {n nv lo : Nat} {ks : List FrameLevel}
    (h_fl : Floor lo (n + 1) ks) (h_cv : Covered lo ks sc)
    (closeFV : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_m) :
    (∃ (nv : Nat) (ks : List FrameLevel),
      ((∃ lo m : Nat, Floor lo m ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_m) ∨ True :=
  Or.inl ⟨nv, ks, Or.inl ⟨lo, n + 1, h_fl, h_cv⟩, closeFV⟩

-- A producer with no cover fills the slot and keeps its frames, which is what
-- the five punting producers do.
example {sc : ScannerState} {sp_start sp_node : SurfPos} {n : Nat} {ks : List FrameLevel}
    (closeF : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m) :
    (∃ ks : List FrameLevel,
      ((∃ lo m : Nat, Floor lo m ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m) ∨ True :=
  Or.inl ⟨ks, Or.inr trivial, closeF⟩

/-! ## §2  The producer census, and why the entry-face preference is free

Ten sites build a `pendingProps`.  Three pay these two fields — the root and
indented mapping-value arms, plus the root's tag twin — and they pay from
`pendingMapValue`'s own covered faces.  Two RELAY them across a run extension.
Five punt: the two landed root runs and the two root `- ` arms hold no frame at
all, and the sequence arm pays the ENTRY face (`h_closeFE`) instead.

That last line is what makes the landing's face selection free.  The props arm
prefers `h_closeFE` where it exists, and `h_closeFE` carries no cover — its one
payer relays `pendingBlock.h_closeF`, which has none.  But **no producer pays
both lanes**: the sequence arm pays the entry face and punts these two, and the
three mapping arms do the reverse.  So the preference never discards a cover
that was there to spend. -/

-- The entry face's own shape, for comparison: a width bound, and no cover slot.
example {sp_start sp_node : SurfPos} {n : Nat} {ks : List FrameLevel}
    (h_lt : ∀ fr ∈ ks, fr.width < n)
    (closeFE : ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp_m sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) :
    (∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < n) ∧
      ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →
      ∀ sp_end : SurfPos, SCompactSeqTail n sp_m sp_end →
      ResumeFrames (SLYamlStream sp_start) ks sp_end) ∨ True :=
  Or.inl ⟨ks, h_lt, closeFE⟩

/-! ## §3  The step

A `[96]` property scan writes no indent level and a content dispatch writes
none either, so a cover carried into the park reaches both of the park's exits
unchanged: the longer run an extension parks, and the completed value's own
park.  Both spends are the same chain — the one items 148/150 already run on
the pack beside them. -/

example {sc s_prep s' : ScannerState} {c : Char} {lo : Nat} {ks : List FrameLevel}
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
      (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep) c = .ok s')
    (h_cv : Covered lo ks sc) : Covered lo ks s' :=
  dispatchContent_cover h_dispatch
    ((preprocess_cover h_preprocess h_cv).of_indents_eq (by split <;> rfl))

/-! ## §4  The payment, and the escape that is not there

The props arm of `accum_content_pending` is the break-crossed landing, and its
park is off a line start by the constructor's own `h_col0`.  So both of
`landing_floor_of_arm`'s inputs are in hand without a case split, and the
payment is `dedent_cover_of_floor` — item 151's factoring — in one line. -/

example {sc s_prep : ScannerState} {c : Char} {sp_scan : SurfPos}
    {w lo m : Nat} {ksw ksw' : List FrameLevel}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    -- the PARK's own field, not a derived fact: a `[96]` run is a character wide
    (h_col0 : 0 < sp_scan.col)
    (h_base : SentinelBase sc) (h_mono : Mono sc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_fl : Floor lo m ksw) (h_cv : Covered lo ksw sc)
    (hmem : FrameLevel.map w ∈ ksw) (h_ww : ResumeWidths ksw ksw' w) (h_scol : s_prep.col = w) :
    ∃ lo : Nat, Floor lo w (FrameLevel.map w :: ksw') ∧ Covered lo (FrameLevel.map w :: ksw') s_prep :=
  dedent_cover_of_floor (preprocess_mono h_preprocess h_mono)
    (by rw [← h_scol]
        exact landing_floor_of_arm h_noflow h_larm (by omega) h_base h_preprocess)
    h_fl (preprocess_cover h_preprocess h_cv) hmem h_ww

-- And the same payment composed into the context the props arm builds.
example {sc s_prep : ScannerState} {c : Char}
    {sp_start sp_scan sp_mid sp_prep : SurfPos} {n lo : Nat} {ks : List FrameLevel}
    (hcol_mid : sp_mid.col = 0)
    (h_ws : GStar SSWhite sp_mid sp_prep)
    (h_ssl : SSLComments sp_scan sp_mid)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (h_fl : Floor lo n ks) (h_cv : Covered lo ks sc)
    (fS : ∀ sp_m : SurfPos, SSLComments sp_scan sp_m →
      ResumeFrames (SLYamlStream sp_start) ks sp_m)
    (h_pay : ∀ (w : Nat) (ksw ksw' : List FrameLevel),
        ((∃ lo m : Nat, Floor lo m ksw ∧ Covered lo ksw sc) ∨ True) →
        FrameLevel.map w ∈ ksw → ResumeWidths ksw ksw' w → s_prep.col = w →
        ((∃ lo : Nat, Floor lo w (FrameLevel.map w :: ksw') ∧
          Covered lo (FrameLevel.map w :: ksw') s_prep) ∨ True)) 
    (h_alt : PackAlt sc)
    -- Item 374: the sentinel base, for the sequence-top face the declined resume now carries.
    (h_base : SentinelBase sc) :
    ResumeKeyCtx s_prep sp_start sp_prep :=
  resumectx_of_landing (h_base := h_base) hcol_mid h_ws h_ssl h_preprocess hcorr_prep
    (Or.inl ⟨ks, Or.inl ⟨lo, n, h_fl, h_cv⟩, fS⟩) (Or.inr h_alt) h_pay
    -- Item 168: the sequence face punts; this guard is about the COVER.
    (Or.inr trivial)

/-! ## §5  The corpus, walked against the scanner

Two things are measured.  A landing is a step whose park is off a line start
and whose walk crossed a break — `landing_floor_of_arm`'s two premises — and
the third component is its conclusion.  A held RUN is a state whose last real
token is a node property: the props park, seen from the scanner.

The split that matters is the last two components.  A landing whose park is a
held run is the `propsEmpty` route through `accum_content_pending`'s props arm,
which spends the payment directly; every other landing is the five-producer
route, where the cover reaches the decorated value's own park and is spent by
item 152's skeleton.  And no held run sits at a line start — the measured form
of `h_col0`, which is why this lane has no column-0 residue. -/

private def heldRunP (s : ScannerState) : Nat :=
  match lastRealToken? s.tokens with
  | some t => if t.val.isNodeProperty then 1 else 0
  | none => 0

private def landingFactsP (s : ScannerState) : Nat × Nat × Nat :=
  match scanNextToken_preprocess s with
  | .ok (some (s', _)) =>
      if s.col ≠ 0 && s'.line != s.line then
        (1, if s'.currentIndent ≤ (s'.col : Int) then 1 else 0, heldRunP s)
      else (0, 0, 0)
  | _ => (0, 0, 0)

/-- States seen; held runs; landings; landings with the walk's own floor;
    landings whose park is a held run; held runs AT a line start. -/
private def walkP (s : ScannerState) : Nat → Nat × Nat × Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, runs, lands, floored, offRun, atStart) =>
    let (l, f, r) := landingFactsP s
    let acc := (seen + 1, runs + heldRunP s, lands + l, floored + f, offRun + r,
                atStart + (if heldRunP s == 1 && s.col == 0 then 1 else 0))
    match scanNextToken s with
    | .ok (some s') => walkP s' fuel acc
    | _ => acc

private def censusP (inputs : List String) : Nat × Nat × Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkP (ScannerState.mk' i) 200 acc) (0, 0, 0, 0, 0, 0)

-- The three paying producers' inputs, the extension's, the `propsEmpty`
-- landing's, a sequence park, and one undecorated control.  **78** states,
-- **8** held runs, **17** landings, all **17** with the walk's own floor,
-- **1** landing off a held run — and **0** held runs at a line start.  The
-- eight is what keeps the zero from passing vacuously: the sweep found runs to
-- check, and none of them was at column 0.
#guard censusP
  ["k:\n  a: &p b\n  c: d\n",
   "?\n  a: &p b\n: v\n",
   "k:\n  a: !t b\n  c: d\n",
   "k:\n  m:\n    a: &p b\n  n: 2\n",
   "k:\n  a: &p\n  c: d\n",
   "k:\n  a: &p !t b\n  c: d\n",
   "k:\n  a: b\n  c: d\nx: 2\n",
   "- &p a\n- y\n"] == (78, 8, 17, 17, 1, 0)

-- The bare anchor: the run is STILL HELD when the break comes, so the landing
-- is the props arm's own and the payment above is the one spent.
#guard walkP (ScannerState.mk' "k:\n  a: &p\n  c: d\n") 200 (0, 0, 0, 0, 0, 0)
  == (9, 1, 2, 2, 1, 0)

-- The decorated value: the run has closed by the landing, so the cover travels
-- the OTHER route — through the value's `pendingContent` park and item 152's
-- skeleton.  Same two landings, neither off a held run.
#guard walkP (ScannerState.mk' "k:\n  a: &p b\n  c: d\n") 200 (0, 0, 0, 0, 0, 0)
  == (10, 1, 2, 2, 0, 0)

-- The extension: two held-run states for one run, which is the relay's input.
#guard walkP (ScannerState.mk' "k:\n  a: &p !t b\n  c: d\n") 200 (0, 0, 0, 0, 0, 0)
  == (11, 2, 2, 2, 0, 0)

-- And the sibling actually resumes rather than re-opening — one inner mapping
-- with both entries, the anchor on the first.
#guard (match Events.streamToEvents "k:\n  a: &p b\n  c: d\n" with
        | .ok s => s | .error _ => "")
  == "+STR\n+DOC\n+MAP\n=VAL :k\n+MAP\n=VAL :a\n=VAL &p :b\n=VAL :c\n=VAL :d\n-MAP\n-MAP\n-DOC\n-STR\n"

/-! ## §6  What still does not pay

* ~~**The column-0 landing arm** of item 152's skeleton — item 147's escape read
  at the consumer.~~  (CLOSED by item 154: the floor there is preprocessing's
  unwind, the unwind runs on `needIndentCheck`, and a park that reached column 0
  consumed the break that arms it.  It never reached this lane in any case — a
  props park is never at a line start, §5's zero.)
* ~~**The sequence chain.**  `pendingProps.h_closeFE`, `pendingBlockContent
  .h_closeF` and `pendingBlock.h_closeF` are one chain carrying widths alone,
  and the sequence park's relay owes a `Mono` and a `SentinelBase` besides.
  This is the last of item 152's three residues.~~  (CLOSED by item 155.  The
  entry was mis-stated: the lane's FRAMES were empty, so the cover would have
  been spendable nowhere.  §2's "its one payer relays `pendingBlock.h_closeF`,
  which has none" was right about the field and wrong about what it cost.)
* **The membership split**, still declined for item 150's reason: paying it
  needs a payload on `KeyPackPunt`, which is a change to the constructor and to
  every consumer. -/

/-! ## §7  The price

**No new declaration.**  The item is two field conjuncts, three producers that
hand over a cover they already hold, two relays that step one they already
carry, seven sites that spend it, and one `have` for the payment.  Everything
the payment is built from — `landing_floor_of_arm`, `dedent_cover_of_floor`,
`preprocess_cover`, `dispatchContent_cover` — was already in the library; this
item adds no lemma to it, which is items 148–152's factoring continuing to pay
for itself. -/

end L4YAML.Tests.Guards.PropsParkCoverSpent

end Blanket
