module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The completed content park carries the cover (DOCS item 152)

Item 151 gave `ResumeKeyCtx` a cover slot on each lane and paid it at the one
relay that held both readings of the stack.  Every other site filled the slot
with a punt, and each punt named a CONSTRUCTOR field rather than a missing
derivation: the faces the landing skeleton is handed carry widths and no cover.

This item pays two of them.  `pendingContent.h_framesS` and `.h_framesV` — the
faces a completed mapping VALUE leaves behind — gain a cover conjunct, the five
producers that already hold one on the close face they ride hand it over, and
`accum_content_pending`'s shared landing skeleton spends it.

**The index is existential, and that is what makes one slot serve two lanes.**
This park is depth-0 by construction: it has no `n` to state a floor against.
The two faces that fund it are bounded at DIFFERENT indices — the stream face at
the entry's own level, the value face one column above the `?` (item 150's
deliberate stagger) — and `IndentStackCover.Floor.pop_to` spends the WIDTHS half
alone.  So the field carries the index and forgets it, exactly as
`resumectx_of_landing` does, and the two faces share one shape.

**The payer is the SKELETON's, not the park's.**  What a landing's payment needs
is `s_prep`'s own floor, and `accum_content_pending` already carries the
`SentinelBase` and `Mono` that produce it.  So a park has only to say what it
kept: the payment is stated once, in the break-crossed landing arm, and serves
both landing routes there.  The column-0 arm cannot state it at all — that is
item 147's escape, met here at a CONSUMER instead of at a producer.

§1 is the slot and its two indices.  §2 is the step that carries a producer's
cover to the park.  §3 is the skeleton's payment, whose conclusion is a plain
existential.  §4 walks the corpus.  §5 is what still does not pay.  §6 is the
price. -/

namespace L4YAML.Tests.Guards.ContentParkCoverSpent

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.IndentStackCover
open L4YAML.Proofs.IndentStackMono
open L4YAML.Proofs.IndentStackBase
open L4YAML.Proofs.CouplingBridge

/-! ## §1  One slot, two indices

The two faces are bounded at different levels and both land in the same field,
because what the field states about the index is only that there IS one. -/

-- The stream face's cover is bounded at the park's own level …
example {sc : ScannerState} {sp_start sp_scan : SurfPos} {n lo : Nat} {ks : List FrameLevel}
    (h_fl : Floor lo n (FrameLevel.map n :: ks)) (h_cv : Covered lo (FrameLevel.map n :: ks) sc)
    (fS : ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) :
    (∃ ks : List FrameLevel,
      ((∃ lo n : Nat, Floor lo n ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) ks sp_mid) ∨ True :=
  Or.inl ⟨FrameLevel.map n :: ks, Or.inl ⟨lo, n, h_fl, h_cv⟩, fS⟩

-- … and the value face's stands one column ABOVE the `?`, over the list the
-- stream face writes as `FrameLevel.map n :: ks`.  Same slot, and no second argument.
example {sc : ScannerState} {sp_start sp_scan : SurfPos} {n nv lo : Nat} {ks : List FrameLevel}
    (h_fl : Floor lo (n + 1) ks) (h_cv : Covered lo ks sc)
    (fV : ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_mid) :
    (∃ (nv : Nat) (ks : List FrameLevel),
      ((∃ lo n : Nat, Floor lo n ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_mid) ∨ True :=
  Or.inl ⟨nv, ks, Or.inl ⟨lo, n + 1, h_fl, h_cv⟩, fV⟩

-- The punt is still a value of the same type, which is what lets the producers
-- that hold nothing keep compiling.
example {sc : ScannerState} {sp_start sp_scan : SurfPos} {ks : List FrameLevel}
    (fS : ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) ks sp_mid) :
    (∃ ks : List FrameLevel,
      ((∃ lo n : Nat, Floor lo n ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) ks sp_mid) ∨ True :=
  Or.inl ⟨ks, Or.inr trivial, fS⟩

/-! ## §2  The step that carries it

A producer holds its cover at the state the ENCLOSING park had; the field is
stated at the state the NEW park has.  Preprocessing only pops and a content
dispatch writes no level, so the two are the same cover and nothing is
re-derived — the whole reason paying these two fields costs the producers one
`Or.imp` each. -/

example {sc s_prep s' : ScannerState} {c : Char} {lo : Nat} {ks : List FrameLevel}
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_dispatch : scanNextToken_dispatchContent
      (if s_prep.allowDirectives then
        { s_prep with allowDirectives := false, documentEverStarted := true }
      else s_prep) c = .ok s')
    (hc : Covered lo ks sc) : Covered lo ks s' :=
  dispatchContent_cover h_dispatch
    ((preprocess_cover h_preprocess hc).of_indents_eq (by split <;> rfl))

/-! ## §3  The skeleton's payment

`landing_floor_of_arm` turns the anyCol product's landed disjunct into the
landing's own floor, and `dedent_cover_of_floor` (item 151's factoring) does the
hop.  **The conclusion carries no `∨ True`**, so a consumer can tell it was paid
— which is the interrogability the two items buy together, and the reason the
payer is worth stating once rather than inlining at each landing route.

Note what the payment does NOT read: the index `m` the incoming cover is bounded
at appears nowhere in the result.  That is the fact §1's two shapes rest on. -/

example {sc s_prep : ScannerState} {c : Char} {sp_scan : SurfPos}
    {w lo m : Nat} {ksw ksw' : List FrameLevel}
    (h_noflow : s_prep.inFlow = false)
    (h_larm : sp_scan.col ≠ 0 → s_prep.inFlow = false →
      s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos.col = s_prep.col ∧
      s_prep.simpleKeyAllowed = true ∧
      (s_prep.currentIndent ≤ (s_prep.col : Int) ∨ s_prep.indents.size ≤ 1))
    (hcol : sp_scan.col ≠ 0)
    (h_base : SentinelBase sc) (h_mono : Mono sc)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, c)))
    (h_fl : Floor lo m ksw) (h_cv : Covered lo ksw sc)
    (hmem : FrameLevel.map w ∈ ksw) (h_ww : ResumeWidths ksw ksw' w) (h_scol : s_prep.col = w) :
    ∃ lo : Nat, Floor lo w (FrameLevel.map w :: ksw') ∧ Covered lo (FrameLevel.map w :: ksw') s_prep :=
  dedent_cover_of_floor (preprocess_mono h_preprocess h_mono)
    (by rw [← h_scol]; exact landing_floor_of_arm h_noflow h_larm hcol h_base h_preprocess)
    h_fl (preprocess_cover h_preprocess h_cv) hmem h_ww

-- And the same payment composed into the context's slot, which is what the two
-- landing routes in the break-crossed arm actually pass.
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

/-! ## §4  The corpus, walked against the scanner

The landings this item reaches are dedents off a completed content park, and
what the derivation needs besides the scanner's own floor is the PARK to be off
a line start — the break-crossed arm is where the payment can be stated.  A
block scalar is the one content scan that ends past a break, so its park sits AT
a line start, and that is what the corpus below discriminates on. -/

private def landingFactsC (s : ScannerState) : Nat × Nat × Nat :=
  match scanNextToken_preprocess s with
  | .ok (some (s', _)) =>
      if s'.indents.size < s.indents.size then
        (1, if s'.currentIndent ≤ (s'.col : Int) then 1 else 0,
            if s.col ≠ 0 then 1 else 0)
      else (0, 0, 0)
  | _ => (0, 0, 0)

/-- States seen; pops; pops with the landing's own floor; pops off a park that
    is not at a line start. -/
private def walkC (s : ScannerState) : Nat → Nat × Nat × Nat × Nat →
    Nat × Nat × Nat × Nat
  | 0, acc => acc
  | fuel + 1, (seen, pops, floored, offStart) =>
    let (p, f, o) := landingFactsC s
    let acc := (seen + 1, pops + p, floored + f, offStart + o)
    match scanNextToken s with
    | .ok (some s') => walkC s' fuel acc
    | _ => acc

private def censusC (inputs : List String) : Nat × Nat × Nat × Nat :=
  inputs.foldl (fun acc i => walkC (ScannerState.mk' i) 200 acc) (0, 0, 0, 0)

-- Item 109's flagship and three of its twins, one nested dedent, and three
-- inputs whose park is a BLOCK SCALAR.  **84** states, **8** pops, all **8**
-- with the landing's own floor, and **6** of the 8 off a line start.  The
-- scanner establishes the floor at every one, so the split measures what the
-- PROOF can reach and not what the landing does.
#guard censusC
  ["?\n  a: b\n  c: d\n: - w\n",
   "k:\n  a: b\n  c: d\nx: 2\n",
   "a:\n  b:\n    c: d\n  e: 2\n",
   "k:\n  a: b\nx: 2\n",
   "a:\n  b: |\n    x\nc: 2\n",
   "a:\n  b: >\n    x\nc: 2\n",
   "k:\n  a: |\n    x\n  c: 2\nd: 3\n",
   "?\n  a: |\n    x\n  c: d\n: - w\n"] == (84, 8, 8, 6)

-- Item 109's own input: one pop, floored, off a line start — the landed `:`
-- resumes the width-2 level with the cover beside its widths.
#guard walkC (ScannerState.mk' "?\n  a: b\n  c: d\n: - w\n") 200 (0, 0, 0, 0)
  == (11, 1, 1, 1)

-- …and the block-scalar park, where the same pop has the same floor and the
-- column-0 landing arm has no way to state it.
#guard walkC (ScannerState.mk' "a:\n  b: |\n    x\nc: 2\n") 200 (0, 0, 0, 0)
  == (9, 1, 1, 0)

-- A block scalar one level in still pays, because the pop that matters is the
-- LATER landing and its park is an ordinary value.
#guard walkC (ScannerState.mk' "k:\n  a: |\n    x\n  c: 2\nd: 3\n") 200 (0, 0, 0, 0)
  == (12, 1, 1, 1)

/-! ## §5  What still does not pay

* ~~**The column-0 landing arm**, item 147's escape read at the consumer.  The
  payment wants the walk's re-arm, and a park AT a line start crossed no break.
  Measured above: two of eight.~~  (CLOSED by item 154.  The payment does not
  want the walk's re-arm — it wants preprocessing's unwind, which runs on
  `needIndentCheck`, and a park that reached column 0 consumed the break that
  armed it.  The datum is the PARK's, as item 77's own save flag has been.)
* ~~**The props park.**  `accum_content_pending`'s `pendingProps` arm is the one
  punt where the PAYER is not the obstacle — that arm is break-crossed, so the
  floor is there for the asking.  `pendingProps`'s own two frames fields carry
  no cover, so there is nothing to spend it on, and the five `pendingContent`
  producers that ride those fields punt for the same reason.~~  (CLOSED by item
  153 — the two fields gained the same conjunct, three mapping producers pay it,
  two extensions relay it, and both consumers spend it.)
* ~~**The sequence chain.**  `pendingBlockContent.h_closeF` carries widths alone,
  and its own payers are `pendingBlock.h_closeF`, which carries none either —
  two fields on one chain, and the sequence park's relay owes a `Mono` and a
  `SentinelBase` besides.~~  (CLOSED by item 155.  The chain is real and the
  diagnosis was incomplete: those fields carried no FRAMES either, so a cover
  on them would have had no width to be spent at.) -/

example {sc : ScannerState} {sp_start sp_scan : SurfPos} {nv : Nat} {ks : List FrameLevel}
    (fV : ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_mid) :
    (∃ (nv : Nat) (ks : List FrameLevel),
      ((∃ lo n : Nat, Floor lo n ks ∧ Covered lo ks sc) ∨ True) ∧
      ∀ sp_mid : SurfPos, SSLComments sp_scan sp_mid →
      ResumeFrames (ExplValueLine sp_start nv) ks sp_mid) ∨ True :=
  Or.inl ⟨nv, ks, Or.inr trivial, fV⟩

/-! ## §6  The price

**No new declaration.**  The item is two field conjuncts, two `have`s (the
producers' step and the skeleton's payment), five producer sites that hand over
a cover they already hold, and seven sites that say in one `Or.inr trivial` that
they hold none.  `dedent_cover_of_floor` — item 151's factoring — is what makes
the payment a single line at the point of use; had the hop stayed inside
`dedent_cover_of_landing` with that lemma's two escapes attached, this item
would have had to re-author it.

What is left of the cover's work is §5's three entries: ~~the col-0 landing
arm~~ (item 154), ~~`pendingProps`'s two frames fields~~ (item 153), and ~~the
`pendingBlock` → `pendingBlockContent` chain's two `h_closeF`s — which item
154's own census finds is a chain of THREE, `pendingProps.h_closeFE`
included~~ (item 155).  All three are closed. -/

end L4YAML.Tests.Guards.ContentParkCoverSpent

end Blanket
