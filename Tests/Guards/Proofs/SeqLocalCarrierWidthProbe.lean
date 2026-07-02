import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Window-local-carrier width-decrease probe (de-risk for the R447 carrier↔recursion co-construction)

A CONCRETE-emitter probe, run BEFORE authoring the R447 JOINT WIDTH INDUCTION (the last seq residual),
per `ref-probe-deferred-universal-before-producing` / `ref-minimal-pair-extracts-the-gate`.  R446 landed
`seqLocalCarrier_of_widthEnc` — the window-parametric carrier that, at any seq window `[lo, hi)`, builds
`SeqInteriorSeparators tokens lo hi` from the window's `SafeBodyUnit` and a width supplier `h_widthEnc`.
The R447 induction will DISCHARGE `h_widthEnc` by strong induction on window width, so its soundness rests
on a measure claim:

> every `RecSeqBody`-IH the carrier-build genuinely CONSUMES is at a window STRICTLY NARROWER than
> `[lo, hi)`.

The only place a `RecSeqBody`-IH is consumed in the carrier descent is `seqChild_safeBodyUnit`, at the
located genuine seq CHILD body `[p + 1, j)` (the interior of the enclosing opener's matched bracket),
gated `hi' - lo' < hiE - p` where `[p, hiE)` is the enclosing window.  This probe confirms — on the SAME
two witnesses `SeqDescentProviderProbe` uses, exercising both reach modes — that the child body is
strictly narrower than BOTH the enclosing window AND the whole window `[lo, hi)`, INCLUDING the
self-instantiation case the R446 next step flagged:

* `[[1, 2], 9]` — DESCEND-AT-ROOT.  The enclosing window `[p, hiE) = [2, 9)` IS the whole window
  `[lo, hi) = [2, 9)` (the `p = lo`, `hiE = hi` self-instantiation).  Even so the IH callee — the child
  body `[3, 6)` — has width `3 < 7`, so the joint width IH covers it with NO circular self-call: the gate
  at the whole window routes to the body via `seqChild_safeBodyUnit`'s strictly-smaller `[p+1, j)`, never
  re-descends into `[lo, hi)` itself.
* `[1, [2, 3]]` — ADVANCE-THEN-DESCEND.  The enclosing window `[p, hiE) = [4, 9)` is STRICTLY inside the
  whole window `[2, 9)` (`p = 4 > lo = 2`, width `5 < 7`); the IH callee `[5, 8)` has width `3`, strictly
  narrower than both.

So the joint width induction's IH (windows strictly narrower than `[lo, hi)`) suffices for every callee
the carrier-build needs, on both reach modes.  This is the positive de-risk for R447's FALLBACK note
(separate carrier/body inductions sharing the IH-supplier) being unnecessary on the measure grounds.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqLocalCarrierWidthProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- Window width — the strong-induction measure `hi - lo`. -/
def width (lo hi : Nat) : Nat := hi - lo

-- ════════════════════ Witness N := `[[1, 2], 9]` — DESCEND-AT-ROOT (self-instantiation) ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE
-- whole window [lo, hi) = [2, 9); gated sub-window [a, b) = [3, 6);
-- enclosing opener p = 2; enclosing window [p, hiE) = [2, 9); matching close j = 6; child body [p+1, j) = [3, 6).
#guard N.size == 11

-- the whole seq window and its width:
#guard flowBracketBalance N 2 9 == 0          -- [2, 9) is balanced (a FlowBodyWindow)
#guard width 2 9 == 7                          -- whole-window width

-- THE SELF-INSTANTIATION: the enclosing window of the gated sub-window [3, 6) IS the whole window [2, 9).
#guard N[2]!.val == .flowSequenceStart        -- enclosing opener p = 2 = lo (the whole window's head)
#guard flowBracketBalance N 2 3 == 1          -- NESTED gate (root discriminator balance lo a ≠ 0)
#guard width 2 9 == width 2 9                  -- enclosing [p, hiE) = [2, 9) = whole [lo, hi) — p = lo, hiE = hi

-- yet the IH is consumed only at the strictly-narrower child body [3, 6):
#guard N[6]!.val == .flowSequenceEnd          -- matching close j = 6, so child body [p+1, j) = [3, 6)
#guard width 3 6 == 3                          -- child-body width
#guard decide (width 3 6 < width 2 9)          -- STRICT: 3 < 7 — narrower than the WHOLE window
#guard decide (width 3 6 < (9 - 2))            -- STRICT vs enclosing-window span hiE - p = 9 - 2 = 7
                                               -- (seqChild_safeBodyUnit's IH gate hi' - lo' < hiE - p)

-- ════════════════════ Witness T := `[1, [2, 3]]` — ADVANCE-THEN-DESCEND ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE
-- whole window [lo, hi) = [2, 9); gated sub-window [a, b) = [5, 8);
-- enclosing opener p = 4; enclosing window [p, hiE) = [4, 9); matching close j = 8; child body [p+1, j) = [5, 8).
#guard T.size == 11
#guard flowBracketBalance T 2 9 == 0          -- whole [2, 9) balanced
#guard width 2 9 == 7

-- the enclosing window [4, 9) is STRICTLY inside the whole window [2, 9) (p = 4 > lo = 2):
#guard T[4]!.val == .flowSequenceStart        -- enclosing opener p = 4 ≠ lo
#guard flowBracketBalance T 4 9 == 0          -- [4, 9) balanced (the ADVANCE-tail FlowBodyWindow)
#guard decide (width 4 9 < width 2 9)          -- STRICT: enclosing width 5 < whole width 7

-- the IH callee — child body [5, 8) — is strictly narrower than BOTH:
#guard T[8]!.val == .flowSequenceEnd          -- matching close j = 8, child body [p+1, j) = [5, 8)
#guard width 5 8 == 3
#guard decide (width 5 8 < width 4 9)          -- STRICT vs enclosing window (3 < 5; seqChild IH gate)
#guard decide (width 5 8 < width 2 9)          -- STRICT vs whole window (3 < 7; joint width IH)

end L4YAML.Proofs.EmitterScannability.SeqLocalCarrierWidthProbe
