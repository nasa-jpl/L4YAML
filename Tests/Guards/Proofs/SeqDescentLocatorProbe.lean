import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.WellBracketed

/-!
# Seq-descent enclosing-locator probe (de-risk for `(i'-b-locator descent)`)

A CONCRETE-emitter probe, run BEFORE authoring the descent of the enclosing-facts `provider`
(per `ref-probe-deferred-universal-before-producing` / `ref-minimal-pair-extracts-the-gate`).

The `provider` (residual of `seqInteriorSeparators_of_enclosing_provider`) must, at every gated
window `[a,b)` with `SeqTypedInterior tokens a b`, hand back an enclosing seq `[loS,hiS)` with
`loS ≤ a`, `b ≤ hiS`, `flowBracketBalance tokens loS a = 0`, plus the three enclosing facts.
The ROOT seed (`seqEnclosingFacts_provider_root`) handles windows with the top-level discriminator
`flowBracketBalance tokens 2 a = 0`.  The DESCENT must handle the NESTED windows (discriminator
FAILS).  This probe answers, on the R304 witness `[[1, 2], 9]`:

* (L) the concrete token layout (pin the windows);
* (G) WHICH windows are gated, and which are nested (discriminator fails);
* (E) for each nested gated window start `a`, the enclosing-seq opener position `p = loS - 1`
      located by a BACKWARD scan (largest `p < a` with `tokens[p]` an opener and the bracket
      opened at `p` still open at `a`), and that `tokens[p] = .flowSequenceStart`,
      `flowBracketBalance tokens (loS) a = 0`, `loS ≤ a`, `b ≤ hiS`;
* (B) the KEY de-risk: that the gate's `btFold`-top `= some true` at `a` and the located opener's
      type AGREE — i.e. the gate-top classifies the located enclosing as a SEQ, so no separate
      type reconstruction is needed at the located position (`enclosingMark` at `loS` = `some true`).
-/

namespace L4YAML.Proofs.EmitterScannability.SeqDescentLocatorProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

/-- A plain scalar leaf. -/
def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The R304 witness: a nested flow sequence holding a flow sequence AND a scalar.
    Emits `[[1, 2], 9]` — one stream with an OUTER seq body and a NESTED seq body, so the
    descent's enclosing-locator can be exercised at depth `> 0`. -/
def probeVal : YamlValue :=
  .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]

/-- The scanned, filtered token array of the emitted witness. -/
def probeToks : Array (Positioned YamlToken) :=
  match scanFiltered (emit probeVal) with
  | .ok ts => ts
  | .error _ => #[]

/-- The seq-vs-map discriminator read off `WellTyped`'s `btFold`: head of the typed stack after
    the prefix `[0, opener)` (`true` = enclosed by `[`, `false` = enclosed by `{`). -/
def enclosingMark (T : Array (Positioned YamlToken)) (opener : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take opener)).bind (·.head?)

/-- The toy `SeqTypedInterior` gate as a `Bool`: depth-`0`-balanced ∧ enclosing mark `true`. -/
def gated (T : Array (Positioned YamlToken)) (a b : Nat) : Bool :=
  decide (flowBracketBalance T a b = 0) && (enclosingMark T a == some true)

/-- BACKWARD enclosing-seq-opener scan: the largest `p < a` whose bracket opened at `p` is still
    open at `a` — i.e. `flowBracketBalance T (p+1) a = 0` (a sits at the opener's body level) and
    the depth from `p+1` never returns below `0` before `a` (the floor stays `≥ 0` over `(p, a]`),
    with `tokens[p]` an opener.  Returns `loS = p + 1` (the body start). -/
def locateEnclosingLoS (T : Array (Positioned YamlToken)) (a : Nat) : Option Nat :=
  ((List.range a).reverse.find? fun p =>
    decide (flowBracketDelta T[p]!.val = 1) &&
    decide (flowBracketBalance T (p+1) a = 0) &&
    (List.range (a + 1)).all (fun i =>
      if p + 1 ≤ i ∧ i ≤ a then decide (flowBracketBalance T (p+1) i ≥ 0) else true)
  ).map (· + 1)

/-- FORWARD matching-close from a body start `loS` (opener at `loS-1`): the smallest `j > loS-1`
    with `flowBracketBalance T loS j = 0` and `tokens[j]` a closer.  Returns `hiS = j`. -/
def locateEnclosingHiS (T : Array (Positioned YamlToken)) (loS : Nat) : Option Nat :=
  (List.range T.size).find? fun j =>
    decide (loS ≤ j) &&
    decide (flowBracketDelta T[j]!.val = -1) &&
    decide (flowBracketBalance T loS j = 0)

-- ════════════════════════ (L) token layout ════════════════════════
#guard emit probeVal == "[[\"1\", \"2\"], \"9\"]"
#guard probeToks.size == 11
#guard probeToks[1]!.val == .flowSequenceStart   -- outer `[`  (outer body [2,9))
#guard probeToks[2]!.val == .flowSequenceStart   -- inner `[`  (inner body [3,6))
#guard probeToks[4]!.val == .flowEntry           -- inner `,`
#guard probeToks[6]!.val == .flowSequenceEnd     -- inner `]`
#guard probeToks[7]!.val == .flowEntry           -- outer `,`
#guard probeToks[9]!.val == .flowSequenceEnd     -- outer `]`

-- ════════════════════════ (G) gated windows, nested vs root ════════════════════════
-- the inner body start a=3 is gated and NESTED (balance 2 3 ≠ 0):
#guard gated probeToks 3 6                         -- inner body [3,6) is gated
#guard flowBracketBalance probeToks 2 3 == 1       -- ... and NESTED (discriminator fails)
-- a root-level window a=7..  balance 2 7 = 0 (root); a=3..6 are nested:
#guard flowBracketBalance probeToks 2 7 == 0       -- root-level
#guard flowBracketBalance probeToks 2 8 == 0       -- root-level

-- ════════════════════════ (E) enclosing locator at nested windows ════════════════════════
-- inner body window [3,6): enclosing opener p=2 → loS=3, hiS=6.
#guard locateEnclosingLoS probeToks 3 == some 3    -- loS = 3 (opener at p=2 = inner `[`)
#guard locateEnclosingHiS probeToks 3 == some 6    -- hiS = 6 (inner `]`)
#guard probeToks[2]!.val == .flowSequenceStart     -- located opener IS a seq opener
#guard flowBracketBalance probeToks 3 3 == 0       -- balance loS a = 0  (a = loS here)
-- a nested INTERIOR window, e.g. the inner first item [3,5) = `"1" ,`:
#guard gated probeToks 3 5                          -- gated (balance 0, enclosed by seq)
#guard flowBracketBalance probeToks 2 3 == 1       -- nested
#guard locateEnclosingLoS probeToks 3 == some 3    -- located enclosing loS = 3
#guard (3 ≤ 3 : Bool)                              -- loS ≤ a
#guard (5 ≤ 6 : Bool)                              -- b ≤ hiS

-- ════════════════════════ (B) gate-top AGREES with located opener type ════════════════════════
-- the KEY de-risk: the gate-top at the located body start loS=3 is `some true` (seq), so the
-- located enclosing's type need NOT be separately reconstructed — the gate already classifies it.
#guard enclosingMark probeToks 3 == some true      -- gate-top at loS = some true
#guard probeToks[2]!.val == .flowSequenceStart     -- ... matching the opener at loS-1 = 2

end L4YAML.Proofs.EmitterScannability.SeqDescentLocatorProbe
