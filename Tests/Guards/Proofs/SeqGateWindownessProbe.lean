import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Gate-underdetermines-windowness probe (de-risk for `(i'-b-B2c-provider-from-gate)`)

A CONCRETE-emitter probe, run BEFORE authoring the gated `desc` provider, per
`ref-probe-provider-satisfiable-before-assembler`.  The next-step question: does the gate
`SeqTypedInterior tokens a b` ALONE force `tokens[b]! = .flowSequenceEnd` (so the provider could read
its close straight off the gated window's END `b`), or does it NOT — so the provider must be stated
INSIDE the parent `windowWidth_strongRecOn` step where the LOCATED enclosing seq body
`[loS, hiS) = [p+1, j)` is the real window, the gate's `[a,b) ⊆ [loS, hiS)` only SELECTING a
sub-interval of it?

**The probe REFUTES "the gate forces window-ness."**  The existing `SeqDescentProviderProbe` only ever
exercises gated windows whose end `b` COINCIDES with the enclosing close `j` (`[3,6)` on `[[1,2],9]`,
`[5,8)` on `[1,[2,3]]`), so it cannot exhibit the refutation.  Here we pick gated windows with
`b ≠ j` — a trailing-separator slice `"1" ,` / `"2" ,` — that STILL pass all three gate conjuncts
(`balance a b = 0`, enclosing-seq `btFold`-top `= some true`, local-Dyck floor) yet whose end token
`tokens[b]!` is a SCALAR, not `.flowSequenceEnd`.  So the gate underdetermines the close: `b` is a free
choice anywhere inside the enclosing seq body, and the provider can NOT read `tokens[b]!` as its close.

**What this confirms about the architecture.**  The provider must locate the ENCLOSING seq body
`[loS, hiS)` and read `tokens[hiS]! = .flowSequenceEnd` off ITS matching close — exactly what
`seqDescent_provider_of_located` (`SeqInteriorSeparators.lean:728`) already does: it never inspects
`tokens[b]!`; it locates `j = hiS` via `flowBracketBalance_matching_close`, proves
`tokens[j]! = .flowSequenceEnd` (its brick (3)), and proves the containment `b ≤ j` (the
`ref-two-floor-relay-close-bound` relay) so the gate window is SELECTED inside `[loS, hiS)`.  Hence the
`(i'-b-B2c-provider-from-gate)` brick is NOT "author a fresh provider from the gate" — that provider
already exists and is correctly stated inside the parent step.  See Reflection 340.

For each witness we exhibit, on the SAME two objects `SeqDescentProviderProbe` uses:

* a `b ≠ j` gated window: gate holds, `tokens[b]!` is NOT `.flowSequenceEnd` (the refutation);
* the enclosing located seq body `[loS, hiS)`: `tokens[hiS]! = .flowSequenceEnd` and `b ≤ hiS`
  (the close the provider actually reads, and the SELECTION bound);
* the `b = j` window for contrast: there `tokens[b]!` HAPPENS to be `.flowSequenceEnd`, but only
  because `b` was chosen `= hiS` — the gate did not force it.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqGateWindownessProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The seq-vs-map mark read off `btFold`: head of the typed stack after the prefix `[0, a)`. -/
def enclosingMark (T : Array (Positioned YamlToken)) (a : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take a)).bind (·.head?)

-- ════════════════════ Witness N := `[[1, 2], 9]` ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE
-- enclosing inner seq body [loS, hiS) = [3, 6), opener p = 2, matching close j = 6.
#guard N.size == 11

-- (the `b ≠ j` gated window [3, 5) = `"1" ,` — a trailing-separator slice):
#guard flowBracketBalance N 3 5 == 0            -- gate conjunct 1: balance a b = 0
#guard enclosingMark N 3 == some true           -- gate conjunct 2: enclosing seq btFold-top
#guard (List.range 3).all fun i =>              -- gate conjunct 3: local-Dyck floor ≥ 0 over [3, 5]
  let t := i + 3; if t ≤ 5 then decide (flowBracketBalance N 3 t ≥ 0) else true
-- ...the gate HOLDS, yet the window END is NOT a close:
#guard N[5]!.val != .flowSequenceEnd            -- tokens[b]! is the scalar "2", NOT seqEnd

-- (the enclosing located seq body [loS, hiS) = [3, 6) supplies the REAL close):
#guard N[2]!.val == .flowSequenceStart          -- opener p = 2 (loS = p + 1 = 3)
#guard N[6]!.val == .flowSequenceEnd            -- tokens[hiS]! = seqEnd — the provider's close
#guard decide (3 ≤ 3) && decide (5 ≤ 6)         -- loS ≤ a ∧ b ≤ hiS — the gate window is SELECTED

-- (contrast: the `b = j` window [3, 6) — tokens[b]! IS seqEnd, but only because b was chosen = hiS):
#guard flowBracketBalance N 3 6 == 0            -- still gated
#guard N[6]!.val == .flowSequenceEnd            -- coincides with the close — NOT forced by the gate

-- ════════════════════ Witness T := `[1, [2, 3]]` ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE
-- enclosing inner seq body [loS, hiS) = [5, 8), opener p = 4, matching close j = 8.
#guard T.size == 11

-- (the `b ≠ j` gated window [5, 7) = `"2" ,`):
#guard flowBracketBalance T 5 7 == 0            -- gate conjunct 1
#guard enclosingMark T 5 == some true           -- gate conjunct 2
#guard (List.range 3).all fun i =>              -- gate conjunct 3: floor ≥ 0 over [5, 7]
  let t := i + 5; if t ≤ 7 then decide (flowBracketBalance T 5 t ≥ 0) else true
-- ...gate HOLDS, yet the END is NOT a close:
#guard T[7]!.val != .flowSequenceEnd            -- tokens[b]! is the scalar "3", NOT seqEnd

-- (the enclosing located seq body [loS, hiS) = [5, 8)):
#guard T[4]!.val == .flowSequenceStart          -- opener p = 4 (loS = 5)
#guard T[8]!.val == .flowSequenceEnd            -- tokens[hiS]! = seqEnd — the provider's close
#guard decide (5 ≤ 5) && decide (7 ≤ 8)         -- loS ≤ a ∧ b ≤ hiS — SELECTED

end L4YAML.Proofs.EmitterScannability.SeqGateWindownessProbe
