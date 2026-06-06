import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.WellBracketed

/-!
# `bodySucc` seq-vs-map discriminator probe (Reflection 297)

A CONCRETE-emitter probe, run BEFORE producing the `(i'-b-descend)` separator carrier per
`ref-probe-deferred-universal-before-producing`: a deferred `∀`-over-sub-windows you only
*project* can hide its own falsity, so check it on real `emit ∘ scanFiltered` output first.

The carrier proposed by the 144th-revision map is *"on every sequence-typed depth-`0`-balanced
bracket-interior sub-window, the `bodySucc` separator fact holds."* This probe answers the two
questions the map gated the brick on, **by `#guard` on the real emitter output** (not by
projection):

* **Is the GATE sufficient?** — does `bodySucc` actually hold on a seq-typed interior of concrete
  output?  YES (`bodySuccHolds probeToks 2 10`).
* **Is the GATE necessary?** — does `bodySucc` FAIL without it, on a map-typed interior of the SAME
  stream?  YES it fails (`¬ bodySuccHolds probeToks 3 7`): inside `{ … }` a key is a depth-`0`
  value-end followed by `value` (`:`), not a separator — exactly the [[ref-non-restriction-residual-root-seed]]
  falsity, now witnessed concretely.

And it settles decision (a) — *which* predicate to gate on — without inventing one: the
discriminator is the `btStack` TOP that `WellTyped`/`btFold` already computes
(`flowSequenceStart ↦ true`, `flowMappingStart ↦ false`).  The minimal pair `[{"k": "v"}, "x"]`
holds both a seq interior and a map interior in one stream; the structural feature that differs
between the holding window and the failing one IS the gate — read off, not invented.
-/

namespace L4YAML.Proofs.EmitterScannability.BodySuccSeqDiscriminator

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)

/-- A plain scalar leaf. -/
def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The minimal pair: a flow sequence holding a flow mapping AND a scalar.
    Emits `[{"k": "v"}, "x"]` — one token stream with a seq-typed interior and a map-typed
    interior, so the discriminator can be exercised on both within a single object. -/
def probeVal : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "k", sc "v")], sc "x"]

/-- The scanned, filtered token array of the emitted minimal pair.

    Layout (verified by the `#guard`s below):
    `0:streamStart 1:[ 2:{ 3:key 4:"k" 5:value 6:"v" 7:} 8:flowEntry 9:"x" 10:] 11:streamEnd`.
    Outer seq body window = `[2,10)`; inner map body window = `[3,7)`. -/
def probeToks : Array (Positioned YamlToken) :=
  match scanFiltered (emit probeVal) with
  | .ok ts => ts
  | .error _ => #[]

/-- Decidable model of the `bodySucc` field over a window `[lo,hi)`: at every position `k` whose
    window-balance-after returns to `0` and whose token is not a `flowEntry`, the window must
    either end (`k+1 = hi`) or be followed by a `flowEntry` separator. -/
def bodySuccHolds (T : Array (Positioned YamlToken)) (lo hi : Nat) : Bool :=
  (List.range hi).all fun k =>
    if lo ≤ k ∧ k < hi then
      if flowBracketBalance T lo (k+1) = 0 ∧ T[k]!.val ≠ .flowEntry then
        decide (k+1 = hi) || decide (T[k+1]!.val = .flowEntry)
      else true
    else true

/-- The seq-vs-map discriminator, read straight off `WellTyped`'s `btFold`: the head of the typed
    stack after consuming the prefix `[0, opener]` is the enclosing bracket's mark
    (`true` = sequence, `false` = mapping). No new predicate — the existing substrate computes it. -/
def enclosingMark (T : Array (Positioned YamlToken)) (opener : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take opener)).bind (·.head?)

-- The emitted string and token layout (pins the windows the claims below reference).
#guard emit probeVal == "[{\"k\": \"v\"}, \"x\"]"
#guard probeToks.size == 12
#guard probeToks[1]!.val == .flowSequenceStart   -- outer `[`, opener of seq body window [2,10)
#guard probeToks[2]!.val == .flowMappingStart    -- inner `{`, opener of map body window [3,7)
#guard probeToks[10]!.val == .flowSequenceEnd    -- outer `]`
#guard probeToks[7]!.val == .flowMappingEnd      -- inner `}`

-- (1) GATE SUFFICIENT: `bodySucc` HOLDS on the seq-typed interior of concrete emitter output.
#guard bodySuccHolds probeToks 2 10
-- (2) GATE NECESSARY: `bodySucc` FAILS on the map-typed interior of the SAME stream
--     (the key at k=3 is a depth-0 value-end followed by `value`, not a separator).
#guard !bodySuccHolds probeToks 3 7

-- (3) The discriminator classifies each window correctly, from the existing typed-bracket fold:
#guard enclosingMark probeToks 2 == some true    -- seq window [2,10): enclosed by `[`
#guard enclosingMark probeToks 3 == some false   -- map window [3,7): enclosed by `{`

end L4YAML.Proofs.EmitterScannability.BodySuccSeqDiscriminator
