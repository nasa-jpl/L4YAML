import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Narrow-from-root coverage probe (de-risk for `seqRoot_seqInteriorSeparators`)

A CONCRETE-emitter probe backing the architectural redirect the root seed commits to: the seq
separator carrier `SeqInteriorSeparators` is established ONCE at the outer span `[2, size-2)` (the
root seed) and lifted to every nested body window by `SeqInteriorSeparators_narrow` — the carrier is
a subset restriction, so this loses nothing.  This is why R317's plan to *re-derive* the carrier per
window (which would source each window's `SafeBodyUnit` from that window's own `RecSeqBody`, the very
output the recursion is producing — a circular dependency) is unnecessary AND avoidable.

`SeqInteriorSeparators_narrow` lifts `[lo, hi)` to any `[lo', hi') ⊆ [lo, hi)`.  So the claim "the
root span covers every B3 window" is exactly: every gated body sub-window `[lo', hi')` satisfies
`2 ≤ lo'` and `hi' ≤ size - 2`.  This probe confirms it on the two witnesses, for the windows the
B3 recursion actually visits (the same windows `SeqDispatchPartitionProbe` exercises):

* `[[1, 2], 9]` (size 11, root span `[2, 9)`): the nested window `[3, 6)` and the top-level window
  `[7, 9)` both have `2 ≤ lo` and `hi ≤ 9`;
* `[1, [2, 3]]` (size 11, root span `[2, 9)`): the top-level window `[2, 4)` and the nested window
  `[5, 8)` both have `2 ≤ lo` and `hi ≤ 9`.

Each window also passes the gate (it is `SeqTypedInterior`-shaped, balance-0 + seq-enclosed + floor),
so the narrow's restricted-domain quantifier body fires on exactly these windows — the root seed's
separator facts cover them with no re-derivation.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqRootSeedNarrowProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The seq-vs-map mark read off `btFold`: head of the typed stack after the prefix `[0, a)`. -/
def enclosingMark (T : Array (Positioned YamlToken)) (a : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take a)).bind (·.head?)

/-- The gate `SeqTypedInterior` evaluated as a `Bool` (the three window-absolute conjuncts). -/
def gateOK (T : Array (Positioned YamlToken)) (a b : Nat) : Bool :=
  (flowBracketBalance T a b == 0) &&
  (enclosingMark T a == some true) &&
  (List.range (b + 1)).all (fun i => if a ≤ i then decide (flowBracketBalance T a i ≥ 0) else true)

/-- Root-span coverage: `2 ≤ lo` and `hi ≤ size - 2`, i.e. `narrow` reaches `[lo, hi)` from `[2, size-2)`. -/
def coveredByRoot (T : Array (Positioned YamlToken)) (lo hi : Nat) : Bool :=
  (2 ≤ lo) && (hi ≤ T.size - 2)

-- ════════════════════ Witness N := `[[1, 2], 9]` (root span [2, 9)) ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE ;  size - 2 = 9 = root span end
#guard N.size == 11
#guard N.size - 2 == 9

-- nested B3 window [3, 6): gated AND covered by the root span (narrow reaches it)
#guard gateOK N 3 6 == true
#guard coveredByRoot N 3 6 == true
-- top-level B3 window [7, 9): gated AND covered
#guard gateOK N 7 9 == true
#guard coveredByRoot N 7 9 == true

-- ════════════════════ Witness T := `[1, [2, 3]]` (root span [2, 9)) ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE ;  size - 2 = 9
#guard T.size == 11
#guard T.size - 2 == 9

-- top-level B3 window [2, 4): gated AND covered
#guard gateOK T 2 4 == true
#guard coveredByRoot T 2 4 == true
-- nested B3 window [5, 8): gated AND covered
#guard gateOK T 5 8 == true
#guard coveredByRoot T 5 8 == true

end L4YAML.Proofs.EmitterScannability.SeqRootSeedNarrowProbe
