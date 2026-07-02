import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Seq-gate floor probe (de-risk for `(i'-b-locator-glue-close)`, R313)

A CONCRETE-emitter probe, run while authoring the forward-CLOSE brick of the enclosing-facts
`provider` (per `ref-probe-deferred-universal-before-producing` / `ref-probe-provider-head-blind-gate`).

It records TWO findings that redirected the route:

* **(I) The 160th "Next step"'s matching-close route is BROKEN.** The prediction was to invoke
  `flowBracketBalance_matching_close` with base `k = p` over `[p, tokens.size)`, "the Dyck floor over
  `[p, size)` from global well-bracketedness".  But the floor from an opener `p` CANNOT survive past
  `p`'s own enclosing close: on `[[1, 2], 9]` (`p = 2`, the inner `[`) the running balance from `p`
  dips to `-1`, and the total `balance 2 11 = -1 ≠ 0` — both `h_dyck` and `h_total` FAIL.  The correct
  enclosing window is `[p, hi)` where `hi` is the enclosing recursion window end (balance `0`, floored),
  NOT `size`.

* **(II) The gate `SeqTypedInterior` was FLOOR-BLIND, making the carrier FALSE on a valid witness.**
  On `[[1], [2]]` the CROSS-SIBLING window `[3, 7)` — from inside the first inner seq to inside the
  second — is depth-`0`-balanced (`balance 3 7 = 0`) and seq-enclosed (`btFold`-top at `3` is
  `some true`), so it passed the BARE two-conjunct gate; yet `bodySuccFact` is outright FALSE on it
  (`tokens[3] = "1"` is depth-`0`-complete but `tokens[4] = ]`, not a `.flowEntry`).  So the carrier
  `SeqInteriorSeparators tokens 2 9` would be FALSE on a *valid* flow value.  Cross-sibling windows DIP
  below `0` (crossing the first sibling's close), so the local-Dyck floor `∀ i ∈ [a,b], balance a i ≥ 0`
  excludes EXACTLY them — `floored ⟹ bodySuccFact` at every gated window of the witness.  R313 added
  the floor as the gate's third conjunct; this probe checks the NEW gate rejects `[3, 7)`.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqGateFloorProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- `[[1], [2]]` — two SIBLING inner flow sequences inside an outer flow sequence.  The two bracket
    siblings are what create a genuine cross-sibling balanced window (a single scalar sibling, as in
    `[[1, 2], 9]`, cannot — there is no second bracket to climb back into). -/
def twoSibVal : YamlValue :=
  .sequence .flow #[.sequence .flow #[sc "1"], .sequence .flow #[sc "2"]]

def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit twoSibVal) with | .ok ts => ts | .error _ => #[]

/-- The bare TWO-conjunct gate (pre-R313): balance-`0` ∧ seq-enclosed.  Floor-blind. -/
def bareGated (a b : Nat) : Bool :=
  decide (flowBracketBalance T a b = 0) &&
  ((btFold (some []) (T.toList.take a)).bind (·.head?) == some true)

/-- The local-Dyck floor over `[a, b]` (R313's added gate conjunct), as a `Bool`. -/
def floored (a b : Nat) : Bool :=
  (List.range (b + 1)).all fun i =>
    if a ≤ i ∧ i ≤ b then decide (flowBracketBalance T a i ≥ 0) else true

/-- Decidable `bodySuccFact tokens a b`. -/
def bodySucc (a b : Nat) : Bool :=
  (List.range b).all fun k =>
    if a ≤ k ∧ k < b ∧ decide (flowBracketBalance T a (k + 1) = 0) ∧ !(T[k]!.val == .flowEntry)
    then (k + 1 == b) || (decide (k + 1 < b) && (T[k + 1]!.val == .flowEntry))
    else true

-- ════════════════════════ (L) token layout of `[[1], [2]]` ════════════════════════
#guard emit twoSibVal == "[[\"1\"], [\"2\"]]"
#guard T.size == 11
#guard T[1]!.val == .flowSequenceStart    -- outer `[`         (outer body [2,9))
#guard T[2]!.val == .flowSequenceStart    -- first inner `[`   (body [3,4))
#guard T[4]!.val == .flowSequenceEnd      -- first inner `]`
#guard T[5]!.val == .flowEntry            -- outer `,`
#guard T[6]!.val == .flowSequenceStart    -- second inner `[`  (body [7,8))
#guard T[8]!.val == .flowSequenceEnd      -- second inner `]`
#guard T[9]!.val == .flowSequenceEnd      -- outer `]`

-- ════════ (II) the cross-sibling window [3,7) — BARE gate passes, but carrier is FALSE ════════
#guard bareGated 3 7                       -- balance 3 7 = 0 ∧ seq-enclosed: bare gate HOLDS
#guard flowBracketBalance T 3 7 == 0
#guard (btFold (some []) (T.toList.take 3)).bind (·.head?) == some true
#guard !(bodySucc 3 7)                     -- ... yet bodySuccFact is FALSE on it
#guard T[3]!.val == .scalar "1" .doubleQuoted   -- the failing entry: depth-0-complete content...
#guard T[4]!.val == .flowSequenceEnd            -- ... followed by `]`, NOT a `.flowEntry`
-- the floor SEPARATES it: the window dips to -1 crossing the first sibling's close at index 4:
#guard flowBracketBalance T 3 5 == -1
#guard !(floored 3 7)                      -- floor VIOLATED ⇒ R313 gate rejects [3,7)

-- ════════ every gated bodySuccFact-FAILING window is exactly a floor-violator (floored ⟹ bsf) ════════
-- enumerate all bare-gated windows in the outer body [2,9); none that is floored fails bodySucc:
#guard (List.range 10).all fun a =>
  (List.range 10).all fun b =>
    if 2 ≤ a && a ≤ b && b ≤ 9 && bareGated a b && floored a b then bodySucc a b else true
-- and the bodySucc-failing bare-gated windows are all NON-floored (the cross-sibling set):
#guard (List.range 10).flatMap (fun a => (List.range 10).filterMap fun b =>
    if 2 ≤ a && a ≤ b && b ≤ 9 && bareGated a b && !(bodySucc a b) then some (a, b) else none)
  == [(3, 7), (3, 8), (4, 8)]
#guard ([(3, 7), (3, 8), (4, 8)] : List (Nat × Nat)).all fun ab => !(floored ab.1 ab.2)

-- ════════ the R313 gate `SeqTypedInterior` (now 3-conjunct) REJECTS [3,7) ════════
-- the third projection (the floor) is false at i = 5, so the full gate cannot hold:
#guard !decide (flowBracketBalance T 3 5 ≥ 0)   -- the floor conjunct `∀ i ∈ [3,7], balance 3 i ≥ 0` fails

-- ════════ (I) the predicted matching-close route over [p, size) is BROKEN on `[[1, 2], 9]` ════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]
-- inner `[` at p = 2; the next-step predicted `matching_close` with base 2 over [2, size=11):
#guard N[2]!.val == .flowSequenceStart
#guard flowBracketBalance N 2 11 == -1          -- h_total FAILS (not 0)
#guard flowBracketBalance N 2 10 == -1          -- the floor DIPS below 0 (fails h_dyck)
-- the CORRECT enclosing window is [p, hi) with hi = the enclosing recursion window end (here 9):
#guard flowBracketBalance N 2 9 == 0            -- balance p hi = 0 over the enclosing seq body
#guard (List.range 8).all fun i => if 2 ≤ i then decide (flowBracketBalance N 2 i ≥ 0) else true
#guard flowBracketBalance N 3 6 == 0            -- matching close found: j = 6, balance (p+1) j = 0
#guard N[6]!.val == .flowSequenceEnd            -- ... and it is a `]`

end L4YAML.Proofs.EmitterScannability.SeqGateFloorProbe
