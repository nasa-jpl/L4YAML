import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Descent-`provider` satisfiability probe (de-risk for `(i'-b-descent-assembly)`)

A CONCRETE-emitter probe, run BEFORE authoring `seqDescent_provider_of_located` (brick (5), the
descent assembly), per `ref-probe-provider-satisfiable-before-assembler`.  The brick LIFTS the
recursion-supplied facts as hypotheses (option A, the [[ref-parametric-assembler-extraction]] cut)
and chains the landed bricks (opener-type → generic matching-close → typed close → child
`SafeBodyUnit` → `seqEnclosingFacts_provider_of_located`) to produce the provider existential at a
nested gated window.  The residual it isolates is the recursion driver that SOURCES those lifted
hypotheses (locate `p`, supply the enclosing window `[p, hi)` facts + the IH).

This probe confirms the lifted hypotheses are **satisfiable** at a nested gated window — so the
assembler is not vacuous — on TWO witnesses that exercise the two ways the residual driver reaches
the innermost enclosing opener `p`:

* `[[1, 2], 9]` — DESCEND-AT-ROOT: the gated window `[3, 6)`'s enclosing opener `p = 2` IS the head
  of the outer body window `[2, 9)`;
* `[1, [2, 3]]` — ADVANCE-THEN-DESCEND: the gated window `[5, 8)`'s enclosing opener `p = 4` is NOT
  the outer body head (`tokens[2] = "1"` is a content scalar), so the driver must ADVANCE past the
  first entry before the enclosing opener becomes the window head `[4, 9)`.

The KEY facts the brick lifts and chains (sourced from the parent recursion step):

* the enclosing window `[p, hi)` is a `FlowBodyWindow` — `flowBracketBalance tokens p hi = 0` AND the
  window Dyck floor `∀ i ∈ [p, hi], balance p i ≥ 0` — with `hi` the OUTER body end (NOT the matching
  close `j`, so `j < hi` strictly);
* the located-opener facts at the gated window start `a`: `flowBracketDelta tokens[p]! = 1`,
  `balance (p+1) a = 0`, the locator floor `∀ i ∈ (p, a], balance (p+1) i ≥ 0`;
* the generic matching-close at `p` over `[p, hi)` returns `j` with `j < hi`, `balance (p+1) j = 0`,
  AND the interior floor `∀ i ∈ (p, j], balance p i ≥ 1` (the `≥ 1` floor that brick (3)'s
  seq-specialized locator DROPS but `seqChild_safeBodyUnit` needs).
-/

namespace L4YAML.Proofs.EmitterScannability.SeqDescentProviderProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The seq-vs-map mark read off `btFold`: head of the typed stack after the prefix `[0, a)`. -/
def enclosingMark (T : Array (Positioned YamlToken)) (a : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take a)).bind (·.head?)

-- ════════════════════ Witness N := `[[1, 2], 9]` — DESCEND-AT-ROOT ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:SE
-- gated window [a,b) = [3, 6); enclosing opener p = 2; enclosing window [p, hi) = [2, 9); close j = 6.
#guard N.size == 11
#guard N[1]!.val == .flowSequenceStart        -- outer `[`
#guard N[2]!.val == .flowSequenceStart        -- enclosing opener p = 2 (= outer body head)
#guard N[6]!.val == .flowSequenceEnd          -- matching close j = 6

-- (gate) the gated window [3, 6) is NESTED (root discriminator `balance 2 a` fails):
#guard flowBracketBalance N 3 6 == 0          -- balance a b = 0
#guard enclosingMark N 3 == some true         -- enclosing mark (seq)
#guard flowBracketBalance N 2 3 == 1          -- NESTED: balance 2 a ≠ 0 (root seed does NOT apply)

-- (enclosing window [p, hi) = [2, 9) is a FlowBodyWindow) — with hi the OUTER body end:
#guard flowBracketBalance N 2 9 == 0          -- balanced
#guard (List.range 8).all fun i =>            -- window Dyck floor ≥ 0 over [2, 9]
  let t := i + 2; if t ≤ 9 then decide (flowBracketBalance N 2 t ≥ 0) else true

-- (located-opener facts at a = 3):
#guard flowBracketDelta N[2]!.val == 1        -- opener delta
#guard flowBracketBalance N 3 3 == 0          -- balance (p+1) a = 0
#guard decide (flowBracketBalance N 3 3 ≥ 0)  -- locator floor over (2, 3] (single point i = 3)

-- (generic matching-close at p = 2 over [2, 9): j = 6 < hi = 9, interior floor ≥ 1 over (2, 6]):
#guard decide (6 < 9)                          -- j < hi (strictly inside the enclosing window)
#guard flowBracketBalance N 3 6 == 0          -- balance (p+1) j = 0
#guard (List.range 7).all fun i =>            -- interior floor ≥ 1 over (2, 6]
  if 2 < i then decide (flowBracketBalance N 2 i ≥ 1) else true
-- (bounds the floor relay delivers): a ≤ j ∧ b ≤ j
#guard decide (3 ≤ 6) && decide (6 ≤ 6)

-- ════════════════════ Witness T := `[1, [2, 3]]` — ADVANCE-THEN-DESCEND ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:SE
-- gated window [a,b) = [5, 8); enclosing opener p = 4; enclosing window [p, hi) = [4, 9); close j = 8.
#guard T.size == 11
#guard flowBracketDelta T[2]!.val == 0        -- outer body HEAD is content (delta 0, NOT an opener)
#guard T[4]!.val == .flowSequenceStart        -- enclosing opener p = 4 (≠ outer head ⇒ advance first)
#guard T[8]!.val == .flowSequenceEnd          -- matching close j = 8

-- (gate) the gated window [5, 8) is NESTED:
#guard flowBracketBalance T 5 8 == 0          -- balance a b = 0
#guard enclosingMark T 5 == some true         -- enclosing mark (seq)
#guard flowBracketBalance T 2 5 == 1          -- NESTED (root discriminator fails at a = 5)

-- (the advance is necessary: the enclosing opener p = 4 is NOT the outer body head at lo = 2):
#guard flowBracketBalance T 2 4 == 0          -- advancing past entry "1" + `,` reaches depth 0 at p = 4
#guard T[3]!.val == .flowEntry                -- the separator the advance steps over

-- (enclosing window [p, hi) = [4, 9) is a FlowBodyWindow — the ADVANCE-tail window):
#guard flowBracketBalance T 4 9 == 0          -- balanced
#guard (List.range 6).all fun i =>            -- window Dyck floor ≥ 0 over [4, 9]
  let t := i + 4; if t ≤ 9 then decide (flowBracketBalance T 4 t ≥ 0) else true

-- (located-opener facts at a = 5):
#guard flowBracketDelta T[4]!.val == 1        -- opener delta
#guard flowBracketBalance T 5 5 == 0          -- balance (p+1) a = 0

-- (generic matching-close at p = 4 over [4, 9): j = 8 < hi = 9, interior floor ≥ 1 over (4, 8]):
#guard decide (8 < 9)                          -- j < hi
#guard flowBracketBalance T 5 8 == 0          -- balance (p+1) j = 0
#guard (List.range 9).all fun i =>            -- interior floor ≥ 1 over (4, 8]
  if 4 < i then decide (flowBracketBalance T 4 i ≥ 1) else true
#guard decide (5 ≤ 8) && decide (8 ≤ 8)       -- a ≤ j ∧ b ≤ j

end L4YAML.Proofs.EmitterScannability.SeqDescentProviderProbe
