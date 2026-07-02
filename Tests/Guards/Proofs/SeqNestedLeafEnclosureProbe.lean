import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# Emission-spine-walk locator WRAPPER — the LEAF map-exclusion is keyed to the TARGET WINDOW, not the base

The PROBE the blueprint queued after R354, sharpening the wrapper interface BEFORE authoring
`nestedSeq_recseqentry_locate`.  R354 settled the wrapper's *recursion-domain* hypothesis is the
WHOLE-path `SeqPathAllSeq tokens off` (carried at the body base `off`, threaded by the descend arm),
not the top-projection `SeqEnclosed tokens off`.  The blueprint then claimed the interface "RESOLVED"
and attributed the LEAF arm's head-is-`.seq` requirement to that same carried hypothesis: *"from
`SeqPathAllSeq` the opener `tokens[off]!` is `.flowSequenceStart`"*.

THE FINDING — that attribution is IMPRECISE, and the carried-state list is INCOMPLETE.  The navigator's
two arms read their exclusion facts at TWO DIFFERENT POSITIONS:

* the DESCEND **domain** lives at the body BASE `off` — `SeqPathAllSeq tokens off` (carried/threaded);
* the LEAF **head classification** lives at the TARGET WINDOW START `a = off+1` — it needs
  `SeqEnclosed tokens a`, the immediate enclosure of the window, which is the push of the head entry's
  OWN opener `tokens[off]`.

`SeqPathAllSeq tokens off` is BLIND to `tokens[off]` (it constrains only the stack BEFORE `off`, the
path enclosing the body), so it cannot decide whether the head entry is a `[` (seq, leaf admissible) or
a `{` (map, leaf inadmissible — `RecSeqEntry.map` has no `h_rec`, and the deliverable demands
`op.val = .flowSequenceStart`).  Only the window's own `SeqEnclosed tokens a` — the second conjunct of
the `SeqTypedInterior tokens a b` that `desc` consumes — separates them.  So the WRAPPER MUST ALSO
CONSUME the target window's `SeqTypedInterior tokens a b` (for the LEAF map-exclusion via `SeqEnclosed`,
and for the balance-0 that pins `b` to the head entry's far edge); the carried `SeqPathAllSeq tokens off`
alone does NOT close the LEAF arm.

THE MINIMAL PAIR (real emitted tokens) — the SAME body base `off = 2`, the SAME would-be leaf window
start `a = off+1 = 3`, differing only in the head entry's bracket TYPE:

* POSITIVE `[[1,2]]`     — root body head entry is a SEQ `[1,2]` (opener at 2).  `SeqEnclosed 3 = true`.
* NEGATIVE `[{x:[1,2]}]` — root body head entry is a MAP `{x:[1,2]}` (opener at 2).  `SeqEnclosed 3 = false`.

They AGREE on the carried base domain (`SeqPathAllSeq tokens 2 = true` for BOTH — the path to the body
base is the lone root `[`), but DISAGREE on the window enclosure (`SeqEnclosed tokens 3`: `true` vs
`false`).  So the carried `SeqPathAllSeq tokens off` cannot exclude the map-headed leaf; the window's
`SeqEnclosed tokens a` is the discriminator.  See Reflection 355.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqNestedLeafEnclosureProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.EmitterScannability (btFold btStep)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- `SeqEnclosed`-style TOP-of-stack projection (the immediate enclosure of position `a`). -/
def topTrue (tokens : Array (Positioned YamlToken)) (a : Nat) : Bool :=
  match (btFold (some []) (tokens.toList.take a)).bind (·.head?) with | some true => true | _ => false

/-- `SeqPathAllSeq`-style WHOLE-path projection (every enclosing frame of position `a` a seq). -/
def allTrue (tokens : Array (Positioned YamlToken)) (a : Nat) : Bool :=
  match btFold (some []) (tokens.toList.take a) with
  | some s => !s.isEmpty && s.all (· == true) | none => false

-- ════════════ NEGATIVE N := `[{x:[1,2]}]` — root body head entry is a MAP ════════════
def Nval : YamlValue := .sequence .flow #[.mapping .flow #[(sc "x", .sequence .flow #[sc "1", sc "2"])]]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit Nval) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:x 5:value 6:[ 7:"1" 8:, 9:"2" 10:] 11:} 12:] 13:SE
-- root body base off = 2; head entry {x:[1,2]} spans [2,11] (L = 10); would-be leaf window a = off+1 = 3.
#guard N.size == 14
#guard N[2]!.val == .flowMappingStart        -- head entry of the root body is a MAP opener
-- the carried base domain HOLDS (path to off = 2 is the lone root `[`):
#guard allTrue N 2 == true                    -- SeqPathAllSeq tokens 2   (stack [true])
-- yet the would-be leaf window's OWN enclosure FAILS (the map opener at 2 pushes a `false`):
#guard topTrue N 3 == false                   -- SeqEnclosed tokens 3   (stack [false,true], top false)
#guard allTrue N 2 != topTrue N 3             -- carried base domain ≠ window enclosure on the map head

-- ════════════ POSITIVE P := `[[1,2]]` — root body head entry is a SEQ ════════════
def Pval : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"]]
def P : Array (Positioned YamlToken) :=
  match scanFiltered (emit Pval) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:] 8:SE ; off = 2, a = off+1 = 3.
#guard P.size == 9
#guard P[2]!.val == .flowSequenceStart        -- head entry of the root body is a SEQ opener
#guard allTrue P 2 == true                     -- SeqPathAllSeq tokens 2 holds
#guard topTrue P 3 == true                     -- SeqEnclosed tokens 3 HOLDS (seq opener pushes true)

-- ════════════ THE MINIMAL PAIR: carried base domain EQUAL, window enclosure SEPARATES ════════════
#guard allTrue P 2 == allTrue N 2              -- SeqPathAllSeq tokens off — EQUAL across the pair
#guard topTrue P 3 != topTrue N 3              -- SeqEnclosed tokens a    — SEPARATES seq head / map head

end L4YAML.Proofs.EmitterScannability.SeqNestedLeafEnclosureProbe
