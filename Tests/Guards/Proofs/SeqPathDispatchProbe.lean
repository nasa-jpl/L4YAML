import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# PATH-dispatch discriminator probe (de-risk for the R335-reshaped driver)

A `ref-minimal-pair-extracts-the-gate` PROBE *over the PATH* (not the window), to settle the
discriminator that partitions `desc`'s gated seq windows into

* **ALL-SEQ-PATH** — every bracket frame from the root down to the window's opener is a seq (`[`),
  so the window's `RecSeqBody` is reachable by root-`RecSeqBody`-navigation (servable by the
  domain-restricted `rec_seq_body_nested_project` driver);
* **MAP-PATH-NESTED** — some frame below the window's immediate `[` is a map (`{`), so the window's
  `RecSeqBody` is buried in a `RecSeqEntry.map`'s `WellBracketed` (the SEVERED edge of R335) and is
  unreachable by navigation — servable only from the FLAT substrate.

The R335 probe (`SeqMapPathNestedProbe`) refuted the driver's totality.  This probe identifies the
DISPATCH predicate — read off real `#guard`-backed output, not invented — by a minimal pair:

* `[{a:[b]}]` (`M`) — the gated SEQ-typed window `[7, 8)`, reached THROUGH the `{` map entry;
* `[[[1, 2]]]` (`D`) — the gated SEQ-typed window `[4, 7)`, reached through `[` seq entries only.

Three candidate discriminators were on the table.  The probe DECIDES between them on the pair:

1. **Root-base balance** `flowBracketBalance tokens 2 a` — `2` for BOTH windows.  Does NOT separate
   (it is the very path-blindness the gate suffers): REJECTED.
2. **Typed-bracket-stack TYPE history** at the opener — the full `btFold` stack after `take a`:
   `[true, false, true]` for the map-path window (a `false`/map frame below the top `true`) vs
   `[true, true, true]` for the all-seq window.  The "stack is ALL `true`" predicate (`pathAllSeq`)
   is `false` vs `true`: SEPARATES.  This is the dispatch predicate.
3. `RecSeqBody`-reachability directly — not a `Bool` of the token stream; candidate 2 is its
   decidable proxy.

Triple duty (per `ref-minimal-pair-extracts-the-gate`): confirms the typed-stack predicate is
SUFFICIENT (all-seq window passes), proves it NECESSARY (the cheaper balance discriminator collapses
the pair to one value), and NAMES it as the existing `btFold` computation that separates the pair —
the map frame buried in the stack IS the discriminator, read off not invented.
-/

namespace L4YAML.Proofs.EmitterScannability.SeqPathDispatchProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)
open L4YAML.Proofs.EmitterScannability (btFold)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The seq-vs-map mark read off `btFold`: head (TOP) of the typed stack after the prefix `[0, a)`.
    This is the gate's IMMEDIATE-enclosure conjunct — path-BLIND (it sees only the top frame). -/
def enclosingMark (T : Array (Positioned YamlToken)) (a : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take a)).bind (·.head?)

/-- The PATH-dispatch predicate: the FULL typed stack at the opener is all-`true` (all-seq path).
    `none` (malformed prefix) and any `false`/map frame both yield `false`. -/
def pathAllSeq (T : Array (Positioned YamlToken)) (a : Nat) : Bool :=
  match btFold (some []) (T.toList.take a) with
  | some stack => stack.all (· == true)
  | none       => false

-- ════════════════════ Map-path witness  M := `[{a:[b]}]` ════════════════════
def mapVal : YamlValue :=
  .sequence .flow #[.mapping .flow #[(sc "a", .sequence .flow #[sc "b"])]]
def M : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:{ 3:key 4:"a" 5:value 6:[ 7:"b" 8:] 9:} 10:] 11:SE
#guard M.size == 12
-- the window `[7, 8)` is gated SEQ-typed (immediate enclosure is a seq — path-blind gate passes):
#guard flowBracketBalance M 7 8 == 0
#guard enclosingMark M 7 == some true
-- …yet its PATH crosses a map: the full typed stack has a `false` frame below the top `true`.
#guard pathAllSeq M 7 == false
-- the dispatch routes this window to the FLAT map-path provider, NOT the navigator.

-- ════════════════════ All-seq witness  D := `[[[1, 2]]]` ════════════════════
def deepVal : YamlValue :=
  .sequence .flow #[.sequence .flow #[.sequence .flow #[sc "1", sc "2"]]]
def D : Array (Positioned YamlToken) :=
  match scanFiltered (emit deepVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:SS 1:[ 2:[ 3:[ 4:"1" 5:, 6:"2" 7:] 8:] 9:] 10:SE
#guard D.size == 11
-- the window `[4, 7)` is gated SEQ-typed, same immediate enclosure as M's window:
#guard flowBracketBalance D 4 7 == 0
#guard enclosingMark D 4 == some true
-- …and its PATH is all-seq: every stack frame is `true`.
#guard pathAllSeq D 4 == true
-- the dispatch routes this window to the root-`RecSeqBody` NAVIGATOR.

-- ════════════════════ The minimal pair DECIDES the discriminator ════════════════════
-- NECESSITY — the cheaper root-base balance discriminator COLLAPSES the pair to one value (`2`),
-- so it cannot separate map-path from all-seq.  (This is the path-blindness of `SeqTypedInterior`.)
#guard flowBracketBalance M 2 7 == 2
#guard flowBracketBalance D 2 4 == 2
#guard flowBracketBalance M 2 7 == flowBracketBalance D 2 4

-- SUFFICIENCY + NAMING — the typed-stack predicate SEPARATES the pair, and the separating feature
-- is exactly the buried map frame (`false`) the balance discriminator cannot see.
#guard pathAllSeq M 7 == false
#guard pathAllSeq D 4 == true
#guard !(pathAllSeq M 7 == pathAllSeq D 4)

-- the opener heads confirm the structural reading: M's window is reached through a `{` (delta +1 but
-- NOT a `.flowSequenceStart`), D's through a `[`.
#guard M[2]!.val == .flowMappingStart
#guard flowBracketDelta M[2]!.val == 1
#guard decide (M[2]!.val ≠ .flowSequenceStart)
#guard D[2]!.val == .flowSequenceStart

end L4YAML.Proofs.EmitterScannability.SeqPathDispatchProbe
