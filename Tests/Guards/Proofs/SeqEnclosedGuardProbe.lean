import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators

/-!
# `SeqEnclosed` guard edge-reconstruction probe (de-risk for `(i'-b-B3-enclosed-guard)`)

A CONCRETE-emitter probe, run BEFORE authoring the `SeqEnclosed` parallel guard and its
`seqEnclosed_descend` / `seqEnclosed_advance` preservation edges, per
`ref-probe-deferred-universal-before-producing`.

`SeqEnclosed tokens lo := (btFold (some []) (tokens.toList.take lo)).bind (·.head?) = some true` is the
single residual `G`-conjunct R320 named: the `lo`-keyed enclosing btFold-top fact that `SeqTypedInterior`
(the gate `seqWindow_flowBodyContent` consumes) needs and `FlowBodyWindow`/`Deep` do not carry.  The
producer `windowWidth_strongRecOn` step must carry it down BOTH recursion edges:

* **DESCEND** (inside `recseqentry_seqbracket_oracle`, NonemptyStructure.lean:3861): the window head
  `tokens[lo]` is a seq opener `[`, and the IH runs on the interior `[lo+1, j)`.  The de-risk's
  structural finding (option A): the oracle reconstructs `h_win'`/`h_deep'` at `[lo+1, j)` with the
  opener `lo` in scope, so a `SeqEnclosed (lo+1)` can be reconstructed AT the IH call site by pushing
  the `[`.  KEY asymmetry: pushing an opener OVERWRITES the stack head with `true` REGARDLESS of the
  parent's head — so the descend edge needs only that the parent fold is DEFINED, not that the parent is
  itself seq-enclosed.  (`SeqEnclosed lo` is the threaded hypothesis and supplies definedness.)

* **ADVANCE** (inside `recseqbody_window_assemble`, NonemptyStructure.lean:3121): after the first entry
  the tail `[m+1, hi)` recurses.  The segment `[lo, m+1)` (entry + depth-0 `.flowEntry` separator) is
  `WellTyped`, so by `btFold_frame` it returns the fold to the SAME stack — the head is PRESERVED.
  Contrast DESCEND: ADVANCE is a FRAME (parent-head-DEPENDENT, preserves), DESCEND is a PUSH
  (parent-head-BLIND, overwrites).

This probe confirms, on real `#guard`-backed emitter output, the btFold-top is `some true` at every
recursion window the producer visits, and that the two edges' arithmetic preconditions hold — BEFORE
authoring the fixpoint.  Plus a NEGATIVE: a map-enclosed window has btFold-top `some false ≠ some true`,
so `SeqEnclosed` correctly FAILS there (it is genuinely seq-specific, not a tautology).
-/

namespace L4YAML.Proofs.EmitterScannability.SeqEnclosedGuardProbe

open L4YAML
open L4YAML.Emit (emit)
open L4YAML.Scanner (scanFiltered)
open L4YAML.Proofs.ParserGrammable (flowBracketBalance flowBracketDelta)

def sc (c : String) : YamlValue := .scalar { content := c, style := .plain }

/-- The `SeqEnclosed` guard BODY: the head of the typed stack after the prefix `[0, lo)`. -/
def enclosingMark (T : Array (Positioned YamlToken)) (lo : Nat) : Option Bool :=
  (btFold (some []) (T.toList.take lo)).bind (·.head?)

/-- The typed-stack fold over the sub-window `[a, b)` from the empty stack (`= some []` iff `WellTyped`). -/
def segFold (T : Array (Positioned YamlToken)) (a b : Nat) : Option (List Bool) :=
  btFold (some []) ((T.toList.take b).drop a)

-- ════════════════════ Witness N := `[[1, 2], 9]` — DESCEND-AT-ROOT ════════════════════
def nestVal : YamlValue := .sequence .flow #[.sequence .flow #[sc "1", sc "2"], sc "9"]
def N : Array (Positioned YamlToken) :=
  match scanFiltered (emit nestVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:streamStart 1:[ 2:[ 3:"1" 4:, 5:"2" 6:] 7:, 8:"9" 9:] 10:streamEnd
#guard N.size == 11

-- (ROOT seed) the outer body window `[2, …)` is seq-enclosed by the outer `[` at position 1:
#guard enclosingMark N 2 == some true          -- SeqEnclosed N 2 (root seed of the guard)

-- (DESCEND edge 2 → 3) the window head `tokens[2] = [` is a seq opener; pushing it overwrites the head:
#guard N[2]!.val == .flowSequenceStart         -- the descend opener at lo = 2
#guard flowBracketDelta N[2]!.val == 1         -- opener delta (the push)
#guard enclosingMark N 3 == some true          -- SeqEnclosed N 3 (descend window [3, 6) start)
-- PUSH is parent-head-BLIND: the single-opener segment `[2, 3)` folds to a one-deeper stack regardless
#guard segFold N 2 3 == some [true]            -- one `[` pushed onto the empty base

-- ════════════════════ Witness T := `[1, [2, 3]]` — ADVANCE-THEN-DESCEND ════════════════════
def advVal : YamlValue := .sequence .flow #[sc "1", .sequence .flow #[sc "2", sc "3"]]
def T : Array (Positioned YamlToken) :=
  match scanFiltered (emit advVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:streamStart 1:[ 2:"1" 3:, 4:[ 5:"2" 6:, 7:"3" 8:] 9:] 10:streamEnd
#guard T.size == 11

-- (ROOT seed) the outer body window `[2, …)` is seq-enclosed:
#guard enclosingMark T 2 == some true          -- SeqEnclosed T 2

-- (ADVANCE edge 2 → 4) the first entry "1" + the depth-0 `.flowEntry` separator at 3:
#guard T[3]!.val == .flowEntry                 -- the separator m = 3
#guard flowBracketBalance T 2 4 == 0           -- balance lo (m+1) = 0 (depth-0 separator)
#guard segFold T 2 4 == some []                -- the advance segment `[2, 4)` = `["1", ,]` is WellTyped
#guard enclosingMark T 4 == some true          -- SeqEnclosed T 4 (advance tail [4, 9) start) — head PRESERVED

-- (DESCEND edge 4 → 5) the tail window head `tokens[4] = [` is a seq opener:
#guard T[4]!.val == .flowSequenceStart         -- the descend opener at lo = 4
#guard flowBracketDelta T[4]!.val == 1         -- opener delta (the push)
#guard enclosingMark T 5 == some true          -- SeqEnclosed T 5 (descend window [5, 8) start)
#guard segFold T 4 5 == some [true]            -- PUSH overwrites: one `[` onto the empty base

-- ════════════════════ NEGATIVE — a map-enclosed window FAILS `SeqEnclosed` ════════════════════
-- `{a: [1]}` : the map body is map-enclosed (`some false`), but the seq VALUE `[1]` body is still
-- seq-enclosed (`some true`) even though nested under a mapping — `SeqEnclosed` reads the IMMEDIATE
-- enclosing bracket, so it is genuinely seq-specific, not a tautology over every nested window.
def mapVal : YamlValue := .mapping .flow #[(sc "a", .sequence .flow #[sc "1"])]
def M : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapVal) with | .ok ts => ts | .error _ => #[]

-- layout: 0:streamStart 1:{ 2:key 3:"a" 4:value 5:[ 6:"1" 7:] 8:} 9:streamEnd
#guard M.size == 10
#guard M[1]!.val == .flowMappingStart          -- the enclosing `{`
#guard enclosingMark M 2 == some false         -- map-body window head: SeqEnclosed FAILS (some false)
#guard !(enclosingMark M 2 == some true)       -- explicitly: NOT seq-enclosed
#guard M[5]!.val == .flowSequenceStart         -- the seq value opener
#guard enclosingMark M 6 == some true          -- seq-value body IS seq-enclosed (immediate bracket = `[`)

end L4YAML.Proofs.EmitterScannability.SeqEnclosedGuardProbe
