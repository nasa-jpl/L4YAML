module

public import L4YAML.Scanner.Scanner
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The park face, and `KeyPackPunt.noFrame`'s deletion (DOCS item 125)

U2 of the under-indent map (`UnderIndentInvariantMap`) asked for the park's
`?`-frame face as a mandatory conditional field on `explicitKeyLine`.  What
the item MEASURED is one construct over, and cheaper: the coupling is not a
park field at all.

* `pendingMapValue.h_ivl` is stamp-or-FACE — the right disjunct is the same
  `[185] s-l+block-indented` slot `h_vslot` already carries.  Every producer
  pays one side outright: the `?` openers (landed and compact) and the
  explicit `:` hand the face they hand `h_vslot`; the four implicit `:`
  producers hand a REAL stamp.
* The stamp is real because the landed-`:` CONSUMERS decide it: a `:` whose
  dispatch state has no live `explicitKeyLine`, or stands off `explicitKeyCol`,
  computed `explicitValue = false` and stamped (item 124's two line-free
  discriminators, joined as `scanValue_stamp_of_src`); a `:` that RESOLVES a
  key stamps whatever the register holds (`scanValue_stamp_of_key`).
* So the pack lemmas' same-line branch is total: frame from `h_compact`, or
  face from the field, or stamp.  `KeyPackPunt.noFrame` — the reason with no
  named input since item 105 — is GONE, and with it the third of the five
  arms every punt consumer had to carry.

What is NOT closed, and is stated here so the next reader does not re-derive
it: a landed `:` under a live register at the `:`'s own column, with no pack
at that column to pay the explicit route with.  `? [a]⏎: b: c` is such an
input: ACCEPTED by the scanner, and on the proof side the same escape it took
before this item, now reached by an undecided source rather than by a punt.
§3 pins that boundary.

**Correction (item 126).**  The two lines above named that residue "the
COLLAPSE lane" and attributed it to `FlowStackB.shape` — a flow collection
that renounced its grammar reading, restoring the scanner's register pair at
a close the surface side kept no face for.  There is no such lane: item 126
measured the collapse constructor UNREACHABLE (every construction of one
consumed one) and deleted it, and these inputs ride the real flow lane, whose
value slot the open pays and the close converts.  The boundary is the state
named above; the story about how it is reached was wrong.  See
`CollapseLaneDeleted`.

§1 pins the field's two shapes and the deletion; §2 the consumer's own
discriminator; §3 the accepted/refused families on both pipelines. -/

namespace L4YAML.Tests.Guards.ParkFaceCoupling

open L4YAML L4YAML.Scanner L4YAML.Surface

/-! ## §1  The field, and what the constructor no longer has

`KeyPackPunt` has ~~FOUR~~ ~~THREE~~ FOUR reasons (item 300 adds `markerLine`).  A
`match` that covers them is total, which is what pins the deletions: were
`noFrame` (item 125) or `dedent` (item 297) still there, this would not
elaborate.  (Item 289: `tab` has four fields
— the saved key's possibility and line beside the scan's reading and the
park's flags.) -/

example {sc : ScannerState} (h : L4YAML.Proofs.StreamAccum.KeyPackPunt sc) : True :=
  match h with
  | .tab _ _ _ _ => trivial
  | .implicitValue _ _ _ => trivial
  | .markerLine _ _ => trivial
  | .noKeyContext => trivial

-- The field's landed type, read off the constructor itself: a `pendingMapValue`
-- hands stamp-or-FACE, and the face is the park's own `[185]` value slot.  The
-- `have`'s explicit type is the pin — either disjunct changing breaks it.
example {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}
    (h : L4YAML.Proofs.StreamAccum.PendingNode sc false sp_start sp_block sp_scan) :
    True := by
  cases h with
  | pendingMapValue _ _ _ n _ _ _ _ _ h_ivl =>
    have : sc.implicitValueLine = some sc.line ∨
        (sp_scan.col = n + 1 ∧ ∀ sp_v : SurfPos,
          SBlockIndented n .blockOut sp_scan sp_v → SLYamlStream sp_start sp_v) := h_ivl
    trivial
  | _ => trivial

/-! ## §2  The consumer's own discriminator

The landed `:` reads its dispatch state, not the park: no live register, a
saved key that SURVIVES the clear, or a column that differs, means the
epilogue stamped.

**Item 185 widened this to three alternatives.**  `explicitValue` is a
conjunction of three tests and item 125 read the first and the third, which
left the consumers' branch weaker than `explicitValue = true` and so unable to
spend the reading it named.  The middle alternative is a field of the same
state, decidable there like the others, so the split is now TOTAL: its negation
is exactly `explicitValue = true`. -/

example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s.inFlow = false → s.peek? = some ':' →
    (s.explicitKeyLine = none ∨
      (scanValueClearKey s).simpleKey.possible = true ∨
      (s.col : Int) ≠ s.explicitKeyCol) →
    s'.implicitValueLine = some s'.line :=
  fun h1 h2 h3 h4 => L4YAML.Proofs.StreamAccum.scanValue_stamp_of_src h1 h2 h3 h4

/-- …and the third alternative on its own, which is what makes it total. -/
example : ∀ {s s' : ScannerState},
    scanValue s = .ok s' → s.inFlow = false → s.peek? = some ':' →
    (scanValueClearKey s).simpleKey.possible = true →
    s'.implicitValueLine = some s'.line :=
  fun h1 h2 h3 h4 =>
    L4YAML.Proofs.ExplicitKeyCoupling.scanValue_stamp_of_cleared_key h1 h2 h3 h4

/-! ## §3  The families, on both pipelines -/

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def accepts (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .ok _, .ok _ => true
  | _, _ => false

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- The face payers: a `?` frame's key slot and an explicit `:`'s value slot,
-- both same-line and across a break.  These are what the field's right
-- disjunct carries, and what the pack lemmas' same-line branch composes
-- through instead of punting.
#guard accepts "? a: b\n"
#guard accepts "?\n: b: c\n"
#guard accepts "? a\n: b: c\n"
#guard accepts "- ? a: b\n"
#guard accepts "? &p a: 1\n"
#guard accepts "?\n: &p a: 1\n"

-- The stamp payers: a `[189]` implicit value whose slot has no compact
-- alternative — the second value indicator on a stamped line is REFUSED, and
-- that refusal is what the field's left disjunct records.
#guard refuses "k: a: 1\n"
#guard refuses "k: &p a: 1\n"

-- The keyed `:` under a live `?` register stamps for the OTHER reason (the
-- resolved key), which is what `colon_open_map_implicit`/`_props` pay with.
#guard emits "? earth: blue\n: moon: white\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :earth", "=VAL :blue", "-MAP",
   "+MAP", "=VAL :moon", "=VAL :white", "-MAP", "-MAP", "-DOC", "-STR"]

-- The residue, pinned as a BOUNDARY rather than a claim: the scanner accepts
-- these, and the proof side reaches them with an undecided stamp source and
-- defers.  (Item 126: the reason given here for the deferral — a collapsed
-- flow stack — was wrong; the inputs themselves are unchanged, and
-- `CollapseLaneDeleted` §3 pins their events.)
#guard accepts "? [a]\n: b: c\n"
#guard accepts "? {x: y}\n: b: c\n"

-- …and the same shapes WITHOUT the collapse, which compose today.
#guard accepts "? [a]\n: v\n"
#guard accepts "? a\n: v\n"

end L4YAML.Tests.Guards.ParkFaceCoupling

end Blanket
