module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The flow collection carries the stamp to its own close (DOCS item 103)

Items 101 and 102 refuted the `[189]` implicit value's frameless key at the
park its CONTENT makes (`k: a: 1`) and at the park a `[96]` PROPERTY RUN makes
(`k: &p a: 1`).  The third park in that slot is a closed flow collection, and
it kept deferring: `flowKeyPack_of_close` punted `noKeyContext` — the reason
that is about the CALLER and carries nothing — wherever item 56's frame had no
key route to hand.

What was missing is a TRANSPORT, and a long one.  The park a `]` makes is not
one step past the value indicator but a whole collection past it, and the datum
the refutation needs is a scanner field read at the close.  `scanValue` is
`implicitValueLine`'s only writer and it declines inside a flow (`[142]`'s `:`
is not `[194]`'s), so the field the open was dispatched under IS the field the
close is dispatched under — and `KmSound`'s base slot, which already carries
the open's key COLUMN across the interior (item 75), carries its stamp reading
with it.  The open records it by a `by_cases` on the saved key's own line, and
the close spends it: `k: [1]: 2` is refused for exactly the reason `k: a: 1`
is, one construct over. -/

namespace L4YAML.Tests.Guards.ScannerFlowCloseSameLineKey

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-- Refused by BOTH pipelines, and by the §8.2.2 check specifically — the error
    names the second value indicator's own position, which is what says the
    stamp is what fired rather than some other refusal. -/
private def stamped (input : String) (line col : Nat) : Bool :=
  ( (match Events.streamToEvents input with
     | .error (.nestedMappingOnLine l c) => some (l, c) | _ => none)
  , (match Events.streamToEventsIx input with
     | .error (.nestedMappingOnLine l c) => some (l, c) | _ => none) )
    == (some (line, col), some (line, col))

private def emitsOk (input : String) : Bool :=
  ( (Events.streamToEvents input).toOption.isSome
  , (Events.streamToEventsIx input).toOption.isSome ) == (true, true)

-- §1 The `:` at a closed collection's park, in a stamped value slot.  Both
-- brackets, empty and nested interiors, and the `s-separate-in-line?` the key
-- may carry before its own `:`.
#guard stamped "k: [1]: 2\n" 0 6
#guard stamped "k: {a: b}: 2\n" 0 9
#guard stamped "k: []: 2\n" 0 5
#guard stamped "k: {}: 2\n" 0 5
#guard stamped "k: [1] : 2\n" 0 7
#guard stamped "k: [[1]]: 2\n" 0 8
#guard stamped "k: [{a: b}]: 2\n" 0 11
-- The value that FOLLOWS the second indicator changes nothing — the refusal is
-- at the indicator, before anything is read after it.
#guard stamped "k: [1]:\n" 0 6
#guard stamped "k: [1]: 2: 3\n" 0 6

-- §2 Every other frame that opens a `[189]` value: the empty key, a sequence
-- entry's mapping, an explicit entry's compact mapping.
#guard stamped ": [1]: 2\n" 0 5
#guard stamped "- k: [1]: 2\n" 0 8
#guard stamped "? a: [1]: 2\n" 0 8

-- §3 …and the PROPS-decorated open, which is item 102's park opening item 56's
-- collection.  The props run needs no stamp field of its own: its `h_key`
-- already punts `implicitValue` in this slot, and that constructor's first
-- component IS the reading the flow open records.
#guard stamped "k: &p [1]: 2\n" 0 9
#guard stamped "k: !t {a: b}: 2\n" 0 12
#guard stamped "k: &p !t [1]: 2\n" 0 12

-- §4 The boundary, which must NOT move: the same collections keyed where no
-- value indicator stamped the line.
#guard emitsOk "[1]: 2\n"
#guard emitsOk "{a: b}: 2\n"
#guard emitsOk "- [1]: 2\n"
#guard emitsOk "k:\n  [1]: 2\n"
#guard emitsOk "&p [1]: 2\n"
#guard emitsOk "- &p [1]: 2\n"
#guard emitsOk "k:\n  &p [1]: 2\n"
-- The EXPLICIT value indicator leaves the field alone (`scanValue`'s
-- `explicitValue` arm), so the `?` frame's own value slot keeps its key.
#guard emitsOk "? [1]\n: 2\n"
#guard emitsOk "? [1]: 2\n"
#guard emitsOk "?\n: [1]: 2\n"
#guard emitsOk "? a\n: [1]: 2\n"
-- And the collection that is a VALUE and never a key, which is the same open
-- with nothing after the close.
#guard emits "k: [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "=VAL :1", "-SEQ", "-MAP",
   "-DOC", "-STR"]
-- An interior `:` is `[142]`'s, not `[194]`'s — the stamp neither fires inside
-- the collection nor is set by it.
#guard emits "k: [a: b]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "+SEQ []", "+MAP {}", "=VAL :a",
   "=VAL :b", "-MAP", "-SEQ", "-MAP", "-DOC", "-STR"]

-- §5a The transport, at its type: the two readings the base slot now carries,
-- and the step that records them.
open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- The mask's base slot answers the close's ~~two~~ three questions at once
    (item 300 adds the marker's line). -/
example {sc : ScannerState} {km : Array Bool} {kc : Nat}
    (h : KmSound sc km kc) (h1 : km.size = 1) :
    -- Item 520 (review round 2): the column alone — the stamp and the marker are decided at the close.
    ∃ key, sc.simpleKeyStack.back? = some key ∧ key.pos.col = kc :=
  KmSound.back_col h h1

-- Item 520 (review round 2): `flowOpen_stamp` is gone — the open records no stamp; the close
-- decides `sc.implicitValueLine = some sc.simpleKey.pos.line` on its own state
-- (`flowKeyPack_of_close`), and Priority 132 reads it: 13 / 251 corpus base opens.

-- §5b …and the reason the transport is possible at all: NOTHING between the
-- open and the close writes the field.  The five `example`s that stood here
-- (`scanValue_inFlow_implicitValueLine`, `scanFlow{Sequence}{Start,End}_preserves_implicitValueLine`,
-- `scanFlowEntry_` / `scanKey_preserves_implicitValueLine`) were deleted with the 23 preservation
-- lemmas on the owner's ruling (item 520's roster, 2026-11-17): the close DECIDES the stamp on its
-- own state (`flowKeyPack_of_close`), so no transport from the open is stated any more and the
-- preservation chain had no consumer (Rule 1).

-- §6 The residue this item does NOT take, pinned as measured: a collection
-- whose interior crossed a LINE is not a key at all, and the scanner says so
-- with its own refusal rather than §8.2.2's.
--
-- ~~Where no indicator stamped the line, `flowKeyPack_of_close` still has only
-- `noKeyContext` to name for it — the head's own `∨ True`.~~  Item 104 TOOK
-- these three, and located them one step earlier: the input never reaches the
-- head, because the pack's own guard — the saved key is on the park's line —
-- is FALSE for it, and §7.4's one-line key check refutes the branch above it.
-- See `ScannerStaleKeyColon`.
private def badKey (input : String) (line : Nat) : Bool :=
  ( (match Events.streamToEvents input with
     | .error (.invalidImplicitKey l) => some l | _ => none)
  , (match Events.streamToEventsIx input with
     | .error (.invalidImplicitKey l) => some l | _ => none) )
    == (some line, some line)

#guard badKey "[1,\n 2]: 3\n" 1
#guard badKey "k: [1,\n 2]: 3\n" 1
#guard badKey "- [1,\n  2]: 3\n" 1

end L4YAML.Tests.Guards.ScannerFlowCloseSameLineKey

end Blanket
