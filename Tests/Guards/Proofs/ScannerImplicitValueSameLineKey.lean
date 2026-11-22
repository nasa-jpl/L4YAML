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

/-! # The implicit value's stamp reaches its own content's park (DOCS item 101)

Item 65 named `KeyPackPunt.noFrame` for a key on the park's own line with no
`[185] s-l+block-indented` compact alternative to close, and its guard
(`ScannerKeyPackPunt` §4) pinned the two shapes the name covered side by side:
`? a⏎: b: c` ACCEPTED and `k: a: 1` REFUSED.  One name, two behaviors — so the
name was covering two reasons, and item 101 splits it.

The refused half is `[189]`'s IMPLICIT value.  Its slot is `s-l+block-node`,
which has no compact alternative, so the pack really has no frame there; but
the value indicator that opened the slot STAMPED its line
(`implicitValueLine`), and §8.2.2 refuses a second value indicator on a
stamped line — the same check item 48 spent at the value indicator's own park,
one step later.  So `KeyPackPunt.implicitValue` carries the stamp and the
park's stale tail, and `colon_fires_implicit_key` refutes instead of deferring.

What makes the stamp spendable is that it SURVIVES the value's own content:
`scanValue` is the field's only writer, so the scalar and alias scans between
the indicator and the park leave it alone
(`dispatchContent_implicitValueLine`, §4 below), and a break-free landing
keeps the park on the stamped line.

The accepted half keeps the name: an EXPLICIT `:`'s value has no slot to hand
over either, and `?⏎: b: c` is legal — that one wants the `?` frame's own
value pack, not a refutation.  §3 pins it, so the split is machine-checked in
both directions rather than asserted here. -/

namespace L4YAML.Tests.Guards.ScannerImplicitValueSameLineKey

open L4YAML

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

/-- Refused by BOTH pipelines, and refused by the §8.2.2 check specifically —
    the error names the second value indicator's own position, which is what
    says the stamp is what fired. -/
private def stamped (input : String) (line col : Nat) : Bool :=
  ( (match Events.streamToEvents input with
     | .error (.nestedMappingOnLine l c) => some (l, c) | _ => none)
  , (match Events.streamToEventsIx input with
     | .error (.nestedMappingOnLine l c) => some (l, c) | _ => none) )
    == (some (line, col), some (line, col))

private def emitsOk (input : String) : Bool :=
  ( (Events.streamToEvents input).toOption.isSome
  , (Events.streamToEventsIx input).toOption.isSome ) == (true, true)

-- §1 The refuted half: an implicit value's own content, then a `:` on its
-- line.  Every scalar head the content dispatch accepts, at every frame that
-- opens an implicit value.
-- The plain scalar, glued and spaced.
#guard stamped "k: a: 1\n" 0 4
#guard stamped "k: a : 1\n" 0 5
-- The two quoted heads.
#guard stamped "k: \"a\" : b\n" 0 7
#guard stamped "k: 'a' : b\n" 0 7
-- An INDENTED value slot, and one inside a sequence entry.
#guard stamped "k:\n  m: a: 1\n" 1 6
#guard stamped "- k: a: 1\n" 0 6
#guard stamped "-\n  k: a: 1\n" 1 6
-- The col-0 EMPTY-key entry (`[189]`'s other alternative) stamps the same way.
#guard stamped ": a: 1\n" 0 3
#guard stamped ": \"a\" : b\n" 0 6
-- …and so does the implicit value INSIDE an explicit entry's compact mapping,
-- which is where `? a: b: c` parts from `?⏎: b: c` below.
#guard stamped "? a: b: c\n" 0 6
#guard stamped "- a: b: c\n" 0 6

-- §2 The boundary, which must NOT move: the same parks with no second `:`.
#guard emits "k: a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard emits "k: \"a\"\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL \"a", "-MAP", "-DOC", "-STR"]
#guard emits ": a\n"
  ["+STR", "+DOC", "+MAP", "=VAL :", "=VAL :a", "-MAP", "-DOC", "-STR"]
#guard emits "? a: b\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "=VAL :",
   "-MAP", "-DOC", "-STR"]
#guard emits "- a: 1\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :1", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- A `:` on the NEXT line is a sibling entry, not a second indicator.
#guard emits "k: a\nj: b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL :a", "=VAL :j", "=VAL :b", "-MAP",
   "-DOC", "-STR"]

-- §3 The half that KEEPS the name, pinned as accepted so the split is checked
-- in both directions: an EXPLICIT `:`'s value has no compact slot either, and
-- its line carries no implicit stamp.
#guard emitsOk "?\n: b: c\n"
#guard emitsOk "? a\n: b: c\n"
#guard emitsOk "?\n: \"b\" : c\n"
#guard emitsOk "? a\n: [1] : c\n"
#guard emitsOk "k:\n  ?\n  : b: c\n"
-- …and the props twin, which rides `noKeyContext` and is untouched here.
#guard emitsOk "?\n: &p a: 1\n"
-- Its IMPLICIT sibling is refused by the same stamp, which is what says the
-- discriminator is the value indicator's kind and not the property run.
#guard stamped "k: &p a: 1\n" 0 7

-- §4 The transport, at its type: the fact that makes the reason spendable at
-- the `:` a step later.  `scanValue` is `implicitValueLine`'s only writer, so
-- NO content scan touches the stamp — item 103 totalized the walk, and the
-- head-restricted readings items 101 and 102 proved are this one at a head.
open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- The stamp survives the implicit value's own content, at every head. -/
example {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.implicitValueLine = s.implicitValueLine :=
  dispatchContent_implicitValueLine hok

open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- …and the punt that spends it names every half of what it carries.  Item
    102 widened the carrier from `StaleNodeTail` to the three flags the
    refutations actually read (`StalePark`) and added the saved key's line,
    which is what a property park needs in order to hand the same reason on;
    a value park still projects into it. -/
example {sc : ScannerState} (h_ivl : sc.implicitValueLine = some sc.line)
    (h_kline : sc.simpleKey.pos.line = sc.line)
    (h_st : StaleNodeTail sc) : KeyPackPunt sc :=
  KeyPackPunt.implicitValue h_ivl h_kline h_st.toStalePark

end L4YAML.Tests.Guards.ScannerImplicitValueSameLineKey

end Blanket
