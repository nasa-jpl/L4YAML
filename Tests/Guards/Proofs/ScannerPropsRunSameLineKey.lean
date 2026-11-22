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

/-! # The property run's park hands the stamp on (DOCS item 102)

Item 101 refuted the `[189]` implicit value's frameless key at the value's own
content park (`k: a: 1`).  Its props twin measured the same refusal and kept
deferring: `entryPropsKeyPack_of_dispatch` returned `PropsKeyPack ∨ True`, so a
run parked in that same value slot had no reason to name.

What stood in the way was the CARRIER, not the reasoning.  `KeyPackPunt`'s two
refutable reasons carried `StaleNodeTail`, whose fourth conjunct says the last
real token COMPLETES a value — and `[96] c-ns-properties` tokens are excluded
from `completesFlowValue` by construction, so no property park has one (§4a
below pins that).  The refutations read three of the four conjuncts.  Typed as
what they read (`StalePark`), the same two reasons serve a value park and a
property park alike, and every one of the props producer's punt branches gets
a name.

The reason then has to TRAVEL, because a run parks before its content:
`k: &p a: 1`'s `:` meets the park the *scalar* made, two steps after the value
indicator that stamped the line.  `keyPackPunt_transport` is that step, and it
is used at both moves — the run's own EXTENSION (`&p !t`) and the run's
CONTENT — which is why `k: !t &p a: 1` is refused wherever `k: a: 1` is. -/

namespace L4YAML.Tests.Guards.ScannerPropsRunSameLineKey

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

/-- Refused by BOTH pipelines at the `:`'s own backward tab scan
    (`scanValueIndentTabCheck`, items 31/32/65), positioned at the tab. -/
private def tabbed (input : String) (line col : Nat) : Bool :=
  ( (match Events.streamToEvents input with
     | .error (.tabInIndentation l c) => some (l, c) | _ => none)
  , (match Events.streamToEventsIx input with
     | .error (.tabInIndentation l c) => some (l, c) | _ => none) )
    == (some (line, col), some (line, col))

private def emitsOk (input : String) : Bool :=
  ( (Events.streamToEvents input).toOption.isSome
  , (Events.streamToEventsIx input).toOption.isSome ) == (true, true)

-- §1 The `:` at the RUN's own park — `colon_fires_props_key`'s share.  The run
-- is `[161]`'s props-only node read as `[193]`'s implicit key (item 49's
-- `&a : b`), and in a stamped value slot that key's `:` is a second indicator.
#guard stamped "k: &p : 1\n" 0 6
#guard stamped "k: !!str : 1\n" 0 9
#guard stamped "k: &p !t : 1\n" 0 9

-- §2 The `:` at the run's CONTENT park — the transport's share.  Every head
-- the content dispatch reads as a key, at every frame that opens an implicit
-- value, with the run in one half and in both.
#guard stamped "k: &p a: 1\n" 0 7
#guard stamped "k: !t a: 1\n" 0 7
#guard stamped "k: &p \"a\" : b\n" 0 10
#guard stamped "k: &p 'a' : b\n" 0 10
-- Both extension orders, which is the run's second move.
#guard stamped "k: &p !t a: 1\n" 0 10
#guard stamped "k: !t &p a: 1\n" 0 10
-- The other frames that open a `[189]` value: the empty key, a sequence
-- entry's mapping, an explicit entry's compact mapping.
#guard stamped ": &p a: 1\n" 0 6
#guard stamped "- k: &p a: 1\n" 0 9
#guard stamped "? a: &p b: c\n" 0 9
-- A TAB between the run and its content is whitespace to the run, and the
-- stamp is unaffected by it.
#guard stamped "k: &p\ta: 1\n" 0 7

-- §3 The boundary, which must NOT move.  Every accepted frame the props pack
-- serves, with and without the extension.
#guard emitsOk "&p a: 1\n"
#guard emitsOk "&p !t a: 1\n"
#guard emitsOk "- &p a: 1\n"
#guard emitsOk "- &p !t a: 1\n"
#guard emitsOk "k:\n  &p a: 1\n"
#guard emitsOk "k:\n  &p !t a: 1\n"
-- The EXPLICIT value slot, which keeps `noFrame` on this side too.
#guard emitsOk "?\n: &p a: 1\n"
#guard emitsOk "?\n: &p !t a: 1\n"
#guard emitsOk "? a\n: &p b: c\n"
-- A break after the run closes it as `propsEmpty`; the stamped line is behind.
#guard emitsOk "k: &p\n  a: 1\n"
-- `&a |` is a node and never a key — the pack's guard is refuted, not punted.
#guard emitsOk "k: &p |\n  x\n"
-- And the one that looks like the refused family and is not: `&p:` is a PLAIN
-- scalar with an anchor, so there is no second indicator at all.
#guard emits "k: &p: 1\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL &p: :1", "-MAP", "-DOC", "-STR"]

-- §4a The measured reason the CARRIER had to change: a park whose last real
-- token is a `[96]` property has no `StaleNodeTail`, because
-- `completesFlowValue` excludes exactly those tokens.  This is what made the
-- props path unable to name a reason while its refutation was available.
open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- A property park is never a completed node's tail. -/
example {sc : ScannerState} {t : YamlToken}
    (h : lastRealTokenVal? sc.tokens = some t) (hp : t.isNodeProperty = true) :
    ¬ StaleNodeTail sc := by
  rintro ⟨-, -, -, t', h', hc⟩
  rw [h] at h'
  cases h'
  cases t <;> simp_all [YamlToken.isNodeProperty, YamlToken.completesFlowValue]

-- §4b …and the two facts that make the reason spendable two steps later.
-- Item 102 proved the property heads' stamp readings separately; item 103
-- totalized the walk, so the run's own scan is the same lemma as its content's.
open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- The stamp survives the property run's own scan — `&` and `!` alike. -/
example {s s' : ScannerState} {c : Char}
    (hok : scanNextToken_dispatchContent s c = .ok s') :
    s'.implicitValueLine = s.implicitValueLine :=
  dispatchContent_implicitValueLine hok

open L4YAML.Scanner L4YAML.Proofs.StreamAccum in
/-- The punt travels with the park it is about — the run's extension takes the
    left line route, the run's content the saved key's.  Item 289: and the saved
    key's possibility travels too, the one premise the `tab` reason added. -/
example {sc s' : ScannerState} (h_punt : KeyPackPunt sc)
    (h_skpos : s'.simpleKey.pos = sc.simpleKey.pos)
    (h_input : s'.input = sc.input)
    (h_line : s'.line = sc.line ∨ s'.simpleKey.pos.line = s'.line)
    (h_ivl : s'.implicitValueLine = sc.implicitValueLine)
    -- Item 300: and the marker's field, which `markerLine` rides on.
    (h_dsl : s'.docStartLine = sc.docStartLine)
    (h_st : StalePark s')
    (h_poss : sc.simpleKey.possible = true → s'.simpleKey.possible = true) :
    KeyPackPunt s' :=
  keyPackPunt_transport h_punt h_skpos h_input h_line h_ivl h_dsl h_st h_poss

-- §5 The TAB reason, which item 102 also NAMES at the props producer, and
-- which is paid at one of its two consumers.  The park is genuinely accepted,
-- so the pack punts (item 65's shape, one construct over) …
#guard emitsOk "k:\n \t&p a\n"
#guard emitsOk "k:\n  \t&p a\n"
-- … and the refusal comes at the `:`.  A decorated CONTENT park lands on
-- `colon_fires_implicit_key`, which refutes the tab (item 65) — this is the
-- family the transport buys beyond the stamp.
#guard tabbed "k:\n \t&p a: 1\n" 1 2
#guard tabbed "k:\n \t&p !t a: 1\n" 1 2
-- The run's OWN park ~~still defers~~ is refuted at item 289:
-- `colon_fires_props_key` had the tab's reading but not the saved key's line
-- and possibility, which item 65's refutation also wants and which
-- `ImplicitKeyPack`'s consumer reads off its own guard.  The reason carries
-- both (both producers hold them).  Measured refused, pinned, named.
#guard tabbed "k:\n \t&p : 1\n" 1 2

-- §6 The other named residue item 102 did not take: a FLOW collection opened
-- at the run's park closes through item 56's frame, whose key context is
-- optional.  Pinned as refused so the next item had its measurement — and
-- item 103 took it, carrying the stamp across the collection on the mask's
-- base slot.  The run's share of that is the punt this file pins: a props park
-- in a stamped slot punts `implicitValue`, and the flow open reads the stamp
-- off that constructor rather than off a field of its own.
#guard stamped "k: &p [1]: 2\n" 0 9

end L4YAML.Tests.Guards.ScannerPropsRunSameLineKey

end Blanket
