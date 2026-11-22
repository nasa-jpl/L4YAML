module

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

/-! # A compact `?` is a `[186]` explicit key like any other (DOCS item 105)

Items 101–103 emptied `KeyPackPunt.implicitValue`'s three parks by refutation:
`[189]`'s value slot stamps its line and §8.2.2 refuses a second value
indicator there.  `noFrame` is the OTHER half of that split — the park with no
frame and no stamp — and it is not a refutation but a missing payment.

The name has been carrying the wrong input.  Item 101 recorded the residue as
the EXPLICIT value slot (`?⏎: b: c`, `? a⏎: b: c`), but both of those are
served: the landed `:` at a `pendingMapValue` reads the `?` frame off `h_expl`
(item 51) and re-parks through `colon_open_map_explicit`, whose `h_vslot` is a
real slot, so the mid-line `:` after `b` composes through `[195]`.  The park
that actually reaches `noFrame` is the COMPACT `?` — `- ? a: b` — whose
producer (`compact_open_map`) handed `Or.inr trivial` for both fields where the
column-0 producer (`question_open_map`) has paid them since item 51.

Nothing about the KEY differs between the two.  `[195] ns-l-compact-mapping`'s
first entry is an ordinary `[188]`, so the `?` heading it is `[186]
c-l-block-map-explicit-key` and owns the same two things: the entry ROUTE that
keeps it open until its `:` value line lands, and the `[186]` KEY SLOT with the
compact alternatives inside it.  Both factor through one route into the
enclosing entry's closure, which is `compactExplicitKeyFrame`.

Everything pinned below is RUNTIME behavior and none of it changed at this
item — no runtime file is touched.  The pins say what the proof's new payment
has to be consistent with; an escape is silent, so no runtime observation can
say which arm a given input takes. -/

namespace L4YAML.Tests.Guards.ScannerCompactExplicitKey

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum

private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )
    == (e, e)

private def emitsOk (input : String) : Bool :=
  ( (Events.streamToEvents input).toOption.isSome
  , (Events.streamToEventsIx input).toOption.isSome ) == (true, true)

private def refuses (input : String) : Bool :=
  match Events.streamToEvents input, Events.streamToEventsIx input with
  | .error _, .error _ => true
  | _, _ => false

-- §1 The KEY SLOT, spent by a same-line `:` through `[195]`.  The compact `?`'s
-- key is a mapping, and the entry's own value is `e-node` — which is exactly
-- what `? a: b` reads as one construct over.
#guard emits "- ? a: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "? ? a: b\n"
  ["+STR", "+DOC", "+MAP", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP",
   "=VAL :", "-MAP", "=VAL :", "-MAP", "-DOC", "-STR"]
-- The props-headed key is the same park with a `[96]` run in front of it —
-- item 102's reason on the same frame, so it needs the same field.
#guard emits "- ? &p a: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL &p :a", "=VAL :b", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- ? !t a: b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL <!t> :a", "=VAL :b", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
-- …and the quoted key head, which reaches the same slot by a different arm.
#guard emits "- ? \"a\": b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL \"a", "=VAL :b", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]

-- §2 The frames the compact `?` can sit in.  Every one of them parks the same
-- pending, so one payment serves them all.
#guard emitsOk "- - ? a: b\n"
#guard emitsOk "k:\n  - ? a: b\n"
#guard emitsOk "? - ? a: b\n"
#guard emitsOk "- ? a: b\n- c\n"

-- §3 The slot's OTHER alternatives — `[185]`'s compact forms and a flow node,
-- all reached through the same field.
#guard emits "- ? - a\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+SEQ", "=VAL :a", "-SEQ", "=VAL :",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- ? ? b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL :b", "=VAL :", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- ? : v\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL :", "=VAL :v", "-MAP",
   "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- ? [1]: 2\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "+SEQ []", "=VAL :1", "-SEQ",
   "=VAL :2", "-MAP", "=VAL :", "-MAP", "-SEQ", "-DOC", "-STR"]

-- §4 The ENTRY ROUTE, spent by the landed `:` at `s-indent(n+1+m)` — the
-- entry stays open across the break, which is what `h_expl` is for.
#guard emits "- ? a\n  : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
#guard emits "- ? a\n  : - w\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :a", "+SEQ", "=VAL :w", "-SEQ",
   "-MAP", "-SEQ", "-DOC", "-STR"]
#guard emits "- ? &p a\n  : b\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL &p :a", "=VAL :b", "-MAP", "-SEQ",
   "-DOC", "-STR"]
-- Both fields at once: the slot takes the compact mapping and the route then
-- closes the entry with its value line.
#guard emits "- ? a: b\n  : c\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "+MAP", "=VAL :a", "=VAL :b", "-MAP",
   "=VAL :c", "-MAP", "-SEQ", "-DOC", "-STR"]

-- §5 The boundary the payment must NOT cross: the compact `:`.  `[189]`'s
-- value is `s-l+block-node`, which has no compact alternative and opens no
-- `[188]` entry — so that branch pays neither field, and its same-line key is
-- refused by the stamp instead (item 101).
#guard refuses "- : a: b\n"
#guard refuses "- ? a: b: c\n"
#guard emits "- : v\n"
  ["+STR", "+DOC", "+SEQ", "+MAP", "=VAL :", "=VAL :v", "-MAP", "-SEQ",
   "-DOC", "-STR"]

/-! ## §6 The payment at its type

One route into the enclosing entry's closure yields both fields.  The `?`
literal is the only premise beyond the frame `compact_open_map` already
holds — which is why the two producers differ in nothing but the route. -/

example {sp_start sp_entry sp_ind sp_scan' : SurfPos} {n m : Nat}
    {ctx : YamlContext}
    (h_close_old : ∀ sp, SBlockIndented n ctx sp_entry sp → SLYamlStream sp_start sp)
    (h_ind : SIndent m sp_entry sp_ind)
    (h_qlit : GLit '?' sp_ind sp_scan') :
    (∃ sp_q : SurfPos, GLit '?' sp_q sp_scan' ∧
      ∀ sp_v : SurfPos, SBlockMapEntry (n + 1 + m) sp_q sp_v →
        SLYamlStream sp_start sp_v) ∧
    (∀ sp_v : SurfPos, SBlockIndented (n + 1 + m) .blockOut sp_scan' sp_v →
      SLYamlStream sp_start sp_v) :=
  compactExplicitKeyFrame h_close_old h_ind h_qlit

end L4YAML.Tests.Guards.ScannerCompactExplicitKey

end Blanket
