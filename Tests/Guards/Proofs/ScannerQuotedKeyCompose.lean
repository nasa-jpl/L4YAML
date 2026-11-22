module

public import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
public meta import L4YAML.Token.Token
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The col-0 QUOTED implicit key composes (DOCS item 16)

`"a": b` and `'a': b` join item 15's `a: b` as GRAMMAR: `[188]
ns-s-block-map-implicit-key`'s **JSON** arm — `[194] c-s-implicit-json-key`
over `[161] ns-flow-node(0, block-key)`'s content alternative, i.e. `[109]
c-double-quoted(0, block-key)` or `[120] c-single-quoted(0, block-key)` —
then `[66]`'s optional in-line separation, `GLit ':'`, and item 13's
`pendingMapValue` awaiting the value.

Item 15's coupling field is unchanged; only its payload widened, from the
plain one-line reading to an `ImplicitKeyHead` carrying either arm of
`[188]`.  What the quoted heads needed was their own one-line reading, and
that one is SELF-CONTAINED rather than a conjunct: `[110]
nb-double-text(n, block-key)` IS `[111] nb-double-one-line`, so a walk
exiting on its entry line simply refutes the two arms that consume a break
— the escaped break (`\` + `b-char`) and the flow fold — both of which open
with `consumeNewline` (+1) and are followed by a walk that never returns.
The escape body is line-transparent for the same reason `s-white` is:
`ns-hex-digit` and the simple escape characters are not `b-char`.

The pins below fix the composed shapes (including every arm of the two
loops: the empty body, the `''` escape, a simple escape, a hex escape) and
the neighbours that must not move — the multi-line keys the one-line
reading refutes, which the scanner rejects at §7.4 in BOTH pipelines.
-/

namespace Tests.Guards.ScannerQuotedKeyCompose

open L4YAML

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

/-- Legacy and indexed end-to-end verdicts as a comparable pair: `none` on
    success (scan errors and parse errors share `ScanError`). -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match Events.streamToEvents input with | .ok _ => none | .error e => some e)
  , (match Events.streamToEventsIx input with | .ok _ => none | .error e => some e) )

/-! ## §1  The composed shapes — col-0 quoted keys, same-line `:` -/

#guard emits "\"a\": b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "'a': b\n"
  ["+STR", "+DOC", "+MAP", "=VAL 'a", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- In-line separation before the `:` ([66], here non-empty).
#guard emits "\"a\" : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- Empty value: `[189]`'s `( e-node s-l-comments )` arm via the pending's close.
#guard emits "\"a\":\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :", "-MAP", "-DOC", "-STR"]
-- A key with layout whitespace inside the quotes.
#guard emits "\"a b\": c\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a b", "=VAL :c", "-MAP", "-DOC", "-STR"]

/-! ### Every arm of the two one-line walks -/

-- The EMPTY body: the closing quote is the walk's first step (`GStar.nil`).
#guard emits "\"\": b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"", "=VAL :b", "-MAP", "-DOC", "-STR"]
#guard emits "'': b\n"
  ["+STR", "+DOC", "+MAP", "=VAL '", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- `[117] c-quoted-quote`: the `''` arm of the single-quoted walk.
#guard emits "'a''b': c\n"
  ["+STR", "+DOC", "+MAP", "=VAL 'a'b", "=VAL :c", "-MAP", "-DOC", "-STR"]
-- `[62] c-ns-esc-char`, simple: `processEscape` is line-transparent.
#guard emits "\"a\\tb\": c\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a\\tb", "=VAL :c", "-MAP", "-DOC", "-STR"]
-- `[60] ns-esc-16-bit`: so is the hex-digit body.
#guard emits "\"a\\u0041b\": c\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"aAb", "=VAL :c", "-MAP", "-DOC", "-STR"]

/-! ### Values and siblings ride item 13's `pendingMapValue` unchanged -/

#guard emits "\"a\": [1, 2]\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "+SEQ []", "=VAL :1", "=VAL :2",
   "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "\"a\": |\n x\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL |x\\n", "-MAP", "-DOC", "-STR"]
#guard emits "\"a\": b\n\"c\": d\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "=VAL \"c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
-- Mixed heads in one mapping: `[188]`'s two arms alternate freely.
#guard emits "a: b\n\"c\": d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL \"c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
#guard emits "\"a\": b\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]

/-! ## §2  Neighbouring heads — the punted one, and the one item 17 packed -/

-- col ≠ 0: the indent machinery's arm.
#guard emits " \"a\": b\n"
  ["+STR", "+DOC", "+MAP", "=VAL \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]
-- A property-prefixed key: packed by item 17, through the same quoted
-- reading (see `ScannerPropsAliasKeyCompose.lean`).
#guard emits "&x \"a\": b\n"
  ["+STR", "+DOC", "+MAP", "=VAL &x \"a", "=VAL :b", "-MAP", "-DOC", "-STR"]

/-! ## §3  The refuted neighbours — must NOT move, identical in BOTH pipelines

A key whose walk crossed a break is not `nb-double-one-line`; the scanner's
§7.4 pass rejects it, exactly where the one-line reading refutes. -/

-- Flow fold inside the key.
#guard verdicts "\"a\nb\": c\n" == (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))
#guard verdicts "'a\nb': c\n" == (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))
-- `[112] s-double-escaped`: the escaped break, the walk's other break arm.
#guard verdicts "\"a\\\nb\": c\n" ==
  (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))
-- A closed predecessor leaves a stale cross-line key.
#guard verdicts "x\n\"a\": b\n" ==
  (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))
-- The break-crossed `:` shape: item 19 composes it as `[189]`'s EMPTY-key
-- entry (the pack is spent — a one-line key cannot span the break), and the
-- parser then refuses the bare document that results.
#guard verdicts "\"a\"\n: b\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))

end Tests.Guards.ScannerQuotedKeyCompose

end Blanket
