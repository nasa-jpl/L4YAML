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

/-! # The last two implicit-key heads: properties and alias (DOCS item 17)

`&a x: v` and `*a : b` join items 15/16's plain and quoted keys as GRAMMAR,
and they cost no new carrier arm: `[188] ns-s-block-map-implicit-key`'s two
alternatives read a plain scalar and a FLOW NODE, and `[161] ns-flow-node(0,
block-key)` already names an alias (`[104] c-ns-alias-node`) and a
property-prefixed node (`c-ns-properties s-separate ns-flow-content`) among its
own arms.  Item 16's key head enumerated three SCANNER branches; item 17 re-cut
it along the PRODUCTION's seam — two arms, one per alternative of `[188]` — and
both remaining heads landed inside the ones already there.

What each head needed beyond that:

* the ALIAS head, nothing at all.  `ns-anchor-char` excludes `s-white` and
  `b-char`, so an alias cannot cross a break; there is no one-line reading to
  prove and no line hypothesis to discharge, and the production is
  context-free, so the scan's own evidence reads at `block-key` directly.
* the PROPS head, one datum carried forward.  The key a following `:`
  validates was saved when the run OPENED (a property push is not a key save),
  so the run's pending carries "that key is still on this line" to the step
  that scans the content — which is exactly the hypothesis items 15/16's
  one-line readings ask for.  `[96]`'s optional second half embeds an
  `s-separate`, so a two-half run (`&a !t x: v`) re-reads at `block-key` only
  because the extension arm built that separator from residual whites.

The pins below fix the composed shapes — both halves of `[96]` in both orders,
every content head under a run, the alias key with its value forms — and the
neighbours that must not move.
-/

namespace Tests.Guards.ScannerPropsAliasKeyCompose

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

/-! ## §1  The props head — a column-0 `[96]` run followed by its content -/

#guard emits "&a x: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The tag half alone: `[96]`'s other single-half arm.
#guard emits "!!str x: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL <tag:yaml.org,2002:str> :x", "=VAL :v",
   "-MAP", "-DOC", "-STR"]
-- Both halves, both orders — the run EXTENDS, and its internal `s-separate`
-- re-reads at `block-key` because the whites stayed on the line.
#guard emits "&a !t x: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a <!t> :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "!t &a x: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a <!t> :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- Every content head reads under a run: plain (above), and the two quoted
-- readings item 16 built, reused verbatim.
#guard emits "&a \"x\": v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a \"x", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "&a 'x': v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a 'x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- In-line separation before the `:` ([66], here non-empty), and the empty
-- value (`[189]`'s `( e-node s-l-comments )` arm).
#guard emits "&a x : v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
#guard emits "&a x:\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :", "-MAP", "-DOC", "-STR"]

/-! ### Values and siblings ride item 13's `pendingMapValue` unchanged -/

#guard emits "&a x: [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "+SEQ []", "=VAL :1", "-SEQ",
   "-MAP", "-DOC", "-STR"]
#guard emits "&a x: &b y\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL &b :y", "-MAP", "-DOC", "-STR"]
#guard emits "&a x: v\n&b y: w\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :v", "=VAL &b :y", "=VAL :w",
   "-MAP", "-DOC", "-STR"]
-- Property-prefixed keys mix freely with bare ones, in both directions.
#guard emits "&a x: v\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :v", "=VAL :c", "=VAL :d",
   "-MAP", "-DOC", "-STR"]
#guard emits "a: b\n&c d: e\n"
  ["+STR", "+DOC", "+MAP", "=VAL :a", "=VAL :b", "=VAL &c :d", "=VAL :e",
   "-MAP", "-DOC", "-STR"]

/-! ## §2  The alias head — `[104] c-ns-alias-node` as `[161]`'s alias arm

An alias key needs a defined anchor (§7.1), so the composed shapes are all
siblings of an earlier entry; and it needs the separating space, because
`ns-anchor-char` admits `:` — `*a:` is one anchor NAME, not an alias and a
value indicator (§4). -/

#guard emits "k: &a v\n*a : b\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL &a :v", "=ALI *a", "=VAL :b",
   "-MAP", "-DOC", "-STR"]
#guard emits "k: &a v\n*a :\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL &a :v", "=ALI *a", "=VAL :",
   "-MAP", "-DOC", "-STR"]
#guard emits "k: &a v\n*a : [1]\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL &a :v", "=ALI *a", "+SEQ []",
   "=VAL :1", "-SEQ", "-MAP", "-DOC", "-STR"]
#guard emits "k: &a v\n*a : b\n*a : c\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL &a :v", "=ALI *a", "=VAL :b",
   "=ALI *a", "=VAL :c", "-MAP", "-DOC", "-STR"]
#guard emits "k: &a v\n*a : b\nc: d\n"
  ["+STR", "+DOC", "+MAP", "=VAL :k", "=VAL &a :v", "=ALI *a", "=VAL :b",
   "=VAL :c", "=VAL :d", "-MAP", "-DOC", "-STR"]

/-! ## §3  Still punted — accepted through the deferral, recorded in row 12 -/

-- col ≠ 0: the indent machinery's arm, the same one the plain and quoted
-- heads still punt on.
#guard emits " &a x: v\n"
  ["+STR", "+DOC", "+MAP", "=VAL &a :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- A block scalar under a run is a NODE (`[198]`'s props slot), never a key —
-- the head punts and the run rides into the scalar, as item 12 built it.
#guard emits "&a |\n y\n"
  ["+STR", "+DOC", "=VAL &a |y\\n", "-DOC", "-STR"]

/-! ## §4  The neighbours — must NOT move, identical in BOTH pipelines -/

-- The run and its content on different lines: the pending CLOSES across the
-- break (the run's couplings go stale with the line), so the key is the plain
-- one item 15 packs, and the anchor decorates what follows.
#guard emits "&a\nx: v\n"
  ["+STR", "+DOC", "+MAP &a", "=VAL :x", "=VAL :v", "-MAP", "-DOC", "-STR"]
-- The break-crossed `:` shape: item 19 composes it as `[189]`'s EMPTY-key
-- entry (the pack is spent — a one-line key cannot span the break), and the
-- parser then refuses the bare document that results.
#guard verdicts "&a x\n: v\n" ==
  (some (.invalidBareDocument 1 0), some (.invalidBareDocument 1 0))
-- An alias key still resolves like any other alias.
#guard verdicts "*a : b\n" == (some (.undefinedAlias "a" 0 0), some (.undefinedAlias "a" 0 0))
-- `ns-anchor-char` is `ns-char` minus the FLOW indicators, so `:` is part of
-- the NAME: `*a: b` is an alias to `a:`, not an alias key.  Both pipelines
-- reject; they disagree only on WHICH check fires first when an undefined
-- alias is also followed by content (legacy resolves, indexed delimits) — an
-- error-stage difference of the verdict-equal class item 14 catalogued, not a
-- difference in what is accepted.
#guard verdicts "*a: b\n" ==
  (some (.undefinedAlias "a:" 0 0), some (.trailingContent 0 4))
-- A key whose run opened on the previous line is not this line's key.
#guard verdicts "&a v\n*a : b\n" ==
  (some (.invalidImplicitKey 1), some (.invalidImplicitKey 1))

end Tests.Guards.ScannerPropsAliasKeyCompose

end Blanket
