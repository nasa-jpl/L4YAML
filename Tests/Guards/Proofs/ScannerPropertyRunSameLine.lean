module

public import L4YAML.Scanner.Scanner

public meta import L4YAML.Scanner.Scanner
public import L4YAML.Scanner.IndexedDispatch
public meta import L4YAML.Scanner.IndexedDispatch
public import L4YAML.Output.Events
public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx

public meta import L4YAML.Output.EventsIx
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # A property run on ONE LINE is one node's (DOCS item 9k)

Item 9e made three §6.9 tests — no second anchor, no second tag, no alias after a
property — and gated all three on `s.inFlow`, because token adjacency means "same
node" only when nothing that emits no token can intervene, and a *block*
collection opens without a token:

```yaml
&mapping
&key [ &item a, b, c ]: value    # 26DV: &mapping is on the MAPPING
top3: &node3
  *alias1 : scalar3              # &node3 is on the nested mapping
```

The gate was read as the premise.  It is not — it is one *sufficient context* for
it, and there is a second, independent of it.  `[200] s-l+block-collection(n,c)`
reads its properties and then `s-l-comments`, whose `[77] s-b-comment` is
`b-non-content` or end of input: **a block collection's properties are always
separated from its content by a break.**  So two property tokens on the SAME LINE
cannot be split by a block opening, whatever the indent stack says — and that is
exactly what separates the two counterexamples above (lines 0 and 1) from every
illegal shape below (all single-line).

So the three tests are now the disjunction `whole run, in flow` (9e) or
`this line's run, anywhere` (9k), and the disjuncts are incomparable: §5 pins a
run 9e still owns and 9k cannot see.

**The residual.**  Same-line is *sufficient*, not necessary, so a run already
broken across lines is not read: `&a⏎&b⏎c` has two anchors on one node, has no
derivation, and is still accepted.  Telling that apart from 26DV needs the indent
machinery (DOCS β.5).  It is deliberately **not** pinned below — pinning an
over-acceptance is what Reflection 622 caught the last pass doing.
-/

namespace Tests.Guards.ScannerPropertyRunSameLine

open L4YAML
open L4YAML.Scanner

/-- Legacy and indexed verdicts as a comparable pair: `none` on success,
    `some e` on rejection.  Equal pairs mean the two pipelines agree. -/
private def verdicts (input : String) : Option ScanError × Option ScanError :=
  ( (match scan input with | .ok _ => none | .error e => some e)
  , (match Indexed.ScannerStateIx.scanIx input with | .ok _ => none | .error e => some e) )

/-- Both pipelines reject `input` at a repeated/misplaced property. -/
private def rejects9k (input : String) (c : Char) (line col : Nat) : Bool :=
  verdicts input == (some (.invalidNodeProperties c line col),
                     some (.invalidNodeProperties c line col))

/-- Both pipelines accept `input`. -/
private def scanOkP (input : String) : String :=
  match Scanner.scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def bothAccept (input : String) : Bool := verdicts input == (none, none)

/-! ## §1  A second anchor on the line

`[96] c-ns-properties` admits at most one `[101] c-ns-anchor-property`.  None of
these derives; all of them scanned clean at depth 0 before this item. -/

#guard rejects9k "&a &b c\n" '&' 0 3              -- before a plain scalar
#guard rejects9k "&a &b [c]\n" '&' 0 3            -- before a flow open (site 5's arm)
#guard rejects9k "&a &b\n" '&' 0 3                -- with no content at all
#guard rejects9k "&a &b: v\n" '&' 0 3
#guard rejects9k "- &a &b: v\n" '&' 0 5           -- inside a block sequence
#guard rejects9k "? &a &b\n" '&' 0 5              -- on an explicit key's node

-- A THIRD property dies on the run's PENULT — the two-token lookback earning
-- its width in block context exactly as it does in flow.
#guard rejects9k "&a !t &b: v\n" '&' 0 6
#guard rejects9k "&a !!str &b c\n" '&' 0 9
#guard rejects9k "&a !!str &b [c]\n" '&' 0 9

/-! ## §2  A second tag on the line

The mirror, for `[97] c-ns-tag-property`.  This is the half the *parser* never
caught either: it accepted `!!str !!int c` and silently kept the last tag. -/

#guard rejects9k "!t !u c\n" '!' 0 3
#guard rejects9k "!!str !!int c\n" '!' 0 6
#guard rejects9k "!!str !!int [c]\n" '!' 0 6
#guard rejects9k "!!str &a !!int c\n" '!' 0 9     -- on the penult again
#guard rejects9k "- !t !u c\n" '!' 0 5

/-! ## §3  An alias after a property on the line

`[104] c-ns-alias-node` is an *alternative* to the properties-bearing form of
`[161] ns-flow-node`, never its content, so a property may not decorate it. -/

#guard rejects9k "k: &b x\nj: &a *b\n" '*' 1 6
#guard rejects9k "- &b x\n- &a *b\n" '*' 1 5
#guard rejects9k "a: &x 1\nb: !t *x\n" '*' 1 6

/-! ## §4  A break makes it two nodes again

The counterexamples that forced 9e's gate, and their neighbours.  Every one puts
the two property tokens on DIFFERENT lines, which is not a coincidence but
`[200]`'s `s-l-comments`. -/

#guard bothAccept "&mapping\n&key [ &item a, b, c ]: value\n"
#guard bothAccept "alias1: &alias1 x\ntop3: &node3\n  *alias1 : scalar3\n"
#guard bothAccept "&node3\n*node3 : scalar3\n"
#guard bothAccept "&a\n- x\n"                     -- a block sequence under a property
#guard bothAccept "&a\n&b k: v\n"                 -- a block mapping under a property,
                                                  -- its first key anchored
#guard bothAccept "- &a\n  &b k: v\n"
-- Item 180: the two pins above used to read `&b: v` — but `:` IS an
-- `ns-anchor-char` (`[102]` excludes only the flow indicators), so `&b:` is
-- the anchor NAMED `b:` and the line is a SECOND anchor with a naked scalar —
-- two anchors, one `[96]` run, no derivation.  The old acceptance silently
-- DROPPED the first anchor; the crossed-block clause refuses at the second
-- anchor's own position.  (PyYAML accepts because its anchor charset is
-- narrower than `[102]` — it reads `&b` + an empty key — a PyYAML-side
-- divergence, and the production text is the reference.)
#guard scanOkP "&a\n&b: v\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOkP "- &a\n  &b: v\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 2"

/-! ## §5  The two disjuncts are incomparable

9e reads the whole run and needs the flow gate; 9k reads the line and needs no
gate.  Inside a flow a run may legally span lines, so 9e still owns these — and
9k, which truncates at the break, cannot see them. -/

#guard rejects9k "[&a\n&b c]\n" '&' 1 0           -- 9e only: run split by a break
#guard rejects9k "{!t\n!u c: v}\n" '!' 1 0
#guard rejects9k "[\n&a\n&b c]\n" '&' 2 0
#guard rejects9k "[&a &b c]\n" '&' 0 4            -- both disjuncts fire
#guard bothAccept "[&a\n!t c]\n"                  -- anchor THEN tag: legal, either way

/-! ## §6  What the rule does not touch

One anchor and one tag on a line are `[96]`'s whole point; an alias that follows
no property is an ordinary node; and the four shapes site 5's arm actually
receives are all still legal. -/

#guard bothAccept "&a !t c\n"
#guard bothAccept "!t &a c\n"
#guard bothAccept "&a c\n"
#guard bothAccept "&a x\n*a\n"
#guard bothAccept "&a [c]\n"
#guard bothAccept "!t {a: b}\n"
#guard bothAccept "&a !!seq [b]\n"
#guard bothAccept "--- &a [b]\n"

/-! ## §7  The compositions the accumulation now DERIVES (DOCS item 12)

Item 9t parked a depth-0 `[96]` run as `PendingNode.pendingProps` but let its
same-line CONTENT dispatch escape into the `pendingFlow` deferral.  Item 12
composes it instead — `[161]`'s `( c-ns-properties s-separate ns-flow-content )`
for scalars and collections, `[198] s-l+block-scalar`'s own props slot for
`|`/`>` — with the `&`/`!` arms EXTENDING the held run.  The event streams
below are the shapes those derivations cover, pinned on BOTH pipelines (the
pass itself is proof-only: no scanner or emitter changed). -/

/-- Legacy and indexed event streams as a comparable pair; `none` on rejection. -/
private def bothEvents (input : String) : Option String × Option String :=
  ( (match Events.streamToEvents input with | .ok s => some s | .error _ => none)
  , (match Events.streamToEventsIx input with | .ok s => some s | .error _ => none) )

/-- Both pipelines accept `input` and emit exactly `expected`. -/
private def emits (input : String) (expected : List String) : Bool :=
  let e := some (String.intercalate "\n" expected ++ "\n")
  bothEvents input == (e, e)

-- The run decorates a plain or quoted scalar — `SFlowNode.propsContent`.
#guard emits "&a b\n" ["+STR", "+DOC", "=VAL &a :b", "-DOC", "-STR"]
#guard emits "&a \"b\"\n" ["+STR", "+DOC", "=VAL &a \"b", "-DOC", "-STR"]

-- The run EXTENDS on the missing half, then decorates — `PropsRun.addTag` /
-- `.addAnchor` feeding the same composition.
#guard emits "&a !t b\n" ["+STR", "+DOC", "=VAL &a <!t> :b", "-DOC", "-STR"]
#guard emits "!t &a b\n" ["+STR", "+DOC", "=VAL &a <!t> :b", "-DOC", "-STR"]

-- …and the extended run rides a flow open (`&a !t [b]` was the recorded
-- escape shape).
#guard emits "&a !t [b]\n"
  ["+STR", "+DOC", "+SEQ [] &a <!t>", "=VAL :b", "-SEQ", "-DOC", "-STR"]

-- The run decorates a BLOCK scalar through `[198]`'s props slot.
#guard emits "&a |\n text\n" ["+STR", "+DOC", "=VAL &a |text\\n", "-DOC", "-STR"]
#guard emits "!t >\n text\n" ["+STR", "+DOC", "=VAL <!t> >text\\n", "-DOC", "-STR"]

end Tests.Guards.ScannerPropertyRunSameLine

end Blanket
