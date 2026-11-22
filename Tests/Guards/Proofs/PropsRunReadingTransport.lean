module

public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The `[96]` run's reading, transported — and the gate's one unpayable site
    (DOCS item 160)

Item 159 left the property lane in two pieces and named the first as "a premise
shape for `pendingProps.h_route` that relays through a PROPERTY push".  This
file is that piece, run: the relay is built, and the gate it was meant to buy
is measured to the SITE.

**What the gate would be.**  `pendingProps.h_route` is the run's stream
closure.  Guarding it with `danglingNodePos? sc = none` — the face
`pendingContent` has carried since item 157 and `pendingBlockContent` since item
159 — is what would let `ContentRouteGate` lose its right disjunct, and with it
the last CHARACTER residue in the content landing's bare-document route.

**What it costs, exactly.**  Guarding the field and building the module names
**23** spend sites, and they fall in four classes:

| class | sites | pays with |
|---|---|---|
| the park's close (`PendingNode.close_with_ssl`) | 1 | `h_nd`, its own parameter |
| the landing producers (`content_dispatch_routed` and its four siblings) | 10 | the gate itself, once the right disjunct is gone |
| the run's rides — its extension and its content (`accum_content_pending`) | 12 | the RELAY, below |
| the run's ride into a FLOW COLLECTION (`accum_flow_open_depth0`) | 1 | ~~**nothing**~~ — item 161's gate, spent by item 165's props arm |

**All four classes pay as of item 165**, and the table's own two surprises are
recorded where they were found: the flow row needed a gate on
`FlowBaseRoutes.value` (items 161–164), and the extension row needed §6.9's
length check (item 165's `propertyRunFull`) before the relay below was true at
all.  The count is TWELVE rides rather than eleven — the re-count is item 165's.

**The relay, in three pushes.**  A park's own last token is a `[96]` property,
so every push onto it is the case item 158's push lemmas exclude, and the three
that can happen do three different things (§1).  A BODY preserves the reading; a
PROPERTY moves its start; a flow COLLECTION preserves it, but only through its
close, and only by item 159's third arm.

**The site that cannot pay** is the flow ride, and §3 is why: it is not a park
whose reading could be read differently, it is a closure with no scanner state
in it at all.  `FlowBaseRoutes.value` is built at the OPEN and spent at the
CLOSE, and the reading only becomes available at the close.  So the gate belongs
on that field, and what it needs is the walk's own answer — which is the flow
stack's to supply. -/

namespace L4YAML.Tests.Guards.PropsRunReadingTransport

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

private def posStr : Option YamlPos → String
  | some p => s!"{p.line},{p.col}"
  | none => "none"

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def parseOk (input : String) : String :=
  match Events.streamToEvents input with
  | .ok _ => "PARSE-OK"
  | .error e => s!"PARSE-ERR {repr e}"

private def stepTo (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepTo s' k
    | _ => none

/-- The run reading after `n` steps: what kind of token the trailing run starts
    with, where it sits, and the verdict `danglingNodePos?` takes off it. -/
private def stepAt (input : String) (n : Nat) : String :=
  match stepTo ((ScannerState.mk' input).emit .streamStart) n with
  | none => "—"
  | some s =>
    match trailingNodeRun? s.tokens with
    | none => s!"run=none park={posStr (danglingNodePos? s)}"
    | some (st, _) =>
      let t := s.tokens[st]!
      let k := if t.val.isNodeProperty then "prop"
               else if t.val.isNodeBody then "body"
               else if t.val.isFlowOpen then "open"
               else if t.val.isFlowClose then "close" else "other"
      s!"run={k}@{t.pos.line},{t.pos.col} park={posStr (danglingNodePos? s)}"

private def walk (input : String) (n : Nat) : String :=
  String.intercalate " ; " ((List.range n).map (stepAt input))

/-! ## §1  The three pushes onto a `[96]` park

### A BODY preserves the reading

`a: 1⏎&p b`: the park after `&p` reads `1,0`, and so does the park after the
scalar it takes as its content.  The walk-back crosses the property and reaches
the same start, which is why §9.2's refusal rides a run into its own node. -/

#guard walk "a: 1\n&p b\n" 7
  == "run=none park=none ; run=body@0,0 park=none ; run=none park=none ; \
run=body@0,3 park=none ; run=prop@1,0 park=1,0 ; run=prop@1,0 park=1,0 ; —"

/-- The relay in the shape its consumer needs: a park's verdict is recovered
    from the verdict one BODY push later.

    **Item 182 made this an implication rather than an equality**, and the
    direction that went is the one no consumer asked for: the content a park
    takes may be the token that STARTS a line, and then the pushed state is
    refused where the park was clean (`k: &x⏎a`).  What survives is exactly
    this — the park's own `none`, recovered from the push's. -/
example {s s' : ScannerState} {c : Char} {i : Nat}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hna : c ≠ '&') (hnt : c ≠ '!')
    (hprev : prevRealIdx? s.tokens s.tokens.size = some i)
    (hiprop : s.tokens[i]!.val.isNodeProperty = true)
    (h_nd : danglingNodePos? s' = none) : danglingNodePos? s = none :=
  danglingNodePos?_dispatch_body_onProp hok hna hnt hprev hiprop h_nd

/-! ### A PROPERTY moves the start — the arm item 165 emptied and item 170 REOPENED

`&a⏎!t &b x` is this file's witness: at step 2 the run starts at the `&a` on
line 0, and the THIRD property pushes the start down to the `!t` on line 1, so
the reading at the park and the reading one push later are readings of
DIFFERENT tokens.  That is why the premise cannot be stated as
`danglingNodePos? sc = none` and relayed through a run's own extension.

**Item 165 refused the input; item 170 narrowed that gate back** (the
length-only form read a parent's full run and a fresh key's run as one — 9KAX
— so in block context it fires only when all three properties share the
cursor's line).  The cross-line third is the PARSER's again, and the start
DOES move at a scanner-reachable park — step 3 below reads `1,0` where step 2
read `0,0`.  ~~The relay serves the moved window by returning it
(`PropsWindowCross`), which `pendingProps.h_routeX` answers without the
verdict.~~  **Item 181: the moved window is a REFUSAL** — the third property
makes three adjacent, `[96]` admits one anchor and one tag, and §9.2's fourth
clause (item 180) reads the duplicate, which the park column below shows as
`park=1,3`.  So the relay is a plain implication whose premise is false there,
and both the window and the route are deleted (`PropsCrossWindowRoute` is that
guard). -/

-- Item 180: the crossed-block clause reads the over-full block as SOME from
-- the excess property on, and the family refuses at the scanner (EOF).
#guard walk "&a\n!t &b x\n" 6
  == "run=none park=none ; run=prop@0,0 park=none ; run=prop@0,0 park=none ; \
run=prop@1,0 park=1,3 ; run=prop@1,0 park=1,3 ; —"
#guard scanOk "&a\n!t &b x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 3"
#guard parseOk "&a\n!t &b x\n"
  == "PARSE-ERR L4YAML.ScanError.invalidBareDocument 1 3"

/-- Where the start goes: the PARK's own last token, not the pushed one. -/
example {s s' : ScannerState} {c : Char} {i : Nat}
    (hok : scanNextToken_dispatchContent s c = .ok s')
    (hc : c = '&' ∨ c = '!')
    (hprev : prevRealIdx? s.tokens s.tokens.size = some i)
    (hiprop : s.tokens[i]!.val.isNodeProperty = true) :
    trailingNodeRun? s'.tokens = some (i, prevRealIdx? s.tokens i) :=
  trailingNodeRun?_dispatch_prop_onProp hok hc hprev hiprop

/-- The dispatch's own pass, read back — under item 170's gate this refutes a
    SAME-LINE below-property, and item 170 spent it on the cross-line window.
    Item 181 retires that spend (the window refuses on its KINDS, with no line
    read at all), so this reading is pinned here and nowhere else. -/
example {s s' : ScannerState} (hok : scanNextToken_dispatchContent s '&' = .ok s') :
    propertyRunFull s = false :=
  propertyRunFull_false_of_anchor_dispatch hok

-- Three properties on ONE line are refused by §6.9's kind and length guards;
-- the TWO-long run is untouched, on a line or across one.
#guard scanOk "&a !t &b x\n"
  == "SCAN-ERR L4YAML.ScanError.invalidNodeProperties '&' 0 6"
#guard (scanOk "&a !t x\n", parseOk "&a !t x\n") == ("SCAN-OK", "PARSE-OK")
#guard (scanOk "&a\n!t x\n", parseOk "&a\n!t x\n") == ("SCAN-OK", "PARSE-OK")

/-! ### A flow COLLECTION preserves it — at the CLOSE

`a: 1⏎&p [b]`: the park after `&p` reads `1,0`; inside the collection there is
no reading at all (in flow); at the `]` the reading is `1,0` again.  That is
item 159's third arm — the close walked back to its open, then the `[96]`
walk-back from there — and it is what makes the collection's own close the
place the run's verdict can be spent. -/

#guard walk "a: 1\n&p [b]\n" 9
  == "run=none park=none ; run=body@0,0 park=none ; run=none park=none ; \
run=body@0,3 park=none ; run=prop@1,0 park=1,0 ; run=none park=none ; \
run=body@1,4 park=none ; run=prop@1,0 park=1,0 ; —"

/-- The same, as a lemma: the array at the close and the array at the park
    report the SAME run, given that the close finds its own open.  That
    hypothesis is the one thing this file cannot discharge — see §3. -/
example {a b : Array (Positioned YamlToken)} {i k : Nat}
    (hagree : ∀ j, j < b.size → a[j]! = b[j]!)
    (hbprev : prevRealIdx? b b.size = some k)
    (hbprop : b[k]!.val.isNodeProperty = true)
    (halast : prevRealIdx? a a.size = some i)
    (haclose : a[i]!.val.isFlowClose = true)
    (haopen : flowOpenIdx? a i = some b.size) :
    trailingNodeRun? a = trailingNodeRun? b :=
  trailingNodeRun?_flowClose_reads_park hagree hbprev hbprop halast haclose haopen

/-! ## §2  What the reading is read WITH

`danglingNodePos?` reads two slots — the run's start and its predecessor — and
`trailingNodeRun?_bounds` says both are below the array the reading was taken
on, in every one of the three arms.  That is what lets a reading be transported
by an agreement on a PREFIX, which is what all three pushes above are. -/

example {s t : ScannerState}
    (hflow : s.inFlow = t.inFlow) (hind : s.indents = t.indents)
    (hrun : trailingNodeRun? s.tokens = trailingNodeRun? t.tokens)
    (hagree : ∀ j, j < t.tokens.size → s.tokens[j]! = t.tokens[j]!)
    -- Item 180: the crossed-block clause reads the whole trailing block, so
    -- its own equality rides as a fifth premise.  Item 182: the break-crossing
    -- clause reads the block's own INTERIOR, so its equality is the sixth —
    -- and it is the premise a body push cannot pay, which is why the body
    -- relay below is an implication now rather than an equality.
    (hx : crossedPropsExcessPos? s.tokens = crossedPropsExcessPos? t.tokens)
    (hlc : runLineCrossPos? s.tokens = runLineCrossPos? t.tokens) :
    danglingNodePos? s = danglingNodePos? t :=
  danglingNodePos?_congr hflow hind hrun hagree hx hlc

example {ts : Array (Positioned YamlToken)} {st : Nat} {pred : Option Nat}
    (h : trailingNodeRun? ts = some (st, pred)) :
    st < ts.size ∧ pred = prevRealIdx? ts st :=
  trailingNodeRun?_bounds h

/-! ## §3  The site that could not pay — closed at item 165

Everything below stood when it was written and is kept as the record of WHY the
gate went on `FlowBaseRoutes.value` rather than here.  It is paid now: item 161
supplied the bracket balance as a forward stack, item 162 carried it across the
collection's interior, item 164 landed the conjunct and spent the gate at the
two base closes, and item 165 made this arm open at `some` — over the park
itself when the landing crossed no break, and ungated when it did, where §9.2's
own check pays.

`accum_flow_open_depth0`'s props arm builds `FlowBaseRoutes.value` — the
collection read as the enclosing construct's own node — by applying the park's
`h_route` to a grammar argument:

```
fun sp_ne sp_m h_content h_ssl =>
  h_route sp_m (flowInBlock_blockNode h_sep_run (SFlowNode.propsContent …) h_ssl)
```

Everything that closure receives is GRAMMAR.  There is no scanner state in it,
so a guard on `h_route` cannot be discharged inside it, and the open cannot
discharge it either: at the open the park really is dangling and really does
need the route.

**It needs it because the route is genuinely owed one step later.**  A dangling
`[96]` park that opens a collection has exactly two futures, and they take
different halves of the frame: -/

-- the collection heads an implicit KEY — LEGAL, and served by `resume.key`
#guard (scanOk "a: 1\n&p [b]: c\n", parseOk "a: 1\n&p [b]: c\n")
  == ("SCAN-OK", "PARSE-OK")
-- the collection closes as a VALUE — REFUSED, at the run's own start
#guard scanOk "a: 1\n&p [b]\n"
  == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"

/-! So `resume.value`'s domain at a dangling park holds no accepted input, and
the refusal that empties it is read at the CLOSE — where §1's third measurement
says the verdict is the park's own, unchanged.  The gate therefore belongs on
`FlowBaseRoutes.value`, not on `pendingProps.h_route` alone, and what it is
missing is the hypothesis `trailingNodeRun?_flowClose_reads_park` takes:
`flowOpenIdx? a i = some b.size`, the statement that the close finds ITS open.

That is a fact about the token array's bracket balance, and the balance is
exactly what the flow stack indexes (`FlowOpenStack`'s kinds array mirrors
`sc.flowStack`).  Relating the two is the piece that is missing.

**And the trade is not available.**  Handing the arm the opaque resume instead
would widen `scannerDrop` over an input that is LEGAL — the first `#guard`
above — because the drop would be taken at the OPEN, before the `:` that
decides which half of the frame is spent.  Item 83 deleted the flow open's last
two drop rides; this would put one back, on accepted input. -/

/-! ## §4  What the next item needs

1. ~~`flowOpenIdx? s_cl.tokens i = some s_park.tokens.size` at a depth-0 flow
   close~~ — **item 161**, as `flowOpenIdxStack` read FORWARD.
2. ~~Then `pendingProps.h_route` takes `danglingNodePos? sc = none`, its 23
   sites pay as the table above says, and `ContentRouteGate` loses its right
   disjunct.~~ — **item 165**, with §6.9's length check under it.
3. Behind both, the block landing's own half — `bareNodeRoute_or_refused`'s
   `h_op = true` branch.  ~~Its `-` family is already refused by the scanner
   (`a: 1⏎- x` is `invalidBareDocument 1 0`, `k:⏎␣␣a: 1⏎␣␣- x` is `2,2`), so
   what is left there is the `:`/`?` family, which is LEGAL and routes through
   the key cascade — a CONSUMER to narrow, as item 156 said, not a guard.~~

   **Corrected by item 166.**  Those two inputs are refused, but not for resting
   on an open level: `scanBlockEntryValidate` refuses a `-` at a block MAPPING's
   own indent with no node slot awaited AND no same-indent sequence open.  Lift
   the last conjunct and the `-` family is legal too — `a:⏎- x⏎- y`,
   `- - a⏎- b`, `- a:⏎␣␣␣␣b: 1⏎- c` all scan and parse clean at the same
   landing.  It IS a consumer to narrow, and the route it wants is the open
   collection's continuation.  See `BlockLandingOpenSeq.lean`. -/

#guard scanOk "a: 1\n- x\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOk "k:\n  a: 1\n  - x\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 2 2"
-- …and the same landing with a sequence open at the column (item 166):
#guard (scanOk "a:\n- x\n- y\n", parseOk "a:\n- x\n- y\n") == ("SCAN-OK", "PARSE-OK")
#guard (scanOk "- - a\n- b\n", parseOk "- - a\n- b\n") == ("SCAN-OK", "PARSE-OK")
#guard (scanOk "a: 1\n: v\n", parseOk "a: 1\n: v\n") == ("SCAN-OK", "PARSE-OK")
#guard (scanOk "a: 1\n? k\n", parseOk "a: 1\n? k\n") == ("SCAN-OK", "PARSE-OK")

end L4YAML.Tests.Guards.PropsRunReadingTransport

end Blanket
