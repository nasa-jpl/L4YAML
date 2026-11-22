module

public import L4YAML.Proofs.Production.StreamAccum

public meta import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The bracket balance, read forward — and the gate priced to its ten sites
    (DOCS item 161)

Item 160 landed the `[96]` run's reading across the three pushes onto a park
and found the gate one site short: `accum_flow_open_depth0` builds
`FlowBaseRoutes.value`, a closure with no scanner state in it, so the verdict it
owes can only be read at the CLOSE.  Reading it there needs
`trailingNodeRun?_flowClose_reads_park`, and that lemma holds its own answer as
a hypothesis — `flowOpenIdx? a i = some b.size`, "the close finds ITS open".

This file is that hypothesis, supplied, and the gate it buys, priced.

**Forward, not backward.**  `flowOpenIdx?` walks the token array BACKWARD from
the close, counting closes it has yet to balance.  No step invariant can carry
that: it is a fact about a finished array.  Read FORWARD the same fact is a
STACK — `flowOpenIdxStack`, the indices of the opens not yet closed, innermost
first — and `flowOpenIdxLoop_eq_stack` says the two readings agree at every
depth at once.  A stack is maintained one push at a time, which is what §1
measures and §2 proves: an open conses, a close pops, everything else is inert.

**What it costs to land.**  Guarding `FlowBaseRoutes.value` and building names
**ten** sites, and only one of them is work:

| class | sites | pays with |
|---|---|---|
| `FlowBaseRoutes.ofValue` | 1 | forwards to its own caller |
| the six open arms with a non-park route (doc-suffix ×2, fresh document, bare document, block value, compact entry) | 6 | nothing — the gate is ignored |
| **the props arm** (`h_route`, item 160's §3) | **1** | the park's own verdict |
| the two base closes (`resume.value`) | 2 | §3, from `FlowOpenHeld` |

-/

namespace L4YAML.Tests.Guards.FlowBracketBalance

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

private def stepTo (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepTo s' k
    | _ => none

private def start (input : String) : ScannerState :=
  (ScannerState.mk' input).emit .streamStart

/-! ## §1  The definition, measured against the scanner it mirrors

`flowOpenIdxStack` is a claim about the scanner: that the opens it has not yet
closed are exactly the ones the token array has not yet closed.  The scanner
keeps that count itself, in `flowLevel`, so the claim is checkable at every
step of every input — and a definition that mirrors the wrong thing fails here
rather than in a proof about it.

`balanceWalk` reports the pair at each step; they agree, and the stack names
the indices `flowLevel` only counts. -/

private def balanceWalk (input : String) (n : Nat) : String :=
  String.intercalate " ; " ((List.range n).map fun k =>
    match stepTo (start input) k with
    | none => "—"
    | some s =>
      s!"d={flowTokenDepth s.tokens}/{s.flowLevel} stk={flowOpenIdxStack s.tokens s.tokens.size}")

#guard balanceWalk "[a, [b]]" 9
  == "d=0/0 stk=[] ; d=1/1 stk=[3] ; d=1/1 stk=[3] ; d=1/1 stk=[3] ; \
d=2/2 stk=[10, 3] ; d=2/2 stk=[10, 3] ; d=1/1 stk=[3] ; d=0/0 stk=[] ; —"

-- The indices are the TOKEN array's, so they count the placeholders a simple
-- key reserves: the outer `[` of `[[a], b]` is token 3 and the inner one 6.
#guard balanceWalk "[[a], b]" 10
  == "d=0/0 stk=[] ; d=1/1 stk=[3] ; d=2/2 stk=[6, 3] ; d=2/2 stk=[6, 3] ; \
d=1/1 stk=[3] ; d=1/1 stk=[3] ; d=1/1 stk=[3] ; d=0/0 stk=[] ; — ; —"

/-! ### The exhaustive sweep

The alphabet carries both brackets, both closes, the two separators, a node, a
`[96]` property, and the three things that END a token — space, break, comment
(Reflection 614: adjacency is manufactured by termination, so a sweep whose
alphabet cannot terminate a token measures nothing).

Every input of length ≤ 4 over eleven symbols, checked at every scanner step.
The same sweep at length 6 — 1 771 561 inputs, 1 638 834 steps at item 161's
runtime — was run out of band and also disagreed nowhere; the length checked
HERE is the one CI carries.  Step totals move with the runtime (item 172's
deferred floor lets refused inputs scan further, +50 steps at length 4), so
each pin names the runtime it measures. -/

private def alphabet : List String :=
  ["[", "]", "{", "}", ",", ":", "a", "&p", " ", "\n", "#c\n"]

/-- Steps checked, and whether `flowTokenDepth` and `flowLevel` agreed at each. -/
private def checkSteps (s : ScannerState) : Nat → Nat × Bool
  | 0 => (0, true)
  | fuel + 1 =>
    if flowTokenDepth s.tokens ≠ s.flowLevel then (0, false)
    else
      match scanNextToken s with
      | .ok (some s') =>
        let (n, ok) := checkSteps s' fuel
        (n + 1, ok)
      | _ => (1, true)

private def sweep : Nat → List String → Nat × Nat × Bool
  | 0, acc => acc.foldl (fun (st : Nat × Nat × Bool) input =>
      let (inputs, steps, ok) := st
      let (n, ok') := checkSteps (start input) 4096
      (inputs + 1, steps + n, ok && ok')) (0, 0, true)
  | k + 1, acc =>
    let next := acc.flatMap fun a => alphabet.map fun c => a ++ c
    sweep k next

#guard sweep 1 [""] == (11, 16, true)
#guard sweep 2 [""] == (121, 203, true)
-- [147] glued value: `scanValueValidate` now refuses `a:[`/`a:{` in flow (`flowGluedCollectionValue`),
-- so those inputs stop at the `:` — length 3: 2382 → 2374 steps, length 4: 27193 → 27009; agreement unchanged.
#guard sweep 3 [""] == (1331, 2374, true)
#guard sweep 4 [""] == (14641, 27009, true)

/-! ## §2  The three pushes, proved

An open conses its own index, a close pops the innermost, everything else is
inert — the whole per-step cost of carrying the balance forward. -/

example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (h : p.val.isFlowOpen = true) :
    flowOpenIdxStack (ts.push p) (ts.push p).size
      = ts.size :: flowOpenIdxStack ts ts.size :=
  flowOpenIdxStack_push_open h

example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (h : p.val.isFlowClose = true) :
    flowOpenIdxStack (ts.push p) (ts.push p).size
      = (flowOpenIdxStack ts ts.size).tail :=
  flowOpenIdxStack_push_close h

example {ts : Array (Positioned YamlToken)} {p : Positioned YamlToken}
    (ho : p.val.isFlowOpen = false) (hc : p.val.isFlowClose = false) :
    flowOpenIdxStack (ts.push p) (ts.push p).size = flowOpenIdxStack ts ts.size :=
  flowOpenIdxStack_push_other ho hc

/-- The two readings of the balance are the same reading, at every depth. -/
example (ts : Array (Positioned YamlToken)) (i d : Nat) :
    flowOpenIdxLoop ts d i = (flowOpenIdxStack ts i)[d]? :=
  flowOpenIdxLoop_eq_stack ts i d

/-- A tower's hold rides its own pushes: deeper at a nested open, shallower at a
    nested close, and unmoved by everything between. -/
example {ts : Array (Positioned YamlToken)} {d o : Nat} {S : List Nat}
    {p q : Positioned YamlToken} (h : FlowOpenHeld ts d o S)
    (hp : p.val.isFlowOpen = true) (hq : q.val.isFlowClose = true) :
    FlowOpenHeld ((ts.push p).push q) d o S :=
  (h.push_open hp).push_close hq

/-! ## §3  What it buys: the close's verdict IS the park's

Item 160 measured the equality on the scanner — `a: 1⏎&p [b]` reads `1,0` at
the park and `1,0` again at the `]` — and proved it from a hypothesis it could
not supply.  `FlowOpenHeld` supplies it. -/

/-! The park's own array is 11 tokens when the `[` arrives, so the open lands at
index 11 — `o = s_park.tokens.size`, which is the identity `FlowOpenHeld`
carries. -/

#guard (match stepTo (start "a: 1\n&p [b]\n") 4, stepTo (start "a: 1\n&p [b]\n") 5 with
        | some park, some opened =>
          s!"park.size={park.tokens.size} held={flowOpenIdxStack opened.tokens opened.tokens.size}"
        | _, _ => "—")
  == "park.size=11 held=[11]"

/-! Read at the CLOSE's own index, the stack still names that open — the hold is
at depth 0 there, and the backward walk lands on it. -/

#guard (match stepTo (start "a: 1\n&p [b]\n") 7 with
        | none => "—"
        | some s =>
          match prevRealIdx? s.tokens s.tokens.size with
          | none => "—"
          | some i => s!"close@{i} held={flowOpenIdxStack s.tokens i} open={flowOpenIdx? s.tokens i}")
  == "close@15 held=[11] open=(some 11)"

example {s_park s_bc s_cl : ScannerState} {i k : Nat} {S : List Nat}
    (hflow : s_cl.inFlow = s_park.inFlow)
    (hind : s_cl.indents = s_park.indents)
    (hpark : ∀ j, j < s_park.tokens.size → s_cl.tokens[j]! = s_park.tokens[j]!)
    (hbc : ∀ j, j < s_bc.tokens.size → s_cl.tokens[j]! = s_bc.tokens[j]!)
    (hheld : FlowOpenHeld s_bc.tokens 0 s_park.tokens.size S)
    (hkprev : prevRealIdx? s_park.tokens s_park.tokens.size = some k)
    (hkprop : s_park.tokens[k]!.val.isNodeProperty = true)
    (hlast : prevRealIdx? s_cl.tokens s_cl.tokens.size = some i)
    (hclose : s_cl.tokens[i]!.val.isFlowClose = true)
    (hi : i = s_bc.tokens.size)
    (h_nd : danglingNodePos? s_cl = none) : danglingNodePos? s_park = none := by
  rw [← danglingNodePos?_flowClose_reads_park hflow hind hpark hbc hheld hkprev
    hkprop hlast hclose hi]
  exact h_nd

/-! The refusal this carries is still the one item 160 pinned: the collection
read as the enclosing construct's own VALUE is refused at the run's start, and
the same park read as a KEY is accepted — which is why the verdict has to reach
the close rather than being decided at the open. -/

#guard scanOk "a: 1\n&p [b]\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOk "a: 1\n&p [b]: c\n" == "SCAN-OK"

/-! ## §4  What the next item needs

`FlowBaseRoutes.value` has to take the gate, and the ten sites above are its
price.  The gate is a `Prop` the OPEN chooses and the CLOSE discharges, so it
rides the structure as a parameter — the shape `kc` already has (item 75:
"a PARAMETER, not an index … nests forward it untouched and read nothing from
it").  Six open arms pass `True`, the props arm passes
`danglingNodePos? sc = none`, and the two base closes pay it with §3.

Behind that, the block landing's own half — `bareNodeRoute_or_refused`'s
`h_op = true` branch, ~~whose `-` family the scanner already refuses and whose
`:`/`?` family is legal and routes through the key cascade~~: a CONSUMER to
narrow, as item 156 said, not a guard.  (**Item 166 corrected the reason**: the
`-` family is legal too wherever a sequence is open at the landing's column, and
what the branch wants is that collection's own continuation.  See
`BlockLandingOpenSeq.lean`.) -/

end L4YAML.Tests.Guards.FlowBracketBalance

end Blanket
