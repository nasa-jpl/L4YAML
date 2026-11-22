module

public import L4YAML.Proofs.Production.StreamAccum

public meta import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Output.Events

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The park a flow frame was opened over, anchored across its interior
    (DOCS item 162)

Item 161 read the bracket balance FORWARD and left one thing standing between
`FlowOpenHeld` and the gate it was built for: the hold is a fact about the state
at the CLOSE, and the close is an arbitrary number of steps away from the open
that established it.  This file is the carrier that closes that gap — the
anchor, the five things a scanner step can do to it, and the spend the base
close makes.

**The anchor.**  `ParkAnchor sc0 s d` says three things about `s` and one about
the park `sc0` it was opened over: the array agrees with the park's BELOW the
open; the open is still HELD, `d` nests deep, in `flowOpenIdxStack`; the indent
stack is the park's; and the park itself is out of flow and ends in a `[96]`
property.  `FlowBaseAnchor` lifts it over `Option ScannerState`, so a frame
whose enclosing construct owes an unconditional node reading carries `none` and
pays nothing — six of the ten `FlowBaseRoutes.value` sites item 161 priced.

**The five step shapes.**  §2 proves them against the scanner's own functions
rather than against abstract pushes, because that is what the dispatchers hand
over: `congr` (no token), `pushInert` (one token that is neither bracket),
`pushOpen`, `pushClose`, and `congrKind` — the REWRITE, which is the shape
`ParkAnchor` needs and token equality cannot express.  A simple key's
resolution turns the two slots the save reserved into the
`[187] c-l-block-map-implicit-key` pair; neither the placeholder nor the `key`
that replaces it is a bracket, so the stack is unchanged while the array is
not.  `preprocess` and `adUpdate` are the two silent writers every flow
dispatch passes through, spelled once rather than at each arm.

**What installing it costs, priced by the compiler** (not by a census — see
`ReindexPriceIsTheSignatures`, Reflection 670).  Giving the tower the gate
parameter and `FlowStackK` the anchor conjunct was built and the errors read
off:

| what pays | count | how it pays |
|---|---|---|
| signatures ascribing `FlowBaseRoutes`/`FlowOpenStack`/`FlowStackB` | **46** | one `{g : Option ScannerState}` binder each; every constructor application and every `cases` compiles verbatim |
| `FlowStackK` constructions at depth **0** | ~50 | **nothing** — the conjunct sits under `0 < fl`, which they already discharge by `absurd` |
| `FlowStackK` constructions at POSITIVE depth | **~20** | one of the five shapes above, per arm |
| `FlowBaseRoutes.value` sites | **10** | item 161's table |

So the re-index is 46 signatures and the carrier is ~20 arms; the depth-0
majority is free, which is the same asymmetry item 161 found at the routes.
-/

namespace L4YAML.Tests.Guards.FlowParkAnchor

open L4YAML L4YAML.Scanner L4YAML.Proofs.StreamAccum

private def stepTo (s : ScannerState) : Nat → Option ScannerState
  | 0 => some s
  | k + 1 =>
    match scanNextToken s with
    | .ok (some s') => stepTo s' k
    | _ => none

private def start (input : String) : ScannerState :=
  (ScannerState.mk' input).emit .streamStart

private def scanOk (input : String) : String :=
  match scan input with
  | .ok _ => "SCAN-OK"
  | .error e => s!"SCAN-ERR {repr e}"

/-- The park's own array, read as a prefix test: every slot below the park's
    size still holds the token the park put there. -/
private def agreesBelow (p s : ScannerState) : Bool :=
  (List.range p.tokens.size).all (fun j => s.tokens[j]!.val == p.tokens[j]!.val)

private def row (p s : ScannerState) : String :=
  s!"sz={s.tokens.size} fl={s.flowLevel} stk={flowOpenIdxStack s.tokens s.tokens.size} \
pre={agreesBelow p s}"

/-- The anchor's three carried facts, read at every step from the park on. -/
private def walk (input : String) (park : Nat) (n : Nat) : String :=
  match stepTo (start input) park with
  | none => "—"
  | some p =>
    let rec go (s : ScannerState) (k : Nat) (acc : List String) : List String :=
      match k with
      | 0 => acc.reverse
      | k + 1 =>
        match scanNextToken s with
        | .ok (some s') => go s' k (row p s' :: acc)
        | _ => acc.reverse
    String.intercalate " ; " (row p p :: go p n [])

/-! ## §1  The anchor, measured

The park in `a: 1⏎&p [b, [c]]` is **11** tokens when the `[` arrives, so the
base open lands at index 11 and the nested one at 18.  `stk` is the anchor's
`held` conjunct, `pre` its `below` conjunct, and `fl` the scanner's own depth —
which the stack's LENGTH tracks at every step. -/

#guard walk "a: 1\n&p [b, [c]]\n" 4 8
  == "sz=11 fl=0 stk=[] pre=true ; sz=12 fl=1 stk=[11] pre=true ; \
sz=15 fl=1 stk=[11] pre=true ; sz=16 fl=1 stk=[11] pre=true ; \
sz=19 fl=2 stk=[18, 11] pre=true ; sz=22 fl=2 stk=[18, 11] pre=true ; \
sz=23 fl=1 stk=[11] pre=true ; sz=24 fl=0 stk=[] pre=true"

#guard walk "a: 1\n&p [b]\n" 4 4
  == "sz=11 fl=0 stk=[] pre=true ; sz=12 fl=1 stk=[11] pre=true ; \
sz=15 fl=1 stk=[11] pre=true ; sz=16 fl=0 stk=[] pre=true"

/-! The `{` frame is the same reading: one open at 11, one close back to 0. -/

#guard walk "a: 1\n&p {x: y}\n" 4 5
  == "sz=11 fl=0 stk=[] pre=true ; sz=12 fl=1 stk=[11] pre=true ; \
sz=15 fl=1 stk=[11] pre=true ; sz=16 fl=1 stk=[11] pre=true ; \
sz=19 fl=1 stk=[11] pre=true ; sz=20 fl=0 stk=[] pre=true"

/-! ### §1.1  Why the verdict has to travel, and why the CLOSE cannot decide it

§9.2's reading is `some 1,0` at the park, `none` right through the interior —
a flow is exempt — and `some 1,0` again at the depth-0 close.  That last
reading is the same for the input the scanner REFUSES and the input it accepts:
what separates them is the `:` that arrives one step LATER.  So the gate cannot
be settled at the open (the park is dangling there either way) and it is not
settled by the close's position either: the close hands the verdict to the park
it makes, and that park's own face is what finally pays.  -/

private def verdicts (input : String) (ks : List Nat) : String :=
  String.intercalate " ; " (ks.map (fun k =>
    match stepTo (start input) k with
    | none => "—"
    | some s => s!"{k}:{if (danglingNodePos? s).isSome then "dangling" else "clear"}"))

#guard scanOk "a: 1\n&p [b]\n" == "SCAN-ERR L4YAML.ScanError.invalidBareDocument 1 0"
#guard scanOk "a: 1\n&p [b]: c\n" == "SCAN-OK"

#guard verdicts "a: 1\n&p [b]\n" [4, 5, 6, 7]
  == "4:dangling ; 5:clear ; 6:clear ; 7:dangling"
#guard verdicts "a: 1\n&p [b]: c\n" [4, 5, 6, 7, 8]
  == "4:dangling ; 5:clear ; 6:clear ; 7:dangling ; 8:clear"

/-! ## §2  The five step shapes, against the scanner's own functions

Each `example` is the transport applied to the real scan step, so what is
checked is that the lemma's premises are the facts the dispatcher already has —
not that some abstract push type-checks. -/

/-- A flow OPEN conses its own index: the anchor goes one nest deeper. -/
example {sc0 s : ScannerState} {d : Nat} (h : ParkAnchor sc0 s d) :
    ParkAnchor sc0 (scanFlowSequenceStart s) (d + 1) :=
  h.pushOpen (scanFlowSequenceStart_tokens s) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowSequenceStart_preserves_indents s)

example {sc0 s : ScannerState} {d : Nat} (h : ParkAnchor sc0 s d) :
    ParkAnchor sc0 (scanFlowMappingStart s) (d + 1) :=
  h.pushOpen (scanFlowMappingStart_tokens s) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowMappingStart_preserves_indents s)

/-- A flow CLOSE pops the innermost: one nest back. -/
example {sc0 s : ScannerState} {d : Nat} (h : ParkAnchor sc0 s (d + 1)) :
    ParkAnchor sc0 (scanFlowSequenceEnd s) d :=
  h.pushClose (scanFlowSequenceEnd_tokens s) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowSequenceEnd_preserves_indents s)

example {sc0 s : ScannerState} {d : Nat} (h : ParkAnchor sc0 s (d + 1)) :
    ParkAnchor sc0 (scanFlowMappingEnd s) d :=
  h.pushClose (scanFlowMappingEnd_tokens s) rfl
    (L4YAML.Proofs.EmitterScannability.scanFlowMappingEnd_preserves_indents s)

/-- `,` is INERT — the shape that carries most of the interior. -/
example {sc0 s s' : ScannerState} {d : Nat} (h : ParkAnchor sc0 s d)
    (hfe : scanFlowEntry s = .ok s') : ParkAnchor sc0 s' d :=
  h.pushInert (scanFlowEntry_tokens hfe) rfl rfl
    (L4YAML.Proofs.FlowIndentStable.scanFlowEntry_preserves_indents hfe)

/-- Preprocessing: the walk writes nothing, §6.1's unwind is `!inFlow`-guarded,
    and the save's reservation is two placeholders. -/
example {g : Option ScannerState} {sc s_prep : ScannerState} {c : Char} {d : Nat}
    (h : FlowBaseAnchor g sc d) (h_flow : sc.inFlow = true)
    (hpre : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    FlowBaseAnchor g s_prep d :=
  h.preprocess h_flow hpre

/-- The REWRITE: a resolution that replaces tokens rather than appending them
    still leaves the stack alone, because the stack reads only the two bracket
    predicates.  Token equality cannot state this; `congrKind` can. -/
example {sc0 s s' : ScannerState} {d : Nat} (h : ParkAnchor sc0 s d)
    (hsz : s'.tokens.size = s.tokens.size)
    (hbelow : ∀ j, j < sc0.tokens.size → s'.tokens[j]! = s.tokens[j]!)
    (hkind : ∀ j, j < s.tokens.size →
      s'.tokens[j]!.val.isFlowOpen = s.tokens[j]!.val.isFlowOpen ∧
      s'.tokens[j]!.val.isFlowClose = s.tokens[j]!.val.isFlowClose)
    (hind : s'.indents = s.indents) : ParkAnchor sc0 s' d :=
  h.congrKind hsz hbelow hkind hind

/-! The placeholder a save reserves and the `key` a resolution writes over it
    are both inert, which is what makes `congrKind`'s premise discharge. -/
#guard (YamlToken.placeholder.isFlowOpen, YamlToken.placeholder.isFlowClose,
        YamlToken.key.isFlowOpen, YamlToken.key.isFlowClose,
        YamlToken.blockMappingStart.isFlowOpen, YamlToken.blockMappingStart.isFlowClose)
  == (false, false, false, false, false, false)

#guard (YamlToken.flowSequenceStart.isFlowOpen, YamlToken.flowMappingStart.isFlowOpen,
        YamlToken.flowSequenceEnd.isFlowClose, YamlToken.flowMappingEnd.isFlowClose)
  == (true, true, true, true)

/-! ## §3  The spend

At a depth-0 close the anchor turns the close's own §9.2 verdict into the
PARK's, which is the gate `FlowBaseRoutes.value` was given.  An ungated frame
(`none`) pays nothing, which is what makes the six non-park open arms free. -/

example {g : Option ScannerState} {s_bc s_cl : ScannerState}
    (h : FlowBaseAnchor g s_bc 0)
    (hpre : ∀ j, j < s_bc.tokens.size → s_cl.tokens[j]! = s_bc.tokens[j]!)
    (hind : s_cl.indents = s_bc.indents)
    (hflow : s_cl.inFlow = false)
    (hlast : prevRealIdx? s_cl.tokens s_cl.tokens.size = some s_bc.tokens.size)
    (hclose : s_cl.tokens[s_bc.tokens.size]!.val.isFlowClose = true)
    (hnd : danglingNodePos? s_cl = none)
    (hui : underIndentedFlowValuePos? s_cl = none) : GateOf g :=
  h.gate hpre hind hflow hlast hclose hnd hui

/-- The ungated half, with nothing to supply. -/
example : GateOf none := trivial

/-! ## §4  What remains

The carrier above is complete: every shape a step can take is proved, and the
close's spend with it.  What is left is INSTALLATION — giving
`FlowBaseRoutes`/`FlowOpenStack`/`FlowStackB` the gate parameter (46
signatures), `FlowStackK` the anchor conjunct (~20 positive-depth arms, each
naming which of §2's five shapes it took), and then `pendingProps.h_route` its
own `danglingNodePos? sc = none` — item 160's other 22 sites — after which
`ContentRouteGate` loses its right disjunct and the content landing's bare
route keeps no CHARACTER residue at all. -/

end L4YAML.Tests.Guards.FlowParkAnchor

end Blanket
