/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.CarrierArmPrice

/-!
# What each exit of the second wave hands the content to (DOCS item 247)

Item 246 found that `BlockStack`'s missing arm is honest and that adding it
breaks the two absorptions and, through them, five step lemmas already inside
β.5's bill.  Its recorded NEXT named the number nothing held — **how many of
the second wave's exits can carry an open entry THROUGH** — and warned that a
pass-through by position is not a pass-through by content: content scanned
inside an open entry moves the entry's content boundary without moving the
carrier's position, so a census by position alone would price such an exit as
free.  So the first question here is what each exit hands the content to, and
only the second is where it re-emits.

**§1 is the five's share of the producers.**  Item 246 counted twenty-one
constants whose proof builds `BlockStack.nil`; the share is the subset the
five reach through their proof terms (item 238's `uses`, generated auxiliaries
inlined), and beside it how many of the share sit inside
`DropDependents.expectedTrans`, the twenty-seven β.5 already owes.

**§2 walks every exit.**  An exit is the carrier slot of an accumulation
package: an `And.intro` whose left conjunct has type `BlockStack _ _`.  Over
each producer in the share and each of the five, `Meta.forEachExpr'` visits
the proof term with binders instantiated as fresh free variables, so two exits
in parallel branches are two.  The slot holds either `BlockStack.nil p` —
classified by `p` against the producer's own telescope: its INPUT position
(the target of its `BlockStack` hypothesis, else of its one direct
`SLYamlStream sp_start _` hypothesis), another parameter, a variable bound
inside the proof (an `∃`-witness the step obtained), or a compound — or the
input carrier hypothesis itself, re-emitted.  Every `BlockStack.nil`
application is read beside the slots so a builder handed to a callee outside
a package is not lost.

**§3 asks first what the exit hands the content to.**  From the same
`And.intro`, the right conjunct's value names the park's head — a
`PendingNode` constructor, a park a callee built, or a lemma — and the flow
conjunct's head: `FlowStackB.nil`, or a stack OPENED at this exit, whose base
route is the hand-off instead.  Beside it, a static reading of the ten parks:
which DEMAND the stream at their block position (a premise
`SLYamlStream sp_start sp_block`), which PROMISE it past their content (a
closure ending in `SLYamlStream sp_start _`), and which say nothing of it.

**§4 puts the two readings side by side.**  By position: slots at the input
position against slots at a new one.  By content: exits that build nothing —
the input carrier re-emitted — against exits whose park or flow base promises
or demands the stream at the position they re-emit at, which an open entry
cannot supply.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (usesAll modOf sorted uses expectedTrans)

set_option autoImplicit false

namespace Tests.Guards.ExitHandoff

/-! ## §2 The exit walk -/

/-- The five: item 246's second wave, the absorptions' readers. -/
def five : List Name :=
  [``preprocessing_eof_extends_stream, ``accum_step_structural,
   -- 2026-11-11 (item 484): the absorptions' reader is the renamed body `accum_step_content_core`; the
   -- `accum_step_content` wrapper only re-packs its tuple (see CarrierArmPrice.expectedAbsorbReaders).
   ``accum_flow_open_depth0, ``accum_step_block, ``accum_step_content_core]

/-- One carrier slot of an accumulation package. -/
structure Exit where
  producer : Name
  /-- `nil`; `carrier` (the input carrier hypothesis re-emitted); `forward`
      (a callee's carrier, obtained and re-packaged); else the slot's head. -/
  slot : String
  /-- The stream conjunct beside the slot: `param:<h>` for one of the
      producer's own stream hypotheses, `bound:<h>` for one built inside the
      proof (with `:=<head>` when a `have` bound it), else its head. -/
  stream : String
  /-- `input`, `param`, `bound`, `expr`; empty for a re-emitted carrier. -/
  posClass : String
  /-- The position's own name, or the compound's head. -/
  posName : String
  /-- The park's head: a `PendingNode` constructor's short name, `bound:<x>`
      for a park a callee built, or a lemma's full name. -/
  park : String
  /-- The flow conjunct's head: `nil` for `FlowStackB.nil`, else the name of
      what built the open stack. -/
  flow : String
  deriving Inhabited, Repr

def shortPark (n : Name) : String :=
  if (`L4YAML.Proofs.StreamAccum.PendingNode).isPrefixOf n then
    n.components.getLast!.toString
  else n.toString

/-- Strip the wrappers a park or a stack rides in — binders, casts, `▸`. -/
partial def peel (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .lam _ _ b _ => peel b
  | _ =>
    if e.isAppOfArity ``Eq.mpr 4 || e.isAppOfArity ``Eq.mp 4 || e.isAppOfArity ``cast 4 then
      peel (e.getArg! 3)
    else if e.isAppOfArity ``Eq.ndrec 6 || e.isAppOfArity ``Eq.rec 6 then
      peel (e.getArg! 3)
    else if e.isAppOfArity ``Eq.subst 6 then peel (e.getArg! 5)
    else if e.isAppOfArity ``id 2 then peel (e.getArg! 1)
    else e

/-- The head of a proof, named the way the ledger reads it.  `haves` maps a
    `have`-bound name to the head of what it was bound to; `params` are the
    producer's own hypotheses.  `absurd` and a `nomatch` (a matcher auxiliary
    with no alternatives) both refute a conjunct: `vacuous`. -/
partial def headOf (params : Array Expr) (haves : Std.HashMap Name String) (e : Expr) :
    MetaM String := do
  let e := peel e
  match e.getAppFn with
  | .const n _ =>
    if n == ``absurd || n == ``False.elim || (n.toString.splitOn ".match_").length > 1 then
      return "vacuous"
    return shortPark n
  | .fvar id =>
    let d ← id.getDecl
    let nm := d.userName
    if params.contains e.getAppFn then return s!"param:{nm}"
    match d.value? with
    | some v => return s!"bound:{nm}:={← headOf params haves v}"
    | none =>
      match haves.get? nm with
      | some h => return s!"bound:{nm}:={h}"
      | none => return s!"bound:{nm}"
  | .bvar _ => return "bvar"
  | e => return e.ctorName

/-- Classify a position against the producer's telescope. -/
def classifyPos (params : Array Expr) (input : Option Expr) (p : Expr) :
    MetaM (String × String) := do
  let p := p.consumeMData
  match p with
  | .fvar id =>
    let nm := (← id.getDecl).userName.toString
    if input == some p then return ("input", nm)
    if params.contains p then return ("param", nm)
    return ("bound", nm)
  | _ =>
    match p.getAppFn with
    | .const n _ => return ("expr", n.toString)
    | e => return ("expr", e.ctorName)

/-- The producer's input: its carrier hypothesis and the position it ends at,
    else the target of its one direct stream hypothesis. -/
def inputOf (params : Array Expr) : MetaM (Option Expr × Option Expr × String) := do
  let mut carrier : Option Expr := none
  let mut pos : Option Expr := none
  let mut streams : Array Expr := #[]
  for x in params do
    let t := (← inferType x).consumeMData
    if t.isAppOfArity ``BlockStack 2 then
      carrier := some x; pos := some (t.getArg! 1)
    else if t.isAppOfArity ``SLYamlStream 2 then
      streams := streams.push (t.getArg! 1)
  if pos.isSome then
    return (carrier, pos, s!"{(← pos.get!.fvarId!.getDecl).userName}")
  if streams.isEmpty then return (none, none, "none")
  -- several direct stream hypotheses: the first is the input, the rest are
  -- fallbacks (`h_stream_fallback`), and the count says so
  let p := streams[0]!
  let extra := if streams.size > 1 then s!"(+{streams.size - 1})" else ""
  return (none, some p, s!"{(← p.fvarId!.getDecl).userName}{extra}")

/-- Walk one producer: its exits, and every `BlockStack.nil` it builds. -/
def walk (c : Name) : MetaM (String × Array Exit × Nat) := do
  let some ci := (← getEnv).find? c | throwError "{c}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  lambdaTelescope v fun params body => do
    let (carrier, input, inputName) ← inputOf params
    let exits ← IO.mkRef (#[] : Array Exit)
    let nils ← IO.mkRef (#[] : Array Expr)
    let slotNils ← IO.mkRef (#[] : Array Expr)
    let haves ← IO.mkRef ({} : Std.HashMap Name String)
    forEachExpr' body fun e => do
      if e.isAppOfArity ``BlockStack.nil 1 then
        nils.modify (·.push e)
      -- `have x := v; b` is `letFun v (fun x => b)`: remember what `x` holds
      if e.isAppOfArity ``letFun 4 then
        if let .lam x _ _ _ := (e.getArg! 3).consumeMData then
          let h ← headOf params (← haves.get) (e.getArg! 2)
          haves.modify (·.insert x h)
      -- the package: `⟨stream, carrier, flow, park, …⟩`
      if e.isAppOfArity ``And.intro 4 then
        let A := (e.getArg! 0).consumeMData
        let r := (e.getArg! 3).consumeMData
        if A.isAppOf ``SLYamlStream && r.isAppOfArity ``And.intro 4 &&
            (r.getArg! 0).consumeMData.isAppOf ``BlockStack then
          let hv ← haves.get
          let stream ← headOf params hv (e.getArg! 2)
          let l := (r.getArg! 2).consumeMData
          let r2 := (r.getArg! 3).consumeMData
          let (slot, pc, pn) ←
            if l.isAppOfArity ``BlockStack.nil 1 then
              slotNils.modify (·.push l)
              let (pc, pn) ← classifyPos params input (l.getArg! 0)
              pure ("nil", pc, pn)
            else if carrier == some l then pure ("carrier", "", "")
            else if l.isFVar then pure ("forward", "", "")
            else pure (← headOf params hv l, "", "")
          let flowE := if r2.isAppOfArity ``And.intro 4 then some (r2.getArg! 2) else none
          let flow ← match flowE with
            | some f =>
              let f := peel f
              if f.isAppOf ``FlowStackB.nil then pure "nil"
              else if f.isAppOf ``Exists.intro then pure "K"
              else headOf params hv f
            | none => pure "?"
          let park ← if r2.isAppOfArity ``And.intro 4 then
              let r3 := (r2.getArg! 3).consumeMData
              if r3.isAppOfArity ``And.intro 4 then headOf params hv (r3.getArg! 2) else pure "?"
            else pure "?"
          exits.modify (·.push { producer := c, slot, stream, posClass := pc, posName := pn, park, flow })
      return true
    let ns ← nils.get
    let sn ← slotNils.get
    let loose := ns.filter fun n => !sn.any (· == n)
    return (inputName, ← exits.get, loose.size)

/-- `k:count` pairs, sorted. -/
def tally (xs : Array String) : String := Id.run do
  let mut m : Array (String × Nat) := #[]
  for x in xs do
    match m.findIdx? (·.1 == x) with
    | some i => m := m.modify i fun (k, n) => (k, n + 1)
    | none => m := m.push (x, 1)
  let sortedM := m.qsort (·.1 < ·.1)
  return String.intercalate "," (sortedM.toList.map fun (k, n) => s!"{k}:{n}")

/-! ## §3 The parks' stream reading -/

/-- What a park says about the stream: `demand` (a premise
    `SLYamlStream sp_start sp_block`, the stream AT its block position),
    `promise` (a closure ending in the stream past its content), `none`. -/
def parkReading (c : Name) : MetaM String := do
  let some ci := (← getEnv).find? c | return "MISSING"
  forallTelescope ci.type fun xs concl => do
    let blockPos := concl.getAppArgs[3]!
    let mut demand := false
    let mut promise := false
    for x in xs do
      let t := (← inferType x).consumeMData
      if t.isAppOfArity ``SLYamlStream 2 && t.getArg! 1 == blockPos then demand := true
      else if (t.find? (·.isConstOf ``SLYamlStream)).isSome then promise := true
    return if demand then "demand" else if promise then "promise" else "none"

/-! ## §4 The pins -/

/-- The five's share of the twenty-one producers: every constant reached from
    the five through proof terms whose own proof builds `BlockStack.nil`. -/
def expectedShare : List String :=
  ["L4YAML.Proofs.StreamAccum.absorb_stacksB",
   "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock",
   "L4YAML.Proofs.StreamAccum.accum_block_on_noPending",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent",
   "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented",
   "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented",
   "L4YAML.Proofs.StreamAccum.accum_content_pending",
   "L4YAML.Proofs.StreamAccum.accum_flow_open_depth0",
   "L4YAML.Proofs.StreamAccum.accum_structural_pending",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred",
   "L4YAML.Proofs.StreamAccum.colon_open_map",
   "L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
   "L4YAML.Proofs.StreamAccum.colon_open_map_implicit",
   "L4YAML.Proofs.StreamAccum.colon_open_map_props",
   "L4YAML.Proofs.StreamAccum.compact_open_map",
   "L4YAML.Proofs.StreamAccum.content_dispatch_routed",
   "L4YAML.Proofs.StreamAccum.question_open_map"]

/-- The producers the five do NOT reach. -/
def expectedOutsideShare : List String :=
  ["L4YAML.Proofs.StreamAccum.absorb_stacks",
   "L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2",
   "Tests.Guards.ParkGapProduction.blockStack_refl"]

/-- The share outside `DropDependents.expectedTrans`: lemmas the arm's third
    wave reaches that β.5's bill never counted. -/
def expectedOutsideT : List String :=
  ["L4YAML.Proofs.StreamAccum.absorb_stacksB",
   "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock",
   "L4YAML.Proofs.StreamAccum.accum_block_on_noPending",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent",
   "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented",
   "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred",
   "L4YAML.Proofs.StreamAccum.colon_open_map",
   "L4YAML.Proofs.StreamAccum.colon_open_map_explicit",
   "L4YAML.Proofs.StreamAccum.colon_open_map_implicit",
   "L4YAML.Proofs.StreamAccum.colon_open_map_props",
   "L4YAML.Proofs.StreamAccum.compact_open_map",
   "L4YAML.Proofs.StreamAccum.content_dispatch_routed",
   "L4YAML.Proofs.StreamAccum.question_open_map"]

/-- The ten parks' stream reading. -/
def expectedParks : List String :=
  ["noPending none",
   "pendingBlock promise",
   "pendingBlockContent promise",
   "pendingContent promise",
   "pendingDirective demand",
   "pendingDocEnd none",
   "pendingDocStart promise",
   "pendingFlow demand",
   "pendingMapValue promise",
   "pendingProps promise"]

/-- One line per walked producer: its input position, its slots by kind, the
    positions its `nil`s re-emit at, the parks and flow heads it hands to. -/
-- 2026-11-11 (item 484): the `accum_step_content` row is now `accum_step_content_core`'s, exit for exit (the body was renamed).
def expectedLines : List String :=
  ["absorb_stacks input=sp_block slots=0 nil=0 carrier=0 forward=0 other=0 loose=1 at=[] stream=[] flow=[] parks=[]",
   "absorb_stacksB input=sp_block slots=0 nil=0 carrier=0 forward=0 other=0 loose=1 at=[] stream=[] flow=[] parks=[]",
   "accum_block_on_closeThenBlock input=none slots=2 nil=2 carrier=0 forward=0 other=0 loose=0 at=[bound(sp_a):1,bound(sp_mid):1] stream=[bound:h_stream_a:1,bound:h_stream_new:=param:h_close_pending:1] flow=[nil:2] parks=[pendingBlock:2]",
   "accum_block_on_noPending input=sp_block slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):1] stream=[param:h_stream_block:1] flow=[nil:1] parks=[pendingBlock:1]",
   -- Item 287: its second stream hypothesis, `h_stream_fallback`, retired, so
   -- the input reads unmarked.
   "accum_block_on_pendingBlock input=sp_block slots=3 nil=3 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):3] stream=[param:h_stream_block:3] flow=[nil:3] parks=[pendingBlock:3]",
   "accum_block_on_pendingBlockContent input=sp_block slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):1] stream=[param:h_stream_block:1] flow=[nil:1] parks=[pendingBlock:1]",
   "accum_content_on_pendingBlock_indented input=sp_block slots=4 nil=4 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):4] stream=[param:h_stream_block:4] flow=[nil:4] parks=[pendingBlockContent:3,pendingProps:1]",
   "accum_content_on_pendingMapValue_indented input=sp_block slots=4 nil=4 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):3,param(sp_scan'):1] stream=[bound:h_stream':=param:h_close_old:1,param:h_stream_block:3] flow=[nil:4] parks=[pendingContent:3,pendingProps:1]",
   "accum_content_pending input=sp_block slots=10 nil=10 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):10] stream=[param:h_stream_block:10] flow=[nil:10] parks=[pendingBlockContent:3,pendingContent:5,pendingProps:2]",
   -- Item 285: one more exit, `slot_ride`'s frame — `nil` at the input, over the
   -- bound `h_stream_block`, parking `noPending` — which the three live arms
   -- spend where they spent `drop_ride`'s.
   "accum_flow_open_depth0 input=sp_block slots=8 nil=5 carrier=3 forward=0 other=0 loose=0 at=[bound(sp_mid):1,input(sp_block):4] stream=[bound:h_stream_block:=L4YAML.Proofs.StreamAccum.absorb_stacksB:4,bound:h_stream_mid:=bound:h_close:1,param:h_stream:3] flow=[bound:h_kpkg:=Exists.intro:8] parks=[noPending:8]",
   "accum_step_block input=sp_block slots=7 nil=0 carrier=6 forward=1 other=0 loose=0 at=[] stream=[bound:q1:1,param:h_stream:6] flow=[K:7] parks=[bound:q4:1,vacuous:6]",
   "accum_step_content_core input=sp_block slots=7 nil=0 carrier=6 forward=1 other=0 loose=0 at=[] stream=[bound:q1:1,param:h_stream:6] flow=[K:7] parks=[bound:q4:1,vacuous:6]",
   "accum_step_structural input=sp_block slots=1 nil=0 carrier=0 forward=1 other=0 loose=0 at=[] stream=[bound:q1:1] flow=[K:1] parks=[bound:q4:1]",
   "accum_structural_pending input=sp_block slots=3 nil=3 carrier=0 forward=0 other=0 loose=0 at=[bound(sp_mid):2,input(sp_block):1] stream=[bound:h_stream_mid:=bound:h_close:2,bound:h_stream_old:1] flow=[nil:3] parks=[bound:h_pend':1,bound:h_pend_new:2]",
   "block_dispatch_deferred input=sp_X slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_X):1] stream=[param:h_stream:1] flow=[nil:1] parks=[pendingFlow:1]",
   "colon_open_map input=sp_land slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_land):1] stream=[param:h_stream_land:1] flow=[nil:1] parks=[pendingMapValue:1]",
   "colon_open_map_explicit input=sp_mid slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_mid):1] stream=[param:h_stream_mid:1] flow=[nil:1] parks=[pendingMapValue:1]",
   "colon_open_map_implicit input=sp_block slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):1] stream=[param:h_stream_block:1] flow=[nil:1] parks=[pendingMapValue:1]",
   "colon_open_map_props input=sp_block slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):1] stream=[param:h_stream_block:1] flow=[nil:1] parks=[pendingMapValue:1]",
   "compact_open_map input=sp_block slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_block):1] stream=[param:h_stream_block:1] flow=[nil:1] parks=[pendingMapValue:1]",
   "content_dispatch_routed input=sp_res slots=4 nil=4 carrier=0 forward=0 other=0 loose=0 at=[input(sp_res):4] stream=[param:h_stream_res:4] flow=[nil:4] parks=[pendingContent:2,pendingProps:2]",
   "preprocessing_eof_extends_stream input=sp_block slots=0 nil=0 carrier=0 forward=0 other=0 loose=0 at=[] stream=[] flow=[] parks=[]",
   "question_open_map input=sp_land slots=1 nil=1 carrier=0 forward=0 other=0 loose=0 at=[input(sp_land):1] stream=[param:h_stream_land:1] flow=[nil:1] parks=[pendingMapValue:1]",
   "scan_content_gives_stream_v2 input=none slots=0 nil=0 carrier=0 forward=0 other=0 loose=1 at=[] stream=[] flow=[] parks=[]",
   "blockStack_refl input=b slots=0 nil=0 carrier=0 forward=0 other=0 loose=1 at=[] stream=[] flow=[] parks=[]"]

-- 2026-10-18 (item 285): `slots`, `nil`, `atInput`, `nilStreamBound`, `flowOpen` and
-- `posFree` each +1 and nothing else — the one exit `slot_ride` adds, read six ways.
def expectedLine : String :=
  "producers=21 readers=3 builders=18 share=18 outsideShare=3 shareInT=3 \
shareOutsideT=15 buildersOutsideT=14 nilOutsideT=26 walked=25 slots=62 nil=44 \
carrier=15 forward=3 other=0 loose=4 atInput=38 atParam=1 atBound=5 atExpr=0 \
nilStreamParam=33 nilStreamBound=11 handedNone=0 flowOpen=5 handedPromise=35 \
handedDemand=1 handedBound=3 posFree=53 through=15"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (authored, usesVal) := usesAll env
  let here : Name := `Tests.Guards.ExitHandoff
  -- §1 producers, and the five's share of them
  let mut producers : Array Name := #[]
  for n in authored do
    if here.isPrefixOf n || (`Tests.Guards.CarrierArmPrice).isPrefixOf n then continue
    if (usesVal.getD n {}).contains ``BlockStack.nil then producers := producers.push n
  let mut reach : Std.HashSet Name := {}
  let mut todo : List Name := five
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if reach.contains n then continue
    reach := reach.insert n
    for d in usesVal.getD n {} do
      if !reach.contains d then todo := d :: todo
  let share := sorted (producers.filter reach.contains)
  let shareL := share.toList.map (·.toString)
  let outsideShare := sorted (producers.filter fun n => !reach.contains n)
  let outsideShareL := outsideShare.toList.map (·.toString)
  let outsideT := sorted (share.filter fun n => !expectedTrans.contains n)
  let outsideL := outsideT.toList.map (·.toString)
  -- the producers that READ the carrier: their `cases` leaves `BlockStack.nil`
  -- in an `HEq` binder, a reference and not a construction
  let elim : List Name := [``BlockStack.casesOn, ``BlockStack.rec, ``BlockStack.recOn]
  let readerProducers := sorted (producers.filter fun n => elim.any (usesVal.getD n {}).contains)
  let readerL := readerProducers.toList.map (·.toString)
  let builders := producers.filter fun n => !readerProducers.contains n
  let buildersOutsideT := outsideT.filter builders.contains
  -- §2–§3 the walk: every producer, and the five
  let walked := sorted (producers ++ (five.toArray.filter fun n => !producers.contains n))
  let mut lines : Array String := #[]
  let mut exitLines : Array String := #[]
  let mut all : Array Exit := #[]
  let mut looseTotal := 0
  let mut nilOutsideT := 0
  for c in walked do
    let (inputName, exits, loose) ← walk c
    all := all ++ exits
    looseTotal := looseTotal + loose
    if buildersOutsideT.contains c then
      nilOutsideT := nilOutsideT + (exits.filter (·.slot == "nil")).size
    let short := c.components.getLast!.toString
    let nilE := exits.filter (·.slot == "nil")
    let carrierE := exits.filter (·.slot == "carrier")
    let otherE := exits.filter fun x => x.slot != "nil" && x.slot != "carrier"
    let at_ := tally (nilE.map fun x => s!"{x.posClass}({x.posName})")
    let parks := tally (exits.map (·.park))
    let flows := tally (exits.map (·.flow))
    let streams := tally (exits.map (·.stream))
    let forwardE := exits.filter (·.slot == "forward")
    lines := lines.push s!"{short} input={inputName} slots={exits.size} nil={nilE.size} \
carrier={carrierE.size} forward={forwardE.size} other={otherE.size - forwardE.size} loose={loose} \
at=[{at_}] stream=[{streams}] flow=[{flows}] parks=[{parks}]"
    for x in exits do
      exitLines := exitLines.push s!"  {short}: {x.slot} {x.posClass}({x.posName}) stream={x.stream} flow={x.flow} park={x.park}"
  let linesL := lines.toList
  -- §3 the parks
  let some (.inductInfo pi) := env.find? ``PendingNode | throwError "PendingNode missing"
  let mut parks : Array String := #[]
  for c in pi.ctors do
    parks := parks.push s!"{shortPark c} {← parkReading c}"
  let parksL := (parks.qsort (· < ·)).toList
  -- §4 the two readings
  let nilA := all.filter (·.slot == "nil")
  let carrierA := all.filter (·.slot == "carrier")
  let atInput := nilA.filter (·.posClass == "input")
  let atParam := nilA.filter (·.posClass == "param")
  let atBound := nilA.filter (·.posClass == "bound")
  let atExpr := nilA.filter (·.posClass == "expr")
  let parkOf (x : Exit) : String := x.park
  let reading (p : String) : String :=
    (parksL.find? (·.startsWith (p ++ " "))).map (fun l => (l.drop (p.length + 1)).toString) |>.getD "?"
  let handedNone := nilA.filter fun x => reading (parkOf x) == "none" && x.flow == "nil"
  let handedFlowOpen := nilA.filter fun x => x.flow != "nil"
  let handedPromise := nilA.filter fun x => reading (parkOf x) == "promise"
  let handedDemand := nilA.filter fun x => reading (parkOf x) == "demand"
  let handedBound := nilA.filter fun x => x.park.startsWith "bound:"
  let forwardA := all.filter (·.slot == "forward")
  -- an exit carries the entry THROUGH when it re-emits BOTH inputs: the
  -- carrier hypothesis and the producer's own stream hypothesis
  let through := carrierA.filter fun x => x.stream.startsWith "param:"
  let nilStreamParam := nilA.filter fun x => x.stream.startsWith "param:"
  let nilStreamBound := nilA.filter fun x => x.stream.startsWith "bound:"
  let got := s!"producers={producers.size} readers={readerProducers.size} builders={builders.size} \
share={share.size} outsideShare={outsideShare.size} shareInT={share.size - outsideT.size} \
shareOutsideT={outsideT.size} buildersOutsideT={buildersOutsideT.size} nilOutsideT={nilOutsideT} \
walked={walked.size} \
slots={all.size} nil={nilA.size} carrier={carrierA.size} forward={forwardA.size} \
other={all.size - nilA.size - carrierA.size - forwardA.size} loose={looseTotal} \
atInput={atInput.size} atParam={atParam.size} atBound={atBound.size} atExpr={atExpr.size} \
nilStreamParam={nilStreamParam.size} nilStreamBound={nilStreamBound.size} \
handedNone={handedNone.size} flowOpen={handedFlowOpen.size} handedPromise={handedPromise.size} \
handedDemand={handedDemand.size} handedBound={handedBound.size} \
posFree={atInput.size + carrierA.size} through={through.size}"
  logInfo m!"ExitHandoff {got}\nshare:\n{String.intercalate "\n" shareL}\n\
readers:\n{String.intercalate "\n" readerL}\n\
outsideShare:\n{String.intercalate "\n" outsideShareL}\n\
outsideT:\n{String.intercalate "\n" outsideL}\nparks:\n{String.intercalate "\n" parksL}\n\
lines:\n{String.intercalate "\n" linesL}\nexits:\n{String.intercalate "\n" exitLines.toList}"
  unless readerL == Tests.Guards.CarrierArmPrice.expectedReaders do
    throwError "the readers among the producers are not item 246's readers:\n{String.intercalate "\n" readerL}"
  unless outsideShareL == expectedOutsideShare do
    throwError "the producers outside the share moved:\n{String.intercalate "\n" outsideShareL}"
  unless shareL == expectedShare do
    throwError "the five's share moved:\n{String.intercalate "\n" shareL}"
  unless outsideL == expectedOutsideT do
    throwError "the share outside T moved:\n{String.intercalate "\n" outsideL}"
  unless parksL == expectedParks do
    throwError "the parks' stream reading moved:\n{String.intercalate "\n" parksL}"
  unless linesL == expectedLines do
    throwError "a producer's exits moved:\n{String.intercalate "\n" linesL}"
  unless got == expectedLine do
    throwError "the exit census moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.ExitHandoff
