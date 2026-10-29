/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.StreamCompositions

/-!
# How many of the eighteen one re-routing lemma covers (DOCS item 250)

Item 249 priced the arm's threading at eighteen (shape, composition) pairs
and found that the commonest composition — A, the stream extended by a bare
document that BEGINS at the landing — is reached through three lemmas that
take the stream closed AT the landing.  Under an open entry that stream does
not exist; what exists is the entry's own closure, `[185] s-l+block-indented`
open at the entry's start and promising the stream at the entry's END.  This
module states `rootMapRoute`'s twin over such a closure, reads what its proof
is made of, and counts how many of the eighteen the twin and its entries-level
twin cover by substitution.

**§1** states the twins.  `slotMapRoute` lands the `[187]` entry INSIDE the
open entry's node — `slotLandedMap`, written by item 189 for the value-line
face of a `?` inside a `?`, one column right of the sequence twin because
`[187]` carries no `seq-spaces` — and hands that node to the closure.
`slotMapRouteF` is the same at the entries level with the bottom a parameter,
as `resumeMapRouteF`'s is.  `slotMapRoute_closedFirst` is the failure mode the
mandate named: the entry closed EMPTY on the landing's comments, the stream
so re-derived at the landing, and `rootMapRoute` applied to it.

**§2** reads each twin with item 249's tracer, the entry CLOSURE in the stream
hypothesis's place as the target: the stream constructors on the path from
the closure to the conclusion — none, for a twin that reaches the entry's end
through the entry's own production; A, for one that closed the entry first —
and the node the closure is handed, rendered at the node level.

**§3** re-runs item 249's trace and classes every segment whose composition
is A under at most a resume wrapper by the lemma hop on it: `rootMapRoute`
(the twin substitutes), `rootMapRouteF` (its entries-level twin does), or
`bareNodeRoute` (a completed node under an open entry — a node route no
mapping twin substitutes for).  **§4** asks whether the twin's hypotheses are
in scope where it would be spent: the slot closures among each producer's
hypotheses, classed by whether the slot's start is bound BEHIND the landing
(an open slot: the twin's `h_close`) or AHEAD of it (a slot that opens after
this entry's own `:` line, item 189's), and the funnel every opener's landing
arm is threaded through.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.NodeProduction (SBlockMapEntries_of_compactTail)
open Tests.Guards.DropDependents (sorted)
open L4YAML.Proofs.IndentStackCover (FrameLevel)
open Tests.Guards.ExitHandoff (five)
open Tests.Guards.RouteShapes
open Tests.Guards.StreamCompositions
set_option autoImplicit false

namespace Tests.Guards.OpenEntryRoute

/-! ## §1 The twins -/

/-- **`rootMapRoute`'s twin over an open entry.**  The landed `[187]` entry is
    the open entry's node — `[185]`'s `s-l+block-node(n, block-out)` crossing
    to `SBlockNode (n + 1)`, whose `[187] l+block-mapping` opens at `n + 1 + m`
    with no `seq-spaces` in front of it — and the closure carries it to the
    entry's end.  What the proof needs beyond `rootMapRoute`'s: the slot's
    comments to the landing in `hcol0`'s place, and the side condition
    `n + 1 ≤ k` that says the landing stands strictly inside the entry; what
    it does not need is the stream. -/
lemma slotMapRoute {sp_start sp_x sp_land sp_key : SurfPos} {n k : Nat}
    (hnk : n + 1 ≤ k)
    (h_close : ∀ sp_e, SBlockIndented n .blockOut sp_x sp_e → SLYamlStream sp_start sp_e)
    (h_ssl : SSLComments sp_x sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  fun sp_v h_entry =>
    h_close sp_v (slotLandedMap hnk h_ssl
      (SBlockMapEntries.single k sp_land sp_key sp_v h_ind h_entry))

/-- The entries-level twin, its bottom a parameter as `resumeMapRouteF`'s is:
    the entry and its whole width-`k` tail fill the slot, and what stands
    below is whatever the open entry's own frames say. -/
lemma slotMapRouteF {P : SurfPos → Prop} {sp_x sp_land sp_key : SurfPos} {n k : Nat}
    {ks : List FrameLevel}
    (hnk : n + 1 ≤ k)
    (h_close : ∀ sp_e, SBlockIndented n .blockOut sp_x sp_e → ResumeFrames P ks sp_e)
    (h_ssl : SSLComments sp_x sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e → ResumeFrames P ks sp_e :=
  fun _sp_v h_entry sp_e h_tail =>
    h_close sp_e (slotLandedMap hnk h_ssl
      (SBlockMapEntries_of_compactTail h_ind h_entry h_tail))

/-- `rootMapRouteF`'s literal twin — the stream closure, the frames bottomed
    at `[]`.  It FORGETS the open entry's own level: the honest `ks` under an
    open entry is the outer park's `FrameLevel.map n :: ks'`, which `slotMapRouteF` carries
    and this instance does not. -/
lemma slotMapRouteF_stream {sp_start sp_x sp_land sp_key : SurfPos} {n k : Nat}
    (hnk : n + 1 ≤ k)
    (h_close : ∀ sp_e, SBlockIndented n .blockOut sp_x sp_e → SLYamlStream sp_start sp_e)
    (h_ssl : SSLComments sp_x sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v →
    ∀ sp_e, SCompactMapTail k sp_v sp_e → ResumeFrames (SLYamlStream sp_start) [] sp_e :=
  slotMapRouteF hnk (fun sp_e h => ResumeFrames.bottom sp_e (h_close sp_e h)) h_ssl h_ind

/-- **The failure mode**: the entry closed EMPTY on the landing's comments, the
    stream so re-derived at the landing, and the entry appended to it as a new
    bare document.  Same conclusion; it needs the landing at column 0 and not
    the side condition, because it is the ROOT reading with the entry thrown
    away — and §2 reads it as A. -/
lemma slotMapRoute_closedFirst {sp_start sp_x sp_land sp_key : SurfPos} {n k : Nat}
    (hcol0 : sp_land.col = 0)
    (h_close : ∀ sp_e, SBlockIndented n .blockOut sp_x sp_e → SLYamlStream sp_start sp_e)
    (h_ssl : SSLComments sp_x sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  rootMapRoute hcol0
    (h_close sp_land (SBlockIndented.empty n .blockOut sp_x sp_land h_ssl)) h_ind

/-- **The twin over EITHER context.**  `slotLandedMap`'s proof never reads the
    context — `[196]`'s block mapping is opened at `n + 1 + m` under
    `block-out` and `block-in` alike — so one lemma serves the `?`'s key slot
    and the explicit `:`'s value slot (`block-out`) and an awaited `[184]`
    sequence entry's node (`block-in`, item 193's `entryChainMap`) at the same
    side condition. -/
lemma slotMapRouteC {c : YamlContext} {sp_start sp_x sp_land sp_key : SurfPos} {n k : Nat}
    (hnk : n + 1 ≤ k)
    (h_close : ∀ sp_e, SBlockIndented n c sp_x sp_e → SLYamlStream sp_start sp_e)
    (h_ssl : SSLComments sp_x sp_land)
    (h_ind : SIndent k sp_land sp_key) :
    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v :=
  fun sp_v h_entry =>
    h_close sp_v (SBlockIndented.node n c sp_x sp_v
      (SBlockNode.blockMap (n + 1) c (k - (n + 1)) sp_x sp_x sp_land sp_v (GOpt.none sp_x) h_ssl
        (by
          have h : (n + 1) + (k - (n + 1)) = k := by omega
          rw [h]; exact SBlockMapEntries.single k sp_land sp_key sp_v h_ind h_entry)))

/-! ## §2 The twins, read with the closure as the target -/

def isCtorName (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.ctorInfo _) => true | _ => false

/-- Casts seen through: the payload applied to the extra arguments. -/
partial def peelCasts (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .letE _ _ v b _ => peelCasts (b.instantiate1 v)
  | _ =>
    match e.getAppFn with
    | .const n _ =>
      let args := e.getAppArgs
      match transparent n with
      | some (arity, k) =>
        if k < args.size then peelCasts (mkAppN args[k]! (args.extract arity args.size)).headBeta else e
      | none =>
        if n == ``letFun && args.size ≥ 4 then
          peelCasts (mkAppN (mkApp args[3]! args[2]!) (args.extract 4 args.size)).headBeta
        else e
    | .lam .. => peelCasts e.headBeta
    | _ => e

/-- A derivation at the NODE level: every constructor with its proof arguments,
    a premise by its head, casts seen through, and a lemma unfolded when what
    it builds is a constructor. -/
partial def nodeShape (e : Expr) (depth : Nat) : MetaM String := do
  let e := peelCasts e
  match e with
  | .fvar id =>
    let d ← id.getDecl
    if let some v := d.value? then return ← nodeShape v depth
    return s!"prem:{← typeHead d.type}"
  | .lam .. => return "λ"
  | _ =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n us =>
      let env ← getEnv
      match env.find? n with
      | some (.ctorInfo ci) =>
        let mut parts : Array String := #[]
        for i in [ci.numParams:args.size] do
          if ← isProofArg args[i]! then
            let s ← if depth == 0 then pure "…" else nodeShape args[i]! (depth - 1)
            parts := parts.push s
        if parts.isEmpty then return short2 n
        return s!"{short2 n}({String.intercalate "," parts.toList})"
      | some ci =>
        if n.getRoot == `L4YAML && depth > 0 then
          if let some v := ci.value? (allowOpaque := true) then
            let v := v.instantiateLevelParams ci.levelParams us
            let body := v.beta args
            if let .const h _ := (peelCasts body).getAppFn then
              if isCtorName env h then return ← nodeShape body depth
        let mut parts : Array String := #[]
        for a in args do
          if ← isProofArg a then
            let s ← if depth == 0 then pure "…" else nodeShape a (depth - 1)
            parts := parts.push s
        return s!"lemma:{short n}({String.intercalate "," parts.toList})"
      | none => return "?"
    | .fvar id =>
      let d ← id.getDecl
      if let some v := d.value? then return ← nodeShape (mkAppN v args).headBeta depth
      return s!"prem:{d.userName}(…)"
    | _ => return "?"

/-- Every application of the closure `hc` in `e`, its argument rendered at the
    node level; lemma hops whose arguments carry the closure are unfolded so
    the argument is read where the closure is finally applied. -/
partial def handedTo (hc : FVarId) (e : Expr) (depth : Nat) : MetaM (Array String) := do
  let e := e.consumeMData
  unless e.containsFVar hc do return #[]
  match e with
  | .lam n t b bi => withLocalDecl n bi t fun x => handedTo hc (b.instantiate1 x) depth
  | .forallE n t b bi => withLocalDecl n bi t fun x => handedTo hc (b.instantiate1 x) depth
  | .letE n t v b _ => withLetDecl n t v fun x => handedTo hc (b.instantiate1 x) depth
  | .proj _ _ b => handedTo hc b depth
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      let mut out : Array String := #[]
      if id == hc && args.size ≥ 2 then out := out.push (← nodeShape args[1]! 6)
      for a in args do out := out ++ (← handedTo hc a depth)
      return out
    | .lam .. => handedTo hc e.headBeta depth
    | .const n us =>
      let env ← getEnv
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← handedTo hc (mkAppN args[k]! (args.extract arity args.size)).headBeta depth
      if n == ``letFun && args.size ≥ 4 then
        return ← handedTo hc (mkAppN (mkApp args[3]! args[2]!) (args.extract 4 args.size)).headBeta depth
      if depth < 8 && !(isCtorName env n) then
        if let some ci@(.thmInfo _) := env.find? n then
          if let some v := ci.value? (allowOpaque := true) then
            let v := v.instantiateLevelParams ci.levelParams us
            return ← handedTo hc (v.beta args) (depth + 1)
      let mut out : Array String := #[]
      for a in args do out := out ++ (← handedTo hc a depth)
      return out
    | _ =>
      let mut out : Array String := #[]
      for a in args do out := out ++ (← handedTo hc a depth)
      return out
  | _ => return #[]

/-- One exhibit read: the stream compositions on the closure's paths, whether a
    stream constructor stands on any (the entry closed first), and the nodes
    handed. -/
def traceExhibit (c : Name) : MetaM (Array String × Bool × Array String × Nat) := do
  let some ci := (← getEnv).find? c | throwError "{c}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  lambdaTelescope v fun params body => do
    let mut hc? : Option FVarId := none
    for x in params do
      if (← x.fvarId!.getDecl).userName == `h_close then hc? := some x.fvarId!
    let some hc := hc? | throwError "{c}: no h_close"
    let st ← IO.mkRef ({ reach := ({} : Std.HashSet FVarId).insert hc, collecting := 1 } : TState)
    let cx : TCtx := { producer := c, params, walked := #[], table := {}, st }
    let tg : Targets := ({} : Targets).insert hc (.mk #[#[]] #[] true)
    go cx tg body [] 0
    let s ← st.get
    let comps := distinctS (s.paths.map compOf)
    let closed := s.paths.any fun p => streamCtors p > 0
    let handed := distinctS (← handedTo hc body 0)
    return (comps, closed, handed, s.paths.size)

/-! ## §3 The census: item 249's trace, the A segments classed by their hop -/

def compA : String :=
  "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]"

/-- The `SLYamlStream` constructors (and absorptions) on a segment, leaf first —
    the resume wrappers left out. -/
def streamOnly (p : Array Step) : Array String :=
  p.filterMap fun s => match s with
    | .ctor n _ sh => if n.getPrefix == ``SLYamlStream then some sh else none
    | .via n _ => if isAbsorb n then some "absorb" else none
    | _ => none

def hopsOf (p : Array Step) : Array String :=
  p.filterMap fun s => match s with | .hop n _ => some (short n) | _ => none

def hopClass (hs : Array String) : String :=
  let t1 := hs.any fun h => h == "rootMapRoute" || h == "rootMapRoute_or_refused"
  let t2 := hs.any fun h => h == "rootMapRouteF" || h == "rootMapRouteF_or_refused"
  let nn := hs.any fun h => h == "bareNodeRoute" || h == "bareNodeRoute_or_refused_content"
  match t1, t2, nn with
  | true, false, false => "T1"
  | false, true, false => "T2"
  | false, false, true => "N"
  | false, false, false => "inline"
  | _, _, _ => "multi"

/-- Item 249's trace over the same reach, unchanged. -/
def runTrace : MetaM (TState × Array Name) := do
  let env ← getEnv
  let some (.inductInfo pi) := env.find? ``PendingNode | throwError "PendingNode missing"
  let mut table : Std.HashMap Name (Array Closure) := {}
  for ctor in pi.ctors ++ [``FlowBaseRoutes.mk] do
    let f ← ctorClosures ctor
    table := table.insert ctor f.closures
  let walked := (Tests.Guards.ExitHandoff.expectedShare ++ Tests.Guards.ExitHandoff.expectedOutsideShare).map
    (fun s => s.toName) |>.toArray
  let walked := sorted (walked ++ (five.toArray.filter fun n => !walked.contains n))
  let st ← IO.mkRef ({} : TState)
  let mut done : Array Name := #[]
  let mut todo : List Name := walked.toList
  let mut reach : Array Name := #[]
  while !todo.isEmpty do
    let c := todo.head!
    todo := todo.tail!
    if done.contains c then continue
    done := done.push c
    reach := reach.push c
    let pb ← traceProducer table (walked ++ done ++ todo.toArray) st c
    for b in pb do if !done.contains b then todo := b :: todo
  return (← st.get, reach)

/-! ## §4 Availability: the slot closures in scope, and the funnel -/

/-- Every premise `SBlockIndented _ c s _` in a hypothesis type, under
    ∀/→/∧/∨/∃: its context and whether the slot's start `s` is bound OUTSIDE
    the hypothesis (behind the landing: an open slot) or inside it (ahead). -/
partial def slotPremises (outer : Std.HashSet FVarId) (t : Expr) : MetaM (Array (String × Bool)) := do
  let t := t.consumeMData
  match t with
  | .forallE n d b bi =>
    let d := d.consumeMData
    let mut out : Array (String × Bool) := #[]
    if d.isAppOfArity ``SBlockIndented 4 then
      let ctx := match (d.getArg! 1).consumeMData with | .const cn _ => short cn | _ => "var"
      let behind := match (d.getArg! 2).consumeMData with | .fvar id => outer.contains id | _ => false
      out := out.push (ctx, behind)
    out := out ++ (← slotPremises outer d)
    let rest ← withLocalDecl n bi d fun x => slotPremises outer (b.instantiate1 x)
    return out ++ rest
  | _ =>
    match t.getAppFn with
    | .const n _ =>
      if (n == ``And || n == ``Or) && t.getAppNumArgs == 2 then
        return (← slotPremises outer (t.getArg! 0)) ++ (← slotPremises outer (t.getArg! 1))
      if n == ``Exists && t.getAppNumArgs == 2 then
        match (t.getArg! 1).consumeMData with
        | .lam .. => return ← lambdaTelescope (t.getArg! 1) fun _ body => slotPremises outer body
        | _ => return #[]
      return #[]
    | _ => return #[]

/-- Per producer: the hypotheses carrying an open (behind) slot closure and
    those carrying only an ahead one. -/
def availability (c : Name) : MetaM (Option String × Nat × Nat) := do
  let some ci := (← getEnv).find? c | return (none, 0, 0)
  forallTelescope ci.type fun params _ => do
    let outer : Std.HashSet FVarId := params.foldl (fun s x => s.insert x.fvarId!) {}
    let mut behind : Array String := #[]
    let mut ahead : Array String := #[]
    for x in params do
      let t ← inferType x
      unless ← isProp t do continue
      let ps ← slotPremises outer t
      if ps.isEmpty then continue
      let nm := (← x.fvarId!.getDecl).userName.toString
      let ctxs := String.intercalate "/" (distinctS (ps.map (·.1))).toList
      if ps.any (·.2) then behind := behind.push s!"{nm}:{ctxs}" else ahead := ahead.push s!"{nm}:{ctxs}"
    if behind.isEmpty && ahead.isEmpty then return (none, 0, 0)
    return (some s!"{short c}: behind=[{String.intercalate ", " behind.toList}] ahead=[{String.intercalate ", " ahead.toList}]",
            behind.size, ahead.size)

/-- The arity of an application that supplies every hypothesis up to `last`
    — measured that way because a lemma whose conclusion is itself a `∀`
    (`slotChainMap`'s) has more binders than hypotheses. -/
def arityUpTo (n : Name) (last : Name) : MetaM Nat := do
  let some ci := (← getEnv).find? n | throwError "{n}: missing"
  let names := ci.type.getForallBinderNames.toArray
  let some i := names.findIdx? (· == last) | throwError "{n}: no binder {last}"
  return i + 1

/-- The funnel: every full application of `indicator_open_map` in the reach,
    with its `h_explUp_chain` argument paid (built through `slotChainMap`) or
    punted; and the counts of the openers' and `slotChainMap`'s applications. -/
def funnel (reach : Array Name) : MetaM (Array String × Nat × Nat × Nat × Nat) := do
  let env ← getEnv
  let some ciI := env.find? ``indicator_open_map | throwError "indicator_open_map missing"
  let names := ciI.type.getForallBinderNames.toArray
  let arityI := names.size
  let some idx := names.findIdx? (· == `h_explUp_chain) | throwError "no h_explUp_chain"
  let arityQ ← arityUpTo ``question_open_map `h_top_in
  let arityC ← arityUpTo ``colon_open_map `h_resV_land
  let arityS ← arityUpTo ``slotChainMap `up
  let arityE ← arityUpTo ``entryChainMap `up
  let lines ← IO.mkRef (#[] : Array String)
  let q ← IO.mkRef 0
  let cc ← IO.mkRef 0
  let sc ← IO.mkRef 0
  let ec ← IO.mkRef 0
  for c in reach do
    let some ci := env.find? c | continue
    let some v := ci.value? (allowOpaque := true) | continue
    forEachExpr' v fun e => do
      if let .const n _ := e.getAppFn then
        let k := e.getAppNumArgs
        if n == ``indicator_open_map && k == arityI then
          let a := e.getArg! idx
          let kind := if (a.find? (·.isConstOf ``slotChainMap)).isSome then "paid:slotChainMap"
            else if (a.find? (·.isConstOf ``entryChainMap)).isSome then "paid:entryChainMap"
            else if a.isAppOf ``Or.inr then "punted" else "other"
          lines.modify (·.push s!"{short c} → indicator_open_map: h_explUp_chain {kind}")
        if n == ``question_open_map && k == arityQ then q.modify (· + 1)
        if n == ``colon_open_map && k == arityC then cc.modify (· + 1)
        if n == ``slotChainMap && k == arityS then sc.modify (· + 1)
        if n == ``entryChainMap && k == arityE then ec.modify (· + 1)
      return true
  return (← lines.get, ← q.get, ← cc.get, ← sc.get, ← ec.get)

/-! ## §5 The pins -/

def exhibits : List Name :=
  [``slotMapRoute, ``slotMapRouteF, ``slotMapRouteF_stream, ``slotMapRoute_closedFirst, ``slotMapRouteC]

-- Item 304: the value-line rows respell `Resume(_)▹…` → `Key(_)▹…` and their bottom
-- `KeyFrames.bottom` — the stacks are `KeyFrames` (item 302's), as `RouteShapes` renders them.
def expectedExhibits : List String :=
  ["slotMapRoute ⟶ (fact) ⊢ SBlockIndented.node(SBlockNode.blockMap(GOpt.none,prem:SSLComments,SBlockMapEntries.single(prem:SIndent,prem:SBlockMapEntry))) paths=1",
   "slotMapRouteF ⟶ (fact) ⊢ SBlockIndented.node(SBlockNode.blockMap(GOpt.none,prem:SSLComments,lemma:SBlockMapEntries_of_compactTail(prem:SIndent,prem:SBlockMapEntry,prem:SCompactMapTail))) paths=1",
   "slotMapRouteF_stream ⟶ ResumeFrames.bottom[S] ⊢ SBlockIndented.node(SBlockNode.blockMap(GOpt.none,prem:SSLComments,lemma:SBlockMapEntries_of_compactTail(prem:SIndent,prem:SBlockMapEntry,prem:SCompactMapTail))) paths=1",
   "slotMapRoute_closedFirst ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ⊢ SBlockIndented.empty(prem:SSLComments) paths=1 CLOSED-FIRST",
   "slotMapRouteC ⟶ (fact) ⊢ SBlockIndented.node(SBlockNode.blockMap(GOpt.none,prem:SSLComments,SBlockMapEntries.single(prem:SIndent,prem:SBlockMapEntry))) paths=1"]
-- 2026-10-29 (item 388): the mapping park's `h_close` / `h_closeF` rows read `SBlockNode(_+1,blockOut)` (the grammar's `[187]` context).
def expectedAPlain : List String :=
  [ "question_open_map:pendingMapValue.h_close [SBlockNode(_+1,blockOut) ⇒ Stream] T1 hops=rootMapRoute,rootMapRoute_or_refused",
    "question_open_map:pendingMapValue.h_ivl [[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream] T1 hops=rootMapRoute,rootMapRoute_or_refused",
    "question_open_map:pendingMapValue.h_vslot [[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream] T1 hops=rootMapRoute,rootMapRoute_or_refused",
    "question_open_map:pendingMapValue.h_closeF [SBlockNode(_+1,blockOut) ⇒ Resume(map(_)::_)▹Stream] T2 hops=rootMapRouteF,rootMapRouteF_or_refused",
    "question_open_map:pendingMapValue.h_frames [SSLComments ⇒ Resume(_)▹Stream] T2 hops=rootMapRouteF,rootMapRouteF_or_refused",
    "colon_open_map:pendingMapValue.h_close [SBlockNode(_+1,blockOut) ⇒ Stream] T1 hops=rootMapRoute,rootMapRoute_or_refused",
    "colon_open_map:pendingMapValue.h_closeF [SBlockNode(_+1,blockOut) ⇒ Resume(map(_)::_)▹Stream] T2 hops=rootMapRouteF,rootMapRouteF_or_refused",
    "colon_open_map:pendingMapValue.h_frames [SSLComments ⇒ Resume(_)▹Stream] T2 hops=rootMapRouteF,rootMapRouteF_or_refused",
    "content_dispatch_after_close→content_dispatch_routed.h_route [SBlockNode(0,blockIn) ⇒ Stream] N hops=bareNodeRoute",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "question_open_map:pendingMapValue.h_expl [SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Stream] T2 hops=rootMapRouteF,rootMapRouteF_or_refused",
   "question_open_map:pendingMapValue.h_kslot [SBlockNode(_+1,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream] T2 hops=rootMapRouteF,rootMapRouteF_or_refused,one",
   "question_open_map:pendingMapValue.h_closeFV [SBlockNode(_+1,blockIn) ⇒ Key(_)▹ExplValueLine(_)] T2 hops=rootMapRouteF,rootMapRouteF_or_refused,one",
   "question_open_map:pendingMapValue.h_framesV [SSLComments ⇒ Key(_)▹ExplValueLine(_)] T2 hops=rootMapRouteF,rootMapRouteF_or_refused,one"]
-- 2026-10-29 (item 388): the two mapping-park pairs (T1/T2) open on `SBlockNode(_+1,blockOut)`.
def expectedAPairs : List String :=
  [ "SBlockNode(0,blockIn) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ⟵ N",
    "SBlockNode(_+1,blockOut) ⇒ Resume(map(_)::_)▹Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S] ⟵ T2",
    "SBlockNode(_+1,blockOut) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ⟵ T1",
    "SSLComments ⇒ Resume(_)▹Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S] ⟵ T2",
    "[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ⟵ T1",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ⟵ T2",
   "SBlockNode(_+1,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ⟵ T2",
   "SBlockNode(_+1,blockIn) ⇒ Key(_)▹ExplValueLine(_) ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S] ⟵ T2",
   "SSLComments ⇒ Key(_)▹ExplValueLine(_) ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S] ⟵ T2"]
def expectedAvail : List String :=
  [ "accum_block_on_closeThenBlock: behind=[h_vslot:blockOut] ahead=[h_vpack:blockOut]",
    -- 2026-10-26 (item 369): `h_closeF_old:blockIn` joins the binders behind the landing — `pendingBlock.h_closeF`
    -- threaded so the `:`/`?` landing pays `indicator_open_map`'s `h_res_land` off the park's frames.
    "accum_block_on_pendingBlock: behind=[h_close_entry_old:blockIn, h_kslot:blockIn/blockOut, h_seqF_old:blockIn, h_kslotUp:blockIn/blockOut, h_closeFV_old:blockIn, h_closeF_old:blockIn] ahead=[]",
    "accum_block_on_pendingBlockContent: behind=[] ahead=[h_kslot:blockOut, h_kslotUp:blockOut]",
    "accum_block_on_pendingContent: behind=[] ahead=[h_vpack:blockOut]",
    "accum_content_on_pendingBlock_indented: behind=[h_close_old:blockIn, h_close_entry_old:blockIn, h_kslot_old:blockIn/blockOut, h_closeF_old:blockIn, h_seqF_old:blockIn, h_kslotUp_old:blockIn/blockOut, h_closeFV_old:blockIn] ahead=[]",
    "accum_content_on_pendingMapValue_indented: behind=[h_vslot:blockOut, h_ivl_mv:blockOut] ahead=[h_kslot:blockOut]",
    "colon_open_map_explicit: behind=[] ahead=[hvp:blockOut]",
    "compact_open_map: behind=[h_close_old:var] ahead=[]",
    "colon_open_map_implicit: behind=[] ahead=[h_kslotD:blockOut]",
    "colon_open_map_props: behind=[] ahead=[h_kslotD:blockOut]",
    "indicator_open_map: behind=[] ahead=[h_explUp_chain:blockOut, h_explUp_chainD:blockOut]",
    "question_open_map: behind=[] ahead=[h_explUp_chain:blockOut, h_explUp_chainD:blockOut]"]
def expectedFunnel : List String :=
  ["accum_block_on_closeThenBlock → indicator_open_map: h_explUp_chain paid:slotChainMap",
   "accum_block_on_noPending → indicator_open_map: h_explUp_chain punted",
   "accum_block_on_pendingBlock → indicator_open_map: h_explUp_chain paid:entryChainMap",
   "accum_block_on_pendingBlockContent → indicator_open_map: h_explUp_chain punted"]
-- 2026-10-24 (B3 [66] col-0 threading): follows StreamCompositions — the content/block parks close from `sp_gram`.
def expectedLine : String :=
-- Item 371 (t1Pairs=6 → 2, t1Sites=8 → 4, t2Pairs=2 → 6, t2Sites=4 → 8, covered1=6 → 2): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
  "aPairs=9 aSites=13 t1Pairs=2 t1Sites=4 t2Pairs=6 t2Sites=8 nPairs=1 nSites=1 multi=0 inline=0 covered1=2 covered2=8 stackedPairs=0 stackedNoDrop=0 nonA=10 nonANoDrop=8 pairs21=19 pairs18=17 sites=20 pairs=20 exhibits=5 closedFirst=1 handedNode=4 avail=12 behindLemmas=5 behindOpeners=0 aheadOpeners=2 funnelApps=4 paid=2 punted=2 other=0 chainApps=3 entryApps=5 qApps=1 cApps=1 reach=38"

/-! ## §6 The reading -/

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- §2 the exhibits
  let mut exLines : Array String := #[]
  let mut closedFirst := 0
  let mut handedNode := 0
  for c in exhibits do
    let (comps, closed, handed, n) ← traceExhibit c
    if closed then closedFirst := closedFirst + 1
    if handed.any (fun h => h.startsWith "SBlockIndented.node(") then handedNode := handedNode + 1
    exLines := exLines.push s!"  {short c} ⟶ {String.intercalate " | " comps.toList} ⊢ {String.intercalate " | " handed.toList} paths={n}{if closed then " CLOSED-FIRST" else ""}"
  -- §3 the census
  let (s, reach) ← runTrace
  let mut segs : Array Tests.Guards.StreamCompositions.Found := #[]
  for f in s.found do
    if !segs.any (fun g => g.site == f.site && g.seg == f.seg) then segs := segs.push f
  let genuine := segs.filter fun f => compOf f.seg != "(via)"
  let sites := distinctS (genuine.map (·.site))
  let pairOf (site : String) : String :=
    if (site.splitOn "→").length > 1 then (site.splitOn "→")[1]! else site
  let pairs := distinctS (sites.map pairOf)
  let mut shapeComps : Array String := #[]
  for f in genuine do
    for sp in f.spine.splitOn " | " do
      let sc := s!"{sp} ⟶ {compOf f.seg}"
      if !shapeComps.contains sc then shapeComps := shapeComps.push sc
  let noDrop := shapeComps.filter fun sc => (sc.splitOn "scannerDrop").length == 1
  -- the A segments
  let aPlain := genuine.filter fun f => streamOnly f.seg == #[compA]
  let stackedA := genuine.filter fun f => let so := streamOnly f.seg; so.size ≥ 2 && so.back? == some compA
  let aSites := distinctS (aPlain.map (·.site))
  let mut aLines : Array String := #[]
  let mut pairClass : Array (String × String) := #[]
  for site in aSites do
    let here := aPlain.filter (·.site == site)
    let classes := distinctS (here.map fun f => hopClass (hopsOf f.seg))
    let hops := distinctS (here.foldl (fun acc f => acc ++ hopsOf f.seg) #[])
    aLines := aLines.push s!"  {site} [{here[0]!.spine}] {String.intercalate "/" classes.toList} hops={String.intercalate "," hops.toList}"
    for f in here do
      for sp in f.spine.splitOn " | " do
        let pr := s!"{sp} ⟶ {compOf f.seg}"
        let cl := hopClass (hopsOf f.seg)
        if !pairClass.contains (pr, cl) then pairClass := pairClass.push (pr, cl)
  let aPairs := distinctS (pairClass.map (·.1))
  let classOfPair (pr : String) : String :=
    let cls := distinctS ((pairClass.filter (·.1 == pr)).map (·.2))
    if cls.size == 1 then cls[0]! else "multi"
  let aPairLines := (aPairs.qsort (· < ·)).map fun pr => s!"  {pr} ⟵ {classOfPair pr}"
  let count (cl : String) : Nat × Nat :=
    ((aPairs.filter fun pr => classOfPair pr == cl).size,
     (aSites.filter fun site => (distinctS ((aPlain.filter (·.site == site)).map fun f => hopClass (hopsOf f.seg))) == #[cl]).size)
  let (t1P, t1S) := count "T1"
  let (t2P, t2S) := count "T2"
  let (nP, nS) := count "N"
  let multi := (aPairs.filter fun pr => classOfPair pr == "multi").size
  let inline := (aPlain.filter fun f => hopClass (hopsOf f.seg) == "inline").size
  let mut stackedPairs : Array String := #[]
  for f in stackedA do
    for sp in f.spine.splitOn " | " do
      let pr := s!"{sp} ⟶ {compOf f.seg}"
      if !stackedPairs.contains pr then stackedPairs := stackedPairs.push pr
  let stackedNoDrop := stackedPairs.filter fun pr => (pr.splitOn "scannerDrop").length == 1
  let nonA := shapeComps.filter fun sc => !aPairs.contains sc && !stackedPairs.contains sc
  let nonANoDrop := nonA.filter fun sc => (sc.splitOn "scannerDrop").length == 1
  -- §4 availability and the funnel
  let mut availLines : Array String := #[]
  let mut behindOpeners := 0
  let mut aheadOpeners := 0
  let mut behindLemmas := 0
  for c in sorted reach do
    let (l?, b, a) ← availability c
    if let some l := l? then availLines := availLines.push s!"  {l}"
    if b > 0 then behindLemmas := behindLemmas + 1
    if c == ``question_open_map || c == ``colon_open_map then
      behindOpeners := behindOpeners + b
      aheadOpeners := aheadOpeners + a
  let (fLines, qApps, cApps, chainApps, entryApps) ← funnel reach
  let paid := (fLines.filter fun l => (l.splitOn " paid:").length > 1).size
  let punted := (fLines.filter fun l => (l.splitOn " punted").length > 1).size
  let other := (fLines.filter fun l => (l.splitOn " other").length > 1).size
  let got := s!"aPairs={aPairs.size} aSites={aSites.size} t1Pairs={t1P} t1Sites={t1S} t2Pairs={t2P} t2Sites={t2S} \
nPairs={nP} nSites={nS} multi={multi} inline={inline} covered1={t1P} covered2={t1P + t2P} \
stackedPairs={stackedPairs.size} stackedNoDrop={stackedNoDrop.size} nonA={nonA.size} nonANoDrop={nonANoDrop.size} \
pairs21={shapeComps.size} pairs18={noDrop.size} sites={sites.size} pairs={pairs.size} \
exhibits={exLines.size} closedFirst={closedFirst} handedNode={handedNode} \
avail={availLines.size} behindLemmas={behindLemmas} behindOpeners={behindOpeners} aheadOpeners={aheadOpeners} \
funnelApps={fLines.size} paid={paid} punted={punted} other={other} chainApps={chainApps} entryApps={entryApps} qApps={qApps} cApps={cApps} reach={reach.size}"
  logInfo s!"OpenEntryRoute {got}"
  logInfo s!"exhibits:\n{String.intercalate "\n" exLines.toList}"
  logInfo s!"aPlain:\n{String.intercalate "\n" aLines.toList}"
  logInfo s!"aPairs:\n{String.intercalate "\n" aPairLines.toList}"
  logInfo s!"stacked: {String.intercalate " ;; " stackedPairs.toList}"
  logInfo s!"nonA:\n{String.intercalate "\n" ((nonA.qsort (· < ·)).map ("  " ++ ·)).toList}"
  logInfo s!"avail:\n{String.intercalate "\n" availLines.toList}"
  logInfo s!"funnel:\n{String.intercalate "\n" (fLines.map ("  " ++ ·)).toList}"
  -- the cross-instrument check: item 249's frame, re-derived here
  -- (2026-10-24, B3 [66] col-0 threading: 23/21/21/18 → 19/19/18/16, as StreamCompositions pins)
  unless sites.size == 20 && pairs.size == 20 && shapeComps.size == 19 && noDrop.size == 17 do
    throwError "item 249's frame moved under this pass: sites={sites.size} pairs={pairs.size} shapeComps={shapeComps.size} noDrop={noDrop.size}"
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedExhibits" exLines expectedExhibits
  check "expectedAPlain" aLines expectedAPlain
  check "expectedAPairs" aPairLines expectedAPairs
  check "expectedAvail" availLines expectedAvail
  check "expectedFunnel" (fLines.map ("  " ++ ·)) expectedFunnel
  unless got == expectedLine do
    throwError "OpenEntryRoute moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.OpenEntryRoute
