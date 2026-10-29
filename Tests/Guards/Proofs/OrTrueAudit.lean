/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.RelaySupplyCensus

/-!
# The `∨ True` audit (DOCS item 395)

The owner's directive on item 394: *fix all `∨ True` — I do not want to carry any such
risk.*  A statement of the shape `P ∨ True` is unfalsifiable at the type: `Or.inr trivial`
proves it, so a green build says nothing about `P`, and only the censuses' pins keep the
informative side honest.  `PackAlt sc` and `PackAltG g` are `True` by definition (item 311),
so `∨ PackAlt …` is the same shape under a name.

This guard is the roster the retirement lane works from.  It is read off the environment,
not off a grep:

* **positions** — every `∨` whose right alternative is `True` / `PackAlt _` / `PackAltG _`
  in the TYPE of any authored constant of any `L4YAML.*` module (a lemma's binder or
  conclusion, a constructor's field, a `Prop` definition's body), keyed by declaration and
  binder; `top` when the binder's own type is the disjunction, `nested` when it sits inside
  a binder's statement;
* **supply** — for every `top` position declared in `StreamAccum`, what the module's own
  applications put there, read through `RelaySupplyCensus.edges` (`PAY` / `DECLINE` /
  `RELAY` / `VIA` / `FIELD` / `SPLIT`): `paid` when at least one `PAY` reaches it,
  `relayed` when only relays and splits do, `declined-only` when every edge is an
  `Or.inr`, `never-supplied` when no application in the module fills it;
* **writers** — every declaration whose value writes `Or.inr trivial` (or `Or.inr True.intro`),
  with the count.

Every pin is **shrink-only**: a retirement item re-pins a position DOWN with its
disposition (paid, refuted, restated); a position that appears needs the owner's word
in the item that adds it.
-/

namespace Tests.Guards.OrTrueAudit

open Lean Elab Command Meta
open L4YAML.Tests.Guards.RelaySupplyCensus (edges Edge isMechanism ns)

/-- The vacuous alternatives, by name. -/
def altOf (e : Expr) : Option String :=
  if e.isAppOfArity ``Or 2 then
    let r := e.getArg! 1
    if r.isConstOf ``True then some "True"
    else if r.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt then some "PackAlt"
    else if r.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG then some "PackAltG"
    else none
  else none

structure Pos where
  decl : String
  site : String
  kind : String
  alt : String
  module : String
deriving Inhabited

def shown (n : Name) : String :=
  let n := n.eraseMacroScopes
  if n.isAnonymous then "_" else n.toString

/-- Every vacuous `∨` INSIDE a statement. -/
partial def walkNested (decl site modName : String) : Expr → StateT (Array Pos) MetaM Unit
  | e => do
    let e := e.consumeMData
    match e with
    | .forallE n t b bi => do
        walkNested decl site modName t
        withLocalDecl n bi t fun x => walkNested decl site modName (b.instantiate1 x)
    | .lam n t b bi => do
        walkNested decl site modName t
        withLocalDecl n bi t fun x => walkNested decl site modName (b.instantiate1 x)
    | .letE _ t v b _ => do
        walkNested decl site modName t; walkNested decl site modName v; walkNested decl site modName b
    | .proj _ _ s => walkNested decl site modName s
    | .app .. => do
        if let some a := altOf e then
          modify (·.push { decl, site, kind := "nested", alt := a, module := modName })
        e.withApp fun f args => do
          if f.isLambda then walkNested decl site modName f
          for a in args do walkNested decl site modName a
    | _ => pure ()

/-- The leading binders of a type are its FIELDS (ordinal + name); the rest is `[ret]`. -/
partial def walkFields (decl modName : String) (i : Nat) : Expr → StateT (Array Pos) MetaM Unit
  | e => do
    let e := e.consumeMData
    match e with
    | .forallE n t b bi => do
        let site := s!"[{i}].{shown n}"
        match altOf t with
        | some a =>
            modify (·.push { decl, site, kind := "top", alt := a, module := modName })
            walkNested decl site modName (t.getArg! 0)
        | none => walkNested decl site modName t
        withLocalDecl n bi t fun x => walkFields decl modName (i + 1) (b.instantiate1 x)
    | _ =>
        match altOf e with
        | some a =>
            modify (·.push { decl, site := "[ret]", kind := "top", alt := a, module := modName })
            walkNested decl "[ret]" modName (e.getArg! 0)
        | none => walkNested decl "[ret]" modName e

def isGenerated (n : Name) : Bool :=
  match n with
  | .str _ s => s ∈ ["below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn",
      "noConfusion", "noConfusionType", "inj", "injEq", "sizeOf_spec", "ctorIdx", "ctorElim",
      "mk.injEq", "mk.inj", "mk.sizeOf_spec"] || s.startsWith "match_" || s.startsWith "proof_"
      || s.startsWith "_eq_" || s.startsWith "eq_" || s.startsWith "_unfold" || s.startsWith "_sunfold"
  | _ => false

/-- The authored constants of the `L4YAML.*` modules, with their module. -/
def authored : MetaM (Array (Name × Name)) := do
  let env ← getEnv
  let mut out : Array (Name × Name) := #[]
  for (nm, ci) in env.constants.toList do
    let un := Lean.privateToUserName nm
    if un.isInternal || un.isInternalDetail || isGenerated un then continue
    let some m := (env.getModuleIdxFor? nm).map (env.header.moduleNames[·.toNat]!) | continue
    unless (`L4YAML).isPrefixOf m do continue
    if env.isProjectionFn nm || isMechanism env nm then continue
    match ci with
    | .ctorInfo _ | .recInfo _ | .quotInfo _ => continue
    | _ => pure ()
    if isAuxRecursor env nm || isNoConfusion env nm then continue
    out := out.push (nm, m)
  return out.qsort (fun a b => a.1.toString < b.1.toString)

def positionsOf (nm m : Name) : MetaM (Array Pos) := do
  let env ← getEnv
  let some ci := env.find? nm | return #[]
  let decl := (Lean.privateToUserName nm).toString
  let (_, rows) ← (do
    walkFields decl m.toString 0 ci.type
    match ci with
    | .inductInfo ind =>
        for ctor in ind.ctors do
          let some cci := env.find? ctor | continue
          forallBoundedTelescope cci.type (some ind.numParams) fun _ body =>
            walkFields s!"{decl}.{ctor.getString!}" m.toString ind.numParams body
    | .defnInfo d =>
        if ← forallTelescopeReducing d.type fun _ b => pure b.isProp then
          forallTelescope d.type fun xs _ => do
            let body := (d.value.beta xs).headBeta
            walkNested decl "body" m.toString body
    | _ => pure ()).run #[]
  return rows

/-- `Or.inr trivial` / `Or.inr True.intro` written in a value — each DISTINCT subterm visited
    once (proof terms are DAGs; an uncached walk is exponential on them). -/
partial def inrTrivialGo (e : Expr) : StateM (Std.HashSet Expr × Nat) Unit := do
  if (← get).1.contains e then return
  modify fun (seen, n) => (seen.insert e, n)
  match e with
  | .app .. =>
      let hd := e.getAppFn
      let args := e.getAppArgs
      if hd.isConstOf ``Or.inr && args.size == 3 &&
          (args[2]!.isConstOf ``trivial || args[2]!.isConstOf ``True.intro) then
        modify fun (seen, n) => (seen, n + 1)
      inrTrivialGo hd
      for a in args do inrTrivialGo a
  | .lam _ t b _ => do inrTrivialGo t; inrTrivialGo b
  | .forallE _ t b _ => do inrTrivialGo t; inrTrivialGo b
  | .letE _ t v b _ => do inrTrivialGo t; inrTrivialGo v; inrTrivialGo b
  | .mdata _ e => inrTrivialGo e
  | .proj _ _ e => inrTrivialGo e
  | _ => pure ()

def inrTrivial (e : Expr) : Nat := ((inrTrivialGo e).run ({}, 0)).2.2

def posLine (p : Pos) : String := s!"{p.decl}{p.site} {p.kind} ∨ {p.alt}"

/-! ## The pins -/

-- 2026-10-29 (item 395): the first reading, pinned as the roster the retirement lane works from.
def expectedSummary : String :=
  "positions=272 top=172 nested=100 True=201 PackAlt=62 PackAltG=9 modules=2 supply: paid=28 relayed=116 declined-only=10 never-supplied=1 conclusions=12 writers=42 inrTrivial=514"

def expectedPositions : List String :=
  [ "L4YAML.Proofs.PreprocessIndentStable.IndentFloor.transport[3].h_floor top ∨ True",
    "L4YAML.Proofs.PreprocessIndentStable.IndentFloor.transport[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[6].valueF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key top ∨ True",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ True",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ True",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[9].vslot top ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.KmSoundbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.KmSoundbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.KmSound.back_col[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.KmSound.back_col[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.KmSound.push[15].h_stamp_new nested ∨ True",
    "L4YAML.Proofs.StreamAccum.KmSound.push[17].h_marker_new nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[9].h_vpack top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[11].h_framesS top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[11].h_framesS nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[12].h_framesV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[12].h_framesV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[16].h_seqF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[19].h_ncol top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[21].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[22].h_routeE top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[23].h_kslotE top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[25].h_closeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[25].h_closeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[26].h_closeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[26].h_closeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[28].h_closeFEV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[12].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[16].h_seqF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[17].h_kslotUp top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[18].h_closeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[18].h_closeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[10].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[13].h_seqF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[14].h_kslotUp top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[15].h_closeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[15].h_closeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[14].h_ncol top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[15].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[16].h_closeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[16].h_closeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[17].h_frames top ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[17].h_frames nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[18].h_closeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[18].h_closeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[19].h_framesV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[19].h_framesV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[21].h_seqF top ∨ True",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[10].h_vpack top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[11].h_vslot nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[11].h_vslot nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[19].h_sfx top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[20].h_mk top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[26].h_tail139 top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[27].h_valF top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[27].h_valF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[28].h_seqF top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[29].h_mapF top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[30].h_pr top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[31].h_mapFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[31].h_mapFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[32].h_valFV top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[13].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[29].h_seqF_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[30].h_kslotUp top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[31].h_closeFV_old top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[31].h_closeFV_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[15].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[34].h_seqF_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[35].h_kslotUp top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[37].h_closeFV_old top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[37].h_closeFV_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[16].h_vpack top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[33].h_seqF168 top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[34].h_mapF109 top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[35].h_mapFV108 top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[13].h_kslot_old top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[15].h_seqF_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[32].h_kslotUp_old top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[33].h_closeFV_old top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[33].h_closeFV_old nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[14].h_ncol_old top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[16].h_vslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[17].h_kslot top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[18].h_closeF99 top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[18].h_closeF99 nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[19].h_frames99 top ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[19].h_frames99 nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[20].h_closeFV108 top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[20].h_closeFV108 nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[21].h_framesV108 top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[21].h_framesV108 nested ∨ True",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[38].h_seqF168 top ∨ True",
    "L4YAML.Proofs.StreamAccum.bareNodeRoute_or_refused[11].h_tail top ∨ True",
    "L4YAML.Proofs.StreamAccum.bareNodeRoute_or_refused_content[12].h_tail top ∨ True",
    "L4YAML.Proofs.StreamAccum.close_col_of_base[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.close_col_of_base[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[19].h_sfx_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[20].h_nodoc_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[21].h_mk_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[22].h_res_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[23].h_ref_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[24].h_cov_in top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[25].h_pr_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map[26].h_resV_land top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.colon_open_map_explicit[21].h_outer top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[12].h_routeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[12].h_routeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[13].h_routeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[27].h_routeS top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[11].h_routeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[11].h_routeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[12].h_routeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[12].h_routeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[29].h_kslotD top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.compact_open_map[29].h_outer top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[16].h_keyctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[18].h_suffixctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[19].h_nodocctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[20].h_markerctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[22].h_ref top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[23].h_propsctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[18].h_keyctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[20].h_suffixctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[21].h_nodocctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[22].h_markerctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[24].h_ref top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[25].h_propsctx top ∨ True",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[26].h_markerline top ∨ True",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[8].h_cov top ∨ True",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[9].h_dcov top ∨ True",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[7].h_valF top ∨ True",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[7].h_valF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[11].h_nodeV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[12].h_compact top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[12].h_compact nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[13].h_ivl nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[14].h_nodeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[14].h_nodeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[15].h_dframes top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[15].h_dframes nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[16].h_nodeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[16].h_nodeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[17].h_dframesV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[17].h_dframesV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[18].h_cov top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[30].h_nodeS top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[31].h_nodeSF top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[11].h_nodeV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[12].h_compact top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[12].h_compact nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[13].h_nodeF top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[13].h_nodeF nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[14].h_dframes top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[14].h_dframes nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[15].h_nodeFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[15].h_nodeFV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[16].h_dframesV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[16].h_dframesV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[17].h_cov top ∨ True",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[27].h_ivl nested ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.flowKeyHead[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[8].h_base nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[8].h_base nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[12].h_compact top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[13].h_compact_pair top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[9].h_col top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[20].h_sfx top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[21].h_nodoc top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[24].h_tail143 top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[25].h_mapF top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[26].h_mapFV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ PackAltG",
    "L4YAML.Proofs.StreamAccum.flowOpen_floor_at_prep[10].h_floor top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowOpen_floor_at_prep[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker[4].h_doc top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp[4].h_ivl top ∨ True",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[22].h_sfx_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[23].h_nodoc_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[24].h_mk_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[25].h_res_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[26].h_ref_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[27].h_cov top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[28].h_pr_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[29].h_explUp_chain top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[30].h_resV_land top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[32].h_explUp_chainD top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.keyctx_of_preprocess[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.km_push_at_open[19].h_stamp_new nested ∨ True",
    "L4YAML.Proofs.StreamAccum.km_push_at_open[21].h_marker_new nested ∨ True",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing[11].h_mk top ∨ True",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.nodocctx_of_preprocess[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[18].h_sfx_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[19].h_nodoc_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[20].h_mk_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[21].h_res_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[22].h_ref_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[23].h_cov_in top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[24].h_cov_nil top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[25].h_pr_land top ∨ True",
    "L4YAML.Proofs.StreamAccum.question_open_map[26].h_explUp_chain top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.question_open_map[27].h_resV_land top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.question_open_map[29].h_explUp_chainD top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[13].h_fS top ∨ True",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[13].h_fS nested ∨ True",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[14].h_fV top ∨ PackAlt",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[14].h_fV nested ∨ True",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[15].h_pay nested ∨ True",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[15].h_pay nested ∨ True",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[16].h_fQ top ∨ True",
    "L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused[7].h_ref top ∨ True",
    "L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused[7].h_ref top ∨ True",
    "L4YAML.Proofs.StreamAccum.scanValue_ok_park_facts[ret] nested ∨ True",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing[11].h_sfx top ∨ True",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing[ret] top ∨ True",
    "L4YAML.Proofs.StreamAccum.topLevelFlowResumeSep_or_refused[6].h_ref top ∨ True"
  ]

def expectedSupply : List String :=
  [ "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key relayed [DECLINE=1 SPLIT=1 VIA=6]",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[9].vslot relayed [DECLINE=5 SPLIT=1 VIA=2]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[9].h_vpack relayed [DECLINE=4 SPLIT=5 VIA=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[11].h_framesS relayed [DECLINE=2 SPLIT=8 VIA=2]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[12].h_framesV relayed [DECLINE=4 SPLIT=8]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[16].h_seqF relayed [DECLINE=9 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[19].h_ncol paid [FIELD=2 PAY=3 RELAY=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[21].h_kslot relayed [DECLINE=3 FIELD=2 RELAY=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[22].h_routeE paid [DECLINE=3 FIELD=2 PAY=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[23].h_kslotE relayed [DECLINE=3 FIELD=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE relayed [DECLINE=3 FIELD=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[25].h_closeF relayed [DECLINE=3 FIELD=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[26].h_closeFV relayed [DECLINE=3 FIELD=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[28].h_closeFEV relayed [DECLINE=3 FIELD=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[12].h_kslot relayed [SPLIT=6]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF relayed [SPLIT=6]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[16].h_seqF relayed [DECLINE=3 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[17].h_kslotUp relayed [DECLINE=3 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[18].h_closeFV relayed [SPLIT=6]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[10].h_kslot relayed [DECLINE=1 SPLIT=6]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF paid [PAY=5 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[13].h_seqF paid [DECLINE=6 PAY=1]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[14].h_kslotUp relayed [DECLINE=3 SPLIT=4]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[15].h_closeFV relayed [DECLINE=1 SPLIT=6]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[14].h_ncol paid [DECLINE=2 PAY=4]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[15].h_kslot relayed [DECLINE=3 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[16].h_closeF paid [PAY=4 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[17].h_frames paid [PAY=4 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[18].h_closeFV paid [DECLINE=2 PAY=1 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[19].h_framesV paid [DECLINE=2 PAY=1 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[21].h_seqF relayed [DECLINE=5 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[10].h_vpack relayed [DECLINE=3 RELAY=1 SPLIT=6 VIA=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[19].h_sfx paid [DECLINE=10 PAY=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[20].h_mk paid [DECLINE=10 PAY=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[26].h_tail139 paid [DECLINE=8 PAY=3]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[27].h_valF relayed [DECLINE=9 FIELD=2]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[28].h_seqF relayed [DECLINE=7 RELAY=4]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[29].h_mapF relayed [DECLINE=7 FIELD=2 RELAY=2]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[30].h_pr relayed [DECLINE=9 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[31].h_mapFV relayed [DECLINE=3 FIELD=2 RELAY=2 SPLIT=4]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[32].h_valFV relayed [DECLINE=8 FIELD=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[13].h_kslot relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[29].h_seqF_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[30].h_kslotUp relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[31].h_closeFV_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[15].h_kslot relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[34].h_seqF_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[35].h_kslotUp relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[37].h_closeFV_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[16].h_vpack relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[33].h_seqF168 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[34].h_mapF109 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[35].h_mapFV108 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[13].h_kslot_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[15].h_seqF_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[32].h_kslotUp_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[33].h_closeFV_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[14].h_ncol_old relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[16].h_vslot relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[17].h_kslot relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[18].h_closeF99 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[19].h_frames99 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[20].h_closeFV108 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[21].h_framesV108 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[38].h_seqF168 relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.bareNodeRoute_or_refused[11].h_tail relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.bareNodeRoute_or_refused_content[12].h_tail other [LOCAL=2]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[19].h_sfx_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[20].h_nodoc_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[21].h_mk_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[22].h_res_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[23].h_ref_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[24].h_cov_in relayed [SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[25].h_pr_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map[26].h_resV_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map_explicit[21].h_outer relayed [SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[12].h_routeF relayed [SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[27].h_routeS relayed [FIELD=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[11].h_routeF relayed [SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[12].h_routeFV relayed [SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[29].h_kslotD declined-only [DECLINE=1]",
    "L4YAML.Proofs.StreamAccum.compact_open_map[29].h_outer relayed [SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[16].h_keyctx paid [PAY=2 VIA=1]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[18].h_suffixctx declined-only [DECLINE=3]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[19].h_nodocctx declined-only [DECLINE=3]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[20].h_markerctx declined-only [DECLINE=3]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[22].h_ref declined-only [DECLINE=3]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[23].h_propsctx relayed [DECLINE=2 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[18].h_keyctx relayed [DECLINE=1 RELAY=1 VIA=6]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[20].h_suffixctx relayed [DECLINE=5 RELAY=1 VIA=2]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[21].h_nodocctx relayed [DECLINE=5 RELAY=1 VIA=2]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[22].h_markerctx relayed [DECLINE=5 RELAY=1 VIA=2]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[24].h_ref relayed [DECLINE=3 LOCAL=4 RELAY=1]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[25].h_propsctx relayed [DECLINE=7 RELAY=1]",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[26].h_markerline paid [DECLINE=7 PAY=1]",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[8].h_cov relayed [RELAY=4]",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[9].h_dcov relayed [FIELD=2 LOCAL=2]",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[7].h_valF relayed [RELAY=2]",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[11].h_nodeV relayed [SPLIT=2 VIA=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[12].h_compact paid [PAY=2 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[14].h_nodeF relayed [SPLIT=4]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[15].h_dframes relayed [RELAY=2 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[16].h_nodeFV relayed [RELAY=2 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[17].h_dframesV relayed [RELAY=2 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[18].h_cov paid [DECLINE=2 PAY=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[30].h_nodeS paid [DECLINE=2 PAY=2]",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[31].h_nodeSF paid [PAY=2 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[11].h_nodeV relayed [SPLIT=1 VIA=1]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[12].h_compact paid [PAY=1 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[13].h_nodeF relayed [SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[14].h_dframes relayed [RELAY=1 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[15].h_nodeFV relayed [RELAY=1 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[16].h_dframesV relayed [RELAY=1 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[17].h_cov paid [DECLINE=1 PAY=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyHead[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key relayed [VIA=2]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[12].h_compact paid [DECLINE=1 FIELD=1 PAY=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[13].h_compact_pair relayed [DECLINE=1 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[9].h_col paid [DECLINE=3 PAY=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[20].h_sfx declined-only [DECLINE=3 LOCAL=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[21].h_nodoc paid [DECLINE=3 PAY=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[24].h_tail143 declined-only [DECLINE=3 LOCAL=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[25].h_mapF declined-only [DECLINE=3 LOCAL=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[26].h_mapFV declined-only [DECLINE=3 LOCAL=1]",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.flowOpen_floor_at_prep[10].h_floor never-supplied []",
    "L4YAML.Proofs.StreamAccum.flowOpen_floor_at_prep[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker[4].h_doc paid [PAY=2]",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp[4].h_ivl paid [FIELD=1 PAY=1]",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[22].h_sfx_land relayed [DECLINE=3 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[23].h_nodoc_land paid [DECLINE=3 PAY=1]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[24].h_mk_land relayed [DECLINE=3 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[25].h_res_land relayed [DECLINE=1 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[26].h_ref_land paid [DECLINE=2 PAY=1 RELAY=1]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[27].h_cov relayed [DECLINE=1 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[28].h_pr_land relayed [DECLINE=3 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[29].h_explUp_chain relayed [DECLINE=2 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[30].h_resV_land relayed [DECLINE=1 SPLIT=3]",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[32].h_explUp_chainD relayed [DECLINE=3 SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.keyctx_of_preprocess[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing[11].h_mk paid [PAY=2]",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.nodocctx_of_preprocess[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.question_open_map[18].h_sfx_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[19].h_nodoc_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[20].h_mk_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[21].h_res_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[22].h_ref_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[23].h_cov_in relayed [SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[24].h_cov_nil relayed [SPLIT=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[25].h_pr_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[26].h_explUp_chain relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[27].h_resV_land relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.question_open_map[29].h_explUp_chainD relayed [RELAY=1]",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[13].h_fS relayed [LOCAL=4 RELAY=1 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[14].h_fV relayed [LOCAL=4 RELAY=1 SPLIT=2]",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[16].h_fQ declined-only [DECLINE=3 LOCAL=4]",
    "L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused[7].h_ref relayed [DECLINE=4 RELAY=5]",
    "L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused[7].h_ref relayed [DECLINE=6 RELAY=5]",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing[11].h_sfx other [LOCAL=2]",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing[ret] conclusion",
    "L4YAML.Proofs.StreamAccum.topLevelFlowResumeSep_or_refused[6].h_ref other [LOCAL=1]"
  ]

def expectedWriters : List String :=
  [ "L4YAML.Proofs.PreprocessIndentStable.IndentFloor.transport ×1 (PreprocessIndentStable)",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.ofValue ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock ×28 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_block_on_noPending ×7 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock ×32 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent ×26 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent ×12 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_block_pending ×43 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_content_on_noPending ×12 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented ×33 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented ×34 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_content_pending ×82 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_flow_open_depth0 ×65 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.accum_step_flow ×6 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.colon_fires_implicit_key ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.colon_fires_props_key ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.colon_open_map ×4 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.colon_open_map_explicit ×6 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit ×4 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props ×4 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.compact_open_map ×7 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed ×25 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume ×2 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch ×14 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch ×7 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open ×7 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root ×9 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.flowOpen_floor_at_prep ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker ×2 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp ×2 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.indicator_open_map ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.keyctx_of_preprocess ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.nodocctx_of_preprocess ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.question_open_map ×3 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing ×9 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.scanValue_ok_park_facts ×1 (StreamAccum)",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing ×3 (StreamAccum)"
  ]

run_cmd do
  let env ← getEnv
  let (es, _) ← edges (ns ++ `content_dispatch_routed)
  liftTermElabM do
    let consts ← authored
    let mut poss : Array Pos := #[]
    let mut writers : Array String := #[]
    let mut nWrites := 0
    for (nm, m) in consts do
      poss := poss ++ (← positionsOf nm m)
      if let some v := (env.find? nm).bind (·.value? (allowOpaque := true)) then
        let k := inrTrivial v
        if k > 0 then
          writers := writers.push s!"{(Lean.privateToUserName nm)} ×{k} ({m.getString!})"
          nWrites := nWrites + k
    -- supply, per top position declared in StreamAccum
    let mut tallies : Std.HashMap String (Std.HashMap String Nat) := {}
    for e in es do
      let k := s!"{Lean.privateToUserName e.callee}[{e.idx}]"
      let how := (e.how.splitOn " ").head!
      let t := tallies.getD k {}
      tallies := tallies.insert k (t.insert how ((t.getD how 0) + 1))
    let mut supply : Array String := #[]
    let mut nPaid := 0; let mut nRelayed := 0; let mut nDeclined := 0; let mut nNever := 0; let mut nConcl := 0
    for p in poss do
      unless p.kind == "top" && p.module == "L4YAML.Proofs.Production.StreamAccum" do continue
      if p.site == "[ret]" then
        nConcl := nConcl + 1
        supply := supply.push s!"{p.decl}[ret] conclusion"
        continue
      let idx := ((p.site.splitOn "]").head!.drop 1)
      let k := s!"{p.decl}[{idx}]"
      let t := tallies.getD k {}
      let g (h : String) := t.getD h 0
      let cls :=
        if t.isEmpty then "never-supplied"
        else if g "PAY" > 0 then "paid"
        else if g "RELAY" + g "VIA" + g "FIELD" + g "SPLIT" + g "READ" + g "RETURN" > 0 then "relayed"
        else if g "DECLINE" > 0 then "declined-only"
        else "other"
      match cls with
      | "paid" => nPaid := nPaid + 1
      | "relayed" => nRelayed := nRelayed + 1
      | "declined-only" => nDeclined := nDeclined + 1
      | "never-supplied" => nNever := nNever + 1
      | _ => pure ()
      let hows := (t.toList.map fun (h, n) => s!"{h}={n}").toArray.qsort (· < ·)
      supply := supply.push s!"{p.decl}{p.site} {cls} [{" ".intercalate hows.toList}]"
    let top := poss.filter (·.kind == "top")
    let nested := poss.filter (·.kind == "nested")
    let byAlt (a : String) := (poss.filter (·.alt == a)).size
    let mods := (poss.map (·.module)).toList.eraseDups
    let summary := s!"positions={poss.size} top={top.size} nested={nested.size} True={byAlt "True"} \
PackAlt={byAlt "PackAlt"} PackAltG={byAlt "PackAltG"} modules={mods.length} \
supply: paid={nPaid} relayed={nRelayed} declined-only={nDeclined} never-supplied={nNever} conclusions={nConcl} \
writers={writers.size} inrTrivial={nWrites}"
    let posLines := (poss.map posLine).toList
    let mut moved : Array String := #[]
    if summary != expectedSummary then
      moved := moved.push s!"the ∨-True AUDIT summary moved (shrink-only).\nexpected: {expectedSummary}\ngot:      {summary}"
    if posLines != expectedPositions then
      moved := moved.push s!"the ∨-True POSITIONS moved (shrink-only: a retirement re-pins DOWN with the disposition; a new position needs the owner's word).\nexpected ({expectedPositions.length}), got ({posLines.length}):\n{String.intercalate "\n" posLines}"
    if supply.toList != expectedSupply then
      moved := moved.push s!"the ∨-True SUPPLY classes moved.\nexpected ({expectedSupply.length}), got ({supply.size}):\n{String.intercalate "\n" supply.toList}"
    if writers.toList != expectedWriters then
      moved := moved.push s!"the Or.inr trivial WRITERS moved (shrink-only).\nexpected ({expectedWriters.length}), got ({writers.size}):\n{String.intercalate "\n" writers.toList}"
    unless moved.isEmpty do
      throwError (String.intercalate "\n\n" moved.toList)

end Tests.Guards.OrTrueAudit
