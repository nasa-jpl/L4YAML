/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.PuntCoverInputs

/-!
# Who writes the value-line packs, and what each writer holds toward the tail at the entry's level (DOCS item 261)

Item 260 read the explicit `:` opener's lack as the field's BOTTOM: its list
is headed, so the resume needs the entry level's tail closed after the value,
and every closure the opener holds — the value-line packs its callers hand it
— closes the VALUE and the stream with it.  The carrier that would fund that
bottom without re-reading the value line as `[192]`'s empty-key entry is a
value-line-then-tail twin of those packs, and its price is the producers
touched: every position that writes a pack.  This module prices it.

**§0** finds the packs by SHAPE, not by name: a park constructor's field is a
value-line pack when its type carries, outside any `ResumeFrames`, the value
closure `∀ sp_v, SBlockIndented lvl .blockOut _ sp_v → SLYamlStream _ sp_v`
(written out, or as `ExplValueLine`); the fields that stand `ResumeFrames`
ON that closure are listed apart — frames whose bottom is a value line, the
tail BEFORE the line and not after it.  Each pack's line prints how its level
is bound, the closure's premise chain, and whether a `SCompactMapTail`
premise follows the value (the twin's shape; no pack has one).  A lemma
parameter of the same shape is a pack position too — the openers take the
packs their callers write — and §0 lists those beside the fields.  **§1**
walks every theorem for full applications of a park constructor and for
applications of a lemma with pack parameters, and at each pack position
classifies the argument: `punt` (the option's `True` arm), `stamp` (the
field's other honest arm, where it has one), `empty` (a pack over `[]`),
`relay` (a hypothesis passed through, tagged with what it is), `step` (an
`Or.imp` over one), `via` (a transport lemma, its own arguments read the
same way), or `paid` — and for a paid pack, the witness list and the closure
the pack's body spends for the value's end, read to its innermost
hypothesis: `chain` when that hypothesis is itself value-line shaped (a
destructured caller pack re-wrapped), `route` when it is a total closure
with no value line in it (the pack is BUILT here), `frames` when it is a
frames face.  **§2** reads, at every writer, each hypothesis in hand that
mentions `SCompactMapTail` or `ResumeFrames`, with its shape (item 260's
`tail(k)←…` / `frames(ks)←…`, a frames face's own bottom tagged when it is
a value line), and answers the mandate's question per row: `held` when a
held tail or frames face names a level the pack writes, `level-var` when
the pack's list is a variable no syntactic reading can enter, `none`
otherwise.  A pack body that spends a tail-premised hypothesis would be a
carrier already; the line counts those (`spendTail`).

The pins hold the eleven packs, the seven frames faces, the pack parameters,
every writer row, the per-position summary and the line.  Beside the rows
the walk records every `let`/`have` (label, type, stack, value), every
application whose head is a local binder, and every match's discriminants:
the side records `Tests/Guards/Proofs/ValueLineOrigins.lean` follows a
row's chain through; they change nothing printed here.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (sorted)
open Tests.Guards.RouteShapes
open Tests.Guards.StreamCompositions
open Tests.Guards.CloseSplitFrames
open Tests.Guards.CloseStackCover
open Tests.Guards.PuntCoverInputs

namespace Tests.Guards.ValueLinePacks

/-! ## §0 The value closure, and the packs by shape -/

def sbiN : Name := ``L4YAML.Surface.SBlockIndented
def evlN : Name := ``L4YAML.Proofs.StreamAccum.ExplValueLine
def glitN : Name := ``L4YAML.Surface.GLit

/-- `∀ sp_v, SBlockIndented lvl .blockOut p sp_v → SLYamlStream s sp_v`, or — since item 371
    restated every pack — `… → ResumeFrames (SLYamlStream s) [FrameLevel.map lvl] sp_v` (the one
    level the pack is about, over the stream).  Both read as THE value closure; the reader is
    told so because a closure it cannot see is a pack it cannot census. -/
def isValueClosure (t : Expr) : Bool :=
  match t.consumeMData with
  | .forallE _ _ (.forallE _ prem concl _) _ =>
    let prem := prem.consumeMData
    let concl := concl.consumeMData
    let streamConcl := concl.isAppOfArity streamN 2 ||
      (concl.isAppOfArity resumeN 3 && (concl.getArg! 0).consumeMData.isAppOfArity streamN 1)
    prem.isAppOfArity sbiN 4 && streamConcl &&
      (match (prem.getArg! 1).consumeMData with | .const c _ => short c == "blockOut" | _ => false)
  | _ => false

/-- The value closure occurs in `e` outside any `ResumeFrames`. -/
-- Item 304: a stack is `ResumeFrames` or `KeyFrames` (item 302's value-line stack); `keyN` is `PuntCoverInputs`'.
partial def vcOutside (e : Expr) : Bool :=
  let e := e.consumeMData
  if isValueClosure e || e.isAppOf evlN then true
  else if (e.isAppOf resumeN || e.isAppOf keyN) then false
  else match e with
    | .app f a => vcOutside f || vcOutside a
    | .forallE _ t b _ => vcOutside t || vcOutside b
    | .lam _ t b _ => vcOutside t || vcOutside b
    | .letE _ t v b _ => vcOutside t || vcOutside v || vcOutside b
    | .proj _ _ b => vcOutside b
    | _ => false

/-- `ResumeFrames` standing on the value closure occurs in `e`. -/
def framesOnVC (e : Expr) : Bool :=
  (e.find? fun s => (s.isAppOfArity resumeN 3 || s.isAppOfArity keyN 3) && vcOutside (s.getArg! 0)).isSome

/-- Which arm of a pack's option carries the closure, and whether the other
    arm is `True` (a punt) or a second honest reading (a stamp). -/
def sideOf (t : Expr) : Bool × Bool :=
  let t := t.consumeMData
  if t.isAppOfArity ``Or 2 then
    let vcLeft := vcOutside (t.getArg! 0)
    let other := (if vcLeft then t.getArg! 1 else t.getArg! 0).consumeMData
    (vcLeft, (other.isConstOf ``True || other.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt || other.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG))  -- item 311: the named alternative reads as `True`
  else (true, true)

/-- A proposition in one token: a relation as `l sym r`, else its head. -/
def propTok (st : Stack) (t : Expr) : String :=
  match rel t with
  | some (sym, l, r) => s!"{ppc st l}{sym}{ppc st r}"
  | none =>
    let t := t.consumeMData
    match t.getAppFn with
    | .const h _ =>
      if h == glitN && t.getAppNumArgs == 3 then s!"GLit({ppc st (t.getArg! 0)})"
      else if (`L4YAML.Surface).isPrefixOf h && t.getAppNumArgs ≥ 1 && (match (t.getArg! 0).consumeMData with | .const .. => false | _ => true) then
        s!"{short h}({ppc st (t.getArg! 0)})"
      else short h
    | _ => "?"

/-- Down through the pack's option, existentials, membership binder and
    conjunctions to the value closure: the stack there, the closure, and
    the level binding read on the way. -/
partial def peelToClosure (st : Stack) (t : Expr) (lvl : Array String) : Stack × Expr × Array String :=
  let t := t.consumeMData
  if t.isAppOfArity ``Or 2 then
    let a := t.getArg! 0
    let b := t.getArg! 1
    if vcOutside a then peelToClosure st a lvl else peelToClosure st b lvl
  else if t.isAppOfArity ``Exists 2 then
    match (t.getArg! 1).consumeMData with
    | .lam n ty body _ => peelToClosure (st.push { name := n, ty := ty, prov := none }) body (lvl.push s!"∃{bname n}")
    | _ => (st, t, lvl)
  else if t.isAppOfArity ``And 2 then
    let a := t.getArg! 0
    let b := t.getArg! 1
    if vcOutside b then peelToClosure st b (lvl.push s!"({propTok st a})")
    else peelToClosure st a (lvl.push s!"({propTok st b})")
  else match t with
    | .forallE n ty body _ =>
      if ty.consumeMData.isConstOf ``Nat then
        match body.consumeMData with
        | .forallE m mem body2 _ =>
          if mem.consumeMData.isAppOf ``Membership.mem then
            let st1 := st.push { name := n, ty := ty, prov := none }
            let mem' := mem.consumeMData
            let ns := ppc st1 (mem'.getArg! (mem'.getAppNumArgs - 2))
            peelToClosure (st1.push { name := m, ty := mem, prov := none }) body2 (lvl.push s!"∀{bname n}∈{ns}")
          else (st, t, lvl)
        | _ => (st, t, lvl)
      else (st, t, lvl)
    | _ => (st, t, lvl)

/-- The closure's premise chain, its conclusion, and whether a
    `SCompactMapTail` premise follows the value. -/
partial def premisesOf (env : Environment) (st : Stack) (t : Expr) (acc : Array String) (seenV : Bool) (tail : Bool) : Array String × String × Bool :=
  let t := t.consumeMData
  match t with
  | .forallE n ty body _ =>
    let ty' := ty.consumeMData
    let st' := st.push { name := n, ty := ty, prov := none }
    match ty'.getAppFn with
    | .const h _ =>
      if h == glitN then premisesOf env st' body (acc.push s!"GLit({ppc st (ty'.getArg! 0)})") seenV tail
      else if (`L4YAML.Surface).isPrefixOf h && ty'.getAppNumArgs ≥ 1 && levelFirst env h then
        let isV := h == sbiN
        let isT := h == tailN
        premisesOf env st' body (acc.push s!"{short h}({ppc st (ty'.getArg! 0)})") (seenV || isV) (tail || (seenV && isT))
      else if h == ``Nat || h == ``L4YAML.Surface.SurfPos then premisesOf env st' body acc seenV tail
      else premisesOf env st' body (acc.push s!"{short h}") seenV tail
    | _ => premisesOf env st' body acc seenV tail
  | _ =>
    let concl := match t.getAppFn with
      | .const h _ => if h == evlN && t.getAppNumArgs ≥ 2 then s!"ExplValueLine({ppc st (t.getArg! 1)})" else short h
      | _ => "?"
    (acc, concl, tail)

/-- Item 260's resume shape, with a frames face's own bottom tagged when it
    is a value line and a bare tail fact named. -/
partial def holdShape (env : Environment) (st : Stack) (t : Expr) (prev : Option String) : Option String :=
  let t := t.consumeMData
  match t with
  | .forallE n ty b _ =>
    let ty' := ty.consumeMData
    if ty'.isAppOfArity tailN 3 then some s!"tail({ppc st (ty'.getArg! 0)})←{prev.getD "landing"}"
    else
      let prev' := match ty'.getAppFn with
        | .const h _ => if (`L4YAML.Surface).isPrefixOf h && ty'.getAppNumArgs ≥ 1 && levelFirst env h then some s!"{short h}({ppc st (ty'.getArg! 0)})" else prev
        | _ => prev
      (holdShape env st ty prev).orElse fun _ => holdShape env (st.push { name := n, ty := ty, prov := none }) b prev'
  | .lam n ty b _ => holdShape env (st.push { name := n, ty := ty, prov := none }) b prev
  | .app .. =>
    if (t.isAppOfArity resumeN 3 || t.isAppOfArity keyN 3) then
      let p := (t.getArg! 0).consumeMData
      let tag := if p.isAppOf evlN && p.getAppNumArgs ≥ 2 then s!"@ExplValueLine({ppc st (p.getArg! 1)})" else ""
      some s!"frames({ppc st (t.getArg! 1)}){tag}←{prev.getD "landing"}"
    else if t.isAppOfArity tailN 3 then some s!"tailFact({ppc st (t.getArg! 0)})"
    else t.getAppArgs.findSome? fun a => holdShape env st a prev
  | _ => none

/-- Every hypothesis in hand mentioning a tail or frames, with its shape. -/
def holdsOf (env : Environment) (stAll : Stack) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:stAll.size] do
    let b := stAll[i]!
    unless (hasHead b.ty resumeN || hasHead b.ty keyN) || hasHead b.ty tailN do continue
    let st0 := stAll.extract 0 i
    out := out.push s!"{bname b.name}:{(holdShape env st0 b.ty none).getD "?"}"
  return out

/-! ## §1 The writers -/

/-- A pack position: the argument index, the name, which arm carries the
    closure, and whether the other arm is `True`. -/
abbrev Pos := Nat × Name × Bool × Bool

structure PCand where
  ctors : Std.HashSet Name := {}
  fieldNames : Std.HashMap Name (Array Name) := {}
  packs : Std.HashMap Name (Array Pos) := {}
  lemParams : Std.HashMap Name (Array Pos) := {}
  consts : Std.HashSet Name := {}

structure WRow where
  lem : Name
  kind : String
  target : String
  callee : Name
  occ : Nat
  argIdx : Nat
  vcLeft : Bool
  otherTrue : Bool
  st : Stack
  args : Array Expr
  deriving Inhabited

/-- A `let`/`have` met on the walk: its label, type, the stack it stands in
    and its value — what a chain that bottoms in it is followed into. -/
structure LetRec where
  lem : Name
  label : String
  name : Name
  ty : Expr
  st : Stack
  val : Expr
  deriving Inhabited

/-- An application whose head is a local binder (a local function or a
    hypothesis applied): the head, its depth, the stack and the arguments. -/
structure LApp where
  lem : Name
  head : Bind
  depth : Nat
  st : Stack
  args : Array Expr
  deriving Inhabited

/-- A match met on the walk: the stack and the discriminants its alternative
    binders were labeled from. -/
structure AltRec where
  lem : Name
  st : Stack
  discrs : Array Expr
  deriving Inhabited

structure W where
  rows : Array WRow := #[]
  occ : Std.HashMap String Nat := {}
  memo : Std.HashMap Expr Bool := {}
  nodes : Nat := 0
  apps : Nat := 0
  lets : Array LetRec := #[]
  lapps : Array LApp := #[]
  alts : Array AltRec := #[]
  liteNodes : Nat := 0

partial def containsP (st : IO.Ref W) (cs : Std.HashSet Name) (e : Expr) : MetaM Bool := do
  match (← st.get).memo[e]? with
  | some b => return b
  | none =>
    let b ← match e with
      | .const n _ => pure (cs.contains n)
      | .app f a => do pure ((← containsP st cs f) || (← containsP st cs a))
      | .lam _ t b _ | .forallE _ t b _ => do pure ((← containsP st cs t) || (← containsP st cs b))
      | .letE _ t v b _ => do pure ((← containsP st cs t) || (← containsP st cs v) || (← containsP st cs b))
      | .mdata _ b | .proj _ _ b => containsP st cs b
      | _ => pure false
    st.modify fun s => { s with memo := s.memo.insert e b }
    return b

/-- How a match's alternative binders are labeled: by the discriminant of
    the same name, else by position when the alternative binds one variable
    per discriminant, else by the first discriminant that has a source. -/
def altLabeler (st : Stack) (discrs : Array Expr) : MetaM (Nat → Name → Option String) := do
  let mut info : Array (Option String × Option Name) := #[]
  for d in discrs do
    let nm := match d.consumeMData with
      | .bvar i => if i < st.size then some st[st.size - 1 - i]!.name else none
      | _ => none
    info := info.push (← sourceOf st d, nm)
  let first := info.findSome? (·.1)
  let n := info.size
  return fun pos name =>
    match info.find? (fun (_, nm) => nm == some name) with
    | some (s, _) => s <|> first
    | none => if n > 1 && pos < n then (info[pos]!.1 <|> first) else first

structure PCx where
  lem : Name
  st : Stack
  paramsLeft : Nat := 0
  door : Option (Name × Array Name × Nat) := none
  inherit : Option (Nat → Name → Option String) := none
  inheritPos : Nat := 0
  /-- Below a subterm with no pack constant: no row can stand here, so the
      walk only labels binders and records the side records. -/
  lite : Bool := false

/-- A binder whose type is data, not a hypothesis. -/
def isDataTy (ty : Expr) : Bool :=
  let ty := ty.consumeMData
  match ty.getAppFn with
  | .const c _ => c == ``Nat || c == ``List || c == ``L4YAML.Surface.SurfPos || c == ``ScannerState || c == ``Char ||
      c == ``Bool || c == ``String || c == ``Option || c == ``Prod || c == ``Int || c == ``YamlContext
  | .sort _ => true
  | _ => (piConcl ty).isSort

/-- A `have`'s label: its name, its source, and — for a transport — the
    hypotheses the transport takes.

    **The head is read under `privateToUserName`, and that is the whole reason
    these rows carry their binder lists.**  A transport's head is usually a
    generated matcher, and the library exports a generated auxiliary under a
    private name — `_private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.compact_open_map.match_1_3`
    is the head of `compact_open_map`'s `h_vslot105`.  Its `getRoot` is
    `_private`, so a raw root test rejects every transport the library writes
    and the list after `<param:…` comes out empty on nine rows.  The
    declaration is the library's either way; the mangling is a name, not a
    fact about the term. -/
def letLabel (st : Stack) (n : Name) (v : Expr) : MetaM String := do
  let v' := peelSafe v
  let src ← sourceOf st v
  let inputs : Array String := match v'.getAppFn with
    | .const c _ => if (Lean.privateToUserName c).getRoot == `L4YAML then v'.getAppArgs.filterMap (fun a =>
        match a.consumeMData with
        | .bvar i => if i < st.size then (if isDataTy st[st.size - 1 - i]!.ty then none else some (bname st[st.size - 1 - i]!.name)) else none
        | _ => none) else #[]
    | _ => #[]
  let tail := match src with
    | some s => if inputs.isEmpty then s!"<{s}" else s!"<{s}({String.intercalate "," inputs.toList})"
    | none => ""
  return s!"let:{bname n}{tail}"

partial def walkP (w : IO.Ref W) (cd : PCand) (cx : PCx) (e : Expr) : MetaM Unit := do
  if cx.lite then w.modify fun s => { s with liteNodes := s.liteNodes + 1 }
  else w.modify fun s => { s with nodes := s.nodes + 1 }
  match e with
  | .mdata _ b => walkP w cd cx b
  | .lam n t b _ =>
    let mut prov : Option String := none
    let mut door := cx.door
    let mut pos := cx.inheritPos
    if cx.paramsLeft > 0 then prov := some s!"param:{short cx.lem}.{bname n}"
    else if let some (c, fields, i) := cx.door then
      if i < fields.size then
        prov := some s!"door:{short c}.{fields[i]!}"
        door := some (c, fields, i + 1)
      else door := none
    else if let some f := cx.inherit then
      prov := f pos n <|> some s!"λ:{bname n}"
      pos := pos + 1
    else prov := some s!"λ:{bname n}"
    let inherit' := if cx.paramsLeft > 0 then none else cx.inherit
    walkP w cd { cx with st := cx.st.push { name := n, ty := t, prov }, paramsLeft := cx.paramsLeft - 1, door, inherit := inherit', inheritPos := pos } b
  | .forallE n t b _ =>
    walkP w cd { cx with st := cx.st.push { name := n, ty := t, prov := none }, paramsLeft := 0, door := none, inherit := none } b
  | .letE n t v b _ =>
    let cx0 := { cx with paramsLeft := 0, door := none, inherit := none }
    let lab ← letLabel cx.st n v
    w.modify fun s => { s with lets := s.lets.push { lem := cx.lem, label := lab, name := n, ty := t, st := cx.st, val := v } }
    walkP w cd cx0 v
    walkP w cd { cx0 with st := cx.st.push { name := n, ty := t, prov := some lab } } b
  | .proj _ _ b => walkP w cd { cx with paramsLeft := 0, door := none, inherit := none } b
  | .app .. =>
    if let .bvar i := e.getAppFn then
      if i < cx.st.size then
        w.modify fun s => { s with lapps := s.lapps.push { lem := cx.lem, head := cx.st[cx.st.size - 1 - i]!, depth := cx.st.size - 1 - i, st := cx.st, args := e.getAppArgs } }
    let mut cx := cx
    unless cx.lite do
      unless ← containsP w cd.consts e do cx := { cx with lite := true }
    let f := e.getAppFn
    let args := e.getAppArgs
    let cx0 := { cx with paramsLeft := 0, door := none, inherit := none }
    match f with
    | .const n _ =>
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← walkP w cd cx (mkAppN args[k]! (args.extract arity args.size)).headBeta
      if n == ``letFun && args.size ≥ 4 then
        match args[3]! with
        | .lam bn bt bb _ =>
          let lab ← letLabel cx.st bn args[2]!
          w.modify fun s => { s with lets := s.lets.push { lem := cx.lem, label := lab, name := bn, ty := args[0]!, st := cx.st, val := args[2]! } }
          walkP w cd cx0 args[2]!
          walkP w cd { cx0 with st := cx.st.push { name := bn, ty := bt, prov := some lab } } bb
        | g =>
          walkP w cd cx0 args[2]!
          walkP w cd cx0 g
        for a in args.extract 4 args.size do walkP w cd cx0 a
        return
      if n == ``PendingNode.casesOn then
        let env ← getEnv
        let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode"
        let majorPos := iv.numParams + 1 + iv.numIndices
        for i in [0:args.size] do
          if i > majorPos && i ≤ majorPos + iv.ctors.length then
            let c := iv.ctors[i - majorPos - 1]!
            walkP w cd { cx0 with door := some (c, cd.fieldNames.getD c #[], 0) } args[i]!
          else walkP w cd cx0 args[i]!
        return
      if let some (_, discrs, brs) ← branchesOf n args then
        w.modify fun s => { s with alts := s.alts.push { lem := cx.lem, st := cx.st, discrs } }
        let f ← altLabeler cx.st discrs
        for i in [0:args.size] do
          if brs.contains i then walkP w cd { cx0 with inherit := some f, inheritPos := 0 } args[i]!
          else walkP w cd cx0 args[i]!
        return
      if cd.ctors.contains n then
        let env ← getEnv
        let some (.ctorInfo cv) := env.find? n | throwError "{n}: not a constructor"
        let fieldArgs := args.extract cv.numParams args.size
        let producer := fieldArgs.any fun a => !(a.consumeMData.isBVar || a.consumeMData.isFVar)
        if producer && args.size == cv.numParams + cv.numFields then
          let key := s!"{cx.lem}/{n}"
          let occ := ((← w.get).occ.getD key 0) + 1
          w.modify fun s => { s with occ := s.occ.insert key occ, apps := s.apps + 1 }
          for (idx, field, vcLeft, otherTrue) in cd.packs.getD n #[] do
            w.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "ctor", target := s!"{short n}.{field}", callee := n, occ, argIdx := idx, vcLeft, otherTrue, st := cx.st, args } }
      if let some ps := cd.lemParams[n]? then
        let key := s!"{cx.lem}/{n}"
        let occ := ((← w.get).occ.getD key 0) + 1
        w.modify fun s => { s with occ := s.occ.insert key occ }
        for (idx, pname, vcLeft, otherTrue) in ps do
          if idx < args.size then
            w.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "param", target := s!"{short n}.{pname}", callee := n, occ, argIdx := idx, vcLeft, otherTrue, st := cx.st, args } }
      for a in args do walkP w cd cx0 a
    | _ =>
      walkP w cd cx0 f
      for a in args do walkP w cd cx0 a
  | _ => return

def walkTheoremP (w : IO.Ref W) (cd : PCand) (n : Name) : MetaM Unit := do
  let some ci := (← getEnv).find? n | return
  let some v := ci.value? (allowOpaque := true) | return
  w.modify fun s => { s with memo := {} }
  unless ← containsP w cd.consts v do return
  walkP w cd { lem := n, st := #[], paramsLeft := ci.type.getForallBinderNames.length } v

/-! ## §2 Classifying a pack argument, and the spend -/

/-- Push every leading lambda of `e`, labeled by `f`. -/
partial def enterAllF (st : Stack) (f : Nat → Name → Option String) (e : Expr) (pos : Nat := 0) : Stack × Expr :=
  match e.consumeMData with
  | .lam n t b _ => enterAllF (st.push { name := n, ty := t, prov := f pos n <|> some s!"λ:{bname n}" }) f b (pos + 1)
  | e => (st, e)

def isThmN (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.thmInfo _) => true | _ => false

def isCtorN (env : Environment) (n : Name) : Bool :=
  match env.find? n with | some (.ctorInfo _) => true | _ => false

/-- A lambda whose body is a proposition: a predicate argument, not a proof. -/
partial def isPredLam (e : Expr) : Bool :=
  match e.consumeMData with
  | .lam _ _ b _ => isPredLam b
  | .forallE .. => true
  | .sort _ => true
  | b => match b.getAppFn with
    | .const c _ => c == ``And || c == ``Or || c == ``Exists || c == ``Not || c == ``Eq || c == ``True
    | _ => false

def bindOf (st : Stack) (e : Expr) : Option Bind :=
  match e.consumeMData with
  | .bvar i => if i < st.size then some st[st.size - 1 - i]! else none
  | _ => none

/-- The kind of hypothesis a spend or a relay bottoms in. -/
def bindKind (b : Option Bind) : String :=
  match b with
  | none => "other"
  | some b =>
    if vcOutside b.ty then "chain"
    else if (hasHead b.ty resumeN || hasHead b.ty keyN) then "frames"
    else if hasHead b.ty tailN then "tail"
    else if (piConcl b.ty).isAppOf streamN then "route"
    else "other"

/-- The closure a pack body spends for the value's end, read to its innermost
    hypothesis: the head chain as text, and the binder that hypothesis is. -/
partial def spendOf (env : Environment) (st : Stack) (e : Expr) (fuel : Nat := 10) : MetaM (String × Option Bind) := do
  if fuel == 0 then return ("…", none)
  let e := peelSafe e
  match e with
  | .lam n t b _ => spendOf env (st.push { name := n, ty := t, prov := none }) b fuel
  | .bvar _ =>
    let b := bindOf st e
    return (s!"{(b.map fun b => bname b.name).getD "#?"}←{(b.bind (·.prov)).getD "?"}", b)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .bvar _ =>
      let b := bindOf st f
      return (s!"{(b.map fun b => bname b.name).getD "#?"}←{(b.bind (·.prov)).getD "?"}", b)
    | .const c _ =>
      if let some (_, discrs, brs) ← branchesOf c args then
        let lab ← altLabeler st discrs
        let mut parts : Array String := #[]
        let mut bind : Option Bind := none
        for b in brs do
          let (st', body) := enterAllF st lab args[b]!
          let (s, bb) ← spendOf env st' body (fuel - 1)
          if s == "absurd" || s == "?" || s == "trivial" || s == "True.intro" then continue
          parts := parts.push s
          if bind.isNone then bind := bb
        if parts.isEmpty then return ("?", none)
        return (if parts.size == 1 then parts[0]! else "alt[" ++ String.intercalate "|" parts.toList ++ "]", bind)
      if deadEnd c then return ("absurd", none)
      if c == ``Or.inl || c == ``Or.inr || c == ``Exists.intro || c == ``And.intro then
        if args.size > 0 then return ← spendOf env st args[args.size - 1]! (fuel - 1)
        return (short c, none)
      if c.getRoot == `L4YAML && isThmN env c then
        for a in args do
          let a' := peelSafe a
          let cand := match a' with
            | .lam .. => !isPredLam a'
            | .bvar .. => (match bindOf st a' with | some b => bindKind (some b) != "other" | none => false)
            | .app .. => (match a'.getAppFn with
                | .bvar _ => true
                | .const m _ => m.getRoot == `L4YAML && isThmN env m
                | _ => false)
            | _ => false
          if cand then
            let (s, bb) ← spendOf env st a' (fuel - 1)
            if bb.isSome || s.startsWith "alt[" then return (s!"{short c}({s})", bb)
        return (short c, none)
      if c.getRoot == `L4YAML && isCtorN env c then return (s!"ctor:{short c}", none)
      return (short c, none)
    | _ => return ("?", none)
  | _ => return ("?", none)

structure PackRead where
  cls : String
  ns : String := "—"
  wits : Array (String × Bool) := #[]
  spend : String := "—"
  spendTail : Bool := false
  deriving Inhabited

/-- A paid pack's reading: the witnesses, then the closure's spend; a pack
    produced by a match is read branch by branch, its punt branches dropped. -/
partial def paidRead (env : Environment) (st : Stack) (x : Expr) (fuel : Nat := 8) : MetaM PackRead := do
  if fuel == 0 then return { cls := "other(fuel)" }
  let mut x := peelSafe x
  if let .const c _ := x.getAppFn then
    if let some (_, discrs, brs) ← branchesOf c x.getAppArgs then
      let lab ← altLabeler st discrs
      let mut out : Array PackRead := #[]
      for b in brs do
        let (st', body) := enterAllF st lab x.getAppArgs[b]!
        let r ← paidRead env st' body (fuel - 1)
        unless r.cls == "punt" || r.cls.startsWith "other(" do out := out.push r
      if out.isEmpty then return { cls := "punt" }
      if out.size == 1 then return out[0]!
      return { cls := "alt[" ++ String.intercalate "|" (out.map (·.cls)).toList ++ "]",
               ns := String.intercalate "|" (out.map (·.ns)).toList, wits := out.foldl (· ++ ·.wits) #[],
               spend := String.intercalate "|" (out.map (·.spend)).toList, spendTail := out.any (·.spendTail) }
    if c == ``Or.inr || c == ``Or.inl then
      -- a nested option inside the paid arm (a stamp-or-slot pair): its arm
      -- is read as it stands
      if x.getAppNumArgs ≥ 3 then return ← paidRead env st (x.getArg! 2) (fuel - 1)
  let mut wits : Array (String × Bool) := #[]
  let mut fuel2 := 8
  while fuel2 > 0 do
    fuel2 := fuel2 - 1
    let xf := x.getAppFn
    let xa := x.getAppArgs
    match xf with
    | .const ``Exists.intro _ =>
      if xa.size ≥ 4 then
        let α := xa[0]!.consumeMData
        if α.isConstOf ``Nat then wits := wits.push (ppc st xa[2]!, false)
        else if α.isAppOf ``List then wits := wits.push (ppc st xa[2]!, true)
        x := peelSafe xa[3]!
      else break
    | .const ``And.intro _ =>
      if xa.size ≥ 4 then x := peelSafe xa[3]! else break
    | _ => break
  let ns := if wits.isEmpty then "—" else String.intercalate "," (wits.map (·.1)).toList
  let lists := wits.filter (·.2)
  if !lists.isEmpty && lists.all (·.1 == "[]") && wits.all (·.2) then return { cls := "empty", ns, wits }
  if x.isConstOf ``trivial || x.isConstOf ``True.intro then return { cls := "punt" }
  let (spend, bind) ← spendOf env st x
  let kind := bindKind bind
  let spendTail := match bind with | some b => hasHead b.ty tailN | none => false
  return { cls := s!"paid:{kind}", ns, wits, spend, spendTail }

partial def packCls (env : Environment) (st : Stack) (e : Expr) (vcLeft otherTrue : Bool) (fuel : Nat := 24) : MetaM PackRead := do
  if fuel == 0 then return { cls := "other(fuel)" }
  let e := peelSafe e
  let relayOf (x : Expr) : MetaM PackRead := do
    let src ← sourceOf st x
    return { cls := s!"relay:{bindKind (bindOf st x)}({src.getD s!"?{pp st x}"})" }
  match e with
  | .bvar _ => relayOf e
  | .proj _ _ b => relayOf b
  | .lam .. =>
    if isPredLam e then return { cls := "other(predicate)" }
    -- a bare closure (a parameter with no option around it)
    let (spend, bind) ← spendOf env st e
    return { cls := s!"paid:{bindKind bind}", spend, spendTail := match bind with | some b => hasHead b.ty tailN | none => false }
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if let some (_, discrs, brs) ← branchesOf n args then
        let lab ← altLabeler st discrs
        let mut out : Array PackRead := #[]
        for b in brs do
          let (st', body) := enterAllF st lab args[b]!
          out := out.push (← packCls env st' body vcLeft otherTrue (fuel - 1))
        -- a punt branch beside a paid one mirrors the source's own option
        let live := out.filter fun r => r.cls != "punt"
        if live.isEmpty then return { cls := "punt" }
        if live.size == 1 then return live[0]!
        return { cls := "alt[" ++ String.intercalate "|" (live.map (·.cls)).toList ++ "]",
                 ns := String.intercalate "|" (live.map (·.ns)).toList, wits := live.foldl (· ++ ·.wits) #[],
                 spend := String.intercalate "|" (live.map (·.spend)).toList, spendTail := live.any (·.spendTail) }
      if n == ``Or.inl && args.size ≥ 3 then
        if vcLeft then return ← paidRead env st args[2]! else return { cls := if otherTrue then "punt" else "stamp" }
      if n == ``Or.inr && args.size ≥ 3 then
        if !vcLeft then return ← paidRead env st args[2]! else return { cls := if otherTrue then "punt" else "stamp" }
      if (n == ``And.left || n == ``And.right) && args.size ≥ 3 then return ← relayOf args[2]!
      if (← getProjectionFnInfo? n).isSome && args.size ≥ 1 then return ← relayOf args[args.size - 1]!
      if n == ``Or.imp && args.size ≥ 7 then return { cls := s!"step({(← sourceOf st args[6]!).getD "?"})" }
      if (n == ``Or.imp_left || n == ``Or.imp_right) && args.size ≥ 5 then return { cls := s!"step({(← sourceOf st args[4]!).getD "?"})" }
      if n.getRoot == `L4YAML && isThmN env n then
        let mut inner : Array PackRead := #[]
        for a in args do
          let a' := peelSafe a
          let ok := match a' with
            | .lam .. => !isPredLam a'
            | .bvar .. => (match bindOf st a' with | some b => !isDataTy b.ty | none => false)
            | .app .. => (match a'.getAppFn with | .const m _ => !isCtorN env m | _ => true)
            | .proj .. => true
            | _ => false
          if ok then
            let r ← packCls env st a' vcLeft otherTrue (fuel - 1)
            unless r.cls.startsWith "other(" do inner := inner.push r
        let nss := inner.filterMap fun r => if r.ns == "—" then none else some r.ns
        let sps := inner.filterMap fun r => if r.spend == "—" then none else some r.spend
        return { cls := s!"via:{short n}[{String.intercalate ";" (inner.map (·.cls)).toList}]",
                 ns := if nss.isEmpty then "—" else String.intercalate "|" nss.toList,
                 wits := inner.foldl (· ++ ·.wits) #[],
                 spend := if sps.isEmpty then "—" else String.intercalate "|" sps.toList,
                 spendTail := inner.any (·.spendTail) }
      if x_isPaidCtor n then return ← paidRead env st e
      return { cls := s!"other({short2 n})" }
    | .bvar _ => relayOf f
    | _ => return { cls := "other(app)" }
  | _ => return { cls := "other(?)" }
where
  x_isPaidCtor (n : Name) : Bool := n == ``Exists.intro || n == ``And.intro

/-- The atoms of a written list (`a :: b :: []` → `[a, b]`, tail variable
    none; `nsU` → `[]`, variable `nsU`); a bare level is one atom. -/
def atomsOf (wits : Array (String × Bool)) (own : String) : List String × Option String := Id.run do
  let mut atoms : List String := []
  let mut var : Option String := none
  for (s, isList) in wits do
    unless isList do continue
    let parts := (s.splitOn " :: ").map (·.trimAscii.toString)
    match parts.getLast? with
    | some "[]" => atoms := atoms ++ parts.dropLast
    | some v => atoms := atoms ++ parts.dropLast; if var.isNone then var := some v
    | none => pure ()
  if atoms.isEmpty && var.isNone then
    match (wits.filter fun (_, l) => !l).back? with
    | some (s, _) => atoms := [s]
    | none => if own != "—" then atoms := [own]
  return (atoms.eraseDups, var)

/-- Which held shapes name a level of the written list. -/
def hits (holds : Array String) (atoms : List String) (var : Option String) : Array String := Id.run do
  let mut out : Array String := #[]
  for h in holds do
    let name := ((h.splitOn ":")[0]?).getD h
    let shape := (h.drop (name.length + 1)).toString
    let inner := if shape.startsWith "tail(" then Option.some (((shape.drop 5).toString.splitOn ")")[0]!)
      else if shape.startsWith "tailFact(" then some (((shape.drop 9).toString.splitOn ")")[0]!)
      else if shape.startsWith "frames(" then some (((shape.drop 7).toString.splitOn ")")[0]!)
      else none
    let some lv := inner | continue
    let hit := if shape.startsWith "frames(" then
        let parts := (lv.splitOn " :: ").map (·.trimAscii.toString)
        (match parts.head? with | some a => atoms.contains a | none => false) || (var.isSome && parts == [var.get!])
      else atoms.contains lv
    if hit then out := out.push name
  return out

/-! ## §3 The pins -/

def pinned : Bool := true
-- Item 371: every pack's conclusion is `⊢ ResumeFrames` (the one-level resume over the stream), not `⊢ SLYamlStream`.
-- 2026-10-30 (item 405): the two `h_kslot` packs and their lemma-premise twins read the head-form chain (`∃ nv0 ns, MarkedColsIn sc (nv0 :: ns) ∧ ∀ nv ∈ nv0 :: ns, …`); `h_explUp` carries its `MarkedColsIn` conjunct.
-- 2026-10-30 (item 405, Rule 8 fix): the two `h_kslot` packs read `lvl=∀nv∈markedCols(…)` — the chain re-indexed by the projection, no `∃nv0∃ns`.
def expectedPacks : List String := [
  "pendingContent.h_vpack arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingProps.h_kslot arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingProps.h_kslotE arm=l lvl=∃ne(n=ne + 1)∀nv∈markedCols(…) premises=[SBlockNode(n),SCompactSeqTail(ne),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingBlockContent.h_kslot arm=l lvl=∀nv∈markedCols(…) premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingBlockContent.h_kslotUp arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingBlock.h_kslot arm=l lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingBlock.h_kslotUp arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "pendingMapValue.h_ivl arm=r/stamp lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  -- Item 288: the field's other disjunct is the stamp, not `True`.
  "pendingMapValue.h_vslot arm=l/stamp lvl=(sc.currentIndent≤n)(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
  "pendingMapValue.h_kslot arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  -- 2026-10-24 (item 350): `arm=l` → `arm=l/stamp` — the alternative is the scanner fact
  -- `NotQuestionPark sc` now, which the census reads as a stamp, not a `PackAlt` escape.
  "pendingMapValue.h_explUp arm=l/stamp lvl=∃sp_q∃ns(GLit('?'))(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  -- 2026-10-31 (item 412): the `?` park's route one frame up — `h_expl`'s chain is read over the park's OWN ENTRY
  -- (`SBlockMapEntry n`), projected on `markedCols sc` minus the own mark (`Ne`), and declines into `PackAlt sc`.
  "pendingMapValue.h_expl arm=l/stamp lvl=∃sp_q(GLit('?'))(?)∀nv∈markedCols(…) premises=[Ne,SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no"]
def expectedFramesOn : List String := [
  "pendingContent.h_framesV frames(ks)@ExplValueLine(nv)←landing",
  "pendingProps.h_closeFV frames(ks)@ExplValueLine(nv)←SBlockNode(n)",
  "pendingProps.h_closeFEV frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)",
  "pendingBlockContent.h_closeFV frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)",
  "pendingBlock.h_closeFV frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)",
  "pendingMapValue.h_closeFV frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1)",
  "pendingMapValue.h_framesV frames(ks)@ExplValueLine(nv)←landing"]
-- 2026-10-20 (item 309): `explFrameValueLine.h_kslot` and `flowVPack_of_close.h_vslot` read `arm=l/stamp` — the census
-- reads a right disjunct other than `True` as the stamp face; theirs is the generic alternative `alt`.
  -- Item 287: `h_vslot`'s other disjunct is the caller's reading of an inline
  -- residue, not `True`, which the census marks `/stamp`.
  -- item 311: `colon_open_map_implicit` states the alternative generically (`{alt : Prop}`), so its premise reads
  -- `arm=l/stamp` (a right disjunct other than `True`), as the three generic helpers do since item 309.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-30 (item 405, Rule 8 fix): the three `h_kslot` parameters read `lvl=∀nv∈markedCols(…)` (projection, no `∃nv0∃ns`).
-- 2026-10-30 (item 408): `flowKeyPack_of_close.h_key` lvl `∃ns∀nv∈ns` → `∀nv∈markedCols(…)` and
-- `flowKeyRoute_of_open.h_compact_pair` lvl `∃nv0∃ns∀nv∈nv0 :: ns` → `∀nv∈markedCols(…)`: the pair rides the
-- scanner-state projection, not a proof-side list (Rule 8).
def expectedParams : List String :=
  ["accum_content_on_pendingMapValue_indented.h_ivl_mv arm=r/stamp lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
    "accum_content_on_pendingMapValue_indented.h_vslot arm=l lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
    "entryChainMap.up arm=l lvl=∀nvX∈ns premises=[SBlockIndented(n),SCompactSeqTail(n)] ⊢ ExplValueLine(nvX) tail=no",
    "explEntryChain_of_keyContent.up arm=l lvl=∀nv∈markedCols(…) premises=[Ne,SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
    "slotChainMap.up arm=l lvl=∀nvX∈ns premises=[SBlockIndented(nv)] ⊢ ExplValueLine(nvX) tail=no",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_block_on_closeThenBlock.h_vpack arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_block_on_closeThenBlock.h_vslot arm=l/stamp lvl=∃nv∃sp_a(SLYamlStream(sp_start))(sc.currentIndent≤nv)(needIndentCheck(…)=false)(simpleKeyAllowed(…)=true)(sp_gram=sp_scan)(sp_scan.col=nv + 1)(?)(Or)∃nsU(MarkedColsIn)∀nvU∈nsU premises=[SBlockIndented(nv),SIndent(nvU),GLit(':'),SBlockIndented(nvU)] ⊢ ResumeFrames tail=no",
   "accum_block_on_pendingBlock.h_kslot arm=l lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_block_on_pendingBlock.h_kslotUp arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_block_on_pendingBlockContent.h_kslot arm=l lvl=∀nv∈markedCols(…) premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_block_on_pendingBlockContent.h_kslotUp arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_block_on_pendingContent.h_vpack arm=l lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_content_on_pendingBlock_indented.h_kslotUp_old arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_content_on_pendingBlock_indented.h_kslot_old arm=l lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "accum_content_on_pendingMapValue_indented.h_kslot arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "colon_open_map_explicit.hvp arm=l lvl= premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "colon_open_map_implicit.h_kslotD arm=l/stamp lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "colon_open_map_props.h_kslotD arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   -- Item 409 (2026-10-30): the pack faces and `h_compact`/`h_ivl`/`h_nodeV` carry the `MarkedColsIn`
   -- domain conjunct; `explFrameValueLine` deleted (its callers pass the park's domained chain).
   "entryKeyPack_of_dispatch.h_compact arm=l lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "entryKeyPack_of_dispatch.h_ivl arm=r/stamp lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "entryKeyPack_of_dispatch.h_nodeV arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "entryPropsKeyPack_of_dispatch.h_compact arm=l lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "entryPropsKeyPack_of_dispatch.h_ivl arm=r/stamp lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "entryPropsKeyPack_of_dispatch.h_nodeV arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "flowKeyPack_of_close.h_key arm=l lvl=∃k∃sp_key(?)(?)(kc=k)(And)∀nv∈markedCols(…) premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "flowKeyRoute_of_open.h_compact_pair arm=l lvl=∀nv∈markedCols(…) premises=[SBlockIndented(nc),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "flowVPack_of_close.h_vslot arm=l/stamp lvl=∃ns∀nv∈ns premises=[SFlowContent(n),SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "indicator_open_map.h_explUp_chain arm=l lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "indicator_open_map.h_explUp_chainD arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "question_open_map.h_explUp_chain arm=l lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "question_open_map.h_explUp_chainD arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  -- 2026-10-31 (item 412): the consumer reads the entry-shaped `h_expl` (its twin of the pack row).
  "accum_content_on_pendingMapValue_indented.h_expl arm=l/stamp lvl=∃sp_q(GLit('?'))(?)∀nv∈markedCols(…) premises=[Ne,SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   -- Item 413: the opener's relay parameter — the `-` / slot park's chain over the entry's CONTENT, on the projection.
   "compact_open_map.h_chainUp arm=l lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "colon_open_map.h_explUp_chainD arm=l lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no"]
-- The nine rows carrying a `(h_vslot)`-style binder list after `<param:…` read
-- the list through `letLabel`'s `privateToUserName`.  Without it the module
-- system's name for a generated matcher (`_private.<module>.0.<name>`) fails a
-- root test and all nine come out bare -- 151 rows in, 151 rows out, the names
-- silently absent, every tally unchanged.  The list is the only thing that
-- moves, which is what made it worth a one-line fix rather than a re-pin.
-- Item 287: the eleven writers of `accum_block_on_closeThenBlock.h_vslot`.  Its
-- other disjunct is the caller's reading of an inline residue now, so the ten
-- that wrote `Or.inr trivial` (`punt`) write a disjunct that is not `True`,
-- which this census labels `stamp`, and the value park's split reads both.
-- Item 288: and the three producers that declined `pendingMapValue.h_vslot`
-- with `True` write the stamp.
-- Item 304: the value-line writers spend the route helpers' `KeyFrames` twins
-- (`resumeFrameRouteK`, `resumeMapRouteK`); the rows name the spend.
-- Item 305: `closeThenBlock`'s writers read the `?` slot's pack behind the first entry's stack and `h_kslot` (`h_slotV`, the compact fill's bottom).
-- 2026-10-20 (item 307): five rows re-read — the three γ roots' `h_vpack` are paid (`close(closeFV←h_closeFV_old)`
-- at the two block routes and at the content route — a `match` on `h_mapFV108`) where item 301 read punts; `closeThenBlock`'s
-- `h_kslot` is `alt[paid:chain | relay:chain(h_resKslot < h_resSeqV < h_mapFV)]` and its `h_kslotUp` row names the new haves.
-- 2026-10-21 (item 313): the props parks' `h_kslot`/`h_kslotE` and the mapping value's `h_kslot` are written through
-- `.imp id (PackAlt.step_content …)`: a `step` on the door (or on `explFrameValueLine`'s return) where the census read a
-- verbatim relay or a `via`; the holdings are unchanged.
-- 2026-10-21 (item 314): six key-pack premises of `accum_content_on_pendingBlock_indented` are built from a `match` whose
-- declining arm hands the alternative on (`alt[…]` around the chain) where it declined with `trivial`.
-- 2026-10-21 (item 319): two rows re-read — `accum_block_on_closeThenBlock #1`'s `h_kslot` writer reads `step` for `relay`
-- (its `h_resKslot` relay is `.imp id (PackAlt.step_blockEntry …)` now), and `accum_block_pending #7`'s `h_vslot` premise
-- spends `alt[up←door|h_alt←door]` for `up←door` (the declining arm hands `h_alt` on); regenerated from the census's own rows.
-- 2026-10-23 (item 345): `accum_content_pending #1–#3 h_kslotUp` punt → paid:chain (ns = [nv] from the park's `h_kslotE_k`).
-- 2026-10-24 (item 350): the `:` producers write `h_explUp` as the stamp `NotQuestionPark sc` (was
-- `punt`); `compact_open_map`/`question_open_map` and the `h_vpack` consumers spend `empty` on the
-- `inr` arm (`ns := []`) instead of relaying the alternative.
-- 2026-10-26 (item 369): 18 rows re-read — `pendingBlock.h_closeF` is kept into `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames), so every writer under that lemma holds one more frame fact.
-- 2026-10-30 (item 405): the chain writers read the head-form chain (`ns=nv0,ns`), the `closeThenBlock` births `hkv`+`hkvUp`, and the declines (`punt`/`stamp`) of ruling "405 a".
-- 2026-10-30 (item 405, Rule 8 fix): the chain writers read the projection — `paid:chain ns=markedCols(…)`/`ns=nv,nsU` through `MarkedColsIn.relay`, the relays into the `∃ ns` faces pass `markedCols sc`, and the two head consumers split on `markedCols sc` (`alt[paid:chain|punt]`).
-- 2026-10-30 (item 408): `accum_flow_open_depth0`'s `h_compact_pair` writers — the `pendingMapValue` arm's fabricated
-- singleton chain is now a DECLINE; the `-` arm passes its projection routes directly (no head split).
def expectedWriters : List String := [
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeV idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeV idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "colon_fires_implicit_key #1 param:colon_open_map_implicit.h_kslotD idx=— := step(param:colon_fires_implicit_key.h_key) ns=— spend=— holds=[h✝:tail(k)←SBlockMapEntry(k); h✝:tail(k)←SBlockMapEntry(k); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_kslot_pk:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_rfr_pk:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_rfrV_pk:tail(k)←SBlockMapEntry(k); h_rseq_pk:tail(k)←SBlockMapEntry(k)] ⊢ —",
   "colon_fires_props_key #1 param:colon_open_map_props.h_kslotD idx=— := step(param:colon_fires_props_key.h_key) ns=— spend=— holds=[left✝:tail(k)←SBlockMapEntry(k); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_kslot_pk:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_resF_pk:tail(k)←SBlockMapEntry(k); h_resFV_pk:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "accum_block_on_noPending #1 ctor:pendingBlock.h_kslot idx=k := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_on_noPending #1 ctor:pendingBlock.h_kslotUp idx=k := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_on_noPending #1 param:indicator_open_map.h_explUp_chain idx=— := punt ns=— spend=— holds=[] ⊢ —",
     "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[] ⊢ —",
  "accum_flow_open_depth0 #1 param:flowKeyRoute_of_open.h_compact_pair idx=— := punt ns=— spend=— holds=[main:frames(ks)←landing] ⊢ —",
  "accum_flow_open_depth0 #1 param:explEntryChain_of_keyContent.up idx=— := relay:chain(door:pendingMapValue.h_expl) ns=— spend=— holds=[main:frames(ks)←landing; h_expl:tail(n_old)←SBlockMapEntry(n_old); h_kslot_mv:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_mv:frames(map(…) :: ks)←SBlockNode(n_old + 1); h_frames✝:frames(ks)←landing; h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV✝:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(n_old)←SBlockNode(n_old + 1); h_explUp_mv:frames(map(…) :: [])←SBlockIndented(nv); route:tail(n_old)←SBlockMapEntry(n_old); h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); up:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
  "accum_step_flow #1 ctor:pendingContent.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_step_flow #1 param:flowKeyPack_of_close.h_key idx=— := relay:other(let:h_tuple<let:h_gap(tl,h_gap)) ns=— spend=— holds=[] ⊢ —",
  "accum_step_flow #2 ctor:pendingContent.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_step_flow #2 param:flowKeyPack_of_close.h_key idx=— := relay:other(let:h_tuple<let:h_gap(tl,h_gap)) ns=— spend=— holds=[] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_ivl idx=k := stamp ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_vslot idx=k := stamp ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_kslot idx=k := paid:chain ns=ns spend=chain←param:colon_open_map.h_explUp_chainD holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ level-var",
  "colon_open_map #1 ctor:pendingMapValue.h_explUp idx=k := stamp ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingProps.h_kslot idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingProps.h_kslotE idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingProps.h_kslot idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingProps.h_kslotE idx=0 := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #1 ctor:pendingContent.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "content_dispatch_routed #2 ctor:pendingContent.h_vpack idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "accum_block_on_noPending #1 param:indicator_open_map.h_explUp_chainD idx=— := punt ns=— spend=— holds=[] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_ivl idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_vslot idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_kslot idx=k := paid:chain ns=ns spend=kslot←param:colon_open_map_implicit.h_kslotD⊣tail holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ level-var",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_explUp idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_ivl idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_vslot idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_kslot idx=k := paid:chain ns=ns spend=kslot←param:colon_open_map_props.h_kslotD⊣tail holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ level-var",
  "colon_open_map_props #1 ctor:pendingMapValue.h_explUp idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslot idx=k := paid:other ns=— spend=relay(h_mcstep_ne←param:accum_block_on_closeThenBlock.h_mcstep_ne) holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_seqBottom:frames([])←SCompactSeqTail(k); h_seqFrames:frames(ks)←SCompactSeqTail(k); h_slotV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k); h_resSeqV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k); h_resKslot:frames(map(…) :: [])←SBlockIndented(nv); h_slotV':frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k); h_seqFramesV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ held(h_res_land,h_resV_land)",
   "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslotUp idx=k := punt ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_seqBottom:frames([])←SCompactSeqTail(k); h_seqFrames:frames(ks)←SCompactSeqTail(k); h_slotV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k); h_resSeqV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k); h_resKslot:frames(map(…) :: [])←SBlockIndented(nv); h_slotV':frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k); h_seqFramesV:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ —",
   "accum_block_on_closeThenBlock #1 param:indicator_open_map.h_explUp_chain idx=— := alt[paid:chain|paid:chain|paid:chain] ns=nv :: nsU|nv :: []|nsU spend=slotChainMap(alt[kv←param:accum_block_on_closeThenBlock.h_vslot|kvU←param:accum_block_on_closeThenBlock.h_vslot])|slotChainMap(kv←param:accum_block_on_closeThenBlock.h_vslot)|slotChainMap(kvU←param:accum_block_on_closeThenBlock.h_vslot) holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ none",
   "accum_block_on_closeThenBlock #1 param:indicator_open_map.h_explUp_chainD idx=— := punt ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing] ⊢ —",
   "accum_block_on_closeThenBlock #1 param:slotChainMap.up idx=— := paid:chain ns=— spend=alt[kv←param:accum_block_on_closeThenBlock.h_vslot|kvU←param:accum_block_on_closeThenBlock.h_vslot] holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; hkv:frames(map(…) :: [])←SBlockIndented(nv); hkvUp:frames(map(…) :: [])←SBlockIndented(nvU); kv:frames(map(…) :: [])←SBlockIndented(nv); kvU:frames(map(…) :: [])←SBlockIndented(nvU)] ⊢ level-var",
   "accum_block_on_closeThenBlock #2 param:slotChainMap.up idx=— := paid:chain ns=— spend=kv←param:accum_block_on_closeThenBlock.h_vslot holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; hkv:frames(map(…) :: [])←SBlockIndented(nv); hkvUp:frames(map(…) :: [])←SBlockIndented(nvU); kv:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_block_on_closeThenBlock #3 param:slotChainMap.up idx=— := relay:chain(param:accum_block_on_closeThenBlock.h_vslot) ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; hkv:frames(map(…) :: [])←SBlockIndented(nv); hkvUp:frames(map(…) :: [])←SBlockIndented(nvU); kvU:frames(map(…) :: [])←SBlockIndented(nvU)] ⊢ —",
   "accum_block_on_closeThenBlock #1 param:colon_open_map_explicit.hvp idx=— := relay:chain(λ:hvp) ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; hvp:frames(map(…) :: [])←SBlockIndented(k)] ⊢ —",
   "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslot idx=nv + 1 + m := paid:other ns=— spend=relay(h_mcstep_ne←param:accum_block_on_closeThenBlock.h_mcstep_ne) holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h✝:frames(map(…) :: [])←SBlockIndented(nv); h✝:frames(map(…) :: [])←SBlockIndented(nv); h✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); hkv:frames(map(…) :: [])←SBlockIndented(nv); hkvUp:frames(map(…) :: [])←SBlockIndented(nvU)] ⊢ none",
   "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslotUp idx=nv + 1 + m := paid:chain ns=nv :: nsU spend=alt[kv←param:accum_block_on_closeThenBlock.h_vslot|kvU←param:accum_block_on_closeThenBlock.h_vslot] holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h✝:frames(map(…) :: [])←SBlockIndented(nv); h✝:frames(map(…) :: [])←SBlockIndented(nv); h✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); hkv:frames(map(…) :: [])←SBlockIndented(nv); hkvUp:frames(map(…) :: [])←SBlockIndented(nvU)] ⊢ none",
   "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslot idx=k := paid:other ns=— spend=relay(h_mcstep_ne←param:accum_block_on_pendingBlock.h_mcstep_ne) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ none",
   "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlock.h_kslotUp holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslot idx=k := paid:other ns=— spend=relay(h_mcstep_ne←param:accum_block_on_pendingBlock.h_mcstep_ne) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ none",
   "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlock.h_kslotUp holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:frames ns=nv :: [] spend=close(closeFV←param:accum_block_on_pendingBlock.h_closeFV_old) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ none",
   "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ —",
   "accum_block_on_pendingBlock #1 param:indicator_open_map.h_explUp_chain idx=— := alt[paid:chain|paid:chain|paid:chain] ns=hAppend(…)|markedCols(…)|nsU spend=entryChainMap(alt[kslot←param:accum_block_on_pendingBlock.h_kslot|kslotU←param:accum_block_on_pendingBlock.h_kslot])|entryChainMap(kslot←param:accum_block_on_pendingBlock.h_kslot)|entryChainMap(kslotU←param:accum_block_on_pendingBlock.h_kslot) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_block_on_pendingBlock #1 param:indicator_open_map.h_explUp_chainD idx=— := alt[paid:chain|paid:chain] ns=hAppend(…)|nsU spend=entryChainMap(alt[kslot←param:accum_block_on_pendingBlock.h_kslot|kslotU←param:accum_block_on_pendingBlock.h_kslot])|entryChainMap(kslotU←param:accum_block_on_pendingBlock.h_kslot) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_block_on_pendingBlock #1 param:entryChainMap.up idx=— := paid:chain ns=— spend=alt[kslot←param:accum_block_on_pendingBlock.h_kslot|kslotU←param:accum_block_on_pendingBlock.h_kslot] holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n); kslot:frames(map(…) :: [])←SBlockIndented(nv); kslotU:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_block_on_pendingBlock #2 param:entryChainMap.up idx=— := relay:chain(param:accum_block_on_pendingBlock.h_kslot) ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n); kslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_block_on_pendingBlock #3 param:entryChainMap.up idx=— := relay:chain(param:accum_block_on_pendingBlock.h_kslot) ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n); kslotU:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_block_on_pendingBlock #4 param:entryChainMap.up idx=— := paid:chain ns=— spend=alt[kslot←param:accum_block_on_pendingBlock.h_kslot|kslotU←param:accum_block_on_pendingBlock.h_kslot] holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n); kslot:frames(map(…) :: [])←SBlockIndented(nv); kslotU:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_block_on_pendingBlock #5 param:entryChainMap.up idx=— := relay:chain(param:accum_block_on_pendingBlock.h_kslot) ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n); kslotU:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_block_on_pendingBlock #1 param:colon_open_map_explicit.hvp idx=— := paid:chain ns=— spend=kslot←λ:kslot holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n); kslot:frames(map(…) :: [])←SBlockIndented(k)] ⊢ level-var",
   "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslot idx=n + 1 + m := paid:other ns=— spend=relay(h_mcstep_ne←param:accum_block_on_pendingBlock.h_mcstep_ne) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ none",
   "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslotUp idx=n + 1 + m := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlock.h_kslotUp holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslot idx=k := paid:other ns=— spend=relay(h_mcstep_ne←param:accum_block_on_pendingBlockContent.h_mcstep_ne) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
   "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslotUp idx=k := paid:chain ns=ns spend=kslot←param:accum_block_on_pendingBlockContent.h_kslotUp holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:frames ns=nv :: [] spend=close(closeFV←param:accum_block_on_pendingBlockContent.h_closeFV_old) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
   "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
   "accum_block_on_pendingBlockContent #1 param:indicator_open_map.h_explUp_chain idx=— := punt ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
   "accum_block_on_pendingBlockContent #1 param:indicator_open_map.h_explUp_chainD idx=— := punt ns=— spend=— holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ —",
   "accum_block_on_pendingBlockContent #1 param:colon_open_map_explicit.hvp idx=— := paid:chain ns=— spend=kslot←λ:kslot holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); kslot:frames(map(…) :: [])←SBlockIndented(k)] ⊢ level-var",
   "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := relay:chain(param:accum_block_on_pendingContent.h_vpack) ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
   "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
   "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:frames ns=nv :: [] spend=close(fV←param:accum_block_on_pendingContent.h_mapFV108) holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ none",
   "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_seqF168:tail(kk)←landing; h_mapF109:frames(ks)←landing; h_mapFV108:frames(ks)@ExplValueLine(nv)←landing] ⊢ —",
   "accum_block_pending #1 param:accum_block_on_pendingContent.h_vpack idx=— := step(door:pendingContent.h_vpack) ns=— spend=— holds=[h_vpack51:frames(map(…) :: [])←SBlockIndented(nv); h_framesS109:frames(ks)←landing; h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(kk)←landing] ⊢ —",
   "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_kslot91:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE✝:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
   "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_kslot91:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE✝:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
   "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_kslot91:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE✝:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
   "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_kslot91:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE✝:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE✝:frames(ks)←SCompactSeqTail(ne); h_closeF✝:frames(ks)←SBlockNode(n_p); h_closeFV_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n_p); h_closeFEV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
   "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslot idx=— := relay:chain(door:pendingBlockContent.h_kslot) ns=— spend=— holds=[h_kslot92:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_kslotUp190:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
   "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslotUp idx=— := relay:chain(door:pendingBlockContent.h_kslotUp) ns=— spend=— holds=[h_kslot92:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_kslotUp190:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
   "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslot idx=— := relay:chain(door:pendingBlock.h_kslot) ns=— spend=— holds=[h_kslot92:frames(map(…) :: [])←SBlockIndented(nv); h_closeF369:frames(ks)←SCompactSeqTail(n_old); h_kslotUp190:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
   "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslotUp idx=— := relay:chain(door:pendingBlock.h_kslotUp) ns=— spend=— holds=[h_kslot92:frames(map(…) :: [])←SBlockIndented(nv); h_closeF369:frames(ks)←SCompactSeqTail(n_old); h_kslotUp190:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
   "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingMapValue.h_kslot holds=[h_expl51:tail(nmv)←SBlockMapEntry(nmv); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF155:frames(map(…) :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1); h_explUp190:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vslot idx=— := stamp ns=— spend=— holds=[h_expl51:tail(nmv)←SBlockMapEntry(nmv); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF155:frames(map(…) :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1); h_explUp190:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vpack idx=— := via:frameChainUnion[via:frameChainUnion[alt[paid:tail|empty];paid:chain];alt[paid:chain|empty]] ns=nmv :: []|[]|ns|nsU|[] spend=frameChainOne(one(route←door:pendingMapValue.h_expl))|—|kslot←door:pendingMapValue.h_kslot|up←door:pendingMapValue.h_explUp|—⊣tail holds=[h_expl51:tail(nmv)←SBlockMapEntry(nmv); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF155:frames(map(…) :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1); h_explUp190:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ held(h_expl51,h_seqF✝)",
   "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vslot idx=— := alt[paid:chain|stamp] ns=nmv|— spend=up←door:pendingMapValue.h_explUp|— holds=[h_expl51:tail(nmv)←SBlockMapEntry(nmv); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF155:frames(map(…) :: ks)←SBlockNode(nmv + 1); h_frames173:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(nmv + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(nmv)←SBlockNode(nmv + 1); h_explUp190:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ held(h_expl51,h_seqF✝)",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslot idx=n := paid:chain ns=— spend=relay(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslotUp idx=n := paid:chain ns=ns spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslotUp_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_nodeV idx=— := paid:chain ns=markedCols(…) spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_compact idx=— := paid:chain ns=— spend=alt[kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old|h←param:accum_content_on_pendingBlock_indented.h_kslot_old] holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_ivl idx=— := paid:chain ns=— spend=alt[kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old|h←param:accum_content_on_pendingBlock_indented.h_kslot_old] holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslot idx=n + 1 := paid:chain ns=markedCols(…) spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslotE idx=n + 1 := paid:chain ns=n spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV idx=— := paid:chain ns=markedCols(…) spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact idx=— := paid:chain ns=— spend=alt[kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old|h←param:accum_content_on_pendingBlock_indented.h_kslot_old] holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl idx=— := paid:chain ns=— spend=alt[kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old|h←param:accum_content_on_pendingBlock_indented.h_kslot_old] holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslot idx=n := paid:chain ns=— spend=relay(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
   "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslotUp idx=n := paid:chain ns=ns spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslotUp_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslot idx=n := paid:chain ns=— spend=relay(kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old) holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ none",
   "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslotUp idx=n := paid:chain ns=ns spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslotUp_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_nodeV idx=— := paid:chain ns=markedCols(…) spend=kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_compact idx=— := paid:chain ns=— spend=alt[kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old|h←param:accum_content_on_pendingBlock_indented.h_kslot_old] holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_ivl idx=— := paid:chain ns=— spend=alt[kslot←param:accum_content_on_pendingBlock_indented.h_kslot_old|h←param:accum_content_on_pendingBlock_indented.h_kslot_old] holds=[h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_old:frames(ks)←SCompactSeqTail(n); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n)] ⊢ level-var",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_vpack idx=— := via:frameChainUnionD[paid:tail;paid:chain] ns=markedCols(…)|ns spend=explEntryChain_of_keyContent(route←param:accum_content_on_pendingMapValue_indented.h_expl)|kslot←param:accum_content_on_pendingMapValue_indented.h_kslot⊣tail holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_compact idx=— := relay:chain(let:h_compact_vslot<param:accum_content_on_pendingMapValue_indented.h_vslot(h_vslot)) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_ivl idx=— := relay:chain(let:h_ivl_pack<param:accum_content_on_pendingMapValue_indented.h_ivl_mv(h_ivl_mv)) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslot idx=n + 1 := step(param:accum_content_on_pendingMapValue_indented.h_kslot) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslotE idx=n + 1 := punt ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact idx=— := relay:chain(let:h_compact_vslot<param:accum_content_on_pendingMapValue_indented.h_vslot(h_vslot)) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl idx=— := relay:chain(let:h_ivl_pack<param:accum_content_on_pendingMapValue_indented.h_ivl_mv(h_ivl_mv)) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #1 param:explEntryChain_of_keyContent.up idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_expl) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv); route:tail(n)←SBlockMapEntry(n); h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); up:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_vpack idx=— := via:frameChainUnionD[paid:tail;paid:chain] ns=markedCols(…)|ns spend=explEntryChain_of_keyContent(route←param:accum_content_on_pendingMapValue_indented.h_expl)|kslot←param:accum_content_on_pendingMapValue_indented.h_kslot⊣tail holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_vpack idx=— := via:frameChainUnionD[paid:tail;paid:chain] ns=markedCols(…)|ns spend=explEntryChain_of_keyContent(route←param:accum_content_on_pendingMapValue_indented.h_expl)|kslot←param:accum_content_on_pendingMapValue_indented.h_kslot⊣tail holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "accum_content_on_pendingMapValue_indented #3 param:explEntryChain_of_keyContent.up idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_expl) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv); route:tail(n)←SBlockMapEntry(n); h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); up:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_compact idx=— := relay:chain(let:h_compact_vslot<param:accum_content_on_pendingMapValue_indented.h_vslot(h_vslot)) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_ivl idx=— := relay:chain(let:h_ivl_pack<param:accum_content_on_pendingMapValue_indented.h_ivl_mv(h_ivl_mv)) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_on_pendingMapValue_indented #2 param:explEntryChain_of_keyContent.up idx=— := relay:chain(param:accum_content_on_pendingMapValue_indented.h_expl) ns=— spend=— holds=[h_expl:tail(n)←SBlockMapEntry(n); h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: [])←SBlockIndented(nv); h_compact_vslot:frames(map(…) :: [])←SBlockIndented(nv); route:tail(n)←SBlockMapEntry(n); h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); up:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_pending #1 ctor:pendingProps.h_kslot idx=n := step(door:pendingProps.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
   "accum_content_pending #1 ctor:pendingProps.h_kslotE idx=n := step(door:pendingProps.h_kslotE) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
   "accum_content_pending #2 ctor:pendingProps.h_kslot idx=n := step(door:pendingProps.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
   "accum_content_pending #2 ctor:pendingProps.h_kslotE idx=n := step(door:pendingProps.h_kslotE) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ —",
   "accum_content_pending #1 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(0); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(0); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
   "accum_content_pending #2 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(0); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(0); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne)] ⊢ level-var",
   "accum_content_pending #1 ctor:pendingBlockContent.h_kslot idx=k := paid:chain ns=— spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ none",
   "accum_content_pending #1 ctor:pendingBlockContent.h_kslotUp idx=k := paid:chain ns=markedCols(…) spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
   "accum_content_pending #3 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
   "accum_content_pending #2 ctor:pendingBlockContent.h_kslot idx=k := paid:chain ns=— spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ none",
   "accum_content_pending #2 ctor:pendingBlockContent.h_kslotUp idx=k := paid:chain ns=markedCols(…) spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
   "accum_content_pending #4 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
   "accum_content_pending #3 ctor:pendingBlockContent.h_kslot idx=k := paid:chain ns=— spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ none",
   "accum_content_pending #3 ctor:pendingBlockContent.h_kslotUp idx=k := paid:chain ns=markedCols(…) spend=kslotE←let:h_kslotE_k<door:pendingProps.h_kslotE holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
   "accum_content_pending #5 ctor:pendingContent.h_vpack idx=— := paid:chain ns=ns spend=kslot←door:pendingProps.h_kslot holds=[h_defer_split:frames(ks)←landing; h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(n); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(n); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslot_p:frames(map(…) :: [])←SBlockIndented(nv); h_kslotE_p:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_p:frames(ks)←SCompactSeqTail(ne); h_closeFS_p:frames(ks)←SBlockNode(k + 1); h_closeFVS_p:frames(ks)@ExplValueLine(nv)←SBlockNode(k + 1); h_closeFEV_p:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(ne); h_kslotE_k:frames(map(…) :: [])←SBlockIndented(nv); h_closeFE_k:frames(ks)←SCompactSeqTail(k); h_closeFEV_k:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(k)] ⊢ level-var",
   "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslot_old idx=— := relay:chain(door:pendingBlock.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_kslot92:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_kslotUp190:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
   "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslotUp_old idx=— := relay:chain(door:pendingBlock.h_kslotUp) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_kslot92:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(ks)←SCompactSeqTail(n_old); h_kslotUp190:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV198:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ —",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_vslot idx=— := step(door:pendingMapValue.h_vslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_expl51:tail(n_old)←SBlockMapEntry(n_old); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1); h_explUp✝:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_kslot idx=— := relay:chain(door:pendingMapValue.h_kslot) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_expl51:tail(n_old)←SBlockMapEntry(n_old); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1); h_explUp✝:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_ivl_mv idx=— := relay:chain(door:pendingMapValue.h_ivl) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_expl51:tail(n_old)←SBlockMapEntry(n_old); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1); h_explUp✝:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "accum_flow_open_depth0 #2 param:flowKeyRoute_of_open.h_compact_pair idx=— := paid:chain ns=— spend=kslot←door:pendingBlock.h_kslot holds=[main:frames(ks)←landing; h_kslot_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeF✝:frames(ks)←SCompactSeqTail(n_old); h_kslotUp_old:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV✝:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n_old)] ⊢ level-var",
   -- 2026-10-29 (item 394): the mapping arm names `h_closeF_mv` (it supplies `FlowBaseRoutes.valueF`); the writer row reads the binder by name.
   "accum_flow_open_depth0 #3 param:flowKeyRoute_of_open.h_compact_pair idx=— := paid:tail ns=— spend=explEntryChain_of_keyContent(route←door:pendingMapValue.h_expl)⊣tail holds=[main:frames(ks)←landing; h_expl:tail(n_old)←SBlockMapEntry(n_old); h_kslot_mv:frames(map(…) :: [])←SBlockIndented(nv); h_closeF_mv:frames(map(…) :: ks)←SBlockNode(n_old + 1); h_frames✝:frames(ks)←landing; h_closeFV✝:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV✝:frames(ks)@ExplValueLine(nv)←landing; h_seqF✝:tail(n_old)←SBlockNode(n_old + 1); h_explUp_mv:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ level-var",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_ivl idx=nv := paid:chain ns=— spend=h_slot←let:h_slot holds=[hvp:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ none",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_vslot idx=nv := paid:chain ns=— spend=h_slot←let:h_slot holds=[hvp:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ none",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_kslot idx=nv := punt ns=— spend=— holds=[hvp:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_explUp idx=nv := stamp ns=— spend=— holds=[hvp:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "compact_open_map #1 ctor:pendingMapValue.h_ivl idx=n + 1 + m := relay:other(?right(…)) ns=— spend=— holds=[h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); h_expl105:tail(n + 1 + m)←SBlockMapEntry(n + 1 + m)] ⊢ —",
   "compact_open_map #1 ctor:pendingMapValue.h_vslot idx=n + 1 + m := relay:chain(let:h_vslot105<param:compact_open_map.hc(hc)) ns=— spend=— holds=[h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); h_expl105:tail(n + 1 + m)←SBlockMapEntry(n + 1 + m)] ⊢ —",
   "compact_open_map #1 ctor:pendingMapValue.h_kslot idx=n + 1 + m := punt ns=— spend=— holds=[h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); h_expl105:tail(n + 1 + m)←SBlockMapEntry(n + 1 + m)] ⊢ —",
   "compact_open_map #1 ctor:pendingMapValue.h_explUp idx=n + 1 + m := alt[stamp|stamp] ns=—|— spend=—|— holds=[h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); h_expl105:tail(n + 1 + m)←SBlockMapEntry(n + 1 + m)] ⊢ held(h_expl105)",
   -- Item 413: the two RELAYS of `compact_open_map.h_chainUp` — the inline fill's slot routes (`hkv` heads, `hkvUp`
   -- follows, through `MarkedColsIn.relay`) and the `pendingBlock` arm's `h_kslotUp` at the `nil` tail; both `paid:chain`.
   "accum_block_on_closeThenBlock #1 param:compact_open_map.h_chainUp idx=— := paid:chain ns=— spend=relay(alt[kv←param:accum_block_on_closeThenBlock.h_vslot|kvU←param:accum_block_on_closeThenBlock.h_vslot]) holds=[h_vpack:frames(map(…) :: [])←SBlockIndented(nv); h_vslot:frames(map(…) :: [])←SBlockIndented(nv); h_valF:frames(map(…) :: ks)←SBlockNode(nv + 1); h_mapF:frames(ks)←landing; h_mapFV:frames(ks)@ExplValueLine(nv)←landing; h_valFV:frames(ks)@ExplValueLine(nv)←SBlockNode(nn + 1); h✝:frames(map(…) :: [])←SBlockIndented(nv); h✝:frames(map(…) :: [])←SBlockIndented(nv); h✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); right✝:frames(map(…) :: [])←SBlockIndented(nv); hkv:frames(map(…) :: [])←SBlockIndented(nv); hkvUp:frames(map(…) :: [])←SBlockIndented(nvU)] ⊢ level-var",
   "accum_block_on_pendingBlock #1 param:compact_open_map.h_chainUp idx=— := paid:chain ns=— spend=relay(up←param:accum_block_on_pendingBlock.h_kslotUp) holds=[h_kslot:frames(map(…) :: [])←SBlockIndented(nv); h_kslotUp:frames(map(…) :: [])←SBlockIndented(nv); h_closeFV_old:frames(ks)@ExplValueLine(nv)←SCompactSeqTail(n); h_closeF_old:frames(ks)←SCompactSeqTail(n)] ⊢ level-var",
   "indicator_open_map #1 param:question_open_map.h_explUp_chain idx=— := relay:chain(param:indicator_open_map.h_explUp_chain) ns=— spend=— holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "indicator_open_map #1 param:question_open_map.h_explUp_chainD idx=— := relay:chain(param:indicator_open_map.h_explUp_chainD) ns=— spend=— holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
   "question_open_map #1 ctor:pendingMapValue.h_ivl idx=k := paid:route ns=— spend=h_route51←let:h_route51<param:question_open_map.h_res_land(h_res_land,h_sfx_land,h_nodoc_land,h_mk_land,h_pr_land) holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_route51F:tail(k)←SBlockMapEntry(k); h_upAll:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F)",
   "question_open_map #1 ctor:pendingMapValue.h_vslot idx=k := paid:route ns=— spend=h_route51←let:h_route51<param:question_open_map.h_res_land(h_res_land,h_sfx_land,h_nodoc_land,h_mk_land,h_pr_land) holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_route51F:tail(k)←SBlockMapEntry(k); h_upAll:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F)",
   "question_open_map #1 ctor:pendingMapValue.h_kslot idx=k := paid:tail ns=k :: nsU spend=alt[one(h_route51F←let:h_route51F)|up←param:question_open_map.h_explUp_chainD]⊣tail holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_route51F:tail(k)←SBlockMapEntry(k); h_upAll:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F)",
   "question_open_map #1 ctor:pendingMapValue.h_explUp idx=k := alt[paid:frames|paid:chain|stamp] ns=nv :: nsD|nsD|— spend=alt[resumeFrameRouteK(contV←param:question_open_map.h_explUp_chainD)|upD←param:question_open_map.h_explUp_chainD]|upD←param:question_open_map.h_explUp_chainD|—⊣tail holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_route51F:tail(k)←SBlockMapEntry(k); h_upAll:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ none",
  -- 2026-10-31 (item 412): seven writers of the entry-shaped `h_expl` — the consumer's relay, the four `:` openers'
  -- stamps, compact_open_map's chain relay off `hc`, and question_open_map's pay from `h_explUp_chainD`.
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_expl idx=— := relay:chain(door:pendingMapValue.h_expl) ns=— spend=— holds=[h_defer_split:frames(ks)←landing; h_expl51:tail(n_old)←SBlockMapEntry(n_old); h_kslot93:frames(map(…) :: [])←SBlockIndented(nv); h_closeF99:frames(map(…) :: ks)←SBlockNode(n_old + 1); h_frames99:frames(ks)←landing; h_closeFV108:frames(ks)@ExplValueLine(nv)←SBlockNode(n_old + 1); h_framesV108:frames(ks)@ExplValueLine(nv)←landing; h_seqF168:tail(n_old)←SBlockNode(n_old + 1); h_explUp✝:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
  "colon_open_map #1 ctor:pendingMapValue.h_expl idx=k := stamp ns=— spend=— holds=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_expl idx=nv := stamp ns=— spend=— holds=[hvp:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_expl idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_expl idx=k := stamp ns=— spend=— holds=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] ⊢ —",
  "compact_open_map #1 ctor:pendingMapValue.h_expl idx=n + 1 + m := relay:chain(let:h_expl105<param:compact_open_map.hc(hc)) ns=— spend=— holds=[h_chainUp:frames(map(…) :: [])←SBlockIndented(nv); h_expl105:tail(n + 1 + m)←SBlockMapEntry(n + 1 + m)] ⊢ —",
  "question_open_map #1 ctor:pendingMapValue.h_expl idx=k := paid:chain ns=— spend=up←param:question_open_map.h_explUp_chainD holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_route51F:tail(k)←SBlockMapEntry(k); h_upAll:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F)",
  "indicator_open_map #1 param:colon_open_map.h_explUp_chainD idx=— := relay:chain(param:indicator_open_map.h_explUp_chainD) ns=— spend=— holds=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: [])←SBlockIndented(nv); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: [])←SBlockIndented(nv)] ⊢ —"]
-- 2026-10-20 (item 307): re-read — the three γ roots' `h_vpack` are paid and `closeThenBlock`'s landed arm
-- resumes the closed park's stack; the rows citing them re-read.
-- 2026-10-21 (item 313): `pendingProps.h_kslot` and `h_kslotE` read `step` where they read `relay` (and one `via`): the
-- content-step relays through `PackAlt.step_content`.
-- 2026-10-23 (item 345): `pendingBlockContent.h_kslotUp` punt 3 → 0, chain 3 → 6 (the three singleton relays).
-- 2026-10-24 (item 350): `h_explUp`'s writers — punt 5 → 0, stamp 0 → 4 (the `:` producers'
-- `NotQuestionPark`), chain 1 → 0 and alt 0 → 2 (`compact_open_map`, `question_open_map` now split
-- on the alternative and spend `empty` on its `inr` arm), touched 1 → 6.
-- 2026-10-30 (item 405): per-position writer classes follow `expectedWriters` (head-form chain; declines of ruling "405 a").
-- 2026-10-30 (item 405, Rule 8 fix): the `h_kslot` positions' writers are classed `other`/`held` (the projection `markedCols sc` is no level variable) and the `h_nodeV`/`h_explUp_chain` relays read `levelVar` for the `markedCols sc` argument.
def expectedPerPos : List String := [
   "param:colon_open_map_implicit.h_kslotD writers=1 punt=0 stamp=0 empty=0 relay=0 step=1 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
   "param:colon_open_map_props.h_kslotD writers=1 punt=0 stamp=0 empty=0 relay=0 step=1 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
   "param:entryKeyPack_of_dispatch.h_nodeV writers=4 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=4",
   "param:entryPropsKeyPack_of_dispatch.h_nodeV writers=2 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=2",
  -- item 311: the two close writers read `step` (their `Or.imp` wrapper, `PackAlt.ofGateClose` on the right) where they
  -- read `via`, and the level variable they carried sits one step further in: `step` 0 → 2, `via` 5 → 3, `levelVar` 7 → 5.
  "ctor:pendingContent.h_vpack writers=12 punt=4 stamp=0 empty=0 relay=0 step=0 via=3 chain=5 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=8 none=0 touched=8",
  "ctor:pendingProps.h_kslot writers=6 punt=2 stamp=0 empty=0 relay=0 step=3 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=4",
  "ctor:pendingProps.h_kslotE writers=6 punt=3 stamp=0 empty=0 relay=0 step=2 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=1 touched=3",
  "ctor:pendingBlockContent.h_kslot writers=6 punt=0 stamp=0 empty=0 relay=0 step=0 via=0 chain=6 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=6 touched=6",
  "ctor:pendingBlockContent.h_kslotUp writers=6 punt=0 stamp=0 empty=0 relay=0 step=0 via=0 chain=6 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=6 none=0 touched=6",
  "ctor:pendingBlock.h_kslot writers=7 punt=1 stamp=0 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=6 alt=0 held=1 levelVar=0 none=5 touched=6",
  "ctor:pendingMapValue.h_ivl writers=6 punt=0 stamp=3 empty=0 relay=1 step=0 via=0 chain=1 route=1 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=1 touched=6",
  "ctor:pendingMapValue.h_vslot writers=6 punt=0 stamp=3 empty=0 relay=1 step=0 via=0 chain=1 route=1 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=1 touched=6",
  "param:accum_block_on_closeThenBlock.h_vpack writers=11 punt=3 stamp=0 empty=0 relay=1 step=0 via=1 chain=3 route=0 frames=3 tail=0 other=0 alt=0 held=1 levelVar=3 none=3 touched=8",
  "param:accum_block_on_closeThenBlock.h_vslot writers=11 punt=0 stamp=10 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=1 held=1 levelVar=0 none=0 touched=11",
  "param:accum_block_on_pendingBlock.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingBlockContent.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingContent.h_vpack writers=1 punt=0 stamp=0 empty=0 relay=0 step=1 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingBlock_indented.h_kslotUp_old writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingBlock_indented.h_kslot_old writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingMapValue_indented.h_ivl_mv writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingMapValue_indented.h_kslot writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_content_on_pendingMapValue_indented.h_vslot writers=1 punt=0 stamp=0 empty=0 relay=0 step=1 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:colon_open_map_explicit.hvp writers=3 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=3",
  "param:entryKeyPack_of_dispatch.h_compact writers=4 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=4",
  "param:entryKeyPack_of_dispatch.h_ivl writers=4 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=4",
  "param:entryPropsKeyPack_of_dispatch.h_compact writers=2 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=2",
  "param:entryPropsKeyPack_of_dispatch.h_ivl writers=2 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=1 none=0 touched=2",
  "param:flowKeyPack_of_close.h_key writers=2 punt=0 stamp=0 empty=0 relay=2 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=2",
  "param:flowVPack_of_close.h_vslot writers=0 punt=0 stamp=0 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=0",
  "param:indicator_open_map.h_explUp_chain writers=4 punt=2 stamp=0 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=2 held=0 levelVar=1 none=1 touched=2",
  "param:question_open_map.h_explUp_chain writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:slotChainMap.up writers=3 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=3",
  "ctor:pendingBlock.h_kslotUp writers=7 punt=2 stamp=0 empty=0 relay=0 step=0 via=0 chain=5 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=4 none=1 touched=5",
  "param:accum_block_on_pendingBlock.h_kslotUp writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:accum_block_on_pendingBlockContent.h_kslotUp writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
  "param:entryChainMap.up writers=5 punt=0 stamp=0 empty=0 relay=3 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=5",
  "param:indicator_open_map.h_explUp_chainD writers=4 punt=3 stamp=0 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=1 held=0 levelVar=1 none=0 touched=1",
  "param:question_open_map.h_explUp_chainD writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "ctor:pendingMapValue.h_kslot writers=6 punt=2 stamp=0 empty=0 relay=0 step=0 via=0 chain=3 route=0 frames=0 tail=1 other=0 alt=0 held=1 levelVar=3 none=0 touched=4",
   "ctor:pendingMapValue.h_explUp writers=6 punt=0 stamp=4 empty=0 relay=0 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=2 held=1 levelVar=0 none=1 touched=6",
   "param:flowKeyRoute_of_open.h_compact_pair writers=3 punt=1 stamp=0 empty=0 relay=0 step=0 via=0 chain=1 route=0 frames=0 tail=1 other=0 alt=0 held=0 levelVar=2 none=0 touched=2",
  -- 2026-10-31 (item 412): the entry-shaped `h_expl` as a ctor position (6 writers) and as the consumer's param position.
  "ctor:pendingMapValue.h_expl writers=6 punt=0 stamp=4 empty=0 relay=1 step=0 via=0 chain=1 route=0 frames=0 tail=0 other=0 alt=0 held=1 levelVar=0 none=0 touched=6",
  "param:accum_content_on_pendingMapValue_indented.h_expl writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1",
   -- Item 413: the opener's relay parameter, written twice (both callers, `paid:chain`).
   "param:compact_open_map.h_chainUp writers=2 punt=0 stamp=0 empty=0 relay=0 step=0 via=0 chain=2 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=2 none=0 touched=2",
   "param:explEntryChain_of_keyContent.up writers=4 punt=0 stamp=0 empty=0 relay=4 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=4",
   "param:colon_open_map.h_explUp_chainD writers=1 punt=0 stamp=0 empty=0 relay=1 step=0 via=0 chain=0 route=0 frames=0 tail=0 other=0 alt=0 held=0 levelVar=0 none=0 touched=1"]
-- 2026-10-18 (item 284): `nodes` 12296 → 12374 and nothing else.  The walk
-- counts nodes only while it follows a value-line pack, so this is item 284's
-- additions inside pack-carrying terms; the old `pendingFlow` arm restored alone
-- still reads 12374, so it is not that arm.  `rows` and every shape and verdict
-- hold.
-- 2026-10-18 (item 285): `apps` 50 → 51 and `nodes` 12374 → 12442, and nothing
-- else: the walk meets item 285's edits inside pack-carrying terms — `slot_ride`'s
-- frame, its three spends, the ring's two call-site payments — as one more
-- application and 68 more nodes; `rows` and every shape and verdict hold.
-- 2026-10-19 (item 287): the eleven `h_vslot` writers above, totalled — `punt`
-- 42 → 32 and `stamp` 3 → 13 for the ten, `chain` 51 → 50 and `alt` 2 → 3 for
-- the value park's split, `touched` +10 — and `nodes` 12442 → 12386 for the
-- walked terms; `rows`, `apps` and every shape hold.
-- 2026-10-19 (item 288): the field's three decliners, totalled — `punt` 32 → 29,
-- `stamp` 13 → 16, `touched` +3; `nodes` holds.
-- 2026-10-19 (item 293): `nodes` 12386 → 12460 alone, named per declaration by
-- the walk run on both trees (`scratchpad/l4yaml-row12-steps/378-walks-perdecl-293.log`):
-- the four park eliminators bind the four new fields (+4 each), and the rest
-- is the threading and payments in the accumulation lemmas (+1 to +14 each).
-- 2026-10-20 (item 299): `nodes` 12460 → 12470 alone — `pendingDocStart`'s new
-- `h_docline` field: one more binder at each park eliminator, one more
-- argument at each of its two producers, and `dispatch_refutes_sameLine`'s
-- new premise at the walked callers; named by cause, the per-declaration walk
-- not re-run.
-- 2026-10-20 (item 300): `nodes` 12470 → 12479 alone — `markerLine`, the pack
-- punt's new constructor: one more alternative at each walked `cases` on the
-- reason and the marker's base-slot conjunct; named by cause.
/-- **The pack line.**  `nodes` is the proof-term size of the walked
    declarations.  Lean v4.35.0 moves it alone: 12307 → 12296, with the other
    27 fields byte-identical. -/
-- 2026-10-20 (item 305): the pushes' and bottoms' terms (item 305): `nodes` 12479 → 12481.
-- 2026-10-20 (item 307): `punt` 29 → 26, `step` 1 → 2, `chain` 50 → 49, `frames` 1 → 3, `alt` 3 → 4, `none` 21 → 23, `touched` 122 → 125, `nodes` 12481 → 12487.
-- 2026-10-20 (item 307, second chain): `step` 2 → 1, `frames` 3 → 4, `none` 23 → 24.
-- 2026-10-20 (item 309): `nodes` 12487 → 12493 — the two generic premises read as stamp arms.
-- 2026-10-21 (item 311): `step` 1 → 3, `via` 12 → 10, `levelVar` 37 → 35, `flowVPack_of_close` leaves the helper list, `nodes`
-- 12493 → 12516 — the two closes wrap the helper's result in `.imp id PackAlt.ofGateClose` (the frame's named alternative into
-- the park's), so the writer is a `step` whose source is the helper, one `Or.imp` further from the level variable it carries.
-- 2026-10-21 (item 313): `relay` 36 → 32, `step` 3 → 8, `via` 10 → 9, `none` 24 → 23, `nodes` 12516 → 12523 — the content
-- lane's five writers on the props and mapping-value packs step through `PackAlt.step_content` where they relayed.
-- 2026-10-21 (item 315): `nodes` 12523 → 12525 — the key-pack lemmas' six arms step through the wrapper.
-- 2026-10-21 (item 320): `nodes` 12525 → 12544 — the marker parks' field, the eight payments, the relay and the
-- two split arms grow the terms; rows and positions stand.
-- 2026-10-21 (item 322): `nodes` 12544 → 12547 — the colon openers' step premise and its six spends grow the terms; rows stand.
-- 2026-10-23 (item 344): `punt` 26 → 25, `chain` 49 → 50, `levelVar` 35 → 36, `touched` 125 → 126 — `accum_block_pending` #2 relays `h_vpack`.
-- 2026-10-23 (item 345): punt 25 → 22, chain 50 → 53, none 26 → 29, touched 126 → 129 — the three `h_kslotUp` singleton relays.
-- 2026-10-23 (item 349): `nodes` 12556 → 12562 — `h_dead` threaded through the content step.
-- 2026-10-24 (item 350): punt 22 → 17, stamp 16 → 20, chain 53 → 52, alt 4 → 6, none 29 → 30, touched 129 → 134, nodes 12562 → 12566
-- — `h_explUp`'s alternative is the stamp `NotQuestionPark sc`; `inr` arms spend `empty`.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-26 (item 367, `[82]`): module-wide tallies only (the two directive sites apply `scannedDirective_toSL`; three `s-l-comments` lemmas join StreamAccum); the pack rows are unchanged: nodes 13691 → 13655.
-- 2026-10-29 (item 388): nodes 13675 → 13679 — the landed birth's `nv ≤ k` arm and the `.blockOut` wraps; no pack moved.
-- 2026-10-29 (item 389): nodes 13679 → 13681 — proof-term size only (the content door's new `h_top_old` premise); no pack row moved.
-- 2026-10-29 (item 394): the term grew with `FlowBaseRoutes.valueF`'s supply and relays; no pack row moved beyond the named binder.
-- 2026-10-29 (item 394, option B): the flow stack's s0 index and valueF's cover (walked-term total).
-- 2026-10-30 (item 405): see `expectedPacks`/`expectedWriters` (the `?`-park chain ladder PAID).
-- 2026-10-30 (item 405, Rule 8 fix): chain 45 → 39, other 0 → 6, held 7 → 8, levelVar 46 → 41, none 12 → 16 — the `h_kslot` writers pass the projection `markedCols sc` (classed `other`, not a level variable) instead of a destructured chain.
-- 2026-10-30 (item 407, flow carrier `pendingKeys` conjunct): nodes 13774 → 13787 — the `FlowStackK` rebuilds in the step lemmas.
def expectedLine : String :=
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); nodes 13689 → 13658 (walked-term total; rows unchanged).
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; five `match` blocks deleted): nodes 13658 → 13660 (walked-term total).
  -- 2026-10-26 (item 365): nodes 13660 → 13677 — the three `h_refused` decisions in the content lemmas; no pack row moved.
  -- 2026-10-26 (item 366): nodes 13677 → 13691 — the two `h_outer` pays at closeThenBlock; no pack row moved.
  -- 2026-10-26 (item 369): nodes=13655 → nodes=13657 — `h_closeF_old` (the `-` park's frames) is one more frame fact held under `accum_block_on_pendingBlock`; no pack row moved.
-- Item 371 (route=4 → 2, tail=0 → 2, held=6 → 7, none=26 → 25, spendTail=2 → 5, nodes=13657 → 13665): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
-- Item 372 (2026-10-27): `ImplicitKeyPack`'s route conjunct is an Or (`∨ SeqTopKey sc`); the pack walker reads the stream route on its left side.
-- Item 374: nodes=13663 → 13665 — the resume context's face disjunct and `resumectx_of_landing`'s `h_base`.
  -- 2026-10-28 (item 386): nodes 13665 → 13675 — the `-` opener's `h_lvl_old` beside the value-line packs it walks; no pack/row moved.
  "packs=12 framesOn=7 params=34 paramLemmas=21 apps=51 rows=166 ctorRows=80 paramRows=86 punt=23 stamp=24 empty=0 relay=36 step=9 via=4 chain=51 route=2 frames=3 tail=2 other=6 alt=6 held=8 levelVar=46 none=20 spendTail=9 lemmas=21 helpers=[frameChainUnion,frameChainUnionD] touched=143 nodes=14221"

/-! ## §4 The reading -/

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cd : PCand := {}
  let mut packLines : Array String := #[]
  let mut framesLines : Array String := #[]
  let mut packKeys : Array String := #[]
  for c in iv.ctors do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut stk : Stack := #[]
    let mut names : Array Name := #[]
    let mut packs : Array Pos := #[]
    while true do
      match ty with
      | .forallE n t b _ =>
        if i ≥ cv.numParams then
          names := names.push n
          if vcOutside t then
            let (vcLeft, otherTrue) := sideOf t
            packs := packs.push (i, n, vcLeft, otherTrue)
            let (st', cl, lvl) := peelToClosure stk t #[]
            let (prems, concl, tail) := premisesOf env st' cl #[] false false
            packLines := packLines.push s!"  {short c}.{n} arm={if vcLeft then "l" else "r"}{if otherTrue then "" else "/stamp"} lvl={String.intercalate "" lvl.toList} premises=[{String.intercalate "," prems.toList}] ⊢ {concl} tail={if tail then "yes" else "no"}"
            packKeys := packKeys.push s!"{short c}.{n}"
          else if framesOnVC t then
            framesLines := framesLines.push s!"  {short c}.{n} {(holdShape env stk t none).getD "?"}"
        stk := stk.push { name := n, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    cd := { cd with ctors := cd.ctors.insert c, fieldNames := cd.fieldNames.insert c names, packs := cd.packs.insert c packs, consts := cd.consts.insert c }
  cd := { cd with consts := cd.consts.insert ``PendingNode.casesOn }
  -- the pack parameters: every theorem binder of the shape
  let mut thms : Array Name := #[]
  let mut paramLines : Array String := #[]
  let mut paramKeys : Array String := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    unless ci matches .thmInfo _ do continue
    thms := thms.push n
    let mut ty := ci.type
    let mut i := 0
    let mut stk : Stack := #[]
    let mut ps : Array Pos := #[]
    while true do
      match ty with
      | .forallE pn t b _ =>
        if vcOutside t then
          let (vcLeft, otherTrue) := sideOf t
          ps := ps.push (i, pn, vcLeft, otherTrue)
          let (st', cl, lvl) := peelToClosure stk t #[]
          let (prems, concl, tail) := premisesOf env st' cl #[] false false
          paramLines := paramLines.push s!"  {short n}.{pn} arm={if vcLeft then "l" else "r"}{if otherTrue then "" else "/stamp"} lvl={String.intercalate "" lvl.toList} premises=[{String.intercalate "," prems.toList}] ⊢ {concl} tail={if tail then "yes" else "no"}"
          paramKeys := paramKeys.push s!"{short n}.{pn}"
        stk := stk.push { name := pn, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    if !ps.isEmpty then cd := { cd with lemParams := cd.lemParams.insert n ps, consts := cd.consts.insert n }
  paramLines := paramLines.qsort (· < ·)
  let w ← IO.mkRef ({} : W)
  for n in sorted thms do walkTheoremP w cd n
  let ws ← w.get
  -- the rows
  let mut writerLines : Array String := #[]
  let mut per : Std.HashMap String (Array String) := {}
  let mut lemmas : Std.HashSet Name := {}
  let mut helpers : Std.HashSet String := {}
  let mut cnt : Std.HashMap String Nat := {}
  let bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat := m.insert k (m.getD k 0 + 1)
  for r in ws.rows do
    unless r.argIdx < r.args.size do throwError "{r.target}: {r.args.size} args"
    -- the constructor's own level, where it has one
    let mut own := "—"
    if r.kind == "ctor" then
      let some (.ctorInfo cv) := env.find? r.callee | throwError "{r.callee}"
      let mut ty := cv.type
      let mut j := 0
      while own == "—" do
        match ty with
        | .forallE _ t b _ =>
          if j ≥ cv.numParams && t.consumeMData.isConstOf ``Nat && j < r.args.size then own := ppc r.st r.args[j]!
          ty := b; j := j + 1
        | _ => break
    let pr ← packCls env r.st r.args[r.argIdx]! r.vcLeft r.otherTrue
    let holds := holdsOf env r.st
    let clsHead := ((pr.cls.splitOn "(")[0]?).getD pr.cls
    let clsTag := if clsHead.startsWith "paid:" then clsHead
      else if clsHead.startsWith "via:" then "via"
      else if clsHead.startsWith "alt[" then "alt"
      else if clsHead.startsWith "relay:" then "relay"
      else if clsHead.startsWith "step" then "step"
      else if clsHead.startsWith "other" then "other" else clsHead
    lemmas := lemmas.insert r.lem
    if clsHead.startsWith "via:" then helpers := helpers.insert ((((clsHead.drop 4).toString).splitOn "[")[0]!)
    let verdict :=
      if clsHead.startsWith "paid:" || clsTag == "alt" || clsTag == "via" then
        let (atoms, var) := atomsOf pr.wits own
        let hs := hits holds atoms var
        if !hs.isEmpty then s!"held({String.intercalate "," hs.toList})"
        else if atoms.isEmpty then "level-var" else "none"
      else "—"
    let vTag := ((verdict.splitOn "(")[0]?).getD verdict
    cnt := bump cnt clsTag
    cnt := bump cnt s!"v:{vTag}"
    cnt := bump cnt s!"k:{r.kind}"
    if pr.spendTail then cnt := bump cnt "spendTail"
    per := per.insert r.target ((per.getD r.target #[]).push s!"{clsTag} {vTag}")
    writerLines := writerLines.push s!"  {short r.lem} #{r.occ} {r.kind}:{r.target} idx={own} := {pr.cls} ns={pr.ns} spend={pr.spend}{if pr.spendTail then "⊣tail" else ""} holds=[{String.intercalate "; " holds.toList}] ⊢ {verdict}"
  -- per position
  let mut perLines : Array String := #[]
  for (kind, ks) in [("ctor", packKeys), ("param", paramKeys.qsort (· < ·))] do
    for k in ks do
      let xs := per.getD k #[]
      let c (p : String) := (xs.filter fun s => (s.splitOn " ")[0]! == p).size
      let v (p : String) := (xs.filter fun s => (s.splitOn " ")[1]! == p).size
      let touched := xs.size - c "punt"
      perLines := perLines.push s!"  {kind}:{k} writers={xs.size} punt={c "punt"} stamp={c "stamp"} empty={c "empty"} relay={c "relay"} step={c "step"} via={c "via"} chain={c "paid:chain"} route={c "paid:route"} frames={c "paid:frames"} tail={c "paid:tail"} other={c "paid:other"} alt={c "alt"} held={v "held"} levelVar={v "level-var"} none={v "none"} touched={touched}"
  let g (k : String) := cnt.getD k 0
  let touched := ws.rows.size - g "punt"
  let helperL := (helpers.toArray.qsort (· < ·)).toList
  let paramLemmas := (cd.lemParams.toList.map (·.1)).length
  let line := s!"packs={packKeys.size} framesOn={framesLines.size} params={paramKeys.size} paramLemmas={paramLemmas} apps={ws.apps} rows={ws.rows.size} ctorRows={g "k:ctor"} paramRows={g "k:param"} punt={g "punt"} stamp={g "stamp"} empty={g "empty"} relay={g "relay"} step={g "step"} via={g "via"} chain={g "paid:chain"} route={g "paid:route"} frames={g "paid:frames"} tail={g "paid:tail"} other={g "paid:other"} alt={g "alt"} held={g "v:held"} levelVar={g "v:level-var"} none={g "v:none"} spendTail={g "spendTail"} lemmas={lemmas.size} helpers=[{String.intercalate "," helperL}] touched={touched} nodes={ws.nodes}"
  logInfo s!"ValueLinePacks {line}"
  logInfo s!"packs:\n{String.intercalate "\n" packLines.toList}"
  logInfo s!"framesOn:\n{String.intercalate "\n" framesLines.toList}"
  logInfo s!"params:\n{String.intercalate "\n" paramLines.toList}"
  logInfo s!"writers:\n{String.intercalate "\n" writerLines.toList}"
  logInfo s!"perPos:\n{String.intercalate "\n" perLines.toList}"
  -- 2026-10-31 (item 412): packs 11 → 12 — `pendingMapValue.h_expl` is entry-shaped now, its chain one frame up
  -- (`∀ nv ∈ markedCols sc, nv ≠ n → … ⊢ ResumeFrames`) declining into `PackAlt sc`: a pack by this census's reading.
  unless packKeys.size == 12 do throwError "the packs moved under this pass: packs={packKeys.size}"
  unless pinned do return
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedPacks" packLines expectedPacks
  check "expectedFramesOn" framesLines expectedFramesOn
  check "expectedParams" paramLines expectedParams
  check "expectedWriters" writerLines expectedWriters
  check "expectedPerPos" perLines expectedPerPos
  unless line == expectedLine do
    throwError "ValueLinePacks moved:\n  got      {line}\n  expected {expectedLine}"

end Tests.Guards.ValueLinePacks
