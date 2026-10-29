/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.OpenEntryRoute

/-!
# How many of the comment closes stand at a landing whose width is in hand (DOCS item 251)

Item 250 covered seven of the eighteen (shape, composition) pairs with two
re-routing lemmas and left eleven, and named the closes on comments among
them — `SSLComments ⇒ Stream` under comments alone, a suffix, and their
absorbed twins, and the value slot handed as a fact — as the failure mode's
first half: under an open entry a close on comments closes the entry EMPTY,
which is the honest reading exactly when what follows the comments stands at
the entry's width or left of it, `k ≤ n`, and a re-derivation otherwise.  This
module asks, at every point where such a close is spent, whether the two
numbers that comparison is made of are in hand.

**§1** re-derives the closes from item 249's trace rather than typing them:
every site whose spine is `SSLComments ⇒ Stream`, or the value-slot fact, with
its compositions, and whether the closure the producer hands goes through
`PendingNode.close_with_ssl`.  **§2** follows each site's callee parameter
through the callee's proof term to every point where it is APPLIED through
its `SSLComments` or `SBlockIndented` argument — a spend — or passed on to
another lemma — a hand-off, followed — and at each, with the real local
context in hand, classifies what stands beside the close: the landing's WIDTH
(an `SIndent k` off the landing, only the raw whites, or nothing), the park's
INDEX (a `Nat` tied to the park by a column fact, an indent floor, the
current indent or a slot closure over the park's own start — nameable, or
only inside an undestructured package), and whether a COMPARISON of the two
is in context.  **§3** censuses the empty-close constructors themselves —
`SBlockIndented.empty` and `SBlockNode.emptyNode` — in `close_with_ssl` and
the thirty-eight lemmas of the reach, with the same three readings beside
each.  Nothing here is counted because it typechecks: an empty close that
typechecks is the failure mode's first half, and what this module counts is
what stands beside it.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (sorted)
open Tests.Guards.RouteShapes
open Tests.Guards.StreamCompositions
open Tests.Guards.OpenEntryRoute
set_option autoImplicit false

namespace Tests.Guards.CloseLandingWidth

/-! ## §1 The closes, re-derived from item 249's trace -/

/-- A close on comments: the comments closure, or the value slot handed as a
    fact (item 249's `(fact)` composition at the block landing). -/
def isClosePair (spine comp : String) : Bool :=
  spine == "SSLComments ⇒ Stream" ||
  (spine.startsWith "[col(_)=_+1] SBlockIndented(_,blockOut)" && comp == "(fact)")

def hasDrop (s : String) : Bool := (s.splitOn "scannerDrop").length > 1

structure Site where
  site : String
  spines : Array String
  comps : Array String
  hops : Array String
  deriving Inhabited

/-- `producer→callee.param` split into the callee's constant and its parameter. -/
def calleeOf (site : String) : MetaM (Name × Name) := do
  let parts := site.splitOn "→"
  unless parts.length == 2 do throwError "{site}: not a callee-parameter site"
  let rest := parts[1]!
  let dot := rest.splitOn "."
  unless dot.length ≥ 2 do throwError "{site}: no parameter"
  let param := dot.getLast!
  let callee := String.intercalate "." (dot.dropLast)
  let env ← getEnv
  for pre in [`L4YAML.Proofs.StreamAccum, `L4YAML.Proofs.StreamAccum.PendingNode, `L4YAML.Proofs.NodeProduction] do
    let n := pre ++ callee.toName
    if env.contains n then return (n, param.toName)
  throwError "{site}: callee {callee} not found"

/-! ## §2 The spends -/

structure Row where
  origin : String
  lem : Name
  kind : String
  landing : String
  arg : String
  width : String
  index : String
  cmp : String
  deriving Inhabited

structure WState where
  rows : Array Row := #[]
  edges : Array String := #[]
  visited : Std.HashSet String := {}
  /-- per callee parameter: its own rows and the parameters it hands off to -/
  perParam : Std.HashMap String (Array Row × Array String) := {}

/-- The close binder of a closure type: its index among the ∀ binders, the
    START of what it closes (the comments' or the slot's start) and its head. -/
def closeBinder (t : Expr) : MetaM (Option (Nat × Expr × Name)) :=
  forallTelescope t fun xs _ => do
    for i in [0:xs.size] do
      let d := (← inferType xs[i]!).consumeMData
      if d.isAppOfArity ``SSLComments 2 then return some (i, (d.getArg! 0).consumeMData, ``SSLComments)
      if d.isAppOfArity ``SBlockIndented 4 then return some (i, (d.getArg! 2).consumeMData, ``SBlockIndented)
      if d.isAppOfArity ``SBlockNode 4 then return some (i, (d.getArg! 2).consumeMData, ``SBlockNode)
    return none

/-- A package (∃/∧/∨) with a closure inside it. -/
def hasCloseInside (t : Expr) : Bool :=
  (t.find? fun e => match e with
    | .forallE _ d _ _ =>
      let d := d.consumeMData
      d.isAppOfArity ``SSLComments 2 || d.isAppOfArity ``SBlockIndented 4 || d.isAppOfArity ``SBlockNode 4
    | _ => false).isSome

def stripSucc (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then (e.getArg! 4).consumeMData else e

def stripCast (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Nat.cast 3 then (e.getArg! 2).consumeMData
  else if e.isAppOfArity ``NatCast.natCast 3 then (e.getArg! 2).consumeMData
  else if e.isAppOfArity ``Int.ofNat 1 then (e.getArg! 0).consumeMData
  else e

def isColOf (e p : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``SurfPos.col 1 && (e.getArg! 0).consumeMData == p

def fvarsOf (e : Expr) : Array FVarId := (Lean.collectFVars {} e).fvarIds

def touches (e : Expr) (s : Array FVarId) : Bool := s.any e.containsFVar

def stripNot (e : Expr) : Expr :=
  let e := e.consumeMData
  if e.isAppOfArity ``Not 1 then (e.getArg! 0).consumeMData else e

/-- The ties of a `Nat` to the park in one hypothesis: (tag, index expression). -/
def tiesIn (start : Expr) (t : Expr) : MetaM (Array (String × Expr)) := do
  let out ← IO.mkRef (#[] : Array (String × Expr))
  let mentionsStart := match start with | .fvar id => t.containsFVar id | _ => (t.find? (· == start)).isSome
  -- `Expr.forEach'` keeps bound variables loose; the Meta variant would
  -- instantiate them with free variables that escape the traversal.
  t.forEach' fun e => do
    let e := e.consumeMData
    if e.isAppOfArity ``Eq 3 then
      let l := (e.getArg! 1).consumeMData
      let r := (e.getArg! 2).consumeMData
      if isColOf l start && r.isAppOfArity ``HAdd.hAdd 6 then out.modify (·.push ("col", r))
      if isColOf r start && l.isAppOfArity ``HAdd.hAdd 6 then out.modify (·.push ("col", l))
    if e.isAppOfArity ``L4YAML.Proofs.PreprocessIndentStable.IndentFloor 2 then out.modify (·.push ("floor", e.getArg! 1))
    if e.isAppOfArity ``LE.le 4 && (e.getArg! 2).consumeMData.isAppOfArity ``ScannerState.currentIndent 1 then
      out.modify (·.push ("cur", stripCast (e.getArg! 3)))
    if (e.isAppOfArity ``SBlockIndented 4 || e.isAppOfArity ``SBlockNode 4) && (e.getArg! 2).consumeMData == start then
      out.modify (·.push ("slot", e.getArg! 0))
    if mentionsStart && (e.isAppOfArity ``SCompactSeqTail 3 || e.isAppOfArity ``SCompactMapTail 3) then
      out.modify (·.push ("tail", e.getArg! 0))
    return true
  out.get

/-- A hypothesis and its conjuncts, one projection away. -/
partial def conjuncts (t : Expr) : Array Expr :=
  let t := t.consumeMData
  if t.isAppOfArity ``And 2 then conjuncts (t.getArg! 0) ++ conjuncts (t.getArg! 1) else #[t]

/-- What stands beside a close: the landing's width, the park's index, a
    comparison of the two.  `landing?` is `none` at a hand-off, where the
    landing is whatever `SSLComments start _` the context holds. -/
def beside (landing? : Option Expr) (start : Expr) (skip : Std.HashSet FVarId) (extraN : Array FVarId) :
    MetaM (String × String × String × String) := do
  let lctx ← getLCtx
  let mut landing := landing?
  if landing.isNone then
    for d in lctx do
      if d.isImplementationDetail then continue
      let t := d.type.consumeMData
      if t.isAppOfArity ``SSLComments 2 && (t.getArg! 0).consumeMData == start then
        landing := some (t.getArg! 1).consumeMData
        break
  -- the positions the context equates with the landing (one equation away)
  let mut alias : Array Expr := #[]
  if let some L := landing then
    for d in lctx do
      if d.isImplementationDetail then continue
      for t in conjuncts d.type do
        if t.isAppOfArity ``Eq 3 && (t.getArg! 0).consumeMData.isConstOf ``SurfPos then
          let a := (t.getArg! 1).consumeMData
          let b := (t.getArg! 2).consumeMData
          if a == L && !alias.contains b then alias := alias.push b
          if b == L && !alias.contains a then alias := alias.push a
  let atLanding (x : Expr) (L : Expr) : Option String :=
    let x := x.consumeMData
    if x == L then some "" else if alias.contains x then some "~" else none
  let mut widthTags : Array String := #[]
  let mut kSet : Array FVarId := #[]
  let mut direct : Array String := #[]
  let mut packed : Array String := #[]
  let mut nSet : Array FVarId := extraN
  for d in lctx do
    if d.isImplementationDetail || skip.contains d.fvarId then continue
    let t := d.type.consumeMData
    if let some L := landing then
      if t.isAppOfArity ``SIndent 3 then
        if let some m := atLanding (t.getArg! 1) L then
          widthTags := widthTags.push s!"ind{m}:{d.userName}"
          kSet := kSet ++ fvarsOf (t.getArg! 0)
      if t.isAppOfArity ``GStar 3 && (t.getArg! 0).consumeMData.isConstOf ``SSWhite then
        if let some m := atLanding (t.getArg! 1) L then
          widthTags := widthTags.push s!"ws{m}:{d.userName}"
      if t.isAppOfArity ``Eq 3 && (isColOf (t.getArg! 1) L || isColOf (t.getArg! 2) L) then
        widthTags := widthTags.push s!"col:{d.userName}"
    for (tag, ix) in ← tiesIn start t do
      let x := stripSucc ix
      match x with
      | .fvar id =>
        direct := direct.push s!"{tag}:{(← id.getDecl).userName}"
        if !nSet.contains id then nSet := nSet.push id
      | _ =>
        -- a compact tail's index counts only when it is a variable of the
        -- lemma: packaged, it may be a pack's width and not the park's
        if x.hasLooseBVars && tag != "tail" then packed := packed.push s!"{tag}:{d.userName}"
        else if x.isRawNatLit || x.isAppOfArity ``OfNat.ofNat 3 then direct := direct.push s!"{tag}:lit"
  let mut cmpTags : Array String := #[]
  -- the landing's width IS the park's index (a `subst` after `k = n`)
  let same := kSet.filter nSet.contains
  for id in same do cmpTags := cmpTags.push s!"≡{(← id.getDecl).userName}"
  if !kSet.isEmpty && !nSet.isEmpty then
    for d in lctx do
      if d.isImplementationDetail || skip.contains d.fvarId then continue
      let t := stripNot d.type
      let rel? : Option (Expr × Expr) :=
        if t.isAppOfArity ``Eq 3 then some (t.getArg! 1, t.getArg! 2)
        else if t.isAppOfArity ``Ne 3 then some (t.getArg! 1, t.getArg! 2)
        else if t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``GE.ge 4 || t.isAppOfArity ``GT.gt 4 then
          some (t.getArg! 2, t.getArg! 3)
        else none
      if let some (a, b) := rel? then
        if (touches a kSet && touches b nSet) || (touches a nSet && touches b kSet) then
          cmpTags := cmpTags.push s!"{d.userName}:{← ppExpr d.type}"
  let landingS ← match landing with
    | some L => pure (toString (← ppExpr L))
    | none => pure "—"
  let width := if widthTags.any (·.startsWith "ind") then s!"ind[{String.intercalate "," widthTags.toList}]"
    else if widthTags.any (·.startsWith "ws") then s!"ws[{String.intercalate "," widthTags.toList}]"
    else if widthTags.isEmpty then "none" else s!"col[{String.intercalate "," widthTags.toList}]"
  let index := if !direct.isEmpty then s!"direct[{String.intercalate "," (distinctS direct).toList}]"
    else if !packed.isEmpty then s!"packed[{String.intercalate "," (distinctS packed).toList}]" else "none"
  let cmp := if cmpTags.isEmpty then "no" else s!"yes[{String.intercalate "," cmpTags.toList}]"
  return (landingS, width, index, cmp)

abbrev Tracked := Std.HashMap FVarId (Nat × Expr × Name)

/-- A tracked closure inside `e` that is not spent there: applied to fewer
    arguments than its close binder needs, under lambdas, casts, matches and
    logic plumbing — but not inside an application `stop` names (a library
    lemma or a constructor), which is a hand-off or carry point of its own. -/
partial def partialUse (stop : Name → Bool) (tc : Tracked) (e : Expr) : Option FVarId :=
  let e := e.consumeMData
  match e with
  | .fvar id => if tc.contains id then some id else none
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      match tc[id]? with
      | some (ci, _, _) => if args.size ≤ ci then some id else args.findSome? (partialUse stop tc)
      | none => args.findSome? (partialUse stop tc)
    | .const n _ => if stop n then none else args.findSome? (partialUse stop tc)
    | _ => (partialUse stop tc f).orElse fun _ => args.findSome? (partialUse stop tc)
  | .lam _ t b _ => (partialUse stop tc t).orElse fun _ => partialUse stop tc b
  | .forallE _ t b _ => (partialUse stop tc t).orElse fun _ => partialUse stop tc b
  | .letE _ t v b _ => (partialUse stop tc t).orElse fun _ => (partialUse stop tc v).orElse fun _ => partialUse stop tc b
  | .mdata _ b => partialUse stop tc b
  | .proj _ _ b => partialUse stop tc b
  | _ => none

/-- Hand-off and carry points: the library's lemmas and every constructor. -/
def stopAt (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some (.thmInfo _) => n.getRoot == `L4YAML
  | some (.ctorInfo _) => true
  | _ => false

/-- The class of a spend by what the closure is handed: the comments premise
    (the close is then `close_with_ssl`'s, empty for an open park), an empty
    node, or a node. -/
def classOf (arg : String) : String :=
  if arg.startsWith "SBlockIndented.empty" || arg.startsWith "SBlockNode.emptyNode" then "empty"
  else if arg == "prem:SSLComments" || arg.startsWith "SSLComments." || arg.startsWith "lemma:left(prem:And" || arg.startsWith "lemma:right(prem:And" then "comments"
  else "node"

def landingOf (ty : Expr) : Option Expr :=
  let ty := ty.consumeMData
  if ty.isAppOfArity ``SSLComments 2 then some (ty.getArg! 1).consumeMData
  else if ty.isAppOfArity ``SBlockIndented 4 || ty.isAppOfArity ``SBlockNode 4 then some (ty.getArg! 3).consumeMData
  else none

mutual

/-- Track a fresh binder: a closure, or a package with a closure inside. -/
partial def trackBinder (x : Expr) (tc : Tracked) (tp : Std.HashSet FVarId) : MetaM (Tracked × Std.HashSet FVarId) := do
  let t ← inferType x
  if let some info ← closeBinder t then return (tc.insert x.fvarId! info, tp)
  if hasCloseInside t then return (tc, tp.insert x.fvarId!)
  return (tc, tp)

partial def walk (st : IO.Ref WState) (origin : String) (lem : Name) (tc : Tracked) (tp : Std.HashSet FVarId)
    (e : Expr) (cand : Bool) (depth : Nat) : MetaM Unit := do
  let e := e.consumeMData
  let anyTracked (x : Expr) : Bool := tc.fold (fun b id _ => b || x.containsFVar id) false || tp.fold (fun b id => b || x.containsFVar id) false
  unless cand || anyTracked e do return
  match e with
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      let (tc, tp) ← if cand then trackBinder x tc tp else pure (tc, tp)
      walk st origin lem tc tp (b.instantiate1 x) cand depth
  | .forallE n t b bi =>
    withLocalDecl n bi t fun x => walk st origin lem tc tp (b.instantiate1 x) false depth
  | .letE n t v b _ =>
    walk st origin lem tc tp v false depth
    withLetDecl n t v fun x => do
      let (tc, tp) ← if anyTracked v then trackBinder x tc tp else pure (tc, tp)
      walk st origin lem tc tp (b.instantiate1 x) false depth
  | .proj _ _ b => walk st origin lem tc tp b false depth
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      if let some (ci, start, _) := tc[id]? then
        if args.size > ci then
          let closeArg := args[ci]!
          let landing := landingOf (← inferType closeArg)
          let skip : Std.HashSet FVarId := tc.fold (fun s k _ => s.insert k) {}
          let (landingS, width, index, cmp) ← beside landing start skip #[]
          let arg ← nodeShape closeArg 6
          st.modify fun s => { s with rows := s.rows.push { origin, lem, kind := "spend", landing := landingS, arg, width, index, cmp } }
      for a in args do walk st origin lem tc tp a false depth
    | .lam .. => walk st origin lem tc tp e.headBeta cand depth
    | .const n us =>
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← walk st origin lem tc tp (mkAppN args[k]! (args.extract arity args.size)).headBeta cand depth
      if n == ``letFun && args.size ≥ 4 then
        let v := args[2]!
        walk st origin lem tc tp v false depth
        match args[3]! with
        | .lam bn bt bb bi =>
          withLetDecl bn bt v fun x => do
            let (tc, tp) ← if anyTracked v then trackBinder x tc tp else pure (tc, tp)
            let _ := bi
            walk st origin lem tc tp (bb.instantiate1 x) false depth
        | g => walk st origin lem tc tp g false depth
        for a in args.extract 4 args.size do walk st origin lem tc tp a false depth
        return
      -- hand-offs: a tracked closure passed to a lemma short of its close
      -- argument, anywhere in the argument (a match that returns it, a
      -- package that holds it); carries: the same into a constructor
      let env ← getEnv
      match env.find? n with
      | some (.thmInfo _) =>
        for i in [0:args.size] do
          if !(n.getRoot == `L4YAML) then break
          if let some id := partialUse (stopAt env) tc args[i]! then
            let (_, start, _) := tc[id]?.get!
            let names := (← getConstInfo n).type.getForallBinderNames.toArray
            let pname := if i < names.size then names[i]! else Name.mkSimple s!"#{i}"
            let target := s!"{short n}.{pname}"
            let skip : Std.HashSet FVarId := tc.fold (fun s k _ => s.insert k) {}
            let (landingS, width, index, cmp) ← beside none start skip #[]
            st.modify fun s => { s with rows := s.rows.push { origin, lem, kind := s!"handoff→{target}", landing := landingS, arg := "—", width, index, cmp },
                                          edges := s.edges.push s!"{short lem} → {target}" }
            if depth < 6 then followParam st origin n pname (depth + 1)
      | some (.ctorInfo _) =>
        for i in [0:args.size] do
          if let some id := partialUse (stopAt env) tc args[i]! then
            let (_, start, _) := tc[id]?.get!
            let skip : Std.HashSet FVarId := tc.fold (fun s k _ => s.insert k) {}
            let (landingS, width, index, cmp) ← beside none start skip #[]
            st.modify fun s => { s with rows := s.rows.push { origin, lem, kind := s!"carry→{short2 n}", landing := landingS, arg := "—", width, index, cmp } }
      | _ => pure ()
      let destr := args.any fun a => match a.consumeMData with | .fvar id => tp.contains id | _ => false
      for a in args do walk st origin lem tc tp a destr depth
      let _ := us
    | _ =>
      walk st origin lem tc tp f false depth
      for a in args do walk st origin lem tc tp a false depth
  | _ => return

/-- Follow one lemma's parameter to its spends and hand-offs; memoized per parameter. -/
partial def followParam (st : IO.Ref WState) (origin : String) (c : Name) (pname : Name) (depth : Nat) : MetaM Unit := do
  let key := s!"{short c}.{pname}"
  if (← st.get).visited.contains key then return
  st.modify fun s => { s with visited := s.visited.insert key }
  let some ci := (← getEnv).find? c | throwError "{c}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  let before := (← st.get).rows.size
  lambdaTelescope v fun xs body => do
    let mut x? : Option Expr := none
    for x in xs do
      if (← x.fvarId!.getDecl).userName == pname then x? := some x
    let some x := x? | throwError "{c}: no parameter {pname} among its lambdas"
    let (tc, tp) ← trackBinder x {} {}
    if tc.isEmpty && tp.isEmpty then
      st.modify fun s => { s with rows := s.rows.push { origin, lem := c, kind := "untyped", landing := "—", arg := "—", width := "none", index := "none", cmp := "no" } }
    else walk st origin c tc tp body false depth
  let s ← st.get
  let mine := (s.rows.extract before s.rows.size).filter (·.lem == c)
  let targets := distinctS ((mine.filter (·.kind.startsWith "handoff→")).map fun r => (r.kind.splitOn "→")[1]!)
  st.modify fun s => { s with perParam := s.perParam.insert key (mine, targets) }

end

/-! ## §3 The empty closes -/

structure Empty where
  lem : Name
  ctor : String
  landing : String
  ix : String
  width : String
  cmp : String
  deriving Inhabited

partial def walkEmpties (st : IO.Ref (Array Empty)) (lem : Name) (e : Expr) : MetaM Unit := do
  let e := e.consumeMData
  match e with
  | .lam n t b bi => withLocalDecl n bi t fun x => walkEmpties st lem (b.instantiate1 x)
  | .forallE n t b bi => withLocalDecl n bi t fun x => walkEmpties st lem (b.instantiate1 x)
  | .letE n t v b _ =>
    walkEmpties st lem v
    withLetDecl n t v fun x => walkEmpties st lem (b.instantiate1 x)
  | .proj _ _ b => walkEmpties st lem b
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n _ := f then
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← walkEmpties st lem (mkAppN args[k]! (args.extract arity args.size)).headBeta
      if (n == ``SBlockIndented.empty || n == ``SBlockNode.emptyNode) && args.size ≥ 5 then
        let landing := (args[3]!).consumeMData
        let start := (args[2]!).consumeMData
        let ix := args[0]!
        let nS := fvarsOf (stripSucc ix)
        let (landingS, width, _, cmp) ← beside (some landing) start {} nS
        st.modify (·.push { lem, ctor := short2 n, landing := landingS, ix := toString (← ppExpr ix), width, cmp })
      if n == ``letFun && args.size ≥ 4 then
        walkEmpties st lem args[2]!
        match args[3]! with
        | .lam bn bt bb _ => withLetDecl bn bt args[2]! fun x => walkEmpties st lem (bb.instantiate1 x)
        | g => walkEmpties st lem g
        for a in args.extract 4 args.size do walkEmpties st lem a
        return
    if f.isLambda then return ← walkEmpties st lem e.headBeta
    walkEmpties st lem f
    for a in args do walkEmpties st lem a
  | _ => return

def emptiesOf (c : Name) : MetaM (Array Empty) := do
  let some ci := (← getEnv).find? c | return #[]
  let some v := ci.value? (allowOpaque := true) | return #[]
  let st ← IO.mkRef (#[] : Array Empty)
  lambdaTelescope v fun _ body => walkEmpties st c body
  st.get

/-! ## §4 The pins -/

-- 2026-10-24 (B3 [66] col-0 threading): follows StreamCompositions — the content/block parks close from `sp_gram` (run + gate).
def expectedCloses : List String :=
  ["accum_block_pending→accum_block_on_closeThenBlock.h_close_pending [SSLComments ⇒ Stream] comps=SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil],SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil],SLYamlStream.scannerDrop[S,prem:SSLComments] viaClose=true param=accum_block_on_closeThenBlock.h_close_pending",
   "accum_block_pending→accum_block_on_pendingBlock.h_close_pending [SSLComments ⇒ Stream] comps=SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil],SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil],SLYamlStream.scannerDrop[S,prem:SSLComments] viaClose=true param=accum_block_on_pendingBlock.h_close_pending",
   "accum_content_on_noPending→keyctx_of_preprocess.h_close [SSLComments ⇒ Stream] comps=SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil] viaClose=false param=keyctx_of_preprocess.h_close",
   "accum_flow_open_depth0→flowKeyRoute_of_root.h_close [SSLComments ⇒ Stream] comps=absorb:absorb_stacksB ▹ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil],absorb:absorb_stacksB ▹ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil],absorb:absorb_stacksB ▹ SLYamlStream.scannerDrop[S,prem:SSLComments] viaClose=true param=flowKeyRoute_of_root.h_close",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_block_pending→accum_block_on_closeThenBlock.h_vslot [[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream | [col(_)=_+1] SBlockIndented(_,blockOut) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream | [col(_)=_+1] SBlockIndented(_,blockOut) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream] comps=(fact) viaClose=false param=accum_block_on_closeThenBlock.h_vslot"]
-- Item 305: `closeThenBlock`'s `h_vslot` is spent at two more nodes — the first entry's
-- value-line stack at the landed-`-` arm (`h_slotV`) and at the compact arm, both the slot's
-- inner pack under `KeyFrames.bottom`: `spends` 8 → 10.
-- 2026-10-24 (B3 [66] col-0 threading): follows StreamCompositions — the content/block parks close from `sp_gram` (run + gate).
def expectedSites : List String :=
  ["accum_block_pending→accum_block_on_closeThenBlock.h_close_pending → accum_block_on_closeThenBlock.h_close_pending: spends=1 (node 0) handoffs=0 carries=0 WIDTH reach=1 reachJudged=1 reachBoth=false",
   "accum_block_pending→accum_block_on_closeThenBlock.h_vslot → accum_block_on_closeThenBlock.h_vslot: spends=8 (node 8) handoffs=3 carries=1 NEITHER reach=2 reachJudged=4 reachBoth=false",
   "accum_block_pending→accum_block_on_pendingBlock.h_close_pending → accum_block_on_pendingBlock.h_close_pending: spends=4 (node 0) handoffs=1 carries=0 BOTH reach=2 reachJudged=6 reachBoth=false",
   "accum_content_on_noPending→keyctx_of_preprocess.h_close → keyctx_of_preprocess.h_close: spends=2 (node 1) handoffs=0 carries=0 WIDTH reach=1 reachJudged=1 reachBoth=false",
   "accum_flow_open_depth0→flowKeyRoute_of_root.h_close → flowKeyRoute_of_root.h_close: spends=2 (node 2) handoffs=0 carries=0 NEITHER reach=1 reachJudged=0 reachBoth=false"]
-- 2026-10-24 (B3 [66] col-0 threading): follows StreamCompositions — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
def expectedSpends : List String :=
  -- Item 305: two spends more at `closeThenBlock` — the slot's inner pack through `slotLandedSeq`
  -- for the first entry's stack (`h_slotV`, the landed arm) and through the compact fill for the
  -- compact entry's (`h_closeFV` at the compact arm), both under `KeyFrames.bottom`.
  [
   -- Item 364: the declined K1-seq cover slot at the consed `seq n :: ks` site reads as a carry
   "accum_block_on_closeThenBlock carry→And.intro @— arg=— width=none index=direct[slot:k,tail:k] cmp=no","accum_block_on_closeThenBlock spend:node @sp_e arg=SBlockIndented.compactSeq(prem:SIndent,SCompactSeq.mk(prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)) width=ind[ind:h_iv] index=direct[cur:nv] cmp=yes[≡nv]",
   "accum_block_on_closeThenBlock spend:node @sp_e arg=SBlockIndented.compactSeq(prem:SIndent,SCompactSeq.mk(prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)) width=none index=direct[cur:nv] cmp=no",
   "accum_block_on_pendingBlock handoff→accum_block_on_closeThenBlock.h_close_pending @sp_mid arg=— width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[slot:n,tail:n,col:n,cur:n] cmp=yes[hkn:¬k = n,_hge:n ≥ k]",
   "accum_block_on_pendingBlock spend:comments @sp_mid arg=prem:SSLComments width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[slot:n,tail:n,col:n,cur:n] cmp=no",
   "accum_block_on_pendingBlock spend:comments @sp_mid arg=prem:SSLComments width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[slot:n,tail:n,col:n,cur:n] cmp=no",
   "accum_block_on_pendingBlock spend:comments @sp_mid arg=prem:SSLComments width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[slot:n,tail:n,col:n,cur:n] cmp=no",
   "keyctx_of_preprocess spend:comments @sp_mid arg=lemma:left(prem:And) width=ind[ws:h_ws,ind:h_ind,ind:h_ind'] index=none cmp=no",
   "slotChainMap spend:node @sp_v arg=SBlockIndented.node(SBlockNode.blockMap(GOpt.none,prem:SSLComments,SBlockMapEntries.single(prem:SIndent,prem:SBlockMapEntry))) width=none index=direct[cur:nv] cmp=no",
   "accum_block_on_closeThenBlock spend:comments @sp_mid arg=prem:SSLComments width=ws[ws:hws,col:hcol_mid] index=packed[cur:h_vslot,slot:h_vslot,slot:h_valF,slot:h_valFV] cmp=no",
   "accum_block_on_closeThenBlock spend:node @sp_e arg=SBlockIndented.node(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail))) width=none index=direct[cur:nv,slot:nv] cmp=no",
   "accum_block_on_closeThenBlock spend:node @sp_e arg=SBlockIndented.node(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail))) width=none index=direct[cur:nv,slot:nv] cmp=no",
   "accum_block_on_closeThenBlock spend:node @sp_e arg=SBlockIndented.node(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail))) width=none index=direct[cur:nv,slot:nv] cmp=no",
   "accum_block_on_closeThenBlock handoff→slotChainMap.up @sp_mid arg=— width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[cur:nv,slot:nv] cmp=yes[hnk:nv + 1 ≤ k]",
   "accum_block_on_closeThenBlock handoff→slotChainMap.up @sp_mid arg=— width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[cur:nv,slot:nv] cmp=yes[hnk:nv + 1 ≤ k]",
   "accum_block_on_closeThenBlock handoff→slotChainMap.up @sp_mid arg=— width=ind[ws:hws,col:hcol_mid,ind:h_ind] index=direct[cur:nv,slot:nv] cmp=yes[hnk:nv + 1 ≤ k]",
   "accum_block_on_closeThenBlock spend:node @sp_final arg=SBlockIndented.compactSeq(prem:SIndent,SCompactSeq.mk(prem:GLit,prem:GNot,prem:SBlockIndented,SCompactSeqTail.nil)) width=none index=direct[cur:nv,slot:nv] cmp=no",
   "accum_block_on_closeThenBlock spend:node @sp_end arg=SBlockIndented.compactSeq(prem:SIndent,SCompactSeq.mk(prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)) width=none index=direct[cur:nv,slot:nv] cmp=no",
   "accum_block_on_closeThenBlock spend:node @sp_e arg=SBlockIndented.compactSeq(prem:SIndent,SCompactSeq.mk(prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)) width=none index=direct[cur:nv,slot:nv] cmp=no",
   "accum_block_on_closeThenBlock spend:node @sp arg=prem:SBlockIndented width=none index=direct[cur:nv,slot:nv] cmp=no",
   "keyctx_of_preprocess spend:node @sp arg=lemma:white_prepend_SSLComments(prem:GStar,SSLComments.startOfLine(GStar.nil)) width=ind[ws~:h_ws,ind~:h_ind,ind~:h_ind',col:hc0] index=none cmp=no",
   "flowKeyRoute_of_root spend:node @sp_mid arg=lemma:SSLCommentsFrom_at_park(prem:ScannerSurfCorr,prem:GStar,prem:∀→Not,lemma:left(prem:And),lemma:left(lemma:right(lemma:right(prem:And)))) width=ind[ws:h_ws,ind:h_ind,ind:h_ind'] index=none cmp=no",
   "flowKeyRoute_of_root spend:node @sp_mid arg=lemma:SSLCommentsFrom_at_park(prem:ScannerSurfCorr,prem:GStar,prem:∀→Not,lemma:left(prem:And),lemma:left(lemma:right(lemma:right(prem:And)))) width=ind[ws:h_ws,ind:h_ind,ind:h_ind'] index=none cmp=no"]
-- 2026-10-24 (B3 [66] col-0 threading): follows StreamCompositions — the content/block parks close from `sp_gram` (run + gate).
def expectedEdges : List String :=
  ["accum_block_on_closeThenBlock → slotChainMap.up",
   "accum_block_on_pendingBlock → accum_block_on_closeThenBlock.h_close_pending"]
-- 2026-10-20 (item 306): 18 → 21 — the three key-pack calls in
-- `accum_content_on_pendingBlock_indented` pay `h_dframesV` with the entry's level
-- pushed over the EMPTY entry (`SBlockIndented.empty n … sp_m`), the value twin of
-- the stream-lane `h_dframes` relay beside it: three more of the same row.
-- 2026-10-20 (item 307): 21 → 23 — `accum_block_on_pendingBlock`'s dedent `-` builds `h_vpack`
-- and `h_mapFV` over the EMPTY awaited entry (`SBlockIndented.empty n … sp_m`), the twins of
-- item 167's `h_seqF_old` relay between them.
-- 2026-10-23 (item 345): 23 → 24 — `accum_content_on_pendingBlock_indented` relays `h_closeFV_old` onto the twin
-- over the EMPTY entry (`SBlockIndented.empty n … sp_m`), beside its `h_closeF_old` relay.
-- 2026-10-29 (item 389): 27 → 28 — the paid `k = n` mapping-top arm at `accum_block_on_pendingBlock` builds the empty `SBlockIndented` node at `sp_mid` for the sibling's route.
def expectedEmpties : List String :=
  ["close_with_ssl SBlockIndented.empty n=n @sp_mid width=none cmp=no",
   "close_with_ssl SBlockNode.emptyNode n=n + 1 @sp_mid width=none cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_mid width=ind[ws:hws,col:hcol_mid,ind:h_ind] cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_mid width=ind[ws:hws,col:hcol_mid,ind:h_ind] cmp=no",
   -- 2026-10-26 (item 369): the same empty close read once more — the `:`/`?` landing pays `h_res_land`
   -- off `pendingBlock.h_closeF` with the awaited entry closed EMPTY (24 → 25).
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_mid width=ind[ws:hws,col:hcol_mid,ind:h_ind] cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_m width=ind[ind:h_iv] cmp=no",
   "accum_block_on_pendingBlock SBlockIndented.empty n=n @sp_mid width=ind[ws:hws,col:hcol_mid,ind:h_ind] cmp=yes[h_nk:n ≤ k,hnk:¬n < k]",
   "accum_block_pending SBlockNode.emptyNode n=nmv + 1 @sp_m width=ind[ind:h_ind] cmp=no",
   "accum_block_pending SBlockIndented.empty n=nmv @sp_m width=ind[ind:h_ind] cmp=yes[≡nmv]",
   "accum_block_pending SBlockNode.emptyNode n=nmv + 1 @sp_m width=ind[ind:h_ind] cmp=no",
   "accum_block_pending SBlockIndented.empty n=nmv @sp_m width=ind[ind:h_ind] cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_mid width=ind[col:h_col0m,ind:h_ind] cmp=yes[_hj:j < n + 1]",
   "accum_content_on_pendingBlock_indented SBlockIndented.empty n=n @sp_m width=none cmp=no",
   "accum_content_on_pendingMapValue_indented SBlockNode.emptyNode n=n + 1 @sp_mid width=ind[col:h_col0m,ind:h_ind] cmp=yes[_hj:j < n + 1]",
   "question_open_map SBlockIndented.empty n=k @sp_m width=none cmp=no",
   "question_open_map SBlockIndented.empty n=k @sp_m width=ind[ind:h_iv] cmp=yes[≡k]",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "colon_open_map_explicit SBlockIndented.empty n=nv @sp_m width=none cmp=no",
   "compact_open_map SBlockIndented.empty n=n + 1 + m @sp_v width=none cmp=no"]
/-- Item 257 spends the compact fill's slot closure once more: the fill's
    `pendingBlock.h_closeF` is paid with a literal cover whose bottom is
    `hvs` applied to the compact sequence — a NODE spend of
    `accum_block_on_closeThenBlock.h_vslot`, so that site reads `spends=8
    (node 8)` and the line `spends=22 spendsN=9`; the spends on comments,
    the hand-offs and every width and index column stand. -/
-- Item 305: `closeThenBlock`'s `h_vslot` is spent at two more nodes (the slot bottoms under
-- `KeyFrames.bottom` at the landed and compact arms): `spends` 22 → 24, `spendsN` 9 → 11.
-- 2026-10-20 (item 306): `empties` 18 → 21 — the content lemma's three key-pack calls pay
-- `h_dframesV` with the entry's level pushed over the EMPTY entry, the value twin of the
-- stream-lane `h_dframes` relay beside each.
-- 2026-10-20 (item 307): `empties` 21 → 23 (the two above).
-- 2026-10-20 (item 307): corrected from the census — the dedent route's two new empties: `emptyInd` 10 → 11.
-- 2026-10-23 (item 345): empties 23 → 24 — the EMPTY-entry twin relay in `accum_content_on_pendingBlock_indented`.
-- 2026-10-24 (B3 [66] col-0 threading): follows StreamCompositions — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-26 (item 369): empties=24 → 25, emptyInd=11 → 12 — the `:`/`?` landing in
-- `accum_block_on_pendingBlock` closes the awaited entry EMPTY once more to read `h_res_land` off `pendingBlock.h_closeF`.
-- 2026-10-29 (item 389): empties 27 → 28, emptyInd 12 → 13, emptyCmp 4 → 5 — the paid k = n mapping-top arm's empty node at sp_mid (width from h_ind, compared n ≤ k).
def expectedLine : String :=
-- Item 371 (empties=25 → 27, emptyLemmas=6 → 8): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
  "closeSites=5 closePairs=6 closePairsD=8 viaClose=3 params=5 spends=18 spendsC=6 spendsE=0 spendsN=12 handoffs=4 carries=1 untyped=0 edges=2 paramsWalked=6 widthInd=5 widthWs=1 widthNone=0 idxDirect=4 idxPacked=1 idxNone=1 cmp=0 cmpSame=0 both=4 bothCmp=0 handInd=4 handDirect=4 handCmp=4 sitesBoth=1 sitesWidth=2 sitesNeither=2 sitesBothAll=0 empties=28 emptyLemmas=8 emptyInd=13 emptyCmp=5 emptySame=2 emptyClose=2 sites=20 pairs=20 pairs21=19 pairs18=17 nonANoDrop=8 reach=38"

/-! ## §5 The reading -/

set_option maxHeartbeats 8000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- §1 the closes, from item 249's trace
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
  let noDrop := shapeComps.filter fun sc => !hasDrop sc
  let aPlain := genuine.filter fun f => streamOnly f.seg == #[compA]
  let stackedA := genuine.filter fun f => let so := streamOnly f.seg; so.size ≥ 2 && so.back? == some compA
  let mut aPairs : Array String := #[]
  for f in aPlain do
    for sp in f.spine.splitOn " | " do
      let pr := s!"{sp} ⟶ {compOf f.seg}"
      if !aPairs.contains pr then aPairs := aPairs.push pr
  let mut stackedPairs : Array String := #[]
  for f in stackedA do
    for sp in f.spine.splitOn " | " do
      let pr := s!"{sp} ⟶ {compOf f.seg}"
      if !stackedPairs.contains pr then stackedPairs := stackedPairs.push pr
  let nonA := shapeComps.filter fun sc => !aPairs.contains sc && !stackedPairs.contains sc
  let nonANoDrop := nonA.filter fun sc => !hasDrop sc
  -- the close pairs and sites
  let mut closePairsD : Array String := #[]
  let mut closeSites : Array Site := #[]
  for f in genuine do
    let comp := compOf f.seg
    let sps := (f.spine.splitOn " | ").toArray.filter fun sp => isClosePair sp comp
    if sps.isEmpty then continue
    for sp in sps do
      let pr := s!"{sp} ⟶ {comp}"
      if !closePairsD.contains pr then closePairsD := closePairsD.push pr
    let hops := hopsOf f.seg
    match closeSites.findIdx? (·.site == f.site) with
    | some i =>
      let c := closeSites[i]!
      closeSites := closeSites.set! i { c with spines := distinctS (c.spines ++ sps), comps := distinctS (c.comps.push comp), hops := distinctS (c.hops ++ hops) }
    | none => closeSites := closeSites.push { site := f.site, spines := sps, comps := #[comp], hops := hops }
  let closePairs := closePairsD.filter fun pr => !hasDrop pr
  closeSites := closeSites.qsort (·.site < ·.site)
  let mut closeLines : Array String := #[]
  let mut viaClose := 0
  let mut paramOf : Array (String × String) := #[]
  for c in closeSites do
    let via := c.hops.any (· == "close_with_ssl")
    if via then viaClose := viaClose + 1
    let (callee, pname) ← calleeOf c.site
    let key := s!"{short callee}.{pname}"
    paramOf := paramOf.push (c.site, key)
    closeLines := closeLines.push s!"  {c.site} [{String.intercalate " | " c.spines.toList}] comps={String.intercalate "," c.comps.toList} viaClose={via} param={key}"
  let params := distinctS (paramOf.map (·.2))
  -- §2 the spends
  let st ← IO.mkRef ({} : WState)
  for key in params do
    let some (site, _) := paramOf.find? (·.2 == key) | continue
    let (callee, pname) ← calleeOf site
    followParam st key callee pname 0
  let w ← st.get
  -- rows, deduplicated by parameter (each parameter walked once)
  let mut spendLines : Array String := #[]
  let mut allRows : Array Row := #[]
  for key in params do
    if let some (rows, _) := w.perParam[key]? then allRows := allRows ++ rows
  -- rows of parameters reached only by hand-off
  for (key, (rows, _)) in w.perParam.toList do
    if !params.contains key then allRows := allRows ++ rows
  for r in allRows do
    let cls := if r.kind == "spend" then s!"spend:{classOf r.arg}" else r.kind
    spendLines := spendLines.push s!"  {short r.lem} {cls} @{r.landing} arg={r.arg} width={r.width} index={r.index} cmp={r.cmp}"
  let spends := allRows.filter (·.kind == "spend")
  let handoffs := allRows.filter (·.kind.startsWith "handoff→")
  let carries := allRows.filter (·.kind.startsWith "carry→")
  let untyped := allRows.filter (·.kind == "untyped")
  let spendsC := spends.filter fun r => classOf r.arg == "comments"
  let spendsE := spends.filter fun r => classOf r.arg == "empty"
  let spendsN := spends.filter fun r => classOf r.arg == "node"
  -- the width question is asked of the comments and empty closes; a node
  -- close carries its own indentation inside the node
  let asked := spendsC ++ spendsE
  let isInd (r : Row) := r.width.startsWith "ind["
  let isWs (r : Row) := r.width.startsWith "ws["
  let isDirect (r : Row) := r.index.startsWith "direct["
  let isPacked (r : Row) := r.index.startsWith "packed["
  let isCmp (r : Row) := r.cmp.startsWith "yes["
  let widthInd := (asked.filter isInd).size
  let widthWs := (asked.filter isWs).size
  let widthNone := (asked.filter fun r => r.width == "none").size
  let idxDirect := (asked.filter isDirect).size
  let idxPacked := (asked.filter isPacked).size
  let idxNone := (asked.filter fun r => r.index == "none").size
  let cmpYes := (asked.filter isCmp).size
  let cmpSame := (asked.filter fun r => (r.cmp.splitOn "≡").length > 1).size
  let both := (asked.filter fun r => isInd r && isDirect r).size
  let bothCmp := (asked.filter fun r => isInd r && isDirect r && isCmp r).size
  let handInd := (handoffs.filter isInd).size
  let handDirect := (handoffs.filter isDirect).size
  let handCmp := (handoffs.filter isCmp).size
  -- per site: over its own parameter's rows (spends and hand-off points)
  let mut siteLines : Array String := #[]
  let mut sitesBoth := 0
  let mut sitesWidth := 0
  let mut sitesNeither := 0
  let mut sitesBothAll := 0
  for (site, key) in paramOf do
    let own := match w.perParam[key]? with | some (rows, _) => rows | none => #[]
    -- the closure over hand-offs
    let mut seen : Array String := #[key]
    let mut todo : List String := [key]
    let mut allR : Array Row := #[]
    while !todo.isEmpty do
      let k := todo.head!
      todo := todo.tail!
      if let some (rows, targets) := w.perParam[k]? then
        allR := allR ++ rows
        for t in targets do
          if !seen.contains t then seen := seen.push t; todo := t :: todo
    let ownSpends := own.filter (·.kind == "spend")
    let ownHand := own.filter (·.kind.startsWith "handoff→")
    let ownCarry := own.filter (·.kind.startsWith "carry→")
    let ownNode := ownSpends.filter fun r => classOf r.arg == "node"
    -- judged at the site's own comments and empty closes, hand-offs and carries
    let judged := own.filter fun r => r.kind != "spend" || classOf r.arg != "node"
    let bothOwn := !judged.isEmpty && judged.all fun r => isInd r && isDirect r
    let widthOwn := !judged.isEmpty && judged.all fun r => isInd r || isWs r
    let status := if bothOwn then "BOTH" else if widthOwn then "WIDTH" else "NEITHER"
    if bothOwn then sitesBoth := sitesBoth + 1 else if widthOwn then sitesWidth := sitesWidth + 1 else sitesNeither := sitesNeither + 1
    let allSp := allR.filter fun r => r.kind != "spend" || classOf r.arg != "node"
    let bothAll := !allSp.isEmpty && allSp.all fun r => isInd r && isDirect r
    if bothAll then sitesBothAll := sitesBothAll + 1
    siteLines := siteLines.push s!"  {site} → {key}: spends={ownSpends.size} (node {ownNode.size}) handoffs={ownHand.size} carries={ownCarry.size} {status} reach={seen.size} reachJudged={allSp.size} reachBoth={bothAll}"
  -- §3 the empty closes
  let mut emptyLines : Array String := #[]
  let mut empties : Array Empty := #[]
  let lems := sorted ((reach.push ``PendingNode.close_with_ssl).filter fun n => true)
  let lems := distinctS (lems.map toString) |>.map (·.toName)
  for c in lems do
    let es ← emptiesOf c
    empties := empties ++ es
  for e in empties do
    emptyLines := emptyLines.push s!"  {short e.lem} {e.ctor} n={e.ix} @{e.landing} width={e.width} cmp={e.cmp}"
  let emptyLemmas := distinctS (empties.map fun e => short e.lem)
  let emptyInd := (empties.filter fun e => e.width.startsWith "ind[").size
  let emptyCmp := (empties.filter fun e => e.cmp.startsWith "yes[").size
  let emptySame := (empties.filter fun e => (e.cmp.splitOn "≡").length > 1).size
  let emptyClose := (empties.filter fun e => e.lem == ``PendingNode.close_with_ssl).size
  let got := s!"closeSites={closeSites.size} closePairs={closePairs.size} closePairsD={closePairsD.size} viaClose={viaClose} params={params.size} \
spends={spends.size} spendsC={spendsC.size} spendsE={spendsE.size} spendsN={spendsN.size} handoffs={handoffs.size} carries={carries.size} untyped={untyped.size} edges={(distinctS w.edges).size} paramsWalked={w.perParam.size} \
widthInd={widthInd} widthWs={widthWs} widthNone={widthNone} idxDirect={idxDirect} idxPacked={idxPacked} idxNone={idxNone} \
cmp={cmpYes} cmpSame={cmpSame} both={both} bothCmp={bothCmp} handInd={handInd} handDirect={handDirect} handCmp={handCmp} \
sitesBoth={sitesBoth} sitesWidth={sitesWidth} sitesNeither={sitesNeither} sitesBothAll={sitesBothAll} \
empties={empties.size} emptyLemmas={emptyLemmas.size} emptyInd={emptyInd} emptyCmp={emptyCmp} emptySame={emptySame} emptyClose={emptyClose} \
sites={sites.size} pairs={pairs.size} pairs21={shapeComps.size} pairs18={noDrop.size} nonANoDrop={nonANoDrop.size} reach={reach.size}"
  logInfo s!"CloseLandingWidth {got}"
  logInfo s!"closes:\n{String.intercalate "\n" closeLines.toList}"
  logInfo s!"sites:\n{String.intercalate "\n" siteLines.toList}"
  logInfo s!"spends:\n{String.intercalate "\n" spendLines.toList}"
  logInfo s!"edges:\n{String.intercalate "\n" ((distinctS w.edges).map ("  " ++ ·)).toList}"
  logInfo s!"empties:\n{String.intercalate "\n" emptyLines.toList}"
  -- the cross-instrument checks: items 249's and 250's frames, re-derived here
  -- (2026-10-24, B3 [66] col-0 threading: 23/21/21/18 → 19/19/18/16, as StreamCompositions pins)
  unless sites.size == 20 && pairs.size == 20 && shapeComps.size == 19 && noDrop.size == 17 do
    throwError "item 249's frame moved under this pass: sites={sites.size} pairs={pairs.size} shapeComps={shapeComps.size} noDrop={noDrop.size}"
  unless aPairs.size == 9 && nonANoDrop.size == 8 do
    throwError "item 250's frame moved under this pass: aPairs={aPairs.size} nonANoDrop={nonANoDrop.size}"
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedCloses" closeLines expectedCloses
  check "expectedSites" siteLines expectedSites
  check "expectedSpends" spendLines expectedSpends
  check "expectedEdges" ((distinctS w.edges).map ("  " ++ ·)) expectedEdges
  check "expectedEmpties" emptyLines expectedEmpties
  unless got == expectedLine do
    throwError "CloseLandingWidth moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.CloseLandingWidth
