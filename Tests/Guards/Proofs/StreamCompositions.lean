/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.RouteShapes

/-!
# How many stream compositions the build points use (DOCS item 249)

Item 248 found ten route shapes first built from the absorbed stream at
seventeen build points in eight lemmas, and priced the arm's threading at ten
re-routing lemmas — a price that holds only if every build point of a shape
COMPOSES the stream the same way.  This module reads the composition: at each
build point, every path from the producer's own `SLYamlStream sp_start _`
hypothesis (the leaf) up to the promise's conclusion, as the constructors the
leaf enters along it, each with the shape of its sibling arguments to the
document level — because `implicitContinue` under `GOpt.some` (a document
appended) and under `GOpt.none` (the stream extended by nothing) are two
compositions, and a census that stops at the constructor's name folds them.

**The trace** walks a term top-down with the leaf as target: through binders,
`have` values (a `have`-bound variable that reaches the leaf becomes a target),
casts, matchers (unfolded), `casesOn` (a target among the EXTRA arguments — a
hypothesis `cases` reverted because it depends on an index — is substituted
into every alternative; an `obtain`ed field inherits the paths of its matched
value's component), and LEMMA HOPS: a call whose argument reaches the leaf is
unfolded at the call site, so the leaf is followed into the lemma's own
constructors.  A path through two stream constructors — a park closed and
the closed stream re-extended — is one stacked composition.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropDependents (sorted)
open Tests.Guards.ExitHandoff (five tally)
open Tests.Guards.RouteShapes
set_option autoImplicit false

namespace Tests.Guards.StreamCompositions

/-! ## §1 Paths -/

/-- One step of a leaf-first path from the stream hypothesis to a term's root. -/
inductive Step where
  /-- the leaf enters a constructor at field `idx`; `shape` renders it with its siblings -/
  | ctor (n : Name) (idx : Nat) (shape : String)
  /-- the leaf flows into a lemma's parameter(s); the lemma is unfolded at the call -/
  | hop (n : Name) (params : String)
  /-- a `casesOn` minor premise entered, of `n` -/
  | case (ctor : Name) (n : Nat)
  /-- a constant not unfolded (logic plumbing), the leaf under argument `idx` -/
  | via (n : Name) (idx : Nat)
  /-- a `have`-bound variable whose value carries the leaf -/
  | have_ (x : Name)
  /-- an `obtain`ed field of a package whose component carries the leaf -/
  | destruct (x : Name) (precise : Bool)
  /-- the leaf passed to a hypothesis closure (a route the producer did not build) -/
  | hyp (x : Name) (idx : Nat)
  /-- a structure projection -/
  | proj (s : Name) (i : Nat)
  /-- a build point crossed: a park constructor's closure field or a lemma's route parameter -/
  | point (site : String) (kind : String) (spine : String)
  deriving Inhabited, BEq, Hashable, Repr

def short2 (n : Name) : String :=
  match n with
  | .str (.str _ a) b => s!"{a}.{b}"
  | _ => short n

def isStreamCtor (n : Name) : Bool :=
  n.getPrefix == ``SLYamlStream || n.getPrefix == ``ResumeFrames || n.getPrefix == ``KeyFrames

def isLogicCtor (n : Name) : Bool :=
  n == ``And.intro || n == ``Or.inl || n == ``Or.inr || n == ``Exists.intro

def logicShort (n : Name) : String :=
  if n == ``And.intro then "∧" else if n == ``Or.inl then "∨L"
  else if n == ``Or.inr then "∨R" else if n == ``Exists.intro then "∃" else short n

def Step.render : Step → String
  | .ctor n i sh => if isLogicCtor n then s!"{logicShort n}{i}" else sh
  | .hop n ps => s!"hop:{short n}.{ps}"
  | .case c n => s!"case:{short c}/{n}"
  | .via n i => s!"via:{short n}@{i}"
  | .have_ x => s!"have:{x}"
  | .destruct x p => s!"{if p then "destruct" else "destruct?"}:{x}"
  | .hyp x i => s!"hyp:{x}@{i}"
  | .proj s i => s!"proj:{short s}.{i}"
  | .point site _ _ => s!"POINT:{site}"

/-- The composition: the stream-family constructors on the path, leaf first. -/
def isAbsorb (n : Name) : Bool := (short n).startsWith "absorb_stacks"

def compOf (p : Array Step) : String :=
  let cs := p.filterMap fun s => match s with
    | .ctor n _ sh => if isStreamCtor n then some sh else none
    | .via n _ => if isAbsorb n then some s!"absorb:{short n}" else none
    | _ => none
  let hasCtor := p.any fun s => match s with | .ctor n _ _ => isStreamCtor n | _ => false
  let plumbing := p.any fun s => match s with
    | .via n _ => !isAbsorb n | .hyp .. | .hop .. => true | _ => false
  if hasCtor then String.intercalate " ▹ " cs.toList
  else String.intercalate " ▹ " (cs.toList ++ [if plumbing then "(via)" else "(fact)"])

/-- The failure mode: the constructors' names alone. -/
def ctorsOf (p : Array Step) : String :=
  let cs := p.filterMap fun s => match s with
    | .ctor n _ _ => if isStreamCtor n then some (short2 n) else none
    | .via n _ => if isAbsorb n then some "absorb" else none
    | _ => none
  if cs.isEmpty then "(none)" else String.intercalate " ▹ " cs.toList

def fullOf (p : Array Step) : String := String.intercalate " ▹ " (p.map Step.render).toList

def streamCtors (p : Array Step) : Nat :=
  (p.filter fun s => match s with | .ctor n _ _ => n.getPrefix == ``SLYamlStream | _ => false).size

/-! ## §2 The tracer -/

/-- One path that crosses a build point: its segment from the leaf to the
    first point crossed, and the whole path. -/
structure Found where
  producer : String
  site : String
  kind : String
  spine : String
  seg : Array Step
  full : Array Step
  deriving Inhabited

structure TState where
  paths : Array (Array Step) := #[]
  reach : Std.HashSet FVarId := {}
  memo : Std.HashMap FVarId (Array (Array Step)) := {}
  prems : Std.HashSet FVarId := {}
  hopOk : Std.HashMap Name Bool := {}
  approx : Nat := 0
  dead : Nat := 0
  opq : Array String := #[]
  hops : Array Name := #[]
  hopMax : Nat := 0
  visits : Nat := 0
  rpCache : Std.HashMap Name (Array (Nat × String) × Bool × Nat) := {}
  spCache : Std.HashMap String String := {}
  found : Array Found := #[]
  unmarked : Nat := 0
  collecting : Nat := 0
  prevStyle : Array String := #[]

structure TCtx where
  producer : Name
  params : Array Expr
  walked : Array Name
  table : Std.HashMap Name (Array Closure)
  st : IO.Ref TState

/-- What is known about a target variable: the paths from the leaf to it (its
    prefixes), and, when it is a package taken apart later, the constructor arms
    its value was built with and the same knowledge for each field. -/
inductive TInfo where
  | mk (prefixes : Array (Array Step)) (arms : Array (Name × Array TInfo)) (precise : Bool)
  deriving Inhabited

def TInfo.prefixes : TInfo → Array (Array Step) | .mk p _ _ => p
def TInfo.arms : TInfo → Array (Name × Array TInfo) | .mk _ a _ => a
def TInfo.precise : TInfo → Bool | .mk _ _ p => p
def TInfo.empty : TInfo := .mk #[] #[] true
partial def TInfo.addStep (s : Step) : TInfo → TInfo
  | .mk p a pr => .mk (p.map (· ++ #[s])) (a.map fun (c, fs) => (c, fs.map (TInfo.addStep s))) pr
def TInfo.merge : TInfo → TInfo → TInfo
  | .mk p a pr, .mk p' a' pr' => .mk (p ++ p') (a ++ a') (pr && pr')

abbrev Targets := Std.HashMap FVarId TInfo

def anyReach (cx : TCtx) (e : Expr) : MetaM Bool := do
  let r := (← cx.st.get).reach
  return e.hasAnyFVar (fun id => r.contains id)

def emitRaw (cx : TCtx) (p : Array Step) : MetaM Unit :=
  cx.st.modify fun s => { s with paths := s.paths.push p }

/-- At a leaf: the whole path is known; keep it when it crosses a build point. -/
def emitTop (cx : TCtx) (p : Array Step) : MetaM Unit := do
  match p.findIdx? (fun s => match s with | .point .. => true | _ => false) with
  | none => cx.st.modify fun s => { s with unmarked := s.unmarked + 1 }
  | some i =>
    let .point site kind spine := p[i]! | return
    let f : Found := { producer := short cx.producer, site, kind, spine, seg := p.extract 0 (i + 1), full := p }
    cx.st.modify fun s => { s with found := s.found.push f }

/-- A path at its leaf: a prefix being collected for a `have` or a field, or a
    whole path from the producer's body. -/
def emit (cx : TCtx) (p : Array Step) : MetaM Unit := do
  if (← cx.st.get).collecting > 0 then emitRaw cx p else emitTop cx p

def typeHead (t : Expr) : MetaM String := do
  let t := t.consumeMData
  let pre := if t.isForall then "∀→" else ""
  let h ← forallTelescope t fun _ b => pure b.consumeMData.getAppFn
  match h with
  | .const n _ => return s!"{pre}{short n}"
  | _ => return s!"{pre}?"

def roleOf (cx : TCtx) (id : FVarId) : MetaM String := do
  if cx.params.any (·.fvarId! == id) then return "hyp"
  if (← cx.st.get).prems.contains id then return "prem"
  return "var"

def docLevel (n : Name) : Bool :=
  let p := n.getPrefix
  p == ``SLYamlStream || p == ``ResumeFrames || p == ``KeyFrames || p == ``GOpt || p == ``GStar || p == ``GPlus ||
  p == ``SLAnyDocument

def isProofArg (a : Expr) : MetaM Bool := do
  try isProof a catch _ => pure true

/-- Casts and their payload: (arity, payload index). -/
def transparent : Name → Option (Nat × Nat)
  | ``Eq.mpr => some (4, 3) | ``Eq.mp => some (4, 3) | ``cast => some (4, 3) | ``id => some (2, 1)
  | ``Eq.ndrec => some (6, 3) | ``Eq.rec => some (6, 3) | ``Eq.subst => some (6, 5)
  | _ => none

def deadEnd (n : Name) : Bool :=
  n == ``absurd || n == ``False.elim || n == ``False.rec || n == ``False.casesOn

partial def shapeOf (cx : TCtx) (e : Expr) (depth : Nat) : MetaM String := do
  let e := peelC e.consumeMData
  match e with
  | .fvar id =>
    let d ← id.getDecl
    if let some v := d.value? then return ← shapeOf cx v depth
    return s!"{← roleOf cx id}:{← typeHead d.type}"
  | .lam .. => return "λ"
  | _ =>
    match e.getAppFn with
    | .const n _ =>
      match (← getEnv).find? n with
      | some (.ctorInfo ci) =>
        if depth == 0 || !docLevel n then return short2 n
        let args := e.getAppArgs
        let mut parts : Array String := #[]
        for i in [ci.numParams:args.size] do
          if ← isProofArg args[i]! then parts := parts.push (← shapeOf cx args[i]! (depth - 1))
        if parts.isEmpty then return short2 n
        return s!"{short2 n}({String.intercalate "," parts.toList})"
      | _ =>
        if (← Lean.Meta.getMatcherInfo? n).isSome || isCasesOnRecursor (← getEnv) n then return "match"
        return s!"lemma:{short n}"
    | .fvar id =>
      let d ← id.getDecl
      if let some v := d.value? then return ← shapeOf cx (mkAppN v e.getAppArgs).headBeta depth
      return s!"{← roleOf cx id}:{d.userName}(…)"
    | _ => return "?"

def shapeAt (cx : TCtx) (n : Name) (args : Array Expr) (idx : Nat) : MetaM String := do
  let some (.ctorInfo ci) := (← getEnv).find? n | return short2 n
  let mut parts : Array String := #[]
  for i in [ci.numParams:args.size] do
    if i == idx then parts := parts.push "S"
    else if ← isProofArg args[i]! then parts := parts.push (← shapeOf cx args[i]! 2)
  return s!"{short2 n}[{String.intercalate "," parts.toList}]"

/-- A lemma is followed into when its conclusion is a stream, a resume frame,
    a value line or a sequence tail, possibly under ∀/∧/∨/∃. -/
partial def concludesStream (t : Expr) : MetaM Bool := do
  forallTelescope t fun _ b => do
    let b := b.consumeMData
    match b.getAppFn with
    | .const n _ =>
      if n == ``SLYamlStream || n == ``ResumeFrames || n == ``KeyFrames || n == ``ExplValueLine || n == ``SeqEntryTail then
        return true
      if (n == ``And || n == ``Or) && b.getAppNumArgs == 2 then
        return (← concludesStream (b.getArg! 0)) || (← concludesStream (b.getArg! 1))
      if n == ``Exists && b.getAppNumArgs == 2 then
        match (b.getArg! 1).consumeMData with
        | .lam .. => return ← lambdaTelescope (b.getArg! 1) fun _ body => concludesStream body
        | _ => return false
      else return false
    | _ => return false

def hopOk (cx : TCtx) (n : Name) (ci : ConstantInfo) : MetaM Bool := do
  if let some r := (← cx.st.get).hopOk.get? n then return r
  let r ← concludesStream ci.type
  cx.st.modify fun s => { s with hopOk := s.hopOk.insert n r }
  return r

def distinctS (xs : Array String) : Array String := Id.run do
  let mut out : Array String := #[]
  for x in xs do if !out.contains x then out := out.push x
  return out

def routeParamsC (cx : TCtx) (n : Name) : MetaM (Array (Nat × String) × Bool × Nat) := do
  if let some r := (← cx.st.get).rpCache.get? n then return r
  let r ← routeParams n
  cx.st.modify fun s => { s with rpCache := s.rpCache.insert n r }
  return r

def routeSpineC (cx : TCtx) (n : Name) (pn : String) : MetaM String := do
  let key := s!"{n}.{pn}"
  if let some r := (← cx.st.get).spCache.get? key then return r
  let r := String.intercalate " | " (← routeParamSpines n pn).toList
  cx.st.modify fun s => { s with spCache := s.spCache.insert key r }
  return r

mutual

partial def go (cx : TCtx) (tg : Targets) (e : Expr) (up : List Step) (depth : Nat) : MetaM Unit := do
  cx.st.modify fun s => { s with visits := s.visits + 1 }
  if (← cx.st.get).visits > 40000000 then throwError "trace budget exceeded in {cx.producer}"
  let e := e.consumeMData
  unless ← anyReach cx e do return
  match e with
  | .fvar id => goFVar cx tg id up depth
  | .lam n t b bi =>
    withLocalDecl n bi t fun x => do
      cx.st.modify fun s => { s with prems := s.prems.insert x.fvarId! }
      go cx tg (b.instantiate1 x) up depth
  | .letE n t v b _ =>
    withLetDecl n t v fun x => do
      if ← anyReach cx v then cx.st.modify fun s => { s with reach := s.reach.insert x.fvarId! }
      go cx tg (b.instantiate1 x) up depth
  | .proj s i b => go cx tg b (.proj s i :: up) depth
  | .app .. => goApp cx tg e up depth
  | _ => return

partial def subPaths (cx : TCtx) (tg : Targets) (e : Expr) (depth : Nat) : MetaM (Array (Array Step)) := do
  let saved := (← cx.st.get).paths
  cx.st.modify fun s => { s with paths := #[], collecting := s.collecting + 1 }
  go cx tg e [] depth
  let ps := (← cx.st.get).paths
  cx.st.modify fun s => { s with paths := saved, collecting := s.collecting - 1 }
  return ps

partial def goFVar (cx : TCtx) (tg : Targets) (id : FVarId) (up : List Step) (depth : Nat) : MetaM Unit := do
  if let some info := tg.get? id then
    for p in info.prefixes do emit cx (p ++ up.toArray)
  else
    let d ← id.getDecl
    if let some v := d.value? then
      let ps ← match (← cx.st.get).memo.get? id with
        | some ps => pure ps
        | none =>
          let ps ← subPaths cx tg v depth
          cx.st.modify fun s => { s with memo := s.memo.insert id ps }
          pure ps
      for p in ps do emit cx (p ++ #[.have_ d.userName] ++ up.toArray)

partial def goApp (cx : TCtx) (tg : Targets) (e : Expr) (up : List Step) (depth : Nat) : MetaM Unit := do
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .fvar id =>
    let d ← id.getDecl
    goFVar cx tg id up depth
    for i in [0:args.size] do
      if ← anyReach cx args[i]! then go cx tg args[i]! (.hyp d.userName i :: up) depth
  | .lam .. => go cx tg e.headBeta up depth
  | .const n us =>
    let env ← getEnv
    if let some (arity, k) := transparent n then
      if k < args.size then
        go cx tg (mkAppN args[k]! (args.extract arity args.size)).headBeta up depth
      return
    if n == ``letFun then
      if args.size ≥ 4 then
        go cx tg (mkAppN (mkApp args[3]! args[2]!) (args.extract 4 args.size)).headBeta up depth
      return
    if deadEnd n then
      cx.st.modify fun s => { s with dead := s.dead + 1 }
      return
    if (← Lean.Meta.getMatcherInfo? n).isSome then
      let some ci := env.find? n | return
      go cx tg ((ci.instantiateValueLevelParams! us).beta args) up depth
      return
    if isCasesOnRecursor env n then
      goCases cx tg n args up depth
      return
    let (rps, park, arity) ← routeParamsC cx n
    let full := args.size == arity
    match env.find? n with
    | some (.ctorInfo ci) =>
      -- a park (or a flow base): its closure fields are build points
      let cls := if full then (cx.table.get? n).getD #[] else #[]
      for i in [ci.numParams:args.size] do
        if ← anyReach cx args[i]! then
          let here := cls.filter (·.fieldIdx == i)
          if !here.isEmpty then
            let spine := String.intercalate " | " (distinctS (here.map (·.spine))).toList
            let cn := if n == ``FlowBaseRoutes.mk then "FlowBaseRoutes" else short n
            go cx tg args[i]! (.point s!"{short cx.producer}:{cn}.{here[0]!.field}" "slot" spine :: up) depth
          else
            let sh ← if isLogicCtor n then pure (logicShort n)
              else if docLevel n then shapeAt cx n args i else pure (short2 n)
            go cx tg args[i]! (.ctor n (i - ci.numParams) sh :: up) depth
    | some (.recInfo _) =>
      cx.st.modify fun s => { s with opq := s.opq.push s!"{cx.producer}:{short n}" }
    | some ci =>
      -- a lemma whose conclusion is a stream and that takes no route: followed into
      if n.getRoot == `L4YAML && !park && rps.isEmpty && !cx.walked.contains n && depth < 12 &&
          (← hopOk cx n ci) then
        if let some v := ci.value? (allowOpaque := true) then
          let v := v.instantiateLevelParams ci.levelParams us
          let names := ci.type.getForallBinderNames.toArray
          let mut ps : Array String := #[]
          for i in [0:args.size] do
            if ← anyReach cx args[i]! then ps := ps.push ((names[i]?.map toString).getD s!"{i}")
          cx.st.modify fun s => { s with hops := if s.hops.contains n then s.hops else s.hops.push n,
                                         hopMax := max s.hopMax (depth + 1) }
          go cx tg (v.beta args) (.hop n (String.intercalate "+" ps.toList) :: up) (depth + 1)
          return
      -- otherwise its route parameters are build points, the rest is plumbing
      for i in [0:args.size] do
        if ← anyReach cx args[i]! then
          match (if full then rps.find? (·.1 == i) else none) with
          | some (_, pn) =>
            let spine ← routeSpineC cx n pn
            go cx tg args[i]! (.point s!"{short cx.producer}→{short n}.{pn}" "route" spine :: up) depth
          | none => go cx tg args[i]! (.via n i :: up) depth
    | none => return
  | _ =>
    for i in [0:args.size] do
      if ← anyReach cx args[i]! then go cx tg args[i]! (.via `app i :: up) depth

/-- What is known about a term that is matched on or projected from. -/
partial def infoOf (cx : TCtx) (tg : Targets) (e : Expr) (depth : Nat) : MetaM TInfo := do
  let prefixes ← subPaths cx tg e depth
  if prefixes.isEmpty then return TInfo.empty
  match ← armsOf cx tg e depth with
  | some arms => return .mk prefixes arms true
  | none => return .mk prefixes #[] false

/-- The arms of a matched value: for each, its constructor and what is known of
    each field.  `none` when some arm is not a constructor application (a lemma
    yields the package) — the destructure is then approximate. -/
partial def armsOf (cx : TCtx) (tg : Targets) (M : Expr) (depth : Nat) :
    MetaM (Option (Array (Name × Array TInfo))) := do
  let M := peelC M.consumeMData
  match M with
  | .fvar id =>
    if let some info := tg.get? id then return if info.precise then some info.arms else none
    let d ← id.getDecl
    if let some v := d.value? then
      let r ← armsOf cx tg v depth
      return r.map fun arms => arms.map fun (c, fs) => (c, fs.map (TInfo.addStep (.have_ d.userName)))
    return none
  | .letE n t v b _ =>
    withLetDecl n t v fun x => do
      if ← anyReach cx v then cx.st.modify fun s => { s with reach := s.reach.insert x.fvarId! }
      armsOf cx tg (b.instantiate1 x) depth
  | .lam .. => return none
  | .proj _ i b =>
    let info ← infoOf cx tg b depth
    if info.precise && info.arms.size == 1 then
      if let some child := info.arms[0]!.2[i]? then
        return if child.precise then some child.arms else none
    return none
  | _ =>
    let f := M.getAppFn
    let args := M.getAppArgs
    match f with
    | .lam .. => armsOf cx tg M.headBeta depth
    | .const n us =>
      let env ← getEnv
      if (n == ``And.left || n == ``And.right) && args.size == 3 then
        let info ← infoOf cx tg args[2]! depth
        if info.precise && info.arms.size == 1 then
          if let some child := info.arms[0]!.2[if n == ``And.left then 0 else 1]? then
            return if child.precise then some child.arms else none
        return none
      match env.find? n with
      | some (.ctorInfo ci) =>
        let mut fs : Array TInfo := #[]
        for i in [ci.numParams:args.size] do fs := fs.push (← infoOf cx tg args[i]! depth)
        return some #[(n, fs)]
      | _ =>
        if (← Lean.Meta.getMatcherInfo? n).isSome then
          let some ci := env.find? n | return none
          return ← armsOf cx tg ((ci.instantiateValueLevelParams! us).beta args) depth
        if isCasesOnRecursor env n then
          let I := n.getPrefix
          let some (.inductInfo iv) := env.find? I | return none
          let majorIdx := iv.numParams + 1 + iv.numIndices
          let arity := majorIdx + 1 + iv.ctors.length
          if args.size < arity then return none
          let extras := args.extract arity args.size
          let major := args[majorIdx]!
          let info? ← if ← anyReach cx major then pure (some (← infoOf cx tg major depth)) else pure none
          let mut out : Array (Name × Array TInfo) := #[]
          for k in [0:iv.ctors.length] do
            let minor := args[majorIdx + 1 + k]!
            let some (.ctorInfo cv) := env.find? iv.ctors[k]! | return none
            let r ← forallBoundedTelescope (← inferType minor) cv.numFields fun xs _ => do
              let tg' ← bindFields cx tg info? iv.ctors[k]! xs
              armsOf cx tg' (mkAppN (mkAppN minor xs) extras).headBeta depth
            match r with
            | some arms => out := out ++ arms
            | none => return none
          return some out
        if let some (arity, k) := transparent n then
          if k < args.size then
            return ← armsOf cx tg (mkAppN args[k]! (args.extract arity args.size)).headBeta depth
          return none
        if n == ``letFun && args.size ≥ 4 then
          return ← armsOf cx tg (mkAppN (mkApp args[3]! args[2]!) (args.extract 4 args.size)).headBeta depth
        if deadEnd n then return some #[]
        return none
    | _ => return none

/-- Entering a minor premise for `ctor` with fields `xs`: the fields that carry
    the leaf become targets — precisely, from the matched value's arms of that
    constructor, or approximately (every field) when the arms are unknown. -/
partial def bindFields (cx : TCtx) (tg : Targets) (info? : Option TInfo) (ctor : Name) (xs : Array Expr) :
    MetaM Targets := do
  let some info := info? | return tg
  let mut tg' := tg
  let mut r := (← cx.st.get).reach
  if info.precise then
    -- merge the arms of this constructor, field by field
    let mut merged : Array (Option TInfo) := xs.map fun _ => none
    for (c, fs) in info.arms do
      if c != ctor then continue
      for i in [0:min xs.size fs.size] do
        merged := merged.set! i (some (match merged[i]! with | some m => m.merge fs[i]! | none => fs[i]!))
    for i in [0:xs.size] do
      if let some m := merged[i]! then
        if m.prefixes.isEmpty then continue
        let nm := (← xs[i]!.fvarId!.getDecl).userName
        tg' := tg'.insert xs[i]!.fvarId! (.mk (m.prefixes.map (· ++ #[.destruct nm true])) m.arms m.precise)
        r := r.insert xs[i]!.fvarId!
  else
    cx.st.modify fun s => { s with approx := s.approx + 1 }
    for x in xs do
      let nm := (← x.fvarId!.getDecl).userName
      tg' := tg'.insert x.fvarId! (.mk (info.prefixes.map (· ++ #[.destruct nm false])) #[] false)
      r := r.insert x.fvarId!
  cx.st.modify fun s => { s with reach := r }
  return tg'

partial def goCases (cx : TCtx) (tg : Targets) (n : Name) (args : Array Expr) (up : List Step) (depth : Nat) :
    MetaM Unit := do
  let env ← getEnv
  let I := n.getPrefix
  let some (.inductInfo iv) := env.find? I | return
  let majorIdx := iv.numParams + 1 + iv.numIndices
  let arity := majorIdx + 1 + iv.ctors.length
  if args.size < arity then
    cx.st.modify fun s => { s with opq := s.opq.push s!"{cx.producer}:partial {short n}" }
    return
  let major := args[majorIdx]!
  let extras := args.extract arity args.size
  let info? ← if ← anyReach cx major then pure (some (← infoOf cx tg major depth)) else pure none
  for k in [0:iv.ctors.length] do
    let ctor := iv.ctors[k]!
    let minor := args[majorIdx + 1 + k]!
    let some (.ctorInfo cv) := env.find? ctor | continue
    forallBoundedTelescope (← inferType minor) cv.numFields fun xs _ => do
      let tg' ← bindFields cx tg info? ctor xs
      go cx tg' (mkAppN (mkAppN minor xs) extras).headBeta (.case ctor iv.ctors.length :: up) depth

end

/-- Trace one producer from its body root: every path from one of its own
    `SLYamlStream sp_start _` hypotheses that crosses a build point. -/
def traceProducer (table : Std.HashMap Name (Array Closure)) (walked : Array Name) (st : IO.Ref TState)
    (c : Name) : MetaM (Array Name) := do
  let some ci := (← getEnv).find? c | throwError "{c}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  lambdaTelescope v fun params body => do
    let mut spStart? : Option FVarId := none
    for x in params do
      if (← x.fvarId!.getDecl).userName == `sp_start then spStart? := some x.fvarId!
    let some spStart := spStart? | return #[]
    let mut streamHyps : Array FVarId := #[]
    for x in params do
      let ty := (← inferType x).consumeMData
      if ty.isAppOfArity ``SLYamlStream 2 && ty.containsFVar spStart then streamHyps := streamHyps.push x.fvarId!
    let cx : TCtx := { producer := c, params, walked, table, st }
    let reach : Std.HashSet FVarId := streamHyps.foldl (fun r h => r.insert h) {}
    st.modify fun s => { s with paths := #[], reach, memo := {}, prems := {} }
    let tg : Targets := streamHyps.foldl (fun m h => m.insert h (.mk #[#[]] #[] true)) {}
    go cx tg body [] 0
    -- the park builders this body calls, for the transitive reach — and item
    -- 248's reading of the same sites (leaves through `have` values), so that
    -- every site the trace finds and that reading did not is explained
    let builders ← IO.mkRef (#[] : Array Name)
    let skip (n : Name) : Bool :=
      n == ``And.intro || n == ``Or.inl || n == ``Or.inr || n == ``Exists.intro ||
      (n.toString.splitOn ".match_").length > 1 || n.isInternal ||
      (`L4YAML.Proofs.StreamAccum.PendingNode).isPrefixOf n || n == ``FlowBaseRoutes.mk
    forEachExpr' body fun e => do
      if let .const n _ := e.getAppFn then
        if e.isApp then
          let (rps, park, arity) ← routeParamsC cx n
          if e.getAppNumArgs == arity then
            let args := e.getAppArgs
            if let some cls := table.get? n then
              for cl in cls do
                if h : cl.fieldIdx < args.size then
                  if (← classify params spStart cl.path args[cl.fieldIdx]) == "stream" then
                    let site := s!"{short c}:{short n}.{cl.field}"
                    st.modify fun s => { s with prevStyle := if s.prevStyle.contains site then s.prevStyle else s.prevStyle.push site }
            if !skip n then
              for (i, pn) in rps do
                if h : i < args.size then
                  let (_, fwd) ← resolve params args[i]
                  let u ← if fwd.isNone then usage params spStart args[i] else pure "fwd"
                  if u == "stream" then
                    let site := s!"{short c}→{short n}.{pn}"
                    st.modify fun s => { s with prevStyle := if s.prevStyle.contains site then s.prevStyle else s.prevStyle.push site }
              if park then builders.modify fun a => if a.contains n then a else a.push n
      return true
    return ← builders.get

/-! ## §4 The pins

Pinned by `scratchpad/l4yaml-beta5-item249/fill_pins.py` from the first clean
reading; every numeric field of the line and one row of each list are
perturbed by `perturb.sh`, and each perturbation must throw. -/

-- Item 304: the two value-line rows respell `Resume(_)▹…` → `Key(_)▹…` — the
-- stacks are `KeyFrames` (item 302's), rendered as `RouteShapes` renders them.
-- 2026-10-24 (B3 [66] col-0 threading): the content/block parks close from `sp_gram` through the frame's run + gate,
-- so four `SSLComments ⇒ Stream` compositions and the `content_dispatch_routed.h_route` one no longer build the
-- stream by composition; `closeThenBlock.h_close_pending` gains the run segment (3 → 4).
-- Item 371: the value-line sites end `⇒ Resume(map(_)::[])▹Stream`; `question_open_map`'s `h_expl` carries its
-- `SCompactMapTail` tail and its `h_closeFV`/`h_framesV` are built from the bound tail route.
-- 2026-10-29 (item 388): the mapping park's `h_close` / `h_closeF` sites read `SBlockNode(_+1,blockOut)` — the
-- grammar's `[187]` context; segments and compositions unchanged.
def expectedSites : List String :=
  [ "question_open_map:pendingMapValue.h_close [SBlockNode(_+1,blockOut) ⇒ Stream] segments=2 comps=1",
    "question_open_map:pendingMapValue.h_ivl [[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream] segments=2 comps=1",
    "question_open_map:pendingMapValue.h_expl [SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Stream] segments=2 comps=1 NEW",
    "question_open_map:pendingMapValue.h_vslot [[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream] segments=2 comps=1",
    "question_open_map:pendingMapValue.h_closeF [SBlockNode(_+1,blockOut) ⇒ Resume(map(_)::_)▹Stream] segments=2 comps=1 NEW",
    "question_open_map:pendingMapValue.h_frames [SSLComments ⇒ Resume(_)▹Stream] segments=2 comps=1 NEW",
    "question_open_map:pendingMapValue.h_closeFV [SBlockNode(_+1,blockIn) ⇒ Key(_)▹ExplValueLine(_)] segments=2 comps=1 NEW",
    "question_open_map:pendingMapValue.h_framesV [SSLComments ⇒ Key(_)▹ExplValueLine(_)] segments=2 comps=1 NEW",
    "colon_open_map:pendingMapValue.h_close [SBlockNode(_+1,blockOut) ⇒ Stream] segments=2 comps=1",
    "colon_open_map:pendingMapValue.h_closeF [SBlockNode(_+1,blockOut) ⇒ Resume(map(_)::_)▹Stream] segments=2 comps=1 NEW",
    "colon_open_map:pendingMapValue.h_frames [SSLComments ⇒ Resume(_)▹Stream] segments=2 comps=1 NEW",
    "content_dispatch_after_close→content_dispatch_routed.h_route [SBlockNode(0,blockIn) ⇒ Stream] segments=1 comps=1",
    "accum_content_on_noPending→keyctx_of_preprocess.h_close [SSLComments ⇒ Stream] segments=1 comps=1",
    "accum_flow_open_depth0→flowKeyRoute_of_root.h_close [SSLComments ⇒ Stream] segments=3 comps=3",
    "accum_block_pending→accum_block_on_closeThenBlock.h_close_pending [SSLComments ⇒ Stream] segments=4 comps=3",
    "accum_block_pending→accum_block_on_pendingBlock.h_close_pending [SSLComments ⇒ Stream] segments=3 comps=3",
    "accum_block_pending→accum_block_on_closeThenBlock.h_vslot [[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream | [col(_)=_+1] SBlockIndented(_,blockOut) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream | [col(_)=_+1] SBlockIndented(_,blockOut) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream] segments=2 comps=2",
    "accum_structural_pending→dispatch_new_pending.h_dir_route [SLDirectiveDocument ⇒ Stream] segments=1 comps=1",
    "structural_dispatch_to_pending:pendingDocStart.h_doc_route [GAlt(SLBareDocument,GSeq(SENode,SSLComments)) ⇒ Stream] segments=1 comps=1",
    "question_open_map:pendingMapValue.h_kslot [SBlockNode(_+1,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream] segments=2 comps=1"]

-- 2026-10-24 (B3 [66] col-0 threading): the compositions behind the five sites dropped above go with them.
-- Item 371: the value-line compositions end in the one-level `ResumeFrames` (the restated pack);
-- `question_open_map` builds `h_expl`/`h_closeFV`/`h_framesV` from the bound tail route `h_route51F`.
def expectedSiteComps : List String :=
  [ "question_open_map:pendingMapValue.h_close ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "question_open_map:pendingMapValue.h_ivl ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "question_open_map:pendingMapValue.h_expl ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S]",
    "question_open_map:pendingMapValue.h_vslot ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "question_open_map:pendingMapValue.h_closeF ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
    "question_open_map:pendingMapValue.h_frames ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
    "question_open_map:pendingMapValue.h_closeFV ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S]",
    "question_open_map:pendingMapValue.h_framesV ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S]",
    "colon_open_map:pendingMapValue.h_close ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "colon_open_map:pendingMapValue.h_closeF ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
    "colon_open_map:pendingMapValue.h_frames ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
    "content_dispatch_after_close→content_dispatch_routed.h_route ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "accum_content_on_noPending→keyctx_of_preprocess.h_close ⟶ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
    "accum_flow_open_depth0→flowKeyRoute_of_root.h_close ⟶ absorb:absorb_stacksB ▹ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
    "accum_flow_open_depth0→flowKeyRoute_of_root.h_close ⟶ absorb:absorb_stacksB ▹ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
    "accum_flow_open_depth0→flowKeyRoute_of_root.h_close ⟶ absorb:absorb_stacksB ▹ SLYamlStream.scannerDrop[S,prem:SSLComments]",
    "accum_block_pending→accum_block_on_closeThenBlock.h_close_pending ⟶ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
    "accum_block_pending→accum_block_on_closeThenBlock.h_close_pending ⟶ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
    "accum_block_pending→accum_block_on_closeThenBlock.h_close_pending ⟶ SLYamlStream.scannerDrop[S,prem:SSLComments]",
    "accum_block_pending→accum_block_on_pendingBlock.h_close_pending ⟶ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
    "accum_block_pending→accum_block_on_pendingBlock.h_close_pending ⟶ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
    "accum_block_pending→accum_block_on_pendingBlock.h_close_pending ⟶ SLYamlStream.scannerDrop[S,prem:SSLComments]",
    "accum_block_pending→accum_block_on_closeThenBlock.h_vslot ⟶ (fact)",
    "accum_block_pending→accum_block_on_closeThenBlock.h_vslot ⟶ (via)",
    "accum_structural_pending→dispatch_new_pending.h_dir_route ⟶ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.some(SLAnyDocument.directive(prem:SLDirectiveDocument)),GStar.nil]",
    "structural_dispatch_to_pending:pendingDocStart.h_doc_route ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.explicit(SLExplicitDocument.withContent)),GStar.nil]",
    "question_open_map:pendingMapValue.h_kslot ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S]"]

-- Item 304: the bottom of the value-line compositions is `KeyFrames.bottom`.
-- 2026-10-24 (B3 [66] col-0 threading): three composition shapes were only built at the dropped content-park sites.
def expectedComps : List String :=
  ["(fact)",
   "SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
   "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
   "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
   "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.explicit(SLExplicitDocument.withContent)),GStar.nil]",
   "SLYamlStream.scannerDrop[S,prem:SSLComments]",
   "SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
   "SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.some(SLAnyDocument.directive(prem:SLDirectiveDocument)),GStar.nil]",
   "absorb:absorb_stacksB ▹ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
   "absorb:absorb_stacksB ▹ SLYamlStream.scannerDrop[S,prem:SSLComments]",
   "absorb:absorb_stacksB ▹ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
   -- Item 371: the restated value-line pack — `ResumeFrames.one`'s level over its bottom (12 → 14)
   "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S]",
   "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S]",
   "SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S]"]
-- 2026-10-24 (B3 [66] col-0 threading): follows the dropped content-park sites above.
-- 2026-10-29 (item 388): the two mapping-park compositions open on `SBlockNode(_+1,blockOut)` (see expectedSites).
def expectedShapeComps : List String :=
  [ "GAlt(SLBareDocument,GSeq(SENode,SSLComments)) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.explicit(SLExplicitDocument.withContent)),GStar.nil]",
    "SBlockNode(0,blockIn) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "SBlockNode(_+1,blockOut) ⇒ Resume(map(_)::_)▹Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
    "SBlockNode(_+1,blockOut) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
    "SLDirectiveDocument ⇒ Stream ⟶ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.some(SLAnyDocument.directive(prem:SLDirectiveDocument)),GStar.nil]",
    "SSLComments ⇒ Resume(_)▹Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[var:∀→lt,S]",
    "SSLComments ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
    "SSLComments ⇒ Stream ⟶ SLYamlStream.scannerDrop[S,prem:SSLComments]",
    "SSLComments ⇒ Stream ⟶ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
    "SSLComments ⇒ Stream ⟶ absorb:absorb_stacksB ▹ SLYamlStream.implicitContinue[S,GStar.cons(SLDocumentPrefix.comments,GStar.nil),GOpt.none,GStar.nil]",
    "SSLComments ⇒ Stream ⟶ absorb:absorb_stacksB ▹ SLYamlStream.scannerDrop[S,prem:SSLComments]",
    "SSLComments ⇒ Stream ⟶ absorb:absorb_stacksB ▹ SLYamlStream.suffixContinue[S,GPlus.mk(SLDocumentSuffix.mk,GStar.nil),GStar.nil,GOpt.none,GStar.nil]",
    "[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream ⟶ (fact)",
    "[col(_)=_+1] SBlockIndented(_,blockOut) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil]",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "SBlockMapEntry(_) > SCompactMapTail(_) ⇒ Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S]",
   "SBlockNode(_+1,blockIn) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S]",
   "SBlockNode(_+1,blockIn) ⇒ Key(_)▹ExplValueLine(_) ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S]",
   "SSLComments ⇒ Key(_)▹ExplValueLine(_) ⟶ SLYamlStream.implicitContinue[S,GStar.nil,GOpt.some(SLAnyDocument.bare(SLBareDocument.mk)),GStar.nil] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.bottom[S] ▹ ResumeFrames.level[λ,S] ▹ KeyFrames.bottom[S]",
   "[col(_)=_+1] SBlockIndented(_,blockOut) > SIndent(_) > GLit(':') > SBlockIndented(_,blockOut) ⇒ Resume(map(_)::[])▹Stream ⟶ (fact)"]
/-- 2026-10-18 (item 284): `unmarked` 218 -> 206 and nothing else.  The twelve are
    `accum_content_pending`'s `pendingFlow` arm, whose landings ran through the
    shared builder's four routes and now defer to the escape at every landing:
    restoring that one arm on the item-284 tree reads 218 and this whole line
    again (`scratchpad/l4yaml-row12-steps/83-isolation-streamcomp.log`).  None of
    the twelve crossed a build point, which is why every site, segment and
    composition count holds.

    2026-10-18 (item 285): `unmarked` 206 -> 203 and nothing else.  The three live
    arms of `accum_flow_open_depth0` spend `slot_ride` where they spent
    `drop_ride`: each of their paths ran to `dropClose`'s leaf, and the slot's
    value route is refuted rather than routed, so it emits none.  Putting the
    three spends back on `drop_ride` on the item-285 tree reads 206 again
    (`scratchpad/l4yaml-row12-steps/153-iso-streamcomp.log`).

    2026-10-19 (item 287): `segments` 51 -> 53 and `unmarked` 203 -> 202.  The
    two segments are ~~the value park's frameless arm, which applies the escape
    to the stream leaf its slot already spends~~ — corrected at item 288 — the
    two deferrals at the one site `accum_block_pending→…closeThenBlock.h_vslot`
    keys: the value park's and the dead `pendingFlow` arm's, each applying the
    escape to the stream leaf; `siteComps` names the composition, `(via)`.
    `unmarked` is net over the restructure: the fallback streams the content
    parks handed `accum_block_on_closeThenBlock` are gone and the deferrals at
    the seven arms are new, and one fewer leaf-to-top path crosses no build
    point.  This item did not isolate which.

    2026-10-19 (item 288): `segments` 53 -> 52 and nothing else — the value
    park's deferral path (`case:inr/2`), refuted now that the park holds the
    stamp; the dead `pendingFlow` arm's stays.

    2026-10-19 (item 289): `unmarked` 202 -> 201 and nothing else — the props
    consumer's `tab` deferral, a leaf-to-top path that crosses no build point,
    refuted on the saved key's possibility and line the reason carries.
    Putting the escape back at that one arm on the item-289 tree reads 202
    again (`scratchpad/l4yaml-row12-steps/312-iso-streamcomp.log`).

    2026-10-19 (item 293): `unmarked` 201 -> 200 and nothing else — the
    implicit-key consumer's `¬ possible` deferral, refuted on the park's
    `h_live`.  Putting the escape back at that one arm on the item-293 tree
    reads 201 again (`scratchpad/l4yaml-row12-steps/371-iso-streamcomp-293.log`).

    2026-10-19 (item 295): `prev` 19 -> 21 and `prevStyle` with it.  `prev` is
    `RouteShapes.expectedK`'s provenance, and item 295's K table names two more
    stream-built sites: `flowKeyRoute_of_root.h_close` in
    `accum_flow_open_depth0` (`new` 5 -> 4, `newVsStyle` with it, and that
    site's row loses its `NEW`), and `slot_ride`'s `mk.key`, which no
    composition here reads (`missing` 1 -> 2, `styleOnly` with it).  No
    composition moved.

    2026-10-20 (item 297): `unmarked` 200 -> 198 and nothing else — the two
    `:` consumers' `dedent` deferrals, leaf-to-top paths that cross no build
    point, deleted with the constructor (both pack exits key a fresh document,
    so `dedent` has no production). -/
-- 2026-10-24 (B3 [66] col-0 threading): the content/block parks close from `sp_gram`; the site/composition
-- tallies follow the lists above.  dropClose 0 → 1: `accum_block_pending` now composes through
-- `close_with_sslFrom`, whose `pendingFlow` arm is the pre-existing drop ride (β.5 R3) — no new spend.
def expectedLine : String :=
-- Item 371 (comps=12 → 14, byCtor=9 → 11, obtainedSites=4 → 8, prev=17 → 14, new=4 → 7, prevStyle=17 → 14, newVsStyle=4 → 7, segHops=9 → 10, hops=11 → 12): the value-line compositions end in
-- the one-level `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` are obtained from the bound tail route.
  "sites=20 genuine=20 pairs=20 viaSites=0 segments=40 genuineSegs=39 facts=1 stacked=0 comps=14 byCtor=11 byFull=39 shapes=13 shapeComps=19 shapeCompsNoDrop=17 obtainedSites=8 approxSites=0 prev=14 new=7 missing=1 prevStyle=14 prevStyleOff=0 newVsStyle=7 styleOnly=1 segHops=10 segAbsorb=3 single=0 dropClose=1 directive=1 hops=12 hopMax=3 approx=37 dead=6 opaque=0 unmarked=157 reach=38"

/-! ## §5 The reading -/

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
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
  -- the reach: the 25, then every park builder they call, transitively
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
  let s ← st.get
  -- distinct (site, segment), in the order found
  let mut segs : Array Found := #[]
  for f in s.found do
    if !segs.any (fun g => g.site == f.site && g.seg == f.seg) then segs := segs.push f
  let sites := distinctS (segs.map (·.site))
  let genuine := segs.filter fun f => compOf f.seg != "(via)"
  let gsites := distinctS (genuine.map (·.site))
  let viaSites := sites.filter fun x => !gsites.contains x
  let pairOf (site : String) : String :=
    if (site.splitOn "→").length > 1 then (site.splitOn "→")[1]! else site
  let pairs := distinctS (gsites.map pairOf)
  let comps := distinctS (genuine.map fun f => compOf f.seg)
  let ctors := distinctS (genuine.map fun f => ctorsOf f.seg)
  let full := distinctS (genuine.map fun f => fullOf f.seg)
  let stacked := (genuine.filter fun f => streamCtors f.seg ≥ 2).size
  let facts := genuine.filter fun f => compOf f.seg == "(fact)"
  let has (f : Found) (pat : String) : Bool := ((fullOf f.seg).splitOn pat).length > 1
  let obtainedSites := distinctS ((genuine.filter fun f => has f "destruct:").map (·.site))
  let approxSites := distinctS ((segs.filter fun f => has f "destruct?").map (·.site))
  let mut shapeComps : Array String := #[]
  for f in genuine do
    for sp in f.spine.splitOn " | " do
      let sc := s!"{sp} ⟶ {compOf f.seg}"
      if !shapeComps.contains sc then shapeComps := shapeComps.push sc
  let noDrop := shapeComps.filter fun sc => (sc.splitOn "scannerDrop").length == 1
  let shapes := distinctS (shapeComps.map fun sc => (sc.splitOn " ⟶ ").head!)
  -- item 248's build points, from its pinned provenance, and its reading redone here
  let mut prev : Array String := #[]
  for line in Tests.Guards.RouteShapes.expectedK do
    let parts := line.splitOn "  ← "
    if parts.length < 2 then continue
    let prov := (parts[1]!.splitOn "  [").head!
    for p in prov.splitOn ", " do
      let p := p.trimAscii.toString
      if p != "" && !prev.contains p then prev := prev.push p
  let newSites := gsites.filter fun x => !prev.contains x
  let missing := prev.filter fun x => !gsites.contains x
  let prevStyle := s.prevStyle
  let prevStyleOff := (prevStyle.filter fun x => !prev.contains x) ++ (prev.filter fun x => !prevStyle.contains x)
  let newVsStyle := gsites.filter fun x => !prevStyle.contains x
  let styleOnly := prevStyle.filter fun x => !gsites.contains x
  let segHops := distinctS (genuine.foldl (fun acc f => acc ++ (f.seg.filterMap fun st => match st with
    | .hop n _ => some (short n) | _ => none)) #[])
  let segAbsorb := (genuine.filter fun f => f.seg.any fun st => match st with | .via n _ => isAbsorb n | _ => false).size
  let got := s!"sites={sites.size} genuine={gsites.size} pairs={pairs.size} viaSites={viaSites.size} \
segments={segs.size} genuineSegs={genuine.size} facts={facts.size} stacked={stacked} comps={comps.size} byCtor={ctors.size} \
byFull={full.size} shapes={shapes.size} shapeComps={shapeComps.size} shapeCompsNoDrop={noDrop.size} \
obtainedSites={obtainedSites.size} approxSites={approxSites.size} prev={prev.size} new={newSites.size} missing={missing.size} \
prevStyle={prevStyle.size} prevStyleOff={prevStyleOff.size} newVsStyle={newVsStyle.size} styleOnly={styleOnly.size} \
segHops={segHops.size} segAbsorb={segAbsorb} \
single={(genuine.filter fun f => has f "SLYamlStream.single").size} dropClose={(genuine.filter fun f => has f "hop:dropClose").size} \
directive={(genuine.filter fun f => has f "directive").size} hops={s.hops.size} hopMax={s.hopMax} approx={s.approx} dead={s.dead} \
opaque={s.opq.size} unmarked={s.unmarked} reach={reach.size}"
  logInfo s!"StreamCompositions {got}"
  let mut siteLines : Array String := #[]
  let mut siteComps : Array String := #[]
  let mut pathLines : Array String := #[]
  for site in sites do
    let here := segs.filter (·.site == site)
    let cs := distinctS (here.map fun f => compOf f.seg)
    siteLines := siteLines.push s!"  {site} [{here[0]!.spine}] segments={here.size} comps={cs.size}{if prev.contains site then "" else " NEW"}"
    for c in cs do siteComps := siteComps.push s!"  {site} ⟶ {c}"
    for f in here do pathLines := pathLines.push s!"  {site}: {fullOf f.seg}"
  logInfo s!"sites:\n{String.intercalate "\n" siteLines.toList}"
  logInfo s!"siteComps:\n{String.intercalate "\n" siteComps.toList}"
  logInfo s!"comps:\n{String.intercalate "\n" ((comps.qsort (· < ·)).map ("  " ++ ·)).toList}"
  logInfo s!"byCtor:\n{String.intercalate "\n" ((ctors.qsort (· < ·)).map ("  " ++ ·)).toList}"
  logInfo s!"shapeComps:\n{String.intercalate "\n" ((shapeComps.qsort (· < ·)).map ("  " ++ ·)).toList}"
  logInfo s!"segHops: {String.intercalate ", " segHops.toList}"
  logInfo s!"hops: {String.intercalate ", " (s.hops.map short).toList}"
  logInfo s!"new: {String.intercalate ", " newSites.toList}"
  logInfo s!"missing: {String.intercalate ", " missing.toList}"
  logInfo s!"newVsStyle: {String.intercalate ", " newVsStyle.toList}"
  logInfo s!"styleOnly: {String.intercalate ", " styleOnly.toList}"
  logInfo s!"prevStyleOff: {String.intercalate ", " prevStyleOff.toList}"
  logInfo s!"opaque: {String.intercalate ", " s.opq.toList}"
  logInfo s!"visits: {s.visits}"
  logInfo s!"reach: {String.intercalate ", " (reach.map short).toList}"
  logInfo s!"paths:\n{String.intercalate "\n" pathLines.toList}"
  -- the pins
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedSites" siteLines expectedSites
  check "expectedSiteComps" siteComps expectedSiteComps
  check "expectedComps" (comps.qsort (· < ·)) expectedComps
  check "expectedShapeComps" (shapeComps.qsort (· < ·)) expectedShapeComps
  unless prevStyleOff.isEmpty do
    throwError "item 248's reading, redone here, differs from its pinned provenance: {prevStyleOff}"
  unless got == expectedLine do
    throwError "StreamCompositions moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.StreamCompositions
