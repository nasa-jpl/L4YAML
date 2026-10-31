/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ValueLinePacks

/-!
# Where the value-line packs are born: every writer row's chain resolved to its origins, and the tail there (DOCS item 262)

Item 261 read, at each of the value-line packs' writer positions, what the
writer holds toward a `SCompactMapTail` at the level it writes, and found
the tail in hand at eleven of the sixty-nine that build, re-wrap or
transport a pack.  A re-wrap holds what its caller handed it: whether a
`none` row is a real absence depends on where its chain is BORN — the
position that first builds the pack from a route or a frames face — and on
whether the tail is in hand THERE.  This module resolves every row to its
origins.

**§0** finds the pack positions as item 261 did, by shape, and one
unfolding deeper: a parameter or field whose type carries the value closure
inside an L4YAML `Prop` definition or single-constructor `Prop` structure
(`ImplicitKeyPack`, `PropsKeyPack`) is a position too, listed `packaged`;
every position gets the PATH from its type to the closure (through the
option's arm, the existentials, the conjunctions, the guards and the
unfolding).  **§1** re-runs item 261's walk over the extended positions and,
at every row, reads the argument's BOTTOMS structurally: the hypotheses the
pack's closure is built from, navigating the term along the position's
path, through matches, casts, transports (lemmas whose conclusion carries
the stream, a frames face or a pack) and constructors.  **§2** follows each
bottom inside its lemma: a pack parameter's or park field's label is an
edge to that POSITION; a route, frames or tail hypothesis is an ORIGIN at
the row; a `let` is followed into its value; a local function's parameter
is resolved through the function's applications; a match's pattern variable
through its discriminant.  **§3** resolves positions by the least fixpoint
over the producer relation (the rows whose target is the position), so a
family whose producers are only punts and relays of each other resolves to
NOTHING: its honest arms are `unborn`.  At every origin the tail reading is
item 261's at the origin row, and for a route origin also at the route's own
level.

The pins hold the positions, the origins, every row's resolution, the
per-position summary, the unborn positions and the line.
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
open Tests.Guards.ValueLinePacks

namespace Tests.Guards.ValueLineOrigins

/-! ## §0 Packaged packs and the path to the closure -/

/-- The environment with the constants that package a value closure: every
    L4YAML `Prop` definition whose body carries it outside a `ResumeFrames`
    (`ImplicitKeyPack`, `PropsKeyPack`).  A `Prop` structure's fields are not
    unfolded: the flow base's routes (`FlowBaseRoutes`) travel in the
    flow-stack invariant, which this census does not follow. -/
structure PackEnv where
  env : Environment
  packConsts : Std.HashSet Name

-- Item 304: a stack is `ResumeFrames` or `KeyFrames` (item 302's value-line stack); `keyN` is `PuntCoverInputs`'.
def mkPackEnv (env : Environment) : PackEnv := Id.run do
  let mut s : Std.HashSet Name := {}
  for (c, ci) in env.constants.toList do
    if c.getRoot != `L4YAML || (c == resumeN || c == keyN) || c == evlN then continue
    match ci with
    | .defnInfo di => if (piConcl di.type).isProp && vcOutside di.value then s := s.insert c
    | _ => pure ()
  return { env, packConsts := s }

/-- A structure's constructor telescope with its conclusion (the structure
    itself, applied) cut to `True`, so an unfolding never re-enters it. -/
partial def cutConcl (t : Expr) : Expr :=
  match t with
  | .forallE n ty b bi => .forallE n ty (cutConcl b) bi
  | _ => mkConst ``True

/-- One unfolding of a packaging constant applied to arguments: the body the
    arguments instantiate (a structure's fields, their conclusion cut). -/
def unfoldPack (pe : PackEnv) (e : Expr) : Option Expr :=
  let e := e.consumeMData
  match e.getAppFn with
  | .const c _ =>
    if !pe.packConsts.contains c then none
    else match pe.env.find? c with
      | some (.defnInfo di) => some (di.value.beta e.getAppArgs)
      | some (.inductInfo iv) =>
        if iv.numParams ≤ e.getAppNumArgs then
          match pe.env.find? iv.ctors[0]! with
          | some (.ctorInfo cv) => Id.run do
            let mut ty := cv.type
            let args := e.getAppArgs
            for i in [0:cv.numParams] do
              match ty with
              | .forallE _ _ b _ => ty := b.instantiate1 args[i]!
              | _ => break
            return some (cutConcl ty)
          | _ => none
        else none
      | _ => none
  | _ => none

/-- The value closure, directly or inside a packaging constant, outside any
    `ResumeFrames`. -/
partial def vcDeep (pe : PackEnv) (e : Expr) : Bool :=
  let e := e.consumeMData
  if isValueClosure e || e.isAppOf evlN then true
  else if (e.isAppOf resumeN || e.isAppOf keyN) then false
  else match e with
    | .const c _ => pe.packConsts.contains c
    | .app f a => vcDeep pe f || vcDeep pe a
    | .forallE _ t b _ => vcDeep pe t || vcDeep pe b
    | .lam _ t b _ => vcDeep pe t || vcDeep pe b
    | .letE _ t v b _ => vcDeep pe t || vcDeep pe v || vcDeep pe b
    | .proj _ _ b => vcDeep pe b
    | _ => false

inductive VStep | orL | orR | ex | andL | andR | unfold | imp
  deriving BEq, Repr, Inhabited, Hashable

def VStep.render : VStep → String
  | .orL => "∨L" | .orR => "∨R" | .ex => "∃" | .andL => "∧L" | .andR => "∧R" | .unfold => "δ" | .imp => "→"

def renderVPath (p : List VStep) : String := String.intercalate "" (p.map VStep.render)

/-- The path from a position's type to its value closure: the option's arm,
    the existentials, the conjunctions (the right side first, as item 261
    read them), the closure's own binders as `→`, and an unfolding. -/
partial def vcPath (pe : PackEnv) (t : Expr) (fuel : Nat := 96) : List VStep :=
  let t := t.consumeMData
  if fuel == 0 then []
  else if isValueClosure t || t.isAppOf evlN then []
  else if t.isAppOfArity ``Or 2 then
    if vcDeep pe (t.getArg! 0) then .orL :: vcPath pe (t.getArg! 0) (fuel - 1) else .orR :: vcPath pe (t.getArg! 1) (fuel - 1)
  else if t.isAppOfArity ``Exists 2 then
    match (t.getArg! 1).consumeMData with
    | .lam _ _ b _ => .ex :: vcPath pe b (fuel - 1)
    | _ => []
  else if t.isAppOfArity ``And 2 then
    if vcDeep pe (t.getArg! 1) then .andR :: vcPath pe (t.getArg! 1) (fuel - 1) else .andL :: vcPath pe (t.getArg! 0) (fuel - 1)
  else match t with
    | .forallE _ _ b _ => .imp :: vcPath pe b (fuel - 1)
    | _ => match unfoldPack pe t with
      | some b => .unfold :: vcPath pe b (fuel - 1)
      | none => []

/-- Item 261's `peelToClosure` through packaged definitions: the stack at
    the closure, the closure, and the level binding read on the way. -/
partial def peelD (pe : PackEnv) (st : Stack) (t : Expr) (lvl : Array String) (fuel : Nat := 96) : Stack × Expr × Array String :=
  let t := t.consumeMData
  if fuel == 0 then (st, t, lvl)
  else if vcOutside t then
    let (st', cl, lvl') := peelToClosure st t #[]
    (st', cl, lvl ++ lvl')
  else if t.isAppOfArity ``Or 2 then
    if vcDeep pe (t.getArg! 0) then peelD pe st (t.getArg! 0) lvl (fuel - 1) else peelD pe st (t.getArg! 1) lvl (fuel - 1)
  else if t.isAppOfArity ``Exists 2 then
    match (t.getArg! 1).consumeMData with
    | .lam n ty b _ => peelD pe (st.push { name := n, ty, prov := none }) b (lvl.push s!"∃{bname n}") (fuel - 1)
    | _ => (st, t, lvl)
  else if t.isAppOfArity ``And 2 then
    if vcDeep pe (t.getArg! 1) then peelD pe st (t.getArg! 1) (lvl.push s!"({propTok st (t.getArg! 0)})") (fuel - 1)
    else peelD pe st (t.getArg! 0) (lvl.push s!"({propTok st (t.getArg! 1)})") (fuel - 1)
  else match t with
    | .forallE n ty b _ => peelD pe (st.push { name := n, ty, prov := none }) b (lvl.push s!"({propTok st ty})→") (fuel - 1)
    | _ => match unfoldPack pe t with
      | some b => peelD pe st b (lvl.push s!"δ{short t.getAppFn.constName!}") (fuel - 1)
      | none => (st, t, lvl)

/-- Which arm carries the closure (packaging seen through), and whether the
    other arm is `True`. -/
def sideOfD (pe : PackEnv) (t : Expr) : Bool × Bool :=
  let t := t.consumeMData
  if t.isAppOfArity ``Or 2 then
    let vcLeft := vcDeep pe (t.getArg! 0)
    let other := (if vcLeft then t.getArg! 1 else t.getArg! 0).consumeMData
    (vcLeft, (other.isConstOf ``True || other.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt || other.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG))  -- item 311: the named alternative reads as `True`
  else (true, true)

structure Position where
  key : String
  kind : String
  owner : Name
  idx : Nat
  name : Name
  path : List VStep
  vcLeft : Bool
  otherTrue : Bool
  packaged : Bool
  line : String
  deriving Inhabited

structure Cands where
  cd : PCand := {}
  positions : Array Position := #[]
  thms : Array Name := #[]

/-- A position's shape line: its level binding, premise chain and where the
    tail stands (after the value, before it, or nowhere). -/
def shapeLine (pe : PackEnv) (stk : Stack) (t : Expr) : String :=
  let (st', cl, lvl) := peelD pe stk t #[]
  let (prems, concl, tail) := premisesOf pe.env st' cl #[] false false
  let before := prems.any (·.startsWith "SCompactMapTail")
  s!"lvl={String.intercalate "" lvl.toList} premises=[{String.intercalate "," prems.toList}] ⊢ {concl} tail={if tail then "after" else if before then "before" else "no"}"

def mkPosition (pe : PackEnv) (kind : String) (owner : Name) (idx : Nat) (n : Name) (stk : Stack) (t : Expr) : Position :=
  let (vcLeft, otherTrue) := sideOfD pe t
  let packaged := !vcOutside t
  let path := vcPath pe t
  let key := s!"{kind}:{short owner}.{n}"
  { key, kind, owner, idx, name := n, path, vcLeft, otherTrue, packaged,
    line := s!"{key}{if packaged then " packaged" else ""} arm={if vcLeft then "l" else "r"}{if otherTrue then "" else "/stamp"} path={renderVPath path} {shapeLine pe stk t}" }

/-- The positions: the park fields and the lemma parameters that carry the
    value closure, directly or packaged. -/
def collect (pe : PackEnv) : MetaM Cands := do
  let env := pe.env
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cs : Cands := {}
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
          if vcDeep pe t then
            let p := mkPosition pe "ctor" c i n stk t
            packs := packs.push (i, n, p.vcLeft, p.otherTrue)
            cs := { cs with positions := cs.positions.push p }
        stk := stk.push { name := n, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    cs := { cs with cd := { cs.cd with ctors := cs.cd.ctors.insert c, fieldNames := cs.cd.fieldNames.insert c names, packs := cs.cd.packs.insert c packs, consts := cs.cd.consts.insert c } }
  cs := { cs with cd := { cs.cd with consts := cs.cd.consts.insert ``PendingNode.casesOn } }
  let mut paramPos : Array Position := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    unless ci matches .thmInfo _ do continue
    cs := { cs with thms := cs.thms.push n }
    let mut ty := ci.type
    let mut i := 0
    let mut stk : Stack := #[]
    let mut ps : Array Pos := #[]
    while true do
      match ty with
      | .forallE pn t b _ =>
        if vcDeep pe t then
          let p := mkPosition pe "param" n i pn stk t
          ps := ps.push (i, pn, p.vcLeft, p.otherTrue)
          paramPos := paramPos.push p
        stk := stk.push { name := pn, ty := t, prov := none }
        ty := b; i := i + 1
      | _ => break
    if !ps.isEmpty then cs := { cs with cd := { cs.cd with lemParams := cs.cd.lemParams.insert n ps, consts := cs.cd.consts.insert n } }
  paramPos := paramPos.qsort (·.key < ·.key)
  return { cs with positions := cs.positions ++ paramPos }

/-! ## §1 The bottoms of a pack argument -/

/-- A hypothesis the pack's closure bottoms in (with the stack it stands
    in, the arguments it is applied to and the path left to the closure), or
    a terminal. -/
inductive Bot
  | bind (b : Bind) (depth : Nat) (st : Stack) (args : Array Expr) (rest : List VStep)
  | term (s : String)
  deriving Inhabited

def isPuntTerm (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isConstOf ``trivial || e.isConstOf ``True.intro

/-- The name of the `j`-th leading lambda binder. -/
partial def lamName (e : Expr) (j : Nat) : Option Name :=
  match e.consumeMData with
  | .lam n _ b _ => if j == 0 then some n else lamName b (j - 1)
  | _ => none

/-- The type of the `j`-th leading lambda binder. -/
partial def lamTy (e : Expr) (j : Nat) : Option Expr :=
  match e.consumeMData with
  | .lam _ t b _ => if j == 0 then some t else lamTy b (j - 1)
  | _ => none

/-- The kind of a hypothesis, packaging seen through. -/
def kindOf (pe : PackEnv) (b : Bind) : String :=
  if vcDeep pe b.ty then "chain" else bindKind (some b)

/-- The level named by the first surface premise of a hypothesis. -/
partial def lvlOf (env : Environment) (st : Stack) (t : Expr) : Option String :=
  let t := t.consumeMData
  let own : Option String := match t.getAppFn with
    | .const h _ => if (`L4YAML.Surface).isPrefixOf h && t.getAppNumArgs ≥ 1 && levelFirst env h then some (ppc st (t.getArg! 0)) else none
    | _ => none
  match t with
  | .forallE n ty b _ =>
    (lvlOf env st ty).orElse fun _ => lvlOf env (st.push { name := n, ty, prov := none }) b
  | .app .. =>
    if t.isAppOfArity ``Or 2 || t.isAppOfArity ``And 2 || t.isAppOfArity ``Exists 2 then
      t.getAppArgs.findSome? fun a => lvlOf env st a
    else own
  | .lam n ty b _ => lvlOf env (st.push { name := n, ty, prov := none }) b
  | _ => none

/-- A lemma whose conclusion carries the stream, a frames face or a pack, or
    a predicate it is polymorphic in (`frameChainOne`'s `P x`): one a pack's
    closure can be built through. -/
def isTransport (pe : PackEnv) (m : Name) : Bool :=
  match pe.env.find? m with
  | some (.thmInfo ti) =>
    let c := piConcl ti.type
    hasHead c streamN || (hasHead c resumeN || hasHead c keyN) || vcDeep pe c || (c.find? fun s => s.isApp && s.getAppFn.isBVar).isSome
  | _ => false

-- Keyed by the whole stack, not its depth: a depth-keyed hit from another binder context returned
-- that context's bottoms (item 349 — `question_open_map`'s `h_resV_land` frames origin vanished).
def stackKey (st : Stack) : Array (Name × Option String) := st.map fun b => (b.name, b.prov)

abbrev BMemo := IO.Ref (Std.HashMap (Expr × Array (Name × Option String) × List VStep) (Array Bot))

/-- The matches the bottoms reader enters (their alternative binders are
    labeled from the discriminants), for the follower to resolve. -/
abbrev DynAlts := IO.Ref (Array AltRec)

/-- A visit budget per row: the reader stops with a `budget` terminal past it. -/
abbrev Budget := IO.Ref Nat


/-- Every hypothesis the argument's closure is built from, navigating the
    term along the position's path. -/
partial def bottomsOf (pe : PackEnv) (memo : BMemo) (budget : Budget) (dyn : DynAlts) (st : Stack) (e : Expr) (path : List VStep) (fuel : Nat := 40) : MetaM (Array Bot) := do
  if fuel == 0 then return #[.term "fuel"]
  if (← budget.get) == 0 then return #[.term "budget"]
  budget.modify (· - 1)
  let e := peelSafe e
  if let some r := (← memo.get)[(e, stackKey st, path)]? then return r
  let r ← go e
  memo.modify (·.insert (e, stackKey st, path) r)
  return r
where
  go (e : Expr) : MetaM (Array Bot) := do
  let env := pe.env
  match e with
  | .lam n t b _ =>
    let path' := match path with | .imp :: r => r | p => p
    bottomsOf pe memo budget dyn (st.push { name := n, ty := t, prov := none }) b path' fuel
  | .bvar i =>
    if i < st.size then return #[.bind st[st.size - 1 - i]! (st.size - 1 - i) st #[] path] else return #[.term "#?"]
  | .const c _ => if isPuntTerm e then return #[.term "punt"] else return #[.term s!"?{short c}"]
  | .proj _ _ b => bottomsOf pe memo budget dyn st b path (fuel - 1)
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .bvar i =>
      if i < st.size then return #[.bind st[st.size - 1 - i]! (st.size - 1 - i) st args path] else return #[.term "#?"]
    | .const c _ =>
      if let some (_, discrs, brs) ← branchesOf c args then
        dyn.modify (·.push { lem := .anonymous, st, discrs })
        let lab ← altLabeler st discrs
        let mut out : Array Bot := #[]
        for b in brs do
          let (st', body) := enterAllF st lab args[b]!
          out := out ++ (← bottomsOf pe memo budget dyn st' body path (fuel - 1))
        return out
      if deadEnd c then return #[.term "absurd"]
      let other (x : Expr) : Array Bot := #[.term (if isPuntTerm x then "punt" else "stamp")]
      if c == ``Or.inl && args.size ≥ 3 then
        match path with
        | .orL :: r => return ← bottomsOf pe memo budget dyn st args[2]! r (fuel - 1)
        | .orR :: _ => return other args[2]!
        | _ => return ← bottomsOf pe memo budget dyn st args[2]! path (fuel - 1)
      if c == ``Or.inr && args.size ≥ 3 then
        match path with
        | .orR :: r => return ← bottomsOf pe memo budget dyn st args[2]! r (fuel - 1)
        | .orL :: _ => return other args[2]!
        | _ => return ← bottomsOf pe memo budget dyn st args[2]! path (fuel - 1)
      if c == ``Exists.intro && args.size ≥ 4 then
        let r := match path with | .ex :: r => r | p => p
        return ← bottomsOf pe memo budget dyn st args[3]! r (fuel - 1)
      if c == ``And.intro && args.size ≥ 4 then
        match path with
        | .andL :: r => return ← bottomsOf pe memo budget dyn st args[2]! r (fuel - 1)
        | .andR :: r => return ← bottomsOf pe memo budget dyn st args[3]! r (fuel - 1)
        | _ => return ← bottomsOf pe memo budget dyn st args[3]! path (fuel - 1)
      if c == ``Or.imp && args.size ≥ 7 then return ← bottomsOf pe memo budget dyn st args[6]! path (fuel - 1)
      if (c == ``Or.imp_left || c == ``Or.imp_right) && args.size ≥ 5 then return ← bottomsOf pe memo budget dyn st args[4]! path (fuel - 1)
      if (c == ``And.left || c == ``And.right) && args.size ≥ 3 then return ← bottomsOf pe memo budget dyn st args[2]! path (fuel - 1)
      if (← getProjectionFnInfo? c).isSome && args.size ≥ 1 then return ← bottomsOf pe memo budget dyn st args[args.size - 1]! path (fuel - 1)
      if c.getRoot == `L4YAML && (isTransport pe c || (isCtorN env c && !(`L4YAML.Surface).isPrefixOf c)) then
        let mut out : Array Bot := #[]
        for a in args do
          let a' := peelSafe a
          let cand := match a' with
            | .lam .. => !isPredLam a'
            | .bvar .. => (match bindOf st a' with
                | some b => !isDataTy b.ty && (kindOf pe b != "other" || hasHead b.ty streamN || (hasHead b.ty resumeN || hasHead b.ty keyN) || hasHead b.ty tailN)
                | none => false)
            | .app .. => (match a'.getAppFn with
                | .bvar _ => true
                | .const m _ => (m.getRoot == `L4YAML && (isTransport pe m || (isCtorN env m && !(`L4YAML.Surface).isPrefixOf m))) || m == ``Or.inl || m == ``Or.inr ||
                    m == ``Exists.intro || m == ``And.intro || m == ``And.left || m == ``And.right || m == ``Or.imp ||
                    (Lean.Meta.Match.Extension.getMatcherInfo? env m).isSome || isCasesOnRecursor env m ||
                    m == ``dite || m == ``ite || m == ``Or.elim || m == ``Exists.elim || m == ``Or.rec || m == ``Decidable.byCases
                | _ => false)
            | .proj .. => true
            | _ => false
          if cand then out := out ++ (← bottomsOf pe memo budget dyn st a' [] (fuel - 1))
        let live := out.filter fun
          | .term s => !(s == "absurd" || s == "punt" || s == "stamp" || s.startsWith "?" || s == "#?")
          | _ => true
        if live.isEmpty then return #[.term s!"{if isCtorN env c then "ctor" else "concl"}:{short c}"]
        return live
      -- a lemma whose conclusion carries no stream and no pack proves a side
      -- fact (a guard, a scanner predicate): not a source
      if c.getRoot == `L4YAML && isThmN env c then return #[.term s!"fact:{short c}"]
      return #[.term s!"?{short c}"]
    | _ => return #[.term "?"]
  | _ => return #[.term "?"]

/-! ## §2 Following a bottom inside its lemma -/

/-- Where a bottom leads: a position (another producer's row set), an
    origin at this row, a dead end the follower cannot read, or nothing
    (a punt, a stamp, an absurd branch). -/
inductive Src
  | pos (key : String)
  | origin (kind : String) (label : String) (lvl : Option String)
  | dead (why : String)
  /-- No source: a punt, a stamp, an absurd branch, a side fact. -/
  | none (why : String)
  deriving Inhabited, BEq

abbrev FMemo := IO.Ref (Std.HashMap (Name × Nat × String × List VStep × Array Expr) (Array Src))

structure FCx where
  pe : PackEnv
  memo : BMemo
  budget : Budget
  dyn : DynAlts
  fmemo : FMemo
  lem : Name
  posKeys : Std.HashSet String
  lets : Array LetRec
  lapps : Array LApp
  alts : Array AltRec

def dedupSrc (xs : Array Src) : Array Src := xs.foldl (fun acc x => if acc.contains x then acc else acc.push x) #[]

mutual
partial def followBot (cx : FCx) (bot : Bot) (fuel : Nat := 8) : MetaM (Array Src) := do
  match bot with
  | .term s =>
    if s == "punt" || s == "stamp" || s == "absurd" then return #[.none s]
    if s.startsWith "fact:" then return #[.none "fact"]
    if s.startsWith "concl:" || s.startsWith "ctor:" then return #[.origin "concl" s none]
    return #[.dead s]
  | .bind b depth st args rest =>
    let key := (cx.lem, depth, b.prov.getD "", rest, args)
    if let some r := (← cx.fmemo.get)[key]? then return r
    let r ← followBind cx b depth st args rest fuel
    let r := dedupSrc r
    cx.fmemo.modify (·.insert key r)
    return r

partial def followBind (cx : FCx) (b : Bind) (depth : Nat) (st : Stack) (args : Array Expr) (rest : List VStep) (fuel : Nat) : MetaM (Array Src) := do
    let kind := kindOf cx.pe b
    let lvl := lvlOf cx.pe.env (st.extract 0 depth) b.ty
    -- a relational invariant (an L4YAML inductive: the flow stack's interior,
    -- a pending node) is an origin of its own kind; a side fact (a column,
    -- an equation, a scanner predicate) is not a source
    let invHead : Option Name := match (piConcl b.ty).getAppFn with
      | .const h _ => (match cx.pe.env.find? h with
        | some (.inductInfo _) => if h.getRoot == `L4YAML && !(`L4YAML.Surface).isPrefixOf h then some h else none
        | _ => none)
      | _ => none
    if kind == "other" && !(hasHead b.ty streamN || (hasHead b.ty resumeN || hasHead b.ty keyN) || hasHead b.ty tailN || vcDeep cx.pe b.ty) then
      if let some h := invHead then return #[.origin "invariant" s!"{short h}@{b.prov.getD (bname b.name)}" lvl]
      return #[.none "fact"]
    match b.prov with
    | none => return #[.dead s!"own:{bname b.name}"]
    | some p =>
      if fuel == 0 then return #[.dead s!"fuel@{p}"]
      if p.startsWith "param:" then
        if kind == "chain" && cx.posKeys.contains p then return #[.pos p] else return #[.origin kind p lvl]
      if p.startsWith "door:" then
        let key := "ctor:" ++ (p.drop 5).toString
        if kind == "chain" && cx.posKeys.contains key then return #[.pos key] else return #[.origin kind p lvl]
      if p.startsWith "let:" then
        let ls := cx.lets.filter fun l => l.label == p
        if ls.isEmpty then return #[.dead s!"let?{p}"]
        let mut out : Array Src := #[]
        for l in ls do out := out ++ (← followLet cx l st args (fuel - 1))
        return out
      if p.startsWith "λ:" then
        let mut out : Array Src := #[]
        let mut found := false
        for l in cx.lets do
          unless l.st.size ≤ depth do continue
          let j := depth - l.st.size
          if lamName l.val j == some b.name then
            found := true
            let path := match lamTy l.val j with | some t => vcPath cx.pe t | none => rest
            for a in cx.lapps do
              unless a.head.name == l.name && a.head.prov == some l.label do continue
              if j < a.args.size then
                for bt in (← bottomsOf cx.pe cx.memo cx.budget cx.dyn a.st a.args[j]! path) do out := out ++ (← followBot cx bt (fuel - 1))
              else out := out.push (.dead s!"{p} partial")
        if found then return out else return #[.dead p]
      let mut out : Array Src := #[]
      let mut found := false
      for a in cx.alts ++ (← cx.dyn.get) do
        unless a.st.size ≤ depth do continue
        for d in a.discrs do
          if (← sourceOf a.st d) == some p then
            found := true
            -- a discriminant that is itself a lemma's conclusion: the pack
            -- is built by that lemma, an origin here
            if p.startsWith "ret:" && !(d.consumeMData.isBVar) then
              let bots ← bottomsOf cx.pe cx.memo cx.budget cx.dyn a.st d rest
              let live := bots.filter fun | .term t => !(t.startsWith "?") | _ => true
              if live.isEmpty then out := out.push (.origin "concl" p lvl)
              else for bt in live do out := out ++ (← followBot cx bt (fuel - 1))
            else
              let path := match bindOf a.st d with | some db => vcPath cx.pe db.ty | none => rest
              for bt in (← bottomsOf cx.pe cx.memo cx.budget cx.dyn a.st d path) do out := out ++ (← followBot cx bt (fuel - 1))
      if found then return out
      if p.startsWith "ret:" then return #[.origin "concl" p lvl]
      return #[.dead p]

/-- Into a `let`'s value: its bottoms, a local function's parameters
    mapped to the arguments at the application the bottom came from. -/
partial def followLet (cx : FCx) (l : LetRec) (appSt : Stack) (args : Array Expr) (fuel : Nat) : MetaM (Array Src) := do
  let bots ← bottomsOf cx.pe cx.memo cx.budget cx.dyn l.st l.val (vcPath cx.pe l.ty)
  let mut out : Array Src := #[]
  for bt in bots do
    match bt with
    | .bind b d _ _ _ =>
      if b.prov.isNone && d ≥ l.st.size && d - l.st.size < args.size then
        let path := match lamTy l.val (d - l.st.size) with | some t => vcPath cx.pe t | none => []
        for b2 in (← bottomsOf cx.pe cx.memo cx.budget cx.dyn appSt args[d - l.st.size]! path) do out := out ++ (← followBot cx b2 (fuel - 1))
      else out := out ++ (← followBot cx bt (fuel - 1))
    | _ => out := out ++ (← followBot cx bt (fuel - 1))
  return out
end

/-! ## §3 The pins -/

def pinned : Bool := true
-- 2026-10-20 (item 309): the two generic premises (`explFrameValueLine.h_kslot`, `flowVPack_of_close.h_vslot`)
-- read `arm=l/stamp` — a right disjunct other than `True`, here the generic alternative `alt`.
-- 2026-10-24 (item 350): `h_explUp`'s alternative reads as the stamp `NotQuestionPark sc` (was `PackAlt`).
  -- Item 288: the field's other disjunct is the stamp, not `True`.
  -- Item 287: `h_vslot`'s other disjunct is not `True` (`ValueLinePacks`' `/stamp`).
  -- item 311: `colon_open_map_implicit` states the alternative generically (`{alt : Prop}`), so its premise reads
  -- `arm=l/stamp` (a right disjunct other than `True`), as the three generic helpers do since item 309.
  -- Item 288: the field's other disjunct is the stamp, not `True`.
  -- Item 287: `h_vslot`'s other disjunct is not `True` (`ValueLinePacks`' `/stamp`).
  -- item 311: `colon_open_map_implicit` states the alternative generically (`{alt : Prop}`), so its premise reads
  -- `arm=l/stamp` (a right disjunct other than `True`), as the three generic helpers do since item 309.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-30 (item 405): the `?`-park field, its content twin and `h_explUp` read the head-form chain / the `MarkedColsIn` conjunct (ruling "405 a").
-- 2026-10-30 (item 405, Rule 8 fix): the five `h_kslot` positions read `path=∨L→…` / `lvl=∀nv∈markedCols(…)` — the chain re-indexed by the projection, no `∃∃∧`.
-- 2026-10-30 (item 408): `flowKeyPack_of_close.h_key` / `flowKeyRoute_of_open.h_compact_pair` paths lose their `∃`
-- — the value-line pair is `∀ nv ∈ markedCols _, …`, a scanner-state projection (Rule 8), no binder.
def expectedPositions : List String :=
  ["ctor:pendingMapValue.h_ivl arm=r/stamp path=∨R∧R lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
   "ctor:pendingContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(Or)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "ctor:pendingProps.h_key packaged arm=l/stamp path=∨Lδ∧L∃∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=δPropsKeyPack(And)∃k(?)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "ctor:pendingBlockContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(Or)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:accum_block_on_pendingBlockContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(Or)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:accum_block_on_pendingContent.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(Or)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:colon_fires_implicit_key.h_key packaged arm=l path=→→∨Lδ∃∃∃∧R∧R∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=(possible(…)=true)→(line(…)=line(…))→δImplicitKeyPack∃k∃sp_key∃sp_gram(Or)(ImplicitKeyHead)(GStar)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:colon_fires_props_key.h_key packaged arm=l/stamp path=∨Lδ∧L∃∧R∧R∧L∨L∃∧R→→→→→→→→→→ lvl=δPropsKeyPack(And)∃k(?)(col(…)=k)(And)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:entryKeyPack_of_dispatch.h_compact arm=l path=∨L∧R∧R∨L∃∧R→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:entryKeyPack_of_dispatch.h_ivl arm=r/stamp path=∨R∧R∧R∨L∃∧R→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:entryKeyPack_of_dispatch.h_nodeV arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:entryPropsKeyPack_of_dispatch.h_compact arm=l path=∨L∧R∧R∨L∃∧R→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:entryPropsKeyPack_of_dispatch.h_ivl arm=r/stamp path=∨R∧R∧R∨L∃∧R→→→→→→→→ lvl=(?)(sp_scan.col=n + 1)∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:entryPropsKeyPack_of_dispatch.h_nodeV arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
    "ctor:pendingMapValue.h_vslot arm=l/stamp path=∨L∧R∧R lvl=(sc.currentIndent≤n)(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
    "param:accum_content_on_pendingMapValue_indented.h_ivl_mv arm=r/stamp path=∨R∧R lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
    "param:accum_content_on_pendingMapValue_indented.h_vslot arm=l path=∨L∧R lvl=(sp_scan.col=n + 1) premises=[SBlockIndented(n)] ⊢ SLYamlStream tail=no",
    "param:entryChainMap.up arm=l path=→→→→→→ lvl=∀nvX∈ns premises=[SBlockIndented(n),SCompactSeqTail(n)] ⊢ ExplValueLine(nvX) tail=no",
    "param:slotChainMap.up arm=l path=→→→→ lvl=∀nvX∈ns premises=[SBlockIndented(nv)] ⊢ ExplValueLine(nvX) tail=no",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   -- Item 372 (2026-10-27): the pack's route conjunct is now an Or (`∨ SeqTopKey sc`), so its head reads `(Or)`.
   "ctor:pendingContent.h_vpack arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingProps.h_kslot arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingProps.h_kslotE arm=l path=∨L∃∃∧R→→→→→→→→ lvl=∃ne∃nv(n=ne + 1) premises=[SBlockNode(n),SCompactSeqTail(ne),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingBlockContent.h_kslot arm=l path=∨L→→→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingBlockContent.h_kslotUp arm=l path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingBlock.h_kslot arm=l path=∨L→→→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingBlock.h_kslotUp arm=l path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingMapValue.h_kslot arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "ctor:pendingMapValue.h_explUp arm=l/stamp path=∨L∃∃∧R∧R→→→→→→→→ lvl=∃sp_q∃ns(GLit('?'))(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_closeThenBlock.h_vpack arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_closeThenBlock.h_vslot arm=l/stamp path=∨L∃∃∧R∧R∧R∧R∧R∧R∧R∧R∨L∃∧R→→→→→→→→ lvl=∃nv∃sp_a(SLYamlStream(sp_start))(sc.currentIndent≤nv)(needIndentCheck(…)=false)(simpleKeyAllowed(…)=true)(sp_gram=sp_scan)(sp_scan.col=nv + 1)(?)(Or)∃nsU(MarkedColsIn)∀nvU∈nsU premises=[SBlockIndented(nv),SIndent(nvU),GLit(':'),SBlockIndented(nvU)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_pendingBlock.h_kslot arm=l path=∨L→→→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_pendingBlock.h_kslotUp arm=l path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_pendingBlockContent.h_kslot arm=l path=∨L→→→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_pendingBlockContent.h_kslotUp arm=l path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SSLComments,SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_block_on_pendingContent.h_vpack arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_content_on_pendingBlock_indented.h_kslotUp_old arm=l path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_content_on_pendingBlock_indented.h_kslot_old arm=l path=∨L→→→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SCompactSeqTail(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:accum_content_on_pendingMapValue_indented.h_kslot arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockNode(n + 1),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:colon_open_map_explicit.hvp arm=l path=→→→→→→ lvl= premises=[SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   -- Item 409 (2026-10-30): `explFrameValueLine` deleted — its position and three writer rows are gone; the two
   -- `:` consumers' `h_kslotD` positions are PAID from the pack (rows below re-read by the build).
   "param:colon_open_map_implicit.h_kslotD arm=l/stamp path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:colon_open_map_props.h_kslotD arm=l path=∨L∃∧R→→→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:flowKeyPack_of_close.h_key arm=l path=∨L∃∃∧R∧R∧R∧L∨L→→→→→→→→→→ lvl=∃k∃sp_key(?)(?)(kc=k)(And)∀nv∈markedCols(…) premises=[SBlockMapEntry(k),SCompactMapTail(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=before",
   "param:flowKeyRoute_of_open.h_compact_pair arm=l path=∨L→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SBlockIndented(nc),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:flowVPack_of_close.h_vslot arm=l/stamp path=∨L∃→→→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SFlowContent(n),SSLComments,SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:indicator_open_map.h_explUp_chain arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:indicator_open_map.h_explUp_chainD arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:question_open_map.h_explUp_chain arm=l path=∨L∃→→→→→→→→ lvl=∃ns∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
   "param:question_open_map.h_explUp_chainD arm=l path=∨L∃∧R→→→→→→→→ lvl=∃ns(MarkedColsIn)∀nv∈ns premises=[SBlockMapEntry(k),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  -- 2026-10-31 (item 412): the entry-shaped `pendingMapValue.h_expl` — the chain one frame up sits inside the `?` arm
  -- (`∨L ∃ ∧R ∧R ∨L`), projected on `markedCols sc` minus the own mark; and its consumer param twin.
  "ctor:pendingMapValue.h_expl arm=l/stamp path=∨L∃∧R∧R∨L→→→→→→→→→ lvl=∃sp_q(GLit('?'))(?)∀nv∈markedCols(…) premises=[Ne,SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  "param:accum_content_on_pendingMapValue_indented.h_expl arm=l/stamp path=∨L∃∧R∧R∨L→→→→→→→→→ lvl=∃sp_q(GLit('?'))(?)∀nv∈markedCols(…) premises=[Ne,SBlockMapEntry(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no",
  -- Item 413: compact_open_map.h_chainUp — the opener's relay parameter (the `-` / slot park's chain over the entry's content).
  "param:compact_open_map.h_chainUp arm=l path=∨L→→→→→→→→ lvl=∀nv∈markedCols(…) premises=[SBlockIndented(n),SIndent(nv),GLit(':'),SBlockIndented(nv)] ⊢ ResumeFrames tail=no"]
-- 2026-10-20 (item 306): 70 → 73 — three origins more, all in `accum_content_on_pendingBlock_indented`:
-- the two key-pack builders' `h_nodeFV`/`h_dframesV` are now built from the entry park's
-- `h_closeFV_old` (frames origin) where item 108 left punts; the rows after them renumber.
-- 2026-10-20 (item 307): 73 → 76 — the three γ roots' `h_vpack` are origins now (two `frames(h_closeFV_old)`,
-- one `step(h_mapFV108)`), each at its `accum_block_on_closeThenBlock.h_vpack` position; the rows after them renumber.
-- 2026-10-20 (item 307, second chain): the content route's `h_vpack` origin reads `⊢ none` under the `match` form.
-- 2026-10-30 (item 405): origins follow `expectedPositions` (head-form chain; `closeThenBlock` births `hkv`+`hkvUp`; declines of ruling "405 a").
-- 2026-10-30 (item 408): rows 67 → 66 — O44 (`accum_flow_open_depth0 #3`'s `h_compact_pair` ← tail(`pendingMapValue.h_expl`))
-- is gone: the `?` entry's singleton pair is DECLINED under the projection face; O45…O66 renumber by one.
def expectedOrigins : List String := [
   -- Item 409 (2026-10-30): origins renumbered after `explFrameValueLine`'s rows left (66 → 54).
  "O0 accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vpack ← frames(param:accum_block_on_pendingBlock.h_closeFV_old) lvl=n ⊢ none | @n:none → unheld",
  "O1 accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vpack ← frames(param:accum_block_on_pendingBlockContent.h_closeFV_old) lvl=n ⊢ none | @n:none → unheld",
  "O2 accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vpack ← frames(param:accum_block_on_pendingContent.h_mapFV108) lvl=— ⊢ none → unheld",
  "O4 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_old) lvl=n ⊢ none | @n:none → unheld",
  "O5 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeF_old) lvl=n ⊢ none | @n:none → unheld",
  "O6 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeFV_old) lvl=n ⊢ none | @n:none → unheld",
  "O7 accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_entry_old) lvl=n ⊢ none | @n:none → unheld",
  "O8 accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_old) lvl=n ⊢ none | @n:none → unheld",
  "O9 accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeF_old) lvl=n ⊢ none | @n:none → unheld",
  "O10 accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeFV_old) lvl=n ⊢ none | @n:none → unheld",
  "O11 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_old) lvl=n ⊢ none | @n:none → unheld",
  "O12 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeF_old) lvl=n ⊢ none | @n:none → unheld",
  "O13 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← frames(param:accum_content_on_pendingBlock_indented.h_closeFV_old) lvl=n ⊢ none | @n:none → unheld",
  "O14 accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key ← route(param:accum_content_on_pendingBlock_indented.h_close_entry_old) lvl=n ⊢ none | @n:none → unheld",
  "O15 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← route(param:accum_content_on_pendingMapValue_indented.h_close_old) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "O3 accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vpack ← tail(door:pendingMapValue.h_expl) lvl=nmv ⊢ held(h_expl51,h_seqF✝) | @nmv:held(h_expl51,h_seqF✝) → held",
  -- 2026-10-31 (item 412): origins renumbered past the two new `h_expl` positions; the entry-shaped chain's
  -- consumer origins (frames and tails read through the park's own entry) are the net +9.
  "O16 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n:held(h_expl,h_seqF168) → unheld",
  "O17 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeF99) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O18 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_frames99) lvl=— ⊢ held(h_frames99,h_closeFV108,h_framesV108) → unheld",
  "O19 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeFV108) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O20 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_framesV108) lvl=— ⊢ held(h_frames99,h_closeFV108,h_framesV108) → unheld",
  "O21 accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_seqF168) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O22 accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_compact ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_expl,h_seqF168) → unheld",
  "O23 accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_ivl ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_expl,h_seqF168) → unheld",
  "O24 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← route(param:accum_content_on_pendingMapValue_indented.h_close_old) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O25 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n:held(h_expl,h_seqF168) → unheld",
  "O26 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeF99) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O27 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_frames99) lvl=— ⊢ held(h_frames99,h_closeFV108,h_framesV108) → unheld",
  "O28 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeFV108) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O29 accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_framesV108) lvl=— ⊢ held(h_frames99,h_closeFV108,h_framesV108) → unheld",
  "O30 accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_expl,h_seqF168) → unheld",
  "O31 accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_expl,h_seqF168) → unheld",
  "O32 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← route(param:accum_content_on_pendingMapValue_indented.h_close_old) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O33 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n:held(h_expl,h_seqF168) → unheld",
  "O34 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeF99) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O35 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_frames99) lvl=— ⊢ held(h_frames99,h_closeFV108,h_framesV108) → unheld",
  "O36 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_closeFV108) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O37 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_framesV108) lvl=— ⊢ held(h_frames99,h_closeFV108,h_framesV108) → unheld",
  "O38 accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key ← frames(param:accum_content_on_pendingMapValue_indented.h_seqF168) lvl=n + 1 ⊢ held(h_frames99,h_closeFV108,h_framesV108) | @n + 1:none → unheld",
  "O39 accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_compact ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_expl,h_seqF168) → unheld",
  "O40 accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_ivl ← tail(param:accum_content_on_pendingMapValue_indented.h_expl) lvl=n ⊢ level-var | @n:held(h_expl,h_seqF168) → unheld",
  "O41 accum_step_flow #1 ctor:pendingContent.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O42 accum_step_flow #1 param:flowKeyPack_of_close.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O43 accum_step_flow #2 ctor:pendingContent.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O44 accum_step_flow #2 param:flowKeyPack_of_close.h_key ← invariant(FlowBaseRoutes@let:h_tuple<let:h_gap(tl,h_gap)) lvl=— ⊢ level-var → unheld",
  "O45 compact_open_map #1 ctor:pendingMapValue.h_ivl ← route(param:compact_open_map.h_close_old) lvl=n ⊢ held(h_expl105) | @n:none → unheld",
  "O46 compact_open_map #1 ctor:pendingMapValue.h_vslot ← route(param:compact_open_map.h_close_old) lvl=n ⊢ held(h_expl105) | @n:none → unheld",
  "O47 content_dispatch_routed #1 ctor:pendingContent.h_key ← frames(param:content_dispatch_routed.h_resumectx) lvl=k ⊢ level-var | @k:none → unheld",
  "O48 content_dispatch_routed #2 ctor:pendingContent.h_key ← frames(param:content_dispatch_routed.h_resumectx) lvl=k ⊢ level-var | @k:none → unheld",
  "O49 question_open_map #1 ctor:pendingMapValue.h_ivl ← frames(param:question_open_map.h_nodoc_land) lvl=k ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O50 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:suffixMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O51 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:nodocMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O52 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:markerMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O53 question_open_map #1 ctor:pendingMapValue.h_ivl ← concl(concl:propsMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O54 question_open_map #1 ctor:pendingMapValue.h_ivl ← route(param:question_open_map.h_stream_land) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O55 question_open_map #1 ctor:pendingMapValue.h_vslot ← frames(param:question_open_map.h_nodoc_land) lvl=k ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O56 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:suffixMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O57 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:nodocMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O58 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:markerMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O59 question_open_map #1 ctor:pendingMapValue.h_vslot ← concl(concl:propsMapRoute) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O60 question_open_map #1 ctor:pendingMapValue.h_vslot ← route(param:question_open_map.h_stream_land) lvl=— ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O61 question_open_map #1 ctor:pendingMapValue.h_kslot ← frames(param:question_open_map.h_res_land) lvl=k ⊢ held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → held",
  "O62 question_open_map #1 ctor:pendingMapValue.h_explUp ← frames(param:question_open_map.h_explUp_chainD) lvl=k ⊢ none | @k:held(h_res_land,h_resV_land,h✝,right✝,h_routeF,h_route51F) → unheld"]
-- Item 287: the eleven writers of `accum_block_on_closeThenBlock.h_vslot`, read
-- as `ValueLinePacks.expectedWriters` reads them — the ten `punt`s are `stamp`s,
-- and the value park's split writes both.  Item 288: the four writers of
-- `pendingMapValue.h_vslot`'s decline write the stamp — three flat, and
-- `compact_open_map`'s `:` branch inside its relay.
-- 2026-10-20 (item 306): the rows citing the renumbered origins (O69 → O72 and the
-- rows after the three new `frames(h_closeFV_old)` origins O3/O7/O10) re-read; the six
-- key-pack stack rows of `accum_content_on_pendingBlock_indented` are built, not punted.
-- 2026-10-20 (item 307): the rows re-read with the three new origins and the renumbering; the three γ roots'
-- `h_vpack` rows are built (`paid:frames`, `step`) where item 301 read punts, and `closeThenBlock`'s `h_kslot` is an alternation.
-- 2026-10-20 (item 307, second chain): re-read with the `match` forms.
-- 2026-10-21 (item 313): the props parks' `h_kslot`/`h_kslotE` and the mapping value's `h_kslot` are written `step/built`
-- (through `PackAlt.step_content`) where the census read `relay/built` or `via/built`; origins and holdings unchanged.
-- 2026-10-21 (item 314): 39 rows of the content lemmas re-read — the declining arm of each `match` hands the
-- alternative on (through `PackAlt.step_content`/`step_dispatch` or verbatim), so `none=[punt]` leaves the row and a `via`
-- reads as a `step`; origins and holdings unchanged.
-- 2026-10-21 (item 318): one row re-read — `accum_block_on_pendingBlock`'s `h_kslot` at the sibling `-` (`#1`) reads
-- `none=[stamp]` where it read `none=[punt]`: the declining arm hands the park's alternative through
-- `PackAlt.step_blockEntry` (the block lane's transport, item 319's consumer probe) instead of punting with `trivial`.
-- 2026-10-21 (item 319): 19 rows re-read — the block lane's paid arms hand the park's alternative on (`stamp` or a
-- `step` through `PackAlt.step_blockEntry`) where they punted with `trivial`; regenerated from the census's own rows.
-- 2026-10-21 (item 320): 3 rows re-read — the marker arms' premises pay through `PackAlt.ofRefused h_noek…` (a `fact`
-- reading) where they punted, and `accum_block_on_closeThenBlock`'s `h_seqFramesV` steps through the transport; regenerated
-- from the census's own rows.
-- 2026-10-21 (item 321): 6 rows re-read — `accum_block_on_noPending`'s fresh fields read a fact (its own `h_noek`,
-- through `PackAlt.step_blockEntry`) where they punted, and `colon_open_map_props`'s leaves step through `PackAlt.step_value`;
-- regenerated from the census's own rows.
-- 2026-10-21 (item 322): 2 rows re-read — the colon openers' leaves hand the alternative on through the step premise
-- (`h_alt_step h_alt`, which this census reads as a stamped transport) where they punted; regenerated from the census's own rows.
-- 2026-10-21 (item 324): 3 rows re-read — `accum_flow_open_depth0`'s three `flowKeyRoute_of_open.h_compact_pair` supplies:
-- the `---` arm (`#1`) pays through `PackAlt.ofRefused h_noekS` and the `pendingBlock`/`pendingMapValue` arms (`#2`/`#3`)
-- hand the park's alternative on (`Or.inr h_alt`), each read `none=[stamp]` where it punted; regenerated from the census's own rows.
-- 2026-10-23 (item 345): `accum_content_pending #1–#3 h_kslotUp` punt → paid:chain off `pendingProps.h_kslotE` (the singleton relays).
-- 2026-10-24 (item 350): the `:` producers write `h_explUp`'s alternative as the stamp `NotQuestionPark sc`;
-- the `?`-entry consumers spend `empty` (`ns := []`) on the `inr` arm instead of relaying it.
   -- 2026-10-23 (item 344): `accum_block_pending` #2 pays `h_vpack` from `h_kslot` (was punt).
  -- item 311: the two closes hand `flowVPack_of_close resume.vslot` on through `.imp id PackAlt.ofGateClose`, so the
  -- writer reads `step` where it read `via`; the origin it carries is the same.
  -- Item 300: the content cascade's marker arm refutes a block-scalar head by
  -- `absurd` (the guard's `h_poss` against the head's cleared key), a third leaf.
   -- 2026-10-23 (item 344): `accum_block_pending` #2 pays `h_vpack` from `h_kslot` (was punt).
  -- item 311: the two closes hand `flowVPack_of_close resume.vslot` on through `.imp id PackAlt.ofGateClose`, so the
  -- writer reads `step` where it read `via`; the origin it carries is the same.
  -- Item 300: the content cascade's marker arm refutes a block-scalar head by
  -- `absurd` (the guard's `h_poss` against the head's cleared key), a third leaf.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-30 (item 405): rows follow `expectedOrigins` (the `?`-park chain ladder PAID, ruling "405 a").
-- 2026-10-30 (item 405, Rule 8 fix): the eight `h_kslot`-fed rows read `paid:other/built` (the projection `markedCols sc` is an `other` level) and `none=[fact,…]` where `MarkedColsIn.self` is spent.
def expectedRows : List String :=
  ["accum_block_on_noPending #1 ctor:pendingBlock.h_kslot := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
   -- Item 409 (2026-10-30): rows re-read with the renumbered origins and the paid `h_kslotD` consumers.
   "accum_block_on_noPending #1 ctor:pendingBlock.h_kslotUp := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_noPending #1 param:indicator_open_map.h_explUp_chain := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vpack := paid:frames/built pos=[] origins=[O0] none=[stamp] ⊢ none-held 0/1",
    "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vpack := paid:frames/built pos=[] origins=[O1] none=[stamp] ⊢ none-held 0/1",
    "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_pendingBlockContent #1 param:indicator_open_map.h_explUp_chain := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
    "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vpack := paid:frames/built pos=[] origins=[O2] none=[stamp] ⊢ none-held 0/1",
    "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vpack := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vpack := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vpack := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
    "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
    "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslotE := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
    "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
    "accum_content_pending #1 ctor:pendingProps.h_key := alt/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
    "accum_content_pending #2 ctor:pendingProps.h_key := alt/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
    "accum_content_pending #1 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
    "accum_content_pending #2 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
    "accum_content_pending #1 ctor:pendingBlockContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
    "accum_content_pending #3 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
    "accum_content_pending #2 ctor:pendingBlockContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
    "accum_content_pending #4 ctor:pendingContent.h_key := paid:other/built pos=[] origins=[] none=[absurd] ⊢ absurd*",
    "accum_content_pending #3 ctor:pendingBlockContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
    "accum_content_pending #5 ctor:pendingContent.h_key := relay/built pos=[] origins=[] none=[absurd,punt,stamp] ⊢ stamp*",
    "accum_flow_open_depth0 #1 param:flowKeyRoute_of_open.h_compact_pair := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map #1 ctor:pendingMapValue.h_ivl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map #1 ctor:pendingMapValue.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_explicit #1 ctor:pendingMapValue.h_kslot := punt/stamp pos=[] origins=[] none=[stamp,punt] ⊢ —",
    "colon_open_map_implicit #1 ctor:pendingMapValue.h_ivl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_implicit #1 ctor:pendingMapValue.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_props #1 ctor:pendingMapValue.h_ivl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_props #1 ctor:pendingMapValue.h_vslot := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "compact_open_map #1 ctor:pendingMapValue.h_kslot := punt/stamp pos=[] origins=[] none=[stamp,punt] ⊢ —",
    "content_dispatch_routed #1 ctor:pendingProps.h_key := relay/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
    "content_dispatch_routed #1 ctor:pendingProps.h_kslot := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "content_dispatch_routed #1 ctor:pendingProps.h_kslotE := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "content_dispatch_routed #2 ctor:pendingProps.h_key := relay/built pos=[] origins=[] none=[fact,stamp] ⊢ stamp*",
    "content_dispatch_routed #2 ctor:pendingProps.h_kslot := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "content_dispatch_routed #2 ctor:pendingProps.h_kslotE := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "content_dispatch_routed #1 ctor:pendingContent.h_vpack := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "content_dispatch_routed #2 ctor:pendingContent.h_vpack := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map #1 ctor:pendingMapValue.h_explUp := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_explicit #1 ctor:pendingMapValue.h_explUp := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_implicit #1 ctor:pendingMapValue.h_explUp := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "colon_open_map_props #1 ctor:pendingMapValue.h_explUp := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "compact_open_map #1 ctor:pendingMapValue.h_explUp := alt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslotUp := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslotUp := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslotUp := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslotUp_old] origins=[] none=[stamp] ⊢ unborn",
    "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslot := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslotUp := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslotUp_old] origins=[] none=[stamp] ⊢ unborn",
    "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslotUp := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslotUp_old] origins=[] none=[stamp] ⊢ unborn",
    "accum_content_pending #1 ctor:pendingBlockContent.h_kslotUp := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_content_pending #2 ctor:pendingBlockContent.h_kslotUp := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_content_pending #3 ctor:pendingBlockContent.h_kslotUp := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslotUp_old := relay/built pos=[ctor:pendingBlock.h_kslotUp] origins=[] ⊢ unborn",
    "accum_step_flow #1 ctor:pendingContent.h_vpack := punt/stamp pos=[] origins=[] none=[stamp,punt] ⊢ —",
    "accum_step_flow #2 ctor:pendingContent.h_vpack := punt/stamp pos=[] origins=[] none=[stamp,punt] ⊢ —",
    "colon_open_map #1 ctor:pendingMapValue.h_kslot := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
    "accum_block_on_closeThenBlock #1 param:indicator_open_map.h_explUp_chainD := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
    -- 2026-10-25 (item 359): punt/punt → punt/stamp — the value-park face beside this parameter pays
    -- `PackAlt.ofRefused (h_noek …)`, which the walker reads as a stamp origin.
    "accum_block_on_noPending #1 param:indicator_open_map.h_explUp_chainD := punt/stamp pos=[] origins=[] none=[stamp] ⊢ —",
    "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[] none=[stamp] ⊢ unborn",
    "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[] none=[stamp] ⊢ unborn",
    "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[] none=[stamp] ⊢ unborn",
    "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslotUp := paid:chain/built pos=[param:accum_block_on_pendingBlockContent.h_kslotUp] origins=[] none=[stamp] ⊢ unborn",
    "accum_block_on_pendingBlockContent #1 param:indicator_open_map.h_explUp_chainD := punt/punt pos=[] origins=[] none=[punt] ⊢ —",
    "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslotUp := relay/built pos=[ctor:pendingBlockContent.h_kslotUp] origins=[] ⊢ unborn",
    "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslotUp := relay/built pos=[ctor:pendingBlock.h_kslotUp] origins=[] ⊢ unborn",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_content_pending #1 ctor:pendingBlockContent.h_kslot := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
   "accum_content_pending #2 ctor:pendingBlockContent.h_kslot := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
   "accum_content_pending #3 ctor:pendingBlockContent.h_kslot := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
   "accum_flow_open_depth0 #3 param:flowKeyRoute_of_open.h_compact_pair := punt/stamp pos=[] origins=[] none=[punt,stamp] ⊢ —",
  -- 2026-10-31 (item 412): rows re-keyed to the renumbered origins (O16 → O62) plus the seven writers of the
  -- entry-shaped `h_expl` (net +7).
  "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_kslot := paid:other/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] none=[fact,punt] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 param:indicator_open_map.h_explUp_chain := alt/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] none=[stamp,punt] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 param:slotChainMap.up := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #2 param:slotChainMap.up := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] none=[absurd] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #3 param:slotChainMap.up := relay/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_closeThenBlock #1 param:colon_open_map_explicit.hvp := relay/built pos=[param:accum_block_on_closeThenBlock.h_vpack] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 2/41",
  "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_kslot := paid:other/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] none=[fact,punt,stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_kslot := paid:other/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] none=[fact,stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_kslot := paid:other/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] none=[fact,stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:indicator_open_map.h_explUp_chain := alt/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] none=[stamp,punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:indicator_open_map.h_explUp_chainD := alt/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] none=[punt] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:entryChainMap.up := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #2 param:entryChainMap.up := relay/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #3 param:entryChainMap.up := relay/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #4 param:entryChainMap.up := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #5 param:entryChainMap.up := relay/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:colon_open_map_explicit.hvp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslot,param:accum_block_on_pendingBlock.h_kslotUp] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_kslot := paid:other/built pos=[param:accum_block_on_pendingBlock.h_kslot] origins=[O62] none=[fact,stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_kslot := paid:other/built pos=[param:accum_block_on_pendingBlockContent.h_kslot] origins=[O62] none=[fact,stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 param:colon_open_map_explicit.hvp := paid:chain/built pos=[param:accum_block_on_pendingBlockContent.h_kslot,param:accum_block_on_pendingBlockContent.h_kslotUp] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlockContent #1 param:colon_fires_implicit_key.h_key := relay/built pos=[param:accum_block_on_pendingBlockContent.h_key] origins=[O4,O5,O6,O7,O11,O12,O13,O14,O62] ⊢ none-held 0/9",
  "accum_block_on_pendingContent #1 param:colon_fires_implicit_key.h_key := relay/built pos=[param:accum_block_on_pendingContent.h_key] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_vpack := relay/built pos=[param:accum_block_on_pendingContent.h_vpack] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_block_pending #1 param:accum_block_on_pendingContent.h_key := relay/built pos=[ctor:pendingContent.h_key] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_block_pending #1 param:accum_block_on_pendingContent.h_vpack := step/built pos=[ctor:pendingContent.h_vpack] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_block_pending #1 param:colon_fires_props_key.h_key := relay/built pos=[ctor:pendingProps.h_key] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_kslot := relay/built pos=[ctor:pendingBlockContent.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_key := relay/built pos=[ctor:pendingBlockContent.h_key] origins=[O4,O5,O6,O7,O11,O12,O13,O14,O62] ⊢ none-held 0/9",
  "accum_block_pending #1 param:accum_block_on_pendingBlock.h_kslot := relay/built pos=[ctor:pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_vpack := paid:chain/built pos=[ctor:pendingMapValue.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vpack := via/built pos=[ctor:pendingMapValue.h_kslot,ctor:pendingMapValue.h_explUp] origins=[O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[fact] ⊢ some-held 2/38",
  "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_vslot := alt/built pos=[ctor:pendingMapValue.h_explUp] origins=[O62] none=[punt,stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_key := via/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O4,O5,O6,O7,O62] none=[fact] ⊢ none-held 0/5",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_nodeV := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_compact := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_ivl := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_key := via/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O8,O9,O10,O62] none=[fact] ⊢ none-held 0/4",
  "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_kslotE := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_key := via/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O11,O12,O13,O14,O62] none=[fact] ⊢ none-held 0/5",
  "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_kslot := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_nodeV := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_compact := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_ivl := paid:chain/built pos=[param:accum_content_on_pendingBlock_indented.h_kslot_old] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_key := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot,param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp,punt,fact] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_vpack := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[fact] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeV := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_compact := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O22,O62] none=[stamp,punt] ⊢ none-held 0/2",
  "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_ivl := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O23,O62] none=[stamp,punt] ⊢ none-held 0/2",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_key := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot,param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp,punt,fact] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_kslot := step/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeV := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_compact := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O30,O62] none=[stamp,punt] ⊢ none-held 0/2",
  "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_ivl := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O31,O62] none=[stamp,punt] ⊢ none-held 0/2",
  "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_vpack := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[fact] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_key := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot,param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp,punt,fact] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_vpack := via/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[fact] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeV := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_compact := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O39,O62] none=[stamp,punt] ⊢ none-held 0/2",
  "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_ivl := relay/built pos=[param:accum_content_on_pendingMapValue_indented.h_expl] origins=[O40,O62] none=[stamp,punt] ⊢ none-held 0/2",
  "accum_content_pending #1 ctor:pendingProps.h_kslot := step/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_pending #1 ctor:pendingProps.h_kslotE := step/built pos=[ctor:pendingProps.h_kslotE] origins=[O62] ⊢ none-held 0/1",
  "accum_content_pending #2 ctor:pendingProps.h_kslot := step/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_pending #2 ctor:pendingProps.h_kslotE := step/built pos=[ctor:pendingProps.h_kslotE] origins=[O62] ⊢ none-held 0/1",
  "accum_content_pending #1 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_content_pending #2 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_content_pending #3 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_content_pending #4 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_content_pending #5 ctor:pendingContent.h_vpack := paid:chain/built pos=[ctor:pendingProps.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_kslot_old := relay/built pos=[ctor:pendingBlock.h_kslot] origins=[O62] ⊢ none-held 0/1",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_expl := relay/built pos=[ctor:pendingMapValue.h_expl] origins=[O62] ⊢ none-held 0/1",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_vslot := step/built pos=[ctor:pendingMapValue.h_vslot] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O46,O47,O48,O55,O56,O57,O58,O59,O60,O61,O62] ⊢ some-held 8/48",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_kslot := relay/built pos=[ctor:pendingMapValue.h_kslot] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_ivl_mv := relay/built pos=[ctor:pendingMapValue.h_ivl] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O45,O47,O48,O49,O50,O51,O52,O53,O54,O61,O62] ⊢ some-held 8/48",
  "accum_flow_open_depth0 #2 param:flowKeyRoute_of_open.h_compact_pair := paid:chain/built pos=[ctor:pendingBlock.h_kslot] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_step_flow #1 ctor:pendingContent.h_key := via/built pos=[] origins=[O41] ⊢ none-held 0/1",
  "accum_step_flow #1 param:flowKeyPack_of_close.h_key := relay/built pos=[] origins=[O42] ⊢ none-held 0/1",
  "accum_step_flow #2 ctor:pendingContent.h_key := via/built pos=[] origins=[O43] ⊢ none-held 0/1",
  "accum_step_flow #2 param:flowKeyPack_of_close.h_key := relay/built pos=[] origins=[O44] ⊢ none-held 0/1",
  "colon_fires_implicit_key #1 param:colon_open_map_implicit.h_kslotD := step/built pos=[param:colon_fires_implicit_key.h_key] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "colon_fires_props_key #1 param:colon_open_map_props.h_kslotD := step/built pos=[param:colon_fires_props_key.h_key] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 1/37",
  "colon_open_map #1 ctor:pendingMapValue.h_expl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_ivl := paid:chain/built pos=[param:colon_open_map_explicit.hvp] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 2/41",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_expl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map_explicit #1 ctor:pendingMapValue.h_vslot := paid:chain/built pos=[param:colon_open_map_explicit.hvp] origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ some-held 2/41",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_expl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map_implicit #1 ctor:pendingMapValue.h_kslot := paid:chain/built pos=[param:colon_open_map_implicit.h_kslotD] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "colon_open_map_props #1 ctor:pendingMapValue.h_expl := stamp/stamp pos=[] origins=[] none=[stamp] ⊢ —",
  "colon_open_map_props #1 ctor:pendingMapValue.h_kslot := paid:chain/built pos=[param:colon_open_map_props.h_kslotD] origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] none=[stamp] ⊢ some-held 1/37",
  "compact_open_map #1 ctor:pendingMapValue.h_ivl := relay/built pos=[] origins=[O45] none=[stamp,fact] ⊢ none-held 0/1",
  "compact_open_map #1 ctor:pendingMapValue.h_vslot := relay/built pos=[] origins=[O46] none=[stamp,fact] ⊢ none-held 0/1",
  "content_dispatch_routed #1 ctor:pendingContent.h_key := relay/built pos=[] origins=[O47] none=[punt,absurd,stamp] ⊢ none-held 0/1",
  "content_dispatch_routed #2 ctor:pendingContent.h_key := relay/built pos=[] origins=[O48] none=[punt,absurd,stamp] ⊢ none-held 0/1",
  "indicator_open_map #1 param:question_open_map.h_explUp_chain := relay/built pos=[param:indicator_open_map.h_explUp_chain] origins=[O62] ⊢ none-held 0/1",
  "indicator_open_map #1 param:question_open_map.h_explUp_chainD := relay/built pos=[param:indicator_open_map.h_explUp_chainD] origins=[O62] ⊢ none-held 0/1",
  "question_open_map #1 ctor:pendingMapValue.h_ivl := paid:route/built pos=[] origins=[O49,O50,O51,O52,O53,O54] ⊢ all-held 6/6",
  "question_open_map #1 ctor:pendingMapValue.h_expl := paid:chain/built pos=[param:question_open_map.h_explUp_chainD] origins=[O62] none=[absurd,punt] ⊢ none-held 0/1",
  "question_open_map #1 ctor:pendingMapValue.h_vslot := paid:route/built pos=[] origins=[O55,O56,O57,O58,O59,O60] ⊢ all-held 6/6",
  "question_open_map #1 ctor:pendingMapValue.h_kslot := paid:tail/built pos=[param:question_open_map.h_explUp_chainD] origins=[O61,O62] none=[punt] ⊢ some-held 1/2",
  "question_open_map #1 ctor:pendingMapValue.h_explUp := alt/built pos=[param:question_open_map.h_explUp_chainD] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  -- Item 413: compact_open_map's h_expl row re-read (its origin list now reaches h_chainUp) + the two paid:chain relays of h_chainUp (the inline fill's slot routes, the pendingBlock arm's h_kslotUp).
  "accum_block_on_closeThenBlock #1 param:compact_open_map.h_chainUp := paid:chain/built pos=[param:accum_block_on_closeThenBlock.h_vslot] origins=[O62] none=[stamp] ⊢ none-held 0/1",
  "accum_block_on_pendingBlock #1 param:compact_open_map.h_chainUp := paid:chain/built pos=[param:accum_block_on_pendingBlock.h_kslotUp] origins=[] none=[stamp] ⊢ unborn",
  "compact_open_map #1 ctor:pendingMapValue.h_expl := relay/built pos=[param:compact_open_map.h_chainUp] origins=[O62] none=[stamp,absurd,punt] ⊢ none-held 0/1"]
-- 2026-10-20 (item 306): the positions' origin sets re-read with the three new origins
-- (`O3`, `O7`, `O10`) and the renumbering behind them; no position is born or dies.
-- 2026-10-20 (item 307): the positions' origin sets re-read (three new origins, renumbered).
-- 2026-10-21 (item 320): 1 position rows re-read — `accum_block_on_closeThenBlock.h_vpack`'s premise at the marker arms
-- is paid through `PackAlt.ofRefused h_noek…` (a fact where it punted); regenerated from the census's own rows.
-- 2026-10-21 (item 321): 3 position rows re-read — `accum_block_on_noPending`'s fresh fields and the openers'
-- paid leaves read `stamp`/`fact` where they punted; regenerated from the census's own rows.
-- 2026-10-21 (item 324): `flowKeyRoute_of_open.h_compact_pair`'s `punt` 1 → 0, `stamp` 0 → 1 — its one punting writer, the
-- `---` arm, pays through `PackAlt.ofRefused h_noekS`; the two built writers and the holdings stand.
-- 2026-10-23 (item 345): `pendingBlockContent.h_kslotUp` punt 3 → 0 (the three singleton relays).
-- 2026-10-24 (item 350): `h_explUp`'s writers — the `:` producers stamp `NotQuestionPark sc` (punt 5 → 0);
-- `compact_open_map`/`question_open_map` split on the alternative.
-- Item 371: the value-line packs end in the one-level `ResumeFrames`; `question_open_map`'s chain
-- is bottomed on the bound tail route `h_route51F` (set re-pinned).
-- 2026-10-30 (item 405): per-position classes follow `expectedRows`.
def expectedPerPos : List String := [
   -- Item 409 (2026-10-30): per-position rows re-read (49 → 48: `explFrameValueLine.h_kslot` gone; origins renumbered).
  "ctor:pendingBlockContent.h_kslotUp writers=6 punt=0 stamp=3 built=3 unborn=3 dead=0 allHeld=0 someHeld=0 noneHeld=0 origins=[] ⊢ unborn",
  "param:accum_block_on_pendingBlock.h_kslotUp writers=1 punt=0 stamp=0 built=1 unborn=1 dead=0 allHeld=0 someHeld=0 noneHeld=0 origins=[] ⊢ unborn",
  "param:accum_block_on_pendingBlockContent.h_kslotUp writers=1 punt=0 stamp=0 built=1 unborn=1 dead=0 allHeld=0 someHeld=0 noneHeld=0 origins=[] ⊢ unborn",
  "param:accum_content_on_pendingBlock_indented.h_kslotUp_old writers=1 punt=0 stamp=0 built=1 unborn=1 dead=0 allHeld=0 someHeld=0 noneHeld=0 origins=[] ⊢ unborn",
  "param:flowVPack_of_close.h_vslot writers=0 punt=0 stamp=0 built=0 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=0 origins=[] ⊢ punt-only",
  "ctor:pendingBlock.h_kslotUp writers=7 punt=0 stamp=3 built=4 unborn=4 dead=0 allHeld=0 someHeld=0 noneHeld=0 origins=[] ⊢ unborn",
  -- 2026-10-31 (item 412): the two entry-shaped `h_expl` positions, and the key positions whose origins are re-keyed past them.
  "ctor:pendingContent.h_key packaged writers=12 punt=0 stamp=0 built=12 unborn=0 dead=0 allHeld=0 someHeld=2 noneHeld=4 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "ctor:pendingContent.h_vpack writers=12 punt=0 stamp=4 built=8 unborn=0 dead=0 allHeld=0 someHeld=8 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "ctor:pendingProps.h_key packaged writers=6 punt=0 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=1 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "ctor:pendingProps.h_kslot writers=6 punt=0 stamp=3 built=3 unborn=0 dead=0 allHeld=0 someHeld=3 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "ctor:pendingProps.h_kslotE writers=6 punt=1 stamp=2 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O62] ⊢ 0/1 held",
  "ctor:pendingBlockContent.h_key packaged writers=6 punt=0 stamp=0 built=6 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O4,O5,O6,O7,O11,O12,O13,O14,O62] ⊢ 0/9 held",
  "ctor:pendingBlockContent.h_kslot writers=6 punt=0 stamp=3 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O62] ⊢ 0/1 held",
  "ctor:pendingBlock.h_kslot writers=7 punt=0 stamp=1 built=6 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=6 origins=[O62] ⊢ 0/1 held",
  "ctor:pendingMapValue.h_ivl writers=6 punt=0 stamp=3 built=3 unborn=0 dead=0 allHeld=1 someHeld=1 noneHeld=1 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O45,O47,O48,O49,O50,O51,O52,O53,O54,O61,O62] ⊢ 8/48 held",
  "ctor:pendingMapValue.h_vslot writers=6 punt=0 stamp=3 built=3 unborn=0 dead=0 allHeld=1 someHeld=1 noneHeld=1 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O46,O47,O48,O55,O56,O57,O58,O59,O60,O61,O62] ⊢ 8/48 held",
  "ctor:pendingMapValue.h_kslot writers=6 punt=0 stamp=3 built=3 unborn=0 dead=0 allHeld=0 someHeld=3 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "ctor:pendingMapValue.h_explUp writers=6 punt=0 stamp=5 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:accum_block_on_closeThenBlock.h_vpack writers=11 punt=1 stamp=2 built=8 unborn=0 dead=0 allHeld=0 someHeld=5 noneHeld=3 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 2/41 held",
  "param:accum_block_on_closeThenBlock.h_vslot writers=11 punt=0 stamp=10 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:accum_block_on_pendingBlock.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:accum_block_on_pendingBlockContent.h_key packaged writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O4,O5,O6,O7,O11,O12,O13,O14,O62] ⊢ 0/9 held",
  "param:accum_block_on_pendingBlockContent.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:accum_block_on_pendingContent.h_key packaged writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:accum_block_on_pendingContent.h_vpack writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:accum_content_on_pendingBlock_indented.h_kslot_old writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:accum_content_on_pendingMapValue_indented.h_expl writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:accum_content_on_pendingMapValue_indented.h_ivl_mv writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O45,O47,O48,O49,O50,O51,O52,O53,O54,O61,O62] ⊢ 8/48 held",
  "param:accum_content_on_pendingMapValue_indented.h_kslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:accum_content_on_pendingMapValue_indented.h_vslot writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O46,O47,O48,O55,O56,O57,O58,O59,O60,O61,O62] ⊢ 8/48 held",
  "param:colon_fires_implicit_key.h_key packaged writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=1 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:colon_fires_props_key.h_key packaged writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:colon_open_map_explicit.hvp writers=3 punt=0 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=2 origins=[O0,O1,O2,O3,O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 2/41 held",
  "param:colon_open_map_implicit.h_kslotD writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:colon_open_map_props.h_kslotD writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=0 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:entryChainMap.up writers=5 punt=0 stamp=0 built=5 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=5 origins=[O62] ⊢ 0/1 held",
  "param:entryKeyPack_of_dispatch.h_compact writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=4 origins=[O22,O39,O62] ⊢ 0/3 held",
  "param:entryKeyPack_of_dispatch.h_ivl writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=4 origins=[O23,O40,O62] ⊢ 0/3 held",
  "param:entryKeyPack_of_dispatch.h_nodeV writers=4 punt=0 stamp=0 built=4 unborn=0 dead=0 allHeld=0 someHeld=2 noneHeld=2 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:entryPropsKeyPack_of_dispatch.h_compact writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O30,O62] ⊢ 0/2 held",
  "param:entryPropsKeyPack_of_dispatch.h_ivl writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O31,O62] ⊢ 0/2 held",
  "param:entryPropsKeyPack_of_dispatch.h_nodeV writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=1 noneHeld=1 origins=[O4,O5,O6,O7,O8,O9,O10,O11,O12,O13,O14,O15,O16,O17,O18,O19,O20,O21,O24,O25,O26,O27,O28,O29,O32,O33,O34,O35,O36,O37,O38,O41,O43,O47,O48,O61,O62] ⊢ 1/37 held",
  "param:flowKeyPack_of_close.h_key writers=2 punt=0 stamp=0 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O42,O44] ⊢ 0/2 held",
  "param:flowKeyRoute_of_open.h_compact_pair writers=3 punt=0 stamp=2 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:indicator_open_map.h_explUp_chain writers=4 punt=1 stamp=1 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O62] ⊢ 0/1 held",
  "param:indicator_open_map.h_explUp_chainD writers=4 punt=2 stamp=1 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:question_open_map.h_explUp_chain writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:question_open_map.h_explUp_chainD writers=1 punt=0 stamp=0 built=1 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held",
  "param:slotChainMap.up writers=3 punt=0 stamp=0 built=3 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=3 origins=[O62] ⊢ 0/1 held",
  -- Item 413: pendingMapValue.h_expl noneHeld 1 -> 2 (compact_open_map's writer re-read) + param:compact_open_map.h_chainUp (two paid:chain writers).
  "ctor:pendingMapValue.h_expl writers=6 punt=0 stamp=4 built=2 unborn=0 dead=0 allHeld=0 someHeld=0 noneHeld=2 origins=[O62] ⊢ 0/1 held",
  "param:compact_open_map.h_chainUp writers=2 punt=0 stamp=0 built=2 unborn=1 dead=0 allHeld=0 someHeld=0 noneHeld=1 origins=[O62] ⊢ 0/1 held"]
-- 2026-10-24 (item 355): 0 → 9.  The marked-column domain is transported through the step by
-- `h.imp (fun ⟨ns, hd, k⟩ => ⟨ns, MarkedColsIn.step_content … hd, k⟩) …`, which this walker reads as a
-- `step(...)` writer with no origin (it does not look through the transport lambda to the door it
-- re-packs); the nine positions below are the domained faces and the twins they feed.  Instrument
-- debt, item 356.
def expectedUnborn : List String := [
  "ctor:pendingBlockContent.h_kslotUp writers=6 punt=0",
  "param:accum_block_on_pendingBlock.h_kslotUp writers=1 punt=0",
  "param:accum_block_on_pendingBlockContent.h_kslotUp writers=1 punt=0",
  "param:accum_content_on_pendingBlock_indented.h_kslotUp_old writers=1 punt=0",
  "ctor:pendingBlock.h_kslotUp writers=7 punt=0"]

/-- **The origins' own line.**  `alts` counts the match alternatives the walk
    crosses and `liteNodes` the term size it walks; item 272 moves both and
    nothing else, because the under-run disjunct the three flow-open arms
    destructure gains a sixth component — one alternative per arm, and the
    terms that carry it.

    Lean v4.35.0 moves the two size readings and nothing else: `nodes` 12337 →
    12326 and `liteNodes` 491982 → 491884.  `alts` holds at 4312, so the walk
    crosses the same alternatives over smaller terms.

    Item 284 moves the same three and nothing else: `alts` 4312 → 4340, `nodes`
    12326 → 12404, `liteNodes` 491886 → 495218.  Two isolations on the item-284
    tree split it.  Restoring the under-run's SIX components reads `alts` 4337:
    the flag it gains is item 272's yardstick exactly, one alternative per
    flow-open arm, with +501 `liteNodes`.  Restoring the old `pendingFlow` arm
    reads `alts` 4340 and `nodes` 12404: that arm moves only `liteNodes`, −211.
    The other 25 alternatives, the 78 `nodes` and the rest of `liteNodes` are
    the item's remaining edits inside walked terms — its four park fields and
    their payments — measured as the remainder and not isolated further.

    Item 285 moves five readings, every one inside `accum_flow_open_depth0`: one
    more `let`, the `have slot_ride` itself; twelve more local applications and
    fourteen more alternatives, its three spends and its `match h_optok`;
    `nodes` +68 as `ValueLinePacks` reads them, and `liteNodes` +1877.

    Item 287 moves six.  `punt` 42 → 32 and `stamp` 3 → 13 are the eleven
    `h_vslot` writers `expectedRows` names; `nodes` 12472 → 12416 is
    `ValueLinePacks`' −56; `lets` 554 → 552 are the two `have h_res` the old
    inline sites bound.  `lapps` +11 and `liteNodes` +2190 are the two `:`
    consumers applying their punt builder and the readings handed to it,
    measured as the remainder and not isolated further.

    Item 288 moves five: `punt` 32 → 29 and `stamp` 13 → 16 are the three flat
    decliners of `pendingMapValue.h_vslot` writing the stamp; `lapps` +1,
    `alts` +4 and `liteNodes` +450 are the frameless arm's refutation and
    `compact_open_map`'s stamp proof, measured as the remainder and not isolated
    further.

    Item 289 moves three, and the walk run per declaration names all of them
    (`scratchpad/l4yaml-row12-steps/320-vlo-perdecl.log`, against item 288's
    tree rebuilt in place).  `lets` +3, `alts` +19 and `liteNodes` +2806 are
    `colon_fires_props_key`'s `tab` arm, which refutes where it deferred; the
    other +16 `liteNodes` are `accum_content_pending`'s three transport calls
    passing the new premise (+12) and the two new fields bound at the `tab`
    arms of `accum_flow_open_depth0` and `colon_fires_implicit_key` (+2 each).
    No row, class or origin moves.

    Item 293 moves five, and the same per-declaration run names them
    (`scratchpad/l4yaml-row12-steps/381-vlo-perdecl-293.log`, against item
    292's tree rebuilt in place).  The largest share is `accum_step_flow`'s two
    depth-0 closes paying `h_live` from the restored slot (`lets` +2, `alts`
    +22, `liteNodes` +1462); then `accum_content_pending`'s props arm, run
    extensions and routed possibility (`alts` +8, `liteNodes` +684), the two
    indented lemmas (`alts` +3 and `liteNodes` +311 each), the three block
    consumers' stamp-wrapper calls paying the escape park's flag (`alts` +2 and
    `liteNodes` +148 each), the eight opens (`lapps` +2, `liteNodes` +261), and
    the refuted `¬ possible` arm (`lapps` +1, `liteNodes` +57).  The two
    `pendingDocStart` producers shrink by 25 each, paying the narrowed field
    without its `Or.inl`; `nodes` +75 is the new fields bound at each
    eliminator and the threading.  No row, class or origin moves.

    Item 295 moves `liteNodes` alone, 506219 → 506370: all of it is
    `accum_flow_open_depth0`'s, the one declaration whose term changed —
    `slot_ride`'s frame built field by field around `flowKeyRoute_of_root`'s
    route, the two indicator parks' own flags, and the props arm's fallback
    route.  No row, class or origin moves.

    Item 297 moves `lapps` 672 → 670 and `liteNodes` 506370 → 506315: the two
    `:` consumers' `dedent` arms, each one application of the punt builder,
    are deleted with the constructor, and `liteNodes` is the net over the
    declarations whose terms changed (the two producers' `w ∉ ks` exits grow,
    the `dedent` alternatives go).  No row, class or origin moves.

    Item 299 moves `nodes` 12491 → 12501 and `liteNodes` 506315 → 515490:
    `pendingDocStart`'s new `h_docline` field (a binder at each park
    eliminator, an argument at each producer) and `dispatch_refutes_sameLine`'s
    new premise at its callers, and the `docStartLine` field's preservation
    family and transport lemmas entering the lite walk.  No row, class or
    origin moves.

    Item 300 moves `lets` 557 → 566, `lapps` 670 → 674, `alts` 4421 → 4454,
    `nodes` 12501 → 12510 and `liteNodes` 515490 → 520132: the marker reason's
    arms — the `have`s and `cases` of `content_dispatch_routed`'s two
    cascades, the flow open's second split on the run's punt, the two `:`
    consumers' arms and the close's third reading — in the walked
    declarations; named by cause.  No row, class or origin moves. -/
-- 2026-10-20 (item 304): `alts` 4454 → 4457, `liteNodes` 520132 → 520404 — the
-- three value-line resumes split `KeyFrames.resumeAt`'s sum with `rcases`, one
-- alternative each; every structural count stands (`frames` 24 among them).
-- 2026-10-20 (item 305): the pushes' and bottoms' terms (item 305): `lets` 566 → 567, `lapps` 674 → 679, `alts` 4457 → 4466, `nodes` 12510 → 12512, `liteNodes` 520404 → 522831.
-- 2026-10-20 (item 306): `origins` 70 → 73, `frames` 24 → 27, `follows` 309 → 315, `lapps` 679 → 688, `alts` 4466 → 4475, `liteNodes` 522831 → 524996 — the three
-- `frames(h_closeFV_old)` origins (two `h_nodeFV`, one `h_dframesV` route) and their terms.
-- 2026-10-20 (item 307): `punt` 29 → 26, `built` 135 → 138, `origins` 73 → 76, `originRows` 38 → 41, `frames` 27 → 30, `noneHeld` 73 → 76, `follows` 315 → 317, `lets` 567 → 570, `lapps` 688 → 696, `alts` 4475 → 4489, `nodes` 12512 → 12518, `liteNodes` 524996 → 526179.
-- 2026-10-20 (item 307, second chain): `follows` 317 → 318, `liteNodes` 526179 → 526154.
-- 2026-10-20 (item 309): `nodes` 12518 → 12524, `liteNodes` 526154 → 526163.
-- 2026-10-21 (item 311): `alts` 4489 → 4495, `nodes` 12524 → 12547, `liteNodes` 526163 → 527740 — the named alternative's
-- definitions and stubs, the frame-crossing conversions and the two `.imp id PackAlt.ofGateClose` wrappers at the closes;
-- every row and position stands (180, 47), two close writers reading `step` where they read `via`.
-- 2026-10-21 (item 313): `nodes` 12547 → 12554, `liteNodes` 527740 → 529047 — the content lane's five writers on the
-- props and mapping-value packs step through `PackAlt.step_content`; every row and position stands (180, 47).
-- 2026-10-21 (item 314): `follows` 318 → 339, `liteNodes` 529047 → 529323 — the content lane's declining arms hand their
-- hypothesis on, and the walk follows each; every row and position stands (180, 47).
-- 2026-10-21 (item 315): `nodes` 12554 → 12556 — the key-pack lemmas' six arms step through the wrapper; rows and positions stand.
-- 2026-10-21 (item 318): `liteNodes` 529323 → 529329 — the one paid dash arm of `accum_block_on_pendingBlock` applies
-- `PackAlt.step_blockEntry` to its two step facts where it wrote `trivial`; rows and positions stand.
-- 2026-10-21 (item 319): `follows` 339 → 342, `liteNodes` 529329 → 529533 — the block lane's paid arms hand their
-- alternative on (three more origins followed through a transport; the fourteen `PackAlt.step_blockEntry` applications and
-- the two `.imp` relays grow the terms); rows and positions as re-pinned above.
-- 2026-10-21 (item 320): `punt` 26 → 24, `stamp` 16 → 18, `follows` 342 → 343, `nodes` 12556 → 12575, `liteNodes` 529533 → 529719
-- — the marker arms' two `h_vpack` premises are stamped from the parks' new field, one more origin is followed through the
-- `h_seqFramesV` relay, and the field, the payments, the relay and the split arms grow the terms; rows as re-pinned above.
-- 2026-10-21 (item 321): `punt` 24 → 21, `stamp` 18 → 21, `lapps` 696 → 701, `liteNodes` 529719 → 529806 — `accum_block_on_noPending`'s
-- three fresh fields are stamped from its own `h_noek` through `PackAlt.step_blockEntry`, and the five applications of the
-- payments grow the terms; rows and positions as re-pinned above.
-- 2026-10-21 (item 322): `lapps` 701 → 707, `nodes` 12575 → 12578, `liteNodes` 529806 → 529833 — the six opener leaves apply the step
-- premise and the two callers apply `PackAlt.step_value`; rows as re-pinned above, positions unchanged.
-- 2026-10-21 (item 324): `punt` 21 → 20, `stamp` 21 → 22, `lapps` 707 → 708, `liteNodes` 529833 → 529841 — the `---` arm's
-- `h_compact_pair` is stamped from the park's `h_noek` through `PackAlt.ofRefused` where it punted, and the payments grow the
-- terms; rows as re-pinned above, positions unchanged.
-- 2026-10-23 (item 344): `punt` 14 → 13, `built` 138 → 139, `noneHeld` 104 → 105, `follows` 343 → 344, `lapps` 709 → 714, `alts` 4490 → 4494, `liteNodes` 543421 → 543929
-- — `accum_block_pending` #2 pays `h_vpack` (one more built row, its term's size).
-- 2026-10-23 (item 345): punt 13 → 10, built 139 → 142, noneHeld 105 → 108, follows 344 → 347, lapps 714 → 722, alts 4494 → 4499, liteNodes 543929 → 544679 — the three `h_kslotUp` singleton relays.
-- 2026-10-23 (item 349): `lets` 570 → 572, `lapps` 722 → 724, `alts` 4499 → 4501, `nodes` 12587 → 12593, `liteNodes` 544679 → 544809 — `h_dead` threaded through the
-- content step; origins/rows unmoved once the bottoms memo is keyed by the binder stack.
-- 2026-10-24 (item 350): punt 10 → 5, stamp 28 → 32, built 142 → 143, relayedStamp 10 → 11, follows 347 → 343, lapps 724 → 725, alts 4501 → 4513, nodes 12593 → 12597, liteNodes 544809 → 546045
-- — the `:` producers stamp `NotQuestionPark sc`; `inr` arms spend `empty`/absurd.
-- 2026-10-23 (item 345): liteNodes 546045 → 546027
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-25 (#99 review): liteNodes=598322 → liteNodes=598322 — the dead `FlowLead` + two lemmas deleted; `leadFree`/`closeFree` are `Bool` (walked-term total).
-- 2026-10-26 (item 367, `[82]`): module-wide tallies only (StreamAccum directive sites apply `scannedDirective_toSL`; three `s-l-comments` lemmas added); origins/routes unchanged: alts 5209 → 5203, nodes 13722 → 13686, liteNodes 621993 → 621478.
-- 2026-10-26 (item 370): one more frame fact at the sibling `-` arm (`h_closeF_old` relayed into `pendingBlock.h_closeF`).
-- 2026-10-28 (item 385): liteNodes 634791 → 634748
-- — tree-size counts only (the two item-385 helpers and their three call sites); no origin row moved.
-- 2026-10-29 (item 387): lets 657 → 658, alts 5280 → 5289, liteNodes 635676 → 636417 — term size only (the no-pop arm's `dite n < k`
-- at `accum_block_on_pendingBlock`); positions, origins and rows unchanged.
-- 2026-10-29 (item 388): lapps 822 → 826, alts 5289 → 5291, nodes 13706 → 13710, liteNodes 636417 → 636818 — the landed birth's `nv ≤ k` arm (cover `Or.inr trivial`, frames `[]`) and the `.blockOut` wraps.
-- 2026-10-29 (item 389): alts 5306 → 5299, lapps 843 → 844, lets 672 → 679, liteNodes 644591 → 641338 against the pre-review pin — term-size counters only (the conjunct resumes the park's own `ks` after PR #161 review; no `let`-destructured witness); no origin row moved.
-- 2026-10-29 (item 394): the term grew with `FlowBaseRoutes.valueF`'s supply and relays; no origin row moved.
-- 2026-10-29 (item 394, option B): the flow stack's s0 index and valueF's cover (walked-term total).
-- 2026-10-29 (item 396): node counts follow flowOpen_floor_at_prep's deletion and content_dispatch_after_close's restatement.
-- 2026-10-30 (item 405): see `expectedPositions`/`expectedRows` (the `?`-park chain ladder PAID).
-- 2026-10-30 (item 405, Rule 8 fix): follows 365 → 373, alts 5506 → 5496, nodes 13816 → 13807, liteNodes 665425 → 662944 — the `h_kslot` writers pass the projection `markedCols sc` (`paid:other`) and spend `MarkedColsIn.self` (`fact`).
-- 2026-10-30 (item 405, Rule 8 fix, review re-read): liteNodes 662944 → 663000 — the two head consumers split on `(markedCols sc).reverse`.
-- 2026-10-30 (item 407, flow carrier `pendingKeys` conjunct): lets 685 → 687, lapps 856 → 857, alts 5496 → 5624, nodes 13807 → 13820, liteNodes 663000 → 674796 — the `h_pk_ad`/`h_pk_park` lets and the 20 `FlowStackK` rebuild siblings in the three step lemmas.
def expectedLine : String :=
  -- 2026-10-25 (item 359): punt 12 → 11, stamp 39 → 40 — the `noPending` value-park face pays `PackAlt.ofRefused (h_noek …)`;
  -- lapps 806 → 807, liteNodes 607398 → 607407 — that one application and its term.
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); lets 640 → 637, lapps 813 → 810, alts 5345 → 5154, nodes 13720 → 13689 (walked-term totals; the faces' punt/stamp rows unchanged).
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; five `match` blocks deleted): follows=355 → 354, lets=637 → 638, alts=5154 → 5153, nodes=13689 → 13691, liteNodes=616435 → 616369
  -- 2026-10-26 (item 365): follows 354 → 360, lets 638 → 641, alts 5189 → 5205, nodes 13691 → 13708,
  -- liteNodes 621021 → 621328 — three `h_refused` lets and eleven `h_alt := h_refused.elim …` alternatives in the
  -- content lemmas; no origin class moved (stamp/ride/none unchanged).
  -- 2026-10-26 (item 366): alts 5205 → 5209, nodes 13708 → 13722, liteNodes 621328 → 621993 — the two `h_outer` pays at
  -- closeThenBlock (`Classical.em` alternatives and their lets); no origin class moved.
  -- 2026-10-26 (item 369): lapps=813 → lapps=814, alts=5203 → alts=5210, nodes=13686 → nodes=13688, liteNodes=621478 → liteNodes=621947 — `h_closeF_old` (the `-` park's frames) held under `accum_block_on_pendingBlock`; no origin row moved.
-- Item 371 (origins=72 → 67, route=21 → 12, tail=0 → 14, other=6 → 0, concl=12 → 8, heldOrigins=26 → 15, allHeld=9 → 3, noneHeld=60 → 66, lets=641 → 645, lapps=815 → 821, alts=5222 → 5229, nodes=13688 → 13696, liteNodes=622909 → 629317): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
-- Item 372 (2026-10-27): the Or-shaped route conjunct of `ImplicitKeyPack` (summary mirrors the five `(Or)` rows).
-- Item 374: lets=647 → 648, lapps=821 → 822, alts=5234 → 5243, nodes=13694 → 13696, liteNodes=630069 → 632322 — the resume context's face disjunct and `resumectx_of_landing`'s `h_base`.
  -- 2026-10-28 (item 386): lets 652 → 657, alts 5277 → 5280, nodes 13696 → 13706, liteNodes 634748 → 635676 — the `-` opener's `h_lvl_old` and its `omega` spend at the no-pop arm; no origin row moved.
  "positions=51 packaged=7 packConsts=[ImplicitKeyPack,PropsKeyPack] rows=190 ctorRows=104 paramRows=86 packagedRows=29 punt=5 stamp=53 built=132 origins=63 originRows=28 route=12 frames=29 tail=10 other=0 concl=8 invariant=4 heldOrigins=14 allHeld=2 someHeld=37 noneHeld=68 unbornRows=11 relayedPunt=0 relayedStamp=10 relayedAbsurd=4 relayedFact=0 deadRows=0 unbornPos=5 rounds=5 follows=378 lets=693 lapps=865 alts=5648 nodes=13903 liteNodes=677986"

/-! ## §4 The reading -/

structure Origin where
  row : Nat
  kind : String
  label : String
  lvl : Option String
  deriving Inhabited

def dedupNat (xs : Array Nat) : Array Nat := (xs.qsort (· < ·)).foldl (fun acc x => if acc.back? == some x then acc else acc.push x) #[]

run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pe := mkPackEnv env
  let cs ← collect pe
  let posKeys : Std.HashSet String := cs.positions.foldl (fun s p => s.insert p.key) {}
  let posMap : Std.HashMap String Position := cs.positions.foldl (fun m p => m.insert p.key p) {}
  let w ← IO.mkRef ({} : W)
  for n in sorted cs.thms do walkTheoremP w cs.cd n
  let ws ← w.get
  let rowKey (r : WRow) : String := s!"{r.kind}:{r.target}"
  let letsBy : Std.HashMap Name (Array LetRec) := ws.lets.foldl (fun m l => m.insert l.lem ((m.getD l.lem #[]).push l)) {}
  let lappsBy : Std.HashMap Name (Array LApp) := ws.lapps.foldl (fun m a => m.insert a.lem ((m.getD a.lem #[]).push a)) {}
  let altsBy : Std.HashMap Name (Array AltRec) := ws.alts.foldl (fun m a => m.insert a.lem ((m.getD a.lem #[]).push a)) {}
  let memo : BMemo ← IO.mkRef {}
  let budget : Budget ← IO.mkRef 0
  let dyn : DynAlts ← IO.mkRef #[]
  let fmemo : FMemo ← IO.mkRef {}
  -- every row: its class (item 261's reading), its bottoms and where they lead
  let mut srcs : Array (Array Src) := #[]
  let mut myCls : Array String := #[]
  let mut prs : Array PackRead := #[]
  let mut owns : Array String := #[]
  let mut follows := 0
  for r in ws.rows do
    unless r.argIdx < r.args.size do throwError "{r.target}: {r.args.size} args"
    let some pos := posMap[rowKey r]? | throwError "{rowKey r}: no position"
    budget.set 100000
    dyn.set #[]
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
    owns := owns.push own
    prs := prs.push (← packCls env r.st r.args[r.argIdx]! r.vcLeft r.otherTrue)
    let bots ← bottomsOf pe memo budget dyn r.st r.args[r.argIdx]! pos.path
    let cx : FCx := { pe, memo, budget, dyn, fmemo, lem := r.lem, posKeys, lets := letsBy.getD r.lem #[], lapps := lappsBy.getD r.lem #[], alts := altsBy.getD r.lem #[] }
    let mut ss : Array Src := #[]
    for bt in bots do
      follows := follows + 1
      ss := ss ++ (← followBot cx bt)
    srcs := srcs.push (dedupSrc ss)
    let terms := bots.filterMap fun | .term t => some t | _ => none
    myCls := myCls.push (if bots.size > 0 && terms.size == bots.size && terms.all (· == "punt") then "punt"
      else if bots.size > 0 && terms.size == bots.size && terms.all (fun t => t == "punt" || t == "stamp") then "stamp" else "built")
  -- the origins, each once per (row, label)
  let mut origins : Array Origin := #[]
  let mut originIdx : Std.HashMap String Nat := {}
  let mut rowOr : Array (Array Nat) := #[]
  let mut rowPos : Array (Array String) := #[]
  let mut rowDead : Array (Array String) := #[]
  let mut rowNone : Array (Array String) := #[]
  for i in [0:ws.rows.size] do
    let mut os : Array Nat := #[]
    let mut ps : Array String := #[]
    let mut ds : Array String := #[]
    let mut ns : Array String := #[]
    for s in srcs[i]! do
      match s with
      | .origin kind label lvl =>
        let k := s!"{i}|{label}"
        let idx ← match originIdx[k]? with
          | some idx => pure idx
          | none =>
            let idx := origins.size
            origins := origins.push { row := i, kind, label, lvl }
            originIdx := originIdx.insert k idx
            pure idx
        os := os.push idx
      | .pos key => unless ps.contains key do ps := ps.push key
      | .dead why => unless ds.contains why do ds := ds.push why
      | .none why => unless ns.contains why do ns := ns.push why
    rowOr := rowOr.push (dedupNat os); rowPos := rowPos.push ps; rowDead := rowDead.push ds; rowNone := rowNone.push ns
  -- the least fixpoint over the producer relation
  let mut byKey : Std.HashMap String (Array Nat) := {}
  for i in [0:ws.rows.size] do
    let k := rowKey ws.rows[i]!
    byKey := byKey.insert k ((byKey.getD k #[]).push i)
  let mut posOr : Std.HashMap String (Array Nat) := {}
  let mut rounds := 0
  let mut changed := true
  while changed && rounds < 64 do
    changed := false
    rounds := rounds + 1
    for p in cs.positions do
      let mut acc : Array Nat := #[]
      for i in byKey.getD p.key #[] do
        acc := acc ++ rowOr[i]!
        for q in rowPos[i]! do acc := acc ++ posOr.getD q #[]
      let acc2 := dedupNat acc
      if acc2 != posOr.getD p.key #[] then
        posOr := posOr.insert p.key acc2
        changed := true
  -- the tail at each origin: item 261's reading at the origin row, and the
  -- route's own level for a route
  let mut originLines : Array String := #[]
  let mut originHeld : Array Bool := #[]
  for o in origins, oi in [0:origins.size] do
    let r := ws.rows[o.row]!
    let holds := holdsOf env r.st
    let (atoms, var) := atomsOf prs[o.row]!.wits owns[o.row]!
    let hs := hits holds atoms var
    let v1 := if !hs.isEmpty then s!"held({String.intercalate "," hs.toList})" else if atoms.isEmpty then "level-var" else "none"
    -- the strict reading: a level the pack names (never a list variable's
    -- equality with a face's own list, which a frames-built pack has by
    -- construction)
    let hsS := hits holds atoms none
    let h2 : Array String := match o.lvl with | some l => hits holds [l] none | none => #[]
    let v2 : Option String := match o.lvl with
      | some l => some (if h2.isEmpty then s!"@{l}:none" else s!"@{l}:held({String.intercalate "," h2.toList})")
      | none => none
    let held := if o.kind == "route" && o.lvl.isSome then !h2.isEmpty else !hsS.isEmpty
    originHeld := originHeld.push held
    originLines := originLines.push s!"  O{oi} {short r.lem} #{r.occ} {rowKey r} ← {o.kind}({o.label}) lvl={o.lvl.getD "—"} ⊢ {v1}{match v2 with | some s => s!" | {s}" | none => ""} → {if held then "held" else "unheld"}"
  -- every row's resolution
  let mut rowLines : Array String := #[]
  let mut cnt : Std.HashMap String Nat := {}
  let bump (m : Std.HashMap String Nat) (k : String) : Std.HashMap String Nat := m.insert k (m.getD k 0 + 1)
  let mut perRows : Std.HashMap String (Array String) := {}
  for i in [0:ws.rows.size] do
    let r := ws.rows[i]!
    let pr := prs[i]!
    let clsHead := ((pr.cls.splitOn "(")[0]?).getD pr.cls
    let clsTag := if clsHead.startsWith "paid:" then clsHead
      else if clsHead.startsWith "via:" then "via" else if clsHead.startsWith "alt[" then "alt"
      else if clsHead.startsWith "relay:" then "relay" else if clsHead.startsWith "step" then "step"
      else if clsHead.startsWith "other" then "other" else clsHead
    let mut os0 := rowOr[i]!
    for q in rowPos[i]! do os0 := os0 ++ posOr.getD q #[]
    let os := dedupNat os0
    let nh := (os.filter fun oi => originHeld[oi]!).size
    let verdict :=
      if myCls[i]! != "built" then "—"
      else if os.isEmpty then
        if !rowDead[i]!.isEmpty then "dead"
        else if !rowPos[i]!.isEmpty then "unborn"
        else if rowNone[i]!.contains "stamp" then "stamp*"
        else if rowNone[i]!.contains "punt" then "punt*"
        else if rowNone[i]!.contains "absurd" then "absurd*"
        else if rowNone[i]!.contains "fact" then "fact*"
        else "unborn"
      else if nh == os.size then s!"all-held {nh}/{os.size}"
      else if nh == 0 then s!"none-held 0/{os.size}"
      else s!"some-held {nh}/{os.size}"
    let vTag := ((verdict.splitOn " ")[0]?).getD verdict
    cnt := bump cnt clsTag
    cnt := bump cnt s!"b:{myCls[i]!}"
    cnt := bump cnt s!"v:{vTag}"
    cnt := bump cnt s!"k:{r.kind}"
    let key := rowKey r
    if (posMap[key]!).packaged then cnt := bump cnt "packagedRows"
    perRows := perRows.insert key ((perRows.getD key #[]).push s!"{myCls[i]!} {vTag}")
    rowLines := rowLines.push s!"  {short r.lem} #{r.occ} {key} := {clsTag}/{myCls[i]!} pos=[{String.intercalate "," rowPos[i]!.toList}] origins=[{String.intercalate "," (os.map fun o => s!"O{o}").toList}]{if rowDead[i]!.isEmpty then "" else s!" dead=[{String.intercalate "," rowDead[i]!.toList}]"}{if rowNone[i]!.isEmpty then "" else s!" none=[{String.intercalate "," rowNone[i]!.toList}]"} ⊢ {verdict}"
  -- per position
  let mut perLines : Array String := #[]
  let mut unbornLines : Array String := #[]
  for p in cs.positions do
    let xs := perRows.getD p.key #[]
    let c (s : String) := (xs.filter fun x => (x.splitOn " ")[0]! == s).size
    let v (s : String) := (xs.filter fun x => (x.splitOn " ")[1]! == s).size
    let os := posOr.getD p.key #[]
    let nh := (os.filter fun oi => originHeld[oi]!).size
    let touched := xs.size - c "punt" - c "stamp"
    let verdict := if touched == 0 then "punt-only" else if os.isEmpty then (if v "dead" > 0 then "dead" else if v "unborn" > 0 then "unborn" else "relayed-punts") else s!"{nh}/{os.size} held"
    perLines := perLines.push s!"  {p.key}{if p.packaged then " packaged" else ""} writers={xs.size} punt={c "punt"} stamp={c "stamp"} built={c "built"} unborn={v "unborn"} dead={v "dead"} allHeld={v "all-held"} someHeld={v "some-held"} noneHeld={v "none-held"} origins=[{String.intercalate "," (os.map fun o => s!"O{o}").toList}] ⊢ {verdict}"
    if verdict == "unborn" then unbornLines := unbornLines.push s!"  {p.key} writers={xs.size} punt={c "punt"}"
  let g (k : String) := cnt.getD k 0
  let originRows := (dedupNat (origins.map (·.row))).size
  let okind (k : String) := (origins.filter fun o => o.kind == k).size
  let heldO := (originHeld.filter id).size
  let packL := ((pe.packConsts.toArray.map short).qsort (· < ·)).toList
  let line := s!"positions={cs.positions.size} packaged={(cs.positions.filter (·.packaged)).size} packConsts=[{String.intercalate "," packL}] rows={ws.rows.size} ctorRows={g "k:ctor"} paramRows={g "k:param"} packagedRows={g "packagedRows"} punt={g "b:punt"} stamp={g "b:stamp"} built={g "b:built"} origins={origins.size} originRows={originRows} route={okind "route"} frames={okind "frames"} tail={okind "tail"} other={okind "other"} concl={okind "concl"} invariant={okind "invariant"} heldOrigins={heldO} allHeld={g "v:all-held"} someHeld={g "v:some-held"} noneHeld={g "v:none-held"} unbornRows={g "v:unborn"} relayedPunt={g "v:punt*"} relayedStamp={g "v:stamp*"} relayedAbsurd={g "v:absurd*"} relayedFact={g "v:fact*"} deadRows={g "v:dead"} unbornPos={unbornLines.size} rounds={rounds} follows={follows} lets={ws.lets.size} lapps={ws.lapps.size} alts={ws.alts.size} nodes={ws.nodes} liteNodes={ws.liteNodes}"
  logInfo s!"ValueLineOrigins {line}"
  logInfo s!"positions:\n{String.intercalate "\n" (cs.positions.map fun p => "  " ++ p.line).toList}"
  logInfo s!"origins:\n{String.intercalate "\n" originLines.toList}"
  logInfo s!"rows:\n{String.intercalate "\n" rowLines.toList}"
  logInfo s!"perPos:\n{String.intercalate "\n" perLines.toList}"
  logInfo s!"unborn:\n{String.intercalate "\n" unbornLines.toList}"
  -- Item 409 (2026-10-30): 42 → 41 — `explFrameValueLine.h_kslot` is gone with the lemma.
  -- 2026-10-31 (item 412): 41 → 43 — the entry-shaped `pendingMapValue.h_expl` (ctor) and its consumer param position, as ValueLinePacks pins.
  -- 2026-10-31 (item 413): 43 → 44 — `compact_open_map.h_chainUp`, the opener's relay parameter (ValueLinePacks params 31 → 32).
  unless (cs.positions.filter (!·.packaged)).size == 44 do throwError "item 261's positions moved under this pass: {(cs.positions.filter (!·.packaged)).size}"
  unless origins.size > 0 do throwError "no origin resolved"
  unless pinned do return
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedPositions" (cs.positions.map (·.line)) expectedPositions
  check "expectedOrigins" originLines expectedOrigins
  check "expectedRows" rowLines expectedRows
  check "expectedPerPos" perLines expectedPerPos
  check "expectedUnborn" unbornLines expectedUnborn
  unless line == expectedLine do
    throwError "ValueLineOrigins moved:\n  got      {line}\n  expected {expectedLine}"

end Tests.Guards.ValueLineOrigins
