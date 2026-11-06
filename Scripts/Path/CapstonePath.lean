module

public import Lean.Environment
public import Lean.PrivateName
public import Lean.Util.FoldConsts
public import Lean.Meta.Match.MatcherInfo
public import Std.Data.HashSet
public import Std.Data.HashMap
public meta import Std.Data.HashSet.Basic

@[expose] public section Blanket

/-!
# Scripts.Path.CapstonePath — the `∨ True` audit's positions, ON or OFF the capstone's path

DOCS item 439 ((ω-path)).  A `P ∨ True` cannot make the capstone unsound, only weak; the
risk the owner refuses to carry is the set of positions whose vacuous arm weakens a fact the
capstone actually consumes.  This module is the pure classifier: it takes

* the `∨ True` audit's pinned tables (`Tests/Guards/Proofs/OrTrueAudit.lean`:
  `expectedPositions`, `expectedSupply`, `expectedConsumers`), and
* the set of constants the capstone reaches — the transitive closure, through types and
  values, of what `DocumentProduction.scan_strict_proof` / `parse_strict_proof` use
  (`reach`), the only two capstones that import `StreamAccum`,

and classes every position:

| class | meaning |
|---|---|
| `on-spent` | top binder of a reached lemma whose own proof cases on the disjunction (`cased>0`) |
| `on-relayed` | top binder of a reached lemma passed on whole (`passed>0`, never cased) |
| `on-field` | constructor field of a reached inductive — read by the reached lemmas that case on the park |
| `on-conclusion` | the `[ret]` of a reached lemma — the fact it hands its callers is the weakened one |
| `on-nested` | a `∨` inside a binder's statement of a reached declaration |
| `on-other` | a reached top position outside the supply/consumer tables (another module) |
| `off-unread` | top binder of a reached lemma whose proof never reads the binder (`cased=0 passed=0`, value readable) |
| `off-unreached` | the declaration is not in the capstone's closure |

`on-*` is the owner's ON set; `off-*` is residue by class.  The guard
`Tests/Guards/Proofs/CapstonePathAudit.lean` pins the reading off the elaborated environment;
`lake run capstone-path` (`Scripts/Main/CapstonePath.lean`) recomputes it off the built
`.olean`s and the audit file's text and prints it.
-/

open Lean

namespace Scripts.Path.CapstonePath

/-- The capstones that consume `StreamAccum`. -/
def roots : List Name :=
  [`L4YAML.Proofs.DocumentProduction.scan_strict_proof,
   `L4YAML.Proofs.DocumentProduction.parse_strict_proof]

/-- What a declaration's type and value mention. -/
def rawRefs (env : Environment) (n : Name) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let v := (ci.value? (allowOpaque := true)).map (·.getUsedConstants) |>.getD #[]
    ci.type.getUsedConstants ++ v

/-- The transitive closure of `roots` through types and values. -/
partial def reach (env : Environment) (roots : List Name) : Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut todo : List Name := roots
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    todo := (rawRefs env n).toList ++ todo
  return seen

/-- How many of the module's authored constants the closure holds, of how many it has. -/
def moduleReach (env : Environment) (r : Std.HashSet Name) (ns : Name) : Nat × Nat :=
  env.constants.fold (init := (0, 0)) fun (a, t) n _ =>
    if ns.isPrefixOf n && !n.isInternal && !(privateToUserName n).isInternal then
      (if r.contains n then a + 1 else a, t + 1)
    else (a, t)

/-- The user-facing spellings of a reached set (private names unwrapped), as the audit shows them. -/
def shownSet (r : Std.HashSet Name) : Std.HashSet String :=
  r.fold (fun acc n => acc.insert (privateToUserName n).toString) {}

/-- One audit position, parsed from its pinned line `DECL[site] kind ∨ alt`. -/
structure Pos where
  decl : String
  site : String
  kind : String
  alt : String
deriving Repr, Inhabited

def parsePos (line : String) : Option Pos := do
  let [declSite, kind, "∨", alt] := line.splitOn " " | none
  match declSite.toList.findIdx? (· == '[') with
  | some i =>
    some { decl := String.ofList (declSite.toList.take i), site := String.ofList (declSite.toList.drop i),
           kind := kind, alt := alt }
  | none =>
    -- a `Prop` definition's body: the audit shows it as `DECLbody`
    if declSite.endsWith "body" then
      some { decl := String.ofList (declSite.toList.take (declSite.length - 4)), site := "body", kind := kind, alt := alt }
    else none

/-- `DECL[site] class [k=v …]` → (`DECL[site]`, class, the bracket's `k=v` pairs). -/
def parseClassed (line : String) : Option (String × String × List (String × Nat)) := do
  let declSite :: cls :: rest := line.splitOn " " | none
  let bracket := String.ofList ((" ".intercalate rest).toList.dropWhile (· == '[')
    |>.reverse.dropWhile (· == ']') |>.reverse)
  let kvs := (bracket.splitOn " ").filterMap fun kv =>
    match kv.splitOn "=" with
    | [k, v] => v.toNat?.map (k, ·)
    | _ => none
  some (declSite, cls, kvs)

/-- A declaration is on the path when the closure holds it, or — for a constructor — its
    inductive or the inductive's eliminators (a park is read by `casesOn`, not by its `mk`). -/
def declReached (shown : Std.HashSet String) (decl : String) : Bool :=
  shown.contains decl ||
    (let pre := (decl.splitOn ".").dropLast
     let ind := ".".intercalate pre
     shown.contains ind || shown.contains s!"{ind}.casesOn" || shown.contains s!"{ind}.rec")


/-- The β.5 deletion set (step 12.4): `scannerDrop` and its two construction sites (`dropClose`,
    `close_with_ssl`'s `pendingFlow` arm), the `pendingFlow` park, and the escape with its twins. -/
def dropSet : List Name :=
  [`L4YAML.Surface.SLYamlStream.scannerDrop,
   `L4YAML.Proofs.StreamAccum.dropClose,
   `L4YAML.Proofs.StreamAccum.PendingNode.pendingFlow,
   `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline]

def saNs : Name := `L4YAML.Proofs.StreamAccum

def isVacuousTy (t : Expr) : Bool :=
  let t := t.consumeMData
  t.isConstOf ``True || t.isAppOf `L4YAML.Proofs.StreamAccum.PackAlt ||
    t.isAppOf `L4YAML.Proofs.StreamAccum.PackAltG

/-- A `casesOn`-shaped arm on a vacuous alternative: the position it was read from (`root`),
    the lemma that reads it, and how the arm closes — `drop` (mentions the deletion set),
    `via` (its StreamAccum closure does), `relay` (writes an `Or.inr` on), `honest`. -/
structure Arm where
  consumer : Name
  root : String
  cls : String
  witness : String
deriving Repr, Inhabited

/-- `consumer` hands the fact rooted at `src` whole to the audit position `dst`. -/
structure Relay where
  consumer : Name
  src : String
  dst : String
  /-- `whole` (the hypothesis handed on) or `decline` (an `Or.inr` written inside `src`'s vacuous arm). -/
  kind : String := "whole"
deriving Repr, Inhabited

structure Walk where
  unrooted : Array String := #[]
  casings : Std.HashMap Name Nat := {}
  matchersInlined : Nat := 0
  dbgName : Option Name := none
  dbg : Array String := #[]
  matchersOpaque : Nat := 0
  matchersLabelled : Nat := 0
  labelled : Nat := 0
  arms : Array Arm := #[]
  relays : Array Relay := #[]
  touches : Std.HashMap Name Bool := {}
  seen : Std.HashSet (Expr × Nat) := {}
  levels : Std.HashMap Expr Nat := {}
  steps : Nat := 0
  levelSteps : Nat := 0
  refSteps : Nat := 0
  budget : Nat := 400000000
  binders : Std.HashMap Name (Array (String × Option Name)) := {}

/-- A root: the audit key of the binder / field the fact came from, and its type's head. -/
abbrev Root := String × Option Name

def shownName (n : Name) : String := (privateToUserName n).toString

/-- The binder keys `DECL[i].name` of a constant's type, with each binder's type head. -/
def binderKeysOf (env : Environment) (c : Name) : Array (String × Option Name) := Id.run do
  let some ci := env.find? c | return #[]
  let mut t := ci.type
  let mut out : Array (String × Option Name) := #[]
  let mut i := 0
  repeat
    match t with
    | .forallE n ty b _ =>
      out := out.push (s!"{shownName c}[{i}].{n.eraseMacroScopes}", ty.getAppFn.constName?)
      t := b; i := i + 1
    | _ => break
  return out

def binderKeys (env : Environment) (c : Name) : StateM Walk (Array (String × Option Name)) := do
  if let some b := (← get).binders.get? c then return b
  let b := binderKeysOf env c
  modify fun w => { w with binders := w.binders.insert c b }
  return b

/-- Does the StreamAccum closure of `n` meet the drop set?  Memoised; a cycle reads `false`. -/
partial def touchesDrop (env : Environment) (drop : Std.HashSet Name) (n : Name) :
    StateM Walk Bool := do
  if drop.contains n then return true
  if let some b := (← get).touches.get? n then return b
  modify fun w => { w with touches := w.touches.insert n false, refSteps := w.refSteps + 1 }
  if (← get).refSteps > (← get).budget then return false
  let mut r := false
  if saNs.isPrefixOf n then
    for c in rawRefs env n do
      if ← touchesDrop env drop c then
        r := true
        break
  modify fun w => { w with touches := w.touches.insert n r }
  return r

/-- How a subterm closes, memoised per subterm: 3 = mentions the deletion set, 2 = mentions a
    constant whose StreamAccum closure does, 1 = writes an `Or.inr`, 0 = none of these. -/
partial def levelOf (env : Environment) (drop : Std.HashSet Name) (e : Expr) : StateM Walk Nat := do
  if let some l := (← get).levels.get? e then return l
  modify fun w => { w with levelSteps := w.levelSteps + 1 }
  if (← get).levelSteps > (← get).budget then return 0
  let l ← match e with
    | .const c _ =>
      if drop.contains c then pure 3
      else if ← touchesDrop env drop c then pure 2
      else pure 0
    | .app f a => do let x ← levelOf env drop f; if x == 3 then pure 3 else pure (max x (← levelOf env drop a))
    | .lam _ t b _ | .forallE _ t b _ => do
      let x ← levelOf env drop t; if x == 3 then pure 3 else pure (max x (← levelOf env drop b))
    | .letE _ t v b _ => do
      let x ← levelOf env drop t; let y ← levelOf env drop v; let z ← levelOf env drop b; pure (max x (max y z))
    | .mdata _ b | .proj _ _ b => levelOf env drop b
    | _ => pure 0
  modify fun w => { w with levels := w.levels.insert e l }
  return l

def armClass (env : Environment) (drop : Std.HashSet Name) (body : Expr) :
    StateM Walk (String × String) := do
  match ← levelOf env drop body with
  | 3 => return ("drop", "")
  | 2 => return ("via", "")
  | _ => return ("honest", "")

def ctorFields (env : Environment) (ctor : Name) : Option (Nat × Array (String × Option Name)) :=
  match env.find? ctor with
  | some (.ctorInfo cv) =>
    let ks := binderKeysOf env ctor
    some (cv.numParams, ks.extract cv.numParams (cv.numParams + cv.numFields))
  | _ => none

/-- Casts a hypothesis passes through unchanged: the root is the last argument's. -/
def isCast (c : Name) : Bool :=
  c == ``Eq.mp || c == ``Eq.mpr || c == ``cast || c == ``id || c == ``Eq.ndrec || c == ``Eq.rec ||
    c == ``Eq.subst || c == ``HEq.ndrec || c == ``Function.comp ||
    -- a reshaped disjunction keeps its vacuous arm: `h.imp f id`, `h.imp_left f`
    c == ``Or.imp || c == ``Or.imp_left || c == ``Or.imp_right

/-- A cast's arity and the index of the term it transports. -/
def castShape (c : Name) : Option (Nat × Nat) :=
  if c == ``Eq.rec || c == ``Eq.ndrec || c == ``HEq.ndrec then some (6, 3)
  else if c == ``Eq.subst then some (6, 5)
  else if c == ``Eq.mp || c == ``Eq.mpr || c == ``cast then some (4, 3)
  else if c == ``id then some (2, 1)
  else none

/-- The root an expression stands for: a labelled bound variable, applied or projected; a
    constant's application stands for that constant's conclusion (`DECL[ret]`), when the audit
    lists it. -/
partial def rootOf (env : Environment) (keys : Std.HashSet String) (rets : Std.HashSet Name)
    (ctx : Array (Option Root)) (e : Expr) : Option Root :=
  let e := e.consumeMData
  match e with
  | .bvar k => (ctx[ctx.size - 1 - k]?).join
  | .app .. =>
    let f := e.getAppFn
    match f with
    | .const c _ =>
      if isCast c then
        let args := e.getAppArgs
        -- `Eq.rec` / `Eq.ndrec` transport their fourth argument; the other casts their last
        let src := if (c == ``Eq.rec || c == ``Eq.ndrec) && args.size ≥ 6 then args[3]? else args.back?
        src >>= rootOf env keys rets ctx
      else if rets.contains c then some (s!"{shownName c}[ret]", none) else none
    | _ => rootOf env keys rets ctx f
  | .const c _ => if rets.contains c then some (s!"{shownName c}[ret]", none) else none
  | .proj s i x => do
    let (r, _) ← rootOf env keys rets ctx x
    match env.find? s with
    | some (.inductInfo iv) =>
      match iv.ctors.head? >>= ctorFields env with
      | some (_, fs) => match fs[i]? with
        | some (k, h) => if keys.contains k then some (k, h) else some (r, none)
        | none => some (r, none)
      | none => some (r, none)
    | _ => some (r, none)
  | _ => none

def isCasing (env : Environment) (c : Name) : Bool :=
  !(`Eq).isPrefixOf c && !(`HEq).isPrefixOf c && (c == ``Or.elim || Lean.Meta.isMatcherCore env c ||
    (match c with
     | .str _ s => s == "casesOn" || s == "rec" || s == "recOn" || s == "ndrec"
     | _ => false))

/-- The inductive a matcher's motive eliminates: the head of the motive's last binder type. -/
def matcherInductive (env : Environment) (c : Name) (mi : Lean.Meta.MatcherInfo) : Option Name := Id.run do
  let some ci := env.find? c | return none
  let mut t := ci.type
  for _ in [0:mi.numParams] do
    match t with
    | .forallE _ _ b _ => t := b
    | _ => return none
  let .forallE _ motiveTy _ _ := t | return none
  let mut m := motiveTy
  let mut last : Option Expr := none
  repeat
    match m with
    | .forallE _ ty b _ => last := some ty; m := b
    | _ => break
  return last >>= fun ty => ty.getAppFn.constName?

/-- A matcher whose body is not exported: when it eliminates a single discriminant of an
    inductive whose constructors the alternatives enumerate in order, the alternatives' leading
    binders are the constructors' fields. -/
def matcherAltLabels (env : Environment) (c : Name) (mi : Lean.Meta.MatcherInfo) :
    Option (Array (Nat × Name)) := do
  guard (mi.numDiscrs == 1)
  let ind ← matcherInductive env c mi
  let .inductInfo iv ← env.find? ind | none
  guard (iv.ctors.length == mi.altNumParams.size)
  let ctors := iv.ctors.toArray
  let start := mi.numParams + 1 + mi.numDiscrs
  let mut out : Array (Nat × Name) := #[]
  for h : k in [0:ctors.size] do
    let some (.ctorInfo cv) := env.find? ctors[k] | none
    guard (mi.altNumParams[k]! ≥ cv.numFields)
    out := out.push (start + k, ctors[k])
  return out

/-- The minor premises of a casing application, with the constructor each binds. -/
def minorsOf (env : Environment) (c : Name) (args : Array Expr) : Array (Nat × Option Name) := Id.run do
  if (`Eq).isPrefixOf c || (`HEq).isPrefixOf c then return #[]
  if c == ``Or.elim then return #[(4, some ``Or.inl), (5, some ``Or.inr)]
  match c with
  | .str ind "casesOn" =>
    match env.find? ind with
    | some (.inductInfo iv) =>
      let start := iv.numParams + 1 + iv.numIndices + 1
      return (iv.ctors.toArray.zipIdx.map fun (ct, j) => (start + j, some ct)).filter (·.1 < args.size)
    | _ => return #[]
  | .str ind "rec" =>
    match env.find? ind, env.find? c with
    | some (.inductInfo iv), some (.recInfo rv) =>
      let start := rv.numParams + rv.numMotives
      return (iv.ctors.toArray.zipIdx.map fun (ct, j) => (start + j, some ct)).filter (·.1 < args.size)
    | _, _ => return #[]
  | _ => return #[]

/-- Walk a value: label the bound variables that stand for audit positions, record every
    vacuous arm read off a labelled root and every whole relay of a labelled root into an
    audit position of a callee. -/
partial def walk (env : Environment) (drop : Std.HashSet Name) (keys : Std.HashSet String)
    (rets : Std.HashSet Name) (self : Name) (arm : Option String) (ctx : Array (Option Root)) (e : Expr) :
    StateM Walk Unit := do
  if (← get).seen.contains (e, ctx.size) then return
  modify fun w => { w with seen := w.seen.insert (e, ctx.size), steps := w.steps + 1 }
  if (← get).steps > (← get).budget then return
  match e with
  | .app .. =>
    let e := e.headBeta
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const c _ =>
      -- an over-applied cast applies its transported term to the extra arguments: `subst`'s
      -- re-binding of the fields.  Read it as that application, so the labels carry over.
      if let some (arity, srcIdx) := castShape c then
        if args.size > arity then
          if let some src := args[srcIdx]? then
            walk env drop keys rets self arm ctx (mkAppN src (args.extract arity args.size)).headBeta
            for h : i in [0:arity] do
              if i != srcIdx then walk env drop keys rets self arm ctx args[i]!
            return
      let mut matcherMinors : Array (Nat × Option Name) := #[]
      if Lean.Meta.isMatcherCore env c then
        if let some v := (env.find? c).bind (·.value?) then
          modify fun w => { w with matchersInlined := w.matchersInlined + 1 }
          walk env drop keys rets self arm ctx (v.beta args)
          return
        modify fun w => { w with matchersOpaque := w.matchersOpaque + 1 }
        if let some mi := Lean.Meta.getMatcherInfoCore? env c then
          if let some ls := matcherAltLabels env c mi then
            modify fun w => { w with matchersLabelled := w.matchersLabelled + 1 }
            matcherMinors := ls.map fun (i, ct) => (i, some ct)
      -- whole relays into a callee's audit positions
      let rooted (a : Expr) : Option Root := rootOf env keys rets ctx a
      let bks ← binderKeys env c
      for h : i in [0:args.size] do
        if let some (k, _) := bks[i]? then
          if keys.contains k then
            if let some (r, _) := rooted args[i] then
              if k != r then
                modify fun w => { w with relays := w.relays.push { consumer := self, src := r, dst := k } }
            else if args[i].consumeMData.isAppOf ``Or.inr then
              if let some a := arm then
                modify fun w => { w with relays := w.relays.push { consumer := self, src := a, dst := k, kind := "decline" } }
      let minors := if matcherMinors.isEmpty then minorsOf env c args else matcherMinors
      if (match c with | .str _ s => s == "casesOn" || s == "rec" | _ => false) then
        modify fun w => { w with casings := w.casings.insert c (w.casings.getD c 0 + 1) }
      let major? := if isCasing env c then args.findSome? rooted else none
      let vacuousMinor := args.any fun a => match a with | .lam _ t _ _ => isVacuousTy t | _ => false
      if isCasing env c && major?.isNone && vacuousMinor && (c == ``Or.casesOn || c == ``Or.elim || c == ``Or.rec) then
        let majIdx := if c == ``Or.rec then 5 else 3
        let desc := match args[majIdx]? with
          | some a => match a.consumeMData.getAppFn with
            | .const d _ => s!"const {shownName d}"
            | .bvar k => s!"bvar {k} (unlabelled)"
            | .proj sn i _ => s!"proj {sn}.{i}"
            | .lam .. => "lam" | .letE .. => "let" | .fvar .. => "fvar" | .mvar .. => "mvar"
            | .mdata .. => "mdata" | .sort .. => "sort" | .forallE .. => "forall" | .lit .. => "lit" | .app .. => "app"
          | none => "missing"
        modify fun w => { w with unrooted := w.unrooted.push s!"{shownName self}: {c} on {desc}" }
      if (← get).dbgName == some self && (c.toString.endsWith "casesOn" || c.toString.startsWith "L4YAML.Proofs.StreamAccum.accum_block_on") then
        let rootedArgs := (List.range args.size).filterMap fun i => (rooted args[i]!).map fun r => s!"{i}:{r.1}"
        let argHeads := (List.range args.size).map fun i => match args[i]!.consumeMData.getAppFn with
          | .bvar k => s!"b{k}" | .const d _ => s!"c:{d}" | .lam .. => "λ" | _ => "?"
        let casts := (List.range args.size).filterMap fun i =>
          let a := args[i]!.consumeMData
          match a.getAppFn with
          | .const d _ => if isCast d then
              let src := a.getAppArgs.back?
              some s!"{i}:{d}/{a.getAppArgs.size} src={src.map fun x => match x.consumeMData.getAppFn with | .bvar k => s!"b{k}" | .const e _ => s!"c:{e}" | _ => "?"} root={src.bind (rootOf env keys rets ctx)}"
            else none
          | _ => none
        let labels := (List.range ctx.size).filterMap fun j => (ctx[j]!).map fun r => s!"{j}:{r.1.drop 42 |>.toString}"
        modify fun w => { w with dbg := w.dbg.push s!"{c} depth={ctx.size} minors={minors.size} major?={major?.map (·.1)} rooted={rootedArgs} heads={argHeads} casts={casts} labels={labels}" }
      let keyedMinors := minors.any fun (_, ct) => match ct >>= ctorFields env with
        | some (_, fs) => fs.any (fun (k, _) => keys.contains k)
        | none => false
      if major?.isSome || keyedMinors then
        for h : i in [0:args.size] do
          match minors.find? (·.1 == i) with
          | some (_, ct) =>
            -- a minor premise: its binders are the constructor's fields
            let labels : Array (Option Root) :=
              match ct >>= ctorFields env with
              | some (_, fs) =>
                if fs.any (fun (k, _) => keys.contains k) then
                  fs.map (fun (k, h) => some (k, h))
                else fs.map fun _ => major?
              | none => #[]
            let mut arm' := arm
            if labels.any (fun l => l.any fun (k, _) => keys.contains k) then
              modify fun w => { w with labelled := w.labelled + 1 }
            if let some root := major? then
              if let .lam _ t _ _ := args[i] then
                if isVacuousTy t then
                  let body := (args[i].bindingBody!)
                  let (cls, wit) ← armClass env drop body
                  modify fun w => { w with arms := w.arms.push { consumer := self, root := root.1, cls := cls, witness := wit } }
                  if let some th := root.2 then
                    let bk := s!"{shownName th}body"
                    if keys.contains bk then
                      modify fun w => { w with arms := w.arms.push { consumer := self, root := bk, cls := cls, witness := wit } }
                  arm' := some root.1
            walkLam env drop keys rets self arm' ctx labels.toList major? args[i]
          | none => walk env drop keys rets self arm ctx args[i]
      else
        for a in args do walk env drop keys rets self arm ctx a
    | _ =>
      walk env drop keys rets self arm ctx f
      for a in args do walk env drop keys rets self arm ctx a
  | .lam _ t b _ => do
    walk env drop keys rets self arm ctx t
    walk env drop keys rets self arm (ctx.push none) b
  | .forallE _ t b _ => do
    walk env drop keys rets self arm ctx t
    walk env drop keys rets self arm (ctx.push none) b
  | .letE _ t v b _ => do
    walk env drop keys rets self arm ctx t
    walk env drop keys rets self arm ctx v
    walk env drop keys rets self arm (ctx.push (rootOf env keys rets ctx v)) b
  | .mdata _ e => walk env drop keys rets self arm ctx e
  | .proj _ _ e => walk env drop keys rets self arm ctx e
  | _ => pure ()
where
  /-- Peel a minor premise's lambdas, labelling each binder (the fields), the rest inheriting the root. -/
  walkLam (env : Environment) (drop : Std.HashSet Name) (keys : Std.HashSet String)
      (rets : Std.HashSet Name) (self : Name) (arm : Option String) (ctx : Array (Option Root))
      (labels : List (Option Root)) (root : Option Root) (e : Expr) : StateM Walk Unit := do
    match e, labels with
    | .lam _ t b _, l :: ls =>
      walk env drop keys rets self arm ctx t
      walkLam env drop keys rets self arm (ctx.push l) ls root b
    | .lam _ t b _, [] =>
      walk env drop keys rets self arm ctx t
      walkLam env drop keys rets self arm (ctx.push none) [] root b
    | e, _ => walk env drop keys rets self arm ctx e

/-- The ret-rooted constants: those whose `DECL[ret]` the audit lists. -/
def retsOf (decls : Array Name) (keys : Std.HashSet String) : Std.HashSet Name :=
  decls.foldl (init := {}) fun acc n =>
    if keys.contains s!"{shownName n}[ret]" then acc.insert n else acc

/-- Walk one constant's value (a leading lambda per type binder, else skipped). -/
def walkDecl (env : Environment) (drop : Std.HashSet Name) (keys : Std.HashSet String)
    (rets : Std.HashSet Name) (w : Walk) (n : Name) : Walk := Id.run do
  let some ci := env.find? n | return w
  let some v := ci.value? (allowOpaque := true) | return w
  let bks := binderKeysOf env n
  let mut body := v
  let mut ctx : Array (Option Root) := #[]
  for (k, h) in bks do
    match body with
    | .lam _ _ b _ =>
      ctx := ctx.push (if keys.contains k then some (k, h) else none)
      body := b
    | _ => return w
  let (_, w') := (walk env drop keys rets n none ctx body).run { w with seen := {}, levels := {} }
  -- a premise the value uses may reach the lemma's own vacuous conclusion
  let retKey := s!"{shownName n}[ret]"
  if !keys.contains retKey then return w'
  let total := ctx.size
  let mut w'' := w'
  for h : i in [0:total] do
    if let some (k, _) := ctx[i] then
      if body.hasLooseBVar (total - 1 - i) then
        w'' := { w'' with relays := w''.relays.push { consumer := n, src := k, dst := retKey } }
  return w''

/-- Walk every constant of `decls`. -/
def walkAll (env : Environment) (drop : Std.HashSet Name) (keys : Std.HashSet String)
    (decls : Array Name) : Walk :=
  let rets := retsOf decls keys
  decls.foldl (walkDecl env drop keys rets) {}

structure Classed where
  pos : Pos
  cls : String
  declines : Nat
deriving Repr, Inhabited

def Classed.line (c : Classed) : String :=
  s!"{c.pos.decl}{c.pos.site} {c.pos.kind} ∨ {c.pos.alt} {c.cls}" ++
    (if c.declines > 0 then s!" DECLINE={c.declines}" else "")

/-- The reading: every position classed, in the audit's order.  `arms` / `relays` come from
    `walkAll`; a position is ON when one of its vacuous arms closes through the deletion set
    (`drop` / `via`) or it is relayed, to a fixpoint, into such a position. -/
def classify (shown : Std.HashSet String) (positions supply consumers : List String)
    (arms : Array Arm) (relays : Array Relay) : Array Classed := Id.run do
  let mut armCls : Std.HashMap String (Array String) := {}
  for a in arms do armCls := armCls.insert a.root ((armCls.getD a.root #[]).push a.cls)
  let hasArm (k cls : String) := (armCls.getD k #[]).contains cls
  let mut on : Std.HashSet String := {}
  for (k, cs) in armCls.toList do
    if cs.contains "drop" || cs.contains "via" then on := on.insert k
  let mut relayed : Std.HashSet String := {}
  let mut changed := true
  while changed do
    changed := false
    for r in relays do
      if on.contains r.dst && !on.contains r.src then
        on := on.insert r.src
        relayed := relayed.insert r.src
        changed := true
  let mut cons : Std.HashMap String (String × List (String × Nat)) := {}
  for l in consumers do
    if let some (k, c, kvs) := parseClassed l then cons := cons.insert k (c, kvs)
  let mut decl : Std.HashMap String Nat := {}
  for l in supply do
    if let some (k, _, kvs) := parseClassed l then
      decl := decl.insert k ((kvs.find? (·.1 == "DECLINE")).map (·.2) |>.getD 0)
  let mut out : Array Classed := #[]
  for l in positions do
    let some p := parsePos l | continue
    let key := s!"{p.decl}{p.site}"
    let isCtor := (p.decl.splitOn ".").getLast? == some "mk" ||
      (match cons.get? key with | some ("unreadable", _) => true | _ => false)
    let _ := isCtor
    let _ := cons
    let cls :=
      if !declReached shown p.decl then "off-unreached"
      else if p.site == "[ret]" then (if on.contains key then "on-conclusion" else "off-conclusion")
      else if hasArm key "drop" then "on-drop"
      else if hasArm key "via" then "on-via"
      else if relayed.contains key then "on-relay"
      else if hasArm key "honest" then "off-honest"
      else "off-unread"
    out := out.push { pos := p, cls := cls, declines := decl.getD key 0 }
  return out

def count (cs : Array Classed) (f : Classed → Bool) : Nat := (cs.filter f).size

/-- The one-line summary the guard pins. -/
def summary (cs : Array Classed) (consumed : List String) (saReached saTotal : Nat) (unrooted : Nat := 0) : String :=
  let classes := ["on-drop", "on-via", "on-relay", "on-conclusion",
                  "off-honest", "off-unread", "off-conclusion", "off-unreached"]
  let byCls := " ".intercalate (classes.map fun c => s!"{c}={count cs (·.cls == c)}")
  let on := cs.filter (·.cls.startsWith "on-")
  let off := cs.filter (·.cls.startsWith "off-")
  let byAlt (xs : Array Classed) (a : String) := (xs.filter (·.pos.alt == a)).size
  -- a nested position shares its top binder's key: count the DECLINE edges once, at the top
  let decl (xs : Array Classed) := (xs.filter (·.pos.kind == "top")).foldl (· + ·.declines) 0
  s!"positions={cs.size} on={on.size} off={off.size} {byCls} " ++
  s!"on-by-alt: True={byAlt on "True"} PackAlt={byAlt on "PackAlt"} PackAltG={byAlt on "PackAltG"} " ++
  s!"off-by-alt: True={byAlt off "True"} PackAlt={byAlt off "PackAlt"} PackAltG={byAlt off "PackAltG"} " ++
  s!"pack-declines: on={decl (on.filter (·.pos.alt != "True"))} off={decl (off.filter (·.pos.alt != "True"))} " ++
  s!"consumed={",".intercalate consumed} streamAccum-reached={saReached}/{saTotal} unrooted-arms={unrooted}"

/-- The ON roster grouped by declaration: `DECL: site alt class, …`. -/
def families (cs : Array Classed) : Array String := Id.run do
  let on := cs.filter (·.cls.startsWith "on-")
  let mut order : Array String := #[]
  let mut m : Std.HashMap String (Array String) := {}
  for c in on do
    if !m.contains c.pos.decl then order := order.push c.pos.decl
    m := m.insert c.pos.decl ((m.getD c.pos.decl #[]).push s!"{c.pos.site} ∨ {c.pos.alt} {c.cls}")
  return order.map fun d => s!"{d}: {"; ".intercalate (m.getD d #[]).toList}"

end Scripts.Path.CapstonePath
