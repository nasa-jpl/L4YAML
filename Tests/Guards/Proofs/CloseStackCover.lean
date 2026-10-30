/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.CloseSplitFrames

/-!
# How many of the resume stacks the eight receive carry the cover paid (DOCS item 253)

Item 252 found the content park's four closes holding a resume stack whose
cover stands two options deep, and the entry park's four holding none.  A
paid cover is what turns a membership miss into a refutation: with
`IndentStackCover.Covered lo ks sc` and `Floor lo n ks` in hand, a landing
below the park's index that moved the scanner's stack is in `ks` or on a
sequence level (`preprocess_landing_mem_or_seq`), and a `:` or `?` at a
sequence level's column is refused.  This module asks where that cover is
paid, and whether a payment reaches the eight.

**§1** finds every position a cover can be paid at: the `PendingNode` fields
whose type mentions the cover, and the parameters of every L4YAML theorem
that do — the cover algebra's own theorems excepted, whose conclusions carry
the cover they take and which a payment passes through — each with the path
from the position's type to its cover option.  **§2** reads, at every
application of a park constructor or of such a lemma in the proof terms of
the library, what stands at each cover-carrying position: a punt, a literal
payment naming its floor and the proof of its cover, or a relay of a
parameter, of a park field bound at a door, of a local or of a destructured
value, with the cover kept, stepped or dropped — following the type's path
through the term, and through `match`, `cases`, `Or.imp` and `obtain` with
the source's name carried onto its pieces.  The walk is syntactic: a binder
stack in place of a local context, casts applied past their arity
beta-reduced so the variables `cases` and `subst` re-introduce are the
originals.  **§3** follows the relays backwards from the stack the content
park's four closes hold, from the entry park's field, from the value slot's
relay and from the mapping value park's field, to their leaves.  **§4**
reads, at the eight, the facts a refutation would spend beside the cover: a
fact about the scanner's stack, a bound on its top, the floor.  **§5** reads
what the accumulation doors do with each cover-carrying field: hand it to a
position that carries a cover, to one that does not, or bind it and drop it.
A relay is credited nothing of its own; only a literal payment at a leaf
counts, and a decision on a membership counts for nothing here at all.
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
open Tests.Guards.CloseLandingWidth
open Tests.Guards.CloseSplitFrames
set_option autoImplicit false

namespace Tests.Guards.CloseStackCover

/-! ## §0 The cover path -/

def coveredN : Name := ``L4YAML.Proofs.IndentStackCover.Covered
def floorN : Name := ``L4YAML.Proofs.IndentStackCover.Floor

def hasCov (e : Expr) : Bool := hasHead e coveredN

/-- The conclusion of a Pi type, syntactically. -/
partial def piConcl (t : Expr) : Expr :=
  match t.consumeMData with
  | .forallE _ _ b _ => piConcl b
  | t => t

/-- The cover itself, or one of the pack types whose fields carry it. -/
def hasCovT (ct : Std.HashSet Name) (e : Expr) : Bool :=
  hasCov e || (e.find? fun x => match x.getAppFn with | .const n _ => ct.contains n | _ => false).isSome

inductive Step | opt | ex | andL | andR
  deriving BEq, Repr, Inhabited

def Step.render : Step → String
  | .opt => "∨" | .ex => "∃" | .andL => "∧L" | .andR => "∧R"

/-- Item 311: a cover-carrying type's outer option is `∨ True` or the family's named alternative
    (`isOptTrue`), or a Prop VARIABLE — a lemma that states the alternative generically
    (`colon_open_map_implicit`'s `{alt : Prop}`), read on its own binders and, through
    `lemParams`, at its applications.  Only under `hasCov`, so no other variable qualifies. -/
def isOptAlt (t : Expr) : Bool :=
  let t := t.consumeMData
  isOptTrue t || (t.isAppOfArity ``Or 2 &&
    match (t.getArg! 1).consumeMData with
    | .bvar _ | .fvar _ => true
    | _ => false)

/-- The path from a position's type to its cover option: through the outer
    option, the existentials and the conjunctions, to the innermost `∨ True`
    whose left mentions the cover, or to a bare `Covered`. -/
partial def coverPath (ty : Expr) : Option (List Step) :=
  let ty := ty.consumeMData
  if !hasCov ty then none
  else if ty.isAppOf coveredN then some []
  else if isOptAlt ty then
    let l := (ty.getArg! 0).consumeMData
    match depthTo l (·.isAppOf coveredN) with
    | some 0 => some []
    | some _ => (coverPath l).map (Step.opt :: ·)
    | none => none
  else if ty.isAppOfArity ``Exists 2 then
    match (ty.getArg! 1).consumeMData with
    | .lam _ _ b _ => (coverPath b).map (Step.ex :: ·)
    | _ => none
  else if ty.isAppOfArity ``And 2 then
    if hasCov (ty.getArg! 0) then (coverPath (ty.getArg! 0)).map (Step.andL :: ·)
    else (coverPath (ty.getArg! 1)).map (Step.andR :: ·)
  else none

def renderPath (p : List Step) : String := String.intercalate "" (p.map Step.render)

/-! ## §1 The binder stack and a small printer -/

structure Bind where
  name : Name
  ty : Expr
  prov : Option String
  deriving Inhabited

abbrev Stack := Array Bind

def bname (n : Name) : String :=
  if n.hasMacroScopes then s!"{n.eraseMacroScopes}✝" else n.toString

/-- Names for the widths a payment names: variables, literals, sums, lists. -/
partial def pp (st : Stack) (e : Expr) (fuel : Nat := 6) : String :=
  let e := e.consumeMData
  if fuel == 0 then "…" else
  match e with
  | .bvar i => if i < st.size then bname st[st.size - 1 - i]!.name else s!"#{i}"
  | .lit (.natVal n) => toString n
  | .const n _ => short n
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if n == ``OfNat.ofNat && args.size == 3 then pp st args[1]! (fuel - 1)
      else if n == ``HAdd.hAdd && args.size == 6 then s!"{pp st args[4]! (fuel - 1)} + {pp st args[5]! (fuel - 1)}"
      else if n == ``Nat.succ && args.size == 1 then s!"{pp st args[0]! (fuel - 1)} + 1"
      else if n == ``List.cons && args.size == 3 then s!"{pp st args[1]! (fuel - 1)} :: {pp st args[2]! (fuel - 1)}"
      else if n == ``List.nil then "[]"
      else s!"{short n}(…)"
    | .bvar _ => s!"{pp st f (fuel - 1)}(…)"
    | _ => "?"
  | .lam n _ _ _ => s!"λ{bname n}"
  | _ => "?"

/-! ## §2 Classifying a payment -/

inductive Cls where
  | punt
  | paid (inner : Cls)
  | lit (lo idx ks : String) (proof : Cls)
  | relay (src : String)
  | step (inner : Cls)
  | via (lem : String) (inner : Cls)
  | lemma (lem : String)
  | imp (src : String) (inner : Cls)
  | alt (kind : String) (alts : Array Cls)
  | other (s : String)
  deriving Inhabited, Repr

partial def Cls.render : Cls → String
  | .punt => "punt"
  | .paid i => s!"paid\{cover={i.render}}"
  | .lit lo idx ks proof => s!"lit(lo={lo},idx={idx},ks={ks},by={proof.render})"
  | .relay s => s!"relay({s})"
  | .step i => s!"step({i.render})"
  | .via l i => s!"via:{l}({i.render})"
  | .lemma l => s!"lemma({l})"
  | .imp s i => s!"imp:{s}\{{i.render}}"
  | .alt k as => k ++ "[" ++ String.intercalate "|" (as.map (·.render)).toList ++ "]"
  | .other s => s!"other({s})"

def Cls.isPunt : Cls → Bool
  | .punt => true
  | _ => false

partial def Cls.sources : Cls → Array String
  | .relay s => #[s]
  | .lit _ _ _ proof => proof.sources
  | .paid i | .step i | .via _ i | .imp _ i => i.sources
  | .alt _ as => as.foldl (· ++ ·.sources) #[]
  | _ => #[]

/-- The terminal leaves of a payment, before any relay is followed.  `cover`
    says whether the walk has entered the outer option. -/
partial def Cls.leaves (c : Cls) (cover : Bool := false) : Array String :=
  match c with
  | .punt => if cover then #["cover-punt"] else #["punt"]
  | .paid i => i.leaves true
  | .lit _ _ _ proof => if proof.sources.isEmpty then #["paid"] else #[]
  | .relay _ => #[]
  | .step i | .via _ i | .imp _ i => i.leaves cover
  | .lemma _ => #["paid:lemma"]
  | .alt _ as => as.foldl (fun acc a => acc ++ a.leaves cover) #[]
  | .other s => #[s!"other({s})"]

/-- The branch shape of an application: its discriminants and its branch
    arguments (lambdas over the pattern variables). -/
def branchesOf (n : Name) (args : Array Expr) : MetaM (Option (String × Array Expr × Array Nat)) := do
  let env ← getEnv
  if (n == ``dite || n == ``ite || n == ``Decidable.byCases) && args.size ≥ 5 then
    return some ("ite", #[], #[3, 4])
  if n == ``Or.elim && args.size ≥ 6 then return some ("elim", #[args[3]!], #[4, 5])
  if n == ``Exists.elim && args.size ≥ 5 then return some ("elim", #[args[3]!], #[4])
  if n == ``Or.rec && args.size ≥ 6 then return some ("rec", #[args[5]!], #[3, 4])
  if isCasesOnRecursor env n then
    let ind := n.getPrefix
    if let some (.inductInfo iv) := env.find? ind then
      let majorPos := iv.numParams + 1 + iv.numIndices
      if args.size ≥ majorPos + 1 + iv.ctors.length then
        let brs := (List.range iv.ctors.length).toArray.map (majorPos + 1 + ·)
        return some ("cases", #[args[majorPos]!], brs)
  if let some info ← getMatcherInfo? n then
    let nAlts := info.altInfos.size
    let firstDiscr := info.numParams + 1
    let firstAlt := firstDiscr + info.numDiscrs
    if args.size ≥ firstAlt + nAlts then
      let discrs := (List.range info.numDiscrs).toArray.map fun i => args[firstDiscr + i]!
      let brs := (List.range nAlts).toArray.map (firstAlt + ·)
      return some ("match", discrs, brs)
  return none

def provOf (st : Stack) (e : Expr) : Option String :=
  match e.consumeMData with
  | .bvar i => if i < st.size then st[st.size - 1 - i]!.prov else none
  | _ => none

/-- The source a term relays: a variable's provenance, through casts, `Or.imp`
    and a match on a variable. -/
partial def sourceOf (st : Stack) (e : Expr) : MetaM (Option String) := do
  let e := peelSafe e
  match e with
  | .bvar _ => return provOf st e
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if n == ``Or.imp && args.size ≥ 7 then return ← sourceOf st args[6]!
      if (n == ``Or.imp_left || n == ``Or.imp_right) && args.size ≥ 5 then return ← sourceOf st args[4]!
      if let some (_, discrs, _) ← branchesOf n args then
        for d in discrs do
          if let some p ← sourceOf st d then return some p
        return none
      if n.getRoot == `L4YAML then return some s!"ret:{short n}"
      return none
    | .bvar _ =>
      -- a local function: its own provenance, else the cover it is applied to
      if let some p := provOf st f then return some p
      for a in args do
        if let some p ← sourceOf st a then return some p
      return none
    | _ => return none
  | _ => return none

/-- Push the consecutive lambda binders of `e`, each with the provenance
    `inherit` when its type mentions the cover, and return the body. -/
partial def enterLams (ct : Std.HashSet Name) (st : Stack) (mk : Name → Option String) (e : Expr) : Stack × Expr :=
  match e.consumeMData with
  | .lam n t b _ =>
    let prov := if hasCovT ct t then mk n <|> some s!"λ:{bname n}" else none
    enterLams ct (st.push { name := n, ty := t, prov }) mk b
  | e => (st, e)

/-- The classification of `e` at a position whose cover path is `path`. -/
partial def classify (ct : Std.HashSet Name) (st : Stack) (e : Expr) (path : List Step) (fuel : Nat := 40) : MetaM Cls := do
  if fuel == 0 then return .other "fuel"
  let e := peelSafe e
  -- a transport (a lemma or a local function) producing the cover: from a
  -- cover among its arguments, or from nothing
  let env ← getEnv
  let isThm (n : Name) : Bool := match env.find? n with | some (.thmInfo _) => true | _ => false
  -- a theorem whose conclusion mentions the cover: a step or a payment
  -- item 259: a conclusion in a cover TYPE (`CoverStep`) is a cover too
  let coverThm (n : Name) : Bool := match env.find? n with
    | some (.thmInfo ti) => n.getRoot == `L4YAML && hasCovT ct (piConcl ti.type)
    | _ => false
  let viaArgs (name : String) (args : Array Expr) : MetaM Cls := do
    for a in args do
      if let some p := provOf st a then return .via name (.relay p)
    for a in args do
      let a' := peelSafe a
      let coverish := match a'.getAppFn with
        | .const m _ => coverThm m || m == ``Or.imp || m == ``Or.imp_left
        | .bvar _ => (provOf st a'.getAppFn).isSome
        | _ => false
      if coverish then
        let r ← classify ct st a' [] (fuel - 1)
        match r with
        | .other _ => pure ()
        | _ => return .via name r
    return .lemma name
  let branch (kind : String) (discrs : Array Expr) (brs : Array Nat) (args : Array Expr) : MetaM Cls := do
    let mut src : Option String := none
    for d in discrs do
      if src.isNone then src ← sourceOf st d
    let mut out : Array Cls := #[]
    for b in brs do
      let (st', body) := enterLams ct st (fun _ => src) args[b]!
      out := out.push (← classify ct st' body path (fuel - 1))
    if out.size == 1 then return out[0]!
    return .alt kind out
  match e with
  | .bvar _ =>
    match provOf st e with
    | some p => return .relay p
    | none => return .other s!"?{pp st e}"
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .const n _ =>
      if let some (kind, discrs, brs) ← branchesOf n args then
        return ← branch kind discrs brs args
      match path with
      | [] =>
        if n == ``Or.inl && args.size ≥ 3 then
          -- the literal: `⟨lo, floor, covered⟩` or a bare cover; the cover's
          -- proof is named, and if it is a variable its provenance is a source
          let a := args[0]!.consumeMData
          let p := peelSafe args[2]!
          let (lo, cv) := match p.getAppFn, p.getAppArgs with
            | .const ``Exists.intro _, pa =>
              if pa.size ≥ 4 then
                let q := peelSafe pa[3]!
                match q.getAppFn, q.getAppArgs with
                | .const ``And.intro _, qa => if qa.size ≥ 4 then (pp st pa[2]!, peelSafe qa[3]!) else (pp st pa[2]!, q)
                | _, _ => (pp st pa[2]!, q)
              else ("?", p)
            | _, _ => ("—", p)
          let proof ← match cv with
            | .bvar _ => pure (match provOf st cv with | some q => Cls.relay q | none => .other s!"?{pp st cv}")
            | .lam .. => pure (Cls.lemma "λ")
            | .app .. =>
              match cv.getAppFn with
              | .const m _ => if isThm m && m.getRoot == `L4YAML then viaArgs (short2 m) cv.getAppArgs else pure (Cls.other (short2 m))
              | .bvar _ => pure (match provOf st cv.getAppFn with | some q => Cls.relay q | none => .other s!"?{pp st cv.getAppFn}")
              | _ => pure (Cls.other "app")
            | _ => pure (Cls.other "?")
          let (idx, ks) := match a.consumeMData with
            | .app .. =>
              if a.isAppOfArity ``Exists 2 then
                match (a.getArg! 1).consumeMData with
                | .lam ln lt body _ =>
                  let st' := st.push { name := ln, ty := lt, prov := none }
                  match (body.consumeMData.find? (·.isAppOfArity floorN 3)) with
                  | some fl => (pp st' (fl.getArg! 1), pp st' (fl.getArg! 2))
                  | none => ("—", "—")
                | _ => ("—", "—")
              else
                match a.find? (·.isAppOfArity coveredN 3) with
                | some cv => ("—", pp st (cv.getArg! 1))
                | none => ("—", "—")
            | _ => ("—", "—")
          return .lit lo idx ks proof
        if n == ``Or.inr then return .punt
        if n == ``And.intro && args.size ≥ 4 then
          return .alt "and" #[← classify ct st args[2]! [] (fuel - 1), ← classify ct st args[3]! [] (fuel - 1)]
        if n == ``Or.imp && args.size ≥ 7 then return .step (← classify ct st args[6]! [] (fuel - 1))
        if (n == ``Or.imp_left || n == ``Or.imp_right) && args.size ≥ 5 then
          return .step (← classify ct st args[4]! [] (fuel - 1))
        if n.getRoot == `L4YAML && isThm n then return ← viaArgs (short2 n) args
        return .other (short2 n)
      | .opt :: rest =>
        if n == ``Or.inl && args.size ≥ 3 then return .paid (← classify ct st args[2]! rest (fuel - 1))
        if n == ``Or.inr then return .punt
        if n == ``Or.imp && args.size ≥ 7 then
          let src := (← sourceOf st args[6]!).getD "?"
          let fe := peelSafe args[4]!
          match fe with
          | .lam .. =>
            let (st', body) := enterLams ct st (fun _ => some src) fe
            return .imp src (← classify ct st' body rest (fuel - 1))
          | _ =>
            if fe.isConstOf ``id then return .relay src
            return .imp src (.other s!"f={pp st fe}")
        if n == ``Or.imp_left && args.size ≥ 5 then
          let src := (← sourceOf st args[4]!).getD "?"
          let (st', body) := enterLams ct st (fun _ => some src) (peelSafe args[3]!)
          return .imp src (← classify ct st' body rest (fuel - 1))
        if n == ``Or.imp_right && args.size ≥ 5 then
          return .relay ((← sourceOf st args[4]!).getD "?")
        return .other (short2 n)
      | .ex :: rest =>
        if n == ``Exists.intro && args.size ≥ 4 then return ← classify ct st args[3]! rest (fuel - 1)
        return .other (short2 n)
      | .andL :: rest =>
        if n == ``And.intro && args.size ≥ 4 then return ← classify ct st args[2]! rest (fuel - 1)
        return .other (short2 n)
      | .andR :: rest =>
        if n == ``And.intro && args.size ≥ 4 then return ← classify ct st args[3]! rest (fuel - 1)
        return .other (short2 n)
    | .bvar _ =>
      match provOf st f with
      | some p => return .relay p
      | none => return .other s!"?{pp st f}(…)"
    | .lam .. => classify ct st e.headBeta path (fuel - 1)
    | _ => return .other "app"
  | .lam .. => return .other "λ"
  | _ => return .other "?"

/-! ## §3 The walk -/

structure Row where
  lem : Name
  kind : String
  target : String
  occ : Nat
  cls : Cls
  -- item 254: at a constructor row, the binder stack the payment stands under
  -- and the constructor's arguments, for a reader of what is in hand there
  st : Stack := #[]
  args : Array Expr := #[]
  deriving Inhabited

structure EightRow where
  lem : Name
  feeds : String
  facts : String
  deriving Inhabited

structure DoorUse where
  lem : Name
  door : String
  callee : String
  cover : Bool
  deriving Inhabited

structure S where
  rows : Array Row := #[]
  eight : Array EightRow := #[]
  doorUses : Array DoorUse := #[]
  occ : Std.HashMap String Nat := {}
  memo : Std.HashMap Expr Bool := {}
  nodes : Nat := 0
  mentions : Nat := 0
  doors : Array Name := #[]
  doorBound : Array String := #[]
  doorUsed : Std.HashSet String := {}

structure Cand where
  ctorFields : Std.HashMap Name (Array (Nat × Name × List Step)) := {}
  lemParams : Std.HashMap Name (Array (Nat × Name × List Step)) := {}
  paramNames : Std.HashMap Name (Array (Name × Bool)) := {}
  funnels : Std.HashMap Name (Nat × Name) := {}
  consts : Std.HashSet Name := {}
  parks : Std.HashSet Name := {}
  ctorNames : Array Name := #[]
  ctorFieldNames : Std.HashMap Name (Array Name) := {}
  coverTypes : Std.HashSet Name := {}

structure Cx where
  lem : Name
  st : Stack
  inherit : Option String := none
  door : Option (Name × Array Name × Nat) := none
  paramsLeft : Nat := 0
  hcp : Option Nat := none
  noPrune : Bool := false
  fnLabel : Option String := none
  inFn : Bool := false

/-- The first binder of a lambda chain whose type mentions the cover. -/
partial def firstCovBinder (ct : Std.HashSet Name) (e : Expr) : Option Name :=
  match e.consumeMData with
  | .lam n t b _ => if hasCovT ct t then some n else firstCovBinder ct b
  | _ => none

/-- The types of a branch construct's discriminants, as far as they can be read
    off the application: a matcher's motive binders, or the proposition a
    `casesOn`/`elim` on `Exists`, `And`, `Or` eliminates. -/
def discrTypes (n : Name) (args : Array Expr) : MetaM (Array Expr) := do
  if (n == ``Or.elim || n == ``Or.rec || n == ``Or.casesOn) && args.size ≥ 2 then
    return #[mkApp2 (mkConst ``Or) args[0]! args[1]!]
  if (n == ``Exists.elim || n == ``Exists.casesOn) && args.size ≥ 2 then
    return #[mkApp2 (mkConst ``Exists) args[0]! args[1]!]
  if n == ``And.casesOn && args.size ≥ 2 then
    return #[mkApp2 (mkConst ``And) args[0]! args[1]!]
  if let some info ← getMatcherInfo? n then
    if args.size > info.numParams then
      let mut tys : Array Expr := #[]
      let mut m := args[info.numParams]!.consumeMData
      for _ in [0:info.numDiscrs] do
        match m with
        | .lam _ t b _ => tys := tys.push t; m := b
        | _ => break
      return tys
  return #[]

partial def containsCand (st : IO.Ref S) (cs : Std.HashSet Name) (e : Expr) : MetaM Bool := do
  match (← st.get).memo[e]? with
  | some b => return b
  | none =>
    let b ← match e with
      | .const n _ => pure (cs.contains n)
      | .app f a => do pure ((← containsCand st cs f) || (← containsCand st cs a))
      | .lam _ t b _ | .forallE _ t b _ => do pure ((← containsCand st cs t) || (← containsCand st cs b))
      | .letE _ t v b _ => do pure ((← containsCand st cs t) || (← containsCand st cs v) || (← containsCand st cs b))
      | .mdata _ b | .proj _ _ b => containsCand st cs b
      | _ => pure false
    st.modify fun s => { s with memo := s.memo.insert e b }
    return b

/-- A relation (possibly negated) with an operand that projects `proj` off a
    scanner state — a fact ABOUT the projection, not a state that mentions it. -/
partial def relOn (t : Expr) (proj : Name) : Bool :=
  let t := t.consumeMData
  match t with
  | .forallE _ _ b _ => relOn b proj
  | _ =>
    let t := if t.isAppOfArity ``Not 1 then (t.getArg! 0).consumeMData else t
    let ops : Array Expr :=
      if t.isAppOfArity ``Eq 3 || t.isAppOfArity ``Ne 3 then #[t.getArg! 1, t.getArg! 2]
      else if t.isAppOfArity ``LE.le 4 || t.isAppOfArity ``LT.lt 4 || t.isAppOfArity ``GE.ge 4 || t.isAppOfArity ``GT.gt 4 then #[t.getArg! 2, t.getArg! 3]
      else #[]
    -- the operand IS the projection, or a cast or a query one level over it
    ops.any fun o => let o := o.consumeMData; o.isAppOf proj || o.getAppArgs.any (·.consumeMData.isAppOf proj)

def factsAt (st : Stack) : String := Id.run do
  let names (p : Expr → Bool) : Array String :=
    (st.filter fun b => p b.ty).map fun b => bname b.name
  let indents := names (relOn · ``ScannerState.indents)
  let top := names (relOn · ``ScannerState.currentIndent)
  let floor := names (hasHead · ``L4YAML.Proofs.PreprocessIndentStable.IndentFloor)
  let minci := names (hasHead · ``L4YAML.Proofs.PreprocessIndentStable.minContentIndentOf)
  let nic := names (relOn · ``ScannerState.needIndentCheck)
  let prep := names (hasHead · ``scanNextToken_preprocess)
  let base := names (hasHead · ``L4YAML.Proofs.IndentStackBase.SentinelBase)
  let mono := names (hasHead · ``L4YAML.Proofs.IndentStackMono.Mono)
  let cover := (st.filter fun b => hasCov b.ty).map fun b =>
    s!"{bname b.name}@{(depthTo b.ty (·.isAppOf coveredN)).getD 0}"
  let r (k : String) (xs : Array String) := s!"{k}={xs.size}{if xs.isEmpty then "" else "(" ++ String.intercalate "," xs.toList ++ ")"}"
  return String.intercalate " " [r "indents" indents, r "top" top, r "floor" floor, r "minCI" minci, r "nic" nic,
    r "prep" prep, r "base" base, r "mono" mono, r "cover" cover]

def posLabel (kind : String) (target : Name) (field : Name) : String :=
  s!"{kind}:{short target}.{field}"

partial def walk (st : IO.Ref S) (cd : Cand) (cx : Cx) (e : Expr) : MetaM Unit := do
  st.modify fun s => { s with nodes := s.nodes + 1 }
  match e with
  | .mdata _ b => walk st cd cx b
  | .lam n t b _ =>
    let mut prov : Option String := none
    let mut door := cx.door
    let mut hcp := cx.hcp
    if cx.paramsLeft > 0 then
      if hasCovT cd.coverTypes t then prov := some (posLabel (if (coverPath t).isSome then "param" else "fnparam") cx.lem n)
      if n == `h_close_pending && cd.parks.contains cx.lem then hcp := some cx.st.size
    else if let some (c, fields, i) := cx.door then
      if i < fields.size then
        if hasCov t then
          let label := posLabel "door" c fields[i]!
          prov := some label
          st.modify fun s => { s with doorBound := s.doorBound.push s!"{short cx.lem}: {label}" }
        door := some (c, fields, i + 1)
      else door := none
    else if let some l := cx.fnLabel then
      if hasCovT cd.coverTypes t then prov := some s!"fnp:{l}.{bname n}"
    else if hasCovT cd.coverTypes t then prov := cx.inherit <|> some s!"λ:{bname n}"
    let st' := cx.st.push { name := n, ty := t, prov }
    let inherit' := if cx.paramsLeft > 0 then none else cx.inherit
    let cx' : Cx := { cx with st := st', door := door, paramsLeft := cx.paramsLeft - 1, hcp := hcp, inherit := inherit' }
    walk st cd cx' b
  | .forallE n t b _ =>
    walk st cd { cx with st := cx.st.push { name := n, ty := t, prov := none }, inherit := none, door := none, paramsLeft := 0, fnLabel := none } b
  | .letE n t v b _ =>
    let cx0 := { cx with inherit := none, door := none, paramsLeft := 0, fnLabel := none }
    let prov ← local? cx n t v
    walk st cd (valueCx cx0 prov) v
    walk st cd { cx0 with st := cx.st.push { name := n, ty := t, prov } } b
  | .proj _ _ b => walk st cd { cx with inherit := none, door := none, paramsLeft := 0, fnLabel := none } b
  | .app .. =>
    unless cx.noPrune || (← containsCand st cd.consts e) do return
    let f := e.getAppFn
    let args := e.getAppArgs
    let cx0 := { cx with inherit := none, door := none, paramsLeft := 0, fnLabel := none }
    match f with
    | .const n _ =>
      -- a cast applied past its arity: `cases` and `subst` re-introduce the
      -- variables they revert this way, so the body is walked beta-reduced
      -- and its binders are the originals
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← walk st cd cx (mkAppN args[k]! (args.extract arity args.size)).headBeta
      if n == ``letFun && args.size ≥ 4 then
        match args[3]! with
        | .lam bn bt bb _ =>
          let prov ← local? cx bn args[0]! args[2]!
          walk st cd (valueCx cx0 prov) args[2]!
          walk st cd { cx0 with st := cx.st.push { name := bn, ty := bt, prov } } bb
        | g =>
          walk st cd cx0 args[2]!
          walk st cd cx0 g
        for a in args.extract 4 args.size do walk st cd cx0 a
        return
      if n == ``PendingNode.casesOn then
        let env ← getEnv
        let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode"
        let majorPos := iv.numParams + 1 + iv.numIndices
        st.modify fun s => { s with doors := if s.doors.contains cx.lem then s.doors else s.doors.push cx.lem }
        for i in [0:args.size] do
          if i > majorPos && i ≤ majorPos + iv.ctors.length then
            let c := iv.ctors[i - majorPos - 1]!
            let fields := cd.ctorFieldNames.getD c #[]
            walk st cd { cx0 with door := some (c, fields, 0), noPrune := true } args[i]!
          else walk st cd cx0 args[i]!
        return
      if let some (_, discrs, brs) ← branchesOf n args then
        let mut src : Option String := none
        for d in discrs do
          if src.isNone then src ← sourceOf cx.st d
        if let some p := src then
          if p.startsWith "door:" then st.modify fun s => { s with doorUsed := s.doorUsed.insert s!"{short cx.lem}: {p}" }
        if src.isNone then
          -- a destructured VALUE: a constructed term whose type carries a cover
          -- is a payment of its own, named after the first cover it binds
          let tys ← discrTypes n args
          for (d, ty) in discrs.zip tys do
            if src.isNone then
              if let some path := coverPath ty then
                let nm := (brs.findSome? fun b => if b < args.size then firstCovBinder cd.coverTypes args[b]! else none).getD `value
                let base := s!"val:{short cx.lem}.{bname nm}"
                let k := ((← st.get).rows.filter fun r => r.lem == cx.lem && (r.target == base || r.target.startsWith (base ++ "#"))).size
                let label := if k == 0 then base else s!"{base}#{k + 1}"
                let cls ← classify cd.coverTypes cx.st d path
                st.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "val", target := label, occ := 1, cls } }
                src := some label
        for i in [0:args.size] do
          if brs.contains i then walk st cd { cx0 with inherit := src } args[i]!
          else walk st cd cx0 args[i]!
        return
      -- a park constructor: its cover-carrying fields
      if let some fields := cd.ctorFields[n]? then
        let env ← getEnv
        let some (.ctorInfo cv) := env.find? n | throwError "{n}: not a constructor"
        let fieldArgs := args.extract cv.numParams args.size
        let producer := fieldArgs.any fun a => !(a.consumeMData.isBVar || a.consumeMData.isFVar)
        if producer && args.size == cv.numParams + cv.numFields then
          let key := s!"{cx.lem}/{n}"
          let occ := ((← st.get).occ.getD key 0) + 1
          st.modify fun s => { s with occ := s.occ.insert key occ }
          for (idx, field, path) in fields do
            if idx < args.size then
              let cls ← classify cd.coverTypes cx.st args[idx]! path
              st.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "ctor", target := posLabel "ctor" n field, occ, cls, st := cx.st, args := args } }
        else
          st.modify fun s => { s with mentions := s.mentions + 1 }
      -- a lemma with cover-carrying parameters
      if let some ps := cd.lemParams[n]? then
       unless cx.inFn do
        let key := s!"{cx.lem}/{n}"
        let occ := ((← st.get).occ.getD key 0) + 1
        st.modify fun s => { s with occ := s.occ.insert key occ }
        for (idx, pname, path) in ps do
          if idx < args.size then
            let cls ← classify cd.coverTypes cx.st args[idx]! path
            st.modify fun s => { s with rows := s.rows.push { lem := cx.lem, kind := "lemma", target := posLabel "param" n pname, occ, cls } }
      -- the eight: the funnel spends of the two park lemmas
      if let some (idx, pname) := cd.funnels[n]? then
        if let some h := cx.hcp then
          if idx < args.size && args[idx]!.hasLooseBVar (cx.st.size - 1 - h) then
            st.modify fun s => { s with eight := s.eight.push { lem := cx.lem, feeds := s!"{short n}.{pname}", facts := factsAt cx.st } }
      for a in args do
        if let some p := provOf cx.st a then
          if p.startsWith "door:" then st.modify fun s => { s with doorUsed := s.doorUsed.insert s!"{short cx.lem}: {p}" }
      -- the doors' hand-overs
      if n.getRoot == `L4YAML then
        if let some names := cd.paramNames[n]? then
          for i in [0:min args.size names.size] do
            if let some srcP ← sourceOf cx.st args[i]! then
              if srcP.startsWith "door:" then
                st.modify fun s => { s with doorUses := s.doorUses.push { lem := cx.lem, door := srcP, callee := s!"{short n}.{names[i]!.1}", cover := names[i]!.2 } }
      for a in args do walk st cd cx0 a
    | .bvar _ =>
      for a in args do
        if let some p := provOf cx.st a then
          if p.startsWith "door:" then st.modify fun s => { s with doorUsed := s.doorUsed.insert s!"{short cx.lem}: {p}" }
      -- a local function: its parameters' names and cover from its type; a
      -- cover-carrying parameter of a named local is a position of its own
      if let some b := (match f with | .bvar i => if i < cx.st.size then some cx.st[cx.st.size - 1 - i]! else none | _ => none) then
        let mut ty := b.ty
        for i in [0:args.size] do
          match ty.consumeMData with
          | .forallE pn pt pb _ =>
            let cp := if hasCov pt then coverPath pt else none
            if let some srcP ← sourceOf cx.st args[i]! then
              if srcP.startsWith "door:" then
                st.modify fun s => { s with doorUses := s.doorUses.push { lem := cx.lem, door := srcP, callee := s!"local:{bname b.name}.{bname pn}", cover := cp.isSome } }
            if let some path := cp then
              if let some l := b.prov then
                if l.startsWith "fn:" && !(piConcl b.ty).isAppOf coveredN then
                  let cls ← classify cd.coverTypes cx.st args[i]! path
                  let target := s!"fnp:{(l.drop 3)}.{bname pn}"
                  let key := s!"{cx.lem}/{target}"
                  let occ := ((← st.get).occ.getD key 0) + 1
                  st.modify fun s => { s with occ := s.occ.insert key occ, rows := s.rows.push { lem := cx.lem, kind := "fnp", target, occ, cls } }
            ty := pb
          | _ => break
      for a in args do walk st cd cx0 a
    | _ =>
      walk st cd cx0 f
      for a in args do walk st cd cx0 a
  | _ => return
where
  valueCx (cx0 : Cx) (prov : Option String) : Cx :=
    match prov with
    | some l => if l.startsWith "fn:" then { cx0 with fnLabel := some (l.drop 3).toString, inFn := true } else cx0
    | none => cx0
  local? (cx : Cx) (n : Name) (t v : Expr) : MetaM (Option String) := do
    if hasCovT cd.coverTypes t then
      if t.consumeMData.isForall then
        let label := posLabel "fn" cx.lem n
        if let some path := coverPath (piConcl t) then
          let (st', body) := enterLams cd.coverTypes cx.st (fun b => some s!"fnp:{(label.drop 3)}.{bname b}") v
          let cls ← classify cd.coverTypes st' body path
          let key := s!"{cx.lem}/{label}"
          let occ := ((← st.get).occ.getD key 0) + 1
          st.modify fun s => { s with occ := s.occ.insert key occ, rows := s.rows.push { lem := cx.lem, kind := "fn", target := label, occ, cls } }
        return some label
      if let some path := coverPath t then
        let cls ← classify cd.coverTypes cx.st v path
        let label := posLabel "local" cx.lem n
        let key := s!"{cx.lem}/{label}"
        let occ := ((← st.get).occ.getD key 0) + 1
        st.modify fun s => { s with occ := s.occ.insert key occ, rows := s.rows.push { lem := cx.lem, kind := "local", target := label, occ, cls } }
        return some label
    return none

/-- Walk one theorem's value. -/
def walkTheorem (st : IO.Ref S) (cd : Cand) (n : Name) : MetaM Unit := do
  let some ci := (← getEnv).find? n | return
  let some v := ci.value? (allowOpaque := true) | return
  st.modify fun s => { s with memo := {} }
  unless ← containsCand st cd.consts v do return
  let nParams := ci.type.getForallBinderNames.length
  walk st cd { lem := n, st := #[], paramsLeft := nParams } v

/-! ## §4 The trees -/

structure Tree where
  lines : Array String := #[]
  leaves : Array String := #[]
  visited : Std.HashSet String := {}
  opens : Array String := #[]

def rowsAt (rows : Array Row) (pos : String) : Array Row := rows.filter (·.target == pos)

def srcToPos (s : String) : Option String :=
  if s.startsWith "door:" then some ("ctor:" ++ (s.drop 5).toString)
  else if s.startsWith "param:" || s.startsWith "local:" || s.startsWith "fnp:" || s.startsWith "fn:" || s.startsWith "val:" then some s
  else none

/-- The positions a source resolves to: a park field's producers, a
    parameter's or a local's rows, or — for a lemma's return value — that
    lemma's own cover-carrying parameters. -/
def srcPositions (rets : Std.HashMap String (Array String)) (s : String) : Array String :=
  match srcToPos s with
  | some p => #[p]
  | none => if s.startsWith "ret:" then rets.getD s #[] else #[]

partial def resolve (rets : Std.HashMap String (Array String)) (rows : Array Row) (pos : String) (depth : Nat) (t : Tree) : Tree := Id.run do
  let ind := String.ofList (List.replicate (4 * depth) ' ')
  let mut t := t
  if t.visited.contains pos then
    return { t with lines := t.lines.push s!"{ind}↺ {pos}" }
  t := { t with visited := t.visited.insert pos, lines := t.lines.push s!"{ind}{pos}" }
  let rs := rowsAt rows pos
  if rs.isEmpty then
    return { t with lines := t.lines.push s!"{ind}  (no rows)", opens := t.opens.push pos, leaves := t.leaves.push s!"open:{pos}" }
  for r in rs do
    -- a relay's own `punt` alternative is its source's punt, not a leaf
    let own := if r.cls.sources.isEmpty then r.cls.leaves else r.cls.leaves.filter (· != "punt")
    t := { t with lines := t.lines.push s!"{ind}  ← {short r.lem} #{r.occ}: {r.cls.render}" }
    for l in own do t := { t with leaves := t.leaves.push l }
    if depth < 40 then
      for s in distinctS r.cls.sources do
        let ps := srcPositions rets s
        if ps.isEmpty then
          if s.startsWith "ret:" then
            t := { t with lines := t.lines.push s!"{ind}    {s}: no cover parameter, a payment from state", leaves := t.leaves.push "paid:lemma" }
          else
            t := { t with lines := t.lines.push s!"{ind}    open {s}", opens := t.opens.push s, leaves := t.leaves.push s!"open:{s}" }
        else
          for p in ps do t := resolve rets rows p (depth + 1) t
    else t := { t with leaves := t.leaves.push "depth" }
  return t

def census (xs : Array String) : String :=
  let ds := distinctS xs
  String.intercalate " " ((ds.qsort (· < ·)).toList.map fun d => s!"{d}={(xs.filter (· == d)).size}")

/-! ## §5 The pins

Item 256 pays two of the entry park's seven producers — the root `-` with a
literal at floor 0 and the content sibling by relaying `h_closeF_old` — and
item 257 a third, the compact fill with a literal from the slot's own top
bound, floored below the fill's index, and item 258 two more, the entry park's
compact and nested re-parks with the same literal from the park's own top
bound, and item 259 a sixth, the compact opener's `pendingMapValue.h_closeF`
with a literal from the CALLER's park bound carried across the indicator's
own step (`CoverStep.cons_of_top_eq`, the level named by the pinned top) —
so the rows below carry those six classes, the content and entry trees are
one component of sixteen positions with six paid leaves and fifteen punts
each, and the value-slot and mapping value trees each read one more paid
leaf than item 253 did, the mapping value field being a position of all
four.  Item 259 also widens the transport rule to cover TYPES (§2's
`coverThm`, the `transport` test below): the six `CoverStep`-concluding
lemmas leave the lemma-parameter table (`lemParams` 35 → 29, `lemmas` 22 →
16, `positions` 27 → 21) and no row moves; the payment adds six walked
nodes (`nodes` 95157 → 95163).  Item 272 adds 861 more without moving a
row: the under-run disjunct the three flow-open arms destructure gains a
sixth component (`nodes` 95163 → 96024). -/

-- 2026-10-20 (item 306): six rows re-read — the two key-pack builders' value-line
-- stacks at the three entry-park calls are `match`es on `h_closeFV_old` (paid with the
-- cover punted | punt) where item 108 left bare punts.
-- 2026-10-23 (item 345): two `h_fV` rows punt → match[paid|punt] — the twin relays at `on_pendingBlock_indented` and
-- `accum_content_pending`'s `h_defer_split` now case on the park's `h_closeFV`.
-- 2026-10-25 (item 358): 167 → 185 rows — the cover rides `h_closeFV_old` (×3) and `closeThenBlock.h_mapFV`
-- (relay rows at every consumer) and `landing_frame_of_cover.h_cov` is fed through `preprocess_cover`/`of_indents_eq`.
-- 2026-10-29 (item 388): `closeThenBlock.h_seqFrames` gains the `nv ≤ k` arm (the value route); `accum_content_pending`
-- relays the mapping park's `.blockOut` `h_closeF` through `.imp` (the node weakened) — two rows reshaped, none added.
-- 2026-10-29 (item 394, option B): accum_step_flow's two h_framesS relays now carry the cover
-- from valueF (paid, not punted); accum_content_pending's h_fS local re-read with the restated
-- h_closeF cover (`∃ lo, Floor lo n ks`).
def expectedRows : List String :=
  ["accum_block_on_closeThenBlock #1 fn:accum_block_on_closeThenBlock.h_cov_step := via:IndentStackCover.scanBlockEntry_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(fnp:accum_block_on_closeThenBlock.h_cov_step.hc))))",
   "accum_block_on_closeThenBlock #1 local:accum_block_on_closeThenBlock.h_seqFrames := cases[ite[paid{cover=step(relay(param:accum_block_on_closeThenBlock.h_valF))}|ite[paid{cover=punt}|paid{cover=punt}]]|paid{cover=punt}]",
   "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_closeF := relay(local:accum_block_on_closeThenBlock.h_seqFrames)",
   "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_closeF := paid{cover=lit(lo=nv + 1,idx=nv + 1 + m,ks=[],by=via:IndentStackCover.scanBlockEntry_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(lemma(IndentStackCover.covered_nil_of_top_le)))))}",
    -- 2026-10-28 (item 385): the no-pop leaves of `h_res_land` relay the park's own value-node frames
    -- (`h_valF`) into `deeperLandingResume`, one row per `rcases h_mapF` arm
    "accum_block_on_closeThenBlock #1 param:deeperLandingResume.h_valF := relay(param:accum_block_on_closeThenBlock.h_valF)",
    "accum_block_on_closeThenBlock #2 param:deeperLandingResume.h_valF := relay(param:accum_block_on_closeThenBlock.h_valF)",
   "accum_block_on_noPending #1 ctor:pendingBlock.h_closeF := paid{cover=lit(lo=0,idx=k,ks=[],by=via:IndentStackCover.scanBlockEntry_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(lemma(IndentStackCover.covered_nil_of_ntop)))))}",
   -- 2026-10-26 (item 370): the sibling `-` re-parks with item 369's `h_closeF_old` (cover stepped across
   -- preprocessing and the `-`), no longer a punt.
   "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_closeF := match[paid{cover=step(relay(param:accum_block_on_pendingBlock.h_closeF_old))}|punt]",
   "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_closeF := paid{cover=lit(lo=n + 1,idx=k,ks=[],by=via:IndentStackCover.scanBlockEntry_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(lemma(IndentStackCover.covered_nil_of_top_le)))))}",
   "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_closeF := paid{cover=lit(lo=n + 1,idx=n + 1 + m,ks=[],by=via:IndentStackCover.scanBlockEntry_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(lemma(IndentStackCover.covered_nil_of_top_le)))))}",
   "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_closeF := match[paid{cover=step(relay(param:accum_block_on_pendingBlockContent.h_closeF_old))}|punt]",
   "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_valF := punt",
   "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_closeF_old := relay(door:pendingBlockContent.h_closeF)",
   "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_valF := imp:door:pendingMapValue.h_closeF{relay(door:pendingMapValue.h_closeF)}",
   "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_valF := imp:door:pendingMapValue.h_closeF{relay(door:pendingMapValue.h_closeF)}",
   "accum_content_on_pendingBlock_indented #1 fn:accum_content_on_pendingBlock_indented.h_cov_step := via:IndentStackCover.dispatchContent_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_on_pendingBlock_indented.h_cov_step.hc))))",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_closeF := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeF_old))}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_nodeF := match[paid{cover=relay(param:accum_content_on_pendingBlock_indented.h_closeF_old)}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_dframes := match[paid{cover=relay(param:accum_content_on_pendingBlock_indented.h_closeF_old)}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_nodeFV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryKeyPack_of_dispatch.h_dframesV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_closeFE := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeF_old))}|punt]",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_closeF := punt",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_closeFV := punt",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeF := match[paid{cover=relay(param:accum_content_on_pendingBlock_indented.h_closeF_old)}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_dframes := match[paid{cover=relay(param:accum_content_on_pendingBlock_indented.h_closeF_old)}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeFV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:entryPropsKeyPack_of_dispatch.h_dframesV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_closeF := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeF_old))}|punt]",
   "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_closeF := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeF_old))}|punt]",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_nodeF := match[paid{cover=relay(param:accum_content_on_pendingBlock_indented.h_closeF_old)}|punt]",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_dframes := match[paid{cover=relay(param:accum_content_on_pendingBlock_indented.h_closeF_old)}|punt]",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_nodeFV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingBlock_indented #2 param:entryKeyPack_of_dispatch.h_dframesV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingBlock_indented #1 fn:accum_content_on_pendingBlock_indented.h_pay_seq := cases[cases[lit(lo=—,idx=w,ks=map(…) :: ksw',by=via:StreamAccum.dedent_cover_of_floor(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_on_pendingBlock_indented.h_pay_seq.h_cv))))|punt]|punt]",
   "accum_content_on_pendingBlock_indented #1 param:resumectx_of_landing.h_fS := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeF_old))}|punt]",
   "accum_content_on_pendingBlock_indented #1 param:resumectx_of_landing.h_fV := match[paid{cover=punt}|punt]",
   "accum_content_on_pendingMapValue_indented #1 fn:accum_content_on_pendingMapValue_indented.h_cov_step := via:IndentStackCover.dispatchContent_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_on_pendingMapValue_indented.h_cov_step.hc))))",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeF99))}|punt]",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108))}|punt]",
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeF := match[paid{cover=relay(param:accum_content_on_pendingMapValue_indented.h_closeF99)}|punt]",
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_dframes := relay(param:accum_content_on_pendingMapValue_indented.h_frames99)",
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_nodeFV := relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108)",
   "accum_content_on_pendingMapValue_indented #1 param:entryKeyPack_of_dispatch.h_dframesV := relay(param:accum_content_on_pendingMapValue_indented.h_framesV108)",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeFE := punt",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeF := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeF99))}|punt]",
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeFV := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108))}|punt]",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeF := match[paid{cover=relay(param:accum_content_on_pendingMapValue_indented.h_closeF99)}|punt]",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_dframes := relay(param:accum_content_on_pendingMapValue_indented.h_frames99)",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_nodeFV := relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108)",
   "accum_content_on_pendingMapValue_indented #1 param:entryPropsKeyPack_of_dispatch.h_dframesV := relay(param:accum_content_on_pendingMapValue_indented.h_framesV108)",
   "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeF99))}|punt]",
   "accum_content_on_pendingMapValue_indented #2 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108))}|punt]",
   "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeF99))}|punt]",
   "accum_content_on_pendingMapValue_indented #3 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108))}|punt]",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeF := match[paid{cover=relay(param:accum_content_on_pendingMapValue_indented.h_closeF99)}|punt]",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_dframes := relay(param:accum_content_on_pendingMapValue_indented.h_frames99)",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_nodeFV := relay(param:accum_content_on_pendingMapValue_indented.h_closeFV108)",
   "accum_content_on_pendingMapValue_indented #2 param:entryKeyPack_of_dispatch.h_dframesV := relay(param:accum_content_on_pendingMapValue_indented.h_framesV108)",
   "accum_content_on_pendingMapValue_indented #1 fn:accum_content_on_pendingMapValue_indented.h_pay_res := cases[cases[lit(lo=—,idx=w,ks=map(…) :: ksw',by=via:StreamAccum.dedent_cover_of_floor(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_on_pendingMapValue_indented.h_pay_res.h_cv))))|punt]|punt]",
   "accum_content_on_pendingMapValue_indented #1 param:resumectx_of_landing.h_fS := imp:param:accum_content_on_pendingMapValue_indented.h_frames99{step(relay(param:accum_content_on_pendingMapValue_indented.h_frames99))}",
   "accum_content_on_pendingMapValue_indented #1 param:resumectx_of_landing.h_fV := imp:param:accum_content_on_pendingMapValue_indented.h_framesV108{step(relay(param:accum_content_on_pendingMapValue_indented.h_framesV108))}",
   "accum_content_pending #1 fn:accum_content_pending.h_cov_step := via:IndentStackCover.dispatchContent_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_pending.h_cov_step.hc))))",
   "accum_content_pending #1 fn:accum_content_pending.h_pay_col0 := cases[lit(lo=—,idx=w,ks=map(…) :: ksw',by=via:StreamAccum.dedent_cover_of_floor(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_pending.h_pay_col0.h_cv))))|punt]",
   "accum_content_pending #1 fn:accum_content_pending.h_pay_res := cases[lit(lo=—,idx=w,ks=map(…) :: ksw',by=via:StreamAccum.dedent_cover_of_floor(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_pending.h_pay_res.h_cv))))|punt]",
   "accum_content_pending #1 fnp:accum_content_pending.h_defer_split.h_fS := relay(door:pendingContent.h_framesS)",
   "accum_content_pending #1 fnp:accum_content_pending.h_defer_split.h_fV := relay(door:pendingContent.h_framesV)",
   "accum_content_pending #1 local:accum_content_pending.h_fS := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #1 local:accum_content_pending.h_fV := match[paid{cover=relay(door:pendingProps.h_closeFV)}|punt]",
   "accum_content_pending #1 fn:accum_content_pending.h_pay_props := cases[lit(lo=—,idx=w,ks=map(…) :: ksw',by=via:StreamAccum.dedent_cover_of_floor(via:IndentStackCover.preprocess_cover(relay(fnp:accum_content_pending.h_pay_props.h_cv))))|punt]",
   "accum_content_pending #1 param:resumectx_of_landing.h_fS := relay(local:accum_content_pending.h_fS)",
   "accum_content_pending #1 param:resumectx_of_landing.h_fV := relay(local:accum_content_pending.h_fV)",
   "accum_content_pending #1 ctor:pendingProps.h_closeFE := imp:door:pendingProps.h_closeFE{step(relay(door:pendingProps.h_closeFE))}",
   "accum_content_pending #1 ctor:pendingProps.h_closeF := imp:door:pendingProps.h_closeF{step(relay(door:pendingProps.h_closeF))}",
   "accum_content_pending #1 ctor:pendingProps.h_closeFV := imp:door:pendingProps.h_closeFV{step(relay(door:pendingProps.h_closeFV))}",
   "accum_content_pending #2 ctor:pendingProps.h_closeFE := imp:door:pendingProps.h_closeFE{step(relay(door:pendingProps.h_closeFE))}",
   "accum_content_pending #2 ctor:pendingProps.h_closeF := imp:door:pendingProps.h_closeF{step(relay(door:pendingProps.h_closeF))}",
   "accum_content_pending #2 ctor:pendingProps.h_closeFV := imp:door:pendingProps.h_closeFV{step(relay(door:pendingProps.h_closeFV))}",
   "accum_content_pending #1 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #1 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #2 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #2 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #1 local:accum_content_pending.h_closeFE_k := cases[paid{cover=relay(door:pendingProps.h_closeFE)}|punt]",
   "accum_content_pending #1 ctor:pendingBlockContent.h_closeF := match[paid{cover=step(relay(local:accum_content_pending.h_closeFE_k))}|punt]",
   "accum_content_pending #3 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #3 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #2 ctor:pendingBlockContent.h_closeF := match[paid{cover=step(relay(local:accum_content_pending.h_closeFE_k))}|punt]",
   "accum_content_pending #4 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #4 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #3 ctor:pendingBlockContent.h_closeF := match[paid{cover=step(relay(local:accum_content_pending.h_closeFE_k))}|punt]",
   "accum_content_pending #5 ctor:pendingContent.h_framesS := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #5 ctor:pendingContent.h_framesV := match[paid{cover=step(relay(door:pendingProps.h_closeFE))}|punt]",
   "accum_content_pending #2 fnp:accum_content_pending.h_defer_split.h_fS := punt",
   "accum_content_pending #2 fnp:accum_content_pending.h_defer_split.h_fV := punt",
   "accum_content_pending #3 fnp:accum_content_pending.h_defer_split.h_fS := punt",
   "accum_content_pending #3 fnp:accum_content_pending.h_defer_split.h_fV := punt",
   -- Item 284: `pendingFlow`'s call (#4, punt/punt) is gone — that arm defers at
   -- every landing now — so `pendingBlockContent`'s call, #5, is #4.
   "accum_content_pending #4 fnp:accum_content_pending.h_defer_split.h_fS := match[paid{cover=step(relay(door:pendingBlockContent.h_closeF))}|punt]",
   "accum_content_pending #4 fnp:accum_content_pending.h_defer_split.h_fV := match[paid{cover=punt}|punt]",
   "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_closeF_old := relay(door:pendingBlock.h_closeF)",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_closeF99 := imp:door:pendingMapValue.h_closeF{relay(door:pendingMapValue.h_closeF)}",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_frames99 := relay(door:pendingMapValue.h_frames)",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_closeFV108 := relay(door:pendingMapValue.h_closeFV)",
   "accum_content_pending #1 param:accum_content_on_pendingMapValue_indented.h_framesV108 := relay(door:pendingMapValue.h_framesV)",
   -- 2026-10-29 (item 394): both flow closes relay `FlowBaseRoutes.valueF` into `h_framesS` (`.imp` over the field; its own `∨ True` is the punt the reader names).
   "accum_step_flow #1 ctor:pendingContent.h_framesS := imp:ret:valueF{lit(lo=lo,idx=lo,ks=x✝,by=other(Exists.intro))}",
   "accum_step_flow #1 ctor:pendingContent.h_framesV := elim[punt|punt]",
   "accum_step_flow #2 ctor:pendingContent.h_framesS := imp:ret:valueF{lit(lo=lo,idx=lo,ks=x✝,by=other(Exists.intro))}",
   "accum_step_flow #2 ctor:pendingContent.h_framesV := elim[punt|punt]",
   "colon_fires_implicit_key #1 param:colon_open_map_implicit.h_routeF := cases[paid{cover=step(relay(fnparam:colon_fires_implicit_key.h_key))}|punt]",
   "colon_fires_implicit_key #1 param:colon_open_map_implicit.h_routeFV := cases[paid{cover=step(relay(fnparam:colon_fires_implicit_key.h_key))}|punt]",
   "colon_fires_props_key #1 param:colon_open_map_props.h_routeF := cases[paid{cover=step(relay(fnparam:colon_fires_props_key.h_key))}|punt]",
   "colon_fires_props_key #1 param:colon_open_map_props.h_routeFV := cases[paid{cover=step(relay(fnparam:colon_fires_props_key.h_key))}|punt]",
   "colon_open_map #1 val:colon_open_map.h✝ := match[punt|step(relay(param:colon_open_map.h_cov_in))|step(relay(param:colon_open_map.h_cov_in))|step(relay(param:colon_open_map.h_cov_in))|step(relay(param:colon_open_map.h_cov_in))|step(relay(param:colon_open_map.h_cov_in))]",
   "colon_open_map #1 ctor:pendingMapValue.h_closeF := paid{cover=relay(val:colon_open_map.h✝)}",
   "colon_open_map #1 ctor:pendingMapValue.h_frames := paid{cover=relay(val:colon_open_map.h✝)}",
   "colon_open_map #1 ctor:pendingMapValue.h_closeFV := match[paid{cover=punt}|punt]",
   "colon_open_map #1 ctor:pendingMapValue.h_framesV := match[paid{cover=punt}|punt]",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_closeFV := elim[punt|punt]",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_framesV := elim[punt|punt]",
   "colon_open_map_implicit #1 fn:colon_open_map_implicit.h_cov_step := via:Covered.dedup_head(via:IndentStackCover.scanValue_cover_key(via:Covered.of_indents_eq(relay(fnp:colon_open_map_implicit.h_cov_step.hc))))",
   "colon_open_map_implicit #1 ctor:pendingMapValue.h_closeF := match[paid{cover=step(relay(param:colon_open_map_implicit.h_routeF))}|punt]",
   "colon_open_map_implicit #1 ctor:pendingMapValue.h_frames := match[paid{cover=step(relay(param:colon_open_map_implicit.h_routeF))}|punt]",
   "colon_open_map_implicit #1 ctor:pendingMapValue.h_closeFV := match[paid{cover=step(relay(param:colon_open_map_implicit.h_routeFV))}|punt]",
   "colon_open_map_implicit #1 ctor:pendingMapValue.h_framesV := match[paid{cover=step(relay(param:colon_open_map_implicit.h_routeFV))}|punt]",
   "colon_open_map_props #1 fn:colon_open_map_props.h_cov_step := via:Covered.dedup_head(via:IndentStackCover.scanValue_cover_key(via:Covered.of_indents_eq(relay(fnp:colon_open_map_props.h_cov_step.hc))))",
   "colon_open_map_props #1 ctor:pendingMapValue.h_closeF := match[paid{cover=step(relay(param:colon_open_map_props.h_routeF))}|punt]",
   "colon_open_map_props #1 ctor:pendingMapValue.h_frames := match[paid{cover=step(relay(param:colon_open_map_props.h_routeF))}|punt]",
   "colon_open_map_props #1 ctor:pendingMapValue.h_closeFV := match[paid{cover=step(relay(param:colon_open_map_props.h_routeFV))}|punt]",
   "colon_open_map_props #1 ctor:pendingMapValue.h_framesV := match[paid{cover=step(relay(param:colon_open_map_props.h_routeFV))}|punt]",
   "compact_open_map #1 ctor:pendingMapValue.h_closeF := paid{cover=lit(lo=n + 1,idx=n + 1 + m,ks=map(…) :: [],by=via:CoverStep.cons_of_top_eq(via:IndentStackCover.dispatchBlockIndicators_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(lemma(IndentStackCover.covered_nil_of_top_le))))))}",
   "compact_open_map #1 ctor:pendingMapValue.h_closeFV := elim[punt|punt]",
   "compact_open_map #1 ctor:pendingMapValue.h_framesV := elim[punt|punt]",
   "content_dispatch_routed #1 fn:content_dispatch_routed.h_cov_lift := via:IndentStackCover.dispatchContent_cover(via:Covered.of_indents_eq(relay(fnp:content_dispatch_routed.h_cov_lift.hc)))",
   "content_dispatch_routed #1 ctor:pendingProps.h_closeFE := punt",
   "content_dispatch_routed #1 ctor:pendingProps.h_closeF := punt",
   "content_dispatch_routed #1 ctor:pendingProps.h_closeFV := punt",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeFE := punt",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeF := punt",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeFV := punt",
   "content_dispatch_routed #1 ctor:pendingContent.h_framesS := punt",
   "content_dispatch_routed #1 ctor:pendingContent.h_framesV := punt",
   "content_dispatch_routed #2 ctor:pendingContent.h_framesS := punt",
   "content_dispatch_routed #2 ctor:pendingContent.h_framesV := punt",
   "dedent_cover_of_landing #1 param:dedent_cover_of_floor.h_cv := relay(fnparam:dedent_cover_of_landing.h_cov_step)",
   "entryKeyPack_of_dispatch #1 fn:entryKeyPack_of_dispatch.h_cov_step := via:IndentStackCover.dispatchContent_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(fnp:entryKeyPack_of_dispatch.h_cov_step.hc))))",
   "entryKeyPack_of_dispatch #1 fn:entryKeyPack_of_dispatch.h_pay := via:StreamAccum.dedent_cover_of_landing(relay(param:entryKeyPack_of_dispatch.h_dframes))",
   "entryKeyPack_of_dispatch #1 fn:entryKeyPack_of_dispatch.h_payV := via:StreamAccum.dedent_cover_of_landing(relay(fnp:entryKeyPack_of_dispatch.h_payV.h_cv))",
   -- Item 372 (2026-10-27): exit (a) spends the park's cover on `preprocess_landing_mem_or_seq`.
   "entryKeyPack_of_dispatch #1 param:preprocess_landing_mem_or_seq.h_cov := relay(param:entryKeyPack_of_dispatch.h_dframes)",
   "entryPropsKeyPack_of_dispatch #1 fn:entryPropsKeyPack_of_dispatch.h_cov_step := via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(fnp:entryPropsKeyPack_of_dispatch.h_cov_step.hc)))",
   "entryPropsKeyPack_of_dispatch #1 fn:entryPropsKeyPack_of_dispatch.h_pay := via:StreamAccum.dedent_cover_of_landing(relay(param:entryPropsKeyPack_of_dispatch.h_dframes))",
   "entryPropsKeyPack_of_dispatch #1 fn:entryPropsKeyPack_of_dispatch.h_payV := via:StreamAccum.dedent_cover_of_landing(relay(fnp:entryPropsKeyPack_of_dispatch.h_payV.h_cv))",
   "indicator_open_map #1 fn:indicator_open_map.h_cov_in := cases[lit(lo=—,idx=—,ks=map(…) :: [],by=lemma(StreamAccum.indicator_cover_at_col))|punt]",
   "indicator_open_map #1 param:colon_open_map.h_cov_in := step(relay(fn:indicator_open_map.h_cov_in))",
   "indicator_open_map #1 param:question_open_map.h_cov_in := step(relay(fn:indicator_open_map.h_cov_in))",
   "indicator_open_map #1 param:question_open_map.h_cov_nil := step(relay(fn:indicator_open_map.h_cov_in))",
   "question_open_map #1 val:question_open_map.h✝ := match[punt|step(relay(param:question_open_map.h_cov_in))|step(relay(param:question_open_map.h_cov_in))|step(relay(param:question_open_map.h_cov_in))|step(relay(param:question_open_map.h_cov_in))|step(relay(param:question_open_map.h_cov_in))]",
   "question_open_map #1 ctor:pendingMapValue.h_closeF := paid{cover=relay(val:question_open_map.h✝)}",
   "question_open_map #1 ctor:pendingMapValue.h_frames := paid{cover=relay(val:question_open_map.h✝)}",
   "question_open_map #1 ctor:pendingMapValue.h_closeFV := paid{cover=step(relay(param:question_open_map.h_cov_nil))}",
   "question_open_map #1 ctor:pendingMapValue.h_framesV := paid{cover=step(relay(param:question_open_map.h_cov_nil))}",
   "accum_block_on_closeThenBlock #1 param:landing_frame_of_cover.h_cov := via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(param:accum_block_on_closeThenBlock.h_mapFV)))",
   "accum_block_on_pendingBlock #1 param:accum_block_on_closeThenBlock.h_mapFV := match[paid{cover=step(relay(param:accum_block_on_pendingBlock.h_closeFV_old))}|punt]",
   "accum_block_on_pendingBlock #1 param:landing_frame_of_cover.h_cov := via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(param:accum_block_on_pendingBlock.h_closeFV_old)))",
   "accum_block_on_pendingBlock #1 param:preprocess_landing_mem_or_seq.h_cov := relay(param:accum_block_on_pendingBlock.h_closeF_old)",
   "accum_block_on_pendingBlockContent #1 param:accum_block_on_closeThenBlock.h_mapFV := match[paid{cover=step(relay(param:accum_block_on_pendingBlockContent.h_closeFV_old))}|punt]",
   "accum_block_on_pendingBlockContent #1 param:landing_frame_of_cover.h_cov := via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(relay(param:accum_block_on_pendingBlockContent.h_closeFV_old)))",
   "accum_block_on_pendingBlockContent #1 param:preprocess_landing_mem_or_seq.h_cov := relay(param:accum_block_on_pendingBlockContent.h_closeF_old)",
   "accum_block_on_pendingContent #1 param:accum_block_on_closeThenBlock.h_mapFV := imp:?{punt}",
   "accum_block_on_pendingContent #2 param:accum_block_on_closeThenBlock.h_mapFV := imp:?{punt}",
   "accum_block_pending #1 param:accum_block_on_closeThenBlock.h_mapFV := match[paid{cover=relay(door:pendingProps.h_closeFV)}|punt]",
   "accum_block_pending #2 param:accum_block_on_closeThenBlock.h_mapFV := match[paid{cover=relay(door:pendingProps.h_closeFV)}|punt]",
   "accum_block_pending #3 param:accum_block_on_closeThenBlock.h_mapFV := punt",
   "accum_block_pending #4 param:accum_block_on_closeThenBlock.h_mapFV := punt",
   "accum_block_pending #5 param:accum_block_on_closeThenBlock.h_mapFV := punt",
   "accum_block_pending #6 param:accum_block_on_closeThenBlock.h_mapFV := imp:door:pendingMapValue.h_framesV{step(relay(door:pendingMapValue.h_framesV))}",
   "accum_block_pending #7 param:accum_block_on_closeThenBlock.h_mapFV := imp:door:pendingMapValue.h_framesV{step(relay(door:pendingMapValue.h_framesV))}",
   "landing_frame_of_cover #1 param:landing_mem_of_key.h_cov := relay(param:landing_frame_of_cover.h_cov)",
   -- Item 364: the K1-fresh cover on `pendingBlock`/`pendingBlockContent.h_closeFV` — 5 ctor rows
   -- carry it by step relay, 3 param relays route it through the door, 8 ctor rows decline it
   -- (consed `seq n :: ks` = K1-seq, or a coverless source twin).
   "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_closeFV := imp:?{punt}",
   "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_closeFV := match[paid{cover=lit(lo=nv + 1,idx=nv + 1 + m,ks=[],by=via:IndentStackCover.scanBlockEntry_cover(via:Covered.of_indents_eq(via:IndentStackCover.preprocess_cover(lemma(IndentStackCover.covered_nil_of_top_le)))))}|punt]",
   "accum_block_on_noPending #1 ctor:pendingBlock.h_closeFV := punt",
   "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_closeFV := match[paid{cover=step(relay(param:accum_block_on_pendingBlock.h_closeFV_old))}|punt]",
   "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_closeFV := match[paid{cover=punt}|punt]",
   "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_closeFV := match[paid{cover=punt}|punt]",
   "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_closeFV := match[paid{cover=step(relay(param:accum_block_on_pendingBlockContent.h_closeFV_old))}|punt]",
   "accum_block_pending #1 param:accum_block_on_pendingBlockContent.h_closeFV_old := imp:door:pendingBlockContent.h_closeFV{relay(door:pendingBlockContent.h_closeFV)}",
   "accum_block_pending #1 param:accum_block_on_pendingBlock.h_closeFV_old := imp:door:pendingBlock.h_closeFV{relay(door:pendingBlock.h_closeFV)}",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingBlockContent.h_closeFV := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeFV_old))}|punt]",
   "accum_content_on_pendingBlock_indented #2 ctor:pendingBlockContent.h_closeFV := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeFV_old))}|punt]",
   "accum_content_on_pendingBlock_indented #3 ctor:pendingBlockContent.h_closeFV := match[paid{cover=step(relay(param:accum_content_on_pendingBlock_indented.h_closeFV_old))}|punt]",
   "accum_content_pending #1 ctor:pendingBlockContent.h_closeFV := match[paid{cover=punt}|punt]",
   "accum_content_pending #2 ctor:pendingBlockContent.h_closeFV := match[paid{cover=punt}|punt]",
   "accum_content_pending #3 ctor:pendingBlockContent.h_closeFV := match[paid{cover=punt}|punt]",
   "accum_content_pending #1 param:accum_content_on_pendingBlock_indented.h_closeFV_old := imp:door:pendingBlock.h_closeFV{relay(door:pendingBlock.h_closeFV)}",
   -- 2026-10-26 (item 369): 198 → 199 — `accum_block_on_pendingBlock.h_closeF_old` relays `pendingBlock.h_closeF`
   "accum_block_pending #1 param:accum_block_on_pendingBlock.h_closeF_old := relay(door:pendingBlock.h_closeF)",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_closeF := paid{cover=punt}",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_frames := paid{cover=punt}",
   "compact_open_map #1 ctor:pendingMapValue.h_frames := paid{cover=punt}",
   -- Item 374: the props twin declines the face (h_rc) and `resumectx_of_landing`
   -- spends its cover on `preprocess_landing_mem_or_seq`.
   "content_dispatch_routed #1 local:content_dispatch_routed.h_rc := elim[elim[paid{cover=relay(fnparam:content_dispatch_routed.h_resumectx)}|punt]|punt]",
   "resumectx_of_landing #1 param:preprocess_landing_mem_or_seq.h_cov := relay(param:resumectx_of_landing.h_fS)"]
-- Item 259: the compact opener's payment of `pendingMapValue.h_closeF` is a
-- leaf of ALL FOUR trees — the mapping value field is a position of the
-- content and entry trees through `accum_block_pending`'s door and of the
-- value-frames tree through the same relay — so each reads one more paid
-- leaf and one punt fewer (`valF` was not predicted; the other three were).
-- 2026-10-26 (item 370): `content:`/`entry:` trees gain one position and one row and lose one punt — the sibling `-`
-- arm's `pendingBlock.h_closeF` relay of `h_closeF_old`.
-- Item 371: the paid `h_closeF`/`h_frames` at `colon_open_map_explicit`/`compact_open_map` carry a punted
-- cover conjunct (`Or.inr trivial`) — the trees read them as `cover-punt`, one fewer plain punt each.
-- 2026-10-29 (item 388): content/entry trees cover-punt 3 → 4 — the landed birth's `nv ≤ k` arm carries the
-- frames' cover as `Or.inr trivial` (frames `[]`, nothing to cover), one more punt leaf on each tree.
def expectedTrees : List String :=
  ["content: positions=17 rows=48 leaves[cover-punt=4 open:fnparam:colon_fires_implicit_key.h_key=1 open:fnparam:colon_fires_props_key.h_key=1 paid=6 punt=13] open=2",
   "entry: positions=17 rows=48 leaves[cover-punt=4 open:fnparam:colon_fires_implicit_key.h_key=1 open:fnparam:colon_fires_props_key.h_key=1 paid=6 punt=13] open=2",
   "valF: positions=9 rows=24 leaves[cover-punt=1 open:fnparam:colon_fires_implicit_key.h_key=1 open:fnparam:colon_fires_props_key.h_key=1 paid=2 punt=10] open=2",
   "mapValue: positions=8 rows=13 leaves[cover-punt=1 open:fnparam:colon_fires_implicit_key.h_key=1 open:fnparam:colon_fires_props_key.h_key=1 paid=2 punt=1] open=2"]
-- 2026-10-26 (item 369): `accum_block_on_pendingBlock` row re-read — `h_closeF_old` (the `-` park's frames) joins its binders.
def expectedEight : List String :=
  -- item 386: `top=2` — the `-` opener reads the park's LEVEL at or below the top
  -- (`h_lvl_old`, `IndentFloor`'s second conjunct) beside the top's bound (`h_top_old`).
  ["accum_block_on_pendingBlock indicator_open_map.h_stream_land indents=0 top=2(h_top_old,h_lvl_old) floor=0 minCI=0 nic=1(h_nic_old) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeFV_old@2,h_closeF_old@2)",
   "accum_block_on_pendingBlock colon_open_map_explicit.h_stream_mid indents=0 top=2(h_top_old,h_lvl_old) floor=0 minCI=0 nic=1(h_nic_old) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeFV_old@2,h_closeF_old@2)",
   "accum_block_on_pendingBlock block_dispatch_deferred_stamp_offcol.h_stream indents=0 top=2(h_top_old,h_lvl_old) floor=0 minCI=0 nic=1(h_nic_old) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeFV_old@2,h_closeF_old@2)",
   "accum_block_on_pendingBlock block_dispatch_deferred_stamp_nopack.h_stream indents=0 top=2(h_top_old,h_lvl_old) floor=0 minCI=0 nic=1(h_nic_old) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeFV_old@2,h_closeF_old@2)",
   "accum_block_on_pendingBlockContent indicator_open_map.h_stream_land indents=0 top=0 floor=0 minCI=0 nic=1(h_nic0) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeF_old@2,h_closeFV_old@2)",
   "accum_block_on_pendingBlockContent colon_open_map_explicit.h_stream_mid indents=0 top=0 floor=0 minCI=0 nic=1(h_nic0) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeF_old@2,h_closeFV_old@2)",
   "accum_block_on_pendingBlockContent block_dispatch_deferred_stamp_offcol.h_stream indents=0 top=0 floor=0 minCI=0 nic=1(h_nic0) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeF_old@2,h_closeFV_old@2)",
   "accum_block_on_pendingBlockContent block_dispatch_deferred_stamp_nopack.h_stream indents=0 top=0 floor=0 minCI=0 nic=1(h_nic0) prep=1(h_preprocess) base=1(h_base) mono=1(h_mono) cover=2(h_closeF_old@2,h_closeFV_old@2)"]
-- 2026-10-26 (item 369): the `-` park's `h_closeF` now feeds `accum_block_on_pendingBlock` (was dropped).
-- 2026-10-29 (item 394, option B): +1 door — accum_flow_open_depth0 reads pendingMapValue.h_closeF's
-- cover through Covered.of_subset (preprocess_indents_subset) into FlowBaseRoutes.valueF.
def expectedDoor : List String :=
  ["accum_block_pending: door:pendingBlock.h_closeF → accum_block_on_pendingBlock.h_closeF_old kept",
   "accum_block_pending: door:pendingBlockContent.h_closeF → accum_block_on_pendingBlockContent.h_closeF_old kept",
   "accum_block_pending: door:pendingContent.h_framesS → accum_block_on_pendingContent.h_mapF109 forgotten",
   "accum_block_pending: door:pendingContent.h_framesV → accum_block_on_pendingContent.h_mapFV108 forgotten",
   "accum_block_pending: door:pendingMapValue.h_closeF → accum_block_on_closeThenBlock.h_valF kept",
   "accum_block_pending: door:pendingMapValue.h_closeFV → accum_block_on_closeThenBlock.h_valFV forgotten",
   "accum_block_pending: door:pendingMapValue.h_frames → accum_block_on_closeThenBlock.h_mapF forgotten",
   "accum_block_pending: door:pendingMapValue.h_framesV → accum_block_on_closeThenBlock.h_mapFV kept",
   "accum_block_pending: door:pendingProps.h_closeF dropped",
   "accum_block_pending: door:pendingProps.h_closeFE dropped",
   -- 2026-10-23 (item 344): the props park's `h_closeFV` now feeds the relayed `h_mapFV` (was dropped).
   "accum_block_pending: door:pendingProps.h_closeFV → accum_block_on_closeThenBlock.h_mapFV kept",
   "accum_content_pending: door:pendingBlock.h_closeF → accum_content_on_pendingBlock_indented.h_closeF_old kept",
   "accum_content_pending: door:pendingBlockContent.h_closeF → local:h_defer_split.h_fS kept",
   "accum_content_pending: door:pendingContent.h_framesS → local:h_defer_split.h_fS kept",
   "accum_content_pending: door:pendingContent.h_framesV → local:h_defer_split.h_fV kept",
   "accum_content_pending: door:pendingMapValue.h_closeF → accum_content_on_pendingMapValue_indented.h_closeF99 kept",
   "accum_content_pending: door:pendingMapValue.h_closeFV → accum_content_on_pendingMapValue_indented.h_closeFV108 kept",
   "accum_content_pending: door:pendingMapValue.h_frames → accum_content_on_pendingMapValue_indented.h_frames99 kept",
   "accum_content_pending: door:pendingMapValue.h_framesV → accum_content_on_pendingMapValue_indented.h_framesV108 kept",
   "accum_flow_open_depth0: door:pendingBlock.h_closeF dropped",
   "accum_flow_open_depth0: door:pendingBlockContent.h_closeF → local:main.a✝ forgotten",
   "accum_flow_open_depth0: door:pendingContent.h_framesS → local:main.a✝ forgotten",
   "accum_flow_open_depth0: door:pendingContent.h_framesV → local:main.a✝ forgotten",
   -- 2026-10-29 (item 394): `accum_flow_open_depth0`'s mapping arm now READS `pendingMapValue.h_closeF` (it supplies `FlowBaseRoutes.valueF`); the dropped-door row is gone (doors 49 → 48).
   "accum_flow_open_depth0: door:pendingMapValue.h_closeFV dropped",
   "accum_flow_open_depth0: door:pendingMapValue.h_frames dropped",
   "accum_flow_open_depth0: door:pendingMapValue.h_framesV dropped",
   "accum_flow_open_depth0: door:pendingProps.h_closeF dropped",
   "accum_flow_open_depth0: door:pendingProps.h_closeFE dropped",
   "accum_flow_open_depth0: door:pendingProps.h_closeFV dropped",
   "accum_structural_pending: door:pendingBlock.h_closeF dropped",
   "accum_structural_pending: door:pendingBlockContent.h_closeF dropped",
   "accum_structural_pending: door:pendingContent.h_framesS dropped",
   "accum_structural_pending: door:pendingContent.h_framesV dropped",
   "accum_structural_pending: door:pendingMapValue.h_closeF dropped",
   "accum_structural_pending: door:pendingMapValue.h_closeFV dropped",
   "accum_structural_pending: door:pendingMapValue.h_frames dropped",
   "accum_structural_pending: door:pendingMapValue.h_framesV dropped",
   "accum_structural_pending: door:pendingProps.h_closeF dropped",
   "accum_structural_pending: door:pendingProps.h_closeFE dropped",
   "accum_structural_pending: door:pendingProps.h_closeFV dropped",
   -- Item 364: the two `h_closeFV` doors now carry the cover — kept by the four block/content
   -- relays, dropped/forgotten by the flow-open and structural parks (coverless lanes).
   "accum_block_pending: door:pendingBlock.h_closeFV → accum_block_on_pendingBlock.h_closeFV_old kept",
   "accum_block_pending: door:pendingBlockContent.h_closeFV → accum_block_on_pendingBlockContent.h_closeFV_old kept",
   "accum_content_pending: door:pendingBlock.h_closeFV → accum_content_on_pendingBlock_indented.h_closeFV_old kept",
   "accum_content_pending: door:pendingBlockContent.h_closeFV → local:h_defer_split.h_fV kept",
   "accum_flow_open_depth0: door:pendingBlock.h_closeFV dropped",
   "accum_flow_open_depth0: door:pendingBlockContent.h_closeFV → local:main.a✝ forgotten",
   "accum_structural_pending: door:pendingBlock.h_closeFV dropped",
   "accum_structural_pending: door:pendingBlockContent.h_closeFV dropped",
   "accum_flow_open_depth0: door:pendingMapValue.h_closeF → of_subset.h kept"
  ]
/-- **The walk's own line.**  `nodes` is the proof-term size of the twenty-four
    declarations walked, and it is the one reading item 272 moves: carrying
    item 147's floor gives `preprocess_some_separate_at_floor`'s under-run
    disjunct a sixth component, which the three arms of
    `accum_flow_open_depth0` each destructure and none yet reads, so the term
    grows and no door, no cover and no verdict changes.

    Lean v4.35.0 moves it again, downward and alone: `nodes` 96158 → 96125.
    Every other field on this line — and every named roster above — is
    byte-identical, so the toolchain elaborates these twenty-four declarations
    to 33 fewer term nodes and changes nothing the walk concludes.

    Item 284 moves three fields.  `rows` 169 → 167 and `fnpRows` 10 → 8 are
    `accum_content_pending`'s `pendingFlow` arm, whose builder call (two `punt`
    rows) is gone because the arm defers at every landing; `pendingBlockContent`'s
    call renumbers #5 → #4 and its rows are otherwise byte-identical.  `nodes`
    96125 → 97863 is the walked terms growing — the under-run's seventh component
    destructured in `accum_flow_open_depth0`'s three arms, the producers' new
    field payments and the gate parameters — and no door, cover or verdict moves.
    Item 285 moves `nodes` alone, 97863 → 98193: the walked arm lemma gains
    `slot_ride`'s frame and its three spends; every row, door and cover holds.
    Item 287 moves `nodes` alone, 98193 → 98962: the walked terms carry the
    inline residue's readings — the refutations at the crossed-break arms and
    the deferrals at the seven — where they carried a fallback stream; every
    row, door and cover holds.  Item 288 moves `nodes` alone, 98962 → 99100:
    the value park's frameless arm refutes where it deferred.  Item 289 moves
    `nodes` alone, 99100 → 99114, and the walk run per declaration names both
    terms: `accum_content_pending` +12, whose three `keyPackPunt_transport`
    calls each pass the new possibility premise, and `accum_flow_open_depth0`
    +2, whose `tab` arm binds the reason's two new fields
    (`scratchpad/l4yaml-row12-steps/317-csc-perdecl.log`).  Item 293 moves
    `nodes` alone, 99114 → 100079, and the same per-declaration run names all
    of it (`375-csc-perdecl-293.log`): `accum_content_pending` +674 — the props
    arm's eight `h_live` payments, its run extensions' `h_poss`, the
    possibility the routed and document-start content take, and the escape
    park's `content_live0` — and `accum_flow_open_depth0` +188, the eight
    opens paying their saved key's possibility.  The other +103 are the four
    new park fields bound at each eliminator (+1 to +5 per declaration),
    `arm_tight_or_col`'s `Or.inl` (+27) and `accum_block_pending`'s threading
    (+29).  Item 295 moves `nodes` alone, 100079 → 100098: its three fixes
    are all in `accum_flow_open_depth0`, the one declaration whose term
    changed — `slot_ride`'s frame built field by field, the two indicator
    parks' own flags, and the props arm's fallback route.  Item 296 moves
    `nodes` alone, 100098 → 100108: the dedent branch's frameless exit in the
    two entry pack producers, the only declarations whose terms changed.  Item
    297 moves `nodes` alone, 100108 → 100103, the net over the walked
    declarations whose terms changed: the two producers' `w ∉ ks` exits grow
    by the fresh-document terms, and the `dedent` alternatives of
    `accum_flow_open_depth0` and the two `:` consumers go with the
    constructor.  Item 299 moves `nodes` alone, 100103 → 100339: the walked
    declarations that build a `pendingDocStart` pass its new `h_docline`
    field, and the six that apply `dispatch_refutes_sameLine` pass its new
    `h_dsl_eq` premise — the `docStartLine` field's transport through
    preprocessing; no row, door or cover moves.  Item 300 moves `nodes` alone,
    100339 → 100885: the marker reason's productions and refutations in the
    walked declarations — the content dispatch's two cascades and its `---`
    caller's payment, the flow close's third base reading, the flow open's
    marker argument at seven arms, the two `:` consumers' new arms, and the
    mask's maintenance lemmas carrying the field; no row, door or cover
    moves. -/
-- Item 305: the sequence fields carry the width bound `∀ k' ∈ ks, k' < n` and the nested arms push the
-- entry's level (`KeyFrames.seqLevel`): `nodes` 100885 → 101410.
-- 2026-10-20 (item 306): the six key-pack stack rows are matches on `h_closeFV_old` (paid, cover punted | punt) where item 108 left bare punts: `nodes` 101410 → 101421.
-- 2026-10-20 (item 307): the γ roots' pack and stack from the closed park's stack, the landed arm's resume: `nodes` 101421 → 101427.
-- 2026-10-20 (item 309): the generic helpers'  terms: `nodes` 101427 → 101432.
-- 2026-10-21 (item 311): the named alternative's definitions and stubs (`PackAlt`, `PackAltG`, `ofRefused`, `ofPark`,
-- `ofGateClose`), the four conversions at the frame crossings and the two `.imp id PackAlt.ofGateClose` wrappers at the
-- closes: `nodes` 101432 → 101924; every row stands (167), with `colon_open_map_implicit`'s generic `h_routeFV` read as
-- the cover-carrying parameter it is (`isOptAlt`).
-- 2026-10-21 (item 313): `nodes` 101924 → 103174 — `ExplicitValueRefused.step_content`, `PackAlt.step_content` and the
-- content lane's twenty-one `.imp id (PackAlt.step_content …)` wrappers; every row stands.
-- 2026-10-21 (item 314): `nodes` 103174 → 103286 — `ExplicitValueRefused.step_dispatch`, `PackAlt.step_dispatch` and the
-- content lane's sixty-one leaf payments (each `Or.inr trivial` an application or a hypothesis now); every row stands.
-- 2026-10-21 (item 315): `nodes` 103286 → 103289 — the key-pack lemmas' six arms step through the wrapper (three a side).
-- 2026-10-21 (item 320): `nodes` 103289 → 103324 — the marker parks' new field (`h_noek`) at the three producers, the eight
-- `PackAlt.ofRefused h_noek…` payments, the `h_seqFramesV` relay and the two split arms grow the family's terms; rows stand.
-- 2026-10-21 (item 322): `nodes` 103324 → 103328 — the two colon openers' new step premise
-- (`h_alt_step`) and the six leaves and two callers that spend it; rows stand.
-- 2026-10-21 (item 324): `nodes` 103328 → 103335 — this item's payments in the flow opener and the resume context
-- (applications where `trivial` stood) grow the walked terms; `walked` and every row stand.
-- 2026-10-23 (item 344): `doorForgotten` 8 → 9, `doorDropped` 23 → 22, `nodes` 104597 → 104913 — the block-park relays read the props park's `h_closeFV`.
-- 2026-10-23 (item 345): nodes 104913 → 105448 — the two `h_fV` rows above now case on the park's `h_closeFV`.
-- 2026-10-23 (item 349): `nodes` 105448 → 105463 — `h_dead` threaded through the content step.
-- 2026-10-24 (item 350): nodes 105463 → 105571 — the `:` producers' `dispatchBlock_colon_notQuestion`
-- payments and the consumers' empty-chain terms; no cover column moved.
-- 2026-10-23 (item 345): nodes 105571 → 105560
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-25 (#99 review): nodes=115233 → nodes=115369 — the dead `FlowLead` + two lemmas deleted; `leadFree`/`closeFree` are `Bool` (walked-term total).
-- 2026-10-26 (item 367, `[82]`): nodes 117899 → 117863 (walked-term total) — the two directive sites in StreamAccum now apply `scannedDirective_toSL` instead of destructuring `scanDirective_prod`'s `rest`/`hchars` and rebuilding `SLDirective.mk`; the cover rows are unchanged.
-- 2026-10-26 (item 369): lemParams=34 → lemParams=35, rows=198 → rows=199, lemRows=73 → lemRows=74, doorKept=16 → doorKept=17, doorDropped=25 → doorDropped=24, nodes=117863 → nodes=117865 — `pendingBlock.h_closeF` kept through the `accum_block_pending` door into `accum_block_on_pendingBlock.h_closeF_old`.
-- 2026-10-26 (item 370): the sibling `-` arm relays `h_closeF_old` into `pendingBlock.h_closeF` — one more relayed door row, one fewer punt.
-- 2026-10-28 (item 385): positions 23 → 24, lemParams 35 → 36, lemmas 18 → 19, rows 204 → 206, lemRows 78 → 80, nodes 120362 → 120403
-- — `deeperLandingResume` is one more walked lemma (its `h_valF` param, relayed at `closeThenBlock`'s two no-pop leaves).
-- 2026-10-29 (item 387): nodes 121047 → 121051 — the no-pop arm's `dite n < k` at
-- `accum_block_on_pendingBlock` (the helper now takes the strict bound; `k = n` splits on the sequence top).
-- 2026-10-29 (item 388): summary contentCoverPunt 3 → 4, entryCoverPunt 3 → 4, nodes 121051 → 121397 — the `nv ≤ k` arm (see expectedRows/expectedTrees).
-- 2026-10-29 (item 389): nodes 122973 → 122297 (from the pre-review 122973) — proof-term size only: the `-` park births' relays and refutations, the conjunct resuming the park's own `ks` after review; no cover row moved.
-- 2026-10-29 (item 394, option B): h_framesS paid at both flow closes (valueF's cover), the
-- of_subset door into valueF; the summary's paid/punt and door counts move accordingly.
-- 2026-10-29 (item 396): flowOpen_floor_at_prep deleted and content_dispatch_after_close's four contexts restated — rows/doors/nodes follow.
-- 2026-10-30 (item 405): the `?`-park chain ladder PAID — `closeThenBlock`'s births destructure `hkvUp` beside `hkv`; the content twin rides the chain.
def expectedLine : String :=
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); nodes 117690 → 117529 (walked-term total; the `elim[punt|punt]` face rows unchanged).
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`); the three `match h_kslot_* with` blocks go — nodes 117529 → 117431 (walked-term total).
  -- 2026-10-26 (item 365): nodes 117848 → 117885 — the `h_refused` decision at the top of the three content
  -- lemmas and the eleven `h_alt := h_refused.elim …` arguments; no cover row moved.
  -- 2026-10-26 (item 366): nodes 117885 → 117899 — the two `Classical.em` pays of `h_outer` in
  -- `accum_block_on_closeThenBlock`; no row of this guard moved.
-- Item 371 (pmvPunt=1 → 0, pmvCoverPunt=0 → 1, contentPunt=14 → 13, contentCoverPunt=2 → 3, entryPunt=14 → 13, entryCoverPunt=2 → 3, nodes=117865 → 119846): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
-- Item 372 (2026-10-27): exit (a)'s cover spend on `preprocess_landing_mem_or_seq` (one more lemma relay row).
-- Item 386 (2026-10-28): nodes 120403 → 121047 — the level conjunct in `h_valF`, the `-` opener's `h_lvl_old`, the helpers' sibling/absurd terms; no row moved.
  -- 2026-10-29 (item 394): `pendingMapValue.h_closeF` is READ at the flow open (doorUses 49 → 48, doorDropped 24 → 23); the valueF supply and relays grow the term (nodes 122297 → 122509).
  "positions=24 ctorFields=13 lemParams=36 lemmas=19 walked=26 doors=9 rows=206 ctorRows=92 lemRows=80 localRows=5 fnRows=19 fnpRows=8 valRows=2 coverTypes=5 mentions=0 pbc=6 pbcRelay=6 pbcPaid=0 pbcPunt=0 pbcCoverPunt=0 pb=7 pbRelay=3 pbPaid=4 pbPunt=0 pbCoverPunt=0 pmv=6 pmvRelay=4 pmvPaid=1 pmvPunt=0 pmvCoverPunt=1 valF=11 valFRelay=2 valFPaid=0 valFPunt=9 contentPaid=6 contentPunt=13 contentCoverPunt=4 contentLemma=0 contentOpen=2 contentPos=17 entryPaid=6 entryPunt=13 entryCoverPunt=4 entryLemma=0 entryOpen=2 entryPos=17 eight=8 eightPB=4 eightPBC=4 eightIndents=0 eightTop=4 eightFloor=0 eightMinCI=0 eightNic=8 eightPrep=8 eightCover=8 doorUses=49 doorKept=18 doorForgotten=8 doorDropped=23 doorsOther=5 nodes=123715"

/-! ## §6 The reading -/

set_option maxHeartbeats 20000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- §1 the positions
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cd : Cand := {}
  let mut posLines : Array String := #[]
  for c in iv.ctors do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut fields : Array (Nat × Name × List Step) := #[]
    let mut names : Array Name := #[]
    while true do
      match ty with
      | .forallE n t b _ =>
        if i ≥ cv.numParams then
          names := names.push n
          if let some p := coverPath t then fields := fields.push (i, n, p)
        ty := b; i := i + 1
      | _ => break
    cd := { cd with ctorFieldNames := cd.ctorFieldNames.insert c names, ctorNames := cd.ctorNames.push c, consts := cd.consts.insert c }
    if !fields.isEmpty then
      cd := { cd with ctorFields := cd.ctorFields.insert c fields }
      posLines := posLines.push s!"  {short c}: {String.intercalate "," (fields.map fun (_, n, p) => s!"{n}[{renderPath p}]").toList}"
  cd := { cd with consts := cd.consts.insert ``PendingNode.casesOn }
  -- the pack types whose fields carry the cover (the park itself excepted:
  -- its fields are read at doors)
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML || n == ``PendingNode then continue
    match ci with
    | .inductInfo ivv =>
      if ivv.ctors.any (fun c => match env.find? c with | some cc => hasCov cc.type | none => false) then
        cd := { cd with coverTypes := cd.coverTypes.insert n }
    | .defnInfo dv =>
      -- a `Prop`-valued definition packing the cover (the key packs)
      if (piConcl dv.type).isSort && hasCov dv.value then
        cd := { cd with coverTypes := cd.coverTypes.insert n }
    | _ => pure ()
  let coverMod := `L4YAML.Proofs.Scanner.IndentStackCover
  -- every L4YAML theorem with a cover-carrying parameter
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    match ci with
    | .thmInfo _ =>
      thms := thms.push n
      let mut ty := ci.type
      let mut i := 0
      let mut ps : Array (Nat × Name × List Step) := #[]
      let mut names : Array (Name × Bool) := #[]
      while true do
        match ty with
        | .forallE pn t b _ =>
          let cp := if hasCov t then coverPath t else none
          names := names.push (pn, cp.isSome)
          if let some p := cp then ps := ps.push (i, pn, p)
          ty := b; i := i + 1
        | _ => break
      cd := { cd with paramNames := cd.paramNames.insert n names }
      -- a transport — the cover algebra's own theorems, whose conclusion
      -- carries the cover they take — is a step a payment passes through, not
      -- a position it is paid at
      let inCoverMod := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod
      -- item 259: a cover TYPE (`CoverStep`) concluded in the cover module is a
      -- transport too — the step across a `?`/`:` dispatch concludes it
      let transport := (piConcl ci.type).isAppOf coveredN || (inCoverMod && hasCovT cd.coverTypes (piConcl ci.type))
      if !ps.isEmpty && !transport then
        cd := { cd with lemParams := cd.lemParams.insert n ps, consts := cd.consts.insert n }
        posLines := posLines.push s!"  {short n}: {String.intercalate "," (ps.map fun (_, pn, p) => s!"{pn}[{renderPath p}]").toList}"
    | _ => pure ()
  posLines := posLines.qsort (· < ·)
  -- the eight's feeds
  for (l, p) in [(``indicator_open_map, `h_stream_land), (``colon_open_map_explicit, `h_stream_mid),
      (``block_dispatch_deferred_stamp_offcol, `h_stream), (``block_dispatch_deferred_stamp_nopack, `h_stream)] do
    let some ci := env.find? l | throwError "{l}: missing"
    let some idx := ci.type.getForallBinderNames.toArray.findIdx? (· == p) | throwError "{l}.{p}: missing"
    cd := { cd with funnels := cd.funnels.insert l (idx, p), consts := cd.consts.insert l }
  cd := { cd with parks := ({} : Std.HashSet Name).insert ``accum_block_on_pendingBlock |>.insert ``accum_block_on_pendingBlockContent }
  -- §2 the walk
  let st ← IO.mkRef ({} : S)
  let thmsS := sorted thms
  let mut walked : Array Name := #[]
  for n in thmsS do
    if (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod then continue
    let before := (← st.get).rows.size + (← st.get).eight.size + (← st.get).doorUses.size
    walkTheorem st cd n
    let after := (← st.get).rows.size + (← st.get).eight.size + (← st.get).doorUses.size
    if after > before then walked := walked.push n
  let w ← st.get
  let rowLines := w.rows.map fun r => s!"  {short r.lem} #{r.occ} {r.target} := {r.cls.render}"
  -- §3 the trees
  let roots := [("content", "param:accum_block_on_pendingBlockContent.h_closeF_old"), ("entry", "ctor:pendingBlock.h_closeF"),
    ("valF", "param:accum_block_on_closeThenBlock.h_valF"), ("mapValue", "ctor:pendingMapValue.h_closeF")]
  let mut rets : Std.HashMap String (Array String) := {}
  for (l, ps) in cd.lemParams.toList do
    rets := rets.insert s!"ret:{short l}" (ps.map fun (_, pn, _) => posLabel "param" l pn)
  let mut treeLines : Array String := #[]
  let mut treeText : Array String := #[]
  for (nm, root) in roots do
    let t := resolve rets w.rows root 0 {}
    treeText := treeText ++ #[s!"--- {nm}"] ++ t.lines
    let rows := (t.visited.toList.map fun p => (rowsAt w.rows p).size).foldl (· + ·) 0
    treeLines := treeLines.push s!"  {nm}: positions={t.visited.size} rows={rows} leaves[{census t.leaves}] open={t.opens.size}"
  -- §4 the eight
  let eightLines := w.eight.map fun r => s!"  {short r.lem} {r.feeds} {r.facts}"
  -- §5 the doors
  let dropped := (distinctS w.doorBound).filter fun b => !w.doorUsed.contains b
  let doorAll := (distinctS ((w.doorUses.map fun d => s!"  {short d.lem}: {d.door} → {d.callee} {if d.cover then "kept" else "forgotten"}") ++ dropped.map fun b => s!"  {b} dropped")).qsort (· < ·)
  -- the accumulation doors; the park's own methods read a field or two each
  let doorLines := doorAll.filter fun l => l.trimAscii.toString.startsWith "accum_"
  let doorsOther := (w.doors.filter fun d => !(short d).startsWith "accum_").size
  -- the counts
  let ctorRows := w.rows.filter (·.kind == "ctor")
  let lemRows := w.rows.filter (·.kind == "lemma")
  let locRows := w.rows.filter (·.kind == "local")
  let fnRows := w.rows.filter (·.kind == "fn")
  let fnpRows := w.rows.filter (·.kind == "fnp")
  let valRows := w.rows.filter (·.kind == "val")
  let doorDropped := (doorLines.filter (·.endsWith "dropped")).size
  let at_ (pos : String) := rowsAt w.rows pos
  let leafOf (rs : Array Row) (l : String) := (rs.filter fun r => r.cls.leaves.contains l).size
  let relayOf (rs : Array Row) := (rs.filter fun r => !r.cls.sources.isEmpty).size
  let puntOf (rs : Array Row) := (rs.filter (·.cls.isPunt)).size
  let pbc := at_ "ctor:pendingBlockContent.h_closeF"
  let pb := at_ "ctor:pendingBlock.h_closeF"
  let pmv := at_ "ctor:pendingMapValue.h_closeF"
  let valF := at_ "param:accum_block_on_closeThenBlock.h_valF"
  let contentT := resolve rets w.rows "param:accum_block_on_pendingBlockContent.h_closeF_old" 0 {}
  let entryT := resolve rets w.rows "ctor:pendingBlock.h_closeF" 0 {}
  let cnt (xs : Array String) (l : String) := (xs.filter (· == l)).size
  let eightPB := (w.eight.filter (·.lem == ``accum_block_on_pendingBlock)).size
  let eightPBC := (w.eight.filter (·.lem == ``accum_block_on_pendingBlockContent)).size
  let factN (facts k : String) : Nat :=
    match (facts.splitOn (k ++ "="))[1]? with
    | some rest => (String.ofList (rest.toList.takeWhile Char.isDigit)).toNat!
    | none => 0
  let factCount (k : String) := (w.eight.filter fun r => factN r.facts k > 0).size
  let contentLemma := cnt contentT.leaves "paid:lemma"
  let entryLemma := cnt entryT.leaves "paid:lemma"
  let contentCoverPunt := cnt contentT.leaves "cover-punt"
  let entryCoverPunt := cnt entryT.leaves "cover-punt"
  let pbcCoverPunt := leafOf pbc "cover-punt"
  let pbCoverPunt := leafOf pb "cover-punt"
  let pmvCoverPunt := leafOf pmv "cover-punt"
  let doorKept := (doorLines.filter (·.endsWith "kept")).size
  let doorForgotten := (doorLines.filter (·.endsWith "forgotten")).size
  let got := s!"positions={posLines.size} ctorFields={cd.ctorFields.fold (fun a _ v => a + v.size) 0} lemParams={cd.lemParams.fold (fun a _ v => a + v.size) 0} lemmas={cd.lemParams.size} \
walked={walked.size} doors={w.doors.size} rows={w.rows.size} ctorRows={ctorRows.size} lemRows={lemRows.size} localRows={locRows.size} fnRows={fnRows.size} fnpRows={fnpRows.size} valRows={valRows.size} coverTypes={cd.coverTypes.size} mentions={w.mentions} \
pbc={pbc.size} pbcRelay={relayOf pbc} pbcPaid={leafOf pbc "paid"} pbcPunt={puntOf pbc} pbcCoverPunt={pbcCoverPunt} \
pb={pb.size} pbRelay={relayOf pb} pbPaid={leafOf pb "paid"} pbPunt={puntOf pb} pbCoverPunt={pbCoverPunt} \
pmv={pmv.size} pmvRelay={relayOf pmv} pmvPaid={leafOf pmv "paid"} pmvPunt={puntOf pmv} pmvCoverPunt={pmvCoverPunt} \
valF={valF.size} valFRelay={relayOf valF} valFPaid={leafOf valF "paid"} valFPunt={puntOf valF} \
contentPaid={cnt contentT.leaves "paid"} contentPunt={cnt contentT.leaves "punt"} contentCoverPunt={contentCoverPunt} contentLemma={contentLemma} contentOpen={contentT.opens.size} contentPos={contentT.visited.size} \
entryPaid={cnt entryT.leaves "paid"} entryPunt={cnt entryT.leaves "punt"} entryCoverPunt={entryCoverPunt} entryLemma={entryLemma} entryOpen={entryT.opens.size} entryPos={entryT.visited.size} \
eight={w.eight.size} eightPB={eightPB} eightPBC={eightPBC} eightIndents={factCount "indents"} eightTop={factCount "top"} eightFloor={factCount "floor"} eightMinCI={factCount "minCI"} eightNic={factCount "nic"} eightPrep={factCount "prep"} eightCover={factCount "cover"} \
doorUses={doorLines.size} doorKept={doorKept} doorForgotten={doorForgotten} doorDropped={doorDropped} doorsOther={doorsOther} nodes={w.nodes}"
  logInfo s!"CloseStackCover {got}"
  logInfo s!"positions:\n{String.intercalate "\n" posLines.toList}"
  logInfo s!"walked: {String.intercalate ", " (walked.map short).toList}"
  logInfo s!"rows:\n{String.intercalate "\n" rowLines.toList}"
  logInfo s!"trees:\n{String.intercalate "\n" treeLines.toList}"
  logInfo s!"treetext:\n{String.intercalate "\n" treeText.toList}"
  logInfo s!"eight:\n{String.intercalate "\n" eightLines.toList}"
  logInfo s!"door:\n{String.intercalate "\n" doorLines.toList}"
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  unless w.eight.size == 8 do throwError "item 252's eight moved under this pass: eight={w.eight.size}"
  check "expectedRows" rowLines expectedRows
  check "expectedTrees" treeLines expectedTrees
  check "expectedEight" eightLines expectedEight
  check "expectedDoor" doorLines expectedDoor
  unless got == expectedLine do
    throwError "CloseStackCover moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.CloseStackCover
