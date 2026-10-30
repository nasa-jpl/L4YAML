/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.CloseLandingWidth

/-!
# How many of the eight closes that hold both numbers can split on them from what they hold (DOCS item 252)

Item 251 found the landing's width and the park's index in hand at eight
closes on comments — the four of `accum_block_on_pendingBlock`'s `:`/`?` arm
and the four of `accum_block_on_pendingBlockContent`'s — and a comparison of
the two beside none of them.  The honest close is a split: at `n < k` the
awaited entry takes the mapping the landing opens as its node (item 250's
twin), at `k ≤ n` the entry closes empty and what follows resumes a frame the
park carries at `k` or is refused.  This module asks, at each of the eight,
what a split would be made of and what stands in its place.

**§1** re-derives the eight from item 251's walk (a comments spend with the
width and a direct index), the other five comments spends beside them as the
control.  **§2** reads, at each spend with the real local context: the FRAME
hypotheses by face (the entry-level closure, the value-line pack and its
chain, the resume stacks at both bottoms, the enclosing sequence's tail, the
stack top) and how many options deep `IndentStackCover.Covered` stands; the
DECISIONS the spend stands under and those in the sibling arguments of the
application it feeds, each classified by what it decides — the landing's `k`
against the park's `n`, a membership of `k`, `k` against another index, a
frame option, a column, a character — and what each branch does with a
closure (spends the entry closure empty or on a node, hands the comments
closure on, punts); and for the spends that feed `indicator_open_map`, that
lemma's optional arguments by name — paid, punted, or decided.  **§3** lists
every decision on `k` in the two lemmas, wherever it stands, so the `-` arm's
own split is read beside the `:`/`?` arm's.  **§4** reads the door: which of
the park's constructor fields `accum_block_pending` binds and never hands to
the lemma.  A decision counts for what its branches do, never for existing:
a case label over a punt is the unconditional close with a name on it.
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
set_option autoImplicit false

namespace Tests.Guards.CloseSplitFrames

/-! ## §0 Rows -/

def squeeze : List Char → Bool → List Char
  | [], _ => []
  | c :: cs, afterSpace =>
    let c := if c == '\n' || c == '\t' then ' ' else c
    if c == ' ' then (if afterSpace then squeeze cs true else ' ' :: squeeze cs true)
    else c :: squeeze cs false

def collapse (s : String) (n : Nat) : String :=
  let one := String.ofList (squeeze s.toList true)
  if one.length ≤ n then one else String.ofList (one.toList.take n) ++ "…"

structure Decision where
  id : Nat
  lem : Name
  kind : String
  cls : String
  cond : String
  /-- the innermost library application containing it, and the argument -/
  app : Option (Nat × Nat)
  nBranches : Nat
  deriving Inhabited

structure SpendRow where
  lem : Name
  kind : String
  closure : String
  cls : String
  landing : String
  width : String
  index : String
  cmp : String
  feeds : String
  app : Option (Nat × Nat)
  frames : String
  cover : String
  floorB : String
  above : Array Nat
  deriving Inhabited

structure AppRow where
  id : Nat
  lem : Name
  callee : Name
  names : Array Name
  heads : Array String
  optArgs : Array Nat
  deriving Inhabited

structure S where
  spends : Array SpendRow := #[]
  decisions : Array Decision := #[]
  apps : Array AppRow := #[]
  /-- (decision, branch, tag) -/
  uses : Array (Nat × Nat × String) := #[]
  nextD : Nat := 0
  nextA : Nat := 0
  nodes : Nat := 0
  optCache : Std.HashMap Name (Array Nat) := {}

structure Ctx where
  lem : Name
  subject : FVarId
  tc : Tracked
  tp : Std.HashSet FVarId
  /-- every tracked variable, closures and packages, for one-pass membership -/
  all : Std.HashSet FVarId
  above : Array (Nat × Nat)
  app : Option (Nat × Nat)
  cand : Bool

def Ctx.retrack (cx : Ctx) (tc : Tracked) (tp : Std.HashSet FVarId) : Ctx :=
  { cx with tc, tp, all := tc.fold (fun s k _ => s.insert k) tp }

/-! ## §1 Reading the context -/

def isOptTrue (t : Expr) : Bool :=
  let t := t.consumeMData
  t.isAppOfArity ``Or 2 && ((t.getArg! 1).consumeMData.isConstOf ``True || (t.getArg! 1).consumeMData.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt || (t.getArg! 1).consumeMData.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG)  -- item 311: or the named alternative

/-- The depth, in `∨ True` options, of the first subterm satisfying `p`. -/
partial def depthTo (t : Expr) (p : Expr → Bool) (d : Nat := 0) : Option Nat :=
  let t := t.consumeMData
  if p t then some d else
  let d' := if isOptTrue t then d + 1 else d
  match t with
  | .app .. => (t.getAppFn :: t.getAppArgs.toList).findSome? fun a => depthTo a p d'
  | .lam _ ty b _ => (depthTo ty p d').orElse fun _ => depthTo b p d'
  | .forallE _ ty b _ => (depthTo ty p d').orElse fun _ => depthTo b p d'
  | .letE _ ty v b _ => (depthTo ty p d').orElse fun _ => (depthTo v p d').orElse fun _ => depthTo b p d'
  | .proj _ _ b => depthTo b p d'
  | _ => none

def hasHead (t : Expr) (n : Name) : Bool := (t.find? (·.isAppOf n)).isSome

/-- The face of a hypothesis: which frame it carries, with its flags. -/
def faceOf (t : Expr) : Option String :=
  let t := t.consumeMData
  let optD := (depthTo t fun e => !isOptTrue e && !(e.isAppOfArity ``Or 2)).getD 0
  let flags := (if optD ≥ 2 then #[s!"opt{optD}"] else if optD == 1 then #["opt"] else #[])
  let coverFlag := match depthTo t (·.isAppOf ``L4YAML.Proofs.IndentStackCover.Covered) with
    | some d => #[s!"cover@{d}"] | none => #[]
  let floorFlag := match depthTo t (·.isAppOf ``L4YAML.Proofs.IndentStackCover.Floor) with
    | some d => #[s!"floor@{d}"] | none => #[]
  -- Item 304: the value-line stacks are `KeyFrames` (item 302's); the face is the same.
  let isStack (t : Expr) : Bool := hasHead t ``ResumeFrames || hasHead t ``KeyFrames
  let wb := if hasHead t ``Membership.mem && hasHead t ``LT.lt && isStack t then #["wb"] else #[]
  let face : Option String :=
    if isStack t then
      match t.find? (fun e => e.isAppOf ``ResumeFrames || e.isAppOf ``KeyFrames) with
      | some r => if (r.getArg! 0).consumeMData.isAppOf ``SLYamlStream then some "closeF"
                  else if (r.getArg! 0).consumeMData.isAppOf ``ExplValueLine then some "closeFV" else some "closeF?"
      | none => none
    else if hasHead t ``SeqEntryTail then some "seqF"
    else if hasHead t ``GLit && hasHead t ``SIndent && hasHead t ``SLYamlStream then
      if hasHead t ``Membership.mem then some "kslotUp" else some "kslot"
    else if hasHead t ``SCompactSeqTail && hasHead t ``SLYamlStream then
      if hasHead t ``SBlockIndented then some "entry(SBI)" else if hasHead t ``SSLComments then some "entry(SSL)" else some "entry(?)"
    else if hasHead t ``L4YAML.Proofs.PreprocessIndentStable.IndentFloor then some "floor"
    else if t.isAppOfArity ``LE.le 4 && (t.getArg! 2).consumeMData.isAppOf ``ScannerState.currentIndent then some "top"
    else if hasHead t ``L4YAML.Proofs.IndentStackMono.Mono then some "mono"
    else if hasHead t ``L4YAML.Proofs.IndentStackBase.SentinelBase then some "base"
    else if hasHead t ``CompletedTail then some "tail"
    else if t.isForall && (t.bindingDomain!.consumeMData.isAppOfArity ``Eq 3 && hasHead t.bindingDomain! ``SurfPos.col)
        && (t.bindingBody!.consumeMData.isAppOfArity ``Eq 3 && hasHead t.bindingBody! ``ScannerState.needIndentCheck) then some "nic0"
    else none
  face.map fun f =>
    let fl := flags ++ wb ++ coverFlag ++ floorFlag
    if fl.isEmpty then f else s!"{f}({String.intercalate "," fl.toList})"

/-- The frames in the local context, as `face:name(flags)`, and the depths of
    the cover and its floor. -/
def framesIn (skip : Std.HashSet FVarId) : MetaM (String × String × String) := do
  let lctx ← getLCtx
  let mut out : Array String := #[]
  let mut cover : Option Nat := none
  let mut floorB : Option Nat := none
  for d in lctx do
    if d.isImplementationDetail || skip.contains d.fvarId then continue
    let t := d.type.consumeMData
    let nm := if d.userName.hasMacroScopes then s!"{d.userName.eraseMacroScopes}✝" else d.userName.toString
    if let some f := faceOf t then out := out.push s!"{f}:{nm}"
    if let some c := depthTo t (·.isAppOf ``L4YAML.Proofs.IndentStackCover.Covered) then
      cover := some (match cover with | some c0 => min c0 c | none => c)
    if let some c := depthTo t (·.isAppOf ``L4YAML.Proofs.IndentStackCover.Floor) then
      floorB := some (match floorB with | some c0 => min c0 c | none => c)
  let render : Option Nat → String := fun | some d => s!"@{d}" | none => "none"
  return (s!"[{String.intercalate "," (out.qsort (· < ·)).toList}]", render cover, render floorB)

/-- The landing's width variables and the park's index variables, read as
    item 251 reads them: the landing is the `SSLComments start _` in context,
    `k` any `SIndent k landing _`'s index, `n` the ties to the park's start. -/
def knSets (start : Expr) : MetaM (Array FVarId × Array FVarId) := do
  let lctx ← getLCtx
  let mut landing : Option Expr := none
  for d in lctx do
    if d.isImplementationDetail then continue
    let t := d.type.consumeMData
    if t.isAppOfArity ``SSLComments 2 && (t.getArg! 0).consumeMData == start then
      landing := some (t.getArg! 1).consumeMData
      break
  let mut kSet : Array FVarId := #[]
  let mut nSet : Array FVarId := #[]
  for d in lctx do
    if d.isImplementationDetail then continue
    let t := d.type.consumeMData
    if let some L := landing then
      if t.isAppOfArity ``SIndent 3 && (t.getArg! 1).consumeMData == L then
        kSet := kSet ++ fvarsOf (t.getArg! 0)
    for (_, ix) in ← tiesIn start t do
      if let .fvar id := stripSucc ix then
        if !nSet.contains id then nSet := nSet.push id
  return (kSet, nSet)

/-- The atoms of a proposition: through `Not`, `Or`, `And`, `Iff`. -/
partial def atoms (t : Expr) : Array Expr :=
  let t := t.consumeMData
  if t.isAppOfArity ``Not 1 then atoms (t.getArg! 0)
  else if t.isAppOfArity ``Or 2 || t.isAppOfArity ``And 2 || t.isAppOfArity ``Iff 2 then
    atoms (t.getArg! 0) ++ atoms (t.getArg! 1)
  else #[t]

/-- What a decision decides. -/
partial def optish (t : Expr) : Bool :=
  let t := t.consumeMData
  isOptTrue t || (t.isAppOfArity ``And 2 && optish (t.getArg! 0) && optish (t.getArg! 1))

def classify (cond : Expr) (kSet nSet : Array FVarId) : String := Id.run do
  let mut cls : Array String := #[]
  if optish cond then cls := cls.push "opt"
  let ats := atoms cond
  let allChar := ats.all fun a => a.isAppOfArity ``Eq 3 && (a.getArg! 0).consumeMData.isConstOf ``Char
  let oneCol := ats.size == 1 && ats[0]!.isAppOfArity ``Eq 3 &&
    ((ats[0]!.getArg! 1).consumeMData.isAppOfArity ``SurfPos.col 1 || (ats[0]!.getArg! 2).consumeMData.isAppOfArity ``SurfPos.col 1)
  if allChar then cls := cls.push "char"
  if oneCol then cls := cls.push "col0"
  for a in atoms cond do
    let rel? : Option (Expr × Expr) :=
      if a.isAppOfArity ``Eq 3 then some (a.getArg! 1, a.getArg! 2)
      else if a.isAppOfArity ``Ne 3 then some (a.getArg! 1, a.getArg! 2)
      else if a.isAppOfArity ``LT.lt 4 || a.isAppOfArity ``LE.le 4 || a.isAppOfArity ``GE.ge 4 || a.isAppOfArity ``GT.gt 4 then
        some (a.getArg! 2, a.getArg! 3)
      else none
    if let some (l, r) := rel? then
      let l := stripCast (stripSucc l)
      let r := stripCast (stripSucc r)
      let lk := touches l kSet
      let rk := touches r kSet
      let ln := touches l nSet
      let rn := touches r nSet
      if (lk && rn) || (ln && rk) then cls := cls.push "kn"
      else if (lk && r.isFVar) || (rk && l.isFVar) then cls := cls.push "knv"
      else if lk || rk then cls := cls.push "k?"
    if a.isAppOfArity ``Membership.mem 5 then
      if touches (a.getArg! 3) kSet || touches (a.getArg! 4) kSet then cls := cls.push "kmem"
    if a.isAppOfArity ``Exists 2 && (touches a kSet) then cls := cls.push "k∃"
  let pri := ["kn", "kmem", "knv", "k?", "k∃", "opt", "col0", "char"]
  for p in pri do if cls.contains p then return p
  return "other"

/-- Whether classifying a condition needs the variable sets: an atom relating
    two terms with a variable, or a membership. -/
def needsSets (cond : Expr) : Bool :=
  (atoms cond).any fun a =>
    a.isAppOfArity ``Membership.mem 5 || a.isAppOfArity ``Exists 2 ||
    ((a.isAppOfArity ``Eq 3 || a.isAppOfArity ``Ne 3 || a.isAppOfArity ``LT.lt 4 || a.isAppOfArity ``LE.le 4 ||
      a.isAppOfArity ``GE.ge 4 || a.isAppOfArity ``GT.gt 4) && a.hasFVar && !(a.getArg! 0).consumeMData.isConstOf ``Char)

/-! ## §2 The walker -/

def nameOf (m : Expr) : MetaM String := do
  match m with
  | .fvar id => return (← id.getDecl).userName.toString
  | _ => return ""

/-- A decision node: its kind, condition, the discriminant's name and its branches (argument indices). -/
def decisionOf (n : Name) (args : Array Expr) : MetaM (Option (String × Expr × String × Array Nat)) := do
  let env ← getEnv
  if (n == ``dite || n == ``ite) && args.size ≥ 5 then
    return some ("dite", args[1]!, "", #[3, 4])
  if n == ``Decidable.byCases && args.size ≥ 5 then
    return some ("byCases", args[0]!, "", #[3, 4])
  if n == ``Or.elim && args.size ≥ 6 then
    let m := args[3]!.consumeMData
    let nm ← nameOf m
    return some ("Or.elim", ← inferType m, nm, #[4, 5])
  if isCasesOnRecursor env n then
    let ind := n.getPrefix
    if let some (.inductInfo iv) := env.find? ind then
      if iv.ctors.length ≥ 2 then
        let majorPos := iv.numParams + 1 + iv.numIndices
        if args.size ≥ majorPos + 1 + iv.ctors.length then
          let m := args[majorPos]!.consumeMData
          let nm ← nameOf m
          let brs := (List.range iv.ctors.length).toArray.map (majorPos + 1 + ·)
          return some (s!"{short2 n}", ← inferType m, nm, brs)
  if let some info ← getMatcherInfo? n then
    let nAlts := info.altInfos.size
    if nAlts ≥ 2 then
      let firstDiscr := info.numParams + 1
      let firstAlt := firstDiscr + info.numDiscrs
      if args.size ≥ firstAlt + nAlts then
        let mut conds : Array Expr := #[]
        let mut nms : Array String := #[]
        for i in [firstDiscr:firstAlt] do
          let m := args[i]!.consumeMData
          conds := conds.push (← inferType m)
          if let .fvar id := m then nms := nms.push (← id.getDecl).userName.toString
        let cond := if conds.size == 1 then conds[0]! else mkAppN (mkConst ``And) #[conds[0]!, conds[1]!]
        let brs := (List.range nAlts).toArray.map (firstAlt + ·)
        return some ("match", cond, String.intercalate "," nms.toList, brs)
  return none

def isPunt (e : Expr) : Bool :=
  let e := e.consumeMData
  e.isAppOfArity ``Or.inr 3 && ((e.getArg! 2).consumeMData.isConstOf ``True.intro || (e.getArg! 2).consumeMData.isConstOf ``trivial)

/-- `peelCasts` that stops at a bare lambda (whose head-beta is itself). -/
partial def peelSafe (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .letE _ _ v b _ => peelSafe (b.instantiate1 v)
  | .app .. =>
    match e.getAppFn with
    | .const n _ =>
      let args := e.getAppArgs
      match transparent n with
      | some (arity, k) => if k < args.size then peelSafe (mkAppN args[k]! (args.extract arity args.size)).headBeta else e
      | none =>
        if n == ``letFun && args.size ≥ 4 then peelSafe (mkAppN (mkApp args[3]! args[2]!) (args.extract 4 args.size)).headBeta
        else e
    | .lam .. => peelSafe e.headBeta
    | _ => e
  | _ => e

def headOf (a : Expr) : MetaM String := do
  let a := peelSafe a
  match a with
  | .fvar _ => return "prem"
  | .lam .. => return "λ"
  | _ =>
    match a.getAppFn with
    | .const n _ =>
      if n == ``Or.inl then return "paid"
      if n == ``Or.inr then return "punt"
      if (← decisionOf n a.getAppArgs).isSome then return "cond"
      if n.getRoot == `L4YAML then return "lemma"
      return s!"other:{short2 n}"
    | _ => return "other"

def tagUse (st : IO.Ref S) (cx : Ctx) (tag : String) : MetaM Unit :=
  for (d, b) in cx.above do
    st.modify fun s => { s with uses := s.uses.push (d, b, tag) }

/-- The class of what an entry-level or frame closure is handed. -/
def entryClass (arg : Expr) : MetaM String := do
  let s ← nodeShape arg 3
  return if s.startsWith "SBlockIndented.empty" || s.startsWith "SBlockNode.emptyNode" then "empty"
    else if s.startsWith "SBlockIndented.node" || s.startsWith "SBlockIndented.compactSeq" || s.startsWith "SBlockIndented.compactMap" then "node"
    else if s == "prem:SSLComments" || s.startsWith "SSLComments." then "comments"
    else if s == "prem:SBlockIndented" || s == "prem:SBlockNode" then "prem"
    else s!"other({s})"

/-- Under its lambdas, an `Or.inr trivial` (a punt) or an `Or.inl` (a paid option). -/
partial def optTag (e : Expr) : Option String :=
  let e := e.consumeMData
  match e with
  | .lam _ _ b _ => optTag b
  | _ => if isPunt e then some "punt" else if e.isAppOfArity ``Or.inl 3 then some "paid" else none

partial def walkS (st : IO.Ref S) (cx : Ctx) (e : Expr) : MetaM Unit := do
  let e := e.consumeMData
  st.modify fun s => { s with nodes := s.nodes + 1 }
  let anyTracked (x : Expr) : Bool := x.hasAnyFVar cx.all.contains
  match e with
  | .lam n t b bi =>
    unless cx.cand || anyTracked e do return
    withLocalDecl n bi t fun x => do
      let (tc, tp) ← if cx.cand then trackBinder x cx.tc cx.tp else pure (cx.tc, cx.tp)
      walkS st (cx.retrack tc tp) (b.instantiate1 x)
  | .forallE n t b bi =>
    unless anyTracked e do return
    withLocalDecl n bi t fun x => walkS st { cx with cand := false } (b.instantiate1 x)
  | .letE n t v b _ =>
    unless anyTracked e do return
    walkS st { cx with cand := false } v
    withLetDecl n t v fun x => do
      let (tc, tp) ← if anyTracked v then trackBinder x cx.tc cx.tp else pure (cx.tc, cx.tp)
      walkS st { cx.retrack tc tp with cand := false } (b.instantiate1 x)
  | .proj _ _ b => walkS st { cx with cand := false } b
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    match f with
    | .fvar id =>
      if let some (ci, start, _) := cx.tc[id]? then
        let isSubject := id == cx.subject
        let name := (← id.getDecl).userName.toString
        if args.size > ci then
          let closeArg := args[ci]!
          let skip : Std.HashSet FVarId := cx.tc.fold (fun s k _ => s.insert k) {}
          if isSubject then
            let landing := landingOf (← inferType closeArg)
            let (landingS, width, index, cmp) ← beside landing start skip #[]
            let arg ← nodeShape closeArg 6
            let (frames, cover, floorB) ← framesIn (({} : Std.HashSet FVarId).insert cx.subject)
            let feeds ← match cx.app with
              | some (aid, i) =>
                let apps := (← st.get).apps
                match apps.find? (·.id == aid) with
                | some a =>
                  let pn := if i < a.names.size then a.names[i]!.toString else "#" ++ toString i
                  pure s!"{short a.callee}.{pn}"
                | none => pure "?"
              | none => pure "tuple"
            let row : SpendRow :=
              { lem := cx.lem, kind := "spend", closure := name, cls := classOf arg, landing := landingS,
                width := width, index := index, cmp := cmp, feeds := feeds, app := cx.app, frames := frames, cover := cover,
                floorB := floorB, above := cx.above.map (·.1) }
            st.modify fun s => { s with spends := s.spends.push row }
            tagUse st cx "P:spend"
          else
            tagUse st cx s!"E:{← entryClass closeArg}"
        else
          tagUse st cx (if isSubject then "P:hand" else "E:pass")
      for a in args do walkS st { cx with cand := false } a
    | .lam .. => walkS st cx e.headBeta
    | .const n us =>
      if let some (arity, k) := transparent n then
        if k < args.size then
          return ← walkS st cx (mkAppN args[k]! (args.extract arity args.size)).headBeta
      if n == ``letFun && args.size ≥ 4 then
        let v := args[2]!
        walkS st { cx with cand := false } v
        match args[3]! with
        | .lam bn bt bb _ =>
          withLetDecl bn bt v fun x => do
            let (tc, tp) ← if anyTracked v then trackBinder x cx.tc cx.tp else pure (cx.tc, cx.tp)
            walkS st { cx.retrack tc tp with cand := false } (bb.instantiate1 x)
        | g => walkS st { cx with cand := false } g
        for a in args.extract 4 args.size do walkS st { cx with cand := false } a
        return
      -- a decision: recorded whether or not a closure is mentioned inside,
      -- entered only when one is
      if let some (kind, cond, nm, brs) ← decisionOf n args then
        let mentions := cx.cand || anyTracked e
        let cls ← if needsSets cond then do
            let (kSet, nSet) ← knSets ((cx.tc[cx.subject]?.map (·.2.1)).getD (mkConst ``True))
            pure (classify cond kSet nSet)
          else pure (classify cond #[] #[])
        let condP := collapse (toString (← ppExpr cond)) 72
        let condS := if nm.isEmpty then condP else s!"{nm}:{condP}"
        let id := (← st.get).nextD
        let dec : Decision := { id := id, lem := cx.lem, kind := kind, cls := cls, cond := condS, app := cx.app, nBranches := brs.size }
        st.modify fun s => { s with nextD := s.nextD + 1, decisions := s.decisions.push dec }
        let _ := mentions
        let destr := args.any fun a => match a.consumeMData with | .fvar id => cx.tp.contains id | _ => false
        for i in [0:args.size] do
          match brs.findIdx? (· == i) with
          | some bi =>
            -- the branch's own value: a paid option or a punt
            if let some t := optTag args[i]! then
              st.modify fun s => { s with uses := s.uses.push (id, bi, t) }
            walkS st { cx with above := cx.above.push (id, bi), cand := destr } args[i]!
          | none => walkS st { cx with cand := false } args[i]!
        return
      unless cx.cand || anyTracked e do return
      let env ← getEnv
      match env.find? n with
      | some (.thmInfo ti) =>
        if n.getRoot == `L4YAML then
          -- a library application: its arguments are the sibling positions
          let names := ti.type.getForallBinderNames.toArray
          let mut heads : Array String := #[]
          for a in args do heads := heads.push (← headOf a)
          let optArgs ← match (← st.get).optCache[n]? with
            | some o => pure o
            | none => do
              let o ← forallTelescope ti.type fun xs _ => do
                let mut o : Array Nat := #[]
                for i in [0:xs.size] do
                  if isOptTrue (← inferType xs[i]!) then o := o.push i
                return o
              st.modify fun s => { s with optCache := s.optCache.insert n o }
              pure o
          let aid := (← st.get).nextA
          let arow : AppRow := { id := aid, lem := cx.lem, callee := n, names := names, heads := heads, optArgs := optArgs }
          st.modify fun s => { s with nextA := s.nextA + 1, apps := s.apps.push arow }
          for i in [0:args.size] do
            if let some id := partialUse (stopAt env) cx.tc args[i]! then
              tagUse st cx (if id == cx.subject then "P:hand" else "E:pass")
              if id == cx.subject then
                let (_, start, _) := cx.tc[id]?.get!
                let skip : Std.HashSet FVarId := cx.tc.fold (fun s k _ => s.insert k) {}
                let (landingS, width, index, cmp) ← beside none start skip #[]
                let (frames, cover, floorB) ← framesIn (({} : Std.HashSet FVarId).insert cx.subject)
                let pname := if i < names.size then names[i]!.toString else s!"#{i}"
                let hname := (← id.getDecl).userName.toString
                let row : SpendRow :=
                  { lem := cx.lem, kind := "hand", closure := hname, cls := "—", landing := landingS,
                    width := width, index := index, cmp := cmp, feeds := s!"{short n}.{pname}", app := some (aid, i), frames := frames,
                    cover := cover, floorB := floorB, above := cx.above.map (·.1) }
                st.modify fun s => { s with spends := s.spends.push row }
            walkS st { cx with app := some (aid, i), cand := false } args[i]!
          return
      | some (.ctorInfo _) =>
        for i in [0:args.size] do
          if let some id := partialUse (stopAt env) cx.tc args[i]! then
            tagUse st cx (if id == cx.subject then "P:carry" else "E:carry")
      | _ => pure ()
      let destr := args.any fun a => match a.consumeMData with | .fvar id => cx.tp.contains id | _ => false
      for a in args do walkS st { cx with cand := destr } a
      let _ := us
    | _ =>
      walkS st { cx with cand := false } f
      for a in args do walkS st { cx with cand := false } a
  | _ => return

/-- Follow one lemma's parameter. -/
def followS (st : IO.Ref S) (c : Name) (pname : Name) : MetaM Unit := do
  let some ci := (← getEnv).find? c | throwError "{c}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{c}: no value"
  lambdaTelescope v fun xs body => do
    let mut x? : Option Expr := none
    let mut tc : Tracked := {}
    let mut tp : Std.HashSet FVarId := {}
    for x in xs do
      let isSubject := (← x.fvarId!.getDecl).userName == pname
      if isSubject then x? := some x
      -- tracked: the subject, the entry-level closures beside it and the
      -- frame packages — what a split would be made of
      let face := faceOf (← inferType x)
      let isFrame := match face with
        | some f => f.startsWith "entry" || f.startsWith "kslot" || f.startsWith "closeF" || f.startsWith "seqF"
        | none => false
      if isSubject || isFrame then
        let (tc', tp') ← trackBinder x tc tp
        tc := tc'; tp := tp'
    let some x := x? | throwError "{c}: no parameter {pname} among its lambdas"
    unless tc.contains x.fvarId! do throwError "{c}.{pname}: not a closure"
    let all : Std.HashSet FVarId := tc.fold (fun s k _ => s.insert k) tp
    walkS st { lem := c, subject := x.fvarId!, tc, tp, all, above := #[], app := none, cand := false } body

/-! ## §3 The door -/

/-- Casts peeled and redexes reduced everywhere: `cases` reintroduces every
    field of the constructor through a cast and a lambda, so an unused field
    still occurs once before this pass and not at all after it. -/
partial def normCasts (e : Expr) : Expr :=
  let e := e.consumeMData
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    let peeled? : Option Expr := match f with
      | .const n _ =>
        match transparent n with
        | some (arity, k) => if k < args.size then some (mkAppN args[k]! (args.extract arity args.size)).headBeta else none
        | none => none
      | _ => none
    match peeled? with
    | some e' => normCasts e'
    | none => (mkAppN (normCasts f) (args.map normCasts)).headBeta
  | .lam n t b bi => .lam n (normCasts t) (normCasts b) bi
  | .forallE n t b bi => .forallE n (normCasts t) (normCasts b) bi
  | .letE n t v b nd => .letE n (normCasts t) (normCasts v) (normCasts b) nd
  | .proj s i b => .proj s i (normCasts b)
  | _ => e

/-- The fields of a park constructor that a `cases` alternative binds and never uses. -/
def doorOf (lem : Name) (parks : List Name) : MetaM (Array String) := do
  let env ← getEnv
  let some ci := env.find? lem | throwError "{lem}: missing"
  let some v := ci.value? (allowOpaque := true) | throwError "{lem}: no value"
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let found ← IO.mkRef (#[] : Array Expr)
  v.forEach' fun e => do
    if e.isAppOf ``PendingNode.casesOn then
      let args := e.getAppArgs
      if args.size ≥ iv.numParams + 1 + iv.numIndices + 1 + iv.ctors.length then found.modify (·.push e)
    return true
  let apps ← found.get
  unless apps.size ≥ 1 do throwError "{lem}: no PendingNode.casesOn"
  let e := apps[0]!
  let args := e.getAppArgs
  let majorPos := iv.numParams + 1 + iv.numIndices
  let mut out : Array String := #[]
  for park in parks do
    let some idx := iv.ctors.findIdx? (· == park) | throwError "{park}: not a constructor"
    let some (.ctorInfo cv) := env.find? park | throwError "{park}: not a constructor"
    let fieldNames := cv.type.getForallBinderNames.toArray.extract cv.numParams (cv.numParams + cv.numFields)
    let minor := args[majorPos + 1 + idx]!
    -- `cases` binds the fields, then one equation per index (whose TYPES mention
    -- the constructor applied to every field), then the alternative's body: a
    -- field is used iff it occurs in that body
    -- the data fields (positions, the index) are unified away by the equations;
    -- the faces are the park's obligations, and those are what a door can drop
    let row ← lambdaTelescope (normCasts minor) fun fs body => do
      let mut data := 0
      let mut used : Array String := #[]
      let mut dropped : Array String := #[]
      for i in [0:min fs.size cv.numFields] do
        if !(← isProp (← inferType fs[i]!)) then
          data := data + 1
          continue
        let fname := if i < fieldNames.size then fieldNames[i]!.toString else s!"#{i}"
        let bn := (← fs[i]!.fvarId!.getDecl).userName
        let bname := if bn.hasMacroScopes then s!"{bn.eraseMacroScopes}✝" else bn.toString
        if body.containsFVar fs[i]!.fvarId! then used := used.push fname
        else dropped := dropped.push s!"{fname}({bname})"
      return s!"{short2 park}: fields={cv.numFields} data={data} faces={cv.numFields - data} equations={fs.size - cv.numFields} used={used.size} dropped={dropped.size} {String.intercalate "," dropped.toList}"
    out := out.push row
  return out

/-! ## §4 The pins -/

-- Item 305: the eight rows that read `h_closeFV_old` flag it `wb` — the field carries the width
-- bound `∀ k' ∈ ks, k' < n` (two rows also print the type's new first conjunct).
-- 2026-10-21 (item 319): two rows re-read — `accum_block_on_pendingBlockContent #6` and `accum_block_on_pendingBlock #10`:
-- the `h_closeFV_old` outer-alternative bullets read `—` where they read `punt` (`rcases … | h_alt` hands the park's
-- alternative on at the park's own state, `Or.inr h_alt`, instead of closing with `trivial`).
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-25 (item 358): the cover conjunct on `h_closeFV_old` (×3) and `closeThenBlock.h_mapFV` reads as
-- `closeFV(opt,wb)` / `closeFV(opt)` frames in every spend; the three K1 arms add a `kmem` branch (`→—|punt`).
-- 2026-10-26 (item 369): `accum_block_on_pendingBlock`'s spends list `closeF:h_closeF_old` among their frames
-- (`pendingBlock.h_closeF` threaded for the `:`/`?` landing's `h_res_land`); the per-lemma `#N` numbering shifts with it.
-- 2026-10-29 (item 389): the `-` park's `#3 BOTH` spend reads its k = n arm's new split — `kn(n < k)→paid` beside item 387's `atSequenceIndent` split, whose mapping-top half now reads the park's conjunct `h_mt` (paid) and whose sequence-top half stays punt.
-- 2026-10-30 (item 405): `accum_block_on_pendingBlock`'s spend reads the `?`-park field's head-form chain (`h_kslot` now `∃ nv0 ns, …`).
-- 2026-10-30 (item 405, Rule 8 fix): the same three rows re-read with the field re-indexed by the projection `markedCols sc` — the `opt(h_kslot:…)` frame now prints `∀ (nv : Nat), nv ∈ …` (no `∃ nv0 ns`), and the off-column decision destructures no chain (the `h✝` binders leave).
def expectedSpends : List String :=
  [
  "keyctx_of_preprocess #1 width feeds=tuple frames=[] cover=none floor=none above=[other(s_prep.simpleKey.possible = true ∧ s_pre…),other((∃ k, SIndent k sp_mid sp_ws) ∨ ∃ sa sb,…),other(h_disj:SSLComments sp_g sp_mid ∧ sp_mid.…)] beside=[]",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_block_on_closeThenBlock #2 width feeds=tuple frames=[base:h_base,closeF(opt):h_mapF,closeF(opt):h_vpack,closeF(opt,wb,cover@2,floor@2):h_valF,closeF:h_vslot,closeFV(opt):h_valFV,closeFV(opt,cover@2,floor@2):h_mapFV,mono:h_mono,nic0:h_nic0,seqF(opt):h_seqF,tail(opt):h_tail139] cover=@2 floor=@2 above=[other(h_land:SSLComments sp_gram sp_mid ∧ sp_m…)] beside=[]",
   -- item 385: the no-pop leaf (`s_prep.indents = sc.indents`) passes the park's `closeF` frames
   -- into `deeperLandingResumeSeq` instead of declining (`E:pass`)
   -- 2026-10-29 (item 387): `#3` gains `kn(n < k)→paid,E:pass|—` before `col0` — the no-pop arm's
   -- strict split: `n < k` is the helper (paid), `k = n` splits on the sequence top (refuted / mapping sibling declined).
   "accum_block_on_pendingBlock #3 BOTH feeds=indicator_open_map.h_stream_land frames=[base:h_base,closeF(opt):h_kslot,closeF(opt):h_kslotUp,closeF(opt,wb,cover@2,floor@2):h_closeF_old,closeFV(opt,wb,cover@2,floor@2):h_closeFV_old,entry(SBI):h_close_entry_old,mono:h_mono,seqF(opt):h_seqF_old,top:h_top_old] cover=@2 floor=@2 above=[other(h_land:SSLComments sp_scan sp_mid ∧ sp_m…),other((∃ k, SIndent k sp_mid sp_sc) ∨ ∃ sa sb,…),char(c = '-'),char(c = ':' ∨ c = '?')] beside=[opt(h_closeF_old:(∃ ks, (∀ (fr : Proofs.Inde…)→E:empty×2,E:pass×2|punt,kmem(Proofs.IndentStackCover.FrameLevel.map k…)→E:empty|E:pass×2,E:empty,other(s_prep.indents = sc.indents ∨ ¬s_prep.in…)→E:pass×2,E:empty|—,kn(n < k)→paid,E:pass|E:pass,E:empty,other(atSequenceIndent s_prep = true ∧ (c = ':…)→—|E:pass,E:empty,other(atSequenceIndent s_prep = false)→E:pass,E:empty|punt,opt(h_mt:((∃ e, sc.indents.back? = some e ∧ …)→E:pass,E:empty|—,col0(sp_scan.col = 0)→punt|paid,kn(n + 1 ≤ k)→E:pass×5|punt,opt(h_kslot,h_kslotUp:((∀ (nv : Nat), nv ∈ P…)→paid,E:pass×3|paid,E:pass|paid,E:pass|—,opt(h_closeFV_old:(∃ nv ks, (∀ (fr : Proofs.…)→E:empty|—,kmem(Proofs.IndentStackCover.FrameLevel.map k…)→—|—,kn(n + 1 ≤ k)→E:pass×4|punt,opt(h_kslot,h_kslotUp:((∀ (nv : Nat), nv ∈ P…)→paid,E:pass×3|paid,E:pass|punt]",
   "accum_block_on_pendingBlock #4 BOTH feeds=colon_open_map_explicit.h_stream_mid frames=[base:h_base,closeF(opt):h_kslot,closeF(opt):h_kslotUp,closeF(opt,wb,cover@2,floor@2):h_closeF_old,closeF:kslot,closeFV(opt,wb,cover@2,floor@2):h_closeFV_old,entry(SBI):h_close_entry_old,mono:h_mono,seqF(opt):h_seqF_old,top:h_top_old] cover=@2 floor=@2 above=[other(h_land:SSLComments sp_scan sp_mid ∧ sp_m…),other((∃ k, SIndent k sp_mid sp_sc) ∨ ∃ sa sb,…),char(c = '-'),char(c = ':' ∨ c = '?'),char(c = ':')] beside=[opt(h_kslotUp:(∃ ns, Proofs.RegisterWitness.…)→—|punt,other(∀ (x : Nat), x ∈ ns → x = k)→paid|punt]",
   "accum_block_on_pendingBlock #5 BOTH feeds=block_dispatch_deferred_stamp_offcol.h_stream frames=[base:h_base,closeF(opt):h_kslot,closeF(opt):h_kslotUp,closeF(opt,wb,cover@2,floor@2):h_closeF_old,closeF:h_explicit,closeF:h_upSpend,closeF:kslot,closeFV(opt,wb,cover@2,floor@2):h_closeFV_old,entry(SBI):h_close_entry_old,mono:h_mono,seqF(opt):h_seqF_old,top:h_top_old] cover=@2 floor=@2 above=[other(h_land:SSLComments sp_scan sp_mid ∧ sp_m…),other((∃ k, SIndent k sp_mid sp_sc) ∨ ∃ sa sb,…),char(c = '-'),char(c = ':' ∨ c = '?'),char(c = ':'),other((if s_prep.allowDirectives = true then {…),opt(h_kslot:(∀ (nv : Nat), nv ∈ Proofs.Regis…),kmem(k ∈ Proofs.RegisterWitness.markedCols sc),k∃(h_upSpend:(∀ (sp_m : SurfPos), SBlockInd…)] beside=[other(s_prep.allowDirectives = true)→—|—]",
   "accum_block_on_pendingBlock #6 BOTH feeds=block_dispatch_deferred_stamp_nopack.h_stream frames=[base:h_base,closeF(opt):h_kslot,closeF(opt):h_kslotUp,closeF(opt,wb,cover@2,floor@2):h_closeF_old,closeF:h_explicit,closeF:h_upSpend,closeFV(opt,wb,cover@2,floor@2):h_closeFV_old,entry(SBI):h_close_entry_old,mono:h_mono,seqF(opt):h_seqF_old,top:h_top_old] cover=@2 floor=@2 above=[other(h_land:SSLComments sp_scan sp_mid ∧ sp_m…),other((∃ k, SIndent k sp_mid sp_sc) ∨ ∃ sa sb,…),char(c = '-'),char(c = ':' ∨ c = '?'),char(c = ':'),other((if s_prep.allowDirectives = true then {…),opt(h_kslot:(∀ (nv : Nat), nv ∈ Proofs.Regis…)] beside=[other(s_prep.allowDirectives = true)→—|—]"]
-- 2026-10-21 (item 319): four rows re-read for the paid block-lane arms — the `rcases … | h_alt` and `| Or.inr h_alt`
-- vectors (`h_resSeqV`, `h_closeFV_old` ×2, `h_kslot`/`h_kslotUp`) read `—` where they read `punt`: the arm hands the park's
-- alternative on at the park's own state instead of closing with `trivial`.
-- 2026-10-23 (item 344): five `accum_block_on_pendingBlock` decisions write `E:node×6` (was ×5) — the caller's
-- `h_valFV` now relays `h_closeFV_old`'s node-domained closure.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-26 (item 370): four `accum_block_on_pendingBlock` rows write one more `E:empty` — the sibling `-` arm's
-- `match h_closeF_old` has an `Or.inr _ => Or.inr trivial` arm (the frameless park stays frameless).
-- 2026-10-26 (item 369): 46 → 48 — the `:`/`?` landing in `accum_block_on_pendingBlock` decides `h_closeF_old`
-- (`rcases` on the frames, `by_cases FrameLevel.map k ∈ ks`) to pay `indicator_open_map`'s `h_res_land`.
-- 2026-10-29 (item 388): the landed `-` birth splits `nv ≤ k` after `nv < k` — the `nv = k` arm pays the
-- Summary: decisions 120 → 121, decOnK 24 → 25, decKN 11 → 12, apps 46 → 47 (the one new `dite`).
-- sequence as the mapping's VALUE (`valueLandedSeq`, `.blockOut`) instead of `h_seqBottom`'s bare root node.
-- 2026-10-29 (item 389): 51 → 56 — the landed birth's `nv < k` arm splits on `s_prep.currentIndent < k` (pushed → refuted by `pushedBirth_not_mapTop`, no-push → declined) and the `-` park's k = n arm reads the mapping-top conjunct `h_mt` beside item 387's `atSequenceIndent` split (mapping top paid, sequence top punt).
-- 2026-10-30 (item 405): the `closeThenBlock` resume-branch decision reads the chain birth (`hkv` + `hkvUp` destructured, `h_resKslot` declined).
def expectedDecisions : List String :=
  [ "flowKeyRoute_of_root dite kmem [Proofs.IndentStackCover.FrameLevel.map w ∈ ks] → E:other(lemma:SSLCommentsFrom_at_park(prem:ScannerSurfCorr,prem:GStar,prem:∀→Not,lemma:left(prem:And),lemma:left(lemma:right(lemma:right(…)))))|punt pos=—",
    "flowKeyRoute_of_root dite kmem [Proofs.IndentStackCover.FrameLevel.map w ∈ ks] → E:other(lemma:SSLCommentsFrom_at_park(prem:ScannerSurfCorr,prem:GStar,prem:∀→Not,lemma:left(prem:And),lemma:left(lemma:right(lemma:right(…)))))|punt pos=—",
    "flowKeyRoute_of_root match k∃ [h_res_land,h_sfx,h_nodoc:((∃ ks', (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks' → fr.wid…] → —|—|—|P:spend pos=—",
    "flowKeyRoute_of_root match k∃ [h_resV_land:(∃ nv ks', (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks' → fr.w…] → paid|punt pos=—",
    "flowKeyRoute_of_root match k∃ [h_res_land,h_sfx,h_nodoc:((∃ ks', (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks' → fr.wid…] → paid|paid|paid|paid,P:spend pos=—",
    "flowKeyRoute_of_root match k∃ [h_resV_land:(∃ nv ks', (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks' → fr.w…] → paid|punt pos=—",
    "accum_block_on_closeThenBlock dite kmem [Proofs.IndentStackCover.FrameLevel.map k ∈ ks] → E:comments|— pos=—",
    -- item 385: `h_res_land`'s `hmem` dite no longer punts — its no-pop leaf is the
    -- `deeperLandingResume` call (`—`), so the row reads like the one above and is pinned twice
    "accum_block_on_closeThenBlock dite kmem [Proofs.IndentStackCover.FrameLevel.map k ∈ ks] → E:comments|— pos=—",
    "accum_block_on_closeThenBlock dite knv [ke = k] → E:comments|— pos=—",
    "accum_block_on_closeThenBlock dite kn [nv ≤ k] → paid,E:node|punt pos=—",
    "accum_block_on_closeThenBlock dite kmem [Proofs.IndentStackCover.FrameLevel.seq k ∈ ks] → E:comments|punt pos=—",
    "accum_block_on_closeThenBlock match k∃ [h_resSeqV:(∃ nv ks, (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks → fr.wid…] → paid,E:prem|— pos=—",
    "accum_block_on_closeThenBlock match k∃ [h_slotV:(∃ nv ks, (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks → fr.wid…] → paid|— pos=—",
    "accum_block_on_closeThenBlock dite kn [nn < k] → paid,E:other(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)))|— pos=—",
    "accum_block_on_closeThenBlock dite kn [nv ≤ k] → paid,E:node×2|punt pos=—",
    "accum_block_on_closeThenBlock dite kn [nv ≤ k] → punt|punt pos=—",
    "accum_block_on_closeThenBlock dite kn [nv + 1 ≤ k] → E:pass×4|punt pos=—",
    "accum_block_on_closeThenBlock dite kmem [k ∈ ns] → E:pass|— pos=—",
    "accum_block_on_closeThenBlock dite kmem [k ∈ ns] → E:pass|— pos=—",
    "accum_block_on_closeThenBlock dite kn [nv < k] → paid,E:other(lemma:SBlockNode_blockIn_to_blockOut(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail))))|E:other(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)))×2,E:pass,E:carry pos=—",
    "accum_block_on_closeThenBlock dite k? [s_prep.currentIndent < ↑k] → paid|paid pos=—",
    "accum_block_on_closeThenBlock dite kn [nv ≤ k] → paid,E:other(SBlockNode.blockSeq(GOpt.none,prem:SSLComments,lemma:SBlockSeqEntries_of_compactTail(prem:SIndent,prem:GLit,prem:GNot,prem:SBlockIndented,prem:SCompactSeqTail)))×2,E:pass|paid,E:carry pos=—",
   -- 2026-10-29 (item 387): the no-pop arm's strict split `n < k` (paid: the helper; `E:pass`: `k = n` to the sequence-top split).
    "accum_block_on_pendingBlock Or.casesOn kn [n < k ∨ n ≥ k] → E:node×5|P:hand,E:carry,E:empty×3,E:node pos=—",
    -- item 385: the no-pop leaf decides on `s_prep.indents = sc.indents` and passes the park's
    -- frames into `deeperLandingResumeSeq` (the dedent stays declined inside the helper)
    "accum_block_on_pendingBlock dite col0 [sp_scan.col = 0] → punt|paid pos=beside#3",
    "accum_block_on_pendingBlock dite kn [n + 1 ≤ k] → E:pass×4|punt pos=beside#3",
    "accum_block_on_pendingBlock Or.elim other [h_land:SSLComments sp_scan sp_mid ∧ sp_mid.col = 0 ∧ (sp_scan.col ≠ 0 → s_prep.…] → E:empty×12,E:pass×15,E:node×6,P:hand,E:carry×2,P:spend×4|E:prem,E:node×6,E:pass pos=above#3,above#4,above#5,above#6",
    "accum_block_on_pendingBlock Or.casesOn opt [h_closeFV_old:(∃ nv ks, (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks → fr.wid…] → E:empty|— pos=beside#3",
    "accum_block_on_pendingBlock dite kmem [Proofs.IndentStackCover.FrameLevel.map k ∈ ks] → —|— pos=beside#3",
    "accum_block_on_pendingBlock Or.elim other [(∃ k, SIndent k sp_mid sp_sc) ∨ ∃ sa sb, GStar SSWhite sp_mid sa ∧ SSWhi…] → E:empty×12,E:pass×15,E:node×6,P:hand,E:carry×2,P:spend×4|— pos=above#3,above#4,above#5,above#6",
    "accum_block_on_pendingBlock dite char [c = '-'] → E:empty×9,E:pass,E:node×6,P:hand,E:carry|P:spend×4,E:empty×3,E:pass×14,E:carry pos=above#3,above#4,above#5,above#6",
    "accum_block_on_pendingBlock dite char [c = ':' ∨ c = '?'] → P:spend×4,E:empty×3,E:pass×14,E:carry|— pos=above#3,above#4,above#5,above#6",
    "accum_block_on_pendingBlock Or.elim opt [h_kslotUp:(∃ ns, Proofs.RegisterWitness.MarkedColsIn sc ns ∧ ∀ (nv : Nat), nv ∈ ns…] → —|punt pos=beside#4",
    "accum_block_on_pendingBlock dite other [∀ (x : Nat), x ∈ ns → x = k] → paid|punt pos=beside#4",
    "accum_block_on_pendingBlock dite kmem [k ∈ nsU] → paid,E:carry,E:pass|— pos=—",
    "accum_block_on_pendingBlock dite kn [n + 1 ≤ k] → E:pass×5|punt pos=beside#3",
    "accum_block_on_pendingBlock match opt [h_kslot,h_kslotUp:((∀ (nv : Nat), nv ∈ Proofs.RegisterWitness.markedCols sc → ∀ (sp_m : Su…] → paid,E:pass×3|paid,E:pass|paid,E:pass|— pos=beside#3",
    "accum_block_on_pendingBlock Or.casesOn k∃ [h_upSpend:(∀ (sp_m : SurfPos), SBlockIndented n YamlContext.blockIn sp_scan sp_m →…] → —|— pos=—",
    "accum_block_on_pendingBlock Or.casesOn k∃ [h_upSpend:(∀ (sp_m : SurfPos), SBlockIndented n YamlContext.blockIn sp_scan sp_m →…] → —|— pos=—",
    "accum_block_on_pendingBlock match opt [h_kslot,h_kslotUp:((∀ (nv : Nat), nv ∈ Proofs.RegisterWitness.markedCols sc → ∀ (sp_m : Su…] → paid,E:pass×3|paid,E:pass|punt pos=beside#3",
    "accum_block_on_pendingBlock dite char [c = ':'] → P:spend×3,E:carry,E:pass×3|— pos=above#4,above#5,above#6",
    "accum_block_on_pendingBlock Or.casesOn k∃ [h_upSpend:(∀ (sp_m : SurfPos), SBlockIndented n YamlContext.blockIn sp_scan sp_m →…] → —|P:spend pos=above#5",
    "accum_block_on_pendingBlock dite other [s_prep.allowDirectives = true] → —|— pos=beside#5",
    "accum_block_on_pendingBlock dite other [s_prep.allowDirectives = true] → —|— pos=beside#6",
    "accum_block_on_pendingBlock dite other [(if s_prep.allowDirectives = true then { input := s_prep.input, inputEnd…] → E:pass|E:pass,P:spend×2 pos=above#5,above#6",
    "accum_block_on_pendingBlock dite kmem [k ∈ Proofs.RegisterWitness.markedCols sc] → E:pass|— pos=—",
    "accum_block_on_pendingBlock Or.casesOn opt [h_kslot:(∀ (nv : Nat), nv ∈ Proofs.RegisterWitness.markedCols sc → ∀ (sp_m : Sur…] → E:pass,P:spend|P:spend pos=above#5,above#6",
    "accum_block_on_pendingBlock dite kn [k = n] → E:empty×6,E:pass|E:node×6,P:hand,E:carry,E:empty×3 pos=—",
    "accum_block_on_pendingBlock dite k? [s_prep.currentIndent < ↑k] → paid|E:pass,E:empty pos=—",
    "accum_block_on_pendingBlock dite kmem [k ∈ Proofs.RegisterWitness.markedCols sc] → E:pass|P:spend pos=above#5",
    "accum_block_on_pendingBlock Or.casesOn opt [h_closeF_old:(∃ ks, (∀ (fr : Proofs.IndentStackCover.FrameLevel), fr ∈ ks → fr.width …] → E:empty×2,E:pass×2|punt pos=beside#3",
    "accum_block_on_pendingBlock dite kmem [Proofs.IndentStackCover.FrameLevel.map k ∈ ks] → E:empty|E:pass×2,E:empty pos=beside#3",
    "accum_block_on_pendingBlock Or.elim other [s_prep.indents = sc.indents ∨ ¬s_prep.indents = sc.indents] → E:pass×2,E:empty|— pos=beside#3",
    "accum_block_on_pendingBlock dite kn [n < k] → paid,E:pass|E:pass,E:empty pos=beside#3",
    "accum_block_on_pendingBlock Or.elim other [atSequenceIndent s_prep = true ∧ (c = ':' → (if s_prep.allowDirectives =…] → —|E:pass,E:empty pos=beside#3",
    "accum_block_on_pendingBlock dite other [atSequenceIndent s_prep = false] → E:pass,E:empty|punt pos=beside#3",
    "accum_block_on_pendingBlock Or.casesOn opt [h_mt:((∃ e, sc.indents.back? = some e ∧ e.isSequence = false) → ∀ (sp_mid : S…] → E:pass,E:empty|— pos=beside#3"]
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-26 (item 369): h_res_land=punt → h_res_land=cond[opt,kmem] — `h_res_land` read off `pendingBlock.h_closeF`.
-- 2026-10-29 (item 387): `h_res_land=cond[opt,kmem,other,kn]` — the no-pop arm's `n < k` split joins its conditions.
def expectedArgs : List String :=
  -- item 385: `h_res_land` is conditioned on the no-pop decision too (`other`: `s_prep.indents = sc.indents`)
  [ "accum_block_on_pendingBlock → indicator_open_map: h_sfx_land=punt h_nodoc_land=punt h_mk_land=punt h_res_land=cond[opt,kmem,other,kn] h_ref_land=punt h_cov=cond[col0] h_pr_land=punt h_explUp_chain=cond[kn,opt] h_resV_land=cond[opt,kmem] h_explUp_chainD=cond[kn,opt]"]
-- Item 284: `pendingBlock` gains a seventeenth field, `h_offer`, and this door
-- DROPS it — the `-` dispatched off the park reads the offer of the `-` it pushes,
-- never the park's own — so the row reads one more field, one more face and one
-- more drop, and every field the door used it still uses.
-- Item 293: `pendingBlockContent` gains a nineteenth field, `h_live`, and this
-- door USES it — `accum_block_pending` hands it to the `:` consumer — so the row
-- reads one more field, one more face and one more use, and drops what it did.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-26 (item 369): used=10 → used=11, dropped=4 → dropped=3, h_close(_h_close),h_closeF(h_closeF✝),h_nodir(h_nodir✝),h_offer(h_offer✝) → h_close(_h_close),h_nodir(h_nodir✝),h_offer(h_offer✝) — `pendingBlock.h_closeF` is now read by
-- `accum_block_on_pendingBlock` (the `:`/`?` landing's `h_res_land`).
def expectedDoor : List String :=
  ["PendingNode.pendingBlock: fields=18 data=4 faces=14 equations=5 used=11 dropped=3 h_close(_h_close),h_nodir(h_nodir✝),h_offer(h_offer✝)",
   "PendingNode.pendingBlockContent: fields=22 data=5 faces=17 equations=5 used=16 dropped=1 h_nodir(h_nodir✝)"]
-- 2026-10-18 (item 284): `decisions` 126 → 127, `apps` 39 → 40 and `doorDropped`
-- 3/2 → 4/2, and nothing else.  The door's extra drop is `pendingBlock.h_offer`
-- (above).  The other two are ONE payment: the walk meets the `-` producer's
-- new field in `accum_block_on_closeThenBlock`, so it records the application
-- `dispatchBlock_dash_offerPred` and, inside its implicit state argument, the
-- allowDirectives-update `if` as a decision.  Dumped and diffed against the
-- item-281 source with this file's own walk, those two records are the whole
-- difference (`scratchpad/l4yaml-row12-steps/87-door-284.txt` against
-- `89-door-orig.txt`).
/-- Item 256 adds one decision to the content sibling's arm — the `match` on
    `h_closeF_old` that relays the park's frames — and one spend of the
    landing's comments on each of that arm's four decision rows.  Item 258 adds no decision and one effect: the compact re-park's resume
    frames bottom out on `h_close_old`, the entry closure over
    `h_close_entry_old`, applied to the compact sequence — an `E:node` in the
    inline branch of `accum_block_on_pendingBlock`'s landing decision
    (`E:node×5` → `×6`); the nested landing's bottom applies `h_close_inner`,
    whose domain is the inner collection's entries, which this census does
    not read as an entry-closure spend. -/
-- Item 305: the sequence fields carry the width bound and `closeThenBlock` decides the first entry's
-- stack on the `?` slot: `decisions` 127 → 132, `decOnK` 23 → 24, `decKN` 9 → 10.
-- 2026-10-20 (item 307): `decisions` 132 → 139, `decOnK` 24 → 25, `decKMem` 9 → 10, `apps` 40 → 45.
-- 2026-10-20 (item 307, second chain): `decisions` 139 → 141.
-- 2026-10-21 (item 319): `apps` 45 → 47 — `accum_block_on_closeThenBlock`'s two `h_resKslot` relays are applications now
-- (`h_resKslot.imp id (PackAlt.step_blockEntry h_preprocess h_dispatch)`, the block lane's transport); every other count stands.
-- 2026-10-21 (item 320): `apps` 47 → 48 — `accum_block_on_closeThenBlock`'s `h_seqFramesV` relay is an application now
-- (`.imp id (PackAlt.step_blockEntry h_preprocess h_dispatch)`); every other count stands.
-- 2026-10-23 (item 344): decisions 138 → 139 — the relayed `h_valFV` adds a `match` on `h_closeFV_old`.
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-26 (item 369): closeF=0 → closeF=4, puntKMem=0 → puntKMem=1, decisions=115 → decisions=117, decOnK=22 → decOnK=23, decKMem=9 → decKMem=10, apps=42 → apps=43, doorDropped=4/1 → doorDropped=3/1 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
-- 2026-10-26 (item 370): decisions 117 → 118 — the sibling `-` arm decides `h_closeF_old` once more.
-- 2026-10-28 (item 385): decisions 118 → 119, apps 43 → 46 — the two paid no-pop leaves
-- (`deeperLandingResume` at `closeThenBlock`, `deeperLandingResumeSeq` at `pendingBlock`) are applications; `pendingBlock` decides `s_prep.indents = sc.indents` on the way.
-- 2026-10-29 (item 387): decisions 119 → 120, decOnK 23 → 24, decKN 10 → 11 — the no-pop arm's `dite n < k`.
-- 2026-10-29 (item 389): decisions 121 → 126, apps 47 → 48 — the five new decision rows above (two `currentIndent < k` splits, the k = n arm's `h_mt` read) and `pushedBirth_not_mapTop`'s application at the landed birth.
-- 2026-10-30 (item 405): see `expectedSpends`/`expectedDecisions` (the `?`-park chain ladder PAID).
-- 2026-10-30 (item 405, Rule 8 fix): `apps` 43 → 48 — the five `h_kslot` decisions apply `MarkedColsIn.relay`/`markedCols` instead of destructuring a chain.  Rule 8 fix (same item): the five `h_kslot` decisions re-read with the projection (`∀ (nv : Nat), nv ∈ markedCols sc …`; the `kmem` splits read `k ∈ markedCols sc`).
def expectedLine : String :=
  -- 2026-10-26 (item 366): decisions 114 → 115 — the `Classical.em (MarkedColsIn sc [k])` decision at
  -- `accum_block_on_closeThenBlock`'s explicit `:` face; no frame row moved.
-- Item 371 (kslot=4 → 0, kslotUp=4 → 0): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
  "asked=6 both=4 lemmas=1 walked=4 feedFunnel=1 feedExplicit=1 feedDeferred=2 feedTuple=0 entry=4 entrySBI=4 kslot=0 kslotUp=0 closeF=4 closeFV=4 seqF=4 top=4 floor=0 cover=4 cover2=4 floorB=4 aboveKN=0 aboveKMem=1 aboveKNv=0 aboveKEx=1 hands=1 besideKN=1 besideKMem=1 besideKNv=0 puntKN=1 puntKMem=0 besideNone=0 decisions=130 decOnK=25 decKN=12 decKMem=12 decKNv=1 apps=48 funnelArgs=1 doorDropped=3/1 closeSites=5 params=5"

/-! ## §5 The reading -/

set_option maxHeartbeats 8000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  -- §1 item 251's closes, re-derived from item 249's trace
  let (s, _reach) ← runTrace
  let mut segs : Array Tests.Guards.StreamCompositions.Found := #[]
  for f in s.found do
    if !segs.any (fun g => g.site == f.site && g.seg == f.seg) then segs := segs.push f
  let genuine := segs.filter fun f => compOf f.seg != "(via)"
  let mut closeSites : Array String := #[]
  for f in genuine do
    let comp := compOf f.seg
    let sps := (f.spine.splitOn " | ").toArray.filter fun sp => isClosePair sp comp
    if sps.isEmpty then continue
    if !closeSites.contains f.site then closeSites := closeSites.push f.site
  let mut params : Array (Name × Name) := #[]
  for site in closeSites do
    let (callee, pname) ← calleeOf site
    if !params.contains (callee, pname) then params := params.push (callee, pname)
  -- (2026-10-24, B3 [66] col-0 threading: 8/7 → 5/5, as CloseLandingWidth pins)
  unless closeSites.size == 5 && params.size == 5 do
    throwError "item 251's frame moved under this pass: closeSites={closeSites.size} params={params.size}"
  -- §2 the walk
  let st ← IO.mkRef ({} : S)
  let mut walked : Array String := #[]
  for (callee, pname) in params do
    -- the value slot is a package, not a closure: item 251 found its spends
    -- are nodes; the split question is asked of the comments closures
    let some ci := (← getEnv).find? callee | continue
    let isClosure ← forallTelescope ci.type fun xs _ => do
      for x in xs do
        if (← x.fvarId!.getDecl).userName == pname then
          return (← closeBinder (← inferType x)).isSome
      return false
    if !isClosure then continue
    followS st callee pname
    walked := walked.push s!"{short callee}.{pname}"
  let w ← st.get
  let useTags (d b : Nat) : Array String :=
    let ts := (w.uses.filter fun (d', b', _) => d' == d && b' == b).map (·.2.2)
    let ds := distinctS ts
    ds.map fun t => let c := (ts.filter (· == t)).size; if c == 1 then t else s!"{t}×{c}"
  let brSummary (d : Decision) : String :=
    String.intercalate "|" ((List.range d.nBranches).map fun b =>
      let ts := useTags d.id b
      if ts.isEmpty then "—" else String.intercalate "," ts.toList)
  -- spends
  let asked := w.spends.filter fun r => r.kind == "spend" && r.cls == "comments"
  let isInd (r : SpendRow) := r.width.startsWith "ind["
  let isDirect (r : SpendRow) := r.index.startsWith "direct["
  let both := asked.filter fun r => isInd r && isDirect r
  let mut spendLines : Array String := #[]
  let mut nBoth := 0
  let mut idxOf : Std.HashMap Nat Nat := {}
  for r in w.spends do
    if r.kind != "spend" then continue
    if r.cls != "comments" then continue
    let isBoth := isInd r && isDirect r
    if isBoth then nBoth := nBoth + 1
    let sid := spendLines.size + 1
    -- decisions above and beside
    let aboveD := w.decisions.filter fun d => r.above.contains d.id
    let besideD := w.decisions.filter fun d => match d.app, r.app with
      | some (a, i), some (a', i') => a == a' && i != i'
      | _, _ => false
    for d in aboveD ++ besideD do idxOf := idxOf.insert d.id sid
    let aboveS := String.intercalate "," (aboveD.map fun d => s!"{d.cls}({collapse d.cond 40})").toList
    let besideS := String.intercalate "," (besideD.map fun d => s!"{d.cls}({collapse d.cond 40})→{brSummary d}").toList
    spendLines := spendLines.push s!"  {short r.lem} #{sid} {if isBoth then "BOTH" else "width"} feeds={r.feeds} frames={r.frames} cover={r.cover} floor={r.floorB} above=[{aboveS}] beside=[{besideS}]"
  -- decisions on k, wherever they stand, and every decision beside or above one of the eight
  let bothIds : Array Nat := Id.run do
    let mut out := #[]
    let mut sid := 0
    for r in w.spends do
      if r.kind != "spend" || r.cls != "comments" then continue
      sid := sid + 1
      if isInd r && isDirect r then out := out.push sid
    return out
  let mut decLines : Array String := #[]
  for d in w.decisions do
    let onK := d.cls == "kn" || d.cls == "kmem" || d.cls == "knv" || d.cls == "k?" || d.cls == "k∃"
    -- position relative to the eight
    let mut pos : Array String := #[]
    let mut sid := 0
    for r in w.spends do
      if r.kind != "spend" || r.cls != "comments" then continue
      sid := sid + 1
      if !(isInd r && isDirect r) then continue
      if r.above.contains d.id then pos := pos.push s!"above#{sid}"
      else match d.app, r.app with
        | some (a, i), some (a', i') => if a == a' && i != i' then pos := pos.push s!"beside#{sid}"
        | _, _ => pure ()
    if onK || !pos.isEmpty then
      decLines := decLines.push s!"  {short d.lem} {d.kind} {d.cls} [{d.cond}] → {brSummary d} pos={if pos.isEmpty then "—" else String.intercalate "," pos.toList}"
  let _ := bothIds
  -- the funnel's arguments at the spends that feed it
  let mut argLines : Array String := #[]
  for r in both do
    if let some (aid, _) := r.app then
      if let some a := w.apps.find? (·.id == aid) then
        if a.callee != ``indicator_open_map then continue
        let mut parts : Array String := #[]
        for i in a.optArgs do
          let nm := if i < a.names.size then a.names[i]!.toString else s!"#{i}"
          let h := if i < a.heads.size then a.heads[i]! else "—"
          let h := if h == "cond" then
              let ds := w.decisions.filter fun d => d.app == some (aid, i)
              s!"cond[{String.intercalate "," (distinctS (ds.map (·.cls))).toList}]"
            else h
          parts := parts.push s!"{nm}={h}"
        argLines := argLines.push s!"  {short r.lem} → {short a.callee}: {String.intercalate " " parts.toList}"
  -- §3 the door
  let doorLines ← doorOf ``accum_block_pending [``PendingNode.pendingBlock, ``PendingNode.pendingBlockContent]
  let doorLines := doorLines.map ("  " ++ ·)
  -- the counts
  let bothRows := both
  let count (p : SpendRow → Bool) := (bothRows.filter p).size
  let hasFace (f : String) (r : SpendRow) := (r.frames.splitOn s!"{f}:").length > 1 || (r.frames.splitOn s!"{f}(").length > 1
  let decOf (r : SpendRow) (where_ : String) : Array Decision :=
    w.decisions.filter fun d =>
      if where_ == "above" then r.above.contains d.id
      else match d.app, r.app with
        | some (a, i), some (a', i') => a == a' && i != i'
        | _, _ => false
  let hasPunt (d : Decision) : Bool :=
    (List.range d.nBranches).any fun b => (useTags d.id b).any (·.startsWith "punt")
  let cnt (where_ cls : String) := (bothRows.filter fun r => (decOf r where_).any fun d => d.cls == cls).size
  let cntPunt (cls : String) := (bothRows.filter fun r => (decOf r "beside").any fun d => d.cls == cls && hasPunt d).size
  let feedsOf (pre : String) := count fun r => r.feeds.startsWith pre
  let doorDropped := doorLines.map fun l => ((l.splitOn "dropped=")[1]!.splitOn " ")[0]!
  let got := s!"asked={asked.size} both={nBoth} lemmas={(distinctS (bothRows.map fun r => short r.lem)).size} walked={walked.size} \
feedFunnel={feedsOf "indicator_open_map."} feedExplicit={feedsOf "colon_open_map_explicit."} feedDeferred={feedsOf "block_dispatch_deferred_stamp_"} feedTuple={feedsOf "tuple"} \
entry={count (hasFace "entry")} entrySBI={count (hasFace "entry(SBI)")} kslot={count (hasFace "kslot")} kslotUp={count (hasFace "kslotUp")} closeF={count (hasFace "closeF")} closeFV={count (hasFace "closeFV")} seqF={count (hasFace "seqF")} top={count (hasFace "top")} floor={count (hasFace "floor")} \
cover={count fun r => r.cover != "none"} cover2={count fun r => r.cover == "@2"} floorB={count fun r => r.floorB != "none"} \
aboveKN={cnt "above" "kn"} aboveKMem={cnt "above" "kmem"} aboveKNv={cnt "above" "knv"} aboveKEx={cnt "above" "k∃"} hands={(w.spends.filter (·.kind == "hand")).size} besideKN={cnt "beside" "kn"} besideKMem={cnt "beside" "kmem"} besideKNv={cnt "beside" "knv"} puntKN={cntPunt "kn"} puntKMem={cntPunt "kmem"} besideNone={count fun r => (decOf r "beside").isEmpty} \
decisions={w.decisions.size} decOnK={(w.decisions.filter fun d => d.cls == "kn" || d.cls == "kmem" || d.cls == "knv").size} decKN={(w.decisions.filter (·.cls == "kn")).size} decKMem={(w.decisions.filter (·.cls == "kmem")).size} decKNv={(w.decisions.filter (·.cls == "knv")).size} \
apps={w.apps.size} funnelArgs={argLines.size} doorDropped={String.intercalate "/" doorDropped.toList} closeSites={closeSites.size} params={params.size}"
  logInfo s!"CloseSplitFrames {got}"
  logInfo s!"spends:\n{String.intercalate "\n" spendLines.toList}"
  logInfo s!"decisions:\n{String.intercalate "\n" decLines.toList}"
  logInfo s!"args:\n{String.intercalate "\n" argLines.toList}"
  logInfo s!"door:\n{String.intercalate "\n" doorLines.toList}"
  -- (2026-10-24, B3 [66] col-0 threading: 13/8 → 6/4 — the content parks' closes are asked from `sp_gram`)
  unless asked.size == 6 && nBoth == 4 do
    throwError "item 251's reading moved under this pass: asked={asked.size} both={nBoth}"
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "expectedSpends" spendLines expectedSpends
  check "expectedDecisions" decLines expectedDecisions
  check "expectedArgs" argLines expectedArgs
  check "expectedDoor" doorLines expectedDoor
  unless got == expectedLine do
    throwError "CloseSplitFrames moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.CloseSplitFrames
