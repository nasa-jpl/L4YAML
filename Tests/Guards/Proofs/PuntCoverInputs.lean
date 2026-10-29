/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.CloseStackCover

/-!
# How many of the eleven producers that punt a park's resume stack hold a cover's inputs, and at what floor (DOCS item 254)

Item 253 found the entry park's field punted at six of its seven producers,
the mapping value park's at two of six and the props park's entry face at
three of six — eleven producers that hand a park a stack with no cover.  The
one literal payment in the library, `indicator_cover_at_col`, takes the
stack's monotonicity and base, the landing's floor and the dispatch; where
those stand in hand a punt is a choice, and where they do not it is a debt
with a producer's name on it.  This module reads, at each of the eleven,
what stands in hand against that signature, and which floor a payment there
could name.

**§1** re-finds the eleven off item 253's walk: `Row` carries the binder
stack and the constructor's arguments at every constructor row, so the same
walk, checked against item 253's pinned rows, hands this module the context
of each punt.  **§2** reads the stack by shape — a hypothesis counts only
where its conclusion IS the shape; one that mentions the shape inside an
option is listed apart and credited nothing.  **§3** is the verdict: the
inputs present or the names missing, and the floor each site could name —
its own index where a top bound or a landed arm stands, zero where the top
bound is negative, a relay's floor where a cover-carrying hypothesis stands,
with that cover's `Floor` index and list printed so a floor at the park's own
index is never read as a floor below it.  **§4** reads the four field types
themselves: the frames bound, the cover's list and the `Floor`'s index — the
shape that decides whether an own-index payment is statable at all.  **§5**
(item 258) reads each site's top bound against its index: the floor
`covered_nil_of_top_le` gives from it, whether the bound stands strictly
below the index — syntactically, or by a binder in scope — and beside it the
state the bound is about, whether `Mono` in hand is about that state, and
whether the site is landed or inline, since a bound on an earlier state
crosses preprocessing's unwind at a landed site.
**§6** (item 259) reads, at each site that lacks `Mono`, what its CALLERS
hold about the state they pass it — every application of the enclosing lemma
in the environment, with `Mono`, the base and each top bound on the
pre-dispatch argument against the site's index instantiated by the caller —
and beside it the cover step the library holds for the site's dispatch, the
shape of its conclusion, the named-level lemmas, and whether the site pins
its top from both sides.  **§6 one hop back** (item 260) reads the same callers
through their own preprocess equation — `Mono`, the base and each top bound
on the state the argument was preprocessed FROM — and beside each site the
closure it holds toward the stream with the level it closes read against
the site's index (the resume's BOTTOM), and the field's index witness where
its statement binds the index by an equation.

**Item 256 pays two of the eleven**: the root `-` its own field, from the
seed's empty stack at floor 0 (`IndentStackCover.covered_nil_of_ntop`), and
the content park's sibling by relaying `h_closeF_old` at the unchanged index.
The compact fill's relay of `h_valF` is refuted there — that closure awaits
a block node read at the park's position, and the compact fill's node is a
compact sequence on the slot's own line — and **item 257 pays the compact
fill a third way**: a literal from the slot's own top bound
(`IndentStackCover.covered_nil_of_top_le`), floored at `nv + 1` below the
fill's index `nv + 1 + m`, because the top bound that site holds is the
SLOT's and not the park's — the reading item 254's own-index verdict did not
take.  **Item 258 pays two more the same way**, from the entry park's own top
bound `h_top_old`: its inline compact re-park (`- - a`, floor `n + 1` below
the index `n + 1 + m`) and its nested landing (`-⏎  - a`, floor `n + 1` below
the index `k` by the arm's `n < k`) — the landed site's bound is the OLD
park's, and it transports because preprocessing's unwind only pops.  Six
punts remain, and the reading below is theirs: three hold no top bound and
three hold one at their own index, so none holds the shape these payments
spend.  **Item 259 pays the compact opener through its callers**: its slot's
own bound is at the index, but §6 reads both callers holding `Mono` and a
bound below the slot's index on the state before the dispatch, the library's
step across the indicator (`dispatchBlockIndicators_cover`, a `CoverStep`
whose opened level is existential), and the site pinning its top from both
sides — so the opener takes the two as binders and pays the mapping value
park's field with that cover, the level named by the pinned top
(`IndentStackCover.CoverStep.cons_of_top_eq`).  Five punts remain: three
hold no top bound, two hold one at their own index, and the three that lack
`Mono` are called with a state no caller bounds below the index.  **Item 260
reads those three one hop back.**  The explicit `:`'s three callers each
hold `Mono`, the base and their preprocess equation on the state they
preprocessed from, so `Mono` at the opener's own state is one transport
away and the opener's own top bound pays the head of its list at its own
floor (`covered_singleton_of_top_le`); no caller holds a bound below the
landing width, so no lower floor.  What the site lacks is the field's
BOTTOM: its list is headed, so the resume needs the level's tail closed,
and the closures it holds (`hvp`, `h_slot`) close the value at the level
itself.  The paid producers of the same field hold that bottom one of two
ways — the level inside a closed node one below (`compact_open_map`), or a
relay of the pack's resume (`h_routeF`, `h✝`: a tail at the level behind a
map entry or the landing) — and this site holds neither; its callers hold
the relay's raw material (`h_res_land`, a tail from the landing, and the
`frames(ks)` faces `resumeAt` reads), and spending it here means reading
the value line as `[192]`'s empty-key entry from the landing — a derivation
of the same string, not the entry the scanner parsed.  The props router
builds both parks at index 0,
where the entry-level field's equation `n = ne + 1` has no witness: those
two positions are the field's own vacuity at the root, not punts a caller
could fund.
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
open Tests.Guards.CloseStackCover
set_option autoImplicit false

namespace Tests.Guards.PuntCoverInputs

/-- The three positions item 253 found punted, and the content park's field
    beside them for the shape reading. -/
def targets : List String :=
  ["ctor:pendingBlock.h_closeF", "ctor:pendingMapValue.h_closeF", "ctor:pendingProps.h_closeFE"]

def shapeTargets : List (Name × Name) :=
  [(``PendingNode.pendingBlock, `h_closeF), (``PendingNode.pendingBlockContent, `h_closeF),
   (``PendingNode.pendingMapValue, `h_closeF), (``PendingNode.pendingProps, `h_closeFE)]

/-! ## §0 Printing: characters, casts and the directive update -/

partial def ppc (st : Stack) (e : Expr) : String :=
  let e := e.consumeMData
  let f := e.getAppFn
  let args := e.getAppArgs
  match f with
  | .const n _ =>
    if n == ``Char.ofNat && args.size == 1 then
      match args[0]!.consumeMData with
      | .lit (.natVal v) => s!"'{Char.ofNat v}'"
      | _ => pp st e
    else if (n == ``Nat.cast || n == ``NatCast.natCast || n == ``Int.ofNat || n == ``Int.cast || n == ``IntCast.intCast) && args.size ≥ 1 then
      ppc st args[args.size - 1]!
    else if n == ``ite && args.size ≥ 5 then s!"{ppc st args[4]!}*"
    else if n == ``ScannerState.currentIndent && args.size == 1 then s!"{ppc st args[0]!}.currentIndent"
    else if n == ``ScannerState.col && args.size == 1 then s!"{ppc st args[0]!}.col"
    else if n == ``SurfPos.col && args.size == 1 then s!"{ppc st args[0]!}.col"
    else pp st e
  | _ => pp st e

/-- A relation, `Not` stripped, as (symbol, left, right). -/
def rel (t : Expr) : Option (String × Expr × Expr) :=
  let t := t.consumeMData
  let (neg, t) := if t.isAppOfArity ``Not 1 then (true, (t.getArg! 0).consumeMData) else (false, t)
  if t.isAppOfArity ``Eq 3 then some (if neg then "≠" else "=", t.getArg! 1, t.getArg! 2)
  else if t.isAppOfArity ``Ne 3 then some ("≠", t.getArg! 1, t.getArg! 2)
  else if t.isAppOfArity ``LE.le 4 then some ("≤", t.getArg! 2, t.getArg! 3)
  else if t.isAppOfArity ``LT.lt 4 then some ("<", t.getArg! 2, t.getArg! 3)
  else if t.isAppOfArity ``GE.ge 4 then some ("≤", t.getArg! 3, t.getArg! 2)
  else if t.isAppOfArity ``GT.gt 4 then some ("<", t.getArg! 3, t.getArg! 2)
  else none

/-- The structure an operand projects `proj` off: the operand is the
    projection, or a cast or a query one level over it. -/
def projOf (o : Expr) (proj : Name) : Option Expr :=
  let o := o.consumeMData
  if o.isAppOf proj then o.getAppArgs.back?
  else o.getAppArgs.findSome? fun a =>
    let a := a.consumeMData
    if a.isAppOf proj then a.getAppArgs.back? else none

def isZeroE (e : Expr) : Bool :=
  let e := e.consumeMData
  match e with
  | .lit (.natVal 0) => true
  | _ => e.isAppOfArity ``OfNat.ofNat 3 && (match (e.getArg! 1).consumeMData with | .lit (.natVal 0) => true | _ => false)

def isBoolLit (e : Expr) (b : Bool) : Bool :=
  e.consumeMData.isConstOf (if b then ``Bool.true else ``Bool.false)

/-- The state and character a preprocess equation's right side names:
    `.ok (some (s', c))`. -/
def digPrep (st : Stack) (rhs : Expr) : String :=
  let rhs := rhs.consumeMData
  let inner := if rhs.isAppOf ``Except.ok then (rhs.getAppArgs.back?.getD rhs).consumeMData else rhs
  let inner := if inner.isAppOf ``Option.some then (inner.getAppArgs.back?.getD inner).consumeMData else inner
  if inner.isAppOfArity ``Prod.mk 4 then s!"{ppc st (inner.getArg! 2)},{ppc st (inner.getArg! 3)}" else ppc st inner

/-- The first sub-term `p` accepts, descending through binders (whose names
    are pushed so widths print by name) and applications. -/
partial def findFirst (st : Stack) (t : Expr) (p : Stack → Expr → Option String) : Option String :=
  let t := t.consumeMData
  match p st t with
  | some s => some s
  | none =>
    match t with
    | .forallE n ty b _ => findFirst (st.push { name := n, ty := ty, prov := none }) b p
    | .lam n ty b _ => findFirst (st.push { name := n, ty := ty, prov := none }) b p
    | .app .. => t.getAppArgs.findSome? fun a => findFirst st a p
    | _ => none

def floorShape (st : Stack) (t : Expr) : Option String :=
  findFirst st t fun st t =>
    if t.isAppOfArity floorN 3 then some s!"Floor({ppc st (t.getArg! 1)},{ppc st (t.getArg! 2)})" else none

/-- `∀ k' ∈ ks, k' < n`: the frames bound, as its relation, list and bound. -/
def boundShape (st : Stack) (t : Expr) : Option String :=
  findFirst st t fun st t =>
    match t with
    | .forallE n ty b _ =>
      let ty := ty.consumeMData
      if ty.isAppOfArity ``Membership.mem 5 then
        let st' := st.push { name := n, ty := ty, prov := none }
        match rel b with
        | some (r, _, rhs) => some s!"bound({ppc st (ty.getArg! 3)}{r}{ppc st' rhs})"
        | none => none
      else none
    | _ => none

def eqShape (st : Stack) (t : Expr) : Option String :=
  findFirst st t fun st t =>
    match rel t with
    | some ("=", l, r) => if (l.consumeMData.isBVar || r.consumeMData.isBVar) && !(hasHead t ``ScannerState.col) && !(hasHead t ``SurfPos.col) then some s!"eq({ppc st l}={ppc st r})" else none
    | _ => none

/-! ## §1 The inputs in hand -/

structure Inputs where
  mono : Array String := #[]
  monoOpt : Array String := #[]
  base : Array String := #[]
  baseOpt : Array String := #[]
  prep : Array String := #[]
  dispB : Array String := #[]
  dispC : Array String := #[]
  hc : Array String := #[]
  chr : Array String := #[]
  corr : Array String := #[]
  noflow : Array String := #[]
  save : Array String := #[]
  fl : Array String := #[]
  top : Array String := #[]
  larm : Array String := #[]
  floor : Array String := #[]
  nic : Array String := #[]
  armed : Array String := #[]
  col0 : Array String := #[]
  ids : Array String := #[]
  cover : Array String := #[]
  coverFn : Array String := #[]
  -- item 258: the top bounds as (name, state, relation, bound), and every
  -- relation in hand as (name, relation, left, right), for the reading of a
  -- bound against the site's index
  tops : Array (String × String × String × String) := #[]
  rels : Array (String × String × String × String) := #[]
  deriving Inhabited

def monoN : Name := ``L4YAML.Proofs.IndentStackMono.Mono
def baseN : Name := ``L4YAML.Proofs.IndentStackBase.SentinelBase
def ifloorN : Name := ``L4YAML.Proofs.PreprocessIndentStable.IndentFloor

/-- A hypothesis whose conclusion is a conjunction has each conjunct in hand;
    one under an implication is kept whole (its premises apply to all of it).
    Only a NAMED hypothesis is split: the inaccessible binders a destructuring
    leaves behind (`right✝`) hold the same conjuncts its named pieces do. -/
partial def conjuncts (nm : String) (t : Expr) : Array (String × Expr) :=
  let t := t.consumeMData
  if t.isForall then #[(nm, t)]
  else if t.isAppOfArity ``And 2 then conjuncts (nm ++ ".1") (t.getArg! 0) ++ conjuncts (nm ++ ".2") (t.getArg! 1)
  else #[(nm, t)]

/-- The conclusion of a Pi type with its premises PUSHED, so the conclusion's
    indices resolve. -/
partial def piConclSt (st : Stack) (t : Expr) : Stack × Expr :=
  match t.consumeMData with
  | .forallE n ty b _ => piConclSt (st.push { name := n, ty := ty, prov := none }) b
  | t => (st, t)

def inputsAt (stAll : Stack) : Inputs := Id.run do
  let mut r : Inputs := {}
  for i in [0:stAll.size] do
    let b := stAll[i]!
    -- a binder's type was elaborated under the binders BEFORE it: its de
    -- Bruijn indices resolve against the prefix, not the whole stack
    let st0 := stAll.extract 0 i
    let t := b.ty
    let (st, c) := piConclSt st0 t
    let isPi := t.consumeMData.isForall
    if hasCov t then
      if isPi then r := { r with coverFn := r.coverFn.push (bname b.name) }
      else r := { r with cover := r.cover.push s!"{bname b.name}@{(depthTo t (·.isAppOf coveredN)).getD 0}:{(floorShape st0 t).getD "—"}" }
      continue
    if isPi && hasHead c ``ScannerState.simpleKeyAllowed && hasHead c ``ScannerState.currentIndent then
      r := { r with larm := r.larm.push (bname b.name) }; continue
    if c.isAppOfArity ``Or 2 && (c.getArg! 0).consumeMData.isAppOfArity ``Eq 3 && ((c.getArg! 0).consumeMData.getArg! 0).consumeMData.isConstOf ``Char then
      let l := (c.getArg! 0).consumeMData
      let rr := (c.getArg! 1).consumeMData
      let rhs2 := if rr.isAppOfArity ``Eq 3 then ppc st (rr.getArg! 2) else "?"
      r := { r with hc := r.hc.push s!"{(if isPi then "→" else "")}{bname b.name}:{ppc st (l.getArg! 2)}|{rhs2}" }; continue
    let parts := if b.name.hasMacroScopes then #[(bname b.name, t)] else conjuncts (bname b.name) t
    -- mentioned inside an option or a disjunction, and not in hand directly
    if hasHead t monoN && !(parts.any fun (_, pt) => (piConcl pt).isAppOf monoN) then r := { r with monoOpt := r.monoOpt.push (bname b.name) }
    if hasHead t baseN && !(parts.any fun (_, pt) => (piConcl pt).isAppOf baseN) then r := { r with baseOpt := r.baseOpt.push (bname b.name) }
    for (pn, pt) in parts do
      -- a fact under an implication is marked: in hand once its premise is
      let nm := (if pt.isForall then "→" else "") ++ pn
      let (st, c) := piConclSt st0 pt
      if c.isAppOf monoN then r := { r with mono := r.mono.push s!"{nm}:{ppc st (c.getArg! 0)}" }; continue
      if c.isAppOf baseN then r := { r with base := r.base.push s!"{nm}:{ppc st (c.getArg! 0)}" }; continue
      if c.isAppOf ifloorN then r := { r with floor := r.floor.push s!"{nm}:{ppc st (c.getArg! 0)}@{ppc st (c.getArg! 1)}" }; continue
      if c.isAppOf ``L4YAML.Proofs.CouplingBridge.ScannerSurfCorr then r := { r with corr := r.corr.push s!"{nm}:{ppc st (c.getArg! 0)}" }; continue
      -- item 258: a relation in hand directly (not under a premise), as printed
      if let some (sym, l, rr) := rel c then
        if !pt.isForall then r := { r with rels := r.rels.push (nm, sym, ppc st l, ppc st rr) }
      match rel c with
      | some ("=", l, rhs) =>
        if c.isAppOfArity ``Eq 3 && (c.getArg! 0).consumeMData.isConstOf ``Char then
          r := { r with chr := r.chr.push s!"{nm}:{ppc st l}={ppc st rhs}" }
        else if l.isAppOf ``scanNextToken_preprocess then
          r := { r with prep := r.prep.push s!"{nm}:{ppc st (l.getArg! 0)}→{digPrep st rhs}" }
        else if l.isAppOf ``scanNextToken_dispatchBlockIndicators && l.getAppNumArgs ≥ 2 then
          r := { r with dispB := r.dispB.push s!"{nm}:{ppc st (l.getArg! 1)}" }
        else if l.isAppOf ``scanNextToken_dispatchContent && l.getAppNumArgs ≥ 2 then
          r := { r with dispC := r.dispC.push s!"{nm}:{ppc st (l.getArg! 1)}" }
        else if (projOf l ``ScannerState.inFlow).isSome && isBoolLit rhs false then
          r := { r with noflow := r.noflow.push nm }
        else if let some s := projOf l ``ScannerState.needIndentCheck then
          if isBoolLit rhs false then r := { r with nic := r.nic.push s!"{nm}:{ppc st s}" }
          else if isBoolLit rhs true then r := { r with armed := r.armed.push s!"{nm}:{ppc st s}" }
        else if (projOf l ``ScannerState.indents).isSome || (projOf rhs ``ScannerState.indents).isSome then
          r := { r with ids := r.ids.push nm }
        else if hasHead l ``ScannerState.simpleKey && hasHead rhs ``ScannerState.col then
          r := { r with save := r.save.push nm }
        else if ((projOf l ``SurfPos.col).isSome && isZeroE rhs) || ((projOf rhs ``SurfPos.col).isSome && isZeroE l) then
          r := { r with col0 := r.col0.push s!"{nm}:{ppc st l}={ppc st rhs}" }
      | some ("≠", l, rhs) =>
        if ((projOf l ``SurfPos.col).isSome && isZeroE rhs) || ((projOf rhs ``SurfPos.col).isSome && isZeroE l) then
          r := { r with col0 := r.col0.push s!"{nm}:{ppc st l}≠{ppc st rhs}" }
      | some (sym, l, rhs) =>
        if let some s := projOf l ``ScannerState.currentIndent then
          if hasHead rhs ``ScannerState.col then r := { r with fl := r.fl.push s!"{nm}:{ppc st s}{sym}col" }
          else r := { r with top := r.top.push s!"{nm}:{ppc st s}{sym}{ppc st rhs}",
                               tops := r.tops.push (nm, ppc st s, sym, ppc st rhs) }
        else if isZeroE l && (projOf rhs ``SurfPos.col).isSome then
          r := { r with col0 := r.col0.push s!"{nm}:0{sym}{ppc st rhs}" }
      | none => pure ()
  return r

def Inputs.render (r : Inputs) : String :=
  let f (k : String) (xs : Array String) := s!"{k}={xs.size}{if xs.isEmpty then "" else "(" ++ String.intercalate "," xs.toList ++ ")"}"
  String.intercalate " " [f "mono" r.mono, f "monoOpt" r.monoOpt, f "base" r.base, f "baseOpt" r.baseOpt, f "prep" r.prep,
    f "dispB" r.dispB, f "dispC" r.dispC, f "hc" r.hc, f "chr" r.chr, f "corr" r.corr, f "noflow" r.noflow, f "save" r.save,
    f "fl" r.fl, f "top" r.top, f "larm" r.larm, f "floor" r.floor, f "nic" r.nic, f "armed" r.armed,
    f "col0" r.col0, f "ids" r.ids, f "cover" r.cover, f "coverFn" r.coverFn]

/-- The verdict: the payment's inputs present or the names missing, and the
    floors a payment here could name. -/
def verdict (r : Inputs) (idx : String) : String := Id.run do
  -- a floor SOURCE bounds the top from above: the dispatch state's floor,
  -- the landed arm, a top bound, or the armed flag `park_col0_floor` spends;
  -- `IndentFloor` bounds it from below and is no source
  let floorSrc := !r.fl.isEmpty || !r.larm.isEmpty || !r.top.isEmpty || !r.armed.isEmpty
  let mut missing : Array String := #[]
  if r.mono.isEmpty then missing := missing.push "mono"
  if r.base.isEmpty then missing := missing.push "base"
  if r.prep.isEmpty then missing := missing.push "prep"
  if r.dispB.isEmpty && r.dispC.isEmpty then missing := missing.push "disp"
  if !floorSrc then missing := missing.push "floorSrc"
  let inputs := if missing.isEmpty then (if r.dispB.isEmpty then "full(dispC)" else "full") else s!"missing({String.intercalate "," missing.toList})"
  let mut lo : Array String := #[]
  if floorSrc then lo := lo.push s!"own={idx}"
  if r.top.any (fun (s : String) => (s.splitOn "<0").length > 1) then lo := lo.push "empty=0"
  for cv in r.cover do
    if let some i := (cv.splitOn ":Floor(")[1]? then lo := lo.push s!"relay={(cv.splitOn "@")[0]!}:Floor({i}"
  return s!"inputs={inputs} lo=[{String.intercalate ";" lo.toList}]{if idx == "0" then " idx0" else ""}"

/-! ## §5 The bound against the index (item 258) -/

/-- The summands of a left-nested `+`, printed: `n + 1 + m` reads `[n, 1, m]`. -/
partial def summands (st : Stack) (e : Expr) : List String :=
  let e := e.consumeMData
  if e.isAppOfArity ``HAdd.hAdd 6 then summands st (e.getArg! 4) ++ [ppc st (e.getArg! 5)]
  else [ppc st e]

def isPosLit (s : String) : Bool := match s.toNat? with | some v => decide (v > 0) | none => false

/-- One top bound `state sym rhs` against the index: the floor
    `IndentStackCover.covered_nil_of_top_le` gives from it (`rhs + 1` under a
    weak bound, `rhs` under a strict one), and where the bound stands —
    `below` the index when the index is the bound plus a positive literal or
    a binder in scope says `rhs < idx`, `at` it when the two print the same
    or a binder equates them, `above` when a binder puts the index at or
    under the bound, `undecided` otherwise.  A strict bound is one below a
    weak one, so it is below the index already where the two print the same. -/
def boundVs (idx : String) (idxSum : List String) (rels : Array (String × String × String × String))
    (sym rhs : String) : String × String × String := Id.run do
  let floor := if sym == "≤" then s!"{rhs} + 1" else rhs
  if idx == rhs then return (floor, if sym == "<" then "below" else "at", "syn")
  if idxSum.head? == some rhs && (idxSum.drop 1).any isPosLit then return (floor, "below", "syn")
  if let some (h, s, l, r) := rels.find? (fun (_, s, l, r) => (s == "<" || (sym == "<" && s == "≤")) && l == rhs && r == idx) then
    return (floor, "below", s!"by {h}:{l}{s}{r}")
  if let some (h, _, l, r) := rels.find? (fun (_, s, l, r) => s == "=" && ((l == rhs && r == idx) || (l == idx && r == rhs))) then
    return (floor, "at", s!"by {h}:{l}={r}")
  if let some (h, s, l, r) := rels.find? (fun (_, s, l, r) => (s == "<" || s == "≤") && l == idx && r == rhs) then
    return (floor, "above", s!"by {h}:{l}{s}{r}")
  return (floor, "undecided", "—")

/-- Where the site stands on its line: `landed` when the landed arm's
    hypothesis or a `.col = 0` fact stands, `inline` when a `.col ≠ 0` or
    `0 < .col` fact does — the datum a bound on an EARLIER state is read
    beside, because at a landed site preprocessing's unwind ran between that
    state and the constructor's. -/
def whereOf (r : Inputs) : String :=
  let landed := !r.larm.isEmpty || r.col0.any fun s => (s.splitOn "=0").length > 1 && (s.splitOn "≠0").length == 1
  let inline := r.col0.any fun s => (s.splitOn "≠0").length > 1 || (s.splitOn ":0<").length > 1
  if landed && inline then "both" else if landed then "landed" else if inline then "inline" else "—"

structure BoundRead where
  line : String
  cls : Array String
  hows : Array String
  own : Array Bool
  payable : Bool
  site : String
  deriving Inhabited

/-- The site's bounds read against its index, and the verdict: `payable`
    when a bound is below the index, `Mono` in hand is about the bound's
    state, and that state is the constructor's or the preprocess and the
    dispatch transport it — item 257's payment term verbatim. -/
def readBounds (r : Inputs) (idx : String) (idxSum : List String) (ctorState : String) : BoundRead := Id.run do
  let monoStates := r.mono.map fun s => ((s.splitOn ":").getLast?).getD ""
  let transport := !r.prep.isEmpty && (!r.dispB.isEmpty || !r.dispC.isEmpty)
  let mut parts : Array String := #[]
  let mut cls : Array String := #[]
  let mut hows : Array String := #[]
  let mut owns : Array Bool := #[]
  let mut payable := false
  for (nm, state, sym, rhs) in r.tops do
    let (floor, c, how) := boundVs idx idxSum r.rels sym rhs
    let own := state == ctorState
    let monoOk := monoStates.contains state
    if c == "below" && monoOk && (own || transport) then payable := true
    let monoS := if monoOk then "yes" else if r.mono.isEmpty then "—" else "no"
    parts := parts.push s!"{nm}:{state}{sym}{rhs} floor={floor} {c}({how}) {if own then "own" else "old"} mono={monoS}"
    cls := cls.push c; hows := hows.push how; owns := owns.push own
  let w := whereOf r
  let verdict :=
    if r.tops.isEmpty then "no-bound"
    else if payable then "payable"
    else if cls.contains "below" then "below-unpayable"
    else if cls.contains "at" then "at-index"
    else if cls.contains "above" then "above-index"
    else "undecided"
  return { line := s!"idx={idx} ctor={ctorState} where={w} bounds=[{String.intercalate "; " parts.toList}] ⊢ {verdict}",
           cls, hows, own := owns, payable, site := w }


/-! ## §6 The callers' inputs, and the step (item 259)

    A site that lacks `Mono`, or a bound on the state its transport starts
    from, cannot pay alone; its price is what its CALLERS hold about the
    state they pass it.  For each such site this section finds every
    application of the enclosing lemma in the environment and reads, in the
    caller's context at the application, the argument passed as the site's
    PRE-DISPATCH state — the state the site's preprocess equation starts from,
    else the one its dispatch is applied to with the directive update
    stripped — whether `Mono` and the base in hand are about it, and every
    top bound on it against the site's index instantiated with the caller's
    arguments.  Beside the site: the cover-library theorem that carries a
    cover across the dispatch the site holds, the shape of its conclusion
    (the opened level marked `existential` where `∃` binds it), the library's
    lemmas whose conclusion names the consed level, and whether the site pins
    its top from both sides — a bound AT the index and `IndentFloor` one
    above it — which is what turns the existential level into the index. -/

/-- The last two components of a name. -/
def last2 (n : Name) : String :=
  match n.components.reverse with
  | a :: b :: _ => s!"{b}.{a}"
  | _ => short n

/-- Every application of `target` in `e`, with the binder stack at it. -/
partial def appsOf (target : Name) (st : Stack) (e : Expr) (acc : Array (Stack × Array Expr)) :
    Array (Stack × Array Expr) :=
  let e := e.consumeMData
  -- an APPLICATION of the target: the bare constant reached by descending an
  -- application's head is not one
  let acc := if e.isApp && e.isAppOf target then acc.push (st, e.getAppArgs) else acc
  match e with
  | .app .. => e.getAppArgs.foldl (fun a x => appsOf target st x a) (appsOf target st e.getAppFn acc)
  | .lam n ty b _ => appsOf target (st.push { name := n, ty := ty, prov := none }) b (appsOf target st ty acc)
  | .forallE n ty b _ => appsOf target (st.push { name := n, ty := ty, prov := none }) b (appsOf target st ty acc)
  | .letE n ty v b _ =>
    appsOf target (st.push { name := n, ty := ty, prov := none }) b (appsOf target st v (appsOf target st ty acc))
  | .proj _ _ b => appsOf target st b acc
  | _ => acc

/-- The parameter a lemma's transport starts from: the state its preprocess
    equation names, else the state its dispatch is applied to (the directive
    update stripped), as (position, how). -/
def preStateParam (ty : Expr) : Option (Nat × String) := Id.run do
  let mut t := ty
  let mut j := 0
  let mut prep : Option Nat := none
  let mut disp : Option Nat := none
  while true do
    match t with
    | .forallE _ bt b _ =>
      match rel (piConcl bt) with
      | some ("=", l, _) =>
        let l := l.consumeMData
        if l.isAppOf ``scanNextToken_preprocess && l.getAppNumArgs ≥ 1 then
          if let .bvar i := (l.getArg! 0).consumeMData then
            if prep.isNone then prep := some (j - 1 - i)
        else if (l.isAppOf ``scanNextToken_dispatchBlockIndicators || l.isAppOf ``scanNextToken_dispatchContent) && l.getAppNumArgs ≥ 2 then
          let y := (l.getArg! 0).consumeMData
          let y := if y.isAppOfArity ``ite 5 then (y.getArg! 4).consumeMData else y
          if let .bvar i := y then
            if disp.isNone then disp := some (j - 1 - i)
      | _ => pure ()
      t := b; j := j + 1
    | _ => break
  match prep, disp with
  | some p, _ => some (p, "prep")
  | none, some d => some (d, "disp")
  | none, none => none

/-- A proposition's shape, for a cover step's conclusion: disjunction,
    existential, conjunction, the back query, the cover. -/
partial def shapeOf (st : Stack) (e : Expr) (fuel : Nat := 12) : String :=
  let e := e.consumeMData
  if fuel == 0 then "…" else
  if e.isAppOfArity ``Or 2 then s!"{shapeOf st (e.getArg! 0) (fuel - 1)} ∨ {shapeOf st (e.getArg! 1) (fuel - 1)}"
  else if e.isAppOfArity ``And 2 then s!"{shapeOf st (e.getArg! 0) (fuel - 1)} ∧ {shapeOf st (e.getArg! 1) (fuel - 1)}"
  else if e.isAppOfArity ``Exists 2 then
    match (e.getArg! 1).consumeMData with
    | .lam n ty b _ => s!"∃{bname n}.{shapeOf (st.push { name := n, ty := ty, prov := none }) b (fuel - 1)}"
    | _ => "∃?"
  else if e.isAppOfArity coveredN 3 then s!"Covered({ppc st (e.getArg! 0)},{ppc st (e.getArg! 1)},{ppc st (e.getArg! 2)})"
  else match rel e with
    | some (sym, l, r) =>
      let l := l.consumeMData
      let lS := if l.isAppOf ``Array.back? && l.getAppNumArgs ≥ 1 then
          let a := (l.getAppArgs.back?.getD l).consumeMData
          if a.isAppOf ``ScannerState.indents then s!"{ppc st (a.getAppArgs.back?.getD a)}.indents.back?" else s!"{ppc st a}.back?"
        else ppc st l
      let r := r.consumeMData
      let rS := if r.isAppOf ``Option.some && r.getAppNumArgs ≥ 1 then
          let v := (r.getAppArgs.back?.getD r).consumeMData
          if v.isAppOf ``IndentEntry.mk && v.getAppNumArgs == 2 then s!"some({ppc st (v.getArg! 0)},{ppc st (v.getArg! 1)})"
          else s!"some({ppc st v})"
        else ppc st r
      s!"{lS}{sym}{rS}"
    | none => ppc st e

/-- The binder types of a Pi type, each under its own prefix. -/
partial def binderTypes (t : Expr) (acc : Array Expr := #[]) : Array Expr :=
  match t.consumeMData with
  | .forallE _ ty b _ => binderTypes b (acc.push ty)
  | _ => acc

/-! ## §6b One hop back, the bottom, and the witness (item 260) -/

/-- The preprocess equation in hand whose target is `arg`: the state it was
    preprocessed FROM, and the hypothesis's name. -/
def backOf (r : Inputs) (arg : String) : Option (String × String) :=
  r.prep.findSome? fun p =>
    match p.splitOn ":" with
    | nm :: rest =>
      match (String.intercalate ":" rest).splitOn "→" with
      | [src, tgt] => if ((tgt.splitOn ",")[0]?).getD "" == arg then some (src, nm) else none
      | _ => none
    | _ => none

def streamN : Name := ``L4YAML.Surface.SLYamlStream

/-- Whether a constant's type opens with a `Nat` binder — a surface production
    that names its level first. -/
def levelFirst (env : Environment) (n : Name) : Bool :=
  match env.find? n with
  | some ci =>
    match ci.type.consumeMData with
    | .forallE _ t _ _ => t.consumeMData.isConstOf ``Nat
    | _ => false
  | none => false

/-- The closures a site holds toward the stream: every hypothesis concluding
    `SLYamlStream`, with the LAST premise that is a surface production naming
    a level — the node the closure closes — as (name, production, level);
    a premise that is no surface production marks the closure guarded (`→`).
    A hypothesis with no such premise closes no node and is not one. -/
def bottomsOf (env : Environment) (stAll : Stack) : Array (String × String × String) := Id.run do
  let mut out : Array (String × String × String) := #[]
  for i in [0:stAll.size] do
    let b := stAll[i]!
    let st0 := stAll.extract 0 i
    let (_, c) := piConclSt st0 b.ty
    unless c.isAppOf streamN && b.ty.consumeMData.isForall do continue
    let mut st := st0
    let mut t := b.ty.consumeMData
    let mut last : Option (String × String) := none
    let mut guarded := false
    let mut fuel := 64
    while fuel > 0 do
      fuel := fuel - 1
      match t with
      | .forallE n ty body _ =>
        let ty' := ty.consumeMData
        match ty'.getAppFn with
        | .const h _ =>
          if (`L4YAML.Surface).isPrefixOf h then
            if ty'.getAppNumArgs ≥ 1 && levelFirst env h then last := some (short h, ppc st (ty'.getArg! 0))
          else if ty'.isApp then guarded := true
        | _ => pure ()
        st := st.push { name := n, ty := ty, prov := none }
        t := body.consumeMData
      | _ => break
    if let some (prod, lvl) := last then
      out := out.push (s!"{if guarded then "→" else ""}{bname b.name}", prod, lvl)
  return out

/-- The field's index witness where its statement binds the index by an
    equation (`eq(n=ne + 1)`): `ne` at the instantiated index, `none` where
    the equation has no solution there, `?` where it is undecided. -/
def witnessOf (eq : String) (idx : String) : String :=
  if eq.isEmpty then "—" else
  let body := ((eq.drop 3).toString.dropEnd 1).toString
  match body.splitOn "=" with
  | [_, r] =>
    if r.endsWith " + 1" then
      match idx.toNat? with
      | some 0 => s!"none({idx}={r})"
      | some v => s!"{v - 1}"
      | none => if idx.endsWith " + 1" then (idx.dropEnd 4).toString else s!"?({idx}={r})"
    else s!"?({idx}={r})"
  | _ => s!"?({body})"

def resumeN : Name := ``L4YAML.Proofs.StreamAccum.ResumeFrames
-- Item 304: the value-line stacks are `KeyFrames` (item 302's); the same faces.
def keyN : Name := ``L4YAML.Proofs.StreamAccum.KeyFrames
def tailN : Name := ``L4YAML.Surface.SCompactMapTail

/-- Inside a hypothesis mentioning `ResumeFrames`: the level of the first
    `SCompactMapTail` premise the resume follows, and what stands before that
    premise — the last surface production naming a level, or `landing` when
    the tail starts at a position already fixed; `frames(ks)` when the
    hypothesis concludes `ResumeFrames` with no tail premise (a frames face,
    resumable at any width in its list). -/
partial def resumeShape (env : Environment) (st : Stack) (t : Expr) (prev : Option String) : Option String :=
  let t := t.consumeMData
  match t with
  | .forallE n ty b _ =>
    let ty' := ty.consumeMData
    if ty'.isAppOfArity tailN 3 then some s!"tail({ppc st (ty'.getArg! 0)})←{prev.getD "landing"}"
    else
      let prev' := match ty'.getAppFn with
        | .const h _ => if (`L4YAML.Surface).isPrefixOf h && ty'.getAppNumArgs ≥ 1 && levelFirst env h then some s!"{short h}({ppc st (ty'.getArg! 0)})" else prev
        | _ => prev
      (resumeShape env st ty prev).orElse fun _ => resumeShape env (st.push { name := n, ty := ty, prov := none }) b prev'
  | .lam n ty b _ => resumeShape env (st.push { name := n, ty := ty, prov := none }) b prev
  | .app .. =>
    if t.isAppOfArity resumeN 3 || t.isAppOfArity keyN 3 then some s!"frames({ppc st (t.getArg! 1)})"
    else t.getAppArgs.findSome? fun a => resumeShape env st a prev
  | _ => none

/-- The relays a stack holds: every binder whose type mentions `ResumeFrames`,
    with its resume shape. -/
def relaysOf (env : Environment) (stAll : Stack) : Array String := Id.run do
  let mut out : Array String := #[]
  for i in [0:stAll.size] do
    let b := stAll[i]!
    unless hasHead b.ty resumeN || hasHead b.ty keyN do continue
    let st0 := stAll.extract 0 i
    out := out.push s!"{bname b.name}:{(resumeShape env st0 b.ty none).getD "?"}"
  return out

/-- The relay sources a payment class names. -/
partial def relaySrcs : Cls → Array String
  | .relay src => #[src]
  | .paid i | .step i | .via _ i | .imp _ i => relaySrcs i
  | .lit _ _ _ i => relaySrcs i
  | .alt _ alts => alts.foldl (fun a x => a ++ relaySrcs x) #[]
  | _ => #[]

/-! ## §2 The pins -/

-- 2026-10-26 (item 370): the sibling `-` arm (`accum_block_on_pendingBlock #1`) relays `h_closeF_old` into
-- `pendingBlock.h_closeF`, so it is no longer a punt SITE: sites 5 → 4; its bounds/caller/bottom rows move to the
-- paid list and the aggregate line follows.
def expectedSites : List String :=
  ["accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeFE idx=n + 1 mono=1(h_mono:sc) monoOpt=0 base=1(h_base:sc) baseOpt=0 prep=1(h_preprocess:sc→s_prep,c) dispB=0 dispC=1(h_dispatch:c) hc=0 chr=0 corr=3(hcorr_prep:s_prep,hcorr_result:s',h_corr:sc) noflow=1(h_flow_disp) save=1(h_sk_s) fl=0 top=0 larm=0 floor=1(h_floor_old:sc@n + 1) nic=2(h_nic_mv:sc,h_nic_s:s') armed=0 col0=1(h_col0_old:0<sp_scan.col) ids=0 cover=4(h_closeF99@2:Floor(n,map(…) :: ks),h_frames99@2:Floor(n,ks),h_closeFV108@2:Floor(n + 1,ks),h_framesV108@2:Floor(n + 1,ks)) coverFn=1(h_cov_step) ⊢ inputs=missing(floorSrc) lo=[relay=h_closeF99:Floor(n,map(…) :: ks);relay=h_frames99:Floor(n,ks);relay=h_closeFV108:Floor(n + 1,ks);relay=h_framesV108:Floor(n + 1,ks)]",
   "content_dispatch_routed #1 ctor:pendingProps.h_closeFE idx=0 mono=0 monoOpt=0 base=0 baseOpt=0 prep=0 dispB=0 dispC=1(h_dispatch:c) hc=1(hprops:'&'|'!') chr=1(h:c='&') corr=3(hcorr_prep:s_prep,hcorr_result:s',hc:s') noflow=1(h_flow_disp) save=0 fl=0 top=0 larm=0 floor=0 nic=3(h_nic_prep:s_prep,h_nic_ad:s_prep*,h_nic_s:s') armed=0 col0=0 ids=0 cover=0 coverFn=1(h_cov_lift) ⊢ inputs=missing(mono,base,prep,floorSrc) lo=[] idx0",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeFE idx=0 mono=0 monoOpt=0 base=0 baseOpt=0 prep=0 dispB=0 dispC=1(h_dispatch:c) hc=1(hprops:'&'|'!') chr=1(h:c='!') corr=3(hcorr_prep:s_prep,hcorr_result:s',hc:s') noflow=1(h_flow_disp) save=0 fl=0 top=0 larm=0 floor=0 nic=3(h_nic_prep:s_prep,h_nic_ad:s_prep*,h_nic_s:s') armed=0 col0=0 ids=0 cover=0 coverFn=1(h_cov_lift) ⊢ inputs=missing(mono,base,prep,floorSrc) lo=[] idx0"]
def expectedShapes : List String :=
  ["pendingBlock.h_closeF bound(ks<n) Floor(n,ks) eq(—)",
   "pendingBlockContent.h_closeF bound(ks<n) Floor(n,ks) eq(—)",
   "pendingMapValue.h_closeF bound(ks<n) Floor(n,map(…) :: ks) eq(—)",
   "pendingProps.h_closeFE bound(ks<ne) Floor(ne,ks) eq(n=ne + 1)"]
def expectedBounds : List String :=
  ["accum_content_on_pendingMapValue_indented #1 idx=n + 1 ctor=s' where=inline bounds=[] ⊢ no-bound",
   "content_dispatch_routed #1 idx=0 ctor=s' where=— bounds=[] ⊢ no-bound",
   "content_dispatch_routed #2 idx=0 ctor=s' where=— bounds=[] ⊢ no-bound"]
def expectedCallers : List String :=
  [-- 2026-10-26 (item 369): the caller now relays the `-` park's `h_closeF_old` cover as well.
   "content_dispatch_routed #1 ← accum_content_on_noPending #1 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=no baseB=no boundsB=[] resumeB=[] ⊢ no-mono-back,no-bound-back",
   "content_dispatch_routed #1 ← accum_content_on_noPending #2 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=no baseB=no boundsB=[] resumeB=[] ⊢ no-mono-back,no-bound-back",
   "content_dispatch_routed #1 ← accum_content_pending #1 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #1 ← accum_content_pending #2 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #1 ← accum_content_pending #3 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #1 ← accum_content_pending #4 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #1 ← accum_content_pending #5 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_defer_split:frames(ks)] ⊢ no-bound-back",
   "content_dispatch_routed #1 ← content_dispatch_after_close #1 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=— monoB=no baseB=no boundsB=[] resumeB=[] ⊢ no-prep-back",
   "content_dispatch_routed #2 ← accum_content_on_noPending #1 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=no baseB=no boundsB=[] resumeB=[] ⊢ no-mono-back,no-bound-back",
   "content_dispatch_routed #2 ← accum_content_on_noPending #2 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=no baseB=no boundsB=[] resumeB=[] ⊢ no-mono-back,no-bound-back",
   "content_dispatch_routed #2 ← accum_content_pending #1 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #2 ← accum_content_pending #2 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #2 ← accum_content_pending #3 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #2 ← accum_content_pending #4 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_fS:frames(ks); h_fV:frames(ks); h_fQ:tail(kk)←landing] ⊢ no-bound-back",
   "content_dispatch_routed #2 ← accum_content_pending #5 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=sc(h_preprocess) monoB=yes(h_mono) baseB=yes(h_base) boundsB=[] resumeB=[h_defer_split:frames(ks)] ⊢ no-bound-back",
   "content_dispatch_routed #2 ← content_dispatch_after_close #1 state=s_prep mono=no base=no bounds=[] idx=0 ⊢ no-mono,no-bound | back=— monoB=no baseB=no boundsB=[] resumeB=[] ⊢ no-prep-back"]
def expectedLack : List String :=
  ["content_dispatch_routed #1 ctor:pendingProps.h_closeFE lacks=[mono,base,prep,floorSrc] idx=0 pre=s_prep(disp) callers=8 supplied=0 suppliedB=0 step=[IndentStackCover.dispatchContent_cover→Covered] shape=Covered consed=none pin=— bottom=at[→h_route:SBlockNode(0) at(syn)] resume=[] ne=none(0=ne + 1) ⊢ vacuous(0=ne + 1)",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeFE lacks=[mono,base,prep,floorSrc] idx=0 pre=s_prep(disp) callers=8 supplied=0 suppliedB=0 step=[IndentStackCover.dispatchContent_cover→Covered] shape=Covered consed=none pin=— bottom=at[→h_route:SBlockNode(0) at(syn)] resume=[] ne=none(0=ne + 1) ⊢ vacuous(0=ne + 1)"]
def expectedBottoms : List String :=
  ["content_dispatch_routed #1 ctor:pendingProps.h_closeFE idx=0 bottom=at[→h_route:SBlockNode(0) at(syn)] resume=[]",
   "content_dispatch_routed #2 ctor:pendingProps.h_closeFE idx=0 bottom=at[→h_route:SBlockNode(0) at(syn)] resume=[]",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_content_on_pendingMapValue_indented #1 ctor:pendingProps.h_closeFE idx=n + 1 bottom=at[h_close_old:SBlockNode(n + 1) at(syn)] resume=[h_kslot:frames(map(…) :: []); h_closeF99:frames(map(…) :: ks); h_frames99:frames(ks); h_closeFV108:frames(ks); h_framesV108:frames(ks); h_seqF168:tail(n)←SBlockNode(n + 1); h_ivl_pack:frames(map(…) :: []); h_compact_vslot:frames(map(…) :: [])]"]
-- 2026-10-20 (item 307): the landed-`-` arm's `pendingBlock.h_closeF` row names the two new resumes
-- (`h_resSeqV`, `h_slotV'`) among its resume haves; nothing else moves.
def expectedBottomsPaid : List String :=
  -- Item 305: `closeThenBlock`'s first entry park reads the `?` slot's bottom (`h_slotV`) beside the awaited node's frames.
  ["accum_block_on_noPending #1 ctor:pendingBlock.h_closeF idx=k bottom=at[h_rootTail:SCompactSeqTail(k) at(syn)] resume=[] relaySrc=[]",
   "colon_open_map #1 ctor:pendingMapValue.h_closeF idx=k bottom=at[h_routeE:SBlockMapEntry(k) at(syn)] resume=[h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k)] relaySrc=[val:colon_open_map.h✝]",
   "compact_open_map #1 ctor:pendingMapValue.h_closeF idx=n + 1 + m bottom=below[h_close_old:SBlockIndented(n) below(syn)] resume=[] relaySrc=[]",
   -- Item 371: the restated value-line pack (`⇒ Resume(map(_)::[])▹Stream`, `ResumeFrames.one`'s level)
   "accum_block_on_closeThenBlock #1 ctor:pendingBlock.h_closeF idx=k bottom=at[h_docRoute:SBlockNode(0) undecided(—); h_seqRoute:SBlockSeqEntries(k) at(syn); h_entryTail:SCompactSeqTail(k) at(syn)] resume=[h_vpack:frames(map(…) :: []); h_vslot:frames(map(…) :: []); h_valF:frames(map(…) :: ks); h_mapF:frames(ks); h_mapFV:frames(ks); h_valFV:frames(ks); h_res_land:tail(k)←landing; h_resV_land:tail(k)←landing; h_seqBottom:frames([]); h_seqFrames:frames(ks); h_slotV:frames(ks); h_resSeqV:frames(ks); h_resKslot:frames(map(…) :: []); h_slotV':frames(ks); h_seqFramesV:frames(ks)] relaySrc=[local:accum_block_on_closeThenBlock.h_seqFrames]",
   "accum_block_on_closeThenBlock #2 ctor:pendingBlock.h_closeF idx=nv + 1 + m bottom=below[hvs:SBlockIndented(nv) below(syn)] resume=[h_vpack:frames(map(…) :: []); h_vslot:frames(map(…) :: []); h_valF:frames(map(…) :: ks); h_mapF:frames(ks); h_mapFV:frames(ks); h_valFV:frames(ks); h✝:frames(map(…) :: []); h✝:frames(map(…) :: []); h✝:frames(map(…) :: []); right✝:frames(map(…) :: []); right✝:frames(map(…) :: []); right✝:frames(map(…) :: []); right✝:frames(map(…) :: []); right✝:frames(map(…) :: []); right✝:frames(map(…) :: []); right✝:frames(map(…) :: []); hkv:frames(map(…) :: []); hkvUp:frames(map(…) :: [])] relaySrc=[]",
   "accum_block_on_pendingBlock #1 ctor:pendingBlock.h_closeF idx=k bottom=at[h_close_entry_old:SCompactSeqTail(n) at(by hkn:k=n); h_cont:SCompactSeqTail(k) at(syn)] resume=[h_kslot:frames(map(…) :: []); h_kslotUp:frames(map(…) :: []); h_closeFV_old:frames(ks); h_closeF_old:frames(ks)] relaySrc=[param:accum_block_on_pendingBlock.h_closeF_old]",
   "accum_block_on_pendingBlock #2 ctor:pendingBlock.h_closeF idx=k bottom=below[h_close_entry_old:SCompactSeqTail(n) below(by hlt:n<k); h_close_inner:SBlockSeqEntries(k) at(syn)] resume=[h_kslot:frames(map(…) :: []); h_kslotUp:frames(map(…) :: []); h_closeFV_old:frames(ks); h_closeF_old:frames(ks)] relaySrc=[]",
   "accum_block_on_pendingBlock #3 ctor:pendingBlock.h_closeF idx=n + 1 + m bottom=below[h_close_entry_old:SCompactSeqTail(n) below(syn); h_close_old:SBlockIndented(n) below(syn)] resume=[h_kslot:frames(map(…) :: []); h_kslotUp:frames(map(…) :: []); h_closeFV_old:frames(ks); h_closeF_old:frames(ks)] relaySrc=[]",
   "accum_block_on_pendingBlockContent #1 ctor:pendingBlock.h_closeF idx=k bottom=at[h_entry_old:SCompactSeqTail(n) at(by hkn:k=n); h_cont:SCompactSeqTail(k) at(syn)] resume=[h_kslot:frames(map(…) :: []); h_kslotUp:frames(map(…) :: []); h_closeF_old:frames(ks); h_closeFV_old:frames(ks)] relaySrc=[param:accum_block_on_pendingBlockContent.h_closeF_old]",
   "accum_content_on_pendingBlock_indented #1 ctor:pendingProps.h_closeFE idx=n + 1 bottom=below[h_close_old:SBlockIndented(n) below(syn); h_close_entry_old:SCompactSeqTail(n) below(syn)] resume=[h_kslot_old:frames(map(…) :: []); h_closeF_old:frames(ks); h_kslotUp_old:frames(map(…) :: []); h_closeFV_old:frames(ks)] relaySrc=[param:accum_content_on_pendingBlock_indented.h_closeF_old]",
   "accum_content_pending #1 ctor:pendingProps.h_closeFE idx=n bottom=at[→h_route,→h_route_new:SBlockNode(n) at(syn)] resume=[h_defer_split:frames(ks); h_kslot_p:frames(map(…) :: []); h_kslotE_p:frames(map(…) :: []); h_closeFE_p:frames(ks); h_closeFS_p:frames(ks); h_closeFVS_p:frames(ks); h_closeFEV_p:frames(ks)] relaySrc=[door:pendingProps.h_closeFE]",
   "accum_content_pending #2 ctor:pendingProps.h_closeFE idx=n bottom=at[→h_route,→h_route_new:SBlockNode(n) at(syn)] resume=[h_defer_split:frames(ks); h_kslot_p:frames(map(…) :: []); h_kslotE_p:frames(map(…) :: []); h_closeFE_p:frames(ks); h_closeFS_p:frames(ks); h_closeFVS_p:frames(ks); h_closeFEV_p:frames(ks)] relaySrc=[door:pendingProps.h_closeFE]",
   "colon_open_map_explicit #1 ctor:pendingMapValue.h_closeF idx=nv bottom=at[h_slot:SBlockIndented(nv) at(syn)] resume=[hvp:frames(map(…) :: [])] relaySrc=[]",
   "colon_open_map_implicit #1 ctor:pendingMapValue.h_closeF idx=k bottom=at[h_route:SBlockMapEntry(k) at(syn)] resume=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_routeS:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] relaySrc=[param:colon_open_map_implicit.h_routeF]",
   "colon_open_map_props #1 ctor:pendingMapValue.h_closeF idx=k bottom=at[h_route:SBlockMapEntry(k) at(syn)] resume=[h_routeF:tail(k)←SBlockMapEntry(k); h_routeFV:tail(k)←SBlockMapEntry(k); h_kslotD:tail(k)←SBlockMapEntry(k)] relaySrc=[param:colon_open_map_props.h_routeF]",
   "question_open_map #1 ctor:pendingMapValue.h_closeF idx=k bottom=at[h_route51:SBlockMapEntry(k) at(syn); h_route51F:SCompactMapTail(k) at(syn)] resume=[h_res_land:tail(k)←landing; h_explUp_chain:frames(map(…) :: []); h_resV_land:tail(k)←landing; h_explUp_chainD:frames(map(…) :: []); h✝:tail(k)←SBlockMapEntry(k); right✝:tail(k)←SBlockMapEntry(k); h_routeF:tail(k)←SBlockMapEntry(k); h_upAll:frames(map(…) :: [])] relaySrc=[val:question_open_map.h✝]"]
-- 2026-10-23 (item 349): `nodes` 105448 → 105463 — `h_dead` threaded through the content step.
def expectedNamed : String :=
  "named=[CoverStep.cons_of_top_eq,Covered.cons,Covered.dedup_head,Covered.pop_to,IndentStackCover.covered_singleton_of_top_le,IndentStackCover.pushMappingIndent_cover,IndentStackCover.scanValuePrepare_cover_key,IndentStackCover.scanValue_cover_key]"
/-- **The cover's own line.**  `nodes` is the proof-term size of the walked
    declarations and it is the one reading item 272 moves, for the reason
    `CloseStackCover` records: the under-run disjunct gains a component the
    three arms destructure and none yet reads, so the terms grow and no punt,
    no bottom and no payability changes.
    Lean v4.35.0 moves it again and alone: `nodes` 96158 → 96125, every other
    field byte-identical — 33 fewer term nodes for the same walk.
    Item 284 moves `rows` 169 → 167 and `nodes` 96125 → 97863 for the reasons
    `CloseStackCover` records: the `pendingFlow` arm's builder call and its two
    `punt` rows are gone, and the walked terms grow by the item's field payments
    and gate parameters; no punt, bottom or payability changes.
    Item 285 moves `nodes` alone, 97863 → 98193, for `CloseStackCover`'s reason:
    the walked arm lemma gains `slot_ride`'s frame and its three spends.  Item
    287 moves it alone again, 98193 → 98962, for the same reason, item 288
    98962 → 99100, item 289 99100 → 99114 (`CloseStackCover` names both
    terms), item 293 99114 → 100079 (`CloseStackCover` names it by
    declaration), item 295 100079 → 100098 (all of it
    `accum_flow_open_depth0`'s, the one declaration whose term changed), and
    item 296 100098 → 100108 (the two entry pack producers' frameless dedent
    exit), item 297 100108 → 100103 (the net over the declarations whose
    terms changed; `CloseStackCover` names them), and item 299 100103 → 100339
    (`pendingDocStart`'s new field and `dispatch_refutes_sameLine`'s new
    premise, passed at every walked site; `CloseStackCover` names them), and
    item 300 100339 → 100885 (the marker reason's productions and refutations;
    `CloseStackCover` names them). -/
-- 2026-10-20 (item 305): the sequence fields carry the width bound and `closeThenBlock`'s first entry park reads the `?` slot's bottom: `nodes` 100885 → 101410.
-- 2026-10-20 (item 306): the content lemma's six key-pack stack arguments are matches on `h_closeFV_old` (the same walk as CloseStackCover): `nodes` 101410 → 101421.
-- 2026-10-20 (item 307): `nodes` 101421 → 101427 (the same walk as CloseStackCover).
-- 2026-10-20 (item 309): `nodes` 101427 → 101432 (CloseStackCover's walk, the generic helpers' `Or.inr h` terms).
-- 2026-10-21 (item 311): `nodes` 101432 → 101924 (CloseStackCover's walk: the named alternative's definitions and stubs, the
-- four frame-crossing conversions, the two `.imp id PackAlt.ofGateClose` wrappers at the closes).
-- 2026-10-21 (item 313): `nodes` 101924 → 103174 — `ExplicitValueRefused.step_content`, `PackAlt.step_content` and the
-- content lane's twenty-one `.imp id (PackAlt.step_content …)` wrappers; every row stands.
-- 2026-10-21 (item 314): `nodes` 103174 → 103286 — `ExplicitValueRefused.step_dispatch`, `PackAlt.step_dispatch` and the
-- content lane's sixty-one leaf payments (each `Or.inr trivial` an application or a hypothesis now); every row stands.
-- 2026-10-21 (item 315): `nodes` 103286 → 103289 — the key-pack lemmas' six arms step through the wrapper (three a side).
-- 2026-10-21 (item 320): `nodes` 103289 → 103324 — the marker parks' new field at the three producers, the eight
-- `PackAlt.ofRefused h_noek…` payments, the `h_seqFramesV` relay and the two split arms grow the family's terms; rows stand.
-- 2026-10-21 (item 322): `nodes` 103324 → 103328 — the colon openers' step premise and its six spends and two
-- callers grow the family's terms; rows stand.
-- 2026-10-21 (item 324): `nodes` 103328 → 103335 — as `CloseStackCover`: this item's payments in the flow opener and the
-- resume context grow the walked terms; every row stands.
-- 2026-10-23 (item 344): `nodes` 104597 → 104913 — the four block-park relays' terms.
-- 2026-10-23 (item 345): nodes 104913 → 105448 — the content-park twin/`h_kslotUp` relays.
-- 2026-10-24 (item 350): nodes 105463 → 105571 — the `:` producers' `NotQuestionPark` payments and the
-- consumers' empty-chain terms; no other column moved.
-- 2026-10-23 (item 345): nodes 105571 → 105560
-- 2026-10-24 (B3 [66] col-0 threading): follows CloseLandingWidth — the content/block parks close from `sp_gram` (run + gate).
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the #98/#100 base.
-- 2026-10-25 (#99 review): nodes=115233 → nodes=115369 — the dead `FlowLead` + two lemmas deleted; `leadFree`/`closeFree` are `Bool` (walked-term total).
-- 2026-10-26 (item 367, `[82]`): module-wide tallies only (the two directive sites apply `scannedDirective_toSL`; three `s-l-comments` lemmas join StreamAccum): nodes 117899 → 117863; the five punt sites and their cover reading are unchanged.
-- 2026-10-26 (item 369): coverBinders=5 → coverBinders=6, relayEntries=5 → relayEntries=6, rows=198 → rows=199, nodes=117863 → nodes=117865 — `pendingBlock.h_closeF` kept into `accum_block_on_pendingBlock.h_closeF_old` and relayed to its cover sites.
-- 2026-10-28 (item 385): rows 204 → 206, nodes 120362 → 120403
-- 2026-10-28 (item 386): nodes 120403 → 121047 (the level conjunct, `h_lvl_old`, the helpers' sibling/absurd terms); no row moved.
-- — the two `deeperLandingResume` relay rows of `h_valF` (CloseStackCover 204 → 206) read here too.
-- 2026-10-29 (item 387): nodes 121047 → 121051 — `accum_block_on_pendingBlock`'s no-pop arm
-- splits `n < k` (helper) from `k = n` (sequence top refuted / mapping sibling declined).
-- 2026-10-29 (item 388): nodes 121051 → 121397 — the landed birth's `nv ≤ k` arm and the `.blockOut` wraps; no row moved.
-- 2026-10-29 (item 389): nodes 121397 → 122297 — proof-term size only (the `-` park births' relays and refutations); no punt-cover input moved.
-- 2026-10-29 (item 394, option B): valueF's cover supplied at the mapping arm from pendingMapValue.h_closeF
-- (Covered.of_subset over preprocess_indents_subset) and spent at both flow closes.
def expectedLine : String :=
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); nodes 117690 → 117529 (walked-term total).
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`); the three `match h_kslot_* with` blocks go — nodes 117529 → 117431 (walked-term total).
  -- 2026-10-26 (item 365): nodes 117848 → 117885 (`StreamAccum` AST size: the `h_refused` decisions and the eleven
  -- `h_alt := h_refused.elim …` arguments); no punt-cover row moved.
  -- 2026-10-26 (item 366): nodes 117885 → 117899 — the two `Classical.em` pays of `h_outer` in
  -- `accum_block_on_closeThenBlock`; no row of this guard moved.
-- Item 371 (sites=4 → 3, pmv=1 → 0, dispB=1 → 0, corr=4 → 3, noflow=4 → 3, top=1 → 0, floor=2 → 1, nic=4 → 3, col0=2 → 1, missMono=3 → 2, missBase=3 → 2, missPrep=3 → 2, own=1 → 0, bounds=1 → 0, at=1 → 0, atSyn=1 → 0, bOwn=1 → 0, lack=3 → 2, lackCallers=19 → 16, lackSuppliedB=3 → 0, paidRows=15 → 16, nodes=117865 → 119846): the value-line packs end in the one-level
-- `ResumeFrames`; `question_open_map`'s `h_expl`/`h_closeFV`/`h_framesV` come from the bound tail route `h_route51F`.
-- Item 372 (2026-10-27): exit (a)'s sequence-top face (`SeqTopKey`) reads at the dedent key's punt.
-- Item 374: rows=200 → 202, nodes=119962 → 120158 — `resumectx_of_landing` gains `h_base`, read at the props park's relay.
  -- 2026-10-29 (item 394): the term grew with `FlowBaseRoutes.valueF`'s supply and relays (nodes 122297 → 122509); no punt-cover row moved.
  "sites=3 pb=0 pmv=0 props=3 idx0=2 mono=1 monoOpt=0 base=1 baseOpt=0 prep=1 dispB=0 dispC=3 hc=2 chr=2 dash=0 corr=3 noflow=3 save=1 fl=0 top=0 larm=0 floor=1 nic=3 armed=0 col0=1 ids=0 coverSites=1 coverBinders=4 coverFnSites=3 full=0 fullB=0 missMono=2 missBase=2 missPrep=2 missFloorSrc=3 own=0 empty=0 relay=1 relayEntries=4 bounds=0 below=0 belowSyn=0 belowArm=0 at=0 atSyn=0 atArm=0 undecided=0 bOwn=0 bOld=0 landedBelow=0 inlineBelow=0 payable=0 lack=2 lackCallers=16 lackSupplied=0 lackSuppliedB=0 lackLow=0 lackPayable=0 vacuous=2 bottomBelow=0 paidRows=16 bottomPaidBelow=5 bottomPaidRelay=9 named=8 rows=206 nodes=123416"

/-! ## §3 The reading -/

set_option maxHeartbeats 20000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  -- item 253's candidates, rebuilt the same way
  let some (.inductInfo iv) := env.find? ``PendingNode | throwError "PendingNode: not an inductive"
  let mut cd : Cand := {}
  for c in iv.ctors do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut fields : Array (Nat × Name × List CloseStackCover.Step) := #[]
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
    if !fields.isEmpty then cd := { cd with ctorFields := cd.ctorFields.insert c fields }
  cd := { cd with consts := cd.consts.insert ``PendingNode.casesOn }
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML || n == ``PendingNode then continue
    match ci with
    | .inductInfo ivv =>
      if ivv.ctors.any (fun c => match env.find? c with | some cc => hasCov cc.type | none => false) then
        cd := { cd with coverTypes := cd.coverTypes.insert n }
    | .defnInfo dv =>
      if (piConcl dv.type).isSort && hasCov dv.value then
        cd := { cd with coverTypes := cd.coverTypes.insert n }
    | _ => pure ()
  let coverMod := `L4YAML.Proofs.Scanner.IndentStackCover
  let mut thms : Array Name := #[]
  for (n, ci) in env.constants.toList do
    if n.getRoot != `L4YAML then continue
    match ci with
    | .thmInfo _ =>
      thms := thms.push n
      let mut ty := ci.type
      let mut i := 0
      let mut ps : Array (Nat × Name × List CloseStackCover.Step) := #[]
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
      let inCoverMod := (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod
      -- item 259: a cover TYPE (`CoverStep`) concluded in the cover module is a
      -- transport too — the step across a `?`/`:` dispatch concludes it
      let transport := (piConcl ci.type).isAppOf coveredN || (inCoverMod && hasCovT cd.coverTypes (piConcl ci.type))
      if !ps.isEmpty && !transport then
        cd := { cd with lemParams := cd.lemParams.insert n ps, consts := cd.consts.insert n }
    | _ => pure ()
  for (l, p) in [(``indicator_open_map, `h_stream_land), (``colon_open_map_explicit, `h_stream_mid),
      (``block_dispatch_deferred_stamp_offcol, `h_stream), (``block_dispatch_deferred_stamp_nopack, `h_stream)] do
    let some ci := env.find? l | throwError "{l}: missing"
    let some idx := ci.type.getForallBinderNames.toArray.findIdx? (· == p) | throwError "{l}.{p}: missing"
    cd := { cd with funnels := cd.funnels.insert l (idx, p), consts := cd.consts.insert l }
  cd := { cd with parks := ({} : Std.HashSet Name).insert ``accum_block_on_pendingBlock |>.insert ``accum_block_on_pendingBlockContent }
  -- item 253's walk, unchanged
  let st ← IO.mkRef ({} : CloseStackCover.S)
  for n in sorted thms do
    if (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod then continue
    walkTheorem st cd n
  let w ← st.get
  let rowLines := w.rows.map fun r => s!"  {short r.lem} #{r.occ} {r.target} := {r.cls.render}"
  let check (name : String) (gotL : Array String) (exp : List String) : MetaM Unit := do
    let gotL := gotL.map (·.trimAscii.toString)
    let missingL := exp.filter fun e => !gotL.contains e
    let extraL := gotL.filter fun g => !exp.contains g
    unless missingL.isEmpty && extraL.isEmpty && gotL.size == exp.length do
      throwError "{name}: pinned {exp.length}, got {gotL.size}; missing {missingL}; extra {extraL.toList}"
  check "item 253's rows (CloseStackCover.expectedRows)" rowLines Tests.Guards.CloseStackCover.expectedRows
  -- §1 the eleven
  let punts := w.rows.filter fun r => r.kind == "ctor" && targets.contains r.target && r.cls.isPunt
  let idxOf (r : CloseStackCover.Row) : MetaM (String × List String) := do
    let ctorShort := ((r.target.drop 5).toString.splitOn ".")[0]!
    let some c := cd.ctorNames.find? (fun c => short c == ctorShort) | throwError "{r.target}: no constructor"
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut i := 0
    let mut idx : Option Nat := none
    while idx.isNone do
      match ty with
      | .forallE _ t b _ =>
        if i ≥ cv.numParams && t.consumeMData.isConstOf ``Nat then idx := some i
        ty := b; i := i + 1
      | _ => break
    let some j := idx | throwError "{c}: no Nat field"
    unless j < r.args.size do throwError "{c}: {r.args.size} args"
    return (ppc r.st r.args[j]!, summands r.st r.args[j]!)
  let mut siteLines : Array String := #[]
  let mut sites : Array (CloseStackCover.Row × String × Inputs) := #[]
  -- §5: the bound against the index, read beside each site
  let mut boundLines : Array String := #[]
  let mut reads : Array BoundRead := #[]
  for r in punts do
    let (idx, idxSum) ← idxOf r
    let ins := inputsAt r.st
    unless r.args.size > 0 do throwError "{r.target}: no constructor arguments"
    let br := readBounds ins idx idxSum (ppc r.st r.args[0]!)
    sites := sites.push (r, idx, ins)
    reads := reads.push br
    siteLines := siteLines.push s!"  {short r.lem} #{r.occ} {r.target} idx={idx} {ins.render} ⊢ {verdict ins idx}"
    boundLines := boundLines.push s!"  {short r.lem} #{r.occ} {br.line}"
  -- §4 the shapes
  let mut shapeLines : Array String := #[]
  -- item 260: the floor and equation shapes per target, for the head and the witness
  let mut shapeMap : Array (String × String × String) := #[]
  for (c, f) in shapeTargets do
    let some (.ctorInfo cv) := env.find? c | throwError "{c}: not a constructor"
    let mut ty := cv.type
    let mut stk : Stack := #[]
    let mut found : Option String := none
    while found.isNone do
      match ty with
      | .forallE n t b _ =>
        if n == f then
          found := some s!"  {short c}.{f} {(boundShape stk t).getD "bound(—)"} {(floorShape stk t).getD "Floor(—)"} {(eqShape stk t).getD "eq(—)"}"
          shapeMap := shapeMap.push (s!"ctor:{short c}.{f}", (floorShape stk t).getD "", (eqShape stk t).getD "")
        stk := stk.push { name := n, ty := t, prov := none }
        ty := b
      | _ => break
    let some l := found | throwError "{c}.{f}: no such field"
    shapeLines := shapeLines.push l
  -- §6 the callers of each site lacking `Mono`, and the step; §6b (item 260)
  -- the same callers one hop back, the bottom and the witness
  let coverThms : Array (Name × ConstantInfo) := (env.constants.toList.filter fun (n, ci) =>
    ci matches .thmInfo _ && (env.getModuleIdxFor? n).map (env.header.moduleNames[·.toNat]!) == some coverMod).toArray
  let namedLemmas := (coverThms.filter fun (_, ci) =>
      let c := piConcl ci.type
      c.isAppOfArity coveredN 3 && (c.getArg! 1).consumeMData.isAppOf ``List.cons).map (fun (n, _) => last2 n) |>.qsort (· < ·)
  let namedS := s!"named=[{String.intercalate "," namedLemmas.toList}]"
  let fmtNs (xs : Array String) : String :=
    if xs.isEmpty then "no" else "yes(" ++ String.intercalate "," (xs.map fun s => (s.splitOn ":")[0]!).toList ++ ")"
  let mut callerLines : Array String := #[]
  let mut lackLines : Array String := #[]
  let mut lackN := 0
  let mut lackCallers := 0
  let mut lackSupplied := 0
  let mut lackPayable := 0
  -- item 260: the callers supplying one hop back, the lower floors among them,
  -- the vacuous fields, and the bottom read at every site
  let mut lackSuppliedB := 0
  let mut lackLow := 0
  let mut vacN := 0
  let bottomRead (st : Stack) (idx : String) (idxSum : List String) (rels : Array (String × String × String × String)) : String × String := Id.run do
    let mut parts : Array (Array String × String × String) := #[]
    for (nm, prod, x) in bottomsOf env st do
      let (_, c, how) := boundVs idx idxSum rels "≤" x
      let key := s!"{prod}({x}) {c}({how})"
      match parts.findIdx? (fun (_, k, _) => k == key) with
      | some i => parts := parts.modify i fun (nms, k, c) => (nms.push nm, k, c)
      | none => parts := parts.push (#[nm], key, c)
    let best := if parts.any (·.2.2 == "below") then "below" else if parts.any (·.2.2 == "at") then "at"
      else if parts.isEmpty then "none" else "undecided"
    let txt := String.intercalate "; " (parts.map fun (nms, k, _) => s!"{String.intercalate "," nms.toList}:{k}").toList
    return (s!"{best}[{txt}]", best)
  for (r, idx, ins) in sites do
    let v := verdict ins idx
    unless (v.splitOn "missing(mono").length > 1 do continue
    lackN := lackN + 1
    let some ci := env.find? r.lem | throwError "{r.lem}: missing"
    let some (pos, how) := preStateParam ci.type | throwError "{short r.lem}: no pre-dispatch state parameter"
    let names := ci.type.getForallBinderNames.toArray.map bname
    let (_, idxSum) ← idxOf r
    let ctorState := ppc r.st r.args[0]!
    let missingS := ((v.splitOn "missing(")[1]!.splitOn ")")[0]!
    -- item 260: the field's shape (a HEADED list `n :: ks` takes an own-floor
    -- payment; a headless one needs a floor below) and whether the site holds
    -- its own top AT the index on the constructor's state
    let (fShape, eqS) := ((shapeMap.find? (·.1 == r.target)).map fun (_, f, e) => (f, e)).getD ("", "")
    let headed := (fShape.splitOn "::").length > 1
    let pinnedTop := ins.tops.any fun (_, state, sym, rhs) => state == ctorState && sym == "≤" && rhs == idx
    let mut supB := 0
    let mut lowN := 0
    -- the callers
    let mut k := 0
    let mut sup := 0
    for n in sorted thms do
      if n == r.lem then continue
      let some (.thmInfo ti) := env.find? n | continue
      unless ti.value.foldConsts false (fun c a => a || c == r.lem) do continue
      let mut occ := 0
      for (st, args) in appsOf r.lem #[] ti.value #[] do
        occ := occ + 1
        k := k + 1
        let argS := if pos < args.size then ppc st args[pos]! else "?"
        let cins := inputsAt st
        let about (s : String) : Bool := ((s.splitOn ":").getLast?).getD "" == argS
        let monoNs := cins.mono.filter about
        let baseNs := cins.base.filter about
        let instSum := idxSum.map fun x => match names.findIdx? (· == x) with
          | some p => if p < args.size then ppc st args[p]! else x
          | none => x
        let instIdx := String.intercalate " + " instSum
        let mut bparts : Array String := #[]
        let mut below := false
        for (nm, state, sym, rhs) in cins.tops do
          if state != argS then continue
          let (floor, c, bhow) := boundVs instIdx instSum cins.rels sym rhs
          if c == "below" then below := true
          bparts := bparts.push s!"{nm}:{state}{sym}{rhs} floor={floor} {c}({bhow})"
        let ok := !monoNs.isEmpty && below
        if ok then sup := sup + 1
        let vc := if ok then "supplied" else String.intercalate "," (
          (if monoNs.isEmpty then ["no-mono"] else []) ++
          (if bparts.isEmpty then ["no-bound"] else if !below then ["no-below"] else []))
        -- item 260: the same reading ONE HOP BACK, through the caller's own
        -- preprocess equation whose target is the argument: `own` when `Mono`
        -- (and, under a block-indicator dispatch, the base) is about the source
        -- state, the field's list is headed and the site holds its own top at
        -- the index — the own-floor payment through `Mono` at the constructor
        -- state; `low=` beside it when a bound below the index is in hand
        let mut backS := "—"
        let mut haveBack := false
        let mut monoB : Array String := #[]
        let mut baseB : Array String := #[]
        let mut bpartsB : Array String := #[]
        let mut lowB : Option String := none
        if let some (src, hn) := backOf cins argS then
          haveBack := true
          backS := s!"{src}({hn})"
          let aboutB (s : String) : Bool := ((s.splitOn ":").getLast?).getD "" == src
          monoB := cins.mono.filter aboutB
          baseB := cins.base.filter aboutB
          for (nm, state, sym, rhs) in cins.tops do
            if state != src then continue
            let (floor, c, bhow) := boundVs instIdx instSum cins.rels sym rhs
            if c == "below" && lowB.isNone then lowB := some floor
            bpartsB := bpartsB.push s!"{nm}:{state}{sym}{rhs} floor={floor} {c}({bhow})"
        let ownOk := haveBack && !monoB.isEmpty && (ins.dispB.isEmpty || !baseB.isEmpty) && headed && pinnedTop
        let lowOk := haveBack && !monoB.isEmpty && lowB.isSome
        if ownOk || lowOk then supB := supB + 1
        if lowOk then lowN := lowN + 1
        let vb := if ownOk || lowOk then
            String.intercalate "," ((if ownOk then ["own"] else []) ++ (match lowB with | some f => [s!"low={f}"] | none => []))
          else String.intercalate "," (
            (if !haveBack then ["no-prep-back"] else []) ++
            (if haveBack && monoB.isEmpty then ["no-mono-back"] else []) ++
            (if haveBack && !ins.dispB.isEmpty && baseB.isEmpty then ["no-base-back"] else []) ++
            (if haveBack && bpartsB.isEmpty then ["no-bound-back"] else if haveBack && lowB.isNone then ["no-below-back"] else []))
        let relaysB := relaysOf env st
        callerLines := callerLines.push s!"  {short r.lem} #{r.occ} ← {short n} #{occ} state={argS} mono={fmtNs monoNs} base={fmtNs baseNs} bounds=[{String.intercalate "; " bparts.toList}] idx={instIdx} ⊢ {vc} | back={backS} monoB={fmtNs monoB} baseB={fmtNs baseB} boundsB=[{String.intercalate "; " bpartsB.toList}] resumeB=[{String.intercalate "; " relaysB.toList}] ⊢ {vb}"
    lackCallers := lackCallers + k
    lackSupplied := lackSupplied + sup
    lackSuppliedB := lackSuppliedB + supB
    lackLow := lackLow + lowN
    -- the step the library holds for the site's dispatch
    let fnN := if !ins.dispB.isEmpty then ``scanNextToken_dispatchBlockIndicators else ``scanNextToken_dispatchContent
    let steps := (coverThms.filter fun (_, ci) =>
      let bs := binderTypes ci.type
      (bs.any fun t => match rel (piConcl t) with | some ("=", l, _) => l.consumeMData.isAppOf fnN | _ => false) &&
        bs.any hasCov).map (fun (n, ci) => (n, piConcl ci.type)) |>.qsort (fun a b => a.1.toString < b.1.toString)
    let stepS := String.intercalate "," (steps.map fun (n, c) => s!"{last2 n}→{match c.getAppFn with | .const h _ => short h | _ => "?"}").toList
    let shapeS := match steps[0]? with
      | some (_, c) =>
        match c.getAppFn with
        | .const h _ =>
          if h == coveredN then "Covered" else
          match env.find? h with
          | some (.defnInfo dv) =>
            -- the definition's body under its own binders
            let rec peel (st : Stack) (e : Expr) : Stack × Expr := match e.consumeMData with
              | .lam n ty b _ => peel (st.push { name := n, ty := ty, prov := none }) b
              | e => (st, e)
            let (st, body) := peel #[] dv.value
            shapeOf st body
          | _ => short h
        | _ => "?"
      | none => "—"
    let consed := if (shapeS.splitOn "∃").length > 1 then "existential" else if (shapeS.splitOn "::").length > 1 then "named" else "none"
    -- the pin: the top from both sides, on the constructor's own state
    let topAt := ins.tops.filter fun (_, state, sym, rhs) => state == ctorState && sym == "≤" && rhs == idx
    let floorAbove := ins.floor.filter fun f => ((f.splitOn ":")[1]?).getD "" == s!"{ctorState}@{idx} + 1"
    let nm (xs : Array String) := String.intercalate "," (xs.map fun s => (s.splitOn ":")[0]!).toList
    let pinS := if !topAt.isEmpty && !floorAbove.isEmpty then s!"top∧floor({nm (topAt.map (·.1))},{nm floorAbove})"
      else if !topAt.isEmpty then s!"top({nm (topAt.map (·.1))})"
      else if !floorAbove.isEmpty then s!"floor({nm floorAbove})" else "—"
    let pinned := !topAt.isEmpty && !floorAbove.isEmpty
    -- item 260: the bottom the field's resume needs — a closure over a node
    -- BELOW the opened level, so the level's tail sits inside it — and the
    -- field's index witness; a field with no witness at the site is vacuous
    -- there, and no caller can fund it
    let (bottomS, bottomC) := bottomRead r.st idx idxSum ins.rels
    let neS := witnessOf eqS idx
    let vac := neS.startsWith "none"
    if vac then vacN := vacN + 1
    let relays := relaysOf env r.st
    let bottomOk := bottomC == "below" || !relays.isEmpty
    let payable := !vac && k > 0 && (sup == k || supB == k) && !steps.isEmpty && pinned && bottomOk
    if payable then lackPayable := lackPayable + 1
    let vs := if vac then s!"vacuous({((neS.drop 5).toString.dropEnd 1).toString})" else if payable then "payable-through-callers" else String.intercalate "," (
      (if k == 0 then ["no-caller"] else if sup < k && supB < k then ["callers-short"] else []) ++
      (if steps.isEmpty then ["no-step"] else []) ++ (if !pinned then ["no-pin"] else []) ++
      (if bottomOk then [] else [s!"bottom-{bottomC},no-relay"]))
    lackLines := lackLines.push s!"  {short r.lem} #{r.occ} {r.target} lacks=[{missingS}] idx={idx} pre={names[pos]?.getD "?"}({how}) callers={k} supplied={sup} suppliedB={supB} step=[{stepS}] shape={shapeS} consed={consed} pin={pinS} bottom={bottomS} resume=[{String.intercalate "; " relays.toList}] ne={neS} ⊢ {vs}"
  -- item 260: the closure toward the stream at every site, the two paid-input
  -- sites as the reading's controls
  let mut bottomLines : Array String := #[]
  let mut bottomBelowN := 0
  for (r, idx, ins) in sites do
    let (_, idxSum) ← idxOf r
    let (bottomS, bottomC) := bottomRead r.st idx idxSum ins.rels
    if bottomC == "below" then bottomBelowN := bottomBelowN + 1
    bottomLines := bottomLines.push s!"  {short r.lem} #{r.occ} {r.target} idx={idx} bottom={bottomS} resume=[{String.intercalate "; " (relaysOf env r.st).toList}]"
  -- item 260: the same reading at the PAID positions of the three fields — the
  -- control: what a producer that pays holds toward the stream
  let paidRows := w.rows.filter fun r => r.kind == "ctor" && targets.contains r.target && !r.cls.isPunt
  let mut bottomPaidLines : Array String := #[]
  let mut bottomPaidBelowN := 0
  let mut bottomPaidRelayN := 0
  for r in paidRows do
    let (idx, idxSum) ← idxOf r
    let ins := inputsAt r.st
    let (bottomS, bottomC) := bottomRead r.st idx idxSum ins.rels
    if bottomC == "below" then bottomPaidBelowN := bottomPaidBelowN + 1
    let srcs := relaySrcs r.cls
    if bottomC != "below" && !srcs.isEmpty then bottomPaidRelayN := bottomPaidRelayN + 1
    bottomPaidLines := bottomPaidLines.push s!"  {short r.lem} #{r.occ} {r.target} idx={idx} bottom={bottomS} resume=[{String.intercalate "; " (relaysOf env r.st).toList}] relaySrc=[{String.intercalate "," srcs.toList}]"
  let lackCounts := s!"lack={lackN} lackCallers={lackCallers} lackSupplied={lackSupplied} lackSuppliedB={lackSuppliedB} lackLow={lackLow} lackPayable={lackPayable} vacuous={vacN} bottomBelow={bottomBelowN} paidRows={paidRows.size} bottomPaidBelow={bottomPaidBelowN} bottomPaidRelay={bottomPaidRelayN} named={namedLemmas.size}"
  -- the counts
  let n (p : Inputs → Array String) := (sites.filter fun (_, _, i) => !(p i).isEmpty).size
  let vs := sites.map fun (_, idx, i) => verdict i idx
  let cnt (s : String) := (vs.filter fun v => (v.splitOn s).length > 1).size
  let byT (t : String) := (sites.filter fun (r, _, _) => r.target == t).size
  -- §5's counts: sites, each counted once
  let nb (p : BoundRead → Bool) := (reads.filter p).size
  let has (c : String) (b : BoundRead) := b.cls.contains c
  let hasHow (c : String) (syn : Bool) (b : BoundRead) := (b.cls.zip b.hows).any fun (x, h) => x == c && (h == "syn") == syn
  let boundCounts := s!"bounds={nb (!·.cls.isEmpty)} below={nb (has "below")} belowSyn={nb (hasHow "below" true)} belowArm={nb (hasHow "below" false)} \
at={nb (has "at")} atSyn={nb (hasHow "at" true)} atArm={nb (hasHow "at" false)} undecided={nb fun b => !b.cls.isEmpty && !has "below" b && !has "at" b && !has "above" b} \
bOwn={nb (·.own.contains true)} bOld={nb (·.own.contains false)} landedBelow={nb fun b => has "below" b && b.site == "landed"} inlineBelow={nb fun b => has "below" b && b.site == "inline"} payable={nb (·.payable)}"
  let got := s!"sites={sites.size} pb={byT "ctor:pendingBlock.h_closeF"} pmv={byT "ctor:pendingMapValue.h_closeF"} props={byT "ctor:pendingProps.h_closeFE"} \
idx0={cnt " idx0"} mono={n (·.mono)} monoOpt={n (·.monoOpt)} base={n (·.base)} baseOpt={n (·.baseOpt)} prep={n (·.prep)} dispB={n (·.dispB)} dispC={n (·.dispC)} \
hc={n (·.hc)} chr={n (·.chr)} dash={(sites.filter fun (_, _, i) => i.chr.any fun x => (x.splitOn "='-'").length > 1).size} corr={n (·.corr)} noflow={n (·.noflow)} save={n (·.save)} fl={n (·.fl)} top={n (·.top)} larm={n (·.larm)} floor={n (·.floor)} nic={n (·.nic)} armed={n (·.armed)} \
col0={n (·.col0)} ids={n (·.ids)} coverSites={n (·.cover)} coverBinders={sites.foldl (fun a (_, _, i) => a + i.cover.size) 0} coverFnSites={n (·.coverFn)} \
full={cnt "inputs=full"} fullB={cnt "inputs=full "} missMono={cnt "missing(mono"} missBase={(vs.filter fun v => (v.splitOn "base").length > 1).size} missPrep={(vs.filter fun v => (v.splitOn "prep").length > 1).size} missFloorSrc={cnt "floorSrc"} \
own={cnt "own="} empty={cnt "empty=0"} relay={cnt "relay="} relayEntries={vs.foldl (fun a v => a + ((v.splitOn "relay=").length - 1)) 0} \
{boundCounts} {lackCounts} rows={w.rows.size} nodes={w.nodes}"
  logInfo s!"PuntCoverInputs {got}"
  logInfo s!"sites:\n{String.intercalate "\n" siteLines.toList}"
  logInfo s!"shapes:\n{String.intercalate "\n" shapeLines.toList}"
  logInfo s!"bounds:\n{String.intercalate "\n" boundLines.toList}"
  logInfo s!"callers:\n{String.intercalate "\n" callerLines.toList}"
  logInfo s!"lack:\n{String.intercalate "\n" lackLines.toList}"
  logInfo s!"bottoms:\n{String.intercalate "\n" bottomLines.toList}"
  logInfo s!"bottomsPaid:\n{String.intercalate "\n" bottomPaidLines.toList}"
  logInfo namedS
  -- 2026-10-26 (item 370): five → four — the sibling `-` arm of `accum_block_on_pendingBlock` relays `h_closeF_old`.
  -- Item 371: four → three — `colon_open_map_explicit`'s `h_closeF` punt is paid from the restated value-line pack.
  unless sites.size == 3 do throwError "the four punts moved under this pass: sites={sites.size}"
  check "expectedSites" siteLines expectedSites
  check "expectedShapes" shapeLines expectedShapes
  check "expectedBounds" boundLines expectedBounds
  check "expectedCallers" callerLines expectedCallers
  check "expectedLack" lackLines expectedLack
  check "expectedBottoms" bottomLines expectedBottoms
  check "expectedBottomsPaid" bottomPaidLines expectedBottomsPaid
  unless namedS == expectedNamed do throwError "named-level lemmas moved:\n  got      {namedS}\n  expected {expectedNamed}"
  unless got == expectedLine do
    throwError "PuntCoverInputs moved:\n  got      {got}\n  expected {expectedLine}"

end Tests.Guards.PuntCoverInputs
