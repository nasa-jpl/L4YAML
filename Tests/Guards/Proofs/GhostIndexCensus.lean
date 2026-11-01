/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Production.StreamAccum

/-!
# The ghost-index census (DOCS item 331)

Row 12's two open forks (items 320 and 325) were both priced as a choice between
widening a park's alternative with a proof-side disjunct and restating a field.
Read together they are one question: **which indices of the accumulation
invariant are proof-side data standing in for scanner state?**  That is the
question Blueprint Rule 8 answers for the future, and this file counts for the
present.

## The classes

Every binder the invariant's carriers introduce — a parameter, an index, a
constructor field, or a quantifier inside a field's statement — is one of:

| class | what it is | ghost? |
|---|---|---|
| `surface` | a `SurfPos`, or a predicate on positions | no — the correspondence is the theorem |
| `state` | the `ScannerState` the carrier is about | no |
| `prop` | a `Prop` binder — a continuation, a route, a fact about the state | no — obligations are the induction hypothesis |
| `scalar` | a `Nat`, `Int`, `Bool`, `Char`, context, token array … | not counted as ghost here: most are grammar parameters (`n`, `c`) or pinned to the state by an inequality |
| `snapshot` | an `Option ScannerState` — a whole scanner state carried as an index | **yes** |
| `ghost` | a `List FrameLevel` (the frame lists — a mirror of `sc.indents` until `Covered` is an equality, item 332), a `List Nat` (the value-line chains), an `Array Bool` (the kinds and the key mask), a `FrameTail` | **yes** unless pinned to a projection of the state |
| `disjunct` | not a binder: an `∨` inside a field's statement, recorded at the field | **the shape Rule 8 forbids** when the alternative restates state (`PackAlt`, item 320's (A)); pinned per field so none can join unnoticed |

Rows are keyed by the FIELD they stand in (`ctor[i].name`), not only by the
constructor: a binder moving from one field to another, or an `∨` added to a
field, moves a row even when the counts do not (Devin Review on PR #7).

The last two columns are the rule's subject.  A snapshot or a ghost datum
either (a) is proved equal to a projection `f sc` of the live state — the kinds
index already is (`sc.flowStack`, 9b(i)) — or (b) names state the scanner does
not have, in which case the scanner is incomplete and the field is added to
`ScannerState` (item 299's `docStartLine`, item 48's `explicitKeyCol`, the
`definedAnchors` argument in DOCS.md).  What the rule forbids is the third
option the two forks offered: a new proof-side disjunct or index carried beside
the data the scanner already holds.

## What the census is and is not

It is a reading of TYPES, taken from the environment: the carriers' telescopes,
their constructors' fields, and every `∃`/`∀` binder inside those fields'
statements (that is where the `List Nat` chains live — `∃ ns : List Nat, ∀ nv ∈
ns, …`).  It does not read proofs, and it does not decide which ghost row is a
projection and which is a missing field: that is each row's own item, priced by
a probe (item 325's `1001`/`1002` pattern).  The pin below is the list to shrink;
a row leaves it when its carrier is re-indexed by a projection or a field, and
nothing may join it (Rule 8).
-/

namespace Tests.Guards.GhostIndexCensus

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab Lean.Elab.Command
open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs L4YAML.Proofs.StreamAccum

/-! ## §1  The instrument -/

inductive Class where
  | surface | state | prop | scalar | snapshot | ghost | disjunct
deriving BEq, Repr, Inhabited, DecidableEq

def Class.key : Class → String
  | .surface => "surface" | .state => "state" | .prop => "prop"
  | .scalar => "scalar" | .snapshot => "snapshot" | .ghost => "ghost" | .disjunct => "∨"

/-- One binder, where it stands. -/
structure Row where
  carrier : String
  site : String
  name : String
  ty : String
  cls : Class
deriving Inhabited

/-- The class of a binder TYPE. -/
def classify (t : Expr) : MetaM Class := do
  let t ← instantiateMVars t
  if t.isSort then return .scalar
  if ← isProp t then return .prop
  if t.isForall then
    return ← forallTelescope t fun xs b => do
      let onPos ← xs.allM fun x => do pure ((← inferType x).isConstOf ``SurfPos)
      if (← isProp b) && onPos then pure .surface else pure .scalar
  match t.getAppFn.constName? with
  | some ``SurfPos => return .surface
  | some ``ScannerState => return .state
  | some ``Option =>
      if t.getAppNumArgs == 1 && t.appArg!.isConstOf ``ScannerState then return .snapshot
      else return .scalar
  | some ``List =>
      if t.getAppNumArgs == 1 && (t.appArg!.isConstOf ``Nat ||
          t.appArg!.isConstOf ``L4YAML.Proofs.IndentStackCover.FrameLevel) then return .ghost
      else return .scalar
  | some ``Array =>
      if t.getAppNumArgs == 1 && t.appArg!.isConstOf ``Bool then return .ghost else return .scalar
  | some ``FrameTail => return .ghost
  | _ => return .scalar

def shown (n : Name) : String :=
  let n := n.eraseMacroScopes
  if n.isAnonymous then "_" else n.toString

/-- Walk a statement, recording every binder it introduces: `∀`, `∃`, and the
    lambdas a matcher alternative binds.  A `Prop` binder's own type is walked
    too — that is where a field's `∃ ns : List Nat` sits. -/
partial def walk (carrier site : String) : Expr → StateT (Array Row) MetaM Unit
  | e => do
    let e := e.consumeMData
    match e with
    | .forallE n t b bi => do
        let c ← classify t
        modify (·.push { carrier, site, name := shown n, ty := toString (← ppExpr t), cls := c })
        if c == .prop then walk carrier site t
        withLocalDecl n bi t fun x => walk carrier site (b.instantiate1 x)
    | .lam n t b bi => do
        let c ← classify t
        modify (·.push { carrier, site, name := shown n, ty := toString (← ppExpr t), cls := c })
        withLocalDecl n bi t fun x => walk carrier site (b.instantiate1 x)
    | .letE _ _ v b _ => do walk carrier site v; walk carrier site b
    | .proj _ _ s => walk carrier site s
    | .app .. => do
        if e.isAppOfArity ``Or 2 then
          modify (·.push { carrier, site, name := "∨", ty := toString (← ppExpr e.appArg!), cls := .disjunct })
        if e.isAppOfArity ``Exists 2 then
          match e.appArg! with
          | .lam n t b bi => do
              let c ← classify t
              modify (·.push { carrier, site, name := shown n, ty := toString (← ppExpr t), cls := c })
              withLocalDecl n bi t fun x => walk carrier site (b.instantiate1 x)
          | lam => walk carrier site lam
        else
          e.withApp fun f args => do
            if f.isLambda then walk carrier site f
            for a in args do walk carrier site a
    | _ => pure ()

/-- The top of a telescope, where each `∀` is a FIELD — an index of the type or
    a constructor's field.  The field's ordinal and name key every row found
    inside it, so the pins tell `pendingContent[3].h_resume`'s `ks` from
    `pendingContent[5].h_park`'s.  The result type is walked as `site[ret]`. -/
partial def walkFields (carrier site : String) (i : Nat) : Expr → StateT (Array Row) MetaM Unit
  | e => do
    let e := e.consumeMData
    match e with
    | .forallE n t b bi => do
        let fs := s!"{site}[{i}].{shown n}"
        let c ← classify t
        modify (·.push { carrier, site := fs, name := shown n, ty := toString (← ppExpr t), cls := c })
        if c == .prop then walk carrier fs t
        withLocalDecl n bi t fun x => walkFields carrier site (i + 1) (b.instantiate1 x)
    | _ => walk carrier s!"{site}[ret]" e

/-- Every binder of one carrier: its type's telescope (`type`), each
    constructor's fields past the shared parameters (the constructor's name),
    or a definition's body (`body`). -/
def carrierRows (c : Name) : MetaM (Array Row) := do
  let env ← getEnv
  let some ci := env.find? c | throwError "the census names no constant {c}"
  let carrier := c.getString!
  let (_, rows) ← (do
    walkFields carrier "type" 0 ci.type
    match ci with
    | .inductInfo ind =>
        for ctor in ind.ctors do
          let some cci := env.find? ctor | continue
          forallBoundedTelescope cci.type (some ind.numParams) fun _ body =>
            walkFields carrier ctor.getString! ind.numParams body
    | .defnInfo d =>
        forallTelescope d.type fun xs _ => do
          let body := (d.value.beta xs).headBeta
          walk carrier "body" body
    | _ => pure ()).run #[]
  return rows

/-- The carriers are READ OFF THE ENVIRONMENT, not listed: every `Prop`-valued
    definition, structure or inductive that `StreamAccum` declares (a route, a
    pack, a park, a frame stack, a context such as `ResumeKeyCtx`), plus the
    correspondence from `CouplingBridge`.  Devin Review on the first cut caught
    why a hand list is the wrong instrument: `ResumeKeyCtx` binds `List Nat`
    frame lists and enters the accumulation lemmas through `h_resumectx`, and a
    list that named thirty-one carriers would never have noticed a ghost added to
    it.  Lemmas (`thmInfo`), constructors, recursors, matchers and the other
    generated auxiliaries are excluded; the module's authored `Prop` vocabulary
    is what remains. -/
def extraCarriers : List Name := [ ``L4YAML.Proofs.CouplingBridge.ScannerSurfCorr ]

/-- Does the constant's type end in `Prop` (a predicate, after its parameters)? -/
def endsInProp (t : Expr) : MetaM Bool :=
  forallTelescopeReducing t fun _ b => pure b.isProp

def carriersOf : MetaM (Array Name) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? ``PendingNode
  let mut out : Array Name := #[]
  for (nm, ci) in env.constants.toList do
    -- Filter on the USER name: the module system privatises generated
    -- auxiliaries, and an authored `private def LocalCtx … : Prop` is mangled
    -- the same way (`_private.<module>.0.<name>`).  Both keep their user name
    -- under `StreamAccum`, so the namespace and the generated-name tests read
    -- `un`; the environment is read at the real `nm`.  (Devin Review's second
    -- finding on PR #26: a `private` predicate must not escape the gate.)
    let un := Lean.privateToUserName nm
    if un.isInternal || un.isInternalDetail then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if env.isProjectionFn nm || isCtorName env nm || isRecCore env nm then continue
    if isAuxRecursor env nm || isNoConfusion env nm || isGenerated un then continue
    if (`L4YAML.Proofs.StreamAccum).isPrefixOf un == false then continue
    match ci with
    | .defnInfo _ | .inductInfo _ =>
        if ← endsInProp ci.type then out := out.push nm
    | _ => pure ()
  let sorted := out.qsort (fun a b => a.toString < b.toString)
  return sorted ++ extraCarriers.toArray
where
  isCtorName (env : Environment) (n : Name) : Bool :=
    match env.find? n with | some (.ctorInfo _) => true | _ => false
  isRecCore (env : Environment) (n : Name) : Bool :=
    match env.find? n with | some (.recInfo _) => true | _ => false
  /-- The structural-recursion and injectivity auxiliaries an inductive
      generates under its own namespace (`X.below`, `X.ibelow`, `X.brecOn`,
      `X.inj`, …): `Prop`-valued, authored by nobody. -/
  isGenerated (n : Name) : Bool :=
    match n with
    | .str _ s => s ∈ ["below", "ibelow", "brecOn", "binductionOn", "casesOn", "recOn",
        "noConfusion", "noConfusionType", "inj", "injEq", "sizeOf_spec", "ctorIdx", "ctorElim"]
    | _ => false

def tallyLine (carrier : String) (rows : Array Row) : String :=
  let count (k : Class) := (rows.filter (·.cls == k)).size
  s!"{carrier}: surface={count .surface} state={count .state} prop={count .prop} \
scalar={count .scalar} snapshot={count .snapshot} ghost={count .ghost} or={count .disjunct}"

def ghostLine (r : Row) : String := s!"{r.carrier}.{r.site} {r.name} : {r.ty}"

/-- One `∨` where it stands: the field, and the alternative it offers. -/
def disjunctLine (r : Row) : String :=
  let oneLine := " ".intercalate ((r.ty.splitOn "\n").map fun l => String.ofList (l.toList.dropWhile (· == ' ')))
  s!"{r.carrier}.{r.site} ∨ {oneLine}"

/-! ## §2  The pins

Regenerated from the guard's own output; a change is recorded with a dated note
like every other census in this directory.  `expectedGhost` is Rule 8's list:
it may only shrink. -/

/-- 52 carriers, 9 snapshot indices, 73 ghost data binders and 92 disjuncts on
    2026-10-21 (item 331; rows re-keyed by field and the disjunct list added the
    same day, after Devin Review on PR #7), the day the census was taken — Rule 8's baseline; the
    carriers are every `Prop`-valued declaration of `StreamAccum` (see `carriersOf`). -/
-- Item 350: carriers 52 → 53 — `NotQuestionPark sc` joins the carrier list (the two
-- `?`-entry faces' `PackAlt` arm became it); the 92 disjuncts are unchanged in number.
-- 2026-10-24: B3 ([66] col-0 threading) adds the JSON-key carry (`FrameTail.colon kj`/`.value kj`),
-- the `ResvOk` reservation carriers and the `InteriorGap` h_q/h_some gap fields.
-- 2026-10-25 (#99 review): `FrameTail.leadFree`/`closeFree` are `Bool` projections of the tail
-- (consumers state `tl.leadFree = true`), not `Prop` carriers over it, and the dead `FlowLead`
-- duplicate is deleted — the eight `FrameTail` ghost rows they added are gone; ghost is back at 72.
-- 2026-10-25 (#112 review): the `FlowStackK.body ∨ True` row #112 added is gone with the carrier (Rule 8: decided at the close by `Classical.em`); or back at 98.
-- Item 372 (2026-10-27): `ImplicitKeyPack`'s route conjunct gained `∨ SeqTopKey sc`
-- — a Bool projection of the pack's own state, so one more carrier and one more
-- disjunct, no ghost row.
-- Item 374: `ResumeKeyCtx` gains the sequence-top face disjunct (or 101 → 102; ghost unchanged).
-- 2026-10-29 (item 389): the mapping-top conjunct inside `pendingBlock.h_closeF` / `pendingBlockContent.h_closeF` / `pendingProps.h_closeFE` adds its own `∨ True` (or 102 → 105) and NO binder: it resumes the park's own `ks` (PR #161 review dropped the first draft's `∃ ks'`; ghost stays 72).
-- 2026-10-30 (item 405, Rule 8 fix): the `?`-park chain fields `pendingBlock.h_kslot`/`pendingBlockContent.h_kslot` are RE-INDEXED by the projection `RegisterWitness.markedCols sc` (`∀ nv ∈ markedCols sc, …`, no `∃ ns`): the two ghost rows the head-form chain had added leave the roster (ghost 75 → 73, back to item 404's reading); `h_explUp` keeps its one new `∨ PackAlt sc` disjunct (or 106 → 107).
def expectedSummary : String := "carriers=60 snapshot=9 ghost=72 or=108"

-- 2026-10-24 (B3 [66] col-0 threading): carriers 61 → 62 — `SSLCommentsFrom` (the separator-less comment product).
-- 2026-10-25 (#99 landed): the `FlowLead`/`leadFree`/`closeFree` tally rows go with the deleted carrier and
-- the two `Bool` projections (the summary above was already re-read; the tally was not).
-- 2026-10-29 (item 394, option B): the flow stack's new state index `s0` (FlowBaseRoutes /
-- FlowOpenStack / FlowStackB state 0 → 1; FlowStackK state 1 → 2 and prop 4 → 5 for the
-- `sc.indents = s0.indents` conjunct); valueF's cover adds the scalar `lo` (FlowBaseRoutes
-- scalar 8 → 9); pendingMapValue.h_closeF's cover lost its ghost level `m` (PendingNode
-- scalar 63 → 62) — the cover is now `Floor lo n ks` at the park's own level.
-- 2026-10-30 (item 407, flow carrier `pendingKeys` conjunct): FlowStackK prop 5 → 6 — the carrier gains `(0 < fl → sc.pendingKeys = s0.pendingKeys)`, an implication whose body is a STATE equality (classed `prop` like its indents twin); ghost 3 → 3, no proof-side list.
def expectedTally : List String :=
  ["BareLandingFacts: surface=0 state=2 prop=0 scalar=1 snapshot=0 ghost=0 or=0",
   "BlockStack: surface=2 state=0 prop=0 scalar=0 snapshot=0 ghost=0 or=0",
   "CommentStop: surface=0 state=0 prop=0 scalar=1 snapshot=0 ghost=0 or=2",
   "CompletedTail: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0 or=0",
   "ContentRouteGate: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0 or=0",
   "DanglingPred: surface=0 state=0 prop=0 scalar=6 snapshot=0 ghost=0 or=0",
   "ExplValueLine: surface=5 state=0 prop=3 scalar=1 snapshot=0 ghost=0 or=0",
   "ExplicitValueRefused: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0 or=0",
   "FlowBaseAnchor: surface=0 state=5 prop=0 scalar=4 snapshot=2 ghost=0 or=0",
   "FlowBaseRoutes: surface=23 state=1 prop=29 scalar=9 snapshot=1 ghost=4 or=7",
   "FlowOpenHeld: surface=0 state=0 prop=0 scalar=3 snapshot=0 ghost=2 or=0",
   "FlowOpenStack: surface=31 state=1 prop=28 scalar=9 snapshot=1 ghost=11 or=2",
   "FlowStack: surface=2 state=0 prop=0 scalar=0 snapshot=0 ghost=0 or=0",
   "FlowStackB: surface=6 state=1 prop=1 scalar=4 snapshot=1 ghost=7 or=0",
   "FlowStackK: surface=5 state=2 prop=6 scalar=5 snapshot=1 ghost=3 or=2",
   "GateOf: surface=0 state=1 prop=0 scalar=1 snapshot=2 ghost=0 or=0",
   "ImplicitKeyHead: surface=2 state=0 prop=2 scalar=0 snapshot=0 ghost=0 or=0",
   "ImplicitKeyPack: surface=16 state=1 prop=16 scalar=9 snapshot=0 ghost=4 or=7",
   "InlineResidue: surface=2 state=0 prop=0 scalar=1 snapshot=0 ghost=0 or=0",
   "InteriorGap: surface=3 state=1 prop=30 scalar=11 snapshot=0 ghost=1 or=4",
   "KeyFloor: surface=0 state=0 prop=1 scalar=7 snapshot=0 ghost=0 or=0",
   "KeyFrames: surface=4 state=0 prop=5 scalar=3 snapshot=0 ghost=2 or=0",
   "KeyPackPunt: surface=0 state=1 prop=9 scalar=0 snapshot=0 ghost=0 or=0",
   "KeyResv: surface=0 state=1 prop=1 scalar=1 snapshot=0 ghost=0 or=0",
   "KeyResvLe: surface=0 state=1 prop=1 scalar=1 snapshot=0 ghost=0 or=0",
   "KmSound: surface=0 state=1 prop=9 scalar=21 snapshot=0 ghost=3 or=2",
   "MapFrame: surface=40 state=0 prop=38 scalar=7 snapshot=0 ghost=1 or=0",
   "MarkerNodeRoute: surface=4 state=0 prop=1 scalar=0 snapshot=0 ghost=0 or=0",
   "NextIsSep: surface=0 state=1 prop=0 scalar=3 snapshot=0 ghost=0 or=0",
   "NotQuestionPark: surface=0 state=1 prop=1 scalar=3 snapshot=0 ghost=0 or=0",
   "OfferPred: surface=0 state=0 prop=0 scalar=4 snapshot=0 ghost=0 or=0",
   "OpenSeqEntry: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0 or=1",
   "PackAlt: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0 or=0",
   "PackAltG: surface=0 state=0 prop=0 scalar=0 snapshot=1 ghost=0 or=0",
   "ParkAnchor: surface=0 state=2 prop=3 scalar=4 snapshot=0 ghost=0 or=0",
   "ParkChoice: surface=0 state=2 prop=0 scalar=1 snapshot=0 ghost=0 or=1",
   "ParkCore: surface=0 state=2 prop=5 scalar=6 snapshot=0 ghost=1 or=0",
   "ParkFloor: surface=0 state=2 prop=4 scalar=4 snapshot=0 ghost=0 or=0",
   "ParkSlot: surface=0 state=2 prop=3 scalar=7 snapshot=0 ghost=0 or=1",
   -- Item 371: `pendingMapValue.h_expl`'s route carries its tail — one more surface binder
   -- (`sp_e`) and one more `Prop` premise (`SCompactMapTail`); ghost 22 and or 60 unchanged.
   "PendingNode: surface=139 state=1 prop=284 scalar=63 snapshot=0 ghost=22 or=65",
   "PropsKeyPack: surface=13 state=1 prop=13 scalar=7 snapshot=0 ghost=3 or=5",
   "PropsNodeRoute: surface=6 state=0 prop=1 scalar=0 snapshot=0 ghost=0 or=0",
   "PropsRideRoute: surface=7 state=0 prop=1 scalar=0 snapshot=0 ghost=0 or=0",
   "PropsRun: surface=14 state=0 prop=8 scalar=4 snapshot=0 ghost=0 or=0",
   "RestoreLayout: surface=0 state=1 prop=0 scalar=4 snapshot=0 ghost=0 or=0",
   "ResumeFrames: surface=4 state=0 prop=5 scalar=3 snapshot=0 ghost=2 or=0",
   "ResumeKeyCtx: surface=7 state=1 prop=6 scalar=9 snapshot=0 ghost=3 or=6",
   "ResumeWidths: surface=0 state=0 prop=0 scalar=2 snapshot=0 ghost=2 or=0",
   "ResvOk: surface=0 state=1 prop=2 scalar=5 snapshot=0 ghost=0 or=0",
   "ResvOkLe: surface=0 state=1 prop=2 scalar=5 snapshot=0 ghost=0 or=0",
   "SeqEntryTail: surface=3 state=0 prop=1 scalar=1 snapshot=0 ghost=0 or=0",
   "SeqFrame: surface=40 state=0 prop=38 scalar=7 snapshot=0 ghost=1 or=0",
   -- Item 372 (2026-10-27): the key pack's sequence-top face, a projection of its own state.
   "SeqTopKey: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0 or=0",
   "SlotFace: surface=0 state=0 prop=0 scalar=4 snapshot=0 ghost=0 or=1",
   "SlotGateAt: surface=0 state=2 prop=7 scalar=1 snapshot=0 ghost=0 or=1",
   "SlotResv: surface=0 state=0 prop=1 scalar=5 snapshot=0 ghost=0 or=1",
   "StaleNodeTail: surface=0 state=1 prop=0 scalar=1 snapshot=0 ghost=0 or=0",
   "StalePark: surface=0 state=1 prop=0 scalar=0 snapshot=0 ghost=0 or=0",
   "SuffixRun: surface=4 state=0 prop=0 scalar=0 snapshot=0 ghost=0 or=0",
   "ScannerSurfCorr: surface=1 state=1 prop=7 scalar=4 snapshot=0 ghost=0 or=0"]

/-- The list to shrink.  Read with the header's caveat: `FlowOpenHeld`'s `S` (and
    `ParkCore`'s, which holds it) is a list of TOKEN INDICES, a projection of
    `tokens` already; `KmSound.body xs` is the array the mask's `[i]` reads.  The
    rest are the frame lists, the value-line chains, the kinds and the mask, the
    frame tail, and the open-time snapshot `g`. -/
-- 2026-10-29 (item 394, option B): the roster is unchanged in content (82 rows); FlowBaseRoutes'
-- constructor indices shift by one for the new state parameter `s0` (mk[5] → mk[6], …).
def expectedGhost : List String :=
  [ "FlowBaseAnchor.type[0].a a : Option ScannerState",
    "FlowBaseAnchor.body x : Option ScannerState",
    "FlowBaseRoutes.type[4].g g : Option ScannerState",
    "FlowBaseRoutes.mk[6].valueF ks : List IndentStackCover.FrameLevel",
    "FlowBaseRoutes.mk[8].key ks : List IndentStackCover.FrameLevel",
    "FlowBaseRoutes.mk[8].key ks : List IndentStackCover.FrameLevel",
    "FlowBaseRoutes.mk[9].vslot ns : List Nat",
    "FlowOpenHeld.type[3].S S : List Nat",
    "FlowOpenHeld.body T : List Nat",
    "FlowOpenStack.type[3].g g : Option ScannerState",
    "FlowOpenStack.type[6].a a : Array Bool",
    "FlowOpenStack.type[7].a a : Array Bool",
    "FlowOpenStack.type[8].a a : FrameTail",
    "FlowOpenStack.seqBase[11].tl tl : FrameTail",
    "FlowOpenStack.mapBase[11].tl tl : FrameTail",
    "FlowOpenStack.seqNest[6].ks ks : Array Bool",
    "FlowOpenStack.seqNest[7].km km : Array Bool",
    "FlowOpenStack.seqNest[9].tl tl : FrameTail",
    "FlowOpenStack.mapNest[6].ks ks : Array Bool",
    "FlowOpenStack.mapNest[7].km km : Array Bool",
    "FlowOpenStack.mapNest[9].tl tl : FrameTail",
    "FlowStackB.type[3].g g : Option ScannerState",
    "FlowStackB.type[6].a a : Array Bool",
    "FlowStackB.type[7].a a : Array Bool",
    "FlowStackB.type[8].a a : FrameTail",
    "FlowStackB.nil[6].tl tl : FrameTail",
    "FlowStackB.open[6].ks ks : Array Bool",
    "FlowStackB.open[7].km km : Array Bool",
    "FlowStackB.open[8].tl tl : FrameTail",
    "FlowStackK.type[3].ks ks : Array Bool",
    "FlowStackK.type[4].tl tl : FrameTail",
    "FlowStackK.body km : Array Bool",
    "FlowStackK.body g : Option ScannerState",
    "GateOf.type[0].a a : Option ScannerState",
    "GateOf.body x : Option ScannerState",
    "ImplicitKeyPack.body ns : List Nat",
    "ImplicitKeyPack.body ks : List IndentStackCover.FrameLevel",
    "ImplicitKeyPack.body ks : List IndentStackCover.FrameLevel",
    "ImplicitKeyPack.body ks : List IndentStackCover.FrameLevel",
    "InteriorGap.type[1].tl tl : FrameTail",
    "KeyFrames.type[1].a a : List IndentStackCover.FrameLevel",
    "KeyFrames.level[2].ks ks : List IndentStackCover.FrameLevel",
    "KmSound.type[1].km km : Array Bool",
    "KmSound.body xs : Array Bool",
    "KmSound.body xs : Array Bool",
    "MapFrame.type[2].a a : FrameTail",
    "PackAltG.type[0]._g _g : Option ScannerState",
    "ParkCore.mk[4].held S : List Nat",
    "PendingNode.pendingContent[9].h_vpack ns : List Nat",
    "PendingNode.pendingContent[11].h_framesS ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingContent[12].h_framesV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingContent[16].h_seqF ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps[21].h_kslot ns : List Nat",
    "PendingNode.pendingProps[24].h_closeFE ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps[25].h_closeF ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps[26].h_closeFV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingProps[28].h_closeFEV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlockContent[13].h_closeF ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlockContent[17].h_kslotUp ns : List Nat",
    "PendingNode.pendingBlockContent[18].h_closeFV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlock[11].h_closeF ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingBlock[14].h_kslotUp ns : List Nat",
    "PendingNode.pendingBlock[15].h_closeFV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue[16].h_kslot ns : List Nat",
    "PendingNode.pendingMapValue[17].h_closeF ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue[18].h_frames ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue[19].h_closeFV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue[20].h_framesV ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue[22].h_seqF ks : List IndentStackCover.FrameLevel",
    "PendingNode.pendingMapValue[23].h_explUp ns : List Nat",
    "PropsKeyPack.body ns : List Nat",
    "PropsKeyPack.body ks : List IndentStackCover.FrameLevel",
    "PropsKeyPack.body ks : List IndentStackCover.FrameLevel",
    "ResumeFrames.type[1].a a : List IndentStackCover.FrameLevel",
    "ResumeFrames.level[2].ks ks : List IndentStackCover.FrameLevel",
    "ResumeKeyCtx.body ks : List IndentStackCover.FrameLevel",
    "ResumeKeyCtx.body ksv : List IndentStackCover.FrameLevel",
    "ResumeKeyCtx.body ksq : List IndentStackCover.FrameLevel",
    "ResumeWidths.type[0].ks ks : List IndentStackCover.FrameLevel",
    "ResumeWidths.type[1].ks' ks' : List IndentStackCover.FrameLevel",
    "SeqFrame.type[2].a a : FrameTail"
  ]

/-- Every `∨` inside a carrier's statements, keyed by field (Devin Review on
    PR #7: a binder-free alternative added to a field moved no binder row).  Like
    `expectedGhost`, a row joining this list is Rule 8's question. -/
-- 2026-10-25 (#99 review): `leadFree`/`closeFree` made `Bool` — still 98 disjuncts; `InteriorGap.props[8].h_lead` now reads `tl.leadFree = true` (the coercion is explicit) and the rows re-order with the carrier roster (read off the environment, `FlowLead` gone).
-- 2026-10-29 (item 389): the mapping-top conjunct's own `∨ True` inside the three route fields (one more disjunct each; or 102 → 105).
-- 2026-10-29 (item 394): `FlowBaseRoutes.valueF` — the flow value's frames twin, `∃ ks` relaying `pendingMapValue.h_closeF`'s list (Rule 8: a RELAY of an existing frames list, the one binder the field needs) with its own `∨ True` (ghost 72 → 73, or 105 → 106).
-- 2026-10-29 (item 394, option B): 106 rows unchanged in count; FlowBaseRoutes' indices shift for
-- `s0` and FlowStackK's colon-route disjunct now names `s0` in the FlowStackB it promises.
def expectedDisjuncts : List String :=
  [ "CommentStop.body ∨ c = '\\n' ∨ c = '\\x0d'",
    "CommentStop.body ∨ c = '\\x0d'",
    "FlowBaseRoutes.mk[6].valueF ∨ True",
    "FlowBaseRoutes.mk[8].key ∨ True",
    "FlowBaseRoutes.mk[8].key ∨ True",
    "FlowBaseRoutes.mk[8].key ∨ PackAltG g",
    "FlowBaseRoutes.mk[8].key ∨ True",
    "FlowBaseRoutes.mk[8].key ∨ PackAltG g",
    "FlowBaseRoutes.mk[9].vslot ∨ PackAltG g",
    "FlowOpenStack.seqNest[15].promise ∨ sp_prep = sp_ne",
    "FlowOpenStack.mapNest[15].promise ∨ sp_prep = sp_ne",
    "FlowStackK.body ∨ ∀ (sp_prep sp_tok : SurfPos), SSeparateLines n sp_flow sp_prep ∨ sp_prep = sp_flow → GLit ':' sp_prep sp_tok → FlowStackB sp_start n kc g s0 fl ks km (FrameTail.colon kj) sp_block sp_tok",
    "FlowStackK.body ∨ sp_prep = sp_flow",
    "ImplicitKeyPack.body ∨ SeqTopKey sc",
    "ImplicitKeyPack.body ∨ PackAlt sc",
    "ImplicitKeyPack.body ∨ True",
    "ImplicitKeyPack.body ∨ True",
    "ImplicitKeyPack.body ∨ PackAlt sc",
    "ImplicitKeyPack.body ∨ True",
    "ImplicitKeyPack.body ∨ True",
    "InteriorGap.props[8].h_lead ∨ ¬m ≤ PreprocessIndentStable.minContentIndentOf sc",
    "InteriorGap.props[8].h_lead ∨ sp_p = sp_flow ∧ tl.leadFree = true",
    "InteriorGap.props[9].h_run ∨ ¬m ≤ PreprocessIndentStable.minContentIndentOf sc",
    "InteriorGap.props[16].h_some ∨ ht = true",
    "KmSound.body ∨ True",
    "KmSound.body ∨ True",
    "OpenSeqEntry.body ∨ sameIndentSequenceOpen s.tokens ↑s.col = true",
    "ParkChoice.body ∨ ParkSlot sc0 s d",
    "ParkSlot.mk[5].slotRun ∨ ∃ j, prevRealIdx? sc0.tokens (propsRunStart sc0.tokens sc0.tokens.size) = some j ∧ sc0.tokens[j]!.val.offersNodeSlot = true",
    "PendingNode.noPending[3].h_col ∨ sc.inFlow = true",
    "PendingNode.noPending[4].h_arm ∨ sc.inFlow = true",
    "PendingNode.pendingContent[5].h_line ∨ LineOpenGuard.LineNodeStop sp_scan.chars",
    "PendingNode.pendingContent[7].h_key ∨ KeyPackPunt sc",
    "PendingNode.pendingContent[9].h_vpack ∨ PackAlt sc",
    "PendingNode.pendingContent[10].h_arm ∨ 0 < sp_scan.col",
    "PendingNode.pendingContent[11].h_framesS ∨ True",
    "PendingNode.pendingContent[11].h_framesS ∨ True",
    "PendingNode.pendingContent[12].h_framesV ∨ PackAlt sc",
    "PendingNode.pendingContent[12].h_framesV ∨ True",
    "PendingNode.pendingContent[16].h_seqF ∨ True",
    "PendingNode.pendingProps[16].h_key ∨ KeyPackPunt sc",
    "PendingNode.pendingProps[19].h_ncol ∨ True",
    "PendingNode.pendingProps[21].h_kslot ∨ PackAlt sc",
    "PendingNode.pendingProps[22].h_routeE ∨ PackAlt sc",
    "PendingNode.pendingProps[23].h_kslotE ∨ PackAlt sc",
    "PendingNode.pendingProps[24].h_closeFE ∨ True",
    "PendingNode.pendingProps[24].h_closeFE ∨ True",
    "PendingNode.pendingProps[24].h_closeFE ∨ True",
    "PendingNode.pendingProps[25].h_closeF ∨ True",
    "PendingNode.pendingProps[25].h_closeF ∨ True",
    "PendingNode.pendingProps[26].h_closeFV ∨ PackAlt sc",
    "PendingNode.pendingProps[26].h_closeFV ∨ True",
    "PendingNode.pendingProps[28].h_closeFEV ∨ PackAlt sc",
    "PendingNode.pendingProps[29].h_slot ∨ SlotFace sc.tokens",
    "PendingNode.pendingDocEnd[4].h_line ∨ LineOpenGuard.LineTailSuffix sp_scan.chars",
    "PendingNode.pendingDocEnd[6].h_arm ∨ 0 < sp_scan.col",
    "PendingNode.pendingFlow[5].h_arm ∨ 0 < sp_scan.col",
    "PendingNode.pendingFlow[8].h_live0 ∨ sc.simpleKey.possible = true",
    "PendingNode.pendingBlockContent[6].h_line ∨ LineOpenGuard.LineNodeStop sp_scan.chars",
    "PendingNode.pendingBlockContent[9].h_key ∨ KeyPackPunt sc",
    "PendingNode.pendingBlockContent[11].h_arm ∨ 0 < sp_scan.col",
    "PendingNode.pendingBlockContent[12].h_kslot ∨ PackAlt sc",
    "PendingNode.pendingBlockContent[13].h_closeF ∨ True",
    "PendingNode.pendingBlockContent[13].h_closeF ∨ True",
    "PendingNode.pendingBlockContent[13].h_closeF ∨ True",
    "PendingNode.pendingBlockContent[16].h_seqF ∨ True",
    "PendingNode.pendingBlockContent[17].h_kslotUp ∨ PackAlt sc",
    "PendingNode.pendingBlockContent[18].h_closeFV ∨ PackAlt sc",
    "PendingNode.pendingBlockContent[18].h_closeFV ∨ True",
    "PendingNode.pendingBlock[10].h_kslot ∨ PackAlt sc",
    "PendingNode.pendingBlock[11].h_closeF ∨ True",
    "PendingNode.pendingBlock[11].h_closeF ∨ True",
    "PendingNode.pendingBlock[11].h_closeF ∨ True",
    "PendingNode.pendingBlock[13].h_seqF ∨ True",
    "PendingNode.pendingBlock[14].h_kslotUp ∨ PackAlt sc",
    "PendingNode.pendingBlock[15].h_closeFV ∨ PackAlt sc",
    "PendingNode.pendingBlock[15].h_closeFV ∨ True",
    "PendingNode.pendingMapValue[10].h_ivl ∨ sp_scan.col = n + 1 ∧ ∀ (sp_v : SurfPos), SBlockIndented n YamlContext.blockOut sp_scan sp_v → SLYamlStream sp_start sp_v",
    "PendingNode.pendingMapValue[11].h_expl ∨ NotQuestionPark sc",
    "PendingNode.pendingMapValue[11].h_expl ∨ PackAlt sc",
    "PendingNode.pendingMapValue[12].h_vslot ∨ sc.implicitValueLine = some sc.line",
    "PendingNode.pendingMapValue[15].h_ncol ∨ True",
    "PendingNode.pendingMapValue[16].h_kslot ∨ PackAlt sc",
    "PendingNode.pendingMapValue[17].h_closeF ∨ True",
    "PendingNode.pendingMapValue[17].h_closeF ∨ True",
    "PendingNode.pendingMapValue[18].h_frames ∨ True",
    "PendingNode.pendingMapValue[18].h_frames ∨ True",
    "PendingNode.pendingMapValue[19].h_closeFV ∨ PackAlt sc",
    "PendingNode.pendingMapValue[19].h_closeFV ∨ True",
    "PendingNode.pendingMapValue[20].h_framesV ∨ PackAlt sc",
    "PendingNode.pendingMapValue[20].h_framesV ∨ True",
    "PendingNode.pendingMapValue[22].h_seqF ∨ True",
    "PendingNode.pendingMapValue[23].h_explUp ∨ NotQuestionPark sc ∨ PackAlt sc",
    "PendingNode.pendingMapValue[23].h_explUp ∨ PackAlt sc",
    "PropsKeyPack.body ∨ PackAlt sc",
    "PropsKeyPack.body ∨ True",
    "PropsKeyPack.body ∨ True",
    "PropsKeyPack.body ∨ PackAlt sc",
    "PropsKeyPack.body ∨ True",
    "ResumeKeyCtx.body ∨ True",
    "ResumeKeyCtx.body ∨ (∃ k sp_land, sp_land.col = 0 ∧ SIndent k sp_land sp_prep ∧ SeqTopKey s_prep) ∧ s_prep.simpleKey.possible = true ∧ s_prep.simpleKey.pos = s_prep.currentPos",
    "ResumeKeyCtx.body ∨ True",
    "ResumeKeyCtx.body ∨ PackAlt s_prep",
    "ResumeKeyCtx.body ∨ True",
    "ResumeKeyCtx.body ∨ True",
    "SlotFace.body ∨ ∃ j, prevRealIdx? ts (propsRunStart ts ts.size) = some j ∧ ts[j]!.val.offersNodeSlot = true",
    "SlotGateAt.body ∨ SlotFace t.tokens",
    "SlotResv.body ∨ p.val = YamlToken.key"
  ]

run_cmd liftTermElabM do
  let mut tally : Array String := #[]
  let mut ghost : Array String := #[]
  let mut disj : Array String := #[]
  let mut nSnap := 0
  let mut nGhost := 0
  let carriers ← carriersOf
  for c in carriers do
    let rows ← carrierRows c
    tally := tally.push (tallyLine c.getString! rows)
    for r in rows do
      if r.cls == .snapshot || r.cls == .ghost then
        ghost := ghost.push (ghostLine r)
        if r.cls == .snapshot then nSnap := nSnap + 1 else nGhost := nGhost + 1
      if r.cls == .disjunct then disj := disj.push (disjunctLine r)
  let summary := s!"carriers={carriers.size} snapshot={nSnap} ghost={nGhost} or={disj.size}"
  -- One report for all four pins, so a re-pin round reads everything at once.
  let mut moved : Array String := #[]
  if summary != expectedSummary then
    moved := moved.push s!"the ghost-index SUMMARY moved.\nexpected: {expectedSummary}\ngot:      {summary}"
  if tally.toList != expectedTally then
    moved := moved.push s!"the per-carrier TALLY moved.\ngot:\n{
      String.intercalate "\n" tally.toList}"
  if ghost.toList != expectedGhost then
    moved := moved.push s!"Rule 8's GHOST LIST moved.\nexpected ({expectedGhost.length}), got ({ghost.size}):\n{
      String.intercalate "\n" ghost.toList}"
  if disj.toList != expectedDisjuncts then
    moved := moved.push s!"Rule 8's DISJUNCT LIST moved.\nexpected ({expectedDisjuncts.length}), got ({disj.size}):\n{
      String.intercalate "\n" disj.toList}"
  unless moved.isEmpty do
    throwError (String.intercalate "\n\n" moved.toList)

end Tests.Guards.GhostIndexCensus
