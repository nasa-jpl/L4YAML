import Tests.Guards.Proofs.RelaySupplyCensus
import Tests.Guards.Proofs.ConclusionCensus

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The census over CONCLUSION ROUTES (DOCS item 213)

Item 212 built the census the four term censuses had each called missing, for
the SUPPLY direction: for every application of a constant with a `_ ∨ True`
binder, what decides that argument.  It closed with the other half still open:

> The relay census answers the UPWARD direction — who supplies an optional
> premise — and it is now a gate.  **The DOWNWARD direction, a conclusion
> conjunct traced into the lemmas that produce it, is still followed by hand,
> one narrowing and one build at a time.**

This is that instrument.  For every `_ ∨ True` in the CONCLUSION of a
`StreamAccum` lemma, follow the proof term to the position that produces it and
resolve what decides it there.

## What a route is

A conclusion's optional conjuncts sit at addresses: left or right of an `∧`,
inside an `∃`, or inside the payload of another `_ ∨ True`.  The census walks
the type to collect those addresses and then walks the PROOF to the same
address, entering `And.intro`, `Exists.intro` and `Or.inl` as it goes.  On the
way it follows the same three things item 212's walk follows — a `have` through
its beta-redex, a `let`, and a case split into each of its alternatives — plus
two more the downward direction needs:

* **`split`'s SPLITTER.**  `split` leaves a `<matcher>.splitter` behind, and the
  splitter is PRIVATE to the module that ran it while its matcher is not, so the
  private prefix has to come off before the matcher table will answer.  Its
  alternatives carry extra hypotheses the matcher's do not, so their binder
  counts are read off the splitter's OWN telescope.
* **PIPES.**  `Or.imp`, `Eq.mpr`, `Eq.ndrec`, `cast`, `id`, `dite` — the
  combinators a tactic leaves behind.  None of them decides an `∨`; each carries
  someone else's.  Reading a pipe as a producer is what makes a relay invisible,
  and it is the same error in the downward direction as the one item 212
  measured in the upward one.

## What each answer means

`PAY` / `DECLINE` — an `Or.inl` / `Or.inr` written for this conjunct on this
arm.  `VIA g` — the conjunct is `g`'s conclusion, so `g` decides it.  `RELAY` —
it is one of the lemma's own premises, so its CALLERS decide it.  `FIELD …` — it
was unpacked from a structure or a destructuring.  `VACUOUS` — the arm is closed
by `False.elim`, so it decides nothing.  `PARENT-DECLINED` — the conjunct lives
inside another optional conjunct's payload and that arm declined the parent, so
this one was never reached.  `UNREACHABLE` — no route exists; see the blind spot
below.

## The control that could fail, and did not

Item 212 measured four rows of `ConclusionCensus` by NARROWING AND BUILDING,
with no term walk involved.  This census re-derives all four from the proof
terms alone:

| lemma | item 212, by build | read here |
|---|---|---|
| `scanValue_ok_park_facts` | declines on one branch of a `split`, pays on the other | `DECLINE ∣ PAY ∣ VACUOUS ×3` |
| `back_col` | relays a structure FIELD of `KmSound` | `FIELD of premise#3` — and premise 3 is the `KmSound` |
| `close_col_of_base` | relays `back_col` | `FIELD of VIA KmSound.back_col` |
| `flowKeyHead` | relays into `flowNode_toBlockKey`, in **another module** | `VIA FlowKeyLift.flowNode_toBlockKey` |

A fifth agreement nobody asked for: item 212's fixpoint found **three**
decisions inside `keyctx_of_preprocess`, at StreamAccum `L26245`, `L26256` and
`L26278`.  This census reads that lemma's conjunct as `DECLINE ∣ DECLINE ∣
DECLINE ∣ PAY ∣ PAY`.

## What it found: two rows that read the same and mean the opposite

Compared conjunct by conjunct against `ConclusionCensus` under that census's own
grammar key — route PAY-arms against its `inl`, route DECLINE-arms against its
`inr` — **20 of 22 agree and 2 disagree**, and both disagreements are real:

* `scanValue_ok_park_facts#0` — route `1+1`, term `0+0`.  Item 212's row,
  re-derived.
* `explFrameValueLine#0` — route `0+0`, term `1+1`.  **New.**  The proof is
  `frameChainUnion (match h_expl with …) h_kslot`: the `Or.inl` and the
  `Or.inr trivial` the key counted are written for `frameChainUnion`'s optional
  PREMISE, and the lemma decides its own conclusion nowhere.

`flowVPack_of_close` reads `inl=1,inr=1 ∣ un=0,0` in `ConclusionCensus` and so
does `explFrameValueLine` — **the same row** — and one of them decides its
conjunct while the other decides nothing.  The `un` column cannot separate them:
it catches a payment made for a PREMISE only when the premise's skeleton differs
from every conclusion conjunct, and a relay's premise is the same proposition as
its conclusion by construction.

Checked against the compiler, predictions written before the patch (DOCS 213):

* narrowing `explFrameValueLine`'s conclusion to `∨ False` breaks it at
  **L6588**, the `frameChainUnion` application — NOT at its `Or.inl` (L6591) or
  its `Or.inr trivial` (L6597);
* narrowing `flowVPack_of_close`'s breaks it at **L962**, its own
  `Or.inr trivial`, and not at its `Or.inl` on L961, because `Or.inl x` still
  elaborates at `A ∨ False` — item 211's lesson, which is why `∨ False` is the
  falsifier and `P` alone is a control that cannot fail.

## What the same build says about counting errors

`explFrameValueLine` has **four** supply edges in item 212's census and the
narrowing refused **three** terms.  The fourth, `pendingProps#21` at L30289,
shares one application with the refused `entryPropsKeyPack_of_dispatch#10` at
L30241, and

```lean
def sink (_a : (0 = 0) ∨ True) (_b : (0 = 0) ∨ True) : Nat := 0
def BAD : (0 = 0) ∨ False := Or.inl rfl
example : Nat := sink BAD BAD      -- ONE error, not two
```

says why: within one application the first refused argument masks its siblings.
**A narrowing's error count is a LOWER bound on the number of supplies.**  At
item 212 the two agreed exactly — eight errors against an eight-entry seed — so
the gap is not visible until an application carries two of them.

## The blind spot, named rather than counted

Two of the 24 conjuncts have no route: `flowKeyRoute_of_open#1` and
`flowKeyRoute_of_root#1` sit under a `→` inside a paid payload, so reaching them
means entering a function the proof has not applied.  They are pinned by name
below, not swept into a number.

## The hole this leaves in item 212's own producer surface

`RelaySupplyCensus` pins thirteen constants as the module's producer surface.
Under the pipe test above, `Or.imp` (39 edges) and `dite` (4) are not producers
at all — they carry a decision made elsewhere — which is **43 of the 79 `VIA`
edges**, more than half.  The split is re-derived from item 212's own pinned
list below rather than asserted here; what it costs to follow those 43 to their
sources is the supply census's next item, not this one's. -/

namespace L4YAML.Tests.Guards.ConclusionRouteCensus

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus
  (isOptTy optBinders lamDepth Bnd resolve isMechanism splitShape Shape)
open L4YAML.Tests.Guards.ConclusionCensus (lefts conclusion skel sides)

/-- A step of the route from a conclusion to one of its `_ ∨ True` conjuncts. -/
inductive Step | l | r | ex | pay
deriving BEq, Inhabited

/-- The head of an expression, for naming what a route stopped at. -/
def leafHead (e : Expr) : String :=
  match e with
  | .proj s _ _ => s!"proj {s}"
  | .forallE .. => "→/∀"
  | .lam .. => "fun"
  | .letE .. => "let"
  | .sort .. => "Sort"
  | _ => match e.getAppFn with
    | .const c _ => s!"{c}"
    | .bvar _ => "bvar"
    | .fvar _ => "fvar"
    | _ => "other"

/-- One slot per `_ ∨ True` of a conclusion, in `ConclusionCensus.lefts` ORDER,
    holding the route to it or the reason there is none.  Keeping the order is
    what makes the two censuses comparable conjunct by conjunct. -/
partial def routes (e : Expr) (p : List Step) : Array (Option (List Step) × String) :=
  let blocked (x : Expr) (why : String) : Array (Option (List Step) × String) :=
    (Array.range (lefts x #[]).size).map (fun _ => (none, why))
  if isOptTy e then
    #[(some p.reverse, "")] ++ routes (e.getArg! 0) (.pay :: p)
  else if e.isAppOfArity ``And 2 then
    routes (e.getArg! 0) (.l :: p) ++ routes (e.getArg! 1) (.r :: p)
  else if e.isAppOfArity ``Exists 2 then
    match e.getArg! 1 with
    | .lam _ t b _ =>
        blocked (e.getArg! 0) "∃'s domain" ++ blocked t "∃'s domain" ++ routes b (.ex :: p)
    | _ => blocked e "∃ without a body"
  else blocked e (leafHead e)

/-- The matcher a `split`-generated SPLITTER came from.  The splitter is PRIVATE
    to the module that ran `split` and its matcher is not, so the private prefix
    has to come off before the matcher table will answer. -/
def matcherOfSplitter (env : Environment) : Name → Option Name
  | .str p "splitter" =>
      let m := Lean.privateToUserName p
      if Lean.Meta.isMatcherCore env m then some m else none
  | _ => none

def isMechD (env : Environment) (g : Name) : Bool :=
  (matcherOfSplitter env g).isSome || isMechanism env g

partial def foralls : Expr → Nat
  | .forallE _ _ b _ => foralls b + 1
  | _ => 0

partial def teleTypes : Expr → Array Expr → Array Expr
  | .forallE _ t b _, acc => teleTypes b (acc.push t)
  | _, acc => acc

/-- A splitter's alternatives sit where its matcher's do; their binder counts are
    read off the SPLITTER's own telescope, because `split` adds the negative
    hypotheses the matcher does not have. -/
def shapeD (env : Environment) (g : Name) : Option Shape :=
  match splitShape env g with
  | some s => some s
  | none =>
    match matcherOfSplitter env g with
    | some m =>
        match Lean.Meta.getMatcherInfoCore? env m, env.find? g with
        | some i, some ci =>
            let bs := teleTypes ci.type #[]
            let first := i.numParams + 1 + i.numDiscrs
            some ⟨i.numParams, i.numDiscrs, i.numAlts,
              (Array.range i.numAlts).map (fun k =>
                if h : first + k < bs.size then foralls bs[first + k] else 0)⟩
        | _, _ => none
    | none => none

/-- An arm closed by refuting its own hypotheses decides nothing. -/
def isVacuous : Name → Bool
  | ``False.elim | ``False.rec | ``absurd | ``Empty.elim | ``Empty.rec => true
  | .str _ s => s == "noConfusion"
  | _ => false

/-- Item 212's `resolve`, refined for the downward direction: a structure
    PROJECTION is named as a FIELD rather than as a producer, and an arm closed
    by `False.elim` or a `noConfusion` is VACUOUS rather than a producer. -/
def resolveDown (env : Environment) (st : Array Bnd) (n d : Nat) (e : Expr) : String :=
  match e with
  | .proj s i _ => s!"FIELD {s}#{i}"
  | _ =>
    match e.getAppFn with
    | .const c _ =>
        if isVacuous c then "VACUOUS"
        else if (env.getProjectionFnInfo? c).isSome then s!"FIELD {c}"
        else (resolve env (isMechD env) st n d e 24).how
    | _ => (resolve env (isMechD env) st n d e 24).how

/-- Follow `path` from a proof term to the conjunct it addresses, and resolve
    what decides it there — one answer per arm of every case split on the way. -/
partial def down (env : Environment) (self : Name) (n : Nat) :
    Array Bnd → List Step → Expr → Nat → Array String
  | _, _, _, 0 => #["DEEP"]
  | st, path, e, fuel+1 =>
    let leaf (e : Expr) : Array String :=
      let r := resolveDown env st n st.size e
      #[if path.isEmpty || r == "VACUOUS" then r else "ALL " ++ r]
    match e with
    | .mdata _ e' => down env self n st path e' fuel
    | .lam bn t b _ => down env self n (st.push { name := bn, opt := isOptTy t, val := none }) path b fuel
    | .letE bn t v b _ =>
        down env self n (st.push { name := bn, opt := isOptTy t, val := some v, dep := st.size }) path b fuel
    | e@(.app _ _) =>
        let f := e.getAppFn
        let args := e.getAppArgs
        let arg (i : Nat) (p : List Step) : Array String :=
          if h : i < args.size then down env self n st p args[i] fuel else leaf e
        match f with
        | .lam .. => Id.run do
            -- a beta-redex: `have x := v; body`
            let d0 := st.size
            let mut st := st
            let mut body := f
            let mut i := 0
            repeat
              match body, (if h : i < args.size then some args[i] else none) with
              | .lam bn t b _, some a =>
                  st := st.push { name := bn, opt := isOptTy t, val := some a, dep := d0 }
                  body := b; i := i + 1
              | _, _ => break
            return down env self n st path body fuel
        | .const g _ =>
            -- ROUTE: the conclusion's own introduction forms
            if g == ``Or.inl then
              match path with
              | .pay :: rest => arg 2 rest
              | _ => leaf e
            else if g == ``Or.inr then
              match path with
              | .pay :: _ => #["PARENT-DECLINED"]
              | _ => leaf e
            else if g == ``And.intro then
              match path with
              | .l :: rest => arg 2 rest
              | .r :: rest => arg 3 rest
              | _ => leaf e
            else if g == ``Exists.intro then
              match path with
              | .ex :: rest => arg 3 rest
              | _ => leaf e
            -- PIPES, checked BEFORE the case-split forms: `Eq.ndrec` — what
            -- `subst` leaves behind — is named like a recursor and is not a
            -- case split.
            else if g == ``Or.imp then arg 6 path
            else if g == ``Or.imp_left || g == ``Or.imp_right then arg 4 path
            else if g == ``Eq.mpr || g == ``Eq.mp || g == ``cast then arg 3 path
            else if g == ``Eq.ndrec || g == ``Eq.rec then arg 3 path
            else if g == ``id then arg 1 path
            -- the two branch forms a tactic leaves behind
            else if g == ``dite || g == ``ite then (arg 3 path) ++ (arg 4 path)
            else if isMechD env g then
              match shapeD env g with
              | some info => Id.run do
                  let firstAlt := info.numParams + 1 + info.numDiscrs
                  let lastAlt := firstAlt + info.numAlts
                  let major := info.numParams + info.numDiscrs
                  -- matched on FIELDS, not positionally: `Res` has grown a
                  -- field in each of items 214, 215, 216 and 217, and every
                  -- one of them broke a positional pattern here first.
                  let disc := if h : major < args.size then
                      (let r := resolve env (isMechD env) st n st.size args[major] 24
                       match r.how, r.tgt with
                       | "RELAY", some j => s!"premise#{j}"
                       | d, _ =>
                           if d.startsWith "FIELD of " then (d.splitOn " of ").getLast! else d)
                    else "?"
                  let trailing := if lastAlt < args.size then
                      args.extract lastAlt args.size else #[]
                  let mut out : Array String := #[]
                  for idx in [firstAlt:min lastAlt args.size] do
                    let d0 := st.size
                    let mut st := st
                    let mut body := args[idx]!
                    let mut i := 0
                    let k := info.altNumParams[idx - firstAlt]!
                    repeat
                      match body with
                      | .lam bn t b _ =>
                          if i < k then
                            st := st.push { name := bn, opt := isOptTy t, val := none,
                                            src := s!"FIELD of {disc}" }
                          else
                            let v := if h : i - k < trailing.size then some trailing[i - k] else none
                            let gsrc : String := if v.isSome then "" else s!"GEN of {disc}"
                            st := st.push { name := bn, opt := isOptTy t, val := v,
                                            src := gsrc, dep := d0 }
                          body := b; i := i + 1
                      | _ => break
                    out := out ++ down env self n st path body fuel
                  return out
              | none => leaf e
            else leaf e
        | _ => leaf e
    | e => leaf e

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- One conclusion conjunct: where it is, what decides it, and the key
    `ConclusionCensus` counts it under. -/
structure Row where
  lemma_ : Name
  idx    : Nat
  hows   : Array String
  key    : Array Name
deriving Inhabited

/-- Every optional CONCLUSION conjunct of the module declaring `anchor`, with
    what decides it, plus the count of constants whose value has fewer leading
    lambdas than their type has binders. -/
def rows (anchor : Name) : CommandElabM (Array Row × Nat) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? anchor
  let mut out : Array Row := #[]
  let mut skipped := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if (env.getProjectionFnInfo? nm).isSome then continue
    let c := conclusion ci.type
    if (lefts c #[]).isEmpty then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let (_, n) := optBinders ci.type
    if lamDepth v < n then skipped := skipped + 1; continue
    let rs := routes c []
    let cs := lefts c #[]
    for h : i in [0:rs.size] do
      let key := if h : i < cs.size then skel cs[i] else #[]
      match rs[i] with
      | (some path, _) => out := out.push ⟨nm, i, (down env nm n #[] path v 4096).qsort, key⟩
      | (none, why) => out := out.push ⟨nm, i, #[s!"UNREACHABLE under {why}"], key⟩
  return (out, skipped)

/-- A combinator that carries a decision rather than making one. -/
def isPipeName : String → Bool
  | "Or.imp" | "Or.imp_left" | "Or.imp_right" | "Eq.mpr" | "Eq.mp" | "cast"
  | "id" | "dite" | "ite" => true
  | _ => false

end L4YAML.Tests.Guards.ConclusionRouteCensus

namespace L4YAML.Tests.Guards.ConclusionRouteCensus

/-- The route census, pinned, one line per optional conclusion conjunct in
    `ConclusionCensus`'s own order — 24 of them, the same 24 that census counts
    (27 since item 300: `flowOpen_marker`, the stamp lemma's twin, decides its
    conclusion the same way, and `back_col` and `close_col_of_base` carry the
    base slot's marker reading as a second optional conjunct, a FIELD read
    like the stamp's).
    A proof that stops deciding its own conjunct, or starts, moves a line here;
    so does a tactic swap that puts a new combinator between the conclusion and
    the term that decides it, because the new combinator will read as a
    producer until it is named a pipe above. -/
-- 2026-10-20 (item 309): 27 → 24 — `frameChainUnion`, `flowVPack_of_close` and `explFrameValueLine` conclude in
-- `∨ alt` (generic in the alternative) and leave the `∨ True` survey.
def expectedRows : List String :=
  ["back_col#0 :: FIELD of premise#3",
   "back_col#1 :: FIELD of premise#3",
   "close_col_of_base#0 :: FIELD of VIA KmSound.back_col",
   "close_col_of_base#1 :: FIELD of VIA KmSound.back_col",
   "dedent_cover_of_landing#0 :: DECLINE | DECLINE | DECLINE | PAY",
   "flowKeyHead#0 :: VIA L4YAML.Proofs.FlowKeyLift.flowNode_toBlockKey",
   "flowKeyRoute_of_open#0 :: DECLINE | DECLINE | DECLINE | DECLINE | PAY | PAY",
   "flowKeyRoute_of_open#1 :: UNREACHABLE under →/∀",
   "flowKeyRoute_of_open#2 :: DECLINE | DECLINE | PARENT-DECLINED | PARENT-DECLINED | \
PARENT-DECLINED | PARENT-DECLINED | PAY",
   "flowKeyRoute_of_open#3 :: PARENT-DECLINED | PARENT-DECLINED | PARENT-DECLINED | \
PARENT-DECLINED | PAY | PAY",
   "flowKeyRoute_of_open#4 :: DECLINE | DECLINE | PARENT-DECLINED | PARENT-DECLINED | \
PARENT-DECLINED | PARENT-DECLINED | PAY",
   "flowKeyRoute_of_root#0 :: DECLINE | DECLINE | PAY | PAY",
   "flowKeyRoute_of_root#1 :: UNREACHABLE under →/∀",
   "flowKeyRoute_of_root#2 :: DECLINE | DECLINE | PARENT-DECLINED | PARENT-DECLINED | PAY",
   "flowKeyRoute_of_root#3 :: PARENT-DECLINED | PARENT-DECLINED | PAY | PAY | PAY | PAY | PAY",
   "flowKeyRoute_of_root#4 :: DECLINE | DECLINE | PARENT-DECLINED | PARENT-DECLINED | PAY",
   "flowOpen_floor_at_prep#0 :: DECLINE | PAY",
   "flowOpen_marker#0 :: DECLINE | DECLINE | PAY",
   "flowOpen_stamp#0 :: DECLINE | DECLINE | PAY",
   "keyctx_of_preprocess#0 :: DECLINE | DECLINE | DECLINE | PAY | PAY",
   "markerctx_of_landing#0 :: DECLINE | DECLINE | DECLINE | PAY",
   "nodocctx_of_preprocess#0 :: DECLINE | DECLINE | DECLINE | PAY | PAY",
   "scanValue_ok_park_facts#0 :: DECLINE | PAY | VACUOUS | VACUOUS | VACUOUS",
   "suffixctx_of_landing#0 :: DECLINE | DECLINE | DECLINE | PAY"]

/-- The tally, with the census's own refusals beside it.  `skipped` counts
    constants whose value has fewer leading lambdas than their type has binders.
    `DEEP`, `OTHER`, `OOB` or an `ALL` prefix appearing here would mean the walk
    stopped short of the conjunct and read whatever it was standing on; none
    does.  Item 300: `positions` 24 → 27 — `FIELD` +2 (`back_col#1`,
    `close_col_of_base#1`, the base slot's marker reading) and `SPLIT` +1
    (`flowOpen_marker#0`, the stamp lemma's twin). -/
-- 2026-10-20 (item 309): `positions` 27 → 24, `SPLIT` 19 → 17, `VIA` 2 → 1 — `frameChainUnion`, `flowVPack_of_close` and
-- `explFrameValueLine` conclude in `∨ alt` and leave the `∨ True` survey.
def expectedTally : String :=
  "positions=24 skipped=0 [FIELD=4, SPLIT=17, UNREACHABLE=2, VIA=1]"

/-- **The cross-instrument control.**  Route PAY-arms against `ConclusionCensus`'s
    `inl`, route DECLINE-arms against its `inr`, conjunct by conjunct under that
    census's own grammar key.  Twenty agree — twenty-three since item 300,
    whose three new conjuncts (`flowOpen_marker#0`, `back_col#1`,
    `close_col_of_base#1`) read alike under both.  The two that do not are the
    whole finding of item 213: one census reads a lemma that decides nothing as
    paying and punting, and the other reads a lemma that pays and punts as
    neither. -/
-- 2026-10-20 (item 309): `agree` 23 → 21 and `explFrameValueLine`'s row gone — its conclusion is `∨ alt`, outside the survey.
def expectedCross : List String :=
  ["agree=21",
   "scanValue_ok_park_facts#0 route=1+1 term=0+0"]

/-- **Item 212's producer surface, split by the pipe test**, re-derived from that
    census's OWN pinned lists rather than counted again here.  ~~Of its 79 `VIA`
    edges, 43 name a combinator that decides nothing.~~  **Item 214 followed the
    43**, so the supply census reports no pipe rows at all and this half of the
    pin would now pass vacuously; it is restated against what replaced them.

    The two censuses reconcile on item 212's published figure: the surviving
    producer surface (`producers`) plus everything the pipes landed on
    (`landed`) is the 79 `VIA` edges item 212 pinned before either direction
    could follow a pipe, plus **item 295's one**: `slot_ride`'s key route is a
    `VIA flowKeyRoute_of_root` edge (`RelaySupplyCensus.expectedProducers`), so
    `producers` reads 37 and `total` 80.  `landed-producers=0` is the finding:
    **not one of the 43 reaches a producer.**  The landing table's own parts are
    summed here too, so a row added to it without its total moving fails.  If
    item 212's lists move, its gate fails before this one does. -/
-- 2026-10-20 (item 307, second chain): back to `landed=43 total=80` — the content route's `h_vpack` was an
-- `.imp` (a landed producer) for one chain and is a `match` now.
-- 2026-10-21 (item 311): `landed` 43 → 45, `landed-producers` 0 → 2, `total` 80 → 82 — the two flow closes hand
-- `flowVPack_of_close resume.vslot` into the content park through `.imp id PackAlt.ofGateClose` (the frame's named
-- alternative into the park's); a pipe whose right map is a lemma lands as a producer, and that lemma is lane (d)'s stub.
-- 2026-10-21 (item 313): `landed` 45 → 54, `landed-producers` 2 → 3, `total` 82 → 91 — the content lane's transports are
-- `Or.imp` pipes with `PackAlt.step_content` on the right, landing in the park the content step builds.
-- 2026-10-21 (item 320): `landed` 54 → 55, `total` 91 → 92 — `accum_block_on_closeThenBlock`'s `h_seqFramesV` lands in the
-- new park through `.imp id (PackAlt.step_blockEntry …)`, the relay item 319's payments surfaced; producers stand.
def expectedPipeSplit : String :=
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; five `match` blocks deleted): PIPE producers 46 → 47, total 109 → 110 (`h_refused` is one more Or.elim producer).
  -- 2026-10-26 (item 366): producers 47 → 49, total 110 → 112 — the two `h_outer` arguments of
  -- `accum_block_on_closeThenBlock` now carry a produced witness (`Classical.em … |>.elim`).
  -- 2026-10-28 (item 380, PR #146 review): producers 49/11 → 32/10, landed 63 → 68, total 112 → 100 — `Or.elim` is a
  -- two-arm split now: its 17 `VIA` edges leave the producer surface (the distinct producer `Or.elim` with them); the
  -- five whose arms disagree land as splits, the twelve whose arms agree are collapsed edges and are counted nowhere here.
  "pipes=0/0 producers=32/10 landed=68 landed-producers=0 total=100"

end L4YAML.Tests.Guards.ConclusionRouteCensus

open Lean Elab Command L4YAML.Tests.Guards.ConclusionRouteCensus in
run_cmd do
  let env ← getEnv
  let (rs, skipped) ← rows (ns ++ `flowKeyRoute_of_root)
  let strip (s : String) := s.replace "L4YAML.Proofs.StreamAccum." ""
  let got := (rs.map (fun r =>
    s!"{r.lemma_.getString!}#{r.idx} :: {
      String.intercalate " | " (r.hows.toList.map strip)}")).qsort.toList
  if got != expectedRows then
    throwError "the conclusion ROUTE census moved.\nexpected ({expectedRows.length}):\n{
      String.intercalate "\n" expectedRows}\ngot ({got.length}):\n{
      String.intercalate "\n" got}"
  let mut tally : Std.HashMap String Nat := {}
  for r in rs do
    let k := if r.hows.size > 1 then "SPLIT" else (r.hows[0]!.splitOn " ").head!
    tally := tally.insert k ((tally.getD k 0) + 1)
  let gotTally := s!"positions={rs.size} skipped={skipped} {
    (tally.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotTally != expectedTally then
    throwError "the route census's TALLY moved.\nexpected: {expectedTally}\ngot:      {gotTally}"
  -- the cross-instrument control
  let mut dis : Array String := #[]
  let mut agree := 0
  for r in rs do
    if r.hows.size == 1 && r.hows[0]!.startsWith "UNREACHABLE" then continue
    let some ci := env.find? r.lemma_ | continue
    let some v := ci.value? (allowOpaque := true) | continue
    let count (side : Name) : Nat :=
      (((L4YAML.Tests.Guards.ConclusionCensus.sides side v #[]).map
        L4YAML.Tests.Guards.ConclusionCensus.skel).filter (· == r.key)).size
    let pay := (r.hows.filter (· == "PAY")).size
    let dec := (r.hows.filter (· == "DECLINE")).size
    if (pay, dec) == (count ``Or.inl, count ``Or.inr) then agree := agree + 1
    else dis := dis.push s!"{r.lemma_.getString!}#{r.idx} route={pay}+{dec} term={
      count ``Or.inl}+{count ``Or.inr}"
  let gotCross := s!"agree={agree}" :: dis.qsort.toList
  if gotCross != expectedCross then
    throwError "the CROSS-INSTRUMENT control moved.\nexpected ({expectedCross.length}):\n{
      String.intercalate "\n" expectedCross}\ngot ({gotCross.length}):\n{
      String.intercalate "\n" gotCross}"
  -- item 212's producer surface, split by the pipe test
  let mut pipeE := 0; let mut pipeC := 0; let mut prodE := 0; let mut prodC := 0
  for row in L4YAML.Tests.Guards.RelaySupplyCensus.expectedProducers do
    match row.splitOn " " with
    | [cnt, "VIA", g] =>
        let k := (cnt.toNat?).getD 0
        if isPipeName g then pipeE := pipeE + k; pipeC := pipeC + 1
        else prodE := prodE + k; prodC := prodC + 1
    | _ => throwError "item 212's producer row is not `<n> VIA <name>`: {row}"
  -- and what item 214's landing table says became of the pipes
  let lnd := L4YAML.Tests.Guards.RelaySupplyCensus.expectedPipeLanding
  let tok := lnd.splitOn " "
  let num (s : String) : Nat := (((s.splitOn "=").getLast!).toNat?).getD 0
  let landed := num (tok.headD "")
  let landedProds := num (tok.getD 1 "")
  let parts := (((lnd.splitOn "[").getLast!).replace "]" "").splitOn ", "
  let partSum := parts.foldl (fun a x => a + num x) 0
  if partSum != landed then
    throwError "item 214's landing table does not sum to its own total: {
      partSum} in {parts.length} rows against piped={landed}"
  let gotSplit := s!"pipes={pipeE}/{pipeC} producers={prodE}/{prodC} landed={
    landed} landed-producers={landedProds} total={prodE + landed}"
  if gotSplit != expectedPipeSplit then
    throwError "the PIPE split of item 212's producer surface moved.\nexpected: {
      expectedPipeSplit}\ngot:      {gotSplit}"
