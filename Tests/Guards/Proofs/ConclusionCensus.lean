import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The census over CONCLUSIONS (DOCS items 201, 202)

Item 198 ran a census over the pending park's CONSTRUCTORS, asking which of
them carried both bottoms; item 200 ran one over their APPLICATION SITES,
asking which sites paid a field and punted its own weakening.  Both items
recorded, in the same words, the row neither could reach:

> Both censuses run over the park family.  Neither runs over lemma
> CONCLUSIONS, so `flowKeyRoute_of_root` — which carries a value-line-bottomed
> resume conjunct and punts it — is still unmeasured.  **A census over
> conclusions is the instrument that would find it, and nobody has built one.**

This is that instrument.  For every non-internal constant of
`L4YAML/Proofs/Production/StreamAccum.lean`, split the TYPE into its binder
telescope and its conclusion, collect the `_ ∨ True` components of the
CONCLUSION, and read the VALUE for an `Or.inl` and an `Or.inr` of each.  A
conjunct with no `Or.inl` anywhere in the proof is one no arm of that lemma
ever pays — which is a different question from "is this field punted at some
site", and is the one the park censuses cannot ask.

**What it reads.**  16 lemmas state an optional conjunct in their conclusion,
24 conjuncts between them — of which **18 have a paying arm and 6 have none**.
**Item 213: that number is right under the route census too, and names a
DIFFERENT 18.**  Two rows swap and the total does not move —
`scanValue_ok_park_facts` is in this census's 6 and pays on one branch of a
`split`, `explFrameValueLine` is in its 18 and decides nothing at all.  A count
can be right for the wrong reason, and this one was, for twelve items.
Three lemmas carry more than one, and they are the same lemma seen three ways:
`flowKeyRoute_of_open` (5), `flowKeyRoute_of_root` (5) and the field that
carries both (`FlowBaseRoutes.key`, 5, excluded below as a projection).
**Conclusion-level optionality in this module is the flow-key lane and nothing
else.**

~~**All six unpaid rows are the RELAY blind spot below** (item 203).~~  Item
202 read seven, of which exactly one was unpaid and not a relay —
`flowKeyRoute_of_open`'s value-line resume — and item 203 paid it.  ~~So the
first column's remainder is entirely the instrument's own blind spot and not
the file's.~~  **Measured at item 212 and false.**  Narrowing the four
single-conjunct rows to `_ ∨ False` and building reads FOUR different
mechanisms, not one — and one of them is a decline:

* `scanValue_ok_park_facts` **DECLINES**, at StreamAccum `L18463`, on one
  branch of a `split`.  It is not relayed at all; its `Or.inl` and its
  `Or.inr` are both written in its own proof and both land in the `un` column
  — which is item 202's KEY, a third time, and not the relay.  **The number
  that refutes the sentence above is `un=1,1` in the pin below, put there to
  catch exactly this and read by nobody.**
* `back_col` relays a structure FIELD of `KmSound`, so what decides it is
  every site that BUILDS a `KmSound` — items 198 and 200's census, not this
  one's.
* `close_col_of_base` relays `back_col` with `Or.imp` and is repaired by
  narrowing `back_col` alongside it: it pays exactly when `back_col` does, and
  nothing here can say whether that is.
* `flowKeyHead` relays into `flowNode_toBlockKey`, which is in
  `FlowKeyLift` — **another module**, which `subjects` filters out by
  construction.  The census cannot follow it however hard it looks.

The supply direction now has its own instrument
(`Tests/Guards/Proofs/RelaySupplyCensus.lean`, item 212), which follows a
`have` through its beta-redex and a case split into its alternatives.  ~~The
CONCLUSION direction — these four — is still followed by hand, by narrowing
and building.~~  **Item 213 built it:**
`Tests/Guards/Proofs/ConclusionRouteCensus.lean` walks a conclusion's own
addresses — left and right of an `∧`, inside an `∃`, inside a paid payload —
and re-derives all four rows above from the proof terms alone, along with the
three decisions item 212 found inside `keyctx_of_preprocess` by building.

## The key, and why item 202 had to correct it

Two conjuncts are "the same" here when their head-constant SKELETONS agree,
and item 201 took the skeleton over ALL constants.  That key is
instantiation-SENSITIVE, which the docstring it was written in denied: a
conjunct paid at a COMPUTED index carries the index's own constants
(`HAdd.hAdd`, `instHAdd`, `OfNat.ofNat`, …) into the skeleton and matches
nothing.  `flowKeyRoute_of_open` pays at `k = nc + 1 + w`, so item 201 read
four of its five fields wrong and reported the module as 15-paying/9-unpaid
when it was 16/8 — and handed item 202 a plan sentence ("`_of_open`'s four
never-paid conjuncts") of which two were paid all along.

The key here keeps only constants under `L4YAML`, which an index cannot
introduce, and falls back to the full skeleton where that leaves nothing.  The
correction is not asserted: `attribControl` below reads BOTH keys and pins the
lemmas where they disagree, so the module states for itself that exactly one
lemma is instantiation-sensitive and that the grammar key attributes strictly
more of its sites.

## The two blind spots that remain, named

* A conjunct **relayed** with `Or.imp` (`h.imp f id`), or discharged by passing
  a lemma whose own conclusion is the `∨ True`, writes no literal `Or.inl` or
  `Or.inr` and reads `inl=0 inr=0` — neither paid nor punted.  ~~`flowKeyHead`,
  `back_col`, `close_col_of_base` and `scanValue_ok_park_facts` are the first
  kind and the two `head` conjuncts are the second, and all six DO pay.~~
  **Item 212: three kinds, not one, and `scanValue_ok_park_facts` is not
  relayed and does not pay — see the correction above.**  The blind spot
  itself is real, and is the same one item 199 measured in the `[210]` flip, in
  a second instrument: **a relay is invisible to anything that counts terms**,
  because it writes the answer down once and the writing is not at either end.
  Its SIZE is now measured rather than described: 345 of the module's 659
  optional-premise supply edges, 52 %, are decided somewhere other than the
  site that writes them (`RelaySupplyCensus`).
* `inr` counts punt SITES, not "always punted".  A payment that keeps a
  fallback arm — every payment made through a `match` on an optional premise —
  leaves the `inr` count exactly where it was.  Item 201's own payment moved
  `flowKeyRoute_of_root`'s two rows `inl=0 → inl=1` and `inr=2 → inr=2`.

So the number to read is the FIRST column.  The `un=` column is the third
thing a term census cannot attribute — an `Or.inl`/`Or.inr` written for an
optional PREMISE rather than a conclusion conjunct — pinned rather than
filtered, so a payment the key stops seeing has to move a number here.

**Item 213: `un` catches such a payment only when the premise's SKELETON
differs from every conclusion conjunct, and a relay's premise is the same
proposition as its conclusion by construction.**  `explFrameValueLine` is
`frameChainUnion (match h_expl with …) h_kslot`: its `Or.inl` and its
`Or.inr trivial` are written for `frameChainUnion`'s optional premise, the key
attributes both to the conclusion, and the row reads `inl=1,inr=1 | un=0,0` —
character for character the row `flowVPack_of_close` reads, which decides its
own conjunct on two arms.  Narrowing says so: `explFrameValueLine` breaks at
its `frameChainUnion` call (StreamAccum `L6588`) and `flowVPack_of_close` at
its own `Or.inr trivial` (`L962`).  The route census separates them; this one
cannot, and the `un` column is not the place to look for it. -/

namespace L4YAML.Tests.Guards.ConclusionCensus

open Lean Elab Command

/-- Item 311: the optional's right disjunct — a literal `True`, or the family's NAMED alternative,
    `PackAlt sc` / `PackAltG g`, `True` by definition until the lanes pay it. -/
def isAltTrue (b : Expr) : Bool :=
  b.isConstOf ``True || b.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt ||
    b.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG

/-- The left-hand sides of every `_ ∨ True`, in traversal order. -/
partial def lefts : Expr → Array Expr → Array Expr
  | .app (.app (.const ``Or _) x) (.const ``True _), acc => lefts x (acc.push x)
  -- item 311: the named alternative `PackAlt sc` / `PackAltG g` reads as `True`
  | .app (.app (.const ``Or _) x) (.app (.const ``L4YAML.Proofs.StreamAccum.PackAlt _) _), acc => lefts x (acc.push x)
  | .app (.app (.const ``Or _) x) (.app (.const ``L4YAML.Proofs.StreamAccum.PackAltG _) _), acc => lefts x (acc.push x)
  | .app f a, acc => lefts a (lefts f acc)
  | .lam _ t b _, acc => lefts b (lefts t acc)
  | .forallE _ t b _, acc => lefts b (lefts t acc)
  | .letE _ t v b _, acc => lefts b (lefts v (lefts t acc))
  | .mdata _ e, acc => lefts e acc
  | .proj _ _ e, acc => lefts e acc
  | _, acc => acc

/-- Every `α` of an `Or.inl`/`Or.inr` at `(α := α) (β := True)`, for one side.
    Both sides are read: see the blind spots above. -/
partial def sides (side : Name) : Expr → Array Expr → Array Expr
  -- Item 311: `β` is `True` or the family's named alternative (`PackAlt sc` / `PackAltG g`).
  | e@(.app (.app (.app (.const s _) a) b) _), acc =>
      let rest := match e with
        | .app f x => sides side x (sides side f acc)
        | _ => acc
      if s == side && isAltTrue b then rest.push a else rest
  | .app f a, acc => sides side a (sides side f acc)
  | .lam _ t b _, acc => sides side b (sides side t acc)
  | .forallE _ t b _, acc => sides side b (sides side t acc)
  | .letE _ t v b _, acc => sides side b (sides side v (sides side t acc))
  | .mdata _ e, acc => sides side e acc
  | .proj _ _ e, acc => sides side e acc
  | _, acc => acc

/-- Head constants in order.  Bound variables drop out, so the telescope's own
    names do not matter — but an INSTANTIATED index does not, which is what
    `skel` below has to fix. -/
partial def skelRaw : Expr → Array Name → Array Name
  | .const n _, acc => acc.push n
  | .app f a, acc => skelRaw a (skelRaw f acc)
  | .lam _ t b _, acc => skelRaw b (skelRaw t acc)
  | .forallE _ t b _, acc => skelRaw b (skelRaw t acc)
  | .letE _ t v b _, acc => skelRaw b (skelRaw v (skelRaw t acc))
  | .mdata _ e, acc => skelRaw e acc
  | .proj _ _ e, acc => skelRaw e acc
  | _, acc => acc

/-- The GRAMMAR vocabulary of an expression: its head constants under
    `L4YAML`, which a `Nat` index cannot introduce, and the full skeleton where
    that leaves nothing to compare. -/
def skel (e : Expr) : Array Name :=
  let raw := skelRaw e #[]
  let g := raw.filter (`L4YAML).isPrefixOf
  if g.isEmpty then raw else g

partial def conclusion : Expr → Expr
  | .forallE _ _ b _ => conclusion b
  | e => e

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- The constants this census reads: non-internal, in `StreamAccum`, with a
    value, stating at least one optional conclusion conjunct.  Structure
    PROJECTIONS are excluded — they carry no proof term, so every conjunct of a
    projection would read as unpaid. -/
def subjects : CommandElabM (Array (Name × Expr × Expr)) := do
  let env ← getEnv
  let modIdx := env.getModuleIdxFor? (ns ++ `flowKeyRoute_of_root)
  let mut out := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if (env.getProjectionFnInfo? nm).isSome then continue
    if (lefts (conclusion ci.type) #[]).isEmpty then continue
    let some v := ci.value? (allowOpaque := true) | continue
    out := out.push (nm, ci.type, v)
  return out

/-- One row per lemma: `name inl=a,inr=b … | un=x,y`, one field per conclusion
    conjunct in the conclusion's own order, then the `Or.inl`/`Or.inr` sites the
    key attributes to no conjunct. -/
def census : CommandElabM (Array String) := do
  let mut rows : Array String := #[]
  for (nm, ty, v) in ← subjects do
    let cs := lefts (conclusion ty) #[]
    let ks := cs.map skel
    if ks.size != (ks.foldl (fun (a : Array (Array Name)) k =>
        if a.contains k then a else a.push k) #[]).size then
      throwError "two conjuncts of {nm} share a census key — the key has stopped \
        telling them apart, and the counts below would silently merge"
    let ps := (sides ``Or.inr v #[]).map skel
    let qs := (sides ``Or.inl v #[]).map skel
    let mut out := s!"{nm.getString!}"
    for k in ks do
      out := out ++ s!" inl={(qs.filter (· == k)).size},inr={(ps.filter (· == k)).size}"
    rows := rows.push (out ++ s!" | un={(qs.filter (!ks.contains ·)).size},{
      (ps.filter (!ks.contains ·)).size}")
  return rows.qsort

/-- **The instrument's own control** (item 202).  The census under item 201's
    RAW key beside the grammar key, reported as the number of `Or.inl`/`Or.inr`
    sites each one ATTRIBUTES to a conclusion conjunct.  The two agree except
    where a lemma pays at a computed index; the row below is the whole list of
    lemmas where they differ, and it is what says the correction is still
    doing something. -/
def attribControl : CommandElabM (Array String) := do
  let mut rows : Array String := #[]
  for (nm, ty, v) in ← subjects do
    let cs := lefts (conclusion ty) #[]
    let read (key : Expr → Array Name) : Nat × Nat :=
      let ks := cs.map key
      ((((sides ``Or.inl v #[]).map key).filter (ks.contains ·)).size,
       (((sides ``Or.inr v #[]).map key).filter (ks.contains ·)).size)
    let (rl, rr) := read (skelRaw · #[])
    let (gl, gr) := read skel
    if (rl, rr) != (gl, gr) then
      rows := rows.push s!"{nm.getString!} raw={rl}+{rr} grm={gl}+{gr}"
  return rows.qsort

/-- The pinned census.  A conjunct that gains or loses a paying arm moves a
    row here; item 201 moved `flowKeyRoute_of_root`'s third and fifth from
    `inl=0` to `inl=1`, item 202 moved `flowKeyRoute_of_open`'s fourth from
    `inl=0,inr=2` to `inl=2,inr=0` — paid on BOTH arms, no punt site left — and
    item 203 moved its FIFTH from `inl=0,inr=2` to `inl=1,inr=2`, the compact
    arm paying and the landing arm keeping the punt it has no face for.  The
    `un` column moved with it: a second `cases` on an optional PREMISE is two
    more sites the key is not meant to attribute, which is what that column is
    for.

    Item 300 adds `flowOpen_marker`, the stamp lemma's twin (`inl=1,inr=2 |
    un=1,1`, the same case split), and a second optional conclusion to
    `back_col` and `close_col_of_base` — the base slot's marker reading beside
    its stamp — paid and declined nowhere in their bodies (`inl=0,inr=0`), as
    the stamp's is.

    Item 304 moves `flowKeyRoute_of_root`'s `un` from 3,5 to 3,6: the value-line
    stacks are `KeyFrames`, whose `resumeAt` hands its consumer a mapping OR a
    sequence continuation, and the value-line resume `h_resV_land` splits on it
    — the sequence case is one more `Or.inr` site the key does not attribute,
    as item 201's second `cases` was. -/
-- 2026-10-20 (item 309): 17 → 14 — `frameChainUnion`, `flowVPack_of_close` and `explFrameValueLine`
-- conclude in `∨ alt` (generic in the alternative) and leave the `∨ True` survey.
def expected : List String :=
  ["back_col inl=0,inr=0 inl=0,inr=0 | un=0,0",
   "close_col_of_base inl=0,inr=0 inl=0,inr=0 | un=0,0",
   "dedent_cover_of_landing inl=1,inr=3 | un=0,0",
   -- item 385: the deeper landing's node route at the mapping park (`h_valF`) and
   -- the `-` park (`closeF`); the `inr`s are the dedent (and the frameless park).
   -- item 386: the mapping helper's second `inl` is the SIBLING at `k = nv` (empty
   -- value, `resumeAt` the head frame); its `inr`s are now the popped/col-0 dedent
   -- and the frameless park — the no-pop dedent closes by `absurd`.
   "deeperLandingResume inl=2,inr=2 | un=0,0",
   "deeperLandingResumeSeq inl=1,inr=1 | un=0,0",
   "flowKeyHead inl=0,inr=0 | un=0,0",
   "flowKeyRoute_of_open inl=2,inr=4 inl=0,inr=0 inl=1,inr=2 inl=2,inr=0 inl=1,inr=2 | un=3,3",
   "flowKeyRoute_of_root inl=2,inr=2 inl=0,inr=0 inl=1,inr=2 inl=5,inr=0 inl=1,inr=2 | un=3,5",
   "flowOpen_floor_at_prep inl=1,inr=1 | un=0,0",
   "flowOpen_marker inl=1,inr=2 | un=1,1",
   "flowOpen_stamp inl=1,inr=2 | un=1,1",
   "keyctx_of_preprocess inl=2,inr=3 | un=0,0",
   "markerctx_of_landing inl=1,inr=3 | un=1,1",
   "nodocctx_of_preprocess inl=2,inr=3 | un=0,0",
   "scanValue_ok_park_facts inl=0,inr=0 | un=1,1",
   "suffixctx_of_landing inl=1,inr=3 | un=1,1"]

/-- The one lemma whose payments instantiate an index, and the sites item 201's
    key could not attribute: 3 of this lemma's 8 `Or.inl` and 6 of its 10
    `Or.inr`, against 6 and 8.  At item 201's own numbers the gap was 2+7
    against 3+10, which is the reading that made its `_of_open` row wrong, and
    item 203's payment widened it by one more `Or.inl` — a payment at
    `k = nc + 1 + w` is exactly what the raw key cannot see.  An empty list
    here would mean the grammar key had stopped earning its keep; a longer one,
    that a second lemma had started computing its key. -/
def expectedControl : List String :=
  ["flowKeyRoute_of_open raw=3+6 grm=6+8"]

run_cmd do
  let got ← census
  if got.toList != expected then
    throwError "the conclusion census moved.\nexpected ({expected.length}):\n{
      String.intercalate "\n" expected}\ngot ({got.size}):\n{
      String.intercalate "\n" got.toList}"
  let ctl ← attribControl
  if ctl.toList != expectedControl then
    throwError "the census's INSTANTIATION control moved.\nexpected ({
      expectedControl.length}):\n{String.intercalate "\n" expectedControl}\ngot ({
      ctl.size}):\n{String.intercalate "\n" ctl.toList}"

end L4YAML.Tests.Guards.ConclusionCensus
