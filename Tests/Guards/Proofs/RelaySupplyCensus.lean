import L4YAML.Proofs.Production.StreamAccum

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # The census over RELAYS (DOCS item 212)

Four censuses stand before this one, and all four count TERMS: over the pending
park's CONSTRUCTORS (item 198), over their APPLICATION SITES (200), over lemma
CONCLUSIONS (201), and over the conclusions' own key (202).  Items 199, 201 and
211 each recorded the same gap, in the same words:

> A conjunct **relayed** with `Or.imp`, or discharged by passing a lemma whose
> own conclusion is the `∨ True`, writes no literal `Or.inl` or `Or.inr` and
> reads `inl=0 inr=0` — neither paid nor punted.  **A relay is invisible to
> anything that counts terms**, because it writes the answer down once and the
> writing is at neither end.  What would see through it is a census that
> follows a conjunct's VALUE through the relays that carry it, and nobody has
> built one.

This is that instrument, for the SUPPLY direction: for every application in
`StreamAccum` of a constant with a `_ ∨ True` binder, resolve the argument in
that position to what actually decides it.

## What it follows, and what each answer means

* `PAY` / `DECLINE` — an `Or.inl` / `Or.inr` written at the call site, on every
  branch there is.  These are the only two a term census can see, and they are
  ~~**314 of 659**~~ **315 of 659** edges — item 216's descent found one more,
  a chain of six splitters that agree.  **Item 218: a `PAY` is an answer about
  the PROOF, and it does not promise the site survives a narrowing.**  The one
  chain of six is a `have` whose ascribed type is the wide `_ ∨ True` and whose
  proof pays it on every branch; narrowing the field it fills breaks the USE
  site while the census is right that nothing declines there.  It is named in
  `expectedCollapsedEdge` because N-218 broke at exactly it.
* `VIA g` — the argument is the result of calling `g`, so `g`'s own conclusion
  decides it.  This is the case items 199–211 called a relay and never counted.
  ~~It is the largest resolvable share after the two above, and `Or.imp` — the
  combinator item 201 named — is **39** of it.~~  **Item 213: `Or.imp` and
  `dite` are PIPES and decide nothing**, and **item 214 followed all 43 of
  them** — `resolve` now has the pipe list (`pipeArg`), so this row is **36**
  edges over 11 constants and every one of them names a lemma.  It is the
  SMALLEST of the four hidden shares, not the largest.
* `SPLIT g` — the argument is the result of a case split at the call site, so
  the site decides it on two branches rather than one.  ~~At **156** this is the
  largest hidden share~~ — **it was never a hidden share at all, and this bullet
  said so before anything measured it.**  `resolve` enters every arm now (item
  216), and of the **328** leaves under the **155** that survive, **168 are
  `DECLINE` and 160 are `PAY` and NONE is anything else**: a split is the site
  writing both answers, once per branch.  What the row hides is not a decider —
  it is the BRANCH, and `expectedSplitLanding` is where that is counted.  156
  splits, 66 distinct splitters, 151 of them two-armed and not one of them a
  single-constructor destructuring.  **Item 217 took the branch**: **145 of the
  155 branch on a value the CALLER supplied**, and **99 of those on a premise
  that is itself a `_ ∨ True`** — the site writes both answers because its own
  caller may have declined.  Only TEN branch on a fact the site derives, and
  `expectedSiteDecided` names every one of them.  **Item 218 asked whether the
  declining branch can be SELECTED** and joined this row against the supply
  rows for the first time: of the 36 `(lemma, premise)` pairs behind the 99,
  **not one has a DECLINE arm nothing can select** — `dead=0` — and only **8**
  have a caller that declines them where they are branched on.  See
  `expectedDeclineReach`.
* `RELAY` — the argument is one of the enclosing constant's OWN binders, so the
  decision belongs to ITS callers.  This is the only shape item 211 looked for.
  **68**, of which 12 arrived through a pipe — **and this row is not what a
  relay costs.**  Item 217 measured a further **99** edges that read `SPLIT`
  and branch on one of these same optional binders: the site cases on whether
  its caller declined and answers in kind, which is a relay with a case
  analysis around it.  See `expectedSplitBranch`.
* `FIELD of g#i on d` — the argument is field `i` of the constructor that split
  `d`, so items 198 and 200's census decides it and not this one.  **58**, and
  53 of them are a field of the pending park the caller was handed: the row
  reads `FIELD of PendingNode.casesOn#23 on RELAY` and `pendingProps`' own
  telescope names index 23 `h_closeFE`, which is the premise being supplied.
  Field-to-same-field, on every one of the 53.  **Item 218 followed the field
  to its CONSTRUCTOR** (`altCtorField`; all **58** resolve) and that is where
  the answer turned out to live: `expectedDeclineReach`'s **`parkHop`** counts
  the branch premises whose supply is a park field and nothing else, and it is
  the majority of them — which is why `RELAY` and `FIELD` are followed and
  everything else is a terminal.
* `LOCAL …` — a binder this census will not name.  **27**, and unlike item 212's
  82 this is not a blind spot with a sentence attached: 20 are lambdas in one
  lemma's alternative bodies and 7 sit under a SATURATED pipe, which transports
  a function nobody applies.  Both are honest locals.  The 55 that used to swell
  this row were under an OVER-APPLIED pipe — see `peelPipe`.

A `have`-bound hypothesis is followed through its beta-redex, a `let` is bound
and followed, and a case split's alternatives are entered with their constructor
fields marked and their generalized binders bound to the matcher's own trailing
arguments — so `have h := f x` reads `VIA f` and not `LOCAL h`.  That single step is the whole
difference from reading the compiler's error text, which prints the BINDER NAME
at every one of them and cannot tell a premise from a `have`.

## The reading that made this item

Item 211 falsified `content_dispatch_routed`'s optional contexts one at a time
and read, off the compiler's own error text, that of its 8 call sites **seven
relay their own `h_keyctx`** — and concluded that `KeyPackPunt.noKeyContext`
"is not missing an input, it is behind a RELAY".  All seven errors do print
`h_keyctx`.  Neither `accum_content_pending` nor `accum_content_on_noPending`
HAS an `h_keyctx` binder: both write `have h_keyctx := keyctx_of_preprocess …`,
which this census reads as `VIA`.  **Six of the seven call a producer; one
relays.**  A name is not a provenance.

Checked against the compiler, by narrowing to a fixpoint (DOCS item 212):
narrowing the premise to `∨ False` breaks 8 sites; also narrowing
`keyctx_of_preprocess`'s conclusion REPAIRS six of them — which a site that
truly relayed a premise could not be, since it would not be calling that lemma
— and the remaining supply closes at **four** decisions, three of them inside
`keyctx_of_preprocess` and one `Or.inr trivial`.

## The `∨ True` binder of `content_dispatch_routed` nobody had counted

`optTargets` below reads the optional binders off the TYPE rather than off a
hand-written list.  `content_dispatch_routed` has **six**, not the five item
211's script enumerated: `h_ref` was never in it. -/

namespace L4YAML.Tests.Guards.RelaySupplyCensus

open Lean Elab Command

/-- Item 311: the family's alternative is NAMED — `PackAlt sc` (and `PackAltG g` over a flow gate),
    `True` by definition until the lanes pay it; an optional binder is one whose right disjunct is
    `True` or that name. -/
def isOptTy (e : Expr) : Bool :=
  e.isAppOfArity ``Or 2 && ((e.getArg! 1).isConstOf ``True || (e.getArg! 1).isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt || (e.getArg! 1).isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG)

/-- `(index, name)` of every optional binder of a type, with the arity: `_ ∨ True`, or
    (item 309) `_ ∨ alt` where `alt` is an earlier binder of the same type NAMED `alt` —
    the generic alternative of `frameChainUnion`, `flowVPack_of_close` and
    `explFrameValueLine`, which their callers instantiate (to `True` today, to
    `ExplicitValueRefused sc` as 12.3.4.2 narrows the family).  A bare variable alone
    is not enough: a first cut accepted any variable right disjunct and read 241 edges
    into binders that are optional in no sense of this census. -/
def optBinders (ty : Expr) : Array (Nat × Name) × Nat := Id.run do
  let mut out := #[]; let mut t := ty; let mut i := 0; let mut names : Array Name := #[]
  repeat match t with
    | .forallE n a b _ =>
        let generic := a.isAppOfArity ``Or 2 &&
          (match a.getArg! 1 with
           | .bvar k => k < names.size && names[names.size - 1 - k]! == `alt
           | _ => false)
        if isOptTy a || generic then out := out.push (i, n)
        names := names.push n
        i := i + 1; t := b
    | _ => break
  return (out, i)

partial def lamDepth : Expr → Nat
  | .lam _ _ b _ => lamDepth b + 1
  | _ => 0

abbrev OptMap := Std.HashMap Name (Array (Nat × Name))

/-- A binder in scope: its name, whether its type is `_ ∨ True`, the VALUE it
    is bound to when it is a `have`/`let`/beta-redex binder, where it came from
    when it is a case split's own, and `dep` — the DEPTH ITS VALUE LIVES AT.

    `dep` is what makes a multi-binder beta-redex readable.  Every argument of
    `(fun x y z => b) a₁ a₂ a₃` lives at the depth the redex was found at, but
    the binders sit at that depth, +1 and +2, so following `a₂` at `y`'s stack
    INDEX reads its de Bruijn variables one binder off.  The two agree for the
    first binder and only for the first, which is why this went unseen: every
    beta-redex item 212 met was a one-binder `have`.  Item 215's `peelPipe`
    peels up to thirteen at a time — see `expectedTally`. -/
structure Bnd where
  name   : Name
  opt    : Bool
  val    : Option Expr
  src    : String := ""
  dep    : Nat := 0
  /-- When this binder is a constructor FIELD, the enclosing constant's binder
      index the split's discriminant ROOTS at — so a field of a relayed datum
      still names the premise it was carved out of.  Item 217: 46 of the 145
      relay-rooted splits reach their premise only through this. -/
  srcTgt : Option Nat := none
  /-- When this binder is a constructor FIELD, the CONSTRUCTOR it is a field of
      and the binder index of that field in the constructor's own type.
      `srcTgt` names the premise the datum ARRIVED at, and for a park field
      that premise is a `PendingNode` rather than a `_ ∨ True`, so the supply
      chase dead-ends there; this names the field itself, where the park's
      CONSTRUCTION sites can be asked what they put in it.  Item 218:
      `expectedDeclineReach`'s `parkHop` counts the branch premises that reach
      their decline only through this. -/
  srcFld : Option (Name × Nat) := none
deriving Inhabited

/-- Which argument of a PIPE carries the decision.  Item 213 named these in the
    DOWNWARD direction and this census had no list: before item 214 a pipe was
    reported as `VIA <the combinator>`, which names what carried the answer and
    not what decided it.  `Or.imp` alone was **39 of the 79 `VIA` edges**.

    `dite`/`ite` are deliberately NOT here.  Downward they are pipes, because a
    route census collects EVERY route and takes both arms; upward this census
    has to name ONE decider, and a two-armed decision written at the call site
    is what it already calls `SPLIT` — see `isTwoArm`. -/
def pipeArg : Name → Option Nat
  | ``Or.imp => some 6
  | ``Or.imp_left | ``Or.imp_right => some 4
  | ``Eq.mpr | ``Eq.mp | ``cast => some 3
  | ``Eq.ndrec | ``Eq.rec => some 3
  | ``id => some 1
  | _ => none

/-- A pipe with two arms: the site decides, on two branches.  Both arms of all
    four occurrences in `StreamAccum` disagree, so reporting the common answer
    when the arms agree would be a knob with nothing behind it.  Item 216
    descended them and the four still disagree — two instruments, one sentence,
    and this is the cross-check. -/
def isTwoArm : Name → Bool
  | ``dite | ``ite | ``Or.elim => true
  | _ => false

/-- `(major, firstAlt, numAlts, binders-per-alt)` for a two-arm pipe, so
    `resolve` can enter its arms the way it enters a matcher's.

    `ite` is deliberately absent.  `dite`'s arms each bind the decision's proof
    and `ite`'s bind nothing, so the two need different shapes — and `ite`
    occurs **zero** times in this module (measured, item 216: the 156 splits are
    66 distinct splitters and `ite` is not one of them).  A shape nothing
    instantiates is not evidence, so `ite` keeps reading `SPLIT ite`, which is
    what it read before.

    `Or.elim` (item 380, PR #146 review): `(Classical.em p).elim (fun _ => …) (fun h => …)` is a
    two-armed decision written at the call site — the builders' `h_res_land` decides the no-pop
    landing in its first arm — and reading it as `VIA Or.elim` hid both arms behind one leaf.
    Its major is the disjunction (`{a b c}` implicit, then `h`), its two arms bind one proof each,
    exactly `dite`'s shape shifted by the three implicits. -/
def twoArmShape : Name → Option (Nat × Nat × Nat × Array Nat)
  | ``dite => some (1, 3, 2, #[1, 1])
  | ``Or.elim => some (3, 4, 2, #[1, 1])
  | _ => none

/-- The loose de Bruijn indices of an expression, relative to where it sits.
    Item 217 uses them for one question only: does an `Or.inl`/`Or.inr`'s
    argument refer to ANYTHING in scope, or is it self-contained? -/
partial def looseRefs : Expr → Nat → Array Nat → Array Nat
  | .bvar k, off, acc => if k ≥ off then acc.push (k - off) else acc
  | .app f a, off, acc => looseRefs a off (looseRefs f off acc)
  | .lam _ t b _, off, acc => looseRefs b (off+1) (looseRefs t off acc)
  | .forallE _ t b _, off, acc => looseRefs b (off+1) (looseRefs t off acc)
  | .letE _ t v b _, off, acc =>
      looseRefs b (off+1) (looseRefs v off (looseRefs t off acc))
  | .mdata _ e, off, acc => looseRefs e off acc
  | .proj _ _ e, off, acc => looseRefs e off acc
  | _, _, acc => acc

/-- `closed` when the `Or` constructor's argument mentions nothing in scope —
    `Or.inr trivial` is the whole of it — and `free` when it hands back
    something it was given.  **This is what makes a premise narrowing
    predictable by line**: a `closed` DECLINE cannot break when the premise its
    split branches on is narrowed, because it never touches it.  Item 217
    measured 164 of the 168 `DECLINE` leaves `closed` and used the count to
    forecast N-217's error set before the edit; see `expectedSplitBranch`. -/
def orArgRefs (args : Array Expr) : String :=
  if h : 2 < args.size then
    (if (looseRefs args[2] 0 #[]).isEmpty then "closed" else "free")
  else "?"

/-- What `resolve` found: the answer, the enclosing constant's binder index when
    the answer is `RELAY`, the pipes crossed on the way, the SPLITS crossed, and
    the LEAVES of the decision tree when the answer is still a split.  `pipes`
    and `splits` are what make the two landings re-derivable instead of
    asserted, and `leaves` is what makes `SPLIT` interrogable at all: before
    item 216 the row named the splitter and stopped. -/
structure Res where
  how     : String
  tgt     : Option Nat := none
  pipes   : List String := []
  splits  : List String := []
  leaves  : Array String := #[]
  /-- The DISCRIMINANT chain of a surviving split, with relay indices: WHICH
      BRANCH is taken is decided by this, and by nothing the site writes.
      Item 217. -/
  disc    : String := ""
  /-- The enclosing constant's binder index the discriminant chain roots at,
      when it roots at one at all — 145 of the 155 do. -/
  rootTgt : Option Nat := none
  /-- One entry per entry of `leaves`: `orArgRefs` at that leaf. -/
  leafSrc : Array String := #[]
  /-- One entry per entry of `leaves`: the leaf's PATH through the nested
      splitters, `<splitter>#<arm>` per hop (item 380, PR #146 review) — what
      names ONE declined arm among several, e.g. the two builders' no-pop arm
      `Or.casesOn#0>Or.elim#0` against the four other `DECLINE` leaves of the
      same split. -/
  leafPath : Array String := #[]
  /-- Item 218: the constructor field a `FIELD` answer was carved from. -/
  fldTgt  : Option (Name × Nat) := none
deriving Inhabited

/-- Where a split's alternatives sit in its argument list, and how many binders
    of each are constructor FIELDS.  Covers `match` auxiliaries and the
    `casesOn` recursors `obtain`/`rcases` elaborate to. -/
structure Shape where
  numParams    : Nat
  numDiscrs    : Nat
  numAlts      : Nat
  altNumParams : Array Nat
deriving Inhabited

def splitShape (env : Environment) (g : Name) : Option Shape :=
  match Lean.Meta.getMatcherInfoCore? env g with
  | some i => some ⟨i.numParams, i.numDiscrs, i.numAlts, i.altNumParams⟩
  | none =>
    match g with
    | .str t "casesOn" =>
      match env.find? t with
      | some (.inductInfo iv) =>
          let fields := iv.ctors.map fun c =>
            match env.find? c with
            | some (.ctorInfo cv) => cv.numFields
            | _ => 0
          some ⟨iv.numParams, iv.numIndices + 1, iv.ctors.length, fields.toArray⟩
      | _ => none
    | _ => none

/-- The CONSTRUCTOR an alternative of a `casesOn` belongs to, and the binder
    index in that constructor's own type which alternative-binder `i` names.

    A matcher returns `none` and says so: its alternatives are patterns, not
    constructors, and inventing a constructor for one would be a knob.  Measured
    (item 218): all **58** `FIELD` edges in this module resolve, so the census
    does not currently need the matcher case — which is a fact about this
    module and not a property of the instrument. -/
-- 2026-10-29 (item 394, option B): accum_content_pending's match auxiliary renumbered
-- (match_1_55 → match_1_57) by the cover relays' new `match` arms; the edge itself is unchanged.
def altCtorField (env : Environment) (g : Name) (alt : Nat) (i : Nat) :
    Option (Name × Nat) :=
  match g with
  | .str t "casesOn" =>
    match env.find? t with
    | some (.inductInfo iv) =>
        match iv.ctors[alt]? with
        | some c => some (c, iv.numParams + i)
        | none => none
    | _ => none
  | _ => none

/-- The last two components of a (de-privatised) name: `Or.casesOn`,
    `accum_content_pending.match_1_57`, `dite` — the splitter as a leaf path hop. -/
def tailName (c : Name) : String :=
  match Lean.privateToUserName c with
  | .str (.str _ a) b => s!"{a}.{b}"
  | u => u.toString

/-- What supplies an argument.  `d` is the number of binders in scope where the
    argument lives; `st` is the binder stack OUTERMOST first, so the enclosing
    constant's own `n` binders are `st[0] … st[n-1]` and `.bvar k` names
    `st[d-1-k]`.  **That indexing is only meaningful while `st.size == d`**, so
    every place this function pushes a binder truncates `st` to `d` first:
    following a value at its own `dep` leaves the stack longer than the depth,
    and item 216 measured the skew reachable (8 occurrences) and moving zero
    edges.  A bound value is followed at the depth it was bound at, which is
    what keeps the de Bruijn indices inside it meaningful.  A PIPE is followed
    into the argument that carries the decision, and a lambda is entered rather
    than reported — three `Or.imp` edges and all eight `dite` arms stop at a
    `BETA` otherwise.

    A SPLIT is entered on every arm, and the answers are joined: agreeing arms
    give one answer and the splitter joins `splits`, disagreeing arms keep the
    `SPLIT` label and their answers become `leaves`.  There is no third rule,
    because a split that answers differently on different branches HAS no single
    answer — see `expectedSplitLanding`. -/
partial def resolve (env : Environment) (isMech : Name → Bool) (st : Array Bnd)
    (n : Nat) : Nat → Expr → Nat → Res
  | _, _, 0 => { how := "DEEP" }
  | d, e, fuel+1 =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if f.isConstOf ``Or.inl then { how := "PAY", leafSrc := #[orArgRefs args] }
    else if f.isConstOf ``Or.inr then
      { how := "DECLINE", leafSrc := #[orArgRefs args] }
    else match f with
      | .const c _ =>
          match pipeArg c with
          | some i =>
              if h : i < args.size then
                let r := resolve env isMech st n d args[i] fuel
                { r with pipes := c.toString :: r.pipes }
              else { how := s!"PIPE-UNDERAPPLIED {c}", pipes := [c.toString] }
          | none =>
            if isTwoArm c || isMech c then
              let pipes0 := if isTwoArm c then [c.toString] else []
              let shp := if isTwoArm c then twoArmShape c else
                match splitShape env c with
                | some i => some (i.numParams + i.numDiscrs,
                                  i.numParams + 1 + i.numDiscrs, i.numAlts, i.altNumParams)
                | none => none
              match shp with
              | none => { how := s!"SPLIT {c}", pipes := pipes0 }
              | some (major, firstAlt, numAlts, altNP) =>
                if firstAlt + numAlts > args.size then { how := s!"SPLIT {c}", pipes := pipes0 }
                else Id.run do
                  -- enter every arm: a split's answer is one answer PER BRANCH,
                  -- so the only thing that can be reported as ONE answer is a
                  -- split whose arms all agree — and exactly one of the 156
                  -- does.  The rest keep the `SPLIT` label and carry their
                  -- leaves, which is what `expectedSplitLanding` reads.
                  let dres := if h : major < args.size then
                      resolve env isMech st n d args[major] fuel else { how := "?" }
                  -- the arm LABEL stays `dres.how`, so every `src` string this
                  -- census has ever printed is byte-identical; the INDEXED
                  -- chain rides beside it in `disc`, and `rootTgt` is where it
                  -- bottoms out.  Item 217.
                  let disc := dres.how
                  let dchain :=
                    if dres.how == "RELAY" then s!"RELAY#{dres.tgt.getD 0}"
                    else if dres.disc != "" then s!"{dres.how} on {dres.disc}"
                    else dres.how
                  let rootTgt := if dres.how == "RELAY" then dres.tgt else dres.rootTgt
                  let mut arms : Array Res := #[]
                  for idx in [firstAlt:firstAlt+numAlts] do
                    let need := altNP[idx - firstAlt]!
                    let mut stA := st.extract 0 d
                    let mut dA := d
                    let mut body := args[idx]!
                    for j in [0:need] do
                      match body with
                      | .lam bn t b _ =>
                          let lbl := if isTwoArm c then s!"GUARD of {c}#{j}"
                                     else s!"FIELD of {c}#{j} on {disc}"
                          stA := stA.push
                            { name := bn, opt := isOptTy t, val := none, src := lbl,
                              srcTgt := rootTgt,
                              srcFld := altCtorField env c (idx - firstAlt) j }
                          body := b; dA := dA + 1
                      | _ => pure ()
                    arms := arms.push (resolve env isMech stA n dA body fuel)
                  let keys := (arms.map (fun r => s!"{r.how}|{r.tgt}")).qsort.toList.eraseDups
                  if keys.length == 1 then
                    let r0 := arms[0]!
                    return { r0 with splits := c.toString :: r0.splits }
                  else
                    let lv := arms.foldl
                      (fun a r => a ++ (if r.leaves.isEmpty then #[r.how] else r.leaves)) #[]
                    let ls := arms.foldl (fun a r => a ++
                      (if r.leaves.isEmpty then
                         (if r.leafSrc.isEmpty then #[""] else r.leafSrc)
                       else r.leafSrc)) #[]
                    let lp := Id.run do
                      let mut acc : Array String := #[]
                      for h : k in [:arms.size] do
                        let r := arms[k]
                        if r.leaves.isEmpty then acc := acc.push s!"{tailName c}#{k}"
                        else
                          for i in [:r.leaves.size] do
                            acc := acc.push s!"{tailName c}#{k}>{r.leafPath[i]?.getD "?"}"
                      return acc
                    return { how := s!"SPLIT {c}", pipes := pipes0, leaves := lv,
                             disc := dchain, rootTgt := rootTgt, leafSrc := ls, leafPath := lp }
            else { how := s!"VIA {c}" }
      | .bvar k =>
          if d - 1 - k < st.size ∧ k < d then
            let j := d - 1 - k
            if j < n then { how := "RELAY", tgt := some j, rootTgt := some j }
            else match st[j]!.val with
              | some v => resolve env isMech st n st[j]!.dep v fuel
              | none =>
                  if st[j]!.src != "" then
                    { how := st[j]!.src, rootTgt := st[j]!.srcTgt, fldTgt := st[j]!.srcFld }
                  else { how := s!"LOCAL {st[j]!.name}{if st[j]!.opt then ":opt" else ":?"}" }
          else { how := "OOB" }
      | .letE bn t v b _ =>
          -- three arms of the 155 splits are a `let`, and item 212's `resolve`
          -- had no case for them: they read `OTHER`, which is the census
          -- declining to answer.  Bind and continue, exactly as `walk` does.
          resolve env isMech ((st.extract 0 d).push { name := bn, opt := isOptTy t, val := some v, dep := d })
            n (d+1) b fuel
      | .lam .. =>
          -- a beta-redex, or a bare function reached through a pipe: bind what
          -- arguments there are and resolve the body at the new depth.  The
          -- arguments all live at `d0`, not at the depth each binder sits at.
          -- `st` is truncated to `d` first: `st[d-1-k]` is only the binder a
          -- `.bvar k` names while INDEX == DEPTH, and following a value at its
          -- own `dep` leaves `st` longer than `d`.  Item 216 measured this
          -- reachable (8 occurrences) and moving ZERO edges.
          let d0 := d
          let rec peel (st : Array Bnd) (body : Expr) (i : Nat) (d : Nat) : Res :=
            match body with
            | .lam bn t b _ =>
                let v := if h : i < args.size then some args[i] else none
                peel (st.push { name := bn, opt := isOptTy t, val := v, dep := d0 }) b (i+1) (d+1)
            | body => resolve env isMech st n d body fuel
          peel (st.extract 0 d) f 0 d
      | _ => { how := "OTHER" }

/-- Caller `C` supplies callee `g`'s optional premise `idx` with `how`. -/
structure Edge where
  caller : Name
  callee : Name
  idx    : Nat
  how    : String
  tgt    : Option Nat := none
  pipes  : List String := []
  splits : List String := []
  leaves : Array String := #[]
  leafPath : Array String := #[]
  disc    : String := ""
  rootTgt : Option Nat := none
  leafSrc : Array String := #[]
  /-- Item 218: the constructor field a `FIELD` supply was carved from. -/
  fldTgt  : Option (Name × Nat) := none
deriving Inhabited

def appEdges (env : Environment) (isMech : Name → Bool) (self : Name) (n : Nat)
    (st : Array Bnd) (g : Name) (obs : Array (Nat × Name)) (args : Array Expr) :
    Array Edge :=
  Id.run do
    let mut out : Array Edge := #[]
    for (i, _) in obs do
      if h : i < args.size then
        let r := resolve env isMech st n st.size args[i] 24
        out := out.push { caller := self, callee := g, idx := i, how := r.how,
                          tgt := r.tgt, pipes := r.pipes, splits := r.splits,
                          leaves := r.leaves, disc := r.disc, rootTgt := r.rootTgt,
                          leafSrc := r.leafSrc, leafPath := r.leafPath, fldTgt := r.fldTgt }
      else out := out.push { caller := self, callee := g, idx := i, how := "UNDERAPPLIED" }
    return out

/-- The case-split MECHANISM, as opposed to a supply site. -/
def isMechanism (env : Environment) (g : Name) : Bool :=
  (Lean.Meta.isMatcherCore env g) ||
  (match g with
   | .str _ s => s == "casesOn" || s == "recOn" || s == "brecOn" || s == "rec"
                 || s == "below" || s == "ndrec" || s == "ndrecOn"
                 || s.startsWith "match_"
   | _ => false)

/-- A constant's arity, counted off its TYPE's leading binders.  An application
    carrying MORE arguments than this is OVER-APPLIED: what it returns is being
    used as a function, and for a PIPE that means the pipe is transporting a
    function to a beta-redex — see `peelPipe`. -/
def arityOf (env : Environment) (g : Name) : Nat :=
  match env.find? g with
  | some ci => (optBinders ci.type).2
  | none => 0

mutual

/-- An over-applied PIPE is a beta-redex with a pipe in the middle: the pipe
    transports a FUNCTION and the trailing arguments are what it is applied to.
    Peel the transported lambda against them, binding each binder to its value
    exactly as the plain beta-redex case does, and recording the depth those
    values live at.

    This is the shape 55 of item 214's 82 `LOCAL` edges were in, and it is NOT
    the shape item 214 forecast.  Item 214 predicted a pipe standing between a
    split and its alternative, to be descended and then shaped; the census
    reports ZERO such sites.  What is actually there is a `cases` whose whole
    motive was transported: `Eq.ndrec` with arity 6 carrying 10 to 19
    arguments, the extra ones being the park's own fields. -/
partial def peelPipe (env : Environment) (m : OptMap) (self : Name) (n : Nat)
    (trailing : Array Expr) (d0 : Nat) : Array Bnd → Expr → Nat →
    Array Edge → Array Edge
  | st, body, j, acc =>
    match body with
    | .lam bn t b _ =>
        if h : j < trailing.size then
          peelPipe env m self n trailing d0
            (st.push { name := bn, opt := isOptTy t, val := some trailing[j], dep := d0 }) b (j+1)
            (walk env m self n st trailing[j] acc)
        else walk env m self n st body acc
    | body =>
        walk env m self n st body
          ((trailing.extract j trailing.size).foldl
            (fun a x => walk env m self n st x a) acc)

/-- One alternative of a case split: its first `k` binders are constructor
    FIELDS of `disc`; the rest take the split's trailing arguments. -/
partial def walkAlt (env : Environment) (m : OptMap) (self : Name) (n : Nat)
    (st : Array Bnd) (k : Nat) (disc : String) (dtgt : Option Nat) (splitter : Name)
    (alt : Nat) (trailing : Array Expr) : Expr → Array Edge → Array Edge
  | e, acc => Id.run do
    let d0 := st.size
    let mut st := st
    let mut e := e
    let mut i := 0
    repeat
      match e with
      | .lam bn t b _ =>
          if i < k then
            st := st.push { name := bn, opt := isOptTy t, val := none,
                            src := s!"FIELD of {splitter}#{i} on {disc}", srcTgt := dtgt,
                            srcFld := altCtorField env splitter alt i }
          else
            let v := if h : i - k < trailing.size then some trailing[i - k] else none
            let gsrc : String := if v.isSome then "" else s!"GEN of {disc}"
            st := st.push { name := bn, opt := isOptTy t, val := v, src := gsrc, dep := d0 }
          e := b; i := i + 1
      | _ => break
    return walk env m self n st e acc

partial def walk (env : Environment) (m : OptMap) (self : Name) (n : Nat) :
    Array Bnd → Expr → Array Edge → Array Edge
  | st, .lam bn t b _, acc => walk env m self n (st.push { name := bn, opt := isOptTy t, val := none }) b acc
  | st, .forallE bn t b _, acc =>
      walk env m self n (st.push { name := bn, opt := isOptTy t, val := none }) b acc
  | st, .letE bn t v b _, acc =>
      walk env m self n (st.push { name := bn, opt := isOptTy t, val := some v, dep := st.size }) b
        (walk env m self n st v acc)
  | st, .mdata _ e, acc => walk env m self n st e acc
  | st, .proj _ _ e, acc => walk env m self n st e acc
  | st, e@(.app _ _), acc =>
      let f := e.getAppFn
      let args := e.getAppArgs
      match f with
      | .lam .. =>
          -- a beta-redex: `have x := v; body` and friends.  Binding the
          -- binders to their arguments is what makes a `have`-built hypothesis
          -- read as its producer instead of as a nameless local.
          let d0 := st.size
          let rec peel (st : Array Bnd) (body : Expr) (i : Nat) (acc : Array Edge) :
              Array Edge :=
            match body, (if i < args.size then some args[i]! else none) with
            | .lam bn t b _, some a =>
                peel (st.push { name := bn, opt := isOptTy t, val := some a, dep := d0 }) b (i+1)
                  (walk env m self n st a acc)
            | body, _ =>
                walk env m self n st body
                  ((args.extract i args.size).foldl
                    (fun a x => walk env m self n st x a) acc)
          peel st f 0 acc
      | .const g _ =>
          if h : (pipeArg g).isSome && arityOf env g < args.size
                 && (pipeArg g).get! < args.size then Id.run do
            -- the pipe treatment `resolve` has had since item 214, one level
            -- up: an over-applied pipe is a beta-redex and its trailing
            -- arguments are what the transported function receives.
            let i := (pipeArg g).get!
            let ar := arityOf env g
            let mut acc := acc
            for idx in [0:ar] do
              if idx != i then acc := walk env m self n st args[idx]! acc
            return peelPipe env m self n (args.extract ar args.size) st.size st
              args[i]! 0 acc
          else if isMechanism env g then
            match splitShape env g with
            | some info => Id.run do
                let firstAlt := info.numParams + 1 + info.numDiscrs
                let lastAlt := firstAlt + info.numAlts
                -- the major premise sits AFTER the indices: `params, motive,
                -- indices…, major`.  Reading `numParams + 1` reads the first
                -- INDEX of an indexed inductive — `PendingNode` has four, so
                -- every field of the park was labelled `of VIA Bool.false`.
                let major := info.numParams + info.numDiscrs
                let dres := if h : major < args.size then
                    resolve env (isMechanism env) st n st.size args[major] 24
                  else { how := "?" }
                let disc := dres.how
                let dtgt := if dres.how == "RELAY" then dres.tgt else dres.rootTgt
                let trailing := if lastAlt < args.size then
                    args.extract lastAlt args.size else #[]
                let mut acc := acc
                for idx in [0:args.size] do
                  let a := args[idx]!
                  if firstAlt ≤ idx && idx < lastAlt then
                    acc := walkAlt env m self n st info.altNumParams[idx - firstAlt]!
                      disc dtgt g (idx - firstAlt) trailing a acc
                  else acc := walk env m self n st a acc
                return acc
            | none => args.foldl (fun a x => walk env m self n st x a) acc
          else
            let acc := args.foldl (fun a x => walk env m self n st x a) acc
            match m[g]? with
            | none => acc
            | some obs => acc ++ appEdges env (isMechanism env) self n st g obs args
      | _ => args.foldl (fun a x => walk env m self n st x a) acc
  | _, _, acc => acc

end

def optMap : CommandElabM OptMap := do
  let env ← getEnv
  let mut mm : OptMap := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    let (obs, _) := optBinders ci.type
    if obs.isEmpty then continue
    mm := mm.insert nm obs
  return mm

def ns : Name := `L4YAML.Proofs.StreamAccum

/-- Every optional-premise supply edge inside the module declaring `anchor`,
    with the count of constants whose value has fewer leading lambdas than
    their type has binders — the census refuses to read those, and says so. -/
def edges (anchor : Name) : CommandElabM (Array Edge × Nat) := do
  let env ← getEnv
  let m ← optMap
  let modIdx := env.getModuleIdxFor? anchor
  let mut acc : Array Edge := #[]
  let mut skipped := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if env.getModuleIdxFor? nm != modIdx then continue
    if isMechanism env nm then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let (_, n) := optBinders ci.type
    if lamDepth v < n then skipped := skipped + 1; continue
    acc := walk env m nm n #[] v acc
  return (acc, skipped)

end L4YAML.Tests.Guards.RelaySupplyCensus

namespace L4YAML.Tests.Guards.RelaySupplyCensus

open Lean Elab Command

/-- The head constant of binder `i` of `c`'s TYPE — read off the declaration
    and never off a proof term.  This is the INDEPENDENT artifact the
    discriminant column is checked against: `expectedSplitBranch`'s
    `agree=99/99` compares the splitter's own declared major type with the type
    of the premise the chain roots at, and the two censuses share no code path
    to reach them. -/
def binderHead (env : Environment) (c : Name) (i : Nat) : Name :=
  match env.find? c with
  | none => `NOCONST
  | some ci => Id.run do
      let mut t := ci.type
      let mut k := 0
      repeat
        match t with
        | .forallE _ ty b _ =>
            if k == i then return (ty.getAppFn.constName?.getD `NOTCONST)
            t := b; k := k + 1
        | _ => break
      return `SHORT

/-- The NAME of binder `i` of `c`'s type, for naming a branch's host premise. -/
def binderName (env : Environment) (c : Name) (i : Nat) : Name :=
  match env.find? c with
  | none => `NOCONST
  | some ci => Id.run do
      let mut t := ci.type
      let mut k := 0
      repeat
        match t with
        | .forallE nm _ b _ =>
            if k == i then return nm
            t := b; k := k + 1
        | _ => break
      return `SHORT

/-- The splitter's own major-premise index, so its DECLARED discriminant type
    can be read off its type rather than inferred from the application. -/
def majorOf (env : Environment) (c : Name) : Option Nat :=
  if isTwoArm c then (twoArmShape c).map (fun s => s.1)
  else (splitShape env c).map (fun i => i.numParams + i.numDiscrs)

/-- Whether binder `j` of `c` is itself one of the `_ ∨ True` premises. -/
def isOptBinder (env : Environment) (c : Name) (j : Nat) : Bool :=
  match env.find? c with
  | some ci => (optBinders ci.type).1.any (fun q => q.1 == j)
  | none => false

/-- Every supply edge, keyed by the premise it fills.  The join item 217 could
    not run: a split knows the premise `(caller, rootTgt)` its discriminant
    roots at, and a supply edge knows the premise `(callee, idx)` it fills, and
    both indices come from `optBinders`' single counter — so the two can be
    joined, and the join PARTITIONS the census (`accounted` below must equal
    `edges`, which is the control). -/
abbrev SupplyMap := Std.HashMap String (Array Edge)

def keyOf (c : Name) (i : Nat) : String := s!"{c}#{i}"

def supplyMap (es : Array Edge) : SupplyMap := Id.run do
  let mut m : SupplyMap := {}
  for e in es do
    let k := keyOf e.callee e.idx
    m := m.insert k ((m.getD k #[]).push e)
  return m

/-- Chase supply UPWARD to the labels it terminates in.  `RELAY` and `FIELD`
    decide nothing — the first hands the caller's own premise down, the second
    hands a park's field down — so both are followed; every other label is a
    terminal, and a `SPLIT`'s leaves come back tagged `br` so a decline written
    on one branch stays distinguishable from a flat one.

    **The `FIELD` hop is an OVER-APPROXIMATION and deliberately so.**  It
    collects every construction site of that constructor in the module, not only
    the ones that can reach this call site, so a `dead` verdict cannot be
    manufactured by a path the chase failed to find.  Where the constructor
    carries no optional field at all — `And.intro` and `Exists.intro` do not;
    those data were destructured out of a nested payload rather than out of a
    park — it falls back to `rootTgt`, the premise the whole nest arrived at.

    `seen` is per PATH: **8 of the 161 nodes' chases reach a cycle**, the
    documented one being the value-line carrier that funds the pack that funds
    the park again.  Without the guard this does not terminate. -/
partial def terminals (m : SupplyMap) (seen : Std.HashSet String) (k : String)
    (depth : Nat) : Std.HashSet String × Nat × Array String :=
  if seen.contains k then (({} : Std.HashSet String).insert "CYCLE", depth, #[])
  else
    let seen := seen.insert k
    match m[k]? with
    | none => (({} : Std.HashSet String).insert "ORPHAN", depth, #[])
    | some arr => Id.run do
        let mut out : Std.HashSet String := {}
        let mut d := depth
        let mut sites : Array String := #[]
        for e in arr do
          let hd := (e.how.splitOn " ").head!
          let up : Option String :=
            if hd == "RELAY" then e.tgt.map (keyOf e.caller)
            else if hd == "FIELD" then
              (match e.fldTgt.map (fun (c, i) => keyOf c i) with
               | some nk => if m.contains nk then some nk else e.rootTgt.map (keyOf e.caller)
               | none => e.rootTgt.map (keyOf e.caller))
            else none
          if hd == "RELAY" || hd == "FIELD" then
            match up with
            | some nk =>
                let (t, d2, si) := terminals m seen nk (depth + 1)
                for x in t.toList do out := out.insert x
                sites := sites ++ si
                d := max d d2
            | none => out := out.insert s!"{hd}-unresolved"
          else if hd == "SPLIT" then
            for lf in e.leaves do out := out.insert s!"br{(lf.splitOn " ").head!}"
            if e.leaves.any (fun lf => (lf.splitOn " ").head! == "DECLINE") then
              sites := sites.push e.caller.toString
          else
            out := out.insert hd
            if hd == "DECLINE" then sites := sites.push e.caller.toString
        return (out, d, sites)

def setStr (t : Std.HashSet String) : String :=
  String.intercalate "+" (t.toList.mergeSort (· ≤ ·))

/-- The first hop of a branch premise's supply chase, named.  A `FIELD` names
    the park field it was carved from (`pendingBlock.h_closeF`), which is the
    form the module's own comments use and therefore checkable against them by
    a route this census does not take. -/
def hopName (env : Environment) (e : Edge) : String :=
  match e.fldTgt with
  | some (c, i) =>
      -- the last TWO components: `PendingNode.pendingBlock`, `And.intro`.  One
      -- component alone renders `And.intro` as `intro`, which names nothing.
      let base := match c with
        | .str (.str _ a) b => s!"{a}.{b}"
        | _ => c.toString
      s!"{base}.{binderName env c i}"
  | none => match e.tgt with
            | some t => s!"{(binderName env e.caller t)}@{e.caller.getString!}"
            | none => "-"

/-- The supply census, pinned.  `DECLINE` and `PAY` are the two a term census
    can see; every other row is a supply it cannot.  ~~**345 of 659 edges — 52 %
    — are decided somewhere other than the site that writes them**~~ — **that
    sentence was wrong from the day it was written, and the `SPLIT` bullet forty
    lines above it says why**: a split IS decided at the site, on branches, and
    it was 156 of the 345.  Corrected by item 216, which entered the arms and
    found every one of the 328 leaves to be a `PAY` or a `DECLINE`: **189 of 659
    edges — 29 % — are decided somewhere other than the site**, and 470 are
    decided at it, 315 unconditionally and 155 per branch.  189 is the share
    items 199, 201 and 211 each described in a sentence and none could count.

    The COMPOSITION has moved three times and the walk has not gained or lost an
    edge: following the pipes (item 214) took `VIA` 79 → 36 and put the
    difference into `LOCAL` (+26), `RELAY` (+10) and `SPLIT` (+7); following the
    OVER-APPLIED ones (item 215) took `LOCAL` 82 → 27, 53 of them to `FIELD` and
    2 to `RELAY`; entering the arms (item 216) took `SPLIT` 156 → 155 and `PAY`
    43 → 44.  `edges=659` is the invariant that matters: if IT ever moves, the
    walk gained or lost an EDGE, which is a different event and a worse one.
    A row moving from hidden to visible, as one did here, is not that.
    `skipped` counts constants whose value has fewer leading lambdas than their
    type has binders — the census will not read those, and a rewrite that hides
    a proof from it has to move this number.  It moved once for a reason that is
    not a rewrite: v4.33.0 generated `FrameTail.toCtorIdx` beside `ctorIdx` for
    the derived enum — a lambda-less alias, which is why this census refused it
    — and v4.34.0 generates no such constant, so it left the module (31 → 30)
    and `edges=659` and every category held.  Isolating test:
    `scratchpad/l4yaml-434-migration/EnumAux.lean` under both toolchains.

    **Item 256 moved two DECLINEs and no edge**: the root `-`'s
    `pendingBlock.h_closeF` is a `PAY` (the seed's cover at floor 0,
    `DECLINE` 271 → 269 and `PAY` 44 → 45 with it) and the content sibling's
    is a `SPLIT` on `h_closeF_old` whose arms are a `PAY` and a `DECLINE`
    (`SPLIT` 155 → 156).  `edges=659` held, as it must.  **Item 257 moves one
    more DECLINE to a PAY**: the compact fill's `pendingBlock.h_closeF` (the
    literal from the slot's own top bound) — one edge, the fill's own
    application, `DECLINE` 269 → 268 and `PAY` 45 → 46; no split is added, so
    the split landing, the split branch and the collapsed edge stand.  **Item
    258 moves two more**: the entry park's compact and nested re-parks'
    `pendingBlock.h_closeF` (the same literal from the park's own top bound),
    one edge each, `DECLINE` 268 → 266 and `PAY` 46 → 48; no split is added.

    **Item 287 moves `edges` for the first time, and no walk lost an edge: a
    BINDER left the population.**  `accum_block_on_closeThenBlock`'s `h_vslot`
    was `_ ∨ True`; its right disjunct is the caller's reading of an inline
    residue now (DOCS item 287), so it is not an optional premise and its
    eleven supply edges are not this census's: the ten callers that wrote
    `Or.inr trivial` (`DECLINE` 265 → 255) and the value park's split on
    `h_vslot51` (`SPLIT` 156 → 155).  `edges` 659 → 648.

    **Item 288 moves `edges` again, for the same reason**:
    `PendingNode.pendingMapValue.h_vslot` declines with the stamp now, so its
    six supply edges leave too — the three stamped producers' `Or.inr trivial`
    (`DECLINE` 255 → 252), the two slot openers' `Or.inl` (`PAY` 49 → 47), and
    `compact_open_map`'s split (`SPLIT` 155 → 154).  `edges` 648 → 642.

    **Item 293 moves `skipped` alone, 30 → 31**: `live_of_dispatch`, which
    concludes in an arrow and case-splits before it introduces it, so its value
    has nine leading lambdas for ten binders — the shape of `stale_of_dispatch`,
    its twin, already among the thirty.  The 31 names, listed with the guard's
    own test: `scratchpad/l4yaml-row12-steps/357-relay-skipped.out`.

    **Item 295 moves `edges` 642 → 656, all in `accum_flow_open_depth0`**: two
    new applications of `flowKeyRoute_of_root` — `slot_ride`'s and the props
    arm's fallback — each decline its six optional faces (`DECLINE` +12), and
    `slot_ride` builds its frame field by field instead of through `mkv`, so
    `FlowBaseRoutes.mk` gains a key supplied VIA `flowKeyRoute_of_root`
    (`VIA` 36 → 37) and a declined `vslot` (`DECLINE` 264 → 265).  Each of the
    six binders reads 2 → 4 applications by the guard's own walk
    (`scratchpad/l4yaml-row12-steps/427-relaydump-295.out`).

    **Item 296 moves `edges` 656 → 660, `DECLINE` 265 → 269**: the two entry
    pack producers' frameless dedent exit applies `rootMapRoute_or_refused`
    and `rootMapRouteF_or_refused`, and each declines its one optional binder,
    `h_ref` (a dedenting landing completes no value).

    **Item 297 moves `edges` 660 → 664, `DECLINE` 269 → 273**: the same pair
    at the producers' `w ∉ ks` exit, `h_ref` declined for the same reason.

    **Item 300 moves `edges` 664 → 674, `DECLINE` 273 → 280, `PAY` 47 → 50**:
    `content_dispatch_routed`'s marker premise at its eight applications — the
    `---` arm pays, seven decline — and `km_push_at_open`'s `h_marker_new` at
    its two nested opens, each a refutation of the base-open premise (PAY). -/
-- 2026-10-20 (item 305): `DECLINE` 280 → 279, `SPLIT` 154 → 155 — `closeThenBlock`'s
-- compact arm pays the compact entry's value-line stack from the `?` slot's inner
-- pack (a `match` on `hkv`: PAY when the slot carries it) where item 200 left a
-- decline it had measured as payable and uninformative.
-- 2026-10-20 (item 306): `DECLINE` 279 → 273, `SPLIT` 155 → 161 — the two key-pack
-- builders' value-line stacks (`h_nodeFV`, `h_dframesV`) are paid from the entry
-- park's `h_closeFV_old` at the three entry-park calls in
-- `accum_content_on_pendingBlock_indented` (a `match`: PAY with the entry's level
-- pushed, DECLINE when the park has none) where item 108 left `Or.inr trivial`.
-- 2026-10-20 (item 307): `DECLINE` 273 → 268, `SPLIT` 161 → 166 — the three γ roots' `h_vpack`
-- and the two block routes' `h_mapFV` are paid from the closed park's stack (a
-- `match` on `h_closeFV_old` or on `h_mapFV108`) where item 301 read bare declines.
-- 2026-10-23 (item 344): DECLINE 268 → 264, SPLIT 166 → 170 — four block-park `PackAlt` sites relay the park's face.
-- 2026-10-23 (item 345): DECLINE 264 → 260, SPLIT 170 → 174 — four of the five content-park relays are `match`
-- splits on the park's `∨ PackAlt` field where `Or.inr trivial` declined.
-- 2026-10-24 (B3 [66] col-0 threading): skipped 31 → 38 — eight new gate lemmas (`ParkFloor.stacked`,
-- `gate_of_blockEntry`, `gate_of_key`, `gate_of_value`, `blockScalar_park_gate`, `noPending_gate_of_inFlow`,
-- `PendingNode.nil_gate_of_allowDirectives`, `FlowBaseRoutes.value`) return functions, so their values
-- have fewer leading lambdas than their types have binders; the census refuses to read them, by design.
-- 2026-10-24 (B3 [66] col-0 threading): edges 674 → 657 (DECLINE 260 → 251, SPLIT 174 → 166, PAY 50 → 55, RELAY 68 → 64,
-- FIELD 58 → 57) — the content parks read the run + gate fields instead of splitting a landing disjunction.
-- 2026-10-26 (item 370): DECLINE 255 → 254, SPLIT 161 → 162 — `accum_block_on_pendingBlock`'s sibling `-` arm
-- splits `h_closeF_old` into the re-parked `pendingBlock.h_closeF` instead of declining it.
-- 2026-10-28 (item 380, PR #146 review): `Or.elim` read as a two-arm split — VIA 49 → 32 (its 17 leaves), DECLINE 253 → 265
-- (the 12 whose arms agree collapse to one DECLINE each), SPLIT 162 → 167 (the 5 whose arms disagree).
-- 2026-10-29 (item 396): content_dispatch_after_close's four declined contexts restated — the
-- three callers' 12 DECLINE edges and the lemma's 4 RELAY edges go (edges 669 → 657, DECLINE
-- 263 → 255, RELAY 67 → 63); the four Or.inr trivial now written inside the lemma are no edge.
-- 2026-10-30 (item 405): the `?`-park chain PAID through its ladder — three `h_kslotE_k` content relays and the `h_resKslot`/`hkvUp`-starved `closeThenBlock` births DECLINE (ruling (a)); SPLIT 167 → 164, DECLINE 255 → 258 (edges 657 unchanged).
def expectedTally : String :=
  -- 2026-10-26 (item 366): DECLINE 258 → 256, VIA 47 → 49 — the two `h_outer` arguments of
  -- `accum_block_on_closeThenBlock` (compact and explicit `:`) pay under `Classical.em (MarkedColsIn sc [col])`.
  -- 2026-10-26 (item 369): edges 664 → 665, DECLINE 256 → 255, FIELD 55 → 56, SPLIT 160 → 161 —
  -- `pendingBlock.h_closeF` threaded into `accum_block_on_pendingBlock` (one FIELD edge) and the
  -- `:`/`?` landing's `h_res_land` there read off those frames instead of `Or.inr trivial`.
  "edges=654 skipped=42 [DECLINE=251, FIELD=58, LOCAL=27, PAY=54, RELAY=62, \
SPLIT=171, VIA=31]"

/-- **The row item 211 read off the compiler's error text and got wrong.**  All
    eight of these print `h_keyctx` when the premise is narrowed; six of them
    are `have h_keyctx := keyctx_of_preprocess …` and one is the binder.  If a
    `have` is ever turned back into a premise — or a premise into a `have` —
    this list moves and the DOCS sentence resting on it has to move with it. -/
def expectedSeed : List String :=
  ["accum_content_on_noPending VIA keyctx_of_preprocess",
   "accum_content_on_noPending VIA keyctx_of_preprocess",
   "accum_content_pending DECLINE",
   "accum_content_pending VIA keyctx_of_preprocess",
   "accum_content_pending VIA keyctx_of_preprocess",
   "accum_content_pending VIA keyctx_of_preprocess",
   "accum_content_pending VIA keyctx_of_preprocess",
   "content_dispatch_after_close RELAY"]

/-- Every lemma that DECIDES an optional premise for someone else, and how
    often.  ~~Thirteen constants carry the module's whole producer surface~~,
    and `Or.imp` — the combinator item 201 named as the blind spot and nobody
    counted — is 39 of the 79.  `keyctx_of_preprocess`'s **7** is the seed's
    six plus `content_dispatch_after_close`'s own premise, and the compiler
    agrees with both halves: narrowing its conclusion repairs exactly seven
    sites (DOCS item 212).

    **Item 213: two of the thirteen are not producers.**  `Or.imp` (39) and
    `dite` (4) are PIPES — they carry a decision made elsewhere — so 43 of those
    79 edges named a combinator and not a decider.  **Item 214 followed them and
    they are gone from this list**: the surface is 36 edges over the 11 constants
    below, and every row names a lemma.  Where the 43 went is
    `expectedPipeLanding`, and the answer is that NONE of them is a producer.

    **Item 295: `flowKeyRoute_of_root` 2 → 3** — `slot_ride`'s frame key.  The
    props arm's fallback is the other new application, and it sits inside the
    arm's split on the run's pack, so it is a `SPLIT` branch and not an edge
    here. -/
-- 2026-10-24 (item 355): the five domained faces — the two `accum_step_flow` pipes
-- (`flowVPack_of_close resume.vslot`, `FlowBaseRoutes.vslot`) and one `explFrameValueLine` pipe now
-- decline (`Or.inr trivial`), three `frameChainUnion`s became the domained `frameChainUnionD`.
  -- 2026-10-26 (item 366): VIA Or.elim 15 → 17 — the two `Classical.em … |>.elim` pays of `h_outer` at closeThenBlock.
  -- 2026-10-28 (item 380, PR #146 review): `Or.elim` is a two-arm SPLIT now (`isTwoArm`), so its 17 VIA leaves
  -- are read arm by arm — 12 whose arms agree (collapsed, one DECLINE each) and 5 that disagree (SPLIT).
-- 2026-10-29 (item 394): `FlowBaseRoutes.valueF` relayed VIA at both flow closes into `pendingContent.h_framesS` (producers 10 → 11).
def expectedProducers : List String :=
  ["2 VIA FlowBaseRoutes.key",
   "2 VIA FlowBaseRoutes.valueF",
   "2 VIA markerctx_of_landing",
   "2 VIA nodocctx_of_preprocess",
   "2 VIA suffixctx_of_landing",
   "3 VIA flowKeyRoute_of_open",
   "3 VIA flowKeyRoute_of_root",
   "3 VIA frameChainUnionD",
   "5 VIA frameChainUnion",
   "7 VIA keyctx_of_preprocess"]

/-- **Where the 43 pipes land (DOCS item 214).**  Item 213 measured that 43 of
    this census's 79 `VIA` edges named a combinator rather than a decider and
    could say nothing about what stood behind them; `resolve` now follows them,
    and this is the answer.  `producers=0` is the row that matters and it is
    asserted as a COUNT, not by being absent from the list: **not one of the 43
    reaches a producer.**  `piped=43` is the same total item 213 derived by
    parsing the row above, now measured rather than parsed, so the two
    instruments can still disagree.

    The landing, read as provenance: 26 are a park or bundle FIELD, 10 are the
    caller's own binder, 7 are a case split — 3 an `Or.casesOn` reached through
    the pipe and 4 the `dite` arms themselves.

    **Item 215 split the first row where item 214 could only assert it.**  Item
    214 read the 26 off the probe by hand and reported 21 of them bound inside
    an `Eq.ndrec`; `peelPipe` now resolves exactly those 21 to `FIELD`, and the
    5 that stay `LOCAL` are the ones under a SATURATED pipe, which transports a
    function nobody applies.  The hand count and the instrument agree, and the
    total is still 43 with still no producer among them. -/
-- 2026-10-20 (item 307): unchanged in the end — `accum_block_on_pendingContent`'s `h_vpack` was an
-- `h_mapFV108.imp …` for one chain and is a `match` (the family's form) now.
-- 2026-10-21 (item 311): `piped` 43 → 45, `producers` 0 → 2, a new row `Or.imp⇒VIA=2` — the two flow closes
-- (`accum_step_flow`) hand `flowVPack_of_close resume.vslot` into the content park's `h_vpack` through
-- `.imp id PackAlt.ofGateClose`: the frame's alternative (`PackAltG g`) becomes the park's (`PackAlt s'`) through a
-- named conversion, which the census rightly reads as a producer — it is lane (d)'s stub.
-- 2026-10-21 (item 313): `piped` 45 → 54, `producers` 2 → 3, `Or.imp⇒FIELD` 21 → 29, `Or.imp⇒VIA` 2 → 3 — the content
-- lane's transports are `Or.imp` pipes whose right map is `PackAlt.step_content h_preprocess h_dispatch`, landing in the
-- park the content step builds (eight in a field, one through `explFrameValueLine`, which the census reads as a producer).
-- 2026-10-21 (item 320): `piped` 54 → 55, `Or.imp⇒SPLIT` 3 → 4 — `accum_block_on_closeThenBlock`'s `h_seqFramesV` is relayed
-- through `.imp id (PackAlt.step_blockEntry h_preprocess h_dispatch)` into the new park's split field (the relay item 319's
-- payments surfaced); producers and the other landings stand.
-- 2026-10-28 (item 380, PR #146 review): piped 63 → 68, `Or.elim⇒SPLIT=5` — the five disagreeing `Or.elim`s land as splits.
-- 2026-10-29 (item 388): piped 68 → 69, Or.imp⇒FIELD 33 → 34 — `accum_content_pending` relays the mapping
-- park's `h_closeF` (now `.blockOut`) into the content lane's `.blockIn` binder by `.imp`, weakening the node.
def expectedPipeLanding : String :=
  "piped=78 producers=10 [Eq.rec⇒VIA=8, Or.elim⇒SPLIT=5, Or.imp⇒FIELD=36, \
Or.imp⇒LOCAL=5, Or.imp⇒RELAY=13, Or.imp⇒SPLIT=4, Or.imp⇒VIA=2, dite⇒SPLIT=5]"

/-- What the SPLITs decide (DOCS item 216), and the row that matters is
    `elsewhere=0`: **not one leaf of any case split in this module is decided
    anywhere but at the site.**  It is asserted as a COUNT, not by being absent
    from the list.

    `resolve` enters every arm now.  An arm's answer is an answer per BRANCH, so
    the only split that can be reported as one answer is one whose arms agree —
    and exactly ONE of the 156 does, a chain of splitters
    (`Or.casesOn→Exists.casesOn→Exists.casesOn→And.casesOn→And.casesOn→And.casesOn→dite`
    — seven since item 386 added `h_valF`'s level conjunct; the dispatcher's two
    `fun ⟨ks, hlt, hcov, r⟩` producers also renumber `accum_block_pending`'s match
    auxiliaries by two) that all land on `PAY`.  The other 155 keep the `SPLIT` label and carry
    their leaves, which is what the shape list below counts.

    **That one is named in `expectedCollapsedEdge` as of item 218**, and naming
    it was not bookkeeping: it is the site N-218 broke at where the join
    predicted no break, because its `have` ascribes the wide `_ ∨ True` while
    its proof pays on all six branches.

    **Item 287: one split fewer**, the value park's split on `h_vslot51`, which
    left with the binder it supplied (`expectedTally`): `survived` 156 → 155,
    `leaves` 330 → 328, one `DECLINE|PAY`.  **Item 288: one more**,
    `compact_open_map`'s split on the indicator, which supplied
    `pendingMapValue.h_vslot` and left with it: 155 → 154, 328 → 326.

    **Item 295: one leaf is decided elsewhere.**  The props arm's split on the
    run's pack wrote `Or.inr trivial` on its fallback branch, and that branch
    takes the landing's route now (`flowKeyRoute_of_root`): one `DECLINE|PAY`
    split becomes `PAY|VIA` (`DECLINE` 167 → 166, `VIA` 0 → 1, `elsewhere`
    0 → 1), and no split is added or lost.

    **Item 304: the sequence case.**  The value-line stacks are `KeyFrames`, and
    `KeyFrames.resumeAt` hands a mapping OR a sequence continuation; the three
    `:`/key consumers that resumed a value-line stack directly
    (`accum_block_on_closeThenBlock`, `…_pendingBlockContent`, `…_pendingBlock`)
    split on it and DECLINE the sequence case, which no producer pushes yet —
    `leaves` 326 → 329, `DECLINE` 166 → 169, three `DECLINE|DECLINE|PAY` splits
    become `DECLINE|DECLINE|DECLINE|PAY`, and `PAY`, `VIA` and `elsewhere` stand.

    **Item 305: two splits more.**  `closeThenBlock`'s landed-`-` arm splits the
    `?` slot for the first entry's stack (`h_slotV`, a leaf under the `h_valFV`
    split: one `DECLINE|DECLINE|PAY` becomes `DECLINE|DECLINE|DECLINE|DECLINE|PAY|PAY|PAY`)
    and its compact arm splits `hkv` for the compact entry's (`DECLINE|PAY` 141 →
    142): `survived` 154 → 155, `leaves` 329 → 335, `DECLINE` 169 → 172, `PAY`
    159 → 162. -/
-- 2026-10-20 (item 306): six splits more, all `DECLINE|PAY` (142 → 148) — the two
-- key-pack builders' value-line stacks at the three entry-park calls, each a `match`
-- on the entry park's `h_closeFV_old`: `survived` 155 → 161, `leaves` 335 → 347,
-- `DECLINE` 172 → 178, `PAY` 162 → 168.
-- 2026-10-20 (item 307): five splits more — `h_vpack` and `h_mapFV` at the two block routes (`match`es on
-- `h_closeFV_old`) and `h_vpack` at the content route (a `match` on `h_mapFV108`): `survived` 161 → 166,
-- `DECLINE|PAY` 148 → 153; and the landed-`-` arm's own tree grows behind `h_resSeqV`/`h_resKslot`/`h_slotV'`
-- (all `match`es): its 7-leaf shape reads 11 leaves and one `DECLINE|DECLINE|PAY` is a 5-leaf shape —
-- `leaves` 347 → 363, `DECLINE` 178 → 185, `PAY` 168 → 177; no `VIA` beyond `flowKeyRoute_of_root`'s one.
-- 2026-10-21 (item 320): `leaves` 363 → 364, `DECLINE` 185 → 186, one vector `DECLINE|DECLINE|PAY` → `DECLINE|DECLINE|DECLINE|PAY`
-- (3 → 2 and 4 → 5) — a catch-all of `accum_block_on_closeThenBlock` split into its inner-alternative arm, which this
-- census reads as one more leaf on that split's vector; the paid arm is a PAY it already counted.
-- 2026-10-21 (item 332): `leaves` 364 → 359, `DECLINE` 186 → 181 — the key-stack resume no longer returns
-- "a mapping tail OR a sequence tail" (`KeyFrames.resumeAtMap`/`resumeAtSeq` by the level's own kind), so the five
-- `Or.inr trivial` arms that refuted the kind it could not take are gone with the `∨`.
-- 2026-10-23 (item 344): survived 166 → 170, leaves 359 → 367, DECLINE|PAY 153 → 157 — the four relayed
-- block-park sites split on the park's `∨ PackAlt` field.
-- 2026-10-23 (item 345): survived 170 → 174, leaves 367 → 375, DECLINE|PAY 157 → 161 — the same four splits.
-- 2026-10-25 (item 363): the flow OPEN lane read off the block state (`h_refused`, one `Classical.em`; the three `match h_kslot_* with` blocks and the two direct matches go): tally DECLINE 259 → 258 / VIA 46 → 47, `14 → 15 VIA Or.elim`, SPLIT landing collapsed 15 → 14 / elsewhere 4 → 5, SPLIT BRANCH, SITE-DECIDED `accum_flow_open_depth0.match_1_24 → match_1_22`, COLLAPSED edge.
-- 2026-10-26 (item 369): survived 160 → 161, leaves 353 → 356, DECLINE 176 → 178, PAY 172 → 173 — the `:`/`?`
-- landing in `accum_block_on_pendingBlock` reads `h_res_land` off `pendingBlock.h_closeF` (one new split: frames
-- absent / level not named / level named).
-- 2026-10-26 (item 370): survived 161 → 162, leaves 356 → 358 — `h_closeF_old` split once more at the sibling `-` arm.
-- 2026-10-28 (item 380, PR #146 review): survived 162 → 167, collapsed 14 → 26 (the twelve agreeing `Or.elim`s), leaves 358 → 384,
-- DECLINE 177 → 197, PAY 174 → 179, VIA 7 → 8 — the arms the `VIA Or.elim` leaves hid, read.
-- 2026-10-29 (item 387): leaves 384 → 386, DECLINE 194 → 195, PAY 179 → 180 — `accum_block_on_pendingBlock`'s
-- no-pop arm splits `n < k` (PAY via the helper) from `k = n` (sequence top refuted / mapping sibling DECLINE).
-- 2026-10-30 (item 405): the `?`-park chain PAID through its ladder — three `h_kslotE_k` content relays and the `h_resKslot`/`hkvUp`-starved `closeThenBlock` births DECLINE (ruling (a)); SPLIT 167 → 164, DECLINE 255 → 258 (edges 657 unchanged).  Rule 8 fix (same item): the chain re-indexed by the projection `markedCols sc`; the two head consumers (`flowKeyRoute_of_open`'s compact pair, the props park's entry-level pack) split on `markedCols sc` and DECLINE at the markless projection — leaves 381 → 383, DECLINE 194 → 196 (DECLINE|PAY 144 → 142, DECLINE|DECLINE|PAY 6 → 8).
def expectedSplitLanding : String :=
  "survived=171 collapsed=23 leaves=402 elsewhere=11 [DECLINE=208, PAY=183, \
VIA=11] \
[DECLINE|DECLINE|DECLINE|DECLINE|DECLINE|DECLINE|PAY|PAY|PAY|VIA|VIA|VIA=1, \
DECLINE|DECLINE|DECLINE|DECLINE|DECLINE|PAY|VIA|VIA=1, \
DECLINE|DECLINE|DECLINE|DECLINE|PAY|PAY|PAY|PAY|PAY=1, \
DECLINE|DECLINE|DECLINE|PAY=2, DECLINE|DECLINE|DECLINE|PAY|PAY|PAY=1, \
DECLINE|DECLINE|DECLINE|PAY|VIA=3, DECLINE|DECLINE|PAY=13, \
DECLINE|DECLINE|PAY|PAY=1, DECLINE|DECLINE|PAY|PAY|PAY=1, DECLINE|PAY=144, \
DECLINE|PAY|PAY=1, PAY|VIA=1, PAY|VIA|VIA=1]"

/-- **Which BRANCH is taken (DOCS item 217).**  Item 216 resolved what a split
    WRITES — both answers, one per arm.  What it could not say was which arm the
    runtime takes, and the answer is that the site almost never chooses:
    **145 of the 155 surviving splits branch on a value the CALLER supplied**,
    99 of them directly on one of the caller's own binders and 46 through a
    constructor field carved out of one.  Ten — and only ten — branch on a fact
    the site derives for itself; they are listed in `expectedSiteDecided`.

    ~~99 split on a `RELAY`~~ — that was item 216's own discriminant column read
    only as far as its bare `RELAY` rows, and it skipped both the 46 chains that
    reach a relay through a field and the 9 nested splits that reach one through
    another split.  **The number is 145.**

    Of the 145, **99 root at a premise that is itself a `_ ∨ True`** — the site
    is casing on whether its OWN CALLER declined, and then declining in the arm
    where the caller did.  Their host premises are `expectedBranchPremises`.

    `agree=99/99` is the control, and it is a cross-check rather than a restated
    count: for every split whose discriminant is a bare relay, the splitter's
    DECLARED major-premise type — read off the splitter's own type by
    `majorOf`/`binderHead` — is compared with the type of the premise the chain
    roots at, read off the enclosing lemma's type.  Neither reading goes through
    the proof term the census walks, so a wrong `major` index would show up here
    as a disagreement rather than as a plausible column.

    The leaf rows are `orArgRefs`: **164 of the 168 `DECLINE` leaves are
    `closed`**, an `Or.inr trivial` that mentions nothing in scope, and all 160
    `PAY` leaves are `free`.  That asymmetry is what made N-217 predictable by
    line: a `closed` decline cannot break when the premise its split branches on
    is narrowed.

    **Item 287 moves six roots.**  Five splits branch on
    `accum_block_on_closeThenBlock`'s own `h_vslot` (`expectedBranchSupply`'s
    row for it read `splits=5`), and they stay and change their ROOT's kind,
    because that binder stopped being a `_ ∨ True`: `optionalRoot` 100 → 95.
    The sixth is the value park's split on its park's `h_vslot` FIELD — a
    plain root — which left with the binder it supplied (`relayRooted`
    146 → 145, one `DECLINE-closed` and one `PAY-free` with it): `plainRoot`
    46 + 5 − 1 = 50.  **Item 288** removes `compact_open_map`'s split on the
    indicator `hc`, a plain root and a bare relay, with the field it supplied:
    `relayRooted` 145 → 144, `plainRoot` 50 → 49, the control 100 → 99.
    **Item 295**: the props arm's fallback branch is a producer call, not a
    closed decline (`DECLINE-closed` 163 → 162, one `VIA flowKeyRoute_of_root`
    leaf); no split or root moves.  **Item 304**: the three value-line resumes
    split `KeyFrames.resumeAt`'s sum and decline its sequence case — one more
    closed decline each (`leaves` 326 → 329, `DECLINE-closed` 162 → 165); no
    split or root moves.  **Item 305**: two splits more — the landed-`-` arm's
    `h_slotV` on the `?` slot (relay-rooted: `relayRooted` 144 → 145) and the
    compact arm's on `hkv` (a plain root: `plainRoot` 49 → 50); `leaves` 329 → 335,
    `DECLINE-closed` 165 → 168, `PAY-free` 159 → 162. -/
-- 2026-10-20 (item 306): the same six splits, each rooted at a relayed OPTIONAL
-- premise (`h_closeFV_old`, `… ∨ True`): `splits` 155 → 161, `leaves` 335 → 347,
-- `relayRooted` 145 → 151, `optionalRoot` 95 → 101, `agree` 99 → 105 (both readings
-- name the same arm at all six), `DECLINE-closed` 168 → 174, `PAY-free` 162 → 168.
-- 2026-10-20 (item 307): the same five, each rooted at a relayed optional premise (`h_closeFV_old`,
-- `h_mapFV108`): `splits` 161 → 166, `leaves` 347 → 363, `relayRooted` 151 → 156, `optionalRoot` 101 → 106,
-- `agree` 105 → 110, `DECLINE-closed` 174 → 181, `PAY-free` 168 → 177; no `Or.elim` bucket — the landed arm's
-- fallbacks are `match`es the census walks.
-- 2026-10-20 (item 309): `DECLINE-closed` 181 → 180, `DECLINE-free` 4 → 5 — `explFrameValueLine`'s
-- `Or.inr h => Or.inr h` (generic in the alternative) hands back the premise's alternative where
-- `Or.inr trivial` mentioned nothing.
-- 2026-10-21 (item 314): `DECLINE-closed` 180 → 132, `DECLINE-free` 5 → 53 — forty-eight split leaves of the content
-- lane hand back their hypothesis (`Or.inr h => Or.inr (PackAlt.step_content … h)` or `Or.inr h`) where they declined with
-- a closed `trivial`; the leaf count, the roots and the agreement stand.
-- 2026-10-21 (item 318): `DECLINE-closed` 132 → 131, `DECLINE-free` 53 → 54 — one dash-arm leaf of
-- `accum_block_on_pendingBlock` hands back its hypothesis through `PackAlt.step_blockEntry` (the block lane's transport,
-- item 319's consumer probe) where it declined with a closed `trivial`.
-- 2026-10-21 (item 319): `DECLINE-closed` 131 → 98, `DECLINE-free` 54 → 87 — the block lane's thirty-three leaf
-- transports and identities hand back their hypothesis (`Or.inr h_alt => Or.inr (PackAlt.step_blockEntry … h_alt)` or
-- `Or.inr h_alt`) where they closed with `trivial`; splits, roots and the agreement stand.
-- 2026-10-21 (item 320): `leaves` 363 → 364, `DECLINE-free` 87 → 88 — the split catch-all's new inner-alternative arm hands
-- its hypothesis back (`Or.inr h_alt`), one more free leaf on that split; roots and the agreement stand.
-- 2026-10-21 (item 321): `DECLINE-closed` 98 → 94, `DECLINE-free` 88 → 92 — `colon_open_map_props`'s three leaves hand back
-- their hypothesis through `PackAlt.step_value` and `question_open_map`'s have-block leaf through the identity, where they
-- closed with `trivial`; leaves, roots and the agreement stand.
-- 2026-10-21 (item 322): `DECLINE-closed` 94 → 88, `DECLINE-free` 92 → 98 — the colon openers' six leaves hand their hypothesis
-- back through the new step premise (`Or.inr (h_alt_step h_alt)`) where they closed with `trivial`; leaves, roots and the
-- agreement stand.
-- 2026-10-21 (item 324): `DECLINE-closed` 88 → 86, `DECLINE-free` 98 → 100 — the flow opener's `pendingBlock` and
-- `pendingMapValue` catch arms hand their hypothesis back (`Or.inr h_alt`) where they closed with `trivial`; leaves, roots and the
-- agreement stand.
-- 2026-10-23 (item 344): splits 166 → 170, leaves 359 → 367, relayRooted 156 → 160, DECLINE-free 100 → 104,
-- PAY-free 177 → 181 — the four block-park relays.
-- 2026-10-23 (item 345): splits 170 → 174, leaves 367 → 375, relayRooted 160 → 164, optionalRoot 107 → 108, plainRoot 53 → 56, agree 111/111 → 112/112, DECLINE-free 104 → 108, PAY-free 181 → 185 — the same four splits.
-- 2026-10-26 (item 369): splits 160 → 161, leaves 353 → 356, relayRooted 151 → 152, optionalRoot 103 → 104,
-- DECLINE-closed 83 → 85, PAY-free 172 → 173 — the `h_res_land` split on `pendingBlock.h_closeF` in
-- `accum_block_on_pendingBlock` (an optional-rooted relay: frames absent / level not named / level named).
-- 2026-10-26 (item 370): splits 161 → 162, relayRooted 152 → 153, optionalRoot 104 → 105 — the sibling `-` arm's split of `h_closeF_old`.
-- 2026-10-28 (item 380, PR #146 review): `Or.elim` read as a two-arm split — splits 162 → 167 (the five whose arms
-- disagree), leaves 358 → 384, siteDecided 9 → 11 (two `Classical.em … |>.elim` whose major the site derives),
-- optionalRoot 105 → 108; `VIA Or.elim` 3 → 0 (now arms), `VIA absurd` 3 → 7 and `DECLINE-closed` 84 → 103 (the
-- arms it hid: item 378's refutations and the declined no-pop / `lo > k` / uncovered arms at the two builders).
-- 2026-10-28 (item 385): DECLINE-closed 103 → 100; VIA deeperLandingResume = 2, VIA deeperLandingResumeSeq = 1 —
-- the three paid no-pop leaves (`closeThenBlock`'s two `h_res_land` arms, `pendingBlock`'s `s_prep.indents = sc.indents` arm)
-- are helper applications now; the helpers' own dedent declines are counted at the helpers, not at the sites.
-- 2026-10-29 (item 387): leaves 384 → 386; `VIA deeperLandingResumeSeq` 1 → 0 (the helper is now the `n < k` arm's
-- PAY-free, +1); `VIA absurd` 7 → 8 (the `k = n` sequence top, refuted by `seqTop_refuted_at_indicator_le`);
-- DECLINE-closed 100 → 101 (the `k = n` mapping top: the enclosing mapping's sibling, declined, named).
-- 2026-10-29 (item 389): leaves 386 → 388, DECLINE-free 94 → 95, PAY-free 180 → 181 — the `-` park's k = n mapping-top arm is a PAY leaf now; its sequence-top half stays a decline.
-- 2026-10-30 (item 405): the `?`-park chain PAID through its ladder — three `h_kslotE_k` content relays and the `h_resKslot`/`hkvUp`-starved `closeThenBlock` births DECLINE (ruling (a)); SPLIT 167 → 164, DECLINE 255 → 258 (edges 657 unchanged).
def expectedSplitBranch : String :=
  "splits=171 leaves=402 relayRooted=160 siteDecided=11 optionalRoot=110 plainRoot=50 agree=115/115 disagree=0 [DECLINE-closed=106, DECLINE-free=102, PAY-free=183, VIA L4YAML.Proofs.StreamAccum.deeperLandingResume-=2, VIA L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root-=1, VIA absurd-=8]"

/-- **The ten splits the site decides for itself**, which is the whole residue
    of the branch question after `expectedSplitBranch`.  Four are a `dite` on a
    condition the site tests (`VIA Eq`, `VIA LE.le`); five case an `Or`-valued
    fact the site derives (`Nat.eq_zero_or_pos`, `frameChainUnion`); one reaches
    its fact through a nested split (`preprocess_some_savedKey_shape`).

    `dite`'s `major` is argument 1 — the PROPOSITION, not a proof of it — so
    `VIA Eq` and `VIA LE.le` naming a type here is the instrument reading the
    condition, not losing the discriminant. -/
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-25 (#112 review): the `FlowStackK` `MarkedColsIn` carrier reverted (Rule 8: a projection of the closed state is decided at the close by `Classical.em`); `accum_flow_open_depth0`'s inline domain matches go — SITE-DECIDED `match_1_27 → match_1_24`, COLLAPSED edge `match_1_25 → match_1_22`; the tally and DECLINE WRITERS (the paid faces) stay.
-- 2026-10-28 (item 380, PR #146 review): `Or.elim` read as a two-arm split — +1 row: item 366's two
-- `Classical.em (MarkedColsIn sc [col]) |>.elim` pays of `h_outer` at closeThenBlock, the site deriving its own major.
def expectedSiteDecided : List String :=
  ["1 accum_block_on_closeThenBlock :: dite on VIA Eq ⇒ DECLINE|PAY",
   "1 accum_block_on_pendingBlock :: dite on VIA Eq ⇒ DECLINE|PAY",
   "1 accum_block_on_pendingBlock :: dite on VIA LE.le ⇒ DECLINE|DECLINE|PAY|PAY",
   "1 accum_block_on_pendingBlock :: dite on VIA LE.le ⇒ DECLINE|DECLINE|PAY|PAY|PAY",
   "1 accum_block_on_pendingBlockContent :: dite on VIA Eq ⇒ DECLINE|PAY",
   "1 accum_content_pending :: Or.casesOn on VIA Nat.eq_zero_or_pos ⇒ DECLINE|DECLINE|DECLINE|PAY",
   "1 accum_flow_open_depth0 :: accum_flow_open_depth0.match_1_22 on SPLIT Or.casesOn on VIA preprocess_some_savedKey_shape ⇒ PAY|VIA",
   "2 accum_block_on_closeThenBlock :: Or.elim on VIA Classical.em ⇒ DECLINE|DECLINE|PAY",
   "2 accum_block_pending :: Or.casesOn on VIA Nat.eq_zero_or_pos ⇒ DECLINE|PAY"]

/-- **The premises the branch is taken on**, by binder NAME, for the 99 splits
    whose discriminant roots at an optional premise of the enclosing lemma.
    These are the pending park's own optional contexts — the same names items
    198/200 counted as park fields — which is why narrowing one of them is a
    question about the park's callers and not about the lemma that splits on it.

    **Item 218 ran that question and the answer is in `expectedBranchSupply`**,
    one row per `(lemma, premise)` pair naming the park field each reads from
    and the labels its own supply terminates in. -/
-- 2026-10-20 (item 306): `h_closeFV_old` 10 → 16 — the six key-pack stack splits of
-- `accum_content_on_pendingBlock_indented` root at it (string-sorted, so its row moves
-- behind `13 h_closeF_old`).
-- 2026-10-23 (item 345): `h_closeFV_old` 21 → 22 — `accum_content_on_pendingBlock_indented`'s twin relay splits on it.
-- Item 350: `h_expl` left the premises — its four splits pay the `?`-entry
-- face directly once the `PackAlt` arm became `NotQuestionPark`.
-- 2026-10-28 (item 380, PR #146 review): `h_kslotUp` 4 → 7 — `Or.elim` read as a two-arm split: the three
-- `Classical.em … |>.elim` decisions that root at the key-slot premise are splits now, not `VIA` leaves.
def expectedBranchPremises : List String :=
  ["1 h_explUp_chainD",
   "1 h_mapF",
   "1 h_mapFV",
   "1 h_mapFV108",
   "1 h_mk",
   "1 h_pr",
   "1 h_routeS",
   "1 h_sfx",
   "1 h_valFV",
   -- 2026-10-26 (item 369): 13 → 14 — `accum_block_on_pendingBlock` now splits on `pendingBlock.h_closeF` too
   -- 2026-10-26 (item 370): 14 → 15 — the sibling `-` arm splits `h_closeF_old` too.
   "15 h_closeF_old",
   "2 h_kslotD",
   "22 h_closeFV_old",
   "3 h_cov",
   "3 h_kslotUp_old",
   "3 h_resV_land",
   "3 h_seqF_old",
   "3 h_vslot",
   "4 h_closeFV108",
   "4 h_routeF",
   "4 h_routeFV",
   "5 h_seqF168",
   "7 h_closeF99",
   "7 h_kslot",
   "8 h_kslotUp",
   "8 h_kslot_old"]

/-- **Is a DECLINE arm ever SELECTED (DOCS item 218).**  Item 217 named, for
    each of the 99 optional-rooted splits, the premise its branch is taken on.
    It could not say whether any caller ever takes the declining branch.  This
    joins the two halves of the census that had never met — every split's
    `(caller, rootTgt)` against every supply edge's `(callee, idx)` — and
    chases the result upward to the labels it terminates in.

    `dead=0` is the row that matters: **not one of the 36 branch premises has a
    DECLINE arm that nothing can select.**  `direct=8` is the row that was a
    surprise: only 8 of the 36 have a caller that writes `Or.inr trivial`
    straight into them, so **a decline is almost never written where it is
    branched on** — 25 of the remaining 28 reach it through a park's
    construction sites, one hop up.

    `orphan=3` is the census DECLINING to answer and is reported apart from
    `dead` for that reason: those three leave the module at
    `colon_fires_implicit_key`/`colon_fires_props_key`'s `h_key`, and a walk
    that is scoped to one module cannot see who fills a premise from outside
    it.  This is the first item at which that horizon bit.

    `accounted` is the control: the join must PARTITION the census, so it has to
    equal `edges`.  `resolved` is the second: every `FIELD` edge must name a
    constructor field, or the `FIELD` hop is guessing. -/
-- Item 287: `accum_block_on_closeThenBlock`'s `h_vslot` left the population
-- (`expectedTally`), and the join with it: one pair, which its ten callers
-- declined DIRECTLY, its node, and the five splits that branched on it.
-- Item 288: `accum_content_on_pendingMapValue_indented`'s `h_vslot` is fed by
-- the park's field through `.imp _ (fun _ => trivial)`, and the field is not a
-- `_ ∨ True` now, so the chase stops at it: one more `orphan`, one fewer
-- `closureDecline`, its three splits no longer live, the field's node gone
-- (`expectedBranchSupply`'s row for it reads `ORPHAN`).
-- Item 295: `accounted` follows `edges` (642 → 656, `expectedTally`); the
-- fourteen new edges reach no new pair, orphan or split.
-- Item 296: and again (656 → 660); the four new edges, each a declined
-- `h_ref`, reach no new pair, orphan or split either.
-- Item 297: and again (660 → 664), the `w ∉ ks` exit's four `h_ref`s.
-- Item 300: and again (664 → 674) — the marker premise's seven declines and
-- one payment at `content_dispatch_routed`, and `h_marker_new`'s two
-- refutations at the nested opens; `nodes` 159 → 161 are those two binders,
-- `content_dispatch_routed.h_markerline` and `km_push_at_open.h_marker_new`,
-- as nodes of the reach graph — each reaching no new pair, orphan or split.
-- 2026-10-20 (item 306): `liveSplits` 89 → 95 — the six key-pack stack splits on
-- `h_closeFV_old` are live (the entry park's callers supply its paying arm); no new
-- pair, orphan, edge or node.
-- 2026-10-20 (item 307): `liveSplits` 95 → 100 — the four above and the content route's split on `h_mapFV108`,
-- which is a new pair (`pairs` 35 → 36, `closureDecline` 31 → 32) reached one park hop up (`parkHop` 21 → 22).
-- 2026-10-23 (item 344): `liveSplits` 100 → 101 — the `on_pendingBlock` caller's `h_valFV` split on `h_closeFV_old`.
-- 2026-10-23 (item 345): liveSplits 101 → 102 — one more live split (the twin relay on `h_closeFV_old`).
-- 2026-10-26 (item 369): pairs 35 → 36, closureDecline 33 → 34, liveSplits 99 → 100, nodes 162 → 163, fieldEdges 55 → 56,
-- parkHop 21 → 22 — one more field-fed split (`pendingBlock.h_closeF` → `accum_block_on_pendingBlock.h_closeF_old`).
-- 2026-10-26 (item 370): liveSplits 100 → 101 — the sibling `-` arm's split of `h_closeF_old` is live (PAY arm reached).
-- 2026-10-28 (item 385): accounted 667/667 → 669/669, nodes 163 → 164
-- — `deeperLandingResume` is one more node; its two `h_valF` relay edges are accounted.
-- 2026-10-29 (item 396): after_close's four declined contexts restated — their decline leaves are no longer reached through the three callers.
def expectedDeclineReach : String :=
-- Item 372 (2026-10-27): two more edges — `ImplicitKeyPack`'s route conjunct is now an Or (the `SeqTopKey` face), split at the producer's exit (a) and resolved at `colon_fires_implicit_key`.
-- 2026-10-28 (item 380, PR #146 review): liveSplits 101 → 104 — `Or.elim` read as a two-arm split: three of the
-- five disagreeing `Classical.em … |>.elim` decisions stand on a live (reachable) decline path; nothing else moved.
  "pairs=36 orphan=4 direct=7 closureDecline=32 dead=0 maxDepth=2 liveSplits=104 deadSplits=0 accounted=654/654 nodes=160 fieldEdges=58 fieldResolved=58 withCycle=8 declineWriters=19 parkHop=22"

/-- **Every branch premise, with what its own callers supply and where that
    bottoms out.**  `⇐` names the FIRST hop — for a park field, the field
    itself (`pendingBlock.h_closeF`), which is the form the module's own
    comments use, so the row is checkable against them by a route this census
    does not take.  `⇒` is the terminal set, `br` marking a label reached on one
    branch of a split rather than flatly.

    Item 287: `h_vslot :: accum_block_on_closeThenBlock#12 :: splits=5 sup=11`
    left with its binder, and every other row of the three lemmas that lost
    `sp_block_ctx` and `h_stream_fallback` reads its binder two places earlier. -/
-- 2026-10-21 (item 311): `colon_open_map_implicit`'s binders shift by one (`{alt : Prop}` is its first binder:
-- the lemma states the family's alternative generically, as the three helpers of item 309 do) — #11/#12/#13/#27
-- → #12/#13/#14/#28, the rows otherwise verbatim.
-- 2026-10-23 (item 344): `on_pendingBlock#29` splits 6 → 7; `closeThenBlock#30` DECLINE 5 → 3, SPLIT 2 → 4;
-- `closeThenBlock#31` DECLINE 9 → 8, SPLIT 0 → 1 — the four block-park relays.
-- 2026-10-23 (item 345): `accum_content_on_pendingBlock_indented#29 h_closeFV_old` splits 10 → 11 (the twin relay);
-- `accum_block_on_pendingBlockContent#33 h_kslotUp` loses its bare DECLINE (the `h_kslotUp` relays downstream).
-- 2026-10-23 (item 349): three hypothesis indices +1 — `h_dead` (the column-0 landing fact) is
-- threaded into `accum_content_on_pendingBlock_indented` / `accum_content_on_pendingMapValue_indented`.
-- Item 350: the two `h_expl` rows left — the field no longer splits (its `?`-entry
-- face is paid directly; the `PackAlt` arm became `NotQuestionPark`).
-- 2026-10-24 (B3 [66] col-0 threading): two binder indices shift with `accum_content_on_pendingBlock_indented`'s
-- new gate field (#28 → #29, #29 → #30); rows unchanged.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-28 (item 380, PR #146 review): `Or.elim` read as a two-arm split — 7 rows: the `VIA` label leaves the
-- terminating-label sets of `h_closeFV108`, `h_kslot`(pendingMapValue), `h_mapFV`, `h_mapFV108`, `h_valFV` (the
-- `Classical.em … |>.elim` behind them is arms now, its leaves counted as DECLINE/PAY), and `h_kslotUp`'s splits
-- 3 → 5 at pendingBlock, 1 → 2 at pendingBlockContent (the `Or.elim` decisions rooted at the key-slot premise).
-- 2026-10-29 (item 389): `accum_content_on_pendingBlock_indented` gains the premise `h_top_old` before `h_col_old`, so its `h_kslotUp_old` / `h_closeFV_old` rows move one hypothesis index (#31 → #32, #32 → #33); supply and branches unchanged.
-- 2026-10-29 (item 394): `h_closeF_mv` at `accum_flow_open_depth0`'s mapping arm now SUPPLIES `FlowBaseRoutes.valueF` (a new branch-supply row from `pendingMapValue.h_closeF`).
-- 2026-10-30 (item 405): the `?`-park chain PAID through its ladder (see `expectedTally`).
def expectedBranchSupply : List String :=
  ["h_closeF99 :: accum_content_on_pendingMapValue_indented#18 :: splits=7 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_closeF ⇒ PAY+brDECLINE+brPAY",
   "h_closeFV108 :: accum_content_on_pendingMapValue_indented#20 :: splits=4 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_closeFV ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_closeFV_old :: accum_block_on_pendingBlock#31 :: splits=7 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeFV ⇒ DECLINE+brDECLINE+brPAY",
   "h_closeFV_old :: accum_block_on_pendingBlockContent#37 :: splits=4 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_closeFV ⇒ brDECLINE+brPAY",
   "h_closeFV_old :: accum_content_on_pendingBlock_indented#33 :: splits=11 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeFV ⇒ DECLINE+brDECLINE+brPAY",
   "h_closeF_old :: accum_block_on_pendingBlock#32 :: splits=2 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeF ⇒ PAY+brDECLINE+brPAY",
   "h_closeF_old :: accum_block_on_pendingBlockContent#36 :: splits=2 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_closeF ⇒ brDECLINE+brPAY",
   "h_closeF_old :: accum_content_on_pendingBlock_indented#14 :: splits=11 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_closeF ⇒ PAY+brDECLINE+brPAY",
   "h_cov :: indicator_open_map#27 :: splits=3 sup=4 [DECLINE=1,SPLIT=3] ⇐ - ⇒ DECLINE+brDECLINE+brPAY",
   "h_explUp_chainD :: question_open_map#29 :: splits=1 sup=1 [RELAY=1] ⇐ h_explUp_chainD@indicator_open_map ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot :: accum_block_on_pendingBlock#13 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot :: accum_block_on_pendingBlockContent#15 :: splits=1 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot :: accum_content_on_pendingMapValue_indented#17 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   -- Item 409 (2026-10-30): both `:` consumers' `h_kslotD` are PAID from the pack's domained pair
   -- (`h_kslot_pk.imp … ⟨ns, MarkedColsIn.step_value …, routes⟩`): DECLINE ⇒ field-supplied, read as ORPHAN.
   "h_kslotD :: colon_open_map_implicit#29 :: splits=1 sup=1 [FIELD=1] ⇐ And.intro.left ⇒ ORPHAN",
   "h_kslotD :: colon_open_map_props#29 :: splits=1 sup=1 [FIELD=1] ⇐ And.intro.left ⇒ ORPHAN",
   "h_kslotUp :: accum_block_on_pendingBlock#30 :: splits=6 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslotUp ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslotUp :: accum_block_on_pendingBlockContent#35 :: splits=2 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlockContent.h_kslotUp ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslotUp_old :: accum_content_on_pendingBlock_indented#32 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslotUp ⇒ DECLINE+brDECLINE+brPAY",
   "h_kslot_old :: accum_content_on_pendingBlock_indented#13 :: splits=8 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_kslot ⇒ DECLINE+brDECLINE+brPAY",
   "h_mapF :: accum_block_on_closeThenBlock#29 :: splits=1 sup=11 [DECLINE=7,FIELD=2,RELAY=2] ⇐ h_mapF109@accum_block_on_pendingContent,-,PendingNode.pendingMapValue.h_frames ⇒ DECLINE+PAY+VIA+brDECLINE+brPAY",
   "h_mapFV :: accum_block_on_closeThenBlock#31 :: splits=1 sup=11 [DECLINE=3,FIELD=2,RELAY=2,SPLIT=4] ⇐ h_mapFV108@accum_block_on_pendingContent,-,PendingNode.pendingMapValue.h_framesV ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_mapFV108 :: accum_block_on_pendingContent#35 :: splits=1 sup=1 [FIELD=1] ⇐ PendingNode.pendingContent.h_framesV ⇒ DECLINE+brDECLINE+brPAY",
   "h_mk :: accum_block_on_closeThenBlock#20 :: splits=1 sup=11 [DECLINE=10,PAY=1] ⇐ - ⇒ DECLINE+PAY",
   "h_pr :: accum_block_on_closeThenBlock#30 :: splits=1 sup=11 [DECLINE=9,SPLIT=2] ⇐ - ⇒ DECLINE+brDECLINE+brPAY",
   "h_resV_land :: colon_open_map#26 :: splits=2 sup=1 [RELAY=1] ⇐ h_resV_land@indicator_open_map ⇒ DECLINE+brDECLINE+brPAY+brVIA",
   "h_resV_land :: question_open_map#27 :: splits=1 sup=1 [RELAY=1] ⇐ h_resV_land@indicator_open_map ⇒ DECLINE+brDECLINE+brPAY+brVIA",
   "h_routeF :: colon_open_map_implicit#12 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeF :: colon_open_map_props#11 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeFV :: colon_open_map_implicit#13 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeFV :: colon_open_map_props#12 :: splits=2 sup=1 [SPLIT=1] ⇐ - ⇒ brDECLINE+brPAY",
   "h_routeS :: colon_open_map_implicit#27 :: splits=1 sup=1 [FIELD=1] ⇐ And.intro.right ⇒ ORPHAN",
   "h_seqF168 :: accum_content_on_pendingMapValue_indented#38 :: splits=5 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_seqF ⇒ DECLINE+brDECLINE+brPAY",
   "h_seqF_old :: accum_content_on_pendingBlock_indented#15 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingBlock.h_seqF ⇒ DECLINE+PAY",
   "h_sfx :: accum_block_on_closeThenBlock#19 :: splits=1 sup=11 [DECLINE=10,PAY=1] ⇐ - ⇒ DECLINE+PAY",
   "h_valFV :: accum_block_on_closeThenBlock#32 :: splits=1 sup=11 [DECLINE=8,FIELD=2,SPLIT=1] ⇐ -,PendingNode.pendingMapValue.h_closeFV ⇒ DECLINE+PAY+brDECLINE+brPAY",
   "h_vslot :: accum_content_on_pendingMapValue_indented#16 :: splits=3 sup=1 [FIELD=1] ⇐ PendingNode.pendingMapValue.h_vslot ⇒ ORPHAN"]
/-- **The lemmas that actually WRITE the declines** the 99 splits branch on,
    and how often each is reached.  The COUNT is per chase and per edge — a
    lemma that declines a field which several branch premises read is counted
    once for each of them — so the **19 names** are the claim and the numbers
    are how the machine re-derives them.

    This is the domain a corpus census would have to cover, and it is the
    number item 218 exists to produce: **the runtime question is not 99 splits
    wide, it is these nineteen lemmas' construction sites wide.**  Most of them
    write their declines while CONSTRUCTING a park rather than at the site that
    branches — `expectedBranchSupply`'s `⇐` column names the park field for
    every row that does, and `direct=8` is the same fact counted the other way
    round.

    **Item 259 moves one down.**  A lemma's number is the number of chases
    that END at a decline it writes (`terminals` pushes the caller of a
    `DECLINE` terminal, or of a `SPLIT` with a `DECLINE` leaf); a payment turns
    that terminal into a `PAY`, which is no site, and the compact opener's
    payment of `pendingMapValue.h_closeF` takes it from 16 to 15 — where
    items 257 and 258's payments moved their lemmas' numbers UP, because the
    count follows the chase and not the direction of the payment.  Predict it
    from the chase, or read it from the run. -/
-- Item 287: the eleven declines written into `accum_block_on_closeThenBlock`'s
-- `h_vslot` left with that binder — two by `…_pendingContent`, one each by
-- `…_pendingBlockContent` and `…_pendingBlock`, and seven by
-- `accum_block_pending` (six flat, one the value park's split branch).
-- Item 288: and one each from the four producers that declined
-- `pendingMapValue.h_vslot` with `True`, which they now pay with the stamp.
-- 2026-10-20 (item 307): `accum_content_on_pendingMapValue_indented` 12 → 15, `accum_block_on_closeThenBlock` 16 → 17, `accum_content_pending` 32 → 37, `accum_step_flow` 8 → 10, `content_dispatch_routed` 8 → 10, `accum_block_on_pendingContent` 9 → 8 —
-- the landed `-` arm's two bare declines of the new park's `h_kslot` are `h_resKslot` now (a `match` with one
-- leaf), and the content route's `h_vpack` match writes one leaf.
-- 2026-10-28 (item 380, PR #146 review): `Or.elim` read as a two-arm split — `accum_step_flow` 4 → 10,
-- `colon_open_map_explicit` 1 → 7, `compact_open_map` 1 → 7: the `Classical.em … |>.elim` decisions in the
-- value-line / flow lanes were one `VIA` each; their declining arms are DECLINE leaves written at the site now.
-- 2026-10-29 (item 394): the two flow closes' `h_framesS` declines became `valueF` relays (accum_step_flow 10 → 8); the seven declining flow-open births write `fun _ _ => Or.inr trivial` for `valueF`.
def expectedDeclineWriters : List String :=
  ["10 colon_open_map_implicit",
   "10 colon_open_map_props",
   "10 content_dispatch_routed",
   "11 accum_block_on_noPending",
   "12 accum_content_on_pendingBlock_indented",
   "15 accum_content_on_pendingMapValue_indented",
   "18 accum_block_on_closeThenBlock",
   "19 accum_block_on_pendingBlockContent",
   -- Item 409 (2026-10-30): the two `:` consumers' `h_kslotD` declines PAID — one writer fewer in each.
   "2 colon_fires_implicit_key",
   "2 colon_fires_props_key",
   "2 question_open_map",
   "32 accum_block_on_pendingBlock",
   "34 accum_block_pending",
   "37 accum_content_pending",
   "6 accum_step_flow",
   "7 colon_open_map",
   "7 colon_open_map_explicit",
   "7 compact_open_map",
   "8 accum_block_on_pendingContent"]

/-- **The ONE collapsed split, named.**  Item 216 measured `collapsed=1` and
    described its splitter chain; nothing named the edge.  It is named here
    because N-218 broke at exactly it: narrowing `pendingBlock.h_closeF` gave
    the five lemmas the join predicted, and this site — whose proof pays on
    every one of its six branches — was the eighth error where seven were
    forecast.  **A `PAY` is an answer about the PROOF and a narrowing is a
    question about the TYPE**: the `have` at
    [StreamAccum.lean:21853](../../../L4YAML/Proofs/Production/StreamAccum.lean)
    ascribes the wide `_ ∨ True` and pays it on every branch, so the census is
    right that nothing declines there and the narrowing breaks at the USE site
    all the same. -/
-- Item 350: six more "collapsed" splits — `frameChainUnion`'s `h₁`/`h₂` matches in
-- `accum_block_pending`, `accum_content_on_pendingMapValue_indented` and `explFrameValueLine`
-- pay on both branches now that the `?`-entry face's `inr` arm pays an empty chain.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-28 (item 380, PR #146 review): `Or.elim` read as a two-arm split — 12 collapsed edges more, all `via
-- Or.elim`: the `Classical.em … |>.elim` decisions whose two arms AGREE (both DECLINE) at `compact_open_map` (3),
-- `colon_open_map_explicit` (3), `accum_step_flow` (4) and `accum_flow_open_depth0` (2) — before, one `VIA` leaf each.
-- 2026-10-29 (item 389): a match-index rename only — `accum_block_on_closeThenBlock`'s `h_kslotUp` decline is now behind `match_1_31` (was `match_1_28`): the landed birth's `nv < k` split added matches before it; no edge moved.
-- 2026-10-30 (item 405): see `expectedTally`.  Rule 8 fix (same item): the chain re-indexed by the projection `markedCols sc` — the two head consumers' `match markedCols sc with | [] => Or.inr trivial` arms are new collapsed DECLINE edges (see `expectedSplitLanding`).
-- 2026-10-30 (item 408): `accum_flow_open_depth0 → flowKeyRoute_of_open#13 (h_compact_pair)` joins the collapsed
-- edges: the `pendingMapValue` arm's fabricated singleton pair `[n_old]` is DECLINED under the projection face.
def expectedCollapsedEdge : String :=
  "compact_open_map → PendingNode.pendingMapValue#16 (h_kslot) = DECLINE via Or.elim; \
compact_open_map → PendingNode.pendingMapValue#19 (h_closeFV) = DECLINE via Or.elim; \
compact_open_map → PendingNode.pendingMapValue#20 (h_framesV) = DECLINE via Or.elim; \
accum_flow_open_depth0 → flowKeyRoute_of_root#26 (h_mapFV) = DECLINE via Or.elim; \
accum_flow_open_depth0 → flowKeyRoute_of_root#26 (h_mapFV) = DECLINE via Or.elim; \
accum_content_pending → PendingNode.pendingBlockContent#12 (h_kslot) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_content_pending.match_1_59; \
accum_content_pending → PendingNode.pendingBlockContent#17 (h_kslotUp) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_content_pending.match_1_59; \
accum_content_pending → PendingNode.pendingBlockContent#12 (h_kslot) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_content_pending.match_1_59; \
accum_content_pending → PendingNode.pendingBlockContent#17 (h_kslotUp) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_content_pending.match_1_59; \
accum_content_pending → PendingNode.pendingBlockContent#12 (h_kslot) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_content_pending.match_1_59; \
accum_content_pending → PendingNode.pendingBlockContent#17 (h_kslotUp) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_content_pending.match_1_59; \
colon_open_map_explicit → PendingNode.pendingMapValue#16 (h_kslot) = DECLINE via Or.elim; \
colon_open_map_explicit → PendingNode.pendingMapValue#19 (h_closeFV) = DECLINE via Or.elim; \
colon_open_map_explicit → PendingNode.pendingMapValue#20 (h_framesV) = DECLINE via Or.elim; \
accum_block_pending → frameChainUnion#2 (h₁) = PAY via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_block_pending.match_1_23; \
accum_block_pending → frameChainUnion#3 (h₂) = PAY via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_block_pending.match_1_25; \
accum_step_flow → PendingNode.pendingContent#9 (h_vpack) = DECLINE via Or.elim; \
accum_step_flow → PendingNode.pendingContent#12 (h_framesV) = DECLINE via Or.elim; \
accum_step_flow → PendingNode.pendingContent#9 (h_vpack) = DECLINE via Or.elim; \
accum_step_flow → PendingNode.pendingContent#12 (h_framesV) = DECLINE via Or.elim; \
colon_open_map → PendingNode.pendingMapValue#16 (h_kslot) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.colon_open_map.match_1_5; \
accum_block_on_closeThenBlock → PendingNode.pendingBlock#11 (h_closeF) = PAY via Or.casesOn→Exists.casesOn→Exists.casesOn→And.casesOn→And.casesOn→And.casesOn→And.casesOn→dite; \
accum_block_on_closeThenBlock → PendingNode.pendingBlock#14 (h_kslotUp) = DECLINE via _private.L4YAML.Proofs.Production.StreamAccum.0.L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock.match_1_34→dite"

/-- **Read off the TYPE, not off a list.**  Item 211's falsification script
    enumerated five optional contexts of `content_dispatch_routed` by hand;
    the lemma states SIX — SEVEN since item 300, whose `h_markerline` is the
    marker-line reason's payload, paid by the `---` arm alone.  A hand-typed
    knob chooses its own answer, so the census names them itself. -/
def expectedOptBinders : List String :=
  ["18 h_keyctx", "20 h_suffixctx", "21 h_nodocctx", "22 h_markerctx",
   "24 h_ref", "25 h_propsctx", "26 h_markerline"]

end L4YAML.Tests.Guards.RelaySupplyCensus

open Lean Elab Command L4YAML.Tests.Guards.RelaySupplyCensus in
run_cmd do
  let (es, skipped) ← edges (ns ++ `content_dispatch_routed)
  let mut tally : Std.HashMap String Nat := {}
  for e in es do
    let k := (e.how.splitOn " ").head!
    tally := tally.insert k ((tally.getD k 0) + 1)
  let gotTally := s!"edges={es.size} skipped={skipped} {
    (tally.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotTally != expectedTally then
    throwError "the relay supply census moved.\nexpected: {expectedTally}\ngot:      {gotTally}"
  let seed := (es.filter (fun e =>
    e.callee == ns ++ `content_dispatch_routed && e.idx == 18)).map (fun e =>
      s!"{e.caller.getString!} {e.how.replace "L4YAML.Proofs.StreamAccum." ""}")
  if seed.qsort.toList != expectedSeed then
    throwError "the SEED's supply moved.\nexpected ({expectedSeed.length}):\n{
      String.intercalate "\n" expectedSeed}\ngot ({seed.size}):\n{
      String.intercalate "\n" seed.qsort.toList}"
  let mut vt : Std.HashMap String Nat := {}
  for e in es.filter (·.how.startsWith "VIA") do
    vt := vt.insert e.how ((vt.getD e.how 0) + 1)
  let prods := ((vt.toList.map (fun (k,v) =>
    s!"{v} {k.replace "L4YAML.Proofs.StreamAccum." ""}")).mergeSort (· ≤ ·))
  if prods != expectedProducers then
    throwError "the PRODUCER surface moved.\nexpected ({expectedProducers.length}):\n{
      String.intercalate "\n" expectedProducers}\ngot ({prods.length}):\n{
      String.intercalate "\n" prods}"
  -- where the pipes land, and that none of them lands on a producer
  let piped := es.filter (fun e => !e.pipes.isEmpty)
  let mut lt : Std.HashMap String Nat := {}
  for e in piped do
    lt := lt.insert s!"{String.intercalate "→" e.pipes}⇒{(e.how.splitOn " ").head!}"
      ((lt.getD s!"{String.intercalate "→" e.pipes}⇒{(e.how.splitOn " ").head!}" 0) + 1)
  let gotLanding := s!"piped={piped.size} producers={
    (piped.filter (·.how.startsWith "VIA")).size} {
    (lt.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotLanding != expectedPipeLanding then
    throwError "the PIPE LANDING moved.\nexpected: {expectedPipeLanding}\ngot:      {gotLanding}"
  -- what the SPLITs decide, and that not one of them decides it elsewhere
  let split := es.filter (·.how.startsWith "SPLIT")
  let coll := es.filter (fun e => !e.splits.isEmpty)
  let leaves := split.foldl (fun a e => a ++ e.leaves) #[]
  let mut lf : Std.HashMap String Nat := {}
  for a in leaves do
    let k := (a.splitOn " ").head!
    lf := lf.insert k ((lf.getD k 0) + 1)
  let mut sh : Std.HashMap String Nat := {}
  for e in split do
    let k := String.intercalate "|" (e.leaves.map (fun a => (a.splitOn " ").head!)).qsort.toList
    sh := sh.insert k ((sh.getD k 0) + 1)
  let gotSplit := s!"survived={split.size} collapsed={coll.size} leaves={leaves.size} \
elsewhere={(leaves.filter (fun a => a != "PAY" && a != "DECLINE")).size} {
    (lf.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)} {
    (sh.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotSplit != expectedSplitLanding then
    throwError "the SPLIT landing moved.\nexpected: {expectedSplitLanding}\ngot:      {gotSplit}"
  -- WHICH BRANCH (DOCS item 217): every surviving split's discriminant, chased
  -- to its root, with the splitter's own declared major type as the control.
  let env ← getEnv
  let pfx := "L4YAML.Proofs.StreamAccum."
  let relayRooted := split.filter (fun e => e.rootTgt.isSome)
  let optRooted := relayRooted.filter (fun e => isOptBinder env e.caller (e.rootTgt.getD 0))
  let direct := split.filter (fun e => e.disc.startsWith "RELAY#")
  let mut agree := 0
  let mut disagree : Array String := #[]
  for e in direct do
    let splitter := (e.how.splitOn " ").getLast!.toName
    match majorOf env splitter with
    | none => disagree := disagree.push s!"NOSHAPE {splitter}"
    | some m =>
        if binderHead env splitter m == binderHead env e.caller (e.rootTgt.getD 0) then
          agree := agree + 1
        else
          disagree := disagree.push s!"{e.caller.getString!}#{e.rootTgt.getD 0} {splitter}"
  let mut lsT : Std.HashMap String Nat := {}
  for e in split do
    for i in [0:e.leaves.size] do
      let k := s!"{e.leaves[i]!}-{if i < e.leafSrc.size then e.leafSrc[i]! else "?"}"
      lsT := lsT.insert k ((lsT.getD k 0) + 1)
  let gotBranch := s!"splits={split.size} leaves={
    split.foldl (fun a e => a + e.leaves.size) 0} relayRooted={relayRooted.size} \
siteDecided={split.size - relayRooted.size} optionalRoot={optRooted.size} \
plainRoot={relayRooted.size - optRooted.size} agree={agree}/{direct.size} \
disagree={disagree.size} {(lsT.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·)}"
  if gotBranch != expectedSplitBranch then
    throwError "the SPLIT BRANCH census moved.\nexpected: {
      expectedSplitBranch}\ngot:      {gotBranch}\ndisagreements: {disagree.toList}"
  let mut sd : Std.HashMap String Nat := {}
  for e in split.filter (fun e => e.rootTgt.isNone) do
    let shp := String.intercalate "|" (e.leaves.map (fun a => (a.splitOn " ").head!)).qsort.toList
    -- The splitter's name goes through `privateToUserName` first.  A generated
    -- matcher stays private inside the blanket's `public section`, so its real
    -- name is `_private.<module>.0.<user name>`; stripping only `pfx` left two
    -- rows reading `_private.L4YAML.Proofs.Production.StreamAccum.0.…`, which
    -- pins this census to a module PATH -- splitting `StreamAccum.lean` would
    -- have moved it.  The user name is the same name it has always been.
    let k := s!"{e.caller.getString!} :: {
      (Lean.privateToUserName ((e.how.splitOn " ").getLast!).toName).toString.replace pfx ""} on {
      e.disc.replace pfx ""} ⇒ {shp}"
    sd := sd.insert k ((sd.getD k 0) + 1)
  let gotSite := (sd.toList.map (fun (a,b) => s!"{b} {a}")).mergeSort (· ≤ ·)
  if gotSite != expectedSiteDecided then
    throwError "the SITE-DECIDED splits moved.\nexpected ({
      expectedSiteDecided.length}):\n{String.intercalate "\n" expectedSiteDecided}\ngot ({
      gotSite.length}):\n{String.intercalate "\n" gotSite}"
  let mut hp : Std.HashMap String Nat := {}
  for e in optRooted do
    let k := (binderName env e.caller (e.rootTgt.getD 0)).toString
    hp := hp.insert k ((hp.getD k 0) + 1)
  let gotHosts := (hp.toList.map (fun (a,b) => s!"{b} {a}")).mergeSort (· ≤ ·)
  if gotHosts != expectedBranchPremises then
    throwError "the BRANCH PREMISES moved.\nexpected ({
      expectedBranchPremises.length}):\n{String.intercalate "\n" expectedBranchPremises}\ngot ({
      gotHosts.length}):\n{String.intercalate "\n" gotHosts}"
  -- IS A DECLINE EVER SELECTED (DOCS item 218): the join of the two halves,
  -- chased upward to where the decline is actually written.
  let sm := supplyMap es
  let accounted := sm.toList.foldl (fun a (_, v) => a + v.size) 0
  let fld := es.filter (fun e => (e.how.splitOn " ").head! == "FIELD")
  let mut pairs : Std.HashMap String Nat := {}
  for e in optRooted do
    let k := keyOf e.caller (e.rootTgt.getD 0)
    pairs := pairs.insert k ((pairs.getD k 0) + 1)
  let mut supRows : Array String := #[]
  let mut nDirect := 0; let mut nDecl := 0; let mut nDead := 0; let mut nOrph := 0
  let mut maxD := 0; let mut liveS := 0; let mut deadS := 0; let mut nPark := 0
  let mut writers : Std.HashMap String Nat := {}
  for (k, nsplits) in pairs.toList do
    let parts := k.splitOn "#"
    let lem := (String.intercalate "#" (parts.dropLast)).toName
    let j := parts.getLast!.toNat!
    let sup := sm.getD k #[]
    let mut dt : Std.HashMap String Nat := {}
    for e in sup do
      let hd := (e.how.splitOn " ").head!
      dt := dt.insert hd ((dt.getD hd 0) + 1)
    let (ts, d, sites) := terminals sm {} k 0
    for w in sites do writers := writers.insert w ((writers.getD w 0) + 1)
    if dt.contains "DECLINE" then nDirect := nDirect + 1
    if ts.contains "DECLINE" || ts.contains "brDECLINE" then
      nDecl := nDecl + 1; liveS := liveS + nsplits
    else if ts.contains "ORPHAN" then nOrph := nOrph + 1
    else nDead := nDead + 1; deadS := deadS + nsplits
    maxD := max maxD d
    if sup.any (fun e => match e.fldTgt with
         | some (c, _) => (c.toString.splitOn ".").any (· == "PendingNode")
         | none => false) then nPark := nPark + 1
    let hops := String.intercalate "," ((sup.toList.map (hopName env)).eraseDups)
    supRows := supRows.push s!"{binderName env lem j} :: {
      lem.toString.replace pfx ""}#{j} :: splits={nsplits} sup={sup.size} [{
      String.intercalate "," ((dt.toList.map (fun (a,b) => s!"{a}={b}")).mergeSort (· ≤ ·))
      }] ⇐ {hops} ⇒ {setStr ts}"
  let mut cyc := 0
  for (k, _) in sm.toList do
    let (ts, _, _) := terminals sm {} k 0
    if ts.contains "CYCLE" then cyc := cyc + 1
  let gotReach := s!"pairs={pairs.size} orphan={nOrph} direct={nDirect} \
closureDecline={nDecl} dead={nDead} maxDepth={maxD} liveSplits={liveS} \
deadSplits={deadS} accounted={accounted}/{es.size} nodes={sm.size} \
fieldEdges={fld.size} fieldResolved={(fld.filter (·.fldTgt.isSome)).size} \
withCycle={cyc} declineWriters={writers.size} parkHop={nPark}"
  if gotReach != expectedDeclineReach then
    throwError "the DECLINE REACH census moved.\nexpected: {
      expectedDeclineReach}\ngot:      {gotReach}"
  let gotSupply := supRows.qsort.toList
  if gotSupply != expectedBranchSupply then
    throwError "the BRANCH SUPPLY moved.\nexpected ({expectedBranchSupply.length}):\n{
      String.intercalate "\n" expectedBranchSupply}\ngot ({gotSupply.length}):\n{
      String.intercalate "\n" gotSupply}"
  let gotWriters := (writers.toList.map (fun (a,b) =>
    s!"{b} {a.replace pfx ""}")).mergeSort (· ≤ ·)
  if gotWriters != expectedDeclineWriters then
    throwError "the DECLINE WRITERS moved.\nexpected ({
      expectedDeclineWriters.length}):\n{String.intercalate "\n" expectedDeclineWriters}\ngot ({
      gotWriters.length}):\n{String.intercalate "\n" gotWriters}"
  let gotColl := String.intercalate "; " ((es.filter (fun e => !e.splits.isEmpty)).toList.map
    (fun e => s!"{e.caller.toString.replace pfx ""} → {
      e.callee.toString.replace pfx ""}#{e.idx} ({binderName env e.callee e.idx}) = {
      e.how} via {String.intercalate "→" e.splits}"))
  if gotColl != expectedCollapsedEdge then
    throwError "the COLLAPSED edge moved.\nexpected: {
      expectedCollapsedEdge}\ngot:      {gotColl}"
  let some ci := env.find? (ns ++ `content_dispatch_routed) | throwError "no seed lemma"
  let obs := ((optBinders ci.type).1.map (fun (i, n) => s!"{i} {n}")).toList
  if obs != expectedOptBinders then
    throwError "the seed's OPTIONAL BINDERS moved.\nexpected ({
      expectedOptBinders.length}):\n{String.intercalate "\n" expectedOptBinders}\ngot ({
      obs.length}):\n{String.intercalate "\n" obs}"
