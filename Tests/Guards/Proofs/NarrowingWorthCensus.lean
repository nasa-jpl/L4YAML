import Tests.Guards.Proofs.PremiseNecessityCensus

/-!
# The worth census: a premise that is NARROWED is not thereby load-bearing (item 227)

Item 226 closed the question item 225 opened in both directions — nothing in
the `RELAY` lane can be dropped, and every optional premise can be and must not
be — and named what was left: **the narrowing itself**, the operation that turns
a vacuous premise into a load-bearing one and the thing items 212–218's supply
census was built to price.  Its sentence was *"the census says who would have
to pay; nothing yet says what the payment is worth"*.

This item measures the worth, and the first thing it had to measure is a
denominator nobody had: **every census of the optional population, from 212 to
226, read the `∨ True` WRAPPER and threw the left disjunct away.**  `isOptTy`
asks whether the type is an `Or` whose SECOND argument is `True`, and its
first argument was never taken, so the population's 163 rows had never been
asked what they are ABOUT.

(Items 221–224's ARM census does read a left disjunct — `armKind` selects
`ska = true ∨ R` by its LEFT, the right being deliberately unconstrained — but
that is a different family and the two are DISJOINT: no arm's right disjunct is
`True`, over all eight sites.  Selected from opposite ends, and only the arm
family was ever asked what it says.)

## What they are about

163 binders, **62 distinct faces**, 18 conclusion heads (§2).  Of those faces
**22 are themselves unconditionally inhabited** (§3): their left disjunct is
`∃ ns : List Nat, ∀ nv ∈ ns, P nv`, which the EMPTY LIST proves.  At those
sites `Or.inr trivial` and `Or.inl ⟨[], _⟩` are the same decline written two
ways, and the narrowing moves the premise from one unconditional inhabitant to
another.  §1 states that as a theorem and
`scripts/pay_chain_optional.py` runs it against the compiler: **14 of them paid
at once with `Or.inl ⟨[], by simp⟩`, one build, zero errors**, after which
Lean's linter calls 11 of the 14 unreferenced.

## The rule this item adds

**A premise that is NARROWED is not thereby load-bearing.**  Narrowing is not
one operation but a LADDER, and the plan's sentence names a rung rather than a
destination: rung 0 is `A ∨ True` (item 226 — all 163 vacuous), rung 1 is `A`
(here — 22 of them still vacuous), and only a rung that reaches a face with no
unconditional inhabitant buys anything.  Its companion, which is why the count
matters: **the sites where the narrowing is free are exactly the sites where it
is worthless**, because "free" and "worthless" are the same fact about the
face read from the producer's end and the consumer's.

## And the instrument the mandate named cannot answer

The mandate prescribed the corpus censuses (items 204, 219).  §4 measures their
reach: **138 of the 163 faces are grammar propositions over `SurfPos`**, which
no scanner-state census can spell — and of the **36** branch premises a
narrowing would actually target, **1** is in reach, covering **3** of the 99
splits.  That is the third consecutive mandate to name a corpus census and the
third time the named instrument was not the one that answered (items 217→218,
218→219).  The rule the three state together: **a plan sentence that names an
instrument is a hypothesis about the instrument, and it goes stale the same way
a number does.**

## A correction to this census's own selector, volunteered

`isOptTy` is syntactic.  §6 runs it against `whnf` and finds **one** definition
in `L4YAML` that unfolds to `_ ∨ True` — `ResumeKeyCtx` — carried by **two**
binders that fifteen items of censuses could not see.  **The optional
population is 165, not 163.**  Item 226's `expectedOptPopulation` pins what
`isOptTy` finds and still passes; what was wrong is the sentence beside it that
called 163 the population.  The 163-row measurements are unaffected — they are
measurements of the 163 — and every one of them is re-derived here unmoved.

## The worth, counted

§7 asks the other side of the same question: how many declarations PROVE
something unconditionally inhabited?  **27**, by two independent instruments
that select the same set.  Those 27 are what a narrowing is worth, as a
population: today each is a theorem `Or.inr trivial` would prove, and a
narrowing of its conclusion is what would make it an obligation.  Ten of them
are in `FlowKeyLift`, which is outside the supply census's one-module horizon —
the instrument-debt row item 218 opened and nothing had measured.

**And an axiom profile cannot see any of this.**  All 27 are `sorry`-free and
two of them are gated at `propext` alone.  CLAUDE.md §8 says to judge by the
axiom profile rather than by the absence of `sorry`; this is the next rung of
the same ladder — **a clean axiom profile does not say the STATEMENT is worth
proving.**
-/

namespace Tests.Guards.NarrowingWorthCensus

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs

open Lean Elab Command
open L4YAML.Tests.Guards.RelaySupplyCensus
open Tests.Guards.HypothesisReaderCensus

/-! ## §1  The ladder's second rung, as a theorem

Item 226 proved rung 0 — `opt_premise_buys_nothing : (A ∨ True → P) → P`.
Rung 1 is the same argument one level in, for the one face shape that has an
unconditional inhabitant of its own. -/

/-- The chain face is inhabited by the EMPTY chain.  This is the whole reason
    the narrowing at those sites is worth nothing: a producer that has no
    funder pays `[]` exactly as easily as it declines. -/
lemma chain_is_unconditional {P : Nat → Prop} : ∃ ns : List Nat, ∀ nv ∈ ns, P nv :=
  ⟨[], fun _ h => absurd h List.not_mem_nil⟩

/-- …so a consumer that takes the NARROWED premise proves its goal without it,
    exactly as item 226's consumer proved its goal without the optional one. -/
lemma chain_premise_buys_nothing {P : Nat → Prop} {Q : Prop}
    (k : (∃ ns : List Nat, ∀ nv ∈ ns, P nv) → Q) : Q :=
  k chain_is_unconditional

lemma chain_premise_is_no_premise {P : Nat → Prop} {Q : Prop} :
    ((∃ ns : List Nat, ∀ nv ∈ ns, P nv) → Q) ↔ Q :=
  ⟨fun k => chain_premise_buys_nothing k, fun q _ => q⟩

/-- **The narrowing itself, and what it is worth.**  For a chain face the
    lemma that takes the optional premise and the lemma that takes the narrowed
    one are the SAME lemma — each direction is one application.  This is the
    item's finding stated where it belongs, in the statement rather than in a
    census, and §3 counts the sites it covers. -/
lemma narrowing_buys_nothing {P : Nat → Prop} {Q : Prop} :
    ((((∃ ns : List Nat, ∀ nv ∈ ns, P nv) ∨ True) → Q))
      ↔ ((∃ ns : List Nat, ∀ nv ∈ ns, P nv) → Q) :=
  ⟨fun k _ => k (Or.inr trivial), fun k _ => k chain_is_unconditional⟩

/-! ## §2  What the 163 optional premises are ABOUT

The left disjunct, keyed two ways.  `faceKey` is the quantifier/arrow spine
(`E` = `∃`, `A` = dependent `∀`, `I` = `→`) down to the conclusion's head, with
`And`/`Or` descended on both sides; `deepHead` is the head alone.  Neither is a
judgment about the face — they are what lets 163 rows be read as a shape
census instead of 163 types. -/

/-- The quantifier/arrow spine, outermost first, stopping at the conclusion. -/
partial def spine : Expr → Array String → Array String × Expr
  | e, acc =>
    match e with
    | .forallE _ _ b _ =>
        if b.hasLooseBVar 0 then spine b (acc.push "A") else spine b (acc.push "I")
    | .mdata _ b => spine b acc
    | _ =>
        if e.isAppOfArity ``Exists 2 then
          match e.getArg! 1 with
          | .lam _ _ body _ => spine body (acc.push "E")
          | _ => (acc, e)
        else (acc, e)

def headName (e : Expr) : String :=
  match e.getAppFn with
  | .const n _ => n.toString
  | .fvar _ => "FVAR" | .bvar _ => "BVAR" | .sort _ => "SORT" | _ => "OTHER"

partial def faceKey (e : Expr) : String :=
  let (sp, concl) := spine e #[]
  let s := String.intercalate "" sp.toList
  if concl.isAppOfArity ``And 2 then
    s!"{s}&({faceKey (concl.getArg! 0)}|{faceKey (concl.getArg! 1)})"
  else if concl.isAppOfArity ``Or 2 then
    s!"{s}|({faceKey (concl.getArg! 0)}|{faceKey (concl.getArg! 1)})"
  else if s.isEmpty then headName concl else s!"{s}>{headName concl}"

partial def deepHead (e : Expr) : String :=
  let (_, concl) := spine e #[]
  if concl.isAppOfArity ``And 2 then deepHead (concl.getArg! 0)
  else if concl.isAppOfArity ``Or 2 then deepHead (concl.getArg! 0)
  else headName concl

/-- A declaration name with the prefixes every row shares removed, so
    `FlowBaseRoutes.mk` and `PendingNode.pendingBlock` stay distinguishable
    where a bare last component prints `mk` for both. -/
def shortName (n : Name) : String :=
  let s := n.toString
  let s := if s.startsWith "L4YAML.Proofs." then (s.drop "L4YAML.Proofs.".length).toString else s
  if s.startsWith "StreamAccum." then (s.drop "StreamAccum.".length).toString else s

/-- Every `L4YAML` declaration carrying at least one `_ ∨ True` binder. -/
def optDecls (env : Environment) : List (Name × ConstantInfo) :=
  env.constants.toList.filter fun (nm, ci) =>
    !nm.isInternal && (`L4YAML).isPrefixOf nm && !(`L4YAML.Tests).isPrefixOf nm
    && !isMechanism env nm && !(optBinders ci.type).1.isEmpty

/-- Does the named term prove the goal, with no metavariable and no `sorry`
    left?  The PROVER IS PART OF THE CLAIM: a `false` here says this term did
    not close this goal, and nothing more.  An inconclusive result is not a
    negative one.

    **Corrected at item 228.**  This used `Term.elabTerm`, which does NOT
    enforce the expected type — it returns whatever it elaborated and leaves
    the mismatch to a later `ensureHasType` that never came, and `Meta.check`
    only asks whether that term is well typed AT ALL.  So the function
    answered `true` for any closed well-typed term, whatever the goal: at item
    228 a bare `trivial` "proved" the separation's arm, `SepCommentedArm
    n s s'`.  Item 227's own numbers
    were right anyway, and for a reason worth recording — `Or.inr trivial`
    against a goal that is not an `Or` leaves `?a` unassigned, so the
    metavariable test rejected it — which is to say the selection was made by
    a side effect and not by the test the docstring claims.  Both halves are
    now explicit: elaborate ENSURING the type, and then check the inferred
    type against the goal. -/
def provableBy (stx : Term) (goal : Expr) : TermElabM Bool :=
  withoutModifyingState do
    try
      let e ← Term.withoutErrToSorry do Term.elabTermEnsuringType stx (some goal)
      Term.synthesizeSyntheticMVarsNoPostponing
      let e ← instantiateMVars e
      if e.hasExprMVar || e.hasSorry then pure false else do
        Meta.check e
        Meta.isDefEq (← Meta.inferType e) goal
    catch _ => pure false

partial def constsIn : Expr → Std.HashSet Name → Std.HashSet Name
  | .const n _, s => s.insert n
  | .app f a, s => constsIn a (constsIn f s)
  | .lam _ t b _, s => constsIn b (constsIn t s)
  | .forallE _ t b _, s => constsIn b (constsIn t s)
  | .mdata _ b, s => constsIn b s
  | .letE _ t v b _, s => constsIn b (constsIn v (constsIn t s))
  | .proj _ _ b, s => constsIn b s
  | _, s => s

partial def fvarsIn : Expr → Std.HashSet FVarId → Std.HashSet FVarId
  | .fvar f, s => s.insert f
  | .app f a, s => fvarsIn a (fvarsIn f s)
  | .lam _ t b _, s => fvarsIn b (fvarsIn t s)
  | .forallE _ t b _, s => fvarsIn b (fvarsIn t s)
  | .mdata _ b, s => fvarsIn b s
  | .letE _ t v b _, s => fvarsIn b (fvarsIn v (fvarsIn t s))
  | .proj _ _ b, s => fvarsIn b s
  | _, s => s

/-- Every binder domain anywhere inside, so an `∃ sp : SurfPos` three
    quantifiers down is still seen. -/
partial def binderDomains : Expr → Array Expr → Array Expr
  | .lam _ t b _, acc => binderDomains b (binderDomains t (acc.push t))
  | .forallE _ t b _, acc => binderDomains b (binderDomains t (acc.push t))
  | .app f a, acc => binderDomains a (binderDomains f acc)
  | .mdata _ b, acc => binderDomains b acc
  | .letE _ t v b _, acc => binderDomains b (binderDomains v (binderDomains t (acc.push t)))
  | .proj _ _ b, acc => binderDomains b acc
  | _, acc => acc

def namesSurfPos (e : Expr) : Bool := (constsIn e {}).contains ``L4YAML.Surface.SurfPos

/-- **Is this face outside a scanner-state census's vocabulary?**  Item 219's
    census evaluates `ScannerState` fields and the runtime's own functions; its
    one bridge to the surface is `ScannerSurfCorr.col_eq`, which carries a
    column and nothing else.  A face that names the surface grammar, names a
    constant whose TYPE is over `SurfPos`, binds a `SurfPos` or mentions one is
    a face that census cannot evaluate.

    The FIRST version of this test asked only the first question and read 129.
    It is wrong in the direction that flatters the instrument:
    `MarkerNodeRoute sp_start sp_land` names no `Surface` constant while being
    a grammar judgment over two `SurfPos`.  Kept as written here because
    item 204's rule applies to this item's own proxy — a class measured by a
    proxy is measured at the proxy's fidelity. -/
def isSurfFace (env : Environment) (lhs : Expr) : MetaM Bool := do
  let cs := constsIn lhs {}
  if cs.toList.any (fun n => (`L4YAML.Surface).isPrefixOf n) then return true
  for c in cs do
    match env.find? c with
    | some cci => if namesSurfPos cci.type then return true
    | none => pure ()
  for d in binderDomains lhs #[] do
    if namesSurfPos d then return true
  for f in fvarsIn lhs {} do
    if namesSurfPos (← f.getType) then return true
  return false

/-- The census's own counts.  `faces` is what makes the row count readable: 163
    binders spell 62 distinct shapes, so the population is not 163 copies of
    one idiom and not 163 unrelated facts. -/
-- Item 287: `accum_block_on_closeThenBlock`'s `h_vslot`, a face, left the
-- `_ ∨ True` population.  Item 288: and `PendingNode.pendingMapValue.h_vslot`.
-- Item 300: two binders join — `content_dispatch_routed.h_markerline`, a new
-- face (a conjunction of two line facts under the `∨ True`), and
-- `km_push_at_open.h_marker_new`, the stamp pair's shape.
-- 2026-10-20 (item 304): `heads` 18 → 19 — nine state-facing conclusions that
-- read `ResumeFrames (ExplValueLine …)` read `KeyFrames (ExplValueLine …)`, item
-- 302's stack (`ResumeFrames` 12 → 3, `KeyFrames` 9 in the head census below).
-- 2026-10-24 (item 350): binders 163 → 159, faces 61 → 59, heads 19 → 18 — `h_expl`/`h_explUp`
-- stopped being optional faces (their alternative is `NotQuestionPark sc`, paid by the `:` producers).
-- 2026-10-26 (item 369): binders=165 → binders=166 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedFaceTally : String := "binders=166 faces=62 heads=20"

/-- The conclusion head of every left disjunct.  `FVAR 2` is `frameChainUnion`,
    whose face is schematic in `P` — the two rows no census of any kind can
    evaluate, because there is nothing there to evaluate. -/
-- Item 287: `accum_block_on_closeThenBlock`'s `h_vslot` was one of the faces
-- headed `SLYamlStream`; it left the population.  Item 288:
-- `PendingNode.pendingMapValue.h_vslot`'s face, headed by its `≤`, left too.
-- 2026-10-26 (item 369): head census re-read — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedHeadCensus : List String :=
  -- Item 300: `Eq` 17 → 19, the two new optional binders (`h_markerline`, `h_marker_new`).
  -- Item 304: `ResumeFrames` 12 → 3 and `KeyFrames` 9 — the value-line stacks' heads.
  -- Item 305: `KeyFrames` 9 → 3, `lt` 23 → 28, `le` 10 → 11 — the census reads the left
  -- disjunct's FIRST conjunct, and the width bound (`<` on the two sequence fields and their
  -- three restating premises, `≤` on `closeThenBlock`'s `h_valFV`) is that conjunct at six sites.
  -- Item 350: `GLit 4` left — the four `GLit '?'` faces were `h_expl`/`h_explUp`'s optional reading;
  -- the field is required now (its alternative is `NotQuestionPark sc`, paid by the `:` producers).
  ["BareLandingFacts 8",
   "CompletedTail 4",
   "Covered 3",
   "Eq 19",
   "FVAR 2",
   "Floor 16",
   "GStar 4",
   "IndentFloor 2",
   "KeyFrames 2",
   "MarkedColsIn 15",
   "MarkerNodeRoute 5",
   "Mono 4",
   "PropsNodeRoute 4",
   -- 2026-10-27 (item 371): ResumeFrames 3 → 18, SLYamlStream 20 → 5 — every value-line pack's
   -- conclusion is a singleton `ResumeFrames` over the stream.
   "ResumeFrames 18",
   "SLYamlStream 5",
   "SeqEntryTail 7",
   "Sound 2",
   "SuffixRun 6",
   "le 11",
   "lt 29"]

/-! ## §3  The rung-1 census: which faces are vacuous on their own

The prover is `⟨[], fun _ h => absurd h List.not_mem_nil⟩` — §1's
`chain_is_unconditional` written as a term — and it is the whole of it.  The
22 rows below are the sites where the narrowing the plan calls for lands on a
premise that is still unconditionally inhabited.

The CALIBRATION is what the prover must NOT reach: `CompletedTail` (recorded
in DOCS' REMAINING section as FALSE by construction at `pendingFlow`),
`IndentFloor`, `BareLandingFacts`, `IndentStackCover.Covered`,
`n ≤ sp_scan.col` and the `implicitValueLine` equation all come back
UNSETTLED — the two pins below say so together, `expectedHeadCensus` counting
those heads and `expectedChainFaces` not naming a single one of them. -/
-- 2026-10-20 (item 309): the generic helpers' binders (`∨ alt`) leave the `∨ True` rung.
-- 2026-10-23 (item 349): three hypothesis indices +1 — `h_dead` (the column-0 landing fact) threaded into
-- `accum_content_on_pendingBlock_indented` / `accum_content_on_pendingMapValue_indented`.
-- 2026-10-24 (item 350): `explFrameValueLine#5` → `#6` — the helper takes `{alt alt' : Prop}` now.
-- 2026-10-24 (B3 [66] col-0 threading): binder indices shift with the park's new `sp_gram`/run/gate fields; faces unchanged.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base (binder indices).
def expectedChainFaces : List String :=
  -- Item 357: the marked-column domain reaches the `:`/`?` producers (`h_kslotD`, `h_explUp_chainD`) and the
  -- block-step `h_kslotUp` twins; the rung-1 faces read off the build.
  ["FlowBaseRoutes.mk#7 (vslot)",
   "accum_block_on_closeThenBlock#10 (h_vpack)",
   "accum_block_on_pendingContent#16 (h_vpack)",
   "entryKeyPack_of_dispatch#11 (h_nodeV)",
   "entryPropsKeyPack_of_dispatch#11 (h_nodeV)",
   "explFrameValueLine#6 (h_kslot)",
   "flowVPack_of_close#5 (h_vslot)",
   "frameChainUnion#2 (h₁)",
   "frameChainUnion#3 (h₂)",
   "indicator_open_map#29 (h_explUp_chain)",
   "question_open_map#26 (h_explUp_chain)"]

/-! ## §4  What a scanner-state census could evaluate

A face is out of a state census's reach if it names the surface grammar, if any
constant it names has a type over `SurfPos`, if it binds a `SurfPos`, or if it
mentions one.  The four tests are run in that order and the first that fires
decides, because the question is reachability of the face by an instrument, not
which of four reasons applies. -/
-- Item 287: the departed `h_vslot` named the surface grammar; item 288's did too.
-- Item 300: the two faces that join (`content_dispatch_routed.h_markerline`,
-- `flowOpen_marker.h_doc`) name scanner state alone, so `state` 25 → 27.
-- 2026-10-24 (item 350): binders 163 → 159, surf 136 → 132 — `h_expl`/`h_explUp` left the optional population.
-- 2026-10-26 (item 369): binders=165 → binders=166, surf=134 → surf=135 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedFidelity : String := "binders=166 surf=135 state=31"

/-- The 25 faces a state census COULD evaluate — 27 since item 300 — which is
    the population the mandate's instrument is actually defined over.  Two of them
    (`frameChainUnion`) are schematic, so the true reach is smaller than the
    number and never larger. -/
-- 2026-10-20 (item 309): binder indices re-read — `{alt : Prop}` precedes the generic helpers' premises.
-- 2026-10-24 (B3): indices shift with the new park fields (closeThenBlock 25→26, entryKeyPack 17→18,
-- entryPropsKeyPack 16→17, flowKeyRoute_of_root 21→24).
def expectedStateFaces : List String :=
  ["PreprocessIndentStable.IndentFloor.transport#3",
   "accum_block_on_closeThenBlock#26",
   "bareNodeRoute_or_refused#11",
   "bareNodeRoute_or_refused_content#12",
   "colon_open_map#23",
   "colon_open_map#24",
   "colon_open_map_explicit#21",
   "compact_open_map#29",
   "content_dispatch_after_close#22",
   "content_dispatch_routed#24",
   "content_dispatch_routed#26",
   "dedent_cover_of_landing#8",
   "dedent_cover_of_landing#9",
   "entryKeyPack_of_dispatch#18",
   "entryPropsKeyPack_of_dispatch#17",
   "flowKeyRoute_of_root#24",  -- item 311: `{g}` precedes it
   "flowOpen_floor_at_prep#10",
   "flowOpen_marker#4",
   "flowOpen_stamp#4",
   "frameChainUnion#2",
   "frameChainUnion#3",
   "frameChainUnionD#3",
   "frameChainUnionD#4",
   "indicator_open_map#26",
   "indicator_open_map#27",
   "question_open_map#22",
   "question_open_map#23",
   "question_open_map#24",
   "rootMapRouteF_or_refused#7",
   "rootMapRoute_or_refused#7",
   "topLevelFlowResumeSep_or_refused#6"]

/-! §2, §3 and §4 are gated in ONE walk, because all three read the same 163
faces and a second walk would be a second chance to disagree with the first. -/

open Meta in
run_cmd do
  let env ← getEnv
  let chainStx ← `(term| ⟨[], fun _ h => absurd h List.not_mem_nil⟩)
  let mut heads : Std.HashMap String Nat := {}
  let mut faces : Std.HashSet String := {}
  let mut chain : Array String := #[]
  let mut stateRows : Array String := #[]
  let mut binders := 0
  let mut surf := 0
  for (nm, ci) in optDecls env do
    for (i, bn) in (optBinders ci.type).1 do
      binders := binders + 1
      let key := s!"{shortName nm}#{i}"
      let (h, fk, isChain, isSurf) ← liftTermElabM do
        forallBoundedTelescope ci.type (some i) fun _ body => do
          match body with
          | .forallE _ a _ _ =>
              let lhs := a.getArg! 0
              return (deepHead lhs, faceKey lhs, ← provableBy chainStx lhs, ← isSurfFace env lhs)
          | _ => return ("NOFORALL", "NOFORALL", false, false)
      let short := (h.splitOn ".").getLast!
      heads := heads.insert short ((heads.getD short 0) + 1)
      faces := faces.insert fk
      if isChain then chain := chain.push s!"{key} ({bn})"
      if isSurf then surf := surf + 1 else stateRows := stateRows.push key
  let gotTally := s!"binders={binders} faces={faces.size} heads={heads.size}"
  if gotTally != expectedFaceTally then
    throwError "the face census moved.\nexpected: {expectedFaceTally}\ngot:      {gotTally}"
  let gotHeads := (heads.toList.map (fun (k, v) => s!"{k} {v}")).mergeSort
  if gotHeads != expectedHeadCensus then
    throwError "the head census moved.\nexpected: {expectedHeadCensus}\ngot:      {gotHeads}"
  let gotChain := (chain.qsort (· < ·)).toList
  if gotChain != expectedChainFaces then
    throwError "the rung-1 census moved.\nexpected: {expectedChainFaces}\ngot:      {gotChain}"
  let gotFid := s!"binders={binders} surf={surf} state={stateRows.size}"
  if gotFid != expectedFidelity then
    throwError "the fidelity census moved.\nexpected: {expectedFidelity}\ngot:      {gotFid}"
  let gotState := (stateRows.qsort (· < ·)).toList
  if gotState != expectedStateFaces then
    throwError "the state-reachable set moved.\nexpected: {expectedStateFaces}\ngot:      {gotState}"

/-! ## §5  The worth ledger: the price and the worth in one row

Item 217 counted, for each of the 99 optional-rooted splits, the premise its
branch is taken on; item 218 counted, for each of the 36 resulting
`(lemma, premise)` pairs, the supply edges that would have to pay.  The two
numbers have been in the same file since item 218 and have never been printed
side by side: `splits` is what a narrowing DELETES and `sup` is what it CHARGES.

This section is a derivation, not a new measurement — it reads item 218's own
`expectedBranchSupply` and §3's gated verdict.  Its control is that the parse
must recover item 217's total exactly: **99**.  A row that failed to parse
would lower it silently, which is the failure mode item 218's `accounted`
column exists to catch. -/

/-- Does another `_ ∨ True` occur inside?  A narrowing of a face that contains
    one does not finish the job: there is a second rung underneath. -/
partial def hasInnerOpt (e : Expr) : Bool :=
  isOptTy e ||
  (match e with
   | .app f a => hasInnerOpt f || hasInnerOpt a
   | .lam _ t b _ => hasInnerOpt t || hasInnerOpt b
   | .forallE _ t b _ => hasInnerOpt t || hasInnerOpt b
   | .mdata _ b => hasInnerOpt b
   | .letE _ t v b _ => hasInnerOpt t || hasInnerOpt v || hasInnerOpt b
   | .proj _ _ b => hasInnerOpt b
   | _ => false)

/-- `(premise, lemma#idx, splits, sup)` off one `expectedBranchSupply` row. -/
def ledgerParts (r : String) : Option (String × String × Nat × Nat) :=
  match r.splitOn " :: " with
  | [prem, key, rest] =>
      match rest.splitOn " " with
      | sp :: su :: _ =>
          some (prem, key, ((sp.splitOn "=").getD 1 "0").toNat!,
                           ((su.splitOn "=").getD 1 "0").toNat!)
      | _ => none
  | _ => none

/-- §3's verdict, keyed the way the ledger keys its rows. -/
def chainKeySet : Std.HashSet String :=
  expectedChainFaces.foldl (fun s r => s.insert ((r.splitOn " ").headD "")) {}

/-- **`chainSplits=12`** is the number the mandate was missing: twelve of the
    ninety-nine arms a narrowing would collapse sit on a premise whose narrowed
    form is STILL unconditionally inhabited, so collapsing them buys nothing.
    **`innerSplits=36`** is the other half: thirty-six more sit on a face that
    contains another `_ ∨ True`, so one narrowing does not reach the bottom.
    Item 256 adds one split on an `inner` face — the content sibling's second
    split on `h_closeF_old` — so `splits` 99 → 100 and `innerSplits` 36 → 37;
    the pairs and the supply do not move. -/
-- Item 287: the `h_vslot` row's own numbers — one pair, five splits, eleven
-- supplies, one `inner` — left with it.
-- 2026-10-20 (item 306): `splits` 95 → 101, the six on `h_closeFV_old` (a `-` row: neither chain nor inner).
-- 2026-10-20 (item 307): `pairs` 35 → 36, `splits` 101 → 106, `sup` 101 → 102 — the four on `h_closeFV_old` at the
-- two block routes and the content route's one on `h_mapFV108` (its `h_vpack`, a `match`).
-- 2026-10-23 (item 344): splits 106 → 107 — `on_pendingBlock#29`'s seventh split (the relayed `h_valFV`).
-- 2026-10-23 (item 345): splits 107 → 108 — the twin relay's split on `h_closeFV_old`.
-- 2026-10-24 (item 350): pairs 36 → 34, splits 108 → 104, sup 102 → 97 — the two `h_expl` pairs left.
-- 2026-10-24 (item 355): pairs 34 → 30, splits 104 → 96, sup 97 → 93, chainPairs 6 → 0, chainSplits 12 → 0 — the five
-- `MarkedColsIn`-domained ctor faces and the two domained content twins are no longer provable by the empty chain.
-- 2026-10-26 (item 369): pairs=35 → pairs=36, splits=103 → splits=104, sup=98 → sup=99, innerPairs=12 → innerPairs=13, innerSplits=55 → innerSplits=56 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
-- 2026-10-26 (item 370): splits 104 → 105, innerSplits 56 → 57 — the sibling `-` arm's split of `h_closeF_old`.
-- 2026-10-28 (item 380, PR #146 review): splits 105 → 108 — `h_kslotUp`'s `Or.elim` decisions (see the ledger); pairs/sup unchanged.
def expectedWorthTally : String :=
  "pairs=36 splits=108 sup=99 chainPairs=0 chainSplits=0 innerPairs=13 \
innerSplits=57"

/-- The ledger, worth-first.  `chain` is §3's verdict — a narrowing here lands
    on another unconditional inhabitant; `inner` means the face carries a
    further `_ ∨ True`; `-` is neither, and those are the rows where a
    narrowing could be worth something.

    Item 256 moves one row: the content sibling's `h_closeF_old` is split
    twice (the `-` arm's relay of the park's frames is the second), so
    `splits=1` reads `splits=2` and the row sorts one place up.

    Item 287: `accum_block_on_closeThenBlock`'s `h_vslot` row leaves with its
    binder (`RelaySupplyCensus.expectedTally`), and every row of the three
    lemmas that lost `sp_block_ctx` and `h_stream_fallback` reads its binder two
    places earlier, its label unmoved. -/
-- 2026-10-20 (item 306): the content lemma's `h_closeFV_old` row reads `splits=10` (4 + the six
-- key-pack stack matches) and sorts second; a `-` row still — the face is the stack itself.
-- 2026-10-20 (item 307): the two block routes' `h_closeFV_old` rows read `splits=6` and `splits=4`
-- (`h_vpack` and `h_mapFV` from the stack at each) and sort up; a new `splits=1` row for the content
-- route's `h_mapFV108` (its `h_vpack`).
-- 2026-10-20 (item 309): re-read — `explFrameValueLine`'s binder index moved (`{alt}` precedes `h_expl`).
-- 2026-10-20 (item 309): `h_expl :: explFrameValueLine#4` reads `chain` and its binder index moved (`{alt}` precedes it).
-- 2026-10-21 (item 311): `colon_open_map_implicit`'s four rows re-indexed by one (`{alt : Prop}` is its first binder); the
-- faces and splits stand, and the list is re-laid in the census's own order.
-- 2026-10-23 (item 349): three hypothesis indices +1 — `h_dead` (the column-0 landing fact) threaded into
-- `accum_content_on_pendingBlock_indented` / `accum_content_on_pendingMapValue_indented`.
-- 2026-10-24 (item 350): the two `h_expl` rows left the ledger — the face no longer splits.
-- 2026-10-24 (B3 [66] col-0 threading): binder indices shift with the new park fields; verdicts unchanged.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-354 base (binder indices).
-- 2026-10-26 (item 369): worth census re-read — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedWorthLedger : List String :=
  [
   -- 2026-10-26 (item 365): binder index #30 → #32 (`h_sound`/`h_fl0` inserted after `h_dead`); worth unchanged.
   "splits=11 sup=1 inner h_closeFV_old :: accum_content_on_pendingBlock_indented#32",
   "splits=11 sup=1 inner h_closeF_old :: accum_content_on_pendingBlock_indented#14",
   "splits=7 sup=1 - h_kslot_old :: accum_content_on_pendingBlock_indented#13",
   "splits=7 sup=1 inner h_closeF99 :: accum_content_on_pendingMapValue_indented#18",
   "splits=7 sup=1 inner h_closeFV_old :: accum_block_on_pendingBlock#31",
   -- 2026-10-28 (item 380, PR #146 review): `h_kslotUp` splits 3 → 5 at pendingBlock, 1 → 2 at pendingBlockContent —
   -- `Or.elim` is a two-arm split (`RelaySupplyCensus.isTwoArm`): the `Classical.em … |>.elim` decisions rooted at
   -- the key-slot premise count as splits; worth (`sup`, inner/-) unchanged.
   "splits=5 sup=1 - h_kslotUp :: accum_block_on_pendingBlock#30",
   "splits=5 sup=1 - h_seqF168 :: accum_content_on_pendingMapValue_indented#38",
   "splits=4 sup=1 inner h_closeFV108 :: accum_content_on_pendingMapValue_indented#20",
   "splits=4 sup=1 inner h_closeFV_old :: accum_block_on_pendingBlockContent#37",
   "splits=3 sup=4 - h_cov :: indicator_open_map#27",
   "splits=3 sup=1 - h_kslot :: accum_block_on_pendingBlock#13",
   "splits=3 sup=1 - h_kslot :: accum_content_on_pendingMapValue_indented#17",
   "splits=3 sup=1 - h_kslotUp_old :: accum_content_on_pendingBlock_indented#31",
   "splits=3 sup=1 - h_seqF_old :: accum_content_on_pendingBlock_indented#15",
   "splits=3 sup=1 - h_vslot :: accum_content_on_pendingMapValue_indented#16",
   "splits=2 sup=1 - h_kslotUp :: accum_block_on_pendingBlockContent#35",
   "splits=2 sup=1 - h_resV_land :: colon_open_map#26",
   -- 2026-10-26 (item 370): splits 1 → 2 — the sibling `-` arm splits `h_closeF_old` too (row moves from the splits=1 group).
   "splits=2 sup=1 inner h_closeF_old :: accum_block_on_pendingBlock#32",
   "splits=2 sup=1 inner h_closeF_old :: accum_block_on_pendingBlockContent#36",
   "splits=2 sup=1 inner h_routeF :: colon_open_map_implicit#12",
   "splits=2 sup=1 inner h_routeF :: colon_open_map_props#11",
   "splits=2 sup=1 inner h_routeFV :: colon_open_map_implicit#13",
   "splits=2 sup=1 inner h_routeFV :: colon_open_map_props#12",
   "splits=1 sup=11 - h_mapF :: accum_block_on_closeThenBlock#29",
   "splits=1 sup=11 - h_mk :: accum_block_on_closeThenBlock#20",
   "splits=1 sup=11 - h_pr :: accum_block_on_closeThenBlock#30",
   "splits=1 sup=11 - h_sfx :: accum_block_on_closeThenBlock#19",
   "splits=1 sup=11 - h_valFV :: accum_block_on_closeThenBlock#32",
   "splits=1 sup=11 inner h_mapFV :: accum_block_on_closeThenBlock#31",
   "splits=1 sup=1 - h_explUp_chainD :: question_open_map#29",
   "splits=1 sup=1 - h_kslot :: accum_block_on_pendingBlockContent#15",
   "splits=1 sup=1 - h_kslotD :: colon_open_map_implicit#29",
   "splits=1 sup=1 - h_kslotD :: colon_open_map_props#29",
   "splits=1 sup=1 - h_mapFV108 :: accum_block_on_pendingContent#35",
   "splits=1 sup=1 - h_resV_land :: question_open_map#27",
   "splits=1 sup=1 - h_routeS :: colon_open_map_implicit#27"]

/-- **What the mandate's instrument could have answered.**  Of the 36 pairs a
    narrowing would target, this many have a face a scanner-state census can
    evaluate, and this many of the 99 splits they cover.  Item 256: `splits`
    99 → 100, the content sibling's second split on `h_closeF_old`; the pairs,
    the state-reachable count and the state splits do not move. -/
-- Item 287: the `h_vslot` row, again.
-- 2026-10-20 (item 306): `splits` 95 → 101 (the same six); no pair, state face or state split moves.
-- 2026-10-20 (item 307): `branchPairs` 35 → 36, `splits` 101 → 106 (the same five).
-- 2026-10-23 (item 344): splits 106 → 107 — the relayed `h_valFV`'s split on `h_closeFV_old`.
-- 2026-10-23 (item 345): splits 107 → 108 — the twin relay's split on `h_closeFV_old`.
-- 2026-10-24 (item 350): branchPairs 36 → 34, splits 108 → 104 — the two `h_expl` pairs left.
-- 2026-10-26 (item 369): branchPairs=35 → branchPairs=36, splits=103 → splits=104 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
-- 2026-10-26 (item 370): splits 104 → 105 — the sibling `-` arm's split of `h_closeF_old`.
-- 2026-10-28 (item 380, PR #146 review): splits 105 → 108, same cause; reach unchanged.
def expectedBranchReach : String := "branchPairs=36 stateReachable=1 splits=108 stateSplits=3"

open Meta in
run_cmd do
  let env ← getEnv
  -- the INNER column, over the 163 faces, keyed as the ledger keys them
  let mut innerKeys : Std.HashSet String := {}
  for (nm, ci) in optDecls env do
    for (i, _) in (optBinders ci.type).1 do
      let inn ← liftTermElabM do
        forallBoundedTelescope ci.type (some i) fun _ body => do
          match body with
          | .forallE _ a _ _ => return hasInnerOpt (a.getArg! 0)
          | _ => return false
      if inn then innerKeys := innerKeys.insert s!"{shortName nm}#{i}"
  let stateKeys : Std.HashSet String := expectedStateFaces.foldl (·.insert ·) {}
  let mut rows : Array (Nat × Nat × String) := #[]
  let mut pairs := 0; let mut splitsT := 0; let mut supT := 0
  let mut chainPairs := 0; let mut chainSplits := 0
  let mut innerPairs := 0; let mut innerSplits := 0
  let mut stateReach := 0; let mut stateSplits := 0
  for r in expectedBranchSupply do
    match ledgerParts r with
    | none => throwError "a branch-supply row did not parse: {r}"
    | some (prem, key, splits, sup) =>
        pairs := pairs + 1; splitsT := splitsT + splits; supT := supT + sup
        let verdict :=
          if chainKeySet.contains key then "chain"
          else if innerKeys.contains key then "inner" else "-"
        if verdict == "chain" then chainPairs := chainPairs + 1; chainSplits := chainSplits + splits
        if innerKeys.contains key then innerPairs := innerPairs + 1; innerSplits := innerSplits + splits
        if stateKeys.contains key then stateReach := stateReach + 1; stateSplits := stateSplits + splits
        rows := rows.push (splits, sup, s!"{verdict} {prem} :: {key}")
  -- worth first, then price, then name: the two numbers are what the ledger is
  -- FOR, and a lexicographic sort would print `sup=11` above `sup=4`.
  let sorted := rows.qsort (fun a b =>
    if a.1 != b.1 then a.1 > b.1
    else if a.2.1 != b.2.1 then a.2.1 > b.2.1
    else a.2.2 < b.2.2)
  let got := (sorted.map (fun (n, sp, r) => s!"splits={n} sup={sp} {r}")).toList
  if got != expectedWorthLedger then
    throwError "the worth ledger moved.\nexpected: {expectedWorthLedger}\ngot:      {got}"
  let gotTally := s!"pairs={pairs} splits={splitsT} sup={supT} chainPairs={chainPairs} \
chainSplits={chainSplits} innerPairs={innerPairs} innerSplits={innerSplits}"
  if gotTally != expectedWorthTally then
    throwError "the worth tally moved.\nexpected: {expectedWorthTally}\ngot:      {gotTally}"
  let gotReach := s!"branchPairs={pairs} stateReachable={stateReach} splits={splitsT} \
stateSplits={stateSplits}"
  if gotReach != expectedBranchReach then
    throwError "the branch reach moved.\nexpected: {expectedBranchReach}\ngot:      {gotReach}"

/-! ## §6  A correction to the selector every census since item 212 has used

`isOptTy` is `e.isAppOfArity ``Or 2 && (e.getArg! 1).isConstOf ``True` — a test
on the SYNTAX.  A `∨ True` behind a definition is invisible to it, and there is
one: `ResumeKeyCtx`.  Two binders carry it, so **the optional population is 165,
not 163**, and fifteen items of censuses have said 163.

Nothing measured on the 163 is wrong — those items measured the 163 and this
file re-derives every one of them unmoved.  What was wrong is the sentence
beside the number.  The gate below is the instrument that would have caught it
at item 212, which is why it is written as a comparison of the two selectors
rather than as a count. -/
-- Item 287: the same binder, read syntactically.  Item 288: and the field.
-- Item 300: the two new binders, read both ways.
-- 2026-10-20 (item 309): `syntactic` 163 → 158, `population` 165 → 160 — the generic helpers' five `∨ alt` binders are no `∨ True` to the syntactic count.
-- 2026-10-21 (item 311): `syntactic` 158 → 156, `population` 160 → 158 — `colon_open_map_implicit`'s two `∨ alt` premises are no
-- `∨ True` to the syntactic count (the lemma states the family's alternative generically).
-- 2026-10-24 (item 350): syntactic 156 → 153, population 158 → 155 — as the face tally.
-- 2026-10-26 (item 369): syntactic=157 → syntactic=158, population=159 → population=160 — `accum_block_on_pendingBlock.h_closeF_old` (the `-` park's frames, read at the `:`/`?` landing for `h_res_land`).
def expectedHiddenTally : String := "hiddenDefs=1 syntactic=158 hiddenOnly=2 population=160"

def expectedHiddenDefs : List String := ["ResumeKeyCtx"]

def expectedHiddenBinders : List String :=
  ["content_dispatch_after_close|h_resumectx|17",
   "content_dispatch_routed|h_resumectx|19"]

open Meta in
run_cmd do
  let env ← getEnv
  let mut hiddenDefs : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    match ci with
    | .defnInfo _ =>
        let ok ← liftTermElabM do
          forallTelescope ci.type fun xs cod => do
            if !cod.isSort then return false
            return isOptTy (← whnf (mkAppN (mkConst nm (ci.levelParams.map mkLevelParam)) xs))
        if ok then hiddenDefs := hiddenDefs.push (shortName nm)
    | _ => pure ()
  let mut syntactic := 0
  let mut hidden : Array String := #[]
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    let rows ← liftTermElabM do
      forallTelescope ci.type fun xs _ => do
        let mut out : Array (Nat × Name × Bool × Bool) := #[]
        for j in [0:xs.size] do
          let f := xs[j]!
          let t ← inferType f
          if !(← inferType t).isProp then continue
          out := out.push (j, ← f.fvarId!.getUserName, isOptTy t, isOptTy (← whnf t))
        return out
    for (j, bn, syn, red) in rows do
      if syn then syntactic := syntactic + 1
      else if red then hidden := hidden.push s!"{shortName nm}|{bn}|{j}"
  let got := s!"hiddenDefs={hiddenDefs.size} syntactic={syntactic} \
hiddenOnly={hidden.size} population={syntactic + hidden.size}"
  if got != expectedHiddenTally then
    throwError "the hidden-optional tally moved.\nexpected: {expectedHiddenTally}\ngot:      {got}"
  let gotDefs := (hiddenDefs.qsort (· < ·)).toList
  if gotDefs != expectedHiddenDefs then
    throwError "the hidden-optional definitions moved.\nexpected: {
      expectedHiddenDefs}\ngot:      {gotDefs}"
  let gotBnd := (hidden.qsort (· < ·)).toList
  if gotBnd != expectedHiddenBinders then
    throwError "the hidden-optional binders moved.\nexpected: {
      expectedHiddenBinders}\ngot:      {gotBnd}"

/-! ## §7  The worth, counted: the declarations that prove nothing

A narrowing's worth is the obligation it creates.  This counts the obligations
that do not exist yet: declarations whose CONCLUSION `Or.inr trivial` proves.

Two instruments select the set — the elaborator, and `isOptTy` under `whnf` —
and the gate is that they agree EXACTLY, in both directions.  They are
independent: the first asks the compiler and the second asks the syntax after
one unfolding, and §6 is the item where those two disagreed about binders. -/
/-- `theorems` is the census POPULATION, and it moves whenever the library
    gains a theorem: 5138 at item 228, 5214 at item 229, **5238** at item 230,
    which added `SurfaceSpan` §6 and five payment lemmas to `FlowKeyLift` §4.

    The delta is NOT the count of `lemma` lines in the diff, and item 229 is
    where that was measured rather than assumed: the census walks environment
    constants, and Lean generates theorems no source line names — the equation
    lemma `SurfaceSpan.Span.eq_1` for a `def` is one of them.  A population
    that counts what the ENVIRONMENT holds cannot be reconciled against a grep
    over line starts, and this docstring no longer claims it can.

    What this pin carries is the other four numbers.  Item 230 moved one of
    them from 21 to 20, because `props_toKey` stopped concluding in `True`;
    item 231 took two more and left the population itself unmoved at 5238,
    because rebuilding eighteen motives and relocating four lemmas within a
    file adds no theorem to the environment.  **Item 232 takes the last
    `FlowKeyLift` row and is the first of the four to move the population**:
    the recursor application became a `mutual` block of eight lemmas, so the
    environment gains exactly seven theorems and reads **5245**.  The sixteen
    `.match_*` auxiliaries the block also creates are not theorems and are not
    counted here.  Item 259 adds one, `IndentStackCover.CoverStep.cons_of_top_eq`
    (a pinned top names the level a cover step opened): **5247**.  Item 267
    adds twenty-six: twenty-three authored lemmas — the transport restated on
    `ParkCore`, the carrier's own rides and two spends, the carrier's source and
    the two step facts it reads through — and the three projections the anchor's
    split nets, four inherited ones giving way to a parent projection and the
    two payloads' own: **5273**.  Item 269 restates that source as four
    declarations where item 267's form is two and retires `unwindIndents_pops`
    from `Proofs.Scanner.PreprocessIndentStable`; this denominator is the whole
    `L4YAML` namespace outside `Tests`, so it sees both sides of that and reads
    **5274**.  None of the four has an `_ ∨ True` conclusion, which is why the
    roster below does not move.  Item 271 adds the under-run's own column
    reading and item 272 the composition that spends it, one authored lemma
    each and neither with that conclusion: **5276**. -/
-- 2026-10-17: population 5294 → 5291 when the library took `module` headers --
-- three declarations the environment used to expose under a plain name are now
-- private-mangled and fall outside the `L4YAML` prefix.  The four numbers this
-- pin actually carries (byElab, byWhnf, elabOnly, whnfOnly) are unchanged, which
-- is what the docstring above says the pin is for.
--
-- Deliberately NOT canonicalized with `privateToUserName`, unlike the verdict
-- censuses: recovering the private-mangled GENERATED auxiliaries is right where
-- the instrument measures declarations and their auxiliaries, and wrong here,
-- where the population counts theorems -- it read 7676 instead of 5291, a 45%
-- inflation, because every generated matcher auxiliary joined the population.
-- 2026-10-18 (item 281): population 5344 → 5345 when `YamlToken.offersNodeSlot`
-- took its sixth arm.  ONE of the two constants the verdict censuses read, and
-- the difference is this pin's own rule: it does NOT canonicalize private names,
-- so `offersNodeSlot.eq_7` counts and the match auxiliary `match_1.eq_7`, which
-- the module system privatises, does not.  The four numbers this pin carries are
-- unchanged.  Both are named in [[HypothesisReaderCensus]].
-- 2026-10-18 (item 284): population 5345 → 5391, the 46 LEMMAS of item 284's 49
-- new declarations (the other three — `SlotFace`, `OfferPred`, `SlotGateAt` —
-- are definitions).  None concludes a no-op, so the four numbers this pin
-- carries hold; the declarations are named in [[HypothesisReaderCensus]].
-- Item 287: five more theorems — the four line-stop lemmas and
-- `sslComments_refutes_inline_residue` — none a no-op.
-- Item 293: eight more — the possibility lemmas named in
-- [[HypothesisReaderCensus]] — none a no-op.
-- Item 299: 5404 → 5459.  Gained 59, counted by this census's own filters
-- (`scratchpad/l4yaml-row12-steps/528-population-299.log`): the `docStartLine`
-- field's preservation family (54 lemmas in `ScannerCorrectness`, 4 in
-- `StreamAccum`) and `scanDocumentStart_docStartLine`; `markerOnLine`'s
-- generated equations are not in the population.  Lost 4, the remainder: the
-- three token walk lemmas and one equation Lean generated for the deleted
-- walk — `docStartOnLineLoop.eq_def`, the one the proofs named; inferred
-- from the remainder, not re-measured on the old tree.  None concludes a
-- no-op; the four numbers hold.
-- Item 300: 5459 → 5460, `flowOpen_marker` — the stamp lemma's twin, whose
-- conclusion is an `∨ True` the way `flowOpen_stamp`'s is, so `byElab` and
-- `byWhnf` read 18 and still agree.
-- 2026-10-20 (item 303): `theorems` 5460 → 5463 — `KeyFrames.close`,
-- `KeyFrames.ofResumeFrames`, `KeyFrames.resumeAt` (item 302's stack); none is a
-- no-op conclusion, so the four other counts stand.
-- 2026-10-20 (item 304): 5463 → 5465 — `resumeFrameRouteK`, `resumeMapRouteK`.
-- 2026-10-20 (item 309): `theorems` 5465 → 5469, `byElab` 18 → 15, `byWhnf` 18 → 15 — four lemmas more; the three generic helpers' `∨ alt` conclusions are no `∨ True` no-ops.
-- 2026-10-21 (item 311): `theorems` 5469 → 5472 — the named alternative's three conversion stubs (`PackAlt.ofRefused`,
-- `PackAltG.ofPark`, `PackAlt.ofGateClose`); the no-op counts stand: `∨ PackAltG g` on the frame's conclusions is `True` by
-- definition, so `FlowBaseRoutes.key`/`vslot` and the two key-route lemmas read as they did.
-- 2026-10-21 (item 313): `theorems` 5472 → 5474 — `ExplicitValueRefused.step_content` and `PackAlt.step_content`; neither
-- concludes an `∨ True` no-op (the wrapper concludes `PackAlt s'`, read by elaboration and by whnf alike), so the no-op
-- counts stand.
-- 2026-10-21 (item 314): `theorems` 5474 → 5476 — the two `step_dispatch` declarations; no new no-op conclusion.
-- 2026-10-21 (item 318): `theorems` 5476 → 5477 — the block lane's two transports and two wrappers (+4) less item 309's
-- three indent lemmas (−3); the no-op counts stand.
-- 2026-10-21 (item 320): `theorems` 5477 → 5479 — the two marker register lemmas of `ExplicitKeyCoupling` in the import cone; the
-- no-op counts stand.
-- 2026-10-21 (item 324): `theorems` 5479 → 5481 — `ExplicitValueRefused.step_preprocess` and its `PackAlt` wrapper;
-- neither conclusion is a no-op, and both readings stand.
-- 2026-10-21 (perf): `theorems` +1 after the base merged `scanBlockScalarIx_eq_impl`, the `@[csimp]` equation for the
-- once-bound block-scalar twin; a plain `rfl` equality, not a no-op conclusion.
-- 2026-10-23 ([162]): `theorems` 6035 → 6042 — five `parseBlockHeaderLoop_*` production lemmas and the two
-- `[163]`/`[164]` suffix lemmas; none is a no-op conclusion.
-- 2026-10-24 (N1a): `theorems` 6044 → 6049 — the `[101]`/`[104]` maximality helpers (`scanner_cond_of_isNsAnchorChar`,
-- `gnot_gchar_nil`/`gnot_gchar_head`/`gnot_gchar_of_peek_none`, `peek_none_of_fuel_zero`); none is a no-op conclusion.
-- 2026-10-23 (item 348): `theorems` 6049 → 6060 — the widened stale-key hook's lemmas (`closeStale_*`, `closeStaleAt_slots`,
-- `SlotsWitness.closeStale`, `innermost_closeStale_col0`, `reg_col_nonneg`, `hook_col0_dead`, `preprocess_col0_dead`); none is a no-op conclusion.
-- 2026-10-23 ([147] glued value): `theorems` 6060 → 6062 — the `flowGluedCollectionValue` helper lemmas
-- (`*_false_of_peekAt_blank`, its Ix twin, `*_false_of_corr_colon_blank`); none is a no-op conclusion.
-- 2026-10-24 ([148]/[149] JSON-key adjacent value, merged from the base): +5 — 2 suffix lemmas, 2 `*_toKey` lifts,
-- 2 scanner JSON-key lemmas (`isValueCandidate_glued_jsonKey` + Ix twin) less the one guard theorem counted elsewhere.
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `theorems` 6060 → 6065 — 2 suffix lemmas, 2 `*_toKey` lifts, 2 scanner JSON-key
-- lemmas (`isValueCandidate_glued_jsonKey` + Ix twin) less the one guard theorem counted elsewhere; none is a no-op conclusion.
-- 2026-10-24 (item 349): `theorems` 6060 → 6064 — the indicator-aware gate's lemmas (`staleGate_true_of_noInd`,
-- `staleGate_false_le`, `closeStaleExplicitKey_peekAt?`, the restated `closeStale_getElem?`); none is a no-op conclusion.
-- 2026-10-23 (item 349): `theorems` 6064 → 6066 — `not_blockEntryCandidate_of_dispatch_none`, `indicatorAt_false_of_dispatch_none`.
-- 2026-10-23 (item 349): `theorems` 6067 → 6073 — `staleGate_true_of_noInd`, `staleGate_false_le`, `closeStaleExplicitKey_peekAt?`,
-- the restated `closeStale_getElem?`, `not_blockEntryCandidate_of_dispatch_none`, `indicatorAt_false_of_dispatch_none`; none is a no-op conclusion.
-- 2026-10-24 (item 350): theorems 6073 → 6076 — `notQuestion_push_top`, `scanValue_notQuestion`,
-- `dispatchBlock_colon_notQuestion`.
-- 2026-10-26 (`[173]` tail confined to EOF): theorems 6308 → 6309 — `collectLineContentLoop_fst_nonempty`
-- (the non-printable stop keeps `s_after_line` only for a non-empty line run); not a no-op conclusion.
-- 2026-10-26 (item 367, `[82]`): +17 lemmas (directive loop/char bridges in StructureProduction, the three `s-l-comments` composition lemmas in StreamAccum): theorems 6309 → 6326; the elab/whnf tallies are unchanged.
-- 2026-10-26 (item 367 review): `collectTagHandleDirectiveLoop_inputEnd` removed (no caller): theorems 6326 → 6325.
-- 2026-10-27 (item 371): `ResumeFrames.one` added: theorems 6325 → 6326.
-- Item 372 (2026-10-27): `SeqTopKey.of_eq` and `seqTopKey_refuted_at_colon` (+2).
def expectedNoopTally : String := "theorems=6335 byElab=15 byWhnf=15 elabOnly=0 whnfOnly=0"
-- 5302 → 5344 on 2026-10-18 (plan row 20's close, closure-log item 280): the
-- parse-side alias obligation moved to §7.1's DECLARATION set, so the carrier
-- grew and the predicate gained its tools.  What is new in kind: `AG` carries
-- three facts instead of one, which is six accessors and two closure lemmas
-- per twin plus `AG0`'s own; the properties/finalization pair that
-- `parseNode` forms needs `propsStage_ag0`,
-- `declsBound_of_props_finalization`, `applyNodeFinalization_binds`,
-- `applyNodeFinalization_decls`, `addAnchor_decls`, `anchors_of_recordPos`
-- and `tryConsume_snd_decls` per twin; the base gained the predicate's five
-- tools (`AllAliasesDeclared.mono`, `AllAliasesResolve.of_declared`,
-- `mem_of_any_beq`, `AnchorBound.mono`, `AnchorBound.push_self`); the two
-- state-preservation proofs became reader-generic, each with two corollaries;
-- and each twin gained a capstone pair plus `DeclarationsBound`'s two
-- transport lemmas.  **The clique's own 22 lemmas per twin are a RENAME and
-- move the count not at all** — `_aar` → `_aad` with a different index — and
-- four declarations LEFT: the two `findSome?` bridges the old alias leaf went
-- through, and `AllAliasesResolve.push`/`.mono`, which an index on the
-- declaration set has no use for.  The census itself is unmoved — `byElab` and
-- `byWhnf` hold at 17 and both residual lists are empty — so only the
-- denominator changed.
-- 5282 → 5292 on 2026-10-02, and the move is +11 − 1 rather than +10 of one
-- kind.  The `+11` is authored: `ParserScannableBase.lean` carries the
-- `Scannable`-valued compose chain (`stripAnchors_preserves_Scannable`,
-- `adaptForFlowContext_scannable_forall`, `wellFormedEnvS_nil`,
-- `WellFormedEnvS.cons`, the two fold helpers,
-- `compose_value_scannable_ordered`, `compose_scannable`), plus
-- `scannableValue_has_witness` and the two `*_output_scannable_composed`
-- twins.  The `−1` is auto-generated: deleting `resolveAliasesOrdered`'s
-- parse-time fallback left its alias branch with one match arm instead of two,
-- so its `eq_*` family lost a member.  Both halves were read off the
-- environment, not inferred from the diff.  The census itself is unmoved —
-- `byElab` and `byWhnf` hold at 17 and both residual lists are empty — so only
-- the denominator changed.
--
-- 5292 → 5294 the same day, and net +2 of a +3/−1: retiring
-- `compose_value_grammable_ordered` and deriving `compose_grammable` from the
-- alias-free identity instead adds `goList_fst_of_aliasFree`,
-- `goPairs_fst_of_aliasFree` and `resolveAliasesOrdered_fst_of_aliasFree`, and
-- removes the 179-line induction they replace.  §3.2.2.2 substitutes only at an
-- alias node, so on an alias-free tree the ordered walk is the identity on
-- values and no induction over the resolver is needed — the `maxHeartbeats
-- 4000000` goes with it.
-- 5278 → 5282 on 2026-10-02: `[104] c-ns-alias-node` joined `ValidNode` and
-- `NodeToValue` (plan row 5a(vii)α), and each constructor carries two
-- auto-generated theorems.  The census itself is unmoved — `byElab` and
-- `byWhnf` hold at 17 and both residual lists are empty — so only the
-- denominator changed.

/-- The 27 item 227 measured, now **18**.  Item 228 narrowed six of
    `FlowKeyLift`'s ten — `plain_toKey`, `doubleQuoted_toKey`,
    `singleQuoted_toKey`, `sep_toKey`, `sepOpt_toKey` and the `sep_toBlockKey`
    relay — from `… ∨ True` to `… ∨ <residue>`, so `Or.inr trivial` no longer
    proves them and this instrument no longer selects them.  Item 230 took the
    seventh, `props_toKey`, by giving the separation a residue that WIDENS:
    the residue arises at the interior separation's span and the conclusion is
    about the outer one, and `breakOrEnd_extend_left`/`_right` carry it there.
    **Item 231 took the recursor application and its top wrapper**,
    `flowNode_toKey` and `flowNode_toBlockKey`, by rebuilding the eight flow
    motives around `SepResidue`.  **Item 232 takes the tenth and last**,
    `flowContent_toBlockKey`, and `FlowKeyLift` is no longer represented here
    at all.

    That one was not a motive.  It recovered the CONTENT conversion by
    wrapping its input in `SFlowNode.content`, converting, and peeling the
    node back — and the peel has four arms that the conversion rules out none
    of, so its `Or.inr` had nothing to return.  What removed it was not a
    stronger proof of the same lemma but a stronger STATEMENT to read:
    `flowContent_toKey` is a lemma in its own right now, one of eight the
    `mutual` block exports
    (`Tests.Guards.SurfaceSpanCensus.expectedMotiveExport`). -/
-- 2026-10-20 (item 309): the three generic helpers conclude in `∨ alt` and are no `∨ True` no-ops.
def expectedNoopConclusions : List String :=
  ["FlowBaseRoutes.key",
   "FlowBaseRoutes.vslot",
   "PreprocessIndentStable.IndentFloor.transport",
   "dedent_cover_of_landing",
   "flowKeyHead",
   "flowKeyRoute_of_open",
   "flowKeyRoute_of_root",
   "flowOpen_floor_at_prep",
   "flowOpen_marker",
   "flowOpen_stamp",
   "keyctx_of_preprocess",
   "markerctx_of_landing",
   "nodocctx_of_preprocess",
   "resumectx_of_landing",
   "suffixctx_of_landing"]

open Meta in
run_cmd do
  let env ← getEnv
  let stx ← `(term| Or.inr trivial)
  let mut elabSel : Array String := #[]
  let mut whnfSel : Array String := #[]
  let mut thms := 0
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    if !(`L4YAML).isPrefixOf nm then continue
    if (`L4YAML.Tests).isPrefixOf nm then continue
    if isMechanism env nm then continue
    match ci with | .thmInfo _ => pure () | _ => continue
    thms := thms + 1
    let (byElab, byWhnf) ← liftTermElabM do
      forallTelescope ci.type fun _ concl => do
        if !(← inferType concl).isProp then return (false, false)
        return (← provableBy stx concl, isOptTy (← whnf concl))
    if byElab then elabSel := elabSel.push (shortName nm)
    if byWhnf then whnfSel := whnfSel.push (shortName nm)
  let a : Std.HashSet String := elabSel.foldl (·.insert ·) {}
  let b : Std.HashSet String := whnfSel.foldl (·.insert ·) {}
  let elabOnly := elabSel.toList.filter (!b.contains ·)
  let whnfOnly := whnfSel.toList.filter (!a.contains ·)
  let got := s!"theorems={thms} byElab={elabSel.size} byWhnf={whnfSel.size} \
elabOnly={elabOnly.length} whnfOnly={whnfOnly.length}"
  if got != expectedNoopTally then
    throwError "the no-op conclusion tally moved.\nexpected: {expectedNoopTally}\n\
got:      {got}\nelabOnly: {elabOnly}\nwhnfOnly: {whnfOnly}"
  let gotRows := (elabSel.qsort (· < ·)).toList
  if gotRows != expectedNoopConclusions then
    throwError "the no-op conclusions moved.\nexpected: {
      expectedNoopConclusions}\ngot:      {gotRows}"

end Tests.Guards.NarrowingWorthCensus
