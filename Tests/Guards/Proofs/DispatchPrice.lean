/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ProducerDerivation

/-!
# What a dispatch equation buys (DOCS item 242)

Item 241 refuted derivability at the park's producer: a `ScannerSurfCorr` is a
statement about a POINT and the datum `SLYamlStream sp_start sp_scan'` is a
statement about a PATH, and the library turns one into the other at the stream's
seed and nowhere else.  Its recorded NEXT named the four consumers as holding
what the producer does not — a dispatch equation and a second correspondence,
at the position BEFORE the step — and called that pair the first thing in the
chain that could turn a point into a path.

**Three of those four hold no dispatch equation.**
`block_dispatch_deferred_inline`, `…_stamp_nopack` and `…_stamp_offcol` carry
branch evidence — `_h_src`, `_h_indent`, `_h_ne`, `_h_park`, `_h_res` — and pass
the producer's own five arguments straight through.  `accum_content_pending` is
the one that holds `scanNextToken_dispatchContent … = .ok s'`, and its second
correspondence is its CONCLUSION rather than a hypothesis.  So the census below
is taken over the whole population instead of over that ring.

## The answer: availability is 299 and derivation is 1

§2 reads every authored statement for a scanner step equation `f … = .ok …`
and for a grammar path landing on the position the step's output names.

| rung | what it asks | count |
|---|---|---|
| `dispHolders` | a `scanNextToken_dispatch*` equation is held | ~~299~~ ~~300~~ **303** |
| `dispTwoCorr` | …with two correspondences beside it | **28** |
| `edge` | a production LANDS on the step's output position | **4** |
| `chain` | a production path RUNS from a known point to it | **1** |

The one is `indentedValue_reads_at_any_indent`, and per FUNCTION the reading is
sharper still: of **72** distinct scanner step functions appearing in step
equations, **one** carries a numbered spec production across it and **two**
carry any Surface relation at all — `scanNextToken_preprocess` (6 of its 186
holders) and `scanNextToken_dispatchContent` (1 of its 129).  The step that
consumes SEPARATION is grammar-visible and routine; the step that consumes
CONTENT is grammar-visible once.  **A census that counts equations measures
availability, and the two numbers are 299 and 1.**

`indentedValue_reads_at_any_indent` is in neither item 238's transitive set nor
either repair thread, so the one worked precedent stands outside β.5's bill.

## And the escape's repaired form needs no arm at all

`SLYamlStream.scannerDrop` takes a stream to `s₁` and an `SSLComments` from an
unrelated `s₂`, which is what makes it hold of every string.  §1 proves that
**connecting the two halves makes the arm redundant**: given `SLYamlStream a b`
and `SSLComments b c`, `SLYamlStream a c` follows from `implicitContinue`,
`SLDocumentPrefix.comments` and the fact that an `s-b-comment` is an
`l-comment`.  `connected_drop_nd` proves the same in item 239's post-β.5 model,
where the arm is gone, so the derivation is not circular — and the pin below
checks that neither proof mentions `SLYamlStream.scannerDrop`.

**So the grammar side of β.5 is three lines, and the whole bill is the
connection.**  What items 240 and 241 priced — nineteen statements threading a
premise through `close_with_ssl`, or eighteen through the producer — is not the
cost of proving the step; it is the cost of establishing that the production
starts where the stream ends.

**The derivation spends `[66]`'s start-of-line arm.**  `s-separate-in-line` is
`s-white+ | <start-of-line>`, and `SSeparateInLine.startOfLine` holds exactly at
column 0 (`L4YAML/Surface/Basic.lean`).  `ssb_to_slcomment`'s `noSep` branch
spends it, so the escape is available only where the comment run begins at
column 0 — the `hcol` premise below — and the pin records the dependency rather
than leaving it to a reader.
-/

namespace Tests.Guards.DispatchPrice

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML (getYamlSpecRefs)
open Tests.Guards.DropFalsity (StreamND)
open Tests.Guards.DropDependents (usesAll census modOf sorted)
open Tests.Guards.RepairChoice (revEdges thread producer supplier)

/-! ## §1 The connected escape -/

lemma ssb_to_slcomment {a b : SurfPos} (h : SSBComment a b) (hcol : a.col = 0) :
    SLComment a b := by
  cases h
  case withSep =>
    rename_i s₁ s₂ hsep hopt hb
    exact SLComment.mk _ s₁ s₂ _ hsep hopt hb
  case noSep =>
    rename_i hb
    exact SLComment.mk _ _ _ _ (SSeparateInLine.startOfLine_of_col0 hcol) (GOpt.none _) hb

lemma sslcomments_to_prefix {a b : SurfPos} (h : SSLComments a b) (hcol : a.col = 0) :
    SLDocumentPrefix a b := by
  cases h
  case withComment =>
    rename_i s₁ hsb hstar
    exact SLDocumentPrefix.comments _ _
      (GStar.cons _ s₁ _ (ssb_to_slcomment hsb hcol) hstar)
  case startOfLine =>
    rename_i chars hstar
    exact SLDocumentPrefix.comments _ _ hstar

lemma connected_drop {a b c : SurfPos}
    (h : SLYamlStream a b) (hc : SSLComments b c) (hcol : b.col = 0) : SLYamlStream a c :=
  SLYamlStream.implicitContinue a b c c c h
    (GStar.cons b c c (sslcomments_to_prefix hc hcol) (GStar.nil c))
    (GOpt.none c) (GStar.nil c)

lemma connected_drop_nd {a b c : SurfPos}
    (h : StreamND a b) (hc : SSLComments b c) (hcol : b.col = 0) : StreamND a c :=
  StreamND.implicitContinue a b c c c h
    (GStar.cons b c c (sslcomments_to_prefix hc hcol) (GStar.nil c))
    (GOpt.none c) (GStar.nil c)

/-! ## §2 The census -/

def isProd (n : Name) : MetaM Bool := do
  let some ci := (← getEnv).find? n | return false
  forallTelescope ci.type fun xs concl => do
    unless concl == mkSort Level.zero do return false
    if xs.size < 2 then return false
    return (← inferType xs[xs.size-2]!).isConstOf ``SurfPos
      && (← inferType xs[xs.size-1]!).isConstOf ``SurfPos

partial def scanAux (prods : Std.HashSet Name) (e : Expr) :
    StateM (Std.HashSet Expr × Array (Name × Expr × Expr) × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a, b) => (s.insert e, a, b)
  if let .const n _ := e.getAppFn then
    if prods.contains n then
      let args := e.getAppArgs
      if args.size ≥ 2 then
        modify fun (s, a, b) => (s, a.push (n, args[args.size-2]!, args[args.size-1]!), b)
  if e.isAppOfArity ``ScannerSurfCorr 2 then
    modify fun (s, a, b) => (s, a, b.push e.appArg!)
  let _ ← e.foldlM (fun (_ : Unit) s => scanAux prods s) ()

def scanE (prods : Std.HashSet Name) (e : Expr) :
    Array (Name × Expr × Expr) × Array Expr :=
  let (_, a, b) := ((scanAux prods e).run ({}, #[], #[])).2
  (a, b)

def stepEqFn? (t : Expr) : Option Name := do
  guard (t.isAppOfArity ``Eq 3)
  let lhs := t.appFn!.appArg!
  guard (t.appArg!.isAppOf ``Except.ok)
  let .const f _ := lhs.getAppFn | none
  guard ((`L4YAML.Scanner).isPrefixOf f)
  some f

partial def fvarsAux (e : Expr) : StateM (Std.HashSet Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a) => (s.insert e, a)
  if e.isFVar then modify fun (s, a) => (s, a.push e)
  let _ ← e.foldlM (fun (_ : Unit) s => fvarsAux s) ()

def okStates (t : Expr) : MetaM (Array Expr) := do
  let vs := ((fvarsAux t.appArg!).run ({}, #[])).2.2
  vs.filterM fun v => return (← inferType v).isConstOf ``ScannerState

structure R where
  fns      : Array Name := #[]
  edgeFns  : Array Name := #[]
  chainFns : Array Name := #[]
  twoCorr  : Bool := false
deriving Inhabited

def readDecl (prods : Std.HashSet Name) (n : Name) : MetaM R := do
  let some ci := (← getEnv).find? n | return {}
  forallTelescope ci.type fun xs concl => do
    let (pc, _) := scanE prods concl
    let mut fns : Array Name := #[]
    let mut posts : Array (Name × Expr) := #[]
    let mut corrHyps : Array Expr := #[]
    let mut corrAt : Array (Expr × Expr) := #[]
    let mut pAll := pc
    for x in xs do
      let t ← inferType x
      if let some f := stepEqFn? t then
        fns := fns.push f
        for st in ← okStates t do posts := posts.push (f, st)
      if t.isAppOfArity ``ScannerSurfCorr 2 then
        corrHyps := corrHyps.push t.appArg!
        corrAt := corrAt.push (t.appFn!.appArg!, t.appArg!)
      pAll := pAll ++ (scanE prods t).1
    let reach (src : Expr) : Std.HashSet Expr := Id.run do
      let mut seen : Std.HashSet Expr := {src}
      let mut todo : List Expr := [src]
      while !todo.isEmpty do
        let x := todo.head!
        todo := todo.tail!
        for (_, a, b) in pAll do
          if a == x && !seen.contains b then
            seen := seen.insert b
            todo := b :: todo
      return seen
    let mut edgeFns : Array Name := #[]
    let mut chainFns : Array Name := #[]
    for (f, st) in posts do
      for (s, p) in corrAt do
        if s == st then
          if pAll.any (fun (_, _, b) => b == p) then edgeFns := edgeFns.push f
          if corrHyps.any (fun q => q != p && (reach q).contains p) then
            chainFns := chainFns.push f
    return { fns := fns, edgeFns := edgeFns, chainFns := chainFns,
             twoCorr := corrHyps.size ≥ 2 }

/-! ## §3 The pins -/

/-- The grammar's alphabet over surface positions, three nested populations.
    `prodTyped` takes every relation whose last two arguments are `SurfPos` and
    so includes the proof layer's own composites (`PendingNode`, `BlockStack`,
    `ImplicitKeyHead`, `PropsRun`); `prodSurf` keeps the `L4YAML/Surface`
    modules, which are the spec transcription and its combinators; `prodSpec`
    keeps only what carries a NUMBERED `@[yaml_spec]` rule.  A combinator
    application like `GStar SSWhite` is headed by `GStar`, which carries no rule
    number of its own, which is why `prodSurf` and not `prodSpec` is the
    population the findings are read over. -/
-- 2026-10-23 ([162]): +2 on all three — `SCIndentationIndicator` and `SCChompingIndicator`, both `@[yaml_spec]`-cited.
-- 137 → 145 on 2026-10-23: the eight multi-line relations of the same module (`SBBreakOk`,
-- `SLEmptyOk`, `DQBreakOk`, `DQTextOk`, `SCDoubleQuotedMultiOk` and the single-quoted twins).
-- 145 → 149 on 2026-10-23: the four one-line plain relations of `Acceptance/Plain.lean`
-- (`PlainCharOk`, `PlainEntryOk`, `PlainFirstOk`, `PlainOneLineOk`; Stream E).
-- 150 → 151 on 2026-10-23: `PlainNextLineOk`, the multi-line plain relation of the same module.
-- 151 → 152 on 2026-10-23: `TagOk`, the narrowed `[97]` relation of `Acceptance/Properties.lean` (Stream E).
-- 152 → 159 on 2026-10-23: the seven block-scalar relations of `Acceptance/BlockScalar.lean`
-- (`BlockLineOk`, `BlockStopOk`, `ChompOk`, `IndentOk`, `HeaderIndicatorsOk`, `HeaderTailOk`,
-- `AutoIndentOk`; Stream E).
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `prodTyped` 160 → 162, `prodSurf` 94 → 96, `prodSpec` 56 → 58 —
-- `SCFlowJsonContent` [154] and `SCFlowJsonNode` [160] enter the surface alphabet.
-- 2026-10-24 (B3): prodTyped 162 → 164 — the explicit JSON-key adjacent-value twins in Surface/Node.lean.
-- 2026-10-25 (#99 review): prodTyped 164 → 163 — the dead `FlowLead` (a `FrameTail`-indexed duplicate of `leadFree`) is deleted.
-- 2026-10-25 (slice 2, `TraceOf/UniqueFlow.lean`): prodTyped 163 → 165 — the proof-layer relations `PStep`
-- (one plain-scalar step) and `Follow` (the flow follow-set on two end positions); not Surface, not `@[yaml_spec]`.
-- 2026-10-26 (item 367, `[82]`): `DigitRun`, `DirectiveStop`, `DirectiveTail`, `ScannedDirective` (StructureProduction) are typed over surface positions: prodTyped 165 → 169.
def expectedAlphabet : String := "prodTyped=169 prodSurf=96 prodSpec=58"
-- 133 → 137 on 2026-10-23: the four narrowed relations of `Proofs.Production.Acceptance.Quoted`
-- (`DQCharOk`, `SQCharOk`, `SCDoubleQuotedOk`, `SCSingleQuotedOk`); not under `Surface`, no rule tag.

/-- The step population, which no choice of grammar moves: 1649 statements hold
    a scanner step equation, 299 of them a dispatch equation, and 28 of those
    hold it with two correspondences — the pair item 241's NEXT called the first
    thing that could turn a point into a path.  Of the 72 step functions, 26 are
    the indexed twin's.

    Item 267 adds the three that hold one: the carrier's source
    (`preprocess_landing_on_stack`), the dedent it reads it through
    (`preprocess_pops_of_below`) and the `skipToContent` wrapper their proof
    spends.  None is a dispatch and both functions were already among the 72, so
    only the first count moves.

    Item 269 adds one more, `preprocess_floor_eq`, which is where the step
    equation is spent for all three.  The fourth declaration of that source,
    `landing_on_stack_of_floor_eq`, holds NONE: it reads one state's own stack
    against one state's own column and names no scanner step, which is what
    makes it the cheap end of the chain.

    Item 272 adds one, `underRunEnd_landing_on_stack`, the composition that
    applies that source at an arm holding the `[63]` failure located: it hands
    the step equation on to `preprocess_landing_on_stack`, so it holds one.
    Item 271's `underRunEnd_col_le_currentIndent` holds none and moves nothing
    here — it reads the landing's column off the under-run and names no step,
    which is the same reason `landing_on_stack_of_floor_eq` sits outside the
    population.

    Moved to 1654 on 2026-10-02 by ONE holder and no new step:
    `parseStream_output_scannable_composed`, the hypothesis-free `Scannable`
    twin of `parseStream_output_grammable`, carries the same
    `Scanner.scanFiltered input = .ok tokens` premise and so names the same
    step its sibling does.  Its indexed twin takes `FlowAwarePSVIx` rather than
    `scanFilteredIx` and names none, which is why this is +1 and not +2 —
    `fns` holds at 72 and `fnsIx` at 26, so the step population itself is
    unmoved and only the holder count changed.

    Moved to 1674 / 299 on 2026-10-18 by item 284's token lemmas and no new
    step: twenty of its new declarations hold a step equation, five of those a
    dispatch equation — `dispatchBlock_dash_offerPred`,
    `dispatchBlock_colon_offerPred`, `dispatchBlock_question_offerPred`,
    `dispatchBlock_colon_or_question_offerPred` and `slotGateAt_spend`.  None
    holds two correspondences (`dispTwoCorr` stays 28), `fns` and `fnsIx` hold,
    and with the 49 declarations excluded the census reads 1654 / 294 again, so
    availability rose by what the slot face reads and derivation did not move.

    Moved to 1675 / 300 by DOCS item 287 and no new step:
    `block_dispatch_deferred_inline` reads its three premises off the dispatch
    now, so its statement holds the preprocessing and dispatch equations it
    did not hold before.  It holds one correspondence (`dispTwoCorr` stays 28),
    and `fns` and `fnsIx` hold.

    Moved to 1681 / 303 by DOCS item 293 and no new step: six of its new
    declarations hold a step equation — `preprocess_saved_key_possible_post`,
    `preprocess_possible_of_live0` and `close_poss_of_base` a preprocessing
    one, `live_of_dispatch`, `dispatchContent_blockScalar_ska` and
    `content_live0` a content dispatch (`content_live0` both).  None holds two
    correspondences, and `fns` and `fnsIx` hold.

    Moved to 1706 / 305 by DOCS item 299 and no new step: the `docStartLine`
    preservation family cloned from `implicitValueLine`'s holds a step
    equation at 25 of its lemmas, two of them a content dispatch
    (`dispatchContent_preserves_docStartLine` and `dispatchContent_docStartLine`); the rest state pure functions.  None holds two
    correspondences, and `fns` and `fnsIx` hold.

    Moved to 1707 / 305 by DOCS item 300 and no new step: `flowOpen_marker`,
    the stamp lemma's twin, holds preprocessing's equation and no path. -/
-- 2026-10-20 (item 309): three lemmas more mention the preprocess step (the sentinel transports and the refutation): `stepHolders` 1707 → 1710.
-- 2026-10-21 (item 313): `stepHolders` 1710 → 1712, `dispHolders` 305 → 307 — `ExplicitValueRefused.step_content` and
-- `PackAlt.step_content` state the preprocess and content-dispatch steps as hypotheses.
-- 2026-10-21 (item 314): `stepHolders` 1712 → 1714, `dispHolders` 307 → 309 — `ExplicitValueRefused.step_dispatch` and
-- `PackAlt.step_dispatch` hold the content dispatch.
-- 2026-10-21 (item 315): `dispHolders` 309 → 310, `dispTwoCorr` 28 → 29 — `entryPropsKeyPack_of_dispatch` takes the content
-- dispatch as a premise beside its two correspondences.
-- 2026-10-21 (item 318): `stepHolders` 1714 → 1716, `dispHolders` 310 → 314 — the block lane's two transports
-- (`ExplicitValueRefused.step_blockEntry`, `.step_value`) and their `PackAlt` wrappers hold the block dispatch, the two
-- predicate lemmas also the preprocess; item 309's three indent lemmas, deleted, held neither step.
-- 2026-10-21 (item 320): `stepHolders` 1716 → 1717 — `ExplicitKeyCoupling.scanDocumentEnd_explicitKeyLine` holds the `...`
-- scan's step (`scanDocumentEnd s = .ok s'`), the marker parks' dead-register fact; the dispatch holders stand.
-- 2026-10-21 (item 324): `stepHolders` 1717 → 1719 — `ExplicitValueRefused.step_preprocess` and its wrapper
-- `PackAlt.step_preprocess` (the family's preprocess transport) each hold the preprocess step equation; dispatch holders stand.
-- 2026-10-23 (Stream E): `stepHolders` 1817 → 1818, `fns` 72 → 73 — `scanValue_accepts` in
-- `Acceptance/BlockIndicators.lean` holds `scanValue`'s step equation; dispatch holders stand.
-- 2026-10-23 (Row 12, item 348): `stepHolders` 1818 → 1819 — `preprocess_col0_dead` in
-- `PendingKeySound.lean` holds `scanNextToken_preprocess`'s step equation; dispatch holders stand.
-- 2026-10-24 (Row 12, item 350): `stepHolders` 1821 → 1823, `dispHolders` 334 → 335 —
-- `scanValue_notQuestion` and `dispatchBlock_colon_notQuestion` hold the `:` step/dispatch equations.
-- 2026-10-24 (B3 [66] col-0 threading): re-read on the item-355 base.
-- 2026-10-29 (item 387): stepHolders 1894 → 1895, dispHolders 362 → 363 — `seqTop_refuted_at_indicator_le`
-- (item 378's refutation with the cursor bound as its premise) holds the dispatch over the directive-reset twin.
-- 2026-10-29 (item 389): stepHolders 1895 → 1902, dispHolders 363 → 368 — `pushedBirth_not_mapTop`, `noPushBirth_indents`, `contentLanding_indents_eq` and the `popStep`/unwind lemmas hold the `-`/content dispatch and the preprocess step as hypotheses.
-- 2026-10-29 (item 394, option B): +1 step holder — `preprocess_indents_subset` (the
-- preprocess only pops the indent stack; the cover's transport to the flow opener).
-- 2026-10-29 (item 396): flowOpen_floor_at_prep deleted — one scanNextToken_preprocess holder fewer.
def expectedSteps : String :=
-- 2026-10-24 (B3 [66] col-0 threading): stepHolders 1819 → 1874, dispHolders 332 → 348, dispTwoCorr 29 → 31 —
-- the gate/JSON-key/reservation lemmas hold the preprocess and dispatch step equations (1878/351 on the
-- item-354 base).
-- 2026-10-25 (item 359): stepHolders 1887 → 1888 — `scanValue_refused_of_outer` (RegisterWitness) holds the
-- `scanValue s = .ok s'` step equation.
-- Item 372 (2026-10-27): `seqTopKey_refuted_at_colon` holds the `:` dispatch step (+1 step/disp holder).
  "stepHolders=1942 dispHolders=374 dispTwoCorr=31 fns=73 fnsIx=26"

/-- **The ladder, at each population.**  `edge` is a production whose right
    endpoint is the step's output; `chain` requires a path to it from another
    correspondence's position, existential midpoints allowed — which is what
    `implicitKeyHead_of_dispatch` needs and a single edge misses.  The counts
    fall 299 → 28 → 18 → 6 → 1 as the question tightens from availability to
    derivation. -/
-- 2026-10-24 (B3 [66] col-0 threading): TYPED 20/7/3 → 22/4/4, SURF 18/6/2 → 20/3/3 — the parks now export
-- the grammar endpoint `sp_gram` directly, so three chain-only correspondences became edges and the
-- explicit JSON-key twins add two.
-- 2026-10-29 (item 389): TYPED edge 22 → 23, SURF edge 20 → 21 — `contentLanding_indents_eq` holds the content dispatch typed through `ScannerSurfCorr`.
-- 2026-10-29 (item 396): flowOpen_floor_at_prep deleted — one TYPED and one SURF holder fewer on the ladder.
def expectedLadder : List String :=
  ["TYPED edge=22 chain=4 fnEdge=4 fnChain=2",
   "SURF edge=20 chain=3 fnEdge=3 fnChain=2",
   "SPEC edge=4 chain=1 fnEdge=2 fnChain=1"]

/-- The six that carry a Surface path across a scanner step.  Five are
    preprocessing's; the sixth holds both equations, which is why the per
    function counts (6 and 1) sum to more than the six declarations here. -/
-- 2026-10-24 (B3 [66] col-0 threading): `SSeparateLines_at_interior`, `keyctx_of_preprocess` and
-- `tab_refutes_dispatch` now read the park's `sp_gram` edge directly (no chain across the step); the
-- `_inline` twin still chains.
def expectedChainSurf : List Name :=
  [`L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent,
   `L4YAML.Proofs.StreamAccum.preprocess_flow_thread,
   `L4YAML.Proofs.StreamAccum.tab_refutes_dispatch_inline]

/-- **And the one that carries a NUMBERED production across a content
    dispatch.**  Its conclusion pairs `SSeparateLines n sp_scan sp_prep` with a
    node reading from `sp_prep` to the dispatch's own output. -/
def expectedChainSpec : List Name :=
  [`L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent]

/-- The two functions, with how many of their holders carry the path.  Item 267
    adds two holders of preprocessing's equation — the carrier's source and the
    dedent it reads it through — and neither carries a path, so only the first
    number moves.  Item 269 adds the third, `preprocess_floor_eq`, which is
    where both of those now spend the equation; it carries no path either.
    Item 272 adds the fourth, `underRunEnd_landing_on_stack`, which hands the
    equation to the source rather than reading a position off it — so it is a
    holder and not a path, and the second number stays at six.  Item 284 adds
    eleven holders of preprocessing's equation and one of the content
    dispatch's, all of them the slot face's transport and gate lemmas —
    `slotFace_preprocess`, `slotRun_of_dn`, `slotRun_of_offer`,
    `preprocess_tokens_of_indents_eq`, `preprocess_pop_pred_nonprop`,
    `preprocess_indents_of_size_le_one`, `slotGateAt_of_pop`,
    `slotGateAt_of_offerPred`, `slotGateAt_of_propsPark`,
    `slotGateAt_of_parkSource`, `slotGateAt_of_noPending`, and
    `slotGateAt_spend` for the dispatch — and none carries a path, so both
    second numbers hold.  DOCS item 287 adds one holder of preprocessing's
    equation, `block_dispatch_deferred_inline`, with no path.  DOCS item 293
    adds four holders of preprocessing's (`preprocess_saved_key_possible_post`,
    `preprocess_possible_of_live0`, `close_poss_of_base`, `content_live0`) and
    three of the content dispatch's (`live_of_dispatch`,
    `dispatchContent_blockScalar_ska`, `content_live0`), none with a path.
    DOCS item 299 adds two holders of each, the `docStartLine` field's
    transport: `preprocess_preserves_docStartLine` and `ad_docStartLine` hold
    preprocessing's equation, `dispatchContent_preserves_docStartLine` and
    `dispatchContent_docStartLine` the content dispatch's, none with a path.
    DOCS item 300 adds one holder of preprocessing's, `flowOpen_marker`, with
    no path. -/
-- 2026-10-20 (item 309): `scanNextToken_preprocess` decls 209 → 212 (the sentinel transports and the refutation).
-- 2026-10-21 (item 313): both steps' declaration counts +2 — `ExplicitValueRefused.step_content` and
-- `PackAlt.step_content` hold the preprocess and the content dispatch as hypotheses.
-- 2026-10-21 (item 314): the dispatch rung +2 (the two `step_dispatch` declarations); the preprocess rung stands.
-- 2026-10-21 (item 315): the dispatch rung +1 — `entryPropsKeyPack_of_dispatch`.
-- 2026-10-21 (item 318): `preprocess decls` 214 → 216 — the block lane's two transports and their two wrappers hold the
-- preprocess (+4), item 309's `preprocess_currentIndent_neg` and `indent_neg_dis_of_park`, deleted, held it too (−2).
-- 2026-10-21 (item 324): `scanNextToken_preprocess decls` 216 → 218 — the two preprocess-transport lemmas of the alternative
-- family (`ExplicitValueRefused.step_preprocess`, `PackAlt.step_preprocess`) read the preprocess equation; the content dispatch stands.
-- 2026-10-23 (item 349): `stepHolders` 1819 → 1821, `dispHolders` 332 → 334 — `not_blockEntryCandidate_of_dispatch_none`
-- and `indicatorAt_false_of_dispatch_none` hold the block-indicator dispatch equation.
-- 2026-10-23 (item 348): `scanNextToken_preprocess decls` 223 → 224 — `preprocess_col0_dead` (the column-0 landing fact).
-- 2026-10-24 (B3 [66] col-0 threading): dispatchContent 146 → 157, preprocess 224 → 240 holders (gate / JSON-key
-- / reservation lemmas); preprocess chain 6 → 3 — three carriers now read the `sp_gram` edge directly.
-- 2026-10-29 (item 389): dispatchContent decls 159 → 160 (`contentLanding_indents_eq`), preprocess 243 → 246 (it plus `preprocess_currentIndent_le`, `preprocess_indents_eq_of_le`).
def expectedPerFn : List String :=
  ["scanNextToken_dispatchContent decls=161 chain=1",
   "scanNextToken_preprocess decls=248 chain=3"]

/-- **The one worked precedent is outside the work.**  It is not in item 238's
    transitive set and not on either repair thread, so β.5 neither pays for it
    nor inherits it. -/
def expectedOne : String := "inT=false onThread=false onProdThread=false"

/-- **What §1's derivation spends and what it does not.**  `startOfLine`
    records whether the `noSep` branch rides on the ε `s-separate-in-line`
    ([66]; col-0 only since the B3 threading, hence `false`);
    `drop=false` is the non-circularity check — a proof that the escape is
    redundant may not route through the escape. -/
-- 2026-10-24 (B3 [66] col-0 threading): startOfLine true → false — the derivation no longer spends the
-- ε `s-separate-in-line` (now col-0 only); its separators are the scanner's own white runs.
def expectedWeak : String := "startOfLine=false drop=false"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pre := usesAll env
  let (authored, usesVal) := pre
  -- §2a the alphabet
  let mut prodTyped : Std.HashSet Name := {}
  let mut prodSurf : Std.HashSet Name := {}
  let mut prodSpec : Std.HashSet Name := {}
  for n in authored do
    if ← isProd n then
      prodTyped := prodTyped.insert n
      if (`L4YAML.Surface).isPrefixOf (modOf env n) then prodSurf := prodSurf.insert n
      if (getYamlSpecRefs env n).any (fun r => r.rule.isSome) then prodSpec := prodSpec.insert n
  let gotA := s!"prodTyped={prodTyped.size} prodSurf={prodSurf.size} prodSpec={prodSpec.size}"
  unless gotA == expectedAlphabet do
    throwError "the grammar alphabet moved:\n  got      {gotA}\n  expected {expectedAlphabet}"
  -- §2b the ladder, at each population
  let mut ladder : Array String := #[]
  let mut perFn : Array String := #[]
  let mut steps := ""
  let mut chainSurf : Array Name := #[]
  let mut chainSpec : Array Name := #[]
  for (tag, prods) in [("TYPED", prodTyped), ("SURF", prodSurf), ("SPEC", prodSpec)] do
    let mut stepHolders : Nat := 0
    let mut dispHolders : Nat := 0
    let mut dispTwoCorr : Nat := 0
    let mut edgeN : Nat := 0
    let mut chainN : Array Name := #[]
    let mut fnsAll : Std.HashSet Name := {}
    let mut fnsEdge : Std.HashSet Name := {}
    let mut fnsChain : Std.HashSet Name := {}
    let mut declByFn : Std.HashMap Name Nat := {}
    let mut chainByFn : Std.HashMap Name (Array Name) := {}
    for n in authored do
      let r ← readDecl prods n
      if r.fns.isEmpty then continue
      stepHolders := stepHolders + 1
      for f in r.fns do
        fnsAll := fnsAll.insert f
        declByFn := declByFn.insert f (declByFn.getD f 0 + 1)
      if r.fns.any (fun f => "scanNextToken_dispatch".isPrefixOf f.getString!) then
        dispHolders := dispHolders + 1
        if r.twoCorr then dispTwoCorr := dispTwoCorr + 1
      for f in r.edgeFns do fnsEdge := fnsEdge.insert f
      for f in r.chainFns do
        fnsChain := fnsChain.insert f
        chainByFn := chainByFn.insert f ((chainByFn.getD f #[]).push n)
      if !r.edgeFns.isEmpty then edgeN := edgeN + 1
      if !r.chainFns.isEmpty then chainN := chainN.push n
    let ixN := (fnsAll.toArray.filter (`L4YAML.Scanner.Indexed).isPrefixOf).size
    steps := s!"stepHolders={stepHolders} dispHolders={dispHolders} \
dispTwoCorr={dispTwoCorr} fns={fnsAll.size} fnsIx={ixN}"
    ladder := ladder.push s!"{tag} edge={edgeN} chain={chainN.size} \
fnEdge={fnsEdge.size} fnChain={fnsChain.size}"
    if tag == "SURF" then
      chainSurf := sorted chainN
      for f in sorted fnsChain.toArray do
        perFn := perFn.push s!"{f.getString!} decls={declByFn.getD f 0} \
chain={(chainByFn.getD f #[]).size}"
    if tag == "SPEC" then chainSpec := sorted chainN
  unless steps == expectedSteps do
    throwError "the step population moved:\n  got      {steps}\n  expected {expectedSteps}"
  unless ladder.toList == expectedLadder do
    throwError "the ladder moved:\n  got      {ladder.toList}\n  expected {expectedLadder}"
  unless chainSurf.toList == expectedChainSurf do
    throwError "the Surface chain-carriers moved: {chainSurf.toList}"
  unless chainSpec.toList == expectedChainSpec do
    throwError "the spec chain-carrier moved: {chainSpec.toList}"
  unless perFn.toList == expectedPerFn do
    throwError "the per-function reading moved:\n  got      {perFn.toList}\n  \
expected {expectedPerFn}"
  -- §4 where the one precedent sits
  let c ← census (some pre)
  let rev := revEdges authored usesVal
  let one := `L4YAML.Proofs.StreamAccum.indentedValue_reads_at_any_indent
  let gotO := s!"inT={c.trans.contains one} onThread={(thread rev supplier).contains one} \
onProdThread={(thread rev producer).contains one}"
  unless gotO == expectedOne do
    throwError "the precedent moved:\n  got      {gotO}\n  expected {expectedOne}"
  -- §5 what §1's derivation spends
  let usedBy (n : Name) : Array Name :=
    match env.find? n with
    | none => #[]
    | some ci => ((ci.value? (allowOpaque := true)).getD (mkConst n)).getUsedConstants
  let deps := usedBy ``connected_drop ++ usedBy ``connected_drop_nd
    ++ usedBy ``sslcomments_to_prefix ++ usedBy ``ssb_to_slcomment
  let gotW := s!"startOfLine={deps.contains ``SSeparateInLine.startOfLine} \
drop={deps.contains ``SLYamlStream.scannerDrop}"
  unless gotW == expectedWeak do
    throwError "the derivation's dependencies moved:\n  got      {gotW}\n  \
expected {expectedWeak}"
  logInfo m!"DispatchPrice {gotA} {steps} {ladder.toList} {gotO} {gotW}"

end Tests.Guards.DispatchPrice
