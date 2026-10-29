/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.RepairChoice

/-!
# Where the thread stops on the producer's side (DOCS item 241)

Item 240 measured the repair lattice and found the `field` repair breaking
exactly one definition: `block_dispatch_deferred`, the producer that builds
the park `PendingNode.pendingFlow`.  That producer is not like the park's
consumers.  It holds `ScannerSurfCorr s' sp_scan'`, a correspondence at the
park's own scan position, so it is the first place in the chain where the datum
the repair needs — `SLYamlStream sp_start sp_scan'` — might be DERIVED instead
of threaded.  (Item 240's mandate has that producer holding a dispatch equation
as well.  It does not: its five hypotheses are the stream to `sp_X`, the arm
disjunction, the correspondence, `h_nodir` and `h_nic0`.  The dispatch
equations belong to the four consumers in §3's first ring.)  **A flip that adds the premise there measures a propagation a
derivation would make zero**, so the derivation is asked about first and the
flip is read afterwards.

## The answer: the datum is a SEED fact, and the park is where the seed is spent

`ScannerSurfCorr` is a correspondence at a POINT — the remaining characters,
the column, the input end, a prefix witness, the signs of the indent stack.
The datum is a statement about a PATH.  §1 proves that the producer's own
premise set does not entail it, in the post-β.5 model item 239 built, and §2
measures what the library derives from a correspondence anywhere:

| reading | what it asks | count |
|---|---|---|
| `free` | a corr HYPOTHESIS, and the CONCLUSION a stream ending there | **0** |
| `pairConcl` | the CONCLUSION puts both at one position | **1** |
| `held` | two HYPOTHESES, a stream ending where a corr stands | **3** |
| `pairAny` | the two meet anywhere in the statement | **8** |

The one conclusion is `initial_stream_and_prefix`, and it is the SEED: input at
offset 0, the stream a `single` over `[202]`'s byte order mark.  The three
premise-holders are seed arms too — `accum_block_on_noPending`,
`accum_content_on_noPending` and `structural_dispatch_to_pending`, whose own
comments call a block-context `noPending` "the stream's seed".  **Nothing in
the library carries a stream to a scanner position except where nothing has
been scanned yet.**  The base case of the induction β.5 needs is the only case
the library has, and `pendingFlow` exists exactly where that case has been
left behind.

## What that makes of the lattice

`scripts/flip_supplier.py --end producer` threads the `field` repair one level:
the park keeps its new field, `close_with_ssl` still reads it, and the producer
gains the premise and spends it.  It reports `producer=4` — the producer's own
consumers, and item 240's `field=1` is the first wave of the same repair
rather than its price.  §3 walks the rest: the producer's thread is ~~18~~ 20
long (DOCS item 287: the two `:` consumers apply the inline wrapper themselves),
**none of the ~~18~~ 20 holds the datum**, and it ends at `L4YAML.Surface.parse_strict`
exactly as the supplier's does.

**So `field=1` is not a cheap repair, it is a short first wave.**  Item 240's
answer to item 239 — nineteen statements under `weak` and zero under the other
two — is exact for the question it was asked, which was how many change
*because `close_with_ssl`'s statement changes*; under `field` that lemma's
statement does not change, and the zero is literal.  It is not a claim that the
`field` repair changes no statements.  It changes `block_dispatch_deferred`'s,
and then its thread's, and §3 measures how far.

## The asymmetry the two threads do not share

The supplier's nineteen are all inside item 238's transitive set: `thread \ T`
is empty, so the weak repair redistributes β.5's bill without extending it.
The producer's are not.  §4 measures `prodThread \ T` and finds declarations
that never ride `SLYamlStream.scannerDrop` at all — they build the park or
stand above something that does, but the arm is not in their proof.  **The
`field` repair reaches declarations β.5's bill never named**, which is a cost
the lattice's first-wave counts cannot show.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.StreamAccum
open Tests.Guards.DropFalsity (StreamND nd_suffix nd_refl)
open Tests.Guards.DropDependents (usesAll census isAuthored inScope sorted)
open Tests.Guards.RepairChoice (revEdges thread rings producer supplier)

namespace Tests.Guards.ProducerDerivation

/-! ## §1 The producer cannot derive the datum from what it holds -/

/-- The scanner at the seed of an input, with the directive flag down — the
    one field `block_dispatch_deferred`'s `h_nodir` constrains. -/
def scSeed (input : String) : ScannerState :=
  { ScannerState.mk' input with allowDirectives := false }

/-- …and its correspondence, which is `initial_corr` re-fielded: the update
    touches no field `ScannerSurfCorr` reads. -/
lemma corrSeed (input : String) :
    ScannerSurfCorr (scSeed input) ⟨input.toList, 0⟩ :=
  let h := initial_corr input input.toList (chars_from_zero_toList input)
  ⟨h.chars_from, h.col_eq, h.end_eq, h.input_prefix, h.indent_cols_nonneg⟩

/-- **The producer's premise set does not entail the datum.**

    Every hypothesis `block_dispatch_deferred` holds is listed here — the
    stream to `sp_X`, the arm disjunction, the correspondence, the directive
    flag and the column-zero flag — and the conclusion is the connection the
    `field` repair asks that producer to supply.  The witness is a scanner
    sitting at the start of the input `"b"` while the stream reaches only the
    empty position, which every premise permits because **nothing in the list
    relates `sp_X` to `sp_scan'`**.

    Stated in `StreamND`, item 239's post-β.5 model: the real `SLYamlStream`
    admits `scannerDrop` and therefore proves nothing about positions, which
    is the defect β.5 removes.  A refutation in the model is a statement about
    the repaired library, which is the one being priced. -/
lemma producer_premises_give_no_stream :
    ¬ (∀ (s' : ScannerState) (sp_start sp_X sp_scan' : SurfPos),
        StreamND sp_start sp_X →
        ((s'.simpleKeyAllowed = true ∧ s'.simpleKey.possible = false)
          ∨ 0 < sp_scan'.col) →
        ScannerSurfCorr s' sp_scan' →
        s'.allowDirectives = false →
        (sp_scan'.col = 0 → s'.needIndentCheck = true) →
        StreamND sp_start sp_scan') := by
  intro h
  have hb := h (scSeed "b") ⟨[], 0⟩ ⟨[], 0⟩ ⟨"b".toList, 0⟩
    (nd_refl _) (Or.inl ⟨rfl, rfl⟩) (corrSeed "b") rfl (fun _ => rfl)
  have hlen := (nd_suffix hb).length_le
  simp at hlen

/-- **And where it IS derivable, it is derivable for free.**  At the seed the
    two positions coincide, so the datum is reflexivity.  This is the whole of
    what §2's census finds in the library: one conclusion and three premise
    sets, all of them at a scanner that has consumed nothing. -/
lemma seed_gives_the_datum (input : String) :
    ScannerSurfCorr (scSeed input) ⟨input.toList, 0⟩ ∧
      StreamND ⟨input.toList, 0⟩ ⟨input.toList, 0⟩ :=
  ⟨corrSeed input, nd_refl _⟩

/-! ## §2 What the library derives from a correspondence -/

/-- Every `SLYamlStream a b` and every `ScannerSurfCorr s p` inside `e`, as
    the two position arrays.  Memoized for the same reason item 240's park
    walk is: a proof-carrying type is a DAG and a walk that forgets is
    exponential on it. -/
partial def positionsAux (e : Expr) :
    StateM (Std.HashSet Expr × Array Expr × Array Expr) Unit := do
  if (← get).1.contains e then return
  modify fun (s, a, b) => (s.insert e, a, b)
  if e.isAppOfArity ``SLYamlStream 2 then
    modify fun (s, a, b) => (s, a.push e.appArg!, b)
  if e.isAppOfArity ``ScannerSurfCorr 2 then
    modify fun (s, a, b) => (s, a, b.push e.appArg!)
  let _ ← e.foldlM (fun (_ : Unit) s => positionsAux s) ()

/-- `(stream ends, corr positions)`. -/
def positions (e : Expr) : Array Expr × Array Expr :=
  let (_, a, b) := ((positionsAux e).run ({}, #[], #[])).2
  (a, b)

/-- The four readings of one declaration.

    They are kept apart because they answer four different questions, and
    merging them would report a rate over the wrong population.  `free` is the
    DERIVATION shape — a correspondence in, a stream at that position out —
    and it is the only one whose emptiness prices anything.  `held` is the
    shape that lets a consumer pay a threaded premise out of what it already
    has.  `pairAny` is the upper bracket: the two named at one position
    anywhere in the statement, nested implications included, where they may
    never be available at the same time.

    **`pairConcl` and `pairAny` compare positions that may be bound**, so two
    variables at the same de Bruijn index under different binders read as one
    and the two counts can over-report.  That is why they are brackets and why
    `free` and `held` — which compare only the telescope's own free variables,
    each globally distinct — carry the findings. -/
structure Readings where
  free : Bool
  pairConcl : Bool
  held : Bool
  pairAny : Bool
  corrHyp : Bool
  streamConcl : Bool
deriving Inhabited

def readDecl (n : Name) : MetaM Readings := do
  let some ci := (← getEnv).find? n | return ⟨false, false, false, false, false, false⟩
  forallTelescope ci.type fun xs concl => do
    let (so, co) := positions concl
    let mut corrHyps : Array Expr := #[]
    let mut streamHyps : Array Expr := #[]
    let mut sAll := so
    let mut cAll := co
    for x in xs do
      let t ← inferType x
      if t.isAppOfArity ``ScannerSurfCorr 2 then corrHyps := corrHyps.push t.appArg!
      if t.isAppOfArity ``SLYamlStream 2 then streamHyps := streamHyps.push t.appArg!
      let (s1, c1) := positions t
      sAll := sAll ++ s1
      cAll := cAll ++ c1
    let meet (a b : Array Expr) : Bool := a.any fun p => b.any fun q => p == q
    return ⟨meet corrHyps so, meet co so, meet corrHyps streamHyps, meet cAll sAll,
            !corrHyps.isEmpty, !so.isEmpty⟩

/-! ## §3 The pins -/

/-- **Nothing derives a stream from a correspondence.**  435 statements hold a
    correspondence and 89 conclude a stream; 39 do both, and none of the 39
    concludes a stream ending where its own correspondence stands.

    The first count moved by one at item 271 and by one again at item 272.
    `underRunEnd_col_le_currentIndent` takes the landing's
    `ScannerSurfCorr s_prep sp_prep` to carry the surface column onto the
    scanner state and concludes an inequality; `underRunEnd_landing_on_stack`
    hands that same correspondence on and concludes a membership on the
    landing's indent stack.  Neither concludes a stream, so both join the count
    and none of the other six readings moves.

    Item 293 moves it by one more, for the same kind of reason:
    `live_of_dispatch` takes the content park's correspondence to read a block
    scalar's line stop, and concludes a possibility — the one new declaration
    holding a correspondence.

    The `[162]` header split (2026-10-23) moves it by two: `parseBlockHeaderLoop_prod_indent`
    and `_prod_chomp` each take a correspondence and conclude one, like `_prod` already did.

    444 → 460 on 2026-10-23: `Proofs.Production.Acceptance.Quoted`, whose sixteen
    acceptance lemmas take a correspondence and conclude a scanner landing.

    460 → 481 on 2026-10-23: the same module's multi-line layer — fold, blank-line,
    landing and break-step lemmas, each taking a correspondence. 
    481 → 489 on 2026-10-23: `Acceptance/Plain.lean`, the one-line plain-scalar converse
    (eight `ScannerSurfCorr`-hypothesis lemmas, Stream E).

    489 → 496 on 2026-10-23: `Acceptance/Plain.lean` multi-line layer — blank-line loop,
    block fold, fold step, continuation loop, `scanPlainScalar_accepts_multi` and two
    document-marker bridges, each taking a correspondence (Stream E).

    496 → 505 on 2026-10-23: `Acceptance/Plain.lean` break-terminated stop and flow fold —
    `peekAt_of_corr`, the two fold refusals, the marker bridge, `break_peek_term`, the block and
    flow break stops, `collectPlainScalarLoop_flowFold_step`, `terminates_at_marker` (Stream E).

    505 → 512 on 2026-10-23: `Acceptance/Properties.lean` — the anchor/alias name loop and
    `scanAnchorOrAlias_accepts`, the tag loops, `scanTag_accepts` and the two tag-handle
    bridges, each taking a correspondence (Stream E).

    512 → 519 on 2026-10-23: `Acceptance/FlowIndicators.lean` — the four bracket converses,
    `scanFlowEntry_accepts` and the two shared landing bridges, each taking a correspondence
    (Stream E).

    519 → 523 on 2026-10-23: `Acceptance/BlockIndicators.lean`, the `-`/`?`/`:` converses
    and `emit_corr` (Stream E).

    527 → 545 on 2026-10-23: `Acceptance/BlockScalar.lean` — the indent/line/comment loop
    converses, the header indicator and tail readers, `blockScalarTabStop_false_of_stop`,
    the auto-detect loop and `scanBlockScalar_accepts`, each taking a correspondence
    (Stream E). -/
-- 2026-10-26 (item 367, `[82]`): `directiveStop_of_validated` (StructureProduction) reads two `ScannerSurfCorr` hypotheses: `corrHyp` 583 → 584; the stream-conclusion counts are unchanged.
def expectedCensus : String :=
-- 2026-10-23 ([147] glued value): corrHyp 545 → 546 — `flowGluedCollectionValue_false_of_corr_colon_blank` reads
-- the `": "` surface through a `ScannerSurfCorr` hypothesis; the thread, held and pair rows are unchanged.
-- 2026-10-24 (B3 [66] col-0 threading): corrHyp 546 → 583, streamConcl 90 → 91, both 40 → 41 — the
-- gate/JSON-key/reservation lemmas read the surface through `ScannerSurfCorr`; `close_with_sslFrom` concludes a stream.
  -- Item 371: streamConcl 91 → 88 — three value-line conclusions now end in the
  -- one-level `ResumeFrames`, not head-`SLYamlStream` (the restated pack).
    -- 2026-10-29 (item 389): corrHyp 584 → 587 — `pushedBirth_not_mapTop`, `noPushBirth_indents`,
  -- `contentLanding_indents_eq` read the cursor through a `ScannerSurfCorr` hypothesis.
  "corrHyp=587 streamConcl=88 both=41 free=0 pairConcl=1 held=3 pairAny=8"

/-- The one conclusion that pairs them, and it is the stream's origin. -/
def expectedSeedConcl : List Name :=
  [`L4YAML.Proofs.StreamAccum.initial_stream_and_prefix]

/-- The three statements that hold the datum as premises — every one an arm
    where nothing is parked, which is the same finding as the seed. -/
def expectedHeld : List Name :=
  [`L4YAML.Proofs.StreamAccum.accum_block_on_noPending,
   `L4YAML.Proofs.StreamAccum.accum_content_on_noPending,
   `L4YAML.Proofs.StreamAccum.structural_dispatch_to_pending]

/-- **And none of the three is on either thread.**  The places that hold the
    datum and the places that need it are disjoint. -/
def expectedHeldOnThreads : String := "onProdThread=0 onThread=0"

/-- The producer's thread, and the discriminator over it: ~~thirteen of the
    eighteen~~ fifteen of the twenty carry a correspondence, and not one of
    them carries a stream to the position it names.  (DOCS item 287 added the
    two `:` consumers, which apply the inline wrapper and carry three
    correspondences each.) -/
def expectedProdThread : String :=
  "prodThread=21 rings=8 withCorr=16 covered=0"

/-- The first ring — the four definitions `--end producer` breaks, which is
    the same four this walk reads.

    The escape's own docstring records ELEVEN application sites, and those are
    reached THROUGH the three wrappers items 184–185 interposed to partition
    them: `block_dispatch_deferred` itself is applied four times and the
    wrappers eight times between them.  So the four here is exact for the first
    wave and the eleven is the shape of the second, which is ring 2. -/
def expectedProdRing1 : List Name :=
  [`L4YAML.Proofs.StreamAccum.accum_content_pending,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol]

/-- **The producer's thread leaves β.5's bill and the supplier's does not.**
    Item 240 measured `thread \ T = []`; this is the other side. -/
-- 2026-10-24 (B3 [66] col-0 threading): union 29 → 24 — the supplier's thread lost `eof_pending` and
-- `accum_structural_pending` (they close through `PendingNode.close_with_sslFrom` now, see RepairChoice); the
-- producer's own rows are unchanged.
def expectedProdInT : String := "prodInT=12 prodOutsideT=9 union=24 unionOutsideT=9"

/-- **The ~~seven~~ nine, named.**  Three wrappers that partition the escape's
    own applications, four `accum_block_on_*` arms, and (DOCS item 287) the two
    `:` consumers, which apply the inline wrapper themselves.  Each of them
    builds the park or stands above something that does, and none of them
    depends — however far down — on a declaration that spends
    `SLYamlStream.scannerDrop`, which is why item 238's walk never counted them
    and why the weak repair never reaches them.  A repair that threads through
    the producer does. -/
def expectedProdOutsideT : List Name :=
  [`L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock,
   `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock,
   `L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent,
   `L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol,
   `L4YAML.Proofs.StreamAccum.colon_fires_implicit_key,
   `L4YAML.Proofs.StreamAccum.colon_fires_props_key]

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pre := usesAll env
  let (authored, usesVal) := pre
  -- §2, over the whole authored population
  let mut corrHyp := 0
  let mut streamConcl := 0
  let mut both := 0
  let mut freeOnes : Array Name := #[]
  let mut seedConcl : Array Name := #[]
  let mut held : Array Name := #[]
  let mut pairAny := 0
  for n in authored do
    let r ← readDecl n
    if r.corrHyp then corrHyp := corrHyp + 1
    if r.streamConcl then streamConcl := streamConcl + 1
    if r.corrHyp && r.streamConcl then both := both + 1
    if r.free then freeOnes := freeOnes.push n
    if r.pairConcl then seedConcl := seedConcl.push n
    if r.held then held := held.push n
    if r.pairAny then pairAny := pairAny + 1
  let gotC := s!"corrHyp={corrHyp} streamConcl={streamConcl} both={both} \
free={freeOnes.size} pairConcl={seedConcl.size} held={held.size} pairAny={pairAny}"
  unless gotC == expectedCensus do
    throwError "the census moved:\n  got      {gotC}\n  expected {expectedCensus}\n\
  free     {sorted freeOnes}\n  pairConcl {sorted seedConcl}\n  held     {sorted held}"
  unless (sorted seedConcl).toList == expectedSeedConcl do
    throwError "the seed conclusion moved: {(sorted seedConcl).toList}"
  unless (sorted held).toList == expectedHeld do
    throwError "the premise-holders moved: {(sorted held).toList}"
  -- §3, the two threads
  let rev := revEdges authored usesVal
  let pth := thread rev producer
  let th := thread rev supplier
  let prs := rings rev producer
  let gotH := s!"onProdThread={(held.filter pth.contains).size} \
onThread={(held.filter th.contains).size}"
  unless gotH == expectedHeldOnThreads do
    throwError "a holder joined a thread:\n  got      {gotH}\n  \
expected {expectedHeldOnThreads}"
  let mut withCorr := 0
  let mut covered := 0
  for n in pth do
    let r ← readDecl n
    if r.corrHyp then withCorr := withCorr + 1
    if r.held then covered := covered + 1
  let gotP := s!"prodThread={pth.size} rings={prs.size} withCorr={withCorr} \
covered={covered}"
  unless gotP == expectedProdThread do
    throwError "the producer's thread moved:\n  got      {gotP}\n  \
expected {expectedProdThread}"
  unless prs.size > 0 && prs[0]!.toList == expectedProdRing1 do
    throwError "the producer's first ring moved: {(prs[0]?.getD #[]).toList}"
  -- §4, against item 238's transitive set
  let c ← census (some pre)
  let union := th ++ pth.filter (fun n => !th.contains n)
  let gotT := s!"prodInT={(pth.filter c.trans.contains).size} \
prodOutsideT={(pth.filter (fun n => !c.trans.contains n)).size} \
union={union.size} \
unionOutsideT={(union.filter (fun n => !c.trans.contains n)).size}"
  let outside := sorted (pth.filter (fun n => !c.trans.contains n))
  unless gotT == expectedProdInT do
    throwError "the producer's thread moved against T:\n  got      {gotT}\n  \
expected {expectedProdInT}\n  outside  {outside}"
  unless outside.toList == expectedProdOutsideT do
    throwError "the seven outside item 238's set moved: {outside.toList}"
  logInfo m!"ProducerDerivation {gotC} {gotH} {gotP} {gotT}"

end Tests.Guards.ProducerDerivation
