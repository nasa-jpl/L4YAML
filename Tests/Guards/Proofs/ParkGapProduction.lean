/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ParkGapWidth

/-!
# The park's literal has no carrier — what a `GLit` costs where the six stand

Item 244 measured the width of `PendingNode.pendingFlow`'s gap and found it
**one scanner step at six of the producer's twelve application sites**, two at a
seventh, and proved the step is exactly one `ScannerState.advance` — so the
production the six owe is a single `GLit` for `-`, `?` or `:`.  It left the
number nothing held: **what that literal costs where the six stand.**

This module answers it with four readings and three proofs.

**§1 asks what the six sites' grammar path ENDS in**, which is the question item
244's census never posed: it measured that a path exists and how many steps sit
beyond it, not what the last production on it is.  At all six the answer is the
same and it is one edge long: `GStar SSWhite` — `[33] s-white` repeated — and
`SIndent`, both running from the park's own position `sp_X` to the position the
dispatch's input correspondence stands at.  Whitespace.  Nothing on the path
opens a collection, and nothing on it is a literal.

**§2 reads what the stream can be extended BY.**  `SLYamlStream`'s three honest
constructors each reach their right endpoint through `GStar SLDocumentSuffix`,
so the alphabet that can move a stream's end is three productions wide —
`SLDocumentPrefix`, `SLAnyDocument`, `SLDocumentSuffix`.  Only one of the three
can contain a `GLit` at all, and it is **four productions above it**:
`SLAnyDocument > SLBareDocument > SBlockNode > SBlockSeqEntries > GLit`.  The
other two encode their own literals as constructor patterns
(`SCDocumentEnd.mk` matches `'.' :: '.' :: '.' :: rest` directly), so "cannot
reach `GLit`" is a statement about the combinator, not about the characters.

**§3 is the price.**  A production can end at a literal — thirty of the
library's two hundred and thirty-five constructors do.  Twenty-three of those
thirty end at one of the three block indicators, and every one of the
twenty-three is a FLOW form: `MapFrame`, `SeqFrame`, `PendingFlowMapEntry`,
`PendingFlowSeqEntry`, `SFlowMapEntry`, `SFlowSeqEntry`.  **`-` ends nothing at
all**, and none of the three productions on the six sites' own chain —
`SBlockSeqEntries`, `SBlockMapEntry`, `SBlockIndented` — is among the thirty.

**§4 closes the loop the mandate warned about.**  The twenty-three that exist
ride the flow stack, and `block_dispatch_deferred` hands its park
`FlowStackB sp_start 0 0 none 0 #[] #[] .sep sp_X sp_X` beside
`BlockStack.nil sp_X`.  Both carriers are reflexive — `BlockStack` has one
constructor and it concludes `BlockStack sp sp`, and a depth-zero `FlowStackB`
is `nil` by the library's own `pos_eq_of_depth_zero` — so neither can hold a
character.  `park_carriers_absorb_nothing` is that, proved.

The ratio names the missing piece exactly: `SeqFrame` and `MapFrame` carry TEN
constructors each; `BlockStack` carries ONE, and it is the same arm
`SeqFrame.betweenEmpty` is — the only one of the ten that is reflexive by
construction.  The block side has the empty frame and none of the nine that
follow it.

**The cheap experiment the mandate named SUCCEEDS, and its statement is the
bill.**  `seq_entry_of_park_span` spends item 244's literal at the shape the six
stand in: the path's `SIndent` and the dispatch's `GLit '-'` are premises one
and two of `SBlockSeqEntries.single`.  What it buys is
`SBlockSeqEntries n sp_mid sp_end` — and `sp_end` is where the entry's CONTENT
ends, not where the character does.  The two unpaid premises are named in the
lemma's own binders: `GNot SNsChar` and `SBlockIndented n .blockIn`.

So the literal costs a carrier, and the park has set both of its carriers to
empty.  The measurement is `ParkGapProduction` below; every number it prints is
re-derived from the environment at elaboration time.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge
open Tests.Guards.DropDependents (usesAll modOf sorted)
open Tests.Guards.DispatchPrice (isProd)
open Tests.Guards.ParkGapWidth (heads stepEqFn? fvarsOf dispatchBI_span_glit)

set_option autoImplicit false

namespace Tests.Guards.ParkGapProduction

/-! ## §1 The park's two carriers absorb nothing -/

/-- `BlockStack` has a single constructor and it is reflexive, so the relation
    cannot separate its two positions.  The library cannot STATE an open block
    collection; `BlockStack` is a placeholder for one. -/
lemma blockStack_refl {a b : SurfPos} (h : BlockStack a b) : a = b := by
  cases h; rfl

/-- **Neither carrier the park hands its consumer can hold a character.**  The
    two hypotheses are `block_dispatch_deferred`'s own second and third
    conjuncts; the conclusion says the grammar position it parks at and the
    position its flow stack reaches are the same point.  A `GLit` spent here has
    nowhere to land: the flow forms that END at a block indicator (§3) all need
    a frame, and this stack is at depth zero. -/
lemma park_carriers_absorb_nothing {s0 : ScannerState} {sp_start sp_gram sp_block sp_flow : SurfPos}
    {tl : FrameTail}
    (hb : BlockStack sp_gram sp_block)
    (hf : FlowStackB sp_start 0 0 none s0 0 #[] #[] tl sp_block sp_flow) :
    sp_gram = sp_flow := by
  rw [blockStack_refl hb, FlowStackB.pos_eq_of_depth_zero hf]

/-- **The cheap experiment, spent.**  The census's path (`SIndent`) and item
    244's span (`GLit '-'`) are premises one and two of
    `SBlockSeqEntries.single`.  The literal composes — and what it composes INTO
    ends at `sp_end`, the end of the entry's content, not at `sp_scan'`, where
    the scanner's cursor stands.  `h_nns` and `h_content` are the price, and
    `h_content` is a whole block node the park has not scanned. -/
lemma seq_entry_of_park_span {n : Nat} {s s' : ScannerState} {rest : List Char}
    {sp_mid sp_sc sp_scan' sp_end : SurfPos}
    (h_path : SIndent n sp_mid sp_sc)
    (h_step : scanNextToken_dispatchBlockIndicators s '-' = Except.ok (some s'))
    (h_in : ScannerSurfCorr s sp_sc) (h_out : ScannerSurfCorr s' sp_scan')
    (h_chars : sp_sc.chars = '-' :: rest)
    (h_nns : GNot SNsChar sp_scan')
    (h_content : SBlockIndented n .blockIn sp_scan' sp_end) :
    SBlockSeqEntries n sp_mid sp_end :=
  .single n sp_mid sp_sc sp_scan' sp_scan' sp_end h_path
    (dispatchBI_span_glit h_step h_in h_out h_chars (by decide) (by decide))
    h_nns h_content

/-! ## §2 The censuses -/

/-- A combinator edge says nothing on its own: `GStar` is a repetition of
    SOMETHING, and which production it repeats is the reading.  Render the inner
    relation's head beside the combinator so the path is interrogable. -/
def edgeLabel (n : Name) (args : Array Expr) : String :=
  if n == ``GStar || n == ``GPlus || n == ``GOpt then
    match args[0]? with
    | some e =>
      match e.getAppFn with
      | Expr.const inner _ => s!"{n.getString!}({inner.getString!})"
      | _ => n.getString!
    | none => n.getString!
  else n.getString!

/-- Item 244's `posEdges` with the production's NAME kept: only strictly
    positive occurrences, so a site cannot cross its own gap with an edge it
    would first have to discharge. -/
partial def namedPosEdges (prods : Std.HashSet Name) (t : Expr) :
    MetaM (Array (String × Expr × Expr)) := do
  match t with
  | .forallE nm a b bi =>
    withLocalDecl nm bi a fun x => namedPosEdges prods (b.instantiate1 x)
  | .mdata _ b => namedPosEdges prods b
  | _ =>
    if t.isAppOfArity ``And 2 then
      return (← namedPosEdges prods t.appFn!.appArg!) ++ (← namedPosEdges prods t.appArg!)
    if t.isAppOfArity ``Exists 2 then
      match t.appArg! with
      | .lam nm a b bi =>
        return ← withLocalDecl nm bi a fun x => namedPosEdges prods (b.instantiate1 x)
      | _ => return #[]
    if let .const n _ := t.getAppFn then
      if prods.contains n then
        let args := t.getAppArgs
        if args.size ≥ 2 then
          return #[(edgeLabel n args, args[args.size-2]!, args[args.size-1]!)]
    return #[]

abbrev W := StateRefT (Array String × Std.HashSet Expr) MetaM

/-- One application site: the productions that land on the position the spent
    step's INPUT correspondence stands at, and how far that position is from the
    park's own. -/
def record (prods : Std.HashSet Name) (decl fn : Name) (a b : Expr) : W Unit := do
  let lctx ← getLCtx
  let mut corrs : Array (Expr × Expr) := #[]
  let mut steps : Array (Name × Array Expr × Array Expr) := #[]
  let mut pe : Array (String × Expr × Expr) := #[]
  for ld in lctx do
    if ld.isImplementationDetail then continue
    let t := ld.type
    unless (← inferType t).isProp do continue
    if t.isAppOfArity ``ScannerSurfCorr 2 then
      corrs := corrs.push (t.appFn!.appArg!, t.appArg!)
    if let some f := stepEqFn? t then
      let inS ← (fvarsOf t.appFn!.appArg!).filterM fun v =>
        return (← inferType v).isConstOf ``ScannerState
      let outS ← (fvarsOf t.appArg!).filterM fun v =>
        return (← inferType v).isConstOf ``ScannerState
      steps := steps.push (f, inS, outS)
    pe := pe ++ (← namedPosEdges prods t)
  let posAt (x : Expr) : Array Expr := (corrs.filter (fun q => q.1 == x)).map (·.2)
  let dists : Std.HashMap Expr Nat := Id.run do
    let mut d : Std.HashMap Expr Nat := ({} : Std.HashMap Expr Nat).insert a 0
    let mut front : Array Expr := #[a]
    let mut k : Nat := 0
    while !front.isEmpty && k < 8 do
      k := k + 1
      let mut nxt : Array Expr := #[]
      for x in front do
        for (_, l, r) in pe do
          if l == x && !d.contains r then d := d.insert r k; nxt := nxt.push r
      front := nxt
    return d
  let mut rows : Array String := #[]
  for (f, inS, outS) in steps do
    unless outS.any (fun o => (posAt o).any (fun q => q == b)) do continue
    for i in inS do
      for p in posAt i do
        let some dp := dists.get? p | continue
        if dp == 0 then continue
        let landing := pe.filter fun e => e.2.2 == p && dists.get? e.2.1 == some (dp - 1)
        let mut u : Array String := #[]
        for n in (landing.map (·.1)).qsort (· < ·) do
          unless u.contains n do u := u.push n
        let row := s!"{decl} <- {fn} step={f.getString!} len={dp} \
ends={String.intercalate "+" u.toList}"
        unless rows.contains row do rows := rows.push row
  if rows.isEmpty then
    modify fun (o, v) => (o.push s!"{decl} <- {fn} NOSPEND", v)
  else
    for r in rows do modify fun (o, v) => (o.push r, v)

/-- Item 243's walk under binders, with this item's recorder. -/
partial def walk (prods : Std.HashSet Name) (decl : Name) (e : Expr) : W Unit := do
  if (← get).2.contains e then return
  modify fun (o, v) => (o, v.insert e)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n _ := f then
      if heads.contains n && args.size > 3 then record prods decl n args[1]! args[2]!
    walk prods decl f
    for x in args do walk prods decl x
  | .lam nm t b bi =>
    walk prods decl t
    withLocalDecl nm bi t fun x => walk prods decl (b.instantiate1 x)
  | .letE nm t val b _ =>
    walk prods decl t
    walk prods decl val
    withLetDecl nm t val fun x => walk prods decl (b.instantiate1 x)
  | .forallE nm t b bi =>
    walk prods decl t
    withLocalDecl nm bi t fun x => walk prods decl (b.instantiate1 x)
  | .mdata _ b => walk prods decl b
  | .proj _ _ b => walk prods decl b
  | _ => pure ()

/-! ## §3 The pins -/

/-- **The path, at every site.**  Six spend a step, and every one of the six
    crosses ONE production edge to get to the dispatch's input — whitespace,
    from the park's own position.  The other ~~six~~ seven spend nothing: the
    ~~width-2 site needs~~ two width-2 sites need two steps and the five item
    244 read as unreached have no chain.  (DOCS item 287 traded the two
    `accum_block_on_*` inline sites for `accum_block_pending`'s and the two `:`
    consumers'; `ParkGapWidth` reads the same trade.) -/
def expectedPaths : List String :=
  ["L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack \
step=scanNextToken_dispatchBlockIndicators len=1 ends=GStar(SSWhite)+SIndent",
   "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol \
step=scanNextToken_dispatchBlockIndicators len=1 ends=GStar(SSWhite)+SIndent",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack \
step=scanNextToken_dispatchBlockIndicators len=1 ends=GStar(SSWhite)+SIndent",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol \
step=scanNextToken_dispatchBlockIndicators len=1 ends=GStar(SSWhite)+SIndent",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack \
step=scanNextToken_dispatchBlockIndicators len=1 ends=GStar(SSWhite)+SIndent",
   "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol \
step=scanNextToken_dispatchBlockIndicators len=1 ends=GStar(SSWhite)+SIndent",
   "L4YAML.Proofs.StreamAccum.accum_block_pending <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline NOSPEND",
   "L4YAML.Proofs.StreamAccum.accum_content_pending <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred NOSPEND",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred NOSPEND",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_nopack <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred NOSPEND",
   "L4YAML.Proofs.StreamAccum.block_dispatch_deferred_stamp_offcol <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred NOSPEND",
   "L4YAML.Proofs.StreamAccum.colon_fires_implicit_key <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline NOSPEND",
   "L4YAML.Proofs.StreamAccum.colon_fires_props_key <- \
L4YAML.Proofs.StreamAccum.block_dispatch_deferred_inline NOSPEND"]

/-- **How far a `GLit` is below the stream's own alphabet.**  A stream's right
    endpoint moves by `SLDocumentPrefix`, `SLAnyDocument` or `SLDocumentSuffix`;
    only the middle one can contain the combinator, and it is three productions
    up (item 367; four before `SLDirective.yaml`'s `GLit '.'`).  The two `UNREACHABLE` readings are about `GLit` and not about
    characters: `SCDocumentEnd.mk` matches `'.' :: '.' :: '.' :: rest` in its
    own constructor pattern. -/
-- 2026-10-26 (item 367, `[82]`): `SLDirective.yaml` matches `[86] ns-yaml-version`'s `.` with
-- `GLit '.'`, so the nearest `GLit` below the stream is now three productions up, through the
-- directive document; the block-sequence chain (depth 4) still stands behind it.
def expectedAlphabet : List String :=
  ["L4YAML.Surface.SLAnyDocument -> GLit depth=3 \
chain=SLAnyDocument > SLDirectiveDocument > SLDirective > GLit",
   "L4YAML.Surface.SLDocumentPrefix -> GLit UNREACHABLE",
   "L4YAML.Surface.SLDocumentSuffix -> GLit UNREACHABLE"]

/-- **Every constructor in the library that ENDS at a literal**, with the
    character it ends at.  Twenty-three of the thirty end at one of the three
    block indicators the park's dispatch scans, and all twenty-three are flow
    forms.  `'-'` — the block sequence's own indicator, and the one the cheap
    experiment spends — ends nothing. -/
-- 2026-10-23: `Proofs.Production.Acceptance.Quoted` adds the two quote-delimited
-- `SC*QuotedOk.mk` relations (narrowed `[109]`/`[120]`).
def expectedEndsLit : List String :=
  ["L4YAML.Proofs.Acceptance.SCDoubleQuotedMultiOk.mk '\\\"'",
   "L4YAML.Proofs.Acceptance.SCDoubleQuotedOk.mk '\\\"'",
   "L4YAML.Proofs.Acceptance.SCSingleQuotedMultiOk.mk '\\''",
   "L4YAML.Proofs.Acceptance.SCSingleQuotedOk.mk '\\''",
   "L4YAML.Proofs.Acceptance.TagOk.verbatim '>'",
   "L4YAML.Proofs.NodeProduction.PendingFlowMapEntry.colonPending ':'",
   "L4YAML.Proofs.NodeProduction.PendingFlowMapEntry.emptyColonPending ':'",
   "L4YAML.Proofs.NodeProduction.PendingFlowMapEntry.explicitColonPending ':'",
   "L4YAML.Proofs.NodeProduction.PendingFlowSeqEntry.colonPending ':'",
   "L4YAML.Proofs.NodeProduction.PendingFlowSeqEntry.explicitColonPending ':'",
   "L4YAML.Proofs.StreamAccum.MapFrame.midColon ':'",
   "L4YAML.Proofs.StreamAccum.MapFrame.midEmptyColon ':'",
   "L4YAML.Proofs.StreamAccum.MapFrame.midExplicitColon ':'",
   "L4YAML.Proofs.StreamAccum.MapFrame.midQuestion '?'",
   "L4YAML.Proofs.StreamAccum.MapFrame.midQuestionEmptyColon ':'",
   "L4YAML.Proofs.StreamAccum.SeqFrame.midColon ':'",
   "L4YAML.Proofs.StreamAccum.SeqFrame.midEmptyColon ':'",
   "L4YAML.Proofs.StreamAccum.SeqFrame.midExplicitColon ':'",
   "L4YAML.Proofs.StreamAccum.SeqFrame.midQuestion '?'",
   "L4YAML.Proofs.StreamAccum.SeqFrame.midQuestionEmptyColon ':'",
   "L4YAML.Surface.SCChompingIndicator.keep '+'",
   "L4YAML.Surface.SCChompingIndicator.strip '-'",
   "L4YAML.Surface.SCDoubleQuoted.mk '\\\"'",
   "L4YAML.Surface.SCIndentationIndicator.digit fun c => '1' ≤ c ∧ c ≤ '9'",
   "L4YAML.Surface.SCNsTagProperty.verbatim '>'",
   "L4YAML.Surface.SCSingleQuoted.mk '\\''",
   "L4YAML.Surface.SFlowMapEntry.emptyKeyEmpty ':'",
   "L4YAML.Surface.SFlowMapEntry.explicitEmpty ':'",
   "L4YAML.Surface.SFlowMapEntry.explicitEmptyKeyEmpty ':'",
   "L4YAML.Surface.SFlowMapEntry.implicitEmpty ':'",
   "L4YAML.Surface.SFlowMapping.empty '}'",
   "L4YAML.Surface.SFlowMapping.nonempty '}'",
   "L4YAML.Surface.SFlowSeqEntry.emptyKeyEmpty ':'",
   "L4YAML.Surface.SFlowSeqEntry.explicitEmptyKeyEmpty ':'",
   "L4YAML.Surface.SFlowSeqEntry.explicitPairEmpty ':'",
   "L4YAML.Surface.SFlowSeqEntry.pairEmpty ':'",
   "L4YAML.Surface.SFlowSequence.empty ']'",
   "L4YAML.Surface.SFlowSequence.nonempty ']'",
   "L4YAML.Surface.SNbNsPlainInLineEntry.hash '#'"]

/-- **The answer, in one line.**  `spend=6 len1=6` is §1; `depth=4` is §2;
    `endsLit=33 minus=1 question=2 colon=21 chainEnds=0` is §3; and
    `blockArms=1` against `seqArms=10` is §4's asymmetry as a ratio —
    `BlockStack` is `SeqFrame` with only its `betweenEmpty` arm.  The denominator
    for `endsLit` is `ctors`, and the denominator for `ctors` is `prods` — a
    production census, not a file census, so it moves only when the grammar
    does.  `prods` is every authored constant in this module's import closure
    whose type ends in `Prop` with two trailing `SurfPos` arguments; the
    combinators are IN it by that definition, checked by deleting an explicit
    insert of `GStar`, `GOpt`, `GPlus`, `GLit`, `GChar` and `SIndent` and
    watching `prods=130` not move.  DOCS item 287: `pop` 7 → 10, `sites`
    12 → 13 and `nospend` 6 → 7, `ParkGapWidth`'s trade read here — the six
    sites that spend a step are untouched. -/
-- 2026-10-23 ([162]): `prods` +2, `ctors` +5, `endsLit` +3 — `SCChompingIndicator.strip`/`.keep` and
-- `SCIndentationIndicator.digit` end in their one literal; `minus` 0 → 1 is the chomping `-`, a header
-- indicator that no park reads, not a sequence entry.
-- `prods` 133 → 137, `ctors` 240 → 249, `endsLit` 33 → 35 on 2026-10-23:
-- `Proofs.Production.Acceptance.Quoted`'s four narrowed quoted-scalar relations.
-- `prods` 137 → 145, `ctors` 249 → 263, `endsLit` 35 → 37 on 2026-10-23: the same module's eight
-- multi-line relations; `SC*QuotedMultiOk.mk` end in their closing quote like the one-line forms.
-- `prods` 145 → 149, `ctors` 263 → 271 on 2026-10-23: the four one-line plain relations of
-- `Acceptance/Plain.lean` (`PlainCharOk`, `PlainEntryOk`, `PlainFirstOk`, `PlainOneLineOk`; Stream E).
-- `prods` 150 → 151, `ctors` 271 → 272 on 2026-10-23: `PlainNextLineOk`, the multi-line plain
-- relation of `Acceptance/Plain.lean` (Stream E).
-- `prods` 151 → 152, `ctors` 272 → 276, `endsLit` 37 → 38 on 2026-10-23: `TagOk` of
-- `Acceptance/Properties.lean` (Stream E); `TagOk.verbatim` ends in `>` like `[97]`'s verbatim arm.
-- `endsLit` 38 → 39 on 2026-10-23: `[132]`'s `SNbNsPlainInLineEntry.hash` ends in its `#` — the
-- one legal `#` position in a plain scalar, replacing `[130]`'s `hashAfterNs` (`ctors` unchanged).
-- `prods` 152 → 159, `ctors` 276 → 293 on 2026-10-23: the seven block-scalar relations of
-- `Acceptance/BlockScalar.lean` (Stream E); none ends at a literal the park reads.
-- `prods` 160 → 162, `ctors` 296 → 304 on 2026-10-24: `SCFlowJsonContent`/`SCFlowJsonNode` ([148]/[149]
-- JSON-key adjacent value) and their 8 arms; no park reading moved.
-- 2026-10-24 (B3): prods 162 → 164, ctors 304 → 306 — the explicit JSON-key adjacent-value twins in Surface/Node.lean.
-- 2026-10-25 (#99 review): prods 164 → 163 — the dead `FlowLead` duplicate of `leadFree` is deleted.
-- 2026-10-25 (slice 2, `TraceOf/UniqueFlow.lean`): prods 163 → 165, ctors 306 → 308 — the proof-layer relations
-- `PStep` (2 arms) and `Follow` (a def); neither ends at a literal the park reads.
-- 2026-10-26 (item 367, `[82]`): `SLDirective` 1 → 3 arms and the four scanner-cut relations in StructureProduction (`DigitRun`, `DirectiveStop`, `DirectiveTail`, `ScannedDirective`): prods 165 → 169, ctors 308 → 313; the `GLit` depth below the stream 4 → 3 (`SLDirective.yaml`'s `GLit '.'`).
def expectedLine : String :=
  "pop=10 sites=13 spend=6 nospend=7 len1=6 ends=GStar(SSWhite)+SIndent \
depth=3 prods=169 ctors=313 \
endsLit=39 minus=1 question=2 colon=21 chainEnds=0 blockArms=1 seqArms=10 \
mapArms=10 streamArms=4 streamHonest=3"

/-- The non-circularity check items 242, 243 and 244 also carry: a measurement
    of what the escape costs may not route through the escape.  `glit=true`
    records that the literal spent here is item 244's own span lemma and not a
    fresh one, and `entry=true` that what it composes into is `[183]`'s entry
    constructor rather than a bespoke relation. -/
def expectedSpend : String := "drop=false glit=true entry=true"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (authored, usesVal) := usesAll env
  -- the production universe, re-derived
  let mut prods : Std.HashSet Name := {}
  for n in authored do
    if ← isProd n then prods := prods.insert n
  -- §1 the path at every application site
  let mut pop : Array Name := #[]
  for n in authored do
    if heads.any (fun h => (usesVal.getD n {}).contains h) then pop := pop.push n
  let mut rows : Array String := #[]
  for n in sorted pop do
    let some ci := env.find? n | continue
    let some val := ci.value? (allowOpaque := true) | continue
    let (_, (o, _)) ← (walk prods n val).run (#[], {})
    rows := rows ++ o
  let paths := rows.qsort (· < ·)
  unless paths.toList == expectedPaths do
    throwError "the six sites' grammar path moved:\n{String.intercalate "\n" paths.toList}"
  let spend := (paths.filter (fun r => !r.endsWith "NOSPEND")).size
  let len1 := (paths.filter (fun (r : String) => (r.splitOn "len=1").length > 1)).size
  let mut endsSet : Array String := #[]
  for r in paths do
    match (r.splitOn "ends=").getD 1 "" with
    | "" => pure ()
    | e => unless endsSet.contains e do endsSet := endsSet.push e
  -- §2 the production graph and the stream's alphabet
  let mut succ : Std.HashMap Name (Array Name) := {}
  let mut ctors : Nat := 0
  let mut endsLit : Array String := #[]
  for A in sorted prods.toArray do
    let some (.inductInfo ii) := env.find? A | continue
    let mut outs : Array Name := #[]
    for c in ii.ctors do
      let some ci := env.find? c | continue
      ctors := ctors + 1
      let (ns, lit) ← forallTelescope ci.type fun xs concl => do
        let cargs := concl.getAppArgs
        let ce? := if cargs.size ≥ 2 then some cargs[cargs.size-1]! else none
        let mut acc : Array Name := #[]
        let mut lit : Option String := none
        for x in xs do
          let t ← inferType x
          unless (← inferType t).isProp do continue
          for B in t.getUsedConstants do
            if prods.contains B && B != A && !acc.contains B then acc := acc.push B
          let hd := t.getAppFn
          if hd.isConstOf ``GLit || hd.isConstOf ``GChar then
            let a := t.getAppArgs
            if a.size ≥ 2 && ce?.isSome && a[a.size-1]! == ce?.get! then
              lit := some (toString (← ppExpr a[0]!))
        return (acc, lit)
      for B in ns do unless outs.contains B do outs := outs.push B
      if let some ch := lit then endsLit := endsLit.push s!"{c} {ch}"
    succ := succ.insert A outs
  let bfs (src : Name) : String := Id.run do
    let mut par : Std.HashMap Name Name := {}
    let mut d : Std.HashMap Name Nat := ({} : Std.HashMap Name Nat).insert src 0
    let mut front : Array Name := #[src]
    let mut k : Nat := 0
    while !front.isEmpty && k < 40 do
      k := k + 1
      let mut nxt : Array Name := #[]
      for x in front do
        for y in (succ.getD x #[]) do
          if !d.contains y then d := d.insert y k; par := par.insert y x; nxt := nxt.push y
      front := nxt
    match d.get? ``GLit with
    | none => return s!"{src} -> GLit UNREACHABLE"
    | some n =>
      let mut path : List Name := [``GLit]
      let mut cur := ``GLit
      let mut guard : Nat := 0
      while cur != src && guard < 40 do
        guard := guard + 1
        cur := par.getD cur src
        path := cur :: path
      return s!"{src} -> GLit depth={n} \
chain={String.intercalate " > " (path.map (·.getString!))}"
  let alphabet := [``SLAnyDocument, ``SLDocumentPrefix, ``SLDocumentSuffix].map bfs
  unless alphabet == expectedAlphabet do
    throwError "the stream's alphabet moved:\n{String.intercalate "\n" alphabet}"
  let depth := ((alphabet.head!.splitOn "depth=").getD 1 "").take 1
  -- §3 the literal-ending census
  let el := endsLit.qsort (· < ·)
  unless el.toList == expectedEndsLit do
    throwError "the literal-ending constructors moved:\n{String.intercalate "\n" el.toList}"
  let countCh (c : String) : Nat := (el.filter (fun r => r.endsWith s!" {c}")).size
  let chainProds : List Name := [``SBlockSeqEntries, ``SBlockMapEntry, ``SBlockIndented]
  let chainEnds := (el.filter fun r =>
    chainProds.any fun p => (p.toString ++ ".").isPrefixOf r).size
  -- §4 the carriers
  let arms (n : Name) : Nat :=
    match env.find? n with | some (.inductInfo ii) => ii.ctors.length | _ => 0
  let got := s!"pop={pop.size} sites={paths.size} spend={spend} \
nospend={paths.size - spend} len1={len1} \
ends={String.intercalate "|" endsSet.toList} depth={depth} prods={prods.size} \
ctors={ctors} endsLit={el.size} minus={countCh "'-'"} question={countCh "'?'"} \
colon={countCh "':'"} chainEnds={chainEnds} blockArms={arms ``BlockStack} \
seqArms={arms ``SeqFrame} mapArms={arms ``MapFrame} \
streamArms={arms ``SLYamlStream} streamHonest={arms ``SLYamlStream - 1}"
  unless got == expectedLine do
    throwError "the park's production reading moved:\n  got      {got}\n  expected {expectedLine}"
  -- §5 what §1's proofs spend
  let usedBy (n : Name) : Array Name :=
    match env.find? n with
    | none => #[]
    | some ci => ((ci.value? (allowOpaque := true)).getD (mkConst n)).getUsedConstants
  let deps := usedBy ``seq_entry_of_park_span ++ usedBy ``park_carriers_absorb_nothing
    ++ usedBy ``blockStack_refl
  let gotS := s!"drop={deps.contains ``SLYamlStream.scannerDrop} \
glit={deps.contains ``Tests.Guards.ParkGapWidth.dispatchBI_span_glit} \
entry={deps.contains ``SBlockSeqEntries.single}"
  unless gotS == expectedSpend do
    throwError "the span proofs' dependencies moved:\n  got      {gotS}\n  expected {expectedSpend}"
  logInfo m!"ParkGapProduction {got} {gotS}"

end Tests.Guards.ParkGapProduction
