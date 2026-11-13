/-
Copyright (c) 2026 L4YAML contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.ParkGapProduction
import Tests.Guards.Proofs.SuffixGapAudit

/-!
# What `BlockStack`'s missing arm costs, and whether it is honest (DOCS item 246)

Item 245 found that the park's literal has nowhere to land: `BlockStack` has one
reflexive constructor against `SeqFrame`'s ten, so the library cannot state an
open block entry, and what the six one-step sites owe is a block node rather
than a character.  Its recorded NEXT named the number nothing held — **what
`BlockStack`'s missing constructor would close** — and warned that an arm
relating two positions its premises do not connect is `scannerDrop` under
another name.  So the first question here is the arm's honesty and only the
second is its price.

**§0 is the arm**, defined here as `BlockStackOpen` so nothing in the library
moves: `SBlockSeqEntries.single`'s first two premises, held the way
`SeqFrame.midQuestion` holds its indicator — at the END of the frame, the
mandatory separator belonging to the next step.  `n` is bound by the arm and
not by the index, so no statement naming `BlockStack sp sp'` would change.

**§1 grades every arm in the library by connectivity**, and the candidate by
the same code.  Item 236's census (`SuffixGapAudit.lean`) read the surface
grammar's 167 arms for a directed chain of production edges from the
conclusion's source to its target and found `scannerDrop` alone broken.  The
proof layer's parks and stacks were outside it, and they carry CLOSURES — a
content park says "if comments run from `sp_scan` to `sp_mid` then the stream
reaches `sp_mid`" and names its block position nowhere else — so a two-way
reading would misgrade them.  Three grades, each strictly weaker than the last:

- `direct` — item 236's reading, with a closure's own hypotheses and body read
  under its telescope: a directed chain of production, parameter or literal
  edges from the production's source (its last-but-one position) to its
  target (its last);
- `anchored` — undirected, every premise linking every position it mentions,
  closures included, and the target linked to SOME position the conclusion
  names other than itself;
- `broken` — not even anchored: the target is held by nothing the arm states.

`broken` is the escape class.  The candidate must read `direct`, the class of
`SeqFrame.midQuestion`, or the flip below prices a repair for a second hole.

**§2 is the carrier's readers, environment-resolved.**  A flip counts what
stops elaborating, and the build stops at the first failing module, so its
count is a lower bound taken inside `StreamAccum` alone.  The environment can
give the whole first wave — every constant whose value reaches a `BlockStack`
eliminator — library and guards together, and beside it the constants that
merely MENTION the carrier (the invariant's conjunct) and those that BUILD its
`nil`, neither of which an added arm touches.

**§3 is the second wave.**  The readers are the two absorptions, and with the
arm both are FALSE as stated — a stream cannot absorb an open entry — so their
repair is a restatement, and a restatement's price is its readers.

**§4 is what the arm closes.**  `entry_open_of_park_span` spends the six
sites' own path and item 244's literal into the candidate carrier with no
unpaid premise, against item 245's `seq_entry_of_park_span`, which needed a
whole block node to land the same literal in the grammar.

`scripts/flips/item246_carrier_{arm,retire}.json` (via `scripts-flip`) runs the flip for real — `arm` adds the constructor,
`retire` adds it and deletes both absorptions — restores the source, and checks
its `StreamAccum` counts against the lists pinned here.
-/

open Lean Lean.Meta Lean.Elab
open L4YAML
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge
open Tests.Guards.DropDependents (usesAll modOf sorted uses)
open Tests.Guards.DispatchPrice (isProd)
open Tests.Guards.SuffixGapAudit (asEdge charsOf peelsTo)
open Tests.Guards.ParkGapWidth (fvarsOf dispatchBI_span_glit)

set_option autoImplicit false

namespace Tests.Guards.CarrierArmPrice

/-! ## §0 The candidate arm -/

/-- `BlockStack` with the arm the flip inserts, under another name so the
    library is untouched.  `seqEntryOpen` is `[183]`'s entry with its content
    still owed: the indentation and the `-`, the indicator at the frame's end
    exactly as `SeqFrame.midQuestion` holds its `?`. -/
inductive BlockStackOpen : SurfPos → SurfPos → Prop where
  /-- No active block collections. -/
  | nil (sp : SurfPos) : BlockStackOpen sp sp
  /-- A block sequence entry OPENED at indentation `n`: `s-indent(n)` and the
      `-` scanned, `s-l+block-indented` awaited. -/
  | seqEntryOpen (n : Nat) (sp sp_i sp' : SurfPos)
      (hind : SIndent n sp sp_i) (hdash : GLit '-' sp_i sp') : BlockStackOpen sp sp'

/-! ## §4 What the arm closes -/

/-- **The park's literal lands, and nothing is owed.**  The same two facts item
    245's `seq_entry_of_park_span` spent — the sites' `SIndent` path and item
    244's `dispatchBI_span_glit` — are the candidate arm's two premises, and
    the arm's target is where the scanner's cursor stands.  Item 245's lemma
    needed `GNot SNsChar` and a whole `SBlockIndented` beyond this point; this
    one needs nothing beyond it, because a carrier holds an entry OPEN where a
    production can only hold one closed. -/
lemma entry_open_of_park_span {n : Nat} {s s' : ScannerState} {rest : List Char}
    {sp_mid sp_sc sp_scan' : SurfPos}
    (h_path : SIndent n sp_mid sp_sc)
    (h_step : scanNextToken_dispatchBlockIndicators s '-' = Except.ok (some s'))
    (h_in : ScannerSurfCorr s sp_sc) (h_out : ScannerSurfCorr s' sp_scan')
    (h_chars : sp_sc.chars = '-' :: rest) :
    BlockStackOpen sp_mid sp_scan' :=
  .seqEntryOpen n sp_mid sp_sc sp_scan' h_path
    (dispatchBI_span_glit h_step h_in h_out h_chars (by decide) (by decide))

/-! ## §1 The connectivity census -/

/-- The directed production edges a premise of type `t` forces.  Item 236's
    `asEdge` on the premise itself; and when the premise is a closure, an
    `∃`, or a conjunction, the edges of its parts under its own telescope —
    what the arm's producer must prove to build it.  A disjunction forces
    neither side and contributes nothing. -/
partial def directEdges (t : Expr) : MetaM (Array (Expr × Expr × Bool)) := do
  if let some e ← asEdge t then return #[e]
  match t with
  | .forallE .. =>
    forallTelescope t fun ys body => do
      let mut acc : Array (Expr × Expr × Bool) := #[]
      for y in ys do acc := acc ++ (← directEdges (← inferType y))
      return acc ++ (← directEdges body)
  | .mdata _ b => directEdges b
  | _ =>
    if t.isAppOfArity ``And 2 then
      return (← directEdges t.appFn!.appArg!) ++ (← directEdges t.appArg!)
    if t.isAppOfArity ``Exists 2 then
      match t.appArg! with
      | .lam nm a b bi =>
        return ← withLocalDecl nm bi a fun x => directEdges (b.instantiate1 x)
      | _ => return #[]
    return #[]

/-- The `SurfPos`-typed free variables a term mentions, closures included. -/
def posFVars (e : Expr) : MetaM (Array Expr) :=
  (fvarsOf e).filterM fun v => return (← inferType v).isConstOf ``SurfPos

/-- Undirected connectivity over hyperedges, by fixpoint. -/
def linked (groups : Array (Array Expr)) (a b : Expr) : Bool := Id.run do
  let mut seen : Array Expr := #[a]
  let mut changed := true
  while changed do
    changed := false
    for g in groups do
      if g.any seen.contains then
        for x in g do
          unless seen.contains x do seen := seen.push x; changed := true
  return seen.contains b

/-- Grade one constructor. -/
def grade (c : Name) : MetaM String := do
  let some ci := (← getEnv).find? c | return "MISSING"
  forallTelescope ci.type fun xs concl => do
    let cargs := concl.getAppArgs
    if cargs.size < 2 then return "NOPOS"
    let src := cargs[cargs.size - 2]!
    let tgt := cargs[cargs.size - 1]!
    let mut edges : Array (Expr × Expr × Bool) := #[]
    let mut groups : Array (Array Expr) := #[]
    for x in xs do
      let t ← inferType x
      unless (← inferType t).isProp do continue
      edges := edges ++ (← directEdges t)
      let ps ← posFVars t
      if ps.size > 1 then groups := groups.push ps
    -- literal steps between explicit positions, item 236's rule
    let mut nodes : Array Expr := #[src, tgt]
    for (u, v, _) in edges do
      nodes := nodes.push u; nodes := nodes.push v
    for a in cargs do
      if (← inferType a).isConstOf ``SurfPos then nodes := nodes.push a
    for a in nodes do
      for b in nodes do
        if a == b then continue
        match charsOf a, charsOf b with
        | some ca, some cb =>
          if peelsTo ca cb 64 then
            edges := edges.push (a, b, false); groups := groups.push #[a, b]
        | _, _ => pure ()
    -- a conclusion position stands for the variables it mentions
    for a in cargs do
      if (← inferType a).isConstOf ``SurfPos then
        let ps ← posFVars a
        if !ps.isEmpty then groups := groups.push (ps.push a)
    -- direct: a directed chain from src to tgt
    let direct : Bool := Id.run do
      let mut seen : Array Expr := #[src]
      let mut changed := true
      while changed do
        changed := false
        for (u, v, _) in edges do
          if seen.contains u && !seen.contains v then
            seen := seen.push v; changed := true
      return seen.contains tgt
    if direct then return "direct"
    -- anchored: tgt linked to some other conclusion position, undirected
    let mut anchored := false
    for a in cargs do
      if a == tgt then continue
      unless (← inferType a).isConstOf ``SurfPos do continue
      if linked groups a tgt then anchored := true
    return if anchored then "anchored" else "broken"

/-! ## §2 The pins -/

/-- The escape class over the library's 235 arms.  Two, and they are R3's two
    deletions: item 236's arm, and item 244's park read by the census instead
    of by hand. -/
-- 2026-11-09 (item 469): `FlowArm.openBase` joins the escape class — the depth-0 open's landing `sp_flow'` is left free (the helper `accum_flow_open_depth0` lands it existentially; the restatement at `sp_open` is priced for (β), IOU 1 of item 469).
def expectedBroken : List String :=
  ["L4YAML.Proofs.StreamAccum.FlowArm.openBase broken",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingFlow broken",
   "L4YAML.Surface.SLYamlStream.scannerDrop broken"]

/-- Connected, but not by a directed production chain from the production's own
    source: the content parks, which leave their block position floating and
    connect the scan position to the STREAM's start through a closure, and the
    flow stack's base arms, whose outer boundary "is free — any gap lives
    inside `resume`". -/
-- 2026-11-09 (item 469): `FlowArm.openNest` / `comma` / `closeNested` join the anchored class — the arm lands at the indicator's end (`sp_open` / `sp_tok`), tied to the lead by `GLit` but not by a directed chain from the stack's own `sp_block`, exactly as `FlowOpenStack`'s four arms.
-- 2026-11-10 (item 469, review round 1): `GapRead.white` joins the anchored class — re-indexed by the state, its white arm lands at its own `sp_flow` (the gap `GStar SSWhite sp_flow sp_scan` reaches the cursor but the frame does not move), as `InteriorGap.props` sits here already.
-- 2026-11-11 (item 484): `ContentArm.blockScalar` joins the anchored class — its landing is the disjunction
-- `SCLLiteral 0 sp sp' ∨ SCLFolded 0 sp sp'` that `scanBlockScalar_prod` concludes for the dispatcher's one `|`/`>` call,
-- which the directed-chain walk does not read through; a literal/folded split is priced as that producer's split.
-- 2026-11-12 (item 487): `ContentLead.white` / `.props` join the anchored class — the receive's premises at `sp_prep`,
-- quantified over every floor `m ≤ minContentIndentOf sc` (`SSeparateLines m` / `PropsRun m` / `SSeparate m`), not one
-- directed chain; they are what the core derives inside its proof, replayed (ContentBridge §5).
def expectedAnchoredOnly : List String :=
  ["L4YAML.Proofs.Serialization.TraceOf.ContentBridge.ContentLead.props",
   "L4YAML.Proofs.Serialization.TraceOf.ContentBridge.ContentLead.white",
   "L4YAML.Proofs.StreamAccum.ContentArm.blockScalar",
   "L4YAML.Proofs.StreamAccum.FlowArm.closeNested",
   "L4YAML.Proofs.StreamAccum.FlowArm.comma",
   "L4YAML.Proofs.StreamAccum.FlowArm.openNest",
   "L4YAML.Proofs.StreamAccum.FlowOpenStack.mapBase",
   "L4YAML.Proofs.StreamAccum.FlowOpenStack.mapNest",
   "L4YAML.Proofs.StreamAccum.FlowOpenStack.seqBase",
   "L4YAML.Proofs.StreamAccum.FlowOpenStack.seqNest",
   "L4YAML.Proofs.StreamAccum.GapRead.white",
   "L4YAML.Proofs.StreamAccum.InteriorGap.props",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingDirective",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingDocStart",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue",
   "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps"]

/-- **Every constant whose value reaches a `BlockStack` eliminator** — the whole
    first wave, which no flip can report because the build stops at the first
    failing module. -/
def expectedReaders : List String :=
  ["L4YAML.Proofs.StreamAccum.absorb_stacks",
   "L4YAML.Proofs.StreamAccum.absorb_stacksB",
   "Tests.Guards.ParkGapProduction.blockStack_refl"]

/-- **The absorptions' readers** — the second wave, what the first propagates
    when it cannot be repaired in place. -/
-- 2026-11-11 (item 484): `accum_step_content` → `accum_step_content_core` — the body that reads the absorptions is the renamed
-- core; the `accum_step_content` wrapper re-packs its tuple and reads no absorption itself.
def expectedAbsorbReaders : List String :=
  ["L4YAML.Proofs.StreamAccum.accum_flow_open_depth0",
   "L4YAML.Proofs.StreamAccum.accum_step_block",
   "L4YAML.Proofs.StreamAccum.accum_step_content_core",
   "L4YAML.Proofs.StreamAccum.accum_step_structural",
   "L4YAML.Proofs.StreamAccum.preprocessing_eof_extends_stream"]

-- 2026-10-23 ([162]): `prods` +2, `ctors`/`surfArms`/`surfDirect` +5, `same` +2 (the two `.empty` arms),
-- `direct` +5 — `SCIndentationIndicator` and `SCChompingIndicator`; the carrier reading is unchanged.
-- `prods` 133 → 137, `ctors` 240 → 249, `direct` 226 → 235 on 2026-10-23:
-- `Proofs.Production.Acceptance.Quoted`'s four narrowed quoted-scalar relations.
-- `prods` 137 → 145, `ctors` 249 → 263, `direct` 235 → 249 on 2026-10-23: the same module's
-- eight multi-line relations (fourteen constructors, all direct).
-- `prods` 145 → 149, `ctors` 263 → 271, `direct` 249 → 257 on 2026-10-23: the four one-line plain
-- relations of `Acceptance/Plain.lean` (Stream E).
-- `prods` 150 → 151, `ctors` 271 → 272, `direct` 257 → 258 on 2026-10-23: `PlainNextLineOk`, the
-- multi-line plain relation of `Acceptance/Plain.lean` (Stream E).
-- `prods` 151 → 152, `ctors` 272 → 276, `direct` 258 → 262 on 2026-10-23: `TagOk` of
-- `Acceptance/Properties.lean` (Stream E).
-- `prods` 152 → 159, `ctors` 276 → 293, `direct` 262 → 279 on 2026-10-23: the seven block-scalar
-- relations of `Acceptance/BlockScalar.lean` (Stream E); `same` 21 → 24: `ChompOk.clip`,
-- `IndentOk.auto` and `BlockStopOk.outdent` land where they start.
-- `prods` 160 → 162, `ctors` 296 → 304, `direct` 282 → 290, `surfArms` 172 → 180, `surfDirect` 171 → 179
-- on 2026-10-24: `SCFlowJsonContent`/`SCFlowJsonNode` ([148]/[149] JSON-key adjacent value); all 8 arms direct.
-- 2026-10-24 (B3): prods/ctors/direct/surfArms/surfDirect each +2 — the explicit JSON-key adjacent-value
-- twins in Surface/Node.lean (both direct, no anchor).
-- 2026-10-25 (#99 review): prods 164 → 163 — the dead `FlowLead` duplicate of `leadFree` is deleted.
-- 2026-10-25 (slice 2, `TraceOf/UniqueFlow.lean`): prods 163 → 165, ctors 306 → 308, direct 292 → 294 — the proof-layer
-- relations `PStep` (2 arms, both direct) and `Follow`; nothing in Surface, no anchor.
-- 2026-10-26 (item 367, `[82]`): `SLDirective` 1 → 3 arms (surfArms 182 → 184, surfDirect 181 → 183) and the four scanner-cut relations in StructureProduction: prods 165 → 169, ctors 308 → 313, direct 294 → 299; the carrier readers are unchanged.
-- 2026-11-09 (item 469): prods 169 → 172, ctors 313 → 318 (`GapRead`, `FlowArm`, `FlowStackKA`); same 25 → 26 and direct 299 → 300 (`GapRead.white` keeps its position, `GapRead.props` lands at `sp_scan`); anchoredOnly 12 → 15 and broken 2 → 3 — `FlowArm`'s arms, as the two pins above record.
-- 2026-11-10 (item 469, review round 1): prods 172 → 171 (`FlowStackKBody`/`FlowStackKA` out, `gapTail` in), ctors 318 → 320 (`GapRead`/`FlowArm` re-shaped), same 26 → 27 and direct 300 → 301 (`GapRead` is indexed by the state: its white arm keeps its own `sp_flow`, counted once more), anchoredOnly 15 → 16 (`GapRead.white`).
-- 2026-11-11 (item 484, ContentArm): prods=171 → 172, ctors=320 → 328, direct=301 → 308, anchoredOnly=16 → 17, mentions=40 → 41 — `ContentArm` (eight
-- constructors; `blockScalar` anchored, see above) and `accum_step_content_core` beside its wrapper.
def expectedLine : String :=
  -- 2026-11-12 (item 487): prods 172 → 173, ctors 328 → 330, anchoredOnly 17 → 19 — `ContentLead` (two anchored arms).
  -- 2026-11-13 (item 489, the landing agreement): prods 173 → 174 (`LastNonWhite`, ContentBridge §7, read now that
  -- §7–§9 are exported), mentions 41 → 42 (`accum_step_content_pairB` names the arm); arm classes unchanged.
  "prods=174 ctors=330 same=27 direct=308 anchoredOnly=19 broken=3 surfArms=184 \
surfDirect=183 candidate=direct candidateNil=direct readers=3 libReaders=2 \
guardReaders=1 mentions=42 producers=21 absorbReaders=5 absorbPlainReaders=0"

/-- Non-circularity, items 242–245's check: the closing lemma spends item 244's
    span (`glit`), lands in the candidate arm (`arm`), and routes through no
    escape (`drop`). -/
def expectedSpend : String := "drop=false glit=true arm=true"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let (authored, usesVal) := usesAll env
  let here : Name := `Tests.Guards.CarrierArmPrice
  -- §1 the production universe, item 245's, and the candidate beside it
  let mut prods : Array Name := #[]
  for n in authored do
    if here.isPrefixOf n then continue
    if ← isProd n then prods := prods.push n
  let mut ctors : Nat := 0
  let mut surfArms : Nat := 0
  let mut surfDirect : Nat := 0
  let mut same : Nat := 0
  let mut direct : Nat := 0
  let mut anchoredOnly : Array String := #[]
  let mut broken : Array String := #[]
  for A in sorted prods do
    let some (.inductInfo ii) := env.find? A | continue
    for c in ii.ctors do
      ctors := ctors + 1
      let g ← grade c
      let isSurf := (`L4YAML.Surface).isPrefixOf c
      if isSurf then surfArms := surfArms + 1
      match g with
      | "direct" =>
        direct := direct + 1
        if isSurf then surfDirect := surfDirect + 1
        let some ci := env.find? c | continue
        let refl ← forallTelescope ci.type fun _ concl => do
          let a := concl.getAppArgs
          return a.size ≥ 2 && a[a.size-2]! == a[a.size-1]!
        if refl then same := same + 1
      | "anchored" => anchoredOnly := anchoredOnly.push c.toString
      | _ => broken := broken.push s!"{c} {g}"
  let candidate ← grade ``BlockStackOpen.seqEntryOpen
  let candidateNil ← grade ``BlockStackOpen.nil
  let brokenL := (broken.qsort (· < ·)).toList
  unless brokenL == expectedBroken do
    throwError "the escape class moved:\n{String.intercalate "\n" brokenL}"
  let anchL := (anchoredOnly.qsort (· < ·)).toList
  unless anchL == expectedAnchoredOnly do
    throwError "the anchored-only class moved:\n{String.intercalate "\n" anchL}"
  -- §2 the carrier's readers, mentions and producers
  let elim : List Name := [``BlockStack.casesOn, ``BlockStack.rec, ``BlockStack.recOn]
  let mut readers : Array Name := #[]
  let mut producers : Nat := 0
  let mut mentions : Nat := 0
  let mut absorbReaders : Array Name := #[]
  let mut absorbPlain : Nat := 0
  for n in authored do
    if here.isPrefixOf n then continue
    let v := usesVal.getD n {}
    let ty := uses env n false
    if elim.any v.contains then readers := readers.push n
    if v.contains ``BlockStack.nil then producers := producers + 1
    if v.contains ``BlockStack || ty.contains ``BlockStack then mentions := mentions + 1
    if v.contains ``absorb_stacks || v.contains ``absorb_stacksB then
      absorbReaders := absorbReaders.push n
    if v.contains ``absorb_stacks then absorbPlain := absorbPlain + 1
  let readersL := (sorted readers).toList.map (·.toString)
  unless readersL == expectedReaders do
    throwError "the carrier's readers moved:\n{String.intercalate "\n" readersL}"
  let libReaders := (readers.filter fun n => (`L4YAML).isPrefixOf (modOf env n)).size
  let absorbL := (sorted absorbReaders).toList.map (·.toString)
  unless absorbL == expectedAbsorbReaders do
    throwError "the absorptions' readers moved:\n{String.intercalate "\n" absorbL}"
  let got := s!"prods={prods.size} ctors={ctors} same={same} direct={direct} \
anchoredOnly={anchL.length} broken={brokenL.length} surfArms={surfArms} \
surfDirect={surfDirect} candidate={candidate} candidateNil={candidateNil} \
readers={readers.size} libReaders={libReaders} guardReaders={readers.size - libReaders} \
mentions={mentions} producers={producers} absorbReaders={absorbL.length} \
absorbPlainReaders={absorbPlain}"
  unless got == expectedLine do
    throwError "the carrier's price moved:\n  got      {got}\n  expected {expectedLine}"
  -- §4 what the closing lemma spends
  let deps := ((env.find? ``entry_open_of_park_span).bind
    (·.value? (allowOpaque := true))).getD (mkConst ``entry_open_of_park_span)
    |>.getUsedConstants
  let gotS := s!"drop={deps.contains ``SLYamlStream.scannerDrop} \
glit={deps.contains ``Tests.Guards.ParkGapWidth.dispatchBI_span_glit} \
arm={deps.contains ``BlockStackOpen.seqEntryOpen}"
  unless gotS == expectedSpend do
    throwError "the closing lemma's dependencies moved:\n  got      {gotS}\n  expected {expectedSpend}"
  logInfo m!"CarrierArmPrice {got} {gotS}"

end Tests.Guards.CarrierArmPrice
