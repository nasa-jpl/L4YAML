/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.DispatchPrice

/-!
# What `connected_drop` closes, site by site (DOCS item 243)

Item 242 proved that the escape's CONNECTED form is a theorem: given
`SLYamlStream a b` and `SSLComments b c`, the stream reaches `c` without
`SLYamlStream.scannerDrop`.  Its recorded NEXT asked how many of β.5's
twenty-four reproofs that theorem closes outright — whether each spends the arm
with the comment run starting where the stream ends — and warned that a census
comparing expressions would UNDER-count, because positions in this library are
pinned by `ScannerSurfCorr_unique` rather than by sharing a variable.

**The twenty-four spend nothing.**  Item 238's `D` is four declarations, two of
them Tests-side exhibits written to witness the arm's falsity, and the arm is
applied in the library at exactly two places — `dropClose` and
`PendingNode.close_with_ssl`'s `pendingFlow` branch, item 239's two
restatements.  The question "which of the twenty-four is connected" is therefore
asked here of the ELEVEN application sites the environment actually holds: the
four that build the arm and the seven that call one of the two restatements.

## The answer is zero, under four readings at once

| reading | what it asks | count |
|---|---|---|
| `syn` | the two endpoints are the same expression | **0** |
| `deq` | …or reducibly defeq | **0** |
| `eqHyp` | …or an equation between them is in scope | **0** |
| `forced` | …or two correspondences at one state force them equal | **0** |

**`connected_drop` closes none of the eleven**, so it closes none of the
twenty-four either, and β.5's bill does not shrink by one item.

## The warned-about mechanism is half-present, and the missing half is the point

`forced` is zero, but not because correspondences are absent.  **Five of the
eleven hold a `ScannerSurfCorr` at the scan position, every one of them at the
PARK'S OWN scanner state, and not one holds a correspondence at the block
position.**  The pair the mandate hoped would pin the two positions together is
exactly half-present at every call site, and the absent half is the one whose
presence would be fatal: §1 proves that a park holding both correspondences has
`sp_block = sp_scan` and therefore **consumed nothing**.

So the mechanism runs the other way from the warning.  A correspondence at a
shared state does not silently identify the endpoints a syntactic census misses;
it would identify them and thereby delete the span the park exists to carry.
The five sites hold one and never two because the park's whole content lives in
the gap between them.

## What the sites do hold, and what it buys

Every one of the five park calls has one hypothesis mentioning both endpoints,
and it is the `PendingNode` itself — the premise item 239 refuted.  Those five
are the same five `scripts/flip_supplier.py --end weak` breaks when
`close_with_ssl` gains the connecting premise, so the walk and the flip name one
ring by two independent routes: the flip reads what stops compiling, this reads
what the proof terms hold.  The other
six sites have none at all.  §1 refutes the premise set the five actually carry:
a stream to the block position, a correspondence at the scan position and a
comment run from it do NOT give a stream to the run's end.  The witness is the
scanner at the seed of `"b"` while the stream reaches only the empty position,
and every premise permits it because **a correspondence at ONE of the two
positions says nothing about the path between them.**

`corr_pair_closes` records the positive half: with both correspondences the arm
closes in item 239's post-β.5 model through item 242's `connected_drop_nd`, no
escape and no new production.  Together the three lemmas say that the park's
gap admits exactly two closures — identify the endpoints, which empties the
park, or derive a path across them, which is the obligation item 242 measured as
carried once in the whole library.

## Where this leaves the price

The unit of β.5's connection price is the CALL, not the dependent.  Six calls
owe a span; the twenty-four owe nothing until their suppliers' statements
change, which is what items 240 and 241 priced at nineteen and eighteen.
-/

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab
open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open Tests.Guards.DropFalsity (StreamND nd_refl nd_suffix)
open Tests.Guards.ColumnWalkPrice (sslComments_refl)
open Tests.Guards.ProducerDerivation (scSeed corrSeed)
open Tests.Guards.DispatchPrice (connected_drop_nd)
open Tests.Guards.DropDependents (usesAll census sorted)

namespace Tests.Guards.ParkGapCensus

/-! ## §1 The two closures of the park's gap -/

/-- **The correspondence pair closes the arm.**  Two correspondences at one
    scanner state pin the park's two positions to one position, and item 242's
    connected form then carries the stream across the comment run with no
    escape.  Stated in `StreamND`, the model that has no `scannerDrop` to
    fall back on. -/
lemma corr_pair_closes {sc : ScannerState} {sp_start sp_block sp_scan sp_mid : SurfPos}
    (h_block : ScannerSurfCorr sc sp_block) (h_scan : ScannerSurfCorr sc sp_scan)
    (h_stream : StreamND sp_start sp_block) (h_ssl : SSLComments sp_scan sp_mid)
    (hcol : sp_scan.col = 0) :
    StreamND sp_start sp_mid := by
  have heq := ScannerSurfCorr_unique h_block h_scan
  subst heq
  exact connected_drop_nd h_stream h_ssl hcol

/-- **…and its price is the park's own content.**  The same pair forces the two
    positions equal, so a park that held both would have absorbed no characters
    between them.  This is why the census finds a correspondence at the scan
    position at every call site and never one at the block position: holding the
    second is holding that the scanner has not moved. -/
lemma corr_pair_consumes_nothing {sc : ScannerState} {sp_block sp_scan : SurfPos}
    (h_block : ScannerSurfCorr sc sp_block) (h_scan : ScannerSurfCorr sc sp_scan) :
    sp_block.chars.length = sp_scan.chars.length := by
  rw [ScannerSurfCorr_unique h_block h_scan]

/-- **The half every call site DOES hold buys nothing.**  The premise set is the
    one the five park calls carry at the arm — a stream to the block position, a
    correspondence at the scan position, a comment run from it — and the
    conclusion is the connection β.5 needs.  The witness is the scanner at the
    seed of `"b"` while the stream reaches only the empty position: the
    correspondence constrains the scan position alone, and the datum is a
    statement about the path.  Item 241 refuted the same shape at the park's
    producer; this is the consumer's side of it. -/
lemma one_corr_gives_no_stream :
    ¬ (∀ (sc : ScannerState) (sp_start sp_block sp_scan sp_mid : SurfPos),
        StreamND sp_start sp_block →
        ScannerSurfCorr sc sp_scan →
        SSLComments sp_scan sp_mid →
        StreamND sp_start sp_mid) := by
  intro h
  have hbad := h (scSeed "b") ⟨[], 0⟩ ⟨[], 0⟩ ⟨"b".toList, 0⟩ ⟨"b".toList, 0⟩
    (nd_refl _) (corrSeed "b") (sslComments_refl _)
  have := (nd_suffix hbad).length_le
  simp at this

/-! ## §2 The site census -/

/-- The arm, the two restatements that spend it, and the park whose two
    positions are the gap.  Named rather than typed into the walk so that a
    rename moves the census with it. -/
def arm : Name := ``SLYamlStream.scannerDrop
def dropClose : Name := `L4YAML.Proofs.StreamAccum.dropClose
def closeWithSsl : Name := `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl
def park : Name := `L4YAML.Proofs.StreamAccum.PendingNode

/-- Where the stream's right endpoint and the comment run's left endpoint sit in
    each head's argument list.  `scannerDrop (s s₁ s₂ s')` puts them at 1 and 2;
    `dropClose (sp_start sp_x) h_stream sp_e sp_m` at 1 and 3;
    `close_with_ssl (sc sp_start sp_block sp_scan sp_mid)` at 2 and 3. -/
def heads : Std.HashMap Name (Nat × Nat) :=
  (((({} : Std.HashMap Name (Nat × Nat)).insert ``SLYamlStream.scannerDrop (1, 2)).insert
    `L4YAML.Proofs.StreamAccum.dropClose (1, 3)).insert
    `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl (2, 3))

/-- One application of one of the three heads, read in the local context it
    stands in. -/
structure Site where
  decl : Name
  fn : Name
  /-- The two endpoints are the same expression. -/
  syn : Bool
  /-- …or reducibly definitionally equal. -/
  deq : Bool
  /-- …or an equation between them is in scope. -/
  eqHyp : Bool
  /-- …or two correspondences at ONE scanner state force them equal. -/
  forced : Bool
  /-- Correspondences at the stream's right endpoint. -/
  corrBlock : Nat
  /-- Correspondences at the comment run's left endpoint. -/
  corrScan : Nat
  /-- …of which this many stand at the state of a `PendingNode` in scope. -/
  corrScanAtPark : Nat
  /-- The head constants of every hypothesis mentioning BOTH endpoints. -/
  spans : Array Name
deriving Inhabited

abbrev W := StateRefT (Array Site × Std.HashSet Expr) MetaM

/-- Read one application site against the local context it stands in. -/
def record (decl fn : Name) (a b : Expr) : W Unit := do
  let syn := a == b
  let deq ← (try withReducible (isDefEq a b) catch _ => pure false)
  let lctx ← getLCtx
  let mut corrs : Array (Expr × Expr) := #[]
  let mut parkStates : Array Expr := #[]
  let mut spans : Array Name := #[]
  let mut eqHyp := false
  for ld in lctx do
    if ld.isImplementationDetail then continue
    let t := ld.type
    unless (← inferType t).isProp do continue
    if t.isAppOfArity ``ScannerSurfCorr 2 then
      corrs := corrs.push (t.appFn!.appArg!, t.appArg!)
    if t.isAppOf park then
      let ar := t.getAppArgs
      if ar.size ≥ 1 then parkStates := parkStates.push ar[0]!
    if t.isAppOfArity ``Eq 3 then
      let l := t.appFn!.appArg!
      let r := t.appArg!
      if (l == a && r == b) || (l == b && r == a) then eqHyp := true
    if a.isFVar && b.isFVar && t.containsFVar a.fvarId! && t.containsFVar b.fvarId! then
      if let .const n _ := t.getAppFn then spans := spans.push n
  let mut forced := false
  for (s1, p1) in corrs do
    for (s2, p2) in corrs do
      if s1 == s2 && ((p1 == a && p2 == b) || (p1 == b && p2 == a)) then forced := true
  let corrBlock := (corrs.filter (fun p => p.2 == a)).size
  let atScan := corrs.filter (fun p => p.2 == b)
  modify fun (hs, v) =>
    (hs.push { decl, fn, syn, deq, eqHyp, forced, corrBlock, corrScan := atScan.size,
               corrScanAtPark := (atScan.filter (fun p => parkStates.any (· == p.1))).size,
               spans := sorted spans }, v)

/-- Walk a proof term under its binders.  `withLocalDecl` is what makes the
    reading a reading of the SITE rather than of the statement: the
    correspondences and the park live in the context the application stands in,
    not in the declaration's telescope. -/
partial def walk (decl : Name) (e : Expr) : W Unit := do
  if (← get).2.contains e then return
  modify fun (hs, v) => (hs, v.insert e)
  match e with
  | .app .. =>
    let f := e.getAppFn
    let args := e.getAppArgs
    if let .const n _ := f then
      if let some (ia, ib) := heads[n]? then
        if args.size > max ia ib then record decl n args[ia]! args[ib]!
    walk decl f
    for x in args do walk decl x
  | .lam nm t b bi =>
    walk decl t
    withLocalDecl nm bi t fun x => walk decl (b.instantiate1 x)
  | .letE nm t val b _ =>
    walk decl t
    walk decl val
    withLetDecl nm t val fun x => walk decl (b.instantiate1 x)
  | .forallE nm t b bi =>
    walk decl t
    withLocalDecl nm bi t fun x => walk decl (b.instantiate1 x)
  | .mdata _ b => walk decl b
  | .proj _ _ b => walk decl b
  | _ => pure ()

/-- One row per site, in the form the pin below compares against. -/
def render (s : Site) : String :=
  s!"{s.decl} <- {s.fn} syn={s.syn} deq={s.deq} eqHyp={s.eqHyp} forced={s.forced} \
corrBlock={s.corrBlock} corrScan={s.corrScan} atPark={s.corrScanAtPark} \
spans={String.intercalate "," (s.spans.map (·.getString!)).toList}"

/-! ## §3 The pins -/

/-- **The population, re-derived rather than typed.**  Item 238's `D` is four;
    the walk runs over every authored declaration whose proof term references
    the arm or one of the two restatements, which is ten. -/
def expectedPop : String := "D=4 T=28 pop=10 sites=11"

/-- **The answer, in one line.**  Four independent readings of "connected", all
    zero, beside the correspondence census that explains why the fourth is. -/
def expectedTally : String :=
  "syn=0 deq=0 eqHyp=0 forced=0 corrBlock=0 corrScan=5 atPark=5 parkSpan=6 noSpan=5 otherSpan=0"

/-- Every site, with what its context holds.  **`atPark=1` on five of them and
    `corrBlock=0` on all eleven is the finding**: the pair that would pin the
    endpoints together is half-present wherever the park is, and the half that
    is missing is the one §1 proves would empty it. -/
def expectedSites : List String :=
  ["L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl <- \
L4YAML.Surface.SLYamlStream.scannerDrop syn=false deq=false eqHyp=false forced=false \
corrBlock=0 corrScan=0 atPark=0 spans=HEq,PendingNode",
   "L4YAML.Proofs.StreamAccum.accum_block_pending <- \
L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl syn=false deq=false eqHyp=false \
forced=false corrBlock=0 corrScan=1 atPark=1 spans=PendingNode",
   "L4YAML.Proofs.StreamAccum.accum_content_pending <- \
L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl syn=false deq=false eqHyp=false \
forced=false corrBlock=0 corrScan=1 atPark=1 spans=PendingNode",
   "L4YAML.Proofs.StreamAccum.accum_flow_open_depth0 <- \
L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl syn=false deq=false eqHyp=false \
forced=false corrBlock=0 corrScan=1 atPark=1 spans=PendingNode",
   "L4YAML.Proofs.StreamAccum.accum_flow_open_depth0 <- \
L4YAML.Proofs.StreamAccum.dropClose syn=false deq=false eqHyp=false forced=false \
corrBlock=0 corrScan=0 atPark=0 spans=",
   "L4YAML.Proofs.StreamAccum.accum_structural_pending <- \
L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl syn=false deq=false eqHyp=false \
forced=false corrBlock=0 corrScan=1 atPark=1 spans=PendingNode,PendingNode",
   "L4YAML.Proofs.StreamAccum.dropClose <- \
L4YAML.Surface.SLYamlStream.scannerDrop syn=false deq=false eqHyp=false forced=false \
corrBlock=0 corrScan=0 atPark=0 spans=",
   "L4YAML.Proofs.StreamAccum.eof_pending <- \
L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl syn=false deq=false eqHyp=false \
forced=false corrBlock=0 corrScan=1 atPark=1 spans=PendingNode",
   "Tests.Guards.ColumnWalkPrice.stream_anything <- \
L4YAML.Surface.SLYamlStream.scannerDrop syn=false deq=false eqHyp=false forced=false \
corrBlock=0 corrScan=0 atPark=0 spans=",
   "Tests.Guards.DropFalsity.close_with_ssl_reaches <- \
L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl syn=false deq=false eqHyp=false \
forced=false corrBlock=0 corrScan=0 atPark=0 spans=",
   "Tests.Guards.SuffixGapAudit.stream_anything <- \
L4YAML.Surface.SLYamlStream.scannerDrop syn=false deq=false eqHyp=false forced=false \
corrBlock=0 corrScan=0 atPark=0 spans="]

/-- **What §1's closures spend.**  `drop=false` on all three is the
    non-circularity check that item 242's derivation also carries; `unique=true`
    records that the pair route is `ScannerSurfCorr_unique` and nothing else. -/
def expectedSpend : String := "drop=false unique=true connected=true"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pre := usesAll env
  let (authored, usesVal) := pre
  let c ← census (some pre)
  let mut pop : Array Name := #[]
  for n in authored do
    let uv := usesVal.getD n {}
    if uv.contains arm || uv.contains dropClose || uv.contains closeWithSsl then
      pop := pop.push n
  let mut sites : Array Site := #[]
  for n in sorted pop do
    let some ci := env.find? n | continue
    let some val := ci.value? (allowOpaque := true) | continue
    let (_, (hs, _)) ← (walk n val).run (#[], {})
    sites := sites ++ hs
  let gotP := s!"D={c.direct.size} T={c.trans.size} pop={pop.size} sites={sites.size}"
  unless gotP == expectedPop do
    throwError "the site population moved:\n  got      {gotP}\n  expected {expectedPop}"
  let cnt (f : Site → Bool) : Nat := (sites.filter f).size
  let gotT := s!"syn={cnt (·.syn)} deq={cnt (·.deq)} eqHyp={cnt (·.eqHyp)} \
forced={cnt (·.forced)} corrBlock={cnt (·.corrBlock > 0)} corrScan={cnt (·.corrScan > 0)} \
atPark={cnt (·.corrScanAtPark > 0)} parkSpan={cnt (·.spans.contains park)} \
noSpan={cnt (·.spans.isEmpty)} \
otherSpan={cnt (fun s => s.spans.any (fun h => h != park && h != ``HEq))}"
  unless gotT == expectedTally do
    throwError "the connected tally moved:\n  got      {gotT}\n  expected {expectedTally}"
  let rows := (sites.map render).qsort (· < ·)
  unless rows.toList == expectedSites do
    throwError "the sites moved:\n{String.intercalate "\n" rows.toList}"
  let usedBy (n : Name) : Array Name :=
    match env.find? n with
    | none => #[]
    | some ci => ((ci.value? (allowOpaque := true)).getD (mkConst n)).getUsedConstants
  let deps := usedBy ``corr_pair_closes ++ usedBy ``corr_pair_consumes_nothing
    ++ usedBy ``one_corr_gives_no_stream
  let gotS := s!"drop={deps.contains arm} unique={deps.contains ``ScannerSurfCorr_unique} \
connected={deps.contains ``Tests.Guards.DispatchPrice.connected_drop_nd}"
  unless gotS == expectedSpend do
    throwError "the closures' dependencies moved:\n  got      {gotS}\n  expected {expectedSpend}"
  logInfo m!"ParkGapCensus {gotP} {gotT} {gotS}"

end Tests.Guards.ParkGapCensus
