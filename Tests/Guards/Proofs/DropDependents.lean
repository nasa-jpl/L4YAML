/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML
-- The library root does not reach these nine.  A census that imports only
-- `L4YAML` reads 222 of the library's 231 modules and reports a library; item
-- 237's read 109 of 230 before it imported the root at all.
import L4YAML.Capstones
import L4YAML.Output.Events
import L4YAML.Output.EventsIx
import L4YAML.Output.JsonIx
import L4YAML.Proofs.Output.IndexedEmitterScannability
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth
import L4YAML.Proofs.Output.IndexedEmitterScannability.FilteredGrowth.PerDispatch
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness
import Tests.Guards.Proofs.ColumnWalkPrice
import Tests.Guards.Proofs.SuffixGapAudit

/-!
# How many proofs β.5 must redo (DOCS item 238)

Row 12's β.5 deletes `SLYamlStream.scannerDrop`.  Three numbers about that arm
were already measured and none of them is its repair bill: it is **two**
textual construction sites (row 12), **one** arm of 167 whose premises leave
the conclusion's target unconnected (item 236), and the sole support of
**fifteen** statements that are true without their hypotheses (item 237).

This file reads the bill off the elaborated environment.  Over the whole tree —
858 modules composed in one environment and the 36 executable entry points
probed one at a time, `scripts/drop_sweep.py` — the arm has

    D=4 direct  S=0 in a statement  R=0 case splits  T=26 transitive

and the transitive set ends at exactly two of the 25 capstones.

## The four populations, and why they must not be merged

**D** names the constructor in its PROOF TERM; **S** names it in its TYPE; **R**
case-splits over `SLYamlStream`, which breaks on an arity change without ever
building the arm; **T** is D closed upward through proof terms.

A walk that reads all four as one number reports the wrong one twice over.
`SLYamlStream.rec`'s own type names every constructor, so a walk that expands
into eliminators reads every case split as a construction — §2 pins that the
recursor's type does carry `scannerDrop`, which is why this census treats
eliminators as terminal and generated `match_`/`proof_`/`eq_` auxiliaries as
transparent.

## T is not the bill

**A theorem's consumers depend on its TYPE, not on its proof.**  Lean's
definitional proof irrelevance (§3) is what makes that exact rather than
approximate: if a supplier keeps its statement and only its proof is redone,
nothing above it is touched.  `S=0` says no consumer's statement names the arm,
so nothing in T breaks on the deletion alone.

The bill is therefore **4 at its floor and 26 at its ceiling**, and which end it
lands on is decided by two statements, not by the graph:

- `dropClose` concludes `SLYamlStream sp_start sp_m` for a `sp_m` its premises
  never reach, so it is the arm restated and cannot survive the deletion.  Its
  one consumer is `accum_flow_open_depth0`.
- `PendingNode.close_with_ssl` is restrictive in its `PendingNode` premise.  Its
  five consumers are `accum_block_pending`, `accum_content_pending`,
  `accum_flow_open_depth0`, `accum_structural_pending` and `eof_pending`.

Whether a statement is reprovable is not a graph property, and this file does
not claim to decide it — the same boundary item 237 drew around its fifteen.
`Tests/Guards/Proofs/DropFalsity.lean` (DOCS item 239) decides it for both of
the two by building the post-β.5 relation and refuting them in it: the
`PendingNode` premise is restrictive in the scanner state and in nothing that
connects `sp_block` to `sp_scan`, so `close_with_ssl` cannot be reproved
either.  **Both are restatements; the other twenty-four are reproofs.**

**How many of the twenty-four are ONLY reproofs is decided by the repair, and
not by this graph either.**  `Tests/Guards/Proofs/RepairChoice.lean` (DOCS item
240) reverses these same edges from `close_with_ssl`: repairing it with a
premise that connects the park's two positions changes NINETEEN statements —
its whole reverse closure, every one of them already inside `T` — while the two
repairs that leave its type alone change none.  That walk also brackets this
one rather than extending it.  For the park's own deletion the environment
reads ten users where the flip breaks seven, and neither one-step references
nor application arity separates a constructor's builders from the case splits
that eliminate it, so there the flip is not optional.

## What the cheap instrument buys over the expensive one

`scripts/flip_drop.py` deletes the arm for real and counts what stops
compiling.  Both construction sites are in one module that the library root
imports, so the build stops there and reports **2** — it cannot see the other
two, and it cannot see the 24 behind them.  Here the environment walk strictly
dominates the flip, which inverts this row's usual ordering; the flip is kept
because it is the only one of the two that checks the deletion elaborates.
-/

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab

namespace Tests.Guards.DropDependents

/-- The arm β.5 deletes. -/
def drop : Name := `L4YAML.Surface.SLYamlStream.scannerDrop

/-- The eliminator suffixes.  A walk must stop at these: the recursor's type
    names every constructor, so expanding into one turns every case split into
    a construction (§2 pins that). -/
def elimNames : List String :=
  ["rec", "recOn", "casesOn", "brecOn", "below", "binductionOn", "ibelow",
   "ndrec", "ndrecOn", "noConfusion", "noConfusionType", "induct",
   "inj", "injEq", "sizeOf_spec"]

/-- Generated for a declaration and regenerated by any repair to it, so a walk
    reads THROUGH these.  Eliminators and constructors are deliberately absent. -/
def isAux (n : Name) : Bool := Id.run do
  if n.isInternal || n.hasMacroScopes then return true
  for c in n.components.map toString do
    if c.startsWith "match_" || c.startsWith "proof_" || c.startsWith "eq_"
       || c.startsWith "_" then
      return true
  return false

/-- Written by a person, and therefore able to carry an obligation. -/
def isAuthored (env : Environment) (n : Name) : Bool := Id.run do
  if isAux n then return false
  if env.isConstructor n then return false
  for c in n.components.map toString do
    if elimNames.contains c then return false
  return true

/-- An eliminator of `SLYamlStream` — what a case split over the stream reaches. -/
def isStreamElim (n : Name) : Bool :=
  (`L4YAML.Surface.SLYamlStream).isPrefixOf n && elimNames.contains n.getString!

def modOf (env : Environment) (n : Name) : Name :=
  match env.getModuleIdxFor? n with
  | some i => env.header.moduleNames[i.toNat]!
  | none => Name.anonymous

/-- This library and its tests, which is the population; everything else in the
    environment is Lean's own. -/
def inScope (env : Environment) (n : Name) : Bool :=
  let m := modOf env n
  (`L4YAML).isPrefixOf m || (`Tests).isPrefixOf m || m == `L4YAML

/-- **`value?` hides a theorem's proof unless `allowOpaque` is set**, and a walk
    that takes the default silently reads types only.  That is the whole
    measurement here, so it is spelled out rather than defaulted. -/
def rawRefs (env : Environment) (n : Name) (wantVal : Bool) : Array Name :=
  match env.find? n with
  | none => #[]
  | some ci =>
    let e := if wantVal then (ci.value? (allowOpaque := true)).getD (mkConst n)
             else ci.type
    e.getUsedConstants

/-- What THIS declaration uses: generated auxiliaries inlined, eliminators and
    constructors left standing. -/
partial def uses (env : Environment) (root : Name) (wantVal : Bool) :
    Std.HashSet Name := Id.run do
  let mut seen : Std.HashSet Name := {}
  let mut out : Std.HashSet Name := {}
  let mut todo : List Name := (rawRefs env root wantVal).toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if seen.contains n then continue
    seen := seen.insert n
    out := out.insert n
    if isAux n then
      todo := (rawRefs env n true).toList ++ (rawRefs env n false).toList ++ todo
  return out

/-- The four populations plus the closure they were read over. -/
structure Census where
  closureModules : Nat
  authored : Nat
  direct : Array Name
  stmt : Array Name
  elimUsers : Array Name
  trans : Array Name
  capstonesInT : Array Name
  /-- Every constant in scope — generated ones included — whose raw references
      reach an `SLYamlStream` eliminator.  A second, independent read of `R`. -/
  rawElim : Array Name
deriving Inhabited

def sorted (a : Array Name) : Array Name := a.qsort (·.toString < ·.toString)

/-- The value walk over the whole population, taken once.  It is the expensive
    half of the census — `uses` inlines generated auxiliaries and the
    accumulation's proof terms are large — so a second instrument in the same
    environment takes this map rather than rebuilding it;
    `Tests/Guards/Proofs/RepairChoice.lean` (DOCS item 240) reverses the same
    edges and computing them twice costs minutes rather than seconds. -/
def usesAll (env : Environment) :
    Array Name × Std.HashMap Name (Std.HashSet Name) := Id.run do
  let mut authored : Array Name := #[]
  for (n, _) in env.constants.toList do
    if inScope env n && isAuthored env n then authored := authored.push n
  let mut m : Std.HashMap Name (Std.HashSet Name) := {}
  for n in authored do
    m := m.insert n (uses env n true)
  return (authored, m)

/-- One environment pass.  `scripts/drop_sweep.py` calls this from an
    environment holding the whole tree; §2 calls it from this file's own,
    narrower closure, and the two agree. -/
def census (pre : Option (Array Name × Std.HashMap Name (Std.HashSet Name)) := none) :
    CoreM Census := do
  let env ← getEnv
  let (authored, usesVal) := pre.getD (usesAll env)
  let mut direct : Array Name := #[]
  let mut stmt : Array Name := #[]
  let mut elimUsers : Array Name := #[]
  for n in authored do
    let uv := usesVal.getD n {}
    let ut := uses env n false
    if uv.contains drop then direct := direct.push n
    if ut.contains drop then stmt := stmt.push n
    if uv.toList.any isStreamElim || ut.toList.any isStreamElim then
      elimUsers := elimUsers.push n
  let authoredSet : Std.HashSet Name := Std.HashSet.ofList authored.toList
  let mut rev : Std.HashMap Name (Array Name) := {}
  for n in authored do
    for m in (usesVal.getD n {}).toList do
      if authoredSet.contains m then rev := rev.insert m ((rev.getD m #[]).push n)
  let mut trans : Std.HashSet Name := {}
  let mut todo : List Name := direct.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if trans.contains n then continue
    trans := trans.insert n
    todo := (rev.getD n #[]).toList ++ todo
  let mut rawElim : Array Name := #[]
  for (n, _) in env.constants.toList do
    if !inScope env n then continue
    if ((rawRefs env n true) ++ (rawRefs env n false)).any isStreamElim then
      rawElim := rawElim.push n
  let closure := env.header.moduleNames.filter (fun m =>
    (`L4YAML).isPrefixOf m || (`Tests).isPrefixOf m || m == `L4YAML)
  return { closureModules := closure.size, authored := authored.size,
           direct := sorted direct, stmt := sorted stmt,
           elimUsers := sorted elimUsers, trans := sorted trans.toArray,
           capstonesInT := sorted ((L4YAML.capstoneDecls env).filter trans.contains),
           rawElim := sorted rawElim }

/-- The line every reader of this instrument compares against. -/
def render (c : Census) : String :=
  s!"D={c.direct.size} S={c.stmt.size} R={c.elimUsers.size} T={c.trans.size} \
capstonesInT={c.capstonesInT.size} rawElim={c.rawElim.size}"

/-! ## §1 The closure this file reads

Item 237's census read 109 of 230 modules before it imported the library root,
and reported a library.  This one pins its own closure first, and
`scripts/drop_sweep.py` re-runs the same `census` over every module in the tree
that has an olean — 858 composed in one environment, plus the 36 executable
entry points probed alone, because two root-namespace `main`s cannot share an
environment.  **The four counts are identical at every closure tried**; the
pins below are what makes that checkable rather than asserted. -/

/-- The modules of this library and its tests that this file's own imports
    reach: the library complete at 243, plus the two `Tests.Guards` modules that
    hold the Tests-side half of the first ring.

    243 on 2026-10-05, when the eleven modules of `L4YAML.Proofs.Serialization`
    joined the library (PR #1), imported by `L4YAML.lean` so the
    kernel-accurate hygiene gate reaches them.  Only the closure moved: the
    census, `direct`, `rawElim` and `trans` pins are unchanged, so the
    serialization package references the `scannerDrop` arm zero times.

    232 on 2026-10-02, when `Proofs.Parser.ParserScannableBase` joined the
    library — the `Scannable`-valued compose chain, kept in its own module
    because two `maxHeartbeats 4000000` `YamlValue` inductions do not elaborate
    in one.
    259 on 2026-10-23 (after `Serialization.EventsOf` and `RefLex`), when `Proofs.Production.Acceptance.Quoted` joined the
    library — the one-line quoted-scalar scanner converses. -/
def expectedClosure : Nat := 274  -- +1: `Proofs.Serialization.ParseCheckFrom` (S5 slice 1)

/-- `scripts/drop_sweep.py`'s reading, re-derivable in one command and pinned
    here so that a walk which starts from the wrong root disagrees with it
    loudly.  The 36 entry points hold 600 declarations between them and
    reference the arm zero times.  (602 on Lean v4.33.0: the count is every
    constant the module declares, generated and internal ones included, and
    v4.34.0 generates no `toCtorIdx` for an enum inductive — the two rows a
    per-module listing under both toolchains differs in are
    `Tests.DeclineReachCensus.Disp.toCtorIdx` and `Tests.SuiteRunner.Main`'s
    `Backend.toCtorIdx`, the two enums among the 36.)

    `readable` is the count that keeps the other numbers honest.  **A probe
    that fails contributes zero, and a zero is indistinguishable from a clean
    module**, so the sweep counts the readings it actually got and names every
    module it could not read.  Two failed when the counter was added, for
    reasons that have nothing in common: `Tests.QueryResults` does not reach
    `Lean.Elab.Command` transitively and the probe's own `run_cmd` would not
    elaborate, and `Tests.LimitTests.Runner` is a `lean_exe` that is not a
    DEFAULT target, so `lake build` never refreshed it and its olean was still
    the one Lean 4.32.0 wrote.  The sweep now imports the command elaborator
    and builds a target by name before giving up on it.

    One module in the tree stays UNMEASURED and the sweep says so:
    `Tests.ContentEqRefl` belongs to no Lake target at all, so nothing can
    elaborate it.  Reading its source finds no mention of the stream, which is
    a hint and not a check — item 237's own finding is that a statement can
    assert `InYamlLanguage` without naming it.

    **Re-pinned at DOCS item 299** (2026-10-20), where the gate battery ran the
    sweep for the first time since item 265 pinned 866: eighteen modules were
    added in between by work outside row 12 — the serialization semantics
    (`097b7a29`, `62cc64ad`: `Proofs/Serialization/*`, ten modules), the WFA
    twins (`f0081be0`, `5a1c0a24`: `Proofs/Parser/*WfaScannable*`,
    `ParserScannableBase`, `Guards/Proofs/AliasNodeRoute`), the deriving
    consumer (`92115689`: `Tests/DerivingConsumer`, whose `Runner` is the one
    new EXCLUDED module, a non-default target) and the schema proof
    (`78fab13e`: `Proofs/Schema/FlowIndicator`) — so the closure reads 883,
    imported 879, excluded 37 and `excludedDecls` 603.  Item 299 itself adds
    no module. -/
def expectedWide : String :=
  "closure=883 imported=879 excluded=37 readable=37 unreadable=0 \
excludedDecls=603 excludedDropRefs=0"

/-- **The four counts the WHOLE TREE reads, which are not the four this file's
    own `run_cmd` reads.**  `census` filters by `inScope`, which reads a
    declaration's MODULE — and a declaration being elaborated has none, so a
    census is blind to its own module.  It is equally blind to any module that
    does not import it.  `Tests/Guards/Proofs/DropFalsity.lean` (DOCS item 239)
    holds one exhibit that rides the arm on purpose, so the tree composed in
    one environment reads `T=27` where §2 reads `T=26`.  Both are pinned, and
    the difference is the instrument counting itself.
    `Tests/Guards/Proofs/RepairChoice.lean` (DOCS item 240),
    `Tests/Guards/Proofs/ProducerDerivation.lean` (DOCS item 241) and
    `Tests/Guards/Proofs/DispatchPrice.lean` (DOCS item 242) and
    `Tests/Guards/Proofs/ParkGapCensus.lean` (DOCS item 243) and
    `Tests/Guards/Proofs/ParkGapWidth.lean` (DOCS item 244) and
    `Tests/Guards/Proofs/ParkGapProduction.lean` (DOCS item 245) all join the
    tree without moving `T`: they reverse these edges, census the statements,
    refute a premise, derive the escape's CONNECTED form, read every site that
    spends it, measure how wide the gap at those sites is and read what the
    crossing lands in, and none of that builds the arm — items 242 through 245
    all pin `drop=false` for exactly that reason.  Item 243 reads `D`'s four
    proof terms under their binders rather than their statements, which is what
    makes `expectedDirect` below the population of a census rather than a list;
    item 244 reads the PARK's producer the same way, one ring outside `D`; and
    item 245 leaves proof terms altogether and censuses the grammar's own
    constructors.  `Tests/Guards/Proofs/ParkBill.lean` (DOCS item 263) joins on
    the same terms: it walks β.5's OTHER deletion, `PendingNode.pendingFlow`,
    and reads `Dp=9 Sp=0 Tp=31` beside this file's `T=26` — twelve declarations
    outside it, and the same `S=0` answer for the park as for the arm. -/
def expectedWideCensus : String :=
  "D=4 S=0 R=0 T=27 capstonesInT=2 rawElim=11"

/-! ## §2 The four counts -/

-- 2026-10-24 (B3 [66] col-0 threading): T 27 → 28 — `PendingNode.close_with_sslFrom`, the
-- `SSLCommentsFrom` twin of `close_with_ssl`, rides the drop through `dropClose` in its
-- `pendingFlow` arm only (the arm β.5 retires with the constructor).  D unchanged.
def expectedCensus : String :=
  "D=4 S=0 R=0 T=28 capstonesInT=2 rawElim=11"

/-- The first ring: two in the library, two in the instruments that exhibit the
    defect.  `stream_anything` is item 236's free-maker and item 235 restates it;
    both are `Tests` declarations that exist to show the arm is broken, so β.5
    deletes them rather than repairing them. -/
def expectedDirect : List Name :=
  [`L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl,
   `L4YAML.Proofs.StreamAccum.dropClose,
   `Tests.Guards.ColumnWalkPrice.stream_anything,
   `Tests.Guards.SuffixGapAudit.stream_anything]

/-- **Nothing in the tree case-splits on an `SLYamlStream`.**  `R=0` is one
    reading of that and `rawElim` is a second, independent one: every constant
    in scope that reaches an eliminator IS one of the eliminators.  The grammar
    is consumed by construction, never by destruction, which is why β.5 costs
    nothing on the case-split side. -/
def expectedRawElim : List Name :=
  [`L4YAML.Surface.SLYamlStream.below,
   `L4YAML.Surface.SLYamlStream.below.casesOn,
   `L4YAML.Surface.SLYamlStream.below.implicitContinue,
   `L4YAML.Surface.SLYamlStream.below.rec,
   `L4YAML.Surface.SLYamlStream.below.scannerDrop,
   `L4YAML.Surface.SLYamlStream.below.single,
   `L4YAML.Surface.SLYamlStream.below.suffixContinue,
   `L4YAML.Surface.SLYamlStream.brecOn,
   `L4YAML.Surface.SLYamlStream.casesOn,
   `L4YAML.Surface.SLYamlStream.rec,
   `L4YAML.Surface.SLYamlStream.recOn]

/-- The spine, in the order the proofs compose: the two construction sites, the
    five `PendingNode` closers, the four `accum_step_*`, the scanner loop, and
    then `scan_content_gives_stream_v2` — capstone 7.2, the lemma item 237 found
    spelling `InYamlLanguage` out — carrying it into `scan_strict`,
    `parse_strict` and the two Group 7 capstones.  Six of the 26 are the
    instruments themselves. -/
def expectedTrans : List Name :=
  [`L4YAML.Proofs.DocumentProduction.parse_strict_proof,
   `L4YAML.Proofs.DocumentProduction.scan_strict_proof,
   `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl,
   `L4YAML.Proofs.StreamAccum.PendingNode.close_with_sslFrom,
   `L4YAML.Proofs.StreamAccum.accum_block_pending,
   `L4YAML.Proofs.StreamAccum.accum_content_pending,
   `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
   `L4YAML.Proofs.StreamAccum.accum_step_block,
   `L4YAML.Proofs.StreamAccum.accum_step_content,
   `L4YAML.Proofs.StreamAccum.accum_step_flow,
   `L4YAML.Proofs.StreamAccum.accum_step_structural,
   `L4YAML.Proofs.StreamAccum.accum_structural_pending,
   `L4YAML.Proofs.StreamAccum.dropClose,
   `L4YAML.Proofs.StreamAccum.eof_pending,
   `L4YAML.Proofs.StreamAccum.preprocessing_eof_extends_stream,
   `L4YAML.Proofs.StreamAccum.scanLoop_grammar_prod,
   `L4YAML.Proofs.StreamAccum.scanNextToken_accum_step,
   `L4YAML.Proofs.StreamAccum.scanNextToken_accum_step_witness,
   `L4YAML.Proofs.StreamAccum.scanNextToken_none_stream,
   `L4YAML.Proofs.StreamAccum.scan_content_gives_stream_v2,
   `L4YAML.Surface.parse_strict,
   `L4YAML.Surface.scan_strict,
   `Tests.Guards.ColumnWalkPrice.stream_anything,
   `Tests.Guards.ColumnWalkPrice.stream_colLaw_refuted,
   `Tests.Guards.ColumnWalkPrice.stream_span_refuted,
   `Tests.Guards.ColumnWalkPrice.stream_suffix_refuted,
   `Tests.Guards.SuffixGapAudit.inYamlLanguage_everything,
   `Tests.Guards.SuffixGapAudit.stream_anything]

/-- The two Group 7 capstones β.5 reaches.  Item 237 found both FREE; this file
    finds both PROVED through the arm as well, which is a stronger statement
    about the same two declarations and does not follow from the first. -/
def expectedCapstones : List Name :=
  [`L4YAML.Proofs.DocumentProduction.parse_strict_proof,
   `L4YAML.Proofs.DocumentProduction.scan_strict_proof]

/-! Every pin above, checked against one environment pass.  Perturb any one of
them and this file stops building. -/

run_cmd Lean.Elab.Command.liftCoreM do
  let c ← census
  let cmp (what : String) (got exp : String) : CoreM Unit :=
    unless got == exp do
      throwError "{what} moved:\n  got      {got}\n  expected {exp}"
  let cmpN (what : String) (got : Array Name) (exp : List Name) : CoreM Unit :=
    cmp what (String.intercalate " " (got.toList.map toString))
             (String.intercalate " " (exp.map toString))
  cmp "closure" s!"closure={c.closureModules}" s!"closure={expectedClosure}"
  cmp "census" (render c) expectedCensus
  cmpN "direct" c.direct expectedDirect
  cmpN "rawElim" c.rawElim expectedRawElim
  cmpN "trans" c.trans expectedTrans
  cmpN "capstones" c.capstonesInT expectedCapstones
  -- The recursor's own type names the arm.  This is why the walk stops at
  -- eliminators, and it is the one line that would silently merge `R` into `D`.
  unless (rawRefs (← getEnv) `L4YAML.Surface.SLYamlStream.rec false).any (· == drop) do
    throwError "the recursor's type no longer names the arm; the walk's reason \
for treating eliminators as terminal is gone and its `D` may now be an `R`"

/-! ## §3 What the numbers rest on -/

/-- **Definitional proof irrelevance** — the reason `T` is a ceiling and not a
    bill.  Two proofs of the same proposition are equal by `rfl`, so a consumer
    of `dropClose` sees its STATEMENT and nothing else; replacing its proof
    under an unchanged statement reaches no one. -/
example (p : Prop) (h₁ h₂ : p) : h₁ = h₂ := rfl

open L4YAML.Surface in
/-- **`dropClose` is the arm restated.**  Its conclusion names a target its
    premises never reach, so it is not a lemma whose proof β.5 redoes — it is
    one whose statement goes with the constructor. -/
example (sp_start sp_x : SurfPos) (h_stream : SLYamlStream sp_start sp_x) :
    ∀ sp_e sp_m, SSLComments sp_e sp_m → SLYamlStream sp_start sp_m :=
  fun _ sp_m h_ssl => SLYamlStream.scannerDrop sp_start sp_x _ sp_m h_stream h_ssl

/-! ## §4 What this file does NOT establish and what it does not carry

The axiom probe reads three theorems here.  All three are `structure Census`'s
generated `mk.injEq`, `mk.inj` and `mk.sizeOf_spec`; this file authors none,
because its exhibits are `example`s (item 229's rule) and its claim is carried
by the pins rather than by a statement it could get wrong twice.

It does not establish that the 24 behind the first ring must be edited.  They
must be edited exactly when a statement below them changes, and only two
statements are candidates — `dropClose`, which goes, and
`PendingNode.close_with_ssl`, which may not.  Deciding the second is β.5's
work, not a census's; what this file fixes is that the question is about two
declarations rather than about twenty-six. -/

end Tests.Guards.DropDependents
