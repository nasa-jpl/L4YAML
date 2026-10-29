/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.DropDependents

/-!
# β.5's other half, and what a closure over-prices (DOCS item 263)

Row 12 names β.5 *"retire `pendingFlow`, delete `scannerDrop`"* — **two**
deletions.  Every instrument in this row measured the second one.  Item 238
walked `SLYamlStream.scannerDrop`'s dependents and read `D=4 S=0 R=0 T=26`, and
twenty-six less the two restatements is the "twenty-four reproofs" the plan has
carried since.  `PendingNode.pendingFlow`'s own dependents have never been
walked, so the bill names one of β.5's two halves.

This file walks the other one, over the same environment pass and with the same
populations, and then does what the arm's census could not do for itself: it
says how much of its own answer is a CEILING.

## The ceiling, restated for the park

Item 238's rule holds here too.  **A consumer depends on its supplier's TYPE,
not on its proof.**  So of the park's populations only `Sp` — the declarations
whose STATEMENT names the constructor — can force work above them.  `Dp` breaks
in its own proofs and stops there, and `Tp` prices a rebuild rather than a
rewrite.  `Tp` is reported because a closure is what the plan has been quoting,
and the honest way to retire that habit is to print the number beside the one
that replaces it.

## What the flip is for, and why it is not optional here

`scripts/flip_beta5.py` applies β.5's actual edit — both deletions and
`dropClose` with them — and then drives the build to a FIXPOINT: it replaces
each broken declaration's proof with `sorry`, neutralizes each top-level census
whose pins the deletion re-reads, and rebuilds until the tree is clean.  That
is what reads the truth.  Every flip before it printed

    LOWER BOUND — the build stopped at the first failing module

and both construction sites live in a module the library root imports, so until
that gate ran, not one of the twenty-four had ever been elaborated against a
post-β.5 tree.  The two instruments bracket each other exactly as item 240's
pair did:

    walk (a rebuild's price)   ⊇   truth (the fixpoint)   ⊇   any flip that stops

and §2 pins the bracket, so a refinement that moves one end without the other
disagrees loudly.
-/

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab

namespace Tests.Guards.ParkBill

open Tests.Guards.DropDependents (uses usesAll sorted)

/-- The park β.5 retires. -/
def park : Name := `L4YAML.Proofs.StreamAccum.PendingNode.pendingFlow

/-- The arm β.5 deletes — item 238's target.  Both halves of β.5 are read from
    ONE environment pass here so the two cannot drift apart, and §2 pins that
    this is still the constant that file walks. -/
def arm : Name := `L4YAML.Surface.SLYamlStream.scannerDrop

/-- One deletion's populations, plus the two overlaps that say how much of
    β.5's bill the arm's census never counted. -/
structure Bill where
  closureModules : Nat
  authored : Nat
  /-- Names the park in its PROOF TERM: builders and case splits together.
      Item 240 established that no syntactic reading separates them — `cases`
      on an indexed family builds the constructor terms of the arms its index
      rules out as much as of the ones it reaches. -/
  direct : Array Name
  /-- Names the park in its TYPE.  **The only population that can force work
      above itself**, and the only one a `sorry` cannot absorb. -/
  stmt : Array Name
  /-- `direct ∪ stmt` closed upward through proof terms — a rebuild's price. -/
  trans : Array Name
  /-- Item 238's `T`, re-derived in this same pass. -/
  armTrans : Array Name
  shared : Array Name
  /-- `trans \ armTrans`: what β.5 reaches that the arm's closure never counted. -/
  extra : Array Name
  capstonesInTrans : Array Name
deriving Inhabited

/-- One environment pass, both halves of β.5. -/
def bill : CoreM Bill := do
  let env ← getEnv
  let pre := usesAll env
  let (authored, usesVal) := pre
  let mut direct : Array Name := #[]
  let mut stmt : Array Name := #[]
  for n in authored do
    if (usesVal.getD n {}).contains park then direct := direct.push n
    if (uses env n false).contains park then stmt := stmt.push n
  let authoredSet : Std.HashSet Name := Std.HashSet.ofList authored.toList
  let mut rev : Std.HashMap Name (Array Name) := {}
  for n in authored do
    for m in (usesVal.getD n {}).toList do
      if authoredSet.contains m then rev := rev.insert m ((rev.getD m #[]).push n)
  let mut trans : Std.HashSet Name := {}
  let mut todo : List Name := direct.toList ++ stmt.toList
  while !todo.isEmpty do
    let n := todo.head!
    todo := todo.tail!
    if trans.contains n then continue
    trans := trans.insert n
    todo := (rev.getD n #[]).toList ++ todo
  let armCensus ← Tests.Guards.DropDependents.census (some pre)
  let armSet : Std.HashSet Name := Std.HashSet.ofList armCensus.trans.toList
  let transArr := trans.toArray
  let closure := env.header.moduleNames.filter (fun m =>
    (`L4YAML).isPrefixOf m || (`Tests).isPrefixOf m || m == `L4YAML)
  return { closureModules := closure.size, authored := authored.size,
           direct := sorted direct, stmt := sorted stmt,
           trans := sorted transArr,
           armTrans := armCensus.trans,
           shared := sorted (transArr.filter armSet.contains),
           extra := sorted (transArr.filter (fun n => !armSet.contains n)),
           capstonesInTrans := sorted
             ((L4YAML.capstoneDecls env).filter trans.contains) }

/-- The line every reader of this instrument compares against. -/
def render (b : Bill) : String :=
  s!"Dp={b.direct.size} Sp={b.stmt.size} Tp={b.trans.size} \
T={b.armTrans.size} shared={b.shared.size} extra={b.extra.size} \
capstonesInTp={b.capstonesInTrans.size}"

/-! ## §1 The park's bill -/

/-- The closure this file reads.  Pinned first, as item 237's lesson requires:
    a census that reports a library it did not import reports a library.

    246 on 2026-10-05, when the eleven modules of
    `L4YAML.Proofs.Serialization` joined the library (PR #1), imported by
    `L4YAML.lean` so the kernel-accurate hygiene gate reaches them.  Only the
    closure moved; every bill pinned below is unchanged.

    235 on 2026-10-02, when `Proofs.Parser.ParserScannableBase` joined the
    library — the `Scannable`-valued compose chain, in its own module because
    two `maxHeartbeats 4000000` `YamlValue` inductions do not elaborate in
    one.
    260 on 2026-10-23 (after `Serialization.EventsOf` and `RefLex`), when `Proofs.Production.Acceptance.Quoted` joined the
    library — the one-line quoted-scalar scanner converses. -/
def expectedClosure : Nat := 275  -- +1: `Proofs.Serialization.ParseCheckFrom` (S5 slice 1)

/-- The park's populations beside the arm's, from one pass. -/
-- 2026-10-24 (B3 [66] col-0 threading): see the dated note on `expectedDirect` below.
def expectedBill : String :=
  "Dp=11 Sp=0 Tp=36 T=28 shared=21 extra=15 capstonesInTp=2"

/-- Names the park in a PROOF TERM — builders and case splits together, which
    no syntactic reading separates (item 240).  **Seven of the nine break and
    two do not**, and the two are the ones item 240 already named:
    `close_with_ssl` case-splits on the park and the retirement deletes its arm
    WITH the constructor, and `accum_structural_pending` splits on the
    `true`-indexed park where `pendingFlow` cannot occur.  So the bracket
    `walk 9 ⊇ truth 7` is not a margin of error — it is two declarations, named. -/
-- 2026-10-24 (B3 [66] col-0 threading): Dp 9 → 11, Tp 34 → 36 — `PendingNode.close_with_sslFrom`
-- (the `SSLCommentsFrom` twin of `close_with_ssl`) and `PendingNode.nil_gate_of_allowDirectives`
-- (reads `pendingFlow`'s gate) name the park in their proof terms.
def expectedDirect : List Name :=
  [`L4YAML.Proofs.StreamAccum.PendingNode.arm_tight_or_col,
   `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl,
   `L4YAML.Proofs.StreamAccum.PendingNode.close_with_sslFrom,
   `L4YAML.Proofs.StreamAccum.PendingNode.dirRoute,
   `L4YAML.Proofs.StreamAccum.PendingNode.nic0,
   `L4YAML.Proofs.StreamAccum.PendingNode.nil_gate_of_allowDirectives,
   `L4YAML.Proofs.StreamAccum.accum_block_pending,
   `L4YAML.Proofs.StreamAccum.accum_content_pending,
   `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
   `L4YAML.Proofs.StreamAccum.accum_structural_pending,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred]

/-- Names the park in a TYPE.  The only population a `sorry` cannot absorb —
    and it is **EMPTY**, the exact twin of item 238's `S=0` for the arm.  Both
    halves of β.5 are invisible to every statement in this closure, and the
    fixpoint reads the same zero over the whole tree (`restated=0`), which is
    what makes this one a reading rather than a limit of the closure. -/
def expectedStmt : List Name := []

/-! ## §2 The bracket, and the three numbers it separates

~~`Tp=31`~~ `Tp=33` against `T=26`: ~~**twelve**~~ **fourteen declarations β.5
reaches that the arm's closure never counted** — `PendingNode.arm_or_col` and
the three park lemmas above, the four `accum_block_on_*`, the four
`block_dispatch_deferred*`, and (DOCS item 287) `colon_fires_implicit_key` and
`colon_fires_props_key`, which apply the inline wrapper themselves.
Nineteen of item 238's twenty-six are shared.  So the bill stated as a closure
is ~~**thirty-eight**~~ **forty**, not twenty-six, and it was never twenty-six
because it was only ever half of β.5.

**And thirty-eight is not what β.5 costs.**  The fixpoint elaborates the whole
tree against the post-β.5 sources and reads

    sorried=13  restated=0  deleted=3  pins=37

— thirteen proofs, of which seven are the library's (all in `StreamAccum.lean`)
and six are Tests-side; ONE statement, `dropClose`, which goes with the arm;
and not one statement anywhere that must change, which is `Sp=0` read a second
way and over the whole tree rather than over this file's closure.

The three numbers are three different questions and only the last is the bill:

| reading | what it counts | value |
|---|---|---|
| `Tp ∪ T` | what a REBUILD touches | ~~38~~ **40** |
| `Dp` (+ item 238's `D`) | what NAMES a deletion | 9 + 4 |
| the fixpoint | what stops ELABORATING | **13 proofs + 1 statement** |

**The closure over-prices by a factor of three**, and every flip before the
fixpoint under-priced by stopping at the first failing module.  That is why
both instruments are kept: neither one alone is the number.

## What this file's closure is, and what it is not

Two hundred and thirty-four modules — item 238's 233 and this file.
`DropFalsity`, `ParkGapCensus` and the rest of the guard tree are outside it,
so `Dp` is a reading of the library plus the two Tests modules that hold the
arm's first ring, exactly as item 238's census was.  **The whole-tree reading
is the fixpoint's**, and the two agree where they overlap: the walk's nine
contains the fixpoint's seven, and the two it adds are named above.
-/

/-- The fixpoint's own reading.  Nothing in Lean can re-derive it — it is a
    property of a source tree that does not exist — so the pin is checked from
    the other side: `scripts/flip_beta5.py` reads this literal out of this file
    and compares its own summary line against it, printing `FIX-PIN agrees`.  A
    pin checked against itself is an empty check (§9). -/
def expectedFixpoint : String :=
  "rounds=23 clean=1 sorried=13 restated=0 deleted=3 refused=0 pins=37 waves=[7,3,2,1,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0,0] gone=1 carried=21 free=4"

/-- **The same edit with the DEAD BRANCHES deleted rather than sorried**
    (item 264).  The fixpoint above keeps every broken statement and loses only
    its proof, so it can say a proof breaks and never say what repairing it
    costs.  `scripts/beta5_arms.py` makes β.5's deletions and then deletes the
    five dead `| pendingFlow` arms for real, and reads the residue:

    * `control` re-derives the seven in the same run, so `dead` is a delta of
      this run rather than of item 263's;
    * ~~`dead=5`~~ `dead=6` — five of the seven are a case arm and nothing else,
      and one of the five (`accum_content_pending`'s) carried an application of
      the escape with it, so a class of `block_dispatch_deferred`'s domain
      empties with the constructor.  The sixth is `accum_flow_open_depth0`, three
      dead blocks since DOCS item 285: the arm, `have opaque_resume` (the arm is
      its only consumer) and `have drop_ride` (`opaque_resume` is its only
      spender, since the three live arms take `slot_ride`);
    * what is LEFT is ~~two errors of one line each.  `accum_flow_open_depth0`
      keeps `have drop_ride`, where `dropClose` is spent and which three LIVE
      arms take (`ScannerFlowOpenUnderRun` §4 prices it), and~~ ONE error:
      `block_dispatch_deferred` is the escape, whose body IS the constructor.
      Its three wrappers' eight applications, in three live declarations, are
      what the escape's deletion still has to route or refute (DOCS item 285,
      step 12.3).

    Checked from the other side, like `expectedFixpoint`: the script reads this
    literal and prints `ARM-PIN agrees`. -/
def expectedArms : String :=
  "control=7 arms=1 dead=6 left=[block_dispatch_deferred]"

/-! ## §3 Every pin above, checked against one environment pass. -/

run_cmd Lean.Elab.Command.liftCoreM do
  let b ← bill
  let cmp (what : String) (got exp : String) : CoreM Unit :=
    unless got == exp do
      throwError "{what} moved:\n  got      {got}\n  expected {exp}"
  let cmpN (what : String) (got : Array Name) (exp : List Name) : CoreM Unit :=
    cmp what (String.intercalate " " (got.toList.map toString))
             (String.intercalate " " (exp.map toString))
  cmp "closure" s!"closure={b.closureModules}" s!"closure={expectedClosure}"
  cmp "bill" (render b) expectedBill
  cmpN "Dp" b.direct expectedDirect
  cmpN "Sp" b.stmt expectedStmt
  -- Both halves must come out of one pass, and the arm's half must still be
  -- the arm's: a rename of item 238's target would otherwise silently make
  -- `shared` and `extra` a comparison against something else.
  unless Tests.Guards.DropDependents.drop == arm do
    throwError "item 238's census no longer walks {arm}; `shared` and `extra` \
compare this file's half against a different deletion"
  Lean.logInfo (render b)
  for n in b.extra do Lean.logInfo s!"extra {n}"

/-! ## §4 What this file does NOT establish

It prices a REBUILD.  Whether any of the declarations it counts can be reproved
with its statement intact is a proof question, and `Tp` has nothing to say about
it — that is the same boundary item 238 drew around its twenty-six and item 237
around its fifteen.  The fixpoint does not decide it either: a declaration whose
proof was replaced by `sorry` may be FALSE in the post-β.5 model, which item 239
proved for `PendingNode.close_with_ssl` after item 238's graph had called it
reprovable.  Both instruments price the BUILD. -/


/-! ## §5 Who HOLDS the gates the under-run dies at (DOCS item 268)

§2's fixpoint prices the rebuild; this prices a REACH.  Item 267 built the
carrier that fires the two gates a depth-0 flow open's under-run dies at, and
the question its wiring turns on is which declaration holds the hypothesis the
firing contradicts.

There are four checks — §8.1's floor and §9.2's dangling run, each with a
mid-stream and an end-of-input twin — and `ScannerFlowOpenUnderRun` §8 reads the
same ninety/fifty-four partition of the 144 at every one of them.  This is the
proof-side half: for each check, the constants of the ACCUMULATION whose TYPE
mentions it, which is what it means to hold the check's success as a premise.

The count is taken in the environment and not over the text.  A grep sees the
name; it does not see whether the mention is a binder of the statement or a step
of the proof, and those are the two halves this census has to separate: a check
whose success is derived inside a proof and spent on the next line reads, to a
grep of that file, exactly like a binder of the statement.

**The reading.**  §9.2 is held twenty-one times mid-stream and five at the end
of input; §8.1 sixteen and four.  The two run together: every accumulation
declaration that holds §9.2's success in order to read a park's FACE holds
§8.1's beside it, and both faces reach the close as premises of
`pendingContent`'s `h_closable` (item 275).

**What the gap is.**  Seven declarations hold §9.2's mid-stream check and not
§8.1's, and two hold §9.2's end-of-input check and not §8.1's; one holds each
of §8.1's and neither of §9.2's, which is what makes the columns 22/16 and 5/4
rather than 22/15 and 5/3.  Those last two are the bridges that read a silence
off a success — `underIndented_none_of_check` and `underIndented_none_of_eof`,
whose §9.2 twins `dangling_none_of_check` and `dangling_none_of_eof` account
for one of the six and one of the two.  The rest is the REFUTATION family:
`propsPark_open_gate`, `propsPark_stale_dangling`, `propsPark_dangling_of_body`
and `propsPark_dangling_of_prop` mid-stream with `danglingPark_refutes_landing`
beside them, and `danglingPark_refutes_eof` at the end of input.  Each reads the
dangling run in order to REFUTE a landing, and §8.1's floor has no twin for
that use, so the gap is a difference in what the two verdicts are FOR rather
than a rail left unbuilt.  The seventh is item 284's `slotRun_of_dn`, which
reads §9.2's silence to OPEN the props park's slot face at the depth-0 open —
again a use §8.1's floor has no twin for.

**And these counts are this theorem's, not the environment's**: the same four
names are held in the emitter-scannability chain too, §8.1's two checks eleven
and fifteen times there.  A census that reported only the first four numbers
could not tell a check nothing holds from a check nothing mentions, and §9 is
that an empty check is not a check. -/

def gateChecks : List (String × Name) :=
  [("dn/mid", `L4YAML.Scanner.scanNextToken_checkDanglingNode),
   ("dn/eof", `L4YAML.Scanner.scanLoop_checkDanglingNode),
   ("fv/mid", `L4YAML.Scanner.scanNextToken_checkFlowValueIndent),
   ("fv/eof", `L4YAML.Scanner.scanLoop_checkFlowValueIndent)]

/-- The accumulation's own namespace: the chain `grammar_completeness` drives. -/
def accumNs : Name := `L4YAML.Proofs.StreamAccum

/-- 21 → 22 on 2026-10-18 (item 284) by ONE holder, `slotRun_of_dn`; with this
    item's 49 new declarations excluded the census reads 21 again, so no other
    holder moved. -/
def expectedGateHolders : String :=
  "dn/mid=22 dn/eof=5 fv/mid=16 fv/eof=4 | \
elsewhere dn/mid=9 dn/eof=14 fv/mid=11 fv/eof=15"

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftCoreM do
  let env ← Lean.getEnv
  let mut here : List String := []
  let mut away : List String := []
  for (tag, g) in gateChecks do
    -- A renamed or deleted check would zero every count below it silently,
    -- which is the phantom item 265 found in the prose and item 266 found one
    -- production over.  So the name is resolved before it is counted.
    if (env.find? g).isNone then
      throwError "the gate {g} resolves to no constant; the census below would \
read zero for a reason that is not a reading"
    let mut h := 0
    let mut a := 0
    for (n, _) in env.constants.toList do
      if n == g then continue
      unless Tests.Guards.DropDependents.isAuthored env n do continue
      unless (uses env n false).contains g do continue
      if accumNs.isPrefixOf n then h := h + 1 else a := a + 1
    here := here ++ [s!"{tag}={h}"]
    away := away ++ [s!"{tag}={a}"]
  let got := String.intercalate " " here ++ " | elsewhere "
    ++ String.intercalate " " away
  unless got == expectedGateHolders do
    throwError "gate holders moved:\n  got      {got}\n  expected \
{expectedGateHolders}"
  Lean.logInfo got

end Tests.Guards.ParkBill
