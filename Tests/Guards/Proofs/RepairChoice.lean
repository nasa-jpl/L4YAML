/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Tests.Guards.Proofs.DropFalsity

/-!
# What a changed SUPPLIER propagates (DOCS item 240)

Item 238 measured what a deleted CONSTRUCTOR propagates and found `S=0`: no
consumer's STATEMENT names `SLYamlStream.scannerDrop`, so nothing above it
breaks on the deletion alone.  A consumer depends on its supplier's TYPE, and
proof irrelevance makes that exact.  β.5's repair, though, does not travel that
edge.  Item 239 proved `PendingNode.close_with_ssl` FALSE in the environment
that deletes the arm and keeps `PendingNode.pendingFlow`, so β.5 must change a
SUPPLIER'S STATEMENT — and what a changed statement propagates is a different
question, asked here.

## The number is a CHOICE, and this file measures the choice rather than the number

There are three repairs, and they are not variants of one edit:

| repair | the edit | `close_with_ssl`'s TYPE | the flip breaks |
|---|---|---|---|
| **weak** | `close_with_ssl` gains `(h_scan : SLYamlStream sp_start sp_scan)` and its flow arm closes with it | **CHANGES** | **5** |
| **field** | `pendingFlow` gains the same connection as its LAST field | unchanged | **1** |
| **retire** | `pendingFlow` deleted, docstring and arm together | unchanged | **7** |

`scripts/flip_supplier.py` runs all three for real, and a fourth end threads
the `field` repair one level to measure its second wave (DOCS item 241).
Each end leaves a well-typed, DROP-FREE supplier behind, and each prints
`REPAIRED errors=0` so that "the repair elaborates" is a reading and not a
silence.  **The three counts travel three different edges and are not a
ratio.**

**Only the weak repair changes a consumer's TYPE, and it changes nineteen of
them.**  §2 walks `close_with_ssl`'s reverse closure: 19 declarations in eight
rings, ending at both of the capstones the arm reaches and at
`L4YAML.Surface.parse_strict` / `scan_strict`.  Every one of the 19 is inside
item 238's transitive set — `thread \ T` is EMPTY — so the thread does not add
a reproof to β.5's bill; it decides how many of the bill's items are
restatements rather than reproofs.  The answer to item 239's question is
therefore **19 under the weak repair and 0 under the other two**.

That question is about `close_with_ssl`'s consumers, so the zero is exact and
narrow.  **It is not a claim that the other two repairs change no statements.**
The `field` end moves the connection to the park's PRODUCER, which cannot
derive it from the correspondence it holds, so a premise is threaded there
instead and the producer's own closure is ~~eighteen~~ **twenty** declarations
(DOCS item 287: the two `:` consumers apply the escape's inline wrapper
themselves) — ~~seven~~ **nine** of them outside item 238's set, which the weak
repair never leaves:
`Tests/Guards/Proofs/ProducerDerivation.lean` (DOCS item 241).

## Why the thread does not stop before the top

§1 proves the two halves that make the weak repair a RELOCATION rather than a
discharge.  `nd_ssl_extend` is the repaired flow arm in the post-β.5 model: a
stream reaching `sp_scan` closes the park across `[79] s-l-comments` with no
escape.  `park_gives_no_scan` refutes the premise's other source: the park
cannot produce that stream, so it has to come from the consumer.

§3 then asks each of the 19 whether it already holds one.  Seven carry a
`PendingNode` hypothesis at all, and **none of the seven carries a stream to
that park's scan position** — so the premise has nowhere to land short of the
top.  The other twelve do not mention a park, which is a stronger form of the
same answer.  This is a census of what the statements HOLD; whether some
statement could DERIVE the datum from its other premises is not decided here,
and §1 decides it only for the park.

## Where this meets item 239

Ten of the twenty-six conclude at `chars = []`, and the suffix law is silent
about such a target because `[]` is a suffix of every input — which is why item
239 could refute six of the twenty-six and not decide the other twenty.  **Nine
of those ten are on this thread.**  The statements no law can force to change
are exactly the ones a premise would have to travel through, so the two
measurements meet at one population rather than overlapping by accident.  §4
pins `empty=10 onThread=9`; the tenth is `inYamlLanguage_everything`, which no
proof in the library derives through the park.

## Which instrument dominates depends on the edge

Item 238 found the environment walk strictly dominating the flip, and for a
constructor's DELETION that still holds.  For its ARMS the ordering inverts:
the walk cannot answer, and §4 pins why.

* the walk reads **10** declarations naming `pendingFlow` in a proof term;
* the flip reports **7**.

Three names differ and each for its own reason.  `close_with_ssl` case-splits
on the park and the `retire` repair deletes its arm with the constructor, so it
does not break.  `accum_structural_pending` case-splits on the `true`-indexed
park, where `pendingFlow` cannot occur, and the flip shows it SURVIVES the
deletion.  `Tests.Guards.DropFalsity.flowPark` builds the park for real and
would break; the flip never sees it, because the build stops at the first
failing module and that module is `StreamAccum`.

**Two refinements of the walk were tried and both read 10.**  Reading raw
references one step, with no generated auxiliary inlined, reads 10; counting
the park's largest application arity reads 8 — a FULL application — for all
ten.  A case split on an indexed family builds its own constructor terms, for
the impossible arms as much as for the reachable ones, so no syntactic reading
of a proof term separates a builder from a case-splitter.  That is item 238's
`SLYamlStream.rec` lesson one level down, and it is why the flip is not
optional here.  §4 pins all three readings at 10 so that a future refinement
which DOES separate them disagrees with this file loudly.
-/

set_option autoImplicit false

open Lean Lean.Meta Lean.Elab

namespace Tests.Guards.RepairChoice

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PreprocessProduction
open Tests.Guards.DropFalsity (StreamND nd_suffix nd_refl flowPark sc0 classifyDecl)
open Tests.Guards.DropDependents (usesAll rawRefs census sorted)

/-! ## §1 The premise the weak repair adds, and where it cannot come from -/

/-- **The repaired flow arm, in the post-β.5 model.**  `close_with_ssl`'s
    `pendingFlow` case is the one place in the library that spends the escape
    on a park; given a stream that already reaches `sp_scan`, the case closes
    through `[202] l-document-prefix`'s comment alternative and needs no
    escape.  This is `ssl_comments_extend_stream`'s proof, transported to the
    relation β.5 leaves behind — so the weak repair is a repair, not a hope. -/
lemma nd_ssl_extend (a b c : SurfPos) (h : StreamND a b) (h_ssl : SSLComments b c)
    (hcol : b.col = 0) :
    StreamND a c :=
  StreamND.implicitContinue a b c c c h
    (GStar.cons b c c
      (SLDocumentPrefix.comments b c (SSLComments_to_GStar b c h_ssl hcol))
      (GStar.nil _))
    (GOpt.none _) (GStar.nil _)

/-- **And the park cannot supply it.**  The premise `nd_ssl_extend` consumes is
    not derivable from `PendingNode sc false sp_start sp_block sp_scan` plus a
    stream to `sp_block`: item 239's witness parks at `⟨['a'], 0⟩` with the
    scanner at `⟨['b','b','b'], 0⟩`, and the model's suffix law refutes the
    conclusion.  So the weak repair RELOCATES one obligation from the supplier
    to its consumers; §3 measures where it lands. -/
lemma park_gives_no_scan :
    ¬ (∀ (sc : ScannerState) (a b c : SurfPos),
        PendingNode sc false a b c → StreamND a b → StreamND a c) := by
  intro h
  have := (nd_suffix
    (h sc0 ⟨['a'], 0⟩ ⟨['a'], 0⟩ ⟨['b','b','b'], 0⟩ flowPark (nd_refl _))).length_le
  simp at this

/-! ## §2 The thread: the supplier's reverse closure -/

/-- The supplier whose statement β.5 changes. -/
def supplier : Name := `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl

/-- The park's sole producer — where the `field` repair's obligation lands. -/
def producer : Name := `L4YAML.Proofs.StreamAccum.block_dispatch_deferred

/-- The park itself. -/
def park : Name := `L4YAML.Proofs.StreamAccum.PendingNode.pendingFlow

/-- One-step reverse edges over the authored, in-scope population — item 238's
    forward walk with its arrows turned around.  It takes that walk's own map
    rather than rebuilding it: `uses … true` inlines generated auxiliaries over
    ten thousand declarations, and a second pass in the same environment costs
    minutes. -/
def revEdges (authored : Array Name)
    (usesVal : Std.HashMap Name (Std.HashSet Name)) :
    Std.HashMap Name (Array Name) := Id.run do
  let aset : Std.HashSet Name := Std.HashSet.ofList authored.toList
  let mut rev : Std.HashMap Name (Array Name) := {}
  for n in authored do
    for m in (usesVal.getD n {}).toList do
      if aset.contains m then rev := rev.insert m ((rev.getD m #[]).push n)
  return rev

/-- The rings of the reverse closure, nearest first.  A ring is what has to be
    touched before the next one can be. -/
def rings (rev : Std.HashMap Name (Array Name)) (root : Name) :
    Array (Array Name) := Id.run do
  let mut seen : Std.HashSet Name := Std.HashSet.emptyWithCapacity 0
  seen := seen.insert root
  let mut out : Array (Array Name) := #[]
  let mut frontier : Array Name := #[root]
  while !frontier.isEmpty do
    let mut nxt : Array Name := #[]
    for n in frontier do
      for p in rev.getD n #[] do
        if !seen.contains p then
          seen := seen.insert p
          nxt := nxt.push p
    if nxt.isEmpty then break
    out := out.push (sorted nxt)
    frontier := nxt
  return out

def thread (rev : Std.HashMap Name (Array Name)) (root : Name) : Array Name :=
  (rings rev root).foldl (fun a r => a ++ r) #[]

/-! ## §3 The discriminator: which of them already hold the premise -/

/-- Does a statement carry a stream to the scan position of a park it also
    carries?  A consumer that does can pay the weak repair's premise out of
    what it already has; one that cannot must GROW a premise, which is a
    change to its own statement.

    Reported as a triple so the denominator is visible: a declaration with no
    park hypothesis scores `covered = false` for a reason that has nothing to
    do with the repair, and merging the two would report a rate over the wrong
    population. -/
def holdsScanStream (n : Name) : MetaM (Nat × Nat × Bool) := do
  let some ci := (← getEnv).find? n | return (0, 0, false)
  forallTelescope ci.type fun xs _ => do
    let mut scans : Array Expr := #[]
    let mut streams : Array Expr := #[]
    for x in xs do
      let t ← inferType x
      if t.isAppOfArity ``PendingNode 5 then scans := scans.push t.appArg!
      if t.isAppOfArity ``SLYamlStream 2 then streams := streams.push t.appArg!
    return (scans.size, streams.size,
      scans.any fun a => streams.any fun b => a == b)

/-! ## §4 The pins -/

/-- The thread, and the producer's own.  `shared` is the eleven declarations
    both repairs reach however the repair is spelled. -/
def expectedThread : String :=
  "thread=20 prodThread=21 shared=12 capstones=2 rings=8"

/-- The first ring: the five library consumers item 238 named, and item 239's
    own exhibit, which rides the arm on purpose and goes with it. -/
def expectedRing1 : List Name :=
  [`L4YAML.Proofs.StreamAccum.accum_block_pending,
   `L4YAML.Proofs.StreamAccum.accum_content_pending,
   `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
   `L4YAML.Proofs.StreamAccum.accum_structural_pending,
   `L4YAML.Proofs.StreamAccum.eof_pending,
   `Tests.Guards.DropFalsity.close_with_ssl_reaches]

/-- **Nowhere for the premise to land.**  Seven of the nineteen carry a park at
    all, and none of the seven carries a stream to its scan position. -/
def expectedDiscriminator : String := "withPark=7 covered=0 total=20"

/-- **The thread adds nothing to β.5's bill.**  Every declaration the weak
    repair's statement change travels through is already one of the
    twenty-six item 238 counted, so the choice of repair moves items between
    *restated* and *reproved* without moving the total. -/
def expectedInT : String := "threadInT=20 outsideT=0"

/-- The walk's reading of the park's users — the upper bracket on what the
    `retire` repair breaks. -/
def expectedParkUsers : List Name :=
  [`L4YAML.Proofs.StreamAccum.PendingNode.arm_tight_or_col,
   `L4YAML.Proofs.StreamAccum.PendingNode.close_with_ssl,
   `L4YAML.Proofs.StreamAccum.PendingNode.dirRoute,
   `L4YAML.Proofs.StreamAccum.PendingNode.nic0,
   `L4YAML.Proofs.StreamAccum.accum_block_pending,
   `L4YAML.Proofs.StreamAccum.accum_content_pending,
   `L4YAML.Proofs.StreamAccum.accum_flow_open_depth0,
   `L4YAML.Proofs.StreamAccum.accum_structural_pending,
   `L4YAML.Proofs.StreamAccum.block_dispatch_deferred,
   `Tests.Guards.DropFalsity.flowPark]

/-- **The class item 239's law could not touch is the class this repair can
    change.**  Ten of the twenty-six conclude at `chars = []`, where
    `[] <:+ anything` leaves the suffix law silent — and NINE of the ten are on
    the thread.  So the statements safe from refutation are exactly the ones a
    premise would have to travel through, and the two measurements meet rather
    than overlap by accident. -/
def expectedEmptyClass : String := "empty=10 onThread=9"

/-- **Three readings of the same ten.**  `users` inlines generated
    auxiliaries, `rawRefs` is one step without them, and `fullApps` counts the
    declarations whose proof term applies the park to all ~~eight~~ nine of its
    arguments (item 293's `h_live0` is the ninth).  Only two of the ten BUILD a park; no reading here can say
    which two, and the pin exists so that a refinement which can disagrees
    with this file rather than replacing it silently. -/
def expectedParkReadings : String := "users=10 rawRefs=10 fullApps=10"

/-- The park's arity, pinned: a change to it re-aims `fullApps`.  Item 293
    re-aims it: the park reads `flag ∨ live` (`pendingFlow.h_live0`). -/
def parkArity : Nat := 9

/-- The largest application of `park` anywhere inside an expression.  A `cases`
    arm builds the constructor it eliminates, so this does NOT separate a
    builder from a case-splitter — see the module docstring.

    **Memoized, because an accumulation proof term is a DAG and a walk that
    forgets is exponential on it.**  An unmemoized version of this walk over
    the same ten declarations does not finish in ten minutes. -/
partial def maxParkArityAux (e : Expr) : StateM (Std.HashSet Expr) Nat := do
  if (← get).contains e then return 0
  modify (·.insert e)
  let here := if e.getAppFn.isConstOf park then e.getAppNumArgs else 0
  e.foldlM (fun a s => do return Nat.max a (← maxParkArityAux s)) here

def maxParkArity (e : Expr) : Nat := (maxParkArityAux e).run' {}

set_option maxHeartbeats 4000000 in
run_cmd Lean.Elab.Command.liftTermElabM do
  let env ← getEnv
  let pre := usesAll env
  let (authored, usesVal) := pre
  let rev := revEdges authored usesVal
  let th := thread rev supplier
  let pth := thread rev producer
  let rs := rings rev supplier
  let caps := (L4YAML.capstoneDecls env).filter th.contains
  let got := s!"thread={th.size} prodThread={pth.size} \
shared={(th.filter pth.contains).size} capstones={caps.size} rings={rs.size}"
  unless got == expectedThread do
    throwError "the thread moved:\n  got      {got}\n  expected {expectedThread}"
  unless rs.size > 0 && rs[0]!.toList == expectedRing1 do
    throwError "the first ring moved: {(rs[0]?.getD #[]).toList}"
  -- §3, over the whole thread
  let mut withPark : Nat := 0
  let mut covered : Nat := 0
  for n in th do
    let (p, _, hit) ← holdsScanStream n
    if p > 0 then withPark := withPark + 1
    if hit then covered := covered + 1
  let gotD := s!"withPark={withPark} covered={covered} total={th.size}"
  unless gotD == expectedDiscriminator do
    throwError "the discriminator moved:\n  got      {gotD}\n  expected {expectedDiscriminator}"
  -- the thread against item 238's transitive set
  let c ← census (some pre)
  let gotT := s!"threadInT={(th.filter c.trans.contains).size} \
outsideT={(th.filter (fun n => !c.trans.contains n)).size}"
  unless gotT == expectedInT do
    throwError "the thread left item 238's set:\n  got      {gotT}\n  expected {expectedInT}"
  -- item 239's `empty` class, against this thread
  let mut emptyAll : Nat := 0
  let mut emptyOn : Nat := 0
  for n in c.trans do
    if (← classifyDecl n) == "empty" then
      emptyAll := emptyAll + 1
      if th.contains n then emptyOn := emptyOn + 1
  let gotE := s!"empty={emptyAll} onThread={emptyOn}"
  unless gotE == expectedEmptyClass do
    throwError "item 239's empty class moved:\n  got      {gotE}\n  \
expected {expectedEmptyClass}"
  -- §4, the bracket and the two refinements that do not separate it
  let users := sorted (authored.filter fun n => (usesVal.getD n {}).contains park)
  let raw := sorted (authored.filter fun n => (rawRefs env n true).contains park)
  let full := sorted (authored.filter fun n =>
    match env.find? n with
    | none => false
    | some ci =>
      maxParkArity ((ci.value? (allowOpaque := true)).getD (mkConst n)) == parkArity)
  unless users.toList == expectedParkUsers do
    throwError "the park's users moved: {users.toList}"
  let gotP := s!"users={users.size} rawRefs={raw.size} fullApps={full.size}"
  unless gotP == expectedParkReadings do
    throwError "a reading of the park separated the ten:\n  got      {gotP}\n  \
expected {expectedParkReadings}"
  logInfo m!"RepairChoice {got} {gotD} {gotT} {gotE} {gotP}"
