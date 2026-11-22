/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML
import L4YAML.Proofs.Production.FlowKeyLift

/-!
# The span instrument, measured (DOCS item 229)

Item 228 priced the suffix lemma for `Surface/Node.lean`'s mutual block by
SIGNATURES, before a line of it existed: **69 constructor arms**.  This file
re-derives that number and the one the price missed.

§1 walks the closure of production types reachable from the block and counts
what a suffix family actually has to cover.  §2 counts how much of the closure
the library now relates to `List.IsSuffix`.  §3 pins the eighteen mutual-block
lemmas by name.  §4 sorts the four residues of `Proofs.FlowKeyLift` by the
only question a narrowing's worth turns on — can a consumer refute it.

The discipline these pins carry: **a price taken by signatures prices the
thing it counted, not the thing that has to be built**.  69 is right about the
block and is 48% of the arms the instrument needed.
-/

set_option autoImplicit false

namespace Tests.Guards.SurfaceSpanCensus

open Lean Elab Command Meta
open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan

/-! ## §0 The instrument is not vacuous

A suffix lemma over an uninhabited family is true and worth nothing, and this
tree has had constructors that nothing ever instantiated (DOCS items 33, 107).
So the family is exercised on a derivation first: `[]`, the empty flow
sequence, read as `[161] ns-flow-node(0, flow-out)`, and the instrument
applied to it. -/

/-- A real derivation in the mutual block. -/
example (rest : List Char) (col : Nat) :
    SFlowNode 0 .flowOut ⟨'[' :: ']' :: rest, col⟩ ⟨rest, col + 2⟩ :=
  SFlowNode.content 0 .flowOut _ _
    (SFlowContent.flowSeq 0 .flowOut _ _
      (SFlowSequence.empty 0 .flowOut _ _ _ _
        (GLit.mk _ _) (GOpt.none _) (GLit.mk _ _)))

/-- …and `sFlowNode_suffix` on it: the two brackets are the span. -/
example (rest : List Char) (col : Nat) : rest <:+ '[' :: ']' :: rest :=
  sFlowNode_suffix (SFlowNode.content 0 .flowOut _ _
    (SFlowContent.flowSeq 0 .flowOut _ _
      (SFlowSequence.empty 0 .flowOut ⟨'[' :: ']' :: rest, col⟩ _ _ ⟨rest, col + 2⟩
        (GLit.mk _ _) (GOpt.none _) (GLit.mk _ _))))

/-! ## §1 The closure the instrument had to cover

A "production" is any constant whose type ends `… → SurfPos → SurfPos → Prop`.
The walk starts at the mutual block and follows constructor types AND def
bodies — the first version of this census followed only inductives and read
**48** types, because `[69] s-separate(n,c)`, `[131] ns-plain(n,c)` and eleven
others are `def`s that dispatch on the context.  A closure walk that stops at
a definition under-reports the thing it is pricing. -/

-- 2026-10-23 ([162]): +3 ind / +7 ctors — `SCIndentationIndicator` (2), `SCChompingIndicator` (3) and `GAlt` (2),
-- which `SCBBlockHeader` now brings into the block's closure; all three are leaves.
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `types` 77 → 79, `ind` 64 → 66, `ctors` 150 → 158, `block` 18/69 → 20/77.
def expectedClosure : String := "types=79 ind=66 def=13 ctors=160 block=20/79 leaf=59/81"

/-- Every production type reachable from `SFlowNode`'s mutual block, with its
    constructor count (0 for a `def`) and whether it is in the block. -/
def productionClosure (env : Environment) : MetaM (Array (Name × String × Nat × Bool)) := do
  let shape (nm : Name) : MetaM (Option (String × Nat)) := do
    let some ci := env.find? nm | return none
    forallTelescope ci.type fun xs cod => do
      if !cod.isProp then return none
      if xs.size < 2 then return none
      let t1 ← inferType xs[xs.size-1]!
      let t2 ← inferType xs[xs.size-2]!
      if !(t1.isConstOf ``SurfPos && t2.isConstOf ``SurfPos) then return none
      match ci with
      | .inductInfo fi => return some ("ind", fi.ctors.length)
      | .defnInfo _ => return some ("def", 0)
      | _ => return none
  let some (.inductInfo root) := env.find? ``SFlowNode
    | throwError "the flow grammar's head type is gone"
  let mut seen : Std.HashSet Name := {}
  let mut work : List Name := root.all
  let mut rows : Array (Name × String × Nat × Bool) := #[]
  while !work.isEmpty do
    let nm := work.head!
    work := work.tail!
    if seen.contains nm then continue
    match ← shape nm with
    | none => continue
    | some (kind, nc) =>
      seen := seen.insert nm
      rows := rows.push (nm, kind, nc, root.all.contains nm)
      let some ci := env.find? nm | continue
      let mut next : Array Name := #[]
      match ci with
      | .inductInfo fi =>
        for ctor in fi.ctors do
          if let some cci := env.find? ctor then next := next ++ cci.type.getUsedConstants
      | _ =>
        if let some v := ci.value? (allowOpaque := true) then next := next ++ v.getUsedConstants
      for u in next do
        if !seen.contains u then work := u :: work
  return rows

/-! ## §2 How much of it the library relates to a suffix

The same reading item 228's `ConclusionObligationCensus` §4 takes, widened
from the 18 to the whole closure: a type is covered when some theorem's TYPE
mentions both it and `List.IsSuffix`.  At item 228 this read 10 of 74 — the
comment family in `Proofs/Coupling/TabIndentBridge.lean`. -/

/-- 69 of the 74; the five that never appear in a suffix lemma's TYPE are
    `abbrev`s — `SBAsLineFeed` and `SBNonContent` are `[28] b-break`, and
    `SNbChar`, `SNsChar`, `SCommentChar` are `GChar` at three predicates — so
    `sbBreak_suffix` and `gchar_suffix` cover them definitionally and a second
    statement would be a second name for the same fact. -/
-- 2026-10-23 ([162]): closure 74 → 77, all three newcomers covered (`scIndentationIndicator_suffix`,
-- `scChompingIndicator_suffix`, `galt_suffix`); the five uncovered are unchanged.
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `closure` 77 → 79, `covered` 72 → 74 — both new types have suffix lemmas.
def expectedCoverage : String := "closure=79 covered=74 uncovered=5"

/-! ## §3 The mutual block's eighteen -/

def expectedBlockLemmas : List String :=
  ["sBlockIndented_suffix",
   "sBlockMapEntries_suffix",
   "sBlockMapEntry_suffix",
   "sBlockNode_suffix",
   "sBlockSeqEntries_suffix",
   "sCompactMapTail_suffix",
   "sCompactMap_suffix",
   "sCompactSeqTail_suffix",
   "sCompactSeq_suffix",
   "sFlowContent_suffix",
   "sFlowMapEntries_suffix",
   "sFlowMapEntry_suffix",
   "sFlowMapping_suffix",
   "sFlowNode_suffix",
   "sFlowSeqEntries_suffix",
   "sFlowSeqEntry_suffix",
   "sFlowSequence_suffix",
   "sImplicitKey_suffix"]

run_cmd liftTermElabM do
  let env ← getEnv
  let rows ← productionClosure env
  let inds := rows.filter (·.2.1 == "ind")
  let defs := rows.filter (·.2.1 == "def")
  let inB := rows.filter (·.2.2.2)
  let ctorsAll := rows.foldl (fun a r => a + r.2.2.1) 0
  let ctorsIn := inB.foldl (fun a r => a + r.2.2.1) 0
  let got := s!"types={rows.size} ind={inds.size} def={defs.size} ctors={ctorsAll} \
block={inB.size}/{ctorsIn} leaf={rows.size - inB.size}/{ctorsAll - ctorsIn}"
  if got != expectedClosure then
    throwError "the production closure moved.\nexpected: {expectedClosure}\ngot:      {got}"
  -- §2
  let names : Std.HashSet Name := rows.foldl (fun a r => a.insert r.1) {}
  let mut covered : Std.HashSet Name := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    match ci with | .thmInfo _ => pure () | _ => continue
    let us := ci.type.getUsedConstants
    if !us.contains ``List.IsSuffix then continue
    for t in us do
      if names.contains t then covered := covered.insert t
  let gotC := s!"closure={rows.size} covered={covered.size} uncovered={rows.size - covered.size}"
  if gotC != expectedCoverage then
    throwError "the suffix coverage moved.\nexpected: {expectedCoverage}\ngot:      {gotC}\n\
uncovered: {(rows.filterMap (fun r => if covered.contains r.1 then none else some r.1.toString)).qsort (· < ·)}"
  -- §3
  let blockLemmas := (rows.filter (·.2.2.2)).filterMap fun r =>
    let lem := (`L4YAML.Proofs.SurfaceSpan).str (r.1.getString!.decapitalize ++ "_suffix")
    if (env.find? lem).isSome then some lem.getString! else none
  let gotB := (blockLemmas.qsort (· < ·)).toList
  if gotB != expectedBlockLemmas then
    throwError "the block's suffix lemmas moved.  Paste-ready:\n{
      String.intercalate "\n" (blockLemmas.qsort (· < ·) |>.map (fun r => "   \"" ++ r ++ "\",")).toList}"

/-! ## §4 The four residues, sorted by refutability

`conclusion_eliminable_iff` (item 228) says a narrowed conclusion `A ∨ R`
yields `A` exactly when the consumer can refute `R`.  These four are
`Proofs.FlowKeyLift`'s residues; the question is settled for all four, and the
answers differ. -/

open L4YAML.Proofs.FlowKeyLift in
/-- Three carry a break in their own span, and so are refutable by a
    single-line consumer. -/
example {n : Nat} {c : L4YAML.YamlContext} {s s' : SurfPos} :
    (PlainResidue n c s s' → BreakBetween s s') ∧
    (DoubleResidue n s s' → BreakBetween s s') ∧
    (SingleResidue n s s' → BreakBetween s s') :=
  ⟨plainResidue_break, doubleResidue_break, singleResidue_break⟩

open L4YAML.Proofs.FlowKeyLift in
/-- The fourth conversion's ARM is not, and the reason is that its span can be
    EMPTY: no predicate on the characters between the two positions separates
    it from a separation that was never taken. -/
example (chars : List Char) :
    SepCommentedArm 0 ⟨chars, 0⟩ ⟨chars, 0⟩ ∧ ¬ BreakBetween ⟨chars, 0⟩ ⟨chars, 0⟩ :=
  sepCommentedArm_span_can_be_empty chars

open L4YAML.Proofs.FlowKeyLift in
/-- **Item 230 answers the fourth by changing the residue, not the arm.**
    `[77] b-comment` ends a comment with a break or at end of input and in no
    other way, so `SepResidue` — `BreakBetween s s' ∨ atEnd s'` — is what the
    conversion really declines on, and the derivation item 229 could not
    refute now returns the LEFT disjunct at every position that is not the end
    of the input. -/
example (ch : Char) (rest : List Char) :
    SSeparate 0 .blockKey ⟨ch :: rest, 0⟩ ⟨ch :: rest, 0⟩ :=
  sep_toKey_left_at_zero_width ch rest

open L4YAML.Proofs.FlowKeyLift in
/-- …and `atEnd` is not slack in it: the second witness is a
    comment-delimited separation that crosses no line and is not inline
    either, so dropping `atEnd` would leave `sep_toKey` with no disjunct for
    that input. -/
example : SepCommentedArm 0 ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ ∧
    ¬ BreakBetween ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ ∧
    ¬ SSeparateInLine ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ :=
  ⟨sepCommentedArm_at_eof_comment.1, sepCommentedArm_at_eof_comment.2,
    sepCommentedArm_at_eof_comment_not_inline⟩

/-! ## §5 Where the 83 dead sites actually go

Item 228's FALSE probe read **83** compiler errors for `flowNode_toKey` and
its NEXT called the suffix lemma "the one thing that would turn 83 dead sites
into 83 payable ones".  The lemma exists now, and that sentence is wrong: a
site is payable when the leaf it declines through carries a REFUTABLE residue,
and at item 229 the four leaves were not alike.

(The two numbers below are 82, not 83.  They are a different instrument —
occurrences of `@Or.inr _ True _` in the proof term, against a count of errors
after rewriting the conclusion — and neither corrects the other; item 228's
own instrument debt records that an error count is a property of how a proof
is written.)

This counts the leaf applications in `flowNode_toKey`'s own proof TERM — not
its source text, so the number survives a re-indent — and splits them by
whether the leaf's residue can be discharged.

**Re-aimed at item 231, because re-pinning it would have emptied it.**  The
sweep selected `@Or.inr _ True _`, and item 231 rebuilt the eighteen motives
so that `flowNode_toKey` carries none: the four numbers would have read
`noop=0 payable=0 blocked=0 relay=0` and the gate would have passed over an
empty population.  It now selects on the right disjunct's type either way and
reports both, so `noop=0` is an assertion and `carried` is the population the
other three are taken over.

**Re-aimed again at item 232, and for the opposite reason**: the population
did not empty, it OCTUPLED.  The conversion is now a `mutual` block of eight
structurally recursive lemmas rather than one recursor application, and
mutual structural recursion does not share a fixpoint — each lemma is its own
`T.brecOn` over the same 41 arms, so each of the eight carries all 82
declining sites.  Reading `flowNode_toKey` alone would still have said
`carried=82` and said nothing about the other seven.  The sweep walks all
eight and ASSERTS their splits are equal; `exports` is what makes the
replication visible, and the four numbers after it are per export, unmoved
since item 230.

**The classification is looked up in the environment, not written here.**  A
leaf counts as payable exactly when the library carries a lemma that returns
the conversion from a consumer's hypotheses.  Item 229's split named the
`sep_*` lane `blocked` in a `let`, and item 230 made that lane payable without
moving a single one of these counts — the census would have kept passing while
its own words went stale.  Selecting on the payment lemma is what stops that:
the roster below is a list of pairs, and a pair pays only if its second name
resolves. -/

/-- The leaf conversions `flowNode_toKey` declines through, each with the
    lemma that discharges its residue.  A missing second name is a blocked
    lane, and that is the whole classification. -/
def leafPayments : List (String × String) :=
  [("plain_toKey", "plain_toKey_of_noBreak"),
   ("doubleQuoted_toKey", "doubleQuoted_toKey_of_noBreak"),
   ("singleQuoted_toKey", "singleQuoted_toKey_of_noBreak"),
   ("sep_toKey", "sep_toKey_of_noResidue"),
   ("sepOpt_toKey", "sepOpt_toKey_of_noResidue"),
   ("props_toKey", "props_toKey_of_noResidue")]

/-- The eight conversions the `mutual` block exports, in the family's order.
    Item 231 had one of these; the other seven were reachable only by
    inverting it. -/
def flowExports : List String :=
  ["flowNode_toKey", "flowContent_toKey", "flowSequence_toKey",
   "flowSeqEntries_toKey", "flowSeqEntry_toKey", "flowMapping_toKey",
   "flowMapEntries_toKey", "flowMapEntry_toKey"]

-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `carried` 82 → 96, `payable` 48 → 55, `relay` 34 → 41 — 8 new arms + 2 suffix lemmas.
def expectedLeafSplit : String := "exports=8 noop=0 carried=108 payable=62 blocked=0 relay=46"

/-- How many times a constant occurs in a term, WITHOUT deduplication: the
    compiler pays per occurrence, and item 228's DAG walk undercounted for
    exactly this reason. -/
partial def countConst (target : Name) (e : Expr) : Nat :=
  (if e.isConstOf target then 1 else 0) + sub e
where
  sub (e : Expr) : Nat :=
    match e with
    | .app f a => countConst target f + countConst target a
    | .lam _ d b _ => countConst target d + countConst target b
    | .forallE _ d b _ => countConst target d + countConst target b
    | .letE _ t v b _ => countConst target t + countConst target v + countConst target b
    | .mdata _ b => countConst target b
    | .proj _ _ b => countConst target b
    | _ => 0

/-- The declining sites themselves, counted per occurrence and selected by the
    right disjunct's TYPE — not by its witness, which at item 230 mattered
    because only 28 of the 82 carried a syntactic `True.intro`, and at item 231
    matters more: every one of the 82 now carries a `sepResidue_widen`
    application or a bridged scalar break, and no two of them are alike. -/
partial def countInr (isRight : Expr → Bool) (e : Expr) : Nat :=
  (if e.isAppOfArity ``Or.inr 3 && isRight (e.getArg! 1) then 1 else 0) +
  match e with
  | .app f a => countInr isRight f + countInr isRight a
  | .lam _ d b _ => countInr isRight d + countInr isRight b
  | .forallE _ d b _ => countInr isRight d + countInr isRight b
  | .letE _ t v b _ => countInr isRight t + countInr isRight v + countInr isRight b
  | .mdata _ b => countInr isRight b
  | .proj _ _ b => countInr isRight b
  | _ => 0

run_cmd liftTermElabM do
  let env ← getEnv
  let fkl := `L4YAML.Proofs.FlowKeyLift
  let mut splits : Array String := #[]
  for export_ in flowExports do
    let some ci := env.find? (fkl.str export_)
      | throwError "{export_} is gone from FlowKeyLift"
    let some v := ci.value? (allowOpaque := true) | throwError "no proof term for {export_}"
    let n (s : String) := countConst (fkl.str s) v
    let noop := countInr (fun x => (x.isConstOf ``True || x.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt || x.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG)) v  -- item 311
    let carried := countInr (·.isAppOf (fkl.str "SepResidue")) v
    let mut payable := 0
    let mut blocked := 0
    for (leaf, payment) in leafPayments do
      if (env.find? (fkl.str leaf)).isNone then
        throwError "leaf {leaf} is gone from FlowKeyLift"
      if (env.find? (fkl.str payment)).isSome then payable := payable + n leaf
      else blocked := blocked + n leaf
    -- what is left declines through the recursion itself, so it follows the
    -- worst leaf its sub-derivation reaches.
    let relay := (noop + carried) - payable - blocked
    splits := splits.push s!"noop={noop} carried={carried} payable={payable} \
blocked={blocked} relay={relay}"
  -- the replication IS the finding: eight fixpoints over one block of arms.
  for (export_, split) in flowExports.zip splits.toList do
    if split != splits[0]! then
      throwError "the eight exports are no longer copies of one block.\n\
        {flowExports[0]!}: {splits[0]!}\n  {export_}: {split}"
  let got := s!"exports={splits.size} {splits[0]!}"
  if got != expectedLeafSplit then
    throwError "the leaf split moved.\nexpected: {expectedLeafSplit}\ngot:      {got}"

/-! ## §6 What the operation cost, in constructor arms (DOCS item 230)

Item 229's NEXT priced the `sep_toKey` re-proof by signatures at **12
constructor arms**, naming seven productions: `[79] s-l-comments` 2,
`[76] s-b-comment` 2, `[78] l-comment` 1, `[77] b-comment` 2,
`[71] s-flow-line-prefix` 1, `[63] s-indent(n)` 2, `[66] s-separate-in-line`
2.  All seven were needed and all twelve arms were cased on.  They were not
all of it.

This walks the proof TERMS of the item's declarations — through their matcher
auxiliaries, which is where a `match` puts its case analysis — collects every
eliminator applied to an inductive, and sums that inductive's constructor
count.  It is the same shape as §1's closure walk and it fails the same way if
you stop at the named productions: the signature walk enumerated the YAML
productions and skipped the generic combinators the productions are built
from, which live in the same namespace and carry arms of their own. -/

def expectedArmPrice : String :=
  "types=16 ctors=26 prod=9/16 comb=4/6 forecast=7/12"

/-- The declarations item 230 added or re-proved.  Private helpers and matcher
    auxiliaries are reached by the walk, not listed here. -/
def item230Roster : List Name :=
  ((`L4YAML.Proofs.SurfaceSpan).str <$>
    ["gstar_append", "gstar_of_gplus", "separateInLine_of_whites",
     "whites_of_separateInLine", "separateInLine_trans", "sIndent_whites",
     "sFlowLinePrefix_separateInLine", "atEnd_of_suffix",
     "breakOrEnd_extend_right", "breakOrEnd_extend_left",
     "sbComment_breakOrEnd", "ssbComment_breakOrEnd", "slComment_breakOrEnd",
     "gstarComment_breakOrEnd", "sslComments_inline_or_breakOrEnd",
     "separateLines_inline_or_breakOrEnd", "separate_inline_or_breakOrEnd"]) ++
  ((`L4YAML.Proofs.FlowKeyLift).str <$>
    ["sep_toKey", "sepOpt_toKey", "props_toKey", "sep_toBlockKey"])

partial def constsOf (e : Expr) : Array Name :=
  match e with
  | .const nm _ => #[nm]
  | .app f a => constsOf f ++ constsOf a
  | .lam _ d b _ => constsOf d ++ constsOf b
  | .forallE _ d b _ => constsOf d ++ constsOf b
  | .letE _ t val b _ => constsOf t ++ constsOf val ++ constsOf b
  | .mdata _ b => constsOf b
  | .proj _ _ b => constsOf b
  | _ => #[]

/-- The inductive an eliminator eliminates, or `none`. -/
def elimTarget : Name → Option Name
  | .str p t => if t ∈ ["casesOn", "rec", "recOn", "brecOn", "below", "binductionOn"]
      then some p else none
  | _ => none

/-- A compiler-generated auxiliary the walk must descend into: a `match` puts
    its case analysis in one of these, so a walk that stops at the named
    declaration sees no eliminator at all. -/
def isAuxiliary : Name → Bool
  | .str _ t => t.startsWith "match_" || t.startsWith "proof_"
  | _ => false

run_cmd liftTermElabM do
  let env ← getEnv
  let mut work := item230Roster
  -- private helpers of the two modules: their user-facing prefix is the
  -- namespace, and the walk needs their bodies for the same reason.
  for (nm, _) in env.constants.toList do
    if isPrivateName nm then
      let u := privateToUserName nm
      if u.getPrefix == `L4YAML.Proofs.SurfaceSpan ||
         u.getPrefix == `L4YAML.Proofs.FlowKeyLift then
        work := nm :: work
  let mut seen : NameSet := {}
  let mut types : NameSet := {}
  while !work.isEmpty do
    let nm := work.head!
    work := work.tail!
    if seen.contains nm then continue
    seen := seen.insert nm
    match env.find? nm with
    | none => throwError "item 230's roster names {nm}, which is not in the environment"
    | some ci =>
      match ci.value? (allowOpaque := true) with
      | none => pure ()
      | some val =>
        for c in constsOf val do
          match elimTarget c with
          | some t => if let some (.inductInfo _) := env.find? t then types := types.insert t
          | none => if isAuxiliary c then work := c :: work
  let mut rows : Array (String × Nat) := #[]
  for t in types.toList do
    if let some (.inductInfo iv) := env.find? t then
      rows := rows.push (t.toString, iv.ctors.length)
  let sum (a : Array (String × Nat)) : Nat := a.foldl (fun acc r => acc + r.2) 0
  let prod := rows.filter (fun r => r.1.startsWith "L4YAML.Surface.S")
  let comb := rows.filter (fun r => r.1.startsWith "L4YAML.Surface.G")
  let got := s!"types={rows.size} ctors={sum rows} prod={prod.size}/{sum prod} \
    comb={comb.size}/{sum comb} forecast=7/12"
  if got != expectedArmPrice then
    throwError "the arm price moved.\nexpected: {expectedArmPrice}\ngot:      {got}\n\
      types: {(rows.qsort (fun a b => a.1 < b.1)).map (·.1)}"

/-! ## §7 What a recursor application exports (DOCS items 231, 232)

A recursor application hands back ONE of its motives.  At item 231
`flowNode_toKey` was one application of `SFlowNode.rec` carrying eighteen, and
its conclusion was `motive_11` applied to the major premise; the other
seventeen were reachable only by building a major premise of the head type and
INVERTING the result, which is what `flowContent_toBlockKey` did — it wrapped
an `SFlowContent` in `SFlowNode.content`, converted, and peeled.  The peel has
four arms and the conversion rules out none of them, so it could not return
the residue, and it was the one conclusion in `FlowKeyLift` ending in `True`.

That is items 229 and 230's corollary one level up: **a population enumerated
by a walk stops where the walk stops.**  There the walk was a signature list
and a name list; there it was the recursor's own major premise.

**Item 232 pays it.**  The conversion is a `mutual` block of eight
structurally recursive lemmas — accepted on a strict SUBFAMILY of the
eighteen, through each type's own `brecOn` with the ten unused `below` motives
filled by the elaborator, which is what item 231 did by hand with ten `True`s.
All eight types are exported and `flowContent_toBlockKey` reads its own lemma
instead of inverting, so `trueOnly` and `none` are both zero and this file has
no conclusion left ending in `True`.  What it cost is §5's `exports=8`: eight
fixpoints, not one shared one. -/

def flowTypeNames : List Name :=
  (`L4YAML.Surface).str <$>
    ["SFlowNode", "SFlowContent", "SFlowSequence", "SFlowSeqEntries",
     "SFlowSeqEntry", "SFlowMapping", "SFlowMapEntries", "SFlowMapEntry"]

-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `motives` 18 → 20 — `scFlowJsonContent_suffix`, `scFlowJsonNode_suffix`.
def expectedMotiveExport : String := "motives=20 flow=8 residue=8 trueOnly=0 none=0"

/-- The recursor's motive binders, read off its type. -/
partial def motiveBinders : Expr → Nat
  | .forallE n _ b _ => (if n.toString.startsWith "motive" then 1 else 0) + motiveBinders b
  | _ => 0

run_cmd liftTermElabM do
  let env ← getEnv
  let some ci := env.find? ``L4YAML.Surface.SFlowNode.rec
    | throwError "the flow grammar's recursor is gone"
  let motives := motiveBinders ci.type
  let fkl := `L4YAML.Proofs.FlowKeyLift
  -- for each flow type: does `FlowKeyLift` conclude a conversion for it, and
  -- does that conclusion carry the residue or `True`?
  let mut residue : NameSet := {}
  let mut viaTrue : NameSet := {}
  for (nm, c) in env.constants.toList do
    if nm.isInternal then continue
    if !fkl.isPrefixOf nm then continue
    match c with | .thmInfo _ => pure () | _ => continue
    let hit ← forallTelescope c.type fun _ cod => do
      if !cod.isAppOfArity ``Or 2 then return none
      let some t := (cod.getArg! 0).getAppFn.constName? | return none
      if !(flowTypeNames.contains t) then return none
      return some (t, cod.getArg! 1)
    if let some (t, r) := hit then
      if r.isAppOf (fkl.str "SepResidue") then residue := residue.insert t
      else if (r.isConstOf ``True || r.isAppOf ``L4YAML.Proofs.StreamAccum.PackAlt || r.isAppOf ``L4YAML.Proofs.StreamAccum.PackAltG) then viaTrue := viaTrue.insert t  -- item 311
  let viaTrueOnly := viaTrue.toList.filter (!residue.contains ·)
  let covered := residue.size + viaTrueOnly.length
  let got := s!"motives={motives} flow={flowTypeNames.length} residue={residue.size} \
trueOnly={viaTrueOnly.length} none={flowTypeNames.length - covered}"
  if got != expectedMotiveExport then
    throwError "the motive export moved.\nexpected: {expectedMotiveExport}\ngot:      {got}\n\
      residue: {residue.toList}\n  trueOnly: {viaTrueOnly}"


/-! ## §8 Who takes it (DOCS item 233)

Items 228–232 built the supply.  Four residues were named, eight conversions
were exported, six leaf payments were written.  This section asks the one
question none of those items asked of its own output — **who takes it** — and
answers it in the environment rather than by grep, because a consumer that
reaches a lemma through a bound variable or an abbreviation is invisible to a
textual search and a name that only appears in a docstring is visible to one.

**The eight exports have no user.**  The demand surface is the three
`*_toBlockKey` wrappers and the two declarations that apply them, both in
`StreamAccum`: `flowKeyHead` reads `flowNode_toBlockKey`, and
`accum_flow_open_depth0` reads `flowContent_toBlockKey` and `sep_toBlockKey`.
Both discard the residue — one with `fun _ => trivial`, one with a wildcard
pattern — and neither holds a fact that would refute it, which is what
`elsewhere=0` below says once it is read as a statement about the whole
library rather than about those two.

**The six leaf payments have no user either.**  Items 229 and 230 built
`plain_toKey_of_noBreak`, `doubleQuoted_toKey_of_noBreak`,
`singleQuoted_toKey_of_noBreak`, `sep_toKey_of_noResidue`,
`sepOpt_toKey_of_noResidue` and `props_toKey_of_noResidue`, and nothing has
instantiated one.  That is this repository's own rule — *a definition nothing
has instantiated is not yet evidence* — read against our own work, and the
census is here so the next item reads it as a number instead of finding it
again.

**Item 223 is the precedent and its title is the lesson**: *tightening the
supply changes nothing until the demand is re-asked.*  It built the ledger for
the pending-park family (`Tests/Guards/Proofs/ArmDemandLedger.lean`) and asks
of a PARAMETER whether its consumers request the strong form.  This asks the
same question of a CONCLUSION, where the weaker answer is available: whether a
consumer exists at all.

**The payment is one `resolve_right`, not forty-eight.**  §5 reports
`payable=48` leaf applications per export, and 48 is a count of PRODUCERS: the
residue widens (`sepResidue_widen`), so every interior one is a residue of the
whole span and a consumer holding the two facts discharges all of them at
once.  The three payments measure it: each contains exactly one
`Or.resolve_right`, and their proof terms are two orders of magnitude smaller
than the export they pay for.

**And the reason there is no consumer is a missing coordinate, not a careless
one.**  `BreakBetween` does not occur in the type of a single declaration
outside the two modules that define the residue vocabulary, so there is
nothing for a consumer to hold: six declarations ASK for `¬ BreakBetween`,
two PROVE one, and both of those two prove it of a literal character list.
**Nothing in the library refutes a break over a derivation**, which is
`overDerivation=0` below and is the supply side in one number.  What `[193] c-s-implicit-json-key` supplies
is a fact about the SCANNER's line counter; `ScannerSurfCorr` — the
correspondence between a scanner state and a surface position — has five
fields and none of them is the line, and `SurfPos` has two, `chars` and `col`.
The price of the supply side is that coordinate.  `scripts/flips/item233_flow_key_head.json` (via `scripts-flip`)
prices the other half: tightening the head promise to take the two facts
breaks four definitions from seven locations, and that is a lower bound
because the build stops at the module all four live in. -/

/-- The three `.flowOut → .blockKey` wrappers: the whole of what anything
    outside this file actually applies. -/
def residueWrappers : List String :=
  ["flowNode_toBlockKey", "flowContent_toBlockKey", "sep_toBlockKey"]

/-- Each group as `names/distinct users`.  Users are counted OUTSIDE
    `FlowKeyLift` and inside `L4YAML`, which is the only thing that imports
    it. -/
def expectedDemand : String :=
  "exports=8/0 wrappers=3/2 payments=6/0 leaves=6/0"

run_cmd liftTermElabM do
  let env ← getEnv
  let fkl := `L4YAML.Proofs.FlowKeyLift
  let payments := leafPayments.map (·.2)
  let leaves := leafPayments.map (·.1)
  for nm in flowExports ++ residueWrappers ++ payments ++ leaves do
    if (env.find? (fkl.str nm)).isNone then
      throwError "{nm} is gone from FlowKeyLift; this census is walking a name that moved"
  let mut uE : NameSet := {}
  let mut uW : NameSet := {}
  let mut uP : NameSet := {}
  let mut uL : NameSet := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if !(`L4YAML).isPrefixOf n then continue
    if fkl.isPrefixOf n then continue
    let some v := ci.value? (allowOpaque := true) | continue
    let used := v.getUsedConstants
    let hits (names : List String) : Bool := names.any (fun nm => used.contains (fkl.str nm))
    if hits flowExports then uE := uE.insert n
    if hits residueWrappers then uW := uW.insert n
    if hits payments then uP := uP.insert n
    if hits leaves then uL := uL.insert n
  let got := s!"exports={flowExports.length}/{uE.size} \
wrappers={residueWrappers.length}/{uW.size} payments={payments.length}/{uP.size} \
leaves={leaves.length}/{uL.size}"
  if got != expectedDemand then
    throwError "the demand moved.\nexpected: {expectedDemand}\ngot:      {got}\n\
      exports:  {uE.toList}\n  wrappers: {uW.toList}\n\
      payments: {uP.toList}\n  leaves:   {uL.toList}"

/-- The size of a proof term, counted per node.  `Expr` is a DAG and this walk
    does not deduplicate, for §5's reason: the compiler pays per occurrence. -/
partial def termSize : Expr → Nat
  | .app f a => 1 + termSize f + termSize a
  | .lam _ d b _ => 1 + termSize d + termSize b
  | .forallE _ d b _ => 1 + termSize d + termSize b
  | .letE _ t v b _ => 1 + termSize t + termSize v + termSize b
  | .mdata _ b => 1 + termSize b
  | .proj _ _ b => 1 + termSize b
  | _ => 1

/-- What a payment costs against what it pays for.  `resolveRight` is the
    assertion: six payments, six `Or.resolve_right` applications, one each. -/
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `export` 55650 → 72045 — the flow mutual block grew by two types.
def expectedPaymentShape : String := "payments=6 resolveRight=6 maxPayment=111 export=78011"

run_cmd liftTermElabM do
  let env ← getEnv
  let fkl := `L4YAML.Proofs.FlowKeyLift
  let payments := leafPayments.map (·.2)
  let term (nm : String) : MetaM Expr := do
    let some ci := env.find? (fkl.str nm) | throwError "{nm} is gone from FlowKeyLift"
    let some v := ci.value? (allowOpaque := true) | throwError "no proof term for {nm}"
    return v
  let mut resolves := 0
  let mut maxPayment := 0
  for nm in payments do
    let v ← term nm
    resolves := resolves + countConst ``Or.resolve_right v
    maxPayment := max maxPayment (termSize v)
  let mut export_ := 0
  for nm in flowExports do
    export_ := max export_ (termSize (← term nm))
  let got := s!"payments={payments.length} resolveRight={resolves} \
maxPayment={maxPayment} export={export_}"
  if got != expectedPaymentShape then
    throwError "the payment shape moved.\nexpected: {expectedPaymentShape}\ngot:      {got}"

/-- Where the refutation would have to come from.  `mentions` is every
    declaration in `L4YAML` whose TYPE mentions `BreakBetween`; `elsewhere` is
    how many of them live outside the two modules that define the residue
    vocabulary, and it is the number this section exists to keep at zero-or-
    known.  `corrFields`/`posFields` name the coordinate that is missing. -/
def expectedRefuters : String :=
  "mentions=25 lift=11 span=14 elsewhere=0 corrFields=5 posFields=2"

/-- The same population split by POLARITY, which is the sharper reading:
    `produces` concludes a `¬ BreakBetween`, `assumes` takes one as a
    hypothesis, and `overDerivation` is how many of the producers state it
    about positions a binder introduced rather than about a literal character
    list.  The last is the number a refuter needs and it is zero: every
    payment in §4 of `FlowKeyLift` asks for a fact the library never proves of
    a derivation. -/
def expectedRefutationSupply : String :=
  "produces=2 assumes=6 overDerivation=0"

/-- Every `¬ BreakBetween a b` inside a type, with its two positions.  Written
    as a walk rather than a pattern match on the conclusion because a payment
    states it in a binder and a witness states it inside a conjunction. -/
partial def negatedBreaks (bb : Name) (e : Expr) : Array (Expr × Expr) :=
  (if e.isAppOfArity ``Not 1 && (e.getArg! 0).isAppOfArity bb 2 then
      #[((e.getArg! 0).getArg! 0, (e.getArg! 0).getArg! 1)] else #[]) ++
  match e with
  | .app f a => negatedBreaks bb f ++ negatedBreaks bb a
  | .lam _ d b _ => negatedBreaks bb d ++ negatedBreaks bb b
  | .forallE _ d b _ => negatedBreaks bb d ++ negatedBreaks bb b
  | .letE _ t v b _ => negatedBreaks bb t ++ negatedBreaks bb v ++ negatedBreaks bb b
  | .mdata _ b => negatedBreaks bb b
  | .proj _ _ b => negatedBreaks bb b
  | _ => #[]

run_cmd liftTermElabM do
  let env ← getEnv
  let bb := ``L4YAML.Proofs.SurfaceSpan.BreakBetween
  let fkl := `L4YAML.Proofs.FlowKeyLift
  let sspan := `L4YAML.Proofs.SurfaceSpan
  let mut lift := 0
  let mut span := 0
  let mut other : NameSet := {}
  let mut produces : NameSet := {}
  let mut assumes : NameSet := {}
  let mut overDeriv : NameSet := {}
  for (n, ci) in env.constants.toList do
    if n.isInternal then continue
    if !(`L4YAML).isPrefixOf n then continue
    if !(ci.type.getUsedConstants.contains bb) then continue
    if fkl.isPrefixOf n then lift := lift + 1
    else if sspan.isPrefixOf n then span := span + 1
    else other := other.insert n
    let (p, a, d) ← forallTelescope ci.type fun xs cod => do
      let inCod := negatedBreaks bb cod
      let mut inBinder := false
      for x in xs do
        if !(negatedBreaks bb (← inferType x)).isEmpty then inBinder := true
      return (!inCod.isEmpty, inBinder, inCod.any (fun (u, v) => u.isFVar && v.isFVar))
    if p then produces := produces.insert n
    if a then assumes := assumes.insert n
    if d then overDeriv := overDeriv.insert n
  let some corr := getStructureInfo? env ``L4YAML.Proofs.CouplingBridge.ScannerSurfCorr
    | throwError "the scanner/surface correspondence is gone"
  let some pos := getStructureInfo? env ``L4YAML.Surface.SurfPos
    | throwError "SurfPos is gone"
  let got := s!"mentions={lift + span + other.size} lift={lift} span={span} \
elsewhere={other.size} corrFields={corr.fieldNames.size} posFields={pos.fieldNames.size}"
  if got != expectedRefuters then
    throwError "the refuter census moved.\nexpected: {expectedRefuters}\ngot:      {got}\n\
      elsewhere: {other.toList}"
  let got2 := s!"produces={produces.size} assumes={assumes.size} \
overDerivation={overDeriv.size}"
  if got2 != expectedRefutationSupply then
    throwError "the refutation supply moved.\nexpected: {expectedRefutationSupply}\n\
      got:      {got2}\n  produces: {produces.toList}\n  assumes: {assumes.toList}\n\
      overDerivation: {overDeriv.toList}"

end Tests.Guards.SurfaceSpanCensus
