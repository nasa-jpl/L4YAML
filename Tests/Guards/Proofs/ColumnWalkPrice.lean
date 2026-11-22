/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Surface
import L4YAML.Proofs.Foundation.SurfaceSpan
import L4YAML.Proofs.Foundation.SurfaceSpanSupply

/-!
# The column walk is one pass carrying three conclusions (DOCS item 235)

Item 234 refuted the column law as item 233 stated it and kept the half a
refuter needs — `BreakBetween s s' → s'.col < |span s s'|`.  Its NEXT asked
the one number nothing held: **can that walk and the span walk be ONE
induction, or does item 232's finding apply again — a mutual block does not
share a fixpoint, so each conclusion is paid for separately?**

The answer is that the question had the wrong pair in it, and that the sharing
is real.

## There are two column conclusions, not one

`BreakBetween s s' → s'.col < |span s s'|` does not compose with itself.  Put
a break in the FIRST half of a two-premise arm and the strict bound on that
half has to be carried across the second, which needs

    s'.col ≤ s.col + |span s s'|                                  (MONOTONE)

— a second statement over the same 167 arms.  §1 does not report this as a
stuck goal: `strict_alone_refuted` REFUTES the composition of the strict bound
alone, with a three-position counterexample, and `counterexample_violates_mono`
shows MONOTONE is exactly what excludes it.

MONOTONE composes with itself and never needs the strict bound, so the
dependency is a one-way chain and not a cycle.  Both arrangements therefore
typecheck, and the question is a price, not a possibility.

## The span is carried, not consumed

The span is not a third walk.  `ColLaw` bundles it, `ColLaw.trans` is
self-contained, and `colLaw_to_suffix` projects the bundle back onto
`SurfaceSpan`'s conclusion — so the span walk is a COMPONENT of the column
walk, not a prerequisite of it.  Fetching each span from a `*_suffix` lemma
instead costs a span citation per link plus an accumulation per composition
node: on the longest arm in the flow cycle, `[150] ns-flow-pair`'s explicit
value form, 13 citations become 52.

## The price, and where it is re-derived

§3 is the recursion's real shape: the closure is **62 strongly connected
components, of which only 8 recurse**.  The eighteen-type mutual block of
`Surface/Node.lean` is not one cycle — it is a 9-type cycle, an 8-type cycle,
and `SImplicitKey`, which is in neither.

§4 prices a walk in the only currency the arms have: a LINK, one citation of a
sub-derivation's own lemma.  One walk carrying every conclusion costs `links`;
two walks cost `2 * links + (links - arms)`, because the second must re-cite
the first at every composition node.  For the whole closure that is **319
against 790**.

Both numbers were checked against compiled Lean before they were pinned.  The
flow cycle — 8 types, 41 arms, the bottom cycle of the mutual family — was
proved three ways in `L4YAML/Scratch` (DOCS item 235): one mutual block
carrying span, MONOTONE and the strict bound (8 lemmas, 41 arms, 123
citations), and the same cycle as two mutual blocks (16 lemmas, 82 arms, 328
citations).  §4's formula reproduces both from the environment alone.

## What this does not say

Nothing here proves the column law over the grammar.  §2 discharges the base
case and the exception — the three `SBBreak` resets, where the strict bound is
the only place it is not vacuous, and `[202] l-document-prefix`'s byte-order
mark, the arm that refuted item 233's equality — and everything else is a
price.
-/

set_option autoImplicit false

namespace Tests.Guards.ColumnWalkPrice

open Lean Lean.Meta Lean.Elab
open L4YAML (YamlContext)
open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan
open L4YAML.CharPredicates

/-! ## §1 Two conclusions, and why the strict one cannot travel alone -/

/-- MONOTONE: the column never exceeds the source column plus the span. -/
def ColMono (s s' : SurfPos) : Prop :=
  ∀ pre, Span s s' pre → s'.col ≤ s.col + pre.length

/-- STRICT: across a break the column is strictly inside the span.  This is
    item 234's surviving half, and what a `SepResidue` refuter consumes. -/
def ColBreak (s s' : SurfPos) : Prop :=
  BreakBetween s s' → ∀ pre, Span s s' pre → s'.col < pre.length

/-- The span between two positions is unique, so the two statements above are
    about one list and not about whichever one a proof happens to produce. -/
lemma span_unique {s s' : SurfPos} {p q : List Char}
    (hp : Span s s' p) (hq : Span s s' q) : p = q := by
  simp only [Span] at hp hq
  exact List.append_cancel_right (hp.symm.trans hq)

lemma span_trans {s s₁ s' : SurfPos} {p q : List Char}
    (hp : Span s s₁ p) (hq : Span s₁ s' q) : Span s s' (p ++ q) := by
  simp only [Span] at *; rw [hp, hq, List.append_assoc]

/-- MONOTONE composes with itself and asks for nothing else. -/
lemma mono_comp {s s₁ s' : SurfPos} {p q : List Char}
    (hp : Span s s₁ p) (hq : Span s₁ s' q)
    (h1 : ColMono s s₁) (h2 : ColMono s₁ s') : ColMono s s' := by
  intro pre hpre
  have : pre = p ++ q := span_unique hpre (span_trans hp hq)
  subst this
  have a1 := h1 p hp
  have a2 := h2 q hq
  simp only [List.length_append]; omega

/-- STRICT composes only when the LATER half also carries MONOTONE. -/
lemma break_comp {s s₁ s' : SurfPos} {p q : List Char}
    (hp : Span s s₁ p) (hq : Span s₁ s' q)
    (b1 : ColBreak s s₁) (b2 : ColBreak s₁ s') (m2 : ColMono s₁ s') :
    ColBreak s s' := by
  intro hbr pre hpre
  have hpq : pre = p ++ q := span_unique hpre (span_trans hp hq)
  subst hpq
  simp only [List.length_append]
  obtain ⟨pre', hspan', ch, hmem, hbrk⟩ := hbr
  have : pre' = p ++ q := span_unique hspan' (span_trans hp hq)
  subst this
  rcases List.mem_append.mp hmem with hin | hin
  · have := b1 ⟨p, hp, ch, hin, hbrk⟩ p hp
    have := m2 q hq
    omega
  · have := b2 ⟨q, hq, ch, hin, hbrk⟩ q hq
    omega

/-- A break, then a long line: the strict bound holds on both halves. -/
def cutA : SurfPos := ⟨['\n', 'a'], 0⟩
def cutB : SurfPos := ⟨['a'], 0⟩
def cutC : SurfPos := ⟨[], 5⟩

lemma cutA_span : Span cutA cutB ['\n'] := rfl
lemma cutB_span : Span cutB cutC ['a'] := rfl

lemma cutA_break : ColBreak cutA cutB := by
  intro _ pre hpre
  have : pre = ['\n'] := span_unique hpre cutA_span
  subst this; simp [cutB]

lemma cutB_break : ColBreak cutB cutC := by
  rintro ⟨pre, hspan, ch, hmem, hbr⟩
  have : pre = ['a'] := span_unique hspan cutB_span
  subst this
  simp only [List.mem_singleton] at hmem
  subst hmem
  simp [isLineBreakProp, isLineFeedProp, isCarriageReturnProp] at hbr

lemma cutA_break_total : BreakBetween cutA cutC :=
  ⟨['\n', 'a'], rfl, '\n', by simp, by simp [isLineBreakProp, isLineFeedProp]⟩

/-- **The strict bound does not compose with itself.**  This is why the walk
    carries two conclusions and not one. -/
lemma strict_alone_refuted :
    ¬ (∀ a b c : SurfPos, ColBreak a b → ColBreak b c → ColBreak a c) := by
  intro h
  have := h cutA cutB cutC cutA_break cutB_break cutA_break_total ['\n', 'a'] rfl
  simp [cutC] at this

/-- …and MONOTONE is exactly what rules the counterexample out. -/
lemma counterexample_violates_mono : ¬ ColMono cutB cutC := by
  intro h
  have := h ['a'] cutB_span
  simp [cutB, cutC] at this

/-! ## §2 The bundle, its base case, and its one exception -/

/-- What one pass carries: the span, MONOTONE, and the strict bound. -/
def ColLaw (s s' : SurfPos) : Prop :=
  (∃ pre, Span s s' pre) ∧ ColMono s s' ∧ ColBreak s s'

/-- Composition is self-contained — this is what makes it ONE walk. -/
lemma ColLaw.trans {a b c : SurfPos} (h : ColLaw b c) (h' : ColLaw a b) :
    ColLaw a c := by
  obtain ⟨⟨q, hq⟩, m2, b2⟩ := h
  obtain ⟨⟨p, hp⟩, m1, b1⟩ := h'
  exact ⟨⟨p ++ q, span_trans hp hq⟩, mono_comp hp hq m1 m2, break_comp hp hq b1 b2 m2⟩

lemma ColLaw.zeroWidth (s : SurfPos) : ColLaw s s := by
  refine ⟨⟨[], rfl⟩, ?_, ?_⟩
  · intro pre hpre
    have : pre = [] := span_unique hpre (by simp [Span])
    subst this; simp
  · rintro ⟨pre, hspan, ch, hmem, _⟩
    have : pre = [] := span_unique hspan (by simp [Span])
    subst this; simp at hmem

/-- **The span walk is a projection of the column walk**, not a second pass. -/
lemma colLaw_to_suffix {a b : SurfPos} (h : ColLaw a b) : b.chars <:+ a.chars := by
  obtain ⟨⟨pre, hp⟩, _, _⟩ := h
  exact ⟨pre, hp.symm⟩

/-- **The base case.**  `[28] b-break` is where the strict bound is not
    vacuous: all three arms write column 0 and all three eat a literal break. -/
lemma sbBreak_law {a b : SurfPos} (h : SBBreak a b) : ColLaw a b := by
  cases h with
  | crLf rest col =>
    refine ⟨⟨['\r', '\n'], rfl⟩, ?_, ?_⟩
    · intro pre hpre
      have : pre = ['\r', '\n'] := span_unique hpre rfl
      subst this; simp
    · intro _ pre hpre
      have : pre = ['\r', '\n'] := span_unique hpre rfl
      subst this; simp
  | cr rest col =>
    refine ⟨⟨['\r'], rfl⟩, ?_, ?_⟩
    · intro pre hpre
      have : pre = ['\r'] := span_unique hpre rfl
      subst this; simp
    · intro _ pre hpre
      have : pre = ['\r'] := span_unique hpre rfl
      subst this; simp
  | lf rest col =>
    refine ⟨⟨['\n'], rfl⟩, ?_, ?_⟩
    · intro pre hpre
      have : pre = ['\n'] := span_unique hpre rfl
      subst this; simp
    · intro _ pre hpre
      have : pre = ['\n'] := span_unique hpre rfl
      subst this; simp

/-- **The exception survives the bundle.**  `[202] l-document-prefix`'s
    byte-order mark refuted item 233's EQUALITY; it satisfies MONOTONE and the
    strict bound, because eating a character without a break only makes the
    span longer. -/
lemma bom_step {rest : List Char} {col : Nat} {s' : SurfPos}
    (h : ColLaw ⟨rest, col⟩ s') : ColLaw ⟨'﻿' :: rest, col⟩ s' := by
  obtain ⟨⟨p, hp⟩, m, b⟩ := h
  simp only [Span] at hp
  refine ⟨⟨'﻿' :: p, by simp [Span, hp]⟩, ?_, ?_⟩
  · intro pre hpre
    have : pre = '﻿' :: p := span_unique hpre (by simp [Span, hp])
    subst this
    have h2 : s'.col ≤ col + p.length := m p hp
    show s'.col ≤ col + ('\uFEFF' :: p).length
    simp only [List.length_cons]; omega
  · rintro ⟨pre', hspan', ch, hmem, hbrk⟩ pre hpre
    have e1 : pre = '﻿' :: p := span_unique hpre (by simp [Span, hp])
    have e2 : pre' = '﻿' :: p := span_unique hspan' (by simp [Span, hp])
    subst e1; subst e2
    simp only [List.mem_cons] at hmem
    rcases hmem with rfl | hin
    · simp [isLineBreakProp, isLineFeedProp, isCarriageReturnProp] at hbrk
    · have := b ⟨p, hp, ch, hin, hbrk⟩ p hp
      simp only [List.length_cons]; omega

/-! ## §3 The recursion's real shape

A walk is one lemma per production, but only a CYCLE needs a fixpoint.  This
reads the population item 234 censused and reports its strongly connected
components — edges taken from constructor PREMISES, because a constructor's
conclusion names its own type and would make every production a self-loop. -/

/-- The item-234 population: `L4YAML.Surface` inductives relating two
    positions. -/
def isSurfRel (t : Expr) : MetaM Bool :=
  forallTelescope t fun xs body => do
    unless body.isProp || body.isSort do return false
    if xs.size < 2 then return false
    let a ← inferType xs[xs.size - 2]!
    let b ← inferType xs[xs.size - 1]!
    return a.isConstOf ``SurfPos && b.isConstOf ``SurfPos

-- 2026-10-23 ([162]): +2 acyclic sccs — `SCIndentationIndicator` and `SCChompingIndicator`, both leaves.
-- 2026-10-24 (B3 [66] col-0 threading): the explicit JSON-key twins (`explicitJsonKeyAdjacentValue`,
-- `explicitPairJsonAdjacentValue`) add two flow arms.
def expectedCycles : String :=
  "types=81 sccs=64 cyclic=8 acyclic=56 cyclicTypes=25 cyclicArms=91 largest=10"
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `types` 79 → 81, `cyclicTypes` 23 → 25, `cyclicArms` 81 → 89, `largest` 9 → 10 —
-- the two JSON-node families join the flow SCC (`SCFlowJsonContent` ↔ `SFlowSequence`/`SFlowMapping`).

/-! ## §4 What a walk costs

A LINK is a constructor premise that is itself a production between two
positions — the one place a walk cites a sub-derivation's own lemma.  One pass
carrying every conclusion costs one citation per link.  Two passes cost twice
that, plus one re-citation of the first pass at every composition node, and a
composition node is a link that is not the first of its arm. -/

-- 2026-10-23 ([162]): +5 arms / +3 links — the `[163]`/`[164]` indicator leaves under `SCBBlockHeader`.
-- 2026-10-24 (B3 [66] col-0 threading): the explicit JSON-key twins (`explicitJsonKeyAdjacentValue`,
-- `explicitPairJsonAdjacentValue`) add two flow arms.
-- 2026-10-26 (item 367, `[82]`): `SLDirective` 1 → 3 arms (`yaml`/`tag`/`reserved`), each with its own literal-prefix and digit/handle/uri links: arms 182 → 184, links 356 → 367, twoWalks 886 → 917.
def expectedPrice : String :=
  "arms=184 links=367 oneWalk=367 twoWalks=917 defProds=9 defCitations=42"
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `arms` 172 → 180, `links`/`oneWalk` 324 → 342, `twoWalks` 800 → 846, `defCitations` 39 → 40.

/-- The two cycles, priced the same way.  `flow` is the one the compiled
    experiment walked three times. -/
-- 2026-10-24 (B3 [66] col-0 threading): the explicit JSON-key twins (`explicitJsonKeyAdjacentValue`,
-- `explicitPairJsonAdjacentValue`) add two flow arms.
def expectedCyclePrice : String :=
  "flow arms=51 links=155 oneWalk=155 twoWalks=414 | block arms=26 links=63 \
oneWalk=63 twoWalks=163"
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): flow `arms` 41 → 49, `links`/`oneWalk` 123 → 141,
-- `twoWalks` 328 → 374 — the two JSON-node families enter the flow cycle; block unchanged.


/-! ## §5 What the walk can already cite, and what it cannot

Every link is a citation of the sub-production's own lemma, so the walk's
input supply is the set of productions that HAVE one.  `SurfaceSpan.lean` and
`SurfaceSpanSupply.lean` together supply 84 of the 92 productions a link can
point at.  The eight this census does not reach are seven `abbrev`s — item
229's five, plus `SBlockLinePrefix` and `SENode` — where a walk cites the
aliased production's lemma and needs no statement of its own, and
`SLYamlStream`, which §6 reads and finds missing because it is FALSE.

The reading is over the census's own import closure, so it measures what a
walk compiled HERE could cite; the same census run without
`SurfaceSpanSupply.lean` in scope reports a supply that is short by the
fifteen lemmas that module carries.  `Tests/Guards/Proofs/SuffixGapAudit.lean`
(DOCS item 236) splits the eight and carries the arm-connectivity census that
says which side a production falls on. -/

-- 2026-10-23 ([162]): +2 productions, both with suffix lemmas — `SCIndentationIndicator`, `SCChompingIndicator`.
def expectedSupply : String :=
-- 2026-10-24 ([148]/[149] JSON-key adjacent value): `productions` 94 → 96, `withSuffixLemma` 86 → 88; `missing` unchanged.
  "productions=96 withSuffixLemma=88 missing=8 documentLayerMissing=1"

run_cmd Command.liftTermElabM do
  let env ← getEnv
  -- the population, in a deterministic order
  let mut pop : Array Name := #[]
  let mut arms : Std.HashMap Name Nat := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    let .inductInfo ind := ci | continue
    unless (`L4YAML.Surface).isPrefixOf nm do continue
    unless (← isSurfRel ind.type) do continue
    pop := pop.push nm
    arms := arms.insert nm ind.ctors.length
  pop := pop.qsort (·.toString < ·.toString)
  let popSet : NameSet := pop.foldl (·.insert ·) {}
  -- premises, once: the edges of §3 and the links of §4 are the same reading
  let mut succ : Std.HashMap Name (List Name) := {}
  let mut totalArms := 0
  let mut totalLinks := 0
  let mut armLinks : Std.HashMap Name Nat := {}
  let mut defProds : Std.HashMap Name Nat := {}
  for t in pop do
    let some (.inductInfo ind) := env.find? t | continue
    let mut outs : NameSet := {}
    let mut tLinks := 0
    for c in ind.ctors do
      let some ci := env.find? c | throwError "{c} is gone from the environment"
      let (heads, links, defs) ← forallTelescope ci.type fun xs _ => do
        let mut hs : NameSet := {}
        let mut k := 0
        let mut ds : Array Name := #[]
        for x in xs do
          let ty ← inferType x
          unless (← isProp ty) do continue
          let some h := ty.getAppFn.constName? | continue
          -- a LINK relates two positions; a `def` production counts too
          let isLink ← match env.find? h with
            | some hci => isSurfRel hci.type
            | none => pure false
          unless isLink do continue
          k := k + 1
          if popSet.contains h then hs := hs.insert h else ds := ds.push h
        return (hs, k, ds)
      for h in heads.toList do outs := outs.insert h
      for d in defs do defProds := defProds.insert d (defProds.getD d 0 + 1)
      totalArms := totalArms + 1
      tLinks := tLinks + links
    totalLinks := totalLinks + tLinks
    armLinks := armLinks.insert t tLinks
    succ := succ.insert t outs.toList
  -- strongly connected components, by mutual reachability
  let sc : Name → List Name := fun n => succ.getD n []
  let mut rch : Std.HashMap Name NameSet := {}
  for t in pop do
    let mut seen : NameSet := {}
    let mut front := sc t
    while !front.isEmpty do
      let x := front.head!
      front := front.tail!
      unless seen.contains x do
        seen := seen.insert x
        front := front ++ sc x
    rch := rch.insert t seen
  let r : Name → NameSet := fun n => rch.getD n {}
  let mut sccs : Array (Array Name) := #[]
  let mut placed : NameSet := {}
  for t in pop do
    if placed.contains t then continue
    let mut grp := #[t]
    for u in pop do
      if u == t then continue
      if (r t).contains u && (r u).contains t then grp := grp.push u
    for g in grp do placed := placed.insert g
    sccs := sccs.push grp
  let isCyclic : Array Name → Bool := fun g => g.size > 1 || (r g[0]!).contains g[0]!
  let cyc := sccs.filter isCyclic
  let cycTypes := cyc.foldl (fun a g => a + g.size) 0
  let cycArms := cyc.foldl (fun a g => a + g.foldl (fun b n => b + arms.getD n 0) 0) 0
  let largest := cyc.foldl (fun a g => max a g.size) 0
  let gotCycles := s!"types={pop.size} sccs={sccs.size} cyclic={cyc.size} \
acyclic={sccs.size - cyc.size} cyclicTypes={cycTypes} cyclicArms={cycArms} \
largest={largest}"
  if gotCycles != expectedCycles then
    throwError "the recursion's shape moved.\nexpected: {expectedCycles}\n\
      got:      {gotCycles}\n  cycles: \
      {cyc.toList.map (fun g => g.toList.map (·.getString!))}"
  -- §4: the price
  let dpCount := defProds.toList.foldl (fun a x => a + x.2) 0
  let twoWalks := fun (l a : Nat) => 3 * l - a
  let gotPrice := s!"arms={totalArms} links={totalLinks} oneWalk={totalLinks} \
twoWalks={twoWalks totalLinks totalArms} defProds={defProds.size} \
defCitations={dpCount}"
  if gotPrice != expectedPrice then
    throwError "the walk's price moved.\nexpected: {expectedPrice}\n\
      got:      {gotPrice}\n  def-valued productions: \
      {defProds.toList.map (fun x => (x.1.getString!, x.2))}"
  -- the two multi-type cycles, named by a member rather than by size
  let cycOf : Name → Array Name := fun n =>
    (cyc.find? (fun g => g.contains n)).getD #[]
  let price : Array Name → String := fun g =>
    let a := g.foldl (fun b n => b + arms.getD n 0) 0
    let l := g.foldl (fun b n => b + armLinks.getD n 0) 0
    s!"arms={a} links={l} oneWalk={l} twoWalks={twoWalks l a}"
  let flow := cycOf ((`L4YAML.Surface).str "SFlowNode")
  let blk := cycOf ((`L4YAML.Surface).str "SBlockNode")
  if flow.isEmpty || blk.isEmpty then
    throwError "a named cycle vanished: flow={flow.size} block={blk.size}"
  let gotCP := s!"flow {price flow} | block {price blk}"
  if gotCP != expectedCyclePrice then
    throwError "a cycle's price moved.\nexpected: {expectedCyclePrice}\n\
      got:      {gotCP}"

  -- §5: the supply
  let mut prods : NameSet := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    unless (`L4YAML.Surface).isPrefixOf nm do continue
    if (`noConfusionType).isSuffixOf nm || (`below).isSuffixOf nm ||
       (`rec).isSuffixOf nm || (`brecOn).isSuffixOf nm then continue
    match ci with
    | .inductInfo _ => if ← isSurfRel ci.type then prods := prods.insert nm
    | .defnInfo _ => if ← isSurfRel ci.type then prods := prods.insert nm
    | _ => pure ()
  let mut covered : NameSet := {}
  for (nm, ci) in env.constants.toList do
    if nm.isInternal then continue
    match ci with | .thmInfo _ => pure () | _ => continue
    let us := ci.type.getUsedConstants
    unless us.contains ``List.IsSuffix do continue
    for u in us do if prods.contains u then covered := covered.insert u
  let missing := prods.toList.filter (!covered.contains ·)
  let inDoc := missing.filter fun n =>
    match env.getModuleIdxFor? n with
    | some idx => env.header.moduleNames[idx.toNat]! == `L4YAML.Surface.Document
    | none => false
  let gotSupply := s!"productions={prods.size} withSuffixLemma={covered.size} \
missing={missing.length} documentLayerMissing={inDoc.length}"
  if gotSupply != expectedSupply then
    throwError "the span supply moved.\nexpected: {expectedSupply}\n\
      got:      {gotSupply}\n  missing: {missing.map (·.getString!)}"

/-! ## §6 One of the twenty-three is missing because it is FALSE

`[211] l-yaml-stream` has no span lemma, and it cannot have one.  Its
`scannerDrop` arm takes `SLYamlStream s s₁` and `SSLComments s₂ s'` with `s₁`
and `s₂` UNRELATED — the module docstring calls the gap opaque — so the
conclusion `SLYamlStream s s'` rests on evidence that never connects `s` to
`s'`.  Below is a derivation whose target holds three characters its source
never had.

So "23 productions without a span lemma" is not 23 unpaid obligations.  Some
of them are refutations, and the precondition for a column walk that reaches
the document layer is row 12's own β.5 work — retiring `scannerDrop` — not 23
more lemmas. -/

/-- The empty stream: every position derives itself. -/
lemma stream_refl (s : SurfPos) : SLYamlStream s s :=
  SLYamlStream.single s s s s (GStar.nil _) (GOpt.none _) (GStar.nil _)

/-- `[77] s-l-comments` admits a zero-width derivation at column 0. -/
lemma sslComments_refl (chars : List Char) :
    SSLComments ⟨chars, 0⟩ ⟨chars, 0⟩ :=
  SSLComments.startOfLine chars ⟨chars, 0⟩ (GStar.nil _)

/-- Through `scannerDrop`, the stream relates any position to any position at
    column 0 — including one holding characters the source never had. -/
lemma stream_anything (s : SurfPos) (chars : List Char) :
    SLYamlStream s ⟨chars, 0⟩ :=
  SLYamlStream.scannerDrop s s ⟨chars, 0⟩ ⟨chars, 0⟩
    (stream_refl s) (sslComments_refl chars)

/-- **The suffix law is false at the top production.** -/
lemma stream_suffix_refuted :
    ¬ (∀ a b : SurfPos, SLYamlStream a b → b.chars <:+ a.chars) := by
  intro h
  have := h ⟨['a'], 0⟩ ⟨['b', 'b', 'b'], 0⟩ (stream_anything _ _)
  have hl := this.length_le
  simp at hl

/-- …and with it the span, so `ColLaw` cannot hold there either. -/
lemma stream_span_refuted :
    ¬ (∀ a b : SurfPos, SLYamlStream a b → ∃ pre, Span a b pre) := by
  intro h
  obtain ⟨pre, hpre⟩ := h ⟨['a'], 0⟩ ⟨['b', 'b', 'b'], 0⟩ (stream_anything _ _)
  simp only [Span] at hpre
  have := congrArg List.length hpre
  simp at this

/-- Which is the same statement about the bundle this file prices. -/
lemma stream_colLaw_refuted :
    ¬ (∀ a b : SurfPos, SLYamlStream a b → ColLaw a b) := fun h =>
  stream_span_refuted fun a b hs => (h a b hs).1

end Tests.Guards.ColumnWalkPrice
