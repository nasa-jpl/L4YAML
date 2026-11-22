/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Surface.Node
public import L4YAML.Spec.CharPredicates
public import L4YAML.Proofs.Foundation.SurfaceSpan

@[expose] public section Blanket

/-! # The closed flow node re-read as `[154]`'s key (DOCS item 56)

    A completed depth-0 flow collection followed by a same-line `:` is
    `[193] c-s-implicit-json-key`'s node — `c-flow-json-node(0, block-key)`.
    The collection was built at the frame's index in the `flow-out`/`flow-in`
    contexts; the KEY contexts read the same characters with two changes:
    the index drops to 0 and every interior separation must be
    `s-separate-in-line` (the key is single-line — which the scanner's
    §7.4 implicit-key checks enforce on everything that reaches a `:`).

    This file is the conversion family: one lemma per type of the flow
    grammar's mutual block, each `… → (converted) ∨ <residue>`, the residue
    taken on a multi-line interior (a `.commented` separation or a multi-line
    scalar body) — inputs the scanner refuses as keys anyway.

    **Corrected at item 228**, in two places.  The residue was written `True`
    everywhere, which made every one of these lemmas a statement that
    `Or.inr trivial` proves; §0 gives the leaf residues their own names.  And
    "taken exactly on a multi-line interior" was imprecise for the separation:
    `[70]`'s comment-delimited arm admits a derivation that crosses no line at
    all (`[79] s-l-comments` has a comment-free arm at column 0 and
    `[63] s-indent(0)` consumes nothing), so that arm and
    `[80] s-separate-in-line` hold at the same zero-width span.

    **Item 230 finishes the separation.**  The arm is not the residue; it is
    an arm, and it keeps its own name (`SepCommentedArm`).  What the
    conversion declines on is `SepResidue` — the span crossed a line, or the
    input ran out — because `[77] b-comment` ends a comment in exactly those
    two ways.  That residue is closed under widening, so it carries out of an
    interior span to an outer one, which is what `True` was standing in for:
    `props_toKey` carries it.

    **Item 231 rebuilds the eighteen motives.**  The eight flow motives carry
    `SepResidue`; the ten block ones stay `True`, because no flow constructor
    mentions a block type and no block motive is ever fed to a flow arm.  Each
    of the 82 declining sites is one `sepResidue_widen` over a fold of the
    arm's OWN piece-suffix facts — §0's lemma, moved there from §4 because §3
    became its heaviest reader.

    **Item 232 exports all eight.**  §3 is a `mutual` block of eight
    structurally recursive lemmas rather than one recursor application, so
    every type of the flow grammar has a conversion of its own and nothing
    here is recovered by INVERTING another conclusion.  `SFlowContent` is the
    one that needed it: `flowContent_toBlockKey` used to wrap its input in
    `SFlowNode.content`, convert, and peel the node back, and the peel has
    four arms the node conversion rules out none of, so its residue could only
    be `True`.  No conclusion in this file ends in `True` now.

    The price is measured, not estimated.  Mutual structural recursion does
    not share a fixpoint: each of the eight is its own `brecOn` over the same
    41 arms, so each carries all 82 declining sites and all 73 widenings, and
    the eight proof terms are the same size to the node
    (`Tests/Guards/Proofs/SurfaceSpanCensus.lean` §5, `exports=8`).  Seven
    more conclusions cost seven more copies of the block.

    **Item 233 measures the demand, and it is zero.**  None of the eight
    exports is applied anywhere outside this file: what the library reads is
    the three `*_toBlockKey` wrappers, from two declarations in `StreamAccum`,
    and both discard the residue.  So do all six of §4's payments, which
    nothing has instantiated.  §8 of the census carries the counts and the
    reason.

    The context pairing is tracked as `KeyPair c tc`: the top node converts
    `(flowOut → blockKey)`, interiors `(flowIn → flowKey)`, and `inFlowCtx`
    maps the first onto the second — `isNsPlainSafe` is EQUAL on each pair,
    which is what the plain leaves transport. -/

set_option autoImplicit false

namespace L4YAML.Proofs.FlowKeyLift

open L4YAML.Surface
open L4YAML.Proofs.SurfaceSpan

/-- The two source→target context pairings the key re-reading makes. -/
def KeyPair (c tc : L4YAML.YamlContext) : Prop :=
  (c = .flowOut ∧ tc = .blockKey) ∨ (c = .flowIn ∧ tc = .flowKey)

lemma KeyPair.inFlow {c tc : L4YAML.YamlContext} (h : KeyPair c tc) :
    KeyPair (inFlowCtx c) (inFlowCtx tc) := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact Or.inr ⟨rfl, rfl⟩

lemma KeyPair.tc_key {c tc : L4YAML.YamlContext} (h : KeyPair c tc) :
    tc = .blockKey ∨ tc = .flowKey := by
  rcases h with ⟨_, rfl⟩ | ⟨_, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- `ns-plain-safe` is EQUAL on each pairing. -/
lemma KeyPair.safe {c tc : L4YAML.YamlContext} (h : KeyPair c tc) {ch : Char}
    (hs : isNsPlainSafe c ch) : isNsPlainSafe tc ch := by
  rcases h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> exact hs

/-! ## §0 What the conversion declines ON (DOCS item 228)

Each conversion below used to end in `… ∨ True`, and `Or.inr trivial` proves
that whatever is on the left: the statement was not a theorem about the
conversion at all.  These are the residues those `True`s stood for, read off
the arm each proof actually takes.  They are `def`s so the residue carries its
own docstring and so a census can select on it.

They are NOT interchangeable, and that is the finding item 228 recorded and
item 229 proved: three of them consume a line break by construction, so a
consumer holding a single-line key can refute them — which is the entire worth
of a narrowing.  The separation's ARM cannot be refuted that way, and §4 gives
the reason rather than the observation: its span can be EMPTY
(`sepCommentedArm_span_can_be_empty`).  Item 230 replaced it with a residue
that can, at the price of one more hypothesis from the consumer: a key is
followed by a `:`, so the separation did not run the input out. -/

/-- **The arm a separation declines ON**: `[70] s-separate-lines(n)`'s
    comment-delimited arm, for which `[69]`'s key contexts have no production.
    Items 228 and 229 carried this as `sep_toKey`'s residue and item 229
    proved it is not one — §4's two witnesses derive it at spans carrying no
    break, one empty and one three characters long, so no consumer can refute
    it.  It keeps a name because those witnesses are what fixes the shape of
    the residue below. -/
def SepCommentedArm (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ s₁, SSLComments s s₁ ∧ SFlowLinePrefix n s₁ s'

/-- **The residue a separation leaves** (item 230): the span crossed a line,
    or the input ran out.  `[77] b-comment` ends a comment in exactly those
    two ways, so a comment-delimited separation that is not itself inline hits
    one of them — `separateLines_inline_or_breakOrEnd`.  Two facts refute it,
    and they are the two `[193] c-s-implicit-json-key` states about everything
    that reaches a `:`: the key crosses no line, and a `:` follows it, so the
    input did not run out.

    **Nothing in the library holds either fact** (item 233).  `BreakBetween`
    occurs in the type of twenty-five declarations, eleven here and fourteen
    in `SurfaceSpan`, and in none anywhere else; what `[193]` states is a fact
    about the scanner's line counter, and the scanner/surface correspondence
    carries characters, a column, an offset and an indent bound, but not the
    line.  `Tests/Guards/Proofs/SurfaceSpanCensus.lean` §8 keeps the count. -/
def SepResidue (s s' : SurfPos) : Prop := BreakBetween s s' ∨ atEnd s'

/-- **The residue widens.**  An interior residue is a residue of any span that
    brackets it — the property `True` was standing in for at item 228's
    interior sites.  The outer derivation's constructor gives the two suffix
    facts and `L4YAML/Proofs/Foundation/SurfaceSpan.lean` gives them for all 74
    production types, which is what §3's rebuilt arms spend: item 231 moved
    this lemma up from §4, because every one of `flowNode_toKey`'s 82 declining
    sites is one application of it. -/
lemma sepResidue_widen {s a b s' : SurfPos} (hl : a.chars <:+ s.chars)
    (hr : s'.chars <:+ b.chars) (h : SepResidue a b) : SepResidue s s' :=
  breakOrEnd_extend_right hr (breakOrEnd_extend_left hl h)

/-- **The residue a plain scalar leaves**: at least one
    `[134] s-ns-plain-next-line(n,c)` past `[133] ns-plain-one-line(c)`.  Every
    one of them opens with `[28] b-break`. -/
def PlainResidue (n : Nat) (c : L4YAML.YamlContext) (s s' : SurfPos) : Prop :=
  ∃ s₁, SNsPlainOneLine c s s₁ ∧ GPlus (SSNsPlainNextLine n c) s₁ s'

/-- **The residue a double-quoted scalar leaves**: `[116]
    nb-double-multi-line(n)`'s `multi` arm, inside the quotes.  `[113]
    s-double-break(n)` is an escaped break or a folded one; either consumes
    one. -/
def DoubleResidue (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ s₁ s₂ a b, GLit '"' s s₁ ∧ SNbDoubleOneLine s₁ a ∧ SSDoubleBreak n a b ∧
    SNbDoubleMultiLine n b s₂ ∧ GLit '"' s₂ s'

/-- **The residue a single-quoted scalar leaves**: `[125]
    nb-single-multi-line(n)`'s `multi` arm, inside the quotes, whose second
    component is `[28] b-break` itself. -/
def SingleResidue (n : Nat) (s s' : SurfPos) : Prop :=
  ∃ s₁ s₂ a b cc d, GLit '\'' s s₁ ∧ SNbSingleOneLine s₁ a ∧ SBBreak a b ∧
    GStar (SLEmpty n .flowIn) b cc ∧ SFlowLinePrefix n cc d ∧
    SNbSingleMultiLine n d s₂ ∧ GLit '\'' s₂ s'

/-! **The three scalar residues each carry a `[28] b-break` inside their span**,
    so each of them IS a `SepResidue` through its left disjunct.  Item 231
    moved these three up from §4: §3's `SFlowContent` arms decline through
    `plain_toKey`, `singleQuoted_toKey` and `doubleQuoted_toKey`, and a
    `SepResidue`-shaped motive needs the bridge at the site. -/

lemma plainResidue_break {n : Nat} {c : L4YAML.YamlContext} {s s' : SurfPos}
    (h : PlainResidue n c s s') : BreakBetween s s' := by
  obtain ⟨_, hone, hplus⟩ := h
  match hplus with
  | .mk _ _ _ hx hrest =>
    refine breakBetween_extend_right ?_
      (breakBetween_extend_left ?_ (ssNsPlainNextLine_break hx))
    · exact gstar_suffix (fun _ _ => ssNsPlainNextLine_suffix) hrest
    · exact snsPlainOneLine_suffix hone

lemma doubleResidue_break {n : Nat} {s s' : SurfPos} (h : DoubleResidue n s s') :
    BreakBetween s s' := by
  obtain ⟨_, _, _, _, hq1, hone, hbrk, hrest, hq2⟩ := h
  refine breakBetween_extend_right ?_ (breakBetween_extend_left ?_ (ssDoubleBreak_break hbrk))
  · exact (glit_suffix hq2).trans (snbDoubleMultiLine_suffix hrest)
  · exact (snbDoubleOneLine_suffix hone).trans (glit_suffix hq1)

lemma singleResidue_break {n : Nat} {s s' : SurfPos} (h : SingleResidue n s s') :
    BreakBetween s s' := by
  obtain ⟨_, _, _, _, _, _, hq1, hone, hbrk, hempty, hpre, hrest, hq2⟩ := h
  refine breakBetween_extend_right ?_ (breakBetween_extend_left ?_ (breakBetween_of_break hbrk))
  · exact (glit_suffix hq2).trans ((snbSingleMultiLine_suffix hrest).trans
      ((sFlowLinePrefix_suffix hpre).trans (gstar_suffix (fun _ _ => sLEmpty_suffix) hempty)))
  · exact (snbSingleOneLine_suffix hone).trans (glit_suffix hq1)
/-! ## §1 Scalar leaves -/

lemma plainFirst_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlainFirst c s s') : SNsPlainFirst tc s s' := by
  cases h with
  | nonIndicator ch rest col hSafe hNotInd =>
    exact SNsPlainFirst.nonIndicator tc ch rest col (hp.safe hSafe) hNotInd
  | dashSafe next rest col hSafe =>
    exact SNsPlainFirst.dashSafe tc next rest col (hp.safe hSafe)
  | colonSafe next rest col hSafe =>
    exact SNsPlainFirst.colonSafe tc next rest col (hp.safe hSafe)
  | questionSafe next rest col hSafe =>
    exact SNsPlainFirst.questionSafe tc next rest col (hp.safe hSafe)

lemma plainChar_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlainChar c s s') : SNsPlainChar tc s s' := by
  cases h with
  | safe ch rest col hSafe hNC hNH =>
    exact SNsPlainChar.safe tc ch rest col (hp.safe hSafe) hNC hNH
  | colonSafe prev next rest col hSafe =>
    exact SNsPlainChar.colonSafe tc prev next rest col (hp.safe hSafe)

lemma plainEntry_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNbNsPlainInLineEntry c s s') :
    SNbNsPlainInLineEntry tc s s' :=
  match h with
  | .mk _ _ s₁ _ hws hch => SNbNsPlainInLineEntry.mk tc _ s₁ _ hws (plainChar_toKey hp hch)
  | .hash _ _ _ hlit => SNbNsPlainInLineEntry.hash tc _ _ hlit

lemma plainOneLine_toKey {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlainOneLine c s s') : SNsPlainOneLine tc s s' := by
  cases h with
  | mk s₁ _ hfirst hentries =>
    refine SNsPlainOneLine.mk tc _ s₁ _ (plainFirst_toKey hp hfirst) ?_
    clear hfirst
    induction hentries with
    | nil => exact GStar.nil _
    | cons a b cc hx _ ih => exact GStar.cons a b cc (plainEntry_toKey hp hx) ih

/-- A plain scalar re-reads at the key context when it is single-line. -/
lemma plain_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlain n c s s') :
    SNsPlain 0 tc s s' ∨ PlainResidue n c s s' := by
  have h' : SNsPlainMultiLine n c s s' := by
    rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact h
  cases h' with
  | mk _ _ hone hnext =>
    cases hnext with
    | nil =>
      have hone' := plainOneLine_toKey hp hone
      rcases hp.tc_key with rfl | rfl <;> exact Or.inl hone'
    | cons _ _ _ hx hrest => exact Or.inr ⟨_, hone, GPlus.mk _ _ _ hx hrest⟩

/-- A double-quoted scalar re-reads at the key context when its body is
    single-line (the one-line body is context- and index-free). -/
lemma doubleQuoted_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCDoubleQuoted n c s s') :
    SCDoubleQuoted 0 tc s s' ∨ DoubleResidue n s s' := by
  cases h with
  | mk s₁ s₂ _ hq1 hbody hq2 =>
    have hbody' : SNbDoubleMultiLine n s₁ s₂ := by
      rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hbody
    cases hbody' with
    | single _ _ hl =>
      have hkey : SNbDoubleText 0 tc s₁ s₂ := by
        rcases hp.tc_key with rfl | rfl <;> exact hl
      exact Or.inl (SCDoubleQuoted.mk 0 tc _ _ _ _ hq1 hkey hq2)
    | multi _ a b _ _ hone hbrk hrest =>
      exact Or.inr ⟨_, _, a, b, hq1, hone, hbrk, hrest, hq2⟩

/-- The single-quoted twin. -/
lemma singleQuoted_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCSingleQuoted n c s s') :
    SCSingleQuoted 0 tc s s' ∨ SingleResidue n s s' := by
  cases h with
  | mk s₁ s₂ _ hq1 hbody hq2 =>
    have hbody' : SNbSingleMultiLine n s₁ s₂ := by
      rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact hbody
    cases hbody' with
    | single _ _ hl =>
      have hkey : SNbSingleText 0 tc s₁ s₂ := by
        rcases hp.tc_key with rfl | rfl <;> exact hl
      exact Or.inl (SCSingleQuoted.mk 0 tc _ _ _ _ hq1 hkey hq2)
    | multi _ a b cc d _ hone hbrk hempty hpre hrest =>
      exact Or.inr ⟨_, _, a, b, cc, d, hq1, hone, hbrk, hempty, hpre, hrest, hq2⟩

/-! ## §2 Separations and properties -/

/-- **A separation re-reads at the key context when it is inline**, and what
    it leaves otherwise is a residue and no longer an arm (item 230).  The
    zero-width derivation item 229 exhibited — `[79]`'s `startOfLine` arm with
    no comments, then `[71]` at index 0 — now returns the LEFT disjunct,
    because `[71] s-flow-line-prefix(n)` is itself an inline separation and
    `[66]` concatenates (`sFlowLinePrefix_separateInLine`,
    `separateInLine_trans`). -/
lemma sep_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SSeparate n c s s') :
    SSeparate 0 tc s s' ∨ SepResidue s s' := by
  have h' : SSeparateLines n s s' := by
    rcases hp with ⟨rfl, _⟩ | ⟨rfl, _⟩ <;> exact h
  rcases separateLines_inline_or_breakOrEnd h' with hsil | hres
  · refine Or.inl ?_
    rcases hp.tc_key with rfl | rfl <;> exact hsil
  · exact Or.inr hres

lemma sepOpt_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : GOpt (SSeparate n c) s s') :
    GOpt (SSeparate 0 tc) s s' ∨ SepResidue s s' := by
  cases h with
  | none => exact Or.inl (GOpt.none _)
  | some _ hx =>
    rcases sep_toKey hp hx with hx' | hr
    · exact Or.inl (GOpt.some _ _ hx')
    · exact Or.inr hr

/-- **Properties re-read at the key context when their interior separation is
    inline** (the tag/anchor tokens themselves are context-free), and the
    residue is now the interior separation's own, carried OUT to this
    conclusion's span (item 230).  That carry is the thing item 228 could not
    do and wrote `True` for: `SepResidue` is closed under widening in both
    directions — `breakOrEnd_extend_left`, `breakOrEnd_extend_right` — because
    a break in a sub-span is a break in the span, and an input that ran out
    stays out. -/
lemma props_toKey {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCNsProperties n c s s') :
    SCNsProperties 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .tagFirst _ _ _ _ _ htag hopt =>
    match hopt with
    | .none _ => exact Or.inl (SCNsProperties.tagFirst 0 tc _ _ _ htag (GOpt.none _))
    | .some _ _ (.mk _ _ _ hsep hanchor) =>
      rcases sep_toKey hp hsep with hsep' | hres
      · exact Or.inl (SCNsProperties.tagFirst 0 tc _ _ _ htag
          (GOpt.some _ _ (GSeq.mk _ _ _ hsep' hanchor)))
      · exact Or.inr (breakOrEnd_extend_right (scNsAnchorProperty_suffix hanchor)
          (breakOrEnd_extend_left (scNsTagProperty_suffix htag) hres))
  | .anchorFirst _ _ _ _ _ hanchor hopt =>
    match hopt with
    | .none _ => exact Or.inl (SCNsProperties.anchorFirst 0 tc _ _ _ hanchor (GOpt.none _))
    | .some _ _ (.mk _ _ _ hsep htag) =>
      rcases sep_toKey hp hsep with hsep' | hres
      · exact Or.inl (SCNsProperties.anchorFirst 0 tc _ _ _ hanchor
          (GOpt.some _ _ (GSeq.mk _ _ _ hsep' htag)))
      · exact Or.inr (breakOrEnd_extend_right (scNsTagProperty_suffix htag)
          (breakOrEnd_extend_left (scNsAnchorProperty_suffix hanchor) hres))

/-! ## §3 The collection family

    The flow grammar is eight types of an 18-type mutual block, so the
    `induction` tactic does not apply — it refuses a mutually inductive type
    outright.  The equation compiler does: `lemma` inside `mutual` is a macro
    in this repo precisely so that it reaches `elabMutual`
    (`L4YAML/Init.lean`), and `L4YAML/Proofs/Foundation/SurfaceSpan.lean` §4
    is eighteen mutually structural lemmas over this same family.

    **Item 232 writes the conversion that way.**  Eight lemmas, one per flow
    type, each `termination_by structural h`, and the ten block types are not
    mentioned at all — the recursion never leaves the flow grammar, so a
    strict subfamily is what the checker is asked to accept, and it does.  The
    pairing is an explicit hypothesis `hp : KeyPair c tc` rather than a
    universally quantified motive, which is what lets a collection's entries
    convert at `inFlowCtx tc` (`hp.inFlow`) while its brackets convert at
    `tc`.

    Item 231 wrote it as ONE application of the family's recursor with
    eighteen motives.  That is the shape that hands back one conclusion for
    the price of all 69 minor premises, and the seven it does not hand back
    are what item 232 is for.

    Every interior piece converts or the whole conversion returns `True`.
    That `True` is the one item 228 could not replace: the residue belongs to
    an interior span and this conclusion is about the outer one, so the
    proposition that would carry it out is a statement about the CHARACTERS
    between the two.  The 18 types below have 69 constructors, and at item 228
    not one lemma related any of them to a suffix; item 229 wrote all
    eighteen, and item 230 gave the separation a residue that widens along
    them (`props_toKey` is the first conclusion to carry one out of an
    interior span).

    **Item 231 spent that mechanically**, and the shape is uniform: every
    constructor is a chain of pieces `s = p₀ → … → p_k = s'`, a declining site
    sits at piece `i` holding `SepResidue pᵢ pᵢ₊₁`, and the two facts
    `sepResidue_widen` wants are the folds `chain(0…i-1)` and
    `chain(i+1…k-1)` of the arm's other pieces' suffix lemmas.  Nothing in an
    arm is chosen: the `have`s below are exactly the pieces some chain reads,
    which is why the three arms that decline nowhere (`SFlowNode.alias`,
    `SFlowSeqEntry.emptyKeyEmpty`, `SFlowMapEntry.emptyKeyEmpty`) carry none.
    Item 232 kept all of it — the same 41 arms, the same 82 sites, the same
    105 `have`s — and changed only who calls whom: an interior premise reads
    its OWN lemma where it used to read an induction hypothesis.

    The three `SFlowContent` scalar arms are the one place the residue is not
    already a `SepResidue`: `plain_toKey`, `singleQuoted_toKey` and
    `doubleQuoted_toKey` return their own, and each is bridged by its §0
    `*_break` lemma into the left disjunct. -/

mutual

/-- **The conversion**: a flow node re-reads at index 0 in the paired
    key context, unless some interior crossed a line. -/
lemma flowNode_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowNode n c s s') (hp : KeyPair c tc) :
    SFlowNode 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .alias _ _ _ _ ha =>
    exact Or.inl (SFlowNode.alias 0 tc _ _ ha)
  | .content _ _ _ _ hc =>
    rcases flowContent_toKey hc hp with hc2 | hres
    · exact Or.inl (SFlowNode.content 0 tc _ _ hc2)
    · exact Or.inr hres
  | .propsContent _ _ _ _ _ _ hprops hsep hc =>
    have qprops := scNsProperties_suffix hprops
    have qsep := sSeparate_suffix hsep
    have qc := sFlowContent_suffix hc
    rcases props_toKey hp hprops with hprops2 | hres
    · rcases sep_toKey hp hsep with hsep2 | hres
      · rcases flowContent_toKey hc hp with hc2 | hres
        · exact Or.inl (SFlowNode.propsContent 0 tc _ _ _ _ hprops2 hsep2 hc2)
        · exact Or.inr (sepResidue_widen (qsep.trans qprops) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qprops qc hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qc.trans qsep) hres)
  | .propsEmpty _ _ _ _ hprops =>
    rcases props_toKey hp hprops with hprops2 | hres
    · exact Or.inl (SFlowNode.propsEmpty 0 tc _ _ hprops2)
    · exact Or.inr hres
termination_by structural h

/-- `[161] c-flow-json-content` re-reads: the four bracket forms and the
    three scalar styles. -/
lemma flowContent_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowContent n c s s') (hp : KeyPair c tc) :
    SFlowContent 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .plain _ _ _ _ hpl =>
    rcases plain_toKey hp hpl with hpl2 | hres
    · exact Or.inl (SFlowContent.plain 0 tc _ _ hpl2)
    · exact Or.inr (Or.inl (plainResidue_break hres))
  | .flowSeq _ _ _ _ hfs =>
    rcases flowSequence_toKey hfs hp with hfs2 | hres
    · exact Or.inl (SFlowContent.flowSeq 0 tc _ _ hfs2)
    · exact Or.inr hres
  | .flowMap _ _ _ _ hfm =>
    rcases flowMapping_toKey hfm hp with hfm2 | hres
    · exact Or.inl (SFlowContent.flowMap 0 tc _ _ hfm2)
    · exact Or.inr hres
  | .singleQ _ _ _ _ hsq =>
    rcases singleQuoted_toKey hp hsq with hsq2 | hres
    · exact Or.inl (SFlowContent.singleQ 0 tc _ _ hsq2)
    · exact Or.inr (Or.inl (singleResidue_break hres))
  | .doubleQ _ _ _ _ hdq =>
    rcases doubleQuoted_toKey hp hdq with hdq2 | hres
    · exact Or.inl (SFlowContent.doubleQ 0 tc _ _ hdq2)
    · exact Or.inr (Or.inl (doubleResidue_break hres))
termination_by structural h

/-- `[137] c-flow-sequence` re-reads; its entries convert at
    `inFlowCtx tc`, its brackets at `tc`. -/
lemma scFlowJsonContent_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCFlowJsonContent n c s s') (hp : KeyPair c tc) :
    SCFlowJsonContent 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .flowSeq _ _ _ _ hfs =>
    rcases flowSequence_toKey hfs hp with hfs2 | hres
    · exact Or.inl (SCFlowJsonContent.flowSeq 0 tc _ _ hfs2)
    · exact Or.inr hres
  | .flowMap _ _ _ _ hfm =>
    rcases flowMapping_toKey hfm hp with hfm2 | hres
    · exact Or.inl (SCFlowJsonContent.flowMap 0 tc _ _ hfm2)
    · exact Or.inr hres
  | .singleQ _ _ _ _ hsq =>
    rcases singleQuoted_toKey hp hsq with hsq2 | hres
    · exact Or.inl (SCFlowJsonContent.singleQ 0 tc _ _ hsq2)
    · exact Or.inr (Or.inl (singleResidue_break hres))
  | .doubleQ _ _ _ _ hdq =>
    rcases doubleQuoted_toKey hp hdq with hdq2 | hres
    · exact Or.inl (SCFlowJsonContent.doubleQ 0 tc _ _ hdq2)
    · exact Or.inr (Or.inl (doubleResidue_break hres))
termination_by structural h

lemma scFlowJsonNode_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SCFlowJsonNode n c s s') (hp : KeyPair c tc) :
    SCFlowJsonNode 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .content _ _ _ _ hc =>
    rcases scFlowJsonContent_toKey hc hp with hc2 | hres
    · exact Or.inl (SCFlowJsonNode.content 0 tc _ _ hc2)
    · exact Or.inr hres
  | .propsContent _ _ _ _ _ _ hprops hsep hc =>
    have qprops := scNsProperties_suffix hprops
    have qsep := sSeparate_suffix hsep
    have qc := scFlowJsonContent_suffix hc
    rcases props_toKey hp hprops with hprops2 | hres
    · rcases sep_toKey hp hsep with hsep2 | hres
      · rcases scFlowJsonContent_toKey hc hp with hc2 | hres
        · exact Or.inl (SCFlowJsonNode.propsContent 0 tc _ _ _ _ hprops2 hsep2 hc2)
        · exact Or.inr (sepResidue_widen (qsep.trans qprops) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qprops qc hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qc.trans qsep) hres)
termination_by structural h

lemma flowSequence_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowSequence n c s s') (hp : KeyPair c tc) :
    SFlowSequence 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .empty _ _ _ _ _ _ hl1 hsep hl2 =>
    have ql1 := glit_suffix hl1
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · exact Or.inl (SFlowSequence.empty 0 tc _ _ _ _ hl1 hsep2 hl2)
    · exact Or.inr (sepResidue_widen ql1 ql2 hres)
  | .nonempty _ _ _ _ _ _ _ hl1 hsep hent hl2 =>
    have ql1 := glit_suffix hl1
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qent := sFlowSeqEntries_suffix hent
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · rcases flowSeqEntries_toKey hent hp.inFlow with hent2 | hres
      · exact Or.inl (SFlowSequence.nonempty 0 tc _ _ _ _ _ hl1 hsep2 hent2 hl2)
      · exact Or.inr (sepResidue_widen (qsep.trans ql1) ql2 hres)
    · exact Or.inr (sepResidue_widen ql1 (ql2.trans qent) hres)
termination_by structural h

/-- `[138] ns-s-flow-seq-entries` re-reads — the comma-separated run. -/
lemma flowSeqEntries_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowSeqEntries n c s s') (hp : KeyPair c tc) :
    SFlowSeqEntries 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .single _ _ _ _ _ hent hsep =>
    have qent := sFlowSeqEntry_suffix hent
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    rcases flowSeqEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (SFlowSeqEntries.single 0 tc _ _ _ hent2 hsep2)
      · exact Or.inr (sepResidue_widen qent (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) qsep hres)
  | .consMore _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 hrest =>
    have qent := sFlowSeqEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qrest := sFlowSeqEntries_suffix hrest
    rcases flowSeqEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowSeqEntries_toKey hrest hp with hrest2 | hres
          · exact Or.inl (SFlowSeqEntries.consMore 0 tc _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b hrest2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcomma.trans (qsep1.trans qent))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) qrest hres)
      · exact Or.inr (sepResidue_widen qent (qrest.trans (qsep2.trans qcomma)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qrest.trans (qsep2.trans (qcomma.trans qsep1))) hres)
  | .consEnd _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 =>
    have qent := sFlowSeqEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    rcases flowSeqEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (SFlowSeqEntries.consEnd 0 tc _ _ _ _ _ hent2 hsep1b hcomma hsep2b)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qent (qsep2.trans qcomma) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qsep2.trans (qcomma.trans qsep1)) hres)
termination_by structural h

/-- `[139] ns-flow-seq-entry` re-reads: a node, or a single pair in
    any of its ten written forms. -/
lemma flowSeqEntry_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowSeqEntry n c s s') (hp : KeyPair c tc) :
    SFlowSeqEntry 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .node _ _ _ _ hn =>
    rcases flowNode_toKey hn hp with hn2 | hres
    · exact Or.inl (SFlowSeqEntry.node 0 tc _ _ hn2)
    · exact Or.inr hres
  | .pairValue _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := sFlowNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := sFlowNode_suffix hv
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sep_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (SFlowSeqEntry.pairValue 0 tc _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .pairEmpty _ _ _ _ _ _ hk hsep hcolon =>
    have qk := sFlowNode_suffix hk
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qcolon := glit_suffix hcolon
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (SFlowSeqEntry.pairEmpty 0 tc _ _ _ _ hk2 hsep2 hcolon)
      · exact Or.inr (sepResidue_widen qk qcolon hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qcolon.trans qsep) hres)
  | .pairJsonAdjacentValue _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := scFlowJsonNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qv := sFlowNode_suffix hv
    rcases scFlowJsonNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (SFlowSeqEntry.pairJsonAdjacentValue 0 tc _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .explicitPairJsonAdjacentValue _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := scFlowJsonNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep3
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases scFlowJsonNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sepOpt_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (SFlowSeqEntry.explicitPairJsonAdjacentValue 0 tc _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .explicitPairValue _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := sFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := sSeparate_suffix hsep3
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sep_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (SFlowSeqEntry.explicitPairValue 0 tc _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .explicitPairEmpty _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := sFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (SFlowSeqEntry.explicitPairEmpty 0 tc _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) qcolon hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qcolon.trans qsep2) hres)
    · exact Or.inr (sepResidue_widen qq (qcolon.trans (qsep2.trans qk)) hres)
  | .explicitPairKeyOnly _ _ _ _ _ _ hq hsep hk =>
    have qq := glit_suffix hq
    have qsep := sSeparate_suffix hsep
    have qk := sFlowNode_suffix hk
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · exact Or.inl (SFlowSeqEntry.explicitPairKeyOnly 0 tc _ _ _ _ hq hsep2 hk2)
      · exact Or.inr (sepResidue_widen (qsep.trans qq) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qq qk hres)
  | .explicitPairEmptyNodes _ _ _ _ _ hq hsep =>
    have qq := glit_suffix hq
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (SFlowSeqEntry.explicitPairEmptyNodes 0 tc _ _ _ hq hsep2)
    · exact Or.inr (sepResidue_widen qq (List.suffix_refl _) hres)
  | .emptyKeyValue _ _ _ _ _ _ hcolon hsep hv =>
    have qcolon := glit_suffix hcolon
    have qsep := sSeparate_suffix hsep
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hv hp with hv2 | hres
      · exact Or.inl (SFlowSeqEntry.emptyKeyValue 0 tc _ _ _ _ hcolon hsep2 hv2)
      · exact Or.inr (sepResidue_widen (qsep.trans qcolon) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qcolon qv hres)
  | .emptyKeyEmpty _ _ _ _ hcolon =>
    exact Or.inl (SFlowSeqEntry.emptyKeyEmpty 0 tc _ _ hcolon)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ hq hsep1 hcolon hsep2 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases sep_toKey hp hsep2 with hsep2b | hres
      · rcases flowNode_toKey hv hp with hv2 | hres
        · exact Or.inl (SFlowSeqEntry.explicitEmptyKeyValue 0 tc _ _ _ _ _ _ hq hsep1b hcolon hsep2b hv2)
        · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qq))) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qq)) qv hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep2.trans qcolon)) hres)
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ hq hsep hcolon =>
    have qq := glit_suffix hq
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (SFlowSeqEntry.explicitEmptyKeyEmpty 0 tc _ _ _ _ hq hsep2 hcolon)
    · exact Or.inr (sepResidue_widen qq qcolon hres)
termination_by structural h

/-- `[140] c-flow-mapping` re-reads; the same split as the sequence. -/
lemma flowMapping_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowMapping n c s s') (hp : KeyPair c tc) :
    SFlowMapping 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .empty _ _ _ _ _ _ hl1 hsep hl2 =>
    have ql1 := glit_suffix hl1
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · exact Or.inl (SFlowMapping.empty 0 tc _ _ _ _ hl1 hsep2 hl2)
    · exact Or.inr (sepResidue_widen ql1 ql2 hres)
  | .nonempty _ _ _ _ _ _ _ hl1 hsep hent hl2 =>
    have ql1 := glit_suffix hl1
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qent := sFlowMapEntries_suffix hent
    have ql2 := glit_suffix hl2
    rcases sepOpt_toKey hp hsep with hsep2 | hres
    · rcases flowMapEntries_toKey hent hp.inFlow with hent2 | hres
      · exact Or.inl (SFlowMapping.nonempty 0 tc _ _ _ _ _ hl1 hsep2 hent2 hl2)
      · exact Or.inr (sepResidue_widen (qsep.trans ql1) ql2 hres)
    · exact Or.inr (sepResidue_widen ql1 (ql2.trans qent) hres)
termination_by structural h

/-- `[141] ns-s-flow-map-entries` re-reads — the comma-separated run. -/
lemma flowMapEntries_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowMapEntries n c s s') (hp : KeyPair c tc) :
    SFlowMapEntries 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .single _ _ _ _ _ hent hsep =>
    have qent := sFlowMapEntry_suffix hent
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    rcases flowMapEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (SFlowMapEntries.single 0 tc _ _ _ hent2 hsep2)
      · exact Or.inr (sepResidue_widen qent (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) qsep hres)
  | .consMore _ _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 hrest =>
    have qent := sFlowMapEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qrest := sFlowMapEntries_suffix hrest
    rcases flowMapEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowMapEntries_toKey hrest hp with hrest2 | hres
          · exact Or.inl (SFlowMapEntries.consMore 0 tc _ _ _ _ _ _ hent2 hsep1b hcomma hsep2b hrest2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcomma.trans (qsep1.trans qent))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) qrest hres)
      · exact Or.inr (sepResidue_widen qent (qrest.trans (qsep2.trans qcomma)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qrest.trans (qsep2.trans (qcomma.trans qsep1))) hres)
  | .consEnd _ _ _ _ _ _ _ hent hsep1 hcomma hsep2 =>
    have qent := sFlowMapEntry_suffix hent
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcomma := glit_suffix hcomma
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    rcases flowMapEntry_toKey hent hp with hent2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (SFlowMapEntries.consEnd 0 tc _ _ _ _ _ hent2 hsep1b hcomma hsep2b)
        · exact Or.inr (sepResidue_widen (qcomma.trans (qsep1.trans qent)) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen qent (qsep2.trans qcomma) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qsep2.trans (qcomma.trans qsep1)) hres)
termination_by structural h

/-- `[142] ns-flow-map-entry` re-reads: eleven written forms of one
    key/value pair. -/
lemma flowMapEntry_toKey {n : Nat} {c tc : L4YAML.YamlContext} {s s' : SurfPos}
    (h : SFlowMapEntry n c s s') (hp : KeyPair c tc) :
    SFlowMapEntry 0 tc s s' ∨ SepResidue s s' := by
  match h with
  | .explicitValue _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := sFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := sSeparate_suffix hsep3
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sep_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (SFlowMapEntry.explicitValue 0 tc _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .explicitEmpty _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := sFlowNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · exact Or.inl (SFlowMapEntry.explicitEmpty 0 tc _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) qcolon hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qcolon.trans qsep2) hres)
    · exact Or.inr (sepResidue_widen qq (qcolon.trans (qsep2.trans qk)) hres)
  | .explicitKeyOnly _ _ _ _ _ _ hq hsep hk =>
    have qq := glit_suffix hq
    have qsep := sSeparate_suffix hsep
    have qk := sFlowNode_suffix hk
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hk hp with hk2 | hres
      · exact Or.inl (SFlowMapEntry.explicitKeyOnly 0 tc _ _ _ _ hq hsep2 hk2)
      · exact Or.inr (sepResidue_widen (qsep.trans qq) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qq qk hres)
  | .implicitValue _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := sFlowNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := sFlowNode_suffix hv
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sep_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (SFlowMapEntry.implicitValue 0 tc _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .implicitEmpty _ _ _ _ _ _ hk hsep hcolon =>
    have qk := sFlowNode_suffix hk
    have qsep := gopt_suffix (fun _ _ => sSeparate_suffix) hsep
    have qcolon := glit_suffix hcolon
    rcases flowNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep with hsep2 | hres
      · exact Or.inl (SFlowMapEntry.implicitEmpty 0 tc _ _ _ _ hk2 hsep2 hcolon)
      · exact Or.inr (sepResidue_widen qk qcolon hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qcolon.trans qsep) hres)
  | .jsonKeyAdjacentValue _ _ _ _ _ _ _ _ hk hsep1 hcolon hsep2 hv =>
    have qk := scFlowJsonNode_suffix hk
    have qsep1 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qv := sFlowNode_suffix hv
    rcases scFlowJsonNode_toKey hk hp with hk2 | hres
    · rcases sepOpt_toKey hp hsep1 with hsep1b | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases flowNode_toKey hv hp with hv2 | hres
          · exact Or.inl (SFlowMapEntry.jsonKeyAdjacentValue 0 tc _ _ _ _ _ _ hk2 hsep1b hcolon hsep2b hv2)
          · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qk))) (List.suffix_refl _) hres)
        · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qk)) qv hres)
      · exact Or.inr (sepResidue_widen qk (qv.trans (qsep2.trans qcolon)) hres)
    · exact Or.inr (sepResidue_widen (List.suffix_refl _) (qv.trans (qsep2.trans (qcolon.trans qsep1))) hres)
  | .explicitJsonKeyAdjacentValue _ _ _ _ _ _ _ _ _ _ hq hsep1 hk hsep2 hcolon hsep3 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qk := scFlowJsonNode_suffix hk
    have qsep2 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep2
    have qcolon := glit_suffix hcolon
    have qsep3 := gopt_suffix (fun _ _ => sSeparate_suffix) hsep3
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases scFlowJsonNode_toKey hk hp with hk2 | hres
      · rcases sepOpt_toKey hp hsep2 with hsep2b | hres
        · rcases sepOpt_toKey hp hsep3 with hsep3b | hres
          · rcases flowNode_toKey hv hp with hv2 | hres
            · exact Or.inl (SFlowMapEntry.explicitJsonKeyAdjacentValue 0 tc _ _ _ _ _ _ _ _ hq hsep1b hk2 hsep2b hcolon hsep3b hv2)
            · exact Or.inr (sepResidue_widen (qsep3.trans (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq))))) (List.suffix_refl _) hres)
          · exact Or.inr (sepResidue_widen (qcolon.trans (qsep2.trans (qk.trans (qsep1.trans qq)))) qv hres)
        · exact Or.inr (sepResidue_widen (qk.trans (qsep1.trans qq)) (qv.trans (qsep3.trans qcolon)) hres)
      · exact Or.inr (sepResidue_widen (qsep1.trans qq) (qv.trans (qsep3.trans (qcolon.trans qsep2))) hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep3.trans (qcolon.trans (qsep2.trans qk)))) hres)
  | .bareKey _ _ _ _ hk =>
    rcases flowNode_toKey hk hp with hk2 | hres
    · exact Or.inl (SFlowMapEntry.bareKey 0 tc _ _ hk2)
    · exact Or.inr hres
  | .emptyKeyValue _ _ _ _ _ _ hcolon hsep hv =>
    have qcolon := glit_suffix hcolon
    have qsep := sSeparate_suffix hsep
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep with hsep2 | hres
    · rcases flowNode_toKey hv hp with hv2 | hres
      · exact Or.inl (SFlowMapEntry.emptyKeyValue 0 tc _ _ _ _ hcolon hsep2 hv2)
      · exact Or.inr (sepResidue_widen (qsep.trans qcolon) (List.suffix_refl _) hres)
    · exact Or.inr (sepResidue_widen qcolon qv hres)
  | .emptyKeyEmpty _ _ _ _ hcolon =>
    exact Or.inl (SFlowMapEntry.emptyKeyEmpty 0 tc _ _ hcolon)
  | .explicitEmptyNodes _ _ _ _ _ hq hsep =>
    have qq := glit_suffix hq
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (SFlowMapEntry.explicitEmptyNodes 0 tc _ _ _ hq hsep2)
    · exact Or.inr (sepResidue_widen qq (List.suffix_refl _) hres)
  | .explicitEmptyKeyValue _ _ _ _ _ _ _ _ hq hsep1 hcolon hsep2 hv =>
    have qq := glit_suffix hq
    have qsep1 := sSeparate_suffix hsep1
    have qcolon := glit_suffix hcolon
    have qsep2 := sSeparate_suffix hsep2
    have qv := sFlowNode_suffix hv
    rcases sep_toKey hp hsep1 with hsep1b | hres
    · rcases sep_toKey hp hsep2 with hsep2b | hres
      · rcases flowNode_toKey hv hp with hv2 | hres
        · exact Or.inl (SFlowMapEntry.explicitEmptyKeyValue 0 tc _ _ _ _ _ _ hq hsep1b hcolon hsep2b hv2)
        · exact Or.inr (sepResidue_widen (qsep2.trans (qcolon.trans (qsep1.trans qq))) (List.suffix_refl _) hres)
      · exact Or.inr (sepResidue_widen (qcolon.trans (qsep1.trans qq)) qv hres)
    · exact Or.inr (sepResidue_widen qq (qv.trans (qsep2.trans qcolon)) hres)
  | .explicitEmptyKeyEmpty _ _ _ _ _ _ hq hsep hcolon =>
    have qq := glit_suffix hq
    have qcolon := glit_suffix hcolon
    rcases sep_toKey hp hsep with hsep2 | hres
    · exact Or.inl (SFlowMapEntry.explicitEmptyKeyEmpty 0 tc _ _ _ _ hq hsep2 hcolon)
    · exact Or.inr (sepResidue_widen qq qcolon hres)
termination_by structural h

end

/-- **The top wrapper**: a completed depth-0 flow node re-reads as `[154]`'s
    JSON key when it is single-line. -/
lemma flowNode_toBlockKey {n : Nat} {s s' : SurfPos}
    (h : SFlowNode n .flowOut s s') :
    SFlowNode 0 .blockKey s s' ∨ SepResidue s s' :=
  flowNode_toKey h (Or.inl ⟨rfl, rfl⟩)

/-- The same conversion one level down, for a key that a held `[96]` run
    DECORATES (`&a [1]: b`): the properties are the head's, so what the
    collection owes is `[158]`'s content, and `[161]`'s `propsContent` arm is
    assembled at the site that holds the run.

    It reads its own lemma.  Item 231 built it by wrapping the content in
    `SFlowNode.content`, converting, and PEELING — and the peel has four arms
    the node conversion rules out none of, so its residue could only be
    `True`.  `flowContent_toKey` is now a lemma in its own right, so the
    residue is the content's own. -/
lemma flowContent_toBlockKey {n : Nat} {s s' : SurfPos}
    (h : SFlowContent n .flowOut s s') :
    SFlowContent 0 .blockKey s s' ∨ SepResidue s s' :=
  flowContent_toKey h (Or.inl ⟨rfl, rfl⟩)

/-- A separation re-reads at `block-key` when it is inline — the pairing
    spelled for the one the block side uses. -/
lemma sep_toBlockKey {n : Nat} {s s' : SurfPos} (h : SSeparate n .flowOut s s') :
    SSeparate 0 .blockKey s s' ∨ SepResidue s s' :=
  sep_toKey (Or.inl ⟨rfl, rfl⟩) h

/-! ## §4 What the narrowing buys (DOCS item 229)

Item 228 narrowed six conclusions and could not say whether the narrowing was
worth anything: a residue is worth exactly what a consumer can refute
(`Tests.Guards.ConclusionObligationCensus.conclusion_eliminable_iff`), and
refuting "some interior crossed a line" needs the span — the characters
between the conclusion's own two positions — which the library could not name.
`L4YAML/Proofs/Foundation/SurfaceSpan.lean` names it, so the four residues can
now be sorted by the only question that matters.

Three carry a `[28] b-break` inside their span, so `¬ BreakBetween s s'`
refutes them — `plainResidue_break`, `doubleResidue_break` and
`singleResidue_break`, which live in §0 since item 231 made §3's scalar arms
their first readers.  The separation's ARM does not, and the two witnesses below are
the proof, not the observation: item 228's zero-width derivation has an EMPTY
span, and the `[77] b-comment` `eof` derivation has a three-character span
with no break in it, so no predicate on the span distinguishes the arm from a
separation that was never taken.

**Item 230 reads the same two witnesses forwards.**  `[77]` ends a comment
with a break OR at the end of the input, and those are the only two ways; so
the statement that IS a residue is `SepResidue` — `BreakBetween s s' ∨
atEnd s'` — and `sep_toKey` now returns the LEFT disjunct on the zero-width
derivation (`sep_toKey_left_at_zero_width`).  The second witness is the one
that forces `atEnd` into the residue: it is a comment-delimited separation
that crosses no line and is NOT inline. -/


/-- **The arm's span can be empty**, so no character predicate refutes it.
    This is `sepCommentedArm_of_startOfLine` read through the span: item 228 showed
    the arm and its own left disjunct hold together, and the reason is that
    the derivation consumes nothing at all. -/
lemma sepCommentedArm_span_can_be_empty (chars : List Char) :
    SepCommentedArm 0 ⟨chars, 0⟩ ⟨chars, 0⟩ ∧ ¬ BreakBetween ⟨chars, 0⟩ ⟨chars, 0⟩ := by
  refine ⟨⟨⟨chars, 0⟩, SSLComments.startOfLine chars _ (GStar.nil _),
    SFlowLinePrefix.mk 0 _ _ _ (SIndent.zero _) (GOpt.none _)⟩, ?_⟩
  rintro ⟨pre, hspan, ch, hmem, -⟩
  have hpre : pre = [] := by
    simp only [Span] at hspan
    simpa using hspan.symm
  exact absurd (hpre ▸ hmem) (by simp)

/-- **…and it can be non-empty and still cross no line.**  `[77] b-comment`
    ends a comment at END OF INPUT as well as at a break, so ` #c<EOF>` is a
    comment-delimited separation whose span is three characters, none of them a
    break.  Together with `sepCommentedArm_span_can_be_empty` this is why no
    predicate on the span refutes the ARM — not `BreakBetween`, and not "the
    span contains a `#`" either, since the zero-width witness has neither.

    It is also the derivation that keeps `atEnd` in `SepResidue`:
    `sepCommentedArm_at_eof_comment_not_inline` shows this span is not an
    inline separation, so the trichotomy's third disjunct is not slack. -/
lemma sepCommentedArm_at_eof_comment :
    SepCommentedArm 0 ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ ∧
      ¬ BreakBetween ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ := by
  refine ⟨⟨⟨[], 6⟩,
    SSLComments.withComment _ _ _
      (SSBComment.withSep _ _ _ _
        (SSeparateInLine.whites _ _
          (GPlus.mk _ ⟨['#', 'c'], 4⟩ _ (SSWhite.space _ 3) (GStar.nil _)))
        (GOpt.some ⟨['#', 'c'], 4⟩ ⟨[], 6⟩
          (SCNbCommentText.mk ['c'] 4 ⟨[], 6⟩
            (GStar.cons ⟨['c'], 5⟩ ⟨[], 6⟩ ⟨[], 6⟩
              (GChar.mk (p := isCommentTextChar) 'c' [] 5
                (by simp [isCommentTextChar, CharPredicates.isLineBreakProp,
                  CharPredicates.isLineFeedProp, CharPredicates.isCarriageReturnProp]))
              (GStar.nil _))))
        (SBComment.eof 6))
      (GStar.nil _),
    SFlowLinePrefix.mk 0 _ _ _ (SIndent.zero _) (GOpt.none _)⟩, ?_⟩
  rintro ⟨pre, hspan, ch, hmem, hbr⟩
  simp only [Span, List.append_nil] at hspan
  subst hspan
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
  rcases hmem with rfl | rfl | rfl <;> revert hbr <;> decide

/-- **The `eof` derivation is not an inline separation.**  `[66]` is a run of
    `[33] s-white`s and `'#'` is not one, so no derivation of
    `SSeparateInLine` spans these three characters.  This is what makes
    `atEnd` load-bearing in `SepResidue`: drop it and `sep_toKey` has no
    disjunct left for this input. -/
lemma sepCommentedArm_at_eof_comment_not_inline :
    ¬ SSeparateInLine ⟨[' ', '#', 'c'], 3⟩ ⟨[], 6⟩ := by
  intro h
  match h with
  | .whites _ _ hp =>
    match hp with
    | .mk _ _ _ hx hrest =>
      match hx with
      | .space _ _ =>
        match hrest with
        | .cons _ _ _ hy _ => cases hy

/-! ### The payment

`narrowed_conclusion_pays` (item 228's §1) with the residue discharged: a
consumer holding "this key's span crosses no line" — which is what
`[193] c-s-implicit-json-key` requires of everything that reaches a `:` —
gets the conversion outright, with no disjunction left to case on.  The
separation's payment needs one more fact from the same consumer, and it is
one a key always has: the `:` that made it a key is still in the input, so
the separation did not run the input out.

**All six are uninstantiated** (item 233), and the conditional above is why:
neither of the two declarations that read this file holds either fact, which
is what `elsewhere=0` says once it is taken over the whole library.  What a
payment costs is settled — each is a single `Or.resolve_right`, two orders of
magnitude smaller than the conversion it discharges, and one of them pays for
all 48 of that conversion's payable sites at once because the residue widens.
What is missing is the coordinate that would state the hypothesis, not a
cheaper proof; `Tests/Guards/Proofs/SurfaceSpanCensus.lean` §8 measures both
halves and `scripts/flips/item233_flow_key_head.json` prices the consumer side. -/

lemma plain_toKey_of_noBreak {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SNsPlain n c s s') (hnb : ¬ BreakBetween s s') :
    SNsPlain 0 tc s s' :=
  (plain_toKey hp h).resolve_right (fun hr => hnb (plainResidue_break hr))

lemma doubleQuoted_toKey_of_noBreak {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCDoubleQuoted n c s s') (hnb : ¬ BreakBetween s s') :
    SCDoubleQuoted 0 tc s s' :=
  (doubleQuoted_toKey hp h).resolve_right (fun hr => hnb (doubleResidue_break hr))

lemma singleQuoted_toKey_of_noBreak {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCSingleQuoted n c s s') (hnb : ¬ BreakBetween s s') :
    SCSingleQuoted 0 tc s s' :=
  (singleQuoted_toKey hp h).resolve_right (fun hr => hnb (singleResidue_break hr))

/-- **The separation's payment** (item 230): the fourth leaf, which item 229
    left with a residue no consumer could refute. -/
lemma sep_toKey_of_noResidue {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SSeparate n c s s') (hnb : ¬ BreakBetween s s')
    (hne : ¬ atEnd s') : SSeparate 0 tc s s' :=
  (sep_toKey hp h).resolve_right (fun hr => hr.elim hnb hne)

lemma sepOpt_toKey_of_noResidue {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : GOpt (SSeparate n c) s s') (hnb : ¬ BreakBetween s s')
    (hne : ¬ atEnd s') : GOpt (SSeparate 0 tc) s s' :=
  (sepOpt_toKey hp h).resolve_right (fun hr => hr.elim hnb hne)

/-- …and the property run's, which item 229 counted among the 45 blocked
    sites because its conclusion is about the OUTER span.  The residue widens,
    so the conclusion can carry it. -/
lemma props_toKey_of_noResidue {n : Nat} {c tc : L4YAML.YamlContext} (hp : KeyPair c tc)
    {s s' : SurfPos} (h : SCNsProperties n c s s') (hnb : ¬ BreakBetween s s')
    (hne : ¬ atEnd s') : SCNsProperties 0 tc s s' :=
  (props_toKey hp h).resolve_right (fun hr => hr.elim hnb hne)

/-- **Item 229's zero-width witness, converted.**  The derivation that item
    229 proved no consumer could refute — `[79]`'s `startOfLine` arm with no
    comments, then `[71]` at index 0, consuming nothing — now returns
    `sep_toKey`'s LEFT disjunct at any position that is not the end of the
    input.  This is the machine-checked form of "the residue is a partition":
    the witness is no longer a counterexample to it. -/
lemma sep_toKey_left_at_zero_width (ch : Char) (rest : List Char) :
    SSeparate 0 .blockKey ⟨ch :: rest, 0⟩ ⟨ch :: rest, 0⟩ :=
  sep_toKey_of_noResidue (n := 0) (Or.inl ⟨rfl, rfl⟩)
    (SSeparateLines.commented 0 ⟨ch :: rest, 0⟩ ⟨ch :: rest, 0⟩ ⟨ch :: rest, 0⟩
      (SSLComments.startOfLine _ _ (GStar.nil _))
      (SFlowLinePrefix.mk 0 _ _ _ (SIndent.zero _) (GOpt.none _)))
    (by
      rintro ⟨pre, hspan, c, hmem, -⟩
      have hpre : pre = [] := by
        simp only [Span] at hspan
        simpa using hspan.symm
      exact absurd (hpre ▸ hmem) (by simp))
    (by simp [atEnd])

end L4YAML.Proofs.FlowKeyLift

end Blanket
