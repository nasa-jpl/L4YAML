/-! # Reflection 516 — a faithful proof-mirror inherits its DEPENDENCY's axiom profile

R516 lands the first sub-brick of the map fold cluster (`mapHRec_of_root_and_emit`, brick (2)):
`mapWholeStreamWellTyped` + `mapFoldTotal_of_context`, the `some false`/`{`/`}` dual of the seq
context pair `seqWholeStreamWellTyped` / `seqFoldTotal_of_context`.  The proofs are a faithful
text-swap mirror — and yet the axiom audit comes out DIFFERENT:

* `seqWholeStreamWellTyped` → `[propext, Classical.choice, Quot.sound]` (clean)
* `mapWholeStreamWellTyped` → `[propext, sorryAx, Classical.choice, Quot.sound]` (carries `sorryAx`)

The asymmetry is invisible in the proof TEXT.  It comes entirely from a DEPENDENCY: both lemmas read
boundary/`WellTyped` facts off a structure lemma, but the SEQ structure lemma
(`scanFiltered_emitSeq_nonempty_structure`) had its `FlowSubrangesOk := sorry` residual RELOCATED out
at R442, while the MAP one (`scanFiltered_emitMap_nonempty_structure`) still discharges its
`ParseEntryFlowMapOk` conjunct with that `sorry` INLINE.  So every map context provider inherits
`sorryAx` — even though `mapWholeStreamWellTyped` never reads the tainted conjunct, only the clean
boundary fields.

The crux this brick pins:

* **Axiom inheritance is at CONSTANT-dependency granularity, not field-usage granularity.**  A lemma
  that projects only the CLEAN field off a structure value `⟨clean, tainted⟩` STILL inherits the
  taint, because `#print axioms` walks the syntactic dependency closure of every referenced constant —
  it does not prune constructor fields the proof happens not to reduce.  So a "pure text-swap mirror"
  claim must be qualified at the axiom layer: audit the `#print axioms` of the mirror's DEPENDENCIES,
  not just its proof body.

* **A cleanup that fixed one sibling may never have been mirrored on the other.**  The R442 relocation
  cleaned the seq structure lemma; the map structure lemma never got it.  When two siblings diverge in
  axiom profile despite identical proofs, look for an asymmetric cleanup upstream — and either mirror
  it (a separate brick) or state the inheritance honestly.

This demo (self-contained core Lean, no imports) models the phenomenon with a custom `axiom` standing
in for the real `sorryAx`: a `Struct` whose hard conjunct is proved via the axiom in the TAINTED
sibling but `trivial`-y in the CLEAN one, and two "whole-stream" readers with BYTE-IDENTICAL bodies
(`·.boundary`) — one reading the clean struct, one the tainted.  `#guard_msgs` pins that the clean
reader sheds the axiom while the tainted reader inherits it, even though neither touches the hard
field.  `demo` (which touches the tainted half) carries `[relocated_residual]`.

## R517 — the COMPLEMENT: a map-axis mirror over a CLEAN dependency stays clean

R516 showed a map-axis mirror INHERITS `sorryAx` by reading the tainted map structure lemma.  R517
lands the map enclosure primitive `MapEnclosed` + `mapEnclosed_descend`/`mapEnclosed_advance` (the
`{`-pushes-`false` mirror of `SeqEnclosed` + its two edges), and its axiom audit comes out
`[propext, Quot.sound]` — axiom-CLEAN, no `sorryAx`, not even the `Classical.choice` the seq
`WellTyped`-plumbing carries.  It is the SAME map axis as the tainted context pair, yet clean —
because its dependency closure reads only pure `btFold`/`WellTyped` plumbing, NEVER the structure
lemma.

So the sharpening: **axiom taint tracks the DEPENDENCY CLOSURE, not the axis.**  "Map-axis ⇒ tainted"
is false; a map-axis brick is clean iff its closure avoids the sorry-bearing structure lemma — which
makes the dependency-closure principle PREDICTIVE, not just diagnostic.  The model below adds a SECOND
clean dependency `btFoldPlumbing` and a map-axis reader `mapEnclosedReader` over it: same map framing
as the tainted `mapWhole`, but axiom-free, because the dependency it reads is clean. -/

namespace MirrorInheritsDependencyAxioms

/-- Stand-in for the real `sorryAx` an inline `:= sorry` introduces.  In the real file this is the
    `FlowSubrangesOk := sorry` inside `scanFiltered_emitMap_nonempty_structure` (sorry #4). -/
axiom relocated_residual : True

/-- A structure lemma's bundle: a CLEAN boundary fact `[0,a)` plus a HARD conjunct (the parser-ok
    obligation `ParseEntryFlowMapOk`, in the real lemma proved through `FlowSubrangesOk`). -/
structure Struct where
  boundary : Nat        -- the clean field the whole-stream reader actually uses
  parserOk : True       -- the hard field; in the map lemma it routes through the residual

/-- **CLEAN sibling** (mirror of the seq structure lemma, post-R442 relocation): the hard conjunct is
    discharged WITHOUT the residual, so the constant depends on no axiom. -/
def cleanStruct : Struct := ⟨7, trivial⟩

/-- **TAINTED sibling** (mirror of the map structure lemma): the SAME bundle, but the hard conjunct is
    discharged through `relocated_residual` — so the constant carries that axiom in its closure. -/
def taintedStruct : Struct := ⟨7, relocated_residual⟩

/-- **Whole-stream reader over the CLEAN sibling** (mirror of `seqWholeStreamWellTyped`).  Body reads
    only `.boundary`. -/
def seqWhole : Nat := cleanStruct.boundary

/-- **Whole-stream reader over the TAINTED sibling** (mirror of `mapWholeStreamWellTyped`).  BYTE-
    IDENTICAL body `·.boundary` — only the struct it reads differs.  Never touches `.parserOk`. -/
def mapWhole : Nat := taintedStruct.boundary

/-- The clean reader's fact — axiom-free. -/
theorem seq_clean : seqWhole = 7 := rfl

/-- The tainted reader's fact — proof-IDENTICAL `rfl`, yet it inherits `relocated_residual` because the
    referenced constant `taintedStruct` mentions it, though `.boundary` never evaluates it. -/
theorem map_tainted : mapWhole = 7 := rfl

/-- The two readers are proof-identical (both reduce to `7`) — the mirror really is a text-swap.  This
    deliverable touches the tainted half, so it carries the taint. -/
theorem demo : seqWhole = 7 ∧ mapWhole = 7 ∧ seqWhole = mapWhole :=
  ⟨rfl, rfl, rfl⟩

/-- A RUN: the inherited axiom does not change the VALUE — both readers deliver `7`. -/
theorem run : seqWhole = mapWhole := rfl

-- ── R517 complement: a map-axis reader over a CLEAN dependency stays clean ──

/-- **A CLEAN map-axis dependency** (mirror of the pure `btFold`/`WellTyped` plumbing the map enclosure
    primitive reads): a map-side constant with NO residual in its closure.  `MapEnclosed`/
    `mapEnclosed_*` depend on plumbing like THIS, not on the tainted map structure lemma. -/
def btFoldPlumbing : Struct := ⟨7, trivial⟩

/-- **Map-axis reader over the CLEAN plumbing** (mirror of `MapEnclosed`/`mapEnclosed_*`).  Same
    map-axis framing as `mapWhole` and a BYTE-IDENTICAL body (`·.boundary`), but its dependency closure
    avoids the tainted struct — so it is axiom-free.  Taint tracks the DEPENDENCY, not the axis. -/
def mapEnclosedReader : Nat := btFoldPlumbing.boundary

/-- The map-axis enclosure reader's fact — axiom-FREE, though `mapWhole` (same axis, tainted
    dependency) carries `[relocated_residual]`.  The contrast IS the R517 lesson. -/
theorem mapEnclosed_clean : mapEnclosedReader = 7 := rfl

end MirrorInheritsDependencyAxioms

-- Axiom audit (machine-checked: `#guard_msgs` pins the profile and fails the build if it ever drifts;
-- it also CONSUMES the info output, so the audit no longer pollutes the build log).
-- The CLEAN reader sheds the axiom; the TAINTED reader INHERITS it though it reads only the clean
-- field — exactly why `mapWholeStreamWellTyped` carries `sorryAx` while its seq twin does not.
/-- info: 'MirrorInheritsDependencyAxioms.seq_clean' does not depend on any axioms -/
#guard_msgs in
#print axioms MirrorInheritsDependencyAxioms.seq_clean

/-- info: 'MirrorInheritsDependencyAxioms.map_tainted' depends on axioms: [MirrorInheritsDependencyAxioms.relocated_residual] -/
#guard_msgs in
#print axioms MirrorInheritsDependencyAxioms.map_tainted

/-- info: 'MirrorInheritsDependencyAxioms.demo' depends on axioms: [MirrorInheritsDependencyAxioms.relocated_residual] -/
#guard_msgs in
#print axioms MirrorInheritsDependencyAxioms.demo

-- R517 complement: the map-axis reader over the CLEAN dependency sheds the axiom — same axis as the
-- tainted `mapWhole`, but clean, because the dependency it reads is clean.  Taint tracks the
-- DEPENDENCY, not the axis: exactly why `MapEnclosed` is `[propext, Quot.sound]` while the map context
-- pair `mapWholeStreamWellTyped`/`mapFoldTotal_of_context` carry `sorryAx`.
/-- info: 'MirrorInheritsDependencyAxioms.mapEnclosed_clean' does not depend on any axioms -/
#guard_msgs in
#print axioms MirrorInheritsDependencyAxioms.mapEnclosed_clean
