/-!
# Reflection 442 — when a `sorry` needs a STRONGER hypothesis than its host lemma threads, RELOCATE the
# sorry (and the conjunct it feeds) to the consumer that natively HAS the strength.  Do NOT strengthen the
# host lemma's predicate: the host is a choke point: strengthening ripples the strong predicate through
# every co-consumer that never needed it (and, here, into deferred work).

Self-contained (core Lean, no `L4YAML` import) toy of the R442 finding — STEP D continued: position the
seq `FlowSubrangesOk` sorry so the seq root carrier's emit-context strength is available at it.

Context.  The seq `FlowSubrangesOk tokens := sorry` lived INSIDE `scanFiltered_emitSeq_nonempty_structure`,
a structure lemma keyed on the WEAK per-item predicate `EmitScansInFlowBlock`.  The R441 audit found: the
seq root carrier behind `FlowSubrangesOk` needs the STRONGER per-item predicate `EmitScansInFlowRecEntry`
(= `EmitScansInFlowBlock` + the extra `RecSeqEntry block` conjunct), but the host threads only `Block`, and
the only coercion runs `RecEntry → Block` (strong→weak) — the WRONG way to manufacture the strong predicate
at the sorry.

Two ways to close a predicate-STRENGTH gap at a sorry:

* **(A) STRENGTHEN the host's predicate Block → RecEntry.**  WRONG here: the host is consumed by ~9
  `Block`-only adjacency/window lemmas (and the *deferred* map side); re-keying it to `RecEntry` ripples the
  strong predicate through all of them, dragging deferred work into scope and re-keying lemmas that never
  used the strength.

* **(B) RELOCATE the sorry to a site that ALREADY has the strength.**  The host conjunct the sorry feeds
  (`h_pnok`/`ParseNodeFlowSeqOk`) is consumed by EXACTLY ONE caller (`parseStream_emitSequence`); every other
  destructure UNDERSCORED it (`_h_pnok`).  That one caller has `Grammable` → `RecEntry` via
  `emit_scans_in_flow_rec_entry`.  So MOVE the conjunct + its sorry OUT of the `Block`-keyed lemma and INTO
  the `RecEntry`-capable caller.  The Block chain is untouched; the strong predicate is in scope at the sorry.

The DISCRIMINATOR that tells (B) is available: the host conjunct that needs the strength is UNDERSCORED at
every consumer BUT ONE.  An underscore-at-every-site-but-one conjunct is a RELOCATION candidate — it is not
load-bearing for the host's other consumers, so pulling it out costs only that one consumer a few
reconstruction lines and frees the rest from a strength requirement they never used.

Frontier-NEUTRAL by construction: moving a sorry (not adding one) keeps the count.  In L4YAML the seq sorry
moved `scanFiltered_emitSeq_nonempty_structure` (`NonemptyStructure.lean`) → `parseStream_emitSequence`
(`EmitterScannability.lean`), leaving the structure lemma seq-side sorry-free and `Block`-only.  The retype
IS the progress: the seq sorry now sits where the next step wires `seqHRec_of_root_and_context` + the root
carrier with `emit_scans_in_flow_rec_entry` DIRECTLY — no coercion against the grain.

The reusable rule.  When a sorry needs a STRONGER hypothesis than its host threads, do NOT strengthen the
host's predicate (it ripples to every co-consumer of the host).  Check whether the host conjunct the sorry
feeds is UNDERSCORED at all consumers but one; if so, RELOCATE the conjunct + sorry to that one consumer,
where the strength is native.  Strengthen-at-the-consumer, not strengthen-the-producer-chain.  Keep the cheap
strong→weak coercion for the residual (windowFacts) that still wants the weak form.

This toy models the impossibility AT the weak host (Weak ⊬ ParserFact) paired with the success AT the
relocated strong site (Strong ⊢ ParserFact), and the untouched co-consumers that only used the weak fact.
-/

set_option autoImplicit false

namespace Tests.Reflections.RelocateSorryToStrongerPredicateSite

/-! ## PART 0 — two per-item predicates, strong strictly above weak; coercion runs strong→weak only. -/

/-- The WEAK per-item predicate the host lemma threads (models `EmitScansInFlowBlock`). -/
abbrev Weak (v : Nat) : Prop := 1 ≤ v

/-- The STRONG per-item predicate the root carrier needs (models `EmitScansInFlowRecEntry`,
    = `Weak` + the extra `RecSeqEntry`-style content `2 ≤ v` carries). -/
abbrev Strong (v : Nat) : Prop := 2 ≤ v

/-- The EXISTING coercion runs strong→weak — the wrong way to manufacture `Strong` at the host
    (models `emitScansInFlowBlock_of_flowRecEntry`). -/
theorem strong_to_weak {v : Nat} (h : Strong v) : Weak v := by omega

/-- The parser-level fact the sorry feeds — reachable only from `Strong`-level evidence
    (models `ParseNodeFlowSeqOk`, derived from `FlowSubrangesOk` which needs the root carrier). -/
abbrev ParserFact (v : Nat) : Prop := 2 ≤ v

/-- A `Weak`-derivable structure fact every consumer actually uses
    (models the boundary/balance/dyck/adjacency facts). -/
abbrev OtherFact (v : Nat) : Prop := 1 ≤ v

/-! ## PART 1 — the host CANNOT manufacture the strong fact: `Weak ⊬ ParserFact` (counterexample `v = 1`).
    This is why the sorry cannot be discharged inside the `Weak`-keyed host. -/

theorem host_cannot_reach_parserFact : ¬ (∀ v, Weak v → ParserFact v) := by
  intro h
  have h1 : ParserFact 1 := h 1 (by omega)   -- `Weak 1` holds (1 ≤ 1) but `ParserFact 1` needs `2 ≤ 1`
  simp only [ParserFact] at h1
  omega

/-! ## PART 2 — the RELOCATED host is `Weak`-only and sorry-free: it delivers ONLY the `Weak`-derivable
    `OtherFact`; the `ParserFact` conjunct has been pulled out.  (Models
    `scanFiltered_emitSeq_nonempty_structure` after R442: `Block`-keyed, `ParseNodeFlowSeqOk` removed.) -/

theorem structFacts (v : Nat) (hw : Weak v) : OtherFact v := hw

/-- A co-consumer that only ever used `OtherFact` and UNDERSCORED the parser fact — untouched by the
    relocation, never burdened with `Strong`.  (Models a `Block`-only adjacency/window lemma.) -/
theorem consumerA (v : Nat) (hw : Weak v) : OtherFact v := structFacts v hw

/-- Another such co-consumer: it reads the structure fact and ignores any parser-level fact entirely. -/
theorem consumerB (v : Nat) (hw : Weak v) : True := by
  have _hother := structFacts v hw   -- the `_h_pnok`-underscoring destructure: parser fact never read
  trivial

/-! ## PART 3 — the ONE consumer that needs `ParserFact`.  It natively has `Strong`, so it derives
    `OtherFact` from `structFacts` (after `strong_to_weak`) and `ParserFact` DIRECTLY from `Strong`.  The
    relocated residual (here PROVED to show non-vacuity; in L4YAML it is the seq `FlowSubrangesOk := sorry`
    awaiting the producer wiring) is owed HERE, where `Strong` is in scope — not inside the `Weak` host. -/

theorem mainCaller (v : Nat) (hs : Strong v) : ParserFact v ∧ OtherFact v := by
  have h_other : OtherFact v := structFacts v (strong_to_weak hs)
  -- Relocated derivation: `ParserFact` from the strong predicate, reachable ONLY here.
  -- (L4YAML: `have h_subranges : FlowSubrangesOk tokens := sorry`, then `flow_parser_ok_of_structure`.)
  have h_subranges : ParserFact v := hs
  exact ⟨h_subranges, h_other⟩

/-- The payoff, side by side: the parser fact is UNPROVABLE at the weak host, but PROVABLE once the sorry
    is relocated to the strong site.  Relocation turned an undischargeable obligation into a dischargeable
    one without touching the weak chain. -/
example :
    (¬ (∀ v, Weak v → ParserFact v)) ∧ (∀ v, Strong v → ParserFact v ∧ OtherFact v) :=
  ⟨host_cannot_reach_parserFact, mainCaller⟩

end Tests.Reflections.RelocateSorryToStrongerPredicateSite
