/-!
# Reflection 354 — a VESTIGIAL projection re-opens for a structure-walking consumer

Self-contained (core Lean, no `L4YAML` import) toy model of the R354 finding: a whole-structure
invariant retired as "vestigial" for a value-blind consumer (which reads only a TOP projection of it)
is LOAD-BEARING for a sibling consumer that WALKS the typed structure.  Vestigial-ness is
CONSUMER-RELATIVE.

THE SETTING.  A bracket stack is a `List Bool` (head = top of stack; `true` = enclosed by a sequence
`[`, `false` = by a mapping `{`).  A position-navigator's DESCEND arm must reject a window whose path
dips through a `{`.  Two candidate domain hypotheses: the TOP projection `topTrue` (what the gate / the
value-blind producer hands over) vs the WHOLE-path invariant `allTrue`.

THE MINIMAL PAIR.  The SAME deepest frame `true` (a nested seq), reached two ways:
* POSITIVE `[true, true]`        — all-`[` path (nested seq inside a seq).
* NEGATIVE `[true, false, true]` — through a `{` (nested seq inside a map).
They AGREE on the top projection but DISAGREE on the whole-path invariant — so the projection cannot
exclude the negative, which the structure-walker MUST reject.

THE TRANSFERABLE RULE.  Vestigial-ness is a claim about a CONSUMER, not an invariant.  When a later
consumer walks the typed structure, re-test the retired invariant with a minimal pair equal under the
projection but split by the full invariant; if it exists, the walker must carry the full invariant.
-/

namespace Tests.Reflections.VestigialProjectionReopens

set_option autoImplicit false

/-! ## The projection vs the full invariant on a bracket stack -/

/-- The TOP-of-stack projection: the immediate enclosure is a sequence.  This is what the value-blind
    producer (and the gate) reads — `SeqEnclosed` / `SeqTypedInterior`'s 2nd conjunct. -/
def topTrue : List Bool → Bool
  | b :: _ => b
  | []     => false

/-- The WHOLE-path invariant: a nonempty stack, every frame a sequence.  This is `SeqPathAllSeq`. -/
def allTrue (s : List Bool) : Bool := !s.isEmpty && s.all (· == true)

/-- POSITIVE path — nested seq reached through all `[`. -/
def posStack : List Bool := [true, true]

/-- NEGATIVE path — same deepest seq, reached through a `{`. -/
def negStack : List Bool := [true, false, true]

/-! ## The minimal pair: projection-equal, full-invariant-split -/

/-- **POSITIVE — on the all-seq path, BOTH hold.** -/
theorem pos_both : topTrue posStack = true ∧ allTrue posStack = true := ⟨rfl, rfl⟩

/-- **NEGATIVE — through a map, the TOP projection HOLDS but the whole-path invariant FAILS.**
    The negative is a window the projection cannot exclude. -/
theorem neg_top_holds_full_fails : topTrue negStack = true ∧ allTrue negStack = false := ⟨rfl, rfl⟩

/-- **THE DISCRIMINATOR — the projection is EQUAL across the pair (so the value-blind consumer cannot
    separate them), while the whole-path invariant DIFFERS (so it is the necessary discriminator).** -/
theorem projection_equal_full_separates :
    topTrue posStack = topTrue negStack ∧ allTrue posStack ≠ allTrue negStack := by
  refine ⟨rfl, ?_⟩; decide

/-! ## Consumer-relativity: vestigial for the value-blind consumer, load-bearing for the walker -/

/-- The value-blind consumer accepts a window iff its TOP projection holds (it reads nothing deeper). -/
def valueBlindAccepts (s : List Bool) : Bool := topTrue s

/-- The structure-walker may descend into a window iff its WHOLE path is all-seq (otherwise it would
    descend into a map entry that has no recursive body). -/
def walkerMayDescend (s : List Bool) : Bool := allTrue s

/-- **NEGATIVE — the value-blind consumer ADMITS the bad window** (it reads only the projection), so for
    IT the whole-path invariant is vestigial: its verdict is unchanged whether or not the deeper frame
    is a map. -/
theorem value_blind_admits_bad_window : valueBlindAccepts negStack = true := rfl

/-- **POSITIVE — the structure-walker REJECTS the bad window** the value-blind consumer admitted: the
    whole-path invariant is LOAD-BEARING for the walker.  Same invariant, opposite verdicts ⇒
    vestigial-ness is consumer-relative. -/
theorem walker_rejects_bad_window :
    valueBlindAccepts negStack = true ∧ walkerMayDescend negStack = false := ⟨rfl, rfl⟩

/-- **NEGATIVE — the bridge "projection ⟹ full invariant" is FALSE**: the negative is a counterexample
    (`topTrue = true` but `allTrue = false`).  So the walker cannot source the full invariant from the
    projection-providing gate; it must come from the walker's own descent discipline. -/
theorem projection_does_not_imply_full :
    ¬ (∀ s : List Bool, topTrue s = true → allTrue s = true) := by
  intro h
  have := h negStack rfl
  simp [allTrue, negStack] at this

end Tests.Reflections.VestigialProjectionReopens
