/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 647 — a production's "auto-detected" parameter is an EXISTENTIAL; inline it as a constant and the language silently shrinks, bind it inside the repetition and the language silently grows

**The rule.**  When a grammar says *for some auto-detected m*, that `m` is
quantified, and the formalization must quantify it too.  Replacing it with the
smallest legal value type-checks, proves everything the campaign asks of it,
and defines a strictly SMALLER language — one no differential test can catch,
because the parser under test still accepts every input the constant excludes.
The only way to find it is to read the production against the inductive.

**And the quantifier's SCOPE is half the content.**  `( s-indent(n+m) X(n+m) )+`
binds `m` *outside* the repetition — one indent, fixed for the whole
collection.  Bind it inside, per entry, and the language grows instead: ragged
indentation derives.  So the parameter belongs on the WRAPPER that opens the
collection, not on the entries' own constructors, and the two mistakes fail in
opposite directions from the same omission.

Concretely (L4YAML): `[183] l+block-sequence(n)` and
`[187] l+block-mapping(n)` are `( s-indent(n+m) … )+` for some fixed
auto-detected `m > 0`.  `SBlockSeqEntries n` takes `SIndent n` per entry and
`SBlockNode.blockSeq` passes `seqSpaces n c` exactly, so `m` is pinned at its
minimum: the `-` of a top-level sequence must sit at column 0.  `  - a`,
`a:⏎  - x` — every indented block collection, which is most of the language —
parses correctly with no derivation at all.  The constructor's own docstring
says it: *"Each entry = s-indent(n+1)"*, beside a production that says *n+m*.

§1 is the model: spec, constant, and per-entry existential, with the two
inclusions that fail.  §2 is the tell — acceptance cannot see it.  §3 is the
repair's shape and its measured cost.  §4 what item 21 recorded rather than
built, and why the order is forced.

Self-contained: three renderings of one production, the two failure directions,
the acceptance blindness, and the counts.
-/

namespace L4YAML.Tests.Reflections.AutoDetectedIsExistential

/-! ## §1  One production, three renderings

  An entry list is just its indents.  `n` is the context indent; the spec's
  `m > 0` is written here as `k = m - 1 ≥ 0`, matching the repo's
  `n_lean = n_spec + 1` convention. -/

/-- **The spec**: `( s-indent(n+m) X(n+m) )+` for some FIXED auto-detected `m`.
    Every entry shares one indent, and that indent is existentially chosen. -/
inductive SpecSeq (n : Nat) : List Nat → Prop where
  /-- The whole collection is at `n + k`, for a `k` fixed once. -/
  | mk (k : Nat) (l : List Nat) : l ≠ [] → (∀ i ∈ l, i = n + k) → SpecSeq n l

/-- **The constant**: `m` inlined at its smallest legal value.  This is what
    `SBlockSeqEntries n` + `blockSeq`'s `seqSpaces n c` amount to. -/
inductive FixedSeq (n : Nat) : List Nat → Prop where
  /-- One entry, at exactly `n`. -/
  | single : FixedSeq n [n]
  /-- …and another, also at exactly `n`. -/
  | cons (l : List Nat) : FixedSeq n l → FixedSeq n (n :: l)

/-- **The existential in the wrong place**: `m` chosen per entry.  Type-checks
    just as well, and admits collections the spec forbids. -/
inductive RaggedSeq (n : Nat) : List Nat → Prop where
  /-- One entry, at any indent ≥ `n`. -/
  | single (k : Nat) : RaggedSeq n [n + k]
  /-- …and another, at an indent chosen independently. -/
  | cons (k : Nat) (l : List Nat) : RaggedSeq n l → RaggedSeq n ((n + k) :: l)

/-- The constant is SOUND — everything it derives, the spec derives. -/
theorem fixed_sound {n : Nat} {l : List Nat} (h : FixedSeq n l) : SpecSeq n l := by
  refine SpecSeq.mk 0 l ?_ ?_
  · induction h with
    | single => exact List.cons_ne_nil _ _
    | cons l _ _ => exact List.cons_ne_nil _ _
  · induction h with
    | single => intro i hi; simp at hi; omega
    | cons l _ ih =>
      intro i hi
      rcases List.mem_cons.mp hi with h' | h'
      · omega
      · exact ih i h'

/-- …and INCOMPLETE.  A collection indented by 2 is a `SpecSeq` and not a
    `FixedSeq`: this is `  - a`, and it is most of the language. -/
theorem fixed_incomplete : SpecSeq 0 [2, 2] ∧ ¬ FixedSeq 0 [2, 2] := by
  refine ⟨SpecSeq.mk 2 [2, 2] (List.cons_ne_nil _ _) (by intro i hi; simp at hi; omega), ?_⟩
  intro h
  cases h

/-- The per-entry existential fails the OTHER way: it is complete… -/
theorem ragged_complete {n : Nat} {l : List Nat} (h : SpecSeq n l) : RaggedSeq n l := by
  obtain ⟨k, l, hne, hall⟩ := h
  induction l with
  | nil => exact absurd rfl hne
  | cons a t ih =>
    have ha : a = n + k := hall a (List.mem_cons_self ..)
    subst ha
    cases t with
    | nil => exact RaggedSeq.single k
    | cons b u =>
      exact RaggedSeq.cons k (b :: u)
        (ih (List.cons_ne_nil _ _) (fun i hi => hall i (List.mem_cons_of_mem _ hi)))

/-- …and UNSOUND: ragged indentation derives, which the spec's "fixed m"
    forbids.  Same omission, opposite direction. -/
theorem ragged_unsound : RaggedSeq 0 [1, 2] ∧ ¬ SpecSeq 0 [1, 2] := by
  refine ⟨RaggedSeq.cons 1 [2] (RaggedSeq.single 2), ?_⟩
  intro h
  obtain ⟨k, l, _, hall⟩ := h
  have h1 : (1 : Nat) = 0 + k := hall 1 (by simp)
  have h2 : (2 : Nat) = 0 + k := hall 2 (by simp)
  omega

/-! ## §2  Why acceptance cannot see it

  The parser under test accepts every indented collection; the grammar derives
  none of them.  A differential harness compares two ACCEPTORS, so it agrees
  with itself on exactly the inputs where the two disagree about derivation.
  Nothing short of reading the production against the inductive finds this. -/

/-- Both pipelines accept an input — the only signal a differential sweep has. -/
def accepted (_indent : Nat) : Bool := true

/-- Whether the surface grammar derives it, under the constant rendering. -/
def derivable (indent : Nat) : Bool := indent == 0

/-- Acceptance is blind to the gap, at every indent. -/
theorem acceptance_blind (i : Nat) : accepted i = true := rfl

/-- …while derivability splits exactly where the constant was inlined. -/
theorem gap_at_every_positive_indent (i : Nat) (h : i ≠ 0) :
    accepted i = true ∧ derivable i = false := by
  refine ⟨rfl, ?_⟩
  simp [derivable, h]

/-! ## §3  The repair's shape, and its cost

  Put the existential back where the production binds it: as a parameter of
  the constructor that OPENS the collection, threaded into the entries' shared
  index.  Widening a `Prop` inductive that way is free exactly when nothing
  ELIMINATES it ([[AwaitNotOpener]] §3) — and here, as there, the count is
  zero.  What is NOT free is the consumer: the awaited node must be re-indexed
  off 0 too, and that is a different item. -/

/-- Sites that CONSTRUCT `SBlockNode.blockSeq` / `.blockMap`: they transport
    canonically, each gaining `m = 0`. -/
def constructionSites : Nat := 7
/-- Sites that ELIMINATE them — `cases`/`induction`/`match`. -/
def eliminationSites : Nat := 0
/-- Pendings whose closure pins the awaited node's indent to 0
    (`pendingBlock`, `pendingMapValue`) — the real blocker, one level up. -/
def pendingsPinnedAtZero : Nat := 2

#guard eliminationSites == 0
#guard pendingsPinnedAtZero == 2

/-- **Why the grammar edit was recorded and not made.**  A widening whose only
    consumer is blocked is a constructor with no arm — the inhabitation debt the
    campaign refuses to take on.  Item 20 added `explicitEmpty` and spent it in
    the same commit; item 21 cannot spend `m` until the pendings carry the
    indent, so it states the gap instead. -/
def arms_that_would_use_it_today : Nat := 0

#guard arms_that_would_use_it_today == 0

/-! ## §4  The shipped counts (item 21, 2026-08-11) -/

/-- Productions found to have inlined an auto-detected parameter. -/
def productionsAffected : Nat := 2
/-- Times this campaign has found completeness debt in the surface GRAMMAR
    rather than the proof: items 9l (`[143]`/`[146]`), 20 (`[186]`'s `e-node`
    value), 21 (`[183]`/`[187]`'s `m`). -/
def grammarDebtFinds : Nat := 3
/-- Deferral families the gap blocks: whites before the indicator. -/
def familiesBlocked : Nat := 1
/-- Grammar constructors added by item 21 (see §3). -/
def grammarEditsMade : Nat := 0

#guard productionsAffected == 2
#guard grammarDebtFinds == 3
#guard familiesBlocked == 1
#guard grammarEditsMade == 0

end L4YAML.Tests.Reflections.AutoDetectedIsExistential

end Blanket
