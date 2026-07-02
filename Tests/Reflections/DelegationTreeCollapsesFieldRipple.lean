/-!
# Reflection 437 — a shared-structure field refinement's ripple is bounded by constructor TOPOLOGY, not count

Self-contained (core Lean, no `L4YAML` import) toy of the R437 finding.

Context.  R435/R436 concluded that the parser-contract Dyck FLOOR must be EXPOSED as a new conjunct on
the bracket-matching fields of `SeqBodyProps` (the field underdetermines the first-return witness, so the
consumer cannot reconstruct it; only the producer, which knows the genuine structure, can supply it —
`SelfPropagatingGuardDescent`).  Exposing a guard on a SHARED STRUCTURE field is exactly the move
[[ref-additive-parallel-type-over-shared-edit]] warns against: a structural edit to a shared type
*nominally* forces every constructor to supply the new conjunct.

The R437 finding.  That "every constructor" fear is CONDITIONAL on the constructors being INDEPENDENT.
When the structure's constructors form a DELEGATION TREE rooted at ONE assembler, the ripple collapses to
the root.  `SeqBodyProps` has five constructors, yet adding the floor conjunct touched ZERO of four of
them:

* `seqBodyProps_assemble` is the ROOT — it produces the bracket field's VALUE (via the conjunct lemmas
  `seq_bracket_{seq,map}_conjunct`, which read the floor off the typed locator).  This is the SINGLE
  field-value edit point.
* `seqBodyProps_of_windowed_safebody`, `_of_recseqbody_window`, `_of_located_entry` all DELEGATE to the
  root (each is `… := seqBodyProps_assemble …` or a chain into it).  A delegator is TRANSPARENT: it passes
  the field through unchanged, so once the root supplies the new conjunct the delegator recompiles with no
  edit.
* `seqBodyProps_empty` discharges the bracket field VACUOUSLY (`lo = hi` ⇒ `k < hi ≤ lo ≤ k` is `False`,
  closed by `False.elim`/`absurd`).  A vacuous leaf is ABSORBENT: `False.elim : C` for *any* `C`, so an
  added conjunct changes nothing.

So the true field-edit cost = one root producer + the field definition + a trailing `_` at each CONSUMER
that doesn't yet use the guard.  The "ripples to every constructor" cost model of
[[ref-additive-parallel-type-over-shared-edit]] applies to INDEPENDENT constructors; a delegation tree
collapses it to the root, and vacuous leaves absorb it.

A SECOND, orthogonal axis.  The floor ORIGINATES at the shared primitive the field-value comes from (the
typed locator).  Enriching that primitive ripples to ALL its consumers — but only as bind-ignore noise:
consumers that don't want the new output drop it with a `_` (or project it away).  Origin-enrichment of a
shared primitive is cheap precisely because the new output is ADDITIVE — nobody who didn't ask for it is
disturbed beyond one `_`.

The toy below models both axes:
* PART 1 — a `Box` structure with one existential field; an `assemble` root, two delegators, and a vacuous
  leaf.  The field is shown ALREADY REFINED (carrying the extra `Floor` conjunct); the delegators and the
  vacuous leaf typecheck against it WITH NO floor-specific code — that is the collapse.
* PART 2 — a shared `locate` primitive whose enriched output a sibling consumer bind-ignores.
-/

namespace Tests.Reflections.DelegationTreeCollapsesFieldRipple

set_option autoImplicit false

/-! ## PART 1 — the field-edit ripple collapses to the delegation root -/

/-- Stand-ins for the per-position predicates: `Close j` (the matching close is typed) and the
    self-propagating guard `Floor k j` (the new conjunct R435/R436 forces onto the field). -/
def Close (j : Nat) : Prop := j % 2 = 0
def Floor (k j : Nat) : Prop := k ≤ j

/-- The shared structure, with its bracket field **already refined** to carry the `Floor` guard.
    Modelled as one field `bracket : ∀ k, k < hi → ∃ j, Close j ∧ Floor k j` over a window `[0, hi)`. -/
structure Box (hi : Nat) : Prop where
  bracket : ∀ k, k < hi → ∃ j, Close j ∧ Floor k j

/-- **The field-value producer (the ROOT's engine).**  The ONE place that must change to supply the new
    `Floor` conjunct — it reads `Close` *and* `Floor` off the located witness.  (In L4YAML: the conjunct
    lemma `seq_bracket_seq_conjunct` reading the floor off the enriched typed locator.) -/
theorem mkBracket (hi k : Nat) (h : k < hi) : ∃ j, Close j ∧ Floor k j :=
  ⟨2 * hi, by unfold Close; omega, by unfold Floor; omega⟩

/-- **The ROOT constructor** — `seqBodyProps_assemble`'s analogue.  Builds `Box` from `mkBracket`. -/
theorem assemble (hi : Nat) : Box hi := ⟨fun k h => mkBracket hi k h⟩

/-- **A delegator** — `seqBodyProps_of_windowed_safebody`'s analogue.  Literally calls the root; carries
    NO floor-specific code, yet typechecks against the refined field.  *This is the collapse.* -/
theorem delegate1 (hi : Nat) : Box hi := assemble hi

/-- **A second-level delegator** — `seqBodyProps_of_located_entry`'s analogue (delegates to a delegator).
    Also untouched by the field refinement. -/
theorem delegate2 (hi : Nat) : Box hi := delegate1 hi

/-- **The vacuous leaf** — `seqBodyProps_empty`'s analogue.  An empty window (`hi = 0`) discharges the
    bracket field via `False.elim`: `k < 0` is absurd.  `False.elim` produces the refined field — with the
    extra `Floor` conjunct — with NO change.  *This is the absorption.* -/
theorem empty : Box 0 := ⟨fun k h => absurd h (by omega)⟩

/-! ## PART 2 — origin-enrichment of the shared primitive is bind-ignore noise -/

/-- The shared primitive whose output the field-value reads, **enriched** to also return `Floor`
    (toy of the typed locator now exposing the inner Dyck floor). -/
theorem locate (hi k : Nat) (h : k < hi) : ∃ j, Close j ∧ Floor k j := mkBracket hi k h

/-- **A sibling consumer that does NOT want the floor.**  It needs only `Close j`, so it bind-IGNORES the
    new `Floor` conjunct with a `_` — the entire cost of origin-enrichment to a consumer that didn't ask
    for it.  (In L4YAML: `map_key_bracket_conjunct`, the M9/M10 projections, `SeqInteriorSeparators`.) -/
theorem siblingConsumer (hi k : Nat) (h : k < hi) : ∃ j, Close j := by
  obtain ⟨j, hc, _⟩ := locate hi k h
  exact ⟨j, hc⟩

/-! ## PART 3 — the collapse is PREDICTIVE across structures that SHARE the topology (R438)

R437 OBSERVED the collapse on one structure (`SeqBodyProps`).  R438 TESTED it as a PREDICTION on a
DIFFERENT, structurally-independent type (`MapBodyProps`, fields M5/M8) that happens to share the
delegation topology — and it held EXACTLY.  The reusable upgrade: a topology-collapse claim is PREDICTIVE
across any structures that share the topology (root + delegators + vacuous leaf), so you read the
prediction off the constructor graph and CONFIRM it cheaply by the build.  In L4YAML the confirmation was
sharper still: the floor landed on both `MapBodyProps` bracket fields with ZERO edits to the file that
DEFINES the five `mapBodyProps_*` constructors — *a green build whose diff leaves the constructor-definition
file entirely untouched IS the machine-checked proof that every non-root constructor produced the refined
field for free.*

`Box2` below is a SECOND structure, independent of `Box`, with a DIFFERENT field shape (an extra `Succ`
conjunct after the witness — the analogue of `MapBodyProps.key_bracket_value`'s `.value` successor) but the
SAME `Floor` refinement and the SAME delegation topology.  It takes the refined field with no
per-constructor code, exactly as the topology predicts. -/

/-- A successor predicate, modelling the extra structure M5/M8 carry beyond the bracket (the `.value` /
    FE-or-mapEnd successor) — present so `Box2`'s field shape genuinely DIFFERS from `Box`'s. -/
def Succ (j : Nat) : Prop := j + 1 ≥ 1

/-- The second, independent structure: different field shape, same `Floor` refinement, same topology. -/
structure Box2 (hi : Nat) : Prop where
  bracket : ∀ k, k < hi → ∃ j, Close j ∧ Succ j ∧ Floor k j

/-- `Box2`'s root field-value producer (the single edit point, like `map_key_bracket_conjunct`). -/
theorem mkBracket2 (hi k : Nat) (h : k < hi) : ∃ j, Close j ∧ Succ j ∧ Floor k j :=
  ⟨2 * hi, by unfold Close; omega, by unfold Succ; omega, by unfold Floor; omega⟩

/-- `Box2`'s ROOT constructor. -/
theorem assemble2 (hi : Nat) : Box2 hi := ⟨fun k h => mkBracket2 hi k h⟩
/-- A `Box2` delegator — transparent, no floor-specific code, predicted free. -/
theorem delegate2a (hi : Nat) : Box2 hi := assemble2 hi
/-- A `Box2` vacuous leaf — absorbs the `Floor` (and `Succ`) conjunct via `False.elim`, predicted free. -/
theorem empty2 : Box2 0 := ⟨fun k h => absurd h (by omega)⟩

/-! ## The point, machine-checked.

`delegate1`/`delegate2`/`empty` are *complete* `Box` constructors that supply the floor-carrying field
with no floor-specific code: the delegators by transparency (they call the root), the leaf by absorption
(`False.elim`).  So the refinement's constructor-side cost was the root `mkBracket` ALONE — four of five
constructors were free.  The sibling consumer pays one `_`. -/
example : Box 7 := delegate2 7
example : Box 0 := empty
/-- The located witness is genuinely `Close` *and* `Floor` — both halves the primitive now exposes. -/
example : ∃ j, Close j ∧ Floor 1 j := locate 5 1 (by omega)
/-- R438: the SECOND structure's delegator and vacuous leaf take the refined field for free too — the
    collapse reproduced across an independent structure exactly as the shared topology predicted. -/
example : Box2 7 := delegate2a 7
example : Box2 0 := empty2

end Tests.Reflections.DelegationTreeCollapsesFieldRipple
