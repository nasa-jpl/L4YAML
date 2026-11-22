/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 667 — a call site's coverage is its BRANCH times its FRAME

**The rule.**  Once a producer is merged over a case split
([[PuntTheShapeNotTheSite]]) and each branch of that split needs a different
optional argument, a call site is served on a branch only if TWO independent
things hold: the caller's own input analysis can reach that branch, and the
caller can supply the frame that branch needs.  Coverage is the product, not
either factor — so before wiring a call site, compute the product.  An empty
product means writing the call buys nothing, and the emptiness is not news the
compiler will give you: the call typechecks and returns `True` forever.

**Why it is worth computing rather than discovering.**  Both factors are already
written down.  Which branches a caller sees is a property of the lemma it got its
evidence from — a break-free analysis returns the on-line branch and nothing else
— and which frames it can offer is a property of the slot its pending carries: a
`SBlockIndented` slot has a compact alternative, a `SBlockNode` slot does not.
Neither is a fact about the input, so both can be read off the types before any
proof is attempted.

**The empty cell is not a boundary.**  This is what makes the product worth
naming rather than folding into [[PuntMayBeTheBoundary]]'s two questions.  Each
factor of an empty product is shared with a site that IS served: another site sees
the same single branch and offers the frame that branch needs, and another site
offers the same single frame and sees the branch that needs it.  So neither
restriction refutes anything — there is no false datum here, and no arm to call
the family's edge.  What is missing is an OVERLAP, which is a property of the
pair.

Concretely (L4YAML item 41): `entryPropsKeyPack_of_dispatch` gives item 17's
props-key pack the route item 38 gave the scalar one, merged over the landing
disjunct as item 40 merged its siblings.  Four call sites, four cells: the
`-`-parked pending at index 0 sees both branches and offers both frames (`- &p
a: 1`, `-⏎  &p a: 1`), the indented one sees the compact branch only, the `[189]`
value at index 0 offers the nested frame only (`k:⏎  &p a: 1`), and the indented
`[189]` value sees one branch and offers the other — so it keeps its `True` and
the call was not written.

§1 the two factors.  §2 the product, and the cell that is empty.  §3 why the
empty cell is not a boundary.  §4 the side condition that vanishes at every
site that could test it.  §5 the shipped counts.
-/

namespace L4YAML.Tests.Reflections.CoverageIsBranchTimesFrame

/-! ## §1  The two factors

The producer is merged over one case split — where the step that reached the
content LANDED — and each branch closes its entry with a different frame. -/

/-- The branch of the merged producer's case split. -/
inductive Branch where
  | onLine       -- the content shares its line with the indicator that parked
  | acrossBreak  -- the step crossed a break and stopped at a line start
deriving DecidableEq, Repr

/-- The frame that branch needs to reach the stream: `[185]`'s compact mapping
    alternative on the line, `[187]` nested in the awaited node across a break. -/
inductive Frame where
  | compact
  | node
deriving DecidableEq, Repr

/-- Which frame each branch needs.  This is the producer's own structure, fixed
    once and for all — not something a caller can vary. -/
def needs : Branch → Frame
  | .onLine => .compact
  | .acrossBreak => .node

/-- A call site is characterised by two independent restrictions, and by nothing
    else that matters here. -/
structure Site where
  /-- Which branches the caller's evidence lemma can hand it.  A break-free
      analysis returns exactly one. -/
  sees : Branch → Bool
  /-- Which frames the caller's pending can close with.  A pending whose slot is
      `SBlockIndented` has the compact alternative; one whose slot is
      `SBlockNode` does not. -/
  offers : Frame → Bool

/-- **The product.**  Served on a branch iff both factors admit it. -/
def covers (s : Site) (b : Branch) : Bool := s.sees b && s.offers (needs b)

/-- Served at all. -/
def served (s : Site) : Bool := covers s .onLine || covers s .acrossBreak

/-! ## §2  The four cells

The two factors are independent, so the four sites of one item are the four
combinations — and the table can be written before a single call is. -/

/-- A `-`-parked pending at index 0: the landing analysis is `anyCol`, and the
    entry's slot is `SBlockIndented`. -/
def entryRoot : Site := ⟨fun _ => true, fun _ => true⟩
/-- The same pending INDENTED: its value reading is break-free, so it sees the
    on-line branch alone. -/
def entryIndented : Site := ⟨fun b => b == .onLine, fun _ => true⟩
/-- A `[189]` VALUE at index 0: `anyCol` again, but the value slot is
    `s-l+block-node`, which has no compact alternative. -/
def valueRoot : Site := ⟨fun _ => true, fun f => f == .node⟩
/-- …and the indented value: one branch, the other frame. -/
def valueIndented : Site := ⟨fun b => b == .onLine, fun f => f == .node⟩

theorem the_table :
    (covers entryRoot .onLine = true ∧ covers entryRoot .acrossBreak = true) ∧
    (covers entryIndented .onLine = true ∧ covers entryIndented .acrossBreak = false) ∧
    (covers valueRoot .onLine = false ∧ covers valueRoot .acrossBreak = true) ∧
    (covers valueIndented .onLine = false ∧ covers valueIndented .acrossBreak = false) := by
  decide

/-- Three of the four are served; the fourth is the empty product. -/
theorem three_of_four_are_served :
    served entryRoot = true ∧ served entryIndented = true ∧
    served valueRoot = true ∧ served valueIndented = false := by
  decide

/-- **Neither factor alone predicts the answer.**  Reading only the branches, or
    only the frames, gets one of the four cells wrong — which is why the product
    is the thing to compute. -/
theorem neither_factor_alone_predicts :
    (∃ s : Site, (∃ b, s.sees b = true) ∧ served s = false) ∧
    (∃ s : Site, (∃ f, s.offers f = true) ∧ served s = false) :=
  ⟨⟨valueIndented, ⟨.onLine, by decide⟩, by decide⟩,
   ⟨valueIndented, ⟨.node, by decide⟩, by decide⟩⟩

/-! ## §3  The empty cell is NOT a boundary

[[PuntMayBeTheBoundary]] asks whether the datum's negation goes through at some
input that reaches the site; [[PuntTheShapeNotTheSite]] asks whether the datum
splits the inputs.  Here neither question applies: nothing is false.  Each factor
of the empty product is SHARED with a site that is served, so the restriction it
imposes is demonstrably not fatal on its own. -/

/-- The branch restriction is shared with a served site. -/
theorem the_branch_factor_is_not_fatal :
    entryIndented.sees = valueIndented.sees ∧ served entryIndented = true := by
  refine ⟨?_, by decide⟩
  funext b; cases b <;> rfl

/-- …and so is the frame restriction. -/
theorem the_frame_factor_is_not_fatal :
    valueRoot.offers = valueIndented.offers ∧ served valueRoot = true := by
  refine ⟨?_, by decide⟩
  funext f; cases f <;> rfl

/-- So the emptiness is a property of the PAIR: the branches this site sees and
    the frames it offers do not meet. -/
theorem emptiness_is_a_property_of_the_pair :
    ∀ b, valueIndented.sees b = true → valueIndented.offers (needs b) = false := by
  intro b h; cases b
  · rfl
  · exact absurd h (by decide)

/-- **And relaxing EITHER factor closes it.**  That is the difference between a
    missing overlap and a boundary: a boundary survives every relaxation that
    keeps the input in the language (`closing_the_boundary_is_refutable` in
    Reflection 665 has no such witness). -/
theorem either_relaxation_closes_it :
    served { valueIndented with sees := fun _ => true } = true ∧
    served { valueIndented with offers := fun _ => true } = true := by
  decide

/-! ## §4  The side condition that vanishes

The merged producer's break-crossed branch carries a route with a side condition
— the pending's index below the column the content landed at — which was item
39's boundary and item 40's shape-punt.  Here it never fires: the only sites that
see the break-crossed branch are the two whose index is 0, and at 0 the
inequality is vacuous.  So the SAME inequality is a boundary, a decidable split,
or nothing at all, depending only on which sites can reach it — which is the
reading [[PuntMayBeTheBoundary]] insists on, made once more. -/

/-- The index each site's pending carries. -/
def index : Site → Nat
  | s => if s.sees .acrossBreak then 0 else 2  -- the anyCol sites are the root ones

/-- The route's side condition. -/
def nests (n w : Nat) : Prop := n ≤ w

/-- At every site that can reach the branch which tests it, it holds for every
    landing — so this item pays nothing for what cost items 39 and 40 an
    argument each. -/
theorem the_side_condition_is_vacuous_where_it_can_fire :
    ∀ s : Site, s.sees .acrossBreak = true → ∀ w, nests (index s) w := by
  intro s h w
  simp only [index, h, ite_eq_left]
  exact Nat.zero_le w

/-! ## §5  What item 41 shipped -/

/-- Producers of the props-key pack: the root one items 17–29 wrote, and the
    entry one this item merged out of the landing disjunct. -/
def packProducersBefore : Nat := 1
def packProducersAfter : Nat := 2
/-- Arms constructing the parked run that can supply the pack, of six: before,
    the root dispatch and the run-extension arm; after, both entry dispatches
    and the root mapping value as well. -/
def supplyingArmsBefore : Nat := 2
def supplyingArmsAfter : Nat := 5
def armsTotal : Nat := 6
/-- Frames a run-headed key can be framed by: the root's, and now the compact
    entry's and the nested mapping's. -/
def runKeyFramesBefore : Nat := 1
def runKeyFramesAfter : Nat := 3
/-- New route lemmas and new frame lemmas: none.  The three routes item 38's
    pack already carries are the three this one needed. -/
def newRouteLemmas : Nat := 0
def newFrameLemmas : Nat := 0
/-- One projection lemma — a single-half run reads at `block-key` — and three
    post-state conjuncts on the indented value's reading, which is what let the
    indented entry reach its one cell. -/
def newProjectionLemmas : Nat := 1
def newCarriedConjuncts : Nat := 3
/-- Consumer arms edited: the `:` reader, which got SHORTER by the one route
    application it used to make. -/
def consumerRouteApplicationsBefore : Nat := 1
def consumerRouteApplicationsAfter : Nat := 0
/-- Sites whose whole product the table says is empty, and calls written for
    them. -/
def emptySites : Nat := 1
def callsWrittenForEmptySites : Nat := 0
/-- Runtime files edited: none.  Proof shape only. -/
def runtimeFilesEdited : Nat := 0
/-- Escape sites and `scannerDrop` sites: unmoved for the fifth item running —
    what moves is the domain ([[CoverageNotCallSites]]). -/
def escapeSitesBefore : Nat := 6
def escapeSitesAfter : Nat := 6
def scannerDropSitesBefore : Nat := 4
def scannerDropSitesAfter : Nat := 4

theorem shipped :
    packProducersAfter = packProducersBefore + 1 ∧
    supplyingArmsAfter = supplyingArmsBefore + 3 ∧
    supplyingArmsAfter + emptySites = armsTotal ∧
    runKeyFramesAfter = runKeyFramesBefore + 2 ∧
    newRouteLemmas = 0 ∧ newFrameLemmas = 0 ∧
    newProjectionLemmas = 1 ∧ newCarriedConjuncts = 3 ∧
    consumerRouteApplicationsAfter + 1 = consumerRouteApplicationsBefore ∧
    callsWrittenForEmptySites = 0 ∧
    runtimeFilesEdited = 0 ∧
    escapeSitesAfter = escapeSitesBefore ∧
    scannerDropSitesAfter = scannerDropSitesBefore := by
  decide

end L4YAML.Tests.Reflections.CoverageIsBranchTimesFrame

end Blanket
