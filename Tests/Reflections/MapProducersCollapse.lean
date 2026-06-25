/-! # Reflection 520 — the carrier → six grammar producers collapse (brick (3) core)

R515 (`mapGrammarFacts_of_mapRoot`, demo `MapRootProjection`) turns the map root carrier
`MapInteriorSeparators tokens lo' hi'` into the bundle `MapGrammarFacts tokens (q+1) hi` at ONE window
whose opener sits at `q`.  R520 closes the gap to the CONSUMER: `flowSubrangesOk_of_window_producers`
does not want a bundle at one window — it wants the SIX per-window producer universals
`h_key_content … h_value_bracket_succ`, each `∀ lo hi, <guards> → <inner body>`, keyed on the window
START `lo` (not the opener position `q = lo - 1`).  Two new lemmas bridge carrier → producers:

* **`mapGrammarFacts_window_of_root`** — the per-window step.  It re-keys R515 from `q` to `lo` by
  taking `q := lo - 1`, so `q + 1 = lo` via `Nat.sub_add_cancel` (the `2 ≤ lo` guard gives `1 ≤ lo`).
  It supplies the pre-opener prefix witness from whole-stream fold-totality, threads the producer's own
  opener/balance/floor, and — the R519 redirect realized — DISCARDS the `.flowMappingEnd` closer guard
  (the marker-free carrier identifies the interior by its `some false` enclosure, not the closer).
* **`mapProducers_of_mapRoot`** — bundles the six producers by projecting the matching `MapGrammarFacts`
  conjunct (`.1 … .2.2.2.2.2`) at every guarded window.  Feeding these into the consumer collapses six
  of its seven map slots onto the single carrier, leaving only `h_map_rec` (the `RecMapBody` recursion,
  brick (2)) raw — the exact map mirror of R512's seq asymmetry.

The crux this demo pins, beyond R515:

* **The empty nested `{}` window forces the NON-strict route.**  The producer slot guards `lo ≤ hi`, NOT
  `lo < hi` — the empty window `lo = hi` (a nested `{}`) makes the six universals vacuous but must still
  type-check.  R515's `q`-keyed route needs only `q + 1 ≤ hi`, never `lo < hi`, so it survives `lo = hi`;
  the `FlowBodyWindow`-keyed alternative (`mapWindow_grammarFacts`) would demand strict `lo < hi` and
  could not.  Picking the route by which arithmetic it forces is the design decision.

* **The `q ↦ lo - 1` re-key is the only new arithmetic.**  Everything else is R515; the bridge is one
  `Nat.sub_add_cancel` rewrite carried through balance, floor, and the conclusion.

* **Closer DISCARDED, floor THREADED.**  R519 showed the six original seven-guard slots are FALSE on a
  cross-matched window; the redirect added the Dyck floor as the eighth guard.  Here the collapse USES
  that floor (it is the gate's third conjunct) and IGNORES the closer — so the producer's guard list and
  the carrier's gate list line up exactly, modulo the dropped marker.

This demo (self-contained core Lean, no imports) models the collapse over a tiny window arithmetic: a
guarded-universal `Carrier` whose `Gate` requires a `floor`, the R515-style `facts_of_root` keyed on the
opener `q`, the R520 re-key `facts_window_of_root` (with the `Nat.sub_add_cancel` bridge, the closer as a
discarded `True`, `lo = hi` admitted), and the bundle collapse `producers_of_root` projecting each
conjunct.  `demo` carries `[propext, Quot.sound]`, faithfully matching the real lemmas (the profile
inherited through R515's `mapGrammarFacts_of_mapRoot`) — and crucially NO `sorryAx`, because the carrier
is an ASSUMED hypothesis, so no taint enters ([[ref-mirror-inherits-dependency-axioms]] R518: taint
tracks the dependency, not the axis; an assumed carrier is clean).
-/

namespace MapProducersCollapse

set_option autoImplicit false

/-- Toy grammar-facts bundle keyed window-absolutely on `[a,b)` (mirror of `MapGrammarFacts`'s six
    conjuncts, here two to keep the projection visible). -/
structure GrammarFacts (a b : Nat) : Prop where
  keyFact : a ≤ b
  valFact : a ≤ b + 1

/-- Toy gate (mirror of `MapTypedInterior`): it REQUIRES the floor.  No closer appears — the carrier is
    marker-free; the interior is identified by the floor + (implicit) enclosure, not the `.flowMappingEnd`. -/
def Gate (a b : Nat) (floor : Nat → Nat → Prop) : Prop := floor a b

/-- Toy guarded-universal carrier (mirror of `MapInteriorSeparators tokens 2 (size-2)`): every gated
    sub-window's facts. -/
def Carrier (hi : Nat) (floor : Nat → Nat → Prop) : Prop :=
  ∀ a b, 2 ≤ a → a ≤ b → b ≤ hi → Gate a b floor → GrammarFacts a b

/-- R515-style projection keyed on the OPENER position `q`: the carrier fires at `[q+1, hi)`.  (Toy of
    `mapGrammarFacts_of_mapRoot`.) -/
theorem facts_of_root (hi q b : Nat) (floor : Nat → Nat → Prop)
    (h_carrier : Carrier hi floor)
    (h_lo : 2 ≤ q + 1) (h_qb : q + 1 ≤ b) (h_b : b ≤ hi)
    (h_floor : floor (q + 1) b) :
    GrammarFacts (q + 1) b :=
  h_carrier (q + 1) b h_lo h_qb h_b h_floor

/-- **The R520 per-window step** (toy of `mapGrammarFacts_window_of_root`).  Re-key from the opener `q`
    to the producer's window start `lo` via `q := lo - 1` (`q + 1 = lo` by `Nat.sub_add_cancel`, valid
    since `2 ≤ lo`).  The closer guard is present (`_h_close : True`) but DISCARDED; the floor is THREADED.
    The producer slot's NON-strict `lo ≤ hi` is honoured — `lo = hi` (the empty nested `{}`) is admitted,
    because the `q`-keyed route needs only `q + 1 ≤ hi`, never `lo < hi`. -/
theorem facts_window_of_root (lo hi b : Nat) (floor : Nat → Nat → Prop)
    (h_carrier : Carrier hi floor)
    (h_lo2 : 2 ≤ lo) (h_lob : lo ≤ b) (h_b : b ≤ hi)
    (_h_close : True)                       -- the `.flowMappingEnd` closer guard — DISCARDED
    (h_floor : floor lo b) :                -- the Dyck-floor eighth guard — THREADED into the gate
    GrammarFacts lo b := by
  have h_eq : lo - 1 + 1 = lo := Nat.sub_add_cancel (by omega)
  have h := facts_of_root hi (lo - 1) b floor h_carrier
    (by omega) (by omega) h_b (by rw [h_eq]; exact h_floor)
  rwa [h_eq] at h

/-- **The collapse** (toy of `mapProducers_of_mapRoot`): from ONE carrier, BOTH producer slots — each a
    guarded universal projecting a `GrammarFacts` conjunct, ignoring the closer at every slot.  In the
    real lemma this is six slots projecting `.1 … .2.2.2.2.2`. -/
theorem producers_of_root (hi : Nat) (floor : Nat → Nat → Prop)
    (h_carrier : Carrier hi floor) :
    (∀ lo b, 2 ≤ lo → lo ≤ b → b ≤ hi → True → floor lo b → lo ≤ b) ∧
    (∀ lo b, 2 ≤ lo → lo ≤ b → b ≤ hi → True → floor lo b → lo ≤ b + 1) := by
  refine ⟨?_, ?_⟩ <;> intro lo b h_lo2 h_lob h_b h_close h_floor
  · exact (facts_window_of_root lo hi b floor h_carrier h_lo2 h_lob h_b h_close h_floor).keyFact
  · exact (facts_window_of_root lo hi b floor h_carrier h_lo2 h_lob h_b h_close h_floor).valFact

/-- A concrete carrier: the facts hold at every gated window, with the gate's floor always satisfiable. -/
def sampleFloor : Nat → Nat → Prop := fun _ _ => True
def sampleCarrier : Carrier 10 sampleFloor :=
  fun _a b _ hab _ _ => ⟨hab, Nat.le_trans hab (Nat.le_succ b)⟩

/-- The empty nested `{}` window `lo = hi = 5`: the producer still fires (vacuously), because the
    re-key route never demanded `lo < hi`. -/
theorem empty_window_admitted : GrammarFacts 5 5 :=
  facts_window_of_root 5 10 5 sampleFloor sampleCarrier (by decide) (by decide) (by decide) trivial trivial

/-- The demo deliverable: both producer slots, collapsed onto the single carrier. -/
theorem demo :
    (∀ lo b, 2 ≤ lo → lo ≤ b → b ≤ 10 → True → sampleFloor lo b → lo ≤ b) ∧
    (∀ lo b, 2 ≤ lo → lo ≤ b → b ≤ 10 → True → sampleFloor lo b → lo ≤ b + 1) :=
  producers_of_root 10 sampleFloor sampleCarrier

end MapProducersCollapse

-- Axiom audit (machine-checked: `#guard_msgs` pins the profile and fails the build if it ever drifts).
-- `[propext, Quot.sound]`, faithfully matching the real `mapProducers_of_mapRoot` /
-- `mapGrammarFacts_window_of_root` (the profile inherited through R515's `mapGrammarFacts_of_mapRoot`);
-- crucially NO `sorryAx`, because the carrier is an ASSUMED hypothesis here — taint tracks the
-- dependency, not the axis ([[ref-mirror-inherits-dependency-axioms]] R518).
/-- info: 'MapProducersCollapse.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms MapProducersCollapse.demo
