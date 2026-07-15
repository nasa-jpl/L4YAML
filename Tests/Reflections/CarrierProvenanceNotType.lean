/-!
# Reflection 346 — a "narrow the root carrier" cycle-break works only if the carrier has an emission-INDEPENDENT producer; narrowability is provenance-blind and certifies nothing

Self-contained (core Lean, no `L4YAML` import) toy model of the PROBE behind the seq `desc`
fixpoint's carrier route (`(i'-b-B2c-carrier-narrow)`), the move R345's resolution handed forward.

R345 charted the fixpoint to "source per-window `FlowBodyContent` from the EMISSION carrier
`h_root_carrier`, narrowed to each window" — the narrow-from-root move that breaks a carrier↔recursion
cycle by seeding once at the root from a flat producer and restricting down. The R346 PROBE REFUTES
that plan as a TYPE MISIDENTIFICATION.

The decisive observation is that a flat universal-over-sub-windows carrier `Carrier lo hi :=
∀ a, lo ≤ a → a ≤ hi → Fact a` is narrowable BY CONSTRUCTION (a two-line `Nat.le_trans` subset
restriction), and that narrow lemma is **provenance-blind**: its proof depends only on `Carrier`'s
SHAPE, so the SAME proof serves a carrier sourced from emission and one sourced from the recursion's
own deliverable. Narrowability therefore certifies NOTHING about whether the root seed exists
non-circularly. The cycle-break works ONLY if the ROOT instance has a producer INDEPENDENT of the
consuming recursion.

In the real proof, `h_root_carrier : SeqInteriorSeparators tokens 2 (size-2)` is NOT an emission fact:
its only producer is `seqRoot_seqInteriorSeparators`, which consumes a `desc`, whose nested half is
the fixpoint `seqWindowRecSeqBody` that consumes `h_root_carrier` — the circle
`carrier ⟸ desc ⟸ fixpoint ⟸ carrier`. Narrowing it per window restricts an object that does not
exist yet, relocating the circle rather than breaking it. The genuine escape (already landed but
unused, `seqSeparatorFacts_of_recseqbody`) reads the per-window facts off the recursion's OWN IH
`RecSeqBody` — a proof-irrelevant `Prop` witness, as good as a carrier lookup — root-seeded from a
recursion-independent emission fact (`emitList_scans_recseqbody`).

The toy below abstracts the flat narrowable carrier, the provenance-blind narrow lemma, and the two
provenances: an emission-INDEPENDENT producer (cycle breaks) versus a carrier whose only arrows form
a closed loop through the fixpoint (cycle relocates, never seeds).

POSITIVE (`carrier_via_rec`): when the carrier has a recursion-independent producer (`rec_from_emission`),
it is obtainable UNCONDITIONALLY — the cycle is broken.

NEGATIVE (`carrier_route_is_a_loop`, `narrow_same`): when the carrier's only producers are the
fixpoint chain, the fully-composed route is an ENDO-map `Carrier → Carrier` with no base case — it
presupposes its own output. The `narrow` lemma is the SAME endo shape, provenance-blind, so it
certifies nothing and cannot seed.
-/

namespace Tests.Reflections.CarrierProvenanceNotType

set_option autoImplicit false

/-! ## A flat per-window fact and a universal-over-sub-windows carrier (toy `SeqInteriorSeparators`) -/

/-- A per-window fact (content is irrelevant; the demo is about provenance, so keep it trivially true). -/
def Fact (a : Nat) : Prop := 0 ≤ a

/-- The flat carrier: the `Fact` holds at every sub-window of `[lo, hi]`.  Its body is `lo`/`hi`-free
    except through the domain bounds, so it restricts to sub-intervals for free (`narrow` below). -/
def Carrier (lo hi : Nat) : Prop := ∀ a, lo ≤ a → a ≤ hi → Fact a

/-- **The NARROW lemma — a pure subset restriction, and PROVENANCE-BLIND.**  Its proof depends only on
    `Carrier`'s shape (universal over sub-windows), so the SAME proof serves a carrier sourced from
    emission and one sourced from the recursion's own deliverable.  Narrowability is free; it certifies
    NOTHING about whether the root seed exists non-circularly. -/
theorem narrow {lo hi lo' hi' : Nat} (h_lo : lo ≤ lo') (h_hi : hi' ≤ hi)
    (h : Carrier lo hi) : Carrier lo' hi' :=
  fun a ha hb => h a (Nat.le_trans h_lo ha) (Nat.le_trans hb h_hi)

/-! ## A recursive deliverable that PROJECTS to the carrier (the IH route, toy `RecSeqBody`) -/

/-- A recursive per-window deliverable (a proof-irrelevant `Prop`). -/
inductive Rec : Nat → Nat → Prop
  | mk (lo hi : Nat) : Rec lo hi

/-- The deliverable projects to the carrier — the toy `seqSeparatorFacts_of_recseqbody`. -/
theorem carrier_of_rec {lo hi : Nat} (_ : Rec lo hi) : Carrier lo hi := fun a _ _ => Nat.zero_le a

/-! ## PROVENANCE A — an emission-INDEPENDENT producer: the cycle breaks -/

/-- `Rec` is producible WITHOUT any carrier — the toy `emitList_scans_recseqbody` (straight from
    emission, recursion-independent). -/
theorem rec_from_emission (lo hi : Nat) : Rec lo hi := Rec.mk lo hi

/-- **POSITIVE.**  With a recursion-independent producer, the carrier is obtained UNCONDITIONALLY —
    a `Carrier`, not a `Carrier → Carrier`.  The cycle is broken; this is the live route. -/
theorem carrier_via_rec (lo hi : Nat) : Carrier lo hi :=
  carrier_of_rec (rec_from_emission lo hi)

/-! ## PROVENANCE B — the carrier's only producers form a loop through the fixpoint -/

/-- The fixpoint's per-window need IS the carrier (toy `seqWindowRecSeqBody` consuming `h_root_carrier`). -/
def Fix (lo hi : Nat) : Prop := Carrier lo hi
/-- The descent's deliverable IS the carrier (toy `desc`). -/
def Desc (lo hi : Nat) : Prop := Carrier lo hi

/-- The carrier's only producer consumes `Desc` (toy `seqRoot_seqInteriorSeparators`). -/
theorem carrier_from_desc {lo hi : Nat} (h : Desc lo hi) : Carrier lo hi := h
/-- `Desc`'s nested half is the fixpoint (toy `seqDescent_provider_of_gate`). -/
theorem desc_from_fix {lo hi : Nat} (h : Fix lo hi) : Desc lo hi := h
/-- The fixpoint CONSUMES the carrier (toy `seqWindowRecSeqBody` reading `h_root_carrier`). -/
theorem fix_from_carrier {lo hi : Nat} (h : Carrier lo hi) : Fix lo hi := h

/-- **NEGATIVE.**  The entire carrier route, fully composed, is an ENDO-map `Carrier → Carrier`: it
    presupposes its own output.  With ONLY these arrows there is no base case, so it can never SEED a
    carrier — only relocate the circle `carrier ⟸ desc ⟸ fixpoint ⟸ carrier`.  Contrast
    `carrier_via_rec`, which produces a `Carrier` outright. -/
theorem carrier_route_is_a_loop {lo hi : Nat} (h : Carrier lo hi) : Carrier lo hi :=
  carrier_from_desc (desc_from_fix (fix_from_carrier h))

/-- **NEGATIVE (narrow adds no seed).**  The narrow lemma at the same window is ALSO just
    `Carrier → Carrier` — provenance-blind, it threads an existing carrier and certifies nothing about
    circularity.  "Narrow the root carrier" cannot break a cycle the root carrier is part of. -/
theorem narrow_same {lo hi : Nat} (h : Carrier lo hi) : Carrier lo hi :=
  narrow (Nat.le_refl lo) (Nat.le_refl hi) h

end Tests.Reflections.CarrierProvenanceNotType
