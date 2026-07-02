/-
# Reflection 531 — the JOINT content-pack provider: the two close-gated content packs the joint
descend consumes, manufactured per-window from a FIXED OUTER carrier (with the map carrier's deferred
fact kept explicit)

Self-contained companion to `recbody_joint_content_pack`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the carrier→content feed for
the joint descend `recbody_joint_descend_tail` (Reflection 530).

R530 takes two close-gated content packs as OPAQUE inputs — `h_seq_pack : seqEnd → DeepS ∧ EncS ∧
ContentS` and `h_map_pack : mapEnd → DeepM ∧ EncM ∧ ContentM` — because the width recursion cannot
reproduce the content fact (`FlowBodyContent` / `MapBodyProps`) at a descended suffix.  This file
models how those packs are MANUFACTURED: the deep/enclosure conjuncts pass straight through from the
navigator guard's close-gated halves, and the content conjunct is produced per-window by a
collection-specific carrier→content provider (`seqWindow_flowBodyContent_seq_general` /
`mapWindow_mapBodyProps_general`), reading from a fixed outer carrier seeded once at the root and
narrowed in place.

Two structural points this file isolates:

* **Pass-through vs manufacture.**  Of the three pack conjuncts, two (`Deep*`, `Enc*`) are NOT
  re-derived — they come verbatim from the guard.  Only the content (`Content*`) is built, and only
  from the carrier + bounds.  So the provider is a guard→guard transform that bolts content on.

* **The asymmetric deferred fact.**  The seq provider needs only its carrier; the MAP provider needs
  one extra fact (`M2` — every depth-`0` comma is followed by a key) that NEITHER carrier bundles.  It
  stays an EXPLICIT input (`h_m2`), the map-carrier debt made legible — the dual of R530's
  debt-exposure discipline, here on the content axis instead of the descend axis.

Unlike R530's descend, there is NO off-branch vacuity here: each pack is an INDEPENDENT close-gated
implication, so the two halves are produced side by side (`refine ⟨fun .. => .., fun .. => ..⟩`), each
opening its own gate — no `rcases` on a shared discriminator, no contradiction to discharge.

This file models the close discriminator as a two-valued token, the guards/carriers/content as abstract
predicates, and the per-collection providers as abstract hypotheses; it proves the exact dual-pack
assembly of the real lemma, then instantiates and runs both branches.
-/

namespace JointContentPackFromCarrier

set_option autoImplicit false

/-- The window close token — the gate discriminator (toy stand-in for `YamlToken`'s
    `.flowSequenceEnd` / `.flowMappingEnd`). -/
inductive Close where
  | seqEnd
  | mapEnd
  | scalar
  deriving DecidableEq

/-! ## The abstract joint content-pack provider — two independently-gated packs, side by side. -/

/-- **The joint content-pack assembler.**  Parametric in the close map `close`, the shared window guard
    `Win`, the two deep-content guards `DeepS`/`DeepM`, the two enclosure guards `EncS`/`EncM`, the two
    manufactured contents `ContentS`/`ContentM`, the two fixed outer carriers `CarrierS`/`CarrierM`
    (keyed on the outer span `lo0 hi0`), the deferred map fact `M2`, and the two per-collection
    carrier→content providers `provideS`/`provideM`.

    Given the window guard, the close-gated deep/enclosure halves (the shape R530 produces and the joint
    driver threads), the two carriers, the deferred map fact, and the narrow bounds `lo0 ≤ lo ∧
    hi ≤ hi0`, it produces the two close-gated content packs R530 consumes.  The deep/enclosure
    conjuncts pass through; the content conjunct is manufactured.  NOTE the map provider alone consumes
    `close hi = .mapEnd` and `M2` — the asymmetry the map carrier defers. -/
theorem joint_content_pack
    (close : Nat → Close)
    (Win DeepS DeepM ContentS ContentM CarrierS CarrierM M2 : Nat → Nat → Prop)
    (EncS EncM : Nat → Prop)
    (provideS : ∀ lo0 hi0 lo hi, Win lo hi → DeepS lo hi → EncS lo →
        CarrierS lo0 hi0 → lo0 ≤ lo → hi ≤ hi0 → ContentS lo hi)
    (provideM : ∀ lo0 hi0 lo hi, Win lo hi → DeepM lo hi → EncM lo →
        close hi = .mapEnd → M2 lo hi → CarrierM lo0 hi0 → lo0 ≤ lo → hi ≤ hi0 → ContentM lo hi)
    (lo0 hi0 lo hi : Nat)
    (h_win : Win lo hi)
    (h_seq_guard : close hi = .seqEnd → DeepS lo hi ∧ EncS lo)
    (h_map_guard : close hi = .mapEnd → DeepM lo hi ∧ EncM lo)
    (h_seq_carrier : CarrierS lo0 hi0)
    (h_map_carrier : CarrierM lo0 hi0)
    (h_m2 : M2 lo hi)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0) :
    (close hi = .seqEnd → DeepS lo hi ∧ EncS lo ∧ ContentS lo hi)
      ∧ (close hi = .mapEnd → DeepM lo hi ∧ EncM lo ∧ ContentM lo hi) := by
  refine ⟨fun h_s => ?_, fun h_m => ?_⟩
  · obtain ⟨h_deep, h_enc⟩ := h_seq_guard h_s
    exact ⟨h_deep, h_enc, provideS lo0 hi0 lo hi h_win h_deep h_enc h_seq_carrier h_lo0 h_hi0⟩
  · obtain ⟨h_deep, h_enc⟩ := h_map_guard h_m
    exact ⟨h_deep, h_enc, provideM lo0 hi0 lo hi h_win h_deep h_enc h_m h_m2 h_map_carrier h_lo0 h_hi0⟩

/-! ## Toy instance: concrete close map, trivial guards, both providers exercised. -/

/-- A toy stream: position `3` is a seq close, `4` is a map close. -/
def close : Nat → Close
  | 3 => .seqEnd
  | 4 => .mapEnd
  | _ => .scalar

/-- All guards are the trivial monotone window predicate `lo ≤ hi` (the content is defeq to the window
    guard), so both providers are trivially provable — this toy exercises the dual-pack ASSEMBLY and the
    deferred-fact asymmetry, not the heavy carrier→content derivation
    (`seqWindow_flowBodyContent_seq_general` / `mapWindow_mapBodyProps_general`) the real lemma calls. -/
def W (lo hi : Nat) : Prop := lo ≤ hi
def Cs (lo hi : Nat) : Prop := lo ≤ hi
def Cm (lo hi : Nat) : Prop := lo ≤ hi
def Dp (_ _ : Nat) : Prop := True
def Car (_ _ : Nat) : Prop := True
def En (_ : Nat) : Prop := True
def M2t (_ _ : Nat) : Prop := True

theorem provS : ∀ lo0 hi0 lo hi, W lo hi → Dp lo hi → En lo →
    Car lo0 hi0 → lo0 ≤ lo → hi ≤ hi0 → Cs lo hi := by
  intro _ _ _ _ h _ _ _ _ _; unfold Cs; unfold W at h; exact h

theorem provM : ∀ lo0 hi0 lo hi, W lo hi → Dp lo hi → En lo →
    close hi = .mapEnd → M2t lo hi → Car lo0 hi0 → lo0 ≤ lo → hi ≤ hi0 → Cm lo hi := by
  intro _ _ _ _ h _ _ _ _ _ _ _; unfold Cm; unfold W at h; exact h

/-- The provider at the toy types — one assembler serving BOTH close tokens. -/
theorem toyPack : ∀ lo0 hi0 lo hi, W lo hi →
    (close hi = .seqEnd → Dp lo hi ∧ En lo) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo) →
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi → lo0 ≤ lo → hi ≤ hi0 →
    (close hi = .seqEnd → Dp lo hi ∧ En lo ∧ Cs lo hi)
      ∧ (close hi = .mapEnd → Dp lo hi ∧ En lo ∧ Cm lo hi) :=
  fun lo0 hi0 lo hi h_win h_sg h_mg h_sc h_mc h_m2 h_lo0 h_hi0 =>
    joint_content_pack close W Dp Dp Cs Cm Car Car M2t En En provS provM
      lo0 hi0 lo hi h_win h_sg h_mg h_sc h_mc h_m2 h_lo0 h_hi0

/-! ## Both branches run. -/

/-- The SEQ pack: `hi = 3` selects `close 3 = .seqEnd`; the seq content is manufactured, the map pack is
    vacuously satisfied (its gate never opens). -/
example : (close 3 = .seqEnd → Dp 2 3 ∧ En 2 ∧ Cs 2 3)
    ∧ (close 3 = .mapEnd → Dp 2 3 ∧ En 2 ∧ Cm 2 3) :=
  toyPack 0 3 2 3 (by unfold W; omega)
    (fun _ => ⟨trivial, trivial⟩)
    (fun h => by simp [close] at h)
    trivial trivial trivial (by omega) (by omega)

/-- The MAP pack: `hi = 4` selects `close 4 = .mapEnd`; the map content is manufactured (the provider
    consuming the close token + the deferred `M2`), the seq pack is vacuous. -/
example : (close 4 = .seqEnd → Dp 2 4 ∧ En 2 ∧ Cs 2 4)
    ∧ (close 4 = .mapEnd → Dp 2 4 ∧ En 2 ∧ Cm 2 4) :=
  toyPack 0 4 2 4 (by unfold W; omega)
    (fun h => by simp [close] at h)
    (fun _ => ⟨trivial, trivial⟩)
    trivial trivial trivial (by omega) (by omega)

/-- The punchline for the axiom audit: the joint content-pack assembler specialised to the toy types —
    the full dual-pack assembly with the deferred-fact-bearing map provider, no `sorry`. -/
theorem demo : ∀ lo0 hi0 lo hi, W lo hi →
    (close hi = .seqEnd → Dp lo hi ∧ En lo) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo) →
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi → lo0 ≤ lo → hi ≤ hi0 →
    (close hi = .seqEnd → Dp lo hi ∧ En lo ∧ Cs lo hi)
      ∧ (close hi = .mapEnd → Dp lo hi ∧ En lo ∧ Cm lo hi) := toyPack

end JointContentPackFromCarrier

/-- info: 'JointContentPackFromCarrier.demo' does not depend on any axioms -/
#guard_msgs in
#print axioms JointContentPackFromCarrier.demo
