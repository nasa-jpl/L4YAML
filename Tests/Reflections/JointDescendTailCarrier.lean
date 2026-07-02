/-
# Reflection 532 — the carrier-fed concrete JOINT descend-tail: an OPAQUE-input recursion edge ∘ its
content-pack provider = the concrete edge, and the composition RETYPES the interface from the
irreproducible top-down content fact to the reproducible root carrier

Self-contained companion to `recbody_joint_descend_tail_carrier`
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`), the composition of the two
landed joint bricks: `recbody_joint_content_pack` (R531) feeds its output into
`recbody_joint_descend_tail` (R530)'s opaque content slot.

The point this file isolates — **importing a provider into a consumer's opaque slot RETYPES the
consumer's interface.**  The descend edge (R530) is stated bare with two opaque close-gated content
packs (`Deep* ∧ *Enc ∧ Content*`) because the width recursion cannot reproduce the content fact at a
descended suffix.  The provider (R531) manufactures exactly those packs from the guard's deep/enclosure
halves plus two fixed outer carriers.  Because the provider's OUTPUT type is, conjunct for conjunct, the
descend's pack INPUT type, the two compose with no glue.  And the composed edge no longer asks for the
content packs — it asks for the CARRIER interface (the two carriers + the map-deferred fact `M2` + the
marker balance `Bal`).  That swap — top-down content → root carrier — is the whole value of the
composition: the content packs were irreproducible top-down, but the root carrier IS reproducible (seed
once at the root, narrow per window by the frame bounds).  No sorry is discharged; the interface is
retyped, and the retype is the progress.

This file models the descend edge and the content-pack provider as abstract hypotheses, proves the exact
composition the real lemma performs, then instantiates at toy types and runs both close branches.
-/

namespace JointDescendTailCarrier

set_option autoImplicit false

/-- The window close token — the gate discriminator (toy stand-in for `YamlToken`'s
    `.flowSequenceEnd` / `.flowMappingEnd`). -/
inductive Close where
  | seqEnd
  | mapEnd
  | scalar
  deriving DecidableEq

/-! ## The composition — feed the provider's output into the descend's opaque content slot. -/

/-- **The carrier-fed concrete descend-tail.**  Parametric in the close map `close`, the window guard
    `Win`, the two deep-content guards `DeepS`/`DeepM`, the two enclosure guards `EncS`/`EncM`, the two
    manufactured contents `ContentS`/`ContentM`, the two fixed outer carriers `CarrierS`/`CarrierM`, the
    deferred map fact `M2`, the marker balance `Bal`, the separator marker `Sep`, and the two abstract
    landed edges:

    * `descend` — the OPAQUE-input edge (R530 analog): given the window, the close disjunction, the two
      close-gated content PACKS (`Deep* ∧ *Enc ∧ Content*`), the marker bounds, the balance and the
      separator, it advances the guard to the suffix `[m+1, hi)`.  It consumes `Content*` but cannot
      reproduce it — hence the packs are opaque INPUTS.
    * `provide` — the content-pack PROVIDER (R531 analog): given the window, the two close-gated
      deep/enclosure HALVES, the two carriers, the deferred `M2` and the frame bounds, it manufactures
      exactly the two close-gated content packs `descend` consumes.

    The composition imports `provide` into `descend`'s opaque slot.  NOTE the resulting hypothesis list:
    the content packs are GONE — replaced by the carrier interface (`CarrierS`/`CarrierM`/`M2`/`Bal`).
    That is the interface retype. -/
theorem descend_tail_carrier
    (close : Nat → Close)
    (Win DeepS DeepM ContentS ContentM CarrierS CarrierM M2 Bal : Nat → Nat → Prop)
    (EncS EncM Sep : Nat → Prop)
    (descend : ∀ lo hi m, Win lo hi →
        (close hi = .seqEnd ∨ close hi = .mapEnd) →
        (close hi = .seqEnd → DeepS lo hi ∧ EncS lo ∧ ContentS lo hi) →
        (close hi = .mapEnd → DeepM lo hi ∧ EncM lo ∧ ContentM lo hi) →
        lo < m → m < hi → Bal lo m → Sep m →
        Win (m + 1) hi
          ∧ (close hi = .seqEnd → DeepS (m + 1) hi ∧ EncS (m + 1))
          ∧ (close hi = .mapEnd → DeepM (m + 1) hi ∧ EncM (m + 1))
          ∧ (close hi = .seqEnd ∨ close hi = .mapEnd))
    (provide : ∀ lo0 hi0 lo hi, Win lo hi →
        (close hi = .seqEnd → DeepS lo hi ∧ EncS lo) →
        (close hi = .mapEnd → DeepM lo hi ∧ EncM lo) →
        CarrierS lo0 hi0 → CarrierM lo0 hi0 → M2 lo hi → lo0 ≤ lo → hi ≤ hi0 →
        (close hi = .seqEnd → DeepS lo hi ∧ EncS lo ∧ ContentS lo hi)
          ∧ (close hi = .mapEnd → DeepM lo hi ∧ EncM lo ∧ ContentM lo hi))
    (lo0 hi0 lo hi m : Nat)
    (h_win : Win lo hi)
    (h_seq_guard : close hi = .seqEnd → DeepS lo hi ∧ EncS lo)
    (h_map_guard : close hi = .mapEnd → DeepM lo hi ∧ EncM lo)
    (h_close : close hi = .seqEnd ∨ close hi = .mapEnd)
    (h_seq_carrier : CarrierS lo0 hi0)
    (h_map_carrier : CarrierM lo0 hi0)
    (h_m2 : M2 lo hi)
    (h_lo0 : lo0 ≤ lo) (h_hi0 : hi ≤ hi0)
    (h_lo_m : lo < m) (h_m_hi : m < hi)
    (h_bal_m : Bal lo m) (h_sep : Sep m) :
    Win (m + 1) hi
      ∧ (close hi = .seqEnd → DeepS (m + 1) hi ∧ EncS (m + 1))
      ∧ (close hi = .mapEnd → DeepM (m + 1) hi ∧ EncM (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) := by
  -- Import the provider into the descend's opaque content slot: its output IS the descend's pack input.
  obtain ⟨h_seq_pack, h_map_pack⟩ :=
    provide lo0 hi0 lo hi h_win h_seq_guard h_map_guard h_seq_carrier h_map_carrier h_m2 h_lo0 h_hi0
  exact descend lo hi m h_win h_close h_seq_pack h_map_pack h_lo_m h_m_hi h_bal_m h_sep

/-! ## Toy instance: concrete close map, trivial guards, both abstract edges discharged. -/

/-- A toy stream: position `3` is a seq close, `4` is a map close. -/
def close : Nat → Close
  | 3 => .seqEnd
  | 4 => .mapEnd
  | _ => .scalar

/-- All window/content/carrier guards are the monotone predicate `lo ≤ hi`; the leaf markers are `True`.
    Enough to discharge both abstract edges by pure term construction, exercising the COMPOSITION (not the
    heavy carrier→content derivation the real lemma calls). -/
def W (lo hi : Nat) : Prop := lo ≤ hi
def Cs (lo hi : Nat) : Prop := lo ≤ hi
def Cm (lo hi : Nat) : Prop := lo ≤ hi
def Dp (_ _ : Nat) : Prop := True
def Car (_ _ : Nat) : Prop := True
def B (_ _ : Nat) : Prop := True
def En (_ : Nat) : Prop := True
def Sp (_ : Nat) : Prop := True
def M2t (_ _ : Nat) : Prop := True

/-- The toy OPAQUE-input descend edge: from `m < hi` the suffix window `(m+1) ≤ hi` holds; the
    deep/enclosure pieces and close disjunction pass through trivially. -/
theorem descToy : ∀ lo hi m, W lo hi →
    (close hi = .seqEnd ∨ close hi = .mapEnd) →
    (close hi = .seqEnd → Dp lo hi ∧ En lo ∧ Cs lo hi) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo ∧ Cm lo hi) →
    lo < m → m < hi → B lo m → Sp m →
    W (m + 1) hi
      ∧ (close hi = .seqEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .mapEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) := by
  intro _ hi m _ h_close _ _ _ h_m_hi _ _
  exact ⟨by unfold W; omega, fun _ => ⟨trivial, trivial⟩, fun _ => ⟨trivial, trivial⟩, h_close⟩

/-- The toy content-pack provider: bolts the trivial content onto the pass-through deep/enclosure
    halves (the `JointContentPackFromCarrier` shape). -/
theorem provToy : ∀ lo0 hi0 lo hi, W lo hi →
    (close hi = .seqEnd → Dp lo hi ∧ En lo) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo) →
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi → lo0 ≤ lo → hi ≤ hi0 →
    (close hi = .seqEnd → Dp lo hi ∧ En lo ∧ Cs lo hi)
      ∧ (close hi = .mapEnd → Dp lo hi ∧ En lo ∧ Cm lo hi) := by
  intro _ _ _ _ h_win h_sg h_mg _ _ _ _ _
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨d, e⟩ := h_sg h; exact ⟨d, e, by unfold Cs; unfold W at h_win; exact h_win⟩
  · obtain ⟨d, e⟩ := h_mg h; exact ⟨d, e, by unfold Cm; unfold W at h_win; exact h_win⟩

/-- The composition at the toy types — one carrier-fed descend serving BOTH close tokens. -/
theorem toyDescend : ∀ lo0 hi0 lo hi m, W lo hi →
    (close hi = .seqEnd → Dp lo hi ∧ En lo) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo) →
    (close hi = .seqEnd ∨ close hi = .mapEnd) →
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi → lo0 ≤ lo → hi ≤ hi0 →
    lo < m → m < hi → B lo m → Sp m →
    W (m + 1) hi
      ∧ (close hi = .seqEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .mapEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) :=
  fun lo0 hi0 lo hi m h_win h_sg h_mg h_close h_sc h_mc h_m2 h_lo0 h_hi0 h_lo_m h_m_hi h_bal h_sep =>
    descend_tail_carrier close W Dp Dp Cs Cm Car Car M2t B En En Sp descToy provToy
      lo0 hi0 lo hi m h_win h_sg h_mg h_close h_sc h_mc h_m2 h_lo0 h_hi0 h_lo_m h_m_hi h_bal h_sep

/-! ## Both branches run. -/

/-- The SEQ descend: `hi = 3` selects `close 3 = .seqEnd`; the suffix `[m+1, 3)` guard is produced. -/
example : W 3 3
    ∧ (close 3 = .seqEnd → Dp 3 3 ∧ En 3)
    ∧ (close 3 = .mapEnd → Dp 3 3 ∧ En 3)
    ∧ (close 3 = .seqEnd ∨ close 3 = .mapEnd) :=
  toyDescend 0 3 0 3 2 (by unfold W; omega)
    (fun _ => ⟨trivial, trivial⟩) (fun h => by simp [close] at h)
    (Or.inl rfl) trivial trivial trivial (by omega) (by omega)
    (by omega) (by omega) trivial trivial

/-- The MAP descend: `hi = 4` selects `close 4 = .mapEnd`; the suffix `[m+1, 4)` guard is produced. -/
example : W 4 4
    ∧ (close 4 = .seqEnd → Dp 4 4 ∧ En 4)
    ∧ (close 4 = .mapEnd → Dp 4 4 ∧ En 4)
    ∧ (close 4 = .seqEnd ∨ close 4 = .mapEnd) :=
  toyDescend 0 4 0 4 3 (by unfold W; omega)
    (fun h => by simp [close] at h) (fun _ => ⟨trivial, trivial⟩)
    (Or.inr rfl) trivial trivial trivial (by omega) (by omega)
    (by omega) (by omega) trivial trivial

/-- The punchline for the axiom audit: the carrier-fed descend specialised to the toy types — the full
    composition (provider imported into the descend's opaque slot), no `sorry`. -/
theorem demo : ∀ lo0 hi0 lo hi m, W lo hi →
    (close hi = .seqEnd → Dp lo hi ∧ En lo) →
    (close hi = .mapEnd → Dp lo hi ∧ En lo) →
    (close hi = .seqEnd ∨ close hi = .mapEnd) →
    Car lo0 hi0 → Car lo0 hi0 → M2t lo hi → lo0 ≤ lo → hi ≤ hi0 →
    lo < m → m < hi → B lo m → Sp m →
    W (m + 1) hi
      ∧ (close hi = .seqEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .mapEnd → Dp (m + 1) hi ∧ En (m + 1))
      ∧ (close hi = .seqEnd ∨ close hi = .mapEnd) := toyDescend

end JointDescendTailCarrier

/-- info: 'JointDescendTailCarrier.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms JointDescendTailCarrier.demo
