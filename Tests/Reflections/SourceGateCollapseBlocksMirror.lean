/-!
# Reflection 422 — a relocated obligation's SOURCE field is leaf-UNCONDITIONAL vs recursive-GATE-COLLAPSED:
the leaf head bridges to any gate for free, but the recursive carrier (already projected to the SIBLING'S
gate) is lossy for the mirror's gate, so the mirror must thread a NEW field there

Self-contained (core Lean, no `L4YAML` import) toy of the R422 head-bridge layer.  R421
(`TriggerCoincidenceRelocatesObligation`) found that mirroring the `OpenerAdj` wrap/seam layer to
`SepAdj` RELOCATES the single content-start obligation to the `.flowEntry` SEAM, where `SepAdj_seam`
demands the content-start head of the separator's SUCCESSOR block.  R422 sources that obligation and
finds the source has TWO forms by POSITION, only one of which mirrors freely.

* **Leaf — unconditional ∃-head, bridges to ANY gate.**  The per-value block (`EmitScansInFlowBlock`)
  stores its head content-start UNCONDITIONALLY (`∃ h, ContentStartTok (block.head h)`).  A bridge
  intro's-and-DISCARDS any gate premise, so it yields `≠ G → content` for EVERY `G` — the `SepAdj`
  mirror `sepAdj_head_of_block_contentStart` is the opener bridge with the gate token swapped.
* **Recursive carrier — gate-COLLAPSED head, lossy for the sibling gate.**  The list body
  (`EmitListScansInFlowBlock`) does NOT keep the ∃-head; its threaded head field was already PROJECTED
  to the FIRST consumer's gate `≠ .flowSequenceEnd`.  Deriving the mirror's `≠ .key → content` from
  `≠ .flowSequenceEnd → content` needs `(≠ .key → ≠ .flowSequenceEnd)` ≡ `(= .flowSequenceEnd → = .key)`,
  FALSE — so the recursive carrier CANNOT source the relocated obligation; it owes a NEW `≠ .key`-gated
  head field.

The toy makes the asymmetry literal:

* `headC` / `bridge` / `bridge_gateA` / `bridge_gateB` — the LEAF: one unconditional head fact, a
  GATE-AGNOSTIC bridge, and its two specialisations to the sibling gate `seqEnd` and the mirror gate
  `key` — the SAME proof at two tokens (the head-bridge clone, positive relocation).
* `gateA_head` / `gateB_head` / `gateB_from_gateA_fails` — the RECURSIVE carrier: the gate-projected
  head `gateA_head` (gate `seqEnd`) does NOT yield `gateB_head` (gate `key`), refuted by the concrete
  witness `[seqEnd]` (where `gateA_head` holds VACUOUSLY yet `gateB_head` is FALSE) — the lossiness, so
  un-ignoring the sibling's head field is INSUFFICIENT.

Sharpens `TriggerCoincidenceRelocatesObligation` (R421 relocates the obligation to the seam; this prices
the seam's SOURCE — leaf-unconditional vs recursive-gate-collapsed).  Failure-mode dual of
`CoerceToWeakerReuseWrapper` (there strong→weak coerces; here the recursive form is weak along the
SIBLING'S axis, so weak→your-gate is impossible — thread, don't coerce).
-/

namespace Tests.Reflections.SourceGateCollapseBlocksMirror

set_option autoImplicit false

/-- Toy token kinds: content-starts `scal` / `opn`; the sibling's close `seqEnd` (the `OpenerAdj` gate);
    the mirror's key indicator `key` (the `SepAdj` gate).  The two gate tokens are DISTINCT — that
    distinctness is exactly what makes the gate-projected head lossy. -/
inductive Tok | scal | opn | seqEnd | key
  deriving DecidableEq, BEq

/-- Content-start predicate (toy of `isFlowContentStart`): a value head, not a structural marker. -/
def isContent : Tok → Bool
  | .scal => true
  | .opn  => true
  | _     => false

/-! ## The LEAF source: an UNCONDITIONAL head fact bridges to ANY gate. -/

/-- The leaf's stored head fact (toy of `∃ h, ContentStartTok (block.head h)`): the head is content,
    UNCONDITIONALLY — no gate baked in, so `isContent` is kept raw. -/
def headC (l : List Tok) : Prop := ∃ (h : 0 < l.length), isContent (l[0]'h) = true

/-- The **gate-agnostic bridge**: from the unconditional head, for ANY excluded token `G`, the gated
    form `head ≠ G → isContent head` holds — the gate premise is intro'd and DISCARDED.  This one
    parametric lemma is why the LEAF head bridge mirrors to either sibling gate for free. -/
theorem bridge (G : Tok) (l : List Tok) (h : headC l) :
    ∀ (h0 : 0 < l.length), (l[0]'h0) ≠ G → isContent (l[0]'h0) = true := by
  obtain ⟨_h0', hc⟩ := h
  intro _h0 _hne
  exact hc

/-- LEAF bridge to the sibling's gate `seqEnd` — `bridge` at `G := seqEnd`. -/
theorem bridge_gateA (l : List Tok) (h : headC l) :
    ∀ (h0 : 0 < l.length), (l[0]'h0) ≠ Tok.seqEnd → isContent (l[0]'h0) = true :=
  bridge Tok.seqEnd l h

/-- LEAF bridge to the mirror's gate `key` — the SAME `bridge` at `G := key` (the verbatim clone). -/
theorem bridge_gateB (l : List Tok) (h : headC l) :
    ∀ (h0 : 0 < l.length), (l[0]'h0) ≠ Tok.key → isContent (l[0]'h0) = true :=
  bridge Tok.key l h

/-! ## The RECURSIVE source: a GATE-PROJECTED head does NOT yield the sibling gate. -/

/-- The recursive carrier's stored head (toy of `EmitListScansInFlowBlock`'s gate-`≠.flowSequenceEnd`
    head field): already PROJECTED to the sibling's gate `seqEnd` when first threaded — the
    unconditional `isContent` is GONE, only `≠ seqEnd → isContent` survives. -/
def gateA_head (l : List Tok) : Prop :=
  ∀ (h0 : 0 < l.length), (l[0]'h0) ≠ Tok.seqEnd → isContent (l[0]'h0) = true

/-- The mirror's NEEDED form, gated on `key` (toy of `SepAdj_seam`'s `h_head_rest`). -/
def gateB_head (l : List Tok) : Prop :=
  ∀ (h0 : 0 < l.length), (l[0]'h0) ≠ Tok.key → isContent (l[0]'h0) = true

/-- The lossiness witness: a head that IS the sibling's gate token. -/
def wSeqEnd : List Tok := [Tok.seqEnd]

/-- `gateA_head` holds on `[seqEnd]` — VACUOUSLY: its premise `seqEnd ≠ seqEnd` is false. -/
theorem gateA_head_wSeqEnd : gateA_head wSeqEnd := by
  intro h0 hne
  have he : (wSeqEnd[0]'h0) = Tok.seqEnd := rfl
  rw [he] at hne
  exact absurd rfl hne

/-- `gateB_head` is FALSE on `[seqEnd]` — its premise `seqEnd ≠ key` is TRUE, so it needs
    `isContent seqEnd`, which is `false`. -/
theorem not_gateB_head_wSeqEnd : ¬ gateB_head wSeqEnd := by
  intro h
  have hlen : 0 < wSeqEnd.length := by decide
  have he : (wSeqEnd[0]'hlen) = Tok.seqEnd := rfl
  have hc : isContent (wSeqEnd[0]'hlen) = true := h hlen (by rw [he]; decide)
  rw [he] at hc
  exact absurd hc (by decide)

/-- **NEGATIVE** — no `gateA_head → gateB_head` exists: the gate-projected (recursive) head is LOSSY
    for the sibling gate, so un-ignoring `_h_head_rest` is INSUFFICIENT and the carrier owes a new
    `key`-gated field.  Witness `wSeqEnd`. -/
theorem gateB_from_gateA_fails : ¬ (∀ l, gateA_head l → gateB_head l) := by
  intro hall
  exact not_gateB_head_wSeqEnd (hall wSeqEnd gateA_head_wSeqEnd)

/-! ## POSITIVE contrast — the UNCONDITIONAL leaf source yields BOTH gates. -/

/-- A content leaf head. -/
def wScal : List Tok := [Tok.scal]

theorem headC_wScal : headC wScal := ⟨by decide, by decide⟩

/-- From the unconditional head, BOTH the sibling-gate and mirror-gate forms hold — the leaf bridges
    for free (contrast `gateB_from_gateA_fails`, where the recursive carrier cannot). -/
theorem gateA_and_gateB_of_headC : gateA_head wScal ∧ gateB_head wScal :=
  ⟨bridge_gateA wScal headC_wScal, bridge_gateB wScal headC_wScal⟩

#guard isContent Tok.seqEnd == false     -- the gate-collapse witness: seqEnd is NOT content
#guard isContent Tok.scal   == true       -- the unconditional source's content head

end Tests.Reflections.SourceGateCollapseBlocksMirror
