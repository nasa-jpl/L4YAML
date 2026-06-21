/-!
# Reflection 487 — a folded co-construction half bottoms out at its SIBLING's output.

Self-contained (core Lean, no `L4YAML` import) toy recording the shape R487 landed:
`seqLocalCarrier_of_recIH`, the CARRIER half of the carrier↔`RecSeqBody` width co-construction,
folded down to its three genuine inputs.

**The setup.**  The last seq residual is a JOINT co-construction: a strong induction on window WIDTH
producing, per body window `[lo, hi)`, the PAIR `SeqInteriorSeparators tokens lo hi`  (the local
*carrier*) `∧ RecSeqBody ((take hi).drop lo)`  (the *recursion* output).  The two conjuncts are mutually
feeding, joined only by the shared well-founded measure (width):

* the RECURSION half builds this window's `RecSeqBody`, consuming the carrier only at STRICTLY-NARROWER
  sub-windows (gated `< hi - lo`);
* the CARRIER half builds this window's `SeqInteriorSeparators`, consuming (i) this window's own
  `SafeBodyUnit` and (ii) a strictly-narrower `RecSeqBody`-IH.

**What R487 landed.**  `seqLocalCarrier_of_recIH` folds the carrier half's whole `widthEnc` chain
(`seqWidthEnc_of_recIH` ∘ `seqLocalCarrier_of_widthEnc`, R486 ∘ R446) into ONE signature whose inputs
are exactly the three the joint step can supply: the body-window facts, the window's own `SafeBodyUnit`,
and the body-width `RecSeqBody`-IH.  (This CONSUMES R486 — `ref-reduction-by-import` retype-is-progress
— and is `ref-fold-consumer-chain-to-producer-contract` applied to the carrier half.)

**The transferable rule.**  When you fold a consumer chain that is ONE HALF of a mutual
co-construction, the folded contract's inputs partition into

* genuine EXTERNALS the joint step already holds (here: the body-window facts + the width IH), and
* at least one SIBLING-SUPPLIED input = the OTHER half's output, possibly projected (here: the window's
  own `SafeBodyUnit` = `RecSeqBody.toSafeBodyUnit` of the recursion half's output at THIS window).

Recognizing the sibling-supplied input is what tells you (1) the fold has bottomed out at the
co-construction BOUNDARY, not at external givens; (2) the joint step's evaluation ORDER — produce the
sibling's output first, then project it in; and (3) that the co-construction is ACYCLIC, because the
sibling consumes only STRICTLY-SMALLER instances of the shared measure, never this window's output.

This toy models the two halves as mutually-recursive `Prop`s over a `Nat` width, exhibits the carrier
half's folded contract with its sibling-supplied input, and closes the joint co-construction by ONE
strong induction whose acyclicity is load-bearing on the `< n` gating.
-/

namespace CoconstructionHalfFoldsToSiblingInput

set_option autoImplicit false

/-! ### The two mutually-recursive halves over a width measure.

`Rec n` — the RECURSION half at width `n`; its sole field consumes `Carrier` only at `m < n`.
`Carrier n` — the CARRIER half at width `n`; it consumes THIS window's own `Rec n` (the
sibling-supplied input, modelling `h_safe`) plus a strictly-narrower `Rec`-IH (modelling `recIH`). -/
mutual
  inductive Carrier : Nat → Prop where
    /-- toy `seqLocalCarrier_of_widthEnc`'s assemble: needs the sibling's own output `hSelfRec : Rec n`
        (the window's `RecSeqBody`, projected to `SafeBodyUnit`) and the narrower `Rec`-IH. -/
    | mk (n : Nat) (hSelfRec : Rec n) (hRecIH : ∀ m, m < n → Rec m) : Carrier n
  inductive Rec : Nat → Prop where
    /-- toy recursion half: builds this window's `RecSeqBody`, consuming `Carrier` only at `m < n`. -/
    | mk (n : Nat) (hCarrierIH : ∀ m, m < n → Carrier m) : Rec n
end

/-! ### `Safe` — the sibling-output projection (toy `RecSeqBody.toSafeBodyUnit`).

In the real code the carrier half consumes a `SafeBodyUnit`, the strictly-WEAKER projection of the
window's `RecSeqBody`.  Here `Safe n := Rec n` with the identity projection keeps the directional
dependency (Carrier ← Safe ← Rec = sibling) while staying minimal. -/
def Safe (n : Nat) : Prop := Rec n

/-- The projection that makes `Safe` SIBLING-supplied: you get it from the recursion half's output. -/
theorem rec_to_safe {n : Nat} (h : Rec n) : Safe n := h

/-! ### The carrier half, folded into ONE contract — toy `seqLocalCarrier_of_recIH`.

The fold is two steps, mirroring `seqLocalCarrier_of_widthEnc ∘ seqWidthEnc_of_recIH`. -/

/-- The toy `widthEnc` deliverable: the narrower-`Rec`-IH, renamed (the real one also carries the
    enclosing-window facts — elided here as they are pure externals). -/
def WidthEnc (n : Nat) : Prop := ∀ m, m < n → Rec m

/-- Toy `seqWidthEnc_of_recIH` (R486): turn the body-width `recIH` into the `widthEnc` deliverable. -/
theorem widthEnc_of_recIH {n : Nat} (recIH : ∀ m, m < n → Rec m) : WidthEnc n := recIH

/-- Toy `seqLocalCarrier_of_widthEnc` (R446): consume the `widthEnc` deliverable + the window's own
    `SafeBodyUnit` to assemble the carrier. -/
theorem carrier_of_widthEnc {n : Nat} (hSafe : Safe n) (hWE : WidthEnc n) : Carrier n :=
  Carrier.mk n hSafe hWE

/-- **The folded carrier half** — toy `seqLocalCarrier_of_recIH` (R487).  Its three inputs:
    `hSafe` (SIBLING-supplied: the window's own `Rec`, projected) and `recIH` (a genuine external: the
    body-width IH).  The body-window facts are elided as further pure externals.  The whole `widthEnc`
    chain is folded into this one signature. -/
theorem carrier_of_recIH {n : Nat} (hSafe : Safe n) (recIH : ∀ m, m < n → Rec m) : Carrier n :=
  carrier_of_widthEnc hSafe (widthEnc_of_recIH recIH)

/-! ### Closing the joint co-construction by ONE strong induction.

The sibling-supplied input FIXES the step order: build `Rec n` first (consuming `Carrier` at `m < n`),
project it to `Safe n`, then feed that into the carrier half (which also consumes `Rec` at `m < n`).
Acyclicity is load-bearing: `Rec.mk` needs `Carrier m` only for `m < n`, so the strong recursion closes.
Had `Rec.mk` needed `Carrier n` (same width), we would need `Carrier n` to build `Rec n` to build
`Safe n` to build `Carrier n` — a cycle the `< n` gating is precisely what avoids. -/
theorem coconstruct (n : Nat) : Carrier n ∧ Rec n :=
  Nat.strongRecOn n (fun n IH =>
    -- sibling half FIRST: build this window's `Rec`, consuming `Carrier` only at `m < n`.
    have hRec : Rec n := Rec.mk n (fun m hm => (IH m hm).1)
    -- carrier half: its `hSafe` is the sibling's output PROJECTED — never an external given.
    ⟨carrier_of_recIH (rec_to_safe hRec) (fun m hm => (IH m hm).2), hRec⟩)

/-- The carrier exists at every width — the deliverable the joint induction hands the consumer. -/
theorem carrier_everywhere (n : Nat) : Carrier n := (coconstruct n).1

/-- The recursion output exists at every width — the sibling deliverable. -/
theorem rec_everywhere (n : Nat) : Rec n := (coconstruct n).2

end CoconstructionHalfFoldsToSiblingInput
