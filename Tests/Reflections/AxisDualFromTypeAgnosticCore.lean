/-
# Reflection 538 — an AXIS DUAL of a locator chain is a near-verbatim mirror when its core
primitives are TYPE-AGNOSTIC (bit-blind) or GENERIC in the tag bit; the ONLY proof content is a
single BRANCH-VACUITY FLIP at the point where the bit is consumed to pick a constructor.

Self-contained companion to the map descent LOCATE half
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`):
`flowBracketBalance_pos_of_mapTypedInterior`, `mapEnclosingOpener_of_gate`,
`mapOpenerType_of_located_and_gate` — the `some false`/`{` dual of the seq locate trio
(`flowBracketBalance_pos_of_seqTypedInterior`, `seqEnclosingOpener_of_gate`,
`seqOpenerType_of_located_and_gate`).

The point this file isolates — **when a downstream lemma chain is a DUAL over a single tag bit (here
seq `[` ↦ `true`, map `{` ↦ `false`), the dual is nearly FREE precisely when the chain's primitives do
not branch on the bit:**

* a primitive is **TYPE-AGNOSTIC** if it reads only bit-blind facts (here the backward balance scan,
  which finds the enclosing opener from balance alone, never inspecting whether it is `[` or `{`); the
  dual reuses it VERBATIM.
* a primitive is **GENERIC in the bit** if it takes the bit as a PARAMETER (here the head-positivity
  lemma `…_pos_of_btFold_head` takes `hd : Bool`); the dual instantiates it with the other bit — a
  one-symbol swap, ZERO proof difference.

**The only proof content of the whole dual lives at the ONE site where the bit is CONSUMED to pick a
constructor** — the opener-type dispatch.  There a decidable two-constructor case split (`delta = 1`:
the opener is `[` OR `{`) is resolved by the gate's head bit: one case discharges the typed conclusion,
the OTHER is killed as absurd (its pushed bit contradicts the gate head).  The seq and map proofs are
the SAME skeleton with the two branches' roles SWAPPED — that flip is the entire cost of the dual.
This is the [[ref-mirror-reads-conjunct-not-projection]] text-swap with one extra symbol, the
branch-vacuity flip, and the absurd branch is [[ref-converse-forward-invariant-asymmetry]] read as
opener-bit exclusivity.

What this file does:
* `Opener` / `pushedBit` — the two flow openers and the bit each pushes (`[ ↦ true`, `{ ↦ false`).
* `pos_generic` + `pos_seq` / `pos_map` — the head-positivity core GENERIC in `hd : Bool`; the two
  axes differ only by instantiating `true` vs `false`.  The toy of `…_pos_of_btFold_head`.
* `locatedDeltaOne` / `locate_any` — the TYPE-AGNOSTIC locate: it returns "the opener is one of the
  two" without reading the bit.  The toy of the backward balance scan.
* `openerType_seq` / `openerType_map` — the dispatch, the ONLY place with proof content; the two are
  the SAME proof with the live/absurd branches SWAPPED (the branch-vacuity flip).
* end-to-end `example`s running each axis, and an axiom audit (the dual depends on NO axioms).
-/

namespace AxisDualFromTypeAgnosticCore

set_option autoImplicit false

/-! ## The tag bit — the only thing the two axes disagree on. -/

/-- Toy of the two flow openers: `[` (sequence) and `{` (mapping). -/
inductive Opener where
  | seqStart
  | mapStart

/-- The bit an opener pushes onto the typed bracket stack (`btStep`'s convention): `[ ↦ true`,
    `{ ↦ false`.  This is the SOLE bit-valued discriminator the two axes split on. -/
def pushedBit : Opener → Bool
  | .seqStart => true
  | .mapStart => false

/-! ## Primitive 1 — GENERIC in the bit: one lemma, both axes instantiate. -/

/-- **GENERIC head-positivity** (toy of `flowBracketBalance_pos_of_btFold_head`, which takes
    `hd : Bool`).  A gate whose enclosing typed-stack head is `some hd` — for ANY bit `hd` — forces the
    enclosing balance positive (a non-empty stack).  The bit is a PARAMETER the proof never inspects, so
    both axes share this one proof. -/
theorem pos_generic (hd : Bool) (stackHead : Option Bool) (bal : Nat)
    (h_head : stackHead = some hd) (h_pos : stackHead ≠ none → bal ≥ 1) : bal ≥ 1 :=
  h_pos (by rw [h_head]; exact Option.some_ne_none hd)

/-- The SEQ instantiation — `hd := true`.  A one-symbol swap from `pos_map`, no proof difference. -/
theorem pos_seq (stackHead : Option Bool) (bal : Nat)
    (h_head : stackHead = some true) (h_pos : stackHead ≠ none → bal ≥ 1) : bal ≥ 1 :=
  pos_generic true stackHead bal h_head h_pos

/-- The MAP instantiation — `hd := false`.  The dual of `pos_seq`: same call, bit flipped. -/
theorem pos_map (stackHead : Option Bool) (bal : Nat)
    (h_head : stackHead = some false) (h_pos : stackHead ≠ none → bal ≥ 1) : bal ≥ 1 :=
  pos_generic false stackHead bal h_head h_pos

/-! ## Primitive 2 — TYPE-AGNOSTIC: locate the opener without reading the bit. -/

/-- The located-opener fact the backward balance scan delivers: the opener has `delta = 1`, i.e. it is
    ONE of the two flow openers — but the scan is BLIND to which.  Toy of
    `flowBracketBalance_backward_open_locate`'s `flowBracketDelta tokens[p]! = 1`. -/
def locatedDeltaOne (o : Opener) : Prop := o = .seqStart ∨ o = .mapStart

/-- **The locate is TYPE-AGNOSTIC** — it produces `delta = 1` for either opener with the SAME proof; the
    bit never enters.  So the dual reuses it verbatim. -/
theorem locate_any (o : Opener) : locatedDeltaOne o := by
  cases o
  · exact Or.inl rfl
  · exact Or.inr rfl

/-! ## The dispatch — the ONLY site with proof content, and the BRANCH-VACUITY FLIP. -/

/-- **OpenerType dispatch, SEQ axis** (toy of `seqOpenerType_of_located_and_gate`).  From `delta = 1`
    (the opener is `[` or `{`) and the gate head `= true`, the located opener is a `[`.  The two cases:
    the seq-opener case DISCHARGES the conclusion; the map-opener case is killed ABSURD (it pushes
    `false ≠ true`). -/
theorem openerType_seq (o : Opener) (h_delta : locatedDeltaOne o)
    (h_head : pushedBit o = true) : o = .seqStart := by
  rcases h_delta with hseq | hmap
  · exact hseq
  · rw [hmap] at h_head; exact absurd h_head (by decide)

/-- **OpenerType dispatch, MAP axis — the DUAL** (toy of `mapOpenerType_of_located_and_gate`).  Identical
    skeleton with the BRANCH-VACUITY FLIP: the gate head is `= false`, so now the MAP-opener case
    discharges the conclusion and the SEQ-opener case is killed absurd.  Diff vs `openerType_seq`: the
    two `rcases` branch bodies are SWAPPED — that flip is the whole cost of the axis dual. -/
theorem openerType_map (o : Opener) (h_delta : locatedDeltaOne o)
    (h_head : pushedBit o = false) : o = .mapStart := by
  rcases h_delta with hseq | hmap
  · rw [hseq] at h_head; exact absurd h_head (by decide)
  · exact hmap

/-! ## The duals RUN end-to-end on each axis. -/

/-- The seq axis runs: locate (type-agnostic) feeds the seq dispatch to a `[`. -/
example : Opener.seqStart = .seqStart :=
  openerType_seq .seqStart (locate_any _) rfl

/-- The map axis runs: the SAME type-agnostic locate feeds the dual dispatch to a `{`. -/
example : Opener.mapStart = .mapStart :=
  openerType_map .mapStart (locate_any _) rfl

end AxisDualFromTypeAgnosticCore

/-- info: 'AxisDualFromTypeAgnosticCore.openerType_map' does not depend on any axioms -/
#guard_msgs in
#print axioms AxisDualFromTypeAgnosticCore.openerType_map

/-- info: 'AxisDualFromTypeAgnosticCore.pos_generic' does not depend on any axioms -/
#guard_msgs in
#print axioms AxisDualFromTypeAgnosticCore.pos_generic
