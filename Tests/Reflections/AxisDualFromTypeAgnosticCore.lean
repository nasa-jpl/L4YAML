/-
# Reflections 538–539 — an AXIS DUAL of a locator chain is a near-verbatim mirror when its core
primitives are TYPE-AGNOSTIC (bit-blind) or GENERIC in the tag bit; the ONLY proof content is a
single BRANCH-VACUITY FLIP at the point where the bit is consumed to pick a constructor — and a brick
DOWNSTREAM of that one dispatch, reading only the bit's type-agnostic residue, costs ZERO (R539).

Self-contained companion to the map descent LOCATE half + CLOSE brick
(`L4YAML/Proofs/Output/EmitterScannability/SeqInteriorSeparators.lean`):
`flowBracketBalance_pos_of_mapTypedInterior`, `mapEnclosingOpener_of_gate`,
`mapOpenerType_of_located_and_gate` (R538), `mapClose_of_located_and_enclosing` (R539) — the
`some false`/`{` duals of the seq locate trio + close
(`flowBracketBalance_pos_of_seqTypedInterior`, `seqEnclosingOpener_of_gate`,
`seqOpenerType_of_located_and_gate`, `seqClose_of_located_and_enclosing`).

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
* (R539) `Closer` / `closerDelta` / `matchClose` / `aleqj_of_relay` / `close_seq` / `close_map` — the
  PURE-SWAP floor: a brick DOWNSTREAM of the dispatch (the matching CLOSE) has no bit-consuming site of
  its own — the matching-close map is generic, the bound relay reads only the type-agnostic
  `closerDelta = -1` — so its dual is a pure token-swap, proof body byte-identical, ZERO flip.
* end-to-end `example`s running each axis, and axiom audits (`close_map`/`pos_generic`/`openerType_map`
  axiom-free; the omega-backed relay `aleqj_of_relay` carries only `[propext, Quot.sound]`).
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

/-! ## The PURE-SWAP floor — a dual brick with NO bit-consuming dispatch costs ZERO proof content (R539).

The opener-type dispatch above paid for a branch-vacuity FLIP because it CONSUMES the bit to pick a
constructor.  A brick DOWNSTREAM of that dispatch — the matching CLOSE (toy of
`mapClose_of_located_and_enclosing`, the `_map` dual of `seqClose_of_located_and_enclosing`) — has no
dispatch of its own.  Its two ingredients are both bit-blind:

* the matching closer is delivered by a GENERIC matching-close map (`matchClose`, toy of
  `flowBracketBalance_matching_close_{seq,map}` which already bundle the typed `.flowSequenceEnd` /
  `.flowMappingEnd`); each axis instantiates it at its own opener;
* the containment-bound relay reads ONLY the TYPE-AGNOSTIC fact `closerDelta = -1` (both closers carry
  it), never the closer's identity.

So the close brick's dual is a PURE token-swap — proof body byte-IDENTICAL, ZERO flip.  This is the
delta-zero floor of the axis-dual alphabet (cf. [[ref-mirror-cost-delta-alphabet]]'s delta-zero floor for
the flat→`*Deep` mirror): once the single bit-consuming site upstream is paid, every brick below it that
reads only the bit's type-agnostic residue (`delta = -1`) is free. -/

/-- The two flow CLOSERS: `]` (sequence) and `}` (mapping). -/
inductive Closer where
  | seqEnd
  | mapEnd

/-- **TYPE-AGNOSTIC closer delta** — BOTH closers carry `-1` (toy of `flowBracketDelta`, which sends
    `.flowSequenceEnd` and `.flowMappingEnd` alike to `-1`).  The two-floor relay reads ONLY this. -/
def closerDelta : Closer → Int
  | .seqEnd => -1
  | .mapEnd => -1

/-- **GENERIC matching close** — the matching closer for each opener (toy of
    `flowBracketBalance_matching_close_{seq,map}`, which bundle the typed close).  Both axes call the same
    map, instantiated at their own opener. -/
def matchClose : Opener → Closer
  | .seqStart => .seqEnd
  | .mapStart => .mapEnd

/-- **The type-agnostic two-floor relay → containment bound** — concludes `a ≤ j` by REFUTING `j < a`:
    under `j < a` the floor forces `0 ≤ balAtJ1`, while the step `balAtJ1 = balAtJ + closerDelta c` with
    `balAtJ = 0` forces `balAtJ1 = -1` (since `closerDelta c = -1` for ANY closer `c`), so `0 ≤ -1` —
    absurd.  The proof reads `closerDelta c = -1` via `cases c <;> rfl`, never the closer's identity, so
    both axes share it verbatim.  Toy of the `a ≤ j` / `b ≤ j` two-floor relay in
    `map`/`seqClose_of_located_and_enclosing`. -/
theorem aleqj_of_relay (c : Closer) (a j : Nat) (balAtJ balAtJ1 : Int)
    (h_balJ : balAtJ = 0) (h_step : balAtJ1 = balAtJ + closerDelta c)
    (h_floor_lt : j < a → 0 ≤ balAtJ1) : a ≤ j := by
  have h_delta : closerDelta c = -1 := by cases c <;> rfl
  rcases Nat.lt_or_ge j a with h | h
  · have := h_floor_lt h
    omega
  · exact h

/-- The seq CLOSE brick (toy of `seqClose_of_located_and_enclosing`): the located matching closer is a
    `]`, read off the generic `matchClose` by `rfl`. -/
theorem close_seq : matchClose .seqStart = .seqEnd := rfl

/-- The map CLOSE brick — the DUAL (toy of `mapClose_of_located_and_enclosing`).  Diff vs `close_seq`:
    `.seqStart → .mapStart`, `.seqEnd → .mapEnd`.  Proof body byte-IDENTICAL (`rfl`); NO `rcases`, NO
    flip — the matching-close map is generic and the relay is type-agnostic, so the close has no
    bit-consuming dispatch.  The whole axis-dual cost here is THREE swapped tokens, zero proof content. -/
theorem close_map : matchClose .mapStart = .mapEnd := rfl

/-- Both close bricks run the SAME type-agnostic relay to a real bound `3 ≤ 5` — instantiated at `.seqEnd`
    and `.mapEnd`, one shared proof; the `j < a` floor premise is vacuous (`5 < 3` is false). -/
example : (3 : Nat) ≤ 5 ∧ (3 : Nat) ≤ 5 :=
  ⟨aleqj_of_relay .seqEnd 3 5 0 (-1) rfl (by decide) (fun h => by omega),
   aleqj_of_relay .mapEnd 3 5 0 (-1) rfl (by decide) (fun h => by omega)⟩

end AxisDualFromTypeAgnosticCore

/-- info: 'AxisDualFromTypeAgnosticCore.openerType_map' does not depend on any axioms -/
#guard_msgs in
#print axioms AxisDualFromTypeAgnosticCore.openerType_map

/-- info: 'AxisDualFromTypeAgnosticCore.pos_generic' does not depend on any axioms -/
#guard_msgs in
#print axioms AxisDualFromTypeAgnosticCore.pos_generic

/-- info: 'AxisDualFromTypeAgnosticCore.close_map' does not depend on any axioms -/
#guard_msgs in
#print axioms AxisDualFromTypeAgnosticCore.close_map

/-- info: 'AxisDualFromTypeAgnosticCore.aleqj_of_relay' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms AxisDualFromTypeAgnosticCore.aleqj_of_relay
