/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-! # A held token re-points the index that names its neighbour (Reflection 620)

The plan said: widen the flow-interior slot so it can hold a scanned but
unattached `[96] c-ns-properties`.  The slot was the obvious thing to change —
`&a` completes no node, so it has to sit somewhere until the next character says
whether it decorates a node or an empty scalar.

The first thing that broke was not the slot.

The accumulation invariant names the open frame by an index computed from the
token history, `tailOf sc.tokens`, and `tailOf` read the LAST REAL token.  The
moment `&a` is scanned after `[`, that reading changes — an anchor completes no
flow value, so the index becomes `.colon` — while the frame itself is untouched,
still the empty `betweenEmpty` frame, whose index is `.sep`.  Nothing about the
frame changed; only the name the invariant computes for it did.  And there is no
`.colon`-indexed empty frame, so the invariant became unsatisfiable **before any
vocabulary for the slot was written at all**.

So the index has to read PAST whatever the slot holds.  That repair has its own
dual, and it is the part worth remembering: the index was not decorative, it was
*transporting two scanner guards*.  `scanNextToken_checkFlowAdjacency` and
`scanFlowEntry` both read the last real token, and the accumulation turned their
success into `tailOf … ≠ .value` and `≠ .sep`.  An index that reads past a held
run no longer reads what those guards read, so both transports go false — and
they go false for a real reason: `[a &b` would have the guard's token be the
harmless `&b` while the frame's token is the completed `a`.  (The scanner
rejects that input at the `&`, which is why the accumulation never meets it, but
the LEMMA cannot know that.)

The fix is to carry the **coincidence of the two readings** as a conjunct of the
invariant — true exactly when the slot is empty — and to state both transports
under it.  That conjunct is the whole mechanical cost, paid once at every
producer, and it is what makes the slot's new constructor purely additive: the
`props` case simply does not carry it.

L4YAML DOCS item 10 (β.3), 2026-08-08.
-/

namespace Tests.Reflections.HeldTokenRepointsIndex

/-! ## §0  The substrate

Three token classes are enough: an `opener` (`[`), a `value` (a scalar — it
COMPLETES a flow value), and a `prop` (`&a`/`!t` — it completes nothing).
Histories are newest-last. -/

inductive Tok where
  | opener | value | prop
  deriving DecidableEq, Repr, BEq

/-- `&a` and `!t`: the tokens a node property emits. -/
def Tok.isProp : Tok → Bool
  | .prop => true
  | _     => false

/-- The scanner's own reading: the last token, whatever it is. -/
def lastTok? (ts : List Tok) : Option Tok := ts.reverse.head?

/-! ## §1  The index, and the frames it names -/

inductive Idx where
  | sep | value | colon
  deriving DecidableEq, Repr, BEq

/-- `value` completes a flow value; `opener` leaves the frame at a separator;
    anything else — a property included — reads as `colon`. -/
def ofTok : Tok → Idx
  | .value  => .value
  | .opener => .sep
  | .prop   => .colon

/-- The index as it WAS: read the last token. -/
def rawIdx (ts : List Tok) : Idx :=
  match lastTok? ts with
  | some t => ofTok t
  | none   => .colon

/-- The index as it must be: read past the trailing property run. -/
def frameIdx (ts : List Tok) : Idx :=
  match (ts.reverse.dropWhile Tok.isProp) with
  | t :: _ => ofTok t
  | []     => .colon

/-- The open frame, indexed. Two shapes only, and neither is `.colon`-indexed:
    `empty` is what `[` leaves behind, `held` is a completed entry. That
    absence is the whole content of §2. -/
inductive Frame : Idx → Prop where
  | empty : Frame .sep
  | held  : Frame .value

theorem no_colon_frame : ¬ Frame .colon := by
  intro h; cases h

/-! ## §2  The index broke, not the slot

`[ &a` — an opener then a held property. The frame is still `empty`. -/

theorem raw_index_moves : rawIdx [Tok.opener, Tok.prop] = .colon := by decide

theorem frame_index_holds : frameIdx [Tok.opener, Tok.prop] = .sep := by decide

/-- …so under the OLD index the invariant is unsatisfiable at that history:
    it demands a frame that does not exist. Note the failure is not "the slot is
    too narrow" — no slot appears in this statement at all. -/
theorem raw_index_unsatisfiable : ¬ Frame (rawIdx [Tok.opener, Tok.prop]) := by
  rw [raw_index_moves]; exact no_colon_frame

/-- Under the new index the frame that was already there still fits. -/
theorem frame_index_satisfiable : Frame (frameIdx [Tok.opener, Tok.prop]) := by
  rw [frame_index_holds]; exact .empty

/-- And the repair is invisible when nothing is held: the two indices agree on
    every history whose last token is not a property. -/
theorem indices_agree_when_nothing_held (ts : List Tok) (t : Tok)
    (h : t.isProp = false) : frameIdx (ts ++ [t]) = rawIdx (ts ++ [t]) := by
  simp [frameIdx, rawIdx, lastTok?, h]

/-! ## §3  …but reading past the run breaks the guard transports

The scanner's guard says "the last token does not complete a flow value". That
was enough to conclude `≠ .value` while the index read the same token. It is not
enough afterwards — and the counterexample is a history, not an abstraction. -/

/-- The guard, as the scanner states it. -/
def guardHolds (ts : List Tok) : Prop :=
  ∀ t, lastTok? ts = some t → t ≠ Tok.value

/-- `[a &b`: the guard is satisfied (the last token is a property, which
    completes nothing) and the frame index is nevertheless `.value`. -/
theorem transport_fails_without_sync :
    ∃ ts, guardHolds ts ∧ frameIdx ts = .value := by
  refine ⟨[Tok.value, Tok.prop], ?_, by decide⟩
  intro t ht
  have : t = Tok.prop := by simpa [lastTok?] using ht.symm
  subst this; decide

/-- The transport under the OLD index was sound — that is why it was never
    stated with a side condition. -/
theorem raw_transport_is_sound {ts : List Tok} (h : guardHolds ts) :
    rawIdx ts ≠ .value := by
  unfold rawIdx
  cases hl : lastTok? ts with
  | none => decide
  | some t =>
    have hne := h t hl
    cases t <;> simp_all [ofTok]

/-! ## §4  The coincidence conjunct

`Sync` says the two readings pick the same token. It is exactly "nothing is
held", and it is the hypothesis under which the transport survives. -/

def Sync (ts : List Tok) : Prop := frameIdx ts = rawIdx ts

theorem transport_under_sync {ts : List Tok} (hsync : Sync ts) (h : guardHolds ts) :
    frameIdx ts ≠ .value := by
  rw [hsync]; exact raw_transport_is_sound h

/-- Every step that emits one non-property token re-establishes it — which is
    why the conjunct is cheap: it is discharged wherever the old proof already
    knew which token it had just pushed. -/
theorem sync_of_push (ts : List Tok) (t : Tok) (h : t.isProp = false) :
    Sync (ts ++ [t]) := indices_agree_when_nothing_held ts t h

/-- And it is genuinely absent while a run is held — the conjunct carries
    information, it is not bookkeeping. -/
theorem sync_fails_while_held : ¬ Sync [Tok.opener, Tok.prop] := by
  simp only [Sync, raw_index_moves, frame_index_holds]; decide

/-! ## §5  Why this ordering makes the slot additive

The invariant's interior conjunct starts with one constructor carrying `Sync`.
The `props` constructor, when it lands, simply omits it — no existing case is
touched, and the two `Inv` cases below are already distinguishable exactly where
they need to be. -/

/-- The invariant as landed: whitespace only, plus the coincidence. -/
inductive Inv (ts : List Tok) : Prop where
  | white (hsync : Sync ts) : Inv ts

/-- The invariant as it will read. Adding the case is additive: `white` is
    unchanged, and every consumer that already had `Sync` still has it. -/
inductive Inv' (ts : List Tok) : Prop where
  | white (hsync : Sync ts) : Inv' ts
  | props (hheld : ts.reverse.head? = some Tok.prop) : Inv' ts

theorem inv_embeds (ts : List Tok) (h : Inv ts) : Inv' ts := by
  cases h with | white hs => exact .white hs

/-- The added case is reachable — the held history that broke §2 inhabits it,
    and no `white` proof does. -/
theorem props_case_is_new :
    Inv' [Tok.opener, Tok.prop] ∧ ¬ Inv [Tok.opener, Tok.prop] := by
  refine ⟨.props (by decide), ?_⟩
  intro h
  cases h with | white hs => exact absurd hs sync_fails_while_held

/-! ## §6  The sweep

Computed, not recalled: where the two indices differ, and whether that is
exactly where a property is held. -/

def histories : List (List Tok) :=
  [[], [.opener], [.value], [.prop],
   [.opener, .prop], [.value, .prop], [.opener, .value],
   [.value, .prop, .prop], [.opener, .value, .prop]]

-- The two indices differ on exactly four of the nine histories.
#guard (histories.filter fun ts => frameIdx ts != rawIdx ts) ==
  [[Tok.opener, Tok.prop], [Tok.value, Tok.prop],
   [Tok.value, Tok.prop, Tok.prop], [Tok.opener, Tok.value, Tok.prop]]

-- …all of which end in a held property.  The converse FAILS, and the exception
-- is instructive: `[prop]` alone ends in a property and the two still agree,
-- because reading past it lands on nothing and both fall back to `.colon`.  So
-- "a property is held" is strictly stronger than "the readings differ" — which
-- is why the invariant carries the coincidence itself and not "the run is
-- empty": the weaker, exactly-right hypothesis is the one the transports need.
#guard (histories.filter fun ts =>
    frameIdx ts != rawIdx ts && (ts.reverse.head?.map Tok.isProp) != some true) == []
#guard (histories.filter fun ts =>
    (ts.reverse.head?.map Tok.isProp) == some true && frameIdx ts == rawIdx ts) ==
  [[Tok.prop]]

-- On every history a flow collection can actually reach — they all begin with
-- the opener — the frame index never names the shape that does not exist.
#guard (histories.filter fun ts =>
    ts.head? == some Tok.opener && frameIdx ts == Idx.colon) == []

/-! ## §7  Axiom pins

The two load-bearing claims are the failure and its repair: the old index makes
the invariant unsatisfiable, and the transport survives only under `Sync`. -/

/-- info: 'Tests.Reflections.HeldTokenRepointsIndex.raw_index_unsatisfiable' does not depend on any axioms -/
#guard_msgs in
#print axioms raw_index_unsatisfiable

/-- info: 'Tests.Reflections.HeldTokenRepointsIndex.transport_fails_without_sync' depends on axioms: [propext] -/
#guard_msgs in
#print axioms transport_fails_without_sync

/-- info: 'Tests.Reflections.HeldTokenRepointsIndex.transport_under_sync' depends on axioms: [propext] -/
#guard_msgs in
#print axioms transport_under_sync

/-- info: 'Tests.Reflections.HeldTokenRepointsIndex.props_case_is_new' depends on axioms: [propext] -/
#guard_msgs in
#print axioms props_case_is_new

end Tests.Reflections.HeldTokenRepointsIndex

end Blanket
