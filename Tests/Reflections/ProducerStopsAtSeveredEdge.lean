/-!
# Reflection 338 — a PRODUCER stops at a severed edge as a leaf; a NAVIGATOR dies there

Self-contained (core Lean, no `L4YAML` import) toy model of the decision behind
`rec_seq_body_nested_project`.

A recursive deliverable `D` is wanted at every window of some structure.  One constructor of `D`'s
carrier is a SEVERED edge — it stores a WEAKER fact, not a recursive `D` child (mirrors
`RecSeqEntry.map`, which stores only `WellBracketed interior`, no `RecSeqBody`).  Two ways to get `D`
at a window:

* **NAVIGATE** the root carrier down to the window and read the stored sub-proof.  This DIES at the
  severed edge: a `box` has no child to descend through ([[ref-severed-edge-bounds-navigator-domain]]
  — the L4YAML R335 refutation).
* **PRODUCE** `D` FRESH from the window's own shape.  This STOPS AT the severed edge — it emits the
  `box` LEAF and recurses no further into it — so it is TOTAL where navigation dies.

The same edge is fatal to navigation (which must cross it INWARD) and invisible to production (which
STOPS at it).  When `D` is a `Prop`, proof-irrelevance makes a produced witness interchangeable with a
navigated one, so production is strictly cheaper.  The toy below mirrors that with a `Carrier` tree
whose `box` member stores only a flat `Bool`.

In L4YAML the real deliverable `RecSeqBody` is a `Prop`; here `Carrier` is a `Type` so the `#guard`s
can compare concrete witnesses — the interchangeability the `Prop` gives is noted, not modelled.
-/

namespace Tests.Reflections.ProducerStopsAtSeveredEdge

set_option autoImplicit false

/-- The carrier of a recursive deliverable.  `seq` stores a recursive CHILD (the KEPT/navigable edge);
    `box` is the SEVERED member — it stores only a flat `Bool` payload, NO recursive child.  Mirrors
    `RecSeqEntry.seq` (stores `RecSeqBody interior`) vs `RecSeqEntry.map` (stores only
    `WellBracketed interior`). -/
inductive Carrier where
  | leaf
  | seq (child : Carrier)
  | box (payload : Bool)
  deriving DecidableEq

/-- A window address: stay here, descend one `seq` level (KEPT edge), or sit inside a `box` (reached
    through the SEVERED edge — the L4YAML map-path-nested seq window). -/
inductive Window where
  | top
  | underSeq (w : Window)
  | underBox (w : Window)

/-! ## NAVIGATION — pull the stored sub-`Carrier` out of a root carrier; DIES at the severed edge

Mirrors root-`RecSeqBody`-navigation (`seqRoot_recseqbody`, R326): descends `seq` children fine, but a
`box` stores no child, so a window `underBox` is unreachable — `none`. This is the R335 refutation. -/

def navigate : Carrier → Window → Option Carrier
  | c,          .top         => some c
  | .seq child, .underSeq w  => navigate child w
  | .box _,     .underBox _  => none   -- SEVERED EDGE: a box has no child to descend into
  | _,          _            => none   -- shape mismatch

/-! ## PRODUCTION — build the deliverable FRESH from the window's shape; STOPS AT the severed edge

Mirrors `seqWindowRecSeqBody` (R323): no root carrier, no navigation.  At `underBox` it emits the `box`
LEAF and ignores the inner window entirely (`underBox _` — no recursion), so it is TOTAL. -/

def produce : Window → Carrier
  | .top        => .leaf
  | .underSeq w => .seq (produce w)
  | .underBox _ => .box true   -- STOP AT the edge: emit the leaf, do NOT descend into the box

/-! ## NEGATIVE — navigation is STUCK at the severed edge

Mirrors R335: a seq window buried in a `RecSeqEntry.map` cannot be reached from the root tree. -/

theorem severed_navigation_stuck (p : Bool) (w : Window) :
    navigate (.box p) (.underBox w) = none := rfl

/-! ## POSITIVE — production is TOTAL, emitting the severed member as a leaf

Mirrors `seqWindowRecSeqBody`'s totality: a `{`-headed first entry becomes a `RecSeqEntry.map` leaf. -/

theorem severed_production_total (w : Window) :
    produce (.underBox w) = .box true := rfl

/-- The KEPT (seq) edge navigates fine AND produces the same shape — navigation and production agree
    everywhere navigation is defined; they DIVERGE only at the severed edge. -/
theorem kept_edge_agrees (w : Window) :
    navigate (produce (.underSeq w)) (.underSeq w) = navigate (.seq (produce w)) (.underSeq w) := rfl

/-! ## Concrete witnesses — the divergence at the severed edge

A window behind a `box`: navigation `none` (stuck), production `some` (total leaf). -/

-- severed window: NAVIGATION dies...
#guard navigate (.box false) (.underBox .top) = none
-- ...but PRODUCTION is total — it stops at the box and emits the leaf:
#guard produce (.underBox .top) = .box true
-- a KEPT (seq) window: navigation succeeds AND production matches:
#guard navigate (.seq .leaf) (.underSeq .top) = some .leaf
#guard produce (.underSeq .top) = .seq .leaf

/-- End-to-end: at the severed edge navigation is stuck but production is total. -/
example :
    navigate (.box false) (.underBox .top) = none ∧ produce (.underBox .top) = .box true :=
  ⟨rfl, rfl⟩

/-! ## R412 — the CONSUMER SLOT's guard decides whether a NAVIGATOR can serve it; a path-blind gate
    conjunct masks the routing tag

When integrating a deliverable into a fixed consumer slot `h_seq_rec : <weak guard> → D window`, the
question "can the existing navigator-producer serve this slot?" is decided by the slot's GUARD SHAPE,
not by whether the navigator produces `D`.  The navigator carries a ROUTING TAG (the whole-path
`pathAllSeq`, restricting it to the navigable domain — [[ref-producer-stops-at-severed-edge]]).  It can
serve the slot ONLY if the slot's guard IMPLIES that tag.  To decide, probe a MINIMAL PAIR satisfying
the slot's WEAK guard ([[ref-minimal-pair-extracts-the-gate]]): if the routing tag SEPARATES them
(holds on one, fails the other), the weak guard does NOT imply it, so the navigator is non-total on the
slot — you need the STOP-AT-EDGE producer instead.

THE TRAP: the slot's guard often CONTAINS a path-BLIND PROJECTION of the routing tag (here `enclosedTop`,
the TOP-of-stack seq mark — `SeqEnclosed`), which makes it tempting to think the tag is covered.  It is
not: the projection SEPARATES NOTHING on the pair (it reads only the immediate frame, blind to a severed
frame deeper down).  Probe the WHOLE-stack predicate, not its head projection
([[ref-aggregate-collapses-structured-separates]]). -/

/-- A window's enclosure PATH: the stack of enclosing frame types, `true` = kept (seq), `false` =
    severed (box).  Mirrors the `btFold` typed-bracket stack. -/
abbrev Stack := List Bool

/-- The WEAK consumer-slot guard `h_seq_rec` is quantified over — a bracket-only fact (here "nonempty
    path") that says NOTHING about frame TYPES.  Holds on every window the slot must cover. -/
def consumerGuard (s : Stack) : Bool := !s.isEmpty

/-- `SeqEnclosed` — the gate's PATH-BLIND conjunct: the TOP frame is a seq.  A head PROJECTION of the
    whole-path routing tag. -/
def enclosedTop (s : Stack) : Bool := s.head? == some true

/-- `SeqPathAllSeq` — the navigator's ROUTING TAG: the WHOLE path is all-seq (no severed frame). -/
def pathAllSeq (s : Stack) : Bool := !s.isEmpty && s.all (· == true)

/-- All-seq window (mirrors `[[1,2],9]`'s inner seq window: stack `[true,true]`). -/
def allSeqWin : Stack := [true, true]
/-- Box-enclosed window (mirrors `[{a:[b]}]`'s inner seq window: stack `[true,false,true]` — the severed
    `box`/`{` frame sits between two seq frames; the TOP is still a seq). -/
def boxPathWin : Stack := [true, false, true]

/-- **NEGATIVE (R412) — the navigator's routing tag is NOT implied by the slot's weak guard.**  The
    box-path window is in the slot's domain (`consumerGuard`) AND passes the gate's path-blind
    `enclosedTop`, yet the routing tag `pathAllSeq` FAILS — so a navigator gated on `pathAllSeq` cannot
    inhabit this window the slot must cover.  This is exactly why `nestedSeq_recseqbody_of_locator`
    (carrying `SeqPathAllSeq`) cannot serve `h_seq_rec`. -/
theorem routingTag_not_implied_by_slot :
    ∃ s, consumerGuard s ∧ enclosedTop s ∧ ¬ (pathAllSeq s) :=
  ⟨boxPathWin, by decide, by decide, by decide⟩

/-- **POSITIVE (R412) — the discriminator is the WHOLE-path tag, not its top projection.**  On the
    minimal pair, the path-blind `enclosedTop` agrees (separates NOTHING), but `pathAllSeq` disagrees
    (separates the all-seq window from the box-path one). -/
theorem discriminator_is_whole_path :
    enclosedTop allSeqWin = enclosedTop boxPathWin ∧ pathAllSeq allSeqWin ≠ pathAllSeq boxPathWin :=
  ⟨by decide, by decide⟩

-- both windows pass the weak slot guard AND the path-blind gate conjunct …
#guard consumerGuard allSeqWin && consumerGuard boxPathWin
#guard enclosedTop allSeqWin && enclosedTop boxPathWin
-- … the navigator serves the all-seq window, but its routing tag FAILS on the box-path window:
#guard pathAllSeq allSeqWin
#guard pathAllSeq boxPathWin == false

end Tests.Reflections.ProducerStopsAtSeveredEdge
