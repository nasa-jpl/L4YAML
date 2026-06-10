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

end Tests.Reflections.ProducerStopsAtSeveredEdge
