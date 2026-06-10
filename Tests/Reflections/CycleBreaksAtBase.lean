/-!
# Reflection 342 — a co-construction cycle breaks at its BASE; the root seed is the landed edge fed the FLAT producer

Self-contained (core Lean, no `L4YAML` import) toy model of the move behind `seqRoot_flowBodyContent`.

A recursion needs a per-window fact `Content` that a cheap guard cannot project.  `Content` is classically
obtained from a `Carrier` — but the `Carrier` is produced FROM the recursion's own output (`Resolved`),
which itself needs `Content`.  So reading `Content` off the `Carrier` is **circular**: the
co-construction tension.

The move (R342): inventory the recursion's EDGES first.

* `descend_edge` — the genuinely-recursive edge: it assembles the child `Content` from the child's OWN
  substrate, drawn from the IH (`Substrate s (lo+1)`), NOT by re-basing a parent fact.  So it has already
  resolved the obstruction the carrier was masking.
* `advance_edge` — the pure re-basing edge, no IH.

Both edges are landed (here: trivial, but the analogy is structural).  So the carrier dependency survives
ONLY at the ROOT window — and the root seed is NOT a fresh derivation: it is `descend_edge`'s OWN
assembler chain (`content_of_substrate`) with the IH-sourced substrate swapped for the FLAT producer's
output (`flat_root_substrate`).  `root_content` IS `content_of_substrate s 0 (flat_root_substrate s)` —
the descend edge fed the flat ingredient.  With it, `content_all` threads `Content` at every window
carrier-free (seed at the root, propagate by the edge), never touching `Carrier`.

The NEGATIVE (`root_content_via_carrier_stuck` + `carrier_from_recursion`): sourcing the root `Content`
from the `Carrier` only DEFERS the obligation — the carrier is built from the recursion (`Resolved`),
which needs `Content` at every window INCLUDING the root, so the route is circular and must take
`Carrier` as an undischarged hypothesis.  `root_content` breaks the cycle precisely because the FLAT
producer needs no recursion.
-/

namespace Tests.Reflections.CycleBreaksAtBase

set_option autoImplicit false

/-- A toy token stream. -/
abbrev Stream := List Nat

/-- The per-window SUBSTRATE (toy `SafeBodyUnit`): the window starting at `lo` is in bounds. -/
def Substrate (s : Stream) (lo : Nat) : Prop := lo ≤ s.length

/-- The per-window FACT the recursion needs (toy `FlowBodyContent`) — assembled from the substrate,
    not projectable from a cheaper guard. -/
def Content (s : Stream) (lo : Nat) : Prop := Substrate s lo

/-- The toy recursion's OUTPUT (toy `RecSeqBody`): a window is "resolved".  Needs `Content`. -/
def Resolved (s : Stream) (lo : Nat) : Prop := Content s lo

/-- The CARRIER (toy `SeqInteriorSeparators` at the root span): if you have it, it gives `Content` at
    every in-bounds window — but it is produced FROM the recursion, so reading `Content` off it is
    circular. -/
def Carrier (s : Stream) : Prop := ∀ lo, lo ≤ s.length → Content s lo

/-! ## The shared assembler and the two recursion edges (landed) -/

/-- **The ASSEMBLER** (toy `flowBodyContent_of_deep`): a substrate assembles a `Content`. -/
theorem content_of_substrate (s : Stream) (lo : Nat) (h : Substrate s lo) : Content s lo := h

/-- **The DESCEND edge** (toy `flowBodyContent_descend`): the genuinely-recursive edge.  It assembles the
    child `Content` from the child's OWN substrate `Substrate s (lo+1)` — drawn from the IH, NOT by
    re-basing a parent fact.  It is `content_of_substrate` fed the IH substrate. -/
theorem descend_edge (s : Stream) (lo : Nat) (h_ih_substrate : Substrate s (lo + 1)) :
    Content s (lo + 1) :=
  content_of_substrate s (lo + 1) h_ih_substrate

/-- **The ADVANCE edge** (toy `flowBodyContent_advance`): a pure re-base, no IH. -/
theorem advance_edge (s : Stream) (lo m : Nat) (_h : Content s lo) (h_m : m ≤ s.length) :
    Content s m :=
  h_m

/-! ## The FLAT producer and the carrier-free ROOT SEED -/

/-- **The FLAT producer** (toy `seqRoot_safeBodyUnit`): the root substrate, off "emission", no recursion. -/
theorem flat_root_substrate (s : Stream) : Substrate s 0 := Nat.zero_le _

/-- **THE ROOT SEED — carrier-free** (toy `seqRoot_flowBodyContent`).  It is `descend_edge`'s OWN
    assembler chain (`content_of_substrate`) with the IH-sourced substrate swapped for the FLAT producer's
    output (`flat_root_substrate`).  No `Carrier`, no recursion. -/
theorem root_content (s : Stream) : Content s 0 :=
  content_of_substrate s 0 (flat_root_substrate s)

/-! ## POSITIVE — thread `Content` at every window carrier-free (root seed + edge)

The producer needs no `Carrier`: seed at the root by `root_content`, propagate by `advance_edge`. -/

theorem content_all (s : Stream) : ∀ lo, lo ≤ s.length → Content s lo := by
  intro lo h
  exact advance_edge s 0 lo (root_content s) h

example : Content [10, 20, 30] 2 := content_all [10, 20, 30] 2 (by decide)

#guard (decide ((2 : Nat) ≤ [10, 20, 30].length))   -- the window `[2, ·)` is in bounds
#guard (decide ((0 : Nat) ≤ [10, 20, 30].length))   -- the root seed's bound
#guard ([10, 20, 30].length == 3)

/-! ## NEGATIVE — the carrier route is circular at the base, broken only by the FLAT root seed

`carrier_from_recursion` builds the `Carrier` FROM the recursion (`Resolved`), which needs `Content` at
EVERY window including the root — so a `root_content_via_carrier` would need a `Carrier` it cannot
produce without already having `Content s 0`.  The route can only DEFER: it must take `Carrier` as an
undischarged hypothesis.  `root_content` (FLAT) is what severs the cycle. -/

/-- The recursion step (toy producer body): `Content` ⇒ `Resolved`. -/
theorem resolved_of_content (s : Stream) (lo : Nat) (h : Content s lo) : Resolved s lo := h

/-- Building the `Carrier` funnels THROUGH the recursion's output, which needs `Content` everywhere —
    INCLUDING the root.  This is the cycle: `Carrier` ⟵ `Resolved` ⟵ `Content s 0`. -/
theorem carrier_from_recursion (s : Stream)
    (h_content_all : ∀ lo, lo ≤ s.length → Content s lo) : Carrier s :=
  fun lo h => resolved_of_content s lo (h_content_all lo h)

/-- The carrier route is STUCK at the base: it can only deliver the root `Content` by ASSUMING a
    `Carrier` (the undischarged debt), since producing the `Carrier` from the recursion would already
    require `Content s 0`.  Contrast `root_content`, which discharges from the FLAT producer. -/
theorem root_content_via_carrier_stuck (s : Stream) (h_carrier : Carrier s) : Content s 0 :=
  h_carrier 0 (Nat.zero_le _)

end Tests.Reflections.CycleBreaksAtBase
