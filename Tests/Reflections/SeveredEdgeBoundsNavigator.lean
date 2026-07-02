/-!
# Reflection 335 — a SEVERED recursion edge bounds a navigator's domain; a PATH-blind gate admits windows past it

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind the
`SeqMapPathNestedProbe` de-risk that REFUTED `rec_seq_body_nested_project`'s totality.

A producer that NAVIGATES a recursive deliverable (descends its STORED edges from a root to a
located window) can only reach windows whose PATH lies within the type's stored edges. A
constructor member that PROJECTS rather than STORES the recursive sub-deliverable SEVERS the
navigation there. Meanwhile the consumer's GATE can be PATH-BLIND — it pins only the window's
IMMEDIATE feature, not the path from the root — so it admits windows behind the severed edge.

The real types: `RecSeqBody` with `RecSeqEntry.seq` STORING `h_rec : RecSeqBody interior` (a stored
edge) and `RecSeqEntry.map` PROJECTING to `h_wb : WellBracketed interior` only (NO `RecSeqBody` —
the severed edge). On `[{a:[b]}]` the inner seq window `[7,8)` passes the immediate-enclosure gate
(`SeqTypedInterior`) yet is buried in a `.map`'s `WellBracketed`, so `rec_seq_body_nested_project`'s
`RecSeqBody`-navigation cannot reach it.

The toy below mirrors that: `Body.seq` stores the inner `Body`; `Body.map` projects to a weaker
`Flat`. The navigator `bodyInner?` reaches through `.seq` but DIES at `.map` — even when the `.map`
interior is gate-passing. The fix is a FLAT provider serving that target from the `Flat` substrate.
-/

namespace Tests.Reflections.SeveredEdgeBoundsNavigator

set_option autoImplicit false

/-- The weaker substrate (the `WellBracketed` analogue): a plain wrapper tree with no link back to
    the recursive deliverable.  A `.wrap` is "seq-shaped at its head" (the gate-passing shape). -/
inductive Flat
  | leaf
  | wrap (inner : Flat)
  deriving DecidableEq, Repr

/-- The recursive deliverable (the `RecSeqBody`/`RecSeqEntry` analogue).
    * `seq` STORES the recursive inner `Body` — a navigable edge (mirrors `RecSeqEntry.seq.h_rec`);
    * `map` PROJECTS to the weaker `Flat` only — the SEVERED edge (mirrors `RecSeqEntry.map.h_wb`,
      which carries `WellBracketed`, not `RecSeqBody`). -/
inductive Body
  | leaf
  | seq (inner : Body)
  | map (interior : Flat)
  deriving DecidableEq, Repr

/-- The NAVIGATOR — extract the located sub-deliverable by reading the STORED edge
    (mirrors `recseqentry_seq_extract` reading the `.seq` constructor's `h_rec`). -/
def bodyInner? : Body → Option Body
  | .seq inner => some inner
  | .leaf      => none
  | .map _     => none          -- severed: a `.map` stores no `Body`, only a `Flat`

/-- The PATH-BLIND GATE on the weaker substrate — "the immediate shape is a seq wrapper"
    (mirrors `SeqTypedInterior`'s `SeqEnclosed` conjunct: it sees only the IMMEDIATE enclosing
    bracket, NOT whether the path from the root crossed a map). -/
def flatIsSeqHead : Flat → Bool
  | .wrap _ => true
  | .leaf   => false

/-! ## NEGATIVE — the navigator dies at the severed edge even on a GATE-PASSING interior

A `.map (.wrap .leaf)` has a gate-passing `Flat` interior (`flatIsSeqHead (.wrap .leaf) = true`),
so the consumer's gate admits the window inside it — yet `bodyInner?` returns `none`: there is no
stored `Body` to navigate to.  This is the map-PATH-nested seq window the `RecSeqBody`-navigator
cannot serve.  Contrast a `.seq` node, whose stored inner IS extractable. -/

-- the interior is gate-passing (the window inside it is in the consumer's domain)…
#guard flatIsSeqHead (.wrap .leaf) = true
-- …yet the navigator cannot reach a `Body` behind the SEVERED `.map` edge.
#guard bodyInner? (.map (.wrap .leaf)) = none
-- contrast: a STORED `.seq` edge IS navigable.
#guard bodyInner? (.seq (.seq .leaf)) = some (.seq .leaf)

/-- The severed edge is intrinsic to the constructor, not the interior: NO `Flat` makes a `.map`
    navigable (mirrors `recseqentry_seq_extract` ruling out the `.map` constructor structurally —
    a `.flowMappingStart` head has no `h_rec`). -/
theorem map_never_navigable (f : Flat) : bodyInner? (.map f) = none := rfl

/-- And a `.seq` always exposes its stored inner — the navigable edge. -/
theorem seq_always_navigable (b : Body) : bodyInner? (.seq b) = some b := rfl

/-! ## POSITIVE — the fix: serve the severed-edge window from the WEAKER substrate (proven)

Don't strengthen the navigator (force `.map` to carry a `Body`).  RESTRICT it to navigable
(all-`.seq`-path) targets, and serve the severed-edge windows from the `Flat` they DO have: a
gate-passing `Flat` yields its inner directly, no recursion through `Body`.  (Mirrors the flat
map-path provider scanning a seq body's `SafeBodyUnit` straight off emission.) -/

def flatProvider : (f : Flat) → flatIsSeqHead f = true → Flat
  | .wrap inner, _ => inner
  | .leaf,       h => by simp [flatIsSeqHead] at h

/-- The flat provider serves exactly the gate-passing target the navigator could not reach. -/
theorem flatProvider_wrap (inner : Flat) :
    flatProvider (.wrap inner) rfl = inner := rfl

/-- End-to-end on the witness `.map (.wrap .leaf)`: the navigator yields `none`, but the gate holds
    and the flat provider delivers — the two providers PARTITION the domain by path. -/
example :
    bodyInner? (.map (.wrap .leaf)) = none
    ∧ flatIsSeqHead (.wrap .leaf) = true
    ∧ flatProvider (.wrap .leaf) rfl = .leaf :=
  ⟨rfl, rfl, rfl⟩

end Tests.Reflections.SeveredEdgeBoundsNavigator
