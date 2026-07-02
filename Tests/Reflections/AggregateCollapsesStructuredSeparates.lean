/-!
# Reflection 336 — the dispatch is the un-aggregated STRUCTURED STATE, not a numeric aggregate of it

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind the
`SeqPathDispatchProbe`: after a [[ref-severed-edge-bounds-navigator-domain]] de-risk refutes a
navigator's totality, the DISPATCH that re-partitions the path-blind gate's windows into NAVIGABLE
vs UNREACHABLE is found by probing a numeric AGGREGATE against the un-aggregated STRUCTURED STATE it
was folded from, over a minimal pair.

A path's navigability depends on the TYPE of every frame from the root to the window. A numeric
aggregate (the stack's depth/size — the `flowBracketBalance` analogue) sums the per-frame types away,
so a map-path and an all-seq path of the SAME depth COLLAPSE to one value (REJECTED — and the
collapse IS the necessity leg). The structured state (the typed stack itself — the `btFold` stack
analogue) retains the types, so the "all frames are the navigable kind" predicate SEPARATES them.

The real types: `flowBracketBalance tokens 2 a` is the depth aggregate (`2` for BOTH `[{a:[b]}]`'s
map-path window and `[[[1,2]]]`'s all-seq window); `pathAllSeq` reads the whole `btFold` stack
(`[true,false,true]` vs `[true,true,true]`). The toy below mirrors that with a list of typed frames.
-/

namespace Tests.Reflections.AggregateCollapsesStructuredSeparates

set_option autoImplicit false

/-- A typed bracket frame: `true` = seq (`[`, navigable), `false` = map (`{`, severs navigation).
    Mirrors the `Bool` pushed by `btStep` (`[`→`true`, `{`→`false`). -/
abbrev Frame := Bool

/-- The structured state at a window's opener: the full stack of enclosing frames, head = top.
    Mirrors `btFold (some []) (tokens.toList.take a)`. -/
abbrev Stack := List Frame

/-- The MAP-PATH window's stack (`[{a:[b]}]` window `[7,8)`): immediate seq frame, but a map frame
    buried below it.  Top is `true` (gate-passing — path-blind), yet the path is NOT all-seq. -/
def mapPathStack : Stack := [true, false, true]

/-- The ALL-SEQ window's stack (`[[[1,2]]]` window `[4,7)`): every frame is a seq. -/
def allSeqStack : Stack := [true, true, true]

/-- The numeric AGGREGATE — the stack DEPTH (its length).  Mirrors the root-base balance: it sums
    the per-frame TYPES away, keeping only the count. -/
def depth (s : Stack) : Nat := s.length

/-- The gate's IMMEDIATE-enclosure conjunct — the stack TOP only (path-blind).  Mirrors
    `enclosingMark`/`btFold`-top: it reads ONE frame of the structured state. -/
def topFrame (s : Stack) : Option Frame := s.head?

/-- The DISPATCH predicate — the structured state read WHOLE: every frame is navigable (`true`).
    Mirrors `pathAllSeq`.  The gate's `topFrame` is a PROJECTION of this. -/
def pathAllSeq (s : Stack) : Bool := s.all (· == true)

/-! ## The gate is path-blind — both windows pass the IMMEDIATE-enclosure check identically -/

#guard topFrame mapPathStack = some true     -- map-path window: gate passes (top is seq)…
#guard topFrame allSeqStack = some true      -- all-seq window: gate passes too — indistinguishable

/-! ## NEGATIVE — the numeric AGGREGATE collapses the pair to one value (REJECTED)

The depth aggregate is `3` for BOTH stacks: it discarded the per-frame types, so it cannot tell the
map-path window from the all-seq one.  This collapse IS the necessity leg of the minimal pair. -/

#guard depth mapPathStack = 3
#guard depth allSeqStack = 3
#guard depth mapPathStack = depth allSeqStack          -- COLLAPSES — cannot separate

/-- The aggregate provably cannot separate: equal depths, distinct navigability. -/
theorem aggregate_collapses :
    depth mapPathStack = depth allSeqStack ∧ pathAllSeq mapPathStack ≠ pathAllSeq allSeqStack :=
  ⟨rfl, by decide⟩

/-! ## POSITIVE — the un-aggregated STRUCTURED STATE separates the pair (the dispatch)

`pathAllSeq` reads the whole stack: the buried `false` (map frame) in the map-path stack makes it
`false`, while the all-seq stack is `true`.  The differing frame IS the discriminator, read off the
existing fold's state — not invented. -/

#guard pathAllSeq mapPathStack = false       -- buried map frame ⇒ NOT navigable (→ flat provider)
#guard pathAllSeq allSeqStack = true         -- all seq frames  ⇒ navigable     (→ the navigator)
#guard !(pathAllSeq mapPathStack == pathAllSeq allSeqStack)   -- SEPARATES

/-- End-to-end on the minimal pair: same depth + same gate-top, but the structured-state predicate
    separates them.  The aggregate is the necessity leg; the structured state is the dispatch. -/
example :
    depth mapPathStack = depth allSeqStack
    ∧ topFrame mapPathStack = topFrame allSeqStack
    ∧ pathAllSeq mapPathStack ≠ pathAllSeq allSeqStack :=
  ⟨rfl, rfl, by decide⟩

end Tests.Reflections.AggregateCollapsesStructuredSeparates
