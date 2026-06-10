/-!
# Reflection 337 — de-risk a navigator's DOMAIN-RESTRICTION with a PRESERVATION/NEGATION pair

Self-contained (core Lean, no `L4YAML` import) toy model of the de-risk behind `SeqPathAllSeq`.

When a severed/projecting recursion edge bounds a navigator's reachable domain
([[ref-severed-edge-bounds-navigator-domain]]) and you RESTRICT the domain to fence it out, the
restriction is only sound if it is SELF-MAINTAINING across the edge the navigator keeps, and provably
ABANDONED across the edge it drops. Prove BOTH before assembling the fixpoint:

* **PRESERVATION** — the KEPT edge maps the domain into itself (so the kept recursion arm inherits the
  domain; it also pins WHICH existing head hypothesis discharges the restriction).
* **NEGATION** — the EXCLUDED edge maps the domain OUT of itself. This is the one that LICENSES
  DROPPING the excluded arm: without it, "we just won't recurse there" is an unproven gap.

The real predicate: `SeqPathAllSeq tokens lo` = the whole `btFold` typed-bracket stack after `[0, lo)`
is nonempty and all-`true` (every enclosing frame a flow SEQUENCE `[`, none a mapping `{`).
`seqPathAllSeq_descend`: a `.flowSequenceStart` head pushes `true` ⇒ PRESERVES.
`seqPathAllSeq_map_push_breaks`: a `.flowMappingStart` head pushes `false` ⇒ BREAKS.
`seqEnclosed_of_seqPathAllSeq`: the domain dominates the dispatch's TOP-only `SeqEnclosed`.
The toy below mirrors that with a list of typed frames and the two pushes.
-/

namespace Tests.Reflections.DomainRestrictionPreservationNegation

set_option autoImplicit false

/-- A typed frame: `true` = seq (`[`, the KEPT/navigable edge), `false` = map (`{`, the EXCLUDED
    severed edge).  Mirrors the `Bool` pushed by `btStep` (`[`→`true`, `{`→`false`). -/
abbrev Frame := Bool

/-- The path stack of enclosing frames, head = TOP (immediate enclosure).
    Mirrors `btFold (some []) (tokens.toList.take lo)`. -/
abbrev Stack := List Frame

/-- The navigator's DOMAIN-RESTRICTION: every frame is the navigable kind (`true`), nonempty.
    Mirrors `SeqPathAllSeq` — the whole stack read, not just the top.  `abbrev` so the witness
    `#guard`s below get `Decidable` for free. -/
abbrev InDomain (s : Stack) : Prop := s ≠ [] ∧ s.all (· == true) = true

/-- The KEPT recursion edge: a seq head pushes `true`.  Mirrors `btStep` on `.flowSequenceStart`. -/
def pushSeq (s : Stack) : Stack := true :: s

/-- The EXCLUDED recursion edge: a map head pushes `false`.  Mirrors `btStep` on `.flowMappingStart`. -/
def pushMap (s : Stack) : Stack := false :: s

/-! ## POSITIVE — PRESERVATION: the KEPT (seq) edge maps the domain into itself

Mirrors `seqPathAllSeq_descend`: the descended window inherits the domain, so the kept arm needs
nothing new — the seq head hypothesis is exactly what discharges the restriction. -/

theorem preservation (s : Stack) (h : InDomain s) : InDomain (pushSeq s) := by
  obtain ⟨_h_ne, h_all⟩ := h
  refine ⟨by simp [pushSeq], ?_⟩
  simp only [pushSeq, List.all_cons, h_all]; rfl

/-! ## NEGATIVE — NEGATION: the EXCLUDED (map) edge maps the domain OUT of itself

Mirrors `seqPathAllSeq_map_push_breaks`: a map head cannot even stay in-domain, so it is served by
the separate flat provider — this is what makes "no fifth (map-mirror) arm" a THEOREM, not a hope. -/

theorem negation (s : Stack) : ¬ InDomain (pushMap s) := by
  rintro ⟨_h_ne, h_all⟩
  simp [pushMap] at h_all

/-! ## DOMINANCE — the domain is STRICTLY STRONGER than the TOP-only enclosure fact

Mirrors `seqEnclosed_of_seqPathAllSeq`: the all-`true` stack has top `true`, supplying the per-window
dispatch's immediate-enclosure fact for free. -/

theorem dominance (s : Stack) (h : InDomain s) : s.head? = some true := by
  obtain ⟨h_ne, h_all⟩ := h
  cases s with
  | nil => exact absurd rfl h_ne
  | cons a t =>
    cases a with
    | false => simp at h_all
    | true => rfl

/-! ## Concrete witnesses — the de-risk on the real minimal pair's stacks

`[true, false, true]` is `[{a:[b]}]`'s map-path window `[7,8)` stack (buried map frame ⇒ NOT in
domain); `[true, true, true]` is `[[[1,2]]]`'s all-seq window `[4,7)` stack (⇒ in domain). -/

-- map-path window's stack: a buried `false` (map frame) ⇒ OUT of domain
#guard decide (¬ InDomain [true, false, true]) = true
-- all-seq window's stack: every frame a seq ⇒ IN domain
#guard decide (InDomain [true, true, true]) = true

/-- End-to-end: a seq push keeps an all-seq stack in domain; a map push drops it out. -/
example :
    InDomain (pushSeq [true, true]) ∧ ¬ InDomain (pushMap [true, true]) :=
  ⟨preservation [true, true] (by decide), negation [true, true]⟩

end Tests.Reflections.DomainRestrictionPreservationNegation
