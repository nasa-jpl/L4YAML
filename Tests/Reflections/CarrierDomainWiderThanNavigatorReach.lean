/-!
# Reflection 448 — a UNIVERSAL producer over a domain predicate D cannot be completed by a NAVIGATOR
# whose reachable domain is a STRICT SUBSET of D.  The gap is forced by a SEVERED recursive edge: the
# navigator walks a recursive structure that, at a FOREIGN-type constructor, stores only a FLAT witness
# (not the recursive one), so it cannot descend into foreign-nested elements of D.  Those elements live
# behind a SIBLING recursive structure (whose value field re-enters the original), reachable only by a
# SIBLING navigator — so the sibling navigator is on the producer's CRITICAL PATH, not a downstream
# concern.

Self-contained (core Lean, no `L4YAML` import) toy of the R448 finding — STEP D: trying to discharge the
seq root carrier revealed it is NOT seq-side-completable.

Context.  The seq ROOT CARRIER `SeqInteriorSeparators tokens 2 (size-2)` is a UNIVERSAL over a domain
predicate (`SeqInteriorSeparators.lean:96`):

    ∀ a b, lo ≤ a → a ≤ b → b ≤ hi → SeqTypedInterior tokens a b → bodySuccFact ∧ noTrailingSepFact

The domain `SeqTypedInterior tokens a b` requires the TOP bracket frame to be `[` — a path-BLIND
condition that admits a seq reached through a MAP (`[{a:[b]}]`'s `[b]`).  The R447 plan sourced each
window's `h_safe : SafeBodyUnit` from the all-seq locator `nestedSeq_safeBodyUnit_of_locator`, gated by
`SeqPathAllSeq tokens (a-1)` — the WHOLE ancestor path `[`.  So the carrier's domain (`SeqTypedInterior`,
top frame) is STRICTLY WIDER than the locator's reach (`SeqPathAllSeq`, whole path);
`SeqCarrierMapNestedDomainProbe` `#guard`s the gap on `[{a:[b]}]`.

Why the gap is structural, not patchable.  The all-seq locator walks the root `RecSeqBody` spine via
`RecSeqEntry.seq`'s stored `h_rec : RecSeqBody interior`.  But `RecSeqEntry.map` stores only
`h_wb : WellBracketed interior` (NonemptyStructure.lean ~500) — the RECURSIVE witness is SEVERED at the
map.  So the seq spine cannot descend into a map's values; a map-nested seq's `RecSeqBody` is unreachable
from the seq side.  It lives behind the SIBLING structure `RecMapBody`/`RecMapPair`, whose value field
re-enters `RecSeqEntry` — reachable only by a MAP-PATH locator (the map mirror).

Conclusion.  The seq root carrier's `h_safe` source splits THREE ways by path: root (flat
`seqRoot_safeBodyUnit`), all-seq-path nested (`nestedSeq_safeBodyUnit_of_locator`, R447), and MAP-path
nested (the deferred map mirror).  R447's 2-way dispatch `seqWindow_safeBodyUnit` is necessary but
INSUFFICIENT.  The map mirror is on the seq root carrier's CRITICAL PATH — deeper than the
`FlowSubrangesOk`-level entanglement (seq half vs map half) the blueprint previously noted.

The reusable rule.  When a UNIVERSAL producer's domain predicate D is WEAKER than a reused navigator's
reachable-domain gate, the elements of D the navigator misses are NOT an edge case to patch — they are a
structurally-severed sub-domain.  Find the severance at the navigator's recursive structure: does its
foreign-type constructor store the RECURSIVE witness or only a FLAT one?  If flat, the foreign-nested
elements require the SIBLING navigator (over the structure that re-enters at its value field), which is on
the producer's critical path.

This toy has two parts:

* PART 1 (the domain/reach gap): `Stack = List Bool` (`true` = seq frame, `false` = map frame),
  `inDomain` = top frame `[` (path-blind, the carrier domain), `reach` = whole path `[` and nonempty
  (the locator reach).  `reach_imp_inDomain` (reach ⊆ domain), `minimal_pair_domain_wider`
  (`[true, false]` is in the domain but not reachable — a map-nested seq).
* PART 2 (the severance): `RecSeq` stores a RECURSIVE child at `.seqChild` but only a FLAT bit at
  `.mapChild`; `descendSeq` returns the child for `.seqChild` and `none` for `.mapChild` (the seq spine
  dead-ends at a map).  The sibling `RecMap.pair` carries a `RecSeq` value — so a foreign-nested `RecSeq`
  IS reachable through `RecMap`, not `RecSeq`.

All sorry-free, axiom-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.CarrierDomainWiderThanNavigatorReach

/-! ## PART 1 — the carrier's domain is strictly wider than the navigator's reach. -/

/-- A typed bracket stack: `true` = seq frame `[`, `false` = map frame `{`; TOP at the HEAD. -/
abbrev Stack := List Bool

/-- The carrier's DOMAIN predicate — `SeqTypedInterior`'s top-frame condition: the immediate enclosing
    frame is `[`.  Path-BLIND (reads only the head). -/
def inDomain (s : Stack) : Prop := s.head? = some true

/-- The all-seq locator's REACH — `SeqPathAllSeq`: the whole ancestor path is `[` and nonempty. -/
def reach (s : Stack) : Prop := s ≠ [] ∧ s.all (· == true) = true

/-- **The navigator reaches a SUBSET of the domain.**  Whole-path-`[` ⇒ top-`[`. -/
theorem reach_imp_inDomain {s : Stack} (h : reach s) : inDomain s := by
  obtain ⟨hne, hall⟩ := h
  cases s with
  | nil => exact absurd rfl hne
  | cons b rest =>
    simp only [List.all_cons, Bool.and_eq_true, beq_iff_eq] at hall
    simp only [inDomain, List.head?_cons, hall.1]

/-- **The domain is STRICTLY wider.**  `[true, false]` — a seq reached through a map (`[{a:[b]}]`'s `[b]`):
    top frame `[` (IN the carrier domain, separator facts owed) but the map's `false` deeper means the
    whole path is not all-`[` (NOT reachable by the all-seq locator). -/
theorem minimal_pair_domain_wider :
    inDomain [true, false] ∧ ¬ reach [true, false] := by
  refine ⟨rfl, ?_⟩
  rintro ⟨_, hall⟩
  simp at hall

/-! ## PART 2 — the gap is forced by a SEVERED recursive edge, reachable only by the sibling structure. -/

/-- An opaque flat witness (models `WellBracketed interior`): carries NO recursive structure. -/
opaque Flat : Type

/-- The seq spine the navigator walks (models `RecSeqEntry`/`RecSeqBody`).  `.seqChild` stores the
    RECURSIVE child; `.mapChild` stores only a FLAT witness — the recursive edge is SEVERED there. -/
inductive RecSeq where
  | leaf
  | seqChild (child : RecSeq)
  | mapChild (flat : Flat)

/-- The seq navigator's single descend step: into `.seqChild`'s recursive child, but STUCK (`none`) at
    `.mapChild` — the spine cannot enter a map's contents. -/
def descendSeq : RecSeq → Option RecSeq
  | .leaf        => none
  | .seqChild c  => some c
  | .mapChild _  => none

/-- The sibling structure (models `RecMapBody`/`RecMapPair`): its value field RE-ENTERS `RecSeq`. -/
inductive RecMap where
  | leaf
  | pair (value : RecSeq)

/-- The sibling navigator's descend: into the pair's value, which IS a `RecSeq` — so a foreign-nested
    `RecSeq` is reachable HERE, where the seq spine dead-ended. -/
def descendMap : RecMap → Option RecSeq
  | .leaf      => none
  | .pair v    => some v

/-- **The severance.**  The seq navigator dead-ends at a map (`descendSeq (.mapChild w) = none`), so a
    `RecSeq` value nested behind a map is UNREACHABLE from the seq spine — but reachable through the
    sibling `RecMap.pair` (`descendMap (.pair v) = some v`).  The sibling navigator is on the critical
    path: only it recovers the foreign-nested structure. -/
theorem severed_edge_needs_sibling (w : Flat) (v : RecSeq) :
    descendSeq (.mapChild w) = none ∧ descendMap (.pair v) = some v :=
  ⟨rfl, rfl⟩

/-- The finding in one proposition: the navigator's reach is a strict subset of the producer's domain
    (PART 1), and the missed elements are behind a severed seq edge, recoverable only by the sibling
    navigator (PART 2). -/
theorem r448_finding (w : Flat) (v : RecSeq) :
    (∀ s : Stack, reach s → inDomain s)                 -- reach ⊆ domain
    ∧ (inDomain [true, false] ∧ ¬ reach [true, false])  -- domain strictly wider (map-nested seq)
    ∧ (descendSeq (.mapChild w) = none)                 -- seq spine SEVERED at the map
    ∧ (descendMap (.pair v) = some v) :=                -- sibling recovers the foreign-nested RecSeq
  ⟨fun _ => reach_imp_inDomain,
   minimal_pair_domain_wider,
   rfl, rfl⟩

end Tests.Reflections.CarrierDomainWiderThanNavigatorReach
