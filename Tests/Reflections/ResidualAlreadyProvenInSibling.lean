/-!
# Reflection 358 — a sub-fact flagged as "the analytically-hard residual" may already be PROVEN inside a SIBLING lemma that derives it internally and CONSUMES it for a different deliverable; the residual is an EXTRACTION, not a derivation

Self-contained (core Lean, no `L4YAML` import) toy model of the move found while authoring the
emission-spine wrapper `nestedSeq_recseqentry_locate`.

A wrapper's LEAF arm needs a fact `F` (the real one: `h_b : b = off + e.length - 1`, the close-pin
coinciding the consumer's window close with the head entry's structural close). A multi-session
pointer flagged `F` as "the analytically-hard residual," deferring it as the last hard piece.

The reframe: before authoring `F` fresh, grep for a SIBLING lemma over the same substrate. A sibling
that produces a *different* deliverable may already derive `F` as an intermediate `have` and then
CONSUME it — discarding it from its signature. The real `recseqbody_head_seq_project` derives exactly
the close-uniqueness `h_uniq : j + 1 = lo + e.length` (a two-sided bracket match) and consumes it to
build the descended interior `RecSeqBody ((take j).drop (lo+1))`. The hard derivation was already
done — two screens up, inside a lemma whose stated output was something else.

The move: extract `F` as a standalone primitive — copy the sibling's prelude verbatim up to the
buried `have`, then RETURN it (in the consumer's required shape) instead of consuming it. The exposure
needs a DIFFERENT SHAPE than the internal use, so it is extract-AND-repackage, not a verbatim call.
Duplicating the prelude (rather than refactoring the sibling) is the low-risk choice under the IRON
RULE: a standalone new lemma cannot break the existing proof.

This toy mirrors the structure: a two-floor uniqueness `j + 1 = L` (omega from the floors, standing
in for the real trichotomy-plus-two-floors), a `sibling_consumer` that derives it internally as
`huniq` and CONSUMES it to produce a SUFFIX-shaped deliverable (`drop (j+1) = []`), and the EXTRACTED
`uniq_pin` that re-surfaces the SAME `j + 1 = L` in a PREFIX-length shape (`j = L - 1`) a second
consumer wants. The `#guard`s show the same uniqueness value serves both shapes; the negative is that
a verbatim call to `sibling_consumer` hands back the SUFFIX, from which the pin cannot be recovered.
-/

namespace Tests.Reflections.ResidualAlreadyProvenInSibling

set_option autoImplicit false

/-- The two "floors" that pin the close: the located floor forbids an earlier close (`j + 1 ≤ L`),
    the entry's own interior floor forbids a later one (`L ≤ j + 1`).  Stands in for the real
    `h_floor` (located, over `(lo, j]`) + `recseqentry_opener_interior_floor` (structural, inside the
    entry).  Together they squeeze the close to a unique position. -/
abbrev Floors (j L : Nat) : Prop := (j + 1 ≤ L) ∧ (L ≤ j + 1)

/-! ## The SIBLING — derives the uniqueness internally, then CONSUMES it for a different deliverable -/

/-- **The sibling lemma** — mirrors `recseqbody_head_seq_project`.  From the two floors it derives the
    close-uniqueness `huniq : j + 1 = L` (the real `h_uniq`), then CONSUMES it to produce a
    SUFFIX-shaped deliverable: the entry's token list `xs` (length `L`) has nothing past the located
    close (`xs.drop (j + 1) = []`, the analogue of the descended interior `(take j).drop (lo+1)`).
    Crucially `huniq` is INTERNAL — it does not appear in the signature, so a downstream consumer that
    needs it must either re-derive it or extract it. -/
theorem sibling_consumer (j L : Nat) (h : Floors j L)
    (xs : List Nat) (h_len : xs.length = L) :
    xs.drop (j + 1) = [] := by
  obtain ⟨h1, h2⟩ := h
  have huniq : j + 1 = L := by omega          -- the buried intermediate, the real `h_uniq`
  rw [huniq, ← h_len, List.drop_length]        -- CONSUMED to build the SUFFIX deliverable

/-! ## The EXTRACTION — re-surface the same buried `have`, repackaged for the leaf consumer -/

/-- **The extracted primitive** — `recseqentry_close_pin`'s toy analogue.  Reuses the sibling's
    derivation (here the same `omega` on the floors) but RETURNS the uniqueness `j + 1 = L` instead of
    consuming it.  This is the `h_b` pin the leaf brick needs (`b = off + L - 1` from `j + 1 = L`). -/
theorem uniq_pin (j L : Nat) (h : Floors j L) : j + 1 = L := by
  obtain ⟨h1, h2⟩ := h; omega

/-- **The second consumer** — the leaf arm — wants the pin in a PREFIX-length SHAPE (`j = L - 1`),
    DIFFERENT from the sibling's suffix deliverable.  Trivial from `uniq_pin`; impossible from
    `sibling_consumer`'s suffix fact alone (a `drop = []` says nothing about `j`'s value). -/
theorem second_consumer (j L : Nat) (hL : 1 ≤ L) (h : Floors j L) : j = L - 1 := by
  have hpin := uniq_pin j L h; omega

/-! ## The same buried value serves both shapes; the sibling's deliverable is the SUFFIX, not the pin

The extraction is sound precisely because the sibling already computes `j + 1 = L`; the only work is
re-exposing it in the leaf's shape.  A verbatim call to the sibling gives the SUFFIX (`drop`), from
which the pin cannot be recovered — so it is extract-AND-repackage, not reuse. -/

-- the floors pin the close to `j = 2` when `L = 3` (so `j + 1 = L`)...
#guard decide (Floors 2 3)
#guard decide (¬ Floors 1 3)                 -- an earlier close violates the located floor
#guard decide (¬ Floors 3 3)                 -- a later close violates the interior floor
-- ...the SIBLING's deliverable is the suffix being empty at that close:
#guard (([10, 20, 30] : List Nat).drop (2 + 1)) == []
-- ...whereas a NON-close index leaves a nonempty suffix (the suffix shape is blind to which index):
#guard (([10, 20, 30] : List Nat).drop (1 + 1)) != []
-- ...and the EXTRACTED pin reads off the close index directly: `j = L - 1 = 2`.
#guard decide (2 = 3 - 1)

/-! ## Concrete witnesses -/

-- the extracted pin applies, giving the close-uniqueness directly:
example : (2 : Nat) + 1 = 3 := uniq_pin 2 3 ⟨by decide, by decide⟩
-- the leaf consumer reads it in the prefix-length shape:
example : (2 : Nat) = 3 - 1 := second_consumer 2 3 (by decide) ⟨by decide, by decide⟩
-- the sibling delivers the SUFFIX, not the pin:
example : ([10, 20, 30] : List Nat).drop (2 + 1) = [] :=
  sibling_consumer 2 3 ⟨by decide, by decide⟩ [10, 20, 30] (by decide)

end Tests.Reflections.ResidualAlreadyProvenInSibling
