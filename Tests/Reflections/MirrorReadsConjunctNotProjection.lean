/-!
# Reflection 464 — a flat→strengthened producer MIRROR is a pure TEXT-SWAP iff the flat proof reads
# each per-item fact from the predicate's STANDALONE CONJUNCT, not from a PROJECTION off the per-item
# inductive.  The minimal/severance-free strengthened family deliberately SHEDS the orthogonal
# projections (it carries only `.toFlat`), so wherever the flat proof wrote `hentry.toExtra` the mirror
# breaks — and must REROUTE to the predicate's standalone `Extra` conjunct (which the predicate keeps
# precisely because the strengthened family cannot reproject it).  So the mirror cost is QUANTIFIED
# BEFORE writing it: (text swaps) + (one reroute per `.toX`-projection read in the flat proof).

Self-contained (core Lean, no `L4YAML` import) toy executing STEP D step 8's seq-body brick and
PREDICTING the map-body brick's cost.  Context: the deep four-inductive family
(`[[ref-deep-family-mirrors-full-mutual-group]]`) is MINIMAL — it sheds the orthogonal
`WellBracketed`/`EntrySafe`/`EntryUnit` projections (`[[ref-parallel-family-sheds-orthogonal-field]]`),
carrying only the recursive body + `RecEntryDeep.toFlat`.  The deep body assemblers are verbatim
mirrors of the flat ones over the SAME induction (`[[ref-recursive-producer-mirrors-flat-over-shared-induction]]`),
swapping the per-item predicate and the leaf constructors.  But the mirror is *pure text-swap* only
where the flat proof read per-item facts the right way:

* The seq-body assembler reads `EntryUnit`/`ContentStartTok` from the predicate's STANDALONE conjuncts
  (`h_eu₁`, `h_cs₁`) — so its deep mirror is two global text swaps, ZERO reroutes (LANDED clean).
* The map-body assembler reads `h_ve.toEntryUnit` — a PROJECTION off the per-item `RecSeqEntry`.  Its
  deep mirror gives `h_ve : RecEntryDeep`, and `RecEntryDeep.toEntryUnit` DOES NOT EXIST (shed).  So the
  map mirror needs a reroute per such read — to the value predicate's standalone `EntryUnit` conjunct
  (`_h_eu_v`, currently bound-but-unused).  Cost predicted before writing: 4 swaps + exactly 2 reroutes.

This toy mirrors that exactly, scaled down:

* `FEntry` (flat, rich — STORES the non-emptiness witness `hne`) vs `DEntry` (deep, minimal — stores
  only the recursive body).  `DEntry.toF` projects deep⟹flat; the deep family carries NO `.toExtra`.
* `Extra` — the orthogonal fact (stand-in for `EntryUnit`).  `FEntry.toExtra` exists (the flat family
  stored its witness); there is deliberately NO `DEntry.toExtra`.
* `PFlat`/`PDeep` — per-item predicates carrying BOTH a STANDALONE `Extra out` conjunct AND the
  structural entry (mirror `EmitScansInFlowRecEntry{,Deep}`, which keep `EntryUnit` as a separate
  conjunct beside `RecSeqEntry`/`RecEntryDeep`).
* `clean_flat` / `clean_deep` — the CONJUNCT-reading assembler: identical proof, swap only the
  predicate.  Pure text-swap (the seq-body case).
* `proj_flat` — the PROJECTION-reading assembler (`he.toExtra`).  `naive_deep_swap_fails` witnesses
  that the text-swap `he.toExtra` with `he : DEntry _` does NOT elaborate (the shed projection).
* `proj_deep_rerouted` — the FIX: reroute the projection read to the standalone `Extra` conjunct.
* `mirror_cost_is_conjunct_vs_projection` — the finding in one proposition.

All sorry-free; the `#check_failure` is the negative witness that the build re-checks on every change.
-/

set_option autoImplicit false

namespace Tests.Reflections.MirrorReadsConjunctNotProjection

/-- Toy alphabet. -/
inductive Tok where
  | a | op | cl
deriving DecidableEq

/-- The FLAT, rich per-item family (mirror `RecSeqEntry`): the `wrap` constructor STORES the
    non-emptiness witness `hne` — so an orthogonal `Extra` fact can be PROJECTED back out of it. -/
inductive FEntry : List Tok → Prop where
  | leaf : FEntry [Tok.a]
  | wrap (interior : List Tok) (hne : interior ≠ []) : FEntry (Tok.op :: (interior ++ [Tok.cl]))

/-- The DEEP, MINIMAL per-item family (mirror `RecEntryDeep`): `wrap` stores ONLY the recursive body
    `h` — it SHEDS the orthogonal `hne` witness (`[[ref-parallel-family-sheds-orthogonal-field]]`).  So
    the only projection it offers is `.toF`; there is no `.toExtra`. -/
inductive DEntry : List Tok → Prop where
  | leaf : DEntry [Tok.a]
  | wrap (interior : List Tok) (h : DEntry interior) : DEntry (Tok.op :: (interior ++ [Tok.cl]))

/-- Every `DEntry` is non-empty — the witness the deep `wrap` did not store is RECONSTRUCTABLE, but
    only via this lemma; there is still no direct `.toExtra` projection on the inductive. -/
theorem DEntry.ne_nil : {l : List Tok} → DEntry l → l ≠ []
  | _, .leaf => by simp
  | _, .wrap _ _ => by simp

/-- The deep⟹flat projection (mirror `RecEntryDeep.toFlat`): re-materialise the shed `hne` via
    `DEntry.ne_nil`.  This is the ONLY projection the minimal deep family carries. -/
theorem DEntry.toF : {l : List Tok} → DEntry l → FEntry l
  | _, .leaf => FEntry.leaf
  | _, .wrap interior h => FEntry.wrap interior (DEntry.ne_nil h)

/-- The orthogonal fact a downstream consumer needs (stand-in for `EntryUnit`/`lastNonOpener`). -/
def Extra (l : List Tok) : Prop := l ≠ []

/-- The FLAT family CAN project `Extra` directly — it stored the witness.  (Mirror
    `RecSeqEntry.toEntryUnit`.) -/
theorem FEntry.toExtra : {l : List Tok} → FEntry l → Extra l
  | _, .leaf => by simp [Extra]
  | _, .wrap _ _ => by simp [Extra]

-- NOTE: there is deliberately NO `DEntry.toExtra`.  The minimal deep family sheds it; the only route
-- from a `DEntry` to `Extra` is `DEntry.toF` then `FEntry.toExtra` — which the assembler avoids by
-- reading the predicate's STANDALONE conjunct instead.

/-! ## The per-item producer predicates — each carries a STANDALONE `Extra out` conjunct BESIDE the
    structural entry (mirror `EmitScansInFlowRecEntry{,Deep}`: `… ∧ EntryUnit block ∧ RecSeqEntry block`
    vs `… ∧ EntryUnit block ∧ RecEntryDeep block`). -/

/-- Flat per-item deliverable: a block carrying the standalone `Extra` AND the flat structural entry. -/
def PFlat : Prop := ∃ out, Extra out ∧ FEntry out
/-- Deep per-item deliverable: the additive parallel — standalone `Extra` AND the deep structural entry. -/
def PDeep : Prop := ∃ out, Extra out ∧ DEntry out

/-! ## CASE 1 — the assembler reads `Extra` from the STANDALONE conjunct ⇒ the mirror is a pure
    text-swap (this is the seq-body assembler that LANDED clean this round). -/

/-- Flat assembler reading the standalone conjunct `hx`. -/
theorem clean_flat (h : PFlat) : ∃ out, Extra out := by
  obtain ⟨out, hx, _he⟩ := h
  exact ⟨out, hx⟩

/-- Deep mirror — character-for-character identical to `clean_flat` except the predicate name; the
    structural conjunct is never touched, so the swap is free. -/
theorem clean_deep (h : PDeep) : ∃ out, Extra out := by
  obtain ⟨out, hx, _he⟩ := h
  exact ⟨out, hx⟩

/-! ## CASE 2 — the assembler reads `Extra` via a PROJECTION off the entry ⇒ the naive text-swap
    BREAKS, because the deep family shed that projection; the fix is a REROUTE to the standalone
    conjunct (this is the map-body assembler's `h_ve.toEntryUnit`, the next brick). -/

/-- Flat assembler reading `Extra` via the projection `he.toExtra` (mirror `h_ve.toEntryUnit`). -/
theorem proj_flat (h : PFlat) : ∃ out, Extra out := by
  obtain ⟨out, _hx, he⟩ := h
  exact ⟨out, he.toExtra⟩

/-! **The negative witness.**  The naive text-swap of `proj_flat` — `he.toExtra` where `he : DEntry _`
    — does NOT elaborate: the minimal deep family carries no `.toExtra` projection.  `#check_failure`
    succeeds exactly when its term fails to elaborate, so a green build certifies the gap is real. -/
#check_failure (fun (he : DEntry [Tok.a]) => he.toExtra)

/-- **The reroute (the fix).**  Read `Extra` from the predicate's STANDALONE conjunct `hx` instead of
    projecting it off the entry.  This is why the strengthened predicate KEEPS the standalone `Extra`
    conjunct: it is the reroute target the deep family's shed projection forces. -/
theorem proj_deep_rerouted (h : PDeep) : ∃ out, Extra out := by
  obtain ⟨out, hx, _he⟩ := h
  exact ⟨out, hx⟩

/-- **The finding in one proposition.**  (1) when the flat proof reads a per-item fact from the
    STANDALONE conjunct, flat and deep assemblers have the SAME proof (`clean_flat`/`clean_deep`) — a
    pure text-swap; (2) when it reads via a PROJECTION off the entry, the deep mirror needs a reroute to
    the standalone conjunct (`proj_deep_rerouted`), because the minimal deep family shed the projection
    (the `#check_failure` above).  So the mirror's cost is QUANTIFIED before writing it: (text swaps) +
    (one reroute per `.toX`-projection read).  Sharpens
    `[[ref-recursive-producer-mirrors-flat-over-shared-induction]]` (when is the mirror truly verbatim)
    via `[[ref-parallel-family-sheds-orthogonal-field]]` (the shed projections are exactly the
    non-verbatim sites) and `[[ref-stored-vs-projected-severs-recursion-edge]]` (stored-vs-projected
    again decides the proof shape, here the read shape not the recursion edge). -/
theorem mirror_cost_is_conjunct_vs_projection :
    (PFlat → ∃ out, Extra out)        -- conjunct read, flat
    ∧ (PDeep → ∃ out, Extra out)      -- conjunct read, deep — SAME proof (pure swap)
    ∧ (PFlat → ∃ out, Extra out)      -- projection read, flat
    ∧ (PDeep → ∃ out, Extra out) :=   -- projection read, deep — REROUTED to the conjunct
  ⟨clean_flat, clean_deep, proj_flat, proj_deep_rerouted⟩

end Tests.Reflections.MirrorReadsConjunctNotProjection
