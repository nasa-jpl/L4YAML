/-!
# Reflection 464 — a flat→strengthened producer MIRROR is a pure TEXT-SWAP iff the flat proof reads
# each per-item fact from the predicate's STANDALONE CONJUNCT, not from a PROJECTION off the per-item
# inductive.  The minimal/severance-free strengthened family deliberately SHEDS the orthogonal
# projections (it carries only `.toFlat`), so wherever the flat proof wrote `hentry.toExtra` the mirror
# breaks — and must REROUTE to the predicate's standalone `Extra` conjunct (which the predicate keeps
# precisely because the strengthened family cannot reproject it).  So the mirror cost is QUANTIFIED
# BEFORE writing it: (text swaps) + (one reroute per `.toX`-projection read in the flat proof).

Self-contained (core Lean, no `L4YAML` import) toy modelling STEP D step 8's seq-body AND map-body
bricks — the map-body brick's pre-write cost prediction (4 swaps + 2 reroutes) now REALIZED off-by-zero
(R465).  Context: the deep four-inductive family
(`[[ref-deep-family-mirrors-full-mutual-group]]`) is MINIMAL — it sheds the orthogonal
`WellBracketed`/`EntrySafe`/`EntryUnit` projections (`[[ref-parallel-family-sheds-orthogonal-field]]`),
carrying only the recursive body + `RecEntryDeep.toFlat`.  The deep body assemblers are verbatim
mirrors of the flat ones over the SAME induction (`[[ref-recursive-producer-mirrors-flat-over-shared-induction]]`),
swapping the per-item predicate and the leaf constructors.  But the mirror is *pure text-swap* only
where the flat proof read per-item facts the right way:

* The seq-body assembler reads `EntryUnit`/`ContentStartTok` from the predicate's STANDALONE conjuncts
  (`h_eu₁`, `h_cs₁`) — so its deep mirror is two global text swaps, ZERO reroutes (R464, LANDED clean).
* The map-body assembler reads `h_ve.toEntryUnit` — a PROJECTION off the per-item `RecSeqEntry`.  Its
  deep mirror gives `h_ve : RecEntryDeep`, and `RecEntryDeep.toEntryUnit` DOES NOT EXIST (shed).  So the
  map mirror needs a reroute per such read — to the value predicate's standalone `EntryUnit` conjunct
  (`_h_eu_v`, bound-but-unused).  Cost predicted before writing: 4 swaps + exactly 2 reroutes.  **R465:
  REALIZED off-by-zero** — `emitPairList_scans_recmapbodyDeep` LANDED with exactly those 4 swaps + 2
  reroutes, no new helper, axioms identical to the flat producer; pre-write quantification was exact.

COROLLARY (composite items).  A map item is a `key ++ value` PAIR; the deep mirror's reroutes landed
ONLY on the value side, not the key side.  Reason: the consumer projects only BOUNDARY facts
(last-token-not-opener-or-sep), and the pair's boundary IS the value tail — so the END-most sub-block
carries every projection read.  Predicting a composite mirror's cost, grep the end-most sub-structure
first.  Illustrated below by `pair_clean_key` (key side, pure swap) vs `pair_proj_value_rerouted`
(value side, the lone reroute).

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
* `proj_flat` — the PROJECTION-reading assembler (`he.toExtra`).  Its naive text-swap `he.toExtra`
  with `he : DEntry _` does NOT elaborate: the minimal deep family shed `.toExtra` (evident from the
  two-constructor `DEntry` definition below, which declares only `.toF`).
* `proj_deep_rerouted` — FIX 1: reroute the projection read to the standalone `Extra` conjunct (the
  map-body brick, R464/R465).
* `proj_deep_coerced` — FIX 2: COERCE to the weaker flat type and project there, `he.toF.toExtra`
  (`[[ref-coerce-to-weaker-reuse-wrapper]]`) — exactly how the deep per-entry PRODUCER reads its
  boundary facts, `(RecSeqBodyDeep.toFlat h_body_rec).openerAdjHead` (R466, the recursion-closing
  `emit_scans_in_flow_rec_entry_both_deep` LANDED this round).
* `mirror_cost_is_conjunct_vs_projection` — the finding in one proposition.

All sorry-free AND diagnostic-free; every route is a machine-checked theorem the build re-checks on
every change.
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
    conjunct (the map-body assembler's `h_ve.toEntryUnit`, R464/R465) OR a coerce-then-project where the
    deep⟹flat coercion exists (the per-entry producer's boundary reads, R466 — both LANDED). -/

/-- Flat assembler reading `Extra` via the projection `he.toExtra` (mirror `h_ve.toEntryUnit`). -/
theorem proj_flat (h : PFlat) : ∃ out, Extra out := by
  obtain ⟨out, _hx, he⟩ := h
  exact ⟨out, he.toExtra⟩

/-! **The gap.**  The naive text-swap of `proj_flat` — `he.toExtra` where `he : DEntry _` — does NOT
    elaborate: the minimal deep family carries no `.toExtra` projection (evident from the `DEntry`
    definition above, which declares only `.toF`).  There are TWO zero-cost fixes, both machine-checked
    below — reroute to the standalone conjunct, or coerce-then-project — so no noisy `#check_failure`
    negative witness is needed. -/

/-- **The reroute (FIX 1).**  Read `Extra` from the predicate's STANDALONE conjunct `hx` instead of
    projecting it off the entry.  This is why the strengthened predicate KEEPS the standalone `Extra`
    conjunct: it is the reroute target the deep family's shed projection forces.  (The map-body brick
    R464/R465.) -/
theorem proj_deep_rerouted (h : PDeep) : ∃ out, Extra out := by
  obtain ⟨out, hx, _he⟩ := h
  exact ⟨out, hx⟩

/-- **The coerce-then-project alternative (FIX 2, `[[ref-coerce-to-weaker-reuse-wrapper]]`).**  When the
    deep⟹flat coercion `DEntry.toF` is available, the shed projection is recovered by COERCING to the
    weaker flat type and projecting there: `he.toF.toExtra` (two hops, since a direct `he.toExtra` does
    not exist).  This is precisely how the deep per-entry PRODUCER reads its boundary facts —
    `(RecSeqBodyDeep.toFlat h_body_rec).openerAdjHead` / `RecMapBody.lastNonSep (RecMapBodyDeep.toFlat …)`
    — in `emit_scans_in_flow_rec_entry_both_deep` (R466, the recursion-closing brick).  The producer
    keeps ONE substrate (the deep family) and weakens on demand at the read site. -/
theorem proj_deep_coerced (h : PDeep) : ∃ out, Extra out := by
  obtain ⟨out, _hx, he⟩ := h
  exact ⟨out, he.toF.toExtra⟩

/-- **The finding in one proposition.**  (1) when the flat proof reads a per-item fact from the
    STANDALONE conjunct, flat and deep assemblers have the SAME proof (`clean_flat`/`clean_deep`) — a
    pure text-swap; (2) when it reads via a PROJECTION off the entry, the deep mirror needs a reroute to
    the standalone conjunct (`proj_deep_rerouted`) — or, where the deep⟹flat coercion exists, a
    coerce-then-project (`proj_deep_coerced`) — because the minimal deep family shed the projection.  So
    the mirror's cost is QUANTIFIED before writing it: (text swaps) +
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

/-! ## COROLLARY — composite (key ++ value) items: the reroute lands on the END-most sub-block only.
    A map item is a PAIR; its predicate carries a standalone `Extra` for EACH side.  But the consumer
    only ever projects the BOUNDARY fact (last-token-not-opener-or-sep), and the pair's boundary is the
    VALUE tail — so the value side is the projection read that must reroute, while the key side (interior,
    never the boundary) stays a pure conjunct read.  This is exactly why `emitPairList_scans_recmapbody`
    reads `h_ve.toEntryUnit` (value) but no key projection: 2 reroutes, value side only. -/

/-- A flat pair deliverable: key entry then value entry, each with its standalone `Extra` conjunct. -/
def PFlatPair : Prop := ∃ kb vb, Extra kb ∧ FEntry kb ∧ Extra vb ∧ FEntry vb
/-- The deep parallel — both entries deep. -/
def PDeepPair : Prop := ∃ kb vb, Extra kb ∧ DEntry kb ∧ Extra vb ∧ DEntry vb

/-- KEY side — the consumer reads no projection off the key (interior, never the boundary), so flat and
    deep are the SAME proof, a pure swap.  (Mirror: the map-body key arm — zero reroutes.) -/
theorem pair_clean_key (h : PDeepPair) : ∃ kb, Extra kb := by
  obtain ⟨kb, _vb, hxk, _hk, _hxv, _hv⟩ := h
  exact ⟨kb, hxk⟩

/-- VALUE side, FLAT — the boundary fact is the value tail, read here via the projection `hv.toExtra`
    (mirror `h_ve.toEntryUnit`). -/
theorem pair_proj_value_flat (h : PFlatPair) : ∃ vb, Extra vb := by
  obtain ⟨_kb, vb, _hxk, _hk, _hxv, hv⟩ := h
  exact ⟨vb, hv.toExtra⟩

/-- VALUE side, DEEP — the lone reroute: `hv : DEntry vb` sheds `.toExtra`, so read the standalone value
    `Extra` conjunct `hxv` instead.  This is the whole key/value asymmetry: reroute, value side only. -/
theorem pair_proj_value_rerouted (h : PDeepPair) : ∃ vb, Extra vb := by
  obtain ⟨_kb, vb, _hxk, _hk, hxv, _hv⟩ := h
  exact ⟨vb, hxv⟩

end Tests.Reflections.MirrorReadsConjunctNotProjection
