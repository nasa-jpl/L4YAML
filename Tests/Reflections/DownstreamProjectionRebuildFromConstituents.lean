/-!
# Reflection 457 — a projection method you proved for a deliverable (for a DOWNSTREAM consumer) is a
# FORWARD REFERENCE at an UPSTREAM producer that BUILDS the deliverable: the producer cannot call its
# own downstream projection. Rebuild the needed boundary fact from the LOCAL constituents the producer
# already has — the same constituents the projection itself is built from — and the two routes
# coincide (no information is lost by not using the projection).

Self-contained (core Lean, no `L4YAML` import) toy of the R457 finding, made executing STEP D step 2b
of the `mapRec` programme: strengthen the assembler `emitPairList_scans_recmapbody` to carry body
`OpenerAdj`/`SepAdj`.

The trap.  The assembler's per-pair OpenerAdj seam needs each entry's TAIL-not-opener fact.  The
entry is a `key: value` pair, and R455 had just landed `RecMapBody.lastNonOpener` — exactly this
boundary fact off the deliverable.  So the natural move was
`(RecMapBody.single _ … h_pair …).lastNonOpener`.  **It failed:** `RecMapBody.lastNonOpener` is
declared ~1400 lines DOWNSTREAM of the assembler (it was added for the future map NAVIGATOR, a
consumer that lives later in the file), so at the assembler it is an unknown identifier — a forward
reference.  A producer that BUILDS a deliverable sits UPSTREAM of the projections proved for that
deliverable's downstream consumers; it cannot call them.

The fix.  Rebuild the boundary fact from the LOCAL constituents the producer already has.  The entry
ends in its VALUE block (`entry = front ++ value`), so the entry's tail-not-opener is the value
block's tail-not-opener, lifted across the append by `lastNonOpener_append_right` — and the value's
tail-not-opener comes off its `EntryUnit`.  These are exactly the constituents `RecMapBody.lastNonOpener`
itself recurses to (the last pair's value block).  Producer and projection share the SAME underlying
derivation; only the entry point differs by declaration site.

This toy mirrors that exactly:

* `lastA` / `append_right_lastA` — the boundary fact and the constituent-lift lemma (mirror
  `lastNonOpener_append_right`).
* `Value` / `Value.lastA` — the constituent (mirror the value `RecSeqEntry` + `EntryUnit`).
* `Deliv` / `Deliv.lastA`  — the deliverable and ITS projection (mirror `RecMapBody` /
  `RecMapBody.lastNonOpener`), the DOWNSTREAM route.
* `producer_lastA`         — the UPSTREAM producer's route: rebuild from the constituent via
  `append_right_lastA`, NOT `Deliv.lastA`.
* `routes_agree`           — both routes deliver the same boundary fact (here, definitionally the
  same `append_right_lastA` application — the projection is just the producer's route packaged).

The point the toy can only DESCRIBE (a forward reference cannot compile): if `producer_lastA` tried to
call `Deliv.lastA` while `Deliv.lastA` were declared AFTER it, Lean would report an unknown
identifier.  The fix is to inline the constituent route — which `Deliv.lastA` is itself built from.

The law: a deliverable's projection is usable only AT-OR-AFTER its declaration; an upstream producer
rebuilds the boundary fact from the constituents (the projection's own ingredients), losing nothing.
Sharpens `[[ref-severed-constructor-boundary-projects-interior-doesnt]]` (boundary facts are
constituent-derivable, so a producer can always rebuild them) and is the use-site dual of the
declaration-ordering safety argument in `[[ref-constructor-field-forces-mutual-group-merge]]`.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.DownstreamProjectionRebuildFromConstituents

/-- Toy alphabet: `a` content, `op`/`cl` brackets. -/
inductive Tok where
  | a | op | cl
deriving DecidableEq

/-- The boundary fact (mirror "last token ≠ opener"; here "last token is `a`"). -/
def lastA (l : List Tok) : Prop := l.getLast? = some Tok.a

/-- **Constituent-lift** (mirror `lastNonOpener_append_right`): a block ending in `b` inherits `b`'s
    boundary fact.  This is the shared ingredient BOTH the producer and the projection use. -/
theorem append_right_lastA (a b : List Tok) (_hb : b ≠ []) (h : lastA b) : lastA (a ++ b) := by
  unfold lastA at *
  rw [List.getLast?_append, h]; rfl

/-- The constituent (mirror the value `RecSeqEntry` + its `EntryUnit`): carries the boundary fact. -/
inductive Value : List Tok → Prop where
  | mk : Value [Tok.a]

theorem Value.lastA : {l : List Tok} → Value l → lastA l
  | _, .mk => rfl
theorem Value.ne_nil : {l : List Tok} → Value l → l ≠ []
  | _, .mk => by simp

/-- The deliverable (mirror `RecMapBody`): built from a `front` ending in a `Value`. -/
inductive Deliv : List Tok → Prop where
  | mk (front : List Tok) (v : List Tok) (hv : Value v) : Deliv (front ++ v)

/-- **The DELIVERABLE's projection** (mirror `RecMapBody.lastNonOpener`) — the DOWNSTREAM route, used
    by a consumer that lives AFTER this declaration.  Built from the constituent via the shared
    `append_right_lastA`. -/
theorem Deliv.lastA : {l : List Tok} → Deliv l → lastA l
  | _, .mk front v hv => append_right_lastA front v hv.ne_nil hv.lastA

/-- **The UPSTREAM producer's route.**  A producer building `Deliv (front ++ v)` needs `lastA
    (front ++ v)`.  If `Deliv.lastA` were declared AFTER this site it would be a forward reference —
    so the producer rebuilds the fact from the LOCAL constituent `v` via the SAME `append_right_lastA`
    the projection uses.  (In the real code: the assembler used `lastNonOpener_append_right` off the
    value block's `EntryUnit`, because `RecMapBody.lastNonOpener` is declared ~1400 lines later.) -/
theorem producer_lastA (front v : List Tok) (hv : Value v) : lastA (front ++ v) :=
  append_right_lastA front v hv.ne_nil hv.lastA   -- constituent route, NOT `Deliv.lastA`

/-- The two routes deliver the same boundary fact — the projection is just the producer's route
    packaged, so rebuilding from constituents loses nothing. -/
theorem routes_agree (front v : List Tok) (hv : Value v) :
    producer_lastA front v hv = Deliv.lastA (Deliv.mk front v hv) := rfl

/-- **The finding in one proposition.**  Both the upstream producer route and the downstream
    projection route deliver the deliverable's boundary fact, and they share the constituent-lift
    `append_right_lastA` — so an upstream producer that cannot reach its deliverable's (downstream)
    projection rebuilds the fact from constituents with no loss.  Sharpens
    `[[ref-severed-constructor-boundary-projects-interior-doesnt]]`. -/
theorem downstream_projection_rebuild_from_constituents :
    (∀ front v, Value v → lastA (front ++ v))                 -- producer route (upstream)
    ∧ (∀ l, Deliv l → lastA l) :=                              -- projection route (downstream)
  ⟨fun front v hv => producer_lastA front v hv, fun _ h => Deliv.lastA h⟩

end Tests.Reflections.DownstreamProjectionRebuildFromConstituents
