/-!
# Reflection 458 — a downstream projection unreachable at an upstream producer has TWO remedies
# (rebuild-from-constituents vs move-the-projection-up); the SELECTOR is the GRAIN at which the
# producer holds the deliverable.  CONSTITUENTS IN HAND → rebuild locally.  OPAQUE WHOLE → you
# cannot rebuild without `cases`-ing it open (= re-deriving the projection), so MOVE the projection
# upstream.  Secondary: a recursive constructor that cannot represent the DEGENERATE (empty) case
# forces an emptiness DISPATCH (empty → flat fallback constructor, non-empty → recursive
# constructor), unified behind a builder FUNCTION so the outer assembler stays constructor-blind.

Self-contained (core Lean, no `L4YAML` import) toy of the R458 finding, executing STEP D steps 2c+3
of the `mapRec` programme: wire the two map arms of `emit_scans_in_flow_rec_entry_both` to build
`RecSeqEntry.mapRec` (carrying `RecMapBody interior`) instead of the flat `RecSeqEntry.map`.

The setup.  R457 had strengthened the *assembler* `emitPairList_scans_recmapbody` to carry the body's
boundary facts by REBUILDING them from the constituents it had in hand (the value block `block_v`),
because `RecMapBody.lastNonOpener` was declared ~1400 lines DOWNSTREAM
(`[[ref-downstream-projection-unavailable-rebuild-from-constituents]]`).  R458 then needs the SAME
boundary facts at the two *map arms* of the producer — but there the body arrives as a single opaque
hypothesis `RecMapBody bodyBlock` returned from the assembler sub-call.  The producer holds NO
constituents, only the whole.

The selector.  At the assembler (constituents in hand) you rebuild: `lastNonOpener_append_right`
off the value block's `EntryUnit`.  At the producer (opaque whole) you CANNOT rebuild without
`cases`-ing `RecMapBody bodyBlock` open and re-deriving the projection inline — which *is* the
projection.  With TWO such opaque-whole sites (both map arms), the dependency-correct fix is to MOVE
`RecMapBody.lastNonOpener`/`.lastNonSep` (and the `RecSeqEntry.ne_nil`/`head_contentStart` helpers
they read) UP to the projection-family region — a move safe by the earlier-declaration ordering
check, since the projections reference only constructors and upstream helpers.  Then the producer
just calls `RecMapBody.lastNonOpener h_body_rec`.

The degenerate dispatch.  `RecSeqEntry.mapRec` carries `RecMapBody interior`, but `RecMapBody` has NO
empty constructor (`single`/`cons` are both non-empty).  So an empty map `{}` (`bodyBlock = []`)
cannot inhabit `.mapRec` — it must fall back to the flat `.map` (which needs only `WellBracketed []`).
The producer dispatches on emptiness and packages BOTH constructors behind one builder function
`(∀ open close, h_open → h_close → RecSeqEntry (open :: (body ++ [close])))` carried as a conjunct of
the nested existential, so the outer wrap code applies it constructor-blind.

This toy mirrors all three:

* `append_right_lastA` / `Val` — the constituent-lift lemma and the leaf constituent (mirror
  `lastNonOpener_append_right` + the value `RecSeqEntry`/`EntryUnit`).
* `RBody` / `RBody.lastA` — the recursive deliverable (NON-EMPTY only, like `RecMapBody`) and its
  boundary projection (mirror `RecMapBody.lastNonOpener`), declared upstream after the move.
* `assembler_lastA` — CONSTITUENTS IN HAND: rebuilds `lastA (front ++ v)` from the leaf `v`, never
  touching `RBody.lastA` (the R457 route).
* `producer_lastA` — OPAQUE WHOLE: holds only `RBody body`, so it CALLS `RBody.lastA body` (the R458
  route — the projection in scope only because it was moved up).
* `move_vs_rebuild_selected_by_grain` — both routes deliver the boundary fact; which one applies is
  fixed by whether the producer holds the constituents or the whole.
* `Entry` / `entryBuilder` — the recursive `recC` (carries `RBody`) vs flat `flatC` (carries `Flat`),
  with the empty body forced into `flatC`, and the emptiness dispatch packaged behind one builder.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.OpaqueWholeMovesProjectionConstituentsRebuild

/-- Toy alphabet: `a` content, `op`/`cl` brackets. -/
inductive Tok where
  | a | op | cl
deriving DecidableEq

/-- The boundary fact (mirror "last token ≠ opener"; here "last token is `a`"). -/
def lastA (l : List Tok) : Prop := l.getLast? = some Tok.a

/-- **Constituent-lift** (mirror `lastNonOpener_append_right`): a block ending in `y` inherits `y`'s
    boundary fact.  The shared ingredient BOTH the rebuild route and the projection use. -/
theorem append_right_lastA (x y : List Tok) (_hy : y ≠ []) (h : lastA y) : lastA (x ++ y) := by
  unfold lastA at *
  rw [List.getLast?_append, h]; rfl

/-- The leaf constituent (mirror the value `RecSeqEntry` + its `EntryUnit`): carries the fact. -/
inductive Val : List Tok → Prop where
  | mk : Val [Tok.a]

theorem Val.lastA : {l : List Tok} → Val l → lastA l
  | _, .mk => rfl
theorem Val.ne_nil : {l : List Tok} → Val l → l ≠ []
  | _, .mk => by simp

/-- The recursive deliverable (mirror `RecMapBody`): one or more `Val` blocks, **NON-EMPTY only** —
    no `[]` constructor, which is exactly why the empty body cannot inhabit it. -/
inductive RBody : List Tok → Prop where
  | single (v : List Tok) (hv : Val v) : RBody v
  | cons (v rest : List Tok) (hv : Val v) (hr : RBody rest) : RBody (v ++ rest)

theorem RBody.ne_nil : {l : List Tok} → RBody l → l ≠ []
  | _, .single _ hv => hv.ne_nil
  | _, .cons _ _ hv _ => by cases hv; simp

/-- **The deliverable's boundary projection** (mirror `RecMapBody.lastNonOpener`).  Declared HERE,
    upstream of the producer (after the step-2c move), by recursion to the last `Val` block.  Note it
    is built from EXACTLY the constituents the rebuild route uses — `append_right_lastA` + the leaf's
    `lastA` — so projecting and rebuilding share one derivation. -/
theorem RBody.lastA : {l : List Tok} → RBody l → lastA l
  | _, .single _ hv => hv.lastA
  | _, .cons v rest _ hr => append_right_lastA v rest hr.ne_nil hr.lastA

/-- **Assembler route — CONSTITUENTS IN HAND** (mirror R457's `emitPairList_scans_recmapbody`).  It
    builds the single pair `front ++ v` and, holding the leaf constituent `v`, needs `lastA
    (front ++ v)`.  It REBUILDS from `v` via `append_right_lastA` — it never calls `RBody.lastA`
    (which, in the real code, was declared downstream at this site). -/
theorem assembler_lastA (front v : List Tok) (hv : Val v) : lastA (front ++ v) :=
  append_right_lastA front v hv.ne_nil hv.lastA   -- leaf constituent in hand

/-- **Producer route — OPAQUE WHOLE** (mirror R458's map arm building `RecSeqEntry.mapRec`).  It
    receives the body's recursive deliverable `hb : RBody body` as a single hypothesis from a
    sub-call and needs `lastA body` to feed the wrap.  It holds NO constituents — only the opaque
    whole — so it CANNOT rebuild via `append_right_lastA`; it CALLS the projection `RBody.lastA hb`
    (in scope only because the projection was MOVED upstream).  Re-deriving inline would mean
    `cases hb` — i.e. rewriting `RBody.lastA` itself. -/
theorem producer_lastA (body : List Tok) (hb : RBody body) : lastA body :=
  RBody.lastA hb   -- opaque whole: project, don't rebuild

/-- **The selector in one proposition.**  Both routes deliver the deliverable's boundary fact; which
    one applies is fixed by the GRAIN at which the producer holds the deliverable — constituents in
    hand (rebuild) vs opaque whole (project, after moving the projection up).  Sharpens
    `[[ref-downstream-projection-unavailable-rebuild-from-constituents]]` by naming the criterion. -/
theorem move_vs_rebuild_selected_by_grain :
    (∀ front v, Val v → lastA (front ++ v))            -- constituents in hand → rebuild
    ∧ (∀ body, RBody body → lastA body) :=             -- opaque whole → project (moved up)
  ⟨fun front v hv => assembler_lastA front v hv, fun body hb => producer_lastA body hb⟩

/-- Flat fallback predicate (mirror `WellBracketed`): holds of ANY block, including `[]`. -/
def Flat (_l : List Tok) : Prop := True

/-- The wrapped entry (mirror `RecSeqEntry`): a recursive `recC` carrying `RBody` and a flat `flatC`
    carrying only `Flat`.  The empty body inhabits ONLY `flatC` — `RBody` has no `[]` constructor. -/
inductive Entry : List Tok → Prop where
  | recC (body : List Tok) (hb : RBody body) : Entry (Tok.op :: (body ++ [Tok.cl]))
  | flatC (body : List Tok) (hf : Flat body) : Entry (Tok.op :: (body ++ [Tok.cl]))

/-- **Degenerate-case dispatch behind a builder function.**  The producer cannot build `recC` for an
    empty body (no `RBody []`), so it DISPATCHES: empty → `flatC` (needs only `Flat`), non-empty →
    `recC` (the rich recursive constructor).  Both branches return the SAME builder type, so the
    outer wrap applies it constructor-blind (mirror the `h_entry_builder` conjunct of the map arms'
    nested existential: `.mapRec` for non-empty pairs, `.map` for empty `{}`). -/
theorem entryBuilder (body : List Tok) (h : RBody body ∨ body = []) :
    Entry (Tok.op :: (body ++ [Tok.cl])) :=
  match h with
  | .inl hb => .recC body hb
  | .inr _  => .flatC body trivial

/-- **The finding in one proposition.**  (1) the rebuild route and the projection route both deliver
    the boundary fact, selected by grain; (2) the empty body cannot inhabit the recursive deliverable
    yet the builder still produces a wrapped `Entry` for it.  Sharpens
    `[[ref-downstream-projection-unavailable-rebuild-from-constituents]]`. -/
theorem opaque_whole_moves_projection_constituents_rebuild :
    (∀ front v, Val v → lastA (front ++ v))            -- constituents → rebuild
    ∧ (∀ body, RBody body → lastA body)               -- opaque whole → project (moved up)
    ∧ Entry (Tok.op :: ([] ++ [Tok.cl])) :=            -- empty body still wraps, via the flat fallback
  ⟨fun front v hv => assembler_lastA front v hv,
   fun body hb => producer_lastA body hb,
   entryBuilder [] (Or.inr rfl)⟩

end Tests.Reflections.OpaqueWholeMovesProjectionConstituentsRebuild
