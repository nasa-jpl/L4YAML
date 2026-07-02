/-!
# Reflection 453 — a deliverable consumed in TWO ROLES at different strengths cannot carry an
# additive REQUIRED field on its SHARED constructor: the weak-role builder has no data to fill it.
# The resolution is a SEPARATE constructor for the strong field, built only by the strong role.

Self-contained (core Lean, no `L4YAML` import) toy of the R453 finding — the DE-RISK of the
queued "add `RecMapBody` to `RecSeqEntry.map`" step, which reading the real construction sites
reveals is BLOCKED.

Context.  The plan (R450–R452) was: now that the producer is merged (`emit_scans_in_flow_rec_entry_both`),
make the map path recursive by adding a field `h_rec : RecMapBody interior` to the shared
`RecSeqEntry.map` constructor, so a map-valued key/value carries the body the MAP navigator descends.
The cited justification was [[ref-additive-parallel-type-over-shared-edit]] — but that principle
warns AGAINST exactly this: a structural edit to a shared/polymorphic type.

The blocker (read off the real code, four construction sites of `RecSeqEntry.map`):

  `RecSeqEntry` is built in TWO ROLES.
  * PRODUCER role (`emit_scans_in_flow_rec_entry_both`'s mapping arm): HAS a `RecMapBody` available
    (from the `emitPairList_scans_recmapbody` assembler) — it could supply the field.
  * SEQ-NAVIGATOR role (`recseqentry_map_window` / `recseqentry_map_dispatch`, the seq locate
    driver's NEAR-LEAF): a nested mapping found while locating a seq item is the point at which the
    seq path SEVERS (R335/R449).  This builder synthesizes `RecSeqEntry.map` from RAW BALANCE
    (`flowBracketBalance` / `WellBracketed interior`) — it has NO `RecMapBody` and no way to get one
    (recovering it needs the key/value structure the balance-only locate never computed).

A REQUIRED field on the single shared `map` constructor is therefore uninhabitable by the
seq-navigator role.  (The newer `nestedSeq_recseqentry_locate_*` family could thread the field from
its `cases h_e` on an incoming `RecSeqBody`, but `recseqentry_map_window` — which must compile — has
no such input; and it feeds the live `recseqentry_classify` chain, so it cannot simply be deleted.)

The resolution — a SEPARATE constructor.  Keep `RecSeqEntry.map` FLAT (the seq-navigator role builds
it from balance, unchanged) and add a parallel `RecSeqEntry.mapRec` carrying the recursive body (the
producer role builds it).  The map navigator descends only `mapRec`; the seq path keeps severing at
`map`.  Every `cases`/projection gains one `mapRec` arm — a verbatim mirror of the `map` arm reading
the balance fact and ignoring the new field.  This is the additive-parallel refinement done RIGHT:
not a new field on the shared constructor, but a new constructor whose strong field only the strong
role fills.

This toy mirrors that exactly:

* `E`         — the shared entry deliverable (mirror `RecSeqEntry`).
* `E.map`     — the FLAT constructor the WEAK (seq-navigator) role builds from `Flat` alone.
* `E.mapRec`  — the RECURSIVE constructor the STRONG (producer) role builds, storing the map body.
* `MB`        — the recursive map body (mirror `RecMapBody`), recursing back through `E` on its
                key/value blocks — the recursion `MB → E.mapRec → MB` the map navigator descends.

`navMap`/`prodMap` are the two role builders.  `flat_does_not_determine_MB` PROVES the blocker (no
total `Flat → MB`, so a required field is uninhabitable by `navMap`).  `E.nonempty` shows the
per-matcher cost (the verbatim `mapRec` arm).  The depth-2 `example` shows the recursion closing
through `mapRec` — precisely because `mapRec` STORES the inner body the `map` constructor severs.

All sorry-free.
-/

set_option autoImplicit false

namespace Tests.Reflections.TwoRoleDeliverableBlocksSharedField

/-- Toy token alphabet: scalar, `{`/`}` (map open/close), `.key`/`.value`.  Mirrors the
    `YamlToken` shapes the real entries are built over. -/
inductive Tok where
  | sc   -- scalar
  | om   -- '{'  (flowMappingStart)
  | cm   -- '}'  (flowMappingEnd)
  | k    -- '.key'
  | v    -- '.value'
deriving DecidableEq

/-- The balance-only fact a navigator holds at a near-leaf (mirror `WellBracketed interior`):
    a coarse predicate that does NOT encode the recursive map structure.  Modelled as `True` —
    every interior "balances", but balancing says nothing about its key/value structure.  This is
    the whole data the seq-navigator role has when it classifies a nested mapping. -/
def Flat (_ : List Tok) : Prop := True

/- The shared entry deliverable `E` (mirror `RecSeqEntry`) and the recursive map body `MB`
   (mirror `RecMapBody`), MUTUALLY recursive: a map body's key/value blocks are `E`s, and an
   `E.mapRec` stores an `MB` for its interior — the recursion the map navigator descends.
   Plain `/- -/`, not `/-- -/`: a doc comment cannot attach to `mutual` (the Reflection-234 gotcha). -/
mutual
  /-- Mirror of `RecSeqEntry`.  `map` is the FLAT constructor the seq-navigator near-leaf
      (`recseqentry_map_window`) builds from `Flat` only — the severed edge.  `mapRec` is the
      RECURSIVE constructor the producer builds, additionally storing the map body `MB`.  The two
      inhabit the SAME `{ interior }` window WITHOUT forcing the weak role to supply `MB`. -/
  inductive E : List Tok → Prop where
    | scalar : E [Tok.sc]
    | map (interior : List Tok) (h_flat : Flat interior) :
        E (Tok.om :: (interior ++ [Tok.cm]))
    | mapRec (interior : List Tok) (h_flat : Flat interior) (h_rec : MB interior) :
        E (Tok.om :: (interior ++ [Tok.cm]))
  /-- Mirror of `RecMapBody`: a key/value pair whose two blocks are `E`s — the recursion closes
      here (a map body is made of entries, an entry may be a recursive map). -/
  inductive MB : List Tok → Prop where
    | mk (bk bv : List Tok) (hk : E bk) (hv : E bv) :
        MB (Tok.k :: (bk ++ Tok.v :: bv))
end

/-! ### The two roles that build `E.map`'s window. -/

/-- **WEAK role** — the seq-navigator near-leaf (`recseqentry_map_window`).  Only `Flat interior` in
    hand (synthesized from raw balance during seq locate), builds the FLAT `E.map`.  THIS is the
    builder a REQUIRED `MB` field on the shared `map` constructor would make impossible. -/
theorem navMap (interior : List Tok) (h : Flat interior) :
    E (Tok.om :: (interior ++ [Tok.cm])) :=
  E.map interior h

/-- **STRONG role** — the producer (`emit_scans_in_flow_rec_entry_both`'s mapping arm, via the
    `emitPairList_scans_recmapbody` assembler).  Has `Flat interior` AND the recursive `MB interior`,
    builds `E.mapRec`.  The strong field is filled only here. -/
theorem prodMap (interior : List Tok) (h : Flat interior) (hr : MB interior) :
    E (Tok.om :: (interior ++ [Tok.cm])) :=
  E.mapRec interior h hr

/-! ### The blocker, PROVEN — why a required field on the shared constructor fails. -/

/-- **THE BLOCKER.**  `Flat` does NOT determine `MB`: there is an interior that is `Flat` but has no
    `MB`.  So there is no total function `Flat interior → MB interior`, hence a REQUIRED
    `h_rec : MB interior` field on the SINGLE `map` constructor is uninhabitable by `navMap` (whose
    only data is `Flat`).  The real witness: a nested mapping located by the seq driver carries only
    `WellBracketed interior`; recovering its `RecMapBody` needs the key/value structure the
    balance-only locate never computed. -/
theorem flat_does_not_determine_MB : ∃ interior, Flat interior ∧ ¬ MB interior :=
  ⟨[Tok.sc], trivial, fun h => by cases h⟩

/-! ### The per-matcher cost — every `cases`/projection gains one verbatim `mapRec` arm. -/

/-- A projection BOTH map constructors satisfy (mirror `RecSeqEntry.toWellBracketed`/`toEntrySafe`):
    the new `mapRec` arm is a VERBATIM mirror of the `map` arm — it reads the balance fact and
    ignores `h_rec`.  This is the entire per-matcher cost of the separate constructor: one extra
    arm, mechanical.  (The real codebase has ~13 such `RecSeqEntry` matchers.) -/
theorem E.nonempty {e : List Tok} (h : E e) : e ≠ [] := by
  cases h with
  | scalar => exact List.cons_ne_nil _ _
  | map interior _ => exact List.cons_ne_nil _ _
  | mapRec interior _ _ => exact List.cons_ne_nil _ _   -- verbatim mirror of the `map` arm

/-! ### The recursion closes through `mapRec` — the map navigator's descent is inhabited. -/

/-- A depth-2 witness: the map body `{ k: sc, v: { k: sc, v: sc } }`-shaped — the OUTER pair's value
    block is a nested map `E.mapRec` carrying the INNER map body.  This is the recursion
    `MB → E.mapRec → MB` the map navigator descends; it closes precisely because `mapRec` STORES the
    inner `MB` — the field the seq navigator's `map` constructor severs.  Built bottom-up.  A
    `map`-built value here would dead-end the descent (no inner body to recover). -/
example :
    MB (Tok.k :: ([Tok.sc] ++ Tok.v ::
      (Tok.om :: ((Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) ++ [Tok.cm])))) := by
  -- inner map body `{ k: sc, v: sc }` — one pair, both blocks scalar leaves.
  have inner : MB (Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) :=
    MB.mk [Tok.sc] [Tok.sc] E.scalar E.scalar
  -- inner map entry — built with `mapRec`, carrying the inner body (descent can recurse).
  have innerMap : E (Tok.om :: ((Tok.k :: ([Tok.sc] ++ Tok.v :: [Tok.sc])) ++ [Tok.cm])) :=
    E.mapRec _ trivial inner
  -- outer pair: key `sc`, value the inner map.
  exact MB.mk [Tok.sc] _ E.scalar innerMap

/-! ### The law, packaged. -/

/-- **The finding in one proposition.**  The separate constructor lets BOTH roles inhabit the map
    window — the weak role with `Flat` alone (`navMap → E.map`), the strong role with the recursive
    body (`prodMap → E.mapRec`) — and the third conjunct is exactly why a REQUIRED field on a single
    shared constructor cannot: `Flat` does not determine `MB`.  Sharpens
    [[ref-additive-parallel-type-over-shared-edit]] (a new CONSTRUCTOR, not a new FIELD on the shared
    one) and names the trap [[ref-derisk-consumer-blindspot-vs-contract]] / [[ref-coerce-to-weaker-reuse-wrapper]]
    warn about: a shared deliverable consumed at two strengths. -/
theorem separate_constructor_resolves_two_roles :
    (∀ interior, Flat interior → E (Tok.om :: (interior ++ [Tok.cm])))                       -- weak role
    ∧ (∀ interior, Flat interior → MB interior → E (Tok.om :: (interior ++ [Tok.cm])))       -- strong role
    ∧ (∃ interior, Flat interior ∧ ¬ MB interior) :=                                         -- required field fails
  ⟨navMap, prodMap, flat_does_not_determine_MB⟩

end Tests.Reflections.TwoRoleDeliverableBlocksSharedField
