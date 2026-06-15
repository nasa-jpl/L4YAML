/-!
# Reflection 449 — a SEVERED recursive edge (R448) does not cost ONE sibling navigator; it costs a
# navigator PER nesting level.  When a deliverable stores a FLAT witness at its foreign-type
# constructor, EACH navigator can cross that foreign boundary at most ONCE (descending into the
# structure the producer built AT that boundary), so a target nested behind k foreign boundaries needs
# k crossings and is unreachable for k ≥ 2.  A PATH-BLIND producer domain admits arbitrary nesting
# depth, so closing it cannot be done by adding ONE sibling navigator — the deliverable itself must
# store a RECURSIVE witness at the foreign constructor (mutual recursion to any depth).

Self-contained (core Lean, no `L4YAML` import) toy of the R449 finding — the map-mirror probe round.

Context (sharpens R448).  R448 found the seq ROOT CARRIER `SeqInteriorSeparators tokens 2 (size-2)`
is a UNIVERSAL over the path-blind domain `SeqTypedInterior` (top frame `[`), strictly wider than the
all-seq locator's reach (`SeqPathAllSeq`, whole path `[`); the gap is map-nested seqs, severed at
`RecSeqEntry.map`'s flat `WellBracketed`.  R448 concluded the MAP MIRROR (a sibling navigator over
`RecMapBody`) is on the carrier's critical path.

R449 probes the map mirror's single-step shape and finds the consequence: ONE sibling navigator is NOT
enough.  `RecSeqEntry.map` stores only `h_wb : WellBracketed interior` — no recursive witness — so the
MAP navigator dead-ends at a NESTED map exactly as the SEQ navigator dead-ends at a map.  Concretely
(`MapPathLocatorMoveProbe`):

* `[{a:[b]}]`, `[{a:[b,c]}]` (map-depth 1): the target seq is the map's VALUE — DESCEND-VALUE reaches a
  `RecSeqEntry.seq`, REACHABLE by the map mirror.
* `[{a:{x:[b]}}]` (map-depth 2): the map's value is a `RecSeqEntry.map` (only `WellBracketed`), so the
  inner `[b]` is behind a SECOND severance — UNREACHABLE by the map mirror.

Yet all three seq windows are in the carrier's path-blind domain `SeqTypedInterior`.  So the map mirror
over the CURRENT depth-bounded deliverable serves map-depth ≤ 1 only; the carrier's domain (any depth)
needs the FULLY-RECURSIVE map interior — `RecSeqEntry.map` storing a recursive `RecMapBody` — so the
seq/map navigators MUTUALLY recurse to any depth.

The reusable rule.  A severed recursive edge (a deliverable storing a FLAT witness at its foreign-type
constructor) is not patched by ONE sibling navigator: each navigator crosses the foreign boundary at
most once, so a target nested behind k boundaries needs k navigators.  A path-blind producer domain
admits unbounded k.  The only bounded-cost fix is to make the deliverable store a RECURSIVE witness at
the foreign constructor — turning the navigators into a MUTUAL recursion that descends any depth.

This toy has two parts:

* PART 1 (the depth ladder generalizing R448's domain/reach gap): a path from the root to a target seq
  is a `List Frame`; `inDomain` (the carrier domain) reads only the LAST frame (path-blind — a seq is
  always enclosed by `[`); `reachCurrent` (what seq locator + map mirror over the current deliverable
  serve) is `mapDepth ≤ 1`.  `reachCurrent_imp_inDomain`, and the minimal TRIPLE `[seq]` / `[map,seq]` /
  `[map,map,seq]` — all in domain, map-depths 0/1/2, only the first two reachable.
* PART 2 (why the bound is structural — the recursion stores a flat witness): the deliverable
  `SEntry`/`SBody` stores a RECURSIVE body at `.seq` but a FLAT witness at `.map`; both navigators
  (`descendSeqEntry`, `descendMapValue`) return `none` at `.map`.  The FIX `RSEntry` stores a recursive
  `RMBody` at `.map`, and `descendRMapValue (.map b) = some b` — the foreign-nested structure is
  recovered, so a mutual seq/map navigator descends any depth.

All sorry-free; axiom footprint `[propext]` only.
-/

set_option autoImplicit false

namespace Tests.Reflections.SeveranceRecursesByNestingDepth

/-! ## PART 1 — the severance is a DEPTH LADDER: reach = `mapDepth ≤ 1`, domain = any depth. -/

/-- A bracket frame on the path from the root to a target window. -/
inductive Frame where
  | seq    -- a `[` frame
  | map    -- a `{` frame
deriving DecidableEq

/-- A path from the root down to a target seq window: the frames crossed, root-first. -/
abbrev Path := List Frame

/-- Number of MAP frames on the path — the count of foreign boundaries between the root and the target.
    Each one is a `RecSeqEntry.map` severance the navigators must cross. -/
def mapDepth : Path → Nat
  | []            => 0
  | .seq :: rest  => mapDepth rest
  | .map :: rest  => mapDepth rest + 1

/-- The carrier's DOMAIN (`SeqTypedInterior`): the target's IMMEDIATE enclosing frame is `[` — the LAST
    frame on the path.  PATH-BLIND: reads only the innermost frame, ignoring `mapDepth`. -/
def inDomain : Path → Prop
  | []   => False
  | [f]  => f = .seq
  | _ :: rest => inDomain rest

/-- What the seq locator (R447, `mapDepth 0`) PLUS the map mirror (R449, one map crossing) serve over
    the CURRENT deliverable: targets at map-depth ≤ 1. -/
def reachCurrent (p : Path) : Prop := inDomain p ∧ mapDepth p ≤ 1

/-- **Reach ⊆ domain** — trivially, `reachCurrent` carries `inDomain`. -/
theorem reachCurrent_imp_inDomain {p : Path} (h : reachCurrent p) : inDomain p := h.1

/-- **The depth ladder.**  Three seq windows, all enclosed by `[` (all in the carrier's path-blind
    domain), at map-depths 0, 1, 2.  The seq locator serves depth 0, the map mirror serves depth 1, but
    depth 2 (`[{a:{x:[b]}}]`'s `[b]`) is NOT served by either — a SECOND severance.  So `reachCurrent`
    (seq locator + map mirror over the current deliverable) is STRICTLY below the domain. -/
theorem depth_ladder :
    -- depth 0 `[seq]` (`[[b]]`-style, all-seq path): in domain AND reachable (seq locator).
    (inDomain [Frame.seq] ∧ mapDepth [Frame.seq] = 0 ∧ reachCurrent [Frame.seq])
    -- depth 1 `[map, seq]` (`[{a:[b]}]`'s `[b]`): in domain AND reachable (map mirror).
    ∧ (inDomain [Frame.map, Frame.seq] ∧ mapDepth [Frame.map, Frame.seq] = 1
        ∧ reachCurrent [Frame.map, Frame.seq])
    -- depth 2 `[map, map, seq]` (`[{a:{x:[b]}}]`'s `[b]`): in domain but NOT reachable — the gap.
    ∧ (inDomain [Frame.map, Frame.map, Frame.seq]
        ∧ mapDepth [Frame.map, Frame.map, Frame.seq] = 2
        ∧ ¬ reachCurrent [Frame.map, Frame.map, Frame.seq]) := by
  refine ⟨⟨rfl, rfl, rfl, ?_⟩, ⟨rfl, rfl, rfl, ?_⟩, ⟨rfl, rfl, ?_⟩⟩
  · decide
  · decide
  · rintro ⟨_, h⟩; exact absurd h (by decide)

/-! ## PART 2 — why the bound is structural: the recursion stores a FLAT witness at the map. -/

/-- An opaque flat witness (models `WellBracketed interior`): carries NO recursive structure. -/
opaque Flat : Type

/- The seq-side deliverable (models `RecSeqEntry`/`RecSeqBody`).  `.seq` stores the RECURSIVE interior
   body; `.map` stores only a FLAT witness — the severance, identical to R448.  (Doc comment is plain
   `/- -/`, not `/-- -/`: a doc comment cannot attach to a `mutual` keyword — the Reflection 234 gotcha.) -/
mutual
inductive SEntry where
  | scalar
  | seq (body : SBody)    -- RecSeqEntry.seq: recursive `RecSeqBody`
  | map (flat : Flat)     -- RecSeqEntry.map: flat `WellBracketed` — SEVERED
inductive SBody where
  | one  (e : SEntry)
  | cons (e : SEntry) (rest : SBody)
end

/-- The map-side deliverable's pair (models `RecMapPair`): key and value each re-enter the SEQ side as
    an `SEntry` — so a seq nested in a map VALUE is reachable (the map mirror's one crossing). -/
structure MPair where
  key : SEntry
  value : SEntry

/-- The seq navigator's descend into an entry's body: into `.seq`'s recursive body, STUCK at `.map`
    (no recursive witness) — the FIRST severance (seq spine dead-ends at a map). -/
def descendSeqEntry : SEntry → Option SBody
  | .scalar  => none
  | .seq b   => some b
  | .map _   => none

/-- The map navigator's descend into a pair's VALUE entry: it reaches the value `SEntry`, then can take
    `.seq`'s body — but is STUCK at `.map` for exactly the same reason (the value entry stores only a
    flat witness).  The SECOND severance is the FIRST one again, one level down. -/
def descendMapValue : MPair → Option SBody
  | ⟨_, .scalar⟩ => none
  | ⟨_, .seq b⟩  => some b   -- map VALUE is a seq ⇒ reachable (map-depth 1, M1/M2)
  | ⟨_, .map _⟩  => none     -- map VALUE is a map ⇒ STUCK (map-depth 2, M3)

/-- **The two severances are ONE severance.**  Both navigators dead-end at a `.map` SEntry — the seq
    navigator on a map-headed entry, the map navigator on a map-valued pair — because `SEntry.map`
    stores only a `Flat` witness in both.  So each navigator crosses at most one map boundary. -/
theorem both_navigators_sever_at_map (f g : Flat) (b : SBody) :
    descendSeqEntry (.map f) = none           -- seq navigator stuck at a map entry (depth-1 severance)
    ∧ descendMapValue ⟨.scalar, .map g⟩ = none -- map navigator stuck at a map value (depth-2 severance)
    ∧ descendMapValue ⟨.scalar, .seq b⟩ = some b := -- but a SEQ value IS reachable (depth-1, M1/M2)
  ⟨rfl, rfl, rfl⟩

/-! ### The FIX: store a RECURSIVE witness at the map, so the navigators mutually recurse to any depth. -/

/- The FULLY-RECURSIVE deliverable (the deferred refinement): `.map` stores a recursive `RMBody`
   instead of a `Flat` witness, so the map interior's structure is recovered.  (Plain `/- -/` — see the
   `mutual` doc-comment gotcha above.) -/
mutual
inductive RSEntry where
  | scalar
  | seq (body : RSBody)    -- recursive seq interior
  | map (mbody : RMBody)   -- recursive MAP interior — the fix (no longer flat)
inductive RSBody where
  | one  (e : RSEntry)
  | cons (e : RSEntry) (rest : RSBody)
inductive RMBody where
  | one  (key : RSEntry) (value : RSEntry)
  | cons (key : RSEntry) (value : RSEntry) (rest : RMBody)
end

/-- The fixed map navigator descends a `.map` value into its recursive body — no severance.  Combined
    with the seq descend, the two navigators MUTUALLY recurse through any seq/map nesting. -/
def descendRMapValue : RSEntry → Option RMBody
  | .scalar  => none
  | .seq _   => none
  | .map mb  => some mb   -- the foreign-nested structure is RECOVERED — descend continues

/-- **The fix recovers the foreign-nested structure.**  Where the current deliverable severs
    (`descendMapValue ⟨_, .map _⟩ = none`), the recursive variant descends
    (`descendRMapValue (.map mb) = some mb`) — so a mutual seq/map navigator reaches ANY map-depth. -/
theorem recursive_map_recovers (mb : RMBody) :
    descendRMapValue (.map mb) = some mb :=
  rfl

/-- The finding in one proposition: (PART 1) the current reach is `mapDepth ≤ 1` but the domain admits
    any depth (depth-2 witness in domain, not reachable); (PART 2) the bound is structural — both
    navigators sever at the flat `SEntry.map` (so each crosses ≤ 1 map), and only storing a recursive
    witness (`RSEntry.map`) recovers the foreign-nested structure. -/
theorem r449_finding (f g : Flat) (b : SBody) (mb : RMBody) :
    (inDomain [Frame.map, Frame.map, Frame.seq]
      ∧ ¬ reachCurrent [Frame.map, Frame.map, Frame.seq])  -- domain wider than reach at depth 2
    ∧ (descendSeqEntry (.map f) = none)                    -- seq navigator severs at a map
    ∧ (descendMapValue ⟨.scalar, .map g⟩ = none)           -- map navigator severs at a nested map
    ∧ (descendMapValue ⟨.scalar, .seq b⟩ = some b)         -- but a map's SEQ value IS reachable
    ∧ (descendRMapValue (.map mb) = some mb) :=             -- the recursive fix recovers it
  ⟨⟨rfl, by rintro ⟨_, h⟩; exact absurd h (by decide)⟩, rfl, rfl, rfl, rfl⟩

end Tests.Reflections.SeveranceRecursesByNestingDepth
