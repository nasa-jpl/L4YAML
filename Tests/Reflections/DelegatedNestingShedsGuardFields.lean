/-! # Reflection 521 — delegated nesting sheds guard fields (the map body content guard)

The L4YAML carrier-free recursion threads a per-window *content-navigation guard* through its width
recursion: the seq driver `seqWindowRecSeqBody_seq_general` threads `FlowBodyContentDeepSeq`, and the
(still-to-be-wired) map driver `mapWindowRecMapBody_map_general` threads the new
`FlowBodyContentDeepMap` (R521, `NonemptyStructure.lean`).  The reflection this demo pins:

* **A deliverable whose recursion DELEGATES nesting needs a STRICTLY SIMPLER threading guard than one
  that INLINES nesting.**  Read the delegation off the inductive.  `RecSeqEntry` *inlines* the seq item
  shapes (`scalar` / `seq` / `mapRec` constructors), so the seq recursion DESCENDS into every nested
  `[ … ]` itself — its guard `FlowBodyContentDeepSeq` carries THREE fields (`headContentStart`,
  `openerContentStart`, `feContentStart`) and supports BOTH a `descend` and an `advance` edge, because
  `openerContentStart` is exactly the fact the descend edge reads to seat a nested child's head.
  `RecMapBody → RecMapPair → RecSeqEntry` *delegates*: the key/value blocks are `RecSeqEntry`s navigated
  by the seq-entry oracles (`recmapentry_pair_located`), and the map body itself only ADVANCES past
  depth-`0` `.flowEntry` separators by BALANCE — it never descends.  So `FlowBodyContentDeepMap` SHEDS
  the opener field and the descend edge: TWO fields (`headKey`, `feKey`), ONE edge (`advance`).  The
  delegation asymmetry in the inductive propagates verbatim to the guard.

* **Dual-axis separator guards mirror by swapping the discriminator to the OTHER axis's
  separator-successor.**  `FlowBodyContentDeepSeq.feContentStart` reads
  `f k = sep → f (k+1) ≠ key → isContent (f (k+1))` — a seq `,` is followed by content, and the `≠ key`
  premise excludes map-internal `,`s (which are followed by a key).  `FlowBodyContentDeepMap.feKey` is
  the exact dual: `f k = sep → ¬ isContent (f (k+1)) → f (k+1) = key` — a map `,` is followed by a key,
  and the `¬ content` premise excludes seq-internal `,`s (which are followed by content).  The
  discriminator is the OTHER axis's separator-successor in each case (`key` for seq, `content` for map);
  everything else is a verbatim mirror.

This demo (self-contained core Lean, no imports) models a token stream as a function `f : Nat → Tok`,
defines both guards, proves both advance edges — exhibiting that the map advance is strictly simpler
(the new head is the supplied successor, no parent-field read; no opener field to restrict; no descend
edge at all) — and inhabits the map guard NON-vacuously on a two-pair `{a: b, c: d}` layout, firing
`feKey` at the depth-`0` separator.  `demo` carries `[propext, Quot.sound]` — matching the real
`flowBodyContentDeepMap_advance`, and crucially NO `sorryAx`: the guard, its edge, and its root probe
never touch the `scanFiltered_emitMap_nonempty_structure` structure lemma that taints the rest of the
map family.
-/

namespace DelegatedNestingShedsGuardFields

set_option autoImplicit false

/-- Toy token alphabet: scalars and the two openers are "content"; `.key`/`.value` are markers, `.sep`
    is the depth-`0` `.flowEntry`. -/
inductive Tok where
  | scalar | key | value | sep | seqOpen | mapOpen | seqClose | mapClose
deriving DecidableEq

/-- Content-start tokens (mirror of `isFlowContentStart`): a scalar or either opener. -/
def isContent : Tok → Prop
  | .scalar => True
  | .seqOpen => True
  | .mapOpen => True
  | _ => False

/-- **The SEQ body guard** (toy of `FlowBodyContentDeepSeq`): THREE fields — head is content, every
    interior opener is followed by content, every interior `.sep` whose successor is not a `.key` is
    followed by content.  The `openerContentStart` field is what the (omitted here) descend edge reads. -/
structure SeqGuard (f : Nat → Tok) (lo hi : Nat) : Prop where
  headContent : isContent (f lo)
  openerContent : ∀ k, lo ≤ k → k + 1 < hi → f k = .seqOpen → f (k + 1) ≠ .seqClose →
    isContent (f (k + 1))
  feContent : ∀ k, lo ≤ k → k + 1 < hi → f k = .sep → f (k + 1) ≠ .key → isContent (f (k + 1))

/-- **The MAP body guard** (toy of `FlowBodyContentDeepMap`): TWO fields — head is a `.key`, every
    interior `.sep` whose successor is not content is followed by a `.key`.  No opener field: the map
    body delegates nesting to the (toy) seq-entry oracles, so it never descends. -/
structure MapGuard (f : Nat → Tok) (lo hi : Nat) : Prop where
  headKey : f lo = .key
  feKey : ∀ k, lo ≤ k → k + 1 < hi → f k = .sep → ¬ isContent (f (k + 1)) → f (k + 1) = .key

/-- **The SEQ advance edge** (toy of `flowBodyContentDeepSeq_advance`).  The child head is read from the
    PARENT's `feContent` at the separator `m` (needs the `≠ key` premise); the opener/sep fields restrict
    to `[m+1, hi)`.  Note: the parent field read is what couples the seq advance to the guard's shape. -/
theorem seqGuard_advance (f : Nat → Tok) (lo m hi : Nat)
    (h : SeqGuard f lo hi) (h_lo_m : lo ≤ m) (h_sep : f m = .sep)
    (h_ne : f (m + 1) ≠ .key) (h_hi : m + 1 < hi) :
    SeqGuard f (m + 1) hi := by
  obtain ⟨_h_head, h_op, h_fe⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · -- child head: the parent's `feContent` at `m` (a PARENT-FIELD read).
    exact h_fe m h_lo_m h_hi h_sep h_ne
  · intro k hk1 hk2 hopen hclose; exact h_op k (by omega) (by omega) hopen hclose
  · intro k hk1 hk2 hfe hkey; exact h_fe k (by omega) (by omega) hfe hkey

/-- **The MAP advance edge** (toy of `flowBodyContentDeepMap_advance`).  STRICTLY SIMPLER: the child head
    is the supplied successor `h_key` DIRECTLY (no parent-field read), there is no opener field to
    restrict, and only `feKey` threads to `[m+1, hi)`.  The whole restriction interface is this one edge;
    there is no map descend edge. -/
theorem mapGuard_advance (f : Nat → Tok) (lo m hi : Nat)
    (h : MapGuard f lo hi) (h_lo_m : lo ≤ m)
    (h_key : f (m + 1) = .key) (_h_hi : m + 1 < hi) :
    MapGuard f (m + 1) hi := by
  obtain ⟨_h_head, h_fe⟩ := h
  refine ⟨h_key, ?_⟩
  intro k hk1 hk2 hfe hncs; exact h_fe k (by omega) (by omega) hfe hncs

/-- A concrete two-pair layout `{a: b, c: d}` over `[2, 11)`: the depth-`0` `.sep` sits at index 6,
    followed by the second pair's `.key` at 7. -/
def sampleF : Nat → Tok
  | 2 => .key | 3 => .scalar | 4 => .value | 5 => .scalar
  | 6 => .sep | 7 => .key | 8 => .scalar | 9 => .value | 10 => .scalar
  | _ => .mapClose

/-- **The map guard holds NON-vacuously** at the root window `[2, 11)`: `headKey` fires, and `feKey`
    fires at the depth-`0` separator `k = 6` (`sampleF 6 = .sep`, `sampleF 7 = .key`). -/
theorem sample_mapGuard : MapGuard sampleF 2 11 := by
  refine ⟨rfl, ?_⟩
  intro k hk1 hk2 hsep _hncs
  have hk : k = 2 ∨ k = 3 ∨ k = 4 ∨ k = 5 ∨ k = 6 ∨ k = 7 ∨ k = 8 ∨ k = 9 := by omega
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first
    | rfl                                   -- k = 6: the conclusion `sampleF 7 = .key`
    | exact absurd hsep (by decide)         -- every other k: `sampleF k ≠ .sep`

/-- **The demo deliverable**: advancing the map guard past the depth-`0` separator at 6 to the window
    `[7, 11)` of the second pair — the single structural move the map body recursion makes. -/
theorem demo : MapGuard sampleF 7 11 :=
  mapGuard_advance sampleF 2 6 11 sample_mapGuard (by omega) rfl (by omega)

end DelegatedNestingShedsGuardFields

-- Axiom audit (machine-checked: `#guard_msgs` pins the profile and fails the build if it ever drifts).
-- `[propext, Quot.sound]` — faithfully matches the real `flowBodyContentDeepMap_advance`, and crucially
-- NO `sorryAx`: the map body guard, its advance edge, and its root probe never touch the
-- `scanFiltered_emitMap_nonempty_structure` structure lemma that taints the rest of the map context
-- family ([[ref-mirror-inherits-dependency-axioms]] R518 — taint tracks the dependency, not the axis).
/-- info: 'DelegatedNestingShedsGuardFields.demo' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms DelegatedNestingShedsGuardFields.demo
