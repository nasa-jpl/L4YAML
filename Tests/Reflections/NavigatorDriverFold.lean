/-! # Reflection 510 — fold the width-recursion combinator + assemble selector into a driver
        whose residual is exactly two named obligations (`locate` + `descend_tail`)

The seq navigator's structural moves are all landed — DESCEND (`recseqbody_window_of_located_entry`),
ADVANCE (`recseqbody_cons_window`), TERMINATE (`recseqbody_single_window`), and their grammar-free
ADVANCE/TERMINATE selector `recseqbody_window_assemble` — and the abstract width-recursion plumbing is
carved off as `windowWidth_strongRecOn`. R510 (`recseqbody_navigator_driver`) is the STITCH between
them: it instantiates the combinator at `P := RecSeqBody ((take hi).drop lo)`, bakes in the
`recseqbody_window_assemble` consumer, and re-expresses the per-window step as the navigator's
*contract* — so the whole seq navigator reduces to **exactly two named obligations**:

* `locate` — the per-window first-entry classify (locate the first entry's extent `m`, the marker
  `m = hi ∨ tokens[m] = .flowEntry`, the entry `RecSeqEntry [lo, m)`), handed the recursion's own
  width-oracle.  This is *nearly* `recseqentry_window_dispatch_seq` already; the only gap is adapting
  its richer `h_ih` premise-list to the combinator's plain `G`-keyed oracle — which is where the
  concrete guard `G` is finally *pinned down*.
* `descend_tail` — the guard `G` descends from `[lo, hi)` to the SUFFIX `[m+1, hi)` past the located
  separator.  The genuine remaining analytical brick (the guard-threading skeleton); the producer's
  GIFT and the consumer's DEBT.

The driver is AGNOSTIC to `G`: leaving it abstract makes visible that the hard guard-reconciliation
(matching the dispatch's `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ …` interface against the
combinator's oracle) reduces to `locate` + `descend_tail` and nothing else.  This is
`fold-consumer-chain-to-producer-contract` at the *recursion-driver* layer — the dual of
`windowWidth_strongRecOn`'s `consumer-joint-before-producer`: where the combinator pinned the
per-window step's IH *interface*, this driver pins the navigator's per-window *contract*.

This demo (self-contained core Lean, no imports) models the architecture over a list-segment toy: a
body = single-token entries separated by single `SEP`s.  It exhibits the three layers literally —

* `lenRec` — the generic width(=length)-recursion combinator (mirror of `windowWidth_strongRecOn`);
* `navigatorDriver` — THE FOLD: combinator + the `Body` constructors (`assemble`/`terminate`, the
  ADVANCE/TERMINATE selector) reduced to the two-obligation contract (`locate`, `descend_tail`);
* a concrete guard `Good`, with both obligations DISCHARGED (`good_locate`, `good_descend_tail`) and a
  RUN (`run`) actually producing a `Body [5, SEP, 7]` through the driver.

The soundness subtlety the demo isolates lives in `good_descend_tail`: it is stated for an ARBITRARY
split `e`, yet is true only because the guard `Good` forces every explicit `SEP` to land on a
separator slot — a split DEEP inside (`e = a :: SEP :: e''`) is discharged by RECURSION on the `Good`
derivation (the IH), mirroring exactly why the real `descend_tail` needs the located-separator
(`least`) clause / an inductive guard rather than an arbitrary positional split.

Axioms: `run` and `demo` depend on `[propext, Quot.sound]` only — no `sorryAx`, no `Classical.choice`
(the real `recseqbody_navigator_driver` additionally carries `Classical.choice`, inherited verbatim
from the `recseqbody_window_assemble` segment-split plumbing it reuses; the toy assemble is the bare
constructors, so it sheds that).
-/

namespace NavigatorDriverFold

/-- The separator marker (mirrors a depth-`0` `.flowEntry`). Everything else is a "content" token. -/
def SEP : Nat := 0

-- ── The deliverable: a body = one-or-more single-token entries separated by single SEPs. ──

/-- A one-token entry (mirrors `RecSeqEntry`; here trivially a single content token `≠ SEP`). -/
inductive EntryTok : List Nat → Prop where
  | mk (a : Nat) (h : a ≠ SEP) : EntryTok [a]

/-- The recursive body deliverable (mirrors `RecSeqBody`): a lone entry (`single`, the TERMINATE
    constructor) or an entry · separator · rest (`cons`, the ADVANCE constructor). -/
inductive Body : List Nat → Prop where
  | single (e : List Nat) (h_e : EntryTok e) : Body e
  | cons (e rest : List Nat) (h_e : EntryTok e) (h_rest : Body rest) :
      Body (e ++ SEP :: rest)

-- ── (1) The width-recursion combinator (mirror of `windowWidth_strongRecOn`). ──

/-- Generic strong recursion on list length: the per-`l` `step` consumes an oracle for every
    strictly-shorter list.  The grammar-free recursion plumbing, carved off once (mirrors
    `windowWidth_strongRecOn`'s span-bound `Nat.strongRecOn`). -/
theorem lenRec {P : List Nat → Prop} (G : List Nat → Prop)
    (step : ∀ l, G l → (∀ l', l'.length < l.length → G l' → P l') → P l) :
    ∀ l, G l → P l := by
  have key : ∀ n, ∀ l, l.length ≤ n → G l → P l := by
    intro n
    induction n using Nat.strongRecOn with
    | ind n IH =>
      intro l h_len h_g
      exact step l h_g (fun l' h_lt h_g' => IH l'.length (by omega) l' (Nat.le_refl _) h_g')
  intro l h_g; exact key l.length l (Nat.le_refl _) h_g

-- ── (2) THE FOLD: the navigator driver (mirror of `recseqbody_navigator_driver`). ──

/-- **The navigator driver fold.**  Folds `lenRec` (the combinator) together with the body
    constructors (`assemble`/`terminate`, the ADVANCE/TERMINATE selector — mirror of
    `recseqbody_window_assemble`) into ONE lemma whose remaining hypotheses are the navigator's
    *contract*: TWO separate named obligations — `locate` (per-list first-entry classify, handed the
    recursion's own oracle) and `descend_tail` (the guard `G` descends to the suffix `rest` past the
    located separator).  The driver is agnostic to `G`; this makes visible that the whole navigator
    reduces to exactly these two. -/
theorem navigatorDriver {EntryP BodyP : List Nat → Prop} (G : List Nat → Prop)
    (assemble : ∀ e rest, EntryP e → BodyP rest → BodyP (e ++ SEP :: rest))
    (terminate : ∀ e, EntryP e → BodyP e)
    (locate : ∀ l, G l → (∀ l', l'.length < l.length → G l' → BodyP l') →
        EntryP l ∨ (∃ e rest, l = e ++ SEP :: rest ∧ EntryP e ∧ rest.length < l.length))
    (descend_tail : ∀ l e rest, G l → l = e ++ SEP :: rest → G rest) :
    ∀ l, G l → BodyP l := by
  refine lenRec G (fun l h_g oracle => ?_)
  rcases locate l h_g oracle with h_term | ⟨e, rest, h_eq, h_e, h_lt⟩
  · -- TERMINATE: the whole list is one entry.
    exact terminate l h_term
  · -- ADVANCE: cons the located entry onto the oracle's tail, with the guard descended by descend_tail.
    have h_grest : G rest := descend_tail l e rest h_g h_eq
    have h_brest : BodyP rest := oracle rest h_lt h_grest
    rw [h_eq]; exact assemble e rest h_e h_brest

-- ── (3) A concrete guard `G := Good` discharging both obligations + a RUN producing a `Body`. ──

/-- A concrete guard: a SEP-alternating non-empty list of content tokens (mirrors the structural
    well-formedness a real `G` would encode). -/
inductive Good : List Nat → Prop where
  | one (a : Nat) (h : a ≠ SEP) : Good [a]
  | more (a : Nat) (rest : List Nat) (h : a ≠ SEP) (h_rest : Good rest) :
      Good (a :: SEP :: rest)

/-- `locate` for `Good`: the first entry is the head token; either the list IS that entry (TERMINATE)
    or it splits as `[a] ++ SEP :: rest` (ADVANCE).  (The oracle is unused — entries are one token.) -/
theorem good_locate (l : List Nat) (h_g : Good l)
    (_oracle : ∀ l', l'.length < l.length → Good l' → Body l') :
    EntryTok l ∨ (∃ e rest, l = e ++ SEP :: rest ∧ EntryTok e ∧ rest.length < l.length) := by
  cases h_g with
  | one a h => exact Or.inl (EntryTok.mk a h)
  | more a rest h _ =>
      exact Or.inr ⟨[a], rest, rfl, EntryTok.mk a h, by simp only [List.length_cons]; omega⟩

/-- `descend_tail` for `Good`.  The SOUNDNESS subtlety: it is stated for an ARBITRARY split `e`, yet is
    true only because `Good` forces every explicit SEP to land on a separator slot — a split deep
    inside (`e = a :: SEP :: e''`) is handled by RECURSION on the `Good` derivation (the IH), mirroring
    why the real `descend_tail` needs the located-separator (`least`) clause / an inductive guard rather
    than an arbitrary positional split. -/
theorem good_descend_tail : ∀ l e rest, Good l → l = e ++ SEP :: rest → Good rest := by
  intro l e rest h_g
  induction h_g generalizing e rest with
  | one a h =>
    intro h_eq
    -- `[a] = e ++ SEP :: rest`: forces `e = []`, then `a = SEP`, contradicting `h`.
    cases e with
    | nil =>
      rw [List.nil_append] at h_eq
      injection h_eq with h_aS _; exact absurd h_aS h
    | cons x e' =>
      rw [List.cons_append] at h_eq
      injection h_eq with _ h_tl; simp at h_tl
  | more a rest' h h_rest' IH =>
    intro h_eq
    -- `a :: SEP :: rest' = e ++ SEP :: rest`.
    cases e with
    | nil =>
      -- `e = []`: forces `a = SEP`, contradicting `h`.
      rw [List.nil_append] at h_eq
      injection h_eq with h_aS _; exact absurd h_aS h
    | cons x e' =>
      rw [List.cons_append] at h_eq
      injection h_eq with _ h_tl
      cases e' with
      | nil =>
        -- `e = [a]`: the canonical first split; `rest = rest'` directly.
        rw [List.nil_append] at h_tl
        injection h_tl with _ h_rr; rw [← h_rr]; exact h_rest'
      | cons y e'' =>
        -- `e = a :: SEP :: e''`: a DEEP split; recurse via the IH on the sub-derivation `Good rest'`.
        rw [List.cons_append] at h_tl
        injection h_tl with _ h_rr; exact IH e'' rest h_rr

/-- The RUN: instantiate the driver with the concrete `Good` and produce a real `Body [5, SEP, 7]`. -/
theorem run : Body [5, SEP, 7] :=
  navigatorDriver Good Body.cons Body.single good_locate good_descend_tail
    [5, SEP, 7] (Good.more 5 [7] (by decide) (Good.one 7 (by decide)))

/-- The demo deliverable: the driver fold is sound (it produces a `Body` from the guard), and its
    residual is EXACTLY the two named obligations `good_locate` + `good_descend_tail` — everything else
    (`lenRec` + the `Body` constructors) is generic, guard-agnostic plumbing. -/
theorem demo :
    Body [5, SEP, 7]
    ∧ (∀ l, Good l → (∀ l', l'.length < l.length → Good l' → Body l') →
        EntryTok l ∨ (∃ e rest, l = e ++ SEP :: rest ∧ EntryTok e ∧ rest.length < l.length))
    ∧ (∀ l e rest, Good l → l = e ++ SEP :: rest → Good rest) :=
  ⟨run, good_locate, good_descend_tail⟩

end NavigatorDriverFold
