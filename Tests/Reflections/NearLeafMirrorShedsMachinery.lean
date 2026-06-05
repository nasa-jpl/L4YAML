/-!
# Reflection 293 — a near-leaf mirror SHEDS the recursion machinery its recursive sibling needed

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`recseqentry_mapbracket_oracle`: the `{ … }` head-dispatch oracle is the mirror of the recursive
`[ … ]` oracle (`recseqentry_seqbracket_oracle`), and the surprise is its DIRECTION.  This mirror
SHRINKS — the map oracle's signature is strictly SMALLER than the seq one, dropping both the
inductive hypothesis and the descend/non-emptiness guard.

The reason is the R244 storage fact read from the producer's side.  `RecSeqEntry.seq` stores a
recursive `RecSeqBody interior`, so its oracle must run the `windowWidth_strongRecOn` IH on the
strictly-narrower interior — which needs the descend guard reconstructed there, which needs interior
non-emptiness.  `RecSeqEntry.map` stores only `WellBracketed interior` (a NEAR-leaf — the nested
map's key/value recursion is deferred to a separate axis).  `WellBracketed` is flat prefix-balance
combinatorics: no IH, no descend, and not even non-emptiness (`WellBracketed []` of an empty `{ }`
is just as valid).

The lesson (R293): when a storage decision makes one axis a near-leaf and the other recursive, the
asymmetry has OPPOSITE signs on the two sides of the boundary.  On the CONSUMER side the near-leaf
is the complication (its body bottoms out at the flat fact, so the consumer cannot descend through
it uniformly and carries extra primitives).  On the PRODUCER side the same near-leaf is the
SIMPLIFICATION — its deliverable is flat-decidable, so the producer needs none of the recursion
machinery its recursive sibling required.  Mirror a near-leaf oracle by DELETING hypotheses, not
adding them.

* POSITIVE — `seq_oracle` (recursive) needs both the IH and non-emptiness to produce `RBody`;
  `map_oracle` (near-leaf) produces `WB` from balance facts ALONE, with both hypotheses gone, and
  `map_fires_empty` shows it fires on the DEGENERATE empty interior.
* NEGATIVE — `not_rbody_empty` shows the recursive deliverable is UNINHABITED on `[]`, so the seq
  oracle's non-emptiness hypothesis is load-bearing; the near-leaf needs no counterpart precisely
  because `WB []` holds.  The empty case is a HOLE for the recursive sibling, FREE for the near-leaf
  — the storage asymmetry's two opposite signs.  `not_wb_opn` confirms `WB` is not vacuous (an
  unbalanced interior fails it).
-/

namespace Tests.Reflections.NearLeafMirrorShedsMachinery

set_option autoImplicit false

/-- Toy token stream: openers / closers carry bracket delta; values are neutral. -/
inductive Tok | opn | cls | val
  deriving DecidableEq, Repr

/-- Bracket delta (toy of `flowBracketDelta`). -/
def delta : Tok → Int
  | .opn => 1
  | .cls => -1
  | _    => 0

/-- Prefix balance of a whole list (toy of `pbalance`). -/
def pbal (l : List Tok) : Int :=
  l.foldl (fun s t => s + delta t) 0

-- Sanity: an opener raises the balance, a value leaves it.
#guard pbal [Tok.opn] == 1
#guard pbal [Tok.val] == 0

/-! ## The two deliverables — one recursive, one near-leaf

`RBody` is the RECURSIVE deliverable (toy of `RecSeqBody`): a non-empty chain of neutral tokens,
inhabited only by its constructors, so it bottoms out by recursion and is UNINHABITED on `[]`.
`WB` is the NEAR-LEAF deliverable (toy of `WellBracketed`): flat prefix-balance, decidable from
balance facts alone, and inhabited on `[]`. -/

/-- The recursive deliverable — built only by its constructors; never represents the empty list. -/
inductive RBody : List Tok → Prop where
  | one  (t : Tok) (h : delta t = 0) : RBody [t]
  | more (t : Tok) (rest : List Tok) (h : delta t = 0) (hr : RBody rest) : RBody (t :: rest)

/-- The near-leaf deliverable — balanced, every prefix balance `≥ 0`. Pure flat combinatorics. -/
def WB (l : List Tok) : Prop :=
  pbal l = 0 ∧ ∀ i, pbal (l.take i) ≥ 0

/-! ## POSITIVE — the recursive oracle needs machinery; the near-leaf mirror sheds it

`seq_oracle` is discharged ONLY by the IH (the deliverable bottoms out by recursion) AND by
non-emptiness (`RBody []` is uninhabited) — both load-bearing.  `map_oracle` produces the same-shape
deliverable for the mirror branch from balance facts ALONE: the IH and the non-emptiness guard are
GONE from its signature. -/

/-- SEQ oracle (recursive sibling): produces `RBody`, needs the IH and the non-emptiness guard. -/
theorem seq_oracle (interior : List Tok)
    (h_ne : interior ≠ [])
    (ih : interior ≠ [] → RBody interior) :
    RBody interior :=
  ih h_ne

/-- MAP oracle (near-leaf mirror): produces `WB` from balance facts ALONE — no IH, no
    non-emptiness.  The seq oracle's two hypotheses are dropped, not mirrored. -/
theorem map_oracle (interior : List Tok)
    (h_bal : pbal interior = 0)
    (h_floor : ∀ i, pbal (interior.take i) ≥ 0) :
    WB interior :=
  ⟨h_bal, h_floor⟩

/-- A one-token neutral interior. -/
def leaf : List Tok := [Tok.val]

/-- Its prefix balances are all `≥ 0` (the floor the near-leaf oracle consumes). -/
theorem leaf_floor : ∀ i, pbal (leaf.take i) ≥ 0 := by
  intro i
  cases i with
  | zero => decide
  | succ n => rw [leaf, List.take_succ_cons, List.take_nil]; decide

/-- The recursive oracle fires on `leaf` — but only by being handed the IH and non-emptiness. -/
theorem seq_fires : RBody leaf :=
  seq_oracle leaf (by decide) (fun _ => RBody.one Tok.val (by decide))

/-- The near-leaf mirror fires on `leaf` from balance facts alone. -/
theorem map_fires : WB leaf :=
  map_oracle leaf (by decide) leaf_floor

/-- …and it ALSO fires on the DEGENERATE empty interior — no IH, no non-emptiness available, yet
    `WB []` holds.  The near-leaf needs strictly less than its recursive sibling. -/
theorem map_fires_empty : WB [] :=
  map_oracle [] (by decide) (by intro i; rw [List.take_nil]; decide)

/-! ## NEGATIVE — the empty case is a HOLE for the recursive sibling, FREE for the near-leaf

`not_rbody_empty` shows the recursive deliverable cannot represent `[]` at all: neither constructor
produces the empty list, so the seq oracle's non-emptiness hypothesis is genuinely load-bearing.
The near-leaf needs no such guard precisely because `WB []` holds (`map_fires_empty`).  This is the
storage asymmetry's two opposite signs on one degenerate input. -/

/-- The recursive deliverable is UNINHABITED on the empty interior. -/
theorem not_rbody_empty : ¬ RBody [] := by
  intro h; cases h

/-- `WB` is not vacuous: an unbalanced interior fails it (so the near-leaf oracle's `h_bal` is real
    content, not a free pass — it is merely IH-free, not hypothesis-free). -/
theorem not_wb_opn : ¬ WB [Tok.opn] := by
  intro h; exact absurd h.1 (by decide)

end Tests.Reflections.NearLeafMirrorShedsMachinery
