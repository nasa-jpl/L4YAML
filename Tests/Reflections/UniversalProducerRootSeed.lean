/-
# Reflections 258 + 259 — a universal producer's first brick is its ROOT SEED: the positional packaging of its one already-available instance, as a faithful mirror of the flat-deliverable characterization (R258); and that seed mirrors verbatim across a symmetric collection axis, the only deltas the feed's per-item hypotheses (R259)

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflections 258 + 259 (and memory `ref-universal-producer-root-seed-first`).

**The principle.** Once the *consumer* of a not-yet-written universal producer is folded to one
lemma keyed on the producer's contract (R257), the producer's **first landable brick** is not the
recursion — it is the recursion's **root seed**: the *one distinguished instance* of the universal
that some existing infrastructure (the emit feed) already delivers, packaged into the *positional*
form the universal is phrased in. You build it as a **faithful mirror of the existing flat-deliverable
characterization**, swapping the flat payload for the recursive one — the positional `drop` step is
*verbatim*; only the payload conjunct differs. It costs almost nothing, is verified-but-unconsumed,
and pins the recursion's **base case** before the navigation engine exists.

In the L4YAML Phase-J locate this is `emitList_body_recseqbody`: the universal producer
`flowSubrangesOk_of_window_producers` owes `∀ lo hi, <guards> → RecSeqBody ((take hi).drop lo)`; its
root instance is the outer window `[2, size-2)` (the whole body interior), where the deliverable is
just the top-level `RecSeqBody` the emit feed `emitList_scans_recseqbody` already produces. The seed
is the `RecSeqBody` analog of the flat `emitList_body_filtered_characterization`, restating the emit
feed's abstract `block` positionally as `RecSeqBody (drop old_sz)` via the same `h_drop`.

**The toy.** An "emit feed" returns a recursive deliverable `Rec block` together with the append
equation `full = prefix ++ block`. The *flat* characterization `charFlat` restates the flat
projection `Flat` positionally as `Flat (full.drop prefix.length)`; the **R258 seed** `charRec` is its
faithful mirror — *same* `subst`/`drop_pre` body, payload swapped to `Rec`. `root_instance` shows the
seed *is* the `lo = prefix.length` (root/outer-window) instance of the universal `UnivRec`; the other
instances need the navigation recursion (deferred — not proved here).

Positive: `good = [OB, A, CB]` is a nested entry, `Rec good` holds, and with a length-1 prefix the
seed recovers it by `drop 1`. Negative: `empty = []` has no `Rec` (via the `Rec ⟹ Flat` projection —
the recursive deliverable can never produce an empty block), so the seed never fires there.
-/

namespace Tests.Reflections.UniversalProducerRootSeed

inductive Tok | A | OB | CB
  deriving DecidableEq, Inhabited, Repr

/-- The recursive deliverable the emit feed produces (toy of `RecSeqBody`): a content leaf or a
    bracket-nested recursive interior. -/
inductive Rec : List Tok → Prop where
  | a : Rec [Tok.A]
  | nest (i : List Tok) (h : Rec i) : Rec ([Tok.OB] ++ i ++ [Tok.CB])

/-- The flat projection the flat characterization delivers (toy of the `SafeBody`/non-empty facts). -/
def Flat (l : List Tok) : Prop := l ≠ []

/-- `Rec` projects to `Flat` (R244 stored-vs-projected): a recursive deliverable is never empty. -/
theorem rec_to_flat {l : List Tok} (h : Rec l) : Flat l := by
  cases h with
  | a => simp [Flat]
  | nest i hi => simp [Flat]

/-! ### The shared positional step — the `h_drop` both characterizations use verbatim -/

/-- Dropping the prefix length off `prefix ++ block` recovers `block` (toy of `h_drop`:
    `block_eq` + `List.drop_append_of_le_length` + `List.drop_length` + `List.nil_append`). -/
theorem drop_pre (pre block : List Tok) : (pre ++ block).drop pre.length = block := by
  rw [List.drop_append_of_le_length (Nat.le_refl _), List.drop_length, List.nil_append]

/-! ### The two characterizations — faithful mirrors, payload swapped -/

/-- **Flat characterization** (toy of `emitList_body_filtered_characterization`): restate the emit
    feed's flat payload positionally. -/
theorem charFlat (pre block full : List Tok) (h_eq : full = pre ++ block) (h : Flat block) :
    Flat (full.drop pre.length) := by
  subst h_eq; rw [drop_pre]; exact h

/-- **The R258 root seed** (toy of `emitList_body_recseqbody`): the *faithful mirror* of `charFlat` —
    identical `subst`/`drop_pre` body, the flat payload `Flat` swapped for the recursive payload
    `Rec`.  Restates the emit feed's abstract `Rec block` positionally as `Rec (full.drop pre.length)`. -/
theorem charRec (pre block full : List Tok) (h_eq : full = pre ++ block) (h : Rec block) :
    Rec (full.drop pre.length) := by
  subst h_eq; rw [drop_pre]; exact h

/-! ### The seed is the universal's ROOT instance (the rest needs navigation, deferred) -/

/-- The universal the locate recursion owes (toy): `Rec` of every suffix window. -/
def UnivRec (full : List Tok) : Prop := ∀ lo, lo ≤ full.length → Rec (full.drop lo)

/-- The seed discharges exactly the **root instance** `lo = pre.length` (the outer window) of
    `UnivRec (pre ++ block)`.  The other instances need the navigation recursion — NOT proved here,
    so `UnivRec` itself is left open: this brick is only the base case. -/
theorem root_instance (pre block : List Tok) (h : Rec block) :
    Rec ((pre ++ block).drop pre.length) :=
  charRec pre block _ rfl h

/-! ### Positive witnesses — `good = [OB, A, CB]` (a nested entry) -/

def good : List Tok := [Tok.OB, Tok.A, Tok.CB]

theorem rec_good : Rec good := Rec.nest [Tok.A] Rec.a
theorem flat_good : Flat good := by simp [Flat, good]

-- with a length-1 prefix the positional packaging recovers the body by `drop 1`:
#guard ([Tok.OB] ++ good).drop 1 == good
#guard good.length == 3

/-- the seed fires at the root window (prefix `[OB]`, `old_sz = 1`). -/
theorem seed_root : Rec (([Tok.OB] ++ good).drop 1) :=
  charRec [Tok.OB] good _ rfl rec_good

/-- the flat mirror lands the *same* positional window — same `drop_pre`, different payload. -/
theorem flat_root : Flat (([Tok.OB] ++ good).drop 1) :=
  charFlat [Tok.OB] good _ rfl flat_good

/-! ### Negative witness — `empty = []` (the recursive deliverable can never be empty) -/

def empty : List Tok := []

#guard empty.length == 0
#guard !(good == empty)

/-- no `Rec` at the empty block — via the `Rec ⟹ Flat` projection, so the seed never fires there. -/
theorem not_rec_empty : ¬ Rec empty := by
  intro h; exact (rec_to_flat h) rfl

/-! ### Map-side mirror (Reflection 259) — the seed mirrors verbatim; the *feed* reads more

The map root seed `emitPairList_body_recmapbody` is the symmetric mirror of the seq seed across the
seq→map collection axis (exactly as the consumer-side R255→R256 boundary joint mirrored its seq
twin).  Its proof body is **verbatim** the seq seed — the positional packaging step (`drop` →
`Deliverable (window)`) is bracket- and collection-agnostic.  The *only* deltas are the **feed's**
inputs/outputs — the R246 stored-vs-projected asymmetry one tier up, at the seed's hypothesis count:
the map feed reads a SECOND per-item (key) hypothesis and an extra `simpleKeyAllowed` precondition
the seq feed lacks, and delivers an extra `3 ≤ n` floor (R250) the seed destructures but never uses. -/

/-- The map deliverable (toy of `RecMapBody`): a parallel collection axis — structurally a copy of
    `Rec`, a *different* collection with its own constructors. -/
inductive RecMap : List Tok → Prop where
  | a : RecMap [Tok.A]
  | nest (i : List Tok) (h : RecMap i) : RecMap ([Tok.OB] ++ i ++ [Tok.CB])

/-- `RecMap` projects to `Flat` (the map twin of `rec_to_flat`). -/
theorem recmap_to_flat {l : List Tok} (h : RecMap l) : Flat l := by
  cases h with
  | a => simp [Flat]
  | nest i hi => simp [Flat]

/-- **The R259 map root seed** (toy of `emitPairList_body_recmapbody`): the *verbatim* mirror of
    `charRec` — identical `subst`/`drop_pre` body, the payload `Rec` swapped for `RecMap`.  The
    positional packaging step is collection-agnostic, so the map seed copies the seq seed exactly. -/
theorem charMap (pre block full : List Tok) (h_eq : full = pre ++ block) (h : RecMap block) :
    RecMap (full.drop pre.length) := by
  subst h_eq; rw [drop_pre]; exact h

/-- toy seq emit feed (of `emitList_scans_recseqbody`): from the items, deliver `Rec block`. -/
structure SeqFeed (block : List Tok) : Prop where
  recv : Rec block

/-- toy map emit feed (of `emitPairList_scans_recmapbody`): the R246 delta — an extra precondition
    `ska` (toy of `simpleKeyAllowed = true`) AND an extra `floor` (toy of the `3 ≤ n` map floor,
    R250), NEITHER present on `SeqFeed`.  A pair carries a key slot the seq item has no analogue for. -/
structure MapFeed (block : List Tok) : Prop where
  ska : True
  recm : RecMap block
  floor : 3 ≤ block.length

/-- the seq seed wraps `SeqFeed` positionally (toy of `emitList_body_recseqbody`). -/
theorem seedSeq (pre block full : List Tok) (h_eq : full = pre ++ block) (f : SeqFeed block) :
    Rec (full.drop pre.length) := charRec pre block full h_eq f.recv

/-- the map seed wraps `MapFeed` by the SAME positional `charMap` — `ska`/`floor` are destructured
    but UNUSED (toy of `emitPairList_body_recmapbody` ignoring `_h_n3`). -/
theorem seedMap (pre block full : List Tok) (h_eq : full = pre ++ block) (f : MapFeed block) :
    RecMap (full.drop pre.length) := charMap pre block full h_eq f.recm

/-! ### Map-side witnesses -/

theorem recmap_good : RecMap good := RecMap.nest [Tok.A] RecMap.a

/-- the map feed is inhabited at `good` — length 3 clears the floor. -/
def mapfeed_good : MapFeed good := ⟨trivial, recmap_good, by decide⟩

/-- the map seed fires at the root window (prefix `[OB]`) — the SAME positional wrap as the seq seed. -/
theorem seed_map_root : RecMap (([Tok.OB] ++ good).drop 1) :=
  seedMap [Tok.OB] good _ rfl mapfeed_good

-- the seq feed IS inhabited at the singleton `[A]` (no floor) …
def seqfeed_singleton : SeqFeed [Tok.A] := ⟨Rec.a⟩

-- … but the map feed is NOT — the `3 ≤ length` floor (R250) excludes it; the seq side has no floor:
#guard ([Tok.A] : List Tok).length == 1
theorem no_mapfeed_singleton : ¬ MapFeed [Tok.A] := fun f => absurd f.floor (by decide)

/-- no `RecMap` at the empty block either — via the `RecMap ⟹ Flat` projection. -/
theorem not_recmap_empty : ¬ RecMap empty := by
  intro h; exact (recmap_to_flat h) rfl

end Tests.Reflections.UniversalProducerRootSeed
