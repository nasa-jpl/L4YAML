/-
# Reflection 260 + 261 — the navigation recursion's *descend step* IS a consumer joint's internal computation, truncated: returned as a value instead of consumed (and its symmetric map mirror)

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflections 260 & 261 (and memory `ref-descend-step-is-consumer-joint-truncated`).

**R260 (seq)** is the first part below; **R261 (map mirror)** is the `## The map mirror` section near
the end — the *same* descent transported verbatim across the seq/map axis, the storage asymmetry
surfacing as a *dropped* opener-guard hypothesis (the map entry type has no scalar constructor).

**The principle.** A consumer joint that runs an internal positional computation (peel an opener,
decompose the rest, **descend** one nesting level into a sub-deliverable) and then *consumes* that
sub-deliverable into a terminal result already contains the producer-side **descend primitive** its
dual recursion needs. The recursion cannot reuse the joint: it needs the descended sub-deliverable
*as a value* to hand to its IH one nesting level down, not the consumed terminal. So the descend
step is the *same proof body truncated at the descent* — the peel/decompose verbatim, terminated by
the single-level descent lemma, returning the inner body as the **conclusion** instead of projecting
it onward into the terminal.

In the L4YAML Phase-J locate this is `recseqbody_window_of_located_entry`: the consumer joint
`seqBodyProps_of_located_entry` peels the opener, decomposes the rest, descends via
`RecSeqEntry.seq_interior`, then consumes the descended `RecSeqBody` into `SeqBodyProps` (the
endpoint). The descend primitive runs the *same* peel/decompose/descent but *stops at the
`RecSeqBody`* — which is exactly the navigation recursion's IH input, and is also the `h_seq_rec`
producer deliverable at a window that is itself a top-level nested sequence.

**The toy.** `RecEntry`/`RecBody` (toy of `RecSeqEntry`/`RecSeqBody`): an entry is a scalar `[A]`,
an empty bracket `[OB, CB]`, or a nested bracket `OB :: (interior ++ [CB])` carrying `RecBody
interior`; a body wraps one entry. `seq_interior` is the single-level descent (the shared internal
computation). `recbody_of_entry` is the **descend primitive** — `seq_interior` returning `RecBody
interior ∨ interior = []`. `flat_of_entry` is the **consumer joint** — the *same* `seq_interior`,
then `RecBody.toFlat` projecting the recursive body away into the weaker terminal `Flat` (so the
joint = the descend primitive followed by the consume step; the descend primitive is the joint with
that last step truncated). `descend_twice` shows the descend primitive's `RecBody` output is
recursion-enabling: it descends a doubly-nested window two levels using only the primitive.

Positive: the nested window `[OB, A, CB]` descends to `RecBody [A]`; the joint keeps only `Flat [A]`.
Negative: a scalar located entry `[A]` has no `OB :: (… ++ [CB])` bracket shape, so the descent
never fires there.
-/

namespace Tests.Reflections.DescendStepConsumerJoint

inductive Tok | A | OB | CB
  deriving DecidableEq, Inhabited, Repr

-- toy of `RecSeqBody` / `RecSeqEntry` (mutual; no `/--` doc-comment directly before `mutual`, R234).
mutual
  inductive RecBody : List Tok → Prop where
    | single (e : List Tok) (h : RecEntry e) : RecBody e
  inductive RecEntry : List Tok → Prop where
    | scalar : RecEntry [Tok.A]
    | nestEmpty : RecEntry (Tok.OB :: (([] : List Tok) ++ [Tok.CB]))
    | nest (i : List Tok) (h : RecBody i) : RecEntry (Tok.OB :: (i ++ [Tok.CB]))
end

/-- A body wraps exactly one entry (toy `RecBody` has only the `single` constructor). -/
theorem RecBody.toEntry {l : List Tok} (h : RecBody l) : RecEntry l := by
  cases h with | single e he => exact he

/-! ### The shared positional helper -/

/-- right-cancel a trailing singleton (toy of the project's `append_singleton_inj`). -/
theorem app_single_inj {α} {a b : List α} {c : α} (h : a ++ [c] = b ++ [c]) : a = b := by
  simpa using congrArg List.reverse h

/-! ### The single-level descent — the internal computation both directions share -/

/-- **Single-level descent** (toy of `RecSeqEntry.seq_interior`): a bracket-shaped located entry
    `OB :: (interior ++ [CB])` descends to its interior's recursive body, OR the interior is empty
    (the `[OB, CB]` case the no-`nil` `RecBody` cannot represent — the R233 producer-contract split).
    The `scalar` constructor is ruled out by the `OB` head. -/
theorem seq_interior {e interior : List Tok} (h : RecEntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) :
    RecBody interior ∨ interior = [] := by
  cases h with
  | scalar =>
      exfalso; injection h_eq with h1 _; exact absurd h1 (by decide)
  | nestEmpty =>
      right; injection h_eq with _ h2; exact (app_single_inj h2).symm
  | nest i hi =>
      left; injection h_eq with _ h2; exact (app_single_inj h2) ▸ hi

/-! ### The two directions — same descent, the consumer projects, the producer truncates -/

/-- toy of `SafeBody` — the flat projection the consumer keeps (the recursive structure is gone). -/
def Flat (l : List Tok) : Prop := l ≠ []

/-- `RecBody` projects to `Flat` (toy of `RecSeqBody.toSafeBody`): a body is never empty. -/
theorem RecBody.toFlat {l : List Tok} (h : RecBody l) : Flat l := by
  cases h with
  | single e he =>
      cases he with
      | scalar => simp [Flat]
      | nestEmpty => simp [Flat]
      | nest i hi => simp [Flat]

/-- **The descend primitive** (R260, toy of `recseqbody_window_of_located_entry`): the internal
    descent, returning the inner-window `RecBody` *as a value* — what the navigation recursion threads
    as its IH input one nesting level down. -/
theorem recbody_of_entry {e interior : List Tok} (h : RecEntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) :
    RecBody interior ∨ interior = [] :=
  seq_interior h h_eq

/-- **The consumer joint** (toy of `seqBodyProps_of_located_entry`): the *same* descent, with one
    extra step — `RecBody.toFlat` projects the recursive body away into the terminal `Flat`.  Defined
    literally as the descend primitive followed by that consume step, so the factoring is manifest at
    definition time: **`flat_of_entry` = `recbody_of_entry` ▸ `toFlat`; the descend primitive is the
    consumer joint with the consume step truncated.** -/
theorem flat_of_entry {e interior : List Tok} (h : RecEntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) :
    Flat interior ∨ interior = [] :=
  (recbody_of_entry h h_eq).imp RecBody.toFlat id

/-! ### Positive — the descend primitive returns the recursable `RecBody`; the joint keeps only `Flat` -/

-- the nested located window `[OB, A, CB]` = `OB :: ([A] ++ [CB])`.
def entry1 : RecEntry [Tok.OB, Tok.A, Tok.CB] :=
  RecEntry.nest [Tok.A] (RecBody.single _ RecEntry.scalar)

/-- the descend primitive hands back the inner body `RecBody [A]` (the recursion's IH input). -/
theorem descend_one : RecBody [Tok.A] := by
  rcases recbody_of_entry (interior := [Tok.A]) entry1 rfl with h | h
  · exact h
  · exact absurd h (by decide)

/-- the consumer joint keeps only the projected terminal `Flat [A]` — the `RecBody` is consumed. -/
theorem consume_one : Flat [Tok.A] := by
  rcases flat_of_entry (interior := [Tok.A]) entry1 rfl with h | h
  · exact h
  · exact absurd h (by decide)

/-! ### Positive — the descend primitive is recursion-enabling (descend two levels) -/

-- a doubly-nested window `[OB, OB, A, CB, CB]` = `OB :: ([OB, A, CB] ++ [CB])`.
def entry2 : RecEntry [Tok.OB, Tok.OB, Tok.A, Tok.CB, Tok.CB] :=
  RecEntry.nest [Tok.OB, Tok.A, Tok.CB] (RecBody.single _ entry1)

/-- descend TWICE using only the primitive: outer window → `RecBody [OB,A,CB]` → (`.toEntry` then
    descend again) → `RecBody [A]`.  The consumer joint cannot do this — its `Flat` output is not an
    entry to re-descend. -/
theorem descend_twice : RecBody [Tok.A] := by
  rcases recbody_of_entry (interior := [Tok.OB, Tok.A, Tok.CB]) entry2 rfl with h1 | h1
  · -- h1 : RecBody [OB, A, CB]; re-descend its entry.
    rcases recbody_of_entry (interior := [Tok.A]) h1.toEntry rfl with h2 | h2
    · exact h2
    · exact absurd h2 (by decide)
  · exact absurd h1 (by decide)

/-! ### Negative — a scalar located entry has no bracket-window shape, so the descent never fires -/

theorem no_descend_scalar : ¬ ∃ interior, ([Tok.A] : List Tok) = Tok.OB :: (interior ++ [Tok.CB]) := by
  rintro ⟨interior, h⟩; injection h with h1 _; exact absurd h1 (by decide)

#guard ([Tok.OB, Tok.A, Tok.CB] : List Tok).length == 3
#guard ([Tok.OB, Tok.OB, Tok.A, Tok.CB, Tok.CB] : List Tok).length == 5

/-! ## The map mirror (Reflection 261) — a single-level descent transports *verbatim* across the
    seq/map axis; the storage asymmetry surfaces as a *dropped* opener-guard hypothesis

The map descend step `recmapbody_window_of_located_entry` (R261) is the symmetric mirror of the seq
one above (R260): the positional `take`/`drop` plumbing is character-for-character identical (here:
the SAME `seq_interior`/`map_interior` shape over the SAME `app_single_inj`), and the **only** delta
is dictated by the parallel deliverable's storage — the R244/R246 stored-vs-projected asymmetry.

Here it surfaces as a **dropped hypothesis**: the real `RecMapEntry.map_interior` needs no `h_op`
opener guard where `RecSeqEntry.seq_interior` does, because **every** `RecMapEntry` constructor is a
`{ … }` bracket frame (`RecSeqEntry` has a non-bracket `scalar`).  In this toy: `MapEntry` has NO
`scalar` constructor, so `map_interior`'s case split is *one branch shorter* than `seq_interior`'s
(two cases, not three) — there is no scalar case to exclude, hence no opener-guard step.  The
structural fact behind the dropped guard: a bare scalar `[A]` is a *valid* seq entry (`RecEntry.scalar`,
which the seq descent must exclude — `no_descend_scalar` above) but is **not a `MapEntry` at all**
(`no_mapentry_scalar` below). -/

-- toy of `RecMapBody` / `RecMapEntry`: like the seq toy but with NO scalar constructor — every entry
-- is a bracket frame, so the descent has no scalar case to rule out (the dropped opener guard).
mutual
  inductive MapBody : List Tok → Prop where
    | single (e : List Tok) (h : MapEntry e) : MapBody e
  inductive MapEntry : List Tok → Prop where
    | mapEmpty : MapEntry (Tok.OB :: (([] : List Tok) ++ [Tok.CB]))
    | nest (i : List Tok) (h : MapBody i) : MapEntry (Tok.OB :: (i ++ [Tok.CB]))
end

/-- A map body wraps exactly one entry. -/
theorem MapBody.toEntry {l : List Tok} (h : MapBody l) : MapEntry l := by
  cases h with | single e he => exact he

/-- **Single-level map descent** (toy of `RecMapEntry.map_interior`): every constructor is a bracket
    frame, so — unlike `seq_interior` — there is NO scalar case to exclude and hence no opener-guard
    step.  The case split is exactly two branches (`mapEmpty`, `nest`), one shorter than
    `seq_interior`'s three: the toy reflection of the real map mirror's *dropped `h_op` hypothesis*. -/
theorem map_interior {e interior : List Tok} (h : MapEntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) :
    MapBody interior ∨ interior = [] := by
  cases h with
  | mapEmpty =>
      right; injection h_eq with _ h2; exact (app_single_inj h2).symm
  | nest i hi =>
      left; injection h_eq with _ h2; exact (app_single_inj h2) ▸ hi

/-- `MapBody` projects to `Flat` (toy of `RecMapBody.toSafeBody`). -/
theorem MapBody.toFlat {l : List Tok} (h : MapBody l) : Flat l := by
  cases h with
  | single e he =>
      cases he with
      | mapEmpty => simp [Flat]
      | nest i hi => simp [Flat]

/-- **The map descend primitive** (R261, toy of `recmapbody_window_of_located_entry`) — the inner-window
    `MapBody` *as a value*, the navigation recursion's IH input one nesting level down. -/
theorem mapbody_of_entry {e interior : List Tok} (h : MapEntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) :
    MapBody interior ∨ interior = [] :=
  map_interior h h_eq

/-- **The map consumer joint** (toy of `mapBodyProps_of_located_entry`): the *same* descent then
    `MapBody.toFlat` consume, defined literally as the descend primitive followed by the consume step —
    the factoring manifest at definition time, exactly as `flat_of_entry`. -/
theorem flat_of_map_entry {e interior : List Tok} (h : MapEntry e)
    (h_eq : e = Tok.OB :: (interior ++ [Tok.CB])) :
    Flat interior ∨ interior = [] :=
  (mapbody_of_entry h h_eq).imp MapBody.toFlat id

/-- The structural asymmetry behind the dropped guard: a bare scalar `[A]` is **not a `MapEntry` at
    all** (every map entry is a bracket frame), so the map descent never confronts a scalar case and
    needs no opener guard — whereas the seq `[A]` IS a `RecEntry.scalar` the seq descent must exclude. -/
theorem no_mapentry_scalar : ¬ MapEntry [Tok.A] := by
  intro h; cases h

-- positive map witnesses (verbatim mirror of the seq witnesses; `{ }` = `[OB, CB]`).
def mapEntry1 : MapEntry [Tok.OB, Tok.OB, Tok.CB, Tok.CB] :=
  MapEntry.nest [Tok.OB, Tok.CB] (MapBody.single _ MapEntry.mapEmpty)

/-- the map descend primitive hands back the inner body `MapBody [OB, CB]` (the recursion's IH input). -/
theorem descend_map_one : MapBody [Tok.OB, Tok.CB] := by
  rcases mapbody_of_entry (interior := [Tok.OB, Tok.CB]) mapEntry1 rfl with h | h
  · exact h
  · exact absurd h (by decide)

-- a doubly-nested map window `{ { { } } }`.
def mapEntry2 : MapEntry [Tok.OB, Tok.OB, Tok.OB, Tok.CB, Tok.CB, Tok.CB] :=
  MapEntry.nest [Tok.OB, Tok.OB, Tok.CB, Tok.CB] (MapBody.single _ mapEntry1)

/-- descend TWICE using only the primitive (mirror of `descend_twice`): the map descend step is
    recursion-enabling exactly as the seq one. -/
theorem descend_map_twice : MapBody [Tok.OB, Tok.CB] := by
  rcases mapbody_of_entry (interior := [Tok.OB, Tok.OB, Tok.CB, Tok.CB]) mapEntry2 rfl with h1 | h1
  · rcases mapbody_of_entry (interior := [Tok.OB, Tok.CB]) h1.toEntry rfl with h2 | h2
    · exact h2
    · exact absurd h2 (by decide)
  · exact absurd h1 (by decide)

#guard ([Tok.OB, Tok.OB, Tok.CB, Tok.CB] : List Tok).length == 4
#guard ([Tok.OB, Tok.OB, Tok.OB, Tok.CB, Tok.CB, Tok.CB] : List Tok).length == 6

end Tests.Reflections.DescendStepConsumerJoint
