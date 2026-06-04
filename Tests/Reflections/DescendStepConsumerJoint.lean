/-
# Reflection 260 — the navigation recursion's *descend step* IS a consumer joint's internal computation, truncated: returned as a value instead of consumed

Self-contained, `L4YAML`-free runnable illustration of the proof-engineering principle in
Blueprint Reflection 260 (and memory `ref-descend-step-is-consumer-joint-truncated`).

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

end Tests.Reflections.DescendStepConsumerJoint
