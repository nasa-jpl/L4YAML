/-! # Reflection 501 — re-threading a guard-strengthened recursion re-twins only the guard-READING edges

Completing the carrier-free `FlowBodyContent` thread for the seq axis (`seqRoot_flowBodyContent_seq`, R501)
needed only the ROOT SEED beyond the R500 descend edge — because the ADVANCE edge `flowBodyContent_advance`
is GUARD-NEUTRAL: it re-bases the PROJECTION (`FlowBodyContent`) and never reads the deep guard, so the SAME
term is reused VERBATIM across the strong and `_seq` threads. The three structural moves of a
root+descend+advance thread PARTITION by guard-sensitivity:

* DESCEND READS the guard (to produce the child) ⇒ needs a `_seq` twin (`flowBodyContent_descend_seq`, R500).
* ROOT CONSUMES the root-true guard (as a hypothesis) ⇒ needs a `_seq` twin (`seqRoot_flowBodyContent_seq`).
* ADVANCE operates on the PROJECTION only (the guard is ABSENT from its type) ⇒ GUARD-NEUTRAL, shared.

So when you weaken/re-scope a recursion guard and must re-thread a downstream projection over it, count the
guard-READS: those edges twin; a projection-re-basing edge does not. The re-thread work-list is
pre-countable from the edge SIGNATURES — guard-in-type ⇒ twin, guard-absent ⇒ shared.

`Proj` models `FlowBodyContent` (the threaded projection); `GStrong`/`GWeak` model
`FlowBodyContentDeep`/`FlowBodyContentDeepSeq` (the strong vs re-scoped guards). The two guards are
genuinely distinct TYPES, so `root`/`descend` must be written once per guard (each MENTIONS its guard);
`advance`'s type mentions NO guard, so a single `advance` term serves BOTH threads.
-/

namespace GuardReadingEdgesNeedTwins

/-- The PROJECTION threaded by the recursion (models `FlowBodyContent`): every element is content (`true`).
    It carries enough to re-base itself, so ADVANCE needs no guard. -/
def Proj (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- STRONG guard (models the all-depth `FlowBodyContentDeep`). -/
def GStrong (l : List Bool) : Prop := ∀ x ∈ l, x = true

/-- RE-SCOPED weak guard (models `FlowBodyContentDeepSeq`): a genuinely DIFFERENT type — it carries the
    content facts PLUS an extra window-absolute gate (here non-emptiness, the `≠ ]` / `≠ .key` analog). -/
structure GWeak (l : List Bool) : Prop where
  allTrue : ∀ x ∈ l, x = true
  nonempty : l ≠ []

/-- ROOT edge, STRONG — guard-READING (the guard appears in its type). -/
theorem rootStrong {l : List Bool} (g : GStrong l) : Proj l := g

/-- ROOT edge, WEAK twin — guard-READING. A SEPARATE function: its domain is `GWeak`, not `GStrong`. The
    re-scoped guard carries strictly more (`nonempty`), but the root reads only the content facts off it —
    the twin exists because the guard TYPE differs, not because the proof differs. -/
theorem rootWeak {l : List Bool} (g : GWeak l) : Proj l := g.allTrue

/-- DESCEND edge, STRONG — guard-READING: the child of `a :: rest` is `rest`, content by the guard. -/
theorem descendStrong {a : Bool} {rest : List Bool} (g : GStrong (a :: rest)) : Proj rest :=
  fun x hx => g x (List.mem_cons_of_mem a hx)

/-- DESCEND edge, WEAK twin — guard-READING (reads `g.allTrue`). Separate from `descendStrong`. -/
theorem descendWeak {a : Bool} {rest : List Bool} (g : GWeak (a :: rest)) : Proj rest :=
  fun x hx => g.allTrue x (List.mem_cons_of_mem a hx)

/-- **ADVANCE edge — GUARD-NEUTRAL.** Its type mentions NO guard, only `Proj`: it re-bases the projection
    by dropping the consumed head. ONE function; there is no `advanceStrong`/`advanceWeak`. -/
theorem advance {a : Bool} {rest : List Bool} (p : Proj (a :: rest)) : Proj rest :=
  fun x hx => p x (List.mem_cons_of_mem a hx)

/-- **The SHARED-advance witness, strong thread.** Root via the strong guard, then the SHARED `advance`. -/
theorem thread_strong {a : Bool} {rest : List Bool} (g : GStrong (a :: rest)) : Proj rest :=
  advance (rootStrong g)

/-- **The SHARED-advance witness, weak thread.** Root via the WEAK guard, then the *same* `advance` term —
    the advance edge did NOT need a `_seq` twin (cf. `flowBodyContent_advance` reused across both threads). -/
theorem thread_weak {a : Bool} {rest : List Bool} (g : GWeak (a :: rest)) : Proj rest :=
  advance (rootWeak g)

/-- **`advance` composes after EITHER descend, too** — guard-neutrality means it does not care which guard
    produced the `Proj` it consumes. The SAME `advance` is applied to a strong-descended projection… -/
theorem advance_after_descendStrong {a b : Bool} {rest : List Bool}
    (g : GStrong (a :: b :: rest)) : Proj rest :=
  advance (descendStrong g)

/-- …and to a weak-descended projection. No twin of `advance` anywhere. -/
theorem advance_after_descendWeak {a b : Bool} {rest : List Bool}
    (g : GWeak (a :: b :: rest)) : Proj rest :=
  advance (descendWeak g)

/-! **The partition, made concrete on the same data.** One `advance` instance serves a `Proj` obtained
    from EITHER guard. The `decide` leaves are axiom-FREE. -/

theorem gStrong2 : GStrong [true, true] := by unfold GStrong; decide
theorem gWeak2 : GWeak [true, true] := ⟨by decide, by decide⟩

/-- The strong thread reaches `Proj [true]`… -/
theorem demo_strong : Proj [true] := advance (a := true) (rootStrong gStrong2)
/-- …and the weak thread reaches the SAME `Proj [true]` via the SAME `advance`. -/
theorem demo_weak : Proj [true] := advance (a := true) (rootWeak gWeak2)

/-- **The twinning is forced by the guard TYPE, not the proof.** `GWeak` is a distinct type from `GStrong`
    (it has an extra field), so `rootStrong` / `descendStrong` cannot be applied to a `GWeak` — hence the
    twins. The discriminator: the guard appears in the root/descend SIGNATURES but is absent from
    `advance`'s. This witnesses that `GWeak` genuinely carries more than `GStrong` (so it is not the same
    type), making the separate root/descend functions necessary while `advance` stays single. -/
theorem gweak_is_strictly_more {l : List Bool} (g : GWeak l) : GStrong l ∧ l ≠ [] :=
  ⟨g.allTrue, g.nonempty⟩

end GuardReadingEdgesNeedTwins
