/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 674 — a disjunctive guard serves each park its own disjunct

**The rule.**  When one runtime guard fires on a DISJUNCTION of recorded
facts, one refutation lemma closes every park that carries any single
disjunct: the park pays only its own fact, the refuter takes the disjunction,
and the transport clauses are shared.  Three arms close for the price of one
lemma — and a park that cannot decide its disjunct pays `∨ True` and keeps
the escape, so the fourth arm costs DOMAIN rather than soundness
(Reflection 653's optional field, on the refutation side).

**The instance** (item 48).  `scanBlockEntry`/`scanKey` refuse on
`implicitValueLine == some line || lastTokenIsNodePropertyOnLine ||
markerOnLine` (item 299's `docStartLine` field; the token walk
`docStartOnLine` until then), and `scanValueValidate` on the first and third.
`dispatch_refutes_sameLine` takes the three facts as one disjunction;
`pendingMapValue` pays the stamp (implicit `:` only — the explicit `:` pays
`∨ True` and stays escapable), `pendingProps` pays the trailing-token read,
`pendingDocStart` pays the marker, and all three ride the same clause-1
payload (`s_prep.line = sc.line`, `lastRealToken?` preserved).

§1 the toy machine: a stamp, a tail flag, and a guard that fires on either.
§2 one refuter, consumed by both single-fact parks.  §3 the optional park:
its left inhabitants refute, and the claim that ALL of them do is FALSE —
the `∨ True` side names the survivors instead of overclaiming them away.
-/

namespace L4YAML.Tests.Reflections.DisjunctiveGuardServesEachPark

/-- §1 the machine: a line-stamp written by one step class, a tail flag
    written by another, and the current line. -/
structure M where
  stamp : Option Nat
  tail : Bool
  line : Nat

/-- The guard: an opener on a line that still carries either record. -/
def openStep (m : M) : Except Unit M :=
  if m.stamp == some m.line || m.tail then .error ()
  else .ok { m with stamp := none, tail := false }

/-- The walk between park and guard preserves both reads and the line. -/
def walk (m : M) : M := { m with line := m.line }

theorem walk_stamp (m : M) : (walk m).stamp = m.stamp := rfl
theorem walk_tail (m : M) : (walk m).tail = m.tail := rfl
theorem walk_line (m : M) : (walk m).line = m.line := rfl

/-- §2 ONE refuter, taking the disjunction the guard reads. -/
theorem openStep_refutes {m m' : M}
    (h_fact : m.stamp = some m.line ∨ m.tail = true)
    (h : openStep (walk m) = .ok m') : False := by
  unfold openStep walk at h
  rcases h_fact with h1 | h1 <;> simp [h1] at h

/-- The stamp park pays its own disjunct… -/
structure ParkStamp (m : M) : Prop where
  stamped : m.stamp = some m.line

/-- …and the tail park pays its own. -/
structure ParkTail (m : M) : Prop where
  tailed : m.tail = true

theorem parkStamp_closes {m m' : M} (hp : ParkStamp m)
    (h : openStep (walk m) = .ok m') : False :=
  openStep_refutes (Or.inl hp.stamped) h

theorem parkTail_closes {m m' : M} (hp : ParkTail m)
    (h : openStep (walk m) = .ok m') : False :=
  openStep_refutes (Or.inr hp.tailed) h

/-- §3 the optional park: a producer that cannot decide whether it stamped
    (item 48's explicit `:`) pays the right side and keeps the escape. -/
structure ParkMaybe (m : M) : Prop where
  stamped? : m.stamp = some m.line ∨ True

/-- Its LEFT inhabitants refute through the same lemma… -/
theorem parkMaybe_closes_left {m m' : M} (hp : m.stamp = some m.line)
    (h : openStep (walk m) = .ok m') : False :=
  openStep_refutes (Or.inl hp) h

/-- …and the claim that ALL of them do is FALSE: the unstamped, untailed
    state is parked by `Or.inr` and the guard passes it.  The `∨ True` side
    is the measured domain of the remaining escape, not a proof debt. -/
theorem parkMaybe_not_all_closed :
    ¬ ∀ m m' : M, ParkMaybe m → openStep (walk m) = .ok m' → False := by
  intro h
  exact h ⟨none, false, 0⟩ { stamp := none, tail := false, line := 0 }
    ⟨Or.inr trivial⟩ rfl

end L4YAML.Tests.Reflections.DisjunctiveGuardServesEachPark

end Blanket
