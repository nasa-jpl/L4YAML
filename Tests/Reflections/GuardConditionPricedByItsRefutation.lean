/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module


@[expose] public section Blanket

/-!
# Reflection 673 — a guard's condition is priced by its refutation

**The rule.**  A runtime guard added so that an invariant arm can REFUTE it —
"this input errors, so the arm's success hypothesis is absurd" — is priced by
that refutation, not by its runtime truth.  Every conjunct of the firing
condition must be (a) a fact the parked invariant CARRIES and (b) one a
preservation lemma TRANSPORTS to the state the guard actually reads.  A
conjunct that is true in every reachable state can still be unpayable (the
invariant never carried its provenance), and a conjunct that looks essential
can be replaced by a cheaper one the machine already records.

**The instance** (item 47).  `scanNextToken_checkAdjacentValue` refuses the
glued `:` after a completed node (`"a" :b`).  Its condition was cut three
times: keyed on the SAVED SIMPLE KEY it was true at every reachable park but
unpayable — flow closes restore the key from a stack no invariant couples to
the line; keyed on the token tail alone it over-fired — `:foo: v` is a legal
`:`-headed KEY at a line start (yaml-test-suite 2EBW); keyed on the token
tail plus the un-re-armed `simpleKeyAllowed` every park pays
(`StaleNodeTail`), the structural break re-arms the flag for the legal keys,
and each conjunct transports (`skipToContentLoop_simpleKeyAllowed_eq_of_needIndentCheck`,
the anyCol payload).

§1 the toy machine: a carried flag, a carried last-token, and a DERIVED cache
the invariant does not carry.  §2 the unpayable cut, measured: two parked
states agree on everything the invariant carries and disagree on the
derived-keyed guard — no arm built from the invariant can refute it.  §3 the
payable cut: decided by the carried fields alone, so the refutation is a
theorem of the invariant.
-/

namespace L4YAML.Tests.Reflections.GuardConditionPricedByItsRefutation

inductive Tok where
  | scalar | entry | opener
  deriving DecidableEq

def Tok.completes : Tok → Bool
  | .scalar => true
  | _ => false

/-- §1 the machine state: `armed` is re-set by every structural break,
    `last` is the token record, `cache` is derived state (a restored save)
    whose provenance no invariant here tracks. -/
structure M where
  armed : Bool
  last : Tok
  cache : Option Nat

/-- The park invariant carries the flag and the token — NOT the cache. -/
structure Park (m : M) : Prop where
  disarmed : m.armed = false
  tail : m.last.completes = true

/-- §2 the unpayable cut: fire on the derived cache. -/
def guardCache (m : M) : Bool := m.cache.isSome

/-- …and the measurement: two parked states, equal on everything `Park`
    carries, deciding `guardCache` differently — so no refutation exists
    that uses only the invariant. -/
theorem cache_cut_undecided :
    ∃ m₁ m₂ : M, Park m₁ ∧ Park m₂ ∧
      m₁.armed = m₂.armed ∧ m₁.last = m₂.last ∧
      guardCache m₁ ≠ guardCache m₂ :=
  ⟨⟨false, .scalar, some 3⟩, ⟨false, .scalar, none⟩,
   ⟨rfl, rfl⟩, ⟨rfl, rfl⟩, rfl, rfl, by decide⟩

/-- §3 the payable cut: fire on the carried fields. -/
def guardTail (m : M) : Bool := !m.armed && m.last.completes

/-- …whose refutation IS a theorem of the invariant: every parked state
    fires the guard, so an arm holding `Park` and the guard's success has
    `False` — the deferral it used to make is gone. -/
theorem tail_cut_decided (m : M) (h : Park m) : guardTail m = true := by
  unfold guardTail
  rw [h.disarmed, h.tail]
  rfl

/-- The boundary the flag protects (2EBW's shape): after a structural break
    the state is re-armed, and the same completed tail no longer fires —
    the legal line-start `:`-key stays served. -/
theorem rearmed_not_fired (t : Tok) (c : Option Nat) :
    guardTail ⟨true, t, c⟩ = false := rfl

end L4YAML.Tests.Reflections.GuardConditionPricedByItsRefutation

end Blanket
