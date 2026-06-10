/-!
# Reflection 341 — verify a deferred sub-brick is LANDED, then author the FOLD that consumes it

Self-contained (core Lean, no `L4YAML` import) toy model of the move behind
`seqDescent_provider_of_gate`.

A long-deferred plan keeps re-stating "author the LOCATOR alone first." But the locator was committed
sessions ago (`git log -S` reveals it). So the genuine smallest next brick is NOT the locator — it is
the **FOLD** that composes the two already-landed halves:

* `locate` — the LANDED half: from a `gate` at `a`, recover an opener `p` with its facts (`opener`);
* `assemble` — the LANDED half: from a located `p` + a `supplier` deliverable, build the `result`;
* `fold` — the NEW brick: `obtain p` from `locate`, then hand `p` + its facts to a producer-guarded
  supplier hypothesis `h_enc`, then call `assemble`.

`h_enc : ∀ p, opener s p a → supplier s p` is the producer-guarded universal whose GUARD `opener s p a`
matches `locate`'s OUTPUT term-for-term, so `h_enc p h_op` is immediate — the positive case of the
producer-guarded-quantifier pattern. `h_enc` IS the next producer's contract: the residual is now
exactly "discharge `h_enc`" (the deferred fixpoint), one named hypothesis instead of a vague "build the
driver."

The NEGATIVE (`fold_misguarded_stuck` below): if `h_enc`'s guard were a DIFFERENT condition the locator
does not supply (here `p = a`, but the locator yields `p < a`), the supplier could not be instantiated
at the located witness — the undischargeable trap. The fold works precisely because the lifted guard
mirrors the producer's.
-/

namespace Tests.Reflections.VerifyDeferredTaskLandedThenFold

set_option autoImplicit false

/-- A toy token stream. -/
abbrev Stream := List Nat

/-- The consumer's GATE over a window end `a`: the analogue of `SeqTypedInterior tokens a b`. -/
def gate (s : Stream) (a : Nat) : Prop := 0 < a ∧ a ≤ s.length

/-- The located opener's FACTS — the analogue of `seqEnclosingOpener_of_gate`'s four outputs
    (`p < a`, in bounds). -/
def opener (s : Stream) (p a : Nat) : Prop := p < a ∧ p < s.length

/-- The SUPPLIER deliverable the assembler additionally needs — the analogue of the enclosing
    `[p, hi)` window facts + IH the fixpoint must provide. -/
def supplier (s : Stream) (p : Nat) : Prop := p < s.length

/-- The provider EXISTENTIAL — the analogue of the `desc` shape. -/
def result (s : Stream) (a : Nat) : Prop := ∃ p, p < a ∧ p < s.length

/-! ## The two ALREADY-LANDED halves (committed sessions ago — `git log -S` finds them) -/

/-- **LANDED — the LOCATE half** (`seqEnclosingOpener_of_gate`): the gate produces an opener `p < a`
    with its facts.  Witness `p = a - 1`. -/
theorem locate (s : Stream) (a : Nat) (h : gate s a) : ∃ p, opener s p a := by
  obtain ⟨h0, hle⟩ := h
  exact ⟨a - 1, by omega, by omega⟩

/-- **LANDED — the ASSEMBLE half** (`seqDescent_provider_of_located`, carrier-free): from a located
    `p` + the supplier deliverable, build the result. -/
theorem assemble (s : Stream) (a p : Nat) (h_op : opener s p a) (h_sup : supplier s p) :
    result s a :=
  ⟨p, h_op.1, h_sup⟩

/-! ## The NEW brick — the FOLD that internalizes `locate` and lifts the supplier as `h_enc` -/

/-- **THE FOLD** (`seqDescent_provider_of_gate`): `obtain p` from the locator, hand `p` + its facts to
    the producer-guarded supplier hypothesis `h_enc`, call the assembler.  `h_enc`'s guard
    `opener s p a` matches `locate`'s output exactly, so `h_enc p h_op` is immediate — the positive
    case of the producer-guarded-quantifier pattern.  `h_enc` is now the residual: the deferred
    fixpoint's exact contract. -/
theorem fold (s : Stream) (a : Nat) (h_gate : gate s a)
    (h_enc : ∀ p, opener s p a → supplier s p) : result s a := by
  obtain ⟨p, h_op⟩ := locate s a h_gate
  exact assemble s a p h_op (h_enc p h_op)

/-! ## POSITIVE — end to end on a concrete stream

The supplier hypothesis discharges trivially (here `supplier s p := p < s.length` is exactly
`opener`'s second fact), so the fold needs nothing the gate did not already imply. -/

example : result [10, 20, 30] 3 :=
  fold [10, 20, 30] 3 ⟨by decide, by decide⟩ (fun _ h_op => h_op.2)

-- The located opener for `gate [10,20,30] 3` is `p = 2`, and `result` holds at it:
#guard (3 - 1 == 2)               -- the locator's witness `a - 1`
#guard (decide (2 < 3))           -- `p < a`
#guard (decide (2 < [10,20,30].length))  -- `p < length` (both `opener`.2 and `supplier`)

/-! ## NEGATIVE — a MIS-GUARDED `h_enc` cannot be discharged at the located witness

If `h_enc`'s guard demanded `p = a` (which `locate` never supplies — it yields `p < a`), the supplier
could not be instantiated at the located `p`.  The fold below is forced to ABANDON `h_enc'` and prove
`supplier` by other means; with a guard the locator's output cannot satisfy, `h_enc'` is dead weight —
the producer-guarded-quantifier trap.  We show it by NOT using `h_enc'` at all (it is unreachable at
`p = a - 1 < a`). -/
theorem fold_misguarded_stuck (s : Stream) (a : Nat) (h_gate : gate s a)
    (_h_enc' : ∀ p, p = a → supplier s p)   -- guard `p = a` ≠ locator output `p < a` ⇒ DEAD WEIGHT
    (h_sup_direct : ∀ p, opener s p a → supplier s p) :  -- must fall back to a matching-guard supplier
    result s a := by
  obtain ⟨p, h_op⟩ := locate s a h_gate
  -- `_h_enc' p` needs `p = a`, but `h_op.1 : p < a` — so `_h_enc'` is undischargeable here; fall back.
  exact assemble s a p h_op (h_sup_direct p h_op)

end Tests.Reflections.VerifyDeferredTaskLandedThenFold
