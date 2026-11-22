/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-!
# Block-scalar-in-flow guard: proof helpers (DOCS item 9c) — legacy scanner

`scanNextToken_dispatchContent`'s `|`/`>` arm is guarded by `s.inFlow`:
`c-l+literal` [170] and `c-l+folded` [174] are reachable only through
`s-l+block-node` [196], and `ns-flow-content` [158] offers plain, flow-seq,
flow-map, single- and double-quoted only — so a block-scalar header inside a
flow collection has no derivation and the scanner rejects it with
`ScanError.blockScalarInFlow`.

The guard sits *inside* the arm rather than at the head of the dispatcher, so
only the `|`/`>` arm changed shape.  Downstream proofs that used to read
`h : scanBlockScalar s = .ok s'` straight off the arm now read the guarded
form; `blockScalarGuard_elim` restores the pre-guard equation and, for free,
the `s.inFlow = false` the guard establishes.

This mirrors `FlowAdjacency.peel_flowAdj`: an *inversion* helper for the sites
that consume a successful dispatch, plus a *construction* helper
(`blockScalarGuard_ok_of_notInFlow`) for the sites that build one.

The indexed twin needs no such helper: its guard is folded into the existing
header check as `blockScalarPreErrIx`, so its arm keeps the exact `split`
sequence it had before item 9c.
-/

namespace L4YAML.Proofs.BlockScalarFlowGuard

open L4YAML L4YAML.Scanner

/-- The guarded `|`/`>` arm of `scanNextToken_dispatchContent`, as it appears
    after `unfold`.  Naming it keeps the helper statements readable and lets a
    call site `show` its way to the expected shape. -/
abbrev guardedArm (s : ScannerState) (c : Char) : Except ScanError ScannerState :=
  if s.inFlow = true then
    .error (.blockScalarInFlow c s.line s.col)
  else
    scanBlockScalar s

/-! ## Inversion (peel the guard off a successful arm) -/

/-- A successful guarded block-scalar arm gives back **both** halves of the
    guard: the flow context was block (`s.inFlow = false` — the `.error` branch
    cannot equal `.ok`), and the underlying `scanBlockScalar` succeeded. -/
lemma blockScalarGuard_elim {s s' : ScannerState} {c : Char}
    (h : guardedArm s c = .ok s') :
    s.inFlow = false ∧ scanBlockScalar s = .ok s' := by
  unfold guardedArm at h
  split at h
  next => exact absurd h (by simp)
  next hf => exact ⟨by simpa using hf, h⟩

/-- Inversion, `scanBlockScalar` half only — the shape most call sites want. -/
lemma peel_blockScalarGuard {s s' : ScannerState} {c : Char}
    (h : guardedArm s c = .ok s') : scanBlockScalar s = .ok s' :=
  (blockScalarGuard_elim h).2

/-- Inversion, context half only. -/
lemma notInFlow_of_blockScalarGuard {s s' : ScannerState} {c : Char}
    (h : guardedArm s c = .ok s') : s.inFlow = false :=
  (blockScalarGuard_elim h).1

/-! ## The dispatcher-level fact (what β.3's content step consumes)

`dispatchContent_evidence` hands the flow-interior content step an
`SFlowNode`-shaped disjunction that still offers `SCLLiteral ∨ SCLFolded`.
Inside a flow collection those two are underivable, and the lemma below is
what says so *about the scanner*: at depth ≥ 1 a successful content dispatch
cannot have been on a block-scalar header, so the literal/folded disjuncts are
refutable rather than merely unwelcome.  This is the whole point of item 9c —
before the guard, the arm was not refutable at all. -/

/-- In flow context a successful `scanNextToken_dispatchContent` was **not** on
    a block-scalar header.  §8.1 [170]/[174] via `ns-flow-content` [158]. -/
lemma dispatchContent_not_blockScalar_of_inFlow {s s' : ScannerState} {c : Char}
    (hf : s.inFlow = true) (h : scanNextToken_dispatchContent s c = .ok s') :
    c ≠ '|' ∧ c ≠ '>' := by
  -- One walk down the dispatcher, reused for both characters.
  have key : ∀ d : Char, (d == '|' || d == '>') = true →
      scanNextToken_dispatchContent s d = .ok s' → False := by
    intro d hd hd_ok
    unfold scanNextToken_dispatchContent at hd_ok
    simp only [bind, Except.bind, pure, Except.pure] at hd_ok
    -- `&`, `*`, `!` are all ruled out by `hd`.
    split at hd_ok
    · rename_i h_eq
      rcases Bool.or_eq_true _ _ |>.mp hd with h | h <;>
        simp only [beq_iff_eq] at h h_eq <;> simp [h] at h_eq
    · split at hd_ok
      · rename_i h_eq
        rcases Bool.or_eq_true _ _ |>.mp hd with h | h <;>
          simp only [beq_iff_eq] at h h_eq <;> simp [h] at h_eq
      · split at hd_ok
        · rename_i h_eq
          rcases Bool.or_eq_true _ _ |>.mp hd with h | h <;>
            simp only [beq_iff_eq] at h h_eq <;> simp [h] at h_eq
        · -- Only the `|`/`>` arm is left, and `hf` fires its item-9c guard, so
          -- the arm is `.error` — `split` reduced both `ite`s against `hd`/`hf`.
          exact absurd hd_ok (by simp)
  exact ⟨fun hc => key c (by simp [hc]) h, fun hc => key c (by simp [hc]) h⟩

/-! ## Construction (discharge the guard from the local invariant) -/

/-- In block context the guard is transparent: the arm *is* `scanBlockScalar`. -/
lemma blockScalarGuard_ok_of_notInFlow {s : ScannerState} {c : Char}
    (hf : s.inFlow = false) : guardedArm s c = scanBlockScalar s := by
  unfold guardedArm
  simp [hf]

end L4YAML.Proofs.BlockScalarFlowGuard

end Blanket
