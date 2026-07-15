/-!
# Reflection 295 — an INCOMPLETE guard-projection still factors

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind `flowBodyContent_of_deep`:
a strengthened carrier (`DeepGuard`, the toy of `FlowBodyContentDeep`) projects MOST of a target
structure (`Content`, the toy of `FlowBodyContent`) but not all of it — and the right brick is the
ASSEMBLER that projects the covered part and NAMES the residual, not a heavier carrier.

The projection is partial in TWO grains at once:

* `head` — a WHOLE-FIELD free projection: `DeepGuard.head` and `Content.head` are the SAME proposition,
  so the deep field types directly (cf. `headContentStart`).
* `sepNext` — a CASE-SPLIT projection: the deep guard covers its INTERIOR (`k + 1 < n`, the
  `sepNextInterior` field) but not its BOUNDARY (`k + 1 = n`); the boundary escapes because the deep
  field is gated `k + 1 < n` (cf. `feContentStart`, gated `k + 1 < hi`).

So the residual is "one whole field (`valSep`, the toy of `bodySucc`) + one missing CASE of another
(`sepNext` at the boundary)" — named as the producer's exact contract.

* POSITIVE — `assemble` builds `Content` from `DeepGuard` plus the two named residual hypotheses; the
  `head` arm is a free projection, the `sepNext` arm is `rcases`-split into projected-interior /
  residual-boundary.
* NEGATIVE — `valSep_not_derivable` shows the carrier is SEPARATOR-BLIND: a `DeepGuard` instance holds
  while `valSep` fails (two adjacent scalars, no comma — `[a b]`), so the residual is genuinely owed.
  `boundary_not_reachable` shows the case-split is real: a `DeepGuard` instance holds while `sepNext`
  fails at the boundary `k + 1 = n` (a trailing comma), so the deep guard's interior-gated field cannot
  reach it.
-/

namespace Tests.Reflections.IncompleteProjectionStillFactors

set_option autoImplicit false

/-- Toy token stream alphabet. -/
inductive Tok | scal | comma | opn | cls
  deriving DecidableEq, Repr

/-- Decidable head-shape classifier (toy of `isFlowContentStart`). -/
def isContentStartB : Tok → Bool
  | .scal => true
  | .opn  => true
  | .comma => false
  | .cls  => false

/-- Propositional version the structures quantify over. -/
def isContentStart (t : Tok) : Prop := isContentStartB t = true

/-! ## The carrier and the target -/

/-- The strengthened carrier the recursion threads (toy of `FlowBodyContentDeep`).  `head` is the
    window-head content-start; `sepNextInterior` is the all-but-boundary "after a comma, content"
    field — GATED `k + 1 < n`, exactly the gating that lets `feContentStart` descend as a restriction. -/
structure DeepGuard (n : Nat) (tok : Nat → Tok) : Prop where
  head : isContentStart (tok 0)
  sepNextInterior : ∀ k, k + 1 < n → tok k = .comma → isContentStart (tok (k + 1))

/-- The target the head-dispatch consumes (toy of `FlowBodyContent`).  `head` matches the carrier;
    `valSep` is the comma-separation field (toy of `bodySucc`); `sepNext` is the after-a-comma field
    over the FULL range `k < n`, so its `k + 1 = n` boundary escapes the carrier's interior field. -/
structure Content (n : Nat) (tok : Nat → Tok) : Prop where
  head : isContentStart (tok 0)
  valSep : ∀ k, k < n → tok k ≠ .comma → (k + 1 = n ∨ tok (k + 1) = .comma)
  sepNext : ∀ k, k < n → tok k = .comma → isContentStart (tok (k + 1))

/-! ## POSITIVE — the assembler projects the covered part and names the residual -/

/-- The assembler (toy of `flowBodyContent_of_deep`).  `head` is a FREE whole-field projection;
    `sepNext` is `rcases`-split into the carrier's interior field (`k + 1 < n`) and the named boundary
    residual (`k + 1 = n`); `valSep` is wholly residual. -/
theorem assemble {n : Nat} {tok : Nat → Tok}
    (h_deep : DeepGuard n tok)
    (h_valSep : ∀ k, k < n → tok k ≠ .comma → (k + 1 = n ∨ tok (k + 1) = .comma))
    (h_boundary : ∀ k, k + 1 = n → tok k = .comma → isContentStart (tok (k + 1))) :
    Content n tok :=
  { head := h_deep.head                       -- whole-field free projection
    valSep := h_valSep                          -- orthogonal residual field
    sepNext := fun k hk hc => by
      rcases Nat.lt_or_ge (k + 1) n with h | h
      · exact h_deep.sepNextInterior k h hc     -- interior: PROJECTED from the carrier
      · exact h_boundary k (by omega) hc }      -- boundary: the NAMED residual

/-! ## NEGATIVE — the residual is genuinely not derivable from the carrier -/

/-- Two adjacent scalars `[a b]`, no comma — the witness that the carrier is SEPARATOR-BLIND. -/
def twoScalars : Nat → Tok := fun _ => .scal

/-- The carrier holds of `[a b]`: `head` is `scal` (content-start), and `sepNextInterior` is vacuous
    (no token is a comma). -/
theorem deep_twoScalars : DeepGuard 2 twoScalars where
  head := rfl
  sepNextInterior := by intro k _ hc; exact absurd hc (by simp [twoScalars])

/-- …yet `valSep` (comma-separation, toy of `bodySucc`) FAILS there: at `k = 0`, `tok 0 = scal` is not
    a comma, but neither `0 + 1 = 2` nor `tok 1 = comma`.  So the carrier cannot project `valSep` — it
    is genuinely owed (the bracket/balance/typed substrate accepts `[a b]`). -/
theorem valSep_not_derivable :
    ∃ tok : Nat → Tok, DeepGuard 2 tok ∧
      ¬ (∀ k, k < 2 → tok k ≠ .comma → (k + 1 = 2 ∨ tok (k + 1) = .comma)) := by
  refine ⟨twoScalars, deep_twoScalars, ?_⟩
  intro h
  rcases h 0 (by omega) (by simp [twoScalars]) with h1 | h2
  · exact absurd h1 (by omega)
  · exact absurd h2 (by simp [twoScalars])

/-- A trailing comma `[a ,]` — the witness that the `sepNext` boundary escapes the carrier. -/
def trailingComma : Nat → Tok
  | 0 => .scal
  | 1 => .comma
  | _ => .cls

/-- The carrier holds of `[a ,]`: `head` is `scal`, and `sepNextInterior` is vacuous (the only comma is
    at `k = 1`, where `k + 1 = 2 = n` is NOT `< n`, so the interior field never fires on it). -/
theorem deep_trailingComma : DeepGuard 2 trailingComma where
  head := rfl
  sepNextInterior := by
    intro k hk hc
    -- the only comma is at k = 1, but there k + 1 = 2 is not < 2
    match k, hk with
    | 0, _ => exact absurd hc (by simp [trailingComma])

/-- …yet `sepNext` FAILS at the boundary `k + 1 = n`: at `k = 1`, `tok 1 = comma` but `tok 2 = cls` is
    not a content-start.  So the carrier's interior-gated field cannot reach the boundary — that case is
    a genuine residual, not a projection. -/
theorem boundary_not_reachable :
    ∃ tok : Nat → Tok, DeepGuard 2 tok ∧
      ¬ (∀ k, k < 2 → tok k = .comma → isContentStart (tok (k + 1))) := by
  refine ⟨trailingComma, deep_trailingComma, ?_⟩
  intro h
  have := h 1 (by omega) (by simp [trailingComma])
  exact absurd this (by simp [isContentStart, trailingComma, isContentStartB])

-- The head field IS a free projection: same proposition on both sides (the function below is the
-- identity on the proof, type-checking only because `DeepGuard.head` and `Content.head` coincide).
#guard isContentStartB Tok.scal == true
#guard isContentStartB Tok.comma == false
#guard isContentStartB Tok.cls == false

end Tests.Reflections.IncompleteProjectionStillFactors
