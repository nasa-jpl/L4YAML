/-!
# Reflection 300 — a PREFIX-quantified gate is never projectable from an interior-only window guard; reconstruct it in place from the boundary opener

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`enclosingMark_true_of_opener` / `seqTypedInterior_of_opener`, the Q2 discharge for the
`(i'-b-descend-root)` root seed.

A consume-time gate `enclosingMark l q = some true` (the seq-vs-map discriminator) quantifies over
the PREFIX `l.take (q+1)` of a window — NOT over the window's interior. So it is *provably not a
projection* of any interior-shaped window guard: two lists with the SAME interior but a DIFFERENT
opener give DIFFERENT marks (`opener_determines_mark_not_interior`). But the gate RECONSTRUCTS in
place from two boundary facts: the opener at `q` is a `seqOpen` (push-`true`), and the pre-opener
prefix folds to *some* stack. A `seqOpen` pushes `true`, so the stack top after the opener is `true`.

Toy substrate: `Tok` (`seqOpen` pushes `true`, `mapOpen` pushes `false`, `other` is inert), a typed
stack fold `tfold`, and `enclosingMark l q := (tfold (some []) (l.take (q+1))).bind (·.head?)`.

* `enclosingMark_true_of_opener` (POSITIVE) — faithful mirror of the real lemma: from a `seqOpen`
  opener + a prefix that folds to `some s`, the mark is `some true`. Same `take_add_one` + `tfold`
  append-split + single push + `head?_cons` shape.
* `enclosingMark_false_of_mapOpener` (NEGATIVE-in-spirit) — the same shape with `mapOpen` yields
  `some false`: the discriminator is real, the opener is what separates the two.
* `opener_determines_mark_not_interior` — two lists with identical interior (`drop 1`) but opposite
  openers have opposite marks, so the gate is NOT a function of the interior: it cannot be projected
  from an interior guard, it must be reconstructed from the boundary.
-/

namespace Tests.Reflections.PrefixGateReconstructedFromBoundary

set_option autoImplicit false

/-- A bracket-ish token: `seqOpen` pushes `true` (like `.flowSequenceStart`), `mapOpen` pushes
    `false` (like `.flowMappingStart`), `other` is inert (like a scalar). -/
inductive Tok | seqOpen | mapOpen | other
  deriving DecidableEq, Repr

/-- One typed-stack step — the toy of `btStep`. -/
def step (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .seqOpen => some (true :: s)
  | .mapOpen => some (false :: s)
  | .other   => some s

/-- The typed-stack fold — the toy of `btFold`. -/
def tfold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun acc t => acc.bind (step t)) s0

/-- `btFold_append`'s toy: the fold is a homomorphism on append. -/
theorem tfold_append (s0 : Option (List Bool)) (a b : List Tok) :
    tfold s0 (a ++ b) = tfold (tfold s0 a) b := by
  simp [tfold, List.foldl_append]

/-- The PREFIX-quantified gate: the typed-stack TOP after consuming `l.take (q+1)` — the toy of
    `SeqTypedInterior`'s `btFold`-stack-top conjunct (`enclosingMark`). It looks at the prefix
    `[0, q+1)`, NOT at any window interior. -/
def enclosingMark (l : List Tok) (q : Nat) : Option Bool :=
  (tfold (some []) (l.take (q + 1))).bind (·.head?)

/-- **POSITIVE — the in-place reconstruction** (faithful mirror of `enclosingMark_true_of_opener`):
    the gate is reconstructed from two boundary facts — the opener at `q` is a `seqOpen`, and the
    pre-opener prefix folds to `some s`. Same `take_add_one` split + single `step` push + `head?_cons`
    the real proof uses. These two hypotheses ARE the per-step thread list the root seed owes. -/
theorem enclosingMark_true_of_opener
    (l : List Tok) (q : Nat) (h_q : q < l.length)
    (s : List Bool) (h_pre : tfold (some []) (l.take q) = some s)
    (h_open : l[q]'h_q = .seqOpen) :
    enclosingMark l q = some true := by
  unfold enclosingMark
  have h_split : l.take (q + 1) = l.take q ++ [l[q]'h_q] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_q]; rfl
  have hstep : step (l[q]'h_q) s = some (true :: s) := by simp only [step, h_open]
  have hfold : tfold (some s) [l[q]'h_q] = step (l[q]'h_q) s := rfl
  rw [h_split, tfold_append, h_pre, hfold, hstep]; rfl

/-- **The discriminator is real** — the same shape with a `mapOpen` opener yields `some false`, not
    `some true`. The opener is exactly what separates seq-typed from map-typed (the R297 minimal pair). -/
theorem enclosingMark_false_of_mapOpener
    (l : List Tok) (q : Nat) (h_q : q < l.length)
    (s : List Bool) (h_pre : tfold (some []) (l.take q) = some s)
    (h_open : l[q]'h_q = .mapOpen) :
    enclosingMark l q = some false := by
  unfold enclosingMark
  have h_split : l.take (q + 1) = l.take q ++ [l[q]'h_q] := by
    rw [List.take_add_one, List.getElem?_eq_getElem h_q]; rfl
  have hstep : step (l[q]'h_q) s = some (false :: s) := by simp only [step, h_open]
  have hfold : tfold (some s) [l[q]'h_q] = step (l[q]'h_q) s := rfl
  rw [h_split, tfold_append, h_pre, hfold, hstep]; rfl

/-- **The gate is NOT a projection of the interior.** Two lists with IDENTICAL interior (`drop 1`)
    but opposite openers have opposite marks — so `enclosingMark` cannot be a function of the
    interior, and an interior-shaped window guard (toy of `FlowBodyWindow.wellTyped`) cannot project
    it. It must be reconstructed from the boundary, which is exactly what the lemmas above do. -/
theorem opener_determines_mark_not_interior :
    ([Tok.seqOpen, Tok.other].drop 1 = [Tok.mapOpen, Tok.other].drop 1) ∧
    enclosingMark [Tok.seqOpen, Tok.other] 0 = some true ∧
    enclosingMark [Tok.mapOpen, Tok.other] 0 = some false := by
  refine ⟨rfl, ?_, ?_⟩ <;> rfl

/-! ## Decidable witnesses -/

-- POSITIVE: a `seqOpen` opener (at the front) makes the window seq-typed (mark `some true`).
#guard enclosingMark [Tok.seqOpen, Tok.other, Tok.other] 0 == some true
-- NEGATIVE: a `mapOpen` opener at the same place makes it map-typed (mark `some false`).
#guard enclosingMark [Tok.mapOpen, Tok.other, Tok.other] 0 == some false
-- The same INTERIOR `[other, other]` under either opener — the mark flips with the OPENER, proving
-- the gate is a prefix/boundary fact, not an interior one.
#guard [Tok.seqOpen, Tok.other, Tok.other].drop 1 == [Tok.mapOpen, Tok.other, Tok.other].drop 1
-- A nested opener deeper in the prefix is still read off correctly (a `[` after a `[`).
#guard enclosingMark [Tok.seqOpen, Tok.other, Tok.seqOpen, Tok.other] 2 == some true

/-- POSITIVE (decidable): both the seq and map reconstructions hold on concrete inputs at once —
    the boundary opener fully determines the gate. -/
theorem reconstruction_examples :
    (enclosingMark [Tok.seqOpen, Tok.other] 0 = some true) ∧
    (enclosingMark [Tok.mapOpen, Tok.other] 0 = some false) := by
  constructor <;> rfl

end Tests.Reflections.PrefixGateReconstructedFromBoundary
