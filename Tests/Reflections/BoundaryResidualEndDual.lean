/-!
# Reflection 299 — the boundary residual is the interior fact's END-dual, discharged vacuously

Self-contained (core Lean, no `L4YAML` import) toy model of the lesson behind
`SafeBodyUnit_last_not_sep` / `SafeBodyUnit_array_last_not_sep_window` and the per-window discharge
`seqSeparatorFacts_of_windowed_safebodyunit`.

A producer-guard residual split into an INTERIOR fact (a separator is always followed by content)
and a BOUNDARY fact (the body never ENDS in a separator). The boundary fact is the END-dual of the
interior one over the SAME inductive substrate, and it discharges VACUOUSLY: the body's last element
cannot be a separator, so any premise asserting "the last position is a separator" is contradictory —
and from that contradiction the unprovable conclusion (a fact about the token PAST the window, which
the window's substrate cannot see) follows by `absurd`.

Toy substrate: `UBody` — a nonempty body of positive "unit" tokens separated by single `0`s
(`0` is the separator, like `.flowEntry`; positives are content, like content-start units).

* `UBody_ends_pos` — the structural END-dual: every `UBody` is `pre ++ [n]` with `0 < n`.
* `UBody_last_not_sep` (POSITIVE) — the boundary lemma: the last token (`k + 1 = length`) is `≠ 0`.
  Faithful mirror of `SafeBodyUnit_last_not_sep` (same `getElem?_append_right` index bridge).
* `UBody_noTrailing` (POSITIVE) — the vacuous discharge: assuming the last token IS a separator
  yields `False`, so any conclusion follows — the toy of `noTrailingSepFact` via `absurd`.
* The decidable model shows the negative: a body ending in a separator is NOT well-formed
  (`endsInSep` and `¬ wellFormed` coincide), so the boundary is never reached.
-/

namespace Tests.Reflections.BoundaryResidualEndDual

set_option autoImplicit false

/-- A body of positive "unit" tokens separated by single `0`s. `0` is the separator (like
    `.flowEntry`), positives are content units (like content-start entries). -/
inductive UBody : List Nat → Prop
  | single (n : Nat) (hn : 0 < n) : UBody [n]
  | cons (n : Nat) (rest : List Nat) (hn : 0 < n) (hr : UBody rest) : UBody (n :: 0 :: rest)

/-- **The structural END-dual**: every `UBody` ends in a positive (content) token, never a separator.
    The toy of "`SafeBodyUnit` is `… ++ [value-end]`". -/
theorem UBody_ends_pos {body : List Nat} (h : UBody body) :
    ∃ pre n, body = pre ++ [n] ∧ 0 < n := by
  induction h with
  | single n hn => exact ⟨[], n, rfl, hn⟩
  | cons n rest hn hr ih =>
    obtain ⟨pre, m, rfl, hm⟩ := ih
    exact ⟨n :: 0 :: pre, m, rfl, hm⟩

/-- **POSITIVE — the boundary lemma** (`SafeBodyUnit_last_not_sep`'s shape exactly): the last token
    of a `UBody` (the position `k` with `k + 1 = length`) is not the separator `0`.  Read off the
    END-dual decomposition; the `getElem?_append_right` index bridge is the same one the real proof
    uses to land at the appended element. -/
theorem UBody_last_not_sep {body : List Nat} (h : UBody body) :
    ∀ (k : Nat) (hk : k < body.length), k + 1 = body.length → body[k]'hk ≠ 0 := by
  obtain ⟨pre, n, rfl, hn⟩ := UBody_ends_pos h
  intro k hk hlast
  have hlen : (pre ++ [n]).length = pre.length + 1 := by simp
  have hkpre : k = pre.length := by rw [hlen] at hlast; omega
  subst hkpre
  have hidx : (pre ++ [n])[pre.length]'hk = n := by
    have h1 : (pre ++ [n])[pre.length]? = some n := by
      rw [List.getElem?_append_right (Nat.le_refl _), Nat.sub_self]; rfl
    rw [List.getElem?_eq_getElem hk] at h1
    exact Option.some.inj h1
  rw [hidx]; omega

/-- **POSITIVE — the vacuous discharge** (the toy of `noTrailingSepFact`): the conclusion `noTrailingSep`
    really wants to assert something about the token PAST the window (the closer the substrate cannot
    see).  It is reached only via a premise "the last in-window token is a separator", which the
    boundary lemma REFUTES — so the premise is contradictory and ANY conclusion (here `False`, standing
    for the un-seeable `isFlowContentStart`) follows by `absurd`. -/
theorem UBody_noTrailing {body : List Nat} (h : UBody body) :
    ∀ (k : Nat) (hk : k < body.length), k + 1 = body.length → body[k]'hk = 0 → False :=
  fun k hk hlast hsep => UBody_last_not_sep h k hk hlast hsep

/-! ## Decidable model: a body ending in a separator is NOT well-formed -/

/-- Decidable recognizer for `UBody`: nonempty, positive units separated by single `0`s. -/
def ubodyB : List Nat → Bool
  | [] => false
  | [n] => decide (0 < n)
  | n :: s :: rest => decide (0 < n) && decide (s = 0) && ubodyB rest

/-- Does the list END in the separator `0`? -/
def endsInSepB (l : List Nat) : Bool := decide (l.getLast? = some 0)

-- POSITIVE: a well-formed body and the no-trailing-separator fact it satisfies.
#guard ubodyB [3, 0, 5]            -- well-formed: units 3, 5 separated by one 0
#guard !endsInSepB [3, 0, 5]       -- ends in content `5`, not a separator (the boundary fact)

-- NEGATIVE: ending in a separator and being well-formed COINCIDE as opposites — the boundary the
-- `noTrailing` premise speaks of is never reached on a well-formed body.
#guard !ubodyB [3, 0, 5, 0]        -- trailing `0` ⇒ NOT well-formed
#guard endsInSepB [3, 0, 5, 0]     -- it does end in the separator
#guard !ubodyB [3, 0]              -- minimal trailing-separator body: NOT well-formed

/-- POSITIVE (decidable, all the example bodies at once): every well-formed example body does NOT end
    in a separator — the boundary fact holds exactly where the recognizer accepts. -/
theorem wf_examples_no_trailing :
    (ubodyB [3, 0, 5] = true ∧ endsInSepB [3, 0, 5] = false) ∧
    (ubodyB [7] = true ∧ endsInSepB [7] = false) := by decide

/-- NEGATIVE (decidable): a body ending in the separator is rejected by the recognizer, so the
    `noTrailing` premise (last token is a separator) never arises on an accepted body. -/
theorem trailing_sep_rejected :
    ubodyB [3, 0, 5, 0] = false ∧ endsInSepB [3, 0, 5, 0] = true := by decide

end Tests.Reflections.BoundaryResidualEndDual
