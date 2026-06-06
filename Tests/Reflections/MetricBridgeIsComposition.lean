/-!
# Reflection 310 — a feared "bridge between two parallel metrics" is often ALREADY a theorem: a STRUCTURAL count and a NUMERIC count that share a substrate are equated by composition, not by a new per-step induction

Self-contained (core Lean) toy of the gate→hypothesis bridge that landed
`flowBracketBalance_pos_of_btFold_head`.

Two metrics over a token stream (`op b` pushes a `Bool`, `cl` pops, `neu` is neutral):
* the NUMERIC balance `bal` (a fold of `+1 / -1 / 0`), and
* the STRUCTURAL typed-stack `fold` (a `List Bool`; its LENGTH is the second metric).

The de-risk fear was that these two counts might DIVERGE (push map vs seq differently),
needing a per-step induction relating pushes to deltas.  They do not — both reduce to the
SAME shared substrate (`bal`): `foldLen` proves `(stack length) = bal`, so the bridge
(non-empty stack ⇒ `bal ≥ 1`) is a two-line COMPOSITION, no new induction.

**Correction 1 (POSITIVE `bridge`).** `bridge` is `foldLen` + "a non-empty stack has length
≥ 1" + `omega`.  The per-step reconciliation the de-risk feared is exactly `foldLen`, which
already exists.

**Type-agnostic dividend (POSITIVE).** `bridge` takes `= some hd` for an ARBITRARY `hd : Bool`
— the proof never branches on the head VALUE, only on the stack being non-empty.  So ONE lemma
serves both axes (`hd = true` = seq, `hd = false` = map) verbatim (`bridgeTrue` / `bridgeFalse`).

**Correction 2 (NEGATIVE, `#guard`-backed).** The fear is legitimate IN GENERAL: a WRONG
structural metric `wfold` (one that pushes only on `op true`, ignoring `op false`) genuinely
diverges from `bal` — `#guard` exhibits a stream where `wfold`'s length ≠ `bal`.  So one must
VERIFY the substrate is shared (here every `op _` pushes uniformly AND contributes `+1`); the
REAL `fold` coincides, the contrived `wfold` does not.  The lesson: don't assume divergence
(author a per-step induction) NOR assume coincidence (skip verification) — look for the count
lemma on each metric and check it reduces to a common substrate.
-/

namespace Tests.Reflections.MetricBridgeIsComposition

set_option autoImplicit false

/-- A token: an opener carrying a `Bool` tag (e.g. `true` = seq `[`, `false` = map `{`), a
    closer, or a neutral token. -/
inductive Tok where
  | op (b : Bool)
  | cl
  | neu

/-- The NUMERIC metric's per-token delta: `+1 / -1 / 0`. -/
def delta : Tok → Int
  | .op _ => 1
  | .cl   => -1
  | .neu  => 0

/-- The NUMERIC metric: cumulative balance. -/
def bal : List Tok → Int
  | []      => 0
  | t :: ts => delta t + bal ts

/-- One step of the STRUCTURAL metric's typed stack (push the tag, pop a match, or no-op). -/
def step (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .op b => some (b :: s)
  | .cl   => match s with | _ :: s' => some s' | [] => none
  | .neu  => some s

/-- The STRUCTURAL metric: fold the typed stack (`none` absorbing). -/
def fold (s0 : Option (List Bool)) : List Tok → Option (List Bool)
  | []      => s0
  | t :: ts => fold (s0.bind (step t)) ts

theorem fold_none (l : List Tok) : fold none l = none := by
  induction l with
  | nil => rfl
  | cons t ts ih => simpa [fold] using ih

/-! ## The SHARED SUBSTRATE — the structural length equals the numeric balance. -/

/-- **The metric-unification lemma.**  Whenever the structural fold stays defined, the stack
    LENGTH differs from the start by the NUMERIC balance: both metrics reduce to `bal`.  This is
    the per-step reconciliation — and it is a plain induction that EXISTS once and for all
    (the toy `btFold_length`); the bridge below never re-derives it. -/
theorem foldLen (l : List Tok) :
    ∀ (s0 s1 : List Bool), fold (some s0) l = some s1 →
      (s1.length : Int) = (s0.length : Int) + bal l := by
  induction l with
  | nil =>
    intro s0 s1 h; simp only [fold] at h
    obtain rfl := Option.some.inj h; simp [bal]
  | cons t ts ih =>
    intro s0 s1 h
    simp only [fold] at h
    cases t with
    | op b =>
      have h' : fold (some (b :: s0)) ts = some s1 := by simpa [step, Option.bind] using h
      have := ih (b :: s0) s1 h'
      simp only [List.length_cons] at this
      have : (s1.length : Int) = (s0.length : Int) + 1 + bal ts := by push_cast at this ⊢; omega
      rw [this, bal]; simp [delta]; omega
    | cl =>
      cases s0 with
      | nil => simp [step, Option.bind, fold_none] at h
      | cons a s0' =>
        have h' : fold (some s0') ts = some s1 := by simpa [step, Option.bind] using h
        have := ih s0' s1 h'
        simp only [List.length_cons]
        rw [bal]; push_cast at this ⊢; simp [delta]; omega
    | neu =>
      have h' : fold (some s0) ts = some s1 := by simpa [step, Option.bind] using h
      have := ih s0 s1 h'
      rw [bal]; simp [delta]; exact this

/-! ## The BRIDGE — a two-line composition, NOT a new induction. -/

/-- **The bridge** (toy `flowBracketBalance_pos_of_btFold_head`): a non-empty structural stack at
    the end forces the numeric balance `≥ 1`.  `hd : Bool` is ARBITRARY — the proof is blind to the
    head value, so this one lemma serves both axes.  Proof = `foldLen` + "non-empty ⇒ length ≥ 1". -/
theorem bridge (l : List Tok) (hd : Bool)
    (h : (fold (some []) l).bind (·.head?) = some hd) : bal l ≥ 1 := by
  cases hf : fold (some []) l with
  | none => rw [hf] at h; simp at h
  | some s =>
    rw [hf] at h
    have hs_ne : s ≠ [] := by intro he; subst he; simp at h
    have hlen := foldLen l [] s hf
    simp only [List.length_nil] at hlen
    have h1 : 1 ≤ s.length := by
      cases s with
      | nil => exact absurd rfl hs_ne
      | cons _ _ => simp
    omega

/-- The seq instance (`hd = true`). -/
theorem bridgeTrue (l : List Tok)
    (h : (fold (some []) l).bind (·.head?) = some true) : bal l ≥ 1 :=
  bridge l true h

/-- The map instance (`hd = false`) — the SAME core, verbatim. -/
theorem bridgeFalse (l : List Tok)
    (h : (fold (some []) l).bind (·.head?) = some false) : bal l ≥ 1 :=
  bridge l false h

/-! ## NEGATIVE — the fear is legitimate in general; verify the substrate is shared. -/

/-- A WRONG structural metric: pushes only on `op true`, IGNORING `op false`.  Its length does NOT
    track `bal` whenever an `op false` appears — exactly the "map vs seq counted differently"
    divergence the de-risk feared.  The REAL `fold` does not have this defect (every `op _` pushes). -/
def wstep (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .op true  => some (true :: s)
  | .op false => some s                 -- BUG: forgets to push the map opener
  | .cl       => match s with | _ :: s' => some s' | [] => none
  | .neu      => some s

def wfold (s0 : Option (List Bool)) : List Tok → Option (List Bool)
  | []      => s0
  | t :: ts => wfold (s0.bind (wstep t)) ts

/-- A stream with a map opener still pending: `[op false, op true]`. -/
def diverge : List Tok := [.op false, .op true]

-- the REAL metrics coincide (length = bal) — the shared substrate holds:
#guard (fold (some []) diverge).map (·.length) == some 2
#guard bal diverge == 2
-- the WRONG metric diverges — its length (1) ≠ bal (2): the fear is real if the substrate is NOT shared:
#guard (wfold (some []) diverge).map (·.length) == some 1
#guard !((wfold (some []) diverge).map (·.length) == some (bal diverge).toNat)
-- the bridge fires on the real metric for BOTH head tags:
#guard decide (bal diverge ≥ 1)
#guard ((fold (some []) diverge).bind (·.head?) == some true)   -- top is the seq opener
#guard ((fold (some []) [.op false]).bind (·.head?) == some false)  -- map opener at top

end Tests.Reflections.MetricBridgeIsComposition
