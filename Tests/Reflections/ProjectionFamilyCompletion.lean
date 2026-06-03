/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Reflection 244 — complete a new deliverable type's projection family before walking it

Self-contained (core Lean, no `L4YAML` import) runnable demonstration of the principle in
Blueprint Reflection 244: a recursive-deliverable family has *two* per-type obligations — the
**descent** (one nesting level down) and the **projection** (the navigation invariant *at this
level*).  When a new member is added to the family to satisfy a consumer joint, it tends to arrive
with only the descent lemma the joint forced.  Complete its **projection family immediately**: the
omitted projection is the locate's navigation invariant at that member's level, it is a *verbatim
mirror* of the sibling type's projection (its interior is another family member whose projection
already exists), and so it costs no new analysis.

The L4YAML instance: R242 added the recursive map-entry deliverable `RecMapEntry` and its descent
`RecMapEntry.map_interior`, but not its balance projection.  Every sibling carries a `→ WellBracketed`
projection (`RecSeqEntry`/`RecSeqBody` R238, `RecMapPair`/`RecMapBody` R240).  `RecMapEntry.toWellBracketed`
(R244) completes the family — a verbatim mirror of `RecSeqEntry.toWellBracketed`'s map case, built by
`wrap_map_block` over the interior's `WellBracketed` (`RecMapBody.toWellBracketed` for the non-empty case).

This toy strips it to a skeleton over a tiny bracket language (`os`/`cs` square, `oc`/`cc` curly, `a`
atom):

* `WellBr`  — count-based balance (any open `+1`, any close `-1`, no underflow); the projection the
  family members *store* and carry.  Toy `WellBracketed`.
* `Typed`   — kind-matched stack (a square open must meet a square close); a STRICTLY STRONGER property
  the entry type does NOT store.  Toy `WellTyped`.
* `RBody`   — the sibling/interior type, with its projection `RBody.toWellBr` already in hand.
* `REntry`  — the newly-added member wrapping an `RBody` interior (`mapEmpty` / `map`).  Toy `RecMapEntry`.

The two obligations: `REntry.descent` (toy `map_interior`) and `REntry.toWellBr` (the projection R244
lands).  The mirror engine is `wrapWB` (toy `wrap_map_block`): it lifts the interior's `WellBr` over a
`{ … }` frame — its own proof is a `ubFold` frame argument, the only real work, reused verbatim by the
projection.

The caveat (R244): the *typing* projection is NOT available the same way.  `WellBr` does not imply
`Typed` (`[os, cc]` is balanced but mistyped), and `REntry` stores only `WellBr`, so no `REntry.toTyped`
can exist from the stored data — the locate recovers `.wt` positionally instead.  Negative witnesses
make the gap concrete; "complete the projection family" means complete the projections the *stored*
fields support, never invent one for an unstored property.

Build: `lake build Tests.Reflections.ProjectionFamilyCompletion`.
-/

namespace ProjectionFamilyCompletion

/-- A tiny two-kind bracket language. `os`/`cs` = square `[`/`]`, `oc`/`cc` = curly `{`/`}`, `a` = atom. -/
inductive Tok | os | cs | oc | cc | a
  deriving DecidableEq, Repr

/-- Append-singleton injectivity (core Lean, no Mathlib): from `a ++ [x] = b ++ [y]` recover both
    `a = b` and `x = y`.  The toy of `append_singleton_inj`, used by the descent below. -/
theorem append_singleton_inj {a b : List Tok} {x y : Tok}
    (h : a ++ [x] = b ++ [y]) : a = b ∧ x = y := by
  have hr := congrArg List.reverse h
  simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
    List.cons_append] at hr
  injection hr with hxy har
  exact ⟨List.reverse_inj.mp har, hxy⟩

/-! ## `WellBr` — count-based balance (toy `WellBracketed`), the STORED/PROJECTED property -/

/-- One step of the count-based depth (any open `+1`; any close `-1`, underflow → `none`). -/
def ubStep (t : Tok) (d : Nat) : Option Nat :=
  match t with
  | .os | .oc => some (d + 1)
  | .cs | .cc => if d = 0 then none else some (d - 1)
  | .a        => some d

/-- Fold the depth across a token list (`none` is absorbing via `bind`). -/
def ubFold (d0 : Option Nat) (l : List Tok) : Option Nat :=
  l.foldl (fun acc t => acc.bind (ubStep t)) d0

/-- Count-based balance: depth returns to `0` with no underflow.  Toy `WellBracketed`. -/
abbrev WellBr (l : List Tok) : Prop := ubFold (some 0) l = some 0

theorem ubFold_cons (d0 : Option Nat) (t : Tok) (rest : List Tok) :
    ubFold d0 (t :: rest) = ubFold (d0.bind (ubStep t)) rest := by
  simp [ubFold, List.foldl_cons]

theorem ubFold_cons_some (d : Nat) (t : Tok) (rest : List Tok) :
    ubFold (some d) (t :: rest) = ubFold (ubStep t d) rest := by
  simp [ubFold, List.foldl_cons, Option.bind]

theorem ubFold_append (d0 : Option Nat) (a b : List Tok) :
    ubFold d0 (a ++ b) = ubFold (ubFold d0 a) b := by
  simp [ubFold, List.foldl_append]

theorem ubFold_none (l : List Tok) : ubFold none l = none := by
  induction l with
  | nil => rfl
  | cons t rest ih => rw [ubFold_cons]; simpa using ih

/-- **Stack-frame for one step.**  A step defined at depth `d` runs identically at depth `d + k`,
    ending `k` higher — the per-step engine of the frame argument. -/
theorem ubStep_frame (t : Tok) (d m k : Nat) (h : ubStep t d = some m) :
    ubStep t (d + k) = some (m + k) := by
  cases t with
  | os => simp only [ubStep] at h ⊢; injection h with h; congr 1; omega
  | oc => simp only [ubStep] at h ⊢; injection h with h; congr 1; omega
  | a  => simp only [ubStep] at h ⊢; injection h with h; congr 1; omega
  | cs =>
    simp only [ubStep] at h ⊢
    by_cases hd : d = 0
    · rw [hd] at h; simp at h
    · have hk : ¬ (d + k = 0) := by omega
      rw [if_neg hd] at h; rw [if_neg hk]; injection h with h; congr 1; omega
  | cc =>
    simp only [ubStep] at h ⊢
    by_cases hd : d = 0
    · rw [hd] at h; simp at h
    · have hk : ¬ (d + k = 0) := by omega
      rw [if_neg hd] at h; rw [if_neg hk]; injection h with h; congr 1; omega

/-- **Stack-frame for a fold.**  A `WellBr` body folded over any starting depth `d` returns to `d`:
    it never underflows its base.  The inductive engine of the mirror wrap. -/
theorem ubFold_frame (l : List Tok) :
    ∀ d m k, ubFold (some d) l = some m → ubFold (some (d + k)) l = some (m + k) := by
  induction l with
  | nil =>
    intro d m k h
    simp only [ubFold, List.foldl_nil] at h ⊢; injection h with h; congr 1; omega
  | cons t rest ih =>
    intro d m k h
    rw [ubFold_cons_some] at h ⊢
    cases hb : ubStep t d with
    | none => rw [hb, ubFold_none] at h; exact absurd h (by simp)
    | some m' =>
      rw [hb] at h; rw [ubStep_frame t d m' k hb]; exact ih m' m k h

/-- **The mirror engine** (toy `wrap_map_block`): a `WellBr` interior framed by `{ … }` is `WellBr`.
    Its only real work is the `ubFold_frame` argument — and the projection below reuses it verbatim. -/
theorem wrapWB (interior : List Tok) (h : WellBr interior) :
    WellBr (.oc :: (interior ++ [.cc])) := by
  have hf : ubFold (some 1) interior = some 1 := by
    have := ubFold_frame interior 0 0 1 h; simpa using this
  show ubFold (some 0) (.oc :: (interior ++ [.cc])) = some 0
  rw [ubFold_cons_some, ubFold_append]
  show ubFold (ubFold (some 1) interior) [Tok.cc] = some 0
  rw [hf]; decide

/-! ## `Typed` — kind-matched stack (toy `WellTyped`), the STRONGER property the entry does NOT store -/

/-- One step of the typed stack (`true` = open square, `false` = open curly; a close pops only a
    matching opener). -/
def tStep (t : Tok) (s : List Bool) : Option (List Bool) :=
  match t with
  | .os => some (true :: s)
  | .oc => some (false :: s)
  | .cs => match s with | true :: s' => some s' | _ => none
  | .cc => match s with | false :: s' => some s' | _ => none
  | .a  => some s

def tFold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun acc t => acc.bind (tStep t)) s0

/-- Kind-matched balance: the typed stack returns empty with no mismatch.  Toy `WellTyped`. -/
abbrev Typed (l : List Tok) : Prop := tFold (some []) l = some []

/-! ## The family — sibling `RBody` (projection in hand) and the new member `REntry` -/

/-- The sibling/interior type, whose projection `RBody.toWellBr` already exists (toy `RecMapBody`). -/
inductive RBody : List Tok → Prop where
  | single (l : List Tok) (h : WellBr l) : RBody l

/-- The sibling's projection (toy `RecMapBody.toWellBracketed`), already in hand. -/
theorem RBody.toWellBr {l : List Tok} (h : RBody l) : WellBr l := by
  cases h with | single hwb => exact hwb

/-- The newly-added member (toy `RecMapEntry`): a `{ … }` frame over an `RBody` interior, with an
    empty `{}` leaf.  It STORES only the interior's recursive structure (→ `WellBr`), never `Typed`. -/
inductive REntry : List Tok → Prop where
  | mapEmpty : REntry (.oc :: ([] ++ [.cc]))
  | map (interior : List Tok) (h : RBody interior) : REntry (.oc :: (interior ++ [.cc]))

/-! ### Obligation 1 — the DESCENT (toy `RecMapEntry.map_interior`), the lemma the joint forced -/

/-- The single-level descent: a located `REntry` interior is an `RBody` or empty.  Verbatim toy of
    `RecMapEntry.map_interior` — `e` general, the shape supplied as a separate `h_eq`, and the
    interior read off the constructor index by `append_singleton_inj`. -/
theorem REntry.descent {e interior : List Tok}
    (h : REntry e) (h_eq : e = .oc :: (interior ++ [.cc])) : RBody interior ∨ interior = [] := by
  cases h with
  | mapEmpty =>
      right
      injection h_eq with _h1 h2
      simp only [List.nil_append] at h2
      exact (append_singleton_inj h2.symm).1
  | map interior' h' =>
      left
      injection h_eq with _h1 h2
      exact (append_singleton_inj h2).1 ▸ h'

/-! ### Obligation 2 — the PROJECTION (toy `RecMapEntry.toWellBracketed`), R244's verbatim mirror -/

/-- **The completed projection** (R244): `REntry → WellBr`, a verbatim mirror of the sibling case —
    the `mapEmpty` leaf by computation, the `map` case by `wrapWB` over `RBody.toWellBr` of the
    interior (the sibling projection already proved).  No new analysis. -/
theorem REntry.toWellBr {e : List Tok} (h : REntry e) : WellBr e := by
  cases h with
  | mapEmpty => decide
  | map interior hb => exact wrapWB interior hb.toWellBr

/-! ## The caveat — no `Typed` projection exists, because `Typed` is not a stored field -/

/-- `WellBr` does NOT imply `Typed`: `[os, cc]` (square open, curly close) is count-balanced but
    mistyped.  The stored projection is strictly weaker than the desired one. -/
theorem wellBr_not_typed : WellBr [.os, .cc] ∧ ¬ Typed [.os, .cc] := by decide

/-- ...and the gap survives the wrap: an entry built over a `WellBr`-but-mistyped interior is `WellBr`
    yet not `Typed` (`{ [ } }`), so no `REntry.toTyped` can be recovered from the stored `WellBr`. -/
theorem entry_wellBr_not_typed :
    WellBr [.oc, .os, .cc, .cc] ∧ ¬ Typed [.oc, .os, .cc, .cc] := by decide

/-- **No typing projection from the stored field.**  There is no total `WellBr → Typed`, which is
    exactly why the locate recovers `.wt` *positionally* (toy `WellTyped_subrange`) and never as a
    projection of the recursive deliverable. -/
theorem no_typed_from_wellBr : ¬ ∀ l : List Tok, WellBr l → Typed l := by
  intro h
  have h25 := h [.os, .cc] (by decide)
  revert h25; decide

/-! ## Positive witnesses — the projection fires; both `WellBr` and `Typed` hold where both should -/

/-- A well-formed entry over interior `[a]`: `{ a }`.  Its interior is `RBody` (toy sibling). -/
theorem entry_ab : REntry [.oc, .a, .cc] := .map [.a] (.single [.a] (by decide))

/-- ...and the completed projection yields its `WellBr`. -/
theorem entry_ab_wellBr : WellBr [.oc, .a, .cc] := entry_ab.toWellBr

/-- The empty leaf `{}` is both `WellBr` and `Typed`. -/
theorem mapEmpty_wellBr_typed : WellBr [.oc, .cc] ∧ Typed [.oc, .cc] := by decide

-- Decidable sanity checks (fail the build if any witness drifts).
#guard decide (WellBr [.os, .cc]) = true            -- count-balanced...
#guard decide (Typed [.os, .cc]) = false             -- ...but mistyped: WellBr ⊉ Typed
#guard decide (WellBr [.oc, .os, .cc, .cc]) = true   -- the gap survives the wrap
#guard decide (Typed [.oc, .os, .cc, .cc]) = false
#guard decide (WellBr [.oc, .a, .cc]) = true         -- the projected entry is WellBr
#guard decide (Typed [.oc, .a, .cc]) = true          -- and well-typed where it should be
#guard decide (WellBr [.oc, .cc]) = true             -- the empty leaf is both
#guard decide (Typed [.oc, .cc]) = true

end ProjectionFamilyCompletion
