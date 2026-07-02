/-!
# Reflection 312 — a type-blind numeric invariant cannot CREATE a typed fact (fold-definedness); it only licenses its TRANSPORT across a frame boundary, and moving definedness from a verified LARGER context to a SMALLER sub-context needs the CONVERSE of the forward framing lemma

Self-contained (core Lean) toy of the moment `(i'-b-locator-glue-opener-type)` was authored.

The brick: from the located innermost opener `p` (its body has numeric balance `0` and a `≥ 0`
floor) plus the gate's typed-stack head `= true`, conclude `tokens[p]` is a seq opener.  The
structural core is that the interior body never pops the bit `p` pushed, so the stack head at the
window start is that bit — fixed to `true` by the gate.

The 159th "Next step" predicted **route (B)**: "prove the interior fold from the singleton frame
`[b]` returns to `[b]` *from the floor*, then extend by the FORWARD frame lemma."  Authoring
corrected it: **the floor cannot prove the interior fold is even DEFINED** — the floor is NUMERIC
(`pbal`), and a numeric invariant is TYPE-BLIND.  Definedness comes only from the real (well-typed)
stream, i.e. from the gate's whole-prefix fold; and moving that definedness DOWN to the interior
sub-fold needs the CONVERSE of the forward frame lemma, not the forward one.

Tokens are a 5-symbol typed-bracket alphabet (`os`/`om` push a `true`/`false`; `cs`/`cm` pop a
matching `true`/`false` or fail; `nt` is neutral).  `step`/`fold` are the typed stack machine;
`pbal` is the numeric balance.

**Correction 1 (NEGATIVE, `#guard`-backed — the floor is TYPE-BLIND).** `[os, cm]` (a seq-open
then a map-close, the `[ }` analog) has every prefix balance `≥ 0` and total balance `0` (so it
passes BOTH the floor and the balance-0 test route (B) relied on), yet `fold (some []) [os, cm] =
none` — the `}` cannot pop the `[`.  So no floor/balance reasoning yields fold-definedness; that is
a typed fact only the real stream supplies.

**Correction 2 (POSITIVE, the forward/converse asymmetry).** `fold_frame` (forward) needs NO
numeric hypothesis: it carries a proven SMALL fold up to a larger frame.  `fold_frame_inv` (the
converse) DOES need the floor: it transports DEFINEDNESS down from the larger frame to the smaller,
and dropping frame elements would underflow unless the floor forbids it.  A property and its
converse over one structure need different invariant strengths — forward is free, the converse is
floor-guarded ([[ref-converse-forward-invariant-asymmetry]]).  Composing the two as the brick does:
the gate gives `fold (some []) whole = some S` (definedness in the large context), `fold_frame_inv`
(with the floor) pushes it down to `fold (some []) interior = some []` (balance-0 ⇒ length 0), and
the head at the window is the opener bit.
-/

namespace Tests.Reflections.TypeBlindInvariantTransportsViaConverseFrame

set_option autoImplicit false

/-- A 5-symbol typed-bracket alphabet: seq/map open, seq/map close, neutral. -/
inductive Tok | os | om | cs | cm | nt
deriving DecidableEq

/-- Numeric bracket delta — TYPE-BLIND: both opens are `+1`, both closes `-1`. -/
def delta : Tok → Int
  | .os => 1 | .om => 1 | .cs => -1 | .cm => -1 | .nt => 0

/-- The TYPED stack step: `os`/`om` push `true`/`false`; `cs`/`cm` pop a *matching* head (or fail);
    `nt` is neutral. -/
def step : Tok → List Bool → Option (List Bool)
  | .os, s => some (true :: s)
  | .om, s => some (false :: s)
  | .cs, s => match s with | true :: r => some r | _ => none
  | .cm, s => match s with | false :: r => some r | _ => none
  | .nt, s => some s

/-- Fold the typed stack across a token list (`none` absorbing via `bind`). -/
def fold (s0 : Option (List Bool)) (l : List Tok) : Option (List Bool) :=
  l.foldl (fun a t => a.bind (step t)) s0

/-- Numeric cumulative balance. -/
def pbal : List Tok → Int
  | [] => 0
  | t :: r => delta t + pbal r

theorem pbal_take_one (t : Tok) (r : List Tok) : pbal ((t :: r).take 1) = delta t := by
  simp [pbal]

theorem fold_cons (s0 : Option (List Bool)) (t : Tok) (r : List Tok) :
    fold s0 (t :: r) = fold (s0.bind (step t)) r := by simp [fold, List.foldl_cons]

theorem fold_cons_some (s : List Bool) (t : Tok) (r : List Tok) :
    fold (some s) (t :: r) = fold (step t s) r := by simp [fold, List.foldl_cons, Option.bind]

theorem fold_none (l : List Tok) : fold none l = none := by
  induction l with
  | nil => rfl
  | cons t r ih => rw [fold_cons]; exact ih

theorem fold_append (s0 : Option (List Bool)) (a b : List Tok) :
    fold s0 (a ++ b) = fold (fold s0 a) b := by simp [fold, List.foldl_append]

/-- One step shifts the stack length by exactly the delta (the `none` cases are excluded). -/
theorem step_length (t : Tok) (s s' : List Bool) (h : step t s = some s') :
    (s'.length : Int) = (s.length : Int) + delta t := by
  cases t <;> simp only [step, delta] at h ⊢ <;>
    first
      | (obtain rfl := Option.some.inj h; simp)
      | (cases s with
         | nil => simp at h
         | cons b s'' => cases b <;> simp_all <;> omega)

/-- A `some`-valued fold shifts length by `pbal` (mirrors `btFold_length`). -/
theorem fold_length (l : List Tok) : ∀ (s0 s1 : List Bool), fold (some s0) l = some s1 →
    (s1.length : Int) = (s0.length : Int) + pbal l := by
  induction l with
  | nil =>
    intro s0 s1 h; simp only [fold, List.foldl_nil] at h
    obtain rfl := Option.some.inj h; simp [pbal]
  | cons t rest ih =>
    intro s0 s1 h
    rw [fold_cons_some] at h
    cases hb : step t s0 with
    | none => rw [hb, fold_none] at h; exact absurd h (by simp)
    | some m =>
      rw [hb] at h
      have hs := step_length t s0 m hb
      have hr := ih m s1 h
      simp only [pbal]; omega

/-! ## NEGATIVE — the floor is type-blind: `[os, cm]` passes floor + balance-0 yet folds to `none`. -/

#guard pbal [Tok.os, Tok.cm] == 0                         -- total balance 0
#guard pbal ([Tok.os, Tok.cm].take 0) == 0                -- prefix balances all ≥ 0
#guard pbal ([Tok.os, Tok.cm].take 1) == 1
#guard pbal ([Tok.os, Tok.cm].take 2) == 0
#guard fold (some []) [Tok.os, Tok.cm] == none            -- yet UNDEFINED (the `}` can't pop the `[`)

/-! ## POSITIVE — forward frame needs no numeric hypothesis. -/

theorem step_frame (t : Tok) (s m extra : List Bool) (h : step t s = some m) :
    step t (s ++ extra) = some (m ++ extra) := by
  cases t <;> simp only [step] at h ⊢ <;>
    first
      | (obtain rfl := Option.some.inj h; rfl)
      | (cases s with
         | nil => simp at h
         | cons b s' => cases b <;> simp_all)

theorem fold_frame (l : List Tok) :
    ∀ (s m extra : List Bool), fold (some s) l = some m →
      fold (some (s ++ extra)) l = some (m ++ extra) := by
  induction l with
  | nil =>
    intro s m extra h
    simp only [fold, List.foldl_nil] at h ⊢
    obtain rfl := Option.some.inj h; rfl
  | cons t rest ih =>
    intro s m extra h
    rw [fold_cons_some] at h ⊢
    cases hb : step t s with
    | none => rw [hb, fold_none] at h; exact absurd h (by simp)
    | some m' =>
      rw [hb] at h
      rw [step_frame t s m' extra hb]
      exact ih m' m extra h

/-! ## POSITIVE — the CONVERSE (frame inverse) needs the floor to transport definedness DOWN. -/

theorem step_frame_inv (t : Tok) (s extra M : List Bool)
    (h_nopop : 0 ≤ (s.length : Int) + delta t)
    (h : step t (s ++ extra) = some M) :
    ∃ n, step t s = some n ∧ M = n ++ extra := by
  cases t <;> simp only [step, delta] at h h_nopop ⊢ <;>
    first
      | (obtain rfl := Option.some.inj h; exact ⟨_, rfl, rfl⟩)
      | (cases s with
         | nil => simp only [List.length_nil] at h_nopop; omega
         | cons b s' => cases b <;> simp_all)

theorem fold_frame_inv (l : List Tok) :
    ∀ (s extra m' : List Bool),
      (∀ k, k ≤ l.length → 0 ≤ (s.length : Int) + pbal (l.take k)) →
      fold (some (s ++ extra)) l = some m' →
      ∃ m, fold (some s) l = some m ∧ m' = m ++ extra := by
  induction l with
  | nil =>
    intro s extra m' _ h
    simp only [fold, List.foldl_nil] at h ⊢
    exact ⟨s, rfl, (Option.some.inj h).symm⟩
  | cons t rest ih =>
    intro s extra m' hfloor h
    rw [fold_cons_some] at h
    have h_nopop : 0 ≤ (s.length : Int) + delta t := by
      have h1 := hfloor 1 (by simp)
      rw [pbal_take_one] at h1; exact h1
    cases hb : step t (s ++ extra) with
    | none => rw [hb, fold_none] at h; exact absurd h (by simp)
    | some M =>
      rw [hb] at h
      obtain ⟨n, hn, hMn⟩ := step_frame_inv t s extra M h_nopop hb
      rw [fold_cons_some, hn]
      have hstep_len : (n.length : Int) = (s.length : Int) + delta t := step_length t s n hn
      have hfloor' : ∀ k, k ≤ rest.length → 0 ≤ (n.length : Int) + pbal (rest.take k) := by
        intro k hk
        have hh := hfloor (k + 1) (by simp only [List.length_cons]; omega)
        have htk : ((t :: rest).take (k + 1)) = t :: rest.take k := by simp
        rw [htk] at hh
        have : pbal (t :: rest.take k) = delta t + pbal (rest.take k) := by simp [pbal]
        rw [this] at hh
        rw [hstep_len]; omega
      exact ih n extra m' hfloor' (by rw [hMn] at h; exact h)

/-- **The brick, in toy form.**  The gate supplies definedness of the whole fold (`fold (some [])
    whole = some S`); the floor (numeric, type-blind) licenses pushing that definedness DOWN to the
    interior via the CONVERSE frame; balance-0 then collapses the interior result to `[]`, so the
    stack head at the window start is exactly the bit the opener pushed. -/
theorem opener_bit_via_converse_frame (interior : List Tok) (b : Bool) (s_p S : List Bool)
    (h_floor : ∀ k, k ≤ interior.length → 0 ≤ pbal (interior.take k))
    (h_bal : pbal interior = 0)
    (h_whole : fold (some (b :: s_p)) interior = some S) :
    S = b :: s_p := by
  have hfloor' : ∀ k, k ≤ interior.length →
      0 ≤ (([] : List Bool).length : Int) + pbal (interior.take k) := by
    intro k hk; simpa using h_floor k hk
  obtain ⟨m, hm, hSm⟩ :=
    fold_frame_inv interior [] (b :: s_p) S hfloor' (by rw [List.nil_append]; exact h_whole)
  have hm_len : (m.length : Int) = 0 := by
    have hlen := fold_length interior [] m hm
    simpa [h_bal] using hlen
  have hm_nil : m = [] := List.eq_nil_of_length_eq_zero (by exact_mod_cast hm_len)
  rw [hm_nil, List.nil_append] at hSm; exact hSm

end Tests.Reflections.TypeBlindInvariantTransportsViaConverseFrame
