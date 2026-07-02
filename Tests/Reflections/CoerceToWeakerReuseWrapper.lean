import Tests.Reflections.RebaseFactFromEnclosingWindow

/-!
# Reflection 306 — reuse the WEAKER structure's existing wrapper via a strong→weak COERCION, not a mirrored wrapper

Self-contained (core Lean) toy of `(i'-b-encfacts)`'s move
(`SafeBodyUnit_safeBody` + `seqInteriorFeContentStart_of_windowed_safebodyunit`).

The real situation: a needed fact (interior `feContentStart` — a separator is followed by content) has
*exactly the shape* of an EXISTING wrapper (`SafeBody_array_flowEntry_window`), but that wrapper
consumes the WEAKER `SafeBody`, while the substrate in hand is the STRONGER `SafeBodyUnit` (the
producer's natural deliverable — one `emit v` is one *unit* entry).  The instinct is to MIRROR the
wrapper onto the stronger type.  The better move: COERCE the stronger substrate down to the weaker one
and reuse the wrapper — the coercion is cheap because `SafeBodyUnit`'s extra strength is *more of the
same constraint* (`EntryUnit`'s `≥ 1` for ALL proper prefixes subsumes `EntrySafe`'s `≥ 1` only at
separators) for every interior position, leaving ONLY the head gap, which the inductive's own
`Q`-head field (with `hQ : Q v → v ≠ sep`) closes.

Toy: `EntS`/`EntW` are the per-entry refinements (`EntryUnit`/`EntrySafe`).  `entS_entW` is the
coercion's per-entry half — its only non-vacuous obligation is the head, closed by `hQ`.  `BodyS`/
`BodyW` are the bodies; `bodyS_bodyW` is the structural coercion (toy `SafeBodyUnit_safeBody`).  The
WRAPPER `bodyW_headQ` is proven ONCE on the weak type; `bodyS_headQ` obtains the same fact for the
STRONG type by `bodyW_headQ ∘ bodyS_bodyW` — reuse, not re-prove.

NEGATIVE — the head gap is REAL: `EntS [sep]` holds (a lone separator IS a unit entry) but
`¬ EntW [sep]` (it is NOT a safe entry — its head is a depth-`0` separator).  So without the `Q`-head /
`hQ`, the coercion is FALSE; `hQ` is load-bearing.
-/

namespace Tests.Reflections.CoerceToWeakerReuseWrapper

set_option autoImplicit false

open Tests.Reflections.RebaseFactFromEnclosingWindow

/-- Toy `ContentStartTok`: a content token or an opener — never the separator `sep`. -/
def Qhead (t : Tok) : Prop := t = .con ∨ t = .opn

theorem Qhead_not_sep : ∀ t, Qhead t → isSep t = false := by
  rintro t (rfl | rfl) <;> rfl

/-- **Weak entry** (toy `EntrySafe`): balanced, every `sep` position has prefix-balance `≥ 1`. -/
def EntW (e : List Tok) : Prop :=
  psum e e.length = 0 ∧ ∀ i, i < e.length → isSep (e[i]!) = true → 1 ≤ psum e i

/-- **Strong entry** (toy `EntryUnit`): balanced, every PROPER nonempty prefix has balance `≥ 1`.
    Strengthens `EntW` at every interior position — but says nothing about the head. -/
def EntS (e : List Tok) : Prop :=
  psum e e.length = 0 ∧ ∀ i, 0 < i → i < e.length → 1 ≤ psum e i

/-- **The coercion's per-entry half** (toy `EntryUnit_entrySafe`): a `Q`-headed strong entry is weak.
    The ONLY gap is the head (`i = 0`): `EntW` would need `psum (take 0) = 0 ≥ 1` if the head were a
    `sep`, which `EntS` alone permits; the `Q`-head + `hQ` forbids a `sep` head, closing it. -/
theorem entS_entW (Q : Tok → Prop) (hQ : ∀ t, Q t → isSep t = false)
    (e : List Tok) (h_ne : e ≠ []) (h_unit : EntS e) (h_head : Q (e.head h_ne)) : EntW e := by
  refine ⟨h_unit.1, fun i hi h_sep => ?_⟩
  rcases Nat.eq_zero_or_pos i with rfl | hipos
  · -- head case: `e[0]! = e.head` would be a `sep`, contradicting the `Q`-head.
    exfalso
    obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h_ne
    rw [List.head_cons] at h_head
    rw [show ((x :: xs)[0]!) = x from rfl] at h_sep
    rw [hQ x h_head] at h_sep
    exact absurd h_sep (by simp)
  · -- interior: `EntS`'s proper-prefix condition gives `≥ 1` directly.
    exact h_unit.2 i hipos hi

/-! ## NEGATIVE — the head gap is real: `EntS [sep]` but `¬ EntW [sep]`. -/

theorem entS_sep : EntS [Tok.sep] := by
  refine ⟨by decide, fun i h0 h1 => ?_⟩
  exfalso; simp only [List.length_singleton] at h1; omega

theorem not_entW_sep : ¬ EntW [Tok.sep] := by
  intro h
  have hcontra := h.2 0 (by decide) (by decide)
  simp only [psum, List.take_zero, List.foldl_nil] at hcontra
  omega

/-! ## The body inductives and the structural coercion (toy `SafeBodyUnit_safeBody`). -/

/-- **Strong body** (toy `SafeBodyUnit`): nonempty `Q`-headed `EntS` entries, `sep`-separated. -/
inductive BodyS (Q : Tok → Prop) : List Tok → Prop
  | single (e : List Tok) (h_ne : e ≠ []) (h_unit : EntS e) (h_head : Q (e.head h_ne)) : BodyS Q e
  | cons (e rest : List Tok) (h_ne : e ≠ []) (h_unit : EntS e) (h_head : Q (e.head h_ne))
      (h_rest : BodyS Q rest) : BodyS Q (e ++ Tok.sep :: rest)

/-- **Weak body** (toy `SafeBody`): the same shape with the weaker `EntW` per-entry refinement. -/
inductive BodyW (Q : Tok → Prop) : List Tok → Prop
  | single (e : List Tok) (h_ne : e ≠ []) (h_unit : EntW e) (h_head : Q (e.head h_ne)) : BodyW Q e
  | cons (e rest : List Tok) (h_ne : e ≠ []) (h_unit : EntW e) (h_head : Q (e.head h_ne))
      (h_rest : BodyW Q rest) : BodyW Q (e ++ Tok.sep :: rest)

/-- **The structural coercion** (toy `SafeBodyUnit_safeBody`): `BodyS Q → BodyW Q`, given `hQ`.
    A two-constructor induction reusing `entS_entW` per entry — the strong body satisfies the weaker
    one, unlocking the WEAK type's wrapper library on the STRONG substrate. -/
theorem bodyS_bodyW (Q : Tok → Prop) (hQ : ∀ t, Q t → isSep t = false)
    {l : List Tok} (h : BodyS Q l) : BodyW Q l := by
  induction h with
  | single e h_ne h_unit h_head =>
      exact BodyW.single e h_ne (entS_entW Q hQ e h_ne h_unit h_head) h_head
  | cons e rest h_ne h_unit h_head h_rest ih =>
      exact BodyW.cons e rest h_ne (entS_entW Q hQ e h_ne h_unit h_head) h_head ih

/-! ## The WRAPPER proven ONCE on the weak type, then REUSED on the strong type via the coercion. -/

/-- **The wrapper** (toy of an existing `SafeBody`-keyed lemma, e.g. `SafeBody.head_Q`): proven on the
    WEAK type.  In the real proof this is `SafeBody_array_flowEntry_window` — a heavier induction you
    specifically avoid duplicating onto the stronger type. -/
theorem bodyW_headQ (Q : Tok → Prop) {l : List Tok} (h : BodyW Q l) :
    ∃ (h_ne : l ≠ []), Q (l.head h_ne) := by
  cases h with
  | single e h_ne h_unit h_head => exact ⟨h_ne, h_head⟩
  | cons e rest h_ne h_unit h_head h_rest =>
      obtain ⟨x, xs, rfl⟩ := List.exists_cons_of_ne_nil h_ne
      exact ⟨by simp, by simpa using h_head⟩

/-- **THE PAYOFF** (toy of `seqInteriorFeContentStart_of_windowed_safebodyunit`): the wrapper's fact for
    the STRONG body, obtained by `bodyW_headQ ∘ bodyS_bodyW` — REUSE, not a mirrored wrapper. -/
theorem bodyS_headQ (Q : Tok → Prop) (hQ : ∀ t, Q t → isSep t = false)
    {l : List Tok} (h : BodyS Q l) : ∃ (h_ne : l ≠ []), Q (l.head h_ne) :=
  bodyW_headQ Q (bodyS_bodyW Q hQ h)

/-! ## POSITIVE — a concrete `Q`-headed strong body, and the reused wrapper fact. -/

theorem entS_con : EntS [Tok.con] := by
  refine ⟨by decide, fun i h0 h1 => ?_⟩
  exfalso; simp only [List.length_singleton] at h1; omega

def goodBody : List Tok := [Tok.con, Tok.sep, Tok.con]

theorem bodyS_good : BodyS Qhead goodBody := by
  have h_tail : BodyS Qhead [Tok.con] :=
    BodyS.single [Tok.con] (by decide) entS_con (Or.inl rfl)
  show BodyS Qhead ([Tok.con] ++ Tok.sep :: [Tok.con])
  exact BodyS.cons [Tok.con] [Tok.con] (by decide) entS_con (Or.inl rfl) h_tail

-- The wrapper fact for the STRONG body, via the coercion (not re-proved on `BodyS`):
example : ∃ (h_ne : goodBody ≠ []), Qhead (goodBody.head h_ne) :=
  bodyS_headQ Qhead Qhead_not_sep bodyS_good

end Tests.Reflections.CoerceToWeakerReuseWrapper
