/-!
# Reflection 397 — a new orthogonal invariant field: land its closure ALGEBRA first,
mirrored on the sibling, before the value-induction; the closure bridge names the producer debt.

Self-contained core-Lean toy of L4YAML R397, the increment after R396's produce-side joint
isolated the seq-axis producer's residual to ONE field `OpenerAdj` (every `.flowSequenceStart`
opener with a non-close successor is followed by a content-start).

De-risk question: does the existing block carrier (`EntrySafe`/`WellBracketed`/`SafeBody`) already
supply `OpenerAdj`?  Answer it from the carrier's CONJUNCTS, not its lemmas: those predicates track
flow-bracket BALANCE and `.flowEntry` SEPARATORS — STRUCTURALLY ORTHOGONAL to `.flowSequenceStart`
OPENERS.  So a NEW field is needed, and the green increment is the field's standalone LIST ALGEBRA
(base + prepend + concat), mirrored on the sibling field's algebra, landed BEFORE the value-induction
that threads it.

POSITIVE: `OpenerAdj_nil`/`_singleton` (base), `OpenerAdj_cons` (prepend = the seq-wrap),
`OpenerAdj_append` (concat with a tail bridge); `openerAdj_goodSeq` composes them into a real
`[ content ]` block.
NEGATIVE 1 (bridge load-bearing): `appendNeedsBridge` — dropping the tail bridge, two opener-adjacent
lists can join into a non-opener-adjacent one (opener-tail before a non-content head).
NEGATIVE 2 (orthogonality / the de-risk): `openerAdj_badBalanced_false` with `#guard balance == 0` —
a flow-bracket-BALANCED list need not be opener-adjacent, so a balance predicate cannot project to
`OpenerAdj`; the new field is genuinely independent.

Mapping to L4YAML: `OpenerAdj` ~ `OpenerAdj` (`WellBracketed.lean`); the four lemmas ~ the same;
`balance` ~ `pbalance`; `badBalanced` ~ a `[ , ]`-shaped emitter-impossible but balanced fragment.
-/

namespace Tests.Reflections.OrthogonalInvariantAlgebraBeforeThreading

set_option autoImplicit false

inductive Tok | opn | cls | content | sep
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A content-start token (= `isFlowContentStart`): content, or a sequence opener. -/
def isContentStart (t : Tok) : Prop := t = .content ∨ t = .opn

/-- **The new field** (= `OpenerAdj`).  Every `.opn` opener with a non-`.cls` successor is
    followed by a content-start.  All-depth, ungated; pure list combinatorics. -/
def OpenerAdj (l : List Tok) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length),
    (l[k]'(by omega)) = .opn → (l[k+1]'h) ≠ .cls → isContentStart (l[k+1]'h)

/-- Base: the empty body is opener-adjacent (vacuous). -/
theorem OpenerAdj_nil : OpenerAdj [] := by intro k h; simp at h

/-- Base: a singleton block is opener-adjacent (no successor index). -/
theorem OpenerAdj_singleton (t : Tok) : OpenerAdj [t] := by intro k h; simp at h

/-- **Fundamental prepend brick** (= `OpenerAdj_cons`); also the seq-wrap with the opener head. -/
theorem OpenerAdj_cons (t : Tok) (rest : List Tok) (h_rest : OpenerAdj rest)
    (h_head : t = .opn → ∀ (h0 : 0 < rest.length),
       (rest[0]'h0) ≠ .cls → isContentStart (rest[0]'h0)) :
    OpenerAdj (t :: rest) := by
  intro k hk hopen hne
  match k with
  | 0 =>
    have hr0 : 0 < rest.length := by simp [List.length_cons] at hk; omega
    rw [List.getElem_cons_zero] at hopen
    rw [List.getElem_cons_succ] at hne ⊢
    exact h_head hopen hr0 hne
  | k'+1 =>
    have hrk : k' + 1 < rest.length := by simp [List.length_cons] at hk; omega
    rw [List.getElem_cons_succ] at hopen
    rw [List.getElem_cons_succ] at hne ⊢
    exact h_rest k' hrk hopen hne

/-- **Concat closure with the tail bridge** (= `OpenerAdj_append`).  The bridge `h_tail`
    (a's last token ≠ opener) is the producer's per-block debt; it makes the boundary vacuous. -/
theorem OpenerAdj_append (a b : List Tok) (ha : OpenerAdj a) (hb : OpenerAdj b)
    (h_tail : ∀ (hla : 0 < a.length), (a[a.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn) :
    OpenerAdj (a ++ b) := by
  intro k hk hopen hne
  have hlen : (a ++ b).length = a.length + b.length := by rw [List.length_append]
  rcases Nat.lt_or_ge (k + 1) a.length with hk1 | hge1
  · have e_k : (a ++ b)[k]'(by omega) = a[k]'(by omega) := List.getElem_append_left (by omega)
    have e_k1 : (a ++ b)[k+1]'hk = a[k+1]'hk1 := List.getElem_append_left hk1
    rw [e_k1]; rw [e_k] at hopen; rw [e_k1] at hne
    exact ha k hk1 hopen hne
  · rcases Nat.lt_or_ge k a.length with hka | hkb
    · exfalso
      have hka' : k = a.length - 1 := by omega
      have e_k : (a ++ b)[k]'(by omega) = a[k]'hka := List.getElem_append_left hka
      rw [e_k] at hopen
      simp only [hka'] at hopen
      exact h_tail (by omega) hopen
    · obtain ⟨m, hm⟩ : ∃ m, k = a.length + m := ⟨k - a.length, by omega⟩
      subst hm
      have hmb1 : m + 1 < b.length := by rw [hlen] at hk; omega
      have e_k : (a ++ b)[a.length + m]'(by omega) = b[m]'(by omega) := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      have e_k1 : (a ++ b)[a.length + m + 1]'hk = b[m+1]'hmb1 := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      rw [e_k1]; rw [e_k] at hopen; rw [e_k1] at hne
      exact hb m hmb1 hopen hne

/-- **POSITIVE — the bricks compose into a real `[ content ]` seq block.**  `[.opn, .content, .cls]`
    = opener-wrap of `[.content] ++ [.cls]`; the interior is concat-closed (tail `.content` ≠ opener)
    and the opener's successor `.content` is a content-start. -/
def goodSeq : List Tok := [.opn, .content, .cls]

theorem openerAdj_goodSeq : OpenerAdj goodSeq := by
  have h_inner : OpenerAdj ([Tok.content, Tok.cls]) :=
    OpenerAdj_cons .content [.cls] (OpenerAdj_singleton _)
      (by intro hc; exact absurd hc (by decide))
  exact OpenerAdj_cons .opn [.content, .cls] h_inner
    (by intro _ h0 _; exact Or.inl rfl)

/-- **NEGATIVE 1 — the tail bridge is load-bearing.**  Without it, `a = [.content, .opn]` (vacuously
    opener-adjacent: its only opener is the last token) joined before `b = [.sep]` yields
    `[.content, .opn, .sep]`, where the opener at index 1 is followed by `.sep` — not a content-start. -/
theorem appendNeedsBridge :
    ¬ ∀ (a b : List Tok), OpenerAdj a → OpenerAdj b → OpenerAdj (a ++ b) := by
  intro h
  have ha : OpenerAdj ([Tok.content, .opn]) := by
    intro k hk hopen hne
    match k with
    | 0 => rw [List.getElem_cons_zero] at hopen; exact absurd hopen (by decide)
    | k'+1 =>
      exfalso
      have hlen : ([Tok.content, Tok.opn] : List Tok).length = 2 := rfl
      omega
  have hbad := h [.content, .opn] [.sep] ha (OpenerAdj_singleton _)
  have hviol := hbad 1 (by decide) (by decide) (by decide)
  simp only [isContentStart] at hviol
  rcases hviol with hc | hc <;> exact absurd hc (by decide)

/-- A flow-bracket balance (= `pbalance`): `.opn` +1, `.cls` -1, others 0. -/
def tokDelta : Tok → Int | .opn => 1 | .cls => -1 | _ => 0
def balance (l : List Tok) : Int := (l.map tokDelta).foldl (· + ·) 0

/-- **NEGATIVE 2 — orthogonality (the de-risk).**  `[.opn, .sep, .cls]` is flow-bracket BALANCED
    (`balance = 0`) yet NOT opener-adjacent (the opener's successor `.sep` is not a content-start).
    So a balance predicate cannot project to `OpenerAdj`; the new field is genuinely independent. -/
def badBalanced : List Tok := [.opn, .sep, .cls]

theorem openerAdj_badBalanced_false : ¬ OpenerAdj badBalanced := by
  intro h
  have hviol := h 0 (by decide) (by decide) (by decide)
  simp only [isContentStart] at hviol
  rcases hviol with hc | hc <;> exact absurd hc (by decide)

#guard balance badBalanced == 0            -- balanced ...
#guard goodSeq.length == 3
#guard badBalanced[1]! == Tok.sep          -- ... but the opener's successor is .sep (not content-start)

end Tests.Reflections.OrthogonalInvariantAlgebraBeforeThreading
