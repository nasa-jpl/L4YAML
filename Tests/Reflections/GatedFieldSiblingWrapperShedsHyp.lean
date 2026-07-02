/-!
# Reflection 398 — a gated invariant field's sibling wrappers shed hypotheses by the gate:
the head that fails the gate discharges the whole head obligation.

Self-contained core-Lean toy of L4YAML R398, the composite-wrapper increment after R397 landed
the base algebra (`OpenerAdj_nil`/`_singleton`/`_cons`/`_append`) of the gated field `OpenerAdj`
(every `.flowSequenceStart` opener with a non-close successor is followed by a content-start).

The value-induction over emitted values has a SEQ arm (block `[ body ]`, head `[`) and a MAP arm
(block `{ body }`, head `{`).  Build BOTH composite wrappers before the induction, and read each
one's hypotheses off the gate-vs-head match — the field is GATED on the seq opener, so:
- the SEQ wrapper (head SATISFIES the gate) owes the body-head content-start + the close-exclusion;
- the MAP wrapper (head FAILS the gate) SHEDS the whole head obligation (cons head premise vacuous).

POSITIVE A (`openerAdj_seqEmpty`): the empty seq `[ ]` via the seq wrapper (close-exclusion path).
POSITIVE B (`openerAdj_mapShedsHead`): `{ [sep] }` is opener-adjacent via the map wrapper EVEN THOUGH
  the body head `.sep` is not a content-start — the head obligation is genuinely shed.
NEGATIVE (`openerAdj_seqSameBody_false`): swap ONLY the opener — `[ [sep] ]` (seq head) is NOT
  opener-adjacent, so the seq wrapper's `h_head` is load-bearing.  The `#guard`s confirm the two
  blocks differ only at index 0 (the opener); the gate alone flips the head obligation on/off.

Mapping to L4YAML: `OpenerAdj` ~ `OpenerAdj` (`WellBracketed.lean`); the two wrappers ~
`OpenerAdj_wrap_seq`/`OpenerAdj_wrap_map`; `.opn` ~ `.flowSequenceStart`, `.mapOpn` ~ `.flowMappingStart`.
-/

namespace Tests.Reflections.GatedFieldSiblingWrapperShedsHyp

set_option autoImplicit false

/-- Two opener kinds: `.opn` is the SEQ opener (the field's gate trigger); `.mapOpn`
    is the MAP opener (does NOT trigger the gate). Plus a close, content, separator. -/
inductive Tok | opn | mapOpn | cls | content | sep
  deriving DecidableEq, Repr, BEq, Inhabited

/-- A content-start token (= `isFlowContentStart`): content, or either opener. -/
def isContentStart (t : Tok) : Prop := t = .content ∨ t = .opn ∨ t = .mapOpn

/-- **The gated field** (= `OpenerAdj`).  Gated on `.opn` ONLY: every `.opn` opener with a
    non-`.cls` successor is followed by a content-start.  `.mapOpn` never triggers it. -/
def OpenerAdj (l : List Tok) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length),
    (l[k]'(by omega)) = .opn → (l[k+1]'h) ≠ .cls → isContentStart (l[k+1]'h)

theorem OpenerAdj_nil : OpenerAdj [] := by intro k h; simp at h

theorem OpenerAdj_singleton (t : Tok) : OpenerAdj [t] := by intro k h; simp at h

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

/-- **Seq wrapper** (= `OpenerAdj_wrap_seq`).  Head `.opn` SATISFIES the gate, so it OWES the
    body-head content-start (`h_head`) and the empty-body close-exclusion (`h_cl`). -/
theorem OpenerAdj_wrap_seq (op cl : Tok) (body : List Tok)
    (_h_op : op = .opn) (h_cl : cl = .cls)
    (h_body : OpenerAdj body)
    (h_head : ∀ (h0 : 0 < body.length),
       (body[0]'h0) ≠ .cls → isContentStart (body[0]'h0))
    (h_tail : ∀ (hla : 0 < body.length),
       (body[body.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn) :
    OpenerAdj (op :: (body ++ [cl])) := by
  have h_rest : OpenerAdj (body ++ [cl]) :=
    OpenerAdj_append body [cl] h_body (OpenerAdj_singleton cl) h_tail
  apply OpenerAdj_cons op (body ++ [cl]) h_rest
  intro _hop h0' hne
  match body, h_head, h_tail, h_body with
  | [], _, _, _ =>
    simp only [List.nil_append, List.getElem_cons_zero] at hne
    exact absurd h_cl hne
  | b0 :: bs, h_head, _, _ =>
    have e0 : ((b0 :: bs) ++ [cl])[0]'h0' = (b0 :: bs)[0]'(by simp) := by
      rw [List.getElem_append_left (by simp)]
    rw [e0] at hne ⊢
    exact h_head (by simp) hne

/-- **Map wrapper** (= `OpenerAdj_wrap_map`).  Head `.mapOpn` FAILS the gate, so the whole head
    obligation is SHED — the cons head premise `op = .opn` is vacuously false.  No `h_head`/`h_cl`. -/
theorem OpenerAdj_wrap_map (op cl : Tok) (body : List Tok)
    (h_op : op = .mapOpn)
    (h_body : OpenerAdj body)
    (h_tail : ∀ (hla : 0 < body.length),
       (body[body.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn) :
    OpenerAdj (op :: (body ++ [cl])) := by
  have h_rest : OpenerAdj (body ++ [cl]) :=
    OpenerAdj_append body [cl] h_body (OpenerAdj_singleton cl) h_tail
  apply OpenerAdj_cons op (body ++ [cl]) h_rest
  intro hop _h0' _hne
  exfalso
  rw [h_op] at hop
  exact absurd hop (by decide)

/-- A singleton body's tail token (the body's only element) is not the `.opn` opener
    when that element isn't `.opn` — the tail-bridge for a one-token body. -/
theorem singleton_tail_ne (t : Tok) (h : t ≠ Tok.opn) :
    ∀ (hla : 0 < [t].length),
       ([t])[([t].length - 1)]'(Nat.sub_lt hla Nat.one_pos) ≠ Tok.opn :=
  fun _ => h

/-- **POSITIVE A — the empty seq `[ ]` via the seq wrapper.**  Body `[]`; the head/tail
    obligations are vacuous and the close-exclusion path (`h_cl`) closes the empty-body head case. -/
theorem openerAdj_seqEmpty : OpenerAdj (Tok.opn :: ([] ++ [Tok.cls])) :=
  OpenerAdj_wrap_seq .opn .cls [] rfl rfl OpenerAdj_nil
    (fun h0 => by simp at h0) (fun hla => by simp at hla)

/-- **POSITIVE B — the map wrapper SHEDS the head obligation.**  `{ [sep] }` = `[mapOpn, sep, cls]`
    is opener-adjacent via `OpenerAdj_wrap_map` EVEN THOUGH the body head `.sep` is NOT a
    content-start: the `.mapOpn` head never triggers the gate, so no head condition is required. -/
theorem openerAdj_mapShedsHead : OpenerAdj (Tok.mapOpn :: ([Tok.sep] ++ [Tok.cls])) :=
  OpenerAdj_wrap_map .mapOpn .cls [.sep] rfl (OpenerAdj_singleton _)
    (singleton_tail_ne .sep (by decide))

/-- **NEGATIVE — swap ONLY the opener and the head obligation flips ON.**  With the SAME body
    `[sep]` and close, the seq-headed analog `[ [sep] ]` = `[opn, sep, cls]` is NOT opener-adjacent:
    the `.opn` head triggers the gate and the successor `.sep` is not a content-start.  So the seq
    wrapper's `h_head` is load-bearing — it could not have been discharged here. -/
theorem openerAdj_seqSameBody_false : ¬ OpenerAdj [Tok.opn, .sep, .cls] := by
  intro h
  have hviol := h 0 (by decide) (by decide) (by decide)
  simp only [isContentStart] at hviol
  rcases hviol with hc | hc | hc <;> exact absurd hc (by decide)

-- The two blocks differ ONLY at index 0 (the opener): same body `.sep`, same close.
#guard ([Tok.mapOpn, .sep, .cls])[1]! == ([Tok.opn, .sep, .cls])[1]!   -- both .sep
#guard ([Tok.mapOpn, .sep, .cls])[2]! == ([Tok.opn, .sep, .cls])[2]!   -- both .cls
#guard ([Tok.mapOpn, .sep, .cls])[0]! != ([Tok.opn, .sep, .cls])[0]!   -- only the opener differs

end Tests.Reflections.GatedFieldSiblingWrapperShedsHyp
