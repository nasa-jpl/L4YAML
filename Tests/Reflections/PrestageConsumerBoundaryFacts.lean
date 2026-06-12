/-!
# Reflection 401 — pre-stage a consumer's DERIVABLE boundary side-inputs as a separate green
increment before an atomic orthogonal-field threading.
-/

namespace Tests.Reflections.PrestageConsumerBoundaryFacts

set_option autoImplicit false

inductive Tok | opn | cls | sep | content
  deriving DecidableEq, Repr, BEq, Inhabited

/-- getLast?⇒getElem bridge: discharge a "last token not opener" fact via `getLast?`. -/
theorem lastNotOpener_of_getLast? (l : List Tok) (t : Tok)
    (h_gl : l.getLast? = some t) (h : t ≠ .opn) :
    ∀ (hla : 0 < l.length), (l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn := by
  intro hla
  have h1 : l[l.length - 1]? = some t := by rw [← List.getLast?_eq_getElem?]; exact h_gl
  rw [List.getElem?_eq_getElem (Nat.sub_lt hla Nat.one_pos)] at h1
  rw [Option.some.inj h1]; exact h

/-- getElem⇒getLast? witness: a stored getElem tail field re-enters the `getLast?` algebra. -/
theorem getLast?_not_opener_of_lastNotOpener (l : List Tok) (hne : l ≠ [])
    (h : ∀ (hla : 0 < l.length), (l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn) :
    ∃ t, l.getLast? = some t ∧ t ≠ .opn := by
  have hla : 0 < l.length := by cases l with | nil => exact absurd rfl hne | cons _ _ => simp
  refine ⟨l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos), ?_, h hla⟩
  rw [List.getLast?_eq_getElem?, List.getElem?_eq_getElem (Nat.sub_lt hla Nat.one_pos)]

/-- **POSITIVE — the EXACT left-associated term shape `a ++ [sep] ++ rest`, discharged purely by
    `getLast?` composition** (`getLast?_append` ⇒ `.or`, `getLast?_concat`), never a list-rewrite
    under the dependent `length - 1` getElem (which would hit "motive is not type correct"). -/
theorem lastNotOpener_append3 (a rest : List Tok) (seam : Tok)
    (h_sep : seam ≠ .opn)
    (h_rest : ∀ (hla : 0 < rest.length),
      (rest[rest.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn) :
    ∀ (hla : 0 < (a ++ [seam] ++ rest).length),
      ((a ++ [seam] ++ rest)[(a ++ [seam] ++ rest).length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn := by
  have hwit : ∃ t, (a ++ [seam] ++ rest).getLast? = some t ∧ t ≠ .opn := by
    cases rest with
    | nil => refine ⟨seam, ?_, h_sep⟩; rw [List.getLast?_append]; simp
    | cons r0 rs =>
      obtain ⟨t, h_gl, h_t⟩ :=
        getLast?_not_opener_of_lastNotOpener (r0 :: rs) (List.cons_ne_nil _ _) h_rest
      refine ⟨t, ?_, h_t⟩; rw [List.getLast?_append, h_gl]; rfl
  obtain ⟨t, h_gl, h_t⟩ := hwit
  exact lastNotOpener_of_getLast? _ t h_gl h_t

/-- A body predicate carrying the DERIVABLE boundary side-input (the tail-not-opener field). -/
def BodyTailOk (l : List Tok) : Prop :=
  ∀ (hla : 0 < l.length), (l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn

/-- **POSITIVE — the cons-seam producer**: `block₁ ++ [sep] ++ block_rest` keeps the side-input
    from the IH's tail field + `sep ≠ opener` (the R401 list-body cons-arm discharge in miniature).
    No `OpenerAdj` ("F") is needed to land this — the side-input is strictly weaker and derivable. -/
theorem bodyTailOk_cons (block₁ block_rest : List Tok) (h_rest : BodyTailOk block_rest) :
    BodyTailOk (block₁ ++ [Tok.sep] ++ block_rest) :=
  lastNotOpener_append3 block₁ block_rest Tok.sep (by decide) h_rest

/-- **NEGATIVE — the field is a genuine CONSTRAINT, not vacuous.**  An opener-tailed body fails
    `BodyTailOk`, so the producer can supply it only because emitter bodies end in a close/scalar/sep;
    and the `h_sep` premise of `lastNotOpener_append3` is NECESSARY (a `.opn` seam with empty `rest`
    tails in `.opn`). -/
theorem singleton_opn_fails_BodyTailOk : ¬ BodyTailOk [Tok.opn] := by
  intro h; exact (h (by decide)) rfl

-- A genuine body (`content ++ sep ++ cls`) ends in a non-opener; the opener-tailed cases do not.
#guard (([Tok.content] ++ [Tok.sep] ++ [Tok.cls]).getLast? == some Tok.cls)
#guard (([Tok.opn, .content, .cls]).getLast? == some Tok.cls)
#guard (([Tok.sep, .opn]).getLast? == some Tok.opn)
-- the `h_sep`-necessity witness: a `.opn` seam with empty `rest` tails in `.opn`.
#guard (([Tok.content] ++ [Tok.opn] ++ ([] : List Tok)).getLast? == some Tok.opn)

end Tests.Reflections.PrestageConsumerBoundaryFacts
