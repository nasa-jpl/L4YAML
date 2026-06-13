/-!
# Reflection 401 / 402 — pre-stage a consumer's DERIVABLE boundary side-inputs as a separate
green increment before an atomic orthogonal-field threading.

R401 stages the seq-side body head+tail fields (`a ++ [sep] ++ rest` shape).  R402 MIRRORS it
on the map side: the map wrap SHEDS the head (one field, not two), and the *singleton* map body
is a DISTINCT right-append `a ++ b` (`b ≠ []`) shape that the seam helper does not cover — it
needs its own `lastNotOpener_append_right`, with `b`'s non-emptiness coming free from the value's
content-start head existential.
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

/-- **POSITIVE — the R402 right-append shape `a ++ b` with `b ≠ []`** (the map *singleton*
    body `block_kc ++ block_v`, ending in the value block).  Once `b ≠ []`, `getLast?_append`
    short-circuits to `b.getLast?`, so `b`'s tail field transfers.  This is a DISTINCT shape from
    `a ++ [sep] ++ rest` — the seam helper does NOT cover it, so the mirror needs its own brick. -/
theorem lastNotOpener_append_right (a b : List Tok) (hb : b ≠ [])
    (h_b : ∀ (hla : 0 < b.length), (b[b.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn) :
    ∀ (hla : 0 < (a ++ b).length),
      ((a ++ b)[(a ++ b).length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn := by
  obtain ⟨t, h_gl, h_t⟩ := getLast?_not_opener_of_lastNotOpener b hb h_b
  have h_gl_ab : (a ++ b).getLast? = some t := by rw [List.getLast?_append, h_gl]; rfl
  exact lastNotOpener_of_getLast? _ t h_gl_ab h_t

/-- A body predicate carrying the DERIVABLE boundary side-input (the tail-not-opener field). -/
def BodyTailOk (l : List Tok) : Prop :=
  ∀ (hla : 0 < l.length), (l[l.length - 1]'(Nat.sub_lt hla Nat.one_pos)) ≠ .opn

/-- **POSITIVE — the cons-seam producer**: `block₁ ++ [sep] ++ block_rest` keeps the side-input
    from the IH's tail field + `sep ≠ opener` (the R401 list-body cons-arm discharge in miniature).
    No `OpenerAdj` ("F") is needed to land this — the side-input is strictly weaker and derivable. -/
theorem bodyTailOk_cons (block₁ block_rest : List Tok) (h_rest : BodyTailOk block_rest) :
    BodyTailOk (block₁ ++ [Tok.sep] ++ block_rest) :=
  lastNotOpener_append3 block₁ block_rest Tok.sep (by decide) h_rest

/-- **POSITIVE — the R402 map *singleton* producer** keeps the side-input off the value block's
    tail.  The value block `block_v` is non-empty (in the real proof from its content-start head
    existential, here `hb`), and the map wrap SHEDS the head, so only the tail side-input is
    pre-staged: one field, vs the seq cons-arm's two. -/
theorem bodyTailOk_singletonMap (key value : Tok) (block_k block_v : List Tok)
    (hb : block_v ≠ []) (h_v : BodyTailOk block_v) :
    BodyTailOk ((key :: (block_k ++ [value])) ++ block_v) :=
  lastNotOpener_append_right _ block_v hb h_v

/-- **NEGATIVE — the field is a genuine CONSTRAINT, not vacuous.**  An opener-tailed body fails
    `BodyTailOk`, so the producer can supply it only because emitter bodies end in a close/scalar/sep;
    and the `h_sep` premise of `lastNotOpener_append3` is NECESSARY (a `.opn` seam with empty `rest`
    tails in `.opn`). -/
theorem singleton_opn_fails_BodyTailOk : ¬ BodyTailOk [Tok.opn] := by
  intro h; exact (h (by decide)) rfl

/-- **NEGATIVE — the `b ≠ []` premise of `lastNotOpener_append_right` is NECESSARY.**  Drop it and
    the claim is FALSE: `[content, opn] ++ [] = [content, opn]` tails in `.opn`, yet `[]` vacuously
    satisfies `BodyTailOk`.  So the value block's non-emptiness (from its content-start head
    existential) is load-bearing for the right-append shape, not decoration. -/
theorem append_right_needs_nonempty :
    ¬ BodyTailOk ([Tok.content, Tok.opn] ++ ([] : List Tok)) := by
  intro h; exact (h (by decide)) rfl

-- A genuine body (`content ++ sep ++ cls`) ends in a non-opener; the opener-tailed cases do not.
#guard (([Tok.content] ++ [Tok.sep] ++ [Tok.cls]).getLast? == some Tok.cls)
#guard (([Tok.opn, .content, .cls]).getLast? == some Tok.cls)
#guard (([Tok.sep, .opn]).getLast? == some Tok.opn)
-- the `h_sep`-necessity witness: a `.opn` seam with empty `rest` tails in `.opn`.
#guard (([Tok.content] ++ [Tok.opn] ++ ([] : List Tok)).getLast? == some Tok.opn)

end Tests.Reflections.PrestageConsumerBoundaryFacts
