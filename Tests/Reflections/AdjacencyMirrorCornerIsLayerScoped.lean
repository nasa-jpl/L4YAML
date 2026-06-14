/-!
# Reflection 420 — a gated-adjacency mirror's non-cloning BOUNDARY corner (R418) is LAYER-SCOPED:
the token-opaque combinator layer clones VERBATIM under a uniform (trigger, gate) substitution

Self-contained (core Lean, no `L4YAML` import) toy model of the `SepAdj` combinator layer (R420), the
`.flowEntry`/`≠ .key` mirror of the R408 `OpenerAdj` machinery, built to feed the body separator field
`h_body` of the R418 produce-side joint `globalFlowSeqSepAdj_of_structure`.

R418 (`BoundaryDischargeGateTriggerTyped`) warned: do NOT price a gated-adjacency producer mirror by its
skeleton — the pre-close BOUNDARY cell does not clone (its discharge is typed by gate-vs-close ×
trigger-balance).  That is true — but it is about the GLOBAL `…Adj_of_structure` layer, whose boundary
discharge INSPECTS a concrete close token.

This reflection scopes that corner.  The list-COMBINATOR layer BELOW the global producer — the predicate
+ `nil`/`singleton`/`cons`/`append` — clones VERBATIM under a single uniform (trigger, gate) substitution,
because every combinator proof is TOKEN-OPAQUE structural induction over LIST POSITION: it never inspects
the trigger/gate token values (they live only in the premises/conclusion, threaded as opaque hypotheses),
and the `append` boundary case refutes the trigger premise against an ABSTRACT tail-bridge hypothesis
`≠ trigger`, never against a concrete token.

The toy makes the verbatim clone LITERAL via PARAMETRICITY: `adj trig gate` is one predicate parametric
over the trigger/gate, its combinators are ONE proof each, and the two concrete combinators (`adjA`,
trigger `opn`/gate `cls`, and `adjB`, trigger `sep`/gate `key`) are the SAME proof term `adj_append` at
different tokens.  A combinator that clones verbatim in the real code = a combinator whose proof factors
through this single parametric theorem.

* `adj` / `adj_nil` / `adj_singleton` / `adj_cons` / `adj_append` — the token-opaque combinator layer,
  parametric over `(trig, gate)` (toy of `SepAdj` + combinators, which clone `OpenerAdj` verbatim).
* `adjA_append` / `adjB_append`           — the two concrete combinators ARE `adj_append` at two token
                                             pairs: the verbatim clone as ONE shared proof term.
* `global_boundary_needs_concrete_close`  — the NEGATIVE: a global-style pre-close discharge needs an
                                             EXTRA premise `isContent close = false` about the CONCRETE
                                             boundary token, which the token-opaque combinators never
                                             required — the layer where R418's corner classification bites.

Sharpens `BoundaryDischargeGateTriggerTyped` (R418 — the non-cloning corner is confined to the
concrete-token-inspecting layer; the combinator layer below clones totally).
-/

namespace Tests.Reflections.AdjacencyMirrorCornerIsLayerScoped

set_option autoImplicit false

/-- Toy token kinds: seq opener `opn` / closer `cls`, separator `sep`, content scalar `scal`, explicit
    key indicator `key`.  Two adjacency pairs live here: (`opn`, `cls`) for the opener field and
    (`sep`, `key`) for the separator field. -/
inductive Tok where
  | opn | cls | sep | scal | key
  deriving DecidableEq, BEq

/-- A content start: a scalar or an opener (toy of `isFlowContentStart`).  Neither `cls` nor `key` nor
    `sep` is content — the lever the global boundary discharge pulls on the concrete close. -/
def isContent : Tok → Bool
  | .scal | .opn => true
  | _ => false

/-! ## The TOKEN-OPAQUE combinator layer — parametric over the (trigger, gate) pair. -/

/-- A gated adjacency field, PARAMETRIC over the trigger and gate tokens (toy of `OpenerAdj`/`SepAdj`):
    every `trig` whose successor is not `gate` is immediately followed by a content-start.  The proofs
    below never inspect `trig`/`gate` as concrete values — they only thread them as the premises
    `= trig` / `≠ gate` — so ONE parametric proof serves EVERY token pair.  That is precisely why
    `OpenerAdj` and `SepAdj` are verbatim clones: their proofs factor through this parametric theorem. -/
def adj (trig gate : Tok) (l : List Tok) : Prop :=
  ∀ (k : Nat) (h : k + 1 < l.length),
    (l[k]'(by omega)) = trig →
    (l[k+1]'h) ≠ gate →
    isContent (l[k+1]'h) = true

theorem adj_nil (trig gate : Tok) : adj trig gate [] := by
  intro k h; simp at h

theorem adj_singleton (trig gate : Tok) (t : Tok) : adj trig gate [t] := by
  intro k h; simp at h

/-- **Fundamental recursive brick**, parametric over `(trig, gate)`: prepending a token preserves the
    field, given the head bridge.  The `k = 0` boundary is discharged by the ABSTRACT hypothesis
    `h_head`, never by inspecting a concrete token — hence token-opaque. -/
theorem adj_cons (trig gate : Tok) (t : Tok) (rest : List Tok)
    (h_rest : adj trig gate rest)
    (h_head : t = trig →
       ∀ (h0 : 0 < rest.length), (rest[0]'h0) ≠ gate → isContent (rest[0]'h0) = true) :
    adj trig gate (t :: rest) := by
  intro k hk htrig hne
  match k with
  | 0 =>
    have hr0 : 0 < rest.length := by simp [List.length_cons] at hk; omega
    rw [List.getElem_cons_zero] at htrig
    rw [List.getElem_cons_succ] at hne ⊢
    exact h_head htrig hr0 hne
  | k'+1 =>
    have hrk : k' + 1 < rest.length := by simp [List.length_cons] at hk; omega
    rw [List.getElem_cons_succ] at htrig
    rw [List.getElem_cons_succ] at hne ⊢
    exact h_rest k' hrk htrig hne

/-- **Closure under concatenation**, parametric over `(trig, gate)`.  The ONLY boundary case (`a`'s last
    token) is discharged by the ABSTRACT tail-bridge hypothesis `h_tail : a's-last ≠ trig` — never by
    inspecting a concrete token.  This is the combinator analogue of the cell R418 says does not clone at
    the global layer; HERE it clones, because the refutation is against a hypothesis, not a token. -/
theorem adj_append (trig gate : Tok) (a b : List Tok)
    (ha : adj trig gate a) (hb : adj trig gate b)
    (h_tail : ∀ (hla : 0 < a.length),
       (a[a.length-1]'(Nat.sub_lt hla Nat.one_pos)) ≠ trig) :
    adj trig gate (a ++ b) := by
  intro k hk htrig hne
  have hlen : (a ++ b).length = a.length + b.length := by rw [List.length_append]
  rcases Nat.lt_or_ge (k + 1) a.length with hk1 | hge1
  · have e_k : (a ++ b)[k]'(by omega) = a[k]'(by omega) := List.getElem_append_left (by omega)
    have e_k1 : (a ++ b)[k+1]'hk = a[k+1]'hk1 := List.getElem_append_left hk1
    rw [e_k1]; rw [e_k] at htrig; rw [e_k1] at hne
    exact ha k hk1 htrig hne
  · rcases Nat.lt_or_ge k a.length with hka | hkb
    · exfalso
      have hka' : k = a.length - 1 := by omega
      have e_k : (a ++ b)[k]'(by omega) = a[k]'hka := List.getElem_append_left hka
      rw [e_k] at htrig
      simp only [hka'] at htrig
      exact h_tail (by omega) htrig
    · obtain ⟨m, hm⟩ : ∃ m, k = a.length + m := ⟨k - a.length, by omega⟩
      subst hm
      have hmb1 : m + 1 < b.length := by rw [hlen] at hk; omega
      have e_k : (a ++ b)[a.length + m]'(by omega) = b[m]'(by omega) := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      have e_k1 : (a ++ b)[a.length + m + 1]'hk = b[m+1]'hmb1 := by
        rw [List.getElem_append_right (by omega)]; congr 1; omega
      rw [e_k1]; rw [e_k] at htrig; rw [e_k1] at hne
      exact hb m hmb1 htrig hne

/-! ## The verbatim clone, made LITERAL: two concrete combinators = ONE parametric proof term. -/

/-- The "opener" adjacency: trigger `opn`, gate `cls` (toy of `OpenerAdj`). -/
abbrev adjA (l : List Tok) : Prop := adj Tok.opn Tok.cls l
/-- The "separator" adjacency: trigger `sep`, gate `key` (toy of `SepAdj`). -/
abbrev adjB (l : List Tok) : Prop := adj Tok.sep Tok.key l

/-- The opener append-combinator and the separator append-combinator are the SAME proof term
    `adj_append` at two different token pairs — the "verbatim clone" made literal.  In the real code
    `OpenerAdj_append` and `SepAdj_append` are separate source theorems, but each is exactly this
    parametric proof specialised, which is why the mirror needed no proof edits. -/
def adjA_append := adj_append Tok.opn Tok.cls
def adjB_append := adj_append Tok.sep Tok.key

#check (adjA_append : ∀ (a b : List Tok), adjA a → adjA b → _ → adjA (a ++ b))
#check (adjB_append : ∀ (a b : List Tok), adjB a → adjB b → _ → adjB (a ++ b))

/-! ## The layer where the corner BITES — a global-style boundary discharge inspects a CONCRETE token. -/

/-- A global-style pre-close boundary discharge (toy of the `…Adj_of_structure` pre-close cell).  Unlike
    the parametric combinators, it needs an EXTRA premise about the CONCRETE boundary token —
    `isContent close = false` — that the token-opaque combinator layer never required (the combinators
    needed only the abstract `h_tail : ≠ trig`).  This dependence on the concrete token is exactly why
    THIS layer is where R418's corner classification applies, while the combinator layer above clones. -/
theorem global_boundary_needs_concrete_close
    (l : List Tok) (i : Nat) (h : i + 1 < l.length) (close : Tok)
    (h_close : (l[i+1]'h) = close) (h_nc : isContent close = false)
    (h_adj : adjB l) (h_trig : (l[i]'(by omega)) = Tok.sep) (h_gate : (l[i+1]'h) ≠ Tok.key) :
    False := by
  have hc := h_adj i h h_trig h_gate     -- isContent (l[i+1]) = true
  rw [h_close, h_nc] at hc               -- false = true: the discharge consumed the CONCRETE close fact
  exact absurd hc (by decide)

/-- The close supplies the concrete fact the global discharge needs; a content token would not — so the
    global boundary cell is token-CONCRETE, unlike the parametric combinator layer.  (`opn`, a content
    token, could legitimately follow a separator; only a non-content boundary refutes.) -/
example : isContent Tok.cls = false ∧ isContent Tok.scal = true ∧ isContent Tok.opn = true := by decide

/-- And a concrete witness: a `sep` followed by content satisfies `adjB` (no contradiction), so the
    global-style refutation has nothing to land — it works only at the non-content close. -/
def wSepThenContent : List Tok := [Tok.sep, Tok.scal]

theorem adjB_holds_sep_then_content : adjB wSepThenContent := by
  intro k h htrig hne
  have hk0 : k = 0 := by
    have hl : wSepThenContent.length = 2 := rfl
    omega
  subst hk0
  simp only [wSepThenContent, List.getElem_cons_succ, List.getElem_cons_zero, isContent]

#guard isContent Tok.cls == false        -- the close: a global boundary CAN refute here
#guard isContent Tok.scal == true         -- content: a global boundary canNOT refute here

end Tests.Reflections.AdjacencyMirrorCornerIsLayerScoped
