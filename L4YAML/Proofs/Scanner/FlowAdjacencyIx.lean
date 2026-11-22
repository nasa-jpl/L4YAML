/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.IndexedDispatch

@[expose] public section Blanket

/-!
# Flow-adjacency check: proof helpers (Fix A, step a) — indexed scanner

Indexed twins of the helpers in `FlowAdjacency.lean`, for
`scanNextTokenIx_dispatchFlowIndicators`.  Kept in a separate module
(importing `L4YAML.Scanner.IndexedDispatch`) so the legacy helpers, which
that scanner module transitively depends on, do not form an import cycle.
-/

namespace L4YAML.Proofs.FlowAdjacencyIx

open L4YAML L4YAML.Indexed L4YAML.Scanner L4YAML.Scanner.Indexed L4YAML.CharPredicates
  L4YAML.Scanner.Indexed.ScannerStateIx

/-- Peel the folded flow-adjacency check off the front of
    `scanNextTokenIx_dispatchFlowIndicators` (inversion sites). -/
lemma peel_flowAdjIx {input : String} {α : Type}
    {s : ScannerStateIx input} {c : Char}
    {k : Unit → Except ScanError α} {r : α}
    (h : (scanNextTokenIx_checkFlowAdjacency s c >>= k) = .ok r) : k () = .ok r := by
  cases hc : scanNextTokenIx_checkFlowAdjacency s c with
  | ok u => rw [hc] at h; simp only [bind, Except.bind] at h; exact h
  | error e => rw [hc] at h; simp [bind, Except.bind] at h

/-- Outside a flow collection the adjacency check is vacuously `.ok ()`. -/
lemma checkFlowAdjacencyIx_ok_of_notInFlow {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : s.inFlow = false) : scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  unfold scanNextTokenIx_checkFlowAdjacency
  simp [h]

/-- If the previous real token does not complete a flow value, the
    adjacency check is `.ok ()` regardless of `c`. -/
lemma checkFlowAdjacencyIx_ok_of_notCompletes {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : ∀ t, lastRealTokenValIx? s.tokens = some t → t.completesFlowValue = false) :
    scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  unfold scanNextTokenIx_checkFlowAdjacency
  split
  · split
    · rename_i hlast; rw [h _ hlast]; simp
    · rfl
  · rfl

/-- If `c` is an unconditional post-value character (`,` `]` `}`), the
    adjacency check is `.ok ()` regardless of the previous token.  Item 9d
    dropped `:`; see `checkFlowAdjacencyIx_ok_of_valueIndicator`. -/
lemma checkFlowAdjacencyIx_ok_of_sepChar {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : c = ',' ∨ c = ']' ∨ c = '}') :
    scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  unfold scanNextTokenIx_checkFlowAdjacency
  split
  · split
    · rcases h with rfl | rfl | rfl <;> simp
    · rfl
  · rfl

/-- A `:` that *is* a value indicator is exempt (item 9d).  Indexed twin of
    `checkFlowAdjacency_ok_of_valueIndicator`. -/
lemma checkFlowAdjacencyIx_ok_of_valueIndicator {input : String}
    {s : ScannerStateIx input} {c : Char}
    (hc : c = ':') (hv : isValueCandidateIx s = true) :
    scanNextTokenIx_checkFlowAdjacency s c = .ok () := by
  subst hc
  unfold scanNextTokenIx_checkFlowAdjacency
  split
  · split
    · simp [hv]
    · rfl
  · rfl

/-- Inversion at a node-starting character (item 9d): indexed twin of
    `notCompletes_of_checkFlowAdjacency_ok_nodeStart`. -/
lemma notCompletes_of_checkFlowAdjacencyIx_ok_nodeStart {input : String}
    {s : ScannerStateIx input} {c : Char}
    (h : scanNextTokenIx_checkFlowAdjacency s c = .ok ())
    (hf : s.inFlow = true)
    (hc : c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}')
    (hcolon : c = ':' → isValueCandidateIx s = false) :
    ∀ t, lastRealTokenValIx? s.tokens = some t → t.completesFlowValue = false := by
  intro t ht
  unfold scanNextTokenIx_checkFlowAdjacency at h
  rw [hf] at h
  simp only [ht] at h
  by_cases hcv : t.completesFlowValue = true
  · obtain ⟨h1, h3, h4⟩ := hc
    by_cases hcol : c = ':'
    · simp [hcv, hcol, hcolon hcol] at h
    · simp [hcv, h1, h3, h4, hcol] at h
  · simpa using hcv

/-! ## Last-token preservation through `saveSimpleKeyIx`

Indexed twins of the `FlowAdjacency.lean` helpers used to thread the
`checkFlowAdjacencyIx_ok_of_notCompletes` discharge from a scanner state
into its `saveSimpleKeyIx`-preprocessed successor. -/

/-- After pushing two `.placeholder` tokens onto a token stream,
    `lastRealTokenValIx?` either reports the pre-push last real token or
    reports `.placeholder`.  Indexed twin of legacy
    `lastRealTokenVal_push_two_ph`. -/
lemma lastRealTokenValIx_push_two_ph {input : String}
    (ts : Indexed.TokenStream input)
    (ph1 ph2 : Indexed.IxToken input)
    (h1 : ph1.token = YamlToken.placeholder)
    (h2 : ph2.token = YamlToken.placeholder)
    (t : YamlToken)
    (ht : lastRealTokenValIx? ((ts.push ph1).push ph2) = some t) :
    lastRealTokenValIx? ts = some t ∨ t = YamlToken.placeholder := by
  unfold lastRealTokenValIx? at ht
  simp only [Indexed.TokenStream.push, Array.size_push] at ht
  simp only [show ts.tokens.size + 1 + 1 > 0 from by omega, ↓reduceIte,
    show ts.tokens.size + 1 + 1 - 1 = ts.tokens.size + 1 from by omega] at ht
  have h_elem1 : ((ts.tokens.push ph1).push ph2)[ts.tokens.size + 1]!.token
      = YamlToken.placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  simp only [h_elem1,
    show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show ts.tokens.size + 1 > 0 from by omega,
    show ts.tokens.size + 1 - 1 = ts.tokens.size from by omega] at ht
  have h_elem2 : ((ts.tokens.push ph1).push ph2)[ts.tokens.size]!.token
      = YamlToken.placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  by_cases h_gt : ts.tokens.size > 0
  · have h_elem3 : ((ts.tokens.push ph1).push ph2)[ts.tokens.size - 1]!.token
        = ts.tokens[ts.tokens.size - 1]!.token := by
      rw [getElem!_pos _ _ (by simp [Array.size_push]; omega),
          getElem!_pos _ _ (by omega)]
      simp only [Array.getElem_push,
        show ts.tokens.size - 1 < (ts.tokens.push ph1).size from by
          simp [Array.size_push]; omega,
        show ts.tokens.size - 1 < ts.tokens.size from by omega, dite_true]
    simp only [h_elem2,
      show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show ts.tokens.size + 1 > 1 from by omega,
      show ts.tokens.size + 1 - 2 = ts.tokens.size - 1 from by omega,
      h_elem3] at ht
    injection ht with ht_val
    by_cases h_ne : t = YamlToken.placeholder
    · exact .inr h_ne
    · left; unfold lastRealTokenValIx?
      show (let arr := ts.tokens
        if arr.size > 0 then
          let lastIdx := arr.size - 1
          let tok1 := arr[lastIdx]!.token
          if tok1 == YamlToken.placeholder && lastIdx > 0 then
            let tok2 := arr[lastIdx - 1]!.token
            if tok2 == YamlToken.placeholder && lastIdx > 1 then
              some arr[lastIdx - 2]!.token
            else some tok2
          else some tok1
        else none) = some t
      simp only [h_gt, ↓reduceIte, ht_val,
        show (t == YamlToken.placeholder) = false from
          beq_eq_false_iff_ne.mpr h_ne, Bool.false_and, Bool.false_eq_true]
  · simp only [h_elem2,
      show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show ¬(ts.tokens.size + 1 > 1) from by omega] at ht
    injection ht with ht_val; exact .inr ht_val.symm

/-- If the final array slot holds a non-placeholder token,
    `lastRealTokenValIx?` returns exactly that token's value.  Indexed
    twin of legacy `lastRealTokenVal_of_last_nonph`. -/
lemma lastRealTokenValIx_of_last_nonph {input : String}
    (ts : Indexed.TokenStream input) (N : Nat) (tok : Indexed.IxToken input)
    (h_size : ts.tokens.size = N + 1) (h_get : ts.tokens[N]? = some tok)
    (h_np : tok.token ≠ YamlToken.placeholder) :
    lastRealTokenValIx? ts = some tok.token := by
  have hN : N < ts.tokens.size := by omega
  have h_eq : ts.tokens[N] = tok := by
    rw [Array.getElem?_eq_getElem hN] at h_get; exact Option.some.inj h_get
  have h_bang : ts.tokens[ts.tokens.size - 1]!.token = tok.token := by
    rw [show ts.tokens.size - 1 = N from by omega, getElem!_pos ts.tokens N hN, h_eq]
  have h_np' : (tok.token == YamlToken.placeholder) = false := beq_eq_false_iff_ne.mpr h_np
  unfold lastRealTokenValIx?
  simp only [show ts.tokens.size > 0 from by omega, ↓reduceIte, h_bang, h_np',
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- `saveSimpleKeyIx` preserves "last real token does not complete a flow
    value" (the placeholders it may push are not value-completers).
    Indexed twin of legacy `saveSimpleKey_preserves_completesFalse`. -/
lemma saveSimpleKeyIx_preserves_completesFalse {input : String}
    (s : ScannerStateIx input)
    (h_last : ∀ t, lastRealTokenValIx? s.tokens = some t → t.completesFlowValue = false)
    (t : YamlToken)
    (ht : lastRealTokenValIx? (saveSimpleKeyIx s).tokens = some t) :
    t.completesFlowValue = false := by
  have h_cases : (saveSimpleKeyIx s).tokens = s.tokens ∨
      (saveSimpleKeyIx s).tokens =
        ((s.tokens.push
            (Indexed.IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder
              s.cursor.pos (Nat.le_refl _) s.cursor.posBound)).push
          (Indexed.IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder
            s.cursor.pos (Nat.le_refl _) s.cursor.posBound)) := by
    unfold saveSimpleKeyIx
    split
    · exact .inl rfl
    · split
      · right
        show ((s.emit YamlToken.placeholder).emit YamlToken.placeholder).tokens = _
        rfl
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq] at ht; exact h_last t ht
  · rw [h_eq] at ht
    have h_or := lastRealTokenValIx_push_two_ph s.tokens
      (Indexed.IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder
        s.cursor.pos (Nat.le_refl _) s.cursor.posBound)
      (Indexed.IxToken.mk' (input := input) s.cursor.pos YamlToken.placeholder
        s.cursor.pos (Nat.le_refl _) s.cursor.posBound)
      rfl rfl t ht
    cases h_or with
    | inl h => exact h_last t h
    | inr h => subst h; rfl


/-! ## `[148]`/`[149]` adjacent value: the indexed scanner's JSON-key path -/

/-- The token slot `isValueCandidateIx` inspects for the JSON-key check. -/
def flowKeyTokenIx {input : String} (s : ScannerStateIx input) : Option (IxToken input) :=
  if s.simpleKey.cursor.pos.offset != s.cursor.pos.offset then s.tokens.tokens[s.tokens.size - 1]?
  else s.tokens.tokens[s.simpleKey.tokenIndex - 1]?

lemma isValueCandidateIx_glued_jsonKey {input : String} (s : ScannerStateIx input) (n : Char)
    (hflow : s.inFlow = true) (hpk : s.peekAt? 1 = some n)
    (hn : (isBlankBool n || isFlowIndicatorBool n) = false)
    (h : isValueCandidateIx s = true) :
    s.simpleKey.possible = true ∧
      ∃ t, flowKeyTokenIx s = some t ∧ isJsonNodeTokenIx t.token = true := by
  unfold isValueCandidateIx at h
  obtain ⟨hb, hf⟩ := Bool.or_eq_false_iff.mp hn
  by_cases hp : s.simpleKey.possible = true
  · refine ⟨hp, ?_⟩
    unfold flowKeyTokenIx
    simp only [hflow, hp, Bool.and_self, ↓reduceIte, hpk] at h
    split at h <;> rename_i hoff <;> simp only [hoff, ↓reduceIte] <;>
      split at h <;> rename_i htok <;> simp [hb, hf] at h
    all_goals exact ⟨_, htok, h⟩
  · simp only [Bool.not_eq_true] at hp
    simp [hflow, hp, hpk, hb, hf] at h

end L4YAML.Proofs.FlowAdjacencyIx

end Blanket
