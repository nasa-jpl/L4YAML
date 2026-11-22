/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

module

public import L4YAML.Scanner.Scanner

@[expose] public section Blanket

/-!
# Flow-adjacency check: proof helpers (Fix A, step a) — legacy scanner

The scanner rejects separator-less adjacent flow entries via
`scanNextToken_checkFlowAdjacency`, folded into the entry of
`scanNextToken_dispatchFlowIndicators`.  This module provides the two
reusable helpers every downstream (legacy) proof needs:

* **`peel_flowAdj`** — for *inversion* sites (given a successful
  `dispatchFlowIndicators` result, derive facts): strip the folded check
  off the front, restoring the pre-fold body so the existing dispatch
  proof proceeds unchanged.

* **`checkFlowAdjacency_ok_of_notInFlow` / `_notCompletes` / `_sepChar`**
  — for *construction* sites (prove `dispatchFlowIndicators s c = .ok …`):
  discharge the check to `.ok ()` from the local scanner invariant.

The indexed twins live in `FlowAdjacencyIx.lean` (kept separate so the
legacy proofs, which `L4YAML.Scanner.IndexedDispatch` transitively
depends on, do not form an import cycle). -/

namespace L4YAML.Proofs.FlowAdjacency

open L4YAML L4YAML.Scanner L4YAML.CharPredicates

/-! ## Inversion helpers (peel the folded check) -/

/-- Peel the folded flow-adjacency check off the front of
    `scanNextToken_dispatchFlowIndicators`.  After
    `unfold scanNextToken_dispatchFlowIndicators`, the body is
    `scanNextToken_checkFlowAdjacency s c >>= k`; on a successful (`.ok`)
    result the check must itself have succeeded, so the continuation
    `k ()` carries the whole `.ok` equation. -/
lemma peel_flowAdj {α : Type} {s : ScannerState} {c : Char}
    {k : Unit → Except ScanError α} {r : α}
    (h : (scanNextToken_checkFlowAdjacency s c >>= k) = .ok r) : k () = .ok r := by
  cases hc : scanNextToken_checkFlowAdjacency s c with
  | ok u => rw [hc] at h; simp only [bind, Except.bind] at h; exact h
  | error e => rw [hc] at h; simp [bind, Except.bind] at h

/-- The folded check itself succeeded (companion to `peel_flowAdj`, which keeps
    the continuation and drops this half). -/
lemma flowAdj_ok_of_dispatch_ok {α : Type} {s : ScannerState} {c : Char}
    {k : Unit → Except ScanError α} {r : α}
    (h : (scanNextToken_checkFlowAdjacency s c >>= k) = .ok r) :
    scanNextToken_checkFlowAdjacency s c = .ok () := by
  cases hc : scanNextToken_checkFlowAdjacency s c with
  | ok u => cases u; rfl
  | error e => rw [hc] at h; simp [bind, Except.bind] at h

/-- Inversion of the adjacency check at a node-starting character: inside a flow,
    a successful check means the previous real token did NOT complete a value.

    **Item 9d.** The `:` premise is the weak one: `:` is exempt only while it is
    a *value indicator*, so a `:` that failed `isValueCandidate` — the one that
    falls through to content dispatch and starts a plain scalar — is a node start
    like any other and this inversion applies to it too. -/
lemma notCompletes_of_checkFlowAdjacency_ok_nodeStart {s : ScannerState} {c : Char}
    (h : scanNextToken_checkFlowAdjacency s c = .ok ())
    (hf : s.inFlow = true)
    (hc : c ≠ ',' ∧ c ≠ ']' ∧ c ≠ '}')
    (hcolon : c = ':' → isValueCandidate s = false) :
    ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false := by
  intro t ht
  unfold scanNextToken_checkFlowAdjacency at h
  rw [hf] at h
  simp only [ht] at h
  by_cases hcv : t.completesFlowValue = true
  · obtain ⟨h1, h3, h4⟩ := hc
    by_cases hcol : c = ':'
    · simp [hcv, hcol, hcolon hcol] at h
    · simp [hcv, h1, h3, h4, hcol] at h
  · simpa using hcv

/-- The `c ∉ {',', ':', ']', '}'}` corollary — the shape every pre-9d call site
    uses, and still the right one wherever `c` is a literal node-start. -/
lemma notCompletes_of_checkFlowAdjacency_ok {s : ScannerState} {c : Char}
    (h : scanNextToken_checkFlowAdjacency s c = .ok ())
    (hf : s.inFlow = true)
    (hc : c ≠ ',' ∧ c ≠ ':' ∧ c ≠ ']' ∧ c ≠ '}') :
    ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false :=
  notCompletes_of_checkFlowAdjacency_ok_nodeStart h hf ⟨hc.1, hc.2.2.1, hc.2.2.2⟩
    (fun hcol => absurd hcol hc.2.1)

/-- Inversion of the comma guard: a successful `scanFlowEntry` means the previous
    real token was not a flow-open indicator or another `,`. -/
lemma notSepTok_of_scanFlowEntry_ok {s s' : ScannerState} (h : scanFlowEntry s = .ok s') :
    ∀ t, lastRealTokenVal? s.tokens = some t →
      ¬(t = .flowSequenceStart ∨ t = .flowMappingStart ∨ t = .flowEntry) := by
  intro t ht hbad
  unfold scanFlowEntry at h
  simp only [Bind.bind, Except.bind, ht] at h
  rcases hbad with rfl | rfl | rfl <;> simp at h

/-! ## Construction helpers (discharge the check to `.ok ()`) -/

/-- Outside a flow collection the adjacency check is vacuously `.ok ()`. -/
lemma checkFlowAdjacency_ok_of_notInFlow {s : ScannerState} {c : Char}
    (h : s.inFlow = false) : scanNextToken_checkFlowAdjacency s c = .ok () := by
  unfold scanNextToken_checkFlowAdjacency
  simp [h]

/-- If the previous real token does not complete a flow value, the
    adjacency check is `.ok ()` regardless of `c`. -/
lemma checkFlowAdjacency_ok_of_notCompletes {s : ScannerState} {c : Char}
    (h : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false) :
    scanNextToken_checkFlowAdjacency s c = .ok () := by
  unfold scanNextToken_checkFlowAdjacency
  split
  · split
    · rename_i hlast; rw [h _ hlast]; simp
    · rfl
  · rfl

/-- If `c` is an unconditional post-value character (`,` `]` `}`), the
    adjacency check is `.ok ()` regardless of the previous token.

    Item 9d dropped `:` from this list: a `:` is exempt only when it is a value
    indicator, so it needs `checkFlowAdjacency_ok_of_valueIndicator` instead. -/
lemma checkFlowAdjacency_ok_of_sepChar {s : ScannerState} {c : Char}
    (h : c = ',' ∨ c = ']' ∨ c = '}') :
    scanNextToken_checkFlowAdjacency s c = .ok () := by
  unfold scanNextToken_checkFlowAdjacency
  split
  · split
    · rcases h with rfl | rfl | rfl <;> simp
    · rfl
  · rfl

/-- A `:` that *is* a value indicator is exempt (item 9d).  The emitter always
    writes `: ` with a following blank, so `isValueCandidate` holds at every `:`
    it produces — this is the form the emit→scan towers discharge. -/
lemma checkFlowAdjacency_ok_of_valueIndicator {s : ScannerState} {c : Char}
    (hc : c = ':') (hv : isValueCandidate s = true) :
    scanNextToken_checkFlowAdjacency s c = .ok () := by
  subst hc
  unfold scanNextToken_checkFlowAdjacency
  split
  · split
    · simp [hv]
    · rfl
  · rfl

/-! ## Last-token preservation through `saveSimpleKey`

Used to thread the `checkFlowAdjacency_ok_of_notCompletes` discharge from a
scanner state into its `saveSimpleKey`-preprocessed successor (the emit→scan
towers scan each flow entry from a `saveSimpleKey`-advanced state). -/

/-- Pushing two `.placeholder` slots does not change the last *real* token
    (it is skipped), so `lastRealTokenVal?` is either unchanged or the
    placeholder itself. -/
lemma lastRealTokenVal_push_two_ph
    (tokens : Array (Positioned YamlToken))
    (ph1 ph2 : Positioned YamlToken) (h1 : ph1.val = .placeholder) (h2 : ph2.val = .placeholder)
    (t : YamlToken)
    (ht : lastRealTokenVal? ((tokens.push ph1).push ph2) = some t) :
    lastRealTokenVal? tokens = some t ∨ t = .placeholder := by
  unfold lastRealTokenVal? at ht
  dsimp only [] at ht
  simp only [Array.size_push] at ht
  simp only [show tokens.size + 2 > 0 from by omega, ↓reduceIte,
    show tokens.size + 2 - 1 = tokens.size + 1 from by omega] at ht
  have h_elem1 : ((tokens.push ph1).push ph2)[tokens.size + 1]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  simp only [h_elem1, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show tokens.size + 1 > 0 from by omega,
    show tokens.size + 1 - 1 = tokens.size from by omega] at ht
  have h_elem2 : ((tokens.push ph1).push ph2)[tokens.size]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  by_cases h_gt : tokens.size > 0
  · have h_elem3 : ((tokens.push ph1).push ph2)[tokens.size - 1]!.val =
        tokens[tokens.size - 1]!.val := by
      rw [getElem!_pos _ _ (by simp [Array.size_push]; omega),
          getElem!_pos _ _ (by omega)]
      simp only [Array.getElem_push,
        show tokens.size - 1 < (tokens.push ph1).size from by simp [Array.size_push]; omega,
        show tokens.size - 1 < tokens.size from by omega, dite_true]
    simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show tokens.size + 1 > 1 from by omega, ↓reduceIte,
      show tokens.size + 1 - 2 = tokens.size - 1 from by omega,
      h_elem3, decide_true] at ht
    injection ht with ht_val
    by_cases h_ne : t = .placeholder
    · exact .inr h_ne
    · left; unfold lastRealTokenVal?; dsimp only []
      simp [h_gt, ht_val,
        show (t == YamlToken.placeholder) = false from beq_eq_false_iff_ne.mpr h_ne]
  · simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
      Bool.true_and, show ¬(tokens.size + 1 > 1) from by omega, ↓reduceIte,
      decide_true, decide_false] at ht
    injection ht with ht_val; exact .inr ht_val.symm

/-- If the final array slot holds a non-placeholder token, `lastRealTokenVal?`
    returns exactly that token's value (no placeholder-skipping needed).  Used to
    read off the last real token from the `scanNextToken_flow_value` `.value`-push
    exposure (which is stated as an index fact, not a `.push` shape). -/
lemma lastRealTokenVal_of_last_nonph
    (tokens : Array (Positioned YamlToken)) (N : Nat) (tok : Positioned YamlToken)
    (h_size : tokens.size = N + 1) (h_get : tokens[N]? = some tok)
    (h_np : tok.val ≠ .placeholder) :
    lastRealTokenVal? tokens = some tok.val := by
  have hN : N < tokens.size := by omega
  have h_eq : tokens[N] = tok := by
    rw [Array.getElem?_eq_getElem hN] at h_get; exact Option.some.inj h_get
  have h_bang : tokens[tokens.size - 1]!.val = tok.val := by
    rw [show tokens.size - 1 = N from by omega, getElem!_pos tokens N hN, h_eq]
  have h_np' : (tok.val == YamlToken.placeholder) = false := beq_eq_false_iff_ne.mpr h_np
  unfold lastRealTokenVal?
  simp only [show tokens.size > 0 from by omega, ↓reduceIte, h_bang, h_np',
    Bool.false_and, Bool.false_eq_true, ↓reduceIte]

/-- `saveSimpleKey` preserves "last real token does not complete a flow
    value" (the placeholders it may push are not value-completers). -/
lemma saveSimpleKey_preserves_completesFalse (s : ScannerState)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t → t.completesFlowValue = false)
    (t : YamlToken)
    (ht : lastRealTokenVal? (saveSimpleKey s).tokens = some t) :
    t.completesFlowValue = false := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    unfold saveSimpleKey
    split
    · exact .inl rfl
    · split
      · right; dsimp only []
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq] at ht; exact h_last t ht
  · rw [h_eq] at ht
    have h_or := lastRealTokenVal_push_two_ph s.tokens
      ⟨s.currentPos, .placeholder, s.currentPos⟩
      ⟨s.currentPos, .placeholder, s.currentPos⟩ rfl rfl t ht
    cases h_or with
    | inl h => exact h_last t h
    | inr h => subst h; rfl

/-! ## Last-slot realness

`saveSimpleKey`'s reservation slots are the only way a placeholder can end the
token array, and `lastRealTokenVal?` skips exactly two of them. So a state whose
array already ends in a REAL token reads the same last real token before and
after preprocessing — which is what lets a production-side invariant state a
token-history coupling about the *pre*-preprocessing state and still use it
against a guard the scanner evaluates *after* preprocessing. -/

/-- The token array is non-empty and its final slot holds a real (non-placeholder)
    token. Every emitting dispatch re-establishes this; only `saveSimpleKey` can
    break it. -/
def LastTokenReal (tokens : Array (Positioned YamlToken)) : Prop :=
  0 < tokens.size ∧ tokens[tokens.size - 1]!.val ≠ .placeholder

/-- With a real final slot there is no placeholder-skipping to do. -/
lemma LastTokenReal.lastRealTokenVal {tokens : Array (Positioned YamlToken)}
    (h : LastTokenReal tokens) :
    lastRealTokenVal? tokens = some tokens[tokens.size - 1]!.val := by
  obtain ⟨hsz, hne⟩ := h
  unfold lastRealTokenVal?
  simp only [hsz, ↓reduceIte, beq_eq_false_iff_ne.mpr hne, Bool.false_and,
    Bool.false_eq_true, ↓reduceIte]

/-- Pushing a real token makes it the final slot. -/
lemma lastTokenReal_push {tokens : Array (Positioned YamlToken)}
    {p : Positioned YamlToken} (h : p.val ≠ .placeholder) :
    LastTokenReal (tokens.push p) := by
  refine ⟨by simp [Array.size_push], ?_⟩
  have hp : (tokens.push p)[(tokens.push p).size - 1]! = p := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.size_push, Array.getElem_push]
  rw [hp]; exact h

/-- …and it is then the last real token. -/
lemma lastRealTokenVal_push {tokens : Array (Positioned YamlToken)}
    {p : Positioned YamlToken} (h : p.val ≠ .placeholder) :
    lastRealTokenVal? (tokens.push p) = some p.val := by
  have hp : (tokens.push p)[(tokens.push p).size - 1]! = p := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.size_push, Array.getElem_push]
  rw [(lastTokenReal_push (tokens := tokens) h).lastRealTokenVal, hp]

/-- Converse of `lastRealTokenVal_push_two_ph` under a real final slot: the two
    reservation placeholders are skipped and land exactly on it, so the reading
    is unchanged. -/
lemma lastRealTokenVal_push_two_ph_of_real
    {tokens : Array (Positioned YamlToken)} {ph1 ph2 : Positioned YamlToken}
    (h1 : ph1.val = .placeholder) (h2 : ph2.val = .placeholder)
    (hr : LastTokenReal tokens) :
    lastRealTokenVal? ((tokens.push ph1).push ph2) = lastRealTokenVal? tokens := by
  obtain ⟨hsz, hne⟩ := hr
  rw [LastTokenReal.lastRealTokenVal ⟨hsz, hne⟩]
  unfold lastRealTokenVal?
  dsimp only []
  simp only [Array.size_push]
  simp only [show tokens.size + 1 + 1 > 0 from by omega, ↓reduceIte,
    show tokens.size + 1 + 1 - 1 = tokens.size + 1 from by omega]
  have h_elem1 : ((tokens.push ph1).push ph2)[tokens.size + 1]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push])]
    simp [Array.getElem_push, Array.size_push, h2]
  simp only [h_elem1, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show tokens.size + 1 > 0 from by omega,
    show tokens.size + 1 - 1 = tokens.size from by omega]
  have h_elem2 : ((tokens.push ph1).push ph2)[tokens.size]!.val = .placeholder := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega)]
    simp [Array.getElem_push, Array.size_push, h1]
  have h_elem3 : ((tokens.push ph1).push ph2)[tokens.size - 1]!.val =
      tokens[tokens.size - 1]!.val := by
    rw [getElem!_pos _ _ (by simp [Array.size_push]; omega),
        getElem!_pos _ _ (by omega)]
    simp only [Array.getElem_push,
      show tokens.size - 1 < (tokens.push ph1).size from by simp [Array.size_push]; omega,
      show tokens.size - 1 < tokens.size from by omega, dite_true]
  simp only [h_elem2, show (YamlToken.placeholder == YamlToken.placeholder) = true from by decide,
    Bool.true_and, show tokens.size + 1 > 1 from by omega,
    show tokens.size + 1 - 2 = tokens.size - 1 from by omega, h_elem3]
  simp

/-- `saveSimpleKey` leaves the last real token alone when the array ends real. -/
lemma saveSimpleKey_preserves_lastRealTokenVal (s : ScannerState)
    (hr : LastTokenReal s.tokens) :
    lastRealTokenVal? (saveSimpleKey s).tokens = lastRealTokenVal? s.tokens := by
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    unfold saveSimpleKey
    split
    · exact .inl rfl
    · split
      · right; dsimp only []
      · exact .inl rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq]
  · rw [h_eq]; exact lastRealTokenVal_push_two_ph_of_real rfl rfl hr


/-! ## `[148]`/`[149]` adjacent value: the scanner's JSON-key path

`isValueCandidate` accepts a `:` whose follower is neither a blank nor a flow
indicator only through its JSON-key branch; the key token the scanner checked
is therefore `isJsonNodeToken`.  Surface's `SFlowMapEntry.jsonKeyAdjacentValue`
/ `SFlowSeqEntry.pairJsonAdjacentValue` are the arms that spend this fact. -/

/-- The token slot `isValueCandidate` inspects for the JSON-key check. -/
def flowKeyToken (s : ScannerState) : Option (Positioned YamlToken) :=
  if s.simpleKey.pos.offset != s.offset then s.tokens[s.tokens.size - 1]?
  else s.tokens[s.simpleKey.tokenIndex - 1]?

lemma isValueCandidate_glued_jsonKey (s : ScannerState) (n : Char)
    (hflow : s.inFlow = true) (hpk : s.peekAt? 1 = some n)
    (hn : (isBlankBool n || isFlowIndicatorBool n) = false)
    (h : isValueCandidate s = true) :
    s.simpleKey.possible = true ∧
      ∃ tok, flowKeyToken s = some tok ∧ isJsonNodeToken tok.val = true := by
  unfold isValueCandidate at h
  obtain ⟨hb, hf⟩ := Bool.or_eq_false_iff.mp hn
  by_cases hp : s.simpleKey.possible = true
  · refine ⟨hp, ?_⟩
    unfold flowKeyToken
    simp only [hflow, hp, Bool.and_self, ↓reduceIte, hpk] at h
    split at h <;> rename_i hoff <;> simp only [hoff, ↓reduceIte] <;>
      split at h <;> rename_i htok <;> simp [hb, hf] at h
    all_goals exact ⟨_, htok, h⟩
  · simp only [Bool.not_eq_true] at hp
    simp [hflow, hp, hpk, hb, hf] at h

end L4YAML.Proofs.FlowAdjacency

end Blanket
