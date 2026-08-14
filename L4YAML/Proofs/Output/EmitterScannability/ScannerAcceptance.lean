/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Spec.CharPredicates
import L4YAML.Proofs.Output.ScannerEmitBridge
import L4YAML.Proofs.RoundTrip.RoundTrip
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Proofs.Coupling.ScalarCoupling
import L4YAML.Proofs.Parser.ParserGrammable
import L4YAML.Proofs.Scanner.ScannerPlainContent
import L4YAML.Proofs.Scanner.ScannerBound
import L4YAML.Proofs.Output.EmitterScannability.EscapeProperties

/-!
# Emitter Scannability — §3 Scanner Acceptance + Substrate Predicates

Foundation module extracted 2026-05-31 from `EmitterScannability.lean` to shrink the
base file toward the remaining proof work (the 7 legacy sorries in §5/§G.balance).
Imports only the base's upstream imports (NOT the base — that would be circular);
the base transitively imports this via the foundation chain
`ScannerAcceptance ← ScanSteps ← FilteredGrowth ← ScanChainGrowth ← base`.
The namespace is reopened so every fully-qualified name is unchanged. A contiguous
prefix of the original file ⇒ zero forward references by Lean's define-before-use rule.

Contents: §3 Scanner Acceptance (Step 1), `SimpleKeyAboveFloor`, `FlowMonoChain`
prefix preservation, and the substrate predicate layers `NoOverwriteAt` (d),
`FlowNoOverwriteAt` (e), `SavedKeyDoesntResolve` (f), non-`:` dispatch (g).
-/

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ScalarCoupling

/-! ## §3  Scanner Acceptance of Canonical Output (Step 1)

The main technical content: proving the scanner accepts emitter output.

### §3.0  Helpers for scanner dispatch on emitter output
-/

-- Each character occupies at least 1 byte in UTF-8
lemma CharsFromOffset_length_le {input : String} {offset : Nat} {chars : List Char}
    (h : CharsFromOffset input offset chars) :
    chars.length ≤ input.utf8ByteSize - offset := by
  induction h with
  | at_end p hp => simp
  | cons p hp c rest hc hrest ih =>
    simp only [List.length_cons]
    rw [next_byteIdx, hc] at ih
    have := Char.utf8Size_pos c
    omega

-- escapeChar produces at least 1 character
lemma escapeChar_toList_length_pos (c : Char) :
    (escapeChar c).toList.length ≥ 1 := by
  unfold escapeChar
  split
  all_goals (try decide)
  -- Remaining: default case with if c.val.toNat < 0x20
  split
  · -- escapeHex2: "\\" ++ "x" ++ h1.toString ++ h2.toString → length ≥ 4
    simp only [escapeHex2, String.toList_append, List.length_append,
               Char.toString, String.toList_singleton, List.length_singleton]
    omega
  · -- c.toString → length = 1
    simp [Char.toString, String.toList_singleton]

-- escapeString preserves or grows the length
lemma escapeString_length_ge (cs : List Char) :
    (escapeString (String.ofList cs)).toList.length ≥ cs.length := by
  induction cs with
  | nil => simp [escapeString_nil]
  | cons c rest ih =>
    rw [escapeString_cons]
    simp only [String.toList_append, List.length_append, List.length_cons]
    have h1 := escapeChar_toList_length_pos c
    omega

-- `validateTrailingContent` succeeds when peek? = none (at EOF)
lemma validateTrailingContent_peek_none (s : ScannerState) (inputEnd : Nat)
    (h_peek : s.peek? = none) : validateTrailingContent s inputEnd = .ok () := by
  -- From peek? = none, derive offset ≥ inputEnd
  have h_not_lt : ¬(s.offset < s.inputEnd) := by
    intro h_lt
    have : s.peek? ≠ none := by unfold ScannerState.peek?; simp [h_lt]
    exact this h_peek
  -- skipTrailingSpaces returns s when peek? = none
  have h_sts : skipTrailingSpaces s (inputEnd - s.offset + 1) = s := by
    generalize inputEnd - s.offset + 1 = fuel
    induction fuel with
    | zero => rfl
    | succ n _ => unfold skipTrailingSpaces; rw [h_peek]
  -- validateTrailingContent: probe = s, probe.peek? = none → pure ()
  unfold validateTrailingContent; simp [h_sts, h_peek]; rfl

-- `scanDoubleQuoted` succeeds using the loop lemma + EOF property
lemma scanDoubleQuoted_emitScalar_ok (sc : ScannerState)
    (content : String)
    (hcorr : ScannerSurfCorr sc
      ⟨['"'] ++ (escapeString content).toList ++ ['"'], sc.col⟩)
    (h_not_flow : sc.inFlow = false) :
    ∃ s', scanDoubleQuoted sc = .ok s' ∧ s'.peek? = none
      ∧ s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .doubleQuoted } := by
  -- Surface after advancing past opening quote
  have ⟨_, h_lt⟩ := peek_of_chars_cons sc '"'
    ((escapeString content).toList ++ ['"']) _ hcorr
  have hcorr_adv := advance_non_newline_corr sc '"'
    ((escapeString content).toList ++ ['"']) hcorr h_lt (by decide) (by decide)
  have h_col_eq : (sc.col + 1 : Nat) = sc.advance.col := hcorr_adv.col_eq
  rw [h_col_eq] at hcorr_adv
  -- Fuel bound for loop
  have h_fuel : sc.advance.inputEnd - sc.advance.offset + 1 ≥ content.toList.length + 1 := by
    rw [hcorr_adv.end_eq]
    have h_cf := CharsFromOffset_length_le hcorr_adv.chars_from
    simp only [List.length_append, List.length_singleton] at h_cf
    have h_esc := escapeString_length_ge content.toList
    simp only [String.ofList_toList] at h_esc
    omega
  -- Loop succeeds and leaves scanner at EOF
  have h_ie : sc.inputEnd = sc.advance.inputEnd := by rw [advance_inputEnd]
  obtain ⟨s_after, h_loop, hcorr_loop, _⟩ :=
    collectDoubleQuotedLoop_escapeString_succeeds sc.advance content.toList [] "" _
      sc.currentPos sc.inFlow sc.currentIndent
      (by simp only [List.append_nil]; rw [String.ofList_toList]; exact hcorr_adv) h_fuel
  -- Derive peek? = none from ScannerSurfCorr at empty rest
  have h_peek_none : s_after.peek? = none := by
    have h_ge : s_after.offset ≥ s_after.input.utf8ByteSize := by
      cases hcorr_loop.chars_from with | at_end _ hge => exact hge
    have h_not_lt : ¬(s_after.offset < s_after.inputEnd) := by
      rw [hcorr_loop.end_eq]; omega
    simp [ScannerState.peek?, h_not_lt]
  -- Validate trailing content succeeds at EOF
  have h_vtc := validateTrailingContent_peek_none s_after sc.advance.inputEnd h_peek_none
  -- The loop returns content = "" ++ String.ofList content.toList = content
  have h_content_eq : "" ++ String.ofList content.toList = content := by
    apply String.ext; simp
  -- Token preservation: loop and advance don't modify tokens
  have h_tok_pres : s_after.tokens = sc.tokens :=
    (ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
      _ _ _ _ _ _ _ _ h_loop).trans
      (ScannerCorrectness.advance_preserves_tokens sc)
  -- Build the result state and prove all conjuncts
  refine ⟨{ (s_after.emitAt sc.currentPos (.scalar content .doubleQuoted))
              with simpleKeyAllowed := false }, ?_, ?_, ?_⟩
  · -- scanDoubleQuoted sc = .ok _
    simp only [scanDoubleQuoted, bind, Except.bind]
    rw [h_ie]
    rw [h_content_eq] at h_loop
    rw [h_loop]
    simp [h_not_flow, h_vtc]
  · -- peek? = none (emitAt and simpleKeyAllowed don't change peek?)
    unfold ScannerState.emitAt ScannerState.peek?
    unfold ScannerState.peek? at h_peek_none
    split at h_peek_none <;> simp_all
  · -- tokens characterization
    show s_after.tokens.push _ = sc.tokens.push _
    rw [h_tok_pres]

/-- If the surface position has empty remaining chars, then peek? = none. -/
lemma peek_none_of_empty_surf (s : ScannerState) (col : Nat)
    (hcorr : ScannerSurfCorr s ⟨[], col⟩) :
    s.peek? = none := by
  unfold ScannerState.peek?
  have h_ge : s.offset ≥ s.input.utf8ByteSize :=
    match hcorr.chars_from with | .at_end _ h => h
  have := hcorr.end_eq
  simp [show ¬(s.offset < s.inputEnd) from by omega]

-- scanNextToken returns none when scanner is at EOF
lemma scanNextToken_eof (s : ScannerState) (h_peek : s.peek? = none) :
    scanNextToken s = .ok none := by
  -- peek? = none → offset ≥ inputEnd
  have h_not_lt : ¬(s.offset < s.inputEnd) := by
    intro h_lt; have : s.peek? ≠ none := by unfold ScannerState.peek?; simp [h_lt]
    exact this h_peek
  -- Key facts that follow from offset ≥ inputEnd
  have h_fuel_zero : s.inputEnd - s.offset = 0 := by omega
  -- skipWhitespace s = s (no chars to skip at EOF)
  have h_sw : skipWhitespace s = s := by
    unfold skipWhitespace; rw [h_fuel_zero]; unfold skipWhitespaceLoop; rfl
  -- skipSpaces s = s
  have h_ss : skipSpaces s = s := by
    unfold skipSpaces; rw [h_fuel_zero]; unfold skipSpacesLoop; rfl
  -- skipToContent s = .ok s
  have h_stc : skipToContent s = .ok s := by
    unfold skipToContent
    rw [show s.inputEnd - s.offset + 1 = 1 from by omega]
    unfold skipToContentLoop
    have h_ws : skipToContentWs s = .ok s := by
      unfold skipToContentWs
      split
      · simp [h_ss, h_peek, h_sw]
      · simp [h_sw]
    simp [h_ws, skipToContentComment, h_peek]
  -- hasMore = false
  have h_hm : s.hasMore = false := by unfold ScannerState.hasMore; simp [h_not_lt]
  -- scanNextToken: preprocess returns none, so result is .ok none
  simp [scanNextToken, scanNextToken_preprocess, bind, Except.bind, h_stc, h_hm, pure, Except.pure]

-- The dispatch chain for '"' reaches scanDoubleQuoted.
-- This captures the fact that all intermediate dispatchers (structural,
-- flow indicators, block indicators) return none for '"'.
lemma dispatchContent_quote (s : ScannerState) (c : Char) (hc : c = '"')
    (h_notFlow : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1)
    (h_noDocStart : atDocumentStart s = false)
    (h_noDocEnd : atDocumentEnd s = false) :
    scanNextToken_dispatchStructural s c = .ok none
    ∧ scanNextToken_checkBlockFlowIndent s c = .ok ()
    ∧ scanNextToken_dispatchFlowIndicators s c = .ok none
    ∧ scanNextToken_dispatchBlockIndicators s c = .ok none := by
  subst hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- dispatchStructural: '"' doesn't match %, -, .
    unfold scanNextToken_dispatchStructural
    simp [ScannerState.inFlow, h_notFlow, h_noDocStart, h_noDocEnd,
          pure, Except.pure]
  · -- checkBlockFlowIndent: currentIndent = -1 < 0, condition false
    unfold scanNextToken_checkBlockFlowIndent
    simp [ScannerState.inFlow, h_notFlow, h_indent]
  · -- dispatchFlowIndicators: '"' doesn't match [, ], {, }, ,
    unfold scanNextToken_dispatchFlowIndicators
    simp [pure, Except.pure]
  · -- dispatchBlockIndicators: '"' doesn't match -, ?, :
    unfold scanNextToken_dispatchBlockIndicators
    simp [pure, Except.pure]

-- Transfer ScannerSurfCorr when only non-position fields change
-- (tokens, simpleKey, flags, etc.)
lemma ScannerSurfCorr_transfer {sc sc' : ScannerState}
    {sp : L4YAML.Surface.SurfPos}
    (hcorr : ScannerSurfCorr sc sp)
    (h_input : sc'.input = sc.input)
    (h_offset : sc'.offset = sc.offset)
    (h_inputEnd : sc'.inputEnd = sc.inputEnd)
    (h_col : sc'.col = sc.col)
    (h_indents : sc'.indents = sc.indents) :
    ScannerSurfCorr sc' sp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_input, h_offset]; exact hcorr.chars_from
  · rw [h_col]; exact hcorr.col_eq
  · rw [h_inputEnd, h_input]; exact hcorr.end_eq
  · rw [h_input, h_offset]; exact hcorr.input_prefix
  · intro i hi h0
    have hi' : i < sc.indents.size := h_indents ▸ hi
    have heq : sc'.indents[i]'hi = sc.indents[i]'hi' := by congr 1
    rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0

-- emitScalar decomposes as ['"'] ++ escaped ++ ['"']
lemma emitScalar_toList (content : String) :
    (emitScalar content).toList = ['"'] ++ (escapeString content).toList ++ ['"'] := by
  have h1 : ("\"" : String).toList = ['"'] := by native_decide
  show (("\"" ++ escapeString content) ++ "\"").toList = _
  simp only [String.toList_append, h1]

-- emitScalar has at least 2 bytes
lemma emitScalar_utf8ByteSize_ge (content : String) :
    (emitScalar content).utf8ByteSize ≥ 2 := by
  simp only [utf8ByteSize_eq_listByteSize, emitScalar_toList,
             listByteSize_append, listByteSize]
  have : Char.utf8Size '"' = 1 := by native_decide
  omega

-- scanLoop with exactly 2 iterations (scanNextToken returns some then none)
-- Returns the exact token array produced.
lemma scanLoop_two_iter {s₀ s₁ : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 2)
    (h_snt0 : scanNextToken s₀ = .ok (some s₁))
    (h_snt1 : scanNextToken s₁ = .ok none)
    (h_flow : s₁.flowLevel = 0)
    (h_dp : s₁.directivesPresent = false) :
    ∃ toks, scanLoop s₀ fuel = .ok toks := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  -- First iteration: scanNextToken s₀ = .ok (some s₁) → recurse
  have h1 : scanLoop s₀ (f + 2) = scanLoop s₁ (f + 1) := by
    simp only [scanLoop, h_snt0]
  -- Second iteration: scanNextToken s₁ = .ok none → checks → ok
  have h2 : ∃ toks, scanLoop s₁ (f + 1) = .ok toks := by
    simp only [scanLoop, h_snt1, h_flow, h_dp]
    exact ⟨_, rfl⟩
  rw [h1]; exact h2

-- scanLoop actually computes to the concrete token array
lemma scanLoop_two_iter_eq {s₀ s₁ : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 2)
    (h_snt0 : scanNextToken s₀ = .ok (some s₁))
    (h_snt1 : scanNextToken s₁ = .ok none)
    (h_flow : s₁.flowLevel = 0)
    (h_dp : s₁.directivesPresent = false) :
    scanLoop s₀ fuel = .ok ((unwindIndents s₁ (-1)).emit .streamEnd).tokens := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  simp only [scanLoop, h_snt0, h_snt1, h_flow, h_dp]
  simp (config := { decide := true }) only [ite_false]

-- ═══ scanLoop compositionality ═══
-- Forward composition: one scanNextToken step + remaining loop = full loop.
-- Enables proving scanner acceptance for multi-token emitter output by
-- chaining individual scanNextToken steps.

/-- **Forward step**: If `scanNextToken` produces a new state `s₁`, and
    `scanLoop s₁ fuel` succeeds, then `scanLoop s₀ (fuel + 1)` succeeds
    with the same result.

    This is the key compositionality lemma for scanner acceptance proofs:
    compose N steps backwards from `scanLoop_two_iter` (or `scanLoop_eof`)
    using repeated applications of `scanLoop_step_eq`. -/
lemma scanLoop_step_eq {s₀ s₁ : ScannerState} {fuel : Nat}
    {toks : Array (Positioned YamlToken)}
    (h_snt : scanNextToken s₀ = .ok (some s₁))
    (h_loop : scanLoop s₁ fuel = .ok toks) :
    scanLoop s₀ (fuel + 1) = .ok toks := by
  simp only [scanLoop, h_snt]; exact h_loop

/-- Existential version of `scanLoop_step_eq`. -/
lemma scanLoop_step {s₀ s₁ : ScannerState} {fuel : Nat}
    (h_snt : scanNextToken s₀ = .ok (some s₁))
    (h_loop : ∃ toks, scanLoop s₁ fuel = .ok toks) :
    ∃ toks, scanLoop s₀ (fuel + 1) = .ok toks := by
  obtain ⟨toks, h⟩ := h_loop
  exact ⟨toks, scanLoop_step_eq h_snt h⟩

/-- **Fuel monotonicity**: If `scanLoop` succeeds with `fuel₁`,
    it succeeds with any larger fuel `fuel₂ ≥ fuel₁`, producing
    the same token array.

    Proof by induction on `fuel₁`. Each `scanLoop` iteration
    either terminates (EOF/error → fuel irrelevant) or recurses with
    one less fuel (→ inductive hypothesis). -/
lemma scanLoop_fuel_mono {s : ScannerState} {fuel₁ fuel₂ : Nat}
    {toks : Array (Positioned YamlToken)}
    (h : scanLoop s fuel₁ = .ok toks) (h_le : fuel₁ ≤ fuel₂) :
    scanLoop s fuel₂ = .ok toks := by
  induction fuel₁ generalizing s fuel₂ toks with
  | zero =>
    -- scanLoop s 0 = .error (.fuelExhausted ...), contradicts h
    unfold scanLoop at h; cases h
  | succ m IH =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel₂ = n + 1 := ⟨fuel₂ - 1, by omega⟩
    -- Both scanLoop s (m+1) and scanLoop s (n+1) unfold to matching on scanNextToken s
    unfold scanLoop at h ⊢
    -- Generalize the shared discriminant, then case-split to reduce both matches
    generalize scanNextToken s = snt_result at h ⊢
    cases snt_result with
    | error e => cases h
    | ok res => cases res with
      | none => exact h
      | some s' => exact IH h (by omega)

/-- **Terminal step**: If `scanNextToken` returns `.ok none` (EOF),
    `scanLoop` with fuel ≥ 1 terminates successfully. -/
lemma scanLoop_eof {s : ScannerState}
    (h_snt : scanNextToken s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    ∃ toks, scanLoop s 1 = .ok toks := by
  unfold scanLoop; rw [h_snt]
  simp [show ¬(s.flowLevel > 0) from by omega, h_dp]

/-- **Terminal step (equality)**: If `scanNextToken` returns `.ok none` (EOF),
    `scanLoop` produces exactly the unwind+streamEnd tokens. -/
lemma scanLoop_eof_eq {s : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 1)
    (h_snt : scanNextToken s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    scanLoop s fuel = .ok ((unwindIndents s (-1)).emit .streamEnd).tokens := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold scanLoop; rw [h_snt]
  simp [show ¬(s.flowLevel > 0) from by omega, h_dp]

-- ═══ ScanChain: composition of N successful scanNextToken calls ═══

/-- `ScanChain s n s'` means `n` successive `scanNextToken` calls starting
    from `s` each return `.ok (some ...)`, with the final state being `s'`.
    Used to express that the scanner processes a multi-token sub-expression
    (e.g., `emit v` within a flow collection). -/
inductive ScanChain : ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} : ScanChain s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat} :
         scanNextToken s = .ok (some s_mid) →
         ScanChain s_mid n s' →
         ScanChain s (n + 1) s'

/-- Transitivity: concatenate two scan chains. -/
lemma ScanChain.trans {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : ScanChain s₁ n₁ s₂) (h2 : ScanChain s₂ n₂ s₃) :
    ScanChain s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_snt h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_snt h_ih

/-- A single scanNextToken step as a ScanChain. -/
lemma ScanChain.single {s s' : ScannerState}
    (h : scanNextToken s = .ok (some s')) :
    ScanChain s 1 s' :=
  .step h .zero

/-- Connect a ScanChain to scanLoop: if N steps succeed reaching s',
    and scanLoop s' fuel succeeds, then scanLoop s (fuel + N) succeeds
    with the same result. -/
lemma ScanChain.to_scanLoop {s s' : ScannerState} {n fuel : Nat}
    {toks : Array (Positioned YamlToken)}
    (h_chain : ScanChain s n s')
    (h_loop : scanLoop s' fuel = .ok toks) :
    scanLoop s (fuel + n) = .ok toks := by
  induction h_chain with
  | zero => exact h_loop
  | @step s s_mid s' k h_snt h_rest ih =>
    have h_ih := ih h_loop
    have : fuel + (k + 1) = (fuel + k) + 1 := by omega
    rw [this]
    exact scanLoop_step_eq h_snt h_ih

/-- Connect a ScanChain to scanLoop (existential version). -/
lemma ScanChain.to_scanLoop_exists {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s')
    (h_loop : ∃ fuel toks, scanLoop s' fuel = .ok toks) :
    ∃ fuel toks, scanLoop s fuel = .ok toks := by
  obtain ⟨fuel, toks, h⟩ := h_loop
  exact ⟨fuel + n, toks, h_chain.to_scanLoop h⟩

/-- The chain fuel bound: any `ScanChain` followed by EOF fits within
    the standard fuel `(input.utf8ByteSize + 1) * 4`.

    Proof strategy:
    1. `scanNextToken_progress` → each step advances offset by ≥ 1
    2. By induction: `s_final.offset ≥ s₀.offset + n`
    3. `s₀.offset = 0` (from `mk'` + `emit streamStart`)
    4. `s_final.offset ≤ s_final.inputEnd` (from upper bound preservation)
    5. `s_final.inputEnd = input.utf8ByteSize` (from inputEnd preservation)
    6. Combining: `n ≤ utf8ByteSize ≤ (utf8ByteSize + 1) * 4` -/

-- scanNextToken preserves key offset/inputEnd invariants.
-- This follows from the BoundInv framework in ScannerBound.lean:
--   (a) `inputEnd` and `input` are never assigned in any `{ s with ... }` update
--   (b) `advance` respects `offset ≤ inputEnd` via `String.next` bounds
--   (c) UTF-8 position validity (`IsValid`) is preserved through all operations
-- Proof delegates to ScannerBound.scanNextToken_preserves_bound.
lemma scanNextToken_preserves_bound (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (h_le : s.offset ≤ s.inputEnd)
    (h_ie : s.inputEnd = s.input.utf8ByteSize)
    (h_iv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩) :
    s'.offset ≤ s'.inputEnd ∧ s'.inputEnd = s.inputEnd ∧ s'.input = s.input
    ∧ String.Pos.Raw.IsValid s'.input ⟨s'.offset⟩ :=
  ScannerBound.scanNextToken_preserves_bound s s' h h_le h_ie h_iv

-- Chain invariant: offset increases, stays bounded, inputEnd preserved
lemma ScanChain.bound_invariant {s₀ s_final : ScannerState} {n : Nat}
    (h_chain : ScanChain s₀ n s_final)
    (h_le : s₀.offset ≤ s₀.inputEnd)
    (h_ie : s₀.inputEnd = s₀.input.utf8ByteSize)
    (h_iv : String.Pos.Raw.IsValid s₀.input ⟨s₀.offset⟩) :
    s_final.offset ≥ s₀.offset + n ∧
    s_final.offset ≤ s_final.inputEnd ∧
    s_final.inputEnd = s₀.inputEnd := by
  induction h_chain with
  | zero => exact ⟨by omega, h_le, rfl⟩
  | @step s s_mid s_final k h_snt h_rest ih =>
    have h_prog := ScannerCorrectness.scanNextToken_progress s s_mid h_snt
    have ⟨h_le', h_ie', h_inp', h_iv'⟩ :=
      scanNextToken_preserves_bound s s_mid h_snt h_le h_ie h_iv
    have h_ie_mid : s_mid.inputEnd = s_mid.input.utf8ByteSize := by
      rw [h_ie', h_inp']; exact h_ie
    have h_iv_mid : String.Pos.Raw.IsValid s_mid.input ⟨s_mid.offset⟩ := h_iv'
    have ⟨h_ge, h_le_final, h_ie_final⟩ := ih h_le' h_ie_mid h_iv_mid
    exact ⟨by omega, h_le_final, by rw [h_ie_final, h_ie']⟩

lemma ScanChain.fuel_bound (input : String)
    (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_chain : ScanChain s₀ n s_final)
    (_h_eof : scanNextToken s_final = .ok none) :
    n + 1 ≤ (input.utf8ByteSize + 1) * 4 := by
  -- Initial state properties
  have h_s0_off : s₀.offset = 0 := by subst h_s0; rfl
  have h_s0_le : s₀.offset ≤ s₀.inputEnd := by subst h_s0; omega
  have h_s0_ie : s₀.inputEnd = s₀.input.utf8ByteSize := by subst h_s0; rfl
  have h_s0_iv : String.Pos.Raw.IsValid s₀.input ⟨s₀.offset⟩ := by
    subst h_s0; exact ScannerLoopInvariant.isValid_at_zero _
  -- Chain invariant gives offset bounds
  have ⟨h_ge, h_le, h_ie⟩ := ScanChain.bound_invariant h_chain h_s0_le h_s0_ie h_s0_iv
  -- s_final.offset ≥ n (since s₀.offset = 0)
  rw [h_s0_off] at h_ge; simp at h_ge
  -- s_final.offset ≤ inputEnd = input.utf8ByteSize
  have h_ie2 : s_final.inputEnd = input.utf8ByteSize := by
    rw [h_ie]; subst h_s0; rfl
  rw [h_ie2] at h_le
  -- n ≤ utf8ByteSize, so n + 1 ≤ utf8ByteSize + 1 ≤ (utf8ByteSize + 1) * 4
  omega

-- ═══ FlowMonoChain: ScanChain with flow-level lower bound ═══

/-- `FlowMonoChain fl₀ s n s'` is a `ScanChain` where every intermediate state
    has `flowLevel ≥ fl₀`. This captures the "flow-balanced" property: the chain
    never closes brackets below the initial flow depth, ensuring stacked simple keys
    from before the chain are never restored.

    **Motivation**: `ScanChain_filtered_prefix` needs to show that `setIfInBounds`
    (from `scanValuePrepare`) never writes at token positions below the initial range.
    This holds when the simpleKeyStack is never popped below its initial height, which
    follows from `flowLevel ≥ fl₀` at every step (since `simpleKeyStack.size` tracks
    `flowLevel` via `scanFlowStart`/`scanFlowEnd` push/pop synchronization).

    For emitter-produced chains, `fl₀ = s.flowLevel` is always satisfied because the
    emitter produces balanced bracket sequences: every `]`/`}` matches an inner `[`/`{`. -/
inductive FlowMonoChain (fl₀ : Nat) : ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} (h_fl : s.flowLevel ≥ fl₀) :
      FlowMonoChain fl₀ s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat}
      (h_fl : s.flowLevel ≥ fl₀)
      (h_snt : scanNextToken s = .ok (some s_mid))
      (h_rest : FlowMonoChain fl₀ s_mid n s') :
      FlowMonoChain fl₀ s (n + 1) s'

/-- Degrade a `FlowMonoChain` to a plain `ScanChain` by forgetting flow-level bounds. -/
lemma FlowMonoChain.toScanChain {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : ScanChain s n s' := by
  induction h with
  | zero => exact .zero
  | step _ h_snt _h_rest ih => exact .step h_snt ih

/-- The start state of a `FlowMonoChain` has `flowLevel ≥ fl₀`. -/
lemma FlowMonoChain.flowLevel_ge_start {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : s.flowLevel ≥ fl₀ := by
  cases h with
  | zero h_fl => exact h_fl
  | step h_fl _ _ => exact h_fl

/-- The end state of a `FlowMonoChain` has `flowLevel ≥ fl₀`. -/
lemma FlowMonoChain.flowLevel_ge_end {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : s'.flowLevel ≥ fl₀ := by
  induction h with
  | zero h_fl => exact h_fl
  | step _ _ _ ih => exact ih

/-- A single `scanNextToken` step as a `FlowMonoChain`. -/
lemma FlowMonoChain.single {fl₀ : Nat} {s s' : ScannerState}
    (h_snt : scanNextToken s = .ok (some s'))
    (h_fl : s.flowLevel ≥ fl₀)
    (h_fl' : s'.flowLevel ≥ fl₀) :
    FlowMonoChain fl₀ s 1 s' :=
  .step h_fl h_snt (.zero h_fl')

/-- Transitivity: concatenate two `FlowMonoChain`s with the same floor. -/
lemma FlowMonoChain.trans {fl₀ : Nat} {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : FlowMonoChain fl₀ s₁ n₁ s₂)
    (h2 : FlowMonoChain fl₀ s₂ n₂ s₃) :
    FlowMonoChain fl₀ s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_fl h_snt h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_fl h_snt h_ih

/-- Weaken the flow-level floor: if `fl₀ ≤ fl₁`, a `FlowMonoChain fl₁` is also
    a `FlowMonoChain fl₀`. -/
lemma FlowMonoChain.weaken {fl₀ fl₁ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₁ s n s') (h_le : fl₀ ≤ fl₁) :
    FlowMonoChain fl₀ s n s' := by
  induction h with
  | zero h_fl => exact .zero (by omega)
  | step h_fl h_snt _h_rest ih => exact .step (by omega) h_snt ih

/-- Token monotonicity for `FlowMonoChain`:
    tokens only grow through the chain (delegates to `ScanChain` version). -/
lemma FlowMonoChain.tokens_mono {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h with
  | zero => omega
  | step _ h_snt _ ih =>
    have := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt; omega

/-! ### SimpleKeyAboveFloor: flow-level-aware simple key invariant

The `SimpleKeyAboveFloor` predicate is like `SimpleKeyAbove` but only constrains
stack entries at index ≥ `stackFloor`, with a size guarantee. It is designed for
use with `FlowMonoChain` where the stack floor equals the initial flow level. -/

-- Like `SimpleKeyAbove` but only constraining stack entries at index ≥ `stackFloor`.
-- Entries below the floor may have stale `tokenIndex` values from before the chain.
def SimpleKeyAboveFloor (s : ScannerState) (n : Nat) (stackFloor : Nat) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
  (∀ j, stackFloor ≤ j → (h : j < s.simpleKeyStack.size) →
    s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ n) ∧
  (s.simpleKeyStack.size ≥ stackFloor)

/-! #### SimpleKeyAboveFloor constructors -/

lemma SimpleKeyAboveFloor_of_cleared_preserved (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ :=
  ⟨fun hp => absurd hp (by rw [h_sk]; decide),
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

lemma SimpleKeyAboveFloor_of_preserved (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ :=
  ⟨fun hp => by rw [h_sk] at hp ⊢; exact h_inv.1 hp,
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

lemma SimpleKeyAboveFloor_of_endLine_update (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_poss : s_out.simpleKey.possible = s_in.simpleKey.possible)
    (h_idx : s_out.simpleKey.tokenIndex = s_in.simpleKey.tokenIndex)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ :=
  ⟨fun hp => by
    have hp' : s_in.simpleKey.possible = true := by rw [← h_poss]; exact hp
    have := h_inv.1 hp'; omega,
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

lemma SimpleKeyAboveFloor_of_flow_open (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hfl hj hp => ?_, ?_⟩
  · simp only [h_stack, Array.size_push] at hj
    by_cases hlt : j < s_in.simpleKeyStack.size
    · have hp' : s_in.simpleKeyStack[j].possible = true := by
        simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
      have h_ge := h_inv.2.1 j hfl hlt hp'
      show s_out.simpleKeyStack[j].tokenIndex ≥ n
      simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_ge
    · have hj_eq : j = s_in.simpleKeyStack.size := by omega
      subst hj_eq
      have hp' : s_in.simpleKey.possible = true := by
        simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
      have h_ge := h_inv.1 hp'
      show s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex ≥ n
      simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_ge
  · simp only [h_stack, Array.size_push]; have := h_inv.2.2; omega

lemma SimpleKeyAboveFloor_of_flow_close (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKeyStack.back?.getD {})
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀)
    (h_size : s_in.simpleKeyStack.size > fl₀ ∨ fl₀ = 0) : SimpleKeyAboveFloor s_out n fl₀ := by
  rcases h_size with h_gt | h_zero
  · -- h_gt : s_in.simpleKeyStack.size > fl₀
    refine ⟨fun hp => ?_, fun j hfl hj hp => ?_, ?_⟩
    · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
      have h_back : s_in.simpleKeyStack.back?.getD {} =
          s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
        simp [Array.back?, h_lt]
      rw [h_sk, h_back] at hp ⊢
      exact h_inv.2.1 _ (by omega) h_lt hp
    · simp only [h_stack, Array.size_pop] at hj
      simp only [h_stack, Array.getElem_pop] at hp ⊢
      exact h_inv.2.1 j hfl (by omega) hp
    · simp only [h_stack, Array.size_pop]; omega
  · -- h_zero : fl₀ = 0 — all conjuncts trivially use ≥ 0
    subst h_zero
    refine ⟨fun hp => ?_, fun j hfl hj hp => ?_, by omega⟩
    · by_cases h_nonempty : s_in.simpleKeyStack.size > 0
      · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
        have h_back : s_in.simpleKeyStack.back?.getD {} =
            s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
          simp [Array.back?, h_lt]
        rw [h_sk, h_back] at hp ⊢
        exact h_inv.2.1 _ (by omega) h_lt hp
      · -- Stack is empty: back? = none, so simpleKey = {} with possible = false
        have h_empty : s_in.simpleKeyStack.size = 0 := by omega
        have h_none : s_in.simpleKeyStack.back? = none := by
          simp [Array.back?, h_empty]
        rw [h_sk, h_none] at hp
        simp at hp
    · simp only [h_stack, Array.size_pop] at hj
      simp only [h_stack, Array.getElem_pop] at hp ⊢
      exact h_inv.2.1 j (by omega) (by omega) hp

/-! #### SimpleKeyAboveFloor preprocess and dispatch maintenance -/

lemma preprocess_preserves_flowLevel (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.flowLevel = s.flowLevel := by
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_fl_skip := ScannerCorrectness.skipToContent_preserves_flowLevel s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
            show (unwindIndents s_skip s_skip.col).flowLevel = s.flowLevel
            rw [ScannerCorrectness.unwindIndents_preserves_flowLevel]; exact h_fl_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerCorrectness.saveSimpleKey_preserves_flowLevel]; exact h_fl_skip

lemma preprocess_maintains_SimpleKeyAboveFloor (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s1 n₀ fl₀ := by
  refine ⟨?_, ?_, ?_⟩
  · exact ScannerCorrectness.preprocess_simpleKey_inv s s1 c h n₀ h_n₀ h_inv.1
  · intro j hfl hj hp
    have h_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2.1 j hfl hj hp
  · have h_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s s1 c h
    rw [h_stack]; exact h_inv.2.2

lemma dispatchStructural_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanDocumentStart_clears_simpleKey s)
        (ScannerCorrectness.scanDocumentStart_preserves_simpleKeyStack s) h_inv
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanDocumentEnd_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDocumentEnd_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanDirective_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDirective_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

lemma dispatchFlowIndicators_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  -- Handle flow open, flow entry, flow close, and none/error cases
  all_goals first
    | exact SimpleKeyAboveFloor_of_flow_open _ s n₀ fl₀
        (ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowSequenceStart_stack_pushed s) h_inv
    | exact SimpleKeyAboveFloor_of_flow_open _ s n₀ fl₀
        (ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowMappingStart_stack_pushed s) h_inv
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)
    | -- Flow close (seq end or mapping end)
      -- Derive s.simpleKeyStack.size > fl₀ ∨ fl₀ = 0
      (have h_gt : s.simpleKeyStack.size > fl₀ ∨ fl₀ = 0 := by
        have h_fl := h_fl_post
        first
        | (unfold scanFlowSequenceEnd at h_fl; dsimp only [] at h_fl
           simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel] at h_fl
           split at h_fl
           · left; omega
           · right; omega)
        | (unfold scanFlowMappingEnd at h_fl; dsimp only [] at h_fl
           simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel] at h_fl
           split at h_fl
           · left; omega
           · right; omega)
       first
       | exact SimpleKeyAboveFloor_of_flow_close _ s n₀ fl₀
           (ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s)
           (ScannerCorrectness.scanFlowSequenceEnd_stack_popped s) h_inv h_gt
       | exact SimpleKeyAboveFloor_of_flow_close _ s n₀ fl₀
           (ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s)
           (ScannerCorrectness.scanFlowMappingEnd_stack_popped s) h_inv h_gt)

lemma dispatchBlockIndicators_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanKey_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanKey_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanValue_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanValue_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

lemma dispatchContent_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact SimpleKeyAboveFloor_of_preserved _ _ n₀ fl₀ rfl rfl
        (SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch) h_inv)
  · split at h
    · -- '*': alias
      split at h
      · contradiction
      · generalize h_anch : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s false s_a h_anch)
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s false s_a h_anch)
              h_inv
    · split at h
      · -- '!': tag
        generalize h_tag : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
            (ScannerCorrectness.scanTag_preserves_simpleKey s s_t h_tag)
            (ScannerCorrectness.scanTag_preserves_simpleKeyStack s s_t h_tag) h_inv
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        all_goals (try contradiction)
        all_goals (try (simp only [Except.ok.injEq] at h; subst h))
        all_goals (
          first
    | (exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanBlockScalar_clears_simpleKey s _ h)
        (ScannerCorrectness.scanBlockScalar_preserves_simpleKeyStack s _ h) h_inv)
    | (exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKey s _ h)
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack s _ h) h_inv)
    | (rename_i h_eq_dq _;
       first
       | (have h_sk := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_endLine_update _ s n₀ fl₀
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv)
       | (have h_sk := ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_endLine_update _ s n₀ fl₀
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv))
    | (rename_i h_eq_dq _;
       first
       | (have h_sk := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀ h_sk h_st h_inv)
       | (have h_sk := ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀ h_sk h_st h_inv))
    | (simp_all; done))

/-! #### scanNextToken-level SimpleKeyAboveFloor maintenance -/

-- scanNextToken maintains the `SimpleKeyAboveFloor` invariant, given:
-- (1) stack-flow sync: `simpleKeyStack.size ≥ flowLevel` (links flow level to stack size),
-- (2) `s'.flowLevel ≥ fl₀` (from FlowMonoChain continuation — ensures close-bracket steps
--     don't pop below the floor).
set_option maxHeartbeats 400000 in
lemma scanNextToken_maintains_SimpleKeyAboveFloor (s : ScannerState) (s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · -- preprocess succeeded with some (s1, c)
      rename_i s1 c1 heq_pre
      -- Invariant through preprocess
      have h_pre_inv := preprocess_maintains_SimpleKeyAboveFloor s _ _ (by assumption)
        n₀ fl₀ h_n₀ h_inv
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _
        (by assumption)
      have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s _ _
        (by assumption)
      have h_pre_fl := preprocess_preserves_flowLevel s _ _ (by assumption)
      -- Stack-flow sync through preprocess
      have h_pre_sync : s1.simpleKeyStack.size ≥ s1.flowLevel := by
        rw [h_pre_stack, h_pre_fl]; exact h_sync
      -- allowDirectives preserves simpleKey, stack, and flowLevel
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      have h_allow_stack : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by
        intro st; split <;> rfl
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      have h_allow_fl : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by
        intro st; split <;> rfl
      -- SimpleKeyAboveFloor through allowDirectives
      have h_allow_inv : SimpleKeyAboveFloor
          (if s1.allowDirectives then
            { s1 with allowDirectives := false, documentEverStarted := true }
          else s1) n₀ fl₀ :=
        SimpleKeyAboveFloor_of_preserved _ s1 n₀ fl₀ (h_allow_sk s1) (h_allow_stack s1)
          h_pre_inv
      -- Stack-flow sync through allowDirectives
      have h_allow_sync : (if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1).simpleKeyStack.size ≥ (if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1).flowLevel := by
        rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
      -- Now split on all dispatch cases
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | -- Structural dispatch
          (have h_d := dispatchStructural_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by omega) h_pre_inv;
           exact h_d)
        | -- Flow indicators dispatch (needs sync and fl_post)
          (have h_d := dispatchFlowIndicators_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            h_allow_inv h_allow_sync (by assumption);
           exact h_d)
        | (have h_d := dispatchBlockIndicators_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            h_allow_inv;
           exact h_d)
        | (have h_d := dispatchContent_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            h_allow_inv;
           exact h_d)
        | (simp_all)

/-! #### FlowMonoChain prefix preservation (Step 4)

Token prefix preservation through a `FlowMonoChain`, using `SimpleKeyAboveFloor`
instead of `SimpleKeyAbove`. The key insight is that `scanNextToken_preserves_prefix`
only reads the simpleKey conjunct (not the stack entries), so we can replicate
its proof using just `SimpleKeyAboveFloor.1`. -/

-- Per-step prefix preservation using only the simpleKey conjunct.
-- This is equivalent to `ScannerCorrectness.scanNextToken_preserves_prefix` but
-- takes `SimpleKeyAboveFloor` instead of `SimpleKeyAbove`.
set_option maxHeartbeats 400000 in
lemma scanNextToken_preserves_prefix_of_skFloor (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_sk : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n)
    (i : Nat) (h_bound : i < n) :
    s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[i]'(by omega) := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · have h_pre_pref := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s _ _ (by assumption) i (by omega)
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _ (by assumption)
      have h_sk_inv := ScannerCorrectness.preprocess_simpleKey_inv s _ _ (by assumption) n h_n h_sk
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix _ _ _ (by assumption) i (by omega);
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchFlowIndicators_preserves_prefix _ _ _ (by assumption) i
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchBlockIndicators_preserves_prefix _ _ _ (by assumption) n
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            (by simp only [h_allow_sk]; exact h_sk_inv) i h_bound;
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix _ _ _ (by assumption) i
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (simp_all)

-- Per-step bundle: prefix preservation + SimpleKeyAboveFloor maintenance.
-- Analogous to `scanNextToken_prefix_and_sk_inv` but for the floor-based invariant.
lemma scanNextToken_prefix_and_skFloor_inv (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    (∀ (i : Nat) (hi : i < n₀),
      s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    SimpleKeyAboveFloor s' n₀ fl₀ :=
  ⟨fun i hi => scanNextToken_preserves_prefix_of_skFloor s s' h_next n₀ h_n₀ h_inv.1 i hi,
   scanNextToken_maintains_SimpleKeyAboveFloor s s' h_next n₀ fl₀ h_n₀ h_inv h_sync h_fl_post⟩

-- `scanNextToken` preserves `simpleKeyStack.size ≥ flowLevel`.
-- This is a scanner global invariant: flow opens push+increment, flow closes pop+decrement.
-- Non-flow dispatches preserve both simpleKeyStack and flowLevel.

-- Helper: flow indicator dispatch preserves the sync invariant.
-- Flow opens push+increment, flow closes pop+decrement, flow entry preserves both.
set_option maxHeartbeats 800000 in
lemma dispatchFlowIndicators_preserves_sync (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    s'.simpleKeyStack.size ≥ s'.flowLevel := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- c == '['
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    dsimp only [scanFlowSequenceStart]
    simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
      ScannerCorrectness.advance_preserves_flowLevel,
      ScannerCorrectness.emit_preserves_simpleKeyStack,
      ScannerCorrectness.emit_preserves_flowLevel,
      Array.size_push]; omega
  -- c == ']'
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          dsimp only [scanFlowSequenceEnd]
          simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
            ScannerCorrectness.advance_preserves_flowLevel,
            ScannerCorrectness.emit_preserves_simpleKeyStack,
            ScannerCorrectness.emit_preserves_flowLevel,
            Array.size_pop]; split <;> omega
    -- c == '{'
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        dsimp only [scanFlowMappingStart]
        simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
          ScannerCorrectness.advance_preserves_flowLevel,
          ScannerCorrectness.emit_preserves_simpleKeyStack,
          ScannerCorrectness.emit_preserves_flowLevel,
          Array.size_push]; omega
      -- c == '}'
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              dsimp only [scanFlowMappingEnd]
              simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
                ScannerCorrectness.advance_preserves_flowLevel,
                ScannerCorrectness.emit_preserves_simpleKeyStack,
                ScannerCorrectness.emit_preserves_flowLevel,
                Array.size_pop]; split <;> omega
        -- c == ','
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have h_stack := ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack _ _ h_entry
                have h_fl := ScannerCorrectness.scanFlowEntry_preserves_flowLevel _ _ h_entry
                rw [h_stack, h_fl]; exact h_sync
          -- fallthrough: none
          · simp at h

set_option maxHeartbeats 1200000 in
lemma scanNextToken_preserves_sync (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    s'.simpleKeyStack.size ≥ s'.flowLevel := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next <;> (try (simp at h_next; done)) -- preprocess Except
  split at h_next <;> (try (simp at h_next; done)) -- preprocess Option
  rename_i s1 c1 h_pre
  have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s _ _ h_pre
  have h_pre_fl := preprocess_preserves_flowLevel s _ _ h_pre
  have h_pre_sync : s1.simpleKeyStack.size ≥ s1.flowLevel := by
    rw [h_pre_stack, h_pre_fl]; exact h_sync
  split at h_next <;> (try (simp at h_next; done)) -- structural Except
  split at h_next
  · -- structural some
    simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
    have h_d_stack := ScannerCorrectness.dispatchStructural_preserves_simpleKeyStack
      s1 c1 _ (by assumption)
    have h_d_fl := ScannerCorrectness.dispatchStructural_preserves_flowLevel
      s1 c1 _ (by assumption)
    rw [h_d_stack, h_d_fl]; exact h_pre_sync
  · -- structural none → allowDirectives → flow/block/content
    have h_allow_stack : ∀ st : ScannerState,
      (if st.allowDirectives then
        { st with allowDirectives := false, documentEverStarted := true }
      else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
    have h_allow_fl : ∀ st : ScannerState,
      (if st.allowDirectives then
        { st with allowDirectives := false, documentEverStarted := true }
      else st).flowLevel = st.flowLevel := by intro st; split <;> rfl
    have h_ad_sync : (if s1.allowDirectives then
        { s1 with allowDirectives := false, documentEverStarted := true }
      else s1).simpleKeyStack.size ≥ (if s1.allowDirectives then
        { s1 with allowDirectives := false, documentEverStarted := true }
      else s1).flowLevel := by
      rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
    -- Pending-directives check (Fix B)
    split at h_next <;> (try (simp at h_next; done))
    -- checkBlockFlowIndent
    split at h_next <;> (try (simp at h_next; done))
    -- Flow Except
    split at h_next <;> (try (simp at h_next; done))
    -- Flow Option
    split at h_next
    · -- flow some → use flow dispatch helper
      simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
      exact dispatchFlowIndicators_preserves_sync _ _ _ (by assumption) h_ad_sync
    · -- flow none → block
      split at h_next <;> (try (simp at h_next; done)) -- block Except
      split at h_next
      · -- block some
        simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
        have h_d_stack := ScannerCorrectness.dispatchBlockIndicators_preserves_simpleKeyStack
          _ c1 _ (by assumption)
        have h_d_fl := ScannerCorrectness.dispatchBlockIndicators_preserves_flowLevel
          _ c1 _ (by assumption)
        rw [h_d_stack, h_d_fl]; rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
      · -- block none → content
        split at h_next <;> (try (simp at h_next; done)) -- content Except
        simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
        have h_d_stack := ScannerCorrectness.dispatchContent_preserves_simpleKeyStack
          _ c1 _ (by assumption)
        have h_d_fl := ScannerCorrectness.dispatchContent_preserves_flowLevel
          _ c1 _ (by assumption)
        rw [h_d_stack, h_d_fl]; rw [h_allow_stack, h_allow_fl]; exact h_pre_sync

-- Main chain theorem: token prefix preservation through FlowMonoChain.
-- Mirrors `ScanChain_preserves_raw_prefix` but uses `SimpleKeyAboveFloor` instead of
-- `SimpleKeyAbove`, enabling the proof when stack entries below floor have stale indices.
-- The floor is the chain's `fl₀` (not the state's stack size), since `fl₀` is constant
-- across chain steps and `scanNextToken_maintains_SimpleKeyAboveFloor` preserves it.
lemma FlowMonoChain_preserves_raw_prefix {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_stack_floor : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := FlowMonoChain.tokens_mono h_fmc; omega) =
    s.tokens[i]'(by omega) := by
  induction h_fmc with
  | zero => rfl
  | step h_fl h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have h_fl_mid := h_rest.flowLevel_ge_start
    have h_sk_inv := scanNextToken_maintains_SimpleKeyAboveFloor _ _ h_snt n₀ fl₀
      h_n₀ h_stack_floor h_sync h_fl_mid
    have h_sync' := scanNextToken_preserves_sync _ _ h_snt h_sync
    have h_pres := scanNextToken_preserves_prefix_of_skFloor _ _ h_snt n₀ h_n₀
      h_stack_floor.1 i hi
    exact (ih (Nat.le_trans h_n₀ h_adds) h_sk_inv h_sync').trans h_pres

/-! ## `NoOverwriteAt` — pointwise no-overwrite invariant (substrate.d)

Non-indexed parallel to `NoOverwriteAtIx` (`IndexedEmitterScannability/EmitScansStrong.lean`
§5). Required by the legacy non-indexed consumers
`emitList_body_filtered_characterization` (line 9474, sorry 9550) and
`emitPairList_body_filtered_characterization` (sorries 9644 etc.). The non-indexed and
indexed substrates are independent because the two worlds operate on different state
types (`ScannerState` vs `ScannerStateIx`) with no transport.

Ships in 6 sub-sections paralleling substrate.c §5.1–§5.6:
  - §D.1 def + 4 transport constructors
  - §D.2 saveSimpleKey + preprocess pointwise maintenance
  - §D.3 four dispatcher maintenance lemmas
  - §D.4 scanNextToken capstone
  - §D.5 scanValuePrepare/scanValue/scanNextToken pointwise preservation
  - §D.6 FlowMonoChain chain wrapper

**Closes zero legacy sorries**: pure enablement for `.body1.tokenshape.list` (sorry 9550)
and `.body1.tokenshape.pair` (sorries 9644, 9646).

**Differs from SKAF**: NO sync hypothesis needed (no floor → no stack-size lower bound
for the flow-close case). Mirrors substrate.c's same simplification. -/

/-! ### §D.1  `NoOverwriteAt` and its 4 transport constructors -/

/-- `NoOverwriteAt s m`: position `m` cannot be overwritten by any future simpleKey
    promotion (current or stacked). Non-indexed twin of `NoOverwriteAtIx`
    (`IndexedEmitterScannability/EmitScansStrong.lean §5`). -/
def NoOverwriteAt (s : ScannerState) (m : Nat) : Prop :=
  (s.simpleKey.possible = true →
    m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) ∧
  (∀ (j : Nat) (h : j < s.simpleKeyStack.size),
    s.simpleKeyStack[j].possible = true →
    m ≠ s.simpleKeyStack[j].tokenIndex ∧ m ≠ s.simpleKeyStack[j].tokenIndex + 1)

/-- If `s_out` clears the simple key and preserves the stack, then `NoOverwriteAt`
    transports. Parallel to `NoOverwriteAtIx_of_cleared_preserved`. -/
lemma NoOverwriteAt_of_cleared_preserved
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : NoOverwriteAt s_in m) :
    NoOverwriteAt s_out m :=
  ⟨fun hp => absurd hp (by rw [h_sk]; decide),
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- If `s_out` preserves both `simpleKey` and `simpleKeyStack`, then `NoOverwriteAt`
    transports. Parallel to `NoOverwriteAtIx_of_preserved`. -/
lemma NoOverwriteAt_of_preserved
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : NoOverwriteAt s_in m) :
    NoOverwriteAt s_out m :=
  ⟨fun hp => by rw [h_sk] at hp ⊢; exact h_inv.1 hp,
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- Flow-open transport: `s_out` clears the current simple key and pushes the old
    `simpleKey` onto `simpleKeyStack`. Parallel to `NoOverwriteAtIx_of_flow_open`. -/
lemma NoOverwriteAt_of_flow_open
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : NoOverwriteAt s_in m) :
    NoOverwriteAt s_out m := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hj hp => ?_⟩
  simp only [h_stack, Array.size_push] at hj
  by_cases hlt : j < s_in.simpleKeyStack.size
  · have hp' : s_in.simpleKeyStack[j].possible = true := by
      simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
    have h_orig := h_inv.2 j hlt hp'
    show m ≠ s_out.simpleKeyStack[j].tokenIndex ∧
         m ≠ s_out.simpleKeyStack[j].tokenIndex + 1
    simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_orig
  · have hj_eq : j = s_in.simpleKeyStack.size := by omega
    subst hj_eq
    have hp' : s_in.simpleKey.possible = true := by
      simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
    have h_orig := h_inv.1 hp'
    show m ≠ s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex ∧
         m ≠ s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex + 1
    simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_orig

/-- endLine-update transport: `s_out`'s simpleKey shares `possible` and `tokenIndex`
    with `s_in.simpleKey` (only the `endLine` and `pos` fields may differ) and the
    stack is preserved. Needed for the double-quoted and single-quoted scalar
    dispatch, which updates the simpleKey's endLine field. -/
lemma NoOverwriteAt_of_endLine_update
    (s_out s_in : ScannerState) (m : Nat)
    (h_poss : s_out.simpleKey.possible = s_in.simpleKey.possible)
    (h_idx : s_out.simpleKey.tokenIndex = s_in.simpleKey.tokenIndex)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : NoOverwriteAt s_in m) :
    NoOverwriteAt s_out m :=
  ⟨fun hp => by
    have hp' : s_in.simpleKey.possible = true := by rw [← h_poss]; exact hp
    have := h_inv.1 hp'; rw [h_idx]; exact this,
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- Flow-close transport: `s_out` restores `simpleKey` from `simpleKeyStack.back?`
    and pops the stack. Parallel to `NoOverwriteAtIx_of_flow_close` — NO sync
    hypothesis needed (NoOverwriteAt's stack-entry conjunct covers ALL slots, so
    popping just reduces the universe of obligations). -/
lemma NoOverwriteAt_of_flow_close
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKeyStack.back?.getD {})
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : NoOverwriteAt s_in m) :
    NoOverwriteAt s_out m := by
  refine ⟨fun hp => ?_, fun j hj hp => ?_⟩
  · by_cases h_nonempty : s_in.simpleKeyStack.size > 0
    · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
      have h_back : s_in.simpleKeyStack.back?.getD {} =
          s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
        simp [Array.back?, h_lt]
      rw [h_sk, h_back] at hp ⊢
      exact h_inv.2 _ h_lt hp
    · have h_empty : s_in.simpleKeyStack.size = 0 := by omega
      have h_none : s_in.simpleKeyStack.back? = none := by simp [Array.back?, h_empty]
      rw [h_sk, h_none] at hp; simp at hp
  · simp only [h_stack, Array.size_pop] at hj
    simp only [h_stack, Array.getElem_pop] at hp ⊢
    exact h_inv.2 j (by omega) hp

/-! ### §D.2  saveSimpleKey + preprocess pointwise maintenance -/

/-- `saveSimpleKey` maintains the pointwise no-overwrite invariant on `simpleKey`:
    if the new simpleKey is possible, its `tokenIndex` is either unchanged (no-op
    branch) or set to `st.tokens.size` (set branch), and both satisfy `≠ m` /
    `≠ m + 1` given `m < st.tokens.size`. Parallel to
    `saveSimpleKeyIx_simpleKey_pointwise_inv`. -/
lemma saveSimpleKey_simpleKey_pointwise_inv (st : ScannerState) (m : Nat)
    (h_tok : m < st.tokens.size)
    (h_inv : st.simpleKey.possible = true →
      m ≠ st.simpleKey.tokenIndex ∧ m ≠ st.simpleKey.tokenIndex + 1) :
    (saveSimpleKey st).simpleKey.possible = true →
    m ≠ (saveSimpleKey st).simpleKey.tokenIndex ∧
    m ≠ (saveSimpleKey st).simpleKey.tokenIndex + 1 := by
  unfold saveSimpleKey
  split
  · exact h_inv
  · split
    · intro _; dsimp only []; exact ⟨by omega, by omega⟩
    · exact h_inv

/-- `scanNextToken_preprocess` carries the simpleKey pointwise invariant. Parallel
    to `scanNextTokenIx_preprocess_simpleKey_pointwise_inv`. -/
lemma preprocess_simpleKey_pointwise_inv (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) (m : Nat)
    (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    s1.simpleKey.possible = true →
    m ≠ s1.simpleKey.tokenIndex ∧ m ≠ s1.simpleKey.tokenIndex + 1 := by
  intro h_poss
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_sk_skip := ScannerCorrectness.skipToContent_preserves_simpleKey s s_skip h_skip
    have h_tok_skip := ScannerCorrectness.skipToContent_preserves_tokens s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_sk_u := ScannerCorrectness.unwindIndents_preserves_simpleKey s_skip s_skip.col
            have h_tok_u := ScannerCorrectness.unwindIndents_adds_tokens s_skip s_skip.col
            have h_tok_post : m <
                ({ unwindIndents s_skip s_skip.col with
                  needIndentCheck := false } : ScannerState).tokens.size := by
              show m < (unwindIndents s_skip s_skip.col).tokens.size
              have := congrArg Array.size h_tok_skip; omega
            have h_sk_post :
                ({ unwindIndents s_skip s_skip.col with
                    needIndentCheck := false } : ScannerState).simpleKey.possible = true →
                m ≠ ({ unwindIndents s_skip s_skip.col with
                    needIndentCheck := false } : ScannerState).simpleKey.tokenIndex ∧
                m ≠ ({ unwindIndents s_skip s_skip.col with
                    needIndentCheck := false } : ScannerState).simpleKey.tokenIndex + 1 := by
              show (unwindIndents s_skip s_skip.col).simpleKey.possible = true → _
              simp only [h_sk_u, h_sk_skip]; exact h_inv
            exact saveSimpleKey_simpleKey_pointwise_inv _ m h_tok_post h_sk_post h_poss
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_tok_post : m < s_skip.tokens.size := by
              have := congrArg Array.size h_tok_skip; omega
            have h_sk_post : s_skip.simpleKey.possible = true →
                m ≠ s_skip.simpleKey.tokenIndex ∧
                m ≠ s_skip.simpleKey.tokenIndex + 1 := by
              simp only [h_sk_skip]; exact h_inv
            exact saveSimpleKey_simpleKey_pointwise_inv s_skip m h_tok_post h_sk_post h_poss

/-- `scanNextToken_preprocess` maintains the full `NoOverwriteAt` invariant.
    Parallel to `scanNextTokenIx_preprocess_maintains_NoOverwriteAtIx`. -/
lemma preprocess_maintains_NoOverwriteAt (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (m : Nat) (h_m : m < s.tokens.size) (h_inv : NoOverwriteAt s m) :
    NoOverwriteAt s1 m := by
  refine ⟨?_, ?_⟩
  · exact preprocess_simpleKey_pointwise_inv s s1 c h m h_m h_inv.1
  · intro j hj hp
    have h_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2 j hj hp

/-! ### §D.3  Dispatcher maintenance for NoOverwriteAt -/

/-- `scanNextToken_dispatchStructural` maintains `NoOverwriteAt`. Parallel to
    `dispatchStructural_maintains_SimpleKeyAboveFloor`. -/
lemma dispatchStructural_maintains_NoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : NoOverwriteAt s m) :
    NoOverwriteAt s' m := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact NoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanDocumentStart_clears_simpleKey s)
        (ScannerCorrectness.scanDocumentStart_preserves_simpleKeyStack s) h_inv
    | (rename_i h_eq; exact NoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanDocumentEnd_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDocumentEnd_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact NoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanDirective_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDirective_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextToken_dispatchFlowIndicators` maintains `NoOverwriteAt`. Parallel to
    `dispatchFlowIndicators_maintains_SimpleKeyAboveFloor` but with NO sync or
    flow-level hypotheses needed (NoOverwriteAt's stack-entry conjunct covers ALL
    slots, so popping just reduces the universe of obligations). -/
lemma dispatchFlowIndicators_maintains_NoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : NoOverwriteAt s m) :
    NoOverwriteAt s' m := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact NoOverwriteAt_of_flow_open _ s m
        (ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowSequenceStart_stack_pushed s) h_inv
    | exact NoOverwriteAt_of_flow_open _ s m
        (ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowMappingStart_stack_pushed s) h_inv
    | exact NoOverwriteAt_of_flow_close _ s m
        (ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s)
        (ScannerCorrectness.scanFlowSequenceEnd_stack_popped s) h_inv
    | exact NoOverwriteAt_of_flow_close _ s m
        (ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s)
        (ScannerCorrectness.scanFlowMappingEnd_stack_popped s) h_inv
    | (rename_i h_eq; exact NoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextToken_dispatchBlockIndicators` maintains `NoOverwriteAt`. Parallel to
    `dispatchBlockIndicators_maintains_SimpleKeyAboveFloor`. -/
lemma dispatchBlockIndicators_maintains_NoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : NoOverwriteAt s m) :
    NoOverwriteAt s' m := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact NoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact NoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanKey_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanKey_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact NoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanValue_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanValue_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextToken_dispatchContent` maintains `NoOverwriteAt`. Parallel to
    `dispatchContent_maintains_SimpleKeyAboveFloor`. -/
lemma dispatchContent_maintains_NoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : NoOverwriteAt s m) :
    NoOverwriteAt s' m := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact NoOverwriteAt_of_preserved _ _ m rfl rfl
        (NoOverwriteAt_of_preserved _ s m
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch) h_inv)
  · split at h
    · -- '*': alias
      split at h
      · contradiction
      · generalize h_anch : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact NoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s false s_a h_anch)
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s false s_a h_anch)
              h_inv
    · split at h
      · -- '!': tag
        generalize h_tag : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact NoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanTag_preserves_simpleKey s s_t h_tag)
            (ScannerCorrectness.scanTag_preserves_simpleKeyStack s s_t h_tag) h_inv
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        all_goals (try contradiction)
        all_goals (try (simp only [Except.ok.injEq] at h; subst h))
        all_goals (
          first
    | (exact NoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanBlockScalar_clears_simpleKey s _ h)
        (ScannerCorrectness.scanBlockScalar_preserves_simpleKeyStack s _ h) h_inv)
    | (exact NoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKey s _ h)
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack s _ h) h_inv)
    | (rename_i h_eq_dq _;
       first
       | (have h_sk := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact NoOverwriteAt_of_endLine_update _ s m
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv)
       | (have h_sk := ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact NoOverwriteAt_of_endLine_update _ s m
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv))
    | (rename_i h_eq_dq _;
       first
       | (exact NoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq)
            (ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq) h_inv)
       | (exact NoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq)
            (ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq) h_inv))
    | (simp_all; done))

/-! ### §D.4  scanNextToken capstone for NoOverwriteAt -/

set_option maxHeartbeats 400000 in
/-- Capstone: `scanNextToken` maintains `NoOverwriteAt`. Parallel to
    `scanNextTokenIx_maintains_NoOverwriteAtIx` (substrate.c §5.4) — and to the
    non-indexed `scanNextToken_maintains_SimpleKeyAboveFloor` but with the
    pointwise (≠m) invariant and no sync/flow-level hypotheses. -/
lemma scanNextToken_maintains_NoOverwriteAt (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size) (h_inv : NoOverwriteAt s m) :
    NoOverwriteAt s' m := by
  have h_allow_sk : ∀ st : ScannerState,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by intro st; split <;> rfl
  have h_allow_stack : ∀ st : ScannerState,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
  have h_allow_tok : ∀ st : ScannerState,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
  unfold scanNextToken at h_next
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · rename_i s1 c1 hPre
      have h_pre_inv := preprocess_maintains_NoOverwriteAt s _ _ hPre m h_m h_inv
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _ hPre
      have h_pre_m : m < s1.tokens.size := Nat.lt_of_lt_of_le h_m h_pre_mono
      split at h_next
      · contradiction
      · split at h_next
        · rename_i s'' hStruct
          simp only [Except.ok.injEq, Option.some.injEq] at h_next
          subst h_next
          exact dispatchStructural_maintains_NoOverwriteAt _ _ _ hStruct m h_pre_m h_pre_inv
        · have h_s2_inv : NoOverwriteAt
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1) m :=
            NoOverwriteAt_of_preserved _ s1 m
              (h_allow_sk s1) (h_allow_stack s1) h_pre_inv
          have h_s2_m : m <
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1).tokens.size := by
            rw [h_allow_tok]; exact h_pre_m
          split at h_next
          · contradiction
          · split at h_next
            · contradiction
            · split at h_next
              · contradiction
              · split at h_next
                · rename_i s'' hFlow
                  simp only [Except.ok.injEq, Option.some.injEq] at h_next
                  subst h_next
                  exact dispatchFlowIndicators_maintains_NoOverwriteAt _ _ _ hFlow m h_s2_m h_s2_inv
                · split at h_next
                  · contradiction
                  · split at h_next
                    · rename_i s'' hBlock
                      simp only [Except.ok.injEq, Option.some.injEq] at h_next
                      subst h_next
                      exact dispatchBlockIndicators_maintains_NoOverwriteAt _ _ _ hBlock
                        m h_s2_m h_s2_inv
                    · split at h_next
                      · contradiction
                      · rename_i sC hContent
                        simp only [Except.ok.injEq, Option.some.injEq] at h_next
                        subst h_next
                        exact dispatchContent_maintains_NoOverwriteAt _ _ _ hContent
                          m h_s2_m h_s2_inv

/-! ### §D.5  Step-level pointwise preservation -/

/-- Pointwise (≠m) form of `scanValuePrepare_preserves_prefix`. Mirrors the
    prefix-form proof but uses the pointwise hypothesis directly. -/
lemma scanValuePrepare_preserves_position_specific (s : ScannerState)
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    (scanValuePrepare s).tokens[m]'(by
        have := ScannerCorrectness.scanValuePrepare_tokens_monotonic s; omega) =
    s.tokens[m]'h_m := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    obtain ⟨h_ne_idx, h_ne_idx1⟩ := h_inv h_poss
    split
    · split
      · -- !inFlow, keyCol > currentIndent: two setIfInBounds at idx, idx+1
        dsimp only []
        rw [Array.getElem_setIfInBounds (by simp [Array.size_setIfInBounds]; omega)]
        simp only [show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm,
          ite_false]
        rw [Array.getElem_setIfInBounds (by omega)]
        simp only [show s.simpleKey.tokenIndex ≠ m from fun h => h_ne_idx h.symm, ite_false]
      · -- !inFlow, keyCol ≤ currentIndent: one setIfInBounds at idx+1
        dsimp only []
        rw [Array.getElem_setIfInBounds (by omega)]
        simp only [show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm,
          ite_false]
    · -- inFlow: one setIfInBounds at idx+1
      dsimp only []
      rw [Array.getElem_setIfInBounds (by omega)]
      simp only [show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm,
        ite_false]
  · -- simpleKey.possible = false
    split
    · -- explicitKeyLine.isSome: only simpleKey field changes
      dsimp only []
    · split
      · -- !inFlow: pushMappingIndent
        exact ScannerCorrectness.ScanHelpers.pushMappingIndent_preserves_prefix s s.col m h_m
      · -- inFlow: identity
        rfl

/-- Pointwise (≠m) form of `scanValue_preserves_prefix`. -/
lemma scanValue_preserves_position_specific (s s' : ScannerState)
    (h_ok : scanValue s = .ok s')
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by have := ScannerCorrectness.scanValue_adds_tokens s s' h_ok; omega) =
    s.tokens[m]'h_m := by
  unfold scanValue at h_ok
  dsimp only [] at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · contradiction
  · split at h_ok
    · contradiction
    · injection h_ok with h_eq
      subst h_eq
      dsimp only []
      have h_ck := ScannerCorrectness.scanValueClearKey_preserves_tokens s
      have h_inv' : (scanValueClearKey s).simpleKey.possible = true →
          m ≠ (scanValueClearKey s).simpleKey.tokenIndex ∧
          m ≠ (scanValueClearKey s).simpleKey.tokenIndex + 1 := by
        unfold scanValueClearKey
        split
        · split
          · simp
          · split
            · simp
            · exact h_inv
        · exact h_inv
      have h_m' : m < (scanValueClearKey s).tokens.size := by rw [h_ck]; exact h_m
      have h_prep := scanValuePrepare_preserves_position_specific (scanValueClearKey s)
        m h_m' h_inv'
      have h_prep_sz := ScannerCorrectness.scanValuePrepare_tokens_monotonic
        (scanValueClearKey s)
      have h_m_lt_prep : m < (scanValuePrepare (scanValueClearKey s)).tokens.size := by
        rw [h_ck] at h_prep_sz; omega
      have h_emit := ScannerCorrectness.emit_preserves_tokens_at
        (scanValuePrepare (scanValueClearKey s)) YamlToken.value m h_m_lt_prep
      have h_adv := ScannerCorrectness.advance_preserves_tokens
        ((scanValuePrepare (scanValueClearKey s)).emit .value)
      simp_all

/-- Pointwise (≠m) version of `dispatchBlockIndicators_preserves_prefix`. The
    block-indicators dispatcher is the only one of the four that can call
    `scanValue` (which overwrites via `scanValuePrepare`), hence the pointwise
    hypothesis is needed here specifically. -/
lemma dispatchBlockIndicators_preserves_position_specific (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by
      have := ScannerCorrectness.ScanHelpers.dispatchBlockIndicators_tokens_mono s c s' h;
      omega) =
    s.tokens[m]'h_m := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := ScannerCorrectness.ScanHelpers.scanBlockEntry_preserves_prefix s _
        (by assumption) m h_m; simp_all)
    | (have := ScannerCorrectness.ScanHelpers.scanKey_preserves_prefix s _
        (by assumption) m h_m; simp_all)
    | (have := scanValue_preserves_position_specific s _ (by assumption) m h_m h_inv; simp_all)
    | (simp_all)

set_option maxHeartbeats 400000 in
/-- Per-step pointwise preservation of position `m` through `scanNextToken`.
    Parallel to `scanNextTokenIx_preserves_position_specific` but with the
    monolithic dispatcher case-analysis style of the non-indexed
    `scanNextToken_preserves_prefix_of_skFloor`. -/
lemma scanNextToken_preserves_position_specific (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex ∧ m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[m]'h_m := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · have h_pre_pref := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s _ _
        (by assumption) m (by omega)
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _
        (by assumption)
      have h_sk_inv := preprocess_simpleKey_pointwise_inv s _ _ (by assumption) m h_m h_inv
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix _ _ _
            (by assumption) m (by omega);
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchFlowIndicators_preserves_prefix _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := dispatchBlockIndicators_preserves_position_specific _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            (by simp only [h_allow_sk]; exact h_sk_inv);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (simp_all)

/-! ### §D.6  Chain-induction wrapper -/

/-- Chain-induction wrapper for pointwise position preservation through a
    `FlowMonoChain`. Parallel to `FlowMonoChainIx_preserves_position_specific`
    (substrate.c §5.6) and to `FlowMonoChain_preserves_raw_prefix` (the
    non-indexed SKAF-form), but with `NoOverwriteAt m` instead of
    `SimpleKeyAboveFloor`. -/
lemma FlowMonoChain_preserves_position_specific
    {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : NoOverwriteAt s m) :
    ∃ (h_size : m < s'.tokens.size),
      s'.tokens[m]'h_size = s.tokens[m]'h_m := by
  induction h_fmc with
  | zero => exact ⟨h_m, rfl⟩
  | @step s s_mid s' n _ h_snt h_rest ih =>
    have h_inv_mid := scanNextToken_maintains_NoOverwriteAt s s_mid h_snt m h_m h_inv
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
    have h_step_size : m < s_mid.tokens.size := by omega
    have h_step_eq := scanNextToken_preserves_position_specific s s_mid h_snt m h_m h_inv.1
    obtain ⟨h_rest_size, h_rest_eq⟩ := ih h_step_size h_inv_mid
    exact ⟨h_rest_size, h_rest_eq.trans h_step_eq⟩

/-! ## `FlowNoOverwriteAt` — flow-relaxed pointwise no-overwrite invariant (substrate.e)

Flow-relaxed parallel to `NoOverwriteAt` (substrate.d §D). The two-clause
`NoOverwriteAt` conservatively forbids `m = tokenIndex` AND `m = tokenIndex + 1`
because BLOCK context's `scanValuePrepare` writes at BOTH `idx` (with
`.blockMappingStart`) and `idx + 1` (with `.key`). In FLOW context,
`scanValuePrepare` writes only at `idx + 1`, so the `m ≠ tokenIndex` clause is
unnecessary; the one-clause relaxation suffices.

Required by `.body1.tokenshape.list` (sorry 9550) to preserve raw position
`m = N` for the `"` head item case, where `s_first.simpleKey.possible = true`
with `tokenIndex = N` makes substrate.d's `NoOverwriteAt N` fail
(`N = tokenIndex`). With flow relaxation, only `N ≠ tokenIndex + 1`
(`N ≠ N + 1`) is needed — which holds. See Reflection 158.

Ships in 6 sub-sections paralleling substrate.d §D.1–§D.6:
  - §E.1 def + 5 transports (cleared/preserved/flow-open/flow-close + endLine-update)
  - §E.2 saveSimpleKey + preprocess pointwise maintenance (one-clause)
  - §E.3 four dispatcher maintenance lemmas
  - §E.4 scanNextToken capstone
  - §E.5 scanValuePrepare/scanValue/scanNextToken pointwise preservation
        (with `s.inFlow = true`)
  - §E.6 FlowMonoChain chain wrapper (with `fl₀ ≥ 1`)

**Closes zero legacy sorries**: pure enablement for `.body1.tokenshape.list`'s
position-`N` half of the raw-prefix bridge. -/

/-! ### §E.1  `FlowNoOverwriteAt` and its 5 transport constructors -/

/-- `FlowNoOverwriteAt s m`: position `m` cannot be overwritten by any future
    `scanValuePrepare` write in FLOW context. Flow-relaxed twin of `NoOverwriteAt`
    (substrate.d §D.1): the `m ≠ tokenIndex` clause is dropped because in flow
    context `scanValuePrepare` writes only at `tokenIndex + 1` (the `.key` slot),
    not at `tokenIndex` (which would be `.blockMappingStart` in block context). -/
def FlowNoOverwriteAt (s : ScannerState) (m : Nat) : Prop :=
  (s.simpleKey.possible = true → m ≠ s.simpleKey.tokenIndex + 1) ∧
  (∀ (j : Nat) (h : j < s.simpleKeyStack.size),
    s.simpleKeyStack[j].possible = true →
    m ≠ s.simpleKeyStack[j].tokenIndex + 1)

/-- If `s_out` clears the simple key and preserves the stack, then
    `FlowNoOverwriteAt` transports. Parallel to `NoOverwriteAt_of_cleared_preserved`. -/
lemma FlowNoOverwriteAt_of_cleared_preserved
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : FlowNoOverwriteAt s_in m) :
    FlowNoOverwriteAt s_out m :=
  ⟨fun hp => absurd hp (by rw [h_sk]; decide),
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- If `s_out` preserves both `simpleKey` and `simpleKeyStack`, then
    `FlowNoOverwriteAt` transports. Parallel to `NoOverwriteAt_of_preserved`. -/
lemma FlowNoOverwriteAt_of_preserved
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : FlowNoOverwriteAt s_in m) :
    FlowNoOverwriteAt s_out m :=
  ⟨fun hp => by rw [h_sk] at hp ⊢; exact h_inv.1 hp,
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- Flow-open transport: `s_out` clears the current simple key and pushes the old
    `simpleKey` onto `simpleKeyStack`. Parallel to `NoOverwriteAt_of_flow_open`. -/
lemma FlowNoOverwriteAt_of_flow_open
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : FlowNoOverwriteAt s_in m) :
    FlowNoOverwriteAt s_out m := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hj hp => ?_⟩
  simp only [h_stack, Array.size_push] at hj
  by_cases hlt : j < s_in.simpleKeyStack.size
  · have hp' : s_in.simpleKeyStack[j].possible = true := by
      simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
    have h_orig := h_inv.2 j hlt hp'
    show m ≠ s_out.simpleKeyStack[j].tokenIndex + 1
    simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_orig
  · have hj_eq : j = s_in.simpleKeyStack.size := by omega
    subst hj_eq
    have hp' : s_in.simpleKey.possible = true := by
      simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
    have h_orig := h_inv.1 hp'
    show m ≠ s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex + 1
    simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_orig

/-- endLine-update transport: `s_out`'s simpleKey shares `possible` and `tokenIndex`
    with `s_in.simpleKey` (only the `endLine` and `pos` fields may differ) and the
    stack is preserved. Parallel to `NoOverwriteAt_of_endLine_update`. -/
lemma FlowNoOverwriteAt_of_endLine_update
    (s_out s_in : ScannerState) (m : Nat)
    (h_poss : s_out.simpleKey.possible = s_in.simpleKey.possible)
    (h_idx : s_out.simpleKey.tokenIndex = s_in.simpleKey.tokenIndex)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : FlowNoOverwriteAt s_in m) :
    FlowNoOverwriteAt s_out m :=
  ⟨fun hp => by
    have hp' : s_in.simpleKey.possible = true := by rw [← h_poss]; exact hp
    have := h_inv.1 hp'; rw [h_idx]; exact this,
   fun j hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp⟩

/-- Flow-close transport: `s_out` restores `simpleKey` from `simpleKeyStack.back?`
    and pops the stack. Parallel to `NoOverwriteAt_of_flow_close`. -/
lemma FlowNoOverwriteAt_of_flow_close
    (s_out s_in : ScannerState) (m : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKeyStack.back?.getD {})
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : FlowNoOverwriteAt s_in m) :
    FlowNoOverwriteAt s_out m := by
  refine ⟨fun hp => ?_, fun j hj hp => ?_⟩
  · by_cases h_nonempty : s_in.simpleKeyStack.size > 0
    · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
      have h_back : s_in.simpleKeyStack.back?.getD {} =
          s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
        simp [Array.back?, h_lt]
      rw [h_sk, h_back] at hp ⊢
      exact h_inv.2 _ h_lt hp
    · have h_empty : s_in.simpleKeyStack.size = 0 := by omega
      have h_none : s_in.simpleKeyStack.back? = none := by simp [Array.back?, h_empty]
      rw [h_sk, h_none] at hp; simp at hp
  · simp only [h_stack, Array.size_pop] at hj
    simp only [h_stack, Array.getElem_pop] at hp ⊢
    exact h_inv.2 j (by omega) hp

/-! ### §E.2  saveSimpleKey + preprocess pointwise maintenance (one-clause) -/

/-- One-clause `saveSimpleKey` pointwise maintenance. Parallel to
    `saveSimpleKey_simpleKey_pointwise_inv` but tracking only `≠ tokenIndex + 1`. -/
lemma saveSimpleKey_simpleKey_pointwise_inv_flow (st : ScannerState) (m : Nat)
    (h_tok : m < st.tokens.size)
    (h_inv : st.simpleKey.possible = true →
      m ≠ st.simpleKey.tokenIndex + 1) :
    (saveSimpleKey st).simpleKey.possible = true →
    m ≠ (saveSimpleKey st).simpleKey.tokenIndex + 1 := by
  unfold saveSimpleKey
  split
  · exact h_inv
  · split
    · intro _; dsimp only []; omega
    · exact h_inv

/-- One-clause `scanNextToken_preprocess` simpleKey maintenance. Parallel to
    `preprocess_simpleKey_pointwise_inv`. -/
lemma preprocess_simpleKey_pointwise_inv_flow (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) (m : Nat)
    (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex + 1) :
    s1.simpleKey.possible = true →
    m ≠ s1.simpleKey.tokenIndex + 1 := by
  intro h_poss
  unfold scanNextToken_preprocess at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_sk_skip := ScannerCorrectness.skipToContent_preserves_simpleKey s s_skip h_skip
    have h_tok_skip := ScannerCorrectness.skipToContent_preserves_tokens s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_sk_u := ScannerCorrectness.unwindIndents_preserves_simpleKey s_skip s_skip.col
            have h_tok_u := ScannerCorrectness.unwindIndents_adds_tokens s_skip s_skip.col
            have h_tok_post : m <
                ({ unwindIndents s_skip s_skip.col with
                  needIndentCheck := false } : ScannerState).tokens.size := by
              show m < (unwindIndents s_skip s_skip.col).tokens.size
              have := congrArg Array.size h_tok_skip; omega
            have h_sk_post :
                ({ unwindIndents s_skip s_skip.col with
                    needIndentCheck := false } : ScannerState).simpleKey.possible = true →
                m ≠ ({ unwindIndents s_skip s_skip.col with
                    needIndentCheck := false } : ScannerState).simpleKey.tokenIndex + 1 := by
              show (unwindIndents s_skip s_skip.col).simpleKey.possible = true → _
              simp only [h_sk_u, h_sk_skip]; exact h_inv
            exact saveSimpleKey_simpleKey_pointwise_inv_flow _ m h_tok_post h_sk_post h_poss
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_tok_post : m < s_skip.tokens.size := by
              have := congrArg Array.size h_tok_skip; omega
            have h_sk_post : s_skip.simpleKey.possible = true →
                m ≠ s_skip.simpleKey.tokenIndex + 1 := by
              simp only [h_sk_skip]; exact h_inv
            exact saveSimpleKey_simpleKey_pointwise_inv_flow s_skip m h_tok_post h_sk_post h_poss

/-- `scanNextToken_preprocess` maintains the full `FlowNoOverwriteAt` invariant.
    Parallel to `preprocess_maintains_NoOverwriteAt`. -/
lemma preprocess_maintains_FlowNoOverwriteAt (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (m : Nat) (h_m : m < s.tokens.size) (h_inv : FlowNoOverwriteAt s m) :
    FlowNoOverwriteAt s1 m := by
  refine ⟨?_, ?_⟩
  · exact preprocess_simpleKey_pointwise_inv_flow s s1 c h m h_m h_inv.1
  · intro j hj hp
    have h_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2 j hj hp

/-! ### §E.3  Dispatcher maintenance for FlowNoOverwriteAt -/

/-- `scanNextToken_dispatchStructural` maintains `FlowNoOverwriteAt`. Parallel to
    `dispatchStructural_maintains_NoOverwriteAt`. -/
lemma dispatchStructural_maintains_FlowNoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : FlowNoOverwriteAt s m) :
    FlowNoOverwriteAt s' m := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact FlowNoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanDocumentStart_clears_simpleKey s)
        (ScannerCorrectness.scanDocumentStart_preserves_simpleKeyStack s) h_inv
    | (rename_i h_eq; exact FlowNoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanDocumentEnd_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDocumentEnd_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact FlowNoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanDirective_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDirective_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextToken_dispatchFlowIndicators` maintains `FlowNoOverwriteAt`. Parallel
    to `dispatchFlowIndicators_maintains_NoOverwriteAt`. -/
lemma dispatchFlowIndicators_maintains_FlowNoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : FlowNoOverwriteAt s m) :
    FlowNoOverwriteAt s' m := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact FlowNoOverwriteAt_of_flow_open _ s m
        (ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowSequenceStart_stack_pushed s) h_inv
    | exact FlowNoOverwriteAt_of_flow_open _ s m
        (ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowMappingStart_stack_pushed s) h_inv
    | exact FlowNoOverwriteAt_of_flow_close _ s m
        (ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s)
        (ScannerCorrectness.scanFlowSequenceEnd_stack_popped s) h_inv
    | exact FlowNoOverwriteAt_of_flow_close _ s m
        (ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s)
        (ScannerCorrectness.scanFlowMappingEnd_stack_popped s) h_inv
    | (rename_i h_eq; exact FlowNoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextToken_dispatchBlockIndicators` maintains `FlowNoOverwriteAt`. Parallel
    to `dispatchBlockIndicators_maintains_NoOverwriteAt`. -/
lemma dispatchBlockIndicators_maintains_FlowNoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : FlowNoOverwriteAt s m) :
    FlowNoOverwriteAt s' m := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact FlowNoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact FlowNoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanKey_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanKey_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact FlowNoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanValue_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanValue_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

/-- `scanNextToken_dispatchContent` maintains `FlowNoOverwriteAt`. Parallel to
    `dispatchContent_maintains_NoOverwriteAt`. -/
lemma dispatchContent_maintains_FlowNoOverwriteAt (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (m : Nat) (_h_m : m < s.tokens.size) (h_inv : FlowNoOverwriteAt s m) :
    FlowNoOverwriteAt s' m := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact FlowNoOverwriteAt_of_preserved _ _ m rfl rfl
        (FlowNoOverwriteAt_of_preserved _ s m
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch) h_inv)
  · split at h
    · -- '*': alias
      split at h
      · contradiction
      · generalize h_anch : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact FlowNoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s false s_a h_anch)
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s false s_a h_anch)
              h_inv
    · split at h
      · -- '!': tag
        generalize h_tag : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact FlowNoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanTag_preserves_simpleKey s s_t h_tag)
            (ScannerCorrectness.scanTag_preserves_simpleKeyStack s s_t h_tag) h_inv
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        all_goals (try contradiction)
        all_goals (try (simp only [Except.ok.injEq] at h; subst h))
        all_goals (
          first
    | (exact FlowNoOverwriteAt_of_cleared_preserved _ s m
        (ScannerCorrectness.scanBlockScalar_clears_simpleKey s _ h)
        (ScannerCorrectness.scanBlockScalar_preserves_simpleKeyStack s _ h) h_inv)
    | (exact FlowNoOverwriteAt_of_preserved _ s m
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKey s _ h)
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack s _ h) h_inv)
    | (rename_i h_eq_dq _;
       first
       | (have h_sk := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact FlowNoOverwriteAt_of_endLine_update _ s m
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv)
       | (have h_sk := ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact FlowNoOverwriteAt_of_endLine_update _ s m
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv))
    | (rename_i h_eq_dq _;
       first
       | (exact FlowNoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq)
            (ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq) h_inv)
       | (exact FlowNoOverwriteAt_of_preserved _ s m
            (ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq)
            (ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq) h_inv))
    | (simp_all; done))

/-! ### §E.4  scanNextToken capstone for FlowNoOverwriteAt -/

set_option maxHeartbeats 400000 in
/-- Capstone: `scanNextToken` maintains `FlowNoOverwriteAt`. Parallel to
    `scanNextToken_maintains_NoOverwriteAt` (substrate.d §D.4). -/
lemma scanNextToken_maintains_FlowNoOverwriteAt (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size) (h_inv : FlowNoOverwriteAt s m) :
    FlowNoOverwriteAt s' m := by
  have h_allow_sk : ∀ st : ScannerState,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by intro st; split <;> rfl
  have h_allow_stack : ∀ st : ScannerState,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
  have h_allow_tok : ∀ st : ScannerState,
      (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
  unfold scanNextToken at h_next
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · rename_i s1 c1 hPre
      have h_pre_inv := preprocess_maintains_FlowNoOverwriteAt s _ _ hPre m h_m h_inv
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _ hPre
      have h_pre_m : m < s1.tokens.size := Nat.lt_of_lt_of_le h_m h_pre_mono
      split at h_next
      · contradiction
      · split at h_next
        · rename_i s'' hStruct
          simp only [Except.ok.injEq, Option.some.injEq] at h_next
          subst h_next
          exact dispatchStructural_maintains_FlowNoOverwriteAt _ _ _ hStruct m h_pre_m h_pre_inv
        · have h_s2_inv : FlowNoOverwriteAt
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1) m :=
            FlowNoOverwriteAt_of_preserved _ s1 m
              (h_allow_sk s1) (h_allow_stack s1) h_pre_inv
          have h_s2_m : m <
              (if s1.allowDirectives then
                  { s1 with allowDirectives := false, documentEverStarted := true }
                else s1).tokens.size := by
            rw [h_allow_tok]; exact h_pre_m
          split at h_next
          · contradiction
          · split at h_next
            · contradiction
            · split at h_next
              · contradiction
              · split at h_next
                · rename_i s'' hFlow
                  simp only [Except.ok.injEq, Option.some.injEq] at h_next
                  subst h_next
                  exact dispatchFlowIndicators_maintains_FlowNoOverwriteAt _ _ _ hFlow
                    m h_s2_m h_s2_inv
                · split at h_next
                  · contradiction
                  · split at h_next
                    · rename_i s'' hBlock
                      simp only [Except.ok.injEq, Option.some.injEq] at h_next
                      subst h_next
                      exact dispatchBlockIndicators_maintains_FlowNoOverwriteAt _ _ _ hBlock
                        m h_s2_m h_s2_inv
                    · split at h_next
                      · contradiction
                      · rename_i sC hContent
                        simp only [Except.ok.injEq, Option.some.injEq] at h_next
                        subst h_next
                        exact dispatchContent_maintains_FlowNoOverwriteAt _ _ _ hContent
                          m h_s2_m h_s2_inv

/-! ### §E.5  Step-level pointwise preservation (with `s.inFlow = true`) -/

/-- `scanValueClearKey` preserves `flowLevel`. -/
lemma scanValueClearKey_preserves_flowLevel (s : ScannerState) :
    (scanValueClearKey s).flowLevel = s.flowLevel := by
  unfold scanValueClearKey
  split
  · split
    · rfl
    · split
      · rfl
      · rfl
  · rfl

/-- Pointwise (≠ idx+1) form of `scanValuePrepare_preserves_position_specific`,
    restricted to FLOW context. In flow, `scanValuePrepare` writes only at
    `idx + 1`, so the one-clause hypothesis suffices. Parallel to substrate.d's
    two-clause version (line 2508). -/
lemma scanValuePrepare_preserves_position_specific_flow (s : ScannerState)
    (h_in_flow : s.inFlow = true)
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex + 1) :
    (scanValuePrepare s).tokens[m]'(by
        have := ScannerCorrectness.scanValuePrepare_tokens_monotonic s; omega) =
    s.tokens[m]'h_m := by
  unfold scanValuePrepare
  split
  · rename_i h_poss
    have h_ne_idx1 := h_inv h_poss
    split
    · -- !inFlow: impossible
      rename_i h_neg
      simp [h_in_flow] at h_neg
    · -- inFlow: one setIfInBounds at idx+1
      dsimp only []
      rw [Array.getElem_setIfInBounds (by omega)]
      simp only [show s.simpleKey.tokenIndex + 1 ≠ m from fun h => h_ne_idx1 h.symm,
        ite_false]
  · split
    · -- explicitKeyLine.isSome
      dsimp only []
    · split
      · -- !inFlow: impossible
        rename_i h_neg
        simp [h_in_flow] at h_neg
      · -- inFlow: identity
        rfl

/-- Pointwise (≠ idx+1) form of `scanValue_preserves_position_specific`,
    restricted to FLOW context. -/
lemma scanValue_preserves_position_specific_flow (s s' : ScannerState)
    (h_in_flow : s.inFlow = true)
    (h_ok : scanValue s = .ok s')
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by have := ScannerCorrectness.scanValue_adds_tokens s s' h_ok; omega) =
    s.tokens[m]'h_m := by
  unfold scanValue at h_ok
  dsimp only [] at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · contradiction
  · split at h_ok
    · contradiction
    · injection h_ok with h_eq
      subst h_eq
      dsimp only []
      have h_ck := ScannerCorrectness.scanValueClearKey_preserves_tokens s
      have h_ck_fl := scanValueClearKey_preserves_flowLevel s
      have h_kc_in_flow : (scanValueClearKey s).inFlow = true := by
        unfold ScannerState.inFlow at h_in_flow ⊢
        rw [h_ck_fl]
        exact h_in_flow
      have h_inv' : (scanValueClearKey s).simpleKey.possible = true →
          m ≠ (scanValueClearKey s).simpleKey.tokenIndex + 1 := by
        unfold scanValueClearKey
        split
        · split
          · simp
          · split
            · simp
            · exact h_inv
        · exact h_inv
      have h_m' : m < (scanValueClearKey s).tokens.size := by rw [h_ck]; exact h_m
      have h_prep := scanValuePrepare_preserves_position_specific_flow
        (scanValueClearKey s) h_kc_in_flow m h_m' h_inv'
      have h_prep_sz := ScannerCorrectness.scanValuePrepare_tokens_monotonic
        (scanValueClearKey s)
      have h_m_lt_prep : m < (scanValuePrepare (scanValueClearKey s)).tokens.size := by
        rw [h_ck] at h_prep_sz; omega
      have h_emit := ScannerCorrectness.emit_preserves_tokens_at
        (scanValuePrepare (scanValueClearKey s)) YamlToken.value m h_m_lt_prep
      have h_adv := ScannerCorrectness.advance_preserves_tokens
        ((scanValuePrepare (scanValueClearKey s)).emit .value)
      simp_all

/-- Pointwise (≠ idx+1) version of `dispatchBlockIndicators_preserves_position_specific`,
    restricted to FLOW context. -/
lemma dispatchBlockIndicators_preserves_position_specific_flow (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h_in_flow : s.inFlow = true)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by
      have := ScannerCorrectness.ScanHelpers.dispatchBlockIndicators_tokens_mono s c s' h;
      omega) =
    s.tokens[m]'h_m := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := ScannerCorrectness.ScanHelpers.scanBlockEntry_preserves_prefix s _
        (by assumption) m h_m; simp_all)
    | (have := ScannerCorrectness.ScanHelpers.scanKey_preserves_prefix s _
        (by assumption) m h_m; simp_all)
    | (have := scanValue_preserves_position_specific_flow s _ h_in_flow (by assumption) m h_m h_inv;
       simp_all)
    | (simp_all)

set_option maxHeartbeats 400000 in
/-- Per-step pointwise preservation of position `m` through `scanNextToken`,
    restricted to FLOW context. Parallel to `scanNextToken_preserves_position_specific`
    (substrate.d §D.5) with the flow-relaxed hypothesis. -/
lemma scanNextToken_preserves_position_specific_flow (s s' : ScannerState)
    (h_in_flow : s.inFlow = true)
    (h_next : scanNextToken s = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : s.simpleKey.possible = true →
      m ≠ s.simpleKey.tokenIndex + 1) :
    s'.tokens[m]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[m]'h_m := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · rename_i s1 c1 hPre
      have h_pre_pref := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s s1 c1
        hPre m (by omega)
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s s1 c1 hPre
      have h_pre_fl := preprocess_preserves_flowLevel s s1 c1 hPre
      have h_sk_inv := preprocess_simpleKey_pointwise_inv_flow s s1 c1 hPre m h_m h_inv
      have h_s1_in_flow : s1.inFlow = true := by
        unfold ScannerState.inFlow at h_in_flow ⊢
        rw [h_pre_fl]
        exact h_in_flow
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      have h_allow_fl : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by
        intro st; split <;> rfl
      have h_s2_in_flow : (if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1).inFlow = true := by
        unfold ScannerState.inFlow at h_s1_in_flow ⊢
        rw [h_allow_fl s1]
        exact h_s1_in_flow
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix _ _ _
            (by assumption) m (by omega);
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchFlowIndicators_preserves_prefix _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := dispatchBlockIndicators_preserves_position_specific_flow _ _ _
            h_s2_in_flow
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            (by simp only [h_allow_sk]; exact h_sk_inv);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (simp_all)

/-! ### §E.6  Chain-induction wrapper (with `fl₀ ≥ 1`) -/

/-- Chain-induction wrapper for pointwise position preservation through a
    `FlowMonoChain` in genuine flow context (`fl₀ ≥ 1` ensures every state in
    the chain has `inFlow = true`). Parallel to
    `FlowMonoChain_preserves_position_specific` (substrate.d §D.6) with the
    flow-relaxed hypothesis throughout. -/
lemma FlowMonoChain_preserves_position_specific_flow
    {s s' : ScannerState} {n fl₀ : Nat}
    (h_fl_pos : fl₀ ≥ 1)
    (h_fmc : FlowMonoChain fl₀ s n s')
    (m : Nat) (h_m : m < s.tokens.size)
    (h_inv : FlowNoOverwriteAt s m) :
    ∃ (h_size : m < s'.tokens.size),
      s'.tokens[m]'h_size = s.tokens[m]'h_m := by
  induction h_fmc with
  | zero => exact ⟨h_m, rfl⟩
  | @step s s_mid s' n h_fl h_snt h_rest ih =>
    have h_in_flow : s.inFlow = true := by
      unfold ScannerState.inFlow
      exact decide_eq_true (by omega)
    have h_inv_mid := scanNextToken_maintains_FlowNoOverwriteAt s s_mid h_snt m h_m h_inv
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
    have h_step_size : m < s_mid.tokens.size := by omega
    have h_step_eq := scanNextToken_preserves_position_specific_flow s s_mid h_in_flow h_snt
      m h_m h_inv.1
    obtain ⟨h_rest_size, h_rest_eq⟩ := ih h_step_size h_inv_mid
    exact ⟨h_rest_size, h_rest_eq.trans h_step_eq⟩

/-! ## `SavedKeyDoesntResolve` — saved-key-doesn't-resolve structural primitive (substrate.f)

Per-position chain predicate that captures the residual `m = N + 1` case
left unresolved by substrate.e's flow-relaxed `FlowNoOverwriteAt`. Required
by `.body1.tokenshape.list` (sorry 9550) because at the chain step where
`scanFlowEnd` restores `simpleKey` from `simpleKeyStack`, the restored
`tokenIndex` equals `N` (the head item's slot), so even the one-clause
relaxation's `tokenIndex + 1 ≠ N + 1` collapses to `N + 1 ≠ N + 1` — false.

`FlowNoOverwriteAt N+1` cannot be a chain-stable invariant, but position
`N + 1` is still preserved because in emitList body chains `scanValuePrepare`
never *fires* on the restored simpleKey: the only character that triggers
`scanValuePrepare` (via `scanValue`) is `:`, and `:` does not follow
`[` / `{` / `"` in the emit output for a list head item. This is a
non-local input-shape argument that cannot be cleanly expressed as a
state-level invariant — instead, substrate.f bundles the position
preservation INTO the chain predicate itself as a per-step witness.

Ships in 3 sub-sections:
  - §F.1 inductive predicate `SavedKeyDoesntResolve fl₀ n_target s n s'`
        + boilerplate transports (degradation to FlowMonoChain, flow-level
        bounds, tokens monotonicity, single-step, transitivity)
  - §F.2 sufficient-condition step constructors:
        * `step_of_tokenIndex_ne` — when the step-start simpleKey does NOT
          have `tokenIndex = n_target` (folds into substrate.e's per-step
          preservation via the FlowNoOverwriteAt first clause)
        * `step_of_simpleKey_not_possible` — when the step-start simpleKey
          is not possible (degenerate case of `step_of_tokenIndex_ne`)
  - §F.3 chain wrapper `SavedKeyDoesntResolve_preserves_position_target` —
        induction on the predicate gives `s'.tokens[n_target + 1] =
        s.tokens[n_target + 1]`. The substrate.e wrapper handles `m ≤ N`;
        this wrapper handles `m = N + 1`. Together they cover the raw
        prefix `[0..N+2)` needed by `.tokenshape.list`.

**Closes zero legacy sorries**: pure enablement for `.body1.tokenshape.list`'s
position-`N + 1` half of the raw-prefix bridge. The establishing lemma
(witnessing the predicate by induction on the emitList input items) lives
in `.tokenshape.list` proper, where the EmitScansInFlow recursion is
unfolded. -/

/-! ### §F.1  `SavedKeyDoesntResolve` predicate + boilerplate transports -/

/-- `SavedKeyDoesntResolve fl₀ n_target s n s'`: a `FlowMonoChain fl₀ s n s'`
    augmented with a per-step witness that the token at position `n_target + 1`
    is preserved across every step. Where `FlowMonoChain` is the bare chain,
    `SavedKeyDoesntResolve` is the chain bundled with the position-`n_target + 1`
    preservation evidence — so the chain wrapper degenerates to plain induction.

    Used to preserve raw position `N + 1` (the slot a saved simpleKey would
    write into if `scanValuePrepare` fired on it) through chains that do not
    structurally invoke `:` on the simpleKey holding `tokenIndex = N`.

    Parallel to `FlowMonoChain` (substrate.e §E.6's input) but parameterized
    by a target position; the safety clause is carried by each step. -/
inductive SavedKeyDoesntResolve (fl₀ n_target : Nat) :
    ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} (h_fl : s.flowLevel ≥ fl₀) :
      SavedKeyDoesntResolve fl₀ n_target s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat}
      (h_fl : s.flowLevel ≥ fl₀)
      (h_snt : scanNextToken s = .ok (some s_mid))
      (h_preserved : ∀ (h : n_target + 1 < s.tokens.size),
        ∃ (h' : n_target + 1 < s_mid.tokens.size),
          s_mid.tokens[n_target + 1]'h' = s.tokens[n_target + 1]'h)
      (h_rest : SavedKeyDoesntResolve fl₀ n_target s_mid n s') :
      SavedKeyDoesntResolve fl₀ n_target s (n + 1) s'

/-- Degrade a `SavedKeyDoesntResolve` to a plain `FlowMonoChain`.
    Parallel to `FlowMonoChain.toScanChain`. -/
lemma SavedKeyDoesntResolve.toFlowMonoChain {fl₀ n_target : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : SavedKeyDoesntResolve fl₀ n_target s n s') : FlowMonoChain fl₀ s n s' := by
  induction h with
  | zero h_fl => exact .zero h_fl
  | step h_fl h_snt _h_pres _h_rest ih => exact .step h_fl h_snt ih

/-- Degrade to a plain `ScanChain` (through the FlowMonoChain). -/
lemma SavedKeyDoesntResolve.toScanChain {fl₀ n_target : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : SavedKeyDoesntResolve fl₀ n_target s n s') : ScanChain s n s' :=
  h.toFlowMonoChain.toScanChain

/-- The start state of a `SavedKeyDoesntResolve` has `flowLevel ≥ fl₀`. -/
lemma SavedKeyDoesntResolve.flowLevel_ge_start {fl₀ n_target : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : SavedKeyDoesntResolve fl₀ n_target s n s') : s.flowLevel ≥ fl₀ :=
  h.toFlowMonoChain.flowLevel_ge_start

/-- The end state of a `SavedKeyDoesntResolve` has `flowLevel ≥ fl₀`. -/
lemma SavedKeyDoesntResolve.flowLevel_ge_end {fl₀ n_target : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : SavedKeyDoesntResolve fl₀ n_target s n s') : s'.flowLevel ≥ fl₀ :=
  h.toFlowMonoChain.flowLevel_ge_end

/-- Token monotonicity for `SavedKeyDoesntResolve`: tokens only grow
    through the chain (delegates to FlowMonoChain version). -/
lemma SavedKeyDoesntResolve.tokens_mono {fl₀ n_target : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : SavedKeyDoesntResolve fl₀ n_target s n s') : s'.tokens.size ≥ s.tokens.size :=
  h.toFlowMonoChain.tokens_mono

/-- A single `scanNextToken` step as a `SavedKeyDoesntResolve`. -/
lemma SavedKeyDoesntResolve.single {fl₀ n_target : Nat} {s s' : ScannerState}
    (h_snt : scanNextToken s = .ok (some s'))
    (h_fl : s.flowLevel ≥ fl₀)
    (h_fl' : s'.flowLevel ≥ fl₀)
    (h_preserved : ∀ (h : n_target + 1 < s.tokens.size),
      ∃ (h' : n_target + 1 < s'.tokens.size),
        s'.tokens[n_target + 1]'h' = s.tokens[n_target + 1]'h) :
    SavedKeyDoesntResolve fl₀ n_target s 1 s' :=
  .step h_fl h_snt h_preserved (.zero h_fl')

/-- Transitivity: concatenate two `SavedKeyDoesntResolve`s with the same
    floor and target. -/
lemma SavedKeyDoesntResolve.trans {fl₀ n_target : Nat}
    {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : SavedKeyDoesntResolve fl₀ n_target s₁ n₁ s₂)
    (h2 : SavedKeyDoesntResolve fl₀ n_target s₂ n₂ s₃) :
    SavedKeyDoesntResolve fl₀ n_target s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_fl h_snt h_pres h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_fl h_snt h_pres h_ih

/-! ### §F.2  Sufficient-condition step constructors -/

/-- **Primary step constructor**: if the step-start simpleKey is either
    not possible OR has `tokenIndex ≠ n_target`, then the step preserves
    position `n_target + 1`. Proof folds substrate.e's per-step preservation
    `scanNextToken_preserves_position_specific_flow` under the
    `FlowNoOverwriteAt` first-clause specialization at `m = n_target + 1`.

    Sufficient (but not necessary) structural condition for establishing
    `SavedKeyDoesntResolve` step-by-step from input-shape reasoning. -/
lemma SavedKeyDoesntResolve.step_of_tokenIndex_ne
    {fl₀ n_target : Nat} {s s_mid s' : ScannerState} {n : Nat}
    (h_fl_pos : fl₀ ≥ 1)
    (h_fl : s.flowLevel ≥ fl₀)
    (h_snt : scanNextToken s = .ok (some s_mid))
    (h_not_target : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≠ n_target)
    (h_rest : SavedKeyDoesntResolve fl₀ n_target s_mid n s') :
    SavedKeyDoesntResolve fl₀ n_target s (n + 1) s' := by
  refine .step h_fl h_snt ?_ h_rest
  intro h_size
  have h_in_flow : s.inFlow = true := by
    unfold ScannerState.inFlow
    exact decide_eq_true (by omega)
  have h_clause : s.simpleKey.possible = true →
      n_target + 1 ≠ s.simpleKey.tokenIndex + 1 := by
    intro h_pos h_eq
    have h_tidx : s.simpleKey.tokenIndex = n_target := by omega
    exact h_not_target h_pos h_tidx
  have h_eq := scanNextToken_preserves_position_specific_flow s s_mid h_in_flow h_snt
    (n_target + 1) h_size h_clause
  have h_adds := ScannerCorrectness.scanNextToken_adds_tokens s s_mid h_snt
  have h_size_mid : n_target + 1 < s_mid.tokens.size := by omega
  exact ⟨h_size_mid, h_eq⟩

/-- Degenerate step constructor: if the step-start simpleKey is not
    possible, the step preserves position `n_target + 1`. Specialization
    of `step_of_tokenIndex_ne` where the `tokenIndex ≠ n_target`
    hypothesis is vacuous. -/
lemma SavedKeyDoesntResolve.step_of_simpleKey_not_possible
    {fl₀ n_target : Nat} {s s_mid s' : ScannerState} {n : Nat}
    (h_fl_pos : fl₀ ≥ 1)
    (h_fl : s.flowLevel ≥ fl₀)
    (h_snt : scanNextToken s = .ok (some s_mid))
    (h_sk : s.simpleKey.possible = false)
    (h_rest : SavedKeyDoesntResolve fl₀ n_target s_mid n s') :
    SavedKeyDoesntResolve fl₀ n_target s (n + 1) s' :=
  SavedKeyDoesntResolve.step_of_tokenIndex_ne h_fl_pos h_fl h_snt
    (fun h_pos => absurd (h_sk.symm.trans h_pos) Bool.false_ne_true) h_rest

/-! ### §F.3  Chain wrapper for position `n_target + 1` preservation -/

/-- **Chain wrapper**: a `SavedKeyDoesntResolve` chain preserves the token
    at position `n_target + 1`. Direct induction on the predicate (each
    step already carries its own preservation witness, transitively
    composed by induction).

    Parallel to `FlowMonoChain_preserves_position_specific_flow`
    (substrate.e §E.6) but for the residual position `n_target + 1` that
    falls outside `FlowNoOverwriteAt`'s expressivity. The two wrappers
    together (substrate.e for `m ≤ N`, substrate.f for `m = N + 1`) cover
    the full raw prefix `[0..N + 2)` needed by `.tokenshape.list`. -/
lemma SavedKeyDoesntResolve_preserves_position_target
    {fl₀ n_target : Nat} {s s' : ScannerState} {n : Nat}
    (h_skdr : SavedKeyDoesntResolve fl₀ n_target s n s')
    (h_m : n_target + 1 < s.tokens.size) :
    ∃ (h_size : n_target + 1 < s'.tokens.size),
      s'.tokens[n_target + 1]'h_size = s.tokens[n_target + 1]'h_m := by
  induction h_skdr with
  | zero => exact ⟨h_m, rfl⟩
  | @step s s_mid s' n h_fl h_snt h_pres h_rest ih =>
    obtain ⟨h_size_mid, h_eq_mid⟩ := h_pres h_m
    obtain ⟨h_size', h_eq'⟩ := ih h_size_mid
    exact ⟨h_size', h_eq'.trans h_eq_mid⟩

/-! ## Non-`:` dispatch position preservation (substrate.g)

A per-character preservation primitive that drops substrate.e's `simpleKey`
hypothesis entirely in favour of a structural fact about the dispatched
character: if the character `scanNextToken` dispatches is **not** `:`, then the
step preserves **every** position `m < s.tokens.size` unconditionally — no
flow hypothesis, no `simpleKey.tokenIndex + 1 ≠ m` side condition.

The reason is local to the dispatch tree: the *only* dispatcher branch that can
invoke `scanValuePrepare` (via `scanValue`) is the `:` branch of
`scanNextToken_dispatchBlockIndicators` (`Scanner.lean`, the
`c == ':' && isValueCandidate s` guard). Every other branch — structural,
flow-indicator, block-entry (`-`), key (`?`), and all content branches —
preserves the full token prefix unconditionally. So gating on `c ≠ ':'`
eliminates the one branch that could overwrite, leaving plain prefix
preservation everywhere.

Why this is needed despite substrate.e/f: substrate.e's flow-relaxed
`FlowNoOverwriteAt` still carries the `m ≠ simpleKey.tokenIndex + 1`
side-condition, and substrate.f's `SavedKeyDoesntResolve` only covers the single
residual position `n_target + 1`. Consumers that walk an emitList/emitPairList
body chain where the saved key genuinely never resolves (because the emitted
characters are `[`/`{`/`"`/`,`/… — never a value-`:` on the saved key) want
position preservation at *arbitrary* `m` without re-deriving a per-character
`simpleKey` bookkeeping argument. The non-`:` route delivers exactly that.

Ships in 4 sub-sections:
  - §G.1 dispatcher-level primitive
        `dispatchBlockIndicators_at_non_colon_preserves_positions`
        (the `:` branch is eliminated by `c ≠ ':'`)
  - §G.2 capstone `scanNextToken_at_non_colon_preserves_positions` — proof spine
        parallel to substrate.e's `scanNextToken_preserves_position_specific_flow`,
        substituting the per-char hypothesis for the simpleKey hypothesis at the
        `dispatchBlockIndicators` case
  - §G.3 bundled chain predicate `NoColonDispatchChain fl₀ s n s'` (a
        `FlowMonoChain` whose every step carries the non-`:`-dispatch witness)
        + boilerplate transports (paralleling substrate.f §F.1)
  - §G.4 chain wrapper `NoColonDispatchChain_preserves_position` — position
        preservation at **any** `m < s.tokens.size` across the chain. (The
        blueprint referred to this wrapper tentatively as
        `FlowMonoChain_preserves_position_when_no_colon_dispatch`; the as-built
        realization splits it into the bundled predicate above plus this
        induction wrapper.)

**Closes zero legacy sorries**: pure enablement for
`.body1.tokenshape.list.establishing`. -/

/-! ### §G.1  Dispatcher-level non-`:` primitive -/

/-- Non-`:` variant of `dispatchBlockIndicators_preserves_position_specific_flow`
    (substrate.e §E.5). With `c ≠ ':'` the value-`:` branch — the one path that
    invokes `scanValue`/`scanValuePrepare` — cannot fire, so the dispatcher
    preserves **every** position `m < s.tokens.size` with no `simpleKey`
    hypothesis and no flow hypothesis. The only token-mutating branches that
    remain are `scanBlockEntry` (`-`) and `scanKey` (`?`), both of which
    preserve the full token prefix. -/
lemma dispatchBlockIndicators_at_non_colon_preserves_positions (s : ScannerState)
    (c : Char) (s' : ScannerState)
    (h_not_colon : c ≠ ':')
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (m : Nat) (h_m : m < s.tokens.size) :
    s'.tokens[m]'(by
      have := ScannerCorrectness.ScanHelpers.dispatchBlockIndicators_tokens_mono s c s' h;
      omega) =
    s.tokens[m]'h_m := by
  have hcf : (c == ':') = false := by
    cases hcc : c == ':' with
    | false => rfl
    | true => exact absurd (eq_of_beq hcc) h_not_colon
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, pure, Pure.pure,
    Except.pure, hcf, Bool.false_and] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := ScannerCorrectness.ScanHelpers.scanBlockEntry_preserves_prefix s _
        (by assumption) m h_m; simp_all)
    | (have := ScannerCorrectness.ScanHelpers.scanKey_preserves_prefix s _
        (by assumption) m h_m; simp_all)
    | (simp_all)

/-! ### §G.2  `scanNextToken` capstone for non-`:` dispatch -/

set_option maxHeartbeats 400000 in
/-- Per-step pointwise preservation of **every** position `m` through
    `scanNextToken`, given that the dispatched character (the one
    `scanNextToken_preprocess` peeks) is not `:`. Proof spine parallel to
    `scanNextToken_preserves_position_specific_flow` (substrate.e §E.5), with the
    per-character `c ≠ ':'` hypothesis replacing the `simpleKey` side condition
    at the `dispatchBlockIndicators` case — every other dispatcher already
    preserves the prefix unconditionally. No flow hypothesis is required. -/
lemma scanNextToken_at_non_colon_preserves_positions (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (h_not_colon : ∀ s1 c1, scanNextToken_preprocess s = .ok (some (s1, c1)) → c1 ≠ ':')
    (m : Nat) (h_m : m < s.tokens.size) :
    s'.tokens[m]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[m]'h_m := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · rename_i s1 c1 hPre
      have h_pre_pref := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s s1 c1
        hPre m (by omega)
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s s1 c1 hPre
      have h_c1 : c1 ≠ ':' := h_not_colon s1 c1 hPre
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix _ _ _
            (by assumption) m (by omega);
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchFlowIndicators_preserves_prefix _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := dispatchBlockIndicators_at_non_colon_preserves_positions _ _ _
            h_c1
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix _ _ _
            (by assumption) m
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (simp_all)

/-! ### §G.3  `NoColonDispatchChain` predicate + boilerplate transports -/

/-- `NoColonDispatchChain fl₀ s n s'`: a `FlowMonoChain fl₀ s n s'` augmented
    with a per-step witness that the dispatched character is not `:`. Where
    `FlowMonoChain` is the bare chain, `NoColonDispatchChain` is the chain
    bundled with the evidence that no step resolves a value-`:` — so the chain
    wrapper degenerates to plain induction applying the §G.2 capstone at each
    step for arbitrary `m`.

    Parallel to `SavedKeyDoesntResolve` (substrate.f §F.1), but the per-step
    witness is the structural non-`:` fact rather than a position-specific
    preservation proof; this makes the wrapper conclude for *every* `m` rather
    than a single target position. -/
inductive NoColonDispatchChain (fl₀ : Nat) :
    ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} (h_fl : s.flowLevel ≥ fl₀) :
      NoColonDispatchChain fl₀ s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat}
      (h_fl : s.flowLevel ≥ fl₀)
      (h_snt : scanNextToken s = .ok (some s_mid))
      (h_no_colon : ∀ t c, scanNextToken_preprocess s = .ok (some (t, c)) → c ≠ ':')
      (h_rest : NoColonDispatchChain fl₀ s_mid n s') :
      NoColonDispatchChain fl₀ s (n + 1) s'

/-- Degrade a `NoColonDispatchChain` to a plain `FlowMonoChain`. -/
lemma NoColonDispatchChain.toFlowMonoChain {fl₀ : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : NoColonDispatchChain fl₀ s n s') : FlowMonoChain fl₀ s n s' := by
  induction h with
  | zero h_fl => exact .zero h_fl
  | step h_fl h_snt _h_nc _h_rest ih => exact .step h_fl h_snt ih

/-- Degrade to a plain `ScanChain` (through the FlowMonoChain). -/
lemma NoColonDispatchChain.toScanChain {fl₀ : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : NoColonDispatchChain fl₀ s n s') : ScanChain s n s' :=
  h.toFlowMonoChain.toScanChain

/-- The start state of a `NoColonDispatchChain` has `flowLevel ≥ fl₀`. -/
lemma NoColonDispatchChain.flowLevel_ge_start {fl₀ : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : NoColonDispatchChain fl₀ s n s') : s.flowLevel ≥ fl₀ :=
  h.toFlowMonoChain.flowLevel_ge_start

/-- The end state of a `NoColonDispatchChain` has `flowLevel ≥ fl₀`. -/
lemma NoColonDispatchChain.flowLevel_ge_end {fl₀ : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : NoColonDispatchChain fl₀ s n s') : s'.flowLevel ≥ fl₀ :=
  h.toFlowMonoChain.flowLevel_ge_end

/-- Token monotonicity for `NoColonDispatchChain` (delegates to FlowMonoChain). -/
lemma NoColonDispatchChain.tokens_mono {fl₀ : Nat}
    {s s' : ScannerState} {n : Nat}
    (h : NoColonDispatchChain fl₀ s n s') : s'.tokens.size ≥ s.tokens.size :=
  h.toFlowMonoChain.tokens_mono

/-- A single non-`:`-dispatch `scanNextToken` step as a `NoColonDispatchChain`. -/
lemma NoColonDispatchChain.single {fl₀ : Nat} {s s' : ScannerState}
    (h_snt : scanNextToken s = .ok (some s'))
    (h_fl : s.flowLevel ≥ fl₀)
    (h_fl' : s'.flowLevel ≥ fl₀)
    (h_no_colon : ∀ t c, scanNextToken_preprocess s = .ok (some (t, c)) → c ≠ ':') :
    NoColonDispatchChain fl₀ s 1 s' :=
  .step h_fl h_snt h_no_colon (.zero h_fl')

/-- Transitivity: concatenate two `NoColonDispatchChain`s with the same floor. -/
lemma NoColonDispatchChain.trans {fl₀ : Nat}
    {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : NoColonDispatchChain fl₀ s₁ n₁ s₂)
    (h2 : NoColonDispatchChain fl₀ s₂ n₂ s₃) :
    NoColonDispatchChain fl₀ s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_fl h_snt h_nc h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_fl h_snt h_nc h_ih


end L4YAML.Proofs.EmitterScannability
