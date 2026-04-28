/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Scanner.Scanner
import L4YAML.Spec.Grammar
import L4YAML.Proofs.Scanner.ScannerProofs
import L4YAML.Proofs.Scanner.ScannerProgress

/-!
# Scanner Correctness (P10.11a)

Proves that the scanner's `scan` function produces token streams that satisfy
the `ValidTokenStream` specification from Grammar.lean.

## Main Result

```lean
theorem scan_produces_valid_tokens :
  ∀ input tokens, Scanner.scan input = .ok tokens → Grammar.ValidTokenStream input tokens
```

This establishes the first bridge between the grammar specification and the
implementation: the scanner's output satisfies the token stream contract that
the parser relies on.

## Structure

### §1  Token Envelope Properties
- `scan_produces_streamStart` — first token is always streamStart
- `scan_produces_streamEnd` — last token is always streamEnd
- `scan_produces_at_least_two` — at least 2 tokens (envelope invariant)

### §2  Position Monotonicity
- `emit_preserves_position_order` — appending tokens preserves ordering
- `advance_increases_offset` — scanner progress is monotonic
- `scan_positions_ordered` — final token array has monotonic positions

### §3  Main Correctness Theorem
- `scan_produces_valid_tokens` — composition of §1 and §2

## Status

Proven (no sorry, no axioms):
- `scanKey_adds_one_token` — scanKey adds at least one token
- `emit_preserves_position_order` — appending tokens preserves ordering
- `scanLoop_increases_tokens` — loop increases token count by at least 1
- `scan_produces_at_least_two` — scan output has at least 2 tokens
- `scanNextToken_preserves_ScanInv` — scanNextToken preserves compound invariant
- `scanNextToken_preserves_AllKeysValid` — scanNextToken preserves simple-key validity
- Helper lemmas: `advance_preserves_tokens`, `advance_preserves_flowLevel`,
  `emit_tokens_size`, `emit_preserves_tokens_at`, `pushMappingIndent_tokens_monotonic`,
  `pushSequenceIndent_tokens_monotonic`, `emitAt_tokens_size`,
  `scanFlowEntry_adds_one_token`, `scanBlockEntry_adds_tokens`,
  `collectAnchorNameLoop_preserves_tokens`, all skipToContent* lemmas,
  `scanValue_adds_tokens` (via scanValue decomposition into 4 helpers)

Position monotonicity infrastructure:
- `ScanInv` / `ScanInv'` — compound invariant (ordered ∧ bounded)
- `emit_preserves_ScanInv` — delegates to `emit_preserves_position_order`
- `advance_preserves_ScanInv` — offset increases, tokens unchanged
- `field_update_preserves_ScanInv` — field updates preserve invariant
- `unwindIndentsLoop_preserves_ScanInv` — loop preserves invariant
- `unwindIndents_preserves_ScanInv` — wrapper
- `scanLoop_ordered` — induction on fuel
- `scan_positions_ordered` — top-level theorem (0 sorry)
-/

namespace L4YAML.Proofs.ScannerCorrectness

open L4YAML
open L4YAML.Scanner
open L4YAML.CharPredicates
open L4YAML.Grammar
open L4YAML.Proofs.ScannerProgress
open L4YAML.Proofs.ScannerProofs

/-- Simple key invariant: all simple keys (current and stacked) have
    `tokenIndex ≥ n`. This is threaded through `scanLoop` to ensure that
    `scanValuePrepare`'s `setIfInBounds` never overwrites tokens below `n`. -/
def SimpleKeyAbove (s : ScannerState) (n : Nat) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
  (∀ j, (h : j < s.simpleKeyStack.size) →
    s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ n)

/-! ## §0  Helper Lemmas for scanLoop

These lemmas characterize the behavior of `scanLoop`, which is the structurally
recursive helper function used by `scan`. They enable proving properties about
`scan` via induction on the fuel parameter.
-/

/-- The `advance` operation preserves the token array.

`advance` only modifies position fields (offset, line, col), never the tokens. -/
theorem advance_preserves_tokens (s : ScannerState) :
    s.advance.tokens = s.tokens := by
  unfold ScannerState.advance
  split
  · -- Case: s.offset < s.inputEnd
    -- Simplify the let bindings and structure updates
    simp only []
    -- The tokens field appears unchanged in all three branches
    split
    · rfl
    · split <;> rfl
  · -- Case: s.offset >= s.inputEnd
    rfl

/-- The `advance` operation preserves flowLevel.

`advance` only modifies position fields, not flow state. -/
theorem advance_preserves_flowLevel (s : ScannerState) :
    s.advance.flowLevel = s.flowLevel := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

/-- The `advance` operation preserves flowStack.

`advance` only modifies position fields, not flow state. -/
theorem advance_preserves_flowStack (s : ScannerState) :
    s.advance.flowStack = s.flowStack := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

/-- The `emit` operation preserves flowLevel.

`emit` only adds to tokens array, doesn't modify flow state. -/
theorem emit_preserves_flowLevel (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).flowLevel = s.flowLevel := by
  unfold ScannerState.emit
  rfl

/-- The `emit` operation preserves flowStack.

`emit` only adds to tokens array, doesn't modify flow state. -/
theorem emit_preserves_flowStack (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).flowStack = s.flowStack := by
  unfold ScannerState.emit
  rfl

/-- The `emit` operation preserves existing tokens.

For any index i < original size, tokens[i] remains unchanged. -/
theorem emit_preserves_tokens_at (s : ScannerState) (tok : YamlToken)
    (i : Nat) (h : i < s.tokens.size) :
    (s.emit tok).tokens[i]'(by have := emit_tokens_size s tok; omega) = s.tokens[i] := by
  unfold ScannerState.emit
  simp only [Array.getElem_push]
  split
  · rfl
  · -- This branch is when i = s.tokens.size, but h says i < s.tokens.size
    omega

/-- Helper lemma: unwindIndentsLoop only appends tokens (never removes).

This is proven by induction on fuel. Each iteration either returns the state unchanged
or emits a blockEnd token (which adds exactly one token). -/
theorem unwindIndentsLoop_tokens_monotonic (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).tokens.size ≥ s.tokens.size := by
  induction fuel generalizing s with
  | zero =>
    -- Base case: fuel = 0, returns s unchanged
    unfold unwindIndentsLoop
    exact Nat.le_refl _
  | succ fuel' ih =>
    -- Inductive case: fuel = fuel' + 1
    unfold unwindIndentsLoop
    split
    · -- Condition true: emit blockEnd and recurse
      -- After emit: size increases by 1
      have h_emit := emit_tokens_size s .blockEnd
      -- After modifying indents, tokens stay same (only indents field changed)
      let s' := s.emit .blockEnd
      let s'' := { s' with indents := s'.indents.pop }
      -- s''.tokens = s'.tokens (modifying indents doesn't affect tokens)
      have h_tokens_eq : s''.tokens = s'.tokens := by rfl
      -- Apply IH to s''
      have h_ih : (unwindIndentsLoop s'' col fuel').tokens.size ≥ s''.tokens.size := ih s''
      -- Combine: result.size ≥ s''.tokens.size = s'.tokens.size = s.tokens.size + 1 ≥ s.tokens.size
      rw [h_tokens_eq] at h_ih
      rw [h_emit] at h_ih
      exact Nat.le_trans (Nat.le_succ s.tokens.size) h_ih
    · -- Condition false: return s
      exact Nat.le_refl _

/-- Helper lemma: unwindIndentsLoop preserves the prefix of tokens.

For any index i < original size, tokens[i] remains unchanged. -/
theorem unwindIndentsLoop_preserves_prefix (s : ScannerState) (col : Int) (fuel : Nat)
    (i : Nat) (h_bound : i < s.tokens.size) :
    (unwindIndentsLoop s col fuel).tokens[i]'
      (by have := unwindIndentsLoop_tokens_monotonic s col fuel; omega) =
    s.tokens[i] := by
  induction fuel generalizing s with
  | zero =>
    -- Base case: fuel = 0, returns s unchanged
    unfold unwindIndentsLoop
    rfl
  | succ fuel' ih =>
    -- Inductive case
    unfold unwindIndentsLoop
    split
    · -- Condition true: emit and recurse
      let s_emit := s.emit .blockEnd
      let s_pop := { s_emit with indents := s_emit.indents.pop }
      -- We know emit increases size by 1
      have h_emit_size : s_emit.tokens.size = s.tokens.size + 1 := emit_tokens_size s .blockEnd
      -- So i < s_emit.tokens.size
      have h_i_lt_emit : i < s_emit.tokens.size := by
        rw [h_emit_size]
        omega
      -- Use emit_preserves_tokens_at instead of unfolding
      have h_emit_preserves : s_emit.tokens[i]'h_i_lt_emit = s.tokens[i] := emit_preserves_tokens_at s .blockEnd i h_bound
      -- After modifying indents field, tokens unchanged
      have h_tokens_same : s_pop.tokens = s_emit.tokens := by rfl
      -- Apply IH to s_pop
      have h_new_size : i < s_pop.tokens.size := by
        rw [h_tokens_same, h_emit_size]
        omega
      have h_ih : (unwindIndentsLoop s_pop col fuel').tokens[i]'_ = s_pop.tokens[i]'h_new_size := ih s_pop h_new_size
      -- Now combine: result[i] = s_pop[i] = s_emit[i] = s[i]
      -- s_pop.tokens[i] = s_emit.tokens[i] because tokens are the same
      have h_pop_eq_emit : s_pop.tokens[i]'h_new_size = s_emit.tokens[i]'h_i_lt_emit := by
        have : s_pop.tokens = s_emit.tokens := h_tokens_same
        cases this
        rfl
      rw [h_ih, h_pop_eq_emit, h_emit_preserves]
    · -- Condition false: return s unchanged
      rfl

/-- The `unwindIndents` operation preserves or adds tokens.

When unwinding indents, we only emit `blockEnd` tokens, never removing any.
So the token count increases or stays the same. -/
theorem unwindIndents_adds_tokens (s : ScannerState) (col : Int) :
    (unwindIndents s col).tokens.size ≥ s.tokens.size := by
  unfold unwindIndents
  exact unwindIndentsLoop_tokens_monotonic s col s.indents.size

/-- unwindIndents preserves the prefix of tokens. -/
theorem unwindIndents_preserves_prefix (s : ScannerState) (col : Int)
    (i : Nat) (h_bound : i < s.tokens.size) :
    (unwindIndents s col).tokens[i]'
      (by have := unwindIndents_adds_tokens s col; omega) =
    s.tokens[i] := by
  unfold unwindIndents
  exact unwindIndentsLoop_preserves_prefix s col s.indents.size i h_bound

/-- `unwindIndentsLoop` preserves `flowLevel` through all iterations.
    Each step does `emit .blockEnd` (preserves flowLevel) + record update
    on `indents` only (preserves flowLevel). -/
theorem unwindIndentsLoop_preserves_flowLevel (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).flowLevel = s.flowLevel := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; exact emit_preserves_flowLevel s .blockEnd
    · rfl

/-- `unwindIndents` preserves `flowLevel`. -/
theorem unwindIndents_preserves_flowLevel (s : ScannerState) (col : Int) :
    (unwindIndents s col).flowLevel = s.flowLevel := by
  unfold unwindIndents
  exact unwindIndentsLoop_preserves_flowLevel s col s.indents.size

/-- `saveSimpleKey` preserves `flowLevel`. -/
theorem saveSimpleKey_preserves_flowLevel (s : ScannerState) :
    (saveSimpleKey s).flowLevel = s.flowLevel := by
  unfold saveSimpleKey
  split <;> (try rfl)
  split <;> rfl

/-- `scanFlowEntry` preserves `flowLevel` on success. -/
theorem scanFlowEntry_preserves_flowLevel (s s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h <;> (try contradiction)
    injection h with h_eq; subst h_eq
    simp [emit_preserves_flowLevel, advance_preserves_flowLevel]
  · injection h with h_eq; subst h_eq
    simp [emit_preserves_flowLevel, advance_preserves_flowLevel]

theorem advanceNLoop_preserves_flowLevel (s : ScannerState) (n : Nat) :
    (ScannerState.advanceNLoop s n).flowLevel = s.flowLevel := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ n' ih =>
    unfold ScannerState.advanceNLoop
    rw [ih]; exact advance_preserves_flowLevel s

theorem advanceN_preserves_flowLevel (s : ScannerState) (n : Nat) :
    (s.advanceN n).flowLevel = s.flowLevel := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_flowLevel s n

/-- scanLoop only succeeds by emitting streamEnd (generalized over all states).

When `scanLoop s fuel` returns `.ok tokens`, those tokens came from a code path
that includes `final.emit .streamEnd`. This means `tokens.size = final.tokens.size + 1`
where `final = unwindIndents s (-1)`. -/
theorem scanLoop_success_emits_streamEnd : ∀ (s : ScannerState) (fuel : Nat) (tokens : Array (Positioned YamlToken)),
    scanLoop s fuel = .ok tokens →
    ∃ (s' : ScannerState), tokens = (s'.emit .streamEnd).tokens := by
  intro s fuel
  induction fuel generalizing s with
  | zero =>
    -- Case fuel = 0: scanLoop returns .error, contradiction
    intro tokens h
    unfold scanLoop at h
    contradiction
  | succ fuel' IH =>
    -- Case fuel = fuel' + 1
    intro tokens h
    unfold scanLoop at h
    -- Case split on scanNextToken result
    split at h
    · -- scanNextToken = .error e: scanLoop returns .error, contradiction
      contradiction
    · -- scanNextToken = .ok none: success path
      -- Need to handle the if-then-else for flowLevel and directivesPresent
      split at h <;> try contradiction
      split at h <;> try contradiction
      -- Now h : .ok ((unwindIndents s (-1)).emit .streamEnd).tokens = .ok tokens
      injection h with h_eq
      exists (unwindIndents s (-1))
      exact h_eq.symm
    · -- scanNextToken = .ok (some s'): recursive call to scanLoop s' fuel'
      -- Apply IH with the new state s'
      rename_i s' _
      exact IH s' tokens h

/-- saveSimpleKey preserves tokens.

saveSimpleKey only modifies the simpleKey field. -/
theorem advanceNLoop_preserves_tokens (s : ScannerState) (n : Nat) :
    (ScannerState.advanceNLoop s n).tokens = s.tokens := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ n' ih =>
    unfold ScannerState.advanceNLoop
    rw [ih]
    exact advance_preserves_tokens s

theorem advanceN_preserves_tokens (s : ScannerState) (n : Nat) :
    (s.advanceN n).tokens = s.tokens := by
  unfold ScannerState.advanceN
  exact advanceNLoop_preserves_tokens s n

/-- saveSimpleKey preserves the token array (post-cutover identity on `.tokens`).

**Initiative 3 / J.2 step 5 cutover**: pre-cutover this lemma stated
size ≥ s.tokens.size; post-cutover saveSimpleKey only touches
`pendingKeys`/`pendingKeyActive`/`simpleKey`, never `tokens`, so the
sharper equality holds by `rfl` after unfolding. -/
theorem saveSimpleKey_tokens_monotonic (s : ScannerState) :
    (saveSimpleKey s).tokens.size ≥ s.tokens.size := by
  unfold saveSimpleKey
  split
  · exact Nat.le_refl _
  · split <;> exact Nat.le_refl _

/-- saveSimpleKey preserves existing token prefix (in fact the whole array).

**Initiative 3 / J.2 step 5 cutover**: post-cutover saveSimpleKey is
identity on `.tokens`, so this reduces to `rfl` after unfolding. -/
theorem saveSimpleKey_preserves_prefix (s : ScannerState)
    (i : Nat) (h_bound : i < s.tokens.size) :
    have h : i < (saveSimpleKey s).tokens.size :=
      Nat.lt_of_lt_of_le h_bound (saveSimpleKey_tokens_monotonic s)
    (saveSimpleKey s).tokens[i] = s.tokens[i] := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl

/-- scanFlowSequenceStart adds exactly one token.

After refactoring with explicit variable names (s_key_disabled, s_with_token,
s_after_advance), the token flow is clear:
- s_key_disabled.tokens = s.tokens (field update doesn't touch tokens)
- s_with_token.tokens = s.tokens.push token (emit adds one)
- s_after_advance.tokens = s_with_token.tokens (advance preserves)
- final result.tokens = s_after_advance.tokens (field update doesn't touch tokens)

Therefore: result.tokens.size = s.tokens.size + 1 -/
theorem scanFlowSequenceStart_adds_one_token (s : ScannerState) :
    (scanFlowSequenceStart s).tokens.size = s.tokens.size + 1 := by
  unfold scanFlowSequenceStart ScannerState.emit
  simp only [advance_preserves_tokens, Array.size_push]

/-- scanFlowSequenceEnd adds exactly one token.

Same refactoring as scanFlowSequenceStart: emit → advance → structure update.
Only emit modifies tokens (adds 1). -/
theorem scanFlowSequenceEnd_adds_one_token (s : ScannerState) :
    (scanFlowSequenceEnd s).tokens.size = s.tokens.size + 1 := by
  unfold scanFlowSequenceEnd ScannerState.emit
  simp only [advance_preserves_tokens, Array.size_push]

/-- scanFlowMappingStart adds exactly one token. -/
theorem scanFlowMappingStart_adds_one_token (s : ScannerState) :
    (scanFlowMappingStart s).tokens.size = s.tokens.size + 1 := by
  unfold scanFlowMappingStart ScannerState.emit
  simp only [advance_preserves_tokens, Array.size_push]

/-- scanFlowMappingEnd adds exactly one token. -/
theorem scanFlowMappingEnd_adds_one_token (s : ScannerState) :
    (scanFlowMappingEnd s).tokens.size = s.tokens.size + 1 := by
  unfold scanFlowMappingEnd ScannerState.emit
  simp only [advance_preserves_tokens, Array.size_push]

/-- `pushMappingIndent` preserves or adds tokens.

When the current column is deeper than `currentIndent`, emits `blockMappingStart`
(+1 token). Otherwise, the state is unchanged. -/
theorem pushMappingIndent_tokens_monotonic (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).tokens.size ≥ s.tokens.size := by
  unfold pushMappingIndent
  split
  · simp [ScannerState.emit, Array.size_push]
  · omega

/-- `pushSequenceIndent` preserves or adds tokens. -/
theorem pushSequenceIndent_tokens_monotonic (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).tokens.size ≥ s.tokens.size := by
  unfold pushSequenceIndent
  split
  · simp [ScannerState.emit, Array.size_push]
  · omega

/-- `emitAt` adds exactly one token (like `emit` but at a saved position). -/
theorem emitAt_tokens_size (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).tokens.size = s.tokens.size + 1 := by
  unfold ScannerState.emitAt; simp [Array.size_push]

/-- scanKey adds at least one token (on success).

scanKey: conditional pushMappingIndent (≥0) → emit .key (+1) → advance (0).
Total: ≥ s.tokens.size + 1. -/
theorem scanKey_adds_one_token (s : ScannerState) (s' : ScannerState)
    (h : scanKey s = .ok s') :
    s'.tokens.size ≥ s.tokens.size + 1 := by
  unfold scanKey at h
  simp only [] at h
  split at h
  · -- !inFlow → pushMappingIndent called
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq
        simp only [advance_preserves_tokens, emit_tokens_size]
        have := pushMappingIndent_tokens_monotonic s s.col; omega
    · injection h with h_eq; subst h_eq
      simp only [advance_preserves_tokens, emit_tokens_size]
      have := pushMappingIndent_tokens_monotonic s s.col; omega
  · -- inFlow → no pushMappingIndent
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq
        simp only [advance_preserves_tokens, emit_tokens_size]; omega
    · injection h with h_eq; subst h_eq
      simp only [advance_preserves_tokens, emit_tokens_size]; omega

/-- scanValueClearKey preserves the token array.

`scanValueClearKey` only modifies `simpleKey` (or returns `s` unchanged),
so the token array is identical. -/
theorem scanValueClearKey_preserves_tokens (s : ScannerState) :
    (scanValueClearKey s).tokens = s.tokens := by
  unfold scanValueClearKey; split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- `scanValueClearKey` either returns `s` unchanged or clears `simpleKey.possible`.
    Used to transfer `SimpleKeyValid` through `scanValueClearKey`. -/
theorem scanValueClearKey_identity_or_clear (s : ScannerState) :
    (scanValueClearKey s = s) ∨
    ((scanValueClearKey s).simpleKey.possible = false ∧
     (scanValueClearKey s).tokens = s.tokens) := by
  unfold scanValueClearKey
  split
  · split
    · right; exact ⟨rfl, rfl⟩
    · split
      · right; exact ⟨rfl, rfl⟩
      · left; rfl
  · left; rfl

/-- scanValuePrepare preserves or adds tokens.

Each branch of `scanValuePrepare` either:
- overwrites placeholder slots via `setIfInBounds` (preserving token count),
- calls `pushMappingIndent` (monotonic), or
- returns an updated state with unchanged tokens. -/
theorem scanValuePrepare_tokens_monotonic (s : ScannerState) :
    (scanValuePrepare s).tokens.size ≥ s.tokens.size := by
  unfold scanValuePrepare
  split
  · -- simpleKey.possible = true
    split
    · -- !inFlow
      split
      · -- keyCol > currentIndent: two setIfInBounds
        dsimp only []
        simp
      · -- keyCol ≤ currentIndent: one setIfInBounds
        dsimp only []
        simp
    · -- inFlow: one setIfInBounds
      dsimp only []
      simp
  · -- simpleKey.possible = false
    split
    · -- explicitKeyLine.isSome: only simpleKey field changes
      dsimp only []; omega
    · -- else
      split
      · -- !inFlow: pushMappingIndent
        exact pushMappingIndent_tokens_monotonic s s.col
      · -- inFlow: identity
        omega

/-- scanValue adds at least one token (on success).

scanValue is decomposed into four helpers:
  `scanValueClearKey` (preserves tokens) →
  `scanValueValidate` (error or ok ()) →
  `scanValuePrepare` (tokens monotonic) →
  `emit .value` (+1 token) →
  `advance` (preserves tokens) →
  `scanValueTabCheck` (error or ok ())

The `Except.bind` chain is exposed via `simp only [bind, Except.bind]`,
then each branch is handled by `split at h` / `contradiction` / `omega`. -/
theorem scanValue_adds_tokens (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') :
    s'.tokens.size ≥ s.tokens.size + 1 := by
  unfold scanValue at h
  dsimp only [] at h
  -- Unfold both Bind.bind calls (validate + tabCheck) to expose matches
  simp only [bind, Except.bind] at h
  -- Split on outer match (scanValueValidate): .error first, .ok second
  split at h
  · -- scanValueValidate = .error → contradiction
    contradiction
  · -- scanValueValidate = .ok ()
    -- Split on inner match (scanValueTabCheck): .error first, .ok second
    split at h
    · -- scanValueTabCheck = .error → contradiction
      contradiction
    · -- scanValueTabCheck = .ok () → h : .ok {...} = .ok s'
      injection h with h_eq; subst h_eq
      -- Reduce struct projection through { ... with simpleKeyAllowed := ... }
      dsimp only []
      rw [advance_preserves_tokens, emit_tokens_size]
      have h_ck := scanValueClearKey_preserves_tokens s
      have h_prep := scanValuePrepare_tokens_monotonic (scanValueClearKey s)
      rw [h_ck] at h_prep; omega

/-- Helper: consumeNewline preserves tokens.

consumeNewline only calls advance and modifies needIndentCheck field. -/
theorem consumeNewline_preserves_tokens (s : ScannerState) :
    (consumeNewline s).tokens = s.tokens := by
  unfold consumeNewline
  split
  · -- some '\n' => { s.advance with needIndentCheck := true }
    exact advance_preserves_tokens s
  · -- some '\r' => ...
    dsimp only []
    split
    · -- CRLF: raw offset skip preserves tokens
      exact advance_preserves_tokens s
    · -- _ => { s.advance with needIndentCheck := true }
      exact advance_preserves_tokens s
  · -- _ => s
    rfl

/-- Helper: skipSpaces preserves tokens.

skipSpaces now uses structural recursion via skipSpacesLoop (Scanner.lean:368-377).
Proof by induction on fuel with advance_preserves_tokens. -/
theorem skipSpaces_preserves_tokens (s : ScannerState) :
    (skipSpaces s).tokens = s.tokens := by
  unfold skipSpaces
  generalize h_fuel : s.inputEnd - s.offset = fuel
  clear h_fuel
  induction fuel generalizing s with
  | zero =>
    unfold skipSpacesLoop
    rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop
    split
    · -- some ' ' => recurse
      have ih_adv := IH s.advance
      rw [ih_adv, advance_preserves_tokens]
    · -- other character or none => stop
      rfl

/-- Helper: skipWhitespace preserves tokens.

skipWhitespace now uses structural recursion via skipWhitespaceLoop (Scanner.lean:350-359). -/
theorem skipWhitespace_preserves_tokens (s : ScannerState) :
    (skipWhitespace s).tokens = s.tokens := by
  unfold skipWhitespace
  generalize h_fuel : s.inputEnd - s.offset = fuel
  clear h_fuel
  induction fuel generalizing s with
  | zero =>
    unfold skipWhitespaceLoop
    rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop
    split
    · -- some c
      split
      · -- isWhiteSpace c = true => recurse
        have ih_adv := IH s.advance
        rw [ih_adv, advance_preserves_tokens]
      · -- isWhiteSpace c = false => stop
        rfl
    · -- none => stop
      rfl

/-- Helper: skipToEndOfLine preserves tokens.

skipToEndOfLine now uses structural recursion via skipToEndOfLineLoop (Scanner.lean:386-395). -/
theorem skipToEndOfLine_preserves_tokens (s : ScannerState) :
    (skipToEndOfLine s).tokens = s.tokens := by
  unfold skipToEndOfLine
  generalize h_fuel : s.inputEnd - s.offset = fuel
  clear h_fuel
  induction fuel generalizing s with
  | zero =>
    unfold skipToEndOfLineLoop
    rfl
  | succ fuel' IH =>
    unfold skipToEndOfLineLoop
    split
    · -- some c
      split
      · -- isLineBreak c = true => stop
        rfl
      · -- isLineBreak c = false => recurse
        have ih_adv := IH s.advance
        rw [ih_adv, advance_preserves_tokens]
    · -- none => stop
      rfl

/-- Helper: collectCommentTextLoop preserves tokens.

    `collectCommentTextLoop` only calls `s.advance` which preserves tokens. -/
theorem collectCommentTextLoop_preserves_tokens (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.tokens = s.tokens := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_tokens]
    · rfl

/-- Helper: skipToContentWs preserves tokens.

`skipToContentWs` only calls `skipSpaces` and `skipWhitespace` (both proven
to preserve tokens), plus field updates and error throws. No `emit` calls. -/
theorem skipToContentWs_preserves_tokens (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.tokens = s.tokens := by
  unfold skipToContentWs at h
  split at h
  · -- needIndentCheck = true
    simp only [] at h  -- reduce `have s1 := skipSpaces s`
    split at h
    · -- col ≤ currentIndent
      split at h
      · -- peek? = some '\t'
        split at h
        · -- probe.peek? = some '#'
          simp at h; rw [← h, skipWhitespace_preserves_tokens, skipSpaces_preserves_tokens]
        · -- probe.peek? = some c (not '#')
          split at h
          · simp at h; rw [← h, skipWhitespace_preserves_tokens, skipSpaces_preserves_tokens]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_tokens, skipSpaces_preserves_tokens]
            · simp at h
        · -- probe.peek? = none
          simp at h; rw [← h, skipWhitespace_preserves_tokens, skipSpaces_preserves_tokens]
      · -- peek? ≠ some '\t'
        simp at h; rw [← h, skipSpaces_preserves_tokens]
    · -- col > currentIndent
      simp at h; rw [← h, skipWhitespace_preserves_tokens, skipSpaces_preserves_tokens]
  · -- needIndentCheck = false
    simp at h; rw [← h, skipWhitespace_preserves_tokens]

/-- Helper: skipToContentComment preserves tokens.

`skipToContentComment` collects comment text into the `comments` side-channel
via `collectCommentTextLoop`, which only calls `advance` and field updates.
No `emit` calls — the `tokens` array is unchanged. -/
theorem skipToContentComment_preserves_tokens (s : ScannerState) :
    (skipToContentComment s).tokens = s.tokens := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []  -- reduce `let commentOk := ...`
    split  -- splits on peekBack?
    · -- peekBack? = some c
      split  -- splits on the if condition
      · -- commentOk = true
        simp only []  -- reduce let bindings
        rw [collectCommentTextLoop_preserves_tokens, advance_preserves_tokens]
      · rfl
    · -- peekBack? = none: commentOk = s.col == 0 || true
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_tokens, advance_preserves_tokens]
      · rfl
  · -- peek? ≠ some '#'
    rfl

/-- `skipToContentLoop` preserves tokens.

By induction on fuel. Each iteration:
1. `skipToContentWs` preserves tokens (or errors out)
2. `skipToContentComment` preserves tokens
3. If line break: `consumeNewline` preserves tokens, `{ .. with simpleKeyAllowed }` preserves tokens, then recurse
4. Otherwise: return — tokens unchanged

The refactoring from `do`+`mut` to explicit state threading (`skipToContentWs`,
`skipToContentComment`) makes each step visible to `unfold`+`split`. -/
theorem skipToContentLoop_preserves_tokens (s : ScannerState) (s' : ScannerState)
    (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.tokens = s.tokens := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    split at h
    · -- skipToContentWs s = .error e → contradiction
      simp at h
    · -- skipToContentWs s = .ok s1
      rename_i s1 hws
      simp only [] at h  -- reduce `let s2 := skipToContentComment s1`
      split at h
      · -- (skipToContentComment s1).peek? = some c
        rename_i c hpeek
        split at h
        · -- isLineBreak c = true
          split at h
          · -- !isInFlowSequence → recurse with simpleKeyAllowed := true
            have ih := IH _ h
            rw [ih, consumeNewline_preserves_tokens, skipToContentComment_preserves_tokens]
            exact skipToContentWs_preserves_tokens s s1 hws
          · -- isInFlowSequence → recurse without flag change
            have ih := IH _ h
            rw [ih, consumeNewline_preserves_tokens, skipToContentComment_preserves_tokens]
            exact skipToContentWs_preserves_tokens s s1 hws
        · -- isLineBreak c = false → .ok (skipToContentComment s1)
          simp at h; rw [← h, skipToContentComment_preserves_tokens]
          exact skipToContentWs_preserves_tokens s s1 hws
      · -- (skipToContentComment s1).peek? = none
        simp at h; rw [← h, skipToContentComment_preserves_tokens]
        exact skipToContentWs_preserves_tokens s s1 hws

/-- `skipToContent` preserves tokens exactly.

Proved by delegating to `skipToContentLoop_preserves_tokens`.
The refactoring from `do`+`mut` to explicit state threading removed
all monadic join points, making `unfold`+`split` proof-tractable.
Zero axioms, zero sorry. -/
theorem skipToContent_preserves_tokens (s : ScannerState) (s' : ScannerState) :
    skipToContent s = .ok s' →
    s'.tokens = s.tokens := by
  intro h
  unfold skipToContent at h
  exact skipToContentLoop_preserves_tokens s s' _ h

/-! ## flowLevel preservation through skipToContent chain

Each function in the skipToContent pipeline preserves `flowLevel` because
none of them emit tokens or modify flow state. -/

theorem consumeNewline_preserves_flowLevel (s : ScannerState) :
    (consumeNewline s).flowLevel = s.flowLevel := by
  unfold consumeNewline
  split
  · exact advance_preserves_flowLevel s
  · dsimp only []
    split
    · exact advance_preserves_flowLevel s
    · exact advance_preserves_flowLevel s
  · rfl

theorem skipSpaces_preserves_flowLevel (s : ScannerState) :
    (skipSpaces s).flowLevel = s.flowLevel := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_preserves_flowLevel]
    · rfl

theorem skipWhitespace_preserves_flowLevel (s : ScannerState) :
    (skipWhitespace s).flowLevel = s.flowLevel := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_preserves_flowLevel]
      · rfl
    · rfl

theorem collectCommentTextLoop_preserves_flowLevel (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.flowLevel = s.flowLevel := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_flowLevel]
    · rfl

theorem skipToEndOfLineLoop_preserves_flowLevel (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).flowLevel = s.flowLevel := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ fuel' IH =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_flowLevel]
    · rfl

theorem skipToEndOfLine_preserves_flowLevel (s : ScannerState) :
    (skipToEndOfLine s).flowLevel = s.flowLevel := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_flowLevel s _

theorem collectDirectiveNameLoop_preserves_flowLevel (s : ScannerState)
    (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).2.flowLevel = s.flowLevel := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' IH =>
    unfold collectDirectiveNameLoop; split
    · -- some c
      split
      · rw [IH, advance_preserves_flowLevel]  -- condition true: recurse
      · rfl  -- condition false: stop
    · rfl  -- none

theorem collectVersionMajorLoop_preserves_flowLevel (s : ScannerState)
    (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).2.flowLevel = s.flowLevel := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' IH =>
    unfold collectVersionMajorLoop
    split <;> try rfl
    · exact advance_preserves_flowLevel s
    · split
      · rw [IH, advance_preserves_flowLevel]
      · rfl

theorem collectVersionMinorLoop_preserves_flowLevel (s : ScannerState)
    (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).2.flowLevel = s.flowLevel := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' IH =>
    unfold collectVersionMinorLoop; split
    · -- some c
      split
      · rw [IH, advance_preserves_flowLevel]  -- isDigit true: recurse
      · rfl  -- isDigit false
    · rfl  -- none

theorem collectTagHandleDirectiveLoop_preserves_flowLevel (s : ScannerState)
    (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).2.flowLevel = s.flowLevel := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' IH =>
    unfold collectTagHandleDirectiveLoop; split
    · -- some c
      split
      · rw [IH, advance_preserves_flowLevel]  -- condition true: recurse
      · rfl  -- condition false: stop
    · rfl  -- none

theorem collectTagPrefixLoop_preserves_flowLevel (s : ScannerState)
    (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).2.flowLevel = s.flowLevel := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' IH =>
    unfold collectTagPrefixLoop; split
    · -- some c
      split
      · rw [IH, advance_preserves_flowLevel]  -- condition true: recurse
      · rfl  -- condition false: stop
    · rfl  -- none

theorem emitAt_preserves_flowLevel (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).flowLevel = s.flowLevel := by
  unfold ScannerState.emitAt; rfl

theorem skipToContentWs_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_flowLevel,
            skipSpaces_preserves_flowLevel]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_flowLevel,
              skipSpaces_preserves_flowLevel]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_flowLevel,
                skipSpaces_preserves_flowLevel]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_flowLevel,
            skipSpaces_preserves_flowLevel]
      · simp at h; rw [← h, skipSpaces_preserves_flowLevel]
    · simp at h; rw [← h, skipWhitespace_preserves_flowLevel,
        skipSpaces_preserves_flowLevel]
  · simp at h; rw [← h, skipWhitespace_preserves_flowLevel]

theorem skipToContentComment_preserves_flowLevel (s : ScannerState) :
    (skipToContentComment s).flowLevel = s.flowLevel := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_flowLevel, advance_preserves_flowLevel]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_flowLevel, advance_preserves_flowLevel]
      · rfl
  · rfl

theorem skipToContentLoop_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') :
    s'.flowLevel = s.flowLevel := by
  induction fuel generalizing s with
  | zero =>
    unfold skipToContentLoop at h
    simp at h; rw [← h]
  | succ fuel' IH =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · rename_i c hpeek
        split at h
        · split at h
          · have ih := IH _ h
            rw [ih, consumeNewline_preserves_flowLevel,
                skipToContentComment_preserves_flowLevel]
            exact skipToContentWs_preserves_flowLevel s s1 hws
          · have ih := IH _ h
            rw [ih, consumeNewline_preserves_flowLevel,
                skipToContentComment_preserves_flowLevel]
            exact skipToContentWs_preserves_flowLevel s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_flowLevel]
          exact skipToContentWs_preserves_flowLevel s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_flowLevel]
        exact skipToContentWs_preserves_flowLevel s s1 hws

theorem skipToContent_preserves_flowLevel (s : ScannerState) (s' : ScannerState) :
    skipToContent s = .ok s' →
    s'.flowLevel = s.flowLevel := by
  intro h
  unfold skipToContent at h
  exact skipToContentLoop_preserves_flowLevel s s' _ h

/-! ## Helper Lemmas for scan* Functions

Each scan* function called by scanNextToken either emits tokens or adds them via
helper functions. These lemmas establish that tokens are only appended, never removed.

Organized in ScanHelpers namespace to keep them separate from main API while
remaining visible to verification tooling (never use `private` for theorems). -/

namespace ScanHelpers

/-- When `collectPlainScalar_terminates?` returns `some result`, the result state is unchanged. -/
theorem collectPlainScalar_terminates?_state (c : Char) (s : ScannerState)
    (content spaces : String) (inFlow : Bool) (result : PlainScalarResult)
    (h : collectPlainScalar_terminates? c s content spaces inFlow = some result) :
    result.state = s := by
  unfold collectPlainScalar_terminates? at h
  split at h
  · injection h with h; cases h; rfl
  · split at h
    · simp only [] at h
      split at h
      · split at h
        · injection h with h; cases h; rfl
        · contradiction
      · split at h
        · injection h with h; cases h; rfl
        · contradiction
    · split at h
      · injection h with h; cases h; rfl
      · split at h
        · injection h with h; cases h; rfl
        · contradiction

/-- Helper: collectHexDigitsLoop preserves tokens. -/
theorem collectHexDigitsLoop_preserves_tokens (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.tokens = s.tokens := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_tokens s
        rw [ih, h_adv]
      · rfl

/-- Helper: parseHexEscape preserves tokens. -/
theorem parseHexEscape_preserves_tokens (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.tokens = s.tokens := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_tokens s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]

/-- Helper: processEscape preserves tokens. -/
theorem processEscape_preserves_tokens (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.tokens = s.tokens := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  -- Split on each character case
  repeat (split at h)
  -- Handle all goals
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_tokens s)
    | (have h_adv := advance_preserves_tokens s
       have h_hex := parseHexEscape_preserves_tokens s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )

/-- Helper: skipBlankLinesLoop preserves tokens. -/
theorem skipBlankLinesLoop_preserves_tokens (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.tokens = s.tokens := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_tokens s
        have h_cn := consumeNewline_preserves_tokens (skipSpaces s)
        rw [ih, h_cn, h_sp]

/-- Helper: foldQuotedNewlinesLoop preserves tokens. -/
theorem foldQuotedNewlinesLoop_preserves_tokens (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.tokens = s.tokens := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_tokens s
        have h_cn := consumeNewline_preserves_tokens (skipSpaces s)
        rw [ih, h_cn, h_sp]

/-- Helper: foldQuotedNewlines preserves tokens. -/
theorem foldQuotedNewlines_preserves_tokens (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.tokens = s.tokens := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_tokens s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_tokens (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_tokens (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_tokens (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  split at h <;> try contradiction
  · -- inFlow check branch
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
  · -- no inFlow check
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]

/-- Helper: collectPlainScalarLoop preserves tokens. -/
theorem collectPlainScalarLoop_preserves_tokens (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.tokens = s.tokens := by
  intro result h
  induction fuel generalizing s content lastLine with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek = none
      injection h with h_eq; cases h_eq; rfl
    · -- peek = some c
      rename_i c
      split at h
      · -- collectPlainScalar_terminates? = some → state = s
        rename_i hterm
        injection h with h_eq; cases h_eq
        rw [collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
      · -- collectPlainScalar_terminates? = none → continue
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk content_fold s_fold =>
              have h_fold := foldQuotedNewlines_preserves_tokens s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · -- recurse with content-length check
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ content_fold) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih s_fold (content ++ content_fold) "" h_loop, h_fold]
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- _handleBlockLineBreak = some → recurse
              rename_i content' s' hblk
              have hprop : s'.tokens = s.tokens := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipSpaces_preserves_tokens,
                    skipBlankLinesLoop_preserves_tokens, consumeNewline_preserves_tokens]
              split at h
              · -- s'.peek? = some '#' → terminate
                injection h with h_eq; cases h_eq; rfl
              · -- s'.peek? = _ → recurse with content-length check
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih _ _ _ h_loop, hprop]
                | error e => simp at h
        · split at h
          · -- isWhiteSpace c
            have h_adv := advance_preserves_tokens s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_tokens s
              rw [ih s.advance _ "" h, h_adv]

/-- Helper: collectDoubleQuotedLoop preserves tokens. -/
theorem collectDoubleQuotedLoop_preserves_tokens (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.tokens = s.tokens := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectDoubleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '"' case (closing quote)
      injection h with h_eq; cases h_eq
      exact advance_preserves_tokens s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break)
        have h_cn := consumeNewline_preserves_tokens s.advance
        have h_sw := skipWhitespace_preserves_tokens (consumeNewline s.advance)
        have h_adv := advance_preserves_tokens s
        rw [ih _ _ h, h_sw, h_cn, h_adv]
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_tokens s.advance ch s_after_escape heq
          have h_adv := advance_preserves_tokens s
          rw [ih _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_tokens s s_fold folded heq
          split at h <;> try contradiction
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [ih s_fold (trimTrailingWS content ++ folded) h, h_fold]
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_tokens s
        rw [ih _ _ h, h_adv]

/-- Helper: collectSingleQuotedLoop preserves tokens. -/
theorem collectSingleQuotedLoop_preserves_tokens (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.tokens = s.tokens := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectSingleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '\'' case
      simp only [] at h
      split at h
      · -- escaped quote: '\''\''
        have h_adv1 := advance_preserves_tokens s
        have h_adv2 := advance_preserves_tokens s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_tokens s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_tokens s s_fold folded heq
          split at h <;> try contradiction  -- atDocumentStart check
          split at h <;> try contradiction  -- atDocumentEnd check
          split at h <;> try contradiction  -- col ≤ currentIndent check
          rw [ih s_fold _ h, h_fold]
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_tokens s
        rw [ih s.advance _ h, h_adv]

/-- Helper: collectAnchorNameLoop preserves tokens. -/
theorem collectAnchorNameLoop_preserves_tokens (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s acc with
  | zero =>
    unfold collectAnchorNameLoop
    rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · -- some c
      split
      · -- condition true: recurse with advance
        rw [ih]
        exact advance_preserves_tokens s
      · -- condition false: return
        rfl
    · -- none
      rfl

/-- scanDocumentStart adds at least one token.

scanDocumentStart: unwindIndents (≥0) → emit .documentStart (+1) → advanceN 3 (preserves).
Total: ≥ s.tokens.size + 1. -/
theorem scanDocumentStart_adds_tokens (s : ScannerState) :
    (scanDocumentStart s).tokens.size ≥ s.tokens.size + 1 := by
  unfold scanDocumentStart
  -- unwindIndents adds ≥ 0 tokens, emit adds 1, advanceN and structure updates preserve
  have h_unwind := unwindIndents_adds_tokens s (-1)
  simp only [emit_tokens_size, advanceN_preserves_tokens]
  -- After unwind, key disable (preserves tokens), emit (+1), advanceN (preserves), final structure update (preserves)
  omega

/-- scanDocumentEnd adds at least one token (on success). -/
theorem skipDocEndWhitespace_preserves_tokens (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).tokens = s.tokens := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ fuel' ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

theorem scanDocumentEnd_adds_tokens (s : ScannerState) (s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') :
    s'.tokens.size ≥ s.tokens.size + 1 := by
  -- The function unwinds indents (adds ≥ 0 tokens), emits documentEnd (+1), advanceN (preserves),
  -- then validates trailing content and returns result. All validation branches return the same result.
  unfold scanDocumentEnd at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          dsimp only []
          simp only [emit_tokens_size, advanceN_preserves_tokens]
          have h_unwind := unwindIndents_adds_tokens s (-1)
          omega
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          dsimp only []
          simp only [emit_tokens_size, advanceN_preserves_tokens]
          have h_unwind := unwindIndents_adds_tokens s (-1)
          omega
      · split at h
        · split at h
          · contradiction
          · injection h with h_eq; subst h_eq
            dsimp only []
            simp only [emit_tokens_size, advanceN_preserves_tokens]
            have h_unwind := unwindIndents_adds_tokens s (-1)
            omega
        · contradiction

/-- collectDirectiveNameLoop preserves tokens. -/
theorem collectDirectiveNameLoop_preserves_tokens (s : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

/-- collectVersionMajorLoop preserves tokens. -/
theorem collectVersionMajorLoop_preserves_tokens (s : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_tokens s
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

/-- collectVersionMinorLoop preserves tokens. -/
theorem collectVersionMinorLoop_preserves_tokens (s : ScannerState) (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

/-- collectTagHandleDirectiveLoop preserves tokens. -/
theorem collectTagHandleDirectiveLoop_preserves_tokens (s : ScannerState) (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

/-- collectTagPrefixLoop preserves tokens. -/
theorem collectTagPrefixLoop_preserves_tokens (s : ScannerState) (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

/-- scanYamlDirective is monotonic in token count. -/
theorem scanYamlDirective_monotonic (s : ScannerState) (s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanYamlDirective s s_after_ws startPos = .ok s') :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanYamlDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · -- some '#'
        split at h
        · contradiction
        · injection h with h_eq; subst h_eq; dsimp only []
          rw [emitAt_tokens_size,
              skipWhitespace_preserves_tokens,
              collectVersionMinorLoop_preserves_tokens,
              collectVersionMajorLoop_preserves_tokens,
              h_ws]
          omega
      · -- some c (not '#')
        split at h
        · contradiction
        · split at h <;> try contradiction
          all_goals (injection h with h_eq; subst h_eq; dsimp only []
                     rw [emitAt_tokens_size,
                         skipWhitespace_preserves_tokens,
                         collectVersionMinorLoop_preserves_tokens,
                         collectVersionMajorLoop_preserves_tokens,
                         h_ws]
                     omega)
      · -- none
        injection h with h_eq; subst h_eq; dsimp only []
        rw [emitAt_tokens_size,
            skipWhitespace_preserves_tokens,
            collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens,
            h_ws]
        omega

/-- scanTagDirective is monotonic in token count. -/
theorem scanTagDirective_monotonic (s : ScannerState) (s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanTagDirective s s_after_ws startPos = .ok s') :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanTagDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · -- some '#'
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      rw [emitAt_tokens_size,
          skipWhitespace_preserves_tokens,
          collectTagPrefixLoop_preserves_tokens,
          skipWhitespace_preserves_tokens,
          collectTagHandleDirectiveLoop_preserves_tokens,
          h_ws]
      omega
  · -- some c (not '#')
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      rw [emitAt_tokens_size,
          skipWhitespace_preserves_tokens,
          collectTagPrefixLoop_preserves_tokens,
          skipWhitespace_preserves_tokens,
          collectTagHandleDirectiveLoop_preserves_tokens,
          h_ws]
      omega
  · -- none
    injection h with h_eq; subst h_eq; dsimp only []
    rw [emitAt_tokens_size,
        skipWhitespace_preserves_tokens,
        collectTagPrefixLoop_preserves_tokens,
        skipWhitespace_preserves_tokens,
        collectTagHandleDirectiveLoop_preserves_tokens,
        h_ws]
    omega

/-- scanDirective is monotonic in token count (YAML/TAG add one, unknown preserves). -/
theorem scanDirective_monotonic (s : ScannerState) (s' : ScannerState)
    (h : scanDirective s = .ok s') :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanDirective at h
  dsimp only [] at h
  split at h
  · contradiction
  · split at h
    · -- YAML
      have h_ws : (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
        rw [skipWhitespace_preserves_tokens,
            collectDirectiveNameLoop_preserves_tokens,
            advance_preserves_tokens]
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_tokens]
        exact scanYamlDirective_monotonic s _ _ s_inner h_ws h_inner
      · contradiction
    · split at h
      · -- TAG
        have h_ws : (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
          rw [skipWhitespace_preserves_tokens,
              collectDirectiveNameLoop_preserves_tokens,
              advance_preserves_tokens]
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_tokens]
          exact scanTagDirective_monotonic s _ _ s_inner h_ws h_inner
        · contradiction
      · -- unknown directive
        injection h with h_eq; subst h_eq
        rw [skipToEndOfLine_preserves_tokens,
            skipWhitespace_preserves_tokens,
            collectDirectiveNameLoop_preserves_tokens,
            advance_preserves_tokens]
        omega

/-- scanAnchorOrAlias adds exactly one token (on success). -/
theorem scanAnchorOrAlias_adds_one_token (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    have h_collect := collectAnchorNameLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
    have h_adv := advance_preserves_tokens s
    rw [emitAt_tokens_size, h_collect, h_adv]

/-- Helper: collectVerbatimTagLoop preserves tokens. -/
theorem collectVerbatimTagLoop_preserves_tokens (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.tokens = s.tokens := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_tokens s  -- found '>', return (uri, s.advance)
    · split  -- isUriCharBool
      · rw [ih]; exact advance_preserves_tokens s  -- uri char, recurse
      · rfl  -- not uri char, return (uri, s)
    · simp only []  -- none, return (uri, s)

/-- Helper: collectTagSuffixLoop preserves tokens. -/
theorem collectTagSuffixLoop_preserves_tokens (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_tokens s  -- tag char, recurse
      · simp only []  -- not tag char, return
    · simp only []  -- none, return

/-- Helper: collectTagHandleLoop preserves tokens. -/
theorem collectTagHandleLoop_preserves_tokens (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.tokens = s.tokens := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_tokens s  -- found '!', return (chars, true, s.advance)
    · split  -- split on the if condition
      · rw [ih]; exact advance_preserves_tokens s  -- word char, recurse
      · simp only []  -- not word char, return
    · simp only []  -- none, return

/-- scanVerbatimTag adds exactly one token (on success). -/
theorem scanVerbatimTag_adds_one_token (s : ScannerState) (pos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s pos = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp only [emitAt_tokens_size, collectVerbatimTagLoop_preserves_tokens, advance_preserves_tokens]

/-- scanSecondaryTag adds exactly one token. -/
theorem scanSecondaryTag_adds_one_token (s : ScannerState) (pos : YamlPos) :
    (scanSecondaryTag s pos).tokens.size = s.tokens.size + 1 := by
  unfold scanSecondaryTag
  simp only [emitAt_tokens_size, collectTagSuffixLoop_preserves_tokens, advance_preserves_tokens]

/-- scanNamedTag adds exactly one token. -/
theorem scanNamedTag_adds_one_token (s : ScannerState) (pos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s pos inputEnd).tokens.size = s.tokens.size + 1 := by
  unfold scanNamedTag; simp only []
  have h_handle := collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  split
  · let s_after := (collectTagHandleLoop s "" (inputEnd - s.offset)).snd.snd
    have h_suffix := collectTagSuffixLoop_preserves_tokens s_after "" (inputEnd - s_after.offset)
    rw [emitAt_tokens_size, h_suffix, h_handle]
  · rw [emitAt_tokens_size, h_handle]

/-- scanTag adds exactly one token (on success). -/
theorem scanTag_adds_one_token (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · -- verbatim
    simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h; dsimp only []
      have := scanVerbatimTag_adds_one_token s.advance s.currentPos s_verb hv
      simp [this, advance_preserves_tokens]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    rw [scanSecondaryTag_adds_one_token, advance_preserves_tokens]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    rw [scanNamedTag_adds_one_token, advance_preserves_tokens]

/-- `parseBlockHeaderLoop` preserves tokens (structural recursion on fuel). -/
theorem parseBlockHeaderLoop_preserves_tokens (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.tokens = s.tokens := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_tokens s
    · rw [ih]; exact advance_preserves_tokens s
    · split
      · rw [ih]; exact advance_preserves_tokens s
      · rfl
    · rfl

/-- `consumeExactSpaces` preserves tokens (structural recursion on count). -/
theorem consumeExactSpaces_preserves_tokens (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.tokens = s.tokens := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_tokens s
    · rfl

/-- `collectLineContentLoop` preserves tokens (structural recursion on fuel). -/
theorem collectLineContentLoop_preserves_tokens (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.tokens = s.tokens := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_tokens s
    · rfl

/-- `collectBlockScalarLoop` preserves tokens (structural recursion on fuel). -/
theorem collectBlockScalarLoop_preserves_tokens (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.tokens = s.tokens := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_tokens s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_tokens, consumeExactSpaces_preserves_tokens]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_tokens,
                    collectLineContentLoop_preserves_tokens, consumeExactSpaces_preserves_tokens]
              · rw [ih, collectLineContentLoop_preserves_tokens, consumeExactSpaces_preserves_tokens]
            · rw [collectLineContentLoop_preserves_tokens, consumeExactSpaces_preserves_tokens]

/-! ### scanBlockScalar sub-function preservation lemmas -/

/-- scanBlockScalarSkipComment preserves tokens. -/
theorem scanBlockScalarSkipComment_preserves_tokens (s : ScannerState) :
    (scanBlockScalarSkipComment s).tokens = s.tokens := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_tokens, advance_preserves_tokens]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

/-- scanBlockScalarConsumeNewline preserves tokens on success. -/
theorem scanBlockScalarConsumeNewline_preserves_tokens (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.tokens = s.tokens := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_tokens s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

/-- scanBlockScalarBody adds exactly one token on success. -/
theorem scanBlockScalarBody_adds_one_token (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState) (h_tok : s_nl.tokens = s_orig.tokens)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.tokens.size = s_orig.tokens.size + 1 := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_tokens_size, collectBlockScalarLoop_preserves_tokens, h_tok]

/-- scanBlockScalar adds exactly one token (on success). -/
theorem scanBlockScalar_adds_one_token (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_adds_one_token s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_tokens,
              skipWhitespace_preserves_tokens,
              parseBlockHeaderLoop_preserves_tokens,
              advance_preserves_tokens]) h

/-- scanDoubleQuoted adds exactly one token (on success). -/
theorem scanDoubleQuoted_adds_one_token (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · -- !inFlow case: validateTrailingContent check
    split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    rw [emitAt_tokens_size, h_collect, h_adv]
  · -- inFlow case: no validation
    injection h with h_eq; subst h_eq
    rw [emitAt_tokens_size, h_collect, h_adv]

/-- scanSingleQuoted adds exactly one token (on success). -/
theorem scanSingleQuoted_adds_one_token (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · -- !inFlow case: validateTrailingContent check
    split at h <;> try contradiction
    injection h with h_eq; subst h_eq
    rw [emitAt_tokens_size, h_collect, h_adv]
  · -- inFlow case: no validation
    injection h with h_eq; subst h_eq
    rw [emitAt_tokens_size, h_collect, h_adv]

/-- scanPlainScalar adds exactly one token (on success). -/
theorem scanPlainScalar_adds_one_token (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') :
    s'.tokens.size = s.tokens.size + 1 := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  -- Extract result from collectPlainScalarLoop
  rename_i heq
  have h_collect := collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  injection h with h_eq; subst h_eq
  rw [emitAt_tokens_size, h_collect]

/-! ### Bind helper lemmas for do-block proof decomposition -/

/-- Reduce `Except.bind` on a known `.error` constructor. -/
theorem bind_error_simp {ε α β : Type} {e : ε} {f : α → Except ε β} :
    Except.bind (Except.error e) f = Except.error e := rfl

/-- Reduce `Except.bind` on a known `.ok` constructor. -/
theorem bind_ok_simp {ε α β : Type} {v : α} {f : α → Except ε β} :
    Except.bind (Except.ok v) f = f v := rfl

/-! ### Struct update token-preservation lemmas -/

/-- Updating `needIndentCheck` preserves tokens. -/
theorem needIndentCheck_update_tokens (s : ScannerState) (b : Bool) :
    { s with needIndentCheck := b }.tokens = s.tokens := rfl

/-- Updating `allowDirectives`/`documentEverStarted` preserves tokens. -/
theorem allowDir_ite_tokens (s : ScannerState) :
    (if s.allowDirectives = true then
      { s with allowDirectives := false, documentEverStarted := true }
    else s).tokens = s.tokens := by
  split <;> rfl

/-- Updating `simpleKey` preserves tokens. -/
theorem simpleKey_update_tokens (s : ScannerState) (sk : SimpleKeyState) :
    { s with simpleKey := sk }.tokens = s.tokens := rfl

/-! ### scanFlowEntry and scanBlockEntry token bounds -/

/-- scanFlowEntry adds at least one token (on success). -/
theorem scanFlowEntry_adds_one_token (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    s'.tokens.size ≥ s.tokens.size + 1 := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind] at h
  repeat (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       simp only [advance_preserves_tokens, emit_tokens_size]; omega))

/-- scanBlockEntry adds at least one token (on success). -/
theorem scanBlockEntry_adds_tokens (s : ScannerState) (s' : ScannerState)
    (h : scanBlockEntry s = .ok s') :
    s'.tokens.size ≥ s.tokens.size + 1 := by
  unfold scanBlockEntry at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  repeat (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq
       simp only [advance_preserves_tokens, emit_tokens_size]
       have := pushSequenceIndent_tokens_monotonic s s.col; omega)
    | (injection h with h_eq; subst h_eq
       simp only [advance_preserves_tokens, emit_tokens_size]; omega))

/-! ### Dispatch helper monotonicity -/

/-- Structural dispatch preserves or adds tokens (on success). -/
theorem dispatchStructural_tokens_mono (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := scanDocumentEnd_adds_tokens s _ (by assumption); simp_all <;> omega)
    | (have := scanDirective_monotonic s _ (by assumption); simp_all <;> omega)
    | (have := scanDocumentStart_adds_tokens s; simp_all <;> omega)
    | (simp_all <;> omega)

/-- Flow indicator dispatch preserves or adds tokens (on success). -/
theorem dispatchFlowIndicators_tokens_mono (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := scanFlowEntry_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (have := scanFlowSequenceStart_adds_one_token s; simp_all <;> omega)
    | (have := scanFlowSequenceEnd_adds_one_token s; simp_all <;> omega)
    | (have := scanFlowMappingStart_adds_one_token s; simp_all <;> omega)
    | (have := scanFlowMappingEnd_adds_one_token s; simp_all <;> omega)
    | (simp_all <;> omega)

/-- Block indicator dispatch preserves or adds tokens (on success). -/
theorem dispatchBlockIndicators_tokens_mono (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := scanBlockEntry_adds_tokens s _ (by assumption); simp_all <;> omega)
    | (have := scanKey_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (have := scanValue_adds_tokens s _ (by assumption); simp_all <;> omega)
    | (simp_all <;> omega)

/-- Content dispatch preserves or adds tokens (on success). -/
theorem dispatchContent_tokens_mono (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.tokens.size ≥ s.tokens.size := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := scanBlockScalar_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (have := scanDoubleQuoted_adds_one_token s _ (by assumption);
       simp only [Except.ok.injEq] at h; subst h; dsimp only []; omega)
    | (have := scanSingleQuoted_adds_one_token s _ (by assumption);
       simp only [Except.ok.injEq] at h; subst h; dsimp only []; omega)
    | (have := scanDoubleQuoted_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (have := scanSingleQuoted_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (have := scanPlainScalar_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (simp only [Except.ok.injEq] at h; subst h; dsimp only [];
       have := scanAnchorOrAlias_adds_one_token s true _ (by assumption); omega)
    | (have := scanAnchorOrAlias_adds_one_token s false _ (by assumption); simp_all <;> omega)
    | (have := scanTag_adds_one_token s _ (by assumption); simp_all <;> omega)
    | (simp_all <;> omega)

/-! ### Preprocess monotonicity and prefix preservation -/

/-- Preprocess step preserves or adds tokens (on success with some result). -/
theorem preprocess_tokens_mono (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.tokens.size ≥ s.tokens.size := by
  unfold scanNextToken_preprocess at h
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i v heq_skip
    have h_skip := skipToContent_preserves_tokens s v heq_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1]
            have h_sk := saveSimpleKey_tokens_monotonic
              { unwindIndents v v.col with needIndentCheck := false }
            simp (config := { unfoldPartialApp := true }) at h_sk
            have h_uw := unwindIndents_adds_tokens v v.col
            have h_eq : v.tokens.size = s.tokens.size := by rw [h_skip]
            omega
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨h1, _⟩ := h
            rw [← h1]
            have h_sk := saveSimpleKey_tokens_monotonic v
            have := congrArg Array.size h_skip; omega

/-- Preprocess step preserves existing token prefix.

For any index i < original size, the preprocessed state's tokens[i] is unchanged.
This follows from: skipToContent (tokens =), unwindIndents (prefix preserved),
and saveSimpleKey (prefix preserved). -/
theorem preprocess_preserves_prefix (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (i : Nat) (h_bound : i < s.tokens.size) :
    s1.tokens[i]'(by have := preprocess_tokens_mono s s1 c h; omega) = s.tokens[i] := by
  unfold scanNextToken_preprocess at h
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i v heq_skip
    have h_skip := skipToContent_preserves_tokens s v heq_skip
    have h_sizes : v.tokens.size = s.tokens.size := congrArg Array.size h_skip
    have h_bound_v : i < v.tokens.size := by omega
    split at h
    · simp at h
    · split at h
      · -- needIndentCheck: unwindIndents + saveSimpleKey
        split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_uw_bound : i < (unwindIndents v v.col).tokens.size := by
              have := unwindIndents_adds_tokens v v.col; omega
            rw [saveSimpleKey_preserves_prefix _ i
              (by exact h_uw_bound)]
            rw [unwindIndents_preserves_prefix v v.col i h_bound_v]
            simp only [h_skip]
      · -- no needIndentCheck: just saveSimpleKey
        split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [saveSimpleKey_preserves_prefix v i h_bound_v]
            simp only [h_skip]

/-! ### Prefix preservation for scan functions -/

/-- `emitAt` preserves existing tokens (same pattern as `emit_preserves_tokens_at`). -/
theorem emitAt_preserves_tokens_at (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (i : Nat) (h : i < s.tokens.size) :
    (s.emitAt pos tok).tokens[i]'(by rw [emitAt_tokens_size]; omega) = s.tokens[i] := by
  unfold ScannerState.emitAt
  simp only [Array.getElem_push]
  split
  · rfl
  · omega

/-- pushMappingIndent preserves existing tokens. -/
theorem pushMappingIndent_preserves_prefix (s : ScannerState) (col : Int)
    (i : Nat) (h : i < s.tokens.size) :
    (pushMappingIndent s col).tokens[i]'(by
      have := pushMappingIndent_tokens_monotonic s col; omega) = s.tokens[i] := by
  unfold pushMappingIndent
  split
  · exact emit_preserves_tokens_at { s with indents := _ } .blockMappingStart i h
  · rfl

/-- pushSequenceIndent preserves existing tokens. -/
theorem pushSequenceIndent_preserves_prefix (s : ScannerState) (col : Int)
    (i : Nat) (h : i < s.tokens.size) :
    (pushSequenceIndent s col).tokens[i]'(by
      have := pushSequenceIndent_tokens_monotonic s col; omega) = s.tokens[i] := by
  unfold pushSequenceIndent
  split
  · exact emit_preserves_tokens_at { s with indents := _ } .blockSequenceStart i h
  · rfl

/-! ### Composition helpers for prefix preservation -/

/-- If `state.tokens = orig.tokens`, then `emit` on `state` preserves prefix of `orig`. -/
theorem emit_chain_preserves_prefix (state : ScannerState) (tok : YamlToken)
    {orig : ScannerState} (h_tok : state.tokens = orig.tokens)
    (i : Nat) (h_i : i < orig.tokens.size) :
    (state.emit tok).tokens[i]'(by rw [emit_tokens_size, h_tok]; omega) = orig.tokens[i] := by
  unfold ScannerState.emit
  simp only [Array.getElem_push, h_tok]
  split
  · rfl
  · omega

/-- If `state.tokens = orig.tokens`, then `emitAt` on `state` preserves prefix of `orig`. -/
theorem emitAt_chain_preserves_prefix (state : ScannerState) (pos : YamlPos) (tok : YamlToken)
    {orig : ScannerState} (h_tok : state.tokens = orig.tokens)
    (i : Nat) (h_i : i < orig.tokens.size) :
    (state.emitAt pos tok).tokens[i]'(by rw [emitAt_tokens_size, h_tok]; omega) = orig.tokens[i] := by
  unfold ScannerState.emitAt
  simp only [Array.getElem_push, h_tok]
  split
  · rfl
  · omega

/-- Emit after `unwindIndents` preserves prefix.  Generalised to take
    both a `SimpleKeyState` override and a `pendingKeyActive` override —
    matches the shape of `scanDocumentStart`/`scanDocumentEnd` after the
    Initiative 3 / J.2 dual-write. -/
theorem emit_unwind_preserves_prefix (s : ScannerState) (n : Int)
    (sk : SimpleKeyState) (pka : Option Nat) (tok : YamlToken)
    (i : Nat) (h_i : i < s.tokens.size) :
    ({ unwindIndents s n with simpleKey := sk, pendingKeyActive := pka }.emit tok).tokens[i]'(by
      have h1 := emit_tokens_size ({ unwindIndents s n with simpleKey := sk,
                                                            pendingKeyActive := pka }) tok
      have h2 := unwindIndents_adds_tokens s n
      have h3 : { unwindIndents s n with simpleKey := sk,
                                          pendingKeyActive := pka }.tokens.size
                = (unwindIndents s n).tokens.size := rfl
      omega) = s.tokens[i] := by
  unfold ScannerState.emit
  simp only [Array.getElem_push]
  split
  · exact unwindIndents_preserves_prefix s n i h_i
  · have := unwindIndents_adds_tokens s n; omega

/-! ### Per-function prefix preservation lemmas -/

/-- scanDocumentStart preserves token prefix. -/
theorem scanDocumentStart_preserves_prefix (s : ScannerState)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanDocumentStart s).tokens[i]'(by
      have := scanDocumentStart_adds_tokens s; omega) = s.tokens[i] := by
  unfold scanDocumentStart
  simp only [advanceN_preserves_tokens]
  exact emit_unwind_preserves_prefix s (-1) _ _ .documentStart i h_i

/-- scanDocumentEnd preserves token prefix. -/
theorem scanDocumentEnd_preserves_prefix (s s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanDocumentEnd_adds_tokens s s' h; omega) = s.tokens[i] := by
  unfold scanDocumentEnd at h; dsimp only [] at h; simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq; dsimp only []
          simp only [advanceN_preserves_tokens]
          exact emit_unwind_preserves_prefix s (-1) _ _ .documentEnd i h_i
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq; dsimp only []
          simp only [advanceN_preserves_tokens]
          exact emit_unwind_preserves_prefix s (-1) _ _ .documentEnd i h_i
      · split at h
        · split at h
          · contradiction
          · injection h with h_eq; subst h_eq; dsimp only []
            simp only [advanceN_preserves_tokens]
            exact emit_unwind_preserves_prefix s (-1) _ _ .documentEnd i h_i
        · contradiction

/-- scanYamlDirective preserves token prefix. -/
theorem scanYamlDirective_preserves_prefix (s s_after_ws : ScannerState)
    (startPos : YamlPos) (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanYamlDirective s s_after_ws startPos = .ok s')
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanYamlDirective_monotonic s s_after_ws startPos s' h_ws h; omega)
    = s.tokens[i] := by
  unfold scanYamlDirective at h; dsimp only [] at h; simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq; dsimp only []
          apply emitAt_chain_preserves_prefix
          rw [skipWhitespace_preserves_tokens, collectVersionMinorLoop_preserves_tokens,
              collectVersionMajorLoop_preserves_tokens, h_ws]
      · split at h
        · contradiction
        · split at h <;> try contradiction
          all_goals (injection h with h_eq; subst h_eq; dsimp only []
                     apply emitAt_chain_preserves_prefix
                     rw [skipWhitespace_preserves_tokens, collectVersionMinorLoop_preserves_tokens,
                         collectVersionMajorLoop_preserves_tokens, h_ws])
      · injection h with h_eq; subst h_eq; dsimp only []
        apply emitAt_chain_preserves_prefix
        rw [skipWhitespace_preserves_tokens, collectVersionMinorLoop_preserves_tokens,
            collectVersionMajorLoop_preserves_tokens, h_ws]

/-- scanTagDirective preserves token prefix. -/
theorem scanTagDirective_preserves_prefix (s s_after_ws : ScannerState)
    (startPos : YamlPos) (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanTagDirective s s_after_ws startPos = .ok s')
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanTagDirective_monotonic s s_after_ws startPos s' h_ws h; omega)
    = s.tokens[i] := by
  unfold scanTagDirective at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · -- some '#'
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      apply emitAt_chain_preserves_prefix
      rw [skipWhitespace_preserves_tokens, collectTagPrefixLoop_preserves_tokens,
          skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  · -- some c
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      apply emitAt_chain_preserves_prefix
      rw [skipWhitespace_preserves_tokens, collectTagPrefixLoop_preserves_tokens,
          skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  · -- none
    injection h with h_eq; subst h_eq; dsimp only []
    apply emitAt_chain_preserves_prefix
    rw [skipWhitespace_preserves_tokens, collectTagPrefixLoop_preserves_tokens,
        skipWhitespace_preserves_tokens, collectTagHandleDirectiveLoop_preserves_tokens, h_ws]

/-- scanDirective preserves token prefix. -/
theorem scanDirective_preserves_prefix (s s' : ScannerState)
    (h : scanDirective s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanDirective_monotonic s s' h; omega) = s.tokens[i] := by
  unfold scanDirective at h; dsimp only [] at h
  split at h
  · contradiction
  · have h_ws : (skipWhitespace (collectDirectiveNameLoop s.advance ""
        (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
      rw [skipWhitespace_preserves_tokens, collectDirectiveNameLoop_preserves_tokens,
          advance_preserves_tokens]
    split at h
    · -- YAML
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        have h_tok : (skipToEndOfLine s_inner).tokens = s_inner.tokens :=
          skipToEndOfLine_preserves_tokens s_inner
        have h_mono := scanYamlDirective_monotonic s _ _ s_inner h_ws h_inner
        simp only [h_tok]
        exact scanYamlDirective_preserves_prefix s _ _ s_inner h_ws h_inner i h_i
      · contradiction
    · split at h
      · -- TAG
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          have h_tok : (skipToEndOfLine s_inner).tokens = s_inner.tokens :=
            skipToEndOfLine_preserves_tokens s_inner
          simp only [h_tok]
          exact scanTagDirective_preserves_prefix s _ _ s_inner h_ws h_inner i h_i
        · contradiction
      · -- Unknown directive: tokens fully preserved
        injection h with h_eq; subst h_eq
        have h_tok : (skipToEndOfLine (skipWhitespace (collectDirectiveNameLoop s.advance ""
              (s.inputEnd - s.advance.offset)).2)).tokens = s.tokens := by
          rw [skipToEndOfLine_preserves_tokens, h_ws]
        simp [h_tok]

/-- scanFlowSequenceStart preserves token prefix. -/
theorem scanFlowSequenceStart_preserves_prefix (s : ScannerState)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanFlowSequenceStart s).tokens[i]'(by
      have := scanFlowSequenceStart_adds_one_token s; omega) = s.tokens[i] := by
  unfold scanFlowSequenceStart
  simp only [advance_preserves_tokens]
  exact emit_preserves_tokens_at { s with simpleKey := _ } .flowSequenceStart i h_i

/-- scanFlowSequenceEnd preserves token prefix. -/
theorem scanFlowSequenceEnd_preserves_prefix (s : ScannerState)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanFlowSequenceEnd s).tokens[i]'(by
      have := scanFlowSequenceEnd_adds_one_token s; omega) = s.tokens[i] := by
  unfold scanFlowSequenceEnd
  simp only [advance_preserves_tokens]
  exact emit_preserves_tokens_at s .flowSequenceEnd i h_i

/-- scanFlowMappingStart preserves token prefix. -/
theorem scanFlowMappingStart_preserves_prefix (s : ScannerState)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanFlowMappingStart s).tokens[i]'(by
      have := scanFlowMappingStart_adds_one_token s; omega) = s.tokens[i] := by
  unfold scanFlowMappingStart
  simp only [advance_preserves_tokens]
  exact emit_preserves_tokens_at { s with simpleKey := _ } .flowMappingStart i h_i

/-- scanFlowMappingEnd preserves token prefix. -/
theorem scanFlowMappingEnd_preserves_prefix (s : ScannerState)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanFlowMappingEnd s).tokens[i]'(by
      have := scanFlowMappingEnd_adds_one_token s; omega) = s.tokens[i] := by
  unfold scanFlowMappingEnd
  simp only [advance_preserves_tokens]
  exact emit_preserves_tokens_at s .flowMappingEnd i h_i

/-- scanFlowEntry preserves token prefix. -/
theorem scanFlowEntry_preserves_prefix (s s' : ScannerState)
    (h : scanFlowEntry s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanFlowEntry_adds_one_token s s' h; omega) = s.tokens[i] := by
  unfold scanFlowEntry at h; simp only [bind, Except.bind] at h
  repeat (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq; dsimp only []
       simp only [advance_preserves_tokens]
       exact emit_preserves_tokens_at s .flowEntry i h_i))

/-- scanBlockEntry preserves token prefix. -/
theorem scanBlockEntry_preserves_prefix (s s' : ScannerState)
    (h : scanBlockEntry s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanBlockEntry_adds_tokens s s' h; omega) = s.tokens[i] := by
  unfold scanBlockEntry at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  repeat (split at h)
  all_goals (first
    | contradiction
    | (injection h with h_eq; subst h_eq; dsimp only []
       simp only [advance_preserves_tokens]
       unfold ScannerState.emit; simp only [Array.getElem_push]; split
       · exact pushSequenceIndent_preserves_prefix s s.col i h_i
       · have := pushSequenceIndent_tokens_monotonic s s.col; omega)
    | (injection h with h_eq; subst h_eq; dsimp only []
       simp only [advance_preserves_tokens]
       exact emit_preserves_tokens_at s .blockEntry i h_i))

/-- scanKey preserves token prefix. -/
theorem scanKey_preserves_prefix (s s' : ScannerState)
    (h : scanKey s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanKey_adds_one_token s s' h; omega) = s.tokens[i] := by
  unfold scanKey at h
  simp only [] at h
  split at h
  · -- !inFlow → pushMappingIndent called
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        simp only [advance_preserves_tokens]
        unfold ScannerState.emit; simp only [Array.getElem_push]; split
        · exact pushMappingIndent_preserves_prefix s s.col i h_i
        · have := pushMappingIndent_tokens_monotonic s s.col; omega
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [advance_preserves_tokens]
      unfold ScannerState.emit; simp only [Array.getElem_push]; split
      · exact pushMappingIndent_preserves_prefix s s.col i h_i
      · have := pushMappingIndent_tokens_monotonic s s.col; omega
  · -- inFlow → no pushMappingIndent
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        simp only [advance_preserves_tokens]
        exact emit_preserves_tokens_at s .key i h_i
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [advance_preserves_tokens]
      exact emit_preserves_tokens_at s .key i h_i

/-- scanAnchorOrAlias preserves token prefix (on success). -/
theorem scanAnchorOrAlias_preserves_prefix (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s')
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanAnchorOrAlias_adds_one_token s isAnchor s' hok; omega) = s.tokens[i] := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    apply emitAt_chain_preserves_prefix
    rw [collectAnchorNameLoop_preserves_tokens, advance_preserves_tokens]

theorem scanVerbatimTag_preserves_prefix (s : ScannerState) (pos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s pos = .ok s')
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanVerbatimTag_adds_one_token s pos s' hok; omega) = s.tokens[i] := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      apply emitAt_chain_preserves_prefix
      rw [collectVerbatimTagLoop_preserves_tokens, advance_preserves_tokens]

theorem scanSecondaryTag_preserves_prefix (s : ScannerState) (pos : YamlPos)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanSecondaryTag s pos).tokens[i]'(by
      have := scanSecondaryTag_adds_one_token s pos; omega) = s.tokens[i] := by
  unfold scanSecondaryTag
  apply emitAt_chain_preserves_prefix
  rw [collectTagSuffixLoop_preserves_tokens, advance_preserves_tokens]

theorem scanNamedTag_preserves_prefix (s : ScannerState) (pos : YamlPos) (inputEnd : Nat)
    (i : Nat) (h_i : i < s.tokens.size) :
    (scanNamedTag s pos inputEnd).tokens[i]'(by
      have := scanNamedTag_adds_one_token s pos inputEnd; omega) = s.tokens[i] := by
  unfold scanNamedTag; simp only []
  have h_handle := collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  split
  · apply emitAt_chain_preserves_prefix
    rw [collectTagSuffixLoop_preserves_tokens, h_handle]
  · apply emitAt_chain_preserves_prefix
    rw [h_handle]

/-- scanTag preserves token prefix (on success). -/
theorem scanTag_preserves_prefix (s : ScannerState)
    (s_ok : ScannerState) (hok : scanTag s = .ok s_ok)
    (i : Nat) (h_i : i < s.tokens.size) :
    s_ok.tokens[i]'(by have := scanTag_adds_one_token s s_ok hok; omega) = s.tokens[i] := by
  unfold scanTag at hok; dsimp only [] at hok
  have h_adv := advance_preserves_tokens s
  split at hok
  · -- verbatim
    simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h; dsimp only []
      have := scanVerbatimTag_preserves_prefix s.advance s.currentPos s_verb hv i
        (by rw [h_adv]; exact h_i)
      simp_all
  · have h := Except.ok.inj hok; subst h; dsimp only []
    have := scanSecondaryTag_preserves_prefix s.advance s.currentPos i
      (by rw [h_adv]; exact h_i)
    simp_all
  · have h := Except.ok.inj hok; subst h; dsimp only []
    have := scanNamedTag_preserves_prefix s.advance s.currentPos s.inputEnd i
      (by rw [h_adv]; exact h_i)
    simp_all

/-- scanBlockScalarBody preserves token prefix. -/
theorem scanBlockScalarBody_preserves_prefix (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState) (h_tok : s_nl.tokens = s_orig.tokens)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s')
    (i : Nat) (h_i : i < s_orig.tokens.size) :
    s'.tokens[i]'(by have := scanBlockScalarBody_adds_one_token s_orig s_nl chomp expl isLit startPos s' h_tok h; omega) = s_orig.tokens[i] := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals (apply emitAt_chain_preserves_prefix; rw [collectBlockScalarLoop_preserves_tokens, h_tok])

/-- scanBlockScalar preserves token prefix. -/
theorem scanBlockScalar_preserves_prefix (s s' : ScannerState)
    (h : scanBlockScalar s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanBlockScalar_adds_one_token s s' h; omega) = s.tokens[i] := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_prefix s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_tokens,
              skipWhitespace_preserves_tokens,
              parseBlockHeaderLoop_preserves_tokens,
              advance_preserves_tokens]) h i h_i

/-- scanDoubleQuoted preserves token prefix. -/
theorem scanDoubleQuoted_preserves_prefix (s s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanDoubleQuoted_adds_one_token s s' h; omega) = s.tokens[i] := by
  unfold scanDoubleQuoted at h; simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq; dsimp only []
    apply emitAt_chain_preserves_prefix; rw [h_collect, h_adv]
  · injection h with h_eq; subst h_eq; dsimp only []
    apply emitAt_chain_preserves_prefix; rw [h_collect, h_adv]

/-- scanSingleQuoted preserves token prefix. -/
theorem scanSingleQuoted_preserves_prefix (s s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanSingleQuoted_adds_one_token s s' h; omega) = s.tokens[i] := by
  unfold scanSingleQuoted at h; simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at h
  · split at h <;> try contradiction
    injection h with h_eq; subst h_eq; dsimp only []
    apply emitAt_chain_preserves_prefix; rw [h_collect, h_adv]
  · injection h with h_eq; subst h_eq; dsimp only []
    apply emitAt_chain_preserves_prefix; rw [h_collect, h_adv]

/-- scanPlainScalar preserves token prefix. -/
theorem scanPlainScalar_preserves_prefix (s s' : ScannerState)
    (h : scanPlainScalar s = .ok s') (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := scanPlainScalar_adds_one_token s s' h; omega) = s.tokens[i] := by
  unfold scanPlainScalar at h; simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i heq
  have h_collect := collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  injection h with h_eq; subst h_eq; dsimp only []
  apply emitAt_chain_preserves_prefix; rw [h_collect]

/-! ### Dispatch prefix preservation proofs -/

/-- Structural dispatch preserves prefix. -/
theorem dispatchStructural_preserves_prefix (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := dispatchStructural_tokens_mono s c s' h; omega) = s.tokens[i] := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_preserves_prefix s i h_i
    | exact scanDocumentEnd_preserves_prefix s _ (by assumption) i h_i
    | exact scanDirective_preserves_prefix s _ (by assumption) i h_i
    | (simp_all; done)

/-- Flow indicator dispatch preserves prefix. -/
theorem dispatchFlowIndicators_preserves_prefix (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := dispatchFlowIndicators_tokens_mono s c s' h; omega) = s.tokens[i] := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, bind_error_simp, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanFlowSequenceStart_preserves_prefix s i h_i
    | exact scanFlowSequenceEnd_preserves_prefix s i h_i
    | exact scanFlowMappingStart_preserves_prefix s i h_i
    | exact scanFlowMappingEnd_preserves_prefix s i h_i
    | exact scanFlowEntry_preserves_prefix s _ (by assumption) i h_i
    | (simp_all; done)

/-- scanValuePrepare preserves tokens at indices below n, given the simpleKey invariant.

If simpleKey.possible, setIfInBounds operates at tokenIndex (≥ n) and tokenIndex+1 (≥ n),
so indices below n are untouched. If not possible, tokens are either unchanged or grown
via pushMappingIndent (append-only). -/
theorem scanValuePrepare_preserves_prefix (s : ScannerState)
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (i : Nat) (h_bound : i < n) :
    (scanValuePrepare s).tokens[i]'(by
      have := scanValuePrepare_tokens_monotonic s; omega) =
    s.tokens[i]'(by omega) := by
  -- Initiative 3 / J.2 step 5 cutover: scanValuePrepare no longer
  -- mutates tokens (the three setIfInBounds calls were dropped).
  -- Every branch except `pushMappingIndent` is identity on `.tokens`.
  unfold scanValuePrepare
  split
  · -- simpleKey.possible = true
    split
    · split <;> rfl  -- !inFlow (both keyCol arms)
    · rfl            -- inFlow
  · -- simpleKey.possible = false
    split
    · rfl            -- explicitKeyLine.isSome
    · split
      · exact pushMappingIndent_preserves_prefix s s.col i (by omega)
      · rfl          -- inFlow: identity

/-- scanValuePrepare preserves `.pos` at ALL existing token positions.

When `possible = false`, no existing tokens are modified.
When `possible = true`, `setIfInBounds` at `idx` and `idx+1` replaces the token VALUE
but the new element has `.pos = simpleKey.pos`, which equals the old `.pos`
(from `SimpleKeyValid`). So `.pos` is preserved everywhere. -/
theorem scanValuePrepare_preserves_all_pos (s : ScannerState)
    (i : Nat) (hi : i < s.tokens.size) :
    ((scanValuePrepare s).tokens[i]'(by
      have := scanValuePrepare_tokens_monotonic s; omega)).pos =
    s.tokens[i].pos := by
  -- Initiative 3 / J.2 step 5 cutover: scanValuePrepare no longer
  -- mutates tokens, so `.pos` is preserved trivially everywhere except
  -- the `pushMappingIndent` branch.
  unfold scanValuePrepare
  split
  · -- simpleKey.possible = true
    split
    · split <;> rfl  -- !inFlow (both keyCol arms)
    · rfl            -- inFlow
  · -- simpleKey.possible = false
    split
    · rfl            -- explicitKeyLine.isSome
    · split
      · -- !inFlow: pushMappingIndent
        have := pushMappingIndent_preserves_prefix s s.col i (by omega)
        simp [this]
      · rfl          -- inFlow: identity

set_option maxHeartbeats 400000 in
/-- scanValue preserves tokens at indices below n, given the simpleKey invariant.

Decomposes scanValue into scanValueClearKey → scanValueValidate → scanValuePrepare →
emit → advance → scanValueTabCheck. The key step is scanValuePrepare, which uses
setIfInBounds at simpleKey.tokenIndex ≥ n, so indices < n are preserved. -/
theorem scanValue_preserves_prefix (s s' : ScannerState)
    (h : scanValue s = .ok s')
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n)
    (i : Nat) (h_bound : i < n) :
    s'.tokens[i]'(by have := scanValue_adds_tokens s s' h; omega) =
    s.tokens[i]'(by omega) := by
  unfold scanValue at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction  -- scanValueValidate = .error
  · split at h
    · contradiction  -- scanValueTabCheck = .error
    · injection h with h_eq; subst h_eq; dsimp only []
      have h_ck := scanValueClearKey_preserves_tokens s
      have h_inv' : (scanValueClearKey s).simpleKey.possible = true →
          (scanValueClearKey s).simpleKey.tokenIndex ≥ n := by
        unfold scanValueClearKey
        split
        · split
          · simp
          · split
            · simp
            · exact h_inv
        · exact h_inv
      have h_prep := scanValuePrepare_preserves_prefix (scanValueClearKey s) n
        (by rw [h_ck]; exact h_n) i h_bound
      have h_emit := emit_preserves_tokens_at (scanValuePrepare (scanValueClearKey s))
        YamlToken.value i (by have := scanValuePrepare_tokens_monotonic (scanValueClearKey s); rw [h_ck] at this; omega)
      have h_adv := advance_preserves_tokens ((scanValuePrepare (scanValueClearKey s)).emit .value)
      simp_all

set_option maxHeartbeats 400000 in
/-- scanValue preserves `.pos` at ALL existing token positions.
Requires `SimpleKeyValid` to establish that placeholder tokens at `tokenIndex`
already have `.pos = simpleKey.pos`. -/
theorem scanValue_preserves_all_pos (s s' : ScannerState)
    (h : scanValue s = .ok s')
    (_h_skv : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≤ s.tokens.size)
    (i : Nat) (hi : i < s.tokens.size) :
    (s'.tokens[i]'(by have := scanValue_adds_tokens s s' h; omega)).pos =
    s.tokens[i].pos := by
  unfold scanValue at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      have h_ck := scanValueClearKey_preserves_tokens s
      have h_prep := scanValuePrepare_preserves_all_pos (scanValueClearKey s) i (by rw [h_ck]; exact hi)
      have h_emit := emit_preserves_tokens_at (scanValuePrepare (scanValueClearKey s))
        YamlToken.value i (by have := scanValuePrepare_tokens_monotonic (scanValueClearKey s); rw [h_ck] at this; omega)
      have h_adv := advance_preserves_tokens ((scanValuePrepare (scanValueClearKey s)).emit .value)
      simp only [h_adv, h_emit]; rw [h_prep]; simp [h_ck]

/-- Block indicator dispatch preserves prefix below n (needs simpleKey invariant for scanValue). -/
theorem dispatchBlockIndicators_preserves_prefix (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n)
    (i : Nat) (h_bound : i < n) :
    s'.tokens[i]'(by have := dispatchBlockIndicators_tokens_mono s c s' h; omega) =
    s.tokens[i]'(by omega) := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals first
    | (have := scanBlockEntry_preserves_prefix s _ (by assumption) i (by omega); simp_all)
    | (have := scanKey_preserves_prefix s _ (by assumption) i (by omega); simp_all)
    | (have := scanValue_preserves_prefix s _ (by assumption) n h_n h_inv i h_bound; simp_all)
    | (simp_all)

/-- Content dispatch preserves prefix. -/
theorem dispatchContent_preserves_prefix (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (i : Nat) (h_i : i < s.tokens.size) :
    s'.tokens[i]'(by have := dispatchContent_tokens_mono s c s' h; omega) = s.tokens[i] := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  -- Handle anchor/alias/tag with explicit generalize to keep ok-equation
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_preserves_prefix s true s_a h_anch i h_i
  · split at h
    · -- '*': alias
      split at h
      · simp at h
      · generalize h_anch : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanAnchorOrAlias_preserves_prefix s false s_a h_anch i h_i
    · split at h
      · -- '!': tag
        generalize h_tag : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_prefix s s_t h_tag i h_i
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_prefix s _ (by assumption) i h_i
          | exact scanDoubleQuoted_preserves_prefix s _ (by assumption) i h_i
          | exact scanSingleQuoted_preserves_prefix s _ (by assumption) i h_i
          | exact scanPlainScalar_preserves_prefix s _ (by assumption) i h_i
          | (simp_all; done)

end ScanHelpers

/-! ## Main Theorems -/

/-- scanNextToken preserves or adds tokens.

`scanNextToken` may emit tokens but never removes existing ones.

**Proof strategy**: scanNextToken has the following structure:
  1. `skipToContent` - preserves tokens (no emit calls)
  2. `unwindIndents` - adds tokens (proven: unwindIndents_adds_tokens)
  3. `saveSimpleKey` - monotonic (proven: saveSimpleKey_tokens_monotonic)
  4. Match on character, calling one of ~17 scan* functions:
     - scanDocumentStart, scanDocumentEnd, scanDirective
     - scanFlowSequenceStart, scanFlowSequenceEnd
     - scanFlowMappingStart, scanFlowMappingEnd
     - scanFlowEntry, scanBlockEntry
     - scanKey, scanValue
     - scanAnchorOrAlias, scanTag
     - scanBlockScalar, scanDoubleQuoted, scanSingleQuoted, scanPlainScalar

Each scan* function either:
  - Returns an error (handled by Except monad)
  - Returns a ScannerState that calls emit (which appends tokens)

Complete proof requires: Analyze each scan* function to show it only appends tokens.
This is mechanical but tedious (~17 functions × ~10-50 lines each). -/
theorem scanNextToken_adds_tokens (s : ScannerState) (s' : ScannerState) :
    (scanNextToken s = .ok (some s')) →
    s'.tokens.size ≥ s.tokens.size := by
  intro h
  unfold scanNextToken at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · split at h
    · simp at h
    · have h_pre := ScanHelpers.preprocess_tokens_mono s _ _ (by assumption)
      repeat (any_goals (split at h))
      any_goals contradiction
      any_goals (simp at h)
      all_goals first
        | contradiction
        | (simp at h)
        | (have := ScanHelpers.dispatchStructural_tokens_mono _ _ _ (by assumption);
           simp_all <;> omega)
        | (have h_d := ScanHelpers.dispatchFlowIndicators_tokens_mono _ _ _ (by assumption);
           rw [ScanHelpers.allowDir_ite_tokens] at h_d; simp_all <;> omega)
        | (have h_d := ScanHelpers.dispatchBlockIndicators_tokens_mono _ _ _ (by assumption);
           rw [ScanHelpers.allowDir_ite_tokens] at h_d; simp_all <;> omega)
        | (have h_d := ScanHelpers.dispatchContent_tokens_mono _ _ _ (by assumption);
           rw [ScanHelpers.allowDir_ite_tokens] at h_d; simp_all <;> omega)
        | (simp_all <;> omega)

/-! ### simpleKey Preservation Lemmas -/

theorem advance_preserves_simpleKey (s : ScannerState) :
    s.advance.simpleKey = s.simpleKey := by
  unfold ScannerState.advance; dsimp only []; split <;> (try split) <;> (try split) <;> rfl

theorem emit_preserves_simpleKey (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).simpleKey = s.simpleKey := by
  unfold ScannerState.emit; rfl

theorem skipSpacesLoop_preserves_simpleKey (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_simpleKey _)
    · rfl

theorem skipWhitespaceLoop_preserves_simpleKey (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_simpleKey _)
      · rfl
    · rfl

theorem skipToEndOfLineLoop_preserves_simpleKey (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_simpleKey _)
    · rfl

theorem skipSpaces_preserves_simpleKey (s : ScannerState) :
    (skipSpaces s).simpleKey = s.simpleKey := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_simpleKey s _

theorem skipWhitespace_preserves_simpleKey (s : ScannerState) :
    (skipWhitespace s).simpleKey = s.simpleKey := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_simpleKey s _

theorem skipToContentWs_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold skipToContentWs at h
  split at h
  · -- needIndentCheck = true
    simp only [] at h  -- reduce `let s1 := skipSpaces s`
    split at h
    · -- col ≤ currentIndent
      split at h
      · -- peek? = some '\t'
        split at h
        · -- probe.peek? = some '#'
          simp at h; rw [← h, skipWhitespace_preserves_simpleKey, skipSpaces_preserves_simpleKey]
        · -- probe.peek? = some c (not '#')
          split at h
          · simp at h; rw [← h, skipWhitespace_preserves_simpleKey, skipSpaces_preserves_simpleKey]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_simpleKey, skipSpaces_preserves_simpleKey]
            · simp at h
        · -- probe.peek? = none
          simp at h; rw [← h, skipWhitespace_preserves_simpleKey, skipSpaces_preserves_simpleKey]
      · -- peek? ≠ some '\t'
        simp at h; rw [← h, skipSpaces_preserves_simpleKey]
    · -- col > currentIndent
      simp at h; rw [← h, skipWhitespace_preserves_simpleKey, skipSpaces_preserves_simpleKey]
  · -- needIndentCheck = false
    simp at h; rw [← h, skipWhitespace_preserves_simpleKey]

theorem skipToEndOfLine_preserves_simpleKey (s : ScannerState) :
    (skipToEndOfLine s).simpleKey = s.simpleKey := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_simpleKey s _

/-- Helper: collectCommentTextLoop preserves simpleKey. -/
theorem collectCommentTextLoop_preserves_simpleKey (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.simpleKey = s.simpleKey := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_simpleKey]
    · rfl

theorem skipToContentComment_preserves_simpleKey (s : ScannerState) :
    (skipToContentComment s).simpleKey = s.simpleKey := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKey, advance_preserves_simpleKey]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKey, advance_preserves_simpleKey]
      · rfl
  · rfl

theorem consumeNewline_preserves_simpleKey (s : ScannerState) :
    (consumeNewline s).simpleKey = s.simpleKey := by
  unfold consumeNewline
  split
  · exact advance_preserves_simpleKey s
  · simp only []; split
    · exact advance_preserves_simpleKey _
    · exact advance_preserves_simpleKey _
  · rfl

theorem skipToContentLoop_preserves_simpleKey (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · have := ih _ h; rw [this, consumeNewline_preserves_simpleKey,
              skipToContentComment_preserves_simpleKey]; exact skipToContentWs_preserves_simpleKey s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_simpleKey,
              skipToContentComment_preserves_simpleKey]; exact skipToContentWs_preserves_simpleKey s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_simpleKey]
          exact skipToContentWs_preserves_simpleKey s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_simpleKey]
        exact skipToContentWs_preserves_simpleKey s s1 hws

theorem skipToContent_preserves_simpleKey (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_simpleKey s s' _ h

theorem unwindIndentsLoop_preserves_simpleKey (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop; split
    · have := ih { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }
      simp [emit_preserves_simpleKey] at this; exact this
    · rfl

theorem unwindIndents_preserves_simpleKey (s : ScannerState) (col : Int) :
    (unwindIndents s col).simpleKey = s.simpleKey := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_simpleKey s col _


/-! ### Loop-level simpleKey preservation lemmas -/


theorem collectHexDigitsLoop_preserves_simpleKey (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.simpleKey = s.simpleKey := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_simpleKey s
        rw [ih, h_adv]
      · rfl


theorem parseHexEscape_preserves_simpleKey (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.simpleKey = s.simpleKey := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_simpleKey s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]


theorem processEscape_preserves_simpleKey (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.simpleKey = s.simpleKey := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  -- Split on each character case
  repeat (split at h)
  -- Handle all goals
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_simpleKey s)
    | (have h_adv := advance_preserves_simpleKey s
       have h_hex := parseHexEscape_preserves_simpleKey s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )


theorem skipBlankLinesLoop_preserves_simpleKey (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_simpleKey s
        have h_cn := consumeNewline_preserves_simpleKey (skipSpaces s)
        rw [ih, h_cn, h_sp]


theorem foldQuotedNewlinesLoop_preserves_simpleKey (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.simpleKey = s.simpleKey := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_simpleKey s
        have h_cn := consumeNewline_preserves_simpleKey (skipSpaces s)
        rw [ih, h_cn, h_sp]


theorem foldQuotedNewlines_preserves_simpleKey (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.simpleKey = s.simpleKey := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_simpleKey s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_simpleKey (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_simpleKey (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_simpleKey (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  split at h <;> try contradiction
  · -- inFlow check branch
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
  · -- no inFlow check
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]


theorem collectPlainScalarLoop_preserves_simpleKey (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.simpleKey = s.simpleKey := by
  intro result h
  induction fuel generalizing s content lastLine with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek = none
      injection h with h_eq; cases h_eq; rfl
    · -- peek = some c
      rename_i c
      split at h
      · -- collectPlainScalar_terminates? = some → state = s
        rename_i hterm
        injection h with h_eq; cases h_eq
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
      · -- collectPlainScalar_terminates? = none → continue
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk content_fold s_fold =>
              have h_fold := foldQuotedNewlines_preserves_simpleKey s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · -- recurse with content-length check
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ content_fold) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih s_fold (content ++ content_fold) "" h_loop, h_fold]
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- _handleBlockLineBreak = some → recurse
              rename_i content' s' hblk
              have hprop : s'.simpleKey = s.simpleKey := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipSpaces_preserves_simpleKey,
                    skipBlankLinesLoop_preserves_simpleKey, consumeNewline_preserves_simpleKey]
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih _ _ _ h_loop, hprop]
                | error e => simp at h
        · split at h
          · -- isWhiteSpace c
            have h_adv := advance_preserves_simpleKey s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_simpleKey s
              rw [ih s.advance _ "" h, h_adv]


theorem collectDoubleQuotedLoop_preserves_simpleKey (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.simpleKey = s.simpleKey := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectDoubleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '"' case (closing quote)
      injection h with h_eq; cases h_eq
      exact advance_preserves_simpleKey s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break)
        have h_cn := consumeNewline_preserves_simpleKey s.advance
        have h_sw := skipWhitespace_preserves_simpleKey (consumeNewline s.advance)
        have h_adv := advance_preserves_simpleKey s
        rw [ih _ _ h, h_sw, h_cn, h_adv]
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_simpleKey s.advance ch s_after_escape heq
          have h_adv := advance_preserves_simpleKey s
          rw [ih _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_simpleKey s s_fold folded heq
          split at h <;> try contradiction
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [ih s_fold (trimTrailingWS content ++ folded) h, h_fold]
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_simpleKey s
        rw [ih _ _ h, h_adv]


theorem collectSingleQuotedLoop_preserves_simpleKey (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.simpleKey = s.simpleKey := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectSingleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '\'' case
      simp only [] at h
      split at h
      · -- escaped quote: '\''\''
        have h_adv1 := advance_preserves_simpleKey s
        have h_adv2 := advance_preserves_simpleKey s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_simpleKey s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_simpleKey s s_fold folded heq
          split at h <;> try contradiction  -- atDocumentStart check
          split at h <;> try contradiction  -- atDocumentEnd check
          split at h <;> try contradiction  -- col ≤ currentIndent check
          rw [ih s_fold _ h, h_fold]
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_simpleKey s
        rw [ih s.advance _ h, h_adv]


theorem collectAnchorNameLoop_preserves_simpleKey (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s acc with
  | zero =>
    unfold collectAnchorNameLoop
    rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · -- some c
      split
      · -- condition true: recurse with advance
        rw [ih]
        exact advance_preserves_simpleKey s
      · -- condition false: return
        rfl
    · -- none
      rfl

theorem collectAnchorNameLoop_preserves_flowLevel (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s acc with
  | zero =>
    unfold collectAnchorNameLoop
    rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · -- some c
      split
      · -- condition true: recurse with advance
        rw [ih]
        exact advance_preserves_flowLevel s
      · -- condition false: return
        rfl
    · -- none
      rfl

theorem collectDirectiveNameLoop_preserves_simpleKey (s : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl


theorem collectVersionMajorLoop_preserves_simpleKey (s : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_simpleKey s
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl


theorem collectVersionMinorLoop_preserves_simpleKey (s : ScannerState) (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl


theorem collectTagHandleDirectiveLoop_preserves_simpleKey (s : ScannerState) (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl


theorem collectTagPrefixLoop_preserves_simpleKey (s : ScannerState) (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl


theorem collectVerbatimTagLoop_preserves_simpleKey (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_simpleKey s  -- found '>', return (uri, s.advance)
    · split  -- isUriCharBool
      · rw [ih]; exact advance_preserves_simpleKey s  -- uri char, recurse
      · rfl  -- not uri char, return (uri, s)
    · simp only []  -- none, return (uri, s)


theorem collectTagSuffixLoop_preserves_simpleKey (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_simpleKey s  -- tag char, recurse
      · simp only []  -- not tag char, return
    · simp only []  -- none, return


theorem collectTagHandleLoop_preserves_simpleKey (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_simpleKey s  -- found '!', return (chars, true, s.advance)
    · split  -- split on the if condition
      · rw [ih]; exact advance_preserves_simpleKey s  -- word char, recurse
      · simp only []  -- not word char, return
    · simp only []  -- none, return


theorem parseBlockHeaderLoop_preserves_simpleKey (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_simpleKey s
    · rw [ih]; exact advance_preserves_simpleKey s
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl


theorem consumeExactSpaces_preserves_simpleKey (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.simpleKey = s.simpleKey := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_simpleKey s
    · rfl


theorem collectLineContentLoop_preserves_simpleKey (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_simpleKey s
    · rfl


theorem collectBlockScalarLoop_preserves_simpleKey (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.simpleKey = s.simpleKey := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_simpleKey s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_simpleKey, consumeExactSpaces_preserves_simpleKey]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_simpleKey,
                    collectLineContentLoop_preserves_simpleKey, consumeExactSpaces_preserves_simpleKey]
              · rw [ih, collectLineContentLoop_preserves_simpleKey, consumeExactSpaces_preserves_simpleKey]
            · rw [collectLineContentLoop_preserves_simpleKey, consumeExactSpaces_preserves_simpleKey]


theorem skipDocEndWhitespace_preserves_simpleKey (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).simpleKey = s.simpleKey := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ fuel' ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact advance_preserves_simpleKey s
      · rfl
    · rfl

/-! ### simpleKeyStack Preservation Lemmas -/

theorem advance_preserves_simpleKeyStack (s : ScannerState) :
    s.advance.simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.advance; dsimp only []; split <;> (try split) <;> (try split) <;> rfl

theorem emit_preserves_simpleKeyStack (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.emit; rfl

theorem skipSpacesLoop_preserves_simpleKeyStack (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_simpleKeyStack _)
    · rfl

theorem skipWhitespaceLoop_preserves_simpleKeyStack (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_simpleKeyStack _)
      · rfl
    · rfl

theorem skipToEndOfLineLoop_preserves_simpleKeyStack (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_simpleKeyStack _)
    · rfl

theorem skipSpaces_preserves_simpleKeyStack (s : ScannerState) :
    (skipSpaces s).simpleKeyStack = s.simpleKeyStack := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_simpleKeyStack s _

theorem skipWhitespace_preserves_simpleKeyStack (s : ScannerState) :
    (skipWhitespace s).simpleKeyStack = s.simpleKeyStack := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_simpleKeyStack s _

theorem skipToEndOfLine_preserves_simpleKeyStack (s : ScannerState) :
    (skipToEndOfLine s).simpleKeyStack = s.simpleKeyStack := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_simpleKeyStack s _

/-- Helper: collectCommentTextLoop preserves simpleKeyStack. -/
theorem collectCommentTextLoop_preserves_simpleKeyStack (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_simpleKeyStack]
    · rfl

theorem skipToContentWs_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyStack, skipSpaces_preserves_simpleKeyStack]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyStack, skipSpaces_preserves_simpleKeyStack]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyStack, skipSpaces_preserves_simpleKeyStack]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyStack, skipSpaces_preserves_simpleKeyStack]
      · simp at h; rw [← h, skipSpaces_preserves_simpleKeyStack]
    · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyStack, skipSpaces_preserves_simpleKeyStack]
  · simp at h; rw [← h, skipWhitespace_preserves_simpleKeyStack]

theorem skipToContentComment_preserves_simpleKeyStack (s : ScannerState) :
    (skipToContentComment s).simpleKeyStack = s.simpleKeyStack := by
  unfold skipToContentComment
  split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKeyStack, advance_preserves_simpleKeyStack]
      · rfl
    · -- peekBack? = none
      split  -- if commentOk
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKeyStack, advance_preserves_simpleKeyStack]
      · rfl
  · rfl

theorem consumeNewline_preserves_simpleKeyStack (s : ScannerState) :
    (consumeNewline s).simpleKeyStack = s.simpleKeyStack := by
  unfold consumeNewline
  split
  · exact advance_preserves_simpleKeyStack s
  · simp only []; split
    · exact advance_preserves_simpleKeyStack _
    · exact advance_preserves_simpleKeyStack _
  · rfl

theorem skipToContentLoop_preserves_simpleKeyStack (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · have := ih _ h; rw [this, consumeNewline_preserves_simpleKeyStack,
              skipToContentComment_preserves_simpleKeyStack]; exact skipToContentWs_preserves_simpleKeyStack s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_simpleKeyStack,
              skipToContentComment_preserves_simpleKeyStack]; exact skipToContentWs_preserves_simpleKeyStack s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_simpleKeyStack]
          exact skipToContentWs_preserves_simpleKeyStack s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_simpleKeyStack]
        exact skipToContentWs_preserves_simpleKeyStack s s1 hws

theorem skipToContent_preserves_simpleKeyStack (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_simpleKeyStack s s' _ h

theorem unwindIndentsLoop_preserves_simpleKeyStack (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop; split
    · have := ih { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }
      simp [emit_preserves_simpleKeyStack] at this; exact this
    · rfl

theorem unwindIndents_preserves_simpleKeyStack (s : ScannerState) (col : Int) :
    (unwindIndents s col).simpleKeyStack = s.simpleKeyStack := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_simpleKeyStack s col _

theorem saveSimpleKey_preserves_simpleKeyStack (st : ScannerState) :
    (saveSimpleKey st).simpleKeyStack = st.simpleKeyStack := by
  unfold saveSimpleKey
  split
  · rfl
  · split <;> rfl


/-! ### Loop-level simpleKeyStack preservation lemmas -/

theorem collectHexDigitsLoop_preserves_simpleKeyStack (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.simpleKeyStack = s.simpleKeyStack := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_simpleKeyStack s
        rw [ih, h_adv]
      · rfl


theorem parseHexEscape_preserves_simpleKeyStack (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_simpleKeyStack s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]


theorem processEscape_preserves_simpleKeyStack (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  -- Split on each character case
  repeat (split at h)
  -- Handle all goals
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_simpleKeyStack s)
    | (have h_adv := advance_preserves_simpleKeyStack s
       have h_hex := parseHexEscape_preserves_simpleKeyStack s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )


theorem skipBlankLinesLoop_preserves_simpleKeyStack (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_simpleKeyStack s
        have h_cn := consumeNewline_preserves_simpleKeyStack (skipSpaces s)
        rw [ih, h_cn, h_sp]


theorem foldQuotedNewlinesLoop_preserves_simpleKeyStack (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_simpleKeyStack s
        have h_cn := consumeNewline_preserves_simpleKeyStack (skipSpaces s)
        rw [ih, h_cn, h_sp]


theorem foldQuotedNewlines_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_simpleKeyStack s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_simpleKeyStack (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_simpleKeyStack (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_simpleKeyStack (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  split at h <;> try contradiction
  · -- inFlow check branch
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
  · -- no inFlow check
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]


theorem collectPlainScalarLoop_preserves_simpleKeyStack (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.simpleKeyStack = s.simpleKeyStack := by
  intro result h
  induction fuel generalizing s content lastLine with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek = none
      injection h with h_eq; cases h_eq; rfl
    · -- peek = some c
      rename_i c
      split at h
      · -- collectPlainScalar_terminates? = some → state = s
        rename_i hterm
        injection h with h_eq; cases h_eq
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
      · -- collectPlainScalar_terminates? = none → continue
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk content_fold s_fold =>
              have h_fold := foldQuotedNewlines_preserves_simpleKeyStack s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ content_fold) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih s_fold (content ++ content_fold) "" h_loop, h_fold]
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- _handleBlockLineBreak = some → recurse
              rename_i content' s' hblk
              have hprop : s'.simpleKeyStack = s.simpleKeyStack := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipSpaces_preserves_simpleKeyStack,
                    skipBlankLinesLoop_preserves_simpleKeyStack,
                    consumeNewline_preserves_simpleKeyStack]
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih _ _ _ h_loop, hprop]
                | error e => simp at h
        · split at h
          · -- isWhiteSpace c
            have h_adv := advance_preserves_simpleKeyStack s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_simpleKeyStack s
              rw [ih s.advance _ "" h, h_adv]


theorem collectDoubleQuotedLoop_preserves_simpleKeyStack (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.simpleKeyStack = s.simpleKeyStack := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectDoubleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '"' case (closing quote)
      injection h with h_eq; cases h_eq
      exact advance_preserves_simpleKeyStack s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break)
        have h_cn := consumeNewline_preserves_simpleKeyStack s.advance
        have h_sw := skipWhitespace_preserves_simpleKeyStack (consumeNewline s.advance)
        have h_adv := advance_preserves_simpleKeyStack s
        rw [ih _ _ h, h_sw, h_cn, h_adv]
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_simpleKeyStack s.advance ch s_after_escape heq
          have h_adv := advance_preserves_simpleKeyStack s
          rw [ih _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_simpleKeyStack s s_fold folded heq
          split at h <;> try contradiction
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [ih s_fold (trimTrailingWS content ++ folded) h, h_fold]
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_simpleKeyStack s
        rw [ih _ _ h, h_adv]


theorem collectSingleQuotedLoop_preserves_simpleKeyStack (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.simpleKeyStack = s.simpleKeyStack := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectSingleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '\'' case
      simp only [] at h
      split at h
      · -- escaped quote: '\''\''
        have h_adv1 := advance_preserves_simpleKeyStack s
        have h_adv2 := advance_preserves_simpleKeyStack s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_simpleKeyStack s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_simpleKeyStack s s_fold folded heq
          split at h <;> try contradiction  -- atDocumentStart check
          split at h <;> try contradiction  -- atDocumentEnd check
          split at h <;> try contradiction  -- col ≤ currentIndent check
          rw [ih s_fold _ h, h_fold]
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_simpleKeyStack s
        rw [ih s.advance _ h, h_adv]


theorem collectAnchorNameLoop_preserves_simpleKeyStack (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s acc with
  | zero =>
    unfold collectAnchorNameLoop
    rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · -- some c
      split
      · -- condition true: recurse with advance
        rw [ih]
        exact advance_preserves_simpleKeyStack s
      · -- condition false: return
        rfl
    · -- none
      rfl


theorem collectDirectiveNameLoop_preserves_simpleKeyStack (s : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl


theorem collectVersionMajorLoop_preserves_simpleKeyStack (s : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_simpleKeyStack s
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl


theorem collectVersionMinorLoop_preserves_simpleKeyStack (s : ScannerState) (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl


theorem collectTagHandleDirectiveLoop_preserves_simpleKeyStack (s : ScannerState) (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl


theorem collectTagPrefixLoop_preserves_simpleKeyStack (s : ScannerState) (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl


theorem collectVerbatimTagLoop_preserves_simpleKeyStack (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_simpleKeyStack s  -- found '>', return (uri, s.advance)
    · split  -- isUriCharBool
      · rw [ih]; exact advance_preserves_simpleKeyStack s  -- uri char, recurse
      · rfl  -- not uri char, return (uri, s)
    · simp only []  -- none, return (uri, s)


theorem collectTagSuffixLoop_preserves_simpleKeyStack (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s  -- tag char, recurse
      · simp only []  -- not tag char, return
    · simp only []  -- none, return


theorem collectTagHandleLoop_preserves_simpleKeyStack (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_simpleKeyStack s  -- found '!', return (chars, true, s.advance)
    · split  -- split on the if condition
      · rw [ih]; exact advance_preserves_simpleKeyStack s  -- word char, recurse
      · simp only []  -- not word char, return
    · simp only []  -- none, return


theorem parseBlockHeaderLoop_preserves_simpleKeyStack (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_simpleKeyStack s
    · rw [ih]; exact advance_preserves_simpleKeyStack s
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl


theorem consumeExactSpaces_preserves_simpleKeyStack (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.simpleKeyStack = s.simpleKeyStack := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_simpleKeyStack s
    · rfl


theorem collectLineContentLoop_preserves_simpleKeyStack (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_simpleKeyStack s
    · rfl


theorem collectBlockScalarLoop_preserves_simpleKeyStack (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_simpleKeyStack s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_simpleKeyStack, consumeExactSpaces_preserves_simpleKeyStack]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_simpleKeyStack,
                    collectLineContentLoop_preserves_simpleKeyStack, consumeExactSpaces_preserves_simpleKeyStack]
              · rw [ih, collectLineContentLoop_preserves_simpleKeyStack, consumeExactSpaces_preserves_simpleKeyStack]
            · rw [collectLineContentLoop_preserves_simpleKeyStack, consumeExactSpaces_preserves_simpleKeyStack]


theorem skipDocEndWhitespace_preserves_simpleKeyStack (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).simpleKeyStack = s.simpleKeyStack := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ fuel' ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact advance_preserves_simpleKeyStack s
      · rfl
    · rfl

/-! ### Full SimpleKeyAbove Preservation -/

theorem preprocess_preserves_simpleKeyStack (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextToken_preprocess at h
  simp only [bind, ScanHelpers.bind_error_simp, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_stack_skip := skipToContent_preserves_simpleKeyStack s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [saveSimpleKey_preserves_simpleKeyStack]
            show (unwindIndents s_skip s_skip.col).simpleKeyStack = s.simpleKeyStack
            rw [unwindIndents_preserves_simpleKeyStack]; exact h_stack_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [saveSimpleKey_preserves_simpleKeyStack]; exact h_stack_skip

/-- Preprocessing maintains the simpleKey part of the invariant.

After `scanNextToken_preprocess`, if the preprocessed state `s1` has
`simpleKey.possible = true`, then `simpleKey.tokenIndex ≥ n`.

This holds because:
- `skipToContent` preserves simpleKey.
- `unwindIndents` preserves simpleKey (only emits blockEnd tokens).
- `saveSimpleKey` either:
  (a) returns unchanged (invariant preserved from input), or
  (b) sets `tokenIndex := tokens.size ≥ n` (fresh key at current position), or
  (c) returns unchanged (invariant preserved from input). -/
theorem preprocess_simpleKey_inv (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) :
    s1.simpleKey.possible = true → s1.simpleKey.tokenIndex ≥ n := by
  -- First prove a standalone fact about saveSimpleKey
  have h_save : ∀ (st : ScannerState),
      n ≤ st.tokens.size →
      (st.simpleKey.possible = true → st.simpleKey.tokenIndex ≥ n) →
      (saveSimpleKey st).simpleKey.possible = true →
      (saveSimpleKey st).simpleKey.tokenIndex ≥ n := by
    intro st h_tok h_sk
    unfold saveSimpleKey
    split
    · exact h_sk  -- explicitKeyLine: unchanged
    · split
      · intro; dsimp only []; omega  -- simpleKeyAllowed: tokenIndex = tokens.size ≥ n
      · exact h_sk  -- else: unchanged
  -- Now unfold preprocess and trace to saveSimpleKey
  intro h_poss
  unfold scanNextToken_preprocess at h
  simp only [bind, ScanHelpers.bind_error_simp, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_sk_skip := skipToContent_preserves_simpleKey s s_skip h_skip
    have h_tok_skip := skipToContent_preserves_tokens s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · -- needIndentCheck path
        split at h
        · contradiction  -- trailing content error
        · split at h
          · simp at h  -- peek? = none
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_sk_u := unwindIndents_preserves_simpleKey s_skip s_skip.col
            have h_tok_u := unwindIndents_adds_tokens s_skip s_skip.col
            have h_tok_pre : n ≤ { unwindIndents s_skip s_skip.col with needIndentCheck := false }.tokens.size := by
              show n ≤ (unwindIndents s_skip s_skip.col).tokens.size
              have := congrArg Array.size h_tok_skip; omega
            have h_sk_pre : { unwindIndents s_skip s_skip.col with needIndentCheck := false }.simpleKey.possible = true →
                { unwindIndents s_skip s_skip.col with needIndentCheck := false }.simpleKey.tokenIndex ≥ n := by
              show (unwindIndents s_skip s_skip.col).simpleKey.possible = true → _
              simp only [h_sk_u, h_sk_skip]; exact h_inv
            exact h_save _ h_tok_pre h_sk_pre h_poss
      · -- no needIndentCheck path
        split at h
        · contradiction  -- trailing content error
        · split at h
          · simp at h  -- peek? = none
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            have h_tok_pre : n ≤ s_skip.tokens.size := by
              have := congrArg Array.size h_tok_skip; omega
            have h_sk_pre : s_skip.simpleKey.possible = true → s_skip.simpleKey.tokenIndex ≥ n := by
              simp only [h_sk_skip]; exact h_inv
            exact h_save s_skip h_tok_pre h_sk_pre h_poss

theorem preprocess_maintains_simpleKeyAbove (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n) :
    SimpleKeyAbove s1 n := by
  constructor
  · exact preprocess_simpleKey_inv s s1 c h n h_n h_inv.1
  · intro j hj hp
    have h_stack := preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2 j hj hp

/-! ### advanceN preservation -/

theorem advanceNLoop_preserves_simpleKey (s : ScannerState) (n : Nat) :
    (s.advanceNLoop n).simpleKey = s.simpleKey := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ _ ih =>
    unfold ScannerState.advanceNLoop
    exact (ih s.advance).trans (advance_preserves_simpleKey s)

theorem advanceNLoop_preserves_simpleKeyStack (s : ScannerState) (n : Nat) :
    (s.advanceNLoop n).simpleKeyStack = s.simpleKeyStack := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ _ ih =>
    unfold ScannerState.advanceNLoop
    exact (ih s.advance).trans (advance_preserves_simpleKeyStack s)

theorem advanceN_preserves_simpleKey (s : ScannerState) (n : Nat) :
    (s.advanceN n).simpleKey = s.simpleKey := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_simpleKey s n

theorem advanceN_preserves_simpleKeyStack (s : ScannerState) (n : Nat) :
    (s.advanceN n).simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_simpleKeyStack s n

/-! ### SimpleKeyAbove helper constructors -/

/-- If simpleKey is cleared and stack preserved, SimpleKeyAbove holds. -/
theorem SimpleKeyAbove_of_cleared_preserved (s_out s_in : ScannerState) (n : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAbove s_in n) : SimpleKeyAbove s_out n := by
  constructor
  · intro hp; exact absurd hp (by rw [h_sk]; decide)
  · intro j hj hp; simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp

/-- If both simpleKey and stack preserved, SimpleKeyAbove holds. -/
theorem SimpleKeyAbove_of_preserved (s_out s_in : ScannerState) (n : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAbove s_in n) : SimpleKeyAbove s_out n := by
  constructor
  · intro hp; rw [h_sk] at hp ⊢; exact h_inv.1 hp
  · intro j hj hp; simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp

/-- If simpleKey.possible preserved and tokenIndex preserved, and stack preserved,
    SimpleKeyAbove holds (for endLine-only updates). -/
theorem SimpleKeyAbove_of_endLine_update (s_out s_in : ScannerState) (n : Nat)
    (h_poss : s_out.simpleKey.possible = s_in.simpleKey.possible)
    (h_idx : s_out.simpleKey.tokenIndex = s_in.simpleKey.tokenIndex)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAbove s_in n) : SimpleKeyAbove s_out n := by
  constructor
  · intro hp
    have hp' : s_in.simpleKey.possible = true := by rw [← h_poss]; exact hp
    have := h_inv.1 hp'; omega
  · intro j hj hp; simp only [h_stack] at hj hp ⊢; exact h_inv.2 j hj hp

/-- Flow open: simpleKey cleared, old simpleKey pushed onto stack. -/
theorem SimpleKeyAbove_of_flow_open (s_out s_in : ScannerState) (n : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : SimpleKeyAbove s_in n) : SimpleKeyAbove s_out n := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hj hp => ?_⟩
  simp only [h_stack, Array.size_push] at hj
  by_cases hlt : j < s_in.simpleKeyStack.size
  · have hp' : s_in.simpleKeyStack[j].possible = true := by
      simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
    have h_ge := h_inv.2 j hlt hp'
    show s_out.simpleKeyStack[j].tokenIndex ≥ n
    simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_ge
  · have hj_eq : j = s_in.simpleKeyStack.size := by omega
    subst hj_eq
    have hp' : s_in.simpleKey.possible = true := by
      simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
    have h_ge := h_inv.1 hp'
    show s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex ≥ n
    simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_ge

/-- Flow close: simpleKey restored from stack back, stack popped. -/
theorem SimpleKeyAbove_of_flow_close (s_out s_in : ScannerState) (n : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKeyStack.back?.getD {})
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : SimpleKeyAbove s_in n)
    (h_size : s_in.simpleKeyStack.size > 0) : SimpleKeyAbove s_out n := by
  refine ⟨fun hp => ?_, fun j hj hp => ?_⟩
  · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
    have h_back : s_in.simpleKeyStack.back?.getD {} =
        s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
      simp [Array.back?, h_lt]
    rw [h_sk, h_back] at hp ⊢
    have := h_inv.2 _ (by omega) hp; omega
  · simp only [h_stack, Array.size_pop] at hj
    simp only [h_stack, Array.getElem_pop] at hp ⊢
    exact h_inv.2 j (by omega) hp

/-! ### Per-function simpleKey/simpleKeyStack property lemmas -/

/-! ### emitAt preservation -/

theorem emitAt_preserves_simpleKey (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).simpleKey = s.simpleKey := by
  unfold ScannerState.emitAt; rfl

theorem emitAt_preserves_simpleKeyStack (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).simpleKeyStack = s.simpleKeyStack := by
  unfold ScannerState.emitAt; rfl

/-! ### pushSequenceIndent / pushMappingIndent preservation -/

theorem pushSequenceIndent_preserves_simpleKey (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).simpleKey = s.simpleKey := by
  unfold pushSequenceIndent; split
  · simp [emit_preserves_simpleKey]
  · rfl

theorem pushSequenceIndent_preserves_simpleKeyStack (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).simpleKeyStack = s.simpleKeyStack := by
  unfold pushSequenceIndent; split
  · simp [emit_preserves_simpleKeyStack]
  · rfl

theorem pushMappingIndent_preserves_simpleKey (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).simpleKey = s.simpleKey := by
  unfold pushMappingIndent; split
  · simp [emit_preserves_simpleKey]
  · rfl

theorem pushMappingIndent_preserves_simpleKeyStack (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).simpleKeyStack = s.simpleKeyStack := by
  unfold pushMappingIndent; split
  · simp [emit_preserves_simpleKeyStack]
  · rfl

theorem pushMappingIndent_preserves_flowLevel (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).flowLevel = s.flowLevel := by
  unfold pushMappingIndent; split
  · simp [emit_preserves_flowLevel]
  · rfl

theorem pushSequenceIndent_preserves_flowLevel (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).flowLevel = s.flowLevel := by
  unfold pushSequenceIndent; split
  · simp [emit_preserves_flowLevel]
  · rfl

/-! ### Per-function simpleKey/simpleKeyStack lemmas -/

-- Category 1: Functions that clear simpleKey and preserve stack

theorem scanDocumentStart_clears_simpleKey (s : ScannerState) :
    (scanDocumentStart s).simpleKey.possible = false := by
  unfold scanDocumentStart; simp [advanceN_preserves_simpleKey, emit_preserves_simpleKey]

theorem scanDocumentStart_preserves_simpleKeyStack (s : ScannerState) :
    (scanDocumentStart s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanDocumentStart
  simp [advanceN_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
        unwindIndents_preserves_simpleKeyStack]

theorem scanDocumentStart_preserves_flowLevel (s : ScannerState) :
    (scanDocumentStart s).flowLevel = s.flowLevel := by
  unfold scanDocumentStart
  simp [advanceN_preserves_flowLevel, emit_preserves_flowLevel, unwindIndents_preserves_flowLevel]

theorem scanDocumentEnd_clears_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advanceN_preserves_simpleKey, emit_preserves_simpleKey]

theorem scanDocumentEnd_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advanceN_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
        unwindIndents_preserves_simpleKeyStack]

theorem scanDocumentEnd_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advanceN_preserves_flowLevel, emit_preserves_flowLevel,
        unwindIndents_preserves_flowLevel]

theorem scanKey_clears_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanKey s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanKey at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

theorem scanKey_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanKey s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanKey at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
                  pushMappingIndent_preserves_simpleKeyStack]

theorem scanKey_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanKey s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanKey at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_flowLevel, emit_preserves_flowLevel,
                  pushMappingIndent_preserves_flowLevel]

theorem scanValuePrepare_clears_simpleKey (s : ScannerState) :
    (scanValuePrepare s).simpleKey.possible = false := by
  unfold scanValuePrepare
  split
  · -- s.simpleKey.possible = true
    split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · -- pushMappingIndent preserves simpleKey; it was already false
        rw [pushMappingIndent_preserves_simpleKey]
        rename_i h_not_possible _ _; simp at h_not_possible; exact h_not_possible
      · -- s unchanged; simpleKey.possible was false
        rename_i h_not_possible _ _; simp at h_not_possible; exact h_not_possible

theorem scanValuePrepare_preserves_simpleKeyStack (s : ScannerState) :
    (scanValuePrepare s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndent_preserves_simpleKeyStack s s.col
      · rfl

theorem scanValuePrepare_preserves_flowLevel (s : ScannerState) :
    (scanValuePrepare s).flowLevel = s.flowLevel := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split
    · rfl
    · split
      · exact pushMappingIndent_preserves_flowLevel s s.col
      · rfl

theorem scanValue_clears_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  simp only [advance_preserves_simpleKey, emit_preserves_simpleKey]
  exact scanValuePrepare_clears_simpleKey (scanValueClearKey s)

theorem scanValue_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
        scanValuePrepare_preserves_simpleKeyStack]
  unfold scanValueClearKey; split
  · split
    · rfl
    · split <;> rfl
  · rfl

theorem scanValue_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  simp [advance_preserves_flowLevel, emit_preserves_flowLevel,
        scanValuePrepare_preserves_flowLevel]
  unfold scanValueClearKey; split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- scanBlockScalarSkipComment preserves simpleKeyStack. -/
theorem scanBlockScalarSkipComment_preserves_simpleKeyStack (s : ScannerState) :
    (scanBlockScalarSkipComment s).simpleKeyStack = s.simpleKeyStack := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_simpleKeyStack, advance_preserves_simpleKeyStack]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

/-- scanBlockScalarConsumeNewline preserves simpleKeyStack on success. -/
theorem scanBlockScalarConsumeNewline_preserves_simpleKeyStack (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_simpleKeyStack s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

/-- scanBlockScalarBody clears simpleKey on success. -/
theorem scanBlockScalarBody_clears_simpleKey (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.simpleKey.possible = false := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; rfl)

/-- scanBlockScalarBody preserves simpleKeyStack on success. -/
theorem scanBlockScalarBody_preserves_simpleKeyStack (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_sk : s_nl.simpleKeyStack = s_orig.simpleKeyStack)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.simpleKeyStack = s_orig.simpleKeyStack := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_simpleKeyStack, collectBlockScalarLoop_preserves_simpleKeyStack, h_sk]

theorem scanBlockScalar_clears_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.simpleKey.possible = false := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_clears_simpleKey s _ _ _ _ _ s' h

theorem scanBlockScalar_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_simpleKeyStack s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_simpleKeyStack _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_simpleKeyStack,
              skipWhitespace_preserves_simpleKeyStack,
              parseBlockHeaderLoop_preserves_simpleKeyStack,
              advance_preserves_simpleKeyStack]) h

-- Category 2: Functions that preserve both simpleKey and simpleKeyStack

theorem scanDirective_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanDirective s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · -- YAML directive (match wrapper)
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_simpleKey]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_preserves_simpleKey, skipWhitespace_preserves_simpleKey,
              collectVersionMinorLoop_preserves_simpleKey,
              collectVersionMajorLoop_preserves_simpleKey])
        all_goals (rw [collectDirectiveNameLoop_preserves_simpleKey, advance_preserves_simpleKey])
      · contradiction
    · split at h
      · -- TAG directive (match wrapper)
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_simpleKey]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_preserves_simpleKey, collectTagPrefixLoop_preserves_simpleKey,
                skipWhitespace_preserves_simpleKey,
                collectTagHandleDirectiveLoop_preserves_simpleKey,
                collectDirectiveNameLoop_preserves_simpleKey,
                advance_preserves_simpleKey]
        · contradiction
      · -- unknown directive → skipToEndOfLine
        simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_simpleKey, skipWhitespace_preserves_simpleKey,
              collectDirectiveNameLoop_preserves_simpleKey, advance_preserves_simpleKey]

theorem scanDirective_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanDirective s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · -- YAML directive (match wrapper)
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_simpleKeyStack]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_preserves_simpleKeyStack, skipWhitespace_preserves_simpleKeyStack,
              collectVersionMinorLoop_preserves_simpleKeyStack,
              collectVersionMajorLoop_preserves_simpleKeyStack])
        all_goals (rw [collectDirectiveNameLoop_preserves_simpleKeyStack, advance_preserves_simpleKeyStack])
      · contradiction
    · split at h
      · -- TAG directive (match wrapper)
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_simpleKeyStack]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_preserves_simpleKeyStack, collectTagPrefixLoop_preserves_simpleKeyStack,
                skipWhitespace_preserves_simpleKeyStack,
                collectTagHandleDirectiveLoop_preserves_simpleKeyStack,
                collectDirectiveNameLoop_preserves_simpleKeyStack,
                advance_preserves_simpleKeyStack]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_simpleKeyStack, skipWhitespace_preserves_simpleKeyStack,
              collectDirectiveNameLoop_preserves_simpleKeyStack, advance_preserves_simpleKeyStack]

theorem scanDirective_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanDirective s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · -- YAML directive
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_flowLevel]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_preserves_flowLevel, skipWhitespace_preserves_flowLevel,
              collectVersionMinorLoop_preserves_flowLevel,
              collectVersionMajorLoop_preserves_flowLevel])
        all_goals (rw [collectDirectiveNameLoop_preserves_flowLevel, advance_preserves_flowLevel])
      · contradiction
    · split at h
      · -- TAG directive
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_flowLevel]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_preserves_flowLevel, collectTagPrefixLoop_preserves_flowLevel,
                skipWhitespace_preserves_flowLevel,
                collectTagHandleDirectiveLoop_preserves_flowLevel,
                collectDirectiveNameLoop_preserves_flowLevel,
                advance_preserves_flowLevel]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_flowLevel, skipWhitespace_preserves_flowLevel,
              collectDirectiveNameLoop_preserves_flowLevel, advance_preserves_flowLevel]

theorem scanFlowEntry_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKey, emit_preserves_simpleKey]

theorem scanFlowEntry_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]

theorem scanBlockEntry_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanBlockEntry s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKey, emit_preserves_simpleKey,
                  pushSequenceIndent_preserves_simpleKey]

theorem scanBlockEntry_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanBlockEntry s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack,
                  pushSequenceIndent_preserves_simpleKeyStack]

theorem scanBlockEntry_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanBlockEntry s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_flowLevel, emit_preserves_flowLevel,
                  pushSequenceIndent_preserves_flowLevel]

theorem scanAnchorOrAlias_preserves_simpleKey (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_simpleKey, collectAnchorNameLoop_preserves_simpleKey,
          advance_preserves_simpleKey]

theorem scanAnchorOrAlias_preserves_simpleKeyStack (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_simpleKeyStack, collectAnchorNameLoop_preserves_simpleKeyStack,
          advance_preserves_simpleKeyStack]

theorem scanAnchorOrAlias_preserves_flowLevel (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_flowLevel, collectAnchorNameLoop_preserves_flowLevel,
          advance_preserves_flowLevel]

theorem scanVerbatimTag_preserves_simpleKey (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_simpleKey, collectVerbatimTagLoop_preserves_simpleKey,
            advance_preserves_simpleKey]

theorem scanVerbatimTag_preserves_simpleKeyStack (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_simpleKeyStack, collectVerbatimTagLoop_preserves_simpleKeyStack,
            advance_preserves_simpleKeyStack]

theorem scanSecondaryTag_preserves_simpleKey (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).simpleKey = s.simpleKey := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_simpleKey, collectTagSuffixLoop_preserves_simpleKey,
        advance_preserves_simpleKey]

theorem scanSecondaryTag_preserves_simpleKeyStack (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).simpleKeyStack = s.simpleKeyStack := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_simpleKeyStack, collectTagSuffixLoop_preserves_simpleKeyStack,
        advance_preserves_simpleKeyStack]

theorem scanNamedTag_preserves_simpleKey (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).simpleKey = s.simpleKey := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_simpleKey, collectTagSuffixLoop_preserves_simpleKey,
          collectTagHandleLoop_preserves_simpleKey]
  · simp [emitAt_preserves_simpleKey, collectTagHandleLoop_preserves_simpleKey]

theorem scanNamedTag_preserves_simpleKeyStack (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).simpleKeyStack = s.simpleKeyStack := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_simpleKeyStack, collectTagSuffixLoop_preserves_simpleKeyStack,
          collectTagHandleLoop_preserves_simpleKeyStack]
  · simp [emitAt_preserves_simpleKeyStack, collectTagHandleLoop_preserves_simpleKeyStack]

theorem scanTag_preserves_simpleKey (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.simpleKey = s.simpleKey := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_simpleKey s.advance s.currentPos s_verb hv,
            advance_preserves_simpleKey]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_simpleKey, advance_preserves_simpleKey]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_simpleKey, advance_preserves_simpleKey]

theorem scanTag_preserves_simpleKeyStack (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_simpleKeyStack s.advance s.currentPos s_verb hv,
            advance_preserves_simpleKeyStack]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_simpleKeyStack, advance_preserves_simpleKeyStack]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_simpleKeyStack, advance_preserves_simpleKeyStack]

/-! ### flowLevel preservation for tag/scalar sub-helpers -/

theorem collectVerbatimTagLoop_preserves_flowLevel (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_flowLevel s
    · split
      · rw [ih]; exact advance_preserves_flowLevel s
      · rfl
    · simp only []

theorem collectTagSuffixLoop_preserves_flowLevel (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_flowLevel s
      · simp only []
    · simp only []

theorem collectTagHandleLoop_preserves_flowLevel (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_flowLevel s
    · split
      · rw [ih]; exact advance_preserves_flowLevel s
      · simp only []
    · simp only []

theorem scanVerbatimTag_preserves_flowLevel (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_flowLevel, collectVerbatimTagLoop_preserves_flowLevel,
            advance_preserves_flowLevel]

theorem scanSecondaryTag_preserves_flowLevel (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).flowLevel = s.flowLevel := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_flowLevel, collectTagSuffixLoop_preserves_flowLevel,
        advance_preserves_flowLevel]

theorem scanNamedTag_preserves_flowLevel (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).flowLevel = s.flowLevel := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_flowLevel, collectTagSuffixLoop_preserves_flowLevel,
          collectTagHandleLoop_preserves_flowLevel]
  · simp [emitAt_preserves_flowLevel, collectTagHandleLoop_preserves_flowLevel]

theorem scanTag_preserves_flowLevel (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_flowLevel s.advance s.currentPos s_verb hv,
            advance_preserves_flowLevel]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_flowLevel, advance_preserves_flowLevel]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_flowLevel, advance_preserves_flowLevel]

theorem scanPlainScalar_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_simpleKey]
  exact collectPlainScalarLoop_preserves_simpleKey s "" "" _ _ _ _ result heq

theorem scanPlainScalar_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_simpleKeyStack]
  exact collectPlainScalarLoop_preserves_simpleKeyStack s "" "" _ _ _ _ result heq

/-! ### flowLevel preservation for scalar collector loops -/

theorem skipBlankLinesLoop_preserves_flowLevel (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_flowLevel s
        have h_cn := consumeNewline_preserves_flowLevel (skipSpaces s)
        rw [ih, h_cn, h_sp]

theorem foldQuotedNewlinesLoop_preserves_flowLevel (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.flowLevel = s.flowLevel := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_flowLevel s
        have h_cn := consumeNewline_preserves_flowLevel (skipSpaces s)
        rw [ih, h_cn, h_sp]

theorem foldQuotedNewlines_preserves_flowLevel (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.flowLevel = s.flowLevel := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_flowLevel s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_flowLevel (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_flowLevel (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_flowLevel (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  split at h <;> try contradiction
  · -- inFlow check branch
    split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
  · -- no inFlow check
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]

theorem collectHexDigitsLoop_preserves_flowLevel (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.flowLevel = s.flowLevel := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_flowLevel s
        rw [ih, h_adv]
      · rfl

theorem parseHexEscape_preserves_flowLevel (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.flowLevel = s.flowLevel := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_flowLevel s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]

theorem processEscape_preserves_flowLevel (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.flowLevel = s.flowLevel := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  repeat (split at h)
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_flowLevel s)
    | (have h_adv := advance_preserves_flowLevel s
       have h_hex := parseHexEscape_preserves_flowLevel s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )

theorem collectPlainScalarLoop_preserves_flowLevel (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.flowLevel = s.flowLevel := by
  intro result h
  induction fuel generalizing s content lastLine with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek = none
      injection h with h_eq; cases h_eq; rfl
    · -- peek = some c
      rename_i c
      split at h
      · -- collectPlainScalar_terminates? = some → state = s
        rename_i hterm
        injection h with h_eq; cases h_eq
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
      · -- collectPlainScalar_terminates? = none → continue
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk content_fold s_fold =>
              have h_fold := foldQuotedNewlines_preserves_flowLevel s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · -- recurse with content-length check
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ content_fold) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih s_fold (content ++ content_fold) "" h_loop, h_fold]
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- _handleBlockLineBreak = some → recurse
              rename_i content' s' hblk
              have hprop : s'.flowLevel = s.flowLevel := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipSpaces_preserves_flowLevel,
                    skipBlankLinesLoop_preserves_flowLevel, consumeNewline_preserves_flowLevel]
              split at h
              · injection h with h_eq; cases h_eq; rfl  -- '#' → state = s
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih _ _ _ h_loop, hprop]
                | error e => simp at h
        · split at h
          · -- isWhiteSpace c
            have h_adv := advance_preserves_flowLevel s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · -- regular content
            split at h
            · -- !isPlainSafe → terminate
              injection h with h_eq; cases h_eq; rfl
            · -- plainSafe → recurse
              simp only [] at h
              have h_adv := advance_preserves_flowLevel s
              rw [ih s.advance _ "" h, h_adv]

theorem collectDoubleQuotedLoop_preserves_flowLevel (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.flowLevel = s.flowLevel := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectDoubleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '"' case (closing quote)
      injection h with h_eq; cases h_eq
      exact advance_preserves_flowLevel s
    · -- some '\\' case (escape sequence)
      simp only [] at h
      split at h <;> try contradiction
      -- some c after backslash
      split at h
      · -- isLineBreak c (escaped line break)
        have h_cn := consumeNewline_preserves_flowLevel s.advance
        have h_sw := skipWhitespace_preserves_flowLevel (consumeNewline s.advance)
        have h_adv := advance_preserves_flowLevel s
        rw [ih _ _ h, h_sw, h_cn, h_adv]
      · -- regular escape sequence
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_flowLevel s.advance ch s_after_escape heq
          have h_adv := advance_preserves_flowLevel s
          rw [ih _ _ h, h_proc, h_adv]
    · -- some c case (regular character)
      split at h
      · -- isLineBreak c
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_flowLevel s s_fold folded heq
          split at h <;> try contradiction
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [ih s_fold (trimTrailingWS content ++ folded) h, h_fold]
      · -- regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_flowLevel s
        rw [ih _ _ h, h_adv]

theorem collectSingleQuotedLoop_preserves_flowLevel (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.flowLevel = s.flowLevel := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectSingleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · -- none case
      contradiction
    · -- some '\'' case
      simp only [] at h
      split at h
      · -- escaped quote: '\''\''
        have h_adv1 := advance_preserves_flowLevel s
        have h_adv2 := advance_preserves_flowLevel s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · -- closing quote
        injection h with h_eq; cases h_eq
        exact advance_preserves_flowLevel s
    · -- some c case (not quote)
      split at h
      · -- isLineBreak c = true
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_flowLevel s s_fold folded heq
          split at h <;> try contradiction  -- atDocumentStart check
          split at h <;> try contradiction  -- atDocumentEnd check
          split at h <;> try contradiction  -- col ≤ currentIndent check
          rw [ih s_fold _ h, h_fold]
      · -- isLineBreak c = false, regular character
        split at h <;> try contradiction  -- isNbJsonBool check
        have h_adv := advance_preserves_flowLevel s
        rw [ih s.advance _ h, h_adv]

/-! ### flowLevel preservation for block scalar sub-helpers -/

theorem consumeExactSpaces_preserves_flowLevel (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.flowLevel = s.flowLevel := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_flowLevel s
    · rfl

theorem parseBlockHeaderLoop_preserves_flowLevel (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_flowLevel s
    · rw [ih]; exact advance_preserves_flowLevel s
    · split
      · rw [ih]; exact advance_preserves_flowLevel s
      · rfl
    · rfl

theorem collectLineContentLoop_preserves_flowLevel (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_flowLevel s
    · rfl

theorem collectBlockScalarLoop_preserves_flowLevel (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.flowLevel = s.flowLevel := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_flowLevel s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_flowLevel, consumeExactSpaces_preserves_flowLevel]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_flowLevel,
                    collectLineContentLoop_preserves_flowLevel, consumeExactSpaces_preserves_flowLevel]
              · rw [ih, collectLineContentLoop_preserves_flowLevel, consumeExactSpaces_preserves_flowLevel]
            · rw [collectLineContentLoop_preserves_flowLevel, consumeExactSpaces_preserves_flowLevel]

theorem scanBlockScalarSkipComment_preserves_flowLevel (s : ScannerState) :
    (scanBlockScalarSkipComment s).flowLevel = s.flowLevel := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_flowLevel, advance_preserves_flowLevel]
      · rfl
    · -- peekBack? = none
      rfl
  · rfl

theorem scanBlockScalarConsumeNewline_preserves_flowLevel (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_flowLevel s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

theorem scanBlockScalarBody_preserves_flowLevel (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_fl : s_nl.flowLevel = s_orig.flowLevel)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.flowLevel = s_orig.flowLevel := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_flowLevel, collectBlockScalarLoop_preserves_flowLevel, h_fl]

theorem scanPlainScalar_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_flowLevel]
  exact collectPlainScalarLoop_preserves_flowLevel s "" "" _ _ _ _ result heq

theorem scanDoubleQuoted_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKey]
    have := collectDoubleQuotedLoop_preserves_simpleKey s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKey]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKey]
    have := collectDoubleQuotedLoop_preserves_simpleKey s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKey]

theorem scanDoubleQuoted_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKeyStack]
    have := collectDoubleQuotedLoop_preserves_simpleKeyStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKeyStack]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKeyStack]
    have := collectDoubleQuotedLoop_preserves_simpleKeyStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKeyStack]

theorem scanDoubleQuoted_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowLevel]
    have := collectDoubleQuotedLoop_preserves_flowLevel s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowLevel]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowLevel]
    have := collectDoubleQuotedLoop_preserves_flowLevel s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowLevel]

theorem scanSingleQuoted_preserves_simpleKey (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.simpleKey = s.simpleKey := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKey]
    have := collectSingleQuotedLoop_preserves_simpleKey s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKey]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKey]
    have := collectSingleQuotedLoop_preserves_simpleKey s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKey]

theorem scanSingleQuoted_preserves_simpleKeyStack (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKeyStack]
    have := collectSingleQuotedLoop_preserves_simpleKeyStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKeyStack]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_simpleKeyStack]
    have := collectSingleQuotedLoop_preserves_simpleKeyStack s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_simpleKeyStack]

theorem scanSingleQuoted_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowLevel]
    have := collectSingleQuotedLoop_preserves_flowLevel s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowLevel]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_flowLevel]
    have := collectSingleQuotedLoop_preserves_flowLevel s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_flowLevel]

theorem scanBlockScalar_preserves_flowLevel (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.flowLevel = s.flowLevel := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_flowLevel s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_flowLevel _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_flowLevel,
              skipWhitespace_preserves_flowLevel,
              parseBlockHeaderLoop_preserves_flowLevel,
              advance_preserves_flowLevel]) h

/-! ### Dispatch flowLevel/simpleKeyStack preservation -/

theorem dispatchStructural_preserves_flowLevel (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.flowLevel = s.flowLevel := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_preserves_flowLevel s
    | exact scanDocumentEnd_preserves_flowLevel _ _ (by assumption)
    | exact scanDirective_preserves_flowLevel _ _ (by assumption)
    | (simp_all [scanDocumentStart_preserves_flowLevel,
        scanDocumentEnd_preserves_flowLevel, scanDirective_preserves_flowLevel]; done)

theorem dispatchStructural_preserves_simpleKeyStack (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_preserves_simpleKeyStack s
    | exact scanDocumentEnd_preserves_simpleKeyStack _ _ (by assumption)
    | exact scanDirective_preserves_simpleKeyStack _ _ (by assumption)
    | (simp_all [scanDocumentStart_preserves_simpleKeyStack,
        scanDocumentEnd_preserves_simpleKeyStack, scanDirective_preserves_simpleKeyStack]; done)

theorem dispatchBlockIndicators_preserves_flowLevel (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.flowLevel = s.flowLevel := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanBlockEntry_preserves_flowLevel _ _ (by assumption)
    | exact scanKey_preserves_flowLevel _ _ (by assumption)
    | exact scanValue_preserves_flowLevel _ _ (by assumption)
    | (simp_all [scanBlockEntry_preserves_flowLevel,
        scanKey_preserves_flowLevel, scanValue_preserves_flowLevel]; done)

theorem dispatchBlockIndicators_preserves_simpleKeyStack (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanBlockEntry_preserves_simpleKeyStack _ _ (by assumption)
    | exact scanKey_preserves_simpleKeyStack _ _ (by assumption)
    | exact scanValue_preserves_simpleKeyStack _ _ (by assumption)
    | (simp_all [scanBlockEntry_preserves_simpleKeyStack,
        scanKey_preserves_simpleKeyStack, scanValue_preserves_simpleKeyStack]; done)

theorem dispatchContent_preserves_flowLevel (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.flowLevel = s.flowLevel := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_preserves_flowLevel s true s_a h_fn
  · split at h
    · -- '*': alias
      split at h
      · simp at h
      · generalize h_fn : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanAnchorOrAlias_preserves_flowLevel s false s_a h_fn
    · split at h
      · -- '!': tag
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_flowLevel s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_flowLevel _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_flowLevel _ _ (by assumption)
          | exact scanSingleQuoted_preserves_flowLevel _ _ (by assumption)
          | exact scanPlainScalar_preserves_flowLevel _ _ (by assumption)
          | (simp_all; done)

theorem dispatchContent_preserves_simpleKeyStack (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.simpleKeyStack = s.simpleKeyStack := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_fn
  · split at h
    · -- '*': alias
      split at h
      · simp at h
      · generalize h_fn : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanAnchorOrAlias_preserves_simpleKeyStack s false s_a h_fn
    · split at h
      · -- '!': tag
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact scanTag_preserves_simpleKeyStack s s_t h_fn
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        any_goals contradiction
        all_goals (try simp only [Except.ok.injEq] at *)
        all_goals (try contradiction)
        all_goals (try subst_vars)
        all_goals (try dsimp only [])
        all_goals first
          | exact scanBlockScalar_preserves_simpleKeyStack _ _ (by assumption)
          | exact scanDoubleQuoted_preserves_simpleKeyStack _ _ (by assumption)
          | exact scanSingleQuoted_preserves_simpleKeyStack _ _ (by assumption)
          | exact scanPlainScalar_preserves_simpleKeyStack _ _ (by assumption)
          | (simp_all; done)

-- Category 3: Flow open — simpleKey cleared, pushed onto stack

theorem scanFlowSequenceStart_simpleKey_cleared (s : ScannerState) :
    (scanFlowSequenceStart s).simpleKey.possible = false := by
  unfold scanFlowSequenceStart
  simp [advance_preserves_simpleKey, emit_preserves_simpleKey]

theorem scanFlowSequenceStart_stack_pushed (s : ScannerState) :
    (scanFlowSequenceStart s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
  unfold scanFlowSequenceStart
  simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]

theorem scanFlowMappingStart_simpleKey_cleared (s : ScannerState) :
    (scanFlowMappingStart s).simpleKey.possible = false := by
  unfold scanFlowMappingStart
  simp [advance_preserves_simpleKey, emit_preserves_simpleKey]

theorem scanFlowMappingStart_stack_pushed (s : ScannerState) :
    (scanFlowMappingStart s).simpleKeyStack = s.simpleKeyStack.push s.simpleKey := by
  unfold scanFlowMappingStart
  simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]

-- Category 4: Flow close — simpleKey restored from stack, stack popped

theorem scanFlowSequenceEnd_simpleKey_restored (s : ScannerState) :
    (scanFlowSequenceEnd s).simpleKey = s.simpleKeyStack.back?.getD {} := by
  unfold scanFlowSequenceEnd
  simp [emit_preserves_simpleKeyStack]

theorem scanFlowSequenceEnd_stack_popped (s : ScannerState) :
    (scanFlowSequenceEnd s).simpleKeyStack = s.simpleKeyStack.pop := by
  unfold scanFlowSequenceEnd
  simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]

theorem scanFlowMappingEnd_simpleKey_restored (s : ScannerState) :
    (scanFlowMappingEnd s).simpleKey = s.simpleKeyStack.back?.getD {} := by
  unfold scanFlowMappingEnd
  simp [emit_preserves_simpleKeyStack]

theorem scanFlowMappingEnd_stack_popped (s : ScannerState) :
    (scanFlowMappingEnd s).simpleKeyStack = s.simpleKeyStack.pop := by
  unfold scanFlowMappingEnd
  simp [advance_preserves_simpleKeyStack, emit_preserves_simpleKeyStack]

set_option maxHeartbeats 400000 in
/-- scanNextToken preserves existing token prefix below `n`.

For any index `i < n ≤ s.tokens.size`, tokens[i] remains unchanged,
provided `SimpleKeyAbove s n` holds (so `scanValuePrepare`'s `setIfInBounds`
never overwrites tokens below `n`). -/
theorem scanNextToken_preserves_prefix (s : ScannerState) (s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n)
    (i : Nat) (h_bound : i < n) :
    s'.tokens[i]'(by have := scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[i]'(by omega) := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · -- preprocess succeeded with some (s1, c)
      have h_pre_pref := ScanHelpers.preprocess_preserves_prefix s _ _ (by assumption) i (by omega)
      have h_pre_mono := ScanHelpers.preprocess_tokens_mono s _ _ (by assumption)
      -- simpleKey invariant for preprocessed state
      have h_sk_inv := preprocess_simpleKey_inv s _ _ (by assumption) n h_n h_inv.1
      -- allowDirectives doesn't change tokens or simpleKey
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScanHelpers.allowDir_ite_tokens
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      -- Now split on all dispatch cases
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | -- Structural dispatch
          (have h_d := ScanHelpers.dispatchStructural_preserves_prefix _ _ _ (by assumption) i (by omega);
           simp_all)
        | -- Flow dispatch
          (have h_d := ScanHelpers.dispatchFlowIndicators_preserves_prefix _ _ _ (by assumption) i
            (by simp only [ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | -- Block dispatch
          (have h_d := ScanHelpers.dispatchBlockIndicators_preserves_prefix _ _ _ (by assumption) n
            (by simp only [ScanHelpers.allowDir_ite_tokens]; omega)
            (by simp only [h_allow_sk]; exact h_sk_inv) i h_bound;
           simp only [ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | -- Content dispatch
          (have h_d := ScanHelpers.dispatchContent_preserves_prefix _ _ _ (by assumption) i
            (by simp only [ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (simp_all)

/-! ### Dispatch-level SimpleKeyAbove maintenance -/

theorem dispatchStructural_maintains_simpleKeyAbove (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (n : Nat) (_h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n) :
    SimpleKeyAbove s' n := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, ScanHelpers.bind_error_simp, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | -- scanDocumentStart: clears simpleKey, preserves stack
      exact SimpleKeyAbove_of_cleared_preserved _ s n
        (scanDocumentStart_clears_simpleKey s) (scanDocumentStart_preserves_simpleKeyStack s) h_inv
    | -- scanDocumentEnd: clears simpleKey, preserves stack
      (rename_i h_eq; exact SimpleKeyAbove_of_cleared_preserved _ s n
        (scanDocumentEnd_clears_simpleKey s _ h_eq)
        (scanDocumentEnd_preserves_simpleKeyStack s _ h_eq) h_inv)
    | -- scanDirective: preserves both
      (rename_i h_eq; exact SimpleKeyAbove_of_preserved _ s n
        (scanDirective_preserves_simpleKey s _ h_eq)
        (scanDirective_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

theorem dispatchFlowIndicators_maintains_simpleKeyAbove (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (n : Nat) (_h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n) :
    SimpleKeyAbove s' n := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, ScanHelpers.bind_error_simp, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | -- scanFlowSequenceStart: flow open
      exact SimpleKeyAbove_of_flow_open _ s n
        (scanFlowSequenceStart_simpleKey_cleared s)
        (scanFlowSequenceStart_stack_pushed s) h_inv
    | -- scanFlowSequenceEnd: flow close
      (by_cases h_size : s.simpleKeyStack.size > 0
       · exact SimpleKeyAbove_of_flow_close _ s n
           (scanFlowSequenceEnd_simpleKey_restored s)
           (scanFlowSequenceEnd_stack_popped s) h_inv h_size
       · -- stack empty: restored key has possible=false, popped stack stays empty
         have h_empty : s.simpleKeyStack.size = 0 := by omega
         have h_sk := scanFlowSequenceEnd_simpleKey_restored s
         have h_st := scanFlowSequenceEnd_stack_popped s
         constructor
         · intro hp; rw [h_sk] at hp
           simp [Array.back?, h_empty] at hp
         · intro j hj hp; rw [h_st] at hj
           simp [Array.size_pop, h_empty] at hj)
    | -- scanFlowMappingStart: flow open
      exact SimpleKeyAbove_of_flow_open _ s n
        (scanFlowMappingStart_simpleKey_cleared s)
        (scanFlowMappingStart_stack_pushed s) h_inv
    | -- scanFlowMappingEnd: flow close
      (by_cases h_size : s.simpleKeyStack.size > 0
       · exact SimpleKeyAbove_of_flow_close _ s n
           (scanFlowMappingEnd_simpleKey_restored s)
           (scanFlowMappingEnd_stack_popped s) h_inv h_size
       · have h_empty : s.simpleKeyStack.size = 0 := by omega
         have h_sk := scanFlowMappingEnd_simpleKey_restored s
         have h_st := scanFlowMappingEnd_stack_popped s
         constructor
         · intro hp; rw [h_sk] at hp
           simp [Array.back?, h_empty] at hp
         · intro j hj hp; rw [h_st] at hj
           simp [Array.size_pop, h_empty] at hj)
    | -- scanFlowEntry: preserves both
      (rename_i h_eq; exact SimpleKeyAbove_of_preserved _ s n
        (scanFlowEntry_preserves_simpleKey s _ h_eq)
        (scanFlowEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

theorem dispatchBlockIndicators_maintains_simpleKeyAbove (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (n : Nat) (_h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n) :
    SimpleKeyAbove s' n := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | -- scanBlockEntry: preserves both
      (rename_i h_eq; exact SimpleKeyAbove_of_preserved _ s n
        (scanBlockEntry_preserves_simpleKey s _ h_eq)
        (scanBlockEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | -- scanKey: clears simpleKey, preserves stack
      (rename_i h_eq; exact SimpleKeyAbove_of_cleared_preserved _ s n
        (scanKey_clears_simpleKey s _ h_eq)
        (scanKey_preserves_simpleKeyStack s _ h_eq) h_inv)
    | -- scanValue: clears simpleKey, preserves stack
      (rename_i h_eq; exact SimpleKeyAbove_of_cleared_preserved _ s n
        (scanValue_clears_simpleKey s _ h_eq)
        (scanValue_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

theorem dispatchContent_maintains_simpleKeyAbove (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (n : Nat)
    (_h_n : n ≤ s.tokens.size)
    (h_inv : SimpleKeyAbove s n) :
    SimpleKeyAbove s' n := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  -- Handle anchor/alias/tag explicitly (need generalize for ok-equation)
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact SimpleKeyAbove_of_preserved _ _ n rfl rfl
        (SimpleKeyAbove_of_preserved _ s n
          (scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
          (scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch) h_inv)
  · split at h
    · -- '*': alias
      split at h
      · contradiction
      · generalize h_anch : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAbove_of_preserved _ s n
            (scanAnchorOrAlias_preserves_simpleKey s false s_a h_anch)
            (scanAnchorOrAlias_preserves_simpleKeyStack s false s_a h_anch) h_inv
    · split at h
      · -- '!': tag
        generalize h_tag : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAbove_of_preserved _ s n
            (scanTag_preserves_simpleKey s s_t h_tag)
            (scanTag_preserves_simpleKeyStack s s_t h_tag) h_inv
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        all_goals (try contradiction)
        all_goals (try (simp only [Except.ok.injEq] at h; subst h))
        all_goals (
          first
    | -- Monadic functions that clear simpleKey
      (rename_i h_eq; exact SimpleKeyAbove_of_cleared_preserved _ s n
        (scanBlockScalar_clears_simpleKey s _ h_eq)
        (scanBlockScalar_preserves_simpleKeyStack s _ h_eq) h_inv)
    | -- scanPlainScalar: preserves both
      (rename_i h_eq; exact SimpleKeyAbove_of_preserved _ s n
        (scanPlainScalar_preserves_simpleKey s _ h_eq)
        (scanPlainScalar_preserves_simpleKeyStack s _ h_eq) h_inv)
    | -- endLine update (isTrue): possible preserved, tokenIndex preserved, stack preserved
      (rename_i h_eq_dq _
       -- Try scanDoubleQuoted first
       first
       | (have h_sk := scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAbove_of_endLine_update _ s n (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv)
       | (have h_sk := scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAbove_of_endLine_update _ s n (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv))
    | -- endLine update (isFalse): unchanged
      (rename_i h_eq_dq _
       first
       | (have h_sk := scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAbove_of_preserved _ s n h_sk h_st h_inv)
       | (have h_sk := scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAbove_of_preserved _ s n h_sk h_st h_inv))
    | (simp_all; done))

/-- scanNextToken maintains the `SimpleKeyAbove` invariant.

After `scanNextToken`, all simple keys (current and stacked) still have
`tokenIndex ≥ n`. This follows from:
- `saveSimpleKey` sets `tokenIndex = st.tokens.size ≥ n` (fresh key) or
  leaves key unchanged / clears it.
- Dispatch functions either don't touch simpleKey, clear it (possible = false),
  push/pop from the stack (preserving the invariant), or restore from stack
  (which was saved when the invariant held). -/
theorem scanNextToken_maintains_simpleKeyAbove (s : ScannerState) (s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n) :
    SimpleKeyAbove s' n := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · -- preprocess succeeded with some (s1, c)
      -- Invariant through preprocess
      have h_pre_inv := preprocess_maintains_simpleKeyAbove s _ _ (by assumption) n h_n h_inv
      have h_pre_mono := ScanHelpers.preprocess_tokens_mono s _ _ (by assumption)
      -- allowDirectives doesn't change simpleKey or simpleKeyStack
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
        else st).tokens = st.tokens := ScanHelpers.allowDir_ite_tokens
      -- Helper: allowDirectives transform preserves SimpleKeyAbove
      rename_i s1 c1 heq_pre
      have h_allow_inv : SimpleKeyAbove
          (if s1.allowDirectives then
            { s1 with allowDirectives := false, documentEverStarted := true }
          else s1) n :=
        SimpleKeyAbove_of_preserved _ s1 n (h_allow_sk s1) (h_allow_stack s1) h_pre_inv
      -- Now split on all dispatch cases
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | -- Structural dispatch
          (have h_d := dispatchStructural_maintains_simpleKeyAbove _ _ _ (by assumption) n
            (by omega) h_pre_inv;
           exact h_d)
        | -- Flow/Block/Content dispatch
          (have h_d := dispatchFlowIndicators_maintains_simpleKeyAbove _ _ _ (by assumption) n
            (by simp only [ScanHelpers.allowDir_ite_tokens]; omega) h_allow_inv;
           exact h_d)
        | (have h_d := dispatchBlockIndicators_maintains_simpleKeyAbove _ _ _ (by assumption) n
            (by simp only [ScanHelpers.allowDir_ite_tokens]; omega) h_allow_inv;
           exact h_d)
        | (have h_d := dispatchContent_maintains_simpleKeyAbove _ _ _ (by assumption) n
            (by simp only [ScanHelpers.allowDir_ite_tokens]; omega) h_allow_inv;
           exact h_d)
        | (simp_all)

/-- scanLoop preserves existing tokens (prefix preservation below `n`).

When `scanLoop` succeeds, tokens below index `n` remain unchanged, provided
the `SimpleKeyAbove s n` invariant holds at the loop entry and is maintained
by each `scanNextToken` step.

**Proof strategy**:
- Base case (fuel = 0): scanLoop returns error, contradiction
- Inductive case: split on scanNextToken result
  - If none: uses unwindIndents + emit (both proven to preserve prefix)
  - If some s': uses IH + scanNextToken_preserves_prefix + maintains_simpleKeyAbove -/
theorem scanLoop_preserves_tokens (s : ScannerState) (fuel : Nat) (tokens : Array (Positioned YamlToken))
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n)
    (h : scanLoop s fuel = .ok tokens) :
    ∀ (i : Nat) (h_bound : i < n),
      ∃ (h_bound' : i < tokens.size), tokens[i] = s.tokens[i]'(by omega) := by
  induction fuel generalizing s tokens with
  | zero =>
    -- Base case: fuel = 0, scanLoop returns error
    intro i h_bound
    unfold scanLoop at h
    contradiction
  | succ fuel' IH =>
    intro i h_bound
    -- Inductive case
    unfold scanLoop at h
    split at h
    · -- scanNextToken = error: contradiction
      contradiction
    · -- scanNextToken = none: success path
      -- Handle if-then-else conditions
      split at h <;> try contradiction
      split at h <;> try contradiction
      -- Now h : .ok ((unwindIndents s (-1)).emit .streamEnd).tokens = .ok tokens
      injection h with h_eq
      let s_unwind := unwindIndents s (-1)
      have h_unwind_mono : s_unwind.tokens.size ≥ s.tokens.size := unwindIndents_adds_tokens s (-1)
      have h_emit_size : (s_unwind.emit .streamEnd).tokens.size = s_unwind.tokens.size + 1 :=
        emit_tokens_size s_unwind .streamEnd
      have h_i_lt_s : i < s.tokens.size := by omega
      have h_i_lt_unwind : i < s_unwind.tokens.size := by omega
      have h_i_lt_emitted : i < (s_unwind.emit .streamEnd).tokens.size := by
        rw [h_emit_size]; omega
      have h_i_lt_tokens : i < tokens.size := by
        rw [← h_eq]; exact h_i_lt_emitted
      exists h_i_lt_tokens
      cases h_eq
      calc (s_unwind.emit .streamEnd).tokens[i]
          = s_unwind.tokens[i]'h_i_lt_unwind :=
            emit_preserves_tokens_at s_unwind .streamEnd i h_i_lt_unwind
        _ = s.tokens[i] :=
            unwindIndents_preserves_prefix s (-1) i h_i_lt_s
    · -- scanNextToken = some s': recursive case
      rename_i s' h_next
      -- h : scanLoop s' fuel' = .ok tokens
      -- h_next : scanNextToken s = .ok (some s')
      have h_s_mono := scanNextToken_adds_tokens s s' h_next
      have h_n' : n ≤ s'.tokens.size := by omega
      have h_inv' := scanNextToken_maintains_simpleKeyAbove s s' h_next n h_n h_inv
      have ⟨h_i_lt_tokens, h_eq_s'⟩ := IH s' tokens h_n' h_inv' h i h_bound
      have h_prefix := scanNextToken_preserves_prefix s s' h_next n h_n h_inv i h_bound
      exact ⟨h_i_lt_tokens, h_eq_s'.trans h_prefix⟩

/-- scanLoop preserves or increases token count.

When `scanLoop` succeeds, the resulting tokens have at least as many tokens
as the input state, plus the streamEnd token (so at least +1).

Proved by structural induction on fuel. Base case (fuel = 0) is contradiction.
Success path (scanNextToken = none) uses unwindIndents_adds_tokens + emit_tokens_size.
Recursive path uses IH + scanNextToken_adds_tokens. -/
theorem scanLoop_increases_tokens (s : ScannerState) (fuel : Nat) (tokens : Array (Positioned YamlToken)) :
    scanLoop s fuel = .ok tokens →
    tokens.size ≥ s.tokens.size + 1 := by
  intro h
  induction fuel generalizing s with
  | zero => unfold scanLoop at h; contradiction
  | succ fuel' IH =>
    unfold scanLoop at h
    split at h
    · contradiction
    · -- scanNextToken = none: final emit
      split at h <;> try contradiction
      split at h <;> try contradiction
      injection h with h_eq; rw [← h_eq]
      have h1 := unwindIndents_adds_tokens s (-1)
      have h2 := emit_tokens_size (unwindIndents s (-1)) .streamEnd
      rw [h2]; omega
    · -- scanNextToken = some s': recursive
      rename_i s' h_snt
      have h_ih := IH s' h
      have h_adds := scanNextToken_adds_tokens s s' h_snt
      omega

/-! ## §1  Token Envelope Properties

The scanner's `scan` function (Scanner.lean:1968-1989) emits `streamStart`
as its first action (line 1970) and `streamEnd` as its final action (line 1987)
before returning the token array.
-/

/--
The `scan` function produces at least 2 tokens.

**Proof strategy**: The scan function:
1. Emits streamStart (Scanner.lean:1970)
2. Loops through scanNextToken
3. Emits streamEnd (Scanner.lean:1987) before returning

Since `emit` appends exactly one token each time, we have at least 2.

**After refactoring to structural recursion**: This proof becomes tractable
via induction on fuel. The key facts are:
- mk' produces 0 tokens (mk'_tokens_empty)
- emit adds 1 token (emit_tokens_size)
- scan does: mk' → emit streamStart → scanLoop → emit streamEnd
- Therefore: 0 + 1 (streamStart) + 1 (streamEnd) = at least 2
-/
theorem scan_produces_at_least_two (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) : tokens.size ≥ 2 := by
  unfold scan at h
  simp only [] at h
  -- h : scanLoop (match ... BOM ...) (fuel*4) = .ok tokens
  have h_loop := scanLoop_increases_tokens _ _ tokens h
  -- h_loop : tokens.size ≥ (match ...).tokens.size + 1
  have h_init_size : ((ScannerState.mk' input).emit .streamStart).tokens.size = 1 := by
    rw [emit_tokens_size, mk'_tokens_empty]; simp
  -- Split on h_loop to resolve the match expression
  split at h_loop
  · rw [advance_preserves_tokens, h_init_size] at h_loop; omega
  · rw [h_init_size] at h_loop; omega

/--
The first token produced by `scan` is always `streamStart`.

**Proof strategy**: Scanner.lean:1970 shows `s := s.emit .streamStart` as the
first token emission. The subsequent loop only appends tokens (via `emit`), never
modifying or removing earlier tokens. Array indexing at position 0 thus retrieves
this initial streamStart token.

**Note**: Complete proof requires tracking array invariants through the loop.
Empirically validated on all test inputs (§4).
-/
theorem scan_first_is_streamStart (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) (h_size : tokens.size > 0) :
    (tokens[0]'(by omega)).val = YamlToken.streamStart := by
  unfold scan at h
  -- After unfolding scan, we have:
  -- let s := (ScannerState.mk' input).emit .streamStart
  -- let s := match s.peek? with | some '\uFEFF' => s.advance | _ => s
  -- scanLoop s fuel

  -- Step 1: After emit .streamStart, token[0] is streamStart
  have h_init_size : ((ScannerState.mk' input).emit .streamStart).tokens.size = 1 := by
    rw [emit_tokens_size, mk'_tokens_empty]
    simp

  have h_init_token : (((ScannerState.mk' input).emit .streamStart).tokens[0]'(by omega : 0 < 1)).val =
    YamlToken.streamStart := by
    unfold ScannerState.emit
    simp [mk'_tokens_empty]

  -- Step 2: BOM handling preserves tokens (advance_preserves_tokens)
  have h_bom_preserves : ∀ s : ScannerState,
    (match s.peek? with | some '\uFEFF' => s.advance | _ => s).tokens = s.tokens := by
    intro s
    split <;> try rfl
    exact advance_preserves_tokens s

  -- Step 3: scanLoop preserves existing tokens
  -- The state after BOM handling
  let s_after_bom := match ((ScannerState.mk' input).emit .streamStart).peek? with
    | some '\uFEFF' => ((ScannerState.mk' input).emit .streamStart).advance
    | _ => (ScannerState.mk' input).emit .streamStart

  -- BOM handling preserves tokens
  have h_bom_eq : s_after_bom.tokens = ((ScannerState.mk' input).emit .streamStart).tokens :=
    h_bom_preserves _

  -- So token[0] is still streamStart after BOM handling
  have h_after_bom_size : s_after_bom.tokens.size = 1 := by
    rw [h_bom_eq, h_init_size]

  have h_0_lt_after_bom : 0 < s_after_bom.tokens.size := by
    rw [h_after_bom_size]; omega

  have h_after_bom_token : (s_after_bom.tokens[0]'h_0_lt_after_bom).val = YamlToken.streamStart := by
    -- s_after_bom.tokens = ((ScannerState.mk' input).emit .streamStart).tokens
    simp only [h_bom_eq]
    grind

  -- Step 4: scanLoop preserves token[0]
  -- The SimpleKeyAbove invariant holds vacuously: simpleKey.possible = false
  -- and simpleKeyStack is empty in the initial state.
  have h_inv : SimpleKeyAbove s_after_bom 1 := by
    unfold SimpleKeyAbove
    constructor
    · -- simpleKey.possible = false since advance/emit/mk' don't change it
      intro h_poss
      exfalso
      revert h_poss; show ¬ _
      dsimp only [s_after_bom, ScannerState.advance, ScannerState.emit, ScannerState.mk']
      split <;> (try split) <;> (try split) <;> (try split) <;> simp
    · -- simpleKeyStack is empty
      intro j h_j
      exfalso
      revert h_j; show ¬ _
      dsimp only [s_after_bom, ScannerState.advance, ScannerState.emit, ScannerState.mk']
      split <;> (try split) <;> (try split) <;> (try split) <;> simp
  -- Apply scanLoop_preserves_tokens with n = 1
  have ⟨h_0_lt_tokens, h_preserved⟩ :=
    scanLoop_preserves_tokens s_after_bom _ tokens 1
      (by omega) h_inv h 0 (by omega)

  -- Combine: tokens[0].val = s_after_bom.tokens[0].val = streamStart
  simp only [h_preserved, h_after_bom_token]

/--
The last token produced by `scan` is always `streamEnd`.

**Proof strategy**: Scanner.lean:1987 shows `let final := final.emit .streamEnd`
followed immediately by `return final.tokens` (line 1988). The streamEnd token
is the last modification before returning, so `tokens[size-1]` is streamEnd.

**Note**: Complete proof requires showing no tokens are appended after streamEnd.
Empirically validated on all test inputs (§4).
-/
theorem scan_last_is_streamEnd (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) (h_size : tokens.size > 0) :
    (tokens[tokens.size - 1]'(by omega)).val = YamlToken.streamEnd := by
  unfold scan at h
  -- Use scanLoop_success_emits_streamEnd to get the structure
  have ⟨s', h_tokens⟩ := scanLoop_success_emits_streamEnd _ _ _ h

  -- Subst tokens with its definition
  subst h_tokens

  -- Now goal is: ((s'.emit .streamEnd).tokens)[...].val = .streamEnd
  unfold ScannerState.emit
  simp only [Array.size_push]

  -- After emit, size is s'.tokens.size + 1
  -- Last index is s'.tokens.size + 1 - 1 = s'.tokens.size
  have h_idx : s'.tokens.size + 1 - 1 = s'.tokens.size := by omega

  -- Array is s'.tokens.push {pos := ..., val := .streamEnd}
  -- Element at index s'.tokens.size is the pushed element
  simp [Array.getElem_push, h_idx]

/-! ## §2  Position Monotonicity

Token positions (offsets) are monotonically non-decreasing throughout the
token array. This follows from two properties:

1. `emit` appends tokens without reordering (structural)
2. Scanner operations either preserve offset or increase it (never decrease)
-/

/-- Helper: array access is equal when indices are equal (regardless of proof terms). -/
theorem Array.getElem_congr {α : Type} {arr : Array α} {i j : Nat}
    (hi : i < arr.size) (hj : j < arr.size) (heq : i = j) :
    arr[i]'hi = arr[j]'hj := by subst heq; rfl

theorem emit_preserves_position_order (s : ScannerState)
    (h_ordered : ∀ (i j : Fin s.tokens.size), i.val < j.val →
                 (s.tokens[i]).pos.offset ≤ (s.tokens[j]).pos.offset)
    (tok : YamlToken)
    (h_nonzero : s.tokens.size > 0)
    (h_pos : s.offset ≥ (s.tokens[s.tokens.size - 1]'(by omega)).pos.offset) :
    ∀ (i j : Fin (s.emit tok).tokens.size), i.val < j.val →
      ((s.emit tok).tokens[i]).pos.offset ≤ ((s.emit tok).tokens[j]).pos.offset := by
  intro i j hij
  show ((s.emit tok).tokens[i.val]'i.isLt).pos.offset ≤
       ((s.emit tok).tokens[j.val]'j.isLt).pos.offset
  unfold ScannerState.emit
  simp only [Array.getElem_push]
  split <;> rename_i hi_lt
  · -- i.val < s.tokens.size (in original array)
    split <;> rename_i hj_lt
    · -- both in original
      exact h_ordered ⟨i.val, hi_lt⟩ ⟨j.val, hj_lt⟩ hij
    · -- i in original, j is pushed element
      simp only [ScannerState.currentPos]
      suffices h : (s.tokens[i.val]'hi_lt).pos.offset ≤ s.offset from h
      calc (s.tokens[i.val]'hi_lt).pos.offset
          ≤ (s.tokens[s.tokens.size - 1]'(by omega)).pos.offset := by
            by_cases h_eq : i.val = s.tokens.size - 1
            · have := Array.getElem_congr hi_lt (by omega : s.tokens.size - 1 < s.tokens.size) h_eq
              rw [this]; omega
            · have h_lt : i.val < s.tokens.size - 1 := by
                have := h_nonzero; have := hi_lt; have := h_eq; omega
              exact h_ordered ⟨i.val, hi_lt⟩ ⟨s.tokens.size - 1, by omega⟩ h_lt
        _ ≤ s.offset := h_pos
  · -- i.val ≥ s.tokens.size
    have : i.val < s.tokens.size + 1 := by
      have := i.isLt; simp [ScannerState.emit, Array.size_push] at this; exact this
    split <;> rename_i hj_lt
    · omega
    · have : j.val < s.tokens.size + 1 := by
        have := j.isLt; simp [ScannerState.emit, Array.size_push] at this; exact this
      omega

/--
The `advance` operation never decreases the offset.

This is a direct consequence of string position advancement: moving forward
in a UTF-8 string increases the byte offset by at least 1.

**Proof**: Directly applies `advance_offset_lt` from ScannerProgress.lean.
-/
theorem advance_increases_offset (s : ScannerState) (h : s.hasMore) :
    s.advance.offset > s.offset := by
  unfold ScannerState.hasMore at h
  simp only [decide_eq_true_eq] at h
  exact ScannerProgress.advance_offset_lt s h

/--
The scanner maintains position monotonicity throughout its operation.

**Proof architecture**:
1. Define `ScanInv s` = tokens ordered ∧ all token offsets ≤ s.offset
2. Prove `ScanInv` preserved by `emit`, `advance`, field updates, `unwindIndents`
3. Express `scanNextToken` preservation as an axiom (empirically validated by 869 tests)
4. Prove `scanLoop` ordering via induction on fuel
5. Compose: initial state satisfies `ScanInv`, `scanLoop` preserves it

**Key insight**: Within each `scanNextToken` iteration, ALL newly pushed tokens
have the same offset (the post-`skipToContent` offset P₀). Since P₀ ≥ s.offset ≥
all existing token offsets, ordering is maintained. `setIfInBounds` (for simple key
resolution) only overwrites placeholders with the same offset they were created at.
-/

-- Compound scanner invariant: tokens ordered and all bounded by current offset.
-- Defined via helper to avoid dependent-type issues when tokens/offset are rewritten.
def ScanInv' (tokens : Array (Positioned YamlToken)) (offset : Nat) : Prop :=
  (∀ i j : Fin tokens.size, i.val < j.val →
    tokens[i].pos.offset ≤ tokens[j].pos.offset) ∧
  (∀ i : Fin tokens.size, tokens[i].pos.offset ≤ offset)

def ScanInv (s : ScannerState) : Prop := ScanInv' s.tokens s.offset

-- emit preserves ScanInv: new token at s.offset, which is ≥ all existing.
theorem emit_preserves_ScanInv (s : ScannerState) (tok : YamlToken)
    (h : ScanInv s) : ScanInv (s.emit tok) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInv ScanInv'
  have h_off : (s.emit tok).offset = s.offset := ScannerProgress.emit_offset s tok
  rw [h_off]
  constructor
  · -- Ordering: delegate to emit_preserves_position_order or trivial
    by_cases h_sz : s.tokens.size > 0
    · have h_pos : s.offset ≥ (s.tokens[s.tokens.size - 1]'(by omega)).pos.offset :=
        h_bnd ⟨s.tokens.size - 1, by omega⟩
      exact emit_preserves_position_order s h_ord tok h_sz h_pos
    · have h0 : s.tokens.size = 0 := by omega
      intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      have : (s.emit tok).tokens.size = 1 := by
        simp [ScannerState.emit, Array.size_push, h0]
      omega
  · -- Bounded: all tokens ≤ s.offset
    intro ⟨i, hi⟩
    have h_sz : i < s.tokens.size ∨ i = s.tokens.size := by
      have := hi; simp [ScannerState.emit, Array.size_push] at this; omega
    rcases h_sz with h_lt | h_eq
    · -- Old token: use emit_preserves_tokens_at
      show ((s.emit tok).tokens[i]'hi).pos.offset ≤ s.offset
      rw [emit_preserves_tokens_at s tok i h_lt]
      exact h_bnd ⟨i, h_lt⟩
    · subst h_eq
      show ((s.emit tok).tokens[s.tokens.size]'hi).pos.offset ≤ s.offset
      unfold ScannerState.emit
      simp only [Array.getElem_push, dif_neg (by omega : ¬ s.tokens.size < s.tokens.size)]
      simp [ScannerState.currentPos]

-- advance preserves ScanInv: offset increases, tokens unchanged.
theorem advance_preserves_ScanInv (s : ScannerState) (h : ScanInv s) :
    ScanInv s.advance := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInv ScanInv'
  rw [advance_preserves_tokens s]
  constructor
  · exact h_ord
  · intro ⟨i, hi⟩
    exact Nat.le_trans (h_bnd ⟨i, hi⟩) (ScannerProgress.advance_offset_ge s)

-- Field updates (not touching tokens/offset) preserve ScanInv.
theorem field_update_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_tok : s'.tokens = s.tokens) (h_off : s'.offset = s.offset) :
    ScanInv s' := by
  unfold ScanInv ScanInv'; rw [h_tok, h_off]; exact h

-- Field updates that only increase offset preserve ScanInv.
theorem offset_ge_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_tok : s'.tokens = s.tokens) (h_off : s'.offset ≥ s.offset) :
    ScanInv s' := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInv ScanInv'; rw [h_tok]
  exact ⟨h_ord, fun ⟨i, hi⟩ => Nat.le_trans (h_bnd ⟨i, hi⟩) h_off⟩

-- unwindIndentsLoop preserves ScanInv (emits blockEnd at current offset).
theorem unwindIndentsLoop_preserves_ScanInv (s : ScannerState) (col : Int) (fuel : Nat)
    (h : ScanInv s) : ScanInv (unwindIndentsLoop s col fuel) := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; exact h
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · -- Condition true: emit blockEnd, pop indents, recurse
      have h_emit : ScanInv (s.emit .blockEnd) := emit_preserves_ScanInv s .blockEnd h
      have h_pop : ScanInv ({ s.emit .blockEnd with
          indents := (s.emit .blockEnd).indents.pop }) :=
        field_update_preserves_ScanInv _ _ h_emit rfl rfl
      exact ih _ h_pop
    · exact h

-- unwindIndents preserves ScanInv.
theorem unwindIndents_preserves_ScanInv (s : ScannerState) (col : Int)
    (h : ScanInv s) : ScanInv (unwindIndents s col) := by
  unfold unwindIndents
  exact unwindIndentsLoop_preserves_ScanInv s col s.indents.size h

/-!
### Phase 1: Primitive ScanInv lemmas

Building blocks for the full `scanNextToken_preserves_ScanInv` proof.
-/

-- emitAt preserves ScanInv when the emitted position is ≤ offset and ≥ all existing tokens.
theorem emitAt_preserves_ScanInv (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (h : ScanInv s) (h_pos : pos.offset ≤ s.offset)
    (h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ pos.offset) :
    ScanInv (s.emitAt pos tok) := by
  obtain ⟨h_ord, h_bnd⟩ := h
  unfold ScanInv ScanInv'
  have h_off : (s.emitAt pos tok).offset = s.offset := rfl
  rw [h_off]
  constructor
  · -- Ordering: all existing ≤ pos.offset, and the new token is at pos.offset
    intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    show ((s.emitAt pos tok).tokens[i]'hi).pos.offset ≤
         ((s.emitAt pos tok).tokens[j]'hj).pos.offset
    unfold ScannerState.emitAt
    simp only [Array.getElem_push]
    split <;> rename_i hi_lt
    · -- i in original array
      split <;> rename_i hj_lt
      · -- j in original: use h_ord
        exact h_ord ⟨i, hi_lt⟩ ⟨j, hj_lt⟩ hij
      · -- j is new element at pos.offset
        exact h_ge ⟨i, hi_lt⟩
    · -- i is new element (i ≥ s.tokens.size)
      have hij' : i < j := hij  -- extract raw Nat inequality from Fin
      have hi_sz : i < s.tokens.size + 1 := by
        have := hi; simp [ScannerState.emitAt, Array.size_push] at this; exact this
      split <;> rename_i hj_lt
      · omega -- impossible: i ≥ size but j < size and i < j
      · have hj_sz : j < s.tokens.size + 1 := by
          have := hj; simp [ScannerState.emitAt, Array.size_push] at this; exact this
        omega -- i = j = s.tokens.size contradicts i < j
  · -- Bounded: all token offsets ≤ s.offset
    intro ⟨i, hi⟩
    show ((s.emitAt pos tok).tokens[i]'hi).pos.offset ≤ s.offset
    have h_sz : i < s.tokens.size ∨ i = s.tokens.size := by
      have := hi; simp [ScannerState.emitAt, Array.size_push] at this; omega
    rcases h_sz with h_lt | h_eq
    · -- Old token: use getElem_push with i < s.tokens.size
      unfold ScannerState.emitAt
      simp only [Array.getElem_push, show i < s.tokens.size from h_lt, dite_true]
      exact h_bnd ⟨i, h_lt⟩
    · subst h_eq
      unfold ScannerState.emitAt
      simp only [Array.getElem_push, dif_neg (by omega : ¬ s.tokens.size < s.tokens.size)]
      exact h_pos

-- Simplified emitAt_preserves_ScanInv: when pos.offset = s.offset (common case).
theorem emitAt_preserves_ScanInv_eq (s : ScannerState) (pos : YamlPos) (tok : YamlToken)
    (h : ScanInv s) (h_pos : pos.offset = s.offset) :
    ScanInv (s.emitAt pos tok) := by
  apply emitAt_preserves_ScanInv s pos tok h (by omega)
  intro ⟨i, hi⟩
  exact Nat.le_of_lt_succ (by rw [h_pos]; exact Nat.lt_succ_of_le (h.2 ⟨i, hi⟩))

-- saveSimpleKey preserves ScanInv.
--
-- **Initiative 3 / J.2 step 5 cutover**: the simpleKeyAllowed branch
-- no longer pushes placeholders (those moved to the `pendingKeys`
-- side-channel, which doesn't enter ScanInv).  The proof reduces to
-- `field_update_preserves_ScanInv` since `tokens` and `offset` are
-- both unchanged.
theorem saveSimpleKey_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · exact h                                          -- inFlow && explicitKeyLine → identity
  · split
    · exact field_update_preserves_ScanInv _ _ h rfl rfl  -- simpleKeyAllowed: pendingKeys/simpleKey only
    · exact h                                        -- not allowed → identity

-- setIfInBounds at index idx preserves ScanInv' when the replacement has
-- the same offset as the original element.
theorem setIfInBounds_preserves_ScanInv' (tokens : Array (Positioned YamlToken))
    (offset : Nat) (idx : Nat) (v : Positioned YamlToken)
    (h : ScanInv' tokens offset)
    (h_idx : idx < tokens.size)
    (h_off : v.pos.offset = tokens[idx].pos.offset) :
    ScanInv' (tokens.setIfInBounds idx v) offset := by
  obtain ⟨h_ord, h_bnd⟩ := h
  have h_sz : (tokens.setIfInBounds idx v).size = tokens.size := Array.size_setIfInBounds
  -- Helper: rewrite Fin-indexed access on setIfInBounds array to if-then-else
  have getElem_helper : ∀ (k : Nat) (hk : k < (tokens.setIfInBounds idx v).size),
      (tokens.setIfInBounds idx v)[k]'hk =
        if idx = k then v else tokens[k]'(by rw [h_sz] at hk; exact hk) :=
    fun k hk => Array.getElem_setIfInBounds (by rw [h_sz] at hk; exact hk)
  unfold ScanInv'
  constructor
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    show ((tokens.setIfInBounds idx v)[i]'hi).pos.offset ≤
         ((tokens.setIfInBounds idx v)[j]'hj).pos.offset
    rw [getElem_helper i hi, getElem_helper j hj]
    have hi' : i < tokens.size := by rw [h_sz] at hi; exact hi
    have hj' : j < tokens.size := by rw [h_sz] at hj; exact hj
    split <;> rename_i h_eq_i
    · split <;> rename_i h_eq_j
      · omega
      · rw [h_off]; subst h_eq_i; exact h_ord ⟨idx, h_idx⟩ ⟨j, hj'⟩ hij
    · split <;> rename_i h_eq_j
      · rw [h_off]; subst h_eq_j; exact h_ord ⟨i, hi'⟩ ⟨idx, h_idx⟩ hij
      · exact h_ord ⟨i, hi'⟩ ⟨j, hj'⟩ hij
  · intro ⟨i, hi⟩
    show ((tokens.setIfInBounds idx v)[i]'hi).pos.offset ≤ offset
    rw [getElem_helper i hi]
    have hi' : i < tokens.size := by rw [h_sz] at hi; exact hi
    split
    · rw [h_off]; exact h_bnd ⟨idx, h_idx⟩
    · exact h_bnd ⟨i, hi'⟩

-- Two consecutive setIfInBounds preserve ScanInv' when both replacements
-- have the same offsets as the originals.
theorem setIfInBounds_twice_preserves_ScanInv' (tokens : Array (Positioned YamlToken))
    (offset : Nat) (idx1 idx2 : Nat) (v1 v2 : Positioned YamlToken)
    (h : ScanInv' tokens offset)
    (h_idx1 : idx1 < tokens.size)
    (h_idx2 : idx2 < tokens.size)
    (h_off1 : v1.pos.offset = tokens[idx1].pos.offset)
    (h_off2 : v2.pos.offset = tokens[idx2].pos.offset)
    (h_ne : idx1 ≠ idx2) :
    ScanInv' (tokens.setIfInBounds idx1 v1 |>.setIfInBounds idx2 v2) offset := by
  have h1 := setIfInBounds_preserves_ScanInv' tokens offset idx1 v1 h h_idx1 h_off1
  have h_idx2' : idx2 < (tokens.setIfInBounds idx1 v1).size := by
    rw [Array.size_setIfInBounds]; exact h_idx2
  refine setIfInBounds_preserves_ScanInv' _ offset idx2 v2 h1 h_idx2' ?_
  -- Need: v2.pos.offset = (tokens.setIfInBounds idx1 v1)[idx2]'h_idx2' |>.pos.offset
  have h_eq : (tokens.setIfInBounds idx1 v1)[idx2]'h_idx2' =
      tokens[idx2]'h_idx2 := by
    rw [Array.getElem_setIfInBounds h_idx2]
    exact if_neg h_ne
  simp only [h_eq]; exact h_off2

-- scanValuePrepare preserves ScanInv.
--
-- **Initiative 3 / J.2 step 5 cutover**: the three `setIfInBounds`
-- calls were dropped, so all `simpleKey.possible = true` branches are
-- now field-only updates that leave `tokens` and `offset` unchanged.
-- `h_sk` is no longer needed (kept in the signature for callers'
-- benefit and J.4 cleanup).
theorem scanValuePrepare_preserves_ScanInv (s : ScannerState) (h : ScanInv s)
    (_h_sk : s.simpleKey.possible = true →
      s.simpleKey.tokenIndex ≤ s.tokens.size) :
    ScanInv (scanValuePrepare s) := by
  unfold scanValuePrepare
  split
  · -- simpleKey.possible = true
    split
    · split
      · exact field_update_preserves_ScanInv _ _ h rfl rfl  -- !inFlow, keyCol > currentIndent
      · exact field_update_preserves_ScanInv _ _ h rfl rfl  -- !inFlow, keyCol ≤ currentIndent
    · exact field_update_preserves_ScanInv _ _ h rfl rfl    -- inFlow
  · -- simpleKey.possible = false
    split
    · exact field_update_preserves_ScanInv _ _ h rfl rfl    -- explicitKeyLine.isSome
    · split
      · -- !inFlow: pushMappingIndent
        unfold pushMappingIndent
        split
        · exact emit_preserves_ScanInv { s with indents := _ } .blockMappingStart
            (field_update_preserves_ScanInv _ _ h rfl rfl)
        · exact h
      · exact h                                             -- inFlow: identity

-- skipSpacesLoop preserves ScanInv: only calls advance.
theorem skipSpacesLoop_preserves_ScanInv (s : ScannerState) (fuel : Nat)
    (h : ScanInv s) : ScanInv (skipSpacesLoop s fuel) := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; exact h
  | succ n ih =>
    unfold skipSpacesLoop; split
    · exact ih _ (advance_preserves_ScanInv _ h)
    · exact h

theorem skipSpaces_preserves_ScanInv (s : ScannerState) (h : ScanInv s) :
    ScanInv (skipSpaces s) := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_ScanInv s _ h

-- skipWhitespaceLoop preserves ScanInv: only calls advance.
theorem skipWhitespaceLoop_preserves_ScanInv (s : ScannerState) (fuel : Nat)
    (h : ScanInv s) : ScanInv (skipWhitespaceLoop s fuel) := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; exact h
  | succ n ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact ih _ (advance_preserves_ScanInv _ h)
      · exact h
    · exact h

theorem skipWhitespace_preserves_ScanInv (s : ScannerState) (h : ScanInv s) :
    ScanInv (skipWhitespace s) := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_ScanInv s _ h

-- skipToEndOfLineLoop preserves ScanInv: only calls advance.
theorem skipToEndOfLineLoop_preserves_ScanInv (s : ScannerState) (fuel : Nat)
    (h : ScanInv s) : ScanInv (skipToEndOfLineLoop s fuel) := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; exact h
  | succ n ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · exact h
      · exact ih _ (advance_preserves_ScanInv _ h)
    · exact h

theorem skipToEndOfLine_preserves_ScanInv (s : ScannerState) (h : ScanInv s) :
    ScanInv (skipToEndOfLine s) := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_ScanInv s _ h

-- consumeNewline preserves ScanInv: advance + field update.
theorem consumeNewline_preserves_ScanInv (s : ScannerState) (h : ScanInv s) :
    ScanInv (consumeNewline s) := by
  unfold consumeNewline; split
  · exact field_update_preserves_ScanInv _ _ (advance_preserves_ScanInv _ h) rfl rfl
  · dsimp only []; split
    · -- CRLF: advance preserves ScanInv, raw offset skip only increases offset
      exact offset_ge_preserves_ScanInv _ _
        (advance_preserves_ScanInv _ h) rfl
        (by dsimp only []; have : s.advance.offset < (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx := String.Pos.Raw.byteIdx_lt_byteIdx_next s.advance.input ⟨s.advance.offset⟩; omega)
    · exact field_update_preserves_ScanInv _ _ (advance_preserves_ScanInv _ h) rfl rfl
  · exact h

-- skipToContentWs preserves ScanInv.
theorem skipToContentWs_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : skipToContentWs s = .ok s') : ScanInv s' := by
  unfold skipToContentWs at h_ok; split at h_ok
  · -- needIndentCheck = true
    simp only [] at h_ok
    have h_sp : ScanInv (skipSpaces s) := skipSpaces_preserves_ScanInv s h
    split at h_ok
    · -- col ≤ currentIndent
      split at h_ok
      · -- peek? = some '\t'
        split at h_ok
        · simp at h_ok; rw [← h_ok]; exact skipWhitespace_preserves_ScanInv _ h_sp
        · split at h_ok
          · simp at h_ok; rw [← h_ok]; exact skipWhitespace_preserves_ScanInv _ h_sp
          · split at h_ok
            · simp at h_ok; rw [← h_ok]; exact skipWhitespace_preserves_ScanInv _ h_sp
            · simp at h_ok
        · simp at h_ok; rw [← h_ok]; exact skipWhitespace_preserves_ScanInv _ h_sp
      · simp at h_ok; rw [← h_ok]; exact h_sp
    · simp at h_ok; rw [← h_ok]; exact skipWhitespace_preserves_ScanInv _ h_sp
  · -- needIndentCheck = false
    simp at h_ok; rw [← h_ok]; exact skipWhitespace_preserves_ScanInv _ h

-- skipToContentComment preserves ScanInv.

/-- Helper: collectCommentTextLoop preserves ScanInv. -/
theorem collectCommentTextLoop_preserves_ScanInv (s : ScannerState)
    (text : String) (fuel : Nat) (h : ScanInv s) :
    ScanInv (collectCommentTextLoop s text fuel).2 := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; exact h
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · exact h
      · exact IH _ _ (advance_preserves_ScanInv _ h)
    · exact h

theorem skipToContentComment_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (skipToContentComment s) := by
  unfold skipToContentComment; split
  · -- peek? = some '#'
    simp only []
    split  -- peekBack?
    · -- peekBack? = some c
      split  -- if commentOk
      · -- true: { s' with comments := ... }
        exact field_update_preserves_ScanInv _ _
          (collectCommentTextLoop_preserves_ScanInv _ _ _ (advance_preserves_ScanInv _ h)) rfl rfl
      · exact h
    · -- peekBack? = none
      split  -- if commentOk
      · exact field_update_preserves_ScanInv _ _
          (collectCommentTextLoop_preserves_ScanInv _ _ _ (advance_preserves_ScanInv _ h)) rfl rfl
      · exact h
  · exact h

-- skipToContentLoop preserves ScanInv.
theorem skipToContentLoop_preserves_ScanInv (s s' : ScannerState) (fuel : Nat)
    (h : ScanInv s) (h_ok : skipToContentLoop s fuel = .ok s') : ScanInv s' := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h_ok; simp at h_ok; rw [← h_ok]; exact h
  | succ n ih =>
    unfold skipToContentLoop at h_ok; split at h_ok
    · simp at h_ok
    · rename_i s1 h_ws
      have h_s1 : ScanInv s1 := skipToContentWs_preserves_ScanInv s s1 h h_ws
      have h_s2 : ScanInv (skipToContentComment s1) :=
        skipToContentComment_preserves_ScanInv s1 h_s1
      simp only [] at h_ok; split at h_ok
      · split at h_ok
        · split at h_ok
          · -- !isInFlowSequence: recurse with { ... simpleKeyAllowed := true }
            have h_cn := consumeNewline_preserves_ScanInv _ h_s2
            have h_fu : ScanInv { consumeNewline (skipToContentComment s1)
                with simpleKeyAllowed := true } :=
              field_update_preserves_ScanInv _ _ h_cn rfl rfl
            exact ih _ h_fu h_ok
          · exact ih _ (consumeNewline_preserves_ScanInv _ h_s2) h_ok
        · simp at h_ok; rw [← h_ok]; exact h_s2
      · simp at h_ok; rw [← h_ok]; exact h_s2

-- skipToContent preserves ScanInv.
theorem skipToContent_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : skipToContent s = .ok s') : ScanInv s' := by
  unfold skipToContent at h_ok
  exact skipToContentLoop_preserves_ScanInv s s' _ h h_ok

-- Phase 2a: preprocess preserves ScanInv.
-- Helper: the state after the optional unwindIndents branch preserves ScanInv.
theorem preprocess_unwind_preserves_ScanInv (s_skip : ScannerState)
    (h_sinv : ScanInv s_skip) :
    ScanInv (if !s_skip.inFlow && s_skip.needIndentCheck then
      { unwindIndents s_skip s_skip.col with needIndentCheck := false }
    else s_skip) := by
  split
  · exact field_update_preserves_ScanInv _ _
      (unwindIndents_preserves_ScanInv s_skip s_skip.col h_sinv) rfl rfl
  · exact h_sinv

theorem preprocess_preserves_ScanInv (s : ScannerState) (s' : ScannerState) (c : Char)
    (h : ScanInv s) (h_ok : scanNextToken_preprocess s = .ok (some (s', c))) : ScanInv s' := by
  unfold scanNextToken_preprocess at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · rename_i s_skip h_skip
    have h_sinv : ScanInv s_skip := skipToContent_preserves_ScanInv s s_skip h h_skip
    split at h_ok
    · simp at h_ok
    · -- past hasMore
      split at h_ok
      · -- unwindIndents active
        split at h_ok
        · simp at h_ok
        · split at h_ok
          · simp at h_ok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
            obtain ⟨h_eq, _⟩ := h_ok; subst h_eq
            apply saveSimpleKey_preserves_ScanInv
            exact field_update_preserves_ScanInv _ _
              (unwindIndents_preserves_ScanInv s_skip s_skip.col h_sinv) rfl rfl
      · -- unwindIndents inactive
        split at h_ok
        · simp at h_ok
        · split at h_ok
          · simp at h_ok
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h_ok
            obtain ⟨h_eq, _⟩ := h_ok; subst h_eq
            exact saveSimpleKey_preserves_ScanInv _ h_sinv

/-!
### Phase 2: Per-dispatcher ScanInv theorems
-/

-- Phase 2c: Each flow indicator function is emit + advance + field updates.
theorem scanFlowSequenceStart_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (scanFlowSequenceStart s) := by
  unfold scanFlowSequenceStart
  apply field_update_preserves_ScanInv _ _ _ rfl rfl
  apply advance_preserves_ScanInv
  apply emit_preserves_ScanInv
  exact field_update_preserves_ScanInv _ _ h rfl rfl

theorem scanFlowSequenceEnd_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (scanFlowSequenceEnd s) := by
  unfold scanFlowSequenceEnd
  apply field_update_preserves_ScanInv _ _ _ rfl rfl
  apply advance_preserves_ScanInv
  exact emit_preserves_ScanInv _ .flowSequenceEnd h

theorem scanFlowMappingStart_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (scanFlowMappingStart s) := by
  unfold scanFlowMappingStart
  apply field_update_preserves_ScanInv _ _ _ rfl rfl
  apply advance_preserves_ScanInv
  apply emit_preserves_ScanInv
  exact field_update_preserves_ScanInv _ _ h rfl rfl

theorem scanFlowMappingEnd_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (scanFlowMappingEnd s) := by
  unfold scanFlowMappingEnd
  apply field_update_preserves_ScanInv _ _ _ rfl rfl
  apply advance_preserves_ScanInv
  exact emit_preserves_ScanInv _ .flowMappingEnd h

theorem scanFlowEntry_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) (s' : ScannerState)
    (h_ok : scanFlowEntry s = .ok s') : ScanInv s' := by
  unfold scanFlowEntry at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · split at h_ok
    · simp at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact field_update_preserves_ScanInv _ _
        (advance_preserves_ScanInv _ (emit_preserves_ScanInv _ .flowEntry h)) rfl rfl
  · simp only [Except.ok.injEq] at h_ok; subst h_ok
    exact field_update_preserves_ScanInv _ _
      (advance_preserves_ScanInv _ (emit_preserves_ScanInv _ .flowEntry h)) rfl rfl

-- Phase 2c: dispatchFlowIndicators preserves ScanInv.
theorem dispatchFlowIndicators_preserves_ScanInv (s : ScannerState) (c : Char)
    (h : ScanInv s) (s' : ScannerState)
    (h_ok : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) : ScanInv s' := by
  unfold scanNextToken_dispatchFlowIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- c == '['
  split at h_ok
  · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact scanFlowSequenceStart_preserves_ScanInv s h
  -- c == ']'
  · split at h_ok
    · split at h_ok
      · simp at h_ok
      · split at h_ok
        · simp at h_ok
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          exact scanFlowSequenceEnd_preserves_ScanInv s h
    -- c == '{'
    · split at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanFlowMappingStart_preserves_ScanInv s h
      -- c == '}'
      · split at h_ok
        · split at h_ok
          · simp at h_ok
          · split at h_ok
            · simp at h_ok
            · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
              exact scanFlowMappingEnd_preserves_ScanInv s h
        -- c == ','
        · split at h_ok
          · split at h_ok
            · simp at h_ok
            · split at h_ok
              · simp at h_ok
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
                exact scanFlowEntry_preserves_ScanInv s h _ h_entry
          -- fallthrough: none
          · simp at h_ok

-- Phase 2b: Structural dispatchers.

-- advanceNLoop preserves ScanInv: just repeated advance.
theorem advanceNLoop_preserves_ScanInv (s : ScannerState) (n : Nat)
    (h : ScanInv s) : ScanInv (ScannerState.advanceNLoop s n) := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; exact h
  | succ n ih => unfold ScannerState.advanceNLoop; exact ih _ (advance_preserves_ScanInv _ h)

theorem advanceN_preserves_ScanInv (s : ScannerState) (n : Nat)
    (h : ScanInv s) : ScanInv (s.advanceN n) := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_ScanInv s n h

-- Advance-only loop ScanInv preservation (directive sub-functions).
theorem collectDirectiveNameLoop_preserves_ScanInv (s : ScannerState)
    (name : String) (fuel : Nat) (h : ScanInv s) :
    ScanInv (collectDirectiveNameLoop s name fuel).2 := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; exact h
  | succ n ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · exact ih _ _ (advance_preserves_ScanInv _ h)
      · exact h
    · exact h

theorem collectVersionMajorLoop_preserves_ScanInv (s : ScannerState)
    (major : String) (fuel : Nat) (h : ScanInv s) :
    ScanInv (collectVersionMajorLoop s major fuel).2 := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; exact h
  | succ n ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_ScanInv _ h
    · split
      · exact ih _ _ (advance_preserves_ScanInv _ h)
      · exact h
    · exact h

theorem collectVersionMinorLoop_preserves_ScanInv (s : ScannerState)
    (minor : String) (fuel : Nat) (h : ScanInv s) :
    ScanInv (collectVersionMinorLoop s minor fuel).2 := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; exact h
  | succ n ih =>
    unfold collectVersionMinorLoop; split
    · split
      · exact ih _ _ (advance_preserves_ScanInv _ h)
      · exact h
    · exact h

theorem collectTagHandleDirectiveLoop_preserves_ScanInv (s : ScannerState)
    (handle : String) (fuel : Nat) (h : ScanInv s) :
    ScanInv (collectTagHandleDirectiveLoop s handle fuel).2 := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; exact h
  | succ n ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · exact ih _ _ (advance_preserves_ScanInv _ h)
      · exact h
    · exact h

theorem collectTagPrefixLoop_preserves_ScanInv (s : ScannerState)
    (pfx : String) (fuel : Nat) (h : ScanInv s) :
    ScanInv (collectTagPrefixLoop s pfx fuel).2 := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; exact h
  | succ n ih =>
    unfold collectTagPrefixLoop; split
    · split
      · exact ih _ _ (advance_preserves_ScanInv _ h)
      · exact h
    · exact h

-- Offset monotonicity for advance-only loops (needed for emitAt h_pos).
theorem skipWhitespaceLoop_offset_ge (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).offset ≥ s.offset := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; omega
  | succ n ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem skipWhitespace_offset_ge (s : ScannerState) :
    (skipWhitespace s).offset ≥ s.offset := by
  unfold skipWhitespace; exact skipWhitespaceLoop_offset_ge s _

theorem collectDirectiveNameLoop_offset_ge (s : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).2.offset ≥ s.offset := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectVersionMajorLoop_offset_ge (s : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).2.offset ≥ s.offset := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectVersionMajorLoop; split
    · exact ScannerProgress.advance_offset_ge s
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectVersionMinorLoop_offset_ge (s : ScannerState) (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).2.offset ≥ s.offset := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectVersionMinorLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectTagHandleDirectiveLoop_offset_ge (s : ScannerState)
    (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).2.offset ≥ s.offset := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectTagPrefixLoop_offset_ge (s : ScannerState) (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).2.offset ≥ s.offset := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectTagPrefixLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

-- Phase 2e offset_ge lemmas for content scanner sub-functions.

theorem skipSpacesLoop_offset_ge (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).offset ≥ s.offset := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold skipSpacesLoop; split
    · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _)
    · exact Nat.le_refl _

theorem skipSpaces_offset_ge (s : ScannerState) :
    (skipSpaces s).offset ≥ s.offset := by
  unfold skipSpaces; exact skipSpacesLoop_offset_ge s _

theorem skipToEndOfLineLoop_offset_ge (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).offset ≥ s.offset := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _)
    · exact Nat.le_refl _

theorem skipToEndOfLine_offset_ge (s : ScannerState) :
    (skipToEndOfLine s).offset ≥ s.offset := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_offset_ge s _

theorem consumeNewline_offset_ge (s : ScannerState) :
    (consumeNewline s).offset ≥ s.offset := by
  unfold consumeNewline
  split
  · -- '\n': advance
    exact ScannerProgress.advance_offset_ge s
  · -- '\r': advance, maybe advance again
    -- The inner match is on s.advance.peek?
    simp only []
    split
    · -- CRLF: raw offset skip increases offset beyond advance
      exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
        (by dsimp only []; have : s.advance.offset < (String.Pos.Raw.next s.advance.input ⟨s.advance.offset⟩).byteIdx := String.Pos.Raw.byteIdx_lt_byteIdx_next s.advance.input ⟨s.advance.offset⟩; omega)
    · exact ScannerProgress.advance_offset_ge s
  · exact Nat.le_refl _

theorem collectHexDigitsLoop_offset_ge (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.offset ≥ s.offset := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; exact Nat.le_refl _
  | succ n' ih =>
    unfold collectHexDigitsLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem parseHexEscape_offset_ge (s : ScannerState) (n : Nat)
    (ch : Char) (s' : ScannerState) (h : parseHexEscape s n = .ok (ch, s')) :
    s'.offset ≥ s.offset := by
  unfold parseHexEscape at h
  simp at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq, Prod.mk.injEq] at h
  exact h.2 ▸ collectHexDigitsLoop_offset_ge s _ n

theorem processEscape_offset_ge (s : ScannerState)
    (ch : Char) (s' : ScannerState) (h : processEscape s = .ok (ch, s')) :
    s'.offset ≥ s.offset := by
  unfold processEscape at h
  split at h
  · contradiction
  · -- Match on character: 26+ branches, all either .ok (ch, s.advance) or parseHexEscape
    simp only [] at h
    -- Split all character match arms
    split at h <;>
    (try (simp only [Except.ok.injEq, Prod.mk.injEq] at h; exact h.2 ▸ ScannerProgress.advance_offset_ge s)) <;>
    (try contradiction) <;>
    -- parseHexEscape branches (x, u, U): s.advance then parseHexEscape
    (exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (parseHexEscape_offset_ge s.advance _ _ _ h))

theorem collectAnchorNameLoop_offset_ge (s : ScannerState) (name : String) (fuel : Nat) :
    (collectAnchorNameLoop s name fuel).snd.offset ≥ s.offset := by
  induction fuel generalizing s name with
  | zero => unfold collectAnchorNameLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectAnchorNameLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectVerbatimTagLoop_offset_ge (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.offset ≥ s.offset := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectVerbatimTagLoop; split
    · exact ScannerProgress.advance_offset_ge s
    · split  -- isUriCharBool
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectTagSuffixLoop_offset_ge (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.offset ≥ s.offset := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectTagSuffixLoop; split
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem collectTagHandleLoop_offset_ge (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).2.2.offset ≥ s.offset := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectTagHandleLoop; split
    · exact ScannerProgress.advance_offset_ge s
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem parseBlockHeaderLoop_offset_ge (s : ScannerState) (chomp : ChompStyle)
    (explicitOffset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp explicitOffset fuel).2.2.offset ≥ s.offset := by
  induction fuel generalizing s chomp explicitOffset with
  | zero => unfold parseBlockHeaderLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold parseBlockHeaderLoop; split
    · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ _)
    · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ _)
    · split
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem consumeExactSpaces_offset_ge (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.offset ≥ s.offset := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; exact Nat.le_refl _
  | succ n ih =>
    unfold consumeExactSpaces; split
    · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _)
    · exact Nat.le_refl _

theorem collectLineContentLoop_offset_ge (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.offset ≥ s.offset := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectLineContentLoop; split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _)
    · exact Nat.le_refl _

/-- Helper: collectCommentTextLoop offset is non-decreasing. -/
theorem collectCommentTextLoop_offset_ge (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.offset ≥ s.offset := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; exact Nat.le_refl _
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · exact Nat.le_refl _
      · exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (IH _ _)
    · exact Nat.le_refl _

theorem scanBlockScalarSkipComment_offset_ge (s : ScannerState) :
    (scanBlockScalarSkipComment s).offset ≥ s.offset := by
  unfold scanBlockScalarSkipComment
  split
  · -- some '#'
    split
    · -- peekBack? = some c
      dsimp only []
      split
      · simp only []
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (collectCommentTextLoop_offset_ge _ _ _)
      · exact Nat.le_refl _
    · -- peekBack? = none: commentOk = false → if false then ... else s
      exact Nat.le_refl _
  · exact Nat.le_refl _

theorem scanBlockScalarConsumeNewline_offset_ge (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') :
    s'.offset ≥ s.offset := by
  unfold scanBlockScalarConsumeNewline at h; split at h
  · split at h
    · simp only [Except.ok.injEq] at h; subst h; exact consumeNewline_offset_ge s
    · split at h
      · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
      · contradiction
  · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _

theorem foldQuotedNewlinesLoop_offset_ge (s : ScannerState) (emptyCount : Nat)
    (fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).1.offset ≥ s.offset := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold foldQuotedNewlinesLoop; simp only []
    split
    · split
      · exact Nat.le_trans (Nat.le_trans (skipSpaces_offset_ge s) (consumeNewline_offset_ge _)) (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem skipBlankLinesLoop_offset_ge (s : ScannerState) (cnt : Nat) (fuel : Nat)
    (inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.offset ≥ s.offset := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold skipBlankLinesLoop; simp only []
    split
    · split
      · exact Nat.le_trans
          (Nat.le_trans (skipSpaces_offset_ge s) (consumeNewline_offset_ge _))
          (ih _ _)
      · exact Nat.le_refl _
    · exact Nat.le_refl _

theorem foldQuotedNewlines_offset_ge (s : ScannerState)
    (str : String) (s' : ScannerState) (h : foldQuotedNewlines s = .ok (str, s')) :
    s'.offset ≥ s.offset := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h <;> try split at h
  all_goals (try contradiction)
  all_goals (try split at h) <;> try contradiction
  all_goals (simp only [Except.ok.injEq, Prod.mk.injEq] at h; obtain ⟨_, rfl⟩ := h)
  all_goals (
    have h1 := consumeNewline_offset_ge s
    have h2 := foldQuotedNewlinesLoop_offset_ge (consumeNewline s) 0
      (s.inputEnd - (consumeNewline s).offset + 1)
    have h3 := skipSpaces_offset_ge (foldQuotedNewlinesLoop (consumeNewline s) 0
      (s.inputEnd - (consumeNewline s).offset + 1)).fst
    have h4 := skipWhitespace_offset_ge (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0
      (s.inputEnd - (consumeNewline s).offset + 1)).fst)
    exact Nat.le_trans h1 (Nat.le_trans h2 (Nat.le_trans h3 h4)))

theorem collectBlockScalarLoop_offset_ge (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.offset ≥ s.offset := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; exact Nat.le_refl _
  | succ n ih =>
    unfold collectBlockScalarLoop; simp only []
    split
    · -- atDocumentBoundary: return s
      exact Nat.le_refl _
    · -- not atDocumentBoundary
      -- After consumeExactSpaces, match on peek?
      split
      · -- none: return s_after_spaces
        exact consumeExactSpaces_offset_ge s _
      · -- some c
        split
        · -- isLineBreak: consumeNewline then recurse
          exact Nat.le_trans (Nat.le_trans (consumeExactSpaces_offset_ge s _) (consumeNewline_offset_ge _)) (ih _ _)
        · -- not isLineBreak
          split
          · -- spacesConsumed < contentIndent: return s
            exact Nat.le_refl _
          · -- collect line content, then match on peek?
            split
            · -- some c': split on isLineBreak
              split
              · -- isLineBreak c': consumeNewline then recurse
                exact Nat.le_trans
                  (Nat.le_trans (consumeExactSpaces_offset_ge s _)
                    (Nat.le_trans (collectLineContentLoop_offset_ge _ _ _)
                      (consumeNewline_offset_ge _)))
                  (ih _ _)
              · -- not isLineBreak c': recurse with s_after_line
                exact Nat.le_trans
                  (Nat.le_trans (consumeExactSpaces_offset_ge s _)
                    (collectLineContentLoop_offset_ge _ _ _))
                  (ih _ _)
            · -- none: return s_after_line
              exact Nat.le_trans (consumeExactSpaces_offset_ge s _)
                (collectLineContentLoop_offset_ge _ _ _)

-- Level 3 offset_ge lemmas for content loop functions.

theorem collectDoubleQuotedLoop_offset_ge (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (str : String) (s' : ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok (str, s')) :
    s'.offset ≥ s.offset := by
  induction fuel generalizing s content with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ n ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · contradiction  -- none
    · -- some '"': closing quote, result is (content, s.advance)
      simp only [Except.ok.injEq, Prod.mk.injEq] at h
      exact h.2 ▸ ScannerProgress.advance_offset_ge s
    · -- some '\\': escape sequence
      simp only [] at h
      split at h
      · -- some c after backslash
        split at h
        · -- isLineBreak: consumeNewline → skipWhitespace → recurse
          exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
            (Nat.le_trans (consumeNewline_offset_ge s.advance)
            (Nat.le_trans (skipWhitespace_offset_ge _) (ih _ _ h)))
        · -- regular escape: processEscape → recurse
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i esc_result heq
          cases esc_result with
          | mk ch s_esc =>
            exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
              (Nat.le_trans (processEscape_offset_ge s.advance ch s_esc heq) (ih _ _ h))
      · contradiction  -- none after backslash
    · -- some c (regular/linebreak)
      split at h
      · -- isLineBreak: foldQuotedNewlines → validation → recurse
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          simp only [pure, Except.pure] at h
          split at h <;> try contradiction  -- atDocumentStart || atDocumentEnd
          split at h <;> try contradiction  -- col ≤ currentIndent
          exact Nat.le_trans (foldQuotedNewlines_offset_ge s folded s_fold heq) (ih _ _ h)
      · -- regular character: advance → recurse
        split at h <;> try contradiction  -- isNbJsonBool check
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ h)

theorem collectSingleQuotedLoop_offset_ge (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (str : String) (s' : ScannerState)
    (h : collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok (str, s')) :
    s'.offset ≥ s.offset := by
  induction fuel generalizing s content with
  | zero => unfold collectSingleQuotedLoop at h; contradiction
  | succ n ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · contradiction  -- none
    · -- some '\'': escaped or closing
      simp only [] at h
      split at h
      · -- escaped quote '\'': advance twice → recurse
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (Nat.le_trans (ScannerProgress.advance_offset_ge s.advance) (ih _ _ h))
      · -- closing quote
        simp only [Except.ok.injEq, Prod.mk.injEq] at h
        exact h.2 ▸ ScannerProgress.advance_offset_ge s
    · -- some c (regular character or linebreak)
      split at h
      · -- isLineBreak: foldQuotedNewlines → validations → recurse
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          simp only [pure, Except.pure] at h
          split at h <;> try contradiction  -- atDocumentStart || atDocumentEnd
          split at h <;> try contradiction  -- col ≤ currentIndent
          exact Nat.le_trans (foldQuotedNewlines_offset_ge s folded s_fold heq) (ih _ _ h)
      · -- regular character: advance → recurse
        split at h <;> try contradiction  -- isNbJsonBool check
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ h)

theorem collectPlainScalarLoop_offset_ge (s : ScannerState) (content spaces : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat)
    (result : PlainScalarResult)
    (h : collectPlainScalarLoop s content spaces fuel inFlow contentIndent inputEnd = .ok result) :
    result.state.offset ≥ s.offset := by
  induction fuel generalizing s content spaces with
  | zero =>
    unfold collectPlainScalarLoop at h
    simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
  | succ n ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · -- peek = none
      simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
    · -- peek = some c
      rename_i c
      split at h
      · -- collectPlainScalar_terminates? = some → state = s
        rename_i hterm
        simp only [Except.ok.injEq] at h; subst h
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
        exact Nat.le_refl _
      · -- collectPlainScalar_terminates? = none → continue
        split at h
        · -- isLineBreak c
          split at h
          · -- inFlow
            simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk folded s_fold =>
              split at h
              · -- some '#': terminate → state = s
                simp only [Except.ok.injEq] at h; subst h
                exact Nat.le_refl _
              · -- recurse with content-length check
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ folded) "" n inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
                  · have h_eq := Except.ok.inj h; subst h_eq
                    exact Nat.le_trans
                      (foldQuotedNewlines_offset_ge s folded s_fold heq) (ih _ _ _ h_loop)
                | error e => simp at h
          · -- !inFlow: block line break
            split at h
            · -- _handleBlockLineBreak = none → terminate
              simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
            · -- _handleBlockLineBreak = some → recurse
              rename_i content' s' hblk
              have hoff : s'.offset ≥ s.offset := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2]
                exact Nat.le_trans (consumeNewline_offset_ge s)
                  (Nat.le_trans (skipBlankLinesLoop_offset_ge _ _ _ _)
                  (skipSpaces_offset_ge _))
              split at h
              · -- s'.peek? = some '#' → terminate → state = s
                simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
              · -- s'.peek? = _ → recurse with content-length check
                dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" n inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
                  · have h_eq := Except.ok.inj h; subst h_eq
                    exact Nat.le_trans hoff (ih _ _ _ h_loop)
                | error e => simp at h
        · split at h
          · -- isWhiteSpace: advance → recurse
            exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ _ h)
          · -- regular content
            split at h
            · -- !isPlainSafe
              simp only [Except.ok.injEq] at h; subst h; exact Nat.le_refl _
            · -- recurse with advance
              simp only [] at h
              exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (ih _ _ _ h)

-- ScanInv monotonicity: if tokens are unchanged and offset increases, ScanInv transfers.
theorem ScanInv_mono {s s' : ScannerState} (h_inv : ScanInv s) (h_tok : s'.tokens = s.tokens)
    (h_off : s'.offset ≥ s.offset) : ScanInv s' := by
  obtain ⟨h_ord, h_bnd⟩ := h_inv
  constructor
  · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
    simp only [h_tok] at hi hj ⊢
    exact h_ord ⟨i, hi⟩ ⟨j, hj⟩ hij
  · intro ⟨i, hi⟩
    simp only [h_tok] at hi ⊢
    exact Nat.le_trans (h_bnd ⟨i, hi⟩) h_off

-- Helper: if tokens are unchanged from a state where all token offsets ≤ pos.offset,
-- then the current tokens are also ≤ pos.offset.
theorem tokens_bounded_through_chain (s_curr s_orig : ScannerState) (pos_off : Nat)
    (h_bnd : ∀ i : Fin s_orig.tokens.size, s_orig.tokens[i].pos.offset ≤ pos_off)
    (h_tok : s_curr.tokens = s_orig.tokens) :
    ∀ i : Fin s_curr.tokens.size, s_curr.tokens[i].pos.offset ≤ pos_off := by
  intro ⟨i, hi⟩
  simp only [h_tok] at hi ⊢
  exact h_bnd ⟨i, hi⟩

-- scanDocumentStart preserves ScanInv (pure function).
theorem scanDocumentStart_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (scanDocumentStart s) := by
  unfold scanDocumentStart
  apply field_update_preserves_ScanInv _ _ _ rfl rfl
  apply advanceN_preserves_ScanInv
  apply emit_preserves_ScanInv
  exact field_update_preserves_ScanInv _ _
    (unwindIndents_preserves_ScanInv s (-1) h) rfl rfl

-- scanDocumentEnd preserves ScanInv (Except — returns `result`, not the validated state).
set_option maxHeartbeats 800000 in
theorem scanDocumentEnd_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanDocumentEnd s = .ok s') : ScanInv s' := by
  unfold scanDocumentEnd at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · -- All ok paths produce the same `result` state; prove ScanInv per branch
    -- Helper tactic macro not needed; just repeat the apply chain
    split at h_ok
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply advanceN_preserves_ScanInv
      apply emit_preserves_ScanInv
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      exact unwindIndents_preserves_ScanInv s (-1) h
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply advanceN_preserves_ScanInv
      apply emit_preserves_ScanInv
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      exact unwindIndents_preserves_ScanInv s (-1) h
    · split at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        apply field_update_preserves_ScanInv _ _ _ rfl rfl
        apply advanceN_preserves_ScanInv
        apply emit_preserves_ScanInv
        apply field_update_preserves_ScanInv _ _ _ rfl rfl
        exact unwindIndents_preserves_ScanInv s (-1) h
      · simp at h_ok

-- scanYamlDirective preserves ScanInv.
-- h_tok_bnd: all existing tokens have offset ≤ startPos.offset (because tokens
-- haven't changed since the original state where startPos was captured).
theorem scanYamlDirective_preserves_ScanInv (s s_after_ws : ScannerState)
    (startPos : YamlPos) (h_inv : ScanInv s_after_ws) (h_pos_ge : startPos.offset ≤ s_after_ws.offset)
    (h_tok_bnd : ∀ i : Fin s_after_ws.tokens.size, s_after_ws.tokens[i].pos.offset ≤ startPos.offset)
    (s' : ScannerState) (h_ok : scanYamlDirective s s_after_ws startPos = .ok s') :
    ScanInv s' := by
  unfold scanYamlDirective at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · simp at h_ok
  · -- past seenYamlDirective check; all intermediate ops are advance-only
    -- s_validated = skipWhitespace (collectVersionMinorLoop (collectVersionMajorLoop s_after_ws ...).2 ...).2
    -- tokens chain: s_validated.tokens = s_after_ws.tokens (all ops preserve tokens)
    -- offset chain: s_validated.offset ≥ s_after_ws.offset (all ops increase offset)
    -- For emitAt: need h_pos (startPos.offset ≤ s_validated.offset) and h_ge (token bound)
    -- All throw/error branches are contradictions
    -- Three match branches on s_validated.peek?:
    split at h_ok
    · -- peek? = some '#'
      split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        apply field_update_preserves_ScanInv _ _ _ rfl rfl
        apply emitAt_preserves_ScanInv
        · exact skipWhitespace_preserves_ScanInv _
            (collectVersionMinorLoop_preserves_ScanInv _ _ _
              (collectVersionMajorLoop_preserves_ScanInv _ _ _ h_inv))
        · exact Nat.le_trans h_pos_ge
            (Nat.le_trans (collectVersionMajorLoop_offset_ge _ _ _)
            (Nat.le_trans (collectVersionMinorLoop_offset_ge _ _ _)
            (skipWhitespace_offset_ge _)))
        · exact tokens_bounded_through_chain _ s_after_ws _ h_tok_bnd
            (by rw [skipWhitespace_preserves_tokens,
                     ScanHelpers.collectVersionMinorLoop_preserves_tokens,
                     ScanHelpers.collectVersionMajorLoop_preserves_tokens])
    · -- peek? = some c (not '#')
      split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq] at h_ok; subst h_ok
        apply field_update_preserves_ScanInv _ _ _ rfl rfl
        apply emitAt_preserves_ScanInv
        · exact skipWhitespace_preserves_ScanInv _
            (collectVersionMinorLoop_preserves_ScanInv _ _ _
              (collectVersionMajorLoop_preserves_ScanInv _ _ _ h_inv))
        · exact Nat.le_trans h_pos_ge
            (Nat.le_trans (collectVersionMajorLoop_offset_ge _ _ _)
            (Nat.le_trans (collectVersionMinorLoop_offset_ge _ _ _)
            (skipWhitespace_offset_ge _)))
        · exact tokens_bounded_through_chain _ s_after_ws _ h_tok_bnd
            (by rw [skipWhitespace_preserves_tokens,
                     ScanHelpers.collectVersionMinorLoop_preserves_tokens,
                     ScanHelpers.collectVersionMajorLoop_preserves_tokens])
    · -- peek? = none
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact skipWhitespace_preserves_ScanInv _
          (collectVersionMinorLoop_preserves_ScanInv _ _ _
            (collectVersionMajorLoop_preserves_ScanInv _ _ _ h_inv))
      · exact Nat.le_trans h_pos_ge
          (Nat.le_trans (collectVersionMajorLoop_offset_ge _ _ _)
          (Nat.le_trans (collectVersionMinorLoop_offset_ge _ _ _)
          (skipWhitespace_offset_ge _)))
      · exact tokens_bounded_through_chain _ s_after_ws _ h_tok_bnd
          (by rw [skipWhitespace_preserves_tokens,
                   ScanHelpers.collectVersionMinorLoop_preserves_tokens,
                   ScanHelpers.collectVersionMajorLoop_preserves_tokens])

-- scanTagDirective preserves ScanInv.
theorem scanTagDirective_preserves_ScanInv (s s_after_ws : ScannerState)
    (startPos : YamlPos) (h_inv : ScanInv s_after_ws) (h_pos_ge : startPos.offset ≤ s_after_ws.offset)
    (h_tok_bnd : ∀ i : Fin s_after_ws.tokens.size, s_after_ws.tokens[i].pos.offset ≤ startPos.offset)
    (s' : ScannerState) (h_ok : scanTagDirective s s_after_ws startPos = .ok s') :
    ScanInv s' := by
  unfold scanTagDirective at h_ok
  dsimp only [] at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok
  · -- some '#'
    split at h_ok
    · contradiction
    · simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact skipWhitespace_preserves_ScanInv _
          (collectTagPrefixLoop_preserves_ScanInv _ _ _
            (skipWhitespace_preserves_ScanInv _
              (collectTagHandleDirectiveLoop_preserves_ScanInv _ _ _ h_inv)))
      · exact Nat.le_trans h_pos_ge
          (Nat.le_trans (collectTagHandleDirectiveLoop_offset_ge _ _ _)
          (Nat.le_trans (skipWhitespace_offset_ge _)
          (Nat.le_trans (collectTagPrefixLoop_offset_ge _ _ _)
          (skipWhitespace_offset_ge _))))
      · exact tokens_bounded_through_chain _ s_after_ws _ h_tok_bnd
          (by rw [skipWhitespace_preserves_tokens,
                   ScanHelpers.collectTagPrefixLoop_preserves_tokens,
                   skipWhitespace_preserves_tokens,
                   ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens])
  · -- some c
    split at h_ok
    · contradiction
    · simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact skipWhitespace_preserves_ScanInv _
          (collectTagPrefixLoop_preserves_ScanInv _ _ _
            (skipWhitespace_preserves_ScanInv _
              (collectTagHandleDirectiveLoop_preserves_ScanInv _ _ _ h_inv)))
      · exact Nat.le_trans h_pos_ge
          (Nat.le_trans (collectTagHandleDirectiveLoop_offset_ge _ _ _)
          (Nat.le_trans (skipWhitespace_offset_ge _)
          (Nat.le_trans (collectTagPrefixLoop_offset_ge _ _ _)
          (skipWhitespace_offset_ge _))))
      · exact tokens_bounded_through_chain _ s_after_ws _ h_tok_bnd
          (by rw [skipWhitespace_preserves_tokens,
                   ScanHelpers.collectTagPrefixLoop_preserves_tokens,
                   skipWhitespace_preserves_tokens,
                   ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens])
  · -- none
    simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_ok; subst h_ok
    apply field_update_preserves_ScanInv _ _ _ rfl rfl
    apply emitAt_preserves_ScanInv
    · exact skipWhitespace_preserves_ScanInv _
        (collectTagPrefixLoop_preserves_ScanInv _ _ _
          (skipWhitespace_preserves_ScanInv _
            (collectTagHandleDirectiveLoop_preserves_ScanInv _ _ _ h_inv)))
    · exact Nat.le_trans h_pos_ge
        (Nat.le_trans (collectTagHandleDirectiveLoop_offset_ge _ _ _)
        (Nat.le_trans (skipWhitespace_offset_ge _)
        (Nat.le_trans (collectTagPrefixLoop_offset_ge _ _ _)
        (skipWhitespace_offset_ge _))))
    · exact tokens_bounded_through_chain _ s_after_ws _ h_tok_bnd
        (by rw [skipWhitespace_preserves_tokens,
                 ScanHelpers.collectTagPrefixLoop_preserves_tokens,
                 skipWhitespace_preserves_tokens,
                 ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens])

-- scanDirective preserves ScanInv.
theorem scanDirective_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanDirective s = .ok s') : ScanInv s' := by
  unfold scanDirective at h_ok
  split at h_ok
  · simp at h_ok
  · -- allowDirectives: process directive
    -- Build the intermediate state chain
    have h_ws_inv : ScanInv (skipWhitespace
        (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2) :=
      skipWhitespace_preserves_ScanInv _
        (collectDirectiveNameLoop_preserves_ScanInv s.advance "" _
          (advance_preserves_ScanInv _ h))
    -- startPos = s.currentPos, so startPos.offset = s.offset
    have h_pos_ge : s.currentPos.offset ≤ (skipWhitespace
        (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).offset :=
      Nat.le_trans (show s.currentPos.offset ≤ s.advance.offset from
        show s.offset ≤ s.advance.offset from ScannerProgress.advance_offset_ge s)
        (Nat.le_trans (collectDirectiveNameLoop_offset_ge _ _ _)
          (skipWhitespace_offset_ge _))
    -- Token bound: all tokens ≤ startPos.offset = s.offset
    have h_tok_bnd : ∀ i : Fin (skipWhitespace
        (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens.size,
        (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).2).tokens[i].pos.offset ≤
          s.currentPos.offset := by
      apply tokens_bounded_through_chain _ s _ (fun i => h.2 i)
      rw [skipWhitespace_preserves_tokens, ScanHelpers.collectDirectiveNameLoop_preserves_tokens,
          advance_preserves_tokens]
    -- Reduce have/let bindings so split can find the match
    dsimp only [] at h_ok
    -- Dispatch on directive name
    split at h_ok
    · -- YAML (match wrapper)
      split at h_ok
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h_ok; subst h_eq
        exact skipToEndOfLine_preserves_ScanInv _
          (scanYamlDirective_preserves_ScanInv s _ _ h_ws_inv h_pos_ge h_tok_bnd s_inner h_inner)
      · contradiction
    · split at h_ok
      · -- TAG (match wrapper)
        split at h_ok
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h_ok; subst h_eq
          exact skipToEndOfLine_preserves_ScanInv _
            (scanTagDirective_preserves_ScanInv s _ _ h_ws_inv h_pos_ge h_tok_bnd s_inner h_inner)
        · contradiction
      · -- Unknown directive: skipToEndOfLine
        simp only [Except.ok.injEq] at h_ok; subst h_ok
        exact skipToEndOfLine_preserves_ScanInv _ h_ws_inv

-- Phase 2b dispatcher: dispatchStructural preserves ScanInv.
theorem dispatchStructural_preserves_ScanInv (s : ScannerState) (c : Char)
    (h : ScanInv s) (s' : ScannerState)
    (h_ok : scanNextToken_dispatchStructural s c = .ok (some s')) : ScanInv s' := by
  unfold scanNextToken_dispatchStructural at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- Flow indentation check: if in_flow && indentation issue
  split at h_ok
  · -- flow indentation check true
    split at h_ok
    · simp at h_ok  -- error
    · -- past flow indentation → document marker in flow check
      split at h_ok
      · simp at h_ok
      · split at h_ok
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          exact scanDocumentStart_preserves_ScanInv s h
        · split at h_ok
          · split at h_ok
            · simp at h_ok
            · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
              rename_i s_de h_de
              exact scanDocumentEnd_preserves_ScanInv s s_de h h_de
          · split at h_ok
            · split at h_ok
              · simp at h_ok
              · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
                rename_i s_dir h_dir
                exact scanDirective_preserves_ScanInv s s_dir h h_dir
            · simp at h_ok
  · -- flow indentation check false
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact scanDocumentStart_preserves_ScanInv s h
      · split at h_ok
        · split at h_ok
          · simp at h_ok
          · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
            rename_i s_de h_de
            exact scanDocumentEnd_preserves_ScanInv s s_de h h_de
        · split at h_ok
          · split at h_ok
            · simp at h_ok
            · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
              rename_i s_dir h_dir
              exact scanDirective_preserves_ScanInv s s_dir h h_dir
          · simp at h_ok

-- Phase 2d: Block indicators preserve ScanInv.

-- Helper lemmas: advance/emit/pushIndent preserve inFlow (they don't change flowLevel).
theorem advance_preserves_inFlow (s : ScannerState) :
    s.advance.inFlow = s.inFlow := by
  unfold ScannerState.advance ScannerState.inFlow
  split
  · dsimp only []
    split
    · rfl
    · split <;> rfl
  · rfl

theorem emit_preserves_inFlow (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).inFlow = s.inFlow := by
  unfold ScannerState.emit ScannerState.inFlow; rfl

theorem pushMappingIndent_preserves_inFlow (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).inFlow = s.inFlow := by
  unfold pushMappingIndent; split
  · simp [ScannerState.emit, ScannerState.inFlow]
  · rfl

theorem pushSequenceIndent_preserves_inFlow (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).inFlow = s.inFlow := by
  unfold pushSequenceIndent; split
  · simp [ScannerState.emit, ScannerState.inFlow]
  · rfl

-- pushSequenceIndent: if col > currentIndent, emit blockSequenceStart + push indent; else identity.
theorem pushSequenceIndent_preserves_ScanInv (s : ScannerState) (col : Int)
    (h : ScanInv s) : ScanInv (pushSequenceIndent s col) := by
  unfold pushSequenceIndent; split
  · apply field_update_preserves_ScanInv _ _ _ rfl rfl
    exact emit_preserves_ScanInv s .blockSequenceStart h
  · exact h

-- pushMappingIndent: if col > currentIndent, emit blockMappingStart + push indent; else identity.
theorem pushMappingIndent_preserves_ScanInv (s : ScannerState) (col : Int)
    (h : ScanInv s) : ScanInv (pushMappingIndent s col) := by
  unfold pushMappingIndent; split
  · apply field_update_preserves_ScanInv _ _ _ rfl rfl
    exact emit_preserves_ScanInv s .blockMappingStart h
  · exact h

-- Helper: the `if !inFlow then pushIndent else s` pattern.
theorem pushSequenceIfNotInFlow_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (if !s.inFlow then pushSequenceIndent s s.col else s) := by
  split
  · exact pushSequenceIndent_preserves_ScanInv _ _ h
  · exact h

theorem pushMappingIfNotInFlow_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (if !s.inFlow then pushMappingIndent s s.col else s) := by
  split
  · exact pushMappingIndent_preserves_ScanInv _ _ h
  · exact h

-- scanBlockEntry preserves ScanInv.
theorem scanBlockEntry_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanBlockEntry s = .ok s') : ScanInv s' := by
  unfold scanBlockEntry at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- guard fired: !s.inFlow = true, split on hasTab
    rename_i h_fl
    split at h_ok
    · contradiction
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      -- h_fl resolves if → pushSequenceIndent s s.col
      have h1 := pushSequenceIndent_preserves_ScanInv s s.col h
      have h2 := emit_preserves_ScanInv _ .blockEntry h1
      have h3 := advance_preserves_ScanInv _ h2
      exact field_update_preserves_ScanInv _ _ h3 rfl rfl
  · -- guard not fired: !s.inFlow = false
    rename_i h_fl
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    -- if !s.inFlow resolves to false → s_with_indent = s
    have h2 := emit_preserves_ScanInv s .blockEntry h
    have h3 := advance_preserves_ScanInv _ h2
    exact field_update_preserves_ScanInv _ _ h3 rfl rfl

-- scanKey preserves ScanInv.
theorem scanKey_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanKey s = .ok s') : ScanInv s' := by
  unfold scanKey at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- Examine what split does:
  split at h_ok
  · rename_i h_cond1
    -- h_cond1 tells us what was split on
    split at h_ok
    · rename_i h_cond2
      split at h_ok <;> (first | contradiction | skip)
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      -- Goal is in the case: s.inFlow = false, tab check passed
      have h1 := pushMappingIndent_preserves_ScanInv s s.col h
      have h2 := emit_preserves_ScanInv _ .key h1
      have h3 := advance_preserves_ScanInv _ h2
      exact field_update_preserves_ScanInv _ _ h3 rfl rfl
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h1 := pushMappingIndent_preserves_ScanInv s s.col h
      have h2 := emit_preserves_ScanInv _ .key h1
      have h3 := advance_preserves_ScanInv _ h2
      exact field_update_preserves_ScanInv _ _ h3 rfl rfl
  · rename_i h_cond1
    split at h_ok
    · split at h_ok <;> (first | contradiction | skip)
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h2 := emit_preserves_ScanInv s .key h
      have h3 := advance_preserves_ScanInv _ h2
      exact field_update_preserves_ScanInv _ _ h3 rfl rfl
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      have h2 := emit_preserves_ScanInv s .key h
      have h3 := advance_preserves_ScanInv _ h2
      exact field_update_preserves_ScanInv _ _ h3 rfl rfl

-- scanValueClearKey preserves ScanInv (pure field update or identity).
theorem scanValueClearKey_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) : ScanInv (scanValueClearKey s) := by
  unfold scanValueClearKey; split
  · split
    · exact field_update_preserves_ScanInv _ _ h rfl rfl
    · split
      · exact field_update_preserves_ScanInv _ _ h rfl rfl
      · exact h
  · exact h

-- scanValue preserves ScanInv.
-- Requires precondition on simple key validity (needed by scanValuePrepare).
theorem scanValue_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s)
    (h_sk : (scanValueClearKey s).simpleKey.possible = true →
      (scanValueClearKey s).simpleKey.tokenIndex ≤ (scanValueClearKey s).tokens.size)
    (h_ok : scanValue s = .ok s') : ScanInv s' := by
  unfold scanValue at h_ok
  simp only [bind, Except.bind] at h_ok
  -- Two Except.bind matches: scanValueValidate and scanValueTabCheck
  -- Don't unfold them — just split on .error/.ok for each
  split at h_ok
  · simp at h_ok  -- scanValueValidate error → contradiction
  · -- scanValueValidate ok; now scanValueTabCheck bind
    split at h_ok
    · simp at h_ok  -- scanValueTabCheck error → contradiction
    · -- Both checks passed
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply advance_preserves_ScanInv
      apply emit_preserves_ScanInv
      exact scanValuePrepare_preserves_ScanInv (scanValueClearKey s)
        (scanValueClearKey_preserves_ScanInv s h) h_sk

-- Phase 2d dispatcher: dispatchBlockIndicators preserves ScanInv.
theorem dispatchBlockIndicators_preserves_ScanInv (s : ScannerState) (c : Char)
    (h : ScanInv s)
    (h_sk : (scanValueClearKey s).simpleKey.possible = true →
      (scanValueClearKey s).simpleKey.tokenIndex ≤ (scanValueClearKey s).tokens.size)
    (s' : ScannerState)
    (h_ok : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) : ScanInv s' := by
  unfold scanNextToken_dispatchBlockIndicators at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok
  · -- c == '-' && !inFlow && isBlockEntryCandidate
    split at h_ok
    · simp at h_ok
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      rename_i s_be h_be
      exact scanBlockEntry_preserves_ScanInv s s_be h h_be
  · -- c == '?' && isKeyCandidate
    split at h_ok
    · split at h_ok
      · simp at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        rename_i s_k h_k
        exact scanKey_preserves_ScanInv s s_k h h_k
    · -- c == ':' && isValueCandidate
      split at h_ok
      · split at h_ok
        · simp at h_ok
        · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
          rename_i s_v h_v
          exact scanValue_preserves_ScanInv s s_v h h_sk h_v
      · simp at h_ok

-- Phase 2e: Content dispatcher ScanInv theorems.

-- scanAnchorOrAlias preserves ScanInv (Except function).
theorem scanAnchorOrAlias_preserves_ScanInv (s : ScannerState) (isAnchor : Bool)
    (h : ScanInv s) (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    ScanInv s' := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have heq := Except.ok.inj hok; subst heq
    apply field_update_preserves_ScanInv _ _ _ rfl rfl
    apply emitAt_preserves_ScanInv
    · exact ScanInv_mono (advance_preserves_ScanInv s h)
        (ScanHelpers.collectAnchorNameLoop_preserves_tokens _ _ _)
        (collectAnchorNameLoop_offset_ge _ _ _)
    · -- startPos.offset (= s.offset) ≤ s_loop.offset
      show s.currentPos.offset ≤ _
      simp only [ScannerState.currentPos]
      exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
        (collectAnchorNameLoop_offset_ge _ _ _)
    · -- all tokens ≤ startPos.offset
      intro ⟨i, hi⟩
      have h_tok := ScanHelpers.collectAnchorNameLoop_preserves_tokens s.advance "" (s.inputEnd - s.advance.offset)
      have h_adv := advance_preserves_tokens s
      simp only [h_tok, h_adv] at hi ⊢
      show s.tokens[i].pos.offset ≤ s.currentPos.offset
      simp only [ScannerState.currentPos]
      exact h.2 ⟨i, hi⟩

-- scanVerbatimTag preserves ScanInv (Except function).
theorem scanVerbatimTag_preserves_ScanInv (s : ScannerState) (startPos : YamlPos)
    (h : ScanInv s) (h_pos : startPos.offset ≤ s.offset)
    (h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ startPos.offset)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    ScanInv s' := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have heq := Except.ok.inj hok; subst heq
      apply emitAt_preserves_ScanInv
      · exact ScanInv_mono (advance_preserves_ScanInv s h)
          (ScanHelpers.collectVerbatimTagLoop_preserves_tokens _ _ _)
          (collectVerbatimTagLoop_offset_ge _ _ _)
      · exact Nat.le_trans h_pos (Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (collectVerbatimTagLoop_offset_ge _ _ _))
      · intro ⟨i, hi⟩
        have h_tok := ScanHelpers.collectVerbatimTagLoop_preserves_tokens s.advance "" (startPos.offset + s.inputEnd - s.advance.offset)
        have h_adv := advance_preserves_tokens s
        simp only [h_tok, h_adv] at hi ⊢
        exact h_ge ⟨i, hi⟩

-- scanSecondaryTag preserves ScanInv (pure function).
theorem scanSecondaryTag_preserves_ScanInv (s : ScannerState) (startPos : YamlPos)
    (h : ScanInv s) (h_pos : startPos.offset ≤ s.offset)
    (h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ startPos.offset) :
    ScanInv (scanSecondaryTag s startPos) := by
  unfold scanSecondaryTag
  apply emitAt_preserves_ScanInv
  · exact ScanInv_mono (advance_preserves_ScanInv s h)
      (ScanHelpers.collectTagSuffixLoop_preserves_tokens _ _ _)
      (collectTagSuffixLoop_offset_ge _ _ _)
  · exact Nat.le_trans h_pos (Nat.le_trans (ScannerProgress.advance_offset_ge s)
      (collectTagSuffixLoop_offset_ge _ _ _))
  · intro ⟨i, hi⟩
    have h_tok := ScanHelpers.collectTagSuffixLoop_preserves_tokens s.advance "" (startPos.offset + s.inputEnd - s.advance.offset)
    have h_adv := advance_preserves_tokens s
    simp only [h_tok, h_adv] at hi ⊢
    exact h_ge ⟨i, hi⟩

-- scanNamedTag preserves ScanInv (pure function).
theorem scanNamedTag_preserves_ScanInv (s : ScannerState) (startPos : YamlPos)
    (inputEnd : Nat) (h : ScanInv s) (h_pos : startPos.offset ≤ s.offset)
    (h_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ startPos.offset) :
    ScanInv (scanNamedTag s startPos inputEnd) := by
  unfold scanNamedTag; simp only []
  split
  · -- foundBang = true: collectTagHandleLoop → collectTagSuffixLoop → emitAt
    apply emitAt_preserves_ScanInv
    · have h_handle_tok := ScanHelpers.collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
      have h_handle_ge := collectTagHandleLoop_offset_ge s "" (inputEnd - s.offset)
      have h_inv_handle : ScanInv (collectTagHandleLoop s "" (inputEnd - s.offset)).snd.snd :=
        ScanInv_mono h h_handle_tok h_handle_ge
      exact ScanInv_mono h_inv_handle
        (ScanHelpers.collectTagSuffixLoop_preserves_tokens _ _ _)
        (collectTagSuffixLoop_offset_ge _ _ _)
    · exact Nat.le_trans h_pos (Nat.le_trans (collectTagHandleLoop_offset_ge s "" _)
        (collectTagSuffixLoop_offset_ge _ _ _))
    · intro ⟨i, hi⟩
      have h_tok1 := ScanHelpers.collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
      have h_tok2 := ScanHelpers.collectTagSuffixLoop_preserves_tokens
        (collectTagHandleLoop s "" (inputEnd - s.offset)).snd.snd "" (inputEnd - (collectTagHandleLoop s "" (inputEnd - s.offset)).snd.snd.offset)
      simp only [h_tok2, h_tok1] at hi ⊢
      exact h_ge ⟨i, hi⟩
  · -- foundBang = false: collectTagHandleLoop only → emitAt
    apply emitAt_preserves_ScanInv
    · exact ScanInv_mono h
        (ScanHelpers.collectTagHandleLoop_preserves_tokens s "" _)
        (collectTagHandleLoop_offset_ge s "" _)
    · exact Nat.le_trans h_pos (collectTagHandleLoop_offset_ge s "" _)
    · intro ⟨i, hi⟩
      have h_tok := ScanHelpers.collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
      simp only [h_tok] at hi ⊢
      exact h_ge ⟨i, hi⟩

-- scanTag preserves ScanInv (Except function).
theorem scanTag_preserves_ScanInv (s : ScannerState)
    (h : ScanInv s) (s' : ScannerState) (hok : scanTag s = .ok s') :
    ScanInv s' := by
  unfold scanTag at hok; dsimp only [] at hok
  have h_adv : ScanInv s.advance := advance_preserves_ScanInv s h
  have h_pos : s.currentPos.offset ≤ s.advance.offset := by
    simp only [ScannerState.currentPos]; exact ScannerProgress.advance_offset_ge s
  have h_ge : ∀ i : Fin s.advance.tokens.size, s.advance.tokens[i].pos.offset ≤ s.currentPos.offset := by
    intro ⟨i, hi⟩
    simp only [advance_preserves_tokens, ScannerState.currentPos] at hi ⊢
    exact h.2 ⟨i, hi⟩
  split at hok
  · -- verbatim
    simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have heq := Except.ok.inj hok; subst heq
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      exact scanVerbatimTag_preserves_ScanInv s.advance s.currentPos h_adv h_pos h_ge s_verb hv
  · have heq := Except.ok.inj hok; subst heq
    apply field_update_preserves_ScanInv _ _ _ rfl rfl
    exact scanSecondaryTag_preserves_ScanInv s.advance s.currentPos h_adv h_pos h_ge
  · have heq := Except.ok.inj hok; subst heq
    apply field_update_preserves_ScanInv _ _ _ rfl rfl
    exact scanNamedTag_preserves_ScanInv s.advance s.currentPos s.inputEnd h_adv h_pos h_ge

-- scanDoubleQuoted preserves ScanInv (Except function).
theorem scanDoubleQuoted_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanDoubleQuoted s = .ok s') : ScanInv s' := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i dq_result heq
  cases dq_result with
  | mk content s_close =>
    -- validateTrailingContent returns Unit, doesn't change state
    split at h_ok
    · -- inFlow check: validation branch
      split at h_ok <;> try contradiction
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact ScanInv_mono (advance_preserves_ScanInv s h)
          (ScanHelpers.collectDoubleQuotedLoop_preserves_tokens _ _ _ _ _ _ _  _ heq)
          (collectDoubleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · show s.currentPos.offset ≤ _
        simp only [ScannerState.currentPos]
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (collectDoubleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · intro ⟨i, hi⟩
        have h_tok : s_close.tokens = s.advance.tokens :=
          ScanHelpers.collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
        have h_adv := advance_preserves_tokens s
        simp only [h_tok, h_adv] at hi ⊢
        show s.tokens[i].pos.offset ≤ s.currentPos.offset
        simp only [ScannerState.currentPos]
        exact h.2 ⟨i, hi⟩
    · -- not inFlow: no validation
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact ScanInv_mono (advance_preserves_ScanInv s h)
          (ScanHelpers.collectDoubleQuotedLoop_preserves_tokens _ _ _ _ _ _ _ _ heq)
          (collectDoubleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · show s.currentPos.offset ≤ _
        simp only [ScannerState.currentPos]
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (collectDoubleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · intro ⟨i, hi⟩
        have h_tok : s_close.tokens = s.advance.tokens :=
          ScanHelpers.collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
        have h_adv := advance_preserves_tokens s
        simp only [h_tok, h_adv] at hi ⊢
        show s.tokens[i].pos.offset ≤ s.currentPos.offset
        simp only [ScannerState.currentPos]
        exact h.2 ⟨i, hi⟩

-- scanSingleQuoted preserves ScanInv (Except function).
theorem scanSingleQuoted_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanSingleQuoted s = .ok s') : ScanInv s' := by
  unfold scanSingleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i sq_result heq
  cases sq_result with
  | mk content s_close =>
    split at h_ok
    · split at h_ok <;> try contradiction
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact ScanInv_mono (advance_preserves_ScanInv s h)
          (ScanHelpers.collectSingleQuotedLoop_preserves_tokens _ _ _ _ _ _ _ _ heq)
          (collectSingleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · show s.currentPos.offset ≤ _
        simp only [ScannerState.currentPos]
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (collectSingleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · intro ⟨i, hi⟩
        have h_tok : s_close.tokens = s.advance.tokens :=
          ScanHelpers.collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
        have h_adv := advance_preserves_tokens s
        simp only [h_tok, h_adv] at hi ⊢
        show s.tokens[i].pos.offset ≤ s.currentPos.offset
        simp only [ScannerState.currentPos]
        exact h.2 ⟨i, hi⟩
    · simp only [Except.ok.injEq] at h_ok; subst h_ok
      apply field_update_preserves_ScanInv _ _ _ rfl rfl
      apply emitAt_preserves_ScanInv
      · exact ScanInv_mono (advance_preserves_ScanInv s h)
          (ScanHelpers.collectSingleQuotedLoop_preserves_tokens _ _ _ _ _ _ _ _ heq)
          (collectSingleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · show s.currentPos.offset ≤ _
        simp only [ScannerState.currentPos]
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
          (collectSingleQuotedLoop_offset_ge s.advance _ _ _ _ _ _ _ _ heq)
      · intro ⟨i, hi⟩
        have h_tok : s_close.tokens = s.advance.tokens :=
          ScanHelpers.collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
        have h_adv := advance_preserves_tokens s
        simp only [h_tok, h_adv] at hi ⊢
        show s.tokens[i].pos.offset ≤ s.currentPos.offset
        simp only [ScannerState.currentPos]
        exact h.2 ⟨i, hi⟩

-- scanPlainScalar preserves ScanInv (Except function).
theorem scanPlainScalar_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanPlainScalar s = .ok s') : ScanInv s' := by
  unfold scanPlainScalar at h_ok
  simp only [bind, Except.bind] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h_ok; subst h_ok
  apply field_update_preserves_ScanInv _ _ _ rfl rfl
  apply emitAt_preserves_ScanInv
  · exact ScanInv_mono h
      (ScanHelpers.collectPlainScalarLoop_preserves_tokens _ _ _ _ _ _ _ _ heq)
      (collectPlainScalarLoop_offset_ge _ _ _ _ _ _ _ _ heq)
  · show s.currentPos.offset ≤ _
    simp only [ScannerState.currentPos]
    exact collectPlainScalarLoop_offset_ge _ _ _ _ _ _ _ _ heq
  · intro ⟨i, hi⟩
    have h_tok := ScanHelpers.collectPlainScalarLoop_preserves_tokens _ _ _ _ _ _ _ _ heq
    simp only [h_tok] at hi ⊢
    show s.tokens[i].pos.offset ≤ s.currentPos.offset
    simp only [ScannerState.currentPos]
    exact h.2 ⟨i, hi⟩

-- scanBlockScalarBody preserves ScanInv (Except function).
-- Requires: ScanInv for s_after_newline state, startPos.offset ≤ s_after_newline.offset,
-- all tokens ≤ startPos.offset.
theorem scanBlockScalarBody_preserves_ScanInv (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState)
    (h_inv : ScanInv s_nl) (h_tok : s_nl.tokens = s_orig.tokens)
    (h_pos : startPos.offset ≤ s_nl.offset)
    (h_ge : ∀ i : Fin s_orig.tokens.size, s_orig.tokens[i].pos.offset ≤ startPos.offset)
    (h_ok : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') : ScanInv s' := by
  unfold scanBlockScalarBody at h_ok
  simp only [] at h_ok
  -- All successful branches produce { (cbs ...).snd.emitAt startPos _ with simpleKeyAllowed := true, simpleKey := _ }
  -- where cbs = collectBlockScalarLoop. Factor out the common tail.
  -- Step 1: Handle match on explicitOffset and autoDetectErr? to get to the ok branch
  repeat (any_goals (split at h_ok))
  all_goals (try contradiction)
  -- Step 2: In each ok branch, extract the result
  all_goals simp only [Except.ok.injEq] at h_ok
  all_goals subst h_ok
  -- Step 3: Prove ScanInv for the result
  all_goals apply field_update_preserves_ScanInv _ _ _ rfl rfl
  all_goals apply emitAt_preserves_ScanInv
  -- h1: ScanInv of collectBlockScalarLoop result
  all_goals first
    | (exact ScanInv_mono h_inv
         (ScanHelpers.collectBlockScalarLoop_preserves_tokens _ _ _ _ _)
         (collectBlockScalarLoop_offset_ge _ _ _ _ _))
    | (exact Nat.le_trans h_pos (collectBlockScalarLoop_offset_ge _ _ _ _ _))
    | (intro ⟨i, hi⟩
       simp only [ScanHelpers.collectBlockScalarLoop_preserves_tokens, h_tok] at hi ⊢
       exact h_ge ⟨i, hi⟩)

-- scanBlockScalar preserves ScanInv (Except function).
theorem scanBlockScalar_preserves_ScanInv (s s' : ScannerState)
    (h : ScanInv s) (h_ok : scanBlockScalar s = .ok s') : ScanInv s' := by
  unfold scanBlockScalar at h_ok
  simp only [] at h_ok
  split at h_ok
  · contradiction  -- scanBlockScalarConsumeNewline error
  · -- scanBlockScalarConsumeNewline ok
    rename_i s_nl heq_nl
    -- Build the invariant chain:
    -- s → advance → parseBlockHeaderLoop → skipWhitespace → scanBlockScalarSkipComment → consumeNewline → body
    have h_adv := advance_preserves_ScanInv s h
    have h_hdr_tok := ScanHelpers.parseBlockHeaderLoop_preserves_tokens s.advance .clip none 2
    have h_hdr_ge := parseBlockHeaderLoop_offset_ge s.advance .clip none 2
    have h_inv_hdr : ScanInv (parseBlockHeaderLoop s.advance .clip none 2).snd.snd :=
      ScanInv_mono h_adv h_hdr_tok h_hdr_ge
    have h_sw_tok := skipWhitespace_preserves_tokens (parseBlockHeaderLoop s.advance .clip none 2).snd.snd
    have h_sw_ge := skipWhitespace_offset_ge (parseBlockHeaderLoop s.advance .clip none 2).snd.snd
    have h_inv_sw : ScanInv (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).snd.snd) :=
      ScanInv_mono h_inv_hdr h_sw_tok h_sw_ge
    have h_sc_tok := ScanHelpers.scanBlockScalarSkipComment_preserves_tokens (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).snd.snd)
    have h_sc_ge := scanBlockScalarSkipComment_offset_ge (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).snd.snd)
    have h_inv_sc : ScanInv (scanBlockScalarSkipComment (skipWhitespace (parseBlockHeaderLoop s.advance .clip none 2).snd.snd)) :=
      ScanInv_mono h_inv_sw h_sc_tok h_sc_ge
    have h_nl_tok := ScanHelpers.scanBlockScalarConsumeNewline_preserves_tokens _ _ heq_nl
    have h_nl_ge := scanBlockScalarConsumeNewline_offset_ge _ _ heq_nl
    have h_inv_nl : ScanInv s_nl := ScanInv_mono h_inv_sc h_nl_tok h_nl_ge
    -- s_nl.tokens = s.tokens (chain through all steps)
    have h_chain_tok : s_nl.tokens = s.tokens := by
      rw [h_nl_tok, h_sc_tok, h_sw_tok, h_hdr_tok, advance_preserves_tokens]
    -- startPos = s.currentPos, so startPos.offset = s.offset ≤ s_nl.offset
    have h_chain_off : s.currentPos.offset ≤ s_nl.offset := by
      simp only [ScannerState.currentPos]
      exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
        (Nat.le_trans h_hdr_ge (Nat.le_trans h_sw_ge (Nat.le_trans h_sc_ge h_nl_ge)))
    -- all tokens in s ≤ s.currentPos.offset = s.offset
    have h_chain_ge : ∀ i : Fin s.tokens.size, s.tokens[i].pos.offset ≤ s.currentPos.offset := by
      intro ⟨i, hi⟩; simp only [ScannerState.currentPos]; exact h.2 ⟨i, hi⟩
    exact scanBlockScalarBody_preserves_ScanInv s s_nl _ _ _ s.currentPos s'
      h_inv_nl h_chain_tok h_chain_off h_chain_ge h_ok

-- Phase 2e dispatcher: dispatchContent preserves ScanInv.
theorem dispatchContent_preserves_ScanInv (s : ScannerState) (c : Char)
    (h : ScanInv s) (s' : ScannerState)
    (h_ok : scanNextToken_dispatchContent s c = .ok s') : ScanInv s' := by
  unfold scanNextToken_dispatchContent at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  -- c == '&'
  split at h_ok
  · -- scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h_ok
    cases result with
    | error e => simp at h_ok
    | ok s_a =>
      simp only [Except.ok.injEq] at h_ok; subst h_ok
      exact field_update_preserves_ScanInv _ _
        (scanAnchorOrAlias_preserves_ScanInv s true h s_a h_anch) rfl rfl
  · -- c == '*'
    split at h_ok
    · -- inner split: alias validation check
      split at h_ok
      · contradiction
      · -- scanAnchorOrAlias bind
        generalize h_anch : scanAnchorOrAlias s false = result at h_ok
        cases result with
        | error e => simp at h_ok
        | ok s_a =>
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact scanAnchorOrAlias_preserves_ScanInv s false h s_a h_anch
    · -- c == '!'
      split at h_ok
      · -- scanTag bind
        generalize h_tag : scanTag s = result at h_ok
        cases result with
        | error e => simp at h_ok
        | ok s_t =>
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          exact scanTag_preserves_ScanInv s h s_t h_tag
      · -- c == '|' || c == '>'
        split at h_ok
        · split at h_ok <;> try contradiction
          simp only [Except.ok.injEq] at h_ok; subst h_ok
          rename_i s_bs h_bs
          exact scanBlockScalar_preserves_ScanInv s s_bs h h_bs
        · -- c == '"'
          split at h_ok
          · split at h_ok <;> try contradiction
            rename_i s_dq h_dq
            -- simpleKey endLine update: field_update only changes simpleKey, not tokens/offset
            split at h_ok
            · simp only [Except.ok.injEq] at h_ok; subst h_ok
              exact field_update_preserves_ScanInv _ _
                (scanDoubleQuoted_preserves_ScanInv s s_dq h h_dq) rfl rfl
            · simp only [Except.ok.injEq] at h_ok; subst h_ok
              exact scanDoubleQuoted_preserves_ScanInv s s_dq h h_dq
          · -- c == '\''
            split at h_ok
            · split at h_ok <;> try contradiction
              rename_i s_sq h_sq
              split at h_ok
              · simp only [Except.ok.injEq] at h_ok; subst h_ok
                exact field_update_preserves_ScanInv _ _
                  (scanSingleQuoted_preserves_ScanInv s s_sq h h_sq) rfl rfl
              · simp only [Except.ok.injEq] at h_ok; subst h_ok
                exact scanSingleQuoted_preserves_ScanInv s s_sq h h_sq
            · -- canStartPlainScalar
              split at h_ok
              · split at h_ok <;> try contradiction
                simp only [Except.ok.injEq] at h_ok; subst h_ok
                rename_i s_ps h_ps
                exact scanPlainScalar_preserves_ScanInv s s_ps h h_ps
              · -- error: unexpectedChar
                simp at h_ok

/-!
### SimpleKeyValid: simpleKey bookkeeping invariant

When `simpleKey.possible` is true, the saved `tokenIndex` is within
bounds (or one past the end, indicating the candidate scalar slot
hasn't been emitted yet).  This is the bookkeeping link between
`simpleKey` metadata and the token array.

**Initiative 3 / J.2 step 5 cutover**: the pre-cutover invariant also
asserted `tokens[tokenIndex].pos = simpleKey.pos` and `tokens[tokenIndex+1].pos =
simpleKey.pos`, established by the two placeholder pushes in
`saveSimpleKey`.  Post-cutover those placeholders are gone — the
candidate scalar fills slot `tokenIndex` on its own emit (so
`tokenIndex = tokens.size` momentarily after `saveSimpleKey`, until
the dispatch in the same `scanNextToken` call appends).  The
position-equality conjuncts are no longer load-bearing on any consumer
(`scanValuePrepare_preserves_ScanInv` and friends silence their
`h_sk` argument with `let _ := h_sk` per the J.2 cutover comments),
so this file weakens `SimpleKeyValid` to a bound-only invariant.
The `h_sk` arguments are kept on the consumers' signatures for
J.4 cleanup.
-/

/-- The simpleKey validity condition: when the simple key is possible,
    the saved `tokenIndex` is at most `tokens.size` (limbo case allowed
    between `saveSimpleKey` and the candidate scalar's emit). -/
def SimpleKeyValid (s : ScannerState) : Prop :=
  s.simpleKey.possible = true → s.simpleKey.tokenIndex ≤ s.tokens.size

-- SimpleKeyValid is vacuously true when possible = false.
theorem SimpleKeyValid_of_not_possible (s : ScannerState)
    (h : s.simpleKey.possible = false) : SimpleKeyValid s :=
  fun h_poss => absurd h_poss (by simp [h])

-- SimpleKeyValid transfers across simpleKey.possible := false updates.
theorem SimpleKeyValid_of_cleared (_s : ScannerState)
    (s' : ScannerState)
    (h : s'.simpleKey.possible = false) : SimpleKeyValid s' :=
  SimpleKeyValid_of_not_possible s' h

-- SimpleKeyValid is monotone: preserved when tokens grow and existing entries unchanged.
-- Initiative 3 / J.2 step 5 cutover: the `h_sk`/`h_pref` arguments are
-- retained for callers' benefit, but with the bound-only invariant the
-- monotone proof reduces to `omega` over `tokenIndex ≤ s.size ≤ s'.size`.
theorem SimpleKeyValid_mono (s s' : ScannerState)
    (h_skv : SimpleKeyValid s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (_h_pref : ∀ i (h : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    SimpleKeyValid s' := by
  intro h_poss
  rw [h_sk] at h_poss ⊢
  have hb := h_skv h_poss
  omega

-- saveSimpleKey preserves SimpleKeyValid.
--
-- **Initiative 3 / J.2 step 5 cutover**: the `simpleKeyAllowed` branch
-- records `tokenIndex := s.tokens.size` (the candidate scalar's
-- upcoming slot) without growing `tokens`.  The bound `tokenIndex ≤
-- tokens.size` therefore holds with equality after the save.  The
-- other two branches return `s` unchanged.
theorem saveSimpleKey_preserves_SimpleKeyValid (s : ScannerState)
    (h_skv : SimpleKeyValid s) : SimpleKeyValid (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · exact h_skv
  · split
    · intro _; simp  -- simpleKeyAllowed: tokenIndex = tokens.size, bound holds with equality
    · exact h_skv

-- skipToContent preserves SimpleKeyValid (preserves simpleKey and tokens exactly).
theorem skipToContent_preserves_SimpleKeyValid (s s' : ScannerState)
    (h : skipToContent s = .ok s') (h_skv : SimpleKeyValid s) : SimpleKeyValid s' := by
  have h_sk := skipToContent_preserves_simpleKey s s' h
  have h_tok := skipToContent_preserves_tokens s s' h
  unfold SimpleKeyValid at h_skv ⊢
  intro h_poss
  rw [h_sk] at h_poss
  rw [h_tok, h_sk]
  exact h_skv h_poss

-- unwindIndents preserves SimpleKeyValid (preserves simpleKey, only appends tokens).
theorem unwindIndents_preserves_SimpleKeyValid (s : ScannerState) (col : Int)
    (h_skv : SimpleKeyValid s) : SimpleKeyValid (unwindIndents s col) :=
  SimpleKeyValid_mono s _ h_skv
    (unwindIndents_preserves_simpleKey s col)
    (unwindIndents_adds_tokens s col)
    (fun i hi => unwindIndents_preserves_prefix s col i hi)

-- preprocess preserves SimpleKeyValid.
theorem preprocess_preserves_SimpleKeyValid (s : ScannerState) (s' : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s', c)))
    (h_skv : SimpleKeyValid s) : SimpleKeyValid s' := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_skv_skip := skipToContent_preserves_SimpleKeyValid s s_skip h_skip h_skv
    split at h
    · simp at h
    · split at h
      · -- needIndentCheck path with unwindIndents
        split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            apply saveSimpleKey_preserves_SimpleKeyValid
            show SimpleKeyValid { unwindIndents s_skip s_skip.col with needIndentCheck := false }
            exact unwindIndents_preserves_SimpleKeyValid s_skip s_skip.col h_skv_skip
      · -- no needIndentCheck
        split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact saveSimpleKey_preserves_SimpleKeyValid s_skip h_skv_skip

-- allowDirectives update preserves SimpleKeyValid.
theorem allowDir_ite_preserves_SimpleKeyValid (s : ScannerState)
    (h_skv : SimpleKeyValid s) :
    SimpleKeyValid (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true } else s) := by
  split <;> exact h_skv

theorem allowDir_ite_preserves_ScanInv (s : ScannerState)
    (h_inv : ScanInv s) :
    ScanInv (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true } else s) := by
  split
  · exact field_update_preserves_ScanInv _ _ h_inv rfl rfl
  · exact h_inv

-- scanValueClearKey transfers SimpleKeyValid to h_sk condition.
theorem SimpleKeyValid_implies_scanValue_h_sk (s : ScannerState) (h_skv : SimpleKeyValid s) :
    (scanValueClearKey s).simpleKey.possible = true →
      (scanValueClearKey s).simpleKey.tokenIndex ≤ (scanValueClearKey s).tokens.size := by
  cases scanValueClearKey_identity_or_clear s with
  | inl h_eq => rw [h_eq]; exact h_skv
  | inr h_cl => intro h_poss; rw [h_cl.1] at h_poss; contradiction

/-!
### SimpleKeyStackValid: validity of stacked simple keys

Flow collection openers (`[`, `{`) push the current simple key onto the
stack. Closers (`]`, `}`) restore it. Between push and pop, the token
array only grows and existing entries are never modified (only extended).
Therefore, the token-position equalities that held at push time continue
to hold at pop time.
-/

/-- Validity of every simple key entry on the stack.
    **Initiative 3 / J.2 step 5 cutover**: weakened to a bound-only
    invariant in lockstep with `SimpleKeyValid` (see comment there). -/
def SimpleKeyStackValid (s : ScannerState) : Prop :=
  ∀ j (h : j < s.simpleKeyStack.size),
    s.simpleKeyStack[j].possible = true →
    s.simpleKeyStack[j].tokenIndex ≤ s.tokens.size

/-- Combined simple key validity for both current and stacked keys. -/
def AllKeysValid (s : ScannerState) : Prop :=
  SimpleKeyValid s ∧ SimpleKeyStackValid s

-- SimpleKeyStackValid is monotone: preserved when tokens grow and existing entries unchanged.
-- Initiative 3 / J.2 step 5 cutover: bound-only invariant, h_pref retained for callers.
theorem SimpleKeyStackValid_mono (s s' : ScannerState)
    (h_ssv : SimpleKeyStackValid s)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (_h_pref : ∀ i (h : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    SimpleKeyStackValid s' := by
  intro j hj h_poss
  have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : s'.simpleKeyStack[j] = s.simpleKeyStack[j]'hj_s := by
    simp [h_stack]
  rw [h_get] at h_poss ⊢
  have hb := h_ssv j hj_s h_poss
  omega

-- Initiative 3 / J.2 step 5 cutover: with the bound-only invariant, the `_pos`
-- variant is structurally identical to `_mono`; both are kept for caller
-- ergonomics (callers in different branches have different .pos witnesses).
theorem SimpleKeyStackValid_mono_pos (s s' : ScannerState)
    (h_ssv : SimpleKeyStackValid s)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (_h_pos : ∀ i (h : i < s.tokens.size), (s'.tokens[i]'(by omega)).pos = s.tokens[i].pos) :
    SimpleKeyStackValid s' := by
  intro j hj h_poss
  have hj_s : j < s.simpleKeyStack.size := by rw [← h_stack]; exact hj
  have h_get : s'.simpleKeyStack[j] = s.simpleKeyStack[j]'hj_s := by
    simp [h_stack]
  rw [h_get] at h_poss ⊢
  have hb := h_ssv j hj_s h_poss
  omega

-- AllKeysValid is monotone under the same conditions.
theorem AllKeysValid_mono (s s' : ScannerState)
    (h_akv : AllKeysValid s)
    (h_sk : s'.simpleKey = s.simpleKey)
    (h_stack : s'.simpleKeyStack = s.simpleKeyStack)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (h_pref : ∀ i (h : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    AllKeysValid s' :=
  ⟨SimpleKeyValid_mono s s' h_akv.1 h_sk h_mono h_pref,
   SimpleKeyStackValid_mono s s' h_akv.2 h_stack h_mono h_pref⟩

-- AllKeysValid when current key cleared (possible = false).
theorem AllKeysValid_of_cleared_current (_s : ScannerState) (s' : ScannerState)
    (h_poss : s'.simpleKey.possible = false)
    (h_ssv : SimpleKeyStackValid s')
    : AllKeysValid s' :=
  ⟨SimpleKeyValid_of_not_possible s' h_poss, h_ssv⟩

-- skipToContent preserves SimpleKeyStackValid.
theorem skipToContent_preserves_SimpleKeyStackValid (s s' : ScannerState)
    (h : skipToContent s = .ok s') (h_ssv : SimpleKeyStackValid s) : SimpleKeyStackValid s' :=
  have h_tok := skipToContent_preserves_tokens s s' h
  SimpleKeyStackValid_mono s s' h_ssv
    (skipToContent_preserves_simpleKeyStack s s' h)
    (by simp [h_tok])
    (fun i hi => by simp [h_tok])

-- unwindIndents preserves SimpleKeyStackValid.
theorem unwindIndents_preserves_SimpleKeyStackValid (s : ScannerState) (col : Int)
    (h_ssv : SimpleKeyStackValid s) : SimpleKeyStackValid (unwindIndents s col) :=
  SimpleKeyStackValid_mono s _ h_ssv
    (unwindIndents_preserves_simpleKeyStack s col)
    (unwindIndents_adds_tokens s col)
    (fun i hi => unwindIndents_preserves_prefix s col i hi)

-- saveSimpleKey preserves SimpleKeyStackValid.
--
-- **Initiative 3 / J.2 step 5 cutover**: post-cutover saveSimpleKey
-- leaves both `simpleKeyStack` and `tokens` unchanged in every branch,
-- so the invariant is preserved trivially.
theorem saveSimpleKey_preserves_SimpleKeyStackValid (s : ScannerState)
    (h_ssv : SimpleKeyStackValid s) : SimpleKeyStackValid (saveSimpleKey s) := by
  unfold saveSimpleKey
  split
  · exact h_ssv
  · split
    · exact h_ssv
    · exact h_ssv

-- preprocess preserves AllKeysValid.
theorem preprocess_preserves_AllKeysValid (s s' : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s', c)))
    (h_akv : AllKeysValid s) : AllKeysValid s' :=
  ⟨preprocess_preserves_SimpleKeyValid s s' c h h_akv.1,
   by -- trace through preprocess: skipToContent → unwindIndents → saveSimpleKey
      unfold scanNextToken_preprocess at h
      simp only [bind, Except.bind, pure, Except.pure] at h
      split at h
      · contradiction
      · rename_i s_skip h_skip
        have h_ssv_skip := skipToContent_preserves_SimpleKeyStackValid s s_skip h_skip h_akv.2
        split at h
        · simp at h
        · split at h
          · split at h
            · contradiction
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, _⟩ := h
                apply saveSimpleKey_preserves_SimpleKeyStackValid
                show SimpleKeyStackValid { unwindIndents s_skip s_skip.col with needIndentCheck := false }
                exact unwindIndents_preserves_SimpleKeyStackValid s_skip s_skip.col h_ssv_skip
          · split at h
            · contradiction
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, _⟩ := h
                exact saveSimpleKey_preserves_SimpleKeyStackValid s_skip h_ssv_skip⟩

-- allowDirectives update preserves AllKeysValid.
theorem allowDir_ite_preserves_AllKeysValid (s : ScannerState)
    (h_akv : AllKeysValid s) :
    AllKeysValid (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true } else s) := by
  split <;> exact h_akv

-- dispatchStructural: all branches either clear possible or preserve simpleKey+stack.
theorem dispatchStructural_preserves_AllKeysValid (s : ScannerState) (c : Char)
    (s' : ScannerState) (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (h_akv : AllKeysValid s) : AllKeysValid s' := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact AllKeysValid_of_cleared_current s _ (scanDocumentStart_clears_simpleKey s)
            (SimpleKeyStackValid_mono s _ h_akv.2
              (scanDocumentStart_preserves_simpleKeyStack s)
              (by have := ScanHelpers.scanDocumentStart_adds_tokens s; omega)
              (fun i hi => ScanHelpers.scanDocumentStart_preserves_prefix s i hi))
        · split at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              rename_i s_de h_de
              exact AllKeysValid_of_cleared_current s _ (scanDocumentEnd_clears_simpleKey s s_de h_de)
                (SimpleKeyStackValid_mono s _ h_akv.2
                  (scanDocumentEnd_preserves_simpleKeyStack s s_de h_de)
                  (by have := ScanHelpers.scanDocumentEnd_adds_tokens s s_de h_de; omega)
                  (fun i hi => ScanHelpers.scanDocumentEnd_preserves_prefix s s_de h_de i hi))
          · split at h
            · split at h
              · simp at h
              · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                rename_i s_dir h_dir
                exact AllKeysValid_mono s _ h_akv
                  (scanDirective_preserves_simpleKey s s_dir h_dir)
                  (scanDirective_preserves_simpleKeyStack s s_dir h_dir)
                  (ScanHelpers.scanDirective_monotonic s s_dir h_dir)
                  (fun i hi => ScanHelpers.scanDirective_preserves_prefix s s_dir h_dir i hi)
            · simp at h
  · split at h
    · simp at h
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact AllKeysValid_of_cleared_current s _ (scanDocumentStart_clears_simpleKey s)
          (SimpleKeyStackValid_mono s _ h_akv.2
            (scanDocumentStart_preserves_simpleKeyStack s)
            (by have := ScanHelpers.scanDocumentStart_adds_tokens s; omega)
            (fun i hi => ScanHelpers.scanDocumentStart_preserves_prefix s i hi))
      · split at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
            rename_i s_de h_de
            exact AllKeysValid_of_cleared_current s _ (scanDocumentEnd_clears_simpleKey s s_de h_de)
              (SimpleKeyStackValid_mono s _ h_akv.2
                (scanDocumentEnd_preserves_simpleKeyStack s s_de h_de)
                (by have := ScanHelpers.scanDocumentEnd_adds_tokens s s_de h_de; omega)
                (fun i hi => ScanHelpers.scanDocumentEnd_preserves_prefix s s_de h_de i hi))
        · split at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              rename_i s_dir h_dir
              exact AllKeysValid_mono s _ h_akv
                (scanDirective_preserves_simpleKey s s_dir h_dir)
                (scanDirective_preserves_simpleKeyStack s s_dir h_dir)
                (ScanHelpers.scanDirective_monotonic s s_dir h_dir)
                (fun i hi => ScanHelpers.scanDirective_preserves_prefix s s_dir h_dir i hi)
          · simp at h

-- Helper: flow start preserves AllKeysValid.
-- Pushes current key to stack (valid → stays valid), clears current.
theorem flowStart_preserves_AllKeysValid (s s' : ScannerState)
    (h_akv : AllKeysValid s)
    (h_cleared : s'.simpleKey.possible = false)
    (h_pushed : s'.simpleKeyStack = s.simpleKeyStack.push s.simpleKey)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (_h_pref : ∀ i (hi : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    AllKeysValid s' := by
  constructor
  · exact SimpleKeyValid_of_not_possible _ h_cleared
  · intro j hj h_poss
    have hj_sz : j < s.simpleKeyStack.size + 1 := by
      rw [h_pushed, Array.size_push] at hj; exact hj
    have h_get : s'.simpleKeyStack[j] = (s.simpleKeyStack.push s.simpleKey)[j]'(by rw [Array.size_push]; exact hj_sz) := by
      simp [h_pushed]
    rw [h_get] at h_poss ⊢
    by_cases hlt : j < s.simpleKeyStack.size
    · -- existing stack entry
      rw [Array.getElem_push_lt hlt] at h_poss ⊢
      have hb := h_akv.2 j hlt h_poss
      omega
    · -- newly pushed entry (j = s.simpleKeyStack.size)
      have hj_eq : j = s.simpleKeyStack.size := by omega
      subst hj_eq
      rw [Array.getElem_push_eq] at h_poss ⊢
      have hb := h_akv.1 h_poss
      omega
-- Restores current key from stack top (valid), pops stack.
theorem flowEnd_preserves_AllKeysValid (s s' : ScannerState)
    (h_akv : AllKeysValid s)
    (h_restored : s'.simpleKey = s.simpleKeyStack.back?.getD {})
    (h_popped : s'.simpleKeyStack = s.simpleKeyStack.pop)
    (h_mono : s'.tokens.size ≥ s.tokens.size)
    (_h_pref : ∀ i (hi : i < s.tokens.size), s'.tokens[i]'(by omega) = s.tokens[i]) :
    AllKeysValid s' := by
  constructor
  · -- current key: restored from stack top
    intro h_poss
    rw [h_restored] at h_poss ⊢
    by_cases h_size : s.simpleKeyStack.size > 0
    · -- stack non-empty
      have h_bound : s.simpleKeyStack.size - 1 < s.simpleKeyStack.size := by omega
      have h_get : (s.simpleKeyStack.back?.getD {}) =
          s.simpleKeyStack[s.simpleKeyStack.size - 1]'h_bound := by
        simp [Array.back?, h_bound]
      rw [h_get] at h_poss ⊢
      have hb := h_akv.2 (s.simpleKeyStack.size - 1) h_bound h_poss
      omega
    · -- stack empty: back? = none, getD = {}, possible = false → contradiction
      have h_empty : s.simpleKeyStack.size = 0 := by omega
      simp [Array.back?, h_empty] at h_poss
  · -- stack: popped (all remaining entries were valid)
    intro j hj h_poss
    have hj' : j < s.simpleKeyStack.size := by
      simp [h_popped, Array.size_pop] at hj; omega
    have h_get : s'.simpleKeyStack[j] = s.simpleKeyStack[j]'hj' := by
      simp [h_popped, Array.getElem_pop]
    rw [h_get] at h_poss ⊢
    have hb := h_akv.2 j hj' h_poss
    omega
theorem dispatchFlowIndicators_preserves_AllKeysValid (s : ScannerState) (c : Char)
    (s' : ScannerState) (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (h_akv : AllKeysValid s) : AllKeysValid s' := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact flowStart_preserves_AllKeysValid s _ h_akv
      (scanFlowSequenceStart_simpleKey_cleared s)
      (scanFlowSequenceStart_stack_pushed s)
      (by have := scanFlowSequenceStart_adds_one_token s; omega)
      (fun i hi => ScanHelpers.scanFlowSequenceStart_preserves_prefix s i hi)
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact flowEnd_preserves_AllKeysValid s _ h_akv
            (scanFlowSequenceEnd_simpleKey_restored s)
            (scanFlowSequenceEnd_stack_popped s)
            (by have := scanFlowSequenceEnd_adds_one_token s; omega)
            (fun i hi => ScanHelpers.scanFlowSequenceEnd_preserves_prefix s i hi)
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact flowStart_preserves_AllKeysValid s _ h_akv
          (scanFlowMappingStart_simpleKey_cleared s)
          (scanFlowMappingStart_stack_pushed s)
          (by have := scanFlowMappingStart_adds_one_token s; omega)
          (fun i hi => ScanHelpers.scanFlowMappingStart_preserves_prefix s i hi)
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              exact flowEnd_preserves_AllKeysValid s _ h_akv
                (scanFlowMappingEnd_simpleKey_restored s)
                (scanFlowMappingEnd_stack_popped s)
                (by have := scanFlowMappingEnd_adds_one_token s; omega)
                (fun i hi => ScanHelpers.scanFlowMappingEnd_preserves_prefix s i hi)
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                exact AllKeysValid_mono s _ h_akv
                  (scanFlowEntry_preserves_simpleKey s _ h_entry)
                  (scanFlowEntry_preserves_simpleKeyStack s _ h_entry)
                  (by have := ScanHelpers.scanFlowEntry_adds_one_token s _ h_entry; omega)
                  (fun i hi => ScanHelpers.scanFlowEntry_preserves_prefix s _ h_entry i hi)
          · simp at h

-- dispatchBlockIndicators: blockEntry preserves, key/value clear possible.
theorem dispatchBlockIndicators_preserves_AllKeysValid (s : ScannerState) (c : Char)
    (s' : ScannerState) (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (h_akv : AllKeysValid s) : AllKeysValid s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- c == '-' && ... : scanBlockEntry (preserves key+stack)
    split at h
    · simp at h
    · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      rename_i s_be h_be
      exact AllKeysValid_mono s _ h_akv
        (scanBlockEntry_preserves_simpleKey s s_be h_be)
        (scanBlockEntry_preserves_simpleKeyStack s s_be h_be)
        (by have := ScanHelpers.scanBlockEntry_adds_tokens s s_be h_be; omega)
        (fun i hi => ScanHelpers.scanBlockEntry_preserves_prefix s s_be h_be i hi)
  · -- c == '?' ... : scanKey (clears key, preserves stack)
    split at h
    · split at h
      · simp at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        rename_i s_k h_k
        exact AllKeysValid_of_cleared_current s _ (scanKey_clears_simpleKey s s_k h_k)
          (SimpleKeyStackValid_mono s _ h_akv.2
            (scanKey_preserves_simpleKeyStack s s_k h_k)
            (by have := scanKey_adds_one_token s s_k h_k; omega)
            (fun i hi => ScanHelpers.scanKey_preserves_prefix s s_k h_k i hi))
    · -- c == ':' ... : scanValue (clears key, preserves stack, pos-preserving)
      split at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          rename_i s_v h_v
          exact AllKeysValid_of_cleared_current s _ (scanValue_clears_simpleKey s s_v h_v)
            (SimpleKeyStackValid_mono_pos s _ h_akv.2
              (scanValue_preserves_simpleKeyStack s s_v h_v)
              (by have := scanValue_adds_tokens s s_v h_v; omega)
              (fun i hi => ScanHelpers.scanValue_preserves_all_pos s s_v h_v h_akv.1 i hi))
      · simp at h

-- dispatchContent: preserves simpleKey (all branches) and stack.
theorem dispatchContent_preserves_AllKeysValid (s : ScannerState) (c : Char)
    (s' : ScannerState) (h : scanNextToken_dispatchContent s c = .ok s')
    (h_akv : AllKeysValid s) : AllKeysValid s' := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · -- c == '&': anchor with definedAnchors update
    split at h
    · contradiction
    · simp only [Except.ok.injEq] at h; subst h
      have h_akv_base := AllKeysValid_mono s _ h_akv
        (scanAnchorOrAlias_preserves_simpleKey s true _ (by assumption))
        (scanAnchorOrAlias_preserves_simpleKeyStack s true _ (by assumption))
        (by have := ScanHelpers.scanAnchorOrAlias_adds_one_token s true _ (by assumption); omega)
        (fun i hi => ScanHelpers.scanAnchorOrAlias_preserves_prefix s true _ (by assumption) i hi)
      exact AllKeysValid_mono _ _ h_akv_base rfl rfl
        (Nat.le_refl _) (fun i hi => rfl)
  · split at h
    · -- c == '*': alias (with alias validation check)
      split at h
      · contradiction
      · split at h
        · contradiction
        · simp only [Except.ok.injEq] at h; subst h
          exact AllKeysValid_mono s _ h_akv
            (scanAnchorOrAlias_preserves_simpleKey s false _ (by assumption))
            (scanAnchorOrAlias_preserves_simpleKeyStack s false _ (by assumption))
            (by have := ScanHelpers.scanAnchorOrAlias_adds_one_token s false _ (by assumption); omega)
            (fun i hi => ScanHelpers.scanAnchorOrAlias_preserves_prefix s false _ (by assumption) i hi)
    · split at h
      · -- c == '!': tag
        split at h
        · contradiction
        · simp only [Except.ok.injEq] at h; subst h
          exact AllKeysValid_mono s _ h_akv
            (scanTag_preserves_simpleKey s _ (by assumption))
            (scanTag_preserves_simpleKeyStack s _ (by assumption))
            (by have := ScanHelpers.scanTag_adds_one_token s _ (by assumption); omega)
            (fun i hi => ScanHelpers.scanTag_preserves_prefix s _ (by assumption) i hi)
      · split at h
        · -- c == '|' || c == '>': block scalar (clears key)
          split at h <;> try contradiction
          simp only [Except.ok.injEq] at h; subst h
          rename_i s_bs h_bs
          exact AllKeysValid_of_cleared_current s _ (scanBlockScalar_clears_simpleKey s s_bs h_bs)
            (SimpleKeyStackValid_mono s _ h_akv.2
              (scanBlockScalar_preserves_simpleKeyStack s s_bs h_bs)
              (by have := ScanHelpers.scanBlockScalar_adds_one_token s s_bs h_bs; omega)
              (fun i hi => ScanHelpers.scanBlockScalar_preserves_prefix s s_bs h_bs i hi))
        · split at h
          · -- c == '"': double quoted (preserves key+stack, possibly endLine update)
            split at h <;> try contradiction
            rename_i s_dq h_dq
            have h_akv_dq := AllKeysValid_mono s s_dq h_akv
              (scanDoubleQuoted_preserves_simpleKey s s_dq h_dq)
              (scanDoubleQuoted_preserves_simpleKeyStack s s_dq h_dq)
              (by have := ScanHelpers.scanDoubleQuoted_adds_one_token s s_dq h_dq; omega)
              (fun i hi => ScanHelpers.scanDoubleQuoted_preserves_prefix s s_dq h_dq i hi)
            split at h
            · simp only [Except.ok.injEq] at h; subst h; exact h_akv_dq
            · simp only [Except.ok.injEq] at h; subst h; exact h_akv_dq
          · split at h
            · -- c == '\'': single quoted (preserves key+stack, possibly endLine update)
              split at h <;> try contradiction
              rename_i s_sq h_sq
              have h_akv_sq := AllKeysValid_mono s s_sq h_akv
                (scanSingleQuoted_preserves_simpleKey s s_sq h_sq)
                (scanSingleQuoted_preserves_simpleKeyStack s s_sq h_sq)
                (by have := ScanHelpers.scanSingleQuoted_adds_one_token s s_sq h_sq; omega)
                (fun i hi => ScanHelpers.scanSingleQuoted_preserves_prefix s s_sq h_sq i hi)
              split at h
              · simp only [Except.ok.injEq] at h; subst h; exact h_akv_sq
              · simp only [Except.ok.injEq] at h; subst h; exact h_akv_sq
            · split at h
              · -- plain scalar
                split at h <;> try contradiction
                simp only [Except.ok.injEq] at h; subst h
                rename_i s_ps h_ps
                exact AllKeysValid_mono s _ h_akv
                  (scanPlainScalar_preserves_simpleKey s s_ps h_ps)
                  (scanPlainScalar_preserves_simpleKeyStack s s_ps h_ps)
                  (by have := ScanHelpers.scanPlainScalar_adds_one_token s s_ps h_ps; omega)
                  (fun i hi => ScanHelpers.scanPlainScalar_preserves_prefix s s_ps h_ps i hi)
              · -- error
                simp at h

/-!
### scanNextToken preserves AllKeysValid

The proof case-splits on which dispatcher handles the character:
- Dispatchers that clear `possible` produce `SimpleKeyValid` vacuously.
- Dispatchers that preserve `simpleKey` and only append tokens preserve it
  via monotonicity.
- Flow-start pushes the valid current key onto the stack and clears current.
- Flow-end restores a valid key from the stack.
-/

-- Helper: after structural dispatch returns none, the remaining dispatchers preserve AllKeysValid.
theorem scanNextToken_postStructural_preserves_AllKeysValid
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h_akv : AllKeysValid s)
    (h_ok : (match scanNextToken_dispatchFlowIndicators s c with
      | Except.ok (some s') => Except.ok (some s')
      | Except.ok none =>
        match scanNextToken_dispatchBlockIndicators s c with
        | Except.ok (some s') => Except.ok (some s')
        | Except.ok none => (scanNextToken_dispatchContent s c).map some
        | Except.error e => Except.error e
      | Except.error e => Except.error e) = Except.ok (some s')) :
    AllKeysValid s' := by
  split at h_ok
  · -- flow = .ok (some _)
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchFlowIndicators_preserves_AllKeysValid s c _ (by assumption) h_akv
  · -- flow = .ok none → try block
    split at h_ok
    · -- block = .ok (some _)
      simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchBlockIndicators_preserves_AllKeysValid s c _ (by assumption) h_akv
    · -- block = .ok none → try content
      unfold Except.map at h_ok
      split at h_ok
      · simp at h_ok  -- content = .error
      · -- content = .ok v✝
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_AllKeysValid s c _ (by assumption) h_akv
    · -- block = .error
      simp at h_ok
  · -- flow = .error
    simp at h_ok

theorem scanNextToken_preserves_AllKeysValid :
    ∀ (s s' : ScannerState),
      AllKeysValid s → scanNextToken s = .ok (some s') → AllKeysValid s' := by
  intro s s' h_akv h_ok
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> (try (simp at h_ok; done)) -- preprocess Except: .error closes
  split at h_ok <;> (try (simp at h_ok; done)) -- preprocess Option: none closes
  rename_i s2 c h_pre
  have h_akv2 := preprocess_preserves_AllKeysValid s s2 c h_pre h_akv
  split at h_ok <;> (try (simp at h_ok; done)) -- structural Except: .error closes
  split at h_ok
  · -- structural Option: some → structural succeeded (source order: some first)
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchStructural_preserves_AllKeysValid s2 c _ (by assumption) h_akv2
  · -- structural Option: none → continue to flow/block/content
    have h_akv3 := allowDir_ite_preserves_AllKeysValid s2 h_akv2
    -- Block→flow underindent check
    split at h_ok <;> (try (simp at h_ok; done))
    -- Flow Except split
    split at h_ok <;> (try (simp at h_ok; done))
    -- Flow Option split (source order: some first, none second)
    split at h_ok
    · -- flow some → flow succeeded
      simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchFlowIndicators_preserves_AllKeysValid _ c _ (by assumption) h_akv3
    · -- flow none → block
      split at h_ok <;> (try (simp at h_ok; done)) -- block Except
      split at h_ok
      · -- block some → block succeeded
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchBlockIndicators_preserves_AllKeysValid _ c _ (by assumption) h_akv3
      · -- block none → content
        split at h_ok <;> (try (simp at h_ok; done)) -- content Except
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_AllKeysValid _ c _ (by assumption) h_akv3

/-!
### PendingKeysWellIndexed: pendingKeys are bounded into tokens

Post-cutover invariant on the append-only side-channel: every entry's
`insertBeforeIdx` falls in the range `[1, tokens.size]`.  Combined with
`tokens.size ≥ 1` (true after the initial `streamStart` emit), this is
exactly the bound the linearise lemmas
`linearise_first_eq_tokens_first` and `linearise_last_eq_tokens_last`
need.  After the final `streamEnd` emit, `tokens.size` strictly
exceeds every saved `insertBeforeIdx`, giving the strict bound
`< final.tokens.size` required for the linearise last-element
preservation.

**Algebraic preservation classes** (see Blueprint J.3.3):
* Class A — passthrough (`s'.pendingKeys = s.pendingKeys`): every op
  outside `saveSimpleKey` / `setPendingKeyKind` / `setPendingKeyEndLine`.
  Preserves the invariant via `PendingKeysWellIndexed_mono`.
* Class B — append-with-bounded-entry: `saveSimpleKey` (when its
  `simpleKeyAllowed` guard fires) appends one entry with
  `insertBeforeIdx = s.tokens.size` and `pos = s.currentPos`.
* Class C — element field-update at active index:
  `setPendingKeyKind` (kind only) and `setPendingKeyEndLine` (endLine
  only) preserve `pendingKeys.size`, `[i].insertBeforeIdx`, and
  `[i].pos` for every `i`.  Preserves the invariant via the structure
  characterizations below.
-/

/-- The pendingKeys well-indexedness invariant. -/
def PendingKeysWellIndexed (s : ScannerState) : Prop :=
  s.tokens.size ≥ 1 ∧
  ∀ p (h : p < s.pendingKeys.size),
    1 ≤ s.pendingKeys[p].insertBeforeIdx ∧
    s.pendingKeys[p].insertBeforeIdx ≤ s.tokens.size

/-- Generic mono lemma: a Class-A passthrough op (preserves
    `pendingKeys`) plus tokens-size-monotone preserves the invariant. -/
theorem PendingKeysWellIndexed_mono (s s' : ScannerState)
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_tok_mono : s'.tokens.size ≥ s.tokens.size)
    (h : PendingKeysWellIndexed s) : PendingKeysWellIndexed s' := by
  obtain ⟨h_tok, h_pks⟩ := h
  refine ⟨by omega, ?_⟩
  intro p hp
  have hp_s : p < s.pendingKeys.size := by rw [h_pks_eq] at hp; exact hp
  have h_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s := by
    simp [h_pks_eq]
  rw [h_get]
  have ⟨hb_lo, hb_hi⟩ := h_pks p hp_s
  exact ⟨hb_lo, by omega⟩

/-- Class C characterization: any operation that preserves
    `pendingKeys.size` and each entry's `insertBeforeIdx`, plus
    tokens-size-monotone, preserves the invariant.  Covers
    `setPendingKeyKind` / `setPendingKeyEndLine`. -/
theorem PendingKeysWellIndexed_field_update (s s' : ScannerState)
    (h_size_eq : s'.pendingKeys.size = s.pendingKeys.size)
    (h_idx_eq : ∀ p (hp : p < s.pendingKeys.size)
                  (hp' : p < s'.pendingKeys.size),
                  (s'.pendingKeys[p]'hp').insertBeforeIdx
                    = (s.pendingKeys[p]'hp).insertBeforeIdx)
    (h_tok_mono : s'.tokens.size ≥ s.tokens.size)
    (h : PendingKeysWellIndexed s) : PendingKeysWellIndexed s' := by
  obtain ⟨h_tok, h_pks⟩ := h
  refine ⟨by omega, ?_⟩
  intro p hp
  have hp_s : p < s.pendingKeys.size := by rw [h_size_eq] at hp; exact hp
  rw [h_idx_eq p hp_s hp]
  have ⟨hb_lo, hb_hi⟩ := h_pks p hp_s
  exact ⟨hb_lo, by omega⟩

/-! ### Class A passthrough micro-lemmas (`*_preserves_pendingKeys`)

For every scanner operation outside of `saveSimpleKey` /
`setPendingKeyKind` / `setPendingKeyEndLine`, the `pendingKeys` field
is unchanged.  These are the structural counterparts to the existing
`*_preserves_simpleKeyStack` chain. -/

theorem advance_preserves_pendingKeys (s : ScannerState) :
    s.advance.pendingKeys = s.pendingKeys := by
  unfold ScannerState.advance
  split
  · dsimp only
    split
    · rfl
    · split <;> rfl
  · rfl

theorem emit_preserves_pendingKeys (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).pendingKeys = s.pendingKeys := rfl

theorem emitAt_preserves_pendingKeys (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).pendingKeys = s.pendingKeys := rfl

/-! ### Class C: setPendingKeyKind / setPendingKeyEndLine size and field
preservation.

Both helpers operate via `Array.setIfInBounds`, which preserves size
and is the identity on indices other than the one being written.  The
field they write (`kind` or `endLine`) is irrelevant to
`PendingKeysWellIndexed`. -/

theorem setPendingKeyKind_size (pks : Array PendingKeyEntry)
    (active : Option Nat) (kind : ResolutionKind) :
    (setPendingKeyKind pks active kind).size = pks.size := by
  unfold setPendingKeyKind
  split
  · rfl
  · split
    · rfl
    · simp [Array.size_setIfInBounds]

/-- `setPendingKeyKind` decomposition: either identity or a single-element
    `setIfInBounds` update at the active index. -/
theorem setPendingKeyKind_decomp (pks : Array PendingKeyEntry)
    (active : Option Nat) (kind : ResolutionKind) :
    setPendingKeyKind pks active kind = pks
      ∨ ∃ j, ∃ (h : j < pks.size),
          setPendingKeyKind pks active kind
            = pks.setIfInBounds j { (pks[j]'h) with kind := kind } := by
  unfold setPendingKeyKind
  split
  · left; rfl
  · rename_i j
    split
    · left; rfl
    · rename_i e h_get
      have hj : j < pks.size := by
        rcases Nat.lt_or_ge j pks.size with h | h
        · exact h
        · exfalso
          rw [Array.getElem?_eq_none h] at h_get
          contradiction
      have h_get_eq : pks[j]'hj = e := by
        have := h_get
        rw [Array.getElem?_eq_getElem hj] at this
        injection this
      right
      refine ⟨j, hj, ?_⟩
      simp [h_get_eq]

/-- Pointwise consequence: `setPendingKeyKind` preserves `insertBeforeIdx`. -/
theorem setPendingKeyKind_insertBeforeIdx (pks : Array PendingKeyEntry)
    (active : Option Nat) (kind : ResolutionKind) (i : Nat)
    (hi : i < pks.size)
    (hi' : i < (setPendingKeyKind pks active kind).size) :
    ((setPendingKeyKind pks active kind)[i]'hi').insertBeforeIdx
      = (pks[i]'hi).insertBeforeIdx := by
  rcases setPendingKeyKind_decomp pks active kind with h_id | ⟨j, hj, h_set⟩
  · -- Identity case: setPendingKeyKind pks active kind = pks
    congr 1
    -- Goal: (setPendingKeyKind pks active kind)[i] = pks[i]
    have h_at_eq : (setPendingKeyKind pks active kind)[i]'hi' = pks[i]'hi := by
      congr 1
    exact h_at_eq
  · -- setIfInBounds case: re-cast the dependent index, then case split on i = j.
    have hi_set : i < (pks.setIfInBounds j
        { (pks[j]'hj) with kind := kind }).size := by
      simp [Array.size_setIfInBounds]; exact hi
    have h_at_eq :
        (setPendingKeyKind pks active kind)[i]'hi'
          = (pks.setIfInBounds j { (pks[j]'hj) with kind := kind })[i]'hi_set := by
      congr 1
    rw [h_at_eq]
    by_cases h_eq : i = j
    · subst h_eq
      rw [Array.getElem_setIfInBounds_self]
    · rw [Array.getElem_setIfInBounds_ne (h := fun h => h_eq h.symm)]

theorem setPendingKeyEndLine_size (pks : Array PendingKeyEntry)
    (active : Option Nat) (endLine : Nat) :
    (setPendingKeyEndLine pks active endLine).size = pks.size := by
  unfold setPendingKeyEndLine
  split
  · rfl
  · split
    · rfl
    · simp [Array.size_setIfInBounds]

/-- `setPendingKeyEndLine` decomposition (parallel to
    `setPendingKeyKind_decomp`). -/
theorem setPendingKeyEndLine_decomp (pks : Array PendingKeyEntry)
    (active : Option Nat) (endLine : Nat) :
    setPendingKeyEndLine pks active endLine = pks
      ∨ ∃ j, ∃ (h : j < pks.size),
          setPendingKeyEndLine pks active endLine
            = pks.setIfInBounds j { (pks[j]'h) with endLine := endLine } := by
  unfold setPendingKeyEndLine
  split
  · left; rfl
  · rename_i j
    split
    · left; rfl
    · rename_i e h_get
      have hj : j < pks.size := by
        rcases Nat.lt_or_ge j pks.size with h | h
        · exact h
        · exfalso
          rw [Array.getElem?_eq_none h] at h_get
          contradiction
      have h_get_eq : pks[j]'hj = e := by
        have := h_get
        rw [Array.getElem?_eq_getElem hj] at this
        injection this
      right
      refine ⟨j, hj, ?_⟩
      simp [h_get_eq]

theorem setPendingKeyEndLine_insertBeforeIdx (pks : Array PendingKeyEntry)
    (active : Option Nat) (endLine : Nat) (i : Nat)
    (hi : i < pks.size)
    (hi' : i < (setPendingKeyEndLine pks active endLine).size) :
    ((setPendingKeyEndLine pks active endLine)[i]'hi').insertBeforeIdx
      = (pks[i]'hi).insertBeforeIdx := by
  rcases setPendingKeyEndLine_decomp pks active endLine with h_id | ⟨j, hj, h_set⟩
  · congr 1
    have h_at_eq : (setPendingKeyEndLine pks active endLine)[i]'hi' = pks[i]'hi := by
      congr 1
    exact h_at_eq
  · have hi_set : i < (pks.setIfInBounds j
        { (pks[j]'hj) with endLine := endLine }).size := by
      simp [Array.size_setIfInBounds]; exact hi
    have h_at_eq :
        (setPendingKeyEndLine pks active endLine)[i]'hi'
          = (pks.setIfInBounds j { (pks[j]'hj) with endLine := endLine })[i]'hi_set := by
      congr 1
    rw [h_at_eq]
    by_cases h_eq : i = j
    · subst h_eq
      rw [Array.getElem_setIfInBounds_self]
    · rw [Array.getElem_setIfInBounds_ne (h := fun h => h_eq h.symm)]

/-! ### Class B: saveSimpleKey decomposition

`saveSimpleKey` either returns `s` unchanged (guard fails) or appends
exactly one entry with `insertBeforeIdx = s.tokens.size` and
`pos = s.currentPos`.  Direct proof of invariant preservation. -/

/-- saveSimpleKey preserves `PendingKeysWellIndexed` when started from
    a state with at least one token (guaranteed by the initial
    `streamStart` emit).  If the `simpleKeyAllowed` guard fires, the
    new entry has `insertBeforeIdx = s.tokens.size ≥ 1` (lower bound
    from `h.1`) and `≤ s.tokens.size` (saveSimpleKey doesn't grow
    tokens).  Otherwise saveSimpleKey is identity on `pendingKeys`. -/
theorem saveSimpleKey_preserves_PendingKeysWellIndexed (s : ScannerState)
    (h : PendingKeysWellIndexed s) : PendingKeysWellIndexed (saveSimpleKey s) := by
  obtain ⟨h_tok, h_pks⟩ := h
  unfold saveSimpleKey
  split
  · exact ⟨h_tok, h_pks⟩
  · split
    · -- simpleKeyAllowed: pendingKeys appended with the new entry.
      refine ⟨?_, ?_⟩
      · -- tokens.size unchanged in this branch.
        show s.tokens.size ≥ 1
        exact h_tok
      · intro p hp
        have h_size :
            (s.pendingKeys.push
              { insertBeforeIdx := s.tokens.size,
                pos := s.currentPos,
                endLine := s.line,
                kind := .unresolved }).size = s.pendingKeys.size + 1 := by
          simp [Array.size_push]
        by_cases h_p_lt : p < s.pendingKeys.size
        · -- Existing entry: preserved by getElem_push_lt.
          have ⟨hb_lo, hb_hi⟩ := h_pks p h_p_lt
          show 1 ≤ _ ∧ _
          rw [Array.getElem_push_lt h_p_lt]
          exact ⟨hb_lo, hb_hi⟩
        · -- New entry: p = s.pendingKeys.size.
          have h_p_eq : p = s.pendingKeys.size := by
            have := hp
            simp at this
            omega
          subst h_p_eq
          show 1 ≤ _ ∧ _
          rw [Array.getElem_push_eq]
          exact ⟨h_tok, Nat.le_refl _⟩
    · exact ⟨h_tok, h_pks⟩

/-! ### Class A passthrough leaves (`*_preserves_pendingKeys`)

Mirrors of the corresponding `*_preserves_simpleKeyStack` chain.  Every
op below leaves `pendingKeys` unchanged because none of them appends
(only `saveSimpleKey` does — see Class B above) nor field-updates
(only `setPendingKeyKind` / `setPendingKeyEndLine` do — see Class C). -/

theorem skipSpacesLoop_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipSpacesLoop s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · exact (ih _).trans (advance_preserves_pendingKeys _)
    · rfl

theorem skipWhitespaceLoop_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipWhitespaceLoop s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · exact (ih _).trans (advance_preserves_pendingKeys _)
      · rfl
    · rfl

theorem skipToEndOfLineLoop_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipToEndOfLineLoop s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipToEndOfLineLoop; rfl
  | succ _ ih =>
    unfold skipToEndOfLineLoop; split
    · split
      · rfl
      · exact (ih _).trans (advance_preserves_pendingKeys _)
    · rfl

theorem skipSpaces_preserves_pendingKeys (s : ScannerState) :
    (skipSpaces s).pendingKeys = s.pendingKeys := by
  unfold skipSpaces; exact skipSpacesLoop_preserves_pendingKeys s _

theorem skipWhitespace_preserves_pendingKeys (s : ScannerState) :
    (skipWhitespace s).pendingKeys = s.pendingKeys := by
  unfold skipWhitespace; exact skipWhitespaceLoop_preserves_pendingKeys s _

theorem skipToEndOfLine_preserves_pendingKeys (s : ScannerState) :
    (skipToEndOfLine s).pendingKeys = s.pendingKeys := by
  unfold skipToEndOfLine; exact skipToEndOfLineLoop_preserves_pendingKeys s _

theorem collectCommentTextLoop_preserves_pendingKeys (s : ScannerState)
    (text : String) (fuel : Nat) :
    (collectCommentTextLoop s text fuel).2.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s text with
  | zero => unfold collectCommentTextLoop; rfl
  | succ fuel' IH =>
    unfold collectCommentTextLoop; split
    · split
      · rfl
      · rw [IH, advance_preserves_pendingKeys]
    · rfl

theorem skipToContentWs_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold skipToContentWs at h
  split at h
  · simp only [] at h
    split at h
    · split at h
      · split at h
        · simp at h; rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
        · split at h
          · simp at h; rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
          · split at h
            · simp at h; rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
            · simp at h
        · simp at h; rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
      · simp at h; rw [← h, skipSpaces_preserves_pendingKeys]
    · simp at h; rw [← h, skipWhitespace_preserves_pendingKeys, skipSpaces_preserves_pendingKeys]
  · simp at h; rw [← h, skipWhitespace_preserves_pendingKeys]

theorem skipToContentComment_preserves_pendingKeys (s : ScannerState) :
    (skipToContentComment s).pendingKeys = s.pendingKeys := by
  unfold skipToContentComment
  split
  · simp only []
    split
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_pendingKeys, advance_preserves_pendingKeys]
      · rfl
    · split
      · simp only []
        rw [collectCommentTextLoop_preserves_pendingKeys, advance_preserves_pendingKeys]
      · rfl
  · rfl

theorem consumeNewline_preserves_pendingKeys (s : ScannerState) :
    (consumeNewline s).pendingKeys = s.pendingKeys := by
  unfold consumeNewline
  split
  · exact advance_preserves_pendingKeys s
  · simp only []; split
    · exact advance_preserves_pendingKeys _
    · exact advance_preserves_pendingKeys _
  · rfl

theorem skipToContentLoop_preserves_pendingKeys (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; simp at h; rw [← h]
  | succ _ ih =>
    unfold skipToContentLoop at h
    split at h
    · simp at h
    · rename_i s1 hws
      simp only [] at h
      split at h
      · split at h
        · split at h
          · have := ih _ h; rw [this, consumeNewline_preserves_pendingKeys,
              skipToContentComment_preserves_pendingKeys]; exact skipToContentWs_preserves_pendingKeys s s1 hws
          · have := ih _ h; rw [this, consumeNewline_preserves_pendingKeys,
              skipToContentComment_preserves_pendingKeys]; exact skipToContentWs_preserves_pendingKeys s s1 hws
        · simp at h; rw [← h, skipToContentComment_preserves_pendingKeys]
          exact skipToContentWs_preserves_pendingKeys s s1 hws
      · simp at h; rw [← h, skipToContentComment_preserves_pendingKeys]
        exact skipToContentWs_preserves_pendingKeys s s1 hws

theorem skipToContent_preserves_pendingKeys (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold skipToContent at h; exact skipToContentLoop_preserves_pendingKeys s s' _ h

theorem unwindIndentsLoop_preserves_pendingKeys (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ _ ih =>
    unfold unwindIndentsLoop; split
    · have := ih { s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop }
      simp [emit_preserves_pendingKeys] at this; exact this
    · rfl

theorem unwindIndents_preserves_pendingKeys (s : ScannerState) (col : Int) :
    (unwindIndents s col).pendingKeys = s.pendingKeys := by
  unfold unwindIndents; exact unwindIndentsLoop_preserves_pendingKeys s col _

theorem advanceNLoop_preserves_pendingKeys (s : ScannerState) (n : Nat) :
    (ScannerState.advanceNLoop s n).pendingKeys = s.pendingKeys := by
  induction n generalizing s with
  | zero => unfold ScannerState.advanceNLoop; rfl
  | succ n' ih =>
    unfold ScannerState.advanceNLoop
    rw [ih]; exact advance_preserves_pendingKeys s

theorem advanceN_preserves_pendingKeys (s : ScannerState) (n : Nat) :
    (s.advanceN n).pendingKeys = s.pendingKeys := by
  unfold ScannerState.advanceN; exact advanceNLoop_preserves_pendingKeys s n

theorem pushSequenceIndent_preserves_pendingKeys (s : ScannerState) (col : Int) :
    (pushSequenceIndent s col).pendingKeys = s.pendingKeys := by
  unfold pushSequenceIndent
  split
  · show (s.emit .blockSequenceStart).pendingKeys = _
    exact emit_preserves_pendingKeys s _
  · rfl

theorem pushMappingIndent_preserves_pendingKeys (s : ScannerState) (col : Int) :
    (pushMappingIndent s col).pendingKeys = s.pendingKeys := by
  unfold pushMappingIndent
  split
  · show (s.emit .blockMappingStart).pendingKeys = _
    exact emit_preserves_pendingKeys s _
  · rfl

theorem skipDocEndWhitespace_preserves_pendingKeys (s : ScannerState) (fuel : Nat) :
    (skipDocEndWhitespace s fuel).pendingKeys = s.pendingKeys := by
  induction fuel generalizing s with
  | zero => unfold skipDocEndWhitespace; rfl
  | succ fuel' ih =>
    unfold skipDocEndWhitespace
    split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

/-! #### Document scan ops (Class A) -/

theorem scanDocumentStart_preserves_pendingKeys (s : ScannerState) :
    (scanDocumentStart s).pendingKeys = s.pendingKeys := by
  unfold scanDocumentStart
  simp [advanceN_preserves_pendingKeys, emit_preserves_pendingKeys,
        unwindIndents_preserves_pendingKeys]

theorem scanDocumentEnd_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanDocumentEnd at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advanceN_preserves_pendingKeys, emit_preserves_pendingKeys,
        unwindIndents_preserves_pendingKeys]

theorem collectDirectiveNameLoop_preserves_pendingKeys (s : ScannerState) (name : String) (fuel : Nat) :
    (collectDirectiveNameLoop s name fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s name with
  | zero => unfold collectDirectiveNameLoop; rfl
  | succ fuel' ih =>
    unfold collectDirectiveNameLoop; split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectVersionMajorLoop_preserves_pendingKeys (s : ScannerState) (major : String) (fuel : Nat) :
    (collectVersionMajorLoop s major fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s major with
  | zero => unfold collectVersionMajorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMajorLoop; split
    · exact advance_preserves_pendingKeys s
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectVersionMinorLoop_preserves_pendingKeys (s : ScannerState) (minor : String) (fuel : Nat) :
    (collectVersionMinorLoop s minor fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s minor with
  | zero => unfold collectVersionMinorLoop; rfl
  | succ fuel' ih =>
    unfold collectVersionMinorLoop; split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectTagHandleDirectiveLoop_preserves_pendingKeys (s : ScannerState) (handle : String) (fuel : Nat) :
    (collectTagHandleDirectiveLoop s handle fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s handle with
  | zero => unfold collectTagHandleDirectiveLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleDirectiveLoop; split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectTagPrefixLoop_preserves_pendingKeys (s : ScannerState) (pfx : String) (fuel : Nat) :
    (collectTagPrefixLoop s pfx fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s pfx with
  | zero => unfold collectTagPrefixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagPrefixLoop; split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectVerbatimTagLoop_preserves_pendingKeys (s : ScannerState) (uri : String) (fuel : Nat) :
    (collectVerbatimTagLoop s uri fuel).snd.snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s uri with
  | zero => unfold collectVerbatimTagLoop; rfl
  | succ fuel' ih =>
    unfold collectVerbatimTagLoop
    split
    · simp only []; exact advance_preserves_pendingKeys s
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · simp only []

theorem collectTagSuffixLoop_preserves_pendingKeys (s : ScannerState) (suffix : String) (fuel : Nat) :
    (collectTagSuffixLoop s suffix fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s suffix with
  | zero => unfold collectTagSuffixLoop; rfl
  | succ fuel' ih =>
    unfold collectTagSuffixLoop
    split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · simp only []
    · simp only []

theorem collectTagHandleLoop_preserves_pendingKeys (s : ScannerState) (chars : String) (fuel : Nat) :
    (collectTagHandleLoop s chars fuel).snd.snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s chars with
  | zero => unfold collectTagHandleLoop; rfl
  | succ fuel' ih =>
    unfold collectTagHandleLoop
    split
    · simp only []; exact advance_preserves_pendingKeys s
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · simp only []
    · simp only []

theorem collectAnchorNameLoop_preserves_pendingKeys (s : ScannerState) (acc : String) (fuel : Nat) :
    (collectAnchorNameLoop s acc fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s acc with
  | zero => unfold collectAnchorNameLoop; rfl
  | succ fuel' ih =>
    unfold collectAnchorNameLoop
    split
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectHexDigitsLoop_preserves_pendingKeys (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.pendingKeys = s.pendingKeys := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    cases h_peek : s.peek? with
    | none => simp []
    | some c =>
      simp []
      split
      · have h_adv := advance_preserves_pendingKeys s
        rw [ih, h_adv]
      · rfl

theorem parseHexEscape_preserves_pendingKeys (s : ScannerState) (n : Nat) (ch : Char) (s' : ScannerState)
    (h : parseHexEscape s n = .ok (ch, s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold parseHexEscape at h
  simp only [] at h
  have h_collect := collectHexDigitsLoop_preserves_pendingKeys s "" n
  split at h <;> try contradiction
  split at h <;> try contradiction
  injection h with h_eq; cases h_eq
  rw [h_collect]

theorem processEscape_preserves_pendingKeys (s : ScannerState) (ch : Char) (s' : ScannerState)
    (h : processEscape s = .ok (ch, s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold processEscape at h
  simp only [] at h
  split at h <;> try contradiction
  repeat (split at h)
  all_goals (
    first
    | (injection h with h_eq; cases h_eq; exact advance_preserves_pendingKeys s)
    | (have h_adv := advance_preserves_pendingKeys s
       have h_hex := parseHexEscape_preserves_pendingKeys s.advance _ ch s' h
       rw [h_hex, h_adv])
    | contradiction
  )

theorem skipBlankLinesLoop_preserves_pendingKeys (s : ScannerState) (cnt fuel inputEnd : Nat) :
    (skipBlankLinesLoop s cnt fuel inputEnd).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s cnt with
  | zero => unfold skipBlankLinesLoop; rfl
  | succ fuel' ih =>
    unfold skipBlankLinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_pendingKeys s
        have h_cn := consumeNewline_preserves_pendingKeys (skipSpaces s)
        rw [ih, h_cn, h_sp]

theorem foldQuotedNewlinesLoop_preserves_pendingKeys (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    cases h_peek : (skipSpaces s).peek? with
    | none => simp [h_peek]
    | some c =>
      simp [h_peek]
      cases h_lb : isLineBreakBool c with
      | false => simp []
      | true =>
        simp []
        have h_sp := skipSpaces_preserves_pendingKeys s
        have h_cn := consumeNewline_preserves_pendingKeys (skipSpaces s)
        rw [ih, h_cn, h_sp]

theorem foldQuotedNewlines_preserves_pendingKeys (s : ScannerState) (s' : ScannerState) (content : String)
    (h : foldQuotedNewlines s = .ok (content, s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold foldQuotedNewlines at h
  simp only [bind, Except.bind, pure] at h
  have h_cn := consumeNewline_preserves_pendingKeys s
  let fuel := s.inputEnd - (consumeNewline s).offset + 1
  have h_fold := foldQuotedNewlinesLoop_preserves_pendingKeys (consumeNewline s) 0 fuel
  have h_sp := skipSpaces_preserves_pendingKeys (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst
  have h_sw := skipWhitespace_preserves_pendingKeys (skipSpaces (foldQuotedNewlinesLoop (consumeNewline s) 0 fuel).fst)
  split at h <;> try contradiction
  · split at h <;> try contradiction
    split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
  · split at h <;> try contradiction
    split at h
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]
    · injection h with heq; cases heq; rw [h_sw, h_sp, h_fold, h_cn]

theorem consumeExactSpaces_preserves_pendingKeys (s : ScannerState) (count : Nat) :
    (consumeExactSpaces s count).snd.pendingKeys = s.pendingKeys := by
  induction count generalizing s with
  | zero => unfold consumeExactSpaces; rfl
  | succ count' ih =>
    unfold consumeExactSpaces; split
    · simp only []; rw [ih]; exact advance_preserves_pendingKeys s
    · rfl

theorem parseBlockHeaderLoop_preserves_pendingKeys (s : ScannerState) (chomp : ChompStyle)
    (offset : Option Nat) (fuel : Nat) :
    (parseBlockHeaderLoop s chomp offset fuel).snd.snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s chomp offset with
  | zero => unfold parseBlockHeaderLoop; rfl
  | succ fuel' ih =>
    unfold parseBlockHeaderLoop; split
    · rw [ih]; exact advance_preserves_pendingKeys s
    · rw [ih]; exact advance_preserves_pendingKeys s
    · split
      · rw [ih]; exact advance_preserves_pendingKeys s
      · rfl
    · rfl

theorem collectLineContentLoop_preserves_pendingKeys (s : ScannerState) (content : String) (fuel : Nat) :
    (collectLineContentLoop s content fuel).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s content with
  | zero => unfold collectLineContentLoop; rfl
  | succ fuel' ih =>
    unfold collectLineContentLoop
    split
    · split
      · rfl
      · rw [ih]; exact advance_preserves_pendingKeys s
    · rfl

theorem collectBlockScalarLoop_preserves_pendingKeys (s : ScannerState) (rawContent : String)
    (fuel : Nat) (contentIndent : Nat) (inputEnd : Nat) :
    (collectBlockScalarLoop s rawContent fuel contentIndent inputEnd).snd.pendingKeys = s.pendingKeys := by
  induction fuel generalizing s rawContent with
  | zero => unfold collectBlockScalarLoop; rfl
  | succ fuel' ih =>
    unfold collectBlockScalarLoop
    split
    · rfl
    · simp only []
      split
      · exact consumeExactSpaces_preserves_pendingKeys s contentIndent
      · split
        · rw [ih, consumeNewline_preserves_pendingKeys, consumeExactSpaces_preserves_pendingKeys]
        · split
          · rfl
          · split
            · split
              · rw [ih, consumeNewline_preserves_pendingKeys,
                    collectLineContentLoop_preserves_pendingKeys, consumeExactSpaces_preserves_pendingKeys]
              · rw [ih, collectLineContentLoop_preserves_pendingKeys, consumeExactSpaces_preserves_pendingKeys]
            · rw [collectLineContentLoop_preserves_pendingKeys, consumeExactSpaces_preserves_pendingKeys]

theorem scanBlockScalarSkipComment_preserves_pendingKeys (s : ScannerState) :
    (scanBlockScalarSkipComment s).pendingKeys = s.pendingKeys := by
  unfold scanBlockScalarSkipComment
  split
  · split
    · dsimp only []
      split
      · simp only []
        rw [collectCommentTextLoop_preserves_pendingKeys, advance_preserves_pendingKeys]
      · rfl
    · rfl
  · rfl

theorem scanBlockScalarConsumeNewline_preserves_pendingKeys (s s' : ScannerState)
    (h : scanBlockScalarConsumeNewline s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanBlockScalarConsumeNewline at h
  split at h
  · split at h
    · injection h with h_eq; subst h_eq; exact consumeNewline_preserves_pendingKeys s
    · split at h
      · injection h with h_eq; subst h_eq; rfl
      · contradiction
  · injection h with h_eq; subst h_eq; rfl

theorem scanBlockScalarBody_preserves_pendingKeys (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos) (s' : ScannerState)
    (h_pks : s_nl.pendingKeys = s_orig.pendingKeys)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.pendingKeys = s_orig.pendingKeys := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals rw [emitAt_preserves_pendingKeys, collectBlockScalarLoop_preserves_pendingKeys, h_pks]

theorem scanBlockScalar_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanBlockScalar s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanBlockScalar at h
  simp only [] at h
  split at h
  · contradiction
  · exact scanBlockScalarBody_preserves_pendingKeys s _ _ _ _ _ s'
      (by rw [scanBlockScalarConsumeNewline_preserves_pendingKeys _ _ (by assumption),
              scanBlockScalarSkipComment_preserves_pendingKeys,
              skipWhitespace_preserves_pendingKeys,
              parseBlockHeaderLoop_preserves_pendingKeys,
              advance_preserves_pendingKeys]) h

/-! #### Anchor / Tag scan ops (Class A) -/

theorem scanAnchorOrAlias_preserves_pendingKeys (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [emitAt_preserves_pendingKeys, collectAnchorNameLoop_preserves_pendingKeys,
          advance_preserves_pendingKeys]

theorem scanVerbatimTag_preserves_pendingKeys (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s startPos = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      simp [emitAt_preserves_pendingKeys, collectVerbatimTagLoop_preserves_pendingKeys,
            advance_preserves_pendingKeys]

theorem scanSecondaryTag_preserves_pendingKeys (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).pendingKeys = s.pendingKeys := by
  unfold scanSecondaryTag
  simp [emitAt_preserves_pendingKeys, collectTagSuffixLoop_preserves_pendingKeys,
        advance_preserves_pendingKeys]

theorem scanNamedTag_preserves_pendingKeys (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).pendingKeys = s.pendingKeys := by
  unfold scanNamedTag
  simp only []
  split
  · simp [emitAt_preserves_pendingKeys, collectTagSuffixLoop_preserves_pendingKeys,
          collectTagHandleLoop_preserves_pendingKeys]
  · simp [emitAt_preserves_pendingKeys, collectTagHandleLoop_preserves_pendingKeys]

theorem scanTag_preserves_pendingKeys (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s') :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanTag at hok; dsimp only [] at hok
  split at hok
  · simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok; have h := Except.ok.inj hok; subst h; dsimp only []
      simp [scanVerbatimTag_preserves_pendingKeys s.advance s.currentPos s_verb hv,
            advance_preserves_pendingKeys]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanSecondaryTag_preserves_pendingKeys, advance_preserves_pendingKeys]
  · have h := Except.ok.inj hok; subst h; dsimp only []
    simp [scanNamedTag_preserves_pendingKeys, advance_preserves_pendingKeys]

/-! #### Directive scan op (Class A) -/

theorem scanDirective_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanDirective s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanDirective at h
  split at h
  · contradiction
  · simp only [] at h
    split at h
    · split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h; subst h_eq
        rw [skipToEndOfLine_preserves_pendingKeys]
        unfold scanYamlDirective at h_inner
        simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_inner
        split at h_inner <;> try contradiction
        repeat (any_goals (split at h_inner))
        all_goals (try contradiction)
        all_goals (simp only [Except.ok.injEq] at h_inner; subst h_inner)
        all_goals (try simp [emitAt_preserves_pendingKeys, skipWhitespace_preserves_pendingKeys,
              collectVersionMinorLoop_preserves_pendingKeys,
              collectVersionMajorLoop_preserves_pendingKeys])
        all_goals (rw [collectDirectiveNameLoop_preserves_pendingKeys, advance_preserves_pendingKeys])
      · contradiction
    · split at h
      · split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h; subst h_eq
          rw [skipToEndOfLine_preserves_pendingKeys]
          unfold scanTagDirective at h_inner
          dsimp only [] at h_inner
          simp only [bind, Except.bind] at h_inner
          split at h_inner <;> try (split at h_inner <;> try contradiction)
          all_goals (try contradiction)
          all_goals (simp only [pure, Except.pure, Pure.pure, Except.ok.injEq] at h_inner; subst h_inner)
          all_goals simp [emitAt_preserves_pendingKeys, collectTagPrefixLoop_preserves_pendingKeys,
                skipWhitespace_preserves_pendingKeys,
                collectTagHandleDirectiveLoop_preserves_pendingKeys,
                collectDirectiveNameLoop_preserves_pendingKeys,
                advance_preserves_pendingKeys]
        · contradiction
      · simp only [Except.ok.injEq] at h; subst h
        simp [skipToEndOfLine_preserves_pendingKeys, skipWhitespace_preserves_pendingKeys,
              collectDirectiveNameLoop_preserves_pendingKeys, advance_preserves_pendingKeys]

/-! #### Flow / Block entry / Key scan ops (Class A) -/

theorem scanFlowEntry_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanFlowEntry s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys]

theorem scanBlockEntry_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanBlockEntry s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanBlockEntry at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys,
                  pushSequenceIndent_preserves_pendingKeys]

theorem scanKey_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanKey s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanKey at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h)
  all_goals simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys,
                  pushMappingIndent_preserves_pendingKeys]

/-! #### Flow start/end scan ops (Class A) -/

theorem scanFlowSequenceStart_preserves_pendingKeys (s : ScannerState) :
    (scanFlowSequenceStart s).pendingKeys = s.pendingKeys := by
  unfold scanFlowSequenceStart
  simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys]

theorem scanFlowSequenceEnd_preserves_pendingKeys (s : ScannerState) :
    (scanFlowSequenceEnd s).pendingKeys = s.pendingKeys := by
  unfold scanFlowSequenceEnd
  simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys]

theorem scanFlowMappingStart_preserves_pendingKeys (s : ScannerState) :
    (scanFlowMappingStart s).pendingKeys = s.pendingKeys := by
  unfold scanFlowMappingStart
  simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys]

theorem scanFlowMappingEnd_preserves_pendingKeys (s : ScannerState) :
    (scanFlowMappingEnd s).pendingKeys = s.pendingKeys := by
  unfold scanFlowMappingEnd
  simp [advance_preserves_pendingKeys, emit_preserves_pendingKeys]

/-! #### Quoted/Plain scalar scan ops (Class A — body of these scanners
preserves pendingKeys; the dispatchContent wrapper around scanDoubleQuoted /
scanSingleQuoted re-applies `setPendingKeyEndLine`, which is Class C and
handled at dispatch time). -/

theorem collectPlainScalarLoop_preserves_pendingKeys (s : ScannerState) (content lastLine : String)
    (fuel : Nat) (inFlow : Bool) (contentIndent inputEnd : Nat) :
    ∀ result, collectPlainScalarLoop s content lastLine fuel inFlow contentIndent inputEnd = .ok result →
    result.state.pendingKeys = s.pendingKeys := by
  intro result h
  induction fuel generalizing s content lastLine with
  | zero =>
    unfold collectPlainScalarLoop at h
    injection h with h_eq; cases h_eq; rfl
  | succ fuel' ih =>
    unfold collectPlainScalarLoop at h
    split at h
    · injection h with h_eq; cases h_eq; rfl
    · rename_i c
      split at h
      · rename_i hterm
        injection h with h_eq; cases h_eq
        rw [ScanHelpers.collectPlainScalar_terminates?_state _ _ _ _ _ _ hterm]
      · split at h
        · split at h
          · simp only [bind, Except.bind] at h
            split at h <;> try contradiction
            rename_i fold_result heq
            cases fold_result with
            | mk content_fold s_fold =>
              have h_fold := foldQuotedNewlines_preserves_pendingKeys s s_fold content_fold heq
              split at h
              · injection h with h_eq; cases h_eq; rfl
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s_fold (content ++ content_fold) "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih s_fold (content ++ content_fold) "" h_loop, h_fold]
                | error e => simp at h
          · split at h
            · injection h with h_eq; cases h_eq; rfl
            · rename_i content' s' hblk
              have hprop : s'.pendingKeys = s.pendingKeys := by
                unfold collectPlainScalar_handleBlockLineBreak at hblk
                simp only [] at hblk
                split at hblk <;> try contradiction
                split at hblk <;> try contradiction
                have := Prod.mk.inj (Option.some.inj hblk)
                rw [← this.2, skipSpaces_preserves_pendingKeys,
                    skipBlankLinesLoop_preserves_pendingKeys, consumeNewline_preserves_pendingKeys]
              split at h
              · injection h with h_eq; cases h_eq; rfl
              · dsimp only [] at h
                generalize h_loop : collectPlainScalarLoop s' content' "" fuel' inFlow contentIndent inputEnd = cont_result at h
                cases cont_result with
                | ok inner_result =>
                  dsimp only [] at h
                  split at h
                  · injection h with h_eq; cases h_eq; rfl
                  · have h_eq := Except.ok.inj h; subst h_eq
                    rw [ih _ _ _ h_loop, hprop]
                | error e => simp at h
        · split at h
          · have h_adv := advance_preserves_pendingKeys s
            rw [ih s.advance content (lastLine.push _) h, h_adv]
          · split at h
            · injection h with h_eq; cases h_eq; rfl
            · simp only [] at h
              have h_adv := advance_preserves_pendingKeys s
              rw [ih s.advance _ "" h, h_adv]

theorem collectDoubleQuotedLoop_preserves_pendingKeys (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.pendingKeys = s.pendingKeys := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectDoubleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h
    · contradiction
    · injection h with h_eq; cases h_eq
      exact advance_preserves_pendingKeys s
    · simp only [] at h
      split at h <;> try contradiction
      split at h
      · have h_cn := consumeNewline_preserves_pendingKeys s.advance
        have h_sw := skipWhitespace_preserves_pendingKeys (consumeNewline s.advance)
        have h_adv := advance_preserves_pendingKeys s
        rw [ih _ _ h, h_sw, h_cn, h_adv]
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i escape_result heq
        cases escape_result with
        | mk ch s_after_escape =>
          have h_proc := processEscape_preserves_pendingKeys s.advance ch s_after_escape heq
          have h_adv := advance_preserves_pendingKeys s
          rw [ih _ _ h, h_proc, h_adv]
    · split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_pendingKeys s s_fold folded heq
          split at h <;> try contradiction
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [ih s_fold (trimTrailingWS content ++ folded) h, h_fold]
      · split at h <;> try contradiction
        have h_adv := advance_preserves_pendingKeys s
        rw [ih _ _ h, h_adv]

theorem collectSingleQuotedLoop_preserves_pendingKeys (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat) :
    ∀ result, collectSingleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result →
    result.snd.pendingKeys = s.pendingKeys := by
  intro result h
  induction fuel generalizing s content with
  | zero =>
    unfold collectSingleQuotedLoop at h
    contradiction
  | succ fuel' ih =>
    unfold collectSingleQuotedLoop at h
    split at h
    · contradiction
    · simp only [] at h
      split at h
      · have h_adv1 := advance_preserves_pendingKeys s
        have h_adv2 := advance_preserves_pendingKeys s.advance
        rw [ih _ _ h, h_adv2, h_adv1]
      · injection h with h_eq; cases h_eq
        exact advance_preserves_pendingKeys s
    · split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq
        cases fold_result with
        | mk folded s_fold =>
          have h_fold := foldQuotedNewlines_preserves_pendingKeys s s_fold folded heq
          split at h <;> try contradiction
          split at h <;> try contradiction
          split at h <;> try contradiction
          rw [ih s_fold _ h, h_fold]
      · split at h <;> try contradiction
        have h_adv := advance_preserves_pendingKeys s
        rw [ih s.advance _ h, h_adv]

theorem scanPlainScalar_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanPlainScalar s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanPlainScalar at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i result heq
  simp only [Except.ok.injEq] at h; subst h
  simp [emitAt_preserves_pendingKeys]
  exact collectPlainScalarLoop_preserves_pendingKeys s "" "" _ _ _ _ result heq

theorem scanDoubleQuoted_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanDoubleQuoted s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_pendingKeys]
    have := collectDoubleQuotedLoop_preserves_pendingKeys s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_pendingKeys]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_pendingKeys]
    have := collectDoubleQuotedLoop_preserves_pendingKeys s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_pendingKeys]

theorem scanSingleQuoted_preserves_pendingKeys (s : ScannerState) (s' : ScannerState)
    (h : scanSingleQuoted s = .ok s') : s'.pendingKeys = s.pendingKeys := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h <;> try contradiction
  rename_i result heq
  split at h
  · split at h <;> try contradiction
    simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_pendingKeys]
    have := collectSingleQuotedLoop_preserves_pendingKeys s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_pendingKeys]
  · simp only [Except.ok.injEq] at h; subst h
    simp [emitAt_preserves_pendingKeys]
    have := collectSingleQuotedLoop_preserves_pendingKeys s.advance "" _ _ _ _ _ result heq
    rw [this, advance_preserves_pendingKeys]

/-! ### Class C composition: scanValueClearKey / scanValuePrepare / scanValue

`scanValueClearKey` is Class A (only sets `pendingKeyActive := none`,
leaves `pendingKeys` unchanged).  `scanValuePrepare` and `scanValue`
hit `setPendingKeyKind` in three of their branches, so we work directly
with `PendingKeysWellIndexed` via `PendingKeysWellIndexed_field_update`. -/

theorem scanValueClearKey_preserves_pendingKeys (s : ScannerState) :
    (scanValueClearKey s).pendingKeys = s.pendingKeys := by
  unfold scanValueClearKey
  split
  · split
    · rfl
    · split <;> rfl
  · rfl

/-- Pointwise: `scanValuePrepare` preserves each entry's `insertBeforeIdx`.
    The three `setPendingKeyKind` branches change only `kind`. -/
theorem scanValuePrepare_pendingKeys_insertBeforeIdx (s : ScannerState) (i : Nat)
    (hi : i < s.pendingKeys.size)
    (hi' : i < (scanValuePrepare s).pendingKeys.size) :
    ((scanValuePrepare s).pendingKeys[i]'hi').insertBeforeIdx
      = (s.pendingKeys[i]'hi).insertBeforeIdx := by
  unfold scanValuePrepare
  split
  · split
    · split
      · -- Branch 1: blockMappingStartAndKey
        show ((setPendingKeyKind s.pendingKeys s.pendingKeyActive .blockMappingStartAndKey)[i]'_).insertBeforeIdx
          = (s.pendingKeys[i]'hi).insertBeforeIdx
        exact setPendingKeyKind_insertBeforeIdx s.pendingKeys s.pendingKeyActive
          .blockMappingStartAndKey i hi (by
            rw [setPendingKeyKind_size]; exact hi)
      · -- Branch 2: keyOnly (block)
        show ((setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly)[i]'_).insertBeforeIdx
          = (s.pendingKeys[i]'hi).insertBeforeIdx
        exact setPendingKeyKind_insertBeforeIdx s.pendingKeys s.pendingKeyActive
          .keyOnly i hi (by rw [setPendingKeyKind_size]; exact hi)
    · -- Branch 3: keyOnly (flow)
      show ((setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly)[i]'_).insertBeforeIdx
        = (s.pendingKeys[i]'hi).insertBeforeIdx
      exact setPendingKeyKind_insertBeforeIdx s.pendingKeys s.pendingKeyActive
        .keyOnly i hi (by rw [setPendingKeyKind_size]; exact hi)
  · split
    · -- Branch 4: explicitKeyLine.isSome — pendingKeys unchanged
      rfl
    · split
      · -- Branch 5: pushMappingIndent — pendingKeys unchanged
        have h_eq : (pushMappingIndent s s.col).pendingKeys = s.pendingKeys :=
          pushMappingIndent_preserves_pendingKeys s s.col
        have hi'' : i < s.pendingKeys.size := hi
        have hi''' : i < (pushMappingIndent s s.col).pendingKeys.size := by rw [h_eq]; exact hi''
        have h_at : (pushMappingIndent s s.col).pendingKeys[i]'hi''' = s.pendingKeys[i]'hi'' := by
          congr 1
        show ((pushMappingIndent s s.col).pendingKeys[i]'hi''').insertBeforeIdx
            = (s.pendingKeys[i]'hi'').insertBeforeIdx
        rw [h_at]
      · -- Branch 6: identity
        rfl

theorem scanValuePrepare_pendingKeys_size (s : ScannerState) :
    (scanValuePrepare s).pendingKeys.size = s.pendingKeys.size := by
  unfold scanValuePrepare
  split
  · split
    · split
      · simp [setPendingKeyKind_size]
      · simp [setPendingKeyKind_size]
    · simp [setPendingKeyKind_size]
  · split
    · rfl
    · split
      · rw [pushMappingIndent_preserves_pendingKeys]
      · rfl

theorem scanValuePrepare_preserves_PendingKeysWellIndexed (s : ScannerState)
    (h : PendingKeysWellIndexed s) : PendingKeysWellIndexed (scanValuePrepare s) := by
  apply PendingKeysWellIndexed_field_update s (scanValuePrepare s)
    (scanValuePrepare_pendingKeys_size s)
    (fun p hp hp' => scanValuePrepare_pendingKeys_insertBeforeIdx s p hp hp')
    (scanValuePrepare_tokens_monotonic s)
    h

theorem scanValue_pendingKeys_size (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') :
    s'.pendingKeys.size = s.pendingKeys.size := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  -- s' = (scanValuePrepare (scanValueClearKey s)).emit .value |>.advance with simpleKeyAllowed/explicitKeyLine
  show ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.pendingKeys.size = _
  rw [advance_preserves_pendingKeys, emit_preserves_pendingKeys, scanValuePrepare_pendingKeys_size,
      scanValueClearKey_preserves_pendingKeys]

theorem scanValue_pendingKeys_insertBeforeIdx (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') (i : Nat) (hi : i < s.pendingKeys.size)
    (hi' : i < s'.pendingKeys.size) :
    (s'.pendingKeys[i]'hi').insertBeforeIdx
      = (s.pendingKeys[i]'hi).insertBeforeIdx := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  split at h <;> try contradiction
  simp only [Except.ok.injEq] at h; subst h
  -- The chain: scanValueClearKey → scanValuePrepare → emit → advance.
  -- emit/advance preserve pendingKeys (Class A); scanValueClearKey too.
  -- Only scanValuePrepare may field-update via setPendingKeyKind.
  have h_clear := scanValueClearKey_preserves_pendingKeys s
  have h_prep_size := scanValuePrepare_pendingKeys_size (scanValueClearKey s)
  have h_emit := emit_preserves_pendingKeys (scanValuePrepare (scanValueClearKey s)) .value
  have h_adv := advance_preserves_pendingKeys ((scanValuePrepare (scanValueClearKey s)).emit .value)
  -- Goal: ((((scanValuePrepare (scanValueClearKey s)).emit .value).advance).pendingKeys[i]'hi').insertBeforeIdx
  --     = (s.pendingKeys[i]'hi).insertBeforeIdx
  -- After simplification, this reduces to scanValuePrepare's insertBeforeIdx preservation.
  show (((scanValuePrepare (scanValueClearKey s)).emit .value).advance.pendingKeys[i]'hi').insertBeforeIdx
    = (s.pendingKeys[i]'hi).insertBeforeIdx
  have hi_clear : i < (scanValueClearKey s).pendingKeys.size := by rw [h_clear]; exact hi
  have hi_prep : i < (scanValuePrepare (scanValueClearKey s)).pendingKeys.size := by
    rw [h_prep_size]; exact hi_clear
  have hi_emit : i < ((scanValuePrepare (scanValueClearKey s)).emit .value).pendingKeys.size := by
    rw [h_emit]; exact hi_prep
  have h_step1 :
      (((scanValuePrepare (scanValueClearKey s)).emit .value).advance.pendingKeys[i]'hi').insertBeforeIdx
        = (((scanValuePrepare (scanValueClearKey s)).emit .value).pendingKeys[i]'hi_emit).insertBeforeIdx := by
    congr 1
    have : ((scanValuePrepare (scanValueClearKey s)).emit .value).advance.pendingKeys[i]'hi'
        = ((scanValuePrepare (scanValueClearKey s)).emit .value).pendingKeys[i]'hi_emit := by
      congr 1
    exact this
  have h_step2 :
      (((scanValuePrepare (scanValueClearKey s)).emit .value).pendingKeys[i]'hi_emit).insertBeforeIdx
        = ((scanValuePrepare (scanValueClearKey s)).pendingKeys[i]'hi_prep).insertBeforeIdx := by
    have : ((scanValuePrepare (scanValueClearKey s)).emit .value).pendingKeys[i]'hi_emit
         = (scanValuePrepare (scanValueClearKey s)).pendingKeys[i]'hi_prep := by congr 1
    rw [this]
  have h_step3 :
      ((scanValuePrepare (scanValueClearKey s)).pendingKeys[i]'hi_prep).insertBeforeIdx
        = ((scanValueClearKey s).pendingKeys[i]'hi_clear).insertBeforeIdx :=
    scanValuePrepare_pendingKeys_insertBeforeIdx (scanValueClearKey s) i hi_clear hi_prep
  have h_step4 :
      ((scanValueClearKey s).pendingKeys[i]'hi_clear).insertBeforeIdx
        = (s.pendingKeys[i]'hi).insertBeforeIdx := by
    congr 1
    have : (scanValueClearKey s).pendingKeys[i]'hi_clear = s.pendingKeys[i]'hi := by congr 1
    exact this
  rw [h_step1, h_step2, h_step3, h_step4]

theorem scanValue_preserves_PendingKeysWellIndexed (s : ScannerState) (s' : ScannerState)
    (h : scanValue s = .ok s') (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed s' := by
  apply PendingKeysWellIndexed_field_update s s'
    (scanValue_pendingKeys_size s s' h)
    (fun p hp hp' => scanValue_pendingKeys_insertBeforeIdx s s' h p hp hp')
    (by have := scanValue_adds_tokens s s' h; omega)
    h_inv

/-! ### Dispatcher-level invariant preservation -/

theorem dispatchStructural_preserves_pendingKeys (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanDocumentStart_preserves_pendingKeys s
    | exact scanDocumentEnd_preserves_pendingKeys _ _ (by assumption)
    | exact scanDirective_preserves_pendingKeys _ _ (by assumption)
    | (simp_all [scanDocumentStart_preserves_pendingKeys,
        scanDocumentEnd_preserves_pendingKeys, scanDirective_preserves_pendingKeys]; done)

theorem dispatchStructural_preserves_PendingKeysWellIndexed
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed s' := by
  apply PendingKeysWellIndexed_mono s s'
    (dispatchStructural_preserves_pendingKeys s c s' h)
    (ScanHelpers.dispatchStructural_tokens_mono s c s' h)
    h_inv

theorem dispatchFlowIndicators_preserves_pendingKeys (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.pendingKeys = s.pendingKeys := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact scanFlowEntry_preserves_pendingKeys _ _ (by assumption)
    | exact scanFlowSequenceStart_preserves_pendingKeys _
    | exact scanFlowSequenceEnd_preserves_pendingKeys _
    | exact scanFlowMappingStart_preserves_pendingKeys _
    | exact scanFlowMappingEnd_preserves_pendingKeys _
    | (simp_all [scanFlowEntry_preserves_pendingKeys,
        scanFlowSequenceStart_preserves_pendingKeys,
        scanFlowSequenceEnd_preserves_pendingKeys,
        scanFlowMappingStart_preserves_pendingKeys,
        scanFlowMappingEnd_preserves_pendingKeys]; done)

theorem dispatchFlowIndicators_preserves_PendingKeysWellIndexed
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed s' := by
  apply PendingKeysWellIndexed_mono s s'
    (dispatchFlowIndicators_preserves_pendingKeys s c s' h)
    (ScanHelpers.dispatchFlowIndicators_tokens_mono s c s' h)
    h_inv

/-- Block indicators: scanBlockEntry/scanKey are Class A (preserve pendingKeys);
    scanValue is Class C (field-update via scanValuePrepare). -/
theorem dispatchBlockIndicators_preserves_PendingKeysWellIndexed
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed s' := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  -- Case-split on three branches: scanBlockEntry / scanKey / scanValue.
  split at h
  · -- '-': scanBlockEntry
    split at h <;> try contradiction
    rename_i h_be
    simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    apply PendingKeysWellIndexed_mono s _
      (scanBlockEntry_preserves_pendingKeys _ _ h_be)
      (by have := ScanHelpers.scanBlockEntry_adds_tokens _ _ h_be; omega)
      h_inv
  · split at h
    · -- '?': scanKey
      split at h <;> try contradiction
      rename_i h_key
      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
      apply PendingKeysWellIndexed_mono s _
        (scanKey_preserves_pendingKeys _ _ h_key)
        (by have := scanKey_adds_one_token _ _ h_key; omega)
        h_inv
    · split at h
      · -- ':': scanValue
        split at h <;> try contradiction
        rename_i h_val
        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact scanValue_preserves_PendingKeysWellIndexed _ _ h_val h_inv
      · -- fallthrough
        simp at h

/-- Content dispatch: most scanners are Class A; the double-quoted and
    single-quoted branches additionally apply `setPendingKeyEndLine`
    (Class C field-update). -/
theorem dispatchContent_preserves_PendingKeysWellIndexed
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s') (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed s' := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · -- '&': scanAnchorOrAlias true (then push to definedAnchors)
    generalize h_fn : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      -- s' = { s_a with definedAnchors := s_a.definedAnchors.push name }
      apply PendingKeysWellIndexed_mono s _ ?_ ?_ h_inv
      · show s_a.pendingKeys = s.pendingKeys
        exact scanAnchorOrAlias_preserves_pendingKeys s true s_a h_fn
      · show s_a.tokens.size ≥ s.tokens.size
        have := ScanHelpers.scanAnchorOrAlias_adds_one_token s true s_a h_fn; omega
  · split at h
    · -- '*': alias
      split at h
      · simp at h
      · generalize h_fn : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          apply PendingKeysWellIndexed_mono s _
            (scanAnchorOrAlias_preserves_pendingKeys s false s_a h_fn)
            (by have := ScanHelpers.scanAnchorOrAlias_adds_one_token s false s_a h_fn; omega)
            h_inv
    · split at h
      · -- '!': tag
        generalize h_fn : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          apply PendingKeysWellIndexed_mono s _
            (scanTag_preserves_pendingKeys s s_t h_fn)
            (by have := ScanHelpers.scanTag_adds_one_token s s_t h_fn; omega)
            h_inv
      · -- block scalar / quoted / plain
        split at h
        · -- block scalar
          generalize h_fn : scanBlockScalar s = result at h
          cases result with
          | error e => simp at h
          | ok s_b =>
            simp only [Except.ok.injEq] at h; subst h
            apply PendingKeysWellIndexed_mono s _
              (scanBlockScalar_preserves_pendingKeys s s_b h_fn)
              (by have := ScanHelpers.scanBlockScalar_adds_one_token s s_b h_fn; omega)
              h_inv
        · split at h
          · -- '"': scanDoubleQuoted + endLine wrapper (Class C if simpleKey.possible)
            generalize h_fn : scanDoubleQuoted s = result at h
            cases result with
            | error e => simp at h
            | ok s_dq =>
              simp only [Except.ok.injEq] at h; subst h
              -- Inner: s_dq preserves invariant via Class A.
              have h_dq_inv : PendingKeysWellIndexed s_dq :=
                PendingKeysWellIndexed_mono s s_dq
                  (scanDoubleQuoted_preserves_pendingKeys s s_dq h_fn)
                  (by have := ScanHelpers.scanDoubleQuoted_adds_one_token s s_dq h_fn; omega)
                  h_inv
              -- Outer: if simpleKey.possible, wrap with setPendingKeyEndLine.
              show PendingKeysWellIndexed (
                if s_dq.simpleKey.possible then
                  { s_dq with simpleKey := { s_dq.simpleKey with endLine := s_dq.line },
                              pendingKeys := setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line }
                else s_dq)
              split
              · -- field-update branch: Class C
                apply PendingKeysWellIndexed_field_update s_dq _
                  (by simp [setPendingKeyEndLine_size])
                  (fun p hp hp' => setPendingKeyEndLine_insertBeforeIdx s_dq.pendingKeys
                    s_dq.pendingKeyActive s_dq.line p hp hp')
                  (by show s_dq.tokens.size ≥ s_dq.tokens.size; omega)
                  h_dq_inv
              · exact h_dq_inv
          · split at h
            · -- '\'': scanSingleQuoted + endLine wrapper
              generalize h_fn : scanSingleQuoted s = result at h
              cases result with
              | error e => simp at h
              | ok s_sq =>
                simp only [Except.ok.injEq] at h; subst h
                have h_sq_inv : PendingKeysWellIndexed s_sq :=
                  PendingKeysWellIndexed_mono s s_sq
                    (scanSingleQuoted_preserves_pendingKeys s s_sq h_fn)
                    (by have := ScanHelpers.scanSingleQuoted_adds_one_token s s_sq h_fn; omega)
                    h_inv
                show PendingKeysWellIndexed (
                  if s_sq.simpleKey.possible then
                    { s_sq with simpleKey := { s_sq.simpleKey with endLine := s_sq.line },
                                pendingKeys := setPendingKeyEndLine s_sq.pendingKeys s_sq.pendingKeyActive s_sq.line }
                  else s_sq)
                split
                · apply PendingKeysWellIndexed_field_update s_sq _
                    (by simp [setPendingKeyEndLine_size])
                    (fun p hp hp' => setPendingKeyEndLine_insertBeforeIdx s_sq.pendingKeys
                      s_sq.pendingKeyActive s_sq.line p hp hp')
                    (by show s_sq.tokens.size ≥ s_sq.tokens.size; omega)
                    h_sq_inv
                · exact h_sq_inv
            · -- plain scalar (or error)
              split at h
              · generalize h_fn : scanPlainScalar s = result at h
                cases result with
                | error e => simp at h
                | ok s_p =>
                  simp only [Except.ok.injEq] at h; subst h
                  apply PendingKeysWellIndexed_mono s _
                    (scanPlainScalar_preserves_pendingKeys s s_p h_fn)
                    (by have := ScanHelpers.scanPlainScalar_adds_one_token s s_p h_fn; omega)
                    h_inv
              · simp at h

/-- preprocess: composes skipToContent (A) + unwindIndents (A) + saveSimpleKey (B). -/
theorem preprocess_preserves_PendingKeysWellIndexed (s : ScannerState) (s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed s1 := by
  unfold scanNextToken_preprocess at h
  simp only [bind, ScanHelpers.bind_error_simp, ScanHelpers.bind_ok_simp,
             pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_skip_inv : PendingKeysWellIndexed s_skip :=
      PendingKeysWellIndexed_mono s s_skip
        (skipToContent_preserves_pendingKeys s s_skip h_skip)
        (by rw [skipToContent_preserves_tokens s s_skip h_skip]; omega)
        h_inv
    split at h
    · simp at h
    · split at h
      · -- needIndentCheck path
        split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            -- s1 = saveSimpleKey { unwindIndents s_skip s_skip.col with needIndentCheck := false }
            -- Step 1: unwindIndents preserves invariant
            have h_unwind_inv : PendingKeysWellIndexed (unwindIndents s_skip s_skip.col) :=
              PendingKeysWellIndexed_mono s_skip _
                (unwindIndents_preserves_pendingKeys s_skip s_skip.col)
                (unwindIndents_adds_tokens s_skip s_skip.col)
                h_skip_inv
            -- Step 2: needIndentCheck := false is a non-pendingKeys/tokens field
            have h_pre_inv : PendingKeysWellIndexed
                { unwindIndents s_skip s_skip.col with needIndentCheck := false } :=
              PendingKeysWellIndexed_mono _ _ rfl (by show _ ≥ _; omega) h_unwind_inv
            -- Step 3: saveSimpleKey is Class B (uses dedicated lemma)
            exact saveSimpleKey_preserves_PendingKeysWellIndexed _ h_pre_inv
      · -- no needIndentCheck path
        split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            exact saveSimpleKey_preserves_PendingKeysWellIndexed _ h_skip_inv

/-! ### scanNextToken preserves PendingKeysWellIndexed -/

theorem allowDir_ite_preserves_PendingKeysWellIndexed (s : ScannerState)
    (h_inv : PendingKeysWellIndexed s) :
    PendingKeysWellIndexed (if s.allowDirectives then
      { s with allowDirectives := false, documentEverStarted := true } else s) := by
  split
  · exact PendingKeysWellIndexed_mono s _ rfl (Nat.le_refl _) h_inv
  · exact h_inv

theorem scanNextToken_preserves_PendingKeysWellIndexed
    (s s' : ScannerState) (h_inv : PendingKeysWellIndexed s)
    (h_ok : scanNextToken s = .ok (some s')) : PendingKeysWellIndexed s' := by
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> (try (simp at h_ok; done)) -- preprocess Except
  split at h_ok <;> (try (simp at h_ok; done)) -- preprocess Option
  rename_i s2 c h_pre
  have h_inv2 := preprocess_preserves_PendingKeysWellIndexed s s2 c h_pre h_inv
  split at h_ok <;> (try (simp at h_ok; done)) -- structural Except
  split at h_ok
  · -- structural some
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchStructural_preserves_PendingKeysWellIndexed s2 c _ (by assumption) h_inv2
  · -- structural none → continue
    have h_inv3 := allowDir_ite_preserves_PendingKeysWellIndexed s2 h_inv2
    -- checkBlockFlowIndent
    split at h_ok <;> (try (simp at h_ok; done))
    -- Flow Except
    split at h_ok <;> (try (simp at h_ok; done))
    -- Flow Option
    split at h_ok
    · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchFlowIndicators_preserves_PendingKeysWellIndexed _ c _ (by assumption) h_inv3
    · -- block Except
      split at h_ok <;> (try (simp at h_ok; done))
      split at h_ok
      · simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchBlockIndicators_preserves_PendingKeysWellIndexed _ c _ (by assumption) h_inv3
      · -- content
        split at h_ok <;> (try (simp at h_ok; done))
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_PendingKeysWellIndexed _ c _ (by assumption) h_inv3

/-! ### scanLoopFull preserves PendingKeysWellIndexed

By induction on fuel.  Recursive arm: apply scanNextToken preservation,
then IH.  Completion arm: skipToContent (Class A) + unwindIndents
(Class A) + emit .streamEnd, all preserving the invariant. -/
theorem scanLoopFull_preserves_PendingKeysWellIndexed
    (s : ScannerState) (fuel : Nat) (final : ScannerState)
    (h_inv : PendingKeysWellIndexed s)
    (h : scanLoopFull s fuel = .ok final) : PendingKeysWellIndexed final := by
  induction fuel generalizing s with
  | zero => unfold scanLoopFull at h; simp at h
  | succ fuel' IH =>
    unfold scanLoopFull at h
    simp only [] at h
    split at h
    · simp at h
    · -- .ok none: completion arm
      split at h
      · simp at h  -- flowLevel > 0 → error
      · split at h
        · simp at h  -- directives without document
        · -- normal completion
          injection h with h_eq
          subst h_eq
          cases h_skip : skipToContent s with
          | ok s_skip =>
            show PendingKeysWellIndexed ((unwindIndents s_skip (-1)).emit .streamEnd)
            have h_skip_inv : PendingKeysWellIndexed s_skip :=
              PendingKeysWellIndexed_mono s s_skip
                (skipToContent_preserves_pendingKeys s s_skip h_skip)
                (by rw [skipToContent_preserves_tokens s s_skip h_skip]; omega)
                h_inv
            have h_unwind_inv : PendingKeysWellIndexed (unwindIndents s_skip (-1)) :=
              PendingKeysWellIndexed_mono s_skip _
                (unwindIndents_preserves_pendingKeys s_skip (-1))
                (unwindIndents_adds_tokens s_skip (-1))
                h_skip_inv
            apply PendingKeysWellIndexed_mono _ _
              (emit_preserves_pendingKeys (unwindIndents s_skip (-1)) .streamEnd)
              (by rw [emit_tokens_size]; omega)
              h_unwind_inv
          | error e =>
            -- skipToContent failed in the live path — but scanLoopFull's
            -- branch unfolds with the same `s` whether skipToContent
            -- succeeds or not (skipToContent isn't actually called here).
            -- The branch we're in just emits streamEnd via unwindIndents s.
            show PendingKeysWellIndexed ((unwindIndents s (-1)).emit .streamEnd)
            have h_unwind_inv : PendingKeysWellIndexed (unwindIndents s (-1)) :=
              PendingKeysWellIndexed_mono s _
                (unwindIndents_preserves_pendingKeys s (-1))
                (unwindIndents_adds_tokens s (-1))
                h_inv
            apply PendingKeysWellIndexed_mono _ _
              (emit_preserves_pendingKeys (unwindIndents s (-1)) .streamEnd)
              (by rw [emit_tokens_size]; omega)
              h_unwind_inv
    · -- .ok (some s'): recursive arm
      rename_i s' h_snt
      exact IH s'
        (scanNextToken_preserves_PendingKeysWellIndexed s s' h_inv h_snt)
        h

/-!
### LineariseFit: bundle of position invariants on (tokens, pendingKeys)

Added in **Phase J.3.3 step 8** (2026-04-27).  The invariant captures
exactly the hypotheses `linearise_positions_ordered` (in
`Proofs/Scanner/ScannerLinearise.lean`) consumes:

* `PendingKeysWellIndexed` (existing): every entry's `insertBeforeIdx`
  is in `[1, tokens.size]`.
* **Sorted-pks**: pks are non-decreasing in both `insertBeforeIdx` and
  `pos.offset` (saveSimpleKey appends with `idx = current size` and
  `pos = currentPos`, both monotone).
* **I1** (low-side fit): every token strictly before `e.insertBeforeIdx`
  has offset ≤ `e.pos.offset`.  Holds because at save time, `e.pos =
  currentPos` and ScanInv gives `tokens[i].offset ≤ currentPos`; later
  emits only add tokens at indices ≥ `e.insertBeforeIdx`.
* **I2** (high-side fit): every token at index ≥ `e.insertBeforeIdx`
  has offset ≥ `e.pos.offset`.  Holds because new tokens emitted after
  the save have offset ≥ `currentPos at save = e.pos.offset` (offset
  monotonicity).
* **I4** (offset bound): `e.pos.offset ≤ s.offset` (trivially true at
  save time and preserved by offset monotonicity).

Bundled with the tokens-sorted property from `ScanInv`, this gives the
exact preconditions for `linearise_positions_ordered` at the scanFiltered
call site. -/

/-- The full positional well-formedness bundle on `(tokens, pendingKeys)`.

    Uses explicit `Nat + bound` indexing throughout (rather than `Fin`)
    so that mono lemmas can rewrite array equalities cleanly via
    `array_get_eq_of_array_eq` without elaboration mismatch between
    `arr[p]` (Fin) and `arr[p.val]'p.isLt` (Nat) elaborations. -/
def LineariseFit (s : ScannerState) : Prop :=
  ScanInv s ∧
  PendingKeysWellIndexed s ∧
  -- pks sorted (idx and pos both non-decreasing)
  (∀ p q (hp : p < s.pendingKeys.size) (hq : q < s.pendingKeys.size), p < q →
    (s.pendingKeys[p]'hp).insertBeforeIdx ≤ (s.pendingKeys[q]'hq).insertBeforeIdx) ∧
  (∀ p q (hp : p < s.pendingKeys.size) (hq : q < s.pendingKeys.size), p < q →
    (s.pendingKeys[p]'hp).pos.offset ≤ (s.pendingKeys[q]'hq).pos.offset) ∧
  -- I1: tokens strictly before insertBeforeIdx have offset ≤ pos
  (∀ p (hp : p < s.pendingKeys.size) i (hi : i < s.tokens.size),
    i < (s.pendingKeys[p]'hp).insertBeforeIdx →
    (s.tokens[i]'hi).pos.offset ≤ (s.pendingKeys[p]'hp).pos.offset) ∧
  -- I2: tokens at/after insertBeforeIdx have offset ≥ pos
  (∀ p (hp : p < s.pendingKeys.size) i (hi : i < s.tokens.size),
    (s.pendingKeys[p]'hp).insertBeforeIdx ≤ i →
    (s.pendingKeys[p]'hp).pos.offset ≤ (s.tokens[i]'hi).pos.offset) ∧
  -- I4: pks pos bounded by current offset
  (∀ p (hp : p < s.pendingKeys.size), (s.pendingKeys[p]'hp).pos.offset ≤ s.offset)

/-- Indexing helper: array equality + same index gives element equality. -/
theorem array_get_eq_of_array_eq {α : Type _} {a b : Array α}
    (h : a = b) (i : Nat) (h1 : i < a.size) (h2 : i < b.size) :
    a[i]'h1 = b[i]'h2 := by subst h; rfl

/-! #### Generic mono lemma: no-token-change ops preserve LineariseFit

Class A leaves that leave `tokens` unchanged (skipSpaces, skipWhitespace,
allowDir-ite, etc.) preserve every conjunct trivially (offset-mono only
strengthens the `pos ≤ offset` bound; pks unchanged so all pks-side
conjuncts hold; tokens unchanged so I1/I2 hold). -/
theorem LineariseFit_no_token_change (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_tok_eq : s'.tokens = s.tokens)
    (h_off_mono : s'.offset ≥ s.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  obtain ⟨_, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩ := h
  refine ⟨h_inv', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- PendingKeysWellIndexed
    exact PendingKeysWellIndexed_mono s s' h_pks_eq
      (by rw [h_tok_eq]; omega) h_well
  · -- pks sorted by idx
    intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hq_s : q < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hp_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    have hq_get : s'.pendingKeys[q]'hq = s.pendingKeys[q]'hq_s :=
      array_get_eq_of_array_eq h_pks_eq q hq hq_s
    rw [hp_get, hq_get]
    exact h_idx p q hp_s hq_s hpq
  · -- pks sorted by pos
    intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hq_s : q < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hp_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    have hq_get : s'.pendingKeys[q]'hq = s.pendingKeys[q]'hq_s :=
      array_get_eq_of_array_eq h_pks_eq q hq hq_s
    rw [hp_get, hq_get]
    exact h_pos p q hp_s hq_s hpq
  · -- I1
    intro p hp i hi h_lt
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hi_s : i < s.tokens.size := by
      have h_size_eq : s'.tokens.size = s.tokens.size := by rw [h_tok_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    have h_tok_get : s'.tokens[i]'hi = s.tokens[i]'hi_s :=
      array_get_eq_of_array_eq h_tok_eq i hi hi_s
    rw [h_pks_get, h_tok_get]
    rw [h_pks_get] at h_lt
    exact h_lo p hp_s i hi_s h_lt
  · -- I2
    intro p hp i hi h_ge
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hi_s : i < s.tokens.size := by
      have h_size_eq : s'.tokens.size = s.tokens.size := by rw [h_tok_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    have h_tok_get : s'.tokens[i]'hi = s.tokens[i]'hi_s :=
      array_get_eq_of_array_eq h_tok_eq i hi hi_s
    rw [h_pks_get, h_tok_get]
    rw [h_pks_get] at h_ge
    exact h_hi p hp_s i hi_s h_ge
  · -- I4: pos ≤ offset
    intro p hp
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    rw [h_pks_get]
    exact Nat.le_trans (h_off p hp_s) h_off_mono

/-! #### Mono lemma: emit-one (single token append) preserves LineariseFit

Covers `emit`, `emitAt` at startPos, and any composite that adds exactly
one token whose offset is between `s.offset` (old) and `s'.offset` (new). -/
theorem LineariseFit_emit_one (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_size : s'.tokens.size = s.tokens.size + 1)
    (h_old : ∀ i (hi : i < s.tokens.size),
        (s'.tokens[i]'(by omega)).pos.offset = (s.tokens[i]'hi).pos.offset)
    (h_new_ge : (s'.tokens[s.tokens.size]'(by omega)).pos.offset ≥ s.offset)
    (h_off_mono : s'.offset ≥ s.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  obtain ⟨_, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩ := h
  refine ⟨h_inv', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PendingKeysWellIndexed_mono s s' h_pks_eq (by omega) h_well
  · intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hq_s : q < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hp_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    have hq_get : s'.pendingKeys[q]'hq = s.pendingKeys[q]'hq_s :=
      array_get_eq_of_array_eq h_pks_eq q hq hq_s
    rw [hp_get, hq_get]
    exact h_idx p q hp_s hq_s hpq
  · intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hq_s : q < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hp_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    have hq_get : s'.pendingKeys[q]'hq = s.pendingKeys[q]'hq_s :=
      array_get_eq_of_array_eq h_pks_eq q hq hq_s
    rw [hp_get, hq_get]
    exact h_pos p q hp_s hq_s hpq
  · -- I1
    intro p hp i hi h_lt
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    rw [h_pks_get]
    rw [h_pks_get] at h_lt
    by_cases hi_s : i < s.tokens.size
    · rw [h_old i hi_s]; exact h_lo p hp_s i hi_s h_lt
    · -- i = s.tokens.size: new index ≥ insertBeforeIdx ≤ s.tokens.size = i
      have hi_eq : i = s.tokens.size := by omega
      have ⟨_, h_idx_le⟩ := h_well.2 p hp_s
      omega
  · -- I2
    intro p hp i hi h_ge
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    rw [h_pks_get]
    rw [h_pks_get] at h_ge
    by_cases hi_s : i < s.tokens.size
    · rw [h_old i hi_s]; exact h_hi p hp_s i hi_s h_ge
    · have hi_eq : i = s.tokens.size := by omega
      subst hi_eq
      exact Nat.le_trans (h_off p hp_s) h_new_ge
  · intro p hp
    have hp_s : p < s.pendingKeys.size := by
      have h_size_eq : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    rw [h_pks_get]
    exact Nat.le_trans (h_off p hp_s) h_off_mono

/-! #### Field-update lemma for setPendingKeyKind / setPendingKeyEndLine

These ops preserve pendingKeys size, every entry's `insertBeforeIdx`,
and every entry's `pos`.  Tokens unchanged.  All conjuncts of
LineariseFit are preserved. -/
theorem LineariseFit_field_update (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_size_eq : s'.pendingKeys.size = s.pendingKeys.size)
    (h_idx_eq : ∀ p (hp : p < s.pendingKeys.size)
                  (hp' : p < s'.pendingKeys.size),
                  (s'.pendingKeys[p]'hp').insertBeforeIdx
                    = (s.pendingKeys[p]'hp).insertBeforeIdx)
    (h_pos_eq : ∀ p (hp : p < s.pendingKeys.size)
                  (hp' : p < s'.pendingKeys.size),
                  (s'.pendingKeys[p]'hp').pos
                    = (s.pendingKeys[p]'hp).pos)
    (h_tok_eq : s'.tokens = s.tokens)
    (h_off_eq : s'.offset = s.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  obtain ⟨_, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩ := h
  refine ⟨h_inv', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PendingKeysWellIndexed_field_update s s' h_size_eq h_idx_eq
      (by rw [h_tok_eq]; omega) h_well
  · intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by omega
    have hq_s : q < s.pendingKeys.size := by omega
    rw [h_idx_eq p hp_s hp, h_idx_eq q hq_s hq]
    exact h_idx p q hp_s hq_s hpq
  · intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by omega
    have hq_s : q < s.pendingKeys.size := by omega
    rw [h_pos_eq p hp_s hp, h_pos_eq q hq_s hq]
    exact h_pos p q hp_s hq_s hpq
  · intro p hp i hi h_lt
    have hp_s : p < s.pendingKeys.size := by omega
    have hi_s : i < s.tokens.size := by
      have h_size_eq : s'.tokens.size = s.tokens.size := by rw [h_tok_eq]
      omega
    have h_tok_get : s'.tokens[i]'hi = s.tokens[i]'hi_s :=
      array_get_eq_of_array_eq h_tok_eq i hi hi_s
    rw [h_tok_get, h_pos_eq p hp_s hp]
    rw [h_idx_eq p hp_s hp] at h_lt
    exact h_lo p hp_s i hi_s h_lt
  · intro p hp i hi h_ge
    have hp_s : p < s.pendingKeys.size := by omega
    have hi_s : i < s.tokens.size := by
      have h_size_eq : s'.tokens.size = s.tokens.size := by rw [h_tok_eq]
      omega
    have h_tok_get : s'.tokens[i]'hi = s.tokens[i]'hi_s :=
      array_get_eq_of_array_eq h_tok_eq i hi hi_s
    rw [h_tok_get, h_pos_eq p hp_s hp]
    rw [h_idx_eq p hp_s hp] at h_ge
    exact h_hi p hp_s i hi_s h_ge
  · intro p hp
    have hp_s : p < s.pendingKeys.size := by omega
    rw [h_pos_eq p hp_s hp, h_off_eq]
    exact h_off p hp_s

/-! #### saveSimpleKey-specific preservation

`saveSimpleKey` either is identity on pendingKeys (guard fails) or
appends one new entry with `insertBeforeIdx = s.tokens.size` and
`pos = s.currentPos` (offset = `s.offset`).  All conjuncts re-establish
naturally:
* idx-sorted: previous idx ≤ s.tokens.size = new idx (PendingKeysWellIndexed).
* pos-sorted: previous pos ≤ s.offset = new pos (I4).
* I1 for new entry: tokens[i].offset ≤ s.offset = new pos (ScanInv).
* I2 for new entry: vacuous (no tokens at index ≥ tokens.size).
* I4 for new entry: new pos = s.offset ≤ s.offset. -/
theorem saveSimpleKey_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (saveSimpleKey s) := by
  obtain ⟨h_inv, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩ := h
  unfold saveSimpleKey
  split
  · exact ⟨h_inv, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩
  · split
    · -- simpleKeyAllowed branch: appends new entry
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · -- ScanInv: tokens and offset unchanged from s
        exact h_inv
      · -- PendingKeysWellIndexed
        refine ⟨h_well.1, ?_⟩
        intro p hp
        by_cases h_p_lt : p < s.pendingKeys.size
        · have ⟨hb_lo, hb_hi⟩ := h_well.2 p h_p_lt
          show 1 ≤ _ ∧ _
          rw [Array.getElem_push_lt h_p_lt]
          exact ⟨hb_lo, hb_hi⟩
        · have h_p_eq : p = s.pendingKeys.size := by
            have := hp; simp [Array.size_push] at this; omega
          subst h_p_eq
          show 1 ≤ _ ∧ _
          rw [Array.getElem_push_eq]
          exact ⟨h_well.1, Nat.le_refl _⟩
      · -- pks sorted by idx
        intro p q hp hq hpq
        have hp_b : p < s.pendingKeys.size + 1 := by
          simp [Array.size_push] at hp; exact hp
        have hq_b : q < s.pendingKeys.size + 1 := by
          simp [Array.size_push] at hq; exact hq
        by_cases hp_lt : p < s.pendingKeys.size
        · by_cases hq_lt : q < s.pendingKeys.size
          · -- both old
            show (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[p].insertBeforeIdx ≤
                (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[q].insertBeforeIdx
            rw [Array.getElem_push_lt hp_lt, Array.getElem_push_lt hq_lt]
            exact h_idx p q hp_lt hq_lt hpq
          · -- p old, q new
            have hq_eq : q = s.pendingKeys.size := by omega
            show (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[p].insertBeforeIdx ≤
                (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[q].insertBeforeIdx
            subst hq_eq
            rw [Array.getElem_push_lt hp_lt]
            rw [Array.getElem_push_eq]
            exact (h_well.2 p hp_lt).2
        · omega
      · -- pks sorted by pos
        intro p q hp hq hpq
        have hp_b : p < s.pendingKeys.size + 1 := by
          simp [Array.size_push] at hp; exact hp
        have hq_b : q < s.pendingKeys.size + 1 := by
          simp [Array.size_push] at hq; exact hq
        by_cases hp_lt : p < s.pendingKeys.size
        · by_cases hq_lt : q < s.pendingKeys.size
          · show (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[p].pos.offset ≤
                (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[q].pos.offset
            rw [Array.getElem_push_lt hp_lt, Array.getElem_push_lt hq_lt]
            exact h_pos p q hp_lt hq_lt hpq
          · have hq_eq : q = s.pendingKeys.size := by omega
            show (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[p].pos.offset ≤
                (s.pendingKeys.push
                    { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
                      endLine := s.line, kind := .unresolved })[q].pos.offset
            subst hq_eq
            rw [Array.getElem_push_lt hp_lt]
            rw [Array.getElem_push_eq]
            show s.pendingKeys[p].pos.offset ≤ (ScannerState.currentPos s).offset
            simp [ScannerState.currentPos]
            exact h_off p hp_lt
        · omega
      · -- I1
        intro p hp i hi h_lt
        have hi_s : i < s.tokens.size := hi
        by_cases hp_lt : p < s.pendingKeys.size
        · -- old entry
          show (s.tokens[i]'hi_s).pos.offset ≤ (s.pendingKeys.push _)[p].pos.offset
          rw [Array.getElem_push_lt hp_lt]
          rw [Array.getElem_push_lt hp_lt] at h_lt
          exact h_lo p hp_lt i hi_s h_lt
        · have h_p_eq : p = s.pendingKeys.size := by
            have := hp; simp [Array.size_push] at this; omega
          subst h_p_eq
          show (s.tokens[i]'hi_s).pos.offset ≤ (s.pendingKeys.push _)[s.pendingKeys.size].pos.offset
          rw [Array.getElem_push_eq]
          show (s.tokens[i]'hi_s).pos.offset ≤ s.currentPos.offset
          simp [ScannerState.currentPos]
          exact h_inv.2 ⟨i, hi_s⟩
      · -- I2
        intro p hp i hi h_ge
        have hi_s : i < s.tokens.size := hi
        by_cases hp_lt : p < s.pendingKeys.size
        · show (s.pendingKeys.push _)[p].pos.offset ≤ (s.tokens[i]'hi_s).pos.offset
          rw [Array.getElem_push_lt hp_lt]
          rw [Array.getElem_push_lt hp_lt] at h_ge
          exact h_hi p hp_lt i hi_s h_ge
        · have h_p_eq : p = s.pendingKeys.size := by
            have := hp; simp [Array.size_push] at this; omega
          subst h_p_eq
          rw [Array.getElem_push_eq] at h_ge
          change s.tokens.size ≤ i at h_ge
          exfalso
          omega
      · -- I4
        intro p hp
        by_cases hp_lt : p < s.pendingKeys.size
        · show (s.pendingKeys.push _)[p].pos.offset ≤ s.offset
          rw [Array.getElem_push_lt hp_lt]
          exact h_off p hp_lt
        · have h_p_eq : p = s.pendingKeys.size := by
            have := hp; simp [Array.size_push] at this; omega
          subst h_p_eq
          show (s.pendingKeys.push _)[s.pendingKeys.size].pos.offset ≤ s.offset
          rw [Array.getElem_push_eq]
          show s.currentPos.offset ≤ s.offset
          simp [ScannerState.currentPos]
    · exact ⟨h_inv, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩

/-! #### Generalized mono lemma: `LineariseFit_extend`

Subsumes both `LineariseFit_no_token_change` and `LineariseFit_emit_one`.
Handles any Class A op that:
* preserves pendingKeys (`h_pks_eq`),
* appends zero or more tokens with old indices preserved (`h_prefix`),
* has new tokens (if any) emitted at offsets ≥ `s.offset` (`h_new_ge`),
* has monotone offset (`h_off_mono`),
* preserves `ScanInv` (`h_inv'`).

This is the workhorse used by every per-op `*_preserves_LineariseFit`. -/
theorem LineariseFit_extend (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_size_mono : s.tokens.size ≤ s'.tokens.size)
    (h_prefix : ∀ i (hi : i < s.tokens.size),
        s'.tokens[i]'(by omega) = s.tokens[i]'hi)
    (h_new_ge : ∀ i (hi : i < s'.tokens.size), s.tokens.size ≤ i →
        s.offset ≤ (s'.tokens[i]'hi).pos.offset)
    (h_off_mono : s.offset ≤ s'.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  obtain ⟨_, h_well, h_idx, h_pos, h_lo, h_hi, h_off⟩ := h
  refine ⟨h_inv', ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact PendingKeysWellIndexed_mono s s' h_pks_eq h_size_mono h_well
  · intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hq_s : q < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    rw [array_get_eq_of_array_eq h_pks_eq p hp hp_s,
        array_get_eq_of_array_eq h_pks_eq q hq hq_s]
    exact h_idx p q hp_s hq_s hpq
  · intro p q hp hq hpq
    have hp_s : p < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have hq_s : q < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    rw [array_get_eq_of_array_eq h_pks_eq p hp hp_s,
        array_get_eq_of_array_eq h_pks_eq q hq hq_s]
    exact h_pos p q hp_s hq_s hpq
  · intro p hp i hi h_lt
    have hp_s : p < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    rw [h_pks_get]
    rw [h_pks_get] at h_lt
    -- i < insertBeforeIdx ≤ s.tokens.size by PendingKeysWellIndexed
    have ⟨_, h_idx_le⟩ := h_well.2 p hp_s
    have hi_s : i < s.tokens.size := by omega
    rw [h_prefix i hi_s]
    exact h_lo p hp_s i hi_s h_lt
  · intro p hp i hi h_ge
    have hp_s : p < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    have h_pks_get : s'.pendingKeys[p]'hp = s.pendingKeys[p]'hp_s :=
      array_get_eq_of_array_eq h_pks_eq p hp hp_s
    rw [h_pks_get]
    rw [h_pks_get] at h_ge
    by_cases hi_s : i < s.tokens.size
    · rw [h_prefix i hi_s]
      exact h_hi p hp_s i hi_s h_ge
    · have h_i_ge : s.tokens.size ≤ i := by omega
      exact Nat.le_trans (h_off p hp_s) (h_new_ge i hi h_i_ge)
  · intro p hp
    have hp_s : p < s.pendingKeys.size := by
      have h_se : s'.pendingKeys.size = s.pendingKeys.size := by rw [h_pks_eq]
      omega
    rw [array_get_eq_of_array_eq h_pks_eq p hp hp_s]
    exact Nat.le_trans (h_off p hp_s) h_off_mono

/-! #### Convenience: Class A passthrough with no token change

For ops where `s'.tokens = s.tokens` and `s'.pendingKeys = s.pendingKeys`
and offset is monotone — covers all skip*, advance*, and most non-emitting
helpers.  Just instantiates `LineariseFit_extend` with size-eq + refl. -/
theorem LineariseFit_via_no_change (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_tok_eq : s'.tokens = s.tokens)
    (h_off_mono : s.offset ≤ s'.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  have h_size : s'.tokens.size = s.tokens.size := by rw [h_tok_eq]
  apply LineariseFit_extend s s' h_inv' h_pks_eq (by omega)
  · intro i hi
    exact array_get_eq_of_array_eq h_tok_eq i (by omega) hi
  · intro i _ h_ge; omega
  · exact h_off_mono
  · exact h

/-! #### Helper: first new token position from `emitAt` -/

/-- The token at index `n` in `(s_after.emitAt pos tok).tokens` is `{pos := pos, val := tok}`
    when `s_after.tokens.size = n`.  Used by emitAt-class ops where the loop preserves
    the token array but the index in the goal is from the caller (`s.tokens.size`). -/
theorem first_new_pos_emitAt (s_after : ScannerState) (pos : YamlPos)
    (tok : YamlToken) (n : Nat) (h_eq : s_after.tokens.size = n)
    (h_lt : n < (s_after.emitAt pos tok).tokens.size) :
    ((s_after.emitAt pos tok).tokens[n]'h_lt).pos = pos := by
  subst h_eq
  have h : (s_after.emitAt pos tok).tokens[s_after.tokens.size]'h_lt =
      ⟨pos, tok, pos⟩ := by
    show (s_after.tokens.push ⟨pos, tok, pos⟩)[s_after.tokens.size] = _
    exact Array.getElem_push_eq
  rw [h]

/-! #### Helper: derive off_mono from first_new + ScanInv at s' -/

theorem offset_mono_via_first_new
    (s s' : ScannerState) (h_inv' : ScanInv s')
    (h_lt : s.tokens.size < s'.tokens.size)
    (h_first_new : s.offset ≤ (s'.tokens[s.tokens.size]'h_lt).pos.offset) :
    s.offset ≤ s'.offset :=
  Nat.le_trans h_first_new (h_inv'.2 ⟨s.tokens.size, h_lt⟩)

/-! #### Convenience: only need first-new-token's offset bound

For multi-emit Class A ops, instead of bounding *every* new token's
offset, it suffices to bound the *first* new token's offset.  ScanInv
at `s'` gives sorted tokens, so all subsequent new tokens (at indices
> `s.tokens.size`) inherit the bound from the first new token's. -/
theorem LineariseFit_via_first_new (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_size_mono : s.tokens.size ≤ s'.tokens.size)
    (h_prefix : ∀ i (hi : i < s.tokens.size),
        s'.tokens[i]'(by omega) = s.tokens[i]'hi)
    (h_first_new : ∀ (h_lt : s.tokens.size < s'.tokens.size),
        s.offset ≤ (s'.tokens[s.tokens.size]'h_lt).pos.offset)
    (h_off_mono : s.offset ≤ s'.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_extend s s' h_inv' h_pks_eq h_size_mono h_prefix
    ?new_ge h_off_mono h
  case new_ge =>
    intro i hi h_ge
    by_cases h_eq : i = s.tokens.size
    · subst h_eq
      exact h_first_new hi
    · -- i > s.tokens.size, use ScanInv's sorted property
      have h_lt : s.tokens.size < i := by omega
      have h_lt_size : s.tokens.size < s'.tokens.size := by omega
      have h_sorted := h_inv'.1 ⟨s.tokens.size, h_lt_size⟩ ⟨i, hi⟩ h_lt
      exact Nat.le_trans (h_first_new h_lt_size) h_sorted

/-! #### Convenience: derive off_mono automatically when at least one token is added

For ops that always add ≥ 1 token (so we have `s.tokens.size < s'.tokens.size`),
we can derive `h_off_mono` from `h_first_new` + ScanInv at s'. -/
theorem LineariseFit_via_first_new_strict (s s' : ScannerState)
    (h_inv' : ScanInv s')
    (h_pks_eq : s'.pendingKeys = s.pendingKeys)
    (h_size_mono : s.tokens.size < s'.tokens.size)
    (h_prefix : ∀ i (hi : i < s.tokens.size),
        s'.tokens[i]'(by omega) = s.tokens[i]'hi)
    (h_first_new : s.offset ≤ (s'.tokens[s.tokens.size]'h_size_mono).pos.offset)
    (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new s s' h_inv' h_pks_eq (by omega) h_prefix
    (fun _ => h_first_new)
    (offset_mono_via_first_new s s' h_inv' h_size_mono h_first_new)
    h

/-! #### Class A passthrough leaves (`*_preserves_LineariseFit`)

For each scanner op that preserves both `tokens` and `pendingKeys` and
has monotone `offset`, derive `LineariseFit` preservation by composing
existing per-op `*_preserves_tokens`, `*_preserves_pendingKeys`,
`*_preserves_ScanInv`, and `*_offset_ge` lemmas through the
`LineariseFit_via_no_change` helper. -/

theorem advance_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit s.advance :=
  LineariseFit_via_no_change s s.advance
    (advance_preserves_ScanInv s h.1)
    (advance_preserves_pendingKeys s)
    (advance_preserves_tokens s)
    (ScannerProgress.advance_offset_ge s) h

theorem skipSpaces_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (skipSpaces s) :=
  LineariseFit_via_no_change s (skipSpaces s)
    (skipSpaces_preserves_ScanInv s h.1)
    (skipSpaces_preserves_pendingKeys s)
    (skipSpaces_preserves_tokens s)
    (skipSpaces_offset_ge s) h

theorem skipWhitespace_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (skipWhitespace s) :=
  LineariseFit_via_no_change s (skipWhitespace s)
    (skipWhitespace_preserves_ScanInv s h.1)
    (skipWhitespace_preserves_pendingKeys s)
    (skipWhitespace_preserves_tokens s)
    (skipWhitespace_offset_ge s) h

theorem skipToEndOfLine_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (skipToEndOfLine s) :=
  LineariseFit_via_no_change s (skipToEndOfLine s)
    (skipToEndOfLine_preserves_ScanInv s h.1)
    (skipToEndOfLine_preserves_pendingKeys s)
    (skipToEndOfLine_preserves_tokens s)
    (skipToEndOfLine_offset_ge s) h

theorem consumeNewline_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (consumeNewline s) :=
  LineariseFit_via_no_change s (consumeNewline s)
    (consumeNewline_preserves_ScanInv s h.1)
    (consumeNewline_preserves_pendingKeys s)
    (consumeNewline_preserves_tokens s)
    (consumeNewline_offset_ge s) h

-- skipToContent_preserves_LineariseFit deferred until after
-- skipToContent_offset_ge (defined later in the file at §5.2).

/-! #### Class A emit-class leaves: emit

`emit s tok` pushes a token at `s.currentPos`, so the new token has
offset = `s.offset`.  Offset is unchanged. -/

theorem emit_preserves_LineariseFit (s : ScannerState) (tok : YamlToken)
    (h : LineariseFit s) : LineariseFit (s.emit tok) := by
  apply LineariseFit_extend s (s.emit tok)
    (emit_preserves_ScanInv s tok h.1)
    (emit_preserves_pendingKeys s tok)
    (by rw [emit_tokens_size]; omega)
    (fun i hi => emit_preserves_tokens_at s tok i hi)
    ?new_ge
    ?off_mono
    h
  case new_ge =>
    intro i hi h_ge
    have h_emit_size := emit_tokens_size s tok
    have hi_eq : i = s.tokens.size := by omega
    subst hi_eq
    show s.offset ≤ ((s.emit tok).tokens[s.tokens.size]'hi).pos.offset
    have h_pos_eq : ((s.emit tok).tokens[s.tokens.size]'hi).pos = s.currentPos := by
      simp [ScannerState.emit, Array.getElem_push_eq]
    rw [h_pos_eq]
    simp [ScannerState.currentPos]
  case off_mono =>
    show s.offset ≤ (s.emit tok).offset
    rw [ScannerProgress.emit_offset]; omega

/-! #### scanFlow* emit-class leaves

Each `scanFlow{Sequence,Mapping}{Start,End}` and `scanFlowEntry` op
follows the same shape: optional simpleKey/pendingKeyActive disable
(no offset/tokens change) → `.emit .flow*` → `.advance` → field
updates.  The new token has `pos = s.currentPos`, so its offset
equals `s.offset`.  Offset monotonicity comes from `advance_offset_ge`
applied after the emit. -/

theorem scanFlowSequenceEnd_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (scanFlowSequenceEnd s) := by
  apply LineariseFit_extend s (scanFlowSequenceEnd s)
    (scanFlowSequenceEnd_preserves_ScanInv s h.1)
    (scanFlowSequenceEnd_preserves_pendingKeys s)
    (by have := scanFlowSequenceEnd_adds_one_token s; omega)
    (fun i hi => ScanHelpers.scanFlowSequenceEnd_preserves_prefix s i hi)
    ?new_ge
    ?off_mono
    h
  case new_ge =>
    intro i hi h_ge
    have h_size := scanFlowSequenceEnd_adds_one_token s
    have hi_eq : i = s.tokens.size := by omega
    subst hi_eq
    show s.offset ≤ ((scanFlowSequenceEnd s).tokens[s.tokens.size]'hi).pos.offset
    have h_pos : ((scanFlowSequenceEnd s).tokens[s.tokens.size]'hi).pos = s.currentPos := by
      unfold scanFlowSequenceEnd
      simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq]
    rw [h_pos]
    simp [ScannerState.currentPos]
  case off_mono =>
    have := ScannerProgress.advance_offset_ge (s.emit .flowSequenceEnd)
    rw [ScannerProgress.emit_offset] at this
    show s.offset ≤ (scanFlowSequenceEnd s).offset
    unfold scanFlowSequenceEnd
    simp only []
    exact this

theorem scanFlowSequenceStart_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (scanFlowSequenceStart s) := by
  apply LineariseFit_extend s (scanFlowSequenceStart s)
    (scanFlowSequenceStart_preserves_ScanInv s h.1)
    (scanFlowSequenceStart_preserves_pendingKeys s)
    (by have := scanFlowSequenceStart_adds_one_token s; omega)
    (fun i hi => ScanHelpers.scanFlowSequenceStart_preserves_prefix s i hi)
    ?new_ge
    ?off_mono
    h
  case new_ge =>
    intro i hi h_ge
    have h_size := scanFlowSequenceStart_adds_one_token s
    have hi_eq : i = s.tokens.size := by omega
    subst hi_eq
    show s.offset ≤ ((scanFlowSequenceStart s).tokens[s.tokens.size]'hi).pos.offset
    unfold scanFlowSequenceStart
    simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq,
               ScannerState.currentPos]
    omega
  case off_mono =>
    have := ScannerProgress.advance_offset_ge
      ({ s with simpleKey := { possible := false }, pendingKeyActive := none }.emit .flowSequenceStart)
    rw [ScannerProgress.emit_offset] at this
    show s.offset ≤ (scanFlowSequenceStart s).offset
    unfold scanFlowSequenceStart
    simp only []
    exact this

theorem scanFlowMappingEnd_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (scanFlowMappingEnd s) := by
  apply LineariseFit_extend s (scanFlowMappingEnd s)
    (scanFlowMappingEnd_preserves_ScanInv s h.1)
    (scanFlowMappingEnd_preserves_pendingKeys s)
    (by have := scanFlowMappingEnd_adds_one_token s; omega)
    (fun i hi => ScanHelpers.scanFlowMappingEnd_preserves_prefix s i hi)
    ?new_ge
    ?off_mono
    h
  case new_ge =>
    intro i hi h_ge
    have h_size := scanFlowMappingEnd_adds_one_token s
    have hi_eq : i = s.tokens.size := by omega
    subst hi_eq
    show s.offset ≤ ((scanFlowMappingEnd s).tokens[s.tokens.size]'hi).pos.offset
    have h_pos : ((scanFlowMappingEnd s).tokens[s.tokens.size]'hi).pos = s.currentPos := by
      unfold scanFlowMappingEnd
      simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq]
    rw [h_pos]
    simp [ScannerState.currentPos]
  case off_mono =>
    have := ScannerProgress.advance_offset_ge (s.emit .flowMappingEnd)
    rw [ScannerProgress.emit_offset] at this
    show s.offset ≤ (scanFlowMappingEnd s).offset
    unfold scanFlowMappingEnd
    simp only []
    exact this

theorem scanFlowMappingStart_preserves_LineariseFit (s : ScannerState)
    (h : LineariseFit s) : LineariseFit (scanFlowMappingStart s) := by
  apply LineariseFit_extend s (scanFlowMappingStart s)
    (scanFlowMappingStart_preserves_ScanInv s h.1)
    (scanFlowMappingStart_preserves_pendingKeys s)
    (by have := scanFlowMappingStart_adds_one_token s; omega)
    (fun i hi => ScanHelpers.scanFlowMappingStart_preserves_prefix s i hi)
    ?new_ge
    ?off_mono
    h
  case new_ge =>
    intro i hi h_ge
    have h_size := scanFlowMappingStart_adds_one_token s
    have hi_eq : i = s.tokens.size := by omega
    subst hi_eq
    show s.offset ≤ ((scanFlowMappingStart s).tokens[s.tokens.size]'hi).pos.offset
    unfold scanFlowMappingStart
    simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq,
               ScannerState.currentPos]
    omega
  case off_mono =>
    have := ScannerProgress.advance_offset_ge
      ({ s with simpleKey := { possible := false }, pendingKeyActive := none }.emit .flowMappingStart)
    rw [ScannerProgress.emit_offset] at this
    show s.offset ≤ (scanFlowMappingStart s).offset
    unfold scanFlowMappingStart
    simp only []
    exact this

theorem scanFlowEntry_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanFlowEntry s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new s s'
    (scanFlowEntry_preserves_ScanInv s h.1 s' h_eq)
    (scanFlowEntry_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanFlowEntry_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanFlowEntry_preserves_prefix s s' h_eq i hi)
    ?first_new
    ?off_mono
    h
  case first_new =>
    intro h_lt
    -- The first new token comes from `s.emit .flowEntry` at currentPos.
    show s.offset ≤ (s'.tokens[s.tokens.size]'h_lt).pos.offset
    unfold scanFlowEntry at h_eq
    simp only [bind, Except.bind, pure, Except.pure] at h_eq
    split at h_eq
    · split at h_eq
      · simp at h_eq
      · simp only [Except.ok.injEq] at h_eq; subst h_eq
        simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq,
                   ScannerState.currentPos]
        omega
    · simp only [Except.ok.injEq] at h_eq; subst h_eq
      simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq,
                 ScannerState.currentPos]
      omega
  case off_mono =>
    -- After successful scanFlowEntry: offset increases by emit (no-op) + advance.
    show s.offset ≤ s'.offset
    unfold scanFlowEntry at h_eq
    simp only [bind, Except.bind, pure, Except.pure] at h_eq
    split at h_eq
    · split at h_eq
      · simp at h_eq
      · simp only [Except.ok.injEq] at h_eq; subst h_eq
        have := ScannerProgress.advance_offset_ge (s.emit .flowEntry)
        rw [ScannerProgress.emit_offset] at this
        simp only []
        exact this
    · simp only [Except.ok.injEq] at h_eq; subst h_eq
      have := ScannerProgress.advance_offset_ge (s.emit .flowEntry)
      rw [ScannerProgress.emit_offset] at this
      simp only []
      exact this

/-! ##### `scanBlockEntry` and `scanKey` (push*Indent + emit + advance)

These ops may add 1 or 2 tokens (pushSequenceIndent/pushMappingIndent
optionally emits .blockSequenceStart/.blockMappingStart at currentPos;
the main op then emits .blockEntry/.key at currentPos).  In both cases,
the FIRST new token is at `s.currentPos` with offset = s.offset, so
`LineariseFit_via_first_new` discharges. -/

/-- After `(pushSequenceIndent s col).emit tok`, the token at `s.tokens.size`
    has `pos.offset = s.offset` (whether or not pushSequenceIndent fired). -/
theorem pushSequenceIndent_emit_first_new_offset (s : ScannerState) (col : Int)
    (tok : YamlToken)
    (h_lt : s.tokens.size <
      ((pushSequenceIndent s col).emit tok).tokens.size) :
    (((pushSequenceIndent s col).emit tok).tokens[s.tokens.size]'h_lt).pos.offset
      = s.offset := by
  by_cases hfire : col > s.currentIndent
  · -- pushSequenceIndent fires: first new token is .blockSequenceStart at s.currentPos
    have h_psi : pushSequenceIndent s col =
        { s.emit .blockSequenceStart with
            indents := (s.emit .blockSequenceStart).indents.push
              { column := col, isSequence := true } } := by
      unfold pushSequenceIndent
      split
      · rfl
      · contradiction
    have h_inner_lt : s.tokens.size <
        (s.tokens.push ⟨s.currentPos, .blockSequenceStart, s.currentPos⟩).size := by
      rw [Array.size_push]; omega
    have h_target :
        (((pushSequenceIndent s col).emit tok).tokens[s.tokens.size]'h_lt) =
        ⟨s.currentPos, .blockSequenceStart, s.currentPos⟩ := by
      simp only [h_psi]
      simp only [ScannerState.emit, Array.getElem_push_lt h_inner_lt, Array.getElem_push_eq]
    rw [h_target]
    rfl
  · -- pushSequenceIndent doesn't fire: tokens = s.tokens.push (tok at s.currentPos)
    have h_psi : pushSequenceIndent s col = s := by
      unfold pushSequenceIndent
      split
      · contradiction
      · rfl
    have h_target :
        (((pushSequenceIndent s col).emit tok).tokens[s.tokens.size]'h_lt) =
        ⟨s.currentPos, tok, s.currentPos⟩ := by
      simp only [h_psi]
      simp only [ScannerState.emit, Array.getElem_push_eq]
    rw [h_target]
    rfl

/-- After `(pushMappingIndent s col).emit tok`, the token at `s.tokens.size`
    has `pos.offset = s.offset` (whether or not pushMappingIndent fired). -/
theorem pushMappingIndent_emit_first_new_offset (s : ScannerState) (col : Int)
    (tok : YamlToken)
    (h_lt : s.tokens.size <
      ((pushMappingIndent s col).emit tok).tokens.size) :
    (((pushMappingIndent s col).emit tok).tokens[s.tokens.size]'h_lt).pos.offset
      = s.offset := by
  by_cases hfire : col > s.currentIndent
  · have h_pmi : pushMappingIndent s col =
        { s.emit .blockMappingStart with
            indents := (s.emit .blockMappingStart).indents.push
              { column := col, isSequence := false } } := by
      unfold pushMappingIndent
      split
      · rfl
      · contradiction
    have h_inner_lt : s.tokens.size <
        (s.tokens.push ⟨s.currentPos, .blockMappingStart, s.currentPos⟩).size := by
      rw [Array.size_push]; omega
    have h_target :
        (((pushMappingIndent s col).emit tok).tokens[s.tokens.size]'h_lt) =
        ⟨s.currentPos, .blockMappingStart, s.currentPos⟩ := by
      simp only [h_pmi]
      simp only [ScannerState.emit, Array.getElem_push_lt h_inner_lt, Array.getElem_push_eq]
    rw [h_target]
    rfl
  · have h_pmi : pushMappingIndent s col = s := by
      unfold pushMappingIndent
      split
      · contradiction
      · rfl
    have h_target :
        (((pushMappingIndent s col).emit tok).tokens[s.tokens.size]'h_lt) =
        ⟨s.currentPos, tok, s.currentPos⟩ := by
      simp only [h_pmi]
      simp only [ScannerState.emit, Array.getElem_push_eq]
    rw [h_target]
    rfl

theorem scanBlockEntry_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanBlockEntry s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new s s'
    (scanBlockEntry_preserves_ScanInv s s' h.1 h_eq)
    (scanBlockEntry_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanBlockEntry_adds_tokens s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanBlockEntry_preserves_prefix s s' h_eq i hi)
    ?first_new
    ?off_mono
    h
  case first_new =>
    intro h_lt
    show s.offset ≤ (s'.tokens[s.tokens.size]'h_lt).pos.offset
    unfold scanBlockEntry at h_eq
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_eq
    repeat (any_goals (split at h_eq))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at h_eq; subst h_eq)
    all_goals first
      | (dsimp only []
         simp only [advance_preserves_tokens]
         rw [pushSequenceIndent_emit_first_new_offset s s.col .blockEntry]
         omega)
      | (dsimp only []
         simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq,
                    ScannerState.currentPos]
         omega)
  case off_mono =>
    show s.offset ≤ s'.offset
    unfold scanBlockEntry at h_eq
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_eq
    repeat (any_goals (split at h_eq))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at h_eq; subst h_eq)
    all_goals first
      | (dsimp only []
         have h_pi := ScannerProgress.pushSequenceIndent_offset s s.col
         have := ScannerProgress.advance_offset_ge ((pushSequenceIndent s s.col).emit .blockEntry)
         rw [ScannerProgress.emit_offset, h_pi] at this
         exact this)
      | (dsimp only []
         have := ScannerProgress.advance_offset_ge (s.emit .blockEntry)
         rw [ScannerProgress.emit_offset] at this
         exact this)

theorem scanKey_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanKey s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new s s'
    (scanKey_preserves_ScanInv s s' h.1 h_eq)
    (scanKey_preserves_pendingKeys s s' h_eq)
    (by have := scanKey_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanKey_preserves_prefix s s' h_eq i hi)
    ?first_new
    ?off_mono
    h
  case first_new =>
    intro h_lt
    show s.offset ≤ (s'.tokens[s.tokens.size]'h_lt).pos.offset
    unfold scanKey at h_eq
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_eq
    repeat (any_goals (split at h_eq))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at h_eq; subst h_eq)
    all_goals first
      | (dsimp only []
         simp only [advance_preserves_tokens]
         rw [pushMappingIndent_emit_first_new_offset s s.col .key]
         omega)
      | (dsimp only []
         simp only [advance_preserves_tokens, ScannerState.emit, Array.getElem_push_eq,
                    ScannerState.currentPos]
         omega)
  case off_mono =>
    show s.offset ≤ s'.offset
    unfold scanKey at h_eq
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_eq
    repeat (any_goals (split at h_eq))
    all_goals (try contradiction)
    all_goals (simp only [Except.ok.injEq] at h_eq; subst h_eq)
    all_goals first
      | (dsimp only []
         have h_pi := ScannerProgress.pushMappingIndent_offset s s.col
         have := ScannerProgress.advance_offset_ge ((pushMappingIndent s s.col).emit .key)
         rw [ScannerProgress.emit_offset, h_pi] at this
         exact this)
      | (dsimp only []
         have := ScannerProgress.advance_offset_ge (s.emit .key)
         rw [ScannerProgress.emit_offset] at this
         exact this)

/-! ##### Tag/anchor/alias `emitAt`-class leaves

These ops run a sequence of `advance`s through `collect…Loop`, then
`emitAt startPos token` where `startPos = s.currentPos`.  The first
new token's `pos` equals the saved start position, so `pos.offset = s.offset`. -/

/-- The first new token's `pos` after `scanAnchorOrAlias` is `s.currentPos`. -/
private theorem scanAnchorOrAlias_first_new_pos (s : ScannerState) (isAnchor : Bool)
    (s' : ScannerState) (hok : scanAnchorOrAlias s isAnchor = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold scanAnchorOrAlias at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · have h := Except.ok.inj hok; subst h; dsimp only []
    apply first_new_pos_emitAt
    rw [ScanHelpers.collectAnchorNameLoop_preserves_tokens, advance_preserves_tokens]

theorem scanAnchorOrAlias_preserves_LineariseFit (s s' : ScannerState) (isAnchor : Bool)
    (h_eq : scanAnchorOrAlias s isAnchor = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new_strict s s'
    (scanAnchorOrAlias_preserves_ScanInv s isAnchor h.1 s' h_eq)
    (scanAnchorOrAlias_preserves_pendingKeys s isAnchor s' h_eq)
    (by have := ScanHelpers.scanAnchorOrAlias_adds_one_token s isAnchor s' h_eq; omega)
    (fun i hi => ScanHelpers.scanAnchorOrAlias_preserves_prefix s isAnchor s' h_eq i hi)
    ?first_new
    h
  case first_new =>
    have h_size : s.tokens.size < s'.tokens.size := by
      have := ScanHelpers.scanAnchorOrAlias_adds_one_token s isAnchor s' h_eq; omega
    rw [scanAnchorOrAlias_first_new_pos s isAnchor s' h_eq h_size]
    show s.offset ≤ s.offset
    omega

/-- The first new token's `pos` after `scanVerbatimTag s pos` is `pos`. -/
private theorem scanVerbatimTag_first_new_pos (s : ScannerState) (pos : YamlPos)
    (s' : ScannerState) (hok : scanVerbatimTag s pos = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = pos := by
  unfold scanVerbatimTag at hok; dsimp only [] at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · have h := Except.ok.inj hok; subst h
      apply first_new_pos_emitAt
      rw [ScanHelpers.collectVerbatimTagLoop_preserves_tokens, advance_preserves_tokens]

/-- The first new token's `pos` after `scanSecondaryTag s pos` is `pos`. -/
private theorem scanSecondaryTag_first_new_pos (s : ScannerState) (pos : YamlPos)
    (h_lt : s.tokens.size < (scanSecondaryTag s pos).tokens.size) :
    ((scanSecondaryTag s pos).tokens[s.tokens.size]'h_lt).pos = pos := by
  unfold scanSecondaryTag
  apply first_new_pos_emitAt
  rw [ScanHelpers.collectTagSuffixLoop_preserves_tokens, advance_preserves_tokens]

/-- The first new token's `pos` after `scanNamedTag s pos inputEnd` is `pos`. -/
private theorem scanNamedTag_first_new_pos (s : ScannerState) (pos : YamlPos) (inputEnd : Nat)
    (h_lt : s.tokens.size < (scanNamedTag s pos inputEnd).tokens.size) :
    ((scanNamedTag s pos inputEnd).tokens[s.tokens.size]'h_lt).pos = pos := by
  unfold scanNamedTag; simp only []
  have h_handle := ScanHelpers.collectTagHandleLoop_preserves_tokens s "" (inputEnd - s.offset)
  split
  · apply first_new_pos_emitAt
    rw [ScanHelpers.collectTagSuffixLoop_preserves_tokens, h_handle]
  · apply first_new_pos_emitAt
    rw [h_handle]

/-- The first new token's `pos` after `scanTag` is `s.currentPos`. -/
private theorem scanTag_first_new_pos (s : ScannerState)
    (s' : ScannerState) (hok : scanTag s = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold scanTag at hok; dsimp only [] at hok
  have h_adv := advance_preserves_tokens s
  split at hok
  · -- verbatim
    simp only [bind, Except.bind] at hok
    generalize hv : scanVerbatimTag s.advance s.currentPos = result at hok
    cases result with
    | error e => simp at hok
    | ok s_verb =>
      dsimp only [] at hok
      have h := Except.ok.inj hok; subst h; dsimp only [] at h_lt ⊢
      have h_lt' : s.advance.tokens.size < s_verb.tokens.size := by
        rw [h_adv]; exact h_lt
      have := scanVerbatimTag_first_new_pos s.advance s.currentPos s_verb hv h_lt'
      simp_all
  · have h := Except.ok.inj hok; subst h; dsimp only [] at h_lt ⊢
    have h_lt' : s.advance.tokens.size < (scanSecondaryTag s.advance s.currentPos).tokens.size := by
      rw [h_adv]; exact h_lt
    have := scanSecondaryTag_first_new_pos s.advance s.currentPos h_lt'
    simp_all
  · have h := Except.ok.inj hok; subst h; dsimp only [] at h_lt ⊢
    have h_lt' : s.advance.tokens.size <
        (scanNamedTag s.advance s.currentPos s.inputEnd).tokens.size := by
      rw [h_adv]; exact h_lt
    have := scanNamedTag_first_new_pos s.advance s.currentPos s.inputEnd h_lt'
    simp_all

theorem scanTag_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanTag s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new_strict s s'
    (scanTag_preserves_ScanInv s h.1 s' h_eq)
    (scanTag_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanTag_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanTag_preserves_prefix s s' h_eq i hi)
    ?first_new
    h
  case first_new =>
    have h_size : s.tokens.size < s'.tokens.size := by
      have := ScanHelpers.scanTag_adds_one_token s s' h_eq; omega
    rw [scanTag_first_new_pos s s' h_eq h_size]
    show s.offset ≤ s.offset
    omega

/-! ##### Scalar `emitAt`-class leaves -/

/-- The first new token's `pos` after `scanDoubleQuoted` is `s.currentPos`. -/
private theorem scanDoubleQuoted_first_new_pos (s : ScannerState)
    (s' : ScannerState) (hok : scanDoubleQuoted s = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold scanDoubleQuoted at hok; simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  rename_i heq
  have h_collect := ScanHelpers.collectDoubleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at hok
  · split at hok <;> try contradiction
    injection hok with h_eq; subst h_eq; dsimp only []
    apply first_new_pos_emitAt; rw [h_collect, h_adv]
  · injection hok with h_eq; subst h_eq; dsimp only []
    apply first_new_pos_emitAt; rw [h_collect, h_adv]

theorem scanDoubleQuoted_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanDoubleQuoted s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new_strict s s'
    (scanDoubleQuoted_preserves_ScanInv s s' h.1 h_eq)
    (scanDoubleQuoted_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanDoubleQuoted_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanDoubleQuoted_preserves_prefix s s' h_eq i hi)
    ?first_new
    h
  case first_new =>
    have h_size : s.tokens.size < s'.tokens.size := by
      have := ScanHelpers.scanDoubleQuoted_adds_one_token s s' h_eq; omega
    rw [scanDoubleQuoted_first_new_pos s s' h_eq h_size]
    show s.offset ≤ s.offset
    omega

/-- The first new token's `pos` after `scanSingleQuoted` is `s.currentPos`. -/
private theorem scanSingleQuoted_first_new_pos (s : ScannerState)
    (s' : ScannerState) (hok : scanSingleQuoted s = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold scanSingleQuoted at hok; simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  rename_i heq
  have h_collect := ScanHelpers.collectSingleQuotedLoop_preserves_tokens s.advance "" _ _ _ _ _ _ heq
  have h_adv := advance_preserves_tokens s
  split at hok
  · split at hok <;> try contradiction
    injection hok with h_eq; subst h_eq; dsimp only []
    apply first_new_pos_emitAt; rw [h_collect, h_adv]
  · injection hok with h_eq; subst h_eq; dsimp only []
    apply first_new_pos_emitAt; rw [h_collect, h_adv]

theorem scanSingleQuoted_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanSingleQuoted s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new_strict s s'
    (scanSingleQuoted_preserves_ScanInv s s' h.1 h_eq)
    (scanSingleQuoted_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanSingleQuoted_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanSingleQuoted_preserves_prefix s s' h_eq i hi)
    ?first_new
    h
  case first_new =>
    have h_size : s.tokens.size < s'.tokens.size := by
      have := ScanHelpers.scanSingleQuoted_adds_one_token s s' h_eq; omega
    rw [scanSingleQuoted_first_new_pos s s' h_eq h_size]
    show s.offset ≤ s.offset
    omega

/-- The first new token's `pos` after `scanPlainScalar` is `s.currentPos`. -/
private theorem scanPlainScalar_first_new_pos (s : ScannerState)
    (s' : ScannerState) (hok : scanPlainScalar s = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold scanPlainScalar at hok; simp only [bind, Except.bind] at hok
  split at hok <;> try contradiction
  rename_i heq
  have h_collect := ScanHelpers.collectPlainScalarLoop_preserves_tokens s "" "" _ _ _ _ _ heq
  injection hok with h_eq; subst h_eq; dsimp only []
  apply first_new_pos_emitAt; rw [h_collect]

theorem scanPlainScalar_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanPlainScalar s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new_strict s s'
    (scanPlainScalar_preserves_ScanInv s s' h.1 h_eq)
    (scanPlainScalar_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanPlainScalar_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanPlainScalar_preserves_prefix s s' h_eq i hi)
    ?first_new
    h
  case first_new =>
    have h_size : s.tokens.size < s'.tokens.size := by
      have := ScanHelpers.scanPlainScalar_adds_one_token s s' h_eq; omega
    rw [scanPlainScalar_first_new_pos s s' h_eq h_size]
    show s.offset ≤ s.offset
    omega

/-- The first new token's `pos` after `scanBlockScalarBody` is `startPos`
    (provided the loop's preserves-tokens chain holds). -/
private theorem scanBlockScalarBody_first_new_pos (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState) (h_tok : s_nl.tokens = s_orig.tokens)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s')
    (h_lt : s_orig.tokens.size < s'.tokens.size) :
    (s'.tokens[s_orig.tokens.size]'h_lt).pos = startPos := by
  unfold scanBlockScalarBody at h
  simp only [] at h
  repeat (any_goals (split at h))
  all_goals (try contradiction)
  all_goals (simp only [Except.ok.injEq] at h; subst h; dsimp only [])
  all_goals
    (apply first_new_pos_emitAt
     rw [ScanHelpers.collectBlockScalarLoop_preserves_tokens, h_tok])

/-- The first new token's `pos` after `scanBlockScalar` is `s.currentPos`. -/
private theorem scanBlockScalar_first_new_pos (s : ScannerState)
    (s' : ScannerState) (hok : scanBlockScalar s = .ok s')
    (h_lt : s.tokens.size < s'.tokens.size) :
    (s'.tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold scanBlockScalar at hok
  simp only [] at hok
  split at hok
  · contradiction
  · exact scanBlockScalarBody_first_new_pos s _ _ _ _ _ s'
      (by rw [ScanHelpers.scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
              ScanHelpers.scanBlockScalarSkipComment_preserves_tokens,
              skipWhitespace_preserves_tokens,
              ScanHelpers.parseBlockHeaderLoop_preserves_tokens,
              advance_preserves_tokens]) hok h_lt

theorem scanBlockScalar_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : scanBlockScalar s = .ok s') (h : LineariseFit s) : LineariseFit s' := by
  apply LineariseFit_via_first_new_strict s s'
    (scanBlockScalar_preserves_ScanInv s s' h.1 h_eq)
    (scanBlockScalar_preserves_pendingKeys s s' h_eq)
    (by have := ScanHelpers.scanBlockScalar_adds_one_token s s' h_eq; omega)
    (fun i hi => ScanHelpers.scanBlockScalar_preserves_prefix s s' h_eq i hi)
    ?first_new
    h
  case first_new =>
    have h_size : s.tokens.size < s'.tokens.size := by
      have := ScanHelpers.scanBlockScalar_adds_one_token s s' h_eq; omega
    rw [scanBlockScalar_first_new_pos s s' h_eq h_size]
    show s.offset ≤ s.offset
    omega

/-! ##### `pushSequenceIndent` / `pushMappingIndent` standalone leaves

These ops fire at most once: when `col > s.currentIndent` they emit
`.blockSequenceStart` / `.blockMappingStart` at `s.currentPos` and push
an indent level; otherwise they're identity.  Tokens monotonic, pending
keys preserved, offset preserved. -/

theorem pushSequenceIndent_preserves_LineariseFit (s : ScannerState) (col : Int)
    (h : LineariseFit s) : LineariseFit (pushSequenceIndent s col) := by
  apply LineariseFit_via_first_new s (pushSequenceIndent s col)
    (pushSequenceIndent_preserves_ScanInv s col h.1)
    (pushSequenceIndent_preserves_pendingKeys s col)
    (pushSequenceIndent_tokens_monotonic s col)
    (fun i hi => ScanHelpers.pushSequenceIndent_preserves_prefix s col i hi)
    ?first_new
    ?off_mono
    h
  case first_new =>
    intro h_lt
    by_cases hfire : col > s.currentIndent
    · have h_psi : pushSequenceIndent s col =
          { s.emit .blockSequenceStart with
              indents := (s.emit .blockSequenceStart).indents.push
                { column := col, isSequence := true } } := by
        unfold pushSequenceIndent; split
        · rfl
        · contradiction
      show s.offset ≤ ((pushSequenceIndent s col).tokens[s.tokens.size]'h_lt).pos.offset
      simp only [h_psi, ScannerState.emit, Array.getElem_push_eq, ScannerState.currentPos]
      omega
    · -- doesn't fire: pushSequenceIndent s col = s, so h_lt is vacuous
      have h_psi : pushSequenceIndent s col = s := by
        unfold pushSequenceIndent; split
        · contradiction
        · rfl
      rw [h_psi] at h_lt; omega
  case off_mono =>
    show s.offset ≤ (pushSequenceIndent s col).offset
    rw [ScannerProgress.pushSequenceIndent_offset]
    omega

theorem pushMappingIndent_preserves_LineariseFit (s : ScannerState) (col : Int)
    (h : LineariseFit s) : LineariseFit (pushMappingIndent s col) := by
  apply LineariseFit_via_first_new s (pushMappingIndent s col)
    (pushMappingIndent_preserves_ScanInv s col h.1)
    (pushMappingIndent_preserves_pendingKeys s col)
    (pushMappingIndent_tokens_monotonic s col)
    (fun i hi => ScanHelpers.pushMappingIndent_preserves_prefix s col i hi)
    ?first_new
    ?off_mono
    h
  case first_new =>
    intro h_lt
    by_cases hfire : col > s.currentIndent
    · have h_pmi : pushMappingIndent s col =
          { s.emit .blockMappingStart with
              indents := (s.emit .blockMappingStart).indents.push
                { column := col, isSequence := false } } := by
        unfold pushMappingIndent; split
        · rfl
        · contradiction
      show s.offset ≤ ((pushMappingIndent s col).tokens[s.tokens.size]'h_lt).pos.offset
      simp only [h_pmi, ScannerState.emit, Array.getElem_push_eq, ScannerState.currentPos]
      omega
    · have h_pmi : pushMappingIndent s col = s := by
        unfold pushMappingIndent; split
        · contradiction
        · rfl
      rw [h_pmi] at h_lt; omega
  case off_mono =>
    show s.offset ≤ (pushMappingIndent s col).offset
    rw [ScannerProgress.pushMappingIndent_offset]
    omega

/-!
### scanNextToken preserves ScanInv

The proof composes all per-dispatcher preservation theorems.
The `SimpleKeyValid` condition is carried as a side invariant to
supply the `h_sk` precondition needed by `scanValue_preserves_ScanInv`.
-/

-- Helper: after structural dispatch returns none, the remaining dispatchers preserve ScanInv.
theorem scanNextToken_postStructural_preserves_ScanInv
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h_inv : ScanInv s) (h_skv : SimpleKeyValid s)
    (h_ok : (match scanNextToken_dispatchFlowIndicators s c with
      | Except.ok (some s') => Except.ok (some s')
      | Except.ok none =>
        match scanNextToken_dispatchBlockIndicators s c with
        | Except.ok (some s') => Except.ok (some s')
        | Except.ok none => (scanNextToken_dispatchContent s c).map some
        | Except.error e => Except.error e
      | Except.error e => Except.error e) = Except.ok (some s')) :
    ScanInv s' := by
  split at h_ok
  · -- flow = .ok (some _)
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchFlowIndicators_preserves_ScanInv s c h_inv _ (by assumption)
  · -- flow = .ok none → try block
    split at h_ok
    · -- block = .ok (some _)
      simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchBlockIndicators_preserves_ScanInv s c h_inv
        (SimpleKeyValid_implies_scanValue_h_sk s h_skv) _ (by assumption)
    · -- block = .ok none → try content
      unfold Except.map at h_ok
      split at h_ok
      · simp at h_ok  -- content = .error
      · -- content = .ok v✝
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_ScanInv s c h_inv _ (by assumption)
    · -- block = .error
      simp at h_ok
  · -- flow = .error
    simp at h_ok

theorem scanNextToken_preserves_ScanInv :
    ∀ (s s' : ScannerState),
      ScanInv s → SimpleKeyValid s → scanNextToken s = .ok (some s') → ScanInv s' := by
  intro s s' h_inv h_skv h_ok
  unfold scanNextToken at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> (try (simp at h_ok; done)) -- preprocess Except
  split at h_ok <;> (try (simp at h_ok; done)) -- preprocess Option
  rename_i s2 c h_pre
  have h_inv2 := preprocess_preserves_ScanInv s s2 c h_inv h_pre
  have h_skv2 := preprocess_preserves_SimpleKeyValid s s2 c h_pre h_skv
  split at h_ok <;> (try (simp at h_ok; done)) -- structural Except
  split at h_ok
  · -- structural some (source order: some first)
    simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
    exact dispatchStructural_preserves_ScanInv s2 c h_inv2 _ (by assumption)
  · -- structural none → continue to flow/block/content
    have h_inv3 := allowDir_ite_preserves_ScanInv s2 h_inv2
    have h_skv3 := allowDir_ite_preserves_SimpleKeyValid s2 h_skv2
    -- Block→flow underindent check
    split at h_ok <;> (try (simp at h_ok; done))
    -- Flow Except split
    split at h_ok <;> (try (simp at h_ok; done))
    -- Flow Option split (source order: some first)
    split at h_ok
    · -- flow some
      simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
      exact dispatchFlowIndicators_preserves_ScanInv _ c h_inv3 _ (by assumption)
    · -- flow none → block
      split at h_ok <;> (try (simp at h_ok; done)) -- block Except
      split at h_ok
      · -- block some
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchBlockIndicators_preserves_ScanInv _ c h_inv3
          (SimpleKeyValid_implies_scanValue_h_sk _ h_skv3) _ (by assumption)
      · -- block none → content
        split at h_ok <;> (try (simp at h_ok; done)) -- content Except
        simp only [Except.ok.injEq, Option.some.injEq] at h_ok; subst h_ok
        exact dispatchContent_preserves_ScanInv _ c h_inv3 _ (by assumption)

-- scanLoop preserves ordering via induction on fuel.
theorem scanLoop_ordered (s : ScannerState) (fuel : Nat)
    (tokens : Array (Positioned YamlToken))
    (h_inv : ScanInv s) (h_akv : AllKeysValid s) (h_ok : scanLoop s fuel = .ok tokens) :
    ∀ i j : Fin tokens.size, i.val < j.val →
      tokens[i].pos.offset ≤ tokens[j].pos.offset := by
  induction fuel generalizing s with
  | zero =>
    -- fuel = 0: scanLoop returns error, contradicts h_ok
    simp [scanLoop] at h_ok
  | succ fuel' ih =>
    -- fuel = n+1: unfold and match on scanNextToken
    simp only [scanLoop] at h_ok
    split at h_ok
    · next _ h_snt => -- scanNextToken s = .error e: contradiction
      simp at h_ok
    · next h_snt => -- scanNextToken s = .ok none: final state
      split at h_ok
      · simp at h_ok
      · split at h_ok
        · simp at h_ok
        · -- tokens = (unwindIndents s (-1)).emit(.streamEnd).tokens
          injection h_ok with h_eq
          rw [← h_eq]
          exact (emit_preserves_ScanInv _ .streamEnd
            (unwindIndents_preserves_ScanInv s (-1) h_inv)).1
    · next s' h_snt => -- scanNextToken s = .ok (some s'): recursive case
      exact ih s'
        (scanNextToken_preserves_ScanInv s s' h_inv h_akv.1 h_snt)
        (scanNextToken_preserves_AllKeysValid s s' h_akv h_snt)
        h_ok

theorem scan_positions_ordered (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    ∀ (i j : Fin tokens.size), i.val < j.val →
      (tokens[i]).pos.offset ≤ (tokens[j]).pos.offset := by
  -- Unfold scan to expose structure: mk' → emit streamStart → BOM → scanLoop
  unfold scan at h
  -- Initial state after emit streamStart satisfies ScanInv
  have h_inv0 : ScanInv ((ScannerState.mk' input).emit .streamStart) := by
    have h_sz : ((ScannerState.mk' input).emit .streamStart).tokens.size = 1 := by
      rw [emit_tokens_size, mk'_tokens_empty]; simp
    constructor
    · intro ⟨i, hi⟩ ⟨j, hj⟩ hij
      rw [h_sz] at hi hj; omega
    · intro ⟨i, hi⟩
      rw [h_sz] at hi
      have h_i0 : i = 0 := by omega
      subst h_i0
      simp [ScannerState.emit, ScannerState.mk', ScannerState.currentPos]
  -- BOM handling preserves ScanInv
  have h_inv : ScanInv (match (ScannerState.mk' input).emit .streamStart |>.peek? with
      | some '\uFEFF' => ((ScannerState.mk' input).emit .streamStart).advance
      | _ => (ScannerState.mk' input).emit .streamStart) := by
    split
    · exact advance_preserves_ScanInv _ h_inv0
    · exact h_inv0
  -- Initial AllKeysValid: simpleKey.possible = false, stack empty.
  have h_akv0 : AllKeysValid ((ScannerState.mk' input).emit .streamStart) := by
    constructor
    · intro h_poss; simp [ScannerState.mk', ScannerState.emit] at h_poss
    · intro j hj; simp [ScannerState.mk', ScannerState.emit] at hj
  have h_akv : AllKeysValid (match (ScannerState.mk' input).emit .streamStart |>.peek? with
      | some '\uFEFF' => ((ScannerState.mk' input).emit .streamStart).advance
      | _ => (ScannerState.mk' input).emit .streamStart) := by
    split
    · have h_tok := advance_preserves_tokens ((ScannerState.mk' input).emit .streamStart)
      exact AllKeysValid_mono _ _ h_akv0
        (advance_preserves_simpleKey _)
        (advance_preserves_simpleKeyStack _)
        (by simp [h_tok])
        (fun i hi => by simp [h_tok])
    · exact h_akv0
  -- Apply scanLoop_ordered with the post-BOM state
  exact scanLoop_ordered _ _ tokens h_inv h_akv h

/-! ## §3  Main Correctness Theorem

Composition of envelope and monotonicity properties establishes that
`scan` produces `ValidTokenStream`s.
-/

/--
**Main result**: The scanner produces valid token streams.

Every successful scan produces a token array that satisfies all four
`ValidTokenStream` invariants:
1. At least 2 tokens (envelope)
2. First token is streamStart
3. Last token is streamEnd
4. Token positions are monotonically non-decreasing

This is a `def` (not `theorem`) because `ValidTokenStream` is a structure (data),
not a proposition. The definition constructs the witness.
-/
def scan_produces_valid_tokens (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) : ValidTokenStream := by
  have h_size : tokens.size ≥ 2 := scan_produces_at_least_two input tokens h
  have h_pos : tokens.size > 0 := by omega
  exact {
    input := input,
    tokens := tokens,
    sizeGe2 := h_size,
    firstIsStreamStart := scan_first_is_streamStart input tokens h h_pos,
    lastIsStreamEnd := scan_last_is_streamEnd input tokens h h_pos,
    positionsOrdered := scan_positions_ordered input tokens h
  }

/-! ### §3.5  `scanFiltered` Lifts `ValidTokenStream`

Filtering out internal `.placeholder` tokens preserves all `ValidTokenStream`
invariants (size, envelope, ordering).  This bridges the scanner's internal
representation to the token stream consumed by `TokenParser`.
-/

/-! #### J.3.2 Bridge: `scanFiltered` ↔ `scan`

Post-cutover `scanFiltered` routes through `scanLoopFull` (returns full
state) rather than `scanLoop` (returns tokens).  The two share their
control flow except for an extra `skipToContent` call in `scanLoopFull`'s
completion branch (collects trailing comments).  Because `skipToContent`
preserves both `tokens` and `flowLevel`, the success/failure of the two
loops coincides, giving us a clean `scanFiltered.ok → scan.ok` bridge. -/

/-! #### J.3.3: `scanLoopFull` token-shape mirrors of the `scanLoop` family

Each lemma here mirrors its `scanLoop_*` analogue.  `scanLoopFull`'s
recursive `.ok (some s')` arm is identical to `scanLoop`'s; the only
divergence is in the `.ok none` completion branch, where `scanLoopFull`
runs an extra `skipToContent` before `unwindIndents`.  Because
`skipToContent` preserves the token array (only updating
offset/line/col/comments), the shape arguments lift unchanged. -/

/-- `scanLoopFull` increases token count by at least 1 (mirror of
    `scanLoop_increases_tokens`). -/
theorem scanLoopFull_increases_tokens (s : ScannerState) (fuel : Nat) (final : ScannerState) :
    scanLoopFull s fuel = .ok final →
    final.tokens.size ≥ s.tokens.size + 1 := by
  intro h
  induction fuel generalizing s with
  | zero => unfold scanLoopFull at h; simp at h
  | succ fuel' IH =>
    unfold scanLoopFull at h
    simp only [] at h
    split at h
    · simp at h
    · -- .ok none: completion
      split at h
      · simp at h  -- flowLevel > 0
      · split at h
        · simp at h  -- directives without document
        · -- normal completion
          injection h with h_eq
          subst h_eq
          -- after skipToContent, tokens preserved (set s_skip via cases on the match)
          cases h_skip : skipToContent s with
          | ok s_skip =>
            show ((unwindIndents s_skip (-1)).emit YamlToken.streamEnd).tokens.size
                  ≥ s.tokens.size + 1
            have h_skip_size : s_skip.tokens.size = s.tokens.size :=
              skipToContent_preserves_tokens s s_skip h_skip ▸ rfl
            have h_unwind := unwindIndents_adds_tokens s_skip (-1)
            have h_emit := emit_tokens_size (unwindIndents s_skip (-1)) .streamEnd
            omega
          | error e =>
            show ((unwindIndents s (-1)).emit YamlToken.streamEnd).tokens.size
                  ≥ s.tokens.size + 1
            have h_unwind := unwindIndents_adds_tokens s (-1)
            have h_emit := emit_tokens_size (unwindIndents s (-1)) .streamEnd
            omega
    · rename_i s' h_snt
      have h_ih := IH s' h
      have h_adds := scanNextToken_adds_tokens s s' h_snt
      omega

/-- `scanLoopFull` preserves an existing token prefix (mirror of
    `scanLoop_preserves_tokens`).  The completion branch's extra
    `skipToContent` preserves tokens (per `skipToContent_preserves_tokens`),
    and `unwindIndents` + `emit .streamEnd` only append. -/
theorem scanLoopFull_preserves_tokens (s : ScannerState) (fuel : Nat) (final : ScannerState)
    (n : Nat) (h_n : n ≤ s.tokens.size) (h_inv : SimpleKeyAbove s n)
    (h : scanLoopFull s fuel = .ok final) :
    ∀ (i : Nat) (h_bound : i < n),
      ∃ (h_bound' : i < final.tokens.size), final.tokens[i] = s.tokens[i]'(by omega) := by
  induction fuel generalizing s final with
  | zero =>
    intro i h_bound
    unfold scanLoopFull at h
    simp at h
  | succ fuel' IH =>
    intro i h_bound
    unfold scanLoopFull at h
    simp only [] at h
    split at h
    · simp at h
    · -- .ok none: completion
      split at h
      · simp at h
      · split at h
        · simp at h
        · injection h with h_eq
          have h_i_lt_s : i < s.tokens.size := by omega
          -- After skipToContent (or error), unwindIndents, emit streamEnd
          cases h_skip : skipToContent s with
          | ok s_skip =>
            have h_skip_tok : s_skip.tokens = s.tokens :=
              skipToContent_preserves_tokens s s_skip h_skip
            have h_i_lt_skip : i < s_skip.tokens.size := by rw [h_skip_tok]; exact h_i_lt_s
            have h_unwind_mono : (unwindIndents s_skip (-1)).tokens.size ≥ s_skip.tokens.size :=
              unwindIndents_adds_tokens s_skip (-1)
            have h_i_lt_unwind : i < (unwindIndents s_skip (-1)).tokens.size := by omega
            have h_emit_size :
                ((unwindIndents s_skip (-1)).emit .streamEnd).tokens.size
                  = (unwindIndents s_skip (-1)).tokens.size + 1 :=
              emit_tokens_size _ _
            have h_i_lt_emit : i < ((unwindIndents s_skip (-1)).emit .streamEnd).tokens.size := by
              rw [h_emit_size]; omega
            rw [h_skip] at h_eq
            simp only [] at h_eq
            subst h_eq
            refine ⟨h_i_lt_emit, ?_⟩
            calc ((unwindIndents s_skip (-1)).emit .streamEnd).tokens[i]
                = (unwindIndents s_skip (-1)).tokens[i]'h_i_lt_unwind :=
                  emit_preserves_tokens_at _ _ i h_i_lt_unwind
              _ = s_skip.tokens[i]'h_i_lt_skip :=
                  unwindIndents_preserves_prefix s_skip (-1) i h_i_lt_skip
              _ = s.tokens[i]'h_i_lt_s := by simp [h_skip_tok]
          | error e =>
            have h_unwind_mono : (unwindIndents s (-1)).tokens.size ≥ s.tokens.size :=
              unwindIndents_adds_tokens s (-1)
            have h_i_lt_unwind : i < (unwindIndents s (-1)).tokens.size := by omega
            have h_emit_size :
                ((unwindIndents s (-1)).emit .streamEnd).tokens.size
                  = (unwindIndents s (-1)).tokens.size + 1 :=
              emit_tokens_size _ _
            have h_i_lt_emit : i < ((unwindIndents s (-1)).emit .streamEnd).tokens.size := by
              rw [h_emit_size]; omega
            rw [h_skip] at h_eq
            simp only [] at h_eq
            subst h_eq
            refine ⟨h_i_lt_emit, ?_⟩
            calc ((unwindIndents s (-1)).emit .streamEnd).tokens[i]
                = (unwindIndents s (-1)).tokens[i]'h_i_lt_unwind :=
                  emit_preserves_tokens_at _ _ i h_i_lt_unwind
              _ = s.tokens[i]'h_i_lt_s :=
                  unwindIndents_preserves_prefix s (-1) i h_i_lt_s
    · -- recursive case: scanNextToken s = .ok (some s')
      rename_i s' h_snt
      have h_s_mono := scanNextToken_adds_tokens s s' h_snt
      have h_n' : n ≤ s'.tokens.size := by omega
      have h_inv' := scanNextToken_maintains_simpleKeyAbove s s' h_snt n h_n h_inv
      have ⟨h_i_lt_final, h_eq_s'⟩ := IH s' final h_n' h_inv' h i h_bound
      have h_prefix := scanNextToken_preserves_prefix s s' h_snt n h_n h_inv i h_bound
      exact ⟨h_i_lt_final, h_eq_s'.trans h_prefix⟩

/-- `scanLoopFull` always emits `.streamEnd` as its final operation
    (mirror of `scanLoop_success_emits_streamEnd`). -/
theorem scanLoopFull_success_emits_streamEnd :
    ∀ (s : ScannerState) (fuel : Nat) (final : ScannerState),
      scanLoopFull s fuel = .ok final →
      ∃ (s' : ScannerState), final = s'.emit .streamEnd := by
  intro s fuel
  induction fuel generalizing s with
  | zero => intro final h; unfold scanLoopFull at h; simp at h
  | succ fuel' IH =>
    intro final h
    unfold scanLoopFull at h
    simp only [] at h
    split at h
    · simp at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · injection h with h_eq
          cases h_skip : skipToContent s with
          | ok s_skip =>
            rw [h_skip] at h_eq
            simp only [] at h_eq
            exact ⟨unwindIndents s_skip (-1), h_eq.symm⟩
          | error e =>
            rw [h_skip] at h_eq
            simp only [] at h_eq
            exact ⟨unwindIndents s (-1), h_eq.symm⟩
    · rename_i s' h_snt
      exact IH s' final h

/-- `scanLoopFull` preserves token offset ordering (mirror of `scanLoop_ordered`).
    `ScanInv` is preserved by every step (including the extra `skipToContent`
    in the completion branch), so the final state's tokens remain ordered. -/
theorem scanLoopFull_ordered (s : ScannerState) (fuel : Nat) (final : ScannerState)
    (h_inv : ScanInv s) (h_akv : AllKeysValid s) (h_ok : scanLoopFull s fuel = .ok final) :
    ∀ i j : Fin final.tokens.size, i.val < j.val →
      final.tokens[i].pos.offset ≤ final.tokens[j].pos.offset := by
  induction fuel generalizing s with
  | zero => simp [scanLoopFull] at h_ok
  | succ fuel' ih =>
    simp only [scanLoopFull] at h_ok
    split at h_ok
    · simp at h_ok
    · split at h_ok
      · simp at h_ok
      · split at h_ok
        · simp at h_ok
        · injection h_ok with h_eq
          cases h_skip : skipToContent s with
          | ok s_skip =>
            rw [h_skip] at h_eq
            simp only [] at h_eq
            subst h_eq
            have h_inv_skip : ScanInv s_skip :=
              skipToContent_preserves_ScanInv s s_skip h_inv h_skip
            exact (emit_preserves_ScanInv _ .streamEnd
              (unwindIndents_preserves_ScanInv s_skip (-1) h_inv_skip)).1
          | error e =>
            rw [h_skip] at h_eq
            simp only [] at h_eq
            subst h_eq
            exact (emit_preserves_ScanInv _ .streamEnd
              (unwindIndents_preserves_ScanInv s (-1) h_inv)).1
    · rename_i s' h_snt
      exact ih s'
        (scanNextToken_preserves_ScanInv s s' h_inv h_akv.1 h_snt)
        (scanNextToken_preserves_AllKeysValid s s' h_akv h_snt)
        h_ok

/-- Both fuel-bounded loops succeed under exactly the same conditions:
    if `scanLoopFull` succeeds, `scanLoop` succeeds too. -/
theorem scanLoopFull_ok_implies_scanLoop_ok :
    ∀ (s : ScannerState) (fuel : Nat) (final : ScannerState),
      scanLoopFull s fuel = .ok final →
      ∃ tokens, scanLoop s fuel = .ok tokens := by
  intro s fuel
  induction fuel generalizing s with
  | zero =>
    intro final h
    simp [scanLoopFull] at h
  | succ fuel' ih =>
    intro final h
    unfold scanLoopFull at h
    simp only [] at h
    cases h_snt : scanNextToken s with
    | error e => rw [h_snt] at h; simp at h
    | ok val =>
      cases val with
      | none =>
        rw [h_snt] at h; simp only [] at h
        by_cases hflow : s.flowLevel > 0
        · simp only [hflow, ↓reduceIte] at h; simp at h
        · simp only [hflow, ↓reduceIte] at h
          by_cases hdir : s.directivesPresent && !s.documentEverStarted
          · simp only [hdir, ↓reduceIte] at h; simp at h
          · simp only [hdir] at h
            -- Both branches in scanLoop also reach the .ok arm.
            unfold scanLoop
            simp only [h_snt, hflow, ↓reduceIte, hdir, ↓reduceIte]
            exact ⟨_, rfl⟩
      | some s' =>
        rw [h_snt] at h; simp only [] at h
        obtain ⟨tokens', h_rec⟩ := ih s' final h
        refine ⟨tokens', ?_⟩
        unfold scanLoop
        simp only [h_snt]
        exact h_rec

/-- **J.3.2 bridge**: `scanFiltered` succeeded ⟹ `scan` succeeded.

    The two share the BOM-handling prefix; their tails differ only in
    that `scanFiltered` calls `scanLoopFull` (returning the full state
    so `linearise` has access to `pendingKeys`) and post-processes via
    `linearise`.  Used by parser-strictness and parse→token-stream
    bridge proofs to relate `scanFiltered.ok` (the actual API the
    parser uses) back to `scan.ok` (the surface used by the legacy
    correctness corpus). -/
theorem scanFiltered_ok_implies_scan_ok (input : String)
    (ftokens : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ftokens) :
    ∃ tokens, scan input = .ok tokens := by
  unfold scanFiltered at h
  simp only [] at h
  split at h
  · -- scanLoopFull s _ = .ok final
    rename_i final h_full
    obtain ⟨tokens, h_loop⟩ := scanLoopFull_ok_implies_scanLoop_ok _ _ final h_full
    refine ⟨tokens, ?_⟩
    unfold scan
    exact h_loop
  · simp at h

/-- `scanFiltered` produces a `ValidTokenStream`.

**Initiative 3 / J.2 step 5 cutover**: pre-cutover this was proven via
`List.filter_sublist` against the unfiltered `scan` output.  Post-cutover
`scanFiltered` routes through `linearise`, so the proof must re-derive
each `ValidTokenStream` field against `linearise`'s shape lemmas
(`linearise_append_token`, `linearise_append_unresolved`, `linearise_resolved`)
which are themselves J.3 deliverables in `Scanner/Linearise.lean`.

J.3 manifest 5.d: `scanFiltered`-shape lemma — Category C. -/
def scanFiltered_produces_valid_tokens (input : String) (ftokens : Array (Positioned YamlToken))
    (h : scanFiltered input = .ok ftokens) : ValidTokenStream := by
  -- J.3 manifest 5.d: scanFiltered now uses linearise; re-derive against
  -- linearise's shape lemmas (currently sorry'd in Scanner/Linearise.lean).
  sorry

/-! ## §4  Compile-Time Verification

`#guard` checks demonstrating the theorem on concrete inputs.
These provide empirical validation before the universal proof.
-/

/-! ### §4.1  ValidTokenStreamProp Bridge Theorems

`ValidTokenStreamProp` is the `Prop` twin of `ValidTokenStream`.
These theorems make scanner correctness visible to the doc-verification-bridge,
which classifies `def`-as-witness patterns as `computationalOperation`
rather than theorems.
-/

/--
**Prop-level scanner correctness**: `scan` produces tokens satisfying all
four `ValidTokenStreamProp` invariants.
-/
theorem scan_valid_token_stream (input : String) (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) : ValidTokenStreamProp tokens :=
  let vts := scan_produces_valid_tokens input tokens h
  ⟨vts.sizeGe2, fun _ => vts.firstIsStreamStart, fun _ => vts.lastIsStreamEnd, vts.positionsOrdered⟩

/--
**Projection**: `ValidTokenStream` fields imply `ValidTokenStreamProp`.
-/
theorem ValidTokenStream_iff_Prop (vts : ValidTokenStream) :
    ValidTokenStreamProp vts.tokens :=
  ⟨vts.sizeGe2, fun _ => vts.firstIsStreamStart, fun _ => vts.lastIsStreamEnd, vts.positionsOrdered⟩

/-! ### §5  Scanner Progress — `scanNextToken` Advances Offset

**Goal**: Prove that every successful `scanNextToken` call that returns
`some s'` has `s'.offset > s.offset`. This is the key termination
argument for `ScanChain.fuel_bound`.

**Structure**:
- §5.1: `unwindIndents` preserves offset/inputEnd/input
- §5.2: `skipToContent` pipeline offset monotonicity
- §5.3: `scanNextToken_preprocess` offset monotonicity + hasMore
- §5.4: Per-dispatch-branch offset strict inequality
- §5.5: `scanNextToken_progress` capstone
-/

/-! #### §5.1  `unwindIndents` Preserves offset/inputEnd/input

`unwindIndentsLoop` only calls `emit .blockEnd` and pops `indents`.
Neither operation touches `offset`, `inputEnd`, or `input`. -/

theorem unwindIndentsLoop_offset_eq (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).offset = s.offset := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · -- condition true: emit blockEnd, pop indents, recurse
      rw [ih]; rfl
    · -- condition false: identity
      rfl

theorem unwindIndents_offset_eq (s : ScannerState) (col : Int) :
    (unwindIndents s col).offset = s.offset :=
  unwindIndentsLoop_offset_eq s col s.indents.size

theorem unwindIndentsLoop_inputEnd_eq (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).inputEnd = s.inputEnd := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; rfl
    · rfl

theorem unwindIndents_inputEnd_eq (s : ScannerState) (col : Int) :
    (unwindIndents s col).inputEnd = s.inputEnd :=
  unwindIndentsLoop_inputEnd_eq s col s.indents.size

theorem unwindIndentsLoop_input_eq (s : ScannerState) (col : Int) (fuel : Nat) :
    (unwindIndentsLoop s col fuel).input = s.input := by
  induction fuel generalizing s with
  | zero => unfold unwindIndentsLoop; rfl
  | succ fuel' ih =>
    unfold unwindIndentsLoop
    split
    · rw [ih]; rfl
    · rfl

theorem unwindIndents_input_eq (s : ScannerState) (col : Int) :
    (unwindIndents s col).input = s.input :=
  unwindIndentsLoop_input_eq s col s.indents.size

/-! #### §5.2  `skipToContent` Pipeline Offset Monotonicity

Each phase of the skipToContent pipeline preserves or increases offset:
- `skipToContentWs`: may advance past whitespace (offset ≥)
- `skipToContentComment`: may advance past comment (offset ≥)
- `consumeNewline`: may advance past newline (offset ≥)
- `skipToContentLoop`: composition, monotone by induction
- `skipToContent`: trivial wrapper -/

-- skipToContentWs: on success, offset ≥
theorem skipToContentWs_offset_ge (s s' : ScannerState)
    (h : skipToContentWs s = .ok s') : s'.offset ≥ s.offset := by
  unfold skipToContentWs at h
  simp (config := { zetaDelta := true }) only [] at h
  split at h  -- if s.needIndentCheck
  · -- needIndentCheck = true: let s1 := skipSpaces s; ...
    split at h  -- if (!inFlow && indent < 0) || col ≤ indent
    · -- condition true
      split at h  -- match (skipSpaces s).peek?
      · -- some '\t'
        split at h  -- match (skipWhitespace (skipSpaces s)).peek?
        · injection h with h; rw [← h]
          exact Nat.le_trans (skipSpaces_offset_ge s) (skipWhitespace_offset_ge _)
        · split at h  -- if isLineBreakBool c
          · injection h with h; rw [← h]
            exact Nat.le_trans (skipSpaces_offset_ge s) (skipWhitespace_offset_ge _)
          · split at h  -- if indent < 0 && flow indicators
            · injection h with h; rw [← h]
              exact Nat.le_trans (skipSpaces_offset_ge s) (skipWhitespace_offset_ge _)
            · simp at h
        · injection h with h; rw [← h]
          exact Nat.le_trans (skipSpaces_offset_ge s) (skipWhitespace_offset_ge _)
      · -- _ (not tab) → .ok (skipSpaces s)
        injection h with h; rw [← h]; exact skipSpaces_offset_ge s
    · -- past indentation → .ok (skipWhitespace (skipSpaces s))
      injection h with h; rw [← h]
      exact Nat.le_trans (skipSpaces_offset_ge s) (skipWhitespace_offset_ge _)
  · -- needIndentCheck = false → .ok (skipWhitespace s)
    injection h with h; rw [← h]; exact skipWhitespace_offset_ge s

-- skipToContentComment: offset ≥ (pure function, no Except)
theorem skipToContentComment_offset_ge (s : ScannerState) :
    (skipToContentComment s).offset ≥ s.offset := by
  unfold skipToContentComment
  split  -- match s.peek?
  · -- some '#'
    dsimp only []  -- zeta-reduce let bindings
    split  -- match s.peekBack? (inside the if condition)
    · -- peekBack? = some c
      split  -- if (s.col == 0 || (pred c)) = true
      · show (collectCommentTextLoop s.advance "" (s.advance.inputEnd - s.advance.offset)).2.offset ≥ s.offset
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (collectCommentTextLoop_offset_ge _ _ _)
      · exact Nat.le_refl _
    · -- peekBack? = none: commentOk = s.col == 0 || true
      split  -- if condition
      · show (collectCommentTextLoop s.advance "" (s.advance.inputEnd - s.advance.offset)).2.offset ≥ s.offset
        exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (collectCommentTextLoop_offset_ge _ _ _)
      · rename_i h_false; simp at h_false
  · exact Nat.le_refl _

-- skipToContentLoop: by induction on fuel, offset monotone
theorem skipToContentLoop_offset_ge (s s' : ScannerState) (fuel : Nat)
    (h : skipToContentLoop s fuel = .ok s') : s'.offset ≥ s.offset := by
  induction fuel generalizing s with
  | zero => unfold skipToContentLoop at h; injection h with h; rw [← h]; exact Nat.le_refl _
  | succ n ih =>
    unfold skipToContentLoop at h
    -- match skipToContentWs s
    split at h
    · simp at h  -- error case
    · -- ok s1
      rename_i s1 h_ws
      -- Now: let s2 := skipToContentComment s1; match s2.peek? with ...
      -- simp only [] to reduce the let binding
      simp only [] at h
      have h1 : s1.offset ≥ s.offset := skipToContentWs_offset_ge s s1 h_ws
      have h2 : (skipToContentComment s1).offset ≥ s1.offset :=
        skipToContentComment_offset_ge s1
      -- match (skipToContentComment s1).peek?
      split at h
      · -- some c
        split at h
        · -- isLineBreak? c = true
          -- consumeNewline → possible struct update → recurse
          split at h
          · -- not in flow sequence → simpleKeyAllowed := true
            -- The struct update { s3 with simpleKeyAllowed := true } preserves offset
            have h3 : (consumeNewline (skipToContentComment s1)).offset ≥
                (skipToContentComment s1).offset := consumeNewline_offset_ge _
            -- Let Lean infer the struct argument from h to avoid type mismatch
            have h4 := ih _ h
            -- h4.offset reduces through the struct projection since simpleKeyAllowed ≠ offset
            exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_trans h3 h4)
          · -- in flow sequence → no struct update
            have h3 : (consumeNewline (skipToContentComment s1)).offset ≥
                (skipToContentComment s1).offset := consumeNewline_offset_ge _
            exact Nat.le_trans (Nat.le_trans h1 h2) (Nat.le_trans h3 (ih _ h))
        · -- isLineBreak? c = false → return s2
          injection h with h; rw [← h]; exact Nat.le_trans h1 h2
      · -- none → return s2
        injection h with h; rw [← h]; exact Nat.le_trans h1 h2

-- skipToContent: trivial wrapper
theorem skipToContent_offset_ge (s s' : ScannerState)
    (h : skipToContent s = .ok s') : s'.offset ≥ s.offset := by
  unfold skipToContent at h
  exact skipToContentLoop_offset_ge s s' _ h

/-! ##### `skipToContent` `_preserves_LineariseFit`

Class A passthrough: tokens unchanged, pendingKeys preserved, offset
monotone.  Uses the no-change convenience helper. -/

theorem skipToContent_preserves_LineariseFit (s s' : ScannerState)
    (h_eq : skipToContent s = .ok s') (h : LineariseFit s) : LineariseFit s' :=
  LineariseFit_via_no_change s s'
    (skipToContent_preserves_ScanInv s s' h.1 h_eq)
    (skipToContent_preserves_pendingKeys s s' h_eq)
    (skipToContent_preserves_tokens s s' h_eq)
    (skipToContent_offset_ge s s' h_eq)
    h

/-! ##### `unwindIndents` `_preserves_LineariseFit`

Multi-emit: any new tokens are `.blockEnd` at the loop state's
`currentPos`, which doesn't drift since `emit`/`indents.pop` preserve
offset/line/col.  So the FIRST new token's pos = original `s.currentPos`. -/

/-- If `unwindIndentsLoop` adds at least one token, the first new
    token's `pos` equals the input state's `currentPos`. -/
private theorem unwindIndentsLoop_first_new_pos
    (s : ScannerState) (col : Int) (fuel : Nat)
    (h_lt : s.tokens.size < (unwindIndentsLoop s col fuel).tokens.size) :
    ((unwindIndentsLoop s col fuel).tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  match fuel with
  | 0 =>
    -- result is s, contradicts h_lt
    simp only [unwindIndentsLoop] at h_lt
    omega
  | fuel' + 1 =>
    simp only [unwindIndentsLoop] at h_lt ⊢
    split at h_lt
    · -- emit + pop + recurse
      split  -- in goal
      · -- consistent: emit branch
        have h_emit_size : (s.emit .blockEnd).tokens.size = s.tokens.size + 1 :=
          emit_tokens_size s _
        have h_pop_size :
            ({s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop}).tokens.size
              = s.tokens.size + 1 := h_emit_size
        have h_lt_pop : s.tokens.size <
            ({s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop}).tokens.size := by
          rw [h_pop_size]; omega
        rw [unwindIndentsLoop_preserves_prefix
            ({s.emit .blockEnd with indents := (s.emit .blockEnd).indents.pop})
            col fuel' s.tokens.size h_lt_pop]
        show ((s.emit .blockEnd).tokens[s.tokens.size]'h_lt_pop).pos = s.currentPos
        simp only [ScannerState.emit, Array.getElem_push_eq]
      · contradiction
    · -- no-emit: h_lt becomes s.tokens.size < s.tokens.size, false
      omega

private theorem unwindIndents_first_new_pos
    (s : ScannerState) (col : Int)
    (h_lt : s.tokens.size < (unwindIndents s col).tokens.size) :
    ((unwindIndents s col).tokens[s.tokens.size]'h_lt).pos = s.currentPos := by
  unfold unwindIndents at h_lt ⊢
  exact unwindIndentsLoop_first_new_pos s col s.indents.size h_lt

theorem unwindIndents_preserves_LineariseFit (s : ScannerState) (col : Int)
    (h : LineariseFit s) : LineariseFit (unwindIndents s col) := by
  apply LineariseFit_via_first_new s (unwindIndents s col)
    (unwindIndents_preserves_ScanInv s col h.1)
    (unwindIndents_preserves_pendingKeys s col)
    (unwindIndents_adds_tokens s col)
    (fun i hi => unwindIndents_preserves_prefix s col i hi)
    ?first_new
    ?off_mono
    h
  case first_new =>
    intro h_lt
    rw [unwindIndents_first_new_pos s col h_lt]
    show s.offset ≤ s.offset
    omega
  case off_mono =>
    rw [unwindIndents_offset_eq]
    omega

/-! #### §5.3  `scanNextToken_preprocess` Offset Monotonicity

`scanNextToken_preprocess` runs skipToContent + unwindIndents + saveSimpleKey.
All three preserve or increase offset. When it returns `some (s', c)`,
`s'.peek? = some c`, which means `s'.hasMore`. -/

theorem preprocess_offset_ge (s s' : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s', c))) :
    s'.offset ≥ s.offset := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h  -- match skipToContent s
  · simp at h
  · rename_i s_skip h_skip
    have h_ge : s_skip.offset ≥ s.offset := skipToContent_offset_ge s s_skip h_skip
    split at h  -- if !s_skip.hasMore
    · simp at h
    · split at h  -- if !inFlow && needIndentCheck
      · -- unwindIndents path: trailing content check
        split at h
        · simp at h
        · split at h  -- match peek?
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerProgress.saveSimpleKey_offset]
            show ({ unwindIndents s_skip ↑s_skip.col with needIndentCheck := false }).offset ≥ s.offset
            show (unwindIndents s_skip ↑s_skip.col).offset ≥ s.offset
            rw [unwindIndents_offset_eq]; exact h_ge
      · -- no unwindIndents path: trailing content check
        split at h
        · simp at h
        · split at h  -- match peek?
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerProgress.saveSimpleKey_offset]; exact h_ge

theorem preprocess_hasMore (s s' : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s', c))) :
    s'.offset < s'.inputEnd := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h  -- if !inFlow && needIndentCheck
      · split at h  -- trailing content
        · simp at h
        · split at h  -- match peek?
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [ScannerState.peek?] at *
            rename_i h_peek
            split at h_peek
            · assumption
            · simp at h_peek
      · split at h  -- trailing content
        · simp at h
        · split at h  -- match peek?
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h
            simp only [ScannerState.peek?] at *
            rename_i h_peek
            split at h_peek
            · assumption
            · simp at h_peek

/-! #### §5.3.5  Sub-Scanner Offset Progress (Strict)

Each sub-scanner called by the dispatch functions strictly advances
offset. These use `advance_offset_lt` from ScannerProgress for the
first `advance`, and the `_offset_ge` helpers from §A for subsequent
operations.
-/

-- scanValueClearKey preserves offset
theorem svck_offset (s : ScannerState) :
    (scanValueClearKey s).offset = s.offset := by
  unfold scanValueClearKey
  split <;> (try split) <;> (try split) <;> rfl
theorem svck_inputEnd (s : ScannerState) :
    (scanValueClearKey s).inputEnd = s.inputEnd := by
  unfold scanValueClearKey
  split <;> (try split) <;> (try split) <;> rfl

-- scanValuePrepare preserves offset
-- (Initiative 3 / J.2 step 5: the `simp ... { zetaDelta := true }`
-- step that folded the setIfInBounds let-bindings is no longer needed.)
theorem svp_offset (s : ScannerState) :
    (scanValuePrepare s).offset = s.offset := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split; · rfl
    · split
      · exact ScannerProgress.pushMappingIndent_offset s _
      · rfl
theorem svp_inputEnd (s : ScannerState) :
    (scanValuePrepare s).inputEnd = s.inputEnd := by
  unfold scanValuePrepare
  split
  · split
    · split <;> rfl
    · rfl
  · split; · rfl
    · split
      · exact ScannerProgress.pushMappingIndent_inputEnd s _
      · rfl

set_option maxHeartbeats 800000 in
/-- `scanValue` strictly advances offset when `offset < inputEnd`. -/
theorem scanValue_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanValue s = .ok s') :
    s.offset < s'.offset := by
  unfold scanValue at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · split at h
    · cases h
    · injection h with h_eq; subst h_eq
      have hck := svck_offset s; have hcke := svck_inputEnd s
      have hvp : (scanValuePrepare (scanValueClearKey s)).offset = s.offset := by rw [svp_offset, hck]
      have hvpe : (scanValuePrepare (scanValueClearKey s)).inputEnd = s.inputEnd := by rw [svp_inputEnd, hcke]
      have h1 := ScannerProgress.advance_offset_lt ((scanValuePrepare (scanValueClearKey s)).emit .value)
        (by rw [ScannerProgress.emit_offset, ScannerProgress.emit_inputEnd, hvp, hvpe]; exact hlt)
      rw [ScannerProgress.emit_offset, hvp] at h1; exact h1

set_option maxHeartbeats 800000 in
/-- `scanDocumentStart` strictly advances offset when `offset < inputEnd`. -/
theorem scanDocumentStart_offset_lt (s : ScannerState) (hlt : s.offset < s.inputEnd) :
    s.offset < (scanDocumentStart s).offset := by
  unfold scanDocumentStart; dsimp only []
  generalize h_su : unwindIndents s (-1) = s_u
  have h_off : s_u.offset = s.offset := h_su ▸ unwindIndents_offset_eq s _
  have h_end : s_u.inputEnd = s.inputEnd := h_su ▸ unwindIndents_inputEnd_eq s _
  rw [← h_off]
  let s_kd : ScannerState := { s_u with simpleKey := { possible := false }, pendingKeyActive := none }
  show s_u.offset < ((s_kd.emit .documentStart).advanceN 3).offset
  refine ScannerProgress.advanceN_succ_offset_lt (s_kd.emit .documentStart) 2 ?_
  rw [ScannerProgress.emit_offset, ScannerProgress.emit_inputEnd]
  show s_u.offset < s_u.inputEnd; rw [h_off, h_end]; exact hlt

theorem docEnd_core (s : ScannerState) (hlt : s.offset < s.inputEnd) :
    ∀ s_u, unwindIndents s (-1) = s_u →
    s.offset < (({ s_u with simpleKey := ({ possible := false } : SimpleKeyState),
                              pendingKeyActive := none }.emit .documentEnd).advanceN 3).offset := by
  intro s_u h_su
  have h_off := (h_su ▸ unwindIndents_offset_eq s _ : s_u.offset = s.offset)
  have h_end := (h_su ▸ unwindIndents_inputEnd_eq s _ : s_u.inputEnd = s.inputEnd)
  rw [← h_off]
  exact ScannerProgress.advanceN_succ_offset_lt
    ({ s_u with simpleKey := ({ possible := false } : SimpleKeyState),
                pendingKeyActive := none }.emit .documentEnd) 2
    (by rw [ScannerProgress.emit_offset, ScannerProgress.emit_inputEnd]; show s_u.offset < s_u.inputEnd; rw [h_off, h_end]; exact hlt)

set_option maxHeartbeats 6400000 in
/-- `scanDocumentEnd` strictly advances offset when `offset < inputEnd`. -/
theorem scanDocumentEnd_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanDocumentEnd s = .ok s') :
    s.offset < s'.offset := by
  unfold scanDocumentEnd at h; dsimp only [] at h
  split at h
  · cases h
  · split at h
    · simp only [pure, Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
      subst h; dsimp only []; exact docEnd_core s hlt _ rfl
    · simp only [pure, Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
      subst h; dsimp only []; exact docEnd_core s hlt _ rfl
    · split at h
      · simp only [pure, Except.pure, Bind.bind, Except.bind, Except.ok.injEq] at h
        subst h; dsimp only []; exact docEnd_core s hlt _ rfl
      · simp only [Bind.bind, Except.bind] at h; cases h

set_option maxHeartbeats 800000 in
/-- `scanAnchorOrAlias` strictly advances offset when `offset < inputEnd`. -/
theorem scanAnchorOrAlias_offset_lt (s s' : ScannerState) (isAnchor : Bool)
    (hlt : s.offset < s.inputEnd) (h : scanAnchorOrAlias s isAnchor = .ok s') :
    s.offset < s'.offset := by
  unfold scanAnchorOrAlias at h; dsimp only [] at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; subst h
    exact Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
      (collectAnchorNameLoop_offset_ge _ _ _)

theorem scanYamlDirective_offset_ge' (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h : scanYamlDirective s s_after_ws startPos = .ok s') :
    s'.offset ≥ s_after_ws.offset := by
  unfold scanYamlDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · split at h
        · contradiction
        · injection h with h_eq; subst h_eq; dsimp only []
          exact Nat.le_trans (collectVersionMajorLoop_offset_ge _ _ _)
            (Nat.le_trans (collectVersionMinorLoop_offset_ge _ _ _) (skipWhitespace_offset_ge _))
      · split at h
        · contradiction
        · split at h <;> try contradiction
          all_goals (injection h with h_eq; subst h_eq; dsimp only []
                     exact Nat.le_trans (collectVersionMajorLoop_offset_ge _ _ _)
                       (Nat.le_trans (collectVersionMinorLoop_offset_ge _ _ _) (skipWhitespace_offset_ge _)))
      · injection h with h_eq; subst h_eq; dsimp only []
        exact Nat.le_trans (collectVersionMajorLoop_offset_ge _ _ _)
          (Nat.le_trans (collectVersionMinorLoop_offset_ge _ _ _) (skipWhitespace_offset_ge _))

theorem scanTagDirective_offset_ge' (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h : scanTagDirective s s_after_ws startPos = .ok s') :
    s'.offset ≥ s_after_ws.offset := by
  unfold scanTagDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      exact Nat.le_trans (collectTagHandleDirectiveLoop_offset_ge _ _ _)
        (Nat.le_trans (skipWhitespace_offset_ge _)
          (Nat.le_trans (collectTagPrefixLoop_offset_ge _ _ _) (skipWhitespace_offset_ge _)))
  · split at h
    · contradiction
    · split at h <;> try contradiction
      all_goals (injection h with h_eq; subst h_eq; dsimp only []
                 exact Nat.le_trans (collectTagHandleDirectiveLoop_offset_ge _ _ _)
                   (Nat.le_trans (skipWhitespace_offset_ge _)
                     (Nat.le_trans (collectTagPrefixLoop_offset_ge _ _ _) (skipWhitespace_offset_ge _))))
  · injection h with h_eq; subst h_eq; dsimp only []
    exact Nat.le_trans (collectTagHandleDirectiveLoop_offset_ge _ _ _)
      (Nat.le_trans (skipWhitespace_offset_ge _)
        (Nat.le_trans (collectTagPrefixLoop_offset_ge _ _ _) (skipWhitespace_offset_ge _)))

set_option maxHeartbeats 1600000 in
/-- `scanDirective` strictly advances offset when `offset < inputEnd`. -/
theorem scanDirective_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanDirective s = .ok s') :
    s.offset < s'.offset := by
  unfold scanDirective at h
  split at h
  · nomatch h
  · dsimp only [] at h
    have h_adv := ScannerProgress.advance_offset_lt s hlt
    have h_ws_ge : (skipWhitespace (collectDirectiveNameLoop s.advance "" (s.inputEnd - s.advance.offset)).snd).offset
        ≥ s.advance.offset :=
      Nat.le_trans (collectDirectiveNameLoop_offset_ge s.advance "" _) (skipWhitespace_offset_ge _)
    split at h
    · generalize h_yd : scanYamlDirective _ _ _ = yd at h
      cases yd with
      | error e => simp at h
      | ok s_yd =>
        simp only [Except.ok.injEq] at h; subst h
        exact Nat.lt_of_lt_of_le h_adv
          (Nat.le_trans h_ws_ge (Nat.le_trans (scanYamlDirective_offset_ge' _ _ _ _ h_yd) (skipToEndOfLine_offset_ge _)))
    · split at h
      · generalize h_td : scanTagDirective _ _ _ = td at h
        cases td with
        | error e => simp at h
        | ok s_td =>
          simp only [Except.ok.injEq] at h; subst h
          exact Nat.lt_of_lt_of_le h_adv
            (Nat.le_trans h_ws_ge (Nat.le_trans (scanTagDirective_offset_ge' _ _ _ _ h_td) (skipToEndOfLine_offset_ge _)))
      · simp only [Except.ok.injEq] at h; subst h
        exact Nat.lt_of_lt_of_le h_adv (Nat.le_trans h_ws_ge (skipToEndOfLine_offset_ge _))

theorem scanVerbatimTag_offset_ge (s : ScannerState) (startPos : YamlPos)
    (s' : ScannerState) (h : scanVerbatimTag s startPos = .ok s') :
    s'.offset ≥ s.offset := by
  unfold scanVerbatimTag at h; dsimp only [] at h
  split at h
  · cases h
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h; subst h
      exact Nat.le_trans (ScannerProgress.advance_offset_ge s)
        (collectVerbatimTagLoop_offset_ge _ _ _)

theorem scanSecondaryTag_offset_ge (s : ScannerState) (startPos : YamlPos) :
    (scanSecondaryTag s startPos).offset ≥ s.offset := by
  unfold scanSecondaryTag; dsimp only []
  show ((_ : ScannerState).emitAt _ _).offset ≥ s.offset
  exact Nat.le_trans (ScannerProgress.advance_offset_ge s) (collectTagSuffixLoop_offset_ge _ _ _)

theorem scanNamedTag_offset_ge (s : ScannerState) (startPos : YamlPos) (inputEnd : Nat) :
    (scanNamedTag s startPos inputEnd).offset ≥ s.offset := by
  unfold scanNamedTag; dsimp only []
  show ((_ : ScannerState).emitAt _ _).offset ≥ s.offset
  split
  · exact Nat.le_trans (collectTagHandleLoop_offset_ge s "" _)
      (collectTagSuffixLoop_offset_ge _ _ _)
  · exact collectTagHandleLoop_offset_ge s "" _

set_option maxHeartbeats 800000 in
/-- `scanTag` strictly advances offset when `offset < inputEnd`. -/
theorem scanTag_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanTag s = .ok s') :
    s.offset < s'.offset := by
  unfold scanTag at h; dsimp only [] at h
  split at h
  · -- verbatim tag (monadic)
    simp only [bind, Except.bind, pure, Except.pure] at h
    split at h
    · cases h
    · simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
        (scanVerbatimTag_offset_ge _ _ _ ‹_›)
  · -- secondary tag (pure)
    simp only [Except.ok.injEq] at h; subst h; dsimp only []
    exact Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
      (scanSecondaryTag_offset_ge _ _)
  · -- named tag (pure)
    simp only [Except.ok.injEq] at h; subst h; dsimp only []
    exact Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
      (scanNamedTag_offset_ge _ _ _)

/-- `scanDoubleQuoted` strictly advances offset when `offset < inputEnd`. -/
theorem scanDoubleQuoted_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanDoubleQuoted s = .ok s') :
    s.offset < s'.offset := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i content_state heq
    obtain ⟨content, s_after_close⟩ := content_state
    simp only [] at h heq
    have h_chain : s.offset < s_after_close.offset :=
      Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
        (collectDoubleQuotedLoop_offset_ge _ _ _ _ _ _ _ _ _ heq)
    split at h
    · split at h
      · cases h
      · injection h with h; subst h; exact h_chain
    · injection h with h; subst h; exact h_chain

/-- `scanSingleQuoted` strictly advances offset when `offset < inputEnd`. -/
theorem scanSingleQuoted_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanSingleQuoted s = .ok s') :
    s.offset < s'.offset := by
  unfold scanSingleQuoted at h
  simp only [bind, Except.bind] at h
  split at h
  · cases h
  · rename_i content_state heq
    obtain ⟨content, s_after_close⟩ := content_state
    simp only [] at h heq
    have h_chain : s.offset < s_after_close.offset :=
      Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
        (collectSingleQuotedLoop_offset_ge _ _ _ _ _ _ _ _ _ heq)
    split at h
    · split at h
      · cases h
      · simp only [Except.ok.injEq] at h; subst h; exact h_chain
    · injection h with h; subst h; exact h_chain

theorem scanBlockScalarBody_offset_ge (s_orig s_nl : ScannerState)
    (chomp : ChompStyle) (expl : Option Nat) (isLit : Bool) (startPos : YamlPos)
    (s' : ScannerState)
    (h : scanBlockScalarBody s_orig s_nl chomp expl isLit startPos = .ok s') :
    s'.offset ≥ s_nl.offset := by
  unfold scanBlockScalarBody at h; dsimp only [] at h
  split at h
  · cases h
  · simp only [Except.ok.injEq] at h; subst h
    exact collectBlockScalarLoop_offset_ge _ _ _ _ _

/-- `scanBlockScalar` strictly advances offset when `offset < inputEnd`. -/
theorem scanBlockScalar_offset_lt (s s' : ScannerState)
    (hlt : s.offset < s.inputEnd) (h : scanBlockScalar s = .ok s') :
    s.offset < s'.offset := by
  unfold scanBlockScalar at h; dsimp only [] at h
  generalize h_cn : scanBlockScalarConsumeNewline _ = cn at h
  cases cn with
  | error e => simp at h
  | ok s_nl =>
    have h_pre : s.advance.offset ≤ s_nl.offset :=
      Nat.le_trans (parseBlockHeaderLoop_offset_ge _ _ _ _)
        (Nat.le_trans (skipWhitespace_offset_ge _)
          (Nat.le_trans (scanBlockScalarSkipComment_offset_ge _)
            (scanBlockScalarConsumeNewline_offset_ge _ _ h_cn)))
    have h_body := scanBlockScalarBody_offset_ge _ _ _ _ _ _ _ h
    exact Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt) (Nat.le_trans h_pre h_body)

-- Helpers for scanPlainScalar_offset_lt

theorem flowIndicator_isIndicator' (c : Char) (h : isFlowIndicatorBool c = true) :
    isIndicatorBool c = true := by
  simp [isFlowIndicatorBool, List.mem_cons] at h
  rcases h with rfl | rfl | rfl | rfl | rfl; all_goals decide

theorem canStart_not_lb (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isLineBreakBool c = false := by
  unfold canStartPlainScalarBool at hcan; split at hcan
  · rename_i hc; rcases hc with rfl | rfl | rfl <;> decide
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan; exact hcan.2

theorem canStart_not_ws (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isWhiteSpaceBool c = false := by
  unfold canStartPlainScalarBool at hcan; split at hcan
  · rename_i hc; rcases hc with rfl | rfl | rfl <;> decide
  · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan; exact hcan.1.2

theorem canStart_plainSafe (c : Char) (next : Option Char) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c next inFlow = true) :
    isPlainSafeBool c inFlow = true := by
  have hws := canStart_not_ws c next inFlow hcan
  have hlb := canStart_not_lb c next inFlow hcan
  simp only [isPlainSafeBool]; split
  · simp [hws, hlb]; cases h_fi : isFlowIndicatorBool c
    · rfl
    · unfold canStartPlainScalarBool at hcan; split at hcan
      · rename_i hc; rcases hc with rfl | rfl | rfl <;> simp [isFlowIndicatorBool] at h_fi
      · simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan
        exact absurd (flowIndicator_isIndicator' c h_fi) (by simp [hcan.1.1])
  · simp [hws, hlb]

set_option maxHeartbeats 1600000 in
theorem canStart_terminates_none (c : Char) (s : ScannerState) (inFlow : Bool)
    (hcan : canStartPlainScalarBool c (s.peekAt? 1) inFlow = true)
    (hnoDoc : (s.col == 0 && atDocumentBoundary s) = false) :
    collectPlainScalar_terminates? c s "" "" inFlow = none := by
  unfold collectPlainScalar_terminates?
  have h_not_hash : (c == '#' && decide ("".length > 0)) = false := by simp
  cases h_colon : (c == ':') with
  | false =>
    have hnofi : (inFlow && isFlowIndicatorBool c) = false := by
      cases h_fi : isFlowIndicatorBool c with
      | false => simp
      | true =>
        have hind : isIndicatorBool c = true := flowIndicator_isIndicator' c h_fi
        have hnd : c ≠ '-' := by intro hh; rw [hh] at h_fi; simp [isFlowIndicatorBool] at h_fi
        have hnq : c ≠ '?' := by intro hh; rw [hh] at h_fi; simp [isFlowIndicatorBool] at h_fi
        have hnc : c ≠ ':' := by intro hh; rw [hh] at h_colon; simp at h_colon
        unfold canStartPlainScalarBool at hcan
        simp only [hnd, hnq, hnc, false_or, ↓reduceIte, Bool.and_eq_true, Bool.not_eq_true'] at hcan
        simp [hind] at hcan
    simp only [h_not_hash, hnofi, hnoDoc, ↓reduceIte, Bool.false_eq_true]
  | true =>
    have hceq : c = ':' := eq_of_beq h_colon
    subst hceq; dsimp only []
    simp only [h_not_hash, ↓reduceIte, Bool.false_eq_true]
    split
    · rename_i n hn
      unfold canStartPlainScalarBool at hcan
      rw [if_pos (Or.inr (Or.inr rfl)), hn] at hcan
      simp only [Bool.and_eq_true, Bool.not_eq_true'] at hcan
      obtain ⟨⟨hws, hlb⟩, hflow⟩ := hcan
      simp [isBlankBool, hws, hlb, hflow]
    · rename_i hn
      unfold canStartPlainScalarBool at hcan
      rw [if_pos (Or.inr (Or.inr rfl)), hn] at hcan
      contradiction

-- `scanPlainScalar` strictly advances offset when `offset < inputEnd`,
-- the first character can start a plain scalar, and there is no document
-- boundary at column 0.
set_option maxHeartbeats 3200000 in
theorem scanPlainScalar_offset_lt (s s' : ScannerState) (c : Char)
    (hlt : s.offset < s.inputEnd) (hpeek : s.peek? = some c)
    (hcan : canStartPlainScalarBool c (s.peekAt? 1) s.inFlow = true)
    (hnoDoc : (s.col == 0 && atDocumentBoundary s) = false)
    (h : scanPlainScalar s = .ok s') :
    s.offset < s'.offset := by
  unfold scanPlainScalar at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  generalize h_loop : collectPlainScalarLoop s "" "" _ s.inFlow _ s.inputEnd = loop_res at h
  cases loop_res with
  | error e => simp at h
  | ok result =>
    simp only [Except.ok.injEq] at h; subst h; dsimp only []
    conv at h_loop => lhs; unfold collectPlainScalarLoop
    dsimp only [] at h_loop
    have h_term := canStart_terminates_none c s s.inFlow hcan hnoDoc
    have h_not_lb := canStart_not_lb c (s.peekAt? 1) s.inFlow hcan
    have h_not_ws := canStart_not_ws c (s.peekAt? 1) s.inFlow hcan
    have h_ps := canStart_plainSafe c (s.peekAt? 1) s.inFlow hcan
    simp only [hpeek, h_term, h_not_lb, h_not_ws, h_ps, ↓reduceIte, Bool.false_eq_true] at h_loop
    exact Nat.lt_of_lt_of_le (ScannerProgress.advance_offset_lt s hlt)
      (collectPlainScalarLoop_offset_ge _ _ _ _ _ _ _ _ h_loop)

/-! #### §5.4  Per-Dispatch Offset Strict Inequality

Each dispatch function that returns `some s'` calls `advance` at
least once on a state with `hasMore`, giving `s'.offset > s_in.offset`.
-/

set_option maxHeartbeats 1600000 in
theorem dispatchStructural_offset_gt (s s' : ScannerState) (c : Char)
    (h_hm : s.offset < s.inputEnd)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    s'.offset > s.offset := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  split at h  -- s.inFlow && indent check
  · split at h  -- c != ']' && c != '}'
    · cases h
    · split at h  -- s.col == 0 && s.inFlow && (atDocumentStart || atDocumentEnd)
      · cases h
      · split at h  -- s.col == 0 && atDocumentStart
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact scanDocumentStart_offset_lt s h_hm
        · split at h  -- s.col == 0 && atDocumentEnd
          · split at h
            · cases h
            · injection h with h; injection h with h; subst h
              exact scanDocumentEnd_offset_lt s _ h_hm ‹_›
          · split at h  -- c == '%' && s.col == 0
            · split at h
              · cases h
              · injection h with h; injection h with h; subst h
                exact scanDirective_offset_lt s _ h_hm ‹_›
            · nomatch h
  · split at h  -- s.col == 0 && s.inFlow && (atDocumentStart || atDocumentEnd)
    · cases h
    · split at h  -- s.col == 0 && atDocumentStart
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact scanDocumentStart_offset_lt s h_hm
      · split at h  -- s.col == 0 && atDocumentEnd
        · split at h  -- scanDocumentEnd result
          · cases h
          · injection h with h; injection h with h; subst h
            exact scanDocumentEnd_offset_lt s _ h_hm ‹_›
        · split at h  -- c == '%' && s.col == 0
          · split at h  -- scanDirective result
            · cases h
            · injection h with h; injection h with h; subst h
              exact scanDirective_offset_lt s _ h_hm ‹_›
          · nomatch h

theorem dispatchFlowIndicators_offset_gt (s s' : ScannerState) (c : Char)
    (h_hm : s.offset < s.inputEnd)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    s'.offset > s.offset := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    exact ScannerProgress.scanFlowSequenceStart_offset_lt s h_hm
  · split at h
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact ScannerProgress.scanFlowSequenceEnd_offset_lt s h_hm
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        exact ScannerProgress.scanFlowMappingStart_offset_lt s h_hm
      · split at h
        · split at h
          · cases h
          · split at h
            · cases h
            · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              exact ScannerProgress.scanFlowMappingEnd_offset_lt s h_hm
        · split at h
          · split at h
            · cases h
            · split at h
              · cases h
              · injection h with h; injection h with h; subst h
                exact ScannerProgress.scanFlowEntry_offset_lt s _ h_hm ‹_›
          · nomatch h

theorem dispatchBlockIndicators_offset_gt (s s' : ScannerState) (c : Char)
    (h_hm : s.offset < s.inputEnd)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    s'.offset > s.offset := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h  -- c == '-' && ...
  · split at h
    · cases h
    · injection h with h; injection h with h; subst h
      exact ScannerProgress.scanBlockEntry_offset_lt s _ h_hm ‹_›
  · split at h  -- c == '?' && ...
    · split at h
      · cases h
      · injection h with h; injection h with h; subst h
        exact ScannerProgress.scanKey_offset_lt s _ h_hm ‹_›
    · split at h  -- c == ':' && ...
      · split at h
        · cases h
        · injection h with h; injection h with h; subst h
          exact scanValue_offset_lt s _ h_hm ‹_›
      · nomatch h

set_option maxHeartbeats 1600000 in
theorem dispatchContent_offset_gt (s s' : ScannerState) (c : Char)
    (h_hm : s.offset < s.inputEnd)
    (hpeek : s.peek? = some c)
    (hnoDoc : (s.col == 0 && atDocumentBoundary s) = false)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    s'.offset > s.offset := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  split at h  -- c == '&'
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h; subst h; dsimp only []
      exact scanAnchorOrAlias_offset_lt s _ true h_hm ‹_›
  · split at h  -- c == '*'
    · split at h
      · cases h
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h; subst h
          exact scanAnchorOrAlias_offset_lt s _ false h_hm ‹_›
    · split at h  -- c == '!'
      · split at h
        · cases h
        · simp only [Except.ok.injEq] at h; subst h
          exact scanTag_offset_lt s _ h_hm ‹_›
      · split at h  -- c == '|' || c == '>'
        · split at h
          · cases h
          · simp only [Except.ok.injEq] at h; subst h
            exact scanBlockScalar_offset_lt s _ h_hm ‹_›
        · split at h  -- c == '"'
          · split at h
            · cases h
            · simp only [Except.ok.injEq] at h
              split at h
              · subst h; dsimp only []; exact scanDoubleQuoted_offset_lt s _ h_hm ‹_›
              · subst h; exact scanDoubleQuoted_offset_lt s _ h_hm ‹_›
          · split at h  -- c == '\''
            · split at h
              · cases h
              · simp only [Except.ok.injEq] at h
                split at h
                · subst h; dsimp only []; exact scanSingleQuoted_offset_lt s _ h_hm ‹_›
                · subst h; exact scanSingleQuoted_offset_lt s _ h_hm ‹_›
            · split at h  -- canStartPlainScalarBool
              · split at h
                · cases h
                · simp only [Except.ok.injEq] at h; subst h
                  exact scanPlainScalar_offset_lt s _ c h_hm hpeek
                    (by assumption) hnoDoc (by assumption)
              · cases h

/-! #### §5.5  `scanNextToken_progress` — Capstone

Every successful `scanNextToken` call returning `some s'` has
`s'.offset > s.offset`. This is the key termination argument. -/

-- Helper: dispatchStructural returning none means no document boundary
theorem dispatchStructural_none_noDoc (s : ScannerState) (c : Char)
    (h : scanNextToken_dispatchStructural s c = .ok none) :
    (s.col == 0 && atDocumentBoundary s) = false := by
  unfold atDocumentBoundary
  rcases hcol : (s.col == 0) with _ | _
  · simp
  · simp only [Bool.true_and]
    rcases hds : atDocumentStart s with _ | _
    · simp only [Bool.false_or]
      rcases hde : atDocumentEnd s with _ | _
      · rfl
      · exfalso
        unfold scanNextToken_dispatchStructural at h
        simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
        simp only [hcol, hde, hds, Bool.true_and, Bool.or_true] at h
        repeat (first | (split at h; all_goals try simp at h) | simp at h)
    · exfalso
      unfold scanNextToken_dispatchStructural at h
      simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
      simp only [hcol, hds, Bool.true_and] at h
      repeat (first | (split at h; all_goals try simp at h) | simp at h)

-- Helper: preprocess returning some gives peek?
theorem preprocess_peek_eq (s s' : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s', c))) :
    s'.peek? = some c := by
  unfold scanNextToken_preprocess at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  split at h
  · simp at h
  · split at h
    · simp at h
    · split at h
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; rename_i h_peek; exact h_peek
      · split at h
        · simp at h
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, rfl⟩ := h; rename_i h_peek; exact h_peek

/- **Scanner progress**: `scanNextToken` strictly advances offset.

    Every dispatch branch of `scanNextToken` calls `advance` at least once
    on a state where `offset < inputEnd` (guaranteed by `peek? = some c`
    from preprocessing). Combined with preprocessing's offset monotonicity,
    this gives `s'.offset > s.offset`.

    **Used by**: `ScanChain.fuel_bound` in EmitterScannability.lean to
    establish that the fuel `(input.utf8ByteSize + 1) * 4` suffices. -/
set_option maxHeartbeats 800000 in
theorem scanNextToken_progress (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s')) :
    s'.offset > s.offset := by
  unfold scanNextToken at h
  simp only [bind, Except.bind, pure, Except.pure, Bind.bind, Pure.pure] at h
  -- Split on preprocess result
  split at h
  · cases h
  · split at h
    · simp at h
    · rename_i sp c h_pre
      have h_ge := preprocess_offset_ge s sp c h_pre
      have h_hm := preprocess_hasMore s sp c h_pre
      -- Split on dispatchStructural
      split at h
      · cases h
      · split at h
        · -- some s1 (structural handled it)
          simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          exact Nat.lt_of_le_of_lt h_ge (dispatchStructural_offset_gt sp _ c h_hm ‹_›)
        · -- none (structural passed, continue to flow/block/content)
          rename_i h_struct
          have hnoDoc := dispatchStructural_none_noDoc sp c h_struct
          have h_peek := preprocess_peek_eq s sp c h_pre
          -- Outermost match is checkBlockFlowIndent
          split at h
          · cases h
          · -- Case-split on allowDirectives to resolve the if-expression
            rcases h_ad : sp.allowDirectives with _ | _
            <;> simp only [h_ad, Bool.false_eq_true, ↓reduceIte] at h
            · -- false case: dispatchers use sp directly
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp c = fi at h
              cases fi with
              | error => cases h
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  have := dispatchFlowIndicators_offset_gt sp _ c h_hm h_fi; omega
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp c = bi at h
                  cases bi with
                  | error => cases h
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      have := dispatchBlockIndicators_offset_gt sp _ c h_hm h_bi; omega
                    | none =>
                      generalize h_dc : scanNextToken_dispatchContent sp c = dc at h
                      cases dc with
                      | error => cases h
                      | ok s_dc =>
                        have h1 := @dispatchContent_offset_gt sp s_dc c h_hm h_peek hnoDoc h_dc
                        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h; omega
            · -- true case: dispatchers use { sp with ... }
              generalize h_sp2 : (({ sp with allowDirectives := false, documentEverStarted := true } : ScannerState)) = sp2 at h
              have h_hm2 : sp2.offset < sp2.inputEnd := by rw [← h_sp2]; exact h_hm
              have h_peek2 : sp2.peek? = some c := by rw [← h_sp2]; exact h_peek
              have hnoDoc2 : (sp2.col == 0 && atDocumentBoundary sp2) = false := by
                rw [← h_sp2]; exact hnoDoc
              have h_sp2_off : sp2.offset = sp.offset := by rw [← h_sp2]
              generalize h_fi : scanNextToken_dispatchFlowIndicators sp2 c = fi at h
              cases fi with
              | error => cases h
              | ok fi_opt =>
                cases fi_opt with
                | some s_fi =>
                  simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                  have := dispatchFlowIndicators_offset_gt sp2 _ c h_hm2 h_fi; omega
                | none =>
                  generalize h_bi : scanNextToken_dispatchBlockIndicators sp2 c = bi at h
                  cases bi with
                  | error => cases h
                  | ok bi_opt =>
                    cases bi_opt with
                    | some s_bi =>
                      simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                      have := dispatchBlockIndicators_offset_gt sp2 _ c h_hm2 h_bi; omega
                    | none =>
                      generalize h_dc : scanNextToken_dispatchContent sp2 c = dc at h
                      cases dc with
                      | error => cases h
                      | ok s_dc =>
                        simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                        have := dispatchContent_offset_gt sp2 _ c h_hm2 h_peek2 hnoDoc2 h_dc
                        omega

end L4YAML.Proofs.ScannerCorrectness
