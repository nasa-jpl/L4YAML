/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Basic
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Preserve.DpInv

/-! # `FlowMonoChain.Preserve.Helpers` — Phase 3 Step 6f.3b3.flowmono.preserve.helpers

**Sub-session 3 of `.flowmono.preserve`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 2747–~3330, ~580 LOC).
The *invariant carriers* that thread through `scanNextTokenIx` and
the per-flow-dispatch primitives in the forthcoming `.maintenance`
and `.sync` sub-sessions.

## Scope

  - **§1** — Per-line invariants over the token stream:
    `AllTokensOnLineIx`, `EndLineOnLineIx`, `StackEndLineOnLineIx`.
  - **§2** — `saveSimpleKeyIx` field-preservation (`@[simp]` lemmas
    for `indents`, `flowLevel`, `inFlow`, `explicitKeyLine`,
    `directivesPresent`, `allowDirectives`, `flowStack`,
    `needIndentCheck`, `peek?`).
  - **§3** — `saveSimpleKeyIx_id_of_flow_ska_false_ek_none` —
    identity in the flow-emitter common case.
  - **§4** — `scanValueValidateIx` success conditions:
    `_ok_of_not_possible_ek_none` and the key
    `_ok_of_flow_allTokensOnLine` that consumes
    `AllTokensOnLineIx` + `EndLineOnLineIx`.
  - **§5** — `saveSimpleKeyIx_filter_placeholder`.
  - **§6** — `AllTokensOnLineIx` transfer lemmas for `emit`,
    `advance`, `emitAt`, `saveSimpleKeyIx`, and the `allowDirectives`
    record update.
  - **§7** — `EndLineOnLineIx_saveSimpleKeyIx_flow`.
  - **§8** — Per-flow-dispatcher `AllTokensOnLineIx`:
    `scanFlowSequenceStartIx`, `scanFlowMappingStartIx`,
    `scanFlowSequenceEndIx`, `scanFlowMappingEndIx`,
    `scanFlowEntry` (literal-expression wrapper), and the
    `scanDoubleQuotedIx` quote-arm wrapper.
  - **§9** — `scanFlowSequenceStartIx` / `scanFlowMappingStartIx`
    clear `simpleKey.possible`.

## Legacy mapping

Mirrors `EmitterScannability.lean` lines 2747–3247 (skipping the
init-state lemma; see below):

  | Section | Legacy lines     | Indexed counterpart           |
  | ------- | ---------------- | ----------------------------- |
  | §1      | 2997–3013        | `AllTokensOnLineIx` family    |
  | §2      | 2925–2974        | `saveSimpleKeyIx_*`           |
  | §3      | 2978–2985        | `saveSimpleKeyIx_id_of_flow_…`|
  | §4      | 2987–3047        | `scanValueValidateIx_ok_*`    |
  | §5      | 3049–3059        | `saveSimpleKeyIx_filter_*`    |
  | §6      | 3063–3125        | `AllTokensOnLineIx_{emit,…}`  |
  | §7      | 3100–3115        | `EndLineOnLineIx_saveSimpleK…`|
  | §8      | 3132–3239        | Per-dispatcher `…OnLineIx`    |
  | §9      | 3147–3156        | `…_simpleKey_not_possible`    |

## Init-state lemma deferral (`.sync`)

The legacy `scanNextToken_preprocess_init_state` (lines 3258–3329)
characterizes the result of `scanNextToken_preprocess` on the initial
state `(ScannerState.mk' input).emit .streamStart`. The proof relies
on `ScannerSurfCorr` infrastructure (`initial_corr`,
`peek_of_chars_cons`, `skipToContent_of_content_char`, explicit
`unwindIndents` unfolding) that *does not yet have indexed twins*:
the indexed substrate uses `IxCursor`'s built-in `posBound` for
position evidence instead of `ScannerSurfCorr`, so a faithful
indexed port would require either (a) building the indexed
surface-correspondence bridge, or (b) re-deriving the analogous
reductions from `IxCursor.peek?_of_input_toList_cons` (no such lemma
exists today).

The lemma is consumed only by the `scanNextTokenIx_emit*_init`
family in `.sync` (legacy 4116+). Since `.sync` will need a
non-trivial indexed surface-correspondence layer anyway, the init-
state characterization moves there. This `.helpers` session ships
the invariant carriers and per-dispatcher transfer lemmas that the
`.maintenance` session consumes; `.sync` will both build the
surface-correspondence bridge and port the init-state characterization.

## Substrate notes

  * **`s.line` vs `s.cursor.pos.line`.** The legacy `ScannerState`
    has a `line : Nat` field; `ScannerStateIx` does not — `line` is a
    projection of the cursor (`s.cursor.pos.line`).
  * **Cursor-only `scanDoubleQuotedIx`.** The legacy
    `scanDoubleQuoted_preserves_simpleKey` is *not* needed as a
    separate lemma: the indexed `scanDoubleQuotedIx` operates on
    `IxCursor input` (no `simpleKey` field), and its state-level
    wrapping in `scanNextTokenIx_dispatchContent`'s `"`-arm is an
    explicit
    `{ { s with cursor := cAfter }.emitAt … with simpleKeyAllowed := false }`
    that preserves `simpleKey` by `rfl`. The §8
    `AllTokensOnLineIx_dispatchContent_quote_arm` lemma captures the
    transfer at the dispatcher-wrapper level instead.
  * **`pos` vs `start`.** Legacy `Positioned.pos.line` becomes
    indexed `IxToken.start.line`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ## §1  Per-line invariants -/

/-- All tokens in the stream are positioned at line `l`.
    Indexed twin of legacy `AllTokensOnLine`. -/
def AllTokensOnLineIx (s : ScannerStateIx input) (l : Nat) : Prop :=
  ∀ i, (h : i < s.tokens.size) → (s.tokens.tokens[i]'h).start.line = l

/-- When `simpleKey.possible`, both `endLine` and the saved cursor's
    line equal the current cursor's line. Indexed twin of legacy
    `EndLineOnLine` (which used `s.line`; the indexed substrate uses
    `s.cursor.pos.line`). -/
def EndLineOnLineIx (s : ScannerStateIx input) : Prop :=
  s.simpleKey.possible →
    s.simpleKey.endLine = s.cursor.pos.line
      ∧ s.simpleKey.pos.line = s.cursor.pos.line

/-- The top of `simpleKeyStack` (if any) satisfies `EndLineOnLineIx`
    at line `l`. Used after a flow close restores from the stack.
    Indexed twin of legacy `StackEndLineOnLine`. -/
def StackEndLineOnLineIx (s : ScannerStateIx input) (l : Nat) : Prop :=
  match s.simpleKeyStack.back? with
  | none => True
  | some sk => sk.possible → sk.endLine = l ∧ sk.pos.line = l

/-! ## §2  `saveSimpleKeyIx` field-preservation

`saveSimpleKeyIx` has three branches (identity / two-emit / identity);
for any field that is *not* touched by the inner `simpleKey`-record
update and is unchanged by `emit`, the proof is `rfl` in all branches. -/

@[simp] theorem saveSimpleKeyIx_indents (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).indents = s.indents := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

@[simp] theorem saveSimpleKeyIx_flowLevel (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).flowLevel = s.flowLevel := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

@[simp] theorem saveSimpleKeyIx_inFlow (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).inFlow = s.inFlow := by
  unfold ScannerStateIx.inFlow
  rw [saveSimpleKeyIx_flowLevel]

@[simp] theorem saveSimpleKeyIx_explicitKeyLine (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).explicitKeyLine = s.explicitKeyLine := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

@[simp] theorem saveSimpleKeyIx_directivesPresent (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).directivesPresent = s.directivesPresent := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

@[simp] theorem saveSimpleKeyIx_allowDirectives (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).allowDirectives = s.allowDirectives := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

@[simp] theorem saveSimpleKeyIx_flowStack (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).flowStack = s.flowStack := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

@[simp] theorem saveSimpleKeyIx_needIndentCheck (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).needIndentCheck = s.needIndentCheck := by
  unfold saveSimpleKeyIx; split
  · rfl
  · split <;> rfl

/-- `saveSimpleKeyIx` preserves `peek?` (it preserves the cursor). -/
theorem saveSimpleKeyIx_peek? (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).peek? = s.peek? := by
  unfold ScannerStateIx.peek?
  rw [saveSimpleKeyIx_cursor]

/-! ## §3  `saveSimpleKeyIx` identity in the flow-emitter case

In the flow-emitter context, every call to `saveSimpleKeyIx` happens
with `simpleKeyAllowed = false` and `explicitKeyLine = none`, so it
is the identity. -/

theorem saveSimpleKeyIx_id_of_flow_ska_false_ek_none (s : ScannerStateIx input)
    (h_flow : s.inFlow = true) (h_ska : s.simpleKeyAllowed = false)
    (h_ek : s.explicitKeyLine = none) :
    saveSimpleKeyIx s = s := by
  unfold saveSimpleKeyIx
  simp only [h_flow, h_ek, show (none == some s.cursor.pos.line) = false from rfl,
             Bool.and_false, Bool.false_eq_true, ↓reduceIte, h_ska]

/-! ## §4  `scanValueValidateIx` success conditions

`scanValueValidateIx` returns `.ok ()` when its five guards all
short-circuit. Two specialized openings (the flow-context one is the
key downstream consumer):

  * §4.1 — `_ok_of_not_possible_ek_none`: when both
    `simpleKey.possible` and `explicitKeyLine` are absent, every
    guard is `false`.
  * §4.2 — `_ok_of_flow_allTokensOnLine`: in flow context with
    `explicitKeyLine = none`, the missing-comma guard (`simpleKey +
    flowSequence + tokens[idx-1] on a prior line`) is discharged from
    `AllTokensOnLineIx` (every token is on the current line, so the
    prior token cannot be on a *different* line). -/

theorem scanValueValidateIx_ok_of_not_possible_ek_none (s : ScannerStateIx input)
    (h_ek : s.explicitKeyLine = none)
    (h_sk : s.simpleKey.possible = false) :
    scanValueValidateIx s = .ok () := by
  unfold scanValueValidateIx
  simp only [h_sk, Bool.false_and, ↓reduceIte, h_ek, reduceCtorEq]
  rfl

/-- In flow context with all tokens on the current cursor line and
    `EndLineOnLineIx s`, `scanValueValidateIx` succeeds. -/
theorem scanValueValidateIx_ok_of_flow_allTokensOnLine (s : ScannerStateIx input)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_end : EndLineOnLineIx s) :
    scanValueValidateIx s = .ok () := by
  unfold scanValueValidateIx EndLineOnLineIx at *
  cases h_poss : s.simpleKey.possible
  · simp only [h_flow, Bool.false_and, Bool.not_true, Bool.and_false,
               ↓reduceIte, h_ek, reduceCtorEq]
    rfl
  · have ⟨h_el, _⟩ := h_end h_poss
    simp only [h_flow, h_el, h_ek, Bool.not_true, Bool.and_false, Bool.false_and,
               Bool.true_and, bne_self_eq_false, ↓reduceIte, reduceCtorEq]
    by_cases h_ti : s.simpleKey.tokenIndex > 0
    · simp only [show (decide (s.simpleKey.tokenIndex > 0)) = true from decide_eq_true h_ti]
      cases h_tok : s.tokens.tokens[s.simpleKey.tokenIndex - 1]? with
      | none => rfl
      | some tok =>
        have ⟨h_bound, h_eq⟩ := Array.getElem?_eq_some_iff.mp h_tok
        have h_pos_line := h_atol (s.simpleKey.tokenIndex - 1) h_bound
        have h_tok_line : tok.start.line = s.cursor.pos.line := h_eq ▸ h_pos_line
        simp only [h_tok_line, bne_self_eq_false, Bool.and_false, ↓reduceIte]
        rfl
    · simp only [show (decide (s.simpleKey.tokenIndex > 0)) = false from
                   decide_eq_false (by omega)]
      rfl

/-! ## §5  `saveSimpleKeyIx_filter_placeholder`

The two-emit branch pushes two `.placeholder` tokens; the
`fun t => t.token != .placeholder` filter discards them. -/

theorem saveSimpleKeyIx_filter_placeholder (s : ScannerStateIx input) :
    (saveSimpleKeyIx s).tokens.tokens.filter (fun t => t.token != .placeholder)
    = s.tokens.tokens.filter (fun t => t.token != .placeholder) := by
  unfold saveSimpleKeyIx
  split
  · rfl
  · split
    · -- Two-emit branch: simpleKey record update is invisible to `.tokens`.
      -- Reduces to filtering after two pushes of `.placeholder`; each pushed
      -- token's `.token` field is `.placeholder`, so the `!=`-filter drops them.
      show
        Array.filter (fun t => t.token != .placeholder)
          ((s.tokens.tokens.push (IxToken.mk' s.cursor.pos YamlToken.placeholder s.cursor.pos
                (Nat.le_refl _) s.cursor.posBound)).push
            (IxToken.mk' s.cursor.pos YamlToken.placeholder s.cursor.pos
                (Nat.le_refl _) s.cursor.posBound)) =
        Array.filter (fun t => t.token != .placeholder) s.tokens.tokens
      rw [Array.filter_push, Array.filter_push]
      rfl
    · rfl

/-! ## §6  `AllTokensOnLineIx` transfer lemmas -/

/-- If two states share the same token stream, they share
    `AllTokensOnLineIx`. Threading record-update branches through this
    avoids dependent-index rewrite headaches: the forall-quantified
    `h` proof slot is rewritten cleanly because it's *bound*, not free. -/
theorem AllTokensOnLineIx_of_tokens_eq {s s' : ScannerStateIx input} {l : Nat}
    (h_eq : s'.tokens = s.tokens) (h_atol : AllTokensOnLineIx s l) :
    AllTokensOnLineIx s' l := by
  unfold AllTokensOnLineIx at *
  rw [h_eq]
  exact h_atol

/-- Emitting a zero-width token at `s.cursor.pos` (line `l` when
    `s.cursor.pos.line = l`) preserves `AllTokensOnLineIx`. -/
theorem AllTokensOnLineIx_emit (s : ScannerStateIx input)
    (tok : YamlToken) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx (s.emit tok) l := by
  intro i h_bound
  -- `(s.emit tok).tokens.tokens` is `s.tokens.tokens.push (new token)`.
  change ((s.tokens.tokens.push
      (IxToken.mk' s.cursor.pos tok s.cursor.pos (Nat.le_refl _) s.cursor.posBound))[i]'
    (by change i < (s.tokens.tokens.push _).size; exact h_bound)).start.line = l
  rw [Array.getElem_push]
  split
  · rename_i hlt; exact h_atol i hlt
  · -- the new token: start = s.cursor.pos, line = h_line.
    exact h_line

/-- Advancing the cursor leaves `tokens` unchanged. -/
theorem AllTokensOnLineIx_advance (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) :
    AllTokensOnLineIx s.advance l := by
  intro i h_bound
  -- `s.advance.tokens = s.tokens` (record update on cursor only).
  exact h_atol i h_bound

/-- `emitAt` with `startPos.line = l` preserves `AllTokensOnLineIx`. -/
theorem AllTokensOnLineIx_emitAt (s : ScannerStateIx input)
    (startPos : YamlPos) (tok : YamlToken)
    (hOrder : startPos.offset ≤ s.cursor.pos.offset) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_pos_line : startPos.line = l) :
    AllTokensOnLineIx (s.emitAt startPos tok hOrder) l := by
  intro i h_bound
  change ((s.tokens.tokens.push
      (IxToken.mk' startPos tok s.cursor.pos hOrder s.cursor.posBound))[i]'
    (by change i < (s.tokens.tokens.push _).size; exact h_bound)).start.line = l
  rw [Array.getElem_push]
  split
  · rename_i hlt; exact h_atol i hlt
  · exact h_pos_line

/-- `saveSimpleKeyIx` preserves `AllTokensOnLineIx`: either no token is
    added, or two placeholders are pushed at `s.cursor.pos`. -/
theorem AllTokensOnLineIx_saveSimpleKeyIx (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx (saveSimpleKeyIx s) l := by
  rcases saveSimpleKeyIx_tokens_cases s with h_eq | h_eq
  · -- Identity branch: tokens unchanged.
    exact AllTokensOnLineIx_of_tokens_eq h_eq h_atol
  · -- Two-emit branch: tokens equal those after `(s.emit .ph).emit .ph`.
    have h_step1 : AllTokensOnLineIx (s.emit YamlToken.placeholder) l :=
      AllTokensOnLineIx_emit s _ l h_atol h_line
    have h_cur1 : (s.emit YamlToken.placeholder).cursor.pos.line = l := by
      rw [emit_cursor]; exact h_line
    have h_step2 :
        AllTokensOnLineIx ((s.emit YamlToken.placeholder).emit YamlToken.placeholder) l :=
      AllTokensOnLineIx_emit _ _ l h_step1 h_cur1
    exact AllTokensOnLineIx_of_tokens_eq h_eq h_step2

/-- The `allowDirectives := false, documentEverStarted := true` record
    update doesn't touch `tokens`. -/
theorem AllTokensOnLineIx_allowDirectives (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) :
    AllTokensOnLineIx (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true } else s) l := by
  split <;> exact h_atol

/-! ## §7  `EndLineOnLineIx_saveSimpleKeyIx`

`saveSimpleKeyIx` either leaves `simpleKey` unchanged or sets it to a
fresh record with `endLine := s.cursor.pos.line` and
`cursor := s.cursor`. Both endLine and pos.line then equal the current
cursor's line. -/

theorem EndLineOnLineIx_saveSimpleKeyIx (s : ScannerStateIx input)
    (h_prev : EndLineOnLineIx s) :
    EndLineOnLineIx (saveSimpleKeyIx s) := by
  -- Unfold the target only; keep saveSimpleKeyIx as `saveSimpleKeyIx` and
  -- use the simp lemmas on cursor / simpleKey to chase.
  unfold EndLineOnLineIx
  -- Case-split on saveSimpleKeyIx structure via its definition.
  unfold saveSimpleKeyIx
  split
  · -- First branch (guard fires): identity, `simpleKey` unchanged.
    intro h; exact h_prev h
  · split
    · -- Two-emit branch: new `simpleKey` with `endLine = cursor.pos.line`,
      -- `cursor = (s.emit .placeholder).emit .placeholder).cursor = s.cursor`.
      intro _
      refine ⟨?_, ?_⟩
      · -- The new `simpleKey.endLine` is set to the cursor's line after two emits;
        -- emit preserves cursor, so this equals `s.cursor.pos.line`, which equals
        -- the post-state's cursor line (also `s.cursor.pos.line`).
        rfl
      · rfl
    · -- Third branch (else): identity.
      intro h; exact h_prev h

/-! ## §8  Per-flow-dispatcher `AllTokensOnLineIx`

Each flow-indicator scanner emits one token at `s.cursor.pos` (line
`l` by hypothesis), then advances, then updates record fields not
visible to `AllTokensOnLineIx`. -/

theorem AllTokensOnLineIx_scanFlowSequenceStartIx (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx (scanFlowSequenceStartIx s) l := by
  unfold scanFlowSequenceStartIx
  -- The record update on flowLevel/flowStack/simpleKeyStack/simpleKey/
  -- simpleKeyAllowed leaves `tokens` alone; reduce to advance ∘ emit.
  intro i h_bound
  have h_emit := AllTokensOnLineIx_emit s YamlToken.flowSequenceStart l h_atol h_line
  have h_adv := AllTokensOnLineIx_advance _ l h_emit
  exact h_adv i h_bound

theorem AllTokensOnLineIx_scanFlowMappingStartIx (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx (scanFlowMappingStartIx s) l := by
  unfold scanFlowMappingStartIx
  intro i h_bound
  have h_emit := AllTokensOnLineIx_emit s YamlToken.flowMappingStart l h_atol h_line
  have h_adv := AllTokensOnLineIx_advance _ l h_emit
  exact h_adv i h_bound

theorem AllTokensOnLineIx_scanFlowSequenceEndIx (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx (scanFlowSequenceEndIx s) l := by
  unfold scanFlowSequenceEndIx
  intro i h_bound
  have h_emit := AllTokensOnLineIx_emit s YamlToken.flowSequenceEnd l h_atol h_line
  have h_adv := AllTokensOnLineIx_advance _ l h_emit
  exact h_adv i h_bound

theorem AllTokensOnLineIx_scanFlowMappingEndIx (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx (scanFlowMappingEndIx s) l := by
  unfold scanFlowMappingEndIx
  intro i h_bound
  have h_emit := AllTokensOnLineIx_emit s YamlToken.flowMappingEnd l h_atol h_line
  have h_adv := AllTokensOnLineIx_advance _ l h_emit
  exact h_adv i h_bound

/-- `scanFlowEntryIx` follows `emit .flowEntry`, `advance`, then a
    `simpleKeyAllowed := true` update. The literal-expression shape
    matches how the dispatcher consumes it (the leading-comma guard
    case-splits *before* this expression). -/
theorem AllTokensOnLineIx_scanFlowEntry_expr (s : ScannerStateIx input) (l : Nat)
    (h_atol : AllTokensOnLineIx s l) (h_line : s.cursor.pos.line = l) :
    AllTokensOnLineIx
      ({ (s.emit YamlToken.flowEntry).advance with simpleKeyAllowed := true }) l := by
  intro i h_bound
  have h_emit := AllTokensOnLineIx_emit s YamlToken.flowEntry l h_atol h_line
  have h_adv := AllTokensOnLineIx_advance _ l h_emit
  exact h_adv i h_bound

/-- `scanDoubleQuotedIx`-quote-arm transfer for `AllTokensOnLineIx`.

The legacy `AllTokensOnLine_scanDoubleQuoted` takes
`s s' : ScannerState` plus `scanDoubleQuoted s = .ok s'`. The
indexed `scanDoubleQuotedIx` is **cursor-only** (returns
`Option (String × IxCursor input)`); the state-level wrapping in
`scanNextTokenIx_dispatchContent`'s `"`-arm is the explicit
expression:

  `{ ({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos
       (.scalar content .doubleQuoted) hOrder
     with simpleKeyAllowed := false }`

This lemma is the transfer keyed on that exact wrapper expression.
The `cursor := cAfter` record update is invisible to `tokens`; the
`simpleKeyAllowed := false` update is also invisible; only `emitAt`
adds a token, with `start = startPos` of line `l`. -/
theorem AllTokensOnLineIx_dispatchContent_quote_arm (s : ScannerStateIx input)
    (cAfter : IxCursor input) (startPos : YamlPos) (content : String)
    (hOrder :
      startPos.offset ≤ (({ s with cursor := cAfter } : ScannerStateIx input)).cursor.pos.offset)
    (l : Nat) (h_atol : AllTokensOnLineIx s l) (h_pos_line : startPos.line = l) :
    AllTokensOnLineIx
      ({ (({ s with cursor := cAfter } : ScannerStateIx input).emitAt startPos
            (YamlToken.scalar content ScalarStyle.doubleQuoted) hOrder)
          with simpleKeyAllowed := false }) l := by
  have h_atol_pre :
      AllTokensOnLineIx ({ s with cursor := cAfter } : ScannerStateIx input) l := by
    intro j h_j; exact h_atol j h_j
  have h_atol_emit :=
    AllTokensOnLineIx_emitAt
      ({ s with cursor := cAfter } : ScannerStateIx input)
      startPos
      (YamlToken.scalar content ScalarStyle.doubleQuoted)
      hOrder l h_atol_pre h_pos_line
  intro i h_bound; exact h_atol_emit i h_bound

/-! ## §9  `scanFlow{Sequence,Mapping}StartIx` clear `simpleKey.possible`

After `scanFlowSequenceStartIx` / `scanFlowMappingStartIx`, the
`simpleKey` field is set to a fresh record (defaulting to
`possible := false`). -/

theorem scanFlowSequenceStartIx_simpleKey_not_possible (s : ScannerStateIx input) :
    (scanFlowSequenceStartIx s).simpleKey.possible = false := by
  unfold scanFlowSequenceStartIx; rfl

theorem scanFlowMappingStartIx_simpleKey_not_possible (s : ScannerStateIx input) :
    (scanFlowMappingStartIx s).simpleKey.possible = false := by
  unfold scanFlowMappingStartIx; rfl

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
