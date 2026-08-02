/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain.Sync.Scenarios.Preflow
import L4YAML.Proofs.Scanner.IndexedScalar

/-! # `FlowMonoChain.Sync.Scenarios.FlowScalar` — Phase 3 Step
`6f.3b3.emitscans.flowpair` (SS2, double-quoted-scalar track)

**Scenario prerequisite for `emit_scans_in_flowIx` (SS3).** The
`.flowmono.sync.scenarios` family ported the structural flow scenarios
but never the *content-dispatch* path for a double-quoted scalar
(`"…"`). The `emit_scans_in_flowIx` induction (scalar case) consumes
it, so it is ported here.

## What this file ships

  * **§1 fuel-bound length helpers** (`CharsFromOffset_length_le`,
    `escapeString_length_ge`) — tiny ports of the legacy lemmas of the
    same names (legacy 850/877). Needed to discharge the
    `input.utf8ByteSize ≥ content.length + 1` fuel obligation of the
    loop lemma. Kept local (not hoisted to `Basic`) to avoid a
    foundation-wide rebuild; `escapeString_length_ge` uses the
    already-ported `escapeString_nil` / `escapeString_cons` /
    `escapeChar_nonempty`.

  * **§2 `scanDoubleQuotedIx_escapeString_corr`** — the cursor-level
    correspondence wrapper around the heavy
    `collectDoubleQuotedLoopIx_escapeString_succeeds` (`Basic` 738).
    Given a cursor whose remaining chars are
    `'"' :: (escapeString content).toList ++ ['"'] ++ rest`,
    `scanDoubleQuotedIx` returns exactly `(content, c')` with `c'`
    sitting at `rest` (column > 0, line preserved).

  * **§3 `scanNextTokenIx_flow_scanDoubleQuoted`** — the full
    `scanNextTokenIx` scenario for a double-quoted scalar in flow
    context. Indexed twin of `scanNextToken_flow_scanDoubleQuoted`
    (legacy 3910).

## Indexed simplification vs legacy

The legacy `scanDoubleQuoted` is a *state-level* function driving
`collectDoubleQuotedLoop` and, crucially, **updates `simpleKey`** on
exit — so the legacy proof must reason about the `simpleKey.possible`
branch and re-establish `EndLineOnLine` from the freshly-set endLine.

The indexed `scanNextTokenIx_dispatchContent` for `'"'` is far simpler:
it calls the *cursor-level* `scanDoubleQuotedIx`, does a single
`emitAt` of the scalar token, and resets only `simpleKeyAllowed`. It
**never touches `simpleKey`**, so `EndLineOnLineIx s'` follows directly
from `EndLineOnLineIx s` (the saved key is unchanged and the line is
preserved). Likewise `simpleKeyStack` is untouched.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain

open L4YAML
open L4YAML.Emit
open L4YAML.CharPredicates
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.Basic
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid
open L4YAML.Proofs.CouplingBridge
open L4YAML.Surface

variable {input : String}

/-! ## §1  Fuel-bound length helpers -/

/-- Each character occupies at least one UTF-8 byte: a `CharsFromOffset`
    witness bounds its list length by the remaining byte count. Local
    port of legacy `CharsFromOffset_length_le` (legacy 850). -/
lemma CharsFromOffset_length_le {offset : Nat} {chars : List Char}
    (h : CharsFromOffset input offset chars) :
    chars.length ≤ input.utf8ByteSize - offset := by
  induction h with
  | at_end p hp => simp
  | cons p hp c rest hc hrest ih =>
    simp only [List.length_cons]
    rw [next_byteIdx, hc] at ih
    have := Char.utf8Size_pos c
    omega

/-- `escapeString` never shrinks the character count. Local port of
    legacy `escapeString_length_ge` (legacy 877), using the
    already-ported `escapeChar_nonempty`. -/
lemma escapeString_length_ge (cs : List Char) :
    (escapeString (String.ofList cs)).toList.length ≥ cs.length := by
  induction cs with
  | nil => exact Nat.zero_le _
  | cons c rest ih =>
    rw [escapeString_cons]
    simp only [String.toList_append, List.length_append, List.length_cons]
    have h1 : (escapeChar c).toList.length ≥ 1 := by
      cases h : (escapeChar c).toList with
      | nil => exact absurd h (escapeChar_nonempty c)
      | cons x xs => simp only [List.length_cons]; omega
    omega

/-! ## §2  Cursor-level double-quoted correspondence

Wraps `collectDoubleQuotedLoopIx_escapeString_succeeds` with the
opening-quote peek/advance and the fuel discharge. -/

/-- `scanDoubleQuotedIx` on a cursor whose remaining characters are
    `'"' :: (escapeString content).toList ++ ['"'] ++ rest` succeeds
    with the decoded `content` and a post-quote cursor at `rest`. -/
lemma scanDoubleQuotedIx_escapeString_corr (c : IxCursor input)
    (content : String) (rest : List Char)
    (hcorr : CursorSurfCorrIx c
      ⟨'"' :: ((escapeString content).toList ++ ['"'] ++ rest), c.pos.col⟩) :
    ∃ c', scanDoubleQuotedIx c = some (content, c')
      ∧ CursorSurfCorrIx c' ⟨rest, c'.pos.col⟩
      ∧ c'.pos.col > 0
      ∧ c'.pos.line = c.pos.line := by
  have ⟨h_peek, h_lt⟩ := peek_of_chars_consIx c '"'
    ((escapeString content).toList ++ ['"'] ++ rest) c.pos.col hcorr
  have hcorr_adv : CursorSurfCorrIx c.advance
      ⟨(escapeString content).toList ++ ['"'] ++ rest, c.pos.col + 1⟩ :=
    advance_non_newline_corrIx c '"'
      ((escapeString content).toList ++ ['"'] ++ rest) hcorr h_lt (by decide) (by decide)
  have h_col_adv : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_adv.col_eq
  rw [h_col_adv] at hcorr_adv
  -- Fuel: input.utf8ByteSize ≥ content.toList.length + 1.
  have h_len := CharsFromOffset_length_le hcorr.chars_from
  have h_esc := escapeString_length_ge content.toList
  rw [String.ofList_toList] at h_esc
  have h_fuel : input.utf8ByteSize ≥ content.toList.length + 1 := by
    simp only [List.length_cons, List.length_append] at h_len
    omega
  have h_corr_loop : CursorSurfCorrIx c.advance
      ⟨(escapeString (String.ofList content.toList)).toList ++ ['"'] ++ rest,
        c.advance.pos.col⟩ := by
    rw [String.ofList_toList]; exact hcorr_adv
  obtain ⟨c', h_loop, hcorr_c', h_col_c', h_line_c'⟩ :=
    collectDoubleQuotedLoopIx_escapeString_succeeds c.advance content.toList rest ""
      input.utf8ByteSize h_corr_loop h_fuel
  have h_content_eq : ("" : String) ++ String.ofList content.toList = content := by
    apply String.ext; simp
  refine ⟨c', ?_, hcorr_c', h_col_c', ?_⟩
  · unfold scanDoubleQuotedIx
    rw [h_peek]
    simp only [show isDoubleQuoteBool '"' = true from by decide, if_true]
    rw [h_loop, h_content_eq]
  · rw [h_line_c']
    exact advance_line_of_peekIx c '"' h_lt h_peek (by decide) (by decide)

/-! ## §3  `scanNextTokenIx_flow_scanDoubleQuoted` -/

/-- Full `scanNextTokenIx` for a double-quoted scalar `"…"` in flow
    context. Indexed twin of `scanNextToken_flow_scanDoubleQuoted`
    (legacy 3910). -/
lemma scanNextTokenIx_flow_scanDoubleQuoted (s : ScannerStateIx input)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorrIx s
      ⟨'"' :: ((escapeString content).toList ++ ['"'] ++ rest), s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.cursor.pos.col > 0)
    (h_atol : AllTokensOnLineIx s s.cursor.pos.line)
    (h_endline : EndLineOnLineIx s)
    (h_dp : s.directivesPresent = false) :
    ∃ s', scanNextTokenIx s = .ok (some s')
      ∧ ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.cursor.pos.col > 0
      ∧ (∀ t, lastRealTokenValIx? s'.tokens = some t →
          t ≠ YamlToken.flowSequenceStart ∧ t ≠ YamlToken.flowMappingStart
          ∧ t ≠ YamlToken.flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.cursor.pos.line = s.cursor.pos.line
      ∧ AllTokensOnLineIx s' s'.cursor.pos.line
      ∧ EndLineOnLineIx s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack := by
  -- ── Dispatch composition prefix (mirror `scanDoubleQuotedIx_first_filtered_token`)
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '"')) :=
    scanNextTokenIx_preprocess_flow s '"'
      ((escapeString content).toList ++ ['"'] ++ rest) s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '"' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    rw [h_s_ad_def]; split <;> exact h_sk_flow
  have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '"' = .ok () :=
    checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
  have h_flow_none : scanNextTokenIx_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _
      (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_block_none : scanNextTokenIx_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- ── s_ad field equalities
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_explicitKeyLine s
  have h_ad_cursor : s_ad.cursor = s.cursor := by
    rw [h_s_ad_def]; split <;> exact saveSimpleKeyIx_cursor s
  have h_ad_line : s_ad.cursor.pos.line = s.cursor.pos.line := by rw [h_ad_cursor]
  have h_ad_tokens : s_ad.tokens = (saveSimpleKeyIx s).tokens := by
    rw [h_s_ad_def]; split <;> rfl
  have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    have h1 : (saveSimpleKeyIx s).simpleKeyStack = s.simpleKeyStack :=
      saveSimpleKeyIx_preserves_simpleKeyStack s
    rw [h_s_ad_def]; split <;> exact h1
  have h_ad_simpleKey : s_ad.simpleKey = (saveSimpleKeyIx s).simpleKey := by
    rw [h_s_ad_def]; split <;> rfl
  -- ── s_ad surface correspondence (chars unchanged from s)
  have h_ad_corr : ScannerSurfCorrIx s_ad
      ⟨'"' :: ((escapeString content).toList ++ ['"'] ++ rest), s_ad.cursor.pos.col⟩ := by
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_ad_cursor]; exact hcorr.chars_from
    · rw [h_ad_cursor]; exact hcorr.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ad_ids ▸ hi
      have heq : s_ad.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  -- ── cursor-level: identify `content` and `cAfter` at `rest`
  have h_ad_cursor_corr : CursorSurfCorrIx s_ad.cursor
      ⟨'"' :: ((escapeString content).toList ++ ['"'] ++ rest), s_ad.cursor.pos.col⟩ :=
    ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.input_prefix⟩
  obtain ⟨cAfter, h_dq, hcorr_cAfter, h_col_cAfter, h_line_cAfter⟩ :=
    scanDoubleQuotedIx_escapeString_corr s_ad.cursor content rest h_ad_cursor_corr
  have h_bound : s_ad.cursor.pos.offset ≤ cAfter.pos.offset :=
    Nat.le_of_lt (scanDoubleQuotedIx_offset_lt s_ad.cursor h_dq)
  -- ── the explicit result state
  let s' : ScannerStateIx input :=
    { ({ s_ad with cursor := cAfter }.emitAt s_ad.cursor.pos
        (YamlToken.scalar content ScalarStyle.doubleQuoted) h_bound)
      with simpleKeyAllowed := false }
  have h_s'_cursor : s'.cursor = cAfter := rfl
  have h_s'_fl : s'.flowLevel = s_ad.flowLevel := rfl
  have h_s'_dp : s'.directivesPresent = s_ad.directivesPresent := rfl
  have h_s'_ids : s'.indents = s_ad.indents := rfl
  have h_s'_ek : s'.explicitKeyLine = s_ad.explicitKeyLine := rfl
  have h_s'_sk : s'.simpleKey = s_ad.simpleKey := rfl
  have h_s'_stack : s'.simpleKeyStack = s_ad.simpleKeyStack := rfl
  have h_s'_ska : s'.simpleKeyAllowed = false := rfl
  have h_s'_tokens : s'.tokens = s_ad.tokens.push
      (IxToken.mk' (input := input) s_ad.cursor.pos
        (YamlToken.scalar content ScalarStyle.doubleQuoted) cAfter.pos h_bound cAfter.posBound) :=
    rfl
  -- ── dispatchContent reduces to s'
  have h_dc : scanNextTokenIx_dispatchContent s_ad '"' = .ok s' := by
    unfold scanNextTokenIx_dispatchContent
    simp only [bind, Except.bind, pure, Pure.pure, Except.pure,
      show ('"' == '&') = false from by decide,
      show ('"' == '*') = false from by decide,
      show ('"' == '!') = false from by decide,
      show ('"' == '|') = false from by decide,
      show ('"' == '>') = false from by decide,
      show ('"' == '"') = true from by decide,
      Bool.or_self, Bool.false_eq_true, ↓reduceIte]
    split
    · rename_i r heq
      rw [h_dq] at heq
      injection heq with heq'
      subst heq'
      rfl
    · rename_i heq; rw [h_dq] at heq; exact absurd heq (by simp)
  have h_snt : scanNextTokenIx s = .ok (some s') :=
    scanNextTokenIx_via_content_dispatch s (saveSimpleKeyIx s) s_ad s' '"'
      h_pp h_struct h_s_ad_def h_check h_flow_none h_block_none h_dc
      ((saveSimpleKeyIx_directivesPresent s).trans h_dp)
  -- ── line equality (used by several conjuncts)
  have h_s'_line_eq : s'.cursor.pos.line = s.cursor.pos.line := by
    rw [h_s'_cursor, h_line_cAfter]; exact h_ad_line
  have h_ids_eq : s'.indents = s.indents := h_s'_ids.trans h_ad_ids
  refine ⟨s', h_snt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- ScannerSurfCorrIx s' ⟨rest, s'.cursor.pos.col⟩
    refine ⟨?_, rfl, ?_, ?_⟩
    · rw [h_s'_cursor]; exact hcorr_cAfter.chars_from
    · rw [h_s'_cursor]; exact hcorr_cAfter.input_prefix
    · intro i hi h0
      have hi' : i < s.indents.size := h_ids_eq ▸ hi
      have heq : s'.indents[i]'hi = s.indents[i]'hi' := by congr 1
      rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0
  · rw [h_s'_fl]; exact h_ad_fl
  · rw [h_s'_dp]; exact h_ad_dp
  · exact h_ids_eq
  · rw [h_s'_ek]; exact h_ad_ek
  · rw [h_s'_cursor]; exact h_col_cAfter
  · -- lastRealTokenValIx? ⇒ not a flow opener / entry
    have h_last_eq : lastRealTokenValIx? s'.tokens
        = some (YamlToken.scalar content ScalarStyle.doubleQuoted) := by
      rw [h_s'_tokens]
      exact lastRealTokenValIx_push_non_ph _ _ nofun
    intro t ht
    rw [h_last_eq] at ht
    injection ht with ht; subst ht
    exact ⟨nofun, nofun, nofun⟩
  · exact h_s'_ska
  · exact h_s'_line_eq
  · -- AllTokensOnLineIx s' s'.cursor.pos.line
    rw [h_s'_line_eq]
    have h_atol_sk : AllTokensOnLineIx (saveSimpleKeyIx s) s.cursor.pos.line :=
      AllTokensOnLineIx_saveSimpleKeyIx s s.cursor.pos.line h_atol rfl
    have h_atol_ad : AllTokensOnLineIx s_ad s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq h_ad_tokens h_atol_sk
    have h_atol_sAfter :
        AllTokensOnLineIx ({ s_ad with cursor := cAfter } : ScannerStateIx input)
          s.cursor.pos.line :=
      AllTokensOnLineIx_of_tokens_eq rfl h_atol_ad
    have h_atol_emit :
        AllTokensOnLineIx (({ s_ad with cursor := cAfter } : ScannerStateIx input).emitAt
          s_ad.cursor.pos (YamlToken.scalar content ScalarStyle.doubleQuoted) h_bound)
          s.cursor.pos.line :=
      AllTokensOnLineIx_emitAt _ s_ad.cursor.pos _ h_bound s.cursor.pos.line
        h_atol_sAfter h_ad_line
    exact AllTokensOnLineIx_of_tokens_eq rfl h_atol_emit
  · -- EndLineOnLineIx s' (simpleKey unchanged, line preserved)
    have h_s_ad_endline : EndLineOnLineIx s_ad := by
      have h_sk_endline : EndLineOnLineIx (saveSimpleKeyIx s) :=
        EndLineOnLineIx_saveSimpleKeyIx s h_endline
      intro h_poss
      rw [h_ad_simpleKey] at h_poss
      have ⟨h1, h2⟩ := h_sk_endline h_poss
      refine ⟨?_, ?_⟩
      · rw [h_ad_simpleKey, h1]
        show (saveSimpleKeyIx s).cursor.pos.line = s_ad.cursor.pos.line
        rw [saveSimpleKeyIx_cursor, h_ad_cursor]
      · rw [h_ad_simpleKey, h2]
        show (saveSimpleKeyIx s).cursor.pos.line = s_ad.cursor.pos.line
        rw [saveSimpleKeyIx_cursor, h_ad_cursor]
    intro h_poss
    rw [h_s'_sk] at h_poss
    have ⟨h1, h2⟩ := h_s_ad_endline h_poss
    have h_line' : s'.cursor.pos.line = s_ad.cursor.pos.line := by
      rw [h_s'_cursor, h_line_cAfter]
    refine ⟨?_, ?_⟩
    · rw [h_s'_sk, h1, h_line']
    · rw [h_s'_sk, h2, h_line']
  · rw [h_s'_stack]; exact h_ad_stack

end L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
