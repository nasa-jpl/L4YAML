/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.FlowMonoChain

/-! # `FilteredGrowth.FirstFiltered` — Phase 3 Step
`6f.3b3.filteredgrowth.firstfiltered`

**Sub-session 1 of `.filteredgrowth`** (legacy
`Proofs/Output/EmitterScannability.lean` lines 5587–5899, ~313 LOC).

First-filtered-token lemmas for flow-content scanners (Tier-2-Turn-1).
When `scanNextTokenIx` runs in flow context with a leading content
character (`"`, `[`, or `{`), the *first* new filtered (non-`.placeholder`)
token is fully determined by that leading character. These three
theorems are building blocks for body-token characterization in the
later `.emitscans.flowvalue` / `.flowpair` sub-sessions.

Ships:
  * **§1 `scanFlowSequenceStartIx_first_filtered_token`** — `[` ↦
    `.flowSequenceStart`.
  * **§2 `scanFlowMappingStartIx_first_filtered_token`** — `{` ↦
    `.flowMappingStart`.
  * **§3 `scanDoubleQuotedIx_first_filtered_token`** — `"` ↦ some
    `.scalar _ .doubleQuoted` (content/subtype existentially quantified;
    the lemma's purpose is dispatch identification).

Plus emitter-shape helpers and a generic array prefix lemma reused by
later filtered-growth bodies:
  * `emit_first_char` / `emitList_first_char` / `emitList_toList_ne_nil`
    — pure `String`-level shape lemmas about `L4YAML.Emit.emit`. No
    indexed-scanner content; ported verbatim from legacy 5833–5871.
  * `emit_tokens_pushIx` — indexed twin of `emit_tokens_push` (legacy
    5877). Identifies the single-token push performed by
    `ScannerStateIx.emit`.
  * `Array_filter_prefix_of_raw_prefix` — generic `Array α` lemma
    (legacy 5883). Used downstream by `.perdispatch` / `.turn3`.

## Indexed simplification

The legacy `scanDoubleQuoted_first_filtered_token` proof had to bridge
through `scanDoubleQuoted_tokens_push` because the *state-level*
legacy `scanDoubleQuoted` was responsible for emitting the scalar
token. The indexed `scanDoubleQuotedIx` is **cursor-level only**:
`IxCursor input → Option (String × IxCursor input)`. The actual
`emitAt` for the scalar token happens inside
`scanNextTokenIx_dispatchContent` itself (see `Scanner/IndexedDispatch.lean`
lines 1002–1014). So this port reduces the dispatch branch directly,
extracting `(content, cAfter)` from the `scanDoubleQuotedIx` case
analysis and reading the `emitAt` shape off the dispatch body — no
separate `_tokens_push` lemma needed.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth

open L4YAML
open L4YAML.CharPredicates
open L4YAML.Indexed
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.Proofs.Indexed.EmitterScannability.Basic
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.ScannerPlainScalarValid

variable {input : String}

/-! ## §1  `scanFlowSequenceStartIx_first_filtered_token` -/

/-- After `scanNextTokenIx` with leading `[` in flow context, the
    first new filtered token is `.flowSequenceStart`. Indexed twin of
    `scanFlowSequenceStart_first_filtered_token` (legacy 5598). -/
lemma scanFlowSequenceStartIx_first_filtered_token (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'[' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.cursor.pos.col > 0)
    {s' : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok (some s')) :
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size <
      (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ∧
    (∀ (h : (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size <
            (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size),
      ((s'.tokens.tokens.filter (fun t => t.token != .placeholder))[
        (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size]'h).token
        = YamlToken.flowSequenceStart) := by
  -- Re-derive dispatch to identify s'
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '[')) :=
    scanNextTokenIx_preprocess_flow s '[' rest s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '[' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    rw [h_s_ad_def]; split <;> exact h_sk_flow
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '[' = .ok () :=
    checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '[' =
      .ok (some (scanFlowSequenceStartIx s_ad)) :=
    dispatchFlowIndicators_bracket s_ad
  have h_snt_eq := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowSequenceStartIx s_ad) '['
    h_pp h_struct h_s_ad_def h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceStartIx s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  -- s_ad's filtered tokens equal s's filtered tokens
  have h_ad_tokens_filter :
      s_ad.tokens.tokens.filter (fun t => t.token != .placeholder) =
      s.tokens.tokens.filter (fun t => t.token != .placeholder) := by
    have h_sk_filt := saveSimpleKeyIx_filter_placeholder s
    rw [h_s_ad_def]; split <;> exact h_sk_filt
  -- scanFlowSequenceStartIx s_ad's raw tokens shape:
  -- = s_ad.tokens.tokens.push (new flowSequenceStart IxToken)
  have h_fss_tokens : (scanFlowSequenceStartIx s_ad).tokens.tokens
      = s_ad.tokens.tokens.push
          (IxToken.mk' (input := input) s_ad.cursor.pos YamlToken.flowSequenceStart
              s_ad.cursor.pos (Nat.le_refl _) s_ad.cursor.posBound) := by
    show (({(s_ad.emit YamlToken.flowSequenceStart).advance with
              flowLevel := _, flowStack := _, simpleKeyStack := _,
              simpleKey := _, simpleKeyAllowed := _ } : ScannerStateIx input).tokens).tokens = _
    rfl
  rw [h_s', h_fss_tokens, Array.filter_push]
  simp only [show ((IxToken.mk' (input := input) s_ad.cursor.pos YamlToken.flowSequenceStart
                    s_ad.cursor.pos (Nat.le_refl _) s_ad.cursor.posBound).token
                  != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; rw [Array.getElem_push_eq]; rfl

/-! ## §2  `scanFlowMappingStartIx_first_filtered_token` -/

/-- After `scanNextTokenIx` with leading `{` in flow context, the
    first new filtered token is `.flowMappingStart`. Indexed twin of
    `scanFlowMappingStart_first_filtered_token` (legacy 5657). -/
lemma scanFlowMappingStartIx_first_filtered_token (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'{' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.cursor.pos.col > 0)
    {s' : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok (some s')) :
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size <
      (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ∧
    (∀ (h : (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size <
            (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size),
      ((s'.tokens.tokens.filter (fun t => t.token != .placeholder))[
        (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size]'h).token
        = YamlToken.flowMappingStart) := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '{')) :=
    scanNextTokenIx_preprocess_flow s '{' rest s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '{' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  obtain ⟨s_ad, h_s_ad_def⟩ : ∃ s_ad : ScannerStateIx input,
      s_ad = if (saveSimpleKeyIx s).allowDirectives then
        { saveSimpleKeyIx s with allowDirectives := false, documentEverStarted := true }
      else saveSimpleKeyIx s := ⟨_, rfl⟩
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    rw [h_s_ad_def]; split <;> exact h_sk_flow
  have h_check : scanNextTokenIx_checkBlockFlowIndent s_ad '{' = .ok () :=
    checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp : scanNextTokenIx_dispatchFlowIndicators s_ad '{' =
      .ok (some (scanFlowMappingStartIx s_ad)) :=
    dispatchFlowIndicators_brace s_ad
  have h_snt_eq := scanNextTokenIx_via_flow_dispatch s (saveSimpleKeyIx s) s_ad
    (scanFlowMappingStartIx s_ad) '{'
    h_pp h_struct h_s_ad_def h_check h_flow_disp
  have h_s' : s' = scanFlowMappingStartIx s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_tokens_filter :
      s_ad.tokens.tokens.filter (fun t => t.token != .placeholder) =
      s.tokens.tokens.filter (fun t => t.token != .placeholder) := by
    have h_sk_filt := saveSimpleKeyIx_filter_placeholder s
    rw [h_s_ad_def]; split <;> exact h_sk_filt
  have h_fms_tokens : (scanFlowMappingStartIx s_ad).tokens.tokens
      = s_ad.tokens.tokens.push
          (IxToken.mk' (input := input) s_ad.cursor.pos YamlToken.flowMappingStart
              s_ad.cursor.pos (Nat.le_refl _) s_ad.cursor.posBound) := by
    show (({(s_ad.emit YamlToken.flowMappingStart).advance with
              flowLevel := _, flowStack := _, simpleKeyStack := _,
              simpleKey := _, simpleKeyAllowed := _ } : ScannerStateIx input).tokens).tokens = _
    rfl
  rw [h_s', h_fms_tokens, Array.filter_push]
  simp only [show ((IxToken.mk' (input := input) s_ad.cursor.pos YamlToken.flowMappingStart
                    s_ad.cursor.pos (Nat.le_refl _) s_ad.cursor.posBound).token
                  != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; rw [Array.getElem_push_eq]; rfl

/-! ## §3  `scanDoubleQuotedIx_first_filtered_token`

The indexed `scanDoubleQuotedIx` is cursor-level. The actual `emitAt`
for the scalar token lives inside `scanNextTokenIx_dispatchContent`
itself, so the proof reduces the dispatch branch in-place and reads
the token-push shape off the `emitAt`-then-record-update body. -/

/-- After `scanNextTokenIx` with leading `"` in flow context, the first
    new filtered token is some `.scalar _ .doubleQuoted`. Content and
    subType are existentially quantified — the lemma's purpose is
    dispatch identification. Indexed twin of
    `scanDoubleQuoted_first_filtered_token` (legacy 5746). -/
lemma scanDoubleQuotedIx_first_filtered_token (s : ScannerStateIx input)
    (rest : List Char)
    (hcorr : ScannerSurfCorrIx s ⟨'"' :: rest, s.cursor.pos.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.cursor.pos.col > 0)
    {s' : ScannerStateIx input}
    (h_snt : scanNextTokenIx s = .ok (some s')) :
    (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size <
      (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size ∧
    (∀ (h : (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size <
            (s'.tokens.tokens.filter (fun t => t.token != .placeholder)).size),
      ∃ c sc, ((s'.tokens.tokens.filter (fun t => t.token != .placeholder))[
        (s.tokens.tokens.filter (fun t => t.token != .placeholder)).size]'h).token
        = YamlToken.scalar c sc) := by
  have h_pp : scanNextTokenIx_preprocess s = .ok (some (saveSimpleKeyIx s, '"')) :=
    scanNextTokenIx_preprocess_flow s '"' rest s.cursor.pos.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKeyIx s).inFlow = s.inFlow := saveSimpleKeyIx_inFlow s
  have h_sk_indent : (saveSimpleKeyIx s).currentIndent = s.currentIndent := by
    unfold ScannerStateIx.currentIndent; rw [saveSimpleKeyIx_indents]
  have h_sk_col : (saveSimpleKeyIx s).cursor.pos.col = s.cursor.pos.col := by
    rw [saveSimpleKeyIx_cursor]
  have h_struct : scanNextTokenIx_dispatchStructural (saveSimpleKeyIx s) '"' = .ok none :=
    dispatchStructural_none_flow _ _
      (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
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
  -- From h_snt + dispatch composition, dispatchContent succeeds and yields s'
  have h_dc : scanNextTokenIx_dispatchContent s_ad '"' = .ok s' := by
    cases h_dc_eq : scanNextTokenIx_dispatchContent s_ad '"' with
    | error e =>
      exfalso
      have h_snt_err := scanNextTokenIx_via_content_dispatch_error
        s (saveSimpleKeyIx s) s_ad '"' e
        h_pp h_struct h_s_ad_def h_check h_flow_none h_block_none h_dc_eq
      rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)
    | ok s_dc =>
      have h_snt_eq := scanNextTokenIx_via_content_dispatch
        s (saveSimpleKeyIx s) s_ad s_dc '"'
        h_pp h_struct h_s_ad_def h_check h_flow_none h_block_none h_dc_eq
      have h_eq2 : s' = s_dc :=
        Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
      subst h_eq2; rfl
  -- Reduce dispatchContent body to identify s' precisely. Case-split on
  -- scanDoubleQuotedIx; the `none` branch contradicts h_dc; the `some` branch
  -- yields s' as the record-update-then-emitAt-then-record-update structure.
  rcases h_dq : scanDoubleQuotedIx s_ad.cursor with _ | ⟨content, cAfter⟩
  · -- none branch: dispatchContent errors; contradicts h_dc
    exfalso
    have h_err : scanNextTokenIx_dispatchContent s_ad '"' =
        .error (.unterminatedScalar ScalarStyle.doubleQuoted s_ad.cursor.pos.line) := by
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
      · rename_i r heq; rw [h_dq] at heq; exact absurd heq (by simp)
      · rfl
    rw [h_err] at h_dc; exact absurd h_dc (by simp)
  · -- some branch: identify s' explicitly
    have h_bound : s_ad.cursor.pos.offset ≤ cAfter.pos.offset :=
      Nat.le_of_lt (scanDoubleQuotedIx_offset_lt s_ad.cursor h_dq)
    have h_red : scanNextTokenIx_dispatchContent s_ad '"' = .ok
        { ({ s_ad with cursor := cAfter }.emitAt s_ad.cursor.pos
            (YamlToken.scalar content ScalarStyle.doubleQuoted) h_bound)
          with simpleKeyAllowed := false } := by
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
        -- heq : some (content, cAfter) = some r
        injection heq with heq'
        subst heq'
        rfl
      · rename_i heq; rw [h_dq] at heq; exact absurd heq (by simp)
    have h_s'_def : s' =
        { ({ s_ad with cursor := cAfter }.emitAt s_ad.cursor.pos
            (YamlToken.scalar content ScalarStyle.doubleQuoted) h_bound)
          with simpleKeyAllowed := false } :=
      Except.ok.inj (h_dc.symm.trans h_red)
    -- s_ad's filtered tokens equal s's filtered tokens
    have h_ad_tokens_filter :
        s_ad.tokens.tokens.filter (fun t => t.token != .placeholder) =
        s.tokens.tokens.filter (fun t => t.token != .placeholder) := by
      have h_sk_filt := saveSimpleKeyIx_filter_placeholder s
      rw [h_s_ad_def]; split <;> exact h_sk_filt
    -- s'.tokens.tokens = s_ad.tokens.tokens.push (new scalar IxToken).
    -- The pushed token has start = s_ad.cursor.pos, stop = cAfter.pos
    -- (per emitAt; the inner state's cursor was updated to cAfter).
    have h_s'_tokens : s'.tokens.tokens
        = s_ad.tokens.tokens.push
            (IxToken.mk' (input := input) s_ad.cursor.pos
              (YamlToken.scalar content ScalarStyle.doubleQuoted)
              cAfter.pos h_bound cAfter.posBound) := by
      rw [h_s'_def]
      show (({ ({ s_ad with cursor := cAfter }.emitAt s_ad.cursor.pos
                  (YamlToken.scalar content ScalarStyle.doubleQuoted) h_bound)
              with simpleKeyAllowed := false } : ScannerStateIx input).tokens).tokens
        = s_ad.tokens.tokens.push _
      rfl
    rw [h_s'_tokens, Array.filter_push]
    simp only [show ((IxToken.mk' (input := input) s_ad.cursor.pos
                      (YamlToken.scalar content ScalarStyle.doubleQuoted)
                      cAfter.pos h_bound cAfter.posBound).token
                    != YamlToken.placeholder) = true from rfl, ite_true]
    rw [h_ad_tokens_filter]
    refine ⟨?_, ?_⟩
    · rw [Array.size_push]; omega
    · intro _; refine ⟨content, ScalarStyle.doubleQuoted, ?_⟩
      rw [Array.getElem_push_eq]
      rfl

/-! ## §4  Emitter shape helpers

These three lemmas are about the **string** produced by `L4YAML.Emit.emit`.
No indexed-scanner content; ported verbatim from legacy 5833–5871.

`Emit.emit` is referenced fully-qualified here to avoid ambiguity with
`ScannerStateIx.emit` (both are in scope via the broader `open L4YAML`
chain). -/

/-- The first char of `Emit.emit v` is always a non-whitespace content char. -/
lemma emit_first_char (v : YamlValue) :
    ∃ c rest', (L4YAML.Emit.emit v).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  cases v with
  | scalar s =>
    refine ⟨'"', (L4YAML.Emit.escapeString s.content).toList ++ ['"'],
            ?_, by decide, by decide, by decide⟩
    simp only [L4YAML.Emit.emit, L4YAML.Emit.emitScalar, String.toList_append]; rfl
  | sequence _ items _ _ =>
    refine ⟨'[', (L4YAML.Emit.emit.emitList items.toList).toList ++ [']'],
            ?_, by decide, by decide, by decide⟩
    simp only [L4YAML.Emit.emit, String.toList_append]; rfl
  | mapping _ pairs _ _ =>
    refine ⟨'{', (L4YAML.Emit.emit.emitPairList pairs.toList).toList ++ ['}'],
            ?_, by decide, by decide, by decide⟩
    simp only [L4YAML.Emit.emit, String.toList_append]; rfl
  | «alias» name =>
    refine ⟨'"', (L4YAML.Emit.escapeString ("*" ++ name)).toList ++ ['"'],
            ?_, by decide, by decide, by decide⟩
    simp only [L4YAML.Emit.emit, L4YAML.Emit.emitScalar, String.toList_append]; rfl

/-- The first char of `Emit.emit.emitList (v :: vs)` is the first char of `Emit.emit v`. -/
lemma emitList_first_char (v : YamlValue) (vs : List YamlValue) :
    ∃ c rest', (L4YAML.Emit.emit.emitList (v :: vs)).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  obtain ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩ := emit_first_char v
  match vs with
  | [] =>
    simp only [L4YAML.Emit.emit.emitList]
    exact ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩
  | v' :: vs' =>
    have h_el : (L4YAML.Emit.emit.emitList (v :: v' :: vs')).toList =
        (L4YAML.Emit.emit v).toList ++
          (", " ++ L4YAML.Emit.emit.emitList (v' :: vs')).toList := by
      simp [L4YAML.Emit.emit.emitList, String.toList_append, List.append_assoc]
    rw [h_el, h_emit_eq]
    exact ⟨c, ev_rest ++ (", " ++ L4YAML.Emit.emit.emitList (v' :: vs')).toList,
      by simp, h_nws, h_nlb, h_nc⟩

/-- `Emit.emit.emitList` is non-empty on non-empty input: its toList is non-nil. -/
lemma emitList_toList_ne_nil (v : YamlValue) (vs : List YamlValue) :
    (L4YAML.Emit.emit.emitList (v :: vs)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitList_first_char v vs
  rw [h_eq]; exact List.cons_ne_nil _ _

/-! ## §5  `emit_tokens_pushIx`

Identifies the single-token push performed by `ScannerStateIx.emit`.
Indexed twin of legacy `emit_tokens_push` (5877). -/

/-- After `s.emit tok`, the pushed token is the last element of the array. -/
lemma emit_tokens_pushIx (s : ScannerStateIx input) (tok : YamlToken) :
    (s.emit tok).tokens.tokens =
      s.tokens.tokens.push
        (IxToken.mk' (input := input) s.cursor.pos tok s.cursor.pos
            (Nat.le_refl _) s.cursor.posBound) := by
  unfold ScannerStateIx.emit
  rfl

/-! ## §6  `Array_filter_prefix_of_raw_prefix`

Generic `Array α` lemma: if `b` extends `a`, then `b.filter p` has
`a.filter p` as a prefix. Ported verbatim from legacy 5883. -/

/-- If `b` extends `a` (same elements at all positions `i < a.size`),
    then `b.filter p` has `a.filter p` as a prefix. -/
lemma Array_filter_prefix_of_raw_prefix {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : a.size ≤ b.size)
    (h_eq : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i]) :
    ∃ suffix, (b.filter p).toList = (a.filter p).toList ++ suffix := by
  have h_take : b.toList.take a.size = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, Array.length_toList, Nat.min_eq_left h_sz]
    · intro n hn₁ hn₂
      simp only [List.getElem_take]
      rw [Array.getElem_toList, Array.getElem_toList]
      exact h_eq n (by simpa [Array.length_toList] using hn₂)
  have h_split : b.toList = a.toList ++ b.toList.drop a.size := by
    rw [← h_take, List.take_append_drop]
  rw [Array.toList_filter, Array.toList_filter, h_split, List.filter_append]
  exact ⟨(b.toList.drop a.size).filter p, rfl⟩

end L4YAML.Proofs.Indexed.EmitterScannability.FilteredGrowth
