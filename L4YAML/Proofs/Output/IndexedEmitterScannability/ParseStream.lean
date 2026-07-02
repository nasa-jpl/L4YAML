/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Output.IndexedEmitterScannability.EmitScans
import L4YAML.Proofs.Parser.IndexedComposition
import L4YAML.Proofs.Parser.IndexedGrammable
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness

/-! # `IndexedEmitterScannability.ParseStream` — Phase 3 Step 6f.3b3.parsestream

**Status**: LANDED 2026-05-28 — §4 Full Pipeline + §5.2 Scanner content
preservation. Indexed twins of legacy `EmitterScannability.lean` lines
8400–8489 (§4) and 8531–8874 (§5.2).

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§4 Full Pipeline: Emit → Scan → Parse** (legacy lines 8400–8489):
    `parseStreamLoop_single_docIx`, `emit_parsed_grammableIx`.

  - **§5.2 Scanner content preservation** (legacy lines 8531–8874):
    `scanFilteredIx_emitScalar_content`, `scanFilteredIx_emitScalar_vals`,
    `parseDirectives_skipIx`, `parseNodeProperties_skipIx`,
    `parseStream_three_tokens_scalarIx`, `parseYamlRawIx_emitScalar_value`.

These proofs bridge the scanner-acceptance result
(`emit_produces_valid_yamlIx` from `EmitScans.lean`) to the parser
output, showing that the recovered AST matches the original value
via the `compose` content-fidelity layer consumed by the `.roundtrip`
cluster.

## Phase 3 Step 6f cutover

See `Basic.lean` for the directory-wide cutover plan.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.ParseStream

open L4YAML
open L4YAML.Grammar
open L4YAML.Indexed
open L4YAML.Emit
open L4YAML.Scanner.Indexed
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.TokenParser.Indexed
open L4YAML.Proofs.Indexed.EmitterScannability.EmitScans
open L4YAML.Proofs.Indexed.EmitterScannability.FlowMonoChain
open L4YAML.Proofs.Indexed.EmitterScannability.ScanChain
open L4YAML.Proofs.Indexed.Composition
open L4YAML.Proofs.Indexed.Grammable
open L4YAML.Proofs.Indexed.ScannerCorrectness

/-! ## §4  Full Pipeline: Emit → Scan → Parse

Combining scanner acceptance (Step 1, `emit_produces_valid_yamlIx`) with
parser acceptance (Step 2).

### Step 2 Architecture

Step 1 gives us `scanFilteredIx (emit v) = .ok tokens`. Step 2 must show
that `parseStreamIx` also succeeds on those tokens. The key argument:

1. **Stream boundaries**: `scanFilteredIx` always produces `streamStart` as
   the first token and `streamEnd` as the last (by scanner construction).
2. **Single implicit document**: The emitter produces no `---`/`...` markers
   and no directives, so `parseStreamLoop` in `.initial` state sees bare
   content → enters `parseDocument` with no directive overhead.
3. **No bare-document violation**: After the single document is parsed, only
   `streamEnd` remains. `StreamState.validNextToken .afterDocument .streamEnd`
   is always `true`, so `invalidBareDocument` cannot fire.
4. **Parser dispatch succeeds**: `parseNode` dispatches on token type.
5. **Fuel sufficiency**: `parseStreamIx` allocates `tokens.size` fuel.
6. **No semantic errors**: The emitter produces no anchors / aliases / tags
   / block content, so no `duplicateAnchor` / `undefinedAlias` / etc.
-/

/-- **`parseStreamLoop` state machine — single implicit document**: if the
    parser sees content (not `streamEnd`), `parseDocument` succeeds and
    leaves `peek?` at `streamEnd`; then `parseStreamLoop` produces exactly
    one document. Indexed twin of legacy `parseStreamLoop_single_doc`
    (line 8433). -/
theorem parseStreamLoop_single_docIx {input : String}
    (ps : ParseStateIx input) (fuel : Nat) (h_fuel : fuel ≥ 2)
    (tok : YamlToken) (h_peek : ps.peek? = some tok) (h_not_se : tok ≠ .streamEnd)
    (doc : YamlDocument) (ps' : ParseStateIx input)
    (h_doc : parseDocument ps = .ok (doc, ps'))
    (h_peek' : ps'.peek? = some .streamEnd) :
    parseStreamLoop ps #[] .initial fuel = .ok #[doc] := by
  -- Two iterations: first parses document, second sees streamEnd and returns.
  cases fuel with
  | zero => omega
  | succ fuel' => cases fuel' with
    | zero => omega
    | succ f =>
      -- First iteration: unfold parseStreamLoop, resolve fuel match
      unfold parseStreamLoop; dsimp only []
      rw [h_peek]
      -- Case-split by YamlToken constructor to resolve the compiled match.
      -- .streamEnd is impossible (contradicts h_not_se); all others take catch-all.
      cases tok
      <;> first | exact absurd rfl h_not_se | skip
      -- All remaining content goals: identical proof structure.
      all_goals (
        dsimp only []
        simp only [StreamState.validNextToken, Bool.not_true]
        rw [h_doc]; dsimp only []
        -- Post-document state: clear anchors/nodePositions/currentPath. The
        -- `peek?` projection depends only on `tokens` and `pos`, both unchanged.
        have h_peek'_r : ({ ps' with anchors := #[], nodePositions := #[],
                                     currentPath := #[] } : ParseStateIx input).peek?
            = some .streamEnd := h_peek'
        simp only [ParseStateIx.tryConsume, h_peek'_r,
                   show (BEq.beq YamlToken.streamEnd YamlToken.documentEnd) = false
                     from by decide]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [parseStreamLoop, h_peek'_r]
        -- Both if-branches collapse to the same `.ok #[doc]` result.
        split <;> rfl)

/-- **Grammability preservation**: the parsed output of emitter output is
    grammable. Follows from `parseStreamIx_output_grammable` applied to
    the scan+parse decomposition. Indexed twin of legacy
    `emit_parsed_grammable` (line 8472). -/
theorem emit_parsed_grammableIx (v : YamlValue)
    (docs : Array YamlDocument)
    (h : parseYamlIx (emit v) = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable doc.value false := by
  simp only [parseYamlIx] at h
  split at h
  · rename_i raw_docs h_raw
    injection h with h_eq
    have ⟨tokens, h_scan, h_parse⟩ := parseYamlRawIx_ok_decompose (emit v) raw_docs h_raw
    have h_fpsv := scanFilteredIx_FlowAwarePSVIx (emit v) tokens h_scan
    have h_matched := scanFilteredIx_FlowBracketsMatchedIx (emit v) tokens h_scan
    have h_gram := parseStreamIx_output_grammable tokens raw_docs h_fpsv h_matched h_parse
    intro doc hdoc
    rw [← h_eq] at hdoc
    simp only [Array.toList_map] at hdoc
    obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
    subst h_compose_eq
    exact h_gram raw_doc h_raw_mem
  · simp at h

/-! ## §5.2  Scanner content preservation

The scanner's double-quoted collector recovers the original content string
from the emitter's escape-encoded output. This bridges
`SS2/scanNextTokenIx_emitScalar_init`'s filtered-token equality (the §3.2
helper's 7th conjunct, added in this session — see Reflection 147) with the
parser's three-token trace through `parseStreamIx`. The downstream consumer
is the `.roundtrip` cluster: with the content recovered exactly, the
canonical roundtrip `parseYamlIx ∘ emit = id` (modulo stripping) follows.
-/

/-! ### Helper: parser-state directive/property skip lemmas -/

/-- When `parseDirectives` sees a non-directive token, it returns immediately
    with empty directives and unchanged state. The `for _ in [:fuel] do`
    loop breaks on the first iteration. Indexed twin of legacy
    `parseDirectives_skip` (line 8677). -/
theorem parseDirectives_skipIx {input : String} (ps : ParseStateIx input)
    (h : match ps.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True) :
    parseDirectives ps = (#[], ps) := by
  unfold parseDirectives
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize ps.tokens.size - ps.pos = fuel
  cases fuel with
  | zero =>
    simp only [List.range', List.forIn_nil]
    rfl
  | succ n =>
    simp only [List.range'_succ, List.forIn_cons, pure, bind]
    split
    · rename_i minor h_done
      split at h_done
      · cases h_done
      · cases h_done
      · cases h_done; rfl
    · rename_i b h_yield
      split at h_yield
      · exfalso; revert h; simp_all
      · exfalso; revert h; simp_all
      · cases h_yield

set_option maxHeartbeats 3200000 in
/-- When `parseNodeProperties` sees a non-anchor/tag token, it returns
    immediately with empty properties and unchanged state. Indexed twin of
    legacy `parseNodeProperties_skip` (`ParserWellBehaved.lean:4692`). -/
theorem parseNodeProperties_skipIx {input : String} (ps : ParseStateIx input)
    (h : match ps.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True) :
    parseNodeProperties ps = .ok ({}, ps) := by
  unfold parseNodeProperties
  dsimp only []
  simp only [Std.Legacy.Range.forIn_eq_forIn_range',
             Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one,
             show List.range' 0 2 1 = 0 :: List.range' 1 1 1 from by decide,
             List.forIn_cons, bind, Except.bind, pure, Except.pure]
  cases hpk : ps.peek?
  case none => simp_all
  case some tok => cases tok <;> simp_all

/-! ### Scanner content preservation: scalar emitter

`emitScalar content` is scanned into exactly three filtered tokens —
`streamStart`, a `scalar content .doubleQuoted` carrying the original
content, and `streamEnd`. Composition: SS2's
`scanNextTokenIx_emitScalar_init` (§3.2, EmitScans.lean) + the
SS2-wrapper `scan_accepts_emitScalarIx` (§3.3) + `scanFilteredIx_of_chain_eq`
(`FlowMonoChain/Sync/Invariant.lean` §5).
-/

/-- **Scanner produces the exact 3-token filtered stream** for a
    `emitScalar` input. Bundles three IxToken witnesses (with their
    `.token` projections fixed) and the explicit `scanFilteredIx`
    equality. Indexed analog of the equality embedded in legacy
    `scanFiltered_emitScalar_vals`'s `h_filt_full` step (line 8647). -/
theorem scanFilteredIx_emitScalar_eq (content : String) :
    ∃ (ss_ix : Indexed.IxToken (emitScalar content))
      (tok_scalar : Indexed.IxToken (emitScalar content))
      (se_ix : Indexed.IxToken (emitScalar content)),
      ss_ix.token = YamlToken.streamStart
      ∧ tok_scalar.token = YamlToken.scalar content ScalarStyle.doubleQuoted
      ∧ se_ix.token = YamlToken.streamEnd
      ∧ scanFilteredIx (emitScalar content)
          = .ok ⟨#[ss_ix, tok_scalar, se_ix]⟩ := by
  -- Pull the full SS2/SS3 chain into focus.
  obtain ⟨s₁, h_snt1, h_peek1, h_flow1, h_dp1, h_ids1, tok_scalar,
          h_tok_val, h_filt1⟩ := scanNextTokenIx_emitScalar_init content
  have h_size := emitScalar_utf8ByteSize_ge content
  have h_fuel : ((emitScalar content).utf8ByteSize + 1) * 4 ≥ 2 := by omega
  -- BOM check: first char is '"', not '﻿'.
  have h_toList : (emitScalar content).toList =
      '"' :: ((escapeString content).toList ++ ['"']) := by
    rw [emitScalar_toList]; rfl
  have h_corr_init : ScannerSurfCorrIx
      (input := emitScalar content)
      (ScannerStateIx.mk' (emitScalar content))
      ⟨'"' :: ((escapeString content).toList ++ ['"']), 0⟩ := by
    have h := initial_corrIx (emitScalar content)
    rw [h_toList] at h; exact h
  have ⟨h_pk_init, _⟩ := peek_of_chars_consIx_state
    (ScannerStateIx.mk' (emitScalar content)) '"'
    ((escapeString content).toList ++ ['"']) 0 h_corr_init
  have h_no_bom : (ScannerStateIx.mk' (emitScalar content)).peek? ≠ some '﻿' := by
    rw [h_pk_init]; decide
  -- EOF step at s₁.
  have h_snt2 : scanNextTokenIx s₁ = .ok none := scanNextTokenIx_eof s₁ h_peek1
  -- Two-step chain: streamStart-emit → s₁ → EOF.
  have h_chain : ScanChainIx
      ((ScannerStateIx.mk' (emitScalar content)).emit YamlToken.streamStart) 1 s₁ :=
    ScanChainIx.single h_snt1
  -- unwindIndentsIx at s₁ is identity (indents = singleton sentinel; size = 1).
  have h_sz1 : s₁.indents.size = 1 := by rw [h_ids1]; rfl
  have h_uwi : unwindIndentsIx s₁ (-1) = s₁ := by
    unfold unwindIndentsIx
    rw [h_sz1]
    show unwindIndentsLoopIx s₁ (-1) 1 = s₁
    unfold unwindIndentsLoopIx
    rw [h_sz1]
    -- Goal: (if ... && decide ((1:Nat) > 1) ... then _ else s₁) = s₁.
    -- decide (1 > 1) = false; AND with false collapses.
    have h_false : decide ((1 : Nat) > 1) = false := by decide
    rw [h_false, Bool.and_false]
    rfl
  -- Apply scanFilteredIx_of_chain_eq for the explicit filtered token equality.
  have h_eq := scanFilteredIx_of_chain_eq (emitScalar content)
    _ s₁ 1 rfl h_no_bom h_chain h_snt2 h_flow1 h_dp1 (by omega)
  -- Compute the filtered array step by step.
  -- Step 1: substitute unwindIndentsIx s₁ (-1) = s₁ in h_eq.
  rw [h_uwi] at h_eq
  -- Step 2: explicit streamEnd IxToken; filter_push since streamEnd ≠ placeholder.
  let se_ix : Indexed.IxToken (emitScalar content) :=
    Indexed.IxToken.mk' s₁.cursor.pos YamlToken.streamEnd s₁.cursor.pos
      (Nat.le_refl _) s₁.cursor.posBound
  have h_se_eq : (s₁.emit YamlToken.streamEnd).tokens.tokens
      = s₁.tokens.tokens.push se_ix := rfl
  rw [h_se_eq, Array.filter_push] at h_eq
  have h_se_keep : (se_ix.token != YamlToken.placeholder) = true := rfl
  rw [if_pos h_se_keep] at h_eq
  -- Step 3: substitute h_filt1 (s₁.tokens.filter = ((mk' input).emit ss).tokens.filter.push tok_scalar).
  rw [h_filt1] at h_eq
  -- Step 4: explicit streamStart IxToken; (mk' input).tokens.tokens = #[], filter empty = empty.
  let ss_ix : Indexed.IxToken (emitScalar content) :=
    Indexed.IxToken.mk' (ScannerStateIx.mk' (emitScalar content)).cursor.pos
      YamlToken.streamStart
      (ScannerStateIx.mk' (emitScalar content)).cursor.pos
      (Nat.le_refl _) (ScannerStateIx.mk' (emitScalar content)).cursor.posBound
  have h_ss_unfold : ((ScannerStateIx.mk' (emitScalar content)).emit
      YamlToken.streamStart).tokens.tokens.filter (fun t => t.token != YamlToken.placeholder)
      = #[ss_ix] := by
    show ((#[] : Array _).push ss_ix).filter _ = #[ss_ix]
    rfl
  rw [h_ss_unfold] at h_eq
  -- Now h_eq : scanFilteredIx (emitScalar content) = .ok ⟨(#[ss_ix].push tok_scalar).push se_ix⟩
  refine ⟨ss_ix, tok_scalar, se_ix, rfl, h_tok_val, rfl, ?_⟩
  rw [h_eq]
  rfl

/-- **Scanner content preservation**: scanning `emitScalar content` produces
    a token stream where the scalar token's value equals the original
    content. Indexed twin of legacy `scanFiltered_emitScalar_content`
    (line 8545). -/
theorem scanFilteredIx_emitScalar_content (content : String)
    (tokens : Indexed.TokenStream (emitScalar content))
    (h_scan : scanFilteredIx (emitScalar content) = .ok tokens) :
    ∃ i, i < tokens.size ∧
      tokens.tokens[i]!.token = YamlToken.scalar content ScalarStyle.doubleQuoted := by
  obtain ⟨ss_ix, tok_scalar, se_ix, _, h_tok_val, _, h_eq⟩ :=
    scanFilteredIx_emitScalar_eq content
  have h_tokens_eq : tokens = ⟨#[ss_ix, tok_scalar, se_ix]⟩ :=
    Except.ok.inj (h_scan.symm.trans h_eq)
  have h_arr : tokens.tokens = #[ss_ix, tok_scalar, se_ix] :=
    congrArg Indexed.TokenStream.tokens h_tokens_eq
  have h_sz : tokens.size = 3 := by show tokens.tokens.size = 3; rw [h_arr]; rfl
  refine ⟨1, ?_, ?_⟩
  · omega
  · rw [h_arr]
    show tok_scalar.token = _
    exact h_tok_val

/-- **Token structure characterization**: the filtered scan of `emitScalar
    content` produces exactly 3 tokens: `streamStart`,
    `scalar content .doubleQuoted`, `streamEnd`. Indexed twin of legacy
    `scanFiltered_emitScalar_vals` (line 8607). -/
theorem scanFilteredIx_emitScalar_vals (content : String)
    (tokens : Indexed.TokenStream (emitScalar content))
    (h_scan : scanFilteredIx (emitScalar content) = .ok tokens) :
    tokens.size = 3
    ∧ tokens.tokens[0]!.token = YamlToken.streamStart
    ∧ tokens.tokens[1]!.token = YamlToken.scalar content ScalarStyle.doubleQuoted
    ∧ tokens.tokens[2]!.token = YamlToken.streamEnd := by
  obtain ⟨ss_ix, tok_scalar, se_ix, h_ss_val, h_tok_val, h_se_val, h_eq⟩ :=
    scanFilteredIx_emitScalar_eq content
  have h_tokens_eq : tokens = ⟨#[ss_ix, tok_scalar, se_ix]⟩ :=
    Except.ok.inj (h_scan.symm.trans h_eq)
  have h_arr : tokens.tokens = #[ss_ix, tok_scalar, se_ix] :=
    congrArg Indexed.TokenStream.tokens h_tokens_eq
  refine ⟨?_, ?_, ?_, ?_⟩
  · show tokens.tokens.size = 3; rw [h_arr]; rfl
  · rw [h_arr]; exact h_ss_val
  · rw [h_arr]; exact h_tok_val
  · rw [h_arr]; exact h_se_val

/-! ### Parser trace on the three-token scalar stream -/

set_option maxHeartbeats 6400000 in
/-- **Parser trace on three-token scalar stream**: given a token array
    with values `[streamStart, scalar content .doubleQuoted, streamEnd]`,
    `parseStreamIx` produces exactly one document whose value is
    `YamlValue.scalar { content := content, style := .doubleQuoted }`.
    Indexed twin of legacy `parseStream_three_tokens_scalar` (line 8710). -/
theorem parseStream_three_tokens_scalarIx {input : String} (content : String)
    (tokens : Indexed.TokenStream input)
    (h_sz : tokens.size = 3)
    (h_t0 : tokens.tokens[0]!.token = YamlToken.streamStart)
    (h_t1 : tokens.tokens[1]!.token = YamlToken.scalar content ScalarStyle.doubleQuoted)
    (h_t2 : tokens.tokens[2]!.token = YamlToken.streamEnd) :
    ∃ (docs : Array YamlDocument),
      parseStreamIx tokens = .ok docs ∧ docs.size = 1 ∧
      docs[0]!.value = .scalar (Scalar.mk content .doubleQuoted none none none) := by
  have h_sz' : tokens.tokens.size = 3 := h_sz
  have h0 : (0 : Nat) < tokens.tokens.size := by omega
  have h1 : (1 : Nat) < tokens.tokens.size := by omega
  have h2 : (2 : Nat) < tokens.tokens.size := by omega
  -- Convert getElem! into getElem-with-bounds.
  have h_gei : ∀ (i : Nat) (hi : i < tokens.tokens.size),
      tokens.tokens[i]!.token = tokens.tokens[i].token := by
    intro i hi; simp [getElem!_pos, hi]
  have h_t1' : tokens.tokens[1].token = YamlToken.scalar content .doubleQuoted := by
    rw [← h_gei 1 h1]; exact h_t1
  have h_t2' : tokens.tokens[2].token = YamlToken.streamEnd := by
    rw [← h_gei 2 h2]; exact h_t2
  -- Token-stream peek? at position i, in terms of getElem (when in bounds).
  have h_peek_get : ∀ (i : Nat) (hi : i < tokens.tokens.size),
      ({ tokens := tokens, pos := i } : ParseStateIx input).peek?
        = some tokens.tokens[i].token := by
    intro i hi
    show ((tokens.get? i).map (·.token)) = some _
    rw [show tokens.get? i = some tokens.tokens[i] from by
      unfold Indexed.TokenStream.get?; rw [Array.getElem?_eq_getElem hi]]
    rfl
  -- Step 1: Unfold parseStreamIx and dispatch expect .streamStart
  unfold parseStreamIx
  simp only [bind, Except.bind]
  unfold ParseStateIx.expect
  rw [h_peek_get 0 h0]
  rw [← h_gei 0 h0, h_t0]
  simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
             ↓reduceIte]
  -- After expect step, introduce ps1 = advance of initial state.
  let ps1 : ParseStateIx input := ({ tokens := tokens } : ParseStateIx input).advance
  show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
    docs.size = 1 ∧ docs[0]!.value = .scalar (Scalar.mk content .doubleQuoted none none none)
  -- peek? at ps1 (pos = 1) = scalar.
  have h_peek1 : ps1.peek? = some (YamlToken.scalar content .doubleQuoted) := by
    show ((tokens.get? 1).map (·.token)) = _
    rw [show tokens.get? 1 = some tokens.tokens[1] from by
      unfold Indexed.TokenStream.get?; rw [Array.getElem?_eq_getElem h1]]
    rw [Option.map_some]; show some tokens.tokens[1].token = _; rw [h_t1']
  have h_peek_not_dir : match ps1.peek? with
      | some (.versionDirective _ _) | some (.tagDirective _ _) => False
      | _ => True := by rw [h_peek1]; trivial
  have h_peek_not_anctag : match ps1.peek? with
      | some (.anchor _) | some (.tag _ _) => False
      | _ => True := by rw [h_peek1]; trivial
  -- parseDirectives and prepareDocumentState
  have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skipIx ps1 h_peek_not_dir
  have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
    unfold prepareDocumentState
    simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
    have h_th : { ps1 with tagHandles := #[] } = ps1 := by
      simp [ps1, ParseStateIx.advance]
    rw [h_th, h_peek1]
    unfold ParseStateIx.tryConsume
    rw [h_peek1]; simp
  -- parseNodeProperties skip
  have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
    parseNodeProperties_skipIx ps1 h_peek_not_anctag
  -- parseNode reduces to the scalar branch.
  have h_parseNode : parseNode ps1 (4 * ps1.tokens.size + 4) = .ok
      (applyNodeFinalization
        (YamlValue.scalar
          { content, style := .doubleQuoted, tag := none, anchor := none })
        ps1.advance {} (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
    cases h_f : 4 * ps1.tokens.size + 4 with
    | zero => simp [ps1, ParseStateIx.advance] at h_f
    | succ n =>
      unfold parseNode
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_np]; simp only []
      unfold validateNodeProps
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      unfold parseNodeContent
      rw [h_peek1]; rfl
  -- applyNodeFinalization on a scalar with no props.
  have h_finalize : applyNodeFinalization
      (YamlValue.scalar { content, style := .doubleQuoted, tag := none, anchor := none })
      ps1.advance {} (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
      = (YamlValue.scalar
          { content, style := .doubleQuoted, tag := none, anchor := none },
         ps1.advance) := by
    unfold applyNodeFinalization
    simp [ps1, ParseStateIx.advance]
  -- Combine into parseDocument.
  have h_doc_val : parseDocument ps1 = .ok
      ({ value := YamlValue.scalar
            { content, style := .doubleQuoted, tag := none, anchor := none },
         directives := #[], anchors := ps1.advance.anchors,
         nodePositions := ps1.advance.nodePositions }, ps1.advance) := by
    unfold parseDocument
    simp only [bind, Except.bind, h_pds, h_peek1, h_parseNode, h_finalize]
  -- ps1.advance.peek? = some .streamEnd
  have h_peek2 : ps1.advance.peek? = some YamlToken.streamEnd := by
    show ((tokens.get? 2).map (·.token)) = _
    rw [show tokens.get? 2 = some tokens.tokens[2] from by
      unfold Indexed.TokenStream.get?; rw [Array.getElem?_eq_getElem h2]]
    rw [Option.map_some]; show some tokens.tokens[2].token = _; rw [h_t2']
  -- Apply parseStreamLoop_single_docIx.
  have h_fuel_ge : tokens.size ≥ 2 := by omega
  have h_loop := parseStreamLoop_single_docIx ps1 tokens.size h_fuel_ge
    (YamlToken.scalar content .doubleQuoted) h_peek1 (by intro h; cases h)
    { value := YamlValue.scalar
        { content, style := .doubleQuoted, tag := none, anchor := none },
      directives := #[], anchors := ps1.advance.anchors,
      nodePositions := ps1.advance.nodePositions }
    ps1.advance h_doc_val h_peek2
  exact ⟨_, h_loop, rfl, by simp [getElem!_pos]⟩

/-- **`parseYamlRawIx` on `emitScalar` produces a scalar value**: when
    `parseYamlRawIx` succeeds on emitter scalar output, the first
    document's value is a scalar with the original content. Indexed twin
    of legacy `parseYamlRaw_emitScalar_value` (line 8812). -/
theorem parseYamlRawIx_emitScalar_value (content : String)
    (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRawIx (emitScalar content) = .ok raw_docs) :
    ∃ s : Scalar, raw_docs[0]!.value = .scalar s ∧ s.content = content := by
  obtain ⟨tokens, h_scan, h_parse⟩ := parseYamlRawIx_ok_decompose _ _ h_raw
  obtain ⟨h_sz3, h_t0, h_t1, h_t2⟩ := scanFilteredIx_emitScalar_vals content tokens h_scan
  obtain ⟨docs, h_ps, _, h_dv⟩ :=
    parseStream_three_tokens_scalarIx (input := emitScalar content) content tokens
      h_sz3 h_t0 h_t1 h_t2
  have h_eq : raw_docs = docs := Except.ok.inj (h_parse.symm.trans h_ps)
  subst h_eq
  exact ⟨Scalar.mk content .doubleQuoted none none none, h_dv, rfl⟩

end L4YAML.Proofs.Indexed.EmitterScannability.ParseStream
