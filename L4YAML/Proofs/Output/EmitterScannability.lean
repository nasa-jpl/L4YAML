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
import L4YAML.Proofs.Output.EmitterScannability.ScannerAcceptance
import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
import L4YAML.Proofs.Output.EmitterScannability.FilteredGrowth
import L4YAML.Proofs.Output.EmitterScannability.ScanChainGrowth
import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Proofs.Output.EmitterScannability.FilteredTracking
import L4YAML.Proofs.Output.EmitterScannability.WellBracketed
import L4YAML.Proofs.Output.EmitterScannability.NonemptyStructure

/-!
# Emitter Scannability (Phase E, Steps 1–2)

Step 1 — Proof that the canonical emitter's output is accepted by the scanner:

```
∀ v, Grammable v false → ∃ tokens, Scanner.scanFiltered (emit v) = .ok tokens
```

Step 2 — Composition with the parser to prove the full pipeline succeeds:

```
∀ v, Grammable v false → ∃ docs, parseYamlRaw (emit v) = .ok docs
```

## Architecture

The canonical emitter produces a strict subset of YAML:
- All scalars are double-quoted (`"..."`)
- All sequences are flow-style (`[...]`)
- All mappings are flow-style (`{...}`)
- No block constructs, no plain scalars, no document markers

### Proof Strategy

Rather than reasoning about the scanner's state machine directly,
we prove that `parseYamlRaw (emit v) = .ok docs` for all grammable `v`.
This is equivalent to proving both scanner acceptance and parser success.

The proof proceeds by structural induction on `YamlValue`:

**§1** — Escape character validity: each `escapeChar c` produces output that
         `collectDoubleQuotedLoop` accepts.
**§2** — Emitter output properties: non-emptiness and structural facts.
**§3** — Scanner acceptance (Step 1): `scan_accepts_emitScalar` and
         `emit_produces_valid_yaml`.
**§4** — Full pipeline composition (Step 2): parse acceptance,
         single-document guarantee, and grammability preservation.

## Zero Axioms

Target: all theorems machine-checked with 0 sorry, 0 axiom, 0 admit.
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

/-! ## §5  Content Fidelity Infrastructure

Helper lemmas for the content fidelity proof (`emit_roundtrip_content_eq`).

### §5.1  Compose invariance for scalars

`YamlDocument.compose` applies `resolveAliases` and `stripAnchors`.
For scalars, `resolveAliases` is identity and `stripAnchors` only clears
the anchor field. Since `contentEq` ignores anchors, compose doesn't
affect content equivalence for scalars.
-/

-- compose on a scalar document preserves the content field
theorem compose_scalar_content (doc : YamlDocument) (s : Scalar)
    (h_val : doc.value = .scalar s) :
    (doc.compose).value = .scalar { s with anchor := none } := by
  unfold YamlDocument.compose; dsimp only []
  rw [h_val, resolveAliases_scalar, stripAnchors_scalar]

-- contentEq through compose for scalars: original vs composed
theorem contentEq_scalar_compose (s_orig : Scalar) (s_parsed : Scalar)
    (h_content : s_orig.content = s_parsed.content) :
    contentEq (.scalar s_orig) (.scalar { s_parsed with anchor := none }) = true := by
  exact contentEq_scalar_content s_orig { s_parsed with anchor := none } h_content

/-- Token structure: the filtered scan of `emitScalar content` produces
    exactly 3 tokens: `streamStart`, `scalar content .doubleQuoted`, `streamEnd`.
    This follows from the scanner producing `[streamStart, ph, ph, scalar, streamEnd]`
    (where `ph` are saveSimpleKey placeholders) and filtering removes placeholders. -/
theorem scanFiltered_emitScalar_vals (content : String) (tokens : Array (Positioned YamlToken))
    (h_scan : scanFiltered (emitScalar content) = .ok tokens) :
    tokens.size = 3 ∧ tokens[0]!.val = .streamStart ∧
    tokens[1]!.val = .scalar content .doubleQuoted ∧ tokens[2]!.val = .streamEnd := by
  -- Reuse scanner infrastructure from scanFiltered_emitScalar_content
  obtain ⟨s₁, h_snt1, h_peek1, h_flow1, h_dp1, ⟨tok, h_tok_mem, h_tok_val⟩, h_ids1, h_filt1⟩ :=
    scanNextToken_emitScalar_init content
  have h_snt2 : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek1
  have h_fuel : ((emitScalar content).utf8ByteSize + 1) * 4 ≥ 2 := by
    have := emitScalar_utf8ByteSize_ge content; omega
  -- Compute raw scan and unwindIndents identity
  have h_scan_eq : scan (emitScalar content)
      = scanLoop ((ScannerState.mk' (emitScalar content)).emit .streamStart)
          (((emitScalar content).utf8ByteSize + 1) * 4) := by
    have h_chars := chars_from_zero_toList (emitScalar content)
    rw [emitScalar_toList] at h_chars
    have h_corr := initial_corr (emitScalar content) _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons (ScannerState.mk' (emitScalar content)) '"'
      ((escapeString content).toList ++ ['"']) 0 h_corr
    have h_pk_emit : ((ScannerState.mk' (emitScalar content)).emit .streamStart).peek?
        = (ScannerState.mk' (emitScalar content)).peek? := rfl
    unfold scan; dsimp only []; rw [h_pk_emit, h_pk]
    split <;> first | rfl | exact absurd ‹_› (by decide)
  have h_ci : s₁.currentIndent = -1 := by
    unfold ScannerState.currentIndent; rw [h_ids1]; rfl
  have h_uwi : unwindIndents s₁ (-1) = s₁ := by
    unfold unwindIndents
    rw [show s₁.indents.size = 1 from by rw [h_ids1]; rfl]
    unfold unwindIndentsLoop; simp [h_ci]
  have h_scan_raw : scan (emitScalar content) =
      .ok (s₁.emit .streamEnd).tokens := by
    rw [h_scan_eq, scanLoop_two_iter_eq h_fuel h_snt1 h_snt2 h_flow1 h_dp1, h_uwi]
  have h_tokens_eq : tokens = (s₁.emit .streamEnd).tokens.filter
      (fun t => t.val != .placeholder) := by
    simp only [scanFiltered, h_scan_raw] at h_scan
    exact (Except.ok.inj h_scan).symm
  -- Now characterize the token structure using the filtered token values from h_filt1.
  -- (s₁.emit .streamEnd).tokens = s₁.tokens.push {streamEnd_tok}
  -- After filter (since streamEnd ≠ placeholder): (s₁.tokens.filter p).push {streamEnd_tok}
  -- After map: [streamStart, scalar, streamEnd] (3 elements)
  have h_filt_full : tokens.map (·.val)
      = #[.streamStart, .scalar content .doubleQuoted, .streamEnd] := by
    rw [h_tokens_eq]
    -- Unfold emit to expose push, then distribute filter and map
    show ((s₁.tokens.push ⟨s₁.currentPos, .streamEnd, s₁.currentPos⟩).filter
          (fun t => t.val != .placeholder)).map (·.val) = _
    simp only [Array.filter_push,
      show (YamlToken.streamEnd != .placeholder) = true from rfl,
      ite_true, Array.map_push, h_filt1]
    rfl
  have h_sz : tokens.size = 3 := by
    have := congrArg Array.size h_filt_full; rwa [Array.size_map] at this
  refine ⟨h_sz, ?_, ?_, ?_⟩
  · rw [show tokens[0]! = tokens[0]'(by omega) from getElem!_pos tokens 0 (by omega)]
    have h := Array.getElem_map (f := (·.val)) (xs := tokens) (i := 0)
      (show 0 < (tokens.map _).size from by rw [Array.size_map]; omega)
    simp only [h_filt_full] at h; exact h.symm
  · rw [show tokens[1]! = tokens[1]'(by omega) from getElem!_pos tokens 1 (by omega)]
    have h := Array.getElem_map (f := (·.val)) (xs := tokens) (i := 1)
      (show 1 < (tokens.map _).size from by rw [Array.size_map]; omega)
    simp only [h_filt_full] at h; exact h.symm
  · rw [show tokens[2]! = tokens[2]'(by omega) from getElem!_pos tokens 2 (by omega)]
    have h := Array.getElem_map (f := (·.val)) (xs := tokens) (i := 2)
      (show 2 < (tokens.map _).size from by rw [Array.size_map]; omega)
    simp only [h_filt_full] at h; exact h.symm

-- **Parser trace on three-token scalar stream**: Given a token array with
-- values `[streamStart, scalar content .doubleQuoted, streamEnd]`,
-- `parseStream` produces exactly one document whose value is
-- `YamlValue.scalar { content := content, style := .doubleQuoted }`.
set_option maxHeartbeats 6400000 in
theorem parseStream_three_tokens_scalar (content : String)
    (tokens : Array (Positioned YamlToken))
    (h_sz : tokens.size = 3)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_t1 : tokens[1]!.val = .scalar content .doubleQuoted)
    (h_t2 : tokens[2]!.val = .streamEnd) :
    ∃ (docs : Array YamlDocument),
      parseStream tokens = .ok docs ∧ docs.size = 1 ∧
      docs[0]!.value = .scalar (Scalar.mk content .doubleQuoted none none none) := by
  -- Establish index bounds
  have h0 : (0 : Nat) < tokens.size := by omega
  have h1 : (1 : Nat) < tokens.size := by omega
  have h2 : (2 : Nat) < tokens.size := by omega
  -- Convert getElem! to getElem in hypotheses
  have h_gei : ∀ (i : Nat) (hi : i < tokens.size),
      tokens[i]!.val = tokens[i].val := by
    intro i hi; simp [getElem!_pos, hi]
  have h_t1' : tokens[1].val = .scalar content .doubleQuoted := by rw [← h_gei 1 h1]; exact h_t1
  have h_t2' : tokens[2].val = .streamEnd := by rw [← h_gei 2 h2]; exact h_t2
  -- Step 1: Unfold parseStream and dispatch expect .streamStart
  unfold parseStream
  simp only [bind, Except.bind]
  unfold ParseState.expect
  simp only [ParseState.peek?]
  simp only [show (0 : Nat) < tokens.size from by omega, ↓reduceIte, h_t0]
  simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
             ↓reduceIte]
  -- After expect step, introduce ps1 = advance of initial state
  let ps1 : ParseState := ({ tokens := tokens } : ParseState).advance
  show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
    docs.size = 1 ∧ docs[0]!.value = .scalar (Scalar.mk content .doubleQuoted none none none)
  -- peek? facts for ps1
  have h_peek1 : ps1.peek? = some (.scalar content .doubleQuoted) := by
    simp only [ps1, ParseState.peek?, ParseState.advance, h1, ↓reduceIte]
    simp only [show (0 : Nat) + 1 = 1 from rfl, h_gei 1 h1, h_t1']
  have h_peek_not_dir : match ps1.peek? with
      | some (.versionDirective _ _) | some (.tagDirective _ _) => False
      | _ => True := by rw [h_peek1]; trivial
  have h_peek_not_anctag : match ps1.peek? with
      | some (.anchor _) | some (.tag _ _) => False
      | _ => True := by rw [h_peek1]; trivial
  -- parseDirectives and prepareDocumentState
  have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skip ps1 h_peek_not_dir
  have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
    unfold prepareDocumentState
    simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
    have h_th : { ps1 with tagHandles := #[] } = ps1 := by
      simp [ps1, ParseState.advance]
    rw [h_th, h_peek1]
    unfold ParseState.tryConsume
    rw [h_peek1]; simp
  -- parseNodeProperties skip
  have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
    parseNodeProperties_skip ps1 h_peek_not_anctag
  -- parseNode
  have h_parseNode : parseNode ps1 (4 * ps1.tokens.size + 4) = .ok
      (applyNodeFinalization
        (.scalar { content, style := .doubleQuoted, tag := none, anchor := none })
        ps1.advance {} (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
    cases h_f : 4 * ps1.tokens.size + 4 with
    | zero => simp [ps1, ParseState.advance] at h_f
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
  -- applyNodeFinalization (scalar with empty props and trackPositions=false)
  have h_finalize : applyNodeFinalization
      (.scalar { content, style := .doubleQuoted, tag := none, anchor := none })
      ps1.advance {} (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
      = (.scalar { content, style := .doubleQuoted, tag := none, anchor := none }, ps1.advance) := by
    unfold applyNodeFinalization
    simp [ps1, ParseState.advance]
  -- Combine into parseDocument
  have h_doc_val : parseDocument ps1 = .ok
      ({ value := .scalar { content, style := .doubleQuoted, tag := none, anchor := none },
         directives := #[], anchors := ps1.advance.anchors,
         nodePositions := ps1.advance.nodePositions }, ps1.advance) := by
    unfold parseDocument
    simp only [bind, Except.bind, h_pds, h_peek1, h_parseNode, h_finalize]
  -- ps1.advance.peek? = some .streamEnd
  have h_peek2 : ps1.advance.peek? = some .streamEnd := by
    simp only [ps1, ParseState.peek?, ParseState.advance, h2, ↓reduceIte]
    simp only [show (0 : Nat) + 1 + 1 = 2 from rfl, h_gei 2 h2, h_t2']
  -- Apply parseStreamLoop_single_doc
  have h_fuel_ge : tokens.size ≥ 2 := by omega
  have h_loop := parseStreamLoop_single_doc ps1 tokens.size h_fuel_ge
    (.scalar content .doubleQuoted) h_peek1 (by intro h; cases h)
    { value := .scalar { content, style := .doubleQuoted, tag := none, anchor := none },
      directives := #[], anchors := ps1.advance.anchors, nodePositions := ps1.advance.nodePositions }
    ps1.advance h_doc_val h_peek2
  -- Provide the witness
  exact ⟨_, h_loop, rfl, by simp [getElem!_pos]⟩

/-- **parseYamlRaw on emitScalar produces scalar value**: When `parseYamlRaw`
    succeeds on emitter scalar output, the first document's value is a scalar
    with the original content. -/
theorem parseYamlRaw_emitScalar_value (content : String)
    (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emitScalar content) = .ok raw_docs) :
    ∃ s : Scalar, raw_docs[0]!.value = .scalar s ∧ s.content = content := by
  -- Decompose into scan + parse
  obtain ⟨tokens, h_scan, h_parse⟩ :=
    Composition.parseYamlRaw_ok_decompose _ _ h_raw
  -- Token structure from scanner
  obtain ⟨h_sz3, h_t0, h_t1, h_t2⟩ := scanFiltered_emitScalar_vals content tokens h_scan
  -- Parser trace on [streamStart, scalar, streamEnd]
  obtain ⟨docs, h_ps, _, h_dv⟩ :=
    parseStream_three_tokens_scalar content tokens h_sz3 h_t0 h_t1 h_t2
  -- Unify raw_docs with docs
  have h_eq : raw_docs = docs := Except.ok.inj (h_parse.symm.trans h_ps)
  subst h_eq
  exact ⟨Scalar.mk content .doubleQuoted none none none, h_dv, rfl⟩

/-- Combined scanner characterization and parser acceptance for flow sequences.
    Given that scanning the emitted sequence succeeds, the parser pipeline
    produces exactly one document.

    - **Empty case** (`items = #[]`): Fully proven via `native_decide` on the
      concrete 4-token stream `[streamStart, flowSequenceStart, flowSequenceEnd, streamEnd]`.
    - **Non-empty case**: Requires parser fuel sufficiency for `parseFlowSequenceLoop`
      on well-bracketed tokens — each loop iteration consumes ≥1 token via `parseNode`,
      so fuel = `4 * tokens.size + 4` suffices. Currently sorry'd pending position
      monotonicity proof through `parseNode` dispatch. -/
theorem parseStream_emitSequence (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) {tokens : Array (Positioned YamlToken)}
    (h_scan : Scanner.scanFiltered (emit (.sequence style items tag anchor)) = .ok tokens)
    (h_items : ∀ (i : Fin items.size), Grammable items[i] (false || style == CollectionStyle.flow)) :
    ∃ docs, parseStream tokens = .ok docs ∧ docs.size = 1 := by
  -- emit ignores style/tag/anchor: always produces "[" ++ emitList items.toList ++ "]"
  have h_emit : emit (.sequence style items tag anchor) =
      "[" ++ emit.emitList items.toList ++ "]" := rfl
  rw [h_emit] at h_scan
  match h_list : items.toList with
  | [] =>
    -- Empty sequence: emit produces "[]", native_decide verifies full pipeline
    rw [h_list] at h_scan
    have h_str : ("[" ++ emit.emitList ([] : List YamlValue) ++ "]") = "[]" := by native_decide
    rw [h_str] at h_scan
    -- h_scan : Scanner.scanFiltered "[]" = .ok tokens
    have h_full := checkFullSeq_true
    unfold checkFullSeq at h_full
    simp only [h_scan] at h_full
    -- h_full : (match parseStream tokens with | .ok docs => docs.size == 1 | ...) = true
    match h_ps : parseStream tokens with
    | .ok docs =>
      simp only [h_ps] at h_full
      exact ⟨docs, rfl, by simpa using h_full⟩
    | .error _ => simp [h_ps] at h_full
  | _ :: _ =>
    -- Non-empty: trace through parseStream → parseStreamLoop → parseDocument →
    -- parseNode → parseFlowSequence → parseFlowSequenceLoop using loop fuel
    -- sufficiency from Sub-phase C.
    -- Flow structure from scanner characterization
    have h_all_block : ∀ w, w ∈ items.toList → EmitScansInFlowBlock w := by
      intro w hw
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
      have h_sz : i < items.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ emit_scans_in_flow_block _ (h_items ⟨i, h_sz⟩)
    obtain ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, h_content0, h_fe_pattern,
            h_pnok⟩ :=
      scanFiltered_emitSeq_nonempty_structure items tokens h_scan (by simp [h_list]) h_all_block
    -- Step 1: Unfold parseStream, dispatch expect .streamStart
    unfold parseStream
    simp only [bind, Except.bind]
    unfold ParseState.expect
    simp only [ParseState.peek?]
    simp only [show (0 : Nat) < tokens.size from by omega, ↓reduceIte, h_t0]
    simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
               ↓reduceIte]
    -- ps1 = advance of initial state (pos = 1)
    let ps1 : ParseState := ({ tokens := tokens } : ParseState).advance
    show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
      docs.size = 1
    -- peek? facts for ps1
    have h_peek1 : ps1.peek? = some .flowSequenceStart := by
      simp only [ps1, ParseState.peek?, ParseState.advance]
      simp only [show (0 : Nat) + 1 = 1 from rfl,
                 show 1 < tokens.size from by omega, ↓reduceIte, h_t1]
    have h_peek_not_dir : match ps1.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    have h_peek_not_anctag : match ps1.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    -- parseDirectives and prepareDocumentState
    have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skip ps1 h_peek_not_dir
    have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
      unfold prepareDocumentState
      simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
      have h_th : { ps1 with tagHandles := #[] } = ps1 := by
        simp [ps1, ParseState.advance]
      rw [h_th, h_peek1]
      unfold ParseState.tryConsume
      rw [h_peek1]; simp
    -- parseNodeProperties skip
    have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
      parseNodeProperties_skip ps1 h_peek_not_anctag
    -- Fuel chain: parseDocument creates fuel 4*N+4 where N = tokens.size
    --   parseNode(4*N+4) destructs → parseNodeContent(4*N+3)
    --   parseNodeContent(4*N+3) dispatches → parseFlowSequence(4*N+3)
    --   parseFlowSequence(4*N+3) destructs → parseFlowSequenceLoop(4*N+2)
    have h_ps1_tok : ps1.tokens.size = tokens.size := by simp [ps1, ParseState.advance]
    -- ps_mid = ps1.advance (pos = 2): start of flow sequence loop body
    let ps_mid : ParseState := ps1.advance
    have h_ps_mid_tok : ps_mid.tokens = tokens := by simp [ps_mid, ps1, ParseState.advance]
    have h_ps_mid_pos : ps_mid.pos = 2 := by simp [ps_mid, ps1, ParseState.advance]
    -- Apply parseFlowSequenceLoop_emitter_ok with loop fuel = 4*N+2
    have h_endPos : tokens.size - 2 < tokens.size := by omega
    have h_loop_fuel : 4 * tokens.size + 2 > (tokens.size - 2) - ps_mid.pos + 1 := by
      simp only [h_ps_mid_pos]; omega
    have h_loop_pos : ps_mid.pos ≤ tokens.size - 2 := by
      simp only [h_ps_mid_pos]; omega
    have h_pnok_adj : L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk
        ps_mid.tokens (tokens.size - 2) (4 * tokens.size + 2) 2 := by
      rw [h_ps_mid_tok]; exact h_pnok.mono (by omega)
    have h_end_tok_adj : ps_mid.tokens[tokens.size - 2]!.val = .flowSequenceEnd := by
      rw [h_ps_mid_tok]; exact h_tpe
    have h_entry_vacuous : (#[] : Array YamlValue).size > 0 →
        ps_mid.peek? = some .flowEntry ∨ ps_mid.peek? = some .flowSequenceEnd := by
      intro h; simp [Array.size] at h
    have h_content_start_adj : ps_mid.pos < tokens.size - 2 → (#[] : Array YamlValue).size = 0 →
        (∃ c s, ps_mid.peek? = some (.scalar c s)) ∨
        ps_mid.peek? = some .flowSequenceStart ∨
        ps_mid.peek? = some .flowMappingStart := by
      intro _ _
      have h_mid_peek_val : ps_mid.peek? = some tokens[2]!.val := by
        simp only [ps_mid, ps1, ParseState.peek?, ParseState.advance]
        simp only [show (0 : Nat) + 1 + 1 = 2 from rfl, show 2 < tokens.size from by omega,
                   ↓reduceIte]
      rcases h_content0 with ⟨c, s, hcs⟩ | hcs | hcs
      · exact .inl ⟨c, s, by rw [h_mid_peek_val, hcs]⟩
      · exact .inr (.inl (by rw [h_mid_peek_val, hcs]))
      · exact .inr (.inr (by rw [h_mid_peek_val, hcs]))
    have h_after_fe_adj : ∀ k, ps_mid.pos ≤ k → k < tokens.size - 2 →
        ps_mid.tokens[k]!.val = .flowEntry →
        L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧
        ((∃ c s, ps_mid.tokens[k + 1]!.val = .scalar c s) ∨
         ps_mid.tokens[k + 1]!.val = .flowSequenceStart ∨
         ps_mid.tokens[k + 1]!.val = .flowMappingStart) := by
      intro k hk1 hk2 hk3 hk4
      rw [h_ps_mid_tok] at hk3 hk4 ⊢; rw [h_ps_mid_pos] at hk1
      exact h_fe_pattern k hk1 hk2 hk3 hk4
    have h_at_end_adj : ps_mid.peek? = some .flowSequenceEnd → ps_mid.pos = tokens.size - 2 := by
      intro h_peek; exfalso
      have ⟨_, h_val⟩ := L4YAML.Proofs.ParserWellBehaved.peek_some_val h_peek
      simp only [h_ps_mid_tok, h_ps_mid_pos] at h_val
      -- h_content0 says tokens[2]!.val is scalar/flowSeqStart/flowMapStart
      -- h_val says tokens[2]!.val = .flowSequenceEnd → contradiction
      rcases h_content0 with ⟨c, s, hcs⟩ | hcs | hcs <;> rw [h_val] at hcs <;> cases hcs
    have h_bal_init : L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 ps_mid.pos = 0 := by
      rw [h_ps_mid_pos]; unfold L4YAML.Proofs.ParserGrammable.flowBracketBalance; simp
    obtain ⟨items_res, ps_loop, h_loop_ok, h_loop_peek, h_loop_pos_eq, h_loop_tok, h_loop_tp⟩ :=
      L4YAML.Proofs.ParserWellBehaved.parseFlowSequenceLoop_emitter_ok
        (4 * tokens.size + 2) ps_mid #[] (tokens.size - 2)
        2
        h_pnok_adj h_loop_fuel h_loop_pos h_endPos h_end_tok_adj
        h_at_end_adj
        h_entry_vacuous
        (fun h_pos_lt h_size_zero => h_content_start_adj h_pos_lt h_size_zero)
        h_after_fe_adj h_bal_init
        (by rw [h_ps_mid_pos]; omega)
    -- parseFlowSequence(4*N+3): destructs, passes 4*N+2 to loop
    have h_parseFlowSeq : parseFlowSequence ps1 (4 * tokens.size + 3) =
        Except.ok (.sequence .flow items_res, ps_loop.advance) := by
      unfold parseFlowSequence
      simp only [bind, Except.bind]
      rw [h_loop_ok]; simp only [h_loop_peek]
    -- parseNodeContent dispatches to parseFlowSequence
    have h_parseNC : parseNodeContent ps1 (4 * tokens.size + 3) {} =
        Except.ok (.sequence .flow items_res, ps_loop.advance) := by
      unfold parseNodeContent; rw [h_peek1]; exact h_parseFlowSeq
    -- applyNodeFinalization is identity for empty props and trackPositions=false
    have h_finalize : applyNodeFinalization
        (.sequence .flow items_res) ps_loop.advance {}
        (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
        = (.sequence .flow items_res, ps_loop.advance) := by
      unfold applyNodeFinalization
      simp only []
      show (YamlValue.sequence .flow items_res none none,
            if ps_loop.advance.trackPositions then _ else ps_loop.advance) = _
      have h_tp : ps_loop.advance.trackPositions = false := by
        exact h_loop_tp
      simp [h_tp]
    -- parseNode(4*N+4): destructs, passes 4*N+3 to parseNodeContent
    have h_parseNode : parseNode ps1 (4 * tokens.size + 4) =
        Except.ok (.sequence .flow items_res, ps_loop.advance) := by
      unfold parseNode
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_np]; simp only []
      unfold validateNodeProps
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_parseNC]; simp [h_finalize]
    -- parseDocument uses fuel 4 * ps1.tokens.size + 4 = 4*N+4
    have h_parseDoc : parseDocument ps1 = Except.ok
        ({ value := .sequence .flow items_res,
           directives := #[], anchors := ps_loop.advance.anchors,
           nodePositions := ps_loop.advance.nodePositions }, ps_loop.advance) := by
      unfold parseDocument
      simp only [bind, Except.bind, h_pds, h_peek1]
      rw [show 4 * ps1.tokens.size + 4 = 4 * tokens.size + 4 from by omega]
      rw [h_parseNode]
    -- ps_loop.advance.peek? = some .streamEnd
    have h_peek_end : ps_loop.advance.peek? = some .streamEnd := by
      have h_loop_tok_eq : ps_loop.tokens = tokens := h_loop_tok.trans h_ps_mid_tok
      -- Position is directly from h_loop_pos_eq (no uniqueness-based trichotomy needed)
      simp only [ParseState.peek?, ParseState.advance, h_loop_tok_eq]
      simp only [h_loop_pos_eq, show tokens.size - 2 + 1 = tokens.size - 1 from by omega,
                 show tokens.size - 1 < tokens.size from by omega, ↓reduceIte, h_tlast]
    -- Apply parseStreamLoop_single_doc
    have h_fuel_ge : tokens.size ≥ 2 := by omega
    have h_loop_doc := parseStreamLoop_single_doc ps1 tokens.size h_fuel_ge
      .flowSequenceStart h_peek1 (by intro h; cases h)
      { value := .sequence .flow items_res,
        directives := #[], anchors := ps_loop.advance.anchors,
        nodePositions := ps_loop.advance.nodePositions }
      ps_loop.advance h_parseDoc h_peek_end
    exact ⟨_, h_loop_doc, rfl⟩

/-- Combined scanner characterization and parser acceptance for flow mappings.
    Analogous to `parseStream_emitSequence` but for `emit (.mapping ...)`.

    - **Empty case** (`pairs = #[]`): Fully proven via `native_decide` on the
      concrete 4-token stream `[streamStart, flowMappingStart, flowMappingEnd, streamEnd]`.
    - **Non-empty case**: Requires parser fuel sufficiency for `parseFlowMappingLoop`
      on well-bracketed tokens. Currently sorry'd pending position monotonicity proof. -/
theorem parseStream_emitMapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) {tokens : Array (Positioned YamlToken)}
    (h_scan : Scanner.scanFiltered (emit (.mapping style pairs tag anchor)) = .ok tokens)
    (hk : ∀ (i : Fin pairs.size), Grammable pairs[i].fst (false || style == CollectionStyle.flow))
    (hv : ∀ (i : Fin pairs.size), Grammable pairs[i].snd (false || style == CollectionStyle.flow)) :
    ∃ docs, parseStream tokens = .ok docs ∧ docs.size = 1 := by
  -- emit ignores style/tag/anchor: always produces "{" ++ emitPairList pairs.toList ++ "}"
  have h_emit : emit (.mapping style pairs tag anchor) =
      "{" ++ emit.emitPairList pairs.toList ++ "}" := rfl
  rw [h_emit] at h_scan
  match h_list : pairs.toList with
  | [] =>
    -- Empty mapping: emit produces "{}", native_decide verifies full pipeline
    rw [h_list] at h_scan
    have h_str : ("{" ++ emit.emitPairList ([] : List (YamlValue × YamlValue)) ++ "}") = "{}" := by native_decide
    rw [h_str] at h_scan
    -- h_scan : Scanner.scanFiltered "{}" = .ok tokens
    have h_full := checkFullMap_true
    unfold checkFullMap at h_full
    simp only [h_scan] at h_full
    match h_ps : parseStream tokens with
    | .ok docs =>
      simp only [h_ps] at h_full
      exact ⟨docs, rfl, by simpa using h_full⟩
    | .error _ => simp [h_ps] at h_full
  | _ :: _ =>
    -- Non-empty: trace through parseStream → parseStreamLoop → parseDocument →
    -- parseNode → parseFlowMapping → parseFlowMappingLoop using loop fuel
    -- sufficiency from Sub-phase D.
    -- Flow structure from scanner characterization
    have h_all_k_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKeyBlock p.1 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ emit_scans_in_flow_saved_key_block _ (hk ⟨i, h_sz⟩)
    have h_all_v_block : ∀ p, p ∈ pairs.toList → EmitScansInFlowBlock p.2 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ emit_scans_in_flow_block _ (hv ⟨i, h_sz⟩)
    obtain ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_key_pattern,
            h_entry_ok⟩ :=
      scanFiltered_emitMap_nonempty_structure pairs tokens h_scan (by simp [h_list])
        h_all_k_block h_all_v_block
    -- Step 1: Unfold parseStream, dispatch expect .streamStart
    unfold parseStream
    simp only [bind, Except.bind]
    unfold ParseState.expect
    simp only [ParseState.peek?]
    simp only [show (0 : Nat) < tokens.size from by omega, ↓reduceIte, h_t0]
    simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
               ↓reduceIte]
    -- ps1 = advance of initial state (pos = 1)
    let ps1 : ParseState := ({ tokens := tokens } : ParseState).advance
    show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
      docs.size = 1
    -- peek? facts for ps1
    have h_peek1 : ps1.peek? = some .flowMappingStart := by
      simp only [ps1, ParseState.peek?, ParseState.advance]
      simp only [show (0 : Nat) + 1 = 1 from rfl,
                 show 1 < tokens.size from by omega, ↓reduceIte, h_t1]
    have h_peek_not_dir : match ps1.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    have h_peek_not_anctag : match ps1.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    -- parseDirectives and prepareDocumentState
    have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skip ps1 h_peek_not_dir
    have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
      unfold prepareDocumentState
      simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
      have h_th : { ps1 with tagHandles := #[] } = ps1 := by
        simp [ps1, ParseState.advance]
      rw [h_th, h_peek1]
      unfold ParseState.tryConsume
      rw [h_peek1]; simp
    -- parseNodeProperties skip
    have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
      parseNodeProperties_skip ps1 h_peek_not_anctag
    -- Fuel chain: parseDocument(4*N+4) → parseNode(4*N+4)
    --   → parseNodeContent(4*N+3) → parseFlowMapping(4*N+3)
    --   → parseFlowMappingLoop(4*N+2)
    have h_ps1_tok : ps1.tokens.size = tokens.size := by simp [ps1, ParseState.advance]
    -- ps_mid = ps1.advance (pos = 2): start of flow mapping loop body
    let ps_mid : ParseState := ps1.advance
    have h_ps_mid_tok : ps_mid.tokens = tokens := by simp [ps_mid, ps1, ParseState.advance]
    have h_ps_mid_pos : ps_mid.pos = 2 := by simp [ps_mid, ps1, ParseState.advance]
    -- Apply parseFlowMappingLoop_emitter_ok with loop fuel = 4*N+2
    have h_endPos : tokens.size - 2 < tokens.size := by omega
    have h_loop_fuel : 4 * tokens.size + 2 > (tokens.size - 2) - ps_mid.pos + 1 := by
      simp only [h_ps_mid_pos]; omega
    have h_loop_pos : ps_mid.pos ≤ tokens.size - 2 := by
      simp only [h_ps_mid_pos]; omega
    have h_entry_adj : L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk
        ps_mid.tokens (tokens.size - 2) (4 * tokens.size + 2) 2 := by
      rw [h_ps_mid_tok]; exact h_entry_ok.mono (by omega)
    have h_end_tok_adj : ps_mid.tokens[tokens.size - 2]!.val = .flowMappingEnd := by
      rw [h_ps_mid_tok]; exact h_tpe
    have h_sep_adj : (#[] : Array (YamlValue × YamlValue)).size > 0 →
        ps_mid.peek? = some .flowEntry ∨ ps_mid.peek? = some .flowMappingEnd := by
      intro h; simp [Array.size] at h
    have h_start_adj : ps_mid.pos < tokens.size - 2 → (#[] : Array (YamlValue × YamlValue)).size = 0 →
        ps_mid.peek? = some .key := by
      intro _ _
      simp only [ps_mid, ps1, ParseState.peek?, ParseState.advance]
      simp only [show (0 : Nat) + 1 + 1 = 2 from rfl, show 2 < tokens.size from by omega,
                 ↓reduceIte, Option.some.injEq]
      exact h_t2_key
    have h_after_fe_adj : ∀ k, ps_mid.pos ≤ k → k < tokens.size - 2 →
        ps_mid.tokens[k]!.val = .flowEntry →
        L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧ ps_mid.tokens[k + 1]!.val = .key := by
      intro k hk1 hk2 hk3 hk4
      rw [h_ps_mid_tok] at hk3 hk4 ⊢; rw [h_ps_mid_pos] at hk1
      exact h_fe_key_pattern k hk1 hk2 hk3 hk4
    have h_at_end_adj : ps_mid.peek? = some .flowMappingEnd → ps_mid.pos = tokens.size - 2 := by
      intro h_peek; exfalso
      have ⟨_, h_val⟩ := L4YAML.Proofs.ParserWellBehaved.peek_some_val h_peek
      simp only [h_ps_mid_tok, h_ps_mid_pos] at h_val
      -- tokens[2] = .key ≠ .flowMappingEnd
      exact absurd (h_t2_key.symm.trans h_val) (by decide)
    have h_bal_init : L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 ps_mid.pos = 0 := by
      rw [h_ps_mid_pos]; unfold L4YAML.Proofs.ParserGrammable.flowBracketBalance; simp
    obtain ⟨pairs_res, ps_loop, h_loop_ok, h_loop_peek, h_loop_pos_eq, h_loop_tok, h_loop_tp⟩ :=
      L4YAML.Proofs.ParserWellBehaved.parseFlowMappingLoop_emitter_ok
        (4 * tokens.size + 2) ps_mid #[] (tokens.size - 2)
        2
        h_entry_adj h_loop_fuel h_loop_pos h_endPos h_end_tok_adj
        h_at_end_adj
        h_sep_adj
        (fun h_pos_lt h_size_zero => h_start_adj h_pos_lt h_size_zero)
        h_after_fe_adj h_bal_init
        (by rw [h_ps_mid_pos]; omega)
    -- parseFlowMapping(4*N+3): destructs, passes 4*N+2 to loop
    have h_parseFlowMap : parseFlowMapping ps1 (4 * tokens.size + 3) =
        Except.ok (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold parseFlowMapping
      simp only [bind, Except.bind]
      rw [h_loop_ok]; simp only [h_loop_peek]
    -- parseNodeContent dispatches to parseFlowMapping
    have h_parseNC : parseNodeContent ps1 (4 * tokens.size + 3) {} =
        Except.ok (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold parseNodeContent; rw [h_peek1]; exact h_parseFlowMap
    -- applyNodeFinalization is identity for empty props and trackPositions=false
    have h_finalize : applyNodeFinalization
        (.mapping .flow pairs_res) ps_loop.advance {}
        (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
        = (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold applyNodeFinalization
      simp only []
      have h_tp : ps_loop.advance.trackPositions = false := by
        exact h_loop_tp
      simp [h_tp]
    -- parseNode(4*N+4): destructs, passes 4*N+3 to parseNodeContent
    have h_parseNode : parseNode ps1 (4 * tokens.size + 4) =
        Except.ok (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold parseNode
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_np]; simp only []
      unfold validateNodeProps
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_parseNC]; simp [h_finalize]
    -- parseDocument uses fuel 4 * ps1.tokens.size + 4 = 4*N+4
    have h_parseDoc : parseDocument ps1 = Except.ok
        ({ value := .mapping .flow pairs_res,
           directives := #[], anchors := ps_loop.advance.anchors,
           nodePositions := ps_loop.advance.nodePositions }, ps_loop.advance) := by
      unfold parseDocument
      simp only [bind, Except.bind, h_pds, h_peek1]
      rw [show 4 * ps1.tokens.size + 4 = 4 * tokens.size + 4 from by omega]
      rw [h_parseNode]
    -- ps_loop.advance.peek? = some .streamEnd
    have h_peek_end : ps_loop.advance.peek? = some .streamEnd := by
      have h_loop_tok_eq : ps_loop.tokens = tokens := h_loop_tok.trans h_ps_mid_tok
      -- Position is directly from h_loop_pos_eq (no uniqueness-based trichotomy needed)
      simp only [ParseState.peek?, ParseState.advance, h_loop_tok_eq]
      simp only [h_loop_pos_eq, show tokens.size - 2 + 1 = tokens.size - 1 from by omega,
                 show tokens.size - 1 < tokens.size from by omega, ↓reduceIte, h_tlast]
    -- Apply parseStreamLoop_single_doc
    have h_fuel_ge : tokens.size ≥ 2 := by omega
    have h_loop_doc := parseStreamLoop_single_doc ps1 tokens.size h_fuel_ge
      .flowMappingStart h_peek1 (by intro h; cases h)
      { value := .mapping .flow pairs_res,
        directives := #[], anchors := ps_loop.advance.anchors,
        nodePositions := ps_loop.advance.nodePositions }
      ps_loop.advance h_parseDoc h_peek_end
    exact ⟨_, h_loop_doc, rfl⟩

/-- **Parse acceptance** (Step 2): The parser accepts the token sequence
    produced by scanning canonical emitter output.

    Given that the scanner successfully tokenized emitter output,
    `parseStream` also succeeds. The emitter's restricted output format
    (double-quoted scalars, flow-only collections, single implicit document)
    avoids all `parseStream` error conditions. -/
theorem parseStream_accepts_emit_tokens (v : YamlValue) (hg : Grammable v false)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered (emit v) = .ok tokens) :
    ∃ docs, parseStream tokens = .ok docs := by
  cases hg with
  | scalar s _ h =>
    -- Recover the 3-token structure [streamStart, scalar, streamEnd] from the scanner
    obtain ⟨h_sz, h_t0, h_t1, h_t2⟩ := scanFiltered_emitScalar_vals s.content tokens h_scan
    -- Apply the parser trace for the 3-token scalar stream
    obtain ⟨docs, h_ps, _, _⟩ := parseStream_three_tokens_scalar s.content tokens h_sz h_t0 h_t1 h_t2
    exact ⟨docs, h_ps⟩

  | sequence style items tag anchor _ h_items =>
    obtain ⟨docs, h_ps, _⟩ := parseStream_emitSequence style items tag anchor h_scan h_items
    exact ⟨docs, h_ps⟩

  | mapping style pairs tag anchor _ hk hv =>
    obtain ⟨docs, h_ps, _⟩ := parseStream_emitMapping style pairs tag anchor h_scan hk hv
    exact ⟨docs, h_ps⟩

/-- **Single document**: The canonical emitter's output produces exactly one
    document when parsed.

    The emitter generates a single implicit document (no `---` markers, no
    multiple-document output), so `parseStreamLoop` produces `#[doc]`.
    This is needed for the universal round-trip theorem which asserts
    `docs.size = 1`. -/
theorem emit_produces_single_document (v : YamlValue) (hg : Grammable v false)
    (docs : Array YamlDocument)
    (h : parseYamlRaw (emit v) = .ok docs) :
    docs.size = 1 := by
  cases hg with
  | scalar s _ h_sc =>
    -- Decompose parseYamlRaw into its scanner and parser components
    obtain ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose _ _ h
    -- Get token boundaries
    obtain ⟨h_sz, h_t0, h_t1, h_t2⟩ := scanFiltered_emitScalar_vals s.content tokens h_scan
    -- Apply the parser trace to get the target output (docs') and its length
    obtain ⟨docs', h_ps, h_docs_sz, _⟩ := parseStream_three_tokens_scalar s.content tokens h_sz h_t0 h_t1 h_t2
    -- Unify the decomposition parse result with the trace parse result
    have h_eq : docs = docs' := Except.ok.inj (h_parse.symm.trans h_ps)
    rwa [h_eq]

  | sequence style items tag anchor _ h_items =>
    obtain ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose _ _ h
    obtain ⟨docs', h_ps, h_docs_sz⟩ := parseStream_emitSequence style items tag anchor h_scan h_items
    have h_eq : docs = docs' := Except.ok.inj (h_parse.symm.trans h_ps)
    rwa [h_eq]

  | mapping style pairs tag anchor _ hk hv =>
    obtain ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose _ _ h
    obtain ⟨docs', h_ps, h_docs_sz⟩ := parseStream_emitMapping style pairs tag anchor h_scan hk hv
    have h_eq : docs = docs' := Except.ok.inj (h_parse.symm.trans h_ps)
    rwa [h_eq]

/-- **Full pipeline (raw)**: The canonical emitter's output parses
    successfully through `parseYamlRaw`.

    Composes Step 1 (`emit_produces_valid_yaml`: scanner acceptance) with
    Step 2 (`parseStream_accepts_emit_tokens`: parser acceptance) via
    `parseYamlRaw_pipeline` (scan + parse → pipeline success). -/
theorem emit_parse_succeeds (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYamlRaw (emit v) = .ok docs := by
  obtain ⟨tokens, h_scan⟩ := emit_produces_valid_yaml v hg
  obtain ⟨docs, h_parse⟩ := parseStream_accepts_emit_tokens v hg tokens h_scan
  exact ⟨docs, Composition.parseYamlRaw_pipeline (emit v) tokens docs h_scan h_parse⟩

/-- **Full pipeline (with compose)**: Emitter output parses successfully
    through `parseYaml`, which resolves aliases via `YamlDocument.compose`.

    Since the emitter produces no aliases (`Grammable` excludes `.alias`
    nodes), compose is effectively the identity on values, but the
    types require going through this step. -/
theorem emit_parseYaml_succeeds (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYaml (emit v) = .ok docs := by
  obtain ⟨raw_docs, h_raw⟩ := emit_parse_succeeds v hg
  exact ⟨raw_docs.map YamlDocument.compose, by simp only [parseYaml, h_raw]⟩

/-- Proves that parsing the emitted tokens for a flow sequence recovers a content-equivalent sequence. -/
theorem emit_roundtrip_sequence_content_eq {inFlow : Bool} (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit (.sequence style items tag anchor)) = .ok raw_docs)
    (h_size : raw_docs.size = 1)
    (h_items : ∀ (i : Fin items.size), Grammable items[i] (inFlow || style == CollectionStyle.flow))
    (ih : ∀ (i : Fin items.size) (raw_docs' : Array YamlDocument),
            parseYamlRaw (emit items[i]) = .ok raw_docs' → raw_docs'.size = 1 →
            contentEq items[i] (raw_docs'.map YamlDocument.compose)[0]!.value = true) :
    contentEq (.sequence style items tag anchor) (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  -- Bridge to canonical style/tag/anchor for contentEq
  rw [contentEq_seq_style_irrel]
  -- Case split on items
  have h_emit : emit (.sequence style items tag anchor) =
      "[" ++ emit.emitList items.toList ++ "]" := rfl
  match h_list : items.toList with
  | [] =>
    -- Empty sequence: emit produces "[]"
    rw [h_list] at h_emit
    have h_str : ("[" ++ emit.emitList ([] : List YamlValue) ++ "]") = "[]" := by native_decide
    rw [h_str] at h_emit
    rw [h_emit] at h_raw
    -- h_raw : parseYamlRaw "[]" = .ok raw_docs
    have h_check := checkContentSeq_true
    unfold checkContentSeq at h_check
    simp only [h_raw] at h_check
    -- h_check : (1 == 1 && contentEq ...) = true   (after reducing docs.size == 1)
    have h_items_empty : items = #[] := by
      exact Array.toList_eq_nil_iff.mp h_list
    rw [h_items_empty]
    -- h_check : (raw_docs.size == 1 && contentEq ...) = true
    -- Extract the contentEq part using h_size
    have h_sz_beq : (raw_docs.size == 1) = true := by simp [h_size]
    rw [h_sz_beq, Bool.true_and] at h_check
    exact h_check
  | _ :: _ =>
    -- Non-empty: requires exact parsed value structure from parser trace.
    exact sorry

/-- Proves that parsing the emitted tokens for a flow mapping recovers a content-equivalent mapping. -/
theorem emit_roundtrip_mapping_content_eq {inFlow : Bool} (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit (.mapping style pairs tag anchor)) = .ok raw_docs)
    (h_size : raw_docs.size = 1)
    (hk : ∀ (i : Fin pairs.size), Grammable pairs[i].fst (inFlow || style == CollectionStyle.flow))
    (hv : ∀ (i : Fin pairs.size), Grammable pairs[i].snd (inFlow || style == CollectionStyle.flow))
    (ihk : ∀ (i : Fin pairs.size) (raw_docs' : Array YamlDocument),
            parseYamlRaw (emit pairs[i].fst) = .ok raw_docs' → raw_docs'.size = 1 →
            contentEq pairs[i].fst (raw_docs'.map YamlDocument.compose)[0]!.value = true)
    (ihv : ∀ (i : Fin pairs.size) (raw_docs' : Array YamlDocument),
            parseYamlRaw (emit pairs[i].snd) = .ok raw_docs' → raw_docs'.size = 1 →
            contentEq pairs[i].snd (raw_docs'.map YamlDocument.compose)[0]!.value = true) :
    contentEq (.mapping style pairs tag anchor) (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  -- Bridge to canonical style/tag/anchor for contentEq
  rw [contentEq_map_style_irrel]
  -- Case split on pairs
  have h_emit : emit (.mapping style pairs tag anchor) =
      "{" ++ emit.emitPairList pairs.toList ++ "}" := rfl
  match h_list : pairs.toList with
  | [] =>
    -- Empty mapping: emit produces "{}"
    rw [h_list] at h_emit
    have h_str : ("{" ++ emit.emitPairList ([] : List (YamlValue × YamlValue)) ++ "}") = "{}" := by native_decide
    rw [h_str] at h_emit
    rw [h_emit] at h_raw
    -- h_raw : parseYamlRaw "{}" = .ok raw_docs
    have h_check := checkContentMap_true
    unfold checkContentMap at h_check
    simp only [h_raw] at h_check
    have h_pairs_empty : pairs = #[] := by
      exact Array.toList_eq_nil_iff.mp h_list
    rw [h_pairs_empty]
    have h_sz_beq : (raw_docs.size == 1) = true := by simp [h_size]
    rw [h_sz_beq, Bool.true_and] at h_check
    exact h_check
  | _ :: _ =>
    -- Non-empty: requires exact parsed value structure from parser trace.
    exact sorry

/-- **Content fidelity**: Parsing canonical emitter output recovers content
    equivalent to the original value.

    The canonical emitter produces double-quoted scalars, flow-style
    collections, and no aliases/tags/anchors. Parsing this output yields
    values with the same string content for scalars and the same tree
    structure for collections, differing only in style annotations.
    Since `contentEq` ignores style, the parsed result is
    content-equivalent to the original.

    **Proof strategy**: Structural induction on `v`:
    - Scalar: `escapeString` round-trips through the scanner's
      `collectDoubleQuotedLoop` + `processEscape`, recovering the
      original content string. `contentEq` ignores scalar style.
    - Sequence: By IH each element round-trips content-equivalently.
      The parser reconstructs the list from flow tokens.
    - Mapping: By IH each key/value round-trips content-equivalently.
      The parser reconstructs pairs from flow tokens. -/
theorem emit_roundtrip_content_eq (v : YamlValue) {b : Bool} (hg : Grammable v b)
    (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit v) = .ok raw_docs)
    (h_size : raw_docs.size = 1) :
    contentEq v (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  induction hg generalizing raw_docs with
  | scalar s _ h_scannable =>
    -- emit (.scalar s) = emitScalar s.content
    -- The scanner produces tokens with the original content
    -- The parser produces a scalar value with the original content
    -- compose preserves content (only clears anchor)
    -- contentEq ignores style/tag/anchor, compares content only
    change contentEq (.scalar s) _ = true
    obtain ⟨s_parsed, h_val, h_content⟩ :=
      parseYamlRaw_emitScalar_value s.content raw_docs
        (by show parseYamlRaw (emit (.scalar s)) = _; exact h_raw)
    have h_compose := compose_scalar_content raw_docs[0]! s_parsed h_val
    -- (raw_docs.map YamlDocument.compose)[0]!.value = (raw_docs[0]!.compose).value
    have h0 : (0 : Nat) < raw_docs.size := by omega
    have h0' : (0 : Nat) < (raw_docs.map YamlDocument.compose).size := by
      rw [Array.size_map]; omega
    rw [show (raw_docs.map YamlDocument.compose)[0]!.value =
        (raw_docs[0]!.compose).value from by
      show (if h : 0 < (raw_docs.map YamlDocument.compose).size
            then (raw_docs.map YamlDocument.compose)[0] else default).value =
           (if h : 0 < raw_docs.size then raw_docs[0] else default).compose.value
      rw [dif_pos h0', dif_pos h0, Array.getElem_map]]
    rw [h_compose]
    exact contentEq_scalar_compose s { s_parsed with anchor := none } (by simp [h_content])

  | sequence style items tag anchor _ h_items ih =>
    -- IH is now available: each child element round-trips content-equivalently
    exact emit_roundtrip_sequence_content_eq style items tag anchor raw_docs h_raw h_size h_items ih

  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    -- IHs are now available: each key and value round-trips content-equivalently
    exact emit_roundtrip_mapping_content_eq style pairs tag anchor raw_docs h_raw h_size hk hv ihk ihv

/-- **Universal round-trip**: For every grammable YAML value, emitting it
    and re-parsing produces a single document whose value is
    content-equivalent to the original.

    This is the main theorem of v0.4.7 (Phase E). It composes:
    - Step 1: `emit_produces_valid_yaml` (scanner accepts emitter output)
    - Step 2: `parseStream_accepts_emit_tokens` (parser accepts scanned tokens)
    - Step 3a: `emit_produces_single_document` (exactly one document)
    - Step 3b: `emit_roundtrip_content_eq` (content fidelity) -/
theorem universal_roundtrip (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYaml (emit v) = .ok docs ∧
            docs.size = 1 ∧
            contentEq v docs[0]!.value = true := by
  obtain ⟨raw_docs, h_raw⟩ := emit_parse_succeeds v hg
  have h_raw_size := emit_produces_single_document v hg raw_docs h_raw
  refine ⟨raw_docs.map YamlDocument.compose, ?_, ?_, ?_⟩
  · simp only [parseYaml, h_raw]
  · simp [Array.size_map, h_raw_size]
  · exact emit_roundtrip_content_eq v hg raw_docs h_raw h_raw_size

end L4YAML.Proofs.EmitterScannability
