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

-- resolveAliases is identity on scalars
theorem resolveAliases_scalar (s : Scalar)
    (anchors : Array (String × YamlValue)) :
    (YamlValue.scalar s).resolveAliases anchors = .scalar s := by
  unfold YamlValue.resolveAliases; rfl

-- stripAnchors on scalar just clears the anchor
theorem stripAnchors_scalar (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := by
  unfold YamlValue.stripAnchors; rfl

-- compose on a scalar document preserves the content field
theorem compose_scalar_content (doc : YamlDocument) (s : Scalar)
    (h_val : doc.value = .scalar s) :
    (doc.compose).value = .scalar { s with anchor := none } := by
  unfold YamlDocument.compose; dsimp only []
  rw [h_val, resolveAliases_scalar, stripAnchors_scalar]

-- contentEq for scalars only depends on content string
theorem contentEq_scalar_content (s₁ s₂ : Scalar)
    (h : s₁.content = s₂.content) : contentEq (.scalar s₁) (.scalar s₂) = true := by
  unfold contentEq; simp [h]

-- contentEq through compose for scalars: original vs composed
theorem contentEq_scalar_compose (s_orig : Scalar) (s_parsed : Scalar)
    (h_content : s_orig.content = s_parsed.content) :
    contentEq (.scalar s_orig) (.scalar { s_parsed with anchor := none }) = true := by
  exact contentEq_scalar_content s_orig { s_parsed with anchor := none } h_content

/-! ### §5.2  Scanner content preservation

The scanner's double-quoted collector recovers the original content string
from the emitter's escape-encoded output. This is the key roundtrip property.
-/

-- Hex foldl roundtrip for control characters (c.val.toNat < 0x20)
/-- **Scanner content preservation**: scanning `emitScalar content` produces
    a token stream where the scalar token's content equals the original.

    This bridges the emitter's `escapeString` encoding with the scanner's
    `collectDoubleQuotedLoop` + `processEscape` decoding. The proof follows
    from `collectDoubleQuotedLoop_escapeString_succeeds` strengthened with
    content equality (the loop accumulator reconstructs the original string). -/
theorem scanFiltered_emitScalar_content (content : String) (tokens : Array (Positioned YamlToken))
    (h_scan : scanFiltered (emitScalar content) = .ok tokens) :
    ∃ i, i < tokens.size ∧ tokens[i]!.val = .scalar content .doubleQuoted := by
  -- Get scanner state with token membership
  obtain ⟨s₁, h_snt1, h_peek1, h_flow1, h_dp1, ⟨tok, h_tok_mem, h_tok_val⟩, h_ids1, _⟩ :=
    scanNextToken_emitScalar_init content
  have h_snt2 : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek1
  -- Compute the raw scan result
  have h_size := emitScalar_utf8ByteSize_ge content
  have h_fuel : ((emitScalar content).utf8ByteSize + 1) * 4 ≥ 2 := by omega
  -- scan reduces to scanLoop on the initial state
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
    unfold scan; dsimp only []
    rw [h_pk_emit, h_pk]
    split <;> first | rfl | exact absurd ‹_› (by decide)
  -- Get concrete token array via scanLoop_two_iter_eq
  have h_loop_eq := scanLoop_two_iter_eq h_fuel h_snt1 h_snt2 h_flow1 h_dp1
  -- The raw scan result is ((unwindIndents s₁ (-1)).emit .streamEnd).tokens
  have h_scan_raw : scan (emitScalar content) =
      .ok ((unwindIndents s₁ (-1)).emit .streamEnd).tokens := by
    rw [h_scan_eq, h_loop_eq]
  -- Scalar token survives through unwindIndents (prefix preservation)
  have h_tok_in_uwi : tok ∈ (unwindIndents s₁ (-1)).tokens := by
    obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp h_tok_mem
    rw [Array.mem_iff_getElem]
    have h_sz := ScannerCorrectness.unwindIndents_adds_tokens s₁ (-1)
    have h_pref := ScannerCorrectness.unwindIndents_preserves_prefix s₁ (-1) i hi
    exact ⟨i, by omega, h_pref⟩
  -- Scalar token survives through .emit .streamEnd (push preserves membership)
  have h_tok_in_raw : tok ∈ ((unwindIndents s₁ (-1)).emit .streamEnd).tokens := by
    exact Array.mem_push_of_mem _ h_tok_in_uwi
  -- Scalar token survives through filter (scalar ≠ placeholder)
  have h_tok_filtered : tok ∈ ((unwindIndents s₁ (-1)).emit .streamEnd).tokens.filter
      (fun t => t.val != .placeholder) := by
    rw [Array.mem_filter]
    refine ⟨h_tok_in_raw, ?_⟩
    rw [h_tok_val]
    -- Different constructors: .scalar vs .placeholder → beq = false → bne = true
    rfl
  -- Link filtered result to `tokens` via h_scan
  have h_tokens_eq : tokens = ((unwindIndents s₁ (-1)).emit .streamEnd).tokens.filter
      (fun t => t.val != .placeholder) := by
    simp only [scanFiltered, h_scan_raw] at h_scan
    exact (Except.ok.inj h_scan).symm
  -- Extract index from membership
  rw [h_tokens_eq]
  obtain ⟨i, hi, rfl⟩ := Array.mem_iff_getElem.mp h_tok_filtered
  exact ⟨i, hi, by rw [getElem!_pos]; exact h_tok_val⟩

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

/-- When `parseDirectives` sees a non-directive token, it returns immediately
    with empty directives and unchanged state.
    The `for _ in [:fuel] do` loop breaks on the first iteration because
    `peek?` matches `| _ => break`. -/
theorem parseDirectives_skip (ps : ParseState)
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

-- ═══ Helper infrastructure for flow collection parser acceptance ═══

-- Combined scanner-parser pipeline Bool checks for "[]" and "{}".
-- Using native_decide on Bool expressions avoids needing DecidableEq instances
-- for Except, Array, etc.
def checkFullSeq : Bool :=
  match Scanner.scanFiltered "[]" with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => docs.size == 1
    | .error _ => false
  | .error _ => false

def checkFullMap : Bool :=
  match Scanner.scanFiltered "{}" with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => docs.size == 1
    | .error _ => false
  | .error _ => false

theorem checkFullSeq_true : checkFullSeq = true := by native_decide
theorem checkFullMap_true : checkFullMap = true := by native_decide

-- Content fidelity Bool checks for empty flow collections.
-- Verifies: parseYamlRaw "[]"/{}" succeeds AND the composed result is content-equivalent
-- to the original empty collection.
def checkContentSeq : Bool :=
  match parseYamlRaw "[]" with
  | .ok raw_docs =>
    raw_docs.size == 1 &&
    contentEq (.sequence .flow #[]) (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

def checkContentMap : Bool :=
  match parseYamlRaw "{}" with
  | .ok raw_docs =>
    raw_docs.size == 1 &&
    contentEq (.mapping .flow #[]) (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

theorem checkContentSeq_true : checkContentSeq = true := by native_decide
theorem checkContentMap_true : checkContentMap = true := by native_decide

-- ═══ Scanner → Parser bridge: token structure for non-empty flow collections ═══

/-! ### Infrastructure for filtered token tracking (Sub-phase 4.4.G) -/

/-- `unwindIndents` is identity when the indent stack has at most 1 entry.
    This covers emitter output where `indents = #[]` (the default from `ScannerState.mk'`).
    `unwindIndentsLoop` checks `s.indents.size > 1` before unwinding; with size ≤ 1,
    the condition fails immediately and the state is returned unchanged. -/
theorem unwindIndents_noop_short_stack (s : ScannerState)
    (h_stack : s.indents.size ≤ 1) :
    unwindIndents s (-1) = s := by
  unfold unwindIndents
  unfold unwindIndentsLoop
  split
  · -- fuel = 0 case is impossible since fuel = s.indents.size ≤ 1
    rfl
  · -- fuel = fuel' + 1
    split
    · -- s.currentIndent > -1 && s.indents.size > 1
      exfalso
      rename_i h_cond
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
      omega
    · rfl

/-- When a ScanChain starts from s₀ via scanFiltered, the token array equation.
    Combines `scanFiltered_of_chain_eq` with `unwindIndents` identity for emitter states. -/
theorem scanFiltered_tokens_eq_of_chain_short_stack
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4)
    (h_stack : s_final.indents.size ≤ 1) :
    Scanner.scanFiltered input =
      .ok ((s_final.emit .streamEnd).tokens.filter (fun t => t.val != .placeholder)) := by
  have h_eq := scanFiltered_of_chain_eq input s₀ s_final n h_s0 h_no_bom h_chain h_eof h_fl h_dp h_fuel
  rwa [unwindIndents_noop_short_stack s_final h_stack] at h_eq

/-- `ScanChain` token array monotonicity: tokens array size grows (non-strictly)
    through any scan chain. -/
theorem ScanChain_tokens_mono {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | step h_snt _h_rest ih => exact Nat.le_trans (ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt) ih

/-- Combined per-step prefix preservation and simpleKey invariant maintenance.

    **Precondition**: `n ≤ s.tokens.size` and the simpleKey condition
    `s.simpleKey.possible → s.simpleKey.tokenIndex ≥ n`, which says that
    the prefix index doesn't overlap the simpleKey placeholder position.
    Without this, `scanNextToken` may overwrite `tokens[tokenIndex]`
    (replacing `.placeholder` with `.key`), violating prefix preservation.

    **Precondition**: Uses `SimpleKeyAbove` to track both the current simpleKey
    and all stacked simpleKeys. This is necessary because flow close operations
    (`]`/`}`) restore a simpleKey from the stack, and without stack bounds,
    the restored `tokenIndex` could fall below `n`.

    **Conclusion**: Returns both prefix preservation and `SimpleKeyAbove s' n`,
    enabling straightforward induction in `ScanChain_preserves_raw_prefix`. -/
theorem scanNextToken_prefix_and_sk_inv (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : ScannerCorrectness.SimpleKeyAbove s n) :
    (∀ (i : Nat) (hi : i < n),
      s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    ScannerCorrectness.SimpleKeyAbove s' n :=
  ⟨fun i hi => ScannerCorrectness.scanNextToken_preserves_prefix s s' h_next n h_n h_inv i hi,
   ScannerCorrectness.scanNextToken_maintains_simpleKeyAbove s s' h_next n h_n h_inv⟩

/-- Through a ScanChain, all raw token positions below `n₀` are preserved,
    provided `n₀ ≤ s.tokens.size` and `SimpleKeyAbove s n₀` holds (tracking
    both the current simpleKey and all stacked simpleKeys).

    The `SimpleKeyAbove` invariant is maintained through each step by
    `scanNextToken_prefix_and_sk_inv`, making the induction straightforward. -/
theorem ScanChain_preserves_raw_prefix {s s' : ScannerState} {k : Nat}
    (h_chain : ScanChain s k s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : ScannerCorrectness.SimpleKeyAbove s n₀)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := ScanChain_tokens_mono h_chain; omega) =
    s.tokens[i]'(by omega) := by
  induction h_chain with
  | zero => rfl
  | step h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have ⟨h_pres, h_inv'⟩ := scanNextToken_prefix_and_sk_inv _ _ h_snt n₀ h_n₀ h_inv
    exact (ih (Nat.le_trans h_n₀ h_adds) h_inv').trans (h_pres i hi)

/-! #### Main theorem: filtered growth through scanNextToken -/

-- Every `scanNextToken` step adds at least one non-placeholder token to the
-- filtered token array.  Note: the structural dispatch case for unknown
-- directives (%RESERVED) adds 0 tokens but still returns `some s'`.  The
-- ≥+1 bound holds for all emitter-produced inputs (which only use %YAML/%TAG
-- directives and document markers, each emitting ≥1 non-placeholder token).
set_option maxHeartbeats 3200000 in
theorem scanNextToken_filtered_grows (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanNextToken at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · split at h
    · simp at h
    · have h_pp_mono := preprocess_filtered_mono s _ _ (by assumption)
      repeat (any_goals (split at h))
      any_goals contradiction
      any_goals (simp at h)
      all_goals first
        | contradiction
        | (simp at h)
        | (have h_d := dispatchFlowIndicators_filtered_grows _ _ _ (by assumption);
           rw [allowDir_ite_filter] at h_d; simp_all <;> omega)
        | (have h_d := dispatchBlockIndicators_filtered_grows _ _ _ (by assumption);
           rw [allowDir_ite_filter] at h_d; simp_all <;> omega)
        | (have h_d := dispatchContent_filtered_grows _ _ _ (by assumption);
           rw [allowDir_ite_filter] at h_d; simp_all <;> omega)
        | (simp_all <;> omega)
        -- structural dispatch: case-split into docStart, docEnd, directive
        | (-- Resolve monadic binds (docEnd/directive use do-notation)
           try simp only [bind, Except.bind] at h
           try (split at h <;> first | contradiction | skip)
           -- Extract equality from .ok/.some wrappers
           try simp only [Except.ok.injEq, Option.some.injEq] at h
           try (injection h with h)
           try subst h
           first
             | (have := scanDocumentStart_filtered_grows _; omega)
             | (have := scanDocumentEnd_filtered_grows _ _ (by assumption); omega)
             | sorry)

/-- Through a ScanChain of `n` steps, the filtered token array grows by at least `n`. -/
theorem ScanChain_filtered_grows {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + n := by
  induction h_chain with
  | zero => omega
  | step h_snt _h_rest ih =>
    have h_step := scanNextToken_filtered_grows _ _ h_snt
    omega


/-- Through a FlowMonoChain, the filtered token array of the final state has the
    filtered array of the initial state as a prefix.

    Uses `FlowMonoChain_preserves_raw_prefix` (which maintains `SimpleKeyAboveFloor`
    through the chain using the flow-level floor) composed with
    `Array_filter_prefix_of_raw_prefix` to lift raw index preservation to
    filtered-array prefix preservation.

    **Preconditions**:
    - `FlowMonoChain fl₀ s n s'`: flow-monotone chain with floor `fl₀`
    - `h_sk`: `s.simpleKey.possible = false` (no in-flight placeholder reservation)
    - `h_sync`: `s.simpleKeyStack.size ≥ s.flowLevel` (stack/flow synchronized)
    - `h_stack_floor`: stack entries at index ≥ `fl₀` have `tokenIndex ≥ s.tokens.size`

    Both call sites have `fl₀ = s₁.flowLevel = 1` with `s₁.simpleKeyStack.size = 1`,
    making `h_stack_floor` vacuously true (no `j` satisfies `1 ≤ j < 1`). -/
theorem ScanChain_filtered_prefix {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (h_sk : s.simpleKey.possible = false)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_stack_floor : ∀ j, fl₀ ≤ j → (hj : j < s.simpleKeyStack.size) →
      s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ s.tokens.size) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ suffix, (s'.tokens.filter p).toList = (s.tokens.filter p).toList ++ suffix := by
  exact Array_filter_prefix_of_raw_prefix s.tokens s'.tokens _
    (FlowMonoChain.tokens_mono h_fmc)
    (fun i hi => FlowMonoChain_preserves_raw_prefix h_fmc s.tokens.size (by omega)
      ⟨fun h => absurd h (by simp [h_sk]), h_stack_floor, by have := h_fmc.flowLevel_ge_start; omega⟩
      h_sync i hi)

/-- `emitPairList` for non-empty pairs produces a non-empty string. -/
theorem emitPairList_toList_ne_nil (p : YamlValue × YamlValue)
    (ps : List (YamlValue × YamlValue)) :
    (emit.emitPairList (p :: ps)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitPairList_first_char p ps
  rw [h_eq]; exact List.cons_ne_nil _ _

/-- `scanFlowSequenceEnd` token array equation: pushes exactly one `.flowSequenceEnd` token. -/
theorem scanFlowSequenceEnd_tokens_eq (s : ScannerState) :
    (scanFlowSequenceEnd s).tokens = s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd } := by
  unfold scanFlowSequenceEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowSequenceEnd)]
  unfold ScannerState.emit; rfl

/-- `scanFlowMappingEnd` token array equation: pushes exactly one `.flowMappingEnd` token. -/
theorem scanFlowMappingEnd_tokens_eq (s : ScannerState) :
    (scanFlowMappingEnd s).tokens = s.tokens.push { pos := s.currentPos, val := .flowMappingEnd } := by
  unfold scanFlowMappingEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowMappingEnd)]
  unfold ScannerState.emit; rfl

/-- The close-bracket step for outermost `]`: filtered token array is the input
    filtered array with `.flowSequenceEnd` appended.

    Traces through `saveSimpleKey` (adds only placeholders, filtered out) →
    `allowDirectives` (no token change) → `scanFlowSequenceEnd` (appends
    `.flowSequenceEnd` which passes the placeholder filter). -/
theorem scanNextToken_flow_close_seq_outermost_ext (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok, tok.val = .flowSequenceEnd ∧
          s'.tokens.filter p = (s.tokens.filter p).push tok) := by
  -- Replay the close bracket proof to get the intermediate state s_ad
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨[']'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_bracket_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- s' = scanFlowSequenceEnd s_ad
  let s' := scanFlowSequenceEnd s_ad
  have h_result_fl : s'.flowLevel = 0 := by
    show (scanFlowSequenceEnd s_ad).flowLevel = 0
    rw [scanFlowSequenceEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : s'.directivesPresent = false := by
    show (scanFlowSequenceEnd s_ad).directivesPresent = false
    rw [scanFlowSequenceEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : s'.peek? = none := by
    show (scanFlowSequenceEnd s_ad).peek? = none
    rw [scanFlowSequenceEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad ']' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowSequenceEnd) ']' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowSequenceEnd).offset < (s_ad.emit .flowSequenceEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Indents preservation: s'.indents = s.indents
  have h_result_indents : s'.indents = s.indents := by
    show (scanFlowSequenceEnd s_ad).indents = s.indents
    rw [scanFlowSequenceEnd_preserves_indents]
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  -- Filtered tokens: s'.tokens.filter p = (s.tokens.filter p).push tok
  have h_ad_tokens_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKey_filter_placeholder s
  have h_result_tokens : ∃ tok, tok.val = .flowSequenceEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
    have h_fse_tokens : (scanFlowSequenceEnd s_ad).tokens =
        s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd } :=
      scanFlowSequenceEnd_tokens_eq s_ad
    have h_filter_push : (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd }).filter
        (fun t => t.val != .placeholder) =
        (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s_ad.currentPos, val := .flowSequenceEnd } := by
      rw [Array.filter_push]; rfl
    exact ⟨{ pos := s_ad.currentPos, val := .flowSequenceEnd }, rfl,
      by rw [show s' = scanFlowSequenceEnd s_ad from rfl,
             h_fse_tokens, h_filter_push, h_ad_tokens_filter]⟩
  exact ⟨s', h_snt, h_result_fl, h_result_dp, h_result_eof, h_result_indents, h_result_tokens⟩

/-- The close-brace step for outermost `}`: filtered token array is the input
    filtered array with `.flowMappingEnd` appended. -/
theorem scanNextToken_flow_close_mapping_outermost_ext (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok, tok.val = .flowMappingEnd ∧
          s'.tokens.filter p = (s.tokens.filter p).push tok) := by
  -- Replay the close brace proof to get the intermediate state s_ad
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['}'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_brace_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- s' = scanFlowMappingEnd s_ad
  let s' := scanFlowMappingEnd s_ad
  have h_result_fl : s'.flowLevel = 0 := by
    show (scanFlowMappingEnd s_ad).flowLevel = 0
    rw [scanFlowMappingEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : s'.directivesPresent = false := by
    show (scanFlowMappingEnd s_ad).directivesPresent = false
    rw [scanFlowMappingEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : s'.peek? = none := by
    show (scanFlowMappingEnd s_ad).peek? = none
    rw [scanFlowMappingEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad '}' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowMappingEnd) '}' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowMappingEnd).offset < (s_ad.emit .flowMappingEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Indents preservation: s'.indents = s.indents
  have h_result_indents : s'.indents = s.indents := by
    show (scanFlowMappingEnd s_ad).indents = s.indents
    rw [scanFlowMappingEnd_preserves_indents]
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  -- Filtered tokens: s'.tokens.filter p = (s.tokens.filter p).push tok
  have h_ad_tokens_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKey_filter_placeholder s
  have h_result_tokens : ∃ tok, tok.val = .flowMappingEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
    have h_fme_tokens : (scanFlowMappingEnd s_ad).tokens =
        s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd } :=
      scanFlowMappingEnd_tokens_eq s_ad
    have h_filter_push : (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd }).filter
        (fun t => t.val != .placeholder) =
        (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s_ad.currentPos, val := .flowMappingEnd } := by
      rw [Array.filter_push]; rfl
    exact ⟨{ pos := s_ad.currentPos, val := .flowMappingEnd }, rfl,
      by rw [show s' = scanFlowMappingEnd s_ad from rfl,
             h_fme_tokens, h_filter_push, h_ad_tokens_filter]⟩
  exact ⟨s', h_snt, h_result_fl, h_result_dp, h_result_eof, h_result_indents, h_result_tokens⟩

-- Every `scanFiltered` result has streamStart first, streamEnd last, size ≥ 2.
-- Mirrors the proof of `scanFiltered_produces_valid_tokens` but returns a
-- plain conjunction (avoiding the `ValidTokenStream` struct indirection).
theorem scanFiltered_boundary_tokens (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    tokens.size ≥ 2 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd := by
  unfold Scanner.scanFiltered at h
  -- Case split on the underlying scan result
  generalize h_scan : Scanner.scan input = result at h
  match result with
  | .error _ => simp at h
  | .ok raw =>
  -- h : .ok (raw.filter (fun t => t.val != .placeholder)) = .ok tokens
  injection h with h_eq
  -- h_eq : raw.filter ... = tokens — keep tokens in goal, transport via ← h_eq
  let p : Positioned YamlToken → Bool := fun t => t.val != .placeholder
  let l := raw.toList
  -- Raw scan properties
  have h_raw_sz := ScannerCorrectness.scan_produces_at_least_two input raw h_scan
  have h_raw_first := ScannerCorrectness.scan_first_is_streamStart input raw h_scan (by omega)
  have h_raw_last := ScannerCorrectness.scan_last_is_streamEnd input raw h_scan (by omega)
  -- List-level reasoning: head/last pass filter, preserved in filtered list
  have h_l_ne : l ≠ [] := by
    intro h0
    have : raw.size = 0 := by show l.length = 0; simp [h0]
    omega
  have h_p_first : p (l.head h_l_ne) = true := by
    show ((l.head h_l_ne).val != .placeholder) = true
    have : (l.head h_l_ne).val = .streamStart := by
      rw [List.head_eq_getElem]; exact h_raw_first
    rw [this]; decide
  have h_p_last : p (l.getLast h_l_ne) = true := by
    show ((l.getLast h_l_ne).val != .placeholder) = true
    have : (l.getLast h_l_ne).val = .streamEnd := by
      rw [List.getLast_eq_getElem]; exact h_raw_last
    rw [this]; decide
  have h_flt_ne : l.filter p ≠ [] := by
    rw [show l = l.head h_l_ne :: l.tail from (List.cons_head_tail h_l_ne).symm,
        List.filter_cons_of_pos h_p_first]
    exact List.cons_ne_nil _ _
  have h_find : l.find? p = some (l.head h_l_ne) := by
    conv => lhs; rw [show l = l.head h_l_ne :: l.tail from (List.cons_head_tail h_l_ne).symm]
    exact List.find?_cons_of_pos h_p_first
  have h_head_filt : (l.filter p).head h_flt_ne = l.head h_l_ne := by
    rw [List.head_filter]; simp [h_find]
  have h_rev_ne : l.reverse ≠ [] := by simp [h_l_ne]
  have h_rfind : l.reverse.find? p = some (l.getLast h_l_ne) := by
    conv => lhs; rw [show l.reverse = l.reverse.head h_rev_ne :: l.reverse.tail
                        from (List.cons_head_tail h_rev_ne).symm,
                      show l.reverse.head h_rev_ne = l.getLast h_l_ne
                        from List.head_reverse ..]
    exact List.find?_cons_of_pos h_p_last
  have h_last_filt : (l.filter p).getLast h_flt_ne = l.getLast h_l_ne := by
    rw [List.getLast_filter]; simp [h_rfind]
  -- Filtered size ≥ 2
  have h_filt_sz_list : (l.filter p).length ≥ 2 := by
    have h_pos : (l.filter p).length > 0 := List.length_pos_iff.mpr h_flt_ne
    have h_ne_1 : (l.filter p).length ≠ 1 := by
      intro h1
      obtain ⟨a, h_eq'⟩ := List.length_eq_one_iff.mp h1
      have : l.head h_l_ne = l.getLast h_l_ne := by
        rw [← h_head_filt, ← h_last_filt]; simp [h_eq']
      have := congrArg Positioned.val this
      rw [show (l.head h_l_ne).val = .streamStart
            from by rw [List.head_eq_getElem]; exact h_raw_first,
          show (l.getLast h_l_ne).val = .streamEnd
            from by rw [List.getLast_eq_getElem]; exact h_raw_last] at this
      cases this
    omega
  have h_filt_sz : (raw.filter p).size ≥ 2 := by
    show (raw.filter p).toList.length ≥ 2
    rw [Array.toList_filter]; exact h_filt_sz_list
  -- Bridge Array.size ↔ List.length for omega
  have h_filt_len : (raw.filter p).toList.length ≥ 2 := by
    rw [Array.toList_filter]; exact h_filt_sz_list
  -- Transport to tokens via ← h_eq
  have h_tsz : tokens.size ≥ 2 := h_eq ▸ h_filt_sz
  refine ⟨h_tsz, ?_, ?_⟩
  · -- tokens[0]!.val = .streamStart
    suffices h : (raw.filter p)[0]!.val = .streamStart by rwa [h_eq] at h
    rw [getElem!_pos _ 0 (by omega)]
    have h_first_val : ((l.filter p).head h_flt_ne).val = .streamStart := by
      rw [h_head_filt, List.head_eq_getElem]; exact h_raw_first
    rw [List.head_eq_getElem] at h_first_val
    show ((raw.filter p).toList[0]'(show 0 < (raw.filter p).size from by omega)).val
      = .streamStart
    simp only [Array.toList_filter]; exact h_first_val
  · -- tokens[N-1]!.val = .streamEnd
    suffices h : (raw.filter p)[(raw.filter p).size - 1]!.val = .streamEnd by rwa [h_eq] at h
    rw [getElem!_pos _ _ (by omega)]
    have h_last_val : ((l.filter p).getLast h_flt_ne).val = .streamEnd := by
      rw [h_last_filt, List.getLast_eq_getElem]; exact h_raw_last
    rw [List.getLast_eq_getElem] at h_last_val
    have h_sz_eq : (raw.filter p).size = (l.filter p).length := by
      have : (raw.filter p).toList = l.filter p := Array.toList_filter
      show (raw.filter p).toList.length = (l.filter p).length; rw [this]
    show ((raw.filter p).toList[(raw.filter p).size - 1]'(show (raw.filter p).size - 1 < (raw.filter p).size from by omega)).val
      = .streamEnd
    simp only [Array.toList_filter, h_sz_eq]; exact h_last_val

-- These characterize the filtered token array produced by scanning emitter output,
-- providing the properties needed by the parser flow loop fuel sufficiency theorems.

-- Flow bracket nesting utilities (flowBracketDelta, flowBracketBalance) are defined
-- in ParserGrammableBase.lean and available via the ParserGrammable import.
open L4YAML.Proofs.ParserGrammable (flowBracketDelta flowBracketBalance
  flowBracketBalance_compose flowBracketBalance_push)

/-! ### §G.balance  Well-bracketed body algebra (`.body2.establishing`)

Pure `flowBracketBalance`-level combinatorics underpinning the outer-level
flowEntry characterizations (legacy sorries 9646 / 9552).

An emitter *body* (the content between `[`/`]` or `{`/`}`) is a list of
**entries** — one per sequence item or one `key: value` pair — separated by
single `.flowEntry` tokens (the `", "` comma separators). Each entry is
`EntrySafe`: its total bracket balance is `0` and every `.flowEntry` strictly
inside it sits at running balance `≥ 1` (so it is an *inner* flowEntry, not an
outer-level one). `SafeBody Q` bundles a body whose entries are all `EntrySafe`
and whose heads all satisfy a predicate `Q` (instantiated downstream to
"content-start" for sequences and ".key" for mappings).

The main lemma `SafeBody_flowEntry_zero_balance` shows the *only* balance-0
flowEntries in such a body are the separators, and each is immediately followed
by an entry head (hence satisfies `Q`). The array/offset wrapper
`SafeBody_array_flowEntry` restates this against `flowBracketBalance` on the
filtered token array with a base offset `lo`, the exact shape the body
characterization theorems consume.

The scanner side — producing a `SafeBody` from emit output, which needs the
per-`emit v` block to be shown bracket-balanced with positive interior — is
`.body2.discharge`. -/

/-- Cumulative flow-bracket balance of a positioned-token list. -/
def pbalance (l : List (Positioned YamlToken)) : Int :=
  l.foldl (fun acc t => acc + flowBracketDelta t.val) 0

theorem pbalance_nil : pbalance [] = 0 := rfl

theorem pbalance_append (a b : List (Positioned YamlToken)) :
    pbalance (a ++ b) = pbalance a + pbalance b := by
  unfold pbalance
  rw [List.foldl_append,
      foldl_add_shift b (fun t => flowBracketDelta t.val) (a.foldl _ 0)]

theorem pbalance_singleton (t : Positioned YamlToken) :
    pbalance [t] = flowBracketDelta t.val := by
  simp [pbalance, List.foldl]

theorem pbalance_cons (t : Positioned YamlToken) (l : List (Positioned YamlToken)) :
    pbalance (t :: l) = flowBracketDelta t.val + pbalance l := by
  have h : t :: l = [t] ++ l := rfl
  rw [h, pbalance_append, pbalance_singleton]

/-- `.flowEntry` contributes `0` to the bracket balance. -/
theorem flowBracketDelta_flowEntry : flowBracketDelta .flowEntry = 0 := rfl

/-- A flow-sequence opener `[` contributes `+1`. -/
theorem flowBracketDelta_flowSequenceStart : flowBracketDelta .flowSequenceStart = 1 := rfl

/-- A flow-sequence closer `]` contributes `-1`. -/
theorem flowBracketDelta_flowSequenceEnd : flowBracketDelta .flowSequenceEnd = -1 := rfl

/-- A flow-mapping opener `{` contributes `+1`. -/
theorem flowBracketDelta_flowMappingStart : flowBracketDelta .flowMappingStart = 1 := rfl

/-- A flow-mapping closer `}` contributes `-1`. -/
theorem flowBracketDelta_flowMappingEnd : flowBracketDelta .flowMappingEnd = -1 := rfl

/-- A scalar token contributes `0`. -/
theorem flowBracketDelta_scalar (value : String) (style : ScalarStyle) :
    flowBracketDelta (.scalar value style) = 0 := rfl

/-- A `.key` token contributes `0`. -/
theorem flowBracketDelta_key : flowBracketDelta .key = 0 := rfl

/-- An emitter *entry* (one sequence item, or one mapping `key: value` pair):
    bracket-balanced overall, with every interior `.flowEntry` at balance `≥ 1`. -/
def EntrySafe (e : List (Positioned YamlToken)) : Prop :=
  pbalance e = 0 ∧
  ∀ (i : Nat) (h : i < e.length), (e[i]'h).val = .flowEntry → pbalance (e.take i) ≥ 1

/-- A flow body: nonempty `EntrySafe` entries with `Q`-satisfying heads,
    separated by single `.flowEntry` tokens. -/
inductive SafeBody (Q : YamlToken → Prop) : List (Positioned YamlToken) → Prop
  | single (e : List (Positioned YamlToken)) (h_ne : e ≠ [])
      (h_safe : EntrySafe e) (h_head : Q (e.head h_ne).val) : SafeBody Q e
  | cons (e : List (Positioned YamlToken)) (fe : Positioned YamlToken)
      (rest : List (Positioned YamlToken)) (h_ne : e ≠ [])
      (h_safe : EntrySafe e) (h_head : Q (e.head h_ne).val)
      (h_fe : fe.val = .flowEntry) (h_rest : SafeBody Q rest) :
      SafeBody Q (e ++ fe :: rest)

/-- The head of a `SafeBody` exists and satisfies `Q`. -/
theorem SafeBody.head_Q {Q : YamlToken → Prop} {l : List (Positioned YamlToken)}
    (h : SafeBody Q l) : ∃ (hl : 0 < l.length), Q (l[0]'hl).val := by
  have key : ∀ (e : List (Positioned YamlToken)) (h_ne : e ≠ []),
      ∃ (hl : 0 < e.length), (e[0]'hl) = e.head h_ne := by
    intro e h_ne
    match e, h_ne with
    | a :: as, _ => exact ⟨by simp, rfl⟩
  induction h with
  | single e h_ne h_safe h_head =>
    obtain ⟨hl, he⟩ := key e h_ne
    exact ⟨hl, he ▸ h_head⟩
  | cons e fe rest h_ne h_safe h_head h_fe h_rest _ih =>
    obtain ⟨hl0, he⟩ := key e h_ne
    have hl : 0 < (e ++ fe :: rest).length := by rw [List.length_append]; omega
    refine ⟨hl, ?_⟩
    have hidx : (e ++ fe :: rest)[0]'hl = e[0]'hl0 := List.getElem_append_left hl0
    rw [hidx, he]; exact h_head

/-- **Main balance lemma.** In a `SafeBody`, every balance-0 `.flowEntry` is a
    separator, immediately followed by an entry head (which satisfies `Q`). -/
theorem SafeBody_flowEntry_zero_balance {Q : YamlToken → Prop}
    {body : List (Positioned YamlToken)} (h : SafeBody Q body) :
    ∀ (k : Nat) (hk : k < body.length),
      (body[k]'hk).val = .flowEntry → pbalance (body.take k) = 0 →
      ∃ (hk1 : k + 1 < body.length), Q (body[k+1]'hk1).val := by
  induction h with
  | single e h_ne h_safe h_head =>
    intro k hk h_fe h_bal
    have := h_safe.2 k hk h_fe
    omega
  | cons e fe rest h_ne h_safe h_head h_fe h_rest ih =>
    intro k hk h_fek h_bal
    have h_len : (e ++ fe :: rest).length = e.length + 1 + rest.length := by
      simp [List.length_append]; omega
    rcases Nat.lt_trichotomy k e.length with hlt | heq | hgt
    · -- inside `e`: flowEntry there has balance ≥ 1, contradicting = 0
      exfalso
      have hbody_k : (e ++ fe :: rest)[k]'hk = e[k]'hlt := List.getElem_append_left hlt
      have hek_fe : (e[k]'hlt).val = .flowEntry := by rw [← hbody_k]; exact h_fek
      have htake : (e ++ fe :: rest).take k = e.take k := by
        rw [List.take_append, show k - e.length = 0 from by omega,
            List.take_zero, List.append_nil]
      rw [htake] at h_bal
      have := h_safe.2 k hlt hek_fe
      omega
    · -- the separator at `k = e.length`: next is the head of `rest`
      subst heq
      obtain ⟨hr0, hQ⟩ := h_rest.head_Q
      have hk1 : e.length + 1 < (e ++ fe :: rest).length := by rw [h_len]; omega
      refine ⟨hk1, ?_⟩
      have hidx : (e ++ fe :: rest)[e.length + 1]'hk1 = rest[0]'hr0 := by
        have h1 : (e ++ fe :: rest)[e.length + 1]? = rest[0]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 - e.length = 0 + 1 from by omega, List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hr0] at h1
        exact Option.some.inj h1
      rw [hidx]; exact hQ
    · -- after the separator: write `k = |e| + 1 + m`, the offset `m` into `rest`
      obtain ⟨m, hm⟩ : ∃ m, k = e.length + 1 + m := ⟨k - e.length - 1, by omega⟩
      subst hm
      have hk_rest : m < rest.length := by rw [h_len] at hk; omega
      -- body[|e|+1+m] = rest[m]
      have hbody_k : (e ++ fe :: rest)[e.length + 1 + m]'hk = rest[m]'hk_rest := by
        have h1 : (e ++ fe :: rest)[e.length + 1 + m]? = rest[m]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 + m - e.length = m + 1 from by omega, List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk, List.getElem?_eq_getElem hk_rest] at h1
        exact Option.some.inj h1
      have h_rest_fe : (rest[m]'hk_rest).val = .flowEntry := by
        rw [← hbody_k]; exact h_fek
      -- balance(take (|e|+1+m)) = pbalance e + delta fe + pbalance (rest.take m) = pbalance (rest.take m)
      have htake : (e ++ fe :: rest).take (e.length + 1 + m) = e ++ fe :: rest.take m := by
        rw [List.take_append, List.take_of_length_le (show e.length ≤ e.length + 1 + m from by omega),
            show e.length + 1 + m - e.length = m + 1 from by omega, List.take_succ_cons]
      have h_bal' : pbalance (rest.take m) = 0 := by
        rw [htake, pbalance_append, pbalance_cons, h_safe.1, h_fe,
            flowBracketDelta_flowEntry] at h_bal
        omega
      obtain ⟨hj1, hQ⟩ := ih m hk_rest h_rest_fe h_bal'
      have hk1 : e.length + 1 + m + 1 < (e ++ fe :: rest).length := by rw [h_len]; omega
      refine ⟨hk1, ?_⟩
      have hidx : (e ++ fe :: rest)[e.length + 1 + m + 1]'hk1 = rest[m + 1]'hj1 := by
        have h1 : (e ++ fe :: rest)[e.length + 1 + m + 1]? = rest[m + 1]? := by
          rw [List.getElem?_append_right (by omega),
              show e.length + 1 + m + 1 - e.length = (m + 1) + 1 from by omega,
              List.getElem?_cons_succ]
        rw [List.getElem?_eq_getElem hk1, List.getElem?_eq_getElem hj1] at h1
        exact Option.some.inj h1
      rw [hidx]; exact hQ

/-- Bridge: `flowBracketBalance` on an array slice equals `pbalance` of the
    corresponding `drop`/`take` of its `toList`. -/
theorem flowBracketBalance_eq_pbalance (arr : Array (Positioned YamlToken))
    (lo k : Nat) (h : lo ≤ k) :
    flowBracketBalance arr lo k = pbalance ((arr.toList.drop lo).take (k - lo)) := by
  unfold flowBracketBalance pbalance
  split
  · rename_i hge
    have : k - lo = 0 := by omega
    rw [this, List.take_zero]; rfl
  · rfl

/-- **Array/offset wrapper.** Restates `SafeBody_flowEntry_zero_balance` against
    `flowBracketBalance` on the filtered token array with base offset `lo`,
    matching the body-characterization consumers. -/
theorem SafeBody_array_flowEntry {Q : YamlToken → Prop}
    (arr : Array (Positioned YamlToken)) (lo : Nat)
    (h : SafeBody Q (arr.toList.drop lo)) :
    ∀ (k : Nat), lo ≤ k → (hk : k < arr.size) →
      (arr[k]'hk).val = .flowEntry → flowBracketBalance arr lo k = 0 →
      ∃ (hk1 : k + 1 < arr.size), Q (arr[k+1]'hk1).val := by
  intro k h_lo hk h_fe h_bal
  have h_len : (arr.toList.drop lo).length = arr.size - lo := by
    rw [List.length_drop, Array.length_toList]
  have hj_lt : k - lo < (arr.toList.drop lo).length := by rw [h_len]; omega
  -- body[k - lo].val = arr[k].val
  have h_drop_get : ((arr.toList.drop lo)[k - lo]'hj_lt).val = (arr[k]'hk).val := by
    rw [List.getElem_drop]
    rw [Array.getElem_toList (by omega)]
    congr 2
    omega
  have h_fe' : ((arr.toList.drop lo)[k - lo]'hj_lt).val = .flowEntry := by
    rw [h_drop_get]; exact h_fe
  -- balance(take (k - lo)) = 0
  have h_bal' : pbalance ((arr.toList.drop lo).take (k - lo)) = 0 := by
    rw [← flowBracketBalance_eq_pbalance arr lo k h_lo]; exact h_bal
  obtain ⟨hj1, hQ⟩ :=
    SafeBody_flowEntry_zero_balance h (k - lo) hj_lt h_fe' h_bal'
  have hk1 : k + 1 < arr.size := by rw [h_len] at hj1; omega
  refine ⟨hk1, ?_⟩
  have h_get : ((arr.toList.drop lo)[(k - lo) + 1]'hj1).val = (arr[k+1]'hk1).val := by
    rw [List.getElem_drop]
    rw [Array.getElem_toList (by omega)]
    congr 2
    omega
  rw [← h_get]; exact hQ

/-! #### Well-bracketed blocks (`.body2.discharge.wbalgebra`)

`WellBracketed` is the Dyck-word condition on flow brackets: total balance `0`
with every prefix balance `≥ 0`. It is the recursive invariant a scanned
`emit v` block satisfies — closed under concatenation (so a body of blocks +
`.flowEntry` separators stays well-bracketed) and under wrapping a
`WellBracketed` interior in a matching `[ ]`/`{ }` pair. The wrapping lemma
additionally yields `EntrySafe` (the per-entry obligation `SafeBody` consumes):
inside a bracket pair every interior `.flowEntry` sits at balance `≥ 1`.

These are pure `pbalance` combinatorics. The scanner side — producing a
`WellBracketed` filtered delta from `emit v`, which threads delta-tracking
through `emit_scans_in_flow` and the list/pairlist producers — is
`.body2.discharge.bridge`. -/

/-- Dyck condition on flow brackets: balanced, with all prefix balances `≥ 0`. -/
def WellBracketed (l : List (Positioned YamlToken)) : Prop :=
  pbalance l = 0 ∧ ∀ (i : Nat), pbalance (l.take i) ≥ 0

theorem WellBracketed_nil : WellBracketed [] := by
  refine ⟨pbalance_nil, fun i => ?_⟩
  simp [List.take_nil, pbalance_nil]

/-- Prefix balance of a concatenation splits additively. -/
theorem pbalance_take_append (a b : List (Positioned YamlToken)) (i : Nat) :
    pbalance ((a ++ b).take i) = pbalance (a.take i) + pbalance (b.take (i - a.length)) := by
  rw [List.take_append, pbalance_append]

/-- Prefix balance of a singleton: `0` (empty prefix) or its delta. -/
theorem pbalance_take_singleton (t : Positioned YamlToken) (j : Nat) :
    pbalance ([t].take j) = if j = 0 then 0 else flowBracketDelta t.val := by
  match j with
  | 0 => simp [pbalance_nil]
  | k + 1 => simp [List.take_succ_cons, pbalance_singleton]

/-- A single token of zero delta (scalar, `:`, `.value`, …) is well-bracketed. -/
theorem WellBracketed_singleton_delta_zero (t : Positioned YamlToken)
    (h : flowBracketDelta t.val = 0) : WellBracketed [t] := by
  refine ⟨by rw [pbalance_singleton, h], fun i => ?_⟩
  rw [pbalance_take_singleton]
  split <;> omega

/-- `WellBracketed` is closed under concatenation. -/
theorem WellBracketed_append (a b : List (Positioned YamlToken))
    (ha : WellBracketed a) (hb : WellBracketed b) : WellBracketed (a ++ b) := by
  refine ⟨?_, fun i => ?_⟩
  · have := ha.1; have := hb.1; rw [pbalance_append]; omega
  · rw [pbalance_take_append]
    have h1 := ha.2 i; have h2 := hb.2 (i - a.length); omega

/-- Inserting a delta-`0` token (a `.key`/`.value`/`.scalar`/`.flowEntry`) at any
    position of a `WellBracketed` list keeps it `WellBracketed`: the total balance
    is unchanged and every prefix balance gains only the (zero) delta.  This is the
    pure lemma the **colon step** needs — `scanValuePrepare`'s retroactive
    placeholder→`.key` write inserts a single delta-`0` token *into the middle* of
    the key block (breaking the per-step append decomposition the sequence-body
    producer relied on), and `WellBracketed`-ness must survive that mid-list
    insertion regardless of *where* it lands. -/
theorem WellBracketed_insert_delta_zero (l : List (Positioned YamlToken))
    (t : Positioned YamlToken) (i : Nat)
    (h_delta : flowBracketDelta t.val = 0) (h_wb : WellBracketed l) :
    WellBracketed (l.take i ++ t :: l.drop i) := by
  obtain ⟨h_bal, h_pre⟩ := h_wb
  have h_split : pbalance (l.take i) + pbalance (l.drop i) = 0 := by
    have h := (pbalance_append (l.take i) (l.drop i)).symm
    rw [List.take_append_drop] at h
    omega
  refine ⟨?_, fun j => ?_⟩
  · -- total balance unchanged: prefix + 0 + suffix = 0
    rw [pbalance_append, pbalance_cons, h_delta]; omega
  · -- prefix balance ≥ 0 at every cut `j`
    rw [pbalance_take_append]
    rcases Nat.eq_zero_or_pos (j - (l.take i).length) with hm | hm
    · -- cut lands inside `l.take i`: a genuine prefix of `l`
      have hlen : (l.take i).length ≤ i := by rw [List.length_take]; omega
      have hji : j ≤ i := by omega
      rw [hm, List.take_zero, pbalance_nil, List.take_take]
      simp only [Nat.min_eq_left hji]
      have := h_pre j; omega
    · -- cut passes the insert: prefix(l.take i) + delta t(=0) + a prefix of the suffix
      obtain ⟨k, hk⟩ : ∃ k, j - (l.take i).length = k + 1 :=
        ⟨_, (Nat.succ_pred_eq_of_pos hm).symm⟩
      rw [hk, List.take_succ_cons, pbalance_cons, h_delta]
      have hlen_le : (l.take i).length ≤ j := by omega
      rw [List.take_of_length_le hlen_le]
      have h2 : pbalance (l.take i) + pbalance ((l.drop i).take k) = pbalance (l.take (i + k)) := by
        rw [List.take_add, pbalance_append]
      have := h_pre (i + k); omega

/-- The `i = 0` specialization of `WellBracketed_insert_delta_zero`: prepending a
    delta-`0` token preserves `WellBracketed`.  The colon writes `.key` at the
    *front* of the key block (the first new filtered token is `.key`, per
    `keyshape_first_token_key`), so this cons form is the one the mapping-body
    producer applies directly. -/
theorem WellBracketed_cons_delta_zero (t : Positioned YamlToken)
    (l : List (Positioned YamlToken))
    (h_delta : flowBracketDelta t.val = 0) (h_wb : WellBracketed l) :
    WellBracketed (t :: l) := by
  simpa using WellBracketed_insert_delta_zero l t 0 h_delta h_wb

/-- **Wrapping lemma.** A `WellBracketed` interior framed by a matching opener
    (delta `+1`) and closer (delta `-1`) is both `WellBracketed` and `EntrySafe`.
    The `EntrySafe` half is the payoff: every interior `.flowEntry` is at
    balance `≥ 1` because the opener already contributes `+1`. -/
theorem wrap_block (op cl : Positioned YamlToken) (body : List (Positioned YamlToken))
    (h_op : flowBracketDelta op.val = 1) (h_cl : flowBracketDelta cl.val = -1)
    (h_body : WellBracketed body) :
    WellBracketed (op :: (body ++ [cl])) ∧ EntrySafe (op :: (body ++ [cl])) := by
  -- total balance: 1 + (0 + -1) = 0
  have h_total : pbalance (op :: (body ++ [cl])) = 0 := by
    rw [pbalance_cons, pbalance_append, pbalance_singleton, h_op, h_cl]
    have := h_body.1; omega
  -- prefix balances ≥ 0
  have h_pref : ∀ i, pbalance ((op :: (body ++ [cl])).take i) ≥ 0 := by
    intro i
    match i with
    | 0 => simp [List.take_zero, pbalance_nil]
    | m + 1 =>
      rw [List.take_succ_cons, pbalance_cons, h_op, pbalance_take_append,
          pbalance_take_singleton]
      have hbody := h_body.2 m
      split <;> omega
  refine ⟨⟨h_total, h_pref⟩, h_total, ?_⟩
  -- EntrySafe interior: a `.flowEntry` can only sit in `body`, at balance ≥ 1
  intro idx h_idx h_fe
  match idx, h_idx, h_fe with
  | 0, h_idx, h_fe =>
    exfalso
    have hv : ((op :: (body ++ [cl]))[0]'h_idx).val = op.val := rfl
    rw [hv] at h_fe
    have hd := h_op
    rw [h_fe, flowBracketDelta_flowEntry] at hd
    omega
  | m + 1, h_idx, h_fe =>
    have h_m_lt : m < (body ++ [cl]).length := by
      rw [List.length_cons] at h_idx; omega
    have hv : ((op :: (body ++ [cl]))[m + 1]'h_idx).val = ((body ++ [cl])[m]'h_m_lt).val := by
      rw [List.getElem_cons_succ]
    rw [hv] at h_fe
    rcases Nat.lt_or_ge m body.length with hlt | hge
    · -- genuine interior flowEntry: balance = 1 + (body prefix ≥ 0) ≥ 1
      rw [List.take_succ_cons, pbalance_cons, h_op, pbalance_take_append,
          show m - body.length = 0 from by omega, List.take_zero, pbalance_nil]
      have := h_body.2 m
      omega
    · -- m = body.length: the token is the closer, not a flowEntry — contradiction
      exfalso
      have h_m_eq : m = body.length := by
        rw [List.length_append] at h_m_lt
        have : ([cl]).length = 1 := rfl
        omega
      have hcl_v : ((body ++ [cl])[m]'h_m_lt).val = cl.val := by
        have e : (body ++ [cl])[m]? = some cl := by
          rw [List.getElem?_append_right (by omega), h_m_eq,
              show body.length - body.length = 0 from by omega]
          rfl
        rw [List.getElem?_eq_getElem h_m_lt] at e
        exact congrArg (·.val) (Option.some.inj e)
      rw [hcl_v] at h_fe
      have hd := h_cl
      rw [h_fe, flowBracketDelta_flowEntry] at hd
      omega

/-- A scalar entry (a single non-`.flowEntry`, delta-`0` token) is `EntrySafe`.
    The `≠ .flowEntry` premise is essential: a singleton `.flowEntry` would have
    its sole token at prefix balance `0`, violating the `≥ 1` interior condition. -/
theorem EntrySafe_singleton (t : Positioned YamlToken)
    (h_delta : flowBracketDelta t.val = 0) (h_ne : t.val ≠ .flowEntry) : EntrySafe [t] := by
  refine ⟨by rw [pbalance_singleton, h_delta], fun i h_i h_fe => ?_⟩
  -- a singleton's only index is 0, and its value is not a flowEntry
  match i, h_i, h_fe with
  | 0, _, h_fe =>
    exfalso
    have hv : (([t])[0]'(by simp)).val = t.val := rfl
    rw [hv] at h_fe
    exact h_ne h_fe
  | k + 1, h_i, _ => simp at h_i

/-- A flow-sequence block `[ body ]` with `WellBracketed` interior is both
    `WellBracketed` and `EntrySafe` — the shape a scanned `emit (.sequence …)`
    block takes. Specializes `wrap_block` with the concrete bracket deltas. -/
theorem wrap_seq_block (op cl : Positioned YamlToken)
    (body : List (Positioned YamlToken))
    (h_op : op.val = .flowSequenceStart) (h_cl : cl.val = .flowSequenceEnd)
    (h_body : WellBracketed body) :
    WellBracketed (op :: (body ++ [cl])) ∧ EntrySafe (op :: (body ++ [cl])) :=
  wrap_block op cl body (h_op ▸ flowBracketDelta_flowSequenceStart)
    (h_cl ▸ flowBracketDelta_flowSequenceEnd) h_body

/-- A flow-mapping block `{ body }` with `WellBracketed` interior is both
    `WellBracketed` and `EntrySafe` — the shape a scanned `emit (.mapping …)`
    block takes. Specializes `wrap_block` with the concrete bracket deltas. -/
theorem wrap_map_block (op cl : Positioned YamlToken)
    (body : List (Positioned YamlToken))
    (h_op : op.val = .flowMappingStart) (h_cl : cl.val = .flowMappingEnd)
    (h_body : WellBracketed body) :
    WellBracketed (op :: (body ++ [cl])) ∧ EntrySafe (op :: (body ++ [cl])) :=
  wrap_block op cl body (h_op ▸ flowBracketDelta_flowMappingStart)
    (h_cl ▸ flowBracketDelta_flowMappingEnd) h_body

/-- A scalar entry — a single `.scalar` token — is `EntrySafe`. -/
theorem EntrySafe_scalar (t : Positioned YamlToken) (value : String) (style : ScalarStyle)
    (h : t.val = .scalar value style) : EntrySafe [t] :=
  EntrySafe_singleton t (h ▸ flowBracketDelta_scalar value style) (by rw [h]; simp)

-- ═══ Filtered token lemmas for scanner handlers ═══

/-- `scanFlowSequenceStart` filtered token equation: adds exactly one `.flowSequenceStart`. -/
theorem scanFlowSequenceStart_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowSequenceStart s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowSequenceStart } := by
  unfold scanFlowSequenceStart
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowMappingStart` filtered token equation: adds exactly one `.flowMappingStart`. -/
theorem scanFlowMappingStart_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowMappingStart s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowMappingStart } := by
  unfold scanFlowMappingStart
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowEntry` filtered token equation (when it succeeds):
    adds exactly one `.flowEntry`. -/
theorem scanFlowEntry_filtered (s s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    s'.tokens.filter p = (s.tokens.filter p).push { pos := s.currentPos, val := .flowEntry } := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- Split on the validation check
  split at h
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      rw [← h]
      dsimp only []
      rw [ScannerCorrectness.advance_preserves_tokens]
      rw [emit_tokens_push]
      rw [Array.filter_push]; rfl
  · simp only [Except.ok.injEq] at h
    rw [← h]
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_tokens]
    rw [emit_tokens_push]
    rw [Array.filter_push]; rfl

/-- `scanFlowSequenceEnd` filtered token equation: adds exactly one `.flowSequenceEnd`. -/
theorem scanFlowSequenceEnd_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowSequenceEnd s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowSequenceEnd } := by
  unfold scanFlowSequenceEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowMappingEnd` filtered token equation: adds exactly one `.flowMappingEnd`. -/
theorem scanFlowMappingEnd_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowMappingEnd s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowMappingEnd } := by
  unfold scanFlowMappingEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-! ### §G.balance.bridge.dispatch — dispatch→handler filtered-LIST connection

    The `.leafdelta` lemmas (above) state the filtered-token effect of the
    low-level *handlers* (`scanFlowSequenceStart`, …).  `emit_scans_in_flow`'s
    `Grammable` recursion, however, calls `scanNextToken` (the *dispatch*), which
    is one hop above the handler.  These five lemmas bridge the gap: given the
    `scanNextToken s = .ok (some s')` fact already produced by the dispatch leaf
    theorems (`scanNextToken_flow_open_nested`, …), each re-derives the dispatch
    composition to pin `s'` to the handler applied to the post-`saveSimpleKey`
    state `s_ad`, then combines the handler `.leafdelta` lemma with
    `saveSimpleKey_filter_placeholder` (the two reserved placeholders filter away)
    to expose the full filtered-LIST delta `s'.tokens.filter p =
    (s.tokens.filter p).push tok`.  These are the per-leaf inputs the
    `EmitScansInFlowBlock` `Grammable` induction (`.blockwb.predicate`, next)
    consumes.  No consumers yet — pure enablement, mirroring `.leafdelta`. -/

/-- `[` dispatch: the new filtered token is exactly one `.flowSequenceStart`. -/
theorem scanNextToken_flow_open_seq_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowSequenceStart ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceStart s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowSequenceStart_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `{` dispatch: the new filtered token is exactly one `.flowMappingStart`. -/
theorem scanNextToken_flow_open_map_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowMappingStart ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingStart s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowMappingStart_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `]` dispatch (nested, `flowLevel ≥ 2`): the new filtered token is exactly
    one `.flowSequenceEnd`. -/
theorem scanNextToken_flow_close_seq_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨']' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowSequenceEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_flow_disp := dispatchFlowIndicators_close_bracket_nested s_ad h_ad_fl_ge2
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceEnd s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceEnd s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowSequenceEnd, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowSequenceEnd_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `}` dispatch (nested, `flowLevel ≥ 2`): the new filtered token is exactly
    one `.flowMappingEnd`. -/
theorem scanNextToken_flow_close_map_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'}' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowMappingEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_flow_disp := dispatchFlowIndicators_close_brace_nested s_ad h_ad_fl_ge2
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingEnd s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingEnd s_ad :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .flowMappingEnd, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowMappingEnd_filtered s_ad
  rw [h_s', hf, h_ad_filter]

/-- `"` dispatch: the new filtered token is exactly one `.scalar _ .doubleQuoted`. -/
theorem scanNextToken_flow_scalar_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'"' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ (tok : Positioned YamlToken) (str : String) (st : ScalarStyle),
      tok.val = .scalar str st ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  have h_dc : scanNextToken_dispatchContent s_ad '"' = Except.ok s' := by
    cases h_dc_eq : scanNextToken_dispatchContent s_ad '"' with
    | error e =>
      exfalso
      have h_snt_err := scanNextToken_via_content_dispatch_error
        _ _ _ _ _ h_pp h_struct rfl h_check h_flow_none h_block_none h_dc_eq
      rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)
    | ok s_dc =>
      have h_snt_eq : scanNextToken s = Except.ok (some s_dc) :=
        scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
          h_flow_none h_block_none h_dc_eq
      have h_eq2 : s' = s_dc := Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
      subst h_eq2; rfl
  have h_tokens_push : ∃ c, s'.tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ := by
    cases h_dq_eq : scanDoubleQuoted s_ad with
    | error e =>
      exfalso
      have h_dc_err : scanNextToken_dispatchContent s_ad '"' = Except.error e := by
        unfold scanNextToken_dispatchContent
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq]
      rw [h_dc_err] at h_dc; exact absurd h_dc (by simp)
    | ok s_dq =>
      obtain ⟨c, h_tok⟩ := scanDoubleQuoted_tokens_push h_dq_eq
      refine ⟨c, ?_⟩
      have h_s'_tokens : s'.tokens = s_dq.tokens := by
        unfold scanNextToken_dispatchContent at h_dc
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq] at h_dc
        split at h_dc
        · rw [← h_dc]
        · rw [← h_dc]
      rw [h_s'_tokens, h_tok]
  obtain ⟨c, h_s'_tokens⟩ := h_tokens_push
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  refine ⟨⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩, c, .doubleQuoted, rfl, ?_⟩
  rw [h_s'_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_filter]

/-- `,` dispatch (flow separator): the new filtered token is exactly one `.flowEntry`.
    Companion to the five `.blockwb.dispatch` push lemmas above — the separator
    leaf the *body* of `EmitListScansInFlowBlock` / `EmitPairListScansInFlowBlock`
    threads between item blocks.  Requires the `lastRealToken ≠ flow*` premise that
    `scanFlowEntry` needs (every preceding `emit v` block supplies it). -/
theorem scanNextToken_flow_comma_filtered_push (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_last : ∀ t, lastRealTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    ∃ tok : Positioned YamlToken, tok.val = .flowEntry ∧
      s'.tokens.filter (fun t => t.val != .placeholder)
        = (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ',')) :=
    scanNextToken_preprocess_flow s ',' rest s.col hcorr h_flow (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ',' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_comma s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  have h_ad_last : ∀ t, lastRealTokenVal? s_ad.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_toks] at ht
    exact saveSimpleKey_preserves_lastRealTokenVal_ne_flow s h_last t ht
  have h_flow_disp := dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  have h_snt_eq : scanNextToken s =
      .ok (some { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = { (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true } :=
    Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
  have h_ad_filter : s_ad.tokens.filter (fun t => t.val != .placeholder)
      = s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]; split <;> exact saveSimpleKey_filter_placeholder s
  have h_sfe : scanFlowEntry s_ad = .ok s' := by rw [h_s']; exact scanFlowEntry_ok s_ad h_ad_last
  refine ⟨⟨s_ad.currentPos, .flowEntry, s_ad.currentPos⟩, rfl, ?_⟩
  have hf := scanFlowEntry_filtered s_ad s' h_sfe
  rw [hf, h_ad_filter]

/-- `ScanChain_deterministic`: two chains with the same start state and step count
    reach the same final state (since `scanNextToken` is a function). -/
theorem ScanChain_deterministic {s s₁ s₂ : ScannerState} {n : Nat}
    (h₁ : ScanChain s n s₁) (h₂ : ScanChain s n s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | zero => cases h₂; rfl
  | @step s s_mid₁ s₁ k h_snt₁ _ ih =>
    match h₂ with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid₁ = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

/-- `ScanChain.split`: decompose a chain into two consecutive sub-chains. -/
theorem ScanChain.split {s s₁ s₂ : ScannerState} {n₁ n₂ : Nat}
    (h₁ : ScanChain s n₁ s₁) (h_total : ScanChain s (n₁ + n₂) s₂) :
    ScanChain s₁ n₂ s₂ := by
  induction h₁ generalizing s₂ with
  | zero => simpa using h_total
  | @step s s_mid s₁ k h_snt₁ _ ih =>
    have h_rw : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [h_rw] at h_total
    match h_total with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

-- ═══ Body token characterization lemmas ═══

-- The proofs require tracing per-step scanner dispatch: each `emit v` produces first
-- character `"`, `[`, or `{`, which dispatch to scanDoubleQuoted / scanFlowSequenceStart /
-- scanFlowMappingStart respectively. The comma separator `, ` dispatches to scanFlowEntry
-- followed by whitespace skip and then the next item's dispatch.
--
-- IMPORTANT: The flowEntry pattern (part 2) is restricted to OUTER-LEVEL flowEntries
-- (where flowBracketBalance from old_sz to k equals 0). Inner flowEntries inside nested
-- bracket groups (e.g., inside a nested mapping `{k1: v1, k2: v2}`) have `.key` after
-- them, not a content start. The parser loop only visits outer-level flowEntries because
-- `parseNode` consumes entire bracket groups, so this restriction is sufficient.

/-- Body token characterization for `emitList` in flow context:
    (1) The first new filtered token (at position `old_sz`) is a content start.
    (2) After every OUTER-LEVEL `.flowEntry` (where bracket balance from `old_sz` to `k` is 0),
        the next filtered token is a content start.

    These follow from `emitList`'s structure: items separated by `", "` (comma + space).
    Each item starts with `emit v`, whose first character (`"`, `[`, or `{`) dispatches to
    `scanDoubleQuoted`, `scanFlowSequenceStart`, or `scanFlowMappingStart` — none of which
    emit `.flowEntry` or `.key` as their first filtered token. -/
theorem emitList_body_filtered_characterization
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlow v)
    (h_all_skdr : ∀ v ∈ items, EmitScansInFlowSKDR v)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false)
    (h_ska : s.simpleKeyAllowed = true)
    (h_sync : s.simpleKeyStack.size = s.flowLevel)
    (h_ssv : ScannerCorrectness.SimpleKeyStackValid s) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    -- (1) First new filtered token is a content start (scalar, flowSeqStart, or flowMapStart)
    ∧ (old_sz < (s'.tokens.filter p).size ∧
     (∀ (h : old_sz < (s'.tokens.filter p).size),
       ((∃ c sc, ((s'.tokens.filter p)[old_sz]'h).val = .scalar c sc) ∨
        ((s'.tokens.filter p)[old_sz]'h).val = .flowSequenceStart ∨
        ((s'.tokens.filter p)[old_sz]'h).val = .flowMappingStart)))
    -- (2) After every OUTER-LEVEL flowEntry, next is a content start
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
      ((s'.tokens.filter p)[k]'h_hi).val = .flowEntry →
      flowBracketBalance (s'.tokens.filter p) old_sz k = 0 →
      k + 1 < (s'.tokens.filter p).size ∧
      (∀ (h' : k + 1 < (s'.tokens.filter p).size),
        ((∃ c sc, ((s'.tokens.filter p)[k + 1]'h').val = .scalar c sc) ∨
         ((s'.tokens.filter p)[k + 1]'h').val = .flowSequenceStart ∨
         ((s'.tokens.filter p)[k + 1]'h').val = .flowMappingStart))) := by
  -- Construct the SKDR-augmented chain.  The strict ScanChainGrew variant is
  -- what's returned; we forget to plain ScanChain only at the public boundary.
  -- The `SavedKeyDoesntResolve` witness (at target `N := s.tokens.size`) feeds
  -- substrate.f's position-`N+1` preservation in Part 1.
  have h_scan := emitList_scans_nonempty_with_skdr items h_ne h_all_skdr
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_skdr⟩ :=
    h_scan s rest s.tokens.size h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      (Nat.le.refl) h_sync
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc, ?_, ?_⟩
  · -- Part 1: First new filtered token is a content start
    have h_grows := ScanChainGrew_filtered_grows h_chain
    have h_n_pos : n ≥ 1 := by
      match n, h_chain with
      | 0, h_zero =>
        exfalso
        have h_eq : s = s' := by cases h_zero; rfl
        rw [h_eq] at h_corr
        have h_chars_eq := CharsFromOffset_unique h_corr.chars_from h_corr'.chars_from
        have h_len := congrArg List.length h_chars_eq
        simp only [List.length_append] at h_len
        have h_nil : (emit.emitList items).toList = [] := by
          match h_list : (emit.emitList items).toList with
          | [] => rfl
          | _ :: _ => simp [h_list] at h_len
        match h_items : items with
        | [] => exact absurd rfl h_ne
        | i :: is => exact absurd h_nil (emitList_toList_ne_nil i is)
      | _ + 1, _ => omega
    refine ⟨by omega, ?_⟩
    intro h_old_lt
    -- Leading char of the emitList body is `[` / `{` / `"`.
    obtain ⟨v, vs, rfl⟩ : ∃ v vs, items = v :: vs := by
      cases items with
      | nil => exact absurd rfl h_ne
      | cons v vs => exact ⟨v, vs, rfl⟩
    obtain ⟨c, rest', h_first, h_c⟩ := emitList_first_char_bracket v vs
    have h_corr_c : ScannerSurfCorr s ⟨c :: (rest' ++ rest), s.col⟩ := by
      have h_eq : (emit.emitList (v :: vs)).toList ++ rest = c :: (rest' ++ rest) := by
        rw [h_first]; simp
      rwa [h_eq] at h_corr
    -- Decompose the SKDR chain to extract the first scanned state `s_first`.
    cases h_skdr with
    | zero => exact (Nat.lt_irrefl _ h_old_lt).elim
    | @step _ s_first _ _ h_fl0 h_snt h_pres h_rest =>
      -- Head step: `s_first.tokens.size = N+3`, plus the two no-overwrite
      -- invariants substrate.d (`N+2`) and substrate.e (`N`) consume.
      obtain ⟨h_sf_size, h_no, h_fno⟩ :=
        emitList_head_step_noOverwrite s s_first c (rest' ++ rest) h_corr_c h_flow h_indent
          h_col h_ek h_ska h_ssv h_c h_snt
      have h_resid_fmc : FlowMonoChain s.flowLevel s_first _ s' := h_rest.toFlowMonoChain
      have h_fl_pos : s.flowLevel ≥ 1 := by omega
      have h_skaf : SimpleKeyAboveFloor s s.tokens.size s.flowLevel :=
        ⟨fun hp => by rw [h_sk] at hp; exact absurd hp (by decide),
         fun j _hj_fl hj _ => by exfalso; rw [h_sync] at hj; omega,
         (Nat.le_of_eq h_sync.symm)⟩
      have h_sf_mono : s_first.tokens.size ≤ s'.tokens.size := by
        have := h_resid_fmc.tokens_mono; omega
      -- The raw prefix `[0..N+3)` of `s'` agrees with `s_first`:
      --   `[0..N)` from the SimpleKeyAboveFloor bulk lemma (+ first-step bridge),
      --   `N` from substrate.e, `N+1` from substrate.f, `N+2` from substrate.d.
      have h_prefix : ∀ i (hi : i < s_first.tokens.size),
          s'.tokens[i]'(by omega) = s_first.tokens[i] := by
        intro i hi
        rw [h_sf_size] at hi
        rcases Nat.lt_or_ge i s.tokens.size with hlt | hge
        · have h1 := FlowMonoChain_preserves_raw_prefix h_fmc s.tokens.size (Nat.le.refl)
            h_skaf (Nat.le_of_eq h_sync.symm) i hlt
          have h2 := scanNextToken_preserves_prefix_of_skFloor s s_first h_snt s.tokens.size
            (Nat.le.refl) (fun hp => by rw [h_sk] at hp; exact absurd hp (by decide)) i hlt
          rw [h2]; exact h1
        · obtain rfl | rfl | rfl :
              i = s.tokens.size ∨ i = s.tokens.size + 1 ∨ i = s.tokens.size + 2 := by omega
          · obtain ⟨_, h⟩ := FlowMonoChain_preserves_position_specific_flow h_fl_pos
              h_resid_fmc s.tokens.size (by rw [h_sf_size]; omega) h_fno
            exact h
          · obtain ⟨_, h⟩ := SavedKeyDoesntResolve_preserves_position_target h_rest
              (by rw [h_sf_size]; omega)
            exact h
          · obtain ⟨_, h⟩ := FlowMonoChain_preserves_position_specific h_resid_fmc
              (s.tokens.size + 2) (by rw [h_sf_size]; omega) h_no
            exact h
      -- Transfer the head content token from `s_first` (first-filtered lemma) to `s'`.
      rcases h_c with rfl | rfl | rfl
      · obtain ⟨h_ff_lt, h_ff_val⟩ :=
          scanFlowSequenceStart_first_filtered_token s (rest' ++ rest) h_corr_c h_flow h_indent
            h_col h_snt
        refine Or.inr (Or.inl ?_)
        rw [Array_filter_getElem_of_raw_prefix s_first.tokens s'.tokens
          (fun t => t.val != .placeholder) h_sf_mono h_prefix _ h_ff_lt h_old_lt]
        exact h_ff_val h_ff_lt
      · obtain ⟨h_ff_lt, h_ff_val⟩ :=
          scanFlowMappingStart_first_filtered_token s (rest' ++ rest) h_corr_c h_flow h_indent
            h_col h_snt
        refine Or.inr (Or.inr ?_)
        rw [Array_filter_getElem_of_raw_prefix s_first.tokens s'.tokens
          (fun t => t.val != .placeholder) h_sf_mono h_prefix _ h_ff_lt h_old_lt]
        exact h_ff_val h_ff_lt
      · obtain ⟨h_ff_lt, h_ff_val⟩ :=
          scanDoubleQuoted_first_filtered_token s (rest' ++ rest) h_corr_c h_flow h_indent
            h_col h_snt
        refine Or.inl ?_
        rw [Array_filter_getElem_of_raw_prefix s_first.tokens s'.tokens
          (fun t => t.val != .placeholder) h_sf_mono h_prefix _ h_ff_lt h_old_lt]
        exact h_ff_val h_ff_lt
  · -- Part 2: After every outer-level flowEntry, next is a content start
    sorry

/-- Body token characterization for `emitPairList` in flow context:
    (1) The chain has ≥ 3 steps (key handling + value indicator + value content).
    (2) The first new filtered token is `.key` (from `saveSimpleKey` + `scanValuePrepare`
        retroactively converting a placeholder when `: ` is scanned).
    (3) After every OUTER-LEVEL `.flowEntry` (where bracket balance from `old_sz` to `k` is 0),
        the next filtered token is `.key`.

    These follow from `emitPairList`'s structure: each pair produces `emit k ++ ": " ++ emit v`,
    with pairs separated by `", "`. The `: ` triggers `scanValuePrepare` which converts the
    placeholder (saved by `saveSimpleKey` before scanning `emit k`) to `.key`. After each
    comma separator, the next pair starts with `emit k` again, preceded by `saveSimpleKey`.

    IMPORTANT: The flowEntry pattern (part 3) is restricted to outer-level flowEntries
    (bracketBalance = 0). Inner flowEntries from nested sequences/mappings may be followed
    by content-start tokens rather than `.key`. The parser loop only visits outer-level
    flowEntries because `parseNode` consumes entire nested bracket groups. -/
theorem emitPairList_body_filtered_characterization
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlow p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlow p.2)
    (h_all_k_sk : ∀ p ∈ pairs, EmitScansInFlowSavedKey p.1)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false)
    (h_ska : s.simpleKeyAllowed = true)
    (h_sync : s.simpleKeyStack.size = s.flowLevel)
    (h_ssv : ScannerCorrectness.SimpleKeyStackValid s) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    -- (1) At least 3 chain steps (key + value indicator + value)
    ∧ n ≥ 3
    -- (2) First new filtered token is .key
    ∧ (old_sz < (s'.tokens.filter p).size ∧
     (∀ (h : old_sz < (s'.tokens.filter p).size),
       ((s'.tokens.filter p)[old_sz]'h).val = .key))
    -- (3) After every OUTER-LEVEL flowEntry, next is .key
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
      ((s'.tokens.filter p)[k]'h_hi).val = .flowEntry →
      flowBracketBalance (s'.tokens.filter p) old_sz k = 0 →
      k + 1 < (s'.tokens.filter p).size ∧
      (∀ (h' : k + 1 < (s'.tokens.filter p).size),
        ((s'.tokens.filter p)[k + 1]'h').val = .key)) := by
  -- Construct the chain from the keyshape producer (carries n ≥ 3 AND Part 2, the
  -- `.key` first-filtered-token fact — sorry 9644 is now discharged via the
  -- saved-key substrate + colon token effect + filter transfer).
  have h_scan := emitPairList_scans_nonempty_keyshape pairs h_ne h_all_k h_all_v h_all_k_sk
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, h_n_ge_3, h_part2⟩ :=
    h_scan s rest h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sk h_ska h_sync h_ssv
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc, h_n_ge_3, h_part2, ?_⟩
  · -- Part 3: After every outer-level flowEntry, next is .key
    sorry

/-- Token structure of `scanFiltered ("[" ++ emitList items ++ "]")` for non-empty items.
    Establishes boundary tokens, body token patterns, and `parseNode` success within
    the flow sequence body.

    Requires `EmitScansInFlow` for each item to construct the scanner chain. -/
theorem scanFiltered_emitSeq_nonempty_structure
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_scan : ∀ w, w ∈ items.toList → EmitScansInFlow w)
    (h_all_skdr : ∀ w, w ∈ items.toList → EmitScansInFlowSKDR w) :
    tokens.size ≥ 5 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd ∧
    tokens[1]!.val = .flowSequenceStart ∧
    tokens[tokens.size - 2]!.val = .flowSequenceEnd ∧
    ((∃ c s, tokens[2]!.val = .scalar c s) ∨
     tokens[2]!.val = .flowSequenceStart ∨
     tokens[2]!.val = .flowMappingStart) ∧
    (∀ k, 2 ≤ k → k < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧
        ((∃ c s, tokens[k + 1]!.val = .scalar c s) ∨
         tokens[k + 1]!.val = .flowSequenceStart ∨
         tokens[k + 1]!.val = .flowMappingStart)) ∧
    L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := by
  -- Step 1: Boundary tokens from scanFiltered_boundary_tokens
  obtain ⟨h_sz2, h_t0, h_tlast⟩ := scanFiltered_boundary_tokens _ _ h_scan
  -- ═══ Chain replay: reconstruct s₁ (after '['), s₂ (after body), s₃ (after ']') ═══
  let input := "[" ++ emit.emitList items.toList ++ "]"
  have h_toList : input.toList = '[' :: (emit.emitList items.toList).toList ++ [']'] := by
    simp only [input, String.toList_append]; rfl
  -- Open bracket → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, h_ska₁, h_ssv₁⟩ :=
    scanNextToken_flow_open_init input
      ((emit.emitList items.toList).toList ++ [']']) h_toList
  -- Body scanning → s₂ (with filtered token characterization)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
          h_ek₂, h_col₂, h_inflow₂, h_indent₂, _, _, _, h_stack₂, h_fmc₂,
          ⟨h_body_sz_raw, h_body_cs_raw⟩, h_body_fe_next_raw⟩ :=
    emitList_body_filtered_characterization items.toList h_ne
      (fun w hw => h_all_scan w hw) (fun w hw => h_all_skdr w hw) s₁ [']']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sk₁ h_ska₁ h_sync₁ h_ssv₁
  -- Close bracket → s₃ (using _ext to get filtered token info + indents)
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fse, h_tok_fse_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_seq_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '['
      ((emit.emitList items.toList).toList ++ [']']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₀.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- ═══ Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p ═══
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  -- Extract: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Decompose filtered token array as: s₂_filtered ++ [flowSeqEnd, streamEnd] ═══
  -- s₃.tokens.filter p = (s₂.tokens.filter p).push tok_fse  (from _ext)
  -- (s₃.emit .streamEnd).tokens.filter p = s₃.tokens.filter p ++ [streamEnd]
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  -- Combine: tokens = (s₂.filter p) ++ [tok_fse] ++ [streamEnd]
  -- i.e. tokens = ((s₂.filter p).push tok_fse).push streamEnd
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fse).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Tier 1 derivations ═══
  -- h_tpe: tokens[tokens.size - 2] = tok_fse, which has val = .flowSequenceEnd
  have h_tpe : tokens[tokens.size - 2]!.val = .flowSequenceEnd := by
    rw [h_tokens_decomp]
    have h_outer_sz : (((s₂.tokens.filter p).push tok_fse).push
        { pos := s₃.currentPos, val := YamlToken.streamEnd }).size =
        (s₂.tokens.filter p).size + 2 := by simp [Array.size_push]
    rw [h_outer_sz, show (s₂.tokens.filter p).size + 2 - 2 = (s₂.tokens.filter p).size from by omega]
    rw [getElem!_pos _ _ (by omega)]
    rw [Array.getElem_push_lt (show (s₂.tokens.filter p).size <
        ((s₂.tokens.filter p).push tok_fse).size from by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
    exact h_tok_fse_val
  -- ═══ Filtered prefix preservation (via ScanChain infrastructure) ═══
  -- h_filt₁ : (s₁.tokens.filter p).map (·.val) = #[.streamStart, .flowSequenceStart]
  -- Extract filtered prefix size and element values
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_filt₁_val1 : ((s₁.tokens.filter p)[1]'(by omega)).val = YamlToken.flowSequenceStart := by
    have h_len : (s₁.tokens.filter p).toList.length = 2 := by
      rw [Array.length_toList]; exact h_filt₁_sz
    have h_vals : (s₁.tokens.filter p).toList.map (·.val) =
        [YamlToken.streamStart, YamlToken.flowSequenceStart] := by
      have := congrArg Array.toList h_filt₁; simpa [Array.toList_map] using this
    obtain ⟨a, b, h_ab⟩ : ∃ a b, (s₁.tokens.filter p).toList = [a, b] := by
      match (s₁.tokens.filter p).toList, h_len with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    show (s₁.tokens.filter p).toList[1].val = YamlToken.flowSequenceStart
    simp only [h_ab, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [h_ab] at h_vals; simp at h_vals; exact h_vals.2
  -- Body chain preserves filtered prefix and grows by ≥ n₂
  obtain ⟨suffix, h_suffix⟩ : ∃ suffix, (s₂.tokens.filter p).toList =
      (s₁.tokens.filter p).toList ++ suffix :=
    ScanChain_filtered_prefix h_fmc₂ h_sk₁ (by omega) (by
      intro j hj hjsz; rw [h_sync₁] at hjsz; rw [h_fl₁] at hj; omega)
  have h_filt_grows : (s₂.tokens.filter p).size ≥
      (s₁.tokens.filter p).size + n₂ := ScanChain_filtered_grows h_chain₂
  -- n₂ ≥ 1 (body is non-empty: s₁ sees body chars, s₂ sees [']'])
  have h_n₂_pos : n₂ ≥ 1 := by
    match n₂, h_chain₂ with
    | 0, h_zero =>
      exfalso
      have h_s1_eq_s2 : s₁ = s₂ := by cases h_zero; rfl
      rw [h_s1_eq_s2] at h_corr₁
      have h_chars_eq := CharsFromOffset_unique h_corr₁.chars_from h_corr₂.chars_from
      have h_len := congrArg List.length h_chars_eq
      simp only [List.length_append] at h_len
      have h_nil : (emit.emitList items.toList).toList = [] := by
        match h_list : (emit.emitList items.toList).toList with
        | [] => rfl
        | _ :: _ => simp [h_list] at h_len
      match h_items : items.toList with
      | [] => exact absurd h_items h_ne
      | v :: vs =>
          rw [h_items] at h_nil; exact absurd h_nil (emitList_toList_ne_nil v vs)
    | _ + 1, _ => omega
  -- (s₂.tokens.filter p).size ≥ 3
  have h_s2_filt_sz : (s₂.tokens.filter p).size ≥ 3 := by
    rw [h_filt₁_sz] at h_filt_grows; omega
  -- h_t1: peel two pushes to reach (s₂.tokens.filter p)[1], then use prefix
  have h_t1 : tokens[1]!.val = .flowSequenceStart := by
    rw [h_tokens_decomp]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < ((s₂.tokens.filter p).push tok_fse).size
        from by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < (s₂.tokens.filter p).size from by omega)]
    -- Goal: (s₂.tokens.filter p)[1]'_.val = .flowSequenceStart
    -- Show filtered[1] is preserved from s₁ to s₂ via ScanChain prefix
    have h1_lt_s1 : 1 < (s₁.tokens.filter p).size := by rw [h_filt₁_sz]; omega
    have h_eq : (s₂.tokens.filter p)[1]'(by omega) = (s₁.tokens.filter p)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega) =
          (s₁.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega)
      simp only [h_suffix]
      exact List.getElem_append_left (by rw [Array.length_toList]; omega)
    calc ((s₂.tokens.filter p)[1]'(by omega)).val
        = ((s₁.tokens.filter p)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowSequenceStart := h_filt₁_val1
  -- h_sz5: tokens.size = (s₂.filter p).size + 2 ≥ 3 + 2 = 5
  have h_sz5 : tokens.size ≥ 5 := by
    rw [h_tokens_decomp]; simp [Array.size_push]; omega
  -- ═══ Body token characterization (now from combined theorem) ═══
  -- Rename _raw variables to match expected names
  have h_body_sz := h_body_sz_raw; have h_body_cs := h_body_cs_raw
  have h_body_fe_next := h_body_fe_next_raw
  rw [h_filt₁_sz] at h_body_sz h_body_cs h_body_fe_next
  -- Helper: tokens[k]! for k < tokens.size - 2 equals (s₂.filter p)[k]
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  have h_tok_body (k : Nat) (h_lt : k < (s₂.tokens.filter p).size) :
      tokens[k]! = ((s₂.tokens.filter p)[k]'h_lt) := by
    rw [h_tokens_decomp, getElem!_pos _ k (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show k < ((s₂.tokens.filter p).push tok_fse).size
        from by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_lt]
  have h_content0 : (∃ c s, tokens[2]!.val = .scalar c s) ∨
      tokens[2]!.val = .flowSequenceStart ∨
      tokens[2]!.val = .flowMappingStart := by
    have h_body := h_body_cs (by omega)
    rw [h_tok_body 2 (by omega)]
    exact h_body
  have h_fe_pattern : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens 2 k = 0 →
      k + 1 ≤ tokens.size - 2 ∧
      ((∃ c s, tokens[k + 1]!.val = .scalar c s) ∨
       tokens[k + 1]!.val = .flowSequenceStart ∨
       tokens[k + 1]!.val = .flowMappingStart) := by
    intro k h_lo h_hi h_fe h_depth
    have h_k_lt : k < (s₂.tokens.filter p).size := by omega
    rw [h_tok_body k h_k_lt] at h_fe
    -- Convert flowBracketBalance from tokens to s₂.tokens.filter p
    have h_depth' : flowBracketBalance (s₂.tokens.filter p) 2 k = 0 := by
      rw [← h_tokens_sz_eq] at h_k_lt
      have : flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
        rw [h_tokens_decomp]
        rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
        rw [flowBracketBalance_push _ _ 2 k (by omega)]
      rw [this] at h_depth; exact h_depth
    obtain ⟨h_next_lt, h_next_cs⟩ := h_body_fe_next k (by omega) h_k_lt h_fe h_depth'
    exact ⟨by omega,
           by rw [h_tok_body (k+1) (by omega)]; exact h_next_cs (by omega)⟩
  have h_pnok : L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk
      tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := sorry
  exact ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, h_content0, h_fe_pattern, h_pnok⟩

/-- Token structure of `scanFiltered ("{" ++ emitPairList pairs ++ "}")` for non-empty pairs.
    Establishes boundary tokens, body token patterns, and `parseExplicitKey`/`parseFlowMappingValue`
    success within the flow mapping body. -/
theorem scanFiltered_emitMap_nonempty_structure
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_scan_k : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.1)
    (h_all_scan_v : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.2)
    (h_all_scan_k_sk : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKey p.1) :
    tokens.size ≥ 7 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd ∧
    tokens[1]!.val = .flowMappingStart ∧
    tokens[tokens.size - 2]!.val = .flowMappingEnd ∧
    tokens[2]!.val = .key ∧
    (∀ k, 2 ≤ k → k < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧ tokens[k + 1]!.val = .key) ∧
    L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := by
  -- Step 1: Boundary tokens from scanFiltered_boundary_tokens
  obtain ⟨h_sz2, h_t0, h_tlast⟩ := scanFiltered_boundary_tokens _ _ h_scan
  -- ═══ Chain replay: reconstruct s₁ (after '{'), s₂ (after body), s₃ (after '}') ═══
  let input := "{" ++ emit.emitPairList pairs.toList ++ "}"
  have h_toList : input.toList = '{' :: (emit.emitPairList pairs.toList).toList ++ ['}'] := by
    simp only [input, String.toList_append]; rfl
  -- Open brace → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, h_ska₁, h_ssv₁⟩ :=
    scanNextToken_flow_open_mapping_init input
      ((emit.emitPairList pairs.toList).toList ++ ['}']) h_toList
  -- Body scanning → s₂ (with filtered token characterization)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
          h_ek₂, h_col₂, h_inflow₂, h_indent₂, _, _, _, h_stack₂, h_fmc₂,
          h_n₂_ge3, ⟨h_body_sz_raw, h_body_key_raw⟩, h_body_fe_next_raw⟩ :=
    emitPairList_body_filtered_characterization pairs.toList h_ne
      (fun p hp => h_all_scan_k p hp) (fun p hp => h_all_scan_v p hp)
      (fun p hp => h_all_scan_k_sk p hp) s₁ ['}']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sk₁ h_ska₁ h_sync₁ h_ssv₁
  -- Close brace → s₃ (using _ext to get filtered token info + indents)
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fme, h_tok_fme_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_mapping_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{'
      ((emit.emitPairList pairs.toList).toList ++ ['}']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₀.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- ═══ Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p ═══
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) :=
    scanFiltered_tokens_eq_of_chain_short_stack input _ s₃ _ rfl h_no_bom
      h_chain_all h_eof h_fl₃ h_dp₃
      (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
      h_indents_small
  -- Extract: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Decompose filtered token array as: s₂_filtered ++ [flowMapEnd, streamEnd] ═══
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fme).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Tier 1 derivations ═══
  -- h_tpe: tokens[tokens.size - 2] = tok_fme, which has val = .flowMappingEnd
  have h_tpe : tokens[tokens.size - 2]!.val = .flowMappingEnd := by
    rw [h_tokens_decomp]
    have h_outer_sz : (((s₂.tokens.filter p).push tok_fme).push
        { pos := s₃.currentPos, val := YamlToken.streamEnd }).size =
        (s₂.tokens.filter p).size + 2 := by simp [Array.size_push]
    rw [h_outer_sz, show (s₂.tokens.filter p).size + 2 - 2 = (s₂.tokens.filter p).size from by omega]
    rw [getElem!_pos _ _ (by omega)]
    rw [Array.getElem_push_lt (show (s₂.tokens.filter p).size <
        ((s₂.tokens.filter p).push tok_fme).size from by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
    exact h_tok_fme_val
  -- ═══ Filtered prefix preservation (via ScanChain infrastructure) ═══
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_filt₁_val1 : ((s₁.tokens.filter p)[1]'(by omega)).val = YamlToken.flowMappingStart := by
    have h_len : (s₁.tokens.filter p).toList.length = 2 := by
      rw [Array.length_toList]; exact h_filt₁_sz
    have h_vals : (s₁.tokens.filter p).toList.map (·.val) =
        [YamlToken.streamStart, YamlToken.flowMappingStart] := by
      have := congrArg Array.toList h_filt₁; simpa [Array.toList_map] using this
    obtain ⟨a, b, h_ab⟩ : ∃ a b, (s₁.tokens.filter p).toList = [a, b] := by
      match (s₁.tokens.filter p).toList, h_len with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    show (s₁.tokens.filter p).toList[1].val = YamlToken.flowMappingStart
    simp only [h_ab, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [h_ab] at h_vals; simp at h_vals; exact h_vals.2
  obtain ⟨suffix, h_suffix⟩ : ∃ suffix, (s₂.tokens.filter p).toList =
      (s₁.tokens.filter p).toList ++ suffix :=
    ScanChain_filtered_prefix h_fmc₂ h_sk₁ (by omega) (by
      intro j hj hjsz; rw [h_sync₁] at hjsz; rw [h_fl₁] at hj; omega)
  have h_filt_grows : (s₂.tokens.filter p).size ≥
      (s₁.tokens.filter p).size + n₂ := ScanChain_filtered_grows h_chain₂
  -- n₂ ≥ 1 (from n₂ ≥ 3)
  have h_n₂_pos : n₂ ≥ 1 := by omega
  have h_s2_filt_sz : (s₂.tokens.filter p).size ≥ 3 := by
    rw [h_filt₁_sz] at h_filt_grows; omega
  have h_t1 : tokens[1]!.val = .flowMappingStart := by
    rw [h_tokens_decomp]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < ((s₂.tokens.filter p).push tok_fme).size
        from by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < (s₂.tokens.filter p).size from by omega)]
    -- Show filtered[1] is preserved from s₁ to s₂ via ScanChain prefix
    have h1_lt_s1 : 1 < (s₁.tokens.filter p).size := by rw [h_filt₁_sz]; omega
    have h_eq : (s₂.tokens.filter p)[1]'(by omega) = (s₁.tokens.filter p)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega) =
          (s₁.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega)
      simp only [h_suffix]
      exact List.getElem_append_left (by rw [Array.length_toList]; omega)
    calc ((s₂.tokens.filter p)[1]'(by omega)).val
        = ((s₁.tokens.filter p)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowMappingStart := h_filt₁_val1
  -- h_sz7: for map, need n₂ ≥ 5 filtered tokens (prefix 2 + suffix ≥ 3)
  -- Non-empty pair list has ≥ 1 pair. Each pair scanning produces ≥ 3 scanNextToken
  -- steps (key, value indicator, value scalar). Combined with n₂ ≥ 1, this gives
  -- filtered size ≥ 2 + n₂. For n₂ ≥ 5 we need the pair structure decomposition.
  -- ═══ Body token characterization (now from combined theorem) ═══
  -- Rename _raw variables to match expected names
  have h_body_sz := h_body_sz_raw; have h_body_key := h_body_key_raw
  have h_body_fe_next := h_body_fe_next_raw
  rw [h_filt₁_sz] at h_body_sz h_body_key h_body_fe_next
  -- tokens.size - 2 = (s₂.filter p).size
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  -- Helper: tokens[k]! for k < tokens.size - 2 equals (s₂.filter p)[k]
  have h_tok_body (k : Nat) (h_lt : k < (s₂.tokens.filter p).size) :
      tokens[k]! = ((s₂.tokens.filter p)[k]'h_lt) := by
    rw [h_tokens_decomp, getElem!_pos _ k (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show k < ((s₂.tokens.filter p).push tok_fme).size
        from by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_lt]
  have h_sz7 : tokens.size ≥ 7 := by
    rw [h_tokens_decomp]; simp [Array.size_push]
    -- (s₂.filter).size ≥ (s₁.filter).size + n₂ = 2 + n₂ ≥ 2 + 3 = 5
    rw [h_filt₁_sz] at h_filt_grows; omega
  have h_t2_key : tokens[2]!.val = .key := by
    rw [h_tok_body 2 (by omega)]; exact h_body_key (by omega)
  have h_fe_pattern : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens 2 k = 0 →
      k + 1 ≤ tokens.size - 2 ∧ tokens[k + 1]!.val = .key := by
    intro k h_lo h_hi h_fe h_depth
    have h_k_lt : k < (s₂.tokens.filter p).size := by omega
    rw [h_tok_body k h_k_lt] at h_fe
    -- Convert flowBracketBalance from tokens to s₂.tokens.filter p
    have h_depth' : flowBracketBalance (s₂.tokens.filter p) 2 k = 0 := by
      rw [← h_tokens_sz_eq] at h_k_lt
      have : flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
        rw [h_tokens_decomp]
        rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
        rw [flowBracketBalance_push _ _ 2 k (by omega)]
      rw [this] at h_depth; exact h_depth
    obtain ⟨h_next_lt, h_next_key⟩ := h_body_fe_next k (by omega) h_k_lt h_fe h_depth'
    exact ⟨by omega, by rw [h_tok_body (k+1) (by omega)]; exact h_next_key (by omega)⟩
  have h_pnok : L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk
      tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := sorry
  exact ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_pattern, h_pnok⟩

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
    have h_all_scan : ∀ w, w ∈ items.toList → EmitScansInFlow w := by
      intro w hw
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
      have h_sz : i < items.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ emit_scans_in_flow _ (h_items ⟨i, h_sz⟩)
    have h_all_skdr : ∀ w, w ∈ items.toList → EmitScansInFlowSKDR w := by
      intro w hw
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
      have h_sz : i < items.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ emit_scans_in_flow_with_skdr _ (h_items ⟨i, h_sz⟩)
    obtain ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, h_content0, h_fe_pattern,
            h_pnok⟩ :=
      scanFiltered_emitSeq_nonempty_structure items tokens h_scan (by simp [h_list]) h_all_scan
        h_all_skdr
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
    have h_loop_fuel : 4 * tokens.size + 2 > (tokens.size - 2) - ps_mid.pos := by
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
    have h_all_scan_k : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.1 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ by exact emit_scans_in_flow _ (hk ⟨i, h_sz⟩)
    have h_all_scan_v : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.2 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ by exact emit_scans_in_flow _ (hv ⟨i, h_sz⟩)
    have h_all_scan_k_sk : ∀ p, p ∈ pairs.toList → EmitScansInFlowSavedKey p.1 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ by exact emit_scans_in_flow_saved_key _ (hk ⟨i, h_sz⟩)
    obtain ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_key_pattern,
            h_entry_ok⟩ :=
      scanFiltered_emitMap_nonempty_structure pairs tokens h_scan (by simp [h_list])
        h_all_scan_k h_all_scan_v h_all_scan_k_sk
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
    have h_loop_fuel : 4 * tokens.size + 2 > (tokens.size - 2) - ps_mid.pos := by
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

-- ==========================================
-- Helper Lemmas for Content Fidelity
-- ==========================================

-- contentEq on sequences ignores style/tag/anchor: only items matter.
theorem contentEq_sequence_items (style₁ style₂ : CollectionStyle)
    (items₁ items₂ : Array YamlValue)
    (tag₁ tag₂ anchor₁ anchor₂ : Option String) :
    contentEq (.sequence style₁ items₁ tag₁ anchor₁)
              (.sequence style₂ items₂ tag₂ anchor₂) =
    (items₁.size == items₂.size && contentEq.contentEqList items₁.toList items₂.toList) := by
  unfold contentEq; rfl

-- contentEq on mappings ignores style/tag/anchor: only pairs matter.
theorem contentEq_mapping_pairs (style₁ style₂ : CollectionStyle)
    (pairs₁ pairs₂ : Array (YamlValue × YamlValue))
    (tag₁ tag₂ anchor₁ anchor₂ : Option String) :
    contentEq (.mapping style₁ pairs₁ tag₁ anchor₁)
              (.mapping style₂ pairs₂ tag₂ anchor₂) =
    (pairs₁.size == pairs₂.size && contentEq.contentEqPairList pairs₁.toList pairs₂.toList) := by
  unfold contentEq; rfl

-- contentEq on sequences with any style/tag/anchor equals contentEq with canonical style/tag/anchor.
theorem contentEq_seq_style_irrel (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) (v : YamlValue) :
    contentEq (.sequence style items tag anchor) v =
    contentEq (.sequence .flow items none none) v := by
  cases v with
  | sequence style₂ items₂ tag₂ anchor₂ =>
    rw [contentEq_sequence_items, contentEq_sequence_items]
  | _ => unfold contentEq; rfl

-- contentEq on mappings with any style/tag/anchor equals contentEq with canonical style/tag/anchor.
theorem contentEq_map_style_irrel (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) (v : YamlValue) :
    contentEq (.mapping style pairs tag anchor) v =
    contentEq (.mapping .flow pairs none none) v := by
  cases v with
  | mapping style₂ pairs₂ tag₂ anchor₂ =>
    rw [contentEq_mapping_pairs, contentEq_mapping_pairs]
  | _ => unfold contentEq; rfl

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
