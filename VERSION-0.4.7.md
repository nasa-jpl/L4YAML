# Version 0.4.7 — Universal Round-Trip Correctness (Phase E)

**Goal:** Prove the universal round-trip theorem — that for every grammable YAML value, emitting it and re-parsing the output yields a content-equivalent result.

```lean
theorem universal_roundtrip (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYaml (emit v) = .ok docs ∧
            docs.size = 1 ∧
            contentEq v docs[0]!.value = true
```

**Status:** Open. This is the sole remaining proof obligation in the completeness/correctness pipeline.

**Codebase baseline (post-v0.4.6):** 61 proof modules, 47k LOC proof, 2,268 theorems, 0 sorry, 0 axiom, 0 admit. Build: 415/415 jobs, 0 warnings.

---

## Background: What v0.4.6 Proved

The v0.4.6 proof suite (61 modules, 2,268 theorems, 0 sorry) establishes the full pipeline from scanner through parser:

| Property | Key theorem/def | Module |
|---|---|---|
| Scanner produces valid token streams | `scan_produces_valid_tokens` (def, constructs `ValidTokenStream` witness); `scan_valid_token_stream` (theorem, `ValidTokenStreamProp`) | ScannerCorrectness |
| Parser produces valid nodes | `parseYaml_produces_valid_nodes` (unconditional — discharges the `h_grammable` hypothesis from `parseStream_respects_grammar`) | ParserGrammable |
| Acceptance strictness | `scan_strict_proof` (`scan .ok → InYamlLanguage`), `parse_strict_proof` (`parseYaml .ok → InYamlLanguage`) | DocumentProduction |
| Soundness, completeness, determinism | `parse_sound`, `parse_complete`, `parse_deterministic` | EndToEndCorrectness |

**`scan_strict_proof` bonus for round-trip:** Once Step 1 proves `Scanner.scanFiltered (emit v) = .ok tokens`, we also obtain `InYamlLanguage (emit v)` for free — emitter output is provably in the YAML 1.2.2 formal language. The round-trip theorem doesn't *require* grammar membership (it only needs parse success), but this strengthens the result.

---

## Existing Infrastructure

The following theorems are already proven and form the foundation for Phase E.

### Canonical Emitter (`Emitter.lean`)

The `emit` function produces a restricted subset of YAML:
- **All scalars**: double-quoted via `emitScalar` (`"\"" ++ escapeString content ++ "\""`)
- **All sequences**: flow-style `[v₁, v₂, ...]`
- **All mappings**: flow-style `{k₁: v₁, k₂: v₂, ...}`
- **No block-style constructs**: no indentation-sensitive output, no plain scalars, no block scalars

This restriction is what makes Phase E tractable — the emitter avoids the hardest scanner edge cases (plain scalar disambiguation, block indent tracking, multi-line folding).

### Content Equivalence (`RoundTrip.lean`)

| Theorem | Signature |
|---|---|
| `contentEq_refl` | `(v : YamlValue) : contentEq v v = true` |
| `contentEq_symm` | `(v₁ v₂ : YamlValue) (h : contentEq v₁ v₂ = true) : contentEq v₂ v₁ = true` |
| `contentEq_trans` | `(v₁ v₂ v₃ : YamlValue) (h₁ : ...) (h₂ : ...) : contentEq v₁ v₃ = true` |
| `contentEq_ignores_style` | `(content : String) (s₁ s₂ : ScalarStyle) (t₁ t₂ : Option String) : contentEq (.scalar ⟨content, s₁, t₁, _, _⟩) (.scalar ⟨content, s₂, t₂, _, _⟩) = true` |

### Escape–Resolve Invertibility (`RoundTrip.lean`)

| Theorem | Signature |
|---|---|
| `escapeTag_roundtrip` | `(c : Char) (tag : Char) (h : escapeTag c = some tag) : escapeChar c = "\\" ++ tag.toString ∧ resolveNamedEscape tag = some c` |
| `escapeChar_identity` | `(c : Char) (h : isEscapedChar c = false) : escapeChar c = c.toString` |
| 13 per-character theorems | `escape_resolve_null` through `escape_resolve_slash` |

### Emit–Parse Bridge (`ScannerEmitBridge.lean`)

| Theorem | Signature |
|---|---|
| `emit_stripAnnotations` | `(v : YamlValue) : emit (stripAnnotations v) = emit v` |
| `contentEq_implies_emit_eq` | `(v₁ v₂ : YamlValue) (h : contentEq v₁ v₂ = true) : emit v₁ = emit v₂` |
| `emit_pipeline_decompose` | `(v : YamlValue) (docs : Array YamlDocument) (h : parseYamlRaw (emit v) = .ok docs) : ∃ tokens, Scanner.scanFiltered (emit v) = .ok tokens ∧ parseStream tokens = .ok docs` |
| `canonical_roundtrip_conditional` | `(n : ValidNode) (docs : ...) (h_parse : parseYamlRaw (emit (toYamlValue n)) = .ok docs) (h_grammable : ...) : ∀ i : Fin docs.size, ∃ m : ValidNode, stripAnnotations (toYamlValue m) = stripAnnotations docs[i].value` |
| `emit_parse_has_witness` | `(v : YamlValue) (_hg : Grammable v false) (docs : ...) (h_parse : parseYamlRaw (emit v) = .ok docs) (h_grammable : ...) : ∀ i : Fin docs.size, ∃ m : ValidNode, ...` |

### End-to-End Correctness (`EndToEndCorrectness.lean`)

| Theorem | Signature |
|---|---|
| `parse_sound` | `(input : String) (docs : ...) (h : parseYaml input = .ok docs) : ValidYamlProp input docs` |
| `parse_complete` | `(input : String) (docs : ...) (h : ValidYamlProp input docs) : parseYaml input = .ok docs` |
| `parse_deterministic` | `(input : String) (docs₁ docs₂ : ...) (h₁ : ...) (h₂ : ...) : docs₁ = docs₂` |
| `parseStream_respects_grammar_unconditional` | `(input tokens docs) (h_scan h_parse) : ∀ doc ∈ docs.toList, ∃ node : ValidNode, stripAnnotations (toYamlValue node) = stripAnnotations (doc.compose.value)` |

### Parser Grammability (`ParserGrammable.lean`)

| Theorem | Signature |
|---|---|
| `parseStream_output_grammable` | `(input tokens raw_docs) (h_scan h_parse) : ∀ doc ∈ raw_docs.toList, Grammable doc.compose.value false` |
| `parseYaml_produces_valid_nodes` | `(input docs) (h : parseYaml input = .ok docs) : ∀ doc ∈ docs.toList, ∃ node : ValidNode, stripAnnotations (toYamlValue node) = stripAnnotations doc.value` |

---

## Implementation Plan

### Step 1: `emit_produces_valid_yaml` — Emitter Output Is Scanner-Accepted

This is the key missing lemma and the core work of v0.4.7:

```lean
theorem emit_produces_valid_yaml (v : YamlValue) (hg : Grammable v false) :
    ∃ tokens : Array (Positioned YamlToken),
      Scanner.scanFiltered (emit v) = .ok tokens
```

**Why this is tractable:** The canonical emitter output is a strict subset of YAML:
- Only double-quoted scalars → scanner's `collectDoubleQuotedLoop` handles these without disambiguation
- Only flow collections → no block-style indent tracking needed
- No plain scalars → avoids the hardest scanner edge case (plain scalar termination)
- Single-line output → no line break folding, no chomping indicators

**Proof strategy — structural induction on `YamlValue`:**

1. **Base case (scalar):** `emit (.scalar ⟨content, _, _, _, _⟩) = "\"" ++ escapeString content ++ "\""`. Show the scanner accepts this double-quoted string. Use `escapeTag_roundtrip` and the 13 per-character escape theorems to show every escaped character is a valid YAML escape sequence.

2. **Sequence case:** `emit (.sequence _ items _) = "[" ++ emitList items ++ "]"`. By inductive hypothesis, each `emit item` is scanner-accepted. Show the scanner accepts the `[`, comma separators, and `]` flow indicators, and that concatenation preserves scannability.

3. **Mapping case:** `emit (.mapping _ pairs _) = "{" ++ emitPairList pairs ++ "}"`. Similar to sequences — each key and value is scanner-accepted by IH, and `{`, `:`, `,`, `}` are flow indicators.

**Concrete sub-lemmas needed:**

| Lemma | Statement |
|---|---|
| `scan_double_quoted_string` | `∀ s, (∀ c ∈ s.toList, validEscapedChar c) → Scanner.scanFiltered ("\"" ++ escapeString s ++ "\"") = .ok [...]` |
| `scan_flow_sequence` | Scanner accepts `[tok₁, tok₂, ...]` when each `tokᵢ` is scanner-accepted |
| `scan_flow_mapping` | Scanner accepts `{k₁: v₁, k₂: v₂, ...}` when each `kᵢ`, `vᵢ` is scanner-accepted |

#### Accomplishments

#### Reflections

### Step 2: Compose with Parse Pipeline

Once `emit_produces_valid_yaml` is proven, compose with existing infrastructure:

```lean
-- emit produces tokens
have h_scan := emit_produces_valid_yaml v hg
obtain ⟨tokens, h_scan_ok⟩ := h_scan
-- parseStream is total (fuel-based) → always produces a result for valid tokens
-- parseYaml_produces_valid_nodes gives us grammar witnesses
-- contentEq_refl closes the equivalence
```

The composition chain:

```
emit v
  → Scanner.scanFiltered (emit v) = .ok tokens     [Step 1: emit_produces_valid_yaml]
  → parseStream tokens = .ok docs                   [Step 2a: parse_emitted_tokens]
  → ∀ doc ∈ docs, Grammable doc.value false         [parseStream_output_grammable]
  → ∀ doc ∈ docs, ∃ node, strip (toYaml node) = strip doc.value
                                                     [parseYaml_produces_valid_nodes]
  → contentEq v docs[0]!.value = true               [contentEq_refl + emit_stripAnnotations
                                                      + contentEq_implies_emit_eq]
```

**Step 2a gap — `parseStream` success:** Scanner success (`scanFiltered = .ok tokens`) does NOT automatically imply parser success (`parseStream tokens = .ok docs`). The `parseStream` function is total (fuel-based, always terminates), but it can return `.error` for syntactically valid but semantically ill-formed token sequences. For emitter output, we need to show that the scanner produces well-formed tokens that the parser will accept. Two approaches:

1. **Direct:** Prove `parseStream` succeeds on tokens from canonical emitter output (characterize the token sequence `emit` produces and show `parseStream` accepts it).
2. **Via `parseYamlRaw`:** Show `parseYamlRaw (emit v) = .ok docs` directly, which bundles scan + parse. The existing `canonical_roundtrip_conditional` and `emit_parse_has_witness` are already conditioned on this — discharging it is the real work.

### Step 3: Close the Universal Round-Trip

Combine Steps 1–2 into the final theorem. The key connector is that `emit` is deterministic and `contentEq` is an equivalence relation, so:

1. `emit v` produces a string `s`
2. `scanFiltered s` succeeds (Step 1)
3. `parseStream` succeeds (totality)
4. The parsed value is content-equivalent to the original (emit normalizes style, contentEq ignores style)

The existing `canonical_roundtrip_conditional` already captures steps 2–4 conditionally on `parseYamlRaw (emit v) = .ok docs`. Step 1 discharges that condition.

---

## Risk Assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| Scanner tokenization proof is complex for double-quoted strings | Medium | Limited to one scalar style; `escapeTag_roundtrip` already inverts escapes |
| Flow collection nesting requires inductive scanner acceptance | Medium | Canonical emitter produces flat output; nesting depth bounded by `Grammable` |
| `parseStream` success gap (scan `.ok` ≠ parse `.ok`) | Medium | Emitter output is structurally simple; characterize exact token sequence |
| `contentEq` bridge from parsed result back to original value | Low | `emit_stripAnnotations` + `contentEq_implies_emit_eq` already proven |
| `parseStream` may produce multiple docs for single-value input | Low | `emit` produces no document markers (`---`/`...`); single implicit document |

---

## File Plan

| File | Action |
|---|---|
| `Lean4Yaml/Proofs/EmitterScannability.lean` | **New** — `emit_produces_valid_yaml` and sub-lemmas |
| `Lean4Yaml/Proofs/UniversalRoundTrip.lean` | **New** — `universal_roundtrip` composing all phases |
| `Lean4Yaml/Proofs/ScannerEmitBridge.lean` | Minor updates — cross-reference new module |
| `Lean4Yaml/Proofs/Completeness.lean` | Update §4 to mark Phase E as resolved |

---

## Success Criteria

- `universal_roundtrip` compiles with 0 sorry
- All existing proof files maintain 0 sorry
- Total proof suite: 0 sorry, 0 axiom, 0 admit across all modules
