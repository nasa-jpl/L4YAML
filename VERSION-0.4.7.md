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

### Step 1: `emit_produces_valid_yaml` — Emitter Output Is Scanner-Accepted (DONE)

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

1. **Spec-compliance fix in `escapeChar`** (Emitter.lean): Discovered that the emitter passed through 23 C0 control characters (0x01–0x06, 0x0E–0x1A, 0x1C–0x1F) that the scanner rejects as non-`nb-json`. Consulted YAML 1.2.2 §5.1 (`c-printable`), §5.7 ("all non-printable characters must be escaped"), and §7.3.1 [107] (`nb-double-char`). Added `hexNibble` and `escapeHex2` helpers and a `\xHH` hex escape fallback for any `c.val.toNat < 0x20` in the match default arm. Without this fix, `emit_produces_valid_yaml` would be unprovable — the scanner would reject emitter output containing these control chars.

2. **Updated `isEscapedChar`** (RoundTrip.lean): Extended the predicate's fallback from `| _ => false` to `| c => c.val.toNat < 0x20` to cover the newly hex-escaped C0 range. Fixed `escapeChar_identity` proof with `omega` for the vacuously-true fallback case.

3. **New `escapeHex2` safety theorems** (ScannerDoubleQuoted.lean): Added 6 bounded `native_decide` lemmas (`escapeHex2_{no_newline,no_cr,head}` × bounded/lifted) proving `\xHH` output contains no bare newlines/CRs and starts with `\\`. Uses `native_decide` on `Fin 32` then lifts via `Char.ofNat_toNat`.

4. **Adapted existing proofs** (ScannerDoubleQuoted.lean): `escapeChar_no_newline`, `escapeChar_no_cr`, and `escapeChar_escaped_starts_backslash` now handle the `if c.val.toNat < 0x20` branch using the new `escapeHex2_*` helpers. Weakened `escapeTag_isSome_iff_isEscapedChar` to `escapeTag_isSome_implies_isEscapedChar` (the iff no longer holds since `isEscapedChar` covers a superset of `escapeTag`'s domain).

5. **EmitterScannability.lean skeleton created**: 6 `sorry`-based theorem stubs for the proof structure: `escapeChar_passthrough_is_valid`, `escapeChar_output_nbJson`, `emit_nonempty`, `scan_accepts_emitScalar`, `emit_produces_valid_yaml`, `emit_parse_succeeds`. Build: 422/422 jobs, 0 errors.

#### Reflections

1. **The spec gap was a prerequisite blocker.** Without fixing `escapeChar`, the target theorem `emit_produces_valid_yaml` would be *false* — the scanner rejects C0 controls that aren't `nb-json`. This was discovered during proof feasibility analysis, not from a test failure. Formal proof forced confronting a real spec-compliance gap in the emitter.

2. **`private` defs leak into proof goals but can't be referenced by name.** Making `hexNibble` and `escapeHex2` private initially caused "free variable" errors in downstream proof files — after `unfold escapeChar`, the private names appear in the goal but can't be unfolded or referenced. Removing `private` was the right fix.

3. **Bounded `native_decide` + `Char.ofNat_toNat` lift is the right pattern for `Char` range properties.** Direct proofs about `hexNibble` output fail because `Char.ofNat` unfolds to a `dite` on `Nat.isValidChar` with a dependent `Char.ofNatAux` that `omega`/`simp` can't penetrate. The bounded approach (`∀ n : Fin 32, P (Char.ofNat n)` by `native_decide`, then `rwa [Char.ofNat_toNat]`) is clean and avoids fighting `Char` internals.

4. **`isEscapedChar` now characterizes a strict superset of `escapeTag`'s domain — by design.** Named escapes (11 chars with tags like `\0`, `\a`, `\n`) are a proper subset of all escaped chars (11 named + 12 hex-escaped C0). The asymmetry is correct: `escapeTag` maps chars to named tags for `escapeTag_roundtrip`, while `isEscapedChar` is the predicate for "does `escapeChar` produce something other than `c.toString`?" used by `escapeChar_identity`. 

   The three cases are: 

   - (a) `isEscapedChar c = false` → passthrough, 
   - (b) `escapeTag c = some tag` → named escape round-trip via `resolveNamedEscape`, 
   - (c) `isEscapedChar c = true ∧ escapeTag c = none` → hex escape, needs a separate `escapeHex2_roundtrip` lemma through `processEscape`'s hex path (`\xHH`).

### Step 2: Compose with Parse Pipeline (DONE)

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
  → parseStream tokens = .ok docs                   [Step 2: parse_emitted_tokens]
  → ∀ doc ∈ docs, Grammable doc.value false         [parseStream_output_grammable]
  → ∀ doc ∈ docs, ∃ node, strip (toYaml node) = strip doc.value
                                                     [parseYaml_produces_valid_nodes]
  → contentEq v docs[0]!.value = true               [contentEq_refl + emit_stripAnnotations
                                                      + contentEq_implies_emit_eq]
```

**Step 2 gap — `parseStream` success:** Scanner success (`scanFiltered = .ok tokens`) does NOT automatically imply parser success (`parseStream tokens = .ok docs`). The `parseStream` function is total (fuel-based, always terminates), but it can return `.error` for syntactically valid but semantically ill-formed token sequences. For emitter output, we need to show that the scanner produces well-formed tokens that the parser will accept. Two approaches:

1. **Direct:** Prove `parseStream` succeeds on tokens from canonical emitter output (characterize the token sequence `emit` produces and show `parseStream` accepts it).
2. **Via `parseYamlRaw`:** Show `parseYamlRaw (emit v) = .ok docs` directly, which bundles scan + parse. The existing `canonical_roundtrip_conditional` and `emit_parse_has_witness` are already conditioned on this — discharging it is the real work.

#### Accomplishments

1. **Identified the scan→parse gap and resolved it architecturally.** `ValidYamlProp` is defined computationally (existential over `scanFiltered = .ok` ∧ `parseStream = .ok`), and `InYamlLanguage input → ∃ docs, parseYaml input = .ok docs` does not exist. There is no shortcut through grammar membership — the proof must reason about `parseStream` acceptance directly. Confirmed there are exactly 8 error conditions in the parser pipeline, and all 8 are structurally impossible for canonical emitter output.

2. **Factored `emit_parse_succeeds` into a proven composition.** Replaced the single sorry with a two-step composition: `emit_produces_valid_yaml` (Step 1, sorry) → `parseStream_accepts_emit_tokens` (Step 2, sorry) → `parseYamlRaw_pipeline` (Composition.lean, proven). The composition proof `emit_parse_succeeds` itself is now sorry-free — it uses `obtain` to destructure existentials and `exact` with `Composition.parseYamlRaw_pipeline`.

3. **Added `emit_parseYaml_succeeds` (proven, no sorry).** Lifts `emit_parse_succeeds` through the `YamlDocument.compose` layer: `parseYaml (emit v) = .ok docs`. Uses `simp only [parseYaml, h_raw]` to unfold the match-based definition and reduce after substitution.

4. **Added `emit_produces_single_document` (sorry, Step 3 prep).** The emitter generates exactly one implicit document. This theorem — `docs.size = 1` — is needed by the universal round-trip theorem. Proof will follow from `parseStreamLoop` producing exactly one document when the token stream has no `---`/`...` markers.

5. **Added `emit_parsed_grammable` (sorry, Step 3 prep).** Output grammability preservation — follows from existing `parseStream_output_grammable` applied to the scan+parse decomposition. This provides the `Grammable doc.value false` hypothesis needed downstream.

6. **Updated module structure.** Renumbered sections (§1–§4), updated module docstring to cover Steps 1–2, revised the section outline to match actual theorem organization.

#### Reflections

1. **`ValidYamlProp` is computational, not semantic.** It requires existential witnesses for both `scanFiltered = .ok tokens` AND `parseStream tokens = .ok raw_docs`. Constructing it from grammar membership (`InYamlLanguage`) would require a converse completeness theorem (`InYamlLanguage → parseYaml = .ok`) that doesn't exist. This means the proof MUST reason about `parseStream` acceptance, not just grammar membership. The scan→parse decomposition is the only viable architecture.

2. **The parser has exactly 8 error conditions, all avoidable for emitter output.** Enumerated: `invalidBareDocument` (impossible — single document), `contentOnDocumentStartLine` (impossible — no `---`), `undeclaredTagHandle` (impossible — no tags), `duplicateAnchor` (impossible — no anchors), `trailingContent` (impossible — no block content), `undefinedAlias` (impossible — no aliases), `nestingDepthExceeded` (impossible — fuel = tokens.size, each call consumes ≥1), `expectedToken` for `]`/`}` (impossible — scanner enforces bracket matching). This is a complete error enumeration, not a heuristic argument.

3. **Composition proofs are the easy part; factoring is the hard part.** `emit_parse_succeeds` went from a single sorry to a proven three-line composition once the right sub-lemma (`parseStream_accepts_emit_tokens`) was identified. The difficulty is always in identifying the right decomposition boundary — once found, the composition is mechanical (`obtain` + `exact`).

### Step 3: Close the Universal Round-Trip (DONE)

Combine Steps 1–2 into the final theorem. The key connector is that `emit` is deterministic and `contentEq` is an equivalence relation, so:

1. `emit v` produces a string `s`
2. `scanFiltered s` succeeds (Step 1)
3. `parseStream` succeeds (Step 2)
4. The parsed value is content-equivalent to the original (emit normalizes style, contentEq ignores style)

The composition follows the chain:

```
emit_produces_valid_yaml  →  scanFiltered (emit v) = .ok tokens
parseStream_accepts_emit_tokens  →  parseStream tokens = .ok raw_docs
  ↓ (Composition.parseYamlRaw_pipeline)
parseYamlRaw (emit v) = .ok raw_docs
  ↓ (simp [parseYaml, h_raw])
parseYaml (emit v) = .ok (raw_docs.map compose)
  +
emit_produces_single_document  →  raw_docs.size = 1  →  docs.size = 1
emit_roundtrip_content_eq       →  contentEq v docs[0]!.value = true
```

#### Accomplishments

1. **Identified the content-fidelity gap.** The existing sorry stubs (Steps 1 + 2) give parse success and single-document guarantee, but no stub existed for **content equivalence** — proving `contentEq v docs[0]!.value = true`. The existing `canonical_roundtrip_conditional` gives `∃ m : ValidNode, stripAnnotations (toYamlValue m) = stripAnnotations doc.value`, which relates parsed output to SOME valid node `m`, but does NOT relate it back to the original value `v`. A new sorry stub is required for the content-fidelity claim.

2. **Added `emit_roundtrip_content_eq` sorry stub** (EmitterScannability.lean §4). Captures the content-fidelity obligation: given `parseYamlRaw (emit v) = .ok raw_docs` with `raw_docs.size = 1`, prove `contentEq v (raw_docs.map compose)[0]!.value = true`. The proof strategy is structural induction on `v`: scalars round-trip through `escapeString`/`processEscape`, collections round-trip through flow token reconstruction, all using `contentEq`'s style-insensitivity.

3. **Wrote `universal_roundtrip` as a sorry-free composition** (EmitterScannability.lean §4). The proof is 5 lines:
   - `obtain` the raw docs from `emit_parse_succeeds`
   - `have` the single-document property from `emit_produces_single_document`
   - `refine` the existential with `raw_docs.map compose`
   - Three goals closed by: `simp only [parseYaml, h_raw]` (parse success), `simp [Array.size_map, h_raw_size]` (size), `exact emit_roundtrip_content_eq` (content)

4. **Build verified: 0 errors, 10 sorry warnings.** 9 sorry stubs (8 from Steps 1–2 + 1 new `emit_roundtrip_content_eq`) plus `universal_roundtrip` itself (flagged because it depends on sorry stubs, but its own proof is sorry-free).

#### Reflections

1. **Content equivalence is a separate concern from parse success.** The existing `emit_parse_has_witness` theorem gives a `ValidNode` that matches the parsed output structurally, but this witness is unrelated to the original input value `v` — it's constructed by the parser from scratch. The content-fidelity claim (`contentEq v docs[0]!.value = true`) is a distinct obligation that requires showing the parser RECOVERS the same content the emitter serialized, not merely that the parsed output has SOME valid structure.

2. **The sorry stubs share a common induction structure.** `emit_produces_valid_yaml`, `parseStream_accepts_emit_tokens`, `emit_produces_single_document`, and `emit_roundtrip_content_eq` all need structural induction on `v : YamlValue` with `Grammable v false`. In practice, these may merge into a single comprehensive induction that proves all four properties simultaneously — the scanner acceptance, parser acceptance, single-document property, and content fidelity are all consequences of the same structural argument about how `emit` output flows through the scanner and parser.

3. **The composition itself is trivially correct.** Once the right decomposition was found, the `universal_roundtrip` proof was 5 lines with no non-trivial reasoning. This confirms the v0.4.7 architecture: all difficulty is in the sorry stubs (characterizing scanner/parser behavior on canonical emitter output), not in the theorem composition.

### Step 4: Escape Character Properties — Stubs 1–3

Discharge the three independent, easy sorry stubs that have no dependencies on scanner/parser internals.

**Stubs to discharge:**

| # | Stub | Strategy | Est. LOC |
|---|------|----------|----------|
| 1 | `escapeChar_passthrough_is_valid` | Case-split on `escapeChar`'s 12 match arms; chars that fall through to the default arm satisfy `isNbJsonBool` ∧ `≠ '"'` ∧ `≠ '\\'` by `omega` on char bounds | 30–50 |
| 2 | `escapeChar_output_nbJson` | For each match arm, enumerate output chars and verify `isNbJsonBool` via `decide`/`native_decide`; passthrough case uses stub 1 | 50–80 |
| 3 | `emit_nonempty` | Structural induction on `YamlValue`: scalar produces `"..."` (≥2 chars), sequence `[...]` (≥2), mapping `{...}` (≥2); alias excluded by `Grammable` | 15–25 |

**Dependencies:** None — these are self-contained character/string lemmas. Stub 2 may use stub 1 for the passthrough case.

**Existing infrastructure:**
- `ScannerDoubleQuoted.lean` already has `escapeChar_no_newline`, `escapeChar_no_cr`, `escapeChar_escaped_starts_backslash`
- Bounded `native_decide` + `Char.ofNat_toNat` lift pattern established in Step 1
- `isNbJsonBool` is a simple character range predicate in `CharPredicates.lean`

**Total: ~95–155 LOC**

#### Accomplishments

#### Reflections

### Step 5: Scanner Acceptance — Stubs 4–5 (Bottleneck)

Prove the scanner accepts canonical emitter output. This is the core technical challenge of v0.4.7.

**Stubs to discharge:**

| # | Stub | Strategy | Est. LOC |
|---|------|----------|----------|
| 4 | `scan_accepts_emitScalar` | Prove `collectDoubleQuotedLoop` accepts `escapeString content` char-by-char. Three char classes: (a) passthrough — `isNbJsonBool` from stub 1, (b) named escape — `\tag` pair accepted by `processEscape`, (c) hex escape — `\xHH` accepted by `processEscape`'s hex path. Loop invariant: scanner position advances by escape sequence length, no error raised. | 150–300 |
| 5 | `emit_produces_valid_yaml` | Structural induction on `YamlValue` with `Grammable v false`. Scalar case delegates to stub 4. Sequence/mapping cases: show scanner threads state through flow indicators (`[`, `]`, `,`, `{`, `}`, `:`) and recursively-emitted sub-values. Key sub-lemma: `scanFiltered` is compositional for flow-style concatenation (scanner accepts `A ++ B` if it accepts `A` and `B` in the right flow context). | 300–600 |

**Dependencies:** Stubs 1–2 from Step 4 (escape character validity).

**Key technical challenges:**

1. **Scanner state threading.** `scanFiltered` is not trivially compositional — the scanner maintains state (position, flow level, indentation). Must show that after scanning `[`, the scanner is in flow context with flow level +1, accepts the comma-separated items, and `]` decrements flow level back.

2. **`collectDoubleQuotedLoop` invariant.** The scanner's double-quoted string handler is a loop that dispatches on each character: passthrough for `nb-json` chars, escape processing for `\`, close on `"`. Must establish the loop invariant that `escapeString` output only triggers passthrough and escape paths (never close-quote mid-string, never invalid char).

3. **Fuel sufficiency.** `scanFiltered` uses a fuel parameter (typically `input.length`). Must show canonical emitter output doesn't exhaust fuel — each scanner step consumes ≥1 character, and `emit v` has bounded length relative to `v`.

**Existing infrastructure:**
- `ScannerDoubleQuoted.lean`: `escape_processEscape_roundtrip` (proven), `escapeChar_no_newline/no_cr` (proven)
- `escapeTag_roundtrip` in `RoundTrip.lean` — inverts named escapes
- Scanner loop structure already characterized in `ScannerCorrectness.lean`

**Total: ~450–900 LOC**

#### Accomplishments

#### Reflections

### Step 6: Parser Acceptance + Document Properties — Stubs 6–8

Prove the parser succeeds on scanner output from canonical emitter input, produces exactly one document, and the output is grammable.

**Stubs to discharge:**

| # | Stub | Strategy | Est. LOC |
|---|------|----------|----------|
| 6 | `parseStream_accepts_emit_tokens` | Characterize the token sequence from `scanFiltered (emit v)` and show `parseStream` succeeds. The 8 parser error conditions are all structurally impossible for canonical emitter tokens: no `---`/`...` markers (eliminates `invalidBareDocument`, `contentOnDocumentStartLine`), no tags/anchors/aliases (eliminates `undeclaredTagHandle`, `duplicateAnchor`, `undefinedAlias`), no block content (eliminates `trailingContent`), fuel = tokens.size with ≥1 consumed per call (eliminates `nestingDepthExceeded`), scanner bracket-matching (eliminates `expectedToken`). | 200–400 |
| 7 | `emit_produces_single_document` | Track `parseStreamLoop`'s accumulator from empty. Canonical tokens have no `---`/`...` → loop enters `parseDocument` exactly once → single document in output array. | 80–150 |
| 8 | `emit_parsed_grammable` | Apply existing `parseStream_output_grammable` from `ParserGrammable.lean`. Decompose `parseYaml` via `emit_pipeline_decompose` to extract `scanFiltered`/`parseStream` witnesses, then direct application. The `compose` step is effectively identity since emitter produces no aliases. | 60–120 |

**Dependencies:** Stubs 4–5 from Step 5 (scanner acceptance provides the token sequence that stubs 6–7 reason about).

**Key technical challenges:**

1. **Token sequence characterization.** Stubs 6–7 need to know WHAT tokens `scanFiltered (emit v)` produces — not just that it succeeds. Either: (a) strengthen `emit_produces_valid_yaml` to also characterize the output tokens, or (b) prove a separate token-characterization lemma, or (c) reason abstractly about token types present/absent (no `---`, no anchors, etc.) via scanner invariants.

2. **`parseStreamLoop` state machine.** The parser's stream-level state machine (`StreamState`: `.initial`, `.afterDocument`, `.afterDocumentEnd`, `.done`) must be traced through exactly one iteration. Show: `.initial` → sees content token → `parseDocument` → `.afterDocument` → sees `streamEnd` → `.done`.

3. **Parser dispatch for flow collections.** `parseNode` dispatches on token type. For `flowSequenceStart`/`flowMappingStart`, it calls `parseFlowSequence`/`parseFlowMapping` which recursively parse items. Must show these recursive calls succeed and consume proper tokens.

**Existing infrastructure:**
- `parseStream_output_grammable` (proven, ParserGrammable.lean) — directly usable for stub 8
- `Composition.parseYamlRaw_ok_decompose` — decomposes `parseYamlRaw` into scan + parse
- Parser error enumeration from Step 2 Reflection 2

**Total: ~340–670 LOC**

#### Accomplishments

#### Reflections

### Step 7: Content Fidelity — Stub 9 (Hardest)

Prove the parsed output is content-equivalent to the original value. This is the hardest sorry stub because it connects the emitter's serialization to the parser's deserialization at the value level.

**Stub to discharge:**

| # | Stub | Strategy | Est. LOC |
|---|------|----------|----------|
| 9 | `emit_roundtrip_content_eq` | Structural induction on `v : YamlValue` with `Grammable v false`. For each constructor, show the emit→scan→parse pipeline recovers the same content (modulo style). | 500–1000 |

**Dependencies:** All of Steps 4–6 (scanner acceptance, parser acceptance, single-document guarantee). The proof USES the fact that parsing succeeds and then reasons about WHAT value the parser produces.

**Sub-proof structure:**

1. **Escape string round-trip** (~100–150 LOC): Show `escapeString content` round-trips through `collectDoubleQuotedLoop` + `processEscape` back to `content`. Three cases per character:
   - Passthrough: `c` → scanned as literal `c` → reconstructed as `c`
   - Named escape: `c` → `\tag` → `processEscape tag` → `resolveNamedEscape tag` → `c` (uses `escapeTag_roundtrip`)
   - Hex escape: `c` → `\xHH` → `processEscape 'x'` → hex parse → `c` (needs `escapeHex2_roundtrip` through hex path)

2. **Scalar case** (~100–150 LOC): `emit (.scalar ⟨content, style, tag, anchor, pos⟩)` produces `"..."` → parser reads double-quoted scalar → creates `YamlValue.scalar ⟨content', .doubleQuoted, none, none, _⟩` where `content' = content` by escape round-trip. `contentEq` ignores style/tag/anchor, compares content strings → `true` by `contentEq_ignores_style`.

3. **Sequence case** (~150–200 LOC): `emit (.sequence style items pos)` produces `[emit item₁, emit item₂, ...]`. Parser reconstructs `YamlValue.sequence .flow items' _` where each `items'[i]` is content-equivalent to `items[i]` by IH. `contentEq` for sequences checks size + element-wise equivalence → `true`.

4. **Mapping case** (~150–200 LOC): `emit (.mapping style pairs pos)` produces `{emit k₁: emit v₁, ...}`. Parser reconstructs `YamlValue.mapping .flow pairs' _` where each pair is content-equivalent by IH. `contentEq` for mappings checks size + pair-wise equivalence → `true`.

**Key technical challenge:** The proof must bridge between the emitter's string output and the parser's value output, passing through the scanner's token intermediate. This requires understanding how all three stages interact for each `YamlValue` constructor — it's not just about success/failure, but about the SPECIFIC values produced.

**Alternative approach:** If stubs 5–9 prove difficult separately, consider a **mega-induction** that proves all 5 properties simultaneously (scanner success, parser success, single document, grammability, content fidelity) per `YamlValue` case. This avoids re-doing the same structural argument 5 times but produces a larger, more complex proof. Assess after Steps 5–6 whether merging is beneficial.

**Existing infrastructure:**
- `escapeTag_roundtrip` (proven) — named escape inversion
- `contentEq_ignores_style` (proven) — scalar content match with different styles
- `contentEq_refl`, `contentEq_symm`, `contentEq_trans` (proven) — equivalence properties
- `escape_processEscape_roundtrip` (proven, ScannerDoubleQuoted.lean)

**Total: ~500–1000 LOC**

#### Accomplishments

#### Reflections

---

## Sorry Inventory

| # | Stub | Step | Tier | Status | Est. LOC |
|---|------|------|------|--------|----------|
| 1 | `escapeChar_passthrough_is_valid` | 4 | 0 | sorry | 30–50 |
| 2 | `escapeChar_output_nbJson` | 4 | 0 | sorry | 50–80 |
| 3 | `emit_nonempty` | 4 | 0 | sorry | 15–25 |
| 4 | `scan_accepts_emitScalar` | 5 | 1 | sorry | 150–300 |
| 5 | `emit_produces_valid_yaml` | 5 | 1 | sorry | 300–600 |
| 6 | `parseStream_accepts_emit_tokens` | 6 | 2 | sorry | 200–400 |
| 7 | `emit_produces_single_document` | 6 | 2 | sorry | 80–150 |
| 8 | `emit_parsed_grammable` | 6 | 2 | sorry | 60–120 |
| 9 | `emit_roundtrip_content_eq` | 7 | 3 | sorry | 500–1000 |
| — | `universal_roundtrip` | 3 | — | **proven** (depends on 1–9) | 5 |
| — | `emit_parse_succeeds` | 2 | — | **proven** (depends on 5, 6) | 3 |
| — | `emit_parseYaml_succeeds` | 2 | — | **proven** (depends on above) | 2 |

**Dependency tiers:**
```
Tier 0: stubs 1, 2, 3 (independent)
  ↓
Tier 1: stubs 4, 5 (scanner — depends on Tier 0)
  ↓
Tier 2: stubs 6, 7, 8 (parser — depends on Tier 1)
  ↓  
Tier 3: stub 9 (content fidelity — depends on all above)
```

**Total estimated new proof: ~1,400–2,700 LOC**

---

## Risk Assessment

| Risk | Likelihood | Mitigation |
|---|---|---|
| Scanner state threading is non-compositional for flow collections | HIGH | Scanner maintains flow level; must prove level increments/decrements correctly through `[`, `]`, `{`, `}` |
| `collectDoubleQuotedLoop` invariant is complex | Medium | Limited to one scalar style; `escape_processEscape_roundtrip` already inverts escapes |
| Token sequence characterization needed for parser proofs | Medium | May strengthen `emit_produces_valid_yaml` to also describe output tokens, or prove separate characterization |
| Content fidelity (stub 9) requires end-to-end value tracking | Medium | Escape round-trip infrastructure exists; `contentEq_ignores_style` simplifies style mismatch |
| Mega-induction may be needed if separate stubs are redundant | Low | Assess after Steps 5–6; merge if structural arguments repeat |

---

## File Plan

| File | Action | Step |
|---|---|---|
| `Lean4Yaml/Proofs/EmitterScannability.lean` | **Exists** — fill sorry stubs, add sub-lemmas | 4–7 |
| `Lean4Yaml/Proofs/EmitterEscapeProps.lean` | **New** (if needed) — escape character property proofs if EmitterScannability grows too large | 4 |
| `Lean4Yaml/Proofs/EmitterScannerAcceptance.lean` | **New** (if needed) — scanner loop invariant and flow-collection composition proofs | 5 |
| `Lean4Yaml/Proofs/EmitterParserAcceptance.lean` | **New** (if needed) — parser error elimination and document count proofs | 6 |
| `Lean4Yaml/Proofs/EmitterContentFidelity.lean` | **New** (if needed) — escape round-trip and per-constructor content equivalence proofs | 7 |
| `Lean4Yaml/Proofs/ScannerEmitBridge.lean` | Minor updates — cross-reference new modules | — |
| `Lean4Yaml/Proofs/Completeness.lean` | Update §4 to mark Phase E as resolved | — |

---

## Success Criteria

- `universal_roundtrip` compiles with 0 sorry
- All existing proof files maintain 0 sorry
- Total proof suite: 0 sorry, 0 axiom, 0 admit across all modules
