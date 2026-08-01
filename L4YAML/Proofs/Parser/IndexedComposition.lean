/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Parser.IndexedComposition

/-! # `IndexedComposition` proofs — Phase 3 Step 6e end-to-end corpus (staging)

**Status**: staging file. Not imported by `L4YAML.lean` until the
Phase 3 Step 6f cutover commit.

## Role

Indexed twin of the corpus-exhibit half of Step 5c
(`Proofs/Scanner/IndexedRoundtrip.lean`), reparented onto
`scanAndParseIx` (from `Parser/IndexedComposition.lean`).

For each input in the fixed corpus, the theorem `scanAndParseIx`
either succeeds with the expected document count or fails with
the expected error. Every proof is `native_decide`: the whole
pipeline is computable, so the kernel just reduces the goal.

This sub-step is the parser-level analogue of Step 5c
(`IndexedRoundtrip`): an end-to-end property exhibited on a fixed
corpus, gated by the `native_decide` budget — no symbolic
reasoning.

## Scope

- §1: success cases — inputs where `scanAndParseIx` returns
  `.ok docs` with a known `docs.size`.
- §2: error cases — inputs where `scanAndParseIx` returns
  `.error` (the expected failure modes of the pipeline).

The corpus deliberately covers both branches so the `.ok` and
`.error` legs of the composition are both exhibited.

## Notes on the indexed parser's current scalar content

Plain-scalar content extraction in the indexed pipeline is not
yet at parity with the legacy parser for all positions (root
plain scalars come through with empty `content`; mapping keys and
flow-collection entries do not). The corpus below only asserts
`.ok` vs `.error` and `docs.size`, so it is robust to the
plain-scalar content quirks that will be resolved during Step 6f
cutover or the broader Phase 4 scanner work.

## Phase 3 Step 6f cutover

At cutover, this file is renamed to
`Proofs/Parser/ParserComposition.lean` (or absorbed into an
existing parser-composition proof file) and the namespace
`L4YAML.Proofs.Indexed.Composition` reverts to
`L4YAML.Proofs.ParserComposition`.

## Zero Axioms

All theorems close by `native_decide`. No `sorry`, no `axiom`,
no `partial`.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.Composition

open L4YAML
open L4YAML.Scanner.Indexed.ScannerStateIx
open L4YAML.TokenParser.Indexed

/-- A success-case check: `scanAndParseIx input` returns `.ok docs`
    with `docs.size = n`. Bundling the success branch and the
    expected size into a `Bool`-valued predicate makes each
    corpus theorem one `native_decide` on a single equation. -/
def parsesToNDocs (input : String) (n : Nat) : Bool :=
  match scanAndParseIx input with
  | .ok docs => docs.size == n
  | .error _ => false

/-- An error-case check: `scanAndParseIx input` returns `.error _`.
    Used to exhibit the error-propagation leg of the composition
    on inputs that the scanner or parser rejects. -/
def parsesError (input : String) : Bool :=
  match scanAndParseIx input with
  | .ok _ => false
  | .error _ => true

/-! ## §1  Success-case corpus

Each entry exhibits `scanAndParseIx input = .ok docs` for a known
`docs.size`. The corpus spans:
- The empty stream (0 docs)
- Single root scalars (1 doc)
- Block-sequence root (1 doc)
- Flow-collection roots (1 doc each)
- A block-style implicit key (2 docs in the current indexed
  parser, see the file docstring) -/

lemma parses_empty : parsesToNDocs "" 0 = true := by native_decide

lemma parses_plain_x : parsesToNDocs "x" 1 = true := by native_decide

lemma parses_plain_abc : parsesToNDocs "abc" 1 = true := by native_decide

lemma parses_block_seq_one : parsesToNDocs "- x" 1 = true := by native_decide

lemma parses_flow_seq_empty : parsesToNDocs "[]" 1 = true := by native_decide

lemma parses_flow_map_empty : parsesToNDocs "{}" 1 = true := by native_decide

lemma parses_flow_seq_three : parsesToNDocs "[1,2,3]" 1 = true := by native_decide

lemma parses_block_map_one : parsesToNDocs "a: b" 1 = true := by native_decide

/-- A two-line block mapping. After Step 6f.0 indexed parser parity,
    the indexed pipeline accepts this (was previously erroring; the
    file docstring noted "implicit-key" divergence is no longer
    observed). -/
lemma parses_block_map_two_lines : parsesToNDocs "a: 1\nb: 2" 1 = true := by native_decide

/-! ## §2  Error-case corpus

Each entry exhibits `scanAndParseIx input = .error _` for an
input that the pipeline rejects. The cases cover scanner-emitted
errors (unterminated flow collections). After Step 6f.0 the indexed
parser no longer errors on multi-line block mappings — the
implicit-key divergence noted in the original Step 6e file
docstring is closed. -/

lemma parses_error_unterminated_flow_seq :
    parsesError "[" = true := by native_decide

/-! ## §3  Pipeline Decomposition (Step 6f.3b1)

Structural decomposition theorems for the indexed pipeline, twins of
`L4YAML.Proofs.Composition.parseYamlRaw_*` / `parseYaml_*`. These are
required by downstream consumers (`EndToEndCorrectness`,
`ScannerEmitBridge`, etc.) at Step 6f.3b. Each proof is a one-line
`simp only [...]` over the indexed pipeline definitions; the work
is purely propagating the `Ix`-suffixed names.

The legacy `Composition.parseYamlRaw_pipeline`/`_ok_decompose`
family quantified over `tokens : Array (Positioned YamlToken)`; the
indexed twins quantify over `Indexed.TokenStream input` since the
indexed `parseStreamIx` operates on the input-indexed token stream.
-/

/-- `parseYamlRawIx` decomposes into scanning then parsing: if both
    stages succeed, the result is the `parseStreamIx` output on the
    scanned tokens. Indexed twin of
    `L4YAML.Proofs.Composition.parseYamlRaw_pipeline`. -/
lemma parseYamlRawIx_pipeline (input : String)
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_scan : scanFilteredIx input = .ok tokens)
    (h_parse : parseStreamIx tokens = .ok docs) :
    parseYamlRawIx input = .ok docs := by
  simp only [parseYamlRawIx, scanAndParseIx, h_scan, h_parse]

/-- If `parseYamlRawIx` succeeds, then both `scanFilteredIx` and
    `parseStreamIx` must have succeeded on some intermediate token
    stream. Indexed twin of
    `L4YAML.Proofs.Composition.parseYamlRaw_ok_decompose`. -/
lemma parseYamlRawIx_ok_decompose (input : String) (docs : Array YamlDocument)
    (h : parseYamlRawIx input = .ok docs) :
    ∃ tokens : Indexed.TokenStream input,
      scanFilteredIx input = .ok tokens ∧ parseStreamIx tokens = .ok docs := by
  simp only [parseYamlRawIx, scanAndParseIx] at h
  match h_scan : scanFilteredIx input with
  | .ok tokens =>
    simp only [h_scan] at h
    match h_parse : parseStreamIx tokens with
    | .ok docs' =>
      simp only [h_parse, Except.ok.injEq] at h
      subst h; exact ⟨tokens, rfl, h_parse⟩
    | .error _ =>
      simp only [h_parse] at h; contradiction
  | .error _ =>
    simp only [h_scan] at h; contradiction

/-- If `scanFilteredIx` fails, `parseYamlRawIx` fails with the same
    error. Indexed twin of
    `L4YAML.Proofs.Composition.parseYamlRaw_scan_error`. -/
lemma parseYamlRawIx_scan_error (input : String) (e : ScanError)
    (h : scanFilteredIx input = .error e) :
    parseYamlRawIx input = .error e := by
  simp only [parseYamlRawIx, scanAndParseIx, h]

/-- If `scanFilteredIx` succeeds but `parseStreamIx` fails,
    `parseYamlRawIx` fails with the same parse error. Indexed twin of
    `L4YAML.Proofs.Composition.parseYamlRaw_parse_error`. -/
lemma parseYamlRawIx_parse_error (input : String) (e : ScanError)
    (tokens : Indexed.TokenStream input)
    (h_scan : scanFilteredIx input = .ok tokens)
    (h_parse : parseStreamIx tokens = .error e) :
    parseYamlRawIx input = .error e := by
  simp only [parseYamlRawIx, scanAndParseIx, h_scan, h_parse]

/-- If `parseYamlRawIx` succeeds, `parseYamlIx` succeeds with composed
    documents. Indexed twin of
    `L4YAML.Proofs.Composition.parseYaml_of_parseYamlRaw_ok`. -/
lemma parseYamlIx_of_parseYamlRawIx_ok (input : String) (docs : Array YamlDocument)
    (h : parseYamlRawIx input = .ok docs) :
    parseYamlIx input = .ok (docs.map YamlDocument.compose) := by
  simp only [parseYamlIx, h]

/-- If `parseYamlRawIx` fails, `parseYamlIx` fails with the same
    error. Indexed twin of
    `L4YAML.Proofs.Composition.parseYaml_of_parseYamlRaw_error`. -/
lemma parseYamlIx_of_parseYamlRawIx_error (input : String) (e : ScanError)
    (h : parseYamlRawIx input = .error e) :
    parseYamlIx input = .error e := by
  simp only [parseYamlIx, h]

/-- Full pipeline composition: `scanFilteredIx → parseStreamIx →
    compose`. If scanning and parsing both succeed, `parseYamlIx`
    returns composed documents. Indexed twin of
    `L4YAML.Proofs.Composition.parseYaml_pipeline`. -/
lemma parseYamlIx_pipeline (input : String)
    (tokens : Indexed.TokenStream input)
    (docs : Array YamlDocument)
    (h_scan : scanFilteredIx input = .ok tokens)
    (h_parse : parseStreamIx tokens = .ok docs) :
    parseYamlIx input = .ok (docs.map YamlDocument.compose) :=
  parseYamlIx_of_parseYamlRawIx_ok input docs
    (parseYamlRawIx_pipeline input tokens docs h_scan h_parse)

/-- `parseYamlIx input = .ok docs` iff there exist raw documents
    from `parseYamlRawIx` that compose to `docs`. Indexed twin of
    `L4YAML.Proofs.Completeness.parseYaml_ok_iff`. -/
lemma parseYamlIx_ok_iff (input : String) (docs : Array YamlDocument) :
    parseYamlIx input = .ok docs ↔
    ∃ rawDocs : Array YamlDocument,
      parseYamlRawIx input = .ok rawDocs ∧
      docs = rawDocs.map YamlDocument.compose := by
  constructor
  · intro h
    simp only [parseYamlIx] at h
    match h_raw : parseYamlRawIx input with
    | .ok rawDocs =>
      simp only [h_raw, Except.ok.injEq] at h
      exact ⟨rawDocs, rfl, h.symm⟩
    | .error _ =>
      simp only [h_raw] at h; contradiction
  · rintro ⟨rawDocs, h_raw, h_eq⟩
    simp only [parseYamlIx, h_raw, h_eq]

end L4YAML.Proofs.Indexed.Composition
