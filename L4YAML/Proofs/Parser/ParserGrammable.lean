module

public import L4YAML.Spec.Grammar
public import L4YAML.Parser.Composition
public import L4YAML.Proofs.Production.ScannerPlainScalarValid
public import L4YAML.Proofs.Composition
public import L4YAML.Proofs.Parser.ParserSoundness
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Parser.ParserScannableBase
public import L4YAML.Proofs.Parser.ParserWellBehaved
public import L4YAML.Proofs.Parser.ParserAnchorProofs

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Phase C: Discharge `h_grammable` (ParserGrammable)

This file combines the component proofs to produce the final `parseYaml_produces_valid_nodes`
theorem.

**Component files:**
- `ParserGrammableBase`: Composition layer (§1–§4)
- `ParserWellBehaved`: Parser output is `Scannable` (§5, C2)
- `ParserAnchorProofs`: Anchor/alias resolution (C2b)

## §6  Final Theorem (C3)

Combines C1 (compose_grammable / compose_scannable) and C2 (parseStream_output_scannable)
to discharge `h_grammable`.
-/

namespace L4YAML.Proofs.ParserGrammable

open L4YAML
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ParserAnchorProofs
open L4YAML.Proofs.ParserWfaProofs
open L4YAML.Proofs.ScannerPlainScalarValid
open L4YAML.Proofs.Composition

/-- `scanFiltered` preserves `PlainScalarsValid`.
    Filtering removes non-content tokens; plain scalar tokens are preserved. -/
lemma scanFiltered_plain_scalars_valid (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    PlainScalarsValid tokens :=
  fun i hi => scan_plain_scalar_valid input tokens h i hi

/-- **C3**: Every document produced by the full pipeline (scan + parse + compose)
    is `Grammable`.

    This theorem eliminates the `h_grammable` hypothesis from
    `parseStream_respects_grammar` in `ParserCorrectness.lean`.

    **Architecture**: Chains B3.5 → C2 → C1 → Grammable.

    **Precondition on anchors**: `WellFormedAnchors` requires that anchor
    values are `Grammable` at every flow context. This excludes the
    pathological case where block-context plain scalars with flow
    indicators are aliased into flow context. See §4 for details. -/
lemma parseStream_output_grammable
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (raw_docs : Array YamlDocument)
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .ok raw_docs)
    (h_af : ∀ doc ∈ raw_docs.toList, AliasFree doc.value) :
    ∀ doc ∈ raw_docs.toList, Grammable doc.compose.value false := by
  intro doc hdoc
  have h_fpsv := scanFiltered_flow_aware_psv input tokens h_scan
  have h_matched := scan_flow_brackets_matched input tokens h_scan
  have h_scannable := parseStream_output_scannable tokens raw_docs h_fpsv h_matched h_parse doc hdoc
  exact compose_grammable doc h_scannable (h_af doc hdoc)

/-- **Unconditional scannability of the composed value.**

    The `Grammable` form above needs `AliasFree` on the input, because an alias
    with no preceding definition survives composition: §3.2.2.2 resolves against
    the most recent preceding event, and a collection's anchor binds only after
    its items, so a node that has itself as a descendant via an alias
    (§3.2.1.3) keeps its `.alias`.  `Grammable` has no constructor for that.

    `Scannable` does, so this form needs no hypothesis on the input — which is
    what the unconditional capstone requires. -/
lemma parseStream_output_scannable_composed
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (raw_docs : Array YamlDocument)
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .ok raw_docs) :
    ∀ doc ∈ raw_docs.toList, Scannable doc.compose.value false := by
  intro doc hdoc
  have h_fpsv := scanFiltered_flow_aware_psv input tokens h_scan
  have h_matched := scan_flow_brackets_matched input tokens h_scan
  have h_scannable := parseStream_output_scannable tokens raw_docs h_fpsv h_matched h_parse doc hdoc
  exact compose_scannable doc h_scannable

/-- **Unconditional correctness**: The full `parseYaml` pipeline produces
    documents whose values have `ValidNode` witnesses.

    Combines the final grammability result with the existing
    `parseStream_respects_grammar` theorem. -/
lemma parseYaml_produces_valid_nodes
    (input : String)
    (docs : Array YamlDocument)
    (h : parseYaml input = .ok docs) :
    ∀ doc ∈ docs.toList, ∃ node : ValidNode,
      stripAnnotations (toYamlValue node) = stripAnnotations doc.value := by
  -- Decompose parseYaml into parseYamlRaw + compose
  simp only [parseYaml] at h
  split at h
  · rename_i raw_docs h_raw
    injection h with h_eq
    -- raw_docs are the pre-compose documents
    -- docs = raw_docs.map YamlDocument.compose
    -- Decompose parseYamlRaw into scan + parseStream
    have ⟨tokens, h_scan, h_parse⟩ := parseYamlRaw_ok_decompose input raw_docs h_raw
    -- Each composed doc is Scannable — unconditionally, which `Grammable`
    -- cannot be: a self-descendant alias survives composition (§3.2.1.3).
    have h_gram := parseStream_output_scannable_composed input tokens raw_docs h_scan h_parse
    -- Apply existing correctness theorem
    intro doc hdoc
    rw [← h_eq] at hdoc
    -- doc ∈ (raw_docs.map compose).toList
    -- So doc = raw_doc.compose for some raw_doc ∈ raw_docs.toList
    simp only [Array.toList_map] at hdoc
    obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
    subst h_compose_eq
    -- Need: Scannable raw_doc.compose.value false
    have h_g := h_gram raw_doc h_raw_mem
    -- raw_doc.compose.value is Scannable → has ValidNode witness, the alias
    -- case carried by `ValidNode.aliasNode` ([104] c-ns-alias-node).
    exact ParserSoundness.scannableValue_has_witness
      raw_doc.compose.value false h_g
  · simp at h

end L4YAML.Proofs.ParserGrammable

end Blanket
