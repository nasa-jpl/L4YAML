import Lean4Yaml.Grammar
import Lean4Yaml.TokenParser
import Lean4Yaml.Proofs.ScannerPlainScalarValid
import Lean4Yaml.Proofs.Composition
import Lean4Yaml.Proofs.ParserSoundness
import Lean4Yaml.Proofs.ParserGrammableBase
import Lean4Yaml.Proofs.ParserWellBehaved
import Lean4Yaml.Proofs.ParserAnchorProofs

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

Combines C1 (compose_scannable_to_grammable) and C2 (parseStream_output_scannable)
to discharge `h_grammable`.
-/

namespace Lean4Yaml.Proofs.ParserGrammable

open Lean4Yaml
open Lean4Yaml.Grammar
open Lean4Yaml.TokenParser
open Lean4Yaml.Proofs.ScannerPlainScalarValid
open Lean4Yaml.Proofs.Composition

/-- `scanFiltered` preserves `PlainScalarsValid`.
    Filtering removes non-content tokens; plain scalar tokens are preserved. -/
theorem scanFiltered_plain_scalars_valid (input : String)
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
theorem parseStream_output_grammable
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (raw_docs : Array YamlDocument)
    (h_scan : Scanner.scanFiltered input = .ok tokens)
    (h_parse : parseStream tokens = .ok raw_docs) :
    ∀ doc ∈ raw_docs.toList, Grammable doc.compose.value false := by
  intro doc hdoc
  have h_fpsv := scanFiltered_flow_aware_psv input tokens h_scan
  have h_matched := scan_flow_brackets_matched input tokens h_scan
  have h_scannable := parseStream_output_scannable tokens raw_docs h_fpsv h_matched h_parse doc hdoc
  have h_resolve := parseStream_output_aliases_resolve tokens raw_docs h_parse doc hdoc
  have h_anchors := parseStream_output_anchors_wellformed tokens raw_docs h_fpsv h_matched h_parse doc hdoc
  exact compose_grammable doc h_scannable h_resolve h_anchors

/-- **Unconditional correctness**: The full `parseYaml` pipeline produces
    documents whose values have `ValidNode` witnesses.

    Combines the final grammability result with the existing
    `parseStream_respects_grammar` theorem. -/
theorem parseYaml_produces_valid_nodes
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
    -- Each composed doc is Grammable
    have h_gram := parseStream_output_grammable input tokens raw_docs h_scan h_parse
    -- Apply existing correctness theorem
    intro doc hdoc
    rw [← h_eq] at hdoc
    -- doc ∈ (raw_docs.map compose).toList
    -- So doc = raw_doc.compose for some raw_doc ∈ raw_docs.toList
    simp only [Array.toList_map] at hdoc
    obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
    subst h_compose_eq
    -- Need: Grammable raw_doc.compose.value false
    have h_g := h_gram raw_doc h_raw_mem
    -- raw_doc.compose.value is Grammable → has ValidNode witness
    exact ParserSoundness.yamlValue_has_witness
      raw_doc.compose.value false h_g
  · simp at h

end Lean4Yaml.Proofs.ParserGrammable
