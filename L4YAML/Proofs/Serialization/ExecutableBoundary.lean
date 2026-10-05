/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Composition

/-!
# Exact executable acceptance boundary

This module records the selected factorization for the load-capstone work.
`InExecutableLanguage` is the scanner-plus-token-parser
acceptance language. Since composition is total, it accepts exactly the same
inputs as `parseYaml`.

This theorem isolates the remaining, separate language bridge: relating the
current-L4YAML executable boundary to exact surface syntax and the independent
serialization event semantics. The current-runtime anchor completion policy
is distinct from YAML 1.2.2 anchor-start commitment (see CommitTrace). This
factorization is not an exactness theorem for the normative YAML language.
-/

namespace L4YAML.Proofs.Serialization

open L4YAML

/-- Exact acceptance by the scanner and token parser, before the total
`YamlDocument.compose` map. -/
def InExecutableLanguage (input : String) : Prop :=
  ∃ (tokens : Array (Positioned YamlToken)) (rawDocs : Array YamlDocument),
    Scanner.scanFiltered input = .ok tokens ∧
    TokenParser.parseStream tokens = .ok rawDocs

/-- Scanner-only acceptance. -/
def InScannerLanguage (input : String) : Prop :=
  ∃ tokens : Array (Positioned YamlToken),
    Scanner.scanFiltered input = .ok tokens

/-- The total composition pass does not change the accepted input language. -/
lemma parse_acceptance_iff_raw_acceptance (input : String) :
    (∃ docs, TokenParser.parseYaml input = .ok docs) ↔
    (∃ rawDocs, TokenParser.parseYamlRaw input = .ok rawDocs) := by
  constructor
  · rintro ⟨docs, h⟩
    unfold TokenParser.parseYaml at h
    split at h
    · rename_i rawDocs hraw
      exact ⟨rawDocs, hraw⟩
    · contradiction
  · rintro ⟨rawDocs, hraw⟩
    exact ⟨rawDocs.map YamlDocument.compose,
      L4YAML.Proofs.Composition.parseYaml_of_parseYamlRaw_ok input rawDocs hraw⟩

/-- Full load acceptance is exactly scanner-plus-token-parser acceptance. -/
lemma parse_iff_executable_language (input : String) :
    (∃ docs, TokenParser.parseYaml input = .ok docs) ↔
      InExecutableLanguage input := by
  constructor
  · rintro ⟨docs, h⟩
    unfold TokenParser.parseYaml at h
    split at h
    · rename_i rawDocs hraw
      obtain ⟨tokens, hscan, hparse⟩ :=
        L4YAML.Proofs.Composition.parseYamlRaw_ok_decompose input rawDocs hraw
      exact ⟨tokens, rawDocs, hscan, hparse⟩
    · contradiction
  · rintro ⟨tokens, rawDocs, hscan, hparse⟩
    exact ⟨rawDocs.map YamlDocument.compose,
      L4YAML.Proofs.Composition.parseYaml_pipeline
        input tokens rawDocs hscan hparse⟩

/-- Executable acceptance implies scanner acceptance. -/
lemma executable_implies_scanner (input : String) :
    InExecutableLanguage input → InScannerLanguage input := by
  rintro ⟨tokens, rawDocs, hscan, hparse⟩
  exact ⟨tokens, hscan⟩

end L4YAML.Proofs.Serialization

#print axioms L4YAML.Proofs.Serialization.parse_iff_executable_language
