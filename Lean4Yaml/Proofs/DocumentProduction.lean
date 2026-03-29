import Lean4Yaml.Proofs.ScanStrictCoupling
import Lean4Yaml.Proofs.StructureProduction
import Lean4Yaml.Proofs.Composition

/-! # Document & Stream Production (Phase D of v0.4.4)

    Compose phases A–C into document/stream-level surface syntax:
    - Stream construction helpers (SLYamlStream, SLDocumentPrefix, etc.)
    - `scan_strict`: scan success → InYamlLanguage
    - `parse_strict`: parse success → InYamlLanguage

    ## Architecture

    Phase A proved `scan_full_consumption`: scan success → all input
    characters consumed (∃ sp_final, sp_final.chars = []).

    Phase D bridges this to `InYamlLanguage` by constructing an
    `SLYamlStream` derivation tree from the consumed characters.

    The key remaining gap is constructing `SBlockNode` for document
    content regions — this requires production coupling for ALL content
    types (plain, single-quoted, block scalars, flow/block collections).
    Only double-quoted scalars have production coupling (Phase B).
    The gap is isolated in a single helper theorem `scan_content_gives_stream`.
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.DocumentProduction

open Lean4Yaml.Surface
open Lean4Yaml.Scanner
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScanStrictCoupling

/-! ## §1 Trivial Stream Constructions -/

/-- The empty string is a valid YAML stream. -/
theorem empty_yaml_stream :
    SLYamlStream ⟨[], 0⟩ ⟨[], 0⟩ :=
  SLYamlStream.single ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩ ⟨[], 0⟩
    (GStar.nil _) (GOpt.none _) (GStar.nil _)

/-- The empty string is in the YAML language. -/
theorem empty_InYamlLanguage : InYamlLanguage "" :=
  ⟨⟨[], 0⟩, empty_yaml_stream, rfl⟩

/-! ## §2 Document Prefix Helpers -/

/-- A zero-width document prefix (no BOM, no comments). -/
theorem trivial_prefix (sp : SurfPos) :
    SLDocumentPrefix sp sp :=
  SLDocumentPrefix.comments sp sp (GStar.nil _)

/-- BOM produces a document prefix.
    '\uFEFF' at any column advances by 1, then no comments. -/
theorem bom_gives_prefix (rest : List Char) (col : Nat) :
    SLDocumentPrefix ⟨'\uFEFF' :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SLDocumentPrefix.bom rest col ⟨rest, col + 1⟩ (GStar.nil _)

/-! ## §3 Document Suffix Helpers -/

/-- `SCDocumentEnd` + `SSLComments` → `SLDocumentSuffix`. -/
theorem doc_end_comments_give_suffix (sp sp₁ sp' : SurfPos)
    (h_end : SCDocumentEnd sp sp₁)
    (h_comments : SSLComments sp₁ sp') :
    SLDocumentSuffix sp sp' :=
  SLDocumentSuffix.mk sp sp₁ sp' h_end h_comments

/-- Document end with break: '...' + newline → suffix. -/
theorem doc_end_break_suffix (rest : List Char) (sp_trail : SurfPos)
    (h_break : SBBreak ⟨rest, 3⟩ sp_trail) :
    SLDocumentSuffix ⟨'.' :: '.' :: '.' :: rest, 0⟩ sp_trail :=
  SLDocumentSuffix.mk _ ⟨rest, 3⟩ sp_trail
    (SCDocumentEnd.mk rest)
    (SSLComments.withComment ⟨rest, 3⟩ sp_trail sp_trail
      (SSBComment.noSep _ _ (SBComment.break _ _ h_break))
      (GStar.nil _))

/-- Document end at EOF: '...' at input end → suffix. -/
theorem doc_end_eof_suffix :
    SLDocumentSuffix ⟨['.', '.', '.'], 0⟩ ⟨[], 3⟩ :=
  SLDocumentSuffix.mk _ ⟨[], 3⟩ ⟨[], 3⟩
    (SCDocumentEnd.mk [])
    (SSLComments.withComment ⟨[], 3⟩ ⟨[], 3⟩ ⟨[], 3⟩
      (SSBComment.noSep _ _ (SBComment.eof _))
      (GStar.nil _))

/-! ## §4 SSLComments Helpers -/

/-- At column 0 with no content, SSLComments is trivially satisfied. -/
theorem start_of_line_comments (rest : List Char) :
    SSLComments ⟨rest, 0⟩ ⟨rest, 0⟩ :=
  SSLComments.startOfLine rest ⟨rest, 0⟩ (GStar.nil _)

/-- EOF gives SSLComments. -/
theorem eof_comments (col : Nat) :
    SSLComments ⟨[], col⟩ ⟨[], col⟩ :=
  SSLComments.withComment ⟨[], col⟩ ⟨[], col⟩ ⟨[], col⟩
    (SSBComment.noSep _ _ (SBComment.eof _))
    (GStar.nil _)

/-- Newline gives SSLComments. -/
theorem break_gives_comments (sp sp' : SurfPos) (h : SBBreak sp sp') :
    SSLComments sp sp' :=
  SSLComments.withComment sp sp' sp'
    (SSBComment.noSep sp sp' (SBComment.break sp sp' h))
    (GStar.nil _)

/-! ## §5 Explicit Document Helpers -/

/-- '---' followed by SSLComments gives an explicit document. -/
theorem directives_end_comments_give_explicit (sp sp₁ sp' : SurfPos)
    (h_end : SCDirectivesEnd sp sp₁)
    (h_comments : SSLComments sp₁ sp') :
    SLExplicitDocument sp sp' :=
  SLExplicitDocument.withContent sp sp₁ sp' h_end
    (GAlt.right sp₁ sp' (GSeq.mk sp₁ sp₁ sp' (GEps.mk sp₁) h_comments))

/-! ## §6 Stream Composition from Scanner -/

-- The core gap: building SLYamlStream from scanner success.
--
-- Phase A proves that scan success → all input characters consumed
-- (scan_full_consumption: ∃ sp_final, sp_final.chars = []).
--
-- To construct InYamlLanguage, we need SLYamlStream ⟨input.toList, 0⟩ sp_final.
-- This requires building the full grammar derivation tree, including:
-- - SLDocumentPrefix for BOM + leading comments
-- - SLAnyDocument for each document's content (SBlockNode, flow nodes, scalars)
-- - SLDocumentSuffix for '...' markers
--
-- The document content (SBlockNode) requires production coupling for ALL
-- content types: plain scalars, single-quoted, block literal/folded,
-- flow sequences/mappings, block sequences/mappings, etc.
-- Currently only double-quoted scalars have production coupling (Phase B).
--
-- This is the sole remaining sorry in the acceptance strictness chain.
-- Eliminating it requires extending Phase B's approach to all content types.
theorem scan_content_gives_stream
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens)
    (sp_final : SurfPos)
    (h_empty : sp_final.chars = []) :
    SLYamlStream ⟨input.toList, 0⟩ sp_final := by
  sorry

/-- **Scanner strictness**: if the scanner successfully processes a string,
    the input belongs to the formal YAML 1.2.2 surface syntax.

    Proof composes Phase A (full consumption) with Phase D (stream construction).
    The stream construction has 1 sorry for SBlockNode content production. -/
theorem scan_strict_proof
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    InYamlLanguage input := by
  obtain ⟨sp_final, h_empty⟩ := scan_full_consumption input tokens h
  exact ⟨sp_final, scan_content_gives_stream input tokens h sp_final h_empty, h_empty⟩

/-! ## §7 Parse Strictness from Scan Strictness -/

/-- **Parser strictness**: if the parser successfully parses a string,
    the input belongs to the formal YAML 1.2.2 surface syntax.

    Proof: parseYaml calls scanFiltered which calls scan. If parseYaml
    succeeds, scan must have succeeded, so scan_strict applies.

    Uses `Composition.parseYamlRaw_ok_decompose` to extract the scan
    step from the pipeline. -/
theorem parse_strict_proof
    (input : String)
    (docs : Array Lean4Yaml.YamlDocument)
    (h : Lean4Yaml.TokenParser.parseYaml input = Except.ok docs) :
    InYamlLanguage input := by
  -- parseYaml = compose ∘ parseYamlRaw
  unfold Lean4Yaml.TokenParser.parseYaml at h
  split at h
  · rename_i rawDocs h_raw
    -- parseYamlRaw .ok → ∃ tokens, scanFiltered .ok ∧ parseStream .ok
    obtain ⟨tokens, h_sf, _⟩ :=
      Lean4Yaml.Proofs.Composition.parseYamlRaw_ok_decompose input rawDocs h_raw
    -- scanFiltered .ok → scan .ok
    unfold Scanner.scanFiltered at h_sf
    split at h_sf
    · rename_i raw_tokens h_scan
      exact scan_strict_proof input raw_tokens h_scan
    · contradiction
  · contradiction

end Lean4Yaml.Proofs.DocumentProduction
