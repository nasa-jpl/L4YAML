import L4YAML.Proofs.Scanner.ScanStrictCoupling
import L4YAML.Proofs.Production.StructureProduction
import L4YAML.Proofs.Production.NodeProduction
import L4YAML.Proofs.Composition
import L4YAML.Proofs.Production.StreamAccum

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

namespace L4YAML.Proofs.DocumentProduction

open L4YAML.Surface
open L4YAML.Scanner
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ScanStrictCoupling
open L4YAML.Proofs.StreamAccum

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

/-! ## §6 Stream Composition from Scanner (Layer 3) -/

-- Layer 3 architecture: decompose scanner success into SLYamlStream.
--
-- The scanner processes input in a loop:
--   scanNextToken_preprocess → skip whitespace/comments → (s', c) or EOF
--   dispatch c → structural (---/...) | flow ([]{}:) | block (-?:) | content
--
-- Each category maps to a grammar element:
--   whitespace/comments  → SLDocumentPrefix.comments | SSLComments
--   '---'                → SCDirectivesEnd → SLExplicitDocument
--   '...'                → SCDocumentEnd → SLDocumentSuffix
--   content tokens       → SBlockNode (via Layer 1/2 _prod theorems)
--
-- The stream is built by composing these pieces into SLYamlStream
-- constructors (single | suffixContinue | implicitContinue).

/-! ### §6a Stream Extension Lemmas -/

-- One bare document forms a stream (no prefix, no suffix).
theorem bare_to_stream (s s' : SurfPos)
    (h_bare : SLBareDocument s s') :
    SLYamlStream s s' :=
  SLYamlStream.single s s s' s'
    (GStar.nil _)
    (GOpt.some _ _ (SLAnyDocument.bare s s' h_bare))
    (GStar.nil _)

-- Empty document at any position forms a stream.
-- Used when all content has been consumed by prefixes/suffixes.
theorem empty_to_stream (sp : SurfPos) :
    SLYamlStream sp sp :=
  SLYamlStream.single sp sp sp sp
    (GStar.nil _)
    (GOpt.none _)
    (GStar.nil _)

-- Extend a stream with suffix(es) (after '...').
theorem stream_append_suffix (s s₁ s₂ : SurfPos)
    (h_stream : SLYamlStream s s₁)
    (h_suffixes : GPlus SLDocumentSuffix s₁ s₂) :
    SLYamlStream s s₂ :=
  SLYamlStream.suffixContinue s s₁ s₂ s₂ s₂ s₂
    h_stream h_suffixes
    (GStar.nil _) (GOpt.none _) (GStar.nil _)

-- Extend a stream with an implicit continuation (after prefix(es) + explicit doc).
theorem stream_implicit_continue (s s₁ s₂ s₃ : SurfPos)
    (h_stream : SLYamlStream s s₁)
    (h_prefixes : GStar SLDocumentPrefix s₁ s₂)
    (h_doc : SLExplicitDocument s₂ s₃) :
    SLYamlStream s s₃ :=
  SLYamlStream.implicitContinue s s₁ s₂ s₃ s₃
    h_stream h_prefixes
    (GOpt.some _ _ (SLAnyDocument.explicit _ _ h_doc))
    (GStar.nil _)

/-! ### §6b Content Production Gap -/

-- The precise gap: given that the scanner consumed all characters from
-- sp to sp_final (where sp_final.chars = []), prove that the character
-- sequence forms a valid SLYamlStream.
--
-- This requires per-content-type production coupling for ALL scanner
-- content dispatch branches:
--
-- | Content type     | Scanner function      | _prod theorem          | Status      |
-- |------------------|-----------------------|------------------------|-------------|
-- | Double-quoted    | scanDoubleQuoted      | scanDoubleQuoted_prod  | ✅ Done     |
-- | Single-quoted    | scanSingleQuoted      | scanSingleQuoted_prod  | ✅ Done     |
-- | Plain scalar     | scanPlainScalar       | scanPlainScalar_prod   | ❌ Missing  |
-- | Block scalar     | scanBlockScalar       | scanBlockScalar_prod   | ❌ Missing  |
-- | Anchor           | scanAnchorOrAlias     | alias_to_flowNode      | ❌ Partial  |
-- | Tag              | scanTag               | scanTag_prod (→ props) | ✅ Done     |
-- | Flow sequence    | (via scanNextToken)   | —                      | ❌ Missing  |
-- | Flow mapping     | (via scanNextToken)   | —                      | ❌ Missing  |
-- | Block sequence   | (multi-token)         | —                      | ❌ Missing  |
-- | Block mapping    | (multi-token)         | —                      | ❌ Missing  |
--
-- Additionally, the stream-level composition requires:
-- (1) Preprocessing characters → SLDocumentPrefix / SSLComments
-- (2) Document marker dispatch → SCDirectivesEnd / SCDocumentEnd
-- (3) Block collection accumulation across multiple scanNextToken calls
--
-- The sorry below captures this entire gap. When all _prod theorems
-- are completed and the loop accumulator is implemented, this sorry
-- is replaced by the composition proof.
--
-- Architecture for eventually eliminating the sorry:
--   scanLoop_grammar_prod : fuel induction threading (ScannerSurfCorr × StreamAccum)
--   StreamAccum : inductive tracking partial SLYamlStream + open document + open block
--   scanNextToken_stream_step : extends StreamAccum for one token
--   finalize_stream : StreamAccum at EOF → SLYamlStream

theorem scan_strict_proof
    (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : scan input = .ok tokens) :
    InYamlLanguage input := by
  obtain ⟨sp_final, h_stream, h_empty⟩ := scan_content_gives_stream_v2 input tokens h
  exact ⟨sp_final, h_stream, h_empty⟩

/-! ## §7 Parse Strictness from Scan Strictness -/

/-- **Parser strictness**: if the parser successfully parses a string,
    the input belongs to the formal YAML 1.2.2 surface syntax.

    Proof: parseYaml calls scanFiltered which calls scan. If parseYaml
    succeeds, scan must have succeeded, so scan_strict applies.

    **Initiative 3 / J.2 step 5 cutover** (Category C): post-cutover
    `scanFiltered` no longer matches on `scan input`; it threads through
    `scanLoopFull` and `linearise`.  The bridge from "scanFiltered .ok"
    back to "scan .ok" needs a small bridging lemma
    (`scanFiltered_ok_implies_scan_ok`) — straightforward but new.
    J.3 manifest 5.d. -/
theorem parse_strict_proof
    (input : String)
    (docs : Array L4YAML.YamlDocument)
    (h : L4YAML.TokenParser.parseYaml input = Except.ok docs) :
    InYamlLanguage input := by
  -- J.3 manifest 5.d: bridge scanFiltered.ok → scan.ok against linearise.
  sorry

end L4YAML.Proofs.DocumentProduction
