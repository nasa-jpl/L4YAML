/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Node
import L4YAML.CharPredicates

/-!
# Document & Stream Surface Syntax — Chapter 9

Surface syntax predicates for YAML document boundaries, document markers,
and stream-level composition.

## Productions Covered

- **Document markers**: [200]-[202] c-forbidden, c-directives-end,
  c-document-end
- **Document types**: [203]-[205] l-bare-document, l-explicit-document,
  l-directive-document
- **Stream**: [206]-[211] l-any-document, l-yaml-stream
-/

set_option autoImplicit false

namespace L4YAML.Surface

open L4YAML (YamlContext)
open L4YAML.CharPredicates

/-! ## §1 Document Markers [200]–[202] -/

/-- Helper: the characters after '---' or '...' must be whitespace,
    line break, or end of input. -/
def isMarkerFollower : List Char → Prop
  | [] => True
  | c :: _ => isWhiteSpaceProp c ∨ isLineBreakProp c

/-- [200] c-forbidden: document boundary markers at column 0.
    Matches '---' or '...' at column 0 followed by whitespace/break/eof. -/
inductive SCForbidden : SurfPos → Prop where
  | directivesEnd (rest : List Char)
      (hFollow : isMarkerFollower rest) :
      SCForbidden ⟨'-' :: '-' :: '-' :: rest, 0⟩
  | documentEnd (rest : List Char)
      (hFollow : isMarkerFollower rest) :
      SCForbidden ⟨'.' :: '.' :: '.' :: rest, 0⟩

/-- [201] c-directives-end: the '---' marker.
    Must be at column 0. Consumes 3 characters, advancing to column 3. -/
inductive SCDirectivesEnd : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) :
      SCDirectivesEnd ⟨'-' :: '-' :: '-' :: rest, 0⟩ ⟨rest, 3⟩

/-- [202] c-document-end: the '...' marker.
    Must be at column 0. Consumes 3 characters, advancing to column 3. -/
inductive SCDocumentEnd : SurfPos → SurfPos → Prop where
  | mk (rest : List Char) :
      SCDocumentEnd ⟨'.' :: '.' :: '.' :: rest, 0⟩ ⟨rest, 3⟩

/-! ## §2 Document Types [203]–[205] -/

/-- [203] l-bare-document: document without explicit markers.
    Content is a block node at indent -1 (top level).
    We use indent = 0 since Nat can't represent -1; hence n_lean = n_spec + 1
    throughout (spec's -1 maps to our 0, spec's 0 maps to our 1, etc.).
    SBlockNode constructors use n directly (not n+1) to match this convention. -/
inductive SLBareDocument : SurfPos → SurfPos → Prop where
  | mk (s s' : SurfPos) :
      SBlockNode 0 .blockIn s s' →
      SLBareDocument s s'

/-- [204] l-explicit-document: '---' + content or empty.
    The content starts after the '---' marker. -/
inductive SLExplicitDocument : SurfPos → SurfPos → Prop where
  | withContent (s s₁ s' : SurfPos) :
      SCDirectivesEnd s s₁ →
      GAlt SLBareDocument (GSeq SENode SSLComments) s₁ s' →
      SLExplicitDocument s s'

/-- [205] l-directive-document: directives + '---' + content.
    One or more directives followed by an explicit document. -/
inductive SLDirectiveDocument : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) :
      GPlus SLDirective s s₁ →
      SLExplicitDocument s₁ s' →
      SLDirectiveDocument s s'

/-- [210] l-any-document: any document form. -/
inductive SLAnyDocument : SurfPos → SurfPos → Prop where
  | directive (s s' : SurfPos) :
      SLDirectiveDocument s s' → SLAnyDocument s s'
  | explicit (s s' : SurfPos) :
      SLExplicitDocument s s' → SLAnyDocument s s'
  | bare (s s' : SurfPos) :
      SLBareDocument s s' → SLAnyDocument s s'

/-! ## §3 Stream [206]–[211]

The YAML stream is the top-level grammar production. It represents one
or more documents separated by document markers, with optional leading
and trailing comments/whitespace.

[211] l-yaml-stream ::=
  l-document-prefix* l-any-document?
  ( l-document-suffix+ l-document-prefix* l-any-document?
  | l-document-prefix* l-explicit-document? )* -/

/-- [206] l-document-prefix: optional BOM + l-comment*.
    Simplified: just comments (BOM is a single-character check). -/
inductive SLDocumentPrefix : SurfPos → SurfPos → Prop where
  | comments (s s' : SurfPos) :
      GStar SLComment s s' → SLDocumentPrefix s s'
  | bom (rest : List Char) (col : Nat) (s' : SurfPos) :
      GStar SLComment ⟨rest, col + 1⟩ s' →
      SLDocumentPrefix ⟨'\uFEFF' :: rest, col⟩ s'

/-- [207] l-document-suffix: '...' + s-l-comments. -/
inductive SLDocumentSuffix : SurfPos → SurfPos → Prop where
  | mk (s s₁ s' : SurfPos) :
      SCDocumentEnd s s₁ → SSLComments s₁ s' →
      SLDocumentSuffix s s'

/-- [211] l-yaml-stream: the complete YAML stream.
    One or more documents with prefixes and suffixes.
    This is the top-level surface syntax production. -/
inductive SLYamlStream : SurfPos → SurfPos → Prop where
  /-- Single document (possibly bare, explicit, or directive). -/
  | single (s s₁ s₂ s' : SurfPos) :
      GStar SLDocumentPrefix s s₁ →
      GOpt SLAnyDocument s₁ s₂ →
      GStar SLDocumentSuffix s₂ s' →
      SLYamlStream s s'
  /-- Multiple documents: previous stream + suffix(es) + prefix(es) + next document. -/
  | suffixContinue (s s₁ s₂ s₃ s₄ s' : SurfPos) :
      SLYamlStream s s₁ →
      GPlus SLDocumentSuffix s₁ s₂ →
      GStar SLDocumentPrefix s₂ s₃ →
      GOpt SLAnyDocument s₃ s₄ →
      GStar SLDocumentSuffix s₄ s' →
      SLYamlStream s s'
  /-- Implicit continuation: previous stream + prefix(es) + any document.
      Matches spec [211] `l-document-prefix* l-any-document?` branch.
      This includes bare documents (no `---` marker). -/
  | implicitContinue (s s₁ s₂ s₃ s' : SurfPos) :
      SLYamlStream s s₁ →
      GStar SLDocumentPrefix s₁ s₂ →
      GOpt SLAnyDocument s₂ s₃ →
      GStar SLDocumentSuffix s₃ s' →
      SLYamlStream s s'
  /-- Directive absorption: previous stream + orphaned directives.
      Accommodates lenient scanners that process `%YAML`/`%TAG` directives
      without a following `c-directives-end` (`---`). The directives are
      absorbed into the stream without forming a document.
      This is a grammar over-approximation not in the YAML spec. -/
  | directiveDrop (s s₁ s' : SurfPos) :
      SLYamlStream s s₁ →
      GPlus SLDirective s₁ s' →
      SLYamlStream s s'
  /-- Scanner content absorption: previous stream + opaque scanned content
      + trailing SSLComments. When the scanner processes flow indicators
      (`[`, `{`, `]`, `}`, `,`) or block indicators (`-`, `?`, `:`) that
      don't correspond to a complete grammar production at closing time, the
      stream absorbs the gap. The SSLComments evidence anchors the endpoint.
      Grammar over-approximation — the gap s₁→s₂ is opaque. -/
  | scannerDrop (s s₁ s₂ s' : SurfPos) :
      SLYamlStream s s₁ →
      SSLComments s₂ s' →
      SLYamlStream s s'

/-! ## Top-Level Predicate -/

/-- A string is a valid YAML stream according to the surface syntax grammar.

    This is the input-level specification: the string's characters conform
    to the YAML 1.2.2 productions [1]–[211], consuming the entire input. -/
def InYamlLanguage (s : String) : Prop :=
  ∃ s' : SurfPos,
    SLYamlStream ⟨s.toList, 0⟩ s' ∧ s'.chars = []

/-- The indent consumed by the scanner corresponds to `SIndent n` in
    the surface syntax. This is the simplest coupling theorem and
    serves as a template for more complex ones. -/
theorem indent_coupling (n : Nat) (cs : List Char) (col : Nat) :
    cs.take n = List.replicate n ' ' →
    cs.length ≥ n →
    SIndent n ⟨cs, col⟩ ⟨cs.drop n, col + n⟩ := by
  induction n generalizing cs col with
  | zero => intros; exact SIndent.zero _
  | succ k ih =>
    intro hrep hlen
    match cs, hlen with
    | c :: rest, hlen =>
      simp [List.replicate_succ] at hrep
      obtain ⟨hc, hrest_rep⟩ := hrep
      subst hc
      have hlen' : rest.length ≥ k := by simp at hlen; omega
      have ih_result := ih rest (col + 1) hrest_rep hlen'
      have hcol : col + 1 + k = col + (k + 1) := by omega
      rw [hcol] at ih_result
      exact SIndent.succ k rest col _ ih_result

end L4YAML.Surface
