/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Surface.Node
import Lean4Yaml.CharPredicates

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

namespace Lean4Yaml.Surface

open Lean4Yaml (YamlContext)
open Lean4Yaml.CharPredicates

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
    We use indent = 0 since Nat can't represent -1; the spec's n=-1
    means the first block content determines its indent. -/
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
  /-- Implicit continuation: previous stream + prefix(es) + explicit document. -/
  | implicitContinue (s s₁ s₂ s₃ s' : SurfPos) :
      SLYamlStream s s₁ →
      GStar SLDocumentPrefix s₁ s₂ →
      GOpt SLExplicitDocument s₂ s₃ →
      GStar SLDocumentSuffix s₃ s' →
      SLYamlStream s s'

end Lean4Yaml.Surface
