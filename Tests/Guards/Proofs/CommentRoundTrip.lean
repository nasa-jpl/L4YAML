import Lean4Yaml.Emitter
import Lean4Yaml.TokenParser
import Lean4Yaml.Dump

/-!
# Comment Round-Trip Guards (Phase G6)

Compile-time `#guard` checks for the comment-aware emitter,
comment classification, comment-aware dump, and the
`parseYamlWithComments` pipeline.

Corresponds to `Lean4Yaml.Proofs.CommentProperties` (algebraic proofs).
-/

namespace Lean4Yaml.Tests.Guards.CommentRoundTrip

open Lean4Yaml
open Lean4Yaml.Emit
open Lean4Yaml.Dump
open Lean4Yaml.TokenParser

/-- Helper: check that a document's comment texts survive the round-trip
    through emitWithComments → parseYamlWithComments. -/
def commentRoundTrips (doc : YamlDocument) : Bool :=
  match parseYamlWithComments (emitWithComments doc) with
  | .ok docs =>
    if h : docs.size = 1 then
      let doc' := docs[0]'(by omega)
      doc.commentTexts == doc'.commentTexts
    else false
  | .error _ => false

/-- Helper: check that a document's value content survives the round-trip
    through emitWithComments → parseYamlWithComments. -/
def valueRoundTrips (doc : YamlDocument) : Bool :=
  match parseYamlWithComments (emitWithComments doc) with
  | .ok docs =>
    if h : docs.size = 1 then
      let doc' := docs[0]'(by omega)
      contentEq doc.value doc'.value
    else false
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §1: Emitter structural properties
-- ═══════════════════════════════════════════════════════════════════

-- emitWithComments on no comments = emit on the value
#guard emitWithComments { value := YamlValue.plainScalar "hello",
                          comments := #[], nodePositions := #[] } ==
       emit (YamlValue.plainScalar "hello")

-- emitWithComments on one comment produces comment line + value
#guard emitWithComments { value := YamlValue.plainScalar "hello",
                          comments := #[(⟨0, 0, 0⟩, ⟨" a comment", .inline⟩)],
                          nodePositions := #[] } ==
       "# a comment\n\"hello\""

-- emitCommentLines on empty comments produces empty string
#guard emitCommentLines #[] == ""

-- emitCommentLines on a single comment produces `#text\n`
#guard emitCommentLines #[(⟨0, 0, 0⟩, ⟨" test", .inline⟩)] == "# test\n"

-- ═══════════════════════════════════════════════════════════════════
-- §2a: Comment text round-trip — scalars with comments
-- ═══════════════════════════════════════════════════════════════════

-- Single comment with plain scalar
#guard commentRoundTrips { value := .plainScalar "hello",
                           comments := #[(⟨0, 0, 0⟩, ⟨" inline", .inline⟩)],
                           nodePositions := #[] }

-- Single comment with empty string scalar
#guard commentRoundTrips { value := .plainScalar "",
                           comments := #[(⟨0, 0, 0⟩, ⟨" note", .inline⟩)],
                           nodePositions := #[] }

-- Comment with special characters in text
#guard commentRoundTrips { value := .plainScalar "val",
                           comments := #[(⟨0, 0, 0⟩, ⟨" has : colon", .inline⟩)],
                           nodePositions := #[] }

-- Two comments
#guard commentRoundTrips { value := .plainScalar "x",
                           comments := #[(⟨0, 0, 0⟩, ⟨" first", .inline⟩),
                                         (⟨1, 0, 10⟩, ⟨" second", .inline⟩)],
                           nodePositions := #[] }

-- Three comments
#guard commentRoundTrips { value := .plainScalar "y",
                           comments := #[(⟨0, 0, 0⟩, ⟨" a", .inline⟩),
                                         (⟨1, 0, 5⟩, ⟨" b", .inline⟩),
                                         (⟨2, 0, 10⟩, ⟨" c", .inline⟩)],
                           nodePositions := #[] }

-- ═══════════════════════════════════════════════════════════════════
-- §2b: Value round-trip — value preserved through comment emission
-- ═══════════════════════════════════════════════════════════════════

-- Plain scalar
#guard valueRoundTrips { value := .plainScalar "hello",
                         comments := #[(⟨0, 0, 0⟩, ⟨" note", .inline⟩)],
                         nodePositions := #[] }

-- Empty string
#guard valueRoundTrips { value := .plainScalar "",
                         comments := #[(⟨0, 0, 0⟩, ⟨" note", .inline⟩)],
                         nodePositions := #[] }

-- Empty flow sequence
#guard valueRoundTrips { value := .sequence .flow #[] none,
                         comments := #[(⟨0, 0, 0⟩, ⟨" seq", .inline⟩)],
                         nodePositions := #[] }

-- Empty flow mapping
#guard valueRoundTrips { value := .mapping .flow #[] none,
                         comments := #[(⟨0, 0, 0⟩, ⟨" map", .inline⟩)],
                         nodePositions := #[] }

-- No comments — value still round-trips
#guard valueRoundTrips { value := .plainScalar "no comments",
                         comments := #[],
                         nodePositions := #[] }

-- ═══════════════════════════════════════════════════════════════════
-- §2c: No-comment round-trip — document without comments
-- ═══════════════════════════════════════════════════════════════════

#guard commentRoundTrips { value := .plainScalar "bare",
                           comments := #[],
                           nodePositions := #[] }

-- ═══════════════════════════════════════════════════════════════════
-- §3: Comment position classification (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

-- Same line as a node → .inline
#guard classifyCommentPosition ⟨10, 1, 5⟩
    #[(#[], ⟨0, 1, 0⟩, ⟨20, 5, 0⟩)] == .inline

-- Before any node → .before
#guard classifyCommentPosition ⟨0, 0, 0⟩
    #[(#[], ⟨5, 1, 0⟩, ⟨20, 5, 0⟩)] == .before

-- After all nodes → .after
#guard classifyCommentPosition ⟨25, 6, 0⟩
    #[(#[], ⟨5, 1, 0⟩, ⟨20, 5, 0⟩)] == .after

-- No node positions → .after (fallback)
#guard classifyCommentPosition ⟨5, 1, 0⟩ #[] == .after

-- Multiple nodes, comment on a node line → .inline
#guard classifyCommentPosition ⟨15, 3, 10⟩
    #[(#[.index 0], ⟨5, 1, 0⟩, ⟨10, 2, 0⟩),
      (#[.index 1], ⟨12, 3, 0⟩, ⟨20, 4, 0⟩)] == .inline

-- Multiple nodes, comment between them → .before (next node exists on later line)
#guard classifyCommentPosition ⟨11, 2, 5⟩
    #[(#[.index 0], ⟨5, 1, 0⟩, ⟨10, 1, 5⟩),
      (#[.index 1], ⟨15, 3, 0⟩, ⟨20, 4, 0⟩)] == .before

-- ═══════════════════════════════════════════════════════════════════
-- §4: classifyDocumentComments end-to-end (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

-- Before comment gets reclassified from .inline to .before
#guard
  let doc : YamlDocument := {
    value := .plainScalar "hello",
    comments := #[(⟨0, 0, 0⟩, ⟨" top comment", .inline⟩)],
    nodePositions := #[(#[], ⟨5, 1, 0⟩, ⟨10, 1, 5⟩)]
  }
  let classified := classifyDocumentComments doc
  classified.comments[0]!.2.position == .before

-- Inline comment stays .inline
#guard
  let doc : YamlDocument := {
    value := .plainScalar "hello",
    comments := #[(⟨6, 1, 6⟩, ⟨" inline note", .inline⟩)],
    nodePositions := #[(#[], ⟨5, 1, 0⟩, ⟨10, 1, 5⟩)]
  }
  let classified := classifyDocumentComments doc
  classified.comments[0]!.2.position == .inline

-- After comment gets reclassified from .inline to .after
#guard
  let doc : YamlDocument := {
    value := .plainScalar "hello",
    comments := #[(⟨15, 3, 0⟩, ⟨" trailing", .inline⟩)],
    nodePositions := #[(#[], ⟨5, 1, 0⟩, ⟨10, 1, 5⟩)]
  }
  let classified := classifyDocumentComments doc
  classified.comments[0]!.2.position == .after

-- ═══════════════════════════════════════════════════════════════════
-- §5: Comment-aware dump (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

open Lean4Yaml.Dump in
-- No comments → same as dumpDocument
#guard dumpDocumentWithComments { value := .plainScalar "hello" } ==
       dumpDocument { value := .plainScalar "hello" }

open Lean4Yaml.Dump in
-- Before comment → emitted before value
#guard dumpDocumentWithComments
  { value := .plainScalar "hello",
    comments := #[(⟨0, 0, 0⟩, ⟨" header", .before⟩)] } ==
  "# header\nhello"

open Lean4Yaml.Dump in
-- After comment → emitted after value
#guard dumpDocumentWithComments
  { value := .plainScalar "hello",
    comments := #[(⟨20, 5, 0⟩, ⟨" footer", .after⟩)] } ==
  "hello\n# footer\n"

open Lean4Yaml.Dump in
-- Inline comment → appended to first line
#guard dumpDocumentWithComments
  { value := .plainScalar "hello",
    comments := #[(⟨5, 1, 5⟩, ⟨" note", .inline⟩)] } ==
  "hello # note"

open Lean4Yaml.Dump in
-- Mixed: before + inline + after
#guard dumpDocumentWithComments
  { value := .plainScalar "hello",
    comments := #[(⟨0, 0, 0⟩, ⟨" top", .before⟩),
                  (⟨5, 1, 5⟩, ⟨" mid", .inline⟩),
                  (⟨20, 5, 0⟩, ⟨" end", .after⟩)] } ==
  "# top\nhello # mid\n# end\n"

-- ═══════════════════════════════════════════════════════════════════
-- §6: parseYamlWithComments produces classified comments (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

-- Single-document: comments are classified
#guard
  match parseYamlWithComments "# top comment\nhello # inline\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 2 &&
    docs[0]!.commentTexts == #[" top comment", " inline"]
  | .error _ => false

-- No comments → empty comments array
#guard
  match parseYamlWithComments "hello\n" with
  | .ok docs => docs.size == 1 && docs[0]!.comments.isEmpty
  | .error _ => false

-- Comment text preserved through parse
#guard
  match parseYamlWithComments "key: value # note\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.commentTexts == #[" note"]
  | .error _ => false

-- Block mapping with comments
#guard
  match parseYamlWithComments "# header\na: 1 # inline\nb: 2\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 2 &&
    docs[0]!.commentTexts == #[" header", " inline"]
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §7: YAML 1.2.2 §6.6 spec example validation (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

-- §6.6 "Comments are a presentation detail"
-- Example: comment after value on same line
#guard
  match parseYamlWithComments "key: value # This is a comment\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 1 &&
    docs[0]!.commentTexts == #[" This is a comment"]
  | .error _ => false

-- Standalone comment line (like spec Example 6.9)
#guard
  match parseYamlWithComments "# Comment\nkey: value\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 1 &&
    docs[0]!.commentTexts == #[" Comment"]
  | .error _ => false

-- Multiple standalone comments
#guard
  match parseYamlWithComments "# First\n# Second\nkey: value\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 2 &&
    docs[0]!.commentTexts == #[" First", " Second"]
  | .error _ => false

-- Comment after key indicator (§6.9 pattern)
#guard
  match parseYamlWithComments "key: # Empty value with comment\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 1 &&
    docs[0]!.commentTexts == #[" Empty value with comment"]
  | .error _ => false

-- Statistics-style block mapping with inline comments (§6.12 pattern)
#guard
  match parseYamlWithComments "hr: 65 # Home runs\navg: 0.278 # Batting average\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 2 &&
    docs[0]!.commentTexts == #[" Home runs", " Batting average"]
  | .error _ => false

-- Flow sequence with trailing comment
#guard
  match parseYamlWithComments "[a, b, c] # items\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 1 &&
    docs[0]!.commentTexts == #[" items"]
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §8: Comment classification end-to-end (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

-- Top comment before content is classified .before
#guard
  match parseYamlWithComments "# Top\nhello\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 1 &&
    docs[0]!.comments[0]!.2.position == .before
  | .error _ => false

-- Inline comment on same line as value is classified .inline
#guard
  match parseYamlWithComments "hello # inline\n" with
  | .ok docs =>
    docs.size == 1 &&
    docs[0]!.comments.size == 1 &&
    docs[0]!.comments[0]!.2.position == .inline
  | .error _ => false

-- ═══════════════════════════════════════════════════════════════════
-- §9: Multi-document comment-aware dump (v0.2.7)
-- ═══════════════════════════════════════════════════════════════════

open Lean4Yaml.Dump in
-- dumpDocumentsWithComments multi-doc includes `---` separator and `...`
#guard
  let doc1 : YamlDocument := { value := .plainScalar "first" }
  let doc2 : YamlDocument := { value := .plainScalar "second" }
  dumpDocumentsWithComments #[doc1, doc2] == "first\n---\nsecond\n..."

end Lean4Yaml.Tests.Guards.CommentRoundTrip
