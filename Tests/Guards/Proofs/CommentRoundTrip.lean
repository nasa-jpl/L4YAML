import Lean4Yaml.Proofs.CommentRoundTrip

namespace Lean4Yaml.Tests.Guards.CommentRoundTrip

open Lean4Yaml
open Lean4Yaml.Emit
open Lean4Yaml.TokenParser

/-- Helper: check that a document's comment texts survive the round-trip
    through emitWithComments → parseYamlWithComments. -/
private def commentRoundTrips (doc : YamlDocument) : Bool :=
  match parseYamlWithComments (emitWithComments doc) with
  | .ok docs =>
    if h : docs.size = 1 then
      let doc' := docs[0]'(by omega)
      doc.commentTexts == doc'.commentTexts
    else false
  | .error _ => false

/-- Helper: check that a document's value content survives the round-trip
    through emitWithComments → parseYamlWithComments. -/
private def valueRoundTrips (doc : YamlDocument) : Bool :=
  match parseYamlWithComments (emitWithComments doc) with
  | .ok docs =>
    if h : docs.size = 1 then
      let doc' := docs[0]'(by omega)
      contentEq doc.value doc'.value
    else false
  | .error _ => false

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

end Lean4Yaml.Tests.Guards.CommentRoundTrip
