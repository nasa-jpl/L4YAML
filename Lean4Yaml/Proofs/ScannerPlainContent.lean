/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.CharPredicates

/-!
# Plain Scalar Content Invariant (B3.2)

Defines `PlainContentInv`, the loop invariant for
`collectPlainScalarLoop` content correctness. This invariant tracks
that the accumulated `content` string satisfies the content predicates
required by `ScalarScannable`, and that `spaces` contains only
whitespace characters.

The boundary condition `boundary_colon` ensures that `noColonSpace` is
preserved when spaces are flushed into content: if content ends with
`:`, spaces must be empty (the scanner always appends a non-whitespace
char immediately after a non-terminating `:`).
-/

namespace Lean4Yaml.Proofs.ScannerPlainContent

open Lean4Yaml.CharPredicates

/-- Loop invariant for `collectPlainScalarLoop` content correctness. -/
structure PlainContentInv (content : String) (spaces : String)
    (inFlow : Bool) : Prop where
  /-- Content has no `: ` (colon-space) pattern. -/
  content_noColonSpace : noColonSpaceProp content
  /-- Content has no ` #` (space-hash) pattern. -/
  content_noSpaceHash : noSpaceHashProp content
  /-- In flow context, content has no flow indicators. -/
  content_noFlowIndicators : inFlow = true → noFlowIndicatorsProp content
  /-- Spaces buffer contains only whitespace characters. -/
  spaces_whitespace : ∀ c ∈ spaces.toList, isWhiteSpaceProp c
  /-- Boundary safety: if content ends with ':', spaces must be empty.
      This prevents `: ` at the content–spaces boundary during flush. -/
  boundary_colon : content.toList.getLast? = some ':' → spaces = ""

/-- The invariant holds trivially for empty content and empty spaces. -/
theorem PlainContentInv.empty (inFlow : Bool) :
    PlainContentInv "" "" inFlow where
  content_noColonSpace := noColonSpaceProp_empty
  content_noSpaceHash := noSpaceHashProp_empty
  content_noFlowIndicators := fun _ => noFlowIndicatorsProp_empty
  spaces_whitespace := fun _ hc => by simp [String.toList] at hc
  boundary_colon := fun h => by simp [String.toList, List.getLast?] at h

end Lean4Yaml.Proofs.ScannerPlainContent
