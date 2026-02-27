import Parser
import Lean4Yaml.Stream
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Document
import Lean4Yaml.Proofs.ParserSpecs
import Lean4Yaml.Proofs.PerParserSpecs
import Lean4Yaml.Proofs.Completeness
import Lean4Yaml.Proofs.FuelSufficiency

/-!
# Composition Theorems  (Step 5.4.5)

This module composes the per-parser specifications (§5.4.3), fuel
sufficiency lemmas (§5.4.2), and the `parseYaml ↔ yamlStream` bridge
(§5.4.1) into intermediate lemmas needed for the top-level completeness
theorem.

## Architecture

The composition proceeds in layers:

1. **Position algebra** (§1): `setPosition`/`getPosition` laws for
   YamlStream — idempotence, get-set, and `next?`-based restoration.
   These underpin position-restoration proofs through multiple
   backtracking layers (`eoption`, `optionM`, `notFollowedBy`).

2. **skipBOM specification** (§2): The BOM-skipping combinator is
   identity when the first character is not a BOM.

3. **parseYaml bridge** (§3): Convenience form of `parseYaml_ok_iff`
   for the forward direction (yamlStream success → parseYaml success).

4. **Fuel wrapper unfolding** (§4): Each high-level parser (`blockValue`,
   `dispatchByChar`, etc.) computes `fuel := 4 * remaining + 4` and
   delegates to its `*Impl` variant.  These lemmas expose the `*Impl`
   call with concrete fuel, connecting the per-parser specs (which
   reason about `*Impl` with fuel) to the top-level wrappers.

5. **Combinator extensions** (§5): Specifications for `endOfInput` and
   `Parser.test` on YamlStream — both the success and failure cases.
   The `test` proofs navigate the `optionM → eoption → Sum.inl/inr`
   chain using `rfl` for beta-iota reduction on concrete Sum constructors.

6. **Stream accessor specifications** (§6): `resetAnchorMap`,
   `getValidationError`, `setValidationError` — used in `document` to
   manage parser state between document parses.

## Key Technical Patterns

- **`*>` decomposition**: `a *> b` desugars through `SeqRight.seqRight`,
  which requires `show (a >>= fun _ => b) s = _` before `bind_eq` applies.

- **Sum match in `optionM`**: The `optionM` chain (`eoption >>= fun |
  .inl x => return x | .inr _ => default`) generates a match auxiliary
  that `simp` cannot reduce.  The fix: prove the `eoption` result as
  a `have`, substitute via `simp only [bind_eq, h]`, then close with
  `rfl` (which handles the beta-iota reduction on concrete `Sum.inl`
  / `Sum.inr` constructors plus `Id` monad lifting).

- **Position algebra**: Multiple layers of `eoption`/`notFollowedBy`
  nest `setPosition` calls.  The `next_setPosition_id` lemma (proved
  via `anyToken_setPosition_roundtrip`) and `setPosition_getPosition_id`
  collapse these chains back to the original stream.
-/

namespace Lean4Yaml.Proofs.Composition

open Parser Lean4Yaml Lean4Yaml.Parse Lean4Yaml.Grammar
open Lean4Yaml.Proofs.ParserSpecs
open Lean4Yaml.Proofs.PerParserSpecs
open Lean4Yaml.Proofs.Completeness
open Lean4Yaml.Proofs.FuelSufficiency

/-! ## §1  Stream Position Algebra

These lemmas capture the algebraic laws of `setPosition`/`getPosition`
for `YamlStream`, enabling composition proofs to simplify position
restoration through multiple parser layers.
-/

/-- `setPosition s (getPosition s) = s` for YamlStream.
    Position roundtrip is the identity when no token was consumed. -/
theorem setPosition_getPosition_id (s : YamlStream) :
    Parser.Stream.setPosition s (Parser.Stream.getPosition s) = s := by
  simp only [Parser.Stream.setPosition, Parser.Stream.getPosition, YamlStream.getPos]

/-- `setPosition` is idempotent on position: the first `setPosition` is absorbed.
    Because `setPosition` only writes `startPos`, `line`, `col` (all from `p2`),
    the intermediate `p1` has no effect. -/
@[simp]
theorem setPosition_setPosition (s : YamlStream) (p1 p2 : YamlPos) :
    Parser.Stream.setPosition (Parser.Stream.setPosition s p1) p2 =
    Parser.Stream.setPosition s p2 := by
  simp only [Parser.Stream.setPosition]

/-- `getPosition` after `setPosition` returns the set position. (get-set law) -/
@[simp]
theorem getPosition_setPosition (s : YamlStream) (p : YamlPos) :
    Parser.Stream.getPosition (Parser.Stream.setPosition s p) = p := by
  simp only [Parser.Stream.getPosition, Parser.Stream.setPosition, YamlStream.getPos]

/-- When `Stream.next?` advances the stream, `setPosition` with the
    original position fully restores the stream to its pre-advance state.
    This follows because `next?` only modifies `startPos`/`line`/`col`,
    and `setPosition` overwrites exactly those fields.

    Proof delegates to `anyToken_setPosition_roundtrip` from
    `PerParserSpecs`: construct the equivalent `anyToken` hypothesis,
    then apply the existing roundtrip lemma. -/
theorem next_setPosition_id (s s' : YamlStream) (c : Char)
    (h : _root_.Stream.next? s = some (c, s')) :
    Parser.Stream.setPosition s' (Parser.Stream.getPosition s) = s := by
  have h_at : (anyToken (m := Id) : YamlParser Char) s = .ok s' c := by
    simp only [anyToken_eq, h]
  exact anyToken_setPosition_roundtrip s s' c h_at

/-! ## §2  skipBOM Specification -/

/-- `skipBOM` is identity on a stream whose first char is not BOM, or empty.
    Required at the start of `document` to prove the stream is unchanged
    when the input has no BOM prefix. -/
theorem skipBOM_noop (s : YamlStream)
    (h : ∀ c s', _root_.Stream.next? s = some (c, s') → c ≠ '\uFEFF') :
    skipBOM s = .ok s () := by
  unfold skipBOM Parser.token
  simp only [bind_eq, option_question_eq, tokenFilter_eq, pure_eq]
  cases h_next : _root_.Stream.next? s with
  | none =>
    simp [setPosition_getPosition_id]
  | some p =>
    obtain ⟨c, s'⟩ := p
    have h_ne := h c s' (by rw [h_next])
    simp only [beq_iff_eq, h_ne, ite_false]
    have h_at : (anyToken (m := Id) : YamlParser Char) s = .ok s' c := by
      simp only [anyToken_eq, h_next]
    have h_eq := anyToken_setPosition_roundtrip s s' c h_at
    simp [h_eq]

/-! ## §3  `parseYaml` → `yamlStream` Bridge (convenience forms) -/

/-- If `yamlStream` succeeds on `ofString input` with no validation error,
    then `parseYamlRaw input = .ok docs`.

    **P10.2**: This theorem linked the old `yamlStream` char-level parser to the
    public API.  Now that `parseYamlRaw` delegates to `TokenParser.parseYamlRaw`,
    the link between the old parser internals and the public API no longer holds.
    This theorem will be removed or rewritten in P10.5 (Proof Migration — Rewrites).
    -/
theorem parseYamlRaw_of_yamlStream_ok (input : String) (docs : Array YamlDocument)
    (s' : YamlStream)
    (h_ys : yamlStream (YamlStream.ofString input) = .ok s' docs)
    (h_val : s'.validationError = none) :
    parseYamlRaw input = .ok docs := by
  sorry

/-- If `yamlStream` succeeds on `ofString input` with no validation error,
    then `parseYaml input = .ok (docs.map YamlDocument.compose)`.

    **P10.2**: Same as `parseYamlRaw_of_yamlStream_ok` — old parser bridge,
    no longer provable now that `parseYaml` delegates to `TokenParser.parseYaml`.
    Will be removed or rewritten in P10.5.
    -/
theorem parseYaml_of_yamlStream_ok (input : String) (docs : Array YamlDocument)
    (s' : YamlStream)
    (h_ys : yamlStream (YamlStream.ofString input) = .ok s' docs)
    (h_val : s'.validationError = none) :
    parseYaml input = .ok (docs.map YamlDocument.compose) := by
  sorry

/-! ## §4  Fuel Wrapper Unfolding

Each `*Impl` function has a corresponding wrapper that computes
`fuel := 4 * Stream.remaining (← getStream) + 4` and delegates.
These lemmas unfold the wrapper, exposing the `*Impl` call with
concrete fuel.

This connects the per-parser specs in `PerParserSpecs.lean` (which
reason about `*Impl` with explicit fuel) to the top-level wrappers
that callers actually invoke.

Note: For functions with default parameters (e.g., `scalarIndent`),
we parenthesize `(wrapper args)` to ensure default args are resolved
before applying the stream.
-/

/-- `blockValue` computes fuel and delegates to `blockValueImpl`. -/
theorem blockValue_eq (minIndent : Nat) (s : YamlStream) :
    (blockValue minIndent) s =
      (blockValueImpl (4 * Parser.Stream.remaining s + 4) minIndent) s := by
  unfold blockValue
  simp only [bind_eq, getStream_eq]

/-- `dispatchByChar` computes fuel and delegates to `dispatchByCharImpl`. -/
theorem dispatchByChar_eq (contentIndent : Nat) (s : YamlStream) :
    (dispatchByChar contentIndent) s =
      (dispatchByCharImpl (4 * Parser.Stream.remaining s + 4) contentIndent) s := by
  unfold dispatchByChar
  simp only [bind_eq, getStream_eq]

/-- `blockSequence` computes fuel and delegates to `blockSequenceImpl`. -/
theorem blockSequence_eq (minIndent : Nat) (s : YamlStream) :
    blockSequence minIndent s =
      (blockSequenceImpl (4 * Parser.Stream.remaining s + 4) minIndent) s := by
  unfold blockSequence
  simp only [bind_eq, getStream_eq]

/-- `blockMapping` computes fuel and delegates to `blockMappingImpl`. -/
theorem blockMapping_eq (minIndent : Nat) (s : YamlStream) :
    (blockMapping minIndent) s =
      (blockMappingImpl (4 * Parser.Stream.remaining s + 4) minIndent) s := by
  unfold blockMapping
  simp only [bind_eq, getStream_eq]

/-- `flowValue` computes fuel and delegates to `flowValueImpl`. -/
theorem flowValue_eq (minIndent : Nat) (s : YamlStream) :
    (flowValue minIndent) s =
      (flowValueImpl (4 * Parser.Stream.remaining s + 4) minIndent) s := by
  unfold flowValue
  simp only [bind_eq, getStream_eq]

/-! ## §5  Combinator Extensions

Additional combinator specs beyond `ParserSpecs.lean`, needed for
document-level composition.  These cover `endOfInput` (used at the
end of `yamlStream`) and `Parser.test` (used at the start of
`document` to check for empty input).
-/

/-- `endOfInput` succeeds (returning `PUnit.unit`) when stream is empty. -/
theorem endOfInput_eof (s : YamlStream)
    (h : _root_.Stream.next? s = none) :
    (endOfInput (m := Id) : YamlParser PUnit) s =
      .ok s PUnit.unit := by
  unfold endOfInput
  simp only [notFollowedBy_eq, anyToken_eq, h, setPosition_getPosition_id]

/-- `endOfInput` fails when the stream has remaining input. -/
theorem endOfInput_not_eof (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : _root_.Stream.next? s = some (c, s')) :
    ∃ e, (endOfInput (m := Id) : YamlParser PUnit) s =
      .error (Parser.Stream.setPosition s' (Parser.Stream.getPosition s)) e := by
  unfold endOfInput
  simp only [notFollowedBy_eq, anyToken_eq, h]
  exact ⟨_, rfl⟩

/-- Helper: `endOfInput *> return true` succeeds when stream is empty. -/
private theorem eoi_then_true (s : YamlStream)
    (h : _root_.Stream.next? s = none) :
    (endOfInput *> (return true : YamlParser Bool)) s = .ok s true := by
  show (endOfInput >>= fun _ => (return true : YamlParser Bool)) s = _
  simp only [bind_eq, endOfInput_eof s h, pure_eq]

/-- `test endOfInput` returns true on empty stream with position unchanged.

    The proof navigates the `test → optionD → optionM → eoption` chain:
    1. `eoption` wraps the success as `Sum.inl true`
    2. `optionM`'s match takes the `.inl` branch → `return true`
    3. `test = optionD = optionM` by definition -/
theorem test_endOfInput_eof (s : YamlStream)
    (h : _root_.Stream.next? s = none) :
    (Parser.test endOfInput : YamlParser Bool) s = .ok s true := by
  have h2 : (Parser.eoption (endOfInput *> (return true : YamlParser Bool))) s =
      .ok s (Sum.inl true) := by
    simp only [eoption_eq, eoi_then_true s h]
  have h3 : (Parser.optionM (endOfInput *> (return true : YamlParser Bool))
      (pure false : Id Bool)) s = .ok s true := by
    show (Parser.eoption _ >>= _) s = _
    simp only [bind_eq, h2]
    rfl  -- beta-iota on Sum.inl
  unfold Parser.test Parser.optionD
  exact h3

/-- `test endOfInput` returns false on non-empty stream with position unchanged.

    Position restoration through the `endOfInput → eoption → optionM`
    chain requires `next_setPosition_id` (to collapse `setPosition s'
    (getPosition s) = s` when `s'` comes from `next?`) and
    `setPosition_getPosition_id` (final roundtrip). -/
theorem test_endOfInput_not_eof (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : _root_.Stream.next? s = some (c, s')) :
    (Parser.test endOfInput : YamlParser Bool) s = .ok s false := by
  obtain ⟨e, he⟩ := endOfInput_not_eof s c s' h
  have h1 : (endOfInput *> (return true : YamlParser Bool)) s =
      .error (Parser.Stream.setPosition s' (Parser.Stream.getPosition s)) e := by
    show (endOfInput >>= fun _ => (return true : YamlParser Bool)) s = _
    simp only [bind_eq, he]
  have h2 : (Parser.eoption (endOfInput *> (return true : YamlParser Bool))) s =
      .ok s (Sum.inr e) := by
    simp only [eoption_eq, h1, next_setPosition_id s s' c h, setPosition_getPosition_id]
  have h3 : (Parser.optionM (endOfInput *> (return true : YamlParser Bool))
      (pure false : Id Bool)) s = .ok s false := by
    show (Parser.eoption _ >>= _) s = _
    simp only [bind_eq, h2]
    rfl  -- beta-iota on Sum.inr + Id monadLift reduction
  unfold Parser.test Parser.optionD
  exact h3

/-! ## §6  Stream Accessor Specifications

These cover the parser-level accessors used in `document` to manage
state (anchor maps, validation errors) between document parses in
a multi-document stream.
-/

/-- `resetAnchorMap` clears the anchor map and returns the stream.
    The stream is modified only in its `anchorMap` field. -/
theorem resetAnchorMap_eq (s : YamlStream) :
    resetAnchorMap s =
      .ok { s with anchorMap := AnchorMap.empty } () := by
  unfold resetAnchorMap
  simp only [bind_eq, getStream_eq, setStream_eq]

/-- `getValidationError` reads the validation error from the stream. -/
theorem getValidationError_eq (s : YamlStream) :
    getValidationError s = .ok s s.validationError := by
  unfold getValidationError
  simp only [bind_eq, getStream_eq, pure_eq]

/-- `setValidationError` on a fresh stream (no prior error) records the error. -/
theorem setValidationError_fresh_eq (msg : String) (s : YamlStream)
    (h : s.validationError = none) :
    (setValidationError msg) s =
      .ok { s with validationError := some msg } () := by
  unfold setValidationError
  simp only [bind_eq, getStream_eq, h, Option.isNone]
  rfl

/-- `setValidationError` on a stream with existing error is a no-op. -/
theorem setValidationError_existing_eq (msg prev : String) (s : YamlStream)
    (h : s.validationError = some prev) :
    (setValidationError msg) s = .ok s () := by
  unfold setValidationError
  simp only [bind_eq, getStream_eq, h, Option.isNone]
  rfl

end Lean4Yaml.Proofs.Composition
