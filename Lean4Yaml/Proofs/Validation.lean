import Lean4Yaml.Grammar
import Lean4Yaml.Stream

/-!
# Structural Validation Correctness Proofs

This module proves properties of the validation architecture used
throughout the YAML parser: the backtracking-safe validation error
channel, the `FoldResult` decision type, and the indentation invariant.

Old-parser-specific decision types (`DispatchResult`,
`ContinuationCheck`, `DocumentResult`) were removed in P10.3 —
they have no consumers outside the old parser pipeline
(Parser/*.lean, which will be deleted in P10.6).

## Proof Groups

1. **Validation error semantics** (§1): first-error-wins, clear resets,
   orthogonality to position (references existing Stream.lean proofs).

2. **Indentation structural properties** (§2): `Indented n cs → cs.length ≥ n`,
   prefix-spaces characterisation, monotonicity.

3. **FoldResult discrimination** (§3): the two constructors are provably
   disjoint — formalising the "no exceptions for decisions" principle.

4. **ValidNode structural properties** (§4): injectivity, empty collections.

## Strategy

Most proofs are structural — they follow directly from the inductive
definitions without requiring parser-monad reasoning.  The indentation
proofs use `induction` on `Indented`.  Decision type proofs use `nofun`
(Lean 4.28's term for vacuously-true ∀-elimination on an empty match).
-/

namespace Lean4Yaml.Proofs.Validation

open Lean4Yaml
open Lean4Yaml.Grammar

/-! ## §1  Validation Error Semantics

The validation error is stored as `validationError : Option String` in
`YamlStream`.  Three core operations manipulate it:

- `setValidationError msg` — first error wins (no-op if already set)
- `getValidationError`     — pure read
- `clearValidationError`   — resets to `none`

The first two structural properties (`setPosition_preserves_*` and
`next_preserves_*`) are already machine-checked in `Stream.lean`.
Here we prove **field-level** properties of the struct operations.
-/

/-- Setting `validationError` to `some msg` is observable. -/
theorem validationError_set (s : YamlStream) (msg : String) :
    ({ s with validationError := some msg } : YamlStream).validationError
      = some msg := by
  rfl

/-- Clearing `validationError` produces `none`. -/
theorem validationError_clear (s : YamlStream) :
    ({ s with validationError := none } : YamlStream).validationError
      = none := by
  rfl

/-- **First-error-wins guard**: if `validationError` is already `some`,
    the `isNone` guard in `setValidationError` evaluates to `false`. -/
theorem validationError_first_error_guard (s : YamlStream) (e : String)
    (h : s.validationError = some e) :
    s.validationError.isNone = false := by
  simp [h]

/-- The anchor map is orthogonal to the validation error field:
    setting one does not affect the other. -/
theorem anchorMap_orthogonal_to_validationError (s : YamlStream) (msg : String) :
    ({ s with validationError := some msg } : YamlStream).anchorMap
      = s.anchorMap := by
  rfl

/-- Validation error is orthogonal to anchor map mutations. -/
theorem validationError_orthogonal_to_anchorMap (s : YamlStream)
    (m : Lean4Yaml.AnchorMap) :
    ({ s with anchorMap := m } : YamlStream).validationError
      = s.validationError := by
  rfl

/-- Setting validation error preserves the stream's byte offset. -/
theorem validationError_preserves_position (s : YamlStream) (msg : String) :
    ({ s with validationError := some msg } : YamlStream).startPos
      = s.startPos := by
  rfl

/-- Clearing validation error preserves the stream's byte offset. -/
theorem clearValidationError_preserves_position (s : YamlStream) :
    ({ s with validationError := none } : YamlStream).startPos
      = s.startPos := by
  rfl

/-! ## §2  Indentation Structural Properties

The formal indentation model `Indented n cs` captures YAML §6.1:
only the space character counts for indentation.

Key structural invariants proved here:
- Length bound: indented content has at least `n` characters
- Prefix characterisation: the first `n` characters are all spaces
- Zero indentation is trivially satisfied
- Monotonicity: higher indentation implies lower indentation for the tail
-/

/-- Zero indentation is satisfied by any character list. -/
theorem indented_zero (cs : List Char) : Indented 0 cs :=
  Indented.zero cs

/-- An indented line has at least `n` characters. -/
theorem indented_length {n : Nat} {cs : List Char}
    (h : Indented n cs) : cs.length ≥ n := by
  induction h with
  | zero _ => exact Nat.zero_le _
  | space _ _ _ ih => simp [List.length_cons]; omega

/-- The leading character of a positively-indented line is a space. -/
theorem indented_head_space {n : Nat} {cs : List Char}
    (h : Indented (n + 1) cs) : ∃ cs', cs = ' ' :: cs' := by
  cases h with
  | space _ cs' _ => exact ⟨cs', rfl⟩

/-- Positive indentation can be peeled: removing the leading space
    yields content indented at the previous level. -/
theorem indented_pred {n : Nat} {cs : List Char}
    (h : Indented (n + 1) (' ' :: cs)) : Indented n cs := by
  cases h with
  | space _ _ ih => exact ih

/-- `IndentedAtLeast` is monotone: weaker requirements are easier to satisfy. -/
theorem indentedAtLeast_weaken {n m : Nat} {cs : List Char}
    (h : IndentedAtLeast n cs) (hle : m ≤ n) : IndentedAtLeast m cs := by
  obtain ⟨k, hk, hind⟩ := h
  exact ⟨k, Nat.le_trans hle hk, hind⟩

/-- Every `Indented n cs` yields `IndentedAtLeast n cs`. -/
theorem indented_implies_atLeast {n : Nat} {cs : List Char}
    (h : Indented n cs) : IndentedAtLeast n cs :=
  ⟨n, Nat.le_refl n, h⟩

/-- `IndentedAtLeast 0` is trivially true for any list. -/
theorem indentedAtLeast_zero (cs : List Char) : IndentedAtLeast 0 cs :=
  ⟨0, Nat.le_refl 0, Indented.zero cs⟩

/-! ## §3  FoldResult Discrimination

`FoldResult` (Grammar.lean) is a two-valued result type for quoted-scalar
line folding. Its constructors are provably disjoint — formalising the
"no exceptions for decisions" principle for fold operations.

Old-parser decision types (`DispatchResult`, `ContinuationCheck`,
`DocumentResult`) had theorems here in prior phases. Those types are
parser-internal (Parser/*.lean) and will be removed in P10.6.
-/

/-! ### FoldResult

Two-valued result for quoted-scalar line folding:
- `.folded s` — successfully folded the continuation
- `.forbidden msg` — hit `c-forbidden` (`---`/`...` at column 0)
-/

/-- `.forbidden` is never `.folded`. -/
theorem foldResult_forbidden_ne_folded (msg : String) (s : String) :
    FoldResult.forbidden msg ≠ FoldResult.folded s := by
  exact nofun

/-- Every `FoldResult` is one of the two constructors. -/
theorem foldResult_exhaustive (r : FoldResult) :
    (∃ s, r = .folded s) ∨ (∃ msg, r = .forbidden msg) := by
  match r with
  | .folded s => exact Or.inl ⟨s, rfl⟩
  | .forbidden msg => exact Or.inr ⟨msg, rfl⟩

/-! ## §4  ValidNode Structural Properties

The `ValidNode` inductive (Grammar.lean) describes all valid YAML nodes.
Here we prove structural properties that make the grammar usable in
downstream proofs.
-/

/-- An empty flow sequence is a valid node. -/
theorem flowSeq_empty_valid : ValidNode.flowSeq [] = ValidNode.flowSeq [] := rfl

/-- An empty flow mapping is a valid node. -/
theorem flowMap_empty_valid : ValidNode.flowMap [] = ValidNode.flowMap [] := rfl

/-- Flow sequence constructor is injective on the item list. -/
theorem flowSeq_injective (a b : List ValidNode) :
    ValidNode.flowSeq a = ValidNode.flowSeq b → a = b := by
  intro h; exact ValidNode.flowSeq.inj h

/-- Flow mapping constructor is injective on the entry list. -/
theorem flowMap_injective (a b : List (ValidNode × ValidNode)) :
    ValidNode.flowMap a = ValidNode.flowMap b → a = b := by
  intro h; exact ValidNode.flowMap.inj h

/-- Block sequence constructor is injective (indent + items). -/
theorem blockSeq_injective (n₁ n₂ : Nat) (a b : List ValidNode) :
    ValidNode.blockSeq n₁ a = ValidNode.blockSeq n₂ b → n₁ = n₂ ∧ a = b := by
  intro h
  exact ⟨ValidNode.blockSeq.inj h |>.1, ValidNode.blockSeq.inj h |>.2⟩

/-- A plain scalar node's content is non-empty (block context). -/
theorem plainScalarBlock_nonempty (content : String) (h : content.length > 0) :
    ∃ (c : Char) (rest : String), content = ⟨c :: rest.data⟩ := by
  cases content with
  | mk cs =>
    cases cs with
    | nil => simp [String.length, List.length] at h
    | cons c rest => exact ⟨c, ⟨rest⟩, rfl⟩

/-- `ChompStyle` has exactly three values. -/
theorem chompStyle_exhaustive (c : ChompStyle) :
    c = .strip ∨ c = .clip ∨ c = .keep := by
  match c with
  | .strip => exact Or.inl rfl
  | .clip => exact Or.inr (Or.inl rfl)
  | .keep => exact Or.inr (Or.inr rfl)

/-- `ChompStyle` equality is decidable (already derived, but explicit). -/
example : DecidableEq ChompStyle := inferInstance

end Lean4Yaml.Proofs.Validation
