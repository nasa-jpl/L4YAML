/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Parser
import Lean4Yaml.Stream
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Proofs.ParserSpecs

/-!
# Per-Parser Specification Lemmas  (Step 5.4.3)

Intermediate specification lemmas that bridge the generic combinator
specs (Step 5.4.2) to per-parser correctness for each `ValidNode`
constructor.

## Architecture

### §1  Wrapper Transparency
`withErrorMessage` is used by every YAML parser.  It is transparent on
success — the lemma `withErrorMessage_ok` lets proofs ignore the error
wrapping entirely when showing a parser succeeds.

### §2  YamlStream.next? Characterization
Links `Parser.Stream.next?` (generic) to `YamlStream.next?` (concrete).
These lemmas drive all token-level reasoning.

### §3  Concrete Token Lemmas
`anyToken`, `token`, `tokenFilter`, `char` specialized for `YamlStream`.
These are the building blocks for per-parser proofs.

### §4  Per-Parser Specification Theorems
One correctness theorem per `ValidNode` constructor.

## Zero Axioms

All proved lemmas are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.PerParserSpecs

open Parser Lean4Yaml.Parse Lean4Yaml.Grammar

-- Re-export key simp lemmas from ParserSpecs
open Lean4Yaml.Proofs.ParserSpecs in

/-! ## §1  Wrapper Transparency

`withErrorMessage msg p` wraps `p` in `try ... catch`, rewriting the
error message but passing through success results unchanged.  Since
every YAML parser wraps its body in `withErrorMessage`, this transparency
lemma is prerequisite for all per-parser proofs.
-/

/--
`withErrorMessage` applied to a stream unfolds to a `tryCatch` that
passes through success and rewrites errors.
-/
@[simp]
theorem withErrorMessage_eq {ε σ : Type} {τ : Type} {α : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (msg : String) (p : Parser ε σ τ α) (s : σ) :
    (withErrorMessage msg p) s =
      match p s with
      | .ok s' a => .ok s' a
      | .error s' e => throwErrorWithMessage e msg s' := by
  dsimp only [withErrorMessage, tryCatch, tryCatchThe, MonadExcept.tryCatch,
              MonadExceptOf.tryCatch, bind, Bind.bind, pure, Pure.pure,
              ParserT.run]
  cases p s <;> rfl

/--
If `p s` succeeds, then `withErrorMessage msg p s` succeeds with the
same result.  This is the key transparency lemma: proofs that show `p`
succeeds can ignore the `withErrorMessage` wrapper entirely.
-/
theorem withErrorMessage_of_ok {ε σ : Type} {τ : Type} {α : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (msg : String) (p : Parser ε σ τ α) (s s' : σ) (a : α)
    (h : p s = .ok s' a) :
    (withErrorMessage msg p) s = .ok s' a := by
  simp [h]

/--
`throwErrorWithMessage` produces an error with the given message at the
current position.
-/
@[simp]
theorem throwErrorWithMessage_eq {ε σ : Type} {τ : Type} {α : Type}
    [Parser.Stream σ τ] [Parser.Error ε σ τ]
    (e : ε) (msg : String) (s : σ) :
    (throwErrorWithMessage e msg : Parser ε σ τ α) s =
      .error s (Error.addMessage e (Stream.getPosition s) msg) := by
  simp only [throwErrorWithMessage, bind, Bind.bind, pure, Pure.pure,
             getPosition, Functor.map, throw, MonadExceptOf.throw,
             Parser.getStream, throwThe]

/-! ## §2  YamlStream.next? Characterization

The lean4-parser `tokenCore` calls `Stream.next?`, which for `YamlStream`
resolves to `YamlStream.next?`.  These lemmas expose the concrete behavior.
-/

/--
For `YamlStream`, `Std.Stream.next?` delegates to `YamlStream.next?`.
This lets hypotheses of either form be used interchangeably.
-/
@[simp]
theorem stream_next?_eq (s : YamlStream) :
    @Std.Stream.next? YamlStream Char _ s = YamlStream.next? s := rfl

/--
When the stream has remaining input (`startPos < stopPos`), `next?` returns
the current character and an advanced stream.
-/
theorem YamlStream_next?_some (s : YamlStream) (h : s.startPos < s.stopPos) :
    YamlStream.next? s =
      let c := String.Pos.Raw.get s.str s.startPos
      let nextPos := String.Pos.Raw.next s.str s.startPos
      let (newLine, newCol) :=
        if c == '\n' then (s.line + 1, 0)
        else (s.line, s.col + 1)
      some (c, { s with
        startPos := nextPos
        line := newLine
        col := newCol
      }) := by
  simp only [YamlStream.next?, h, ↓reduceIte]

/--
When the stream is exhausted (`¬(startPos < stopPos)`), `next?` returns `none`.
-/
theorem YamlStream_next?_none (s : YamlStream)
    (h : ¬(s.startPos < s.stopPos)) :
    YamlStream.next? s = none := by
  simp only [YamlStream.next?, h, ↓reduceIte]

/-! ## §3  Concrete Token Lemmas

Specialize the generic `tokenCore_eq`, `anyToken_eq`, `tokenFilter_eq` from
`ParserSpecs` to `YamlStream` + `YamlError`.

These are the innermost building blocks: every YAML parser eventually reduces
to a sequence of `anyToken` / `tokenFilter` / `token` calls.
-/

/-- Abbreviation for the concrete YAML parser type. -/
local notation "YP" α => YamlParser α

/--
`anyToken` on a `YamlStream` with remaining input returns the current
character and advances the stream.
-/
theorem yamlAnyToken_some (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : YamlStream.next? s = some (c, s')) :
    (Parser.anyToken (m := Id) : YP Char) s = .ok s' c := by
  have h' : Stream.next? s = some (c, s') := h
  simp only [ParserSpecs.anyToken_eq, h']

/--
`anyToken` on an exhausted `YamlStream` returns an error.
-/
theorem yamlAnyToken_none (s : YamlStream) (h : YamlStream.next? s = none) :
    (Parser.anyToken (m := Id) : YP Char) s =
      .error s (Error.unexpected (Stream.getPosition s) none) := by
  have h' : Stream.next? s = none := h
  simp only [ParserSpecs.anyToken_eq, h']

/--
`tokenFilter test` on a `YamlStream` where the next character passes `test`.
-/
theorem yamlTokenFilter_ok (s : YamlStream) (c : Char) (s' : YamlStream)
    (test : Char → Bool)
    (hnext : YamlStream.next? s = some (c, s'))
    (htest : test c = true) :
    (Parser.tokenFilter (ε := YamlError) (m := Id) test) s = .ok s' c := by
  have hnext' : Stream.next? s = some (c, s') := hnext
  simp only [ParserSpecs.tokenFilter_eq, hnext', htest, ↓reduceIte]

/--
`tokenFilter test` where the next character *fails* `test`.
-/
theorem yamlTokenFilter_fail (s : YamlStream) (c : Char) (s' : YamlStream)
    (test : Char → Bool)
    (hnext : YamlStream.next? s = some (c, s'))
    (htest : test c = false) :
    (Parser.tokenFilter (ε := YamlError) (m := Id) test) s =
      .error s' (Error.unexpected (Stream.getPosition s') (some c)) := by
  have hnext' : Stream.next? s = some (c, s') := hnext
  simp only [ParserSpecs.tokenFilter_eq, hnext']
  simp [htest]

/--
`token tk` succeeds when the next character equals `tk`.
This unfolds `token` → `tokenFilter (· == tk)`.
-/
@[simp]
theorem yamlToken_ok (s : YamlStream) (c : Char) (s' : YamlStream)
    (tk : Char)
    (hnext : YamlStream.next? s = some (c, s'))
    (heq : (c == tk) = true) :
    (Parser.token (ε := YamlError) (m := Id) tk) s = .ok s' c := by
  simp only [Parser.token]
  exact yamlTokenFilter_ok s c s' (fun x => x == tk) hnext heq

/--
`Parser.Char.char tk` — the standard parser `char` is `withErrorMessage` around `token`.
On success, it behaves identically to `token`.
-/
theorem yamlChar_ok (s : YamlStream) (c : Char) (s' : YamlStream)
    (tk : Char)
    (hnext : YamlStream.next? s = some (c, s'))
    (heq : (c == tk) = true) :
    (Parser.Char.char (ε := YamlError) (m := Id) tk) s = .ok s' c := by
  simp only [Parser.Char.char]
  exact withErrorMessage_of_ok _ _ _ _ _ (yamlToken_ok s c s' tk hnext heq)

/-! ## §4  Per-Parser Specification Theorems

Each `ValidNode` constructor corresponds to a parser.  The specification
takes the form:

  `∀ (stream conditions), parser stream = .ok stream' (toYamlValue node)`

The stream conditions encode that the input contains a well-formed
representation of the grammar node.

### Approach

We build bottom-up:
1. Token-level lemmas (§3 above) handle single-character consumption
2. Loop lemmas handle fuel-bounded iteration (collectChars, collectPlain)
3. Per-parser lemmas compose token + loop lemmas

### Status

| Constructor | Status |
|-------------|--------|
| `singleQuoted` | WIP — loop lemma needed |
| `doubleQuoted` | WIP — escape resolution |
| `plainScalarBlock` | ✓ — `plainScalarSingleLine_block` |
| `plainScalarFlow` | ✓ — `plainScalarSingleLine_flow` |
| `literalScalar` | WIP — applyChomp, processFolded.go, collectLines loop, autoDetectIndent (11 lemmas) |
| `foldedScalar` | WIP — applyChomp, processFolded.go, collectLines loop, autoDetectIndent (11 lemmas) |
| `blockSeq` | planned — mutual recursion |
| `blockMap` | planned — mutual recursion |
| `flowSeq` | planned — mutual recursion |
| `flowMap` | planned — mutual recursion |
-/

/-! ### §4.1  `option?` derived lemmas

`option?` is fundamental — used by nearly every YAML parser for optional
elements.  We specialize the generic spec for `YamlParser`.
-/

/--
`option? p` on `YamlStream`: when `p` succeeds, returns `some`.
-/
theorem yamlOption?_some {α : Type} (p : YP α) (s s' : YamlStream) (a : α)
    (h : p s = .ok s' a) :
    (option? p) s = .ok s' (some a) := by
  simp only [ParserSpecs.option_question_eq, h]

/--
`option? p` on `YamlStream`: when `p` fails, returns `none` with
position restored.
-/
theorem yamlOption?_none {α : Type} (p : YP α) (s s' : YamlStream) (e : YamlError)
    (h : p s = .error s' e) :
    (option? p) s = .ok (Stream.setPosition s' (Stream.getPosition s)) none := by
  simp only [ParserSpecs.option_question_eq, h]

/-! ### §4.2  `lookAhead` derived lemma -/

/--
`lookAhead p` on `YamlStream`: when `p` succeeds, returns the value
but restores position.
-/
theorem yamlLookAhead_ok {α : Type} (p : YP α) (s s' : YamlStream) (a : α)
    (h : p s = .ok s' a) :
    (lookAhead p) s =
      .ok (Stream.setPosition s' (Stream.getPosition s)) a := by
  simp only [ParserSpecs.lookAhead_eq, h]

/-! ## §5  Anchor Parser Specifications

`lookupAnchor` and `parseAlias` are the simplest YAML-level parsers.
We fully characterize them, demonstrating the proof pattern that
composes `bind_eq`, `getStream_eq`, `pure_eq`, and `withErrorMessage_eq`.
-/

/--
`lookupAnchor name` searches the anchor map without modifying the stream.
-/
@[simp]
theorem lookupAnchor_eq (name : String) (s : YamlStream) :
    lookupAnchor name s = .ok s (AnchorMap.find? s.anchorMap name) := by
  simp only [lookupAnchor, ParserSpecs.bind_eq, ParserSpecs.getStream_eq,
             ParserSpecs.pure_eq]

/--
**parseAlias — success, anchor found.**

When `char '*'` succeeds, `anchorName` parses the name, and the anchor
IS in the stream's anchor map, `parseAlias` returns `.alias name`
(the serialization-tree form). The anchor `val` witnesses existence.
-/
theorem parseAlias_found (s s₁ s₂ : YamlStream) (name : String) (val : YamlValue)
    (h_star : (Parser.Char.char (ε := YamlError) (m := Id) '*') s = .ok s₁ '*')
    (h_name : anchorName s₁ = .ok s₂ name)
    (h_find : AnchorMap.find? s₂.anchorMap name = some val) :
    parseAlias s = .ok s₂ (.alias name) := by
  unfold parseAlias
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_star, h_name, lookupAnchor_eq, h_find, ParserSpecs.pure_eq]

/--
**parseAlias — success, anchor undefined.**

When `char '*'` succeeds, `anchorName` parses the name, but the anchor
is NOT in the map, `parseAlias` returns `.alias name` and sets a
validation error.
-/
theorem parseAlias_not_found (s s₁ s₂ : YamlStream) (name : String)
    (h_star : (Parser.Char.char (ε := YamlError) (m := Id) '*') s = .ok s₁ '*')
    (h_name : anchorName s₁ = .ok s₂ name)
    (h_find : AnchorMap.find? s₂.anchorMap name = none)
    -- setValidationError post-condition:
    (s₃ : YamlStream)
    (h_seterr : setValidationError s!"undefined anchor: *{name}" s₂ = .ok s₃ ()) :
    parseAlias s = .ok s₃ (.alias name) := by
  unfold parseAlias
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_star, h_name, lookupAnchor_eq, h_find, h_seterr,
             ParserSpecs.pure_eq]

/-! ## §6  `setValidationError` Specification

`setValidationError` is called by parsers to record soft errors without
failing.  It is a first-error-wins write to `stream.validationError`.
-/

/--
`setValidationError` when no previous error exists: sets the error and
preserves the stream otherwise unchanged.
-/
theorem setValidationError_fresh (msg : String) (s : YamlStream)
    (h : s.validationError = none) :
    setValidationError msg s =
      .ok { s with validationError := some msg } PUnit.unit := by
  unfold setValidationError
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq, h]
  rfl

/--
`setValidationError` when a previous error already exists: no-op.
-/
theorem setValidationError_already (msg : String) (s : YamlStream) (prev : String)
    (h : s.validationError = some prev) :
    setValidationError msg s = .ok s PUnit.unit := by
  unfold setValidationError
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq, h]
  rfl

/-! ## §7  Pure Block Scalar Helpers

`processLiteral`, `processFolded`, and `applyChomp` are pure string
transformations.  Their specifications are stated here as `@[simp]`
lemmas.
-/

/-- `processLiteral` is the identity function. -/
@[simp]
theorem processLiteral_eq (raw : String) :
    Lean4Yaml.Parse.processLiteral raw = raw := rfl

/-- `applyChomp .keep` is the identity. -/
@[simp]
theorem applyChomp_keep (content : String) :
    Lean4Yaml.Parse.applyChomp content .keep = content := rfl

/-- `applyChomp .strip` trims trailing ASCII whitespace. -/
@[simp]
theorem applyChomp_strip (content : String) :
    Lean4Yaml.Parse.applyChomp content .strip = content.trimAsciiEnd.toString := rfl

/-- `applyChomp .clip` trims then appends one newline (or empty if all whitespace). -/
@[simp]
theorem applyChomp_clip (content : String) :
    Lean4Yaml.Parse.applyChomp content .clip =
      let trimmed := content.trimAsciiEnd.toString
      if trimmed.isEmpty then "" else trimmed.push '\n' := rfl

/-! ### §7.1  `processFolded` Lemmas

`processFolded` splits on `"\n"` and folds lines into the result.
Its `where`-clause helper `go` is specified by structural induction
on the line list.
-/

/-- `processFolded.go` on an empty list returns the accumulator. -/
@[simp]
theorem processFolded_go_nil (acc : String) (first : Bool) :
    Lean4Yaml.Parse.processFolded.go [] acc first = acc := by
  unfold Lean4Yaml.Parse.processFolded.go
  rfl

/-- `processFolded.go` on a singleton list with `first = true` returns that line. -/
@[simp]
theorem processFolded_go_singleton_first (line : String) (acc : String) :
    Lean4Yaml.Parse.processFolded.go [line] acc true = line := by
  unfold Lean4Yaml.Parse.processFolded.go
  simp

/-- `processFolded.go` on a singleton non-empty line with `first = false`
    joins with space. -/
theorem processFolded_go_singleton_nonempty (line : String) (acc : String)
    (h : line.isEmpty = false) :
    Lean4Yaml.Parse.processFolded.go [line] acc false = acc ++ " " ++ line := by
  unfold Lean4Yaml.Parse.processFolded.go
  simp [h]

/-- `processFolded.go` on a singleton empty line with `first = false`
    returns the accumulator unchanged. -/
@[simp]
theorem processFolded_go_singleton_empty (acc : String) :
    Lean4Yaml.Parse.processFolded.go [""] acc false = acc := by
  unfold Lean4Yaml.Parse.processFolded.go
  simp [String.isEmpty]

/-- `processFolded.go` on `line :: next :: rest` with `first = true`
    recurses with `acc := line`. -/
@[simp]
theorem processFolded_go_cons_first (line : String) (next : String) (rest : List String)
    (acc : String) :
    Lean4Yaml.Parse.processFolded.go (line :: next :: rest) acc true =
      Lean4Yaml.Parse.processFolded.go (next :: rest) line false := by
  show Lean4Yaml.Parse.processFolded.go (line :: next :: rest) acc true = _
  rw [Lean4Yaml.Parse.processFolded.go]
  · simp
  · exact fun h => absurd h (List.cons_ne_nil _ _)

/-- `processFolded.go` on an empty line with `first = false` preserves a newline. -/
@[simp]
theorem processFolded_go_cons_empty (next : String) (rest : List String)
    (acc : String) :
    Lean4Yaml.Parse.processFolded.go ("" :: next :: rest) acc false =
      Lean4Yaml.Parse.processFolded.go (next :: rest) (acc.push '\n') false := by
  show Lean4Yaml.Parse.processFolded.go ("" :: next :: rest) acc false = _
  rw [Lean4Yaml.Parse.processFolded.go]
  · simp [String.isEmpty]
  · exact fun h => absurd h (List.cons_ne_nil _ _)

/-- `processFolded.go` on a more-indented line (starts with space) preserves newline. -/
theorem processFolded_go_cons_more_indented (line : String) (next : String)
    (rest : List String) (acc : String)
    (h_ne : line.isEmpty = false) (h_sp : (line.front == ' ') = true) :
    Lean4Yaml.Parse.processFolded.go (line :: next :: rest) acc false =
      Lean4Yaml.Parse.processFolded.go (next :: rest) (acc ++ "\n" ++ line) false := by
  show Lean4Yaml.Parse.processFolded.go (line :: next :: rest) acc false = _
  rw [Lean4Yaml.Parse.processFolded.go]
  · simp [h_ne, h_sp]
  · exact fun h => absurd h (List.cons_ne_nil _ _)

/-- `processFolded.go` on a normal (non-empty, non-space-leading) line folds to space. -/
theorem processFolded_go_cons_fold (line : String) (next : String)
    (rest : List String) (acc : String)
    (h_ne : line.isEmpty = false) (h_nsp : (line.front == ' ') = false) :
    Lean4Yaml.Parse.processFolded.go (line :: next :: rest) acc false =
      Lean4Yaml.Parse.processFolded.go (next :: rest) (acc ++ " " ++ line) false := by
  show Lean4Yaml.Parse.processFolded.go (line :: next :: rest) acc false = _
  rw [Lean4Yaml.Parse.processFolded.go]
  · simp [h_ne, h_nsp]
  · exact fun h => absurd h (List.cons_ne_nil _ _)

/-! ## §8  Per-Parser Relational Specifications

One correctness theorem per `ValidNode` constructor.  Each takes the
form of a **relational spec**: hypotheses about sub-parser success
imply conclusions about the composite parser.  This avoids needing
to unfold fuel-bounded loops directly; the loop specs become separate
obligations in §5.4.4.

### Design principle

Each theorem states:
```
(sub-parser₁ succeeds) → (sub-parser₂ succeeds) → ... →
compositeParser stream = .ok stream' result
```

The hypotheses are dischargeable either by:
- Further per-parser specs (recursive composition), or
- `native_decide` on concrete inputs (as in Completeness.lean)
-/

/-! ### §8.1  Quoted Scalar Specifications -/

/--
**singleQuotedScalar — relational spec.**

When `char '\''` succeeds (opening quote) and the internal `collectChars`
loop produces `content`, `singleQuotedScalar` returns
`.scalar { content, style := .singleQuoted }`.
-/
theorem singleQuotedScalar_spec
    (s s₁ s₂ : YamlStream) (content : String) (contentIndent : Nat)
    (h_quote : (Parser.Char.char (ε := YamlError) (m := Id) '\'') s = .ok s₁ '\'')
    (h_collect : (Lean4Yaml.Parse.singleQuotedScalar.collectChars contentIndent
        (Stream.remaining s₁) "") s₁ = .ok s₂ content) :
    singleQuotedScalar contentIndent s =
      .ok s₂ (.scalar { content, style := .singleQuoted }) := by
  unfold singleQuotedScalar
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq, h_quote,
             ParserSpecs.getStream_eq, h_collect, ParserSpecs.pure_eq]

/--
**doubleQuotedScalar — relational spec.**

When `char '"'` succeeds (opening quote) and the internal `collectChars`
loop produces `content`, `doubleQuotedScalar` returns
`.scalar { content, style := .doubleQuoted }`.
-/
theorem doubleQuotedScalar_spec
    (s s₁ s₂ : YamlStream) (content : String) (contentIndent : Nat)
    (h_quote : (Parser.Char.char (ε := YamlError) (m := Id) '"') s = .ok s₁ '"')
    (h_collect : (Lean4Yaml.Parse.doubleQuotedScalar.collectChars contentIndent
        (Stream.remaining s₁) "") s₁ = .ok s₂ content) :
    doubleQuotedScalar contentIndent s =
      .ok s₂ (.scalar { content, style := .doubleQuoted }) := by
  unfold doubleQuotedScalar
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq, h_quote,
             ParserSpecs.getStream_eq, h_collect, ParserSpecs.pure_eq]

/-! ### §8.1.1  `collectChars` Loop Specifications (Quoted Scalars)

The `collectChars` `where`-clause loops in `singleQuotedScalar` and
`doubleQuotedScalar` are fuel-bounded.  These lemmas characterize
their fuel-zero base cases and closing-quote termination conditions,
following the same pattern as the `collectPlain` loop specs in §8.2.1.
-/

/--
**singleQuotedScalar.collectChars — fuel-zero base case.**

When fuel is exhausted, `collectChars` sets a validation error and
returns the current accumulator.
-/
theorem singleQuoted_collectChars_zero (contentIndent : Nat) (acc : String)
    (s s' : YamlStream)
    (h_seterr : setValidationError "unterminated single-quoted scalar" s = .ok s' ()) :
    singleQuotedScalar.collectChars contentIndent 0 acc s = .ok s' acc := by
  unfold singleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_seterr, ParserSpecs.pure_eq]

/--
**doubleQuotedScalar.collectChars — fuel-zero base case.**

When fuel is exhausted, `collectChars` sets a validation error and
returns the current accumulator.
-/
theorem doubleQuoted_collectChars_zero (contentIndent : Nat) (acc : String)
    (s s' : YamlStream)
    (h_seterr : setValidationError "unterminated double-quoted scalar" s = .ok s' ()) :
    doubleQuotedScalar.collectChars contentIndent 0 acc s = .ok s' acc := by
  unfold doubleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_seterr, ParserSpecs.pure_eq]

/--
**singleQuotedScalar.collectChars — closing quote termination.**

When the next character is a single quote `'` and the following character
is NOT another `'` (i.e., not an escaped quote `''`), the loop returns
the accumulator.
-/
theorem singleQuoted_collectChars_close
    (contentIndent fuel : Nat) (acc : String)
    (s s₁ s₂ : YamlStream)
    (h_anytoken : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '\'')
    (h_no_escape : (option? (Parser.Char.char (ε := YamlError) (m := Id) '\'')) s₁ =
      .ok s₂ none) :
    singleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₂ acc := by
  unfold singleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_anytoken, h_no_escape, ParserSpecs.pure_eq]

/--
**doubleQuotedScalar.collectChars — closing quote termination.**

When the next character is a double quote `"`, the loop returns the
accumulator immediately.
-/
theorem doubleQuoted_collectChars_close
    (contentIndent fuel : Nat) (acc : String)
    (s s₁ : YamlStream)
    (h_anytoken : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '"') :
    doubleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₁ acc := by
  unfold doubleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_anytoken, ParserSpecs.pure_eq]

/--
**singleQuotedScalar.collectChars — escaped quote step.**

When the next character is `'` followed by another `'` (escaped quote `''`),
the loop appends `'` to the accumulator and continues with decremented fuel.
-/
theorem singleQuoted_collectChars_escape
    (contentIndent fuel : Nat) (acc result : String)
    (s s₁ s₂ s₃ : YamlStream)
    (h_anytoken : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '\'')
    (h_escape : (option? (Parser.Char.char (ε := YamlError) (m := Id) '\'')) s₁ =
      .ok s₂ (some '\''))
    (h_recurse : singleQuotedScalar.collectChars contentIndent fuel
        (acc.push '\'') s₂ = .ok s₃ result) :
    singleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₃ result := by
  unfold singleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_anytoken, h_escape, h_recurse]

/--
**doubleQuotedScalar.collectChars — normal character step.**

When the next character `c` is not `"`, `\`, `\n`, or `\r`, it is
appended to the accumulator and the loop continues.
-/
theorem doubleQuoted_collectChars_char_step
    (contentIndent fuel : Nat) (acc result : String) (c : Char)
    (s s₁ s₂ : YamlStream)
    (h_anytoken : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ c)
    (hc_not_dq : (c == '"') = false)
    (hc_not_bs : (c == '\\') = false)
    (hc_not_lf : (c == '\n') = false)
    (hc_not_cr : (c == '\r') = false)
    (h_recurse : doubleQuotedScalar.collectChars contentIndent fuel
        (acc.push c) s₁ = .ok s₂ result) :
    doubleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₂ result := by
  unfold doubleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_anytoken]
  have hne_dq : c ≠ '"' := by intro h; subst h; simp at hc_not_dq
  have hne_bs : c ≠ '\\' := by intro h; subst h; simp at hc_not_bs
  have hne_lf : c ≠ '\n' := by intro h; subst h; simp at hc_not_lf
  have hne_cr : c ≠ '\r' := by intro h; subst h; simp at hc_not_cr
  split
  · exact absurd rfl hne_dq   -- c = '"': contradiction
  · exact absurd rfl hne_bs   -- c = '\\': contradiction
  · exact absurd rfl hne_lf   -- c = '\n': contradiction
  · exact absurd rfl hne_cr   -- c = '\r': contradiction
  · exact h_recurse            -- default: recursive call

/--
**singleQuotedScalar.collectChars — normal character step.**

When the next character `c` is not `'`, `\n`, or `\r`, it is appended
to the accumulator and the loop continues.
-/
theorem singleQuoted_collectChars_char_step
    (contentIndent fuel : Nat) (acc result : String) (c : Char)
    (s s₁ s₂ : YamlStream)
    (h_anytoken : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ c)
    (hc_not_sq : (c == '\'') = false)
    (hc_not_lf : (c == '\n') = false)
    (hc_not_cr : (c == '\r') = false)
    (h_recurse : singleQuotedScalar.collectChars contentIndent fuel
        (acc.push c) s₁ = .ok s₂ result) :
    singleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₂ result := by
  unfold singleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_anytoken]
  have hne_sq : c ≠ '\'' := by intro h; subst h; simp at hc_not_sq
  have hne_lf : c ≠ '\n' := by intro h; subst h; simp at hc_not_lf
  have hne_cr : c ≠ '\r' := by intro h; subst h; simp at hc_not_cr
  split
  · exact absurd rfl hne_sq   -- c = '\'': contradiction
  · exact absurd rfl hne_lf   -- c = '\n': contradiction
  · exact absurd rfl hne_cr   -- c = '\r': contradiction
  · exact h_recurse            -- default: recursive call

/-! ### §8.1.2  Double-Quoted Escape Processing Specifications

Concrete evaluation lemmas for `doubleQuotedScalar.processEscape` —
the escape-sequence dispatcher inside double-quoted scalar parsing.
Each theorem shows that for a specific escape character, the function
emits the correct character without consuming any stream tokens.
-/

/-- Escape `\n` produces line feed. -/
theorem doubleQuoted_processEscape_n (s : YamlStream) :
    doubleQuotedScalar.processEscape 'n' s = .ok s '\n' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\t` produces tab. -/
theorem doubleQuoted_processEscape_t (s : YamlStream) :
    doubleQuotedScalar.processEscape 't' s = .ok s '\t' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\\` produces backslash. -/
theorem doubleQuoted_processEscape_backslash (s : YamlStream) :
    doubleQuotedScalar.processEscape '\\' s = .ok s '\\' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\"` produces double quote. -/
theorem doubleQuoted_processEscape_dquote (s : YamlStream) :
    doubleQuotedScalar.processEscape '"' s = .ok s '"' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\0` produces null. -/
theorem doubleQuoted_processEscape_null (s : YamlStream) :
    doubleQuotedScalar.processEscape '0' s = .ok s '\x00' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\r` produces carriage return. -/
theorem doubleQuoted_processEscape_r (s : YamlStream) :
    doubleQuotedScalar.processEscape 'r' s = .ok s '\r' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\ ` produces space. -/
theorem doubleQuoted_processEscape_space (s : YamlStream) :
    doubleQuotedScalar.processEscape ' ' s = .ok s ' ' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-- Escape `\/` produces slash. -/
theorem doubleQuoted_processEscape_slash (s : YamlStream) :
    doubleQuotedScalar.processEscape '/' s = .ok s '/' := by
  unfold doubleQuotedScalar.processEscape
  simp [ParserSpecs.pure_eq]

/-! ### §8.1.3  Double-Quoted Backslash Escape Relay

When `collectChars` encounters `\\` followed by a non-linebreak character,
it delegates to `processEscape` and recursively continues.
-/

/--
**doubleQuotedScalar.collectChars — backslash + simple escape step.**

When `\\` is consumed, then `c` (not `\n`/`\r`), the loop calls
`processEscape c` and continues with the escaped character appended.
-/
theorem doubleQuoted_collectChars_backslash_escape
    (contentIndent fuel : Nat) (acc result : String) (c escaped : Char)
    (s s₁ s₂ s₃ s₄ : YamlStream)
    (h_bs : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '\\')
    (h_c : (Parser.anyToken (m := Id) : YamlParser Char) s₁ = .ok s₂ c)
    (hc_not_lf : (c == '\n') = false)
    (hc_not_cr : (c == '\r') = false)
    (h_escape : doubleQuotedScalar.processEscape c s₂ = .ok s₃ escaped)
    (h_recurse : doubleQuotedScalar.collectChars contentIndent fuel
        (acc.push escaped) s₃ = .ok s₄ result) :
    doubleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₄ result := by
  unfold doubleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_bs, h_c]
  split <;> simp_all [ParserSpecs.bind_eq]

/-! ### §8.1.4  Quoted Scalar Line Fold Loop Specifications -/

/-- `foldQuotedNewlines.loop` fuel-zero returns `.folded result` immediately. -/
@[simp]
theorem foldQuotedNewlines_loop_zero (contentIndent : Nat)
    (result : String) (blankCount : Nat) (s : YamlStream) :
    foldQuotedNewlines.loop contentIndent 0 result blankCount s =
      .ok s (.folded result) := by
  unfold foldQuotedNewlines.loop
  simp [ParserSpecs.pure_eq]

/-! ### §8.1.5  Additional Escape Character Specifications -/

/-- Escape `\a` produces bell (U+0007). -/
theorem doubleQuoted_processEscape_a (s : YamlStream) :
    doubleQuotedScalar.processEscape 'a' s = .ok s '\x07' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape `\b` produces backspace (U+0008). -/
theorem doubleQuoted_processEscape_b (s : YamlStream) :
    doubleQuotedScalar.processEscape 'b' s = .ok s '\x08' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape `\v` produces vertical tab (U+000B). -/
theorem doubleQuoted_processEscape_v (s : YamlStream) :
    doubleQuotedScalar.processEscape 'v' s = .ok s '\x0b' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape `\f` produces form feed (U+000C). -/
theorem doubleQuoted_processEscape_f (s : YamlStream) :
    doubleQuotedScalar.processEscape 'f' s = .ok s '\x0c' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape `\e` produces escape (U+001B). -/
theorem doubleQuoted_processEscape_e (s : YamlStream) :
    doubleQuotedScalar.processEscape 'e' s = .ok s '\x1b' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape `\N` produces next line (U+0085). -/
theorem doubleQuoted_processEscape_N (s : YamlStream) :
    doubleQuotedScalar.processEscape 'N' s = .ok s '\x85' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape `\_` produces non-breaking space (U+00A0). -/
theorem doubleQuoted_processEscape_underscore (s : YamlStream) :
    doubleQuotedScalar.processEscape '_' s = .ok s '\xa0' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-- Escape with literal tab character `\<TAB>` produces tab. -/
theorem doubleQuoted_processEscape_tab_literal (s : YamlStream) :
    doubleQuotedScalar.processEscape '\t' s = .ok s '\t' := by
  unfold doubleQuotedScalar.processEscape; simp [ParserSpecs.pure_eq]

/-! ### §8.1.6  Double-Quoted Line Fold Relay

When `collectChars` encounters a bare newline (`\n`), it delegates to
`foldQuotedNewlines` for line-fold processing and continues.
-/

/--
**doubleQuotedScalar.collectChars — line fold on `\n`.**

When `\n` is the current token (bare newline, not preceded by `\\`),
the loop delegates to `foldQuotedNewlines` and recurses with the folded result.
-/
theorem doubleQuoted_collectChars_linefold_lf
    (contentIndent fuel : Nat) (acc result newAcc : String)
    (s s₁ s₂ s₃ : YamlStream)
    (h_lf : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '\n')
    (h_fold : foldQuotedNewlines acc contentIndent s₁ = .ok s₂ (.folded newAcc))
    (h_recurse : doubleQuotedScalar.collectChars contentIndent fuel
        newAcc s₂ = .ok s₃ result) :
    doubleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₃ result := by
  unfold doubleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_lf, h_fold, h_recurse]

/-! ### §8.1.7  Single-Quoted Escape Pair and Line Fold Relay

Single-quoted scalars only have one escape: `''` → `'`.
Line folding follows the same `foldQuotedNewlines` path.
-/

/--
**singleQuotedScalar.collectChars — escape pair `''` → `'`.**

When the first `'` is consumed and `option? (char '\'')` succeeds
(finding a second `'`), the loop pushes `'` and continues.
-/
theorem singleQuoted_collectChars_escape_pair
    (contentIndent fuel : Nat) (acc result : String)
    (s s₁ s₂ s₃ : YamlStream)
    (h_sq : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '\'')
    (h_opt : (option? (Parser.Char.char '\'') : YamlParser (Option Char)) s₁ = .ok s₂ (some '\''))
    (h_recurse : singleQuotedScalar.collectChars contentIndent fuel
        (acc.push '\'') s₂ = .ok s₃ result) :
    singleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₃ result := by
  unfold singleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_sq, h_opt, h_recurse]

/--
**singleQuotedScalar.collectChars — line fold on `\n`.**

Bare newline delegates to `foldQuotedNewlines` and continues.
-/
theorem singleQuoted_collectChars_linefold_lf
    (contentIndent fuel : Nat) (acc result newAcc : String)
    (s s₁ s₂ s₃ : YamlStream)
    (h_lf : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s₁ '\n')
    (h_fold : foldQuotedNewlines acc contentIndent s₁ = .ok s₂ (.folded newAcc))
    (h_recurse : singleQuotedScalar.collectChars contentIndent fuel
        newAcc s₂ = .ok s₃ result) :
    singleQuotedScalar.collectChars contentIndent (fuel + 1) acc s = .ok s₃ result := by
  unfold singleQuotedScalar.collectChars
  simp only [ParserSpecs.bind_eq, h_lf, h_fold, h_recurse]

/-! ### §8.2  Plain Scalar Specifications -/

/--
**plainScalar — relational spec (non-empty content).**

When `plainScalarContent` succeeds with non-empty content,
`plainScalar` returns `.scalar { content, style := .plain }`.
-/
theorem plainScalar_nonempty
    (s s' : YamlStream) (content : String) (inFlow : Bool) (contentIndent : Nat)
    (h_content : plainScalarContent inFlow contentIndent s = .ok s' content)
    (h_nonempty : content.isEmpty = false) :
    plainScalar inFlow contentIndent s =
      .ok s' (.scalar { content, style := .plain }) := by
  unfold plainScalar
  simp only [ParserSpecs.bind_eq, h_content]
  simp [h_nonempty]

/--
**plainScalar — relational spec (empty content, defensive path).**

When `plainScalarContent` succeeds with empty content (edge case),
`plainScalar` sets a validation error and returns `.null`.
-/
theorem plainScalar_empty
    (s s' s'' : YamlStream) (inFlow : Bool) (contentIndent : Nat)
    (h_content : plainScalarContent inFlow contentIndent s = .ok s' "")
    (h_seterr : setValidationError "internal: empty plain scalar content" s' = .ok s'' ()) :
    plainScalar inFlow contentIndent s = .ok s'' YamlValue.null := by
  unfold plainScalar
  simp (config := { decide := true }) only [ParserSpecs.bind_eq, h_content,
    String.isEmpty]
  simp only [ite_true, ParserSpecs.bind_eq, h_seterr, ParserSpecs.pure_eq]

/-! ### §8.2.1  collectPlain Loop Specifications

The `collectPlain` `where`-clause loop appears in both `plainScalarContent`
and `plainScalarSingleLine`.  These lemmas characterize its termination
conditions: fuel exhaustion, EOF, line break, and flow indicator.
-/

/--
**collectPlain — fuel-zero base case.**

When fuel is exhausted, `collectPlain` returns the accumulator unchanged.
-/
@[simp]
theorem collectPlain_zero (inFlow : Bool) (acc : String) (lws : Bool)
    (s : YamlStream) :
    plainScalarContent.collectPlain inFlow 0 acc lws s = .ok s acc := by
  unfold plainScalarContent.collectPlain
  simp only [ParserSpecs.pure_eq]

/--
**collectPlain (singleLine) — fuel-zero base case.**
-/
@[simp]
theorem collectPlain_singleLine_zero (inFlow : Bool) (acc : String) (lws : Bool)
    (s : YamlStream) :
    plainScalarSingleLine.collectPlain inFlow 0 acc lws s = .ok s acc := by
  unfold plainScalarSingleLine.collectPlain
  simp only [ParserSpecs.pure_eq]

/--
**collectPlain — EOF termination.**

When `option? (lookAhead anyToken)` returns `none` (no input left),
`collectPlain` returns the accumulator.
-/
theorem collectPlain_eof (inFlow : Bool) (fuel : Nat) (acc : String)
    (lws : Bool) (s : YamlStream)
    (h_look : (option? (lookAhead (anyToken (m := Id) : YamlParser Char))) s =
      .ok s none) :
    plainScalarContent.collectPlain inFlow (fuel + 1) acc lws s = .ok s acc := by
  unfold plainScalarContent.collectPlain
  simp only [ParserSpecs.bind_eq, h_look, ParserSpecs.pure_eq]

/--
**collectPlain (singleLine) — EOF termination.**
-/
theorem collectPlain_singleLine_eof (inFlow : Bool) (fuel : Nat)
    (acc : String) (lws : Bool) (s : YamlStream)
    (h_look : (option? (lookAhead (anyToken (m := Id) : YamlParser Char))) s =
      .ok s none) :
    plainScalarSingleLine.collectPlain inFlow (fuel + 1) acc lws s =
      .ok s acc := by
  unfold plainScalarSingleLine.collectPlain
  simp only [ParserSpecs.bind_eq, h_look, ParserSpecs.pure_eq]

/--
**collectPlain — line break termination.**

When lookAhead sees a line break character, `collectPlain` returns
the current accumulator without consuming.
-/
theorem collectPlain_linebreak (inFlow : Bool) (fuel : Nat) (acc : String)
    (lws : Bool) (s : YamlStream) (c : Char)
    (h_look : (option? (lookAhead (anyToken (m := Id) : YamlParser Char))) s =
      .ok s (some c))
    (h_lb : Parse.isLineBreak c = true) :
    plainScalarContent.collectPlain inFlow (fuel + 1) acc lws s = .ok s acc := by
  unfold plainScalarContent.collectPlain
  simp only [ParserSpecs.bind_eq, h_look, h_lb]
  simp [ParserSpecs.pure_eq]

/--
**collectPlain (singleLine) — line break termination.**
-/
theorem collectPlain_singleLine_linebreak (inFlow : Bool) (fuel : Nat)
    (acc : String) (lws : Bool) (s : YamlStream) (c : Char)
    (h_look : (option? (lookAhead (anyToken (m := Id) : YamlParser Char))) s =
      .ok s (some c))
    (h_lb : Parse.isLineBreak c = true) :
    plainScalarSingleLine.collectPlain inFlow (fuel + 1) acc lws s =
      .ok s acc := by
  unfold plainScalarSingleLine.collectPlain
  simp only [ParserSpecs.bind_eq, h_look, h_lb]
  simp [ParserSpecs.pure_eq]

/--
**collectPlain — flow indicator termination.**

In flow context (`inFlow = true`), when the lookahead character is a
flow indicator (`,`, `[`, `]`, `{`, `}`), and it is not a line break,
comment-after-space, or colon, `collectPlain` returns the accumulator
without consuming the indicator.  This is the key §7.3.3 behavior.
-/
theorem collectPlain_flow_indicator (fuel : Nat) (acc : String)
    (lws : Bool) (s : YamlStream) (c : Char)
    (h_look : (option? (lookAhead (anyToken (m := Id) : YamlParser Char))) s =
      .ok s (some c))
    (h_not_lb : Parse.isLineBreak c = false)
    (h_not_comment : (c == '#' && lws) = false)
    (h_not_colon : (c == ':') = false)
    (h_flow : Parse.isFlowIndicator c = true) :
    plainScalarContent.collectPlain true (fuel + 1) acc lws s = .ok s acc := by
  unfold plainScalarContent.collectPlain
  simp only [ParserSpecs.bind_eq, h_look, h_not_lb]
  simp [h_not_comment, h_not_colon, h_flow, ParserSpecs.pure_eq]

/--
**collectPlain (singleLine) — flow indicator termination.**
-/
theorem collectPlain_singleLine_flow_indicator (fuel : Nat) (acc : String)
    (lws : Bool) (s : YamlStream) (c : Char)
    (h_look : (option? (lookAhead (anyToken (m := Id) : YamlParser Char))) s =
      .ok s (some c))
    (h_not_lb : Parse.isLineBreak c = false)
    (h_not_comment : (c == '#' && lws) = false)
    (h_not_colon : (c == ':') = false)
    (h_flow : Parse.isFlowIndicator c = true) :
    plainScalarSingleLine.collectPlain true (fuel + 1) acc lws s =
      .ok s acc := by
  unfold plainScalarSingleLine.collectPlain
  simp only [ParserSpecs.bind_eq, h_look, h_not_lb]
  simp [h_not_comment, h_not_colon, h_flow, ParserSpecs.pure_eq]

/-! ### §8.2.2  collectLines / collectFlowLines Zero Cases -/

/--
**collectLines — fuel-zero base case.**
-/
@[simp]
theorem collectLines_zero (inFlow : Bool) (contentIndent : Nat)
    (acc : String) (s : YamlStream) :
    plainScalarContent.collectLines inFlow contentIndent 0 acc s =
      .ok s acc := by
  unfold plainScalarContent.collectLines
  simp only [ParserSpecs.pure_eq]

/--
**collectFlowLines — fuel-zero base case.**
-/
@[simp]
theorem collectFlowLines_zero (inFlow : Bool) (acc : String)
    (s : YamlStream) :
    plainScalarContent.collectFlowLines inFlow 0 acc s = .ok s acc := by
  unfold plainScalarContent.collectFlowLines
  simp only [ParserSpecs.pure_eq]

/-! ### §8.2.3  plainScalarSingleLine Auxiliary Lemmas -/

/--
**Position roundtrip for `anyToken`.**

`anyToken` only advances position fields (`startPos`, `line`, `col`) of
`YamlStream`, leaving `str`, `stopPos`, `anchorMap`, `validationError`,
and `tagHandles` unchanged.  Therefore `setPosition/getPosition` roundtrips
back to the original stream.  This is needed because `lookAhead` restores
position via `Stream.setPosition s' (Stream.getPosition s)`, which is not
definitionally `s`.
-/
theorem anyToken_setPosition_roundtrip (s s₁ : YamlStream) (c : Char)
    (h : (anyToken (m := Id) : YamlParser Char) s = .ok s₁ c) :
    Stream.setPosition s₁ (Stream.getPosition s) = s := by
  simp only [ParserSpecs.anyToken_eq] at h
  split at h
  case h_1 c' s' h_next =>
    have hs : s' = s₁ := by injection h
    subst hs
    simp only [stream_next?_eq] at h_next
    unfold YamlStream.next? at h_next
    split at h_next
    case isTrue =>
      simp only [Option.some.injEq, Prod.mk.injEq] at h_next
      obtain ⟨_, rfl⟩ := h_next
      simp only [Parser.Stream.setPosition, Parser.Stream.getPosition,
                 YamlStream.getPos]
    case isFalse =>
      exact absurd h_next (by simp)
  case h_2 =>
    exact absurd h (by simp)

/--
**Indicator characters include `-`, `?`, `:`.**

When `isIndicator c = false`, the character cannot be any of the
special plain-scalar start characters.  This lets the lookAhead
validation skip the second `if` branch entirely.
-/
theorem isIndicator_not_special (c : Char)
    (h : Parse.isIndicator c = false) :
    (c == '-' || c == '?' || c == ':') = false := by
  unfold Parse.isIndicator at h
  simp only [decide_eq_false_iff_not, List.mem_cons,
             not_or, List.mem_nil_iff] at h
  obtain ⟨h1, h2, h3, _⟩ := h
  simp only [Bool.or_eq_false_iff]
  exact ⟨⟨by simp [h1], by simp [h2]⟩, by simp [h3]⟩

/-! ### §8.2.4  plainScalarSingleLine Relational Specification -/

/--
**plainScalarSingleLine — normal-start relational spec.**

When the first character is plain-safe and not an indicator (covers the
common case of alphanumeric/special characters), `plainScalarSingleLine`
decomposes into `anyToken` + `collectPlain` with trimmed-end result.

The lookAhead validation body cannot be named in a hypothesis because
`do` notation inside `lookAhead` creates a monad application that fails
type inference outside the parser context.  Instead, we derive success
of the lookAhead from the character properties `h_safe` and `h_not_ind`.

**Coverage**: handles all first characters EXCEPT `-`, `?`, `:` which
require additional next-character validation.  A separate theorem for
those special-start characters is a §5.4.5 obligation.
-/
theorem plainScalarSingleLine_normal_start
    (inFlow : Bool) (s s₁ s₂ : YamlStream) (first : Char) (rest : String)
    (h_safe : Parse.isPlainSafe first inFlow = true)
    (h_not_ind : Parse.isIndicator first = false)
    (h_first : (anyToken (m := Id) : YamlParser Char) s = .ok s₁ first)
    (h_collect : plainScalarSingleLine.collectPlain inFlow
        (Stream.remaining s₁) (String.ofList [first]) false s₁ =
        .ok s₂ rest) :
    plainScalarSingleLine inFlow s =
      .ok s₂ (rest.trimAsciiEnd.toString) := by
  have h_roundtrip := anyToken_setPosition_roundtrip s s₁ first h_first
  have h_not_special := isIndicator_not_special first h_not_ind
  unfold plainScalarSingleLine
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq, ParserSpecs.lookAhead_eq,
             h_first, h_safe, h_not_ind, h_not_special,
             Bool.not_false, Bool.and_true, Bool.true_or,
             Bool.not_true, ite_false, Bool.false_eq_true,
             ParserSpecs.pure_eq, ParserSpecs.getStream_eq,
             h_collect, h_roundtrip]

/-! ### §8.3  Block Scalar Specification -/

/--
**blockScalar — relational spec.**

When the indicator (`|` or `>`) is parsed, header processing succeeds,
indentation is determined, and content is collected, `blockScalar`
returns the processed and chomped result.

This theorem is parametric over the intermediate results, allowing
each sub-parser to be verified independently.
-/
theorem blockScalar_spec
    (s s₁ s₂ s₃ s₄ : YamlStream) (contentIndent : Nat)
    (indicator : Char) (style : ScalarStyle)
    (explicitIndent : Option Nat) (chomp : ChompIndicator)
    (indent : Nat) (raw content : String)
    -- Phase 1: indicator parsed
    (h_indicator : (Parser.first
        [(Parser.Char.char (ε := YamlError) (m := Id) '|'),
         (Parser.Char.char (ε := YamlError) (m := Id) '>')]) s = .ok s₁ indicator)
    (h_style : style = if (indicator == '|') = true
        then ScalarStyle.literal else ScalarStyle.folded)
    -- Phase 2: header parsed
    (h_header : blockScalarHeader s₁ = .ok s₂ (explicitIndent, chomp))
    -- Phase 3: indentation determined
    (h_indent : (match explicitIndent with
      | some n => (pure (contentIndent + n - 1) : YamlParser Nat)
      | none => autoDetectIndent contentIndent) s₂ = .ok s₃ indent)
    -- Phase 4: content collected
    (h_raw : blockScalarContent indent s₃ = .ok s₄ raw)
    -- Phase 5: post-processing (pure computation)
    (h_content : content = Lean4Yaml.Parse.applyChomp
        (match style with
         | .literal => Lean4Yaml.Parse.processLiteral raw
         | .folded => Lean4Yaml.Parse.processFolded raw
         | _ => raw)
        chomp) :
    blockScalar contentIndent s =
      .ok s₄ (.scalar { content, style }) := by
  unfold blockScalar
  simp only [withErrorMessage_eq]
  subst h_style; subst h_content
  cases explicitIndent with
  | some n =>
    simp only [ParserSpecs.pure_eq] at h_indent
    obtain ⟨rfl, rfl⟩ := h_indent
    simp only [ParserSpecs.bind_eq, h_indicator, h_header,
               ParserSpecs.pure_eq, h_raw]
    rfl
  | none =>
    simp only [] at h_indent
    simp only [ParserSpecs.bind_eq, h_indicator, h_header,
               h_indent, h_raw, ParserSpecs.pure_eq]
    rfl

/-! ### §8.3.1  `blockScalarContent.collectLines` Loop Specifications

The `collectLines` `where`-clause loop in `blockScalarContent` is
fuel-bounded.  These lemmas characterize its termination and
step behavior.
-/

/--
**collectLines — fuel-zero base case.**
When fuel is exhausted, `collectLines` returns the accumulator unchanged.
-/
@[simp]
theorem blockCollectLines_zero (indent : Nat) (acc : String) (first : Bool)
    (s : YamlStream) :
    blockScalarContent.collectLines indent 0 acc first s = .ok s acc := by
  rfl

section BlockScalarContentLoopSpecs

/--
**collectLines — no line matches.**
When `option? (blockScalarLine indent first)` returns `none`,
`collectLines` returns the accumulator unchanged.  The result
stream `s_out` is whatever `option?` produces (position-restored).
-/
theorem blockCollectLines_no_match (indent : Nat) (fuel : Nat)
    (acc : String) (first : Bool) (s s_out : YamlStream)
    (h : (Parser.option? (blockScalarContent.blockScalarLine indent first)) s =
           .ok s_out none) :
    blockScalarContent.collectLines indent (fuel + 1) acc first s =
      .ok s_out acc := by
  show (do
    match ← Parser.option? (blockScalarContent.blockScalarLine indent first) with
    | some line =>
      let acc' := if first then line else acc ++ "\n" ++ line
      blockScalarContent.collectLines indent fuel acc' false
    | none =>
      return acc) s = _
  simp only [ParserSpecs.bind_eq, h, ParserSpecs.pure_eq]

/--
**collectLines — first-line step.**
When `option? (blockScalarLine)` returns `some line` and `first = true`,
the line becomes the new accumulator (no separator prepended).
-/
theorem blockCollectLines_first_step (indent : Nat) (fuel : Nat)
    (acc : String) (line : String) (s s₁ : YamlStream)
    (h : (Parser.option? (blockScalarContent.blockScalarLine indent true)) s =
           .ok s₁ (some line)) :
    blockScalarContent.collectLines indent (fuel + 1) acc true s =
      blockScalarContent.collectLines indent fuel line false s₁ := by
  show (do
    match ← Parser.option? (blockScalarContent.blockScalarLine indent true) with
    | some line =>
      let acc' := if true then line else acc ++ "\n" ++ line
      blockScalarContent.collectLines indent fuel acc' false
    | none =>
      return acc) s = _
  simp only [ParserSpecs.bind_eq, h, ite_true]

/--
**collectLines — continuation step.**
When `option? (blockScalarLine)` returns `some line` and `first = false`,
the line is concatenated with a newline separator.
-/
theorem blockCollectLines_cont_step (indent : Nat) (fuel : Nat)
    (acc : String) (line : String) (s s₁ : YamlStream)
    (h : (Parser.option? (blockScalarContent.blockScalarLine indent false)) s =
           .ok s₁ (some line)) :
    blockScalarContent.collectLines indent (fuel + 1) acc false s =
      blockScalarContent.collectLines indent fuel (acc ++ "\n" ++ line) false s₁ := by
  show (do
    match ← Parser.option? (blockScalarContent.blockScalarLine indent false) with
    | some line =>
      let acc' := if false then line else acc ++ "\n" ++ line
      blockScalarContent.collectLines indent fuel acc' false
    | none =>
      return acc) s = _
  simp only [ParserSpecs.bind_eq, h]
  rfl

end BlockScalarContentLoopSpecs

/-! ### §8.3.1a  `blockScalarLine` Branch Specifications

`blockScalarLine indent first` has three main branches:

1. **Blank line**: `option? (lookAhead newline)` succeeds → consume newline, return `""`
2. **Under-indented blank**: `isBlankUnderIndented = true` → skip whitespace,
   optional newline, return `""`
3. **Content line**: lookAhead anyToken succeeds → `consumeIndent indent` →
   `takeLineContent` → return content
-/

section BlockScalarLineSpecs

/--
**blockScalarLine — blank line.**
When `option? (lookAhead newline)` succeeds, consumes the newline and
returns the empty string.
-/
theorem blockScalarLine_blank (indent : Nat) (first : Bool)
    (s s₁ s₂ : YamlStream)
    (h_look : (option? (lookAhead newline)) s = .ok s₁ (some ()))
    (h_newline : newline s₁ = .ok s₂ ()) :
    blockScalarContent.blockScalarLine indent first s = .ok s₂ "" := by
  show (do
    match ← option? (lookAhead newline) with
    | some _ =>
      newline
      return ""
    | none =>
      let isBlankUnderIndented ← lookAhead do
        skipHWhitespace
        let col ← currentCol
        match ← option? (lookAhead newline) with
        | some _ => return decide (col < indent)
        | none => return false
      if isBlankUnderIndented then
        skipHWhitespace
        let _ ← option? newline
        return ""
      let _ ← lookAhead anyToken
      consumeIndent indent
      let content ← blockScalarContent.takeLineContent
      return content) s = _
  simp only [ParserSpecs.bind_eq, h_look, h_newline, ParserSpecs.pure_eq]

/--
**blockScalarLine — content line.**
When the blank-line lookAhead fails, the `isBlankUnderIndented` lookAhead
returns `false`, `lookAhead anyToken` succeeds, `consumeIndent` succeeds,
and `takeLineContent` returns `content`, the result is `content`.
-/
theorem blockScalarLine_content (indent : Nat) (first : Bool)
    (s s₁ s₂ s₃ s₄ s₅ : YamlStream)
    (content : String) (ch : Char)
    (h_no_blank : (option? (lookAhead newline)) s = .ok s₁ none)
    (h_not_under : (lookAhead ((do
        skipHWhitespace
        let col ← currentCol
        match ← option? (lookAhead newline) with
        | some _ => return decide (col < indent)
        | none => return false) : YamlParser Bool)) s₁ = .ok s₂ false)
    (h_lookahead : (lookAhead (anyToken : YamlParser Char)) s₂ = .ok s₃ ch)
    (h_indent : consumeIndent indent s₃ = .ok s₄ ())
    (h_content : blockScalarContent.takeLineContent s₄ = .ok s₅ content) :
    blockScalarContent.blockScalarLine indent first s = .ok s₅ content := by
  show (do
    match ← option? (lookAhead newline) with
    | some _ =>
      newline
      return ""
    | none =>
      let isBlankUnderIndented ← lookAhead do
        skipHWhitespace
        let col ← currentCol
        match ← option? (lookAhead newline) with
        | some _ => return decide (col < indent)
        | none => return false
      if isBlankUnderIndented then
        skipHWhitespace
        let _ ← option? newline
        return ""
      let _ ← lookAhead anyToken
      consumeIndent indent
      let content ← blockScalarContent.takeLineContent
      return content) s = _
  simp only [ParserSpecs.bind_eq, h_no_blank, h_not_under,
             Bool.false_eq_true, ite_false,
             h_lookahead, h_indent, h_content, ParserSpecs.pure_eq]

/--
**blockScalarLine — under-indented blank line.**
When the blank-line lookAhead fails but `isBlankUnderIndented` is `true`,
skips horizontal whitespace + optional newline and returns `""`.
-/
theorem blockScalarLine_under_indented_blank (indent : Nat) (first : Bool)
    (s s₁ s₂ s₃ s₄ : YamlStream) (nlOpt : Option Unit)
    (h_no_blank : (option? (lookAhead newline)) s = .ok s₁ none)
    (h_under : (lookAhead ((do
        skipHWhitespace
        let col ← currentCol
        match ← option? (lookAhead newline) with
        | some _ => return decide (col < indent)
        | none => return false) : YamlParser Bool)) s₁ = .ok s₂ true)
    (h_skip : skipHWhitespace s₂ = .ok s₃ ())
    (h_opt_nl : (option? newline) s₃ = .ok s₄ nlOpt) :
    blockScalarContent.blockScalarLine indent first s = .ok s₄ "" := by
  show (do
    match ← option? (lookAhead newline) with
    | some _ =>
      newline
      return ""
    | none =>
      let isBlankUnderIndented ← lookAhead do
        skipHWhitespace
        let col ← currentCol
        match ← option? (lookAhead newline) with
        | some _ => return decide (col < indent)
        | none => return false
      if isBlankUnderIndented then
        skipHWhitespace
        let _ ← option? newline
        return ""
      let _ ← lookAhead anyToken
      consumeIndent indent
      let content ← blockScalarContent.takeLineContent
      return content) s = _
  simp only [ParserSpecs.bind_eq, h_no_blank, h_under,
             ite_true, h_skip, h_opt_nl, ParserSpecs.pure_eq]

end BlockScalarLineSpecs

/-! ### §8.3.1b  `takeLineContent` Specification

`takeLineContent` is a fuel-bounded loop collecting non-linebreak characters.
It uses `for _ in [:fuel]` with `option? anyToken`, breaking on linebreak
or EOF.  The `for` desugars to `Range.forIn` with `ForInStep`.

We state relational specs rather than unfolding the `forIn` machinery.
-/

section TakeLineContentSpecs

/--
**takeLineContent — relational spec.**
Decomposes into `getStream` for fuel, then the for-loop body.
The result is a string of non-linebreak characters consumed from the stream.
-/
theorem takeLineContent_eq (s : YamlStream) :
    blockScalarContent.takeLineContent s =
      (do
        let fuel := Stream.remaining (← getStream)
        let mut acc := ""
        for _ in [:fuel] do
          match ← option? anyToken with
          | some c =>
            if Parse.isLineBreak c then
              break
            else
              acc := acc.push c
          | none => break
        return acc : YamlParser String) s := by
  rfl

end TakeLineContentSpecs

/-! ### §8.3.2  `autoDetectIndent` Specification

`autoDetectIndent` is wrapped in `lookAhead`, so it is non-consuming.
Its inner loop uses `count (token ' ')` to count leading spaces.
-/

/--
**autoDetectIndent.loop — fuel-zero base case.**
When fuel is exhausted, returns the minimum indent.
-/
@[simp]
theorem autoDetectIndent_loop_zero (minIndent : Nat) (maxBlank : Nat) (s : YamlStream) :
    autoDetectIndent.loop minIndent 0 maxBlank s = .ok s minIndent := by
  rfl

/--
**currentCol — specification.**
Returns the column number from the stream position without consuming input.
-/
@[simp]
theorem currentCol_eq (s : YamlStream) :
    currentCol s = .ok s s.col := by
  unfold currentCol
  simp only [ParserSpecs.bind_eq, ParserSpecs.getPosition_eq, ParserSpecs.pure_eq,
             Parser.Stream.getPosition, YamlStream.getPos]

section AutoDetectIndentLoopSpecs

/--
**autoDetectIndent.loop — blank line step.**
When `currentCol` returns `col`, `count (token ' ')` returns `spaces`,
and `option? newline` succeeds, the loop recurses with
`max maxBlankSpaces (col + spaces)`.
-/
theorem autoDetectIndent_loop_blank_line (minIndent fuel : Nat)
    (maxBlankSpaces col spaces : Nat)
    (s s₁ s₂ : YamlStream)
    (h_col : s.col = col)
    (h_count : (Parser.count (Parser.token (ε := YamlError) (m := Id) ' ') :
        YamlParser Nat) s = .ok s₁ spaces)
    (h_newline : (Parser.option? newline) s₁ = .ok s₂ (some ())) :
    autoDetectIndent.loop minIndent (fuel + 1) maxBlankSpaces s =
      autoDetectIndent.loop minIndent fuel (max maxBlankSpaces (col + spaces)) s₂ := by
  show (do
    let col ← currentCol
    let spaces ← count (token ' ')
    let totalCol := col + spaces
    match ← option? newline with
    | some _ =>
      autoDetectIndent.loop minIndent fuel (max maxBlankSpaces totalCol)
    | none =>
      if totalCol >= minIndent then
        if maxBlankSpaces > totalCol then
          setValidationError
            s!"block scalar has whitespace-only line ({maxBlankSpaces} spaces) exceeding content indent ({totalCol})"
        return totalCol
      else
        return minIndent) s = _
  simp only [ParserSpecs.bind_eq, currentCol_eq, h_col, h_count, h_newline]

/--
**autoDetectIndent.loop — content line at or above minIndent, no warning.**
When `option? newline` fails (content found), `totalCol >= minIndent`,
and `maxBlankSpaces <= totalCol`, returns `totalCol`.
-/
theorem autoDetectIndent_loop_content_ge (minIndent fuel : Nat)
    (maxBlankSpaces col spaces : Nat)
    (s s₁ s₂ : YamlStream)
    (h_col : s.col = col)
    (h_count : (Parser.count (Parser.token (ε := YamlError) (m := Id) ' ') :
        YamlParser Nat) s = .ok s₁ spaces)
    (h_newline : (Parser.option? newline) s₁ = .ok s₂ none)
    (h_ge : (col + spaces >= minIndent) = true)
    (h_no_warn : (maxBlankSpaces > col + spaces) = false) :
    autoDetectIndent.loop minIndent (fuel + 1) maxBlankSpaces s =
      .ok s₂ (col + spaces) := by
  show (do
    let col ← currentCol
    let spaces ← count (token ' ')
    let totalCol := col + spaces
    match ← option? newline with
    | some _ =>
      autoDetectIndent.loop minIndent fuel (max maxBlankSpaces totalCol)
    | none =>
      if totalCol >= minIndent then
        if maxBlankSpaces > totalCol then
          setValidationError
            s!"block scalar has whitespace-only line ({maxBlankSpaces} spaces) exceeding content indent ({totalCol})"
        return totalCol
      else
        return minIndent) s = _
  simp only [ParserSpecs.bind_eq, currentCol_eq, h_col, h_count, h_newline,
             h_ge, ite_true, h_no_warn]
  rfl

/--
**autoDetectIndent.loop — content line below minIndent.**
When `option? newline` fails and `totalCol < minIndent`, returns `minIndent`.
-/
theorem autoDetectIndent_loop_content_lt (minIndent fuel : Nat)
    (maxBlankSpaces col spaces : Nat)
    (s s₁ s₂ : YamlStream)
    (h_col : s.col = col)
    (h_count : (Parser.count (Parser.token (ε := YamlError) (m := Id) ' ') :
        YamlParser Nat) s = .ok s₁ spaces)
    (h_newline : (Parser.option? newline) s₁ = .ok s₂ none)
    (h_lt : (col + spaces >= minIndent) = false) :
    autoDetectIndent.loop minIndent (fuel + 1) maxBlankSpaces s =
      .ok s₂ minIndent := by
  show (do
    let col ← currentCol
    let spaces ← count (token ' ')
    let totalCol := col + spaces
    match ← option? newline with
    | some _ =>
      autoDetectIndent.loop minIndent fuel (max maxBlankSpaces totalCol)
    | none =>
      if totalCol >= minIndent then
        if maxBlankSpaces > totalCol then
          setValidationError
            s!"block scalar has whitespace-only line ({maxBlankSpaces} spaces) exceeding content indent ({totalCol})"
        return totalCol
      else
        return minIndent) s = _
  simp only [ParserSpecs.bind_eq, currentCol_eq, h_col, h_count, h_newline,
             h_lt]
  rfl

end AutoDetectIndentLoopSpecs

/-! ### §8.3.3  `consumeIndent` Specification

`consumeIndent n` checks for a leading tab (setting a validation error
if found), then consumes exactly `n` spaces via `drop n (token ' ')`.
-/

/--
**consumeIndent — no tab, drop succeeds.**
When `option? (lookAhead (token '\t'))` returns `none` (no tab at start)
and `drop n (token ' ')` succeeds, `consumeIndent` succeeds.
-/
theorem consumeIndent_no_tab (n : Nat) (s s₁ s₂ : YamlStream)
    (h_no_tab : (Parser.option? (Parser.lookAhead
        (Parser.token (ε := YamlError) (m := Id) '\t'))) s = .ok s₁ none)
    (h_drop : (Parser.drop (m := Id) n
        (Parser.token (ε := YamlError) (m := Id) ' ') : YamlParser PUnit) s₁ =
        .ok s₂ PUnit.unit) :
    consumeIndent n s = .ok s₂ () := by
  unfold consumeIndent
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq, h_no_tab, h_drop]

/--
**consumeIndent — tab detected.**
When `option? (lookAhead (token '\t'))` returns `some '\t'`,
a validation error is set, then `drop n (token ' ')` determines
the final result.  If `drop` fails (tab ≠ space), the wrapped
`withErrorMessage` catches the error.
-/
theorem consumeIndent_tab_drop_ok (n : Nat) (s s₁ s₂ s₃ : YamlStream)
    (h_tab : (Parser.option? (Parser.lookAhead
        (Parser.token (ε := YamlError) (m := Id) '\t'))) s = .ok s₁ (some '\t'))
    (h_seterr : setValidationError
        "tabs are not allowed for indentation (YAML 1.2.2 §6.1)" s₁ = .ok s₂ ())
    (h_drop : (Parser.drop (m := Id) n
        (Parser.token (ε := YamlError) (m := Id) ' ') : YamlParser PUnit) s₂ =
        .ok s₃ PUnit.unit) :
    consumeIndent n s = .ok s₃ () := by
  unfold consumeIndent
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq, h_tab, h_seterr, h_drop]

/-! ### §8.3.4  `blockScalarContent` Top-Level Specification

`blockScalarContent` wraps `getStream` (to read fuel) + `collectLines`.
-/

/--
**blockScalarContent — relational spec.**
Decomposes into `getStream` for fuel, then `collectLines` with
`fuel = Stream.remaining s`.
-/
theorem blockScalarContent_eq (indent : Nat) (s : YamlStream) :
    blockScalarContent indent s =
      blockScalarContent.collectLines indent (Stream.remaining s) "" true s := by
  unfold blockScalarContent
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq]

/-! ### §8.3.5  `autoDetectIndent` Top-Level Specification

`autoDetectIndent minIndent` wraps `lookAhead` around `getStream` + `loop`.
-/

/--
**autoDetectIndent — relational spec.**
Decomposes into `lookAhead` wrapping `getStream` for fuel, then `loop fuel 0`.
-/
theorem autoDetectIndent_eq (minIndent : Nat) (s : YamlStream) :
    autoDetectIndent minIndent s =
      (lookAhead (getStream >>= fun stream =>
        autoDetectIndent.loop minIndent (Stream.remaining stream) 0)) s := by
  unfold autoDetectIndent
  rfl

/-! ### §8.3.6  `processFolded` Extra Specifications -/

/--
**processFolded — single line.**
A raw string with no newline is returned as-is (the `first = true` base case).
-/
theorem processFolded_single_line (s : String)
    (h_split : s.splitOn "\n" = [s]) :
    processFolded s = s := by
  unfold processFolded
  simp only [h_split, processFolded.go, ite_true]

/--
**processFolded — decomposition.**
`processFolded raw` delegates to `processFolded.go (raw.splitOn "\n") "" true`.
-/
theorem processFolded_eq (raw : String) :
    processFolded raw = processFolded.go (raw.splitOn "\n") "" true := by
  unfold processFolded
  rfl

/-! ### §8.3.7  `blockScalar` Style-Dispatch Specifications -/

/--
**blockScalar — literal style processing identity.**
When the indicator is `|`, `processLiteral raw = raw`.  Combined with
`blockScalar_spec`, this shows the literal pipeline preserves raw content
before chomping.
-/
theorem blockScalar_literal_processing (raw : String) :
    (match ScalarStyle.literal with
     | .literal => processLiteral raw
     | .folded => processFolded raw
     | _ => raw) = raw := by
  rfl

/--
**blockScalar — folded style processing.**
When the indicator is `>`, `processFolded raw` is applied.
-/
theorem blockScalar_folded_processing (raw : String) :
    (match ScalarStyle.folded with
     | .literal => processLiteral raw
     | .folded => processFolded raw
     | _ => raw) = processFolded raw := by
  rfl

/-! ### §8.4  Block Collection Specifications -/

/--
**blockSequence — relational spec.**

When the fuel wrapper delegates to `blockSequenceImpl` and that
implementation succeeds, `blockSequence` returns the same result.
-/
theorem blockSequence_spec
    (s s' : YamlStream) (result : Option YamlValue) (minIndent : Nat)
    (h_impl : blockSequenceImpl (4 * Stream.remaining s + 4) minIndent s = .ok s' result) :
    blockSequence minIndent s = .ok s' result := by
  unfold blockSequence
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq, h_impl]

/--
**blockMapping — relational spec.**

When the fuel wrapper delegates to `blockMappingImpl` and that
implementation succeeds, `blockMapping` returns the same result.
-/
theorem blockMapping_spec
    (s s' : YamlStream) (result : Option YamlValue) (minIndent : Nat)
    (h_impl : blockMappingImpl (4 * Stream.remaining s + 4) minIndent s = .ok s' result) :
    blockMapping minIndent s = .ok s' result := by
  unfold blockMapping
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq, h_impl]

/-! ### §8.5  Flow Collection Specifications -/

/--
**flowSequence — relational spec.**

When the fuel wrapper delegates to `flowSequenceImpl` and that
implementation succeeds, `flowSequence` returns the same result.
-/
theorem flowSequence_spec
    (s s' : YamlStream) (result : YamlValue) (minIndent : Nat)
    (h_impl : flowSequenceImpl (4 * Stream.remaining s + 4) minIndent s = .ok s' result) :
    flowSequence minIndent s = .ok s' result := by
  unfold flowSequence
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq, h_impl]

/--
**flowMapping — relational spec.**

When the fuel wrapper delegates to `flowMappingImpl` and that
implementation succeeds, `flowMapping` returns the same result.
-/
theorem flowMapping_spec
    (s s' : YamlStream) (result : YamlValue) (minIndent : Nat)
    (h_impl : flowMappingImpl (4 * Stream.remaining s + 4) minIndent s = .ok s' result) :
    flowMapping minIndent s = .ok s' result := by
  unfold flowMapping
  simp only [ParserSpecs.bind_eq, ParserSpecs.getStream_eq, h_impl]

/-! ### §8.6  Flow Collection Empty-Case Specifications

The empty cases (`[]`, `{}`) are fully provable with just token-level
lemmas — no fuel unrolling needed.
-/

/--
**flowSequenceImpl — empty sequence `[]`.**

When `[` is consumed, whitespace is skipped, and `]` is found immediately,
the result is an empty flow sequence.
-/
theorem flowSequenceImpl_empty
    (fuel : Nat) (s s₁ s₂ s₃ : YamlStream) (minIndent : Nat)
    (h_open : (Parser.Char.char (ε := YamlError) (m := Id) '[') s = .ok s₁ '[')
    (h_ws : flowWhitespace minIndent s₁ = .ok s₂ ())
    (h_close : (option? (Parser.Char.char (ε := YamlError) (m := Id) ']')) s₂ =
      .ok s₃ (some ']')) :
    flowSequenceImpl (fuel + 1) minIndent s =
      .ok s₃ (.sequence .flow #[]) := by
  unfold flowSequenceImpl
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_open, h_ws, h_close, ParserSpecs.pure_eq]

/--
**flowMappingImpl — empty mapping `{}`.**

When `{` is consumed, whitespace is skipped, and `}` is found immediately,
the result is an empty flow mapping.
-/
theorem flowMappingImpl_empty
    (fuel : Nat) (s s₁ s₂ s₃ : YamlStream) (minIndent : Nat)
    (h_open : (Parser.Char.char (ε := YamlError) (m := Id) '{') s = .ok s₁ '{')
    (h_ws : flowWhitespace minIndent s₁ = .ok s₂ ())
    (h_close : (option? (Parser.Char.char (ε := YamlError) (m := Id) '}')) s₂ =
      .ok s₃ (some '}')) :
    flowMappingImpl (fuel + 1) minIndent s =
      .ok s₃ (.mapping .flow #[]) := by
  unfold flowMappingImpl
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_open, h_ws, h_close, ParserSpecs.pure_eq]

/-! ### §8.7  Collection Fuel-Zero Specifications

When fuel is exhausted, every fuel-bounded collection parser returns its
default value without consuming input (pure `none` / `acc` / `#[]`).
These provide uniform base-case coverage for fuel induction.
-/

/-- `flowSequenceImpl 0` returns an empty sequence without consuming input. -/
@[simp]
theorem flowSequenceImpl_zero (minIndent : Nat) (s : YamlStream) :
    flowSequenceImpl 0 minIndent s = .ok s (.sequence .flow #[]) := by
  unfold flowSequenceImpl
  simp [ParserSpecs.pure_eq]

/-- `flowMappingImpl 0` returns an empty mapping without consuming input. -/
@[simp]
theorem flowMappingImpl_zero (minIndent : Nat) (s : YamlStream) :
    flowMappingImpl 0 minIndent s = .ok s (.mapping .flow #[]) := by
  unfold flowMappingImpl
  simp [ParserSpecs.pure_eq]

/-- `flowSequenceItemsImpl 0` returns the accumulator. -/
@[simp]
theorem flowSequenceItemsImpl_zero (acc : Array YamlValue) (minIndent : Nat)
    (s : YamlStream) :
    flowSequenceItemsImpl 0 acc minIndent s = .ok s acc := by
  unfold flowSequenceItemsImpl
  simp [ParserSpecs.pure_eq]

/-- `flowMappingEntriesImpl 0` returns the accumulator. -/
@[simp]
theorem flowMappingEntriesImpl_zero
    (acc : Array (YamlValue × YamlValue)) (minIndent : Nat) (s : YamlStream) :
    flowMappingEntriesImpl 0 acc minIndent s = .ok s acc := by
  unfold flowMappingEntriesImpl
  simp [ParserSpecs.pure_eq]

/-- `flowMappingEntryImpl 0` returns `(.null, .null)`. -/
@[simp]
theorem flowMappingEntryImpl_zero (minIndent : Nat) (s : YamlStream) :
    flowMappingEntryImpl 0 minIndent s = .ok s (.null, .null) := by
  unfold flowMappingEntryImpl
  simp [ParserSpecs.pure_eq]

/-- `blockSequenceImpl 0` returns `none` without consuming input. -/
@[simp]
theorem blockSequenceImpl_zero (minIndent : Nat) (s : YamlStream) :
    blockSequenceImpl 0 minIndent s = .ok s none := by
  unfold blockSequenceImpl
  simp [ParserSpecs.pure_eq]

/-- `blockMappingImpl 0` returns `none` without consuming input. -/
@[simp]
theorem blockMappingImpl_zero (minIndent : Nat) (s : YamlStream) :
    blockMappingImpl 0 minIndent s = .ok s none := by
  unfold blockMappingImpl
  simp [ParserSpecs.pure_eq]

/-- `blockSequenceItemsImpl 0` returns the accumulator. -/
@[simp]
theorem blockSequenceItemsImpl_zero (seqIndent : Nat)
    (acc : Array YamlValue) (s : YamlStream) :
    blockSequenceItemsImpl 0 seqIndent acc s = .ok s acc := by
  unfold blockSequenceItemsImpl
  simp [ParserSpecs.pure_eq]

/-- `blockMappingEntriesImpl 0` returns the accumulator. -/
@[simp]
theorem blockMappingEntriesImpl_zero (mapIndent : Nat)
    (acc : Array (YamlValue × YamlValue)) (s : YamlStream) :
    blockMappingEntriesImpl 0 mapIndent acc s = .ok s acc := by
  unfold blockMappingEntriesImpl
  simp [ParserSpecs.pure_eq]

/-! ### §8.8  Character Predicate Specifications

Concrete evaluation lemmas for the pure `Bool`-valued character
predicates.  These serve as `simp` fuel when reasoning about parser
branching on specific characters.
-/

/-- Line feed is a line break. -/
@[simp] theorem isLineBreak_lf : Parse.isLineBreak '\n' = true := by native_decide

/-- Carriage return is a line break. -/
@[simp] theorem isLineBreak_cr : Parse.isLineBreak '\r' = true := by native_decide

/-- A normal letter is not a line break. -/
@[simp] theorem isLineBreak_letter : Parse.isLineBreak 'a' = false := by native_decide

/-- Space is whitespace. -/
@[simp] theorem isWhiteSpace_space : Parse.isWhiteSpace ' ' = true := by native_decide

/-- Tab is whitespace. -/
@[simp] theorem isWhiteSpace_tab : Parse.isWhiteSpace '\t' = true := by native_decide

/-- A normal letter is not whitespace. -/
@[simp] theorem isWhiteSpace_letter : Parse.isWhiteSpace 'a' = false := by native_decide

/-- Comma is a flow indicator. -/
@[simp] theorem isFlowIndicator_comma : Parse.isFlowIndicator ',' = true := by native_decide

/-- Open bracket is a flow indicator. -/
@[simp] theorem isFlowIndicator_lbracket : Parse.isFlowIndicator '[' = true := by native_decide

/-- Close bracket is a flow indicator. -/
@[simp] theorem isFlowIndicator_rbracket : Parse.isFlowIndicator ']' = true := by native_decide

/-- Open brace is a flow indicator. -/
@[simp] theorem isFlowIndicator_lbrace : Parse.isFlowIndicator '{' = true := by native_decide

/-- Close brace is a flow indicator. -/
@[simp] theorem isFlowIndicator_rbrace : Parse.isFlowIndicator '}' = true := by native_decide

/-- A normal letter is not a flow indicator. -/
@[simp] theorem isFlowIndicator_letter : Parse.isFlowIndicator 'a' = false := by native_decide

/-- A normal letter is plain-safe in block context. -/
@[simp] theorem isPlainSafe_letter_block : Parse.isPlainSafe 'a' false = true := by native_decide

/-- A normal letter is plain-safe in flow context. -/
@[simp] theorem isPlainSafe_letter_flow : Parse.isPlainSafe 'a' true = true := by native_decide

/-- A newline is not plain-safe. -/
@[simp] theorem isPlainSafe_newline : Parse.isPlainSafe '\n' false = false := by native_decide

/-- A comma is not plain-safe in flow context. -/
@[simp] theorem isPlainSafe_comma_flow : Parse.isPlainSafe ',' true = false := by native_decide

/-- A comma IS plain-safe in block context. -/
@[simp] theorem isPlainSafe_comma_block : Parse.isPlainSafe ',' false = true := by native_decide

/-- A normal letter can start a plain scalar (with or without next char). -/
@[simp] theorem canStartPlainScalar_letter :
    Parse.canStartPlainScalar 'a' none = true := by native_decide

/-- '-' can start a plain scalar when followed by a non-space char. -/
@[simp] theorem canStartPlainScalar_dash_alpha :
    Parse.canStartPlainScalar '-' (some 'a') = true := by native_decide

/-- '-' cannot start a plain scalar when followed by nothing. -/
@[simp] theorem canStartPlainScalar_dash_none :
    Parse.canStartPlainScalar '-' none = false := by native_decide

/-- '-' cannot start a plain scalar when followed by a space. -/
@[simp] theorem canStartPlainScalar_dash_space :
    Parse.canStartPlainScalar '-' (some ' ') = false := by native_decide

/-! ### §8.9  Remaining Fuel-Zero Specifications

Additional fuel-exhaustion base cases for block/flow parser functions
not covered in §8.7.
-/

/-- `dispatchByCharImpl 0` returns `.noMatch` without consuming input. -/
@[simp]
theorem dispatchByCharImpl_zero (contentIndent scalarIndent : Nat) (s : YamlStream) :
    dispatchByCharImpl 0 contentIndent scalarIndent s =
      .ok s .noMatch := by
  unfold dispatchByCharImpl
  simp [ParserSpecs.pure_eq]

/-- `blockValueImpl 0` returns `none` without consuming input. -/
@[simp]
theorem blockValueImpl_zero (minIndent propertyMinIndent : Nat) (s : YamlStream) :
    blockValueImpl 0 minIndent propertyMinIndent s = .ok s none := by
  unfold blockValueImpl
  simp [ParserSpecs.pure_eq]

/-- `blockValueSameLineImpl 0` returns `.null` without consuming input. -/
@[simp]
theorem blockValueSameLineImpl_zero (startCol contentIndent : Nat) (s : YamlStream) :
    blockValueSameLineImpl 0 startCol contentIndent s = .ok s .null := by
  unfold blockValueSameLineImpl
  simp [ParserSpecs.pure_eq]

/-- `blockMappingEntryImpl 0` returns `(.null, .null)`. -/
@[simp]
theorem blockMappingEntryImpl_zero (mapIndent : Nat) (s : YamlStream) :
    blockMappingEntryImpl 0 mapIndent s = .ok s (.null, .null) := by
  unfold blockMappingEntryImpl
  simp [ParserSpecs.pure_eq]

/-- `blockMappingKeyImpl 0` returns `.null` without consuming input. -/
@[simp]
theorem blockMappingKeyImpl_zero (s : YamlStream) :
    blockMappingKeyImpl 0 s = .ok s .null := by
  unfold blockMappingKeyImpl
  simp [ParserSpecs.pure_eq]

/-- `detectMappingKeyImpl 0` returns `false` without consuming input. -/
@[simp]
theorem detectMappingKeyImpl_zero (inFlow : Bool) (s : YamlStream) :
    detectMappingKeyImpl 0 inFlow s = .ok s false := by
  unfold detectMappingKeyImpl
  simp [ParserSpecs.pure_eq]

/-- `flowValueImpl 0` returns `.null` without consuming input. -/
@[simp]
theorem flowValueImpl_zero (minIndent : Nat) (s : YamlStream) :
    flowValueImpl 0 minIndent s = .ok s .null := by
  unfold flowValueImpl
  simp [ParserSpecs.pure_eq]

/-! ### §8.10  Block Collection Under-Indented Specifications

When the detected indentation is below `minIndent`, block sequence/mapping
return `none` immediately — the content belongs to a parent structure.
-/

/--
**blockSequenceImpl — under-indented termination.**

After consuming blank lines, if the current column is less than
`minIndent`, the sequence returns `none`.
-/
theorem blockSequenceImpl_under_indented
    (fuel minIndent : Nat) (s s₁ : YamlStream)
    (h_skip : skipBlankLines s = .ok s₁ ())
    (h_lt : s₁.col < minIndent) :
    blockSequenceImpl (fuel + 1) minIndent s = .ok s₁ none := by
  unfold blockSequenceImpl
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_skip, currentCol_eq]
  simp [h_lt]

/--
**blockMappingImpl — under-indented termination.**

After consuming blank lines, if the current column is less than
`minIndent`, the mapping returns `none`.
-/
theorem blockMappingImpl_under_indented
    (fuel minIndent : Nat) (s s₁ : YamlStream)
    (h_skip : skipBlankLines s = .ok s₁ ())
    (h_lt : s₁.col < minIndent) :
    blockMappingImpl (fuel + 1) minIndent s = .ok s₁ none := by
  unfold blockMappingImpl
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_skip, currentCol_eq]
  simp [h_lt]

/-! ### §8.11  Additional Character Predicate Specifications -/

/-- Dash is an indicator. -/
@[simp] theorem isIndicator_dash : Parse.isIndicator '-' = true := by native_decide

/-- Question mark is an indicator. -/
@[simp] theorem isIndicator_question : Parse.isIndicator '?' = true := by native_decide

/-- Colon is an indicator. -/
@[simp] theorem isIndicator_colon : Parse.isIndicator ':' = true := by native_decide

/-- Hash is an indicator. -/
@[simp] theorem isIndicator_hash : Parse.isIndicator '#' = true := by native_decide

/-- A normal letter is not an indicator. -/
@[simp] theorem isIndicator_letter : Parse.isIndicator 'a' = false := by native_decide

/-- A digit is not an indicator. -/
@[simp] theorem isIndicator_digit : Parse.isIndicator '0' = false := by native_decide

/-- `isForbiddenPlainStart` equals `isIndicator`. -/
theorem isForbiddenPlainStart_eq (c : Char) :
    Parse.isForbiddenPlainStart c = Parse.isIndicator c := by
  unfold Parse.isForbiddenPlainStart
  rfl

/-- A letter is a valid anchor character. -/
@[simp] theorem isAnchorChar_letter : Parse.isAnchorChar 'a' = true := by native_decide

/-- A digit is a valid anchor character. -/
@[simp] theorem isAnchorChar_digit : Parse.isAnchorChar '0' = true := by native_decide

/-- A comma is not a valid anchor character (flow indicator). -/
@[simp] theorem isAnchorChar_comma : Parse.isAnchorChar ',' = false := by native_decide

/-- Space is not a valid anchor character. -/
@[simp] theorem isAnchorChar_space : Parse.isAnchorChar ' ' = false := by native_decide

/-! ## §9  Summary

### Proved Specifications

| # | Theorem | Section | Technique |
|---|---------|---------|-----------|
| 1 | `withErrorMessage_eq` | §1 | `dsimp + cases` |
| 2 | `withErrorMessage_of_ok` | §1 | `simp` on success |
| 3 | `throwErrorWithMessage_eq` | §1 | `simp` |
| 4 | `stream_next?_eq` | §2 | `rfl` |
| 5 | `YamlStream_next?_some` | §2 | `simp` on bounds |
| 6 | `YamlStream_next?_none` | §2 | `simp` on bounds |
| 7 | `yamlAnyToken_some` | §3 | Specialize anyToken_eq |
| 8 | `yamlAnyToken_none` | §3 | Specialize anyToken_eq |
| 9 | `yamlTokenFilter_ok` | §3 | Specialize tokenFilter_eq |
| 10 | `yamlTokenFilter_fail` | §3 | Specialize tokenFilter_eq |
| 11 | `yamlToken_ok` | §3 | Lift tokenFilter |
| 12 | `yamlChar_ok` | §3 | withErrorMessage transparency |
| 13 | `yamlOption?_some` | §4.1 | Specialize option? |
| 14 | `yamlOption?_none` | §4.1 | Specialize option? |
| 15 | `yamlLookAhead_ok` | §4.2 | Specialize lookAhead |
| 16 | `lookupAnchor_eq` | §5 | bind + getStream + pure |
| 17 | `parseAlias_found` | §5 | Full pipeline simp |
| 18 | `parseAlias_not_found` | §5 | Full pipeline simp |
| 19 | `setValidationError_fresh` | §6 | unfold + simp + rfl |
| 20 | `setValidationError_already` | §6 | unfold + simp + rfl |
| 21 | `processLiteral_eq` | §7 | rfl |
| 22 | `applyChomp_keep` | §7 | rfl |
| 23 | `singleQuotedScalar_spec` | §8.1 | Relational: unfold + simp |
| 24 | `doubleQuotedScalar_spec` | §8.1 | Relational: unfold + simp |
| 25 | `plainScalar_nonempty` | §8.2 | Relational: unfold + simp |
| 26 | `plainScalar_empty` | §8.2 | Relational: unfold + simp |
| 27 | `blockScalar_spec` | §8.3 | Relational: 5-phase pipeline |
| 28 | `blockSequence_spec` | §8.4 | Fuel wrapper transparency |
| 29 | `blockMapping_spec` | §8.4 | Fuel wrapper transparency |
| 30 | `flowSequence_spec` | §8.5 | Fuel wrapper transparency |
| 31 | `flowMapping_spec` | §8.5 | Fuel wrapper transparency |
| 32 | `flowSequenceImpl_empty` | §8.6 | Empty-case: token only |
| 33 | `flowMappingImpl_empty` | §8.6 | Empty-case: token only |
| 34 | `collectPlain_zero` | §8.2.1 | Loop: fuel=0 → acc |
| 35 | `collectPlain_singleLine_zero` | §8.2.1 | Loop: fuel=0 → acc |
| 36 | `collectPlain_eof` | §8.2.1 | Loop: EOF → acc |
| 37 | `collectPlain_singleLine_eof` | §8.2.1 | Loop: EOF → acc |
| 38 | `collectPlain_linebreak` | §8.2.1 | Loop: linebreak → acc |
| 39 | `collectPlain_singleLine_linebreak` | §8.2.1 | Loop: linebreak → acc |
| 40 | `collectPlain_flow_indicator` | §8.2.1 | Loop: flow indicator → acc |
| 41 | `collectPlain_singleLine_flow_indicator` | §8.2.1 | Loop: flow indicator → acc |
| 42 | `collectLines_zero` | §8.2.2 | Loop: fuel=0 → acc |
| 43 | `collectFlowLines_zero` | §8.2.2 | Loop: fuel=0 → acc |
| 44 | `anyToken_setPosition_roundtrip` | §8.2.3 | Position roundtrip |
| 45 | `isIndicator_not_special` | §8.2.3 | Indicator → not special |
| 46 | `plainScalarSingleLine_normal_start` | §8.2.4 | Relational: normal start |
| 47 | `applyChomp_strip` | §7 | `rfl` |
| 48 | `applyChomp_clip` | §7 | `rfl` |
| 49 | `processFolded_go_nil` | §7.1 | `unfold; rfl` |
| 50 | `processFolded_go_singleton_first` | §7.1 | `unfold; simp` |
| 51 | `processFolded_go_singleton_nonempty` | §7.1 | `unfold; simp [h]` |
| 52 | `processFolded_go_singleton_empty` | §7.1 | `unfold; simp [String.isEmpty]` |
| 53 | `blockCollectLines_zero` | §8.3.1 | `rfl` |
| 54 | `blockCollectLines_no_match` | §8.3.1 | `show` + `simp` |
| 55 | `blockCollectLines_first_step` | §8.3.1 | `show` + `simp [ite_true]` |
| 56 | `blockCollectLines_cont_step` | §8.3.1 | `show` + `simp` + `rfl` |
| 57 | `autoDetectIndent_loop_zero` | §8.3.2 | `rfl` |
| 58 | `currentCol_eq` | §8.3.2 | `unfold; simp` |
| 59 | `autoDetectIndent_loop_blank_line` | §8.3.2 | `show` + `simp` |
| 60 | `autoDetectIndent_loop_content_ge` | §8.3.2 | `show` + `simp` + `rfl` |
| 61 | `autoDetectIndent_loop_content_lt` | §8.3.2 | `show` + `simp` + `rfl` |
| 62 | `consumeIndent_no_tab` | §8.3.3 | `unfold; simp` |
| 63 | `consumeIndent_tab_drop_ok` | §8.3.3 | `unfold; simp` |
| 64 | `blockScalarContent_eq` | §8.3.4 | `unfold; simp` |
| 65 | `blockScalarLine_blank` | §8.3.1a | `show` + `simp` |
| 66 | `blockScalarLine_content` | §8.3.1a | `show` + `simp [Bool.false_eq_true]` |
| 67 | `blockScalarLine_under_indented_blank` | §8.3.1a | `show` + `simp [ite_true]` |
| 68 | `autoDetectIndent_eq` | §8.3.5 | `unfold; rfl` |
| 69 | `processFolded_single_line` | §8.3.6 | `unfold; simp` |
| 70 | `processFolded_go_cons_first` | §7.1 | `show/rw` + cons_ne_nil |
| 71 | `processFolded_go_cons_empty` | §7.1 | `show/rw` + cons_ne_nil |
| 72 | `processFolded_go_cons_more_indented` | §7.1 | `show/rw` + cons_ne_nil |
| 73 | `processFolded_go_cons_fold` | §7.1 | `show/rw` + cons_ne_nil |
| 74 | `takeLineContent_eq` | §8.3.1b | `rfl` |
| 75 | `processFolded_eq` | §8.3.6 | `rfl` |
| 76 | `blockScalar_literal_processing` | §8.3.7 | `rfl` |
| 77 | `blockScalar_folded_processing` | §8.3.7 | `rfl` |
| 78 | `flowSequenceImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 79 | `flowMappingImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 80 | `flowSequenceItemsImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 81 | `flowMappingEntriesImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 82 | `flowMappingEntryImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 83 | `blockSequenceImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 84 | `blockMappingImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 85 | `blockSequenceItemsImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 86 | `blockMappingEntriesImpl_zero` | §8.7 | `unfold; simp [pure_eq]` |
| 87–107 | `isLineBreak_*`, `isWhiteSpace_*`, etc. | §8.8 | `native_decide` |
| 108 | `dispatchByCharImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 109 | `blockValueImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 110 | `blockValueSameLineImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 111 | `blockMappingEntryImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 112 | `blockMappingKeyImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 113 | `detectMappingKeyImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 114 | `flowValueImpl_zero` | §8.9 | `unfold; simp [pure_eq]` |
| 115 | `blockSequenceImpl_under_indented` | §8.10 | `unfold; simp [h_lt]` |
| 116 | `blockMappingImpl_under_indented` | §8.10 | `unfold; simp [h_lt]` |
| 117–127 | `isIndicator_*`, `isAnchorChar_*`, etc. | §8.11 | `native_decide` |
| 128 | `isForbiddenPlainStart_eq` | §8.11 | `unfold; rfl` |

### Remaining Obligations (deferred to §5.4.5)

The relational specs above reduce per-parser correctness to sub-parser
correctness.  The remaining obligations are:

1. **Special-start plain scalar** — `plainScalarSingleLine` when the
   first character is `-`, `?`, or `:` (requires next-character validation
   in the lookAhead body).

2. **Fuel-bounded loop induction** — `collectChars` (quoted),
   `blockScalarContent`, `blockSequenceItemsImpl`, `flowSequenceItemsImpl`, etc.
   Each requires structural induction on the fuel parameter.

3. **Mutual recursion** — `blockValueImpl` dispatches to `blockSequence`,
   `blockMapping`, scalars; similarly `flowValueImpl`.  These form the
   cross-cutting obligations that connect all per-parser specs.
-/

end Lean4Yaml.Proofs.PerParserSpecs
