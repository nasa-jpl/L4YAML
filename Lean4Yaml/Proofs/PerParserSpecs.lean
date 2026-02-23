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
Theorems marked `sorry` are explicitly labeled as work-in-progress.
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
| `plainScalarBlock` | WIP — safe-char predicate |
| `plainScalarFlow` | WIP — flow indicator exclusion |
| `literalScalar` | planned |
| `foldedScalar` | planned |
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
IS in the stream's anchor map, `parseAlias` returns the stored value.
-/
theorem parseAlias_found (s s₁ s₂ : YamlStream) (name : String) (val : YamlValue)
    (h_star : (Parser.Char.char (ε := YamlError) (m := Id) '*') s = .ok s₁ '*')
    (h_name : anchorName s₁ = .ok s₂ name)
    (h_find : AnchorMap.find? s₂.anchorMap name = some val) :
    parseAlias s = .ok s₂ val := by
  unfold parseAlias
  simp only [withErrorMessage_eq, ParserSpecs.bind_eq,
             h_star, h_name, lookupAnchor_eq, h_find, ParserSpecs.pure_eq]

/--
**parseAlias — success, anchor undefined.**

When `char '*'` succeeds, `anchorName` parses the name, but the anchor
is NOT in the map, `parseAlias` returns `YamlValue.null` and sets a
validation error.
-/
theorem parseAlias_not_found (s s₁ s₂ : YamlStream) (name : String)
    (h_star : (Parser.Char.char (ε := YamlError) (m := Id) '*') s = .ok s₁ '*')
    (h_name : anchorName s₁ = .ok s₂ name)
    (h_find : AnchorMap.find? s₂.anchorMap name = none)
    -- setValidationError post-condition:
    (s₃ : YamlStream)
    (h_seterr : setValidationError s!"undefined anchor: *{name}" s₂ = .ok s₃ ()) :
    parseAlias s = .ok s₃ YamlValue.null := by
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

### Remaining Obligations (deferred to §5.4.4)

The relational specs above reduce per-parser correctness to sub-parser
correctness.  The remaining obligations are:

1. **Fuel-bounded loop specs** — `collectChars` (quoted), `collectPlain` (plain),
   `blockScalarContent`, `blockSequenceItemsImpl`, `flowSequenceItemsImpl`, etc.
   Each requires structural induction on the fuel parameter.

2. **Fuel sufficiency** — bounding the fuel needed as a function of input length.
   The `4 * Stream.remaining + 4` factor for collections needs justification.

3. **Mutual recursion** — `blockValueImpl` dispatches to `blockSequence`,
   `blockMapping`, scalars; similarly `flowValueImpl`.  These form the
   cross-cutting obligations that connect all per-parser specs.
-/

end Lean4Yaml.Proofs.PerParserSpecs
