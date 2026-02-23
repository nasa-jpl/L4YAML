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

/-! ## §6  Per-Parser Specification Theorem Statements

One correctness theorem per `ValidNode` constructor.  These state that
when the input stream encodes a well-formed YAML node, the corresponding
parser succeeds and produces `toYamlValue node`.

### Proof Status

| # | Constructor | Parser | Status |
|---|-------------|--------|--------|
| 1 | `plainScalarBlock` | `plainScalar false` | planned — loop |
| 2 | `plainScalarFlow` | `plainScalar true` | planned — loop |
| 3 | `singleQuoted` | `singleQuotedScalar` | planned — loop |
| 4 | `doubleQuoted` | `doubleQuotedScalar` | planned — loop + escapes |
| 5 | `literalScalar` | `blockScalar` | planned — loop + indent |
| 6 | `foldedScalar` | `blockScalar` | planned — loop + fold |
| 7 | `blockSeq` | `blockSequence` | planned — mutual recursion |
| 8 | `blockMap` | `blockMapping` | planned — mutual recursion |
| 9 | `flowSeq` | `flowSequence` | planned — mutual recursion |
| 10 | `flowMap` | `flowMapping` | planned — mutual recursion |

All require fuel-sufficiency reasoning (§5.4.4) and loop unrolling.
The intermediate lemmas above (§1–§5) are prerequisites for all 10.
-/

end Lean4Yaml.Proofs.PerParserSpecs
