/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Parser
import Lean4Yaml.Stream

/-!
# Combinator Specifications  (Step 5.4.2)

Foundation lemmas that unfold lean4-parser combinator definitions into
concrete `Parser.Result` expressions.  lean4-parser ships **zero** theorems
or `@[simp]` annotations, so every lemma here is proved from first
principles by unfolding the function definitions.

## Scope

All lemmas are stated for `Parser ε σ τ α` (i.e., `ParserT ε σ τ Id α`),
which is `σ → Parser.Result ε σ α`.  Since `Id` is the identity monad
(`pure = id`, `bind x f = f x`), all monadic plumbing reduces away.

**Universe note**: All type variables use plain `Type` (= `Type 0`).
Universe-polymorphic `Type u` fails because `Parser.Stream` and
`Parser.Error` have independent universe parameters that cannot unify
with a single `u`.  All YAML parser types are in `Type 0` anyway.

## Proof technique

The lean4-parser type class instances generate internal `match` auxiliary
functions (e.g., `instMonadParserT.match_1`).  Theorem statements also
generate `match` auxiliaries (e.g., `theorem_name.match_1`).  These are
*different named* functions and are NOT definitionally equal, so `rfl`
fails for any statement that mentions `match` on both sides.

The solution is:
1. `simp only [...]` / `dsimp only [...]` — unfold definitions using their
   equation lemmas (not the kernel's definitional equality)
2. `cases <discriminant> <;> rfl` — eliminate the `match` discriminant
   so that both sides reduce to the same constructor application

## Structure

### §1  Monad Primitives
- `pure_eq`, `bind_eq`, `map_eq`

### §2  Stream / Position Access
- `getStream_eq`, `setStream_eq`, `getPosition_eq`, `setPosition_eq`

### §3  Error Primitives
- `throw_eq`, `tryCatch_eq`, `throwUnexpected_eq`, `throwUnexpected_some_eq`

### §4  Backtracking Combinators
- `withBacktracking_eq`, `orElse_eq`, `lookAhead_eq`

### §5  Option Family
- `eoption_eq`, `option_question_eq`

### §6  Lookahead
- `notFollowedBy_eq`

### §7  Token Primitives
- `tokenCore_eq`, `anyToken_eq`, `tokenFilter_eq`

## Zero Axioms

All lemmas are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.ParserSpecs

open Parser

variable {ε σ : Type} {τ : Type} {α β : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

/-! ## §1  Monad Primitives

The `Monad (ParserT ε σ τ m)` instance defines `pure`, `bind`, `map`,
`seq`, `seqLeft`, `seqRight` as explicit lambda-over-stream functions.
For `m = Id` all inner monadic operations (`return`, `>>=`) reduce to
identity / function application.
-/

/--
`pure x` applied to stream `s` returns `.ok s x`.

Unfolds: ParserT.Monad.pure → Id.pure
-/
@[simp]
theorem pure_eq (x : α) (s : σ) :
    (pure x : Parser ε σ τ α) s = .ok s x := rfl

/--
`p >>= f` applied to stream `s` pattern-matches on `p s`.

Unfolds: ParserT.Monad.bind → Id.bind → match on Result
-/
@[simp]
theorem bind_eq (p : Parser ε σ τ α) (f : α → Parser ε σ τ β) (s : σ) :
    (p >>= f) s =
      match p s with
      | .ok s' a => f a s'
      | .error s' e => .error s' e := by
  simp only [bind, Bind.bind, pure, Pure.pure]; cases p s <;> rfl

/--
`f <$> p` applied to stream `s` maps `f` over the success value.

Unfolds: ParserT.Monad.map → Id.bind
-/
@[simp]
theorem map_eq (f : α → β) (p : Parser ε σ τ α) (s : σ) :
    (f <$> p) s =
      match p s with
      | .ok s' a => .ok s' (f a)
      | .error s' e => .error s' e := by
  simp only [Functor.map, bind, Bind.bind, pure, Pure.pure]; cases p s <;> rfl

/-! ## §2  Stream / Position Access

`getStream`, `setStream`, `getPosition`, `setPosition` are defined as
explicit lambdas in lean4-parser.  For `m = Id` they reduce immediately.
-/

/--
`getStream` returns the current stream both as the value and the
(unchanged) state.
-/
@[simp]
theorem getStream_eq (s : σ) :
    (Parser.getStream : Parser ε σ τ σ) s = .ok s s := rfl

/--
`setStream s'` replaces the stream state with `s'`.
-/
@[simp]
theorem setStream_eq (s' s : σ) :
    (Parser.setStream s' : Parser ε σ τ PUnit) s = .ok s' PUnit.unit := rfl

/--
`getPosition` returns `Stream.getPosition s` without modifying state.

Unfolds: getPosition → getStream → Stream.getPosition → map
-/
@[simp]
theorem getPosition_eq (s : σ) :
    (Parser.getPosition : Parser ε σ τ (Stream.Position σ)) s =
      .ok s (Stream.getPosition s) := rfl

/--
`setPosition pos` restores the stream to position `pos`.

Unfolds: setPosition → getStream → Stream.setPosition → setStream → bind
-/
@[simp]
theorem setPosition_eq (pos : Stream.Position σ) (s : σ) :
    (Parser.setPosition pos : Parser ε σ τ PUnit) s =
      .ok (Stream.setPosition s pos) PUnit.unit := by
  simp only [Parser.setPosition, Parser.getStream, Parser.setStream,
             bind, Bind.bind, pure, Pure.pure]

/-! ## §3  Error Primitives

`throw` and `tryCatch` from `MonadExceptOf`.  `throwUnexpected`
composes `getPosition` with `throw ∘ Error.unexpected`.
-/

/--
`throw e` applied to stream `s` returns `.error s e`.
-/
@[simp]
theorem throw_eq (e : ε) (s : σ) :
    (throw e : Parser ε σ τ α) s = .error s e := rfl

/--
`tryCatch p c` pattern-matches on `p s`: on `.ok` pass through,
on `.error` invoke `c e s'` where `s'` is the error stream.
-/
@[simp]
theorem tryCatch_eq
    (p : Parser ε σ τ α) (c : ε → Parser ε σ τ α) (s : σ) :
    (tryCatch p c) s =
      match p s with
      | .ok s' v => .ok s' v
      | .error s' e => c e s' := by
  dsimp only [tryCatch, tryCatchThe, MonadExcept.tryCatch, MonadExceptOf.tryCatch,
              bind, Bind.bind, pure, Pure.pure, ParserT.run]
  cases p s <;> rfl

/--
`throwUnexpected` (with `input := none`) returns an error with
`Error.unexpected` at the current position.

Unfolds: throwUnexpected → getPosition → throw ∘ Error.unexpected
-/
@[simp]
theorem throwUnexpected_eq (s : σ) :
    (Parser.throwUnexpected (ε := ε) (τ := τ) (α := α)
      (input := none) : Parser ε σ τ α) s =
      .error s (Error.unexpected (Stream.getPosition s) none) := rfl

/--
`throwUnexpected` with an explicit token argument.
-/
@[simp]
theorem throwUnexpected_some_eq (tok : τ) (s : σ) :
    (Parser.throwUnexpected (ε := ε) (τ := τ) (α := α)
      (input := some tok) : Parser ε σ τ α) s =
      .error s (Error.unexpected (Stream.getPosition s) (some tok)) := rfl

/-! ## §4  Backtracking Combinators

These save the position before running a sub-parser and restore it
(on error, or on both error and success for `lookAhead`).

**Stream semantics note**: `setPosition` receives the *post-p* stream
(from the error/success branch of `p`), not the original stream.  This
is because the `do`-notation desugaring threads the stream through:
`getPosition` captures `savePos`, then `p` runs and may change the
stream to `s'`, then `setPosition savePos` receives `s'`.
-/

/--
`withBacktracking p` runs `p`; on error, restores position.

Note: `setPosition` receives the error stream `s'` from `p`, not `s`.
-/
@[simp]
theorem withBacktracking_eq (p : Parser ε σ τ α) (s : σ) :
    (Parser.withBacktracking p) s =
      match p s with
      | .ok s' v => .ok s' v
      | .error s' e =>
        .error (Stream.setPosition s' (Stream.getPosition s)) e := by
  dsimp only [withBacktracking, tryCatch, tryCatchThe, MonadExcept.tryCatch,
              MonadExceptOf.tryCatch, MonadExcept.throw,
              bind, Bind.bind, pure, Pure.pure, getPosition, setPosition,
              throw, MonadExceptOf.throw, throwThe, ParserT.run,
              getStream, setStream, Functor.map]
  cases p s <;> rfl

/--
`OrElse`: `p <|> q` tries `p`; on error, restores position and tries `q`.

Note: `setPosition` receives the error stream `s'` from `p`, not `s`.
-/
@[simp]
theorem orElse_eq
    (p : Parser ε σ τ α) (q : Unit → Parser ε σ τ α) (s : σ) :
    (p <|> q ()) s =
      match p s with
      | .ok s' v => .ok s' v
      | .error s' _ => q () (Stream.setPosition s' (Stream.getPosition s)) := by
  simp only [HOrElse.hOrElse, OrElse.orElse,
             bind, Bind.bind, pure, Pure.pure]
  cases p s <;> rfl

/--
`lookAhead p` runs `p`; restores position on **both** success and error.

Note: `setPosition` receives the post-p stream `s'` in both branches.
-/
@[simp]
theorem lookAhead_eq (p : Parser ε σ τ α) (s : σ) :
    (Parser.lookAhead p) s =
      match p s with
      | .ok s' x => .ok (Stream.setPosition s' (Stream.getPosition s)) x
      | .error s' e =>
        .error (Stream.setPosition s' (Stream.getPosition s)) e := by
  dsimp only [lookAhead, tryCatch, tryCatchThe, MonadExcept.tryCatch,
              MonadExceptOf.tryCatch, MonadExcept.throw,
              bind, Bind.bind, pure, Pure.pure, getPosition, setPosition,
              throw, MonadExceptOf.throw, throwThe, ParserT.run,
              getStream, setStream, Functor.map]
  cases p s <;> rfl

/-! ## §5  Option Family

`eoption` is the proof workhorse — it is defined as a direct
`fun s =>` lambda that bypasses the Monad entirely.
The chain `option? → option! → optionD → optionM → eoption`
(5 delegation layers) ultimately reduces to `eoption`.
-/

/--
`eoption p` always succeeds: returns `.inl x` on success, `.inr e`
(with position restored) on error.

Note: `setPosition` receives the error stream `s'` from `p`.
-/
@[simp]
theorem eoption_eq (p : Parser ε σ τ α) (s : σ) :
    (Parser.eoption p) s =
      match p s with
      | .ok s' x => .ok s' (.inl x)
      | .error s' e =>
        .ok (Stream.setPosition s' (Stream.getPosition s)) (.inr e) := by
  simp only [Parser.eoption, bind, Bind.bind, pure, Pure.pure]
  cases p s <;> rfl

/--
`option? p` always succeeds: returns `some a` on success, `none`
(with position restored) on failure.

This is the most heavily used combinator in the YAML parser.
Note: `p` receives `s` directly; on error, `setPosition` uses `s'`.
-/
@[simp]
theorem option_question_eq (p : Parser ε σ τ α) (s : σ) :
    (Parser.option? p) s =
      match p s with
      | .ok s' a => .ok s' (some a)
      | .error s' _ =>
        .ok (Stream.setPosition s' (Stream.getPosition s)) none := by
  simp only [option?, option!, optionD, optionM, eoption, Functor.map,
             bind, Bind.bind, pure, Pure.pure,
             liftM, monadLift, MonadLift.monadLift]
  cases p s <;> rfl

/-! ## §6  Lookahead

`notFollowedBy` succeeds when the sub-parser fails, and vice versa.
Both branches go through `lookAhead` so the position is always restored.
-/

/--
`notFollowedBy p` succeeds (with `.unit`) when `p` fails, and fails
(with `unexpected`) when `p` succeeds.  Position is restored in both cases.

In the failure branch (when `p` succeeds), `throwUnexpected` is called
on the restored-position stream, so the error's position references
`getPosition restored` rather than `getPosition s`.
-/
@[simp]
theorem notFollowedBy_eq (p : Parser ε σ τ α) (s : σ) :
    (Parser.notFollowedBy p) s =
      match p s with
      | .ok s' _ =>
          let restored := Stream.setPosition s' (Stream.getPosition s)
          .error restored (Error.unexpected (Stream.getPosition restored) none)
      | .error s' _ =>
          .ok (Stream.setPosition s' (Stream.getPosition s)) .unit := by
  simp only [notFollowedBy, lookAhead, tryCatch, tryCatchThe, MonadExcept.tryCatch,
             MonadExceptOf.tryCatch, MonadExcept.throw,
             bind, Bind.bind, pure, Pure.pure, getPosition, setPosition,
             throw, MonadExceptOf.throw, throwThe, throwUnexpected, ParserT.run,
             getStream, setStream, Functor.map]
  cases p s <;> rfl

/-! ## §7  Token Primitives

`tokenCore` is the lowest-level token consumer.  `anyToken` and
`tokenFilter` build on it via `tokenMap`.

For concrete types (e.g., `YamlParser`), these reduce by `rfl`.
For abstract types, the `do`-block desugaring creates `Monad.bind`
applications that don't fully reduce in the kernel; we use `simp`
with the §1 lemmas (`bind_eq`, `pure_eq`) to reduce them.
-/

/--
`tokenCore next?` reads one token using `next?`: returns `.ok` with
the token and advanced stream, or `.error` on end-of-input.

Unfolds: tokenCore → getStream → setStream → throwUnexpected
-/
@[simp]
theorem tokenCore_eq
    (next? : σ → Option (τ × σ)) (s : σ) :
    (Parser.tokenCore (ε := ε) (m := Id) next?) s =
      match next? s with
      | some (tok, s') => .ok s' ⟨tok⟩
      | none =>
        .error s (Error.unexpected (Stream.getPosition s) none) := by
  simp only [Parser.tokenCore, Parser.getStream,
    Parser.throwUnexpected, Parser.getPosition, bind_eq]
  cases next? s with
  | none => rfl
  | some p => cases p; rfl

/--
`anyToken` consumes one token via `Stream.next?`.

Unfolds: anyToken → tokenMap → tokenCore → Stream.next?
-/
@[simp]
theorem anyToken_eq (s : σ) :
    (Parser.anyToken (m := Id) : Parser ε σ τ τ) s =
      match Stream.next? s with
      | some (tok, s') => .ok s' tok
      | none =>
        .error s (Error.unexpected (Stream.getPosition s) none) := by
  simp only [Parser.anyToken, Parser.tokenMap, tokenCore_eq, bind_eq, pure_eq]
  cases Stream.next? s with
  | none => rfl
  | some p => cases p; rfl

/--
`tokenFilter test` consumes one token if `test` returns `true`.

Unfolds: tokenFilter → tokenMap → tokenCore → Stream.next?
-/
@[simp]
theorem tokenFilter_eq
    (test : τ → Bool) (s : σ) :
    (Parser.tokenFilter (ε := ε) (m := Id) test) s =
      match Stream.next? s with
      | some (tok, s') =>
        if test tok then .ok s' tok
        else .error s'
          (Error.unexpected (Stream.getPosition s')
            (some tok))
      | none =>
        .error s (Error.unexpected (Stream.getPosition s) none) := by
  simp only [Parser.tokenFilter, Parser.tokenMap, tokenCore_eq, bind_eq,
    Parser.throwUnexpected, Parser.getPosition]
  cases Stream.next? s with
  | none => rfl
  | some p =>
    cases p with | mk tok s' =>
    simp only []
    split <;> rfl

end Lean4Yaml.Proofs.ParserSpecs
