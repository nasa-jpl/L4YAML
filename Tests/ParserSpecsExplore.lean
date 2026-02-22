import Parser
import Lean4Yaml.Stream

/-!
# Parser Specs Exploration  (Step 5.4.2)

Exploration file for combinator specification lemmas.  Investigates
universe constraints, unfolding depths, and proof strategies for the
~15 foundation lemmas needed in `Proofs/ParserSpecs.lean`.

## Key discoveries

1. `Parser.Result.{u}` requires `ε σ α : Type u` — all in the **same** universe.
2. `tokenCore` returns `ULift τ`, introducing universe `max u_τ u_ε_σ`.
   For the generic case, `τ` must be in the same universe as `ε`/`σ`.
3. For concrete `YamlParser`, everything is `Type 0` — no universe issues.
4. Generic lemmas need either `{ε σ τ : Type u}` (all same universe) or
   separate universe variables with careful `ULift` handling.
-/

open Lean4Yaml
open Lean4Yaml.Parse
open Parser

/-! ## §1  Universe structure of lean4-parser types -/

-- Parser.Result has a single universe for all three type params
#check @Parser.Result  -- Type u → Type u → Type u → Type u

-- ParserT has many implicit universe params
#check @ParserT  -- (ε σ τ : Type _) → ... → (m : Type _ → Type _) → Type _ → Type _

-- Parser is abbrev of ParserT with m = Id
#check @Parser  -- (ε σ τ : Type _) → ... → Type _ → Type _

-- Stream class has separate universes for σ and τ
#check @Parser.Stream  -- (σ : Type _) → (τ : outParam (Type _)) → Type _

/-! ## §2  Concrete YamlParser types — all Type 0 -/

-- Verify all YamlParser types are in Type 0
#check (inferInstance : Parser.Stream YamlStream Char)
#check (inferInstance : Parser.Error YamlError YamlStream Char)
example : YamlError = Parser.Error.Simple YamlStream Char := rfl
-- YamlParser α = YamlStream → Parser.Result YamlError YamlStream α

/-! ## §3  Monad primitive unfolding (generic) -/

section MonadPrimitives

variable {ε σ : Type} {τ : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

-- pure: reduces by rfl  (unfold depth 1)
example (x : α) (s : σ) :
    (pure x : Parser ε σ τ α) s = .ok s x := rfl

-- bind: reduces by rfl  (unfold depth 1)
example (p : Parser ε σ τ α) (f : α → Parser ε σ τ β) (s : σ) :
    (p >>= f) s =
      match p s with
      | .ok s' a => f a s'
      | .error s' e => .error s' e := rfl

-- map: reduces by rfl  (unfold depth 1)
example (f : α → β) (p : Parser ε σ τ α) (s : σ) :
    (f <$> p) s =
      match p s with
      | .ok s' a => .ok s' (f a)
      | .error s' e => .error s' e := rfl

end MonadPrimitives

/-! ## §4  Stream access unfolding (generic) -/

section StreamAccess

variable {ε σ : Type} {τ : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

-- getStream: one lambda, reduces by rfl  (depth 1)
example (s : σ) :
    (Parser.getStream : Parser ε σ τ σ) s = .ok s s := rfl

-- setStream: one lambda, reduces by rfl  (depth 1)
example (s' s : σ) :
    (Parser.setStream s' : Parser ε σ τ PUnit) s = .ok s' PUnit.unit := rfl

-- getPosition: map ∘ getStream, reduces by rfl  (depth 2)
example (s : σ) :
    (Parser.getPosition : Parser ε σ τ (Parser.Stream.Position σ)) s =
      .ok s (Parser.Stream.getPosition s) := rfl

-- setPosition: getStream >>= setStream ∘ Stream.setPosition, reduces by rfl  (depth 3)
example (pos : Parser.Stream.Position σ) (s : σ) :
    (Parser.setPosition pos : Parser ε σ τ PUnit) s =
      .ok (Parser.Stream.setPosition s pos) PUnit.unit := rfl

end StreamAccess

/-! ## §5  Error primitive unfolding (generic) -/

section ErrorPrimitives

variable {ε σ : Type} {τ : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

-- throw: reduces by rfl  (depth 1)
example (e : ε) (s : σ) :
    (throw e : Parser ε σ τ α) s = .error s e := rfl

-- tryCatch: reduces by rfl  (depth 1)
example (p : Parser ε σ τ α) (c : ε → Parser ε σ τ α) (s : σ) :
    (tryCatch p c) s =
      match p s with
      | .ok s' v => .ok s' v
      | .error s' e => c e s' := rfl

-- throwUnexpected (none): reduces by rfl  (depth 3)
example (s : σ) :
    (Parser.throwUnexpected (ε := ε) (τ := τ) (α := α)
      (input := none) : Parser ε σ τ α) s =
      .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := rfl

-- throwUnexpected (some tok): reduces by rfl  (depth 3)
example (tok : τ) (s : σ) :
    (Parser.throwUnexpected (ε := ε) (τ := τ) (α := α)
      (input := some tok) : Parser ε σ τ α) s =
      .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) (some tok)) := rfl

end ErrorPrimitives

/-! ## §6  Backtracking combinator unfolding (generic) -/

section Backtracking

variable {ε σ : Type} {τ : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

-- orElse: reduces by rfl  (depth 2)
example (p : Parser ε σ τ α) (q : Unit → Parser ε σ τ α) (s : σ) :
    (p <|> q ()) s =
      let savePos := Parser.Stream.getPosition s
      match p s with
      | .ok s' v => .ok s' v
      | .error s' _ => q () (Parser.Stream.setPosition s' savePos) := rfl

-- withBacktracking: reduces by rfl  (depth 4)
example (p : Parser ε σ τ α) (s : σ) :
    (Parser.withBacktracking p) s =
      let savePos := Parser.Stream.getPosition s
      match p s with
      | .ok s' v => .ok s' v
      | .error s' e =>
        .error (Parser.Stream.setPosition s' savePos) e := rfl

-- lookAhead: reduces by rfl  (depth 4)
example (p : Parser ε σ τ α) (s : σ) :
    (Parser.lookAhead p) s =
      let savePos := Parser.Stream.getPosition s
      match p s with
      | .ok s' x => .ok (Parser.Stream.setPosition s' savePos) x
      | .error s' e =>
        .error (Parser.Stream.setPosition s' savePos) e := rfl

end Backtracking

/-! ## §7  Option family unfolding (generic) -/

section OptionFamily

variable {ε σ : Type} {τ : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

-- eoption: reduces by rfl  (depth 1, direct lambda)
example (p : Parser ε σ τ α) (s : σ) :
    (Parser.eoption p) s =
      let savePos := Parser.Stream.getPosition s
      match p s with
      | .ok s' x => .ok s' (.inl x)
      | .error s' e =>
        .ok (Parser.Stream.setPosition s' savePos) (.inr e) := rfl

-- option?: chain option? → option! → optionD → optionM → eoption (5 layers)
-- reduces by rfl despite the chain
example (p : Parser ε σ τ α) (s : σ) :
    (Parser.option? p) s =
      let savePos := Parser.Stream.getPosition s
      match p s with
      | .ok s' a => .ok s' (some a)
      | .error s' _ =>
        .ok (Parser.Stream.setPosition s' savePos) none := rfl

end OptionFamily

/-! ## §8  Token primitives — universe exploration -/

section TokenUniverse

-- For concrete YamlParser types (all Type 0), no universe issue
-- tokenCore: reduces by rfl when all types are in same universe
example (next? : YamlStream → Option (Char × YamlStream)) (s : YamlStream) :
    (Parser.tokenCore (ε := YamlError) (m := Id) next?) s =
      match next? s with
      | some (tok, s') => .ok s' ⟨tok⟩
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := rfl

-- anyToken for YamlParser: reduces by rfl
example (s : YamlStream) :
    (Parser.anyToken (ε := YamlError) (σ := YamlStream) (τ := Char)
      (m := Id) : YamlParser Char) s =
      match Stream.next? s with
      | some (tok, s') => .ok s' tok
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := rfl

-- tokenFilter for YamlParser: reduces by rfl
example (test : Char → Bool) (s : YamlStream) :
    (Parser.tokenFilter (ε := YamlError) (m := Id) test : YamlParser Char) s =
      match Stream.next? s with
      | some (tok, s') =>
        if test tok then .ok s' tok
        else .error s'
          (Parser.Error.unexpected (Parser.Stream.getPosition s')
            (some tok))
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := rfl

-- Generic version: rfl does NOT work for token functions because
-- the `do` block's Monad `bind` doesn't reduce with abstract instances.
-- Solution: define `@[simp]` helper lemmas and chain them.

variable {ε σ : Type} {τ : Type}
  [Parser.Stream σ τ] [Parser.Error ε σ τ]

-- Step 1: bind_eq reduces `(p >>= f) s` — key for token lemma proofs
@[simp]
private theorem bind_eq' (p : Parser ε σ τ α) (f : α → Parser ε σ τ β) (s : σ) :
    (p >>= f) s = match p s with
    | .ok s' a => f a s'
    | .error s' e => .error s' e := rfl

@[simp]
private theorem pure_eq' (x : α) (s : σ) :
    (pure x : Parser ε σ τ α) s = .ok s x := rfl

@[simp]
private theorem map_eq' (f : α → β) (p : Parser ε σ τ α) (s : σ) :
    (f <$> p) s = match p s with
    | .ok s' a => .ok s' (f a)
    | .error s' e => .error s' e := rfl

-- Step 2: tokenCore with simp lemmas
example (next? : σ → Option (τ × σ)) (s : σ) :
    (Parser.tokenCore (ε := ε) (m := Id) next?) s =
      match next? s with
      | some (tok, s') => .ok s' ⟨tok⟩
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := by
  simp only [Parser.tokenCore, Parser.getStream, Parser.setStream,
    Parser.throwUnexpected, Parser.getPosition, bind_eq', pure_eq', map_eq']
  cases next? s with
  | none => rfl
  | some p => cases p; rfl

-- Step 3: tokenMap with simp lemmas — the key building block
@[simp]
private theorem tokenCore_eq' (next? : σ → Option (τ × σ)) (s : σ) :
    (Parser.tokenCore (ε := ε) (m := Id) next?) s =
      match next? s with
      | some (tok, s') => .ok s' ⟨tok⟩
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := by
  simp only [Parser.tokenCore, Parser.getStream, Parser.setStream,
    Parser.throwUnexpected, Parser.getPosition, bind_eq', pure_eq', map_eq']
  cases next? s with
  | none => rfl
  | some p => cases p; rfl

-- Step 4: anyToken via tokenCore_eq'
example (s : σ) :
    (Parser.anyToken (m := Id) : Parser ε σ τ τ) s =
      match Stream.next? s with
      | some (tok, s') => .ok s' tok
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := by
  simp only [Parser.anyToken, Parser.tokenMap, tokenCore_eq', bind_eq', pure_eq',
    Parser.throwUnexpected, Parser.getPosition, map_eq']
  cases Stream.next? s with
  | none => rfl
  | some p => cases p; rfl

-- Step 5: tokenFilter via tokenCore_eq' + split on test
example (test : τ → Bool) (s : σ) :
    (Parser.tokenFilter (ε := ε) (m := Id) test) s =
      match Stream.next? s with
      | some (tok, s') =>
        if test tok then .ok s' tok
        else .error s'
          (Parser.Error.unexpected (Parser.Stream.getPosition s')
            (some tok))
      | none =>
        .error s (Parser.Error.unexpected (Parser.Stream.getPosition s) none) := by
  simp only [Parser.tokenFilter, Parser.tokenMap, tokenCore_eq', bind_eq', pure_eq',
    Parser.throwUnexpected, Parser.getPosition, map_eq']
  cases Stream.next? s with
  | none => rfl
  | some p =>
    cases p with | mk tok s' =>
    simp only []
    split <;> rfl

end TokenUniverse

/-! ## §9  Summary

All lemmas verified by Lean's kernel — no `sorry`, no `axiom`.

Key findings:
1. Use `{ε σ : Type} {τ : Type}` (plain `Type` = `Type 0`), NOT `Type u`.
   The `Type u` version fails because `Parser.Stream` and `Parser.Error`
   have independent universe params that can't unify with a single `u`.
2. §1–§7 lemmas (monad primitives, stream access, error, backtracking,
   option family) all reduce by `rfl`.
3. §8 token lemmas need `@[simp]` helper chain: `bind_eq` and `pure_eq`
   must be in the simp set so that the Monad `bind/pure` for `ParserT`
   reduces when the outer `do` block from `tokenMap` is unfolded.
   Pattern: `simp only [..., bind_eq, pure_eq]; cases ...; rfl`
4. Concrete YamlParser specializations reduce by `rfl` for ALL lemmas
   (including tokens) — the kernel can fully evaluate when instances
   are concrete.
5. The proof chain for token lemmas is:
   `tokenCore_eq` → `anyToken_eq` → `tokenFilter_eq`
   where each lemma uses the previous one(s) via `simp only`.
-/
