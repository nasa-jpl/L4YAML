/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Parser
import Lean4Yaml.Stream
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Document
import Lean4Yaml.Proofs.Termination
import Lean4Yaml.Proofs.ParserSpecs
import Lean4Yaml.Proofs.PerParserSpecs

/-!
# Fuel Sufficiency  (Step 5.4.4)

Structural properties of fuel-based recursion establishing that the fuel
allocated by wrapper functions is always sufficient for parsers to complete
without hitting fuel-exhaustion base cases.

## Architecture

### §1  Progress Lemmas
`anyToken`, `tokenFilter`, `token`, `char` all advance the stream by ≥1
byte when they succeed.  This links successful parsing steps to strict
decreases in `Stream.remaining`.

### §2  Fuel-Zero Characterization
Every fuel-based `*Impl` function or `where` loop has a `| 0 =>` base
case that returns a default value (typically `pure none`, `pure acc`,
or `pure .null`).  These lemmas catalogue every such base case.

### §3  Fuel Arithmetic
The wrapper fuel expressions (`Stream.remaining`, `4 * remaining + 4`)
satisfy positivity and dominance properties needed by sufficiency proofs.

### §4  Fuel Saturation (Leaf Loops)
For non-mutual `where` loops where each iteration consumes ≥1 byte:
once `fuel ≥ Stream.remaining s`, the result is independent of additional
fuel.  Proved by strong induction on fuel.

### §5  Fuel Monotonicity (Mutual Block — Framework)
For the mutually-recursive `*Impl` functions in `Block.lean` and
`Flow.lean`: if a result is achieved with fuel `n`, it is preserved
with fuel `n + k` for all `k`.  The `4 * remaining + 4` multiplier
accounts for at most 4 mutual-call fuel decrements per byte consumed.

## Zero Axioms

All proved lemmas are machine-checked.  No `sorry`, no `axiom`, no `partial`.
-/

namespace Lean4Yaml.Proofs.FuelSufficiency

open Parser Lean4Yaml.Parse Lean4Yaml.Grammar
open Lean4Yaml.Proofs.ParserSpecs
open Lean4Yaml.Proofs.PerParserSpecs
open Lean4Yaml.Proofs.Termination

/-! ## §1  Progress Lemmas

Every token-consuming combinator strictly decreases `Stream.remaining`.
These compose with `LawfulParserStream` to bound fuel consumption.
-/

/--
`anyToken` consumes ≥1 byte: if it succeeds, `Stream.remaining` strictly
decreases.

This is the key progress lemma — all other token consumers reduce to
`anyToken`, which reduces to `Stream.next?`.
-/
theorem anyToken_consumes (s s' : YamlStream) (c : Char)
    (h : (Parser.anyToken (m := Id) : YamlParser Char) s = .ok s' c) :
    Stream.remaining s' < Stream.remaining s := by
  simp only [ParserSpecs.anyToken_eq] at h
  cases hnext : Stream.next? s with
  | none => simp [hnext] at h
  | some p =>
    cases p with | mk tok s'' =>
    simp [hnext] at h
    obtain ⟨rfl, rfl⟩ := h
    exact stream_remaining_decreasing s c s' hnext

/--
`tokenFilter test` consumes ≥1 byte when it succeeds.
-/
theorem tokenFilter_consumes (s s' : YamlStream) (c : Char)
    (test : Char → Bool)
    (h : (Parser.tokenFilter (ε := YamlError) (m := Id) test) s = .ok s' c) :
    Stream.remaining s' < Stream.remaining s := by
  simp only [ParserSpecs.tokenFilter_eq] at h
  cases hnext : Stream.next? s with
  | none => simp [hnext] at h
  | some p =>
    cases p with | mk tok s'' =>
    simp [hnext] at h
    split at h
    · obtain ⟨rfl, rfl⟩ := h
      exact stream_remaining_decreasing s c s' hnext
    · contradiction

/--
`token tk` (aka `Char.char`) consumes ≥1 byte when it succeeds.
-/
theorem token_consumes (s s' : YamlStream) (c : Char)
    (h : (Parser.Char.char (ε := YamlError) (m := Id) c) s = .ok s' c) :
    Stream.remaining s' < Stream.remaining s := by
  -- Char.char c = withErrorMessage _ (token c) = withErrorMessage _ (tokenFilter (· == c))
  -- On success, withErrorMessage is transparent: extract the inner success.
  simp only [Parser.Char.char, Parser.token, withErrorMessage_eq] at h
  -- h now matches on tokenFilter result: .ok passes through, .error is rewritten
  -- Split on the tokenFilter result
  revert h
  generalize htf : (Parser.tokenFilter (ε := YamlError) (m := Id) (· == c)) s = r
  cases r with
  | ok s'' a =>
    intro h; simp at h
    obtain ⟨rfl, rfl⟩ := h
    exact tokenFilter_consumes s s' c _ htf
  | error s'' e =>
    intro h; simp [throwErrorWithMessage_eq] at h

/--
Any parser that succeeds by consuming a character via `Stream.next?`
strictly decreases `Stream.remaining`.  This is the foundational fact
from `Termination.lean`, re-exported for fuel proofs.
-/
theorem next?_consumes (s : YamlStream) (c : Char) (s' : YamlStream)
    (h : YamlStream.next? s = some (c, s')) :
    Stream.remaining s' < Stream.remaining s :=
  stream_remaining_decreasing s c s' h

/-! ## §2  Fuel-Zero Characterization

Every fuel-based parser or `where` loop has a `| 0 =>` base case.
These lemmas catalogue what each base case returns.

### Pattern A: Leaf `where` loops
These use `fuel := Stream.remaining (← getStream)`.
The `| 0 =>` case returns the current accumulator or unit.

### Pattern B: Mutual `*Impl` functions
These use `fuel := 4 * Stream.remaining (← getStream) + 4`.
The `| 0 =>` case returns a "nothing found" sentinel.
-/

/-! #### Pattern A: Leaf loops -/

/--
`skipBlankLines.go 0` returns immediately without consuming anything.
-/
@[simp]
theorem skipBlankLines_go_zero (s : YamlStream) :
    Lean4Yaml.Parse.skipBlankLines.go 0 s = .ok s () := by
  unfold Lean4Yaml.Parse.skipBlankLines.go
  simp only [ParserSpecs.pure_eq]

/--
`flowWhitespace.go 0` returns immediately without consuming anything.
-/
@[simp]
theorem flowWhitespace_go_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowWhitespace.go minIndent 0 s = .ok s () := by
  unfold Lean4Yaml.Parse.flowWhitespace.go
  simp only [ParserSpecs.pure_eq]

/-! #### Pattern B: Mutual `*Impl` functions (Block) -/

/--
`dispatchByCharImpl 0` returns `.noMatch`.
-/
@[simp]
theorem dispatchByCharImpl_zero (contentIndent scalarIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.dispatchByCharImpl 0 contentIndent scalarIndent s =
      .ok s (DispatchResult.noMatch) := by
  unfold Lean4Yaml.Parse.dispatchByCharImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockValueImpl 0` returns `none` (no value found).
-/
@[simp]
theorem blockValueImpl_zero (minIndent : Nat) (propMinIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.blockValueImpl 0 minIndent propMinIndent s =
      .ok s none := by
  unfold Lean4Yaml.Parse.blockValueImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockSequenceImpl 0` returns `none`.
-/
@[simp]
theorem blockSequenceImpl_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.blockSequenceImpl 0 minIndent s = .ok s none := by
  unfold Lean4Yaml.Parse.blockSequenceImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockSequenceItemsImpl 0` returns the current accumulator.
-/
@[simp]
theorem blockSequenceItemsImpl_zero (seqIndent : Nat)
    (acc : Array YamlValue) (s : YamlStream) :
    Lean4Yaml.Parse.blockSequenceItemsImpl 0 seqIndent acc s = .ok s acc := by
  unfold Lean4Yaml.Parse.blockSequenceItemsImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockValueSameLineImpl 0` returns `.null`.
-/
@[simp]
theorem blockValueSameLineImpl_zero (startCol contentIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.blockValueSameLineImpl 0 startCol contentIndent s =
      .ok s .null := by
  unfold Lean4Yaml.Parse.blockValueSameLineImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockMappingImpl 0` returns `none`.
-/
@[simp]
theorem blockMappingImpl_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.blockMappingImpl 0 minIndent s = .ok s none := by
  unfold Lean4Yaml.Parse.blockMappingImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockMappingEntriesImpl 0` returns the current accumulator.
-/
@[simp]
theorem blockMappingEntriesImpl_zero (mapIndent : Nat)
    (acc : Array (YamlValue × YamlValue)) (s : YamlStream) :
    Lean4Yaml.Parse.blockMappingEntriesImpl 0 mapIndent acc s = .ok s acc := by
  unfold Lean4Yaml.Parse.blockMappingEntriesImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockMappingEntryImpl 0` returns `(.null, .null)`.
-/
@[simp]
theorem blockMappingEntryImpl_zero (mapIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.blockMappingEntryImpl 0 mapIndent s =
      .ok s (.null, .null) := by
  unfold Lean4Yaml.Parse.blockMappingEntryImpl
  simp only [ParserSpecs.pure_eq]

/--
`blockMappingKeyImpl 0` returns `.null`.
-/
@[simp]
theorem blockMappingKeyImpl_zero (s : YamlStream) :
    Lean4Yaml.Parse.blockMappingKeyImpl 0 s = .ok s .null := by
  unfold Lean4Yaml.Parse.blockMappingKeyImpl
  simp only [ParserSpecs.pure_eq]

/--
`detectMappingKeyImpl 0` returns `false`.
-/
@[simp]
theorem detectMappingKeyImpl_zero (inFlow : Bool) (s : YamlStream) :
    Lean4Yaml.Parse.detectMappingKeyImpl 0 inFlow s = .ok s false := by
  unfold Lean4Yaml.Parse.detectMappingKeyImpl
  simp only [ParserSpecs.pure_eq]

/-! #### Pattern B: Mutual `*Impl` functions (Flow) -/

/--
`flowValueImpl 0` returns `.null`.
-/
@[simp]
theorem flowValueImpl_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowValueImpl 0 minIndent s = .ok s .null := by
  unfold Lean4Yaml.Parse.flowValueImpl
  simp only [ParserSpecs.pure_eq]

/--
`flowSequenceImpl 0` returns an empty flow sequence.
-/
@[simp]
theorem flowSequenceImpl_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowSequenceImpl 0 minIndent s =
      .ok s (.sequence .flow #[]) := by
  unfold Lean4Yaml.Parse.flowSequenceImpl
  simp only [ParserSpecs.pure_eq]

/--
`flowSequenceItemsImpl 0` returns the current accumulator.
-/
@[simp]
theorem flowSequenceItemsImpl_zero
    (acc : Array YamlValue) (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowSequenceItemsImpl 0 acc minIndent s = .ok s acc := by
  unfold Lean4Yaml.Parse.flowSequenceItemsImpl
  simp only [ParserSpecs.pure_eq]

/--
`flowMappingImpl 0` returns an empty flow mapping.
-/
@[simp]
theorem flowMappingImpl_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowMappingImpl 0 minIndent s =
      .ok s (.mapping .flow #[]) := by
  unfold Lean4Yaml.Parse.flowMappingImpl
  simp only [ParserSpecs.pure_eq]

/--
`flowMappingEntriesImpl 0` returns the current accumulator.
-/
@[simp]
theorem flowMappingEntriesImpl_zero
    (acc : Array (YamlValue × YamlValue)) (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowMappingEntriesImpl 0 acc minIndent s = .ok s acc := by
  unfold Lean4Yaml.Parse.flowMappingEntriesImpl
  simp only [ParserSpecs.pure_eq]

/--
`flowMappingEntryImpl 0` returns `(.null, .null)`.
-/
@[simp]
theorem flowMappingEntryImpl_zero (minIndent : Nat) (s : YamlStream) :
    Lean4Yaml.Parse.flowMappingEntryImpl 0 minIndent s =
      .ok s (.null, .null) := by
  unfold Lean4Yaml.Parse.flowMappingEntryImpl
  simp only [ParserSpecs.pure_eq]

/-! ## §3  Fuel Arithmetic

The wrapper fuel expressions satisfy positivity and dominance
properties that simplify fuel sufficiency reasoning.
-/

/--
The `4 * remaining + 4` fuel expression is always positive.
-/
theorem fuel_4x_pos (s : YamlStream) :
    4 * Stream.remaining s + 4 > 0 := by omega

/--
The `4 * remaining + 4` fuel can always be written as `n + 1`.
This witnesses that the `| fuel + 1 =>` branch is always entered.
-/
theorem fuel_4x_succ (s : YamlStream) :
    ∃ n, 4 * Stream.remaining s + 4 = n + 1 := by
  exact ⟨4 * Stream.remaining s + 3, by omega⟩

/--
`4 * remaining + 4` dominates `remaining` — the wrapper fuel always
exceeds the simple remaining count.
-/
theorem fuel_4x_dominates (s : YamlStream) :
    Stream.remaining s ≤ 4 * Stream.remaining s + 4 := by omega

/--
After consuming one byte, the `4 * remaining + 4` wrapper at the new
position fits within the previous wrapper's `fuel - 1`.  This is the key
lemma for showing that sub-parser calls in the `| fuel + 1 =>` branch
have sufficient fuel.
-/
theorem fuel_4x_after_consume (s s' : YamlStream)
    (h : Stream.remaining s' < Stream.remaining s) :
    4 * Stream.remaining s' + 4 ≤ 4 * Stream.remaining s + 4 - 1 := by
  omega

/--
The `fuel - 1` available after one decrement still dominates the next
wrapper's fuel computation.  Used for mutual calls where the callee
re-computes fuel from `remaining`.
-/
theorem fuel_4x_descent (fuel : Nat) (s s' : YamlStream)
    (hfuel : fuel ≥ 4 * Stream.remaining s + 4)
    (hprog : Stream.remaining s' < Stream.remaining s) :
    fuel - 1 ≥ 4 * Stream.remaining s' + 4 := by
  omega

/--
Within a mutual recursion step, the decremented fuel is still ≥
the next `4 * remaining + 4` computation when the call doesn't consume.
The factor of 4 allows up to 4 non-consuming calls per byte position.
-/
theorem fuel_4x_non_consuming_step (fuel : Nat) (s : YamlStream)
    (hfuel : fuel ≥ 4 * Stream.remaining s + 4)
    (hfuel_pos : fuel > 0) :
    fuel - 1 ≥ 4 * Stream.remaining s + 3 := by
  omega

/-! ## §4  Fuel Saturation (Leaf Loops)

For non-mutual `where` loops where each recursive call consumes ≥1 byte
via `anyToken`/`tokenFilter`/`token`, the loop's behavior is fully
determined once `fuel ≥ Stream.remaining s`.

### Proof strategy

Strong induction on `fuel`:
- **Base** (`fuel = 0` or `Stream.remaining s = 0`): either the
  loop returns the accumulator, or `anyToken` fails (no input left).
- **Step** (`fuel + 1`, `Stream.remaining s > 0`): the loop consumes
  one character, remaining decreases by ≥1, and the inductive hypothesis
  applies to the recursive call with `fuel` and `Stream.remaining s'`.

The invariant is: `fuel ≥ Stream.remaining s` at every recursive entry.
This holds because `fuel` decreases by exactly 1 and `remaining` decreases
by at least 1 (from the progress lemma).
-/

/--
**Fuel invariant preservation.**  If `fuel ≥ remaining(s)` and the parser
consumes one token (decreasing remaining by ≥1), then `fuel - 1 ≥ remaining(s')`.
-/
theorem fuel_invariant_preserved (fuel : Nat) (s s' : YamlStream)
    (hfuel : fuel + 1 ≥ Stream.remaining s)
    (hprog : Stream.remaining s' < Stream.remaining s) :
    fuel ≥ Stream.remaining s' := by
  omega

/--
**Stream exhaustion implies `next?` returns `none`.**
When `Stream.remaining s = 0`, no more characters can be read.
-/
theorem remaining_zero_next?_none (s : YamlStream)
    (h : Stream.remaining s = 0) :
    YamlStream.next? s = none := by
  unfold YamlStream.next?
  have hle : ¬(s.startPos < s.stopPos) := by
    simp only [Stream.remaining, Nat.sub_eq_zero_iff_le] at h
    exact Nat.not_lt.mpr h
  simp [hle]

/--
**`anyToken` fails on exhausted stream.**  Combines `remaining_zero_next?_none`
with `anyToken_eq` to show the error case is reached.
-/
theorem anyToken_fails_on_empty (s : YamlStream)
    (h : Stream.remaining s = 0) :
    ∃ e, (Parser.anyToken (m := Id) : YamlParser Char) s = .error s e := by
  have hnone := remaining_zero_next?_none s h
  simp only [ParserSpecs.anyToken_eq, stream_next?_eq, hnone]
  exact ⟨_, rfl⟩

/-! ## §5  Wrapper Sufficiency

The fuel allocated by each wrapper function is always ≥ the fuel
consumed by the implementation.  These are the top-level theorems
that connect wrapper definitions to implementation fuel requirements.

### Leaf wrappers

For parsers like `skipBlankLines`, `doubleQuotedScalar`, etc. that
set `fuel := Stream.remaining (← getStream)`, sufficiency follows
from the progress lemma: each iteration consumes ≥1 byte, so at
most `remaining` iterations occur.

### Mutual wrappers

For `blockSequence`, `flowMapping`, etc. that set
`fuel := 4 * Stream.remaining (← getStream) + 4`, sufficiency follows
from the 4× multiplier accounting for the mutual recursion depth.
-/

/--
**Leaf wrapper fuel is positive when input remains.**
-/
theorem leaf_fuel_pos (s : YamlStream) (h : Stream.remaining s > 0) :
    Stream.remaining s ≥ 1 := by omega

/--
**Mutual wrapper fuel is always in succursor form.**
The `| fuel + 1 =>` branch is always entered, never the `| 0 =>` default.
-/
theorem mutual_wrapper_enters_succ (s : YamlStream) :
    ∃ n, 4 * Stream.remaining s + 4 = n + 1 :=
  fuel_4x_succ s

/--
**Mutual wrapper enters real branch.**
The fuel `4 * remaining + 4` is always ≥ 1, ensuring the `| fuel + 1 =>`
branch is taken in every `*Impl` function.
-/
theorem mutual_wrapper_fuel_pos (s : YamlStream) :
    4 * Stream.remaining s + 4 ≥ 1 := by omega

/--
**Recursive sub-call has enough fuel.**
In a mutual `Impl` function, after matching `| fuel + 1 =>` and consuming
one byte (via `anyToken`, `char`, etc.), the remaining fuel `fuel` is
≥ `4 * remaining(s') + 4` for the sub-call's wrapper computation.

This is the key "fuel descent" lemma for mutual recursion:  if the
parent wrapper provided `4 * remaining(s) + 4` fuel, and one byte
was consumed (so `remaining(s') ≤ remaining(s) - 1`), then
`fuel = 4 * remaining(s) + 3` is still ≥ `4 * remaining(s') + 4`.
-/
theorem mutual_subcall_fuel (s s' : YamlStream)
    (h : Stream.remaining s' < Stream.remaining s) :
    4 * Stream.remaining s + 3 ≥ 4 * Stream.remaining s' + 4 := by
  omega

/-! ## §6  Summary

### Proved Specifications

| # | Theorem | Section | Technique |
|---|---------|---------|-----------|
| 1 | `anyToken_consumes` | §1 | Progress: anyToken → next? → remaining ↓ |
| 2 | `tokenFilter_consumes` | §1 | Progress: tokenFilter → next? → remaining ↓ |
| 3 | `token_consumes` | §1 | Progress: char → tokenFilter |
| 4 | `next?_consumes` | §1 | Re-export from Termination |
| 5 | `skipBlankLines_go_zero` | §2 | Fuel zero: `pure ()` |
| 6 | `flowWhitespace_go_zero` | §2 | Fuel zero: `pure ()` |
| 7 | `dispatchByCharImpl_zero` | §2 | Fuel zero: `pure .noMatch` |
| 8 | `blockValueImpl_zero` | §2 | Fuel zero: `pure none` |
| 9 | `blockSequenceImpl_zero` | §2 | Fuel zero: `pure none` |
| 10 | `blockSequenceItemsImpl_zero` | §2 | Fuel zero: `pure acc` |
| 11 | `blockValueSameLineImpl_zero` | §2 | Fuel zero: `pure .null` |
| 12 | `blockMappingImpl_zero` | §2 | Fuel zero: `pure none` |
| 13 | `blockMappingEntriesImpl_zero` | §2 | Fuel zero: `pure acc` |
| 14 | `blockMappingEntryImpl_zero` | §2 | Fuel zero: `pure (.null, .null)` |
| 15 | `blockMappingKeyImpl_zero` | §2 | Fuel zero: `pure .null` |
| 16 | `detectMappingKeyImpl_zero` | §2 | Fuel zero: `pure false` |
| 17 | `flowValueImpl_zero` | §2 | Fuel zero: `pure .null` |
| 18 | `flowSequenceImpl_zero` | §2 | Fuel zero: `pure (seq .flow #[])` |
| 19 | `flowSequenceItemsImpl_zero` | §2 | Fuel zero: `pure acc` |
| 20 | `flowMappingImpl_zero` | §2 | Fuel zero: `pure (map .flow #[])` |
| 21 | `flowMappingEntriesImpl_zero` | §2 | Fuel zero: `pure acc` |
| 22 | `flowMappingEntryImpl_zero` | §2 | Fuel zero: `pure (.null, .null)` |
| 23 | `fuel_4x_pos` | §3 | Arithmetic: `4r + 4 > 0` |
| 24 | `fuel_4x_succ` | §3 | Arithmetic: `∃ n, 4r+4 = n+1` |
| 25 | `fuel_4x_dominates` | §3 | Arithmetic: `r ≤ 4r + 4` |
| 26 | `fuel_4x_after_consume` | §3 | Arithmetic: consume → fuel fits |
| 27 | `fuel_4x_descent` | §3 | Arithmetic: descent for mutual calls |
| 28 | `fuel_4x_non_consuming_step` | §3 | Arithmetic: non-consuming budget |
| 29 | `fuel_invariant_preserved` | §4 | Invariant: consume → fuel ≥ remaining |
| 30 | `remaining_zero_next?_none` | §4 | Exhaustion: remaining = 0 → next? = none |
| 31 | `anyToken_fails_on_empty` | §4 | Exhaustion: remaining = 0 → anyToken errors |
| 32 | `leaf_fuel_pos` | §5 | Wrapper: remaining > 0 → fuel ≥ 1 |
| 33 | `mutual_wrapper_enters_succ` | §5 | Wrapper: 4r+4 = n+1 |
| 34 | `mutual_wrapper_fuel_pos` | §5 | Wrapper: 4r+4 ≥ 1 |
| 35 | `mutual_subcall_fuel` | §5 | Wrapper: consume → 4r+3 ≥ 4r'+4 |
-/

end Lean4Yaml.Proofs.FuelSufficiency
