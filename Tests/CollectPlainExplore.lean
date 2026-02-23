import Parser
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Proofs.ParserSpecs

/-!
# CollectPlain Exploration  (Step 5.4.3 — plainScalarSingleLine)

Exploration file for `collectPlain` loop specification lemmas.
Investigates unfold + simp strategies for proving that `collectPlain`
terminates at line breaks, flow indicators, and other stop characters.

## Key discoveries

1. `plainScalarContent.collectPlain` and `plainScalarSingleLine.collectPlain`
   are separate `where`-clause functions with similar structure but different
   fully-qualified names.
2. Fuel-zero case: `unfold` + `simp only [pure_eq]` closes the goal.
3. Fuel+1 with linebreak: `unfold` + `simp only [bind_eq, h_look, h_lb]` +
   `simp [pure_eq]` handles the early-return branch.
4. Flow indicator termination requires careful handling of the nested
   `if`-chain: linebreak → comment → colon → flowIndicator → whitespace → consume.
-/

open Parser Lean4Yaml.Parse
open Lean4Yaml.Proofs.ParserSpecs

-- ═══════════════════════════════════════════════════════════════════
-- §1  Fuel-Zero Base Case
-- ═══════════════════════════════════════════════════════════════════

/-- `collectPlain 0` returns the accumulator unchanged. -/
example (s : Lean4Yaml.YamlStream) (acc : String) (lws : Bool) :
    Lean4Yaml.Parse.plainScalarContent.collectPlain false 0 acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarContent.collectPlain
  simp only [pure_eq]

/-- Same for `plainScalarSingleLine.collectPlain`. -/
example (s : Lean4Yaml.YamlStream) (acc : String) (lws : Bool) :
    Lean4Yaml.Parse.plainScalarSingleLine.collectPlain false 0 acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarSingleLine.collectPlain
  simp only [pure_eq]

-- ═══════════════════════════════════════════════════════════════════
-- §2  Line Break Termination
-- ═══════════════════════════════════════════════════════════════════

/-- `collectPlain` returns the accumulator when looking ahead sees a line break. -/
example (s : Lean4Yaml.YamlStream) (c : Char) (fuel : Nat) (acc : String) (lws : Bool)
    (h_look : (Parser.option?
      (Parser.lookAhead (Parser.anyToken (m := Id) : Lean4Yaml.YamlParser Char))) s =
      Parser.Result.ok s (some c))
    (h_lb : Lean4Yaml.Parse.isLineBreak c = true) :
    Lean4Yaml.Parse.plainScalarContent.collectPlain false (fuel + 1) acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarContent.collectPlain
  simp only [bind_eq, h_look, h_lb]
  simp [pure_eq]

-- ═══════════════════════════════════════════════════════════════════
-- §3  Flow Indicator Termination
-- ═══════════════════════════════════════════════════════════════════

/-- `collectPlain` returns the accumulator when a flow indicator is seen
    in flow context (inFlow = true). The proof must navigate the full
    if-chain:  ¬lineBreak → ¬(# after space) → ¬colon → flowIndicator. -/
example (s : Lean4Yaml.YamlStream) (c : Char) (fuel : Nat) (acc : String) (lws : Bool)
    (h_look : (Parser.option?
      (Parser.lookAhead (Parser.anyToken (m := Id) : Lean4Yaml.YamlParser Char))) s =
      Parser.Result.ok s (some c))
    (h_not_lb : Lean4Yaml.Parse.isLineBreak c = false)
    (h_not_hash_space : (c == '#' && lws) = false)
    (h_not_colon : (c == ':') = false)
    (h_flow : Lean4Yaml.Parse.isFlowIndicator c = true) :
    Lean4Yaml.Parse.plainScalarContent.collectPlain true (fuel + 1) acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarContent.collectPlain
  simp only [bind_eq, h_look, h_not_lb]
  simp [h_not_hash_space, h_not_colon, h_flow, pure_eq]

-- ═══════════════════════════════════════════════════════════════════
-- §4  EOF Termination
-- ═══════════════════════════════════════════════════════════════════

/-- `collectPlain` returns the accumulator when lookAhead sees no character. -/
example (s : Lean4Yaml.YamlStream) (fuel : Nat) (acc : String) (lws : Bool)
    (h_look : (Parser.option?
      (Parser.lookAhead (Parser.anyToken (m := Id) : Lean4Yaml.YamlParser Char))) s =
      Parser.Result.ok s none) :
    Lean4Yaml.Parse.plainScalarContent.collectPlain false (fuel + 1) acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarContent.collectPlain
  simp only [bind_eq, h_look, pure_eq]

-- ═══════════════════════════════════════════════════════════════════
-- §5  plainScalarSingleLine Analogues
-- ═══════════════════════════════════════════════════════════════════

/-- `plainScalarSingleLine.collectPlain` line break termination. -/
example (s : Lean4Yaml.YamlStream) (c : Char) (fuel : Nat) (acc : String) (lws : Bool)
    (h_look : (Parser.option?
      (Parser.lookAhead (Parser.anyToken (m := Id) : Lean4Yaml.YamlParser Char))) s =
      Parser.Result.ok s (some c))
    (h_lb : Lean4Yaml.Parse.isLineBreak c = true) :
    Lean4Yaml.Parse.plainScalarSingleLine.collectPlain false (fuel + 1) acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarSingleLine.collectPlain
  simp only [bind_eq, h_look, h_lb]
  simp [pure_eq]

/-- `plainScalarSingleLine.collectPlain` flow indicator termination. -/
example (s : Lean4Yaml.YamlStream) (c : Char) (fuel : Nat) (acc : String) (lws : Bool)
    (h_look : (Parser.option?
      (Parser.lookAhead (Parser.anyToken (m := Id) : Lean4Yaml.YamlParser Char))) s =
      Parser.Result.ok s (some c))
    (h_not_lb : Lean4Yaml.Parse.isLineBreak c = false)
    (h_not_hash_space : (c == '#' && lws) = false)
    (h_not_colon : (c == ':') = false)
    (h_flow : Lean4Yaml.Parse.isFlowIndicator c = true) :
    Lean4Yaml.Parse.plainScalarSingleLine.collectPlain true (fuel + 1) acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarSingleLine.collectPlain
  simp only [bind_eq, h_look, h_not_lb]
  simp [h_not_hash_space, h_not_colon, h_flow, pure_eq]

/-- `plainScalarSingleLine.collectPlain` EOF termination. -/
example (s : Lean4Yaml.YamlStream) (fuel : Nat) (acc : String) (lws : Bool)
    (h_look : (Parser.option?
      (Parser.lookAhead (Parser.anyToken (m := Id) : Lean4Yaml.YamlParser Char))) s =
      Parser.Result.ok s none) :
    Lean4Yaml.Parse.plainScalarSingleLine.collectPlain false (fuel + 1) acc lws s =
      Parser.Result.ok s acc := by
  unfold Lean4Yaml.Parse.plainScalarSingleLine.collectPlain
  simp only [bind_eq, h_look, pure_eq]
