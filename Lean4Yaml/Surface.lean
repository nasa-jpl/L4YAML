/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Surface.Document
import Lean4Yaml.TokenParser
import Lean4Yaml.Scanner

/-!
# Surface Syntax — Top-Level Definitions & Strictness Theorem

This module ties together all surface syntax productions and defines
the top-level predicate `InYamlLanguage` and the acceptance strictness
theorem statement.

## The Acceptance Strictness Property

**Theorem** (acceptance strictness): If the parser accepts an input
string and produces documents, then the input belongs to the formal
YAML 1.2.2 surface syntax grammar.

```
parseYaml s = .ok docs → InYamlLanguage s
```

This is strictly stronger than the existing soundness property (which
states the *output AST* is well-formed). Acceptance strictness ensures
the *input characters* conform to the YAML grammar — ruling out
leniencies where the parser accidentally accepts invalid syntax.

## Architecture

The surface syntax is organized in five layers:

1. **Combinators** (`Surface.Combinators`): Generic grammar combinators
   over positioned character streams.

2. **Basic** (`Surface.Basic`): Character-level, line break, whitespace,
   indentation, comment, separation, and directive productions.

3. **Scalars** (`Surface.Scalars`): Double-quoted, single-quoted, plain,
   literal block, and folded block scalar productions.

4. **Node** (`Surface.Node`): Mutually recursive flow/block collection
   and node productions (the core of the YAML grammar).

5. **Document** (`Surface.Document`): Document markers, document types,
   and the stream-level composition.
-/

set_option autoImplicit false

namespace Lean4Yaml.Surface

/-! ## Top-Level Predicate -/

/-- A string is a valid YAML stream according to the surface syntax grammar.

    This is the input-level specification: the string's characters conform
    to the YAML 1.2.2 productions [1]–[211], consuming the entire input. -/
def InYamlLanguage (s : String) : Prop :=
  ∃ s' : SurfPos,
    SLYamlStream ⟨s.toList, 0⟩ s' ∧ s'.chars = []

/-! ## Acceptance Strictness Theorem (Statement)

The theorem connects the parser implementation to the formal grammar.
The proof requires coupling theorems for every scanner/parser function,
showing that successful parsing implies the input matches the surface syntax.

Proof strategy (bottom-up):
1. Scanner produces tokens → input characters match basic productions
2. Token parser consumes tokens → token sequences match node productions
3. Document/stream composition → full input matches stream production
-/

/-- **Acceptance strictness**: if the parser successfully parses a string,
    the input belongs to the formal YAML 1.2.2 surface syntax.

    This is the target theorem for v0.4.0. The proof will be constructed
    incrementally by establishing coupling theorems for each layer of
    the parser pipeline. -/
theorem parse_strict
    (input : String)
    (docs : Array Lean4Yaml.YamlDocument)
    (h : Lean4Yaml.TokenParser.parseYaml input = .ok docs) :
    InYamlLanguage input := by
  sorry -- Target theorem: proof to be constructed from coupling lemmas

/-! ## Partial Strictness Results

While the full theorem is under construction, we can prove strictness
for specific production layers. These partial results are independently
useful and serve as building blocks for the complete proof. -/

/-- Scanner strictness: if scanning succeeds, the input matches
    the character-level and whitespace surface syntax productions
    (basic structure layer). -/
theorem scan_strict
    (input : String)
    (tokens : Array (Lean4Yaml.Positioned Lean4Yaml.YamlToken))
    (h : Lean4Yaml.Scanner.scan input = .ok tokens) :
    InYamlLanguage input := by
  sorry -- Partial result: scanner produces valid surface syntax

/-! ## Coupling Infrastructure

Coupling theorems connect each layer of the parser pipeline to the
corresponding surface syntax productions. -/

/-- The indent consumed by the scanner corresponds to `SIndent n` in
    the surface syntax. This is the simplest coupling theorem and
    serves as a template for more complex ones. -/
theorem indent_coupling (n : Nat) (cs : List Char) (col : Nat) :
    cs.take n = List.replicate n ' ' →
    cs.length ≥ n →
    SIndent n ⟨cs, col⟩ ⟨cs.drop n, col + n⟩ := by
  induction n generalizing cs col with
  | zero => intros; exact SIndent.zero _
  | succ k ih =>
    intro hrep hlen
    match cs, hlen with
    | c :: rest, hlen =>
      simp [List.replicate_succ] at hrep
      obtain ⟨hc, hrest_rep⟩ := hrep
      subst hc
      have hlen' : rest.length ≥ k := by simp at hlen; omega
      have ih_result := ih rest (col + 1) hrest_rep hlen'
      have hcol : col + 1 + k = col + (k + 1) := by omega
      rw [hcol] at ih_result
      exact SIndent.succ k rest col _ ih_result

end Lean4Yaml.Surface
