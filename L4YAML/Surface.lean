/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Surface.Document
import L4YAML.Proofs.DocumentProduction

/-!
# Surface Syntax — Top-Level Definitions & Strictness Theorem

This module ties together all surface syntax productions and defines
the acceptance strictness theorem statements.

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
   stream-level composition, and `InYamlLanguage`.
-/

set_option autoImplicit false

namespace L4YAML.Surface

/-! ## Acceptance Strictness Theorems

The proofs for these theorems are constructed bottom-up through the
coupling infrastructure in the Proofs/ directory. See
`DocumentProduction.lean` for the composition of phases A–D. -/

/-- **Acceptance strictness**: if the parser successfully parses a string,
    the input belongs to the formal YAML 1.2.2 surface syntax.

    This is the target theorem for v0.4.0. The proof will be constructed
    incrementally by establishing coupling theorems for each layer of
    the parser pipeline. -/
theorem parse_strict
    (input : String)
    (docs : Array L4YAML.YamlDocument)
    (h : L4YAML.TokenParser.parseYaml input = .ok docs) :
    InYamlLanguage input :=
  L4YAML.Proofs.DocumentProduction.parse_strict_proof input docs h

/-- Scanner strictness: if scanning succeeds, the input matches
    the character-level and whitespace surface syntax productions
    (basic structure layer). -/
theorem scan_strict
    (input : String)
    (tokens : Array (L4YAML.Positioned L4YAML.YamlToken))
    (h : L4YAML.Scanner.scan input = .ok tokens) :
    InYamlLanguage input :=
  L4YAML.Proofs.DocumentProduction.scan_strict_proof input tokens h

end L4YAML.Surface
