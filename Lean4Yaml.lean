import Lean4Yaml.Types
import Lean4Yaml.Stream
import Lean4Yaml.Grammar
import Lean4Yaml.Parser.Combinators
import Lean4Yaml.Parser.Scalar
import Lean4Yaml.Parser.Anchor
import Lean4Yaml.Parser.Tag
import Lean4Yaml.Parser.Flow
import Lean4Yaml.Parser.Block
import Lean4Yaml.Parser.Document
import Lean4Yaml.Proofs.CharClass
import Lean4Yaml.Proofs.Termination
import Lean4Yaml.Proofs.Soundness
import Lean4Yaml.Proofs.RoundTrip
import Lean4Yaml.Proofs.BlockScalarContracts
import Lean4Yaml.Proofs.StringProperties
import Lean4Yaml.Proofs.DocumentContracts
import Lean4Yaml.Proofs.TestSuite

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Lean4Yaml — Verified YAML Parser

A YAML 1.2.2 parser built on lean4-parser with the goal of
verified correctness.

## Quick Start

```lean
import Lean4Yaml

open Lean4Yaml

-- Parse a YAML string
#eval Parse.parseYaml "key: value\nlist:\n  - a\n  - b"

-- Parse expecting a single document
#eval Parse.parseYamlSingle "hello: world"
```

## Architecture

- **Types**: `YamlValue` AST (compatible with lean4-yaml)
- **Stream**: `YamlStream` with automatic line/column tracking
- **Grammar**: Formal specification as inductive `Prop`s
- **Parser**: lean4-parser combinators producing `YamlValue`
- **Proofs**: Termination, soundness, round-trip (in progress)
-/
