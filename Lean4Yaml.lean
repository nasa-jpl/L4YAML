import LeanPrism

import Lean4Yaml.Types
import Lean4Yaml.YamlSpec
import Lean4Yaml.Grammar
import Lean4Yaml.Token
import Lean4Yaml.Scanner
import Lean4Yaml.TokenParser
import Lean4Yaml.Emitter
import Lean4Yaml.Dump
import Lean4Yaml.Schema
import Lean4Yaml.Schema.FromToYaml
import Lean4Yaml.Schema.Struct
import Lean4Yaml.Schema.Deriving
import Lean4Yaml.Schema.Api
import Lean4Yaml.Schema.Dump
import Lean4Yaml.Proofs.BlockScalarContracts
import Lean4Yaml.Proofs.CharClass
import Lean4Yaml.Proofs.CommentProperties
import Lean4Yaml.Proofs.CommentRoundTrip
import Lean4Yaml.Proofs.Completeness
import Lean4Yaml.Proofs.Composition
import Lean4Yaml.Proofs.DocumentContracts
import Lean4Yaml.Proofs.DumpRoundTrip
import Lean4Yaml.Proofs.EndToEndCorrectness
import Lean4Yaml.Proofs.ErrorProperties
import Lean4Yaml.Proofs.EscapeResolution
import Lean4Yaml.Proofs.FoldNewlines
import Lean4Yaml.Proofs.ParserCompleteness
import Lean4Yaml.Proofs.ParserCorrectness
import Lean4Yaml.Proofs.ParserGrammable
import Lean4Yaml.Proofs.ParserSoundness
import Lean4Yaml.Proofs.RoundTrip
import Lean4Yaml.Proofs.ScannerContracts
import Lean4Yaml.Proofs.ScannerDispatch
import Lean4Yaml.Proofs.ScannerDocument
import Lean4Yaml.Proofs.ScannerDoubleQuoted
import Lean4Yaml.Proofs.ScannerEmitBridge
import Lean4Yaml.Proofs.ScannerFlowCollection
import Lean4Yaml.Proofs.ScannerIndent
import Lean4Yaml.Proofs.ScannerIndentStack
import Lean4Yaml.Proofs.ScannerLoopInvariant
import Lean4Yaml.Proofs.ScannerPlainContent
import Lean4Yaml.Proofs.ScannerPlainScalar
import Lean4Yaml.Proofs.ScannerPlainScalarValid
import Lean4Yaml.Proofs.ScannerProgress
import Lean4Yaml.Proofs.ScannerProofs
import Lean4Yaml.Proofs.ScannerScalar
import Lean4Yaml.Proofs.ScannerSimpleKey
import Lean4Yaml.Proofs.ScannerWhitespace
import Lean4Yaml.Proofs.SchemaDump
import Lean4Yaml.Proofs.SchemaResolution
import Lean4Yaml.Proofs.Soundness
import Lean4Yaml.Proofs.StringProperties
import Lean4Yaml.Proofs.ValueAlgebra

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Lean4Yaml — Verified YAML Parser

A YAML 1.2.2 parser with the goal of verified correctness.

## Quick Start

```lean
import Lean4Yaml

open Lean4Yaml

-- Parse a YAML string
#eval TokenParser.parseYaml "key: value\nlist:\n  - a\n  - b"

-- Parse expecting a single document
#eval TokenParser.parseYamlSingle "hello: world"
```

## Architecture

- **Types**: `YamlValue` AST, `YamlPos` position tracking
- **Token**: Token types with position information
- **Scanner**: Tokenizer producing `TokenStream`
- **TokenParser**: Token-level parser producing `YamlValue`
- **Grammar**: Formal specification as inductive `Prop`s
- **Proofs**: Soundness, completeness, round-trip, composition
-/
