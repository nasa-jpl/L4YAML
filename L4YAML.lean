import L4YAML.Config.Config
import L4YAML.Output.Dump
import L4YAML.Output.Emitter
import L4YAML.FFI.FFI
import L4YAML.Spec.Grammar
import L4YAML.Config.Limits
import L4YAML.Proofs.Contracts.BlockScalarContracts
import L4YAML.Proofs.Foundation.CharClass
import L4YAML.Proofs.RoundTrip.CommentProperties
import L4YAML.Proofs.RoundTrip.CommentRoundTrip
import L4YAML.Proofs.Completeness
import L4YAML.Proofs.Composition
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Proofs.Contracts.DocumentContracts
import L4YAML.Proofs.Production.DocumentProduction
import L4YAML.Proofs.Output.DumpRoundTrip
import L4YAML.Proofs.Output.EmitterScannability
import L4YAML.Proofs.EndToEndCorrectness
import L4YAML.Proofs.Errors.ErrorProperties
import L4YAML.Proofs.Errors.EscapeResolution
import L4YAML.Proofs.Errors.FoldNewlines
import L4YAML.Algebra.AnchorMap
import L4YAML.Algebra.Equivalence
import L4YAML.Algebra.Combinators
import L4YAML.Algebra.Fuel
import L4YAML.Algebra.Idempotence
import L4YAML.Algebra.Indent
import L4YAML.Algebra.LawfulBEq
import L4YAML.Algebra.Position
import L4YAML.Algebra.Schema
import L4YAML.Algebra.StringList
import L4YAML.Algebra.Token
import L4YAML.Algebra.TokenStream
import L4YAML.Algebra.Value
import L4YAML.Config.LoadConfig
import L4YAML.Indexed.Range
import L4YAML.Indexed.RepGraph
import L4YAML.Indexed.TokenStream
import L4YAML.Proofs.Production.NodeProduction
import L4YAML.Proofs.Parser.ParserAnchorProofs
import L4YAML.Proofs.Parser.ParserCompleteness
import L4YAML.Proofs.Parser.ParserCorrectness
import L4YAML.Proofs.Parser.ParserGrammable
import L4YAML.Proofs.Parser.ParserGrammableBase
import L4YAML.Proofs.Parser.ParserNodeProofs
import L4YAML.Proofs.Parser.ParserSoundness
import L4YAML.Proofs.Parser.ParserWellBehaved
import L4YAML.Proofs.Parser.ParserWfaProofs
import L4YAML.Proofs.Production.PreprocessProduction
import L4YAML.Proofs.RoundTrip.RoundTrip
import L4YAML.Proofs.RoundTrip.RoundTripComposition
import L4YAML.Proofs.Coupling.ScalarCoupling
import L4YAML.Proofs.Production.ScalarProduction
import L4YAML.Proofs.Scanner.ScannerContracts
import L4YAML.Proofs.Scanner.ScannerCorrectness
import L4YAML.Proofs.Coupling.ScannerCoupling
import L4YAML.Proofs.Scanner.ScannerDispatch
import L4YAML.Proofs.Scanner.ScannerDocument
import L4YAML.Proofs.Scanner.ScannerDoubleQuoted
import L4YAML.Proofs.Output.ScannerEmitBridge
import L4YAML.Proofs.Scanner.ScannerFlowCollection
import L4YAML.Proofs.Scanner.ScannerIndent
import L4YAML.Proofs.Scanner.ScannerIndentStack
import L4YAML.Proofs.Scanner.ScannerLoopInvariant
import L4YAML.Proofs.Scanner.ScannerPlainContent
import L4YAML.Proofs.Scanner.ScannerPlainScalar
import L4YAML.Proofs.Production.ScannerPlainScalarValid
import L4YAML.Proofs.Scanner.ScannerProgress
import L4YAML.Proofs.Scanner.ScannerProofs
import L4YAML.Proofs.Scanner.ScannerScalar
import L4YAML.Proofs.Scanner.ScannerSimpleKey
import L4YAML.Proofs.Scanner.ScannerWhitespace
import L4YAML.Proofs.Scanner.ScanStrictCoupling
import L4YAML.Proofs.Schema.SchemaComposition
import L4YAML.Proofs.Schema.SchemaDump
import L4YAML.Proofs.Schema.SchemaResolution
import L4YAML.Proofs.Soundness
import L4YAML.Proofs.Production.StreamAccum
import L4YAML.Proofs.Foundation.StringProperties
import L4YAML.Proofs.Coupling.StructureCoupling
import L4YAML.Proofs.Production.StructureProduction
import L4YAML.Proofs.Coupling.SurfaceCoupling
import L4YAML.Proofs.Schema.TagResolution
import L4YAML.Scanner.Scanner
import L4YAML.Schema.Schema
import L4YAML.Schema.Api
import L4YAML.Schema.Deriving
import L4YAML.Schema.Dump
import L4YAML.Schema.FromToYaml
import L4YAML.Schema.Struct
import L4YAML.Surface.Surface
import L4YAML.Token.Token
import L4YAML.Parser.Composition
import L4YAML.Spec.Types
import L4YAML.Spec.YamlSpec

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# L4YAML — Verified YAML Parser

A YAML 1.2.2 parser with the goal of verified correctness.

## Quick Start

```lean
import L4YAML

open L4YAML

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
