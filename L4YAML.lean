module

public import L4YAML.Init
public import L4YAML.CapstoneAttr
public import L4YAML.Capstones
public import L4YAML.Config.Config
public import L4YAML.Output.Dump
public import L4YAML.Output.Align
public import L4YAML.Proofs.Output.AlignProofs
public import L4YAML.Output.Emitter
public import L4YAML.FFI.FFI
public import L4YAML.Spec.Grammar
public import L4YAML.Config.Limits
public import L4YAML.Proofs.Contracts.BlockScalarContracts
public import L4YAML.Proofs.Foundation.CharClass
public import L4YAML.Proofs.RoundTrip.CommentProperties
public import L4YAML.Proofs.RoundTrip.CommentRoundTrip
public import L4YAML.Proofs.Completeness
public import L4YAML.Proofs.Composition
public import L4YAML.Proofs.Serialization
public import L4YAML.Proofs.Coupling.CouplingBridge
public import L4YAML.Proofs.Contracts.DocumentContracts
public import L4YAML.Proofs.Production.Acceptance.Quoted
public import L4YAML.Proofs.Production.Acceptance.Plain
public import L4YAML.Proofs.Production.Acceptance.Properties
public import L4YAML.Proofs.Production.Acceptance.FlowIndicators
public import L4YAML.Proofs.Production.Acceptance.BlockIndicators
public import L4YAML.Proofs.Production.Acceptance.BlockScalar
public import L4YAML.Proofs.Production.DocumentProduction
public import L4YAML.Proofs.Output.DumpRoundTrip
public import L4YAML.Proofs.Output.EmitterScannability.EscapeProperties
public import L4YAML.Proofs.Output.EmitterScannability.ScannerAcceptance
public import L4YAML.Proofs.Output.EmitterScannability.ScanSteps
public import L4YAML.Proofs.Output.EmitterScannability.FilteredGrowth
public import L4YAML.Proofs.Output.EmitterScannability.ScanChainGrowth
public import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
public import L4YAML.Proofs.Output.EmitterScannability.FilteredTracking
public import L4YAML.Proofs.Output.EmitterScannability.WellBracketed
public import L4YAML.Proofs.Output.EmitterScannability.Block
public import L4YAML.Proofs.Output.EmitterScannability.BlockProducers
public import L4YAML.Proofs.Output.EmitterScannability.NonemptyStructure
public import L4YAML.Proofs.Output.EmitterScannability.SeqInteriorSeparators
public import L4YAML.Proofs.Output.EmitterScannability
public import L4YAML.Proofs.Output.IndexedEmitterScannability
public import L4YAML.Proofs.EndToEndCorrectness
public import L4YAML.Proofs.Errors.ErrorProperties
public import L4YAML.Proofs.Errors.EscapeResolution
public import L4YAML.Proofs.Errors.FoldNewlines
public import L4YAML.Algebra.AnchorMap
public import L4YAML.Algebra.Equivalence
public import L4YAML.Algebra.Combinators
public import L4YAML.Algebra.Fuel
public import L4YAML.Algebra.Idempotence
public import L4YAML.Algebra.Indent
public import L4YAML.Algebra.LawfulBEq
public import L4YAML.Algebra.Position
public import L4YAML.Algebra.Schema
public import L4YAML.Algebra.StringList
public import L4YAML.Algebra.Token
public import L4YAML.Algebra.TokenStream
public import L4YAML.Algebra.Value
public import L4YAML.Config.LoadConfig
public import L4YAML.Indexed.CharStream
public import L4YAML.Indexed.Range
public import L4YAML.Indexed.RepGraph
public import L4YAML.Indexed.TokenStream
public import L4YAML.Proofs.Production.NodeProduction
public import L4YAML.Proofs.Parser.ParserAnchorProofs
public import L4YAML.Proofs.Parser.ParserCompleteness
public import L4YAML.Proofs.Parser.ParserCorrectness
public import L4YAML.Proofs.Parser.ParserGrammable
public import L4YAML.Proofs.Parser.ParserGrammableBase
public import L4YAML.Proofs.Parser.TokenGrammar
public import L4YAML.Proofs.Parser.StreamCompleteness
public import L4YAML.Proofs.Parser.ParserScannableBase
public import L4YAML.Proofs.Parser.ParserNodeProofs
public import L4YAML.Proofs.Parser.ParserSoundness
public import L4YAML.Proofs.Parser.ParserWellBehaved
public import L4YAML.Proofs.Parser.FlowParserAcceptance
public import L4YAML.Proofs.Parser.ParserWfaProofs
public import L4YAML.Proofs.Parser.ParserWfaScannable
public import L4YAML.Proofs.Parser.IndexedCorrectness
public import L4YAML.Proofs.Production.PreprocessProduction
public import L4YAML.Proofs.RoundTrip.RoundTrip
public import L4YAML.Proofs.RoundTrip.RoundTripComposition
public import L4YAML.Proofs.Coupling.ScalarCoupling
public import L4YAML.Proofs.Production.ScalarProduction
public import L4YAML.Proofs.Scanner.ScannerContracts
public import L4YAML.Proofs.Scanner.ScannerCorrectness
public import L4YAML.Proofs.Scanner.IndexedRoundtrip
public import L4YAML.Proofs.Coupling.ScannerCoupling
public import L4YAML.Proofs.Scanner.ScannerDispatch
public import L4YAML.Proofs.Scanner.ScannerDocument
public import L4YAML.Proofs.Scanner.ScannerDoubleQuoted
public import L4YAML.Proofs.Output.ScannerEmitBridge
public import L4YAML.Proofs.Scanner.ScannerFlowCollection
public import L4YAML.Proofs.Scanner.ScannerIndent
public import L4YAML.Proofs.Scanner.ScannerIndentStack
public import L4YAML.Proofs.Scanner.ScannerLinePreservation
public import L4YAML.Proofs.Scanner.ScannerLoopInvariant
public import L4YAML.Proofs.Scanner.ScannerPlainContent
public import L4YAML.Proofs.Scanner.ScannerPlainScalar
public import L4YAML.Proofs.Production.ScannerPlainScalarValid
public import L4YAML.Proofs.Scanner.ScannerProgress
public import L4YAML.Proofs.Scanner.ScannerProofs
public import L4YAML.Proofs.Scanner.ScannerScalar
public import L4YAML.Proofs.Scanner.ScalarWalkColFloor
public import L4YAML.Proofs.Scanner.RegisterWitness
public import L4YAML.Proofs.Scanner.StaleCursorFloor
public import L4YAML.Proofs.Scanner.ExplicitKeyCoupling
public import L4YAML.Proofs.Scanner.ScannerSimpleKey
public import L4YAML.Proofs.Scanner.ScannerWhitespace
public import L4YAML.Proofs.Scanner.ScanStrictCoupling
public import L4YAML.Proofs.Schema.SchemaComposition
public import L4YAML.Proofs.Schema.FlowIndicator
public import L4YAML.Proofs.Schema.SchemaDump
public import L4YAML.Proofs.Schema.SchemaResolution
public import L4YAML.Proofs.Soundness
public import L4YAML.Proofs.Production.StreamAccum
public import L4YAML.Proofs.Foundation.StringProperties
public import L4YAML.Proofs.Coupling.StructureCoupling
public import L4YAML.Proofs.Production.StructureProduction
public import L4YAML.Proofs.Coupling.SurfaceCoupling
public import L4YAML.Proofs.Foundation.SurfaceSpanSupply
public import L4YAML.Proofs.Coupling.TabIndentBridge
public import L4YAML.Proofs.Schema.TagResolution
public import L4YAML.Scanner.Scanner
public import L4YAML.Schema.Schema
public import L4YAML.Schema.Api
public import L4YAML.Schema.Deriving
public import L4YAML.Schema.Dump
public import L4YAML.Schema.FromToYaml
public import L4YAML.Schema.Struct
public import L4YAML.Surface.Surface
public import L4YAML.Token.Token
public import L4YAML.Parser.Composition
public import L4YAML.Spec.Types
public import L4YAML.Spec.YamlSpec

@[expose] public section Blanket

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
import L4YAML.Output.Events
import L4YAML.Output.Json

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

end Blanket
