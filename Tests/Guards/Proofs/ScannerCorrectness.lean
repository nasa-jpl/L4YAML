import Lean4Yaml.Proofs.ScannerCorrectness

namespace ScanHelpers

open Lean4Yaml
open Lean4Yaml.Scanner
open Lean4Yaml.Grammar
open Lean4Yaml.Proofs.ScannerProgress
open Lean4Yaml.Proofs.ScannerProofs
open Lean4Yaml.Proofs.ScannerCorrectness

-- Envelope property holds on diverse inputs
#guard checkValidStream ""
#guard checkValidStream "hello"
#guard checkValidStream "key: value"
#guard checkValidStream "- item"
#guard checkValidStream "{ a: 1 }"
#guard checkValidStream "---\ndoc\n..."
#guard checkValidStream "# comment"
#guard checkValidStream "literal: |\n  text"

end ScanHelpers
