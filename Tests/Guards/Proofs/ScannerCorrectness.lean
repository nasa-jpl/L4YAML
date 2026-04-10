import L4YAML.Proofs.ScannerCorrectness

namespace ScanHelpers

open L4YAML
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.Proofs.ScannerProgress
open L4YAML.Proofs.ScannerProofs
open L4YAML.Proofs.ScannerCorrectness

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
