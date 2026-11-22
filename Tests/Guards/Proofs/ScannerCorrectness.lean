module

public import L4YAML.Proofs.Scanner.ScannerCorrectness


public meta import L4YAML.Scanner.Scanner
@[expose] public section Blanket

namespace ScanHelpers

open L4YAML
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.Proofs.ScannerProgress
open L4YAML.Proofs.ScannerProofs
open L4YAML.Proofs.ScannerCorrectness

def checkValidStream (input : String) : Bool :=
  match scanFiltered input with
  | .ok tokens =>
      tokens.size ≥ 2 &&
      (if _h : tokens.size > 0 then tokens[0]!.val == .streamStart else false) &&
      (if _h : tokens.size > 0 then tokens[tokens.size - 1]!.val == .streamEnd else false)
  | .error _ => false

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

end Blanket
