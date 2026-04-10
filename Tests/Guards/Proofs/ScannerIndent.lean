import L4YAML.Proofs.ScannerIndent

namespace L4YAML.Proofs.ScannerIndent

open L4YAML.Scanner

private def skipSpacesCol (input : String) : Nat :=
  (skipSpaces (ScannerState.mk' input)).col

-- skipSpaces on no spaces → col stays at 0
#guard skipSpacesCol "hello" == 0

-- skipSpaces on 1 space → col = 1
#guard skipSpacesCol " hello" == 1

-- skipSpaces on 2 spaces → col = 2
#guard skipSpacesCol "  hello" == 2

-- skipSpaces on 4 spaces → col = 4
#guard skipSpacesCol "    hello" == 4

-- skipSpaces on 8 spaces → col = 8
#guard skipSpacesCol "        hello" == 8

-- skipSpaces stops at tab (not a space)
#guard skipSpacesCol "\thello" == 0

-- skipSpaces on empty string → col = 0
#guard skipSpacesCol "" == 0

-- skipSpaces on all spaces → col = length
#guard skipSpacesCol "   " == 3

-- advance column tracking: non-newline increments
#guard (ScannerState.mk' "abc").advance.col == 1
#guard (ScannerState.mk' "abc").advance.advance.col == 2

-- advance column tracking: newline resets
#guard (ScannerState.mk' "a\nb").advance.advance.col == 0
#guard (ScannerState.mk' "a\nb").advance.advance.line == 1
#guard (ScannerState.mk' "a\nb").advance.advance.advance.col == 1

end L4YAML.Proofs.ScannerIndent
