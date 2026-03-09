import Lean4Yaml.Proofs.ScannerLoopInvariant

namespace Lean4Yaml.Proofs.ScannerLoopInvariant

open Lean4Yaml.Scanner

-- Concrete validation that advance preserves offset bound for ASCII strings
#guard (ScannerState.mk' "abc").advance.offset ≤ (ScannerState.mk' "abc").advance.inputEnd
#guard (ScannerState.mk' "abc").advance.advance.offset ≤
       (ScannerState.mk' "abc").advance.advance.inputEnd
#guard (ScannerState.mk' "abc").advance.advance.advance.offset ≤
       (ScannerState.mk' "abc").advance.advance.advance.inputEnd

-- Validation for multi-byte UTF-8 characters
#guard (ScannerState.mk' "αβγ").advance.offset ≤ (ScannerState.mk' "αβγ").advance.inputEnd
#guard (ScannerState.mk' "αβγ").advance.advance.offset ≤
       (ScannerState.mk' "αβγ").advance.advance.inputEnd

-- Validation for 3-byte and 4-byte characters
#guard (ScannerState.mk' "日本語").advance.offset ≤ (ScannerState.mk' "日本語").advance.inputEnd
#guard (ScannerState.mk' "🎉🎊").advance.offset ≤ (ScannerState.mk' "🎉🎊").advance.inputEnd
#guard (ScannerState.mk' "🎉🎊").advance.advance.offset ≤
       (ScannerState.mk' "🎉🎊").advance.advance.inputEnd

-- Empty string: advance is identity
#guard (ScannerState.mk' "").advance.offset == 0

-- Mixed ASCII and multi-byte
#guard (ScannerState.mk' "a日b").advance.offset ≤ (ScannerState.mk' "a日b").advance.inputEnd
#guard (ScannerState.mk' "a日b").advance.advance.offset ≤
       (ScannerState.mk' "a日b").advance.advance.inputEnd

-- mk' produces well-formed state (concrete check on each conjunct)
#guard (ScannerState.mk' "test").indents.size ≥ 1
#guard (ScannerState.mk' "test").flowLevel == (ScannerState.mk' "test").flowStack.size
#guard (ScannerState.mk' "test").simpleKeyStack.size == (ScannerState.mk' "test").flowStack.size
#guard (ScannerState.mk' "test").offset ≤ (ScannerState.mk' "test").inputEnd

-- advance chain stays well-formed (concrete check on each conjunct)
#guard (ScannerState.mk' "ab").advance.indents.size ≥ 1
#guard (ScannerState.mk' "ab").advance.flowLevel == (ScannerState.mk' "ab").advance.flowStack.size
#guard (ScannerState.mk' "ab").advance.simpleKeyStack.size == (ScannerState.mk' "ab").advance.flowStack.size
#guard (ScannerState.mk' "ab").advance.offset ≤ (ScannerState.mk' "ab").advance.inputEnd

end Lean4Yaml.Proofs.ScannerLoopInvariant
