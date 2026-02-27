import Tests.ScannerSpecExamples
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.ScannerSpecExamples.collectTests
  printSuiteResult result
