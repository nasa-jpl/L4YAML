import Tests.SpecExamples
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.SpecExamples.collectTests
  printSuiteResult result
