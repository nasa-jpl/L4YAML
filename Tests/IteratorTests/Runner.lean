import Tests.IteratorTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.IteratorTests.collectTests
  printSuiteResult result
