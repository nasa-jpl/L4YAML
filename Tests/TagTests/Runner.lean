import Tests.TagTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.Tag.collectTests
  printSuiteResult result
