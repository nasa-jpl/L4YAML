import Tests.RawParseTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.RawParse.collectTests
  printSuiteResult result
