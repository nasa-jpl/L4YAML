import Tests.DumpRoundTrip
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.DumpRoundTrip.collectTests
  printSuiteResult result
