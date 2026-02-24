import Tests.SchemaDump
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.SchemaDump.collectTests
  printSuiteResult result
