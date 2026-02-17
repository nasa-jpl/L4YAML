import Tests.AnchorAlias
import Tests.VerifiedResult

open Tests

def main : IO Unit := do
  let result ← Tests.Anchor.collectTests
  printSuiteResult result
