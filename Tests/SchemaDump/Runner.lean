module

public import Tests.SchemaDump
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := do
  let result ← Tests.SchemaDump.collectTests
  printSuiteResult result

end Blanket
