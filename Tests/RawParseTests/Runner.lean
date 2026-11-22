module

public import Tests.RawParseTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := do
  let result ← Tests.RawParse.collectTests
  printSuiteResult result

end Blanket
