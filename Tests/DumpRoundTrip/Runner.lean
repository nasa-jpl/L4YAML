module

public import Tests.DumpRoundTrip
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := do
  let result ← Tests.DumpRoundTrip.collectTests
  printSuiteResult result

end Blanket
