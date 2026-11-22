module

public import Tests.DerivingConsumer
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := do
  let result ← Tests.DerivingConsumer.collectTests
  printSuiteResult result

end Blanket
