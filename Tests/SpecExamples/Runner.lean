module

public import Tests.SpecExamples
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := do
  let result ← Tests.SpecExamples.collectTests
  printSuiteResult result

end Blanket
