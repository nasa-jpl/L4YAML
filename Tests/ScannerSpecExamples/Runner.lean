module

public import Tests.ScannerSpecExamples
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := do
  let result ← Tests.ScannerSpecExamples.collectTests
  printSuiteResult result

end Blanket
