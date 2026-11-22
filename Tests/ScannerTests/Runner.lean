module

public import Tests.ScannerTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.ScannerTests.collectTests >>= printSuiteResult

end Blanket
