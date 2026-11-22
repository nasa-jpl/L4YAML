module

public import Tests.PropertyTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.PropertyTests.collectTests >>= printSuiteResult

end Blanket
