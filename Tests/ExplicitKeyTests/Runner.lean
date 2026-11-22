module

public import Tests.ExplicitKeyTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.ExplicitKey.collectTests >>= printSuiteResult

end Blanket
