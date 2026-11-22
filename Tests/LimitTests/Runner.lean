module

public import Tests.LimitTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.Limits.collectTests >>= printSuiteResult

end Blanket
