module

public import Tests.FlowTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.Flow.collectTests >>= printSuiteResult

end Blanket
