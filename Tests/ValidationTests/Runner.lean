module

public import Tests.ValidationTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.Validation.collectTests >>= printSuiteResult

end Blanket
