module

public import Tests.MutationSuiteTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit :=
  Tests.MutationSuite.collectTests >>= printSuiteResult

end Blanket
