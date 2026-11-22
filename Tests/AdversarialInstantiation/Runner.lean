module

public import Tests.AdversarialInstantiation
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.AdversarialInstantiation.collectTests >>= printSuiteResult

end Blanket
