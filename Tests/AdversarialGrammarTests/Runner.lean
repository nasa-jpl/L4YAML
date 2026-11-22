module

public import Tests.AdversarialGrammarTests
public import Tests.VerifiedResult

@[expose] public section Blanket

open Tests

def main : IO Unit := Tests.AdversarialGrammar.collectTests >>= printSuiteResult

end Blanket
