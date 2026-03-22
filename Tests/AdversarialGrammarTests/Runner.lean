import Tests.AdversarialGrammarTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.AdversarialGrammar.collectTests >>= printSuiteResult
