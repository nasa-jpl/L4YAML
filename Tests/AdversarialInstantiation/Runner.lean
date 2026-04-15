import Tests.AdversarialInstantiation
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.AdversarialInstantiation.collectTests >>= printSuiteResult
