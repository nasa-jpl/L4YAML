import Tests.CharClassTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.CharClass.collectTests >>= printSuiteResult
