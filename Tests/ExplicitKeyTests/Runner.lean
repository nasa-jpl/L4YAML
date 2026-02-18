import Tests.ExplicitKeyTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.ExplicitKey.collectTests >>= printSuiteResult
