import Tests.LimitTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.Limits.collectTests >>= printSuiteResult
