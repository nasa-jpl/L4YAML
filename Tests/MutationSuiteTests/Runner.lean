import Tests.MutationSuiteTests
import Tests.VerifiedResult

open Tests

def main : IO Unit :=
  Tests.MutationSuite.collectTests >>= printSuiteResult
