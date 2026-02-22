import Tests.CompletenessTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.Completeness.collectTests >>= printSuiteResult
