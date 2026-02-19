import Tests.ValidationTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.Validation.collectTests >>= printSuiteResult
