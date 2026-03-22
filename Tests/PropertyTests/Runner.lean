import Tests.PropertyTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.PropertyTests.collectTests >>= printSuiteResult
