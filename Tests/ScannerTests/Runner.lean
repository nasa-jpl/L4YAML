import Tests.ScannerTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.ScannerTests.collectTests >>= printSuiteResult
