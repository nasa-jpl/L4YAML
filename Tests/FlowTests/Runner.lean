import Tests.FlowTests
import Tests.VerifiedResult

open Tests

def main : IO Unit := Tests.Flow.collectTests >>= printSuiteResult
