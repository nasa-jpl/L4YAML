import Tests.Verification
def main : IO Unit := do
  let result ← Tests.Verification.collectTests
  Tests.printSuiteResult result
  if !result.allPass then IO.Process.exit 1
