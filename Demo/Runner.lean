import Demo
def main : IO Unit := do
  let result ← Demo.collectTests
  Tests.printSuiteResult result
  if !result.allPass then IO.Process.exit 1
