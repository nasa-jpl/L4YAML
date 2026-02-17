import Tests.ParseTest
def main : IO Unit := do
  let result ← Tests.Parse.collectTests
  Tests.printSuiteResult result
  if !result.allPass then IO.Process.exit 1
