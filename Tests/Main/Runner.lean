import Tests.Main
def main : IO Unit := do
  let result ← Tests.collectTests
  Tests.printSuiteResult result
  if !result.allPass then IO.Process.exit 1
