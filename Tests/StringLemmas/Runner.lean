import Tests.StringLemmas
def main : IO Unit := do
  let result ← Tests.StringLemmas.collectTests
  Tests.printSuiteResult result
  if !result.allPass then IO.Process.exit 1
