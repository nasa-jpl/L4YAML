import Tests.QuotedFolding
def main : IO Unit := do
  let result ← Tests.QuotedFolding.collectTests
  Tests.printSuiteResult result
  if !result.allPass then IO.Process.exit 1
