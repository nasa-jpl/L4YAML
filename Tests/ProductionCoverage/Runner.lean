import Tests.ProductionCoverage
import Tests.VerifiedResult

open Tests

def main (args : List String) : IO Unit := do
  let result ← Tests.ProdCoverage.collectTests
  printSuiteResult result
  let outDir := args.head? |>.getD "docs/reports"
  Tests.ProdCoverage.writeProductionCoverageHtml outDir
