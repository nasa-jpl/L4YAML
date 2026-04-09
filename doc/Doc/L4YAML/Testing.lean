/-
  L4YAML Documentation — Testing
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Testing" =>
%%%
tag := "testing"
%%%

{index}[testing]
Beyond the 2,309 formal theorems, L4YAML maintains extensive
runtime and compile-time test suites that validate the parser
against real-world YAML inputs and the official specification.

# Specification Coverage
%%%
tag := "spec-coverage"
%%%

{index}[specification coverage]

 * *132/132* YAML 1.2.2 specification examples pass (100%)
 * *225/225* unique YAML test IDs from the yaml-test-suite pass
   (100% of YAML 1.2.2-applicable tests)
 * *354/406* total yaml-test-suite tests pass (87.2%)
 * The 52 skipped tests cover YAML 1.1 and YAML 1.3 features
   that are outside the YAML 1.2.2 scope

# Test Suites
%%%
tag := "test-suites"
%%%

{index}[test suites]
The project includes 24 test executables spanning 19 hand-written
suites and 7 diagnostic pipelines:

:::table +header
*
  * Suite
  * Focus
*
  * `specexamples`
  * All 132 YAML 1.2.2 specification examples
*
  * `scannerspecexamples`
  * Scanner-level token stream for spec examples
*
  * `scannertests`
  * Scanner behavior on targeted inputs
*
  * `rawparsetests`
  * Raw token-to-AST parsing
*
  * `flowtests`
  * Flow collection syntax (inline sequences, mappings)
*
  * `flowregressioncheck`
  * Regression tests for flow parsing edge cases
*
  * `explicitkeytests`
  * Explicit key (`?`) handling
*
  * `validationtests`
  * Input validation and error reporting
*
  * `limittests`
  * Parser limit enforcement
*
  * `adversarialtests`
  * Adversarial inputs targeting parser robustness
*
  * `mutationtests`
  * Systematic input perturbation
*
  * `propertytests`
  * Randomized property-based testing
*
  * `dumproundtrip`
  * Parse → dump → parse cycle validation
*
  * `schemadump`
  * Schema resolution and dump formatting
*
  * `productioncoverage`
  * Coverage analysis across production inputs
*
  * `errorstagediag`
  * Error stage diagnostic output
*
  * `scalarstagediag`
  * Scalar stage diagnostic output
:::

# Running Tests
%%%
tag := "running-tests"
%%%

All tests are built as Lake executables.
To run the full default test suite:

```
lake build
```

This builds all 415 jobs (zero warnings) including all test
executables listed in `defaultTargets`.
Individual suites can be run directly:

```
lake exe specexamples
lake exe scannertests
lake exe adversarialtests
```

Test results are captured in `docs/` as both plain text and HTML reports.
