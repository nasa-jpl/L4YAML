/-
  L4YAML Documentation — Verification Strategy
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Verification" =>
%%%
tag := "verification"
%%%

{index}[verification]
L4YAML employs a three-layer verification strategy that combines
formal proofs, compile-time checks, and runtime tests to achieve
comprehensive coverage of the YAML 1.2.2 specification.

# Three-Layer Strategy
%%%
tag := "three-layer-strategy"
%%%

## Layer 1: Machine-Checked Proofs
%%%
tag := "formal-proofs"
%%%

{index}[machine-checked proofs]
The core layer consists of 2,309 Lean 4 theorems across 61 proof
modules (~47,000 lines).
These proofs are checked by the Lean kernel — the small trusted
core of the system — and establish properties including:

 * *Soundness* — every token stream produced by the scanner
   corresponds to a valid YAML grammar derivation
 * *Completeness* — every valid YAML input is accepted (not
   rejected with an error)
 * *Progress* — the scanner's input offset strictly increases
   on every step, guaranteeing termination
 * *Well-formedness preservation* — internal invariants
   (indentation stack consistency, flow level balance, simple key
   lifecycle) are maintained across all scanner operations
 * *Pipeline composition* — scanner and parser compose correctly
   to deliver end-to-end guarantees

## Layer 2: Compile-Time Guards
%%%
tag := "compile-time-guards"
%%%

{index}[compile-time guards]
2,124 `#guard` statements are evaluated by the Lean kernel at
build time.
These are not runtime tests — they are _kernel-evaluated assertions_
that must hold for the project to compile.
A failing `#guard` is a build error, not a test failure.

Guards are used extensively for:

 * Concrete scanner behavior on specific inputs
 * Round-trip properties (parse → emit → parse = original)
 * Token stream structure for specification examples
 * Character predicate boundary conditions

## Layer 3: Runtime Tests
%%%
tag := "runtime-tests"
%%%

{index}[runtime tests]
1,041 runtime tests across 19 suites provide additional coverage:

 * _Specification examples_ — all 132/132 YAML 1.2.2 examples
 * _yaml-test-suite_ — 225/225 applicable test IDs (354/406 total;
   52 YAML 1.1/1.3 tests are correctly skipped)
 * _Property tests_ — randomized input generation for edge cases
 * _Mutation tests_ — systematic input perturbation
 * _Adversarial tests_ — handcrafted inputs targeting parser limits
 * _Round-trip tests_ — parse → dump → parse cycle validation

# Key Proof Modules
%%%
tag := "proof-modules"
%%%

:::table +header
*
  * Module
  * Theorems
  * Scope
*
  * `ScannerCorrectness.lean`
  * 259 theorems + 1,063 guards
  * Character-to-token correctness for all scanner operations
*
  * `Completeness.lean`
  * 63 theorems
  * Valid YAML inputs are accepted
*
  * `Soundness.lean`
  * 28 theorems
  * Output corresponds to valid grammar derivations
*
  * `RoundTrip.lean`
  * 58 theorems + 63 guards
  * Parse-emit-parse cycle properties
*
  * `Composition.lean`
  * 12 theorems
  * Scanner + parser pipeline correctness
*
  * `ScannerEmitBridge.lean`
  * 12 theorems + 64 guards
  * Bridge between scanner emissions and grammar predicates
*
  * `ParserSoundness.lean`
  * 12 theorems
  * Grammar-to-implementation correspondence
*
  * `ScannerProgress.lean`
  * Multiple theorems
  * Offset strictly increases on every scanner step
*
  * `ScannerSimpleKey.lean`
  * Multiple theorems
  * Simple key lifecycle well-formedness
*
  * `ScannerDispatch.lean`
  * Multiple theorems
  * Dispatch pipeline preserves all invariants
:::

# Proof Engineering Patterns
%%%
tag := "proof-patterns"
%%%

{index}[proof engineering]
Several patterns emerged during the verification effort:

 * _Decomposition_ — large functions are decomposed into
   validation (error guards), state transformation (pure updates),
   and emission (token output) phases, each proved independently
   then composed.

 * _Append-only invariant_ — the switch from `insertAt` to
   placeholder reservation slots with `setIfInBounds` backpatching
   eliminated the hardest class of proof obligations (index shifting).

 * _Monotonic progress_ — proving `offset_lt` (strict increase)
   for every scanner operation provides termination and guarantees
   no infinite loops.

 * _Well-formedness threading_ — a `WellFormed` predicate on
   scanner state is threaded through every operation, establishing
   that invariants are maintained from `scannerInit` through
   `scanNextToken` to stream completion.

# Zero-Axiom Policy
%%%
tag := "zero-axiom"
%%%

{index}[zero axioms]
The project uses zero axioms beyond Lean's built-in foundations
(`propext`, `Quot.sound`, `Classical.choice`).
No `sorry` appears anywhere in the codebase.
No `partial def` is used — every function has a kernel-checked
termination proof.

This means the formal guarantees are as strong as the Lean kernel
itself: if the kernel accepts the proofs, the properties hold.
