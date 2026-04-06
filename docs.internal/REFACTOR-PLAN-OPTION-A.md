# Option A Refactoring Plan — Structural Recursion for scan

## Goal

Refactor the `scan` function to use explicit structural recursion instead of imperative `for` loops, enabling formal proofs of all remaining theorems.

## Current Implementation (Scanner.lean:1968-1989)

```lean
def scan (input : String) : Except ScanError (Array (Positioned YamlToken)) := do
  let mut s := ScannerState.mk' input
  s := s.emit .streamStart
  -- Handle BOM
  match s.peek? with
  | some '\uFEFF' => s := s.advance
  | _ => pure ()
  let fuel := input.utf8ByteSize + 1
  for _ in [:fuel * 4] do                        -- IMPERATIVE LOOP
    match ← scanNextToken s with
    | some s' => s := s'                        -- MUTABLE STATE
    | none =>
      -- Error checks
      if s.flowLevel > 0 then throw (.unterminatedFlowCollection '[' s.line)
      if s.directivesPresent && !s.documentEverStarted then
        throw (.directiveWithoutDocument s.line)
      let final := unwindIndents s (-1)
      let final := final.emit .streamEnd
      return final.tokens                       -- EARLY RETURN
  .error (.fuelExhausted s.line s.col)
```

**Problems for verification**:
1. `for _ in [:fuel * 4] do` - No induction principle
2. `s := s'` - Mutable state
3. `return final.tokens` - Early return inside loop
4. Cannot use standard induction tactics

## Proposed Implementation

### Step 1: Create scanLoop Helper

```lean
/-- Structurally recursive helper for scan.

    Processes tokens one at a time, decreasing fuel on each iteration.
    Returns when either:
    - scanNextToken returns none (success)
    - fuel exhausted (error)

    **Design for provability**: Uses structural recursion on fuel,
    enabling standard induction tactics. -/
def scanLoop (s : ScannerState) (fuel : Nat) :
    Except ScanError (Array (Positioned YamlToken)) :=
  match fuel with
  | 0 =>
    -- Fuel exhausted
    .error (.fuelExhausted s.line s.col)
  | fuel' + 1 =>
    match scanNextToken s with
    | .error e => .error e
    | .ok none =>
      -- Scanner finished, perform final checks and emit streamEnd
      if s.flowLevel > 0 then
        .error (.unterminatedFlowCollection '[' s.line)
      else if s.directivesPresent && !s.documentEverStarted then
        .error (.directiveWithoutDocument s.line)
      else
        let final := unwindIndents s (-1)
        let final := final.emit .streamEnd
        .ok final.tokens
    | .ok (some s') =>
      -- Continue scanning
      scanLoop s' fuel'
termination_by fuel
```

**Key changes**:
- `match fuel` gives structural recursion
- No mutable state
- No early return - just recursive call
- `termination_by fuel` proves termination

### Step 2: Refactor scan to Use scanLoop

```lean
def scan (input : String) : Except ScanError (Array (Positioned YamlToken)) :=
  let s := ScannerState.mk' input
  let s := s.emit .streamStart
  -- Handle BOM
  let s := match s.peek? with
    | some '\uFEFF' => s.advance
    | _ => s
  let fuel := input.utf8ByteSize + 1
  scanLoop s (fuel * 4)
```

**Key changes**:
- No `do` notation
- No `mut`
- Pure function composition
- Delegates to scanLoop

## Equivalence Strategy

We need to prove the new implementation is equivalent to the old one. However, we can't keep both simultaneously, so we'll use testing for equivalence.

### Testing Strategy

1. **Unit tests**: Ensure all existing unit tests pass
2. **Integration tests**: Run full test suite
3. **YAML test suite**: All yaml-test-suite tests
4. **Regression tests**: Compare output on large corpus

### Validation Checklist

- [ ] All unit tests pass (Tests/ScannerTests.lean)
- [ ] All integration tests pass (Tests/*.lean)
- [ ] yaml-test-suite results unchanged
- [ ] #guard checks in proofs still pass (39 checks)
- [ ] Performance benchmarks acceptable (within 2x)

## Implementation Steps

### Phase 1: Implementation (Day 1-2)

1. **Backup original**
   - Copy current scan to scan_imperative (commented out)
   - Document as "Original implementation for reference"

2. **Implement scanLoop**
   - Create scanLoop function with structural recursion
   - Add termination_by clause
   - Handle all three cases (fuel=0, none, some)

3. **Refactor scan**
   - Remove do-notation
   - Remove mutable state
   - Call scanLoop

4. **Fix compilation errors**
   - Adjust type signatures if needed
   - Fix any dependency issues

### Phase 2: Validation (Day 2-3)

1. **Compile check**
   - `lake build` succeeds
   - No new warnings

2. **Unit tests**
   - Run scanner tests
   - Fix any failures

3. **Full test suite**
   - Run all tests
   - Compare results to baseline

4. **YAML test suite**
   - Run yaml-test-suite
   - Ensure pass/fail counts unchanged

### Phase 3: Proof Infrastructure (Day 3-4)

1. **Update ScannerCorrectness.lean**
   - Proofs should become simpler
   - Remove comments about "imperative loops"

2. **Prove scan_produces_at_least_two**
   - Use induction on fuel
   - Apply mk'_tokens_empty + emit_tokens_size

3. **Prove scan_first_is_streamStart**
   - Direct from mk' + emit streamStart

4. **Prove scan_last_is_streamEnd**
   - Case analysis on scanLoop result

### Phase 4: Complete Remaining Proofs (Day 4-7)

1. **Scanner invariants** (2 theorems)
2. **Parser proofs** (2 theorems)
3. **End-to-end proofs** (2 theorems)

## Risk Assessment

### High Risk
- **Behavioral changes**: Refactoring might introduce subtle bugs
  - Mitigation: Extensive testing before committing
- **Performance regression**: Recursive calls might be slower
  - Mitigation: Benchmark critical paths, accept 2x slowdown if needed

### Medium Risk
- **Test failures**: Some tests might need updating
  - Mitigation: Understand each failure before fixing
- **Unexpected dependencies**: Code might depend on scan internals
  - Mitigation: Grep for scan usage patterns

### Low Risk
- **Compilation errors**: Should be caught immediately
  - Mitigation: Incremental compilation
- **Proof complications**: Proofs might still be hard
  - Mitigation: We've confirmed helper lemmas exist

## Success Criteria

### Minimum Success (Phase 1-2)
- [ ] New implementation compiles
- [ ] All tests pass
- [ ] No behavioral regressions
- [ ] Performance acceptable (within 2x)

### Target Success (Phase 3)
- [ ] 3 structural property proofs complete
- [ ] No sorry statements in those proofs
- [ ] Build succeeds with no warnings

### Full Success (Phase 4)
- [ ] All 9 remaining proofs complete
- [ ] Zero sorry statements in P10.11 files
- [ ] Zero axioms used
- [ ] All 39 #guard checks pass
- [ ] Documentation updated

## Timeline

| Day | Phase | Tasks | Deliverable |
|-----|-------|-------|-------------|
| 1 | Implementation | Backup, scanLoop, scan refactor | Compiling code |
| 2 | Validation | Tests, yaml-test-suite | Passing tests |
| 3 | Structural proofs | Prove 3 properties | 3 proven theorems |
| 4-5 | Scanner invariants | Prove 2 invariants | 5 scanner theorems done |
| 6 | Parser proofs | Prove 2 parser theorems | 7 total theorems done |
| 7 | End-to-end | Prove 2 final theorems | All 9 theorems complete |

**Total**: 7 days (optimistic), 12 days (with issues)

## Rollback Plan

If refactoring fails or causes major issues:

1. Restore original scan from backup
2. Keep new implementation as `scan_recursive` for future work
3. Document what went wrong in refactor log
4. Return to Option C (accept current state)

## Next Step

Begin Phase 1: Create scanLoop function in Scanner.lean
