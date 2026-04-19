# ParserWellBehaved.lean Remaining Work

## Status: 8 sorry-using declarations remaining

## Lessons Learned (2026-04-18)

**Initial estimates were too optimistic.** The "easy" Tier 1-2 proofs turned out to require significantly more infrastructure:

1. **Fuel monotonicity** (Tier 1): Estimated ~20 lines, actually needs ~200+ lines
   - Root cause: parseFlowSequenceLoop calls parseNode and parseSinglePairMapping with fuel parameter
   - These nested functions need their own fuel monotonicity proofs first
   - Deep case analysis with 15+ branches in inductive case alone

2. **forIn loop reasoning** (Tier 2): Estimated ~5-10 lines per lemma, likely ~10-15 lines
   - parseNodeProperties unfolds to large goals with deep forIn structure
   - Better approach: single helper lemma capturing all 3 properties together

3. **Proof strategy implications**:
   - Bottom-up approach (infrastructure first) is blocking on complex auxiliary lemmas
   - Top-down approach (main theorems with sorries) might reveal which auxiliary lemmas are actually needed
   - Consider working on EmitterScannability in parallel since loop theorems are already proven

### Recently Completed
✅ Easy/medium balance preservation proofs (5 sorries eliminated):
- Line 6394: Span bound omega proof (parseNode_flowMapStart_in_seq)
- Line 5846: Bracket balance [key_ps.pos+1, j+1) in parseFlowMappingValue_ok flowSequenceStart case  
- Line 6564: Balance preserved through .key and .scalar tokens (scalar key case)
- Line 6676: Balance preserved through .key and flowSequenceStart bracket pair
- Line 6824: Balance preserved through .key and flowMappingStart bracket pair  

### Remaining Sorries (8 declarations, grouped by difficulty)

#### Tier 1: Fuel Monotonicity (2 declarations, ~150-200 lines total)
**REVISED DIFFICULTY: Complex - requires auxiliary lemmas for nested functions**

**Status**: Partial framework in place with 4 sorries

1. **Line 4466**: `parseFlowSequenceLoop_fuel_mono_succ`
   - Successor case: fuel N → fuel N+1 preserves result
   - Proof: Induction on loop structure with extensive case analysis
   - **Actual complexity**: ~150 lines base + ~50-100 lines for auxiliary lemmas
   - **Blockers**:
     - Base case (fuel=0): needs detailed split analysis (~30 lines) - line 4497
     - Inductive case with .flowEntry + recursion: needs parseNode/parseSinglePairMapping fuel monotonicity - line 4547
     - Inductive case items.size=0: symmetric complexity - line 4558
   - **Root cause**: parseFlowSequenceLoop calls parseSinglePairMapping and parseNode with fuel parameter
     - Both functions need their own fuel monotonicity proofs first
     - Or need to prove they don't actually consume extra fuel in these contexts

2. **Line 4475**: `parseFlowSequenceLoop_fuel_mono`  
   - General case: fuel ≤ fuel' preserves result
   - Proof: Induction on fuel' - fuel applying _succ repeatedly
   - ~10 lines (straightforward once _succ is complete)
   - **Depends on**: Line 4466 (fuel_mono_succ)

**Recommendation**: Consider deferring fuel monotonicity or proving auxiliary lemmas:
- `parseNode_fuel_mono`: parseNode with fuel N succeeds → parseNode with fuel N+1 succeeds
- `parseSinglePairMapping_fuel_mono`: symmetric for parseSinglePairMapping
- Alternative: prove these functions don't use fuel in the contexts where parseFlowSequenceLoop calls them

#### Tier 2: parseNodeProperties forIn Lemmas (3 sorries in 1 declaration, ~20-30 lines total)
**Medium difficulty - requires understanding forIn loop behavior**

**Status**: All 3 sorries remain, attempted proof showed deep forIn unfolding complexity

3. **Line 6084** (declaration): `parseNode_flowSeqStart_in_seq`
   - Contains 3 sorries about parseNodeProperties behavior:
   - **Line 6169**: parseNodeProperties returns .ok (not .error) when peek? = flowSequenceStart
     - Proof: parseNodeProperties is a for-loop checking for anchor/tag tokens
     - Since flowSequenceStart is neither anchor nor tag, loop breaks immediately with .ok
     - **Challenge**: Deep forIn unfolding creates large goals, need targeted lemma
     - ~10-15 lines (revised from 5-10)
   
   - **Line 6179**: ps_after_props = ps (state unchanged)
     - Proof: Loop breaks immediately without calling advance
     - **Depends on**: Understanding forIn break behavior
     - ~10-15 lines (revised from 5-10)
   
   - **Line 6184**: props = {} (empty properties)
     - Proof: Loop starts with {}, breaks immediately, returns initial value
     - ~10-15 lines (revised from 5-10)

**Recommendation**: Create helper lemma `parseNodeProperties_break_on_non_tag` that captures all 3 properties at once

#### Tier 3: parseExplicitKey Helpers (2 declarations, ~40-60 lines each)
**Medium-high difficulty - follow template from parseNode_flowSeqStart_in_seq**

4. **Line 5110**: `parseExplicitKey_flowSeq`
   - parseExplicitKey on [ succeeds, advances to after ]
   - **Strategy**: Extract proof pattern from parseNode_flowSeqStart_in_seq (lines 6050-6300)
   - Key steps:
     1. Unfold parseExplicitKey → dispatches to parseNode
     2. parseNode → parseNodeProperties (no-op) → parseNodeContent → parseFlowSequence
     3. parseFlowSequence → parseFlowSequenceLoop (use h_inner: ParseNodeFlowSeqOk)
     4. Loop succeeds, returns at position j
     5. Advance past flowSequenceEnd → position j+1
     6. applyNodeFinalization preserves tokens, trackPositions
   - **Depends on**: Lines 6120, 6130, 6135 (parseNodeProperties lemmas)
   - ~40-60 lines

5. **Line 5149**: `parseExplicitKey_flowMap`
   - Symmetric with parseExplicitKey_flowSeq but for flow mappings
   - parseExplicitKey on { succeeds, advances to after }
   - Same proof structure, replace Seq with Map throughout
   - **Depends on**: parseNodeProperties lemmas (would need similar ones for flowMappingStart)
   - ~40-60 lines

#### Tier 4: Main parseNode Witnesses (2 declarations, ~60-100 lines each)
**High difficulty - complete implementations of complex theorems**

6. **Line 5293** (declaration): `parseFlowMappingValue_ok` 
   - Contains 2 remaining sorries:
   - **Line 5779**: Main witness for flowSequenceStart value case
     - Full parseNode unfolding: properties → validateNodeProps → parseFlowSequence → loop → finalization
     - Similar to parseNode_flowSeqStart_in_seq but for value position instead of element position
     - **Depends on**: Lines 5110 (parseExplicitKey_flowSeq)
     - ~60 lines
   
   - **Line 5907**: Main witness for flowMappingStart value case  
     - Parallel to line 5779 but for flow mappings
     - **Depends on**: Lines 5149 (parseExplicitKey_flowMap)
     - ~60 lines

7. **Line 6366**: `parseNode_flowMapStart_in_seq`
   - Nested flowMappingStart case in sequence body
   - Parallel structure to parseNode_flowSeqStart_in_seq (lines 6050-6365)
   - Key differences:
     - Uses MapBodyProps.bracket_map instead of SeqBodyProps.bracket_seq
     - Calls parseFlowMappingLoop instead of parseFlowSequenceLoop
     - Uses ih_map instead of ih_seq
   - **Template available**: Copy parseNode_flowSeqStart_in_seq, adapt Map-specific lemmas
   - ~80-100 lines

#### Tier 5: Mapping Entry Parser (1 declaration, ~60-80 lines)
**Medium-high difficulty - different structure from loop-based cases**

8. **Line 6923**: `parseEntry_in_flowMap`
   - Map body case: .key → parseExplicitKey → .value → parseFlowMappingValue
   - Different from nested collection cases (no loop, sequential structure)
   - Three sub-cases: scalar key, [ key, { key
   - Each case: parseExplicitKey (helper) → position at .value → parseFlowMappingValue_ok (proven)
   - **Depends on**: Lines 5110, 5149, 5293 (parseExplicitKey helpers + parseFlowMappingValue_ok)
   - ~60-80 lines

### Recommended Attack Order (REVISED 2026-04-18)

Given the discovered complexity of Tier 1-2 infrastructure, recommend one of these strategies:

#### Strategy A: Complete Infrastructure First (Bottom-Up)
**Total estimated effort**: ~450-650 lines

**Phase 1a: Auxiliary Fuel Lemmas** (~100-150 lines)
**Status (2026-04-18)**: Lemma declarations added with structural analysis

Added auxiliary lemma declarations:
1. `parseNode_fuel_mono_succ` (line 4468) - analyzed structure, reveals mutual dependency
2. `parseSinglePairMapping_fuel_mono_succ` (line 4486) - depends on parseNode_fuel_mono_succ

**Discovered Dependency Graph**:
```
parseNode_fuel_mono_succ
  ↓ (calls parseNodeContent which dispatches to)
  ├─ parseFlowSequence → parseFlowSequenceLoop (our original target!)
  ├─ parseFlowMapping → parseFlowMappingLoop
  ├─ parseBlockSequence → parseBlockSequenceLoop  
  ├─ parseBlockMapping → parseBlockMappingLoop
  └─ parseImplicitBlockSequence → parseImplicitBlockSequenceLoop

parseSinglePairMapping_fuel_mono_succ
  ↓ (calls parseNode for key and value)
  parseNode_fuel_mono_succ

parseFlowSequenceLoop_fuel_mono_succ
  ↓ (calls parseSinglePairMapping and parseNode)
  ├─ parseSinglePairMapping_fuel_mono_succ
  └─ parseNode_fuel_mono_succ
```

**Circular Dependency**: parseNode → parseFlowSequence → parseFlowSequenceLoop needs parseNode fuel monotonicity!

**Resolution Strategies**:
1. **Mutual Induction**: Prove all loop and parser fuel monotonicity simultaneously (~300-500 lines)
   - **CHOSEN APPROACH** - implemented as `parser_fuel_mono_succ` theorem (line 4462)
   - 12-part mutual induction covering all parsers and loops:
     1. `parseNode` fuel monotonicity
     2. `parseFlowSequence` fuel monotonicity
     3. `parseFlowMapping` fuel monotonicity
     4. `parseBlockSequence` fuel monotonicity
     5. `parseBlockMapping` fuel monotonicity
     6. `parseImplicitBlockSequence` fuel monotonicity
     7. `parseSinglePairMapping` fuel monotonicity
     8. `parseFlowSequenceLoop` fuel monotonicity
     9. `parseFlowMappingLoop` fuel monotonicity
     10. `parseBlockSequenceLoop` fuel monotonicity
     11. `parseBlockMappingLoop` fuel monotonicity
     12. `parseImplicitBlockSequenceLoop` fuel monotonicity
   - Framework structure (50 lines): base cases complete, inductive cases pending
   - Estimated completion: ~350 lines remaining across all 12 inductive cases
   - Individual extractors defined for easy use (e.g., `parseNode_fuel_mono_succ`)

2. **Weakening**: Prove "fuel doesn't matter" for specific well-formed inputs (avoids general monotonicity)
3. **Assumption**: Assert parseNode/parseSinglePairMapping fuel monotonicity as axioms (risky but unblocks progress)
4. **Alternative Path**: Skip fuel monotonicity entirely, prove main theorems work around it

**Phase 1b: Complete Mutual Induction (parser_fuel_mono_succ)** (~350 lines)
**Current Status**: Framework established, base cases complete, 11 inductive cases pending

Completion order (each part builds on previous):
1. Part 1 (parseNode): ~40 lines - needs Parts 2-6 for parseNodeContent dispatch
2. Part 2 (parseFlowSequence): ~20 lines - needs Part 8 (parseFlowSequenceLoop)
3. Part 3 (parseFlowMapping): ~20 lines - needs Part 9 (parseFlowMappingLoop)
4. Part 4 (parseBlockSequence): ~20 lines - needs Part 10 (parseBlockSequenceLoop)
5. Part 5 (parseBlockMapping): ~20 lines - needs Part 11 (parseBlockMappingLoop)
6. Part 6 (parseImplicitBlockSequence): ~20 lines - needs Part 12 (parseImplicitBlockSequenceLoop)
7. Part 7 (parseSinglePairMapping): ~30 lines - needs Part 1 (parseNode)
8. Part 8 (parseFlowSequenceLoop): ~60 lines - needs Parts 1 & 7
9. Part 9 (parseFlowMappingLoop): ~60 lines - needs Parts 1 & 7
10. Part 10 (parseBlockSequenceLoop): ~40 lines - needs Part 1
11. Part 11 (parseBlockMappingLoop): ~40 lines - needs Part 1
12. Part 12 (parseImplicitBlockSequenceLoop): ~40 lines - needs Part 1

**Mutual Dependency Resolution**: Prove all 12 parts simultaneously in one theorem
- Each inductive case can reference other parts via the mutual induction hypothesis
- Example: Part 1 (parseNode) dispatches to Parts 2-6 via parseNodeContent
- Example: Part 8 (parseFlowSequenceLoop) calls Parts 1 & 7 for nested parsing

**Phase 1c: Complete parseFlowSequenceLoop_fuel_mono_succ** (~40 lines)
- Once parser_fuel_mono_succ is complete, the 3 remaining sorries can be filled in
- Apply Parts 1 & 7 from mutual induction for parseSinglePairMapping/parseNode branches
- Base case (line 4529): ~30 lines detailed split analysis
- Inductive case (line 4569): ~10 lines applying Parts 1 & 7

**Phase 1d: Complete parseFlowSequenceLoop_fuel_mono** (~10 lines)
- Straightforward induction on fuel' - fuel applying _succ repeatedly

**Phase 2: forIn Infrastructure** (~30-40 lines)
- Helper lemma parseNodeProperties_break_on_non_tag
- Use it to eliminate sorries at lines 6169, 6179, 6184

**Phase 3-4**: Continue with Tiers 3-5 as originally planned (~340-420 lines)

#### Strategy B: Skip Infrastructure, Work Top-Down (Recommended)
**Total estimated effort**: ~340-420 lines (defer Tier 1-2)

**Phase 1: Main Witness Constructions** (~200-260 lines)
- parseFlowMappingValue_ok flowSequenceStart case (line 5779)
- parseFlowMappingValue_ok flowMappingStart case (line 5907)
- Work around parseNodeProperties sorries with inline reasoning

**Phase 2: Template-Based Cases** (~140-160 lines)  
- parseNode_flowMapStart_in_seq (line 6366) - copy from parseNode_flowSeqStart_in_seq
- parseEntry_in_flowMap (line 6923)

**Benefits**: 
- Proves main theorems first, shows which auxiliary lemmas are actually needed
- Fuel monotonicity may not be needed if we always have sufficient fuel bounds
- Can work around parseNodeProperties by inline unfolding

**Phase 3 (Optional)**: Circle back to infrastructure if actually needed

#### Strategy C: Pivot to EmitterScannability
Work on EmitterScannability.lean Phases A-C (~500-800 lines) in parallel
- Loop theorems already proven, no blocking dependencies
- Return to ParserWellBehaved after gaining more proof experience

### Notes

- **Template reuse**: parseNode_flowSeqStart_in_seq (lines 6050-6365) is the proven template
  - ~315 lines including all 7 properties
  - Can be adapted for flowMapStart case with Map-specific lemmas
  
- **Fuel management**: Most proofs need fuel ≥ 4*N+6 where N = tokens.size
  - Inner loops use 4*N+4
  - Fuel monotonicity bridges the gap

- **Bracket balance pattern**: All bracket cases use same 3-piece composition:
  - [pos, pos+1): opening bracket = +1
  - [pos+1, j): inner body = 0 (from IH)  
  - [j, j+1): closing bracket = -1
  - Total: 1 + 0 + (-1) = 0

- **State field preservation**: All cases must prove:
  - tokens preserved
  - trackPositions preserved  
  - pos advanced within bounds
  - peek? postcondition (flowEntry or collection end)
