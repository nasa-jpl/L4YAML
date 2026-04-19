# EmitterScannability.lean Remaining Work

## Status: 7 sorry-using declarations remaining  

### Remaining Sorries (7 declarations, grouped by difficulty)

#### Tier 1: Filtered Token Infrastructure (2 declarations, ~30-50 lines each)
**Foundation for structure theorems**

1. **Line 8169**: `scanNextToken_filtered_grows`
   - Each scanNextToken call extends filtered token array
   - Proof: Show s'.tokens.filter p = s.tokens.filter p ++ suffix
   - Uses saveSimpleKey_filter_placeholder + Array.filter_push
   - ~30-40 lines

2. **Line 8208**: `ScanChain_filtered_grows`  
   - Extends filtered_grows to full ScanChain
   - Proof: Induction using scanNextToken_filtered_grows
   - ~20-30 lines
   - **Depends on**: Line 8169

#### Tier 2: Body Token Characterization (2 declarations, ~100-200 lines each)
**Compositional tracking of body tokens**

3. **Line 8665**: `emitList_body_filtered_characterization`
   - Characterizes what tokens emitList produces
   - Proof: Induction on items list, compose per-item tokens
   - Shows body doesn't contain flowSequenceEnd at top level
   - Uses ScanChain composition + lastRealTokenVal? postconditions
   - **Depends on**: Lines 8169, 8208 (filtered infrastructure)
   - ~100-150 lines

4. **Line 8757**: `emitPairList_body_filtered_characterization`
   - Parallel to emitList but for mapping pairs
   - Shows body doesn't contain flowMappingEnd at top level
   - Same proof structure as emitList case
   - **Depends on**: Lines 8169, 8208 (filtered infrastructure)
   - ~100-150 lines

#### Tier 3: Structure Theorems (2 declarations, ~150-300 lines each)
**Main token array structure proofs**

5. **Line 8839**: `scanFiltered_emitSeq_nonempty_structure`
   - For non-empty sequence: tokens = [streamStart, flowSequenceStart] ++ body ++ [flowSequenceEnd, streamEnd]
   - Proves 8 properties:
     1. tokens[0]!.val = .streamStart
     2. tokens[1]!.val = .flowSequenceStart  
     3. tokens[tokens.size-2]!.val = .flowSequenceEnd
     4. tokens[tokens.size-1]!.val = .streamEnd
     5. tokens.size ≥ 6 (minimum tokens)
     6. Uniqueness: ∀ k < tokens.size-2, tokens[k]!.val ≠ .flowSequenceEnd
     7-8. Position and token properties
   - **Depends on**: Lines 8665 (body characterization), filtered infrastructure
   - ~150-250 lines

6. **Line 9057**: `scanFiltered_emitMap_nonempty_structure`
   - Parallel to scanFiltered_emitSeq_nonempty_structure for mappings
   - Proves 7 similar properties with flowMappingStart/End
   - **Depends on**: Lines 8757 (body characterization), filtered infrastructure
   - ~150-250 lines

#### Tier 4: Content Fidelity (2 declarations, ~150-300 lines each)
**Round-trip correctness for nested structures**

7. **Line 9773**: `emit_roundtrip_sequence_content_eq`
   - Non-empty case: parsed sequence items match originals
   - Proof: Structural decomposition + IH
   - Uses parseFlowSequence result analysis
   - **Depends on**: Parser acceptance (parseStream_emitSequence, implicitly depends on ParserWellBehaved)
   - ~150-200 lines

8. **Line 9812**: `emit_roundtrip_mapping_content_eq`
   - Non-empty case: parsed mapping pairs match originals
   - Proof: Structural decomposition + IH
   - Parallel to sequence case
   - **Depends on**: Parser acceptance (parseStream_emitMapping)
   - ~150-200 lines

### Dependencies Between Layers

```
Tier 1: scanNextToken_filtered_grows (8169)
         ↓
       ScanChain_filtered_grows (8208)
         ↓
         ├─→ emitList_body_filtered_characterization (8665)
         │    ↓
         │   scanFiltered_emitSeq_nonempty_structure (8839)
         │    ↓
         │   parseStream_emitSequence (uses structure + ParserWellBehaved)
         │    ↓
         │   emit_roundtrip_sequence_content_eq (9773)
         │
         └─→ emitPairList_body_filtered_characterization (8757)
              ↓
             scanFiltered_emitMap_nonempty_structure (9057)
              ↓
             parseStream_emitMapping (uses structure + ParserWellBehaved)
              ↓
             emit_roundtrip_mapping_content_eq (9812)
```

### Cross-Module Dependencies

**EmitterScannability depends on ParserWellBehaved:**
- `parseStream_emitSequence` and `parseStream_emitMapping` call `parseFlowSequenceLoop_emitter_ok` and `parseFlowMappingLoop_emitter_ok`
- These are PROVEN in ParserWellBehaved.lean
- Content fidelity proofs use parser acceptance to show parsed values match originals

**Impact of ParserWellBehaved sorries:**
- Tier 4 proofs (content fidelity) may need to wait for:
  - `parseNode_flowSeqStart_in_seq` (line 6017) - COMPLETE except parseNodeProperties lemmas
  - `parseNode_flowMapStart_in_seq` (line 6366) - needs completion
- However, the loop theorems used by `parseStream_emit*` are ALREADY PROVEN
- So Tier 1-3 can proceed independently

### Recommended Attack Order

**Phase A: Token Infrastructure (Tier 1)** (~50-80 lines)
1. scanNextToken_filtered_grows (8169)
2. ScanChain_filtered_grows (8208)
- Unlocks: All body characterization and structure theorems

**Phase B: Sequence Path (Tiers 2-3)** (~250-400 lines)
1. emitList_body_filtered_characterization (8665)
2. scanFiltered_emitSeq_nonempty_structure (8839)
- Unlocks: emit_roundtrip_sequence_content_eq

**Phase C: Mapping Path (Tiers 2-3)** (~250-400 lines)
1. emitPairList_body_filtered_characterization (8757)
2. scanFiltered_emitMap_nonempty_structure (9057)
- Unlocks: emit_roundtrip_mapping_content_eq

**Phase D: Content Fidelity (Tier 4)** (~300-400 lines)
1. emit_roundtrip_sequence_content_eq (9773)
2. emit_roundtrip_mapping_content_eq (9812)

**Estimated Total**: ~850-1280 lines

### Alternative: Interleaved Approach

Could work on both EmitterScannability and ParserWellBehaved in parallel:
- EmitterScannability Phases A-C can proceed independently
- Phase D requires some ParserWellBehaved lemmas but the critical loop theorems are done

### Current Blocker Status

**No blockers for Phases A-C!**
- The loop theorems (`parseFlowSequenceLoop_emitter_ok`, `parseFlowMappingLoop_emitter_ok`) are PROVEN
- These are used in `parseStream_emitSequence` and `parseStream_emitMapping` which are also PROVEN
- Phase D (content fidelity) is the only part that may benefit from additional ParserWellBehaved lemmas

### Notes

- **Filtered token tracking**: Core pattern is showing `.filter` preserves structure through ScanChain
- **Body characterization**: Key insight is that nested brackets are consumed by sub-chains, so body tokens don't contain top-level closing brackets
- **Structure theorems**: Largest proofs, but mostly mechanical composition of infrastructure
- **Content fidelity**: Requires understanding both scanner and parser behavior together
