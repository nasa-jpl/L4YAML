# Exception Type Refactoring Plan

**Project:** lean4-yaml-verified.iterators
**Date:** 2026-03-11
**Status:** Planning Phase

## Executive Summary

This document outlines a plan to refactor exception handling throughout the YAML library by replacing all `Except String ...` with explicit inductive exception types. This improves type safety, enables pattern matching on error conditions, and strengthens the formal verification properties of the codebase.

## Current State Analysis

### Already Implemented: ScanError

The codebase already has a well-designed `ScanError` inductive type ([Token.lean:237-311](Lean4Yaml/Token.lean#L237-L311)) that covers:

- **Scanner errors** (13 categories): character-level tokenization violations
- **Parser errors** (11 categories): token-level grammar violations

This type demonstrates the target pattern:
```lean
inductive ScanError where
  | tabInIndentation     (line col : Nat)
  | unexpectedChar       (c : Char) (line col : Nat)
  | unterminatedScalar   (style : ScalarStyle) (line : Nat)
  -- ... 21 more structured constructors
```

Key benefits already realized:
- Machine-inspectable error categories
- Pattern-matchable for recovery logic
- Structured position tracking (line/column)
- Centralized `toString` for human-readable messages

### Remaining: Schema API Layer

The Schema API layer (FromYaml/ToYaml typeclasses) still uses `Except String` throughout:

**API Functions** (5 sites):
- `parseAs` [Schema/Api.lean:35](Lean4Yaml/Schema/Api.lean#L35)
- `parseTyped` [Schema/Api.lean:44](Lean4Yaml/Schema/Api.lean#L44)
- `roundTripTyped` [Schema/Dump.lean:128](Lean4Yaml/Schema/Dump.lean#L128)

**Typeclass Methods** (8 sites):
- `FromYamlType.fromYamlType?` [Schema/FromToYaml.lean:43](Lean4Yaml/Schema/FromToYaml.lean#L43)
- `FromYaml.fromYaml?` [Schema/FromToYaml.lean:51](Lean4Yaml/Schema/FromToYaml.lean#L51)
- Instances for 11 primitive/collection types

**Struct Helpers** (4 sites):
- `getMapping` [Schema/Struct.lean:52](Lean4Yaml/Schema/Struct.lean#L52)
- `getString` [Schema/Struct.lean:64](Lean4Yaml/Schema/Struct.lean#L64)
- `getField` [Schema/Struct.lean:79](Lean4Yaml/Schema/Struct.lean#L79)
- `getFieldOpt` [Schema/Struct.lean:90](Lean4Yaml/Schema/Struct.lean#L90)

**Parser Entry Points** (5 sites):
- `parseYamlRaw` [TokenParser.lean:920](Lean4Yaml/TokenParser.lean#L920)
- `parseYaml` [TokenParser.lean:938](Lean4Yaml/TokenParser.lean#L938)
- `parseYamlSingleRaw` [TokenParser.lean:948](Lean4Yaml/TokenParser.lean#L948)
- `parseYamlSingle` [TokenParser.lean:962](Lean4Yaml/TokenParser.lean#L962)
- `parseYamlWithComments` [TokenParser.lean:984](Lean4Yaml/TokenParser.lean#L984)

## Proposed Exception Hierarchy

### 1. SchemaError (NEW)

Type conversion and schema validation errors during FromYaml/ToYaml operations.

```lean
/-
  Schema-level errors (Schema/FromToYaml.lean, Schema/Struct.lean).

  These errors occur during type conversion between `YamlValue`/`YamlType`
  and Lean types via the FromYaml/ToYaml typeclasses.
-/
inductive SchemaError where
  /- Type mismatch errors -/

  | expectedNull       (got : YamlType)
  | expectedBoolean    (got : YamlType)
  | expectedInteger    (got : YamlType)
  | expectedString     (got : YamlType)
  | expectedFloat      (got : YamlType)
  | expectedSequence   (got : YamlType)
  | expectedMapping    (got : YamlType)

  /- Range/constraint errors -/

  | negativeNat        (value : Int)
  | invalidKeyType     (got : YamlType)  -- HashMap keys must be string-like

  /- Struct/field access errors -/

  | notAMapping        (got : YamlValue)
  | notAScalar         (got : YamlValue)
  | missingField       (fieldName : String)
  | fieldConversionError (fieldName : String) (inner : SchemaError)

  /- Collection errors -/

  | wrongSequenceSize  (expected : Nat) (got : Nat)  -- for tuples
  | conversionFailed   (element : Nat) (inner : SchemaError)  -- for array/list elements

  deriving Repr, BEq, Inhabited, DecidableEq

def SchemaError.toString : SchemaError → String
  | .expectedNull got => s!"expected null, got {repr got}"
  | .expectedBoolean got => s!"expected boolean, got {repr got}"
  | .expectedInteger got => s!"expected integer, got {repr got}"
  | .expectedString got => s!"expected string, got {repr got}"
  | .expectedFloat got => s!"expected float, got {repr got}"
  | .expectedSequence got => s!"expected sequence, got {repr got}"
  | .expectedMapping got => s!"expected mapping, got {repr got}"
  | .negativeNat n => s!"expected non-negative integer, got {n}"
  | .invalidKeyType got => s!"HashMap keys must be strings or convertible to strings, got {repr got}"
  | .notAMapping got => s!"expected YAML mapping, got {repr got}"
  | .notAScalar got => s!"expected YAML string scalar, got {repr got}"
  | .missingField name => s!"missing required field '{name}'"
  | .fieldConversionError name inner => s!"{name}: {inner.toString}"
  | .wrongSequenceSize exp got => s!"expected {exp}-element sequence for pair, got {got} elements"
  | .conversionFailed idx inner => s!"element {idx}: {inner.toString}"

instance : ToString SchemaError := ⟨SchemaError.toString⟩
```

### 2. YamlError (NEW)

Top-level exception type that unifies all error categories.

```lean
/-
  Unified YAML error type covering all library layers.

  This is the error type returned by top-level API functions like
  `parseAs`, `parseYaml`, etc.
-/
inductive YamlError where
  | scanError   (err : ScanError)   -- Scanner/Parser layer
  | schemaError (err : SchemaError) -- Type conversion layer
  deriving Repr, BEq, Inhabited, DecidableEq

def YamlError.toString : YamlError → String
  | .scanError e => e.toString
  | .schemaError e => e.toString

instance : ToString YamlError := ⟨YamlError.toString⟩

-- Convenience coercion for lifting errors
instance : Coe ScanError YamlError where
  coe := YamlError.scanError

instance : Coe SchemaError YamlError where
  coe := YamlError.schemaError
```

## Refactoring Roadmap

### Phase 1: Create New Exception Types

**Files to create/modify:**
- [Token.lean](Lean4Yaml/Token.lean) — Add `SchemaError` and `YamlError` near existing `ScanError`

**Impact:**
- No breaking changes yet (additive only)
- Establish the exception hierarchy foundation

### Phase 2: Refactor Schema Layer

**Files to modify:**

1. **[Schema/FromToYaml.lean](Lean4Yaml/Schema/FromToYaml.lean)** (34 occurrences)
   ```lean
   -- Before:
   class FromYamlType (α : Type u) where
     fromYamlType? : YamlType → Except String α

   -- After:
   class FromYamlType (α : Type u) where
     fromYamlType? : YamlType → Except SchemaError α
   ```
   - Update all 11 primitive/collection instances
   - Replace `.error "..."` with structured constructors (e.g., `.error (.expectedBoolean got)`)

2. **[Schema/Struct.lean](Lean4Yaml/Schema/Struct.lean)** (13 occurrences)
   ```lean
   -- Before:
   def getMapping (v : YamlValue) : Except String (Array (YamlValue × YamlValue))

   -- After:
   def getMapping (v : YamlValue) : Except SchemaError (Array (YamlValue × YamlValue))
   ```
   - Update `getString`, `getField`, `getFieldOpt`
   - Wrap nested errors with `.fieldConversionError`

3. **[Schema/Api.lean](Lean4Yaml/Schema/Api.lean)** (4 occurrences)
   ```lean
   -- Before:
   def parseAs (α : Type) [Schema.FromYaml α] (s : String) : Except String α

   -- After:
   def parseAs (α : Type) [Schema.FromYaml α] (s : String) : Except YamlError α
   ```
   - Lift `ScanError` from parser → `YamlError.scanError`
   - Lift `SchemaError` from conversion → `YamlError.schemaError`

4. **[Schema/Dump.lean](Lean4Yaml/Schema/Dump.lean)** (4 occurrences)
   - Update `roundTripTyped`, `roundTripDiagnostics`

**Impact:**
- Breaking change for Schema API users
- Enables pattern matching on error types
- Migration path: `match err with | .schemaError (.missingField name) => ... | .scanError _ => ...`

### Phase 3: Update Parser Entry Points

**Files to modify:**

1. **[TokenParser.lean](Lean4Yaml/TokenParser.lean)** (68 occurrences)
   ```lean
   -- Before:
   def parseYaml (input : String) : Except String (Array YamlDocument)

   -- After:
   def parseYaml (input : String) : Except ScanError (Array YamlDocument)
   ```
   - These functions don't perform schema conversion, so they return `ScanError` not `YamlError`
   - Only functions in `Schema.Api` that combine parsing + conversion return `YamlError`

**Impact:**
- Breaking change for low-level parser users
- No change for users who use `Schema.parseAs` (already returns `YamlError`)

### Phase 4: Update Tests and Examples

**Files to modify:**
- [Tests/FlowTests.lean](Tests/FlowTests.lean)
- [Tests/ExplicitKeyTests.lean](Tests/ExplicitKeyTests.lean)
- [Tests/TryDump.lean](Tests/TryDump.lean)
- [examples/typed/*.lean](examples/typed/)

**Impact:**
- Update test assertions from string matching to pattern matching
- Better test granularity (can assert specific error types)

### Phase 5: Update Proofs

**Files requiring proof updates:** (See detailed analysis in "Implications on Proofs" section)
- [Proofs/SchemaDump.lean](Lean4Yaml/Proofs/SchemaDump.lean) — 3 occurrences
- [Proofs/EndToEndCorrectness.lean](Lean4Yaml/Proofs/EndToEndCorrectness.lean) — 18 occurrences
- [Proofs/Composition.lean](Lean4Yaml/Proofs/Composition.lean) — 22 occurrences
- Others: ~750 total occurrences across 32 proof files

**Impact:**
- Proofs about `Except String` need to become proofs about `Except SchemaError`
- See detailed implications below

## Migration Example

### Before (Current)
```lean
-- Current API usage
match Lean4Yaml.parseAs AppConfig yamlString with
| .ok config => processConfig config
| .error msg =>
    -- Can only check string contents
    if msg.contains "missing required field" then
      handleMissingField
    else
      handleOtherError
```

### After (With Typed Exceptions)
```lean
-- New API usage with pattern matching
match Lean4Yaml.parseAs AppConfig yamlString with
| .ok config => processConfig config
| .error (.schemaError (.missingField name)) =>
    -- Structured error handling
    handleMissingField name
| .error (.schemaError (.fieldConversionError field inner)) =>
    reportFieldError field inner
| .error (.scanError err) =>
    reportSyntaxError err
```

## Implications on Proofs

### Overview

The lean4-yaml-verified.iterators project contains extensive formal verification (~32 proof files, ~750 `.error`/`.ok` occurrences). The exception type refactoring has **significant but manageable** implications on the proof layer.

### Impact Categories

#### 1. No Impact: Scanner/Parser Proofs (Majority)

**Status:** ✅ Already use `ScanError`

The scanner and parser layers already use structured `ScanError` types, so these proofs are unaffected:
- `Proofs/Scanner*.lean` files — Scanner correctness, progress, invariants
- `Proofs/Parser*.lean` files — Parser soundness, completeness, correctness

These represent the bulk of the verification effort and **require no changes**.

#### 2. Minor Impact: Schema Conversion Proofs

**Status:** ⚠️ Require mechanical updates

Files that prove properties about Schema conversions need updates:

**[Proofs/SchemaDump.lean](Lean4Yaml/Proofs/SchemaDump.lean)** (201 lines, 3 error sites):
```lean
-- Before:
theorem roundTrip_preserves_content {α : Type} [ToYaml α] [FromYaml α] (a : α) :
  match parseYamlSingle (dumpTyped a) with
  | .error _ => False  -- String error
  | .ok v' => contentEq (toYaml a) v'

-- After:
theorem roundTrip_preserves_content {α : Type} [ToYaml α] [FromYaml α] (a : α) :
  match parseYamlSingle (dumpTyped a) with
  | .error _ => False  -- YamlError
  | .ok v' => contentEq (toYaml a) v'
```

**Changes required:**
- Update type signatures from `Except String` → `Except SchemaError`
- Error pattern matching remains identical (`| .error _ => ...`)
- Proof structure unchanged (only error type wrapper changes)

**Estimated effort:** Low (mechanical substitution)

#### 3. Moderate Impact: Composition/End-to-End Proofs

**Status:** ⚠️⚠️ Require theorem restructuring

Files proving properties across multiple layers need updates:

**[Proofs/Composition.lean](Lean4Yaml/Proofs/Composition.lean)** (22 error sites):
- Theorems about `parse ∘ dump` round-trips
- Properties spanning Scanner → Parser → Schema layers
- May need explicit error lifting lemmas

**[Proofs/EndToEndCorrectness.lean](Lean4Yaml/Proofs/EndToEndCorrectness.lean)** (18 error sites):
- Top-level correctness theorems
- Integration of all verification layers

**Changes required:**
- Theorems about error propagation need explicit `YamlError` constructors
- Add lemmas about error coercions: `ScanError → YamlError`, `SchemaError → YamlError`
- Update error preservation theorems

**Example refactoring:**
```lean
-- Before: Single error type
theorem parse_error_preserves_line {s : String} {e : String} :
  parseYaml s = .error e →
  ∃ line : Nat, e.contains s!"line {line}"

-- After: Multiple error types with lifting
theorem parse_error_preserves_line {s : String} {e : ScanError} :
  parseYaml s = .error e →
  ∃ line : Nat, e.toString.contains s!"line {line}"

theorem parseAs_scan_error_preserves_line {s : String} {e : YamlError} :
  parseAs α s = .error (.scanError se) →
  ∃ line : Nat, se.toString.contains s!"line {line}"
```

**Estimated effort:** Moderate (theorem restructuring + new lemmas)

#### 4. New Opportunities: Error-Specific Proofs

**Status:** ✅ Enables stronger properties

Structured errors enable **new classes of proofs** previously impossible with `String`:

**Discriminability:**
```lean
-- New theorem: Scanner errors never claim missing fields
theorem scan_error_not_schema_error :
  ∀ (e : YamlError),
    match e with
    | .scanError _ => True
    | .schemaError _ => False
    ∨ True  -- Unprovable with String

-- Concrete property: Field errors always name a field
theorem field_error_has_name :
  ∀ (e : SchemaError),
    match e with
    | .missingField name => name ≠ ""
    | .fieldConversionError name _ => name ≠ ""
    | _ => True
```

**Error Coverage:**
```lean
-- Prove that certain operations only produce certain error types
theorem getMapping_only_type_errors {v : YamlValue} {e : SchemaError} :
  getMapping v = .error e →
  e = .notAMapping v

theorem fromYamlType_nat_errors {t : YamlType} {e : SchemaError} :
  (fromYamlType? t : Except SchemaError Nat) = .error e →
  e = .expectedInteger t ∨ e = .negativeNat n
```

**Position Preservation:**
```lean
-- Prove error positions trace back to input
theorem schema_error_no_position :
  ∀ (e : SchemaError), ¬∃ (line col : Nat), False  -- SchemaError has no position

theorem scan_error_has_position :
  ∀ (e : ScanError), ∃ (line : Nat),
    e.toString.contains s!"line {line}"
```

### Proof Strategy Recommendations

#### 1. Error Lifting Lemmas
Create a small library of error conversion properties:

```lean
-- Coercion preserves toString
theorem coe_scan_error_toString (e : ScanError) :
  (e : YamlError).toString = e.toString := rfl

theorem coe_schema_error_toString (e : SchemaError) :
  (e : YamlError).toString = e.toString := rfl

-- Error injection (discriminability)
theorem scan_error_ne_schema_error (se : ScanError) (sce : SchemaError) :
  YamlError.scanError se ≠ YamlError.schemaError sce := by
  intro h
  cases h

-- Constructor injectivity
theorem yaml_error_scan_injective {e1 e2 : ScanError} :
  YamlError.scanError e1 = YamlError.scanError e2 → e1 = e2 := by
  intro h
  cases h
  rfl
```

#### 2. Backwards Compatibility Bridge
During transition, provide conversion functions:

```lean
-- Temporary: Convert typed errors back to strings for old proof code
def yamlErrorToString (e : YamlError) : String := e.toString

-- Mark old proofs with this during refactoring
def oldProofCompat {α : Type} : Except YamlError α → Except String α
  | .ok a => .ok a
  | .error e => .error e.toString
```

#### 3. Incremental Migration Path

**Phase A: Add new types (no breakage)**
- Define `SchemaError`, `YamlError` in `Token.lean`
- Add coercion instances
- All existing code still compiles

**Phase B: Parallel APIs**
- Create `parseAs'`, `fromYaml'?` with typed errors
- Implement in terms of new types
- Keep old APIs as wrappers (`.mapError toString`)
- Migrate tests to new APIs

**Phase C: Update proofs incrementally**
- Start with leaf proofs (no dependencies)
- Build error lifting lemma library
- Update composition proofs
- Verify no proof regressions

**Phase D: Remove old APIs**
- Delete string-based wrappers
- Update all call sites
- Final proof cleanup

### Proof Maintenance Burden

**Low-risk changes (80% of proof files):**
- Scanner proofs — already use `ScanError`, no changes
- Parser proofs — already use `ScanError`, no changes
- Type signature updates — mechanical substitution
- Error pattern matching — structure unchanged

**Medium-risk changes (15% of proof files):**
- Composition theorems — need error lifting
- End-to-end properties — need new lemmas
- Round-trip proofs — may need restructuring

**High-value additions (5% of effort):**
- Error discriminability proofs
- Error coverage theorems
- Position preservation properties

**Overall assessment:** The refactoring strengthens the formal verification properties by making error handling explicit and inspectable. The proof updates are largely mechanical, with opportunities for stronger theorems that were impossible with unstructured strings.

### Zero Axiom Preservation

**Critical constraint:** The project maintains **zero axioms, zero sorry, zero partial**.

The exception refactoring **preserves this property** because:
- All error types are inductive ADTs (fully defined, no axioms)
- `toString` functions are total (cover all constructors)
- Coercion instances are trivial wrappers (transparent)
- No `partial`, no `unsafe`, no `opaque` required

**Theorem count estimate:**
- 30-50 new error lifting lemmas (trivial proofs)
- 10-20 error discriminability theorems (by cases)
- 100-150 proof updates (mostly mechanical type changes)

**Benefit:** Stronger static guarantees with similar proof complexity.

## Benefits Summary

### Type Safety
- ✅ Errors are machine-inspectable (pattern matching)
- ✅ Compiler prevents missing error cases
- ✅ Impossible to construct invalid error states

### Formal Verification
- ✅ Error categories become provable predicates
- ✅ Enables error coverage theorems
- ✅ Proves error/success path separation
- ✅ Maintains zero axiom property

### Developer Experience
- ✅ IDE autocomplete for error handling
- ✅ Structured error data (no string parsing)
- ✅ Clear error source (scanner vs schema)
- ✅ Better debugging with concrete types

### API Clarity
- ✅ Function signatures document failure modes
- ✅ `YamlError` vs `ScanError` vs `SchemaError` hierarchy
- ✅ Clear error propagation path

## Migration Timeline

| Phase | Effort | Files Changed | Breaking |
|-------|--------|---------------|----------|
| 1. Create Types | 1 day | 1 (Token.lean) | No |
| 2. Schema Layer | 2-3 days | 4 (Schema/*) | Yes |
| 3. Parser Layer | 1 day | 1 (TokenParser.lean) | Yes |
| 4. Tests/Examples | 1-2 days | ~15 | No |
| 5. Proof Updates | 3-5 days | ~32 | No |
| **Total** | **8-12 days** | **~53 files** | **API only** |

## Open Questions

### 1. Error Position Tracking
**Question:** Should `SchemaError` include position information?

**Current:** `SchemaError` has no position fields (unlike `ScanError`)

**Options:**
- **Option A (current):** Schema errors are type-level, no position
- **Option B:** Add optional position to track where conversion failed

**Recommendation:** Start with Option A. Schema errors occur after successful parsing, so the position context is lost. If needed later, add `SchemaError.withPosition (line col : Nat) (inner : SchemaError)` wrapper.

### 2. Nested Error Context
**Question:** Should errors carry full error chains?

**Current:** `fieldConversionError` carries one level of nesting

**Options:**
- **Option A (current):** Single-level nesting (`fieldConversionError name inner`)
- **Option B:** Error chain with full path (`["users", 0, "email"]`)

**Recommendation:** Start with Option A. Option B can be added as a wrapper type later if deep nesting becomes common.

### 3. Error Recovery
**Question:** Should we provide partial parsing with error collection?

**Current:** Fail-fast on first error

**Options:**
- **Option A (current):** Return first error encountered
- **Option B:** Collect multiple errors (`Except (List YamlError) α`)
- **Option C:** Result type with warnings + errors

**Recommendation:** Out of scope for this refactoring. The current fail-fast semantics match the YAML spec and existing behavior.

### 4. Backwards Compatibility Shims
**Question:** Should we provide `Except String` compatibility wrappers?

**Options:**
- **Option A:** Breaking change, update all users
- **Option B:** Provide `parseAs_compat`, `fromYaml?_compat` wrappers with `.mapError toString`

**Recommendation:** Option B for one release cycle, with deprecation warnings. Remove in next major version.

## Success Criteria

- ✅ All API functions use structured exceptions
- ✅ No `Except String` in public APIs
- ✅ All tests pass with new error types
- ✅ All proofs verified (no `sorry`)
- ✅ Zero axioms maintained
- ✅ Documentation updated
- ✅ Migration guide provided

## References

- [Token.lean:237-311](Lean4Yaml/Token.lean#L237-L311) — Existing `ScanError` design
- [Schema/FromToYaml.lean](Lean4Yaml/Schema/FromToYaml.lean) — Schema typeclass layer
- [Schema/Struct.lean](Lean4Yaml/Schema/Struct.lean) — Struct helper functions
- [Proofs/SchemaDump.lean](Lean4Yaml/Proofs/SchemaDump.lean) — Round-trip proofs
- [Proofs/EndToEndCorrectness.lean](Lean4Yaml/Proofs/EndToEndCorrectness.lean) — Integration proofs

## Conclusion

Refactoring to explicit exception types is a **high-value, manageable change** that:
- Strengthens type safety and formal verification
- Maintains zero axioms and totality
- Enables new classes of proofs
- Improves API usability

The proof impact is **largely mechanical** with opportunities for **stronger theorems**. The estimated 8-12 day effort is justified by long-term benefits to correctness, maintainability, and developer experience.
