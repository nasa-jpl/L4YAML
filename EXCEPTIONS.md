# Exception Type Refactoring Plan

**Project:** lean4-yaml-verified.iterators
**Date:** 2026-03-11
**Status:** Complete (2026-03-20) — All 5 phases done

## Executive Summary

This document outlines a plan to refactor exception handling throughout the YAML library by replacing all `Except String ...` with explicit inductive exception types. This improves type safety, enables pattern matching on error conditions, and strengthens the formal verification properties of the codebase.

## Current State Analysis

### Already Implemented: ScanError

The codebase already has a well-designed `ScanError` inductive type ([Token.lean:237-311](L4YAML/Token.lean#L237-L311)) that covers:

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
- `parseAs` [Schema/Api.lean:35](L4YAML/Schema/Api.lean#L35)
- `parseTyped` [Schema/Api.lean:44](L4YAML/Schema/Api.lean#L44)
- `roundTripTyped` [Schema/Dump.lean:128](L4YAML/Schema/Dump.lean#L128)

**Typeclass Methods** (8 sites):
- `FromYamlType.fromYamlType?` [Schema/FromToYaml.lean:43](L4YAML/Schema/FromToYaml.lean#L43)
- `FromYaml.fromYaml?` [Schema/FromToYaml.lean:51](L4YAML/Schema/FromToYaml.lean#L51)
- Instances for 11 primitive/collection types

**Struct Helpers** (4 sites):
- `getMapping` [Schema/Struct.lean:52](L4YAML/Schema/Struct.lean#L52)
- `getString` [Schema/Struct.lean:64](L4YAML/Schema/Struct.lean#L64)
- `getField` [Schema/Struct.lean:79](L4YAML/Schema/Struct.lean#L79)
- `getFieldOpt` [Schema/Struct.lean:90](L4YAML/Schema/Struct.lean#L90)

**Parser Entry Points** (5 sites):
- `parseYamlRaw` [TokenParser.lean:920](L4YAML/TokenParser.lean#L920)
- `parseYaml` [TokenParser.lean:938](L4YAML/TokenParser.lean#L938)
- `parseYamlSingleRaw` [TokenParser.lean:948](L4YAML/TokenParser.lean#L948)
- `parseYamlSingle` [TokenParser.lean:962](L4YAML/TokenParser.lean#L962)
- `parseYamlWithComments` [TokenParser.lean:984](L4YAML/TokenParser.lean#L984)

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

### Phase 1: Create New Exception Types ✅ (2026-03-20)

**Files modified:**
- [Schema.lean](L4YAML/Schema.lean) — Added `SchemaError` (15 constructors), `YamlError` (2 constructors), `ToString`/`Coe` instances

**Design note:** Types placed in `Schema.lean` (not `Token.lean` as originally planned) because `SchemaError` references `Schema.YamlType` and `YamlValue`, which are defined in `Schema.lean` and `Types.lean` respectively. `Schema.lean` already imports `Types.lean`; adding `import L4YAML.Token` brings `ScanError` into scope for `YamlError`. This avoids pulling schema-layer dependencies into the scanner layer.

**Result:**
- Build: 334/334 jobs, 0 errors, 0 warnings, 0 sorry
- No breaking changes (additive only)
- Exception hierarchy foundation established

### Phase 2: Refactor Schema Layer ✅ (2026-03-20)

**Files modified:**

1. **[Schema.lean](L4YAML/Schema.lean)** — Added 2 new `SchemaError` constructors:
   - `notASequence (got : YamlValue)` — for `FromYaml` List/Array/Pair instances on raw `YamlValue`
   - `unknownVariant (got : String) (typeName : String)` — for derived enum deserialization

2. **[Schema/FromToYaml.lean](L4YAML/Schema/FromToYaml.lean)** — Typeclass signatures + all 11 instances:
   - `FromYamlType.fromYamlType?` : `Except String α` → `Except SchemaError α`
   - `FromYaml.fromYaml?` : `Except String α` → `Except SchemaError α`
   - All `.error s!"..."` → structured `SchemaError` constructors
   - `yamlTypeToString?` : `Except String` → `Except SchemaError`

3. **[Schema/Struct.lean](L4YAML/Schema/Struct.lean)** — All 4 helpers:
   - `getMapping`, `getString` : `Except String` → `Except SchemaError`
   - `getField`, `getFieldOpt` : `Except String` → `Except SchemaError`
   - `.error s!"{fieldName}: {msg}"` → `.error (.fieldConversionError fieldName e)`
   - `.error s!"missing required field..."` → `.error (.missingField fieldName)`

4. **[Schema/Deriving.lean](L4YAML/Schema/Deriving.lean)** — Enum error generation:
   - String error → `SchemaError.unknownVariant other "{typeName}"`

5. **[Schema/Api.lean](L4YAML/Schema/Api.lean)** — Bridge with `.mapError toString`:
   - `parseAs` and `parseTyped` keep `Except String` return type (parser still returns `Except String`)
   - Internal `fromYaml?` now returns `Except SchemaError`, bridged via `.mapError toString`
   - Will switch to `Except YamlError` in Phase 3 when parser returns `Except ScanError`

6. **[Schema/Dump.lean](L4YAML/Schema/Dump.lean)** — Bridge with `.mapError toString`:
   - `roundTripTyped` and `roundTripDiagnostics` keep `Except String` return type
   - Internal `fromYaml?` bridged via `.mapError toString`

**Design note:** `Api.lean` and `Dump.lean` cannot return `Except YamlError` yet because
`TokenParser.parseYamlSingle` still returns `Except String`. These will switch to
`Except YamlError` / `Except ScanError` in Phase 3 when the parser entry points change.

**Result:**
- Build: 334/334 jobs, 0 errors, 0 warnings, 0 sorry
- Schema layer fully uses `SchemaError` internally
- External API unchanged (`Except String`) — no downstream breakage yet

### Phase 3: Update Parser Entry Points ✅ (2026-03-20)

**Files modified:**

1. **[TokenParser.lean](L4YAML/TokenParser.lean)** — 5 public API functions:
   - `parseYamlRaw` : `Except String` → `Except ScanError` (removed `.toString` conversion)
   - `parseYaml` : `Except String` → `Except ScanError`
   - `parseYamlSingleRaw` : `Except String` → `Except ScanError`
   - `parseYamlSingle` : `Except String` → `Except ScanError`
   - `parseYamlWithComments` : `Except String` → `Except ScanError`
   - Simplified implementations: `.error e.toString` → `.error e` (no more string conversion)

2. **[Schema/Api.lean](L4YAML/Schema/Api.lean)** — Now uses `YamlError`:
   - `parseAs` : `Except String α` → `Except YamlError α`
     (lifts `ScanError` via `.mapError YamlError.scanError`,
      lifts `SchemaError` via `.mapError YamlError.schemaError`)
   - `parseTyped` : `Except String Schema.YamlType` → `Except ScanError Schema.YamlType`
     (pure schema resolution, no type conversion errors possible)

3. **[Schema/Dump.lean](L4YAML/Schema/Dump.lean)** — Now uses `YamlError`/`ScanError`/`SchemaError`:
   - `roundTripTyped` : `Except String α` → `Except YamlError α`
   - `roundTripDiagnostics` : `Except String (... × Except String α)` →
     `Except ScanError (... × Except SchemaError α)` (separate error types per layer)
   - `contentRoundTrips` : unchanged (returns `Bool`, error type is internal)

4. **[Proofs/Composition.lean](L4YAML/Proofs/Composition.lean)** — 3 theorem updates:
   - `parseYamlRaw_scan_error` : conclusion `.error e.toString` → `.error e`
   - `parseYamlRaw_parse_error` : conclusion `.error e.toString` → `.error e`
   - `parseYaml_of_parseYamlRaw_error` : `e : String` → `e : ScanError`

5. **[Proofs/EndToEndCorrectness.lean](L4YAML/Proofs/EndToEndCorrectness.lean)** — 1 proof simplified:
   - `parse_sound` : removed nested `split` (no more intermediate match on `parseStream`)

6. **Test files** — `ScanError` where `String` was expected:
   - [Tests/ExplicitKeyTests.lean](Tests/ExplicitKeyTests.lean) : `parseSingle` wrapper `Except String` → `Except ScanError` + 24 `checkM e` → `e.toString`
   - [Tests/FlowTests.lean](Tests/FlowTests.lean) : same pattern, 27 `checkM` sites
   - [Tests/SpecExamples.lean](Tests/SpecExamples.lean) : tuple `e` → `e.toString`
   - [Tests/ScannerSpecExamples.lean](Tests/ScannerSpecExamples.lean) : same
   - [Tests/ScalarStageDiag.lean](Tests/ScalarStageDiag.lean) : tuple `some e` → `some e.toString`
   - [Tests/RawParseTests.lean](Tests/RawParseTests.lean) : 16 `checkM` sites
   - [Demo.lean](Demo.lean) : 10 `checkM` sites

**Design notes:**
- `parseAs` is the first function to return `Except YamlError` — unifying `ScanError` + `SchemaError`
- Parser-only functions (`parseYaml`, `parseTyped`) return `Except ScanError` directly
- `roundTripDiagnostics` separates error types per pipeline stage for precise diagnostics
- Test files that use string interpolation `s!"{e}"` needed no changes since `ToString ScanError` exists
- Only `checkM` calls (passing error as `String` parameter) required `.toString`
- Proof simplification: `parse_sound` proof became shorter because `parseYamlRaw` no longer wraps `parseStream` in a redundant match

**Result:**
- Build: 334/334 jobs, 0 errors, 0 warnings, 0 sorry
- No more `Except String` in the public parser API
- All error types are now structured: `ScanError`, `SchemaError`, or `YamlError`

### Phase 4: Update Tests and Examples ✅ (2026-03-20)

Completed as part of Phase 3 — all test files updated to handle `ScanError`
instead of `String` in error branches. See Phase 3 file list above.

### Phase 5: Update Proofs ✅ (2026-03-20)

Completed as part of Phase 3 — proof updates were minimal:
- 3 theorem signatures/conclusions in Composition.lean
- 1 proof simplification in EndToEndCorrectness.lean
- All other proofs (Completeness.lean, ParserGrammable.lean, ScannerEmitBridge.lean,
  CommentProperties.lean, CommentRoundTrip.lean, etc.) required **no changes** — they
  only reference `.ok` branches or use `native_decide`, both unaffected by error type.

## Migration Example

### Before (Current)
```lean
-- Current API usage
match L4YAML.parseAs AppConfig yamlString with
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
match L4YAML.parseAs AppConfig yamlString with
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

The lean4-yaml-verified.iterators project contains extensive formal verification (45 proof modules, 1,589 theorems, ~750 `.error`/`.ok` occurrences). The exception type refactoring had **minimal impact** on the proof layer — far less than the pre-refactoring predictions anticipated.

### Actual Impact (Post-Refactoring)

#### 1. No Impact: Scanner/Parser Proofs (Majority)

**Status:** ✅ No changes needed

The scanner and parser layers already used structured `ScanError` types, so these proofs were unaffected:
- `Proofs/Scanner*.lean` (18 files) — Scanner correctness, progress, invariants
- `Proofs/Parser*.lean` (8 files) — Parser soundness, completeness, correctness

These represent the bulk of the verification effort (>80% of proof code) and **required zero changes**.

#### 2. No Impact: Schema Conversion Proofs

**Status:** ✅ No changes needed

Contrary to the pre-refactoring prediction of "⚠️ mechanical updates", these proofs required **no changes at all**:

- **[Proofs/SchemaDump.lean](L4YAML/Proofs/SchemaDump.lean)** — All error-matching uses wildcard `| .error _ =>`, so the error type change from `String` to `ScanError`/`SchemaError` was invisible to the proof.
- **[Proofs/SchemaResolution.lean](L4YAML/Proofs/SchemaResolution.lean)** — Only references the `Schema.resolve` function, which has no error-type dependency.

#### 3. Minimal Impact: Composition/End-to-End Proofs

**Status:** ✅ 3 theorem signatures + 1 proof simplification

The pre-refactoring prediction of "⚠️⚠️ theorem restructuring" proved far too pessimistic. Actual changes were trivial:

**[Proofs/Composition.lean](L4YAML/Proofs/Composition.lean)** — 3 type annotation updates:
```lean
-- parseYamlRaw_scan_error: conclusion `.error e.toString` → `.error e`
-- parseYamlRaw_parse_error: same
-- parseYaml_of_parseYamlRaw_error: `e : String` → `e : ScanError`
```
All three proofs remained `by simp only [...]` — no restructuring needed.

**[Proofs/EndToEndCorrectness.lean](L4YAML/Proofs/EndToEndCorrectness.lean)** — 1 proof simplification:
```lean
-- parse_sound: removed nested `split` since `parseYamlRaw` no longer wraps
-- `parseStream` in a redundant match (the `.mapError toString` wrapper was gone)
```
The proof became *simpler*, not more complex.

**No new error lifting lemmas were required** for existing proofs. The predicted need for `ScanError → YamlError` coercion properties in proof chains did not materialize because the composition proofs only span the scanner/parser pipeline (which uses `ScanError` uniformly).

#### 4. New Opportunities: Error-Specific Proofs

**Status:** ✅ Implemented in [Proofs/ErrorProperties.lean](L4YAML/Proofs/ErrorProperties.lean)

Structured errors enabled **new classes of proofs** previously impossible with `Except String`. These are now proven in the `ErrorProperties` module:

**Error Lifting Lemmas:**
- `coe_scan_error_toString` — coercion preserves `toString` (`rfl`)
- `coe_schema_error_toString` — coercion preserves `toString` (`rfl`)

**Discriminability:**
- `scan_error_ne_schema_error` — `YamlError.scanError se ≠ YamlError.schemaError sce`
- `yaml_error_scan_injective` — `scanError` constructor is injective
- `yaml_error_schema_injective` — `schemaError` constructor is injective

**Error Coverage (exact error characterization):**
- `getMapping_error` — `getMapping v = .error e → e = .notAMapping v`
- `getString_error` — `getString v = .error e → e = .notAScalar v`
- `fromYamlType_unit_error` — `Unit` conversion only produces `.expectedNull`
- `fromYamlType_bool_error` — `Bool` conversion only produces `.expectedBoolean`
- `fromYamlType_int_error` — `Int` conversion only produces `.expectedInteger`
- `fromYamlType_string_error` — `String` conversion only produces `.expectedString`
- `fromYamlType_nat_error` — `Nat` conversion produces `.expectedInteger` or `.negativeNat`

### Migration Retrospective

The pre-refactoring document predicted a four-phase incremental migration (Phases A–D) with parallel APIs and backwards-compatibility bridges. In practice, the direct migration was completed in a single pass:

- **Phase A** (define types): ✅ Done as planned
- **Phase B** (parallel APIs): Skipped — unnecessary. Direct signature changes compiled cleanly.
- **Phase C** (incremental proof updates): Skipped — only 4 proof changes were needed, all trivial.
- **Phase D** (remove old APIs): Skipped — there were no parallel APIs to remove.

The backwards-compatibility bridge (`oldProofCompat`, `yamlErrorToString`) was never needed. The `#guard`-based compile-time checks and all `native_decide` proofs were completely unaffected by the type changes.

### Proof Maintenance Burden (Actual)

| Category | Files | Changes | Risk |
|----------|-------|---------|------|
| Scanner proofs | 18 files | 0 | None |
| Parser proofs | 8 files | 0 | None |
| Schema proofs | 2 files | 0 | None |
| Composition/E2E | 2 files | 4 changes | Trivial |
| New error proofs | 1 file (new) | +12 theorems | Low |

**Total**: 4 existing proof changes + 12 new theorems added. Zero axioms, zero sorry, zero partial preserved.

### Zero Axiom Preservation

**Critical constraint:** The project maintains **zero axioms, zero sorry, zero partial**.

The exception refactoring **preserved this property**:
- All error types are inductive ADTs (fully defined, no axioms)
- `toString` functions are total (cover all constructors)
- Coercion instances are trivial wrappers (transparent)
- No `partial`, no `unsafe`, no `opaque` required
- The new `ErrorProperties.lean` module adds 12 theorems, all proven by `rfl`, `intro h; cases h`, or `by simp`

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
| 1. Create Types | ✅ done | 1 (Schema.lean) | No |
| 2. Schema Layer | ✅ done | 6 (Schema.lean + Schema/*) | Internal only |
| 3. Parser Layer | ✅ done | 7 (TokenParser + Api + Dump + Proofs) | Yes |
| 4. Tests/Examples | ✅ done | 7 (Tests/* + Demo) | No |
| 5. Proof Updates | ✅ done | 2 (Composition + EndToEnd) | No |
| **Total** | **✅ done** | **13 files** | **API only** |

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

- [Token.lean:237-311](L4YAML/Token.lean#L237-L311) — Existing `ScanError` design
- [Schema/FromToYaml.lean](L4YAML/Schema/FromToYaml.lean) — Schema typeclass layer
- [Schema/Struct.lean](L4YAML/Schema/Struct.lean) — Struct helper functions
- [Proofs/SchemaDump.lean](L4YAML/Proofs/SchemaDump.lean) — Round-trip proofs
- [Proofs/EndToEndCorrectness.lean](L4YAML/Proofs/EndToEndCorrectness.lean) — Integration proofs

## Conclusion

Refactoring to explicit exception types is a **high-value, manageable change** that:
- Strengthens type safety and formal verification
- Maintains zero axioms and totality
- Enables new classes of proofs
- Improves API usability

The proof impact is **largely mechanical** with opportunities for **stronger theorems**. The estimated 8-12 day effort is justified by long-term benefits to correctness, maintainability, and developer experience.
