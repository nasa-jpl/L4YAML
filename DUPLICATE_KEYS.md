# Handling of Duplicate Keys in YAML Mappings

## Motivation

YAML 1.2.2 §3.2.1.3 (Node Comparison) specifies that mapping keys **MUST** be
unique, but delegates key equality semantics to the application:

> "Since YAML mappings require key uniqueness, representations must include a
> mechanism for testing the equality of nodes. This is non-trivial since YAML
> allows various ways to format scalar content. For example, the integer eleven
> can be written as `0o13` (octal) or `0xB` (hexadecimal). If both notations
> are used as keys in the same mapping, only a YAML processor which recognizes
> integer formats would correctly flag the duplicate key as an error."

The spec further requires:

> "Two scalars are equal only when their **tags and canonical forms** are equal
> character-by-character. Equality of collections is defined recursively."

This means key equality is **schema-dependent** — the parser alone cannot fully
determine it.  A failsafe-schema parser compares raw string content; a
core-schema processor must resolve `0o13` and `0xB` to their canonical integer
form before comparing.  Application-specific schemas may impose further rules.

This is precisely the kind of problem Lean 4's type system excels at: we can
express the key equality contract as a typeclass with proof obligations, ensure
handlers are well-typed, and verify that the output satisfies uniqueness
relative to the provided equivalence — all within the same language that
implements the parser.

## Current State

| Layer | Behavior with duplicates | Semantics |
|-------|--------------------------|-----------|
| Scanner / TokenParser | Silently accepts all | All pairs preserved in `Array (YamlValue × YamlValue)` |
| Lean `findField` / `lookup?` | `findSome?` | **First-wins** |
| C `l4yaml_value_lookup` | `findSome?` | **First-wins** |
| Python `as_dict()` | Dict assignment | **Last-wins** |
| `validateStructure` | Checks `maxMappingSize` only | No uniqueness check |

There is an existing **first-wins vs last-wins inconsistency** between the
Lean/C and Python layers, independent of this feature.

## Design

### Three-Component Architecture

The design separates three orthogonal concerns:

1. **Key equality predicate** — how does the application define "same key"?
2. **Duplicate resolution handler** — what to do when a duplicate is found?
3. **Diagnostic result** — report all duplicates found alongside the resolved value.

This maps directly to the spec's delegation model: the parser provides the
mechanism; the application provides the policy.

### Component 1: Key Equality Predicate with Proof Obligations

The key equality predicate determines when two `YamlValue` nodes represent
"the same key."  To meaningfully prove that the output has unique keys, the
predicate must be an equivalence relation.  Without transitivity, "uniqueness"
is ill-defined — the result of the deduplication fold would depend on
encounter order.

```lean
/-- A key equality predicate with proof that it forms an equivalence relation.
    This is the typeclass constraint that applications must satisfy to get
    verified unique-key guarantees.

    The default instance (`defaultKeyEq`) compares `(tag, content)` pairs
    of scalar keys character-by-character, matching the spec's failsafe
    schema definition.  Schema-aware instances can resolve canonical forms
    before comparison. -/
class KeyEqPred (keyEq : YamlValue → YamlValue → Bool) where
  /-- Reflexivity: every key is equal to itself. -/
  refl  : ∀ k, keyEq k k = true
  /-- Symmetry: equality is direction-independent. -/
  symm  : ∀ a b, keyEq a b = true → keyEq b a = true
  /-- Transitivity: equality chains.  Without this, uniqueness after
      folding is order-dependent and cannot be stated as a proposition. -/
  trans : ∀ a b c, keyEq a b = true → keyEq b c = true → keyEq a c = true
```

This is a Lean typeclass, meaning:
- Applications can provide custom instances for schema-aware comparison.
- Proof obligations are checked at compile time.
- The uniqueness theorem is *parametric* over any lawful `KeyEqPred`.

#### Built-in predicates

| Predicate | Compares | Use case |
|-----------|----------|----------|
| `defaultScalarEq` | `(tag, content)` pairs of scalar keys | Failsafe schema (default) |
| `contentOnlyEq` | Scalar content only, ignoring tags | Quick-and-dirty, most common real-world use |
| `coreSchemaEq` | Resolved canonical forms under core schema | Full spec compliance for `!!int`, `!!float`, etc. |

```lean
/-- Default: compare scalar tag × content pairs.
    Non-scalar keys (sequences, mappings used as keys) compare structurally
    via the existing `BEq YamlValue` instance. -/
def defaultScalarEq (a b : YamlValue) : Bool :=
  match a, b with
  | .scalar sa, .scalar sb => sa.tag == sb.tag && sa.content == sb.content
  | _, _ => a == b  -- fall back to structural BEq for collection keys

instance : KeyEqPred defaultScalarEq where
  refl  := by intro k; cases k <;> simp [defaultScalarEq, BEq.beq]
  symm  := by intro a b; cases a <;> cases b <;> simp [defaultScalarEq] <;> omega
  trans := by intro a b c; cases a <;> cases b <;> cases c <;>
              simp [defaultScalarEq] <;> intro h1 h2 <;> exact h1 ▸ h2
```

### Component 2: Monadic Duplicate Resolution Handler

When a duplicate key is detected during the fold, the handler decides what the
mapping should contain.  The handler is monadic to support both pure resolution
(first-wins, last-wins) and effectful resolution (error, logging).

```lean
/-- Context passed to the duplicate key handler when a conflict is detected
    during the deduplication fold over a mapping's pairs. -/
structure DuplicateKeyContext where
  /-- YAML path to the mapping node containing the duplicate. -/
  mappingPath : YamlPath
  /-- The key already present in the accumulator. -/
  existingKey : YamlValue
  /-- The value associated with the existing key. -/
  existingVal : YamlValue
  /-- The newly encountered key (equal to `existingKey` under `keyEq`). -/
  newKey      : YamlValue
  /-- The newly encountered value. -/
  newVal      : YamlValue

/-- Information recorded for each duplicate key encountered, regardless of
    the handler's resolution decision. -/
structure DuplicateKeyInfo where
  mappingPath : YamlPath
  key         : YamlValue
  firstValue  : YamlValue
  laterValue  : YamlValue
```

#### Built-in handlers

```lean
/-- Keep the first occurrence; discard later duplicates.
    Matches the behavior of Lean `findField` / C `l4yaml_value_lookup`. -/
def firstKeyHandler (ctx : DuplicateKeyContext)
    : Except String (YamlValue × YamlValue) :=
  .ok (ctx.existingKey, ctx.existingVal)

/-- Keep the last occurrence; overwrite earlier entries.
    Matches Python `as_dict()` / ruamel.yaml `allow_duplicate_keys=False`. -/
def lastKeyHandler (ctx : DuplicateKeyContext)
    : Except String (YamlValue × YamlValue) :=
  .ok (ctx.newKey, ctx.newVal)

/-- Reject: return an error on the first duplicate found.
    This is the default handler (spec-compliant). -/
def rejectHandler (ctx : DuplicateKeyContext)
    : Except String (YamlValue × YamlValue) :=
  .error s!"duplicate key at {ctx.mappingPath}: {reprKey ctx.existingKey}"

/-- Accept silently: keep all pairs as-is (no deduplication).
    This is a no-op — the mapping retains its original `Array` unmodified.
    Equivalent to ruamel.yaml `allow_duplicate_keys=True`. -/
def keepAllHandler : DuplicateKeyConfig := { onDuplicate := none }
```

### Component 3: Configuration and Result Types

```lean
/-- Configuration for duplicate key handling, passed alongside ParserLimits.
    Kept separate from ParserLimits because this is a semantic concern
    (interpretation), not a resource concern (DoS prevention). -/
structure DuplicateKeyConfig where
  /-- The key equality predicate.  Default compares (tag, content) pairs. -/
  keyEq       : YamlValue → YamlValue → Bool := defaultScalarEq
  /-- Handler called for each duplicate.  `none` means keep all pairs
      (no deduplication pass). -/
  onDuplicate : Option (DuplicateKeyContext → Except String (YamlValue × YamlValue))
                := some rejectHandler

/-- Result of duplicate key resolution: the resolved tree plus diagnostics. -/
structure DuplicateKeyResult where
  /-- The YAML value tree with mappings resolved per the handler. -/
  value      : YamlValue
  /-- Every duplicate key encountered during the walk, regardless of
      handler outcome.  Applications can use this for warnings, auditing,
      or CW16-style diagnostics. -/
  duplicates : Array DuplicateKeyInfo

/-- Top-level configuration wrapping both resource limits and semantic config. -/
structure ParserConfig where
  limits        : ParserLimits := {}
  duplicateKeys : DuplicateKeyConfig := {}  -- default: reject duplicates
```

### Core Algorithm: `resolveDuplicateKeys`

A recursive tree walk.  At each `.mapping` node, fold over `pairs` building
a deduplicated accumulator:

```lean
/-- Resolve duplicate keys throughout a YAML value tree.

    For each mapping node, folds over its pairs array.  For each (k, v):
    1. Scan the accumulator for an existing entry where `config.keyEq existing k = true`.
    2. If found: record a `DuplicateKeyInfo`, call `config.onDuplicate`, replace/keep
       according to the handler's return value.
    3. If not found: append (k, v) to the accumulator.

    Recurses into nested values (including mapping values and sequence items)
    to resolve duplicates at all nesting depths. -/
def resolveDuplicateKeys (config : DuplicateKeyConfig) (root : YamlValue)
    : Except String DuplicateKeyResult := ...
```

### Pipeline Integration

The resolution step sits **after** composition and validation, as a separate
function — not folded into `validateStructure` or `composeLimited`:

```
  input string
    → parse (Scanner → TokenParser)        -- syntactic
    → compose (resolve aliases)            -- structural
    → validateStructure (resource limits)  -- safety
    → resolveDuplicateKeys (semantic)      -- NEW: key uniqueness
    → return DuplicateKeyResult
```

Entry points gain an optional `DuplicateKeyConfig` parameter:

```lean
def parseYamlSingleSafe (input : String) (limits : ParserLimits := {})
    (dupConfig : DuplicateKeyConfig := {})
    : Except String DuplicateKeyResult := ...
```

## Proof Obligations and Impact

### Tier 0: Zero Impact (Unchanged Files)

| Component | Why untouched |
|-----------|---------------|
| Scanner (2,309 theorems) | Produces tokens — no concept of keys/values |
| TokenParser proofs (`parseBlockMapping_ag`, `parseFlowMapping_ag`) | Accumulates raw pairs — no semantic check |
| `ParserNodeProofs` | Proves fuel consumption + well-formedness, not key semantics |
| Composition proofs | `composeLimited` pipeline unchanged — dup resolution is a separate downstream step |

**All existing proofs remain completely untouched.**

### Tier 1: New Self-Contained Proof Module

A new `L4YAML/Proofs/DuplicateKeyProofs.lean` with **zero dependency** on
existing proof files.  These are proofs about `resolveDuplicateKeys` and its
helpers:

| Theorem | Statement |
|---------|-----------|
| `resolveDuplicateKeys_unique` | If `KeyEqPred keyEq` holds, output mapping keys are pairwise non-equal under `keyEq` |
| `firstKeyHandler_subset` | Output pairs ⊆ input pairs (first occurrence of each key class) |
| `lastKeyHandler_subset` | Output pairs ⊆ input pairs (last occurrence of each key class) |
| `rejectHandler_iff` | Returns `.error` ↔ input has at least one duplicate key under `keyEq` |
| `resolveDuplicateKeys_preserves_non_mapping` | Scalars and sequences pass through unchanged |
| `resolveDuplicateKeys_recursive` | Nested mappings are also resolved |
| `defaultScalarEq_equiv` | `defaultScalarEq` satisfies `KeyEqPred` |
| `resolveDuplicateKeys_idempotent` | Applying resolution twice yields the same result |
| `resolveDuplicateKeys_diagnostics_complete` | Every duplicate in the input appears in `result.duplicates` |

#### Central Uniqueness Theorem

```lean
/-- The main correctness theorem: if the key equality predicate is a lawful
    equivalence relation (via `KeyEqPred`), then every mapping in the resolved
    output has pairwise-distinct keys.

    This is parametric over any `keyEq` satisfying the typeclass — the same
    theorem covers default scalar comparison, core-schema canonical forms,
    and any future application-specific predicate. -/
theorem resolveDuplicateKeys_unique
    {keyEq : YamlValue → YamlValue → Bool}
    [KeyEqPred keyEq]
    (config : DuplicateKeyConfig)
    (h_eq : config.keyEq = keyEq)
    (h_handler : config.onDuplicate.isSome)
    (h_ok : resolveDuplicateKeys config val = .ok result)
    : ∀ pairs ∈ allMappingPairs result.value,
        ∀ i j, i < pairs.size → j < pairs.size → i ≠ j →
          keyEq pairs[i].1 pairs[j].1 = false := by
  -- Proof sketch:
  -- Induction on the structure of `val`.
  -- At each mapping: induction on the fold over pairs.
  -- Base: empty accumulator — trivially unique.
  -- Step: adding (k, v) — either:
  --   (a) k matches existing entry → handler replaces, array size unchanged,
  --       uniqueness preserved by IH.
  --   (b) k is fresh → "not found" scan result means ∀ existing, keyEq existing k = false.
  --       Append preserves pairwise distinctness (IH + fresh).
  --       Transitivity of keyEq is needed to ensure the "not found" scan
  --       result is consistent across all prior entries.
  sorry -- TODO: fill in
```

The proof structure is a standard `Array.foldl` induction — no dependent types,
no fuel, no scanner state.  These will be among the cleanest proofs in the
project.

### Tier 2: Minor Integration Plumbing

- Entry point signatures gain `DuplicateKeyConfig` parameter (additive change).
- `ToString` for error types may need a new arm if `StructuralLimitError` gains
  a constructor (minimal).
- Any theorem of the form "parseYamlSafe returns `.ok` → property" needs to
  account for the new pipeline step, but this is mechanical — it's a function
  composition, not a change to existing logic.

### Tier 3: Equivalence Relation Proofs (Deferrable)

The `KeyEqPred` instances for built-in predicates need their three laws proved:

| Instance | Difficulty | Notes |
|----------|-----------|-------|
| `defaultScalarEq` | Easy | String `BEq` is decidable equality; tag comparison likewise |
| `contentOnlyEq` | Easy | Same, ignoring tag field |
| `coreSchemaEq` | Medium | Requires proving canonical form normalization is idempotent and injective |

These can be deferred — the implementation works without them, and the
uniqueness theorem simply requires the typeclass instance to exist at the
call site.

## FFI and API Surface

### C API

```c
// New configuration handle
void *l4yaml_dupkey_config_new(void);
void  l4yaml_dupkey_config_set_policy(void *cfg, int policy);
  // 0 = reject (default), 1 = keep_first, 2 = keep_last, 3 = keep_all

// Extended parse function
void *l4yaml_parse_single_safe_ex(const char *input, void *limits, void *dupkey_cfg);

// Diagnostic access
int   l4yaml_dupkey_result_count(void *result);
void *l4yaml_dupkey_result_get(void *result, int index);
```

### Python API (ruamel.yaml parity)

```python
import l4yaml

# Default: reject duplicates (spec-compliant)
doc = l4yaml.load("{a: 1, b: 2}")

# Permissive: keep all pairs (ruamel allow_duplicate_keys=True)
doc = l4yaml.load("{a: 1, a: 2}", allow_duplicate_keys=True)

# Last-wins normalization (ruamel allow_duplicate_keys=False behavior)
result = l4yaml.load("{a: 1, a: 2}", duplicate_key_policy="last")
assert result.as_dict() == {"a": 2}

# Access diagnostics
result = l4yaml.load("{a: 1, a: 2}", duplicate_key_policy="last")
for dup in result.duplicate_keys:
    print(f"Duplicate at {dup.path}: {dup.key}")
```

### Mapping to ruamel.yaml

| ruamel.yaml | l4yaml | Handler |
|-------------|-----------|---------|
| `allow_duplicate_keys=False` (default) | `duplicate_key_policy="reject"` (default) | `rejectHandler` |
| `allow_duplicate_keys=True` | `allow_duplicate_keys=True` | `keepAllHandler` (no dedup) |
| — | `duplicate_key_policy="first"` | `firstKeyHandler` |
| — | `duplicate_key_policy="last"` | `lastKeyHandler` |

## Implementation Plan

### Phase 1: Types and Config (no proof impact)

1. Define `KeyEqPred` typeclass in `L4YAML/DuplicateKeys.lean`
2. Define `DuplicateKeyContext`, `DuplicateKeyInfo`, `DuplicateKeyConfig`,
   `DuplicateKeyResult`
3. Implement `defaultScalarEq`, `firstKeyHandler`, `lastKeyHandler`,
   `rejectHandler`
4. Add `FromYaml` / `ToYaml` instances in `Config.lean`
5. Define `ParserConfig` wrapper

### Phase 2: Core Algorithm

6. Implement `resolveDuplicateKeys` — recursive tree walk with fold
7. Integrate into entry points (`parseYamlSingleSafe`, `parseYamlSafe`)
8. Add `#guard` tests in `Tests/Guards/DuplicateKeyGuards.lean`

### Phase 3: FFI and Python

9. C API extensions in `ffi/l4yaml.h` and `ffi/l4yaml_shim.c`
10. Python bindings: `allow_duplicate_keys` and `duplicate_key_policy` params
11. Python tests in `Tests/test_python_ffi.py`

### Phase 4: Proofs

12. `KeyEqPred defaultScalarEq` instance with proofs
13. `resolveDuplicateKeys_unique` — central uniqueness theorem
14. Handler correctness lemmas (`_subset`, `_iff`)
15. Diagnostics completeness (`_diagnostics_complete`)

### Phase 5: Extended Predicates (future)

16. `coreSchemaEq` with canonical form normalization
17. `KeyEqPred coreSchemaEq` instance
18. Application-specific predicate examples / documentation

## Files

| File | Change | Impact |
|------|--------|--------|
| `L4YAML/DuplicateKeys.lean` | **NEW** | Core types, algorithm, built-in handlers |
| `L4YAML/Config.lean` | Add `FromYaml`/`ToYaml` for new types | Additive |
| `L4YAML/Limits.lean` | Add `ParserConfig` wrapper | Additive |
| `L4YAML/FFI.lean` | New `@[export]` functions | Additive |
| `L4YAML/Proofs/DuplicateKeyProofs.lean` | **NEW** | Self-contained proof module |
| `Tests/Guards/DuplicateKeyGuards.lean` | **NEW** | Compile-time `#guard` checks |
| `Tests/test_python_ffi.py` | Add duplicate key test class | Additive |
| `ffi/l4yaml.h` | New C API functions | Additive |
| `ffi/l4yaml_shim.c` | Shim implementations | Additive |
| `python/l4yaml/__init__.py` | New params on `load()` | Additive |
| Scanner.lean, TokenParser.lean, all Proofs/* | **UNCHANGED** | Zero impact |

## Design Decisions

- **Separate from `ParserLimits`**: Duplicate key handling is a semantic concern
  (interpretation), not a resource concern (DoS prevention).  The two are
  orthogonal and should not be conflated.
- **`KeyEqPred` as typeclass**: Lean's typeclass resolution provides
  compile-time proof checking.  Applications that want verified unique-key
  guarantees must supply an equivalence relation.  Applications that just want
  pragmatic deduplication can use the built-in instances.
- **Handler is `Except`-based**: Covers reject (error), first/last-wins (pure
  `.ok`), and logging (via `StateT` transformer) uniformly.
- **`resolveDuplicateKeys` is a separate pipeline step**: Not embedded in
  `validateStructure` or `composeLimited`.  This architectural choice is what
  gives us zero impact on existing proofs.
- **Default is `rejectHandler`**: Spec-compliant.  Matches ruamel.yaml default.
- **`defaultScalarEq` compares `(tag, content)`**: Matches the spec's
  requirement that "two scalars are equal only when their tags and canonical
  forms are equal."  For the failsafe schema, the canonical form IS the raw
  content.
- **Diagnostics always collected**: Even when using `lastKeyHandler` (which
  silently resolves), the `DuplicateKeyResult.duplicates` array records every
  conflict.  This enables CW16-style warnings without requiring a separate pass.
- **Fix first-wins/last-wins inconsistency**: As a follow-up, add `lookupLast?`
  to `Types.lean` and make `as_dict()` semantics explicit.
