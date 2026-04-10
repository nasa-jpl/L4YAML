# YAML Value Merge: Algebraic Semantics

## Motivation

Configuration systems routinely need to combine multiple YAML files —
defaults with overrides, base configs with environment-specific layers,
shared templates with local customizations.  Today this is handled by
ad-hoc scripts or language-specific libraries (Python `deepmerge`,
Kubernetes strategic merge patches, Helm value overlays) with no formal
specification of merge behavior.

We define `merge : YamlValue → YamlValue → YamlValue` with precise
algebraic laws, provable in Lean 4, that guarantee predictable behavior
across any number of layered configurations.

## Required Algebraic Laws

The merge operation must satisfy three properties:

### 1. Idempotence (Reflexivity)

```
∀ y : YamlValue, merge y y = y
```

Merging a document with itself produces itself — no duplication, no
structural inflation.  This is the essential safety property for
configuration layering: applying the same overlay twice is harmless.

### 2. Antisymmetry (Argument Order Matters)

```
∀ y₁ y₂ : YamlValue, merge y₁ y₂ = merge y₂ y₁ → y₁ = y₂
```

Merge is **not** commutative — the right argument takes precedence on
conflicts.  This is exactly the override semantics that configuration
layering requires: `merge(defaults, overrides)` is different from
`merge(overrides, defaults)`.  The two results coincide only when the
inputs are equal.

### 3. Associativity

```
∀ y₁ y₂ y₃ : YamlValue, merge y₁ (merge y₂ y₃) = merge (merge y₁ y₂) y₃
```

Multi-file merges can be folded left or right with the same result.
This enables `foldl merge base [layer1, layer2, layer3]` without
worrying about evaluation order.  Essential for composable pipelines.

### Algebraic Structure

Together, these three laws make `(YamlValue, merge)` a **band** (idempotent
semigroup) that is *right-biased* and *anti-commutative*.  This is the
standard algebraic structure for override-merge in configuration management.

## Design

### Merge Semantics by Node Kind

The merge is defined by structural recursion on the pair `(left, right)`:

| Left | Right | Result | Rationale |
|------|-------|--------|-----------|
| any | `y` (same kind + tag) | deep merge | Recurse structurally |
| scalar | scalar | right wins | Right-biased override |
| sequence | sequence | right wins | Sequences are atomic — no element-wise merge (see Design Decisions) |
| mapping | mapping | deep key merge | Union of keys; on conflict, recursively merge values |
| any | different kind | right wins | Kind mismatch = replacement |

### Core Definition

```lean
/-- Right-biased deep merge of YAML value trees.

    Forms an idempotent semigroup (band) on `YamlValue`:
    - `merge_idempotent : merge y y = y`
    - `merge_assoc : merge y₁ (merge y₂ y₃) = merge (merge y₁ y₂) y₃`
    - `merge_antisymm : merge y₁ y₂ = merge y₂ y₁ → y₁ = y₂`

    For mappings, keys are matched using `keyEq` and values are merged
    recursively.  For all other node kinds, the right argument wins. -/
def merge (keyEq : YamlValue → YamlValue → Bool) [KeyEqPred keyEq]
    : YamlValue → YamlValue → YamlValue
  | .mapping st₁ pairs₁ tag₁ anc₁, .mapping st₂ pairs₂ tag₂ anc₂ =>
    if tag₁ == tag₂ then
      let merged := mergeMappingPairs keyEq pairs₁ pairs₂
      .mapping st₂ merged tag₂ anc₂
    else
      .mapping st₂ pairs₂ tag₂ anc₂  -- tag mismatch: right wins entirely
  | _, right => right

where
  /-- Merge two mapping pair arrays.

      Start with `left` pairs.  For each pair `(k₂, v₂)` in `right`:
      - If `left` contains `(k₁, v₁)` with `keyEq k₁ k₂ = true`:
        replace with `(k₂, merge keyEq v₁ v₂)` (recursive).
      - Otherwise: append `(k₂, v₂)` to the result.

      This preserves the order of `left` keys, appending new `right` keys
      at the end. -/
  mergeMappingPairs (keyEq : YamlValue → YamlValue → Bool)
      (left right : Array (YamlValue × YamlValue))
      : Array (YamlValue × YamlValue) :=
    right.foldl (init := left) fun acc (k₂, v₂) =>
      match acc.findIdx? (fun (k₁, _) => keyEq k₁ k₂) with
      | some idx =>
        let (_, v₁) := acc[idx]!
        acc.set! idx (k₂, merge keyEq v₁ v₂)
      | none => acc.push (k₂, v₂)
```

### Relationship to `KeyEqPred` (Duplicate Keys)

The merge operation reuses the `KeyEqPred` typeclass from
[DUPLICATE_KEYS.md](DUPLICATE_KEYS.md).  The same key equality predicate
determines both:

- When two keys in a single mapping are "duplicates"
- When a key in the right document "overrides" a key in the left document

This is not coincidental — the merge of two mappings must produce a mapping
with unique keys (under `keyEq`), which is exactly the duplicate-key contract.

**Theorem**: If both inputs have unique keys (under `keyEq`) and `KeyEqPred keyEq`
holds, then `merge keyEq y₁ y₂` has unique keys.

### Merge Configuration

```lean
/-- Configuration for YAML merge operations. -/
structure MergeConfig where
  /-- Key equality predicate for matching mapping keys across documents. -/
  keyEq : YamlValue → YamlValue → Bool := defaultScalarEq
  /-- Strategy for sequence merging.  Default: right-wins (atomic replace).
      Alternative strategies can be provided for specific use cases. -/
  sequenceStrategy : SequenceMergeStrategy := .replace
  /-- Whether to merge across different tags.  Default: false (tag mismatch
      means right wins entirely).  If true, merge structurally regardless
      of tag differences. -/
  mergeAcrossTags : Bool := false

/-- Strategy for merging sequences. -/
inductive SequenceMergeStrategy where
  /-- Right sequence replaces left entirely (default).
      Required for associativity — element-wise strategies break it. -/
  | replace
  /-- Append right elements after left elements.
      WARNING: satisfies associativity but NOT idempotence. -/
  | append
  /-- Concatenate and deduplicate (by value equality).
      WARNING: satisfies idempotence but NOT associativity. -/
  | union
```

Only `SequenceMergeStrategy.replace` satisfies all three laws simultaneously.
The alternatives are provided for practical use cases where applications
accept weaker guarantees, but the proof obligations are adjusted accordingly.

## Proof Obligations

### Core Theorems

| Theorem | Statement | Difficulty |
|---------|-----------|------------|
| `merge_idempotent` | `merge keyEq y y = y` | Medium — structural induction on `YamlValue`, mapping case needs `foldl` idempotence over identical pairs |
| `merge_assoc` | `merge keyEq y₁ (merge keyEq y₂ y₃) = merge keyEq (merge keyEq y₁ y₂) y₃` | Hard — the mapping case requires showing `foldl` over merged pairs is associative, using `KeyEqPred.trans` |
| `merge_antisymm` | `merge keyEq y₁ y₂ = merge keyEq y₂ y₁ → y₁ = y₂` | Hard — contrapositive: if `y₁ ≠ y₂`, exhibit a difference preserved by the right-bias |
| `merge_preserves_uniqueness` | If both inputs have unique keys under `keyEq`, so does the output | Medium — `foldl` preserves the no-duplicate invariant |

### Proof Strategy

**Idempotence** is the most approachable:
- Scalar/sequence/alias cases: `merge y y = y` by definition (right wins = same value).
- Mapping case: `tag₁ == tag₂` is `true` (same tag). Then show `mergeMappingPairs keyEq pairs pairs = pairs`:
  - By `foldl` induction: each `(k, v)` from `right` finds its match in `acc` at the same position (by `KeyEqPred.refl`), replaces with `(k, merge keyEq v v)` which equals `(k, v)` by IH.

**Associativity** requires the key insight that `mergeMappingPairs` acts like
a right-biased association table update, and `foldl` over such updates is
associative when the lookup predicate is an equivalence relation.  Specifically:

```
mergeMappingPairs keyEq (mergeMappingPairs keyEq p₁ p₂) p₃
  = mergeMappingPairs keyEq p₁ (mergeMappingPairs keyEq p₂ p₃)
```

This follows from:
1. `findIdx?` with a transitive `keyEq` produces the same match regardless
   of whether keys were inserted via merge from `p₁` or `p₂`.
2. Recursive merge on values is associative by induction hypothesis.
3. `KeyEqPred.trans` ensures that if `k₁ ≡ k₂` and `k₂ ≡ k₃`, the merged
   key from `p₁ ∪ p₂` still matches `k₃`.

**Antisymmetry** is proved by contrapositive:
- If `y₁ ≠ y₂`, there exists some structural difference.
- Scalar/sequence: `merge y₁ y₂ = y₂` and `merge y₂ y₁ = y₁`, so
  `y₂ ≠ y₁` implies `merge y₁ y₂ ≠ merge y₂ y₁`.
- Mapping: if key sets differ, one merge appends keys the other doesn't (order
  changes). If a shared key has different values, the right-bias means the two
  merges produce different values for that key.

### Proof Dependencies

```
KeyEqPred.refl  ──→ merge_idempotent
KeyEqPred.trans ──→ merge_assoc
KeyEqPred.symm  ──→ merge_antisymm
                    merge_preserves_uniqueness
```

All three `KeyEqPred` laws are needed — this validates the typeclass design
from the duplicate keys work.

## Interaction with YAML `<<` Merge Key

The YAML 1.1 merge key `<<` (https://yaml.org/type/merge.html) is a
**different** concept:

| Aspect | `<<` merge key | `merge(y₁, y₂)` |
|--------|----------------|-------------------|
| Scope | Within a single document | Across documents |
| Trigger | Special key `<<` with alias value | Explicit API call |
| Spec status | YAML 1.1 type; **not** in YAML 1.2.2 core schema | Application-level operation |
| Implementation | Expand during composition (resolve aliases first) | Post-parse pipeline step |

The `<<` key is currently treated as a literal string key by the parser
(correct for YAML 1.2.2).  Support for `<<` as a merge directive would be a
separate feature — an optional composition step that expands `<<` entries
before the value tree is returned.

The `merge(y₁, y₂)` operation defined here operates on fully composed,
alias-resolved value trees.

## API Surface

### Lean API

```lean
/-- Merge two YAML values with default configuration (right-biased, reject
    on key equality using `defaultScalarEq`). -/
def YamlValue.merge (left right : YamlValue) : YamlValue :=
  L4YAML.merge defaultScalarEq left right

/-- Merge two YAML values with custom key equality. -/
def YamlValue.mergeWith (keyEq : YamlValue → YamlValue → Bool) [KeyEqPred keyEq]
    (left right : YamlValue) : YamlValue :=
  L4YAML.merge keyEq left right

/-- Merge a base document with a sequence of overlay documents. -/
def YamlValue.mergeAll (keyEq : YamlValue → YamlValue → Bool) [KeyEqPred keyEq]
    (base : YamlValue) (overlays : Array YamlValue) : YamlValue :=
  overlays.foldl (L4YAML.merge keyEq) base
```

### C API

```c
// Merge two parsed YAML values
void *l4yaml_merge(void *left, void *right);
void *l4yaml_merge_with_config(void *left, void *right, void *merge_cfg);

// Merge multiple documents
void *l4yaml_merge_all(void **docs, int count, void *merge_cfg);
```

### Python API

```python
import l4yaml

base = l4yaml.load("base.yaml")
overlay = l4yaml.load("overlay.yaml")

# Right-biased deep merge
result = l4yaml.merge(base, overlay)

# Merge multiple layers (left fold)
result = l4yaml.merge_all(base, [layer1, layer2, layer3])

# With custom config
result = l4yaml.merge(base, overlay, key_equality="content_only")
```

## Examples

### Basic Override

```yaml
# base.yaml
server:
  host: localhost
  port: 8080
  debug: false

# overlay.yaml
server:
  port: 9090
  debug: true
  tls: true
```

```
merge(base, overlay) =
  server:
    host: localhost    # from base (no conflict)
    port: 9090         # from overlay (right wins)
    debug: true        # from overlay (right wins)
    tls: true          # from overlay (new key appended)
```

### Associativity in Practice

```yaml
# defaults.yaml          # env.yaml              # local.yaml
server:                   server:                  server:
  host: 0.0.0.0            host: prod.example.com   port: 3000
  port: 8080                port: 443
  debug: false              debug: false
```

Both evaluation orders produce the same result:

```
merge(defaults, merge(env, local))
  = merge(merge(defaults, env), local)
  = server:
      host: prod.example.com
      port: 3000
      debug: false
```

### Idempotence

```
merge(config, config) = config    -- always, for any config
```

This guarantees that accidentally applying the same layer twice is harmless.

## Implementation Plan

### Phase 1: Core Merge (depends on DuplicateKeys Phase 1)

1. Define `merge` and `mergeMappingPairs` in `L4YAML/Merge.lean`
2. Reuse `KeyEqPred` from `L4YAML/DuplicateKeys.lean`
3. Define `MergeConfig` and `SequenceMergeStrategy`
4. Add `#guard` tests in `Tests/Guards/MergeGuards.lean`

### Phase 2: Proofs

5. Prove `merge_idempotent` — structural induction + `foldl` lemma
6. Prove `merge_assoc` — `foldl` associativity under `KeyEqPred.trans`
7. Prove `merge_antisymm` — contrapositive argument
8. Prove `merge_preserves_uniqueness`

### Phase 3: FFI and Python

9. C API in `ffi/l4yaml_shim.c`
10. Python bindings: `merge()`, `merge_all()`
11. Python tests

### Phase 4: Extended (future)

12. `<<` merge key expansion as optional composition step
13. Strategic merge patches (Kubernetes-style `$patch: delete`)
14. Conflict reporting — return `MergeResult` with diagnostics alongside value

## Files

| File | Change | Impact |
|------|--------|--------|
| `L4YAML/Merge.lean` | **NEW** | Core merge algorithm + config types |
| `L4YAML/Proofs/MergeProofs.lean` | **NEW** | All merge theorems |
| `L4YAML/FFI.lean` | New `@[export]` functions | Additive |
| `Tests/Guards/MergeGuards.lean` | **NEW** | Compile-time `#guard` tests |
| `Tests/test_python_ffi.py` | Add merge tests | Additive |
| `ffi/l4yaml.h` | New C API functions | Additive |
| `ffi/l4yaml_shim.c` | Shim implementations | Additive |
| `python/l4yaml/__init__.py` | `merge()`, `merge_all()` | Additive |
| Scanner, TokenParser, all Proofs/* | **UNCHANGED** | Zero impact |

## Design Decisions

- **Sequences are atomic (right-wins)**: Element-wise sequence merge breaks
  associativity.  `merge([a,b], [c]) = [a,b,c]` but then
  `merge([a,b,c], [d])` appends `d`, while `merge([a,b], merge([c],[d]))` =
  `merge([a,b], [c,d])` = `[a,b,c,d]`.  The only strategy satisfying all
  three laws for sequences is atomic replacement.  Alternative strategies
  (`append`, `union`) are available for applications that accept weaker
  guarantees.

- **Right-biased, not left-biased**: The convention `merge(base, overlay)` is
  universal in configuration management (Helm, Kustomize, Nix, etc.).
  Right-bias means "later layers win," matching natural reading order:
  `merge(defaults, env_specific, local_overrides)`.

- **Tag mismatch = replacement**: If the left mapping has `!!myapp/config` and
  the right has `!!myapp/secrets`, they represent different schemas — deep
  merging would be meaningless.  `mergeAcrossTags` can be set to `true`
  for applications that ignore tags.

- **Style from right**: The merged mapping takes the `CollectionStyle` from
  the right (overlay) document.  The right document is the "most recent"
  specification of how the mapping should be presented.

- **Reuses `KeyEqPred`**: A single typeclass governs key identity across
  duplicate detection and merging — no risk of inconsistent key comparison
  between the two features.

- **`merge` is total**: No `Except`, no `Option` — merge always succeeds.
  This is a deliberate departure from `resolveDuplicateKeys` which can fail
  (via `rejectHandler`).  Merge is a pure structural combination; errors
  belong to the validation layer.
