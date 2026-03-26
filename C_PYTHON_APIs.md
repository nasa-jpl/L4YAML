# C and Python APIs for the safe YAML parser

Version 0.4.1 exposes the safe YAML parsing and dumping functionality (implemented in v0.3.0) through C and Python APIs, enabling non-Lean programs to use the verified parser with full security limit enforcement.

## Motivation

The parser is verified in Lean 4 and enforces security limits (DoS, tag validation) that no mainstream YAML library provides by default.  Exposing a C ABI makes the verified parser usable from **any** language with FFI, while a Python wrapper (the most common YAML attack surface) provides the highest-impact integration.

## Lean API Surface (reference)

### Safe Parsing — [Limits.lean](./Lean4Yaml/Limits.lean)

```lean
def parseYamlSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument)

def parseYamlSingleSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlValue

def parseYamlSingleRawSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlDocument
```

Presets: `ParserLimits.strict`, `.permissive`, `.unlimited`, `.safeTagsOnly`.

### Dumping — [Dump.lean](./Lean4Yaml/Dump.lean)

```lean
def dump (v : YamlValue) (cfg : DumpConfig := {}) : String
def dumpDocumentWithComments (doc : YamlDocument) (cfg : DumpConfig := {}) : String
def dumpDocumentsWithComments (docs : Array YamlDocument) (cfg : DumpConfig := {}) : String
```

---

## Design Constraint: Fixed-Size Memory Pool for Flight Software

Flight software (DO-178C, NASA Class A/B, ARINC 653) requires **no dynamic memory allocation after initialization**.  This constraint shaped every layer of the C/Python API design — the C header exposes pool initialization functions, the shim implements them via mimalloc's arena API, and the test plan includes pool exhaustion and fragmentation stress tests.

Lean 4's runtime uses reference-counted objects allocated via mimalloc, with no built-in "arena mode."  However, the mimalloc allocator bundled with Lean 4.28 (mimalloc v2.23) **does** export arena reservation and OS-alloc-disabling APIs — and these symbols are present in `libleanshared.so`.

### Solution: mimalloc Exclusive Arena

Lean 4.28's `libleanshared.so` exports every mimalloc API needed to implement a pre-allocated fixed-size memory pool.  The approach:

1. **At init time**: reserve a fixed-size OS memory region as a mimalloc arena
2. **Disable further OS allocation**: set `mi_option_disallow_os_alloc` so mimalloc can only use the pre-reserved arena
3. **All subsequent Lean allocations** (`mi_malloc_small`, `mi_malloc`) draw from the arena
4. **If the pool is exhausted**: mimalloc returns `NULL`, Lean calls `lean_internal_panic_out_of_memory()` — deterministic, no silent fallback

#### Verified exported symbols (Lean 4.28, `nm -D libleanshared.so`)

```
mi_reserve_os_memory_ex    — reserve N bytes as exclusive arena
mi_manage_os_memory_ex     — register caller-provided buffer as arena
mi_option_set              — set mimalloc option values
mi_option_get              — query mimalloc option values
mi_heap_new_in_arena       — create heap bound to specific arena
mi_arena_area              — query arena base/size
```

#### Pool allocation options

There are two ways to pre-allocate the memory pool.  Choose **one** based on your target environment.

##### Option A: OS-backed pool (`mi_reserve_os_memory_ex`)

For Linux, macOS, or any RTOS with `mmap` support.  mimalloc requests the pool from the OS at init time.

```c
mi_arena_id_t arena_id;
int err = mi_reserve_os_memory_ex(
    pool_bytes,     // e.g., 64 * 1024 * 1024 (64 MB)
    true,           // commit: map pages immediately
    false,          // allow_large: no huge pages
    true,           // exclusive: only this arena is used
    &arena_id       // out: arena identifier
);
if (err != 0) { /* handle init failure */ }
mi_option_set(mi_option_disallow_os_alloc, 1);
```

The C API wraps this as `lean4yaml_init_fixed_pool(size_t pool_bytes)`.

##### Option B: Link-time static buffer (`mi_manage_os_memory_ex`)

For bare-metal or RTOS targets without `mmap`.  A buffer is allocated at link time in the `.bss` section (or provided by a BSP allocator).

```c
static char yaml_pool[64 * 1024 * 1024]
    __attribute__((aligned(4096)));   // .bss — zero cost at load time

mi_arena_id_t arena_id;
mi_manage_os_memory_ex(
    yaml_pool, sizeof(yaml_pool),
    true,   // committed
    false,  // not large pages
    true,   // zero-initialized (static storage)
    0,      // NUMA node
    true,   // exclusive
    &arena_id
);
mi_option_set(mi_option_disallow_os_alloc, 1);
```

The C API wraps this as `lean4yaml_init_static_pool(void *buf, size_t buf_bytes)`.

##### Sequencing

After either option, call `lean4yaml_initialize()` to start the Lean runtime.  All Lean allocations (`mi_malloc_small`, `mi_malloc`) will be confined to the pre-reserved arena:

```
Option A or B  →  lean4yaml_initialize()  →  lean4yaml_parse() ...
```

#### How it works

Lean's small-object allocator calls `mi_malloc_small(sz)` (see [lean.h line 358](https://github.com/leanprover/lean4)):

```c
// From lean/lean.h — lean_alloc_small_object (LEAN_MIMALLOC path)
sz = lean_align(sz, LEAN_OBJECT_SIZE_DELTA);  // 8-byte alignment
void * mem = mi_malloc_small(sz);              // ← uses default thread heap
```

When `mi_option_disallow_os_alloc == 1`, mimalloc's internal page allocator **cannot** request new segments from the OS.  All allocations are satisfied from the pre-reserved arena.  If the arena is exhausted, `mi_malloc_small` returns `NULL` → `lean_internal_panic_out_of_memory()`.

Large objects (> 4096 bytes) go through `mi_malloc()` in `lean_alloc_object()`, which follows the same arena constraint.

#### Two-layer memory protection: `ParserLimits` + arena cap

The safe parsing API (`parseYamlSafe`) enforces resource limits **before** allocation:

| Limit | Default | Effect |
|---|---|---|
| `maxInputBytes` | 100 MB | Rejects oversized input before parsing starts |
| `maxTotalNodes` | 1,000,000 | Caps tree size during construction |
| `maxResolvedNodes` | 100,000 | Caps alias expansion |
| `maxScalarBytes` | 10 MB | Caps individual scalar allocation |
| `maxSequenceLength` | 100,000 | Caps per-collection size |
| `maxDepth` | 100 | Caps recursion depth |

By choosing `ParserLimits.strict` (or custom limits), the **worst-case memory usage is bounded at the application level** before mimalloc ever sees the allocation.  This gives two layers of protection:

1. **Application layer**: `ParserLimits` rejects inputs that would require too much memory
2. **Runtime layer**: mimalloc arena cap guarantees hard memory ceiling

This two-layer model is why the C header exposes both `lean4yaml_init_fixed_pool` (runtime layer) and limit presets like `LEAN4YAML_LIMITS_STRICT` (application layer) — they are designed to work together.

#### Pool sizing

A conservative estimate for pool size given `ParserLimits l`:

```
pool_bytes ≥ lean_runtime_overhead                       (~2 MB)
           + l.document.maxInputBytes                    (input copy)
           + l.structural.maxTotalNodes × avg_node_bytes (~80 bytes/node)
           + l.structural.maxScalarBytes                 (largest scalar)
           + mimalloc_metadata_overhead                  (~5% of pool)
```

For `ParserLimits.strict`: ~2 MB + 10 MB + 10K×80 + 10 MB + overhead ≈ **25 MB** is sufficient.
For default limits: ~2 MB + 100 MB + 1M×80 + 10 MB + overhead ≈ **200 MB**.

#### Caveats

1. **Must call before `lean_initialize_runtime_module()`**.  Lean's init allocates persistent objects (string constants, closures).  These go into the arena too.
2. **Thread-local heaps**.  Each thread gets its own mimalloc heap.  In single-threaded flight software this is not an issue.  For multi-threaded use, all threads share the same arena but have independent heaps within it.
3. **`mi_option_disallow_os_alloc` is global**.  Once set, no mimalloc allocation in the process can fall back to OS memory.  This is the desired behavior for flight software.
4. **No compaction / defragmentation**.  mimalloc does not compact.  Over many parse-free cycles, fragmentation can reduce usable pool capacity.  Mitigation: size the pool with margin (2× worst-case), or parse in a subprocess/forked process for complete isolation.
5. **`lean_internal_panic_out_of_memory()` behavior**.  By default this calls `abort()`.  For flight software, override with `lean_set_exit_on_panic(false)` and install a custom panic handler via `lean_set_panic_fn` (if available), or wrap the parse call in a subprocess with watchdog.

#### Usage Synopsis

Complete initialization-to-parse sequences for both C and Python.

##### C API — Option A (OS-backed pool)

```c
#include "lean4yaml.h"

int main(void) {
    // 1. Reserve 64 MB OS-backed pool
    lean4yaml_init_fixed_pool(64 * 1024 * 1024);

    // 2. Initialize Lean runtime (allocations go to the pool)
    lean4yaml_initialize();

    // 3. Parse YAML with strict limits
    const char *input = "name: Apollo\nstatus: nominal\n";
    lean4yaml_result_t r = lean4yaml_parse(
        input, strlen(input), LEAN4YAML_LIMITS_STRICT);

    if (lean4yaml_result_is_ok(r)) {
        lean4yaml_docs_t docs = lean4yaml_result_docs(r);
        lean4yaml_doc_t  doc  = lean4yaml_docs_get(docs, 0);
        lean4yaml_value_t root = lean4yaml_doc_root(doc);

        // Navigate the mapping
        lean4yaml_value_t name = lean4yaml_value_lookup(root, "name");
        printf("name = %s\n", lean4yaml_value_string(name));

        lean4yaml_free(name);
        lean4yaml_free(root);
        lean4yaml_free(doc);
        lean4yaml_free(docs);
    } else {
        fprintf(stderr, "parse error: %s\n",
                lean4yaml_result_error_message(r));
    }

    lean4yaml_free(r);
    lean4yaml_finalize();
    return 0;
}
```

##### C API — Option B (static buffer)

```c
#include "lean4yaml.h"

static char yaml_pool[32 * 1024 * 1024]
    __attribute__((aligned(4096)));   // 32 MB in .bss

int main(void) {
    // 1. Register the static buffer as the sole arena
    lean4yaml_init_static_pool(yaml_pool, sizeof(yaml_pool));

    // 2. Initialize Lean runtime
    lean4yaml_initialize();

    // 3. Parse (identical to Option A from here on)
    const char *input = "items:\n  - alpha\n  - bravo\n";
    lean4yaml_result_t r = lean4yaml_parse_single(
        input, strlen(input), LEAN4YAML_LIMITS_STRICT);

    if (lean4yaml_result_is_ok(r)) {
        lean4yaml_value_t val = lean4yaml_result_value(r);
        lean4yaml_value_t seq = lean4yaml_value_lookup(val, "items");
        uint32_t n = lean4yaml_value_seq_length(seq);
        for (uint32_t i = 0; i < n; i++) {
            lean4yaml_value_t item = lean4yaml_value_seq_get(seq, i);
            printf("  [%u] %s\n", i, lean4yaml_value_string(item));
            lean4yaml_free(item);
        }
        lean4yaml_free(seq);
        lean4yaml_free(val);
    } else {
        fprintf(stderr, "parse error: %s\n",
                lean4yaml_result_error_message(r));
    }

    lean4yaml_free(r);
    lean4yaml_finalize();
    return 0;
}
```

##### Python API

The Python package wraps the C API via `ctypes`.  Pool initialization (Option A) is available for memory-constrained ground systems; most Python users will skip it and let mimalloc allocate from the OS normally.

```python
import lean4yaml

# Optional: pre-allocate a fixed pool (Option A)
lean4yaml.init_pool(64 * 1024 * 1024)   # 64 MB; omit for default behavior

# Parse a single document with strict limits
value = lean4yaml.load("name: Apollo\nstatus: nominal\n", limits="strict")
assert value.kind == "mapping"
print(value["name"].as_str())       # → "Apollo"
print(value["status"].as_str())     # → "nominal"

# Parse multiple documents
yaml_stream = """---
alpha: 1
---
bravo: 2
"""
docs = lean4yaml.load_all(yaml_stream, limits="strict")
for doc in docs:
    print(doc.root.as_dict())

# Dump back to YAML
print(lean4yaml.dump(value))

# Error handling
try:
    lean4yaml.load(malicious_input, limits="strict")
except lean4yaml.LimitError as e:
    print(f"Security limit exceeded: {e}")
except lean4yaml.ParseError as e:
    print(f"Syntax error: {e}")
```

Pool initialization is **not needed** for Option B from Python — static buffers are a C/link-time concern for embedded targets.

---

## Architecture

```
┌──────────────────────────────────────────────────────────┐
│  Lean 4  (verified core)                                 │
│  Lean4Yaml/Limits.lean   — parseYamlSafe, etc.           │
│  Lean4Yaml/Dump.lean     — dump, dumpDocument*, etc.     │
│  Lean4Yaml/FFI.lean      — @[export] wrappers            │
└────────────────┬─────────────────────────────────────────┘
                 │  Lean 4 @[export] → C symbol
                 ▼
┌──────────────────────────────────────────────────────────┐
│  C ABI  (liblean4yaml.so / .dylib / .a)                  │
│  ffi/lean4yaml.h         — public header                 │
│  ffi/lean4yaml_shim.c    — thin C helpers (optional)     │
└────────────────┬─────────────────────────────────────────┘
                 │  dlopen / ctypes / cffi
                 ▼
┌──────────────────────────────────────────────────────────┐
│  Python  (lean4yaml package)                             │
│  python/lean4yaml/__init__.py  — high-level API          │
│  python/lean4yaml/_ffi.py      — cffi / ctypes bindings  │
│  python/lean4yaml/types.py     — YamlValue, etc.         │
└──────────────────────────────────────────────────────────┘
```

---

## Phase 1: Lean `@[export]` Wrappers (`Lean4Yaml/FFI.lean`)

Create a new module that wraps the safe API into C-callable functions using Lean 4's `@[export]` attribute.  Every exported function operates on opaque handles or flat C-compatible types (pointers, `uint32_t`, `const char *`).

### Design: opaque handle model

Lean objects are GC-managed.  The C API uses **opaque handles** (`lean_object *` cast to `void *` on the C side) with explicit `retain`/`release` calls.  This avoids copying the full recursive `YamlValue` tree across the FFI boundary — instead, C/Python code navigates the tree via accessor functions.

### Exported functions

| Lean `@[export]` name | C signature | Description |
|---|---|---|
| `lean4yaml_parse_safe` | `lean_obj_res lean4yaml_parse_safe(b_lean_obj_arg input, uint8_t preset)` | Parse UTF-8 string with preset limits (0=default, 1=strict, 2=permissive, 3=unlimited, 4=safeTagsOnly). Returns opaque result handle. |
| `lean4yaml_parse_single_safe` | `lean_obj_res lean4yaml_parse_single_safe(b_lean_obj_arg input, uint8_t preset)` | Single-document variant. Returns opaque `YamlValue` or error. |
| `lean4yaml_result_is_ok` | `uint8_t lean4yaml_result_is_ok(b_lean_obj_arg result)` | 1 if parse succeeded, 0 if error. |
| `lean4yaml_result_get_error` | `lean_obj_res lean4yaml_result_get_error(b_lean_obj_arg result)` | Extract error message as Lean `String`. |
| `lean4yaml_result_get_value` | `lean_obj_res lean4yaml_result_get_value(b_lean_obj_arg result)` | Extract the `YamlValue` handle from an ok result. |
| `lean4yaml_result_get_docs` | `lean_obj_res lean4yaml_result_get_docs(b_lean_obj_arg result)` | Extract `Array YamlDocument` handle from multi-doc ok result. |
| `lean4yaml_docs_count` | `uint32_t lean4yaml_docs_count(b_lean_obj_arg docs)` | Number of documents in array. |
| `lean4yaml_docs_get` | `lean_obj_res lean4yaml_docs_get(b_lean_obj_arg docs, uint32_t i)` | Get i-th document handle. |
| `lean4yaml_doc_value` | `lean_obj_res lean4yaml_doc_value(b_lean_obj_arg doc)` | Root `YamlValue` of a document. |
| **Value inspection** | | |
| `lean4yaml_value_tag` | `uint8_t lean4yaml_value_tag(b_lean_obj_arg val)` | Node kind: 0=scalar, 1=sequence, 2=mapping, 3=alias. |
| `lean4yaml_value_as_string` | `lean_obj_res lean4yaml_value_as_string(b_lean_obj_arg val)` | Scalar content as Lean `String` (or null). |
| `lean4yaml_value_seq_length` | `uint32_t lean4yaml_value_seq_length(b_lean_obj_arg val)` | Sequence item count. |
| `lean4yaml_value_seq_get` | `lean_obj_res lean4yaml_value_seq_get(b_lean_obj_arg val, uint32_t i)` | i-th sequence element. |
| `lean4yaml_value_map_length` | `uint32_t lean4yaml_value_map_length(b_lean_obj_arg val)` | Mapping pair count. |
| `lean4yaml_value_map_key` | `lean_obj_res lean4yaml_value_map_key(b_lean_obj_arg val, uint32_t i)` | i-th key. |
| `lean4yaml_value_map_val` | `lean_obj_res lean4yaml_value_map_val(b_lean_obj_arg val, uint32_t i)` | i-th value. |
| `lean4yaml_value_lookup` | `lean_obj_res lean4yaml_value_lookup(b_lean_obj_arg val, b_lean_obj_arg key)` | Mapping key lookup (returns `Option YamlValue` handle). |
| `lean4yaml_value_yaml_tag` | `lean_obj_res lean4yaml_value_yaml_tag(b_lean_obj_arg val)` | Tag string (or null). |
| `lean4yaml_value_anchor` | `lean_obj_res lean4yaml_value_anchor(b_lean_obj_arg val)` | Anchor name (or null). |
| **Dumping** | | |
| `lean4yaml_dump` | `lean_obj_res lean4yaml_dump(b_lean_obj_arg val)` | Dump `YamlValue` → YAML `String` (default config). |
| `lean4yaml_dump_docs` | `lean_obj_res lean4yaml_dump_docs(b_lean_obj_arg docs)` | Dump `Array YamlDocument` → YAML `String`. |
| **Lifecycle** | | |
| `lean4yaml_string_to_cstr` | `const char * lean4yaml_string_to_cstr(b_lean_obj_arg s)` | Extract `const char *` (UTF-8) from Lean `String`. Pointer valid while handle is live. |
| `lean4yaml_string_byte_length` | `uint32_t lean4yaml_string_byte_length(b_lean_obj_arg s)` | UTF-8 byte length. |
| `lean4yaml_retain` | `void lean4yaml_retain(lean_obj_arg obj)` | Increment reference count. |
| `lean4yaml_release` | `void lean4yaml_release(lean_obj_arg obj)` | Decrement reference count (may free). |

### Preset encoding

| `uint8_t` | Lean value |
|---|---|
| 0 | `ParserLimits` (default) |
| 1 | `ParserLimits.strict` |
| 2 | `ParserLimits.permissive` |
| 3 | `ParserLimits.unlimited` |
| 4 | `ParserLimits.safeTagsOnly` |

Custom `ParserLimits` with per-field configuration is deferred to a later version (would require a builder-pattern API or struct passing).

---

## Phase 2: C Header & Shared Library (`ffi/`)

### `ffi/lean4yaml.h`

```c
#ifndef LEAN4YAML_H
#define LEAN4YAML_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque handles — callers must not dereference */
typedef void *lean4yaml_result_t;
typedef void *lean4yaml_value_t;
typedef void *lean4yaml_docs_t;
typedef void *lean4yaml_doc_t;
typedef void *lean4yaml_string_t;

/* Limit presets */
#define LEAN4YAML_LIMITS_DEFAULT      0
#define LEAN4YAML_LIMITS_STRICT       1
#define LEAN4YAML_LIMITS_PERMISSIVE   2
#define LEAN4YAML_LIMITS_UNLIMITED    3
#define LEAN4YAML_LIMITS_SAFE_TAGS    4

/* Node kinds */
#define LEAN4YAML_SCALAR    0
#define LEAN4YAML_SEQUENCE  1
#define LEAN4YAML_MAPPING   2
#define LEAN4YAML_ALIAS     3

/* Initialize / finalize Lean runtime */
void lean4yaml_initialize(void);
void lean4yaml_finalize(void);

/*
 * Fixed-size memory pool initialization (flight software).
 * Call ONE of these BEFORE lean4yaml_initialize().
 * See "Design Constraint: Fixed-Size Memory Pool" section.
 */
/* Option A: OS-backed pool (mimalloc reserves via mmap) */
int lean4yaml_init_fixed_pool(size_t pool_bytes);
/* Option B: Caller-provided static buffer (bare-metal / RTOS) */
int lean4yaml_init_static_pool(void *buf, size_t buf_bytes);

/* Parsing */
lean4yaml_result_t lean4yaml_parse(const char *input, size_t len, uint8_t preset);
lean4yaml_result_t lean4yaml_parse_single(const char *input, size_t len, uint8_t preset);

/* Result inspection */
uint8_t lean4yaml_result_is_ok(lean4yaml_result_t r);
const char *lean4yaml_result_error_message(lean4yaml_result_t r);

/* Multi-document access */
lean4yaml_docs_t lean4yaml_result_docs(lean4yaml_result_t r);
uint32_t lean4yaml_docs_count(lean4yaml_docs_t docs);
lean4yaml_doc_t lean4yaml_docs_get(lean4yaml_docs_t docs, uint32_t i);
lean4yaml_value_t lean4yaml_doc_root(lean4yaml_doc_t doc);

/* Single-document access */
lean4yaml_value_t lean4yaml_result_value(lean4yaml_result_t r);

/* Value inspection */
uint8_t lean4yaml_value_kind(lean4yaml_value_t v);
const char *lean4yaml_value_string(lean4yaml_value_t v);
uint32_t lean4yaml_value_seq_length(lean4yaml_value_t v);
lean4yaml_value_t lean4yaml_value_seq_get(lean4yaml_value_t v, uint32_t i);
uint32_t lean4yaml_value_map_length(lean4yaml_value_t v);
lean4yaml_value_t lean4yaml_value_map_key(lean4yaml_value_t v, uint32_t i);
lean4yaml_value_t lean4yaml_value_map_val(lean4yaml_value_t v, uint32_t i);
lean4yaml_value_t lean4yaml_value_lookup(lean4yaml_value_t v, const char *key);
const char *lean4yaml_value_tag(lean4yaml_value_t v);
const char *lean4yaml_value_anchor(lean4yaml_value_t v);

/* Dumping */
const char *lean4yaml_dump(lean4yaml_value_t v);
const char *lean4yaml_dump_docs(lean4yaml_docs_t docs);

/* Memory management */
void lean4yaml_free(void *handle);

#ifdef __cplusplus
}
#endif

#endif /* LEAN4YAML_H */
```

### `ffi/lean4yaml_shim.c`

Thin C wrapper that:
1. Calls `lean_initialize_runtime_module()` and `lean_init_task_manager()` from `lean4yaml_initialize()`.
2. Converts `const char *` + `size_t` → Lean `String` via `lean_mk_string_from_bytes`.
3. Converts Lean `String` → `const char *` via `lean_string_cstr`.
4. Wraps `lean_dec` behind `lean4yaml_free` for a uniform cleanup API.
5. Implements `lean4yaml_init_fixed_pool()` — calls `mi_reserve_os_memory_ex` + `mi_option_set(mi_option_disallow_os_alloc, 1)` before `lean_initialize_runtime_module()`.
6. Implements `lean4yaml_init_static_pool()` — calls `mi_manage_os_memory_ex` on caller-provided buffer (for bare-metal / RTOS targets without `mmap`).

### Build integration

Build via CMake after `lake build Lean4Yaml` has generated the IR C files:

```sh
lake build Lean4Yaml          # generate .lake/build/ir/*.c
cmake -B ffi/out -S ffi       # configure (auto-detects Lean sysroot via elan)
cmake --build ffi/out          # compile 76 IR files + shim → liblean4yaml.so
```

Or with a custom Lean sysroot:
```sh
cmake -B ffi/out -S ffi -DLEAN_SYSROOT=/path/to/lean
cmake --build ffi/out
```

Deliverables: `liblean4yaml.so` (Linux), `liblean4yaml.dylib` (macOS).

---

## Phase 3: Python Package (`python/lean4yaml/`)

### Package structure

```
python/
├── pyproject.toml
├── lean4yaml/
│   ├── __init__.py       # Public API: load, load_safe, dump
│   ├── _ffi.py           # ctypes bindings to liblean4yaml.so
│   ├── types.py          # YamlValue, YamlDocument, YamlScalar dataclasses
│   └── exceptions.py     # ParseError, LimitError, TagSecurityError
└── tests/
    ├── test_parse.py
    ├── test_dump.py
    ├── test_limits.py
    └── test_roundtrip.py
```

### Python API design

```python
import lean4yaml

# Safe parse (default limits) — recommended
docs = lean4yaml.load_all(yaml_string)
value = lean4yaml.load(yaml_string)

# Strict limits for web APIs
value = lean4yaml.load(yaml_string, limits="strict")

# Dump back to YAML
output = lean4yaml.dump(value)

# Value navigation
assert value.kind == "mapping"
name = value["name"].as_str()
items = value["items"].as_list()

# Error handling
try:
    lean4yaml.load(malicious_input, limits="strict")
except lean4yaml.LimitError as e:
    print(f"Security limit hit: {e}")
except lean4yaml.ParseError as e:
    print(f"Syntax error: {e}")
```

### Type mapping

| Lean type | Python type |
|---|---|
| `YamlValue.scalar` | `YamlValue` with `.kind == "scalar"`, `.as_str()` → `str` |
| `YamlValue.sequence` | `YamlValue` with `.kind == "sequence"`, `len()`, `__getitem__(int)` |
| `YamlValue.mapping` | `YamlValue` with `.kind == "mapping"`, `__getitem__(str)`, `.keys()`, `.items()` |
| `YamlValue.alias` | Resolved before reaching Python (safe API resolves aliases) |
| `Array YamlDocument` | `list[YamlDocument]` |
| `Except ParseError _` | `return value` or `raise ParseError(...)` |
| `ParserLimits preset` | `limits="default"` / `"strict"` / `"permissive"` / `"unlimited"` / `"safe_tags"` |

### `YamlValue` class

```python
class YamlValue:
    """Immutable YAML value backed by an opaque Lean handle."""

    @property
    def kind(self) -> str: ...          # "scalar" | "sequence" | "mapping"

    def as_str(self) -> str: ...        # scalar content (raises if not scalar)
    def as_list(self) -> list: ...      # sequence items (raises if not sequence)
    def as_dict(self) -> dict: ...      # mapping as Python dict (string keys only)

    @property
    def tag(self) -> str | None: ...    # YAML tag
    @property
    def anchor(self) -> str | None: ... # YAML anchor name

    def __getitem__(self, key): ...     # mapping[str] or sequence[int]
    def __len__(self) -> int: ...       # sequence/mapping length
    def __iter__(self): ...             # iterate items/pairs
    def __contains__(self, key): ...    # mapping key membership
    def __repr__(self) -> str: ...      # lean4yaml.dump(self)

    def __del__(self):
        """Release the underlying Lean handle."""
        ...
```

### Memory management

The `YamlValue` Python object holds a Lean `lean_object *` handle obtained from the C API.  `__del__` calls `lean4yaml_free`.  To prevent use-after-free, child values obtained via `__getitem__` call `lean4yaml_retain` on the child handle.  The `lean4yaml_result_t` returned by `parse` is freed after extracting the value/error.

### PyYAML compatibility shim (optional, deferred)

A `lean4yaml.compat` module could provide `yaml.safe_load` / `yaml.safe_dump` signatures backed by the verified parser, enabling drop-in replacement.  This is a stretch goal, not part of the initial v0.4.1 scope.

---

## Phase 4: Testing

### C API tests (`ffi/test_lean4yaml.c`)

- Parse valid YAML, navigate value tree, verify scalar content
- Parse invalid YAML, verify error messages
- Parse billion-laugh payload with `STRICT` preset, verify `LimitError`
- Parse `!!python/object` tag with default limits, verify `TagSecurityError`
- Multi-document parsing, verify document count and per-doc navigation
- Dump round-trip: parse → dump → re-parse → structural equality
- Memory leak check: parse, navigate, free; check under Valgrind/ASan

### Fixed-pool tests (`ffi/test_lean4yaml_pool.c`)

- Pool exhaustion: `lean4yaml_init_fixed_pool(64 * 1024)` (tiny), parse moderate input, verify deterministic OOM (not hang/crash)
- Static buffer variant: `lean4yaml_init_static_pool(buf, sizeof(buf))`, parse valid YAML, verify success
- Fragmentation stress: 10,000 parse→free cycles with `ParserLimits.strict`, verify pool remains usable
- Pool sizing validation: pool sized per formula from appendix, parse worst-case input for each limit preset, verify no OOM
- No-OS-alloc enforcement: after `init_fixed_pool`, verify `mi_option_get(mi_option_disallow_os_alloc) == 1`

### Python tests (`python/tests/`)

- `test_parse.py` — valid inputs, navigation, error cases
- `test_limits.py` — preset limits reject billion-laugh, oversized input, dangerous tags
- `test_dump.py` — round-trip fidelity, scalar style preservation
- `test_roundtrip.py` — parse → dump → parse identity for yaml-test-suite valid cases

### Cross-validation

Run the yaml-test-suite (311 valid + 158 invalid cases) through the Python API and compare results against the existing Lean `suiterunner`.  The 869/0/151 pass/fail/skip baseline must be preserved.

---

## Task Checklist

### Phase 1: Lean `@[export]` Wrappers

| # | Task | Status |
|---|------|--------|
| 1 | Create `Lean4Yaml/FFI.lean` with `@[export]` wrappers for safe parse + dump + value navigation | ☑ |
| 2 | Verify `FFI.lean` compiles and exports appear in `.o` symbol table | ☑ |

### Phase 2: C Header & Shared Library

| # | Task | Status |
|---|------|--------|
| 3 | Create `ffi/lean4yaml.h` public C header (including `lean4yaml_init_fixed_pool`, `lean4yaml_init_static_pool`) | ☑ |
| 4 | Create `ffi/lean4yaml_shim.c` (runtime init, string conversion, free, pool init) | ☑ |
| 5 | Create `ffi/CMakeLists.txt` to compile IR + shim → `liblean4yaml.so` | ☑ |
| 6 | Build shared library, verify symbols with `nm -D` | ☑ |

### Phase 3: Python Package

| # | Task | Status |
|---|------|--------|
| 7 | Create `python/lean4yaml/` package (`_ffi.py`, `types.py`, `exceptions.py`, `__init__.py`) | ☐ |
| 8 | Create `python/tests/test_*.py`, run pytest | ☐ |

### Phase 4: Testing & Validation

| # | Task | Status |
|---|------|--------|
| 9 | Create `ffi/test_lean4yaml.c`, compile and run C API tests | ☐ |
| 10 | Create `ffi/test_lean4yaml_pool.c`, compile and run fixed-pool tests | ☐ |
| 11 | Cross-validate Python API against yaml-test-suite (869/0/151 baseline) | ☐ |
| 12 | Valgrind/ASan pass on C test binary (standard + pool modes) | ☐ |
| 13 | Pool fragmentation stress test: 10,000 parse-free cycles | ☐ |
| 14 | Document pool sizing formula in header comments and README | ☐ |
| 15 | Update README.md v0.4.1 section with results | ☐ |
| 16 | Prototype on VxWorks/RTEMS target (stretch goal) | ☐ |

---

## Risks and Mitigations

| Risk | Impact | Mitigation |
|---|---|---|
| Lean 4.28 `@[export]` ABI stability | Symbol names or calling convention changes across Lean versions | Pin `lean-toolchain` to v4.28.0; test on CI |
| GC interaction with long-lived C handles | Lean GC may relocate objects if handles are not properly retained | Use `lean_inc_ref` / `lean_dec_ref` consistently; all exported functions use `b_lean_obj_arg` (borrowed) or `lean_obj_arg` (consumed) correctly |
| Python `__del__` non-determinism | Handles may outlive the Lean runtime if Python shutdown order is wrong | Register an `atexit` hook to finalize Lean runtime after all handles are freed |
| Thread safety | Lean runtime is single-threaded by default | Document that all calls must be from a single thread, or initialize Lean's task manager for multi-threaded use |
| Large input copies across FFI boundary | Copying multi-MB strings is wasteful | Use `lean_mk_string_from_bytes` which takes ownership of the buffer; Python `ctypes` passes pointer directly |
| **Pool exhaustion during parse** | `lean_internal_panic_out_of_memory()` calls `abort()` | Size pool conservatively (2× worst-case from `ParserLimits`); use `ParserLimits.strict` to cap application-level allocation before it reaches mimalloc |
| **Fragmentation over repeated parse cycles** | Usable pool shrinks over time | Size pool with 2× headroom; consider subprocess isolation for long-running systems |
| **mimalloc arena API stability** | mimalloc bundled version may change across Lean releases | Pin Lean toolchain; arena APIs have been stable since mimalloc v2.0 |
| **Bare-metal `lean_initialize_runtime_module`** | Lean runtime assumes POSIX environment (threads, mmap, signals) | For true bare-metal, a custom Lean runtime fork is needed; for RTOS with POSIX layer (VxWorks, RTEMS), the standard runtime works with `mi_manage_os_memory_ex` |
