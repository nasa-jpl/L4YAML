# C, Python, and Rust APIs for the safe YAML parser

Version 0.5.0 exposes the safe YAML parsing and dumping functionality (implemented in v0.3.0) through C, Python, and Rust APIs, enabling non-Lean programs to use the verified parser with full security limit enforcement.

## Motivation

The parser is verified in Lean 4 and enforces security limits (DoS, tag validation) that no mainstream YAML library provides by default.  Exposing a C ABI makes the verified parser usable from **any** language with FFI, while a Python wrapper (the most common YAML attack surface) provides the highest-impact integration.

## Lean API Surface (reference)

### Safe Parsing — [Limits.lean](./L4YAML/Limits.lean)

```lean
def parseYamlSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError (Array YamlDocument)

def parseYamlSingleSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlValue

def parseYamlSingleRawSafe (input : String) (limits : ParserLimits := {})
    : Except ParseError YamlDocument
```

Presets: `ParserLimits.strict`, `.permissive`, `.unlimited`, `.safeTagsOnly`.

### Dumping — [Dump.lean](./L4YAML/Dump.lean)

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

The C API wraps this as `l4yaml_init_fixed_pool(size_t pool_bytes)`.

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

The C API wraps this as `l4yaml_init_static_pool(void *buf, size_t buf_bytes)`.

##### Sequencing

After either option, call `l4yaml_initialize()` to start the Lean runtime.  All Lean allocations (`mi_malloc_small`, `mi_malloc`) will be confined to the pre-reserved arena:

```
Option A or B  →  l4yaml_initialize()  →  l4yaml_parse() ...
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

This two-layer model is why the C header exposes both `l4yaml_init_fixed_pool` (runtime layer) and limit presets like `L4YAML_LIMITS_STRICT` (application layer) — they are designed to work together.

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
#include "l4yaml.h"

int main(void) {
    // 1. Reserve 64 MB OS-backed pool
    l4yaml_init_fixed_pool(64 * 1024 * 1024);

    // 2. Initialize Lean runtime (allocations go to the pool)
    l4yaml_initialize();

    // 3. Parse YAML with strict limits
    const char *input = "name: Apollo\nstatus: nominal\n";
    l4yaml_result_t r = l4yaml_parse(
        input, strlen(input), L4YAML_LIMITS_STRICT);

    if (l4yaml_result_is_ok(r)) {
        l4yaml_docs_t docs = l4yaml_result_docs(r);
        l4yaml_doc_t  doc  = l4yaml_docs_get(docs, 0);
        l4yaml_value_t root = l4yaml_doc_root(doc);

        // Navigate the mapping
        l4yaml_value_t name = l4yaml_value_lookup(root, "name");
        printf("name = %s\n", l4yaml_value_string(name));

        l4yaml_free(name);
        l4yaml_free(root);
        l4yaml_free(doc);
        l4yaml_free(docs);
    } else {
        fprintf(stderr, "parse error: %s\n",
                l4yaml_result_error_message(r));
    }

    l4yaml_free(r);
    l4yaml_finalize();
    return 0;
}
```

##### C API — Option B (static buffer)

```c
#include "l4yaml.h"

static char yaml_pool[32 * 1024 * 1024]
    __attribute__((aligned(4096)));   // 32 MB in .bss

int main(void) {
    // 1. Register the static buffer as the sole arena
    l4yaml_init_static_pool(yaml_pool, sizeof(yaml_pool));

    // 2. Initialize Lean runtime
    l4yaml_initialize();

    // 3. Parse (identical to Option A from here on)
    const char *input = "items:\n  - alpha\n  - bravo\n";
    l4yaml_result_t r = l4yaml_parse_single(
        input, strlen(input), L4YAML_LIMITS_STRICT);

    if (l4yaml_result_is_ok(r)) {
        l4yaml_value_t val = l4yaml_result_value(r);
        l4yaml_value_t seq = l4yaml_value_lookup(val, "items");
        uint32_t n = l4yaml_value_seq_length(seq);
        for (uint32_t i = 0; i < n; i++) {
            l4yaml_value_t item = l4yaml_value_seq_get(seq, i);
            printf("  [%u] %s\n", i, l4yaml_value_string(item));
            l4yaml_free(item);
        }
        l4yaml_free(seq);
        l4yaml_free(val);
    } else {
        fprintf(stderr, "parse error: %s\n",
                l4yaml_result_error_message(r));
    }

    l4yaml_free(r);
    l4yaml_finalize();
    return 0;
}
```

##### Python API

The Python package wraps the C API via `ctypes`.  Pool initialization (Option A) is available for memory-constrained ground systems; most Python users will skip it and let mimalloc allocate from the OS normally.

```python
import l4yaml

# Optional: pre-allocate a fixed pool (Option A)
l4yaml.init_pool(64 * 1024 * 1024)   # 64 MB; omit for default behavior

# Parse a single document with strict limits
value = l4yaml.load("name: Apollo\nstatus: nominal\n", limits="strict")
assert value.kind == "mapping"
print(value["name"].as_str())       # → "Apollo"
print(value["status"].as_str())     # → "nominal"

# Parse multiple documents
yaml_stream = """---
alpha: 1
---
bravo: 2
"""
docs = l4yaml.load_all(yaml_stream, limits="strict")
for doc in docs:
    print(doc.root.as_dict())

# Dump back to YAML
print(l4yaml.dump(value))

# Error handling
try:
    l4yaml.load(malicious_input, limits="strict")
except l4yaml.LimitError as e:
    print(f"Security limit exceeded: {e}")
except l4yaml.ParseError as e:
    print(f"Syntax error: {e}")
```

Pool initialization is **not needed** for Option B from Python — static buffers are a C/link-time concern for embedded targets.

---

## Architecture

```
┌──────────────────────────────────────────────────────────┐
│  Lean 4  (verified core)                                 │
│  L4YAML/Limits.lean   — parseYamlSafe, etc.           │
│  L4YAML/Dump.lean     — dump, dumpDocument*, etc.     │
│  L4YAML/FFI.lean      — @[export] wrappers            │
└────────────────┬─────────────────────────────────────────┘
                 │  Lean 4 @[export] → C symbol
                 ▼
┌──────────────────────────────────────────────────────────┐
│  C ABI  (libl4yaml.so / .dylib / .a)                  │
│  ffi/l4yaml.h         — public header                 │
│  ffi/l4yaml_shim.c    — thin C helpers (optional)     │
└────────────────┬─────────────────────────────────────────┘
                 │  dlopen / ctypes / cffi
                 ▼
┌──────────────────────────────────────────────────────────┐
│  Python  (l4yaml package)                             │
│  python/l4yaml/__init__.py  — high-level API          │
│  python/l4yaml/_ffi.py      — cffi / ctypes bindings  │
│  python/l4yaml/types.py     — YamlValue, etc.         │
└──────────────────────────────────────────────────────────┘
```

---

## Phase 1: Lean `@[export]` Wrappers (`L4YAML/FFI.lean`)

Create a new module that wraps the safe API into C-callable functions using Lean 4's `@[export]` attribute.  Every exported function operates on opaque handles or flat C-compatible types (pointers, `uint32_t`, `const char *`).

### Design: opaque handle model

Lean objects are GC-managed.  The C API uses **opaque handles** (`lean_object *` cast to `void *` on the C side) with explicit `retain`/`release` calls.  This avoids copying the full recursive `YamlValue` tree across the FFI boundary — instead, C/Python code navigates the tree via accessor functions.

### Exported functions

| Lean `@[export]` name | C signature | Description |
|---|---|---|
| `l4yaml_parse_safe` | `lean_obj_res l4yaml_parse_safe(b_lean_obj_arg input, uint8_t preset)` | Parse UTF-8 string with preset limits (0=default, 1=strict, 2=permissive, 3=unlimited, 4=safeTagsOnly). Returns opaque result handle. |
| `l4yaml_parse_single_safe` | `lean_obj_res l4yaml_parse_single_safe(b_lean_obj_arg input, uint8_t preset)` | Single-document variant. Returns opaque `YamlValue` or error. |
| `l4yaml_result_is_ok` | `uint8_t l4yaml_result_is_ok(b_lean_obj_arg result)` | 1 if parse succeeded, 0 if error. |
| `l4yaml_result_get_error` | `lean_obj_res l4yaml_result_get_error(b_lean_obj_arg result)` | Extract error message as Lean `String`. |
| `l4yaml_result_get_value` | `lean_obj_res l4yaml_result_get_value(b_lean_obj_arg result)` | Extract the `YamlValue` handle from an ok result. |
| `l4yaml_result_get_docs` | `lean_obj_res l4yaml_result_get_docs(b_lean_obj_arg result)` | Extract `Array YamlDocument` handle from multi-doc ok result. |
| `l4yaml_docs_count` | `uint32_t l4yaml_docs_count(b_lean_obj_arg docs)` | Number of documents in array. |
| `l4yaml_docs_get` | `lean_obj_res l4yaml_docs_get(b_lean_obj_arg docs, uint32_t i)` | Get i-th document handle. |
| `l4yaml_doc_value` | `lean_obj_res l4yaml_doc_value(b_lean_obj_arg doc)` | Root `YamlValue` of a document. |
| **Value inspection** | | |
| `l4yaml_value_tag` | `uint8_t l4yaml_value_tag(b_lean_obj_arg val)` | Node kind: 0=scalar, 1=sequence, 2=mapping, 3=alias. |
| `l4yaml_value_as_string` | `lean_obj_res l4yaml_value_as_string(b_lean_obj_arg val)` | Scalar content as Lean `String` (or null). |
| `l4yaml_value_seq_length` | `uint32_t l4yaml_value_seq_length(b_lean_obj_arg val)` | Sequence item count. |
| `l4yaml_value_seq_get` | `lean_obj_res l4yaml_value_seq_get(b_lean_obj_arg val, uint32_t i)` | i-th sequence element. |
| `l4yaml_value_map_length` | `uint32_t l4yaml_value_map_length(b_lean_obj_arg val)` | Mapping pair count. |
| `l4yaml_value_map_key` | `lean_obj_res l4yaml_value_map_key(b_lean_obj_arg val, uint32_t i)` | i-th key. |
| `l4yaml_value_map_val` | `lean_obj_res l4yaml_value_map_val(b_lean_obj_arg val, uint32_t i)` | i-th value. |
| `l4yaml_value_lookup` | `lean_obj_res l4yaml_value_lookup(b_lean_obj_arg val, b_lean_obj_arg key)` | Mapping key lookup (returns `Option YamlValue` handle). |
| `l4yaml_value_yaml_tag` | `lean_obj_res l4yaml_value_yaml_tag(b_lean_obj_arg val)` | Tag string (or null). |
| `l4yaml_value_anchor` | `lean_obj_res l4yaml_value_anchor(b_lean_obj_arg val)` | Anchor name (or null). |
| **Dumping** | | |
| `l4yaml_dump` | `lean_obj_res l4yaml_dump(b_lean_obj_arg val)` | Dump `YamlValue` → YAML `String` (default config). |
| `l4yaml_dump_docs` | `lean_obj_res l4yaml_dump_docs(b_lean_obj_arg docs)` | Dump `Array YamlDocument` → YAML `String`. |
| **Lifecycle** | | |
| `l4yaml_string_to_cstr` | `const char * l4yaml_string_to_cstr(b_lean_obj_arg s)` | Extract `const char *` (UTF-8) from Lean `String`. Pointer valid while handle is live. |
| `l4yaml_string_byte_length` | `uint32_t l4yaml_string_byte_length(b_lean_obj_arg s)` | UTF-8 byte length. |
| `l4yaml_retain` | `void l4yaml_retain(lean_obj_arg obj)` | Increment reference count. |
| `l4yaml_release` | `void l4yaml_release(lean_obj_arg obj)` | Decrement reference count (may free). |

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

### `ffi/l4yaml.h`

```c
#ifndef L4YAML_H
#define L4YAML_H

#include <stdint.h>
#include <stddef.h>

#ifdef __cplusplus
extern "C" {
#endif

/* Opaque handles — callers must not dereference */
typedef void *l4yaml_result_t;
typedef void *l4yaml_value_t;
typedef void *l4yaml_docs_t;
typedef void *l4yaml_doc_t;
typedef void *l4yaml_string_t;

/* Limit presets */
#define L4YAML_LIMITS_DEFAULT      0
#define L4YAML_LIMITS_STRICT       1
#define L4YAML_LIMITS_PERMISSIVE   2
#define L4YAML_LIMITS_UNLIMITED    3
#define L4YAML_LIMITS_SAFE_TAGS    4

/* Node kinds */
#define L4YAML_SCALAR    0
#define L4YAML_SEQUENCE  1
#define L4YAML_MAPPING   2
#define L4YAML_ALIAS     3

/* Initialize / finalize Lean runtime */
void l4yaml_initialize(void);
void l4yaml_finalize(void);

/*
 * Fixed-size memory pool initialization (flight software).
 * Call ONE of these BEFORE l4yaml_initialize().
 * See "Design Constraint: Fixed-Size Memory Pool" section.
 */
/* Option A: OS-backed pool (mimalloc reserves via mmap) */
int l4yaml_init_fixed_pool(size_t pool_bytes);
/* Option B: Caller-provided static buffer (bare-metal / RTOS) */
int l4yaml_init_static_pool(void *buf, size_t buf_bytes);

/* Parsing */
l4yaml_result_t l4yaml_parse(const char *input, size_t len, uint8_t preset);
l4yaml_result_t l4yaml_parse_single(const char *input, size_t len, uint8_t preset);

/* Result inspection */
uint8_t l4yaml_result_is_ok(l4yaml_result_t r);
const char *l4yaml_result_error_message(l4yaml_result_t r);

/* Multi-document access */
l4yaml_docs_t l4yaml_result_docs(l4yaml_result_t r);
uint32_t l4yaml_docs_count(l4yaml_docs_t docs);
l4yaml_doc_t l4yaml_docs_get(l4yaml_docs_t docs, uint32_t i);
l4yaml_value_t l4yaml_doc_root(l4yaml_doc_t doc);

/* Single-document access */
l4yaml_value_t l4yaml_result_value(l4yaml_result_t r);

/* Value inspection */
uint8_t l4yaml_value_kind(l4yaml_value_t v);
const char *l4yaml_value_string(l4yaml_value_t v);
uint32_t l4yaml_value_seq_length(l4yaml_value_t v);
l4yaml_value_t l4yaml_value_seq_get(l4yaml_value_t v, uint32_t i);
uint32_t l4yaml_value_map_length(l4yaml_value_t v);
l4yaml_value_t l4yaml_value_map_key(l4yaml_value_t v, uint32_t i);
l4yaml_value_t l4yaml_value_map_val(l4yaml_value_t v, uint32_t i);
l4yaml_value_t l4yaml_value_lookup(l4yaml_value_t v, const char *key);
const char *l4yaml_value_tag(l4yaml_value_t v);
const char *l4yaml_value_anchor(l4yaml_value_t v);

/* Dumping */
const char *l4yaml_dump(l4yaml_value_t v);
const char *l4yaml_dump_docs(l4yaml_docs_t docs);

/* Memory management */
void l4yaml_free(void *handle);

#ifdef __cplusplus
}
#endif

#endif /* L4YAML_H */
```

### `ffi/l4yaml_shim.c`

Thin C wrapper that:
1. Calls `lean_initialize_runtime_module()` and `lean_init_task_manager()` from `l4yaml_initialize()`.
2. Converts `const char *` + `size_t` → Lean `String` via `lean_mk_string_from_bytes`.
3. Converts Lean `String` → `const char *` via `lean_string_cstr`.
4. Wraps `lean_dec` behind `l4yaml_free` for a uniform cleanup API.
5. Implements `l4yaml_init_fixed_pool()` — calls `mi_reserve_os_memory_ex` + `mi_option_set(mi_option_disallow_os_alloc, 1)` before `lean_initialize_runtime_module()`.
6. Implements `l4yaml_init_static_pool()` — calls `mi_manage_os_memory_ex` on caller-provided buffer (for bare-metal / RTOS targets without `mmap`).

### Build integration

Build via CMake after `lake build L4YAML` has generated the IR C files:

```sh
lake build L4YAML          # generate .lake/build/ir/*.c
cmake -B ffi/out -S ffi       # configure (auto-detects Lean sysroot via elan)
cmake --build ffi/out          # compile 76 IR files + shim → libl4yaml.so
```

Or with a custom Lean sysroot:
```sh
cmake -B ffi/out -S ffi -DLEAN_SYSROOT=/path/to/lean
cmake --build ffi/out
```

Deliverables: `libl4yaml.so` (Linux), `libl4yaml.dylib` (macOS).

---

## Phase 3: Python Package (`python/l4yaml/`)

### Package structure

```
python/
├── pyproject.toml
├── l4yaml/
│   ├── __init__.py       # Public API: load, load_safe, dump
│   ├── _ffi.py           # ctypes bindings to libl4yaml.so
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
import l4yaml

# Safe parse (default limits) — recommended
docs = l4yaml.load_all(yaml_string)
value = l4yaml.load(yaml_string)

# Strict limits for web APIs
value = l4yaml.load(yaml_string, limits="strict")

# Dump back to YAML
output = l4yaml.dump(value)

# Value navigation
assert value.kind == "mapping"
name = value["name"].as_str()
items = value["items"].as_list()

# Error handling
try:
    l4yaml.load(malicious_input, limits="strict")
except l4yaml.LimitError as e:
    print(f"Security limit hit: {e}")
except l4yaml.ParseError as e:
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
    def __repr__(self) -> str: ...      # l4yaml.dump(self)

    def __del__(self):
        """Release the underlying Lean handle."""
        ...
```

### Memory management

The `YamlValue` Python object holds a Lean `lean_object *` handle obtained from the C API.  `__del__` calls `l4yaml_free`.  To prevent use-after-free, child values obtained via `__getitem__` call `l4yaml_retain` on the child handle.  The `l4yaml_result_t` returned by `parse` is freed after extracting the value/error.

### PyYAML compatibility shim (optional, deferred)

A `l4yaml.compat` module could provide `yaml.safe_load` / `yaml.safe_dump` signatures backed by the verified parser, enabling drop-in replacement.  This is a stretch goal, not part of the initial v0.4.1 scope.

---

## Phase 4: Rust APIs

Two-crate Rust workspace (`rust/`) wrapping the Phase 2 C shared library. **Completed 2026-03-26**: tasks 8a, 8b, 8d done; 8c (Aeneas) and 8e (crates.io) remain as stretch goals.

**Call chain:** Rust safe wrapper → Rust raw FFI (`l4yaml-sys`, `bindgen`) → C ABI (`libl4yaml.so`) → C shim (`lean_inc` + `_impl` dispatch) → Lean `@[export]` → verified parser.

See the [Task Checklist — Phase 4](#phase-4-rust-api) below for full design, code samples, type mappings, and completion details.

---

## Phase 5: Cross-Language yaml-test-suite Validation

### C API tests (`ffi/test_l4yaml.c`)

- Parse valid YAML, navigate value tree, verify scalar content
- Parse invalid YAML, verify error messages
- Parse billion-laugh payload with `STRICT` preset, verify `LimitError`
- Parse `!!python/object` tag with default limits, verify `TagSecurityError`
- Multi-document parsing, verify document count and per-doc navigation
- Dump round-trip: parse → dump → re-parse → structural equality
- Memory leak check: parse, navigate, free; check under Valgrind/ASan

### Fixed-pool tests (`ffi/test_l4yaml_pool.c`)

- Pool exhaustion: `l4yaml_init_fixed_pool(64 * 1024)` (tiny), parse moderate input, verify deterministic OOM (not hang/crash)
- Static buffer variant: `l4yaml_init_static_pool(buf, sizeof(buf))`, parse valid YAML, verify success
- Fragmentation stress: 10,000 parse→free cycles with `ParserLimits.strict`, verify pool remains usable
- Pool sizing validation: pool sized per formula from appendix, parse worst-case input for each limit preset, verify no OOM
- No-OS-alloc enforcement: after `init_fixed_pool`, verify `mi_option_get(mi_option_disallow_os_alloc) == 1`

### Python tests (`python/tests/`)

- `test_parse.py` — valid inputs, navigation, error cases
- `test_limits.py` — preset limits reject billion-laugh, oversized input, dangerous tags
- `test_dump.py` — round-trip fidelity, scalar style preservation
- `test_roundtrip.py` — parse → dump → parse identity for yaml-test-suite valid cases

### Rust tests (`rust/l4yaml/tests/`)

- `integration.rs` — 21 tests covering: `load`/`load_all`, `load_configured`/`load_all_configured`, value navigation (`as_str`, `get`, `index`), error cases (invalid YAML, empty input), `Display` formatting, document metadata, multi-document parsing, limits presets, config builder, version/limits-presets queries. **All 21 passing** (must run `--test-threads=1`; Lean runtime is not thread-safe).

### Cross-Language yaml-test-suite Comparison

**Architecture: Lean-orchestrated, single source of truth.**

Rather than duplicating the yaml-test-suite metadata parser, skip logic, outcome classification, and reporting in each language, the existing Lean `suiterunner` orchestrates everything. Each language provides only a minimal **tryparse** binary (read file → parse → exit code), and the suiterunner swaps backends via `--backend <lean|c|python|rust>`.

#### tryparse binaries

Each tryparse mirrors the Lean `Tests/TryParse.lean` interface exactly:
- **Input:** single file path argument
- **Output:** exit 0 (parse success), exit 1 (parse error, message on stderr), exit 2 (usage error)
- **Limits:** `UNLIMITED` preset (matching Lean's raw `TokenParser.parseYaml`)
- **Multi-doc:** all backends use multi-document parse (`parse`/`load_all`) since test suite files may contain multiple documents

| Backend | Binary/Script | API call |
|---------|--------------|----------|
| Lean | `.lake/build/bin/tryparse` | `TokenParser.parseYaml` (raw) |
| C | `ffi/out/tryparse_c` | `l4yaml_parse(buf, len, UNLIMITED)` |
| Python | `Tests/tryparse_python.py` | `l4yaml.load_all(content, limits="unlimited")` |
| Rust | `rust/target/release/examples/tryparse` | `l4yaml::load_all(input, Unlimited)` |

#### Suiterunner `--backend` flag

```bash
# Run with native Lean parser (default)
.lake/build/bin/suiterunner --backend lean

# Run with C API
.lake/build/bin/suiterunner --backend c

# Run with Python API (requires L4YAML_LIB env var)
.lake/build/bin/suiterunner --backend python

# Run with Rust API
.lake/build/bin/suiterunner --backend rust

# Generate JSON/HTML reports for any backend
.lake/build/bin/suiterunner --json docs/ --backend c
.lake/build/bin/suiterunner --html docs/ --backend rust
```

The `--backend` flag works with all existing modes (console stages, `--json`, `--html`). The Lean orchestrator handles all metadata parsing, skip logic, outcome classification, and reporting identically regardless of backend.

#### Results (verified 2026-03-26)

**Unlimited preset** (no security limits — matches raw `parseYaml`):

| Backend | Passed | Failed | Skipped | Total |
|---------|--------|--------|---------|-------|
| Lean    | 869    | 0      | 151     | 1020  |
| C       | 869    | 0      | 151     | 1020  |
| Python  | 869    | 0      | 151     | 1020  |
| Rust    | 869    | 0      | 151     | 1020  |

**Limit-enforcing presets** (all 4 backends identical per preset):

| Preset     | Passed | Failed | Skipped | Total | Delta vs unlimited |
|------------|--------|--------|---------|-------|--------------------|
| unlimited  | 869    | 0      | 151     | 1020  | —                  |
| default    | 854    | 15     | 151     | 1020  | −15 (tag security) |
| strict     | 853    | 16     | 151     | 1020  | −16 (tag security + anchor name limits) |
| permissive | 854    | 15     | 151     | 1020  | −15 (tag security) |
| safe_tags  | 853    | 16     | 151     | 1020  | −16 (tag security) |

All four backends produce **identical** outcome vectors for every preset.
The `--limits <preset>` flag passes the preset name to each tryparse binary,
which maps it to the corresponding `ParserLimits` configuration.

Usage:
```bash
.lake/build/bin/suiterunner --backend rust --limits default
```

#### Key design decisions

1. **No per-language suite runners** — avoided ~500 lines each of brittle metadata parsing in C/Python/Rust
2. **Lean as single source of truth** — skip lists, tag classification, outcome mapping maintained in one place
3. **UNLIMITED preset** — tryparse binaries must use unlimited limits to match Lean's raw `parseYaml` (which has no security limits); using DEFAULT caused 15 false failures from tag restrictions
4. **Multi-document parse** — tryparse binaries must handle multi-doc inputs; using single-doc parse caused 22 false failures from `expected single document, found N` errors
5. **Process isolation** — each test case runs in its own OS process with `timeout`, so crashes in one backend don't affect others

---

## Task Checklist

### Phase 1: Lean `@[export]` Wrappers

| # | Task | Status |
|---|------|--------|
| 1 | Create `L4YAML/FFI.lean` with `@[export]` wrappers for safe parse + dump + value navigation | ☑ |
| 2 | Verify `FFI.lean` compiles and exports appear in `.o` symbol table | ☑ |

### Phase 2: C Header & Shared Library

| # | Task | Status |
|---|------|--------|
| 3 | Create `ffi/l4yaml.h` public C header (including `l4yaml_init_fixed_pool`, `l4yaml_init_static_pool`) | ☑ |
| 4 | Create `ffi/l4yaml_shim.c` (runtime init, string conversion, free, pool init) | ☑ |
| 5 | Create `ffi/CMakeLists.txt` to compile IR + shim → `libl4yaml.so` | ☑ |
| 6 | Build shared library, verify symbols with `nm -D` | ☑ |
| 6a | Self-hosted config deserialization: `Config.lean` + FFI exports + C API | ☑ |

#### Config deserialization (self-hosted bootstrapping)

Created [`L4YAML/Config.lean`](L4YAML/Config.lean) — `FromYaml`/`ToYaml` instances for all config types so the verified parser can parse its own `ParserLimits` and `DumpConfig` from YAML.

**Types with `FromYaml`/`ToYaml` instances (9 types):**

| Type | Strategy |
|------|----------|
| `DefaultStyle` | Manual enum (3 variants: `block`, `flow`, `auto`) |
| `ScalarPref` | Manual enum (4 variants: `plain`, `doubleQuoted`, `singleQuoted`, `auto`) |
| `DumpConfig` | Manual struct, all 8 fields optional with defaults |
| `AliasLimits` | Manual struct, all 4 fields optional with defaults |
| `StructuralLimits` | Manual struct, all 5 fields optional with defaults |
| `DocumentLimits` | Manual struct, all 3 fields optional with defaults |
| `TagPolicy` | Manual — scalars for 0-ary (`"coreSchemaOnly"`), single-key mapping for parametric (`{whitelist: [...]}`) |
| `TagLimits` | Manual struct, all 6 fields optional with defaults |
| `ParserLimits` | Manual struct, all 5 fields optional with defaults |

**Bootstrap design:** `parseConfigYaml` uses `parseYamlSingleSafe` with hardcoded tight limits (`configParserLimits` — 64 KB max input, depth 10, 1 document, tags rejected) to safely parse config YAML without circular dependency.

**New @[export] functions (7):**

| Lean `@[export]` name | Description |
|---|---|
| `l4yaml_parse_limits_yaml_impl` | Parse YAML string → `Except String ParserLimits` |
| `l4yaml_parse_dump_config_yaml_impl` | Parse YAML string → `Except String DumpConfig` |
| `l4yaml_config_result_is_ok` | Check config result success |
| `l4yaml_config_result_get_error` | Extract error message |
| `l4yaml_config_result_get_limits` | Extract `ParserLimits` handle |
| `l4yaml_parse_with_yaml_config_impl` | Two-step: parse config YAML → parse input with limits |
| `l4yaml_dump_with_yaml_config_impl` | Dump with YAML-configured `DumpConfig` |

**New C API functions (6):**

| C function | Description |
|---|---|
| `l4yaml_parse_limits_yaml(yaml, len)` | Parse YAML config → `ParserLimits` result handle |
| `l4yaml_config_is_ok(r)` | Check config parse success (1/0) |
| `l4yaml_config_error_message(r)` | Error message or NULL |
| `l4yaml_config_get_limits(r)` | Extract `ParserLimits` handle |
| `l4yaml_parse_configured(input, len, config_yaml, config_len)` | Parse with YAML-configured limits |
| `l4yaml_dump_configured(v, config_yaml, config_len)` | Dump with YAML-configured `DumpConfig` |

**Verification:** `libl4yaml.so` — 50 symbols total (was 40, +10 new). Build: 395/395 jobs, 0 new warnings.

### Phase 3: Python Package

| # | Task | Status |
|---|------|--------|
| 7 | Create `python/l4yaml/` package (`_ffi.py`, `types.py`, `exceptions.py`, `__init__.py`) | ☑ |
| 8 | Create `python/tests/test_*.py`, run pytest | ☑ |

#### Completion details (2026-03-25)

Created `python/l4yaml/` package with ctypes bindings to `libl4yaml.so`, Python-native value types, and a public API matching the design spec.

**Files created (5):**

| File | Purpose |
|------|----------|
| `python/l4yaml/__init__.py` | Public API: `load()`, `load_all()`, `dump()`, `dump_configured()`, `parse_limits_yaml()` |
| `python/l4yaml/_ffi.py` | ctypes bindings: library discovery, `libleanshared.so` pre-load, 30+ function signatures, runtime lifecycle (`ensure_initialized`, `init_pool`) |
| `python/l4yaml/types.py` | `YamlValue` (opaque handle, `__getitem__`, `__contains__`, `__iter__`, `__len__`, `__repr__`, `__eq__`, `as_str`, `as_list`, `as_dict`, `keys`, `items`, `tag`, `anchor`) and `YamlDocument` (`.root`) |
| `python/l4yaml/exceptions.py` | `L4YAMLError` (base), `ParseError`, `LimitError`, `ConfigError` |
| `python/conftest.py` | pytest config: ROS 2 plugin deconfliction |

**Test files created (6):**

| File | Tests | Coverage |
|------|-------|----------|
| `python/tests/test_parse.py` | 12 | Scalar, sequence, mapping parsing; error cases; nested structures |
| `python/tests/test_limits.py` | 5 | Preset names, invalid presets, strict limits |
| `python/tests/test_dump.py` | 4 | Scalar/sequence/mapping dump, round-trip |
| `python/tests/test_roundtrip.py` | 5 | parse→dump→reparse identity for all value types |
| `Tests/test_python_ffi.py` | 78 | Comprehensive CI suite: 14 classes (ScalarParsing, SequenceParsing, MappingParsing, NestedStructures, MultiDocument, Dump, RoundTrip, LimitPresets, ConfigYaml, ErrorHandling, TypeSafety, TagAnchor, ValueEquality, MemorySafety) |
| `Tests/conftest.py` | — | pytest config: `sys.path` setup + ROS 2 plugin deconfliction |

**Critical FFI bugs fixed during development:**

1. **Lean `@[export]` ownership model**: All `@[export]` functions consume their arguments via `lean_dec_ref`, regardless of `@&` annotations in Lean source. The shim was not `lean_inc`-ing handles before calling them, causing use-after-free. Fix: renamed 19 exports to `_impl` suffix, wrote C wrappers that `lean_inc` before calling.
2. **`lean_ptr_tag` on `Option.none`**: `Option.none` = `lean_box(0)` (scalar at address 1). `lean_ptr_tag()` dereferences this → segfault. Fix: replaced with `lean_obj_tag()` which checks `lean_is_scalar()` first.

**Verification:** 78/78 pytest tests pass (0.14s). All Python API functions exercised: `load`, `load_all`, `dump`, `dump_configured`, `parse_limits_yaml`, value navigation, error handling, memory safety.

### Phase 4: Rust API

| # | Task | Status |
|---|------|--------|
| 8a | Create `rust/l4yaml-sys/` raw FFI bindings crate (`bindgen` from `l4yaml.h`) | ☑ |
| 8b | Create `rust/l4yaml/` safe wrapper crate (RAII handles, `Result` error mapping, iterators) | ☑ |
| 8c | Translate safe Rust wrapper to Lean via Aeneas/Charon, verify preservation of safety properties | ☐ |
| 8d | Create `rust/l4yaml/tests/` integration tests, run `cargo test` | ☑ |
| 8e | Publish to crates.io (stretch goal) | ☐ |

#### Completion details (2026-03-26)

Created `rust/` two-crate workspace with raw FFI bindings and a safe RAII wrapper, fully tested against `libl4yaml.so`.

**Files created (10):**

| File | Purpose |
|------|----------|
| `rust/Cargo.toml` | Workspace manifest (members: `l4yaml-sys`, `l4yaml`) |
| `rust/.cargo/config.toml` | Build-time rpath for `libl4yaml.so` + `libleanshared.so` |
| `rust/l4yaml-sys/Cargo.toml` | Raw FFI crate, `links = "l4yaml"`, dep on `bindgen 0.71` |
| `rust/l4yaml-sys/build.rs` | Locates `libl4yaml.so` + `libleanshared.so`, runs `bindgen` on `ffi/l4yaml.h` |
| `rust/l4yaml-sys/src/lib.rs` | `include!` of auto-generated `bindings.rs` |
| `rust/l4yaml/Cargo.toml` | Safe wrapper crate, deps: `l4yaml-sys`, `thiserror 2` |
| `rust/l4yaml/src/lib.rs` | Public API: `initialize()`, `finalize()`, `load()`, `load_all()`, `dump()`, `dump_configured()`, `load_configured()`, `load_all_configured()` |
| `rust/l4yaml/src/value.rs` | `YamlValue`: RAII `Drop`, `kind()`, `as_str()`, `get()`, `keys()`, `items()`, `as_list()`, `Index<&str>`, `Index<usize>`, `IntoIterator`, `Display` |
| `rust/l4yaml/src/document.rs` | `YamlDocument`: RAII `Drop`, `root()` |
| `rust/l4yaml/src/error.rs` | `Error` enum (`Parse`, `Limit`, `Config`, `Utf8`, `NullHandle`), `Kind` enum, `thiserror` derives |
| `rust/l4yaml/src/config.rs` | `LimitsPreset` enum (5 variants), `ParserLimitsHandle`, `parse_limits_yaml()` |
| `rust/l4yaml/tests/integration.rs` | 21 integration tests: scalar/sequence/mapping parsing, nested structures, multi-document, dump, round-trip, limit presets, error handling, iterators, display, empty values, config-based parsing |

**Critical bug fixed during development:**

1. **`load_configured` result type mismatch**: `l4yaml_parse_configured` returns a multi-doc result (`Except ParseError (Array YamlDocument)`), not a single-doc result. Initially called `l4yaml_result_value` (single-doc accessor) on it, causing a Lean runtime abort (`SIGABRT`). Fix: use `extract_multi_result` and return first doc's root.

**Thread safety:** `YamlValue`, `YamlDocument`, and `ParserLimitsHandle` are `!Send + !Sync` via `PhantomData<*mut ()>` (stable Rust, no nightly features required).

**Build requirements:** Rust 1.88+, `libl4yaml.so` (Phase 2), `libleanshared.so` (Lean 4.28 sysroot). Tests must run single-threaded: `cargo test -- --test-threads=1`.

**Verification:** 21/21 integration tests pass (0.06s). All public API functions exercised: `load`, `load_all`, `dump`, `load_configured`, value navigation (`kind`, `as_str`, `get`, `keys`, `items`, `as_list`, `seq_get`, `map_key`, `map_val`), iterators, `Display`, error handling.

#### Design

The Rust API is a two-crate workspace (`rust/`) that wraps the Phase 2 C shared library:

```
rust/
├── Cargo.toml              # workspace
├── l4yaml-sys/
│   ├── Cargo.toml          # links = "l4yaml"
│   ├── build.rs            # bindgen from ffi/l4yaml.h + link libl4yaml.so
│   └── src/lib.rs          # raw extern "C" bindings (auto-generated)
└── l4yaml/
    ├── Cargo.toml
    └── src/
        ├── lib.rs          # pub API: parse, parse_single, dump, LimitsPreset
        ├── value.rs        # YamlValue: RAII Drop, kind(), as_str(), index, iter
        ├── document.rs     # YamlDocument, root()
        ├── error.rs        # ParseError, LimitError, ConfigError → thiserror
        └── config.rs       # LimitsPreset, parse_limits_yaml, dump_configured
```

#### `l4yaml-sys` — raw bindings

Auto-generated via `bindgen` from `ffi/l4yaml.h`.  The `build.rs` script:
1. Locates `libl4yaml.so` via `L4YAML_LIB_DIR` env or `../ffi/build/`
2. Runs `bindgen` with `--allowlist-function "l4yaml_.*"` and `--allowlist-var "L4YAML_.*"`
3. Emits `cargo:rustc-link-lib=dylib=l4yaml` + `cargo:rustc-link-search`
4. Sets `cargo:rustc-link-lib=dylib=leanshared` for transitive Lean runtime dependency

The crate declares `links = "l4yaml"` to prevent duplicate linking.

#### `l4yaml` — safe Rust wrapper

```rust
use l4yaml::{YamlValue, LimitsPreset};

// Safe parse — recommended
let value = l4yaml::load("key: value", LimitsPreset::Default)?;
assert_eq!(value.kind(), Kind::Mapping);
assert_eq!(value["key"].as_str()?, "value");

// Strict limits for web APIs
let value = l4yaml::load(input, LimitsPreset::Strict)?;

// Multi-document
let docs = l4yaml::load_all(multi_doc, LimitsPreset::Default)?;
assert_eq!(docs.len(), 3);

// Dump round-trip
let yaml_str = l4yaml::dump(&value)?;

// Error handling
match l4yaml::load(bad_input, LimitsPreset::Strict) {
    Err(l4yaml::Error::Parse(e)) => eprintln!("syntax: {e}"),
    Err(l4yaml::Error::Limit(e)) => eprintln!("limit: {e}"),
    Ok(v) => { /* use v */ }
}
```

**Key design decisions:**

| Concern | Approach |
|---------|----------|
| Ownership | `YamlValue` owns its `lean_object *` via `Drop` calling `l4yaml_free` |
| Child values | `value["key"]` returns an **owned** `YamlValue` (C API returns new references) |
| Thread safety | `YamlValue: !Send + !Sync` — Lean runtime is single-threaded unless task manager initialized |
| Error mapping | C `result_is_ok` + `error_message` → `Result<T, Error>` with `thiserror` |
| Lifetimes | No borrowed references across FFI — all values are owned, avoiding lifetime entanglement |
| Presets | `enum LimitsPreset { Default, Strict, Permissive, Unlimited, SafeTags }` → `u8` |
| `no_std` | Not initially — requires `std` for `String`, `Vec`, `CStr`. A `no_std` + `alloc` variant is a stretch goal |

**Type mapping:**

| C type | Rust type |
|--------|----------|
| `l4yaml_result_t` | Internal; consumed by `load()`/`load_all()` → `Result<YamlValue, Error>` |
| `l4yaml_value_t` | `YamlValue` (RAII, `Drop`) |
| `l4yaml_docs_t` | `Vec<YamlDocument>` (eagerly extracted) |
| `l4yaml_doc_t` | `YamlDocument { root: YamlValue }` |
| `uint8_t` kind | `enum Kind { Scalar, Sequence, Mapping, Alias }` |
| `const char *` | `&str` (via `CStr::from_ptr` + `to_str()`) |
| `uint8_t` preset | `enum LimitsPreset` |

**`YamlValue` trait implementations:**

```rust
impl YamlValue {
    pub fn kind(&self) -> Kind;
    pub fn as_str(&self) -> Result<&str, Error>;    // borrows from internal C string
    pub fn as_seq(&self) -> Result<Vec<YamlValue>, Error>;
    pub fn as_map(&self) -> Result<Vec<(String, YamlValue)>, Error>;
    pub fn get(&self, key: &str) -> Option<YamlValue>;
    pub fn tag(&self) -> Option<&str>;
    pub fn anchor(&self) -> Option<&str>;
    pub fn len(&self) -> usize;
    pub fn is_empty(&self) -> bool;
}

impl std::ops::Index<&str> for YamlValue { ... }     // mapping lookup
impl std::ops::Index<usize> for YamlValue { ... }    // sequence indexing
impl IntoIterator for &YamlValue { ... }              // seq items or map (key, val) pairs
impl std::fmt::Display for YamlValue { ... }          // l4yaml::dump
impl Drop for YamlValue { ... }                       // l4yaml_free
```

#### Aeneas/Charon verification bridge

[Aeneas](https://github.com/AeneasVerif/aeneas) translates Rust programs (via [Charon](https://github.com/AeneasVerif/charon) MIR extraction) into pure Lean 4 functions, enabling formal verification of Rust code within Lean.

The verification strategy for the Rust wrapper:

1. **Charon extraction**: Run `charon` on the `l4yaml` crate to produce LLBC (Low-Level Borrow Calculus) IR. This captures ownership, borrowing, and control flow.

2. **Aeneas translation**: Translate LLBC to Lean 4 pure functions. Each Rust function `f` becomes a Lean function `f_lean` with explicit `Result` for fallibility and state-passing for mutable operations.

3. **Correspondence proofs**: Prove that the translated Lean functions correspond to the C API calls they wrap:
   - `load_lean input preset = l4yaml_parse_single_safe input (presetToLimits preset)` — the Rust `load()` calls the same verified parser
   - `YamlValue.drop_lean v` corresponds to `l4yaml_free` — no resource leaks
   - `YamlValue.as_str_lean v` returns `Except.ok s ↔ l4yaml_value_string v = s` — value extraction is faithful

4. **Safety invariants**: Prove that the Rust wrapper maintains:
   - **No use-after-free**: `Drop` is called exactly once per `YamlValue`, and no method accesses a freed handle
   - **No double-free**: Owned children cannot alias their parents (the C API returns new references)
   - **Error completeness**: Every C API error path maps to a Rust `Err` variant

**Limitations:**
- Aeneas requires Rust code to be in the `supported` subset (no `unsafe` in verified portions) — the `l4yaml-sys` raw FFI layer is trusted, only the safe wrapper is verified
- `extern "C"` calls are modeled as opaque axioms in the Lean translation — correctness of the C ↔ Lean correspondence is assumed (already verified by Phase 1–2)
- Aeneas is under active development; API stability is not guaranteed across versions

#### Build integration

```sh
# Build the C shared library first
lake build L4YAML
cmake -B ffi/build -S ffi && cmake --build ffi/build

# Build and test the Rust crate
cd rust
export L4YAML_LIB_DIR="$(pwd)/../ffi/build"
export LD_LIBRARY_PATH="$L4YAML_LIB_DIR:$(lean --print-prefix)/lib/lean:$LD_LIBRARY_PATH"
cargo build
cargo test

# Optional: Aeneas verification
charon --crate l4yaml
aeneas --backend lean4 l4yaml.llbc -o ../L4YAML/RustBridge/
# Then verify correspondence in Lean
```

### Phase 5: Testing & Validation

| # | Task | Status |
|---|------|--------|
| 9 | Create `ffi/test_l4yaml.c`, compile and run C API unit tests | ☐ |
| 10 | Create `ffi/test_l4yaml_pool.c`, compile and run fixed-pool tests | ☐ |
| 11 | Create `ffi/tryparse_c.c` — C tryparse binary (UNLIMITED, multi-doc) | ☑ |
| 12 | Create `Tests/tryparse_python.py` — Python tryparse script (UNLIMITED, multi-doc) | ☑ |
| 13 | Create `rust/l4yaml/examples/tryparse.rs` — Rust tryparse binary (UNLIMITED, multi-doc) | ☑ |
| 14 | Extend `suiterunner` with `--backend <lean\|c\|python\|rust>` flag | ☑ |
| 15 | Run cross-language comparison: all 4 backends match 869/0/151 baseline | ☑ |
| 15a | Add `--limits <preset>` to suiterunner and tryparse binaries | ☑ |
| 15b | Run limit-enforcing comparison: all 5 presets × 4 backends identical | ☑ |
| 16 | Valgrind/ASan pass on C test binary and C tryparse (standard + pool modes) | ☐ |
| 17 | Pool fragmentation stress test: 10,000 parse-free cycles | ☐ |
| 18 | Document pool sizing formula in header comments and README | ☐ |
| 19 | Integrate cross-language comparison into CI workflow | ☐ |
| 20 | Update README.md v0.5.0 section with cross-language results | ☐ |
| 21 | Prototype on VxWorks/RTEMS target (stretch goal) | ☐ |

#### Phase 5 completion details (tasks 11–15b, 2026-03-26)

**Architecture:** Lean-orchestrated. Instead of per-language suite runners (~500 lines each
of brittle metadata/skip logic), each language provides a minimal tryparse binary (~40 lines)
and the existing `suiterunner` handles orchestration via `--backend` and `--limits`.

**Files created:**
- `ffi/tryparse_c.c` — C tryparse: `l4yaml_parse(buf, len, preset)`, optional `argv[2]` preset
- `Tests/tryparse_python.py` — Python tryparse: `l4yaml.load_all(content, limits=preset)`, optional `sys.argv[2]`
- `rust/l4yaml/examples/tryparse.rs` — Rust tryparse: `l4yaml::load_all(input, preset)`, optional `args[2]`

**Files modified:**
- `Tests/SuiteRunner/Main.lean` — added `Backend` inductive, `--backend` flag parsing, `--limits <preset>` flag, threaded through `runTest`/`runStage`/`runAllForReport`
- `Tests/TryParse.lean` — added `parsePreset` function, optional second arg uses `parseYamlSafe` with limits
- `ffi/CMakeLists.txt` — added `tryparse_c` executable target

**Bugs found during integration:**
- Using `L4YAML_LIMITS_DEFAULT` (preset 0) caused 15 false failures — tag security checks rejected non-core-schema tags. Fixed: use `UNLIMITED` (preset 3) to match Lean's raw `parseYaml`.
- Using single-doc parse (`load`/`parse_single`) caused 22 false failures — multi-doc test inputs rejected. Fixed: use multi-doc parse (`load_all`/`parse`) in all tryparse binaries.

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
