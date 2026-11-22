# L4YAML C/C++ API Usage Guide

This directory contains the C FFI (Foreign Function Interface) for L4YAML, a formally verified YAML parser implemented in Lean4.

## Overview

L4YAML exposes opaque handle types that must be explicitly freed:
- `l4yaml_result_t` - Parse result handle
- `l4yaml_value_t` - YAML value handle (scalars, sequences, mappings)
- `l4yaml_docs_t` - Multi-document collection handle
- `l4yaml_doc_t` - Single document handle

**Critical**: All handles returned by L4YAML functions must be freed with `l4yaml_free()` to prevent memory leaks.

## C Usage

### Basic Pattern

```c
#include <l4yaml.h>

// Parse YAML
l4yaml_result_t result = l4yaml_parse_single(yaml_text, strlen(yaml_text));
if (!result || !l4yaml_result_is_ok(result)) {
    if (result) l4yaml_free(result);
    return ERROR;
}

// Get root value
l4yaml_value_t root = l4yaml_result_value(result);

// Use the value
if (l4yaml_value_kind(root) == L4YAML_SEQUENCE) {
    uint32_t count = l4yaml_value_seq_length(root);
    // Process sequence...
}

// Free handles (root first, then result)
l4yaml_free(root);
l4yaml_free(result);
```

### Iterating Sequences

**Important**: Free each item immediately after use, then free the parent sequence.

```c
l4yaml_value_t seq = l4yaml_value_lookup(parent, "items");
if (seq && l4yaml_value_kind(seq) == L4YAML_SEQUENCE) {
    uint32_t n = l4yaml_value_seq_length(seq);
    for (uint32_t i = 0; i < n; i++) {
        l4yaml_value_t item = l4yaml_value_seq_get(seq, i);
        
        // Use item...
        const char* str = l4yaml_value_string(item);
        printf("Item %u: %s\n", i, str);
        
        l4yaml_free(item);  // Free immediately after use
    }
    l4yaml_free(seq);  // Free parent after loop
}
```

### Nested Lookups

Each lookup returns a new handle that must be freed:

```c
l4yaml_value_t config = l4yaml_value_lookup(root, "config");
l4yaml_value_t timeout = l4yaml_value_lookup(config, "timeout");

if (timeout && l4yaml_value_kind(timeout) == L4YAML_SCALAR) {
    const char* value = l4yaml_value_string(timeout);
    // Use value...
}

// Free in reverse order of acquisition
l4yaml_free(timeout);
l4yaml_free(config);
l4yaml_free(root);
```

### Error Handling

Always check for null handles and free on error paths:

```c
l4yaml_result_t result = l4yaml_parse_single(text, len);
if (!result) {
    return ERROR;  // Allocation failed, nothing to free
}

if (!l4yaml_result_is_ok(result)) {
    l4yaml_free(result);  // Free the error result
    return ERROR;
}

l4yaml_value_t root = l4yaml_result_value(result);
if (!root) {
    l4yaml_free(result);
    return ERROR;
}

// ... use root ...

l4yaml_free(root);
l4yaml_free(result);
```

## C++ Usage

### RAII Wrapper (Recommended)

The `l4yaml_raii.hpp` header provides RAII wrappers that automatically manage memory:

```cpp
#include <l4yaml_raii.hpp>

// Parse YAML - automatic cleanup on scope exit
l4yaml::ResultHandle result(l4yaml_parse_single(yaml_text, strlen(yaml_text)));
if (!result || !l4yaml_result_is_ok(result.get())) {
    return ERROR;  // Automatic cleanup, no manual free needed
}

// Get root value - automatic cleanup
l4yaml::ValueHandle root(l4yaml_result_value(result.get()));

// Use the value with .get()
if (l4yaml_value_kind(root.get()) == L4YAML_SEQUENCE) {
    uint32_t count = l4yaml_value_seq_length(root.get());
    // Process sequence...
}

// Handles automatically freed when they go out of scope
```

### Type Aliases

Convenient type aliases for common handle types:

```cpp
using ResultHandle = L4YAMLHandle<l4yaml_result_t>;
using ValueHandle = L4YAMLHandle<l4yaml_value_t>;
using DocsHandle = L4YAMLHandle<l4yaml_docs_t>;
using DocHandle = L4YAMLHandle<l4yaml_doc_t>;
```

### Iterating with RAII

```cpp
l4yaml::ValueHandle seq(l4yaml_value_lookup(root.get(), "items"));
if (seq && l4yaml_value_kind(seq.get()) == L4YAML_SEQUENCE) {
    uint32_t n = l4yaml_value_seq_length(seq.get());
    
    for (uint32_t i = 0; i < n; i++) {
        // Each iteration creates a new handle
        l4yaml::ValueHandle item(l4yaml_value_seq_get(seq.get(), i));
        
        if (item && l4yaml_value_kind(item.get()) == L4YAML_SCALAR) {
            const char* str = l4yaml_value_string(item.get());
            // Use str...
        }
        // item automatically freed at end of iteration
    }
    // seq automatically freed at end of scope
}
```

### Nested Lookups with RAII

```cpp
l4yaml::ValueHandle config(l4yaml_value_lookup(root.get(), "config"));
l4yaml::ValueHandle timeout(l4yaml_value_lookup(config.get(), "timeout"));

if (timeout && l4yaml_value_kind(timeout.get()) == L4YAML_SCALAR) {
    const char* value = l4yaml_value_string(timeout.get());
    // Use value...
}
// Both handles automatically freed in reverse order (timeout, then config)
```

### RAII Handle Operations

```cpp
// Construction from raw handle
l4yaml::ValueHandle handle(l4yaml_value_lookup(parent, "key"));

// Check if handle is valid
if (handle) {
    // Use handle
}

// Get raw handle for C API calls
l4yaml_value_t raw = handle.get();

// Release ownership (returns raw handle without freeing)
l4yaml_value_t released = handle.release();
// Now you must manually call l4yaml_free(released)

// Reset to a new handle (frees old handle if present)
handle.reset(l4yaml_value_lookup(parent, "other_key"));

// Move semantics (transfer ownership)
l4yaml::ValueHandle other = std::move(handle);
// handle is now nullptr, other owns the resource
```

## Common Pitfalls

### ❌ Double Free

```c
l4yaml_value_t value = l4yaml_value_lookup(root, "key");
l4yaml_free(value);
l4yaml_free(value);  // CRASH: double free
```

**Fix**: Only free each handle once. RAII wrappers prevent this automatically.

### ❌ Use After Free

```c
l4yaml_value_t value = l4yaml_value_lookup(root, "key");
const char* str = l4yaml_value_string(value);
l4yaml_free(value);
printf("%s", str);  // CRASH: str points to freed memory
```

**Fix**: Copy the string before freeing, or keep the handle alive while using the string.

### ❌ Memory Leak

```c
l4yaml_value_t value = l4yaml_value_lookup(root, "key");
// ... use value ...
// Forgot to call l4yaml_free(value)
```

**Fix**: Always free handles. Use RAII wrappers in C++ to automate this.

### ❌ Mixing C and C++ Linkage

```cpp
extern "C" {
  #include <l4yaml.h>
  #include <l4yaml_raii.hpp>  // ERROR: templates can't have C linkage
}
```

**Fix**: Include C++ headers outside `extern "C"` blocks:

```cpp
extern "C" {
  #include <l4yaml.h>
}
#include <l4yaml_raii.hpp>  // Correct
```

## Memory Management Rules

1. **Every handle must be freed**: If a function returns a handle (non-null), you own it and must free it.
2. **Free in reverse order**: For nested handles, free children before parents.
3. **Free immediately in loops**: Don't accumulate handles across iterations.
4. **Check for null**: Not all operations return valid handles (lookup may fail).
5. **Use RAII in C++**: Prefer `l4yaml_raii.hpp` wrappers to eliminate manual memory management.

## Building

### C
```bash
gcc -o myapp myapp.c -ll4yaml -I/path/to/install/include -L/path/to/install/lib
```

### C++
```bash
g++ -o myapp myapp.cpp -ll4yaml -I/path/to/install/include -L/path/to/install/lib
```

## Further Documentation

See [`C_PYTHON_RUST_APIs.md`](../C_PYTHON_RUST_APIs.md) for complete API reference and additional examples.
