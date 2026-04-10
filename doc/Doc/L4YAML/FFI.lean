/-
  L4YAML Documentation — FFI Bindings
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "FFI Bindings" =>
%%%
tag := "ffi"
%%%

{index}[FFI]
L4YAML provides foreign function interface bindings for C, Python,
and Rust, enabling the verified parser to be used from mainstream
languages.
The FFI layer sits above the full parser pipeline — callers get
the same verified parsing logic, security limits, and schema
resolution available in Lean.

# Dependency Graph
%%%
tag := "ffi-graph"
%%%

The FFI module sits at the top of the dependency chain:

```
FFI
 └── Config
      └── Dump
           └── Schema
                ├── Token
                │    └── Scanner
                │         └── TokenParser
                └── CharPredicates
                     └── YamlSpec
```

`FFI.lean` exports functions via `@[export]` that are callable
from C.
The Python and Rust bindings wrap these C-level exports
with idiomatic APIs in their respective languages.

# C API
%%%
tag := "c-api"
%%%

{index}[C API]
The C API is defined in `ffi/l4yaml.h` with a bridge layer in
`ffi/l4yaml_shim.c`.
It provides approximately 26 exported functions covering:

 * _Parsing_ — `l4yaml_parse_safe` and related functions
 * _Dumping_ — converting `YamlValue` back to YAML text
 * _Schema_ — tag handle registration and type resolution
 * _Limits_ — configuring `ParserLimits` via preset codes or
   individual parameter setters
 * _Memory_ — proper Lean object lifecycle management
   (`lean_inc_ref` / `lean_dec_ref`)

All C API functions operate on opaque Lean object pointers.
The shim layer handles the Lean runtime initialization and
provides stable C-callable entry points.

# Python API
%%%
tag := "python-api"
%%%

{index}[Python API]
The Python package (`python/l4yaml/`) wraps the C API using
`ctypes`, providing a Pythonic interface with:

 * Full type annotations for IDE support
 * Automatic garbage collection of Lean objects via reference counting
 * Cross-platform support (Linux, macOS, Windows)
 * 78 tests covering the full API surface

Usage follows the familiar pattern:

```
from l4yaml import parse

result = parse("key: value")
```

# Rust API
%%%
tag := "rust-api"
%%%

{index}[Rust API]
The Rust workspace (`rust/`) provides two crates:

 * *`l4yaml-sys`* — raw FFI bindings generated from the C header.
   Unsafe, low-level, intended for direct interop.

 * *`l4yaml`* — safe RAII wrapper with 21 tests.
   Lean object lifetimes are managed via the `Drop` trait,
   ensuring proper cleanup without manual reference counting.

The safe wrapper provides idiomatic Rust types and error handling
via `Result<T, E>`, translating Lean's `Except` into Rust's error
model.

# Adding FFI Bindings
%%%
tag := "adding-ffi"
%%%

To expose a new Lean function via FFI:

 1. Add `@[export l4yaml_function_name]` to the Lean definition
 2. Declare the corresponding C prototype in `ffi/l4yaml.h`
 3. Add any necessary shim code in `ffi/l4yaml_shim.c`
 4. Update the Python/Rust wrappers as needed
 5. Add tests at each layer

The `@[export]` attribute instructs the Lean compiler to generate
a C-callable symbol with the specified name.
