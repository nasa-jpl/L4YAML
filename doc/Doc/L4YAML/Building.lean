/-
  L4YAML Documentation — Building
-/
import VersoManual

open Verso.Genre Manual

set_option pp.rawOnError true

#doc (Manual) "Building" =>
%%%
tag := "building"
%%%

{index}[building]
L4YAML ships a top-level CMake driver that orchestrates Lake for the
Lean side and compiles the C FFI and (optionally) Rust shim in the
same configuration.
The recommended workflow is therefore one CMake invocation rather
than three separate per-language build commands.

# Recommended Build

```
cmake -B build -S . -DL4YAML_BUILD_RUST=ON
cmake --build build -j
cmake --install build --prefix /path/to/stage
```

The `--install` step is optional; it stages the artifacts into a
standard `${prefix}/{bin,lib,include}` layout plus the compiled
Lean module tree under `${prefix}/lib/lean/`.

The build produces, in order:

 * The Lean library, proof modules, compile-time guards, and every
   executable in the `L4YAML_EXES` list (a superset of the
   `defaultTargets` from `lakefile.toml`), driven by `lake build`.
 * `libl4yaml.so` and the C example `tryparse_c`, defined in
   `ffi/CMakeLists.txt`.
 * The Rust workspace (`l4yaml-sys`, `l4yaml`) and the
   `tryparse_rs` example, driven by
   `cargo build --release --workspace --examples`.

The installed C and Rust binaries have RPATHs that resolve
`libl4yaml.so` via `$ORIGIN/../lib` and `libleanshared.so` from the
Lean toolchain, so they work directly out of the install tree.

# CMake Options

:::table +header
*
  * Option
  * Default
  * Effect
*
  * `L4YAML_BUILD_FFI`
  * `ON`
  * Build `libl4yaml.so` and `tryparse_c`
*
  * `L4YAML_BUILD_RUST`
  * `OFF`
  * Also build the Rust shim and `tryparse_rs`
*
  * `L4YAML_PYTHON_INSTALL`
  * `auto`
  * Python install mode: `auto`, `ament`, `venv`, `none`
*
  * `L4YAML_PYTHON_VENV`
  * (empty)
  * Path to a Python venv (used when mode is `venv`)
*
  * `L4YAML_ENABLE_TESTS`
  * `OFF`
  * Register lake-built test runners with CTest
:::

# Python Install Modes

{index}[Python install modes]
The Python package (`python/l4yaml`) is pure Python over `ctypes`,
so it has no compile step — only an install step.
The CMake driver supports three install paradigms, picked by the
`L4YAML_PYTHON_INSTALL` option:

 * *`ament`* — uses `ament_cmake_python` from a sourced ROS 2
   environment.
   Installs the package at
   `${prefix}/lib/pythonX.Y/site-packages/l4yaml/`; colcon's
   `setup.bash` automatically prepends that path to `PYTHONPATH`.
   This is the right mode for a ROS 2 / colcon workflow.

 * *`venv`* — runs `pip install -e python` from
   `${L4YAML_PYTHON_VENV}/bin/python` at configure time.
   The install is editable, so source edits in `python/l4yaml/`
   take effect without re-running CMake.

 * *`none`* — CMake does not touch Python; the user installs the
   package manually with `pip install python` or equivalent.

The default `auto` mode picks `ament` when `ament_cmake_python` is
on the CMake prefix path (i.e. a ROS underlay is sourced), `venv`
when `L4YAML_PYTHON_VENV` is set, otherwise `none`.
The same `colcon build` command therefore works in both a ROS shell
(uses `ament`) and a plain dev shell (falls back to `none`),
without flag changes.

## ROS 2 / colcon

In a colcon workspace with a ROS underlay sourced, no additional
flags are needed:

```
source /opt/ros/jazzy/setup.bash
colcon build --packages-select L4YAML
```

After build, source the workspace overlay (`. install/setup.bash`)
and `import l4yaml` works.

## venv (non-ROS)

For local development outside ROS, point the CMake driver at a
venv:

```
python -m venv .venv && . .venv/bin/activate
cmake -B build -S . \
      -DL4YAML_PYTHON_INSTALL=venv \
      -DL4YAML_PYTHON_VENV=$VIRTUAL_ENV
cmake --build build -j
```

The `pip install -e python` runs at configure time and the venv
keeps tracking `python/l4yaml/` thereafter.

# Prerequisites

{index}[prerequisites]
The minimum environment is:

 * `elan` on `PATH` — provides the `lean` and `lake` versions
   pinned in `lean-toolchain`.
 * A C compiler and a CMake ≥ 3.20 (the top-level project enables
   only the `C` language; the Lean side is driven through Lake).

`L4YAML_BUILD_RUST=ON` additionally requires:

 * `cargo` (recent stable Rust; the workspace pins
   `edition = "2024"` and `rust-version = "1.85"`).
 * `libclang` development files for `bindgen` to parse
   `ffi/l4yaml.h`.
 * Network access on the first build, so `cargo` can fetch
   `bindgen` and `thiserror` from `crates.io`.

# Lean-Only Build

If you only need to typecheck and build the Lean library, proofs,
and test executables — without the FFI shim or any Rust output —
the unmodified Lake invocation works on its own:

```
lake build
```

This is also what the top-level CMake driver invokes internally as
its first step.

# Standalone Per-Binding Builds

Each binding can also be built independently of the top-level
driver, which is occasionally convenient when iterating on a
single language layer:

```
# C shared library + header
cmake -B ffi/build ffi && cmake --build ffi/build

# Python package — venv-based editable install.  Or use the
# top-level CMake driver above with -DL4YAML_PYTHON_INSTALL=venv.
python -m venv .venv && . .venv/bin/activate
python -m pip install -e python

# Rust crates — needs libl4yaml.so on disk; either build it via
# the cmake line above (the default path is ffi/out/) or point
# at any other location with L4YAML_LIB_DIR.
cargo build --manifest-path rust/Cargo.toml
```

The top-level driver wires these together so that artifact paths
match the install tree without needing per-binding configuration.
