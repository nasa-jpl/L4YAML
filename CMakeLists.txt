# L4YAML — top-level CMake wrapper around `lake build`.
#
# Lake (Lean's build tool) drops its outputs into <source>/.lake/build/
# rather than into a CMake build tree.  This file lets you drive that
# build from CMake and stage the artifacts into a standard
# ${CMAKE_INSTALL_PREFIX}/{bin,lib,share} layout via `cmake --install`.
#
# Prerequisites:
#   * elan on PATH (provides `lake` and `lean` matching ./lean-toolchain)
#
# Typical use:
#   cmake -B build -S . -DCMAKE_INSTALL_PREFIX=/path/to/stage
#   cmake --build build           # runs `lake build` + ffi
#   cmake --install build         # copies bin/, lib/, headers
#
# Caveat: the installed .olean tree cannot be picked up by another
# Lean project via `import` — Lake resolves deps via [[require]] against
# git URLs, not against a CMake install prefix.  The install is meant
# for shipping the executables and the FFI shared library, not for
# republishing this package as a Lean dependency.

cmake_minimum_required(VERSION 3.20)
# C is enabled unconditionally so GNUInstallDirs can resolve lib vs lib64
# from the target architecture, and so the ffi/ subproject can compile
# without re-enabling the language later.
project(L4YAML LANGUAGES C)
include(GNUInstallDirs)

# ── elan-managed Lean toolchain ─────────────────────────────────────
find_program(LAKE_EXECUTABLE NAMES lake REQUIRED
             DOC "Lake — Lean 4 build tool (provided by elan)")
find_program(LEAN_EXECUTABLE NAMES lean REQUIRED
             DOC "Lean 4 compiler (provided by elan)")
message(STATUS "lake: ${LAKE_EXECUTABLE}")
message(STATUS "lean: ${LEAN_EXECUTABLE}")

# Resolve once at top level so both ffi/ and the Rust block see them.
execute_process(
  COMMAND "${LEAN_EXECUTABLE}" --print-prefix
  OUTPUT_VARIABLE LEAN_SYSROOT
  OUTPUT_STRIP_TRAILING_WHITESPACE
  COMMAND_ERROR_IS_FATAL ANY)
set(LEAN_LIB_DIR "${LEAN_SYSROOT}/lib/lean")
message(STATUS "lean sysroot: ${LEAN_SYSROOT}")

set(L4YAML_LAKE_BUILD "${CMAKE_CURRENT_SOURCE_DIR}/.lake/build")

# ── Executables produced by lake ────────────────────────────────────
# Mirrors the [[lean_exe]] entries in lakefile.toml.  Trim this list if
# some of these are internal/diagnostic and shouldn't ship.  Note: this
# is a superset of lakefile.toml's `defaultTargets`, so we pass it
# explicitly to `lake build` below — otherwise execs like `tests` and
# `demo` (which aren't in defaultTargets) wouldn't be built and the
# install step would fail trying to copy them.
set(L4YAML_EXES
  tests
  demo
  suiterunner
  tryparse
  tryscan
  tryroundtrip
  trydump
  queryresults
  propertytests
  mutationtests
  adversarialinstantiation
  adversarialtests
  explicitkeytests
  flowtests
  validationtests
  limittests
  flowregressioncheck
  errorstagediag
  scalarstagediag
  dumproundtrip
  rawparsetests
  specexamples
  extractSpecExamples
  schemadump
  scannertests
  scannerspecexamples
  productioncoverage)

# ── Drive lake from CMake ───────────────────────────────────────────
# Lake is internally incremental, so we just invoke it every time and
# let it no-op when nothing changed.  We pass L4YAML_EXES explicitly
# rather than relying on lakefile's defaultTargets so the build set
# matches the install set.
add_custom_target(lake-build ALL
  COMMAND "${LAKE_EXECUTABLE}" build ${L4YAML_EXES}
  WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
  COMMENT "lake build ${L4YAML_EXES} (incremental)"
  USES_TERMINAL
  VERBATIM)

foreach(exe IN LISTS L4YAML_EXES)
  install(PROGRAMS "${L4YAML_LAKE_BUILD}/bin/${exe}"
          DESTINATION "${CMAKE_INSTALL_BINDIR}"
          COMPONENT L4YAML_Runtime)
endforeach()

# ── Compiled Lean module tree (.olean / .ilean) ─────────────────────
# Useful for tarballing or for `LEAN_PATH=<prefix>/lib/lean lean ...`,
# NOT for `[[require]]`-based consumption from another Lean project.
install(DIRECTORY "${L4YAML_LAKE_BUILD}/lib/"
        DESTINATION "${CMAKE_INSTALL_LIBDIR}/lean"
        COMPONENT L4YAML_LeanLib
        FILES_MATCHING
          PATTERN "*.olean"
          PATTERN "*.ilean")

# Lean sources, in case downstream tooling wants to re-typecheck.
install(DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}/L4YAML"
        DESTINATION "${CMAKE_INSTALL_DATADIR}/lean/src"
        COMPONENT L4YAML_LeanSrc
        FILES_MATCHING PATTERN "*.lean")
install(FILES "${CMAKE_CURRENT_SOURCE_DIR}/L4YAML.lean"
        DESTINATION "${CMAKE_INSTALL_DATADIR}/lean/src"
        COMPONENT L4YAML_LeanSrc)

# ── FFI shared library (libl4yaml + tryparse_c) ─────────────────────
# Defined in ffi/CMakeLists.txt; depends on `lake build L4YAML` having
# generated .lake/build/ir/*.c, so it must run after lake-build.
option(L4YAML_BUILD_FFI "Build libl4yaml shared library and tryparse_c" ON)
if(L4YAML_BUILD_FFI)
  # ffi/CMakeLists.txt globs .lake/build/ir/*.c at *configure* time and
  # errors out if empty.  On a fresh tree (e.g. a colcon build), lake
  # has not run yet, so we bootstrap the IR here with `lake build L4YAML`,
  # which produces the .c files for the L4YAML lib + its transitive deps.
  # Lake is incremental, so the subsequent build-time `lake-build` target
  # is a no-op when nothing changed.
  #
  # We deliberately do NOT run `lake update` here — that would re-resolve
  # mutable inputRevs (`main`, `nightly-testing`, …) in lake-manifest.json
  # and pull in dep revisions whose own lean-toolchain may be newer than
  # this project's pin, producing IR with runtime symbols missing from
  # the parent's libleanshared.so → undefined references at link time.
  # `lake build` alone fetches any missing deps at the manifest's pinned
  # revs without rewriting it.  To intentionally advance dep revs, run
  # `lake update` from the shell.
  message(STATUS "Bootstrapping Lake IR for ffi/ (lake build L4YAML)…")
  message(STATUS "  HOME=$ENV{HOME}")
  message(STATUS "  cwd=${CMAKE_CURRENT_SOURCE_DIR}")
  execute_process(
    COMMAND "${LAKE_EXECUTABLE}" --verbose build L4YAML
    WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}"
    RESULT_VARIABLE _lake_bootstrap_rc
    OUTPUT_VARIABLE _lake_bootstrap_out
    ERROR_VARIABLE  _lake_bootstrap_err)
  if(NOT _lake_bootstrap_rc EQUAL 0)
    message(FATAL_ERROR
      "lake build L4YAML failed (exit ${_lake_bootstrap_rc}).\n"
      "If you see 'Permission denied' with no path, elan is likely the\n"
      "culprit — check that \$HOME and ~/.elan/ are owned by the user\n"
      "running colcon, and try `elan show` standalone in this directory.\n"
      "---- lake stdout ----\n${_lake_bootstrap_out}"
      "---- lake stderr ----\n${_lake_bootstrap_err}")
  endif()

  add_subdirectory(ffi)
  add_dependencies(l4yaml lake-build)
  install(FILES "${CMAKE_CURRENT_SOURCE_DIR}/ffi/l4yaml.h"
          DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
          COMPONENT L4YAML_Devel)
endif()

# ── Rust shim (l4yaml-sys, l4yaml) + tryparse_rs example ────────────
# Cargo workspace at rust/ with two crates:
#   * l4yaml-sys — raw bindgen FFI bindings, links libl4yaml.so
#   * l4yaml     — safe wrapper crate
# Plus a `tryparse` example binary in l4yaml/examples/.
#
# Requires: cargo on PATH, libclang (for bindgen), network access on
# first build (cargo fetches bindgen + thiserror from crates.io).
option(L4YAML_BUILD_RUST "Build Rust shim crates and tryparse_rs example" OFF)
if(L4YAML_BUILD_RUST)
  if(NOT L4YAML_BUILD_FFI)
    message(FATAL_ERROR
      "L4YAML_BUILD_RUST=ON requires L4YAML_BUILD_FFI=ON: the Rust crates "
      "link against libl4yaml.so produced by ffi/.")
  endif()
  find_program(CARGO_EXECUTABLE NAMES cargo REQUIRED
               DOC "Cargo — Rust package manager")

  set(L4YAML_RUST_DIR        "${CMAKE_CURRENT_SOURCE_DIR}/rust")
  set(L4YAML_RUST_TARGET_DIR "${CMAKE_CURRENT_BINARY_DIR}/rust-target")
  set(L4YAML_RUST_TRYPARSE   "${L4YAML_RUST_TARGET_DIR}/release/examples/tryparse")

  # Glob for change tracking; CONFIGURE_DEPENDS re-globs on reconfigure.
  file(GLOB_RECURSE L4YAML_RUST_SOURCES CONFIGURE_DEPENDS
       "${L4YAML_RUST_DIR}/*.rs"
       "${L4YAML_RUST_DIR}/*/Cargo.toml"
       "${L4YAML_RUST_DIR}/Cargo.toml"
       "${L4YAML_RUST_DIR}/l4yaml-sys/build.rs")

  # RUSTFLAGS: rpath entries to find libl4yaml.so (build-tree absolute
  # path + install-tree $ORIGIN-relative) and libleanshared.so.
  # $ORIGIN must reach the linker as a literal — CMake leaves it alone
  # because it's not ${ORIGIN}, and VERBATIM in add_custom_command
  # bypasses shell expansion.
  set(_l4yaml_rustflags
      "-C link-arg=-Wl,-rpath,$<TARGET_FILE_DIR:l4yaml> \
-C link-arg=-Wl,-rpath,${LEAN_LIB_DIR} \
-C link-arg=-Wl,-rpath,$ORIGIN/../${CMAKE_INSTALL_LIBDIR}")

  add_custom_command(
    OUTPUT  "${L4YAML_RUST_TRYPARSE}"
    COMMAND ${CMAKE_COMMAND} -E env
            "L4YAML_LIB_DIR=$<TARGET_FILE_DIR:l4yaml>"
            "LEAN_LIB_DIR=${LEAN_LIB_DIR}"
            "CARGO_TARGET_DIR=${L4YAML_RUST_TARGET_DIR}"
            "RUSTFLAGS=${_l4yaml_rustflags}"
            "${CARGO_EXECUTABLE}" build --release --workspace --examples
    WORKING_DIRECTORY "${L4YAML_RUST_DIR}"
    DEPENDS l4yaml ${L4YAML_RUST_SOURCES}
    COMMENT "cargo build --release (Rust shim + tryparse example)"
    USES_TERMINAL
    VERBATIM)

  add_custom_target(rust-build ALL DEPENDS "${L4YAML_RUST_TRYPARSE}")

  # Install the Rust example as `tryparse_rs` to disambiguate from the
  # Lean-built `tryparse` (already in L4YAML_EXES).
  install(PROGRAMS "${L4YAML_RUST_TRYPARSE}"
          DESTINATION "${CMAKE_INSTALL_BINDIR}"
          RENAME tryparse_rs
          COMPONENT L4YAML_Runtime)
endif()

# ── Python package (l4yaml) ─────────────────────────────────────────
# Pure-Python ctypes package at python/l4yaml/.  Three install modes:
#
#   * ament — uses ament_cmake_python from a sourced ROS environment
#     to install at ${prefix}/lib/pythonX.Y/site-packages/l4yaml/.
#     Colcon's setup.bash auto-prepends that to PYTHONPATH.
#   * venv  — runs `pip install -e python` from the venv at
#     L4YAML_PYTHON_VENV at configure time.  Editable, so source
#     edits take effect without re-running cmake.
#   * none  — cmake doesn't touch Python; install manually.
#
# `auto` picks ament if the ROS underlay is on CMAKE_PREFIX_PATH,
# else venv if L4YAML_PYTHON_VENV is set, else none.  This lets the
# same `colcon build` command work in both a ROS shell and a plain
# dev shell, opt-in for the venv path.
set(L4YAML_PYTHON_INSTALL "auto" CACHE STRING
    "Python install mode: auto, ament, venv, none")
set_property(CACHE L4YAML_PYTHON_INSTALL PROPERTY STRINGS auto ament venv none)
set(L4YAML_PYTHON_VENV "" CACHE PATH
    "Path to a Python venv (used when L4YAML_PYTHON_INSTALL=venv)")

set(_l4yaml_py_mode "${L4YAML_PYTHON_INSTALL}")
if(_l4yaml_py_mode STREQUAL "auto")
  find_package(ament_cmake_python QUIET)
  if(ament_cmake_python_FOUND)
    set(_l4yaml_py_mode "ament")
  elseif(L4YAML_PYTHON_VENV)
    set(_l4yaml_py_mode "venv")
  else()
    set(_l4yaml_py_mode "none")
  endif()
endif()
message(STATUS "l4yaml Python install mode: ${_l4yaml_py_mode}")

if(_l4yaml_py_mode STREQUAL "ament")
  find_package(ament_cmake_python REQUIRED)
  ament_python_install_package(l4yaml
    PACKAGE_DIR "${CMAKE_CURRENT_SOURCE_DIR}/python/l4yaml")

elseif(_l4yaml_py_mode STREQUAL "venv")
  if(NOT L4YAML_PYTHON_VENV)
    message(FATAL_ERROR
      "L4YAML_PYTHON_INSTALL=venv requires -DL4YAML_PYTHON_VENV=/path/to/venv. "
      "Create it with `python -m venv /path/to/venv` first.")
  endif()
  if(NOT EXISTS "${L4YAML_PYTHON_VENV}/bin/python")
    message(FATAL_ERROR
      "L4YAML_PYTHON_VENV=${L4YAML_PYTHON_VENV} doesn't look like a venv "
      "(no bin/python).  Create it with `python -m venv ${L4YAML_PYTHON_VENV}`.")
  endif()
  message(STATUS "  pip install -e python  (into ${L4YAML_PYTHON_VENV})")
  execute_process(
    COMMAND "${L4YAML_PYTHON_VENV}/bin/python" -m pip install -e
            "${CMAKE_CURRENT_SOURCE_DIR}/python"
    RESULT_VARIABLE _l4yaml_pip_rc)
  if(NOT _l4yaml_pip_rc EQUAL 0)
    message(FATAL_ERROR
      "pip install -e python failed (exit ${_l4yaml_pip_rc}). "
      "Check that the venv at ${L4YAML_PYTHON_VENV} has pip and that "
      "python/pyproject.toml is well-formed.")
  endif()

elseif(NOT _l4yaml_py_mode STREQUAL "none")
  message(FATAL_ERROR
    "Unknown L4YAML_PYTHON_INSTALL value: '${_l4yaml_py_mode}' "
    "(expected: auto, ament, venv, none)")
endif()

unset(_l4yaml_py_mode)

# ── Optional: CTest integration ─────────────────────────────────────
option(L4YAML_ENABLE_TESTS "Register lake-built test runners with CTest" OFF)
if(L4YAML_ENABLE_TESTS)
  enable_testing()
  foreach(t IN ITEMS tests suiterunner propertytests mutationtests
                     adversarialtests explicitkeytests flowtests
                     validationtests rawparsetests specexamples
                     scannertests scannerspecexamples productioncoverage)
    add_test(NAME L4YAML.${t}
             COMMAND "${LAKE_EXECUTABLE}" exe ${t}
             WORKING_DIRECTORY "${CMAKE_CURRENT_SOURCE_DIR}")
  endforeach()
endif()
