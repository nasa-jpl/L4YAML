# ffi/CMakeLists.txt — Build libl4yaml.so from Lean IR + C shim
#
# Prerequisites:
#   lake build L4YAML    (generates .lake/build/ir/*.c)
#
# Usage:
#   cmake -B ffi/out -S ffi
#   cmake --build ffi/out
#
# Or with a custom Lean sysroot:
#   cmake -B ffi/out -S ffi -DLEAN_SYSROOT=/path/to/lean
#
cmake_minimum_required(VERSION 3.16)
project(l4yaml C)

# ── Locate Lean sysroot ─────────────────────────────────────────────
if(NOT LEAN_SYSROOT)
  find_program(LEAN_BIN lean REQUIRED)
  execute_process(
    COMMAND "${LEAN_BIN}" --print-prefix
    OUTPUT_VARIABLE LEAN_SYSROOT
    OUTPUT_STRIP_TRAILING_WHITESPACE
    COMMAND_ERROR_IS_FATAL ANY)
endif()
message(STATUS "Lean sysroot: ${LEAN_SYSROOT}")

set(LEAN_INCLUDE_DIR "${LEAN_SYSROOT}/include")
set(LEAN_LIB_DIR     "${LEAN_SYSROOT}/lib/lean")

if(NOT EXISTS "${LEAN_INCLUDE_DIR}/lean/lean.h")
  message(FATAL_ERROR "lean.h not found at ${LEAN_INCLUDE_DIR}/lean/lean.h")
endif()

set(PROJECT_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/..")
set(IR_DIR "${PROJECT_ROOT}/.lake/build/ir")

# ── Toolchain consistency guard ─────────────────────────────────────
# Two ways the libl4yaml.so link can degenerate into hundreds of
# undefined references to runtime / specialized stdlib symbols:
#
#   1. The `lean` cmake just resolved isn't the one Lake will use.
#      (Common when elan can't walk up to lean-toolchain from the build
#      dir — e.g. when colcon configures from a build/ outside the
#      source tree.)
#   2. A Lake dependency pins a NEWER lean-toolchain than this project.
#      Modern Lake fetches each dep's own toolchain and emits IR
#      referencing runtime/stdlib symbols from THAT version, which
#      then don't exist in this project's libleanshared.so.
#      (Triggered by deps tracking moving inputRevs like `main` /
#      `nightly-testing` — they advance past the parent's pin.)

# 1. lean-toolchain (what Lake will use for THIS project) vs the lean
#    cmake just found.
set(_l4yaml_toolchain_file "${PROJECT_ROOT}/lean-toolchain")
if(EXISTS "${_l4yaml_toolchain_file}")
  file(READ "${_l4yaml_toolchain_file}" _l4yaml_toolchain_pin)
  string(STRIP "${_l4yaml_toolchain_pin}" _l4yaml_toolchain_pin)
  string(REGEX REPLACE "^[^:]*:" "" _l4yaml_expected_ver "${_l4yaml_toolchain_pin}")

  if(NOT LEAN_BIN)
    find_program(LEAN_BIN lean REQUIRED)
  endif()
  execute_process(
    COMMAND "${LEAN_BIN}" --version
    OUTPUT_VARIABLE _l4yaml_lean_version_out
    OUTPUT_STRIP_TRAILING_WHITESPACE
    COMMAND_ERROR_IS_FATAL ANY)
  string(REGEX MATCH "version ([^,]+)" _ "${_l4yaml_lean_version_out}")
  set(_l4yaml_actual_ver "v${CMAKE_MATCH_1}")

  if(NOT _l4yaml_actual_ver STREQUAL _l4yaml_expected_ver)
    message(FATAL_ERROR
      "Lean toolchain mismatch:\n"
      "  ${_l4yaml_toolchain_file} pins : ${_l4yaml_expected_ver}\n"
      "  ${LEAN_BIN} --version reports  : ${_l4yaml_actual_ver}\n"
      "  --print-prefix returned        : ${LEAN_SYSROOT}\n"
      "\n"
      "Lake will generate IR with the pinned toolchain but cmake would "
      "link it against a different libleanshared.so — producing "
      "hundreds of undefined references at the libl4yaml.so link step.\n"
      "\n"
      "Fix: ensure elan's shim directory is first on PATH (so `lean` "
      "resolves to the elan-managed toolchain that matches "
      "${_l4yaml_toolchain_file}), or run `elan show` from "
      "${PROJECT_ROOT} to install the pinned toolchain.")
  endif()
endif()

# 2. Each Lake-resolved dep's lean-toolchain vs the parent project's.
#    Lake compiles a dep with that dep's own pin, then we link
#    everything against this project's libleanshared.so — if a dep is
#    NEWER than the parent, its IR uses runtime / specialized stdlib
#    symbols that don't exist in the parent's libleanshared.so.
#    Override with -DL4YAML_SKIP_DEP_TOOLCHAIN_CHECK=ON if you've
#    verified the mismatch is benign.
option(L4YAML_SKIP_DEP_TOOLCHAIN_CHECK
  "Skip the cross-check that every .lake/packages/*/lean-toolchain \
matches the parent project's lean-toolchain" OFF)
set(_l4yaml_packages_dir "${PROJECT_ROOT}/.lake/packages")
if(EXISTS "${_l4yaml_packages_dir}"
   AND EXISTS "${_l4yaml_toolchain_file}"
   AND NOT L4YAML_SKIP_DEP_TOOLCHAIN_CHECK)
  file(GLOB _l4yaml_pkg_dirs LIST_DIRECTORIES true "${_l4yaml_packages_dir}/*")
  set(_l4yaml_dep_mismatches "")
  foreach(_pkg_dir ${_l4yaml_pkg_dirs})
    if(IS_DIRECTORY "${_pkg_dir}" AND EXISTS "${_pkg_dir}/lean-toolchain")
      file(READ "${_pkg_dir}/lean-toolchain" _pkg_tc)
      string(STRIP "${_pkg_tc}" _pkg_tc)
      if(NOT _pkg_tc STREQUAL _l4yaml_toolchain_pin)
        get_filename_component(_pkg_name "${_pkg_dir}" NAME)
        list(APPEND _l4yaml_dep_mismatches "  ${_pkg_name}: ${_pkg_tc}")
      endif()
    endif()
  endforeach()
  if(_l4yaml_dep_mismatches)
    string(JOIN "\n" _l4yaml_dep_mismatches_str ${_l4yaml_dep_mismatches})
    message(FATAL_ERROR
      "Lake dependency toolchain mismatch.\n"
      "\n"
      "${_l4yaml_toolchain_file} pins:\n"
      "  ${_l4yaml_toolchain_pin}\n"
      "\n"
      "But these deps under ${_l4yaml_packages_dir}/ pin different versions:\n"
      "${_l4yaml_dep_mismatches_str}\n"
      "\n"
      "Lake compiles each dep with its OWN toolchain, producing IR that "
      "references that toolchain's runtime / specialized stdlib symbols. "
      "Linking the combined IR against this project's libleanshared.so "
      "then fails with hundreds of undefined references.\n"
      "\n"
      "Fix options:\n"
      "  (1) Pin those deps to revisions compatible with "
      "${_l4yaml_toolchain_pin} in lakefile.toml (instead of tracking "
      "moving inputRevs like `main` / `nightly-testing`), then\n"
      "      rm -rf ${PROJECT_ROOT}/.lake && lake update\n"
      "  (2) Bump ${_l4yaml_toolchain_file} to the version the deps "
      "now require, then re-bootstrap.\n"
      "  (3) -DL4YAML_SKIP_DEP_TOOLCHAIN_CHECK=ON if you've verified "
      "the mix is intentional and the link still resolves.")
  endif()
endif()

# ── Collect Lean IR C files ──────────────────────────────────────────
file(GLOB_RECURSE LEAN_IR_SOURCES "${IR_DIR}/L4YAML/*.c")
if(EXISTS "${IR_DIR}/L4YAML.c")
  list(APPEND LEAN_IR_SOURCES "${IR_DIR}/L4YAML.c")
endif()

# ── Collect Lake dependency IR files ─────────────────────────────────
set(PACKAGES_DIR "${PROJECT_ROOT}/.lake/packages")
file(GLOB LAKE_PACKAGE_DIRS "${PACKAGES_DIR}/*")
set(NATIVE_C_SOURCES "")
set(NATIVE_ARCHIVES "")
# Tooling-only Lake packages whose IR is invoked only via `lake exe …`
# (DocGen4, importGraph) — never linked into libl4yaml.so.  Both
# bundle `lean_exe` entry points (collide on `main`) and reference the
# Lake runtime (`l_Lake_Manifest_*`) which isn't part of this shared
# library.  Add new tooling-only packages here as they appear.
set(L4YAML_FFI_SKIP_PACKAGES "DocGen4" "importGraph")

foreach(PKG_DIR ${LAKE_PACKAGE_DIRS})
  if(IS_DIRECTORY "${PKG_DIR}")
    get_filename_component(PKG_NAME "${PKG_DIR}" NAME)
    if(PKG_NAME IN_LIST L4YAML_FFI_SKIP_PACKAGES)
      message(STATUS "Skipping tooling package ${PKG_NAME} from libl4yaml IR collection")
      continue()
    endif()
    file(GLOB_RECURSE PKG_IR_SOURCES "${PKG_DIR}/.lake/build/ir/*.c")
    # Safety net for any other dep that bundles a `lean_exe` entry: drop
    # top-level `Main*.c` (Lake convention for exe roots) so two `main`
    # symbols can't sneak through.
    list(FILTER PKG_IR_SOURCES EXCLUDE REGEX
      "\\.lake/build/ir/Main[A-Za-z0-9_]*\\.c$")
    list(APPEND LEAN_IR_SOURCES ${PKG_IR_SOURCES})
    # Native C libraries (e.g. UnicodeBasic/UnicodeCLib/*.c)
    file(GLOB_RECURSE PKG_NATIVE_C
      "${PKG_DIR}/*CLib/*.c"
      "${PKG_DIR}/*clib/*.c")
    list(APPEND NATIVE_C_SOURCES ${PKG_NATIVE_C})
    # Static archives (e.g. MD4Lean libleanmd4c.a)
    file(GLOB_RECURSE PKG_ARCHIVES "${PKG_DIR}/.lake/build/lib/*.a")
    list(APPEND NATIVE_ARCHIVES ${PKG_ARCHIVES})
  endif()
endforeach()

list(LENGTH NATIVE_C_SOURCES NATIVE_C_COUNT)
if(NATIVE_C_COUNT GREATER 0)
  message(STATUS "Found ${NATIVE_C_COUNT} native C source files from dependencies")
endif()
list(LENGTH NATIVE_ARCHIVES NATIVE_ARCHIVE_COUNT)
if(NATIVE_ARCHIVE_COUNT GREATER 0)
  message(STATUS "Found ${NATIVE_ARCHIVE_COUNT} native archives from dependencies")
endif()

list(LENGTH LEAN_IR_SOURCES IR_COUNT)
if(IR_COUNT EQUAL 0)
  message(FATAL_ERROR
    "No Lean IR .c files found under ${IR_DIR}.\n"
    "Run 'lake build L4YAML' first.")
endif()
message(STATUS "Found ${IR_COUNT} Lean IR C files (including dependencies)")

# ── Shared library target ───────────────────────────────────────────
add_library(l4yaml SHARED
  l4yaml_shim.c
  ${LEAN_IR_SOURCES}
  ${NATIVE_C_SOURCES})

target_include_directories(l4yaml PRIVATE "${LEAN_INCLUDE_DIR}")

# Suppress warnings from Lean-generated IR code and native deps; keep for shim
set_source_files_properties(${LEAN_IR_SOURCES} ${NATIVE_C_SOURCES}
  PROPERTIES COMPILE_OPTIONS "-w")

target_compile_options(l4yaml PRIVATE -O2)

# Link against libleanshared.so — the 138M umbrella that bundles the
# entire Lean stdlib (Init / Std / Lean.Meta / Lean.Compiler /
# Lean.Server / runtime).  We do NOT use the .a archives: lake compiles
# them with TLS local-exec relocations (they're meant for executables),
# so linking them into a .so fails with R_X86_64_TPOFF32 errors.
#
# PUBLIC visibility is critical: modern linkers default to
# --no-copy-dt-needed-entries, so the consumer (tryparse_c) won't pick
# up libleanshared.so via libl4yaml.so's NEEDED entry.  PUBLIC adds it
# to consumers' link lines explicitly.
target_link_directories(l4yaml PUBLIC "${LEAN_LIB_DIR}")
target_link_libraries(l4yaml
  PRIVATE ${NATIVE_ARCHIVES} m
  PUBLIC  leanshared)

# Catch missing symbols at libl4yaml.so link time rather than later
# when downstream consumers fail.
target_link_options(l4yaml PRIVATE "-Wl,--no-undefined")

set_target_properties(l4yaml PROPERTIES
  BUILD_RPATH   "${LEAN_LIB_DIR}"
  INSTALL_RPATH "${LEAN_LIB_DIR}")

# ── Install ─────────────────────────────────────────────────────────
include(GNUInstallDirs)
install(TARGETS l4yaml
        LIBRARY DESTINATION "${CMAKE_INSTALL_LIBDIR}"
        COMPONENT L4YAML_Runtime)
install(FILES l4yaml.h
        DESTINATION "${CMAKE_INSTALL_INCLUDEDIR}"
        COMPONENT L4YAML_Devel)

# ── tryparse_c executable (for cross-language yaml-test-suite) ──────
add_executable(tryparse_c tryparse_c.c)
target_include_directories(tryparse_c PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(tryparse_c PRIVATE l4yaml)
# RPATH: $ORIGIN/../<libdir> finds installed libl4yaml.so;
# LEAN_LIB_DIR finds libleanshared.so.
set_target_properties(tryparse_c PROPERTIES
  BUILD_RPATH   "\$ORIGIN;${LEAN_LIB_DIR}"
  INSTALL_RPATH "\$ORIGIN/../${CMAKE_INSTALL_LIBDIR};${LEAN_LIB_DIR}")
install(TARGETS tryparse_c
        RUNTIME DESTINATION "${CMAKE_INSTALL_BINDIR}"
        COMPONENT L4YAML_Runtime)
