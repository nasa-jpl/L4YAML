# ffi/CMakeLists.txt — Build liblean4yaml.so from Lean IR + C shim
#
# Prerequisites:
#   lake build Lean4Yaml    (generates .lake/build/ir/*.c)
#
# Usage:
#   cmake -B ffi/out -S ffi
#   cmake --build ffi/out
#
# Or with a custom Lean sysroot:
#   cmake -B ffi/out -S ffi -DLEAN_SYSROOT=/path/to/lean
#
cmake_minimum_required(VERSION 3.16)
project(lean4yaml C)

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

# ── Collect Lean IR C files ──────────────────────────────────────────
set(PROJECT_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/..")
set(IR_DIR "${PROJECT_ROOT}/.lake/build/ir")

file(GLOB_RECURSE LEAN_IR_SOURCES "${IR_DIR}/Lean4Yaml/*.c")
if(EXISTS "${IR_DIR}/Lean4Yaml.c")
  list(APPEND LEAN_IR_SOURCES "${IR_DIR}/Lean4Yaml.c")
endif()

list(LENGTH LEAN_IR_SOURCES IR_COUNT)
if(IR_COUNT EQUAL 0)
  message(FATAL_ERROR
    "No Lean IR .c files found under ${IR_DIR}.\n"
    "Run 'lake build Lean4Yaml' first.")
endif()
message(STATUS "Found ${IR_COUNT} Lean IR C files")

# ── Shared library target ───────────────────────────────────────────
add_library(lean4yaml SHARED
  lean4yaml_shim.c
  ${LEAN_IR_SOURCES})

target_include_directories(lean4yaml PRIVATE "${LEAN_INCLUDE_DIR}")

# Suppress warnings from Lean-generated IR code; keep warnings for the shim
set_source_files_properties(${LEAN_IR_SOURCES}
  PROPERTIES COMPILE_OPTIONS "-w")

target_compile_options(lean4yaml PRIVATE -O2)

# Link against libleanshared and set RPATH so it's found at runtime
target_link_directories(lean4yaml PRIVATE "${LEAN_LIB_DIR}")
target_link_libraries(lean4yaml PRIVATE leanshared)
set_target_properties(lean4yaml PROPERTIES
  BUILD_RPATH   "${LEAN_LIB_DIR}"
  INSTALL_RPATH "${LEAN_LIB_DIR}")

# ── Install (optional) ──────────────────────────────────────────────
install(TARGETS lean4yaml LIBRARY DESTINATION lib)
install(FILES lean4yaml.h DESTINATION include)
