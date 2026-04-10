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

# ── Collect Lean IR C files ──────────────────────────────────────────
set(PROJECT_ROOT "${CMAKE_CURRENT_SOURCE_DIR}/..")
set(IR_DIR "${PROJECT_ROOT}/.lake/build/ir")

file(GLOB_RECURSE LEAN_IR_SOURCES "${IR_DIR}/L4YAML/*.c")
if(EXISTS "${IR_DIR}/L4YAML.c")
  list(APPEND LEAN_IR_SOURCES "${IR_DIR}/L4YAML.c")
endif()

# ── Collect Lake dependency IR files ─────────────────────────────────
set(PACKAGES_DIR "${PROJECT_ROOT}/.lake/packages")
file(GLOB LAKE_PACKAGE_DIRS "${PACKAGES_DIR}/*")
set(NATIVE_C_SOURCES "")
set(NATIVE_ARCHIVES "")
foreach(PKG_DIR ${LAKE_PACKAGE_DIRS})
  if(IS_DIRECTORY "${PKG_DIR}")
    file(GLOB_RECURSE PKG_IR_SOURCES "${PKG_DIR}/.lake/build/ir/*.c")
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

# Link against libleanshared, native archives, and set RPATH
target_link_directories(l4yaml PRIVATE "${LEAN_LIB_DIR}")
target_link_libraries(l4yaml PRIVATE leanshared ${NATIVE_ARCHIVES})
set_target_properties(l4yaml PROPERTIES
  BUILD_RPATH   "${LEAN_LIB_DIR}"
  INSTALL_RPATH "${LEAN_LIB_DIR}")

# ── Install (optional) ──────────────────────────────────────────────
install(TARGETS l4yaml LIBRARY DESTINATION lib)
install(FILES l4yaml.h DESTINATION include)

# ── tryparse_c executable (for cross-language yaml-test-suite) ──────
add_executable(tryparse_c tryparse_c.c)
target_include_directories(tryparse_c PRIVATE "${CMAKE_CURRENT_SOURCE_DIR}")
target_link_libraries(tryparse_c PRIVATE l4yaml)
set_target_properties(tryparse_c PROPERTIES
  BUILD_RPATH   "$ORIGIN;${LEAN_LIB_DIR}"
  INSTALL_RPATH "$ORIGIN;${LEAN_LIB_DIR}")
