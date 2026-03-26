"""Low-level ctypes bindings to liblean4yaml.so.

This module loads the shared library and exposes every C API function
with proper argtypes/restype declarations.  Higher-level code should
use :mod:`lean4yaml.types` and the public API in :mod:`lean4yaml`
rather than calling these directly.
"""
from __future__ import annotations

import atexit
import ctypes
import os
import sys
from ctypes import (
    POINTER,
    c_char_p,
    c_int,
    c_size_t,
    c_uint8,
    c_uint32,
    c_void_p,
)
from pathlib import Path

# ── Library discovery ────────────────────────────────────────────────

_LIB: ctypes.CDLL | None = None


def _find_library() -> Path:
    """Locate liblean4yaml.so by searching several candidate paths."""
    # 1. Explicit environment variable
    env_path: str | None = os.environ.get("LEAN4YAML_LIB")
    if env_path:
        p = Path(env_path)
        if p.is_file():
            return p

    # 2. Relative to this package (../../../ffi/build/liblean4yaml.so)
    pkg_dir: Path = Path(__file__).resolve().parent
    candidates: list[Path] = [
        pkg_dir / "liblean4yaml.so",
        pkg_dir.parent / "liblean4yaml.so",
        pkg_dir.parent.parent.parent / "ffi" / "build" / "liblean4yaml.so",
        pkg_dir.parent.parent.parent / "ffi" / "out" / "liblean4yaml.so",
    ]

    # 3. Platform-specific extension
    if sys.platform == "darwin":
        candidates.extend(
            [p.with_suffix(".dylib") for p in candidates]
        )

    for candidate in candidates:
        if candidate.is_file():
            return candidate

    raise OSError(
        "Cannot find liblean4yaml.so. Set LEAN4YAML_LIB environment "
        "variable to the full path, or place the library next to this "
        "package."
    )


def _load_lib() -> ctypes.CDLL:
    """Load the shared library and declare all function signatures."""
    global _LIB  # noqa: PLW0603
    if _LIB is not None:
        return _LIB

    lib_path: Path = _find_library()

    # Load libleanshared first so its symbols are available for our lib.
    # Lean sysroot detection: elan toolchains or LEAN_SYSROOT env.
    lean_sysroot: str | None = os.environ.get("LEAN_SYSROOT")
    if not lean_sysroot:
        import shutil
        lean_bin: str | None = shutil.which("lean")
        if lean_bin:
            import subprocess
            try:
                lean_sysroot = subprocess.check_output(
                    [lean_bin, "--print-prefix"],
                    text=True,
                ).strip()
            except subprocess.CalledProcessError:
                pass
    if lean_sysroot:
        lean_lib = Path(lean_sysroot) / "lib" / "lean"
        lean_shared = lean_lib / "libleanshared.so"
        if sys.platform == "darwin":
            lean_shared = lean_lib / "libleanshared.dylib"
        if lean_shared.is_file():
            ctypes.CDLL(str(lean_shared), mode=ctypes.RTLD_GLOBAL)

    lib: ctypes.CDLL = ctypes.CDLL(str(lib_path))

    # ── Lifecycle ────────────────────────────────────────────────────
    lib.lean4yaml_initialize.argtypes = []
    lib.lean4yaml_initialize.restype = None

    lib.lean4yaml_finalize.argtypes = []
    lib.lean4yaml_finalize.restype = None

    lib.lean4yaml_init_fixed_pool.argtypes = [c_size_t]
    lib.lean4yaml_init_fixed_pool.restype = c_int

    lib.lean4yaml_init_static_pool.argtypes = [c_void_p, c_size_t]
    lib.lean4yaml_init_static_pool.restype = c_int

    # ── Parsing ──────────────────────────────────────────────────────
    lib.lean4yaml_parse.argtypes = [c_char_p, c_size_t, c_uint8]
    lib.lean4yaml_parse.restype = c_void_p

    lib.lean4yaml_parse_single.argtypes = [c_char_p, c_size_t, c_uint8]
    lib.lean4yaml_parse_single.restype = c_void_p

    # ── Result inspection ────────────────────────────────────────────
    lib.lean4yaml_result_is_ok.argtypes = [c_void_p]
    lib.lean4yaml_result_is_ok.restype = c_uint8

    lib.lean4yaml_result_error_message.argtypes = [c_void_p]
    lib.lean4yaml_result_error_message.restype = c_char_p

    # ── Multi-document access ────────────────────────────────────────
    lib.lean4yaml_result_docs.argtypes = [c_void_p]
    lib.lean4yaml_result_docs.restype = c_void_p

    lib.lean4yaml_docs_count.argtypes = [c_void_p]
    lib.lean4yaml_docs_count.restype = c_uint32

    lib.lean4yaml_docs_get.argtypes = [c_void_p, c_uint32]
    lib.lean4yaml_docs_get.restype = c_void_p

    lib.lean4yaml_doc_root.argtypes = [c_void_p]
    lib.lean4yaml_doc_root.restype = c_void_p

    # ── Single-document access ───────────────────────────────────────
    lib.lean4yaml_result_value.argtypes = [c_void_p]
    lib.lean4yaml_result_value.restype = c_void_p

    # ── Value inspection ─────────────────────────────────────────────
    lib.lean4yaml_value_kind.argtypes = [c_void_p]
    lib.lean4yaml_value_kind.restype = c_uint8

    lib.lean4yaml_value_string.argtypes = [c_void_p]
    lib.lean4yaml_value_string.restype = c_char_p

    lib.lean4yaml_value_seq_length.argtypes = [c_void_p]
    lib.lean4yaml_value_seq_length.restype = c_uint32

    lib.lean4yaml_value_seq_get.argtypes = [c_void_p, c_uint32]
    lib.lean4yaml_value_seq_get.restype = c_void_p

    lib.lean4yaml_value_map_length.argtypes = [c_void_p]
    lib.lean4yaml_value_map_length.restype = c_uint32

    lib.lean4yaml_value_map_key.argtypes = [c_void_p, c_uint32]
    lib.lean4yaml_value_map_key.restype = c_void_p

    lib.lean4yaml_value_map_val.argtypes = [c_void_p, c_uint32]
    lib.lean4yaml_value_map_val.restype = c_void_p

    lib.lean4yaml_value_lookup.argtypes = [c_void_p, c_char_p]
    lib.lean4yaml_value_lookup.restype = c_void_p

    lib.lean4yaml_value_tag.argtypes = [c_void_p]
    lib.lean4yaml_value_tag.restype = c_char_p

    lib.lean4yaml_value_anchor.argtypes = [c_void_p]
    lib.lean4yaml_value_anchor.restype = c_char_p

    # ── Dumping ──────────────────────────────────────────────────────
    lib.lean4yaml_dump.argtypes = [c_void_p]
    lib.lean4yaml_dump.restype = c_char_p

    lib.lean4yaml_dump_docs.argtypes = [c_void_p]
    lib.lean4yaml_dump_docs.restype = c_char_p

    lib.lean4yaml_dump_configured.argtypes = [c_void_p, c_char_p, c_size_t]
    lib.lean4yaml_dump_configured.restype = c_char_p

    # ── Config deserialization ───────────────────────────────────────
    lib.lean4yaml_parse_limits_yaml.argtypes = [c_char_p, c_size_t]
    lib.lean4yaml_parse_limits_yaml.restype = c_void_p

    lib.lean4yaml_config_is_ok.argtypes = [c_void_p]
    lib.lean4yaml_config_is_ok.restype = c_uint8

    lib.lean4yaml_config_error_message.argtypes = [c_void_p]
    lib.lean4yaml_config_error_message.restype = c_char_p

    lib.lean4yaml_config_get_limits.argtypes = [c_void_p]
    lib.lean4yaml_config_get_limits.restype = c_void_p

    lib.lean4yaml_parse_configured.argtypes = [
        c_char_p, c_size_t, c_char_p, c_size_t,
    ]
    lib.lean4yaml_parse_configured.restype = c_void_p

    # ── Memory management ────────────────────────────────────────────
    lib.lean4yaml_free.argtypes = [c_void_p]
    lib.lean4yaml_free.restype = None

    _LIB = lib
    return lib


# ── Runtime lifecycle ────────────────────────────────────────────────

_INITIALIZED: bool = False


def ensure_initialized() -> ctypes.CDLL:
    """Load the library and initialize the Lean runtime (once)."""
    global _INITIALIZED  # noqa: PLW0603
    lib: ctypes.CDLL = _load_lib()
    if not _INITIALIZED:
        lib.lean4yaml_initialize()
        atexit.register(lib.lean4yaml_finalize)
        _INITIALIZED = True
    return lib


def init_pool(pool_bytes: int) -> None:
    """Pre-allocate a fixed-size memory pool (OS-backed, via mmap).

    Must be called **before** any parsing.  Intended for flight software
    or memory-constrained environments.

    Args:
        pool_bytes: Size of the memory pool in bytes.

    Raises:
        RuntimeError: If pool allocation fails.
    """
    lib: ctypes.CDLL = _load_lib()
    rc: int = lib.lean4yaml_init_fixed_pool(pool_bytes)
    if rc != 0:
        raise RuntimeError(f"lean4yaml_init_fixed_pool({pool_bytes}) failed: {rc}")


def get_lib() -> ctypes.CDLL:
    """Return the initialized library handle."""
    return ensure_initialized()
