"""YAML value types backed by opaque Lean handles.

Each :class:`YamlValue` wraps a ``lean_object *`` pointer obtained from
the C API.  The handle is freed via ``lean4yaml_free`` when the Python
object is garbage-collected.

Child values obtained through :meth:`__getitem__`, :meth:`items`, etc.
are **owned** handles — the C accessor functions return new references
that must be freed independently.
"""
from __future__ import annotations

import ctypes
from typing import Iterator

from lean4yaml import _ffi
from lean4yaml.exceptions import Lean4YamlError

# Node kind constants (must match lean4yaml.h)
_SCALAR: int = 0
_SEQUENCE: int = 1
_MAPPING: int = 2
_ALIAS: int = 3

_KIND_NAMES: dict[int, str] = {
    _SCALAR: "scalar",
    _SEQUENCE: "sequence",
    _MAPPING: "mapping",
    _ALIAS: "alias",
}


class YamlValue:
    """Immutable YAML value backed by an opaque Lean handle.

    Do not instantiate directly — use :func:`lean4yaml.load` or
    :func:`lean4yaml.load_all` to obtain values.
    """

    __slots__ = ("_handle", "_lib")

    def __init__(self, handle: int, lib: ctypes.CDLL | None = None) -> None:
        if not handle:
            raise Lean4YamlError("Cannot create YamlValue from null handle")
        self._handle: int = handle
        self._lib: ctypes.CDLL = lib or _ffi.get_lib()

    def __del__(self) -> None:
        h: int = getattr(self, "_handle", 0)
        if h:
            self._lib.lean4yaml_free(h)
            self._handle = 0

    # ── Kind ─────────────────────────────────────────────────────────

    @property
    def kind(self) -> str:
        """Node kind: ``"scalar"``, ``"sequence"``, ``"mapping"``."""
        k: int = self._lib.lean4yaml_value_kind(self._handle)
        return _KIND_NAMES.get(k, "unknown")

    @property
    def _kind_id(self) -> int:
        return self._lib.lean4yaml_value_kind(self._handle)

    # ── Scalar ───────────────────────────────────────────────────────

    def as_str(self) -> str:
        """Return scalar content as a Python string.

        Raises:
            Lean4YamlError: If the value is not a scalar.
        """
        if self._kind_id != _SCALAR:
            raise Lean4YamlError(
                f"as_str() requires a scalar, got {self.kind}"
            )
        raw: bytes | None = self._lib.lean4yaml_value_string(self._handle)
        if raw is None:
            return ""
        return raw.decode("utf-8")

    # ── Sequence ─────────────────────────────────────────────────────

    def as_list(self) -> list[YamlValue]:
        """Return sequence items as a list of :class:`YamlValue`.

        Raises:
            Lean4YamlError: If the value is not a sequence.
        """
        if self._kind_id != _SEQUENCE:
            raise Lean4YamlError(
                f"as_list() requires a sequence, got {self.kind}"
            )
        n: int = self._lib.lean4yaml_value_seq_length(self._handle)
        result: list[YamlValue] = []
        for i in range(n):
            h: int = self._lib.lean4yaml_value_seq_get(self._handle, i)
            result.append(YamlValue(handle=h, lib=self._lib))
        return result

    # ── Mapping ──────────────────────────────────────────────────────

    def as_dict(self) -> dict[str, YamlValue]:
        """Return mapping as ``{str: YamlValue}`` dict.

        Only works for mappings with string keys.

        Raises:
            Lean4YamlError: If the value is not a mapping.
        """
        if self._kind_id != _MAPPING:
            raise Lean4YamlError(
                f"as_dict() requires a mapping, got {self.kind}"
            )
        n: int = self._lib.lean4yaml_value_map_length(self._handle)
        result: dict[str, YamlValue] = {}
        for i in range(n):
            kh: int = self._lib.lean4yaml_value_map_key(self._handle, i)
            key_val = YamlValue(handle=kh, lib=self._lib)
            key_str: str = key_val.as_str()
            vh: int = self._lib.lean4yaml_value_map_val(self._handle, i)
            result[key_str] = YamlValue(handle=vh, lib=self._lib)
        return result

    def keys(self) -> list[str]:
        """Return mapping keys as a list of strings."""
        if self._kind_id != _MAPPING:
            raise Lean4YamlError(
                f"keys() requires a mapping, got {self.kind}"
            )
        n: int = self._lib.lean4yaml_value_map_length(self._handle)
        result: list[str] = []
        for i in range(n):
            kh: int = self._lib.lean4yaml_value_map_key(self._handle, i)
            key_val = YamlValue(handle=kh, lib=self._lib)
            result.append(key_val.as_str())
        return result

    def items(self) -> list[tuple[str, YamlValue]]:
        """Return mapping as a list of ``(key_str, value)`` pairs."""
        if self._kind_id != _MAPPING:
            raise Lean4YamlError(
                f"items() requires a mapping, got {self.kind}"
            )
        n: int = self._lib.lean4yaml_value_map_length(self._handle)
        result: list[tuple[str, YamlValue]] = []
        for i in range(n):
            kh: int = self._lib.lean4yaml_value_map_key(self._handle, i)
            key_val = YamlValue(handle=kh, lib=self._lib)
            key_str: str = key_val.as_str()
            vh: int = self._lib.lean4yaml_value_map_val(self._handle, i)
            result.append((key_str, YamlValue(handle=vh, lib=self._lib)))
        return result

    # ── Tag / Anchor ─────────────────────────────────────────────────

    @property
    def tag(self) -> str | None:
        """YAML tag (e.g. ``"!!int"``), or ``None`` if untagged."""
        raw: bytes | None = self._lib.lean4yaml_value_tag(self._handle)
        if raw is None:
            return None
        return raw.decode("utf-8")

    @property
    def anchor(self) -> str | None:
        """YAML anchor name, or ``None`` if not anchored."""
        raw: bytes | None = self._lib.lean4yaml_value_anchor(self._handle)
        if raw is None:
            return None
        return raw.decode("utf-8")

    # ── Dunder protocols ─────────────────────────────────────────────

    def __len__(self) -> int:
        k: int = self._kind_id
        if k == _SEQUENCE:
            return self._lib.lean4yaml_value_seq_length(self._handle)
        if k == _MAPPING:
            return self._lib.lean4yaml_value_map_length(self._handle)
        raise Lean4YamlError(f"len() not supported for {self.kind}")

    def __getitem__(self, key: str | int) -> YamlValue:
        if isinstance(key, int):
            if self._kind_id != _SEQUENCE:
                raise Lean4YamlError(
                    f"integer indexing requires a sequence, got {self.kind}"
                )
            n: int = self._lib.lean4yaml_value_seq_length(self._handle)
            if key < 0:
                key += n
            if key < 0 or key >= n:
                raise IndexError(f"sequence index {key} out of range [0, {n})")
            h: int = self._lib.lean4yaml_value_seq_get(self._handle, key)
            return YamlValue(handle=h, lib=self._lib)

        if isinstance(key, str):
            if self._kind_id != _MAPPING:
                raise Lean4YamlError(
                    f"string key lookup requires a mapping, got {self.kind}"
                )
            key_bytes: bytes = key.encode("utf-8")
            h = self._lib.lean4yaml_value_lookup(self._handle, key_bytes)
            if not h:
                raise KeyError(key)
            return YamlValue(handle=h, lib=self._lib)

        raise TypeError(f"key must be str or int, got {type(key).__name__}")

    def __contains__(self, key: str) -> bool:
        if self._kind_id != _MAPPING:
            return False
        key_bytes: bytes = key.encode("utf-8")
        h: int = self._lib.lean4yaml_value_lookup(self._handle, key_bytes)
        if h:
            self._lib.lean4yaml_free(h)
            return True
        return False

    def __iter__(self) -> Iterator[YamlValue | tuple[str, YamlValue]]:
        k: int = self._kind_id
        if k == _SEQUENCE:
            n: int = self._lib.lean4yaml_value_seq_length(self._handle)
            for i in range(n):
                h: int = self._lib.lean4yaml_value_seq_get(self._handle, i)
                yield YamlValue(handle=h, lib=self._lib)
        elif k == _MAPPING:
            yield from self.items()
        else:
            raise Lean4YamlError(f"iteration not supported for {self.kind}")

    def __repr__(self) -> str:
        raw: bytes | None = self._lib.lean4yaml_dump(self._handle)
        if raw is None:
            return f"YamlValue({self.kind})"
        return raw.decode("utf-8").rstrip("\n")

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, YamlValue):
            return NotImplemented
        return repr(self) == repr(other)

    def __hash__(self) -> int:
        return hash(repr(self))


class YamlDocument:
    """A parsed YAML document with its root value.

    Wraps an opaque ``lean4yaml_doc_t`` handle.
    """

    __slots__ = ("_handle", "_lib", "_root")

    def __init__(self, handle: int, lib: ctypes.CDLL) -> None:
        self._handle: int = handle
        self._lib: ctypes.CDLL = lib
        self._root: YamlValue | None = None

    def __del__(self) -> None:
        h: int = getattr(self, "_handle", 0)
        if h:
            self._lib.lean4yaml_free(h)
            self._handle = 0

    @property
    def root(self) -> YamlValue:
        """Root :class:`YamlValue` of this document."""
        if self._root is None:
            h: int = self._lib.lean4yaml_doc_root(self._handle)
            self._root = YamlValue(handle=h, lib=self._lib)
        return self._root
