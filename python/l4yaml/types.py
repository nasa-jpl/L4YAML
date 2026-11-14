"""YAML value types backed by opaque Lean handles.

Each :class:`YamlValue` wraps a ``lean_object *`` pointer obtained from
the C API.  The handle is freed via ``l4yaml_free`` when the Python
object is garbage-collected.

Child values obtained through :meth:`__getitem__`, :meth:`items`, etc.
are **owned** handles — the C accessor functions return new references
that must be freed independently.
"""
from __future__ import annotations

import ctypes
from typing import Any, Iterator

from l4yaml import _ffi
from l4yaml.exceptions import L4YAMLError

# Node kind constants (must match l4yaml.h)
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

# Scalar style constants (must match l4yaml.h L4YAML_STYLE_*)
_PLAIN: int = 0

_STYLE_NAMES: dict[int, str] = {
    _PLAIN: "plain",
    1: "single_quoted",
    2: "double_quoted",
    3: "literal",
    4: "folded",
}


class YamlValue:
    """Immutable YAML value backed by an opaque Lean handle.

    Do not instantiate directly — use :func:`l4yaml.load` or
    :func:`l4yaml.load_all` to obtain values.
    """

    __slots__ = ("_handle", "_lib", "_repr")

    def __init__(self, handle: int, lib: ctypes.CDLL | None = None) -> None:
        if not handle:
            raise L4YAMLError("Cannot create YamlValue from null handle")
        self._handle: int = handle
        self._lib: ctypes.CDLL = lib or _ffi.get_lib()
        # Dump cache for __repr__/__eq__/__hash__; valid because the
        # Lean value behind the handle never changes.
        self._repr: str | None = None

    def __del__(self) -> None:
        h: int = getattr(self, "_handle", 0)
        if h:
            self._lib.l4yaml_free(h)
            self._handle = 0

    # ── Kind ─────────────────────────────────────────────────────────

    @property
    def kind(self) -> str:
        """Node kind: ``"scalar"``, ``"sequence"``, ``"mapping"``."""
        k: int = self._lib.l4yaml_value_kind(self._handle)
        return _KIND_NAMES.get(k, "unknown")

    @property
    def _kind_id(self) -> int:
        return self._lib.l4yaml_value_kind(self._handle)

    # ── Scalar ───────────────────────────────────────────────────────

    @property
    def style(self) -> str | None:
        """Scalar presentation style: ``"plain"``, ``"single_quoted"``,
        ``"double_quoted"``, ``"literal"``, or ``"folded"``;
        ``None`` for non-scalar values.

        Per the YAML 1.2 Core Schema (§10.3.2) only PLAIN scalars are
        subject to type resolution — quoted and block scalars are
        always strings.
        """
        return _STYLE_NAMES.get(self._style_id)

    @property
    def _style_id(self) -> int:
        return self._lib.l4yaml_value_scalar_style(self._handle)

    def as_str(self) -> str:
        """Return scalar content as a Python string.

        Raises:
            L4YAMLError: If the value is not a scalar.
        """
        if self._kind_id != _SCALAR:
            raise L4YAMLError(
                f"as_str() requires a scalar, got {self.kind}"
            )
        return self._str_unchecked()

    def _str_unchecked(self) -> str:
        """Scalar content for a handle the caller already knows is a scalar."""
        byte_len = ctypes.c_size_t()
        ptr: int = self._lib.l4yaml_value_string_bytes(
            self._handle, ctypes.byref(byte_len)
        )
        if not ptr:
            return ""
        return ctypes.string_at(ptr, byte_len.value).decode("utf-8")

    # ── Sequence ─────────────────────────────────────────────────────

    def as_list(self) -> list[YamlValue]:
        """Return sequence items as a list of :class:`YamlValue`.

        Raises:
            L4YAMLError: If the value is not a sequence.
        """
        if self._kind_id != _SEQUENCE:
            raise L4YAMLError(
                f"as_list() requires a sequence, got {self.kind}"
            )
        return list(self._seq_unchecked())

    def _seq_unchecked(self) -> Iterator[YamlValue]:
        """Items of a handle the caller already knows is a sequence."""
        lib = self._lib
        h: int = self._handle
        for i in range(lib.l4yaml_value_seq_length(h)):
            yield YamlValue(handle=lib.l4yaml_value_seq_get(h, i), lib=lib)

    # ── Mapping ──────────────────────────────────────────────────────

    def as_dict(self) -> dict[str, YamlValue]:
        """Return mapping as ``{str: YamlValue}`` dict.

        Only works for mappings with string keys.

        Raises:
            L4YAMLError: If the value is not a mapping.
        """
        if self._kind_id != _MAPPING:
            raise L4YAMLError(
                f"as_dict() requires a mapping, got {self.kind}"
            )
        return {k.as_str(): v for k, v in self._map_unchecked()}

    def _map_unchecked(self) -> Iterator[tuple[YamlValue, YamlValue]]:
        """Pairs of a handle the caller already knows is a mapping."""
        lib = self._lib
        h: int = self._handle
        for i in range(lib.l4yaml_value_map_length(h)):
            key_val = YamlValue(handle=lib.l4yaml_value_map_key(h, i), lib=lib)
            yield key_val, YamlValue(handle=lib.l4yaml_value_map_val(h, i), lib=lib)

    def keys(self) -> list[str]:
        """Return mapping keys as a list of strings."""
        if self._kind_id != _MAPPING:
            raise L4YAMLError(
                f"keys() requires a mapping, got {self.kind}"
            )
        lib = self._lib
        h: int = self._handle
        return [
            YamlValue(handle=lib.l4yaml_value_map_key(h, i), lib=lib).as_str()
            for i in range(lib.l4yaml_value_map_length(h))
        ]

    def items(self) -> list[tuple[str, YamlValue]]:
        """Return mapping as a list of ``(key_str, value)`` pairs."""
        if self._kind_id != _MAPPING:
            raise L4YAMLError(
                f"items() requires a mapping, got {self.kind}"
            )
        return [(k.as_str(), v) for k, v in self._map_unchecked()]

    def raw_items(self) -> list[tuple[YamlValue, YamlValue]]:
        """Return mapping as ``(key, value)`` pairs with the keys as
        :class:`YamlValue` — unlike :meth:`items`, which stringifies
        keys and so loses their kind/style/tag."""
        if self._kind_id != _MAPPING:
            raise L4YAMLError(
                f"raw_items() requires a mapping, got {self.kind}"
            )
        return list(self._map_unchecked())

    # ── Tag / Anchor ─────────────────────────────────────────────────

    @property
    def tag(self) -> str | None:
        """YAML tag (e.g. ``"!!int"``), or ``None`` if untagged."""
        raw: bytes | None = self._lib.l4yaml_value_tag(self._handle)
        if raw is None:
            return None
        return raw.decode("utf-8")

    @property
    def anchor(self) -> str | None:
        """YAML anchor name, or ``None`` if not anchored."""
        raw: bytes | None = self._lib.l4yaml_value_anchor(self._handle)
        if raw is None:
            return None
        return raw.decode("utf-8")

    # ── Dunder protocols ─────────────────────────────────────────────

    def __len__(self) -> int:
        k: int = self._kind_id
        if k == _SEQUENCE:
            return self._lib.l4yaml_value_seq_length(self._handle)
        if k == _MAPPING:
            return self._lib.l4yaml_value_map_length(self._handle)
        raise L4YAMLError(f"len() not supported for {self.kind}")

    def __getitem__(self, key: str | int) -> YamlValue:
        if isinstance(key, int):
            if self._kind_id != _SEQUENCE:
                raise L4YAMLError(
                    f"integer indexing requires a sequence, got {self.kind}"
                )
            n: int = self._lib.l4yaml_value_seq_length(self._handle)
            if key < 0:
                key += n
            if key < 0 or key >= n:
                raise IndexError(f"sequence index {key} out of range [0, {n})")
            h: int = self._lib.l4yaml_value_seq_get(self._handle, key)
            return YamlValue(handle=h, lib=self._lib)

        if isinstance(key, str):
            if self._kind_id != _MAPPING:
                raise L4YAMLError(
                    f"string key lookup requires a mapping, got {self.kind}"
                )
            key_bytes: bytes = key.encode("utf-8")
            h = self._lib.l4yaml_value_lookup_bytes(
                self._handle, key_bytes, len(key_bytes)
            )
            if not h:
                raise KeyError(key)
            return YamlValue(handle=h, lib=self._lib)

        raise TypeError(f"key must be str or int, got {type(key).__name__}")

    def __contains__(self, key: str) -> bool:
        if self._kind_id != _MAPPING:
            return False
        key_bytes: bytes = key.encode("utf-8")
        h: int = self._lib.l4yaml_value_lookup_bytes(
            self._handle, key_bytes, len(key_bytes)
        )
        if h:
            self._lib.l4yaml_free(h)
            return True
        return False

    def __iter__(self) -> Iterator[YamlValue | tuple[str, YamlValue]]:
        k: int = self._kind_id
        if k == _SEQUENCE:
            yield from self._seq_unchecked()
        elif k == _MAPPING:
            for key_val, val in self._map_unchecked():
                yield key_val.as_str(), val
        else:
            raise L4YAMLError(f"iteration not supported for {self.kind}")

    def __repr__(self) -> str:
        if self._repr is None:
            raw: bytes | None = self._lib.l4yaml_dump(self._handle)
            if raw is None:
                self._repr = f"YamlValue({self.kind})"
            else:
                self._repr = raw.decode("utf-8").rstrip("\n")
        return self._repr

    def __eq__(self, other: object) -> bool:
        if not isinstance(other, YamlValue):
            return NotImplemented
        return repr(self) == repr(other)

    def __hash__(self) -> int:
        return hash(repr(self))

    def to_python(self) -> Any:
        """Recursively convert to native Python objects.

        Scalars are coerced per the YAML 1.2 Core Schema:
        ``int``, ``float``, ``bool``, ``None``, or ``str``.
        Sequences become ``list``, mappings become ``dict``.
        """
        from l4yaml.compat import to_python

        return to_python(self)


class YamlDocument:
    """A parsed YAML document with its root value.

    Wraps an opaque ``l4yaml_doc_t`` handle.
    """

    __slots__ = ("_handle", "_lib", "_root")

    def __init__(self, handle: int, lib: ctypes.CDLL) -> None:
        self._handle: int = handle
        self._lib: ctypes.CDLL = lib
        self._root: YamlValue | None = None

    def __del__(self) -> None:
        h: int = getattr(self, "_handle", 0)
        if h:
            self._lib.l4yaml_free(h)
            self._handle = 0

    @property
    def root(self) -> YamlValue:
        """Root :class:`YamlValue` of this document."""
        if self._root is None:
            h: int = self._lib.l4yaml_doc_root(self._handle)
            self._root = YamlValue(handle=h, lib=self._lib)
        return self._root
