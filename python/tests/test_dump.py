"""Tests for dumping YAML values back to strings."""
from __future__ import annotations

import pytest

try:
    import lean4yaml

    _LIB_AVAILABLE = True
except OSError:
    _LIB_AVAILABLE = False

needs_lib = pytest.mark.skipif(
    not _LIB_AVAILABLE,
    reason="liblean4yaml.so not found",
)


@needs_lib
class TestDump:
    def test_dump_scalar(self) -> None:
        v = lean4yaml.load("hello")
        out = lean4yaml.dump(v)
        assert "hello" in out

    def test_dump_mapping(self) -> None:
        v = lean4yaml.load("a: 1\nb: 2")
        out = lean4yaml.dump(v)
        assert "a" in out
        assert "b" in out

    def test_dump_sequence(self) -> None:
        v = lean4yaml.load("[x, y, z]")
        out = lean4yaml.dump(v)
        assert "x" in out
        assert "z" in out

    def test_repr_uses_dump(self) -> None:
        v = lean4yaml.load("key: value")
        r = repr(v)
        assert "key" in r


@needs_lib
class TestDumpConfigured:
    def test_configured_dump(self) -> None:
        v = lean4yaml.load("key: value")
        # Use default-ish config in YAML form
        cfg = "defaultStyle: block"
        out = lean4yaml.dump_configured(v, config_yaml=cfg)
        assert "key" in out
