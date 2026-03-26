"""Round-trip tests: parse → dump → re-parse → compare."""
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
class TestRoundTrip:
    def _roundtrip(self, yaml: str) -> None:
        v1 = lean4yaml.load(yaml)
        dumped = lean4yaml.dump(v1)
        v2 = lean4yaml.load(dumped)
        assert v1 == v2

    def test_scalar(self) -> None:
        self._roundtrip("hello")

    def test_simple_mapping(self) -> None:
        self._roundtrip("a: 1\nb: 2")

    def test_simple_sequence(self) -> None:
        self._roundtrip("- x\n- y\n- z")

    def test_nested_structure(self) -> None:
        yaml = """\
name: test
items:
  - first
  - second
meta:
  version: '1'
"""
        self._roundtrip(yaml)

    def test_flow_sequence(self) -> None:
        v1 = lean4yaml.load("[a, b, c]")
        dumped = lean4yaml.dump(v1)
        v2 = lean4yaml.load(dumped)
        # Compare item-by-item since flow vs block may differ
        assert len(v1) == len(v2)
        for i in range(len(v1)):
            assert v1[i].as_str() == v2[i].as_str()

    def test_empty_mapping(self) -> None:
        v1 = lean4yaml.load("{}")
        dumped = lean4yaml.dump(v1)
        v2 = lean4yaml.load(dumped)
        assert v2.kind == "mapping"
        assert len(v2) == 0

    def test_multiline_scalar(self) -> None:
        yaml = "|\n  line one\n  line two"
        v1 = lean4yaml.load(yaml)
        dumped = lean4yaml.dump(v1)
        v2 = lean4yaml.load(dumped)
        assert v1.as_str() == v2.as_str()
