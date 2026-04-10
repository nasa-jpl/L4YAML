"""Tests for the PyYAML-compatible API layer."""
from __future__ import annotations

import io
import math
from pathlib import Path

import pytest

try:
    from l4yaml.compat import (
        safe_dump,
        safe_dump_all,
        safe_load,
        safe_load_all,
        to_python,
    )
    import l4yaml

    _LIB_AVAILABLE = True
except OSError:
    _LIB_AVAILABLE = False

needs_lib = pytest.mark.skipif(
    not _LIB_AVAILABLE,
    reason="libl4yaml.so not found",
)


# ── safe_load: scalar coercion ───────────────────────────────────────


@needs_lib
class TestSafeLoadScalar:
    def test_string(self) -> None:
        assert safe_load("hello") == "hello"

    def test_integer(self) -> None:
        assert safe_load("42") == 42

    def test_negative_integer(self) -> None:
        assert safe_load("-7") == -7

    def test_hex_integer(self) -> None:
        assert safe_load("0xFF") == 255

    def test_octal_integer(self) -> None:
        assert safe_load("0o17") == 15

    def test_float(self) -> None:
        assert safe_load("3.14") == pytest.approx(3.14)

    def test_negative_float(self) -> None:
        assert safe_load("-2.5") == pytest.approx(-2.5)

    def test_scientific_float(self) -> None:
        assert safe_load("1.5e10") == pytest.approx(1.5e10)

    def test_true(self) -> None:
        assert safe_load("true") is True

    def test_True(self) -> None:
        assert safe_load("True") is True

    def test_false(self) -> None:
        assert safe_load("false") is False

    def test_null(self) -> None:
        assert safe_load("null") is None

    def test_tilde_null(self) -> None:
        assert safe_load("~") is None

    def test_inf(self) -> None:
        assert safe_load(".inf") == math.inf

    def test_neg_inf(self) -> None:
        assert safe_load("-.inf") == -math.inf

    def test_nan(self) -> None:
        result = safe_load(".nan")
        assert math.isnan(result)

    def test_quoted_stays_string(self) -> None:
        assert safe_load('"42"') == "42"

    def test_quoted_true_stays_string(self) -> None:
        assert safe_load('"true"') == "true"


# ── safe_load: structures ────────────────────────────────────────────


@needs_lib
class TestSafeLoadStructures:
    def test_mapping(self) -> None:
        result = safe_load("name: alice\nage: '30'")
        assert isinstance(result, dict)
        assert result["name"] == "alice"
        assert result["age"] == "30"

    def test_mapping_with_int_values(self) -> None:
        result = safe_load("x: 1\ny: 2")
        assert result == {"x": 1, "y": 2}

    def test_sequence(self) -> None:
        result = safe_load("- a\n- b\n- c")
        assert isinstance(result, list)
        assert result == ["a", "b", "c"]

    def test_flow_sequence(self) -> None:
        result = safe_load("[1, 2, 3]")
        assert result == [1, 2, 3]

    def test_nested(self) -> None:
        yaml = "items:\n  - one\n  - two"
        result = safe_load(yaml)
        assert result == {"items": ["one", "two"]}

    def test_sequence_of_mappings(self) -> None:
        yaml = "- name: a\n  val: 1\n- name: b\n  val: 2"
        result = safe_load(yaml)
        assert len(result) == 2
        assert result[0]["name"] == "a"
        assert result[1]["val"] == 2

    def test_empty_mapping(self) -> None:
        result = safe_load("{}")
        assert result == {}

    def test_empty_sequence(self) -> None:
        result = safe_load("[]")
        assert result == []

    def test_deeply_nested(self) -> None:
        yaml = "a:\n  b:\n    c: deep"
        result = safe_load(yaml)
        assert result["a"]["b"]["c"] == "deep"


# ── safe_load: input types ───────────────────────────────────────────


@needs_lib
class TestSafeLoadInputTypes:
    def test_bytes_input(self) -> None:
        result = safe_load(b"key: value")
        assert result == {"key": "value"}

    def test_path_input(self, tmp_path: Path) -> None:
        yaml_file = tmp_path / "test.yaml"
        yaml_file.write_text("x: 42")
        result = safe_load(yaml_file)
        assert result == {"x": 42}

    def test_file_like_input(self) -> None:
        f = io.StringIO("key: value")
        result = safe_load(f)
        assert result == {"key": "value"}

    def test_bytes_file_like(self) -> None:
        f = io.BytesIO(b"key: value")
        result = safe_load(f)
        assert result == {"key": "value"}

    def test_bad_input_type(self) -> None:
        with pytest.raises(TypeError, match="Expected str"):
            safe_load(12345)


# ── safe_load: limits as YAML config ─────────────────────────────────


@needs_lib
class TestSafeLoadLimits:
    def test_default_limits(self) -> None:
        result = safe_load("hello")
        assert result == "hello"

    def test_limits_yaml_string(self) -> None:
        cfg = "structural:\n  maxDepth: 100"
        result = safe_load("hello", limits=cfg)
        assert result == "hello"

    def test_limits_from_file(self, tmp_path: Path) -> None:
        cfg_file = tmp_path / "limits.yaml"
        cfg_file.write_text("structural:\n  maxDepth: 100")
        result = safe_load("hello", limits=cfg_file)
        assert result == "hello"


# ── safe_load_all ─────────────────────────────────────────────────────


@needs_lib
class TestSafeLoadAll:
    def test_multi_doc(self) -> None:
        yaml = "---\nfirst\n---\nsecond"
        results = list(safe_load_all(yaml))
        assert len(results) >= 2
        assert results[0] == "first"
        assert results[1] == "second"

    def test_single_doc(self) -> None:
        results = list(safe_load_all("hello"))
        assert len(results) >= 1
        assert results[0] == "hello"

    def test_returns_iterator(self) -> None:
        result = safe_load_all("hello")
        # Should be an iterator, not a list
        assert hasattr(result, "__next__")

    def test_multi_doc_with_limits(self) -> None:
        yaml = "---\nfirst\n---\nsecond"
        cfg = "structural:\n  maxDepth: 100"
        results = list(safe_load_all(yaml, limits=cfg))
        assert len(results) >= 2


# ── safe_dump ─────────────────────────────────────────────────────────


@needs_lib
class TestSafeDump:
    def test_dump_string(self) -> None:
        result = safe_dump("hello")
        assert result is not None
        assert "hello" in result

    def test_dump_integer(self) -> None:
        result = safe_dump(42)
        assert result is not None
        assert "42" in result

    def test_dump_mapping(self) -> None:
        result = safe_dump({"key": "value"})
        assert result is not None
        assert "key" in result

    def test_dump_sequence(self) -> None:
        result = safe_dump([1, 2, 3])
        assert result is not None

    def test_dump_nested(self) -> None:
        data = {"items": ["a", "b"], "count": 2}
        result = safe_dump(data)
        assert result is not None
        assert "items" in result

    def test_dump_none(self) -> None:
        result = safe_dump(None)
        assert result is not None
        assert "null" in result

    def test_dump_bool(self) -> None:
        result = safe_dump(True)
        assert result is not None
        assert "true" in result

    def test_dump_to_stream(self) -> None:
        f = io.StringIO()
        result = safe_dump({"k": "v"}, stream=f)
        assert result is None
        assert "k" in f.getvalue()

    def test_dump_with_config(self) -> None:
        data = {"key": "value"}
        cfg = "defaultStyle: block"
        result = safe_dump(data, config=cfg)
        assert result is not None
        assert "key" in result

    def test_dump_unsupported_type(self) -> None:
        with pytest.raises(TypeError, match="Cannot serialize"):
            safe_dump(object())


# ── safe_dump_all ─────────────────────────────────────────────────────


@needs_lib
class TestSafeDumpAll:
    def test_dump_multiple(self) -> None:
        result = safe_dump_all(["first", "second"])
        assert result is not None
        assert "first" in result
        assert "second" in result

    def test_dump_all_to_stream(self) -> None:
        f = io.StringIO()
        result = safe_dump_all([{"a": 1}, {"b": 2}], stream=f)
        assert result is None
        content = f.getvalue()
        assert "a" in content
        assert "b" in content


# ── to_python on YamlValue ────────────────────────────────────────────


@needs_lib
class TestToPython:
    def test_scalar_to_python(self) -> None:
        v = l4yaml.load("42")
        assert v.to_python() == 42

    def test_bool_to_python(self) -> None:
        v = l4yaml.load("true")
        assert v.to_python() is True

    def test_null_to_python(self) -> None:
        v = l4yaml.load("null")
        assert v.to_python() is None

    def test_mapping_to_python(self) -> None:
        v = l4yaml.load("x: 1\ny: 2")
        result = v.to_python()
        assert result == {"x": 1, "y": 2}

    def test_sequence_to_python(self) -> None:
        v = l4yaml.load("[a, b, c]")
        result = v.to_python()
        assert result == ["a", "b", "c"]

    def test_nested_to_python(self) -> None:
        yaml = "items:\n  - name: a\n    val: 1"
        v = l4yaml.load(yaml)
        result = v.to_python()
        assert result == {"items": [{"name": "a", "val": 1}]}


# ── Round-trip: safe_load → safe_dump → safe_load ─────────────────────


@needs_lib
class TestCompatRoundTrip:
    def _roundtrip(self, data: object) -> None:
        yaml_str = safe_dump(data)
        assert yaml_str is not None
        result = safe_load(yaml_str)
        assert result == data

    def test_string(self) -> None:
        self._roundtrip("hello")

    def test_integer(self) -> None:
        self._roundtrip(42)

    def test_mapping(self) -> None:
        self._roundtrip({"a": 1, "b": 2})

    def test_sequence(self) -> None:
        self._roundtrip([1, 2, 3])

    def test_nested(self) -> None:
        self._roundtrip({"items": ["x", "y"], "count": 2})

    def test_bool(self) -> None:
        self._roundtrip(True)

    def test_none(self) -> None:
        self._roundtrip(None)
