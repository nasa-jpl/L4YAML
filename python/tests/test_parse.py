"""Tests for parsing YAML via lean4yaml."""
from __future__ import annotations

import pytest

try:
    import lean4yaml
    from lean4yaml.types import YamlValue

    _LIB_AVAILABLE = True
except OSError:
    _LIB_AVAILABLE = False

needs_lib = pytest.mark.skipif(
    not _LIB_AVAILABLE,
    reason="liblean4yaml.so not found",
)


# ── Single-document parsing ──────────────────────────────────────────

@needs_lib
class TestLoadScalar:
    def test_plain_scalar(self) -> None:
        v: YamlValue = lean4yaml.load("hello")
        assert v.kind == "scalar"
        assert v.as_str() == "hello"

    def test_quoted_scalar(self) -> None:
        v = lean4yaml.load('"hello world"')
        assert v.as_str() == "hello world"

    def test_integer_scalar(self) -> None:
        v = lean4yaml.load("42")
        assert v.kind == "scalar"
        assert v.as_str() == "42"


@needs_lib
class TestLoadSequence:
    def test_block_sequence(self) -> None:
        v = lean4yaml.load("- a\n- b\n- c")
        assert v.kind == "sequence"
        assert len(v) == 3
        items = v.as_list()
        assert items[0].as_str() == "a"
        assert items[2].as_str() == "c"

    def test_flow_sequence(self) -> None:
        v = lean4yaml.load("[1, 2, 3]")
        assert v.kind == "sequence"
        assert len(v) == 3

    def test_index(self) -> None:
        v = lean4yaml.load("[x, y, z]")
        assert v[0].as_str() == "x"
        assert v[-1].as_str() == "z"

    def test_index_out_of_range(self) -> None:
        v = lean4yaml.load("[a]")
        with pytest.raises(IndexError):
            v[5]

    def test_iterate(self) -> None:
        v = lean4yaml.load("[a, b]")
        strs = [item.as_str() for item in v]
        assert strs == ["a", "b"]


@needs_lib
class TestLoadMapping:
    def test_block_mapping(self) -> None:
        v = lean4yaml.load("name: alice\nage: '30'")
        assert v.kind == "mapping"
        assert v["name"].as_str() == "alice"
        assert v["age"].as_str() == "30"

    def test_flow_mapping(self) -> None:
        v = lean4yaml.load("{a: 1, b: 2}")
        assert len(v) == 2

    def test_as_dict(self) -> None:
        v = lean4yaml.load("x: 1\ny: 2")
        d = v.as_dict()
        assert set(d.keys()) == {"x", "y"}

    def test_keys(self) -> None:
        v = lean4yaml.load("a: 1\nb: 2\nc: 3")
        assert v.keys() == ["a", "b", "c"]

    def test_contains(self) -> None:
        v = lean4yaml.load("k: v")
        assert "k" in v
        assert "missing" not in v

    def test_missing_key(self) -> None:
        v = lean4yaml.load("k: v")
        with pytest.raises(KeyError):
            v["nonexistent"]


@needs_lib
class TestLoadNested:
    def test_mapping_with_sequence(self) -> None:
        yaml = "items:\n  - one\n  - two"
        v = lean4yaml.load(yaml)
        items = v["items"]
        assert items.kind == "sequence"
        assert items[0].as_str() == "one"

    def test_sequence_of_mappings(self) -> None:
        yaml = "- name: a\n- name: b"
        v = lean4yaml.load(yaml)
        assert v[0]["name"].as_str() == "a"


# ── Multi-document parsing ───────────────────────────────────────────

@needs_lib
class TestLoadAll:
    def test_multi_doc(self) -> None:
        yaml = "---\nfirst\n---\nsecond"
        docs = lean4yaml.load_all(yaml)
        assert len(docs) >= 2
        assert docs[0].root.as_str() == "first"
        assert docs[1].root.as_str() == "second"

    def test_single_doc_via_load_all(self) -> None:
        docs = lean4yaml.load_all("hello")
        assert len(docs) >= 1


# ── Error handling ───────────────────────────────────────────────────

@needs_lib
class TestParseErrors:
    def test_invalid_yaml(self) -> None:
        with pytest.raises(lean4yaml.ParseError):
            lean4yaml.load(":\n  :\n    :")

    def test_bad_preset_name(self) -> None:
        with pytest.raises(ValueError, match="Unknown limits preset"):
            lean4yaml.load("x", limits="bogus")


# ── Tag / Anchor ─────────────────────────────────────────────────────

@needs_lib
class TestTagAnchor:
    def test_tag(self) -> None:
        v = lean4yaml.load("!!str hello")
        tag = v.tag
        # Tag may be the full or short form
        assert tag is None or "str" in tag

    def test_no_anchor(self) -> None:
        v = lean4yaml.load("hello")
        assert v.anchor is None


# ── Type errors ──────────────────────────────────────────────────────

@needs_lib
class TestTypeErrors:
    def test_as_str_on_sequence(self) -> None:
        v = lean4yaml.load("[1, 2]")
        with pytest.raises(lean4yaml.Lean4YamlError):
            v.as_str()

    def test_as_list_on_scalar(self) -> None:
        v = lean4yaml.load("hello")
        with pytest.raises(lean4yaml.Lean4YamlError):
            v.as_list()

    def test_as_dict_on_scalar(self) -> None:
        v = lean4yaml.load("hello")
        with pytest.raises(lean4yaml.Lean4YamlError):
            v.as_dict()

    def test_int_index_on_mapping(self) -> None:
        v = lean4yaml.load("k: v")
        with pytest.raises(lean4yaml.Lean4YamlError):
            v[0]

    def test_str_key_on_sequence(self) -> None:
        v = lean4yaml.load("[a, b]")
        with pytest.raises(lean4yaml.Lean4YamlError):
            v["key"]

    def test_len_on_scalar(self) -> None:
        v = lean4yaml.load("hello")
        with pytest.raises(lean4yaml.Lean4YamlError):
            len(v)
