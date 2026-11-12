"""Tests for parsing YAML via l4yaml."""
from __future__ import annotations

import ctypes
import subprocess
import sys

import pytest

try:
    import l4yaml
    from l4yaml.types import YamlValue

    _LIB_AVAILABLE = True
except OSError:
    _LIB_AVAILABLE = False

needs_lib = pytest.mark.skipif(
    not _LIB_AVAILABLE,
    reason="libl4yaml.so not found",
)


# ── Single-document parsing ──────────────────────────────────────────

@needs_lib
class TestLoadScalar:
    def test_plain_scalar(self) -> None:
        v: YamlValue = l4yaml.load("hello")
        assert v.kind == "scalar"
        assert v.as_str() == "hello"

    def test_quoted_scalar(self) -> None:
        v = l4yaml.load('"hello world"')
        assert v.as_str() == "hello world"

    def test_integer_scalar(self) -> None:
        v = l4yaml.load("42")
        assert v.kind == "scalar"
        assert v.as_str() == "42"


@needs_lib
class TestLoadSequence:
    def test_block_sequence(self) -> None:
        v = l4yaml.load("- a\n- b\n- c")
        assert v.kind == "sequence"
        assert len(v) == 3
        items = v.as_list()
        assert items[0].as_str() == "a"
        assert items[2].as_str() == "c"

    def test_flow_sequence(self) -> None:
        v = l4yaml.load("[1, 2, 3]")
        assert v.kind == "sequence"
        assert len(v) == 3

    def test_index(self) -> None:
        v = l4yaml.load("[x, y, z]")
        assert v[0].as_str() == "x"
        assert v[-1].as_str() == "z"

    def test_index_out_of_range(self) -> None:
        v = l4yaml.load("[a]")
        with pytest.raises(IndexError):
            v[5]

    def test_iterate(self) -> None:
        v = l4yaml.load("[a, b]")
        strs = [item.as_str() for item in v]
        assert strs == ["a", "b"]


@needs_lib
class TestLoadMapping:
    def test_block_mapping(self) -> None:
        v = l4yaml.load("name: alice\nage: '30'")
        assert v.kind == "mapping"
        assert v["name"].as_str() == "alice"
        assert v["age"].as_str() == "30"

    def test_flow_mapping(self) -> None:
        v = l4yaml.load("{a: 1, b: 2}")
        assert len(v) == 2

    def test_as_dict(self) -> None:
        v = l4yaml.load("x: 1\ny: 2")
        d = v.as_dict()
        assert set(d.keys()) == {"x", "y"}

    def test_keys(self) -> None:
        v = l4yaml.load("a: 1\nb: 2\nc: 3")
        assert v.keys() == ["a", "b", "c"]

    def test_contains(self) -> None:
        v = l4yaml.load("k: v")
        assert "k" in v
        assert "missing" not in v

    def test_missing_key(self) -> None:
        v = l4yaml.load("k: v")
        with pytest.raises(KeyError):
            v["nonexistent"]

    @pytest.mark.parametrize("key", ["\x00a", "a\x00b", "a\x00"])
    def test_escaped_nul_keys_preserve_identity(self, key: str) -> None:
        # YAML's quoted \0 escape represents a character inside the key,
        # not a C terminator.  Include the truncated prefix as a decoy.
        prefix = key.split("\x00", 1)[0]
        escaped_key = key.replace("\x00", r"\0")
        yaml = f'"{prefix}": wrong\n"{escaped_key}": correct'
        v = l4yaml.load(yaml)
        assert v.keys() == [prefix, key]
        assert [k for k, _ in v.items()] == [prefix, key]
        assert set(v.as_dict()) == {prefix, key}
        assert v[key].as_str() == "correct"
        assert v[prefix].as_str() == "wrong"
        assert key in v
        assert dict(v)[key].as_str() == "correct"

    def test_escaped_nul_scalar_preserves_suffix(self) -> None:
        assert l4yaml.load(r'"before\0after"').as_str() == "before\x00after"

    def test_escaped_nul_unicode_key_roundtrip(self) -> None:
        v = l4yaml.load('"é": wrong\n"é\\0💫": correct')
        assert v["é\x00💫"].as_str() == "correct"
        assert v.keys() == ["é", "é\x00💫"]

    def test_length_aware_c_abi(self) -> None:
        """Exercise both new C entry points, not only Python's wrappers."""
        v = l4yaml.load('"a": wrong\n"a\\0b": correct')
        lib = v._lib
        data = b"a\x00b"
        handle = lib.l4yaml_value_lookup_bytes(v._handle, data, len(data))
        assert handle
        try:
            length = ctypes.c_size_t()
            ptr = lib.l4yaml_value_string_bytes(handle, ctypes.byref(length))
            assert ctypes.string_at(ptr, length.value) == b"correct"
        finally:
            lib.l4yaml_free(handle)

        scalar = l4yaml.load(r'"before\0after"')
        length = ctypes.c_size_t()
        ptr = lib.l4yaml_value_string_bytes(
            scalar._handle, ctypes.byref(length)
        )
        assert ctypes.string_at(ptr, length.value) == b"before\x00after"

        # Existing C ABI calls retain their legacy NUL-terminated behavior.
        assert lib.l4yaml_value_string(scalar._handle) == b"before"
        old_handle = lib.l4yaml_value_lookup(v._handle, b"a\x00b")
        assert old_handle
        try:
            assert lib.l4yaml_value_string(old_handle) == b"wrong"
        finally:
            lib.l4yaml_free(old_handle)

    def test_length_aware_c_abi_null_length(self) -> None:
        # A subprocess turns a native crash into a test failure instead of
        # terminating the entire suite. NULL means the caller needs no length.
        result = subprocess.run(
            [sys.executable, "-c", r'''
import ctypes
import l4yaml

scalar = l4yaml.load(r'"before\0after"')
ptr = scalar._lib.l4yaml_value_string_bytes(scalar._handle, None)
assert ctypes.string_at(ptr, 12) == b"before\x00after"
mapping = l4yaml.load("a: b")
ptr = mapping._lib.l4yaml_value_string_bytes(mapping._handle, None)
assert ctypes.string_at(ptr) == b""
'''],
            capture_output=True,
            text=True,
        )
        assert result.returncode == 0, result.stderr


@needs_lib
class TestLoadNested:
    def test_mapping_with_sequence(self) -> None:
        yaml = "items:\n  - one\n  - two"
        v = l4yaml.load(yaml)
        items = v["items"]
        assert items.kind == "sequence"
        assert items[0].as_str() == "one"

    def test_sequence_of_mappings(self) -> None:
        yaml = "- name: a\n- name: b"
        v = l4yaml.load(yaml)
        assert v[0]["name"].as_str() == "a"


# ── Multi-document parsing ───────────────────────────────────────────

@needs_lib
class TestLoadAll:
    def test_multi_doc(self) -> None:
        yaml = "---\nfirst\n---\nsecond"
        docs = l4yaml.load_all(yaml)
        assert len(docs) >= 2
        assert docs[0].root.as_str() == "first"
        assert docs[1].root.as_str() == "second"

    def test_single_doc_via_load_all(self) -> None:
        docs = l4yaml.load_all("hello")
        assert len(docs) >= 1


# ── Error handling ───────────────────────────────────────────────────

@needs_lib
class TestParseErrors:
    def test_invalid_yaml(self) -> None:
        # (":\n  :\n    :" is VALID — nested mappings with empty keys —
        # so use bare content after a mapping, which cannot parse.)
        with pytest.raises(l4yaml.ParseError):
            l4yaml.load("a: b\n- c")

    def test_bad_preset_name(self) -> None:
        with pytest.raises(ValueError, match="Unknown limits preset"):
            l4yaml.load("x", limits="bogus")


# ── Tag / Anchor ─────────────────────────────────────────────────────

@needs_lib
class TestTagAnchor:
    def test_tag(self) -> None:
        v = l4yaml.load("!!str hello")
        tag = v.tag
        # Tag may be the full or short form
        assert tag is None or "str" in tag

    def test_no_anchor(self) -> None:
        v = l4yaml.load("hello")
        assert v.anchor is None


# ── Scalar style ─────────────────────────────────────────────────────

@needs_lib
class TestScalarStyle:
    def test_plain(self) -> None:
        assert l4yaml.load("42").style == "plain"

    def test_single_quoted(self) -> None:
        assert l4yaml.load("'42'").style == "single_quoted"

    def test_double_quoted(self) -> None:
        assert l4yaml.load('"42"').style == "double_quoted"

    def test_literal(self) -> None:
        v = l4yaml.load("x: |\n  body")
        assert v.as_dict()["x"].style == "literal"

    def test_folded(self) -> None:
        v = l4yaml.load("x: >\n  body")
        assert v.as_dict()["x"].style == "folded"

    def test_non_scalar_has_no_style(self) -> None:
        assert l4yaml.load("[1, 2]").style is None


# ── Type errors ──────────────────────────────────────────────────────

@needs_lib
class TestTypeErrors:
    def test_as_str_on_sequence(self) -> None:
        v = l4yaml.load("[1, 2]")
        with pytest.raises(l4yaml.L4YAMLError):
            v.as_str()

    def test_as_list_on_scalar(self) -> None:
        v = l4yaml.load("hello")
        with pytest.raises(l4yaml.L4YAMLError):
            v.as_list()

    def test_as_dict_on_scalar(self) -> None:
        v = l4yaml.load("hello")
        with pytest.raises(l4yaml.L4YAMLError):
            v.as_dict()

    def test_int_index_on_mapping(self) -> None:
        v = l4yaml.load("k: v")
        with pytest.raises(l4yaml.L4YAMLError):
            v[0]

    def test_str_key_on_sequence(self) -> None:
        v = l4yaml.load("[a, b]")
        with pytest.raises(l4yaml.L4YAMLError):
            v["key"]

    def test_len_on_scalar(self) -> None:
        v = l4yaml.load("hello")
        with pytest.raises(l4yaml.L4YAMLError):
            len(v)


# ── Equality / hashing / iteration ───────────────────────────────────

@needs_lib
class TestValueIdentity:
    def test_eq_and_hash_are_structural(self) -> None:
        a: YamlValue = l4yaml.load("{k: [1, 2], j: x}")
        b: YamlValue = l4yaml.load("{k: [1, 2], j: x}")
        c: YamlValue = l4yaml.load("{k: [1, 3], j: x}")
        assert a == b and hash(a) == hash(b)
        assert a != c
        assert len({a, b, c}) == 2

    def test_repr_is_cached_and_stable(self) -> None:
        v: YamlValue = l4yaml.load("a: [1, 2]")
        first: str = repr(v)
        assert repr(v) is first
        assert repr(l4yaml.load("a: [1, 2]")) == first

    def test_mapping_iter_is_lazy(self) -> None:
        v: YamlValue = l4yaml.load("a: 1\nb: 2\nc: 3")
        it = iter(v)
        k, val = next(it)
        assert (k, val.as_str()) == ("a", "1")
        assert [k for k, _ in it] == ["b", "c"]

    def test_sequence_iter_matches_as_list(self) -> None:
        v: YamlValue = l4yaml.load("[x, y, z]")
        assert [i.as_str() for i in v] == [i.as_str() for i in v.as_list()]
