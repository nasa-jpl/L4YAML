"""Python FFI integration tests for libl4yaml.

These tests exercise the full pipeline:
  Lean 4 verified parser → C shim → Python ctypes bindings

They are designed for CI integration alongside the Lean test suites
in this directory.  When the shared library is unavailable (e.g. on a
build node without libleanshared.so), all tests are gracefully skipped.

Run with:
    cd <project-root>
    python3 -m pytest Tests/test_python_ffi.py -v
"""
from __future__ import annotations

import pytest

# ── Library availability gate ────────────────────────────────────────

try:
    import l4yaml
    from l4yaml.types import YamlValue, YamlDocument

    _LIB_AVAILABLE = True
except (OSError, ImportError):
    l4yaml = None  # type: ignore[assignment]
    YamlValue = None  # type: ignore[assignment,misc]
    YamlDocument = None  # type: ignore[assignment,misc]
    _LIB_AVAILABLE = False

needs_lib = pytest.mark.skipif(
    not _LIB_AVAILABLE,
    reason="libl4yaml.so or l4yaml package not available",
)


# ═══════════════════════════════════════════════════════════════════════
#  1. Scalar Parsing
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestScalarParsing:
    """Verify that plain, quoted, and special scalars parse correctly."""

    def test_plain_scalar(self) -> None:
        v = l4yaml.load("hello")
        assert v.kind == "scalar"
        assert v.as_str() == "hello"

    def test_double_quoted(self) -> None:
        v = l4yaml.load('"hello world"')
        assert v.as_str() == "hello world"

    def test_single_quoted(self) -> None:
        v = l4yaml.load("'hello'")
        assert v.as_str() == "hello"

    def test_integer_as_string(self) -> None:
        v = l4yaml.load("42")
        assert v.kind == "scalar"
        assert v.as_str() == "42"

    def test_boolean_as_string(self) -> None:
        v = l4yaml.load("true")
        assert v.kind == "scalar"
        assert v.as_str() == "true"

    def test_null_as_string(self) -> None:
        v = l4yaml.load("null")
        assert v.kind == "scalar"

    def test_empty_string(self) -> None:
        v = l4yaml.load("''")
        assert v.as_str() == ""

    def test_multiline_literal(self) -> None:
        v = l4yaml.load("|\n  line one\n  line two\n")
        content = v.as_str()
        assert "line one" in content
        assert "line two" in content

    def test_multiline_folded(self) -> None:
        v = l4yaml.load(">\n  folded\n  text\n")
        content = v.as_str()
        assert "folded" in content

    def test_unicode_scalar(self) -> None:
        v = l4yaml.load('"caf\\u00e9"')
        assert v.as_str() == "café"


# ═══════════════════════════════════════════════════════════════════════
#  2. Sequence Parsing
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestSequenceParsing:
    """Verify block and flow sequence parsing and navigation."""

    def test_block_sequence(self) -> None:
        v = l4yaml.load("- a\n- b\n- c")
        assert v.kind == "sequence"
        assert len(v) == 3

    def test_flow_sequence(self) -> None:
        v = l4yaml.load("[1, 2, 3]")
        assert v.kind == "sequence"
        assert len(v) == 3

    def test_as_list(self) -> None:
        v = l4yaml.load("[x, y, z]")
        items = v.as_list()
        assert len(items) == 3
        assert items[0].as_str() == "x"
        assert items[2].as_str() == "z"

    def test_index_access(self) -> None:
        v = l4yaml.load("[a, b, c]")
        assert v[0].as_str() == "a"
        assert v[1].as_str() == "b"
        assert v[2].as_str() == "c"

    def test_negative_index(self) -> None:
        v = l4yaml.load("[x, y, z]")
        assert v[-1].as_str() == "z"
        assert v[-3].as_str() == "x"

    def test_index_out_of_range(self) -> None:
        v = l4yaml.load("[a]")
        with pytest.raises(IndexError):
            v[5]

    def test_iteration(self) -> None:
        v = l4yaml.load("[a, b, c]")
        strs = [item.as_str() for item in v]
        assert strs == ["a", "b", "c"]

    def test_empty_sequence(self) -> None:
        v = l4yaml.load("[]")
        assert v.kind == "sequence"
        assert len(v) == 0

    def test_nested_sequences(self) -> None:
        v = l4yaml.load("[[1, 2], [3, 4]]")
        assert len(v) == 2
        assert v[0][0].as_str() == "1"
        assert v[1][1].as_str() == "4"


# ═══════════════════════════════════════════════════════════════════════
#  3. Mapping Parsing
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestMappingParsing:
    """Verify block and flow mapping parsing and key lookup."""

    def test_block_mapping(self) -> None:
        v = l4yaml.load("name: alice\nage: '30'")
        assert v.kind == "mapping"
        assert v["name"].as_str() == "alice"
        assert v["age"].as_str() == "30"

    def test_flow_mapping(self) -> None:
        v = l4yaml.load("{a: 1, b: 2}")
        assert v.kind == "mapping"
        assert len(v) == 2

    def test_as_dict(self) -> None:
        v = l4yaml.load("x: 1\ny: 2")
        d = v.as_dict()
        assert set(d.keys()) == {"x", "y"}
        assert d["x"].as_str() == "1"

    def test_keys(self) -> None:
        v = l4yaml.load("a: 1\nb: 2\nc: 3")
        assert v.keys() == ["a", "b", "c"]

    def test_items(self) -> None:
        v = l4yaml.load("a: 1\nb: 2")
        pairs = v.items()
        assert len(pairs) == 2
        assert pairs[0][0] == "a"
        assert pairs[0][1].as_str() == "1"

    def test_contains(self) -> None:
        v = l4yaml.load("k: v")
        assert "k" in v
        assert "missing" not in v

    def test_missing_key_raises(self) -> None:
        v = l4yaml.load("k: v")
        with pytest.raises(KeyError):
            v["nonexistent"]

    def test_empty_mapping(self) -> None:
        v = l4yaml.load("{}")
        assert v.kind == "mapping"
        assert len(v) == 0


# ═══════════════════════════════════════════════════════════════════════
#  4. Nested Structures
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestNestedStructures:
    """Verify navigation of deeply nested YAML trees."""

    def test_mapping_with_sequence(self) -> None:
        yaml = "items:\n  - one\n  - two"
        v = l4yaml.load(yaml)
        items = v["items"]
        assert items.kind == "sequence"
        assert items[0].as_str() == "one"
        assert items[1].as_str() == "two"

    def test_sequence_of_mappings(self) -> None:
        yaml = "- name: Alice\n- name: Bob"
        v = l4yaml.load(yaml)
        assert v[0]["name"].as_str() == "Alice"
        assert v[1]["name"].as_str() == "Bob"

    def test_deep_nesting(self) -> None:
        yaml = "a:\n  b:\n    c:\n      d: leaf"
        v = l4yaml.load(yaml)
        assert v["a"]["b"]["c"]["d"].as_str() == "leaf"

    def test_mixed_collections(self) -> None:
        yaml = """\
servers:
  - host: alpha
    ports: [80, 443]
  - host: beta
    ports: [8080]
"""
        v = l4yaml.load(yaml)
        s0 = v["servers"][0]
        assert s0["host"].as_str() == "alpha"
        assert s0["ports"][0].as_str() == "80"
        assert s0["ports"][1].as_str() == "443"
        s1 = v["servers"][1]
        assert s1["host"].as_str() == "beta"
        assert s1["ports"][0].as_str() == "8080"


# ═══════════════════════════════════════════════════════════════════════
#  5. Multi-Document Parsing
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestMultiDocument:
    """Verify multi-document YAML stream parsing."""

    def test_two_documents(self) -> None:
        yaml = "---\nfirst\n---\nsecond"
        docs = l4yaml.load_all(yaml)
        assert len(docs) >= 2
        assert docs[0].root.as_str() == "first"
        assert docs[1].root.as_str() == "second"

    def test_single_doc_via_load_all(self) -> None:
        docs = l4yaml.load_all("hello")
        assert len(docs) >= 1
        assert docs[0].root.as_str() == "hello"

    def test_document_type(self) -> None:
        docs = l4yaml.load_all("hello")
        assert isinstance(docs[0], YamlDocument)
        assert isinstance(docs[0].root, YamlValue)


# ═══════════════════════════════════════════════════════════════════════
#  6. Dumping
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestDump:
    """Verify YAML dumping (serialization) of parsed values."""

    def test_dump_scalar(self) -> None:
        v = l4yaml.load("hello")
        out = l4yaml.dump(v)
        assert "hello" in out

    def test_dump_mapping(self) -> None:
        v = l4yaml.load("a: 1\nb: 2")
        out = l4yaml.dump(v)
        assert "a" in out
        assert "b" in out

    def test_dump_sequence(self) -> None:
        v = l4yaml.load("[x, y, z]")
        out = l4yaml.dump(v)
        assert "x" in out
        assert "z" in out

    def test_dump_configured(self) -> None:
        v = l4yaml.load("key: value")
        cfg = "defaultStyle: block"
        out = l4yaml.dump_configured(v, config_yaml=cfg)
        assert "key" in out

    def test_repr_uses_dump(self) -> None:
        v = l4yaml.load("key: value")
        r = repr(v)
        assert "key" in r


# ═══════════════════════════════════════════════════════════════════════
#  7. Round-Trip (parse → dump → re-parse)
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestRoundTrip:
    """Verify that parse-dump-reparse preserves semantic content."""

    def _roundtrip(self, yaml: str) -> None:
        v1 = l4yaml.load(yaml)
        dumped = l4yaml.dump(v1)
        v2 = l4yaml.load(dumped)
        assert v1 == v2

    def test_scalar_roundtrip(self) -> None:
        self._roundtrip("hello")

    def test_mapping_roundtrip(self) -> None:
        self._roundtrip("a: 1\nb: 2")

    def test_sequence_roundtrip(self) -> None:
        self._roundtrip("- x\n- y\n- z")

    def test_nested_roundtrip(self) -> None:
        yaml = "name: test\nitems:\n  - first\n  - second\nmeta:\n  version: '1'"
        self._roundtrip(yaml)

    def test_flow_sequence_values(self) -> None:
        v1 = l4yaml.load("[a, b, c]")
        dumped = l4yaml.dump(v1)
        v2 = l4yaml.load(dumped)
        assert len(v1) == len(v2)
        for i in range(len(v1)):
            assert v1[i].as_str() == v2[i].as_str()

    def test_empty_mapping_roundtrip(self) -> None:
        v1 = l4yaml.load("{}")
        dumped = l4yaml.dump(v1)
        v2 = l4yaml.load(dumped)
        assert v2.kind == "mapping"
        assert len(v2) == 0

    def test_multiline_roundtrip(self) -> None:
        yaml = "|\n  line one\n  line two"
        v1 = l4yaml.load(yaml)
        dumped = l4yaml.dump(v1)
        v2 = l4yaml.load(dumped)
        assert v1.as_str() == v2.as_str()


# ═══════════════════════════════════════════════════════════════════════
#  8. Limit Presets
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestLimitPresets:
    """Verify all limit presets parse without error."""

    @pytest.mark.parametrize("preset", [
        "default", "strict", "permissive", "unlimited", "safe_tags",
    ])
    def test_preset_parses(self, preset: str) -> None:
        v = l4yaml.load("hello", limits=preset)
        assert v.as_str() == "hello"

    def test_bad_preset_name(self) -> None:
        with pytest.raises(ValueError, match="Unknown limits preset"):
            l4yaml.load("x", limits="bogus")

    def test_strict_rejects_deep_nesting(self) -> None:
        """Strict preset should reject excessively deep nesting."""
        yaml = ""
        for i in range(70):
            yaml += "  " * i + f"k{i}:\n"
        yaml += "  " * 70 + "leaf"
        with pytest.raises((l4yaml.LimitError, l4yaml.ParseError)):
            l4yaml.load(yaml, limits="strict")


# ═══════════════════════════════════════════════════════════════════════
#  9. Config YAML (self-hosted config parser)
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestConfigYaml:
    """Verify YAML-based ParserLimits configuration."""

    def test_parse_limits_yaml(self) -> None:
        cfg = "structural:\n  maxDepth: 10\n  maxAliasExpansion: 50\n"
        handle = l4yaml.parse_limits_yaml(cfg)
        assert handle != 0

    def test_invalid_config_yaml(self) -> None:
        with pytest.raises(l4yaml.ConfigError):
            l4yaml.parse_limits_yaml("not: valid: limits: yaml: {{{{")


# ═══════════════════════════════════════════════════════════════════════
# 10. Error Handling
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestErrorHandling:
    """Verify that parse errors raise appropriate exceptions."""

    def test_unclosed_flow_sequence(self) -> None:
        with pytest.raises(l4yaml.ParseError):
            l4yaml.load("[unclosed")

    def test_unclosed_flow_mapping(self) -> None:
        with pytest.raises(l4yaml.ParseError):
            l4yaml.load("{unclosed")

    def test_tab_in_indentation(self) -> None:
        with pytest.raises(l4yaml.ParseError):
            l4yaml.load("key:\n\t value")

    def test_error_message_nonempty(self) -> None:
        with pytest.raises(l4yaml.ParseError) as exc_info:
            l4yaml.load("[unclosed")
        assert len(str(exc_info.value)) > 0


# ═══════════════════════════════════════════════════════════════════════
# 11. Type Safety
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestTypeSafety:
    """Verify that type mismatches raise appropriate errors."""

    def test_as_str_on_sequence(self) -> None:
        v = l4yaml.load("[1, 2]")
        with pytest.raises(l4yaml.L4YAMLError):
            v.as_str()

    def test_as_str_on_mapping(self) -> None:
        v = l4yaml.load("{a: 1}")
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

    def test_string_index_on_sequence(self) -> None:
        v = l4yaml.load("[a, b]")
        with pytest.raises(l4yaml.L4YAMLError):
            v["key"]


# ═══════════════════════════════════════════════════════════════════════
# 12. Tag and Anchor Metadata
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestTagAnchor:
    """Verify tag and anchor metadata access."""

    def test_explicit_tag(self) -> None:
        v = l4yaml.load("!!str hello")
        tag = v.tag
        assert tag is None or "str" in tag

    def test_no_tag(self) -> None:
        v = l4yaml.load("hello")
        # Untagged scalars may or may not carry a tag
        # (implementation-dependent; just check no crash)
        _ = v.tag

    def test_no_anchor(self) -> None:
        v = l4yaml.load("hello")
        assert v.anchor is None


# ═══════════════════════════════════════════════════════════════════════
# 13. YamlValue Equality and Hashing
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestValueEquality:
    """Verify YamlValue equality and hash behavior."""

    def test_equal_scalars(self) -> None:
        v1 = l4yaml.load("hello")
        v2 = l4yaml.load("hello")
        assert v1 == v2

    def test_unequal_scalars(self) -> None:
        v1 = l4yaml.load("hello")
        v2 = l4yaml.load("world")
        assert v1 != v2

    def test_equal_mappings(self) -> None:
        v1 = l4yaml.load("a: 1\nb: 2")
        v2 = l4yaml.load("a: 1\nb: 2")
        assert v1 == v2

    def test_hash_consistency(self) -> None:
        v1 = l4yaml.load("hello")
        v2 = l4yaml.load("hello")
        assert hash(v1) == hash(v2)


# ═══════════════════════════════════════════════════════════════════════
# 14. Memory Safety (handle reuse)
# ═══════════════════════════════════════════════════════════════════════

@needs_lib
class TestMemorySafety:
    """Verify handles survive multiple accesses without corruption."""

    def test_repeated_kind_access(self) -> None:
        v = l4yaml.load("hello")
        for _ in range(10):
            assert v.kind == "scalar"

    def test_repeated_as_str(self) -> None:
        v = l4yaml.load("hello")
        for _ in range(10):
            assert v.as_str() == "hello"

    def test_repeated_len(self) -> None:
        v = l4yaml.load("[a, b, c]")
        for _ in range(10):
            assert len(v) == 3

    def test_repeated_index(self) -> None:
        v = l4yaml.load("[a, b, c]")
        for _ in range(10):
            assert v[1].as_str() == "b"

    def test_repeated_dump(self) -> None:
        v = l4yaml.load("key: value")
        for _ in range(10):
            out = l4yaml.dump(v)
            assert "key" in out

    def test_many_parses(self) -> None:
        """Parse many documents to exercise allocation/GC paths."""
        for i in range(50):
            v = l4yaml.load(f"key{i}: value{i}")
            assert v[f"key{i}"].as_str() == f"value{i}"
