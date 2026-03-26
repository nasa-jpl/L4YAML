"""Tests for parser limit presets and custom limits."""
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
class TestPresets:
    def test_default_preset(self) -> None:
        v = lean4yaml.load("hello", limits="default")
        assert v.as_str() == "hello"

    def test_strict_preset(self) -> None:
        v = lean4yaml.load("hello", limits="strict")
        assert v.as_str() == "hello"

    def test_permissive_preset(self) -> None:
        v = lean4yaml.load("hello", limits="permissive")
        assert v.as_str() == "hello"

    def test_unlimited_preset(self) -> None:
        v = lean4yaml.load("hello", limits="unlimited")
        assert v.as_str() == "hello"

    def test_safe_tags_preset(self) -> None:
        v = lean4yaml.load("hello", limits="safe_tags")
        assert v.as_str() == "hello"


@needs_lib
class TestStrictLimits:
    def test_deeply_nested_rejected(self) -> None:
        """Strict preset should reject deeply nested structures."""
        # Build a deeply nested mapping (64+ levels)
        yaml = ""
        for i in range(70):
            yaml += "  " * i + f"k{i}:\n"
        yaml += "  " * 70 + "leaf"
        with pytest.raises((lean4yaml.LimitError, lean4yaml.ParseError)):
            lean4yaml.load(yaml, limits="strict")


@needs_lib
class TestConfigYaml:
    def test_parse_limits_yaml(self) -> None:
        """Parse a YAML config string into ParserLimits."""
        cfg = """\
structural:
  maxDepth: 10
  maxAliasExpansion: 50
"""
        handle = lean4yaml.parse_limits_yaml(cfg)
        assert handle != 0

    def test_invalid_config(self) -> None:
        with pytest.raises(lean4yaml.ConfigError):
            lean4yaml.parse_limits_yaml("not: valid: limits: yaml: {{{{")
