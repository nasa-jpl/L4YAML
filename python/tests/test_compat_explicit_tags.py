"""Explicit YAML Core Schema tags survive the PyYAML-compatible adapter.

The pure converter tests run without Lean/C.  Native end-to-end tests are
activated when the caller supplies the pinned L4YAML_LIB shared library.
"""

from __future__ import annotations

import os
from types import SimpleNamespace
import unittest

from l4yaml.compat import _resolve_scalar, safe_load


class TestExplicitScalarTagConverter(unittest.TestCase):
    def test_declared_string_overrides_plain_boolean(self) -> None:
        node = SimpleNamespace(tag="!!str", _style_id=0)
        result = _resolve_scalar(node, "false")
        self.assertIs(type(result), str)
        self.assertEqual(result, "false")

    def test_declared_integer_overrides_quoted_style(self) -> None:
        node = SimpleNamespace(tag="!!int", _style_id=2)
        result = _resolve_scalar(node, "42")
        self.assertIs(type(result), int)
        self.assertEqual(result, 42)

    def test_declared_boolean_overrides_quoted_style(self) -> None:
        node = SimpleNamespace(tag="tag:yaml.org,2002:bool", _style_id=2)
        result = _resolve_scalar(node, "false")
        self.assertIs(type(result), bool)
        self.assertIs(result, False)

    def test_explicit_full_string_uri(self) -> None:
        node = SimpleNamespace(tag="tag:yaml.org,2002:str", _style_id=0)
        result = _resolve_scalar(node, "null")
        self.assertIs(type(result), str)
        self.assertEqual(result, "null")

    def test_non_core_tag_is_not_implicitly_coerced(self) -> None:
        node = SimpleNamespace(tag="!custom", _style_id=0)
        result = _resolve_scalar(node, "false")
        self.assertIs(type(result), str)
        self.assertEqual(result, "false")

    def test_untagged_plain_and_quoted_controls(self) -> None:
        self.assertIs(_resolve_scalar(SimpleNamespace(tag=None, _style_id=0), "false"), False)
        self.assertEqual(_resolve_scalar(SimpleNamespace(tag=None, _style_id=2), "false"), "false")


@unittest.skipUnless(os.environ.get("L4YAML_LIB"), "native C library not configured")
class TestExplicitScalarTagNative(unittest.TestCase):
    def test_top_level_string_tag(self) -> None:
        self.assertEqual(safe_load("!!str false"), "false")

    def test_top_level_integer_tag(self) -> None:
        result = safe_load('!!int "42"')
        self.assertIs(type(result), int)
        self.assertEqual(result, 42)

    def test_nested_value_tags(self) -> None:
        actual = safe_load('enabled: !!str false\ncount: !!int "42"\n')
        self.assertEqual(actual, {"enabled": "false", "count": 42})
        self.assertIs(type(actual["enabled"]), str)
        self.assertIs(type(actual["count"]), int)


if __name__ == "__main__":
    unittest.main()
