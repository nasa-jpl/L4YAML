"""Exact YAML 1.2.2 Core Schema numeric boundaries for Python consumers.

These tests compare types, not just values: 12.0 == 12 is insufficient.
The native mapping tests also catch Python-dict key conflation.
"""

from __future__ import annotations

import os
import sys
import unittest

from l4yaml.compat import _coerce_scalar, safe_load
from l4yaml.exceptions import LimitError


class TestCoreNumericResolver(unittest.TestCase):
    def test_decimal_integer_limit_does_not_silently_change_type(self) -> None:
        limit = getattr(sys, "get_int_max_str_digits", lambda: 0)()
        if not 0 < limit <= 10_000:
            self.skipTest("No bounded Python decimal integer digit limit")
        spelling = "1" * (limit + 1)
        with self.assertRaises(LimitError):
            _coerce_scalar(spelling)

    def test_valid_leading_zero_decimals_remain_integers(self) -> None:
        for spelling, expected in (("012", 12), ("007", 7), ("+012", 12)):
            with self.subTest(spelling=spelling):
                actual = _coerce_scalar(spelling)
                self.assertIs(type(actual), int)
                self.assertEqual(actual, expected)

    def test_invalid_numeric_spelling_remains_string(self) -> None:
        for spelling in (
            "1_000", "0_1", "0x_F", "1_0.2", "+0xF", "-0o7",
            "0x", "0o", "0Xf", "0O7",
        ):
            with self.subTest(spelling=spelling):
                actual = _coerce_scalar(spelling)
                self.assertIs(type(actual), str)
                self.assertEqual(actual, spelling)

    def test_valid_yaml_12_core_numerics(self) -> None:
        cases = (
            ("42", 42, int), ("-7", -7, int), ("0o7", 7, int),
            ("0x3A", 58, int), (".5", 0.5, float), ("1.", 1.0, float),
            ("1e3", 1000.0, float), ("-1.5", -1.5, float),
            ("+12e03", 12000.0, float),
        )
        for spelling, expected, kind in cases:
            with self.subTest(spelling=spelling):
                actual = _coerce_scalar(spelling)
                self.assertIs(type(actual), kind)
                self.assertEqual(actual, expected)


@unittest.skipUnless(os.environ.get("L4YAML_LIB"), "native C library not configured")
class TestCoreNumericNative(unittest.TestCase):
    def test_numeric_types_through_real_parser(self) -> None:
        cases = (("012", 12, int), ("007", 7, int),
                 ("1_000", "1_000", str), ("0x_F", "0x_F", str))
        for source, expected, kind in cases:
            with self.subTest(source=source):
                actual = safe_load(source)
                self.assertIs(type(actual), kind)
                self.assertEqual(actual, expected)

    def test_mapping_keys_do_not_collapse(self) -> None:
        cases = (
            ("1_000: first\n1000: second\n", {"1_000": "first", 1000: "second"}),
            ("0_1: first\n1: second\n", {"0_1": "first", 1: "second"}),
            ("0x_F: first\n15: second\n", {"0x_F": "first", 15: "second"}),
        )
        for source, expected in cases:
            with self.subTest(source=source):
                actual = safe_load(source)
                self.assertEqual(len(actual), 2)
                self.assertEqual(actual, expected)


if __name__ == "__main__":
    unittest.main()
