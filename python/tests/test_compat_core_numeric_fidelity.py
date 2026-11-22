"""Exact YAML 1.2.2 Core Schema numeric boundaries for Python consumers.

These tests compare types, not just values: 12.0 == 12 is insufficient.
The native mapping tests also catch Python-dict key conflation.
"""

from __future__ import annotations

import os
import sys
import unittest
from itertools import product
from types import SimpleNamespace

from l4yaml.compat import _coerce_scalar, _resolve_scalar, safe_load
from l4yaml.exceptions import LimitError


def _ascii_digits(s: str, alphabet: str = "0123456789") -> bool:
    return bool(s) and all(c in alphabet for c in s)


def _core_kind(s: str) -> type:
    """Independent character-scanning oracle for the ordered §10.3.2 table.

    https://yaml.org/spec/1.2.2/#1032-tag-resolution
    No production regex, coercion helper, or Python numeric lexer is used.
    This predicts tags/types, not floating-point values or parser acceptance.
    """
    if s in ("", "~", "null", "Null", "NULL"):
        return type(None)
    if s in ("true", "True", "TRUE", "false", "False", "FALSE"):
        return bool
    unsigned = s[1:] if s.startswith(("+", "-")) else s
    if _ascii_digits(unsigned):
        return int
    if s.startswith("0o") and _ascii_digits(s[2:], "01234567"):
        return int
    if s.startswith("0x") and _ascii_digits(s[2:], "0123456789abcdefABCDEF"):
        return int
    if unsigned in (".inf", ".Inf", ".INF") or s in (".nan", ".NaN", ".NAN"):
        return float

    # Consume an optional exponent, then a mantissa with at most one dot.
    parts = unsigned.lower().split("e")
    if len(parts) > 2:
        return str
    if len(parts) == 2:
        exponent = parts[1]
        if exponent.startswith(("+", "-")):
            exponent = exponent[1:]
        if not _ascii_digits(exponent):
            return str
    mantissa = parts[0].split(".")
    if len(mantissa) == 1:
        numeric = _ascii_digits(mantissa[0])
    elif len(mantissa) == 2:
        whole, fraction = mantissa
        numeric = (
            _ascii_digits(whole) and (not fraction or _ascii_digits(fraction))
        ) or (not whole and _ascii_digits(fraction))
    else:
        numeric = False
    return float if numeric else str


class TestCoreNumericResolver(unittest.TestCase):
    def test_bounded_spelling_differential(self) -> None:
        # Freeze the independently reviewed 24-character corpus, including
        # malformed signs, prefixes, exponents, dots and underscores.
        alphabet = "+-01789afFxXoOeE._nNiI:b"
        seen = 0
        for length in range(5):
            for chars in product(alphabet, repeat=length):
                spelling = "".join(chars)
                self.assertIs(type(_coerce_scalar(spelling)), _core_kind(spelling),
                              msg=repr(spelling))
                seen += 1
        self.assertEqual(seen, 346_201)

    def test_full_table_and_non_ascii_boundaries(self) -> None:
        cases = (
            ("", type(None)), ("~", type(None)), ("null", type(None)),
            ("Null", type(None)), ("NULL", type(None)),
            ("true", bool), ("True", bool), ("TRUE", bool),
            ("false", bool), ("False", bool), ("FALSE", bool),
            (".inf", float), ("+.Inf", float), ("-.INF", float),
            (".nan", float), (".NaN", float), (".NAN", float),
            ("+.nan", str), ("-.NaN", str), ("True ", str),
            ("1\u0660", str), ("\uff11", str), ("1\n", str), ("1\r", str),
            (" 1", str), ("1 ", str), ("0b101", str), ("1:30", str),
            ("0xFf", int), ("0o777", int), ("1E+03", float),
            ("0.0e0", float), ("5e-324", float),
        )
        for spelling, expected in cases:
            with self.subTest(spelling=spelling):
                self.assertIs(_core_kind(spelling), expected)
                self.assertIs(type(_coerce_scalar(spelling)), expected)

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

    def test_style_and_explicit_tags_precede_large_integer_conversion(self) -> None:
        # Exercise the converter even when the native library is unavailable.
        spelling = "1" * 10_001
        for tag in (None, "!!str", "tag:yaml.org,2002:str", "!custom"):
            for style in (1, 2, 3, 4):
                with self.subTest(tag=tag, style=style):
                    node = SimpleNamespace(tag=tag, _style_id=style)
                    self.assertEqual(_resolve_scalar(node, spelling), spelling)
        node = SimpleNamespace(tag="!!int", _style_id=2)
        self.assertIs(type(_resolve_scalar(node, "42")), int)

    def test_non_plain_numeric_strings_bypass_coercion(self) -> None:
        # A quoted scalar is a string independently of numeric grammar or
        # the interpreter's currently configured decimal conversion limit.
        for style in (1, 2, 3, 4):
            node = SimpleNamespace(tag=None, _style_id=style)
            self.assertEqual(_resolve_scalar(node, "012"), "012")


@unittest.skipUnless(os.environ.get("L4YAML_LIB"), "native C library not configured")
class TestCoreNumericNative(unittest.TestCase):
    def test_quoted_overlimit_decimal_is_string(self) -> None:
        limit = getattr(sys, "get_int_max_str_digits", lambda: 0)()
        if not 0 < limit <= 10_000:
            self.skipTest("No bounded Python decimal integer digit limit")
        spelling = "1" * (limit + 1)
        sources = (
            '"' + spelling + '"', "'" + spelling + "'",
            "|-\n  " + spelling + "\n", ">-\n  " + spelling + "\n",
            "!!str " + spelling,
            '!!str "' + spelling + '"', "!!str '" + spelling + "'",
            "!!str |-\n  " + spelling + "\n",
            "!!str >-\n  " + spelling + "\n",
            '!<tag:yaml.org,2002:str> "' + spelling + '"',
        )
        for index, source in enumerate(sources):
            with self.subTest(case=index):
                actual = safe_load(source)
                self.assertIs(type(actual), str)
                self.assertEqual(actual, spelling)

    def test_plain_overlimit_decimal_raises_through_real_parser(self) -> None:
        limit = getattr(sys, "get_int_max_str_digits", lambda: 0)()
        if not 0 < limit <= 10_000:
            self.skipTest("No bounded Python decimal integer digit limit")
        for prefix in ("", "+", "-"):
            with self.subTest(prefix=prefix):
                with self.assertRaises(LimitError):
                    safe_load(prefix + "1" * (limit + 1))

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
