#!/usr/bin/env python3
"""tryparse_python — Minimal Python tryparse for yaml-test-suite integration.

Reads a YAML file, parses it via the Python API (lean4yaml.load_all), and
exits 0 on success, 1 on parse error.  Mirrors the Lean tryparse
binary exactly so the suiterunner can swap backends.

Usage: tryparse_python.py <file.yaml> [preset]
  preset: unlimited (default) | default | strict | permissive | safe_tags
"""
import sys
import os

# Add the python package to the path (relative to this script's location)
_script_dir = os.path.dirname(os.path.abspath(__file__))
_python_dir = os.path.join(_script_dir, "..", "python")
if os.path.isdir(_python_dir):
    sys.path.insert(0, _python_dir)

import lean4yaml  # noqa: E402

_VALID_PRESETS = ("unlimited", "default", "strict", "permissive", "safe_tags")


def main() -> int:
    if len(sys.argv) < 2 or len(sys.argv) > 3:
        print("Usage: tryparse_python.py <file.yaml> [preset]", file=sys.stderr)
        return 2

    preset = "unlimited"
    if len(sys.argv) == 3:
        preset = sys.argv[2]
        if preset not in _VALID_PRESETS:
            print(
                f"Unknown preset '{preset}'; choose from: {', '.join(_VALID_PRESETS)}",
                file=sys.stderr,
            )
            return 2

    try:
        with open(sys.argv[1], "r", encoding="utf-8") as f:
            content = f.read()
    except (OSError, IOError) as e:
        print(f"Cannot open {sys.argv[1]}: {e}", file=sys.stderr)
        return 2

    try:
        lean4yaml.load_all(content, limits=preset)
        return 0
    except lean4yaml.Lean4YamlError as e:
        print(str(e), file=sys.stderr)
        return 1


if __name__ == "__main__":
    sys.exit(main())
