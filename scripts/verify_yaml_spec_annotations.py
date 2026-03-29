#!/usr/bin/env python3
"""
Verify consistency between @[yaml_spec] Lean annotations and the
canonical yaml-spec-1.2.yaml production rule file.

Usage:
    python3 scripts/verify_yaml_spec_annotations.py [--spec-url URL | --spec-file PATH]

By default, fetches the spec from:
    https://raw.githubusercontent.com/yaml/yaml-grammar/master/yaml-spec-1.2.yaml

Reports:
    1. NAME MISMATCHES  — rule number exists in spec but annotation has a different name
    2. UNKNOWN RULES    — annotation references a rule number not in the spec (1–211)
    3. COVERAGE          — spec rules not referenced by any annotation
"""

import argparse
import os
import re
import sys
from pathlib import Path
from typing import Optional
from urllib.request import urlopen

DEFAULT_SPEC_URL = (
    "https://raw.githubusercontent.com/yaml/yaml-grammar/master/yaml-spec-1.2.yaml"
)

# ── Parse the yaml-spec-1.2.yaml ──────────────────────────────────────────────
# Format:  :NNN: rule-name
SPEC_RULE_RE = re.compile(r"^:(\d{3}):\s+(\S+)", re.MULTILINE)


def parse_spec(text: str) -> dict[int, str]:
    """Extract rule_number → rule_name from the spec YAML file."""
    rules: dict[int, str] = {}
    for m in SPEC_RULE_RE.finditer(text):
        num = int(m.group(1))
        name = m.group(2)
        rules[num] = name
    return rules


# ── Parse Lean @[yaml_spec …] annotations ────────────────────────────────────
# Matches:  yaml_spec "section" number "name"
#       or: yaml_spec "section"              (section-only, no rule)
LEAN_ANNOT_RE = re.compile(
    r'yaml_spec\s+"([^"]+)"'        # section string
    r'(?:\s+(\d+)\s+"([^"]+)")?'    # optional: rule number + rule name
)


def normalise_lean_name(name: str) -> str:
    """
    Normalise a Lean annotation rule name so it can be compared with the
    spec's ASCII name.

    Known transformations:
      - s-indent(≤n) → s-indent-le       (spec uses short names for these)
      - s-indent(<n) → s-indent-lt
      - Strip parameter lists:  s-indent(n) → s-indent
      - X+Y(n,c) stays as-is after param strip → X+Y
    """
    # The spec file uses bare names without parameters.
    # Lean annotations keep the parameter signatures, e.g. "s-indent(n)".
    # Strip everything from the first '(' onward.
    base = re.sub(r"\(.*\)$", "", name)
    return base


def normalise_spec_name(name: str) -> str:
    """Normalise the spec rule name (already bare, no params)."""
    return name


def names_match(lean_name: str, spec_name: str) -> bool:
    """
    Check whether a Lean annotation name matches a spec rule name,
    accounting for known systematic differences.
    """
    ln = normalise_lean_name(lean_name)
    sn = normalise_spec_name(spec_name)
    if ln == sn:
        return True
    # The YAML 1.2 spec file uses s-indent-lt / s-indent-le for the
    # parameterised variants, whereas the Lean annotations embed the
    # relation into the parameter: s-indent(<n) / s-indent(≤n).
    # After stripping params, both become "s-indent".
    # So s-indent(≤n) → "s-indent" matches spec's "s-indent-le"?  No.
    # Actually, in the spec:
    #   :063: s-indent       (the plain s-indent(n))
    #   :064: s-indent-lt    (s-indent(<n))
    #   :065: s-indent-le    (s-indent(<=n))
    # The Lean annotation for 63 is "s-indent(n)" → after strip → "s-indent" ✓
    # The Lean annotation for 65 is "s-indent(≤n)":
    #   after strip → "s-indent" but spec is "s-indent-le" ✗
    #
    # Handle these known variant forms:
    variant_map = {
        "s-indent(≤n)": "s-indent-le",
        "s-indent(<n)": "s-indent-lt",
    }
    if lean_name in variant_map:
        return variant_map[lean_name] == sn

    # Known divergences between yaml-grammar repo and YAML 1.2.2 spec text.
    # The yaml-grammar file uses slightly different names for some rules.
    # Our Lean annotations follow the actual spec text, which is authoritative.
    spec_to_actual = {
        # yaml-grammar says "seq-spaces" (plural), spec §8.2.3 says "seq-space"
        "seq-spaces": "seq-space",
    }
    if sn in spec_to_actual:
        return ln == spec_to_actual[sn]

    return False


class Annotation:
    """A single @[yaml_spec] annotation occurrence."""

    def __init__(
        self,
        file: str,
        line: int,
        section: str,
        rule_num: Optional[int],
        rule_name: Optional[str],
    ):
        self.file = file
        self.line = line
        self.section = section
        self.rule_num = rule_num
        self.rule_name = rule_name

    def loc(self) -> str:
        return f"{self.file}:{self.line}"


def scan_lean_files(root: Path) -> list[Annotation]:
    """Walk .lean files under root and extract all yaml_spec annotations."""
    annotations: list[Annotation] = []
    for lean_file in sorted(root.rglob("*.lean")):
        rel = lean_file.relative_to(root)
        with open(lean_file, "r", encoding="utf-8") as f:
            for lineno, text in enumerate(f, start=1):
                for m in LEAN_ANNOT_RE.finditer(text):
                    section = m.group(1)
                    rule_num = int(m.group(2)) if m.group(2) else None
                    rule_name = m.group(3) if m.group(3) else None
                    annotations.append(
                        Annotation(str(rel), lineno, section, rule_num, rule_name)
                    )
    return annotations


# ── Cross-reference ───────────────────────────────────────────────────────────

def verify(
    spec_rules: dict[int, str], annotations: list[Annotation]
) -> tuple[list[str], list[str], list[str]]:
    """
    Returns three lists of diagnostic strings:
      - mismatches: rule number exists but name doesn't match
      - unknown:    rule number outside 1–211 or not in spec
      - uncovered:  spec rules with no annotation
    """
    mismatches: list[str] = []
    unknown: list[str] = []
    covered: set[int] = set()

    for ann in annotations:
        if ann.rule_num is None:
            continue  # section-only annotation, no rule to check
        num = ann.rule_num
        if num not in spec_rules:
            unknown.append(
                f"  [{num:3d}] \"{ann.rule_name}\" — not in spec (1–{max(spec_rules)})"
                f"  @ {ann.loc()}"
            )
            continue
        covered.add(num)
        if ann.rule_name is not None:
            spec_name = spec_rules[num]
            if not names_match(ann.rule_name, spec_name):
                mismatches.append(
                    f"  [{num:3d}] lean=\"{ann.rule_name}\"  spec=\"{spec_name}\""
                    f"  @ {ann.loc()}"
                )

    uncovered_rules: list[str] = []
    for num in sorted(spec_rules):
        if num not in covered:
            uncovered_rules.append(f"  [{num:3d}] {spec_rules[num]}")

    return mismatches, unknown, uncovered_rules


# ── Main ──────────────────────────────────────────────────────────────────────

def main() -> int:
    parser = argparse.ArgumentParser(
        description="Verify @[yaml_spec] annotations against yaml-spec-1.2.yaml"
    )
    parser.add_argument(
        "--spec-url",
        default=DEFAULT_SPEC_URL,
        help="URL to fetch yaml-spec-1.2.yaml from",
    )
    parser.add_argument(
        "--spec-file",
        default=None,
        help="Local path to yaml-spec-1.2.yaml (overrides --spec-url)",
    )
    parser.add_argument(
        "--lean-root",
        default=None,
        help="Root directory of Lean source files (default: script's grandparent)",
    )
    args = parser.parse_args()

    # Determine Lean root
    if args.lean_root:
        lean_root = Path(args.lean_root)
    else:
        lean_root = Path(__file__).resolve().parent.parent
    if not lean_root.is_dir():
        print(f"Error: Lean root not found: {lean_root}", file=sys.stderr)
        return 1

    # Load spec
    if args.spec_file:
        print(f"Reading spec from {args.spec_file}")
        with open(args.spec_file, "r", encoding="utf-8") as f:
            spec_text = f.read()
    else:
        print(f"Fetching spec from {args.spec_url}")
        with urlopen(args.spec_url) as resp:
            spec_text = resp.read().decode("utf-8")

    spec_rules = parse_spec(spec_text)
    print(f"Parsed {len(spec_rules)} spec rules (expected 211)")
    if len(spec_rules) != 211:
        print(f"  WARNING: expected 211 rules, got {len(spec_rules)}", file=sys.stderr)

    # Scan Lean annotations
    print(f"Scanning Lean files under {lean_root}")
    annotations = scan_lean_files(lean_root)
    rule_annotations = [a for a in annotations if a.rule_num is not None]
    section_only = [a for a in annotations if a.rule_num is None]
    unique_rules = {a.rule_num for a in rule_annotations}

    print(f"Found {len(annotations)} total annotations "
          f"({len(rule_annotations)} with rule numbers, "
          f"{len(section_only)} section-only)")
    print(f"Covering {len(unique_rules)} unique rule numbers")
    print()

    # Verify
    mismatches, unknown, uncovered = verify(spec_rules, annotations)

    exit_code = 0

    if mismatches:
        exit_code = 1
        print(f"=== NAME MISMATCHES ({len(mismatches)}) ===")
        print("  Annotation rule name doesn't match spec rule name:")
        for m in mismatches:
            print(m)
        print()

    if unknown:
        exit_code = 1
        print(f"=== UNKNOWN RULES ({len(unknown)}) ===")
        print("  Rule number not found in spec:")
        for u in unknown:
            print(u)
        print()

    print(f"=== COVERAGE ({len(unique_rules)}/{len(spec_rules)} rules) ===")
    coverage_pct = len(unique_rules) / len(spec_rules) * 100 if spec_rules else 0
    print(f"  {coverage_pct:.1f}% of spec rules are annotated")
    if uncovered:
        print(f"  {len(uncovered)} uncovered rules:")
        for u in uncovered:
            print(u)
    else:
        print("  All spec rules are covered!")
    print()

    if not mismatches and not unknown:
        print("OK — all annotated rules are consistent with the spec.")
    else:
        print("FAIL — inconsistencies found (see above).")

    return exit_code


if __name__ == "__main__":
    sys.exit(main())
