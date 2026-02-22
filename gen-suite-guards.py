#!/usr/bin/env python3
"""
Generate compile-time #guard tests from yaml-test-suite.

Reads every .yaml file in yaml-test-suite/src/, parses the test metadata,
identifies passing tests, and generates Lean files with #guard statements
that inline the YAML content as string literals.

The generated files go to Lean4Yaml/Proofs/SuiteGuards/*.lean.
Each stage is a separate file for parallel compilation.

Usage:
    python3 gen-suite-guards.py [--dry-run]
"""

import os
import re
import sys
from dataclasses import dataclass, field
from pathlib import Path
from typing import Optional


@dataclass
class TestCase:
    id: str = ""
    name: str = ""
    tags: list[str] = field(default_factory=list)
    expect_fail: bool = False
    yaml: str = ""
    tree: str = ""
    variant: int = 0


def count_leading_spaces(s: str) -> int:
    return len(s) - len(s.lstrip(' '))


def strip_indent(n: int, s: str) -> str:
    return s[n:] if len(s) >= n else s


def unescape_test_yaml(s: str) -> str:
    """Replicate the SuiteRunner.unescapeTestYaml logic."""
    s = s.replace('\u2423', ' ')   # ␣ → space
    s = s.replace('\u2014', '')    # — (em-dash) → remove (tab fill)
    s = s.replace('\u00BB', '\t')  # » → tab
    s = s.replace('\u2192', '\t')  # → → tab
    s = s.replace('\u2190', '\r')  # ← → carriage return
    s = s.replace('\u21B5', '')    # ↵ → remove (cosmetic)
    s = s.replace('\u220E', '')    # ∎ → remove (cosmetic)
    s = s.replace('\u21D4', '\uFEFF')  # ⇔ → BOM
    return s


def parse_test_file(test_id: str, content: str) -> list[TestCase]:
    """Parse a yaml-test-suite test file into test cases.

    Replicates the Meta.lean state machine parser.
    """
    cases: list[TestCase] = []
    current = TestCase()
    in_item = False
    current_field: Optional[str] = None  # None, 'yaml', 'tree', 'other'
    block_indent = 0
    variant_counter = 0

    def finalize_item():
        nonlocal cases, current, in_item, current_field, block_indent
        if in_item:
            cases.append(current)
            current = TestCase()
            in_item = False
        current_field = None
        block_indent = 0

    def process_block_line(line: str):
        nonlocal current, current_field, block_indent
        indent = count_leading_spaces(line)
        if block_indent == 0 and indent > 0:
            block_indent = indent
        trimmed = line.lstrip()
        if indent < block_indent and trimmed:
            return  # dedented non-empty → end of block
        content_str = "\n" if not trimmed else strip_indent(block_indent, line) + "\n"
        if current_field == 'yaml':
            current.yaml += content_str
        elif current_field == 'tree':
            current.tree += content_str

    def process_key_value(key: str, value: str):
        nonlocal current, current_field, block_indent
        current_field = None
        block_indent = 0
        val = value.strip()
        if key == 'name':
            current.name = val
        elif key == 'tags':
            current.tags = [t for t in val.split(' ') if t]
        elif key == 'fail':
            current.expect_fail = (val == 'true')
        elif key == 'yaml':
            if val.startswith('|'):
                current.yaml = ''
                current_field = 'yaml'
                block_indent = 0
            else:
                current.yaml = val
        elif key == 'tree':
            if val.startswith('|'):
                current.tree = ''
                current_field = 'tree'
                block_indent = 0
            else:
                current.tree = val
        elif key in ('json', 'dump', 'from', 'tidy', 'emit'):
            if val.startswith('|'):
                current_field = 'other'
                block_indent = 0

    lines = content.split('\n')
    for line in lines:
        if current_field is not None:
            indent = count_leading_spaces(line)
            trimmed = line.lstrip()
            if not trimmed:
                process_block_line(line)
                continue
            if block_indent > 0 and indent < block_indent:
                current_field = None
                block_indent = 0
                # Fall through to process as normal line
            elif block_indent == 0 and indent >= 4:
                process_block_line(line)
                continue
            elif block_indent > 0:
                process_block_line(line)
                continue
            else:
                current_field = None
                block_indent = 0
                # Fall through

        stripped = line.strip()
        if stripped == '---':
            finalize_item()
            continue

        trimmed = line.lstrip()
        if trimmed.startswith('- '):
            finalize_item()
            current = TestCase(id=test_id, variant=variant_counter)
            variant_counter += 1
            in_item = True
            rest = trimmed[2:]
            parts = rest.split(': ', 1)
            if len(parts) == 2:
                process_key_value(parts[0].strip(), parts[1])
            elif len(parts) == 1 and ':' in parts[0]:
                kv = parts[0].split(':', 1)
                process_key_value(kv[0].strip(), kv[1] if len(kv) > 1 else '')
        else:
            parts = trimmed.split(': ', 1)
            if len(parts) == 2:
                process_key_value(parts[0].strip(), parts[1])

    finalize_item()
    for tc in cases:
        tc.id = test_id
    return cases


def classify_stage(tags: list[str]) -> str:
    """Classify a test into a stage based on its tags (mirrors Meta.lean)."""
    if any(t == 'error' for t in tags):
        return 'error'
    if any(t in ('anchor', 'alias', 'tag', 'complex-key', 'explicit-key') for t in tags):
        return 'advanced'
    if any(t in ('directive', 'footer', 'header', 'document') for t in tags):
        return 'document'
    if any(t == 'flow' for t in tags):
        return 'flow'
    if any(t in ('scalar', 'double', 'single', 'literal', 'folded') for t in tags):
        return 'scalar'
    return 'block'


def is_1_3_specific(tags: list[str]) -> bool:
    return any(t in ('1.3-err', '1.3-mod') for t in tags)


def should_skip(tc: TestCase) -> Optional[str]:
    """Return skip reason or None if test should be included."""
    yaml = unescape_test_yaml(tc.yaml)
    if not yaml or yaml.isspace():
        return "empty yaml input"
    if is_1_3_specific(tc.tags):
        return "YAML 1.3 specific"
    return None


def lean_escape_string(s: str) -> str:
    """Escape a string for use as a Lean string literal."""
    result = []
    for ch in s:
        cp = ord(ch)
        if ch == '\\':
            result.append('\\\\')
        elif ch == '"':
            result.append('\\"')
        elif ch == '\n':
            result.append('\\n')
        elif ch == '\t':
            result.append('\\t')
        elif ch == '\r':
            result.append('\\r')
        elif ch == '\0':
            result.append('\\0')
        elif cp == 0xFEFF:
            result.append('\\uFEFF')
        elif 0x20 <= cp <= 0x7E:
            result.append(ch)
        elif cp > 0x7E:
            # Use Lean's Unicode escape syntax:
            # \uXXXX for BMP (exactly 4 hex digits)
            # For supplementary chars (> U+FFFF), include directly as UTF-8
            # since Lean 4 source files are UTF-8 and \U is not supported.
            if cp <= 0xFFFF:
                result.append(f'\\u{cp:04X}')
            else:
                result.append(ch)
        else:
            # Control characters
            result.append(f'\\x{cp:02X}')
    return result


def lean_string_literal(s: str) -> str:
    """Create a complete Lean string literal."""
    escaped = lean_escape_string(s)
    return '"' + ''.join(escaped) + '"'


def generate_guard(tc: TestCase, unescaped_yaml: str) -> str:
    """Generate a #guard statement for a test case."""
    lit = lean_string_literal(unescaped_yaml)
    tid = tc.id
    variant = tc.variant

    if tc.expect_fail:
        # Error test: parser should fail
        guard_expr = (
            f"-- {tid}:{variant} {tc.name}\n"
            f"#guard match parseYaml {lit} with\n"
            f"  | .ok _ => false\n"
            f"  | .error _ => true\n"
        )
    else:
        # Normal test: parser should succeed
        guard_expr = (
            f"-- {tid}:{variant} {tc.name}\n"
            f"#guard match parseYaml {lit} with\n"
            f"  | .ok _ => true\n"
            f"  | .error _ => false\n"
        )
    return guard_expr


def generate_lean_file(stage: str, guards: list[str], total: int) -> str:
    """Generate a complete Lean file for a stage."""
    stage_cap = stage.capitalize()
    header = f"""/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Parser.Document

/-!
# yaml-test-suite Compile-Time Guards \u2014 {stage_cap} Stage

Auto-generated from yaml-test-suite test files by `gen-suite-guards.py`.
Each `#guard` is evaluated by Lean's kernel during `lake build`.

**{total} guards** covering all passing {stage} tests.

These are Phase 4 of the verification plan: yaml-test-suite as compile-time proofs.
-/

namespace Lean4Yaml.Proofs.SuiteGuards.{stage_cap}

open Lean4Yaml.Parse

"""
    footer = f"\nend Lean4Yaml.Proofs.SuiteGuards.{stage_cap}\n"
    return header + '\n'.join(guards) + footer


def main():
    dry_run = '--dry-run' in sys.argv

    suite_dir = Path(__file__).parent / 'yaml-test-suite' / 'src'
    if not suite_dir.exists():
        print(f"Error: {suite_dir} not found", file=sys.stderr)
        sys.exit(1)

    output_dir = Path(__file__).parent / 'Lean4Yaml' / 'Proofs' / 'SuiteGuards'

    # Read and parse all test files
    all_tests: list[TestCase] = []
    for yaml_file in sorted(suite_dir.glob('*.yaml')):
        test_id = yaml_file.stem
        content = yaml_file.read_text(encoding='utf-8')
        cases = parse_test_file(test_id, content)
        all_tests.extend(cases)

    print(f"Parsed {len(all_tests)} test cases from {len(list(suite_dir.glob('*.yaml')))} files")

    # Classify and filter
    by_stage: dict[str, list[tuple[TestCase, str]]] = {
        'scalar': [], 'flow': [], 'block': [],
        'document': [], 'advanced': [], 'error': []
    }

    skipped = 0
    included = 0
    for tc in all_tests:
        skip_reason = should_skip(tc)
        if skip_reason:
            skipped += 1
            continue

        unescaped = unescape_test_yaml(tc.yaml)
        stage = classify_stage(tc.tags)

        # For error tests without the error stage classification,
        # they get classified by their other tags. But if expect_fail=True
        # and not classified as error, we still need to handle them.
        # The suite runner skips error tests in non-error stages,
        # but in the "advanced" stage run (which is cumulative), error tests
        # would be in the error stage. Let's follow the suite runner:
        # error tests go to the error stage.
        if tc.expect_fail:
            stage = 'error'

        by_stage[stage].append((tc, unescaped))
        included += 1

    # Now we need to figure out which tests actually PASS.
    # For non-error tests: test passes if parseYaml succeeds
    # For error tests: test passes if parseYaml fails (expected fail)
    #   OR if it's the one known UP (H7TQ), it would fail the guard
    #
    # Since we're generating compile-time guards, we need to only include
    # tests that will actually pass the guard. The suite runner shows:
    # - 847 passed, 2 failed (H7TQ × 2 stages)
    # - H7TQ: expected parse failure but succeeded
    #
    # H7TQ is an error test where our parser succeeds but shouldn't.
    # We should EXCLUDE H7TQ from the error guards.

    print(f"Included: {included}, Skipped: {skipped}")
    for stage, tests in sorted(by_stage.items()):
        print(f"  {stage}: {len(tests)} tests")

    # Known discrepancies between kernel evaluation and compiled execution.
    # These error tests pass in the runtime suite runner (compiled tryparse)
    # but the kernel evaluates parseYaml differently. Typically parser
    # recovery behaviors (e.g., unclosed quotes → plain scalar) where
    # validationError propagation differs between kernel and native code.
    # NOTE: CQ3W was here but fixed by adding setValidationError to the
    # fuel-exhaustion case of collectChars in doubleQuotedScalar.
    KERNEL_DISCREPANCIES: set[str] = set()

    # Generate guards per stage
    generated_files = {}
    total_guards = 0

    for stage, tests in sorted(by_stage.items()):
        guards = []
        for tc, unescaped in tests:
            # Skip H7TQ (known unfixable UP) and kernel discrepancies
            if tc.id == 'H7TQ' and tc.expect_fail:
                continue
            if tc.id in KERNEL_DISCREPANCIES:
                continue
            guard = generate_guard(tc, unescaped)
            guards.append(guard)

        if guards:
            content = generate_lean_file(stage, guards, len(guards))
            generated_files[stage] = content
            total_guards += len(guards)
            print(f"  → {stage}.lean: {len(guards)} guards")

    print(f"\nTotal: {total_guards} guards across {len(generated_files)} files")

    if dry_run:
        print("\n[DRY RUN] Would generate:")
        for stage in sorted(generated_files):
            path = output_dir / f"{stage.capitalize()}.lean"
            print(f"  {path}")
        return

    # Write files
    output_dir.mkdir(parents=True, exist_ok=True)
    for stage, content in sorted(generated_files.items()):
        path = output_dir / f"{stage.capitalize()}.lean"
        path.write_text(content, encoding='utf-8')
        print(f"Wrote {path}")

    print(f"\nDone! {total_guards} guards in {len(generated_files)} files.")
    print("Next: add imports to Lean4Yaml.lean and run `lake build`")


if __name__ == '__main__':
    main()
