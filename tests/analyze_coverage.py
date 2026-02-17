#!/usr/bin/env python3
"""Analyze yaml-test-suite coverage results from the HTML report.

Usage:
    python3 tests/analyze_coverage.py [docs/coverage-all.html]

Outputs:
    - Failure root cause analysis (grouped by error pattern)
    - Unexpected pass analysis (grouped by stage + tags)
    - Prioritized fix recommendations
"""

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


def parse_html(html: str) -> list[dict]:
    """Extract test rows from coverage HTML report."""
    tests = []
    # Split into individual <tr> blocks
    row_pattern = re.compile(
        r'<tr class="test-row" data-outcome="([^"]+)" '
        r'data-stage="([^"]+)" data-search="([^"]+)">'
    )
    tag_pattern = re.compile(r'<span class="tag">([^<]+)</span>')
    error_pattern = re.compile(r'<span class="error-msg" title="([^"]*)">')
    id_pattern = re.compile(r'<td>([A-Z0-9]{3,5})</td>')

    # Split by test rows
    parts = html.split('<tr class="test-row"')
    for part in parts[1:]:  # skip before first match
        part = '<tr class="test-row"' + part
        row_match = row_pattern.search(part)
        if not row_match:
            continue

        outcome, stage, search = row_match.groups()
        tags = tag_pattern.findall(part)
        error_match = error_pattern.search(part)
        error = error_match.group(1) if error_match else ""
        id_match = id_pattern.search(part)
        test_id = id_match.group(1) if id_match else search.split()[0].upper()

        # Extract name from search field (ID is first word, rest is name + tags)
        search_parts = search.split()
        name_words = [w for w in search_parts[1:] if w not in tags]
        name = " ".join(name_words).strip()

        tests.append({
            "id": test_id,
            "outcome": outcome,
            "stage": stage,
            "name": name,
            "tags": tags,
            "error": error,
        })

    return tests


def classify_error(error: str) -> str:
    """Classify an error message into a root cause category."""
    if not error:
        return "no error message"
    if "expected parse failure but succeeded" in error:
        return "PERMISSIVE: expected parse failure but succeeded"

    # Tag-related
    if "unexpected token" in error and "'!'" in error:
        return "TAG: ! token not supported"
    if "expected plain scalar" in error and "'!'" in error:
        return "TAG: ! token not supported"

    # Explicit key
    if "'?'" in error:
        return "EXPLICIT_KEY: ? token not supported"

    # Anchor/alias issues
    if "'*'" in error:
        return "ALIAS: * parse error"
    if "'&'" in error:
        return "ANCHOR: & parse error"

    # Colon issues
    if "unhandled construct ':'" in error:
        return "COLON: unhandled : in context"

    # Escape sequences
    if "unknown escape" in error:
        return "ESCAPE: unknown escape sequence"

    # Value expected
    if "expected YAML value" in error and "'!'" not in error:
        return "VALUE: expected YAML value"

    # Flow issues
    if "expected flow" in error:
        return "FLOW: flow construct error"
    if "'['" in error or "']'" in error:
        return "FLOW: bracket error"

    # Block issues
    if "expected block" in error:
        return "BLOCK: block construct error"

    # Indent
    if "indent" in error.lower():
        return "INDENT: indentation error"

    # Output mismatch (wrong parse result)
    if "output mismatch" in error.lower() or "wrong output" in error.lower():
        return "MISMATCH: wrong parse output"

    # Scalar issues
    if "expected plain scalar" in error:
        return "SCALAR: plain scalar error"
    if "expected double" in error or "expected single" in error:
        return "SCALAR: quoted scalar error"

    return f"OTHER: {error[:80]}"


def analyze_failures(tests: list[dict]) -> None:
    """Analyze failures grouped by root cause."""
    failures = [t for t in tests if t["outcome"] == "fail"]
    print(f"\n{'='*70}")
    print(f"FAILURE ANALYSIS ({len(failures)} failures)")
    print(f"{'='*70}")

    # Group by root cause
    by_cause = defaultdict(list)
    for t in failures:
        cause = classify_error(t["error"])
        by_cause[cause].append(t)

    # Sort by count
    for cause, tests_in_cause in sorted(by_cause.items(), key=lambda x: -len(x[1])):
        count = len(tests_in_cause)
        print(f"\n  [{count:2d}] {cause}")
        # Group by stage within cause
        by_stage = Counter(t["stage"] for t in tests_in_cause)
        stage_str = ", ".join(f"{s}:{c}" for s, c in sorted(by_stage.items(), key=lambda x: -x[1]))
        print(f"       stages: {stage_str}")
        # Show first few test IDs
        ids = [t["id"] for t in tests_in_cause[:8]]
        if len(tests_in_cause) > 8:
            ids.append(f"... +{len(tests_in_cause) - 8} more")
        print(f"       tests:  {', '.join(ids)}")


def analyze_unexpected_passes(tests: list[dict]) -> None:
    """Analyze unexpected passes grouped by cause."""
    unexp = [t for t in tests if t["outcome"] == "unexpected-pass"]
    print(f"\n{'='*70}")
    print(f"UNEXPECTED PASS ANALYSIS ({len(unexp)} unexpected passes)")
    print(f"{'='*70}")

    # Group by stage
    by_stage = defaultdict(list)
    for t in unexp:
        by_stage[t["stage"]].append(t)

    for stage, tests_in_stage in sorted(by_stage.items(), key=lambda x: -len(x[1])):
        count = len(tests_in_stage)
        print(f"\n  Stage: {stage} ({count} tests)")

        # Sub-group by tags
        tag_counter = Counter()
        for t in tests_in_stage:
            for tag in t["tags"]:
                tag_counter[tag] += 1
        top_tags = tag_counter.most_common(10)
        print(f"    common tags: {', '.join(f'{t}({c})' for t, c in top_tags)}")

        # Group by error category
        by_cause = defaultdict(list)
        for t in tests_in_stage:
            cause = classify_error(t["error"])
            by_cause[cause].append(t)

        for cause, cause_tests in sorted(by_cause.items(), key=lambda x: -len(x[1])):
            print(f"    [{len(cause_tests):2d}] {cause}")
            ids = [t["id"] for t in cause_tests[:6]]
            if len(cause_tests) > 6:
                ids.append(f"+{len(cause_tests) - 6}")
            print(f"         {', '.join(ids)}")


def generate_recommendations(tests: list[dict]) -> None:
    """Generate prioritized fix recommendations."""
    failures = [t for t in tests if t["outcome"] == "fail"]
    unexp = [t for t in tests if t["outcome"] == "unexpected-pass"]

    print(f"\n{'='*70}")
    print(f"PRIORITIZED RECOMMENDATIONS")
    print(f"{'='*70}")

    # Count failure root causes
    fail_causes = Counter()
    for t in failures:
        fail_causes[classify_error(t["error"])] += 1

    # Count unexpected pass causes
    unexp_causes = Counter()
    for t in unexp:
        unexp_causes[classify_error(t["error"])] += 1

    print(f"\n  --- Failures: Top Root Causes (fix these to increase pass rate) ---")
    for i, (cause, count) in enumerate(fail_causes.most_common(10), 1):
        impact = f"+{count} tests"
        print(f"  {i:2d}. [{impact:>10s}] {cause}")

    print(f"\n  --- Unexpected Passes: Root Causes (parser too permissive) ---")
    for i, (cause, count) in enumerate(unexp_causes.most_common(10), 1):
        print(f"  {i:2d}. [{count:3d} tests] {cause}")

    # Feature-based summary
    print(f"\n  --- Feature Implementation Priority ---")
    tag_to_fail = defaultdict(int)
    tag_to_unexp = defaultdict(int)
    for t in failures:
        for tag in t["tags"]:
            tag_to_fail[tag] += 1
    for t in unexp:
        for tag in t["tags"]:
            tag_to_unexp[tag] += 1

    all_tags = set(tag_to_fail.keys()) | set(tag_to_unexp.keys())
    tag_impact = []
    for tag in all_tags:
        total = tag_to_fail.get(tag, 0) + tag_to_unexp.get(tag, 0)
        tag_impact.append((tag, tag_to_fail.get(tag, 0), tag_to_unexp.get(tag, 0), total))

    tag_impact.sort(key=lambda x: -x[3])
    print(f"  {'Tag':<20s} {'Failures':>10s} {'Unexp Pass':>12s} {'Total Impact':>14s}")
    print(f"  {'-'*20} {'-'*10} {'-'*12} {'-'*14}")
    for tag, fails, unexp_count, total in tag_impact[:15]:
        print(f"  {tag:<20s} {fails:>10d} {unexp_count:>12d} {total:>14d}")


def print_summary(tests: list[dict]) -> None:
    """Print overall summary."""
    outcomes = Counter(t["outcome"] for t in tests)
    total = len(tests)
    correct = outcomes.get("pass", 0)

    print(f"\n{'='*70}")
    print(f"COVERAGE SUMMARY")
    print(f"{'='*70}")
    print(f"  Total:           {total}")
    print(f"  Passed:          {outcomes.get('pass', 0)}")
    print(f"  Failed:          {outcomes.get('fail', 0)}")
    print(f"  Unexpected Pass: {outcomes.get('unexpected-pass', 0)}")
    print(f"  Skipped:         {outcomes.get('skip', 0)}")
    print(f"  Correct:         {correct}/{total} ({100*correct/total:.1f}%)")

    # By stage
    stages = ["scalar", "flow", "block", "document", "advanced", "error"]
    print(f"\n  {'Stage':<12s} {'Total':>6s} {'Pass':>6s} {'Fail':>6s} {'Unexp':>6s} {'Skip':>6s} {'Rate':>8s}")
    print(f"  {'-'*12} {'-'*6} {'-'*6} {'-'*6} {'-'*6} {'-'*6} {'-'*8}")
    for stage in stages:
        stage_tests = [t for t in tests if t["stage"] == stage]
        st = Counter(t["outcome"] for t in stage_tests)
        n = len(stage_tests)
        p = st.get("pass", 0)
        rate = f"{100*p/n:.0f}%" if n > 0 else "N/A"
        print(f"  {stage:<12s} {n:>6d} {p:>6d} {st.get('fail',0):>6d} {st.get('unexpected-pass',0):>6d} {st.get('skip',0):>6d} {rate:>8s}")


def list_all_failures(tests: list[dict]) -> None:
    """List every failure with its error, for detailed debugging."""
    failures = [t for t in tests if t["outcome"] == "fail"]
    print(f"\n{'='*70}")
    print(f"ALL FAILURES (detailed)")
    print(f"{'='*70}")

    by_cause = defaultdict(list)
    for t in failures:
        cause = classify_error(t["error"])
        by_cause[cause].append(t)

    for cause, cause_tests in sorted(by_cause.items(), key=lambda x: -len(x[1])):
        print(f"\n  --- {cause} ({len(cause_tests)}) ---")
        for t in sorted(cause_tests, key=lambda x: x["id"]):
            tags_str = ",".join(t["tags"]) if t["tags"] else ""
            name = t["name"][:50] if t["name"] else ""
            print(f"    {t['id']:<6s} [{t['stage']:<8s}] {name:<50s} {tags_str}")


def list_all_unexpected_passes(tests: list[dict]) -> None:
    """List every unexpected pass for detailed review."""
    unexp = [t for t in tests if t["outcome"] == "unexpected-pass"]
    print(f"\n{'='*70}")
    print(f"ALL UNEXPECTED PASSES (detailed)")
    print(f"{'='*70}")

    by_stage = defaultdict(list)
    for t in unexp:
        by_stage[t["stage"]].append(t)

    for stage, stage_tests in sorted(by_stage.items(), key=lambda x: -len(x[1])):
        print(f"\n  --- Stage: {stage} ({len(stage_tests)}) ---")
        for t in sorted(stage_tests, key=lambda x: x["id"]):
            tags_str = ",".join(t["tags"]) if t["tags"] else ""
            name = t["name"][:50] if t["name"] else ""
            err = t["error"][:60] if t["error"] else ""
            print(f"    {t['id']:<6s} {name:<50s} {tags_str}")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    flags = [a for a in sys.argv[1:] if a.startswith("-")]
    html_path = args[0] if args else "docs/coverage-all.html"
    path = Path(html_path)
    if not path.exists():
        print(f"Error: {path} not found", file=sys.stderr)
        print(f"Usage: python3 tests/analyze_coverage.py [docs/coverage-all.html] [-v|--verbose]", file=sys.stderr)
        sys.exit(1)

    html = path.read_text()
    tests = parse_html(html)

    if not tests:
        print("Error: no test rows found in HTML", file=sys.stderr)
        sys.exit(1)

    verbose = "--verbose" in flags or "-v" in flags

    print_summary(tests)
    analyze_failures(tests)
    analyze_unexpected_passes(tests)
    generate_recommendations(tests)

    if verbose:
        list_all_failures(tests)
        list_all_unexpected_passes(tests)


if __name__ == "__main__":
    main()
