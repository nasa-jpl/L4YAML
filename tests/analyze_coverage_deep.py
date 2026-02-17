#!/usr/bin/env python3
"""Deep-dive analysis of yaml-test-suite failures and unexpected passes.

Usage:
    python3 tests/analyze_coverage_deep.py [docs/coverage-all.html]

Provides:
    - Token-level failure root cause analysis
    - Missing feature categorization
    - Unexpected pass categorization by error type missed
    - Actionable fix batches with estimated impact
"""

import re
import sys
from collections import Counter, defaultdict
from pathlib import Path


def parse_html(html: str) -> list[dict]:
    """Extract test rows from coverage HTML."""
    rows = []
    parts = html.split('<tr class="test-row"')
    for part in parts[1:]:
        part = '<tr class="test-row"' + part
        m = re.search(
            r'data-outcome="([^"]+)" data-stage="([^"]+)" data-search="([^"]+)"', part
        )
        if not m:
            continue
        tags = re.findall(r'<span class="tag">([^<]+)</span>', part)
        err_m = re.search(r'<span class="error-msg" title="([^"]*?)">', part)
        err = err_m.group(1) if err_m else ""
        id_m = re.search(r"<td>([A-Z0-9]{3,5})</td>", part)
        test_id = id_m.group(1) if id_m else m.group(3).split()[0].upper()
        name_m = re.search(r"<td>([^<]*)</td>\s*<td>[^<]*</td>\s*<td>", part)
        name = ""
        tds = re.findall(r"<td>([^<]*)</td>", part)
        if len(tds) >= 2:
            name = tds[1]  # second td is name

        rows.append(
            {
                "id": test_id,
                "outcome": m.group(1),
                "stage": m.group(2),
                "name": name,
                "tags": tags,
                "error": err,
            }
        )
    return rows


def analyze_failure_tokens(rows: list[dict]) -> None:
    """Categorize failures by the specific token that trips the parser."""
    failures = [r for r in rows if r["outcome"] == "fail"]
    print(f"\n{'='*70}")
    print(f"FAILURE TOKEN ANALYSIS ({len(failures)} failures)")
    print(f"{'='*70}")

    token_counter = Counter()
    token_tests = defaultdict(list)
    for r in failures:
        err = r["error"]
        # Extract the problematic token
        token_m = re.search(r"unexpected token '([^']*)'", err)
        if token_m:
            token = token_m.group(1)
            token_counter[f"unexpected '{token}'"] += 1
            token_tests[f"unexpected '{token}'"].append(r["id"])
        elif "unhandled construct" in err:
            constr_m = re.search(r"unhandled construct '([^']*)'", err)
            if constr_m:
                token_counter[f"unhandled '{constr_m.group(1)}'"] += 1
                token_tests[f"unhandled '{constr_m.group(1)}'"].append(r["id"])
        elif "unknown escape" in err:
            esc_m = re.search(r"unknown escape: \\(.)", err)
            token_counter[f"unknown escape"] += 1
            token_tests["unknown escape"].append(r["id"])
        elif "expected parse failure" in err:
            token_counter["PERMISSIVE (should fail)"] += 1
            token_tests["PERMISSIVE (should fail)"].append(r["id"])
        elif err:
            token_counter[f"other: {err[:50]}"] += 1
            token_tests[f"other: {err[:50]}"].append(r["id"])
        else:
            token_counter["no error msg"] += 1
            token_tests["no error msg"].append(r["id"])

    for k, v in sorted(token_counter.items(), key=lambda x: -x[1]):
        ids = token_tests[k][:6]
        more = f" +{len(token_tests[k]) - 6}" if len(token_tests[k]) > 6 else ""
        print(f"  {v:3d}  {k}")
        print(f"       {', '.join(ids)}{more}")


def analyze_missing_features(rows: list[dict]) -> None:
    """Categorize failures by what YAML feature is missing."""
    failures = [r for r in rows if r["outcome"] == "fail"]
    print(f"\n{'='*70}")
    print(f"MISSING FEATURE ANALYSIS ({len(failures)} failures)")
    print(f"{'='*70}")

    feature_tests = defaultdict(list)
    for r in failures:
        tags = set(r["tags"])
        if "tag" in tags or "unknown-tag" in tags or "local-tag" in tags:
            feature_tests["TAGS (!/!!/<handle>)"].append(r)
        elif "explicit-key" in tags:
            feature_tests["EXPLICIT KEY (?)"].append(r)
        elif "complex-key" in tags:
            feature_tests["COMPLEX KEY"].append(r)
        elif "alias" in tags and "anchor" not in tags:
            feature_tests["ALIAS edge cases"].append(r)
        elif "anchor" in tags:
            feature_tests["ANCHOR edge cases"].append(r)
        elif "comment" in tags:
            feature_tests["COMMENT handling"].append(r)
        elif "empty-key" in tags:
            feature_tests["EMPTY KEY"].append(r)
        elif "flow" in tags:
            feature_tests["FLOW edge cases"].append(r)
        elif "edge" in tags:
            feature_tests["EDGE cases"].append(r)
        elif "indent" in tags:
            feature_tests["INDENT edge cases"].append(r)
        else:
            feature_tests["OTHER"].append(r)

    for feat, tests in sorted(feature_tests.items(), key=lambda x: -len(x[1])):
        count = len(tests)
        by_stage = Counter(t["stage"] for t in tests)
        stage_str = ", ".join(
            f"{s}:{c}" for s, c in sorted(by_stage.items(), key=lambda x: -x[1])
        )
        ids = [t["id"] for t in tests[:8]]
        more = f" +{count - 8}" if count > 8 else ""
        print(f"\n  [{count:2d}] {feat}")
        print(f"       stages: {stage_str}")
        print(f"       tests:  {', '.join(ids)}{more}")


def analyze_unexpected_passes_detail(rows: list[dict]) -> None:
    """Categorize unexpected passes by what validation the parser is missing."""
    unexp = [r for r in rows if r["outcome"] == "unexpected-pass"]
    print(f"\n{'='*70}")
    print(f"UNEXPECTED PASS ANALYSIS ({len(unexp)} unexpected passes)")
    print(f"{'='*70}")

    # Error stage: parser should reject but doesn't
    error_unexp = [r for r in unexp if r["stage"] == "error"]
    print(f"\n  Error stage: {len(error_unexp)} tests (parser too permissive)")
    print(f"  These are invalid YAML that the parser incorrectly accepts.\n")

    cat_tests = defaultdict(list)
    for r in error_unexp:
        tags = set(r["tags"])
        if "indent" in tags:
            cat_tests["INDENT validation missing"].append(r)
        elif "flow" in tags and ("sequence" in tags or "mapping" in tags):
            cat_tests["FLOW structure validation missing"].append(r)
        elif "double" in tags or "single" in tags:
            cat_tests["QUOTED scalar validation missing"].append(r)
        elif "comment" in tags:
            cat_tests["COMMENT validation missing"].append(r)
        elif "directive" in tags:
            cat_tests["DIRECTIVE validation missing"].append(r)
        elif "anchor" in tags or "alias" in tags:
            cat_tests["ANCHOR/ALIAS validation missing"].append(r)
        elif "folded" in tags or "literal" in tags:
            cat_tests["BLOCK SCALAR validation missing"].append(r)
        elif "tag" in tags:
            cat_tests["TAG validation missing"].append(r)
        elif "footer" in tags or "header" in tags:
            cat_tests["DOCUMENT marker validation missing"].append(r)
        elif "mapping" in tags:
            cat_tests["MAPPING validation missing"].append(r)
        elif "sequence" in tags:
            cat_tests["SEQUENCE validation missing"].append(r)
        elif "scalar" in tags:
            cat_tests["SCALAR validation missing"].append(r)
        else:
            cat_tests["OTHER"].append(r)

    for cat, tests in sorted(cat_tests.items(), key=lambda x: -len(x[1])):
        ids = [t["id"] for t in tests[:6]]
        more = f" +{len(tests) - 6}" if len(tests) > 6 else ""
        print(f"    [{len(tests):2d}] {cat}")
        print(f"         {', '.join(ids)}{more}")

    # Non-error stages
    non_error = [r for r in unexp if r["stage"] != "error"]
    print(f"\n  Non-error stages: {len(non_error)} tests")
    print(f"  These expect parse failure for invalid YAML in scalar/flow/block/document stages.\n")

    by_stage = defaultdict(list)
    for r in non_error:
        by_stage[r["stage"]].append(r)

    for stage, tests in sorted(by_stage.items(), key=lambda x: -len(x[1])):
        ids = [t["id"] for t in tests[:8]]
        more = f" +{len(tests) - 8}" if len(tests) > 8 else ""
        print(f"    [{len(tests):2d}] {stage}: {', '.join(ids)}{more}")


def generate_fix_batches(rows: list[dict]) -> None:
    """Generate prioritized fix batches with estimated impact."""
    failures = [r for r in rows if r["outcome"] == "fail"]
    unexp = [r for r in rows if r["outcome"] == "unexpected-pass"]

    print(f"\n{'='*70}")
    print(f"PRIORITIZED FIX BATCHES")
    print(f"{'='*70}")

    batches = []

    # Batch 1: Tags
    tag_fails = [
        r
        for r in failures
        if set(r["tags"]) & {"tag", "unknown-tag", "local-tag"}
    ]
    tag_unexp = [r for r in unexp if "tag" in r["tags"]]
    batches.append(
        (
            "Step 8: Tag support (!tag, !!type, %TAG directive)",
            len(tag_fails),
            len(tag_unexp),
            "Parser ignores ! in all positions. Need: tag parsing in node properties, "
            "%TAG directive handling, verbatim tags (!!str etc). "
            "Largest single feature gap.",
        )
    )

    # Batch 2: Explicit keys
    ek_fails = [
        r
        for r in failures
        if "explicit-key" in r["tags"] and not (set(r["tags"]) & {"tag", "unknown-tag", "local-tag"})
    ]
    batches.append(
        (
            "Step 9: Explicit key support (?)",
            len(ek_fails),
            0,
            "Parser ignores ? as explicit key indicator. "
            "Need: ? detection in block/flow contexts, "
            "complex key support for multi-line keys.",
        )
    )

    # Batch 3: Error rejection (indentation)
    indent_unexp = [
        r for r in unexp if r["stage"] == "error" and "indent" in r["tags"]
    ]
    batches.append(
        (
            "Step 10a: Strict indentation validation",
            0,
            len(indent_unexp),
            "Parser accepts wrongly-indented YAML. "
            "Strengthen indent checking in block sequences/mappings.",
        )
    )

    # Batch 4: Error rejection (flow)
    flow_unexp = [
        r
        for r in unexp
        if r["stage"] == "error" and "flow" in r["tags"]
    ]
    batches.append(
        (
            "Step 10b: Strict flow collection validation",
            0,
            len(flow_unexp),
            "Parser accepts malformed flow sequences/mappings "
            "(missing commas, extra brackets, etc).",
        )
    )

    # Batch 5: Error rejection (quotes)
    quote_unexp = [
        r
        for r in unexp
        if r["stage"] == "error" and (set(r["tags"]) & {"double", "single"})
    ]
    batches.append(
        (
            "Step 10c: Strict quoted scalar validation",
            0,
            len(quote_unexp),
            "Parser accepts invalid quoted scalars "
            "(unclosed quotes, invalid escapes, etc).",
        )
    )

    # Batch 6: Error rejection (mapping/sequence structure)
    struct_unexp = [
        r
        for r in unexp
        if r["stage"] == "error"
        and ("mapping" in r["tags"] or "sequence" in r["tags"])
        and not (set(r["tags"]) & {"indent", "flow", "double", "single", "anchor", "alias", "directive", "tag", "comment", "folded", "literal", "footer", "header"})
    ]
    batches.append(
        (
            "Step 10d: Strict mapping/sequence validation",
            0,
            len(struct_unexp),
            "Parser accepts structurally invalid mappings/sequences.",
        )
    )

    # Batch 7: Comment handling
    comment_fails = [
        r
        for r in failures
        if "comment" in r["tags"]
        and not (set(r["tags"]) & {"tag", "unknown-tag", "explicit-key"})
    ]
    comment_unexp = [
        r for r in unexp if r["stage"] == "error" and "comment" in r["tags"]
    ]
    batches.append(
        (
            "Step 10e: Comment edge cases",
            len(comment_fails),
            len(comment_unexp),
            "Comment handling in various contexts (after flow, in plain scalars, etc).",
        )
    )

    # Batch 8: Escape sequences
    escape_fails = [r for r in failures if "unknown escape" in r["error"]]
    batches.append(
        (
            "Step 10f: Unicode escape sequences",
            len(escape_fails),
            0,
            "Parser doesn't handle some Unicode escape sequences in double-quoted scalars.",
        )
    )

    # Batch 9: Anchor/alias edge cases
    aa_fails = [
        r
        for r in failures
        if set(r["tags"]) & {"anchor", "alias"}
        and not (set(r["tags"]) & {"tag", "explicit-key"})
    ]
    aa_unexp = [
        r
        for r in unexp
        if r["stage"] == "error" and (set(r["tags"]) & {"anchor", "alias"})
    ]
    batches.append(
        (
            "Step 10g: Anchor/alias edge cases",
            len(aa_fails),
            len(aa_unexp),
            "Edge cases: anchor on explicit keys, aliases as mapping keys, "
            "double-anchor detection, etc.",
        )
    )

    # Print batches
    print()
    total_fail_fix = 0
    total_unexp_fix = 0
    for name, fail_fix, unexp_fix, desc in batches:
        total_fail_fix += fail_fix
        total_unexp_fix += unexp_fix
        total = fail_fix + unexp_fix
        print(f"  {name}")
        print(f"    Impact: {fail_fix} failures fixed, {unexp_fix} unexpected passes resolved ({total} total)")
        print(f"    {desc}")
        print()

    print(f"  Total addressable: {total_fail_fix}/{len(failures)} failures, {total_unexp_fix}/{len(unexp)} unexpected passes")

    # Current vs projected
    passed = len([r for r in rows if r["outcome"] == "pass"])
    total = len(rows)
    print(f"\n  Current: {passed}/{total} correct ({100*passed/total:.1f}%)")
    projected = passed + total_fail_fix + total_unexp_fix
    print(f"  Projected after all batches: ~{projected}/{total} correct (~{100*projected/total:.1f}%)")


def main():
    args = [a for a in sys.argv[1:] if not a.startswith("-")]
    html_path = args[0] if args else "docs/coverage-all.html"
    path = Path(html_path)
    if not path.exists():
        print(f"Error: {path} not found", file=sys.stderr)
        sys.exit(1)

    html = path.read_text()
    rows = parse_html(html)
    if not rows:
        print("Error: no test rows found", file=sys.stderr)
        sys.exit(1)

    analyze_failure_tokens(rows)
    analyze_missing_features(rows)
    analyze_unexpected_passes_detail(rows)
    generate_fix_batches(rows)


if __name__ == "__main__":
    main()
