#!/usr/bin/env python3
"""Generate HTML reports from test result data.

Usage: python3 scripts/generate-test-reports.py RESULTS_DIR

Generates:
  - cross-lang-comparison.html  (from cross-lang-results.json)
  - python-ffi-tests.html       (from JUnit XML files)
"""
import json
import sys
import xml.etree.ElementTree as ET
from pathlib import Path
import html as htmlmod


def generate_cross_lang_html(results_dir: Path) -> None:
    results_file = results_dir / "cross-lang-results.json"
    out = results_dir / "cross-lang-comparison.html"

    if not results_file.is_file():
        print("No cross-lang-results.json found, skipping")
        return

    data = json.loads(results_file.read_text())
    backends = ["lean", "c", "python", "rust"]
    presets = ["unlimited", "default", "strict", "permissive", "safe_tags"]

    parts = [
        "<!DOCTYPE html>",
        '<html lang="en"><head><meta charset="utf-8">',
        "<title>Cross-Language yaml-test-suite Comparison</title>",
        "<style>",
        "body{font-family:system-ui,sans-serif;margin:2em;background:#f8f9fa}",
        "h1{color:#1a1a2e} h2{color:#16213e;margin-top:1.5em}",
        "table{border-collapse:collapse;margin:1em 0}",
        "th,td{border:1px solid #dee2e6;padding:6px 14px;text-align:right}",
        "th{background:#343a40;color:#fff;text-align:center}",
        "td:first-child{text-align:left;font-weight:bold}",
        ".match{background:#d4edda;color:#155724}",
        ".mismatch{background:#f8d7da;color:#721c24}",
        ".summary{font-size:1.1em;margin:1em 0}",
        "</style></head><body>",
        "<h1>Cross-Language yaml-test-suite Comparison</h1>",
        "<p>All four backends (Lean, C, Python, Rust) run the same yaml-test-suite "
        "test cases through the verified parser via their respective FFI layers.</p>",
    ]

    all_match = True
    parts.append("<h2>Results by Limit Preset</h2>")
    parts.append(
        "<table><tr><th>Preset</th><th>Passed</th><th>Failed</th>"
        "<th>Skipped</th><th>Total</th><th>Backends Match?</th></tr>"
    )
    for preset in presets:
        if preset not in data:
            continue
        vals = [
            tuple(data[preset][b].values())
            for b in backends
            if b in data[preset]
        ]
        match = len(set(vals)) == 1
        if not match:
            all_match = False
        css = "match" if match else "mismatch"
        icon = "\u2713" if match else "\u2717"
        p, f, s, t = vals[0]
        parts.append(
            f'<tr><td>{htmlmod.escape(preset)}</td>'
            f"<td>{p}</td><td>{f}</td><td>{s}</td><td>{t}</td>"
            f'<td class="{css}">{icon} {"All identical" if match else "MISMATCH"}</td></tr>'
        )
    parts.append("</table>")

    # Per-backend detail table
    parts.append("<h2>Full Matrix (Backend \u00d7 Preset)</h2>")
    parts.append("<table><tr><th>Backend</th>")
    for preset in presets:
        parts.append(f"<th>{htmlmod.escape(preset)}</th>")
    parts.append("</tr>")
    for backend in backends:
        parts.append(f"<tr><td>{htmlmod.escape(backend)}</td>")
        for preset in presets:
            if preset in data and backend in data[preset]:
                d = data[preset][backend]
                parts.append(f'<td>{d["passed"]}/{d["failed"]}/{d["skipped"]}</td>')
            else:
                parts.append("<td>\u2014</td>")
        parts.append("</tr>")
    parts.append("</table>")

    color = "match" if all_match else "mismatch"
    icon = "\u2713" if all_match else "\u2717"
    msg = (
        "All backends produce identical results for every preset"
        if all_match
        else "Backend mismatch detected!"
    )
    parts.append(f'<p class="summary {color}">{icon} {msg}</p>')
    parts.append("</body></html>")
    out.write_text("\n".join(parts))
    print(f"Generated {out}")


def generate_python_ffi_html(results_dir: Path) -> None:
    out = results_dir / "python-ffi-tests.html"
    sections = []
    for junit_file, title in [
        (results_dir / "python-ffi-junit.xml", "Python FFI Integration Tests (Tests/)"),
        (results_dir / "python-package-junit.xml", "Python Package Tests (python/tests/)"),
    ]:
        if not junit_file.is_file():
            continue
        tree = ET.parse(str(junit_file))
        root = tree.getroot()
        suites = root.findall(".//testsuite") if root.tag != "testsuite" else [root]
        rows = []
        total = passed = failed = skipped = 0
        for suite in suites:
            for tc in suite.findall("testcase"):
                name = tc.get("classname", "") + "." + tc.get("name", "")
                time_s = tc.get("time", "0")
                fail_el = tc.find("failure")
                skip_el = tc.find("skipped")
                total += 1
                if fail_el is not None:
                    status, css, _ = "FAIL", "fail", (failed := failed + 1)
                elif skip_el is not None:
                    status, css, _ = "SKIP", "skip", (skipped := skipped + 1)
                else:
                    status, css, _ = "PASS", "pass", (passed := passed + 1)
                rows.append((name, status, css, time_s))
        sections.append((title, rows, total, passed, failed, skipped))

    if not sections:
        print("No JUnit XML files found, skipping Python FFI HTML report")
        return

    parts = [
        "<!DOCTYPE html>",
        '<html lang="en"><head><meta charset="utf-8">',
        "<title>Python API Test Results</title>",
        "<style>",
        "body{font-family:system-ui,sans-serif;margin:2em;background:#f8f9fa}",
        "h1{color:#1a1a2e} h2{color:#16213e;margin-top:2em}",
        "table{border-collapse:collapse;width:100%;margin:1em 0}",
        "th,td{border:1px solid #dee2e6;padding:6px 12px;text-align:left}",
        "th{background:#343a40;color:#fff}",
        ".pass{background:#d4edda;color:#155724}",
        ".fail{background:#f8d7da;color:#721c24}",
        ".skip{background:#fff3cd;color:#856404}",
        ".summary{font-size:1.1em;margin:0.5em 0}",
        "</style></head><body>",
        "<h1>Python API Test Results</h1>",
    ]
    grand_total = grand_passed = grand_failed = grand_skipped = 0
    for title, rows, total, passed, failed, skipped in sections:
        grand_total += total
        grand_passed += passed
        grand_failed += failed
        grand_skipped += skipped
        parts.append(f"<h2>{htmlmod.escape(title)}</h2>")
        parts.append(
            f'<p class="summary">Total: {total} &mdash; '
            f'<span class="pass">Passed: {passed}</span> &middot; '
            f'<span class="fail">Failed: {failed}</span> &middot; '
            f'<span class="skip">Skipped: {skipped}</span></p>'
        )
        parts.append("<table><tr><th>Test</th><th>Status</th><th>Time (s)</th></tr>")
        for name, status, css, time_s in rows:
            parts.append(
                f'<tr><td>{htmlmod.escape(name)}</td>'
                f'<td class="{css}">{status}</td>'
                f"<td>{htmlmod.escape(time_s)}</td></tr>"
            )
        parts.append("</table>")

    parts.append("<hr>")
    color = "pass" if grand_failed == 0 else "fail"
    parts.append(
        f'<p class="summary {color}">Grand Total: {grand_total} &mdash; '
        f"Passed: {grand_passed}, Failed: {grand_failed}, "
        f"Skipped: {grand_skipped}</p>"
    )
    parts.append("</body></html>")
    out.write_text("\n".join(parts))
    print(f"Generated {out} ({grand_total} tests)")


def main() -> None:
    if len(sys.argv) < 2:
        print(f"Usage: {sys.argv[0]} RESULTS_DIR", file=sys.stderr)
        sys.exit(1)
    results_dir = Path(sys.argv[1])
    generate_cross_lang_html(results_dir)
    generate_python_ffi_html(results_dir)


if __name__ == "__main__":
    main()
