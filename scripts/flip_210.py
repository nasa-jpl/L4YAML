#!/usr/bin/env python3
"""Run the `[210] l-yaml-stream` flip gate and report the DEFINITIONS it breaks
(DOCS item 230).

The gate itself is item 210's: tighten `SLYamlStream.implicitContinue` from
`GOpt SLAnyDocument` to `GOpt SLExplicitDocument`, build, and see what stops
compiling.  What breaks is the set of definitions that actually depend on the
looser reading, and item 210's rule is to **record definitions, not line
numbers**, because a re-indent moves the numbers and moves nothing else.

Until now the mapping from the build log's error locations to those
definitions was done by reading the log.  That is a number no instrument
re-derives, so the five names were re-typed at every item that ran the flip
(items 210 and 226-229 each carry a `flip.defs.txt` in their scratchpad and
none carries a generator).  This script is the generator; run against item
229's log it reproduces its five exactly.

    scripts/flip_210.py                    # run the gate end to end
    scripts/flip_210.py --map <build.log>  # just map an existing log

The gate is destructive while it runs — it edits `L4YAML/Surface/Document.lean`
in place — so it restores from its own backup in a `finally` and prints the
md5 both before and after.  A run that dies between the two leaves the backup
beside the source.
"""

from __future__ import annotations

import argparse
import hashlib
import os
import re
import shutil
import subprocess
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
DOC = ROOT / "L4YAML" / "Surface" / "Document.lean"
OLD = "GOpt SLAnyDocument s₂ s₃ →"
NEW = "GOpt SLExplicitDocument s₂ s₃ →"

#: `error: <file>:<line>:<col>: <msg>` is how Lake renders a Lean diagnostic.
#: The same shape item 228 corrected `decline_all_optional.py` for.
ERROR_LOC = re.compile(r"error: ([^ :]+\.lean):(\d+):(\d+):")

DECL_HEAD = re.compile(
    r"^(?:private |protected |@\[[^\]]*\]\s*)*"
    r"(?:lemma|theorem|def|abbrev|instance|structure|inductive) "
    r"([A-Za-z_][A-Za-z0-9_'!?.]*)")


def md5(path: Path) -> str:
    return hashlib.md5(path.read_bytes()).hexdigest()


def broken_definitions(log: str) -> tuple[list[str], int, list[str]]:
    """Map error LOCATIONS to the definitions that enclose them.

    Returns (definitions, number of distinct locations, complaints).  A
    location with no enclosing declaration is reported rather than dropped:
    an error inside a `run_cmd` or a module docstring has no definition to
    name, and silently discarding it would under-report the gate.
    """
    locs = {(m.group(1), int(m.group(2))) for m in ERROR_LOC.finditer(log)}
    defs: set[str] = set()
    complaints: list[str] = []
    for path, line in sorted(locs):
        src_path = ROOT / path
        if not src_path.exists():
            complaints.append(f"no such file: {path}")
            continue
        src = src_path.read_text().split("\n")
        for i in range(min(line, len(src)) - 1, -1, -1):
            m = DECL_HEAD.match(src[i])
            if m:
                defs.add(m.group(1))
                break
        else:
            complaints.append(f"no enclosing definition: {path}:{line}")
    return sorted(defs), len(locs), complaints


def report(log: str) -> int:
    defs, nlocs, complaints = broken_definitions(log)
    for d in defs:
        print(f"BROKEN {d}")
    for c in complaints:
        print(f"UNMAPPED {c}")
    print(f"COUNT {len(defs)} definitions from {nlocs} locations")
    return len(complaints)


def main() -> int:
    ap = argparse.ArgumentParser()
    ap.add_argument("--map", metavar="LOG",
                    help="map an existing build log instead of running the gate")
    ap.add_argument("--log", metavar="PATH", help="write the build log here")
    args = ap.parse_args()

    if args.map:
        return 1 if report(Path(args.map).read_text()) else 0

    before = md5(DOC)
    print(f"md5 before  {before}")
    src = DOC.read_text()
    if OLD not in src:
        sys.exit(f"the flip's target text is not in {DOC.relative_to(ROOT)}; "
                 "the production moved and this gate needs re-aiming")
    backup = DOC.with_suffix(".lean.flip-backup")
    shutil.copy(DOC, backup)
    try:
        DOC.write_text(src.replace(OLD, NEW))
        out = subprocess.run(["lake", "build"], cwd=ROOT,
                             capture_output=True, text=True)
        log = out.stdout + out.stderr
        if args.log:
            Path(args.log).write_text(log)
        if out.returncode == 0:
            print("THE FLIP BUILT CLEAN — the tightening costs nothing, which "
                  "is a finding and not a pass")
            return 1
        bad = report(log)
    finally:
        shutil.copy(backup, DOC)
        backup.unlink()
        after = md5(DOC)
        print(f"md5 after   {after}")
        if after != before:
            sys.exit("the restore did not restore; fix the source before "
                     "trusting anything else in this run")
        print("rebuilding so no later probe reads the flipped oleans...")
        subprocess.run(["lake", "build"], cwd=ROOT, capture_output=True, text=True)
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
