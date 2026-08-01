#!/usr/bin/env python3
"""CI gate: no orphan modules.

1. Every `L4YAML/**/*.lean` module must be transitively imported from the
   library root `L4YAML.lean` (textual `import` parsing — deliberately NOT
   importGraph env-loading: merging the full Proofs environment trips a
   duplicate equation-lemma error, see .github/workflows/test-coverage.yml).
2. Every `Tests/Reflections/*.lean` must be imported by the
   `Tests/Reflections.lean` index (a file missing from the index is never
   built by CI and can rot silently).
"""

import re
import sys
from pathlib import Path

IMPORT_RE = re.compile(r"^import\s+([A-Za-z0-9_.«»]+)", re.M)


def module_of(path: Path) -> str:
    return ".".join(path.with_suffix("").parts)


def imports_of(path: Path):
    return IMPORT_RE.findall(path.read_text())


def main() -> int:
    repo = Path(__file__).resolve().parent.parent
    failures = []

    # --- 1. library reachability from L4YAML.lean ---
    lib_files = sorted((repo / "L4YAML").rglob("*.lean"))
    on_disk = {module_of(f.relative_to(repo)): f for f in lib_files}
    seen, frontier = set(), ["L4YAML"]
    file_of = dict(on_disk)
    file_of["L4YAML"] = repo / "L4YAML.lean"
    while frontier:
        mod = frontier.pop()
        if mod in seen:
            continue
        seen.add(mod)
        f = file_of.get(mod)
        if f is None or not f.exists():
            continue
        for imp in imports_of(f):
            if imp == "L4YAML" or imp.startswith("L4YAML."):
                frontier.append(imp)
    orphans = sorted(set(on_disk) - seen)
    for mod in orphans:
        failures.append(f"orphan library module (unreachable from L4YAML.lean): "
                        f"{on_disk[mod].relative_to(repo)}")

    # --- 2. Tests/Reflections index completeness ---
    index = repo / "Tests" / "Reflections.lean"
    indexed = set(imports_of(index))
    for f in sorted((repo / "Tests" / "Reflections").glob("*.lean")):
        mod = f"Tests.Reflections.{f.stem}"
        if mod not in indexed:
            failures.append(f"unindexed reflection (add `import {mod}` to "
                            f"Tests/Reflections.lean): {f.relative_to(repo)}")

    if failures:
        print("\n".join(failures))
        print(f"error: {len(failures)} import-closure violations", file=sys.stderr)
        return 1
    print(f"OK: {len(on_disk)} library modules reachable from L4YAML.lean; "
          f"Tests/Reflections index complete ({len(indexed)} imports)")
    return 0


if __name__ == "__main__":
    sys.exit(main())
