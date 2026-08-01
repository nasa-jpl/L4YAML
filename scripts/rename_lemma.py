#!/usr/bin/env python3
"""theorem/lemma keyword tool for the L4YAML library.

Project policy (Blueprint/06-discipline.md): the `theorem` keyword is
reserved for the @[capstone]-tagged blueprint capstones; every other
proof uses `lemma` (provided by L4YAML/Init.lean).

Modes:
  --stats               count `theorem` keyword sites (whitelisted vs not)
  --check               exit 1 listing every non-whitelisted `theorem` site
  --apply               rewrite non-whitelisted `theorem` -> `lemma` in place

The scanner is comment-, string-, and char-literal-aware:
  * `/- -/` block comments nest (includes `/--` and `/-!` doc comments)
  * `--` line comments
  * `"..."` string literals (escape-aware, may span lines)
  * `'c'` char literals (only when `'` does not follow an identifier char,
    so `foo'` stays an identifier and `'"'` does not open a string)
A `theorem` token counts only in code, at a token boundary, and not
preceded by `.` or `` ` `` (so `Parser.Command.theorem` name literals and
docstring prose are never touched).

Whitelist file format (default scripts/capstones.txt): one
`relative/path.lean:name` per line; `#` comments; a trailing `*` in the
name is a prefix wildcard (`SIndent_*`).
"""

import argparse
import sys
from pathlib import Path

IDENT_CH = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ0123456789_'!?")
NAME_START = set("abcdefghijklmnopqrstuvwxyzABCDEFGHIJKLMNOPQRSTUVWXYZ_«")


def load_whitelist(path):
    entries = []
    for raw in Path(path).read_text().splitlines():
        line = raw.strip()
        if not line or line.startswith("#"):
            continue
        file_part, name = line.rsplit(":", 1)
        entries.append((file_part, name))
    return entries


def name_allowed(relpath, name, whitelist):
    for file_part, wname in whitelist:
        if file_part != relpath:
            continue
        if wname.endswith("*"):
            if name.startswith(wname[:-1]):
                return True
        elif name == wname:
            return True
    return False


def decl_name_after(text, i):
    """Identifier (possibly dot-qualified, possibly guillemet-quoted)
    starting at text[i]; returns (name, ok)."""
    parts = []
    while True:
        if i < len(text) and text[i] == "«":
            j = text.find("»", i + 1)
            if j == -1:
                return "", False
            parts.append(text[i + 1 : j])
            i = j + 1
        else:
            j = i
            while j < len(text) and text[j] in IDENT_CH:
                j += 1
            if j == i:
                return "", False
            parts.append(text[i:j])
            i = j
        if i < len(text) and text[i] == "." and i + 1 < len(text) and text[i + 1] in NAME_START:
            i += 1
            continue
        return ".".join(parts), True


def scan_file(text):
    """Yield (offset, name) for each `theorem` keyword site in code."""
    sites = []
    i, n = 0, len(text)
    depth = 0          # block-comment nesting
    in_line = False    # line comment
    in_str = False     # string literal
    while i < n:
        c = text[i]
        if in_line:
            if c == "\n":
                in_line = False
            i += 1
            continue
        if depth > 0:
            if text.startswith("/-", i):
                depth += 1
                i += 2
            elif text.startswith("-/", i):
                depth -= 1
                i += 2
            else:
                i += 1
            continue
        if in_str:
            if c == "\\":
                i += 2
            elif c == '"':
                in_str = False
                i += 1
            else:
                i += 1
            continue
        # normal code state
        if text.startswith("/-", i):
            depth = 1
            i += 2
            continue
        if text.startswith("--", i):
            in_line = True
            i += 2
            continue
        if c == '"':
            in_str = True
            i += 1
            continue
        if c == "'" and (i == 0 or text[i - 1] not in IDENT_CH):
            # char literal: '\x' or 'x'
            j = i + 1
            if j < n and text[j] == "\\":
                j += 2
            else:
                j += 1
            if j < n and text[j] == "'":
                i = j + 1
                continue
            i += 1
            continue
        if text.startswith("theorem", i):
            prev = text[i - 1] if i > 0 else "\n"
            nxt = text[i + 7] if i + 7 < n else "\n"
            if prev not in IDENT_CH and prev not in ".`" and nxt in " \t\n":
                j = i + 7
                while j < n and text[j] in " \t\n":
                    j += 1
                name, ok = decl_name_after(text, j)
                if ok:
                    sites.append((i, name))
                i += 7
                continue
        i += 1
    return sites


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("roots", nargs="+", help="files or directories to scan")
    ap.add_argument("--whitelist", default="scripts/capstones.txt")
    mode = ap.add_mutually_exclusive_group(required=True)
    mode.add_argument("--stats", action="store_true")
    mode.add_argument("--check", action="store_true")
    mode.add_argument("--apply", action="store_true")
    args = ap.parse_args()

    repo = Path.cwd()
    whitelist = load_whitelist(args.whitelist)

    files = []
    for r in args.roots:
        p = Path(r)
        files.extend(sorted(p.rglob("*.lean")) if p.is_dir() else [p])

    kept = renamed = 0
    violations = []
    for f in files:
        rel = f.relative_to(repo).as_posix() if f.is_absolute() else f.as_posix()
        text = f.read_text()
        sites = scan_file(text)
        edits = []
        for off, name in sites:
            if name_allowed(rel, name, whitelist):
                kept += 1
            else:
                line = text.count("\n", 0, off) + 1
                violations.append((rel, line, name))
                edits.append(off)
        if args.apply and edits:
            out, prev = [], 0
            for off in edits:
                out.append(text[prev:off])
                out.append("lemma")
                prev = off + len("theorem")
            out.append(text[prev:])
            f.write_text("".join(out))
            renamed += len(edits)

    if args.stats:
        print(f"theorem keyword sites: {kept + len(violations)} "
              f"(whitelisted: {kept}, other: {len(violations)}) "
              f"in {len(files)} files")
        return 0
    if args.check:
        if violations:
            for rel, line, name in violations:
                print(f"{rel}:{line}: non-capstone `theorem {name}` "
                      f"(use `lemma`, or whitelist in {args.whitelist})")
            print(f"error: {len(violations)} non-capstone `theorem` sites", file=sys.stderr)
            return 1
        print(f"OK: all {kept} `theorem` sites are whitelisted capstones")
        return 0
    if args.apply:
        print(f"renamed {renamed} `theorem` sites to `lemma`; kept {kept} capstones")
        return 0


if __name__ == "__main__":
    sys.exit(main())
