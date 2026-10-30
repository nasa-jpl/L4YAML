#!/usr/bin/env python3
"""The PACK residue's declines classed by the existential index each declined field carries
(item 403).  Read-only: joins three pinned/derived readings, runs nothing.

* `Tests/Guards/Proofs/OrTrueAudit.lean` — `expectedPositions` (which `∨` positions have a
  `PackAlt`/`PackAltG` alternative) and `expectedSupply` (the `DECLINE=n` edges at each
  position: the `Or.inr trivial` writers the audit found);
* `L4YAML/Proofs/Production/StreamAccum.lean` — the binder of each such field, read by regex
  from its carrier constructor or lemma telescope, classed by the ghost datum its informative
  side quantifies: `ks` (a `List FrameLevel`, with or without a scalar width beside it), `ns` (a `List Nat` chain or a
  bare `∃ nv : Nat` slot — the value-line family), `pack` (both: the key packs and the flow key route),
  `scalar` (an `∃` over a `Nat` width only, no list), `none` (no `∃` at all);
* optionally `--tsv residue.tsv` from `scripts/pack_flip_census.py --alt refused --tsv …` —
  the residue's DECLINE sites, split into `∨`-position sites and bare `PackAlt` lemma
  parameters (`h_alt := … trivial`, `(fun _ => trivial)`), which the audit does not see.

Prints one `RESIDUE-CLASSES` line (the pin DOCS quotes) and the per-field rows.
"""
import argparse, csv, re, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
AUDIT = ROOT / "Tests/Guards/Proofs/OrTrueAudit.lean"
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
NS = "L4YAML.Proofs.StreamAccum."


def lean_list(text, name):
    m = re.search(r"def " + name + r" : List String :=\s*\[(.*?)\n  \]", text, re.S)
    return re.findall(r'"([^"]*)"', m[1])


def binder_text(src, decl, field):
    """The `(field : …)` binder of `decl`, whether `decl` is a lemma or a constructor arm."""
    leaf = decl.split(".")[-1]
    heads = [m.end() for m in re.finditer(r"\n(?:public |private )?(?:lemma|theorem|def) " + re.escape(leaf) + r"\b", src)]
    heads += [m.end() for m in re.finditer(r"\n\s*\| " + re.escape(leaf) + r"\b", src)]
    for m in re.finditer(r"\nstructure " + re.escape(decl.split(".")[0]) + r"\b.*?\n(?=\S)", src, re.S):
        f = re.search(r"\n  " + re.escape(field) + r" :(.*?)(?=\n  \w+ :|\n\S|$)", m[0], re.S)
        if f:
            return "(" + field + " :" + f[1] + ")"
    for h in heads:
        body = src[h:h + 40000]
        i = body.find("(" + field + " :")
        if i < 0:
            continue
        depth, j = 0, i
        while j < len(body):
            depth += body[j] == "("
            depth -= body[j] == ")"
            if depth == 0:
                break
            j += 1
        return body[i:j + 1]
    return ""


def classify(binder):
    informative = binder  # the alternative names no list; the search strings read only the informative side
    has_ks = "List FrameLevel" in informative or "List IndentStackCover.FrameLevel" in informative
    has_chain = "List Nat" in informative
    has_slot = re.search(r"∃ \(?(?:ne )?nv\b", informative) is not None
    if has_ks and has_chain:
        return "pack"
    if has_ks:
        return "ks"
    if has_chain or has_slot:
        return "ns"
    if "∃" in informative:
        return "scalar"
    return "none"


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--tsv", type=Path, default=None)
    args = ap.parse_args()
    audit = AUDIT.read_text()
    src = SRC.read_text()
    positions = lean_list(audit, "expectedPositions")
    supply = lean_list(audit, "expectedSupply")
    pack_fields = {}
    for p in positions:
        m = re.match(r"(\S+) (top|nested) ∨ (PackAlt\S*)", p)
        if m:
            pack_fields.setdefault(m[1], m[3])
    rows, totals = [], {}
    for s in supply:
        key = s.split(" ")[0]
        if key not in pack_fields:
            continue
        d = re.search(r"DECLINE=(\d+)", s)
        n = int(d[1]) if d else 0
        m = re.match(r"(.*?)\[(\d+|ret)\]\.?(\S*)", key[len(NS):] if key.startswith(NS) else key)
        if not m:
            continue
        decl, field = m[1], m[3]
        if field == "":
            cls = "conclusion"
        else:
            b = binder_text(src, decl, field)
            cls = classify(b) if b else "unread"
        rows.append((cls, n, key[len(NS):] if key.startswith(NS) else key, s.split(" ", 1)[1]))
        totals[cls] = totals.get(cls, 0) + n
    rows.sort(key=lambda r: (r[0], -r[1], r[2]))
    for cls, n, key, rest in rows:
        print(f"  {cls:10s} {n:3d}  {key}  {rest}")
    unsupplied = [k[len(NS):] for k in pack_fields if not any(s.startswith(k + " ") for s in supply)]
    edges = sum(totals.values())
    line = (f"RESIDUE-CLASSES positions={sum(1 for p in positions if '∨ PackAlt' in p)} "
            f"fields={len(pack_fields)} declineEdges={edges} "
            + " ".join(f"{k}={totals.get(k, 0)}" for k in ("ns", "ks", "pack", "scalar", "none", "unread"))
            + f" unsuppliedFields={len(unsupplied)}")
    if args.tsv:
        sites = [r for r in csv.reader(args.tsv.open(), delimiter="\t") if r[3] == "DECLINE"]
        bare = sum(1 for r in sites if "h_alt :=" in r[6] or "fun _ => trivial" in r[6])
        line += f" sites={len(sites)} orSites={len(sites) - bare} bareParamSites={bare}"
    print(line)
    print("  unsupplied PackAlt fields:", ", ".join(unsupplied))


if __name__ == "__main__":
    main()
