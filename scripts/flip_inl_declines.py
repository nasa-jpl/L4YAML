#!/usr/bin/env python3
"""Item 415's probe: the OWED TYPE at each statement-shaped `| Or.inl … => Or.inr trivial` decline.
The 14 sites (item 414's residue TSV, class `Or.inl`) are the arms where the upstream alternative
is INFORMATIVE and the site still declines.  Pricing them means knowing what each owes: this
script rewrites each site's `Or.inr trivial` into `(by exact (⟨⟩ : Unit))` — a deliberate type
mismatch whose error message prints the goal — names the arm's witnesses so the message can be
read against them, runs `lake build L4YAML`, collects the 14 expected types, and restores
`StreamAccum.lean` byte-identical (both md5s printed).  Read-only in effect; never run it beside
another `lake build`.

The 14 sites are addressed by line number and text AT THE REVISION THAT HOLDS THEM (`BASE_REV`,
the merged item 414 base — item 415 paid seven of them, so the paid tree no longer has the rows).
The probe therefore prices a REVISION, not the checkout: `--rev REV` (default `BASE_REV`) takes
`StreamAccum.lean` from `git show REV:…`, patches that copy into the working tree, builds, and
restores the working tree's own bytes.  It refuses when any OTHER library file differs between
REV and HEAD (the base file would then compile against a library it was not written for); use a
`git worktree` of REV in that case.  Example: `python3 scripts/flip_inl_declines.py --rev 73042a01`."""
import argparse, hashlib, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
REL = "L4YAML/Proofs/Production/StreamAccum.lean"
SRC = ROOT / REL
BASE_REV = "73042a01"  # merged #188 (item 414): the revision whose line numbers SITES names
SITES = {  # line: (expected text, named replacement of the arm head)
    40379: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40396: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40503: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40520: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40624: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40641: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    38182: ("| Or.inl ⟨sp_q, h_qlit, route, _⟩ => Or.inr trivial", "| Or.inl ⟨sp_q, h_qlit, route, h_chainUp⟩ => "),
    38372: ("| Or.inl ⟨sp_q, h_qlit, route, _⟩ => Or.inr trivial", "| Or.inl ⟨sp_q, h_qlit, route, h_chainUp⟩ => "),
    38467: ("| Or.inl ⟨sp_q, h_qlit, route, _⟩ => Or.inr trivial", "| Or.inl ⟨sp_q, h_qlit, route, h_chainUp⟩ => "),
    37461: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    27801: ("| Or.inl _, Or.inr _ => Or.inr trivial", "| Or.inl h_own, Or.inr h_altUp => "),
    27844: ("| Or.inl ⟨nsU, _, kvU⟩ => Or.inr trivial", "| Or.inl ⟨nsU, h_domU, kvU⟩ => "),
    24659: ("| Or.inl ⟨nv, _, _, contV⟩ => Or.inr trivial", "| Or.inl ⟨nv, h_ltV, h_covV, contV⟩ => "),
    14872: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
}
PROBE = "(by exact (⟨⟩ : Unit))"
ap = argparse.ArgumentParser(description="price the 14 Or.inl declines of item 415 at a revision")
ap.add_argument("--rev", default=BASE_REV, help=f"revision holding the sites (default {BASE_REV})")
args = ap.parse_args()
git = lambda *a: subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
others = git("diff", "--quiet", args.rev, "--", "L4YAML", f":!{REL}")  # REV vs the WORKING TREE: uncommitted edits count
if others.returncode != 0:
    sys.exit(f"library files other than {REL} differ between {args.rev} and the working tree; "
             f"run the probe in a `git worktree` of {args.rev} instead")
shown = git("show", f"{args.rev}:{REL}")
if shown.returncode != 0:
    sys.exit(f"cannot read {REL} at {args.rev}: {shown.stderr.strip()}")
md5 = lambda: hashlib.md5(SRC.read_bytes()).hexdigest()
orig = SRC.read_bytes(); m0 = md5()
lines = shown.stdout.split("\n")
print(f"pricing {REL} at {args.rev} (working tree md5 {m0[:12]})", flush=True)
for ln, (text, head) in SITES.items():
    if text not in lines[ln - 1]:
        sys.exit(f"site moved: {args.rev}:{REL} line {ln} does not contain `{text}`")
    lines[ln - 1] = lines[ln - 1].replace(text, head + PROBE)
try:
    SRC.write_text("\n".join(lines))
    print(f"probe tree md5 {md5()[:12]}; building L4YAML …", flush=True)
    r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    (ROOT / "scratch").mkdir(exist_ok=True)
    errs = re.findall(r"error: L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): [Tt]ype mismatch.*?\n(.*?)(?=\n(?:error|warning|info|✖|✔|Build|\[)|\Z)", out, re.S)
    print(f"INL-PROBE sites={len(SITES)} mismatches={len(errs)} exit={r.returncode}")
    for ln, col, body in errs:
        print(f"--- site {ln}:{col}\n{body.strip()}\n")
finally:
    SRC.write_bytes(orig)
    print(f"restored md5 {md5()[:12]} (orig {m0[:12]}) identical={md5() == m0}")
