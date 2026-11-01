#!/usr/bin/env python3
"""Item 418's probe: the OWED TYPE at each decline whose writer HOLDS a chain over the projection.
Item 414's class table left 71 `PackAlt` declines; item 418 read the two largest writers site by
site and found three writes that decline a chain the writer already holds in a destructured
premise (`accum_block_on_closeThenBlock`'s `h_kslotUp` arm and its `h_explUp_chainD` argument,
both off `h_vslot`'s item-191 ancestor list; `accum_block_on_pendingBlock`'s `(h_kslot, h_kslotUp)`
catch-all with `h_kslot` held).  Pricing them means knowing what each owes against the held
witnesses: this script names the witnesses at each arm head, rewrites the decline into
`(by exact (⟨⟩ : Unit))` — a deliberate type mismatch whose error prints the goal — runs
`lake build L4YAML`, prints the owed types and restores `StreamAccum.lean` byte-identical (both
md5s printed).  Read-only in effect; never run it beside another `lake build`.

The sites are addressed by line and text AT THE REVISION THAT HOLDS THEM (`BASE_REV`, the merged
item 417 base), so the probe prices a REVISION: `--rev REV` takes `StreamAccum.lean` from
`git show REV:…`, patches that copy into the working tree, builds, restores the working tree's own
bytes, and refuses when any OTHER library file differs between REV and the working tree.
Example: `python3 scripts/flip_held_chains.py --rev 01a73090`."""
import argparse, hashlib, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
REL = "L4YAML/Proofs/Production/StreamAccum.lean"
SRC = ROOT / REL
BASE_REV = "01a73090"  # merged #191 (item 417): the revision whose line numbers SITES names
PROBE = "(by exact (⟨⟩ : Unit))"
SITES = {  # line: (expected text, replacement)
    # closeThenBlock, `-` landing: h_kslotUp's arm head names the held list, its hnk arm is probed
    28503: ("| Or.inl ⟨nv, _, _, _, _, _, _, _, _, _, Or.inl ⟨nsU, hkvU⟩⟩ =>",
            "| Or.inl ⟨nv, _, _, _, _, _, _, _, _, hkv, Or.inl ⟨nsU, hdomU, kvU⟩⟩ =>"),
    28507: ("Or.inr trivial", PROBE),
    # closeThenBlock, `?`/`:` landing: indicator_open_map's h_explUp_chainD argument
    28607: ("(Or.inr trivial) h_mcstep h_mcstep_ne", PROBE + " h_mcstep h_mcstep_ne"),
    # pendingBlock's landed `?`: the (h_kslot, h_kslotUp) catch-all with h_kslot named
    30616: ("| _, Or.inr _ => Or.inr trivial", "| hks, Or.inr _ => " + PROBE),
}
ap = argparse.ArgumentParser(description="price item 418's held-chain declines at a revision")
ap.add_argument("--rev", default=BASE_REV, help=f"revision holding the sites (default {BASE_REV})")
args = ap.parse_args()
git = lambda *a: subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
others = git("diff", "--quiet", args.rev, "--", "L4YAML", f":!{REL}")
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
for ln, (text, repl) in SITES.items():
    if text not in lines[ln - 1]:
        sys.exit(f"site moved: {args.rev}:{REL} line {ln} does not contain `{text}`")
    lines[ln - 1] = lines[ln - 1].replace(text, repl)
try:
    SRC.write_text("\n".join(lines))
    print(f"probe tree md5 {md5()[:12]}; building L4YAML …", flush=True)
    r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    errs = re.findall(r"error: L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): [Tt]ype mismatch.*?\n(.*?)(?=\n(?:error|warning|info|✖|✔|Build|\[)|\Z)", out, re.S)
    print(f"HELD-PROBE sites=3 mismatches={len(errs)} exit={r.returncode}")
    for ln, col, body in errs:
        print(f"--- site {ln}:{col}\n{body.strip()}\n")
    other = [l for l in out.splitlines() if "error:" in l and "ype mismatch" not in l]
    for l in other[:20]: print("OTHER", l[:200])
finally:
    SRC.write_bytes(orig)
    print(f"restored md5 {md5()[:12]} (orig {m0[:12]}) identical={md5() == m0}")
