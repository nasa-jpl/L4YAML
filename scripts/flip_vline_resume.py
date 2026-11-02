#!/usr/bin/env python3
"""Restate the item-192 value-line chain's conclusion and report what breaks (DOCS item 371).

Every value-line pack in `StreamAccum.lean` — `pendingMapValue.h_kslot`/`h_explUp`,
the `pendingBlock*`/`pendingProps`/`pendingContent` relays, the key packs' chains,
`accum_block_on_closeThenBlock.h_vpack`, `colon_open_map_explicit.hvp`,
`ExplValueLine` — ends FUSED:

    ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →
    SLYamlStream sp_start sp_v

so after the explicit `:`'s value the mapping at `nv` is CLOSED: `? a⏎:⏎b: 1`
cannot continue `b: 1` as a sibling and the value park is born frameless
(item 370's exit (b)).  This flip restates the conclusion, in place, at every
two-line fused site, to the one-level resume

    ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v

(no new binder, no new disjunct — Rule 8's restatement, not item 320's (A)),
builds the LIBRARY (`lake build L4YAML`), resolves the errors to declarations with
`scripts-flip-census`, and restores the file (md5 printed both sides).  Round 1 is a
FLOOR: the build stops at the first failing module.

    scripts/flip_vline_resume.py            # price: edit, build, census, restore
    scripts/flip_vline_resume.py --keep     # apply the edit and stop (the item's first step)
    scripts/flip_vline_resume.py --dry      # list the sites only
"""
import hashlib, pathlib, re, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PREM = re.compile(r"SBlockIndented (\w+) \.blockOut sp_c (sp_[vw]) →\s*$")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.split("\n"); sites = []
    for i in range(len(lines) - 1):
        m = PREM.search(lines[i])
        if not m: continue
        nv, sp = m.group(1), m.group(2)
        concl = f"SLYamlStream sp_start {sp}"
        if concl in lines[i + 1] and "ResumeFrames" not in lines[i + 1]:
            lines[i + 1] = lines[i + 1].replace(concl, f"ResumeFrames (SLYamlStream sp_start) [FrameLevel.map {nv}] {sp}", 1)
            sites.append(i + 2)
    return "\n".join(lines), sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text()
    new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: {len(sites)}\n" + " ".join(map(str, sites)))
    if not sites:
        sys.exit("no fused value-line conclusion left to flip: the restatement is landed "
                 "(DOCS item 371), so a build here would price a no-op; the measured price "
                 "is the item's entry.  To re-price, check out the pre-371 tree first.")
    if dry: return
    SRC.write_text(new)
    if keep: print(f"kept; md5 now {md5(SRC)}"); return
    try:
        log = ROOT / "scratch/371-flip-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        if c.returncode != 0: sys.exit(f"scripts-flip-census exit={c.returncode}: {c.stderr.strip()}")
        print(c.stdout[-6000:]); print(c.stderr[-2000:], file=sys.stderr)
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'NOT RESTORED'})")
if __name__ == "__main__": main()
