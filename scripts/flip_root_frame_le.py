#!/usr/bin/env python3
"""Price item 391's option (α) (DOCS item 391): frames that may name the park's OWN level.

`pendingMapValue.h_closeF` bounds its frame list (`h_frames` carries no width bound: its list is bounded by `Floor` alone) by `fr.width < n` (strictly below the
park's level), and `accum_block_on_closeThenBlock.h_valF` / `deeperLandingResume` relay that bound as
`fr.width < nv`.  Option (α) widens all three to `≤`, so a root park may carry `FrameLevel.map 0` and the
root sibling (`a: 1⏎b: 2`) takes the openers' resume arm instead of the `[211]` fallback.  Read-only:
patch, one `lake build L4YAML` (a FLOOR), `lake exe scripts-flip-census`, restore; md5 both sides.
`--dry` patches nothing; `--keep` leaves the patch.  Refuses a dirty `StreamAccum.lean`.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
CLOSEF = "      (h_closeF : (∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < n) ∧\n"
FRAMES_HEAD = "      (h_frames : (∃ ks : List FrameLevel,\n"
VALF = "    (h_valF : (∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < nv) ∧\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True); out = []; sites = []; ctor = None; want_frames = False
    for i, l in enumerate(lines):
        if l.startswith("  | ") and not l.startswith("  | ."): ctor = l.split()[1]
        if ctor == "pendingMapValue" and l == CLOSEF:
            l = l.replace("fr.width < n)", "fr.width ≤ n)"); sites.append((i + 1, "pendingMapValue.h_closeF"))
        elif l == VALF:
            l = l.replace("fr.width < nv)", "fr.width ≤ nv)"); sites.append((i + 1, "h_valF"))
        out.append(l)
    if len(sites) != 3: sys.exit(f"expected 3 sites, matched {sites}")
    return "".join(out), sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for ln, n in sites))
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/391-flip-root-frame-le-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__":
    main()
