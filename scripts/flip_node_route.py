#!/usr/bin/env python3
"""Item 383 price instrument (design (a′), owner's ruling 2026-10-28): the ENTRY-shaped
NODE ROUTE as a third arm on the three openers' `h_res_land` binders —
  ∨ (∀ s₁ s₂ sp_end, SIndent k sp_land s₁ → SBlockMapEntry k s₁ s₂ → SCompactMapTail k s₂ sp_end
       → SLYamlStream sp_start sp_end)
— inserted before the `∨ True`.  Changing only the binders breaks every PRODUCER
(`Or.inr trivial : _ ∨ True` no longer typechecks against the three-armed type) and every
CONSUMER (the openers' `rcases`), so ONE build of `L4YAML` reads the whole roster.
Read-only: edits StreamAccum.lean, builds, runs scripts/flip_census.py, restores; md5 both sides.
`--dry` lists the sites without editing; `--keep` leaves the flipped tree (for the pay)."""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
BINDER = "    (h_res_land : (∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < k) ∧\n"
TAIL_OLD = "        ResumeFrames (SLYamlStream sp_start) ks sp_end) ∨ True)\n"
TAIL_NEW = ("        ResumeFrames (SLYamlStream sp_start) ks sp_end) ∨\n"
            "      (∀ (s₁ s₂ sp_end : SurfPos), SIndent k sp_land s₁ → SBlockMapEntry k s₁ s₂ →\n"
            "        SCompactMapTail k s₂ sp_end → SLYamlStream sp_start sp_end) ∨ True)\n")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True); sites = []
    for i, l in enumerate(lines):
        if l == BINDER and lines[i + 2] == TAIL_OLD:
            lines[i + 2] = TAIL_NEW; sites.append(i + 1)
    if len(sites) != 3: sys.exit(f"expected 3 opener binders, matched {sites}")
    return "".join(lines), sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites (h_res_land binders): {sites}")
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/383-flip-node-route-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__": main()
