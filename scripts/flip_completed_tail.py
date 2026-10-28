#!/usr/bin/env python3
"""Item 384 price instrument: `CompletedTail sc` WITHOUT its `∨ True` — the stale-tail face
that refutes the deeper landing in `closeThenBlock`'s `h_vslot` residue arm (item 383's stop).
Stage 1 flips `accum_block_on_closeThenBlock`'s own binder `h_tail139`; stage 2 flips every
`CompletedTail sc ∨ True` binder/field in StreamAccum.lean (the fixpoint's upper bound), so the
relays that merely pass a `∨ True` fact through are read too.  One `L4YAML` build per stage,
`flip_census.py` on its log, source restored (md5 both sides).  `--dry` lists sites; `--keep` leaves
the flipped tree in place (for the pay).  Never run concurrently with `lake build`."""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
NEEDLE = "CompletedTail sc ∨ True"
STAGE1_ANCHOR = "    (h_tail139 : CompletedTail sc ∨ True)\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text, stage):
    lines = text.splitlines(keepends=True); sites = []
    for i, l in enumerate(lines):
        if NEEDLE in l and not l.lstrip().startswith("--"):
            if stage == 1 and l != STAGE1_ANCHOR: continue
            lines[i] = l.replace(NEEDLE, "CompletedTail sc"); sites.append(i + 1)
    want = 1 if stage == 1 else None
    if want and len(sites) != want: sys.exit(f"stage 1 expected 1 site, matched {sites}")
    return "".join(lines), sites
def main():
    stage = 2 if "--stage" in sys.argv and sys.argv[sys.argv.index("--stage") + 1] == "2" else 1
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig, stage)
    print(f"stage {stage}; md5 before: {before}\nsites (`{NEEDLE}` → `CompletedTail sc`): {sites}")
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / f"scratch/384-flip-completed-tail-stage{stage}-build.log"; log.parent.mkdir(exist_ok=True)
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
