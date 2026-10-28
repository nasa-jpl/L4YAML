#!/usr/bin/env python3
"""Item 380 pricing instrument (PRICE BEFORE PROVING): the ROOT FRAME at the births.
Question (item 379's NEXT): if every frameless park birth — `Or.inl ⟨[], fun _ h => absurd h
(List.not_mem_nil), …⟩` and `⟨[], fun _ hm => (List.not_mem_nil hm).elim⟩` in `StreamAccum`,
the frames lane with NOTHING below the entry's level — carried the root level instead,
`[FrameLevel.map 0]`, so that the accepted root sibling (`a: 1⏎b: 2`, Priority 44) found its
level in the frames and took the resume arm, which declarations break and where?  The width
proof `h_lt : ∀ fr ∈ ks, fr.width < k` is sorried at every birth (it is the Rule-8 question:
at a root birth `k = 0` it asks `0 < 0`), so the build reads the CONSUMERS of the list — the
F-routes whose conclusions end in `ResumeFrames … [] sp_e` and whatever destructures them.
Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML` once (a FLOOR),
classifies with `scripts/flip_census.py`, restores; md5 printed both sides.  `--dry` edits
nothing; `--keep` leaves the flipped tree.  Refuses a dirty StreamAccum.  Reading recorded in
DOCS item 380.
"""
import hashlib, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
A1 = "⟨[], fun _ h => absurd h (List.not_mem_nil),"
A2 = "⟨[], fun _ hm => (List.not_mem_nil hm).elim⟩"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean not clean; refusing to flip")
    before = md5(SRC); old = SRC.read_text()
    n1, n2 = old.count(A1), old.count(A2)
    new = old.replace(A1, "⟨[FrameLevel.map 0], sorry,").replace(A2, "⟨[FrameLevel.map 0], sorry⟩")
    print(f"md5 before: {before}\nsites: {n1} frames-lane births + {n2} cover-lane births = {n1 + n2} (h_lt sorried at each)")
    if dry or n1 + n2 == 0: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/380-flip-root-frames-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(old)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__": main()
