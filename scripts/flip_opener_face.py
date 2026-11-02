"""Price item 376's SECOND design — the decline face on the OPENERS' CONCLUSIONS instead of
the parks' route field: `colon_open_map`, `question_open_map` and
`accum_block_on_closeThenBlock` conclude `(∃ … ∧ ScannerSurfCorr s' sp_scan') ∨ PackAlt s'`,
so their callers must match the disjunction (the breaks are the ring that has to sink the
decline).  `flowKeyRoute_of_root` already concludes `… ∨ True` and `accum_flow_open_depth0`
concludes the step tuple, so neither is flipped here (DOCS item 376 says why).

Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`lake exe scripts-flip-census`, restores; md5 printed both sides.  FLOOR: one build of the library;
guard modules behind it unmeasured.  `--dry` patches nothing; `--keep` leaves the patch.
"""
import hashlib, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
OPENERS = ("colon_open_map", "question_open_map", "accum_block_on_closeThenBlock")
TAIL = "      ScannerSurfCorr s' sp_scan' := by\n"

def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()

def patch(text):
    lines = text.splitlines(keepends=True); n = 0
    for i, l in enumerate(lines):
        if any(l.startswith(f"lemma {o} ") or l.rstrip("\n") == f"lemma {o}" for o in OPENERS):
            j = i
            while not lines[j].rstrip("\n").endswith(":= by"): j += 1
            if lines[j] != TAIL: sys.exit(f"{l.strip()}: conclusion tail is not the park tuple; refusing")
            k = j
            while not lines[k].lstrip().startswith("∃ sp_gram'"): k -= 1
            lines[k] = lines[k].replace("∃ sp_gram'", "(∃ sp_gram'", 1)
            lines[j] = "      ScannerSurfCorr s' sp_scan') ∨ PackAlt s' := by\n"; n += 1
    if n != 3: sys.exit(f"expected 3 openers, patched {n}")
    return "".join(lines)

def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    if "ScannerSurfCorr s' sp_scan') ∨ PackAlt s' := by" in SRC.read_text():
        sys.exit("the opener face is already in place: priced/landed, see DOCS item 376")
    before = md5(SRC); orig = SRC.read_text(); new = patch(orig)
    print(f"md5 before: {before}\nsites: 3 opener conclusions ({', '.join(OPENERS)}) take `∨ PackAlt s'`")
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/376-flip-opener-face-build.log"; log.parent.mkdir(exist_ok=True)
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
