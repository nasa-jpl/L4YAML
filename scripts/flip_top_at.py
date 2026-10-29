"""Price item 387's field (DOCS item 387): the `-` park's stack TOP stands at the park's column.
The mandated shape ("the top IS the sequence the `-` pushed") is refuted by `a:⏎- b` — a `-` at
the mapping's own column pushes nothing (`pushSequenceIndent` guards `col > currentIndent`) and
the top stays the MAPPING at `n` — so the field priced here is the honest one:
    (h_top_at : ∃ e : IndentEntry, sc.indents.back? = some e ∧ e.column = (n : Int))
added to `PendingNode.pendingBlock` right after `h_park_top`.  Births break on the ctor's arity
(each must read the top off its `-` dispatch), the dispatcher's three `pendingBlock` patterns on
the field count.  Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`,
classifies with `scripts/flip_census.py`, restores; md5 printed both sides.  FLOOR: one build.
`--dry` patches nothing; `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
OLD = "      (h_park_top : sc.currentIndent ≤ (n : Int))\n"
NEW = OLD + "      (h_top_at : ∃ e : IndentEntry, sc.indents.back? = some e ∧ e.column = (n : Int))\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text()
    if orig.count(OLD) != 1: sys.exit(f"expected 1 site, found {orig.count(OLD)}")
    print(f"md5 before: {before}\nsite: h_top_at after h_park_top (line {orig[:orig.index(OLD)].count(chr(10)) + 1})")
    if dry: return
    SRC.write_text(orig.replace(OLD, NEW))
    if keep: print("kept"); return
    try:
        log = ROOT / "scratch/387-flip-top-at-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__":
    main()
