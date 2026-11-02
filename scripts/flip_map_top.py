"""Price item 388's field (DOCS item 388): the `-` park's MAPPING-TOP route — when the park's
stack top is the enclosing MAPPING (a `-` at that mapping's own column pushed nothing, `a:⏎- b`),
a `:`/`?` landing at the park's column after its compact tail is that mapping's SIBLING
(`a:⏎-⏎c: 1`), whose route no frame of the park names (`h_lt` bounds them strictly below `n`):
    (h_mapTop : atSequenceIndent sc = false →
      ∃ ks, (∀ fr ∈ ks, fr.width < n) ∧ ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
        ∀ sp_end, SCompactSeqTail n sp_mid sp_end → ∀ sp_fin, SCompactMapTail n sp_end sp_fin →
        ResumeFrames (SLYamlStream sp_start) ks sp_fin)
stated OUTRIGHT (no `∨ True`), added to `PendingNode.pendingBlock` after `h_nodir`.  Births break on
the ctor's arity: the landed `closeThenBlock` birth must supply it from `h_valF` (`.blockOut`,
`valueLandedSeq`, the `.level` inversion) at `nv = k` and refute the premise at `nv < k` (the `-`
pushed a sequence); `pendingBlock`/`pendingBlockContent` births relay the old park's; a bare root `-`
refutes (pushed).  Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`,
classifies with `lake exe scripts-flip-census`, restores; md5 printed both sides.  FLOOR: one build.
`--dry` patches nothing; `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
OLD = "      (h_nodir : sc.allowDirectives = false)\n      -- **Item 167 — the ENCLOSING collection's tail**"
NEW = ("      (h_nodir : sc.allowDirectives = false)\n"
       "      (h_mapTop : atSequenceIndent sc = false →\n"
       "        ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < n) ∧\n"
       "        ∀ sp_mid : SurfPos, SBlockIndented n .blockIn sp_scan sp_mid →\n"
       "        ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →\n"
       "        ∀ sp_fin : SurfPos, SCompactMapTail n sp_end sp_fin →\n"
       "        ResumeFrames (SLYamlStream sp_start) ks sp_fin)\n"
       "      -- **Item 167 — the ENCLOSING collection's tail**")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text()
    if orig.count(OLD) != 1: sys.exit(f"expected 1 site, found {orig.count(OLD)}")
    print(f"md5 before: {before}\nsite: h_mapTop after h_nodir (line {orig[:orig.index(OLD)].count(chr(10)) + 1})")
    if dry: return
    SRC.write_text(orig.replace(OLD, NEW))
    if keep: print("kept"); return
    try:
        log = ROOT / "scratch/388-flip-map-top-build.log"; log.parent.mkdir(exist_ok=True)
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
