"""Price item 389's field on BOTH `-` parks (DOCS item 389): `h_mapTop`, the enclosing MAPPING's
sibling route when the park's stack TOP is that mapping (a `-` at the mapping's own column pushed
nothing, `a:⏎- b`), stated OUTRIGHT and added after `h_nodir` to `PendingNode.pendingBlock` AND
`PendingNode.pendingBlockContent` (the content park born from a `-` park must RELAY it, item 389's
reading of `flip_map_top.py`'s single-ctor price).  The premise reads the TOP's kind, not
`atSequenceIndent sc` — the park's `sc.col` is `n + 1`, so that predicate is false at every park:
    (h_mapTop : (∃ e, sc.indents.back? = some e ∧ e.isSequence = false) →
      ∃ ks, (∀ fr ∈ ks, fr.width < n) ∧ ∀ sp_mid, SBlockIndented n .blockIn sp_scan sp_mid →
        ∀ sp_end, SCompactSeqTail n sp_mid sp_end → ∀ sp_fin, SCompactMapTail n sp_end sp_fin →
        ResumeFrames (SLYamlStream sp_start) ks sp_fin)
Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`lake exe scripts-flip-census`, restores; md5 printed both sides.  FLOOR: one build.  `--dry` patches
nothing; `--keep` leaves the patch in place; `--one` patches `pendingBlock` only (item 388's shape
with the corrected premise).
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PREM = "      (h_mapTop : (∃ e, sc.indents.back? = some e ∧ e.isSequence = false) →\n"
FIELDS = {
    "pendingBlock": PREM
        + "        ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < n) ∧\n"
        + "        ∀ sp_mid : SurfPos, SBlockIndented n .blockIn sp_scan sp_mid →\n"
        + "        ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →\n"
        + "        ∀ sp_fin : SurfPos, SCompactMapTail n sp_end sp_fin →\n"
        + "        ResumeFrames (SLYamlStream sp_start) ks sp_fin)\n",
    "pendingBlockContent": PREM
        + "        ∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < n) ∧\n"
        + "        ∀ sp_mid : SurfPos, SSLComments sp_gram sp_mid →\n"
        + "        ∀ sp_end : SurfPos, SCompactSeqTail n sp_mid sp_end →\n"
        + "        ∀ sp_fin : SurfPos, SCompactMapTail n sp_end sp_fin →\n"
        + "        ResumeFrames (SLYamlStream sp_start) ks sp_fin)\n",
    "pendingProps": "      (h_mapTopE : (∃ e, sc.indents.back? = some e ∧ e.isSequence = false) →\n"
        + "        ∃ (ne : Nat) (ks : List FrameLevel), n = ne + 1 ∧ (∀ fr ∈ ks, fr.width < ne) ∧\n"
        + "        ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →\n"
        + "        ∀ sp_end : SurfPos, SCompactSeqTail ne sp_m sp_end →\n"
        + "        ∀ sp_fin : SurfPos, SCompactMapTail ne sp_end sp_fin →\n"
        + "        ResumeFrames (SLYamlStream sp_start) ks sp_fin)\n",
}
NODIR = "      (h_nodir : sc.allowDirectives = false)\n"
CTORS = ["pendingBlockContent", "pendingBlock"] + (["pendingProps"] if "--props" in sys.argv else [])
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def main():
    dry, keep, one = "--dry" in sys.argv, "--keep" in sys.argv, "--one" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); text = orig
    for name in CTORS:
        if one and name != "pendingBlock": continue
        head = f"  | {name} (sp_start"
        if text.count(head) != 1: sys.exit(f"{name}: expected 1 ctor head, found {text.count(head)}")
        i = text.index(head); j = text.index(NODIR, i)
        print(f"site {name}: h_mapTop after h_nodir (line {text[:j].count(chr(10)) + 2})")
        text = text[:j + len(NODIR)] + FIELDS[name] + text[j + len(NODIR):]
    print(f"md5 before: {before}")
    if dry: return
    SRC.write_text(text)
    if keep: print("kept"); return
    try:
        log = ROOT / ("scratch/389-flip-map-top3-build.log" if "--props" in sys.argv else "scratch/389-flip-map-top2-build.log"); log.parent.mkdir(exist_ok=True)
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
