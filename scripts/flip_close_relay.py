#!/usr/bin/env python3
"""Item 384 price instrument (second reading): relay the mapping park's own value-node route
`pendingMapValue.h_close : ∀ sp_mid, SBlockNode (n+1) .blockIn sp_scan sp_mid → SLYamlStream sp_start sp_mid`
into `accum_block_on_closeThenBlock`, whose `h_res_land` builder needs it for the deeper landing
(item 383's stop).  The instrument adds the binder in a COUNTING shape — `(∃ n, …) ∨ True` — so every
caller breaks (an added explicit binder shifts the application) and one `L4YAML` build reads the
producer roster; the pay's shape is decided arm by arm (no `∨ True` lands).  Read-only: edits
StreamAccum.lean, builds, runs flip_census.py, restores (md5 both sides).  `--dry` lists the site."""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
ANCHOR = ("    (h_close_pending : danglingNodePos? sc = none →\n"
          "      underIndentedFlowValuePos? sc = none →\n"
          "      ∀ sp_mid, SSLComments sp_gram sp_mid → SLYamlStream sp_start sp_mid)\n")
NEW_BINDER = ("    (h_closeN : (∃ n : Nat, ∀ sp_mid : SurfPos,\n"
              "      SBlockNode (n + 1) .blockIn sp_scan sp_mid → SLYamlStream sp_start sp_mid) ∨ True)\n")
DECL = "lemma accum_block_on_closeThenBlock"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    d = text.index(DECL); a = text.index(ANCHOR, d)
    nxt = text.find("\nlemma ", d + len(DECL))
    if nxt != -1 and a > nxt: sys.exit("anchor not inside the declaration")
    line = text[:a].count("\n") + 1
    return text[:a + len(ANCHOR)] + NEW_BINDER + text[a + len(ANCHOR):], line
def main():
    dry = "--dry" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, line = patch(orig)
    print(f"md5 before: {before}\nbinder inserted after h_close_pending (line {line}) in {DECL}")
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/384-flip-close-relay-build.log"; log.parent.mkdir(exist_ok=True)
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
