#!/usr/bin/env python3
"""Price item 393 (DOCS item 392's NEXT, re-sited to the flow CLOSE): a frames face on `pendingFlow`.

`a: [1]⏎b: 2`: the flow value closes into `PendingNode.pendingFlow`, whose only route is the stream
BEFORE the collection (`h_stream`) — `accum_block_pending`'s `pendingFlow` arm hands `closeThenBlock`
every face as `Or.inr trivial`, so the root sibling `b` rides `rootMapRoute` (`[211]`'s laxity).  The
field priced here, inserted after `h_stream`:
  (h_frF : (∃ (n : Nat) (ks : List FrameLevel), ∀ sp_mid, SSLComments sp_scan sp_mid →
      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) ∨ True)
— the enclosing mapping's frames after the closed flow value, the shape `closeThenBlock.h_valF`
spends.  Nothing supplies it (no `sorry`): the build counts the construction(s) and the pattern
matches the field's arity breaks.  Read-only: patch, one `lake build L4YAML` (a FLOOR),
`lake exe scripts-flip-census`, restore; md5 both sides.  `--dry` patches nothing; `--keep` leaves the patch.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
CTOR = "  | pendingFlow (sp_start sp_block sp_scan : SurfPos)\n"
STREAM = "      (h_stream : SLYamlStream sp_start sp_block)\n"
FIELD = ("      (h_frF : (∃ (n : Nat) (ks : List FrameLevel), ∀ sp_mid, SSLComments sp_scan sp_mid →\n"
         "          ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) ∨ True)\n")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True)
    hits = [i for i in range(len(lines) - 1) if lines[i] == CTOR and lines[i + 1] == STREAM]
    if len(hits) != 1: sys.exit(f"expected one pendingFlow ctor, matched {hits}")
    lines.insert(hits[0] + 2, FIELD)
    return "".join(lines), hits[0] + 3
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, at = patch(orig)
    print(f"md5 before: {before}\nfield inserted at line {at}")
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/393-flip-flow-frames-field-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-6000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__":
    main()
