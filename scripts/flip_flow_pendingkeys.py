#!/usr/bin/env python3
"""Price item 407 (DOCS item 406's NEXT, ruling (A) by default): the flow carrier's `pendingKeys`
conjunct.  `FlowStackK` carries `(0 < fl → sc.indents = s0.indents)` from the flow OPEN state `s0` to
every interior state `sc`; `MarkedColsIn.transport` (RegisterWitness) also needs
`sc.pendingKeys = s0.pendingKeys` to move a marked-column domain from the open to the close
(item 406 round 2, `accum_step_flow` lines 20556 / 20796).  The flip ADDS the conjunct
`(0 < fl → sc.pendingKeys = s0.pendingKeys) ∧` beside the indents one and reads which
constructors/relays of `FlowStackK` break — every break is a site that must SUPPLY the equality
(from `PendingKeysStable`'s per-dispatch lemmas, or a new `preprocess_pendingKeys_of_inFlow`).
Read-only: patch, one `lake build L4YAML` (a FLOOR), `lake exe scripts-flip-census`, restore; md5 both sides.
`--dry` prints the site; `--keep` leaves the patched tree for the pay.  On a tree where the carrier is
already PAID (item 407) the script refuses instead of inserting a duplicate conjunct.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
IND = "    (0 < fl → sc.indents = s0.indents) ∧\n"
IND_PK = "    (0 < fl → sc.indents = s0.indents) ∧\n    (0 < fl → sc.pendingKeys = s0.pendingKeys) ∧\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True)
    d = [i for i, l in enumerate(lines) if l.startswith("def FlowStackK ")]
    if len(d) != 1: sys.exit(f"expected one def FlowStackK, matched {d}")
    head = lines[d[0]:d[0] + 14]
    if any("sc.pendingKeys = s0.pendingKeys" in l for l in head):
        sys.exit("FlowStackK already carries the pendingKeys conjunct (item 407 PAID); nothing to price — "
                 "the flip's reading is recorded in DOCS item 407 (8 declarations / 25 sites)")
    hs = [i for i in range(d[0], d[0] + 14) if lines[i] == IND]
    if len(hs) != 1: sys.exit(f"expected one indents conjunct in FlowStackK, matched {hs}")
    h = hs[0]
    lines[h] = IND_PK
    return "".join(lines), [("FlowStackK pendingKeys conjunct", h + 1)]
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for n, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/flip_flow_pendingkeys.log"; log.parent.mkdir(exist_ok=True)
        with open(log, "w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        if c.returncode != 0: sys.exit(f"scripts-flip-census exit={c.returncode}: {c.stderr.strip()}")
        print(c.stdout[-6000:]); print(c.stderr[-2000:], file=sys.stderr)
    finally:
        if not keep: SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__": main()
