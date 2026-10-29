#!/usr/bin/env python3
"""Price item 394 (DOCS item 393's NEXT, re-sited to the flow CLOSE's park): the frames CHAIN for
`a: [1]⏎b: 2`.  The flow close (`accum_step_flow`, `]`/`}` at depth 1 → 0) builds
`PendingNode.pendingContent` with `h_framesS := Or.inr trivial`, so `accum_block_pending`'s content arm
relays no frames into `closeThenBlock.h_mapF` and `b` rides `rootMapRoute`.  The chain: a frames twin
of `FlowBaseRoutes.value` —
  valueF : GateOf g → ∀ sp_ne sp_mid, SFlowContent n .flowOut sp_br sp_ne → SSLComments sp_ne sp_mid →
    (∃ ks : List FrameLevel, ResumeFrames (SLYamlStream sp_start) ks sp_mid) ∨ True
— born at the flow OPEN (`accum_flow_open_depth0`'s `pendingMapValue` arm, from `h_closeF` over
`SBlockNode.flowInBlock`), riding the base frame's `resume`, spent at the close as `h_framesS`.
The flip adds the field (`.ofValue` supplies `Or.inr trivial`) and sorries the two close-arm supplies;
the build reads every other construction of the record (arity) and every consumer.  Read-only: patch,
one `lake build L4YAML` (a FLOOR), `scripts/flip_census.py`, restore; md5 both sides.  `--dry`/`--keep`.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
KEY = "  key : (∃ (k : Nat) (sp_key : SurfPos),\n"
FIELD = ("  valueF : GateOf g → ∀ sp_ne sp_mid, SFlowContent n .flowOut sp_br sp_ne →\n"
         "    SSLComments sp_ne sp_mid → (∃ ks : List FrameLevel, ResumeFrames (SLYamlStream sp_start) ks sp_mid) ∨ True\n")
OFV_OLD = "  ⟨value, Or.inr trivial, Or.inr trivial⟩\n"
OFV_NEW = "  ⟨value, Or.inr trivial, Or.inr trivial, Or.inr trivial⟩\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True); sites = []
    ks = [i for i, l in enumerate(lines) if l == KEY]
    if len(ks) != 1: sys.exit(f"expected one FlowBaseRoutes.key line, matched {ks}")
    lines[ks[0]:ks[0]] = [FIELD]; sites.append(("FlowBaseRoutes.valueF", ks[0] + 1))
    ofv = [i for i, l in enumerate(lines) if l == OFV_OLD]
    if len(ofv) != 1: sys.exit(f"expected one .ofValue body, matched {ofv}")
    lines[ofv[0]] = OFV_NEW; sites.append((".ofValue", ofv[0] + 1))
    closes = [i for i, l in enumerate(lines) if "=> resume.value" in l]
    if len(closes) != 2: sys.exit(f"expected two close arms spending resume.value, matched {closes}")
    for c in closes:
        j = next(k for k in range(c, c + 40) if lines[k].strip() == "(Or.inr trivial)")
        lines[j] = lines[j].replace("(Or.inr trivial)", "(sorry)"); sites.append(("close h_framesS → sorry", j + 1))
    return "".join(lines), sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for n, ln in sites))
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/394-flip-flow-frames-chain-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-6000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__":
    main()
