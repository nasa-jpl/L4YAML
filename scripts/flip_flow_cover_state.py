#!/usr/bin/env python3
"""Price option B for item 394 (Rule 8 review on PR #166): tie `FlowBaseRoutes.valueF`'s frames list to the
scanner's indent stack.  A new state index `(s0 : ScannerState)` on `FlowBaseRoutes`, `FlowOpenStack` and
`FlowStackB` (census class `state`), and `valueF`'s informative side gains the cover
`(∃ lo m, IndentStackCover.Floor lo m ks ∧ IndentStackCover.Covered lo ks s0)`.  The flip adds the index to
the three headers and the conjunct to the field, sorries the mapping arm's supply and both close relays, and
lets one `lake build L4YAML` list every type mention and construction that must restate (a FLOOR: guard
modules behind the library are unmeasured).  Read-only: md5 printed both sides, source restored.  `--dry`.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True); sites = []
    def hdr(start, old="    (g : Option ScannerState) :", new="    (g : Option ScannerState) (s0 : ScannerState) :"):
        i = next(k for k, l in enumerate(lines) if l.startswith(start))
        j = next(k for k in range(i, i + 4) if lines[k].startswith(old))
        lines[j] = lines[j].replace(old, new, 1); sites.append((start.split()[1], j + 1))
    hdr("inductive FlowOpenStack"); hdr("inductive FlowStackB")
    # recursive mentions inside the three declaration blocks must carry s0 too, or the headers fail and
    # every external mention reads "Unknown identifier" (round 1: capped at 100 errors, not a reading)
    def block(start):
        i = next(k for k, l in enumerate(lines) if l.startswith(start))
        j = next(k for k in range(i + 1, len(lines)) if lines[k] and not lines[k][0].isspace() and not lines[k].startswith(("/--", "--", "|")))
        return i, j
    for start, subs in (("inductive FlowOpenStack", [("FlowOpenStack sp_start n kc g ", "FlowOpenStack sp_start n kc g s0 "), ("FlowBaseRoutes sp_start n sp_br kc g)", "FlowBaseRoutes sp_start n sp_br kc g s0)")]),
                        ("inductive FlowStackB", [("FlowStackB sp_start n kc g ", "FlowStackB sp_start n kc g s0 "), ("FlowOpenStack sp_start n kc g ", "FlowOpenStack sp_start n kc g s0 ")])):
        i, j = block(start)
        for k in range(i + 1, j):
            for a, b in subs:
                if a in lines[k] and b not in lines[k]: lines[k] = lines[k].replace(a, b)
    imp = max(k for k, l in enumerate(lines[:200]) if l.startswith(("import ", "public import ")))
    lines.insert(imp + 1, "set_option maxErrors 5000\n"); sites.append(("maxErrors", imp + 2))
    i = next(k for k, l in enumerate(lines) if l.startswith("structure FlowBaseRoutes"))
    j = next(k for k in range(i, i + 3) if "(g : Option ScannerState) : Prop where" in lines[k])
    lines[j] = lines[j].replace("(g : Option ScannerState) : Prop where", "(g : Option ScannerState) (s0 : ScannerState) : Prop where"); sites.append(("FlowBaseRoutes", j + 1))
    old = "    (∃ ks : List FrameLevel, ∀ sp_mid, SSLComments sp_ne sp_mid →\n"
    k = next(k for k, l in enumerate(lines) if l == old)
    lines[k] = ("    (∃ ks : List FrameLevel,\n      (∃ lo m : Nat, IndentStackCover.Floor lo m ks ∧ IndentStackCover.Covered lo ks s0) ∧\n"
                "      ∀ sp_mid, SSLComments sp_ne sp_mid →\n"); sites.append(("valueF cover", k + 1))
    # the mapping arm's supply and both close relays → sorry
    sup = [k for k, l in enumerate(lines) if "sp_block ⟨(fun sp_ne h_content => h_closeF_mv.imp" in l]
    assert len(sup) == 1, sup
    k0 = sup[0]; l0 = lines[k0]; a = l0.index("⟨(fun sp_ne h_content")
    l2 = lines[k0 + 2]; tail_marker = "⟩) id), "
    assert tail_marker in l2, l2
    rest = l2[l2.index(tail_marker) + len(tail_marker):]
    lines[k0] = l0[:a] + "⟨sorry, " + rest
    del lines[k0 + 1: k0 + 3]; sites.append(("mapping-arm supply → sorry", k0 + 1))
    rel = [k for k, l in enumerate(lines) if "((resume.valueF sp_tok (SFlowContent." in l]
    assert len(rel) == 2, rel
    for k in rel:
        ind = lines[k][:len(lines[k]) - len(lines[k].lstrip())]
        lines[k] = ind + "(sorry)\n"; sites.append(("close relay → sorry", k + 1))
    return "".join(lines), sites
def main():
    dry = "--dry" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for n, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/394-flip-flow-cover-state-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-5000:]); print(c.stderr[-1500:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig); print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__":
    main()
