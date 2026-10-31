#!/usr/bin/env python3
"""Item 415's probe: the OWED TYPE at each statement-shaped `| Or.inl … => Or.inr trivial` decline.
The 14 sites (item 414's residue TSV, class `Or.inl`) are the arms where the upstream alternative
is INFORMATIVE and the site still declines.  Pricing them means knowing what each owes: this
script rewrites each site's `Or.inr trivial` into `(by exact (⟨⟩ : Unit))` — a deliberate type
mismatch whose error message prints the goal — names the arm's witnesses so the message can be
read against them, runs `lake build L4YAML`, collects the 14 expected types, and restores
`StreamAccum.lean` byte-identical (both md5s printed).  Read-only in effect; never run it beside
another `lake build`.  Sites are addressed by the committed line numbers below and verified by
their text, so the probe refuses on a tree where they moved."""
import hashlib, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
SITES = {  # line: (expected text, named replacement of the arm head)
    40379: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40396: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40503: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40520: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40624: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    40641: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    38182: ("| Or.inl ⟨sp_q, h_qlit, route, _⟩ => Or.inr trivial", "| Or.inl ⟨sp_q, h_qlit, route, h_chainUp⟩ => "),
    38372: ("| Or.inl ⟨sp_q, h_qlit, route, _⟩ => Or.inr trivial", "| Or.inl ⟨sp_q, h_qlit, route, h_chainUp⟩ => "),
    38467: ("| Or.inl ⟨sp_q, h_qlit, route, _⟩ => Or.inr trivial", "| Or.inl ⟨sp_q, h_qlit, route, h_chainUp⟩ => "),
    37461: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
    27801: ("| Or.inl _, Or.inr _ => Or.inr trivial", "| Or.inl h_own, Or.inr h_altUp => "),
    27844: ("| Or.inl ⟨nsU, _, kvU⟩ => Or.inr trivial", "| Or.inl ⟨nsU, h_domU, kvU⟩ => "),
    24659: ("| Or.inl ⟨nv, _, _, contV⟩ => Or.inr trivial", "| Or.inl ⟨nv, h_ltV, h_covV, contV⟩ => "),
    14872: ("| Or.inl _ => Or.inr trivial", "| Or.inl h_inl => "),
}
PROBE = "(by exact (⟨⟩ : Unit))"
md5 = lambda: hashlib.md5(SRC.read_bytes()).hexdigest()
orig = SRC.read_text(); lines = orig.split("\n"); m0 = md5()
for ln, (text, head) in SITES.items():
    if text not in lines[ln - 1]:
        sys.exit(f"site moved: line {ln} does not contain `{text}`")
    lines[ln - 1] = lines[ln - 1].replace(text, head + PROBE)
try:
    SRC.write_text("\n".join(lines))
    print(f"probe tree md5 {md5()[:12]}; building L4YAML …", flush=True)
    r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    (ROOT / "scratch").mkdir(exist_ok=True)
    errs = re.findall(r"error: L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): [Tt]ype mismatch.*?\n(.*?)(?=\n(?:error|warning|info|✖|✔|Build|\[)|\Z)", out, re.S)
    print(f"INL-PROBE sites={len(SITES)} mismatches={len(errs)} exit={r.returncode}")
    for ln, col, body in errs:
        print(f"--- site {ln}:{col}\n{body.strip()}\n")
finally:
    SRC.write_text(orig)
    print(f"restored md5 {md5()[:12]} (orig {m0[:12]}) identical={md5() == m0}")
