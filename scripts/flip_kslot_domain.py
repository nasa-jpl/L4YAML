#!/usr/bin/env python3
"""Price item 397 (re-anchored 2026-10-30, item 406: the props `:` birth's decline line (inside `colon_fires_props_key`, the `colon_open_map_props` application) now reads `h_dispatch (Or.inr trivial) h_cf h_lkt` on the #179 base) (DOCS item 396's NEXT, re-sited): `h_kslotD`'s informative side at the two
implicit-key `:` births.  `colon_open_map_implicit.h_kslotD` / `colon_open_map_props.h_kslotD` ask
`∃ ns, MarkedColsIn s' ns ∧ ∀ nv ∈ ns, …` and both producers (`colon_fires_implicit_key`,
`colon_fires_props_key`) pass `Or.inr trivial`, because the packs' value-line faces
(`ImplicitKeyPack` / `PropsKeyPack`, the `∃ ns, ∀ nv ∈ ns, …` conjunct) carry NO domain: the pack
producers' `h_nodeV` premise drops the park's `MarkedColsIn sc ns` (`pendingMapValue.h_kslot` has it;
`entryPropsKeyPack_of_dispatch`'s caller strips it with `h_kslot.imp (fun ⟨ns, _, k⟩ => ⟨ns, k⟩) id`).
The flip DOMAINS the chain: the two pack faces and the two `h_nodeV` premises gain
`RegisterWitness.MarkedColsIn sc ns ∧`, and the two `:` births' declines become `sorry` so the build
reports the supply as an obligation.  Every other breakage is the price (pack builders that fabricate
`ns = []` now owe `MarkedColsIn s' []`, relays owe `MarkedColsIn.step_content`).  Read-only: patch, one
`lake build L4YAML` (a FLOOR), `lake exe scripts-flip-census`, restore; md5 both sides.  `--dry`/`--keep`; `--round2` also domains the flow record's key face
(`FlowBaseRoutes.key`, at the open state `s0`) and `flowKeyPack_of_close.h_key`'s (at the close state), the
chain round 1 exposed at lines 1692 / 14657.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
HEAD = "    ((∃ ns : List Nat, ∀ nv ∈ ns,\n"
HEAD_D = "    ((∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv ∈ ns,\n"
HEAD6 = "      ((∃ ns : List Nat, ∀ nv ∈ ns,\n"
NODEV = "    (h_nodeV : (∃ ns : List Nat, ∀ nv ∈ ns,\n"
NODEV_D = "    (h_nodeV : (∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv ∈ ns,\n"
DECL_PROPS = "        h_dispatch (Or.inr trivial) h_cf h_lkt\n"
DECL_IMPL = "            (PackAlt.step_value h_preprocess h_dispatch h_noflow) (Or.inr trivial)\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True); sites = []
    for name in ("ImplicitKeyPack", "PropsKeyPack"):
        d = [i for i, l in enumerate(lines) if l.startswith(f"def {name} ")]
        if len(d) != 1: sys.exit(f"expected one def {name}, matched {d}")
        h = next(i for i in range(d[0], d[0] + 120) if lines[i] == HEAD)
        lines[h] = HEAD_D; sites.append((f"{name} face", h + 1))
    if "--round2" in sys.argv:
        for anchor, old, new, tag in (
            ("structure FlowBaseRoutes ", HEAD, HEAD.replace("∀ nv", "RegisterWitness.MarkedColsIn s0 ns ∧ ∀ nv"), "FlowBaseRoutes.key face (s0)"),
            ("lemma flowKeyPack_of_close ", HEAD6, HEAD6.replace("∀ nv", "RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv"), "flowKeyPack_of_close.h_key face (sc)")):
            d = [i for i, l in enumerate(lines) if l.startswith(anchor)]
            if len(d) != 1: sys.exit(f"expected one {anchor}, matched {d}")
            h = next(i for i in range(d[0], d[0] + 120) if lines[i] == old)
            lines[h] = new; sites.append((tag, h + 1))
    nv = [i for i, l in enumerate(lines) if l == NODEV]
    if len(nv) != 2: sys.exit(f"expected two h_nodeV heads, matched {nv}")
    for i in nv: lines[i] = NODEV_D; sites.append(("h_nodeV", i + 1))
    for old, tag in ((DECL_PROPS, "props h_kslotD"), (DECL_IMPL, "implicit h_kslotD")):
        k = [i for i, l in enumerate(lines) if l == old]
        if len(k) != 1: sys.exit(f"expected one {tag} decline, matched {k}")
        new = old.replace("(Or.inr trivial)", "(sorry)", 1)
        if new == old: sys.exit(f"{tag} decline line did not change: {old!r}")
        lines[k[0]] = new; sites.append((f"{tag} → sorry", k[0] + 1))
    return "".join(lines), sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for n, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/flip_kslot_domain.log"; log.parent.mkdir(exist_ok=True)
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
