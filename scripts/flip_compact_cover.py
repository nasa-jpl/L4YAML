#!/usr/bin/env python3
"""Price item 411: the compact builder's four cover arms, end-to-end.

`accum_content_on_pendingMapValue_indented` births the pack's value-line pair face twice
(`h_ivl_pack`, `h_compact_vslot`), each cased on `h_expl` (the park IS a `?` / is not): four
arms that since item 409 DECLINE (`Or.inr trivial`), because the face's chain is a COVER
(`∃ ns, MarkedColsIn sc ns ∧ ∀ nv ∈ ns, …`) and the old witnesses `[n]` / `[]` are false under a
nested `?` (Priority 69).  The payable witness is `ns := markedCols sc` (`MarkedColsIn.self`) with a
route per mark: the park's OWN mark (`nv = n`) rides `h_expl`'s compact route exactly as before
item 409; an ANCESTOR's mark (`nv ≠ n`) needs `h_kslot`'s route, whose premise is
`SBlockNode (n + 1) .blockIn sp_scan sp_m` while the face asks `SBlockIndented n .blockIn sp_scan sp`
— `[185]` is WIDER than `[196]` (compact forms, `e-node`), so the route does not transfer.

Stage A (`--stage A`, default): rewrite the four arms to the `markedCols sc` witness with the own
route paid and the ancestor route `sorry`; `lake build L4YAML` reports whether the own route is a
LEMMA (0 declarations broken, 4 `sorry` obligations) — the first half of the mandate's question.
Stage B (`--stage B`): stage A plus the STATEMENT change the ancestor route needs — the chain's
node premise re-shaped `SBlockNode (n + 1) .blockIn` → `SBlockIndented n .blockIn` at the park field
(`pendingMapValue.h_kslot`), the lemma's `h_kslot`, and the two pack lemmas' `h_nodeV`; the build's
broken declarations (resolved by `lake exe scripts-flip-census`) are the price of widening the face,
a FLOOR (one round).  Read-only: patch, build, census, restore; md5 both sides.  `--dry` prints
the sites; `--keep` leaves the patch in place (for a descent round).
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
ARM = (
    "        -- Item 409: `[n]` is the `?` park's own column — marked in fact, but no face here says\n"
    "        -- so (the own-mark scanner lemma is unpaid), so under the domain this birth DECLINES.\n"
    "        | Or.inl _ => Or.inr trivial\n"
    "        -- …and `[]` would claim the park holds NO mark (`MarkedColsIn` is a cover): DECLINES.\n"
    "        | Or.inr _ => Or.inr trivial⟩\n")
ARM_NEW = (
    "        | Or.inl ⟨sp_q, h_qlit, route⟩ => Or.inl ⟨RegisterWitness.markedCols sc,\n"
    "            RegisterWitness.MarkedColsIn.self sc,\n"
    "            fun nv _hnv sp h_bi sp_i sp_c h_iv h_lit sp_v h_sbi =>\n"
    "              if hn : nv = n then by\n"
    "                subst hn\n"
    "                exact ResumeFrames.one (route sp_v (SBlockMapEntry.explicit _ sp_q sp_scan sp sp_i sp_c sp_v\n"
    "                  h_qlit (SBlockIndented_blockIn_to_blockOut h_bi) h_iv h_lit h_sbi))\n"
    "              else sorry⟩\n"
    "        | Or.inr _ => Or.inl ⟨RegisterWitness.markedCols sc, RegisterWitness.MarkedColsIn.self sc,\n"
    "            fun _nv _hnv _sp _h_bi _sp_i _sp_c _h_iv _h_lit _sp_v _h_sbi => sorry⟩⟩\n")
NODE = "SBlockNode (n + 1) .blockIn sp_scan sp_m →\n"
NODE_W = "SBlockIndented n .blockIn sp_scan sp_m →\n"
PREMISES = ("  | pendingMapValue (", "lemma entryKeyPack_of_dispatch", "lemma entryPropsKeyPack_of_dispatch",
            "lemma accum_content_on_pendingMapValue_indented")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text, stage):
    n = text.count(ARM)
    if n != 2: sys.exit(f"expected the four arms as two identical blocks, matched {n}")
    sites = [("arms (h_ivl_pack + h_compact_vslot)", text[:text.index(ARM)].count("\n") + 1)]
    text = text.replace(ARM, ARM_NEW)
    if stage == "B":
        lines = text.splitlines(keepends=True)
        for anchor in PREMISES:
            d = [i for i, l in enumerate(lines) if l.startswith(anchor)]
            if len(d) != 1: sys.exit(f"expected one {anchor!r}, matched {d}")
            hits = [i for i in range(d[0], d[0] + 160) if lines[i].endswith(NODE) and "ns," in lines[i - 1]]
            if len(hits) != 1: sys.exit(f"expected one chain premise under {anchor!r}, matched {hits}")
            lines[hits[0]] = lines[hits[0]].replace(NODE, NODE_W); sites.append((f"{anchor.strip()} chain premise", hits[0] + 1))
        text = "".join(lines)
    return text, sites
def main():
    stage = sys.argv[sys.argv.index("--stage") + 1] if "--stage" in sys.argv else "A"
    if stage not in ("A", "B"):
        sys.exit(f"unknown stage {stage!r}; expected A or B")
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig, stage)
    print(f"stage {stage}; md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for n, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / f"scratch/411-flip-{stage}.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        if c.returncode != 0: sys.exit(f"scripts-flip-census exit={c.returncode}: {c.stderr.strip()}")
        print(c.stdout[-6000:]); print(c.stderr[-2000:], file=sys.stderr)
        txt = log.read_text()
        print(f"sorry warnings: {txt.count('declaration uses ')}; errors: {txt.count(': error:')}")
    finally:
        if not keep:
            SRC.write_text(orig); print(f"md5 after: {md5(SRC)} (restored={md5(SRC) == before})")
        else: print("--keep: patch left in place")
if __name__ == "__main__": main()
