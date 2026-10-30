#!/usr/bin/env python3
"""Price item 404 (the `h_kslotD` lane's first item, owner-ruled in items 397/399): the `?`-park
field `PendingNode.pendingBlock.h_kslot` DOMAINED.  Item 397 found the lane's chain starved at this
field: the park's own-slot face `∃ nv : Nat, … ResumeFrames … [FrameLevel.map nv]` carries no
marked-slot fact, so its three consumers fabricate `MarkedColsIn s' [nv]` singletons they cannot
prove.  A singleton is also the wrong statement — a park nested in two open `?` frames has two
marked columns (the field's own item-190 note) — so the flip restates the field in its twin
`h_kslotUp`'s CHAIN shape:

    (h_kslot : (∃ nv : Nat, ∀ sp_m …)                              -- before
    (h_kslot : (∃ (nv0 : Nat) (ns : List Nat), RegisterWitness.MarkedColsIn sc (nv0 :: ns) ∧ ∀ nv ∈ nv0 :: ns, ∀ sp_m …)  -- after (item 405: the HEAD is the park's own slot, which every birth knows; a bare chain left the single-slot consumers no head)

and reads who pays: every birth now owes the domain (a relay of the enclosing park's, or a
STARVED fresh singleton) and every consumer destructures `⟨ns, hdom, kslot⟩`.  Read-only: patch,
one `lake build L4YAML` (a FLOOR), `scripts/flip_census.py`, restore; md5 both sides.  `--dry`/`--keep`;
`--round N` (1–4, default 1) applies rounds 1..N CUMULATIVELY — round 2 adds the three lemma
premises, round 3 the `hkvUp` face, round 4 the `h_explUp` field; the sites line lists every head
patched, so round 4 always shows the seven-site ladder (item 405 added the content twin's field).
"""
import hashlib, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
CTOR = "  | pendingBlock (sp_start sp_block sp_scan : SurfPos) (n : Nat)\n"
OLD = "      (h_kslot : (∃ nv : Nat,\n"
NEW = "      (h_kslot : (∃ (nv0 : Nat) (ns : List Nat), RegisterWitness.MarkedColsIn sc (nv0 :: ns) ∧ ∀ nv ∈ nv0 :: ns,\n"
CTOR2 = "  | pendingBlockContent (sp_start sp_block sp_scan sp_gram : SurfPos) (n : Nat)\n"
# round 2: the three lemma PREMISES that restate the field (the callers that pattern-match the
# constructor and hand `h_kslot92` on break first otherwise, hiding every consumer behind them).
PREMS = [("lemma accum_block_on_pendingBlockContent", "    (h_kslot : (∃ nv : Nat,\n"),
         ("lemma accum_block_on_pendingBlock", "    (h_kslot : (∃ nv : Nat,\n"),
         ("lemma accum_content_on_pendingBlock_indented", "    (h_kslot_old : (∃ nv : Nat,\n")]
def dom(old): return old.replace("(∃ nv : Nat,", "(∃ (nv0 : Nat) (ns : List Nat), RegisterWitness.MarkedColsIn sc (nv0 :: ns) ∧ ∀ nv ∈ nv0 :: ns,")
# round 3: the supply question round 2 exposes — the `?`-park births inside
# `accum_block_on_closeThenBlock` build the field off its `h_vslot` premise's ancestor chain
# `hkvUp` (`∃ nsU, ∀ nvU ∈ nsU, …`), which carries no domain.  Domain it over the landed slot
# and the chain, `MarkedColsIn sc (nv :: nsU)`, and read which of the eleven callers can pay.
HKVUP = "      ((∃ nsU : List Nat, ∀ nvU ∈ nsU,\n"
HKVUP_D = "      ((∃ nsU : List Nat, RegisterWitness.MarkedColsIn sc (nv :: nsU) ∧ ∀ nvU ∈ nsU,\n"
# round 4: hkvUp's own supplier at the mapping-value park is the field `pendingMapValue.h_explUp`
# (the chain above a `?` park, item 191), undomained; domain it over the park's level and its chain.
EXPLUP = "      (h_explUp : (∃ (sp_q : SurfPos) (ns : List Nat), GLit '?' sp_q sp_scan ∧\n"
EXPLUP_D = "      (h_explUp : (∃ (sp_q : SurfPos) (ns : List Nat), GLit '?' sp_q sp_scan ∧ RegisterWitness.MarkedColsIn sc (n :: ns) ∧\n"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def round_of(argv):
    if "--round" in argv:
        n = int(argv[argv.index("--round") + 1])
        if not 1 <= n <= 4: sys.exit(f"--round takes 1..4, got {n}")
        return n
    return 1
def patch(text, rnd=1):
    lines = text.splitlines(keepends=True)
    c = [i for i, l in enumerate(lines) if l == CTOR]
    if len(c) != 1: sys.exit(f"expected one pendingBlock constructor head, matched {c}")
    h = next(i for i in range(c[0], c[0] + 60) if lines[i] == OLD)
    lines[h] = NEW
    sites = [("pendingBlock.h_kslot → chain + domain", h + 1)]
    c2 = [i for i, l in enumerate(lines) if l == CTOR2]
    if len(c2) != 1: sys.exit(f"expected one pendingBlockContent constructor head, matched {c2}")
    h2 = next(i for i in range(c2[0], c2[0] + 60) if lines[i] == OLD)
    lines[h2] = NEW
    sites.append(("pendingBlockContent.h_kslot → chain + domain (item 405: the content twin rides the ladder)", h2 + 1))
    if rnd >= 2:
        for anchor, old in PREMS:
            d = [i for i, l in enumerate(lines) if re.match(r"(public |private )?" + re.escape(anchor) + r"\b", l)]
            if len(d) != 1: sys.exit(f"expected one {anchor}, matched {d}")
            k = next(i for i in range(d[0], d[0] + 200) if lines[i] == old)
            lines[k] = dom(old); sites.append((anchor.split()[1] + " premise", k + 1))
    if rnd >= 3:
        u = [i for i, l in enumerate(lines) if l == HKVUP]
        if len(u) != 1: sys.exit(f"expected one hkvUp head, matched {u}")
        lines[u[0]] = HKVUP_D; sites.append(("closeThenBlock.h_vslot hkvUp → domained", u[0] + 1))
    if rnd >= 4:
        e = [i for i, l in enumerate(lines) if l == EXPLUP]
        if len(e) != 1: sys.exit(f"expected one h_explUp head, matched {e}")
        lines[e[0]] = EXPLUP_D; sites.append(("pendingMapValue.h_explUp → domained", e[0] + 1))
    return "".join(lines), sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    rnd = round_of(sys.argv)
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig, rnd)
    print(f"md5 before: {before}\nround: {rnd}\nsites: " + ", ".join(f"{n}@{ln}" for n, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/flip_kslot_field.log"; log.parent.mkdir(exist_ok=True)
        with open(log, "w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
    finally:
        if not keep: SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")
if __name__ == "__main__": main()
