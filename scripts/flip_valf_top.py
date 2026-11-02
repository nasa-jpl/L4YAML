#!/usr/bin/env python3
"""Price item 390 (DOCS item 390): the landed `nv < k` NO-PUSH half at `accum_block_on_closeThenBlock`.

Item 389 left `(if hci : s_prep.currentIndent < k then Or.inl (pushedBirth_not_mapTop …) else Or.inr trivial)`
at the landed birth under `nv < k`: the push half is refuted (a pushed `-` has a SEQUENCE top), the no-push
half is declined.  The no-push half is UNREACHABLE if the mapping park's own top is at or left of its level:
`k ≤ s_prep.currentIndent ≤ sc.currentIndent ≤ nv < k`.  The upper bound `sc.currentIndent ≤ nv` is what
`h_valF` does not carry — item 386 added the LOWER bound `nv ≤ sc.currentIndent` (`IndentFloor`) and no
`pendingMapValue` field states the upper one (`pendingBlock.h_top_old` is the `-` park's).

Two read-only stages, one `L4YAML` build each (FLOOR; guard modules behind it unmeasured):
  --stage 1  the conjunct `sc.currentIndent ≤ (nv : Int)` inside `h_valF`'s existential at
             `accum_block_on_closeThenBlock` and its helper `deeperLandingResume` — producers break
             where they build the existential, consumers at the destructuring pattern.
  --stage 2  a new field `h_top : sc.currentIndent ≤ (n : Int)` on `pendingMapValue` after `h_floor` —
             the six births break by arity, the pattern matches by shape; a birth with no top fact in
             scope is STARVED.
Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`lake exe scripts-flip-census`, restores; md5 printed both sides.  `--dry` patches nothing; `--keep` leaves
the patch in place.  Refuses a dirty `StreamAccum.lean`.
"""
import hashlib, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
LVL = "      (nv : Int) ≤ sc.currentIndent ∧\n"
TOP = "      sc.currentIndent ≤ (nv : Int) ∧\n"
FLOOR_MV = "      (h_floor : IndentFloor sc (n + 1))\n"
FIELD = "      (h_top : sc.currentIndent ≤ (n : Int))\n"
EXPECT = {1: 2, 2: 1}

def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()

def patch(text, stage):
    lines = text.splitlines(keepends=True); out = []; sites = []
    ctor = None
    for i, l in enumerate(lines):
        if l.startswith("  | ") and not l.startswith("  | ."): ctor = l.split()[1]
        if stage == 1 and l == LVL:
            out.append(l); out.append(TOP); sites.append((i + 1, "h_valF-top")); continue
        if stage == 2 and l == FLOOR_MV and ctor == "pendingMapValue":
            out.append(l); out.append(FIELD); sites.append((i + 1, "pendingMapValue.h_top")); continue
        out.append(l)
    if len(sites) != EXPECT[stage]: sys.exit(f"stage {stage}: expected {EXPECT[stage]} sites, matched {sites}")
    return "".join(out), sites

def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    stage = int(sys.argv[sys.argv.index("--stage") + 1]) if "--stage" in sys.argv else 1
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig, stage)
    print(f"stage {stage}\nmd5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for ln, n in sites))
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / f"scratch/390-flip-valf-top-s{stage}-build.log"; log.parent.mkdir(exist_ok=True)
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
