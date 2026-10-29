"""Price item 386's L1 (DOCS item 386): the openers' DEDENT leaves under a no-pop landing.  Item 385's
helpers (`deeperLandingResume`, `deeperLandingResumeSeq`) decline `k ≤ level`; closing those leaves
needs the park's LEVEL at or below the scanner's top — `(n : Int) ≤ sc.currentIndent`, which is
`IndentFloor sc (n + 1)`'s second conjunct unfolded (`minContentIndentOf`), a field BOTH node-holding
parks carry (`pendingBlock.h_floor`, `pendingMapValue.h_floor`) and the dispatcher drops (it passes
`h_floor208.1` alone to `accum_block_on_pendingBlock`; binds `pendingMapValue`'s as `_`).  The upper
bound (`s_prep.currentIndent ≤ s_prep.col`, `landing_floor_of_arm`) is already in both openers' scope.

Three read-only stages, one `L4YAML` build each (FLOOR; guard modules behind it unmeasured):
  --stage 1  R1: a new binder `h_lvl_old : (n : Int) ≤ sc.currentIndent` on `accum_block_on_pendingBlock`
             after `h_top_old` — callers break by arity (the dispatcher's `pendingBlock` arm).
  --stage 2  R2: the conjunct `(nv : Int) ≤ sc.currentIndent` inside `h_valF`'s existential at
             `accum_block_on_closeThenBlock` and its consumer helper `deeperLandingResume` — no new
             binder; the `∨ True` arm absorbs; producers break where they build the existential
             (`h_closeF155.imp (fun h => ⟨nmv, h⟩) id`), consumers at the destructuring pattern.
  --stage 3  R3: the cover's `∨ True` dropped on `pendingMapValue.h_closeF` and every relay of it
             (`h_valF` at the opener and the helper, the content twin) — births that cannot supply
             the cover break as STARVED; this is the pop case's price at the mapping park.
Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`scripts/flip_census.py`, restores; md5 printed both sides.  `--dry` patches nothing and reports
the sites; `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
TOP_OLD = "    (h_top_old : sc.currentIndent ≤ (n : Int))\n"
LVL_NEW = "    (h_lvl_old : (n : Int) ≤ sc.currentIndent)\n"
VALF_OLD = "    (h_valF : (∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < nv) ∧\n"
VALF_NEW = "    (h_valF : (∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < nv) ∧ (nv : Int) ≤ sc.currentIndent ∧\n"
COVER_OLD = ("IndentStackCover.Covered lo (FrameLevel.map n :: ks) sc) ∨ True) ∧\n",
             "IndentStackCover.Covered lo (FrameLevel.map nv :: ks) sc) ∨ True) ∧\n")
EXPECT = {1: 1, 2: 2, 3: 4}

def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()

def patch(text, stage):
    lines = text.splitlines(keepends=True); out = []; sites = []
    for i, l in enumerate(lines):
        if stage == 1 and l == TOP_OLD:
            out.append(l); out.append(LVL_NEW); sites.append((i + 1, "h_lvl_old")); continue
        if stage == 2 and l == VALF_OLD:
            out.append(VALF_NEW); sites.append((i + 1, "h_valF")); continue
        if stage == 3:
            for c in COVER_OLD:
                if l.endswith(c):
                    l = l[: -len(c)] + c.replace(" ∨ True)", ")"); sites.append((i + 1, "cover")); break
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
        log = ROOT / f"scratch/386-flip-floor-relay-s{stage}-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'MISMATCH'})")

if __name__ == "__main__":
    main()
