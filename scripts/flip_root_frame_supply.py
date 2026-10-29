#!/usr/bin/env python3
"""Price item 392 (DOCS item 391's NEXT): the SECOND (α) flip — the root births SUPPLYING `[FrameLevel.map 0]`.

Option (α) lets a frame name the park's OWN level.  Stage A is the statement side (item 150's stagger):
`ResumeFrames.level`'s `h_lt : ∀ fr ∈ ks, fr.width < k` widened to `≤ k`, together with the three (α)
bounds `flip_root_frame_le.py` priced (`pendingMapValue.h_closeF` `< n` → `≤ n`, both `h_valF` binders
`< nv` → `≤ nv`).  Stage B adds the supply side on top: every frameless birth item 380's
`flip_root_frames.py` rewrote — `⟨[], fun _ h => absurd h (List.not_mem_nil), …⟩` (frames lane) and
`⟨[], fun _ hm => (List.not_mem_nil hm).elim⟩` (cover lane) — becomes `[FrameLevel.map 0]` with `h_lt`
sorried, so the build reads the CONSUMERS of the longer list (the F-routes' `… [] sp_e` conclusions).
Read-only: patch, one `lake build L4YAML` (a FLOOR), `scripts/flip_census.py`, restore; md5 both sides.
`--stage A|B` (default A); `--dry` patches nothing; `--keep` leaves the patch.  Refuses a dirty StreamAccum.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
LEVEL = "      (h_lt : ∀ fr ∈ ks, fr.width < k)\n"
CLOSEF = "      (h_closeF : (∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < n) ∧\n"
VALF = "    (h_valF : (∃ (nv : Nat) (ks : List FrameLevel), (∀ fr ∈ ks, fr.width < nv) ∧\n"
A1 = "⟨[], fun _ h => absurd h (List.not_mem_nil),"
A2 = "⟨[], fun _ hm => (List.not_mem_nil hm).elim⟩"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text, stage):
    lines = text.splitlines(keepends=True); out = []; sites = []; ctor = None; in_level = False
    for i, l in enumerate(lines):
        if l.startswith("inductive ResumeFrames"): in_level = True
        elif l.startswith(("inductive", "lemma", "def", "structure", "/--")) and in_level and not l.startswith("inductive ResumeFrames"): in_level = False
        if l.startswith("  | ") and not l.startswith("  | ."): ctor = l.split()[1]
        if in_level and l == LEVEL:
            l = l.replace("fr.width < k)", "fr.width ≤ k)"); sites.append((i + 1, "ResumeFrames.level.h_lt"))
        elif ctor == "pendingMapValue" and l == CLOSEF:
            l = l.replace("fr.width < n)", "fr.width ≤ n)"); sites.append((i + 1, "pendingMapValue.h_closeF"))
        elif l == VALF:
            l = l.replace("fr.width < nv)", "fr.width ≤ nv)"); sites.append((i + 1, "h_valF"))
        out.append(l)
    if len(sites) != 4: sys.exit(f"expected 4 stage-A sites, matched {sites}")
    new = "".join(out)
    if stage == "B":
        n1, n2 = new.count(A1), new.count(A2)
        new = new.replace(A1, "⟨[FrameLevel.map 0], sorry,").replace(A2, "⟨[FrameLevel.map 0], sorry⟩")
        sites.append((0, f"stage B: {n1} frames-lane + {n2} cover-lane births → [FrameLevel.map 0] (h_lt sorried)"))
    return new, sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    stage = "A"
    if "--stage" in sys.argv:
        i = sys.argv.index("--stage") + 1
        if i >= len(sys.argv) or sys.argv[i] not in ("A", "B"): sys.exit("expected --stage A or --stage B")
        stage = sys.argv[i]
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig, stage)
    print(f"stage {stage}; md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for ln, n in sites))
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / f"scratch/392-flip-root-frame-supply-{stage}-build.log"; log.parent.mkdir(exist_ok=True)
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
