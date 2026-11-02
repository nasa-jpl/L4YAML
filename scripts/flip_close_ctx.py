"""Price item 388's lever (DOCS item 388): the mapping park's VALUE route is typed `.blockIn`
where the grammar's `[187]` implicit value is `.blockOut` (`SBlockMapEntry.implicitKeyNode`), and
the producers already weaken it (`SBlockNode_blockIn_to_blockOut`, 26 uses).  The `.blockIn`
typing is what keeps a `-` at the mapping's OWN column (`a:⏎- b`, `seq-spaces`: `[185]`'s n-1)
off the value route: `nestedBlockSeq` needs `nv + 1 ≤ k`, false at `nv = k`, while
`slotLandedSeq`'s `.blockOut` shape needs only `nv ≤ k`.  So the landed `-` birth routes it as a
BARE ROOT node (`h_docRoute` → `bareNodeRoute_or_refused`) and the mapping's sibling after it
(`a:⏎-⏎c: 1`) has no frame.
  stage 1 — `closeThenBlock`'s `h_valF` (binder + `deeperLandingResume`): `SBlockNode (nv + 1)
            .blockIn` → `.blockOut`  (2 sites)
  stage 2 — + the park's own `h_close` / `h_closeF` / `h_closeFV` at `PendingNode.pendingMapValue`
            and the relay `h_valFV` (`SBlockNode (n + 1)` / `(nn + 1)` `.blockIn` → `.blockOut`)
Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`lake exe scripts-flip-census`, restores; md5 printed both sides.  FLOOR: one build per stage.
`--stage 1|2` (default 2), `--dry` patches nothing, `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
S1 = [("∀ sp_mid : SurfPos, SBlockNode (nv + 1) .blockIn sp_gram sp_mid →\n      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map nv :: ks) sp_mid) ∨ True)",
       "∀ sp_mid : SurfPos, SBlockNode (nv + 1) .blockOut sp_gram sp_mid →\n      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map nv :: ks) sp_mid) ∨ True)", 2)]
S2 = S1 + [
  ("        SBlockNode (n + 1) .blockIn sp_scan sp_mid →\n        SLYamlStream sp_start sp_mid)",
   "        SBlockNode (n + 1) .blockOut sp_scan sp_mid →\n        SLYamlStream sp_start sp_mid)", 1),
  ("        ∀ sp_mid : SurfPos, SBlockNode (n + 1) .blockIn sp_scan sp_mid →\n        ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) ∨ True)",
   "        ∀ sp_mid : SurfPos, SBlockNode (n + 1) .blockOut sp_scan sp_mid →\n        ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) ∨ True)", 1),
  ("        ∀ sp_mid : SurfPos, SBlockNode (n + 1) .blockIn sp_scan sp_mid →\n        KeyFrames (ExplValueLine sp_start nv) ks sp_mid) ∨ PackAlt sc)",
   "        ∀ sp_mid : SurfPos, SBlockNode (n + 1) .blockOut sp_scan sp_mid →\n        KeyFrames (ExplValueLine sp_start nv) ks sp_mid) ∨ PackAlt sc)", 1),
  ("∀ sp_mid : SurfPos, SBlockNode (nn + 1) .blockIn sp_gram sp_mid →",
   "∀ sp_mid : SurfPos, SBlockNode (nn + 1) .blockOut sp_gram sp_mid →", 1)]
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    stage = int(sys.argv[sys.argv.index("--stage") + 1]) if "--stage" in sys.argv else 2
    edits = S1 if stage == 1 else S2
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); text = orig
    for old, new, n in edits:
        if text.count(old) != n: sys.exit(f"expected {n} site(s), found {text.count(old)} for {old[:60]!r}")
        text = text.replace(old, new)
    print(f"md5 before: {before}\nstage {stage}: {sum(n for _, _, n in edits)} statement sites flipped .blockIn → .blockOut")
    if dry: return
    SRC.write_text(text)
    if keep: print("kept"); return
    try:
        log = ROOT / f"scratch/388-flip-close-ctx-s{stage}-build.log"; log.parent.mkdir(exist_ok=True)
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
