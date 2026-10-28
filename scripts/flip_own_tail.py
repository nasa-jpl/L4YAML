"""Price item 382's design (a) (DOCS item 382): the MAPPING parks carry their OWN level's open
tail.  `ResumeFrames.level n ks sp` IS the conjunct `(∀ fr ∈ ks, fr.width < n) ∧ ∀ sp_end,
SCompactMapTail n sp sp_end → ResumeFrames … ks sp_end`, so the own tail is the frame list's HEAD:
`pendingMapValue.h_frames` resumes `FrameLevel.map n :: ks` after its comments run, and the three
relays of that field to the openers (`flowKeyRoute_of_root.h_mapF`, `accum_block_on_closeThenBlock.h_mapF`,
`accum_block_on_pendingContent.h_mapF109`, which have no level in scope) resume
`FrameLevel.map n' :: ks` for an existential `n'`.  The park's OTHER resume field (`h_closeF`, the
non-empty value's `SBlockNode (n + 1)` domain) already resumes `FrameLevel.map n :: ks` — the own
tail is a projection the park holds today; this flip extends it to the EMPTY-value path
(`a:⏎b: 2`: comments run to the landing), the one that reaches the openers' no-pop arms.  Producers that cannot supply the own-level
entry+tail (a birth with no empty-value entry over its comments run) break as STARVED; consumers
break on the pattern's arity and at `hmem`, which the head frame now decides.

Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`scripts/flip_census.py`, restores; md5 printed both sides.  FLOOR: one build of the library.
`--dry` patches nothing and reports the sites; `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
PARK_TAIL_OLD = "        ResumeFrames (SLYamlStream sp_start) ks sp_mid) ∨ True)\n"
PARK_TAIL_NEW = "        ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n :: ks) sp_mid) ∨ True)\n"
RELAYS = ("h_mapF", "h_mapF", "h_mapF109")
RELAY_TAIL_OLD = "      ResumeFrames (SLYamlStream sp_start) ks sp_m) ∨ True)\n"
RELAY_TAIL_NEW = "      ResumeFrames (SLYamlStream sp_start) (FrameLevel.map n' :: ks) sp_m) ∨ True)\n"

def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()

def patch(text):
    lines = text.splitlines(keepends=True); sites = []
    for i, l in enumerate(lines):
        if l == "      (h_frames : (∃ ks : List FrameLevel,\n":
            j = i + 1
            while lines[j].lstrip().startswith("--"): j += 1          # item 147's cover comment
            if "IndentStackCover.Floor lo n ks" in lines[j] and lines[j + 3] == PARK_TAIL_OLD:
                lines[j + 3] = PARK_TAIL_NEW; sites.append((i + 1, "pendingMapValue.h_frames"))
        for name in set(RELAYS):
            if l == f"    ({name} : (∃ ks : List FrameLevel,\n" and lines[i + 2] == RELAY_TAIL_OLD:
                lines[i] = f"    ({name} : (∃ (n' : Nat) (ks : List FrameLevel),\n"
                lines[i + 2] = RELAY_TAIL_NEW; sites.append((i + 1, name))
    if len(sites) != 4: sys.exit(f"expected 4 sites, matched {sites}")
    return "".join(lines), sites

def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text(); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{n}@{ln}" for ln, n in sites))
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/382-flip-own-tail-build.log"; log.parent.mkdir(exist_ok=True)
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
