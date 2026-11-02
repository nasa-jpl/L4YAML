"""Price item 377's carrier (DOCS item 377): the openers' `h_res_land` carries item 372's
sequence-top face in place of its vacuous `∨ True` — at `colon_open_map`, `question_open_map`
and `indicator_open_map` the binder's tail `… ResumeFrames (SLYamlStream sp_start) ks sp_end)
∨ True)` becomes `… ∨ SeqTopKey s_prep)`.  Every supplier that declined with `Or.inr trivial`
(the three split builders' `hmem`-false branches and the frameless suppliers
`OpenerFallbackReach` lists) stops compiling; the breaks are the roster that must pay the
face, route, or declare a decline at `[211]`.

Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`, classifies with
`lake exe scripts-flip-census`, restores; md5 printed both sides.  FLOOR: one build of the library
(every application lives in `StreamAccum.lean`; guard modules behind it that spell the binder
are unmeasured proof repairs).  `--dry` patches nothing and reports the sites; `--keep`
leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
OPENERS = ("colon_open_map", "question_open_map", "indicator_open_map")
HEAD = "    (h_res_land : (∃ ks : List FrameLevel, (∀ fr ∈ ks, fr.width < k) ∧\n"
TAIL_OLD = "        ResumeFrames (SLYamlStream sp_start) ks sp_end) ∨ True)\n"
TAIL_NEW = "        ResumeFrames (SLYamlStream sp_start) ks sp_end) ∨ SeqTopKey s_prep)\n"

def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()

def patch(text):
    lines = text.splitlines(keepends=True); n = 0; i = 0
    while i < len(lines):
        if any(lines[i].startswith(f"lemma {o} ") or lines[i].rstrip("\n") == f"lemma {o}" for o in OPENERS):
            j = i
            while lines[j] != HEAD: j += 1
            if lines[j + 2] != TAIL_OLD: sys.exit(f"{lines[i].strip()}: h_res_land's tail moved; refusing")
            lines[j + 2] = TAIL_NEW; n += 1; i = j + 3
        else: i += 1
    if n != 3: sys.exit(f"expected 3 openers, patched {n}")
    return "".join(lines)

def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    if TAIL_NEW in SRC.read_text(): sys.exit("the face is already on h_res_land: priced/landed, see DOCS item 377")
    before = md5(SRC); orig = SRC.read_text(); new = patch(orig)
    print(f"md5 before: {before}\nsites: 3 h_res_land binders ({', '.join(OPENERS)}) take `∨ SeqTopKey s_prep`")
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/377-flip-res-land-split-build.log"; log.parent.mkdir(exist_ok=True)
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
