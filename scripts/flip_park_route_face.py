"""Price item 376's decline face on the parks' plain route field (DOCS item 376):
`PendingNode.pendingMapValue.h_close` and `PendingNode.pendingBlock.h_close` become
`(∀ sp_mid, … → SLYamlStream sp_start sp_mid) ∨ PackAlt sc`, so every producer that
fills the field must wrap its route in `Or.inl` (or declare `Or.inr` — the sink item
375's seven/eight class-(A) fallback arms lack) and every consumer that applies the
field as a function must match it.  The breaks are the roster of the face.

Edits `L4YAML/Proofs/Production/StreamAccum.lean` in place, builds `L4YAML`,
classifies with `lake exe scripts-flip-census`, restores; md5 printed both sides.  The
count is a FLOOR (one build of the library stops at the first failing module): the
guard modules behind `StreamAccum.lean` that spell the field's type (`example`
mirrors, park walkers) are unmeasured proof repairs beyond the price (item 373's
review lesson).  `--dry` patches nothing and reports the sites; `--keep` leaves
the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
FIELDS = {
    "pendingMapValue": ("      (h_close : ∀ sp_mid,\n"
                        "        SBlockNode (n + 1) .blockIn sp_scan sp_mid →\n"
                        "        SLYamlStream sp_start sp_mid)\n",
                        "      (h_close : (∀ sp_mid,\n"
                        "        SBlockNode (n + 1) .blockIn sp_scan sp_mid →\n"
                        "        SLYamlStream sp_start sp_mid) ∨ PackAlt sc)\n"),
    "pendingBlock": ("      (h_close : ∀ sp_mid,\n"
                     "        SBlockIndented n .blockIn sp_scan sp_mid →\n"
                     "        SLYamlStream sp_start sp_mid)\n",
                     "      (h_close : (∀ sp_mid,\n"
                     "        SBlockIndented n .blockIn sp_scan sp_mid →\n"
                     "        SLYamlStream sp_start sp_mid) ∨ PackAlt sc)\n"),
}

def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()

def patch(text):
    for ctor, (old, new) in FIELDS.items():
        head = f"  | {ctor} (sp_start sp_block sp_scan : SurfPos) (n : Nat)\n"
        i = text.find(head)
        if i < 0: sys.exit(f"constructor {ctor} not found; refusing")
        j = text.find(old, i)
        if j < 0 or j - i > 200: sys.exit(f"{ctor}.h_close is not the plain route field (moved?); refusing")
        text = text[:j] + new + text[j + len(old):]
    return text

def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    if "SLYamlStream sp_start sp_mid) ∨ PackAlt sc)" in SRC.read_text():
        sys.exit("the face is already on a park route field: priced/landed, see DOCS item 376")
    before = md5(SRC); orig = SRC.read_text(); new = patch(orig)
    print(f"md5 before: {before}\nsites: 2 park route fields ({', '.join(FIELDS)}.h_close) take `∨ PackAlt sc`")
    if dry: return
    SRC.write_text(new)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/376-flip-park-route-face-build.log"; log.parent.mkdir(exist_ok=True)
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
