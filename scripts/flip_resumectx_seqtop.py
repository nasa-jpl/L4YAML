#!/usr/bin/env python3
"""Item 374 price: give `ResumeKeyCtx` a `SeqTopKey s_prep` disjunct and read what breaks.

Rewrites the definition's closing `… ∨ True` to `… ∨ SeqTopKey s_prep) ∨ True` (opening paren
inserted at the def's first `((`), so every `Or.inr trivial` keeps typing and the breaks are the
sites that READ the left disjunct — the price of carrying the face, not of spelling it.  Builds
`L4YAML` only, classifies with `lake exe scripts-flip-census`, restores; md5 printed both sides.  The
count is a FLOOR scoped to library declarations (one build stops at the first failing module);
the guard modules that spell or apply `ResumeKeyCtx`/`resumectx_of_landing` are listed by file
as unmeasured proof repairs and pins.  `--dry` prints the patched definition; `--keep` leaves
the flipped source in place (for a hand build).  Refuses a tree where the disjunct has landed.
"""
import hashlib, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
NAMES = ("ResumeKeyCtx", "resumectx_of_landing")
LANDED = "SIndent k sp_land sp_prep ∧ SeqTopKey s_prep) ∧"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    lines = text.splitlines(keepends=True)
    i = next(k for k, l in enumerate(lines) if l.startswith("def ResumeKeyCtx "))
    j = next(k for k in range(i, len(lines)) if lines[k].rstrip().endswith("∨ True") and lines[k].startswith("    s_prep.simpleKey.pos"))
    assert lines[i + 1].startswith("  ((∃ (k : Nat)"), lines[i + 1]
    lines[i + 1] = "  (" + lines[i + 1]
    lines[j] = lines[j].rstrip()[: -len("∨ True")] + "∨ SeqTopKey s_prep) ∨ True\n"
    return "".join(lines), "".join(lines[i:j + 1])
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    if LANDED in SRC.read_text(): sys.exit("the disjunct has landed (DOCS item 374); the price was 2 declarations / 4 sites")
    before = md5(SRC); orig = SRC.read_text(); new, shown = patch(orig)
    print(f"md5 before: {before}\nsite: def ResumeKeyCtx (two lines)")
    if dry: print(shown); return
    SRC.write_text(new)
    if keep: print(f"kept; md5 now {md5(SRC)}"); return
    try:
        log = ROOT / "scratch/374-flip-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        if c.returncode != 0: sys.exit(f"scripts-flip-census exit={c.returncode}: {c.stderr.strip()}")
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        rest = {}
        for d in ("L4YAML", "Tests"):
            for f in (ROOT / d).rglob("*.lean"):
                if f == SRC: continue
                n = sum(f.read_text().count(w) for w in NAMES)
                if n: rest[str(f.relative_to(ROOT))] = n
        lib = sum(v for k, v in rest.items() if k.startswith("L4YAML/"))
        print(f"FLOOR: one build of `L4YAML`, stopped in StreamAccum.lean; the price above is the LIBRARY price "
              f"(library mentions outside StreamAccum: {lib}).  Unmeasured behind it: {sum(rest.values())} mentions in "
              f"{len(rest)} modules (guard proofs + censuses; grep, a roster to read, not a price):")
        for k in sorted(rest): print(f"  {rest[k]:3d}  {k}")
    finally:
        SRC.write_text(orig)
        after = md5(SRC); print(f"md5 after: {after} ({'restored' if after == before else 'NOT RESTORED'})")
        if after != before: sys.exit(2)
if __name__ == "__main__": main()
