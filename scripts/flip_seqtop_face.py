#!/usr/bin/env python3
"""Price item 372's face: `∨ SeqTopKey sc` on `ImplicitKeyPack`'s ROUTE conjunct.

`PropsKeyPack` is NOT flipped: its route is relayed into the state-free
`FlowBaseRoutes.key` rider at the props-flow open, where no `:` can refute the
face (lane (c)/(d)'s carrier, DOCS item 372).

Edits `StreamAccum.lean` in place — inserts the `SeqTopKey` definition ahead of
`ImplicitKeyPack` and widens the route conjunct of `ImplicitKeyPack`
to `(route) ∨ SeqTopKey sc` — builds the library, runs
`scripts-flip-census` on the log, and restores the file (both md5s printed).  The
broken declarations are the producers that build the conjunct bare and the
consumers that spend it as a function; that roster is the item's price.

    scripts/flip_seqtop_face.py            # price: edit, build, census, restore
    scripts/flip_seqtop_face.py --keep     # apply the edit and stop (the item's first step)
    scripts/flip_seqtop_face.py --dry      # report the sites only

Exits non-zero when a marker is missing or already flipped: a build on an
unchanged file prices a no-op (§9).
"""
import hashlib, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
DOC = "/-- The implicit-key pack (item 15)"
ROUTE_I = "  ∃ (k : Nat) (sp_key sp_gram : SurfPos),\n    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∧\n"
SEQTOP = '''/-- **The landing on a sequence top** (item 372): the saved key's column is the
    scanner's top level and that level is a SEQUENCE — `- a⏎b: 1`'s `b` — which
    §8.2.1 refuses at the `:` (`scanValue_top_not_sequence`).  A key pack's route
    may decline into this face where the frames cover the stack and name no level
    at the landing (`preprocess_landing_mem_or_seq`'s right disjunct); the `:`
    consumers refute it. -/
def SeqTopKey (sc : ScannerState) : Prop :=
  (sc.indents.back?.map fun e =>
    e.isSequence && e.column == (sc.simpleKey.pos.col : Int)) = some true

'''
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def patch(text):
    for m, name in ((DOC, "pack docstring"), (ROUTE_I, "ImplicitKeyPack route")):
        if text.count(m) != 1:
            sys.exit(f"marker for {name} found {text.count(m)} times; nothing to price")
    if "def SeqTopKey" in text:
        sys.exit("SeqTopKey already present: the face is landed, the price is DOCS item 372")
    text = text.replace(DOC, SEQTOP + DOC, 1)
    text = text.replace(ROUTE_I, "  ∃ (k : Nat) (sp_key sp_gram : SurfPos),\n    ((∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∨ SeqTopKey sc) ∧\n", 1)
    return text
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    before = md5(SRC); orig = SRC.read_text()
    new = patch(orig)
    print(f"md5 before: {before}\nsites: 2 (SeqTopKey def, ImplicitKeyPack route)")
    if dry: return
    SRC.write_text(new)
    if keep: print(f"kept; md5 now {md5(SRC)}"); return
    try:
        log = ROOT / "scratch/372-flip-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
    finally:
        SRC.write_text(orig)
        print(f"md5 after: {md5(SRC)} ({'restored' if md5(SRC) == before else 'NOT RESTORED'})")
if __name__ == "__main__": main()
