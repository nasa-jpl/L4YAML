#!/usr/bin/env python3
"""Item 416's flip: `pendingProps.h_kslotE` DOMAINED over the projection.
The field's informative side carries a BARE `∃ nv` (one column, no domain); the six
`accum_content_pending` sites that read it (`h_kslotE_k`) owe `∀ nv ∈ markedCols s'` and so
decline (item 415's stopped DOMAIN class).  This script restates the FIELD as
`∃ ne, n = ne + 1 ∧ ∀ nv ∈ RegisterWitness.markedCols sc, …` and the one `have h_kslotE_k`
specialisation (read at six sites) as `∀ nv ∈ RegisterWitness.markedCols sc, …`, builds `L4YAML`, and reports every
error with its enclosing declaration — the PRODUCERS that can no longer supply the field (STARVED
or re-shapeable) and any other reader that breaks — then restores `StreamAccum.lean`
byte-identically (both md5s printed).  Read-only in effect; never run it beside another
`lake build`.  `--keep` leaves the patched tree in place (the pay's starting point).

The anchors are the field's text BEFORE the pay, so on the paid tree the probe would stop before
building.  It therefore prices a REVISION, not the checkout: `--rev REV` (default `BASE_REV`, the
merged #189 the item cut from) takes `StreamAccum.lean` from `git show REV:…`, patches that copy
into the working tree, builds, and restores the working tree's own bytes.  It refuses when any
OTHER library file differs between REV and HEAD (the build would read a mixed tree) — run it in a
`git worktree` of REV in that case.  Example: `python3 scripts/flip_kslote_domain.py --rev 55d03804`."""
import argparse, hashlib, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
FIELD_OLD = """      (h_kslotE : (∃ (ne nv : Nat), n = ne + 1 ∧
        ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →"""
FIELD_NEW = """      (h_kslotE : (∃ ne : Nat, n = ne + 1 ∧
        ∀ nv ∈ RegisterWitness.markedCols sc,
        ∀ sp_m : SurfPos, SBlockNode n .blockIn sp_node sp_m →"""
HAVE_OLD = """              have h_kslotE_k : (∃ nv : Nat,
                  ∀ sp_m : SurfPos, SBlockNode (k + 1) .blockIn sp_node sp_m →"""
HAVE_NEW = """              have h_kslotE_k : (∀ nv ∈ RegisterWitness.markedCols sc,
                  ∀ sp_m : SurfPos, SBlockNode (k + 1) .blockIn sp_node sp_m →"""
PROOF_OLD = """                rcases h_kslotE_p with ⟨ne, nv, hne, r⟩ | h_alt
                · obtain rfl : ne = k := by omega
                  exact Or.inl ⟨nv, r⟩"""
PROOF_NEW = """                rcases h_kslotE_p with ⟨ne, hne, r⟩ | h_alt
                · obtain rfl : ne = k := by omega
                  exact Or.inl r"""
BASE_REV = "55d03804"  # merged #189 (item 415): the revision whose field text the anchors name
REL = "L4YAML/Proofs/Production/StreamAccum.lean"
ap = argparse.ArgumentParser(description="price item 416's field change at a revision")
ap.add_argument("--rev", default=BASE_REV, help=f"revision holding the un-paid field (default {BASE_REV})")
ap.add_argument("--keep", action="store_true", help="leave the patched tree in place")
args = ap.parse_args()
git = lambda *a: subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
others = git("diff", "--quiet", args.rev, "--", "L4YAML", f":!{REL}")  # REV vs the WORKING TREE: uncommitted edits count
if others.returncode != 0:
    sys.exit(f"library files other than {REL} differ between {args.rev} and the working tree; "
             f"run the probe in a `git worktree` of {args.rev} instead")
shown = git("show", f"{args.rev}:{REL}")
if shown.returncode != 0:
    sys.exit(f"cannot read {REL} at {args.rev}: {shown.stderr.strip()}")
md5 = lambda: hashlib.md5(SRC.read_bytes()).hexdigest()
orig = SRC.read_bytes(); m0 = md5(); t = shown.stdout
print(f"pricing {REL} at {args.rev} (working tree md5 {m0[:12]})", flush=True)
for old, new, want in ((FIELD_OLD, FIELD_NEW, 1), (HAVE_OLD, HAVE_NEW, 1), (PROOF_OLD, PROOF_NEW, 1)):
    if t.count(old) != want:
        sys.exit(f"anchor count {t.count(old)} != {want} for:\n{old[:80]}")
    t = t.replace(old, new)
lines = t.split("\n")
def decl_of(ln):
    for i in range(ln - 1, -1, -1):
        m = re.match(r"(?:private |protected )?(?:lemma|theorem|def|inductive) (\S+)", lines[i])
        if m: return m[1]
    return "?"
try:
    SRC.write_text(t)
    print(f"flip tree md5 {md5()[:12]}; building L4YAML …", flush=True)
    r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, capture_output=True, text=True)
    out = r.stdout + r.stderr
    errs = re.findall(r"^error: L4YAML/Proofs/Production/StreamAccum\.lean:(\d+):(\d+): (.*)$", out, re.M)
    by = {}
    for ln, col, msg in errs:
        by.setdefault(decl_of(int(ln)), []).append((int(ln), msg[:100]))
    print(f"KSLOTE-FLIP exit={r.returncode} errors={len(errs)} decls={len(by)}")
    for d, es in by.items():
        print(f"  {d}: {len(es)} site(s)")
        for ln, msg in es: print(f"    {ln}: {msg}")
    (ROOT / "scratch").mkdir(exist_ok=True)
    (ROOT / "scratch/kslote_flip.log").write_text(out)
finally:
    if args.keep:
        print(f"--keep: patched copy of {args.rev}:{REL} left in place (md5 {md5()[:12]}; working tree was {m0[:12]})")
    else:
        SRC.write_bytes(orig)
        print(f"restored md5 {md5()[:12]} (orig {m0[:12]}) identical={md5() == m0}")
