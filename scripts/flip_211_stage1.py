#!/usr/bin/env python3
"""Item 375 pricing instrument (PRICE BEFORE PROVING): the `[211]` flip, stage 1.

Question: once `SLYamlStream.implicitContinue` is narrowed to an EXPLICIT continued
document (`GOpt SLAnyDocument` → `GOpt SLExplicitDocument`), the four bare routes
(`bareNodeRoute`, `rootMapRoute`, `rootMapRouteF`, `topLevelFlowResumeSep`) are
deleted, `structural_dispatch_to_pending`'s explicit-document site is restated, and
the four `_or_refused` wrappers conclude `(route) ∨ True` with `Or.inr trivial` at
their two decline arms — which declarations break, and where?  Those sites are the
consumers that must take the disjunction: each needs a decline SINK (a `KeyPackPunt`,
a `∨ True` conclusion, or — where the result is a park's route field — none, which is
the reading DOCS item 375 records).

Edits `L4YAML/Surface/Document.lean` and `L4YAML/Proofs/Production/StreamAccum.lean`
in place, builds `L4YAML`, classifies with `lake exe scripts-flip-census`, restores; md5
printed both sides.  One build of the library is a FLOOR (first failing module).
`--dry` edits nothing; `--keep` leaves the flipped tree for a manual build.  Refuses
a dirty tree.  Reading recorded in DOCS item 375: 10 declarations / 25 sites.
"""
import hashlib, pathlib, subprocess, sys
ROOT = pathlib.Path(__file__).resolve().parent.parent
DOC = ROOT / "L4YAML/Surface/Document.lean"
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
ROUTES = ("bareNodeRoute", "rootMapRoute", "rootMapRouteF", "topLevelFlowResumeSep")
DECLS = ("lemma ", "def ", "theorem ", "/--", "abbrev ", "@[", "structure ", "inductive ",
         "end ", "namespace ", "section ", "private ", "protected ")
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def rep1(s, old, new):
    if s.count(old) != 1: sys.exit(f"anchor not unique/present: {old[:60]!r}")
    return s.replace(old, new)
def patch_doc(t):
    return rep1(t, "      GOpt SLAnyDocument s₂ s₃ →\n      GStar SLDocumentSuffix s₃ s' →\n      SLYamlStream s s'",
                   "      GOpt SLExplicitDocument s₂ s₃ →\n      GStar SLDocumentSuffix s₃ s' →\n      SLYamlStream s s'")
def patch_src(s):
    s = rep1(s, "          (GOpt.some sp sp_end\n            (SLAnyDocument.explicit sp sp_end\n              (SLExplicitDocument.withContent sp sp' sp_end h_marker h_content)))\n",
                "          (GOpt.some sp sp_end\n            (SLExplicitDocument.withContent sp sp' sp_end h_marker h_content))\n")
    for old, new in [
        ("    (h_ind : SIndent k sp_land sp_key) :\n    ∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v := by\n  cases h_op",
         "    (h_ind : SIndent k sp_land sp_key) :\n    (∀ sp_v, SBlockMapEntry k sp_key sp_v → SLYamlStream sp_start sp_v) ∨ True := by\n  cases h_op"),
        ("    (h_ind : SIndent k sp_land sp_key) :\n    ∀ sp_v, SBlockMapEntry k sp_key sp_v →\n    ∀ sp_e, SCompactMapTail k sp_v sp_e →\n    ResumeFrames (SLYamlStream sp_start) [] sp_e := by\n  cases h_op",
         "    (h_ind : SIndent k sp_land sp_key) :\n    (∀ sp_v, SBlockMapEntry k sp_key sp_v →\n    ∀ sp_e, SCompactMapTail k sp_v sp_e →\n    ResumeFrames (SLYamlStream sp_start) [] sp_e) ∨ True := by\n  cases h_op"),
        ("    (h_tail : CompletedTail sc ∨ True) :\n    ∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m →\n      SLYamlStream sp_start sp_m := by\n  cases h_op",
         "    (h_tail : CompletedTail sc ∨ True) :\n    (∀ sp_m, SBlockNode 0 .blockIn sp_anchor sp_m →\n      SLYamlStream sp_start sp_m) ∨ True := by\n  cases h_op"),
        ("    (h_sep : SSeparateLines 0 sp_mid sp_br) :\n    ∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →\n      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m := by\n  cases h_op",
         "    (h_sep : SSeparateLines 0 sp_mid sp_br) :\n    (∀ sp_ne sp_m, SFlowContent 0 .flowOut sp_br sp_ne →\n      SSLComments sp_ne sp_m → SLYamlStream sp_start sp_m) ∨ True := by\n  cases h_op"),
        ("    | Or.inr _ => exact rootMapRoute hcol0 h_stream_land h_ind\n  | true => exact rootMapRoute hcol0 h_stream_land h_ind",
         "    | Or.inr _ => exact Or.inr trivial\n  | true => exact Or.inr trivial"),
        ("    | Or.inr _ => exact rootMapRouteF hcol0 h_stream_land h_ind\n  | true => exact rootMapRouteF hcol0 h_stream_land h_ind",
         "    | Or.inr _ => exact Or.inr trivial\n  | true => exact Or.inr trivial"),
        ("    | Or.inr _ => exact bareNodeRoute h_stream\n  | true => exact bareNodeRoute h_stream",
         "    | Or.inr _ => exact Or.inr trivial\n  | true => exact Or.inr trivial"),
        ("    | Or.inr _ => exact topLevelFlowResumeSep h_stream h_sep\n  | true => exact topLevelFlowResumeSep h_stream h_sep",
         "    | Or.inr _ => exact Or.inr trivial\n  | true => exact Or.inr trivial"),
    ]: s = rep1(s, old, new)
    lines = s.splitlines(keepends=True)
    for name in ROUTES:   # delete docstring (from its `/--` opener) + body, up to the next blank line
        i = next(i for i, l in enumerate(lines) if l.startswith(f"lemma {name} "))
        j = i
        while j > 0 and not lines[j - 1].lstrip().startswith("/--"): j -= 1
        j -= 1
        k = i
        while k < len(lines) and lines[k].strip() != "": k += 1
        del lines[j:k + 1]
    return "".join(lines)
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    st = subprocess.run(["git", "status", "--porcelain", str(DOC), str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip()
    if st: sys.exit("Document.lean / StreamAccum.lean not clean; refusing to flip")
    bd, bs = md5(DOC), md5(SRC); od, os_ = DOC.read_text(), SRC.read_text()
    nd, ns = patch_doc(od), patch_src(os_)
    print(f"md5 before: Document {bd} StreamAccum {bs}\nsites: 1 narrowing + 1 restatement + 4 wrappers widened + 4 routes deleted")
    if dry: return
    DOC.write_text(nd); SRC.write_text(ns)
    if keep: print("kept (flipped tree left in place)"); return
    try:
        log = ROOT / "scratch/375-flip211-build.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        if c.returncode != 0: sys.exit(f"scripts-flip-census exit={c.returncode}: {c.stderr.strip()}")
        print(c.stdout[-8000:]); print(c.stderr[-2000:], file=sys.stderr)
        print("FLOOR: one build of `L4YAML`; guard modules behind it unmeasured.")
    finally:
        DOC.write_text(od); SRC.write_text(os_)
        print(f"md5 after: Document {md5(DOC)} StreamAccum {md5(SRC)} ({'restored' if (md5(DOC), md5(SRC)) == (bd, bs) else 'MISMATCH'})")
if __name__ == "__main__": main()
