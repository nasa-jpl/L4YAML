#!/usr/bin/env python3
"""Item 417's flip: `colon_open_map`'s statement-shaped decline RELAYED from the entry chain.
The `:` opener fills the new park's `pendingMapValue.h_kslot` (a domained NODE chain,
`∃ ns, MarkedColsIn s' ns ∧ ∀ nv ∈ ns, ∀ sp_m, SBlockNode (k+1) .blockIn sp_scan' sp_m → …`) by
`| Or.inl ⟨nv, _, _, contV⟩ => Or.inr trivial` off `h_resV_land` — a FRAMES fact at one `nv`, no
domain (item 415's stopped class G).  Its single caller `indicator_open_map` HOLDS the chain over
the ENTRY (`h_explUp_chainD`, item 412) and hands it only to `question_open_map`; the `:` arm
builds that entry from the node (`SBlockMapEntry.emptyKeyNode`), so the owed chain is the held
one at the built entry, with the domain carried across the `:` by a mark step (`h_mcstep_ne`, the
`c ≠ '?'` twin `accum_block_pending` already builds).  This script adds the two premises to
`colon_open_map`, restates the decline as the pay, adds `h_mcstep_ne` to `indicator_open_map`
and relays both at its call, builds `L4YAML`, and reports every error with its enclosing
declaration — the CALLERS that must now supply the step (STARVED if none holds it) — then
restores `StreamAccum.lean` byte-identically (both md5s printed).  Read-only in effect; never run
it beside another `lake build`.  `--keep` leaves the patched tree in place (the pay's start).

The anchors are the text BEFORE the pay, so the probe prices a REVISION: `--rev REV` (default
`BASE_REV`, the merged #190 the item cut from) takes `StreamAccum.lean` from `git show REV:…`,
patches that copy into the working tree, builds, and restores the working tree's own bytes.  It
refuses when any OTHER library file differs between REV and the WORKING TREE (uncommitted edits
count) — run it in a `git worktree` of REV in that case."""
import argparse, hashlib, re, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
REL = "L4YAML/Proofs/Production/StreamAccum.lean"
SRC = ROOT / REL
BASE_REV = "b377aadc"  # merged #190 (item 416)
COLON_HDR_OLD = """    (h_alt_step : PackAlt sc → PackAlt s')
"""
COLON_HDR_NEW = """    (h_alt_step : PackAlt sc → PackAlt s')
    -- **Item 417: the `?` chain ONE FRAME UP over the entry this `:` builds** (item 412's
    -- `h_explUp_chainD`, relayed by the caller) and the `:`'s own mark step — a `:` adds no
    -- mark (`h_mcstep_ne`).  The new park's `h_kslot` is this chain read at the `[189]` entry.
    (h_explUp_chainD : (∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv ∈ ns,
      ∀ sp_v : SurfPos, SBlockMapEntry k sp_ind sp_v →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →
      ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) ∨ PackAlt sc)
    (h_mstep : ∀ ns : List Nat, RegisterWitness.MarkedColsIn sc ns →
      RegisterWitness.MarkedColsIn s' ns)
"""
PAY_OLD = """           (match h_resV_land with
            | Or.inl ⟨nv, _, _, contV⟩ => Or.inr trivial
            | Or.inr h_alt => Or.inr (h_alt_step h_alt))
"""
PAY_NEW = """           -- **Item 417: PAID from the caller's chain one frame up** — `h_resV_land` is a
           -- frames fact at one level and cannot domain the slot; `h_explUp_chainD` is the same
           -- chain over EVERY marked column at the `[189]` entry this `:` builds from the node.
           (match h_explUp_chainD with
            | Or.inl ⟨ns, hdom, chain⟩ =>
                Or.inl ⟨ns, h_mstep ns hdom,
                  fun nv hmem sp_m h_node =>
                    chain nv hmem sp_m
                      (SBlockMapEntry.emptyKeyNode k sp_ind sp_scan' sp_m h_lit
                        (SBlockNode_blockIn_to_blockOut h_node))⟩
            | Or.inr h_alt => Or.inr (h_alt_step h_alt))
"""
IND_HDR_OLD = """    (h_top_prep : s_prep.currentIndent ≤ (s_prep.col : Int))
    (h_explUp_chainD : (∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv ∈ ns,
      ∀ sp_v : SurfPos, SBlockMapEntry k sp_ind sp_v →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →
      ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) ∨ PackAlt sc)
    (h_mcstep : ∀ ns : List Nat, RegisterWitness.MarkedColsIn sc ns →
      RegisterWitness.MarkedColsIn s' ((s_prep.col : Int).toNat :: ns)) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none s' 0 #[] #[] .sep sp_block' sp_flow' ∧"""
IND_HDR_NEW = """    (h_top_prep : s_prep.currentIndent ≤ (s_prep.col : Int))
    (h_explUp_chainD : (∃ ns : List Nat, RegisterWitness.MarkedColsIn sc ns ∧ ∀ nv ∈ ns,
      ∀ sp_v : SurfPos, SBlockMapEntry k sp_ind sp_v →
      ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →
      ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →
      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) ∨ PackAlt sc)
    (h_mcstep : ∀ ns : List Nat, RegisterWitness.MarkedColsIn sc ns →
      RegisterWitness.MarkedColsIn s' ((s_prep.col : Int).toNat :: ns))
    -- Item 417: the `:` twin of the step — a non-`?` indicator adds no mark — relayed to
    -- `colon_open_map` for its `h_kslot`.
    (h_mcstep_ne : c ≠ '?' → ∀ ns : List Nat, RegisterWitness.MarkedColsIn sc ns →
      RegisterWitness.MarkedColsIn s' ns) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none s' 0 #[] #[] .sep sp_block' sp_flow' ∧"""
IND_CALL_OLD = """      (PackAlt.step_value h_preprocess h_dispatch (noflow_of_noflow_disp h_noflow_disp))
      (indicator_top_kv_at_col (Or.inl rfl) hcol_ind hcorr_prep h_save h_noflow_disp h_top_prep h_dispatch)
  | inr h =>"""
IND_CALL_NEW = """      (PackAlt.step_value h_preprocess h_dispatch (noflow_of_noflow_disp h_noflow_disp))
      h_explUp_chainD (h_mcstep_ne (by decide))
      (indicator_top_kv_at_col (Or.inl rfl) hcol_ind hcorr_prep h_save h_noflow_disp h_top_prep h_dispatch)
  | inr h =>"""
ap = argparse.ArgumentParser(description="price item 417's relay at a revision")
ap.add_argument("--rev", default=BASE_REV, help=f"revision holding the un-paid site (default {BASE_REV})")
ap.add_argument("--keep", action="store_true", help="leave the patched tree in place")
args = ap.parse_args()
git = lambda *a: subprocess.run(["git", *a], cwd=ROOT, capture_output=True, text=True)
others = git("diff", "--quiet", args.rev, "--", "L4YAML", f":!{REL}")  # REV vs the WORKING TREE
if others.returncode != 0:
    sys.exit(f"library files other than {REL} differ between {args.rev} and the working tree; "
             f"run the probe in a `git worktree` of {args.rev} instead")
shown = git("show", f"{args.rev}:{REL}")
if shown.returncode != 0:
    sys.exit(f"cannot read {REL} at {args.rev}: {shown.stderr.strip()}")
md5 = lambda: hashlib.md5(SRC.read_bytes()).hexdigest()
orig = SRC.read_bytes(); m0 = md5(); t = shown.stdout
print(f"pricing {REL} at {args.rev} (working tree md5 {m0[:12]})", flush=True)
for old, new in ((COLON_HDR_OLD, COLON_HDR_NEW), (PAY_OLD, PAY_NEW), (IND_HDR_OLD, IND_HDR_NEW), (IND_CALL_OLD, IND_CALL_NEW)):
    if t.count(old) != 1:
        sys.exit(f"anchor count {t.count(old)} != 1 for:\n{old[:90]}")
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
        by.setdefault(decl_of(int(ln)), []).append((int(ln), msg[:110]))
    print(f"COLON-FLIP exit={r.returncode} errors={len(errs)} decls={len(by)}")
    for d, es in by.items():
        print(f"  {d}: {len(es)} site(s)")
        for ln, msg in es: print(f"    {ln}: {msg}")
    (ROOT / "scratch").mkdir(exist_ok=True)
    (ROOT / "scratch/colon_flip.log").write_text(out)
finally:
    if args.keep:
        print(f"--keep: patched copy of {args.rev}:{REL} left in place (md5 {md5()[:12]}; working tree was {m0[:12]})")
    else:
        SRC.write_bytes(orig)
        print(f"restored md5 {md5()[:12]} (orig {m0[:12]}) identical={md5() == m0}")
