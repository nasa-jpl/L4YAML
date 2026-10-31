#!/usr/bin/env python3
"""Price item 412 (α): the `?` park's chain ONE FRAME UP carried in `pendingMapValue.h_expl`.

Item 411 found the compact builder's four cover arms need an ANCESTORS' route whose premise is the
park's whole ENTRY, not its value node (`SBlockIndented n .blockIn` is `[185]`-wide at a `?` park and
`[196]`-wide at an implicit-key park; one node premise cannot serve both).  `question_open_map` and
`compact_open_map` already HOLD that route for the park they open — `h_explUp_chainD`:
`∃ ns, MarkedColsIn sc ns ∧ ∀ nv ∈ ns, ∀ sp_v, SBlockMapEntry k sp_ind sp_v → SIndent nv → GLit ':' →
SBlockIndented nv .blockOut → ResumeFrames … [FrameLevel.map nv]` (item 197).  (α) carries it into the
field: `h_expl`'s `?` disjunct gains a fourth component, the domained up-chain over the park's own entry
(`∨ PackAlt sc`), so the compact builder routes an ancestor's mark by `SBlockMapEntry.explicitEmpty`
(the inner `?` key with no own value, then the outer `:`), its own mark by the compact route as before
item 409, and relays the chain's `PackAlt` instead of writing `Or.inr trivial`.

The flip: (1) the field's and the consumer lemma's `h_expl` type gain the component; (2) the four arms
are rewritten to the routed shape (the `NotQuestionPark` arms stay declined — the explicit `:` park's
compact value under an outer `?`, `? ? a⏎  : - b⏎: c`, has no entry head here); (3) the two `?`
producers (`question_open_map`'s `Or.inl ⟨sp_ind, h_lit, h_route51F⟩`, `compact_open_map`'s
`h_expl105`) supply the component as `sorry`, so the build reports the SUPPLY as an obligation.  Every
other breakage is the price: three-field destructurings `⟨sp_q, h_qlit, route⟩` of the old `h_expl`
(`accum_flow_open_depth0`, `accum_block_pending`, the consumer's three sibling arms).  Read-only:
patch, `lake build L4YAML` (a FLOOR, one round), `scripts/flip_census.py`, restore; md5 both sides.
`--dry` prints the sites; `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
def chain(ind, n, sc, sp_q):
    return (f"{ind}((∃ ns : List Nat, RegisterWitness.MarkedColsIn {sc} ns ∧ ∀ nv ∈ ns,\n"
            f"{ind}  ∀ sp_v : SurfPos, SBlockMapEntry {n} {sp_q} sp_v →\n"
            f"{ind}  ∀ sp_i sp_c : SurfPos, SIndent nv sp_v sp_i → GLit ':' sp_i sp_c →\n"
            f"{ind}  ∀ sp_w : SurfPos, SBlockIndented nv .blockOut sp_c sp_w →\n"
            f"{ind}  ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_w) ∨ PackAlt {sc})")
FIELD_OLD = ("      (h_expl : (∃ sp_q : SurfPos, GLit '?' sp_q sp_scan ∧\n"
             "        ∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →\n"
             "        ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e →\n"
             "          SLYamlStream sp_start sp_e) ∨ NotQuestionPark sc)\n")
FIELD_NEW = ("      (h_expl : (∃ sp_q : SurfPos, GLit '?' sp_q sp_scan ∧\n"
             "        (∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →\n"
             "        ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e →\n"
             "          SLYamlStream sp_start sp_e) ∧\n"
             + chain("        ", "n", "sc", "sp_q") + ") ∨ NotQuestionPark sc)\n")
LEMMA_OLD = FIELD_OLD.replace("\n      ", "\n    ").replace("      (h_expl", "    (h_expl", 1)
LEMMA_NEW = ("    (h_expl : (∃ sp_q : SurfPos, GLit '?' sp_q sp_scan ∧\n"
             "      (∀ sp_v : SurfPos, SBlockMapEntry n sp_q sp_v →\n"
             "      ∀ sp_e : SurfPos, SCompactMapTail n sp_v sp_e →\n"
             "        SLYamlStream sp_start sp_e) ∧\n"
             + chain("      ", "n", "sc", "sp_q") + ") ∨ NotQuestionPark sc)\n")
E105_OLD = ("  have h_expl105 : (∃ sp_q : SurfPos, GLit '?' sp_q sp_scan' ∧\n"
            "      ∀ sp_v : SurfPos, SBlockMapEntry (n + 1 + m) sp_q sp_v →\n"
            "      ∀ sp_e : SurfPos, SCompactMapTail (n + 1 + m) sp_v sp_e →\n"
            "        SLYamlStream sp_start sp_e) ∨ NotQuestionPark s' :=\n")
E105_NEW = ("  have h_expl105 : (∃ sp_q : SurfPos, GLit '?' sp_q sp_scan' ∧\n"
            "      (∀ sp_v : SurfPos, SBlockMapEntry (n + 1 + m) sp_q sp_v →\n"
            "      ∀ sp_e : SurfPos, SCompactMapTail (n + 1 + m) sp_v sp_e →\n"
            "        SLYamlStream sp_start sp_e) ∧\n"
            + chain("      ", "(n + 1 + m)", "s'", "sp_q") + ") ∨ NotQuestionPark s' :=\n")
E105_BODY_OLD = ("    | Or.inr h => Or.inl ⟨sp_ind, h_qlit h, fun sp_v h_entry sp_e h_tail =>\n"
                 "        h_close_old sp_e (SBlockIndented.compactMap n ctx m sp_entry sp_ind sp_e h_ind\n"
                 "          (SCompactMap.mk (n + 1 + m) sp_ind sp_v sp_e h_entry h_tail))⟩\n")
E105_BODY_NEW = ("    | Or.inr h => Or.inl ⟨sp_ind, h_qlit h, fun sp_v h_entry sp_e h_tail =>\n"
                 "        h_close_old sp_e (SBlockIndented.compactMap n ctx m sp_entry sp_ind sp_e h_ind\n"
                 "          (SCompactMap.mk (n + 1 + m) sp_ind sp_v sp_e h_entry h_tail)), sorry⟩\n")
QOM_OLD = "           (Or.inl ⟨sp_ind, h_lit, h_route51F⟩)\n"
QOM_NEW = "           (Or.inl ⟨sp_ind, h_lit, h_route51F, sorry⟩)\n"
ARM = (
    "        -- Item 409: `[n]` is the `?` park's own column — marked in fact, but no face here says\n"
    "        -- so (the own-mark scanner lemma is unpaid), so under the domain this birth DECLINES.\n"
    "        | Or.inl _ => Or.inr trivial\n"
    "        -- …and `[]` would claim the park holds NO mark (`MarkedColsIn` is a cover): DECLINES.\n"
    "        | Or.inr _ => Or.inr trivial⟩\n")
ARM_NEW = (
    "        | Or.inl ⟨sp_q, h_qlit, route, chainUp⟩ => (match chainUp with\n"
    "            | Or.inl ⟨nsU, hdomU, up⟩ => Or.inl ⟨nsU, hdomU,\n"
    "                fun nv hnv sp h_bi sp_i sp_c h_iv h_lit sp_v h_sbi =>\n"
    "                  if hn : nv = n then by\n"
    "                    subst hn\n"
    "                    exact ResumeFrames.one (route sp_v (SBlockMapEntry.explicit _ sp_q sp_scan sp sp_i sp_c sp_v\n"
    "                      h_qlit (SBlockIndented_blockIn_to_blockOut h_bi) h_iv h_lit h_sbi))\n"
    "                  else up nv hnv sp (SBlockMapEntry.explicitEmpty n sp_q sp_scan sp h_qlit\n"
    "                    (SBlockIndented_blockIn_to_blockOut h_bi)) sp_i sp_c h_iv h_lit sp_v h_sbi⟩\n"
    "            | Or.inr h => Or.inr h)\n"
    "        -- Item 412: the explicit `:` park's compact value under an outer `?` has no entry head\n"
    "        -- here (`? ? a⏎  : - b⏎: c`): DECLINES.\n"
    "        | Or.inr _ => Or.inr trivial⟩\n")
def patch(text):
    sites = []
    for old, new, tag, want in ((FIELD_OLD, FIELD_NEW, "pendingMapValue.h_expl", 1), (LEMMA_OLD, LEMMA_NEW, "consumer h_expl", 1),
                                (E105_OLD, E105_NEW, "compact_open_map h_expl105 type", 1), (E105_BODY_OLD, E105_BODY_NEW, "compact_open_map supply → sorry", 1),
                                (QOM_OLD, QOM_NEW, "question_open_map supply → sorry", 1), (ARM, ARM_NEW, "compact builder arms", 2)):
        n = text.count(old)
        if n != want: sys.exit(f"{tag}: expected {want} match(es), got {n}")
        sites.append((tag, text[:text.index(old)].count("\n") + 1)); text = text.replace(old, new)
    return text, sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    orig = SRC.read_text()
    if "| Or.inl ⟨sp_q, h_qlit, route, chainUp⟩" in orig:
        sys.exit("the chain one frame up is already PAID on this tree (item 412); nothing to price")
    before = md5(SRC); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{t}@{ln}" for t, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/412-flip.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run([sys.executable, "scripts/flip_census.py", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-7000:]); print(c.stderr[-1500:], file=sys.stderr)
        txt = log.read_text(); print(f"sorry declarations: {txt.count('declaration uses')}; errors: {txt.count(': error:')}")
    finally:
        if not keep: SRC.write_text(orig); print(f"md5 after: {md5(SRC)} (restored={md5(SRC) == before})")
        else: print("--keep: patch left in place")
if __name__ == "__main__": main()
