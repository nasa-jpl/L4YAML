#!/usr/bin/env python3
"""Price item 413: `compact_open_map`'s chain ONE FRAME UP supplied from the `-` park.

Item 412 carried the `?` park's ancestors' chain into `pendingMapValue.h_expl` over the park's own
ENTRY; `question_open_map` supplied it from `h_explUp_chainD`, `compact_open_map` had no premise to
read it from and DECLINED (`Or.inr trivial`).  The supply is the chain its two callers already hold
over the `-` (or slot) park's CONTENT — `accum_block_on_closeThenBlock`'s `hkv`/`hkvUp` (the open
slot's own route + ancestors, domain `MarkedColsIn sc (nv :: nsU)`) and `pendingBlock.h_kslotUp`
(`SBlockIndented n .blockIn sp_scan → SCompactSeqTail n → …`) — restated as ONE premise on the
projection: `∀ nv ∈ markedCols sc, ∀ sp_m, SBlockIndented n ctx sp_entry sp_m → SIndent nv → ':' →
SBlockIndented nv .blockOut → ResumeFrames … [map nv]) ∨ PackAlt sc`, plus the mark step of the
compact `?`'s push (`h_mcstep`, the callers' own).  Inside, the entry is wrapped into the content
(`SBlockIndented.compactMap … (SCompactMap.mk … entry (SCompactMapTail.nil …))`) and a mark of `s'`
is the own column (excluded by `nv ≠ n + 1 + m`) or one of `sc`'s (`h_mcstep` on `markedCols sc`).

The flip: the two premises are added to the lemma, its decline becomes `sorry` (the SUPPLY is the
obligation), and both callers pass `sorry sorry` (the RELAY is the obligation) — so the build reports
the price as the declarations that carry `sorry`: a STARVED caller is one whose `sorry` no held fact
can replace.  Read-only: patch, `lake build L4YAML` (a FLOOR, one round), `lake exe scripts-flip-census`,
restore; md5 both sides.  `--dry` prints the sites; `--keep` leaves the patch in place.
"""
import hashlib, subprocess, sys
from pathlib import Path
ROOT = Path(__file__).resolve().parent.parent
SRC = ROOT / "L4YAML/Proofs/Production/StreamAccum.lean"
def md5(p): return hashlib.md5(p.read_bytes()).hexdigest()
SIG_OLD = ("    (h_outer : (PendingKeySound.Sound s_prep ∧ RegisterWitness.MarkedColsIn s_prep [n + 1 + m] ∧\n"
           "      (s_prep.simpleKey.possible = true → s_prep.simpleKey.pos.col = s_prep.col)) ∨ True) :\n"
           "    ∃ sp_gram' sp_block' sp_flow' sp_scan',\n")
PREMISES = ("    (h_chainUp : (∀ nv ∈ RegisterWitness.markedCols sc,\n"
            "      ∀ sp_m : SurfPos, SBlockIndented n ctx sp_entry sp_m →\n"
            "      ∀ sp_i sp_c : SurfPos, SIndent nv sp_m sp_i → GLit ':' sp_i sp_c →\n"
            "      ∀ sp_v : SurfPos, SBlockIndented nv .blockOut sp_c sp_v →\n"
            "      ResumeFrames (SLYamlStream sp_start) [FrameLevel.map nv] sp_v) ∨ PackAlt sc)\n"
            "    (h_mcstep : ∀ ns : List Nat, RegisterWitness.MarkedColsIn sc ns →\n"
            "      RegisterWitness.MarkedColsIn s' ((s_prep.col : Int).toNat :: ns))")
SIG_NEW = SIG_OLD.replace(" ∨ True) :\n", " ∨ True)\n" + PREMISES + " :\n")
BODY_OLD = ("        -- callers with a mark step for the compact `?`'s push (item 413): DECLINES.\n"
            "        Or.inr trivial⟩\n")
BODY_NEW = ("        -- callers with a mark step for the compact `?`'s push (item 413): DECLINES.\n"
            "        sorry⟩\n")
CALL1_OLD = ("                    fun _ => (preprocess_saved_key_col hp.1 h_noflow h_preprocess).2⟩)\n"
             "                (fun _ => Or.inr trivial)) (fun _ => Or.inr trivial))\n")
CALL1_NEW = CALL1_OLD + "              sorry sorry\n"
CALL2_OLD = ("            (h_kslotUp.elim (fun ⟨ns, hdom, _⟩ => if hns : ∀ x ∈ ns, x = n + 1 + m\n"
             "              then Or.inl ⟨PendingKeySound.preprocess_sound h_preprocess h_sound h_mono,\n"
             "                (RegisterWitness.preprocess_markedCols h_preprocess hdom).mono (fun x hx => List.mem_singleton.2 (hns x hx)),\n"
             "                fun _ => (preprocess_saved_key_col h_sk h_noflow h_preprocess).2⟩\n"
             "              else Or.inr trivial) (fun _ => Or.inr trivial))\n")
CALL2_NEW = CALL2_OLD + "            sorry sorry\n"
def patch(text):
    sites = []
    for old, new, tag in ((SIG_OLD, SIG_NEW, "compact_open_map premises"), (BODY_OLD, BODY_NEW, "compact_open_map supply → sorry"),
                          (CALL1_OLD, CALL1_NEW, "accum_block_on_closeThenBlock relay → sorry"), (CALL2_OLD, CALL2_NEW, "pendingBlock arm relay → sorry")):
        n = text.count(old)
        if n != 1: sys.exit(f"{tag}: expected 1 match, got {n}")
        sites.append((tag, text[:text.index(old)].count("\n") + 1)); text = text.replace(old, new)
    return text, sites
def main():
    dry, keep = "--dry" in sys.argv, "--keep" in sys.argv
    if subprocess.run(["git", "status", "--porcelain", str(SRC)], cwd=ROOT, capture_output=True, text=True).stdout.strip():
        sys.exit("StreamAccum.lean is not clean; refusing to flip")
    orig = SRC.read_text()
    if "(h_chainUp :" in orig:
        sys.exit("the chain one frame up is already carried on this tree (item 413); nothing to price")
    before = md5(SRC); new, sites = patch(orig)
    print(f"md5 before: {before}\nsites: " + ", ".join(f"{t}@{ln}" for t, ln in sites))
    if dry: return
    SRC.write_text(new)
    try:
        log = ROOT / "scratch/413-flip.log"; log.parent.mkdir(exist_ok=True)
        with log.open("w") as f:
            r = subprocess.run(["lake", "build", "L4YAML"], cwd=ROOT, stdout=f, stderr=subprocess.STDOUT)
        print(f"lake build L4YAML exit={r.returncode}; log {log}")
        c = subprocess.run(["lake", "exe", "scripts-flip-census", str(log)], cwd=ROOT, capture_output=True, text=True)
        print(c.stdout[-7000:]); print(c.stderr[-1500:], file=sys.stderr)
        txt = log.read_text(); print(f"sorry declarations: {txt.count('declaration uses')}; errors: {txt.count(': error:')}")
    finally:
        if not keep: SRC.write_text(orig); print(f"md5 after: {md5(SRC)} (restored={md5(SRC) == before})")
        else: print("--keep: patch left in place")
if __name__ == "__main__": main()
