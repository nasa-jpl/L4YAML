module

public import L4YAML.Proofs.Production.StreamAccum

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-! # `FlowStackK`'s floor is real (DOCS item 84)

The keystone: the invariant's floor conjunct is `n ≤ minContentIndentOf sc`
outright.  The collapse re-indexes at 0 (free), the depth-0 stack is at 0, and
every OPEN measures now — the parks' floors are unconditional (items
73/82/83), and the landing's column is derived from the WALK
(`preprocess_some_separate_at_floor` hands the separator and the floor
together: inline off the stability the floor's own `needIndentCheck = false`
buys, landed off the landing's own `s-indent(n)`) instead of asked of the
pack, which retires the open's `h_ncol` reads.

What it bought at once: `h_lead_at`'s negative arm — `¬ (nn ≤
minContentIndentOf sc)` — refutes against the floor, so SIX `dropClose` sites
became refutations (the interior separator's run-end half at the content and
`:`-receiving arms).  The 17 that remain are the named residues: the
`:`-closure's 0-index ARGUMENT (6), `InteriorGap`'s index (3+3), the node at
`nn` (2), the tuple fallback (3, fed by those), and `pendingFlow`'s own ride
(1) — none of them floor-shaped.

§1 pins the conjunct; §2 measures the floor's transport fact — inside an open
flow the indent stack never moves.
-/

namespace Tests.Guards.FlowStackFloorReal

open L4YAML L4YAML.Scanner L4YAML.Surface L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.PreprocessIndentStable L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.FlowIndexLift L4YAML.Proofs.LandingTab L4YAML.Proofs.EntryBoundaryLayout

/-! ## §1  The conjunct is bare -/

example {sp_start : SurfPos} {sc : ScannerState} {fl : Nat} {ks : Array Bool}
    {tl : FrameTail} {sp_block sp_flow : SurfPos}
    (h : FlowStackK sp_start sc fl ks tl sp_block sp_flow) :
    ∃ n, n ≤ minContentIndentOf sc := by
  obtain ⟨n, -, -, -, -, -, h_floor, -⟩ := h
  exact ⟨n, h_floor⟩

/-- ...and the separator arrives WITH its floor at the open. -/
example {n : Nat} {sc s_prep : ScannerState} {sp : SurfPos} {c : Char}
    (h_floor : IndentFloor sc n)
    (hcorr : ScannerSurfCorr sc sp)
    (hok : scanNextToken_preprocess sc = .ok (some (s_prep, c))) :
    ∃ sp_prep, ScannerSurfCorr s_prep sp_prep ∧
      (((SSeparateLines n sp sp_prep ∨ (sp_prep = sp ∧ 0 < sp.col)) ∧
          n ≤ minContentIndentOf s_prep) ∨
        ∃ sp_mid, SSLComments sp sp_mid ∧ sp_mid.col = 0 ∧
          WhiteRunUnderRun n sp_mid sp_prep ∧
          LandingTabFacts sc.currentIndent sc.needIndentCheck s_prep.peek? sp sp_mid ∧
          (sp.col ≠ 0 → s_prep.inFlow = false →
            (s_prep.currentIndent ≤ (s_prep.col : Int) ∨
              s_prep.indents.size ≤ 1)) ∧
          (sp.col ≠ 0 → s_prep.inFlow = false → s_prep.simpleKeyAllowed = true)) :=
  preprocess_some_separate_at_floor n sc sp s_prep c h_floor hcorr hok

/-! ## §2  The measurement: inside a flow, nothing writes the indent stack

The floor transports across every interior step because §6.1's unwind and both
block pushes are `!inFlow`-guarded (`FlowIndentStable`) — measured here at
every step taken at `flowLevel ≥ 1`, over interiors that cross lines, hold
properties, quoted folds and nested collections.  `flowSeen` witnesses the
steps fire. -/

private def flowStableLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => true
  | fuel' + 1 =>
    match scanNextToken s with
    | .error _ => true
    | .ok none => true
    | .ok (some s') =>
      (!(0 < s.flowLevel) || s'.indents == s.indents) && flowStableLoop s' fuel'

private def flowStable (input : String) : Bool :=
  flowStableLoop (ScannerState.mk' input) 128

private def flowSeenLoop (s : ScannerState) (fuel : Nat) : Bool :=
  match fuel with
  | 0 => false
  | fuel' + 1 =>
    (0 < s.flowLevel) ||
      match scanNextToken s with
      | .error _ => false
      | .ok none => false
      | .ok (some s') => flowSeenLoop s' fuel'

private def flowSeen (input : String) : Bool :=
  flowSeenLoop (ScannerState.mk' input) 128

#guard flowSeen "[1, 2]\n"
#guard flowSeen "k:\n  a: [1,\n    2]\n"
#guard flowStable "[1, 2]\n"
#guard flowStable "k: [1, 2]\n"
#guard flowStable "k:\n  a: [1,\n    2]\n"
#guard flowStable "k:\n  a: [\"p\n     q\", 2]\n"
#guard flowStable "k:\n  a: [&x b, {c: d}, [e]]\n"
#guard flowStable "- [1, [2, [3]]]\n"
#guard flowStable "{a: [1,\n  2], b: c}\n"

/-! ## §3  The `.value`-tail colon route reads at the stack's index (item 85)

The packaged case split's closure takes `SSeparateLines n` — the stack's own
`n`, not 0 — so the producers hand their separator straight through and the
consumer derives the at-`n` reading off the floor.  Pinned by applying the
promise at an abstract index. -/

example {sp_start : SurfPos} {sc : ScannerState} {fl : Nat} {ks : Array Bool}
    {sp_block sp_flow sp_prep sp_tok : SurfPos}
    (h : FlowStackK sp_start sc fl ks .value sp_block sp_flow)
    (h_fl : 0 < fl) :
    ∃ n kc km g, KeyAfterValueLayout sc ∨
      (SSeparateLines n sp_flow sp_prep → GLit ':' sp_prep sp_tok →
        FlowStackB sp_start n kc g fl ks km .colon sp_block sp_tok) := by
  obtain ⟨n, kc, km, g, -, -, -, h_prom⟩ := h
  exact ⟨n, kc, km, g, ((h_prom h_fl).2.2 rfl).imp id (fun f => f sp_prep sp_tok)⟩

end Tests.Guards.FlowStackFloorReal

end Blanket
