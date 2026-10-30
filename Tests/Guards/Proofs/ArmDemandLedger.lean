import Tests.Guards.Proofs.ArmStrengthLadder

/-!
# The demand ledger: who still asks for the weak form (item 223)

Item 222 built the STRENGTH LADDER — for one fact held by a family of carriers,
the strongest form each carrier can state from its own fields — and read it at
6 of 9.  Item 223 paid the last three rungs, so the supply is uniform and lives
in the library as `PendingNode.arm_tight_or_col`, with no hypothesis but
`inFlow = false`.

A uniform supply changes nothing by itself.  This file is the other half of the
instrument, and the ledger row item 223 adds is the **DEMAND LEDGER**: for a
fact whose supply has just become uniform, which CONSUMERS still ask for the
weak form.  The ladder is a census of producers; this is a census of parameters,
taken by TYPE rather than by binder name — item 221's lesson, that a census
scoped to a literal under-reports where the literal hides.

## The demand, consumer by consumer

| consumer | asks | after item 223 |
|---|---|---|
| `preprocess_flow_thread` | loose | loose |
| `landing_or_park_save` | loose | loose |
| `landing_or_park_ska` | loose | loose |
| `flowKeyRoute_of_open` | loose | loose |
| `flowKeyRoute_of_root` | loose | loose |
| `keyctx_of_preprocess` | loose | loose |
| `accum_content_on_noPending` | loose | loose |
| `accum_block_on_noPending` | loose (`∨ inFlow`) | loose |
| **`accum_block_on_closeThenBlock`** | loose | **tight** |
| `accum_block_on_pendingContent` | tight (item 80) | tight |
| `accum_block_on_pendingBlockContent` | tight | tight |
| `colon_fires_implicit_key` | tight | tight |

Nine loose and three tight before; eight and four after.  **Tightening the
supply changes nothing until the demand is re-asked — a uniform producer met by
a weak parameter is strength thrown away at the door.**

## What re-asking ONE parameter cost, and what it paid

Tightening `accum_block_on_closeThenBlock.h_park` broke five definitions, and
the repairs split three ways:

* **four projections IN** — the lemma's own calls to `landing_or_park_ska` and
  `landing_or_park_save`, which still ask loose;
* **six projections OUT** — three inside the two content-park landings, which
  had held the tight arm since item 80 and wrote `.imp_left And.left` to hand
  it on weakened, and three at `accum_block_pending`'s document-marker and
  escape arms;
* **three rows CASHED** — `pendingBlock` and `pendingMapValue` were paying
  `Or.inl h_sk` off their `simpleKeyAllowed` field, and item 222's ladder had
  already measured that both carry a COLUMN that pays the tight arm outright.
  Those are the two rows of free strength item 222 named and could not spend.

## What it buys: §5

`colon_fires_implicit_key` asked the tight arm, so until item 222 only the two
content parks could reach it.  §5 exhibits the call **from an arbitrary park**,
no constructor named — and the residual is named in the SIGNATURE rather than in
prose: five hypotheses the arm does not touch.  So the arm was one blocker of
five, and it is the one now paid; the four that remain are three scanner
invariants and one grammar stream, none of them arm-shaped.
-/

namespace Tests.Guards.ArmDemandLedger

set_option autoImplicit false

open L4YAML L4YAML.Scanner L4YAML.Surface
open L4YAML.Proofs.StreamAccum
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs

variable {sc : ScannerState} {sp_start sp_block sp_scan : SurfPos}

/-! ## §1  The supply, uniform

The ladder's nine rows, as one library lemma with no park class named. -/

example (h_noflow : sc.inFlow = false)
    (h : PendingNode sc false sp_start sp_block sp_scan) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  PendingNode.arm_tight_or_col h_noflow h

/-! ## §2  The two rows item 222 measured and could not spend

`pendingBlock` pays a WIDTH and `pendingMapValue` a COLUMN, and both were
handing consumers `Or.inl` off their `simpleKeyAllowed` field instead.  The
tightened `h_park` is what made the cheaper disjunct the only one that types. -/

/-- `pendingBlock.h_col_old`. -/
example {n : Nat} (h_col : sp_scan.col = n + 1) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  Or.inr (by omega)

/-- `pendingMapValue.h_col0`. -/
example (h_col0 : 0 < sp_scan.col) :
    (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨ 0 < sp_scan.col :=
  Or.inr h_col0

/-- …and the field they WERE paying with does not reach the tight arm, which is
    why the two rows sat unspent from item 80 to item 223. -/
example : ∃ (ska skp : Bool) (col : Nat),
    (ska = true ∧ ¬((ska = true ∧ skp = false) ∨ 0 < col)) :=
  ⟨true, true, 0, by simp⟩

/-! ## §3  The blocker that never was

`colon_fires_implicit_key`'s pack obligation looks like the reason only a
content park could call it — a park with no content behind it has no key head
to offer.  It is not: `KeyPackPunt` has ~~two~~ one argument-free constructor
(`noKeyContext`; `dedent` went at item 297), so ANY caller can discharge the
obligation by punting.  The price of the punt is paid at `h_punt` in §5, which
is a parameter and therefore visible. -/

example : sc.simpleKey.possible = true → sc.simpleKey.pos.line = sc.line →
    ImplicitKeyPack sc sp_start sp_scan ∨ KeyPackPunt sc :=
  fun _ _ => Or.inr .noKeyContext

/-! ## §4  …and the obligation the tight arm makes HARDER, not easier

`StaleNodeTail` demands the save be DOWN; the tight arm's left disjunct says it
is up.  So a park paying on the left can satisfy `h_stale` only by refuting its
`InlineResidue` premise — the two facts are incompatible at a line start.  This
is worth stating because it is the direction a strengthening is not expected to
move a consumer in. -/

example (h_arm : (sc.simpleKeyAllowed = true ∧ sc.simpleKey.possible = false) ∨
      0 < sp_scan.col) (h_col : sp_scan.col = 0) : ¬ StaleNodeTail sc := by
  rcases h_arm with ⟨h_ska, _⟩ | h_pos
  · intro h_st
    have : sc.simpleKeyAllowed = false := h_st.2.1
    rw [h_ska] at this; exact absurd this (by simp)
  · omega

/-! ## §5  The route, with its residual in the signature

Item 222's NEXT recorded this as the route it "measured and did not build".
Here it is built — `colon_fires_implicit_key` applied with no park class named,
the arm coming from the family reading.  Everything else the lemma wants is a
PARAMETER below, so the residual is ~~five~~ **six**, it is machine-checked, and
it moves only when this signature moves — as it did at item 293, when the
consumer's `¬ possible` arm took the park's `h_live`. -/

lemma colon_fires_from_any_park
    (sc : ScannerState) (sp_start sp_block sp_scan : SurfPos)
    (s_prep s' : ScannerState) (sp_prep sp_scan' : SurfPos)
    -- What the PARK supplies, from item 223's uniform ladder: the arm, at any
    -- one of the nine block-context classes, with none of them named.
    (h_noflow_sc : sc.inFlow = false)
    (h_pending : PendingNode sc false sp_start sp_block sp_scan)
    -- …and the FIVE the arm does not touch.  One grammar stream —
    (h_stream_block : SLYamlStream sp_start sp_block)
    -- — three scanner invariants —
    (h_stale : InlineResidue sp_scan ':' → StaleNodeTail sc)
    (h_kbc : ScannerCorrectness.KeysBehindCursor sc)
    (h_scf : StaleCursorFloor.StaleKeyCursorFloor sc)
    -- — item 293's live key at an inline `:` (a content park's `h_live`) —
    (h_live : InlineResidue sp_scan ':' → sc.simpleKey.possible = true)
    -- — and the punt §3's `.noKeyContext` defers to (`.dedent` until item 297).
    (h_punt : ∃ sp_gram' sp_block' sp_flow' sp_scan'',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none s' 0 #[] #[] .sep sp_block' sp_flow' ∧
      PendingNode s' false sp_start sp_flow' sp_scan'' ∧
      ScannerSurfCorr s' sp_scan'')
    (hcorr_prep : ScannerSurfCorr s_prep sp_prep)
    (hcorr_result : ScannerSurfCorr s' sp_scan')
    (h_corr : ScannerSurfCorr sc sp_scan)
    (h_noflow : s_prep.inFlow = false)
    (h_preprocess : scanNextToken_preprocess sc = .ok (some (s_prep, ':')))
    (h_dispatch : scanNextToken_dispatchBlockIndicators
        (if s_prep.allowDirectives then
          { s_prep with allowDirectives := false, documentEverStarted := true }
        else s_prep) ':' = .ok (some s'))
    (h_cf : ColFloor.ColFloor sc) (h_lkt : ScalarWalkColFloor.LiveKeyTop sc) :
    ∃ sp_gram' sp_block' sp_flow' sp_scan',
      SLYamlStream sp_start sp_gram' ∧
      BlockStack sp_gram' sp_block' ∧
      FlowStackB sp_start 0 0 none s' 0 #[] #[] .sep sp_block' sp_flow' ∧
      PendingNode s' false sp_start sp_flow' sp_scan' ∧
      ScannerSurfCorr s' sp_scan' :=
  colon_fires_implicit_key sc sp_start sp_block sp_scan s_prep s' sp_prep sp_scan'
    h_stream_block
    -- §3: the pack obligation, punted.
    (fun _ _ => Or.inr .noKeyContext)
    h_stale
    -- **The arm, from ANY park** — the one blocker item 223 paid.
    (PendingNode.arm_tight_or_col h_noflow_sc h_pending)
    -- Item 287: the consumer takes the punt as a builder, told what an inline
    -- residue at the park is; this route's punt is already the conclusion.
    h_kbc h_scf h_live (fun _ => h_punt) hcorr_prep hcorr_result h_corr h_noflow h_preprocess h_dispatch h_cf h_lkt

end Tests.Guards.ArmDemandLedger
