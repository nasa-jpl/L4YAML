/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Scripts.Path.CapstonePath
import Tests.Guards.Proofs.OrTrueAudit
import L4YAML.Proofs.Production.DocumentProduction

/-!
# The `∨ True` audit, ON or OFF the capstone's path (DOCS item 439)

The owner's reading of item 438: a `∨ True` cannot make the capstone unsound, only weak; the
risk he refuses to carry is the set of positions whose vacuous arm weakens a fact the capstone
CONSUMES.  This guard pins that set.  It takes the `∨ True` audit's pinned tables
(`OrTrueAudit.expectedPositions` / `expectedSupply` / `expectedConsumers`) and the closure of
constants `DocumentProduction.scan_strict_proof` / `parse_strict_proof` reach — the two
capstones that import `StreamAccum` — and classes every position with
`Scripts.Path.CapstonePath.classify` (the classes are documented there).

Pins are **shrink-only**: the ON roster is re-pinned DOWN when an item pays or retires a
position (it leaves the audit) or moves it OFF; a position that appears ON needs the owner's
word in the item that adds it.  The OFF roster is residue by class and is pinned exactly.
`lake run capstone-path` recomputes the same reading off the built `.olean`s.
-/

namespace Tests.Guards.CapstonePathAudit

open Lean Elab Command
open Scripts.Path.CapstonePath

-- 2026-11-10 (item 469, review round 1): `FlowStackKBody`/`FlowStackKA` out, `gapTail` + `FlowStackK.withArm` in — the StreamAccum
-- reached count moves 1132/1274 → 1133/1276; every other count unmoved.
-- 2026-11-09 (item 469): `FlowArm`/`GapRead`/`FlowStackKA` and `accum_step_flow_trace` — StreamAccum constants reached 1118/1254 → 1132/1274; every other count unmoved.
-- 2026-11-10 (item 471, option (A)): streamAccum-reached=1133/1276 → streamAccum-reached=1133/1279 — the level constructors' `≤` bound and the
-- positional `ResumeWidths` add reached positions in `StreamAccum` (the helper readers), no capstone path moved.
def expectedSummary : String :=
  "positions=269 on=7 off=192 unresolved=70 on-drop=3 on-via=0 on-relay=4 on-conclusion=0 off-honest=94 off-unread=53 off-conclusion=25 off-unreached=0 on-drop-nested=0 on-via-nested=0 on-relay-nested=0 off-honest-nested=20 nested-unresolved=70 on-by-alt: True=0 PackAlt=7 PackAltG=0 off-by-alt: True=135 PackAlt=50 PackAltG=7 pack-declines: on=8 off=43 consumed=scan_content_gives_stream_v2 streamAccum-reached=1133/1279 unrooted-arms=86 arms=245 relays=141 drop-set=8/8"

def expectedOn : List String :=
  [ "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[9].h_vpack top ∨ PackAlt on-relay DECLINE=4",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[12].h_kslot top ∨ PackAlt on-relay",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[10].h_kslot top ∨ PackAlt on-relay DECLINE=1",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[10].h_vpack top ∨ PackAlt on-drop DECLINE=3",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[13].h_kslot top ∨ PackAlt on-drop",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[15].h_kslot top ∨ PackAlt on-drop",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[16].h_vpack top ∨ PackAlt on-relay"
  ]

def expectedOff : List String :=
  [ "L4YAML.Proofs.PreprocessIndentStable.IndentFloor.transport[3].h_floor top ∨ True off-unread",
    "L4YAML.Proofs.PreprocessIndentStable.IndentFloor.transport[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[6].valueF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key top ∨ True off-unread DECLINE=1",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ True nested-unresolved DECLINE=1",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ PackAltG nested-unresolved DECLINE=1",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ True nested-unresolved DECLINE=1",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[8].key nested ∨ PackAltG nested-unresolved DECLINE=1",
    "L4YAML.Proofs.StreamAccum.FlowBaseRoutes.mk[9].vslot top ∨ PackAltG off-unread DECLINE=5",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ImplicitKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.KmSoundbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.KmSoundbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.KmSound.back_col[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.KmSound.back_col[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.KmSound.push[15].h_stamp_new nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.KmSound.push[17].h_marker_new nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[11].h_framesS top ∨ True off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[11].h_framesS nested ∨ True nested-unresolved DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[12].h_framesV top ∨ PackAlt off-unread DECLINE=4",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[12].h_framesV nested ∨ True nested-unresolved DECLINE=4",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent[16].h_seqF top ∨ True off-unread DECLINE=9",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[19].h_ncol top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[21].h_kslot top ∨ PackAlt off-honest DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[22].h_routeE top ∨ PackAlt off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[23].h_kslotE top ∨ PackAlt off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE nested ∨ True nested-unresolved DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[24].h_closeFE nested ∨ True nested-unresolved DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[25].h_closeF top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[25].h_closeF nested ∨ True nested-unresolved DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[26].h_closeFV top ∨ PackAlt off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[26].h_closeFV nested ∨ True nested-unresolved DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingProps[28].h_closeFEV top ∨ PackAlt off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[13].h_closeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[16].h_seqF top ∨ True off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[17].h_kslotUp top ∨ PackAlt off-unread",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[18].h_closeFV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent[18].h_closeFV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[11].h_closeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[13].h_seqF top ∨ True off-unread DECLINE=6",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[14].h_kslotUp top ∨ PackAlt off-honest DECLINE=1",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[15].h_closeFV top ∨ PackAlt off-unread DECLINE=1",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock[15].h_closeFV nested ∨ True nested-unresolved DECLINE=1",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[11].h_expl nested ∨ PackAlt off-honest-nested",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[15].h_ncol top ∨ True off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[16].h_kslot top ∨ PackAlt off-honest DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[17].h_closeF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[17].h_closeF nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[18].h_frames top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[18].h_frames nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[19].h_closeFV top ∨ PackAlt off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[19].h_closeFV nested ∨ True nested-unresolved DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[20].h_framesV top ∨ PackAlt off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[20].h_framesV nested ∨ True nested-unresolved DECLINE=2",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[22].h_seqF top ∨ True off-unread DECLINE=5",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingMapValue[23].h_explUp nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.PropsKeyPackbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.ResumeKeyCtxbody nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[11].h_vslot nested ∨ PackAlt off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[11].h_vslot nested ∨ PackAlt off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[19].h_sfx top ∨ True off-honest DECLINE=10",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[20].h_mk top ∨ True off-honest DECLINE=10",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[26].h_tail139 top ∨ True off-unread DECLINE=8",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[27].h_valF top ∨ True off-honest DECLINE=9",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[27].h_valF nested ∨ True nested-unresolved DECLINE=9",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[28].h_seqF top ∨ True off-honest DECLINE=7",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[29].h_mapF top ∨ True off-honest DECLINE=7",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[30].h_pr top ∨ True off-honest DECLINE=9",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[31].h_mapFV top ∨ PackAlt off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[31].h_mapFV nested ∨ True off-honest-nested DECLINE=3",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock[32].h_valFV top ∨ True off-honest DECLINE=8",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[29].h_seqF_old top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[30].h_kslotUp top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[31].h_closeFV_old top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[31].h_closeFV_old nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock[32].h_closeF_old nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[34].h_seqF_old top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[35].h_kslotUp top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[36].h_closeF_old nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[37].h_closeFV_old top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent[37].h_closeFV_old nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[33].h_seqF168 top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[34].h_mapF109 top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent[35].h_mapFV108 top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[13].h_kslot_old top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[14].h_closeF_old nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[15].h_seqF_old top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[32].h_kslotUp_old top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[33].h_closeFV_old top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingBlock_indented[33].h_closeFV_old nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[14].h_ncol_old top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[15].h_expl nested ∨ PackAlt off-honest-nested",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[16].h_vslot top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[17].h_kslot top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[18].h_closeF99 top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[18].h_closeF99 nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[19].h_frames99 top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[19].h_frames99 nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[20].h_closeFV108 top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[20].h_closeFV108 nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[21].h_framesV108 top ∨ PackAlt off-unread",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[21].h_framesV108 nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.accum_content_on_pendingMapValue_indented[38].h_seqF168 top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.bareNodeRoute_or_refused[11].h_tail top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.bareNodeRoute_or_refused_content[12].h_tail top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.close_col_of_base[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.close_col_of_base[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.colon_open_map[19].h_sfx_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map[20].h_nodoc_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map[21].h_mk_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map[22].h_res_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map[23].h_ref_land top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.colon_open_map[24].h_cov_in top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.colon_open_map[25].h_pr_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map[26].h_resV_land top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map[28].h_explUp_chainD top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[12].h_routeF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[12].h_routeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[13].h_routeFV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.colon_open_map_implicit[27].h_routeS top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[11].h_routeF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[11].h_routeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[12].h_routeFV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[12].h_routeFV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.colon_open_map_props[29].h_kslotD top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.compact_open_map[30].h_chainUp top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[16].h_keyctx top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.content_dispatch_after_close[19].h_propsctx top ∨ True off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[18].h_keyctx top ∨ True off-honest DECLINE=1",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[20].h_suffixctx top ∨ True off-honest DECLINE=6",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[21].h_nodocctx top ∨ True off-honest DECLINE=6",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[22].h_markerctx top ∨ True off-honest DECLINE=6",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[24].h_ref top ∨ True off-unread DECLINE=4",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[25].h_propsctx top ∨ True off-honest DECLINE=7",
    "L4YAML.Proofs.StreamAccum.content_dispatch_routed[26].h_markerline top ∨ True off-honest DECLINE=7",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[8].h_cov top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[9].h_dcov top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.dedent_cover_of_landing[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[7].h_valF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[7].h_valF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.deeperLandingResume[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[11].h_nodeV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[12].h_compact top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[12].h_compact nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[13].h_ivl nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[14].h_nodeF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[14].h_nodeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[15].h_dframes top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[15].h_dframes nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[16].h_nodeFV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[16].h_nodeFV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[17].h_dframesV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[17].h_dframesV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[18].h_cov top ∨ True off-honest DECLINE=2",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[30].h_nodeS top ∨ True off-honest DECLINE=2",
    "L4YAML.Proofs.StreamAccum.entryKeyPack_of_dispatch[31].h_nodeSF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[11].h_nodeV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[12].h_compact top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[12].h_compact nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[13].h_nodeF top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[13].h_nodeF nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[14].h_dframes top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[14].h_dframes nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[15].h_nodeFV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[15].h_nodeFV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[16].h_dframesV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[16].h_dframesV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[17].h_cov top ∨ True off-unread DECLINE=1",
    "L4YAML.Proofs.StreamAccum.entryPropsKeyPack_of_dispatch[27].h_ivl nested ∨ PackAlt nested-unresolved",
    "L4YAML.Proofs.StreamAccum.flowKeyHead[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ PackAltG off-honest-nested",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[7].h_key nested ∨ PackAltG off-honest-nested",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[8].h_base nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.flowKeyPack_of_close[8].h_base nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[12].h_compact top ∨ True off-honest DECLINE=1",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[13].h_compact_pair top ∨ PackAlt off-honest DECLINE=1",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ PackAltG off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_open[ret] nested ∨ PackAltG off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[9].h_col top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[20].h_sfx top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[21].h_nodoc top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[24].h_tail143 top ∨ True off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[25].h_mapF top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[26].h_mapFV top ∨ PackAlt off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ PackAltG off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowKeyRoute_of_root[ret] nested ∨ PackAltG off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker[4].h_doc top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.flowOpen_marker[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp[4].h_ivl top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.flowOpen_stamp[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[22].h_sfx_land top ∨ True off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[23].h_nodoc_land top ∨ True off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[24].h_mk_land top ∨ True off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[25].h_res_land top ∨ True off-unread DECLINE=1",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[26].h_ref_land top ∨ True off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[27].h_cov top ∨ True off-honest DECLINE=1",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[28].h_pr_land top ∨ True off-unread DECLINE=3",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[29].h_explUp_chain top ∨ PackAlt off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[30].h_resV_land top ∨ PackAlt off-unread DECLINE=1",
    "L4YAML.Proofs.StreamAccum.indicator_open_map[32].h_explUp_chainD top ∨ PackAlt off-unread DECLINE=2",
    "L4YAML.Proofs.StreamAccum.keyctx_of_preprocess[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.km_push_at_open[19].h_stamp_new nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.km_push_at_open[21].h_marker_new nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing[11].h_mk top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.markerctx_of_landing[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.nodocctx_of_preprocess[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.question_open_map[18].h_sfx_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.question_open_map[19].h_nodoc_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.question_open_map[20].h_mk_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.question_open_map[21].h_res_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.question_open_map[22].h_ref_land top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.question_open_map[23].h_cov_in top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.question_open_map[24].h_cov_nil top ∨ True off-unread",
    "L4YAML.Proofs.StreamAccum.question_open_map[25].h_pr_land top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.question_open_map[26].h_explUp_chain top ∨ PackAlt off-unread",
    "L4YAML.Proofs.StreamAccum.question_open_map[27].h_resV_land top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.question_open_map[29].h_explUp_chainD top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[13].h_fS top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[13].h_fS nested ∨ True off-honest-nested",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[14].h_fV top ∨ PackAlt off-honest",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[14].h_fV nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[15].h_pay nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[15].h_pay nested ∨ True nested-unresolved",
    "L4YAML.Proofs.StreamAccum.resumectx_of_landing[16].h_fQ top ∨ True off-honest DECLINE=3",
    "L4YAML.Proofs.StreamAccum.rootMapRouteF_or_refused[7].h_ref top ∨ True off-unread DECLINE=4",
    "L4YAML.Proofs.StreamAccum.rootMapRoute_or_refused[7].h_ref top ∨ True off-unread DECLINE=6",
    "L4YAML.Proofs.StreamAccum.scanValue_ok_park_facts[ret] nested ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing[11].h_sfx top ∨ True off-honest",
    "L4YAML.Proofs.StreamAccum.suffixctx_of_landing[ret] top ∨ True off-conclusion",
    "L4YAML.Proofs.StreamAccum.topLevelFlowResumeSep_or_refused[6].h_ref top ∨ True off-unread"
  ]

def expectedFamilies : List String :=
  [ "L4YAML.Proofs.StreamAccum.PendingNode.pendingContent: [9].h_vpack ∨ PackAlt on-relay",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlockContent: [12].h_kslot ∨ PackAlt on-relay",
    "L4YAML.Proofs.StreamAccum.PendingNode.pendingBlock: [10].h_kslot ∨ PackAlt on-relay",
    "L4YAML.Proofs.StreamAccum.accum_block_on_closeThenBlock: [10].h_vpack ∨ PackAlt on-drop",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlock: [13].h_kslot ∨ PackAlt on-drop",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingBlockContent: [15].h_kslot ∨ PackAlt on-drop",
    "L4YAML.Proofs.StreamAccum.accum_block_on_pendingContent: [16].h_vpack ∨ PackAlt on-relay"
  ]

open Lean Elab Command in

/- Regression (PR #249 review): `rootOf` follows `Or.imp f g h` / `Or.imp_left f h` to the SOURCE
    disjunction `h`, and gives a partial application (a function, not a fact) no root. -/
run_cmd Lean.Elab.Command.liftTermElabM do
  let keys : Std.HashSet String := Std.HashSet.ofList ["T[0].h"]
  let ctx : Array (Option Scripts.Path.CapstonePath.Root) := #[some ("T[0].h", none)]
  let env ← Lean.getEnv
  let check (stx : Lean.Term) (want : Option String) : Lean.Elab.TermElabM Unit := do
    let e ← Lean.Elab.Term.elabTerm stx none
    let e ← Lean.instantiateMVars e
    let .lam _ _ b _ := e | throwError "regression: expected a lambda"
    let got := (Scripts.Path.CapstonePath.rootOf env keys {} ctx b).map (·.1)
    unless got == want do throwError "regression: rootOf gave {got}, wanted {want} on {e}"
  check (← `(fun (h : True ∨ True) => Or.imp id id h)) (some "T[0].h")
  check (← `(fun (h : True ∨ True) => Or.imp_left id h)) (some "T[0].h")
  check (← `(fun (h : True ∨ True) => Or.imp_right id h)) (some "T[0].h")
  check (← `(fun (h : True ∨ True) => Or.imp (fun (_ : True) => h) id)) none

run_cmd do
  let env ← getEnv
  let r := reach env roots
  let shown := shownSet r
  -- the StreamAccum conclusions the capstones consume directly
  let consumed := (roots.foldl (fun acc n => acc ++ (rawRefs env n).toList) [])
    |>.filter (fun n => (`L4YAML.Proofs.StreamAccum).isPrefixOf n) |>.eraseDups
    |>.map (fun n => (privateToUserName n).toString.drop "L4YAML.Proofs.StreamAccum.".length |>.toString)
  let positions := Tests.Guards.OrTrueAudit.expectedPositions
  let keys : Std.HashSet String := positions.foldl (fun acc l => match parsePos l with
    | some p => acc.insert s!"{p.decl}{p.site}" | none => acc) {}
  let drop : Std.HashSet Name := Std.HashSet.ofList (dropSet.filter env.contains)
  let decls := r.toArray.filter fun n => saNs.isPrefixOf n || (`L4YAML.Proofs.PreprocessIndentStable).isPrefixOf n
  let w := walkAll env drop keys decls
  let cs := classify shown positions Tests.Guards.OrTrueAudit.expectedSupply
    Tests.Guards.OrTrueAudit.expectedConsumers w.arms w.relays
  let (saR, saT) := moduleReach env r `L4YAML.Proofs.StreamAccum
  let summ := summary cs consumed saR saT w.unrooted.size ++ s!" arms={w.arms.size} relays={w.relays.size} drop-set={drop.size}/{dropSet.length}"
  let on := (cs.filter (·.cls.startsWith "on-")).map Classed.line |>.toList
  -- the residue: every row not ON, the `nested-unresolved` rows included (a third bucket, pinned too)
  let off := (cs.filter (fun c => !c.cls.startsWith "on-")).map Classed.line |>.toList
  let fams := (families cs).toList
  let show_ (xs : List String) := String.intercalate "\n" (xs.map fun x => s!"    \"{x}\",")
  let mut moved : Array String := #[]
  if summ != expectedSummary then
    moved := moved.push s!"the capstone-path SUMMARY moved.\nexpected: {expectedSummary}\ngot:      {summ}"
  if on != expectedOn then
    moved := moved.push s!"the capstone-path ON roster moved (shrink-only: a position leaves when paid / retired / moved OFF; one that appears needs the owner's word).\nexpected ({expectedOn.length}), got ({on.length}):\n{show_ on}"
  if off != expectedOff then
    moved := moved.push s!"the capstone-path OFF residue moved.\nexpected ({expectedOff.length}), got ({off.length}):\n{show_ off}"
  if fams != expectedFamilies then
    moved := moved.push s!"the capstone-path FAMILIES moved.\nexpected ({expectedFamilies.length}), got ({fams.length}):\n{show_ fams}"
  unless moved.isEmpty do
    throwError (String.intercalate "\n\n" moved.toList)

end Tests.Guards.CapstonePathAudit
