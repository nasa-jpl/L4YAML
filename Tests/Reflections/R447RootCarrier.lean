import L4YAML.Proofs.Output.EmitterScannability

/-!
# Reflection -- R447: Root carrier via the R505 provider route (`seqRoot_carrier_r447`)

`seqRoot_carrier_r447` proves `SeqInteriorSeparators tokens 2 (tokens.size - 2)` (ROOT CARRIER).
As of the R505 reduction, its `recIH` is **discharged** (no sorry) by the landed
`seqWindowRecSeqBody_seq_of_provider`, fed the single residual `seqBody_flowBodyContent_provider`:

```
recIH  ← seqWindowRecSeqBody_seq_of_provider (R505, landed)
           ← seqBody_flowBodyContent_provider  (THE one remaining sorry)
seqRoot_carrier_r447 ← seqWidthEnc_of_recIH_seq + seqRoot_carrier_of_widthEnc_seq (both landed)
```

The lone sorry now lives in `seqBody_flowBodyContent_provider`: a **path-FREE** per-window
`FlowBodyContent` source (gate `FlowBodyWindow ∧ FlowBodyContentDeepSeq ∧ SeqEnclosed`, NOT the
stronger `SeqPathAllSeq`).  It must be a STRUCTURAL navigator over the stored root `RecSeqBody`
(`seqRoot_recseqbody`), because the landed token-spine navigator
(`nestedSeq_flowBodyContent_of_locator`, R507) covers only all-seq-path windows.

## Inhabitation debt check (per [[inhabitation-debt-validate-target-defs]])

The provider must serve TWO window classes.  Both must be inhabited before the navigator is written.

### Class 1 -- all-seq-path window: `[["a"]]`  (covered by the landed R507 navigator)

Token stream (7 tokens): `streamStart · [ · [ · "a" · ] · ] · streamEnd`.
Root window `[2,5)`; inner window `[3,4)` (width `1 < (7-2)-2 = 3`).  Inner `[` at position 2,
all enclosing frames `[`-typed → `SeqPathAllSeq` holds.

### Class 2 -- MAP-NESTED seq window: `[{a:[b]}]`  (the residual the navigator must reach)

The single item is a MAPPING `{a:[b]}` whose value is a nested seq `[b]`.  The inner `[b]` is a
balanced seq subrange with `SeqEnclosed` TRUE (top frame `[`) but `SeqPathAllSeq` FALSE (a `{` frame
sits below the top).  This is the fragment `nestedSeq_flowBodyContent_of_locator` (R507) provably
CANNOT reach; the structural navigator over the stored `RecSeqBody` reaches it because
`RecSeqEntry.mapRec` stores `RecMapBody interior` and each `RecMapPair` stores its value block as a
`RecSeqEntry` -- so `[b]`'s body IS a stored subterm of the root `RecSeqBody`.
-/

namespace R447RootCarrier

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Proofs.RoundTrip
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures -/

def inner_sc : Scalar := { content := "a", style := .plain }
def inner_item : YamlValue := .sequence .flow #[.scalar inner_sc] none none
def outer_items : Array YamlValue := #[inner_item]

/-- Map-nested witness: `{a:[b]}` -- a flow mapping whose value is a nested flow seq. -/
def mn_key : YamlValue := .scalar { content := "a", style := .plain }
def mn_val : YamlValue := .sequence .flow #[.scalar { content := "b", style := .plain }] none none
def mn_map : YamlValue := .mapping .flow #[(mn_key, mn_val)] none none
def mn_items : Array YamlValue := #[mn_map]

/-- Helper: pre-compute the scanned token array for the outer `[["a"]]`. -/
def outer_tokens : Option (Array (Positioned YamlToken)) :=
  match Scanner.scanFiltered ("[" ++ emit.emitList outer_items.toList ++ "]") with
  | .ok toks => some toks
  | _ => none

/-- Helper: pre-compute the scanned token array for the map-nested `[{a:[b]}]`. -/
def mn_tokens : Option (Array (Positioned YamlToken)) :=
  match Scanner.scanFiltered ("[" ++ emit.emitList mn_items.toList ++ "]") with
  | .ok toks => some toks
  | _ => none

/-- Helper: the inner seq round-trip gives a value content-equal to `inner_item`. -/
def inner_roundtrip_ok : Bool :=
  match parseYamlRaw (emit inner_item) with
  | .ok docs => contentEq inner_item (docs.map YamlDocument.compose)[0]!.value
  | _ => false

/-- Helper: the map-nested `[{a:[b]}]` round-trips content-equal (whole-structure inhabitation). -/
def mn_roundtrip_ok : Bool :=
  match parseYamlRaw (emit (.sequence .flow mn_items none none)) with
  | .ok docs => contentEq (.sequence .flow mn_items none none) (docs.map YamlDocument.compose)[0]!.value
  | _ => false

/-! ## Class 1: all-seq-path window is reachable & non-vacuous -/

/-- The outer `[["a"]]` scans to exactly 7 tokens. -/
theorem outer_token_size : outer_tokens.map (·.size) = some 7 := by native_decide

/-- Pure arithmetic: the inner window `[3, 4)` is strictly narrower than the root window `[2, 5)`. -/
theorem inner_width_lt_root_width : (4 - 3 : Nat) < (7 - 2) - 2 := by omega

/-- The inner seq `["a"]` round-trips (content-equivalent) -- the target body is real. -/
theorem inner_roundtrip_is_ok : inner_roundtrip_ok = true := by native_decide

/-! ## Class 2: MAP-NESTED window is inhabited (the navigator's residual case)

The map-nested `[{a:[b]}]` emits and re-parses to a content-equal value, so its inner `[b]` window
-- the one `SeqPathAllSeq` cannot reach -- is a genuine balanced seq subrange whose stored
`RecSeqBody` exists.  This validates the provider's hardest case is non-vacuous BEFORE the navigator
is written. -/

/-- The map-nested `[{a:[b]}]` scans successfully (its token stream exists). -/
theorem mn_scans_ok : mn_tokens.map (fun _ => true) = some true := by native_decide

/-- The map-nested `[{a:[b]}]` has strictly more tokens than `[["a"]]` (the `{`/`}`/`key`/`value`
    frame adds depth) -- the inner `[b]` sits two bracket levels deep, one through a `{` frame. -/
theorem mn_token_size_gt : (mn_tokens.map (·.size)).getD 0 > 7 := by native_decide

/-- The whole map-nested structure round-trips content-equal -- domain inhabited & target meaningful. -/
theorem mn_roundtrip_is_ok : mn_roundtrip_ok = true := by native_decide

/-! ## Structural probes: both R447 theorems are well-formed -/

/-- Type-check probe: `seqRoot_carrier_r447` has the expected signature. -/
theorem seqRoot_carrier_r447_type_ok :
    ∀ (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
      (_h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
      (_h_ne : items.toList ≠ [])
      (_h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntryDeep v),
      SeqInteriorSeparators tokens 2 (tokens.size - 2) :=
  @seqRoot_carrier_r447

/-- Type-check probe: `seqBody_recseqbody_provider` is exactly the per-window `RecSeqBody` navigator
    (the lone R447 residual) `seqRoot_carrier_r447`'s `recIH` consumes directly.  Carries the
    close-gate `tokens[hi]!.val = .flowSequenceEnd` (the Rule-2 correction — the ungated form is
    REFUTED by `Tests/Reflections/ProviderCloseGate.lean`; the consumer supplies the close fact
    verbatim). -/
theorem provider_type_ok :
    ∀ (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
      (_h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
      (_h_ne : items.toList ≠ [])
      (_h_all : ∀ v ∈ items.toList, EmitScansInFlowRecEntryDeep v),
      ∀ lo hi, FlowBodyWindow tokens lo hi → FlowBodyContentDeepSeq tokens lo hi →
        SeqEnclosed tokens lo → tokens[hi]!.val = .flowSequenceEnd →
        2 ≤ lo → hi ≤ tokens.size - 2 →
        RecSeqBody ((tokens.toList.take hi).drop lo) :=
  @seqBody_recseqbody_provider

/-! ## Axiom audit

With the R447 residual `seqBody_recseqbody_provider` CLOSED (the deep-family navigator,
`DeepNavigator.lean`), the root carrier's profile is `sorryAx`-FREE — the pin below is the
regression guard on that closure. -/

/-- info: 'R447RootCarrier.seqRoot_carrier_r447_type_ok' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms seqRoot_carrier_r447_type_ok

end R447RootCarrier
