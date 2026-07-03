import L4YAML.Output.Json
import L4YAML.Output.Events

/-!
# Reflection — INHABITATION / BOUNDARY probe for order-aware alias resolution (matrix defect J2)

Matrix defect **J2** (`YAML_MATRIX_100PCT_ASSESSMENT.md`, 3GZX): a document that REBINDS an anchor
name must resolve each alias against the definition in scope at the alias's own position
(YAML 1.2.2 §7.1: an alias refers to the *most recent preceding* node with that anchor).  A global
table cannot serve two aliases that need different values for the same name: first-wins broke
`Reuse anchor` (the old defect), last-wins would break `Second occurrence` (the naive fix).
`YamlDocument.compose` now resolves via `YamlValue.resolveAliasesOrdered`, an in-document-order walk
threading a binding environment (a node's anchor binds *after* its own content).

This is a [[feedback-inhabitation-debt-validate-target-defs]] probe: the environment plumbing
*type-checks* under first-wins, last-wins, and positional lookup alike, so the discriminating
documents are pinned here by their full emitted JSON, where resolution is actually performed.
Because the pipeline runs through `parseYaml` (`partial def` parser), every check is `native_decide`.

The pins bracket the fix from both sides:
  * 3GZX/rebind: `Second occurrence`/`b` pin `Foo`/`1` (a global LAST-wins would give `Bar`/`2`),
    `Reuse anchor`/`d` pin `Bar`/`2` (the old global FIRST-wins gave `Foo`/`1`).
  * the EVENT axis emits `=ALI *anchor` from the serialization tree — `compose` never runs there,
    so J2 cannot move the event stream (the axis stands at 402/402).
  * a forward alias is still rejected at PARSE time (§7.1), before `compose` — order-aware
    resolution did not loosen the acceptance boundary.
-/

namespace OrderAwareAlias

/-- The Core-Schema JSON `streamToJson` emits for `input`, or a fixed error marker. -/
private def runJson (input : String) : String :=
  match L4YAML.Json.streamToJson input with | .ok s => s | .error _ => "«parse-error»"

/-- The full event stream `streamToEvents` emits for `input`, or a fixed error marker. -/
private def runEvents (input : String) : String :=
  match L4YAML.Events.streamToEvents input with | .ok s => s | .error _ => "«parse-error»"

/-! ## Rule 5 (positive) — 3GZX, grounded on the yaml-test-suite bytes

Each alias binds to the most recent *preceding* definition: the alias between the two
definitions gets `Foo`, the alias after the rebinding gets `Bar`. -/

/-- `data/3GZX/in.yaml` — Spec Example 7.1 (alias nodes with a rebound anchor). -/
def in3GZX : String :=
  "First occurrence: &anchor Foo\nSecond occurrence: *anchor\nOverride anchor: &anchor Bar\nReuse anchor: *anchor\n"
def outJson3GZX : String :=
  "{\"First occurrence\":\"Foo\",\"Second occurrence\":\"Foo\",\"Override anchor\":\"Bar\",\"Reuse anchor\":\"Bar\"}"
theorem gzx_resolves_each_alias_at_its_position : runJson in3GZX = outJson3GZX := by native_decide

/-- Minimal rebinding mapping: `b` (NOT last-wins) and `d` (NOT first-wins) discriminate
    every global-table discipline from the positional one in a single document. -/
def inRebindMap : String := "a: &x 1\nb: *x\nc: &x 2\nd: *x\n"
def outRebindMap : String := "{\"a\":1,\"b\":1,\"c\":2,\"d\":2}"
theorem rebind_map_b_first_d_second : runJson inRebindMap = outRebindMap := by native_decide

/-- Rebinding across SEQUENCE items — the `goList` environment threading: a binding made by
    item 0 serves item 1, and item 2's rebinding serves item 3. -/
def inRebindSeq : String := "- &x 1\n- *x\n- &x 2\n- *x\n"
def outRebindSeq : String := "[1,1,2,2]"
theorem rebind_seq_items_thread_env : runJson inRebindSeq = outRebindSeq := by native_decide

/-- Bindings made INSIDE an earlier sibling escape to later siblings (the joint
    grammable ∧ well-formed-env conclusion of `compose_value_grammable_ordered` exists
    because of exactly this): `l` consumes the `&x` bound inside `k`'s value, and `m`
    consumes `k`'s own completed node. -/
def inNestedEscape : String := "k: &o {a: &x 1, b: *x}\nl: *x\nm: *o\n"
def outNestedEscape : String := "{\"k\":{\"a\":1,\"b\":1},\"l\":1,\"m\":{\"a\":1,\"b\":1}}"
theorem nested_bindings_escape_to_later_siblings : runJson inNestedEscape = outNestedEscape := by
  native_decide

/-! ## Rule 2 (boundary) — what must NOT change

The event axis reads the serialization tree (aliases emitted as `=ALI`, never resolved), and
the parser still rejects a forward alias before `compose` ever runs. -/

/-- 3GZX on the EVENT axis: byte-identical to before J2 — both `=ALI *anchor` entries survive,
    no resolution happens in the serialization tree. -/
def outEvents3GZX : String :=
  "+STR\n+DOC\n+MAP\n=VAL :First occurrence\n=VAL &anchor :Foo\n=VAL :Second occurrence\n=ALI *anchor\n=VAL :Override anchor\n=VAL &anchor :Bar\n=VAL :Reuse anchor\n=ALI *anchor\n-MAP\n-DOC\n-STR\n"
theorem gzx_event_axis_untouched : runEvents in3GZX = outEvents3GZX := by native_decide

/-- A forward alias (no preceding definition) is still rejected at parse time (§7.1) —
    order-aware resolution did not loosen the acceptance boundary. -/
def inForwardAlias : String := "d: *y\ne: &y 9\n"
theorem forward_alias_still_rejected : runJson inForwardAlias = "«parse-error»" := by native_decide

-- Axiom audit — the pins run the real parse pipeline (`Except`-monad + `partial def` parser,
-- hence `Classical.choice`/`Quot.sound`), closed by `native_decide`.  No `sorryAx`.
/-- info: 'OrderAwareAlias.gzx_resolves_each_alias_at_its_position' depends on axioms: [propext,
 Classical.choice,
 Quot.sound,
 gzx_resolves_each_alias_at_its_position._native.native_decide.ax_1_1] -/
#guard_msgs in
#print axioms gzx_resolves_each_alias_at_its_position

end OrderAwareAlias
