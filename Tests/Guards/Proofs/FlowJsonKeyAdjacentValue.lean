module

public import L4YAML.Proofs.Serialization.TraceOf.Node
public import L4YAML.Scanner.Scanner
public meta import L4YAML.Proofs.Serialization.TraceOf.Node
public meta import L4YAML.Scanner.Scanner

/-! # `[148]`/`[149]` JSON-key adjacent value — the `←` side of the glued-colon gap

`{"a":b}` and `["a":[1]]` are spec-valid (`c-ns-flow-map-json-key-entry`,
`c-ns-flow-pair-json-key-entry`) and the scanner accepts them, but until
`SFlowMapEntry.jsonKeyAdjacentValue` / `SFlowSeqEntry.pairJsonAdjacentValue`
Surface had no derivation (productions jumped 143 → 146).  Both readings are
exhibited concretely below; the plain-key shape `{a:[1]}` deliberately has no arm. -/

namespace L4YAML.Tests.Guards.FlowJsonKeyAdjacentValue

open L4YAML L4YAML.Surface L4YAML.CharPredicates

def accepts (s : String) : Bool :=
  match L4YAML.Scanner.scan s with
  | .ok _ => true
  | .error _ => false

#guard accepts "{\"a\":b}" = true
#guard accepts "{\"a\":[1]}" = true
#guard accepts "[\"a\":[1]]" = true
#guard accepts "{'a':{b: c}}" = true

private lemma safe_b : isNsPlainSafe .flowIn 'b' := by unfold isNsPlainSafe isNsChar; decide
private lemma safe_1 : isNsPlainSafe .flowIn '1' := by unfold isNsPlainSafe isNsChar; decide

/-! ## `{"a":b}` — `[148]` key `"a"`, `[149]` value `b` with no separator -/

abbrev p0 : SurfPos := ⟨['{', '"', 'a', '"', ':', 'b', '}'], 0⟩
abbrev p1 : SurfPos := ⟨['"', 'a', '"', ':', 'b', '}'], 1⟩
abbrev p4 : SurfPos := ⟨[':', 'b', '}'], 4⟩
abbrev p5 : SurfPos := ⟨['b', '}'], 5⟩
abbrev p6 : SurfPos := ⟨['}'], 6⟩
abbrev p7 : SurfPos := ⟨[], 7⟩

lemma readJsonKeyMap : SFlowMapping 0 .flowOut p0 p7 :=
  .nonempty 0 .flowOut p0 p1 p1 p6 p7 (GLit.mk _ 0) (GOpt.none _)
    (.single 0 .flowIn p1 p6 p6
      (.jsonKeyAdjacentValue 0 .flowIn p1 p4 p4 p5 p5 p6
        (.content 0 .flowIn p1 p4 (.doubleQ 0 .flowIn p1 p4
          (SCDoubleQuoted.mk 0 .flowIn _ _ _ _ (GLit.mk _ 1)
            (SNbDoubleMultiLine.single 0 _ _
              (GStar.cons _ _ _
                (SNbDoubleChar.plain 'a' _ 2 (by decide) (by decide) (by decide))
                (GStar.nil _)))
            (GLit.mk _ 3))))
        (GOpt.none _) (GLit.mk _ 4) (GOpt.none _)
        (.content 0 .flowIn p5 p6 (.plain 0 .flowIn p5 p6
          (SNsPlainMultiLine.mk 0 .flowIn p5 p6 p6
            (SNsPlainOneLine.mk .flowIn p5 p6 p6
              (SNsPlainFirst.nonIndicator .flowIn 'b' _ 5 safe_b (by decide)) (GStar.nil _))
            (GStar.nil _)))))
      (GOpt.none _))
    (GLit.mk _ 6)

/-! ## `["a":[1]]` — `[153]` pair: `c-s-implicit-json-key(flow-key)` then `[149]` -/

abbrev q0 : SurfPos := ⟨['[', '"', 'a', '"', ':', '[', '1', ']', ']'], 0⟩
abbrev q1 : SurfPos := ⟨['"', 'a', '"', ':', '[', '1', ']', ']'], 1⟩
abbrev q4 : SurfPos := ⟨[':', '[', '1', ']', ']'], 4⟩
abbrev q5 : SurfPos := ⟨['[', '1', ']', ']'], 5⟩
abbrev q6 : SurfPos := ⟨['1', ']', ']'], 6⟩
abbrev q7 : SurfPos := ⟨[']', ']'], 7⟩
abbrev q8 : SurfPos := ⟨[']'], 8⟩
abbrev q9 : SurfPos := ⟨[], 9⟩

lemma readJsonKeyPair : SFlowSequence 0 .flowOut q0 q9 :=
  .nonempty 0 .flowOut q0 q1 q1 q8 q9 (GLit.mk _ 0) (GOpt.none _)
    (.single 0 .flowIn q1 q8 q8
      (.pairJsonAdjacentValue 0 .flowIn q1 q4 q4 q5 q5 q8
        (.content 0 .flowIn q1 q4 (.doubleQ 0 .flowIn q1 q4
          (SCDoubleQuoted.mk 0 .flowIn _ _ _ _ (GLit.mk _ 1)
            (SNbDoubleMultiLine.single 0 _ _
              (GStar.cons _ _ _
                (SNbDoubleChar.plain 'a' _ 2 (by decide) (by decide) (by decide))
                (GStar.nil _)))
            (GLit.mk _ 3))))
        (GOpt.none _) (GLit.mk _ 4) (GOpt.none _)
        (.content 0 .flowIn q5 q8 (.flowSeq 0 .flowIn q5 q8
          (.nonempty 0 .flowIn q5 q6 q6 q7 q8 (GLit.mk _ 5) (GOpt.none _)
            (.single 0 .flowIn q6 q7 q7
              (.node 0 .flowIn q6 q7 (.content 0 .flowIn q6 q7 (.plain 0 .flowIn q6 q7
                (SNsPlainMultiLine.mk 0 .flowIn q6 q7 q7
                  (SNsPlainOneLine.mk .flowIn q6 q7 q7
                    (SNsPlainFirst.nonIndicator .flowIn '1' _ 6 safe_1 (by decide))
                    (GStar.nil _))
                  (GStar.nil _)))))
              (GOpt.none _))
            (GLit.mk _ 7)))))
      (GOpt.none _))
    (GLit.mk _ 8)

end L4YAML.Tests.Guards.FlowJsonKeyAdjacentValue
