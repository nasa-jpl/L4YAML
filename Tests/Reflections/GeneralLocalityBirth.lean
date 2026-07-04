import L4YAML.Proofs.Output.EmitterScannability
import L4YAML.Proofs.Output.EmitterScannability.TokVals

/-!
# Reflection — birth probes for the Front-B general-locality plan

Per [[inhabitation-debt-validate-target-defs]], every to-be-built target of the Front-B closure
plan is validated on REAL emissions before construction:

1. **TokVals pin** (module-C target): the filtered `.val`-run of `scanFiltered (emit v)` is
   exactly `[.streamStart] ++ emitTokVals v ++ [.streamEnd]` — probed on a nested map, an outer
   sequence, an EMPTY collection element, and (critically) a **collection-keyed** mapping
   `{[b]: a}` — the `.key`-marker-before-non-scalar-key assumption of `mapTokVals`.
2. **Two-fuel both-success joint** (module-B target): `parseNode` at the standalone position 1
   and at the in-stream element position, with DIFFERENT fuels, yields equal values and equal
   relative advances.
3. **Standalone end pin** (W3a target): the standalone `parseNode` at position 1 of a
   single-document emission ends exactly at `tokens.size - 1` (the `streamEnd` position).
4. **Purity** (module-B2 target): a value parsed from a flow-clean window is
   `resolveAliases`-invariant under an arbitrary junk anchor map, `stripAnchors`-invariant,
   and `anchorFree`.
-/

namespace GeneralLocalityBirth

open L4YAML
open L4YAML.Emit
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.Scanner
open L4YAML.Proofs.EmitterScannability

/-! ## Fixtures -/

def sc (s : String) : YamlValue := .scalar { content := s, style := .plain }

/-- `{a: [b, c]}` — nested map, the class the all-scalar chain cannot reach. -/
def nested : YamlValue :=
  .mapping .flow #[(sc "a", .sequence .flow #[sc "b", sc "c"] none none)] none none

/-- `[{a: [b, c]}, z]` — the whole-stream context embedding `nested` at slot 0. -/
def outer : YamlValue := .sequence .flow #[nested, sc "z"] none none

/-- `[[], z]` — empty-collection element. -/
def withEmpty : YamlValue :=
  .sequence .flow #[.sequence .flow #[] none none, sc "z"] none none

/-- `{[b]: a}` — COLLECTION key: probes that the scanner still materialises the `.key` marker. -/
def collKey : YamlValue :=
  .mapping .flow #[(.sequence .flow #[sc "b"] none none, sc "a")] none none

def toks (v : YamlValue) : Array (Positioned YamlToken) :=
  match Scanner.scanFiltered (emit v) with
  | .ok t => t
  | _ => #[]

/-! ## 1. TokVals pins -/

theorem tokvals_pin_nested :
    ((Scanner.scanFiltered (emit nested)).toOption.map (fun ts => ts.toList.map (·.val))
      == some ([.streamStart] ++ emitTokVals nested ++ [.streamEnd])) = true := by
  native_decide

theorem tokvals_pin_outer :
    ((Scanner.scanFiltered (emit outer)).toOption.map (fun ts => ts.toList.map (·.val))
      == some ([.streamStart] ++ emitTokVals outer ++ [.streamEnd])) = true := by
  native_decide

theorem tokvals_pin_empty_elt :
    ((Scanner.scanFiltered (emit withEmpty)).toOption.map (fun ts => ts.toList.map (·.val))
      == some ([.streamStart] ++ emitTokVals withEmpty ++ [.streamEnd])) = true := by
  native_decide

theorem tokvals_pin_collection_key :
    ((Scanner.scanFiltered (emit collKey)).toOption.map (fun ts => ts.toList.map (·.val))
      == some ([.streamStart] ++ emitTokVals collKey ++ [.streamEnd])) = true := by
  native_decide

/-! ## 2. Two-fuel both-success joint birth

`nested` sits at stream position 2 of `emit outer` (after `streamStart`, `[`); its standalone
tokens put it at position 1.  Fuels differ (40 vs 23) — the joint target must be two-fuel. -/

theorem joint_birth_two_fuel :
    (((parseNode { tokens := toks nested, pos := 1 } 40).toOption.map (·.1)
       == (parseNode { tokens := toks outer, pos := 2 } 23).toOption.map (·.1))
     && ((parseNode { tokens := toks nested, pos := 1 } 40).toOption.map (fun r => r.2.pos - 1)
       == (parseNode { tokens := toks outer, pos := 2 } 23).toOption.map
            (fun r => r.2.pos - 2))) = true := by
  native_decide

/-- The second element `z` of `outer` sits after `nested`'s run + one separator:
    pos = 2 + |emitTokVals nested| + 1. -/
theorem joint_birth_slot1 :
    (((parseNode { tokens := toks (sc "z"), pos := 1 } 40).toOption.map (·.1)
       == (parseNode { tokens := toks outer, pos := 2 + (emitTokVals nested).length + 1 }
            17).toOption.map (·.1))) = true := by
  native_decide

/-! ## 3. Standalone end pin -/

theorem std_end_pin_nested :
    ((parseNode { tokens := toks nested, pos := 1 } 40).toOption.map (fun r => r.2.pos)
      == some ((toks nested).size - 1)) = true := by
  native_decide

theorem std_end_pin_scalar :
    ((parseNode { tokens := toks (sc "z"), pos := 1 } 40).toOption.map (fun r => r.2.pos)
      == some ((toks (sc "z")).size - 1)) = true := by
  native_decide

/-! ## 4. Purity -/

def junkAnchors : Array (String × YamlValue) := #[("x", sc "q"), ("b", nested)]

theorem purity_birth :
    ((parseNode { tokens := toks outer, pos := 2 } 23).toOption.map
       (fun r => (r.1.resolveAliases junkAnchors == r.1)
         && (r.1.stripAnchors == r.1) && r.1.anchorFree)
      == some true) = true := by
  native_decide

end GeneralLocalityBirth
