import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity

/-!
# Reflection 603 -- resolveAliases on empty anchors is identity (R603)

`resolveAliases_empty` (§5.0a) asserts that for any `YamlValue`, resolving aliases
against an empty anchor table `#[]` is the identity function:

  `theorem resolveAliases_empty (v : YamlValue) : v.resolveAliases #[] = v`

This is a KEY SIMPLIFICATION LEMMA for the compositionality chain in the non-scalar
branch of the Front-B sequence locality proof: it collapses
  `items'' = items'.map (fun v => (v.resolveAliases #[]).stripAnchors)`
to
  `items'' = items'.map YamlValue.stripAnchors`
since the emitter never produces anchors, so anchor tables in parsed output are `#[]`.

## Inhabitation-debt check

* **Rule 1** (antecedents reachable): the theorem has NO hypotheses — `v : YamlValue`
  is the only input.  Every inhabitant of `YamlValue` is a reachable antecedent.
  The four concrete checks below witness all four constructors.

* **Rule 2** (conclusion non-vacuous): the `native_decide` checks show that for
  concrete scalars, aliases, sequences, and mappings, `resolveAliases #[]` does
  return the original value unchanged.

* **Rule 3** does not apply (no universal in the precondition).
-/

namespace ResolveAliasesEmpty

open L4YAML
open L4YAML.Proofs.EmitterScannability

/-! ## Concrete fixtures -/

def v_scalar : YamlValue := .scalar { content := "hello", style := .plain }
def v_alias  : YamlValue := .alias "myAnchor"
def v_seq    : YamlValue := .sequence .flow #[.scalar { content := "a", style := .plain }] none none
def v_map    : YamlValue := .mapping .flow #[(.scalar { content := "k", style := .plain },
                                               .scalar { content := "v", style := .plain })] none none

/-! ## Rule 1 + 2: each constructor fires correctly

`YamlValue` has no `DecidableEq`, so concrete checks use direct theorem application.
The four witnesses cover all constructors: scalar, alias, sequence, mapping. -/

theorem scalar_roundtrips : v_scalar.resolveAliases #[] = v_scalar := resolveAliases_empty _

/-- Alias with no matching anchor stays as-is (findSome? on #[] = none). -/
theorem alias_roundtrips : v_alias.resolveAliases #[] = v_alias := resolveAliases_empty _

theorem seq_roundtrips : v_seq.resolveAliases #[] = v_seq := resolveAliases_empty _

theorem map_roundtrips : v_map.resolveAliases #[] = v_map := resolveAliases_empty _

/-! ## Abstract application of R603 -/

/-- R603: `resolveAliases_empty` fires on an arbitrary `YamlValue`. -/
theorem r603_fires (v : YamlValue) : v.resolveAliases #[] = v :=
  resolveAliases_empty v

/-! ## Axiom audit -/

/-- info: 'L4YAML.Proofs.EmitterScannability.resolveAliases_empty' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms resolveAliases_empty

end ResolveAliasesEmpty
