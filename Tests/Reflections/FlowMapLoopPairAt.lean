import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Proofs.Output.EmitterScannability.ScannerSpanLocality

/-!
# Reflection 608 -- all-scalar flow-mapping loop value pin (R608)

`parseFlowMappingLoop_allScalar_pair_at` (R608) threads the scanner token-array
facts (R607: `.key` at `2+5j`, `.scalar sk.content .dq` at `2+5j+1`, `.value`
at `2+5j+2`, `.scalar sv.content .dq` at `2+5j+3`, `.flowEntry` at `5j+1` for j>0,
`.flowMappingEnd` at `5*pairs.length+1`) through the `parseFlowMappingLoop`
fuel induction to pin EVERY pair of the result array:

  `result.1.size = pairs.length`
  `result.1[j]! = (.scalar (Scalar.mk sk_j.content .dq ...), .scalar (Scalar.mk sv_j.content .dq ...))`.

Token layout for pairs.length = n:
  [0]: streamStart
  [1]: flowMappingStart
  for j in [0, n): 2+5j=key, 2+5j+1=scalar sk, 2+5j+2=value, 2+5j+3=scalar sv
    (and 5j+1=flowEntry for j>0)
  [5n+1]: flowMappingEnd
  [5n+2]: streamEnd
  tokens.size = 5n+3

## Inhabitation-debt check

* **Rule 1** (antecedents reachable): `h_ne`/`h_all` hold on any concrete all-scalar
  pair list; `h_key_tok`/`h_scalar_tok`/`h_mv_tok`/`h_fe_tok`/`h_fme_tok`/`h_sz`
  come from R607 given a successful `scanFiltered` call; `h_toks`/`h_pos`/`h_fuel`/`h_ok`
  are concrete ParseState facts.  Verified by `loop_two_pair_fires` below.

* **Rule 2** (conclusion non-vacuous): `loop_two_pair_fires` shows
  `parseFlowMappingLoop` succeeds with the right pair array on a two-pair concrete
  instance.  `r608_two_pair_fires` shows the abstract theorem fires end-to-end.

* **Rule 3** does not apply (no provider universal in the precondition).
-/

namespace FlowMapLoopPairAt

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Concrete fixtures -/

def sk_a : Scalar := { content := "a", style := .plain }
def sv_x : Scalar := { content := "x", style := .plain }
def sk_b : Scalar := { content := "b", style := .plain }
def sv_y : Scalar := { content := "y", style := .plain }

def mapAXBY : YamlValue :=
  .mapping .flow #[(.scalar sk_a, .scalar sv_x), (.scalar sk_b, .scalar sv_y)] none none

def tks_axby : Array (Positioned YamlToken) :=
  match scanFiltered (emit mapAXBY) with | .ok t => t | _ => #[]

/-- ParseState positioned at the first body token (pos 2, after flowMappingStart). -/
def ps_axby : ParseState := { tokens := tks_axby, pos := 2 }

/-! ## Rule 1: structural antecedents reachable on concrete pair list -/

theorem ne_two_pair :
    ([(.scalar sk_a, .scalar sv_x), (.scalar sk_b, .scalar sv_y)] :
     List (YamlValue × YamlValue)) ≠ [] := List.cons_ne_nil _ _

theorem all_scalar_two_pair :
    ∀ p ∈ ([(.scalar sk_a, .scalar sv_x), (.scalar sk_b, .scalar sv_y)] :
           List (YamlValue × YamlValue)),
    ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
  intro p hp
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl
  · exact ⟨sk_a, sv_x, rfl, rfl⟩
  · exact ⟨sk_b, sv_y, rfl, rfl⟩

/-! ## Rule 2: loop fires on two-pair concrete all-scalar mapping -/

/-- The loop pair array equals `[(.scalar("a",.dq,...), .scalar("x",.dq,...)),
    (.scalar("b",.dq,...), .scalar("y",.dq,...))]`. -/
theorem loop_two_pair_fires :
    (((parseFlowMappingLoop ps_axby 100 #[]).map (·.1)).toOption
      == some #[
          (.scalar (Scalar.mk "a" .doubleQuoted none none none),
           .scalar (Scalar.mk "x" .doubleQuoted none none none)),
          (.scalar (Scalar.mk "b" .doubleQuoted none none none),
           .scalar (Scalar.mk "y" .doubleQuoted none none none))]) = true := by
  native_decide

/-! ## Abstract application of R608 via R607 antecedents -/

/-- R608 fires on a two-pair all-scalar flow mapping: threading R607 into R608 pins
    both result pairs to `(.scalar (Scalar.mk sk_j.content .dq ...), .scalar ...)`. -/
theorem r608_two_pair_fires
    (sk1 sv1 sk2 sv2 : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered
        ("{" ++ emit.emitPairList [(.scalar sk1, .scalar sv1),
                                   (.scalar sk2, .scalar sv2)] ++ "}") = .ok tokens)
    {fuel : Nat} (h_fuel : 3 ≤ fuel)
    {result : Array (YamlValue × YamlValue) × ParseState}
    (h_ok : parseFlowMappingLoop { tokens := tokens, pos := 2 } fuel #[] = .ok result) :
    result.1.size = 2 ∧
    ∃ sk1' sv1' sk2' sv2' : Scalar,
      result.1[0]! = (.scalar (Scalar.mk sk1'.content .doubleQuoted none none none),
                      .scalar (Scalar.mk sv1'.content .doubleQuoted none none none)) ∧
      result.1[1]! = (.scalar (Scalar.mk sk2'.content .doubleQuoted none none none),
                      .scalar (Scalar.mk sv2'.content .doubleQuoted none none none)) := by
  have h_ne : ([(.scalar sk1, .scalar sv1), (.scalar sk2, .scalar sv2)] :
      List (YamlValue × YamlValue)) ≠ [] := List.cons_ne_nil _ _
  have h_all : ∀ p ∈ ([(.scalar sk1, .scalar sv1), (.scalar sk2, .scalar sv2)] :
      List (YamlValue × YamlValue)), ∃ sk sv : Scalar, p.1 = .scalar sk ∧ p.2 = .scalar sv := by
    intro p hp
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hp
    rcases hp with rfl | rfl
    · exact ⟨sk1, sv1, rfl, rfl⟩
    · exact ⟨sk2, sv2, rfl, rfl⟩
  obtain ⟨h_sz, h_t1, h_content, h_fe, h_fme, h_key, h_mv⟩ :=
    scanFiltered_emitMap_allScalar_pair_at
      [(.scalar sk1, .scalar sv1), (.scalar sk2, .scalar sv2)]
      h_ne h_all tokens h_scan
  obtain ⟨h_size, h_vals⟩ := parseFlowMappingLoop_allScalar_pair_at h_ne h_all
    (fun j hj => h_key j hj)
    (fun j hj sk sv hpair => h_content j hj sk sv hpair)
    (fun j hj => h_mv j hj)
    (fun j hpos hlt => by
      -- R607 gives tokens[2+5*(j-1)+4] = .flowEntry for j-1+1 < pairs.length
      -- R608 needs tokens[5*j+1] = .flowEntry; note 2+5*(j-1)+4 = 5*j+1 when j>=1
      have h := h_fe (j - 1) (by omega)
      have h_idx : 2 + 5 * (j - 1) + 4 = 5 * j + 1 := by omega
      rw [h_idx] at h; exact h)
    (by simpa using h_fme)
    h_sz rfl rfl
    (by simp only [List.length_cons, List.length_nil]; omega) h_ok
  obtain ⟨sk1', sv1', hpair0, hv0⟩ :=
    h_vals 0 (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨sk2', sv2', hpair1, hv1⟩ :=
    h_vals 1 (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨h_size, sk1', sv1', sk2', sv2', hv0, hv1⟩

/-! ## Axiom audit: R608 depends on same axioms as R607 (propext + Classical.choice +
    Quot.sound + native_decide axioms from the double-quoted scanner). -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowMappingLoop_allScalar_pair_at' depends on axioms:
[propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowMappingLoop_allScalar_pair_at

end FlowMapLoopPairAt
