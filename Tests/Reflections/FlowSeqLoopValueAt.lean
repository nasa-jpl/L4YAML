import L4YAML.Proofs.Output.EmitterScannability.ContentFidelity
import L4YAML.Proofs.Output.EmitterScannability.ScannerSpanLocality

/-!
# Reflection 601 -- all-scalar flow-sequence loop value pin (R601)

`parseFlowSeqLoop_allScalar_value_at` (§5.18) threads the scanner token-array
facts (R597: `tokens[2+2*j]! = .scalar sc.content .doubleQuoted`) through the
`parseFlowSequenceLoop` fuel induction to pin EVERY element of the result array:

  `result.1.size = items.length`
  `result.1[j]! = .scalar (Scalar.mk sc_j.content .doubleQuoted none none none)`.

## Inhabitation-debt check

* **Rule 1** (antecedents reachable): `h_ne`/`h_all` hold on any concrete all-scalar
  list; `h_scalar_tok`/`h_fe_tok`/`h_fse_tok`/`h_sz` come from R597 given a successful
  `scanFiltered` call; `h_toks`/`h_pos`/`h_fuel`/`h_ok` are concrete ParseState facts.
  Verified by `ne_ab`, `all_scalar_ab`, and `loop_ab_fires` below.

* **Rule 2** (conclusion non-vacuous): `loop_ab_fires` shows `parseFlowSequenceLoop`
  succeeds with the right value array on a two-element concrete instance.
  `r601_two_elem_fires` shows the abstract theorem fires end-to-end.

* **Rule 3** does not apply (no provider universal in the precondition).
-/

namespace FlowSeqLoopValueAt

open L4YAML
open L4YAML.Emit
open L4YAML.Scanner
open L4YAML.TokenParser
open L4YAML.Proofs.EmitterScannability

/-! ## Concrete fixtures -/

def sc_a : Scalar := { content := "a", style := .plain }
def sc_b : Scalar := { content := "b", style := .plain }

def seqAB : YamlValue := .sequence .flow #[.scalar sc_a, .scalar sc_b] none none

def tks_ab : Array (Positioned YamlToken) :=
  match scanFiltered (emit seqAB) with | .ok t => t | _ => #[]

/-- ParseState positioned at the first body token (pos 2, after flowSequenceStart). -/
def ps_ab : ParseState := { tokens := tks_ab, pos := 2 }

/-! ## Rule 1: structural antecedents reachable on concrete list -/

theorem ne_ab : ([.scalar sc_a, .scalar sc_b] : List YamlValue) ≠ [] := List.cons_ne_nil _ _

theorem all_scalar_ab :
    ∀ v ∈ ([.scalar sc_a, .scalar sc_b] : List YamlValue), ∃ sc : Scalar, v = .scalar sc := by
  intro v hv
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
  rcases hv with rfl | rfl
  · exact ⟨sc_a, rfl⟩
  · exact ⟨sc_b, rfl⟩

/-! ## Rule 2: loop fires on two-element concrete all-scalar sequence -/

/-- The loop value array equals `[.scalar ("a", .dq, ...), .scalar ("b", .dq, ...)]`. -/
theorem loop_ab_fires :
    (((parseFlowSequenceLoop ps_ab 100 #[]).map (·.1)).toOption
      == some #[.scalar (Scalar.mk "a" .doubleQuoted none none none),
               .scalar (Scalar.mk "b" .doubleQuoted none none none)]) = true := by
  native_decide

/-! ## Abstract application of R601 via R597 antecedents -/

/-- R601 fires on a two-element all-scalar list: threading R597 into R601 pins both
    result elements to `.scalar (Scalar.mk sc_j.content .doubleQuoted none none none)`. -/
theorem r601_two_elem_fires
    (sca scb : Scalar)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered
        ("[" ++ emit.emitList [.scalar sca, .scalar scb] ++ "]") = .ok tokens)
    {fuel : Nat} (h_fuel : 3 ≤ fuel)
    {result : Array YamlValue × ParseState}
    (h_ok : parseFlowSequenceLoop { tokens := tokens, pos := 2 } fuel #[] = .ok result) :
    result.1.size = 2 ∧
    ∃ sc0 sc1 : Scalar,
      result.1[0]! = .scalar (Scalar.mk sc0.content .doubleQuoted none none none) ∧
      result.1[1]! = .scalar (Scalar.mk sc1.content .doubleQuoted none none none) := by
  have h_ne : ([.scalar sca, .scalar scb] : List YamlValue) ≠ [] := List.cons_ne_nil _ _
  have h_all : ∀ v ∈ ([.scalar sca, .scalar scb] : List YamlValue), ∃ sc : Scalar, v = .scalar sc := by
    intro v hv
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv
    rcases hv with rfl | rfl
    · exact ⟨sca, rfl⟩
    · exact ⟨scb, rfl⟩
  obtain ⟨h_sz, _, h_content, h_fe, h_fse⟩ :=
    scanFiltered_emitSeq_allScalar_token_at [.scalar sca, .scalar scb] h_ne h_all tokens h_scan
  obtain ⟨h_size, h_vals⟩ := parseFlowSeqLoop_allScalar_value_at h_ne h_all
    h_content h_fe h_fse h_sz rfl rfl
    (by simp only [List.length_cons, List.length_nil]; omega) h_ok
  obtain ⟨sc0, _, hv0⟩ := h_vals 0 (by simp only [List.length_cons, List.length_nil]; omega)
  obtain ⟨sc1, _, hv1⟩ := h_vals 1 (by simp only [List.length_cons, List.length_nil]; omega)
  exact ⟨h_size, sc0, sc1, hv0, hv1⟩

/-! ## Axiom audit: R601 depends on [propext, Classical.choice, Quot.sound] -/

/-- info: 'L4YAML.Proofs.EmitterScannability.parseFlowSeqLoop_allScalar_value_at' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs (whitespace := lax) in
#print axioms parseFlowSeqLoop_allScalar_value_at

end FlowSeqLoopValueAt
