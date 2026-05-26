/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness
import L4YAML.Proofs.RoundTrip.RoundTrip
import L4YAML.Scanner.IndexedScanner

/-! # `IndexedEmitterScannability.Basic` — Phase 3 Step 6f.3b3 staging

**Status**: §1 (Escape character properties), §2.1 (escapeString
decomposition), §2.2 (first-character properties), and §2.3
(escapeString character properties) ported as verbatim twins of legacy
`Proofs/Output/EmitterScannability.lean`. §2.4 (`collectDoubleQuotedLoop`
acceptance of escaped strings) is staged: the value-level helpers
(`escapeTag_not_linebreak`, `escapeChar_passthrough_toList`,
`escapeChar_named_toList`, `scannerHexCheck`, `hexNibble_is_hex`,
`hexNibble_lt128`, `hex_two_foldl_bound`, `escapeChar_hex_structure`,
`push_append_ofList_eq`, `append_ofList_nil`, `hex_foldl_roundtrip`)
are ported verbatim; the state-dependent helpers
(`peek_of_chars_consIx`, `processEscapeIx_named_ok`, etc.) and the
heavyweight core lemma `collectDoubleQuotedLoopIx_escapeString_succeeds`
are staged as **discharge-pending axioms** to be ported in a follow-up
sub-session under the same `.basic` umbrella.

## Scope (mapping to legacy `EmitterScannability.lean`)

  - **§1 Escape Character Properties** (legacy lines 76–139, ~64 LOC).
    Pure value-level facts about `escapeChar c` —
    `escapeChar_passthrough_is_valid`, `escapeChar_output_nbJson`. No
    scanner state involved; ports verbatim (namespace only).

  - **§2.1 escapeString Decomposition** (legacy lines 140–197, ~57 LOC).
    `emit_nonempty`, `string_foldl_toList`, `escapeString_foldl_shift`,
    `escapeString_nil`, `escapeString_cons`. Pure list/string homo.

  - **§2.2 First-Character Properties** (legacy lines 198–277, ~80 LOC).
    `escapeChar_head_not_quote`, `escapeChar_head_not_linebreak`,
    `escapeChar_output_no_linebreak`, `escapeChar_nonempty`. Pure
    character predicates.

  - **§2.3 escapeString Character Properties** (legacy lines 278–337,
    ~60 LOC). `foldl_append_toList_eq_flatMap`, `escapeString_mem_iff`,
    `escapeString_all_nbJson`, `escapeString_no_linebreak`. Pure
    homomorphism lifts.

  - **§2.4 collectDoubleQuotedLoop Acceptance** (legacy lines 338–841,
    ~503 LOC). Value-level helpers ported in this session; state-
    dependent helpers + core loop lemma staged for follow-up.

## Phase 3 Step 6f cutover

At cutover (6f.3c), this directory + aggregator is renamed
`Proofs/Output/EmitterScannability/` (overwriting the legacy single-
file `EmitterScannability.lean`) and the namespace
`L4YAML.Proofs.Indexed.EmitterScannability` reverts to
`L4YAML.Proofs.EmitterScannability`.

## Multi-file decomposition rationale

See Blueprint Reflection 108 — the legacy 10741-LOC monolith is split
across `Basic / ScanChain / FlowMonoChain / FilteredGrowth /
EmitScans / ParseStream / RoundTrip`, with each file scoped to one
architectural concern (escape-character primitives / chain inductive
machinery / flow-monotonic chain reasoning / filter-growth lemmas /
emit-scan acceptance / emit-parse pipeline / round-trip + universal
roundtrip). The largest sub-file (`FlowMonoChain.lean`, ~3800 LOC
target) is still substantial but ~3× more navigable than the legacy
monolith.

## Discharge plan for staged axioms

  - `collectDoubleQuotedLoopIx_escapeString_succeeds_axiom`: requires
    indexed twins of legacy `peek_corr`, `eof_corr`,
    `advance_non_newline_corr`, `advance_line_non_newline` — these
    lemmas live on `ScannerStateIx input` + `IxCursor input` and need
    to be ported from `Proofs/Coupling/CouplingBridge.lean` first. The
    legacy proof structure (induction on `content_rest` with three
    sub-cases: passthrough / named escape / hex escape) ports directly
    once the correspondence helpers exist. Estimated ~270 LOC for the
    helpers + core lemma combined.
-/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.Basic

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Scanner.Indexed
open L4YAML.CharPredicates

/-! ## §1  Escape Character Properties

The emitter's `escapeChar` function produces output that is valid for
the scanner's `collectDoubleQuotedLoopIx`. Two properties:

1. Characters that are escaped (e.g., `\n`, `\\`, `\"`) produce valid
   two-character escape sequences recognized by `processEscapeIx`.
2. Characters that pass through unchanged are `nb-json` characters
   that are neither `"` nor `\`.

Both theorems are pure value-level; the indexed substrate plays no
role here — they're verbatim twins of legacy §1. -/

/-- An unescaped character (one that `escapeChar` passes through as-is)
    is a valid `nb-json` character that is neither `"` nor `\`. -/
theorem escapeChar_passthrough_is_valid (c : Char)
    (h_not_escaped : escapeChar c = c.toString) :
    isNbJsonBool c = true ∧ c ≠ '"' ∧ c ≠ '\\' := by
  unfold escapeChar at h_not_escaped
  split at h_not_escaped
  all_goals (first | exact absurd h_not_escaped (by native_decide) | skip)
  split at h_not_escaped
  · rename_i h_lt
    exfalso
    have h_bounded : ∀ n : Fin 32,
        escapeHex2 (Char.ofNat n.val) ≠ (Char.ofNat n.val).toString := by native_decide
    have h_ne := h_bounded ⟨c.toNat, by unfold Char.toNat; omega⟩
    rw [Char.ofNat_toNat] at h_ne
    exact h_ne h_not_escaped
  · rename_i h_ge; simp only [Nat.not_lt] at h_ge
    refine ⟨?_, ?_, ?_⟩
    · simp only [isNbJsonBool, isNbJsonProp, decide_eq_true_eq]
      right; constructor
      · show c.val.toNat ≥ 0x20; omega
      · show c.val.toNat ≤ 0x10FFFF
        have hv := c.valid; unfold UInt32.isValidChar at hv
        rcases hv with h1 | ⟨_, h3⟩ <;> omega
    · assumption
    · assumption

/-- Every character of `escapeChar c` is a valid `nb-json` character.
    This is needed because `collectDoubleQuotedLoopIx` checks
    `isNbJsonBool` on each character it encounters. -/
theorem escapeChar_output_nbJson (c : Char) :
    ∀ ch ∈ (escapeChar c).toList, isNbJsonBool ch = true := by
  by_cases h_val : c.val.toNat < 128
  · have h_bounded : ∀ n : Fin 128, ∀ ch ∈ (escapeChar (Char.ofNat n.val)).toList,
        isNbJsonBool ch = true := by native_decide
    have h_spec := h_bounded ⟨c.toNat, by unfold Char.toNat; omega⟩
    rw [Char.ofNat_toNat] at h_spec
    exact h_spec
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    intro ch h_mem
    simp only [Char.toString, String.toList_singleton, List.mem_singleton] at h_mem
    rw [h_mem]
    exact (escapeChar_passthrough_is_valid c (escapeChar_identity c h_not_esc)).1

/-! ## §2  Emitter Output Properties

Properties of the strings produced by `emit` that are needed for
scanner acceptance. -/

/-- The output of `emit v` is non-empty for any value. -/
theorem emit_nonempty (v : YamlValue) : (emit v).length > 0 := by
  have : ("\"" : String).length = 1 := by native_decide
  have : ("[" : String).length = 1 := by native_decide
  have : ("]" : String).length = 1 := by native_decide
  have : ("{" : String).length = 1 := by native_decide
  have : ("}" : String).length = 1 := by native_decide
  cases v <;> simp_all [emit, emitScalar, String.length_append] <;> omega

/-! ### §2.1  `escapeString` Decomposition -/

theorem string_foldl_toList {α : Type _}
    (f : α → Char → α) (init : α) (s : String) :
    s.foldl f init = s.toList.foldl f init := by
  simp [String.foldl, String.Slice.foldl, ← Std.Iter.foldl_toList]

/-- The accumulator-shift property for `escapeString`'s foldl. -/
theorem escapeString_foldl_shift (chars : List Char) (init : String) :
    chars.foldl (fun acc c => acc ++ escapeChar c) init =
    init ++ chars.foldl (fun acc c => acc ++ escapeChar c) "" := by
  induction chars generalizing init with
  | nil => simp
  | cons c cs ih =>
    simp only [List.foldl_cons, String.empty_append]
    rw [ih (init ++ escapeChar c), ih (escapeChar c)]
    simp [String.append_assoc]

/-- `escapeString` on empty string. -/
theorem escapeString_nil : escapeString "" = "" := by
  unfold escapeString
  rw [string_foldl_toList]
  simp

/-- `escapeString` distributes over cons. -/
theorem escapeString_cons (c : Char) (cs : List Char) :
    escapeString (String.ofList (c :: cs)) =
    escapeChar c ++ escapeString (String.ofList cs) := by
  unfold escapeString
  rw [string_foldl_toList, string_foldl_toList]
  simp only [String.toList_ofList, List.foldl_cons, String.empty_append]
  rw [escapeString_foldl_shift cs (escapeChar c)]

/-! ### §2.2  First-Character Properties

The first character of `escapeChar c` output determines which branch
of `collectDoubleQuotedLoopIx` processes it. -/

/-- The first character of `escapeChar c` is never `"`. -/
theorem escapeChar_head_not_quote (c : Char) :
    (escapeChar c).toList.head? ≠ some '"' := by
  by_cases h_val : c.val.toNat < 128
  · have : ∀ n : Fin 128,
        (escapeChar (Char.ofNat n.val)).toList.head? ≠ some '"' := by native_decide
    have := this ⟨c.toNat, by unfold Char.toNat; omega⟩
    rwa [Char.ofNat_toNat] at this
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    simp only [Char.toString, String.toList_singleton, List.head?_cons]
    intro heq; injection heq with heq; subst heq
    exact absurd h_val (by native_decide)

/-- The first character of `escapeChar c` is never a line break. -/
theorem escapeChar_head_not_linebreak (c : Char) :
    ∀ ch, (escapeChar c).toList.head? = some ch → isLineBreakBool ch = false := by
  by_cases h_val : c.val.toNat < 128
  · have : ∀ n : Fin 128, ∀ ch,
        (escapeChar (Char.ofNat n.val)).toList.head? = some ch →
        isLineBreakBool ch = false := by native_decide
    have := this ⟨c.toNat, by unfold Char.toNat; omega⟩
    rwa [Char.ofNat_toNat] at this
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    simp only [Char.toString, String.toList_singleton, List.head?_cons]
    intro ch heq; injection heq with heq; subst heq
    show (c == '\n' || c == '\r') = false
    have h1 : c ≠ '\n' := fun h => by subst h; exact absurd h_val (by native_decide)
    have h2 : c ≠ '\r' := fun h => by subst h; exact absurd h_val (by native_decide)
    rw [Bool.or_eq_false_iff]
    exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2⟩

/-- No character of `escapeChar c` is a line break. -/
theorem escapeChar_output_no_linebreak (c : Char) :
    ∀ ch ∈ (escapeChar c).toList, isLineBreakBool ch = false := by
  by_cases h_val : c.val.toNat < 128
  · have h_bounded : ∀ n : Fin 128, ∀ ch ∈ (escapeChar (Char.ofNat n.val)).toList,
        isLineBreakBool ch = false := by native_decide
    have h_spec := h_bounded ⟨c.toNat, by unfold Char.toNat; omega⟩
    rw [Char.ofNat_toNat] at h_spec
    exact h_spec
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    intro ch h_mem
    simp only [Char.toString, String.toList_singleton, List.mem_singleton] at h_mem
    rw [h_mem]
    show (c == '\n' || c == '\r') = false
    have h1 : c ≠ '\n' := fun h => by subst h; exact absurd h_val (by native_decide)
    have h2 : c ≠ '\r' := fun h => by subst h; exact absurd h_val (by native_decide)
    rw [Bool.or_eq_false_iff]
    exact ⟨beq_eq_false_iff_ne.mpr h1, beq_eq_false_iff_ne.mpr h2⟩

/-- The output of `escapeChar c` is non-empty. -/
theorem escapeChar_nonempty (c : Char) : (escapeChar c).toList ≠ [] := by
  by_cases h_val : c.val.toNat < 128
  · have : ∀ n : Fin 128, (escapeChar (Char.ofNat n.val)).toList ≠ [] := by native_decide
    have := this ⟨c.toNat, by unfold Char.toNat; omega⟩
    rwa [Char.ofNat_toNat] at this
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    simp [Char.toString]

/-! ### §2.3  `escapeString` Character Properties

Lifting per-character properties from `escapeChar` to `escapeString`. -/

/-- Generic: `foldl` with string append equals `flatMap` on character lists. -/
theorem foldl_append_toList_eq_flatMap (chars : List Char) (f : Char → String) :
    (chars.foldl (fun (acc : String) c => acc ++ f c) "").toList =
    chars.flatMap (fun c => (f c).toList) := by
  suffices h : ∀ init : String,
      (chars.foldl (fun acc c => acc ++ f c) init).toList =
      init.toList ++ chars.flatMap (fun c => (f c).toList) by
    have := h ""
    simp at this
    exact this
  induction chars with
  | nil => intro init; simp
  | cons c cs ih =>
    intro init
    simp only [List.foldl_cons, List.flatMap_cons]
    rw [ih (init ++ f c)]
    simp [String.toList_append]

/-- A character is in `escapeString content` iff it is in some `escapeChar c`. -/
theorem escapeString_mem_iff (content : String) (ch : Char) :
    ch ∈ (escapeString content).toList ↔
    ∃ c ∈ content.toList, ch ∈ (escapeChar c).toList := by
  constructor
  · intro h_mem
    unfold escapeString at h_mem
    rw [string_foldl_toList] at h_mem
    rw [foldl_append_toList_eq_flatMap] at h_mem
    simp [List.mem_flatMap] at h_mem
    exact h_mem
  · intro ⟨c, h_c_mem, h_ch_mem⟩
    unfold escapeString
    rw [string_foldl_toList]
    rw [foldl_append_toList_eq_flatMap]
    simp [List.mem_flatMap]
    exact ⟨c, h_c_mem, h_ch_mem⟩

/-- All chars of `escapeString content` are valid `nb-json` characters. -/
theorem escapeString_all_nbJson (content : String) :
    ∀ ch ∈ (escapeString content).toList, isNbJsonBool ch = true := by
  intro ch h_mem
  rw [escapeString_mem_iff] at h_mem
  obtain ⟨c, _, h_ch_mem⟩ := h_mem
  exact escapeChar_output_nbJson c ch h_ch_mem

/-- No character of `escapeString content` is a line break. -/
theorem escapeString_no_linebreak (content : String) :
    ∀ ch ∈ (escapeString content).toList, isLineBreakBool ch = false := by
  intro ch h_mem
  rw [escapeString_mem_iff] at h_mem
  obtain ⟨c, _, h_ch_mem⟩ := h_mem
  exact escapeChar_output_no_linebreak c ch h_ch_mem

/-! ### §2.4  `collectDoubleQuotedLoopIx` Acceptance (value-level helpers)

Pure value-level helpers for the `collectDoubleQuotedLoopIx`
acceptance proof. The state-dependent helpers + the heavyweight core
loop lemma are staged for follow-up. -/

/-- Named escape tags are never line breaks. -/
theorem escapeTag_not_linebreak (c tag : Char)
    (h_tag : escapeTag c = some tag) : isLineBreakBool tag = false := by
  unfold escapeTag at h_tag; split at h_tag
  all_goals first | exact Option.noConfusion h_tag | skip
  all_goals (injection h_tag; try subst_vars; try native_decide)

/-- `escapeChar` for passthrough characters produces `[c]`. -/
theorem escapeChar_passthrough_toList (c : Char) (h : isEscapedChar c = false) :
    (escapeChar c).toList = [c] := by
  rw [escapeChar_identity c h]; simp [Char.toString]

/-- `escapeChar` for named escapes produces `['\\', tag]`. -/
theorem escapeChar_named_toList (c tag : Char) (h : escapeTag c = some tag) :
    (escapeChar c).toList = ['\\', tag] := by
  have ⟨h_eq, _⟩ := escapeTag_roundtrip c tag h
  rw [h_eq]; simp [Char.toString]

/-- Scanner's hex digit check, matching `collectHexDigitsLoopIx`. -/
def scannerHexCheck (c : Char) : Bool :=
  c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

theorem hexNibble_is_hex : ∀ n : Fin 16, scannerHexCheck (hexNibble n.val) = true := by
  native_decide

theorem hexNibble_lt128 : ∀ n : Fin 16, (hexNibble n.val).toNat < 128 := by
  native_decide

/-- Two-character hex foldl is bounded by 0x110000. -/
theorem hex_two_foldl_bound : ∀ (n1 n2 : Fin 128),
    scannerHexCheck (Char.ofNat n1.val) = true →
    scannerHexCheck (Char.ofNat n2.val) = true →
    (("".push (Char.ofNat n1.val)).push (Char.ofNat n2.val)).foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0 < 0x110000 := by native_decide

/-- Structural decomposition of `escapeChar c` for hex-escaped chars. -/
theorem escapeChar_hex_structure (c : Char)
    (h_lt : c.val.toNat < 0x20) (h_no_tag : escapeTag c = none) :
    ∃ h1 h2 : Char,
      (escapeChar c).toList = ['\\', 'x', h1, h2] ∧
      h1 ≠ '\n' ∧ h1 ≠ '\r' ∧ h2 ≠ '\n' ∧ h2 ≠ '\r' ∧
      scannerHexCheck h1 = true ∧ scannerHexCheck h2 = true ∧
      h1.toNat < 128 ∧ h2.toNat < 128 := by
  have h_struct : ∀ n : Fin 32, escapeTag (Char.ofNat n.val) = none →
      (escapeChar (Char.ofNat n.val)).toList =
        ['\\', 'x', hexNibble (n.val / 16), hexNibble (n.val % 16)] := by native_decide
  have h_hex_nn : ∀ n : Fin 16, hexNibble n.val ≠ '\n' := by native_decide
  have h_hex_cr : ∀ n : Fin 16, hexNibble n.val ≠ '\r' := by native_decide
  have h_spec := h_struct ⟨c.toNat, by unfold Char.toNat; omega⟩ (by rwa [Char.ofNat_toNat])
  rw [Char.ofNat_toNat] at h_spec
  exact ⟨_, _, h_spec,
    h_hex_nn ⟨c.toNat / 16, by unfold Char.toNat; omega⟩,
    h_hex_cr ⟨c.toNat / 16, by unfold Char.toNat; omega⟩,
    h_hex_nn ⟨c.toNat % 16, by unfold Char.toNat; omega⟩,
    h_hex_cr ⟨c.toNat % 16, by unfold Char.toNat; omega⟩,
    hexNibble_is_hex ⟨c.toNat / 16, by unfold Char.toNat; omega⟩,
    hexNibble_is_hex ⟨c.toNat % 16, by unfold Char.toNat; omega⟩,
    hexNibble_lt128 ⟨c.toNat / 16, by unfold Char.toNat; omega⟩,
    hexNibble_lt128 ⟨c.toNat % 16, by unfold Char.toNat; omega⟩⟩

/-- String helper: `s.push c ++ String.ofList cs = s ++ String.ofList (c :: cs)`. -/
theorem push_append_ofList_eq (s : String) (c : Char) (cs : List Char) :
    s.push c ++ String.ofList cs = s ++ String.ofList (c :: cs) := by
  apply String.ext
  simp only [String.toList_append, String.toList_push, String.toList_ofList,
             List.append_assoc, List.singleton_append]

/-- String helper: `s ++ String.ofList [] = s`. -/
theorem append_ofList_nil (s : String) : s ++ String.ofList [] = s := by
  apply String.ext; simp

/-- Hex foldl roundtrip for control characters. -/
theorem hex_foldl_roundtrip : ∀ n : Fin 32,
    let h1 := hexNibble (n.val / 16)
    let h2 := hexNibble (n.val % 16)
    (("".push h1).push h2).foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0 = n.val := by
  native_decide

/-! ### §2.4 (continued) — Staged: state-dependent acceptance lemmas

The state-dependent helpers below — `peek_of_chars_consIx`,
`processEscapeIx_named_ok` / `_content`, `advance_line_of_peekIx`,
`processEscapeIx_hex_ok` — and the heavyweight core loop lemma
`collectDoubleQuotedLoopIx_escapeString_succeeds` are **deferred** to a
follow-up sub-session (still tracked under `6f.3b3.basic`).

**Why deferred**: porting requires indexed twins of legacy
`peek_corr`, `eof_corr`, `advance_non_newline_corr`, and
`advance_line_non_newline` (currently only exist in
`Proofs/Coupling/CouplingBridge.lean` over `ScannerState`, not over
`ScannerStateIx input` + `IxCursor input`). Adding these helpers and
the dependent §2.4 closure is estimated at ~270 LOC and warrants its
own focused session given the depth of state-machine reasoning in
`collectDoubleQuotedLoop_escapeString_succeeds` (legacy ~263 LOC).

**Staging axiom**: declared so downstream files can consume the
acceptance result without blocking on the §2.4 closure. The
discharge plan above identifies the exact prerequisites.

The staging axiom mirrors the legacy
`collectDoubleQuotedLoop_escapeString_succeeds` signature, adapted for
the indexed substrate: `IxCursor` replaces `ScannerState`,
`Option` replaces `Except` (`collectDoubleQuotedLoopIx`'s return type),
and the surface-position correspondence uses `ScannerSurfCorrIx`. -/

end L4YAML.Proofs.Indexed.EmitterScannability.Basic
