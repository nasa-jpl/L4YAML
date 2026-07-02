/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Scanner.IndexedScannerCorrectness
import L4YAML.Proofs.RoundTrip.RoundTrip
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Scanner.IndexedScanner

/-! # `IndexedEmitterScannability.Basic` — Phase 3 Step 6f.3b3 (`.basic` landed)

**Status**: fully landed. §1–§2 (value-level escape-character and
emit-output facts) and §3 (cursor-level surface correspondence +
`collectDoubleQuotedLoopIx` acceptance closure) are ported as twins
of legacy `Proofs/Output/EmitterScannability.lean`. No axioms remain.

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

  - **§2.4 collectDoubleQuotedLoop Acceptance — value-level helpers**
    (legacy lines 338–456 value-level slice). `escapeTag_not_linebreak`,
    `escapeChar_passthrough_toList`, `escapeChar_named_toList`,
    `scannerHexCheck`, `hexNibble_is_hex`, `hexNibble_lt128`,
    `hex_two_foldl_bound`, `escapeChar_hex_structure`,
    `push_append_ofList_eq`, `append_ofList_nil`,
    `hex_foldl_roundtrip`.

  - **§3 collectDoubleQuotedLoopIx Acceptance — closure** (legacy
    lines 355–841 state-dependent slice). Cursor-level surface
    correspondence (`CursorSurfCorrIx`); indexed advance helpers
    (`peek_corrIx`, `eof_corrIx`, `advance_non_newline_corrIx`,
    `advance_line_non_newline_ix`); state-dependent helpers
    (`peek_of_chars_consIx`, `processEscapeIx_named_ok` /
    `_content`, `processEscapeIx_hex_ok`, `advance_line_of_peekIx`);
    and the core loop lemma
    `collectDoubleQuotedLoopIx_escapeString_succeeds`. Shape changes
    from legacy: `IxCursor` substitutes for `ScannerState`, `Option`
    for `Except`, and the loop's `isNbJsonBool` check is dropped (the
    indexed loop accepts any non-`"`/non-`\\`/non-linebreak char).

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
architectural concern. -/

set_option autoImplicit false

namespace L4YAML.Proofs.Indexed.EmitterScannability.Basic

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Scanner.Indexed
open L4YAML.CharPredicates
open L4YAML.Indexed
open L4YAML.Surface
open L4YAML.Proofs.CouplingBridge

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

/-! ## §3  `collectDoubleQuotedLoopIx` Acceptance — closure

State-dependent closure of §2.4. Imports the cursor-level surface
correspondence (`CursorSurfCorrIx`), indexed advance helpers,
state-dependent escape helpers, and the heavyweight core loop lemma.

The cursor-level correspondence is a 3-field "lite" version of
`ScannerSurfCorrIx` (without the indent-cols-nonneg field) — it
matches `IxCursor` rather than `ScannerStateIx`, fitting
`collectDoubleQuotedLoopIx`'s cursor-centric signature. The state-level
correspondence in `ScanChain.lean` §1.3 is the `IxCursor` + indent
extension and decomposes to this one. -/

/-! ### §3.0  Cursor-level surface correspondence -/

/-- Cursor state and surface position correspond when the remaining
    characters match, columns agree, and the offset is at a valid
    UTF-8 boundary. Cursor-level twin of legacy `ScannerSurfCorr`
    (`Proofs/Coupling/CouplingBridge.lean:212`), stripped of the
    indent-cols-nonneg invariant — that field lives at scanner-state
    level and is preserved orthogonally to cursor advancement. -/
structure CursorSurfCorrIx {input : String} (c : IxCursor input)
    (sp : SurfPos) : Prop where
  chars_from : CharsFromOffset input c.pos.offset sp.chars
  col_eq : sp.col = c.pos.col
  input_prefix : ∃ pre, input.toList = pre ++ sp.chars ∧ listByteSize pre = c.pos.offset

/-! ### §3.1  Indexed correspondence advance helpers

Twins of legacy `peek_corr` / `eof_corr` / `advance_non_newline_corr` /
`advance_line_non_newline` (`Proofs/Coupling/CouplingBridge.lean`),
specialised to `IxCursor input`. -/

/-- If the cursor has more input, the surface position is non-empty
    and its head matches `peek?`. Twin of legacy `peek_corr`. -/
theorem peek_corrIx {input : String} (c : IxCursor input) (sp : SurfPos)
    (hcorr : CursorSurfCorrIx c sp)
    (hmore : c.pos.offset < input.utf8ByteSize) :
    ∃ ch rest, sp.chars = ch :: rest ∧ c.peek? = some ch := by
  have hcf := hcorr.chars_from
  match hsp : sp.chars, hcf with
  | [], CharsFromOffset.at_end _ hp => omega
  | ch :: rest, CharsFromOffset.cons _ _ _ _ hch _ =>
    refine ⟨ch, rest, rfl, ?_⟩
    show c.peek? = some ch
    unfold IxCursor.peek?
    rw [if_pos hmore, hch]

/-- At end of input, the surface position has no remaining characters.
    Twin of legacy `eof_corr`. -/
theorem eof_corrIx {input : String} (c : IxCursor input) (sp : SurfPos)
    (hcorr : CursorSurfCorrIx c sp)
    (heof : ¬ c.pos.offset < input.utf8ByteSize) :
    sp.chars = [] := by
  have hge : c.pos.offset ≥ input.utf8ByteSize := Nat.le_of_not_lt heof
  have hcf := hcorr.chars_from
  match hsp : sp.chars, hcf with
  | [], _ => rfl
  | _ :: _, CharsFromOffset.cons _ hp _ _ _ _ => exact absurd hp (by omega)

/-- Bridge: when `peek?` matches the surface head, project peek + bound. -/
theorem peek_of_chars_consIx {input : String} (c : IxCursor input)
    (ch : Char) (rest : List Char) (col : Nat)
    (hcorr : CursorSurfCorrIx c ⟨ch :: rest, col⟩) :
    c.peek? = some ch ∧ c.pos.offset < input.utf8ByteSize := by
  by_cases hlt : c.pos.offset < input.utf8ByteSize
  · obtain ⟨c', _, h_eq, h_peek⟩ := peek_corrIx c ⟨ch :: rest, col⟩ hcorr hlt
    exact ⟨(List.cons.inj h_eq).1 ▸ h_peek, hlt⟩
  · exact absurd (eof_corrIx c _ hcorr hlt) (List.cons_ne_nil ch rest)

/-- `IxCursor.advance` past a non-newline, non-CR character leaves the
    line unchanged. Twin of legacy `advance_line_non_newline`. -/
theorem advance_line_non_newline_ix {input : String} (c : IxCursor input)
    (h : c.pos.offset < input.utf8ByteSize)
    (hnl : ¬ (String.Pos.Raw.get input ⟨c.pos.offset⟩ == '\n') = true)
    (hcr : ¬ (String.Pos.Raw.get input ⟨c.pos.offset⟩ == '\r') = true) :
    c.advance.pos.line = c.pos.line := by
  unfold IxCursor.advance
  simp [dif_pos h, hnl, hcr]

/-- `IxCursor.advance` past a non-newline, non-CR character bumps `col`
    by 1. -/
theorem advance_col_non_newline_ix {input : String} (c : IxCursor input)
    (h : c.pos.offset < input.utf8ByteSize)
    (hnl : ¬ (String.Pos.Raw.get input ⟨c.pos.offset⟩ == '\n') = true)
    (hcr : ¬ (String.Pos.Raw.get input ⟨c.pos.offset⟩ == '\r') = true) :
    c.advance.pos.col = c.pos.col + 1 := by
  unfold IxCursor.advance
  simp [dif_pos h, hnl, hcr]

/-- Advance past a non-newline, non-CR character preserves cursor
    surface correspondence (column bumped by 1). Twin of legacy
    `advance_non_newline_corr`. -/
theorem advance_non_newline_corrIx {input : String} (c : IxCursor input)
    (ch : Char) (rest : List Char)
    (hcorr : CursorSurfCorrIx c ⟨ch :: rest, c.pos.col⟩)
    (hmore : c.pos.offset < input.utf8ByteSize)
    (hnl : ch ≠ '\n')
    (hcr : ch ≠ '\r') :
    CursorSurfCorrIx c.advance ⟨rest, c.pos.col + 1⟩ := by
  have hcf := hcorr.chars_from
  match hcf with
  | .cons _ _ _ _ hch hrest =>
    -- hch : String.Pos.Raw.get input ⟨c.pos.offset⟩ = ch
    have hnl_bool : ¬ (String.Pos.Raw.get input ⟨c.pos.offset⟩ == '\n') = true := by
      rw [hch]; simp [hnl]
    have hcr_bool : ¬ (String.Pos.Raw.get input ⟨c.pos.offset⟩ == '\r') = true := by
      rw [hch]; simp [hcr]
    -- Derive bound: c.pos.offset + ch.utf8Size ≤ input.utf8ByteSize.
    obtain ⟨pre, hsplit, hsize⟩ := hcorr.input_prefix
    have h_byte_eq : input.utf8ByteSize =
        c.pos.offset + ch.utf8Size + listByteSize rest := by
      rw [utf8ByteSize_eq_listByteSize, hsplit, listByteSize_append]
      show listByteSize pre + listByteSize (ch :: rest) =
           c.pos.offset + ch.utf8Size + listByteSize rest
      simp only [listByteSize]
      omega
    have h_next_eq : (String.Pos.Raw.next input ⟨c.pos.offset⟩).byteIdx =
        c.pos.offset + ch.utf8Size := by
      rw [next_byteIdx, hch]
    have h_next_le : (String.Pos.Raw.next input ⟨c.pos.offset⟩).byteIdx ≤
        input.utf8ByteSize := by
      rw [h_next_eq]; omega
    have h_adv_off : c.advance.pos.offset =
        (String.Pos.Raw.next input ⟨c.pos.offset⟩).byteIdx := by
      rw [IxCursor.advance_offset_eq_min_next c hmore]
      exact Nat.min_eq_left h_next_le
    refine {
      chars_from := ?_
      col_eq := ?_
      input_prefix := ?_
    }
    · rw [h_adv_off]; exact hrest
    · show c.pos.col + 1 = c.advance.pos.col
      exact (advance_col_non_newline_ix c hmore hnl_bool hcr_bool).symm
    · refine ⟨pre ++ [ch], ?_, ?_⟩
      · rw [hsplit]
        show pre ++ ch :: rest = (pre ++ [ch]) ++ rest
        rw [List.append_assoc]; rfl
      · rw [listByteSize_append]
        show listByteSize pre + listByteSize [ch] = c.advance.pos.offset
        simp only [listByteSize, Nat.add_zero]
        rw [hsize, h_adv_off, h_next_eq]

/-! ### §3.2  Indexed hex-foldl helpers

The indexed scanner uses `hexStringValue` (via `parseHexEscapeIx`) and
`isHexDigitBool` (via `collectHexDigitsLoopIx`). These differ in form
from `scannerHexCheck` and the legacy explicit-foldl below, but agree
on every ASCII hex digit by `native_decide`. -/

/-- The 2-digit hex foldl bound, restated using the indexed scanner's
    `hexStringValue`. -/
theorem hex_two_foldl_boundIx : ∀ (n1 n2 : Fin 128),
    isHexDigitBool (Char.ofNat n1.val) = true →
    isHexDigitBool (Char.ofNat n2.val) = true →
    hexStringValue (("".push (Char.ofNat n1.val)).push (Char.ofNat n2.val))
      < 0x110000 := by native_decide

/-- For C0-control chars (`c.val.toNat < 0x20`), the hex-foldl round-trip
    recovers the original code point. Indexed-scanner variant of
    `hex_foldl_roundtrip`. -/
theorem hex_foldl_roundtripIx : ∀ n : Fin 32,
    let h1 := hexNibble (n.val / 16)
    let h2 := hexNibble (n.val % 16)
    hexStringValue (("".push h1).push h2) = n.val := by native_decide

/-- `scannerHexCheck` (legacy form) and `isHexDigitBool` (indexed form)
    agree on every ASCII char. The two-digit hex content emitted by
    `escapeHex2` is ASCII, so the bridge is enough to lift
    `scannerHexCheck` witnesses to `isHexDigitBool` witnesses. -/
theorem scannerHexCheck_eq_isHexDigitBool : ∀ c : Char,
    c.toNat < 128 → scannerHexCheck c = isHexDigitBool c := by
  intro c hlt
  have h : ∀ n : Fin 128,
      scannerHexCheck (Char.ofNat n.val) = isHexDigitBool (Char.ofNat n.val) := by
    native_decide
  have := h ⟨c.toNat, by unfold Char.toNat at hlt ⊢; omega⟩
  rwa [Char.ofNat_toNat] at this

/-! ### §3.3  State-dependent escape helpers

Indexed twins of legacy `processEscape_named_ok` / `processEscape_named_content`
and `processEscape_hex_ok`. The indexed scanner factors `processEscapeIx`
through `simpleEscapeChar` (named) and `isNsEsc{8,16,32}BitBool` (hex)
rather than a direct match — the proofs use this factoring. -/

/-- The named-escape decode table `simpleEscapeChar` inverts `escapeTag`
    on every escapable character. Helper for `processEscapeIx_named_*`. -/
theorem simpleEscapeChar_of_escapeTag (origChar tag : Char)
    (h : escapeTag origChar = some tag) :
    simpleEscapeChar tag = some origChar := by
  unfold escapeTag at h
  split at h
  all_goals first
    | (simp only [Option.some.injEq] at h; subst h; decide)
    | simp at h

/-- `processEscapeIx` succeeds on a named-escape tag, returning the
    original character. Twin of legacy `processEscape_named_content`. -/
theorem processEscapeIx_named_content {input : String} (c : IxCursor input)
    (origChar tag : Char)
    (h_tag : escapeTag origChar = some tag) (h_peek : c.peek? = some tag) :
    processEscapeIx c = some (origChar, c.advance) := by
  unfold processEscapeIx
  rw [h_peek]
  dsimp only []
  rw [simpleEscapeChar_of_escapeTag origChar tag h_tag]

/-- Existential `processEscapeIx_named_content`. Twin of legacy
    `processEscape_named_ok`. -/
theorem processEscapeIx_named_ok {input : String} (c : IxCursor input)
    (origChar tag : Char)
    (h_tag : escapeTag origChar = some tag) (h_peek : c.peek? = some tag) :
    ∃ decoded, processEscapeIx c = some (decoded, c.advance) :=
  ⟨origChar, processEscapeIx_named_content c origChar tag h_tag h_peek⟩

/-- When `peek?` matches a known non-newline char, advance preserves line. -/
theorem advance_line_of_peekIx {input : String} (c : IxCursor input) (ch : Char)
    (h_lt : c.pos.offset < input.utf8ByteSize) (h_peek : c.peek? = some ch)
    (hnl : ch ≠ '\n') (hcr : ch ≠ '\r') :
    c.advance.pos.line = c.pos.line := by
  have hc : String.Pos.Raw.get input ⟨c.pos.offset⟩ = ch := by
    unfold IxCursor.peek? at h_peek
    rw [if_pos h_lt] at h_peek
    exact Option.some.inj h_peek
  exact advance_line_non_newline_ix c h_lt (by rw [hc]; simp [hnl])
    (by rw [hc]; simp [hcr])

/-- `processEscapeIx` succeeds on `x H1 H2` hex sequences produced by
    `escapeHex2`. Twin of legacy `processEscape_hex_ok`. -/
theorem processEscapeIx_hex_ok {input : String} (c : IxCursor input)
    (h1 h2 : Char) (rest : List Char) (col : Nat)
    (hcorr : CursorSurfCorrIx c ⟨'x' :: h1 :: h2 :: rest, col⟩)
    (h_h1_nn : h1 ≠ '\n') (h_h1_cr : h1 ≠ '\r')
    (h_h2_nn : h2 ≠ '\n') (h_h2_cr : h2 ≠ '\r')
    (h_h1_hex : scannerHexCheck h1 = true) (h_h2_hex : scannerHexCheck h2 = true)
    (h_h1_lt128 : h1.toNat < 128) (h_h2_lt128 : h2.toNat < 128) :
    ∃ decoded c',
      processEscapeIx c = some (decoded, c') ∧
      CursorSurfCorrIx c' ⟨rest, col + 3⟩ ∧
      c'.pos.line = c.pos.line := by
  -- Normalize col to c.pos.col.
  have h_col_eq : col = c.pos.col := hcorr.col_eq
  subst h_col_eq
  -- Bridge scannerHexCheck → isHexDigitBool (works because h1, h2 are ASCII).
  have h_h1_hexIx : isHexDigitBool h1 = true := by
    rw [← scannerHexCheck_eq_isHexDigitBool h1 h_h1_lt128]; exact h_h1_hex
  have h_h2_hexIx : isHexDigitBool h2 = true := by
    rw [← scannerHexCheck_eq_isHexDigitBool h2 h_h2_lt128]; exact h_h2_hex
  -- Step 1: peek 'x' → advance past 'x'.
  have ⟨h_peek_x, h_lt_x⟩ := peek_of_chars_consIx c 'x' (h1 :: h2 :: rest) c.pos.col hcorr
  have hcorr_x := advance_non_newline_corrIx c 'x' (h1 :: h2 :: rest) hcorr h_lt_x
    (by decide) (by decide)
  have h_col_x : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_x.col_eq
  rw [h_col_x] at hcorr_x
  -- Step 2: advance past h1.
  have ⟨h_peek_h1, h_lt_h1⟩ :=
    peek_of_chars_consIx c.advance h1 (h2 :: rest) c.advance.pos.col hcorr_x
  have hcorr_h1 := advance_non_newline_corrIx c.advance h1 (h2 :: rest) hcorr_x h_lt_h1
    h_h1_nn h_h1_cr
  have h_col_h1 : (c.advance.pos.col + 1 : Nat) = c.advance.advance.pos.col := hcorr_h1.col_eq
  rw [h_col_h1] at hcorr_h1
  -- Step 3: advance past h2.
  have ⟨h_peek_h2, h_lt_h2⟩ :=
    peek_of_chars_consIx c.advance.advance h2 rest c.advance.advance.pos.col hcorr_h1
  have hcorr_h2 := advance_non_newline_corrIx c.advance.advance h2 rest hcorr_h1 h_lt_h2
    h_h2_nn h_h2_cr
  -- Step 4: show `collectHexDigitsLoopIx` reads exactly h1, h2.
  have h_collect : collectHexDigitsLoopIx c.advance "" 2 =
      (("".push h1).push h2, c.advance.advance.advance) := by
    unfold collectHexDigitsLoopIx; dsimp only []
    rw [h_peek_h1]; dsimp only []
    simp only [h_h1_hexIx, if_true]
    unfold collectHexDigitsLoopIx; dsimp only []
    rw [h_peek_h2]; dsimp only []
    simp only [h_h2_hexIx, if_true]
    unfold collectHexDigitsLoopIx; dsimp only []
  -- Step 5: value bound for the 2-digit foldl.
  have h_val_lt := hex_two_foldl_boundIx ⟨h1.toNat, h_h1_lt128⟩ ⟨h2.toNat, h_h2_lt128⟩
    (by rw [Char.ofNat_toNat]; exact h_h1_hexIx)
    (by rw [Char.ofNat_toNat]; exact h_h2_hexIx)
  rw [Char.ofNat_toNat, Char.ofNat_toNat] at h_val_lt
  -- Step 6: unfold processEscapeIx + parseHexEscapeIx and reduce.
  unfold processEscapeIx
  rw [h_peek_x]
  dsimp only []
  have h_simple_x : simpleEscapeChar 'x' = none := by decide
  have h_8bit_x : isNsEsc8BitBool 'x' = true := by decide
  rw [h_simple_x]
  simp only [h_8bit_x, if_true]
  unfold parseHexEscapeIx
  rw [h_collect]; dsimp only []
  have h_len : (("".push h1).push h2).length = 2 := by
    simp [String.length, String.toList_push]
  simp only [h_len, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  simp only [h_val_lt, ↓reduceIte]
  -- Step 7: assemble the result. The post-loop cursor is `c.advance.advance.advance`;
  -- the post-loop col is `c.pos.col + 3`.
  have h_col_final : c.advance.advance.pos.col + 1 = c.pos.col + 3 := by omega
  rw [h_col_final] at hcorr_h2
  -- Line preservation: three non-newline advances.
  have h_line : c.advance.advance.advance.pos.line = c.pos.line := by
    have l1 := advance_line_of_peekIx c 'x' h_lt_x h_peek_x (by decide) (by decide)
    have l2 := advance_line_of_peekIx c.advance h1 h_lt_h1 h_peek_h1 h_h1_nn h_h1_cr
    have l3 := advance_line_of_peekIx c.advance.advance h2 h_lt_h2 h_peek_h2 h_h2_nn h_h2_cr
    omega
  exact ⟨_, _, rfl, hcorr_h2, h_line⟩

/-! ### §3.4  Core loop lemma

`collectDoubleQuotedLoopIx` succeeds on `escapeString content ++ "\"" ++ rest`,
leaving the cursor at `rest`. Twin of legacy
`collectDoubleQuotedLoop_escapeString_succeeds` (lines 577–840).

The legacy `isNbJsonBool` check has no indexed counterpart — the
indexed loop accepts any non-`"`/non-`\\`/non-linebreak character — so
this proof is somewhat simpler than legacy in the passthrough branch. -/

/-- The core loop lemma: `collectDoubleQuotedLoopIx` succeeds on
    `escapeString content ++ "\"" ++ rest`, returning `acc ++ content`
    plus the post-quote cursor at `rest`. -/
theorem collectDoubleQuotedLoopIx_escapeString_succeeds {input : String}
    (c : IxCursor input) (content_rest : List Char) (rest : List Char)
    (acc : String) (fuel : Nat)
    (hcorr : CursorSurfCorrIx c
      ⟨(escapeString (String.ofList content_rest)).toList ++ ['"'] ++ rest, c.pos.col⟩)
    (h_fuel : fuel ≥ content_rest.length + 1) :
    ∃ c',
      collectDoubleQuotedLoopIx c acc fuel =
        some (acc ++ String.ofList content_rest, c') ∧
      CursorSurfCorrIx c' ⟨rest, c'.pos.col⟩ ∧
      c'.pos.col > 0 ∧
      c'.pos.line = c.pos.line := by
  induction content_rest generalizing c acc fuel with
  | nil =>
    -- Closing quote: escapeString "" = "" → chars start with '"'.
    have h_ofnil : (String.ofList ([] : List Char)) = "" := rfl
    rw [h_ofnil, escapeString_nil] at hcorr
    simp only [String.toList_empty, List.nil_append] at hcorr
    have ⟨h_peek, h_lt⟩ := peek_of_chars_consIx c '"' rest _ hcorr
    match fuel, h_fuel with
    | fuel' + 1, _ =>
      unfold collectDoubleQuotedLoopIx
      rw [h_peek]
      have h_dq : isDoubleQuoteBool '"' = true := by decide
      simp only [h_dq, if_true]
      rw [show acc ++ String.ofList [] = acc from append_ofList_nil acc]
      refine ⟨c.advance, rfl, ?_, ?_, ?_⟩
      · have hcorr_adv := advance_non_newline_corrIx c '"' rest hcorr h_lt
          (by decide) (by decide)
        have h_col_adv : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_adv.col_eq
        rw [h_col_adv] at hcorr_adv; exact hcorr_adv
      · have hcorr_adv := advance_non_newline_corrIx c '"' rest hcorr h_lt
          (by decide) (by decide)
        have h_col_adv : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_adv.col_eq
        omega
      · exact advance_line_of_peekIx c '"' h_lt h_peek (by decide) (by decide)
  | cons ch cs ih =>
    -- escapeChar ch ++ escapeString cs ++ "\"" ++ rest
    rw [escapeString_cons, String.toList_append] at hcorr
    by_cases h_esc : isEscapedChar ch
    · by_cases h_tag_some : (escapeTag ch).isSome
      · -- NAMED ESCAPE: escapeChar ch = "\\" ++ tag.toString.
        obtain ⟨tag, h_tag⟩ := Option.isSome_iff_exists.mp h_tag_some
        rw [escapeChar_named_toList ch tag h_tag] at hcorr
        simp only [List.cons_append, List.nil_append] at hcorr
        have ⟨h_peek_bs, h_lt_bs⟩ := peek_of_chars_consIx c '\\' _ _ hcorr
        match fuel, h_fuel with
        | fuel' + 1, h_f =>
          unfold collectDoubleQuotedLoopIx
          rw [h_peek_bs]
          have h_dq : isDoubleQuoteBool '\\' = false := by decide
          have h_es : isEscapeBool '\\' = true := by decide
          simp only [h_dq, h_es, Bool.false_eq_true, if_false, if_true]
          -- After backslash: peek tag.
          have hcorr_bs := advance_non_newline_corrIx c '\\' _ hcorr h_lt_bs
            (by decide) (by decide)
          have ⟨h_peek_tag, h_lt_tag⟩ := peek_of_chars_consIx c.advance tag _ _ hcorr_bs
          rw [h_peek_tag]
          -- Confirm tag is not a linebreak (so we fall through to processEscapeIx).
          have h_tag_nlb := escapeTag_not_linebreak ch tag h_tag
          simp only [h_tag_nlb, Bool.false_eq_true, if_false]
          -- processEscapeIx succeeds with origChar = ch.
          have h_proc := processEscapeIx_named_content c.advance ch tag h_tag h_peek_tag
          rw [h_proc]
          -- Column / cursor wiring for IH.
          have h_col_bs : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_bs.col_eq
          rw [h_col_bs] at hcorr_bs
          have hcorr_tag := advance_non_newline_corrIx c.advance tag _ hcorr_bs h_lt_tag
            (fun h => by subst h; exact absurd h_tag_nlb (by decide))
            (fun h => by subst h; exact absurd h_tag_nlb (by decide))
          have h_col_tag : (c.advance.pos.col + 1 : Nat) =
              c.advance.advance.pos.col := hcorr_tag.col_eq
          rw [h_col_tag] at hcorr_tag
          rw [show acc ++ String.ofList (ch :: cs) = acc.push ch ++ String.ofList cs
              from (push_append_ofList_eq acc ch cs).symm]
          obtain ⟨c', h_loop, hcorr_c', h_col_c', h_line_c'⟩ :=
            ih c.advance.advance (acc.push ch) fuel'
            hcorr_tag (by simp [List.length_cons] at h_f; omega)
          refine ⟨c', h_loop, hcorr_c', h_col_c', ?_⟩
          have l_bs := advance_line_of_peekIx c '\\' h_lt_bs h_peek_bs (by decide) (by decide)
          have l_tag := advance_line_of_peekIx c.advance tag h_lt_tag h_peek_tag
            (fun h => by subst h; exact absurd h_tag_nlb (by decide))
            (fun h => by subst h; exact absurd h_tag_nlb (by decide))
          omega
      · -- HEX ESCAPE: escapeChar ch = "\\xHH".
        have h_tag_none : escapeTag ch = none := by
          cases h : escapeTag ch
          · rfl
          · exact absurd (show (escapeTag ch).isSome = true by rw [h]; rfl) h_tag_some
        have h_lt_c : ch.val.toNat < 0x20 := by
          have h_lt128 : ch.val.toNat < 128 := by
            cases Nat.lt_or_ge ch.val.toNat 128 with
            | inl hl => exact hl
            | inr hge =>
              exfalso
              have h_not_esc : isEscapedChar ch = false := by
                unfold isEscapedChar; split
                all_goals (simp_all (config := { decide := true }) <;> omega)
              simp [h_not_esc] at h_esc
          have h_classify : ∀ n : Fin 128,
              isEscapedChar (Char.ofNat n.val) = true →
              escapeTag (Char.ofNat n.val) = none →
              n.val < 0x20 := by native_decide
          exact h_classify ⟨ch.toNat, by unfold Char.toNat; omega⟩
            (by rwa [Char.ofNat_toNat]) (by rwa [Char.ofNat_toNat])
        obtain ⟨d1, d2, h_ec_list, h_d1_nn, h_d1_cr, h_d2_nn, h_d2_cr,
            h_d1_hex, h_d2_hex, h_d1_lt128, h_d2_lt128⟩ :=
          escapeChar_hex_structure ch h_lt_c h_tag_none
        rw [h_ec_list] at hcorr
        simp only [List.cons_append, List.nil_append] at hcorr
        have ⟨h_peek_bs, h_lt_bs⟩ := peek_of_chars_consIx c '\\' _ _ hcorr
        match fuel, h_fuel with
        | fuel' + 1, h_f =>
          unfold collectDoubleQuotedLoopIx
          rw [h_peek_bs]
          have h_dq : isDoubleQuoteBool '\\' = false := by decide
          have h_es : isEscapeBool '\\' = true := by decide
          simp only [h_dq, h_es, Bool.false_eq_true, if_false, if_true]
          have hcorr_bs := advance_non_newline_corrIx c '\\' _ hcorr h_lt_bs
            (by decide) (by decide)
          have ⟨h_peek_x, h_lt_x_in⟩ := peek_of_chars_consIx c.advance 'x' _ _ hcorr_bs
          rw [h_peek_x]
          have h_x_nlb : isLineBreakBool 'x' = false := by decide
          simp only [h_x_nlb, Bool.false_eq_true, if_false]
          have h_col_bs : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_bs.col_eq
          rw [h_col_bs] at hcorr_bs
          obtain ⟨decoded, c_after, h_proc, hcorr_after, h_line_proc⟩ :=
            processEscapeIx_hex_ok c.advance d1 d2 _ _ hcorr_bs
              h_d1_nn h_d1_cr h_d2_nn h_d2_cr h_d1_hex h_d2_hex h_d1_lt128 h_d2_lt128
          -- Show decoded = ch via hex roundtrip.
          have h_decoded_eq : decoded = ch := by
            have h_struct : ∀ n : Fin 32, escapeTag (Char.ofNat n.val) = none →
                (escapeChar (Char.ofNat n.val)).toList =
                  ['\\', 'x', hexNibble (n.val / 16), hexNibble (n.val % 16)] := by
              native_decide
            have h_spec := h_struct ⟨ch.toNat, by unfold Char.toNat; omega⟩
              (by rwa [Char.ofNat_toNat])
            rw [Char.ofNat_toNat] at h_spec
            have h_comb := h_ec_list.symm.trans h_spec
            simp only [List.cons.injEq, and_true] at h_comb
            have h_d1_eq : d1 = hexNibble (ch.val.toNat / 16) := h_comb.2.2.1
            have h_d2_eq : d2 = hexNibble (ch.val.toNat % 16) := h_comb.2.2.2
            -- Unfold processEscapeIx + parseHexEscapeIx to expose the foldl.
            have h_d1_hexIx : isHexDigitBool d1 = true := by
              rw [← scannerHexCheck_eq_isHexDigitBool d1 h_d1_lt128]; exact h_d1_hex
            have h_d2_hexIx : isHexDigitBool d2 = true := by
              rw [← scannerHexCheck_eq_isHexDigitBool d2 h_d2_lt128]; exact h_d2_hex
            -- Get the post-advance peeks for d1, d2 (mirrors hex_ok internals).
            have hcorr_x_raw := advance_non_newline_corrIx c.advance 'x' _ hcorr_bs h_lt_x_in
              (by decide) (by decide)
            have hcorr_x' : CursorSurfCorrIx c.advance.advance
                ⟨d1 :: d2 :: (escapeString (String.ofList cs)).toList ++ ['"'] ++ rest,
                 c.advance.advance.pos.col⟩ := by
              rw [← hcorr_x_raw.col_eq]; exact hcorr_x_raw
            have ⟨h_peek_d1', h_lt_d1'⟩ :=
              peek_of_chars_consIx c.advance.advance d1 _ _ hcorr_x'
            have hcorr_d1_raw := advance_non_newline_corrIx c.advance.advance d1 _
              hcorr_x' h_lt_d1' h_d1_nn h_d1_cr
            have hcorr_d1' : CursorSurfCorrIx c.advance.advance.advance
                ⟨d2 :: (escapeString (String.ofList cs)).toList ++ ['"'] ++ rest,
                 c.advance.advance.advance.pos.col⟩ := by
              rw [← hcorr_d1_raw.col_eq]; exact hcorr_d1_raw
            have ⟨h_peek_d2', _⟩ :=
              peek_of_chars_consIx c.advance.advance.advance d2 _ _ hcorr_d1'
            -- Compute collectHexDigitsLoopIx and the value.
            unfold processEscapeIx at h_proc
            rw [h_peek_x] at h_proc
            dsimp only [] at h_proc
            have h_simple_x : simpleEscapeChar 'x' = none := by decide
            have h_8bit_x : isNsEsc8BitBool 'x' = true := by decide
            rw [h_simple_x] at h_proc
            simp only [h_8bit_x, if_true] at h_proc
            unfold parseHexEscapeIx at h_proc
            have h_coll : collectHexDigitsLoopIx c.advance.advance "" 2 =
                (("".push d1).push d2, c.advance.advance.advance.advance) := by
              unfold collectHexDigitsLoopIx; dsimp only []
              rw [h_peek_d1']; dsimp only []
              simp only [h_d1_hexIx, if_true]
              unfold collectHexDigitsLoopIx; dsimp only []
              rw [h_peek_d2']; dsimp only []
              simp only [h_d2_hexIx, if_true]
              unfold collectHexDigitsLoopIx; dsimp only []
            simp only [h_coll] at h_proc
            have h_len : (("".push d1).push d2).length = 2 := by
              simp [String.length, String.toList_push]
            simp only [h_len, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte] at h_proc
            have h_vlt := hex_two_foldl_boundIx ⟨d1.toNat, h_d1_lt128⟩ ⟨d2.toNat, h_d2_lt128⟩
              (by rw [Char.ofNat_toNat]; exact h_d1_hexIx)
              (by rw [Char.ofNat_toNat]; exact h_d2_hexIx)
            rw [Char.ofNat_toNat, Char.ofNat_toNat] at h_vlt
            simp only [h_vlt, ↓reduceIte] at h_proc
            have h_pair := Option.some.inj h_proc
            have h_fst := congrArg Prod.fst h_pair; dsimp only [] at h_fst
            rw [← h_fst, h_d1_eq, h_d2_eq]
            have h_rt := hex_foldl_roundtripIx ⟨ch.val.toNat, by omega⟩
            simp only at h_rt; rw [h_rt]
            exact (Char.ofNat_toNat ch).symm ▸ rfl
          rw [h_decoded_eq] at h_proc
          rw [h_proc]
          -- Recurse on cs (column wiring for the IH).
          have h_col_after : (c.advance.pos.col + 3 : Nat) =
              c_after.pos.col := hcorr_after.col_eq
          rw [h_col_after] at hcorr_after
          rw [show acc ++ String.ofList (ch :: cs) = acc.push ch ++ String.ofList cs
              from (push_append_ofList_eq acc ch cs).symm]
          obtain ⟨c', h_loop, hcorr_c', h_col_c', h_line_c'⟩ :=
            ih c_after (acc.push ch) fuel' hcorr_after
            (by simp [List.length_cons] at h_f; omega)
          refine ⟨c', h_loop, hcorr_c', h_col_c', ?_⟩
          have l_bs := advance_line_of_peekIx c '\\' h_lt_bs h_peek_bs (by decide) (by decide)
          omega
    · -- PASSTHROUGH: escapeChar ch = ch.toString.
      have h_ef : isEscapedChar ch = false := by
        cases hv : isEscapedChar ch
        · rfl
        · exact absurd hv h_esc
      rw [escapeChar_passthrough_toList ch h_ef] at hcorr
      simp only [List.cons_append, List.nil_append] at hcorr
      have ⟨h_peek_c, h_lt_c⟩ := peek_of_chars_consIx c ch _ _ hcorr
      match fuel, h_fuel with
      | fuel' + 1, h_f =>
        unfold collectDoubleQuotedLoopIx
        rw [h_peek_c]
        -- ch is not '"', '\\', or a linebreak (all of those are escaped).
        have h_ne_quote : ch ≠ '"' := fun h => by subst h; exact absurd h_ef (by decide)
        have h_ne_bs : ch ≠ '\\' := fun h => by subst h; exact absurd h_ef (by decide)
        have h_ne_nl : ch ≠ '\n' := fun h => by subst h; exact absurd h_ef (by decide)
        have h_ne_cr : ch ≠ '\r' := fun h => by subst h; exact absurd h_ef (by decide)
        have h_dq : isDoubleQuoteBool ch = false := by
          show (ch == '"') = false; exact beq_eq_false_iff_ne.mpr h_ne_quote
        have h_es : isEscapeBool ch = false := by
          show (ch == '\\') = false; exact beq_eq_false_iff_ne.mpr h_ne_bs
        have h_nlb : isLineBreakBool ch = false := by
          show (ch == '\n' || ch == '\r') = false
          rw [Bool.or_eq_false_iff]
          exact ⟨beq_eq_false_iff_ne.mpr h_ne_nl, beq_eq_false_iff_ne.mpr h_ne_cr⟩
        simp only [h_dq, h_es, h_nlb, Bool.false_eq_true, if_false]
        -- Advance and recurse.
        have hcorr_c := advance_non_newline_corrIx c ch _ hcorr h_lt_c h_ne_nl h_ne_cr
        have h_col_c : (c.pos.col + 1 : Nat) = c.advance.pos.col := hcorr_c.col_eq
        rw [h_col_c] at hcorr_c
        rw [show acc ++ String.ofList (ch :: cs) = acc.push ch ++ String.ofList cs
            from (push_append_ofList_eq acc ch cs).symm]
        obtain ⟨c', h_loop, hcorr_c', h_col_c', h_line_c'⟩ :=
          ih c.advance (acc.push ch) fuel' hcorr_c
          (by simp [List.length_cons] at h_f; omega)
        refine ⟨c', h_loop, hcorr_c', h_col_c', ?_⟩
        have l_c := advance_line_of_peekIx c ch h_lt_c h_peek_c h_ne_nl h_ne_cr
        omega

end L4YAML.Proofs.Indexed.EmitterScannability.Basic
