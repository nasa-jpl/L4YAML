/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Emitter
import Lean4Yaml.Scanner
import Lean4Yaml.Grammar
import Lean4Yaml.TokenParser
import Lean4Yaml.CharPredicates
import Lean4Yaml.Proofs.ScannerEmitBridge
import Lean4Yaml.Proofs.RoundTrip
import Lean4Yaml.Proofs.CouplingBridge
import Lean4Yaml.Proofs.ScalarCoupling

/-!
# Emitter Scannability (Phase E, Steps 1–2)

Step 1 — Proof that the canonical emitter's output is accepted by the scanner:

```
∀ v, Grammable v false → ∃ tokens, Scanner.scanFiltered (emit v) = .ok tokens
```

Step 2 — Composition with the parser to prove the full pipeline succeeds:

```
∀ v, Grammable v false → ∃ docs, parseYamlRaw (emit v) = .ok docs
```

## Architecture

The canonical emitter produces a strict subset of YAML:
- All scalars are double-quoted (`"..."`)
- All sequences are flow-style (`[...]`)
- All mappings are flow-style (`{...}`)
- No block constructs, no plain scalars, no document markers

### Proof Strategy

Rather than reasoning about the scanner's state machine directly,
we prove that `parseYamlRaw (emit v) = .ok docs` for all grammable `v`.
This is equivalent to proving both scanner acceptance and parser success.

The proof proceeds by structural induction on `YamlValue`:

**§1** — Escape character validity: each `escapeChar c` produces output that
         `collectDoubleQuotedLoop` accepts.
**§2** — Emitter output properties: non-emptiness and structural facts.
**§3** — Scanner acceptance (Step 1): `scan_accepts_emitScalar` and
         `emit_produces_valid_yaml`.
**§4** — Full pipeline composition (Step 2): parse acceptance,
         single-document guarantee, and grammability preservation.

## Zero Axioms

Target: all theorems machine-checked with 0 sorry, 0 axiom, 0 admit.
-/

namespace Lean4Yaml.Proofs.EmitterScannability

open Lean4Yaml
open Lean4Yaml.Emit
open Lean4Yaml.Proofs.RoundTrip
open Lean4Yaml.Scanner
open Lean4Yaml.Grammar
open Lean4Yaml.TokenParser
open Lean4Yaml.CharPredicates
open Lean4Yaml.Proofs.CouplingBridge
open Lean4Yaml.Proofs.ScalarCoupling

/-! ## §1  Escape Character Properties

The emitter's `escapeChar` function produces output that is valid for
the scanner's `collectDoubleQuotedLoop`. We need two properties:

1. Characters that are escaped (e.g., `\n`, `\\`, `\"`) produce valid
   two-character escape sequences recognized by `processEscape`.
2. Characters that pass through unchanged are `nb-json` characters
   that are neither `"` nor `\`.
-/

/-- An unescaped character (one that `escapeChar` passes through as-is)
    is a valid `nb-json` character that is neither `"` nor `\`. -/
theorem escapeChar_passthrough_is_valid (c : Char)
    (h_not_escaped : escapeChar c = c.toString) :
    isNbJsonBool c = true ∧ c ≠ '"' ∧ c ≠ '\\' := by
  unfold escapeChar at h_not_escaped
  split at h_not_escaped
  -- 11 named arms: each maps to a concrete multi-char string ≠ c.toString
  all_goals (first | exact absurd h_not_escaped (by native_decide) | skip)
  -- Default arm: if c.val.toNat < 0x20 then escapeHex2 c else c.toString
  split at h_not_escaped
  · -- escapeHex2 c = c.toString: impossible for c.val.toNat < 0x20
    rename_i h_lt
    exfalso
    have h_bounded : ∀ n : Fin 32,
        escapeHex2 (Char.ofNat n.val) ≠ (Char.ofNat n.val).toString := by native_decide
    have h_ne := h_bounded ⟨c.toNat, by simp [Char.toNat]; omega⟩
    rw [Char.ofNat_toNat] at h_ne
    exact h_ne h_not_escaped
  · -- passthrough: c.val.toNat ≥ 0x20
    rename_i h_ge; simp only [Nat.not_lt] at h_ge
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
    This is needed because `collectDoubleQuotedLoop` checks `isNbJsonBool`
    on each character it encounters. -/
theorem escapeChar_output_nbJson (c : Char) :
    ∀ ch ∈ (escapeChar c).toList, isNbJsonBool ch = true := by
  by_cases h_val : c.val.toNat < 128
  · -- ASCII range: native_decide over Fin 128 covers all cases
    have h_bounded : ∀ n : Fin 128, ∀ ch ∈ (escapeChar (Char.ofNat n.val)).toList,
        isNbJsonBool ch = true := by native_decide
    have h_spec := h_bounded ⟨c.toNat, by simp [Char.toNat]; omega⟩
    rw [Char.ofNat_toNat] at h_spec
    exact h_spec
  · -- Non-ASCII (c.val.toNat ≥ 128): escapeChar c = c.toString (passthrough)
    simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    intro ch h_mem
    simp only [Char.toString, String.toList_singleton, List.mem_singleton] at h_mem
    rw [h_mem]
    exact (escapeChar_passthrough_is_valid c (escapeChar_identity c h_not_esc)).1

/-! ## §2  Emitter Output Properties

Properties of the strings produced by `emit` that are needed for
scanner acceptance.
-/

/-- The output of `emit v` is non-empty for any value. -/
theorem emit_nonempty (v : YamlValue) : (emit v).length > 0 := by
  have : ("\"" : String).length = 1 := by native_decide
  have : ("[" : String).length = 1 := by native_decide
  have : ("]" : String).length = 1 := by native_decide
  have : ("{" : String).length = 1 := by native_decide
  have : ("}" : String).length = 1 := by native_decide
  cases v <;> simp_all [emit, emitScalar, String.length_append] <;> omega

/-! ### §2.1  `escapeString` Decomposition

Helper lemmas for inductive reasoning about `escapeString` output.
The key fact: `escapeString` is a monoid homomorphism that concatenates
`escapeChar c` for each character `c` in the input.
-/

-- Bridge: `String.foldl` in Lean 4.29 goes through `Std.Iter.fold` on
-- `Slice.chars`, NOT `List.foldl`.  We prove the equivalence via
-- `Iter.foldl_toList` and `String.toList_chars` (both `@[simp]`).
theorem string_foldl_toList {α : Type _}
    (f : α → Char → α) (init : α) (s : String) :
    s.foldl f init = s.toList.foldl f init := by
  simp [String.foldl, String.Slice.foldl, ← Std.Iter.foldl_toList]

/-- The accumulator-shift property for `escapeString`'s foldl: prepending
    to the accumulator is the same as prepending to the result. -/
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

/-- `escapeString` distributes over cons: the output is the escape of the
    first character followed by the escape of the rest. -/
theorem escapeString_cons (c : Char) (cs : List Char) :
    escapeString (String.ofList (c :: cs)) =
    escapeChar c ++ escapeString (String.ofList cs) := by
  unfold escapeString
  rw [string_foldl_toList, string_foldl_toList]
  simp only [String.toList_ofList, List.foldl_cons, String.empty_append]
  rw [escapeString_foldl_shift cs (escapeChar c)]

/-! ### §2.2  First-Character Properties

The first character of `escapeChar c` output determines which branch
of `collectDoubleQuotedLoop` processes it.
-/

/-- The first character of `escapeChar c` is never `"`.
    This ensures the scanner never mistakes escape output for a closing quote. -/
theorem escapeChar_head_not_quote (c : Char) :
    (escapeChar c).toList.head? ≠ some '"' := by
  by_cases h_val : c.val.toNat < 128
  · have : ∀ n : Fin 128,
        (escapeChar (Char.ofNat n.val)).toList.head? ≠ some '"' := by native_decide
    have := this ⟨c.toNat, by simp [Char.toNat]; omega⟩
    rwa [Char.ofNat_toNat] at this
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    simp only [Char.toString, String.toList_singleton, List.head?_cons]
    intro heq; injection heq with heq; subst heq
    exact absurd h_val (by native_decide)

/-- The first character of `escapeChar c` is never a line break.
    This ensures `collectDoubleQuotedLoop` never takes the newline-fold branch. -/
theorem escapeChar_head_not_linebreak (c : Char) :
    ∀ ch, (escapeChar c).toList.head? = some ch → isLineBreakBool ch = false := by
  by_cases h_val : c.val.toNat < 128
  · have : ∀ n : Fin 128, ∀ ch,
        (escapeChar (Char.ofNat n.val)).toList.head? = some ch →
        isLineBreakBool ch = false := by native_decide
    have := this ⟨c.toNat, by simp [Char.toNat]; omega⟩
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

/-- No character of `escapeChar c` is a line break.
    Stronger than `escapeChar_head_not_linebreak` — covers ALL output chars. -/
theorem escapeChar_output_no_linebreak (c : Char) :
    ∀ ch ∈ (escapeChar c).toList, isLineBreakBool ch = false := by
  by_cases h_val : c.val.toNat < 128
  · have h_bounded : ∀ n : Fin 128, ∀ ch ∈ (escapeChar (Char.ofNat n.val)).toList,
        isLineBreakBool ch = false := by native_decide
    have h_spec := h_bounded ⟨c.toNat, by simp [Char.toNat]; omega⟩
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
    have := this ⟨c.toNat, by simp [Char.toNat]; omega⟩
    rwa [Char.ofNat_toNat] at this
  · simp only [Nat.not_lt] at h_val
    have h_not_esc : isEscapedChar c = false := by
      unfold isEscapedChar; split <;> simp_all <;> omega
    rw [escapeChar_identity c h_not_esc]
    simp [Char.toString]

/-! ### §2.3  `escapeString` Character Properties

Since `escapeString s = s.foldl (fun acc c => acc ++ escapeChar c) ""`,
every character of the output is a character of some `escapeChar c`.
We lift per-character properties from `escapeChar` to `escapeString`.
-/

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

/-- A character is in `escapeString content` iff it is in some `escapeChar c`
    for `c` in `content`. -/
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

/-! ### §2.4  `collectDoubleQuotedLoop` Acceptance of Escaped Strings

The core lemma: `collectDoubleQuotedLoop` succeeds on
`escapeString content ++ "\""` for any content string. This is the
key step in proving scanner acceptance of canonical emitter output.

The proof proceeds by induction on `content.toList`:
- **Base case**: `escapeString "" = ""`, remaining is `['"']` → close quote.
- **Inductive step**: `escapeString (c :: cs) = escapeChar c ++ escapeString cs`.
  Three sub-cases for `escapeChar c`:
  - **Passthrough** (`escapeChar c = c.toString`): regular char branch, 1 fuel unit.
  - **Named escape** (`escapeTag c = some tag`): escape branch, `processEscape`
    consumes tag, 1 fuel unit.
  - **Hex escape** (`c.val.toNat < 0x20`, no named tag): escape branch,
    `processEscape` consumes `\xHH`, 1 fuel unit.
-/

/-- Derive `peek?` from `ScannerSurfCorr` when the surface position starts
    with a known character. Column can be arbitrary. -/
theorem peek_of_chars_cons (sc : ScannerState) (c : Char) (rest : List Char)
    (col : Nat) (hcorr : ScannerSurfCorr sc ⟨c :: rest, col⟩) :
    sc.peek? = some c ∧ sc.offset < sc.inputEnd := by
  by_cases h_lt : sc.offset < sc.inputEnd
  · obtain ⟨c', _, h_eq, h_peek⟩ := peek_corr sc ⟨c :: rest, col⟩ hcorr h_lt
    exact ⟨(List.cons.inj h_eq).1 ▸ h_peek, h_lt⟩
  · exact absurd (eof_corr sc _ hcorr h_lt) (List.cons_ne_nil c rest)

/-- `processEscape` succeeds when peeking at a named escape tag
    (one of `escapeTag`'s output characters). Returns `(decoded, sc.advance)`. -/
theorem processEscape_named_ok (sc : ScannerState) (c tag : Char)
    (h_tag : escapeTag c = some tag) (h_peek : sc.peek? = some tag) :
    ∃ decoded, processEscape sc = .ok (decoded, sc.advance) := by
  unfold processEscape; rw [h_peek]; dsimp only []
  -- Split on inner match over tag
  split
  -- All .ok arms: immediate
  all_goals (first | exact ⟨_, rfl⟩ | skip)
  -- Remaining arms (x/u/U/wildcard): tag can't be these per escapeTag
  all_goals exfalso
  all_goals (unfold escapeTag at h_tag; split at h_tag
    <;> simp_all <;> (try subst_vars) <;> contradiction)

/-- Named escape tags are never line breaks — needed to distinguish
    escape from escaped-newline in the scanner. -/
theorem escapeTag_not_linebreak (c tag : Char)
    (h_tag : escapeTag c = some tag) : isLineBreakBool tag = false := by
  unfold escapeTag at h_tag; split at h_tag
  all_goals first | exact Option.noConfusion h_tag | skip
  all_goals (injection h_tag; try subst_vars; try native_decide)

/-- `escapeChar` for passthrough characters produces a single-element
    char list equal to `[c]`. -/
theorem escapeChar_passthrough_toList (c : Char) (h : isEscapedChar c = false) :
    (escapeChar c).toList = [c] := by
  rw [escapeChar_identity c h]; simp [Char.toString]

/-- `escapeChar` for named escapes produces exactly `['\\', tag]`. -/
theorem escapeChar_named_toList (c tag : Char) (h : escapeTag c = some tag) :
    (escapeChar c).toList = ['\\', tag] := by
  have ⟨h_eq, _⟩ := escapeTag_roundtrip c tag h
  rw [h_eq]; simp [Char.toString]

/-- Scanner's hex digit check, matching `collectHexDigitsLoop`'s condition. -/
def scannerHexCheck (c : Char) : Bool :=
  c.isDigit || (c >= 'a' && c <= 'f') || (c >= 'A' && c <= 'F')

theorem hexNibble_is_hex : ∀ n : Fin 16, scannerHexCheck (hexNibble n.val) = true := by
  native_decide

theorem hexNibble_lt128 : ∀ n : Fin 16, (hexNibble n.val).toNat < 128 := by
  native_decide

/-- For any two hex chars (each with toNat < 128 and scannerHexCheck = true),
    the 2-digit hex foldl value is < 0x110000. -/
theorem hex_two_foldl_bound : ∀ (n1 n2 : Fin 128),
    scannerHexCheck (Char.ofNat n1.val) = true →
    scannerHexCheck (Char.ofNat n2.val) = true →
    (("".push (Char.ofNat n1.val)).push (Char.ofNat n2.val)).foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0 < 0x110000 := by native_decide

/-- `escapeChar` output for hex-escaped characters (C0 controls with no named tag)
    has the form `['\\', 'x', h1, h2]` where h1, h2 are hex digits with toNat < 128. -/
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
  have h_spec := h_struct ⟨c.toNat, by simp [Char.toNat]; omega⟩ (by rwa [Char.ofNat_toNat])
  rw [Char.ofNat_toNat] at h_spec
  exact ⟨_, _, h_spec,
    h_hex_nn ⟨c.toNat / 16, by simp [Char.toNat]; omega⟩,
    h_hex_cr ⟨c.toNat / 16, by simp [Char.toNat]; omega⟩,
    h_hex_nn ⟨c.toNat % 16, by simp [Char.toNat]; omega⟩,
    h_hex_cr ⟨c.toNat % 16, by simp [Char.toNat]; omega⟩,
    hexNibble_is_hex ⟨c.toNat / 16, by simp [Char.toNat]; omega⟩,
    hexNibble_is_hex ⟨c.toNat % 16, by simp [Char.toNat]; omega⟩,
    hexNibble_lt128 ⟨c.toNat / 16, by simp [Char.toNat]; omega⟩,
    hexNibble_lt128 ⟨c.toNat % 16, by simp [Char.toNat]; omega⟩⟩

/-- `processEscape` succeeds on hex escape sequences produced by `escapeHex2`.
    When the scanner is positioned at `'x' :: h1 :: h2 :: rest`, processEscape
    reads `x`, then `parseHexEscape` consumes `h1 h2`. -/
theorem processEscape_hex_ok (sc : ScannerState) (h1 h2 : Char)
    (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr sc ⟨'x' :: h1 :: h2 :: rest, col⟩)
    (h_h1_nn : h1 ≠ '\n') (h_h1_cr : h1 ≠ '\r')
    (h_h2_nn : h2 ≠ '\n') (h_h2_cr : h2 ≠ '\r')
    (h_h1_hex : scannerHexCheck h1 = true) (h_h2_hex : scannerHexCheck h2 = true)
    (h_h1_lt128 : h1.toNat < 128) (h_h2_lt128 : h2.toNat < 128) :
    ∃ decoded s',
      processEscape sc = .ok (decoded, s') ∧
      ScannerSurfCorr s' ⟨rest, col + 3⟩ ∧
      s'.inputEnd = sc.inputEnd := by
  -- Normalize col to sc.col
  have h_col_eq : col = sc.col := hcorr.col_eq
  subst h_col_eq
  -- Step 1: processEscape peeks 'x', matches → parseHexEscape sc.advance 2
  have ⟨h_peek_x, h_lt_x⟩ := peek_of_chars_cons sc 'x' (h1 :: h2 :: rest) sc.col hcorr
  -- Step 2: advance past 'x'
  have hcorr_x := advance_non_newline_corr sc 'x' (h1 :: h2 :: rest) hcorr h_lt_x
    (by decide) (by decide)
  -- hcorr_x : ScannerSurfCorr sc.advance ⟨h1 :: h2 :: rest, sc.col + 1⟩
  have h_col_x : (sc.col + 1 : Nat) = sc.advance.col := hcorr_x.col_eq
  rw [h_col_x] at hcorr_x
  -- Step 3: advance past h1
  have ⟨h_peek_h1, h_lt_h1⟩ := peek_of_chars_cons sc.advance h1 (h2 :: rest) sc.advance.col hcorr_x
  have hcorr_h1 := advance_non_newline_corr sc.advance h1 (h2 :: rest) hcorr_x h_lt_h1
    h_h1_nn h_h1_cr
  -- hcorr_h1 : ScannerSurfCorr sc.advance.advance ⟨h2 :: rest, sc.advance.col + 1⟩
  have h_col_h1 : (sc.advance.col + 1 : Nat) = sc.advance.advance.col := hcorr_h1.col_eq
  rw [h_col_h1] at hcorr_h1
  -- Step 4: advance past h2
  have ⟨h_peek_h2, h_lt_h2⟩ := peek_of_chars_cons sc.advance.advance h2 rest sc.advance.advance.col hcorr_h1
  have hcorr_h2 := advance_non_newline_corr sc.advance.advance h2 rest hcorr_h1 h_lt_h2
    h_h2_nn h_h2_cr
  -- hcorr_h2 : ScannerSurfCorr sc.advance.advance.advance ⟨rest, sc.advance.advance.col + 1⟩
  -- Step 5: show collectHexDigitsLoop produces 2-char hex string
  unfold scannerHexCheck at h_h1_hex h_h2_hex
  have h_collect : collectHexDigitsLoop sc.advance "" 2 =
      (("".push h1).push h2, sc.advance.advance.advance) := by
    unfold collectHexDigitsLoop; dsimp only []; rw [h_peek_h1]; dsimp only []
    simp only [h_h1_hex, if_true]
    unfold collectHexDigitsLoop; dsimp only []; rw [h_peek_h2]; dsimp only []
    simp only [h_h2_hex, if_true]
    unfold collectHexDigitsLoop; dsimp only []
  -- Step 6: show foldl value < 0x110000
  have h_val_lt := hex_two_foldl_bound ⟨h1.toNat, h_h1_lt128⟩ ⟨h2.toNat, h_h2_lt128⟩
    (by rwa [Char.ofNat_toNat]) (by rwa [Char.ofNat_toNat])
  rw [Char.ofNat_toNat, Char.ofNat_toNat] at h_val_lt
  -- Step 7: unfold processEscape and parseHexEscape, apply results
  unfold processEscape; rw [h_peek_x]; dsimp only []
  unfold parseHexEscape; simp only [h_collect]
  -- Reduce length check: ("".push h1).push h2 has length 2
  have h_len : (("".push h1).push h2).length = 2 := by
    simp [String.length, String.toList_push]
  simp only [h_len, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte]
  -- Reduce val < 0x110000 check
  simp only [h_val_lt, ↓reduceIte]
  -- Goal: ScannerSurfCorr sc.advance.advance.advance ⟨rest, sc.col + 3⟩
  -- hcorr_h2 has col = sc.advance.advance.col + 1
  -- Need: sc.advance.advance.col + 1 = sc.col + 3
  -- From h_col_x: sc.col + 1 = sc.advance.col
  -- From h_col_h1: sc.advance.col + 1 = sc.advance.advance.col
  -- So sc.advance.advance.col + 1 = sc.col + 3
  have h_col_final : sc.advance.advance.col + 1 = sc.col + 3 := by omega
  rw [h_col_final] at hcorr_h2
  exact ⟨_, _, rfl, hcorr_h2,
    by rw [advance_inputEnd, advance_inputEnd, advance_inputEnd]⟩

/-- The core loop lemma: `collectDoubleQuotedLoop` succeeds on
    `escapeString content ++ "\""` for any content string.

    By induction on the characters of `content`:
    - Base: closing `"` → loop terminates.
    - Passthrough char: regular char branch → recurse.
    - Named escape: `\tag` → processEscape → recurse.
    - Hex escape: `\xHH` → processEscape → recurse. -/
theorem collectDoubleQuotedLoop_escapeString_succeeds
    (sc : ScannerState) (content_rest : List Char)
    (acc : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (hcorr : ScannerSurfCorr sc
      ⟨(escapeString (String.ofList content_rest)).toList ++ ['"'], sc.col⟩)
    (h_fuel : fuel ≥ content_rest.length + 1) :
    ∃ result s',
      collectDoubleQuotedLoop sc acc fuel startPos inFlow currentIndent sc.inputEnd =
      .ok (result, s') := by
  induction content_rest generalizing sc acc fuel with
  | nil =>
    -- Remaining chars: escapeString "" ++ "\"" = "\""
    have h_ofnil : (String.ofList ([] : List Char)) = "" := rfl
    rw [h_ofnil, escapeString_nil] at hcorr
    simp only [String.toList_empty, List.nil_append] at hcorr
    have ⟨h_peek, _⟩ := peek_of_chars_cons sc '"' [] _ hcorr
    match fuel, h_fuel with
    | fuel' + 1, _ =>
      unfold collectDoubleQuotedLoop; rw [h_peek]; dsimp only []
      exact ⟨acc, sc.advance, rfl⟩
  | cons c cs ih =>
    -- Remaining chars: escapeChar c ++ escapeString cs ++ "\""
    rw [escapeString_cons, String.toList_append, List.append_assoc] at hcorr
    -- Case split: passthrough vs escape
    by_cases h_esc : isEscapedChar c
    · -- ESCAPE: escapeTag c = some tag (named) or c.val.toNat < 0x20 (hex)
      by_cases h_tag_some : (escapeTag c).isSome
      · -- NAMED ESCAPE: escapeChar c = "\\" ++ tag.toString
        obtain ⟨tag, h_tag⟩ := Option.isSome_iff_exists.mp h_tag_some
        rw [escapeChar_named_toList c tag h_tag] at hcorr
        simp only [List.cons_append] at hcorr
        -- Now: ScannerSurfCorr sc ⟨'\\' :: tag :: (escapeString cs).toList ++ ['"'], sc.col⟩
        have ⟨h_peek_bs, h_lt_bs⟩ := peek_of_chars_cons sc '\\' _ _ hcorr
        match fuel, h_fuel with
        | fuel' + 1, h_f =>
          unfold collectDoubleQuotedLoop; rw [h_peek_bs]; dsimp only []
          -- Scanner sees '\\' → escape branch, advance past '\\'
          have hcorr_bs := advance_non_newline_corr sc '\\' _ hcorr h_lt_bs
            (by decide) (by decide)
          -- hcorr_bs : ScannerSurfCorr sc.advance ⟨tag :: ... ++ ['"'], sc.col + 1⟩
          have ⟨h_peek_tag, h_lt_tag⟩ := peek_of_chars_cons sc.advance tag _ _ hcorr_bs
          rw [h_peek_tag]; dsimp only []
          -- Check: tag is not a linebreak
          have h_tag_nlb := escapeTag_not_linebreak c tag h_tag
          rw [h_tag_nlb, if_neg Bool.false_ne_true]
          -- processEscape succeeds with named tag
          obtain ⟨decoded, h_proc⟩ := processEscape_named_ok sc.advance c tag h_tag h_peek_tag
          simp only [bind, Except.bind, h_proc]
          -- Adjust column for chained advance
          have h_col_bs : (sc.col + 1 : Nat) = sc.advance.col := hcorr_bs.col_eq
          rw [h_col_bs] at hcorr_bs
          have hcorr_tag := advance_non_newline_corr sc.advance tag _ hcorr_bs h_lt_tag
            (fun h => by subst h; exact absurd h_tag_nlb (by decide))
            (fun h => by subst h; exact absurd h_tag_nlb (by decide))
          -- Adjust column for IH
          have h_col_tag : (sc.advance.col + 1 : Nat) = sc.advance.advance.col := hcorr_tag.col_eq
          rw [h_col_tag] at hcorr_tag
          -- Apply IH (bridge inputEnd: advance preserves it)
          rw [show sc.inputEnd = sc.advance.advance.inputEnd from
            by rw [advance_inputEnd, advance_inputEnd]]
          exact ih sc.advance.advance (acc.push decoded) fuel'
            hcorr_tag (by simp [List.length_cons] at h_f; omega)
      · -- HEX ESCAPE: escapeChar c = "\\xHH"
        have h_tag_none : escapeTag c = none := by
          cases h : escapeTag c
          · rfl
          · exact absurd (show (escapeTag c).isSome = true by rw [h]; rfl) h_tag_some
        have h_lt_c : c.val.toNat < 0x20 := by
          have h_lt128 : c.val.toNat < 128 := by
            cases Nat.lt_or_ge c.val.toNat 128 with
            | inl h => exact h
            | inr hge =>
              exfalso
              have : isEscapedChar c = false := by
                unfold isEscapedChar; split
                all_goals (simp_all (config := { decide := true }) <;> omega)
              simp [this] at h_esc
          have : ∀ n : Fin 128,
              isEscapedChar (Char.ofNat n.val) = true →
              escapeTag (Char.ofNat n.val) = none →
              n.val < 0x20 := by native_decide
          exact this ⟨c.toNat, by simp [Char.toNat]; omega⟩
            (by rwa [Char.ofNat_toNat]) (by rwa [Char.ofNat_toNat])
        obtain ⟨d1, d2, h_ec_list, h_d1_nn, h_d1_cr, h_d2_nn, h_d2_cr, h_d1_hex, h_d2_hex,
            h_d1_lt128, h_d2_lt128⟩ :=
          escapeChar_hex_structure c h_lt_c h_tag_none
        rw [h_ec_list] at hcorr
        simp only [List.cons_append] at hcorr
        have ⟨h_peek_bs, h_lt_bs⟩ := peek_of_chars_cons sc '\\' _ _ hcorr
        match fuel, h_fuel with
        | fuel' + 1, h_f =>
          unfold collectDoubleQuotedLoop; rw [h_peek_bs]; dsimp only []
          have hcorr_bs := advance_non_newline_corr sc '\\' _ hcorr h_lt_bs
            (by decide) (by decide)
          have ⟨h_peek_x, _⟩ := peek_of_chars_cons sc.advance 'x' _ _ hcorr_bs
          rw [h_peek_x]; dsimp only []
          rw [show isLineBreakBool 'x' = false from by decide, if_neg Bool.false_ne_true]
          -- processEscape handles 'x' → parseHexEscape
          have h_col_bs : (sc.col + 1 : Nat) = sc.advance.col := hcorr_bs.col_eq
          rw [h_col_bs] at hcorr_bs
          obtain ⟨decoded, s_after, h_proc, hcorr_after, h_ie_after⟩ :=
            processEscape_hex_ok sc.advance d1 d2 _ _ hcorr_bs
              h_d1_nn h_d1_cr h_d2_nn h_d2_cr h_d1_hex h_d2_hex h_d1_lt128 h_d2_lt128
          simp only [bind, Except.bind, h_proc]
          -- Column and inputEnd adjustment for IH
          have h_col_after : (sc.advance.col + 3 : Nat) = s_after.col := hcorr_after.col_eq
          rw [h_col_after] at hcorr_after
          rw [show sc.inputEnd = s_after.inputEnd from
            by rw [← advance_inputEnd sc]; exact h_ie_after.symm]
          exact ih s_after (acc.push decoded) fuel' hcorr_after
            (by simp [List.length_cons] at h_f; omega)
    · -- PASSTHROUGH: escapeChar c = c.toString
      -- h_esc here : ¬(isEscapedChar c = true) or isEscapedChar c = false
      have h_ef : isEscapedChar c = false := by
        cases hv : isEscapedChar c
        · rfl
        · exact absurd hv h_esc
      rw [escapeChar_passthrough_toList c h_ef] at hcorr
      simp only [List.singleton_append] at hcorr
      have ⟨h_peek_c, h_lt_c⟩ := peek_of_chars_cons sc c _ _ hcorr
      match fuel, h_fuel with
      | fuel' + 1, h_f =>
        unfold collectDoubleQuotedLoop; rw [h_peek_c]
        -- c must reach catch-all arm (not '"' or '\\', both escaped)
        split
        · simp at *
        · rename_i h; have := Option.some.inj h; subst this
          exact absurd h_ef (by decide)
        · rename_i h; have := Option.some.inj h; subst this
          exact absurd h_ef (by decide)
        · -- Catch-all: regular char c
          rename_i c' h_match; have := Option.some.inj h_match; subst this
          -- isLineBreakBool c = false (c ≠ '\n', c ≠ '\r')
          have h_ne_nl : c ≠ '\n' := fun h => by subst h; exact absurd h_ef (by decide)
          have h_ne_cr : c ≠ '\r' := fun h => by subst h; exact absurd h_ef (by decide)
          have h_nlb : isLineBreakBool c = false := by
            unfold isLineBreakBool; simp [beq_eq_false_iff_ne, h_ne_nl, h_ne_cr]
          rw [h_nlb, if_neg Bool.false_ne_true]
          -- isNbJsonBool c = true (c.val ≥ 0x20)
          have h_json : isNbJsonBool c = true := by
            have h_ascii : ∀ n : Fin 128, isEscapedChar (Char.ofNat n.val) = false →
                isNbJsonBool (Char.ofNat n.val) = true := by native_decide
            by_cases h128 : c.toNat < 128
            · have := h_ascii ⟨c.toNat, by simp [Char.toNat] at h128 ⊢; omega⟩
                (by rwa [Char.ofNat_toNat])
              rwa [Char.ofNat_toNat] at this
            · -- c.toNat ≥ 128: always nb-json valid
              have h128' : c.val.toNat ≥ 128 := by
                change ¬(c.val.toNat < 128) at h128; omega
              suffices isNbJsonProp c by simp [isNbJsonBool, this]
              unfold isNbJsonProp; right
              constructor
              · change (0x20 : Nat) ≤ c.val.toNat; omega
              · change c.val.toNat ≤ (0x10FFFF : Nat)
                have := c.valid; unfold UInt32.isValidChar at this; omega
          simp only [h_json, Bool.not_true]; rw [if_neg Bool.false_ne_true]
          -- Advance and apply IH
          have hcorr_c := advance_non_newline_corr sc c _ hcorr h_lt_c
            (fun h => by subst h; exact absurd h_ef (by decide))
            (fun h => by subst h; exact absurd h_ef (by decide))
          have h_col_c : (sc.col + 1 : Nat) = sc.advance.col := hcorr_c.col_eq
          rw [h_col_c] at hcorr_c
          rw [show sc.inputEnd = sc.advance.inputEnd from by rw [advance_inputEnd]]
          exact ih sc.advance (acc.push c) fuel' hcorr_c
            (by simp [List.length_cons] at h_f; omega)

/-! ## §3  Scanner Acceptance of Canonical Output (Step 1)

The main technical content: proving the scanner accepts emitter output.
-/

/-- **Scalar case**: The scanner accepts any double-quoted scalar produced
    by the emitter. -/
theorem scan_accepts_emitScalar (content : String) :
    ∃ tokens, scanFiltered (emitScalar content) = .ok tokens := by
  sorry

/-- **Main theorem**: The scanner accepts any canonical emitter output.

    For any grammable `YamlValue`, `scanFiltered (emit v)` succeeds.
    This is Step 1 of the universal round-trip proof.

    **Proof strategy**: Structural induction on `YamlValue`.
    - Scalar case: delegates to `scan_accepts_emitScalar`
    - Sequence/mapping cases: delegates to scanner acceptance of
      flow collections with inductively-accepted sub-expressions
    - Alias case: impossible (excluded by `Grammable`) -/
theorem emit_produces_valid_yaml (v : YamlValue) (hg : Grammable v false) :
    ∃ tokens, scanFiltered (emit v) = .ok tokens := by
  cases hg with
  | scalar s _ h =>
    -- emit (.scalar s) = emitScalar s.content
    exact scan_accepts_emitScalar s.content
  | sequence style items tag anchor _ h =>
    -- emit (.sequence style items tag anchor) = "[" ++ emitList items.toList ++ "]"
    -- Requires scanner compositionality for flow sequences:
    -- scanner threads state through [, comma-separated items, ]
    sorry
  | mapping style pairs tag anchor _ hk hv =>
    -- emit (.mapping style pairs tag anchor) = "{" ++ emitPairList pairs.toList ++ "}"
    -- Requires scanner compositionality for flow mappings:
    -- scanner threads state through {, colon/comma-separated pairs, }
    sorry

/-! ## §4  Full Pipeline: Emit → Scan → Parse

Combining scanner acceptance (Step 1) with parser acceptance (Step 2).

### Step 2 Architecture

Step 1 gives us `scanFiltered (emit v) = .ok tokens`. Step 2 must show
that `parseStream` also succeeds on those tokens. The key argument:

1. **Stream boundaries**: `scanFiltered` always produces `streamStart` as
   the first token and `streamEnd` as the last (by scanner construction).
2. **Single implicit document**: The emitter produces no `---`/`...` markers
   and no directives, so `parseStreamLoop` in `.initial` state sees bare
   content → enters `parseDocument` with no directive overhead.
3. **No bare-document violation**: After the single document is parsed, only
   `streamEnd` remains. `StreamState.validNextToken .afterDocument .streamEnd`
   is always `true`, so `invalidBareDocument` cannot fire.
4. **Parser dispatch succeeds**: `parseNode` dispatches on token type:
   - `scalar` (double-quoted) → single token consumption, always succeeds
   - `flowSequenceStart` → `parseFlowSequence` handles `[`, `,`, `]`
   - `flowMappingStart` → `parseFlowMapping` handles `{`, `:`, `,`, `}`
5. **Fuel sufficiency**: `parseStream` allocates `tokens.size` fuel.
   Each recursive `parseNode` call consumes ≥1 token, so fuel cannot
   be exhausted for well-formed flow output.
6. **No semantic errors**: The emitter produces no anchors (no
   `duplicateAnchor`), no aliases (no `undefinedAlias`), no tags (no
   `undeclaredTagHandle`), and no block content (no `trailingContent`
   on document start line).
-/

/-- **Parse acceptance** (Step 2): The parser accepts the token sequence
    produced by scanning canonical emitter output.

    Given that the scanner successfully tokenized emitter output,
    `parseStream` also succeeds. The emitter's restricted output format
    (double-quoted scalars, flow-only collections, single implicit document)
    avoids all `parseStream` error conditions. -/
theorem parseStream_accepts_emit_tokens (v : YamlValue) (hg : Grammable v false)
    (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered (emit v) = .ok tokens) :
    ∃ docs, parseStream tokens = .ok docs := by
  sorry

/-- **Full pipeline (raw)**: The canonical emitter's output parses
    successfully through `parseYamlRaw`.

    Composes Step 1 (`emit_produces_valid_yaml`: scanner acceptance) with
    Step 2 (`parseStream_accepts_emit_tokens`: parser acceptance) via
    `parseYamlRaw_pipeline` (scan + parse → pipeline success). -/
theorem emit_parse_succeeds (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYamlRaw (emit v) = .ok docs := by
  obtain ⟨tokens, h_scan⟩ := emit_produces_valid_yaml v hg
  obtain ⟨docs, h_parse⟩ := parseStream_accepts_emit_tokens v hg tokens h_scan
  exact ⟨docs, Composition.parseYamlRaw_pipeline (emit v) tokens docs h_scan h_parse⟩

/-- **Full pipeline (with compose)**: Emitter output parses successfully
    through `parseYaml`, which resolves aliases via `YamlDocument.compose`.

    Since the emitter produces no aliases (`Grammable` excludes `.alias`
    nodes), compose is effectively the identity on values, but the
    types require going through this step. -/
theorem emit_parseYaml_succeeds (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYaml (emit v) = .ok docs := by
  obtain ⟨raw_docs, h_raw⟩ := emit_parse_succeeds v hg
  exact ⟨raw_docs.map YamlDocument.compose, by simp only [parseYaml, h_raw]⟩

/-- **Single document**: The canonical emitter's output produces exactly one
    document when parsed.

    The emitter generates a single implicit document (no `---` markers, no
    multiple-document output), so `parseStreamLoop` produces `#[doc]`.
    This is needed for the universal round-trip theorem which asserts
    `docs.size = 1`. -/
theorem emit_produces_single_document (v : YamlValue) (hg : Grammable v false)
    (docs : Array YamlDocument)
    (h : parseYamlRaw (emit v) = .ok docs) :
    docs.size = 1 := by
  sorry

/-- **Grammability preservation**: The parsed output of emitter output
    is grammable. Follows from `parseStream_output_grammable` applied
    to the scan+parse decomposition. -/
theorem emit_parsed_grammable (v : YamlValue) (hg : Grammable v false)
    (docs : Array YamlDocument)
    (h : parseYaml (emit v) = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable doc.value false := by
  sorry

/-- **Content fidelity**: Parsing canonical emitter output recovers content
    equivalent to the original value.

    The canonical emitter produces double-quoted scalars, flow-style
    collections, and no aliases/tags/anchors. Parsing this output yields
    values with the same string content for scalars and the same tree
    structure for collections, differing only in style annotations.
    Since `contentEq` ignores style, the parsed result is
    content-equivalent to the original.

    **Proof strategy**: Structural induction on `v`:
    - Scalar: `escapeString` round-trips through the scanner's
      `collectDoubleQuotedLoop` + `processEscape`, recovering the
      original content string. `contentEq` ignores scalar style.
    - Sequence: By IH each element round-trips content-equivalently.
      The parser reconstructs the list from flow tokens.
    - Mapping: By IH each key/value round-trips content-equivalently.
      The parser reconstructs pairs from flow tokens. -/
theorem emit_roundtrip_content_eq (v : YamlValue) (hg : Grammable v false)
    (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit v) = .ok raw_docs)
    (h_size : raw_docs.size = 1) :
    contentEq v (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  sorry

/-- **Universal round-trip**: For every grammable YAML value, emitting it
    and re-parsing produces a single document whose value is
    content-equivalent to the original.

    This is the main theorem of v0.4.7 (Phase E). It composes:
    - Step 1: `emit_produces_valid_yaml` (scanner accepts emitter output)
    - Step 2: `parseStream_accepts_emit_tokens` (parser accepts scanned tokens)
    - Step 3a: `emit_produces_single_document` (exactly one document)
    - Step 3b: `emit_roundtrip_content_eq` (content fidelity) -/
theorem universal_roundtrip (v : YamlValue) (hg : Grammable v false) :
    ∃ docs, parseYaml (emit v) = .ok docs ∧
            docs.size = 1 ∧
            contentEq v docs[0]!.value = true := by
  obtain ⟨raw_docs, h_raw⟩ := emit_parse_succeeds v hg
  have h_raw_size := emit_produces_single_document v hg raw_docs h_raw
  refine ⟨raw_docs.map YamlDocument.compose, ?_, ?_, ?_⟩
  · simp only [parseYaml, h_raw]
  · simp [Array.size_map, h_raw_size]
  · exact emit_roundtrip_content_eq v hg raw_docs h_raw h_raw_size

end Lean4Yaml.Proofs.EmitterScannability
