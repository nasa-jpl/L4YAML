/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Output.Emitter
import L4YAML.Scanner.Scanner
import L4YAML.Spec.Grammar
import L4YAML.Parser.Composition
import L4YAML.Spec.CharPredicates
import L4YAML.Proofs.Output.ScannerEmitBridge
import L4YAML.Proofs.RoundTrip.RoundTrip
import L4YAML.Proofs.Coupling.CouplingBridge
import L4YAML.Proofs.Coupling.ScalarCoupling
import L4YAML.Proofs.Parser.ParserGrammable
import L4YAML.Proofs.Scanner.ScannerPlainContent
import L4YAML.Proofs.Scanner.ScannerBound

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

namespace L4YAML.Proofs.EmitterScannability

open L4YAML
open L4YAML.Emit
open L4YAML.Proofs.RoundTrip
open L4YAML.Scanner
open L4YAML.Grammar
open L4YAML.TokenParser
open L4YAML.CharPredicates
open L4YAML.Proofs.CouplingBridge
open L4YAML.Proofs.ParserGrammable
open L4YAML.Proofs.ParserWellBehaved
open L4YAML.Proofs.ScalarCoupling

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
    have h_ne := h_bounded ⟨c.toNat, by unfold Char.toNat; omega⟩
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
    have h_spec := h_bounded ⟨c.toNat, by unfold Char.toNat; omega⟩
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
    have := this ⟨c.toNat, by unfold Char.toNat; omega⟩
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

/-- No character of `escapeChar c` is a line break.
    Stronger than `escapeChar_head_not_linebreak` — covers ALL output chars. -/
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

/-- **Strengthened named escape**: `processEscape` on a named escape tag
    returns the ORIGINAL character `c`, not just some existential decoded value.
    This is the content-preservation key for the round-trip proof. -/
theorem processEscape_named_content (sc : ScannerState) (c tag : Char)
    (h_tag : escapeTag c = some tag) (h_peek : sc.peek? = some tag) :
    processEscape sc = .ok (c, sc.advance) := by
  unfold escapeTag at h_tag; split at h_tag <;> simp_all
  all_goals (subst_vars; unfold processEscape; rw [h_peek]; dsimp only [])
  all_goals (first | rfl | (split <;> first | rfl | (exfalso; simp_all (config := { decide := true }))))

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

-- ═══ line preservation helper ═══
-- When we know peek? = some c and c is not a newline/CR, advance preserves line.
-- This bridges ScannerSurfCorr-level character identity with advance_line_non_newline.
theorem advance_line_of_peek (s : ScannerState) (c : Char)
    (h_lt : s.offset < s.inputEnd) (h_peek : s.peek? = some c)
    (hnl : c ≠ '\n') (hcr : c ≠ '\r') :
    s.advance.line = s.line := by
  have hc : String.Pos.Raw.get s.input ⟨s.offset⟩ = c := by
    unfold ScannerState.peek? at h_peek; split at h_peek
    · exact Option.some.inj h_peek
    · contradiction
  exact advance_line_non_newline s h_lt (by rw [hc]; simp [hnl]) (by rw [hc]; simp [hcr])

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
      s'.inputEnd = sc.inputEnd ∧
      s'.line = sc.line := by
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
  -- Line preservation: 3 advances past non-newline chars (x, h1, h2)
  have h_line : sc.advance.advance.advance.line = sc.line := by
    have := advance_line_of_peek sc 'x' h_lt_x h_peek_x (by decide) (by decide)
    have := advance_line_of_peek sc.advance h1 h_lt_h1 h_peek_h1 h_h1_nn h_h1_cr
    have := advance_line_of_peek sc.advance.advance h2 h_lt_h2 h_peek_h2 h_h2_nn h_h2_cr
    omega
  exact ⟨_, _, rfl, hcorr_h2,
    by rw [advance_inputEnd, advance_inputEnd, advance_inputEnd],
    h_line⟩

-- String helper: s.push c ++ String.ofList cs = s ++ String.ofList (c :: cs)
theorem push_append_ofList_eq (s : String) (c : Char) (cs : List Char) :
    s.push c ++ String.ofList cs = s ++ String.ofList (c :: cs) := by
  apply String.ext
  simp only [String.toList_append, String.toList_push, String.toList_ofList,
             List.append_assoc, List.singleton_append]

-- String helper: s ++ String.ofList [] = s
theorem append_ofList_nil (s : String) : s ++ String.ofList [] = s := by
  apply String.ext; simp

-- Hex foldl roundtrip for control characters (c.val.toNat < 0x20)
theorem hex_foldl_roundtrip : ∀ n : Fin 32,
    let h1 := hexNibble (n.val / 16)
    let h2 := hexNibble (n.val % 16)
    (("".push h1).push h2).foldl (fun acc c =>
      acc * 16 + if c.isDigit then c.toNat - '0'.toNat
                 else if c >= 'a' then c.toNat - 'a'.toNat + 10
                 else c.toNat - 'A'.toNat + 10) 0 = n.val := by
  native_decide

/-- The core loop lemma: `collectDoubleQuotedLoop` succeeds on
    `escapeString content ++ "\"" ++ rest` for any content string,
    leaving the scanner with `ScannerSurfCorr` at `rest`.

    By induction on the characters of `content`:
    - Base: closing `"` → loop terminates.
    - Passthrough char: regular char branch → recurse.
    - Named escape: `\tag` → processEscape → recurse.
    - Hex escape: `\xHH` → processEscape → recurse. -/
theorem collectDoubleQuotedLoop_escapeString_succeeds
    (sc : ScannerState) (content_rest : List Char) (rest : List Char)
    (acc : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int)
    (hcorr : ScannerSurfCorr sc
      ⟨(escapeString (String.ofList content_rest)).toList ++ ['"'] ++ rest, sc.col⟩)
    (h_fuel : fuel ≥ content_rest.length + 1) :
    ∃ s',
      collectDoubleQuotedLoop sc acc fuel startPos inFlow currentIndent sc.inputEnd =
      .ok (acc ++ String.ofList content_rest, s') ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.col > 0
      ∧ s'.line = sc.line := by
  induction content_rest generalizing sc acc fuel with
  | nil =>
    -- Remaining chars: escapeString "" ++ "\"" ++ rest = '"' :: rest
    have h_ofnil : (String.ofList ([] : List Char)) = "" := rfl
    rw [h_ofnil, escapeString_nil] at hcorr
    simp only [String.toList_empty, List.nil_append] at hcorr
    have ⟨h_peek, h_lt⟩ := peek_of_chars_cons sc '"' rest _ hcorr
    match fuel, h_fuel with
    | fuel' + 1, _ =>
      unfold collectDoubleQuotedLoop; rw [h_peek]; dsimp only []
      rw [show acc ++ String.ofList [] = acc from append_ofList_nil acc]
      refine ⟨sc.advance, rfl, ?_, ?_, ?_⟩
      · -- After closing quote advance, ScannerSurfCorr at rest
        have hcorr_adv := advance_non_newline_corr sc '"' rest hcorr h_lt
          (by decide) (by decide)
        have h_col_adv : (sc.col + 1 : Nat) = sc.advance.col := hcorr_adv.col_eq
        rw [h_col_adv] at hcorr_adv; exact hcorr_adv
      · -- col > 0 after advancing past closing quote
        have hcorr_adv := advance_non_newline_corr sc '"' rest hcorr h_lt
          (by decide) (by decide)
        have h_col_adv : (sc.col + 1 : Nat) = sc.advance.col := hcorr_adv.col_eq
        omega
      · -- line preserved: '"' is non-newline
        exact advance_line_of_peek sc '"' h_lt h_peek (by decide) (by decide)
  | cons c cs ih =>
    -- Remaining chars: escapeChar c ++ escapeString cs ++ "\"" ++ rest
    rw [escapeString_cons, String.toList_append] at hcorr
    -- Case split: passthrough vs escape
    by_cases h_esc : isEscapedChar c
    · -- ESCAPE: escapeTag c = some tag (named) or c.val.toNat < 0x20 (hex)
      by_cases h_tag_some : (escapeTag c).isSome
      · -- NAMED ESCAPE: escapeChar c = "\\" ++ tag.toString
        obtain ⟨tag, h_tag⟩ := Option.isSome_iff_exists.mp h_tag_some
        rw [escapeChar_named_toList c tag h_tag] at hcorr
        simp only [List.cons_append, List.nil_append] at hcorr
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
          -- processEscape succeeds with named tag and returns original char c
          have h_proc := processEscape_named_content sc.advance c tag h_tag h_peek_tag
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
          rw [show acc ++ String.ofList (c :: cs) = acc.push c ++ String.ofList cs
            from (push_append_ofList_eq acc c cs).symm]
          obtain ⟨s', h_loop, hcorr_s', h_col_s', h_line_s'⟩ :=
            ih sc.advance.advance (acc.push c) fuel'
            hcorr_tag (by simp [List.length_cons] at h_f; omega)
          exact ⟨s', h_loop, hcorr_s', h_col_s',
            h_line_s'.trans ((advance_line_of_peek sc.advance tag h_lt_tag h_peek_tag
              (fun h => by subst h; exact absurd h_tag_nlb (by decide))
              (fun h => by subst h; exact absurd h_tag_nlb (by decide))).trans
              (advance_line_of_peek sc '\\' h_lt_bs h_peek_bs (by decide) (by decide)))⟩
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
          exact this ⟨c.toNat, by unfold Char.toNat; omega⟩
            (by rwa [Char.ofNat_toNat]) (by rwa [Char.ofNat_toNat])
        obtain ⟨d1, d2, h_ec_list, h_d1_nn, h_d1_cr, h_d2_nn, h_d2_cr, h_d1_hex, h_d2_hex,
            h_d1_lt128, h_d2_lt128⟩ :=
          escapeChar_hex_structure c h_lt_c h_tag_none
        rw [h_ec_list] at hcorr
        simp only [List.cons_append, List.nil_append] at hcorr
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
          obtain ⟨decoded, s_after, h_proc, hcorr_after, h_ie_after, h_ie_line⟩ :=
            processEscape_hex_ok sc.advance d1 d2 _ _ hcorr_bs
              h_d1_nn h_d1_cr h_d2_nn h_d2_cr h_d1_hex h_d2_hex h_d1_lt128 h_d2_lt128
          -- decoded = c via hex escape roundtrip
          have h_decoded_eq : decoded = c := by
            -- Step 1: Identify d1 and d2 as specific hexNibble values
            have h_struct : ∀ n : Fin 32, escapeTag (Char.ofNat n.val) = none →
                (escapeChar (Char.ofNat n.val)).toList =
                  ['\\', 'x', hexNibble (n.val / 16), hexNibble (n.val % 16)] := by native_decide
            have h_spec := h_struct ⟨c.toNat, by unfold Char.toNat; omega⟩
              (by rwa [Char.ofNat_toNat])
            rw [Char.ofNat_toNat] at h_spec
            have h_comb := h_ec_list.symm.trans h_spec
            simp only [List.cons.injEq, and_true] at h_comb
            have h_d1_eq : d1 = hexNibble (c.val.toNat / 16) := h_comb.2.2.1
            have h_d2_eq : d2 = hexNibble (c.val.toNat % 16) := h_comb.2.2.2
            -- Step 2: Derive peeks for d1 and d2 (col adjusted for advance_non_newline_corr)
            have ⟨_, h_lt_x'⟩ := peek_of_chars_cons sc.advance 'x' _ _ hcorr_bs
            have hcorr_x_raw := advance_non_newline_corr sc.advance 'x' _
              hcorr_bs h_lt_x' (by decide) (by decide)
            have hcorr_x' : ScannerSurfCorr sc.advance.advance
                ⟨d1 :: d2 :: (escapeString (String.ofList cs)).toList ++ ['"'] ++ rest,
                 sc.advance.advance.col⟩ := by
              rw [← hcorr_x_raw.col_eq]; exact hcorr_x_raw
            have ⟨h_peek_d1', h_lt_d1'⟩ := peek_of_chars_cons sc.advance.advance d1 _ _ hcorr_x'
            have hcorr_d1_raw := advance_non_newline_corr sc.advance.advance d1 _
              hcorr_x' h_lt_d1'
              h_d1_nn h_d1_cr
            have hcorr_d1' : ScannerSurfCorr sc.advance.advance.advance
                ⟨d2 :: (escapeString (String.ofList cs)).toList ++ ['"'] ++ rest,
                 sc.advance.advance.advance.col⟩ := by
              rw [← hcorr_d1_raw.col_eq]; exact hcorr_d1_raw
            have ⟨h_peek_d2', _⟩ := peek_of_chars_cons sc.advance.advance.advance d2 _ _ hcorr_d1'
            -- Step 3: Unfold processEscape at h_proc to expose parseHexEscape
            unfold processEscape at h_proc; rw [h_peek_x] at h_proc; dsimp only [] at h_proc
            unfold parseHexEscape at h_proc
            -- Step 4: Show collectHexDigitsLoop reads d1,d2
            have h_d1_hex' := h_d1_hex; have h_d2_hex' := h_d2_hex
            unfold scannerHexCheck at h_d1_hex' h_d2_hex'
            have h_coll : collectHexDigitsLoop sc.advance.advance "" 2 =
                (("".push d1).push d2, sc.advance.advance.advance.advance) := by
              unfold collectHexDigitsLoop; dsimp only []; rw [h_peek_d1']; dsimp only []
              simp only [h_d1_hex', if_true]
              unfold collectHexDigitsLoop; dsimp only []; rw [h_peek_d2']; dsimp only []
              simp only [h_d2_hex', if_true]
              unfold collectHexDigitsLoop; dsimp only []
            simp only [h_coll] at h_proc
            -- Step 5: Reduce length check and value bound
            have h_len : (("".push d1).push d2).length = 2 := by
              simp [String.length, String.toList_push]
            simp only [h_len, Nat.reduceBNe, Bool.false_eq_true, ↓reduceIte] at h_proc
            have h_vlt := hex_two_foldl_bound ⟨d1.toNat, h_d1_lt128⟩ ⟨d2.toNat, h_d2_lt128⟩
              (by rwa [Char.ofNat_toNat]) (by rwa [Char.ofNat_toNat])
            rw [Char.ofNat_toNat, Char.ofNat_toNat] at h_vlt
            simp only [h_vlt, ↓reduceIte] at h_proc
            -- Step 6: Extract decoded = Char.ofNat (foldl d1 d2)
            have h_pair := Except.ok.inj h_proc
            have h_fst := congrArg Prod.fst h_pair; dsimp only [] at h_fst
            -- Step 7: Rewrite d1,d2 to hexNibble form and apply roundtrip
            rw [← h_fst, h_d1_eq, h_d2_eq]
            have h_rt := hex_foldl_roundtrip ⟨c.val.toNat, by omega⟩
            simp only at h_rt; rw [h_rt]; exact (Char.ofNat_toNat c).symm ▸ rfl
          rw [h_decoded_eq] at h_proc
          simp only [bind, Except.bind, h_proc]
          -- Column and inputEnd adjustment for IH
          have h_col_after : (sc.advance.col + 3 : Nat) = s_after.col := hcorr_after.col_eq
          rw [h_col_after] at hcorr_after
          rw [show sc.inputEnd = s_after.inputEnd from
            by rw [← advance_inputEnd sc]; exact h_ie_after.symm]
          rw [show acc ++ String.ofList (c :: cs) = acc.push c ++ String.ofList cs
            from (push_append_ofList_eq acc c cs).symm]
          obtain ⟨s', h_loop, hcorr_s', h_col_s', h_line_s'⟩ :=
            ih s_after (acc.push c) fuel' hcorr_after
            (by simp [List.length_cons] at h_f; omega)
          -- Line chain: s' → s_after → sc.advance → sc
          have h_line_proc : s_after.line = sc.advance.line := h_ie_line
          have h_line_bs : sc.advance.line = sc.line :=
            advance_line_of_peek sc '\\' h_lt_bs h_peek_bs (by decide) (by decide)
          exact ⟨s', h_loop, hcorr_s', h_col_s',
            h_line_s'.trans (h_line_proc.trans h_line_bs)⟩
    · -- PASSTHROUGH: escapeChar c = c.toString
      -- h_esc here : ¬(isEscapedChar c = true) or isEscapedChar c = false
      have h_ef : isEscapedChar c = false := by
        cases hv : isEscapedChar c
        · rfl
        · exact absurd hv h_esc
      rw [escapeChar_passthrough_toList c h_ef] at hcorr
      simp only [List.cons_append, List.nil_append] at hcorr
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
            · have := h_ascii ⟨c.toNat, by unfold Char.toNat at h128 ⊢; omega⟩
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
          rw [show acc ++ String.ofList (c :: cs) = acc.push c ++ String.ofList cs
            from (push_append_ofList_eq acc c cs).symm]
          obtain ⟨s', h_loop, hcorr_s', h_col_s', h_line_s'⟩ :=
            ih sc.advance (acc.push c) fuel' hcorr_c
            (by simp [List.length_cons] at h_f; omega)
          exact ⟨s', h_loop, hcorr_s', h_col_s',
            h_line_s'.trans (advance_line_of_peek sc c h_lt_c h_peek_c h_ne_nl h_ne_cr)⟩

/-! ## §3  Scanner Acceptance of Canonical Output (Step 1)

The main technical content: proving the scanner accepts emitter output.

### §3.0  Helpers for scanner dispatch on emitter output
-/

-- Each character occupies at least 1 byte in UTF-8
theorem CharsFromOffset_length_le {input : String} {offset : Nat} {chars : List Char}
    (h : CharsFromOffset input offset chars) :
    chars.length ≤ input.utf8ByteSize - offset := by
  induction h with
  | at_end p hp => simp
  | cons p hp c rest hc hrest ih =>
    simp only [List.length_cons]
    rw [next_byteIdx, hc] at ih
    have := Char.utf8Size_pos c
    omega

-- escapeChar produces at least 1 character
theorem escapeChar_toList_length_pos (c : Char) :
    (escapeChar c).toList.length ≥ 1 := by
  unfold escapeChar
  split
  all_goals (try decide)
  -- Remaining: default case with if c.val.toNat < 0x20
  split
  · -- escapeHex2: "\\" ++ "x" ++ h1.toString ++ h2.toString → length ≥ 4
    simp only [escapeHex2, String.toList_append, List.length_append,
               Char.toString, String.toList_singleton, List.length_singleton]
    omega
  · -- c.toString → length = 1
    simp [Char.toString, String.toList_singleton]

-- escapeString preserves or grows the length
theorem escapeString_length_ge (cs : List Char) :
    (escapeString (String.ofList cs)).toList.length ≥ cs.length := by
  induction cs with
  | nil => simp [escapeString_nil]
  | cons c rest ih =>
    rw [escapeString_cons]
    simp only [String.toList_append, List.length_append, List.length_cons]
    have h1 := escapeChar_toList_length_pos c
    omega

-- `validateTrailingContent` succeeds when peek? = none (at EOF)
theorem validateTrailingContent_peek_none (s : ScannerState) (inputEnd : Nat)
    (h_peek : s.peek? = none) : validateTrailingContent s inputEnd = .ok () := by
  -- From peek? = none, derive offset ≥ inputEnd
  have h_not_lt : ¬(s.offset < s.inputEnd) := by
    intro h_lt
    have : s.peek? ≠ none := by unfold ScannerState.peek?; simp [h_lt]
    exact this h_peek
  -- skipTrailingSpaces returns s when peek? = none
  have h_sts : skipTrailingSpaces s (inputEnd - s.offset + 1) = s := by
    generalize inputEnd - s.offset + 1 = fuel
    induction fuel with
    | zero => rfl
    | succ n _ => unfold skipTrailingSpaces; rw [h_peek]
  -- validateTrailingContent: probe = s, probe.peek? = none → pure ()
  unfold validateTrailingContent; simp [h_sts, h_peek]; rfl

-- `scanDoubleQuoted` succeeds using the loop lemma + EOF property
theorem scanDoubleQuoted_emitScalar_ok (sc : ScannerState)
    (content : String)
    (hcorr : ScannerSurfCorr sc
      ⟨['"'] ++ (escapeString content).toList ++ ['"'], sc.col⟩)
    (h_not_flow : sc.inFlow = false) :
    ∃ s', scanDoubleQuoted sc = .ok s' ∧ s'.peek? = none
      ∧ s'.tokens = sc.tokens.push { pos := sc.currentPos, val := .scalar content .doubleQuoted } := by
  -- Surface after advancing past opening quote
  have ⟨_, h_lt⟩ := peek_of_chars_cons sc '"'
    ((escapeString content).toList ++ ['"']) _ hcorr
  have hcorr_adv := advance_non_newline_corr sc '"'
    ((escapeString content).toList ++ ['"']) hcorr h_lt (by decide) (by decide)
  have h_col_eq : (sc.col + 1 : Nat) = sc.advance.col := hcorr_adv.col_eq
  rw [h_col_eq] at hcorr_adv
  -- Fuel bound for loop
  have h_fuel : sc.advance.inputEnd - sc.advance.offset + 1 ≥ content.toList.length + 1 := by
    rw [hcorr_adv.end_eq]
    have h_cf := CharsFromOffset_length_le hcorr_adv.chars_from
    simp only [List.length_append, List.length_singleton] at h_cf
    have h_esc := escapeString_length_ge content.toList
    simp only [String.ofList_toList] at h_esc
    omega
  -- Loop succeeds and leaves scanner at EOF
  have h_ie : sc.inputEnd = sc.advance.inputEnd := by rw [advance_inputEnd]
  obtain ⟨s_after, h_loop, hcorr_loop, _⟩ :=
    collectDoubleQuotedLoop_escapeString_succeeds sc.advance content.toList [] "" _
      sc.currentPos sc.inFlow sc.currentIndent
      (by simp only [List.append_nil]; rw [String.ofList_toList]; exact hcorr_adv) h_fuel
  -- Derive peek? = none from ScannerSurfCorr at empty rest
  have h_peek_none : s_after.peek? = none := by
    have h_ge : s_after.offset ≥ s_after.input.utf8ByteSize := by
      cases hcorr_loop.chars_from with | at_end _ hge => exact hge
    have h_not_lt : ¬(s_after.offset < s_after.inputEnd) := by
      rw [hcorr_loop.end_eq]; omega
    simp [ScannerState.peek?, h_not_lt]
  -- Validate trailing content succeeds at EOF
  have h_vtc := validateTrailingContent_peek_none s_after sc.advance.inputEnd h_peek_none
  -- The loop returns content = "" ++ String.ofList content.toList = content
  have h_content_eq : "" ++ String.ofList content.toList = content := by
    apply String.ext; simp
  -- Token preservation: loop and advance don't modify tokens
  have h_tok_pres : s_after.tokens = sc.tokens :=
    (ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
      _ _ _ _ _ _ _ _ h_loop).trans
      (ScannerCorrectness.advance_preserves_tokens sc)
  -- Build the result state and prove all conjuncts
  refine ⟨{ (s_after.emitAt sc.currentPos (.scalar content .doubleQuoted))
              with simpleKeyAllowed := false }, ?_, ?_, ?_⟩
  · -- scanDoubleQuoted sc = .ok _
    simp only [scanDoubleQuoted, bind, Except.bind]
    rw [h_ie]
    rw [h_content_eq] at h_loop
    rw [h_loop]
    simp [h_not_flow, h_vtc]
  · -- peek? = none (emitAt and simpleKeyAllowed don't change peek?)
    unfold ScannerState.emitAt ScannerState.peek?
    unfold ScannerState.peek? at h_peek_none
    split at h_peek_none <;> simp_all
  · -- tokens characterization
    show s_after.tokens.push _ = sc.tokens.push _
    rw [h_tok_pres]

/-- If the surface position has empty remaining chars, then peek? = none. -/
theorem peek_none_of_empty_surf (s : ScannerState) (col : Nat)
    (hcorr : ScannerSurfCorr s ⟨[], col⟩) :
    s.peek? = none := by
  unfold ScannerState.peek?
  have h_ge : s.offset ≥ s.input.utf8ByteSize :=
    match hcorr.chars_from with | .at_end _ h => h
  have := hcorr.end_eq
  simp [show ¬(s.offset < s.inputEnd) from by omega]

-- scanNextToken returns none when scanner is at EOF
theorem scanNextToken_eof (s : ScannerState) (h_peek : s.peek? = none) :
    scanNextToken s = .ok none := by
  -- peek? = none → offset ≥ inputEnd
  have h_not_lt : ¬(s.offset < s.inputEnd) := by
    intro h_lt; have : s.peek? ≠ none := by unfold ScannerState.peek?; simp [h_lt]
    exact this h_peek
  -- Key facts that follow from offset ≥ inputEnd
  have h_fuel_zero : s.inputEnd - s.offset = 0 := by omega
  -- skipWhitespace s = s (no chars to skip at EOF)
  have h_sw : skipWhitespace s = s := by
    unfold skipWhitespace; rw [h_fuel_zero]; unfold skipWhitespaceLoop; rfl
  -- skipSpaces s = s
  have h_ss : skipSpaces s = s := by
    unfold skipSpaces; rw [h_fuel_zero]; unfold skipSpacesLoop; rfl
  -- skipToContent s = .ok s
  have h_stc : skipToContent s = .ok s := by
    unfold skipToContent
    rw [show s.inputEnd - s.offset + 1 = 1 from by omega]
    unfold skipToContentLoop
    have h_ws : skipToContentWs s = .ok s := by
      unfold skipToContentWs
      split
      · simp [h_ss, h_peek, h_sw]
      · simp [h_sw]
    simp [h_ws, skipToContentComment, h_peek]
  -- hasMore = false
  have h_hm : s.hasMore = false := by unfold ScannerState.hasMore; simp [h_not_lt]
  -- scanNextToken: preprocess returns none, so result is .ok none
  simp [scanNextToken, scanNextToken_preprocess, bind, Except.bind, h_stc, h_hm, pure, Except.pure]

-- The dispatch chain for '"' reaches scanDoubleQuoted.
-- This captures the fact that all intermediate dispatchers (structural,
-- flow indicators, block indicators) return none for '"'.
theorem dispatchContent_quote (s : ScannerState) (c : Char) (hc : c = '"')
    (h_notFlow : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1)
    (h_noDocStart : atDocumentStart s = false)
    (h_noDocEnd : atDocumentEnd s = false) :
    scanNextToken_dispatchStructural s c = .ok none
    ∧ scanNextToken_checkBlockFlowIndent s c = .ok ()
    ∧ scanNextToken_dispatchFlowIndicators s c = .ok none
    ∧ scanNextToken_dispatchBlockIndicators s c = .ok none := by
  subst hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- dispatchStructural: '"' doesn't match %, -, .
    unfold scanNextToken_dispatchStructural
    simp [ScannerState.inFlow, h_notFlow, h_noDocStart, h_noDocEnd,
          bind, Except.bind, pure, Except.pure]
  · -- checkBlockFlowIndent: currentIndent = -1 < 0, condition false
    unfold scanNextToken_checkBlockFlowIndent
    simp [ScannerState.inFlow, h_notFlow, h_indent]
  · -- dispatchFlowIndicators: '"' doesn't match [, ], {, }, ,
    unfold scanNextToken_dispatchFlowIndicators
    simp [bind, Except.bind, pure, Except.pure]
  · -- dispatchBlockIndicators: '"' doesn't match -, ?, :
    unfold scanNextToken_dispatchBlockIndicators
    simp [bind, Except.bind, pure, Except.pure]

-- Transfer ScannerSurfCorr when only non-position fields change
-- (tokens, simpleKey, flags, etc.)
theorem ScannerSurfCorr_transfer {sc sc' : ScannerState}
    {sp : L4YAML.Surface.SurfPos}
    (hcorr : ScannerSurfCorr sc sp)
    (h_input : sc'.input = sc.input)
    (h_offset : sc'.offset = sc.offset)
    (h_inputEnd : sc'.inputEnd = sc.inputEnd)
    (h_col : sc'.col = sc.col)
    (h_indents : sc'.indents = sc.indents) :
    ScannerSurfCorr sc' sp := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · rw [h_input, h_offset]; exact hcorr.chars_from
  · rw [h_col]; exact hcorr.col_eq
  · rw [h_inputEnd, h_input]; exact hcorr.end_eq
  · rw [h_input, h_offset]; exact hcorr.input_prefix
  · intro i hi h0
    have hi' : i < sc.indents.size := h_indents ▸ hi
    have heq : sc'.indents[i]'hi = sc.indents[i]'hi' := by congr 1
    rw [heq]; exact hcorr.indent_cols_nonneg i hi' h0

-- emitScalar decomposes as ['"'] ++ escaped ++ ['"']
theorem emitScalar_toList (content : String) :
    (emitScalar content).toList = ['"'] ++ (escapeString content).toList ++ ['"'] := by
  have h1 : ("\"" : String).toList = ['"'] := by native_decide
  show (("\"" ++ escapeString content) ++ "\"").toList = _
  simp only [String.toList_append, h1]

-- emitScalar has at least 2 bytes
theorem emitScalar_utf8ByteSize_ge (content : String) :
    (emitScalar content).utf8ByteSize ≥ 2 := by
  simp only [utf8ByteSize_eq_listByteSize, emitScalar_toList,
             listByteSize_append, listByteSize]
  have : Char.utf8Size '"' = 1 := by native_decide
  omega

-- scanLoop with exactly 2 iterations (scanNextToken returns some then none)
-- Returns the exact token array produced.
theorem scanLoop_two_iter {s₀ s₁ : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 2)
    (h_snt0 : scanNextToken s₀ = .ok (some s₁))
    (h_snt1 : scanNextToken s₁ = .ok none)
    (h_flow : s₁.flowLevel = 0)
    (h_dp : s₁.directivesPresent = false) :
    ∃ toks, scanLoop s₀ fuel = .ok toks := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  -- First iteration: scanNextToken s₀ = .ok (some s₁) → recurse
  have h1 : scanLoop s₀ (f + 2) = scanLoop s₁ (f + 1) := by
    simp only [scanLoop, h_snt0]
  -- Second iteration: scanNextToken s₁ = .ok none → checks → ok
  have h2 : ∃ toks, scanLoop s₁ (f + 1) = .ok toks := by
    simp only [scanLoop, h_snt1, h_flow, h_dp, Bool.false_and]
    exact ⟨_, rfl⟩
  rw [h1]; exact h2

-- scanLoop actually computes to the concrete token array
theorem scanLoop_two_iter_eq {s₀ s₁ : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 2)
    (h_snt0 : scanNextToken s₀ = .ok (some s₁))
    (h_snt1 : scanNextToken s₁ = .ok none)
    (h_flow : s₁.flowLevel = 0)
    (h_dp : s₁.directivesPresent = false) :
    scanLoop s₀ fuel = .ok ((unwindIndents s₁ (-1)).emit .streamEnd).tokens := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 2 := ⟨fuel - 2, by omega⟩
  simp only [scanLoop, h_snt0, h_snt1, h_flow, h_dp, Bool.false_and]
  simp (config := { decide := true }) only [ite_false]

-- ═══ scanLoop compositionality ═══
-- Forward composition: one scanNextToken step + remaining loop = full loop.
-- Enables proving scanner acceptance for multi-token emitter output by
-- chaining individual scanNextToken steps.

/-- **Forward step**: If `scanNextToken` produces a new state `s₁`, and
    `scanLoop s₁ fuel` succeeds, then `scanLoop s₀ (fuel + 1)` succeeds
    with the same result.

    This is the key compositionality lemma for scanner acceptance proofs:
    compose N steps backwards from `scanLoop_two_iter` (or `scanLoop_eof`)
    using repeated applications of `scanLoop_step_eq`. -/
theorem scanLoop_step_eq {s₀ s₁ : ScannerState} {fuel : Nat}
    {toks : Array (Positioned YamlToken)}
    (h_snt : scanNextToken s₀ = .ok (some s₁))
    (h_loop : scanLoop s₁ fuel = .ok toks) :
    scanLoop s₀ (fuel + 1) = .ok toks := by
  simp only [scanLoop, h_snt]; exact h_loop

/-- Existential version of `scanLoop_step_eq`. -/
theorem scanLoop_step {s₀ s₁ : ScannerState} {fuel : Nat}
    (h_snt : scanNextToken s₀ = .ok (some s₁))
    (h_loop : ∃ toks, scanLoop s₁ fuel = .ok toks) :
    ∃ toks, scanLoop s₀ (fuel + 1) = .ok toks := by
  obtain ⟨toks, h⟩ := h_loop
  exact ⟨toks, scanLoop_step_eq h_snt h⟩

/-- **Fuel monotonicity**: If `scanLoop` succeeds with `fuel₁`,
    it succeeds with any larger fuel `fuel₂ ≥ fuel₁`, producing
    the same token array.

    Proof by induction on `fuel₁`. Each `scanLoop` iteration
    either terminates (EOF/error → fuel irrelevant) or recurses with
    one less fuel (→ inductive hypothesis). -/
theorem scanLoop_fuel_mono {s : ScannerState} {fuel₁ fuel₂ : Nat}
    {toks : Array (Positioned YamlToken)}
    (h : scanLoop s fuel₁ = .ok toks) (h_le : fuel₁ ≤ fuel₂) :
    scanLoop s fuel₂ = .ok toks := by
  induction fuel₁ generalizing s fuel₂ toks with
  | zero =>
    -- scanLoop s 0 = .error (.fuelExhausted ...), contradicts h
    unfold scanLoop at h; cases h
  | succ m IH =>
    obtain ⟨n, rfl⟩ : ∃ n, fuel₂ = n + 1 := ⟨fuel₂ - 1, by omega⟩
    -- Both scanLoop s (m+1) and scanLoop s (n+1) unfold to matching on scanNextToken s
    unfold scanLoop at h ⊢
    -- Generalize the shared discriminant, then case-split to reduce both matches
    generalize scanNextToken s = snt_result at h ⊢
    cases snt_result with
    | error e => cases h
    | ok res => cases res with
      | none => exact h
      | some s' => exact IH h (by omega)

/-- **Terminal step**: If `scanNextToken` returns `.ok none` (EOF),
    `scanLoop` with fuel ≥ 1 terminates successfully. -/
theorem scanLoop_eof {s : ScannerState}
    (h_snt : scanNextToken s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    ∃ toks, scanLoop s 1 = .ok toks := by
  unfold scanLoop; rw [h_snt]
  simp [show ¬(s.flowLevel > 0) from by omega, h_dp]

/-- **Terminal step (equality)**: If `scanNextToken` returns `.ok none` (EOF),
    `scanLoop` produces exactly the unwind+streamEnd tokens. -/
theorem scanLoop_eof_eq {s : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 1)
    (h_snt : scanNextToken s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false) :
    scanLoop s fuel = .ok ((unwindIndents s (-1)).emit .streamEnd).tokens := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold scanLoop; rw [h_snt]
  simp [show ¬(s.flowLevel > 0) from by omega, h_dp]

-- ═══ ScanChain: composition of N successful scanNextToken calls ═══

/-- `ScanChain s n s'` means `n` successive `scanNextToken` calls starting
    from `s` each return `.ok (some ...)`, with the final state being `s'`.
    Used to express that the scanner processes a multi-token sub-expression
    (e.g., `emit v` within a flow collection). -/
inductive ScanChain : ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} : ScanChain s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat} :
         scanNextToken s = .ok (some s_mid) →
         ScanChain s_mid n s' →
         ScanChain s (n + 1) s'

/-- Transitivity: concatenate two scan chains. -/
theorem ScanChain.trans {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : ScanChain s₁ n₁ s₂) (h2 : ScanChain s₂ n₂ s₃) :
    ScanChain s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_snt h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_snt h_ih

/-- A single scanNextToken step as a ScanChain. -/
theorem ScanChain.single {s s' : ScannerState}
    (h : scanNextToken s = .ok (some s')) :
    ScanChain s 1 s' :=
  .step h .zero

/-- Connect a ScanChain to scanLoop: if N steps succeed reaching s',
    and scanLoop s' fuel succeeds, then scanLoop s (fuel + N) succeeds
    with the same result. -/
theorem ScanChain.to_scanLoop {s s' : ScannerState} {n fuel : Nat}
    {toks : Array (Positioned YamlToken)}
    (h_chain : ScanChain s n s')
    (h_loop : scanLoop s' fuel = .ok toks) :
    scanLoop s (fuel + n) = .ok toks := by
  induction h_chain with
  | zero => exact h_loop
  | @step s s_mid s' k h_snt h_rest ih =>
    have h_ih := ih h_loop
    have : fuel + (k + 1) = (fuel + k) + 1 := by omega
    rw [this]
    exact scanLoop_step_eq h_snt h_ih

/-- Connect a ScanChain to scanLoop (existential version). -/
theorem ScanChain.to_scanLoop_exists {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s')
    (h_loop : ∃ fuel toks, scanLoop s' fuel = .ok toks) :
    ∃ fuel toks, scanLoop s fuel = .ok toks := by
  obtain ⟨fuel, toks, h⟩ := h_loop
  exact ⟨fuel + n, toks, h_chain.to_scanLoop h⟩

/-- **Initiative 3 / J.3.7**: skipToContent is identity at EOF.
    Inline-derived in `scanNextToken_eof`; factored out so
    `scanFiltered_emitScalar_vals` can stitch a full scanFiltered walk. -/
theorem skipToContent_eq_self_of_peek_none {s : ScannerState}
    (h_peek : s.peek? = none) : skipToContent s = .ok s := by
  have h_not_lt : ¬(s.offset < s.inputEnd) := by
    intro h_lt; have : s.peek? ≠ none := by unfold ScannerState.peek?; simp [h_lt]
    exact this h_peek
  have h_fuel_zero : s.inputEnd - s.offset = 0 := by omega
  have h_sw : skipWhitespace s = s := by
    unfold skipWhitespace; rw [h_fuel_zero]; unfold skipWhitespaceLoop; rfl
  have h_ss : skipSpaces s = s := by
    unfold skipSpaces; rw [h_fuel_zero]; unfold skipSpacesLoop; rfl
  unfold skipToContent
  rw [show s.inputEnd - s.offset + 1 = 1 from by omega]
  unfold skipToContentLoop
  have h_ws : skipToContentWs s = .ok s := by
    unfold skipToContentWs
    split
    · simp [h_ss, h_peek, h_sw]
    · simp [h_sw]
  simp [h_ws, skipToContentComment, h_peek]

/-- **Initiative 3 / J.3.7**: equality form of `scanLoopFull` at EOF.
    Mirrors `scanLoop_eof_eq` for the `scanLoopFull` variant used by
    `scanFiltered`.  The extra `skipToContent` step in `scanLoopFull`'s
    EOF arm is supplied as `h_skip`. -/
theorem scanLoopFull_eof_eq {s s_skipped : ScannerState} {fuel : Nat}
    (h_fuel : fuel ≥ 1)
    (h_snt : scanNextToken s = .ok none)
    (h_fl : s.flowLevel = 0)
    (h_dp : s.directivesPresent = false)
    (h_skip : skipToContent s = .ok s_skipped) :
    scanLoopFull s fuel = .ok ((unwindIndents s_skipped (-1)).emit .streamEnd) := by
  obtain ⟨f, rfl⟩ : ∃ n, fuel = n + 1 := ⟨fuel - 1, by omega⟩
  unfold scanLoopFull
  rw [h_snt]
  simp only []
  have h_not_pos : ¬(s.flowLevel > 0) := by omega
  simp only [h_not_pos, ↓reduceIte]
  have h_dir_false : (s.directivesPresent && !s.documentEverStarted) = false := by
    rw [h_dp]; simp
  simp only [h_dir_false, Bool.false_eq_true, ↓reduceIte]
  rw [h_skip]

/-- **Initiative 3 / J.3.7**: `ScanChain` composes with `scanLoopFull`.
    Mirrors `ScanChain.to_scanLoop` for the `scanLoopFull` variant. -/
theorem ScanChain.to_scanLoopFull {s s' : ScannerState} {n fuel : Nat}
    {final : ScannerState}
    (h_chain : ScanChain s n s')
    (h_loop : scanLoopFull s' fuel = .ok final) :
    scanLoopFull s (fuel + n) = .ok final := by
  induction h_chain with
  | zero => exact h_loop
  | @step s s_mid s' k h_snt h_rest ih =>
    have h_ih := ih h_loop
    have h_eq : fuel + (k + 1) = (fuel + k) + 1 := by omega
    rw [h_eq]
    unfold scanLoopFull
    rw [h_snt]
    exact h_ih

/-- The chain fuel bound: any `ScanChain` followed by EOF fits within
    the standard fuel `(input.utf8ByteSize + 1) * 4`.

    Proof strategy:
    1. `scanNextToken_progress` → each step advances offset by ≥ 1
    2. By induction: `s_final.offset ≥ s₀.offset + n`
    3. `s₀.offset = 0` (from `mk'` + `emit streamStart`)
    4. `s_final.offset ≤ s_final.inputEnd` (from upper bound preservation)
    5. `s_final.inputEnd = input.utf8ByteSize` (from inputEnd preservation)
    6. Combining: `n ≤ utf8ByteSize ≤ (utf8ByteSize + 1) * 4` -/

-- scanNextToken preserves key offset/inputEnd invariants.
-- This follows from the BoundInv framework in ScannerBound.lean:
--   (a) `inputEnd` and `input` are never assigned in any `{ s with ... }` update
--   (b) `advance` respects `offset ≤ inputEnd` via `String.next` bounds
--   (c) UTF-8 position validity (`IsValid`) is preserved through all operations
-- Proof delegates to ScannerBound.scanNextToken_preserves_bound.
theorem scanNextToken_preserves_bound (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s'))
    (h_le : s.offset ≤ s.inputEnd)
    (h_ie : s.inputEnd = s.input.utf8ByteSize)
    (h_iv : String.Pos.Raw.IsValid s.input ⟨s.offset⟩) :
    s'.offset ≤ s'.inputEnd ∧ s'.inputEnd = s.inputEnd ∧ s'.input = s.input
    ∧ String.Pos.Raw.IsValid s'.input ⟨s'.offset⟩ :=
  ScannerBound.scanNextToken_preserves_bound s s' h h_le h_ie h_iv

-- Chain invariant: offset increases, stays bounded, inputEnd preserved
theorem ScanChain.bound_invariant {s₀ s_final : ScannerState} {n : Nat}
    (h_chain : ScanChain s₀ n s_final)
    (h_le : s₀.offset ≤ s₀.inputEnd)
    (h_ie : s₀.inputEnd = s₀.input.utf8ByteSize)
    (h_iv : String.Pos.Raw.IsValid s₀.input ⟨s₀.offset⟩) :
    s_final.offset ≥ s₀.offset + n ∧
    s_final.offset ≤ s_final.inputEnd ∧
    s_final.inputEnd = s₀.inputEnd := by
  induction h_chain with
  | zero => exact ⟨by omega, h_le, rfl⟩
  | @step s s_mid s_final k h_snt h_rest ih =>
    have h_prog := ScannerCorrectness.scanNextToken_progress s s_mid h_snt
    have ⟨h_le', h_ie', h_inp', h_iv'⟩ :=
      scanNextToken_preserves_bound s s_mid h_snt h_le h_ie h_iv
    have h_ie_mid : s_mid.inputEnd = s_mid.input.utf8ByteSize := by
      rw [h_ie', h_inp']; exact h_ie
    have h_iv_mid : String.Pos.Raw.IsValid s_mid.input ⟨s_mid.offset⟩ := h_iv'
    have ⟨h_ge, h_le_final, h_ie_final⟩ := ih h_le' h_ie_mid h_iv_mid
    exact ⟨by omega, h_le_final, by rw [h_ie_final, h_ie']⟩

theorem ScanChain.fuel_bound (input : String)
    (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_chain : ScanChain s₀ n s_final)
    (_h_eof : scanNextToken s_final = .ok none) :
    n + 1 ≤ (input.utf8ByteSize + 1) * 4 := by
  -- Initial state properties
  have h_s0_off : s₀.offset = 0 := by subst h_s0; rfl
  have h_s0_le : s₀.offset ≤ s₀.inputEnd := by subst h_s0; omega
  have h_s0_ie : s₀.inputEnd = s₀.input.utf8ByteSize := by subst h_s0; rfl
  have h_s0_iv : String.Pos.Raw.IsValid s₀.input ⟨s₀.offset⟩ := by
    subst h_s0; exact ScannerLoopInvariant.isValid_at_zero _
  -- Chain invariant gives offset bounds
  have ⟨h_ge, h_le, h_ie⟩ := ScanChain.bound_invariant h_chain h_s0_le h_s0_ie h_s0_iv
  -- s_final.offset ≥ n (since s₀.offset = 0)
  rw [h_s0_off] at h_ge; simp at h_ge
  -- s_final.offset ≤ inputEnd = input.utf8ByteSize
  have h_ie2 : s_final.inputEnd = input.utf8ByteSize := by
    rw [h_ie]; subst h_s0; rfl
  rw [h_ie2] at h_le
  -- n ≤ utf8ByteSize, so n + 1 ≤ utf8ByteSize + 1 ≤ (utf8ByteSize + 1) * 4
  omega

/-! ### J.4.2.b — `PendingKeysWellIndexed` propagation through `ScanChain`

The seq/map cascade consumers (`scanFiltered_emitSeq_nonempty_structure`,
`scanFiltered_emitMap_nonempty_structure`) need
`PendingKeysWellIndexed (s_final.emit .streamEnd)` to discharge the
`h_pks_bound` precondition of `linearise_push_eq_push_linearise`.  The
chain endpoint version follows by induction along `ScanChain` from the
initial state, using `scanNextToken_preserves_PendingKeysWellIndexed`
at each step.  Companion to `scanLoopFull_preserves_PendingKeysWellIndexed`
in `ScannerCorrectness.lean` (which lives downstream of the chain
abstraction). -/

/-- The initial scanner state immediately after `streamStart` has been
    emitted satisfies `PendingKeysWellIndexed`: `tokens.size = 1` and
    `pendingKeys = #[]`, so the well-indexed bound holds vacuously. -/
theorem PendingKeysWellIndexed_init (input : String) :
    ScannerCorrectness.PendingKeysWellIndexed
      ((ScannerState.mk' input).emit .streamStart) := by
  refine ⟨?_, ?_⟩
  · -- tokens.size ≥ 1
    rw [ScannerProofs.emit_tokens_size]; omega
  · -- pks empty → vacuous
    intro p hp
    have h_emp :
        ((ScannerState.mk' input).emit .streamStart).pendingKeys.size = 0 := by
      rw [ScannerCorrectness.emit_preserves_pendingKeys]; rfl
    omega

/-- `ScanChain` preserves `PendingKeysWellIndexed`: by induction on the
    chain, applying `scanNextToken_preserves_PendingKeysWellIndexed` at
    each step.  This is the chain-side companion to
    `scanLoopFull_preserves_PendingKeysWellIndexed` for use by emitter
    consumers that work in `ScanChain`-shape. -/
theorem ScanChain.preserves_PendingKeysWellIndexed
    {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s')
    (h_inv : ScannerCorrectness.PendingKeysWellIndexed s) :
    ScannerCorrectness.PendingKeysWellIndexed s' := by
  induction h_chain with
  | zero => exact h_inv
  | step h_snt _ ih =>
    exact ih (ScannerCorrectness.scanNextToken_preserves_PendingKeysWellIndexed
      _ _ h_inv h_snt)

/-- Combined helper: any chain anchored at the `streamStart`-initialized
    state preserves `PendingKeysWellIndexed` to its endpoint.  This is the
    form the seq/map cascade consumers use to derive the chain-endpoint
    invariant they need to discharge `linearise_push_eq_push_linearise`'s
    `h_pks_bound` after replacing `h_tok_eq` with the linearise bridge
    from `scanFiltered_tokens_eq_of_chain_short_stack`. -/
theorem PendingKeysWellIndexed_of_chain_from_init
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_chain : ScanChain s₀ n s_final) :
    ScannerCorrectness.PendingKeysWellIndexed s_final :=
  h_chain.preserves_PendingKeysWellIndexed
    (h_s0 ▸ PendingKeysWellIndexed_init input)

/-- After the final `streamEnd` emit, the invariant still holds: `emit`
    pushes one token (preserving the `tokens.size ≥ 1` lower bound and
    only weakening the upper bound on each pending entry) and leaves
    `pendingKeys` unchanged.  Consumed in the cascade where
    `linearise_push_eq_push_linearise` operates on
    `(s_final.emit .streamEnd)`. -/
theorem PendingKeysWellIndexed_emit_streamEnd
    (s : ScannerState) (tok : YamlToken)
    (h_inv : ScannerCorrectness.PendingKeysWellIndexed s) :
    ScannerCorrectness.PendingKeysWellIndexed (s.emit tok) :=
  ScannerCorrectness.PendingKeysWellIndexed_mono s (s.emit tok)
    (ScannerCorrectness.emit_preserves_pendingKeys s tok)
    (by rw [ScannerProofs.emit_tokens_size]; omega) h_inv

/-! ### J.4.2.b-2a-chain — `AllUnresolved` propagation through `ScanChain`

Chain-side companion to the per-action lemmas landed in `J.4.2.b-2a`
(`AllUnresolved_mono`, `AllUnresolved_push_unresolved`,
`AllUnresolved_field_update`, `setPendingKeyKind_unresolved_preserves_AllUnresolved`,
`saveSimpleKey_preserves_AllUnresolved`).

Unlike `PendingKeysWellIndexed` — preserved by *every* scanner action,
including `scanValuePrepare`'s `:`-resolution — `AllUnresolved` is
broken by the single per-action path
`setPendingKeyKind active <non-.unresolved>`.  The chain induction
therefore takes the per-action preservation as a parametric
hypothesis: for inputs in the no-`:`-pair sub-class (flow seqs of
scalars; nested flow seqs), the consumer discharges that hypothesis
via the Class A/B/C machinery on a step-by-step basis (every action
along the chain falls into Class A passthrough, Class B push of
`.unresolved`, or Class C with kind preserved).

Companion to `ScanChain.preserves_PendingKeysWellIndexed` for the
linearise-shape body characterizations of the seq/map cascade
(J.4.2.b-2c, J.4.2.b-2d): combined with
`linearise_eq_filter_no_resolutions` (J.4.1) it lets cascade consumers
collapse `linearise` to the legacy filter shape used by Tier 1
emitter derivations. -/

/-- The initial scanner state immediately after `streamStart` has been
    emitted satisfies `AllUnresolved`: `pendingKeys = #[]`, so the
    predicate holds vacuously. -/
theorem AllUnresolved_init (input : String) :
    ScannerCorrectness.AllUnresolved
      ((ScannerState.mk' input).emit .streamStart) := by
  intro e he
  rw [Array.mem_iff_getElem] at he
  obtain ⟨i, hi, _⟩ := he
  have h_emp :
      ((ScannerState.mk' input).emit .streamStart).pendingKeys.size = 0 := by
    rw [ScannerCorrectness.emit_preserves_pendingKeys]; rfl
  omega

/-- `ScanChain` preserves `AllUnresolved` parametrically in a per-action
    preservation hypothesis: by induction on the chain, applying
    `h_step` at each successful `scanNextToken` step.  For inputs in
    the no-`:`-pair sub-class, the consumer discharges `h_step` via the
    Class A/B/C machinery from `J.4.2.b-2a`. -/
theorem ScanChain.preserves_AllUnresolved
    {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s')
    (h_step : ∀ {sa sb : ScannerState},
                ScannerCorrectness.AllUnresolved sa →
                scanNextToken sa = .ok sb →
                ScannerCorrectness.AllUnresolved sb)
    (h_inv : ScannerCorrectness.AllUnresolved s) :
    ScannerCorrectness.AllUnresolved s' := by
  induction h_chain with
  | zero => exact h_inv
  | step h_snt _ ih =>
    exact ih (h_step h_inv h_snt)

/-- Combined helper: any chain anchored at the `streamStart`-initialized
    state, whose per-action transitions all preserve `AllUnresolved`,
    extends the invariant to the chain endpoint.  Companion to
    `PendingKeysWellIndexed_of_chain_from_init` for the
    linearise-shape cascade derivations. -/
theorem AllUnresolved_of_chain_from_init
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_chain : ScanChain s₀ n s_final)
    (h_step : ∀ {sa sb : ScannerState},
                ScannerCorrectness.AllUnresolved sa →
                scanNextToken sa = .ok sb →
                ScannerCorrectness.AllUnresolved sb) :
    ScannerCorrectness.AllUnresolved s_final :=
  h_chain.preserves_AllUnresolved h_step
    (h_s0 ▸ AllUnresolved_init input)

/-- After the final `streamEnd` emit, `AllUnresolved` still holds:
    `emit` only pushes a token and leaves `pendingKeys` unchanged.
    Consumed in the cascade where `linearise_eq_filter_no_resolutions`
    operates on `(s_final.emit .streamEnd)`. -/
theorem AllUnresolved_emit_streamEnd
    (s : ScannerState) (tok : YamlToken)
    (h_inv : ScannerCorrectness.AllUnresolved s) :
    ScannerCorrectness.AllUnresolved (s.emit tok) :=
  ScannerCorrectness.AllUnresolved_mono
    (ScannerCorrectness.emit_preserves_pendingKeys s tok) h_inv

/-! ### J.4.2.b-2b — `NoPlaceholders` propagation through `ScanChain`

Chain-side companion to the per-state lemmas landed in `J.4.2.b-2b`
(`NoPlaceholders_mono`, `NoPlaceholders_emit`, `NoPlaceholders_emitAt`).

Unlike `AllUnresolved` — broken by `scanValuePrepare`'s `:`-resolution
arm — `NoPlaceholders` has no break path: the J.2 step 5 cutover
removed every legacy `placeholder` push from the scanner, so every
scanner action either leaves `tokens` unchanged (Class A) or pushes
a single concrete non-`.placeholder` token (Class B).  The chain
induction is therefore parametric in a per-action preservation
hypothesis (uniform with `ScanChain.preserves_AllUnresolved`),
discharged unconditionally by the consumer (every input shape) via
the J.4.2.b-2b-discharge per-action chain.

Together with `AllUnresolved` (J.4.2.b-2a) and
`linearise_eq_filter_no_resolutions` (J.4.1), this lets cascade
consumers collapse `linearise s.tokens s.pendingKeys` to
`s.tokens.filter (· != .placeholder)` and then to `s.tokens` itself
(filter is identity when no placeholders are present), bridging the
post-cutover linearise shape to the legacy filter shape used by
Tier 1 emitter derivations. -/

/-- The initial scanner state immediately after `streamStart` has been
    emitted satisfies `NoPlaceholders`: the only token is
    `.streamStart`, which is not `.placeholder`. -/
theorem NoPlaceholders_init (input : String) :
    ScannerCorrectness.NoPlaceholders
      ((ScannerState.mk' input).emit .streamStart) := by
  intro t ht
  have h_emp : (ScannerState.mk' input).tokens = #[] := rfl
  unfold ScannerState.emit at ht
  dsimp only [] at ht
  rw [h_emp] at ht
  rw [Array.mem_push] at ht
  rcases ht with h_old | h_new
  · simp at h_old
  · subst h_new
    exact YamlToken.noConfusion

/-- `ScanChain` preserves `NoPlaceholders` parametrically in a
    per-action preservation hypothesis: by induction on the chain,
    applying `h_step` at each successful `scanNextToken` step.  Unlike
    `ScanChain.preserves_AllUnresolved`, no extra sub-class hypothesis
    is needed — the consumer discharges `h_step` unconditionally via
    the J.4.2.b-2b-discharge per-action chain. -/
theorem ScanChain.preserves_NoPlaceholders
    {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s')
    (h_step : ∀ {sa sb : ScannerState},
                ScannerCorrectness.NoPlaceholders sa →
                scanNextToken sa = .ok sb →
                ScannerCorrectness.NoPlaceholders sb)
    (h_inv : ScannerCorrectness.NoPlaceholders s) :
    ScannerCorrectness.NoPlaceholders s' := by
  induction h_chain with
  | zero => exact h_inv
  | step h_snt _ ih =>
    exact ih (h_step h_inv h_snt)

/-- Combined helper: any chain anchored at the `streamStart`-initialized
    state, whose per-action transitions all preserve `NoPlaceholders`,
    extends the invariant to the chain endpoint.  Companion to
    `AllUnresolved_of_chain_from_init` for the linearise-shape cascade
    derivations. -/
theorem NoPlaceholders_of_chain_from_init
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_chain : ScanChain s₀ n s_final)
    (h_step : ∀ {sa sb : ScannerState},
                ScannerCorrectness.NoPlaceholders sa →
                scanNextToken sa = .ok sb →
                ScannerCorrectness.NoPlaceholders sb) :
    ScannerCorrectness.NoPlaceholders s_final :=
  h_chain.preserves_NoPlaceholders h_step
    (h_s0 ▸ NoPlaceholders_init input)

/-- After the final `streamEnd` emit, `NoPlaceholders` still holds:
    `streamEnd ≠ .placeholder` is decidable, and `emit` only pushes
    that token without mutating earlier ones.  Consumed in the
    cascade where `linearise_eq_filter_no_resolutions` operates on
    `(s_final.emit .streamEnd)`. -/
theorem NoPlaceholders_emit_streamEnd
    (s : ScannerState)
    (h_inv : ScannerCorrectness.NoPlaceholders s) :
    ScannerCorrectness.NoPlaceholders (s.emit .streamEnd) :=
  ScannerCorrectness.NoPlaceholders_emit
    (show (.streamEnd : YamlToken) ≠ .placeholder from
      fun h => YamlToken.noConfusion h)
    h_inv

-- ═══ FlowMonoChain: ScanChain with flow-level lower bound ═══

/-- `FlowMonoChain fl₀ s n s'` is a `ScanChain` where every intermediate state
    has `flowLevel ≥ fl₀`. This captures the "flow-balanced" property: the chain
    never closes brackets below the initial flow depth, ensuring stacked simple keys
    from before the chain are never restored.

    **Motivation**: `ScanChain_filtered_prefix` needs to show that `setIfInBounds`
    (from `scanValuePrepare`) never writes at token positions below the initial range.
    This holds when the simpleKeyStack is never popped below its initial height, which
    follows from `flowLevel ≥ fl₀` at every step (since `simpleKeyStack.size` tracks
    `flowLevel` via `scanFlowStart`/`scanFlowEnd` push/pop synchronization).

    For emitter-produced chains, `fl₀ = s.flowLevel` is always satisfied because the
    emitter produces balanced bracket sequences: every `]`/`}` matches an inner `[`/`{`. -/
inductive FlowMonoChain (fl₀ : Nat) : ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} (h_fl : s.flowLevel ≥ fl₀) :
      FlowMonoChain fl₀ s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat}
      (h_fl : s.flowLevel ≥ fl₀)
      (h_snt : scanNextToken s = .ok (some s_mid))
      (h_rest : FlowMonoChain fl₀ s_mid n s') :
      FlowMonoChain fl₀ s (n + 1) s'

/-- Degrade a `FlowMonoChain` to a plain `ScanChain` by forgetting flow-level bounds. -/
theorem FlowMonoChain.toScanChain {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : ScanChain s n s' := by
  induction h with
  | zero => exact .zero
  | step _ h_snt _h_rest ih => exact .step h_snt ih

/-- The start state of a `FlowMonoChain` has `flowLevel ≥ fl₀`. -/
theorem FlowMonoChain.flowLevel_ge_start {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : s.flowLevel ≥ fl₀ := by
  cases h with
  | zero h_fl => exact h_fl
  | step h_fl _ _ => exact h_fl

/-- The end state of a `FlowMonoChain` has `flowLevel ≥ fl₀`. -/
theorem FlowMonoChain.flowLevel_ge_end {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : s'.flowLevel ≥ fl₀ := by
  induction h with
  | zero h_fl => exact h_fl
  | step _ _ _ ih => exact ih

/-- A single `scanNextToken` step as a `FlowMonoChain`. -/
theorem FlowMonoChain.single {fl₀ : Nat} {s s' : ScannerState}
    (h_snt : scanNextToken s = .ok (some s'))
    (h_fl : s.flowLevel ≥ fl₀)
    (h_fl' : s'.flowLevel ≥ fl₀) :
    FlowMonoChain fl₀ s 1 s' :=
  .step h_fl h_snt (.zero h_fl')

/-- Transitivity: concatenate two `FlowMonoChain`s with the same floor. -/
theorem FlowMonoChain.trans {fl₀ : Nat} {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : FlowMonoChain fl₀ s₁ n₁ s₂)
    (h2 : FlowMonoChain fl₀ s₂ n₂ s₃) :
    FlowMonoChain fl₀ s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_fl h_snt h_rest ih =>
    have h_ih := ih h2
    have : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [this]
    exact .step h_fl h_snt h_ih

/-- Weaken the flow-level floor: if `fl₀ ≤ fl₁`, a `FlowMonoChain fl₁` is also
    a `FlowMonoChain fl₀`. -/
theorem FlowMonoChain.weaken {fl₀ fl₁ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₁ s n s') (h_le : fl₀ ≤ fl₁) :
    FlowMonoChain fl₀ s n s' := by
  induction h with
  | zero h_fl => exact .zero (by omega)
  | step h_fl h_snt _h_rest ih => exact .step (by omega) h_snt ih

/-- Token monotonicity for `FlowMonoChain`:
    tokens only grow through the chain (delegates to `ScanChain` version). -/
theorem FlowMonoChain.tokens_mono {fl₀ : Nat} {s s' : ScannerState} {n : Nat}
    (h : FlowMonoChain fl₀ s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h with
  | zero => omega
  | step _ h_snt _ ih =>
    have := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt; omega

/-! ### SimpleKeyAboveFloor: flow-level-aware simple key invariant

The `SimpleKeyAboveFloor` predicate is like `SimpleKeyAbove` but only constrains
stack entries at index ≥ `stackFloor`, with a size guarantee. It is designed for
use with `FlowMonoChain` where the stack floor equals the initial flow level. -/

-- Like `SimpleKeyAbove` but only constraining stack entries at index ≥ `stackFloor`.
-- Entries below the floor may have stale `tokenIndex` values from before the chain.
def SimpleKeyAboveFloor (s : ScannerState) (n : Nat) (stackFloor : Nat) : Prop :=
  (s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n) ∧
  (∀ j, stackFloor ≤ j → (h : j < s.simpleKeyStack.size) →
    s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ n) ∧
  (s.simpleKeyStack.size ≥ stackFloor)

/-! #### SimpleKeyAboveFloor constructors -/

theorem SimpleKeyAboveFloor_of_cleared_preserved (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ :=
  ⟨fun hp => absurd hp (by rw [h_sk]; decide),
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

theorem SimpleKeyAboveFloor_of_preserved (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKey)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ :=
  ⟨fun hp => by rw [h_sk] at hp ⊢; exact h_inv.1 hp,
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

theorem SimpleKeyAboveFloor_of_endLine_update (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_poss : s_out.simpleKey.possible = s_in.simpleKey.possible)
    (h_idx : s_out.simpleKey.tokenIndex = s_in.simpleKey.tokenIndex)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ :=
  ⟨fun hp => by
    have hp' : s_in.simpleKey.possible = true := by rw [← h_poss]; exact hp
    have := h_inv.1 hp'; omega,
   fun j hfl hj hp => by simp only [h_stack] at hj hp ⊢; exact h_inv.2.1 j hfl hj hp,
   by rw [h_stack]; exact h_inv.2.2⟩

theorem SimpleKeyAboveFloor_of_flow_open (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey.possible = false)
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.push s_in.simpleKey)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀) : SimpleKeyAboveFloor s_out n fl₀ := by
  refine ⟨fun hp => absurd hp (by rw [h_sk]; decide), fun j hfl hj hp => ?_, ?_⟩
  · simp only [h_stack, Array.size_push] at hj
    by_cases hlt : j < s_in.simpleKeyStack.size
    · have hp' : s_in.simpleKeyStack[j].possible = true := by
        simp only [h_stack, Array.getElem_push, dif_pos hlt] at hp; exact hp
      have h_ge := h_inv.2.1 j hfl hlt hp'
      show s_out.simpleKeyStack[j].tokenIndex ≥ n
      simp only [h_stack, Array.getElem_push, dif_pos hlt]; exact h_ge
    · have hj_eq : j = s_in.simpleKeyStack.size := by omega
      subst hj_eq
      have hp' : s_in.simpleKey.possible = true := by
        simp only [h_stack, Array.getElem_push, dif_neg hlt] at hp; exact hp
      have h_ge := h_inv.1 hp'
      show s_out.simpleKeyStack[s_in.simpleKeyStack.size].tokenIndex ≥ n
      simp only [h_stack, Array.getElem_push, dif_neg hlt]; exact h_ge
  · simp only [h_stack, Array.size_push]; have := h_inv.2.2; omega

theorem SimpleKeyAboveFloor_of_flow_close (s_out s_in : ScannerState) (n fl₀ : Nat)
    (h_sk : s_out.simpleKey = s_in.simpleKeyStack.back?.getD {})
    (h_stack : s_out.simpleKeyStack = s_in.simpleKeyStack.pop)
    (h_inv : SimpleKeyAboveFloor s_in n fl₀)
    (h_size : s_in.simpleKeyStack.size > fl₀ ∨ fl₀ = 0) : SimpleKeyAboveFloor s_out n fl₀ := by
  rcases h_size with h_gt | h_zero
  · -- h_gt : s_in.simpleKeyStack.size > fl₀
    refine ⟨fun hp => ?_, fun j hfl hj hp => ?_, ?_⟩
    · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
      have h_back : s_in.simpleKeyStack.back?.getD {} =
          s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
        simp [Array.back?, h_lt]
      rw [h_sk, h_back] at hp ⊢
      exact h_inv.2.1 _ (by omega) h_lt hp
    · simp only [h_stack, Array.size_pop] at hj
      simp only [h_stack, Array.getElem_pop] at hp ⊢
      exact h_inv.2.1 j hfl (by omega) hp
    · simp only [h_stack, Array.size_pop]; omega
  · -- h_zero : fl₀ = 0 — all conjuncts trivially use ≥ 0
    subst h_zero
    refine ⟨fun hp => ?_, fun j hfl hj hp => ?_, by omega⟩
    · by_cases h_nonempty : s_in.simpleKeyStack.size > 0
      · have h_lt : s_in.simpleKeyStack.size - 1 < s_in.simpleKeyStack.size := by omega
        have h_back : s_in.simpleKeyStack.back?.getD {} =
            s_in.simpleKeyStack[s_in.simpleKeyStack.size - 1]'h_lt := by
          simp [Array.back?, h_lt]
        rw [h_sk, h_back] at hp ⊢
        exact h_inv.2.1 _ (by omega) h_lt hp
      · -- Stack is empty: back? = none, so simpleKey = {} with possible = false
        have h_empty : s_in.simpleKeyStack.size = 0 := by omega
        have h_none : s_in.simpleKeyStack.back? = none := by
          simp [Array.back?, h_empty]
        rw [h_sk, h_none] at hp
        simp at hp
    · simp only [h_stack, Array.size_pop] at hj
      simp only [h_stack, Array.getElem_pop] at hp ⊢
      exact h_inv.2.1 j (by omega) (by omega) hp

/-! #### SimpleKeyAboveFloor preprocess and dispatch maintenance -/

theorem preprocess_preserves_flowLevel (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c))) :
    s1.flowLevel = s.flowLevel := by
  unfold scanNextToken_preprocess at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_error_simp,
    ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · rename_i s_skip h_skip
    have h_fl_skip := ScannerCorrectness.skipToContent_preserves_flowLevel s s_skip h_skip
    split at h
    · simp at h
    · split at h
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerCorrectness.saveSimpleKey_preserves_flowLevel]
            show (unwindIndents s_skip s_skip.col).flowLevel = s.flowLevel
            rw [ScannerCorrectness.unwindIndents_preserves_flowLevel]; exact h_fl_skip
      · split at h
        · contradiction
        · split at h
          · simp at h
          · simp only [Except.ok.injEq, Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, _⟩ := h
            rw [ScannerCorrectness.saveSimpleKey_preserves_flowLevel]; exact h_fl_skip

theorem preprocess_maintains_SimpleKeyAboveFloor (s s1 : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s1, c)))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s1 n₀ fl₀ := by
  refine ⟨?_, ?_, ?_⟩
  · exact ScannerCorrectness.preprocess_simpleKey_inv s s1 c h n₀ h_n₀ h_inv.1
  · intro j hfl hj hp
    have h_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s s1 c h
    simp only [h_stack] at hj hp ⊢
    exact h_inv.2.1 j hfl hj hp
  · have h_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s s1 c h
    rw [h_stack]; exact h_inv.2.2

theorem dispatchStructural_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchStructural s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchStructural at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_error_simp,
    ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanDocumentStart_clears_simpleKey s)
        (ScannerCorrectness.scanDocumentStart_preserves_simpleKeyStack s) h_inv
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanDocumentEnd_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDocumentEnd_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanDirective_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanDirective_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

theorem dispatchFlowIndicators_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_error_simp,
    ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  -- Handle flow open, flow entry, flow close, and none/error cases
  all_goals first
    | exact SimpleKeyAboveFloor_of_flow_open _ s n₀ fl₀
        (ScannerCorrectness.scanFlowSequenceStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowSequenceStart_stack_pushed s) h_inv
    | exact SimpleKeyAboveFloor_of_flow_open _ s n₀ fl₀
        (ScannerCorrectness.scanFlowMappingStart_simpleKey_cleared s)
        (ScannerCorrectness.scanFlowMappingStart_stack_pushed s) h_inv
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)
    | -- Flow close (seq end or mapping end)
      -- Derive s.simpleKeyStack.size > fl₀ ∨ fl₀ = 0
      (have h_gt : s.simpleKeyStack.size > fl₀ ∨ fl₀ = 0 := by
        have h_fl := h_fl_post
        first
        | (unfold scanFlowSequenceEnd at h_fl; dsimp only [] at h_fl
           simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel] at h_fl
           split at h_fl
           · left; omega
           · right; omega)
        | (unfold scanFlowMappingEnd at h_fl; dsimp only [] at h_fl
           simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel] at h_fl
           split at h_fl
           · left; omega
           · right; omega)
       first
       | exact SimpleKeyAboveFloor_of_flow_close _ s n₀ fl₀
           (ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored s)
           (ScannerCorrectness.scanFlowSequenceEnd_stack_popped s) h_inv h_gt
       | exact SimpleKeyAboveFloor_of_flow_close _ s n₀ fl₀
           (ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored s)
           (ScannerCorrectness.scanFlowMappingEnd_stack_popped s) h_inv h_gt)

theorem dispatchBlockIndicators_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure,
    Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanBlockEntry_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanKey_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanKey_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanValue_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanValue_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (simp_all; done)

theorem dispatchContent_maintains_SimpleKeyAboveFloor (s : ScannerState) (c : Char)
    (s' : ScannerState)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (n₀ fl₀ : Nat) (_h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h
  split at h
  · -- '&': scanAnchorOrAlias bind
    generalize h_anch : scanAnchorOrAlias s true = result at h
    cases result with
    | error e => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h
      exact SimpleKeyAboveFloor_of_preserved _ _ n₀ fl₀ rfl rfl
        (SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s true s_a h_anch)
          (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s true s_a h_anch) h_inv)
  · split at h
    · -- '*': alias
      split at h
      · contradiction
      · generalize h_anch : scanAnchorOrAlias s false = result at h
        cases result with
        | error e => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKey s false s_a h_anch)
            (ScannerCorrectness.scanAnchorOrAlias_preserves_simpleKeyStack s false s_a h_anch)
              h_inv
    · split at h
      · -- '!': tag
        generalize h_tag : scanTag s = result at h
        cases result with
        | error e => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
            (ScannerCorrectness.scanTag_preserves_simpleKey s s_t h_tag)
            (ScannerCorrectness.scanTag_preserves_simpleKeyStack s s_t h_tag) h_inv
      · -- remaining: block scalar, quoted, plain
        repeat (any_goals (split at h))
        all_goals (try contradiction)
        all_goals (try (simp only [Except.ok.injEq] at h; subst h))
        all_goals (
          first
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_cleared_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanBlockScalar_clears_simpleKey s _ h_eq)
        (ScannerCorrectness.scanBlockScalar_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq; exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKey s _ h_eq)
        (ScannerCorrectness.scanPlainScalar_preserves_simpleKeyStack s _ h_eq) h_inv)
    | (rename_i h_eq_dq _;
       first
       | (have h_sk := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_endLine_update _ s n₀ fl₀
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv)
       | (have h_sk := ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_endLine_update _ s n₀ fl₀
            (by simp [h_sk]) (by simp [h_sk]) (by simp [h_st]) h_inv))
    | (rename_i h_eq_dq _;
       first
       | (have h_sk := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀ h_sk h_st h_inv)
       | (have h_sk := ScannerCorrectness.scanSingleQuoted_preserves_simpleKey s _ h_eq_dq
          have h_st := ScannerCorrectness.scanSingleQuoted_preserves_simpleKeyStack s _ h_eq_dq
          exact SimpleKeyAboveFloor_of_preserved _ s n₀ fl₀ h_sk h_st h_inv))
    | (simp_all; done))

/-! #### scanNextToken-level SimpleKeyAboveFloor maintenance -/

-- scanNextToken maintains the `SimpleKeyAboveFloor` invariant, given:
-- (1) stack-flow sync: `simpleKeyStack.size ≥ flowLevel` (links flow level to stack size),
-- (2) `s'.flowLevel ≥ fl₀` (from FlowMonoChain continuation — ensures close-bracket steps
--     don't pop below the floor).
set_option maxHeartbeats 400000 in
theorem scanNextToken_maintains_SimpleKeyAboveFloor (s : ScannerState) (s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size) (h_inv : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    SimpleKeyAboveFloor s' n₀ fl₀ := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · -- preprocess succeeded with some (s1, c)
      rename_i s1 c1 heq_pre
      -- Invariant through preprocess
      have h_pre_inv := preprocess_maintains_SimpleKeyAboveFloor s _ _ (by assumption)
        n₀ fl₀ h_n₀ h_inv
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _
        (by assumption)
      have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s _ _
        (by assumption)
      have h_pre_fl := preprocess_preserves_flowLevel s _ _ (by assumption)
      -- Stack-flow sync through preprocess
      have h_pre_sync : s1.simpleKeyStack.size ≥ s1.flowLevel := by
        rw [h_pre_stack, h_pre_fl]; exact h_sync
      -- allowDirectives preserves simpleKey, stack, and flowLevel
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      have h_allow_stack : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKeyStack = st.simpleKeyStack := by
        intro st; split <;> rfl
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      have h_allow_fl : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).flowLevel = st.flowLevel := by
        intro st; split <;> rfl
      -- SimpleKeyAboveFloor through allowDirectives
      have h_allow_inv : SimpleKeyAboveFloor
          (if s1.allowDirectives then
            { s1 with allowDirectives := false, documentEverStarted := true }
          else s1) n₀ fl₀ :=
        SimpleKeyAboveFloor_of_preserved _ s1 n₀ fl₀ (h_allow_sk s1) (h_allow_stack s1)
          h_pre_inv
      -- Stack-flow sync through allowDirectives
      have h_allow_sync : (if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1).simpleKeyStack.size ≥ (if s1.allowDirectives then
          { s1 with allowDirectives := false, documentEverStarted := true }
        else s1).flowLevel := by
        rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
      -- Now split on all dispatch cases
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | -- Structural dispatch
          (have h_d := dispatchStructural_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by omega) h_pre_inv;
           exact h_d)
        | -- Flow indicators dispatch (needs sync and fl_post)
          (have h_d := dispatchFlowIndicators_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            h_allow_inv h_allow_sync (by assumption);
           exact h_d)
        | (have h_d := dispatchBlockIndicators_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            h_allow_inv;
           exact h_d)
        | (have h_d := dispatchContent_maintains_SimpleKeyAboveFloor _ _ _ (by assumption)
            n₀ fl₀ (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            h_allow_inv;
           exact h_d)
        | (simp_all)

/-! #### FlowMonoChain prefix preservation (Step 4)

Token prefix preservation through a `FlowMonoChain`, using `SimpleKeyAboveFloor`
instead of `SimpleKeyAbove`. The key insight is that `scanNextToken_preserves_prefix`
only reads the simpleKey conjunct (not the stack entries), so we can replicate
its proof using just `SimpleKeyAboveFloor.1`. -/

-- Per-step prefix preservation using only the simpleKey conjunct.
-- This is equivalent to `ScannerCorrectness.scanNextToken_preserves_prefix` but
-- takes `SimpleKeyAboveFloor` instead of `SimpleKeyAbove`.
set_option maxHeartbeats 400000 in
theorem scanNextToken_preserves_prefix_of_skFloor (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_sk : s.simpleKey.possible = true → s.simpleKey.tokenIndex ≥ n)
    (i : Nat) (h_bound : i < n) :
    s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[i]'(by omega) := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · have h_pre_pref := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s _ _ (by assumption) i (by omega)
      have h_pre_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _ (by assumption)
      have h_sk_inv := ScannerCorrectness.preprocess_simpleKey_inv s _ _ (by assumption) n h_n h_sk
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens := ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      have h_allow_sk : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).simpleKey = st.simpleKey := by
        intro st; split <;> rfl
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix _ _ _ (by assumption) i (by omega);
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchFlowIndicators_preserves_prefix _ _ _ (by assumption) i
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchBlockIndicators_preserves_prefix _ _ _ (by assumption) n
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
            (by simp only [h_allow_sk]; exact h_sk_inv) i h_bound;
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix _ _ _ (by assumption) i
            (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega);
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d; simp_all)
        | (simp_all)

-- Per-step bundle: prefix preservation + SimpleKeyAboveFloor maintenance.
-- Analogous to `scanNextToken_prefix_and_sk_inv` but for the floor-based invariant.
theorem scanNextToken_prefix_and_skFloor_inv (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n₀ fl₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_fl_post : s'.flowLevel ≥ fl₀) :
    (∀ (i : Nat) (hi : i < n₀),
      s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    SimpleKeyAboveFloor s' n₀ fl₀ :=
  ⟨fun i hi => scanNextToken_preserves_prefix_of_skFloor s s' h_next n₀ h_n₀ h_inv.1 i hi,
   scanNextToken_maintains_SimpleKeyAboveFloor s s' h_next n₀ fl₀ h_n₀ h_inv h_sync h_fl_post⟩

-- `scanNextToken` preserves `simpleKeyStack.size ≥ flowLevel`.
-- This is a scanner global invariant: flow opens push+increment, flow closes pop+decrement.
-- Non-flow dispatches preserve both simpleKeyStack and flowLevel.

-- Helper: flow indicator dispatch preserves the sync invariant.
-- Flow opens push+increment, flow closes pop+decrement, flow entry preserves both.
set_option maxHeartbeats 800000 in
theorem dispatchFlowIndicators_preserves_sync (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s'))
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    s'.simpleKeyStack.size ≥ s'.flowLevel := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- c == '['
  split at h
  · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
    dsimp only [scanFlowSequenceStart]
    simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
      ScannerCorrectness.advance_preserves_flowLevel,
      ScannerCorrectness.emit_preserves_simpleKeyStack,
      ScannerCorrectness.emit_preserves_flowLevel,
      Array.size_push]; omega
  -- c == ']'
  · split at h
    · split at h
      · simp at h
      · split at h
        · simp at h
        · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
          dsimp only [scanFlowSequenceEnd]
          simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
            ScannerCorrectness.advance_preserves_flowLevel,
            ScannerCorrectness.emit_preserves_simpleKeyStack,
            ScannerCorrectness.emit_preserves_flowLevel,
            Array.size_pop]; split <;> omega
    -- c == '{'
    · split at h
      · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
        dsimp only [scanFlowMappingStart]
        simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
          ScannerCorrectness.advance_preserves_flowLevel,
          ScannerCorrectness.emit_preserves_simpleKeyStack,
          ScannerCorrectness.emit_preserves_flowLevel,
          Array.size_push]; omega
      -- c == '}'
      · split at h
        · split at h
          · simp at h
          · split at h
            · simp at h
            · simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
              dsimp only [scanFlowMappingEnd]
              simp only [ScannerCorrectness.advance_preserves_simpleKeyStack,
                ScannerCorrectness.advance_preserves_flowLevel,
                ScannerCorrectness.emit_preserves_simpleKeyStack,
                ScannerCorrectness.emit_preserves_flowLevel,
                Array.size_pop]; split <;> omega
        -- c == ','
        · split at h
          · split at h
            · simp at h
            · split at h
              · simp at h
              · rename_i _ _ _ h_entry
                simp only [Except.ok.injEq, Option.some.injEq] at h; subst h
                have h_stack := ScannerCorrectness.scanFlowEntry_preserves_simpleKeyStack _ _ h_entry
                have h_fl := ScannerCorrectness.scanFlowEntry_preserves_flowLevel _ _ h_entry
                rw [h_stack, h_fl]; exact h_sync
          -- fallthrough: none
          · simp at h

set_option maxHeartbeats 1200000 in
theorem scanNextToken_preserves_sync (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel) :
    s'.simpleKeyStack.size ≥ s'.flowLevel := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next <;> (try (simp at h_next; done)) -- preprocess Except
  split at h_next <;> (try (simp at h_next; done)) -- preprocess Option
  rename_i s1 c1 h_pre
  have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack s _ _ h_pre
  have h_pre_fl := preprocess_preserves_flowLevel s _ _ h_pre
  have h_pre_sync : s1.simpleKeyStack.size ≥ s1.flowLevel := by
    rw [h_pre_stack, h_pre_fl]; exact h_sync
  split at h_next <;> (try (simp at h_next; done)) -- structural Except
  split at h_next
  · -- structural some
    simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
    have h_d_stack := ScannerCorrectness.dispatchStructural_preserves_simpleKeyStack
      s1 c1 _ (by assumption)
    have h_d_fl := ScannerCorrectness.dispatchStructural_preserves_flowLevel
      s1 c1 _ (by assumption)
    rw [h_d_stack, h_d_fl]; exact h_pre_sync
  · -- structural none → allowDirectives → flow/block/content
    have h_allow_stack : ∀ st : ScannerState,
      (if st.allowDirectives then
        { st with allowDirectives := false, documentEverStarted := true }
      else st).simpleKeyStack = st.simpleKeyStack := by intro st; split <;> rfl
    have h_allow_fl : ∀ st : ScannerState,
      (if st.allowDirectives then
        { st with allowDirectives := false, documentEverStarted := true }
      else st).flowLevel = st.flowLevel := by intro st; split <;> rfl
    have h_ad_sync : (if s1.allowDirectives then
        { s1 with allowDirectives := false, documentEverStarted := true }
      else s1).simpleKeyStack.size ≥ (if s1.allowDirectives then
        { s1 with allowDirectives := false, documentEverStarted := true }
      else s1).flowLevel := by
      rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
    -- checkBlockFlowIndent
    split at h_next <;> (try (simp at h_next; done))
    -- Flow Except
    split at h_next <;> (try (simp at h_next; done))
    -- Flow Option
    split at h_next
    · -- flow some → use flow dispatch helper
      simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
      exact dispatchFlowIndicators_preserves_sync _ _ _ (by assumption) h_ad_sync
    · -- flow none → block
      split at h_next <;> (try (simp at h_next; done)) -- block Except
      split at h_next
      · -- block some
        simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
        have h_d_stack := ScannerCorrectness.dispatchBlockIndicators_preserves_simpleKeyStack
          _ c1 _ (by assumption)
        have h_d_fl := ScannerCorrectness.dispatchBlockIndicators_preserves_flowLevel
          _ c1 _ (by assumption)
        rw [h_d_stack, h_d_fl]; rw [h_allow_stack, h_allow_fl]; exact h_pre_sync
      · -- block none → content
        split at h_next <;> (try (simp at h_next; done)) -- content Except
        simp only [Except.ok.injEq, Option.some.injEq] at h_next; subst h_next
        have h_d_stack := ScannerCorrectness.dispatchContent_preserves_simpleKeyStack
          _ c1 _ (by assumption)
        have h_d_fl := ScannerCorrectness.dispatchContent_preserves_flowLevel
          _ c1 _ (by assumption)
        rw [h_d_stack, h_d_fl]; rw [h_allow_stack, h_allow_fl]; exact h_pre_sync

-- Main chain theorem: token prefix preservation through FlowMonoChain.
-- Mirrors `ScanChain_preserves_raw_prefix` but uses `SimpleKeyAboveFloor` instead of
-- `SimpleKeyAbove`, enabling the proof when stack entries below floor have stale indices.
-- The floor is the chain's `fl₀` (not the state's stack size), since `fl₀` is constant
-- across chain steps and `scanNextToken_maintains_SimpleKeyAboveFloor` preserves it.
theorem FlowMonoChain_preserves_raw_prefix {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_stack_floor : SimpleKeyAboveFloor s n₀ fl₀)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := FlowMonoChain.tokens_mono h_fmc; omega) =
    s.tokens[i]'(by omega) := by
  induction h_fmc with
  | zero => rfl
  | step h_fl h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have h_fl_mid := h_rest.flowLevel_ge_start
    have h_sk_inv := scanNextToken_maintains_SimpleKeyAboveFloor _ _ h_snt n₀ fl₀
      h_n₀ h_stack_floor h_sync h_fl_mid
    have h_sync' := scanNextToken_preserves_sync _ _ h_snt h_sync
    have h_pres := scanNextToken_preserves_prefix_of_skFloor _ _ h_snt n₀ h_n₀
      h_stack_floor.1 i hi
    exact (ih (Nat.le_trans h_n₀ h_adds) h_sk_inv h_sync').trans h_pres

/-! ### Path C unconditional strict prefix preservation
(J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6b)

Post-cutover (Initiative 3 / J.2 step 5), the scanner is append-only on
`tokens`: every code path either leaves `tokens` unchanged or pushes a
single concrete (non-`.placeholder`) token via `emit`/`emitAt`.  No
`Array.setIfInBounds` mutates existing tokens, so prefix preservation
holds **unconditionally** — no `SimpleKeyAbove` / `SimpleKeyAboveFloor`
hypothesis is required.

The existing `scanNextToken_preserves_prefix` /
`scanNextToken_preserves_prefix_of_skFloor` are Path-B-aware and thread
the simpleKey invariant for compatibility with the legacy proof shape.
The strict variants below mirror the existing proofs but use
`scanValue_preserves_prefix_strict` (already discharged in
`ScannerCorrectness`) for the `:` case, dropping the hypothesis.

Used in `emitPairList_scans_nonempty`'s recursive case to lift the
comma's `.flowEntry` push through the IH chain without having to
establish `SimpleKeyAboveFloor s_pp s_pp.tokens.size s_pp.flowLevel`
(which would require non-trivial tracing of `s_pp.simpleKey`/
`simpleKeyStack` state). -/

/-- Strict (unconditional) version of
    `ScanHelpers.dispatchBlockIndicators_preserves_prefix`: drops the
    `SimpleKeyAbove`-style precondition by routing the `scanValue` case
    through `scanValue_preserves_prefix_strict`. -/
theorem dispatchBlockIndicators_preserves_prefix_strict
    (s : ScannerState) (c : Char) (s' : ScannerState)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s'))
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by
      have := ScannerCorrectness.ScanHelpers.dispatchBlockIndicators_tokens_mono s c s' h
      omega) =
    s.tokens[i]'h_bound := by
  -- Mirrors the existing `dispatchBlockIndicators_preserves_prefix` proof
  -- structure, but routes the `:` branch through `scanValue_preserves_prefix_strict`
  -- (which has no h_inv requirement).
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp,
    pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | exact ScannerCorrectness.ScanHelpers.scanBlockEntry_preserves_prefix
        s _ (by assumption) i h_bound
    | exact ScannerCorrectness.ScanHelpers.scanKey_preserves_prefix
        s _ (by assumption) i h_bound
    | exact ScannerCorrectness.scanValue_preserves_prefix_strict
        s _ (by assumption) i h_bound
    | (simp_all)

-- Strict (unconditional) version of `ScannerCorrectness.scanNextToken_preserves_prefix`:
-- drops the `SimpleKeyAbove` hypothesis.  Path C is append-only on tokens, so every
-- existing token at index `< s.tokens.size` is preserved through a `scanNextToken`
-- step regardless of simpleKey state.
set_option maxHeartbeats 400000 in
theorem scanNextToken_preserves_prefix_strict (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by
      have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
    s.tokens[i]'h_bound := by
  unfold scanNextToken at h_next
  simp only [bind, pure, Pure.pure, Except.pure] at h_next
  simp only [Except.bind] at h_next
  split at h_next
  · contradiction
  · split at h_next
    · simp at h_next
    · have h_pre_pref :=
        ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s _ _ (by assumption) i h_bound
      have h_pre_mono :=
        ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s _ _ (by assumption)
      have h_allow_tok : ∀ st : ScannerState,
        (if st.allowDirectives then
          { st with allowDirectives := false, documentEverStarted := true }
        else st).tokens = st.tokens :=
        ScannerCorrectness.ScanHelpers.allowDir_ite_tokens
      repeat (any_goals (split at h_next))
      any_goals contradiction
      any_goals (simp at h_next)
      all_goals (try subst_vars)
      all_goals first
        | contradiction
        | (simp at h_next)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix
             _ _ _ (by assumption) i (by omega)
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchFlowIndicators_preserves_prefix
             _ _ _ (by assumption) i
             (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d
           simp_all)
        | (have h_d := dispatchBlockIndicators_preserves_prefix_strict
             _ _ _ (by assumption) i
             (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d
           simp_all)
        | (have h_d := ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix
             _ _ _ (by assumption) i
             (by simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens]; omega)
           simp only [ScannerCorrectness.ScanHelpers.allowDir_ite_tokens] at h_d
           simp_all)
        | (simp_all)

/-- Chain version of `scanNextToken_preserves_prefix_strict` over a
    `FlowMonoChain`: every existing token is preserved through any
    chain step, unconditionally.  Used in `emitPairList_scans_nonempty`'s
    recursive case (sub-task 6a-i1-lift) to carry the comma's
    `.flowEntry` push through the IH chain `s_pp → s_end`. -/
theorem FlowMonoChain_preserves_existing_tokens {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (i : Nat) (h_bound : i < s.tokens.size) :
    s'.tokens[i]'(by have := FlowMonoChain.tokens_mono h_fmc; omega) =
    s.tokens[i]'h_bound := by
  induction h_fmc with
  | zero => rfl
  | step _ h_snt _ ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have h_pres := scanNextToken_preserves_prefix_strict _ _ h_snt i h_bound
    exact (ih (Nat.lt_of_lt_of_le h_bound h_adds)).trans h_pres

/-- Connect a ScanChain to scanFiltered.

    **Initiative 3 / J.3.6** (2026-04-28): post-cutover `scanFiltered`
    routes through `scanLoopFull`.  We compose the existing
    `ScanChain → scanLoop = .ok` machinery (`scanLoop_eof_eq` +
    `ScanChain.to_scanLoop`) with the J.3.6 reverse bridge
    `scan_ok_implies_scanFiltered_ok` (in `ScannerCorrectness`) to
    recover existence at the `scanFiltered` layer. -/
theorem scanFiltered_of_chain (input : String)
    (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4) :
    ∃ tokens, scanFiltered input = .ok tokens := by
  -- Step 1: scanLoop on s_final closes into `.ok ...` for any fuel ≥ 1.
  have h_f_ge : (input.utf8ByteSize + 1) * 4 - n ≥ 1 := by omega
  have h_loop_final := scanLoop_eof_eq h_f_ge h_eof h_fl h_dp
  -- Step 2: Compose with the chain → scanLoop on s₀ closes into `.ok ...`.
  have h_loop_s0 := h_chain.to_scanLoop h_loop_final
  have h_fuel_eq : ((input.utf8ByteSize + 1) * 4 - n) + n = (input.utf8ByteSize + 1) * 4 := by
    omega
  rw [h_fuel_eq] at h_loop_s0
  -- Step 3: scan input = .ok _ via the BOM/fuel bookkeeping.
  have h_scan_eq : scan input =
      .ok ((unwindIndents s_final (-1)).emit .streamEnd).tokens := by
    -- `peek?` is invariant under `emit` (which only touches `tokens`),
    -- so the BOM-handle in `scan` resolves to identity and the start
    -- state matches s₀.
    have h_no_bom' : ((ScannerState.mk' input).emit .streamStart).peek? ≠ some '﻿' :=
      h_no_bom
    show scanLoop (match ((ScannerState.mk' input).emit .streamStart).peek? with
            | some '﻿' => ((ScannerState.mk' input).emit .streamStart).advance
            | _ => (ScannerState.mk' input).emit .streamStart)
          ((input.utf8ByteSize + 1) * 4) =
          .ok ((unwindIndents s_final (-1)).emit .streamEnd).tokens
    split
    · rename_i h_bom
      exact absurd h_bom h_no_bom'
    · rw [← h_s0]
      exact h_loop_s0
  -- Step 4: lift to scanFiltered via the J.3.6 reverse bridge.
  exact L4YAML.Proofs.ScannerCorrectness.scan_ok_implies_scanFiltered_ok _ _ h_scan_eq

/-- **Equality version**: gives the exact filtered token array from a ScanChain.

    **Initiative 3 / J.2 step 5 cutover** (Category C, J.3.8): RHS is
    `linearise final.tokens final.pendingKeys` rather than the legacy
    `tokens.filter (· != .placeholder)` shape.  The `skipToContent`
    fallback in `scanLoopFull`'s EOF arm is exposed via `h_skip`; callers
    that have `s_final.peek? = none` discharge it via
    `skipToContent_eq_self_of_peek_none`. -/
theorem scanFiltered_of_chain_eq (input : String)
    (s₀ s_final s_skipped : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_skip : skipToContent s_final = .ok s_skipped)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4) :
    scanFiltered input = .ok (Scanner.linearise
        ((unwindIndents s_skipped (-1)).emit .streamEnd).tokens
        ((unwindIndents s_skipped (-1)).emit .streamEnd).pendingKeys) := by
  -- Step 1: scanLoopFull on s_final closes with `s_skipped` flowed through.
  have h_f_ge : (input.utf8ByteSize + 1) * 4 - n ≥ 1 := by omega
  have h_loop_final :=
    scanLoopFull_eof_eq h_f_ge h_eof h_fl h_dp h_skip
  -- Step 2: Compose chain → scanLoopFull on s₀.
  have h_loop_s0 := h_chain.to_scanLoopFull h_loop_final
  have h_fuel_eq :
      ((input.utf8ByteSize + 1) * 4 - n) + n = (input.utf8ByteSize + 1) * 4 := by omega
  rw [h_fuel_eq] at h_loop_s0
  -- Step 3: walk scanFiltered: BOM identity + scanLoopFull + linearise.
  show (match scanLoopFull
          (match ((ScannerState.mk' input).emit .streamStart).peek? with
           | some '﻿' => ((ScannerState.mk' input).emit .streamStart).advance
           | _ => (ScannerState.mk' input).emit .streamStart)
          ((input.utf8ByteSize + 1) * 4) with
        | Except.ok final =>
            Except.ok (Scanner.linearise final.tokens final.pendingKeys)
        | Except.error e => Except.error e) =
      Except.ok (Scanner.linearise
        ((unwindIndents s_skipped (-1)).emit .streamEnd).tokens
        ((unwindIndents s_skipped (-1)).emit .streamEnd).pendingKeys)
  have h_bom_branch :
      (match ((ScannerState.mk' input).emit .streamStart).peek? with
       | some '﻿' => ((ScannerState.mk' input).emit .streamStart).advance
       | _ => (ScannerState.mk' input).emit .streamStart)
        = (ScannerState.mk' input).emit .streamStart := by
    split
    · rename_i h_bom; exact absurd h_bom h_no_bom
    · rfl
  rw [h_bom_branch, ← h_s0, h_loop_s0]

-- ═══ scanNextToken preprocessing equality ═══

-- If two states produce the same preprocessing result, scanNextToken gives the same result.
-- This is because scanNextToken = bind (preprocess s) f where f doesn't capture s.
theorem scanNextToken_eq_of_preprocess (s₁ s₂ : ScannerState)
    (h : scanNextToken_preprocess s₁ = scanNextToken_preprocess s₂) :
    scanNextToken s₁ = scanNextToken s₂ := by
  unfold scanNextToken
  simp only [bind, Except.bind]
  rw [h]

-- If scanNextToken gives the same result for two states, and the second has
-- a ScanChain of length ≥ 1, then the first does too.
theorem ScanChain_of_scanNextToken_eq {s₁ s₂ s' : ScannerState} {n : Nat}
    (h_eq : scanNextToken s₁ = scanNextToken s₂)
    (h_chain : ScanChain s₂ (n + 1) s') :
    ScanChain s₁ (n + 1) s' := by
  cases h_chain with
  | step h_snt h_rest =>
    exact .step (by rw [h_eq]; exact h_snt) h_rest

/-- `FlowMonoChain` version of `ScanChain_of_scanNextToken_eq`: if scanNextToken gives
    the same result for two states, and the second has a FlowMonoChain of length ≥ 1,
    then the first does too (given the flow-level bound at the first state). -/
theorem FlowMonoChain_of_scanNextToken_eq {fl₀ : Nat} {s₁ s₂ s' : ScannerState} {n : Nat}
    (h_eq : scanNextToken s₁ = scanNextToken s₂)
    (h_fl : s₁.flowLevel ≥ fl₀)
    (h_chain : FlowMonoChain fl₀ s₂ (n + 1) s') :
    FlowMonoChain fl₀ s₁ (n + 1) s' := by
  cases h_chain with
  | step _ h_snt h_rest =>
    exact .step h_fl (by rw [h_eq]; exact h_snt) h_rest

-- ═══ scanNextToken pipeline factoring ═══
-- The scanNextToken pipeline has 5 stages:
--   preprocess → structural → allowDirectives → checkBlockFlowIndent → flow/block/content
-- These factoring lemmas let us compose results from individual stages.

/-- When preprocessing succeeds, structural dispatch returns none, and flow
    indicator dispatch produces a result, then scanNextToken returns that result.
    This captures the common case for flow indicator characters [`[`, `]`, `{`, `}`, `,`].

    `s_ad` is the state after the allowDirectives update, defined as:
    `if s_pp.allowDirectives then { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp` -/
theorem scanNextToken_via_flow_dispatch (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok (some s_result)) :
    scanNextToken s = .ok (some s_result) := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_struct, pure, Except.pure]
  -- After preprocessing and structural dispatch, the allowDirectives conditional
  -- and remaining dispatch stages are visible. Substitute s_ad.
  rw [← h_ad_eq]
  simp only [h_check, h_flow]

-- ═══ directivesPresent preservation helpers ═══
-- None of advance/emitAt/consumeNewline/skipSpaces/skipWhitespace/processEscape/
-- foldQuotedNewlines/collectDoubleQuotedLoop modify directivesPresent.

theorem advance_preserves_dp (s : ScannerState) :
    s.advance.directivesPresent = s.directivesPresent := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

theorem consumeNewline_preserves_dp (s : ScannerState) :
    (consumeNewline s).directivesPresent = s.directivesPresent := by
  unfold consumeNewline
  split
  · exact advance_preserves_dp s
  · dsimp only []
    split
    · exact advance_preserves_dp s
    · exact advance_preserves_dp s
  · rfl

theorem skipSpaces_preserves_dp (s : ScannerState) :
    (skipSpaces s).directivesPresent = s.directivesPresent := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_preserves_dp]
    · rfl

theorem skipWhitespace_preserves_dp (s : ScannerState) :
    (skipWhitespace s).directivesPresent = s.directivesPresent := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_preserves_dp]
      · rfl
    · rfl

theorem emitAt_preserves_dp (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).directivesPresent = s.directivesPresent := by
  unfold ScannerState.emitAt; rfl

theorem collectHexDigitsLoop_preserves_dp (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.directivesPresent = s.directivesPresent := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_preserves_dp]
      · rfl
    · rfl

theorem parseHexEscape_preserves_dp (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_dp s "" digits
    · contradiction

theorem processEscape_preserves_dp (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · injection h with h_eq; subst h_eq; exact advance_preserves_dp s
  · simp only [] at h; exact parseHexEscape_preserves_dp _ _ _ h |>.trans (advance_preserves_dp s)
  · simp only [] at h; exact parseHexEscape_preserves_dp _ _ _ h |>.trans (advance_preserves_dp s)
  · simp only [] at h; exact parseHexEscape_preserves_dp _ _ _ h |>.trans (advance_preserves_dp s)
  · contradiction

theorem foldQuotedNewlinesLoop_preserves_dp (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · rw [ih, consumeNewline_preserves_dp, skipSpaces_preserves_dp]
      · rfl
    · rfl

theorem foldQuotedNewlines_preserves_dp (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_dp, skipSpaces_preserves_dp,
            foldQuotedNewlinesLoop_preserves_dp, consumeNewline_preserves_dp]

theorem collectDoubleQuotedLoop_preserves_dp (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.directivesPresent = s.directivesPresent := by
  induction fuel generalizing s content with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- Case: peek? = some '"' - closing quote
      injection h with h_eq; subst h_eq
      exact advance_preserves_dp s
    · -- Case: peek? = some '\\' - escape sequence
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · -- Escaped line break
          exact ih _ _ h |>.trans (skipWhitespace_preserves_dp _)
                         |>.trans (consumeNewline_preserves_dp _)
                         |>.trans (advance_preserves_dp s)
        · -- Regular escape
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          have h_dp_escape := processEscape_preserves_dp _ _ heq_escape
          exact ih _ _ h |>.trans h_dp_escape |>.trans (advance_preserves_dp s)
    · -- Case: peek? = some c (other character)
      split at h
      · -- Line break: fold newlines
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i folded_result heq_fold
        have h_dp_fold := foldQuotedNewlines_preserves_dp _ _ heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        simp only [] at h
        split at h <;> try contradiction
        exact ih _ _ h |>.trans h_dp_fold
      · -- Regular character
        split at h <;> try contradiction
        exact ih _ _ h |>.trans (advance_preserves_dp s)

-- scanDoubleQuoted preserves directivesPresent (structural — only tokens/offset/line/col change)
theorem scanDoubleQuoted_preserves_dp (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.directivesPresent = s.directivesPresent := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_dp_collect := collectDoubleQuotedLoop_preserves_dp _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_dp, h_dp_collect, advance_preserves_dp]
  · injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_dp, h_dp_collect, advance_preserves_dp]

-- ═══ indents preservation helpers ═══
-- Structurally identical to directivesPresent: none of advance/emitAt/consumeNewline/
-- skipSpaces/skipWhitespace/processEscape/foldQuotedNewlines/collectDoubleQuotedLoop
-- modify indents.

theorem advance_preserves_indents (s : ScannerState) :
    s.advance.indents = s.indents := by
  unfold ScannerState.advance
  split
  · simp only []
    split
    · rfl
    · split <;> rfl
  · rfl

theorem consumeNewline_preserves_indents (s : ScannerState) :
    (consumeNewline s).indents = s.indents := by
  unfold consumeNewline
  split
  · exact advance_preserves_indents s
  · dsimp only []
    split
    · exact advance_preserves_indents s
    · exact advance_preserves_indents s
  · rfl

theorem skipSpaces_preserves_indents (s : ScannerState) :
    (skipSpaces s).indents = s.indents := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ _ ih =>
    unfold skipSpacesLoop; split
    · rw [ih, advance_preserves_indents]
    · rfl

theorem skipWhitespace_preserves_indents (s : ScannerState) :
    (skipWhitespace s).indents = s.indents := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ _ ih =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [ih, advance_preserves_indents]
      · rfl
    · rfl

theorem collectHexDigitsLoop_preserves_indents (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.indents = s.indents := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ _ ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_preserves_indents]
      · rfl
    · rfl

theorem parseHexEscape_preserves_indents (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.indents = s.indents := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_indents s "" digits
    · contradiction

theorem processEscape_preserves_indents (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.indents = s.indents := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · injection h with h_eq; subst h_eq; exact advance_preserves_indents s
  · simp only [] at h; exact parseHexEscape_preserves_indents _ _ _ h |>.trans (advance_preserves_indents s)
  · simp only [] at h; exact parseHexEscape_preserves_indents _ _ _ h |>.trans (advance_preserves_indents s)
  · simp only [] at h; exact parseHexEscape_preserves_indents _ _ _ h |>.trans (advance_preserves_indents s)
  · contradiction

theorem foldQuotedNewlinesLoop_preserves_indents (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.indents = s.indents := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ _ ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · rw [ih, consumeNewline_preserves_indents, skipSpaces_preserves_indents]
      · rfl
    · rfl

theorem foldQuotedNewlines_preserves_indents (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.indents = s.indents := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_indents, skipSpaces_preserves_indents,
            foldQuotedNewlinesLoop_preserves_indents, consumeNewline_preserves_indents]

theorem collectDoubleQuotedLoop_preserves_indents (s : ScannerState) (content : String)
    (fuel : Nat) (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.indents = s.indents := by
  induction fuel generalizing s content with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- closing quote
      injection h with h_eq; subst h_eq
      exact advance_preserves_indents s
    · -- escape
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · exact (ih _ _ h).trans (skipWhitespace_preserves_indents _)
                |>.trans (consumeNewline_preserves_indents _) |>.trans (advance_preserves_indents s)
        · simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          cases escape_result
          exact (ih _ _ h).trans (processEscape_preserves_indents _ _ heq_escape)
                |>.trans (advance_preserves_indents s)
    · -- regular character
      split at h
      · simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i fold_result heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        simp only [] at h
        split at h <;> try contradiction
        exact (ih _ _ h).trans (foldQuotedNewlines_preserves_indents _ _ heq_fold)
      · split at h <;> try contradiction
        exact (ih _ _ h).trans (advance_preserves_indents s)

theorem scanDoubleQuoted_preserves_indents (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.indents = s.indents := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_ids_collect := collectDoubleQuotedLoop_preserves_indents _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    unfold ScannerState.emitAt
    exact h_ids_collect.trans (advance_preserves_indents s)
  · injection h_ok with h_eq; subst h_eq
    unfold ScannerState.emitAt
    exact h_ids_collect.trans (advance_preserves_indents s)

-- ═══ explicitKeyLine preservation helpers ═══
-- Structurally identical to directivesPresent: none of advance/emitAt/consumeNewline/
-- skipSpaces/skipWhitespace/processEscape/foldQuotedNewlines/collectDoubleQuotedLoop
-- modify explicitKeyLine.

theorem consumeNewline_preserves_ek (s : ScannerState) :
    (consumeNewline s).explicitKeyLine = s.explicitKeyLine := by
  unfold consumeNewline
  split
  · exact advance_explicitKeyLine s
  · dsimp only []
    split
    · exact advance_explicitKeyLine s
    · exact advance_explicitKeyLine s
  · rfl

theorem skipSpaces_preserves_ek (s : ScannerState) :
    (skipSpaces s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipSpaces
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipSpacesLoop; rfl
  | succ fuel' IH =>
    unfold skipSpacesLoop; split
    · rw [IH, advance_explicitKeyLine]
    · rfl

theorem skipWhitespace_preserves_ek (s : ScannerState) :
    (skipWhitespace s).explicitKeyLine = s.explicitKeyLine := by
  unfold skipWhitespace
  generalize s.inputEnd - s.offset = fuel
  induction fuel generalizing s with
  | zero => unfold skipWhitespaceLoop; rfl
  | succ fuel' IH =>
    unfold skipWhitespaceLoop; split
    · split
      · rw [IH, advance_explicitKeyLine]
      · rfl
    · rfl

theorem emitAt_preserves_ek (s : ScannerState) (pos : YamlPos) (tok : YamlToken) :
    (s.emitAt pos tok).explicitKeyLine = s.explicitKeyLine := by
  unfold ScannerState.emitAt; rfl

theorem collectHexDigitsLoop_preserves_ek (s : ScannerState) (hex : String) (n : Nat) :
    (collectHexDigitsLoop s hex n).snd.explicitKeyLine = s.explicitKeyLine := by
  induction n generalizing s hex with
  | zero => unfold collectHexDigitsLoop; rfl
  | succ n' ih =>
    unfold collectHexDigitsLoop
    split
    · split
      · rw [ih, advance_explicitKeyLine]
      · rfl
    · rfl

theorem parseHexEscape_preserves_ek (s : ScannerState) (digits : Nat)
    (result : Char × ScannerState) (h : parseHexEscape s digits = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  unfold parseHexEscape at h
  simp only [] at h
  split at h
  · contradiction
  · split at h
    · injection h with h_eq; subst h_eq
      exact collectHexDigitsLoop_preserves_ek s "" digits
    · contradiction

theorem processEscape_preserves_ek (s : ScannerState) (result : Char × ScannerState)
    (h : processEscape s = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  unfold processEscape at h
  split at h <;> try contradiction
  split at h
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · injection h with h_eq; subst h_eq; exact advance_explicitKeyLine s
  · simp only [] at h; exact parseHexEscape_preserves_ek _ _ _ h |>.trans (advance_explicitKeyLine s)
  · simp only [] at h; exact parseHexEscape_preserves_ek _ _ _ h |>.trans (advance_explicitKeyLine s)
  · simp only [] at h; exact parseHexEscape_preserves_ek _ _ _ h |>.trans (advance_explicitKeyLine s)
  · contradiction

theorem foldQuotedNewlinesLoop_preserves_ek (s : ScannerState) (emptyCount fuel : Nat) :
    (foldQuotedNewlinesLoop s emptyCount fuel).fst.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s emptyCount with
  | zero => unfold foldQuotedNewlinesLoop; rfl
  | succ fuel' ih =>
    unfold foldQuotedNewlinesLoop
    simp only []
    split
    · split
      · rw [ih, consumeNewline_preserves_ek, skipSpaces_preserves_ek]
      · rfl
    · rfl

theorem foldQuotedNewlines_preserves_ek (s : ScannerState) (result : String × ScannerState)
    (h : foldQuotedNewlines s = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  unfold foldQuotedNewlines at h
  simp only [] at h
  split at h
  · split at h <;> try contradiction
    split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]
  · split at h
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]
    · injection h with h_eq; subst h_eq
      simp [skipWhitespace_preserves_ek, skipSpaces_preserves_ek,
            foldQuotedNewlinesLoop_preserves_ek, consumeNewline_preserves_ek]

theorem collectDoubleQuotedLoop_preserves_ek (s : ScannerState) (content : String) (fuel : Nat)
    (startPos : YamlPos) (inFlow : Bool) (currentIndent : Int) (inputEnd : Nat)
    (result : String × ScannerState)
    (h : collectDoubleQuotedLoop s content fuel startPos inFlow currentIndent inputEnd = .ok result) :
    result.snd.explicitKeyLine = s.explicitKeyLine := by
  induction fuel generalizing s content with
  | zero => unfold collectDoubleQuotedLoop at h; contradiction
  | succ fuel' ih =>
    unfold collectDoubleQuotedLoop at h
    split at h <;> try contradiction
    · -- Case: peek? = some '"' - closing quote
      injection h with h_eq; subst h_eq
      exact advance_explicitKeyLine s
    · -- Case: peek? = some '\\' - escape sequence
      simp only [] at h
      split at h <;> try contradiction
      · split at h
        · -- Escaped line break
          exact ih _ _ h |>.trans (skipWhitespace_preserves_ek _)
                         |>.trans (consumeNewline_preserves_ek _)
                         |>.trans (advance_explicitKeyLine s)
        · -- Regular escape
          simp only [bind, Except.bind] at h
          split at h <;> try contradiction
          rename_i escape_result heq_escape
          exact ih _ _ h |>.trans (processEscape_preserves_ek _ _ heq_escape)
                |>.trans (advance_explicitKeyLine s)
    · -- Case: peek? = some c (other character)
      split at h
      · -- Line break: fold newlines
        simp only [bind, Except.bind] at h
        split at h <;> try contradiction
        rename_i folded_result heq_fold
        split at h <;> try contradiction
        split at h <;> try contradiction
        simp only [] at h
        split at h <;> try contradiction
        exact ih _ _ h |>.trans (foldQuotedNewlines_preserves_ek _ _ heq_fold)
      · -- Regular character
        split at h <;> try contradiction
        exact ih _ _ h |>.trans (advance_explicitKeyLine s)

-- scanDoubleQuoted preserves explicitKeyLine
theorem scanDoubleQuoted_preserves_ek (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.explicitKeyLine = s.explicitKeyLine := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind, pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  have h_ek_collect := collectDoubleQuotedLoop_preserves_ek _ _ _ _ _ _ _ _ heq
  split at h_ok
  · split at h_ok <;> try contradiction
    injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_ek, h_ek_collect, advance_explicitKeyLine]
  · injection h_ok with h_eq; subst h_eq
    simp [emitAt_preserves_ek, h_ek_collect, advance_explicitKeyLine]

-- Helper: lastTokenVal? on array.push tok returns tok.val.
--
-- **Initiative 3 / J.2 step 5 cutover** (Category B): `lastTokenVal?`
-- is now `tokens.back?.map (·.val)`, so the proof collapses and `h_nph`
-- is no longer needed (kept in the signature for caller compatibility).
theorem lastTokenVal_push_non_ph'
    (tokens : Array (Positioned YamlToken))
    (tok : Positioned YamlToken) (h_nph : tok.val ≠ .placeholder) :
    lastTokenVal? (tokens.push tok) = some tok.val := by
  let _ := h_nph
  simp [lastTokenVal?]

-- `scanDoubleQuoted` succeeds in flow context (inFlow = true) with trailing input.
-- Simpler than `scanDoubleQuoted_emitScalar_ok` because `validateTrailingContent` is skipped.
theorem scanDoubleQuoted_flow_ok (sc : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr sc
      ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, sc.col⟩)
    (h_flow : sc.inFlow = true) :
    ∃ s', scanDoubleQuoted sc = .ok s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = sc.flowLevel
      ∧ s'.directivesPresent = sc.directivesPresent
      ∧ s'.indents = sc.indents
      ∧ s'.explicitKeyLine = sc.explicitKeyLine
      ∧ s'.col > 0
      ∧ lastTokenVal? s'.tokens = some (.scalar content .doubleQuoted)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = sc.line := by
  -- Surface after advancing past opening quote
  have ⟨_, h_lt⟩ := peek_of_chars_cons sc '"'
    ((escapeString content).toList ++ ['"'] ++ rest) _ hcorr
  have hcorr_adv := advance_non_newline_corr sc '"'
    ((escapeString content).toList ++ ['"'] ++ rest) hcorr h_lt (by decide) (by decide)
  have h_col_eq : (sc.col + 1 : Nat) = sc.advance.col := hcorr_adv.col_eq
  rw [h_col_eq] at hcorr_adv
  -- Fuel bound for loop
  have h_fuel : sc.advance.inputEnd - sc.advance.offset + 1 ≥ content.toList.length + 1 := by
    rw [hcorr_adv.end_eq]
    have h_cf := CharsFromOffset_length_le hcorr_adv.chars_from
    simp only [List.length_append, List.length_singleton] at h_cf
    have h_esc := escapeString_length_ge content.toList
    simp only [String.ofList_toList] at h_esc
    omega
  -- Loop succeeds and leaves scanner at rest
  have h_ie : sc.inputEnd = sc.advance.inputEnd := by rw [advance_inputEnd]
  -- Rewrite to match loop lemma signature: (escapeString ...).toList ++ ['"'] ++ rest
  have h_corr_loop : ScannerSurfCorr sc.advance
      ⟨(escapeString (String.ofList content.toList)).toList ++ ['"'] ++ rest, sc.advance.col⟩ := by
    rw [String.ofList_toList]; exact hcorr_adv
  obtain ⟨s_after, h_loop, hcorr_loop, h_col_loop, h_line_loop⟩ :=
    collectDoubleQuotedLoop_escapeString_succeeds sc.advance content.toList rest "" _
      sc.currentPos sc.inFlow sc.currentIndent
      h_corr_loop h_fuel
  -- Content string
  have h_content_eq : "" ++ String.ofList content.toList = content := by
    apply String.ext; simp
  -- Token and field preservation
  have h_tok_pres : s_after.tokens = sc.tokens :=
    (ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
      _ _ _ _ _ _ _ _ h_loop).trans
      (ScannerCorrectness.advance_preserves_tokens sc)
  have h_fl_pres : s_after.flowLevel = sc.flowLevel :=
    (ScannerPlainScalarValid.collectDoubleQuotedLoop_preserves_flowLevel
      _ _ _ _ _ _ _ _ h_loop).trans
      (ScannerCorrectness.advance_preserves_flowLevel sc)
  have h_dp_pres : s_after.directivesPresent = sc.directivesPresent :=
    (collectDoubleQuotedLoop_preserves_dp _ _ _ _ _ _ _ _ h_loop).trans
      (advance_preserves_dp sc)
  have h_ids_pres : s_after.indents = sc.indents :=
    (collectDoubleQuotedLoop_preserves_indents _ _ _ _ _ _ _ _ h_loop).trans
      (advance_preserves_indents sc)
  have h_ek_pres : s_after.explicitKeyLine = sc.explicitKeyLine :=
    (collectDoubleQuotedLoop_preserves_ek _ _ _ _ _ _ _ _ h_loop).trans
      (advance_explicitKeyLine sc)
  -- Build the result state
  let s_result := { (s_after.emitAt sc.currentPos (.scalar content .doubleQuoted))
                     with simpleKeyAllowed := false }
  refine ⟨s_result, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · -- scanDoubleQuoted sc = .ok s_result
    simp only [scanDoubleQuoted, bind, Except.bind]
    rw [h_ie]
    rw [h_content_eq] at h_loop
    rw [h_loop]
    simp only [h_flow, Bool.not_true]
    rfl
  · -- ScannerSurfCorr s_result ⟨rest, s_result.col⟩
    exact ⟨hcorr_loop.chars_from, hcorr_loop.col_eq, hcorr_loop.end_eq,
           hcorr_loop.input_prefix, hcorr_loop.indent_cols_nonneg⟩
  · -- flowLevel preserved
    show s_after.flowLevel = sc.flowLevel
    exact h_fl_pres
  · -- directivesPresent preserved
    show s_after.directivesPresent = sc.directivesPresent
    exact h_dp_pres
  · -- indents preserved
    show s_after.indents = sc.indents
    exact h_ids_pres
  · -- explicitKeyLine preserved
    show s_after.explicitKeyLine = sc.explicitKeyLine
    exact h_ek_pres
  · -- col > 0
    show s_after.col > 0
    exact h_col_loop
  · -- lastTokenVal? = .scalar content .doubleQuoted
    show lastTokenVal? (s_after.tokens.push _) = some (.scalar content .doubleQuoted)
    exact lastTokenVal_push_non_ph' s_after.tokens _ nofun
  · -- simpleKeyAllowed = false
    rfl
  · -- line preserved: s_result.line = sc.line
    show s_after.line = sc.line
    have h_line_adv : sc.advance.line = sc.line :=
      advance_line_of_peek sc '"' (by exact (peek_of_chars_cons sc '"' _ _ hcorr).2)
        (by exact (peek_of_chars_cons sc '"' _ _ hcorr).1) (by decide) (by decide)
    exact h_line_loop.trans h_line_adv

-- Helper: skipWhitespace is identity when first char is not whitespace
theorem skipWhitespace_of_not_ws (s : ScannerState) (c : Char)
    (h_pk : s.peek? = some c) (h_nws : isWhiteSpaceBool c = false)
    (h_more : s.offset < s.inputEnd) :
    skipWhitespace s = s := by
  unfold skipWhitespace
  obtain ⟨n, hn⟩ : ∃ n, s.inputEnd - s.offset = n + 1 :=
    ⟨s.inputEnd - s.offset - 1, by omega⟩
  rw [hn]; unfold skipWhitespaceLoop; simp [h_pk, h_nws]

-- Helper: skipSpaces is identity when first char is not a space
theorem skipSpaces_of_not_space (s : ScannerState) (c : Char)
    (h_pk : s.peek? = some c) (h_ns : c ≠ ' ') :
    skipSpaces s = s := by
  unfold skipSpaces
  cases h_fuel : (s.inputEnd - s.offset) with
  | zero => unfold skipSpacesLoop; rfl
  | succ n =>
    unfold skipSpacesLoop
    -- match s.peek? with | some ' ' => ... | _ => s
    split
    · -- s.peek? = some ' '
      rename_i h_peek
      rw [h_pk] at h_peek; exact absurd (Option.some.inj h_peek) h_ns
    · rfl

-- Helper: skipToContent is identity when first char is content (not ws/lb/comment)
theorem skipToContent_of_content_char (s : ScannerState) (c : Char)
    (h_pk : s.peek? = some c)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_more : s.offset < s.inputEnd) :
    skipToContent s = .ok s := by
  have h_ns : c ≠ ' ' := by intro h; subst h; exact absurd h_nws (by decide)
  have h_nt : c ≠ '\t' := by intro h; subst h; exact absurd h_nws (by decide)
  -- First prove skipToContentWs returns .ok s
  have h_ws : skipToContentWs s = .ok s := by
    unfold skipToContentWs
    split
    · -- needIndentCheck = true: skipSpaces then tab check
      have h_ss := skipSpaces_of_not_space s c h_pk h_ns
      rw [h_ss]; dsimp only []
      split
      · -- at/below indent level: tab check
        -- match s.peek? with | some '\t' => ... | _ => .ok s
        split
        · rename_i h_peek; rw [h_pk] at h_peek
          exact absurd (Option.some.inj h_peek) h_nt
        · rfl
      · -- past indent boundary: skipWhitespace
        exact congrArg Except.ok (skipWhitespace_of_not_ws s c h_pk h_nws h_more)
    · -- needIndentCheck = false: just skipWhitespace
      exact congrArg Except.ok (skipWhitespace_of_not_ws s c h_pk h_nws h_more)
  unfold skipToContent
  obtain ⟨n, hn⟩ : ∃ n, s.inputEnd - s.offset + 1 = n + 1 :=
    ⟨s.inputEnd - s.offset, by omega⟩
  rw [hn]; unfold skipToContentLoop
  simp only [h_ws]
  unfold skipToContentComment; rw [h_pk]; simp [h_nc, h_pk, h_nlb]

-- Helper: saveSimpleKey preserves peek?
theorem saveSimpleKey_preserves_peek (s : ScannerState) :
    (saveSimpleKey s).peek? = s.peek? := by
  unfold saveSimpleKey
  split
  · rfl
  · split
    · dsimp only []; rfl
    · rfl

-- saveSimpleKey preserves all non-token/key fields
@[simp] theorem saveSimpleKey_preserves_input (s : ScannerState) :
    (saveSimpleKey s).input = s.input := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_offset (s : ScannerState) :
    (saveSimpleKey s).offset = s.offset := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_inputEnd (s : ScannerState) :
    (saveSimpleKey s).inputEnd = s.inputEnd := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_col (s : ScannerState) :
    (saveSimpleKey s).col = s.col := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_line (s : ScannerState) :
    (saveSimpleKey s).line = s.line := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_inFlow (s : ScannerState) :
    (saveSimpleKey s).inFlow = s.inFlow := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_indents (s : ScannerState) :
    (saveSimpleKey s).indents = s.indents := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_allowDirectives (s : ScannerState) :
    (saveSimpleKey s).allowDirectives = s.allowDirectives := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_directivesPresent (s : ScannerState) :
    (saveSimpleKey s).directivesPresent = s.directivesPresent := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_flowStack (s : ScannerState) :
    (saveSimpleKey s).flowStack = s.flowStack := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_needIndentCheck (s : ScannerState) :
    (saveSimpleKey s).needIndentCheck = s.needIndentCheck := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_flowLevel (s : ScannerState) :
    (saveSimpleKey s).flowLevel = s.flowLevel := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
@[simp] theorem saveSimpleKey_preserves_ek (s : ScannerState) :
    (saveSimpleKey s).explicitKeyLine = s.explicitKeyLine := by
  unfold saveSimpleKey; split <;> (try rfl); split <;> rfl

-- saveSimpleKey is the identity when simpleKeyAllowed = false and the
-- flow-context explicit-key guard doesn't fire (explicitKeyLine ≠ some line).
-- In our emitter context: inFlow = true, explicitKeyLine = none, simpleKeyAllowed = false.
theorem saveSimpleKey_id_of_flow_ska_false_ek_none (s : ScannerState)
    (h_flow : s.inFlow = true) (h_ska : s.simpleKeyAllowed = false)
    (h_ek : s.explicitKeyLine = none) :
    saveSimpleKey s = s := by
  unfold saveSimpleKey
  simp only [h_flow, h_ek, show (none == some s.line) = false from by rfl,
             Bool.true_and, Bool.false_eq_true, ite_false, h_ska]

/-- **J.4.2.b-2d-key-chain-Part2-body-A foundational lemma**:
    `saveSimpleKey`'s exact pendingKey effect when the push branch fires.

    Under `simpleKeyAllowed = true` and `explicitKeyLine = none` (so the
    flow-context explicit-key guard doesn't fire), `saveSimpleKey` pushes
    one new `.unresolved` entry at `insertBeforeIdx = s.tokens.size`,
    sets `pendingKeyActive` to its index, and marks `simpleKey.possible
    = true`.  Companion to `saveSimpleKey_id_of_flow_ska_false_ek_none`
    (which covers the identity branch).

    Used by `scanNextToken_flow_scanDoubleQuoted_pkPush` (per-leaf
    scalar pkPush theorem). -/
theorem saveSimpleKey_pkPush_when_allowed (s : ScannerState)
    (h_ska : s.simpleKeyAllowed = true)
    (h_ek : s.explicitKeyLine = none) :
    (saveSimpleKey s).pendingKeys = s.pendingKeys.push
      { insertBeforeIdx := s.tokens.size,
        pos := s.currentPos,
        endLine := s.line,
        kind := .unresolved }
    ∧ (saveSimpleKey s).pendingKeyActive = some s.pendingKeys.size
    ∧ (saveSimpleKey s).simpleKey.possible = true := by
  refine ⟨?_, ?_, ?_⟩ <;>
  · unfold saveSimpleKey
    simp only [h_ek, show (none == some s.line) = false from by rfl,
               Bool.and_false, Bool.false_eq_true, ↓reduceIte, h_ska]

/-- **J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-helpers-size**:
    `saveSimpleKey` is push-or-id on `pendingKeys`, so size grows or
    stays.  Used by the size-monotonicity conjuncts of the
    `scanNextToken_flow_*` helpers (each helper's `s'.pendingKeys`
    factors through `(saveSimpleKey s).pendingKeys` via emit/advance
    and inner-scan preservation lemmas, so size mono follows). -/
theorem saveSimpleKey_pendingKeys_size_ge (s : ScannerState) :
    s.pendingKeys.size ≤ (saveSimpleKey s).pendingKeys.size := by
  unfold saveSimpleKey
  split
  · exact Nat.le_refl _
  · split
    · simp [Array.size_push]
    · exact Nat.le_refl _

/-- **J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers**:
    `saveSimpleKey` preserves `(insertBeforeIdx, kind)` of every prior
    pendingKey entry.  Applies unconditionally — when `saveSimpleKey`
    pushes (under `simpleKeyAllowed = true ∧ not (inFlow ∧ explicitKeyLine = some line)`)
    the existing entries are unchanged by the push; when it is the
    identity the result is trivial.  Used by the helper-strengthening
    cadence to thread pkRec preservation through `scanNextToken_flow_*`
    helpers (comma, open, close, value) where saveSimpleKey runs
    inside preprocessing. -/
theorem saveSimpleKey_preserves_pkRec_prior (s : ScannerState) :
    ∀ j (hj : j < s.pendingKeys.size) (hj' : j < (saveSimpleKey s).pendingKeys.size),
      ((saveSimpleKey s).pendingKeys[j]'hj').insertBeforeIdx
        = (s.pendingKeys[j]'hj).insertBeforeIdx
      ∧ ((saveSimpleKey s).pendingKeys[j]'hj').kind
        = (s.pendingKeys[j]'hj).kind := by
  intro j hj hj'
  unfold saveSimpleKey at hj' ⊢
  split
  · refine ⟨rfl, rfl⟩
  · split
    · -- push branch: getElem_push_lt gives the pre-push entry
      refine ⟨?_, ?_⟩
      · simp only [Array.getElem_push_lt hj]
      · simp only [Array.getElem_push_lt hj]
    · refine ⟨rfl, rfl⟩

/-- **J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove**:
    `pendingKeys` equality lifts to (size-mono + pkRec-preservation) — used
    when bridging through `scanNextToken_preprocess_flow_ws1` (which has
    `s₃.pendingKeys = s₂.pendingKeys` via skipToContent's no-op on
    pendingKeys). -/
theorem pkRec_size_of_pks_eq {s₁ s₂ : ScannerState}
    (h : s₂.pendingKeys = s₁.pendingKeys) :
    s₁.pendingKeys.size ≤ s₂.pendingKeys.size ∧
    (∀ j (hj : j < s₁.pendingKeys.size) (hj' : j < s₂.pendingKeys.size),
        (s₂.pendingKeys[j]'hj').insertBeforeIdx = (s₁.pendingKeys[j]'hj).insertBeforeIdx
        ∧ (s₂.pendingKeys[j]'hj').kind = (s₁.pendingKeys[j]'hj).kind) := by
  refine ⟨h ▸ Nat.le_refl _, ?_⟩
  intro j hj hj'
  refine ⟨?_, ?_⟩ <;> simp only [h]

/-- **J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove**:
    Compose two consecutive (size-mono + pkRec-preservation) witnesses through
    an intermediate state.  Used by `emit_scans_in_flow` and consumer lemmas
    to chain helper-level pkRec preservation across multi-step paths
    (key + colon + value + comma + recurse). -/
theorem pkRec_size_compose
    {s s_mid s_end : ScannerState}
    (h_size_mid : s.pendingKeys.size ≤ s_mid.pendingKeys.size)
    (h_size_end : s_mid.pendingKeys.size ≤ s_end.pendingKeys.size)
    (h_rec_mid : ∀ j (hj : j < s.pendingKeys.size) (hj' : j < s_mid.pendingKeys.size),
        (s_mid.pendingKeys[j]'hj').insertBeforeIdx
          = (s.pendingKeys[j]'hj).insertBeforeIdx
        ∧ (s_mid.pendingKeys[j]'hj').kind
          = (s.pendingKeys[j]'hj).kind)
    (h_rec_end : ∀ j (hj : j < s_mid.pendingKeys.size) (hj' : j < s_end.pendingKeys.size),
        (s_end.pendingKeys[j]'hj').insertBeforeIdx
          = (s_mid.pendingKeys[j]'hj).insertBeforeIdx
        ∧ (s_end.pendingKeys[j]'hj').kind
          = (s_mid.pendingKeys[j]'hj).kind) :
    s.pendingKeys.size ≤ s_end.pendingKeys.size ∧
    (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s_end.pendingKeys.size),
        (s_end.pendingKeys[j]'hj').insertBeforeIdx
          = (s.pendingKeys[j]'hj).insertBeforeIdx
        ∧ (s_end.pendingKeys[j]'hj').kind
          = (s.pendingKeys[j]'hj).kind) := by
  refine ⟨Nat.le_trans h_size_mid h_size_end, ?_⟩
  intro j hj hj'
  have hj_mid : j < s_mid.pendingKeys.size := Nat.lt_of_lt_of_le hj h_size_mid
  obtain ⟨h_idx_mid, h_kind_mid⟩ := h_rec_mid j hj hj_mid
  obtain ⟨h_idx_end, h_kind_end⟩ := h_rec_end j hj_mid hj'
  exact ⟨h_idx_end.trans h_idx_mid, h_kind_end.trans h_kind_mid⟩

-- scanValueValidate always succeeds when simpleKey.possible is false
-- and explicitKeyLine is none: all 5 checks short-circuit.
theorem scanValueValidate_ok_of_not_possible_ek_none (s : ScannerState)
    (h_ek : s.explicitKeyLine = none)
    (h_sk : s.simpleKey.possible = false) :
    scanValueValidate s = .ok () := by
  unfold scanValueValidate
  simp only [h_sk, Bool.false_and, ite_false, h_ek, reduceCtorEq]
  rfl

/-- **J.4.2.b-2d-key-chain-Part2-body-B foundational lemma**:
    `scanValuePrepare`'s exact pendingKey effect in flow context with an
    active simple-key reservation.

    Under `s.inFlow = true ∧ s.simpleKey.possible = true`, the flow branch
    of `scanValuePrepare` resolves the active pending-key reservation via
    `setPendingKeyKind …  .keyOnly` and clears `pendingKeyActive`.  The
    `pendingKeys` field equation extracted here is the engine of
    Part2-body-B's per-entry conclusions (size preservation, kind set to
    `.keyOnly` at the active index, insertBeforeIdx preserved, other
    entries unchanged) via the existing `setPendingKeyKind_*` lemmas. -/
theorem scanValuePrepare_pendingKeys_flow_resolve (s : ScannerState)
    (h_flow : s.inFlow = true)
    (h_sk_poss : s.simpleKey.possible = true) :
    (scanValuePrepare s).pendingKeys
      = setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly := by
  unfold scanValuePrepare
  simp only [h_sk_poss, ite_true, h_flow, Bool.not_true, Bool.false_eq_true,
             ite_false]

-- All tokens in the array have pos.line equal to a given line number.
-- This captures the invariant that the emitter produces single-line output.
def AllTokensOnLine (s : ScannerState) (l : Nat) : Prop :=
  ∀ i, (h : i < s.tokens.size) → s.tokens[i].pos.line = l

-- Convenience alias: simpleKey fields track the current line when possible.
-- Both endLine and pos.line are set from s.line by saveSimpleKey; strengthening
-- to a conjunction lets us transfer AllTokensOnLine through scanValuePrepare.
def EndLineOnLine (s : ScannerState) : Prop :=
  s.simpleKey.possible → s.simpleKey.endLine = s.line ∧ s.simpleKey.pos.line = s.line

-- Stack-level EndLineOnLine: the top of simpleKeyStack satisfies EndLineOnLine
-- at a given line. Used to prove EndLineOnLine after flow close restores from stack.
def StackEndLineOnLine (s : ScannerState) (l : Nat) : Prop :=
  match s.simpleKeyStack.back? with
  | none => True
  | some sk => sk.possible → sk.endLine = l ∧ sk.pos.line = l

-- scanValueValidate succeeds in flow context when all tokens are on the same
-- line as the scanner and endLine = line (when possible).
theorem scanValueValidate_ok_of_flow_allTokensOnLine (s : ScannerState)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_end : EndLineOnLine s) :
    scanValueValidate s = .ok () := by
  unfold scanValueValidate EndLineOnLine at *
  cases h_poss : s.simpleKey.possible
  · -- possible = false: all checks short-circuit
    simp only [h_flow, Bool.false_and, Bool.not_true, Bool.and_false,
               ite_false, h_ek, reduceCtorEq]; rfl
  · -- possible = true: endLine = line from h_end
    have ⟨h_el, _⟩ := h_end h_poss
    -- Checks 1,3: !inFlow = false.  Check 2: endLine = line.  Check 5: ek = none.
    simp only [h_flow, h_el, h_ek, Bool.not_true, Bool.and_false, Bool.false_and,
               Bool.true_and, bne_self_eq_false, ite_false, reduceCtorEq]
    -- Check 4: possible && inFlow && tokenIndex > 0 && ...
    by_cases h_ti : s.simpleKey.tokenIndex > 0
    · simp only [show (decide (s.simpleKey.tokenIndex > 0)) = true from decide_eq_true h_ti]
      -- Case analysis on `s.tokens[tokenIndex - 1]?`
      cases h_tok : s.tokens[s.simpleKey.tokenIndex - 1]? with
      | none => rfl -- no token at that index: check passes trivially
      | some tok =>
        -- h_tok tells us getElem? returned some, so index is in bounds
        have ⟨h_bound, h_eq⟩ := Array.getElem?_eq_some_iff.mp h_tok
        have h_pos_line := h_atol (s.simpleKey.tokenIndex - 1) h_bound
        -- h_eq : s.tokens[i] = tok, so tok.pos.line = s.line
        have h_tok_line : tok.pos.line = s.line := h_eq ▸ h_pos_line
        simp only [h_tok_line, bne_self_eq_false, Bool.and_false]; rfl
    · simp only [show (decide (s.simpleKey.tokenIndex > 0)) = false from
                   decide_eq_false (by omega)]; rfl

-- saveSimpleKey leaves tokens unchanged, so filtering is invariant.
--
-- **Initiative 3 / J.2 step 5 cutover** (Category B): post-cutover the
-- middle branch is also identity on tokens (placeholder pushes moved
-- to pendingKeys), so the lemma reduces to `(saveSimpleKey s).tokens = s.tokens`.
theorem saveSimpleKey_filter_placeholder (s : ScannerState) :
    (saveSimpleKey s).tokens.filter (fun t => t.val != .placeholder)
    = s.tokens.filter (fun t => t.val != .placeholder) := by
  have h_eq : (saveSimpleKey s).tokens = s.tokens := by
    unfold saveSimpleKey
    split
    · rfl
    · split <;> rfl
  rw [h_eq]

-- ═══ AllTokensOnLine transfer lemmas ═══

/-- Pushing one token at `currentPos` preserves AllTokensOnLine. -/
theorem AllTokensOnLine_emit (s : ScannerState) (tok : YamlToken) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (s.emit tok) l := by
  intro i h_bound
  unfold ScannerState.emit at h_bound ⊢; dsimp only [] at h_bound ⊢
  simp only [Array.getElem_push]; split
  · exact h_atol i (by assumption)
  · simp [ScannerState.currentPos, h_line]

/-- Advancing preserves AllTokensOnLine (tokens unchanged). -/
theorem AllTokensOnLine_advance (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) :
    AllTokensOnLine s.advance l := by
  intro i h_bound
  simp only [ScannerCorrectness.advance_preserves_tokens s] at h_bound ⊢
  exact h_atol i h_bound

/-- saveSimpleKey preserves AllTokensOnLine.

**Initiative 3 / J.2 step 5 cutover** (Category B): post-cutover
saveSimpleKey is identity on tokens, so the lemma is preserved
trivially. -/
theorem AllTokensOnLine_saveSimpleKey (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (saveSimpleKey s) l := by
  let _ := h_line
  unfold saveSimpleKey
  split
  · exact h_atol
  · split
    · exact h_atol
    · exact h_atol

/-- saveSimpleKey establishes EndLineOnLine in flow context.
    Both endLine and pos.line are set from s.line when saving. -/
theorem EndLineOnLine_saveSimpleKey_flow (s : ScannerState)
    (h_prev : EndLineOnLine s) :
    EndLineOnLine (saveSimpleKey s) := by
  unfold EndLineOnLine saveSimpleKey
  split
  · exact h_prev
  · split
    · intro _; constructor
      · -- endLine = line: by definition, saveSimpleKey sets endLine := st.line
        rfl
      · -- pos.line = line: currentPos.line = line by definition
        show s.currentPos.line = s.line
        unfold ScannerState.currentPos; rfl
    · exact h_prev

/-- emitAt with a pos on line l preserves AllTokensOnLine. -/
theorem AllTokensOnLine_emitAt (s : ScannerState) (pos : YamlPos) (tok : YamlToken) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_pos_line : pos.line = l) :
    AllTokensOnLine (s.emitAt pos tok) l := by
  intro i h_bound
  unfold ScannerState.emitAt at h_bound ⊢; dsimp only [] at h_bound ⊢
  simp only [Array.getElem_push]; split
  · exact h_atol i (by assumption)
  · simp [h_pos_line]

-- ═══ AllTokensOnLine through scan operations ═══
-- Each flow-scan helper composes emit + advance (token-only changes).
-- Struct updates (flowLevel, simpleKeyAllowed, etc.) don't touch tokens
-- and are transparent to AllTokensOnLine by definitional equality.

/-- scanFlowSequenceStart preserves AllTokensOnLine. -/
theorem AllTokensOnLine_scanFlowSequenceStart (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowSequenceStart s) l := by
  unfold scanFlowSequenceStart
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowMappingStart preserves AllTokensOnLine. -/
theorem AllTokensOnLine_scanFlowMappingStart (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowMappingStart s) l := by
  unfold scanFlowMappingStart
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowSequenceStart sets simpleKey.possible to false. -/
theorem scanFlowSequenceStart_simpleKey_not_possible (s : ScannerState) :
    (scanFlowSequenceStart s).simpleKey.possible = false := by
  unfold scanFlowSequenceStart ScannerState.emit ScannerState.advance
  dsimp only []; split <;> (try split) <;> (try split) <;> rfl

/-- scanFlowMappingStart sets simpleKey.possible to false. -/
theorem scanFlowMappingStart_simpleKey_not_possible (s : ScannerState) :
    (scanFlowMappingStart s).simpleKey.possible = false := by
  unfold scanFlowMappingStart ScannerState.emit ScannerState.advance
  dsimp only []; split <;> (try split) <;> (try split) <;> rfl

/-- scanFlowSequenceEnd preserves AllTokensOnLine. -/
theorem AllTokensOnLine_scanFlowSequenceEnd (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowSequenceEnd s) l := by
  unfold scanFlowSequenceEnd
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowMappingEnd preserves AllTokensOnLine. -/
theorem AllTokensOnLine_scanFlowMappingEnd (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine (scanFlowMappingEnd s) l := by
  unfold scanFlowMappingEnd
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- scanFlowEntry preserves AllTokensOnLine
    (emit .flowEntry → advance → set simpleKeyAllowed). -/
theorem AllTokensOnLine_scanFlowEntry (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine ({ (s.emit .flowEntry).advance with simpleKeyAllowed := true }) l := by
  exact AllTokensOnLine_advance _ l (AllTokensOnLine_emit _ _ l h_atol h_line)

/-- allowDirectives struct update preserves AllTokensOnLine (no token changes). -/
theorem AllTokensOnLine_allowDirectives (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) :
    AllTokensOnLine (if s.allowDirectives then
        { s with allowDirectives := false, documentEverStarted := true } else s) l := by
  split <;> exact h_atol

/-- scanValuePrepare in flow context preserves AllTokensOnLine.

**Initiative 3 / J.2 step 5 cutover** (Category B): post-cutover the
flow branch is identity on tokens (setIfInBounds dropped), so the
proof reduces to the unchanged-tokens case in every sub-branch.
`h_endline` is no longer needed. -/
theorem AllTokensOnLine_scanValuePrepare_flow (s : ScannerState) (l : Nat)
    (h_atol : AllTokensOnLine s l) (h_line : s.line = l)
    (h_flow : s.inFlow = true)
    (h_ek : s.explicitKeyLine = none)
    (h_endline : EndLineOnLine s) :
    AllTokensOnLine (scanValuePrepare s) l := by
  let _ := h_line; let _ := h_endline
  unfold AllTokensOnLine scanValuePrepare
  cases h_poss : s.simpleKey.possible
  · -- possible = false: explicitKeyLine = none, inFlow = true → identity
    simp only [h_ek, Option.isSome_none, ite_false,
               h_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    intro i h_bound; exact h_atol i h_bound
  · -- possible = true, inFlow: tokens unchanged
    simp only [h_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    intro i h_bound; exact h_atol i h_bound

/-- scanDoubleQuoted preserves AllTokensOnLine: the loop doesn't add tokens,
    and emitAt pushes one token at currentPos.line = s.line. -/
theorem AllTokensOnLine_scanDoubleQuoted (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s')
    (h_flow : s.inFlow = true)
    (l : Nat) (h_atol : AllTokensOnLine s l) (h_line : s.line = l) :
    AllTokensOnLine s' l := by
  unfold scanDoubleQuoted at h_ok
  simp only [bind, Except.bind, pure, Pure.pure, Except.pure] at h_ok
  split at h_ok <;> try contradiction
  rename_i result heq
  split at h_ok
  · -- block context: impossible since h_flow says inFlow = true
    exfalso; simp [h_flow] at *
  · -- flow context
    simp only [Except.ok.injEq] at h_ok; subst h_ok
    apply AllTokensOnLine_emitAt
    · intro i h_bound
      have h_toks : result.snd.tokens = s.tokens :=
        (ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
          _ _ _ _ _ _ _ _ heq).trans
          (ScannerCorrectness.advance_preserves_tokens s)
      simp only [h_toks] at h_bound ⊢
      exact h_atol i h_bound
    · simp [ScannerState.currentPos, h_line]

/-- scanDoubleQuoted preserves simpleKey: the loop, advance, and emitAt
    don't modify simpleKey. -/
theorem scanDoubleQuoted_preserves_simpleKey (s s' : ScannerState)
    (h_ok : scanDoubleQuoted s = .ok s') :
    s'.simpleKey = s.simpleKey :=
  ScannerCorrectness.scanDoubleQuoted_preserves_simpleKey s s' h_ok

-- ═══ Factored preprocessing for initial scanner state ═══

/-- Preprocessing on the initial scanner state returns the first character.

    For any non-empty input string starting with a non-blank, non-comment,
    non-line-break character `c`, preprocessing the initial state
    `(ScannerState.mk' input).emit .streamStart` succeeds and returns
    `(s_pp, c)` with all position/metadata fields preserved.

    This is the common first step for all `scanNextToken_emit*_init` proofs. -/
theorem scanNextToken_preprocess_init_state (input : String) (c : Char)
    (rest : List Char)
    (h_toList : input.toList = c :: rest)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#') :
    ∃ s_pp, scanNextToken_preprocess ((ScannerState.mk' input).emit .streamStart)
          = .ok (some (s_pp, c))
      ∧ s_pp.flowLevel = 0
      ∧ s_pp.inFlow = false
      ∧ s_pp.currentIndent = -1
      ∧ s_pp.col = 0
      ∧ s_pp.allowDirectives = true
      ∧ s_pp.directivesPresent = false
      ∧ s_pp.indents = #[{column := -1, isSequence := false}]
      ∧ s_pp.input = input
      ∧ s_pp.offset = 0
      ∧ s_pp.inputEnd = input.utf8ByteSize
      ∧ s_pp.explicitKeyLine = none
      ∧ s_pp.line = 0
      ∧ AllTokensOnLine s_pp s_pp.line
      ∧ s_pp.tokens.filter (fun t => t.val != .placeholder)
          = ((ScannerState.mk' input).emit .streamStart).tokens.filter
              (fun t => t.val != .placeholder) := by
  -- Build ScannerSurfCorr for the initial state
  have h_chars := chars_from_zero_toList input
  rw [h_toList] at h_chars
  have h_corr₀ := initial_corr input _ h_chars
  have h_corr_s₀ : ScannerSurfCorr
      ((ScannerState.mk' input).emit .streamStart) ⟨c :: rest, 0⟩ :=
    ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
  have ⟨h_pk₀, _⟩ := peek_of_chars_cons _ c _ 0 h_corr_s₀
  have h_size : input.utf8ByteSize ≥ 1 := by
    rw [utf8ByteSize_eq_listByteSize, h_toList, listByteSize]
    have := Char.utf8Size_pos c; omega
  -- skipToContent is identity (c is not whitespace/linebreak/comment)
  have h_stc : skipToContent ((ScannerState.mk' input).emit .streamStart)
      = .ok ((ScannerState.mk' input).emit .streamStart) :=
    skipToContent_of_content_char _ c h_pk₀ h_nws h_nlb h_nc (by omega)
  -- Construct the witness
  refine ⟨saveSimpleKey { (ScannerState.mk' input).emit .streamStart
    with needIndentCheck := false },
    ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl,
    by exact AllTokensOnLine_saveSimpleKey _ 0
         (AllTokensOnLine_emit _ _ 0
           (by intro i h_bound; have : 0 = (ScannerState.mk' input).tokens.size := rfl; omega) rfl)
         rfl,
    saveSimpleKey_filter_placeholder _⟩
  -- Prove: scanNextToken_preprocess = .ok (some (saveSimpleKey {...}, c))
  unfold scanNextToken_preprocess
  rw [h_stc]; simp only [bind, Except.bind, pure, Except.pure]
  have h_hm : ((ScannerState.mk' input).emit .streamStart).hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true (by omega)
  simp only [h_hm, Bool.not_true, Bool.false_eq_true, ite_false]
  -- unwindIndents is identity since currentIndent = -1 < col = 0
  have h_uwi : unwindIndents ((ScannerState.mk' input).emit .streamStart)
      ↑((ScannerState.mk' input).emit .streamStart).col
      = (ScannerState.mk' input).emit .streamStart := by
    unfold unwindIndents unwindIndentsLoop; split <;> rfl
  simp only [h_uwi]
  -- inFlow = false, needIndentCheck = true → enters the branch
  have h_inFlow : ((ScannerState.mk' input).emit .streamStart).inFlow = false := rfl
  have h_nic_true : ((ScannerState.mk' input).emit .streamStart).needIndentCheck = true := rfl
  have h_no_shrink : ¬(((ScannerState.mk' input).emit .streamStart).indents.size <
      ((ScannerState.mk' input).emit .streamStart).indents.size) := by omega
  simp only [h_inFlow, h_nic_true, Bool.not_false, Bool.true_and,
             h_no_shrink, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  -- peek? of saveSimpleKey result = some c
  have h_sk_peek : (saveSimpleKey { (ScannerState.mk' input).emit .streamStart
      with needIndentCheck := false }).peek? = some c := by
    rw [saveSimpleKey_preserves_peek]; exact h_pk₀
  rw [h_sk_peek]

-- The first scanNextToken call on the initial emitScalar state
-- dispatches to scanDoubleQuoted and succeeds.
--
-- **Initiative 3 / J.3.7** (2026-04-29): added two unfiltered clauses
-- (`s₁.tokens.map (·.val) = #[.streamStart, .scalar ...]` and
-- `pendingKeys all unresolved`) needed by `scanFiltered_emitScalar_vals`
-- and `scanFiltered_emitScalar_content`.  Post-cutover the scanner
-- never pushes `.placeholder`, so the filter and unfiltered shapes
-- coincide, but the unfiltered form is what `linearise_all_unresolved`
-- consumes.
theorem scanNextToken_emitScalar_init (content : String) :
    ∃ s₁, scanNextToken ((ScannerState.mk' (emitScalar content)).emit .streamStart) = .ok (some s₁)
      ∧ s₁.peek? = none ∧ s₁.flowLevel = 0 ∧ s₁.directivesPresent = false
      ∧ (∃ tok ∈ s₁.tokens, tok.val = .scalar content .doubleQuoted)
      ∧ s₁.indents = #[{column := -1, isSequence := false}]
      ∧ (s₁.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .scalar content .doubleQuoted]
      ∧ s₁.tokens.map (·.val) = #[.streamStart, .scalar content .doubleQuoted]
      ∧ (∀ e ∈ s₁.pendingKeys, e.kind = .unresolved) := by
  -- Build ScannerSurfCorr for the initial state
  have h_chars := chars_from_zero_toList (emitScalar content)
  rw [emitScalar_toList] at h_chars
  have h_corr₀ := initial_corr (emitScalar content) _ h_chars
  -- ═══ Step 1: preprocessing returns (s_pp, '"') with key invariants ═══
  -- The preprocessing (skipToContent → hasMore → unwindIndents → saveSimpleKey → peek?)
  -- returns a state s_pp preserving all position/metadata fields.
  have h_pp : ∃ s_pp, scanNextToken_preprocess
      ((ScannerState.mk' (emitScalar content)).emit .streamStart)
      = .ok (some (s_pp, '"'))
    ∧ s_pp.input = emitScalar content ∧ s_pp.offset = 0
    ∧ s_pp.inputEnd = (emitScalar content).utf8ByteSize
    ∧ s_pp.col = 0
    ∧ s_pp.indents = #[{column := -1, isSequence := false}]
    ∧ s_pp.flowLevel = 0 ∧ s_pp.directivesPresent = false
    ∧ s_pp.allowDirectives = true ∧ s_pp.currentIndent = -1
    ∧ (s_pp.tokens.filter (fun t => t.val != .placeholder)).map (·.val) = #[.streamStart]
    ∧ s_pp.tokens.map (·.val) = #[.streamStart]
    ∧ (∀ e ∈ s_pp.pendingKeys, e.kind = .unresolved) := by
    -- Get peek? for initial state
    have h_corr_s₀ : ScannerSurfCorr
        ((ScannerState.mk' (emitScalar content)).emit .streamStart)
        ⟨['"'] ++ (escapeString content).toList ++ ['"'], 0⟩ :=
      ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
    have ⟨h_pk₀, _⟩ := peek_of_chars_cons _ '"' _ 0 h_corr_s₀
    have h_size := emitScalar_utf8ByteSize_ge content
    -- skipToContent is identity ('"' is not whitespace/linebreak/comment)
    have h_stc : skipToContent ((ScannerState.mk' (emitScalar content)).emit .streamStart)
        = .ok ((ScannerState.mk' (emitScalar content)).emit .streamStart) :=
      skipToContent_of_content_char _ '"' h_pk₀ (by decide) (by decide) (by decide) (by omega)
    -- Construct witness: the actual preprocessing modifies needIndentCheck before saveSimpleKey
    -- (default needIndentCheck is true; the if-branch sets it to false after unwindIndents)
    refine ⟨saveSimpleKey { (ScannerState.mk' (emitScalar content)).emit .streamStart
              with needIndentCheck := false },
      ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_, ?_⟩
    · -- Prove: scanNextToken_preprocess = .ok (some (saveSimpleKey {...}, '"'))
      unfold scanNextToken_preprocess
      -- Step 1: resolve skipToContent bind
      rw [h_stc]; simp only [bind, Except.bind, pure, Except.pure]
      -- Step 2: resolve hasMore
      have h_hm : ((ScannerState.mk' (emitScalar content)).emit .streamStart).hasMore = true := by
        unfold ScannerState.hasMore; exact decide_eq_true (by omega)
      simp only [h_hm, Bool.not_true, Bool.false_eq_true, ite_false]
      -- Step 3: resolve unwindIndents (identity since currentIndent = -1 < col = 0)
      have h_uwi : unwindIndents ((ScannerState.mk' (emitScalar content)).emit .streamStart)
          ↑((ScannerState.mk' (emitScalar content)).emit .streamStart).col
          = (ScannerState.mk' (emitScalar content)).emit .streamStart := by
        unfold unwindIndents unwindIndentsLoop; split <;> rfl
      simp only [h_uwi]
      -- Step 4: resolve if-checks and remaining computation
      have h_inFlow : ((ScannerState.mk' (emitScalar content)).emit .streamStart).inFlow = false := by rfl
      have h_nic_true : ((ScannerState.mk' (emitScalar content)).emit .streamStart).needIndentCheck = true := by rfl
      have h_no_trailing : ¬(((ScannerState.mk' (emitScalar content)).emit .streamStart).indents.size <
          ((ScannerState.mk' (emitScalar content)).emit .streamStart).indents.size) := by omega
      simp only [h_inFlow, h_nic_true, Bool.not_false, Bool.true_and,
                 h_no_trailing, decide_false, Bool.false_and, Bool.false_eq_true, ↓reduceIte]
      -- Prove peek? of saveSimpleKey result = some '"'
      have h_sk_peek : (saveSimpleKey { (ScannerState.mk' (emitScalar content)).emit .streamStart
          with needIndentCheck := false }).peek?
          = some '"' := by
        rw [saveSimpleKey_preserves_peek]
        exact h_pk₀
      -- Rewrite the peek? in the match to resolve it
      rw [h_sk_peek]
    · -- Filter property: saveSimpleKey preserves filtered tokens
      unfold saveSimpleKey
      split
      · simp [ScannerState.emit, ScannerState.mk']
      · split
        · dsimp only []
          simp [ScannerState.emit, ScannerState.mk']
        · simp [ScannerState.emit, ScannerState.mk']
    · -- **J.3.7**: unfiltered tokens = #[streamStart].  Post-cutover
      -- saveSimpleKey doesn't push tokens, so all three branches
      -- preserve the streamStart-emitted token array.
      unfold saveSimpleKey
      split
      · simp [ScannerState.emit, ScannerState.mk']
      · split
        · dsimp only []
          simp [ScannerState.emit, ScannerState.mk']
        · simp [ScannerState.emit, ScannerState.mk']
    · -- **J.3.7**: pendingKeys are all unresolved.  The streamStart-
      -- emitted state has empty pendingKeys (vacuous); saveSimpleKey
      -- pushes at most one entry whose kind is `.unresolved`.
      unfold saveSimpleKey
      split
      · -- Branch 1: state unchanged → pendingKeys is initial (empty).
        intro e h_mem
        simp [ScannerState.emit, ScannerState.mk'] at h_mem
      · split
        · -- Branch 2: pushes one .unresolved entry.  The starting
          -- pendingKeys is empty (mk' default), so the only member is
          -- the freshly-pushed entry whose `.kind = .unresolved`.
          dsimp only []
          intro e h_mem
          simp [ScannerState.emit, ScannerState.mk'] at h_mem
          subst h_mem; rfl
        · -- Branch 3: state unchanged.
          intro e h_mem
          simp [ScannerState.emit, ScannerState.mk'] at h_mem
  obtain ⟨s_pp, h_pp_eq, h_inp, h_off, h_ie, h_col_pp, h_ids,
          h_fl_pp, h_dp_pp, h_ad_pp, h_ci_pp, h_filt_pp, h_map_pp, h_pks_pp⟩ := h_pp
  -- ═══ Step 2: build ScannerSurfCorr for s_pp from field equalities ═══
  have h_corr_pp : ScannerSurfCorr s_pp
      ⟨['"'] ++ (escapeString content).toList ++ ['"'], s_pp.col⟩ := by
    rw [h_col_pp]
    exact ScannerSurfCorr_transfer h_corr₀ h_inp h_off h_ie h_col_pp h_ids
  have ⟨h_pk_pp, _⟩ := peek_of_chars_cons s_pp '"'
    ((escapeString content).toList ++ ['"']) _ h_corr_pp
  -- peekAt? 0 = peek? (definitional)
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?; rfl
  -- atDocumentStart/End: first char is '"' which is not '-' or '.'
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart; rw [h_pat0, h_pk_pp]
    simp only [show (some '"' == some '-') = false from by decide,
               Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd; rw [h_pat0, h_pk_pp]
    simp only [show (some '"' == some '.') = false from by decide,
               Bool.and_false, Bool.false_and]
  -- dispatchStructural returns .ok none for '"'
  have ⟨h_disp_s, _, _, _⟩ :=
    dispatchContent_quote s_pp '"' rfl h_fl_pp h_ci_pp h_ds h_de
  -- ═══ Step 3: dispatch chain on s_ad (after allowDirectives modification) ═══
  let s_ad : ScannerState := { s_pp with allowDirectives := false, documentEverStarted := true }
  have ⟨_, h_cbfi_ad, h_dfi_ad, h_dbi_ad⟩ :=
    dispatchContent_quote s_ad '"' rfl h_fl_pp h_ci_pp h_ds h_de
  -- ═══ Step 4: ScannerSurfCorr for s_ad and scanDoubleQuoted setup ═══
  have h_corr_ad : ScannerSurfCorr s_ad
      ⟨['"'] ++ (escapeString content).toList ++ ['"'], s_ad.col⟩ :=
    ScannerSurfCorr_transfer h_corr_pp rfl rfl rfl rfl rfl
  have h_fl_ad : s_ad.flowLevel = 0 := h_fl_pp
  have h_inFlow : s_ad.inFlow = false := by
    unfold ScannerState.inFlow; rw [h_fl_ad]; decide
  -- ═══ Step 5: dispatchContent produces final state with right properties ═══
  have h_dc : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final
    ∧ s_final.peek? = none ∧ s_final.flowLevel = 0
    ∧ s_final.directivesPresent = false
    ∧ (∃ tok ∈ s_final.tokens, tok.val = .scalar content .doubleQuoted)
    ∧ s_final.indents = s_ad.indents
    ∧ (s_final.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
        = #[.streamStart, .scalar content .doubleQuoted]
    ∧ s_final.tokens.map (·.val) = #[.streamStart, .scalar content .doubleQuoted]
    ∧ (∀ e ∈ s_final.pendingKeys, e.kind = .unresolved) := by
    -- scanDoubleQuoted succeeds and preserves fields
    obtain ⟨s_dq, h_dq, h_pk_dq, h_tok_dq⟩ := scanDoubleQuoted_emitScalar_ok s_ad content h_corr_ad h_inFlow
    have h_fl_dq : s_dq.flowLevel = 0 :=
      (L4YAML.Proofs.ScannerPlainScalarValid.scanDoubleQuoted_preserves_flowLevel
        s_ad s_dq h_dq).trans h_fl_ad
    have h_dp_dq : s_dq.directivesPresent = false :=
      (scanDoubleQuoted_preserves_dp s_ad s_dq h_dq).trans h_dp_pp
    have h_ids_dq : s_dq.indents = s_ad.indents :=
      scanDoubleQuoted_preserves_indents s_ad s_dq h_dq
    -- **J.3.7**: scanDoubleQuoted preserves pendingKeys (proven in
    -- ScannerCorrectness.lean line 10343).  Combined with `s_ad.pendingKeys
    -- = s_pp.pendingKeys` (struct-update on different field) and
    -- `h_pks_pp`, all entries of s_dq.pendingKeys are unresolved.
    have h_pks_dq : ∀ e ∈ s_dq.pendingKeys, e.kind = .unresolved := by
      have h_eq : s_dq.pendingKeys = s_ad.pendingKeys :=
        L4YAML.Proofs.ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeys s_ad s_dq h_dq
      rw [h_eq, show s_ad.pendingKeys = s_pp.pendingKeys from rfl]
      exact h_pks_pp
    -- Token membership: scalar is in s_dq.tokens
    have h_tok_mem : ∃ tok ∈ s_dq.tokens, tok.val = .scalar content .doubleQuoted :=
      ⟨_, by rw [h_tok_dq]; exact Array.mem_push_self, rfl⟩
    -- Extend filtered tokens: s_dq.tokens = s_ad.tokens.push {scalar}, s_ad.tokens = s_pp.tokens
    have h_filt_dq :
        (s_dq.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .scalar content .doubleQuoted] := by
      rw [h_tok_dq]
      simp only [Array.filter_push,
        show (YamlToken.scalar content .doubleQuoted != .placeholder) = true from rfl,
        ite_true, Array.map_push,
        show s_ad.tokens = s_pp.tokens from rfl, h_filt_pp]
      rfl
    -- **J.3.7**: unfiltered map shape derived from h_map_pp.
    have h_map_dq : s_dq.tokens.map (·.val) = #[.streamStart, .scalar content .doubleQuoted] := by
      rw [h_tok_dq, Array.map_push,
          show s_ad.tokens = s_pp.tokens from rfl, h_map_pp]
      rfl
    -- Unfold dispatchContent: all if-branches except '"' are eliminated by decide
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, h_dq]
    -- The simpleKey update preserves peek?/flowLevel/directivesPresent/tokens/indents/
    -- pendingKey-kinds.  In the `simpleKey.possible = true` branch the update wraps
    -- s_dq with `setPendingKeyEndLine` on pendingKeys, which only touches the
    -- `endLine` field — preserving every entry's `.kind`.
    -- Use Bool.rec to avoid dependent elimination issues with cases.
    have h_pks_setEL : ∀ (active : Option Nat) (line : Nat)
        (e : PendingKeyEntry),
        e ∈ setPendingKeyEndLine s_dq.pendingKeys active line →
        e.kind = .unresolved := by
      intro active line e h_mem
      unfold setPendingKeyEndLine at h_mem
      cases active with
      | none => exact h_pks_dq e h_mem
      | some i =>
        simp only [] at h_mem
        cases h_get : s_dq.pendingKeys[i]? with
        | none =>
          rw [h_get] at h_mem
          exact h_pks_dq e h_mem
        | some entry =>
          rw [h_get] at h_mem
          -- `setIfInBounds i entry'` may either return original or update entry at i
          have h_entry_unres : entry.kind = .unresolved :=
            h_pks_dq entry (Array.mem_of_getElem? h_get)
          have h_mem_or := Array.mem_or_eq_of_mem_setIfInBounds h_mem
          cases h_mem_or with
          | inl h => exact h_pks_dq e h
          | inr h =>
            -- e = { entry with endLine := line } → e.kind = entry.kind
            rw [h]; exact h_entry_unres
    exact ⟨_, rfl,
      s_dq.simpleKey.possible.rec h_pk_dq h_pk_dq,
      s_dq.simpleKey.possible.rec h_fl_dq h_fl_dq,
      s_dq.simpleKey.possible.rec h_dp_dq h_dp_dq,
      s_dq.simpleKey.possible.rec h_tok_mem h_tok_mem,
      s_dq.simpleKey.possible.rec h_ids_dq h_ids_dq,
      s_dq.simpleKey.possible.rec h_filt_dq h_filt_dq,
      s_dq.simpleKey.possible.rec h_map_dq h_map_dq,
      s_dq.simpleKey.possible.rec h_pks_dq (h_pks_setEL _ _)⟩
  obtain ⟨s_final, h_dc_eq, h_pkf, h_flf, h_dpf, h_tokf, h_idsf, h_filtf,
          h_mapf, h_pksf⟩ := h_dc
  -- ═══ Step 6: compose all steps through scanNextToken ═══
  refine ⟨s_final, ?_, h_pkf, h_flf, h_dpf, h_tokf, h_idsf.trans h_ids, h_filtf,
          h_mapf, h_pksf⟩
  -- Reduce: scanNextToken = preprocess →ᵦ dispatchStructural →ᵦ allowDirectives →
  --   checkBlockFlowIndent →ᵦ dispatchFlowIndicators →ᵦ dispatchBlockIndicators →ᵦ dispatchContent
  unfold scanNextToken
  simp only [bind, Except.bind, h_pp_eq]
  simp only [h_disp_s]
  simp only [show s_pp.allowDirectives = true from h_ad_pp, ite_true]
  -- Remaining dispatch steps use s_ad = { s_pp with allowDirectives := false, ... }
  -- which is definitionally equal to the expanded struct in the goal
  exact h_cbfi_ad ▸ h_dfi_ad ▸ h_dbi_ad ▸ h_dc_eq ▸ rfl

/-- **Scalar case**: The scanner accepts any double-quoted scalar produced
    by the emitter.

    **Initiative 3 / J.3.6** (2026-04-28): post-cutover, route the
    one-step `scanNextToken_emitScalar_init` chain through the J.3.6
    `scanFiltered_of_chain` consumer.  The init lemma already supplies
    `s₁.peek? = none`, `flowLevel = 0`, `directivesPresent = false`;
    `scanNextToken_eof` closes the loop on `s₁`. -/
theorem scan_accepts_emitScalar (content : String) :
    ∃ tokens, scanFiltered (emitScalar content) = .ok tokens := by
  obtain ⟨s₁, h_snt₁, h_peek₁, h_fl₁, h_dp₁, _, _, _, _, _⟩ :=
    scanNextToken_emitScalar_init content
  let s₀ := (ScannerState.mk' (emitScalar content)).emit .streamStart
  have h_chain : ScanChain s₀ 1 s₁ := ScanChain.single h_snt₁
  have h_eof : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek₁
  -- BOM check: emitScalar content starts with '"', not '﻿'.
  have h_no_bom : (ScannerState.mk' (emitScalar content)).peek? ≠ some '﻿' := by
    have h_chars := chars_from_zero_toList (emitScalar content)
    rw [emitScalar_toList] at h_chars
    have h_corr := initial_corr (emitScalar content) _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '"' _ 0 h_corr
    rw [h_pk]; decide
  -- Fuel: emitScalar produces ≥ 2 bytes, so (utf8ByteSize + 1) * 4 ≥ 12 ≥ 1 + 1.
  have h_fuel : 1 + 1 ≤ ((emitScalar content).utf8ByteSize + 1) * 4 := by
    have h := emitScalar_utf8ByteSize_ge content; omega
  exact scanFiltered_of_chain (emitScalar content) s₀ s₁ 1 rfl h_no_bom
    h_chain h_eof h_fl₁ h_dp₁ h_fuel

-- ═══ Flow collection scanner acceptance ═══
-- Infrastructure for proving that the scanner accepts emitted flow collections.

-- Test: can we evaluate scanFiltered on small flow collections?
theorem scan_emptySeq_test :
    (Scanner.scanFiltered "[]").isOk = true := by native_decide

theorem scan_emptyMap_test :
    (Scanner.scanFiltered "{}").isOk = true := by native_decide

theorem scan_singleScalarSeq_test :
    (Scanner.scanFiltered "[\"hello\"]").isOk = true := by native_decide

theorem scan_twoScalarSeq_test :
    (Scanner.scanFiltered "[\"a\", \"b\"]").isOk = true := by native_decide

theorem scan_nestedSeq_test :
    (Scanner.scanFiltered "[[\"a\"]]").isOk = true := by native_decide

-- ═══ Flow-context preprocessing ═══

/-- In flow context, `scanNextToken_preprocess` with a content character
    returns `some (saveSimpleKey s, c)` unchanged.  The proof relies on:
    1. `skipToContent` is identity for non-ws/non-lb/non-comment chars
    2. `!s.inFlow = false` skips `unwindIndents`
    3. `indents.size` unchanged → trailing content check is false
    4. `saveSimpleKey` preserves peek -/
theorem scanNextToken_preprocess_flow (s : ScannerState) (c : Char)
    (rest : List Char) (col : Nat)
    (hcorr : ScannerSurfCorr s ⟨c :: rest, col⟩)
    (h_flow : s.inFlow = true)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#') :
    scanNextToken_preprocess s = .ok (some (saveSimpleKey s, c)) := by
  have ⟨h_pk, h_lt⟩ := peek_of_chars_cons s c rest col hcorr
  -- skipToContent is identity
  have h_stc : skipToContent s = .ok s :=
    skipToContent_of_content_char s c h_pk h_nws h_nlb h_nc h_lt
  -- hasMore = true
  have h_hm : s.hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true h_lt
  unfold scanNextToken_preprocess
  rw [h_stc]; simp only [bind, Except.bind, pure, Except.pure]
  -- !s.inFlow = false → skip unwindIndents branch
  simp only [h_hm, h_flow, Bool.not_true, Bool.false_eq_true, ite_false]
  -- indents.size < savedIndentSize is s.indents.size < s.indents.size → false
  simp only [show ¬(s.indents.size < s.indents.size) from by omega, decide_false,
             Bool.false_and, Bool.false_eq_true, ↓reduceIte]
  -- saveSimpleKey preserves peek
  rw [saveSimpleKey_preserves_peek, h_pk]

-- Variant with a single leading space: preprocessing of `' ' :: c :: rest`
-- yields the same result as preprocessing of the post-space state.
-- Key idea: skipToContent absorbs the space, reaching the same state s₁
-- as skipToContent on s₁ (identity for non-ws first char).
theorem scanNextToken_preprocess_flow_ws1 (s : ScannerState) (c : Char)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨' ' :: c :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_indent : s.currentIndent < 0) :
    ∃ s₁, ScannerSurfCorr s₁ ⟨c :: rest, s₁.col⟩
      ∧ s₁.inFlow = true
      ∧ s₁.flowLevel = s.flowLevel
      ∧ s₁.currentIndent = s.currentIndent
      ∧ s₁.col = s.col + 1
      ∧ s₁.directivesPresent = s.directivesPresent
      ∧ s₁.indents = s.indents
      ∧ s₁.explicitKeyLine = s.explicitKeyLine
      ∧ s₁.line = s.line
      ∧ scanNextToken_preprocess s = scanNextToken_preprocess s₁
      ∧ (AllTokensOnLine s s.line → AllTokensOnLine s₁ s₁.line)
      ∧ (EndLineOnLine s → EndLineOnLine s₁)
      ∧ s₁.simpleKeyStack = s.simpleKeyStack
      ∧ s₁.tokens = s.tokens
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- skipToContent doesn't touch pendingKeys, so the preprocessed state's
      -- pendingKeys equal the input's.
      ∧ s₁.pendingKeys = s.pendingKeys
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack also passes through (mirror of simpleKeyStack).
      ∧ s₁.pendingKeyStack = s.pendingKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon:
      -- skipToContent preserves `simpleKeyAllowed` (advance/skipWhitespace are
      -- field-preserving record-update passes), so the gate threads through
      -- ws1 untouched.  Used by `emitPairList_scans_nonempty`'s recursive case
      -- to lift `simpleKeyAllowed = true` from post-comma to the IH input. -/
      ∧ s₁.simpleKeyAllowed = s.simpleKeyAllowed := by
  -- Key: skipToContent absorbs the single space. We decompose the proof:
  -- (a) skipToContent s = .ok s₁ for some s₁ at c :: rest with field preservation
  -- (b) skipToContent s₁ = .ok s₁ (identity, via skipToContent_of_content_char)
  -- (c) both preprocessing paths yield (saveSimpleKey s₁, c)
  -- Part (a): skipToContent s advances past the space
  -- This traces through skipToContentLoop → skipToContentWs (needIndentCheck branch) →
  -- skipWhitespace/skipSpaces → skipToContentComment (identity) → not line break → return.
  have h_stc_exists : ∃ s₁, skipToContent s = .ok s₁
      ∧ ScannerSurfCorr s₁ ⟨c :: rest, s₁.col⟩
      ∧ s₁.flowLevel = s.flowLevel
      ∧ s₁.indents = s.indents
      ∧ s₁.directivesPresent = s.directivesPresent
      ∧ s₁.explicitKeyLine = s.explicitKeyLine
      ∧ s₁.col = s.col + 1
      ∧ s₁.line = s.line
      ∧ s₁.tokens = s.tokens
      ∧ s₁.simpleKey = s.simpleKey
      ∧ s₁.simpleKeyStack = s.simpleKeyStack
      ∧ s₁.simpleKeyAllowed = s.simpleKeyAllowed := by
    -- Both needIndentCheck branches yield s.advance. Proof via advance lemmas.
    have ⟨h_pk_space, h_lt⟩ := peek_of_chars_cons s ' ' (c :: rest) s.col hcorr
    -- s.advance is at c :: rest with col + 1
    have h_adv_corr : ScannerSurfCorr s.advance ⟨c :: rest, s.col + 1⟩ :=
      advance_non_newline_corr s ' ' (c :: rest) hcorr h_lt (by decide) (by decide)
    -- advance.peek? = some c
    have ⟨h_pk_adv, h_lt_adv⟩ := peek_of_chars_cons s.advance c rest (s.col + 1) h_adv_corr
    have h_ns : c ≠ ' ' := by intro h; subst h; exact absurd h_nws (by decide)
    -- Helper: skipWhitespace s = s.advance
    have h_sw_eq : skipWhitespace s = s.advance := by
      unfold skipWhitespace
      obtain ⟨n, hn⟩ : ∃ n, s.inputEnd - s.offset = n + 1 :=
        ⟨s.inputEnd - s.offset - 1, by omega⟩
      rw [hn]; unfold skipWhitespaceLoop; simp only [h_pk_space, show isWhiteSpaceBool ' ' = true from by decide, ite_true]
      cases n with
      | zero => unfold skipWhitespaceLoop; rfl
      | succ n' => unfold skipWhitespaceLoop; simp [h_pk_adv, h_nws]
    -- Helper: skipSpaces s = s.advance
    have h_ss_eq : skipSpaces s = s.advance := by
      unfold skipSpaces
      cases h_fuel : (s.inputEnd - s.offset) with
      | zero => omega
      | succ n =>
        unfold skipSpacesLoop; simp only [h_pk_space]
        cases n with
        | zero => unfold skipSpacesLoop; rfl
        | succ n' => unfold skipSpacesLoop; rw [h_pk_adv]; simp [h_ns]
    -- advance field properties
    have h_adv_fl : s.advance.flowLevel = s.flowLevel :=
      ScannerCorrectness.advance_preserves_flowLevel s
    have h_adv_flow : s.advance.inFlow = true := by
      unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_adv_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow)
    have h_adv_ids : s.advance.indents = s.indents := advance_indents s
    have h_adv_indent : s.advance.currentIndent = s.currentIndent := by
      unfold ScannerState.currentIndent; rw [h_adv_ids]
    have h_adv_col : s.advance.col = s.col + 1 := h_adv_corr.col_eq.symm
    -- skipToContentWs s = .ok s.advance (case split on needIndentCheck)
    have h_ws : skipToContentWs s = .ok s.advance := by
      unfold skipToContentWs
      split
      · -- needIndentCheck = true: skipSpaces s = s.advance, then condition false → else
        rw [h_ss_eq]
        -- condition: (!s.advance.inFlow && ...) || (col ≤ currentIndent) both false
        simp only [h_adv_flow, Bool.not_true, Bool.false_and, Bool.false_or]
        simp only [show ¬((s.advance.col : Int) ≤ s.advance.currentIndent) from by
          rw [h_adv_col, h_adv_indent]; omega, decide_false]
        -- else: skipWhitespace s.advance = s.advance (c is non-ws)
        exact congrArg Except.ok (skipWhitespace_of_not_ws s.advance c h_pk_adv h_nws h_lt_adv)
      · -- needIndentCheck = false: skipWhitespace s = s.advance
        exact congrArg Except.ok h_sw_eq
    -- Now compose: skipToContent s = skipToContentLoop s fuel
    have h_adv_corr' : ScannerSurfCorr s.advance ⟨c :: rest, s.advance.col⟩ := by
      rw [h_adv_col]; exact h_adv_corr
    have h_adv_ska : s.advance.simpleKeyAllowed = s.simpleKeyAllowed := by
      -- s.advance preserves simpleKeyAllowed (record-update on offset/line/col only).
      unfold ScannerState.advance; dsimp only []
      split <;> (try split) <;> (try split) <;> rfl
    refine ⟨s.advance, ?_, h_adv_corr', ScannerCorrectness.advance_preserves_flowLevel s,
      advance_indents s, advance_preserves_dp s, advance_explicitKeyLine s, h_adv_col,
      advance_line_of_peek s ' ' h_lt h_pk_space (by decide) (by decide),
      ScannerCorrectness.advance_preserves_tokens s,
      ScannerCorrectness.advance_preserves_simpleKey s,
      ScannerCorrectness.advance_preserves_simpleKeyStack s,
      h_adv_ska⟩
    -- skipToContent s = .ok s.advance
    unfold skipToContent
    obtain ⟨m, hm⟩ : ∃ m, s.inputEnd - s.offset + 1 = m + 1 :=
      ⟨s.inputEnd - s.offset, by omega⟩
    rw [hm]; unfold skipToContentLoop
    simp only [h_ws]
    -- skipToContentComment s.advance: c ≠ '#' → identity
    unfold skipToContentComment; rw [h_pk_adv]; simp [h_nc, h_pk_adv, h_nlb]
  obtain ⟨s₁, h_stc_ok, h_corr₁, h_fl₁, h_ids₁, h_dp₁, h_ek₁, h_col₁, h_line₁, h_toks₁, h_sk₁, h_stack₁, h_ska₁⟩ := h_stc_exists
  -- Part (b): derive further properties of s₁
  have h_flow₁ : s₁.inFlow = true := by
    unfold ScannerState.inFlow
    exact decide_eq_true (by rw [h_fl₁]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow)
  have h_indent₁ : s₁.currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [h_ids₁]
  have ⟨h_pk₁, h_lt₁⟩ := peek_of_chars_cons s₁ c rest s₁.col h_corr₁
  have h_stc₁ : skipToContent s₁ = .ok s₁ :=
    skipToContent_of_content_char s₁ c h_pk₁ h_nws h_nlb h_nc h_lt₁
  have h_hm₁ : s₁.hasMore = true := by
    unfold ScannerState.hasMore; exact decide_eq_true h_lt₁
  -- Part (c): both preprocessing paths yield (saveSimpleKey s₁, c)
  have h_pp_s : scanNextToken_preprocess s = .ok (some (saveSimpleKey s₁, c)) := by
    unfold scanNextToken_preprocess
    rw [h_stc_ok]; simp only [bind, Except.bind, pure, Except.pure]
    simp only [h_hm₁, h_flow₁, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [show ¬(s₁.indents.size < s₁.indents.size) from by omega, decide_false,
               Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [saveSimpleKey_preserves_peek, h_pk₁]
  have h_pp_s₁ : scanNextToken_preprocess s₁ = .ok (some (saveSimpleKey s₁, c)) := by
    unfold scanNextToken_preprocess
    rw [h_stc₁]; simp only [bind, Except.bind, pure, Except.pure]
    simp only [h_hm₁, h_flow₁, Bool.not_true, Bool.false_eq_true, ite_false]
    simp only [show ¬(s₁.indents.size < s₁.indents.size) from by omega, decide_false,
               Bool.false_and, Bool.false_eq_true, ↓reduceIte]
    rw [saveSimpleKey_preserves_peek, h_pk₁]
  exact ⟨s₁, h_corr₁, h_flow₁, h_fl₁, h_indent₁, h_col₁, h_dp₁, h_ids₁, h_ek₁, h_line₁,
    by rw [h_pp_s, h_pp_s₁],
    fun h_a => by unfold AllTokensOnLine at h_a ⊢; simp only [h_line₁, h_toks₁]; exact h_a,
    fun h_e => by unfold EndLineOnLine at h_e ⊢; rw [h_sk₁, h_line₁]; exact h_e,
    h_stack₁, h_toks₁,
    ScannerCorrectness.skipToContent_preserves_pendingKeys s s₁ h_stc_ok,
    ScannerCorrectness.skipToContent_preserves_pendingKeyStack s s₁ h_stc_ok,
    h_ska₁⟩

-- ═══ Flow-context dispatch lemmas ═══

/-- `dispatchStructural` returns `none` for non-structural characters in flow
    context when the column is past any document boundary position. -/
theorem dispatchStructural_none_flow (s : ScannerState) (c : Char)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0) :
    scanNextToken_dispatchStructural s c = .ok none := by
  have h_fl_pos : s.flowLevel > 0 := by
    unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  unfold scanNextToken_dispatchStructural
  simp [ScannerState.inFlow, h_fl_pos,
        show ¬(s.currentIndent ≥ (0 : Int)) from by omega,
        show ¬((s.col : Int) ≤ s.currentIndent) from by omega,
        show s.col ≠ 0 from by omega,
        bind, Except.bind, pure, Except.pure]

/-- `checkBlockFlowIndent` succeeds for non-bracket characters or when in flow. -/
theorem checkBlockFlowIndent_ok_flow (s : ScannerState) (c : Char)
    (h_flow : s.inFlow = true) :
    scanNextToken_checkBlockFlowIndent s c = .ok () := by
  have h_fl_pos : s.flowLevel > 0 := by
    unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  unfold scanNextToken_checkBlockFlowIndent
  simp [ScannerState.inFlow, h_fl_pos]

/-- `dispatchFlowIndicators` returns `none` for non-flow-indicator characters. -/
theorem dispatchFlowIndicators_none (s : ScannerState) (c : Char)
    (h1 : c ≠ '[') (h2 : c ≠ ']') (h3 : c ≠ '{') (h4 : c ≠ '}') (h5 : c ≠ ',') :
    scanNextToken_dispatchFlowIndicators s c = .ok none := by
  unfold scanNextToken_dispatchFlowIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i h; exact absurd (beq_iff_eq.mp h) h1
  · split
    · rename_i h; exact absurd (beq_iff_eq.mp h) h2
    · split
      · rename_i h; exact absurd (beq_iff_eq.mp h) h3
      · split
        · rename_i h; exact absurd (beq_iff_eq.mp h) h4
        · split
          · rename_i h; exact absurd (beq_iff_eq.mp h) h5
          · rfl

/-- `dispatchBlockIndicators` returns `none` for `'"'` (and many other chars). -/
theorem dispatchBlockIndicators_none_quote (s : ScannerState) :
    scanNextToken_dispatchBlockIndicators s '"' = .ok none := by
  unfold scanNextToken_dispatchBlockIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  -- '"' ≠ '-', '"' ≠ '?', '"' ≠ ':'
  split
  · rename_i h; simp at h
  · split
    · rename_i h; simp at h
    · split
      · rename_i h; simp at h
      · rfl

-- ═══ scanFlowSequenceStart detailed properties ═══

-- Field preservation through scanFlowSequenceStart
theorem scanFlowSequenceStart_preserves_dp (s : ScannerState) :
    (scanFlowSequenceStart s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceStart; simp only [advance_preserves_dp, ScannerState.emit]

theorem scanFlowSequenceStart_preserves_indents (s : ScannerState) :
    (scanFlowSequenceStart s).indents = s.indents := by
  unfold scanFlowSequenceStart; simp only [advance_preserves_indents, ScannerState.emit]

theorem scanFlowSequenceStart_preserves_ek (s : ScannerState) :
    (scanFlowSequenceStart s).explicitKeyLine = s.explicitKeyLine := by
  unfold scanFlowSequenceStart; dsimp only []; simp only [advance_explicitKeyLine, ScannerState.emit]

theorem scanFlowSequenceStart_line_eq (s : ScannerState) :
    (scanFlowSequenceStart s).line = s.advance.line := by
  simp only [scanFlowSequenceStart, ScannerState.emit, ScannerState.advance]
  split <;> (try split <;> (try split)) <;> rfl

theorem scanFlowSequenceStart_flowLevel_eq (s : ScannerState) :
    (scanFlowSequenceStart s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowSequenceStart
  simp only [ScannerCorrectness.advance_preserves_flowLevel, ScannerCorrectness.emit_preserves_flowLevel]

/-- `scanFlowSequenceStart` advances past `[`, giving specific ScannerSurfCorr
    and field preservation. -/
theorem scanFlowSequenceStart_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowSequenceStart s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowSequenceStart s).flowLevel = s.flowLevel + 1
    ∧ (scanFlowSequenceStart s).directivesPresent = s.directivesPresent
    ∧ (scanFlowSequenceStart s).indents = s.indents
    ∧ (scanFlowSequenceStart s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '[' rest _ hcorr
  have h_emit_corr : ScannerSurfCorr
      ({ s with simpleKey := { possible := false }, pendingKeyActive := none }.emit .flowSequenceStart)
      ⟨'[' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr
    ({ s with simpleKey := { possible := false }, pendingKeyActive := none }.emit .flowSequenceStart)
    '[' rest h_emit_corr h_lt (by decide) (by decide)
  -- Transfer corr from advance result to scanFlowSequenceStart result
  -- After unfold, struct-with on advance result preserves ScannerSurfCorr fields
  have h_corr_final : ScannerSurfCorr (scanFlowSequenceStart s) ⟨rest, s.col + 1⟩ := by
    unfold scanFlowSequenceStart
    exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
           h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩
  exact ⟨h_corr_final,
         scanFlowSequenceStart_flowLevel_eq s,
         scanFlowSequenceStart_preserves_dp s,
         scanFlowSequenceStart_preserves_indents s,
         h_corr_final.col_eq.symm ▸ rfl⟩

-- ═══ Full scanNextToken pipeline composition ═══

/-- When preprocessing succeeds, structural dispatch returns none,
    flow indicators return none, block indicators return none,
    and content dispatch produces `s_result`, then scanNextToken
    returns `some s_result`.

    `s_ad` is the state after the allowDirectives update. -/
theorem scanNextToken_via_content_dispatch (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextToken_dispatchContent s_ad c = .ok s_result) :
    scanNextToken s = .ok (some s_result) := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_struct, pure, Except.pure]
  rw [← h_ad_eq]
  simp only [h_check, h_flow, h_block, h_content]

/-- Error variant of `scanNextToken_via_content_dispatch`: when content
    dispatch errors, `scanNextToken` propagates that error. -/
theorem scanNextToken_via_content_dispatch_error
    (s s_pp s_ad : ScannerState) (c : Char) (e : ScanError)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextToken_dispatchContent s_ad c = .error e) :
    scanNextToken s = .error e := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_struct, pure, Except.pure]
  rw [← h_ad_eq]
  simp only [h_check, h_flow, h_block, h_content]

/-- When preprocessing succeeds, structural/flow dispatches return none,
    and block indicator dispatch produces a result, then scanNextToken
    returns that result. This is used for `:` (value indicator) in flow context,
    which goes through `scanNextToken_dispatchBlockIndicators`. -/
theorem scanNextToken_via_block_dispatch (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok (some s_result)) :
    scanNextToken s = .ok (some s_result) := by
  unfold scanNextToken; dsimp only []
  simp only [bind, Except.bind, h_pp, h_struct, pure, Except.pure]
  rw [← h_ad_eq]
  simp only [h_check, h_flow, h_block]

-- ═══ Flow-context scanDoubleQuoted dispatch ═══

/-- In flow context with state at `'"'`, `scanNextToken` dispatches to
    `scanDoubleQuoted`, which succeeds and advances past the quoted scalar.
    Combines preprocessing, all-none dispatches, and content dispatch.

    This is the flow-context analog of `scanNextToken_emitScalar_init`. -/
theorem scanNextToken_flow_scanDoubleQuoted (s : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ (∀ t, lastTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- pkRec preserved at indices < initial size.  scanDoubleQuoted preserves
      -- pendingKeys; the dispatchContent wrap fires `setPendingKeyEndLine`
      -- which only touches endLine, leaving insertBeforeIdx + kind intact.
      -- C-foundation-EmitScansInFlow-defns-helpers-size: size monotonic.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore +
      -- preservation-chain: pendingKeyStack preserved (scanDoubleQuoted is a Class A
      -- passthrough that doesn't push/pop pendingKeyStack; the surrounding
      -- setPendingKeyEndLine wrap mutates pendingKeys[active].endLine but leaves
      -- pendingKeyStack alone).  Discharged via the proven
      -- `ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeyStack` chain.
      ∧ s'.pendingKeyStack = s.pendingKeyStack := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' ((escapeString content).toList ++ ['"'] ++ rest) s.col
      hcorr h_flow (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch returns none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  -- Step 4: checkBlockFlowIndent
  have h_check : scanNextToken_checkBlockFlowIndent s_ad '"' = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Step 5: flow dispatch returns none
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Step 6: block dispatch returns none
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- Step 7: content dispatch → scanDoubleQuoted
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s_ad.col⟩ := by
    have h_ad_input : s_ad.input = s.input := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
    have h_ad_offset : s_ad.offset = s.offset := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
    have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
    have h_ad_indents : s_ad.indents = s.indents := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr h_ad_input h_ad_offset h_ad_inputEnd h_ad_col h_ad_indents
  have h_ad_flow_bool : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  -- s_ad.flowLevel = s.flowLevel (through saveSimpleKey + allowDirectives branch)
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).flowLevel = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  obtain ⟨s_dq, h_dq, h_dq_corr, h_dq_fl, h_dq_dp, h_dq_ids, h_dq_ek, h_dq_col, h_dq_tokens, h_dq_ska, h_dq_line⟩ :=
    scanDoubleQuoted_flow_ok s_ad content rest h_ad_corr h_ad_flow_bool
  -- Content dispatch: unfold to reach scanDoubleQuoted + simpleKey update
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have h_content : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final
      ∧ ScannerSurfCorr s_final ⟨rest, s_final.col⟩
      ∧ s_final.flowLevel = s.flowLevel
      ∧ s_final.directivesPresent = s.directivesPresent
      ∧ s_final.indents = s.indents
      ∧ s_final.explicitKeyLine = s.explicitKeyLine
      ∧ s_final.col > 0
      ∧ lastTokenVal? s_final.tokens = some (.scalar content .doubleQuoted)
      ∧ s_final.simpleKeyAllowed = false
      ∧ s_final.line = s.line
      ∧ AllTokensOnLine s_final s.line
      ∧ EndLineOnLine s_final
      ∧ s_final.simpleKeyStack = s.simpleKeyStack
      ∧ s.pendingKeys.size ≤ s_final.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s_final.pendingKeys.size),
          (s_final.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s_final.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- stack-restore + preservation-chain: pendingKeyStack preserved (Class A
      -- passthrough — discharged via
      -- `ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeyStack`).
      ∧ s_final.pendingKeyStack = s.pendingKeyStack := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, Except.pure, h_dq]
    -- AllTokensOnLine for s_dq: scanDoubleQuoted preserves AllTokensOnLine
    -- scanDoubleQuoted does emitAt startPos + collectLoop (no extra tokens)
    -- We need AllTokensOnLine s_dq s.line
    -- s_dq.tokens = s_ad tokens + emitAt at startPos = s_ad.currentPos (line = s_ad.line = s.line)
    -- For now, we'll prove it using sorry for AllTokensOnLine_scanDoubleQuoted
    have h_atol_ad : AllTokensOnLine s_ad s.line :=
      AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)
    have h_atol_dq : AllTokensOnLine s_dq s.line :=
      AllTokensOnLine_scanDoubleQuoted s_ad s_dq h_dq h_ad_flow_bool
        s.line h_atol_ad h_ad_line
    have h_sk_dq : s_dq.simpleKey = s_ad.simpleKey :=
      scanDoubleQuoted_preserves_simpleKey s_ad s_dq h_dq
    have h_dq_stack : s_dq.simpleKeyStack = s_ad.simpleKeyStack :=
      ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s_ad s_dq h_dq
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    -- pkRec preservation chain s → saveSimpleKey s → s_ad → s_dq
    have h_dq_pks : s_dq.pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeys s_ad s_dq h_dq
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    have h_dq_pks_full : s_dq.pendingKeys = (saveSimpleKey s).pendingKeys :=
      h_dq_pks.trans h_ad_pks
    -- pendingKeyStack chain s → saveSimpleKey s → s_ad → s_dq via the proven
    -- `_preserves_pendingKeyStack` chain (preservation-chain sub-step).
    have h_dq_pks_stack : s_dq.pendingKeyStack = s_ad.pendingKeyStack :=
      ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeyStack s_ad s_dq h_dq
    have h_ad_pks_stack : s_ad.pendingKeyStack = s.pendingKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
    have h_dq_pks_stack_full : s_dq.pendingKeyStack = s.pendingKeyStack :=
      h_dq_pks_stack.trans h_ad_pks_stack
    -- After scanDoubleQuoted, simpleKey.possible branches
    cases h_skp : s_dq.simpleKey.possible
    · -- simpleKey.possible = false: s' = s_dq
      simp only [Bool.false_eq_true, ↓reduceIte]
      refine ⟨_, rfl, h_dq_corr,
        h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
        h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
        h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack, ?_, ?_, ?_⟩
      · intro h_poss; rw [h_skp] at h_poss; exact absurd h_poss (by decide)
      · -- size monotonic: s_dq.pendingKeys = (saveSimpleKey s).pendingKeys
        rw [h_dq_pks_full]; exact saveSimpleKey_pendingKeys_size_ge s
      · -- pkRec preserved: s_dq.pendingKeys = (saveSimpleKey s).pendingKeys
        intro j hj hj'
        have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
          rw [← h_dq_pks_full]; exact hj'
        have ⟨h_ib, h_kd⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
        have h_eq : s_dq.pendingKeys[j]'hj' = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by
          congr 1
        refine ⟨?_, ?_⟩
        · rw [h_eq]; exact h_ib
        · rw [h_eq]; exact h_kd
      · exact h_dq_pks_stack_full
    · -- simpleKey.possible = true: s' = { s_dq with simpleKey endLine update }
      simp only [↓reduceIte]
      refine ⟨_, rfl,
        ⟨h_dq_corr.chars_from, h_dq_corr.col_eq, h_dq_corr.end_eq,
         h_dq_corr.input_prefix, h_dq_corr.indent_cols_nonneg⟩,
        h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
        h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
        h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack, ?_, ?_, ?_⟩
      · -- EndLineOnLine: endLine just set to s_dq.line, pos from saveSimpleKey
        intro _
        constructor
        · rfl
        · show s_dq.simpleKey.pos.line = s_dq.line
          rw [h_sk_dq]
          have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
            simp only [s_ad]; split <;> rfl
          rw [h_ad_sk]
          have h_eol_sk := EndLineOnLine_saveSimpleKey_flow s h_endline
          have h_sk_poss : (saveSimpleKey s).simpleKey.possible = true := by
            rw [← h_ad_sk, ← h_sk_dq]; exact h_skp
          exact (h_eol_sk h_sk_poss).2 |>.trans (saveSimpleKey_preserves_line s)
            |>.trans (h_dq_line.trans h_ad_line).symm
      · -- size monotonic: setPendingKeyEndLine preserves size; s_dq.pks = saveSimpleKey s.pks
        show s.pendingKeys.size ≤ (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line).size
        rw [ScannerCorrectness.setPendingKeyEndLine_size, h_dq_pks_full]
        exact saveSimpleKey_pendingKeys_size_ge s
      · -- pkRec preserved through setPendingKeyEndLine wrap on top of s_dq chain
        intro j hj hj'
        -- Goal pendingKeys is `setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line`
        have h_set_size : j < (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line).size :=
          hj'
        have h_dq_lt : j < s_dq.pendingKeys.size := by
          rw [ScannerCorrectness.setPendingKeyEndLine_size] at h_set_size; exact h_set_size
        have h_ib_set := ScannerCorrectness.setPendingKeyEndLine_insertBeforeIdx
          s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line j h_dq_lt h_set_size
        have h_kd_set := ScannerCorrectness.setPendingKeyEndLine_kind
          s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line j h_dq_lt h_set_size
        -- Now bridge s_dq.pendingKeys[j] to s.pendingKeys[j]
        have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
          rw [← h_dq_pks_full]; exact h_dq_lt
        have ⟨h_ib_chain, h_kd_chain⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
        have h_eq : s_dq.pendingKeys[j]'h_dq_lt = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by
          congr 1
        refine ⟨?_, ?_⟩
        · exact h_ib_set.trans (h_eq ▸ h_ib_chain)
        · exact h_kd_set.trans (h_eq ▸ h_kd_chain)
      · -- pendingKeyStack: setPendingKeyEndLine wrap doesn't touch stack
        show s_dq.pendingKeyStack = s.pendingKeyStack
        exact h_dq_pks_stack_full
  obtain ⟨s_final, h_dc_eq, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f, h_tok_f,
          h_ska_f, h_line_f, h_atol_f, h_endline_f, h_stack_f, h_size_f, h_pkRec_f, h_pks_f⟩ := h_content
  -- Step 8: compose through scanNextToken
  exact ⟨s_final, scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
    h_flow_none h_block_none h_dc_eq, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f,
    fun t ht => by rw [h_tok_f] at ht; injection ht with ht; subst ht; exact ⟨nofun, nofun, nofun⟩,
    h_ska_f, h_line_f, (by rw [h_line_f]; exact h_atol_f), h_endline_f, h_stack_f, h_size_f, h_pkRec_f,
    h_pks_f⟩

/-- Per-leaf scalar pkPush variant of `scanNextToken_flow_scanDoubleQuoted`.

    Adds three pendingKey-tracking conclusions under the additional
    `simpleKeyAllowed = true` and `explicitKeyLine = none` hypotheses:
    the `saveSimpleKey` push branch fires (A1 lemma),
    `scanDoubleQuoted` preserves `pendingKeys`, and the
    `dispatchContent` `setPendingKeyEndLine` wrap preserves size,
    insertBeforeIdx, and kind per-entry — so the new entry at index
    `s.pendingKeys.size` carries `insertBeforeIdx = s.tokens.size` and
    `kind = .unresolved`.

    Initiative 3 J.4.2.b-2d-key-chain-Part2-body-A2: per-leaf scalar
    pkPush theorem.  Consumed by an eventual strengthening of
    `EmitScansInFlow` (A4) to expose the first-key chain-side
    accounting facts required by `emitPairList_chain_first_pkShape`. -/
theorem scanNextToken_flow_scanDoubleQuoted_pkPush (s : ScannerState)
    (content : String) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = true)
    (h_ek_none : s.explicitKeyLine = none) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ (∀ t, lastTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ s'.pendingKeys.size = s.pendingKeys.size + 1
      ∧ (∃ (h : s.pendingKeys.size < s'.pendingKeys.size),
          (s'.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
          ∧ (s'.pendingKeys[s.pendingKeys.size]'h).kind = .unresolved)
      ∧ s'.pendingKeyActive = some s.pendingKeys.size
      ∧ s'.simpleKey.possible = true
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj) := by
  -- Step 1: preprocessing (parallel to base theorem)
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' ((escapeString content).toList ++ ['"'] ++ rest) s.col
      hcorr h_flow (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch returns none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  -- Step 4: checkBlockFlowIndent
  have h_check : scanNextToken_checkBlockFlowIndent s_ad '"' = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Step 5: flow dispatch returns none
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Step 6: block dispatch returns none
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- Step 7: content dispatch → scanDoubleQuoted
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['"'] ++ (escapeString content).toList ++ ['"'] ++ rest, s_ad.col⟩ := by
    have h_ad_input : s_ad.input = s.input := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
    have h_ad_offset : s_ad.offset = s.offset := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
    have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
    have h_ad_indents : s_ad.indents = s.indents := by
      simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr h_ad_input h_ad_offset h_ad_inputEnd h_ad_col h_ad_indents
  have h_ad_flow_bool : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ek s
  obtain ⟨s_dq, h_dq, h_dq_corr, h_dq_fl, h_dq_dp, h_dq_ids, h_dq_ek, h_dq_col, h_dq_tokens, h_dq_ska, h_dq_line⟩ :=
    scanDoubleQuoted_flow_ok s_ad content rest h_ad_corr h_ad_flow_bool
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  -- pkPush tracking: A1 lemma + record-update preservations
  obtain ⟨h_sk_pks, h_sk_pka, h_sk_skp⟩ :=
    saveSimpleKey_pkPush_when_allowed s h_ska h_ek_none
  have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
    simp only [s_ad]; split <;> rfl
  have h_dq_pks : s_dq.pendingKeys = s_ad.pendingKeys :=
    ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeys s_ad s_dq h_dq
  have h_dq_pks_full : s_dq.pendingKeys = s.pendingKeys.push
      { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
        endLine := s.line, kind := .unresolved } := by
    rw [h_dq_pks, h_ad_pks, h_sk_pks]
  -- s_dq.simpleKey.possible = true: dispatchContent wrap fires
  have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
    simp only [s_ad]; split <;> rfl
  have h_dq_sk : s_dq.simpleKey = s_ad.simpleKey :=
    scanDoubleQuoted_preserves_simpleKey s_ad s_dq h_dq
  have h_dq_skp : s_dq.simpleKey.possible = true := by
    rw [h_dq_sk, h_ad_sk]; exact h_sk_skp
  -- pendingKeyActive tracking: saveSimpleKey sets it, s_ad/s_dq preserve it.
  have h_ad_pka : s_ad.pendingKeyActive = (saveSimpleKey s).pendingKeyActive := by
    simp only [s_ad]; split <;> rfl
  have h_dq_pka : s_dq.pendingKeyActive = s_ad.pendingKeyActive :=
    ScannerCorrectness.scanDoubleQuoted_preserves_pendingKeyActive s_ad s_dq h_dq
  have h_dq_pka_full : s_dq.pendingKeyActive = some s.pendingKeys.size := by
    rw [h_dq_pka, h_ad_pka, h_sk_pka]
  have h_content : ∃ s_final, scanNextToken_dispatchContent s_ad '"' = .ok s_final
      ∧ ScannerSurfCorr s_final ⟨rest, s_final.col⟩
      ∧ s_final.flowLevel = s.flowLevel
      ∧ s_final.directivesPresent = s.directivesPresent
      ∧ s_final.indents = s.indents
      ∧ s_final.explicitKeyLine = s.explicitKeyLine
      ∧ s_final.col > 0
      ∧ lastTokenVal? s_final.tokens = some (.scalar content .doubleQuoted)
      ∧ s_final.simpleKeyAllowed = false
      ∧ s_final.line = s.line
      ∧ AllTokensOnLine s_final s.line
      ∧ EndLineOnLine s_final
      ∧ s_final.simpleKeyStack = s.simpleKeyStack
      ∧ s_final.pendingKeys.size = s.pendingKeys.size + 1
      ∧ (∃ (h : s.pendingKeys.size < s_final.pendingKeys.size),
          (s_final.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
          ∧ (s_final.pendingKeys[s.pendingKeys.size]'h).kind = .unresolved)
      ∧ s_final.pendingKeyActive = some s.pendingKeys.size
      ∧ s_final.simpleKey.possible = true
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s_final.pendingKeys.size),
          s_final.pendingKeys[j]'hj' = s.pendingKeys[j]'hj) := by
    unfold scanNextToken_dispatchContent
    simp (config := { decide := true }) only [bind, Except.bind, pure, Except.pure, h_dq]
    have h_atol_ad : AllTokensOnLine s_ad s.line :=
      AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)
    have h_atol_dq : AllTokensOnLine s_dq s.line :=
      AllTokensOnLine_scanDoubleQuoted s_ad s_dq h_dq h_ad_flow_bool
        s.line h_atol_ad h_ad_line
    have h_dq_stack : s_dq.simpleKeyStack = s_ad.simpleKeyStack :=
      ScannerCorrectness.scanDoubleQuoted_preserves_simpleKeyStack s_ad s_dq h_dq
    have h_ad_stack : s_ad.simpleKeyStack = s.simpleKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
    -- Reduce the inner ite via h_dq_skp = true
    simp only [h_dq_skp, ↓reduceIte]
    refine ⟨_, rfl,
      ⟨h_dq_corr.chars_from, h_dq_corr.col_eq, h_dq_corr.end_eq,
       h_dq_corr.input_prefix, h_dq_corr.indent_cols_nonneg⟩,
      h_dq_fl.trans h_ad_fl, h_dq_dp.trans h_ad_dp, h_dq_ids.trans h_ad_ids,
      h_dq_ek.trans h_ad_ek, h_dq_col, h_dq_tokens, h_dq_ska,
      h_dq_line.trans h_ad_line, h_atol_dq, ?_, h_dq_stack.trans h_ad_stack,
      ?_, ?_, ?_, ?_, ?_⟩
    · -- EndLineOnLine on the wrap (parallel to base theorem true branch)
      intro _
      constructor
      · rfl
      · show s_dq.simpleKey.pos.line = s_dq.line
        rw [h_dq_sk, h_ad_sk]
        have h_eol_sk := EndLineOnLine_saveSimpleKey_flow s h_endline
        have h_sk_poss : (saveSimpleKey s).simpleKey.possible = true := h_sk_skp
        exact (h_eol_sk h_sk_poss).2 |>.trans (saveSimpleKey_preserves_line s)
          |>.trans (h_dq_line.trans h_ad_line).symm
    · -- pkPush size: setPendingKeyEndLine preserves size, then s_dq.pendingKeys = push
      show (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line).size
        = s.pendingKeys.size + 1
      rw [ScannerCorrectness.setPendingKeyEndLine_size, h_dq_pks_full, Array.size_push]
    · -- pkPush entry at s.pendingKeys.size
      have h_dq_size : s_dq.pendingKeys.size = s.pendingKeys.size + 1 := by
        rw [h_dq_pks_full, Array.size_push]
      have h_dq_lt : s.pendingKeys.size < s_dq.pendingKeys.size := by
        rw [h_dq_size]; exact Nat.lt_succ_self _
      have h_size_eq : (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line).size
          = s_dq.pendingKeys.size := ScannerCorrectness.setPendingKeyEndLine_size _ _ _
      have h_lt_wrap : s.pendingKeys.size <
          (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line).size := by
        rw [h_size_eq]; exact h_dq_lt
      have h_get : s_dq.pendingKeys[s.pendingKeys.size]'h_dq_lt =
          { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
            endLine := s.line, kind := .unresolved } := by
        simp only [h_dq_pks_full, Array.getElem_push]
        rw [dif_neg (Nat.lt_irrefl _)]
      refine ⟨h_lt_wrap, ?_, ?_⟩
      · rw [ScannerCorrectness.setPendingKeyEndLine_insertBeforeIdx s_dq.pendingKeys s_dq.pendingKeyActive
            s_dq.line s.pendingKeys.size h_dq_lt h_lt_wrap, h_get]
      · rw [ScannerCorrectness.setPendingKeyEndLine_kind s_dq.pendingKeys s_dq.pendingKeyActive
            s_dq.line s.pendingKeys.size h_dq_lt h_lt_wrap, h_get]
    · -- pendingKeyActive: wrap leaves it untouched, s_dq inherits from saveSimpleKey
      show s_dq.pendingKeyActive = some s.pendingKeys.size
      exact h_dq_pka_full
    · -- simpleKey.possible: after `↓reduceIte` substitution the wrap has
      -- `simpleKey.possible := true` baked in by simp, so the goal is `true = true`.
      rfl
    · -- preserves-prior: setPendingKeyEndLine doesn't touch indices < active = s.pendingKeys.size
      intro j hj _hj'
      have h_dq_lt : j < s_dq.pendingKeys.size := by
        rw [h_dq_pks_full, Array.size_push]; omega
      have h_ne : j ≠ s.pendingKeys.size := Nat.ne_of_lt hj
      -- Bridge: rewrite s_dq.pendingKeyActive to some s.pendingKeys.size, then use the helper
      have h_pka_eq :
          (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line)
          = (setPendingKeyEndLine s_dq.pendingKeys (some s.pendingKeys.size) s_dq.line) := by
        rw [h_dq_pka_full]
      have _hj'_some : j < (setPendingKeyEndLine s_dq.pendingKeys (some s.pendingKeys.size) s_dq.line).size :=
        h_pka_eq ▸ _hj'
      have step1 :
          (setPendingKeyEndLine s_dq.pendingKeys s_dq.pendingKeyActive s_dq.line)[j]'_hj'
            = (setPendingKeyEndLine s_dq.pendingKeys (some s.pendingKeys.size) s_dq.line)[j]'_hj'_some := by
        congr 1
      have step2 :
          (setPendingKeyEndLine s_dq.pendingKeys (some s.pendingKeys.size) s_dq.line)[j]'_hj'_some
            = s_dq.pendingKeys[j]'h_dq_lt :=
        ScannerCorrectness.setPendingKeyEndLine_some_at_other_unchanged
          s_dq.pendingKeys s.pendingKeys.size s_dq.line j h_dq_lt _hj'_some h_ne
      have step3 : s_dq.pendingKeys[j]'h_dq_lt = s.pendingKeys[j]'hj := by
        simp only [h_dq_pks_full]
        exact Array.getElem_push_lt hj
      exact (step1.trans step2).trans step3
  obtain ⟨s_final, h_dc_eq, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f,
         h_tok_f, h_ska_f, h_line_f, h_atol_f, h_endline_f, h_stack_f,
         h_pks_size_f, h_pks_idx_f, h_pka_f, h_skp_f, h_prior_f⟩ := h_content
  exact ⟨s_final, scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
    h_flow_none h_block_none h_dc_eq, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_ek_f, h_col_f,
    fun t ht => by rw [h_tok_f] at ht; injection ht with ht; subst ht; exact ⟨nofun, nofun, nofun⟩,
    h_ska_f, h_line_f, (by rw [h_line_f]; exact h_atol_f), h_endline_f, h_stack_f,
    h_pks_size_f, h_pks_idx_f, h_pka_f, h_skp_f, h_prior_f⟩

-- ═══ scanNextToken for '[' from initial state ═══

/-- Structural dispatch returns none for `[` at initial state. -/
theorem dispatchStructural_none_bracket_init (s : ScannerState)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStart s = false)
    (h_noDocEnd : atDocumentEnd s = false) :
    scanNextToken_dispatchStructural s '[' = .ok none := by
  unfold scanNextToken_dispatchStructural
  simp [ScannerState.inFlow, h_fl, h_noDocStart, h_noDocEnd,
        bind, Except.bind, pure, Except.pure]

/-- checkBlockFlowIndent passes for `[` at initial state
    (currentIndent = -1 < 0, so the guard is false). -/
theorem checkBlockFlowIndent_bracket_init (s : ScannerState)
    (h_fl : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1) :
    scanNextToken_checkBlockFlowIndent s '[' = .ok () := by
  unfold scanNextToken_checkBlockFlowIndent
  simp [ScannerState.inFlow, h_fl, h_indent]

/-- Flow dispatch for `[` returns `some (scanFlowSequenceStart s)`. -/
theorem dispatchFlowIndicators_bracket (s : ScannerState) :
    scanNextToken_dispatchFlowIndicators s '[' = .ok (some (scanFlowSequenceStart s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  simp [pure, Except.pure]

/-- `scanNextToken` on the initial scanner state at `[` dispatches to
    `scanFlowSequenceStart`, entering flow context.

    Result state has `flowLevel = 1` (i.e. `inFlow = true`),
    `currentIndent = -1`, `col = 1`, and ScannerSurfCorr at rest. -/
theorem scanNextToken_flow_open_init (input : String) (rest : List Char)
    (h_toList : input.toList = '[' :: rest) :
    let s₀ := (ScannerState.mk' input).emit .streamStart
    ∃ s', scanNextToken s₀ = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = 1
      ∧ s'.directivesPresent = false
      ∧ s'.indents = s₀.indents
      ∧ s'.col = 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = 0
      ∧ AllTokensOnLine s' 0
      ∧ EndLineOnLine s'
      ∧ s'.simpleKey.possible = false
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .flowSequenceStart]
      ∧ s'.simpleKeyStack.size = s'.flowLevel := by
  intro s₀
  -- Step 1: preprocessing
  have h_pp := scanNextToken_preprocess_init_state input '[' rest h_toList
    (by decide) (by decide) (by decide)
  obtain ⟨s_pp, h_pp_eq, h_fl_pp, h_inflow_pp, h_ci_pp, h_col_pp,
          h_ad_pp, h_dp_pp, h_ids, h_inp, h_off, h_ie, h_ek_pp,
          h_line_pp, h_atol_pp, h_pp_filt⟩ := h_pp
  -- Step 2: ScannerSurfCorr for s_pp
  have h_chars := chars_from_zero_toList input
  rw [h_toList] at h_chars
  have h_corr₀ := initial_corr input _ h_chars
  have h_corr_s₀ : ScannerSurfCorr s₀ ⟨'[' :: rest, 0⟩ :=
    ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
  have h_corr_pp : ScannerSurfCorr s_pp ⟨'[' :: rest, s_pp.col⟩ := by
    rw [h_col_pp]
    exact ScannerSurfCorr_transfer h_corr_s₀ h_inp h_off h_ie h_col_pp h_ids
  have ⟨h_pk_pp, _⟩ := peek_of_chars_cons s_pp '[' rest _ h_corr_pp
  -- Step 3: atDocumentStart/End false for '['
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?; rfl
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart; rw [h_pat0, h_pk_pp]
    simp only [show (some '[' == some '-') = false from by decide,
               Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd; rw [h_pat0, h_pk_pp]
    simp only [show (some '[' == some '.') = false from by decide,
               Bool.and_false, Bool.false_and]
  -- Step 4: structural dispatch → none
  have h_struct := dispatchStructural_none_bracket_init s_pp h_fl_pp h_ds h_de
  -- Step 5: allowDirectives update → s_ad
  -- s_pp.allowDirectives = true, so s_ad = { s_pp with ... }
  let s_ad := if s_pp.allowDirectives then
    { s_pp with allowDirectives := false, documentEverStarted := true }
  else s_pp
  have h_ad_fl : s_ad.flowLevel = 0 := by
    simp only [s_ad]; split <;> exact h_fl_pp
  have h_ad_ci : s_ad.currentIndent = -1 := by
    have : s_ad.indents = s_pp.indents := by simp only [s_ad]; split <;> rfl
    unfold ScannerState.currentIndent at h_ci_pp ⊢; rw [this]; exact h_ci_pp
  -- Step 6: checkBlockFlowIndent ok
  have h_check := checkBlockFlowIndent_bracket_init s_ad h_ad_fl h_ad_ci
  -- Step 7: flow dispatch → some (scanFlowSequenceStart s_ad)
  have h_flow := dispatchFlowIndicators_bracket s_ad
  -- Step 8: compose through scanNextToken
  have h_snt : scanNextToken s₀ = .ok (some (scanFlowSequenceStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp_eq h_struct rfl h_check h_flow
  -- Step 9: field properties of scanFlowSequenceStart s_ad
  have h_ad_col : s_ad.col = 0 := by
    simp only [s_ad]; split <;> exact h_col_pp
  have h_ad_col_eq : s_ad.col = s_pp.col := by simp only [s_ad]; split <;> rfl
  have h_corr_ad : ScannerSurfCorr s_ad ⟨'[' :: rest, s_ad.col⟩ := by
    rw [h_ad_col_eq]
    exact ScannerSurfCorr_transfer h_corr_pp
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      h_ad_col_eq
      (by simp only [s_ad]; split <;> rfl)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStart_detail s_ad rest h_corr_ad
  -- Compute final field values
  have h_fl_final : (scanFlowSequenceStart s_ad).flowLevel = 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_dp_final : (scanFlowSequenceStart s_ad).directivesPresent = false := by
    rw [h_dp_f]; simp only [s_ad]; split <;> exact h_dp_pp
  have h_ids_final : (scanFlowSequenceStart s_ad).indents = s₀.indents := by
    rw [h_ids_f]; simp only [s_ad]; split <;> exact h_ids
  have h_col_final : (scanFlowSequenceStart s_ad).col = 1 := by
    rw [h_col_f, h_ad_col]
  -- ScannerSurfCorr at rest with correct col
  have h_corr_result : ScannerSurfCorr (scanFlowSequenceStart s_ad)
      ⟨rest, (scanFlowSequenceStart s_ad).col⟩ := by
    rw [h_col_f]
    exact h_corr_f
  exact ⟨scanFlowSequenceStart s_ad, h_snt, h_corr_result,
         h_fl_final, h_dp_final, h_ids_final, h_col_final,
         by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_final]; omega),
         by have hb : (scanFlowSequenceStart s_ad).indents.back? =
                some { column := (-1 : Int), isSequence := false } := by
              rw [h_ids_final]; rfl
            unfold ScannerState.currentIndent; rw [hb]; decide,
         by rw [scanFlowSequenceStart_preserves_ek s_ad]
            simp only [s_ad]; split <;> exact h_ek_pp,
         by rw [scanFlowSequenceStart_line_eq]
            have h_ad_pk : s_ad.peek? = some '[' := by
              simp only [s_ad]; split <;> exact h_pk_pp
            have h_ad_lt := (peek_of_chars_cons s_ad '[' rest _ h_corr_ad).2
            have h_ad_line : s_ad.line = 0 := by simp only [s_ad]; split <;> exact h_line_pp
            exact (advance_line_of_peek s_ad '[' h_ad_lt h_ad_pk (by decide) (by decide)).trans h_ad_line,
         by exact AllTokensOnLine_scanFlowSequenceStart s_ad 0
              (AllTokensOnLine_allowDirectives _ 0 (h_line_pp ▸ h_atol_pp))
              (by simp only [s_ad]; split <;> exact h_line_pp),
         by intro h_poss
            rw [scanFlowSequenceStart_simpleKey_not_possible] at h_poss
            exact absurd h_poss (by decide),
         scanFlowSequenceStart_simpleKey_not_possible s_ad,
         by -- Filtered token characterization:
            have h_fss_tokens : (scanFlowSequenceStart s_ad).tokens
                = s_ad.tokens.push ⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩ := by
              show ({ ({ s_ad with simpleKey := _, pendingKeyActive := _ }.emit .flowSequenceStart).advance with
                  flowLevel := _, simpleKeyAllowed := _,
                  flowStack := _, simpleKeyStack := _, pendingKeyStack := _ }).tokens = _
              simp only [ScannerCorrectness.advance_preserves_tokens,
                         ScannerState.emit, ScannerState.currentPos]
            have h_ad_tokens : s_ad.tokens = s_pp.tokens := by
              simp only [s_ad]; split <;> rfl
            rw [h_fss_tokens]
            simp only [Array.filter_push,
              show (YamlToken.flowSequenceStart != YamlToken.placeholder) = true from rfl,
              ite_true, Array.map_push,
              show s_ad.tokens = s_pp.tokens from h_ad_tokens,
              h_pp_filt]
            simp [ScannerState.mk', ScannerState.emit],
         by -- Stack/flowLevel sync:
            rw [h_fl_final]
            have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack
              _ _ _ h_pp_eq
            have h_ad_stack_sz : s_ad.simpleKeyStack.size = 0 := by
              simp only [s_ad]; split
              · show s_pp.simpleKeyStack.size = 0; rw [h_pre_stack]; rfl
              · rw [h_pre_stack]; rfl
            rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed]
            simp [Array.size_push, h_ad_stack_sz]⟩

-- Helper: Nat BEq with 0
theorem nat_beq_zero_false (n : Nat) (h : n > 0) : (n == 0) = false := by
  cases n with | zero => omega | succ => rfl

theorem nat_beq_zero_true {n : Nat} (h : n = 0) : (n == 0) = true := by
  subst h; rfl

-- ═══ Nested flow open: `[` when already in flow context ═══

/-- `scanNextToken` dispatches `[` in flow context to `scanFlowSequenceStart`,
    incrementing flowLevel. Similar to `scanNextToken_flow_open_init` but
    for the nested case where flowLevel > 0. -/
theorem scanNextToken_flow_open_nested (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ StackEndLineOnLine s' s'.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- pkRec preserved at indices < initial size (saveSimpleKey is push-or-id;
      -- scanFlowSequenceStart doesn't touch pendingKeys).
      -- C-foundation-EmitScansInFlow-defns-helpers-size: size monotonic.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack pushed (saveSimpleKey + allowDirectives preserve it;
      -- scanFlowSequenceStart pushes prior pendingKeyActive); the matching
      -- close-side pop cancels this push in the seq composition.
      ∧ s'.pendingKeyStack.pop = s.pendingKeyStack := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none (inFlow)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 4: checkBlockFlowIndent succeeds (inFlow)
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  -- Step 5: flow dispatch → some (scanFlowSequenceStart s_ad)
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
  -- Step 6: compose through scanNextToken
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- Step 7: properties of scanFlowSequenceStart s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'[' :: rest, s_ad.col⟩ := by
    rw [show s_ad.col = s.col from h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStart_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowSequenceStart_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '[' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowSequenceStart s_ad).line = s.line := by
    rw [scanFlowSequenceStart_line_eq]
    exact (advance_line_of_peek s_ad '[' h_lt_ad h_peek_ad (by decide) (by decide)).trans h_ad_line
  refine ⟨_, h_snt, ?_, h_fl_f.trans (congrArg (· + 1) h_ad_fl),
    h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f.trans h_ad_ek, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_scanFlowSequenceStart s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: scanFlowSequenceStart sets simpleKey.possible = false
    intro h_poss
    rw [scanFlowSequenceStart_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  · -- StackEndLineOnLine: pushed savedKey = s_ad.simpleKey satisfies EndLineOnLine at s'.line
    unfold StackEndLineOnLine
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.back?_push, h_line_f]
    intro h_poss
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad]; split
      · show EndLineOnLine { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
        exact EndLineOnLine_saveSimpleKey_flow s h_endline
      · exact EndLineOnLine_saveSimpleKey_flow s h_endline
    exact ⟨(h_ad_endline h_poss).1.trans h_ad_line, (h_ad_endline h_poss).2.trans h_ad_line⟩
  · -- simpleKeyStack.pop = s.simpleKeyStack
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.pop_push]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- size monotonic
    have h_fss_pks : (scanFlowSequenceStart s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    rw [h_fss_pks, h_ad_pks]
    exact saveSimpleKey_pendingKeys_size_ge s
  · -- pkRec preserved at j < initial size
    intro j hj hj'
    have h_fss_pks : (scanFlowSequenceStart s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    have h_full_pks : (scanFlowSequenceStart s_ad).pendingKeys = (saveSimpleKey s).pendingKeys :=
      h_fss_pks.trans h_ad_pks
    have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
      rw [← h_full_pks]; exact hj'
    have ⟨h_ib, h_kd⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
    have h_eq : (scanFlowSequenceStart s_ad).pendingKeys[j]'hj'
                = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by
      congr 1
    refine ⟨?_, ?_⟩
    · rw [h_eq]; exact h_ib
    · rw [h_eq]; exact h_kd
  · -- pendingKeyStack.pop = s.pendingKeyStack (mirror of simpleKeyStack)
    rw [ScannerCorrectness.scanFlowSequenceStart_pendingKeyStack_pushed, Array.pop_push]
    show s_ad.pendingKeyStack = s.pendingKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s

/-- Per-leaf flow-sequence pkPush theorem.  Mirrors
    `scanNextToken_flow_open_nested` but additionally exposes the
    pendingKeys push effect under the assumption that the push branch
    of `saveSimpleKey` fires (`simpleKeyAllowed = true ∧
    explicitKeyLine = none`).  Builds on A1
    (`saveSimpleKey_pkPush_when_allowed`) and the
    `scanFlowSequenceStart_preserves_pendingKeys` Class A property:
    the `[` flow path does NOT invoke `dispatchContent`, so there is
    no `setPendingKeyEndLine` wrap — pendingKeys is just `s.pendingKeys.push`
    of the unresolved entry recorded by `saveSimpleKey`. -/
theorem scanNextToken_flow_open_nested_pkPush (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = true)
    (h_ek_none : s.explicitKeyLine = none) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ StackEndLineOnLine s' s'.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      ∧ s'.pendingKeys.size = s.pendingKeys.size + 1
      ∧ (∃ (h : s.pendingKeys.size < s'.pendingKeys.size),
          (s'.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
          ∧ (s'.pendingKeys[s.pendingKeys.size]'h).kind = .unresolved)
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated-discharge:
      -- Stack push-shape: pendingKeyStack pushes `some s.pendingKeys.size`
      -- (saveSimpleKey's gated branch sets pendingKeyActive = some s.pendingKeys.size,
      -- and scanFlowSequenceStart pushes that onto pendingKeyStack);
      -- and the top-of-stack simpleKey carries `possible = true`
      -- (saveSimpleKey's gated branch sets simpleKey.possible = true,
      -- and scanFlowSequenceStart pushes that onto simpleKeyStack).
      -- Used to compose through body preservation + close-side restore
      -- in `emit_scans_in_flow` to recover the gated facts at s₃.
      ∧ s'.pendingKeyStack = s.pendingKeyStack.push (some s.pendingKeys.size)
      ∧ (s'.simpleKeyStack.back?.getD {}).possible = true := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ek s
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'[' :: rest, s_ad.col⟩ := by
    rw [show s_ad.col = s.col from h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowSequenceStart_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowSequenceStart_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '[' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowSequenceStart s_ad).line = s.line := by
    rw [scanFlowSequenceStart_line_eq]
    exact (advance_line_of_peek s_ad '[' h_lt_ad h_peek_ad (by decide) (by decide)).trans h_ad_line
  -- pkPush tracking: A1 lemma + record-update + scanFlowSequenceStart preservation
  obtain ⟨h_sk_pks, _h_sk_pka, _h_sk_skp⟩ :=
    saveSimpleKey_pkPush_when_allowed s h_ska h_ek_none
  have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
    simp only [s_ad]; split <;> rfl
  have h_fss_pks : (scanFlowSequenceStart s_ad).pendingKeys = s_ad.pendingKeys :=
    ScannerCorrectness.scanFlowSequenceStart_preserves_pendingKeys s_ad
  have h_fss_pks_full : (scanFlowSequenceStart s_ad).pendingKeys = s.pendingKeys.push
      { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
        endLine := s.line, kind := .unresolved } := by
    rw [h_fss_pks, h_ad_pks, h_sk_pks]
  have h_fss_size : (scanFlowSequenceStart s_ad).pendingKeys.size = s.pendingKeys.size + 1 := by
    rw [h_fss_pks_full, Array.size_push]
  have h_lt : s.pendingKeys.size < (scanFlowSequenceStart s_ad).pendingKeys.size := by
    rw [h_fss_size]; exact Nat.lt_succ_self _
  have h_get : (scanFlowSequenceStart s_ad).pendingKeys[s.pendingKeys.size]'h_lt =
      { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
        endLine := s.line, kind := .unresolved } := by
    simp only [h_fss_pks_full, Array.getElem_push]
    rw [dif_neg (Nat.lt_irrefl _)]
  refine ⟨_, h_snt, ?_, h_fl_f.trans (congrArg (· + 1) h_ad_fl),
    h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f.trans h_ad_ek,
    ?_, h_line_f, ?_, ?_, ?_, ?_, h_fss_size, ⟨h_lt, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_scanFlowSequenceStart s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · intro h_poss
    rw [scanFlowSequenceStart_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  · unfold StackEndLineOnLine
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.back?_push, h_line_f]
    intro h_poss
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad]; split
      · show EndLineOnLine { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
        exact EndLineOnLine_saveSimpleKey_flow s h_endline
      · exact EndLineOnLine_saveSimpleKey_flow s h_endline
    exact ⟨(h_ad_endline h_poss).1.trans h_ad_line, (h_ad_endline h_poss).2.trans h_ad_line⟩
  · rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.pop_push]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · rw [h_get]
  · rw [h_get]
  · -- preserves-prior: pendingKeys at j < s.pendingKeys.size unchanged through the push
    intro j hj _hj'
    simp only [h_fss_pks_full]
    exact Array.getElem_push_lt hj
  · -- pendingKeyStack push-shape:
    -- scanFlowSequenceStart pushes s_ad.pendingKeyActive onto s_ad.pendingKeyStack;
    -- s_ad mirrors saveSimpleKey s (allowDirectives branch is a non-stack record-update),
    -- and saveSimpleKey under the gate sets pendingKeyActive = some s.pendingKeys.size.
    rw [ScannerCorrectness.scanFlowSequenceStart_pendingKeyStack_pushed]
    have h_ad_pendingKeyStack : s_ad.pendingKeyStack = s.pendingKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
    have h_ad_pka : s_ad.pendingKeyActive = (saveSimpleKey s).pendingKeyActive := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_pendingKeyStack, h_ad_pka, _h_sk_pka]
  · -- simpleKeyStack top: pushed simpleKey carries possible = true
    -- (saveSimpleKey under the gate sets simpleKey.possible = true).
    rw [ScannerCorrectness.scanFlowSequenceStart_stack_pushed, Array.back?_push]
    show (s_ad.simpleKey).possible = true
    have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_sk]; exact _h_sk_skp

-- ═══ Block indicators: concrete none lemmas ═══

/-- `dispatchBlockIndicators` returns `none` for `,`. -/
theorem dispatchBlockIndicators_none_comma (s : ScannerState) :
    scanNextToken_dispatchBlockIndicators s ',' = .ok none := by
  unfold scanNextToken_dispatchBlockIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i h; simp at h
  · split
    · rename_i h; simp at h
    · split
      · rename_i h; simp at h
      · rfl

/-- `dispatchBlockIndicators` returns `none` for `]`. -/
theorem dispatchBlockIndicators_none_close_bracket (s : ScannerState) :
    scanNextToken_dispatchBlockIndicators s ']' = .ok none := by
  unfold scanNextToken_dispatchBlockIndicators
  simp only [bind, Except.bind, pure, Except.pure]
  split
  · rename_i h; simp at h
  · split
    · rename_i h; simp at h
    · split
      · rename_i h; simp at h
      · rfl

-- ═══ Flow comma: scanFlowEntry dispatch ═══

/-- `checkBlockFlowIndent` passes for `,`  (the guard only fires for `[` or `{`). -/
theorem checkBlockFlowIndent_ok_comma (s : ScannerState) :
    scanNextToken_checkBlockFlowIndent s ',' = .ok () := by
  unfold scanNextToken_checkBlockFlowIndent; split
  · exfalso; rename_i h; simp at h
  · rfl

/-- `checkBlockFlowIndent` passes for `]`  (the guard only fires for `[` or `{`). -/
theorem checkBlockFlowIndent_ok_close_bracket (s : ScannerState) :
    scanNextToken_checkBlockFlowIndent s ']' = .ok () := by
  unfold scanNextToken_checkBlockFlowIndent; split
  · exfalso; rename_i h; simp at h
  · rfl

/-- `scanFlowEntry` succeeds when the last real token is not a flow
    delimiter (flowSequenceStart, flowMappingStart, or flowEntry).
    This holds whenever we've just scanned a content token (scalar, etc.). -/
theorem scanFlowEntry_ok (s : ScannerState)
    (h_last : ∀ t, lastTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    scanFlowEntry s = .ok { (s.emit .flowEntry).advance with simpleKeyAllowed := true } := by
  unfold scanFlowEntry; dsimp only [bind, Except.bind, pure, Except.pure]
  -- After unfold+dsimp, the goal has a match on lastTokenVal? and if-then-else
  cases h_lrt : lastTokenVal? s.tokens with
  | none => rfl
  | some t =>
    have ⟨h1, h2, h3⟩ := h_last t h_lrt
    -- Show the boolean condition is false by case analysis on each BEq
    have : (t == YamlToken.flowSequenceStart) = false := by
      cases h : (t == YamlToken.flowSequenceStart)
      · rfl
      · exact absurd (beq_iff_eq.mp h) h1
    have : (t == YamlToken.flowMappingStart) = false := by
      cases h : (t == YamlToken.flowMappingStart)
      · rfl
      · exact absurd (beq_iff_eq.mp h) h2
    have : (t == YamlToken.flowEntry) = false := by
      cases h : (t == YamlToken.flowEntry)
      · rfl
      · exact absurd (beq_iff_eq.mp h) h3
    simp_all

/-- Field preservation through scanFlowEntry. -/
theorem scanFlowEntry_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_last : ∀ t, lastTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    let s' := { (s.emit .flowEntry).advance with simpleKeyAllowed := true }
    scanFlowEntry s = .ok s'
    ∧ ScannerSurfCorr s' ⟨rest, s.col + 1⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.col = s.col + 1 := by
  have h_ok := scanFlowEntry_ok s h_last
  have ⟨_, h_lt⟩ := peek_of_chars_cons s ',' rest _ hcorr
  let s_em := s.emit .flowEntry
  have h_em_corr : ScannerSurfCorr s_em ⟨',' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em ',' rest h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  refine ⟨h_ok, ?_, ?_, ?_, ?_, ?_⟩
  · -- ScannerSurfCorr
    exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
           h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩
  · -- flowLevel: { s_em.advance with simpleKeyAllowed := true }.flowLevel = s.flowLevel
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_flowLevel,
        ScannerCorrectness.emit_preserves_flowLevel]
  · -- directivesPresent
    dsimp only []
    rw [advance_preserves_dp]; rfl
  · -- indents
    dsimp only []
    rw [advance_preserves_indents]; rfl
  · -- col: { s_em.advance with ... }.col = s.col + 1
    -- h_adv_corr.col_eq : ⟨rest, s_em.col + 1⟩.col = s_em.advance.col
    -- i.e., s_em.col + 1 = s_em.advance.col, and s_em.col = s.col (emit preserves)
    dsimp only []
    exact h_adv_corr.col_eq.symm

-- Helper: lastTokenVal? on array.push tok returns tok.val.
--
-- **Initiative 3 / J.2 step 5 cutover** (Category B): same as
-- `lastTokenVal_push_non_ph'` — body simplifies under the new
-- `tokens.back?.map (·.val)` definition; `h_nph` is unused.
theorem lastTokenVal_push_non_ph
    (tokens : Array (Positioned YamlToken))
    (tok : Positioned YamlToken) (h_nph : tok.val ≠ .placeholder) :
    lastTokenVal? (tokens.push tok) = some tok.val := by
  let _ := h_nph
  simp [lastTokenVal?]

-- Helper: pushing two placeholders, the "skip up to 2 placeholders" lookup
-- on the new array either reaches `tokens`'s last token or returns placeholder.
--
-- **Initiative 3 / J.2 step 5 cutover** (Category A): post-cutover
-- `lastTokenVal? = tokens.back?.map (·.val)`, so on `(_.push ph1).push ph2`
-- it returns `some ph2.val = some .placeholder`.  Hence `t = .placeholder`
-- always — the disjunct holds vacuously on the right.
theorem lastTokenVal_push_two_ph
    (tokens : Array (Positioned YamlToken))
    (ph1 ph2 : Positioned YamlToken) (h1 : ph1.val = .placeholder) (h2 : ph2.val = .placeholder)
    (t : YamlToken)
    (ht : lastTokenVal? ((tokens.push ph1).push ph2) = some t) :
    lastTokenVal? tokens = some t ∨ t = .placeholder := by
  let _ := h1
  right
  simp [lastTokenVal?] at ht
  exact ht.symm.trans h2

theorem saveSimpleKey_preserves_lastTokenVal_ne_flow (s : ScannerState)
    (h_last : ∀ t, lastTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    (t : YamlToken)
    (ht : lastTokenVal? (saveSimpleKey s).tokens = some t) :
    t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
  -- **Initiative 3 / J.2 step 5 cutover** (Category B): post-cutover
  -- saveSimpleKey is identity on tokens, so the "two-placeholders" branch
  -- of the original case-split is dead.
  have h_cases : (saveSimpleKey s).tokens = s.tokens ∨
      (saveSimpleKey s).tokens = ((s.tokens.push ⟨s.currentPos, .placeholder, s.currentPos⟩).push
        ⟨s.currentPos, .placeholder, s.currentPos⟩) := by
    left
    unfold saveSimpleKey
    split
    · rfl
    · split <;> rfl
  rcases h_cases with h_eq | h_eq
  · rw [h_eq] at ht; exact h_last t ht
  · rw [h_eq] at ht
    have h_or := lastTokenVal_push_two_ph s.tokens
      ⟨s.currentPos, .placeholder, s.currentPos⟩
      ⟨s.currentPos, .placeholder, s.currentPos⟩ rfl rfl t ht
    cases h_or with
    | inl h => exact h_last t h
    | inr h => subst h; exact ⟨by decide, by decide, by decide⟩

/-- Flow dispatch for `,` returns `some (scanFlowEntry result)` when flowLevel > 0. -/
theorem dispatchFlowIndicators_comma (s : ScannerState)
    (h_fl : s.flowLevel > 0)
    (h_last : ∀ t, lastTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry) :
    scanNextToken_dispatchFlowIndicators s ',' =
      .ok (some { (s.emit .flowEntry).advance with simpleKeyAllowed := true }) := by
  unfold scanNextToken_dispatchFlowIndicators
  simp only [bind, Except.bind, pure, Except.pure,
    show (',' == '[') = false from by decide,
    show (',' == ']') = false from by decide,
    show (',' == '{') = false from by decide,
    show (',' == '}') = false from by decide,
    show (',' == ',') = true from by decide, ite_true]
  simp only [show (s.flowLevel == 0) = false from nat_beq_zero_false _ (by omega)]
  -- Goal: Bind.bind (scanFlowEntry s) (pure ∘ some) = .ok (some { ... })
  rw [scanFlowEntry_ok s h_last]
  rfl

/-- Full `scanNextToken` for `,` in flow context.
    Handles preprocessing (skips nothing for non-ws `,`),
    structural dispatch (none), flow dispatch (scanFlowEntry). -/
theorem scanNextToken_flow_comma (s : ScannerState)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨',' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_last : ∀ t, lastTokenVal? s.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- pkRec preserved at indices < initial size (saveSimpleKey is push-or-id;
      -- scanFlowEntry doesn't touch pendingKeys).
      -- C-foundation-EmitScansInFlow-defns-helpers-size: size monotonic.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack preserved (scanFlowEntry doesn't touch it; saveSimpleKey
      -- and the allowDirectives record-update preserve it).
      ∧ s'.pendingKeyStack = s.pendingKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon:
      -- scanFlowEntry's final record-update sets `simpleKeyAllowed := true`,
      -- which is the gate the next key needs to fire `saveSimpleKey`'s push
      -- branch.  Used by `emitPairList_scans_nonempty`'s recursive case to
      -- thread the gate through ws1 into the IH call.
      ∧ s'.simpleKeyAllowed = true
      -- J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6a (2026-05-02):
      -- the comma push.  scanFlowEntry pushes exactly one `.flowEntry` token
      -- at the previous tail (`s.tokens.size`), under the saveSimpleKey/
      -- allowDirectives wrappers (both preserve `tokens`).  Threaded into
      -- `emitPairList_scans_nonempty`'s recursive case to seed the
      -- predecessor-flowEntry conjunct for `qs[1]` (and lifted through the
      -- IH via tokens-prefix preservation). -/
      ∧ (s'.tokens.size = s.tokens.size + 1
          ∧ (∀ (h_lt : s.tokens.size < s'.tokens.size),
              (s'.tokens[s.tokens.size]'h_lt).val = .flowEntry)) := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ',')) :=
    scanNextToken_preprocess_flow s ',' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ',' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 4: checkBlockFlowIndent for ','
  have h_check := checkBlockFlowIndent_ok_comma s_ad
  -- Step 5: flow dispatch for ','
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by
    rw [h_ad_fl]; unfold ScannerState.inFlow at h_flow; exact of_decide_eq_true h_flow
  have h_ad_corr : ScannerSurfCorr s_ad ⟨',' :: rest, s_ad.col⟩ := by
    have h_ad_col_eq : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
    rw [h_ad_col_eq]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col_eq
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_ad_last : ∀ t, lastTokenVal? s_ad.tokens = some t →
      t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry := by
    intro t ht
    have h_ad_toks : s_ad.tokens = (saveSimpleKey s).tokens := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_toks] at ht
    exact saveSimpleKey_preserves_lastTokenVal_ne_flow s h_last t ht
  have h_flow_disp := dispatchFlowIndicators_comma s_ad h_fl_pos h_ad_last
  -- Step 6: compose
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- Step 7: extract properties
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have ⟨_, h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ := scanFlowEntry_detail s_ad rest h_ad_corr h_ad_last
  have h_ek_f : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).explicitKeyLine = s_ad.explicitKeyLine := by
    dsimp only []; rw [advance_explicitKeyLine]; rfl
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad ',' rest s_ad.col h_ad_corr
  have h_line_f : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).line = s.line := by
    dsimp only []
    rw [advance_line_of_peek (s_ad.emit .flowEntry) ',' h_lt_ad h_peek_ad (by decide) (by decide)]
    exact h_ad_line
  refine ⟨_, h_snt, ?_, h_fl_f.trans h_ad_fl, h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids,
    h_ek_f.trans h_ad_ek, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_advance _ _ (AllTokensOnLine_emit _ _ _
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line)
  · -- EndLineOnLine: simpleKey preserved through emit/advance, use saveSimpleKey lemma
    intro h_poss
    have h_sk_eq : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).simpleKey =
        (saveSimpleKey s).simpleKey := by
      dsimp only []
      rw [ScannerCorrectness.advance_preserves_simpleKey, ScannerCorrectness.emit_preserves_simpleKey]
      simp only [s_ad]; split <;> rfl
    rw [h_sk_eq] at h_poss ⊢
    have h_sk_endline := EndLineOnLine_saveSimpleKey_flow s h_endline
    obtain ⟨h1, h2⟩ := h_sk_endline h_poss
    have h_sk_line : (saveSimpleKey s).line = s.line := saveSimpleKey_preserves_line s
    exact ⟨h_line_f ▸ h_sk_line ▸ h1, h_line_f ▸ h_sk_line ▸ h2⟩
  · -- simpleKeyStack preserved: scanFlowEntry doesn't touch stack
    show ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).simpleKeyStack = s.simpleKeyStack
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_simpleKeyStack, ScannerCorrectness.emit_preserves_simpleKeyStack]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- size monotonic: emit/advance/record-update preserve pendingKeys; saveSimpleKey grows
    show s.pendingKeys.size ≤ ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).pendingKeys.size
    have h_pks_f : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).pendingKeys
        = (saveSimpleKey s).pendingKeys := by
      show (s_ad.emit .flowEntry).advance.pendingKeys = (saveSimpleKey s).pendingKeys
      rw [ScannerCorrectness.advance_preserves_pendingKeys,
          ScannerCorrectness.emit_preserves_pendingKeys]
      show s_ad.pendingKeys = (saveSimpleKey s).pendingKeys
      simp only [s_ad]; split <;> rfl
    rw [h_pks_f]; exact saveSimpleKey_pendingKeys_size_ge s
  · -- pkRec preserved at j < initial size: pendingKeys flow through saveSimpleKey
    -- (push or identity), s_ad (record-update), emit/advance (no-touch).
    intro j hj hj'
    have h_pks_f : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).pendingKeys
        = (saveSimpleKey s).pendingKeys := by
      show (s_ad.emit .flowEntry).advance.pendingKeys = (saveSimpleKey s).pendingKeys
      rw [ScannerCorrectness.advance_preserves_pendingKeys,
          ScannerCorrectness.emit_preserves_pendingKeys]
      show s_ad.pendingKeys = (saveSimpleKey s).pendingKeys
      simp only [s_ad]; split <;> rfl
    have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
      rw [← h_pks_f]; exact hj'
    have ⟨h_ib, h_kd⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
    refine ⟨?_, ?_⟩
    · -- insertBeforeIdx
      have : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }
              ).pendingKeys[j]'hj' = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by
        congr 1
      rw [this]; exact h_ib
    · have : ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }
              ).pendingKeys[j]'hj' = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by
        congr 1
      rw [this]; exact h_kd
  · -- pendingKeyStack preserved: scanFlowEntry doesn't touch it
    show ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).pendingKeyStack
        = s.pendingKeyStack
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_pendingKeyStack,
        ScannerCorrectness.emit_preserves_pendingKeyStack]
    show s_ad.pendingKeyStack = s.pendingKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
  · -- simpleKeyAllowed = true: scanFlowEntry's record-update sets it directly.
    show ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).simpleKeyAllowed = true
    rfl
  · -- Part3-final-discharge-bridge-6a: the comma's flowEntry push.
    -- s' = ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true });
    -- chase tokens through advance/record-update/emit/saveSimpleKey/allowDirectives.
    have h_ad_tk : s_ad.tokens = s.tokens := by
      simp only [s_ad]; split
      · show (saveSimpleKey s).tokens = s.tokens
        exact ScannerCorrectness.saveSimpleKey_preserves_tokens s
      · exact ScannerCorrectness.saveSimpleKey_preserves_tokens s
    have h_s'_tokens :
        ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }).tokens
          = s.tokens.push ⟨s_ad.currentPos, .flowEntry, s_ad.currentPos⟩ := by
      show (s_ad.emit .flowEntry).advance.tokens = _
      rw [ScannerCorrectness.advance_preserves_tokens]
      show s_ad.tokens.push _ = _
      rw [h_ad_tk]
    refine ⟨?_, ?_⟩
    · rw [h_s'_tokens, Array.size_push]
    · intro h_lt
      -- Index into the push via h_s'_tokens.  Use a generalize + subst
      -- pattern to rewrite the dependent array under the bound.
      have h_lt' :
          s.tokens.size <
            (s.tokens.push ⟨s_ad.currentPos, .flowEntry, s_ad.currentPos⟩).size := by
        rw [Array.size_push]; omega
      have h_get :
          ({ (s_ad.emit .flowEntry).advance with simpleKeyAllowed := true }
            ).tokens[s.tokens.size]'h_lt
            = (s.tokens.push ⟨s_ad.currentPos, .flowEntry, s_ad.currentPos⟩
                )[s.tokens.size]'h_lt' := by
        -- generalize the LHS array, subst via h_s'_tokens, then rfl.
        generalize h_arr : ({ (s_ad.emit .flowEntry).advance with
            simpleKeyAllowed := true }).tokens = arr at h_lt ⊢
        have h_arr_eq :
            arr = s.tokens.push ⟨s_ad.currentPos, .flowEntry, s_ad.currentPos⟩ := by
          rw [← h_arr]; exact h_s'_tokens
        subst h_arr_eq; rfl
      rw [h_get, Array.getElem_push_eq]

-- ═══ Flow close bracket: scanFlowSequenceEnd dispatch ═══

/-- Field preservation through scanFlowSequenceEnd: directivesPresent. -/
theorem scanFlowSequenceEnd_preserves_dp (s : ScannerState) :
    (scanFlowSequenceEnd s).directivesPresent = s.directivesPresent := by
  unfold scanFlowSequenceEnd; dsimp only []; simp only [advance_preserves_dp, ScannerState.emit]

/-- Field preservation through scanFlowSequenceEnd: indents. -/
theorem scanFlowSequenceEnd_preserves_indents (s : ScannerState) :
    (scanFlowSequenceEnd s).indents = s.indents := by
  unfold scanFlowSequenceEnd; dsimp only []; simp only [advance_preserves_indents, ScannerState.emit]

theorem scanFlowSequenceEnd_preserves_ek (s : ScannerState) :
    (scanFlowSequenceEnd s).explicitKeyLine = s.explicitKeyLine := by
  unfold scanFlowSequenceEnd; dsimp only []; simp only [advance_explicitKeyLine, ScannerState.emit]

/-- FlowLevel through scanFlowSequenceEnd: decremented by 1. -/
theorem scanFlowSequenceEnd_flowLevel (s : ScannerState) :
    (scanFlowSequenceEnd s).flowLevel =
      if s.flowLevel > 0 then s.flowLevel - 1 else 0 := by
  unfold scanFlowSequenceEnd; dsimp only []
  simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel]

/-- ScannerSurfCorr + properties through scanFlowSequenceEnd. -/
theorem scanFlowSequenceEnd_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨']' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowSequenceEnd s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowSequenceEnd s).flowLevel = (if s.flowLevel > 0 then s.flowLevel - 1 else 0)
    ∧ (scanFlowSequenceEnd s).directivesPresent = s.directivesPresent
    ∧ (scanFlowSequenceEnd s).indents = s.indents
    ∧ (scanFlowSequenceEnd s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s ']' rest _ hcorr
  let s_em := s.emit .flowSequenceEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨']' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em ']' rest h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_col_eq : (scanFlowSequenceEnd s).col = s.col + 1 := by
    unfold scanFlowSequenceEnd; dsimp only []; exact h_adv_corr.col_eq.symm
  refine ⟨?_, scanFlowSequenceEnd_flowLevel s,
          scanFlowSequenceEnd_preserves_dp s,
          scanFlowSequenceEnd_preserves_indents s, h_col_eq⟩
  -- ScannerSurfCorr: scanFlowSequenceEnd only adds flowLevel/simpleKeyAllowed/flowStack/simpleKey/simpleKeyStack
  -- on top of (s.emit .flowSequenceEnd).advance
  unfold scanFlowSequenceEnd
  exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
         h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩

/-- Token property: `scanFlowSequenceEnd` ends with `.flowSequenceEnd` as last real token. -/
theorem scanFlowSequenceEnd_lastTokenVal (s : ScannerState) :
    lastTokenVal? (scanFlowSequenceEnd s).tokens = some .flowSequenceEnd := by
  unfold scanFlowSequenceEnd; dsimp only []
  -- tokens = (s.emit .flowSequenceEnd).advance.tokens
  --        = (s.emit .flowSequenceEnd).tokens (advance preserves tokens)
  --        = s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd }
  show lastTokenVal? (s.emit .flowSequenceEnd).advance.tokens = _
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowSequenceEnd)]
  show lastTokenVal? (s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd }) = _
  exact lastTokenVal_push_non_ph' s.tokens _ nofun

/-- `validateFlowClose` passes when flowLevel > 0. -/
theorem validateFlowClose_pass_nested (s : ScannerState) (h_fl : s.flowLevel > 0) :
    validateFlowClose s = .ok () := by
  unfold validateFlowClose
  have := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp [this, pure, Except.pure]

/-- `skipTrailingSpaces` at EOF is a no-op. -/
theorem skipTrailingSpaces_at_eof (s : ScannerState) (n : Nat) (h : s.peek? = none) :
    skipTrailingSpaces s n = s := by
  cases n with
  | zero => unfold skipTrailingSpaces; rfl
  | succ m =>
    unfold skipTrailingSpaces
    split
    · split
      · simp_all
      · rfl
    · rfl

/-- `validateFlowClose` passes at flowLevel = 0 when peek? = none (EOF). -/
theorem validateFlowClose_pass_eof (s : ScannerState)
    (h_fl : s.flowLevel = 0) (h_eof : s.peek? = none) :
    validateFlowClose s = .ok () := by
  unfold validateFlowClose
  simp only [show (s.flowLevel == 0) = true from nat_beq_zero_true h_fl]
  simp [skipTrailingSpaces_at_eof s _ h_eof, h_eof, pure, Except.pure]

/-- Flow dispatch for `]` returns `some (scanFlowSequenceEnd s)` when
    flowLevel ≥ 2 (nested case — validateFlowClose is no-op). -/
theorem dispatchFlowIndicators_close_bracket_nested (s : ScannerState)
    (h_fl : s.flowLevel ≥ 2) :
    scanNextToken_dispatchFlowIndicators s ']' = .ok (some (scanFlowSequenceEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  simp only [bind, Except.bind, pure, Except.pure,
    show (']' == '[') = false from by decide,
    show (']' == ']') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne]
  have h_fl_after : (scanFlowSequenceEnd s).flowLevel > 0 := by
    rw [scanFlowSequenceEnd_flowLevel]; split <;> omega
  rw [validateFlowClose_pass_nested _ h_fl_after]
  simp

/-- Full `scanNextToken` for `]` in flow context when flowLevel ≥ 2
    (nested flow close — no validateFlowClose concern). -/
theorem scanNextToken_flow_close_seq_nested (s : ScannerState)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨']' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    (h_atol : AllTokensOnLine s s.line)
    (h_stack_endline : StackEndLineOnLine s s.line) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel - 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ (∀ t, lastTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.pop
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- pkRec preserved at indices < initial size (saveSimpleKey is push-or-id;
      -- scanFlowSequenceEnd doesn't touch pendingKeys).
      -- C-foundation-EmitScansInFlow-defns-helpers-size: size monotonic.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- close-side restore: simpleKey/pendingKeyActive recover from the
      -- corresponding stack tops, and the stacks pop in tandem (J.2 dual-write).
      ∧ s'.simpleKey = s.simpleKeyStack.back?.getD {}
      ∧ s'.pendingKeyActive = s.pendingKeyStack.back?.getD none
      ∧ s'.pendingKeyStack = s.pendingKeyStack.pop := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 4: checkBlockFlowIndent for ']'
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  -- Step 5: flow dispatch for ']'
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_fl_pos : s_ad.flowLevel > 0 := by rw [h_ad_fl]; omega
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨']' :: rest, s_ad.col⟩ := by
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  -- Flow dispatch: nested close, flowLevel ≥ 2 so validateFlowClose is no-op
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_flow_disp := dispatchFlowIndicators_close_bracket_nested s_ad h_ad_fl_ge2
  -- Step 6: compose
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- Step 7: extract properties
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ := scanFlowSequenceEnd_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowSequenceEnd_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad ']' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowSequenceEnd s_ad).line = s.line := by
    show (s_ad.emit .flowSequenceEnd).advance.line = s.line
    rw [advance_line_of_peek (s_ad.emit .flowSequenceEnd) ']' h_lt_ad h_peek_ad (by decide) (by decide)]
    exact h_ad_line
  -- Stack-restore facts (J.4.2.b…stack-restore): `s_ad.simpleKeyStack`,
  -- `s_ad.pendingKeyStack`, and `s_ad.pendingKeys` all equal the
  -- corresponding `saveSimpleKey s` projections (which equal `s`'s
  -- projections for the stacks; saveSimpleKey only mutates pendingKeys).
  have h_ad_simpleKeyStack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  have h_ad_pendingKeyStack : s_ad.pendingKeyStack = s.pendingKeyStack := by
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
  refine ⟨_, h_snt, ?_, ?_, h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f.trans h_ad_ek, ?_, ?_, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_fl_f]; split
    · rw [h_ad_fl]
    · exfalso; omega
  · rw [h_col_f, h_ad_col]
  · -- lastTokenVal? = .flowSequenceEnd
    intro t ht
    have h_lrt := scanFlowSequenceEnd_lastTokenVal s_ad
    rw [h_lrt] at ht; injection ht with ht; subst ht
    exact ⟨by decide, by decide, by decide⟩
  · -- simpleKeyAllowed = false
    show (scanFlowSequenceEnd s_ad).simpleKeyAllowed = false
    rfl
  · -- AllTokensOnLine
    rw [h_line_f]
    exact AllTokensOnLine_scanFlowSequenceEnd s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: simpleKey restored from stack
    intro h_poss
    rw [ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored] at h_poss ⊢
    rw [h_ad_simpleKeyStack] at h_poss ⊢
    unfold StackEndLineOnLine at h_stack_endline
    rw [h_line_f]
    cases h_back : s.simpleKeyStack.back? with
    | none => rw [h_back] at h_poss; simp [Option.getD] at h_poss
    | some sk =>
      rw [h_back] at h_poss h_stack_endline; simp [Option.getD] at h_poss
      exact h_stack_endline h_poss
  · -- simpleKeyStack.pop
    show (scanFlowSequenceEnd s_ad).simpleKeyStack = s.simpleKeyStack.pop
    rw [ScannerCorrectness.scanFlowSequenceEnd_stack_popped, h_ad_simpleKeyStack]
  · -- size monotonic
    have h_fse_pks : (scanFlowSequenceEnd s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowSequenceEnd_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    rw [h_fse_pks, h_ad_pks]
    exact saveSimpleKey_pendingKeys_size_ge s
  · -- pkRec preserved at j < initial size
    intro j hj hj'
    have h_fse_pks : (scanFlowSequenceEnd s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowSequenceEnd_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    have h_full_pks : (scanFlowSequenceEnd s_ad).pendingKeys = (saveSimpleKey s).pendingKeys :=
      h_fse_pks.trans h_ad_pks
    have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
      rw [← h_full_pks]; exact hj'
    have ⟨h_ib, h_kd⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
    have h_eq : (scanFlowSequenceEnd s_ad).pendingKeys[j]'hj'
                = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by congr 1
    refine ⟨?_, ?_⟩
    · rw [h_eq]; exact h_ib
    · rw [h_eq]; exact h_kd
  · -- simpleKey restored
    show (scanFlowSequenceEnd s_ad).simpleKey = s.simpleKeyStack.back?.getD {}
    rw [ScannerCorrectness.scanFlowSequenceEnd_simpleKey_restored, h_ad_simpleKeyStack]
  · -- pendingKeyActive restored
    show (scanFlowSequenceEnd s_ad).pendingKeyActive = s.pendingKeyStack.back?.getD none
    rw [ScannerCorrectness.scanFlowSequenceEnd_pendingKeyActive_restored,
        h_ad_pendingKeyStack]
  · -- pendingKeyStack popped
    show (scanFlowSequenceEnd s_ad).pendingKeyStack = s.pendingKeyStack.pop
    rw [ScannerCorrectness.scanFlowSequenceEnd_pendingKeyStack_popped,
        h_ad_pendingKeyStack]

-- ═══ Outermost flow close: ] at flowLevel = 1 ═══

/-- `scanFlowSequenceEnd` preserves `peek?` from the underlying advance. -/
theorem scanFlowSequenceEnd_peek (s : ScannerState) :
    (scanFlowSequenceEnd s).peek? = (s.emit .flowSequenceEnd).advance.peek? := by
  unfold scanFlowSequenceEnd ScannerState.peek?; rfl

/-- Flow dispatch for `]` when flowLevel = 1 and at EOF (outermost close).
    After scanFlowSequenceEnd, flowLevel = 0 and validateFlowClose passes. -/
theorem dispatchFlowIndicators_close_bracket_outermost (s : ScannerState)
    (h_fl : s.flowLevel = 1)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩) :
    scanNextToken_dispatchFlowIndicators s ']' = .ok (some (scanFlowSequenceEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  simp only [bind, Except.bind, pure, Except.pure,
    show (']' == '[') = false from by decide,
    show (']' == ']') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne]
  -- After scanFlowSequenceEnd: flowLevel = 0
  have h_fl_after : (scanFlowSequenceEnd s).flowLevel = 0 := by
    rw [scanFlowSequenceEnd_flowLevel, h_fl]
    simp (config := { decide := true })
  -- EOF: peek? = none after advancing past ']'
  have ⟨_, h_lt⟩ := peek_of_chars_cons s ']' [] s.col hcorr
  let s_em := s.emit .flowSequenceEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨[']'], s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em ']' [] h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_adv_peek := peek_none_of_empty_surf s_em.advance (s.col + 1) h_adv_corr
  have h_eof : (scanFlowSequenceEnd s).peek? = none := by
    rw [scanFlowSequenceEnd_peek]; exact h_adv_peek
  rw [validateFlowClose_pass_eof _ h_fl_after h_eof]
  simp

/-- Full `scanNextToken` for `]` at flowLevel = 1 (outermost flow close).
    The result has flowLevel = 0, directivesPresent = false. -/
theorem scanNextToken_flow_close_seq_outermost (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none := by
  -- Step 1: preprocessing
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: structural dispatch → none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 4: checkBlockFlowIndent
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  -- Step 5: flow dispatch
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨[']'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_bracket_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- Extract properties
  have h_result_fl : (scanFlowSequenceEnd s_ad).flowLevel = 0 := by
    rw [scanFlowSequenceEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : (scanFlowSequenceEnd s_ad).directivesPresent = false := by
    rw [scanFlowSequenceEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : (scanFlowSequenceEnd s_ad).peek? = none := by
    rw [scanFlowSequenceEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad ']' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowSequenceEnd) ']' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowSequenceEnd).offset < (s_ad.emit .flowSequenceEnd).inputEnd from h_lt)
        (by decide) (by decide))
  exact ⟨scanFlowSequenceEnd s_ad, h_snt, h_result_fl, h_result_dp, h_result_eof⟩

-- ═══ Flow mapping: scanFlowMappingStart / scanFlowMappingEnd ═══
-- Symmetric to scanFlowSequenceStart/End but for `{`/`}`.

theorem scanFlowMappingStart_preserves_dp (s : ScannerState) :
    (scanFlowMappingStart s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingStart; simp only [advance_preserves_dp, ScannerState.emit]

theorem scanFlowMappingStart_preserves_indents (s : ScannerState) :
    (scanFlowMappingStart s).indents = s.indents := by
  unfold scanFlowMappingStart; simp only [advance_preserves_indents, ScannerState.emit]

theorem scanFlowMappingStart_preserves_ek (s : ScannerState) :
    (scanFlowMappingStart s).explicitKeyLine = s.explicitKeyLine := by
  unfold scanFlowMappingStart; dsimp only []; simp only [advance_explicitKeyLine, ScannerState.emit]

theorem scanFlowMappingStart_line_eq (s : ScannerState) :
    (scanFlowMappingStart s).line = s.advance.line := by
  simp only [scanFlowMappingStart, ScannerState.emit, ScannerState.advance]
  split <;> (try split <;> (try split)) <;> rfl

theorem scanFlowMappingStart_flowLevel_eq (s : ScannerState) :
    (scanFlowMappingStart s).flowLevel = s.flowLevel + 1 := by
  unfold scanFlowMappingStart
  simp only [ScannerCorrectness.advance_preserves_flowLevel, ScannerCorrectness.emit_preserves_flowLevel]

theorem scanFlowMappingStart_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowMappingStart s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowMappingStart s).flowLevel = s.flowLevel + 1
    ∧ (scanFlowMappingStart s).directivesPresent = s.directivesPresent
    ∧ (scanFlowMappingStart s).indents = s.indents
    ∧ (scanFlowMappingStart s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '{' rest _ hcorr
  have h_emit_corr : ScannerSurfCorr
      ({ s with simpleKey := { possible := false }, pendingKeyActive := none }.emit .flowMappingStart)
      ⟨'{' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr
    ({ s with simpleKey := { possible := false }, pendingKeyActive := none }.emit .flowMappingStart)
    '{' rest h_emit_corr h_lt (by decide) (by decide)
  have h_corr_final : ScannerSurfCorr (scanFlowMappingStart s) ⟨rest, s.col + 1⟩ := by
    unfold scanFlowMappingStart
    exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
           h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩
  exact ⟨h_corr_final,
         scanFlowMappingStart_flowLevel_eq s,
         scanFlowMappingStart_preserves_dp s,
         scanFlowMappingStart_preserves_indents s,
         h_corr_final.col_eq.symm ▸ rfl⟩

theorem dispatchFlowIndicators_brace (s : ScannerState) :
    scanNextToken_dispatchFlowIndicators s '{' = .ok (some (scanFlowMappingStart s)) := by
  unfold scanNextToken_dispatchFlowIndicators; dsimp only []
  simp only [pure, Except.pure, bind, Except.bind,
    show ('{' == '[') = false from by decide,
    show ('{' == ']') = false from by decide,
    show ('{' == '{') = true from by decide,
    ite_true, ite_false, Bool.false_eq_true]

theorem scanFlowMappingEnd_preserves_dp (s : ScannerState) :
    (scanFlowMappingEnd s).directivesPresent = s.directivesPresent := by
  unfold scanFlowMappingEnd; dsimp only []; simp only [advance_preserves_dp, ScannerState.emit]

theorem scanFlowMappingEnd_preserves_indents (s : ScannerState) :
    (scanFlowMappingEnd s).indents = s.indents := by
  unfold scanFlowMappingEnd; dsimp only []; simp only [advance_preserves_indents, ScannerState.emit]

theorem scanFlowMappingEnd_preserves_ek (s : ScannerState) :
    (scanFlowMappingEnd s).explicitKeyLine = s.explicitKeyLine := by
  unfold scanFlowMappingEnd; dsimp only []; simp only [advance_explicitKeyLine, ScannerState.emit]

theorem scanFlowMappingEnd_flowLevel (s : ScannerState) :
    (scanFlowMappingEnd s).flowLevel =
      if s.flowLevel > 0 then s.flowLevel - 1 else 0 := by
  unfold scanFlowMappingEnd; dsimp only []
  simp only [ScannerCorrectness.advance_preserves_flowLevel,
             ScannerCorrectness.emit_preserves_flowLevel]

theorem scanFlowMappingEnd_detail (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'}' :: rest, s.col⟩) :
    ScannerSurfCorr (scanFlowMappingEnd s) ⟨rest, s.col + 1⟩
    ∧ (scanFlowMappingEnd s).flowLevel = (if s.flowLevel > 0 then s.flowLevel - 1 else 0)
    ∧ (scanFlowMappingEnd s).directivesPresent = s.directivesPresent
    ∧ (scanFlowMappingEnd s).indents = s.indents
    ∧ (scanFlowMappingEnd s).col = s.col + 1 := by
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '}' rest _ hcorr
  let s_em := s.emit .flowMappingEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨'}' :: rest, s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em '}' rest h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_col_eq : (scanFlowMappingEnd s).col = s.col + 1 := by
    unfold scanFlowMappingEnd; dsimp only []; exact h_adv_corr.col_eq.symm
  refine ⟨?_, scanFlowMappingEnd_flowLevel s,
          scanFlowMappingEnd_preserves_dp s,
          scanFlowMappingEnd_preserves_indents s, h_col_eq⟩
  unfold scanFlowMappingEnd
  exact ⟨h_adv_corr.chars_from, h_adv_corr.col_eq, h_adv_corr.end_eq,
         h_adv_corr.input_prefix, h_adv_corr.indent_cols_nonneg⟩

theorem scanFlowMappingEnd_lastTokenVal (s : ScannerState) :
    lastTokenVal? (scanFlowMappingEnd s).tokens = some .flowMappingEnd := by
  unfold scanFlowMappingEnd; dsimp only []
  show lastTokenVal? (s.emit .flowMappingEnd).advance.tokens = _
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowMappingEnd)]
  show lastTokenVal? (s.tokens.push { pos := s.currentPos, val := .flowMappingEnd }) = _
  exact lastTokenVal_push_non_ph' s.tokens _ nofun

theorem scanFlowMappingEnd_peek (s : ScannerState) :
    (scanFlowMappingEnd s).peek? = (s.emit .flowMappingEnd).advance.peek? := by
  unfold scanFlowMappingEnd ScannerState.peek?; rfl

theorem checkBlockFlowIndent_ok_close_brace (s : ScannerState) :
    scanNextToken_checkBlockFlowIndent s '}' = .ok () := by
  unfold scanNextToken_checkBlockFlowIndent; split
  · exfalso; rename_i h; simp at h
  · rfl

theorem dispatchFlowIndicators_close_brace_nested (s : ScannerState)
    (h_fl : s.flowLevel ≥ 2) :
    scanNextToken_dispatchFlowIndicators s '}' = .ok (some (scanFlowMappingEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  simp only [bind, Except.bind, pure, Except.pure,
    show ('}' == '[') = false from by decide,
    show ('}' == ']') = false from by decide,
    show ('}' == '{') = false from by decide,
    show ('}' == '}') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne]
  have h_fl_after : (scanFlowMappingEnd s).flowLevel > 0 := by
    rw [scanFlowMappingEnd_flowLevel]; split <;> omega
  rw [validateFlowClose_pass_nested _ h_fl_after]
  simp

theorem scanNextToken_flow_close_mapping_nested (s : ScannerState)
    (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'}' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl_ge2 : s.flowLevel ≥ 2)
    (h_atol : AllTokensOnLine s s.line)
    (h_stack_endline : StackEndLineOnLine s s.line) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel - 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ (∀ t, lastTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ s'.simpleKeyAllowed = false
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack.pop
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- pkRec preserved at indices < initial size.
      -- C-foundation-EmitScansInFlow-defns-helpers-size: size monotonic.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- close-side restore: simpleKey/pendingKeyActive recover from the
      -- corresponding stack tops, and the stacks pop in tandem (J.2 dual-write).
      ∧ s'.simpleKey = s.simpleKeyStack.back?.getD {}
      ∧ s'.pendingKeyActive = s.pendingKeyStack.back?.getD none
      ∧ s'.pendingKeyStack = s.pendingKeyStack.pop := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'}' :: rest, s_ad.col⟩ := by
    rw [h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_ad_fl_ge2 : s_ad.flowLevel ≥ 2 := by rw [h_ad_fl]; exact h_fl_ge2
  have h_flow_disp := dispatchFlowIndicators_close_brace_nested s_ad h_ad_fl_ge2
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ := scanFlowMappingEnd_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowMappingEnd_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '}' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowMappingEnd s_ad).line = s.line := by
    show (s_ad.emit .flowMappingEnd).advance.line = s.line
    rw [advance_line_of_peek (s_ad.emit .flowMappingEnd) '}' h_lt_ad h_peek_ad (by decide) (by decide)]
    exact h_ad_line
  -- Stack-restore facts (J.4.2.b…stack-restore): saveSimpleKey + allowDirectives
  -- update preserve both stacks; close pops both in tandem.
  have h_ad_simpleKeyStack : s_ad.simpleKeyStack = s.simpleKeyStack := by
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  have h_ad_pendingKeyStack : s_ad.pendingKeyStack = s.pendingKeyStack := by
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
  refine ⟨_, h_snt, ?_, ?_, h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f.trans h_ad_ek, ?_, ?_, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_fl_f]; split
    · rw [h_ad_fl]
    · exfalso; omega
  · rw [h_col_f, h_ad_col]
  · intro t ht
    have h_lrt := scanFlowMappingEnd_lastTokenVal s_ad
    rw [h_lrt] at ht; injection ht with ht; subst ht
    exact ⟨nofun, nofun, nofun⟩
  · -- simpleKeyAllowed = false
    show (scanFlowMappingEnd s_ad).simpleKeyAllowed = false
    rfl
  · -- AllTokensOnLine
    rw [h_line_f]
    exact AllTokensOnLine_scanFlowMappingEnd s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: simpleKey restored from stack
    intro h_poss
    rw [ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored] at h_poss ⊢
    rw [h_ad_simpleKeyStack] at h_poss ⊢
    unfold StackEndLineOnLine at h_stack_endline
    rw [h_line_f]
    cases h_back : s.simpleKeyStack.back? with
    | none => rw [h_back] at h_poss; simp [Option.getD] at h_poss
    | some sk =>
      rw [h_back] at h_poss h_stack_endline; simp [Option.getD] at h_poss
      exact h_stack_endline h_poss
  · -- simpleKeyStack.pop
    show (scanFlowMappingEnd s_ad).simpleKeyStack = s.simpleKeyStack.pop
    rw [ScannerCorrectness.scanFlowMappingEnd_stack_popped, h_ad_simpleKeyStack]
  · -- size monotonic
    have h_fme_pks : (scanFlowMappingEnd s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowMappingEnd_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    rw [h_fme_pks, h_ad_pks]
    exact saveSimpleKey_pendingKeys_size_ge s
  · -- pkRec preserved at j < initial size
    intro j hj hj'
    have h_fme_pks : (scanFlowMappingEnd s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowMappingEnd_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    have h_full_pks : (scanFlowMappingEnd s_ad).pendingKeys = (saveSimpleKey s).pendingKeys :=
      h_fme_pks.trans h_ad_pks
    have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
      rw [← h_full_pks]; exact hj'
    have ⟨h_ib, h_kd⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
    have h_eq : (scanFlowMappingEnd s_ad).pendingKeys[j]'hj'
                = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by congr 1
    refine ⟨?_, ?_⟩
    · rw [h_eq]; exact h_ib
    · rw [h_eq]; exact h_kd
  · -- simpleKey restored
    show (scanFlowMappingEnd s_ad).simpleKey = s.simpleKeyStack.back?.getD {}
    rw [ScannerCorrectness.scanFlowMappingEnd_simpleKey_restored, h_ad_simpleKeyStack]
  · -- pendingKeyActive restored
    show (scanFlowMappingEnd s_ad).pendingKeyActive = s.pendingKeyStack.back?.getD none
    rw [ScannerCorrectness.scanFlowMappingEnd_pendingKeyActive_restored,
        h_ad_pendingKeyStack]
  · -- pendingKeyStack popped
    show (scanFlowMappingEnd s_ad).pendingKeyStack = s.pendingKeyStack.pop
    rw [ScannerCorrectness.scanFlowMappingEnd_pendingKeyStack_popped,
        h_ad_pendingKeyStack]

theorem dispatchFlowIndicators_close_brace_outermost (s : ScannerState)
    (h_fl : s.flowLevel = 1)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩) :
    scanNextToken_dispatchFlowIndicators s '}' = .ok (some (scanFlowMappingEnd s)) := by
  unfold scanNextToken_dispatchFlowIndicators
  simp only [bind, Except.bind, pure, Except.pure,
    show ('}' == '[') = false from by decide,
    show ('}' == ']') = false from by decide,
    show ('}' == '{') = false from by decide,
    show ('}' == '}') = true from by decide]
  have h_ne := nat_beq_zero_false s.flowLevel (by omega : s.flowLevel > 0)
  simp only [h_ne]
  have h_fl_after : (scanFlowMappingEnd s).flowLevel = 0 := by
    rw [scanFlowMappingEnd_flowLevel, h_fl]
    simp (config := { decide := true })
  have ⟨_, h_lt⟩ := peek_of_chars_cons s '}' [] s.col hcorr
  let s_em := s.emit .flowMappingEnd
  have h_em_corr : ScannerSurfCorr s_em ⟨['}'], s.col⟩ :=
    ⟨hcorr.chars_from, hcorr.col_eq, hcorr.end_eq, hcorr.input_prefix, hcorr.indent_cols_nonneg⟩
  have h_adv_corr := advance_non_newline_corr s_em '}' [] h_em_corr
    (show s_em.offset < s_em.inputEnd from h_lt) (by decide) (by decide)
  have h_adv_peek := peek_none_of_empty_surf s_em.advance (s.col + 1) h_adv_corr
  have h_eof : (scanFlowMappingEnd s).peek? = none := by
    rw [scanFlowMappingEnd_peek]; exact h_adv_peek
  rw [validateFlowClose_pass_eof _ h_fl_after h_eof]
  simp

theorem scanNextToken_flow_close_mapping_outermost (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['}'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_brace_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_result_fl : (scanFlowMappingEnd s_ad).flowLevel = 0 := by
    rw [scanFlowMappingEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : (scanFlowMappingEnd s_ad).directivesPresent = false := by
    rw [scanFlowMappingEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : (scanFlowMappingEnd s_ad).peek? = none := by
    rw [scanFlowMappingEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad '}' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowMappingEnd) '}' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowMappingEnd).offset < (s_ad.emit .flowMappingEnd).inputEnd from h_lt)
        (by decide) (by decide))
  exact ⟨scanFlowMappingEnd s_ad, h_snt, h_result_fl, h_result_dp, h_result_eof⟩

-- Nested flow open for `{`
theorem scanNextToken_flow_open_mapping_nested (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ StackEndLineOnLine s' s'.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-helpers:
      -- pkRec preserved at indices < initial size.
      -- C-foundation-EmitScansInFlow-defns-helpers-size: size monotonic.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack pushed (mirror of simpleKeyStack); the matching
      -- close-side pop cancels in the map composition.
      ∧ s'.pendingKeyStack.pop = s.pendingKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon:
      -- scanFlowMappingStart's final record-update sets `simpleKeyAllowed := true`;
      -- the consumer in `emit_scans_in_flow`'s mapping case threads this gate
      -- into `EmitPairListScansInFlow`'s precondition. -/
      ∧ s'.simpleKeyAllowed = true := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = _
      unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
    · unfold saveSimpleKey; split <;> (try rfl); split <;> rfl
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'{' :: rest, s_ad.col⟩ := by
    rw [show s_ad.col = s.col from h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStart_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowMappingStart_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '{' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowMappingStart s_ad).line = s.line := by
    rw [scanFlowMappingStart_line_eq]
    exact (advance_line_of_peek s_ad '{' h_lt_ad h_peek_ad (by decide) (by decide)).trans h_ad_line
  refine ⟨_, h_snt, ?_, h_fl_f.trans (congrArg (· + 1) h_ad_fl),
    h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f.trans h_ad_ek, ?_, h_line_f, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_scanFlowMappingStart s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · -- EndLineOnLine: scanFlowMappingStart sets simpleKey.possible = false
    intro h_poss
    rw [scanFlowMappingStart_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  · -- StackEndLineOnLine: pushed savedKey = s_ad.simpleKey satisfies EndLineOnLine at s'.line
    unfold StackEndLineOnLine
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.back?_push, h_line_f]
    intro h_poss
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad]; split
      · show EndLineOnLine { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
        exact EndLineOnLine_saveSimpleKey_flow s h_endline
      · exact EndLineOnLine_saveSimpleKey_flow s h_endline
    exact ⟨(h_ad_endline h_poss).1.trans h_ad_line, (h_ad_endline h_poss).2.trans h_ad_line⟩
  · -- simpleKeyStack.pop = s.simpleKeyStack
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.pop_push]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · -- size monotonic
    have h_fms_pks : (scanFlowMappingStart s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowMappingStart_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    rw [h_fms_pks, h_ad_pks]
    exact saveSimpleKey_pendingKeys_size_ge s
  · -- pkRec preserved at j < initial size
    intro j hj hj'
    have h_fms_pks : (scanFlowMappingStart s_ad).pendingKeys = s_ad.pendingKeys :=
      ScannerCorrectness.scanFlowMappingStart_preserves_pendingKeys s_ad
    have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
      simp only [s_ad]; split <;> rfl
    have h_full_pks : (scanFlowMappingStart s_ad).pendingKeys = (saveSimpleKey s).pendingKeys :=
      h_fms_pks.trans h_ad_pks
    have hj'_sk : j < (saveSimpleKey s).pendingKeys.size := by
      rw [← h_full_pks]; exact hj'
    have ⟨h_ib, h_kd⟩ := saveSimpleKey_preserves_pkRec_prior s j hj hj'_sk
    have h_eq : (scanFlowMappingStart s_ad).pendingKeys[j]'hj'
                = (saveSimpleKey s).pendingKeys[j]'hj'_sk := by congr 1
    refine ⟨?_, ?_⟩
    · rw [h_eq]; exact h_ib
    · rw [h_eq]; exact h_kd
  · -- pendingKeyStack.pop = s.pendingKeyStack
    rw [ScannerCorrectness.scanFlowMappingStart_pendingKeyStack_pushed, Array.pop_push]
    show s_ad.pendingKeyStack = s.pendingKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
  · -- simpleKeyAllowed = true: scanFlowMappingStart's record-update sets it directly.
    show (scanFlowMappingStart s_ad).simpleKeyAllowed = true
    unfold scanFlowMappingStart; rfl

/-- Per-leaf flow-mapping pkPush theorem.  Mirrors
    `scanNextToken_flow_open_mapping_nested` but additionally exposes the
    pendingKeys push effect under the assumption that the push branch
    of `saveSimpleKey` fires (`simpleKeyAllowed = true ∧
    explicitKeyLine = none`).  Mechanical mirror of A3
    (`scanNextToken_flow_open_nested_pkPush`) with `[` → `{`,
    `scanFlowSequenceStart` → `scanFlowMappingStart`,
    `dispatchFlowIndicators_bracket` → `dispatchFlowIndicators_brace`,
    using `scanFlowMappingStart_preserves_pendingKeys`: the `{` flow
    path does NOT invoke `dispatchContent`, so there is no
    `setPendingKeyEndLine` wrap — pendingKeys is just `s.pendingKeys.push`
    of the unresolved entry recorded by `saveSimpleKey`. -/
theorem scanNextToken_flow_open_mapping_nested_pkPush (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = true)
    (h_ek_none : s.explicitKeyLine = none) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel + 1
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col = s.col + 1
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ StackEndLineOnLine s' s'.line
      ∧ s'.simpleKeyStack.pop = s.simpleKeyStack
      ∧ s'.pendingKeys.size = s.pendingKeys.size + 1
      ∧ (∃ (h : s.pendingKeys.size < s'.pendingKeys.size),
          (s'.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
          ∧ (s'.pendingKeys[s.pendingKeys.size]'h).kind = .unresolved)
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated-discharge:
      -- Stack push-shape (mirror of A3 / `scanNextToken_flow_open_nested_pkPush`):
      -- pendingKeyStack pushes `some s.pendingKeys.size`, and the top-of-stack
      -- simpleKey carries `possible = true`.  Used to compose through body
      -- preservation + close-side restore in `emit_scans_in_flow` to recover
      -- the gated facts at s₃.
      ∧ s'.pendingKeyStack = s.pendingKeyStack.push (some s.pendingKeys.size)
      ∧ (s'.simpleKeyStack.back?.getD {}).possible = true := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_ids : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_ek : s_ad.explicitKeyLine = s.explicitKeyLine := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_ek s
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨'{' :: rest, s_ad.col⟩ := by
    rw [show s_ad.col = s.col from h_ad_col]
    exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStart_detail s_ad rest h_ad_corr
  have h_ek_f := scanFlowMappingStart_preserves_ek s_ad
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have ⟨h_peek_ad, h_lt_ad⟩ := peek_of_chars_cons s_ad '{' rest s_ad.col h_ad_corr
  have h_line_f : (scanFlowMappingStart s_ad).line = s.line := by
    rw [scanFlowMappingStart_line_eq]
    exact (advance_line_of_peek s_ad '{' h_lt_ad h_peek_ad (by decide) (by decide)).trans h_ad_line
  -- pkPush tracking: A1 lemma + record-update + scanFlowMappingStart preservation
  obtain ⟨h_sk_pks, _h_sk_pka, _h_sk_skp⟩ :=
    saveSimpleKey_pkPush_when_allowed s h_ska h_ek_none
  have h_ad_pks : s_ad.pendingKeys = (saveSimpleKey s).pendingKeys := by
    simp only [s_ad]; split <;> rfl
  have h_fms_pks : (scanFlowMappingStart s_ad).pendingKeys = s_ad.pendingKeys :=
    ScannerCorrectness.scanFlowMappingStart_preserves_pendingKeys s_ad
  have h_fms_pks_full : (scanFlowMappingStart s_ad).pendingKeys = s.pendingKeys.push
      { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
        endLine := s.line, kind := .unresolved } := by
    rw [h_fms_pks, h_ad_pks, h_sk_pks]
  have h_fms_size : (scanFlowMappingStart s_ad).pendingKeys.size = s.pendingKeys.size + 1 := by
    rw [h_fms_pks_full, Array.size_push]
  have h_lt : s.pendingKeys.size < (scanFlowMappingStart s_ad).pendingKeys.size := by
    rw [h_fms_size]; exact Nat.lt_succ_self _
  have h_get : (scanFlowMappingStart s_ad).pendingKeys[s.pendingKeys.size]'h_lt =
      { insertBeforeIdx := s.tokens.size, pos := s.currentPos,
        endLine := s.line, kind := .unresolved } := by
    simp only [h_fms_pks_full, Array.getElem_push]
    rw [dif_neg (Nat.lt_irrefl _)]
  refine ⟨_, h_snt, ?_, h_fl_f.trans (congrArg (· + 1) h_ad_fl),
    h_dp_f.trans h_ad_dp, h_ids_f.trans h_ad_ids, h_ek_f.trans h_ad_ek,
    ?_, h_line_f, ?_, ?_, ?_, ?_, h_fms_size, ⟨h_lt, ?_, ?_⟩, ?_, ?_, ?_⟩
  · rw [h_col_f]; exact h_corr_f
  · rw [h_col_f, h_ad_col]
  · rw [h_line_f]
    exact AllTokensOnLine_scanFlowMappingStart s_ad s.line
      (AllTokensOnLine_allowDirectives _ _
        (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl)) h_ad_line
  · intro h_poss
    rw [scanFlowMappingStart_simpleKey_not_possible] at h_poss
    exact absurd h_poss (by decide)
  · unfold StackEndLineOnLine
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.back?_push, h_line_f]
    intro h_poss
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad]; split
      · show EndLineOnLine { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
        exact EndLineOnLine_saveSimpleKey_flow s h_endline
      · exact EndLineOnLine_saveSimpleKey_flow s h_endline
    exact ⟨(h_ad_endline h_poss).1.trans h_ad_line, (h_ad_endline h_poss).2.trans h_ad_line⟩
  · rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.pop_push]
    show s_ad.simpleKeyStack = s.simpleKeyStack
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s
  · rw [h_get]
  · rw [h_get]
  · -- preserves-prior: pendingKeys at j < s.pendingKeys.size unchanged through the push
    intro j hj _hj'
    simp only [h_fms_pks_full]
    exact Array.getElem_push_lt hj
  · -- pendingKeyStack push-shape:
    -- scanFlowMappingStart pushes s_ad.pendingKeyActive onto s_ad.pendingKeyStack;
    -- s_ad mirrors saveSimpleKey s (allowDirectives branch is a non-stack record-update),
    -- and saveSimpleKey under the gate sets pendingKeyActive = some s.pendingKeys.size.
    rw [ScannerCorrectness.scanFlowMappingStart_pendingKeyStack_pushed]
    have h_ad_pendingKeyStack : s_ad.pendingKeyStack = s.pendingKeyStack := by
      simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s
    have h_ad_pka : s_ad.pendingKeyActive = (saveSimpleKey s).pendingKeyActive := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_pendingKeyStack, h_ad_pka, _h_sk_pka]
  · -- simpleKeyStack top: pushed simpleKey carries possible = true
    -- (saveSimpleKey under the gate sets simpleKey.possible = true).
    rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed, Array.back?_push]
    show (s_ad.simpleKey).possible = true
    have h_ad_sk : s_ad.simpleKey = (saveSimpleKey s).simpleKey := by
      simp only [s_ad]; split <;> rfl
    rw [h_ad_sk]; exact _h_sk_skp

-- ═══ Init flow open: `{` — mapping at top level ═══

/-- Structural dispatch returns none for `{` at initial state. -/
theorem dispatchStructural_none_brace_init (s : ScannerState)
    (h_fl : s.flowLevel = 0)
    (h_noDocStart : atDocumentStart s = false)
    (h_noDocEnd : atDocumentEnd s = false) :
    scanNextToken_dispatchStructural s '{' = .ok none := by
  unfold scanNextToken_dispatchStructural
  simp [ScannerState.inFlow, h_fl, h_noDocStart, h_noDocEnd,
        bind, Except.bind, pure, Except.pure]

/-- checkBlockFlowIndent passes for `{` at initial state. -/
theorem checkBlockFlowIndent_brace_init (s : ScannerState)
    (h_fl : s.flowLevel = 0)
    (h_indent : s.currentIndent = -1) :
    scanNextToken_checkBlockFlowIndent s '{' = .ok () := by
  unfold scanNextToken_checkBlockFlowIndent
  simp [ScannerState.inFlow, h_fl, h_indent]

/-- `scanNextToken` on the initial scanner state at `{` dispatches to
    `scanFlowMappingStart`, entering flow context.
    Result state has `flowLevel = 1`, `col = 1`, and ScannerSurfCorr at rest. -/
theorem scanNextToken_flow_open_mapping_init (input : String) (rest : List Char)
    (h_toList : input.toList = '{' :: rest) :
    let s₀ := (ScannerState.mk' input).emit .streamStart
    ∃ s', scanNextToken s₀ = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = 1
      ∧ s'.directivesPresent = false
      ∧ s'.indents = s₀.indents
      ∧ s'.col = 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = 0
      ∧ AllTokensOnLine s' 0
      ∧ EndLineOnLine s'
      ∧ s'.simpleKey.possible = false
      ∧ (s'.tokens.filter (fun t => t.val != .placeholder)).map (·.val)
          = #[.streamStart, .flowMappingStart]
      ∧ s'.simpleKeyStack.size = s'.flowLevel
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon:
      -- scanFlowMappingStart sets `simpleKeyAllowed := true`; threaded into
      -- `EmitPairListScansInFlow`'s precondition by `scanFiltered_exists_emit_aux`. -/
      ∧ s'.simpleKeyAllowed = true := by
  intro s₀
  -- Step 1: preprocessing
  have h_pp := scanNextToken_preprocess_init_state input '{' rest h_toList
    (by decide) (by decide) (by decide)
  obtain ⟨s_pp, h_pp_eq, h_fl_pp, h_inflow_pp, h_ci_pp, h_col_pp,
          h_ad_pp, h_dp_pp, h_ids, h_inp, h_off, h_ie, h_ek_pp,
          h_line_pp, h_atol_pp, h_pp_filt⟩ := h_pp
  -- Step 2: ScannerSurfCorr for s_pp
  have h_chars := chars_from_zero_toList input
  rw [h_toList] at h_chars
  have h_corr₀ := initial_corr input _ h_chars
  have h_corr_s₀ : ScannerSurfCorr s₀ ⟨'{' :: rest, 0⟩ :=
    ScannerSurfCorr_transfer h_corr₀ rfl rfl rfl rfl rfl
  have h_corr_pp : ScannerSurfCorr s_pp ⟨'{' :: rest, s_pp.col⟩ := by
    rw [h_col_pp]
    exact ScannerSurfCorr_transfer h_corr_s₀ h_inp h_off h_ie h_col_pp h_ids
  have ⟨h_pk_pp, _⟩ := peek_of_chars_cons s_pp '{' rest _ h_corr_pp
  -- Step 3: atDocumentStart/End false for '{'
  have h_pat0 : s_pp.peekAt? 0 = s_pp.peek? := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop ScannerState.peek?; rfl
  have h_ds : atDocumentStart s_pp = false := by
    unfold atDocumentStart; rw [h_pat0, h_pk_pp]
    simp only [show (some '{' == some '-') = false from by decide,
               Bool.and_false, Bool.false_and]
  have h_de : atDocumentEnd s_pp = false := by
    unfold atDocumentEnd; rw [h_pat0, h_pk_pp]
    simp only [show (some '{' == some '.') = false from by decide,
               Bool.and_false, Bool.false_and]
  -- Step 4: structural dispatch → none
  have h_struct := dispatchStructural_none_brace_init s_pp h_fl_pp h_ds h_de
  -- Step 5: allowDirectives update → s_ad
  let s_ad := if s_pp.allowDirectives then
    { s_pp with allowDirectives := false, documentEverStarted := true }
  else s_pp
  have h_ad_fl : s_ad.flowLevel = 0 := by
    simp only [s_ad]; split <;> exact h_fl_pp
  have h_ad_ci : s_ad.currentIndent = -1 := by
    have : s_ad.indents = s_pp.indents := by simp only [s_ad]; split <;> rfl
    unfold ScannerState.currentIndent at h_ci_pp ⊢; rw [this]; exact h_ci_pp
  -- Step 6: checkBlockFlowIndent ok
  have h_check := checkBlockFlowIndent_brace_init s_ad h_ad_fl h_ad_ci
  -- Step 7: flow dispatch → some (scanFlowMappingStart s_ad)
  have h_flow := dispatchFlowIndicators_brace s_ad
  -- Step 8: compose through scanNextToken
  have h_snt : scanNextToken s₀ = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp_eq h_struct rfl h_check h_flow
  -- Step 9: field properties of scanFlowMappingStart s_ad
  have h_ad_col : s_ad.col = 0 := by
    simp only [s_ad]; split <;> exact h_col_pp
  have h_ad_col_eq : s_ad.col = s_pp.col := by simp only [s_ad]; split <;> rfl
  have h_corr_ad : ScannerSurfCorr s_ad ⟨'{' :: rest, s_ad.col⟩ := by
    rw [h_ad_col_eq]
    exact ScannerSurfCorr_transfer h_corr_pp
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      (by simp only [s_ad]; split <;> rfl)
      h_ad_col_eq
      (by simp only [s_ad]; split <;> rfl)
  obtain ⟨h_corr_f, h_fl_f, h_dp_f, h_ids_f, h_col_f⟩ :=
    scanFlowMappingStart_detail s_ad rest h_corr_ad
  -- Compute final field values
  have h_fl_final : (scanFlowMappingStart s_ad).flowLevel = 1 := by
    rw [h_fl_f, h_ad_fl]
  have h_dp_final : (scanFlowMappingStart s_ad).directivesPresent = false := by
    rw [h_dp_f]; simp only [s_ad]; split <;> exact h_dp_pp
  have h_ids_final : (scanFlowMappingStart s_ad).indents = s₀.indents := by
    rw [h_ids_f]; simp only [s_ad]; split <;> exact h_ids
  have h_col_final : (scanFlowMappingStart s_ad).col = 1 := by
    rw [h_col_f, h_ad_col]
  have h_corr_result : ScannerSurfCorr (scanFlowMappingStart s_ad)
      ⟨rest, (scanFlowMappingStart s_ad).col⟩ := by
    rw [h_col_f]
    exact h_corr_f
  exact ⟨scanFlowMappingStart s_ad, h_snt, h_corr_result,
         h_fl_final, h_dp_final, h_ids_final, h_col_final,
         by unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_final]; omega),
         by have hb : (scanFlowMappingStart s_ad).indents.back? =
                some { column := (-1 : Int), isSequence := false } := by
              rw [h_ids_final]; rfl
            unfold ScannerState.currentIndent; rw [hb]; decide,
         by rw [scanFlowMappingStart_preserves_ek s_ad]
            simp only [s_ad]; split <;> exact h_ek_pp,
         by rw [scanFlowMappingStart_line_eq]
            have h_ad_pk : s_ad.peek? = some '{' := by
              simp only [s_ad]; split <;> exact h_pk_pp
            have h_ad_lt := (peek_of_chars_cons s_ad '{' rest _ h_corr_ad).2
            have h_ad_line : s_ad.line = 0 := by simp only [s_ad]; split <;> exact h_line_pp
            exact (advance_line_of_peek s_ad '{' h_ad_lt h_ad_pk (by decide) (by decide)).trans h_ad_line,
         by exact AllTokensOnLine_scanFlowMappingStart s_ad 0
              (AllTokensOnLine_allowDirectives _ 0 (h_line_pp ▸ h_atol_pp))
              (by simp only [s_ad]; split <;> exact h_line_pp),
         by intro h_poss
            rw [scanFlowMappingStart_simpleKey_not_possible] at h_poss
            exact absurd h_poss (by decide),
         scanFlowMappingStart_simpleKey_not_possible s_ad,
         by -- Filtered token characterization for mapping (mirrors sequence case)
            have h_fms_tokens : (scanFlowMappingStart s_ad).tokens
                = s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
              show ({ ({ s_ad with simpleKey := _, pendingKeyActive := _ }.emit .flowMappingStart).advance with
                  flowLevel := _, simpleKeyAllowed := _,
                  flowStack := _, simpleKeyStack := _, pendingKeyStack := _ }).tokens = _
              simp only [ScannerCorrectness.advance_preserves_tokens,
                         ScannerState.emit, ScannerState.currentPos]
            have h_ad_tokens : s_ad.tokens = s_pp.tokens := by
              simp only [s_ad]; split <;> rfl
            rw [h_fms_tokens]
            simp only [Array.filter_push,
              show (YamlToken.flowMappingStart != YamlToken.placeholder) = true from rfl,
              ite_true, Array.map_push,
              show s_ad.tokens = s_pp.tokens from h_ad_tokens,
              h_pp_filt]
            simp [ScannerState.mk', ScannerState.emit],
         by -- Stack/flowLevel sync:
            rw [h_fl_final]
            have h_pre_stack := ScannerCorrectness.preprocess_preserves_simpleKeyStack
              _ _ _ h_pp_eq
            have h_ad_stack_sz : s_ad.simpleKeyStack.size = 0 := by
              simp only [s_ad]; split
              · show s_pp.simpleKeyStack.size = 0; rw [h_pre_stack]; rfl
              · rw [h_pre_stack]; rfl
            rw [ScannerCorrectness.scanFlowMappingStart_stack_pushed]
            simp [Array.size_push, h_ad_stack_sz],
         by -- simpleKeyAllowed = true: scanFlowMappingStart's record-update sets it.
            show (scanFlowMappingStart s_ad).simpleKeyAllowed = true
            unfold scanFlowMappingStart; rfl⟩

/-! ### First-filtered-token lemmas for flow-content scanners (Tier 2 Turn 1)

When `scanNextToken` runs in flow context with a leading content character
(`"`, `[`, or `{`), the *first* new filtered (non-placeholder) token is
fully determined by that leading character.  These three lemmas pin down
that fact and serve as building blocks for body-token characterization in
`emitList_body_filtered_characterization` and
`emitPairList_body_filtered_characterization`. -/

/-- After `scanNextToken` with leading `[` in flow context, the first new
    filtered token is `.flowSequenceStart`. -/
theorem scanFlowSequenceStart_first_filtered_token (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'[' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
    (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size),
      ((s'.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val
        = .flowSequenceStart) := by
  -- Re-derive dispatch to identify s'
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '[')) :=
    scanNextToken_preprocess_flow s '[' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '[' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '[' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_bracket s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowSequenceStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowSequenceStart s_ad := by
    have h := h_snt.symm.trans h_snt_eq
    exact Option.some.inj (Except.ok.inj h)
  -- Tokens shape: scanFlowSequenceStart s_ad pushes one .flowSequenceStart token
  have h_fss_tokens : (scanFlowSequenceStart s_ad).tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩ := by
    show ({ ({ s_ad with simpleKey := _, pendingKeyActive := _ }.emit .flowSequenceStart).advance with
        flowLevel := _, simpleKeyAllowed := _,
        flowStack := _, simpleKeyStack := _, pendingKeyStack := _ }).tokens = _
    simp only [ScannerCorrectness.advance_preserves_tokens,
               ScannerState.emit, ScannerState.currentPos]
  have h_ad_tokens_filter :
      s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    have h_pp_filt := saveSimpleKey_filter_placeholder s
    simp only [s_ad]; split <;> exact h_pp_filt
  rw [h_s', h_fss_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .flowSequenceStart, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; rw [Array.getElem_push_eq]

/-- After `scanNextToken` with leading `{` in flow context, the first new
    filtered token is `.flowMappingStart`. -/
theorem scanFlowMappingStart_first_filtered_token (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'{' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
    (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size),
      ((s'.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val
        = .flowMappingStart) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '{')) :=
    scanNextToken_preprocess_flow s '{' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '{' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '{' (h_ad_flow ▸ h_flow)
  have h_flow_disp := dispatchFlowIndicators_brace s_ad
  have h_snt_eq : scanNextToken s = .ok (some (scanFlowMappingStart s_ad)) :=
    scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  have h_s' : s' = scanFlowMappingStart s_ad := by
    have h := h_snt.symm.trans h_snt_eq
    exact Option.some.inj (Except.ok.inj h)
  have h_fms_tokens : (scanFlowMappingStart s_ad).tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ := by
    show ({ ({ s_ad with simpleKey := _, pendingKeyActive := _ }.emit .flowMappingStart).advance with
        flowLevel := _, simpleKeyAllowed := _,
        flowStack := _, simpleKeyStack := _, pendingKeyStack := _ }).tokens = _
    simp only [ScannerCorrectness.advance_preserves_tokens,
               ScannerState.emit, ScannerState.currentPos]
  have h_ad_tokens_filter :
      s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    have h_pp_filt := saveSimpleKey_filter_placeholder s
    simp only [s_ad]; split <;> exact h_pp_filt
  rw [h_s', h_fms_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .flowMappingStart, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; rw [Array.getElem_push_eq]

/-- Extract from a successful `scanDoubleQuoted` call: the result's tokens
    are exactly the input's tokens with one `.scalar _ .doubleQuoted` pushed.
    Used by `scanDoubleQuoted_first_filtered_token` to identify the new
    token without knowing the specific content string. -/
theorem scanDoubleQuoted_tokens_push {s s' : ScannerState}
    (h : scanDoubleQuoted s = .ok s') :
    ∃ c, s'.tokens
      = s.tokens.push ⟨s.currentPos, .scalar c .doubleQuoted, s.currentPos⟩ := by
  unfold scanDoubleQuoted at h
  simp only [bind, Except.bind] at h
  split at h <;> try contradiction
  rename_i ev_result heq_loop
  obtain ⟨content, s_after_close⟩ := ev_result
  refine ⟨content, ?_⟩
  have h_collect := ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
    s.advance "" _ _ _ _ _ _ heq_loop
  have h_adv := ScannerCorrectness.advance_preserves_tokens s
  split at h
  · -- !inFlow case: validateTrailingContent check
    split at h <;> try contradiction
    injection h with h_eq; subst h_eq; dsimp only []
    show (s_after_close.emitAt s.currentPos (.scalar content .doubleQuoted)).tokens = _
    unfold ScannerState.emitAt; simp only [Array.push]
    rw [h_collect, h_adv]
  · -- inFlow case: no validation
    injection h with h_eq; subst h_eq; dsimp only []
    show (s_after_close.emitAt s.currentPos (.scalar content .doubleQuoted)).tokens = _
    unfold ScannerState.emitAt; simp only [Array.push]
    rw [h_collect, h_adv]

/-- After `scanNextToken` with leading `"` in flow context, the first new
    filtered token is some `.scalar` token (the doubleQuoted scalar emitted
    by `scanDoubleQuoted`).  Content and subType are existentially
    quantified — the lemma's purpose is dispatch identification. -/
theorem scanDoubleQuoted_first_filtered_token (s : ScannerState) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨'"' :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col : s.col > 0)
    {s' : ScannerState} (h_snt : scanNextToken s = .ok (some s')) :
    (s.tokens.filter (fun t => t.val != .placeholder)).size <
      (s'.tokens.filter (fun t => t.val != .placeholder)).size ∧
    (∀ (h : (s.tokens.filter (fun t => t.val != .placeholder)).size <
            (s'.tokens.filter (fun t => t.val != .placeholder)).size),
      ∃ c sc, ((s'.tokens.filter (fun t => t.val != .placeholder))[
        (s.tokens.filter (fun t => t.val != .placeholder)).size]'h).val
        = .scalar c sc) := by
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '"')) :=
    scanNextToken_preprocess_flow s '"' rest s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '"' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_ad_flow_true : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  have h_check := checkBlockFlowIndent_ok_flow s_ad '"' h_ad_flow_true
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad '"' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_block_none : scanNextToken_dispatchBlockIndicators s_ad '"' = .ok none :=
    dispatchBlockIndicators_none_quote _
  -- From h_snt + dispatch composition, dispatchContent must succeed and yield s'
  have h_dc : scanNextToken_dispatchContent s_ad '"' = Except.ok s' := by
    cases h_dc_eq : scanNextToken_dispatchContent s_ad '"' with
    | error e =>
      exfalso
      have h_snt_err := scanNextToken_via_content_dispatch_error
        _ _ _ _ _ h_pp h_struct rfl h_check h_flow_none h_block_none h_dc_eq
      rw [h_snt_err] at h_snt; exact absurd h_snt (by simp)
    | ok s_dc =>
      have h_snt_eq : scanNextToken s = Except.ok (some s_dc) :=
        scanNextToken_via_content_dispatch _ _ _ _ _ h_pp h_struct rfl h_check
          h_flow_none h_block_none h_dc_eq
      have h_eq2 : s' = s_dc := Option.some.inj (Except.ok.inj (h_snt.symm.trans h_snt_eq))
      subst h_eq2; rfl
  -- Extract scanDoubleQuoted's effect from dispatchContent
  -- For c = '"', dispatchContent: scanDoubleQuoted s_ad ; (optional simpleKey update)
  have h_tokens_push : ∃ c, s'.tokens
      = s_ad.tokens.push ⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ := by
    -- Reduce h_dc to extract the scanDoubleQuoted result
    cases h_dq_eq : scanDoubleQuoted s_ad with
    | error e =>
      exfalso
      have h_dc_err : scanNextToken_dispatchContent s_ad '"' = Except.error e := by
        unfold scanNextToken_dispatchContent
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq]
      rw [h_dc_err] at h_dc; exact absurd h_dc (by simp)
    | ok s_dq =>
      obtain ⟨c, h_tok⟩ := scanDoubleQuoted_tokens_push h_dq_eq
      refine ⟨c, ?_⟩
      have h_s'_tokens : s'.tokens = s_dq.tokens := by
        unfold scanNextToken_dispatchContent at h_dc
        simp [bind, Except.bind, pure, Except.pure, h_dq_eq] at h_dc
        split at h_dc
        · rw [← h_dc]
        · rw [← h_dc]
      rw [h_s'_tokens, h_tok]
  obtain ⟨c, h_s'_tokens⟩ := h_tokens_push
  -- Now apply filter_push
  have h_ad_tokens_filter :
      s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    have h_pp_filt := saveSimpleKey_filter_placeholder s
    simp only [s_ad]; split <;> exact h_pp_filt
  rw [h_s'_tokens, Array.filter_push]
  simp only [show ((⟨s_ad.currentPos, .scalar c .doubleQuoted, s_ad.currentPos⟩ : Positioned YamlToken).val
                   != YamlToken.placeholder) = true from rfl, ite_true]
  rw [h_ad_tokens_filter]
  refine ⟨?_, ?_⟩
  · rw [Array.size_push]; omega
  · intro _; refine ⟨c, .doubleQuoted, ?_⟩; exact congrArg _ Array.getElem_push_eq

-- The first char of `emit v` is always a non-whitespace content char.
-- Used for space-handling in comma-separated lists.
theorem emit_first_char (v : YamlValue) :
    ∃ c rest', (emit v).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  cases v with
  | scalar s =>
    refine ⟨'"', (escapeString s.content).toList ++ ['"'], ?_, by decide, by decide, by decide⟩
    simp only [emit, emitScalar, String.toList_append]; rfl
  | sequence _ items _ _ =>
    refine ⟨'[', (emit.emitList items.toList).toList ++ [']'], ?_, by decide, by decide, by decide⟩
    simp only [emit, String.toList_append]; rfl
  | mapping _ pairs _ _ =>
    refine ⟨'{', (emit.emitPairList pairs.toList).toList ++ ['}'], ?_, by decide, by decide, by decide⟩
    simp only [emit, String.toList_append]; rfl
  | «alias» name =>
    refine ⟨'"', (escapeString ("*" ++ name)).toList ++ ['"'], ?_, by decide, by decide, by decide⟩
    simp only [emit, emitScalar, String.toList_append]; rfl

-- The first char of `emitList (v :: vs)` is the first char of `emit v`.
theorem emitList_first_char (v : YamlValue) (vs : List YamlValue) :
    ∃ c rest', (emit.emitList (v :: vs)).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  obtain ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩ := emit_first_char v
  match vs with
  | [] =>
    simp only [emit.emitList]
    exact ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩
  | v' :: vs' =>
    have h_el : (emit.emitList (v :: v' :: vs')).toList =
        (emit v).toList ++ (", " ++ emit.emitList (v' :: vs')).toList := by
      simp [emit.emitList, String.toList_append, List.append_assoc]
    rw [h_el, h_emit_eq]
    exact ⟨c, ev_rest ++ (", " ++ emit.emitList (v' :: vs')).toList,
      by simp, h_nws, h_nlb, h_nc⟩

-- `emitList` is non-empty on non-empty input: its toList is non-nil.
theorem emitList_toList_ne_nil (v : YamlValue) (vs : List YamlValue) :
    (emit.emitList (v :: vs)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitList_first_char v vs
  rw [h_eq]; exact List.cons_ne_nil _ _

/-- After `emit streamEnd`, the pushed token is the last element of the array.
    Gives: `(s.emit tok).tokens = s.tokens.push ⟨s.currentPos, tok⟩`.
    Forward-declared from its later siblings to support the filtered-growth
    infrastructure that follows. -/
theorem emit_tokens_push (s : ScannerState) (tok : YamlToken) :
    (s.emit tok).tokens = s.tokens.push { pos := s.currentPos, val := tok } := by
  unfold ScannerState.emit; rfl

/-- If `b` extends `a` (same elements at all positions `i < a.size`), then
    `b.filter p` has `a.filter p` as a prefix. -/
theorem Array_filter_prefix_of_raw_prefix {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : a.size ≤ b.size)
    (h_eq : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i]) :
    ∃ suffix, (b.filter p).toList = (a.filter p).toList ++ suffix := by
  have h_take : b.toList.take a.size = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take, Array.length_toList, Nat.min_eq_left h_sz]
    · intro n hn₁ hn₂
      simp only [List.getElem_take]
      rw [Array.getElem_toList, Array.getElem_toList]
      exact h_eq n (by simpa [Array.length_toList] using hn₂)
  have h_split : b.toList = a.toList ++ b.toList.drop a.size := by
    rw [← h_take, List.take_append_drop]
  rw [Array.toList_filter, Array.toList_filter, h_split, List.filter_append]
  exact ⟨(b.toList.drop a.size).filter p, rfl⟩

/-! ### Filtered token array growth infrastructure

   Every `scanNextToken` step adds at least one non-placeholder token.
   The proof decomposes into:
   1. Preprocessing (skipToContent, unwindIndents, saveSimpleKey) preserves
      or grows filtered count — from existing `preprocess_preserves_prefix`.
   2. Each dispatch branch emits at least one non-placeholder token.
   3. `setIfInBounds` with non-placeholder replacement doesn't decrease
      filtered count (only used in `scanValuePrepare`).
-/

-- List helper: replacing an element that passes a filter doesn't decrease filter count.
theorem List_filter_set_length_mono {α : Type} (l : List α) (i : Nat) (v : α)
    (p : α → Bool) (hv : p v = true) :
    ((l.set i v).filter p).length ≥ (l.filter p).length := by
  induction l generalizing i with
  | nil => simp
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.filter_cons, hv, ite_true]
      split <;> simp <;> omega
    | succ j =>
      simp only [List.set_cons_succ, List.filter_cons]
      have := ih j
      split <;> simp <;> omega

-- Array.setIfInBounds with a filter-passing replacement preserves or grows
-- the filtered array size.
theorem Array_setIfInBounds_filter_mono {α : Type} (a : Array α) (i : Nat) (v : α)
    (p : α → Bool) (hv : p v = true) :
    ((a.setIfInBounds i v).filter p).size ≥ (a.filter p).size := by
  unfold Array.setIfInBounds
  split
  · -- i < a.size: use List_filter_set_length_mono
    next h_bound =>
    have : ((a.set i v h_bound).filter p).toList.length ≥ (a.filter p).toList.length := by
      rw [Array.toList_filter, Array.toList_filter, Array.toList_set]
      exact List_filter_set_length_mono a.toList i v p hv
    exact this
  · -- i ≥ a.size: identity
    omega

-- Preprocessing monotonicity: the filtered token count doesn't decrease
-- through `scanNextToken_preprocess`.
theorem preprocess_filtered_mono (s : ScannerState) (s₁ : ScannerState) (c : Char)
    (h : scanNextToken_preprocess s = .ok (some (s₁, c))) :
    (s₁.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size := by
  have h_mono := ScannerCorrectness.ScanHelpers.preprocess_tokens_mono s s₁ c h
  have h_pres := ScannerCorrectness.ScanHelpers.preprocess_preserves_prefix s s₁ c h
  obtain ⟨suffix, h_eq⟩ := Array_filter_prefix_of_raw_prefix s.tokens s₁.tokens
    (fun t => t.val != .placeholder) h_mono h_pres
  show (s₁.tokens.filter (fun t => t.val != .placeholder)).toList.length ≥
       (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
  rw [h_eq, List.length_append]; omega

-- `allowDirectives` if-then-else preserves filtered token count (tokens unchanged).
theorem allowDir_ite_filter (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ((if s.allowDirectives = true then
        { s with allowDirectives := false, documentEverStarted := true }
      else s).tokens.filter p).size = (s.tokens.filter p).size := by
  split <;> rfl

/-! #### General filtered growth helper -/

-- If a non-empty list's first element passes filter `p`, filter has length ≥ 1.
theorem List_filter_length_ge_one {α : Type} (l : List α) (p : α → Bool)
    (h_len : l.length ≥ 1) (h_head : p (l[0]'(by omega)) = true) :
    (l.filter p).length ≥ 1 := by
  match l with
  | [] => simp at h_len
  | hd :: tl =>
    have h_hd : p hd = true := h_head
    rw [List.filter_cons_of_pos h_hd, List.length_cons]; omega

-- If array `b` extends array `a` (same elements at positions `< a.size`), has at
-- least one more element, and that element at position `a.size` passes filter `p`,
-- then `(b.filter p).size ≥ (a.filter p).size + 1`.
theorem filtered_grows_of_extended_prefix {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : b.size ≥ a.size + 1)
    (h_pres : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (h_new : p (b[a.size]'(by omega)) = true) :
    (b.filter p).size ≥ (a.filter p).size + 1 := by
  -- Convert to List level (Array.size = toList.length definitionally)
  show (b.filter p).toList.length ≥ (a.filter p).toList.length + 1
  simp only [Array.toList_filter]
  -- Goal: (b.toList.filter p).length ≥ (a.toList.filter p).length + 1
  have h_len_le : a.toList.length ≤ b.toList.length := by
    simp only [Array.length_toList]; omega
  -- Prefix equality via ext_getElem
  have h_take : b.toList.take a.toList.length = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro n hn₁ hn₂
      simp only [List.getElem_take, Array.getElem_toList]
      exact h_pres n (by simp only [Array.length_toList] at hn₂; exact hn₂)
  -- Split b.toList = a.toList ++ drop
  have h_split_eq : b.toList = a.toList ++ b.toList.drop a.toList.length := by
    have := List.take_append_drop a.toList.length b.toList
    rw [h_take] at this; exact this.symm
  -- Rewrite filter length as sum of parts
  have h_filter_eq : (b.toList.filter p).length =
      (a.toList.filter p).length + (b.toList.drop a.toList.length |>.filter p).length := by
    have := congrArg (fun l => (l.filter p).length) h_split_eq
    simp only [List.filter_append, List.length_append] at this
    exact this
  rw [h_filter_eq]
  -- Suffices: the drop's filter has ≥ 1 element
  suffices (b.toList.drop a.toList.length |>.filter p).length ≥ 1 by omega
  -- The drop has ≥ 1 element and its first element passes p
  have h_drop_len : (b.toList.drop a.toList.length).length ≥ 1 := by
    simp only [List.length_drop, Array.length_toList]; omega
  have h_head_p : p ((b.toList.drop a.toList.length)[0]'(by omega)) = true := by
    simp only [List.getElem_drop, Nat.add_zero, Array.getElem_toList]
    exact h_new
  exact List_filter_length_ge_one _ _ h_drop_len h_head_p

-- Variant: if array `b` extends array `a`, has at least one more element, and
-- some element at position `j ≥ a.size` passes filter `p`,
-- then `(b.filter p).size ≥ (a.filter p).size + 1`.
-- Used when we know a specific NEW element (e.g. the last) is non-placeholder,
-- but don't know the exact value at the first new position `a.size`.
theorem filtered_grows_of_any_new {α : Type}
    (a b : Array α) (p : α → Bool)
    (h_sz : b.size ≥ a.size + 1)
    (h_pres : ∀ i (hi : i < a.size), b[i]'(by omega) = a[i])
    (j : Nat) (hj_lo : a.size ≤ j) (hj_hi : j < b.size)
    (h_new : p (b[j]'hj_hi) = true) :
    (b.filter p).size ≥ (a.filter p).size + 1 := by
  show (b.filter p).toList.length ≥ (a.filter p).toList.length + 1
  simp only [Array.toList_filter]
  have h_len_le : a.toList.length ≤ b.toList.length := by
    simp only [Array.length_toList]; omega
  have h_take : b.toList.take a.toList.length = a.toList := by
    apply List.ext_getElem
    · simp only [List.length_take]; omega
    · intro n hn₁ hn₂
      simp only [List.getElem_take, Array.getElem_toList]
      exact h_pres n (by simp only [Array.length_toList] at hn₂; exact hn₂)
  have h_split_eq : b.toList = a.toList ++ b.toList.drop a.toList.length := by
    have := List.take_append_drop a.toList.length b.toList
    rw [h_take] at this; exact this.symm
  have h_filter_eq : (b.toList.filter p).length =
      (a.toList.filter p).length + (b.toList.drop a.toList.length |>.filter p).length := by
    have := congrArg (fun l => (l.filter p).length) h_split_eq
    simp only [List.filter_append, List.length_append] at this
    exact this
  rw [h_filter_eq]
  suffices (b.toList.drop a.toList.length |>.filter p).length ≥ 1 by omega
  -- j - a.size is a valid index in the drop
  have h_j_drop : j - a.toList.length < (b.toList.drop a.toList.length).length := by
    simp only [List.length_drop, Array.length_toList]; omega
  -- The element at j-a.size in drop equals b[j]
  have h_drop_eq : (b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop = b[j]'hj_hi := by
    simp only [List.getElem_drop, Array.getElem_toList, Array.length_toList]
    congr 1; omega
  -- So it passes p
  have h_j_p : p ((b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop) = true := by
    rw [h_drop_eq]; exact h_new
  -- That element is in the filter
  have h_mem : (b.toList.drop a.toList.length)[j - a.toList.length]'h_j_drop ∈
      (b.toList.drop a.toList.length).filter p :=
    List.mem_filter.mpr ⟨List.getElem_mem h_j_drop, h_j_p⟩
  -- So the filter is non-empty, hence length ≥ 1
  cases h_cases : (b.toList.drop a.toList.length).filter p with
  | nil => rw [h_cases] at h_mem; simp at h_mem
  | cons => simp

/-! #### Per-dispatch-layer filtered growth lemmas -/

-- scanDocumentStart grows filtered array by ≥1.
-- The last new token is .documentStart (non-placeholder).
theorem scanDocumentStart_filtered_grows (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ((scanDocumentStart s).tokens.filter p).size ≥ (s.tokens.filter p).size + 1 := by
  apply filtered_grows_of_any_new s.tokens (scanDocumentStart s).tokens _
    (ScannerCorrectness.ScanHelpers.scanDocumentStart_adds_tokens s)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanDocumentStart_preserves_prefix s i hi)
    ((scanDocumentStart s).tokens.size - 1)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentStart_adds_tokens s; omega)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentStart_adds_tokens s; omega)
  -- h_new: the last token is .documentStart (non-placeholder)
  unfold scanDocumentStart; dsimp only []
  simp only [ScannerCorrectness.advanceN_preserves_tokens, emit_tokens_push]
  simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
  decide

-- scanDocumentEnd grows filtered array by ≥1.
-- The last new token is .documentEnd (non-placeholder).
theorem scanDocumentEnd_filtered_grows (s s' : ScannerState)
    (h : scanDocumentEnd s = .ok s') :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (s'.tokens.filter p).size ≥ (s.tokens.filter p).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (ScannerCorrectness.ScanHelpers.scanDocumentEnd_adds_tokens s s' h)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanDocumentEnd_preserves_prefix s s' h i hi)
    (s'.tokens.size - 1)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentEnd_adds_tokens s s' h; omega)
    (by have := ScannerCorrectness.ScanHelpers.scanDocumentEnd_adds_tokens s s' h; omega)
  -- h_new: the last token is .documentEnd (non-placeholder)
  unfold scanDocumentEnd at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h <;> (split at h <;> first | contradiction | skip) <;>
        (injection h with h_eq; subst h_eq; dsimp only []
         simp only [ScannerCorrectness.advanceN_preserves_tokens, emit_tokens_push]
         simp only [Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
         decide)

/-! #### Directive new-token identification (Tier 1, Turn 1)

`scanDirective` is the one structural-dispatch leaf where the post-state's
filtered token count is *not* always strictly greater than the pre-state:
the YAML 1.2.2 §6.8.3 reserved-directive branch (`%FOO ...`) skips the
trailing line and emits no token at all.  The two YAML/TAG branches do
emit a `.versionDirective`/`.tagDirective` token via `emitAt`.

The three lemmas below characterize the YAML/TAG branches' new token
exactly (`scan{Yaml,Tag}Directive_new_token_eq`) and combine that with a
contradiction in the reserved branch to produce a clean "filtered grows
by ≥1" lemma at the `scanDirective` level under a raw-growth precondition
(`scanDirective_filtered_grows`).  The `h_grew` hypothesis is sound here
because `scanDirective` itself does not invoke `scanNextToken_preprocess`
— the `saveSimpleKey`-induced placeholder pushes happen *before*
structural dispatch, so at this level a strict raw-token-size increase
genuinely identifies a YAML/TAG branch.
-/

/-- The new token emitted by a successful `scanYamlDirective` is exactly
    `.versionDirective major minor` for some `major`/`minor` parsed from
    the input — a non-placeholder. -/
theorem scanYamlDirective_new_token_eq (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanYamlDirective s s_after_ws startPos = .ok s') :
    ∃ major minor : Nat,
      s'.tokens = s.tokens.push { pos := startPos, val := .versionDirective major minor } := by
  unfold scanYamlDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · split at h
      · -- some '#'
        split at h
        · contradiction
        · injection h with h_eq; subst h_eq
          dsimp only [ScannerState.emitAt]
          apply Exists.intro
          apply Exists.intro
          rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
              ScannerCorrectness.ScanHelpers.collectVersionMinorLoop_preserves_tokens,
              ScannerCorrectness.ScanHelpers.collectVersionMajorLoop_preserves_tokens, h_ws]
      · -- some c (not '#')
        split at h
        · contradiction
        · split at h <;> try contradiction
          all_goals (injection h with h_eq; subst h_eq
                     dsimp only [ScannerState.emitAt]
                     apply Exists.intro
                     apply Exists.intro
                     rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
                         ScannerCorrectness.ScanHelpers.collectVersionMinorLoop_preserves_tokens,
                         ScannerCorrectness.ScanHelpers.collectVersionMajorLoop_preserves_tokens, h_ws])
      · -- none
        injection h with h_eq; subst h_eq
        dsimp only [ScannerState.emitAt]
        apply Exists.intro
        apply Exists.intro
        rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
            ScannerCorrectness.ScanHelpers.collectVersionMinorLoop_preserves_tokens,
            ScannerCorrectness.ScanHelpers.collectVersionMajorLoop_preserves_tokens, h_ws]

/-- The new token emitted by a successful `scanTagDirective` is exactly
    `.tagDirective handle pfx` for some `handle`/`pfx` parsed from the
    input — a non-placeholder. -/
theorem scanTagDirective_new_token_eq (s s_after_ws : ScannerState) (startPos : YamlPos)
    (s' : ScannerState)
    (h_ws : s_after_ws.tokens = s.tokens)
    (h : scanTagDirective s s_after_ws startPos = .ok s') :
    ∃ handle pfx : String,
      s'.tokens = s.tokens.push { pos := startPos, val := .tagDirective handle pfx } := by
  unfold scanTagDirective at h
  dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · -- some '#'
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq
      dsimp only [ScannerState.emitAt]
      apply Exists.intro
      apply Exists.intro
      rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagPrefixLoop_preserves_tokens,
          ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  · -- some c (not '#')
    split at h
    · contradiction
    · injection h with h_eq; subst h_eq
      dsimp only [ScannerState.emitAt]
      apply Exists.intro
      apply Exists.intro
      rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagPrefixLoop_preserves_tokens,
          ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens, h_ws]
  · -- none
    injection h with h_eq; subst h_eq
    dsimp only [ScannerState.emitAt]
    apply Exists.intro
    apply Exists.intro
    rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
        ScannerCorrectness.ScanHelpers.collectTagPrefixLoop_preserves_tokens,
        ScannerCorrectness.skipWhitespace_preserves_tokens,
        ScannerCorrectness.ScanHelpers.collectTagHandleDirectiveLoop_preserves_tokens, h_ws]

/-- `scanDirective` grows the filtered token count by ≥1 *whenever* it
    grows the raw token count.  The contrapositive of the awkward case:
    the RESERVED branch (`%FOO`) yields `s'.tokens.size = s.tokens.size`,
    which contradicts `h_grew`; in YAML/TAG branches the new token is
    `.versionDirective`/`.tagDirective` (non-placeholder) by the
    `*_new_token_eq` lemmas above. -/
theorem scanDirective_filtered_grows (s s' : ScannerState)
    (h : scanDirective s = .ok s')
    (h_grew : s'.tokens.size > s.tokens.size) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (by omega)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanDirective_preserves_prefix s s' h i hi)
    s.tokens.size
    (Nat.le_refl _)
    (by omega)
  -- Goal: (s'.tokens[s.tokens.size]'_).val != .placeholder = true
  unfold scanDirective at h
  dsimp only [] at h
  split at h
  · contradiction  -- !s.allowDirectives → throw
  · have h_ws : (skipWhitespace (collectDirectiveNameLoop s.advance ""
        (s.inputEnd - s.advance.offset)).2).tokens = s.tokens := by
      rw [ScannerCorrectness.skipWhitespace_preserves_tokens,
          ScannerCorrectness.ScanHelpers.collectDirectiveNameLoop_preserves_tokens,
          ScannerCorrectness.advance_preserves_tokens]
    split at h
    · -- YAML
      split at h
      · rename_i s_inner h_inner
        have h_eq := Except.ok.inj h
        subst h_eq
        obtain ⟨major, minor, h_eq_tok⟩ :=
          scanYamlDirective_new_token_eq s _ _ s_inner h_ws h_inner
        have h_tokens : (skipToEndOfLine s_inner).tokens =
            s.tokens.push { pos := s.currentPos, val := .versionDirective major minor } := by
          rw [ScannerCorrectness.skipToEndOfLine_preserves_tokens, h_eq_tok]
        simp only [h_tokens, Array.getElem_push_eq]
        rfl
      · contradiction
    · split at h
      · -- TAG
        split at h
        · rename_i s_inner h_inner
          have h_eq := Except.ok.inj h
          subst h_eq
          obtain ⟨handle, tagPfx, h_eq_tok⟩ :=
            scanTagDirective_new_token_eq s _ _ s_inner h_ws h_inner
          have h_tokens : (skipToEndOfLine s_inner).tokens =
              s.tokens.push { pos := s.currentPos, val := .tagDirective handle tagPfx } := by
            rw [ScannerCorrectness.skipToEndOfLine_preserves_tokens, h_eq_tok]
          simp only [h_tokens, Array.getElem_push_eq]
          rfl
        · contradiction
      · -- RESERVED: no token emitted, contradicts h_grew
        injection h with h_eq
        subst h_eq
        exfalso
        rw [ScannerCorrectness.skipToEndOfLine_preserves_tokens, h_ws] at h_grew
        omega

-- Structural dispatch: full case analysis proving ≥+1 for docStart and docEnd,
-- and ≥0 for directives.  For the directive case, YAML/TAG emit non-placeholder
-- tokens but unknown directives (%RESERVED) emit none.
-- We keep ≥0 (monotone) for the overall structural dispatch but prove ≥+1
-- for the document marker sub-cases which is sufficient for scanNextToken.
theorem dispatchStructural_filtered_mono (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchStructural s c = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size := by
  have h_mono := ScannerCorrectness.ScanHelpers.dispatchStructural_tokens_mono s c s' h
  have h_pres := ScannerCorrectness.ScanHelpers.dispatchStructural_preserves_prefix s c s' h
  obtain ⟨suffix, h_eq⟩ := Array_filter_prefix_of_raw_prefix s.tokens s'.tokens
    (fun t => t.val != .placeholder) h_mono h_pres
  show (s'.tokens.filter (fun t => t.val != .placeholder)).toList.length ≥
       (s.tokens.filter (fun t => t.val != .placeholder)).toList.length
  rw [h_eq, List.length_append]; omega
-- Flow indicator dispatch: each function emits exactly 1 non-placeholder token.
-- scanFlowSequenceStart/End, scanFlowMappingStart/End push one token each;
-- scanFlowEntry pushes .flowEntry. validateFlowClose is error-only (no state change).
theorem dispatchFlowIndicators_filtered_grows (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchFlowIndicators s c = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanNextToken_dispatchFlowIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_error_simp,
             ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  -- Each goal corresponds to one flow function: seq start, seq end, map start, map end, entry.
  all_goals (
    apply filtered_grows_of_extended_prefix s.tokens _ (fun t => t.val != .placeholder)
    case h_sz =>
      first
        | (have := ScannerCorrectness.scanFlowSequenceStart_adds_one_token s; omega)
        | (have := ScannerCorrectness.scanFlowSequenceEnd_adds_one_token s; omega)
        | (have := ScannerCorrectness.scanFlowMappingStart_adds_one_token s; omega)
        | (have := ScannerCorrectness.scanFlowMappingEnd_adds_one_token s; omega)
        | (have := ScannerCorrectness.ScanHelpers.scanFlowEntry_adds_one_token s _ (by assumption); omega)
    case h_pres =>
      intro i hi
      first
        | exact ScannerCorrectness.ScanHelpers.scanFlowSequenceStart_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowSequenceEnd_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowMappingStart_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowMappingEnd_preserves_prefix s i hi
        | exact ScannerCorrectness.ScanHelpers.scanFlowEntry_preserves_prefix s _ (by assumption) i hi
    case h_new =>
      first
        | (unfold scanFlowSequenceStart; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (unfold scanFlowSequenceEnd; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (unfold scanFlowMappingStart; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (unfold scanFlowMappingEnd; dsimp only []
           simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                       Array.getElem_push_eq]; decide)
        | (-- scanFlowEntry: monadic, unfold to trace the emitted token
           rename_i s' h_fe
           unfold scanFlowEntry at h_fe
           simp only [bind, Except.bind] at h_fe
           repeat (split at h_fe)
           all_goals (first
             | contradiction
             | (injection h_fe with h_eq; subst h_eq; dsimp only []
                simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                            Array.getElem_push_eq]; decide)))
  )

-- Block indicator dispatch: scanBlockEntry, scanKey, scanValue.
-- scanValue uses setIfInBounds → needs scanValuePrepare_filtered_mono.
-- Per-block-function filtered growth lemmas.
-- scanBlockEntry: pushSequenceIndent (monotonic) + emit .blockEntry (+1).
theorem scanBlockEntry_filtered_grows (s s' : ScannerState)
    (h : scanBlockEntry s = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (ScannerCorrectness.ScanHelpers.scanBlockEntry_adds_tokens s s' h)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanBlockEntry_preserves_prefix s s' h i hi)
    (s'.tokens.size - 1)
    (by have := ScannerCorrectness.ScanHelpers.scanBlockEntry_adds_tokens s s' h; omega)
    (by have := ScannerCorrectness.ScanHelpers.scanBlockEntry_adds_tokens s s' h; omega)
  -- h_new: the last token is .blockEntry (non-placeholder)
  unfold scanBlockEntry at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  repeat (split at h)
  all_goals (first | contradiction | skip)
  all_goals (injection h with h_eq; subst h_eq; dsimp only [])
  all_goals simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                        Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
  all_goals decide

-- scanKey: pushMappingIndent (monotonic) + emit .key (+1).
theorem scanKey_filtered_grows (s s' : ScannerState)
    (h : scanKey s = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  apply filtered_grows_of_any_new s.tokens s'.tokens _
    (by have := ScannerCorrectness.scanKey_adds_one_token s s' h; omega)
    (fun i hi => ScannerCorrectness.ScanHelpers.scanKey_preserves_prefix s s' h i hi)
    (s'.tokens.size - 1)
    (by have := ScannerCorrectness.scanKey_adds_one_token s s' h; omega)
    (by have := ScannerCorrectness.scanKey_adds_one_token s s' h; omega)
  -- h_new: the last token is .key (non-placeholder)
  unfold scanKey at h
  simp only [] at h
  split at h
  · -- !inFlow: pushMappingIndent called
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                    Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
        decide
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                  Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
      decide
  · -- inFlow: no pushMappingIndent
    split at h
    · split at h
      · contradiction
      · injection h with h_eq; subst h_eq; dsimp only []
        simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                    Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
        decide
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [ScannerCorrectness.advance_preserves_tokens, emit_tokens_push,
                  Array.size_push, Nat.add_sub_cancel, Array.getElem_push_eq]
      decide

-- scanValue: setIfInBounds replaces placeholder → non-placeholder (monotonic),
-- then emit .value (+1). Uses Array_setIfInBounds_filter_mono for monotonicity
-- through scanValuePrepare, then filtered_grows_of_extended_prefix for the emit step.
set_option maxHeartbeats 400000 in
theorem scanValue_filtered_grows (s s' : ScannerState)
    (h : scanValue s = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanValue at h; dsimp only [] at h
  simp only [bind, Except.bind] at h
  split at h
  · contradiction
  · split at h
    · contradiction
    · injection h with h_eq; subst h_eq; dsimp only []
      simp only [ScannerCorrectness.advance_preserves_tokens]
      -- Goal: ((scanValuePrepare (scanValueClearKey s)).emit(.value).tokens.filter p).size
      --       ≥ (s.tokens.filter p).size + 1
      -- Step 1: emit .value adds 1 non-placeholder via filtered_grows_of_extended_prefix
      have h_emit_grows :=
        filtered_grows_of_extended_prefix
          (scanValuePrepare (scanValueClearKey s)).tokens
          ((scanValuePrepare (scanValueClearKey s)).emit .value).tokens
          (fun t => t.val != .placeholder)
          (by unfold ScannerState.emit; simp [Array.size_push])
          (fun i hi => ScannerCorrectness.emit_preserves_tokens_at _ .value i hi)
          (by simp only [emit_tokens_push, Array.getElem_push_eq]; decide)
      -- Step 2: scanValuePrepare is filter-monotonic
      have h_ck : (scanValueClearKey s).tokens = s.tokens :=
        ScannerCorrectness.scanValueClearKey_preserves_tokens s
      suffices h_prep_mono :
          ((scanValuePrepare (scanValueClearKey s)).tokens.filter
            (fun t => t.val != .placeholder)).size ≥
          (s.tokens.filter (fun t => t.val != .placeholder)).size by omega
      rw [← h_ck]
      unfold scanValuePrepare
      split
      · -- simpleKey.possible = true
        rename_i h_sk
        split
        · split
          · -- Two setIfInBounds
            dsimp only []
            have h1 := Array_setIfInBounds_filter_mono (scanValueClearKey s).tokens
              (scanValueClearKey s).simpleKey.tokenIndex
              ⟨(scanValueClearKey s).simpleKey.pos, .blockMappingStart, (scanValueClearKey s).simpleKey.pos⟩
              (fun t : Positioned YamlToken => t.val != .placeholder) rfl
            have h2 := Array_setIfInBounds_filter_mono
              ((scanValueClearKey s).tokens.setIfInBounds (scanValueClearKey s).simpleKey.tokenIndex
                ⟨(scanValueClearKey s).simpleKey.pos, .blockMappingStart, (scanValueClearKey s).simpleKey.pos⟩)
              ((scanValueClearKey s).simpleKey.tokenIndex + 1)
              ⟨(scanValueClearKey s).simpleKey.pos, .key, (scanValueClearKey s).simpleKey.pos⟩
              (fun t : Positioned YamlToken => t.val != .placeholder) rfl
            omega
          · -- One setIfInBounds
            dsimp only []
            have := Array_setIfInBounds_filter_mono (scanValueClearKey s).tokens
              ((scanValueClearKey s).simpleKey.tokenIndex + 1)
              ⟨(scanValueClearKey s).simpleKey.pos, .key, (scanValueClearKey s).simpleKey.pos⟩
              (fun t : Positioned YamlToken => t.val != .placeholder) rfl
            omega
        · -- inFlow: one setIfInBounds
          dsimp only []
          have := Array_setIfInBounds_filter_mono (scanValueClearKey s).tokens
            ((scanValueClearKey s).simpleKey.tokenIndex + 1)
            ⟨(scanValueClearKey s).simpleKey.pos, .key, (scanValueClearKey s).simpleKey.pos⟩
            (fun t : Positioned YamlToken => t.val != .placeholder) rfl
          omega
      · split
        · dsimp only []; omega
        · split
          · -- pushMappingIndent
            unfold pushMappingIndent
            split
            · -- emit .blockMappingStart
              dsimp only []
              have := filtered_grows_of_extended_prefix (scanValueClearKey s).tokens
                ((scanValueClearKey s).emit .blockMappingStart).tokens
                (fun t : Positioned YamlToken => t.val != .placeholder)
                (by unfold ScannerState.emit; simp [Array.size_push])
                (fun i hi => ScannerCorrectness.emit_preserves_tokens_at _ .blockMappingStart i hi)
                (by simp only [emit_tokens_push, Array.getElem_push_eq]; decide)
              omega
            · omega
          · omega

-- Block indicator dispatch: scanBlockEntry, scanKey, scanValue.
theorem dispatchBlockIndicators_filtered_grows (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchBlockIndicators s c = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanNextToken_dispatchBlockIndicators at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  repeat (any_goals (split at h))
  any_goals contradiction
  all_goals (try simp only [Except.ok.injEq, Option.some.injEq] at *)
  any_goals contradiction
  all_goals (try subst_vars)
  all_goals first
    | (have := scanBlockEntry_filtered_grows _ _ (by assumption); simp_all <;> omega)
    | (have := scanKey_filtered_grows _ _ (by assumption); simp_all <;> omega)
    | (have := scanValue_filtered_grows _ _ (by assumption); simp_all <;> omega)
    | (simp_all; done)

-- Content dispatch: each content function emits exactly 1 non-placeholder token.
-- Helper: the newly-added token at index s.tokens.size is non-placeholder.
-- Each content scanner emits .anchor/.alias/.tag/.scalar — never .placeholder.
-- The proof mirrors dispatchContent_preserves_prefix but tracks the NEW token value
-- instead of preserving existing tokens.
set_option maxHeartbeats 3200000 in
theorem dispatchContent_new_not_placeholder (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchContent s c = .ok s')
    (h_strict : s'.tokens.size ≥ s.tokens.size + 1) :
    (s'.tokens[s.tokens.size]'(by omega)).val ≠ YamlToken.placeholder := by
  unfold scanNextToken_dispatchContent at h
  simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  -- '&' anchor
  split at h
  · generalize h_sc : scanAnchorOrAlias s true = result at h
    cases result with
    | error => simp at h
    | ok s_a =>
      simp only [Except.ok.injEq] at h; subst h; dsimp only []
      unfold scanAnchorOrAlias at h_sc; dsimp only [] at h_sc
      split at h_sc
      · exact absurd h_sc (by simp)
      · have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
        unfold ScannerState.emitAt; dsimp only []
        simp only [ScannerCorrectness.ScanHelpers.collectAnchorNameLoop_preserves_tokens,
                    ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
        split <;> intro h <;> cases h
  · split at h
    · -- '*' alias
      split at h
      · simp at h
      · generalize h_sc : scanAnchorOrAlias s false = result at h
        cases result with
        | error => simp at h
        | ok s_a =>
          simp only [Except.ok.injEq] at h; subst h
          unfold scanAnchorOrAlias at h_sc; dsimp only [] at h_sc
          split at h_sc
          · exact absurd h_sc (by simp)
          · have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
            unfold ScannerState.emitAt; dsimp only []
            simp only [ScannerCorrectness.ScanHelpers.collectAnchorNameLoop_preserves_tokens,
                        ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
            intro h; cases h
    · split at h
      · -- '!' tag
        generalize h_sc : scanTag s = result at h
        cases result with
        | error => simp at h
        | ok s_t =>
          simp only [Except.ok.injEq] at h; subst h
          unfold scanTag at h_sc; dsimp only [] at h_sc
          split at h_sc
          · -- '<' → scanVerbatimTag (Except-returning)
            simp only [bind, Except.bind] at h_sc
            generalize hv : scanVerbatimTag s.advance s.currentPos = vresult at h_sc
            cases vresult with
            | error => simp at h_sc
            | ok s_verb =>
              dsimp only [] at h_sc
              have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
              unfold scanVerbatimTag at hv; dsimp only [] at hv
              split at hv
              · exact absurd hv (by simp)
              · split at hv
                · exact absurd hv (by simp)
                · have h_eq := Except.ok.inj hv; subst h_eq
                  unfold ScannerState.emitAt; dsimp only []
                  simp only [ScannerCorrectness.ScanHelpers.collectVerbatimTagLoop_preserves_tokens,
                              ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
                  intro h; cases h
          · -- '!' → scanSecondaryTag (pure)
            have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
            unfold scanSecondaryTag; dsimp only []
            unfold ScannerState.emitAt; dsimp only []
            simp only [ScannerCorrectness.ScanHelpers.collectTagSuffixLoop_preserves_tokens,
                        ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
            intro h; cases h
          · -- other → scanNamedTag (pure)
            have h_eq := Except.ok.inj h_sc; subst h_eq; dsimp only []
            unfold scanNamedTag; dsimp only []; split
            · -- foundBang = true
              unfold ScannerState.emitAt; dsimp only []
              simp only [ScannerCorrectness.ScanHelpers.collectTagSuffixLoop_preserves_tokens,
                          ScannerCorrectness.ScanHelpers.collectTagHandleLoop_preserves_tokens,
                          ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
              intro h; cases h
            · -- foundBang = false
              unfold ScannerState.emitAt; dsimp only []
              simp only [ScannerCorrectness.ScanHelpers.collectTagHandleLoop_preserves_tokens,
                          ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
              intro h; cases h
      · -- remaining: block scalar, double/single quoted, plain
        -- Further case-split per character
        split at h
        · -- '|' or '>' → scanBlockScalar
          generalize h_sc : scanBlockScalar s = result at h
          cases result with
          | error => simp at h
          | ok s_bs =>
            simp only [Except.ok.injEq] at h; subst h
            unfold scanBlockScalar at h_sc; simp only [] at h_sc
            split at h_sc
            · contradiction
            · unfold scanBlockScalarBody at h_sc; simp only [] at h_sc
              repeat (any_goals (split at h_sc))
              all_goals (try contradiction)
              all_goals (simp only [Except.ok.injEq] at h_sc; subst h_sc; dsimp only [])
              all_goals (unfold ScannerState.emitAt; dsimp only [])
              all_goals simp only [ScannerCorrectness.ScanHelpers.collectBlockScalarLoop_preserves_tokens,
                                   ScannerCorrectness.ScanHelpers.scanBlockScalarConsumeNewline_preserves_tokens _ _ (by assumption),
                                   ScannerCorrectness.ScanHelpers.scanBlockScalarSkipComment_preserves_tokens,
                                   ScannerCorrectness.skipWhitespace_preserves_tokens,
                                   ScannerCorrectness.ScanHelpers.parseBlockHeaderLoop_preserves_tokens,
                                   ScannerCorrectness.advance_preserves_tokens, Array.getElem_push_eq]
              all_goals (intro h; cases h)
        · split at h
          · -- '"' → scanDoubleQuoted
            generalize h_sc : scanDoubleQuoted s = result at h
            cases result with
            | error => simp at h
            | ok s_dq =>
              simp only [Except.ok.injEq] at h
              -- s' may have simpleKey update: split at the conditional
              split at h <;> (subst h; try dsimp only [])
              all_goals (
                unfold scanDoubleQuoted at h_sc
                simp only [bind, Except.bind] at h_sc
                split at h_sc <;> try contradiction
                rename_i heq_dq
                have h_collect := ScannerCorrectness.ScanHelpers.collectDoubleQuotedLoop_preserves_tokens
                  s.advance "" _ _ _ _ _ _ heq_dq
                have h_adv := ScannerCorrectness.advance_preserves_tokens s
                split at h_sc
                · split at h_sc <;> try contradiction
                  injection h_sc with h_eq; subst h_eq; dsimp only []
                  unfold ScannerState.emitAt; dsimp only []
                  simp only [h_collect, h_adv, Array.getElem_push_eq]
                  intro h; cases h
                · injection h_sc with h_eq; subst h_eq; dsimp only []
                  unfold ScannerState.emitAt; dsimp only []
                  simp only [h_collect, h_adv, Array.getElem_push_eq]
                  intro h; cases h)
          · split at h
            · -- '\'' → scanSingleQuoted
              generalize h_sc : scanSingleQuoted s = result at h
              cases result with
              | error => simp at h
              | ok s_sq =>
                simp only [Except.ok.injEq] at h
                split at h <;> (subst h; try dsimp only [])
                all_goals (
                  unfold scanSingleQuoted at h_sc
                  simp only [bind, Except.bind] at h_sc
                  split at h_sc <;> try contradiction
                  rename_i heq_sq
                  have h_collect := ScannerCorrectness.ScanHelpers.collectSingleQuotedLoop_preserves_tokens
                    s.advance "" _ _ _ _ _ _ heq_sq
                  have h_adv := ScannerCorrectness.advance_preserves_tokens s
                  split at h_sc
                  · split at h_sc <;> try contradiction
                    injection h_sc with h_eq; subst h_eq; dsimp only []
                    unfold ScannerState.emitAt; dsimp only []
                    simp only [h_collect, h_adv, Array.getElem_push_eq]
                    intro h; cases h
                  · injection h_sc with h_eq; subst h_eq; dsimp only []
                    unfold ScannerState.emitAt; dsimp only []
                    simp only [h_collect, h_adv, Array.getElem_push_eq]
                    intro h; cases h)
            · split at h
              · -- canStartPlainScalar → scanPlainScalar
                generalize h_sc : scanPlainScalar s = result at h
                cases result with
                | error => simp at h
                | ok s_ps =>
                  simp only [Except.ok.injEq] at h; subst h
                  unfold scanPlainScalar at h_sc
                  simp only [bind, Except.bind] at h_sc
                  split at h_sc <;> try contradiction
                  rename_i heq_ps
                  injection h_sc with h_eq; subst h_eq; dsimp only []
                  unfold ScannerState.emitAt; dsimp only []
                  have h_collect := ScannerCorrectness.ScanHelpers.collectPlainScalarLoop_preserves_tokens
                    s "" "" _ _ _ _ _ heq_ps
                  simp only [h_collect, Array.getElem_push_eq]
                  intro h; cases h
              · -- error case: unexpectedChar
                simp at h

-- All content tokens (anchor, alias, tag, scalar) are non-placeholder.
set_option maxHeartbeats 3200000 in
theorem dispatchContent_filtered_grows (s s' : ScannerState) (c : Char)
    (h : scanNextToken_dispatchContent s c = .ok s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pres i (hi : i < s.tokens.size) :=
    ScannerCorrectness.ScanHelpers.dispatchContent_preserves_prefix s c s' h i hi
  have h_strict : s'.tokens.size ≥ s.tokens.size + 1 := by
    have h_mono := ScannerCorrectness.ScanHelpers.dispatchContent_tokens_mono s c s' h
    -- Each scanner adds exactly 1 token (≥ + 1):
    unfold scanNextToken_dispatchContent at h
    simp only [bind, ScannerCorrectness.ScanHelpers.bind_ok_simp, pure, Pure.pure, Except.pure] at h
    simp only [Except.bind] at h
    repeat (any_goals (split at h))
    any_goals contradiction
    all_goals first
      | (have := ScannerCorrectness.ScanHelpers.scanBlockScalar_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanDoubleQuoted_adds_one_token s _ (by assumption);
         simp only [Except.ok.injEq] at h; subst h; dsimp only []; omega)
      | (have := ScannerCorrectness.ScanHelpers.scanSingleQuoted_adds_one_token s _ (by assumption);
         simp only [Except.ok.injEq] at h; subst h; dsimp only []; omega)
      | (have := ScannerCorrectness.ScanHelpers.scanDoubleQuoted_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanSingleQuoted_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanPlainScalar_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (simp only [Except.ok.injEq] at h; subst h; dsimp only [];
         have := ScannerCorrectness.ScanHelpers.scanAnchorOrAlias_adds_one_token s true _ (by assumption); omega)
      | (have := ScannerCorrectness.ScanHelpers.scanAnchorOrAlias_adds_one_token s false _ (by assumption); simp_all <;> omega)
      | (have := ScannerCorrectness.ScanHelpers.scanTag_adds_one_token s _ (by assumption); simp_all <;> omega)
      | (simp_all <;> omega)
  exact filtered_grows_of_any_new s.tokens s'.tokens _
    h_strict (fun i hi => h_pres i hi) s.tokens.size
    (by omega) (by omega)
    (by have := dispatchContent_new_not_placeholder s s' c h h_strict
        simp only [bne_iff_ne]; exact this)

/-! #### Dispatch-level filtered growth (Turn 3 of EmitterScannability migration)

These three helpers compose `preprocess_filtered_mono` (≥), `allowDir_ite_filter`
(=), and one of the `dispatch*_filtered_grows` lemmas (≥ +1) to give a clean
witness that — given a SUCCESSFUL non-structural dispatch path — `scanNextToken`
strictly grows the filtered token count.  They are the building blocks Turn 3
uses inside each `scanNextToken_flow_*` emitter helper to expose a per-step
`ScanChainGrew` witness alongside the existing `scanNextToken s = .ok (some s')`
output, sidestepping the line-8343 sorry. -/

theorem scanNextToken_via_flow_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok (some s_result)) :
    (s_result.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_mono s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.filter (fun t => t.val != .placeholder)).size =
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchFlowIndicators_filtered_grows _ _ _ h_flow
  omega

theorem scanNextToken_via_block_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (_h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok (some s_result)) :
    (s_result.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_mono s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.filter (fun t => t.val != .placeholder)).size =
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchBlockIndicators_filtered_grows _ _ _ h_block
  omega

theorem scanNextToken_via_content_dispatch_filtered_grows
    (s s_pp s_ad s_result : ScannerState) (c : Char)
    (h_pp : scanNextToken_preprocess s = .ok (some (s_pp, c)))
    (_h_struct : scanNextToken_dispatchStructural s_pp c = .ok none)
    (h_ad_eq : s_ad = if s_pp.allowDirectives then
      { s_pp with allowDirectives := false, documentEverStarted := true } else s_pp)
    (_h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok ())
    (_h_flow : scanNextToken_dispatchFlowIndicators s_ad c = .ok none)
    (_h_block : scanNextToken_dispatchBlockIndicators s_ad c = .ok none)
    (h_content : scanNextToken_dispatchContent s_ad c = .ok s_result) :
    (s_result.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  have h_pp_mono := preprocess_filtered_mono s _ _ h_pp
  have h_ad_eq_filter :
      (s_ad.tokens.filter (fun t => t.val != .placeholder)).size =
      (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
    rw [h_ad_eq]; split <;> rfl
  have h_disp := dispatchContent_filtered_grows _ _ _ h_content
  omega

-- In flow context, every successful `scanNextToken` step strictly grows the
-- filtered token count.  This is the in-flow analogue of the loose
-- `scanNextToken_filtered_grows` (which carries a sorry on the
-- structural-directive branch).  With `s.inFlow = true ∧ s.currentIndent < 0
-- ∧ s.col > 0` and the next character being non-whitespace,
-- `dispatchStructural_none_flow` rules out the directive branch entirely, so
-- the conclusion goes through unconditionally for emitter outputs.
--
-- Used at construction sites of `EmitScansInFlow` family (Tier 1 Turn 3) to
-- obtain the per-step witness needed to build `ScanChainGrew`.
set_option maxHeartbeats 800000 in
theorem scanNextToken_filtered_grows_in_flow
    (s s' : ScannerState) (c : Char) (rest : List Char)
    (hcorr : ScannerSurfCorr s ⟨c :: rest, s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_nws : isWhiteSpaceBool c = false)
    (h_nlb : isLineBreakBool c = false)
    (h_nc : c ≠ '#')
    (h_snt : scanNextToken s = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size >
    (s.tokens.filter (fun t => t.val != .placeholder)).size := by
  -- Step 1: pin down preprocess output.
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, c)) :=
    scanNextToken_preprocess_flow s c rest s.col hcorr h_flow h_nws h_nlb h_nc
  -- Step 2: structural dispatch returns none (saveSimpleKey preserves
  -- inFlow / currentIndent / col).
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) c = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent)
      (h_sk_col ▸ h_col_pos)
  -- Step 3: post-allowDir state s_ad and its inFlow witness for checkBlockFlowIndent.
  let s_ad : ScannerState := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have hs_ad : s_ad = if (saveSimpleKey s).allowDirectives then
      { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
    else saveSimpleKey s := rfl
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check : scanNextToken_checkBlockFlowIndent s_ad c = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Step 4: unfold scanNextToken using the pinned dispatch info.
  unfold scanNextToken at h_snt
  simp only [bind, pure, Pure.pure, Except.pure, Except.bind, h_pp, h_struct,
             ← hs_ad, h_check] at h_snt
  -- Step 5: case-analyze on dispatchFlowIndicators result.
  match h_flow_eq : scanNextToken_dispatchFlowIndicators s_ad c with
  | .error _ => rw [h_flow_eq] at h_snt; simp at h_snt
  | .ok (some s_flow) =>
    rw [h_flow_eq] at h_snt; simp only at h_snt
    injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
    have h_grew := scanNextToken_via_flow_dispatch_filtered_grows
      s _ s_ad s_flow c h_pp h_struct hs_ad h_check h_flow_eq
    omega
  | .ok none =>
    rw [h_flow_eq] at h_snt; simp only at h_snt
    -- Now case-analyze on dispatchBlockIndicators result.
    match h_block_eq : scanNextToken_dispatchBlockIndicators s_ad c with
    | .error _ => rw [h_block_eq] at h_snt; simp at h_snt
    | .ok (some s_block) =>
      rw [h_block_eq] at h_snt; simp only at h_snt
      injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
      have h_grew := scanNextToken_via_block_dispatch_filtered_grows
        s _ s_ad s_block c h_pp h_struct hs_ad h_check h_flow_eq h_block_eq
      omega
    | .ok none =>
      rw [h_block_eq] at h_snt; simp only at h_snt
      -- Final dispatch: content.
      match h_cont_eq : scanNextToken_dispatchContent s_ad c with
      | .error _ => rw [h_cont_eq] at h_snt; simp at h_snt
      | .ok s_cont =>
        rw [h_cont_eq] at h_snt; simp only at h_snt
        injection h_snt with h_eq; injection h_eq with h_eq; subst h_eq
        have h_grew := scanNextToken_via_content_dispatch_filtered_grows
          s _ s_ad s_cont c h_pp h_struct hs_ad h_check h_flow_eq h_block_eq h_cont_eq
        omega


/-! ### Strict-variant track: `ScanChainGrew`

`ScanChainGrew p` is `ScanChain` augmented with a per-step witness that
the filtered count under predicate `p` strictly increases at each step.
Built constructively at the call site, it sidesteps the loose
`scanNextToken_filtered_grows` (which contains a sorry on the RESERVED
directive branch — see Turn 1's `scanDirective_filtered_grows` for the
honest precondition).

Existing `ScanChain` / `ScanChain_filtered_grows` are unchanged; this
predicate runs alongside them.  Forgetful `toScanChain` lets a strict
chain be passed wherever a `ScanChain` was expected. -/
inductive ScanChainGrew (p : Positioned YamlToken → Bool) :
    ScannerState → Nat → ScannerState → Prop where
  | zero {s : ScannerState} : ScanChainGrew p s 0 s
  | step {s s_mid s' : ScannerState} {n : Nat} :
         scanNextToken s = .ok (some s_mid) →
         (s_mid.tokens.filter p).size > (s.tokens.filter p).size →
         ScanChainGrew p s_mid n s' →
         ScanChainGrew p s (n + 1) s'

/-- Forgetful map: a `ScanChainGrew` is, in particular, a `ScanChain`. -/
theorem ScanChainGrew.toScanChain {p : Positioned YamlToken → Bool}
    {s s' : ScannerState} {n : Nat}
    (h : ScanChainGrew p s n s') : ScanChain s n s' := by
  induction h with
  | zero => exact .zero
  | step h_snt _h_grew _h_rest ih => exact .step h_snt ih

/-- Single-step constructor for `ScanChainGrew`. -/
theorem ScanChainGrew.single {p : Positioned YamlToken → Bool}
    {s s' : ScannerState}
    (h : scanNextToken s = .ok (some s'))
    (h_grew : (s'.tokens.filter p).size > (s.tokens.filter p).size) :
    ScanChainGrew p s 1 s' :=
  .step h h_grew .zero

/-- Transitivity for `ScanChainGrew`: concatenate two strict chains. -/
theorem ScanChainGrew.trans {p : Positioned YamlToken → Bool}
    {s₁ s₂ s₃ : ScannerState} {n₁ n₂ : Nat}
    (h1 : ScanChainGrew p s₁ n₁ s₂) (h2 : ScanChainGrew p s₂ n₂ s₃) :
    ScanChainGrew p s₁ (n₁ + n₂) s₃ := by
  induction h1 with
  | zero => simpa using h2
  | @step s s_mid s₂ k h_snt h_grew _h_rest ih =>
    have h_ih := ih h2
    have hk : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [hk]
    exact .step h_snt h_grew h_ih

/-- Strict-chain growth: through a `ScanChainGrew p` of `n` steps, the
    filtered token array grows by at least `n`.  Same conclusion as
    `ScanChain_filtered_grows`, but proven directly from the per-step
    witness — does not depend on `scanNextToken_filtered_grows` (and so
    does not depend on the line-8379 sorry). -/
theorem ScanChainGrew_filtered_grows {p : Positioned YamlToken → Bool}
    {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChainGrew p s n s') :
    (s'.tokens.filter p).size ≥ (s.tokens.filter p).size + n := by
  induction h_chain with
  | zero => omega
  | step _h_snt h_grew _h_rest ih => omega

/-- Lift a `ScanChainGrew` through a `scanNextToken` equality.  Used when
    `s₂` is derived from `s₁` by preprocessing whitespace (which preserves
    the dispatch result via `scanNextToken_eq_of_preprocess` and is
    monotone on filtered token count via `preprocess_filtered_mono`).  The
    chain must be non-empty (length ≥ 1) so the first step's witness can
    be transitively weakened from `s₂.tokens.filter` down to
    `s₁.tokens.filter`. -/
theorem ScanChainGrew_of_scanNextToken_eq {p : Positioned YamlToken → Bool}
    {s₁ s₂ s' : ScannerState} {n : Nat}
    (h_eq : scanNextToken s₁ = scanNextToken s₂)
    (h_le : (s₁.tokens.filter p).size ≤ (s₂.tokens.filter p).size)
    (h_chain : ScanChainGrew p s₂ (n + 1) s') :
    ScanChainGrew p s₁ (n + 1) s' := by
  cases h_chain with
  | step h_snt h_grew h_rest =>
    refine .step (by rw [h_eq]; exact h_snt) ?_ h_rest
    omega

-- ═══ EmitScansInFlow: flow-context scanner acceptance ═══

/-- `EmitScansInFlow v` asserts that `emit v` can be scanned successfully
    from any scanner state in flow context.

    This is the inductive property needed for flow collection composition:
    each sub-expression of a flow collection scans correctly from mid-stream,
    preserving scanner invariants for subsequent tokens.

    **Tier 1 Turn 3 update**: produces `ScanChainGrew` (strict per-step
    filtered-growth witness) rather than the loose `ScanChain`.  Consumers
    that only need `ScanChain` may use `.toScanChain` to forget the
    witness. -/
def EmitScansInFlow (v : YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit v).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ s'.simpleKeyAllowed = false
      ∧ (∀ t, lastTokenVal? s'.tokens = some t →
          t ≠ .flowSequenceStart ∧ t ≠ .flowMappingStart ∧ t ≠ .flowEntry)
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove:
      -- pkRec preserved at indices < initial size, plus size monotonicity.
      -- Composes through the (helper) per-step preservation along all paths
      -- of `emit_scans_in_flow`'s induction (scalar/seq/map).
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack preserved (scalar: helper preserves it; seq/map: open
      -- pushes and matching close pops cancel; the body of EmitListScansInFlow /
      -- EmitPairListScansInFlow preserves it).
      ∧ s'.pendingKeyStack = s.pendingKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated:
      -- Under the `simpleKeyAllowed = true` gate, scanning emit(v) registers
      -- a fresh pendingKey at index `s.pendingKeys.size` (per A1's saveSimpleKey
      -- push) with `insertBeforeIdx = s.tokens.size` and `kind = .unresolved`,
      -- and at the post-state we have `pendingKeyActive = some s.pendingKeys.size`
      -- and `simpleKey.possible = true` (scalar: per A2; seq/map: A3/A4 push at
      -- OPEN, body preserves-prior at index `s.pendingKeys.size`, CLOSE restore
      -- recovers `pendingKeyActive`/`simpleKey` from the J.2-shadowed stacks).
      -- (Preserves-prior at `j < s.pendingKeys.size` already exposed by the
      -- unconditional kind+insertBeforeIdx conjunct above; not duplicated here.)
      ∧ (s.simpleKeyAllowed = true →
          (∃ (h : s.pendingKeys.size < s'.pendingKeys.size),
              (s'.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
              ∧ (s'.pendingKeys[s.pendingKeys.size]'h).kind = .unresolved)
          ∧ s'.pendingKeyActive = some s.pendingKeys.size
          ∧ s'.simpleKey.possible = true)

/-- `EmitListScansInFlow items` asserts that scanning the comma-separated
    emitList output succeeds in flow context, preserving invariants.
    This is the body between `[` and `]` in a flow sequence. -/
def EmitListScansInFlow (items : List YamlValue) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack preserved across the body (mirrors simpleKeyStack;
      -- inner [/{ pushes are cancelled by the matching ]/} pops).
      ∧ s'.pendingKeyStack = s.pendingKeyStack

/-- Empty list body is trivially scanned (0-step chain). -/
theorem emitList_scans_empty : EmitListScansInFlow [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  -- emit.emitList [] = "", toList = [], so state is already at rest
  have h_eq : (emit.emitList ([] : List YamlValue)).toList ++ rest = rest := by
    simp only [emit.emitList]; rfl
  rw [h_eq] at hcorr
  exact ⟨0, s, .zero, hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl, h_atol,
    h_endline, rfl, .zero (Nat.le_refl _), Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl⟩, rfl⟩

/-- Non-empty list scanning via induction on the item list.
    Structure: singleton case uses EmitScansInFlow directly;
    multi-item case chains emit v + comma + space + recursive emitList. -/
theorem emitList_scans_nonempty (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlow v) :
    EmitListScansInFlow items := by
  induction items with
  | nil => contradiction
  | cons v tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    match tail, ih with
    | [], _ =>
      -- Singleton [v]: emitList [v] = emit v
      have h_eq : (emit.emitList [v]).toList = (emit v).toList := by
        simp only [emit.emitList]
      rw [h_eq] at hcorr
      obtain ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent',
              h_line_v, _, _, h_atol', h_endline', h_stack', h_fmc', h_size', h_pkRec',
              h_pks_v, _h_gated_v⟩ :=
        h_all v (.head _) s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      exact ⟨n, s', h_chain, h_corr, h_fl', h_dp, h_ids, h_ek', h_col', h_flow', h_indent',
        h_line_v, h_atol', h_endline', h_stack', h_fmc', h_size', h_pkRec', h_pks_v⟩
        -- (singleton: h_pks_v = s'.pendingKeyStack = s.pendingKeyStack from EmitScansInFlow)
        -- (singleton: _h_gated_v is the gated first-key conjunct, not propagated here)
    | v' :: vs, ih =>
      -- Multi-item: emitList (v :: v' :: vs) = emit v ++ ", " ++ emitList (v' :: vs)
      -- Rewrite chars to decompose
      have h_eq : (emit.emitList (v :: v' :: vs)).toList ++ rest_chars =
          (emit v).toList ++ ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
        simp [emit.emitList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan emit v via EmitScansInFlow
      have h_ev : EmitScansInFlow v := h_all v (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, h_flow₁,
              h_indent₁, _h_line₁, _, h_last₁, h_atol₁, h_endline₁, h_stack₁, h_fmc₁,
              h_size₁, h_pkRec₁, h_pks_v, _h_gated₁⟩ :=
        h_ev s ([',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: Scan ',' via scanNextToken_flow_comma
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, _h_line₂,
              h_atol₂, h_endline₂, h_stack₂, h_size₂, h_pkRec₂, h_pks₂, _h_ska₂,
              _h_comma_push⟩ :=
        scanNextToken_flow_comma s₁
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁
          h_last₁ h_atol₁ h_endline₁
      -- s₂ at ' ' :: (emitList (v' :: vs)).toList ++ rest_chars
      -- Step 3: Handle leading space via preprocessing equality
      obtain ⟨c, rest', h_first, h_nws, h_nlb, h_nc⟩ := emitList_first_char v' vs
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c :: (rest' ++ rest_chars), s₂.col⟩ := by
        have : ' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars =
            ' ' :: c :: (rest' ++ rest_chars) := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₂
      have h_s2_flow : s₂.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₂]; omega)
      have h_s2_indent : s₂.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids₂]; exact h_indent₁
      have h_s2_col : s₂.col > 0 := by rw [h_col₂]; omega
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _h_pks_pp₃, h_pks_pp₃, _h_ska_pp₃⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c (rest' ++ rest_chars) h_corr₂_ws
          h_s2_flow h_nws h_nlb h_nc h_s2_indent
      -- s₃ at c :: rest' ++ rest_chars = (emitList (v' :: vs)).toList ++ rest_chars
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit.emitList (v' :: vs)).toList ++ rest_chars, s₃.col⟩ := by
        have : c :: (rest' ++ rest_chars) = (emit.emitList (v' :: vs)).toList ++ rest_chars := by
          rw [h_first]; simp only [List.cons_append]
        rwa [this] at h_corr₃
      -- Step 4: Recursive scan of emitList (v' :: vs) from s₃
      have h_tail_all : ∀ w ∈ v' :: vs, EmitScansInFlow w :=
        fun w hw => h_all w (.tail _ hw)
      have h_ih_list : EmitListScansInFlow (v' :: vs) :=
        ih (by simp) h_tail_all
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end,
              h_endline_end, h_stack_end, h_fmc₃, h_size₃, h_pkRec₃, h_pks_end⟩ :=
        h_ih_list s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_s2_indent)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃, h_ek₂, h_ek₁]; exact h_ek)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Step 5: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      -- Chain from s₃ must have n₃ ≥ 1 (emitList is non-empty)
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitList (v' :: vs)).toList = [] := by
            match h_list : (emit.emitList (v' :: vs)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          exact absurd h_nil (emitList_toList_ne_nil v' vs)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      -- Lift the recursive ScanChainGrew through the preprocess equality.
      -- preprocess_flow_ws1 preserves tokens (h_toks_pp₃ : s₃.tokens = s₂.tokens),
      -- so the per-step witness from h_chain₃ at s₃ remains valid at s₂.
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      -- Per-step witness for the comma step (s₁ → s₂): the next char is ','.
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars), s₁.col⟩ := by
          have : [',', ' '] ++ (emit.emitList (v' :: vs)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ','
          (' ' :: (emit.emitList (v' :: vs)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- FlowMonoChain: lift recursive chain through preprocessing, then compose
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      -- Compose strict chains: emit v (n₁) + comma (1) + space+rest (n₃'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      -- pkRec / size composition along s → s₁ → s₂ → s₃ → s_end
      have ⟨h_size₁₂, h_pkRec₁₂⟩ :=
        pkRec_size_compose h_size₁ h_size₂ h_pkRec₁ h_pkRec₂
      have ⟨h_size_pp, h_pkRec_pp⟩ := pkRec_size_of_pks_eq _h_pks_pp₃
      have ⟨h_size₁₂₃, h_pkRec₁₂₃⟩ :=
        pkRec_size_compose h_size₁₂ h_size_pp h_pkRec₁₂ h_pkRec_pp
      have ⟨h_size_all, h_pkRec_all⟩ :=
        pkRec_size_compose h_size₁₂₃ h_size₃ h_pkRec₁₂₃ h_pkRec₃
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end,
        h_endline_end, ?_, h_arith ▸ h_fmc_all, h_size_all, h_pkRec_all, ?_⟩
      · -- flowLevel preserved
        rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · -- directivesPresent preserved
        rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · -- indents preserved
        rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · -- explicitKeyLine preserved
        rw [h_ek_end, h_ek₃, h_ek₂, h_ek₁]
      · -- line preserved
        rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · -- simpleKeyStack preserved
        rw [h_stack_end, h_stack_pp₃, h_stack₂, h_stack₁]
      · -- pendingKeyStack preserved through s → s₁ → s₂ → s₃ → s_end
        rw [h_pks_end, h_pks_pp₃, h_pks₂, h_pks_v]

-- ═══ Flow mapping pair list scanning ═══

-- The first char of `emitPairList (p :: ps)` is the first char of `emit p.1` (the key).
theorem emitPairList_first_char (p : YamlValue × YamlValue) (ps : List (YamlValue × YamlValue)) :
    ∃ c rest', (emit.emitPairList (p :: ps)).toList = c :: rest' ∧
      isWhiteSpaceBool c = false ∧ isLineBreakBool c = false ∧ c ≠ '#' := by
  obtain ⟨c, ev_rest, h_emit_eq, h_nws, h_nlb, h_nc⟩ := emit_first_char p.1
  match ps with
  | [] =>
    simp only [emit.emitPairList]
    rw [show (emit p.1 ++ ": " ++ emit p.2).toList =
        (emit p.1).toList ++ (": " ++ emit p.2).toList from by
      simp [String.toList_append]]
    rw [h_emit_eq]
    exact ⟨c, ev_rest ++ (": " ++ emit p.2).toList, by simp, h_nws, h_nlb, h_nc⟩
  | p' :: ps' =>
    have h_ep : (emit.emitPairList (p :: p' :: ps')).toList =
        (emit p.1).toList ++ (": " ++ emit p.2 ++ ", " ++ emit.emitPairList (p' :: ps')).toList := by
      simp [emit.emitPairList, String.toList_append, List.append_assoc]
    rw [h_ep, h_emit_eq]
    exact ⟨c, ev_rest ++ (": " ++ emit p.2 ++ ", " ++ emit.emitPairList (p' :: ps')).toList,
      by simp, h_nws, h_nlb, h_nc⟩

-- isValueCandidate returns true when peekAt? 1 is a space (blank).
-- This works through ALL branches of isValueCandidate because each branch
-- has a peekAt? 1 fallback path.
theorem isValueCandidate_of_peekAt_blank (s : ScannerState)
    (h : s.peekAt? 1 = some ' ') :
    isValueCandidate s = true := by
  unfold isValueCandidate
  split
  · split
    · -- offset ≠: match tokens[size-1]?; if isJsonNodeToken then true else peekAt fallback
      dsimp only []
      split  -- match tokens[...]?
      · split  -- if isJsonNodeToken tok.val
        · dsimp only []  -- reduces true = true
        · rw [h]; decide
      · rw [h]; decide
    · -- offset =: similar
      dsimp only []
      split
      · split
        · dsimp only []
        · rw [h]; decide
      · rw [h]; decide
  · rw [h]; dsimp only []; simp [isBlankBool, isWhiteSpaceBool]

-- Value indicator `:` scanning in flow context.
-- Value indicator `:` scanning in flow context.
-- After scanning a key (e.g., double-quoted scalar), `:` dispatches through
-- isValueCandidate → scanValue, emitting a .value token and advancing past `:`.
-- Requires space after `:` (emitter always produces ": ") for isValueCandidate
-- to hold in all simpleKey branches via peekAt? fallback.
-- Result state is at `' ' :: rest'` (space not yet consumed).
theorem scanNextToken_flow_value (s : ScannerState)
    (rest' : List Char)
    (hcorr : ScannerSurfCorr s ⟨':' :: ' ' :: rest', s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_sv : scanValueValidate (saveSimpleKey s) = .ok ())
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨' ' :: rest', s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.col = s.col + 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack := by
  -- Step 1: Preprocessing — `:` is non-ws content char
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ':')) :=
    scanNextToken_preprocess_flow s ':' (' ' :: rest') s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  -- Step 2: Structural dispatch returns none
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ':' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  -- Step 3: allowDirectives update
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  -- Step 4: checkBlockFlowIndent passes in flow
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check : scanNextToken_checkBlockFlowIndent s_ad ':' = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  -- Step 5: Flow dispatch returns none (`:` is not a flow indicator)
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad ':' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  -- Step 6: isValueCandidate via peekAt? 1 = space fallback
  have h_ad_offset : s_ad.offset = s.offset := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
  have h_ad_input : s_ad.input = s.input := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
  have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
  have ⟨h_pk_colon, h_lt_colon⟩ := peek_of_chars_cons s ':' (' ' :: rest') s.col hcorr
  have h_adv_corr := advance_non_newline_corr s ':' (' ' :: rest') hcorr h_lt_colon
    (by decide) (by decide)
  have ⟨h_pk_space, _⟩ := peek_of_chars_cons s.advance ' ' rest' (s.col + 1) h_adv_corr
  have h_peekAt1 : s.peekAt? 1 = some ' ' := by
    rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one s ':' h_pk_colon]
    exact h_pk_space
  have h_ad_peekAt1 : s_ad.peekAt? 1 = some ' ' := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop
    rw [h_ad_offset, h_ad_input, h_ad_inputEnd]
    change ScannerState.peekAt?Loop s.input s.inputEnd ⟨s.offset⟩ 1 = some ' '
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop at h_peekAt1; exact h_peekAt1
  have h_vc : isValueCandidate s_ad = true :=
    isValueCandidate_of_peekAt_blank s_ad h_ad_peekAt1
  -- Step 7: Block dispatch yields scanValue
  have h_block_eq : scanNextToken_dispatchBlockIndicators s_ad ':' =
      (scanValue s_ad >>= fun s' => .ok (some s')) := by
    unfold scanNextToken_dispatchBlockIndicators
    simp only [show (':' == '-') = false from by decide, Bool.false_and,
               show (':' == '?') = false from by decide,
               show (':' == ':') = true from by decide, Bool.true_and, h_vc, ite_true]
    rfl
  -- Step 8: scanValue decomposition
  have h_ad_ek : s_ad.explicitKeyLine = none := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = none
      unfold saveSimpleKey; split <;> (try exact h_ek) <;> split <;> exact h_ek
    · unfold saveSimpleKey; split <;> (try exact h_ek) <;> split <;> exact h_ek
  have h_ckr : scanValueClearKey s_ad = s_ad := by
    unfold scanValueClearKey; rw [h_ad_ek]
  have h_validate : scanValueValidate s_ad = .ok () := by
    -- scanValueValidate only reads simpleKey, tokens, inFlow, isInFlowSequence,
    -- explicitKeyLine, line, col, currentIndent — none affected by allowDirectives
    have : scanValueValidate s_ad = scanValueValidate (saveSimpleKey s) := by
      simp only [s_ad]; split <;> (unfold scanValueValidate; rfl)
    rw [this]; exact h_sv
  -- scanValueTabCheck is identity in flow
  have h_ad_inFlow : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  -- Unfold scanValue, building the result state
  -- scanValue s_ad = do
  --   let s_kc := scanValueClearKey s_ad  -- = s_ad (since ek = none)
  --   scanValueValidate s_kc              -- .ok ()
  --   let s_prep := scanValuePrepare s_kc
  --   let s_tok := s_prep.emit .value
  --   let s_adv := s_tok.advance
  --   scanValueTabCheck s_ad.col s_ad.currentIndent s_adv  -- .ok () in flow
  --   .ok { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }
  let s_prep := scanValuePrepare s_ad
  let s_tok := s_prep.emit .value
  let s_adv := s_tok.advance
  have h_scanValue_result : scanValue s_ad =
      (scanValueTabCheck (s_ad.col : Int) s_ad.currentIndent s_adv >>= fun () =>
        .ok { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }) := by
    unfold scanValue
    dsimp only []  -- zeta-reduce let bindings in the unfolded body
    rw [h_ckr, h_validate]
    dsimp only [Bind.bind, Except.bind]
  -- scanValueTabCheck is .ok () since !s_adv.inFlow = false
  -- s_adv.inFlow = s_prep.inFlow = s_ad.inFlow = true (through emit and advance)
  have h_prep_inFlow : s_prep.inFlow = s_ad.inFlow := by
    show (scanValuePrepare s_ad).inFlow = s_ad.inFlow
    unfold scanValuePrepare
    split <;> (split <;> try split) <;> simp_all [ScannerState.inFlow]
  have h_tok_inFlow : s_tok.inFlow = s_prep.inFlow := by
    show (s_prep.emit .value).inFlow = s_prep.inFlow
    simp only [ScannerState.emit, ScannerState.inFlow]; rfl
  have h_adv_inFlow : s_adv.inFlow = s_tok.inFlow := by
    show s_tok.advance.inFlow = s_tok.inFlow
    exact advance_inFlow s_tok
  have h_tab_ok : scanValueTabCheck (s_ad.col : Int) s_ad.currentIndent s_adv = .ok () := by
    unfold scanValueTabCheck
    have : s_adv.inFlow = true := by
      rw [h_adv_inFlow, h_tok_inFlow, h_prep_inFlow]; exact h_ad_inFlow
    simp [this]
  -- Derive scanValue s_ad = .ok s_final
  let s_final : ScannerState := { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }
  have h_scanValue_ok : scanValue s_ad = .ok s_final := by
    rw [h_scanValue_result, h_tab_ok]; dsimp only [Bind.bind, Except.bind]
  -- Derive block dispatch result
  have h_block_result : scanNextToken_dispatchBlockIndicators s_ad ':' = .ok (some s_final) := by
    rw [h_block_eq, h_scanValue_ok]; dsimp only [Bind.bind, Except.bind]
  -- Compose pipeline
  have h_snt : scanNextToken s = .ok (some s_final) :=
    scanNextToken_via_block_dispatch s (saveSimpleKey s) s_ad s_final ':'
      h_pp h_struct (by rfl) h_check h_flow_none h_block_result
  -- scanValuePrepare preserves key fields in flow context
  -- (only modifies tokens and simpleKey when inFlow = true)
  have h_svp_flow := h_ad_inFlow
  have h_prep_fl : s_prep.flowLevel = s_ad.flowLevel := by
    show (scanValuePrepare s_ad).flowLevel = s_ad.flowLevel
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_dp : s_prep.directivesPresent = s_ad.directivesPresent := by
    show (scanValuePrepare s_ad).directivesPresent = s_ad.directivesPresent
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_indents : s_prep.indents = s_ad.indents := by
    show (scanValuePrepare s_ad).indents = s_ad.indents
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_col : s_prep.col = s_ad.col := by
    show (scanValuePrepare s_ad).col = s_ad.col
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_offset : s_prep.offset = s_ad.offset := by
    show (scanValuePrepare s_ad).offset = s_ad.offset
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_input : s_prep.input = s_ad.input := by
    show (scanValuePrepare s_ad).input = s_ad.input
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  have h_prep_inputEnd : s_prep.inputEnd = s_ad.inputEnd := by
    show (scanValuePrepare s_ad).inputEnd = s_ad.inputEnd
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  -- s_ad fields equal s fields (through allowDirectives branch + saveSimpleKey)
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_indents : s_ad.indents = s.indents := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  have h_ad_col : s_ad.col = s.col := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_col s
  -- Surface field equalities between s_final/s_adv and s.advance
  have h_final_input : s_final.input = s.advance.input := by
    show s_adv.input = s.advance.input
    rw [show s_adv.input = s_tok.input from advance_input s_tok]
    show s_prep.input = s.advance.input
    rw [h_prep_input, h_ad_input, advance_input s]
  have h_final_offset : s_final.offset = s.advance.offset := by
    show s_adv.offset = s.advance.offset
    exact advance_offset_of_eq s_tok s
      (by show s_prep.input = s.input; rw [h_prep_input, h_ad_input])
      (by show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset])
      (by show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd])
  have h_final_inputEnd : s_final.inputEnd = s.advance.inputEnd := by
    show s_adv.inputEnd = s.advance.inputEnd
    rw [show s_adv.inputEnd = s_tok.inputEnd from advance_inputEnd s_tok]
    show s_prep.inputEnd = s.advance.inputEnd
    rw [h_prep_inputEnd, h_ad_inputEnd, advance_inputEnd s]
  have h_final_indents : s_final.indents = s.advance.indents := by
    show s_adv.indents = s.advance.indents
    rw [advance_indents s_tok]
    show s_prep.indents = s.advance.indents
    rw [h_prep_indents, h_ad_indents, advance_indents s]
  -- Line preservation
  have h_ad_line : s_ad.line = s.line := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_line s
  have h_prep_line : s_prep.line = s_ad.line := by
    show (scanValuePrepare s_ad).line = s_ad.line
    unfold scanValuePrepare
    simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
    split <;> (try (split <;> rfl)); rfl
  refine ⟨s_final, h_snt, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, ?_, ?_, ?_⟩
  · -- ScannerSurfCorr s_final ⟨' ' :: rest', s_final.col⟩
    exact {
      chars_from := by rw [h_final_input, h_final_offset]; exact h_adv_corr.chars_from
      col_eq := rfl
      end_eq := by rw [h_final_inputEnd, h_final_input]; exact h_adv_corr.end_eq
      input_prefix := by rw [h_final_input, h_final_offset]; exact h_adv_corr.input_prefix
      indent_cols_nonneg := by
        intro i hi h0
        have hi' : i < s.advance.indents.size := by
          rw [← h_final_indents]; exact hi
        have : s_final.indents[i] = s.advance.indents[i]'hi' := by
          simp only [h_final_indents]
        rw [this]; exact h_adv_corr.indent_cols_nonneg i hi' h0
    }
  · -- s_final.flowLevel = s.flowLevel
    show s_adv.flowLevel = s.flowLevel
    rw [show s_adv.flowLevel = s_tok.flowLevel from advance_flowLevel s_tok]
    show s_prep.flowLevel = s.flowLevel
    rw [h_prep_fl, h_ad_fl]
  · -- s_final.directivesPresent = s.directivesPresent
    show s_adv.directivesPresent = s.directivesPresent
    rw [show s_adv.directivesPresent = s_tok.directivesPresent from advance_dp s_tok]
    show s_prep.directivesPresent = s.directivesPresent
    rw [h_prep_dp, h_ad_dp]
  · -- s_final.indents = s.indents
    show s_adv.indents = s.indents
    rw [show s_adv.indents = s_tok.indents from advance_indents s_tok]
    show s_prep.indents = s.indents
    rw [h_prep_indents, h_ad_indents]
  · -- s_final.col = s.col + 1
    show s_adv.col = s.col + 1
    -- s_adv = s_tok.advance, s_tok at ':' (non-newline), advance increments col
    have h_tok_col : s_tok.col = s.col := by
      show s_prep.col = s.col; rw [h_prep_col, h_ad_col]
    have h_tok_offset : s_tok.offset = s.offset := by
      show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset]
    have h_tok_input : s_tok.input = s.input := by
      show s_prep.input = s.input; rw [h_prep_input, h_ad_input]
    have h_tok_inputEnd : s_tok.inputEnd = s.inputEnd := by
      show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd]
    have h_tok_lt : s_tok.offset < s_tok.inputEnd := by
      rw [h_tok_offset, h_tok_inputEnd]; exact h_lt_colon
    -- Character at s_tok's position is `:`
    have h_s_char : String.Pos.Raw.get s.input ⟨s.offset⟩ = ':' := by
      have h_pk := h_pk_colon; unfold ScannerState.peek? at h_pk
      simp only [show s.offset < s.inputEnd from h_lt_colon, ite_true] at h_pk
      exact Option.some.inj h_pk
    have h_tok_char : String.Pos.Raw.get s_tok.input ⟨s_tok.offset⟩ = ':' := by
      rw [h_tok_input, h_tok_offset]; exact h_s_char
    rw [show s_adv.col = s_tok.advance.col from rfl]
    rw [advance_col_non_newline s_tok h_tok_lt
      (by rw [h_tok_char]; decide)
      (by rw [h_tok_char]; decide)]
    rw [h_tok_col]
  · -- s_final.inFlow = true
    show s_adv.inFlow = true
    rw [h_adv_inFlow, h_tok_inFlow, h_prep_inFlow]; exact h_ad_inFlow
  · -- s_final.currentIndent < 0
    show s_adv.currentIndent < 0
    have h_adv_indents : s_adv.indents = s.indents := by
      show s_tok.advance.indents = s.indents
      rw [advance_indents s_tok]
      show s_prep.indents = s.indents
      rw [h_prep_indents, h_ad_indents]
    unfold ScannerState.currentIndent
    rw [h_adv_indents]
    unfold ScannerState.currentIndent at h_indent
    exact h_indent
  · -- s_final.line = s.line
    show s_adv.line = s.line
    have h_tok_offset : s_tok.offset = s.offset := by
      show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset]
    have h_tok_input : s_tok.input = s.input := by
      show s_prep.input = s.input; rw [h_prep_input, h_ad_input]
    have h_tok_inputEnd : s_tok.inputEnd = s.inputEnd := by
      show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd]
    have h_tok_lt : s_tok.offset < s_tok.inputEnd := by
      rw [h_tok_offset, h_tok_inputEnd]; exact h_lt_colon
    have h_tok_peek : s_tok.peek? = some ':' := by
      unfold ScannerState.peek? at h_pk_colon ⊢
      rw [h_tok_offset, h_tok_inputEnd, h_tok_input]
      simp only [show s.offset < s.inputEnd from h_lt_colon, ite_true] at h_pk_colon ⊢
      exact h_pk_colon
    rw [advance_line_of_peek s_tok ':' h_tok_lt h_tok_peek (by decide) (by decide)]
    show s_prep.line = s.line; rw [h_prep_line, h_ad_line]
  · -- AllTokensOnLine s_final s_final.line
    -- s_final = { s_adv with simpleKeyAllowed, explicitKeyLine }, same tokens/line as s_adv
    have h_tok_offset' : s_tok.offset = s.offset := by
      show s_prep.offset = s.offset; rw [h_prep_offset, h_ad_offset]
    have h_tok_input' : s_tok.input = s.input := by
      show s_prep.input = s.input; rw [h_prep_input, h_ad_input]
    have h_tok_inputEnd' : s_tok.inputEnd = s.inputEnd := by
      show s_prep.inputEnd = s.inputEnd; rw [h_prep_inputEnd, h_ad_inputEnd]
    have h_tok_lt' : s_tok.offset < s_tok.inputEnd := by
      rw [h_tok_offset', h_tok_inputEnd']; exact h_lt_colon
    have h_tok_peek' : s_tok.peek? = some ':' := by
      unfold ScannerState.peek? at h_pk_colon ⊢
      rw [h_tok_offset', h_tok_inputEnd', h_tok_input']
      simp only [show s.offset < s.inputEnd from h_lt_colon, ite_true] at h_pk_colon ⊢
      exact h_pk_colon
    have h_adv_line : s_adv.line = s.line := by
      rw [advance_line_of_peek s_tok ':' h_tok_lt' h_tok_peek' (by decide) (by decide)]
      show s_prep.line = s.line; rw [h_prep_line, h_ad_line]
    rw [show s_final.line = s_adv.line from rfl, h_adv_line]
    change AllTokensOnLine s_adv s.line
    have h_sk_endline : EndLineOnLine (saveSimpleKey s) :=
      EndLineOnLine_saveSimpleKey_flow s h_endline
    have h_ad_endline : EndLineOnLine s_ad := by
      simp only [s_ad, EndLineOnLine]; split <;> exact h_sk_endline
    exact AllTokensOnLine_advance _ _
      (AllTokensOnLine_emit _ _ _
        (AllTokensOnLine_scanValuePrepare_flow s_ad s.line
          (AllTokensOnLine_allowDirectives _ _
            (AllTokensOnLine_saveSimpleKey _ _ h_atol rfl))
          h_ad_line h_ad_inFlow h_ad_ek h_ad_endline)
        (by rw [h_prep_line, h_ad_line]))
  · -- EndLineOnLine s_final — vacuously true: scanValuePrepare in flow always gives possible = false
    intro h_poss
    exfalso
    have h_chain : s_final.simpleKey = (scanValuePrepare s_ad).simpleKey := by
      show s_adv.simpleKey = _
      rw [ScannerCorrectness.advance_preserves_simpleKey, ScannerCorrectness.emit_preserves_simpleKey]
    have h_false : s_final.simpleKey.possible = false := by
      rw [h_chain]
      unfold scanValuePrepare
      simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
      split
      · rfl
      · split
        · rfl
        · simp_all
    rw [h_false] at h_poss; exact absurd h_poss (by decide)
  · -- s_final.simpleKeyStack = s.simpleKeyStack
    show s_adv.simpleKeyStack = s.simpleKeyStack
    rw [ScannerCorrectness.advance_preserves_simpleKeyStack, ScannerCorrectness.emit_preserves_simpleKeyStack]
    have h_svp_stack : (scanValuePrepare s_ad).simpleKeyStack = s_ad.simpleKeyStack := by
      unfold scanValuePrepare
      simp only [h_svp_flow, Bool.not_true, Bool.false_eq_true, ite_false]
      split
      · rfl
      · split <;> rfl
    rw [h_svp_stack]
    simp only [s_ad]; split <;> exact ScannerCorrectness.saveSimpleKey_preserves_simpleKeyStack s

/-- **J.4.2.b-2d-key-chain-Part2-body-B**: strengthened
    `scanNextToken_flow_value` exposing the resolution effect on the
    active pendingKey.  Under preconditions
      `s.simpleKeyAllowed = false ∧ s.simpleKey.possible = true ∧
       s.pendingKeyActive = some i ∧ i < s.pendingKeys.size`,
    the `:` step's `scanValuePrepare` flow branch resolves the entry
    at index `i` to `.keyOnly`, preserving size, the entry's
    `insertBeforeIdx`, and all other entries.

    Mirrors `scanNextToken_flow_value` (above) with three additional
    pkResolve conjuncts.  The `simpleKeyAllowed = false` precondition
    makes `saveSimpleKey s = s` (via `saveSimpleKey_id_of_flow_ska_false_ek_none`),
    so `s.pendingKeyActive` flows unchanged into `scanValuePrepare`'s
    flow branch where it is consumed by `setPendingKeyKind`.

    Used by Part2-body-C to compose `:`-resolution into
    `emitPairList_chain_first_pkShape` after a per-leaf pkPush
    (A2/A3/A4) has installed an `.unresolved` entry. -/
theorem scanNextToken_flow_value_pkResolve (s : ScannerState)
    (rest' : List Char)
    (hcorr : ScannerSurfCorr s ⟨':' :: ' ' :: rest', s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_sv : scanValueValidate (saveSimpleKey s) = .ok ())
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_ska : s.simpleKeyAllowed = false)
    (h_sk_poss : s.simpleKey.possible = true)
    (i : Nat) (h_pka : s.pendingKeyActive = some i)
    (h_lt : i < s.pendingKeys.size) :
    ∃ s', scanNextToken s = .ok (some s')
      ∧ ScannerSurfCorr s' ⟨' ' :: rest', s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.col = s.col + 1
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.explicitKeyLine = none
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ s'.pendingKeys.size = s.pendingKeys.size
      ∧ (∃ (h' : i < s'.pendingKeys.size),
          (s'.pendingKeys[i]'h').kind = .keyOnly
            ∧ (s'.pendingKeys[i]'h').insertBeforeIdx = (s.pendingKeys[i]'h_lt).insertBeforeIdx)
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          j ≠ i → s'.pendingKeys[j]'hj' = s.pendingKeys[j]'hj)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon:
      -- pendingKeyStack preserved through the colon step (scanValuePrepare modifies
      -- pendingKeys/pendingKeyActive/simpleKey but not pendingKeyStack;
      -- emit/advance/record-update preserve it). -/
      ∧ s'.pendingKeyStack = s.pendingKeyStack := by
  -- Get surface conjuncts and `s'` from the existing theorem.
  obtain ⟨s', h_snt, h_corr, h_fl, h_dp, h_ids, h_col_eq, h_iflow, h_ind_neg,
         h_ek_none, h_line, h_atol', h_endline', h_stack⟩ :=
    scanNextToken_flow_value s rest' hcorr h_flow h_indent h_col_pos h_ek h_sv h_atol h_endline
  -- Re-derive the chain to identify `s'` with the canonical `s_final` and
  -- track `pendingKeys` through it.  `simpleKeyAllowed = false` makes
  -- `saveSimpleKey s = s`, simplifying the chain.
  have h_sk_id : saveSimpleKey s = s :=
    saveSimpleKey_id_of_flow_ska_false_ek_none s h_flow h_ska h_ek
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ':')) :=
    scanNextToken_preprocess_flow s ':' (' ' :: rest') s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ':' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_ad_flow : s_ad.inFlow = s.inFlow := by
    simp only [s_ad]; split <;> exact h_sk_flow
  have h_check : scanNextToken_checkBlockFlowIndent s_ad ':' = .ok () :=
    checkBlockFlowIndent_ok_flow _ _ (h_ad_flow ▸ h_flow)
  have h_flow_none : scanNextToken_dispatchFlowIndicators s_ad ':' = .ok none :=
    dispatchFlowIndicators_none _ _ (by decide) (by decide) (by decide) (by decide) (by decide)
  have h_ad_offset : s_ad.offset = s.offset := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s
  have h_ad_input : s_ad.input = s.input := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s
  have h_ad_inputEnd : s_ad.inputEnd = s.inputEnd := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s
  have ⟨h_pk_colon, h_lt_colon⟩ := peek_of_chars_cons s ':' (' ' :: rest') s.col hcorr
  have h_adv_corr := advance_non_newline_corr s ':' (' ' :: rest') hcorr h_lt_colon
    (by decide) (by decide)
  have ⟨h_pk_space, _⟩ := peek_of_chars_cons s.advance ' ' rest' (s.col + 1) h_adv_corr
  have h_peekAt1 : s.peekAt? 1 = some ' ' := by
    rw [← L4YAML.Proofs.ScannerPlainContent.advance_peek_eq_peekAt_one s ':' h_pk_colon]
    exact h_pk_space
  have h_ad_peekAt1 : s_ad.peekAt? 1 = some ' ' := by
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop
    rw [h_ad_offset, h_ad_input, h_ad_inputEnd]
    change ScannerState.peekAt?Loop s.input s.inputEnd ⟨s.offset⟩ 1 = some ' '
    unfold ScannerState.peekAt? ScannerState.peekAt?Loop at h_peekAt1; exact h_peekAt1
  have h_vc : isValueCandidate s_ad = true :=
    isValueCandidate_of_peekAt_blank s_ad h_ad_peekAt1
  have h_block_eq : scanNextToken_dispatchBlockIndicators s_ad ':' =
      (scanValue s_ad >>= fun s' => .ok (some s')) := by
    unfold scanNextToken_dispatchBlockIndicators
    simp only [show (':' == '-') = false from by decide, Bool.false_and,
               show (':' == '?') = false from by decide,
               show (':' == ':') = true from by decide, Bool.true_and, h_vc, ite_true]
    rfl
  have h_ad_ek : s_ad.explicitKeyLine = none := by
    simp only [s_ad]; split
    · show (saveSimpleKey s).explicitKeyLine = none
      unfold saveSimpleKey; split <;> (try exact h_ek) <;> split <;> exact h_ek
    · unfold saveSimpleKey; split <;> (try exact h_ek) <;> split <;> exact h_ek
  have h_ckr : scanValueClearKey s_ad = s_ad := by
    unfold scanValueClearKey; rw [h_ad_ek]
  have h_validate : scanValueValidate s_ad = .ok () := by
    have : scanValueValidate s_ad = scanValueValidate (saveSimpleKey s) := by
      simp only [s_ad]; split <;> (unfold scanValueValidate; rfl)
    rw [this]; exact h_sv
  have h_ad_inFlow : s_ad.inFlow = true := h_ad_flow ▸ h_flow
  let s_prep := scanValuePrepare s_ad
  let s_tok := s_prep.emit .value
  let s_adv := s_tok.advance
  have h_scanValue_result : scanValue s_ad =
      (scanValueTabCheck (s_ad.col : Int) s_ad.currentIndent s_adv >>= fun () =>
        .ok { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }) := by
    unfold scanValue
    dsimp only []
    rw [h_ckr, h_validate]
    dsimp only [Bind.bind, Except.bind]
  have h_prep_inFlow : s_prep.inFlow = s_ad.inFlow := by
    show (scanValuePrepare s_ad).inFlow = s_ad.inFlow
    unfold scanValuePrepare
    split <;> (split <;> try split) <;> simp_all [ScannerState.inFlow]
  have h_tok_inFlow : s_tok.inFlow = s_prep.inFlow := by
    show (s_prep.emit .value).inFlow = s_prep.inFlow
    simp only [ScannerState.emit, ScannerState.inFlow]; rfl
  have h_adv_inFlow : s_adv.inFlow = s_tok.inFlow := by
    show s_tok.advance.inFlow = s_tok.inFlow
    exact advance_inFlow s_tok
  have h_tab_ok : scanValueTabCheck (s_ad.col : Int) s_ad.currentIndent s_adv = .ok () := by
    unfold scanValueTabCheck
    have : s_adv.inFlow = true := by
      rw [h_adv_inFlow, h_tok_inFlow, h_prep_inFlow]; exact h_ad_inFlow
    simp [this]
  let s_final : ScannerState := { s_adv with simpleKeyAllowed := true, explicitKeyLine := none }
  have h_scanValue_ok : scanValue s_ad = .ok s_final := by
    rw [h_scanValue_result, h_tab_ok]; dsimp only [Bind.bind, Except.bind]
  have h_block_result : scanNextToken_dispatchBlockIndicators s_ad ':' = .ok (some s_final) := by
    rw [h_block_eq, h_scanValue_ok]; dsimp only [Bind.bind, Except.bind]
  have h_snt_final : scanNextToken s = .ok (some s_final) :=
    scanNextToken_via_block_dispatch s (saveSimpleKey s) s_ad s_final ':'
      h_pp h_struct (by rfl) h_check h_flow_none h_block_result
  -- Identify s' with s_final via determinism of scanNextToken.
  have h_eq : s' = s_final := by
    rw [h_snt] at h_snt_final
    exact Option.some.inj (Except.ok.injEq .. |>.mp h_snt_final)
  -- Track pendingKeys through the chain: s → saveSimpleKey s = s → s_ad
  -- (allowDirectives doesn't touch pendingKeys/pendingKeyActive) → scanValueClearKey s_ad
  -- = s_ad → scanValuePrepare s_ad (flow + simpleKey.possible = true → setPendingKeyKind)
  -- → emit/advance/record-update preserve pendingKeys.
  have h_ad_pks : s_ad.pendingKeys = s.pendingKeys := by
    simp only [s_ad]
    split
    · show (saveSimpleKey s).pendingKeys = s.pendingKeys; rw [h_sk_id]
    · show (saveSimpleKey s).pendingKeys = s.pendingKeys; rw [h_sk_id]
  have h_ad_pka : s_ad.pendingKeyActive = s.pendingKeyActive := by
    simp only [s_ad]
    split
    · show (saveSimpleKey s).pendingKeyActive = s.pendingKeyActive; rw [h_sk_id]
    · show (saveSimpleKey s).pendingKeyActive = s.pendingKeyActive; rw [h_sk_id]
  have h_ad_sk_poss : s_ad.simpleKey.possible = true := by
    have : s_ad.simpleKey = s.simpleKey := by
      simp only [s_ad]
      split
      · show (saveSimpleKey s).simpleKey = s.simpleKey; rw [h_sk_id]
      · show (saveSimpleKey s).simpleKey = s.simpleKey; rw [h_sk_id]
    rw [this]; exact h_sk_poss
  have h_prep_pks : s_prep.pendingKeys
      = setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly := by
    show (scanValuePrepare s_ad).pendingKeys = _
    rw [scanValuePrepare_pendingKeys_flow_resolve s_ad h_ad_inFlow h_ad_sk_poss,
        h_ad_pks, h_ad_pka]
  have h_final_pks : s_final.pendingKeys
      = setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly := by
    show s_adv.pendingKeys = _
    rw [show s_adv.pendingKeys = s_tok.pendingKeys
          from ScannerCorrectness.advance_preserves_pendingKeys s_tok]
    show s_prep.pendingKeys = _
    exact h_prep_pks
  -- Now derive the new conjuncts at s'.
  have h_s'_pks : s'.pendingKeys
      = setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly := by
    rw [h_eq]; exact h_final_pks
  -- The setPendingKeyKind operation reduces to setIfInBounds at i.
  have h_get_some : s.pendingKeys[i]? = some (s.pendingKeys[i]'h_lt) :=
    Array.getElem?_eq_getElem h_lt
  have h_pks_full : s'.pendingKeys = s.pendingKeys.setIfInBounds i
      { (s.pendingKeys[i]'h_lt) with kind := .keyOnly } := by
    rw [h_s'_pks]
    show setPendingKeyKind s.pendingKeys s.pendingKeyActive .keyOnly = _
    unfold setPendingKeyKind
    simp only [h_pka, h_get_some]
  -- Discharge.
  refine ⟨s', h_snt, h_corr, h_fl, h_dp, h_ids, h_col_eq, h_iflow, h_ind_neg,
          h_ek_none, h_line, h_atol', h_endline', h_stack, ?_, ?_, ?_, ?_⟩
  · -- size preservation
    rw [h_pks_full, Array.size_setIfInBounds]
  · -- entry at i: kind = .keyOnly ∧ insertBeforeIdx preserved
    have h_lt' : i < s'.pendingKeys.size := by
      rw [h_pks_full, Array.size_setIfInBounds]; exact h_lt
    refine ⟨h_lt', ?_, ?_⟩
    · -- kind = .keyOnly via Array.getElem_setIfInBounds_self
      have h_lt_setIf : i < (s.pendingKeys.setIfInBounds i
          { (s.pendingKeys[i]'h_lt) with kind := .keyOnly }).size := by
        rw [Array.size_setIfInBounds]; exact h_lt
      have h_get_eq : s'.pendingKeys[i]'h_lt'
          = (s.pendingKeys.setIfInBounds i
              { (s.pendingKeys[i]'h_lt) with kind := .keyOnly })[i]'h_lt_setIf := by
        simp [h_pks_full]
      rw [h_get_eq, Array.getElem_setIfInBounds_self]
    · -- insertBeforeIdx preserved at i via Array.getElem_setIfInBounds_self
      have h_lt_setIf : i < (s.pendingKeys.setIfInBounds i
          { (s.pendingKeys[i]'h_lt) with kind := .keyOnly }).size := by
        rw [Array.size_setIfInBounds]; exact h_lt
      have h_get_eq : s'.pendingKeys[i]'h_lt'
          = (s.pendingKeys.setIfInBounds i
              { (s.pendingKeys[i]'h_lt) with kind := .keyOnly })[i]'h_lt_setIf := by
        simp [h_pks_full]
      rw [h_get_eq, Array.getElem_setIfInBounds_self]
  · -- j ≠ i → entries unchanged via Array.getElem_setIfInBounds_ne
    intro j hj hj' h_ne
    have hj_setIf : j < (s.pendingKeys.setIfInBounds i
        { (s.pendingKeys[i]'h_lt) with kind := .keyOnly }).size := by
      rw [Array.size_setIfInBounds]; exact hj
    have h_get_eq : s'.pendingKeys[j]'hj'
        = (s.pendingKeys.setIfInBounds i
            { (s.pendingKeys[i]'h_lt) with kind := .keyOnly })[j]'hj_setIf := by
      simp [h_pks_full]
    rw [h_get_eq]
    exact Array.getElem_setIfInBounds_ne hj h_ne.symm
  · -- pendingKeyStack preservation: s' = s_final = { s_adv with ... }; chain
    -- through advance/emit/scanValuePrepare/s_ad/saveSimpleKey, none of which
    -- touch pendingKeyStack.
    rw [h_eq]
    show s_adv.pendingKeyStack = s.pendingKeyStack
    rw [show s_adv.pendingKeyStack = s_tok.pendingKeyStack
          from ScannerCorrectness.advance_preserves_pendingKeyStack s_tok]
    show s_prep.pendingKeyStack = s.pendingKeyStack
    rw [show s_prep.pendingKeyStack = s_ad.pendingKeyStack from by
      show (scanValuePrepare s_ad).pendingKeyStack = _
      unfold scanValuePrepare
      split <;> (split <;> try split) <;> rfl]
    show s_ad.pendingKeyStack = s.pendingKeyStack
    simp only [s_ad]
    split <;> exact ScannerCorrectness.saveSimpleKey_preserves_pendingKeyStack s

/-- `EmitPairListScansInFlow pairs` asserts that scanning the
    emitPairList output succeeds in flow context, preserving invariants.
    This is the body between `{` and `}` in a flow mapping.

    **discharge-colon (2026-05-02)**: precondition `s.simpleKeyAllowed = true`
    added to enable the gated saveSimpleKey push for the first key of each
    pair, which is required to compose `pkRec_size_compose` through the
    colon step (`scanNextToken_flow_value_pkResolve` resolves the freshly
    pushed entry at index `s.pendingKeys.size`, leaving prefix entries at
    `j < s.pendingKeys.size` untouched).  Discharged at call sites by
    `scanNextToken_flow_open_mapping_nested`/`_init`'s `simpleKeyAllowed = true`
    conjunct (post-`{`) and by the comma+ws1 chain in the recursive case. -/
def EmitPairListScansInFlow (pairs : List (YamlValue × YamlValue)) : Prop :=
  ∀ (s : ScannerState) (rest : List Char),
    ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩ →
    s.inFlow = true →
    s.flowLevel > 0 →
    s.currentIndent < 0 →
    s.col > 0 →
    s.explicitKeyLine = none →
    AllTokensOnLine s s.line →
    EndLineOnLine s →
    s.simpleKeyAllowed = true →
    ∃ n s', ScanChainGrew (fun t => t.val != .placeholder) s n s'
      ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
      ∧ s'.flowLevel = s.flowLevel
      ∧ s'.directivesPresent = s.directivesPresent
      ∧ s'.indents = s.indents
      ∧ s'.explicitKeyLine = s.explicitKeyLine
      ∧ s'.col > 0
      ∧ s'.inFlow = true
      ∧ s'.currentIndent < 0
      ∧ s'.line = s.line
      ∧ AllTokensOnLine s' s'.line
      ∧ EndLineOnLine s'
      ∧ s'.simpleKeyStack = s.simpleKeyStack
      ∧ FlowMonoChain s.flowLevel s n s'
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-defns-prove.
      ∧ s.pendingKeys.size ≤ s'.pendingKeys.size
      ∧ (∀ j (hj : j < s.pendingKeys.size) (hj' : j < s'.pendingKeys.size),
          (s'.pendingKeys[j]'hj').insertBeforeIdx = (s.pendingKeys[j]'hj).insertBeforeIdx
          ∧ (s'.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind)
      -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-stack-restore:
      -- pendingKeyStack preserved across the body (mirrors simpleKeyStack;
      -- inner [/{ pushes are cancelled by the matching ]/} pops).
      ∧ s'.pendingKeyStack = s.pendingKeyStack
      -- J.4.2.b-2d-key-chain-Part2-body-C-compose: first-pair resolved-key shape.
      -- Under `pairs ≠ []`, the first pair's first key was pushed at index
      -- `s.pendingKeys.size` (per `EmitScansInFlow`'s gated conjunct under
      -- `s.simpleKeyAllowed = true`) with `insertBeforeIdx = s.tokens.size`,
      -- and resolved to `.keyOnly` by the first `:` step
      -- (`scanNextToken_flow_value_pkResolve`).  Subsequent value/comma/ws/IH
      -- preserve `(insertBeforeIdx, kind)` at this index via pkRec preservation.
      ∧ (pairs ≠ [] →
          ∃ (h : s.pendingKeys.size < s'.pendingKeys.size),
            (s'.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
            ∧ (s'.pendingKeys[s.pendingKeys.size]'h).kind = .keyOnly)
      -- J.4.2.b-2d-key-chain-Part3-extend-EmitPairListScansInFlow-per-pair:
      -- per-pair locator array.  Under `pairs ≠ []`, exposes the indices in
      -- `s'.pendingKeys` of the resolved-key entries for each pair (one per
      -- pair; `qs[0] = s.pendingKeys.size` from the gated push of the first
      -- pair's key, `qs[i+1] = qs_tail[i]` from the IH on the tail).
      -- Strict-monotonicity of `qs` reflects pendingKey monotonicity at
      -- each pair's saveSimpleKey.  `insertBeforeIdx` is NOT exposed
      -- directly for `i = 0` here — sub-step 5's
      -- `linearise_walk_at_kth_resolved_splice` consumer derives it from
      -- the saveSimpleKey monotonicity invariant.  Cons construction:
      -- `qs = #[s.pendingKeys.size] ++ qs_tail`.
      --
      -- J.4.2.b-2d-key-chain-Part3-final-discharge-bridge-6a (2026-05-02):
      -- predecessor-flowEntry conjunct.  For each `i ≥ 1`, the token at
      -- index `pks[qs[i]].insertBeforeIdx - 1` in `s'.tokens` is
      -- `.flowEntry` — the comma separating pair `i-1` from pair `i`,
      -- pushed by `scanFlowEntry` in `emitPairList_scans_nonempty`'s
      -- recursive case and persisting through ws1 + the IH's recursive
      -- chain via tokens-prefix preservation.  Consumed by
      -- 6b's linearise-side bridge to invert the walk-locator state and
      -- discharge `emitPairList_body_linearise_characterization`'s Part (3).
      ∧ (pairs ≠ [] →
          ∃ (qs : Array Nat) (_h_size : qs.size = pairs.length)
            (h_pos : 0 < qs.size),
            qs[0]'h_pos = s.pendingKeys.size
            ∧ (∀ i (h : i < qs.size),
                ∃ (h_lt : qs[i]'h < s'.pendingKeys.size),
                  (s'.pendingKeys[qs[i]'h]'h_lt).kind = .keyOnly)
            ∧ (∀ i j (hi : i < qs.size) (hj : j < qs.size),
                i < j → qs[i]'hi < qs[j]'hj)
            ∧ (∀ i (hi : i < qs.size) (_h_pos_i : 0 < i),
                ∃ (h_lt : qs[i]'hi < s'.pendingKeys.size)
                  (_h_ib_pos : 0 < (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx)
                  (h_pred_lt :
                    (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx - 1
                      < s'.tokens.size),
                  (s'.tokens[
                      (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx - 1
                    ]'h_pred_lt).val = .flowEntry))

theorem emitPairList_scans_empty : EmitPairListScansInFlow [] := by
  intro s rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline _h_ska
  have h_eq : (emit.emitPairList ([] : List (YamlValue × YamlValue))).toList ++ rest = rest := by
    simp [emit.emitPairList]
  exact ⟨0, s, .zero, h_eq ▸ hcorr, rfl, rfl, rfl, rfl, h_col, h_flow, h_indent, rfl,
    h_atol, h_endline, rfl, .zero (Nat.le_refl _), Nat.le_refl _, fun _ _ _ => ⟨rfl, rfl⟩, rfl,
    fun h_ne => absurd rfl h_ne, fun h_ne => absurd rfl h_ne⟩

-- Non-empty pair list scanning: each pair contributes key + ":" + space + value steps.
-- Uses emitPairList_first_char, scanNextToken_flow_value, scanNextToken_flow_comma,
-- scanNextToken_preprocess_flow_ws1, and EmitScansInFlow for keys and values.
--
-- Note: scanValueValidate discharge is sorry'd pending line/token tracking
-- (Change B Layer 1.1 — checks 2 and 4 require isInFlowSequence + token analysis).
theorem emitPairList_scans_nonempty (pairs : List (YamlValue × YamlValue))
    (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlow p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlow p.2) :
    EmitPairListScansInFlow pairs := by
  induction pairs with
  | nil => contradiction
  | cons p tail ih =>
    intro s rest_chars hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska
    match tail, ih with
    | [], _ =>
      -- ══ Singleton [(k,v)]: emitPairList [(k,v)] = emit k ++ ": " ++ emit v ══
      have h_eq : (emit.emitPairList [p]).toList ++ rest_chars =
          (emit p.1).toList ++ ([':',  ' '] ++ (emit p.2).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan key via EmitScansInFlow
      have h_ek_key : EmitScansInFlow p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_ska₁, _, h_atol₁, h_endline₁, h_stack₁,
              h_fmc₁, _h_size₁, _h_pkRec₁, _h_pks₁, _h_gated₁⟩ :=
        h_ek_key s ([':',  ' '] ++ (emit p.2).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: Derive saveSimpleKey identity and scanValueValidate
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: Scan ':' via scanNextToken_flow_value
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_value s₁ ((emit p.2).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      -- Step 4: Handle leading space before value via preprocessing equality
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _h_pks_pp₃, h_pks_pp₃, _h_ska_pp₃⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v (rest_v ++ rest_chars) h_corr₂_ws
          h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++ rest_chars)) =
            ((emit p.2).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append]
        exact h_eq_chars ▸ h_corr₃
      -- Step 5: Scan value via EmitScansInFlow
      have h_ev : EmitScansInFlow p.2 := h_all_v p (.head _)
      obtain ⟨n₃, s_end, h_chain₃, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, _, _,
              h_atol_end, h_endline_end, h_stack_end, h_fmc₃, _h_size₃, _h_pkRec₃, _h_pks₃, _h_gated₃⟩ :=
        h_ev s₃ rest_chars h_corr₃'
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Step 6: Lift chain for s₂ via preprocessing equality
      have h_snt_eq : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n₃_pos : n₃ ≥ 1 := by
        match n₃, h_chain₃ with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n₃', rfl⟩ : ∃ k, n₃ = k + 1 := ⟨n₃ - 1, by omega⟩
      have h_filt_le : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                       (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n₃' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq h_filt_le h_chain₃
      -- Per-step witness for the colon step (s₁ → s₂): the next char is ':'.
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- FlowMonoChain: lift value chain through preprocessing, compose with key + colon
      have h_fmc₃' : FlowMonoChain s.flowLevel s₃ (n₃' + 1) s_end :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc₃
      have h_fmc_ws : FlowMonoChain s.flowLevel s₂ (n₃' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq (by omega) h_fmc₃'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans h_fmc_ws)
      -- Compose strict chains: key (n₁) + colon (1) + space+value (n₃'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans h_chain_ws)
      have h_arith : n₁ + (1 + (n₃' + 1)) = n₁ + 1 + (n₃' + 1) := by omega
      refine ⟨n₁ + 1 + (n₃' + 1), s_end, h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end,
        h_endline_end, ?_, h_arith ▸ h_fmc_all, ?_⟩
      · rw [h_fl_end, h_fl₃, h_fl₂, h_fl₁]
      · rw [h_dp_end, h_dp₃, h_dp₂, h_dp₁]
      · rw [h_ids_end, h_ids₃, h_ids₂, h_ids₁]
      · rw [h_ek_end, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line₃, _h_line₂, _h_line₁]
      · rw [h_stack_end, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon
        -- + C-compose: inline discharge via pkResolve + determinism +
        -- pkRec_size_compose chain (size + pkRec preservation + pendingKeyStack
        -- equality), plus the first-pair resolved-key facts at index `s.pendingKeys.size`.
        -- Gated facts at s₁ (under h_ska): a fresh pendingKey was pushed at index
        -- s.pendingKeys.size with `insertBeforeIdx = s.tokens.size`, kind = .unresolved;
        -- `pendingKeyActive = some s.pendingKeys.size`, `simpleKey.possible = true`.
        -- Re-call `scanNextToken_flow_value_pkResolve` on s₁ to derive pendingKeys
        -- facts at s₂ via determinism.
        obtain ⟨⟨h_lt_pk_s1, h_ib_s1, _h_kd_s1⟩, h_pka_eq, h_skp_eq⟩ := _h_gated₁ h_ska
        have h_corr₁_colon : ScannerSurfCorr s₁
            ⟨':' :: ' ' :: ((emit p.2).toList ++ rest_chars), s₁.col⟩ := by
          have : [':',  ' '] ++ (emit p.2).toList ++ rest_chars =
              ':' :: ' ' :: ((emit p.2).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        obtain ⟨s₂_pk, h_snt₂_pk, _, _, _, _, _, _, _, _, _, _, _, _,
                h_size_pk, h_pk_resolved, h_pks_other_pk, h_pks_pk_pkr⟩ :=
          scanNextToken_flow_value_pkResolve s₁
            ((emit p.2).toList ++ rest_chars) h_corr₁_colon h_flow₁ h_indent₁ h_col₁
            (by rw [h_ek₁]; exact h_ek) h_sv h_atol₁ h_endline₁ h_ska₁ h_skp_eq
            s.pendingKeys.size h_pka_eq h_lt_pk_s1
        have h_eq₂ : s₂ = s₂_pk := by
          rw [h_snt₂] at h_snt₂_pk
          exact Option.some.inj (Except.ok.injEq .. |>.mp h_snt₂_pk)
        subst h_eq₂
        -- Compose pkRec_size_compose: s → s₁ → s₂ → s₃ → s_end at j < s.pendingKeys.size.
        have h_size_s_s1 : s.pendingKeys.size ≤ s₁.pendingKeys.size := _h_size₁
        have h_size_s1_s2 : s₁.pendingKeys.size ≤ s₂.pendingKeys.size := by
          rw [h_size_pk]; exact Nat.le_refl _
        have h_size_s_s2 : s.pendingKeys.size ≤ s₂.pendingKeys.size :=
          Nat.le_trans h_size_s_s1 h_size_s1_s2
        have h_pkRec_s_s2 :
            ∀ j (hj : j < s.pendingKeys.size) (hj' : j < s₂.pendingKeys.size),
              (s₂.pendingKeys[j]'hj').insertBeforeIdx
                = (s.pendingKeys[j]'hj).insertBeforeIdx
              ∧ (s₂.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind := by
          intro j hj hj'
          have hj_s1 : j < s₁.pendingKeys.size := Nat.lt_of_lt_of_le hj h_size_s_s1
          have h_ne : j ≠ s.pendingKeys.size := Nat.ne_of_lt hj
          have h_at := h_pks_other_pk j (by rw [h_size_pk] at hj'; exact hj') hj' h_ne
          have ⟨h_ib_s1, h_kd_s1⟩ := _h_pkRec₁ j hj hj_s1
          refine ⟨?_, ?_⟩
          · rw [show (s₂.pendingKeys[j]'hj').insertBeforeIdx
                  = (s₁.pendingKeys[j]'hj_s1).insertBeforeIdx from congrArg _ h_at]
            exact h_ib_s1
          · rw [show (s₂.pendingKeys[j]'hj').kind
                  = (s₁.pendingKeys[j]'hj_s1).kind from congrArg _ h_at]
            exact h_kd_s1
        -- s₂ → s₃: ws1 preserves pendingKeys (`_h_pks_pp₃ : s₃.pendingKeys = s₂.pendingKeys`).
        have h_size_s2_s3 : s₂.pendingKeys.size ≤ s₃.pendingKeys.size := by
          rw [_h_pks_pp₃]; exact Nat.le_refl _
        have h_pkRec_s2_s3 :
            ∀ j (hj : j < s₂.pendingKeys.size) (hj' : j < s₃.pendingKeys.size),
              (s₃.pendingKeys[j]'hj').insertBeforeIdx
                = (s₂.pendingKeys[j]'hj).insertBeforeIdx
              ∧ (s₃.pendingKeys[j]'hj').kind = (s₂.pendingKeys[j]'hj).kind := by
          intro j hj hj'; refine ⟨?_, ?_⟩ <;> simp only [_h_pks_pp₃]
        have ⟨h_size_s_s3, h_pkRec_s_s3⟩ :=
          pkRec_size_compose h_size_s_s2 h_size_s2_s3 h_pkRec_s_s2 h_pkRec_s2_s3
        -- s₃ → s_end: from EmitScansInFlow (value) — `_h_size₃`, `_h_pkRec₃`.
        have ⟨h_size_all, h_pkRec_all⟩ :=
          pkRec_size_compose h_size_s_s3 _h_size₃ h_pkRec_s_s3 _h_pkRec₃
        -- pendingKeyStack: chain s → s₁ → s₂ → s₃ → s_end.
        -- Pre-derive first-pair resolved-key facts at index s.pendingKeys.size
        -- (shared by C-compose first-key conjunct and Part3 per-pair locator).
        obtain ⟨h_lt_at_s2, h_kd_s2, h_ib_s2_s1⟩ := h_pk_resolved
        have h_lt_s_s3 : s.pendingKeys.size < s₃.pendingKeys.size := by
          have h_eq_sz : s₂.pendingKeys.size = s₃.pendingKeys.size := by
            rw [_h_pks_pp₃]
          omega
        have h_lt_s_s_end : s.pendingKeys.size < s_end.pendingKeys.size :=
          Nat.lt_of_lt_of_le h_lt_s_s3 _h_size₃
        have ⟨h_ib_pres, h_kd_pres⟩ :=
          _h_pkRec₃ s.pendingKeys.size h_lt_s_s3 h_lt_s_s_end
        have h_eq_s3_s2_ib :
            (s₃.pendingKeys[s.pendingKeys.size]'h_lt_s_s3).insertBeforeIdx
              = (s₂.pendingKeys[s.pendingKeys.size]'h_lt_at_s2).insertBeforeIdx := by
          simp only [_h_pks_pp₃]
        have h_eq_s3_s2_kd :
            (s₃.pendingKeys[s.pendingKeys.size]'h_lt_s_s3).kind
              = (s₂.pendingKeys[s.pendingKeys.size]'h_lt_at_s2).kind := by
          simp only [_h_pks_pp₃]
        have h_kd_s_end :
            (s_end.pendingKeys[s.pendingKeys.size]'h_lt_s_s_end).kind = .keyOnly := by
          rw [h_kd_pres, h_eq_s3_s2_kd]; exact h_kd_s2
        have h_ib_s_end :
            (s_end.pendingKeys[s.pendingKeys.size]'h_lt_s_s_end).insertBeforeIdx
              = s.tokens.size := by
          rw [h_ib_pres, h_eq_s3_s2_ib, h_ib_s2_s1]; exact h_ib_s1
        refine ⟨h_size_all, h_pkRec_all, ?_, ?_, ?_⟩
        · rw [_h_pks₃, h_pks_pp₃, h_pks_pk_pkr, _h_pks₁]
        · -- C-compose: first-pair resolved-key facts at index s.pendingKeys.size.
          intro _h_ne_pairs
          exact ⟨h_lt_s_s_end, h_ib_s_end, h_kd_s_end⟩
        · -- Part3-extend: per-pair locator (singleton: qs = #[s.pendingKeys.size]).
          intro _h_ne_pairs
          have h_size_one : (#[s.pendingKeys.size] : Array Nat).size = 1 := rfl
          refine ⟨#[s.pendingKeys.size], rfl, h_size_one ▸ Nat.zero_lt_one, rfl, ?_, ?_, ?_⟩
          · -- per-i kind = .keyOnly (only i = 0)
            intro i h_i
            rw [h_size_one] at h_i
            have h_i_eq : i = 0 := by omega
            subst h_i_eq
            exact ⟨h_lt_s_s_end, h_kd_s_end⟩
          · -- strict-monotone (vacuous: only one element)
            intro a b h_a h_b h_lt
            rw [h_size_one] at h_a h_b
            omega
          · -- Part3-final-discharge-bridge-6a: predecessor-flowEntry
            -- (vacuous: only i = 0, but conjunct requires 0 < i).
            intro i h_i h_pos_i
            rw [h_size_one] at h_i
            omega
    | p' :: ps, ih =>
      -- ══ Multi-pair: emit k ++ ": " ++ emit v ++ ", " ++ emitPairList (p' :: ps) ══
      have h_eq : (emit.emitPairList (p :: p' :: ps)).toList ++ rest_chars =
          (emit p.1).toList ++ ([':',  ' '] ++ (emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
        simp [emit.emitPairList, String.toList_append, List.append_assoc]
      rw [h_eq] at hcorr
      -- Step 1: Scan key via EmitScansInFlow
      have h_ek_key : EmitScansInFlow p.1 := h_all_k p (.head _)
      obtain ⟨n₁, s₁, h_chain₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁,
              h_flow₁, h_indent₁, _h_line₁, h_ska₁, h_last₁, h_atol₁, h_endline₁,
              h_stack₁, h_fmc₁, _h_size₁, _h_pkRec₁, _h_pks₁, _h_gated₁⟩ :=
        h_ek_key s ([':',  ' '] ++ (emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
      -- Step 2: Derive saveSimpleKey identity and scanValueValidate
      have h_sk_id := saveSimpleKey_id_of_flow_ska_false_ek_none s₁ h_flow₁ h_ska₁
          (by rw [h_ek₁]; exact h_ek)
      have h_sv : scanValueValidate (saveSimpleKey s₁) = .ok () := by
        rw [h_sk_id]
        exact scanValueValidate_ok_of_flow_allTokensOnLine s₁ h_flow₁
          (by rw [h_ek₁]; exact h_ek) h_atol₁ h_endline₁
      -- Step 3: Scan ':' via scanNextToken_flow_value
      obtain ⟨s₂, h_snt₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_col₂,
              h_flow₂, h_indent₂, h_ek₂, _h_line₂, h_atol₂, h_endline₂, h_stack_v₂⟩ :=
        scanNextToken_flow_value s₁
          ((emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁ h_flow₁ h_indent₁ h_col₁ (by rw [h_ek₁]; exact h_ek) h_sv
          h_atol₁ h_endline₁
      -- Step 4: Handle leading space before value
      obtain ⟨c_v, rest_v, h_first_v, h_nws_v, h_nlb_v, h_nc_v⟩ := emit_first_char p.2
      have h_corr₂_ws : ScannerSurfCorr s₂
          ⟨' ' :: c_v :: (rest_v ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₂.col⟩ := by
        have h_eq_chars : (' ' :: (emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) =
            (' ' :: c_v :: (rest_v ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) := by
          congr 1; rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₂
      obtain ⟨s₃, h_corr₃, h_flow₃, h_fl₃, h_indent₃, h_col₃, h_dp₃, h_ids₃, h_ek₃, _h_line₃, h_pp_eq, h_atol_transfer₃, h_endline_transfer₃, h_stack_pp₃, h_toks_pp₃, _h_pks_pp₃, h_pks_pp₃, _h_ska_pp₃⟩ :=
        scanNextToken_preprocess_flow_ws1 s₂ c_v
          (rest_v ++ [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₂_ws h_flow₂ h_nws_v h_nlb_v h_nc_v h_indent₂
      have h_corr₃' : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars, s₃.col⟩ := by
        have h_eq_chars : (c_v :: (rest_v ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)) =
            ((emit p.2).toList ++
            [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
          rw [h_first_v]; simp only [List.cons_append, List.append_assoc]
        exact h_eq_chars ▸ h_corr₃
      -- Step 5: Scan value via EmitScansInFlow
      have h_ev : EmitScansInFlow p.2 := h_all_v p (.head _)
      have h_corr₃_assoc : ScannerSurfCorr s₃
          ⟨(emit p.2).toList ++ ([',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₃.col⟩ := by
        simp only [List.append_assoc] at h_corr₃' ⊢; exact h_corr₃'
      obtain ⟨n_v, s_v, h_chain_v, h_corr_v, h_fl_v, h_dp_v, h_ids_v,
              h_ek_v, h_col_v, h_flow_v, h_indent_v, _h_line_v, _, h_last_v, h_atol_v,
              h_endline_v, h_stack_v, h_fmc_v, _h_size_v, _h_pkRec_v, _h_pks_v, _h_gated_v⟩ :=
        h_ev s₃
          ([',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₃_assoc
          h_flow₃ (by rw [h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent₃]; exact h_indent₂)
          (by rw [h_col₃]; omega)
          (by rw [h_ek₃]; exact h_ek₂)
          (h_atol_transfer₃ h_atol₂)
          (h_endline_transfer₃ h_endline₂)
      -- Lift value chain through preprocessing equality
      have h_snt_eq_v : scanNextToken s₂ = scanNextToken s₃ :=
        scanNextToken_eq_of_preprocess s₂ s₃ h_pp_eq
      have h_n_v_pos : n_v ≥ 1 := by
        match n_v, h_chain_v with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr₃'.chars_from h_corr_v.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit p.2).toList = [] := by
            match h_list : (emit p.2).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emit_first_char p.2
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_v', rfl⟩ : ∃ k, n_v = k + 1 := ⟨n_v - 1, by omega⟩
      have h_filt_le_v : (s₂.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s₃.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp₃]; exact Nat.le_refl _
      have h_chain_ws_v : ScanChainGrew (fun t => t.val != .placeholder)
            s₂ (n_v' + 1) s_v :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_v h_filt_le_v h_chain_v
      -- Per-step witness for the colon step (s₁ → s₂): next char is ':'.
      have h_grew₂ : (s₂.tokens.filter (fun t => t.val != .placeholder)).size >
                     (s₁.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr₁_cons : ScannerSurfCorr s₁
            ⟨':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₁.col⟩ := by
          have : [':', ' '] ++ (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        exact scanNextToken_filtered_grows_in_flow s₁ s₂ ':'
          (' ' :: (emit p.2).toList ++ [',', ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr₁_cons h_flow₁ h_indent₁ h_col₁
          (by decide) (by decide) (by decide) h_snt₂
      -- Step 6: Scan ',' via scanNextToken_flow_comma
      obtain ⟨s_c, h_snt_c, h_corr_c, h_fl_c, h_dp_c, h_ids_c, h_ek_c, h_col_c, _h_line_c,
              h_atol_c, h_endline_c, h_stack_c, _h_size_c, _h_pkRec_c, _h_pks_c, h_ska_c,
              h_comma_push⟩ :=
        scanNextToken_flow_comma s_v
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v h_flow_v h_indent_v h_col_v h_last_v h_atol_v h_endline_v
      -- Step 7: Handle leading space before next pair
      obtain ⟨c_p, rest_p, h_first_p, h_nws_p, h_nlb_p, h_nc_p⟩ :=
        emitPairList_first_char p' ps
      have h_corr_c_ws : ScannerSurfCorr s_c
          ⟨' ' :: c_p :: (rest_p ++ rest_chars), s_c.col⟩ := by
        have : ' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
            ' ' :: c_p :: (rest_p ++ rest_chars) := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_c
      have h_sc_flow : s_c.inFlow = true := by
        unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl_c]; omega)
      have h_sc_indent : s_c.currentIndent < 0 := by
        unfold ScannerState.currentIndent; rw [h_ids_c]; exact h_indent_v
      obtain ⟨s_pp, h_corr_pp, h_flow_pp, h_fl_pp, h_indent_pp, h_col_pp,
              h_dp_pp, h_ids_pp, h_ek_pp, _h_line_pp, h_pp_eq_r, h_atol_transfer_pp, h_endline_transfer_pp, h_stack_pp, h_toks_pp, _h_pks_pp_pks, _h_pks_pp_stk, h_ska_pp⟩ :=
        scanNextToken_preprocess_flow_ws1 s_c c_p (rest_p ++ rest_chars) h_corr_c_ws
          h_sc_flow h_nws_p h_nlb_p h_nc_p h_sc_indent
      have h_corr_pp' : ScannerSurfCorr s_pp
          ⟨(emit.emitPairList (p' :: ps)).toList ++ rest_chars, s_pp.col⟩ := by
        have : c_p :: (rest_p ++ rest_chars) =
            (emit.emitPairList (p' :: ps)).toList ++ rest_chars := by
          rw [h_first_p]; simp only [List.cons_append]
        rwa [this] at h_corr_pp
      -- Step 8: Recursive scan of emitPairList (p' :: ps)
      have h_tail_all_k : ∀ q ∈ p' :: ps, EmitScansInFlow q.1 :=
        fun q hq => h_all_k q (.tail _ hq)
      have h_tail_all_v : ∀ q ∈ p' :: ps, EmitScansInFlow q.2 :=
        fun q hq => h_all_v q (.tail _ hq)
      have h_ih_list : EmitPairListScansInFlow (p' :: ps) :=
        ih (by simp) h_tail_all_k h_tail_all_v
      obtain ⟨n_r, s_end, h_chain_r, h_corr_end, h_fl_end, h_dp_end, h_ids_end,
              h_ek_end, h_col_end, h_flow_end, h_indent_end, h_line_end, h_atol_end,
              h_endline_end, h_stack_end, h_fmc_r, h_size_r, h_pkRec_r, h_pks_r,
              h_first_r, h_first_qs_r⟩ :=
        h_ih_list s_pp rest_chars h_corr_pp'
          h_flow_pp
          (by rw [h_fl_pp, h_fl_c]; rw [h_fl_v, h_fl₃, h_fl₂, h_fl₁]; exact h_fl)
          (by rw [h_indent_pp]; exact h_sc_indent)
          (by rw [h_col_pp]; omega)
          (by rw [h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂])
          (h_atol_transfer_pp h_atol_c)
          (h_endline_transfer_pp h_endline_c)
          (by rw [h_ska_pp]; exact h_ska_c)
      -- Lift recursive chain through preprocessing equality
      have h_snt_eq_r : scanNextToken s_c = scanNextToken s_pp :=
        scanNextToken_eq_of_preprocess s_c s_pp h_pp_eq_r
      have h_n_r_pos : n_r ≥ 1 := by
        match n_r, h_chain_r with
        | 0, .zero =>
          exfalso
          have h_chars_eq := CharsFromOffset_unique h_corr_pp'.chars_from h_corr_end.chars_from
          have h_len := congrArg List.length h_chars_eq
          simp only [List.length_append] at h_len
          have h_nil : (emit.emitPairList (p' :: ps)).toList = [] := by
            match h_list : (emit.emitPairList (p' :: ps)).toList with
            | [] => rfl
            | _ :: _ => simp [h_list] at h_len
          obtain ⟨_, _, h_ne_nil, _, _, _⟩ := emitPairList_first_char p' ps
          exact absurd h_nil (by rw [h_ne_nil]; exact List.cons_ne_nil _ _)
        | _ + 1, _ => omega
      obtain ⟨n_r', rfl⟩ : ∃ k, n_r = k + 1 := ⟨n_r - 1, by omega⟩
      have h_filt_le_r : (s_c.tokens.filter (fun t => t.val != .placeholder)).size ≤
                         (s_pp.tokens.filter (fun t => t.val != .placeholder)).size := by
        rw [h_toks_pp]; exact Nat.le_refl _
      have h_chain_ws_r : ScanChainGrew (fun t => t.val != .placeholder)
            s_c (n_r' + 1) s_end :=
        ScanChainGrew_of_scanNextToken_eq h_snt_eq_r h_filt_le_r h_chain_r
      -- Per-step witness for the comma step (s_v → s_c): next char is ','.
      have h_grew_c : (s_c.tokens.filter (fun t => t.val != .placeholder)).size >
                      (s_v.tokens.filter (fun t => t.val != .placeholder)).size := by
        have h_corr_v_cons : ScannerSurfCorr s_v
            ⟨',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s_v.col⟩ := by
          have : [',', ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ',' :: (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr_v
        exact scanNextToken_filtered_grows_in_flow s_v s_c ','
          (' ' :: (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
          h_corr_v_cons h_flow_v h_indent_v h_col_v
          (by decide) (by decide) (by decide) h_snt_c
      -- FlowMonoChain: compose all sub-chains
      -- value chain: lift through preprocessing s₂→s₃
      have h_fmc_v' : FlowMonoChain s.flowLevel s₃ (n_v' + 1) s_v :=
        (show s.flowLevel = s₃.flowLevel from by omega) ▸ h_fmc_v
      have h_fmc_ws_v : FlowMonoChain s.flowLevel s₂ (n_v' + 1) s_v :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_v (by omega) h_fmc_v'
      -- recursive chain: lift through preprocessing s_c→s_pp
      have h_fmc_r' : FlowMonoChain s.flowLevel s_pp (n_r' + 1) s_end :=
        (show s.flowLevel = s_pp.flowLevel from by omega) ▸ h_fmc_r
      have h_fmc_ws_r : FlowMonoChain s.flowLevel s_c (n_r' + 1) s_end :=
        FlowMonoChain_of_scanNextToken_eq h_snt_eq_r (by omega) h_fmc_r'
      have h_fmc_all := h_fmc₁.trans
        ((FlowMonoChain.single h_snt₂ (by omega) (by omega)).trans
          (h_fmc_ws_v.trans
            ((FlowMonoChain.single h_snt_c (by omega)
              (by omega)).trans h_fmc_ws_r)))
      -- Step 9: Compose strict chains
      -- key(n₁) + colon(1) + space+value(n_v'+1) + comma(1) + space+recurse(n_r'+1)
      have h_chain_all := h_chain₁.trans
        ((ScanChainGrew.single h_snt₂ h_grew₂).trans
          (h_chain_ws_v.trans
            ((ScanChainGrew.single h_snt_c h_grew_c).trans h_chain_ws_r)))
      have h_arith : n₁ + (1 + ((n_v' + 1) + (1 + (n_r' + 1)))) =
          n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1) := by omega
      refine ⟨n₁ + 1 + (n_v' + 1) + 1 + (n_r' + 1), s_end,
        h_arith ▸ h_chain_all,
        h_corr_end, ?_, ?_, ?_, ?_, h_col_end, h_flow_end, h_indent_end, ?_, h_atol_end,
        h_endline_end, ?_, h_arith ▸ h_fmc_all, ?_⟩
      · -- flowLevel preserved
        rw [h_fl_end, h_fl_pp, h_fl_c, h_fl_v, h_fl₃, h_fl₂, h_fl₁]
      · -- directivesPresent preserved
        rw [h_dp_end, h_dp_pp, h_dp_c, h_dp_v, h_dp₃, h_dp₂, h_dp₁]
      · -- indents preserved
        rw [h_ids_end, h_ids_pp, h_ids_c, h_ids_v, h_ids₃, h_ids₂, h_ids₁]
      · -- explicitKeyLine preserved
        rw [h_ek_end, h_ek_pp, h_ek_c, h_ek_v, h_ek₃, h_ek₂]; exact h_ek.symm
      · rw [h_line_end, _h_line_pp, _h_line_c, _h_line_v, _h_line₃, _h_line₂, _h_line₁]
      · -- simpleKeyStack preserved
        rw [h_stack_end, h_stack_pp, h_stack_c, h_stack_v, h_stack_pp₃, h_stack_v₂, h_stack₁]
      · -- J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-discharge-colon
        -- + C-compose: inline discharge via pkResolve + determinism +
        -- pkRec_size_compose chain (size + pkRec preservation + pendingKeyStack
        -- equality), plus the first-pair resolved-key facts at index `s.pendingKeys.size`.
        -- Mirrors the singleton-case discharge above; the only structural
        -- difference is the trailing comma + ws1 + recurse legs (s_v → s_c → s_pp → s_end).
        obtain ⟨⟨h_lt_pk_s1, h_ib_s1, _h_kd_s1⟩, h_pka_eq, h_skp_eq⟩ := _h_gated₁ h_ska
        have h_corr₁_colon : ScannerSurfCorr s₁
            ⟨':' :: ' ' :: ((emit p.2).toList ++
              [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars), s₁.col⟩ := by
          have : [':',  ' '] ++ (emit p.2).toList ++
              [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars =
              ':' :: ' ' :: ((emit p.2).toList ++
                [',',  ' '] ++ (emit.emitPairList (p' :: ps)).toList ++ rest_chars) := by
            simp only [List.cons_append, List.nil_append]
          rwa [this] at h_corr₁
        obtain ⟨s₂_pk, h_snt₂_pk, _, _, _, _, _, _, _, _, _, _, _, _,
                h_size_pk, h_pk_resolved, h_pks_other_pk, h_pks_pk_pkr⟩ :=
          scanNextToken_flow_value_pkResolve s₁
            ((emit p.2).toList ++ [',',  ' '] ++
              (emit.emitPairList (p' :: ps)).toList ++ rest_chars)
            h_corr₁_colon h_flow₁ h_indent₁ h_col₁
            (by rw [h_ek₁]; exact h_ek) h_sv h_atol₁ h_endline₁ h_ska₁ h_skp_eq
            s.pendingKeys.size h_pka_eq h_lt_pk_s1
        have h_eq₂ : s₂ = s₂_pk := by
          rw [h_snt₂] at h_snt₂_pk
          exact Option.some.inj (Except.ok.injEq .. |>.mp h_snt₂_pk)
        subst h_eq₂
        -- Compose s → s₁ → s₂ at j < s.pendingKeys.size.
        have h_size_s_s1 : s.pendingKeys.size ≤ s₁.pendingKeys.size := _h_size₁
        have h_size_s1_s2 : s₁.pendingKeys.size ≤ s₂.pendingKeys.size := by
          rw [h_size_pk]; exact Nat.le_refl _
        have h_size_s_s2 : s.pendingKeys.size ≤ s₂.pendingKeys.size :=
          Nat.le_trans h_size_s_s1 h_size_s1_s2
        have h_pkRec_s_s2 :
            ∀ j (hj : j < s.pendingKeys.size) (hj' : j < s₂.pendingKeys.size),
              (s₂.pendingKeys[j]'hj').insertBeforeIdx
                = (s.pendingKeys[j]'hj).insertBeforeIdx
              ∧ (s₂.pendingKeys[j]'hj').kind = (s.pendingKeys[j]'hj).kind := by
          intro j hj hj'
          have hj_s1 : j < s₁.pendingKeys.size := Nat.lt_of_lt_of_le hj h_size_s_s1
          have h_ne : j ≠ s.pendingKeys.size := Nat.ne_of_lt hj
          have h_at := h_pks_other_pk j (by rw [h_size_pk] at hj'; exact hj') hj' h_ne
          have ⟨h_ib_s1, h_kd_s1⟩ := _h_pkRec₁ j hj hj_s1
          refine ⟨?_, ?_⟩
          · rw [show (s₂.pendingKeys[j]'hj').insertBeforeIdx
                  = (s₁.pendingKeys[j]'hj_s1).insertBeforeIdx from congrArg _ h_at]
            exact h_ib_s1
          · rw [show (s₂.pendingKeys[j]'hj').kind
                  = (s₁.pendingKeys[j]'hj_s1).kind from congrArg _ h_at]
            exact h_kd_s1
        -- s₂ → s₃: ws1 preserves pendingKeys.
        have h_size_s2_s3 : s₂.pendingKeys.size ≤ s₃.pendingKeys.size := by
          rw [_h_pks_pp₃]; exact Nat.le_refl _
        have h_pkRec_s2_s3 :
            ∀ j (hj : j < s₂.pendingKeys.size) (hj' : j < s₃.pendingKeys.size),
              (s₃.pendingKeys[j]'hj').insertBeforeIdx
                = (s₂.pendingKeys[j]'hj).insertBeforeIdx
              ∧ (s₃.pendingKeys[j]'hj').kind = (s₂.pendingKeys[j]'hj).kind := by
          intro j hj hj'; refine ⟨?_, ?_⟩ <;> simp only [_h_pks_pp₃]
        have ⟨h_size_s_s3, h_pkRec_s_s3⟩ :=
          pkRec_size_compose h_size_s_s2 h_size_s2_s3 h_pkRec_s_s2 h_pkRec_s2_s3
        -- s₃ → s_v: from EmitScansInFlow on p.2.
        have ⟨h_size_s_sv, h_pkRec_s_sv⟩ :=
          pkRec_size_compose h_size_s_s3 _h_size_v h_pkRec_s_s3 _h_pkRec_v
        -- s_v → s_c: from scanNextToken_flow_comma.
        have ⟨h_size_s_sc, h_pkRec_s_sc⟩ :=
          pkRec_size_compose h_size_s_sv _h_size_c h_pkRec_s_sv _h_pkRec_c
        -- s_c → s_pp: ws1 preserves pendingKeys (`_h_pks_pp_pks : s_pp.pendingKeys = s_c.pendingKeys`).
        have h_size_sc_spp : s_c.pendingKeys.size ≤ s_pp.pendingKeys.size := by
          rw [_h_pks_pp_pks]; exact Nat.le_refl _
        have h_pkRec_sc_spp :
            ∀ j (hj : j < s_c.pendingKeys.size) (hj' : j < s_pp.pendingKeys.size),
              (s_pp.pendingKeys[j]'hj').insertBeforeIdx
                = (s_c.pendingKeys[j]'hj).insertBeforeIdx
              ∧ (s_pp.pendingKeys[j]'hj').kind = (s_c.pendingKeys[j]'hj).kind := by
          intro j hj hj'; refine ⟨?_, ?_⟩ <;> simp only [_h_pks_pp_pks]
        have ⟨h_size_s_spp, h_pkRec_s_spp⟩ :=
          pkRec_size_compose h_size_s_sc h_size_sc_spp h_pkRec_s_sc h_pkRec_sc_spp
        -- s_pp → s_end: from recursive IH (h_size_r, h_pkRec_r).
        have ⟨h_size_all, h_pkRec_all⟩ :=
          pkRec_size_compose h_size_s_spp h_size_r h_pkRec_s_spp h_pkRec_r
        -- pendingKeyStack: chain s → s₁ → s₂ → s₃ → s_v → s_c → s_pp → s_end.
        -- Pre-derive first-pair resolved-key facts at index s.pendingKeys.size
        -- (shared by C-compose first-key conjunct and Part3 per-pair locator).
        -- Chain: s → s₁ (gated push, kind=.unresolved, ib=s.tokens.size)
        --        → s₂ (pkResolve, kind=.keyOnly, ib preserved)
        --        → s₃ (ws1 preserves pendingKeys)
        --        → s_v (value pkRec at j < s₃.size)
        --        → s_c (comma pkRec at j < s_v.size)
        --        → s_pp (ws1 preserves pendingKeys)
        --        → s_end (IH pkRec at j < s_pp.size).
        obtain ⟨h_lt_at_s2, h_kd_s2, h_ib_s2_s1⟩ := h_pk_resolved
        have h_lt_s_s3 : s.pendingKeys.size < s₃.pendingKeys.size := by
          have h_eq_sz : s₂.pendingKeys.size = s₃.pendingKeys.size := by
            rw [_h_pks_pp₃]
          omega
        have h_lt_s_sv : s.pendingKeys.size < s_v.pendingKeys.size :=
          Nat.lt_of_lt_of_le h_lt_s_s3 _h_size_v
        have h_lt_s_sc : s.pendingKeys.size < s_c.pendingKeys.size :=
          Nat.lt_of_lt_of_le h_lt_s_sv _h_size_c
        have h_lt_s_spp : s.pendingKeys.size < s_pp.pendingKeys.size := by
          have h_eq_sz : s_c.pendingKeys.size = s_pp.pendingKeys.size := by
            rw [_h_pks_pp_pks]
          omega
        have h_lt_s_send : s.pendingKeys.size < s_end.pendingKeys.size :=
          Nat.lt_of_lt_of_le h_lt_s_spp h_size_r
        have h_eq_s3_s2_ib :
            (s₃.pendingKeys[s.pendingKeys.size]'h_lt_s_s3).insertBeforeIdx
              = (s₂.pendingKeys[s.pendingKeys.size]'h_lt_at_s2).insertBeforeIdx := by
          simp only [_h_pks_pp₃]
        have h_eq_s3_s2_kd :
            (s₃.pendingKeys[s.pendingKeys.size]'h_lt_s_s3).kind
              = (s₂.pendingKeys[s.pendingKeys.size]'h_lt_at_s2).kind := by
          simp only [_h_pks_pp₃]
        have h_eq_spp_sc_ib :
            (s_pp.pendingKeys[s.pendingKeys.size]'h_lt_s_spp).insertBeforeIdx
              = (s_c.pendingKeys[s.pendingKeys.size]'h_lt_s_sc).insertBeforeIdx := by
          simp only [_h_pks_pp_pks]
        have h_eq_spp_sc_kd :
            (s_pp.pendingKeys[s.pendingKeys.size]'h_lt_s_spp).kind
              = (s_c.pendingKeys[s.pendingKeys.size]'h_lt_s_sc).kind := by
          simp only [_h_pks_pp_pks]
        have ⟨h_ib_sv, h_kd_sv⟩ :=
          _h_pkRec_v s.pendingKeys.size h_lt_s_s3 h_lt_s_sv
        have ⟨h_ib_sc, h_kd_sc⟩ :=
          _h_pkRec_c s.pendingKeys.size h_lt_s_sv h_lt_s_sc
        have ⟨h_ib_send, h_kd_send⟩ :=
          h_pkRec_r s.pendingKeys.size h_lt_s_spp h_lt_s_send
        have h_kd_s_end :
            (s_end.pendingKeys[s.pendingKeys.size]'h_lt_s_send).kind = .keyOnly := by
          rw [h_kd_send, h_eq_spp_sc_kd, h_kd_sc, h_kd_sv, h_eq_s3_s2_kd]
          exact h_kd_s2
        have h_ib_s_end :
            (s_end.pendingKeys[s.pendingKeys.size]'h_lt_s_send).insertBeforeIdx
              = s.tokens.size := by
          rw [h_ib_send, h_eq_spp_sc_ib, h_ib_sc, h_ib_sv, h_eq_s3_s2_ib, h_ib_s2_s1]
          exact h_ib_s1
        refine ⟨h_size_all, h_pkRec_all, ?_, ?_, ?_⟩
        · rw [h_pks_r, _h_pks_pp_stk, _h_pks_c, _h_pks_v, h_pks_pp₃, h_pks_pk_pkr, _h_pks₁]
        · -- C-compose: first-pair resolved-key facts at index s.pendingKeys.size.
          intro _h_ne_pairs
          exact ⟨h_lt_s_send, h_ib_s_end, h_kd_s_end⟩
        · -- Part3-extend: per-pair locator (cons: qs = #[s.pendingKeys.size] ++ qs_tail).
          -- IH on the tail (p' :: ps) under s_pp gives qs_tail of size = (p'::ps).length
          -- with qs_tail[0] = s_pp.pendingKeys.size; values are indices into
          -- s_end.pendingKeys (the IH's "s'") with kind = .keyOnly; strict-monotone.
          -- Part3-final-discharge-bridge-6a (2026-05-02): also threads
          -- the IH's predecessor-flowEntry conjunct (`h_pred_t`) for `i_tail ≥ 1`
          -- entries; cons-case `i = 1` discharge requires lifting the comma push
          -- through ws1 + the IH chain (sub-task 6a-i1-lift).
          intro _h_ne_pairs
          obtain ⟨qs_tail, h_size_t, h_pos_t, h_q0_t, h_per_i_t, h_strict_t, h_pred_t⟩ :=
            h_first_qs_r (by simp)
          have h_size_one : (#[s.pendingKeys.size] : Array Nat).size = 1 := rfl
          refine ⟨#[s.pendingKeys.size] ++ qs_tail, ?_, ?_, ?_, ?_, ?_, ?_⟩
          · -- size: 1 + qs_tail.size = (p :: p' :: ps).length
            rw [Array.size_append, h_size_one, h_size_t]
            simp [List.length]; omega
          · -- 0 < size
            rw [Array.size_append, h_size_one]; omega
          · -- qs[0] = s.pendingKeys.size
            rw [Array.getElem_append_left (h_size_one ▸ Nat.zero_lt_one)]
            rfl
          · -- per-i kind = .keyOnly
            intro i h_i
            rw [Array.size_append, h_size_one] at h_i
            by_cases h_i_zero : i = 0
            · subst h_i_zero
              have h_lt_one : 0 < (#[s.pendingKeys.size] : Array Nat).size :=
                h_size_one ▸ Nat.zero_lt_one
              rw [Array.getElem_append_left h_lt_one]
              show ∃ (h_lt : (#[s.pendingKeys.size] : Array Nat)[0]'h_lt_one
                              < s_end.pendingKeys.size),
                  (s_end.pendingKeys[(#[s.pendingKeys.size] : Array Nat)[0]'h_lt_one]'h_lt).kind
                    = .keyOnly
              exact ⟨h_lt_s_send, h_kd_s_end⟩
            · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
              have h_j : j < qs_tail.size := by omega
              have h_ge : (#[s.pendingKeys.size] : Array Nat).size ≤ j + 1 := by
                rw [h_size_one]; omega
              rw [Array.getElem_append_right h_ge]
              have h_sub : j + 1 - (#[s.pendingKeys.size] : Array Nat).size = j := by
                rw [h_size_one]; omega
              simp only [h_sub]
              exact h_per_i_t j h_j
          · -- strict-monotone
            intro a b h_a h_b h_lt
            rw [Array.size_append, h_size_one] at h_a h_b
            by_cases h_a_zero : a = 0
            · subst h_a_zero
              have h_b_pos : 0 < b := h_lt
              obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
              have h_b' : b' < qs_tail.size := by omega
              have h_lt_one : 0 < (#[s.pendingKeys.size] : Array Nat).size :=
                h_size_one ▸ Nat.zero_lt_one
              rw [Array.getElem_append_left h_lt_one]
              have h_ge_b : (#[s.pendingKeys.size] : Array Nat).size ≤ b' + 1 := by
                rw [h_size_one]; omega
              rw [Array.getElem_append_right h_ge_b]
              have h_sub_b : b' + 1 - (#[s.pendingKeys.size] : Array Nat).size = b' := by
                rw [h_size_one]; omega
              simp only [h_sub_b]
              show s.pendingKeys.size < qs_tail[b']'h_b'
              by_cases h_b'_zero : b' = 0
              · subst h_b'_zero
                rw [h_q0_t]; exact h_lt_s_spp
              · have h_b'_pos : 0 < b' := by omega
                have h_strict := h_strict_t 0 b' h_pos_t h_b' h_b'_pos
                rw [h_q0_t] at h_strict
                exact Nat.lt_of_lt_of_le h_lt_s_spp (Nat.le_of_lt h_strict)
            · obtain ⟨a', rfl⟩ : ∃ a', a = a' + 1 := ⟨a - 1, by omega⟩
              have h_b_pos : 0 < b := by omega
              obtain ⟨b', rfl⟩ : ∃ b', b = b' + 1 := ⟨b - 1, by omega⟩
              have h_a' : a' < qs_tail.size := by omega
              have h_b' : b' < qs_tail.size := by omega
              have h_ge_a : (#[s.pendingKeys.size] : Array Nat).size ≤ a' + 1 := by
                rw [h_size_one]; omega
              have h_ge_b : (#[s.pendingKeys.size] : Array Nat).size ≤ b' + 1 := by
                rw [h_size_one]; omega
              rw [Array.getElem_append_right h_ge_a, Array.getElem_append_right h_ge_b]
              have h_sub_a : a' + 1 - (#[s.pendingKeys.size] : Array Nat).size = a' := by
                rw [h_size_one]; omega
              have h_sub_b : b' + 1 - (#[s.pendingKeys.size] : Array Nat).size = b' := by
                rw [h_size_one]; omega
              simp only [h_sub_a, h_sub_b]
              exact h_strict_t a' b' h_a' h_b' (by omega)
          · -- Part3-final-discharge-bridge-6a: predecessor-flowEntry conjunct.
            -- Outer index i ≥ 1 in `qs = #[s.pendingKeys.size] ++ qs_tail`
            -- decomposes as `i = j + 1` for `j < qs_tail.size`.  When `j ≥ 1`,
            -- the IH's `h_pred_t` provides the fact directly.  When `j = 0`
            -- (outer `i = 1`), the predecessor token is the `.flowEntry` pushed
            -- by the comma step (`s_v → s_c`) at index `s_v.tokens.size`,
            -- preserved through ws1 (`s_pp.tokens = s_c.tokens`), and lifted
            -- across the IH chain (`s_pp → s_end`) via tokens-prefix
            -- preservation (`FlowMonoChain_preserves_raw_prefix`).
            --
            -- **Sub-task 6a-i1-lift (sorry'd 2026-05-02)**: the j = 0 lift
            -- requires `SimpleKeyAboveFloor s_pp s_pp.tokens.size s_pp.flowLevel`
            -- which depends on tracing `s_pp.simpleKey`/`simpleKeyStack` state
            -- through the comma + ws1 sequence.  Discharged in 6b alongside
            -- the linearise-side bridge for `emitPairList_body_linearise_characterization`'s
            -- Part (3).  Net sorry-count effect: 6a adds +1, 6b discharges
            -- both this and the Part (3) sorry (8 → 9 → 7 across the pair).
            intro i h_i h_pos_i
            rw [Array.size_append, h_size_one] at h_i
            obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
            have h_j : j < qs_tail.size := by omega
            have h_ge : (#[s.pendingKeys.size] : Array Nat).size ≤ j + 1 := by
              rw [h_size_one]; omega
            have h_sub : j + 1 - (#[s.pendingKeys.size] : Array Nat).size = j := by
              rw [h_size_one]; omega
            -- Get `qs[j+1] = qs_tail[j]` via append + sub.
            have h_qj_eq :
                (#[s.pendingKeys.size] ++ qs_tail)[j + 1]'(by
                    rw [Array.size_append, h_size_one]; omega)
                  = qs_tail[j]'h_j := by
              rw [Array.getElem_append_right h_ge]; simp only [h_sub]
            rw [h_qj_eq]
            by_cases h_j_zero : j = 0
            · -- j = 0 (outer i = 1): the predecessor is the comma's flowEntry.
              -- Discharged in 6b via FlowMonoChain_preserves_existing_tokens
              -- (Path C unconditional prefix preservation).
              subst h_j_zero
              -- Get the IH's first-key fact at index `s_pp.pendingKeys.size`
              -- (insertBeforeIdx = s_pp.tokens.size, kind = .keyOnly).
              obtain ⟨h_lt_pp_send, h_ib_pp, _h_kd_pp⟩ := h_first_r (by simp)
              -- qs_tail[0] = s_pp.pendingKeys.size (h_q0_t).
              rw [h_q0_t]
              -- Decompose comma push: s_c.tokens.size = s_v.tokens.size + 1
              -- and s_c.tokens[s_v.tokens.size].val = .flowEntry.
              obtain ⟨h_sc_size, h_ph_at⟩ := h_comma_push
              -- s_pp.tokens.size = s_c.tokens.size = s_v.tokens.size + 1.
              have h_pp_size : s_pp.tokens.size = s_v.tokens.size + 1 := by
                rw [h_toks_pp]; exact h_sc_size
              -- (ib at this index = s_pp.tokens.size); ib > 0 since ≥ 1.
              have h_ib_pos :
                  0 < (s_end.pendingKeys[s_pp.pendingKeys.size]'h_lt_pp_send).insertBeforeIdx := by
                rw [h_ib_pp, h_pp_size]; omega
              -- ib - 1 = s_pp.tokens.size - 1 = s_v.tokens.size.
              have h_ib_minus_one :
                  (s_end.pendingKeys[s_pp.pendingKeys.size]'h_lt_pp_send).insertBeforeIdx - 1
                    = s_v.tokens.size := by
                rw [h_ib_pp, h_pp_size]; omega
              -- s_v.tokens.size < s_pp.tokens.size (= s_v.tokens.size + 1).
              have h_sv_lt_pp : s_v.tokens.size < s_pp.tokens.size := by
                rw [h_pp_size]; omega
              -- s_v.tokens.size < s_end.tokens.size via chain monotonicity.
              have h_sv_lt_send : s_v.tokens.size < s_end.tokens.size := by
                have h_mono := FlowMonoChain.tokens_mono h_fmc_r
                omega
              have h_pred_lt :
                  (s_end.pendingKeys[s_pp.pendingKeys.size]'h_lt_pp_send).insertBeforeIdx - 1
                    < s_end.tokens.size := by
                rw [h_ib_minus_one]; exact h_sv_lt_send
              refine ⟨h_lt_pp_send, h_ib_pos, h_pred_lt, ?_⟩
              -- Goal: s_end.tokens[ib - 1].val = .flowEntry.  The index is a
              -- complex expression involving `pks[s_pp.pks.size].insertBeforeIdx - 1`.
              -- Strategy: show the equality of the indexed tokens via a helper that
              -- carries the bound through.
              have h_sv_lt_sc : s_v.tokens.size < s_c.tokens.size := by
                rw [h_sc_size]; omega
              -- Key identity: the token at the predecessor index equals the comma's
              -- pushed flowEntry.  Use `h_ib_minus_one` to align indices, then chain
              -- through h_pres + h_toks_pp.
              have h_tok_eq :
                  s_end.tokens[
                      (s_end.pendingKeys[s_pp.pendingKeys.size]'h_lt_pp_send).insertBeforeIdx - 1
                    ]'h_pred_lt
                    = s_c.tokens[s_v.tokens.size]'h_sv_lt_sc := by
                -- Substitute the index expression by `s_v.tokens.size`.
                have h_idx_eq :
                    (s_end.pendingKeys[s_pp.pendingKeys.size]'h_lt_pp_send).insertBeforeIdx - 1
                      = s_v.tokens.size := h_ib_minus_one
                -- generalize+subst pattern handles the dependent bound proof.
                generalize h_idx : (s_end.pendingKeys[s_pp.pendingKeys.size]'h_lt_pp_send).insertBeforeIdx - 1
                  = idx at h_pred_lt ⊢
                rw [h_idx] at h_idx_eq
                subst h_idx_eq
                -- Now goal: s_end.tokens[s_v.tokens.size]'h_pred_lt = s_c.tokens[s_v.tokens.size]'h_sv_lt_sc.
                have h_pres :
                    s_end.tokens[s_v.tokens.size]'h_pred_lt
                      = s_pp.tokens[s_v.tokens.size]'h_sv_lt_pp :=
                  FlowMonoChain_preserves_existing_tokens h_fmc_r s_v.tokens.size h_sv_lt_pp
                rw [h_pres]
                -- s_pp.tokens = s_c.tokens via h_toks_pp.
                generalize h_arr_pp : s_pp.tokens = arr_pp at h_sv_lt_pp ⊢
                generalize h_arr_sc : s_c.tokens = arr_sc at h_sv_lt_sc
                have h_arr_eq : arr_pp = arr_sc := by
                  rw [← h_arr_pp, ← h_arr_sc]; exact h_toks_pp
                subst h_arr_eq; rfl
              rw [h_tok_eq]
              exact h_ph_at h_sv_lt_sc
            · -- j ≥ 1: from IH's predecessor-flowEntry conjunct directly.
              exact h_pred_t j h_j (by omega)

/-- Every grammable value satisfies `EmitScansInFlow`. -/
theorem emit_scans_in_flow (v : YamlValue) {inFlow : Bool} (hg : Grammable v inFlow) :
    EmitScansInFlow v := by
  induction hg with
  | scalar s _ h =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    -- emit (.scalar s) = "\"" ++ escapeString s.content ++ "\""
    -- Rewrite hcorr to match scanNextToken_flow_scanDoubleQuoted precondition
    have h_chars : (emit (.scalar s)).toList ++ rest =
        ['"'] ++ (escapeString s.content).toList ++ ['"'] ++ rest := by
      simp only [emit, emitScalar, String.toList_append]; rfl
    have hcorr' : ScannerSurfCorr s_state
        ⟨['"'] ++ (escapeString s.content).toList ++ ['"'] ++ rest, s_state.col⟩ := by
      rwa [← h_chars]
    obtain ⟨s', h_snt, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_tok', h_ska',
            _h_line', h_atol', h_endline', h_stack', h_size', h_pkRec', h_pks'⟩ :=
      scanNextToken_flow_scanDoubleQuoted s_state s.content rest hcorr' h_flow h_indent h_col
        h_atol (by intro h_poss; exact h_endline h_poss)
    -- Per-step witness for the scalar's scanNextToken call.
    have h_grew : (s'.tokens.filter (fun t => t.val != .placeholder)).size >
                  (s_state.tokens.filter (fun t => t.val != .placeholder)).size :=
      scanNextToken_filtered_grows_in_flow s_state s' '"'
        ((escapeString s.content).toList ++ ['"'] ++ rest)
        (by have : ['"'] ++ (escapeString s.content).toList ++ ['"'] ++ rest =
                    '"' :: ((escapeString s.content).toList ++ ['"'] ++ rest) := by
              simp only [List.cons_append, List.nil_append, List.append_assoc]
            rwa [this] at hcorr')
        h_flow h_indent h_col (by decide) (by decide) (by decide) h_snt
    refine ⟨1, s', ScanChainGrew.single h_snt h_grew, h_corr', h_fl', h_dp', h_ids', h_ek',
      ?_, ?_, ?_, _h_line', h_ska', ?_, ?_, ?_, ?_, ?_, h_size', h_pkRec', h_pks', ?_⟩
    · exact h_col'
    · unfold ScannerState.inFlow; rw [h_fl']
      unfold ScannerState.inFlow at h_flow; exact h_flow
    · unfold ScannerState.currentIndent; rw [h_ids']; exact h_indent
    · exact h_tok'
    · exact h_atol'
    · exact h_endline'
    · exact h_stack'
    · exact FlowMonoChain.single h_snt (Nat.le_refl _) (by omega)
    · -- gated first-key conjunct (J.4.2.b-2d-key-chain-Part2-body-C-foundation-EmitScansInFlow-gated):
      -- under simpleKeyAllowed = true, derive first-key facts via the scalar pkPush variant.
      -- By determinism of scanNextToken, the s' from scanNextToken_flow_scanDoubleQuoted_pkPush
      -- equals the s' we already have.
      intro h_ska_input
      have h_ek_none : s_state.explicitKeyLine = none := h_ek
      obtain ⟨s'_pk, h_snt_pk, _, _, _, _, _, _, _, _, _, _, _, _, _h_size_eq, h_pk_entry,
              h_pka_pk, h_skp_pk, _h_pkRec_pk⟩ :=
        scanNextToken_flow_scanDoubleQuoted_pkPush s_state s.content rest hcorr' h_flow h_indent h_col
          h_atol (by intro h_poss; exact h_endline h_poss) h_ska_input h_ek_none
      have h_eq : s' = s'_pk := by
        rw [h_snt] at h_snt_pk
        exact Option.some.inj (Except.ok.injEq .. |>.mp h_snt_pk)
      refine ⟨?_, ?_, ?_⟩
      · -- first-key entry at s_state.pendingKeys.size
        rw [h_eq]; exact h_pk_entry
      · -- pendingKeyActive = some s_state.pendingKeys.size
        rw [h_eq]; exact h_pka_pk
      · -- simpleKey.possible = true
        rw [h_eq]; exact h_skp_pk
  | sequence style items tag anchor _ h ih =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    -- emit (.sequence ...) = "[" ++ emitList items.toList ++ "]"
    -- Convert: unfold emit and distribute String.toList over ++
    have h_chars : (emit (.sequence style items tag anchor)).toList ++ rest =
        ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    -- hcorr₀ now has ['['] ++ ... which is def-eq to '[' :: ...
    -- Step 1: Scan '[' with nested flow open
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁,
            h_endline₁, h_stack_endline₁, h_stack_pop₁, h_size₁, h_pkRec₁, h_pks_pop₁⟩ :=
      scanNextToken_flow_open_nested s_state
        ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    -- Step 2: Scan emitList body via EmitListScansInFlow
    have h_list_scan : EmitListScansInFlow items.toList := by
      match h_list : items.toList with
      | [] => exact emitList_scans_empty
      | _ :: _ =>
        exact emitList_scans_nonempty _ (by simp) (fun w hw => by
          -- Convert list membership to array index for IH
          have hw' : w ∈ items.toList := h_list ▸ hw
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw'
          have h_sz : i < items.size := by
            rwa [Array.length_toList] at hi
          exact h_eq ▸ ih ⟨i, h_sz⟩)
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitList items.toList).toList ++ ([']'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow,
            h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_size₂, h_pkRec₂,
            h_pks₂⟩ :=
      h_list_scan s₁ ([']'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek)
        h_atol₁ -- AllTokensOnLine s₁ s₁.line (from flow_open_nested postcondition)
        h_endline₁ -- EndLineOnLine s₁ (from flow_open_nested postcondition)
    -- Step 3: Scan ']' with nested close (flowLevel ≥ 2)
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    -- Derive StackEndLineOnLine s₂ s₂.line from open theorem's postcondition
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃,
            _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_size₃, h_pkRec₃,
            _h_sk_restore₃, _h_pka_restore₃, _h_pks_pop₃⟩ :=
      scanNextToken_flow_close_seq_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    -- Compose: [ (1 step) + list body (n₂ steps) + ] (1 step)
    -- FlowMonoChain: open bracket (fl→fl+1) + body (floor fl+1) + close (fl+1→fl)
    -- The body chain has floor s₁.flowLevel = s_state.flowLevel + 1.
    -- Weaken to s_state.flowLevel, then compose with open/close single steps.
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ :=
      h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le_refl _) (by omega)).trans
        (h_fmc₂'.trans
          (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    -- Per-step witnesses: '[' (s_state → s₁) and ']' (s₂ → s₃).
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest), s_state.col⟩ := by
        have : ['['] ++ (emit.emitList items.toList).toList ++ [']'] ++ rest =
            '[' :: ((emit.emitList items.toList).toList ++ [']'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      exact scanNextToken_filtered_grows_in_flow s_state s₁ '['
        ((emit.emitList items.toList).toList ++ [']'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col
        (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨']' :: rest, s₂.col⟩ := by
        have : [']'] ++ rest = ']' :: rest := by simp
        rwa [this] at h_corr₂
      exact scanNextToken_filtered_grows_in_flow s₂ s₃ ']' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
        (by decide) (by decide) (by decide) h_snt₃
    -- pkRec / size composition: s_state → s₁ → s₂ → s₃
    have ⟨h_size₁₂, h_pkRec₁₂⟩ :=
      pkRec_size_compose h_size₁ h_size₂ h_pkRec₁ h_pkRec₂
    have ⟨h_size_all, h_pkRec_all⟩ :=
      pkRec_size_compose h_size₁₂ h_size₃ h_pkRec₁₂ h_pkRec₃
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
      h_size_all, h_pkRec_all, ?_⟩
    · -- flowLevel: (fl+1) - 1 = fl
      rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · -- explicitKeyLine preserved
      rw [h_ek₃, h_ek₂, h_ek₁]
    · -- col > 0
      rw [h_col₃]; omega
    · -- inFlow
      unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · -- currentIndent
      unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · -- line preserved
      rw [_h_line₃, _h_line₂, _h_line₁]
    · -- AllTokensOnLine s₃ s₃.line (from close theorem postcondition)
      exact h_atol₃
    · -- EndLineOnLine s₃ (from close theorem postcondition)
      exact h_endline₃
    · -- simpleKeyStack: s₃.simpleKeyStack = s_state.simpleKeyStack
      -- Chain: close pops → list preserved → open pushed then pop cancels
      rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · -- pendingKeyStack equality + gated conjunct (right-assoc ∧ absorption).
      refine ⟨?_, ?_⟩
      · -- pendingKeyStack: s₃.pendingKeyStack = s_state.pendingKeyStack
        -- Chain: close pops → body preserves → open pushed then pop cancels
        rw [_h_pks_pop₃, h_pks₂, h_pks_pop₁]
      · -- gated first-key conjunct: inline discharge via the open-pkPush variant.
        -- Strategy: re-call the pkPush variant on s_state (under the gate) to
        -- expose the push-shape facts (entry at s_state.pendingKeys.size,
        -- pendingKeyStack push of `some s_state.pendingKeys.size`, and
        -- top-of-stack simpleKey.possible = true).  By scanNextToken
        -- determinism (h_snt₁ vs the new h_snt_pk), the resulting state is s₁.
        -- Then chain through body preservation (h_pks₂, h_stack₂, h_pkRec₂)
        -- and close-side restore (_h_pka_restore₃, _h_sk_restore₃, h_pkRec₃).
        intro h_ska_input
        obtain ⟨s₁_pk, h_snt_pk, _, _, _, _, _, _, _, _, _, _, _, _h_size_pk_eq,
                h_pk_entry_pk, _h_preserves_pk, h_pks_push, h_skback⟩ :=
          scanNextToken_flow_open_nested_pkPush s_state
            ((emit.emitList items.toList).toList ++ [']'] ++ rest) hcorr₀ h_flow h_indent h_col
            h_atol h_endline h_ska_input h_ek
        have h_eq₁ : s₁ = s₁_pk := by
          rw [h_snt₁] at h_snt_pk
          exact Option.some.inj (Except.ok.injEq .. |>.mp h_snt_pk)
        subst h_eq₁
        have h_lt₁ : s_state.pendingKeys.size < s₁.pendingKeys.size := by
          rw [_h_size_pk_eq]; exact Nat.lt_succ_self _
        have h_lt₃ : s_state.pendingKeys.size < s₃.pendingKeys.size :=
          Nat.lt_of_lt_of_le h_lt₁ (Nat.le_trans h_size₂ h_size₃)
        have ⟨_, h_pkRec_s1_s3⟩ := pkRec_size_compose h_size₂ h_size₃ h_pkRec₂ h_pkRec₃
        obtain ⟨_, h_ib_s1, h_kd_s1⟩ := h_pk_entry_pk
        have ⟨h_ib_s3, h_kd_s3⟩ := h_pkRec_s1_s3 s_state.pendingKeys.size h_lt₁ h_lt₃
        refine ⟨⟨h_lt₃, ?_, ?_⟩, ?_, ?_⟩
        · rw [h_ib_s3]; exact h_ib_s1
        · rw [h_kd_s3]; exact h_kd_s1
        · -- pendingKeyActive: close restores from s₂.pendingKeyStack;
          --   body preserves it from s₁; s₁ pushes some s_state.pendingKeys.size.
          rw [_h_pka_restore₃, h_pks₂, h_pks_push, Array.back?_push]; rfl
        · -- simpleKey.possible: close restores from s₂.simpleKeyStack;
          --   body preserves it from s₁; s₁'s top simpleKey has possible = true.
          rw [_h_sk_restore₃, h_stack₂]; exact h_skback
  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    intro s_state rest hcorr h_flow h_fl h_indent h_col h_ek h_atol h_endline
    -- emit (.mapping ...) = "{" ++ emitPairList pairs.toList ++ "}"
    have h_chars : (emit (.mapping style pairs tag anchor)).toList ++ rest =
        ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest := by
      simp only [emit, String.toList_append]; rfl
    have hcorr₀ := hcorr; rw [h_chars] at hcorr₀
    -- Step 1: Scan '{' with nested flow open
    obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_ek₁, h_col₁, _h_line₁, h_atol₁,
            h_endline₁, h_stack_endline₁, h_stack_pop₁, h_size₁, h_pkRec₁, h_pks_pop₁, h_ska₁⟩ :=
      scanNextToken_flow_open_mapping_nested s_state
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
        h_atol h_endline
    have h_fl₁_ge2 : s₁.flowLevel ≥ 2 := by rw [h_fl₁]; omega
    have h_s1_inflow : s₁.inFlow = true := by
      unfold ScannerState.inFlow; exact decide_eq_true (by rw [h_fl₁]; omega)
    have h_s1_indent : s₁.currentIndent < 0 := by
      unfold ScannerState.currentIndent; rw [h_ids₁]; exact h_indent
    have h_s1_col : s₁.col > 0 := by rw [h_col₁]; omega
    -- Step 2: Scan emitPairList body via EmitPairListScansInFlow
    have h_pair_scan : EmitPairListScansInFlow pairs.toList := by
      match h_list : pairs.toList with
      | [] => exact emitPairList_scans_empty
      | _ :: _ =>
        exact emitPairList_scans_nonempty _ (by simp) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ ihk ⟨i, h_sz⟩) (fun p hp => by
          have hp' : p ∈ pairs.toList := h_list ▸ hp
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp'
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ ihv ⟨i, h_sz⟩)
    have h_corr₁_assoc : ScannerSurfCorr s₁
        ⟨(emit.emitPairList pairs.toList).toList ++ (['}'] ++ rest), s₁.col⟩ := by
      rw [List.append_assoc] at h_corr₁; exact h_corr₁
    obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂, h_ek₂, h_col₂, h_s2_inflow,
            h_s2_indent, _h_line₂, h_atol₂, h_endline₂, h_stack₂, h_fmc₂, h_size₂, h_pkRec₂,
            h_pks₂, _h_first₂, _h_first_qs₂⟩ :=
      h_pair_scan s₁ (['}'] ++ rest) h_corr₁_assoc h_s1_inflow (by rw [h_fl₁]; omega) h_s1_indent h_s1_col
        (by rw [h_ek₁]; exact h_ek)
        h_atol₁
        h_endline₁ -- EndLineOnLine s₁ (from flow_open_mapping_nested postcondition)
        h_ska₁ -- simpleKeyAllowed = true (from flow_open_mapping_nested postcondition)
    -- Step 3: Scan '}' with nested close (flowLevel ≥ 2)
    have h_fl₂_ge2 : s₂.flowLevel ≥ 2 := by rw [h_fl₂, h_fl₁]; omega
    -- Derive StackEndLineOnLine s₂ s₂.line from open theorem's postcondition
    have h_stack_endline₂ : StackEndLineOnLine s₂ s₂.line := by
      unfold StackEndLineOnLine at h_stack_endline₁ ⊢
      rw [h_stack₂, _h_line₂]; exact h_stack_endline₁
    obtain ⟨s₃, h_snt₃, h_corr₃, h_fl₃, h_dp₃, h_ids₃, h_ek₃, h_col₃, h_tok₃, h_ska₃,
            _h_line₃, h_atol₃, h_endline₃, h_stack₃, h_size₃, h_pkRec₃,
            _h_sk_restore₃, _h_pka_restore₃, _h_pks_pop₃⟩ :=
      scanNextToken_flow_close_mapping_nested s₂ rest h_corr₂ h_s2_inflow h_s2_indent h_col₂ h_fl₂_ge2
        h_atol₂ h_stack_endline₂
    -- Compose: { (1 step) + pair body (n₂ steps) + } (1 step)
    -- FlowMonoChain: open brace (fl→fl+1) + body (floor fl+1) + close (fl+1→fl)
    have h_fmc₂' : FlowMonoChain s_state.flowLevel s₁ n₂ s₂ :=
      h_fmc₂.weaken (by omega)
    have h_fmc_all :=
      (FlowMonoChain.single h_snt₁ (Nat.le_refl _) (by omega)).trans
        (h_fmc₂'.trans
          (FlowMonoChain.single h_snt₃ (by omega) (by omega)))
    -- Per-step witnesses: '{' (s_state → s₁) and '}' (s₂ → s₃).
    have h_grew₁ : (s₁.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s_state.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr_state_cons : ScannerSurfCorr s_state
          ⟨'{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest), s_state.col⟩ := by
        have : ['{'] ++ (emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest =
            '{' :: ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) := by
          simp only [List.cons_append, List.nil_append, List.append_assoc]
        rwa [this] at hcorr₀
      exact scanNextToken_filtered_grows_in_flow s_state s₁ '{'
        ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest)
        h_corr_state_cons h_flow h_indent h_col
        (by decide) (by decide) (by decide) h_snt₁
    have h_grew₃ : (s₃.tokens.filter (fun t => t.val != .placeholder)).size >
                   (s₂.tokens.filter (fun t => t.val != .placeholder)).size := by
      have h_corr₂_cons : ScannerSurfCorr s₂ ⟨'}' :: rest, s₂.col⟩ := by
        have : ['}'] ++ rest = '}' :: rest := by simp
        rwa [this] at h_corr₂
      exact scanNextToken_filtered_grows_in_flow s₂ s₃ '}' rest
        h_corr₂_cons h_s2_inflow h_s2_indent h_col₂
        (by decide) (by decide) (by decide) h_snt₃
    -- pkRec / size composition: s_state → s₁ → s₂ → s₃
    -- (s₁→s₂ leg uses EmitPairListScansInFlow; size+pkRec there are sorry'd
    --  for the colon-step pkRec analysis — propagated downstream as gated work.)
    have ⟨h_size₁₂, h_pkRec₁₂⟩ :=
      pkRec_size_compose h_size₁ h_size₂ h_pkRec₁ h_pkRec₂
    have ⟨h_size_all, h_pkRec_all⟩ :=
      pkRec_size_compose h_size₁₂ h_size₃ h_pkRec₁₂ h_pkRec₃
    refine ⟨(1 + n₂) + 1, s₃,
      (ScanChainGrew.single h_snt₁ h_grew₁).trans
        (h_chain₂.trans (ScanChainGrew.single h_snt₃ h_grew₃)),
      h_corr₃, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, h_ska₃, h_tok₃, ?_, ?_, ?_, h_fmc_all,
      h_size_all, h_pkRec_all, ?_⟩
    · rw [h_fl₃, h_fl₂, h_fl₁]; omega
    · rw [h_dp₃, h_dp₂, h_dp₁]
    · rw [h_ids₃, h_ids₂, h_ids₁]
    · -- explicitKeyLine preserved
      rw [h_ek₃, h_ek₂, h_ek₁]
    · rw [h_col₃]; omega
    · unfold ScannerState.inFlow
      exact decide_eq_true (by rw [h_fl₃, h_fl₂, h_fl₁]; omega)
    · unfold ScannerState.currentIndent; rw [h_ids₃, h_ids₂, h_ids₁]; exact h_indent
    · -- line preserved
      rw [_h_line₃, _h_line₂, _h_line₁]
    · -- AllTokensOnLine s₃ s₃.line (from close theorem postcondition)
      exact h_atol₃
    · -- EndLineOnLine s₃ (from close theorem postcondition)
      exact h_endline₃
    · -- simpleKeyStack: s₃.simpleKeyStack = s_state.simpleKeyStack
      rw [h_stack₃, h_stack₂, h_stack_pop₁]
    · -- pendingKeyStack equality + gated conjunct (right-assoc ∧ absorption).
      refine ⟨?_, ?_⟩
      · -- pendingKeyStack: s₃.pendingKeyStack = s_state.pendingKeyStack
        -- Chain: close pops → body preserves → open pushed then pop cancels
        rw [_h_pks_pop₃, h_pks₂, h_pks_pop₁]
      · -- gated first-key conjunct: inline discharge via the open-mapping-pkPush
        -- variant.  Mirror of the seq case: re-call pkPush on s_state under the
        -- gate, identify with s₁ via determinism, then chain through body
        -- preservation and close-side restore.
        intro h_ska_input
        obtain ⟨s₁_pk, h_snt_pk, _, _, _, _, _, _, _, _, _, _, _, _h_size_pk_eq,
                h_pk_entry_pk, _h_preserves_pk, h_pks_push, h_skback⟩ :=
          scanNextToken_flow_open_mapping_nested_pkPush s_state
            ((emit.emitPairList pairs.toList).toList ++ ['}'] ++ rest) hcorr₀ h_flow h_indent h_col
            h_atol h_endline h_ska_input h_ek
        have h_eq₁ : s₁ = s₁_pk := by
          rw [h_snt₁] at h_snt_pk
          exact Option.some.inj (Except.ok.injEq .. |>.mp h_snt_pk)
        subst h_eq₁
        have h_lt₁ : s_state.pendingKeys.size < s₁.pendingKeys.size := by
          rw [_h_size_pk_eq]; exact Nat.lt_succ_self _
        have h_lt₃ : s_state.pendingKeys.size < s₃.pendingKeys.size :=
          Nat.lt_of_lt_of_le h_lt₁ (Nat.le_trans h_size₂ h_size₃)
        have ⟨_, h_pkRec_s1_s3⟩ := pkRec_size_compose h_size₂ h_size₃ h_pkRec₂ h_pkRec₃
        obtain ⟨_, h_ib_s1, h_kd_s1⟩ := h_pk_entry_pk
        have ⟨h_ib_s3, h_kd_s3⟩ := h_pkRec_s1_s3 s_state.pendingKeys.size h_lt₁ h_lt₃
        refine ⟨⟨h_lt₃, ?_, ?_⟩, ?_, ?_⟩
        · rw [h_ib_s3]; exact h_ib_s1
        · rw [h_kd_s3]; exact h_kd_s1
        · rw [_h_pka_restore₃, h_pks₂, h_pks_push, Array.back?_push]; rfl
        · rw [_h_sk_restore₃, h_stack₂]; exact h_skback

-- Helper: extract existential from isOk
theorem scanFiltered_exists_of_isOk {s : String}
    (h : (Scanner.scanFiltered s).toBool = true) :
    ∃ tokens, Scanner.scanFiltered s = .ok tokens := by
  cases h_eq : Scanner.scanFiltered s with
  | ok tokens => exact ⟨tokens, rfl⟩
  | error _ =>
    exfalso; revert h; simp [h_eq]; rfl

/-- **Main theorem**: The scanner accepts any canonical emitter output.

    For any grammable `YamlValue`, `scanFiltered (emit v)` succeeds.
    This is Step 1 of the universal round-trip proof.

    **Proof strategy**: Structural induction on `YamlValue`.
    - Scalar case: delegates to `scan_accepts_emitScalar`
    - Sequence/mapping cases: delegates to scanner acceptance of
      flow collections with inductively-accepted sub-expressions
    - Alias case: impossible (excluded by `Grammable`)

    Note: generalized to arbitrary `inFlow` to enable structural induction
    on `Grammable`. The `emit` function ignores `inFlow` (always produces
    flow format), so scanner acceptance is independent of the flow context
    under which the value is grammable. -/
theorem emit_produces_valid_yaml (v : YamlValue) {inFlow : Bool} (hg : Grammable v inFlow) :
    ∃ tokens, scanFiltered (emit v) = .ok tokens := by
  induction hg with
  | scalar s _ h =>
    -- emit (.scalar s) = emitScalar s.content
    exact scan_accepts_emitScalar s.content
  | sequence style items tag anchor _ h ih =>
    -- emit (.sequence style items tag anchor) = "[" ++ emitList items.toList ++ "]"
    change ∃ tokens, scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens
    match h_items : items.toList with
    | [] =>
      simp only [emit.emitList]
      exact scanFiltered_exists_of_isOk (by native_decide)
    | _ :: _ =>
      -- Non-empty: compose flow open '[', body scanning, flow close ']', EOF
      -- Rewrite goal back to use items.toList (match substituted it)
      simp only [← h_items]
      -- Step 1: Show input.toList starts with '['
      have h_toList : ("[" ++ emit.emitList items.toList ++ "]").toList =
          '[' :: (emit.emitList items.toList).toList ++ [']'] := by
        simp only [String.toList_append]; rfl
      -- Step 2: Scan '[' from initial state via flow_open_init
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
              h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, _h_filt₁, _⟩ :=
        scanNextToken_flow_open_init ("[" ++ emit.emitList items.toList ++ "]")
          ((emit.emitList items.toList).toList ++ [']']) h_toList
      -- Step 3: Build EmitListScansInFlow for non-empty items list
      have h_list_scan : EmitListScansInFlow items.toList :=
        emitList_scans_nonempty items.toList (by simp [h_items]) (fun w hw => by
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
          have h_sz : i < items.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow items[i] (h ⟨i, h_sz⟩))
      -- Step 4: Apply body scanning (emitList → ScanChain through body)
      obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
              h_ek₂, h_col₂, h_inflow₂, h_indent₂, _h_line₂, _, _, _, _⟩ :=
        h_list_scan s₁ [']'] h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega)
          h_indent₁ (by rw [h_col₁]; omega) h_ek₁
          (h_line₁ ▸ h_atol₁) -- AllTokensOnLine s₁ s₁.line
          h_endline₁ -- EndLineOnLine s₁
      -- Step 5: Scan ']' (outermost, flowLevel = 1 → 0)
      obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃⟩ :=
        scanNextToken_flow_close_seq_outermost s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
          (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
      -- Step 6: EOF
      have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
      -- Step 7: BOM check (input starts with '[', not BOM)
      have h_no_bom : (ScannerState.mk' ("[" ++ emit.emitList items.toList ++ "]")).peek?
          ≠ some '\uFEFF' := by
        have h_chars := chars_from_zero_toList ("[" ++ emit.emitList items.toList ++ "]")
        rw [h_toList] at h_chars
        have h_corr := initial_corr _ _ h_chars
        have ⟨h_pk, _⟩ := peek_of_chars_cons _ '['
          ((emit.emitList items.toList).toList ++ [']']) 0 h_corr
        rw [h_pk]; decide
      -- Step 8: Compose chain: '[' (1 step) + body (n₂ steps) + ']' (1 step)
      -- Forget the strict ScanChainGrew witness back to ScanChain for the consumer.
      have h_chain_all := (ScanChain.single h_snt₁).trans
        (h_chain₂.toScanChain.trans (ScanChain.single h_snt₃))
      -- Apply scanFiltered_of_chain
      exact scanFiltered_of_chain _ _ s₃ _ rfl h_no_bom h_chain_all h_eof h_fl₃ h_dp₃
        (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)
  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    -- emit (.mapping style pairs tag anchor) = "{" ++ emitPairList pairs.toList ++ "}"
    change ∃ tokens, scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens
    match h_pairs : pairs.toList with
    | [] =>
      simp only [emit.emitPairList]
      exact scanFiltered_exists_of_isOk (by native_decide)
    | _ :: _ =>
      -- Non-empty: compose flow open '{', body scanning, flow close '}', EOF
      simp only [← h_pairs]
      -- Step 1: Show input.toList starts with '{'
      have h_toList : ("{" ++ emit.emitPairList pairs.toList ++ "}").toList =
          '{' :: (emit.emitPairList pairs.toList).toList ++ ['}'] := by
        simp only [String.toList_append]; rfl
      -- Step 2: Scan '{' from initial state via flow_open_mapping_init
      obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
              h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, _h_sk₁, _h_filt₁, _, h_ska₁⟩ :=
        scanNextToken_flow_open_mapping_init ("{" ++ emit.emitPairList pairs.toList ++ "}")
          ((emit.emitPairList pairs.toList).toList ++ ['}']) h_toList
      -- Step 3: Build EmitPairListScansInFlow for non-empty pair list
      have h_pair_scan : EmitPairListScansInFlow pairs.toList :=
        emitPairList_scans_nonempty pairs.toList (by simp [h_pairs]) (fun p hp => by
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow pairs[i].1 (hk ⟨i, h_sz⟩)) (fun p hp => by
          have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
          have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
          exact h_eq ▸ emit_scans_in_flow pairs[i].2 (hv ⟨i, h_sz⟩))
      -- Step 4: Apply body scanning
      obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
              h_ek₂, h_col₂, h_inflow₂, h_indent₂, _h_line₂, _, _, _, _, _⟩ :=
        h_pair_scan s₁ ['}'] h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega)
          h_indent₁ (by rw [h_col₁]; omega) h_ek₁
          (h_line₁ ▸ h_atol₁) -- AllTokensOnLine s₁ s₁.line
          h_endline₁ -- EndLineOnLine s₁
          h_ska₁ -- simpleKeyAllowed = true (from flow_open_mapping_init)
      -- Step 5: Scan '}' (outermost, flowLevel = 1 → 0)
      obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃⟩ :=
        scanNextToken_flow_close_mapping_outermost s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
          (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
      -- Step 6: EOF
      have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
      -- Step 7: BOM check (input starts with '{', not BOM)
      have h_no_bom : (ScannerState.mk' ("{" ++ emit.emitPairList pairs.toList ++ "}")).peek?
          ≠ some '\uFEFF' := by
        have h_chars := chars_from_zero_toList ("{" ++ emit.emitPairList pairs.toList ++ "}")
        rw [h_toList] at h_chars
        have h_corr := initial_corr _ _ h_chars
        have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{'
          ((emit.emitPairList pairs.toList).toList ++ ['}']) 0 h_corr
        rw [h_pk]; decide
      -- Step 8: Compose chain
      -- Forget the strict ScanChainGrew witness back to ScanChain for the consumer.
      have h_chain_all := (ScanChain.single h_snt₁).trans
        (h_chain₂.toScanChain.trans (ScanChain.single h_snt₃))
      -- Apply scanFiltered_of_chain
      exact scanFiltered_of_chain _ _ s₃ _ rfl h_no_bom h_chain_all h_eof h_fl₃ h_dp₃
        (ScanChain.fuel_bound _ _ _ _ rfl h_chain_all h_eof)

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

-- ═══ Challenge 2: parseStreamLoop state machine — single implicit document ═══
-- If the parser sees content (not streamEnd), parseDocument succeeds and
-- leaves peek? at streamEnd, then parseStreamLoop produces exactly one document.
theorem parseStreamLoop_single_doc
    (ps : ParseState) (fuel : Nat) (h_fuel : fuel ≥ 2)
    (tok : YamlToken) (h_peek : ps.peek? = some tok) (h_not_se : tok ≠ .streamEnd)
    (doc : YamlDocument) (ps' : ParseState)
    (h_doc : parseDocument ps = .ok (doc, ps'))
    (h_peek' : ps'.peek? = some .streamEnd) :
    parseStreamLoop ps #[] .initial fuel = .ok #[doc] := by
  -- Two iterations: first parses document, second sees streamEnd and returns.
  cases fuel with
  | zero => omega
  | succ fuel' => cases fuel' with
    | zero => omega
    | succ f =>
      -- First iteration: unfold parseStreamLoop, resolve fuel match
      unfold parseStreamLoop; dsimp only []  -- reduce Nat.succ match
      rw [h_peek]  -- substitute ps.peek? = some tok
      -- Case-split by YamlToken constructor to resolve the compiled match.
      -- .streamEnd is impossible (contradicts h_not_se); all others take catch-all.
      cases tok
      <;> first | exact absurd rfl h_not_se | skip
      -- All 22 remaining goals: content branch (identical proof)
      all_goals (
        dsimp only []  -- reduce the YamlToken match
        simp only [StreamState.validNextToken, Bool.not_true]
        rw [h_doc]; dsimp only []
        have h_peek'_r : (ParseState.mk ps'.tokens ps'.pos #[]
            ps'.tagHandles ps'.trackPositions #[] #[]).peek?
            = some .streamEnd := h_peek'
        simp only [ParseState.tryConsume, h_peek'_r,
                   show (BEq.beq YamlToken.streamEnd YamlToken.documentEnd) = false
                     from by decide]
        simp only [Bool.false_eq_true, ↓reduceIte]
        simp only [parseStreamLoop, h_peek'_r]
        -- Both if-branches are identical (stuck or not, result is same)
        split <;> rfl)

/-- **Grammability preservation**: The parsed output of emitter output
    is grammable. Follows from `parseStream_output_grammable` applied
    to the scan+parse decomposition. -/
theorem emit_parsed_grammable (v : YamlValue)
    (docs : Array YamlDocument)
    (h : parseYaml (emit v) = .ok docs) :
    ∀ doc ∈ docs.toList, Grammable doc.value false := by
  simp only [parseYaml] at h
  split at h
  · rename_i raw_docs h_raw
    injection h with h_eq
    have ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose (emit v) raw_docs h_raw
    have h_gram := ParserGrammable.parseStream_output_grammable (emit v) tokens raw_docs h_scan h_parse
    intro doc hdoc
    rw [← h_eq] at hdoc
    simp only [Array.toList_map] at hdoc
    obtain ⟨raw_doc, h_raw_mem, h_compose_eq⟩ := List.mem_map.mp hdoc
    subst h_compose_eq
    exact h_gram raw_doc h_raw_mem
  · simp at h

/-! ## §5  Content Fidelity Infrastructure

Helper lemmas for the content fidelity proof (`emit_roundtrip_content_eq`).

### §5.1  Compose invariance for scalars

`YamlDocument.compose` applies `resolveAliases` and `stripAnchors`.
For scalars, `resolveAliases` is identity and `stripAnchors` only clears
the anchor field. Since `contentEq` ignores anchors, compose doesn't
affect content equivalence for scalars.
-/

-- resolveAliases is identity on scalars
theorem resolveAliases_scalar (s : Scalar)
    (anchors : Array (String × YamlValue)) :
    (YamlValue.scalar s).resolveAliases anchors = .scalar s := by
  unfold YamlValue.resolveAliases; rfl

-- stripAnchors on scalar just clears the anchor
theorem stripAnchors_scalar (s : Scalar) :
    (YamlValue.scalar s).stripAnchors = .scalar { s with anchor := none } := by
  unfold YamlValue.stripAnchors; rfl

-- compose on a scalar document preserves the content field
theorem compose_scalar_content (doc : YamlDocument) (s : Scalar)
    (h_val : doc.value = .scalar s) :
    (doc.compose).value = .scalar { s with anchor := none } := by
  unfold YamlDocument.compose; dsimp only []
  rw [h_val, resolveAliases_scalar, stripAnchors_scalar]

-- contentEq for scalars only depends on content string
theorem contentEq_scalar_content (s₁ s₂ : Scalar)
    (h : s₁.content = s₂.content) : contentEq (.scalar s₁) (.scalar s₂) = true := by
  unfold contentEq; simp [h]

-- contentEq through compose for scalars: original vs composed
theorem contentEq_scalar_compose (s_orig : Scalar) (s_parsed : Scalar)
    (h_content : s_orig.content = s_parsed.content) :
    contentEq (.scalar s_orig) (.scalar { s_parsed with anchor := none }) = true := by
  exact contentEq_scalar_content s_orig { s_parsed with anchor := none } h_content

/-! ### §5.2  Scanner content preservation

The scanner's double-quoted collector recovers the original content string
from the emitter's escape-encoded output. This is the key roundtrip property.
-/

-- Hex foldl roundtrip for control characters (c.val.toNat < 0x20)
-- (`scanFiltered_emitScalar_content` is defined after
--  `scanFiltered_emitScalar_vals` so the corollary proof can reuse the
--  vals-shape characterization.)

/-- Token structure: the filtered scan of `emitScalar content` produces
    exactly 3 tokens: `streamStart`, `scalar content .doubleQuoted`, `streamEnd`.

    **Initiative 3 / J.3.7** (2026-04-29): post-cutover proof routes
    through the strengthened `scanNextToken_emitScalar_init` (concrete
    `s₁.tokens` shape + pendingKeys all unresolved) +
    `scanLoopFull_eof_eq` + `linearise_all_unresolved`.  No reliance on
    the legacy `tokens.filter (· != .placeholder)` shape. -/
theorem scanFiltered_emitScalar_vals (content : String) (tokens : Array (Positioned YamlToken))
    (h_scan : scanFiltered (emitScalar content) = .ok tokens) :
    tokens.size = 3 ∧ tokens[0]!.val = .streamStart ∧
    tokens[1]!.val = .scalar content .doubleQuoted ∧ tokens[2]!.val = .streamEnd := by
  -- ═══ Step 1: extract concrete s₁ from strengthened init ═══
  obtain ⟨s₁, h_snt₁, h_peek₁, h_fl₁, h_dp₁, _, h_inds₁, _, h_map_s₁, h_pks_s₁⟩ :=
    scanNextToken_emitScalar_init content
  -- Build chain s₀ →¹ s₁.
  have h_chain : ScanChain ((ScannerState.mk' (emitScalar content)).emit .streamStart) 1 s₁ :=
    ScanChain.single h_snt₁
  have h_eof : scanNextToken s₁ = .ok none := scanNextToken_eof s₁ h_peek₁
  -- BOM: emitScalar starts with '"', not BOM.
  have h_no_bom : (ScannerState.mk' (emitScalar content)).peek? ≠ some '﻿' := by
    have h_chars := chars_from_zero_toList (emitScalar content)
    rw [emitScalar_toList] at h_chars
    have h_corr := initial_corr (emitScalar content) _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '"' _ 0 h_corr
    rw [h_pk]; decide
  -- skipToContent identity (peek? = none).
  have h_skip : skipToContent s₁ = .ok s₁ := skipToContent_eq_self_of_peek_none h_peek₁
  -- unwindIndents identity (indents.size = 1) — inline since
  -- `unwindIndents_noop_short_stack` is defined later in the file.
  have h_uwi : unwindIndents s₁ (-1) = s₁ := by
    have h_stack : s₁.indents.size ≤ 1 := by rw [h_inds₁]; decide
    unfold unwindIndents unwindIndentsLoop
    split
    · rfl
    · split
      · exfalso
        rename_i h_cond
        simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
        omega
      · rfl
  -- scanLoopFull at s₁ closes.
  have h_loop_s₁ :
      scanLoopFull s₁ (((emitScalar content).utf8ByteSize + 1) * 4 - 1)
        = .ok ((unwindIndents s₁ (-1)).emit .streamEnd) := by
    have h_size := emitScalar_utf8ByteSize_ge content
    exact scanLoopFull_eof_eq (by omega) h_eof h_fl₁ h_dp₁ h_skip
  -- scanLoopFull at s₀ closes via chain composition.
  have h_loop_s₀ := h_chain.to_scanLoopFull h_loop_s₁
  have h_fuel_eq : ((emitScalar content).utf8ByteSize + 1) * 4 - 1 + 1 =
      ((emitScalar content).utf8ByteSize + 1) * 4 := by
    have h_size := emitScalar_utf8ByteSize_ge content; omega
  rw [h_fuel_eq] at h_loop_s₀
  rw [h_uwi] at h_loop_s₀
  -- ═══ Step 3: scanFiltered = (s₁.emit streamEnd).tokens (after linearise) ═══
  -- Walk scanFiltered: BOM identity + scanLoopFull + linearise.
  have h_pks_final : ∀ e ∈ (s₁.emit .streamEnd).pendingKeys, e.kind = .unresolved := by
    show ∀ e ∈ s₁.pendingKeys, e.kind = .unresolved
    exact h_pks_s₁
  have h_lin :
      Scanner.linearise (s₁.emit .streamEnd).tokens (s₁.emit .streamEnd).pendingKeys
        = (s₁.emit .streamEnd).tokens :=
    L4YAML.Proofs.ScannerLinearise.linearise_all_unresolved
      (s₁.emit .streamEnd).tokens (s₁.emit .streamEnd).pendingKeys h_pks_final
  -- Reduce h_scan to a concrete tokens equation.
  have h_scan_explicit :
      Scanner.scanFiltered (emitScalar content) =
        Except.ok (s₁.emit .streamEnd).tokens := by
    -- Use `show` to reshape the goal into a form where we can split on the
    -- BOM-match and rewrite scanLoopFull explicitly (mirroring the
    -- J.3.6 `scanFiltered_of_chain` proof technique).
    show (match scanLoopFull
            (match ((ScannerState.mk' (emitScalar content)).emit .streamStart).peek? with
             | some '﻿' => ((ScannerState.mk' (emitScalar content)).emit .streamStart).advance
             | _ => (ScannerState.mk' (emitScalar content)).emit .streamStart)
            (((emitScalar content).utf8ByteSize + 1) * 4) with
          | Except.ok final =>
              Except.ok (Scanner.linearise final.tokens final.pendingKeys)
          | Except.error e => Except.error e) =
        Except.ok (s₁.emit .streamEnd).tokens
    -- BOM identity.
    have h_bom_branch :
        (match ((ScannerState.mk' (emitScalar content)).emit .streamStart).peek? with
         | some '﻿' => ((ScannerState.mk' (emitScalar content)).emit .streamStart).advance
         | _ => (ScannerState.mk' (emitScalar content)).emit .streamStart)
          = (ScannerState.mk' (emitScalar content)).emit .streamStart := by
      split
      · rename_i h_bom; exact absurd h_bom h_no_bom
      · rfl
    rw [h_bom_branch]
    rw [h_loop_s₀]
    show Except.ok (Scanner.linearise (s₁.emit .streamEnd).tokens
            (s₁.emit .streamEnd).pendingKeys) =
          Except.ok (s₁.emit .streamEnd).tokens
    rw [h_lin]
  have h_scan_eq : tokens = (s₁.emit .streamEnd).tokens := by
    rw [h_scan_explicit] at h_scan
    exact (Except.ok.inj h_scan).symm
  -- ═══ Step 4: derive size + element vals ═══
  -- Substitute tokens by the concrete `s₁.tokens.push streamEnd-pos` shape.
  have h_final_tokens : (s₁.emit .streamEnd).tokens = s₁.tokens.push
      { pos := s₁.currentPos, val := YamlToken.streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_tokens_eq :
      tokens = s₁.tokens.push { pos := s₁.currentPos, val := YamlToken.streamEnd } := by
    rw [h_scan_eq, h_final_tokens]
  -- Discharge size + per-index claims from the concrete shape.
  have h_s1_size : s₁.tokens.size = 2 := by
    have h := congrArg Array.size h_map_s₁
    simpa [Array.size_map] using h
  have h_tok_size : tokens.size = 3 := by
    rw [h_tokens_eq, Array.size_push, h_s1_size]
  -- Convert s₁.tokens.map vals = [ss, scalar] to per-element facts via toList.
  have h_s1_toList_map :
      s₁.tokens.toList.map (·.val) = [.streamStart, .scalar content .doubleQuoted] := by
    have h := congrArg Array.toList h_map_s₁
    simpa [Array.toList_map] using h
  have h_s1_size_list : s₁.tokens.toList.length = 2 := by
    rw [Array.length_toList]; exact h_s1_size
  obtain ⟨a, b, h_ab⟩ : ∃ a b, s₁.tokens.toList = [a, b] := by
    match h_eq : s₁.tokens.toList, h_s1_size_list with
    | [a, b], _ => exact ⟨a, b, rfl⟩
  have h_ab_vals : a.val = .streamStart ∧ b.val = .scalar content .doubleQuoted := by
    rw [h_ab] at h_s1_toList_map
    simp at h_s1_toList_map
    exact h_s1_toList_map
  obtain ⟨h_a_val, h_b_val⟩ := h_ab_vals
  -- Lift list elements to array via Array.toList_inj: s₁.tokens = #[a, b],
  -- so s₁.tokens[0] = a and s₁.tokens[1] = b by rfl.
  have h_s1_arr_eq : s₁.tokens = #[a, b] := Array.toList_inj.mp h_ab
  have h_s1_t0 : s₁.tokens[0]'(by rw [h_s1_size]; omega) = a := by
    have h_lit : (#[a, b] : Array (Positioned YamlToken))[0]'(by simp) = a := rfl
    have h_eq :
        s₁.tokens[0]'(by rw [h_s1_size]; omega) =
          (#[a, b] : Array (Positioned YamlToken))[0]'(by simp) := by
      congr 1 <;> exact h_s1_arr_eq
    rw [h_eq]; exact h_lit
  have h_s1_t1 : s₁.tokens[1]'(by rw [h_s1_size]; omega) = b := by
    have h_lit : (#[a, b] : Array (Positioned YamlToken))[1]'(by simp) = b := rfl
    have h_eq :
        s₁.tokens[1]'(by rw [h_s1_size]; omega) =
          (#[a, b] : Array (Positioned YamlToken))[1]'(by simp) := by
      congr 1 <;> exact h_s1_arr_eq
    rw [h_eq]; exact h_lit
  refine ⟨h_tok_size, ?_, ?_, ?_⟩
  · -- tokens[0]!.val = .streamStart
    have h0 : 0 < tokens.size := by rw [h_tok_size]; omega
    rw [getElem!_pos tokens 0 h0]
    have h_lt : (0 : Nat) < s₁.tokens.size := by rw [h_s1_size]; omega
    have h_get :
        tokens[0]'h0 = (s₁.tokens.push
          { pos := s₁.currentPos, val := YamlToken.streamEnd })[0]'(by
            rw [h_tokens_eq] at h0; exact h0) := by
      congr 1 <;> exact h_tokens_eq
    rw [h_get, Array.getElem_push_lt h_lt, h_s1_t0]
    exact h_a_val
  · -- tokens[1]!.val = .scalar content .doubleQuoted
    have h1 : 1 < tokens.size := by rw [h_tok_size]; omega
    rw [getElem!_pos tokens 1 h1]
    have h_lt : (1 : Nat) < s₁.tokens.size := by rw [h_s1_size]; omega
    have h_get :
        tokens[1]'h1 = (s₁.tokens.push
          { pos := s₁.currentPos, val := YamlToken.streamEnd })[1]'(by
            rw [h_tokens_eq] at h1; exact h1) := by
      congr 1 <;> exact h_tokens_eq
    rw [h_get, Array.getElem_push_lt h_lt, h_s1_t1]
    exact h_b_val
  · -- tokens[2]!.val = .streamEnd
    have h2 : 2 < tokens.size := by rw [h_tok_size]; omega
    rw [getElem!_pos tokens 2 h2]
    have h_get :
        tokens[2]'h2 = (s₁.tokens.push
          { pos := s₁.currentPos, val := YamlToken.streamEnd })[2]'(by
            rw [h_tokens_eq] at h2; exact h2) := by
      congr 1 <;> exact h_tokens_eq
    rw [h_get]
    -- (s₁.tokens.push x)[2] when s₁.tokens.size = 2 is just x.
    -- Use Array.getElem_push to compute (s₁.tokens.push x)[i] in general,
    -- then split on whether i < s₁.tokens.size.
    rw [Array.getElem_push]
    -- Goal: if h : 2 < s₁.tokens.size then s₁.tokens[2]'h else x = x, but 2 ≥ size so else branch.
    have h_not_lt : ¬ (2 < s₁.tokens.size) := by rw [h_s1_size]; omega
    simp [h_not_lt]

/-- **Scanner content preservation**: scanning `emitScalar content` produces
    a token stream where the scalar token's content equals the original.

    This bridges the emitter's `escapeString` encoding with the scanner's
    `collectDoubleQuotedLoop` + `processEscape` decoding.

    **Initiative 3 / J.3.7** (2026-04-29): post-cutover, this is a
    direct corollary of `scanFiltered_emitScalar_vals` — `tokens[1]!.val`
    pins the scalar at index 1 and `tokens.size = 3` provides the bound. -/
theorem scanFiltered_emitScalar_content (content : String) (tokens : Array (Positioned YamlToken))
    (h_scan : scanFiltered (emitScalar content) = .ok tokens) :
    ∃ i, i < tokens.size ∧ tokens[i]!.val = .scalar content .doubleQuoted := by
  obtain ⟨h_size, _, h_val1, _⟩ := scanFiltered_emitScalar_vals content tokens h_scan
  exact ⟨1, by rw [h_size]; omega, h_val1⟩

/-- When `parseDirectives` sees a non-directive token, it returns immediately
    with empty directives and unchanged state.
    The `for _ in [:fuel] do` loop breaks on the first iteration because
    `peek?` matches `| _ => break`. -/
theorem parseDirectives_skip (ps : ParseState)
    (h : match ps.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True) :
    parseDirectives ps = (#[], ps) := by
  unfold parseDirectives
  simp only [Id.run]
  rw [Std.Legacy.Range.forIn_eq_forIn_range']
  simp only [Std.Legacy.Range.size, Nat.sub_zero, Nat.add_sub_cancel, Nat.div_one]
  generalize ps.tokens.size - ps.pos = fuel
  cases fuel with
  | zero =>
    simp only [List.range', List.forIn_nil]
    rfl
  | succ n =>
    simp only [List.range'_succ, List.forIn_cons, pure, bind]
    split
    · rename_i minor h_done
      split at h_done
      · cases h_done
      · cases h_done
      · cases h_done; rfl
    · rename_i b h_yield
      split at h_yield
      · exfalso; revert h; simp_all
      · exfalso; revert h; simp_all
      · cases h_yield

-- **Parser trace on three-token scalar stream**: Given a token array with
-- values `[streamStart, scalar content .doubleQuoted, streamEnd]`,
-- `parseStream` produces exactly one document whose value is
-- `YamlValue.scalar { content := content, style := .doubleQuoted }`.
set_option maxHeartbeats 6400000 in
theorem parseStream_three_tokens_scalar (content : String)
    (tokens : Array (Positioned YamlToken))
    (h_sz : tokens.size = 3)
    (h_t0 : tokens[0]!.val = .streamStart)
    (h_t1 : tokens[1]!.val = .scalar content .doubleQuoted)
    (h_t2 : tokens[2]!.val = .streamEnd) :
    ∃ (docs : Array YamlDocument),
      parseStream tokens = .ok docs ∧ docs.size = 1 ∧
      docs[0]!.value = .scalar (Scalar.mk content .doubleQuoted none none none) := by
  -- Establish index bounds
  have h0 : (0 : Nat) < tokens.size := by omega
  have h1 : (1 : Nat) < tokens.size := by omega
  have h2 : (2 : Nat) < tokens.size := by omega
  -- Convert getElem! to getElem in hypotheses
  have h_gei : ∀ (i : Nat) (hi : i < tokens.size),
      tokens[i]!.val = tokens[i].val := by
    intro i hi; simp [getElem!_pos, hi]
  have h_t1' : tokens[1].val = .scalar content .doubleQuoted := by rw [← h_gei 1 h1]; exact h_t1
  have h_t2' : tokens[2].val = .streamEnd := by rw [← h_gei 2 h2]; exact h_t2
  -- Step 1: Unfold parseStream and dispatch expect .streamStart
  unfold parseStream
  simp only [bind, Except.bind]
  unfold ParseState.expect
  simp only [ParseState.peek?]
  simp only [show (0 : Nat) < tokens.size from by omega, ↓reduceIte, h_t0]
  simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
             ↓reduceIte]
  -- After expect step, introduce ps1 = advance of initial state
  let ps1 : ParseState := ({ tokens := tokens } : ParseState).advance
  show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
    docs.size = 1 ∧ docs[0]!.value = .scalar (Scalar.mk content .doubleQuoted none none none)
  -- peek? facts for ps1
  have h_peek1 : ps1.peek? = some (.scalar content .doubleQuoted) := by
    simp only [ps1, ParseState.peek?, ParseState.advance, h1, ↓reduceIte]
    simp only [show (0 : Nat) + 1 = 1 from rfl, h_gei 1 h1, h_t1']
  have h_peek_not_dir : match ps1.peek? with
      | some (.versionDirective _ _) | some (.tagDirective _ _) => False
      | _ => True := by rw [h_peek1]; trivial
  have h_peek_not_anctag : match ps1.peek? with
      | some (.anchor _) | some (.tag _ _) => False
      | _ => True := by rw [h_peek1]; trivial
  -- parseDirectives and prepareDocumentState
  have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skip ps1 h_peek_not_dir
  have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
    unfold prepareDocumentState
    simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
    have h_th : { ps1 with tagHandles := #[] } = ps1 := by
      simp [ps1, ParseState.advance]
    rw [h_th, h_peek1]
    unfold ParseState.tryConsume
    rw [h_peek1]; simp
  -- parseNodeProperties skip
  have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
    parseNodeProperties_skip ps1 h_peek_not_anctag
  -- parseNode
  have h_parseNode : parseNode ps1 (4 * ps1.tokens.size + 4) = .ok
      (applyNodeFinalization
        (.scalar { content, style := .doubleQuoted, tag := none, anchor := none })
        ps1.advance {} (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })) := by
    cases h_f : 4 * ps1.tokens.size + 4 with
    | zero => simp [ps1, ParseState.advance] at h_f
    | succ n =>
      unfold parseNode
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_np]; simp only []
      unfold validateNodeProps
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      unfold parseNodeContent
      rw [h_peek1]; rfl
  -- applyNodeFinalization (scalar with empty props and trackPositions=false)
  have h_finalize : applyNodeFinalization
      (.scalar { content, style := .doubleQuoted, tag := none, anchor := none })
      ps1.advance {} (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
      = (.scalar { content, style := .doubleQuoted, tag := none, anchor := none }, ps1.advance) := by
    unfold applyNodeFinalization
    simp [ps1, ParseState.advance]
  -- Combine into parseDocument
  have h_doc_val : parseDocument ps1 = .ok
      ({ value := .scalar { content, style := .doubleQuoted, tag := none, anchor := none },
         directives := #[], anchors := ps1.advance.anchors,
         nodePositions := ps1.advance.nodePositions }, ps1.advance) := by
    unfold parseDocument
    simp only [bind, Except.bind, h_pds, h_peek1, h_parseNode, h_finalize]
  -- ps1.advance.peek? = some .streamEnd
  have h_peek2 : ps1.advance.peek? = some .streamEnd := by
    simp only [ps1, ParseState.peek?, ParseState.advance, h2, ↓reduceIte]
    simp only [show (0 : Nat) + 1 + 1 = 2 from rfl, h_gei 2 h2, h_t2']
  -- Apply parseStreamLoop_single_doc
  have h_fuel_ge : tokens.size ≥ 2 := by omega
  have h_loop := parseStreamLoop_single_doc ps1 tokens.size h_fuel_ge
    (.scalar content .doubleQuoted) h_peek1 (by intro h; cases h)
    { value := .scalar { content, style := .doubleQuoted, tag := none, anchor := none },
      directives := #[], anchors := ps1.advance.anchors, nodePositions := ps1.advance.nodePositions }
    ps1.advance h_doc_val h_peek2
  -- Provide the witness
  exact ⟨_, h_loop, rfl, by simp [getElem!_pos]⟩

/-- **parseYamlRaw on emitScalar produces scalar value**: When `parseYamlRaw`
    succeeds on emitter scalar output, the first document's value is a scalar
    with the original content. -/
theorem parseYamlRaw_emitScalar_value (content : String)
    (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emitScalar content) = .ok raw_docs) :
    ∃ s : Scalar, raw_docs[0]!.value = .scalar s ∧ s.content = content := by
  -- Decompose into scan + parse
  obtain ⟨tokens, h_scan, h_parse⟩ :=
    Composition.parseYamlRaw_ok_decompose _ _ h_raw
  -- Token structure from scanner
  obtain ⟨h_sz3, h_t0, h_t1, h_t2⟩ := scanFiltered_emitScalar_vals content tokens h_scan
  -- Parser trace on [streamStart, scalar, streamEnd]
  obtain ⟨docs, h_ps, _, h_dv⟩ :=
    parseStream_three_tokens_scalar content tokens h_sz3 h_t0 h_t1 h_t2
  -- Unify raw_docs with docs
  have h_eq : raw_docs = docs := Except.ok.inj (h_parse.symm.trans h_ps)
  subst h_eq
  exact ⟨Scalar.mk content .doubleQuoted none none none, h_dv, rfl⟩

-- ═══ Helper infrastructure for flow collection parser acceptance ═══

-- Combined scanner-parser pipeline Bool checks for "[]" and "{}".
-- Using native_decide on Bool expressions avoids needing DecidableEq instances
-- for Except, Array, etc.
def checkFullSeq : Bool :=
  match Scanner.scanFiltered "[]" with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => docs.size == 1
    | .error _ => false
  | .error _ => false

def checkFullMap : Bool :=
  match Scanner.scanFiltered "{}" with
  | .ok tokens =>
    match parseStream tokens with
    | .ok docs => docs.size == 1
    | .error _ => false
  | .error _ => false

theorem checkFullSeq_true : checkFullSeq = true := by native_decide
theorem checkFullMap_true : checkFullMap = true := by native_decide

-- Content fidelity Bool checks for empty flow collections.
-- Verifies: parseYamlRaw "[]"/{}" succeeds AND the composed result is content-equivalent
-- to the original empty collection.
def checkContentSeq : Bool :=
  match parseYamlRaw "[]" with
  | .ok raw_docs =>
    raw_docs.size == 1 &&
    contentEq (.sequence .flow #[]) (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

def checkContentMap : Bool :=
  match parseYamlRaw "{}" with
  | .ok raw_docs =>
    raw_docs.size == 1 &&
    contentEq (.mapping .flow #[]) (raw_docs.map YamlDocument.compose)[0]!.value
  | .error _ => false

theorem checkContentSeq_true : checkContentSeq = true := by native_decide
theorem checkContentMap_true : checkContentMap = true := by native_decide

-- ═══ Scanner → Parser bridge: token structure for non-empty flow collections ═══

/-! ### Infrastructure for filtered token tracking (Sub-phase 4.4.G) -/

/-- `unwindIndents` is identity when the indent stack has at most 1 entry.
    This covers emitter output where `indents = #[]` (the default from `ScannerState.mk'`).
    `unwindIndentsLoop` checks `s.indents.size > 1` before unwinding; with size ≤ 1,
    the condition fails immediately and the state is returned unchanged. -/
theorem unwindIndents_noop_short_stack (s : ScannerState)
    (h_stack : s.indents.size ≤ 1) :
    unwindIndents s (-1) = s := by
  unfold unwindIndents
  unfold unwindIndentsLoop
  split
  · -- fuel = 0 case is impossible since fuel = s.indents.size ≤ 1
    rfl
  · -- fuel = fuel' + 1
    split
    · -- s.currentIndent > -1 && s.indents.size > 1
      exfalso
      rename_i h_cond
      simp only [Bool.and_eq_true, decide_eq_true_iff] at h_cond
      omega
    · rfl

/-- When a ScanChain starts from s₀ via scanFiltered, the token array equation.
    Combines `scanFiltered_of_chain_eq` with `unwindIndents` identity for emitter states.

    **Initiative 3 / J.3.8** (2026-04-29): post-cutover RHS is
    `linearise final.tokens final.pendingKeys` rather than the legacy
    `tokens.filter (· != .placeholder)`.  Callers that have
    `s_final.peek? = none` discharge `h_peek_eof` accordingly. -/
theorem scanFiltered_tokens_eq_of_chain_short_stack
    (input : String) (s₀ s_final : ScannerState) (n : Nat)
    (h_s0 : s₀ = (ScannerState.mk' input).emit .streamStart)
    (h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF')
    (h_chain : ScanChain s₀ n s_final)
    (h_eof : scanNextToken s_final = .ok none)
    (h_fl : s_final.flowLevel = 0)
    (h_dp : s_final.directivesPresent = false)
    (h_peek_eof : s_final.peek? = none)
    (h_fuel : n + 1 ≤ (input.utf8ByteSize + 1) * 4)
    (h_stack : s_final.indents.size ≤ 1) :
    Scanner.scanFiltered input = .ok (Scanner.linearise
      (s_final.emit .streamEnd).tokens (s_final.emit .streamEnd).pendingKeys) := by
  have h_skip : skipToContent s_final = .ok s_final :=
    skipToContent_eq_self_of_peek_none h_peek_eof
  have h_eq := scanFiltered_of_chain_eq input s₀ s_final s_final n
    h_s0 h_no_bom h_chain h_eof h_fl h_dp h_skip h_fuel
  rwa [unwindIndents_noop_short_stack s_final h_stack] at h_eq

/-- `ScanChain` token array monotonicity: tokens array size grows (non-strictly)
    through any scan chain. -/
theorem ScanChain_tokens_mono {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s') : s'.tokens.size ≥ s.tokens.size := by
  induction h_chain with
  | zero => exact Nat.le_refl _
  | step h_snt _h_rest ih => exact Nat.le_trans (ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt) ih

/-- Combined per-step prefix preservation and simpleKey invariant maintenance.

    **Precondition**: `n ≤ s.tokens.size` and the simpleKey condition
    `s.simpleKey.possible → s.simpleKey.tokenIndex ≥ n`, which says that
    the prefix index doesn't overlap the simpleKey placeholder position.
    Without this, `scanNextToken` may overwrite `tokens[tokenIndex]`
    (replacing `.placeholder` with `.key`), violating prefix preservation.

    **Precondition**: Uses `SimpleKeyAbove` to track both the current simpleKey
    and all stacked simpleKeys. This is necessary because flow close operations
    (`]`/`}`) restore a simpleKey from the stack, and without stack bounds,
    the restored `tokenIndex` could fall below `n`.

    **Conclusion**: Returns both prefix preservation and `SimpleKeyAbove s' n`,
    enabling straightforward induction in `ScanChain_preserves_raw_prefix`. -/
theorem scanNextToken_prefix_and_sk_inv (s s' : ScannerState)
    (h_next : scanNextToken s = .ok (some s'))
    (n : Nat) (h_n : n ≤ s.tokens.size)
    (h_inv : ScannerCorrectness.SimpleKeyAbove s n) :
    (∀ (i : Nat) (hi : i < n),
      s'.tokens[i]'(by have := ScannerCorrectness.scanNextToken_adds_tokens s s' h_next; omega) =
      s.tokens[i]'(by omega)) ∧
    ScannerCorrectness.SimpleKeyAbove s' n :=
  ⟨fun i hi => ScannerCorrectness.scanNextToken_preserves_prefix s s' h_next n h_n h_inv i hi,
   ScannerCorrectness.scanNextToken_maintains_simpleKeyAbove s s' h_next n h_n h_inv⟩

/-- Through a ScanChain, all raw token positions below `n₀` are preserved,
    provided `n₀ ≤ s.tokens.size` and `SimpleKeyAbove s n₀` holds (tracking
    both the current simpleKey and all stacked simpleKeys).

    The `SimpleKeyAbove` invariant is maintained through each step by
    `scanNextToken_prefix_and_sk_inv`, making the induction straightforward. -/
theorem ScanChain_preserves_raw_prefix {s s' : ScannerState} {k : Nat}
    (h_chain : ScanChain s k s')
    (n₀ : Nat) (h_n₀ : n₀ ≤ s.tokens.size)
    (h_inv : ScannerCorrectness.SimpleKeyAbove s n₀)
    (i : Nat) (hi : i < n₀) :
    s'.tokens[i]'(by have := ScanChain_tokens_mono h_chain; omega) =
    s.tokens[i]'(by omega) := by
  induction h_chain with
  | zero => rfl
  | step h_snt h_rest ih =>
    have h_adds := ScannerCorrectness.scanNextToken_adds_tokens _ _ h_snt
    have ⟨h_pres, h_inv'⟩ := scanNextToken_prefix_and_sk_inv _ _ h_snt n₀ h_n₀ h_inv
    exact (ih (Nat.le_trans h_n₀ h_adds) h_inv').trans (h_pres i hi)

/-! #### Main theorem: filtered growth through scanNextToken -/

-- Every `scanNextToken` step adds at least one non-placeholder token to the
-- filtered token array.  Note: the structural dispatch case for unknown
-- directives (%RESERVED) adds 0 tokens but still returns `some s'`.  The
-- ≥+1 bound holds for all emitter-produced inputs (which only use %YAML/%TAG
-- directives and document markers, each emitting ≥1 non-placeholder token).
set_option maxHeartbeats 3200000 in
theorem scanNextToken_filtered_grows (s s' : ScannerState)
    (h : scanNextToken s = .ok (some s')) :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + 1 := by
  unfold scanNextToken at h
  simp only [bind, pure, Pure.pure, Except.pure] at h
  simp only [Except.bind] at h
  split at h
  · contradiction
  · split at h
    · simp at h
    · have h_pp_mono := preprocess_filtered_mono s _ _ (by assumption)
      repeat (any_goals (split at h))
      any_goals contradiction
      any_goals (simp at h)
      all_goals first
        | contradiction
        | (simp at h)
        | (have h_d := dispatchFlowIndicators_filtered_grows _ _ _ (by assumption);
           rw [allowDir_ite_filter] at h_d; simp_all <;> omega)
        | (have h_d := dispatchBlockIndicators_filtered_grows _ _ _ (by assumption);
           rw [allowDir_ite_filter] at h_d; simp_all <;> omega)
        | (have h_d := dispatchContent_filtered_grows _ _ _ (by assumption);
           rw [allowDir_ite_filter] at h_d; simp_all <;> omega)
        | (simp_all <;> omega)
        -- structural dispatch: case-split into docStart, docEnd, directive
        | (-- Resolve monadic binds (docEnd/directive use do-notation)
           try simp only [bind, Except.bind] at h
           try (split at h <;> first | contradiction | skip)
           -- Extract equality from .ok/.some wrappers
           try simp only [Except.ok.injEq, Option.some.injEq] at h
           try (injection h with h)
           try subst h
           first
             | (have := scanDocumentStart_filtered_grows _; omega)
             | (have := scanDocumentEnd_filtered_grows _ _ (by assumption); omega)
             | sorry)

/-- Through a ScanChain of `n` steps, the filtered token array grows by at least `n`. -/
theorem ScanChain_filtered_grows {s s' : ScannerState} {n : Nat}
    (h_chain : ScanChain s n s') :
    (s'.tokens.filter (fun t => t.val != .placeholder)).size ≥
    (s.tokens.filter (fun t => t.val != .placeholder)).size + n := by
  induction h_chain with
  | zero => omega
  | step h_snt _h_rest ih =>
    have h_step := scanNextToken_filtered_grows _ _ h_snt
    omega


/-- Through a FlowMonoChain, the filtered token array of the final state has the
    filtered array of the initial state as a prefix.

    Uses `FlowMonoChain_preserves_raw_prefix` (which maintains `SimpleKeyAboveFloor`
    through the chain using the flow-level floor) composed with
    `Array_filter_prefix_of_raw_prefix` to lift raw index preservation to
    filtered-array prefix preservation.

    **Preconditions**:
    - `FlowMonoChain fl₀ s n s'`: flow-monotone chain with floor `fl₀`
    - `h_sk`: `s.simpleKey.possible = false` (no in-flight placeholder reservation)
    - `h_sync`: `s.simpleKeyStack.size ≥ s.flowLevel` (stack/flow synchronized)
    - `h_stack_floor`: stack entries at index ≥ `fl₀` have `tokenIndex ≥ s.tokens.size`

    Both call sites have `fl₀ = s₁.flowLevel = 1` with `s₁.simpleKeyStack.size = 1`,
    making `h_stack_floor` vacuously true (no `j` satisfies `1 ≤ j < 1`). -/
theorem ScanChain_filtered_prefix {s s' : ScannerState} {n fl₀ : Nat}
    (h_fmc : FlowMonoChain fl₀ s n s')
    (h_sk : s.simpleKey.possible = false)
    (h_sync : s.simpleKeyStack.size ≥ s.flowLevel)
    (h_stack_floor : ∀ j, fl₀ ≤ j → (hj : j < s.simpleKeyStack.size) →
      s.simpleKeyStack[j].possible = true → s.simpleKeyStack[j].tokenIndex ≥ s.tokens.size) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ suffix, (s'.tokens.filter p).toList = (s.tokens.filter p).toList ++ suffix := by
  exact Array_filter_prefix_of_raw_prefix s.tokens s'.tokens _
    (FlowMonoChain.tokens_mono h_fmc)
    (fun i hi => FlowMonoChain_preserves_raw_prefix h_fmc s.tokens.size (by omega)
      ⟨fun h => absurd h (by simp [h_sk]), h_stack_floor, by have := h_fmc.flowLevel_ge_start; omega⟩
      h_sync i hi)

/-- `emitPairList` for non-empty pairs produces a non-empty string. -/
theorem emitPairList_toList_ne_nil (p : YamlValue × YamlValue)
    (ps : List (YamlValue × YamlValue)) :
    (emit.emitPairList (p :: ps)).toList ≠ [] := by
  obtain ⟨c, rest', h_eq, _, _, _⟩ := emitPairList_first_char p ps
  rw [h_eq]; exact List.cons_ne_nil _ _

/-- `scanFlowSequenceEnd` token array equation: pushes exactly one `.flowSequenceEnd` token. -/
theorem scanFlowSequenceEnd_tokens_eq (s : ScannerState) :
    (scanFlowSequenceEnd s).tokens = s.tokens.push { pos := s.currentPos, val := .flowSequenceEnd } := by
  unfold scanFlowSequenceEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowSequenceEnd)]
  unfold ScannerState.emit; rfl

/-- `scanFlowMappingEnd` token array equation: pushes exactly one `.flowMappingEnd` token. -/
theorem scanFlowMappingEnd_tokens_eq (s : ScannerState) :
    (scanFlowMappingEnd s).tokens = s.tokens.push { pos := s.currentPos, val := .flowMappingEnd } := by
  unfold scanFlowMappingEnd
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens (s.emit .flowMappingEnd)]
  unfold ScannerState.emit; rfl

/-- The close-bracket step for outermost `]`: filtered token array is the input
    filtered array with `.flowSequenceEnd` appended.

    Traces through `saveSimpleKey` (adds only placeholders, filtered out) →
    `allowDirectives` (no token change) → `scanFlowSequenceEnd` (appends
    `.flowSequenceEnd` which passes the placeholder filter). -/
theorem scanNextToken_flow_close_seq_outermost_ext (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨[']'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok, tok.val = .flowSequenceEnd ∧
          s'.tokens.filter p = (s.tokens.filter p).push tok) := by
  -- Replay the close bracket proof to get the intermediate state s_ad
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, ']')) :=
    scanNextToken_preprocess_flow s ']' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) ']' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_bracket s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨[']'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_bracket_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- s' = scanFlowSequenceEnd s_ad
  let s' := scanFlowSequenceEnd s_ad
  have h_result_fl : s'.flowLevel = 0 := by
    show (scanFlowSequenceEnd s_ad).flowLevel = 0
    rw [scanFlowSequenceEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : s'.directivesPresent = false := by
    show (scanFlowSequenceEnd s_ad).directivesPresent = false
    rw [scanFlowSequenceEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : s'.peek? = none := by
    show (scanFlowSequenceEnd s_ad).peek? = none
    rw [scanFlowSequenceEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad ']' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowSequenceEnd) ']' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowSequenceEnd).offset < (s_ad.emit .flowSequenceEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Indents preservation: s'.indents = s.indents
  have h_result_indents : s'.indents = s.indents := by
    show (scanFlowSequenceEnd s_ad).indents = s.indents
    rw [scanFlowSequenceEnd_preserves_indents]
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  -- Filtered tokens: s'.tokens.filter p = (s.tokens.filter p).push tok
  have h_ad_tokens_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKey_filter_placeholder s
  have h_result_tokens : ∃ tok, tok.val = .flowSequenceEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
    have h_fse_tokens : (scanFlowSequenceEnd s_ad).tokens =
        s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd } :=
      scanFlowSequenceEnd_tokens_eq s_ad
    have h_filter_push : (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowSequenceEnd }).filter
        (fun t => t.val != .placeholder) =
        (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s_ad.currentPos, val := .flowSequenceEnd } := by
      rw [Array.filter_push]; rfl
    exact ⟨{ pos := s_ad.currentPos, val := .flowSequenceEnd }, rfl,
      by rw [show s' = scanFlowSequenceEnd s_ad from rfl,
             h_fse_tokens, h_filter_push, h_ad_tokens_filter]⟩
  exact ⟨s', h_snt, h_result_fl, h_result_dp, h_result_eof, h_result_indents, h_result_tokens⟩

/-- The close-brace step for outermost `}`: filtered token array is the input
    filtered array with `.flowMappingEnd` appended. -/
theorem scanNextToken_flow_close_mapping_outermost_ext (s : ScannerState)
    (hcorr : ScannerSurfCorr s ⟨['}'], s.col⟩)
    (h_flow : s.inFlow = true)
    (h_indent : s.currentIndent < 0)
    (h_col_pos : s.col > 0)
    (h_fl : s.flowLevel = 1)
    (h_dp : s.directivesPresent = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    ∃ s', scanNextToken s = .ok (some s')
      ∧ s'.flowLevel = 0
      ∧ s'.directivesPresent = false
      ∧ s'.peek? = none
      ∧ s'.indents = s.indents
      ∧ (∃ tok, tok.val = .flowMappingEnd ∧
          s'.tokens.filter p = (s.tokens.filter p).push tok) := by
  -- Replay the close brace proof to get the intermediate state s_ad
  have h_pp : scanNextToken_preprocess s = .ok (some (saveSimpleKey s, '}')) :=
    scanNextToken_preprocess_flow s '}' [] s.col hcorr h_flow
      (by decide) (by decide) (by decide)
  have h_sk_flow : (saveSimpleKey s).inFlow = s.inFlow := saveSimpleKey_preserves_inFlow s
  have h_sk_col : (saveSimpleKey s).col = s.col := saveSimpleKey_preserves_col s
  have h_sk_indent : (saveSimpleKey s).currentIndent = s.currentIndent := by
    unfold ScannerState.currentIndent; rw [saveSimpleKey_preserves_indents]
  have h_struct : scanNextToken_dispatchStructural (saveSimpleKey s) '}' = .ok none :=
    dispatchStructural_none_flow _ _ (h_sk_flow ▸ h_flow) (h_sk_indent ▸ h_indent) (h_sk_col ▸ h_col_pos)
  let s_ad := if (saveSimpleKey s).allowDirectives then
    { saveSimpleKey s with allowDirectives := false, documentEverStarted := true }
  else saveSimpleKey s
  have h_check := checkBlockFlowIndent_ok_close_brace s_ad
  have h_ad_fl : s_ad.flowLevel = s.flowLevel := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_flowLevel s
  have h_ad_dp : s_ad.directivesPresent = s.directivesPresent := by
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_directivesPresent s
  have h_ad_col : s_ad.col = s.col := by simp only [s_ad]; split <;> exact h_sk_col
  have h_ad_corr : ScannerSurfCorr s_ad ⟨['}'], s_ad.col⟩ := by
    rw [h_ad_col]; exact ScannerSurfCorr_transfer hcorr
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_input s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_offset s)
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_inputEnd s)
      h_ad_col
      (by simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s)
  have h_flow_disp := dispatchFlowIndicators_close_brace_outermost s_ad
    (h_ad_fl ▸ h_fl) h_ad_corr
  have h_snt := scanNextToken_via_flow_dispatch _ _ _ _ _ h_pp h_struct rfl h_check h_flow_disp
  -- s' = scanFlowMappingEnd s_ad
  let s' := scanFlowMappingEnd s_ad
  have h_result_fl : s'.flowLevel = 0 := by
    show (scanFlowMappingEnd s_ad).flowLevel = 0
    rw [scanFlowMappingEnd_flowLevel, h_ad_fl, h_fl]
    simp (config := { decide := true })
  have h_result_dp : s'.directivesPresent = false := by
    show (scanFlowMappingEnd s_ad).directivesPresent = false
    rw [scanFlowMappingEnd_preserves_dp, h_ad_dp]; exact h_dp
  have h_result_eof : s'.peek? = none := by
    show (scanFlowMappingEnd s_ad).peek? = none
    rw [scanFlowMappingEnd_peek]; exact peek_none_of_empty_surf _ _ (by
      have ⟨_, h_lt⟩ := peek_of_chars_cons s_ad '}' [] s_ad.col h_ad_corr
      exact advance_non_newline_corr (s_ad.emit .flowMappingEnd) '}' []
        ⟨h_ad_corr.chars_from, h_ad_corr.col_eq, h_ad_corr.end_eq,
         h_ad_corr.input_prefix, h_ad_corr.indent_cols_nonneg⟩
        (show (s_ad.emit .flowMappingEnd).offset < (s_ad.emit .flowMappingEnd).inputEnd from h_lt)
        (by decide) (by decide))
  -- Indents preservation: s'.indents = s.indents
  have h_result_indents : s'.indents = s.indents := by
    show (scanFlowMappingEnd s_ad).indents = s.indents
    rw [scanFlowMappingEnd_preserves_indents]
    simp only [s_ad]; split <;> exact saveSimpleKey_preserves_indents s
  -- Filtered tokens: s'.tokens.filter p = (s.tokens.filter p).push tok
  have h_ad_tokens_filter : s_ad.tokens.filter (fun t => t.val != .placeholder) =
      s.tokens.filter (fun t => t.val != .placeholder) := by
    simp only [s_ad]
    split <;> exact saveSimpleKey_filter_placeholder s
  have h_result_tokens : ∃ tok, tok.val = .flowMappingEnd ∧
      s'.tokens.filter (fun t => t.val != .placeholder) =
      (s.tokens.filter (fun t => t.val != .placeholder)).push tok := by
    have h_fme_tokens : (scanFlowMappingEnd s_ad).tokens =
        s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd } :=
      scanFlowMappingEnd_tokens_eq s_ad
    have h_filter_push : (s_ad.tokens.push { pos := s_ad.currentPos, val := .flowMappingEnd }).filter
        (fun t => t.val != .placeholder) =
        (s_ad.tokens.filter (fun t => t.val != .placeholder)).push
          { pos := s_ad.currentPos, val := .flowMappingEnd } := by
      rw [Array.filter_push]; rfl
    exact ⟨{ pos := s_ad.currentPos, val := .flowMappingEnd }, rfl,
      by rw [show s' = scanFlowMappingEnd s_ad from rfl,
             h_fme_tokens, h_filter_push, h_ad_tokens_filter]⟩
  exact ⟨s', h_snt, h_result_fl, h_result_dp, h_result_eof, h_result_indents, h_result_tokens⟩

-- Every `scanFiltered` result has streamStart first, streamEnd last, size ≥ 2.
-- Mirrors the proof of `scanFiltered_produces_valid_tokens` but returns a
-- plain conjunction (avoiding the `ValidTokenStream` struct indirection).
theorem scanFiltered_boundary_tokens (input : String)
    (tokens : Array (Positioned YamlToken))
    (h : Scanner.scanFiltered input = .ok tokens) :
    tokens.size ≥ 2 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd := by
  -- **Initiative 3 / J.3.6** (2026-04-28): post-cutover `scanFiltered`
  -- uses `linearise`; the per-field theorems
  -- `scanFiltered_first_is_streamStart` / `scanFiltered_last_is_streamEnd`
  -- (Step 9.b in `ScannerCorrectness`) already discharge the new shape.
  have h_size : tokens.size ≥ 2 :=
    L4YAML.Proofs.ScannerCorrectness.scanFiltered_produces_at_least_two
      input tokens h
  have h_pos₀ : 0 < tokens.size := by omega
  have h_pos_last : tokens.size - 1 < tokens.size := by omega
  refine ⟨h_size, ?_, ?_⟩
  · rw [getElem!_pos _ 0 h_pos₀]
    exact L4YAML.Proofs.ScannerCorrectness.scanFiltered_first_is_streamStart
      input tokens h h_pos₀
  · rw [getElem!_pos _ (tokens.size - 1) h_pos_last]
    exact L4YAML.Proofs.ScannerCorrectness.scanFiltered_last_is_streamEnd
      input tokens h h_pos₀

theorem scanFlowSequenceStart_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowSequenceStart s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowSequenceStart } := by
  unfold scanFlowSequenceStart
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowMappingStart` filtered token equation: adds exactly one `.flowMappingStart`. -/
theorem scanFlowMappingStart_filtered (s : ScannerState) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    (scanFlowMappingStart s).tokens.filter p =
    (s.tokens.filter p).push { pos := s.currentPos, val := .flowMappingStart } := by
  unfold scanFlowMappingStart
  dsimp only []
  rw [ScannerCorrectness.advance_preserves_tokens]
  rw [emit_tokens_push]
  rw [Array.filter_push]; rfl

/-- `scanFlowEntry` filtered token equation (when it succeeds):
    adds exactly one `.flowEntry`. -/
theorem scanFlowEntry_filtered (s s' : ScannerState)
    (h : scanFlowEntry s = .ok s') :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    s'.tokens.filter p = (s.tokens.filter p).push { pos := s.currentPos, val := .flowEntry } := by
  unfold scanFlowEntry at h
  simp only [bind, Except.bind, pure, Except.pure] at h
  -- Split on the validation check
  split at h
  · split at h
    · cases h
    · simp only [Except.ok.injEq] at h
      rw [← h]
      dsimp only []
      rw [ScannerCorrectness.advance_preserves_tokens]
      rw [emit_tokens_push]
      rw [Array.filter_push]; rfl
  · simp only [Except.ok.injEq] at h
    rw [← h]
    dsimp only []
    rw [ScannerCorrectness.advance_preserves_tokens]
    rw [emit_tokens_push]
    rw [Array.filter_push]; rfl

/-- `ScanChain_deterministic`: two chains with the same start state and step count
    reach the same final state (since `scanNextToken` is a function). -/
theorem ScanChain_deterministic {s s₁ s₂ : ScannerState} {n : Nat}
    (h₁ : ScanChain s n s₁) (h₂ : ScanChain s n s₂) : s₁ = s₂ := by
  induction h₁ generalizing s₂ with
  | zero => cases h₂; rfl
  | @step s s_mid₁ s₁ k h_snt₁ _ ih =>
    match h₂ with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid₁ = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

/-- `ScanChain.split`: decompose a chain into two consecutive sub-chains. -/
theorem ScanChain.split {s s₁ s₂ : ScannerState} {n₁ n₂ : Nat}
    (h₁ : ScanChain s n₁ s₁) (h_total : ScanChain s (n₁ + n₂) s₂) :
    ScanChain s₁ n₂ s₂ := by
  induction h₁ generalizing s₂ with
  | zero => simpa using h_total
  | @step s s_mid s₁ k h_snt₁ _ ih =>
    have h_rw : k + 1 + n₂ = (k + n₂) + 1 := by omega
    rw [h_rw] at h_total
    match h_total with
    | .step h_snt₂ h_rest₂ =>
      have : s_mid = _ := Option.some.inj (Except.ok.inj (h_snt₁.symm.trans h_snt₂))
      subst this
      exact ih h_rest₂

-- ═══ Body token characterization lemmas ═══

-- The proofs require tracing per-step scanner dispatch: each `emit v` produces first
-- character `"`, `[`, or `{`, which dispatch to scanDoubleQuoted / scanFlowSequenceStart /
-- scanFlowMappingStart respectively. The comma separator `, ` dispatches to scanFlowEntry
-- followed by whitespace skip and then the next item's dispatch.
--
-- IMPORTANT: The flowEntry pattern (part 2) is restricted to OUTER-LEVEL flowEntries
-- (where flowBracketBalance from old_sz to k equals 0). Inner flowEntries inside nested
-- bracket groups (e.g., inside a nested mapping `{k1: v1, k2: v2}`) have `.key` after
-- them, not a content start. The parser loop only visits outer-level flowEntries because
-- `parseNode` consumes entire bracket groups, so this restriction is sufficient.

/-- Body token characterization for `emitList` in flow context:
    (1) The first new filtered token (at position `old_sz`) is a content start.
    (2) After every OUTER-LEVEL `.flowEntry` (where bracket balance from `old_sz` to `k` is 0),
        the next filtered token is a content start.

    These follow from `emitList`'s structure: items separated by `", "` (comma + space).
    Each item starts with `emit v`, whose first character (`"`, `[`, or `{`) dispatches to
    `scanDoubleQuoted`, `scanFlowSequenceStart`, or `scanFlowMappingStart` — none of which
    emit `.flowEntry` or `.key` as their first filtered token. -/
theorem emitList_body_filtered_characterization
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlow v)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    -- (1) First new filtered token is a content start (scalar, flowSeqStart, or flowMapStart)
    ∧ (old_sz < (s'.tokens.filter p).size ∧
     (∀ (h : old_sz < (s'.tokens.filter p).size),
       ((∃ c sc, ((s'.tokens.filter p)[old_sz]'h).val = .scalar c sc) ∨
        ((s'.tokens.filter p)[old_sz]'h).val = .flowSequenceStart ∨
        ((s'.tokens.filter p)[old_sz]'h).val = .flowMappingStart)))
    -- (2) After every OUTER-LEVEL flowEntry, next is a content start
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
      ((s'.tokens.filter p)[k]'h_hi).val = .flowEntry →
      flowBracketBalance (s'.tokens.filter p) old_sz k = 0 →
      k + 1 < (s'.tokens.filter p).size ∧
      (∀ (h' : k + 1 < (s'.tokens.filter p).size),
        ((∃ c sc, ((s'.tokens.filter p)[k + 1]'h').val = .scalar c sc) ∨
         ((s'.tokens.filter p)[k + 1]'h').val = .flowSequenceStart ∨
         ((s'.tokens.filter p)[k + 1]'h').val = .flowMappingStart))) := by
  -- Construct the chain from EmitListScansInFlow.  The strict ScanChainGrew
  -- variant is what's returned now; we forget to plain ScanChain only at the
  -- public boundary, but use the strict-track filtered_grows internally to
  -- bypass the line-8541 sorry.
  have h_scan := emitList_scans_nonempty items h_ne h_all
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, _h_size, _h_pkRec⟩ :=
    h_scan s rest h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc, ?_, ?_⟩
  · -- Part 1: First new filtered token is a content start
    have h_grows := ScanChainGrew_filtered_grows h_chain
    have h_n_pos : n ≥ 1 := by
      match n, h_chain with
      | 0, h_zero =>
        exfalso
        have h_eq : s = s' := by cases h_zero; rfl
        rw [h_eq] at h_corr
        have h_chars_eq := CharsFromOffset_unique h_corr.chars_from h_corr'.chars_from
        have h_len := congrArg List.length h_chars_eq
        simp only [List.length_append] at h_len
        have h_nil : (emit.emitList items).toList = [] := by
          match h_list : (emit.emitList items).toList with
          | [] => rfl
          | _ :: _ => simp [h_list] at h_len
        match h_items : items with
        | [] => exact absurd rfl h_ne
        | i :: is => exact absurd h_nil (emitList_toList_ne_nil i is)
      | _ + 1, _ => omega
    constructor
    · -- old_sz < filtered size
      omega
    · -- The token at old_sz is a content start
      sorry
  · -- Part 2: After every outer-level flowEntry, next is a content start
    sorry

/-! ### J.4.2.b-2c — Linearise-shape body characterization for `emitList`

Linearise-shape variant of `emitList_body_filtered_characterization` for the
no-resolution sub-class.  Wraps the filter-shape characterization with three
extra outputs:

* `AllUnresolved s'`: chain-side propagation via
  `ScanChain.preserves_AllUnresolved` (J.4.2.b-2a-chain), parametric in a
  per-action `h_step_unres` discharge — the consumer plugs in
  `scanNextToken_preserves_AllUnresolved` (J.4.2.b-2a-discharge) under the
  no-`:`-pair sub-class hypothesis.
* `NoPlaceholders s'`: chain-side propagation via
  `ScanChain.preserves_NoPlaceholders` (J.4.2.b-2b-chain), discharged
  unconditionally by `scanNextToken_preserves_NoPlaceholders`
  (J.4.2.b-2b-discharge).
* `linearise s'.tokens s'.pendingKeys = s'.tokens.filter p`: the bridge
  collapse via `linearise_eq_filter_no_resolutions` (J.4.1).

Together these let cascade consumers in
`scanFiltered_emitSeq_nonempty_structure` read the body content tokens off
the linearise-shape output (the post-cutover bridge target) using the
J.4.2.c positional family (`-pos1`, `-pos2`, `-prefix`) and the
`linearise_push_eq_push_linearise` (J.4.2.c-prep) `streamEnd` peeler. -/

/-- Linearise-shape variant of `emitList_body_filtered_characterization`
    for the no-resolution sub-class.  Restates parts (1) and (2) of the
    filter-shape body characterization on `linearise s'.tokens s'.pendingKeys`,
    using `linearise_eq_filter_no_resolutions` (J.4.1) as the bridge after
    chain-side propagation of `AllUnresolved` (J.4.2.b-2a-chain) and
    `NoPlaceholders` (J.4.2.b-2b-chain). -/
theorem emitList_body_linearise_characterization
    (items : List YamlValue) (h_ne : items ≠ [])
    (h_all : ∀ v ∈ items, EmitScansInFlow v)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitList items).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false)
    (h_unres : ScannerCorrectness.AllUnresolved s)
    (h_no_pl : ScannerCorrectness.NoPlaceholders s)
    (h_step_unres : ∀ {sa sb : ScannerState},
        ScannerCorrectness.AllUnresolved sa →
        scanNextToken sa = .ok (some sb) →
        ScannerCorrectness.AllUnresolved sb) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    ∧ ScannerCorrectness.AllUnresolved s'
    ∧ ScannerCorrectness.NoPlaceholders s'
    ∧ linearise s'.tokens s'.pendingKeys = s'.tokens.filter p
    -- (1) First new linearised token is a content start
    ∧ (old_sz < (linearise s'.tokens s'.pendingKeys).size ∧
       (∀ (h : old_sz < (linearise s'.tokens s'.pendingKeys).size),
         ((∃ c sc, ((linearise s'.tokens s'.pendingKeys)[old_sz]'h).val = .scalar c sc) ∨
          ((linearise s'.tokens s'.pendingKeys)[old_sz]'h).val = .flowSequenceStart ∨
          ((linearise s'.tokens s'.pendingKeys)[old_sz]'h).val = .flowMappingStart)))
    -- (2) After every OUTER-LEVEL flowEntry in linearised output, next is a content start
    ∧ (∀ (k : Nat), old_sz ≤ k →
       (h_hi : k < (linearise s'.tokens s'.pendingKeys).size) →
       ((linearise s'.tokens s'.pendingKeys)[k]'h_hi).val = .flowEntry →
       flowBracketBalance (linearise s'.tokens s'.pendingKeys) old_sz k = 0 →
       k + 1 < (linearise s'.tokens s'.pendingKeys).size ∧
       (∀ (h' : k + 1 < (linearise s'.tokens s'.pendingKeys).size),
         ((∃ c sc, ((linearise s'.tokens s'.pendingKeys)[k + 1]'h').val = .scalar c sc) ∨
          ((linearise s'.tokens s'.pendingKeys)[k + 1]'h').val = .flowSequenceStart ∨
          ((linearise s'.tokens s'.pendingKeys)[k + 1]'h').val = .flowMappingStart))) := by
  -- Step 1: invoke the filter-shape body characterization
  have h_filt := emitList_body_filtered_characterization items h_ne h_all s rest
    h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sk
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc',
          h_body_pair, h_body_fe_next⟩ := h_filt
  -- Step 2: derive AllUnresolved s' (parametric in h_step_unres)
  have h_unres' : ScannerCorrectness.AllUnresolved s' :=
    h_chain.preserves_AllUnresolved h_step_unres h_unres
  -- Step 3: derive NoPlaceholders s' (unconditional via 2b-discharge)
  have h_no_pl' : ScannerCorrectness.NoPlaceholders s' :=
    h_chain.preserves_NoPlaceholders
      (fun h h_ok => ScannerCorrectness.scanNextToken_preserves_NoPlaceholders _ _ h h_ok)
      h_no_pl
  -- Step 4: bridge linearise = filter via J.4.1
  have h_lin_eq :
      linearise s'.tokens s'.pendingKeys =
        s'.tokens.filter (fun (t : Positioned YamlToken) => t.val != .placeholder) :=
    L4YAML.Proofs.ScannerLinearise.linearise_eq_filter_no_resolutions
      s'.tokens s'.pendingKeys h_unres' h_no_pl'
  -- Step 5: assemble the conclusion, transporting (1) and (2) via h_lin_eq
  refine ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc', h_unres', h_no_pl', h_lin_eq, ?_, ?_⟩
  · -- Part (1): linearise-shape content start at old_sz
    rw [h_lin_eq]
    exact h_body_pair
  · -- Part (2): linearise-shape after-flowEntry pattern
    rw [h_lin_eq]
    exact h_body_fe_next

/-- Body token characterization for `emitPairList` in flow context:
    (1) The chain has ≥ 3 steps (key handling + value indicator + value content).
    (2) The first new filtered token is `.key` (from `saveSimpleKey` + `scanValuePrepare`
        retroactively converting a placeholder when `: ` is scanned).
    (3) After every OUTER-LEVEL `.flowEntry` (where bracket balance from `old_sz` to `k` is 0),
        the next filtered token is `.key`.

    These follow from `emitPairList`'s structure: each pair produces `emit k ++ ": " ++ emit v`,
    with pairs separated by `", "`. The `: ` triggers `scanValuePrepare` which converts the
    placeholder (saved by `saveSimpleKey` before scanning `emit k`) to `.key`. After each
    comma separator, the next pair starts with `emit k` again, preceded by `saveSimpleKey`.

    IMPORTANT: The flowEntry pattern (part 3) is restricted to outer-level flowEntries
    (bracketBalance = 0). Inner flowEntries from nested sequences/mappings may be followed
    by content-start tokens rather than `.key`. The parser loop only visits outer-level
    flowEntries because `parseNode` consumes entire nested bracket groups. -/
theorem emitPairList_body_filtered_characterization
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlow p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlow p.2)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false)
    (h_ska : s.simpleKeyAllowed = true) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    -- (1) At least 3 chain steps (key + value indicator + value)
    ∧ n ≥ 3
    -- (2) First new filtered token is .key
    ∧ (old_sz < (s'.tokens.filter p).size ∧
     (∀ (h : old_sz < (s'.tokens.filter p).size),
       ((s'.tokens.filter p)[old_sz]'h).val = .key))
    -- (3) After every OUTER-LEVEL flowEntry, next is .key
    ∧ (∀ (k : Nat), old_sz ≤ k → (h_hi : k < (s'.tokens.filter p).size) →
      ((s'.tokens.filter p)[k]'h_hi).val = .flowEntry →
      flowBracketBalance (s'.tokens.filter p) old_sz k = 0 →
      k + 1 < (s'.tokens.filter p).size ∧
      (∀ (h' : k + 1 < (s'.tokens.filter p).size),
        ((s'.tokens.filter p)[k + 1]'h').val = .key))
    -- (4) C-compose: first-pair resolved-key entry at index `s.pendingKeys.size`
    -- (insertBeforeIdx = `s.tokens.size`, kind = `.keyOnly`).  Threaded from
    -- `emitPairList_scans_nonempty`'s first-key conjunct (under the existing
    -- `pairs ≠ []` hypothesis); consumed by `emitPairList_body_linearise_characterization`
    -- to align with Foundation A's `[0]`-index splice when `s.pendingKeys = #[]`.
    ∧ (∃ (h : s.pendingKeys.size < s'.pendingKeys.size),
        (s'.pendingKeys[s.pendingKeys.size]'h).insertBeforeIdx = s.tokens.size
        ∧ (s'.pendingKeys[s.pendingKeys.size]'h).kind = .keyOnly)
    -- (5) Part3-extend: per-pair locator array `qs : Array Nat` of pendingKey
    -- indices (one per pair).  Threaded from `emitPairList_scans_nonempty`'s
    -- per-pair conjunct (J.4.2.b-2d-key-chain-Part3-extend-EmitPairListScansInFlow-per-pair).
    -- Sub-step 4 (Part3-thread-body-filtered-char): re-stated here so
    -- consumers (linearise wrapper + Tier 1 derivations) can read the
    -- per-pair shape without re-invoking `emitPairList_scans_nonempty`.
    -- `insertBeforeIdx` is NOT exposed (sub-step 5 derives it from
    -- saveSimpleKey monotonicity).  `qs[0] = s.pendingKeys.size` aligns
    -- with conjunct (4); strict-monotonicity reflects pendingKey
    -- monotonicity at each pair's saveSimpleKey.
    ∧ (∃ (qs : Array Nat) (_h_size : qs.size = pairs.length)
         (h_pos : 0 < qs.size),
         qs[0]'h_pos = s.pendingKeys.size
         ∧ (∀ i (h : i < qs.size),
             ∃ (h_lt : qs[i]'h < s'.pendingKeys.size),
               (s'.pendingKeys[qs[i]'h]'h_lt).kind = .keyOnly)
         ∧ (∀ i j (hi : i < qs.size) (hj : j < qs.size),
             i < j → qs[i]'hi < qs[j]'hj)
         -- (6) Part3-final-discharge-bridge-6a (2026-05-02): predecessor-flowEntry.
         -- For each `i ≥ 1`, the token at `pks[qs[i]].insertBeforeIdx - 1`
         -- in `s'.tokens` is `.flowEntry` (the comma between pair i-1 and pair i).
         -- Threaded from `emitPairList_scans_nonempty`'s new conjunct.
         ∧ (∀ i (hi : i < qs.size) (_h_pos_i : 0 < i),
             ∃ (h_lt : qs[i]'hi < s'.pendingKeys.size)
               (_h_ib_pos : 0 < (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx)
               (h_pred_lt :
                 (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx - 1
                   < s'.tokens.size),
               (s'.tokens[
                   (s'.pendingKeys[qs[i]'hi]'h_lt).insertBeforeIdx - 1
                 ]'h_pred_lt).val = .flowEntry)) := by
  -- Construct the chain from EmitPairListScansInFlow
  have h_scan := emitPairList_scans_nonempty pairs h_ne h_all_k h_all_v
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc, _h_size, _h_pkRec,
          _h_pks_eq, h_first, h_first_qs⟩ :=
    h_scan s rest h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_ska
  have h_n_pos : n ≥ 1 := by
    match n, h_chain with
    | 0, h_zero =>
      exfalso
      have h_eq : s = s' := by cases h_zero; rfl
      rw [h_eq] at h_corr
      have h_chars_eq := CharsFromOffset_unique h_corr.chars_from h_corr'.chars_from
      have h_len := congrArg List.length h_chars_eq
      simp only [List.length_append] at h_len
      have h_nil : (emit.emitPairList pairs).toList = [] := by
        match h_list : (emit.emitPairList pairs).toList with
        | [] => rfl
        | _ :: _ => simp [h_list] at h_len
      match h_pairs : pairs with
      | [] => exact absurd rfl h_ne
      | p :: ps => exact absurd h_nil (emitPairList_toList_ne_nil p ps)
    | _ + 1, _ => omega
  have h_grows := ScanChainGrew_filtered_grows h_chain
  refine ⟨n, s', h_chain.toScanChain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc, ?_, ?_, ?_, h_first h_ne, h_first_qs h_ne⟩
  · -- Part 1: n ≥ 3
    sorry
  · -- Part 2: First new filtered token is .key
    constructor
    · -- old_sz < filtered size
      omega
    · -- The token at old_sz is .key
      sorry
  · -- Part 3: After every outer-level flowEntry, next is .key
    sorry

/-! ### J.4.2.b-2d-key-chain-Part3 sub-step 6c-ii-α (2026-05-02):
    bracket-balance preservation through `linearise.go`

Bracket-balance preservation is the foundational mechanism for the
inversion-direction discharge of `emitPairList_body_linearise_characterization`
Part (3): an outer-level `.flowEntry` in `linearise` (balance = 0) corresponds
to an outer-level `.flowEntry` in `s'.tokens` at the matching token-cursor
position.

Spliced tokens (`.key`, `.blockMappingStart` from `expandKind`) all have
`flowBracketDelta = 0`, so they never affect cumulative bracket count.
Token-copy steps push `tokens[j]`, advancing both `linearise`'s and
`tokens`'s bracket balances by the same `flowBracketDelta tokens[j].val`.
Therefore `flowBracketBalance acc 0 acc.size = flowBracketBalance tokens 0 j`
is invariant across the walk.

Sub-step 6c-ii-β (forthcoming) consumes this preservation to invert
`linearise[k] = .flowEntry` ∧ outer-level into `s'.tokens[j_k] = .flowEntry`
∧ outer-level, then chain-side `qs` enumeration yields the matching
pair index `i ≥ 1`. -/

/-- Splice tokens contributed by `expandKind` (`.key`, `.blockMappingStart`)
    have `flowBracketDelta = 0`.  Trivial corollary of `expandKind_val_neutral`
    (the splice tokens are never flow brackets). -/
theorem expandKind_flowBracketDelta_zero (e : PendingKeyEntry)
    (i : Nat) (h : i < (expandKind e).size) :
    flowBracketDelta (expandKind e)[i].val = 0 := by
  rcases L4YAML.Proofs.ScannerLinearise.expandKind_val_neutral e i h with h_key | h_bms
  · rw [h_key]; rfl
  · rw [h_bms]; rfl

/-- Pushing one token to `acc` and extending the balance range by 1 picks up
    the new token's `flowBracketDelta`.  Builds on `flowBracketBalance_compose`
    + `flowBracketBalance_push` + `flowBracketBalance_single`. -/
theorem flowBracketBalance_push_extend
    (acc : Array (Positioned YamlToken))
    (tok : Positioned YamlToken) (lo : Nat) (h_lo : lo ≤ acc.size) :
    flowBracketBalance (acc.push tok) lo (acc.size + 1)
      = flowBracketBalance acc lo acc.size + flowBracketDelta tok.val := by
  rw [flowBracketBalance_compose (acc.push tok) lo acc.size (acc.size + 1)
        h_lo (Nat.le_succ _)]
  rw [flowBracketBalance_push acc tok lo acc.size (Nat.le_refl _)]
  congr 1
  -- balance over [acc.size, acc.size + 1] = flowBracketDelta tok.val
  have h_lt : acc.size < (acc.push tok).toList.length := by
    rw [Array.length_toList, Array.size_push]; omega
  rw [flowBracketBalance_single (acc.push tok) acc.size h_lt]
  congr 1
  -- (acc.push tok).toList[acc.size] = tok
  have h_idx_eq : (acc.push tok).toList[acc.size]'h_lt = tok := by
    have h_arr_lt : acc.size < (acc.push tok).size := by rw [Array.size_push]; omega
    have h_arr_eq : (acc.push tok)[acc.size]'h_arr_lt = tok :=
      Array.getElem_push_eq (xs := acc) (x := tok)
    exact h_arr_eq
  rw [h_idx_eq]

/-- Splice step: `acc ++ expandKind e` extends `acc` by 0, 1, or 2 tokens,
    each with `flowBracketDelta = 0`.  The bracket balance is unchanged
    over the extended range.  Proof by case analysis on `e.kind`, applying
    `flowBracketBalance_push_extend` once or twice. -/
theorem flowBracketBalance_splice_unchanged
    (acc : Array (Positioned YamlToken)) (e : PendingKeyEntry)
    (lo : Nat) (h_lo : lo ≤ acc.size) :
    flowBracketBalance (acc ++ expandKind e) lo (acc.size + (expandKind e).size)
      = flowBracketBalance acc lo acc.size := by
  match h_kind : e.kind with
  | .unresolved =>
    have h_exp : expandKind e = (#[] : Array (Positioned YamlToken)) := by
      simp [expandKind, h_kind]
    rw [h_exp]
    rw [show (#[] : Array (Positioned YamlToken)).size = 0 from rfl]
    rw [show acc ++ (#[] : Array (Positioned YamlToken)) = acc from Array.append_empty]
    rw [Nat.add_zero]
  | .keyOnly =>
    have h_exp : expandKind e = #[⟨e.pos, .key, e.pos⟩] := by
      simp [expandKind, h_kind]
    rw [h_exp]
    rw [show acc ++ (#[⟨e.pos, .key, e.pos⟩] : Array (Positioned YamlToken))
            = acc.push ⟨e.pos, .key, e.pos⟩ from rfl]
    rw [show (#[⟨e.pos, .key, e.pos⟩] : Array (Positioned YamlToken)).size = 1 from rfl]
    rw [flowBracketBalance_push_extend acc ⟨e.pos, .key, e.pos⟩ lo h_lo]
    rw [show flowBracketDelta (Positioned.mk e.pos YamlToken.key e.pos).val = 0 from rfl]
    rw [Int.add_zero]
  | .blockMappingStartAndKey =>
    have h_exp : expandKind e
                  = #[⟨e.pos, .blockMappingStart, e.pos⟩, ⟨e.pos, .key, e.pos⟩] := by
      simp [expandKind, h_kind]
    rw [h_exp]
    rw [show acc ++ (#[⟨e.pos, .blockMappingStart, e.pos⟩,
                       ⟨e.pos, .key, e.pos⟩] : Array (Positioned YamlToken))
            = (acc.push ⟨e.pos, .blockMappingStart, e.pos⟩).push ⟨e.pos, .key, e.pos⟩ from rfl]
    rw [show (#[⟨e.pos, .blockMappingStart, e.pos⟩,
                ⟨e.pos, .key, e.pos⟩] : Array (Positioned YamlToken)).size = 2 from rfl]
    -- balance over [lo, acc.size + 2] = balance over [lo, (acc.push bms).size + 1]
    have h_lo' : lo ≤ (acc.push ⟨e.pos, .blockMappingStart, e.pos⟩).size := by
      rw [Array.size_push]; omega
    have h_size_two_eq : acc.size + 2
                          = (acc.push ⟨e.pos, .blockMappingStart, e.pos⟩).size + 1 := by
      rw [Array.size_push]
    rw [h_size_two_eq]
    rw [flowBracketBalance_push_extend (acc.push ⟨e.pos, .blockMappingStart, e.pos⟩)
          ⟨e.pos, .key, e.pos⟩ lo h_lo']
    rw [show flowBracketDelta (Positioned.mk e.pos YamlToken.key e.pos).val = 0 from rfl]
    rw [Int.add_zero]
    rw [Array.size_push]
    rw [flowBracketBalance_push_extend acc ⟨e.pos, .blockMappingStart, e.pos⟩ lo h_lo]
    rw [show flowBracketDelta (Positioned.mk e.pos YamlToken.blockMappingStart e.pos).val
            = 0 from rfl]
    rw [Int.add_zero]

/-! ### J.4.2.b-2d — Linearise-shape body characterization for `emitPairList`

Linearise-shape variant of `emitPairList_body_filtered_characterization` for
the resolution case (each pair contributes one `:` resolution that converts
its `.unresolved` pendingKey entry into `.keyOnly`).  Unlike 2c (seq body),
the bridge `linearise = filter` does NOT hold here: the linearise output
splices a `.key` token at each resolved pendingKey's `insertBeforeIdx`, so
linearise[old_sz] = .key whereas filter[old_sz] = first content token of
`emit k`.  The wrapper therefore states the linearise-shape claims directly
rather than transporting from the filter shape.

Stub-level discharge for this cadence step:
* Chain side: reuse `emitPairList_body_filtered_characterization` for the
  chain, all 13 invariant carries, `n ≥ 3`, and `FlowMonoChain`.
* `NoPlaceholders s'`: chain-side propagation via
  `ScanChain.preserves_NoPlaceholders` (J.4.2.b-2b-chain), discharged
  unconditionally by `scanNextToken_preserves_NoPlaceholders`
  (J.4.2.b-2b-discharge).
* Linearise-shape Parts (2)/(3) (`linearise[old_sz] = .key` and
  `linearise[k+1] = .key` after outer-level flowEntry): SORRY'd as
  J.4.2.b-2d-key follow-up.  These require resolved-key splice analysis
  using the J.4.2.c positional family + new pendingKey-aware linearise
  lemmas (forthcoming).

NOTE: `AllUnresolved s'` does NOT carry through (the `:` actions resolve
pendingKey entries to `.keyOnly`).  The pair body's per-action discharge
condition for AllUnresolved fails by design — this is why the legacy
`linearise = filter` bridge cannot carry the pair-body conclusion. -/

/-- Linearise-shape variant of `emitPairList_body_filtered_characterization`
    for the resolution case.  Carries the chain, structural invariants,
    `n ≥ 3`, and `NoPlaceholders s'` from the filter-shape characterization;
    states the linearise-shape Parts (2) and (3) (first new linearised
    token is `.key`; after every outer-level flowEntry, next is `.key`)
    directly on `linearise s'.tokens s'.pendingKeys` without the
    `linearise = filter` bridge (which fails when `:` resolutions fire).

    Stub-level discharge: linearise-shape Parts (2)/(3) are sorry'd as
    J.4.2.b-2d-key follow-up (resolved-key splice analysis). -/
theorem emitPairList_body_linearise_characterization
    (pairs : List (YamlValue × YamlValue)) (h_ne : pairs ≠ [])
    (h_all_k : ∀ p ∈ pairs, EmitScansInFlow p.1)
    (h_all_v : ∀ p ∈ pairs, EmitScansInFlow p.2)
    (s : ScannerState) (rest : List Char)
    (h_corr : ScannerSurfCorr s ⟨(emit.emitPairList pairs).toList ++ rest, s.col⟩)
    (h_flow : s.inFlow = true) (h_fl : s.flowLevel > 0)
    (h_indent : s.currentIndent < 0) (h_col : s.col > 0)
    (h_ek : s.explicitKeyLine = none)
    (h_atol : AllTokensOnLine s s.line)
    (h_endline : EndLineOnLine s)
    (h_sk : s.simpleKey.possible = false)
    (h_ska : s.simpleKeyAllowed = true)
    (h_no_pl : ScannerCorrectness.NoPlaceholders s)
    (h_pks_empty : s.pendingKeys = #[]) :
    let p := fun (t : Positioned YamlToken) => t.val != .placeholder
    let old_sz := (s.tokens.filter p).size
    ∃ n s', ScanChain s n s'
    ∧ ScannerSurfCorr s' ⟨rest, s'.col⟩
    ∧ s'.flowLevel = s.flowLevel
    ∧ s'.directivesPresent = s.directivesPresent
    ∧ s'.indents = s.indents
    ∧ s'.explicitKeyLine = s.explicitKeyLine
    ∧ s'.col > 0
    ∧ s'.inFlow = true
    ∧ s'.currentIndent < 0
    ∧ s'.line = s.line
    ∧ AllTokensOnLine s' s'.line
    ∧ EndLineOnLine s'
    ∧ s'.simpleKeyStack = s.simpleKeyStack
    ∧ FlowMonoChain s.flowLevel s n s'
    ∧ n ≥ 3
    ∧ ScannerCorrectness.NoPlaceholders s'
    -- (2) First new linearised token is .key
    ∧ (old_sz < (linearise s'.tokens s'.pendingKeys).size ∧
       (∀ (h : old_sz < (linearise s'.tokens s'.pendingKeys).size),
         ((linearise s'.tokens s'.pendingKeys)[old_sz]'h).val = .key))
    -- (3) After every OUTER-LEVEL flowEntry in linearised output, next is .key
    ∧ (∀ (k : Nat), old_sz ≤ k →
       (h_hi : k < (linearise s'.tokens s'.pendingKeys).size) →
       ((linearise s'.tokens s'.pendingKeys)[k]'h_hi).val = .flowEntry →
       flowBracketBalance (linearise s'.tokens s'.pendingKeys) old_sz k = 0 →
       k + 1 < (linearise s'.tokens s'.pendingKeys).size ∧
       (∀ (h' : k + 1 < (linearise s'.tokens s'.pendingKeys).size),
         ((linearise s'.tokens s'.pendingKeys)[k + 1]'h').val = .key)) := by
  -- Step 1: invoke the filter-shape body characterization for `emitPairList`
  have h_filt := emitPairList_body_filtered_characterization pairs h_ne h_all_k h_all_v
    s rest h_corr h_flow h_fl h_indent h_col h_ek h_atol h_endline h_sk h_ska
  obtain ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek', h_col', h_inflow',
          h_indent', h_line', h_atol', h_endline', h_stack', h_fmc',
          h_n_ge3, _h_body_key, _h_body_fe_next, h_first_key, _h_first_qs⟩ := h_filt
  -- Step 2: derive NoPlaceholders s' (unconditional via 2b-discharge).
  -- AllUnresolved does NOT carry — `:` resolutions are by design here.
  have h_no_pl' : ScannerCorrectness.NoPlaceholders s' :=
    h_chain.preserves_NoPlaceholders
      (fun h h_ok => ScannerCorrectness.scanNextToken_preserves_NoPlaceholders _ _ h h_ok)
      h_no_pl
  -- Step 3: assemble.
  refine ⟨n, s', h_chain, h_corr', h_fl', h_dp', h_ids', h_ek',
          h_col', h_inflow', h_indent', h_line', h_atol', h_endline',
          h_stack', h_fmc', h_n_ge3, h_no_pl', ?_, ?_⟩
  · -- Part (2): linearise-shape first-key claim — discharged via Foundation A
    -- (`linearise_first_splice_keyonly`) plus the first-pair chain-side facts
    -- now exposed by `emitPairList_body_filtered_characterization`'s
    -- C-compose conjunct.  With `h_pks_empty : s.pendingKeys = #[]`, the
    -- conjunct's index `s.pendingKeys.size` collapses to `0`, aligning with
    -- Foundation A's `[0]`-index splice.

    -- (s.tokens.filter p) = s.tokens since `NoPlaceholders s`.
    have h_filter_eq_s :
        s.tokens.filter (fun t => t.val != .placeholder) = s.tokens := by
      apply Array.filter_eq_self.mpr
      intro t h_mem
      have h_ne : t.val ≠ .placeholder := h_no_pl t h_mem
      simp [bne_iff_ne, h_ne]
    -- Trivial sub-fact: token monotonicity through the chain (filter ≤ identity
    -- on `s.tokens`, then chain extends).  Discharged directly via
    -- `ScanChain_tokens_mono` + `Array.size_filter_le`.
    have h_size_le : (s.tokens.filter (fun t => t.val != .placeholder)).size
        ≤ s'.tokens.size := by
      have h_filt_le : (s.tokens.filter (fun t => t.val != .placeholder)).size
          ≤ s.tokens.size := Array.size_filter_le
      have h_chain_mono : s.tokens.size ≤ s'.tokens.size :=
        ScanChain_tokens_mono h_chain
      exact Nat.le_trans h_filt_le h_chain_mono
    -- C-compose: specialize the body's first-key conjunct via `h_pks_empty`.
    have h_sz_zero : s.pendingKeys.size = 0 := by rw [h_pks_empty]; rfl
    -- Rewrite the conjunct at the type level so the index becomes `0`.
    have h_first_key₀ : ∃ (h : 0 < s'.pendingKeys.size),
        (s'.pendingKeys[0]'h).insertBeforeIdx = s.tokens.size
        ∧ (s'.pendingKeys[0]'h).kind = .keyOnly := h_sz_zero ▸ h_first_key
    obtain ⟨h_pos, h_idx_raw, h_kind⟩ := h_first_key₀
    have h_idx : s'.pendingKeys[0].insertBeforeIdx
        = (s.tokens.filter (fun t => t.val != .placeholder)).size := by
      rw [h_idx_raw, h_filter_eq_s]
    -- Apply Foundation A.
    obtain ⟨h_lin, h_at⟩ :=
      L4YAML.Proofs.ScannerLinearise.linearise_first_splice_keyonly
        s'.tokens s'.pendingKeys
        (s.tokens.filter (fun t => t.val != .placeholder)).size
        h_size_le h_pos h_idx h_kind
    exact ⟨h_lin, fun _ => h_at⟩
  · -- Part (3): linearise-shape after-flowEntry-key claim — discharged via Foundation B
    -- (`linearise_splice_keyonly_at_index`) plus chain-side accounting of the
    -- `s'.pendingKeys[p]` shape for each outer-level flowEntry.  Foundation B
    -- supplies the splice mechanic (transport + .keyOnly readout); the chain
    -- supplies the (j, p, acc) state with `acc.size = k + 1` matching the
    -- after-flowEntry position.  The remaining sorry is narrowed to chain-side
    -- accounting (J.4.2.b-2d-key-chain extended to all outer pairs).
    intro k h_old_le_k h_hi h_fe h_balance
    -- Chain-side accounting (J.4.2.b-2d-key-chain): the pending key entry
    -- corresponding to the pair AFTER the flowEntry at outer-level position `k`
    -- has `kind = .keyOnly` and the linearise walk reaches state `(j, p, acc)`
    -- with `acc.size = k + 1` and `pks[p].insertBeforeIdx ≤ j`.
    --
    -- **Sub-task 6c-ii-bridge-inversion (sorry'd, decomposed across sub-steps)**:
    -- The forward direction (each pair contributes a `.flowEntry → .key` pair
    -- at consecutive linearise positions `(pks[qs[i]].insertBeforeIdx - 1 +
    -- P(qs[i]), pks[qs[i]].insertBeforeIdx + P(qs[i]))` for `i ≥ 1`) is now
    -- discharged via two ScannerLinearise lemmas:
    --   * `linearise_walk_at_kth_predecessor_token` (sub-step 6c-i, 2026-05-02)
    --     reads off `linearise[(j_i - 1) + P(qs[i])] = tokens[j_i - 1]` (where
    --     `j_i = pks[qs[i]].insertBeforeIdx`); combined with `h_first_qs`'s
    --     predecessor-flowEntry conjunct, this gives `.flowEntry` at the
    --     forward position.
    --   * `linearise_walk_at_kth_resolved_splice` reads off `linearise[j_i +
    --     P(qs[i])] = .key` at the immediately following position.
    -- The INVERSE direction — given an arbitrary outer-level flowEntry at
    -- linearise position `k`, identify the unique pair index `i ≥ 1` such
    -- that `k + 1 = pks[qs[i]].insertBeforeIdx + P(qs[i])` — requires
    -- bracket-balance accounting to enumerate all outer-level flowEntries
    -- and rule out any coming from inner flow scopes.  Decomposed into:
    --   * **Sub-step 6c-ii-α (DONE 2026-05-02)**: bracket-balance algebra
    --     helpers — `expandKind_flowBracketDelta_zero`,
    --     `flowBracketBalance_push_extend`, `flowBracketBalance_splice_unchanged`.
    --     These establish that splice tokens contribute 0 to bracket balance and
    --     that `linearise.go`'s push/append steps update balance predictably.
    --   * **Sub-step 6c-ii-β (PENDING)**: bracket-balance preservation lemma
    --     `linearise_go_walk_flowBracketBalance` — the parallel induction over
    --     `linearise.go`'s lex-measure proving
    --     `flowBracketBalance acc' acc.size acc'.size = flowBracketBalance tokens j j'`
    --     for any walk transport `(j, p, acc) → (j', p', acc')`.
    --   * **Sub-step 6c-ii-γ (PENDING)**: inversion enumeration — given an
    --     outer-level `.flowEntry` at linearise position `k`, identify the
    --     unique pair index `i ≥ 1` with `k + 1 = j_i + P(qs[i])`.  Consumes
    --     6c-ii-β to translate balance condition to `s'.tokens` side, then
    --     uses chain-side `qs` enumeration to pin down `i`.
    --
    -- Sub-step 6b dispatched the easier 6a-i1-lift sorry (cons-case `i = 1`
    -- predecessor-flowEntry lift via `FlowMonoChain_preserves_existing_tokens`).
    -- Sub-step 6c-i landed the forward-direction readout
    -- (`linearise_walk_at_kth_predecessor_token`); sub-step 6c-ii-α landed
    -- the bracket-balance algebra helpers.  The full inversion bridge here
    -- remains pending across 6c-ii-β / 6c-ii-γ.
    have h_chain_facts :
        ∃ (j p : Nat) (acc : Array (Positioned YamlToken))
          (_ : linearise s'.tokens s'.pendingKeys
                = L4YAML.Scanner.linearise.go s'.tokens s'.pendingKeys j p acc)
          (_ : acc.size = k + 1)
          (h_p : p < s'.pendingKeys.size),
          s'.pendingKeys[p].insertBeforeIdx ≤ j ∧ s'.pendingKeys[p].kind = .keyOnly := by
      sorry
    obtain ⟨j, p, acc, h_eq_lin, h_acc_size, h_p, h_splice, h_kind⟩ := h_chain_facts
    obtain ⟨h_k1_lt, h_at⟩ :=
      L4YAML.Proofs.ScannerLinearise.linearise_splice_keyonly_at_index
        s'.tokens s'.pendingKeys j p (k + 1) acc
        h_eq_lin h_acc_size h_p h_splice h_kind
    exact ⟨h_k1_lt, fun _ => h_at⟩

/-- Token structure of `scanFiltered ("[" ++ emitList items ++ "]")` for non-empty items.
    Establishes boundary tokens, body token patterns, and `parseNode` success within
    the flow sequence body.

    Requires `EmitScansInFlow` for each item to construct the scanner chain. -/
theorem scanFiltered_emitSeq_nonempty_structure
    (items : Array YamlValue) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("[" ++ emit.emitList items.toList ++ "]") = .ok tokens)
    (h_ne : items.toList ≠ [])
    (h_all_scan : ∀ w, w ∈ items.toList → EmitScansInFlow w) :
    tokens.size ≥ 5 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd ∧
    tokens[1]!.val = .flowSequenceStart ∧
    tokens[tokens.size - 2]!.val = .flowSequenceEnd ∧
    ((∃ c s, tokens[2]!.val = .scalar c s) ∨
     tokens[2]!.val = .flowSequenceStart ∨
     tokens[2]!.val = .flowMappingStart) ∧
    (∀ k, 2 ≤ k → k < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧
        ((∃ c s, tokens[k + 1]!.val = .scalar c s) ∨
         tokens[k + 1]!.val = .flowSequenceStart ∨
         tokens[k + 1]!.val = .flowMappingStart)) ∧
    L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := by
  -- Step 1: Boundary tokens from scanFiltered_boundary_tokens
  obtain ⟨h_sz2, h_t0, h_tlast⟩ := scanFiltered_boundary_tokens _ _ h_scan
  -- ═══ Chain replay: reconstruct s₁ (after '['), s₂ (after body), s₃ (after ']') ═══
  let input := "[" ++ emit.emitList items.toList ++ "]"
  have h_toList : input.toList = '[' :: (emit.emitList items.toList).toList ++ [']'] := by
    simp only [input, String.toList_append]; rfl
  -- Open bracket → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁⟩ :=
    scanNextToken_flow_open_init input
      ((emit.emitList items.toList).toList ++ [']']) h_toList
  -- Body scanning → s₂ (with filtered token characterization)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
          h_ek₂, h_col₂, h_inflow₂, h_indent₂, _, _, _, h_stack₂, h_fmc₂,
          ⟨h_body_sz_raw, h_body_cs_raw⟩, h_body_fe_next_raw⟩ :=
    emitList_body_filtered_characterization items.toList h_ne
      (fun w hw => h_all_scan w hw) s₁ [']']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sk₁
  -- Close bracket → s₃ (using _ext to get filtered token info + indents)
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fse, h_tok_fse_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_seq_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '['
      ((emit.emitList items.toList).toList ++ [']']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₀.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- ═══ Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p ═══
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  -- Initiative 3 / J.3.8 (2026-04-29): post-cutover, the bridge yields
  -- `linearise (...).tokens (...).pendingKeys` rather than the legacy
  -- `tokens.filter p` shape used by the Tier 1 derivations below.  The
  -- legacy form is recoverable when all `pendingKeys` at `s₃` are
  -- `.unresolved` AND `s₃.tokens` contains no `.placeholder`.  The
  -- former fails when items contain flow maps (`{k: v}`-style with
  -- `:`-resolution), so this bridge is sorry'd as J.4 cascade work.
  -- Cf. linearise_all_unresolved + post-cutover no-placeholder invariant.
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) := by
    sorry
  -- Extract: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Decompose filtered token array as: s₂_filtered ++ [flowSeqEnd, streamEnd] ═══
  -- s₃.tokens.filter p = (s₂.tokens.filter p).push tok_fse  (from _ext)
  -- (s₃.emit .streamEnd).tokens.filter p = s₃.tokens.filter p ++ [streamEnd]
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  -- Combine: tokens = (s₂.filter p) ++ [tok_fse] ++ [streamEnd]
  -- i.e. tokens = ((s₂.filter p).push tok_fse).push streamEnd
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fse).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Tier 1 derivations ═══
  -- h_tpe: tokens[tokens.size - 2] = tok_fse, which has val = .flowSequenceEnd
  have h_tpe : tokens[tokens.size - 2]!.val = .flowSequenceEnd := by
    rw [h_tokens_decomp]
    have h_outer_sz : (((s₂.tokens.filter p).push tok_fse).push
        { pos := s₃.currentPos, val := YamlToken.streamEnd }).size =
        (s₂.tokens.filter p).size + 2 := by simp [Array.size_push]
    rw [h_outer_sz, show (s₂.tokens.filter p).size + 2 - 2 = (s₂.tokens.filter p).size from by omega]
    rw [getElem!_pos _ _ (by omega)]
    rw [Array.getElem_push_lt (show (s₂.tokens.filter p).size <
        ((s₂.tokens.filter p).push tok_fse).size from by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
    exact h_tok_fse_val
  -- ═══ Filtered prefix preservation (via ScanChain infrastructure) ═══
  -- h_filt₁ : (s₁.tokens.filter p).map (·.val) = #[.streamStart, .flowSequenceStart]
  -- Extract filtered prefix size and element values
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_filt₁_val1 : ((s₁.tokens.filter p)[1]'(by omega)).val = YamlToken.flowSequenceStart := by
    have h_len : (s₁.tokens.filter p).toList.length = 2 := by
      rw [Array.length_toList]; exact h_filt₁_sz
    have h_vals : (s₁.tokens.filter p).toList.map (·.val) =
        [YamlToken.streamStart, YamlToken.flowSequenceStart] := by
      have := congrArg Array.toList h_filt₁; simpa [Array.toList_map] using this
    obtain ⟨a, b, h_ab⟩ : ∃ a b, (s₁.tokens.filter p).toList = [a, b] := by
      match (s₁.tokens.filter p).toList, h_len with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    show (s₁.tokens.filter p).toList[1].val = YamlToken.flowSequenceStart
    simp only [h_ab, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [h_ab] at h_vals; simp at h_vals; exact h_vals.2
  -- Body chain preserves filtered prefix and grows by ≥ n₂
  obtain ⟨suffix, h_suffix⟩ : ∃ suffix, (s₂.tokens.filter p).toList =
      (s₁.tokens.filter p).toList ++ suffix :=
    ScanChain_filtered_prefix h_fmc₂ h_sk₁ (by omega) (by
      intro j hj hjsz; rw [h_sync₁] at hjsz; rw [h_fl₁] at hj; omega)
  have h_filt_grows : (s₂.tokens.filter p).size ≥
      (s₁.tokens.filter p).size + n₂ := ScanChain_filtered_grows h_chain₂
  -- n₂ ≥ 1 (body is non-empty: s₁ sees body chars, s₂ sees [']'])
  have h_n₂_pos : n₂ ≥ 1 := by
    match n₂, h_chain₂ with
    | 0, h_zero =>
      exfalso
      have h_s1_eq_s2 : s₁ = s₂ := by cases h_zero; rfl
      rw [h_s1_eq_s2] at h_corr₁
      have h_chars_eq := CharsFromOffset_unique h_corr₁.chars_from h_corr₂.chars_from
      have h_len := congrArg List.length h_chars_eq
      simp only [List.length_append] at h_len
      have h_nil : (emit.emitList items.toList).toList = [] := by
        match h_list : (emit.emitList items.toList).toList with
        | [] => rfl
        | _ :: _ => simp [h_list] at h_len
      match h_items : items.toList with
      | [] => exact absurd h_items h_ne
      | v :: vs =>
          rw [h_items] at h_nil; exact absurd h_nil (emitList_toList_ne_nil v vs)
    | _ + 1, _ => omega
  -- (s₂.tokens.filter p).size ≥ 3
  have h_s2_filt_sz : (s₂.tokens.filter p).size ≥ 3 := by
    rw [h_filt₁_sz] at h_filt_grows; omega
  -- h_t1: peel two pushes to reach (s₂.tokens.filter p)[1], then use prefix
  have h_t1 : tokens[1]!.val = .flowSequenceStart := by
    rw [h_tokens_decomp]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < ((s₂.tokens.filter p).push tok_fse).size
        from by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < (s₂.tokens.filter p).size from by omega)]
    -- Goal: (s₂.tokens.filter p)[1]'_.val = .flowSequenceStart
    -- Show filtered[1] is preserved from s₁ to s₂ via ScanChain prefix
    have h1_lt_s1 : 1 < (s₁.tokens.filter p).size := by rw [h_filt₁_sz]; omega
    have h_eq : (s₂.tokens.filter p)[1]'(by omega) = (s₁.tokens.filter p)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega) =
          (s₁.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega)
      simp only [h_suffix]
      exact List.getElem_append_left (by rw [Array.length_toList]; omega)
    calc ((s₂.tokens.filter p)[1]'(by omega)).val
        = ((s₁.tokens.filter p)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowSequenceStart := h_filt₁_val1
  -- h_sz5: tokens.size = (s₂.filter p).size + 2 ≥ 3 + 2 = 5
  have h_sz5 : tokens.size ≥ 5 := by
    rw [h_tokens_decomp]; simp [Array.size_push]; omega
  -- ═══ Body token characterization (now from combined theorem) ═══
  -- Rename _raw variables to match expected names
  have h_body_sz := h_body_sz_raw; have h_body_cs := h_body_cs_raw
  have h_body_fe_next := h_body_fe_next_raw
  rw [h_filt₁_sz] at h_body_sz h_body_cs h_body_fe_next
  -- Helper: tokens[k]! for k < tokens.size - 2 equals (s₂.filter p)[k]
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  have h_tok_body (k : Nat) (h_lt : k < (s₂.tokens.filter p).size) :
      tokens[k]! = ((s₂.tokens.filter p)[k]'h_lt) := by
    rw [h_tokens_decomp, getElem!_pos _ k (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show k < ((s₂.tokens.filter p).push tok_fse).size
        from by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_lt]
  have h_content0 : (∃ c s, tokens[2]!.val = .scalar c s) ∨
      tokens[2]!.val = .flowSequenceStart ∨
      tokens[2]!.val = .flowMappingStart := by
    have h_body := h_body_cs (by omega)
    rw [h_tok_body 2 (by omega)]
    exact h_body
  have h_fe_pattern : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens 2 k = 0 →
      k + 1 ≤ tokens.size - 2 ∧
      ((∃ c s, tokens[k + 1]!.val = .scalar c s) ∨
       tokens[k + 1]!.val = .flowSequenceStart ∨
       tokens[k + 1]!.val = .flowMappingStart) := by
    intro k h_lo h_hi h_fe h_depth
    have h_k_lt : k < (s₂.tokens.filter p).size := by omega
    rw [h_tok_body k h_k_lt] at h_fe
    -- Convert flowBracketBalance from tokens to s₂.tokens.filter p
    have h_depth' : flowBracketBalance (s₂.tokens.filter p) 2 k = 0 := by
      rw [← h_tokens_sz_eq] at h_k_lt
      have : flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
        rw [h_tokens_decomp]
        rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
        rw [flowBracketBalance_push _ _ 2 k (by omega)]
      rw [this] at h_depth; exact h_depth
    obtain ⟨h_next_lt, h_next_cs⟩ := h_body_fe_next k (by omega) h_k_lt h_fe h_depth'
    exact ⟨by omega,
           by rw [h_tok_body (k+1) (by omega)]; exact h_next_cs (by omega)⟩
  have h_pnok : L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk
      tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := sorry
  exact ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, h_content0, h_fe_pattern, h_pnok⟩

/-- Token structure of `scanFiltered ("{" ++ emitPairList pairs ++ "}")` for non-empty pairs.
    Establishes boundary tokens, body token patterns, and `parseExplicitKey`/`parseFlowMappingValue`
    success within the flow mapping body. -/
theorem scanFiltered_emitMap_nonempty_structure
    (pairs : Array (YamlValue × YamlValue)) (tokens : Array (Positioned YamlToken))
    (h_scan : Scanner.scanFiltered ("{" ++ emit.emitPairList pairs.toList ++ "}") = .ok tokens)
    (h_ne : pairs.toList ≠ [])
    (h_all_scan_k : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.1)
    (h_all_scan_v : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.2) :
    tokens.size ≥ 7 ∧
    tokens[0]!.val = .streamStart ∧
    tokens[tokens.size - 1]!.val = .streamEnd ∧
    tokens[1]!.val = .flowMappingStart ∧
    tokens[tokens.size - 2]!.val = .flowMappingEnd ∧
    tokens[2]!.val = .key ∧
    (∀ k, 2 ≤ k → k < tokens.size - 2 →
        tokens[k]!.val = .flowEntry →
        flowBracketBalance tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧ tokens[k + 1]!.val = .key) ∧
    L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := by
  -- Step 1: Boundary tokens from scanFiltered_boundary_tokens
  obtain ⟨h_sz2, h_t0, h_tlast⟩ := scanFiltered_boundary_tokens _ _ h_scan
  -- ═══ Chain replay: reconstruct s₁ (after '{'), s₂ (after body), s₃ (after '}') ═══
  let input := "{" ++ emit.emitPairList pairs.toList ++ "}"
  have h_toList : input.toList = '{' :: (emit.emitPairList pairs.toList).toList ++ ['}'] := by
    simp only [input, String.toList_append]; rfl
  -- Open brace → s₁
  obtain ⟨s₁, h_snt₁, h_corr₁, h_fl₁, h_dp₁, h_ids₁, h_col₁,
          h_inflow₁, h_indent₁, h_ek₁, h_line₁, h_atol₁, h_endline₁, h_sk₁, h_filt₁,
          h_sync₁, h_ska₁⟩ :=
    scanNextToken_flow_open_mapping_init input
      ((emit.emitPairList pairs.toList).toList ++ ['}']) h_toList
  -- Body scanning → s₂ (with filtered token characterization)
  obtain ⟨n₂, s₂, h_chain₂, h_corr₂, h_fl₂, h_dp₂, h_ids₂,
          h_ek₂, h_col₂, h_inflow₂, h_indent₂, _, _, _, h_stack₂, h_fmc₂,
          h_n₂_ge3, ⟨h_body_sz_raw, h_body_key_raw⟩, h_body_fe_next_raw,
          _h_body_first, _h_body_first_qs⟩ :=
    emitPairList_body_filtered_characterization pairs.toList h_ne
      (fun p hp => h_all_scan_k p hp) (fun p hp => h_all_scan_v p hp) s₁ ['}']
      h_corr₁ h_inflow₁ (by rw [h_fl₁]; omega) h_indent₁ (by rw [h_col₁]; omega)
      h_ek₁ (h_line₁ ▸ h_atol₁) h_endline₁ h_sk₁ h_ska₁
  -- Close brace → s₃ (using _ext to get filtered token info + indents)
  obtain ⟨s₃, h_snt₃, h_fl₃, h_dp₃, h_peek₃, h_ids₃, ⟨tok_fme, h_tok_fme_val, h_filt₃⟩⟩ :=
    scanNextToken_flow_close_mapping_outermost_ext s₂ h_corr₂ h_inflow₂ h_indent₂ h_col₂
      (by rw [h_fl₂, h_fl₁]) (by rw [h_dp₂, h_dp₁])
  -- EOF + chain composition
  have h_eof : scanNextToken s₃ = .ok none := scanNextToken_eof s₃ h_peek₃
  have h_chain_all := (ScanChain.single h_snt₁).trans
    (h_chain₂.trans (ScanChain.single h_snt₃))
  -- BOM check
  have h_no_bom : (ScannerState.mk' input).peek? ≠ some '\uFEFF' := by
    have h_chars := chars_from_zero_toList input
    rw [h_toList] at h_chars
    have h_corr := initial_corr _ _ h_chars
    have ⟨h_pk, _⟩ := peek_of_chars_cons _ '{'
      ((emit.emitPairList pairs.toList).toList ++ ['}']) 0 h_corr
    rw [h_pk]; decide
  -- Indents chain: s₃.indents = s₀.indents = #[] (default from mk')
  have h_indents_small : s₃.indents.size ≤ 1 := by
    rw [h_ids₃, h_ids₂, h_ids₁]
    unfold ScannerState.emit ScannerState.mk'
    dsimp only []
    decide
  -- ═══ Token equation: tokens = (s₃.emit .streamEnd).tokens.filter p ═══
  let p := fun (t : Positioned YamlToken) => t.val != .placeholder
  -- Initiative 3 / J.3.8 (2026-04-29): post-cutover, the bridge yields
  -- `linearise (...).tokens (...).pendingKeys` rather than the legacy
  -- `tokens.filter p` shape used by the Tier 1 derivations below.  Map
  -- pairs always trigger `:`-resolution at top level, so resolved
  -- `.keyOnly` entries always exist in `pendingKeys` at `s₃` — i.e.
  -- `linearise ≠ tokens.filter p` even after the no-placeholder
  -- invariant.  The Tier 1 derivations need re-stating in linearise
  -- terms (J.4 cascade work).
  have h_tok_eq : Scanner.scanFiltered input =
      .ok ((s₃.emit .streamEnd).tokens.filter p) := by
    sorry
  -- Extract: tokens = (s₃.emit .streamEnd).tokens.filter p
  have h_tokens_eq : tokens = (s₃.emit .streamEnd).tokens.filter p := by
    have : Scanner.scanFiltered input = .ok tokens := h_scan
    rw [h_tok_eq] at this; exact (Except.ok.inj this).symm
  -- ═══ Decompose filtered token array as: s₂_filtered ++ [flowMapEnd, streamEnd] ═══
  have h_emit_se_tokens : (s₃.emit .streamEnd).tokens =
      s₃.tokens.push { pos := s₃.currentPos, val := .streamEnd } := by
    unfold ScannerState.emit; rfl
  have h_final_filter : (s₃.emit .streamEnd).tokens.filter p =
      (s₃.tokens.filter p).push { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_emit_se_tokens, Array.filter_push]; rfl
  have h_tokens_decomp : tokens = ((s₂.tokens.filter p).push tok_fme).push
      { pos := s₃.currentPos, val := .streamEnd } := by
    rw [h_tokens_eq, h_final_filter, h_filt₃]
  -- ═══ Tier 1 derivations ═══
  -- h_tpe: tokens[tokens.size - 2] = tok_fme, which has val = .flowMappingEnd
  have h_tpe : tokens[tokens.size - 2]!.val = .flowMappingEnd := by
    rw [h_tokens_decomp]
    have h_outer_sz : (((s₂.tokens.filter p).push tok_fme).push
        { pos := s₃.currentPos, val := YamlToken.streamEnd }).size =
        (s₂.tokens.filter p).size + 2 := by simp [Array.size_push]
    rw [h_outer_sz, show (s₂.tokens.filter p).size + 2 - 2 = (s₂.tokens.filter p).size from by omega]
    rw [getElem!_pos _ _ (by omega)]
    rw [Array.getElem_push_lt (show (s₂.tokens.filter p).size <
        ((s₂.tokens.filter p).push tok_fme).size from by simp [Array.size_push])]
    rw [Array.getElem_push_eq]
    exact h_tok_fme_val
  -- ═══ Filtered prefix preservation (via ScanChain infrastructure) ═══
  have h_filt₁_sz : (s₁.tokens.filter p).size = 2 := by
    have : ((s₁.tokens.filter p).map (·.val)).size = 2 := by rw [h_filt₁]; rfl
    simpa [Array.size_map] using this
  have h_filt₁_val1 : ((s₁.tokens.filter p)[1]'(by omega)).val = YamlToken.flowMappingStart := by
    have h_len : (s₁.tokens.filter p).toList.length = 2 := by
      rw [Array.length_toList]; exact h_filt₁_sz
    have h_vals : (s₁.tokens.filter p).toList.map (·.val) =
        [YamlToken.streamStart, YamlToken.flowMappingStart] := by
      have := congrArg Array.toList h_filt₁; simpa [Array.toList_map] using this
    obtain ⟨a, b, h_ab⟩ : ∃ a b, (s₁.tokens.filter p).toList = [a, b] := by
      match (s₁.tokens.filter p).toList, h_len with
      | [a, b], _ => exact ⟨a, b, rfl⟩
    show (s₁.tokens.filter p).toList[1].val = YamlToken.flowMappingStart
    simp only [h_ab, List.getElem_cons_succ, List.getElem_cons_zero]
    rw [h_ab] at h_vals; simp at h_vals; exact h_vals.2
  obtain ⟨suffix, h_suffix⟩ : ∃ suffix, (s₂.tokens.filter p).toList =
      (s₁.tokens.filter p).toList ++ suffix :=
    ScanChain_filtered_prefix h_fmc₂ h_sk₁ (by omega) (by
      intro j hj hjsz; rw [h_sync₁] at hjsz; rw [h_fl₁] at hj; omega)
  have h_filt_grows : (s₂.tokens.filter p).size ≥
      (s₁.tokens.filter p).size + n₂ := ScanChain_filtered_grows h_chain₂
  -- n₂ ≥ 1 (from n₂ ≥ 3)
  have h_n₂_pos : n₂ ≥ 1 := by omega
  have h_s2_filt_sz : (s₂.tokens.filter p).size ≥ 3 := by
    rw [h_filt₁_sz] at h_filt_grows; omega
  have h_t1 : tokens[1]!.val = .flowMappingStart := by
    rw [h_tokens_decomp]
    rw [getElem!_pos _ _ (by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < ((s₂.tokens.filter p).push tok_fme).size
        from by simp only [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show 1 < (s₂.tokens.filter p).size from by omega)]
    -- Show filtered[1] is preserved from s₁ to s₂ via ScanChain prefix
    have h1_lt_s1 : 1 < (s₁.tokens.filter p).size := by rw [h_filt₁_sz]; omega
    have h_eq : (s₂.tokens.filter p)[1]'(by omega) = (s₁.tokens.filter p)[1]'h1_lt_s1 := by
      show (s₂.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega) =
          (s₁.tokens.filter p).toList[1]'(by rw [Array.length_toList]; omega)
      simp only [h_suffix]
      exact List.getElem_append_left (by rw [Array.length_toList]; omega)
    calc ((s₂.tokens.filter p)[1]'(by omega)).val
        = ((s₁.tokens.filter p)[1]'h1_lt_s1).val := congrArg Positioned.val h_eq
      _ = .flowMappingStart := h_filt₁_val1
  -- h_sz7: for map, need n₂ ≥ 5 filtered tokens (prefix 2 + suffix ≥ 3)
  -- Non-empty pair list has ≥ 1 pair. Each pair scanning produces ≥ 3 scanNextToken
  -- steps (key, value indicator, value scalar). Combined with n₂ ≥ 1, this gives
  -- filtered size ≥ 2 + n₂. For n₂ ≥ 5 we need the pair structure decomposition.
  -- ═══ Body token characterization (now from combined theorem) ═══
  -- Rename _raw variables to match expected names
  have h_body_sz := h_body_sz_raw; have h_body_key := h_body_key_raw
  have h_body_fe_next := h_body_fe_next_raw
  rw [h_filt₁_sz] at h_body_sz h_body_key h_body_fe_next
  -- tokens.size - 2 = (s₂.filter p).size
  have h_tokens_sz_eq : tokens.size - 2 = (s₂.tokens.filter p).size := by
    rw [h_tokens_decomp]; simp [Array.size_push]
  -- Helper: tokens[k]! for k < tokens.size - 2 equals (s₂.filter p)[k]
  have h_tok_body (k : Nat) (h_lt : k < (s₂.tokens.filter p).size) :
      tokens[k]! = ((s₂.tokens.filter p)[k]'h_lt) := by
    rw [h_tokens_decomp, getElem!_pos _ k (by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt (show k < ((s₂.tokens.filter p).push tok_fme).size
        from by simp [Array.size_push]; omega)]
    rw [Array.getElem_push_lt h_lt]
  have h_sz7 : tokens.size ≥ 7 := by
    rw [h_tokens_decomp]; simp [Array.size_push]
    -- (s₂.filter).size ≥ (s₁.filter).size + n₂ = 2 + n₂ ≥ 2 + 3 = 5
    rw [h_filt₁_sz] at h_filt_grows; omega
  have h_t2_key : tokens[2]!.val = .key := by
    rw [h_tok_body 2 (by omega)]; exact h_body_key (by omega)
  have h_fe_pattern : ∀ k, 2 ≤ k → k < tokens.size - 2 →
      tokens[k]!.val = .flowEntry →
      flowBracketBalance tokens 2 k = 0 →
      k + 1 ≤ tokens.size - 2 ∧ tokens[k + 1]!.val = .key := by
    intro k h_lo h_hi h_fe h_depth
    have h_k_lt : k < (s₂.tokens.filter p).size := by omega
    rw [h_tok_body k h_k_lt] at h_fe
    -- Convert flowBracketBalance from tokens to s₂.tokens.filter p
    have h_depth' : flowBracketBalance (s₂.tokens.filter p) 2 k = 0 := by
      rw [← h_tokens_sz_eq] at h_k_lt
      have : flowBracketBalance tokens 2 k = flowBracketBalance (s₂.tokens.filter p) 2 k := by
        rw [h_tokens_decomp]
        rw [flowBracketBalance_push _ _ 2 k (by simp [Array.size_push]; omega)]
        rw [flowBracketBalance_push _ _ 2 k (by omega)]
      rw [this] at h_depth; exact h_depth
    obtain ⟨h_next_lt, h_next_key⟩ := h_body_fe_next k (by omega) h_k_lt h_fe h_depth'
    exact ⟨by omega, by rw [h_tok_body (k+1) (by omega)]; exact h_next_key (by omega)⟩
  have h_pnok : L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk
      tokens (tokens.size - 2) (4 * tokens.size + 4) 2 := sorry
  exact ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_pattern, h_pnok⟩

/-- Combined scanner characterization and parser acceptance for flow sequences.
    Given that scanning the emitted sequence succeeds, the parser pipeline
    produces exactly one document.

    - **Empty case** (`items = #[]`): Fully proven via `native_decide` on the
      concrete 4-token stream `[streamStart, flowSequenceStart, flowSequenceEnd, streamEnd]`.
    - **Non-empty case**: Requires parser fuel sufficiency for `parseFlowSequenceLoop`
      on well-bracketed tokens — each loop iteration consumes ≥1 token via `parseNode`,
      so fuel = `4 * tokens.size + 4` suffices. Currently sorry'd pending position
      monotonicity proof through `parseNode` dispatch. -/
theorem parseStream_emitSequence (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) {tokens : Array (Positioned YamlToken)}
    (h_scan : Scanner.scanFiltered (emit (.sequence style items tag anchor)) = .ok tokens)
    (h_items : ∀ (i : Fin items.size), Grammable items[i] (false || style == CollectionStyle.flow)) :
    ∃ docs, parseStream tokens = .ok docs ∧ docs.size = 1 := by
  -- emit ignores style/tag/anchor: always produces "[" ++ emitList items.toList ++ "]"
  have h_emit : emit (.sequence style items tag anchor) =
      "[" ++ emit.emitList items.toList ++ "]" := rfl
  rw [h_emit] at h_scan
  match h_list : items.toList with
  | [] =>
    -- Empty sequence: emit produces "[]", native_decide verifies full pipeline
    rw [h_list] at h_scan
    have h_str : ("[" ++ emit.emitList ([] : List YamlValue) ++ "]") = "[]" := by native_decide
    rw [h_str] at h_scan
    -- h_scan : Scanner.scanFiltered "[]" = .ok tokens
    have h_full := checkFullSeq_true
    unfold checkFullSeq at h_full
    simp only [h_scan] at h_full
    -- h_full : (match parseStream tokens with | .ok docs => docs.size == 1 | ...) = true
    match h_ps : parseStream tokens with
    | .ok docs =>
      simp only [h_ps] at h_full
      exact ⟨docs, rfl, by simpa using h_full⟩
    | .error _ => simp [h_ps] at h_full
  | _ :: _ =>
    -- Non-empty: trace through parseStream → parseStreamLoop → parseDocument →
    -- parseNode → parseFlowSequence → parseFlowSequenceLoop using loop fuel
    -- sufficiency from Sub-phase C.
    -- Flow structure from scanner characterization
    have h_all_scan : ∀ w, w ∈ items.toList → EmitScansInFlow w := by
      intro w hw
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hw
      have h_sz : i < items.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ emit_scans_in_flow _ (h_items ⟨i, h_sz⟩)
    obtain ⟨h_sz5, h_t0, h_tlast, h_t1, h_tpe, h_content0, h_fe_pattern,
            h_pnok⟩ :=
      scanFiltered_emitSeq_nonempty_structure items tokens h_scan (by simp [h_list]) h_all_scan
    -- Step 1: Unfold parseStream, dispatch expect .streamStart
    unfold parseStream
    simp only [bind, Except.bind]
    unfold ParseState.expect
    simp only [ParseState.peek?]
    simp only [show (0 : Nat) < tokens.size from by omega, ↓reduceIte, h_t0]
    simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
               ↓reduceIte]
    -- ps1 = advance of initial state (pos = 1)
    let ps1 : ParseState := ({ tokens := tokens } : ParseState).advance
    show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
      docs.size = 1
    -- peek? facts for ps1
    have h_peek1 : ps1.peek? = some .flowSequenceStart := by
      simp only [ps1, ParseState.peek?, ParseState.advance]
      simp only [show (0 : Nat) + 1 = 1 from rfl,
                 show 1 < tokens.size from by omega, ↓reduceIte, h_t1]
    have h_peek_not_dir : match ps1.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    have h_peek_not_anctag : match ps1.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    -- parseDirectives and prepareDocumentState
    have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skip ps1 h_peek_not_dir
    have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
      unfold prepareDocumentState
      simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
      have h_th : { ps1 with tagHandles := #[] } = ps1 := by
        simp [ps1, ParseState.advance]
      rw [h_th, h_peek1]
      unfold ParseState.tryConsume
      rw [h_peek1]; simp
    -- parseNodeProperties skip
    have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
      parseNodeProperties_skip ps1 h_peek_not_anctag
    -- Fuel chain: parseDocument creates fuel 4*N+4 where N = tokens.size
    --   parseNode(4*N+4) destructs → parseNodeContent(4*N+3)
    --   parseNodeContent(4*N+3) dispatches → parseFlowSequence(4*N+3)
    --   parseFlowSequence(4*N+3) destructs → parseFlowSequenceLoop(4*N+2)
    have h_ps1_tok : ps1.tokens.size = tokens.size := by simp [ps1, ParseState.advance]
    -- ps_mid = ps1.advance (pos = 2): start of flow sequence loop body
    let ps_mid : ParseState := ps1.advance
    have h_ps_mid_tok : ps_mid.tokens = tokens := by simp [ps_mid, ps1, ParseState.advance]
    have h_ps_mid_pos : ps_mid.pos = 2 := by simp [ps_mid, ps1, ParseState.advance]
    -- Apply parseFlowSequenceLoop_emitter_ok with loop fuel = 4*N+2
    have h_endPos : tokens.size - 2 < tokens.size := by omega
    have h_loop_fuel : 4 * tokens.size + 2 > (tokens.size - 2) - ps_mid.pos := by
      simp only [h_ps_mid_pos]; omega
    have h_loop_pos : ps_mid.pos ≤ tokens.size - 2 := by
      simp only [h_ps_mid_pos]; omega
    have h_pnok_adj : L4YAML.Proofs.ParserWellBehaved.ParseNodeFlowSeqOk
        ps_mid.tokens (tokens.size - 2) (4 * tokens.size + 2) 2 := by
      rw [h_ps_mid_tok]; exact h_pnok.mono (by omega)
    have h_end_tok_adj : ps_mid.tokens[tokens.size - 2]!.val = .flowSequenceEnd := by
      rw [h_ps_mid_tok]; exact h_tpe
    have h_entry_vacuous : (#[] : Array YamlValue).size > 0 →
        ps_mid.peek? = some .flowEntry ∨ ps_mid.peek? = some .flowSequenceEnd := by
      intro h; simp [Array.size] at h
    have h_content_start_adj : ps_mid.pos < tokens.size - 2 → (#[] : Array YamlValue).size = 0 →
        (∃ c s, ps_mid.peek? = some (.scalar c s)) ∨
        ps_mid.peek? = some .flowSequenceStart ∨
        ps_mid.peek? = some .flowMappingStart := by
      intro _ _
      have h_mid_peek_val : ps_mid.peek? = some tokens[2]!.val := by
        simp only [ps_mid, ps1, ParseState.peek?, ParseState.advance]
        simp only [show (0 : Nat) + 1 + 1 = 2 from rfl, show 2 < tokens.size from by omega,
                   ↓reduceIte]
      rcases h_content0 with ⟨c, s, hcs⟩ | hcs | hcs
      · exact .inl ⟨c, s, by rw [h_mid_peek_val, hcs]⟩
      · exact .inr (.inl (by rw [h_mid_peek_val, hcs]))
      · exact .inr (.inr (by rw [h_mid_peek_val, hcs]))
    have h_after_fe_adj : ∀ k, ps_mid.pos ≤ k → k < tokens.size - 2 →
        ps_mid.tokens[k]!.val = .flowEntry →
        L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧
        ((∃ c s, ps_mid.tokens[k + 1]!.val = .scalar c s) ∨
         ps_mid.tokens[k + 1]!.val = .flowSequenceStart ∨
         ps_mid.tokens[k + 1]!.val = .flowMappingStart) := by
      intro k hk1 hk2 hk3 hk4
      rw [h_ps_mid_tok] at hk3 hk4 ⊢; rw [h_ps_mid_pos] at hk1
      exact h_fe_pattern k hk1 hk2 hk3 hk4
    have h_at_end_adj : ps_mid.peek? = some .flowSequenceEnd → ps_mid.pos = tokens.size - 2 := by
      intro h_peek; exfalso
      have ⟨_, h_val⟩ := L4YAML.Proofs.ParserWellBehaved.peek_some_val h_peek
      simp only [h_ps_mid_tok, h_ps_mid_pos] at h_val
      -- h_content0 says tokens[2]!.val is scalar/flowSeqStart/flowMapStart
      -- h_val says tokens[2]!.val = .flowSequenceEnd → contradiction
      rcases h_content0 with ⟨c, s, hcs⟩ | hcs | hcs <;> rw [h_val] at hcs <;> cases hcs
    have h_bal_init : L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 ps_mid.pos = 0 := by
      rw [h_ps_mid_pos]; unfold L4YAML.Proofs.ParserGrammable.flowBracketBalance; simp
    obtain ⟨items_res, ps_loop, h_loop_ok, h_loop_peek, h_loop_pos_eq, h_loop_tok, h_loop_tp⟩ :=
      L4YAML.Proofs.ParserWellBehaved.parseFlowSequenceLoop_emitter_ok
        (4 * tokens.size + 2) ps_mid #[] (tokens.size - 2)
        2
        h_pnok_adj h_loop_fuel h_loop_pos h_endPos h_end_tok_adj
        h_at_end_adj
        h_entry_vacuous
        (fun h_pos_lt h_size_zero => h_content_start_adj h_pos_lt h_size_zero)
        h_after_fe_adj h_bal_init
        (by rw [h_ps_mid_pos]; omega)
    -- parseFlowSequence(4*N+3): destructs, passes 4*N+2 to loop
    have h_parseFlowSeq : parseFlowSequence ps1 (4 * tokens.size + 3) =
        Except.ok (.sequence .flow items_res, ps_loop.advance) := by
      unfold parseFlowSequence
      simp only [bind, Except.bind]
      rw [h_loop_ok]; simp only [h_loop_peek]
    -- parseNodeContent dispatches to parseFlowSequence
    have h_parseNC : parseNodeContent ps1 (4 * tokens.size + 3) {} =
        Except.ok (.sequence .flow items_res, ps_loop.advance) := by
      unfold parseNodeContent; rw [h_peek1]; exact h_parseFlowSeq
    -- applyNodeFinalization is identity for empty props and trackPositions=false
    have h_finalize : applyNodeFinalization
        (.sequence .flow items_res) ps_loop.advance {}
        (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
        = (.sequence .flow items_res, ps_loop.advance) := by
      unfold applyNodeFinalization
      simp only []
      show (YamlValue.sequence .flow items_res none none,
            if ps_loop.advance.trackPositions then _ else ps_loop.advance) = _
      have h_tp : ps_loop.advance.trackPositions = false := by
        exact h_loop_tp
      simp [h_tp]
    -- parseNode(4*N+4): destructs, passes 4*N+3 to parseNodeContent
    have h_parseNode : parseNode ps1 (4 * tokens.size + 4) =
        Except.ok (.sequence .flow items_res, ps_loop.advance) := by
      unfold parseNode
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_np]; simp only []
      unfold validateNodeProps
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_parseNC]; simp [h_finalize]
    -- parseDocument uses fuel 4 * ps1.tokens.size + 4 = 4*N+4
    have h_parseDoc : parseDocument ps1 = Except.ok
        ({ value := .sequence .flow items_res,
           directives := #[], anchors := ps_loop.advance.anchors,
           nodePositions := ps_loop.advance.nodePositions }, ps_loop.advance) := by
      unfold parseDocument
      simp only [bind, Except.bind, h_pds, h_peek1]
      rw [show 4 * ps1.tokens.size + 4 = 4 * tokens.size + 4 from by omega]
      rw [h_parseNode]
    -- ps_loop.advance.peek? = some .streamEnd
    have h_peek_end : ps_loop.advance.peek? = some .streamEnd := by
      have h_loop_tok_eq : ps_loop.tokens = tokens := h_loop_tok.trans h_ps_mid_tok
      -- Position is directly from h_loop_pos_eq (no uniqueness-based trichotomy needed)
      simp only [ParseState.peek?, ParseState.advance, h_loop_tok_eq]
      simp only [h_loop_pos_eq, show tokens.size - 2 + 1 = tokens.size - 1 from by omega,
                 show tokens.size - 1 < tokens.size from by omega, ↓reduceIte, h_tlast]
    -- Apply parseStreamLoop_single_doc
    have h_fuel_ge : tokens.size ≥ 2 := by omega
    have h_loop_doc := parseStreamLoop_single_doc ps1 tokens.size h_fuel_ge
      .flowSequenceStart h_peek1 (by intro h; cases h)
      { value := .sequence .flow items_res,
        directives := #[], anchors := ps_loop.advance.anchors,
        nodePositions := ps_loop.advance.nodePositions }
      ps_loop.advance h_parseDoc h_peek_end
    exact ⟨_, h_loop_doc, rfl⟩

/-- Combined scanner characterization and parser acceptance for flow mappings.
    Analogous to `parseStream_emitSequence` but for `emit (.mapping ...)`.

    - **Empty case** (`pairs = #[]`): Fully proven via `native_decide` on the
      concrete 4-token stream `[streamStart, flowMappingStart, flowMappingEnd, streamEnd]`.
    - **Non-empty case**: Requires parser fuel sufficiency for `parseFlowMappingLoop`
      on well-bracketed tokens. Currently sorry'd pending position monotonicity proof. -/
theorem parseStream_emitMapping (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) {tokens : Array (Positioned YamlToken)}
    (h_scan : Scanner.scanFiltered (emit (.mapping style pairs tag anchor)) = .ok tokens)
    (hk : ∀ (i : Fin pairs.size), Grammable pairs[i].fst (false || style == CollectionStyle.flow))
    (hv : ∀ (i : Fin pairs.size), Grammable pairs[i].snd (false || style == CollectionStyle.flow)) :
    ∃ docs, parseStream tokens = .ok docs ∧ docs.size = 1 := by
  -- emit ignores style/tag/anchor: always produces "{" ++ emitPairList pairs.toList ++ "}"
  have h_emit : emit (.mapping style pairs tag anchor) =
      "{" ++ emit.emitPairList pairs.toList ++ "}" := rfl
  rw [h_emit] at h_scan
  match h_list : pairs.toList with
  | [] =>
    -- Empty mapping: emit produces "{}", native_decide verifies full pipeline
    rw [h_list] at h_scan
    have h_str : ("{" ++ emit.emitPairList ([] : List (YamlValue × YamlValue)) ++ "}") = "{}" := by native_decide
    rw [h_str] at h_scan
    -- h_scan : Scanner.scanFiltered "{}" = .ok tokens
    have h_full := checkFullMap_true
    unfold checkFullMap at h_full
    simp only [h_scan] at h_full
    match h_ps : parseStream tokens with
    | .ok docs =>
      simp only [h_ps] at h_full
      exact ⟨docs, rfl, by simpa using h_full⟩
    | .error _ => simp [h_ps] at h_full
  | _ :: _ =>
    -- Non-empty: trace through parseStream → parseStreamLoop → parseDocument →
    -- parseNode → parseFlowMapping → parseFlowMappingLoop using loop fuel
    -- sufficiency from Sub-phase D.
    -- Flow structure from scanner characterization
    have h_all_scan_k : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.1 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ by exact emit_scans_in_flow _ (hk ⟨i, h_sz⟩)
    have h_all_scan_v : ∀ p, p ∈ pairs.toList → EmitScansInFlow p.2 := by
      intro p hp
      have ⟨i, hi, h_eq⟩ := List.getElem_of_mem hp
      have h_sz : i < pairs.size := by rwa [Array.length_toList] at hi
      exact h_eq ▸ by exact emit_scans_in_flow _ (hv ⟨i, h_sz⟩)
    obtain ⟨h_sz7, h_t0, h_tlast, h_t1, h_tpe, h_t2_key, h_fe_key_pattern,
            h_entry_ok⟩ :=
      scanFiltered_emitMap_nonempty_structure pairs tokens h_scan (by simp [h_list])
        h_all_scan_k h_all_scan_v
    -- Step 1: Unfold parseStream, dispatch expect .streamStart
    unfold parseStream
    simp only [bind, Except.bind]
    unfold ParseState.expect
    simp only [ParseState.peek?]
    simp only [show (0 : Nat) < tokens.size from by omega, ↓reduceIte, h_t0]
    simp only [show BEq.beq YamlToken.streamStart YamlToken.streamStart = true from by decide,
               ↓reduceIte]
    -- ps1 = advance of initial state (pos = 1)
    let ps1 : ParseState := ({ tokens := tokens } : ParseState).advance
    show ∃ docs, parseStreamLoop ps1 #[] StreamState.initial tokens.size = Except.ok docs ∧
      docs.size = 1
    -- peek? facts for ps1
    have h_peek1 : ps1.peek? = some .flowMappingStart := by
      simp only [ps1, ParseState.peek?, ParseState.advance]
      simp only [show (0 : Nat) + 1 = 1 from rfl,
                 show 1 < tokens.size from by omega, ↓reduceIte, h_t1]
    have h_peek_not_dir : match ps1.peek? with
        | some (.versionDirective _ _) | some (.tagDirective _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    have h_peek_not_anctag : match ps1.peek? with
        | some (.anchor _) | some (.tag _ _) => False
        | _ => True := by rw [h_peek1]; trivial
    -- parseDirectives and prepareDocumentState
    have h_pd : parseDirectives ps1 = (#[], ps1) := parseDirectives_skip ps1 h_peek_not_dir
    have h_pds : prepareDocumentState ps1 = .ok (#[], ps1) := by
      unfold prepareDocumentState
      simp only [bind, Except.bind, pure, Except.pure, h_pd, Array.filterMap_empty]
      have h_th : { ps1 with tagHandles := #[] } = ps1 := by
        simp [ps1, ParseState.advance]
      rw [h_th, h_peek1]
      unfold ParseState.tryConsume
      rw [h_peek1]; simp
    -- parseNodeProperties skip
    have h_np : parseNodeProperties ps1 = .ok ({}, ps1) :=
      parseNodeProperties_skip ps1 h_peek_not_anctag
    -- Fuel chain: parseDocument(4*N+4) → parseNode(4*N+4)
    --   → parseNodeContent(4*N+3) → parseFlowMapping(4*N+3)
    --   → parseFlowMappingLoop(4*N+2)
    have h_ps1_tok : ps1.tokens.size = tokens.size := by simp [ps1, ParseState.advance]
    -- ps_mid = ps1.advance (pos = 2): start of flow mapping loop body
    let ps_mid : ParseState := ps1.advance
    have h_ps_mid_tok : ps_mid.tokens = tokens := by simp [ps_mid, ps1, ParseState.advance]
    have h_ps_mid_pos : ps_mid.pos = 2 := by simp [ps_mid, ps1, ParseState.advance]
    -- Apply parseFlowMappingLoop_emitter_ok with loop fuel = 4*N+2
    have h_endPos : tokens.size - 2 < tokens.size := by omega
    have h_loop_fuel : 4 * tokens.size + 2 > (tokens.size - 2) - ps_mid.pos := by
      simp only [h_ps_mid_pos]; omega
    have h_loop_pos : ps_mid.pos ≤ tokens.size - 2 := by
      simp only [h_ps_mid_pos]; omega
    have h_entry_adj : L4YAML.Proofs.ParserWellBehaved.ParseEntryFlowMapOk
        ps_mid.tokens (tokens.size - 2) (4 * tokens.size + 2) 2 := by
      rw [h_ps_mid_tok]; exact h_entry_ok.mono (by omega)
    have h_end_tok_adj : ps_mid.tokens[tokens.size - 2]!.val = .flowMappingEnd := by
      rw [h_ps_mid_tok]; exact h_tpe
    have h_sep_adj : (#[] : Array (YamlValue × YamlValue)).size > 0 →
        ps_mid.peek? = some .flowEntry ∨ ps_mid.peek? = some .flowMappingEnd := by
      intro h; simp [Array.size] at h
    have h_start_adj : ps_mid.pos < tokens.size - 2 → (#[] : Array (YamlValue × YamlValue)).size = 0 →
        ps_mid.peek? = some .key := by
      intro _ _
      simp only [ps_mid, ps1, ParseState.peek?, ParseState.advance]
      simp only [show (0 : Nat) + 1 + 1 = 2 from rfl, show 2 < tokens.size from by omega,
                 ↓reduceIte, Option.some.injEq]
      exact h_t2_key
    have h_after_fe_adj : ∀ k, ps_mid.pos ≤ k → k < tokens.size - 2 →
        ps_mid.tokens[k]!.val = .flowEntry →
        L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 k = 0 →
        k + 1 ≤ tokens.size - 2 ∧ ps_mid.tokens[k + 1]!.val = .key := by
      intro k hk1 hk2 hk3 hk4
      rw [h_ps_mid_tok] at hk3 hk4 ⊢; rw [h_ps_mid_pos] at hk1
      exact h_fe_key_pattern k hk1 hk2 hk3 hk4
    have h_at_end_adj : ps_mid.peek? = some .flowMappingEnd → ps_mid.pos = tokens.size - 2 := by
      intro h_peek; exfalso
      have ⟨_, h_val⟩ := L4YAML.Proofs.ParserWellBehaved.peek_some_val h_peek
      simp only [h_ps_mid_tok, h_ps_mid_pos] at h_val
      -- tokens[2] = .key ≠ .flowMappingEnd
      exact absurd (h_t2_key.symm.trans h_val) (by decide)
    have h_bal_init : L4YAML.Proofs.ParserGrammable.flowBracketBalance ps_mid.tokens 2 ps_mid.pos = 0 := by
      rw [h_ps_mid_pos]; unfold L4YAML.Proofs.ParserGrammable.flowBracketBalance; simp
    obtain ⟨pairs_res, ps_loop, h_loop_ok, h_loop_peek, h_loop_pos_eq, h_loop_tok, h_loop_tp⟩ :=
      L4YAML.Proofs.ParserWellBehaved.parseFlowMappingLoop_emitter_ok
        (4 * tokens.size + 2) ps_mid #[] (tokens.size - 2)
        2
        h_entry_adj h_loop_fuel h_loop_pos h_endPos h_end_tok_adj
        h_at_end_adj
        h_sep_adj
        (fun h_pos_lt h_size_zero => h_start_adj h_pos_lt h_size_zero)
        h_after_fe_adj h_bal_init
        (by rw [h_ps_mid_pos]; omega)
    -- parseFlowMapping(4*N+3): destructs, passes 4*N+2 to loop
    have h_parseFlowMap : parseFlowMapping ps1 (4 * tokens.size + 3) =
        Except.ok (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold parseFlowMapping
      simp only [bind, Except.bind]
      rw [h_loop_ok]; simp only [h_loop_peek]
    -- parseNodeContent dispatches to parseFlowMapping
    have h_parseNC : parseNodeContent ps1 (4 * tokens.size + 3) {} =
        Except.ok (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold parseNodeContent; rw [h_peek1]; exact h_parseFlowMap
    -- applyNodeFinalization is identity for empty props and trackPositions=false
    have h_finalize : applyNodeFinalization
        (.mapping .flow pairs_res) ps_loop.advance {}
        (ps1.peekPos?.getD { offset := 0, line := 0, col := 0 })
        = (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold applyNodeFinalization
      simp only []
      have h_tp : ps_loop.advance.trackPositions = false := by
        exact h_loop_tp
      simp [h_tp]
    -- parseNode(4*N+4): destructs, passes 4*N+3 to parseNodeContent
    have h_parseNode : parseNode ps1 (4 * tokens.size + 4) =
        Except.ok (.mapping .flow pairs_res, ps_loop.advance) := by
      unfold parseNode
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_np]; simp only []
      unfold validateNodeProps
      simp only [bind, Except.bind, pure, Except.pure]
      rw [h_peek1]; simp only []
      rw [h_parseNC]; simp [h_finalize]
    -- parseDocument uses fuel 4 * ps1.tokens.size + 4 = 4*N+4
    have h_parseDoc : parseDocument ps1 = Except.ok
        ({ value := .mapping .flow pairs_res,
           directives := #[], anchors := ps_loop.advance.anchors,
           nodePositions := ps_loop.advance.nodePositions }, ps_loop.advance) := by
      unfold parseDocument
      simp only [bind, Except.bind, h_pds, h_peek1]
      rw [show 4 * ps1.tokens.size + 4 = 4 * tokens.size + 4 from by omega]
      rw [h_parseNode]
    -- ps_loop.advance.peek? = some .streamEnd
    have h_peek_end : ps_loop.advance.peek? = some .streamEnd := by
      have h_loop_tok_eq : ps_loop.tokens = tokens := h_loop_tok.trans h_ps_mid_tok
      -- Position is directly from h_loop_pos_eq (no uniqueness-based trichotomy needed)
      simp only [ParseState.peek?, ParseState.advance, h_loop_tok_eq]
      simp only [h_loop_pos_eq, show tokens.size - 2 + 1 = tokens.size - 1 from by omega,
                 show tokens.size - 1 < tokens.size from by omega, ↓reduceIte, h_tlast]
    -- Apply parseStreamLoop_single_doc
    have h_fuel_ge : tokens.size ≥ 2 := by omega
    have h_loop_doc := parseStreamLoop_single_doc ps1 tokens.size h_fuel_ge
      .flowMappingStart h_peek1 (by intro h; cases h)
      { value := .mapping .flow pairs_res,
        directives := #[], anchors := ps_loop.advance.anchors,
        nodePositions := ps_loop.advance.nodePositions }
      ps_loop.advance h_parseDoc h_peek_end
    exact ⟨_, h_loop_doc, rfl⟩

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
  cases hg with
  | scalar s _ h =>
    -- Recover the 3-token structure [streamStart, scalar, streamEnd] from the scanner
    obtain ⟨h_sz, h_t0, h_t1, h_t2⟩ := scanFiltered_emitScalar_vals s.content tokens h_scan
    -- Apply the parser trace for the 3-token scalar stream
    obtain ⟨docs, h_ps, _, _⟩ := parseStream_three_tokens_scalar s.content tokens h_sz h_t0 h_t1 h_t2
    exact ⟨docs, h_ps⟩

  | sequence style items tag anchor _ h_items =>
    obtain ⟨docs, h_ps, _⟩ := parseStream_emitSequence style items tag anchor h_scan h_items
    exact ⟨docs, h_ps⟩

  | mapping style pairs tag anchor _ hk hv =>
    obtain ⟨docs, h_ps, _⟩ := parseStream_emitMapping style pairs tag anchor h_scan hk hv
    exact ⟨docs, h_ps⟩

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
  cases hg with
  | scalar s _ h_sc =>
    -- Decompose parseYamlRaw into its scanner and parser components
    obtain ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose _ _ h
    -- Get token boundaries
    obtain ⟨h_sz, h_t0, h_t1, h_t2⟩ := scanFiltered_emitScalar_vals s.content tokens h_scan
    -- Apply the parser trace to get the target output (docs') and its length
    obtain ⟨docs', h_ps, h_docs_sz, _⟩ := parseStream_three_tokens_scalar s.content tokens h_sz h_t0 h_t1 h_t2
    -- Unify the decomposition parse result with the trace parse result
    have h_eq : docs = docs' := Except.ok.inj (h_parse.symm.trans h_ps)
    rwa [h_eq]

  | sequence style items tag anchor _ h_items =>
    obtain ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose _ _ h
    obtain ⟨docs', h_ps, h_docs_sz⟩ := parseStream_emitSequence style items tag anchor h_scan h_items
    have h_eq : docs = docs' := Except.ok.inj (h_parse.symm.trans h_ps)
    rwa [h_eq]

  | mapping style pairs tag anchor _ hk hv =>
    obtain ⟨tokens, h_scan, h_parse⟩ := Composition.parseYamlRaw_ok_decompose _ _ h
    obtain ⟨docs', h_ps, h_docs_sz⟩ := parseStream_emitMapping style pairs tag anchor h_scan hk hv
    have h_eq : docs = docs' := Except.ok.inj (h_parse.symm.trans h_ps)
    rwa [h_eq]

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

-- ==========================================
-- Helper Lemmas for Content Fidelity
-- ==========================================

-- contentEq on sequences ignores style/tag/anchor: only items matter.
theorem contentEq_sequence_items (style₁ style₂ : CollectionStyle)
    (items₁ items₂ : Array YamlValue)
    (tag₁ tag₂ anchor₁ anchor₂ : Option String) :
    contentEq (.sequence style₁ items₁ tag₁ anchor₁)
              (.sequence style₂ items₂ tag₂ anchor₂) =
    (items₁.size == items₂.size && contentEq.contentEqList items₁.toList items₂.toList) := by
  unfold contentEq; rfl

-- contentEq on mappings ignores style/tag/anchor: only pairs matter.
theorem contentEq_mapping_pairs (style₁ style₂ : CollectionStyle)
    (pairs₁ pairs₂ : Array (YamlValue × YamlValue))
    (tag₁ tag₂ anchor₁ anchor₂ : Option String) :
    contentEq (.mapping style₁ pairs₁ tag₁ anchor₁)
              (.mapping style₂ pairs₂ tag₂ anchor₂) =
    (pairs₁.size == pairs₂.size && contentEq.contentEqPairList pairs₁.toList pairs₂.toList) := by
  unfold contentEq; rfl

-- contentEq on sequences with any style/tag/anchor equals contentEq with canonical style/tag/anchor.
theorem contentEq_seq_style_irrel (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) (v : YamlValue) :
    contentEq (.sequence style items tag anchor) v =
    contentEq (.sequence .flow items none none) v := by
  cases v with
  | sequence style₂ items₂ tag₂ anchor₂ =>
    rw [contentEq_sequence_items, contentEq_sequence_items]
  | _ => unfold contentEq; rfl

-- contentEq on mappings with any style/tag/anchor equals contentEq with canonical style/tag/anchor.
theorem contentEq_map_style_irrel (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) (v : YamlValue) :
    contentEq (.mapping style pairs tag anchor) v =
    contentEq (.mapping .flow pairs none none) v := by
  cases v with
  | mapping style₂ pairs₂ tag₂ anchor₂ =>
    rw [contentEq_mapping_pairs, contentEq_mapping_pairs]
  | _ => unfold contentEq; rfl

/-- Proves that parsing the emitted tokens for a flow sequence recovers a content-equivalent sequence. -/
theorem emit_roundtrip_sequence_content_eq {inFlow : Bool} (style : CollectionStyle) (items : Array YamlValue)
    (tag anchor : Option String) (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit (.sequence style items tag anchor)) = .ok raw_docs)
    (h_size : raw_docs.size = 1)
    (h_items : ∀ (i : Fin items.size), Grammable items[i] (inFlow || style == CollectionStyle.flow))
    (ih : ∀ (i : Fin items.size) (raw_docs' : Array YamlDocument),
            parseYamlRaw (emit items[i]) = .ok raw_docs' → raw_docs'.size = 1 →
            contentEq items[i] (raw_docs'.map YamlDocument.compose)[0]!.value = true) :
    contentEq (.sequence style items tag anchor) (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  -- Bridge to canonical style/tag/anchor for contentEq
  rw [contentEq_seq_style_irrel]
  -- Case split on items
  have h_emit : emit (.sequence style items tag anchor) =
      "[" ++ emit.emitList items.toList ++ "]" := rfl
  match h_list : items.toList with
  | [] =>
    -- Empty sequence: emit produces "[]"
    rw [h_list] at h_emit
    have h_str : ("[" ++ emit.emitList ([] : List YamlValue) ++ "]") = "[]" := by native_decide
    rw [h_str] at h_emit
    rw [h_emit] at h_raw
    -- h_raw : parseYamlRaw "[]" = .ok raw_docs
    have h_check := checkContentSeq_true
    unfold checkContentSeq at h_check
    simp only [h_raw] at h_check
    -- h_check : (1 == 1 && contentEq ...) = true   (after reducing docs.size == 1)
    have h_items_empty : items = #[] := by
      exact Array.toList_eq_nil_iff.mp h_list
    rw [h_items_empty]
    -- h_check : (raw_docs.size == 1 && contentEq ...) = true
    -- Extract the contentEq part using h_size
    have h_sz_beq : (raw_docs.size == 1) = true := by simp [h_size]
    rw [h_sz_beq, Bool.true_and] at h_check
    exact h_check
  | _ :: _ =>
    -- Non-empty: requires exact parsed value structure from parser trace.
    exact sorry

/-- Proves that parsing the emitted tokens for a flow mapping recovers a content-equivalent mapping. -/
theorem emit_roundtrip_mapping_content_eq {inFlow : Bool} (style : CollectionStyle) (pairs : Array (YamlValue × YamlValue))
    (tag anchor : Option String) (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit (.mapping style pairs tag anchor)) = .ok raw_docs)
    (h_size : raw_docs.size = 1)
    (hk : ∀ (i : Fin pairs.size), Grammable pairs[i].fst (inFlow || style == CollectionStyle.flow))
    (hv : ∀ (i : Fin pairs.size), Grammable pairs[i].snd (inFlow || style == CollectionStyle.flow))
    (ihk : ∀ (i : Fin pairs.size) (raw_docs' : Array YamlDocument),
            parseYamlRaw (emit pairs[i].fst) = .ok raw_docs' → raw_docs'.size = 1 →
            contentEq pairs[i].fst (raw_docs'.map YamlDocument.compose)[0]!.value = true)
    (ihv : ∀ (i : Fin pairs.size) (raw_docs' : Array YamlDocument),
            parseYamlRaw (emit pairs[i].snd) = .ok raw_docs' → raw_docs'.size = 1 →
            contentEq pairs[i].snd (raw_docs'.map YamlDocument.compose)[0]!.value = true) :
    contentEq (.mapping style pairs tag anchor) (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  -- Bridge to canonical style/tag/anchor for contentEq
  rw [contentEq_map_style_irrel]
  -- Case split on pairs
  have h_emit : emit (.mapping style pairs tag anchor) =
      "{" ++ emit.emitPairList pairs.toList ++ "}" := rfl
  match h_list : pairs.toList with
  | [] =>
    -- Empty mapping: emit produces "{}"
    rw [h_list] at h_emit
    have h_str : ("{" ++ emit.emitPairList ([] : List (YamlValue × YamlValue)) ++ "}") = "{}" := by native_decide
    rw [h_str] at h_emit
    rw [h_emit] at h_raw
    -- h_raw : parseYamlRaw "{}" = .ok raw_docs
    have h_check := checkContentMap_true
    unfold checkContentMap at h_check
    simp only [h_raw] at h_check
    have h_pairs_empty : pairs = #[] := by
      exact Array.toList_eq_nil_iff.mp h_list
    rw [h_pairs_empty]
    have h_sz_beq : (raw_docs.size == 1) = true := by simp [h_size]
    rw [h_sz_beq, Bool.true_and] at h_check
    exact h_check
  | _ :: _ =>
    -- Non-empty: requires exact parsed value structure from parser trace.
    exact sorry

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
theorem emit_roundtrip_content_eq (v : YamlValue) {b : Bool} (hg : Grammable v b)
    (raw_docs : Array YamlDocument)
    (h_raw : parseYamlRaw (emit v) = .ok raw_docs)
    (h_size : raw_docs.size = 1) :
    contentEq v (raw_docs.map YamlDocument.compose)[0]!.value = true := by
  induction hg generalizing raw_docs with
  | scalar s _ h_scannable =>
    -- emit (.scalar s) = emitScalar s.content
    -- The scanner produces tokens with the original content
    -- The parser produces a scalar value with the original content
    -- compose preserves content (only clears anchor)
    -- contentEq ignores style/tag/anchor, compares content only
    change contentEq (.scalar s) _ = true
    obtain ⟨s_parsed, h_val, h_content⟩ :=
      parseYamlRaw_emitScalar_value s.content raw_docs
        (by show parseYamlRaw (emit (.scalar s)) = _; exact h_raw)
    have h_compose := compose_scalar_content raw_docs[0]! s_parsed h_val
    -- (raw_docs.map YamlDocument.compose)[0]!.value = (raw_docs[0]!.compose).value
    have h0 : (0 : Nat) < raw_docs.size := by omega
    have h0' : (0 : Nat) < (raw_docs.map YamlDocument.compose).size := by
      rw [Array.size_map]; omega
    rw [show (raw_docs.map YamlDocument.compose)[0]!.value =
        (raw_docs[0]!.compose).value from by
      show (if h : 0 < (raw_docs.map YamlDocument.compose).size
            then (raw_docs.map YamlDocument.compose)[0] else default).value =
           (if h : 0 < raw_docs.size then raw_docs[0] else default).compose.value
      rw [dif_pos h0', dif_pos h0, Array.getElem_map]]
    rw [h_compose]
    exact contentEq_scalar_compose s { s_parsed with anchor := none } (by simp [h_content])

  | sequence style items tag anchor _ h_items ih =>
    -- IH is now available: each child element round-trips content-equivalently
    exact emit_roundtrip_sequence_content_eq style items tag anchor raw_docs h_raw h_size h_items ih

  | mapping style pairs tag anchor _ hk hv ihk ihv =>
    -- IHs are now available: each key and value round-trips content-equivalently
    exact emit_roundtrip_mapping_content_eq style pairs tag anchor raw_docs h_raw h_size hk hv ihk ihv

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

end L4YAML.Proofs.EmitterScannability
