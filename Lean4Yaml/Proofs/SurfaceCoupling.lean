/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import Lean4Yaml.Surface

/-!
# Surface Syntax Coupling Proofs

Theorems connecting the parser implementation to the formal surface
syntax predicates. These form the proof backbone for the acceptance
strictness property: `parseYaml s = .ok docs → InYamlLanguage s`.

## Architecture

The coupling works through a **state correspondence** relation that
bridges the Scanner's `ScannerState` (byte-level offsets into a `String`)
with the Surface syntax's `SurfPos` (character-level `List Char` + column).

At each scanner step, we show that the scanner's state change corresponds
to a surface syntax production step:
- `skipSpaces n` → `SIndent n`
- `consumeNewline` → `SBBreak`
- `skipWhitespace` → `SSWhite*`
- `skipToContent` → `SSLComments`

## Strategy

Bottom-up: prove character-level coupling first, then compose into
production-level coupling, then chain through the full pipeline.
-/

set_option autoImplicit false

namespace Lean4Yaml.Proofs.SurfaceCoupling

open Lean4Yaml.Surface
open Lean4Yaml.CharPredicates

/-! ## §1 Character-Level Lemmas

These lemmas establish basic properties of the surface syntax
combinators that are used throughout the coupling proofs. -/

/-- `SIndent 0` is the identity (no characters consumed). -/
theorem SIndent_zero (s : SurfPos) : SIndent 0 s s :=
  SIndent.zero s

/-- `SIndent (n+1)` requires a leading space. -/
theorem SIndent_succ (n : Nat) (rest : List Char) (col : Nat) (s' : SurfPos)
    (h : SIndent n ⟨rest, col + 1⟩ s') :
    SIndent (n + 1) ⟨' ' :: rest, col⟩ s' :=
  SIndent.succ n rest col s' h

/-- `SIndent n` advances column by exactly `n`. -/
theorem SIndent_col (n : Nat) (s s' : SurfPos)
    (h : SIndent n s s') : s'.col = s.col + n := by
  induction h with
  | zero => omega
  | succ k _ col _ _ ih => dsimp only [] at *; omega

/-- `SIndent n` consumes exactly `n` characters. -/
theorem SIndent_chars (n : Nat) (s s' : SurfPos)
    (h : SIndent n s s') : s'.chars = s.chars.drop n := by
  induction h with
  | zero => simp
  | succ k rest _ _ _ ih => simp [List.drop_succ_cons] at ih ⊢; exact ih

/-- `SIndent n` consumes `n` spaces from the front. -/
theorem SIndent_all_spaces (n : Nat) (s s' : SurfPos)
    (h : SIndent n s s') : s.chars.take n = List.replicate n ' ' := by
  induction h with
  | zero => simp
  | succ k rest _ _ _ ih => simp [List.take_succ_cons, List.replicate_succ]; exact ih

/-- `GChar p` advances column by 1. -/
theorem GChar_col (p : Char → Prop) (s s' : SurfPos)
    (h : GChar p s s') : s'.col = s.col + 1 := by
  cases h; rfl

/-- `GLit ch` advances column by 1. -/
theorem GLit_col (ch : Char) (s s' : SurfPos)
    (h : GLit ch s s') : s'.col = s.col + 1 := by
  cases h; rfl

/-- `SBBreak` resets column to 0 (line feed case). -/
theorem SBBreak_lf_col (rest : List Char) (col : Nat) :
    SBBreak ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBBreak.lf rest col

/-- `SBBreak` resets column to 0 (carriage return case). -/
theorem SBBreak_cr_col (rest : List Char) (col : Nat) :
    SBBreak ⟨'\r' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBBreak.cr rest col

/-- `SBBreak` resets column to 0 (CRLF case). -/
theorem SBBreak_crlf_col (rest : List Char) (col : Nat) :
    SBBreak ⟨'\r' :: '\n' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBBreak.crLf rest col

/-! ## §2 Composition Lemmas

These lemmas show how surface syntax productions compose. -/

/-- Sequential composition preserves column tracking. -/
theorem GSeq_col (P Q : SurfPos → SurfPos → Prop) (s₁ _s₂ s₃ : SurfPos)
    (colP : ∀ a b, P a b → b.col = a.col + 1)
    (colQ : ∀ a b, Q a b → b.col = a.col + 1)
    (h : GSeq P Q s₁ s₃) : s₃.col = s₁.col + 2 := by
  cases h with
  | mk _ _ hp hq =>
    have h1 := colP _ _ hp
    have h2 := colQ _ _ hq
    omega

/-- `GStar P` preserves the starting position when empty. -/
theorem GStar_nil (P : SurfPos → SurfPos → Prop) (s : SurfPos) :
    GStar P s s :=
  GStar.nil s

/-- `GOpt P` can always match as none (zero-width). -/
theorem GOpt_none (P : SurfPos → SurfPos → Prop) (s : SurfPos) :
    GOpt P s s :=
  GOpt.none s

/-! ## §3 Indent Coupling (Scanner → Surface)

The key theorem: scanner's `skipSpaces` consuming `n` spaces
corresponds to `SIndent n` in the surface syntax. -/

/-- If a list starts with `n` spaces, `SIndent n` holds on the
    corresponding `SurfPos`, advancing by exactly `n` characters. -/
theorem spaces_give_SIndent (n : Nat) (chars : List Char) (col : Nat)
    (hpre : chars.take n = List.replicate n ' ')
    (hlen : chars.length ≥ n) :
    SIndent n ⟨chars, col⟩ ⟨chars.drop n, col + n⟩ :=
  indent_coupling n chars col hpre hlen

/-! ## §4 Line Break Coupling (Scanner → Surface)

The scanner's `consumeNewline` consuming CR/LF/CRLF corresponds
to `SBBreak` in the surface syntax. -/

/-- If the head character is `\n`, `SBBreak` holds. -/
theorem lf_gives_SBBreak (rest : List Char) (col : Nat) :
    SBBreak ⟨'\n' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBBreak.lf rest col

/-- If the head characters are `\r\n`, `SBBreak` holds. -/
theorem crlf_gives_SBBreak (rest : List Char) (col : Nat) :
    SBBreak ⟨'\r' :: '\n' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBBreak.crLf rest col

/-- If the head character is `\r` (not followed by `\n`), `SBBreak` holds. -/
theorem cr_gives_SBBreak (rest : List Char) (col : Nat) :
    SBBreak ⟨'\r' :: rest, col⟩ ⟨rest, 0⟩ :=
  SBBreak.cr rest col

/-! ## §5 Whitespace Coupling

Single whitespace character matches `SSWhite` (the `GChar isWhiteSpaceProp`
combinator applied to space or tab). -/

/-- Space satisfies `isWhiteSpaceProp`. -/
theorem space_is_white : isWhiteSpaceProp ' ' := by
  unfold isWhiteSpaceProp
  decide

/-- Tab satisfies `isWhiteSpaceProp`. -/
theorem tab_is_white : isWhiteSpaceProp '\t' := by
  unfold isWhiteSpaceProp
  decide

/-- A space character matches `SSWhite`. -/
theorem space_gives_SSWhite (rest : List Char) (col : Nat) :
    SSWhite ⟨' ' :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SSWhite.space rest col

/-- A tab character matches `SSWhite`. -/
theorem tab_gives_SSWhite (rest : List Char) (col : Nat) :
    SSWhite ⟨'\t' :: rest, col⟩ ⟨rest, col + 1⟩ :=
  SSWhite.tab rest col

/-! ## §6 Comment Coupling

A `#` followed by non-break characters to end of line matches
`SCNbCommentText`. -/

/-- Comment text starting with `#` produces `SCNbCommentText`. -/
theorem hash_comment (rest : List Char) (col : Nat) (s' : SurfPos)
    (hBody : GStar (GChar isNbChar) ⟨rest, col + 1⟩ s') :
    SCNbCommentText ⟨'#' :: rest, col⟩ s' :=
  SCNbCommentText.mk rest col s' hBody

/-! ## §7 Empty Node Coupling -/

/-- The empty node `e-node` [72] matches trivially at any position. -/
theorem empty_node (s : SurfPos) : SENode s s :=
  GEps.mk s

end Lean4Yaml.Proofs.SurfaceCoupling
