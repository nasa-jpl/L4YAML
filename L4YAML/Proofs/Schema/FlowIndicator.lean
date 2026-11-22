module

public import L4YAML.Schema.Schema
public meta import L4YAML.Schema.Schema
public import L4YAML.Spec.Types
public meta import L4YAML.Spec.Types

@[expose] public section Blanket

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# Flow Indicators Are Never Numbers

`adaptForFlowContext` double-quotes a plain scalar whose content contains a
flow indicator (`,` `[` `]` `{` `}`).  Under style-aware resolution a quoted
scalar is a string, so for that rewrite to preserve `resolve` the content must
already have been a string, i.e. no Core Schema spelling of null, bool, int or
float may contain a flow indicator.  This file proves that:

  `resolveImplicit_of_hasFlowIndicator : hasFlowIndicator c.toList = true →
     resolveImplicit c = .str c`

by showing that every recognizer (`isNull`, `isBool`, `isIntL`, `parseFloatL?`)
only accepts character lists drawn from a numeric alphabet with no indicator in
it.  The literal recognizers are finite case splits; the lexers are list
inductions over `isNatL.go`, `parseHex.go`, `parseOctal.go` and `splitOnChar`.
-/

namespace L4YAML.Schema

open L4YAML

/-! ## §1 — Flow indicator characters -/

/-- The five flow indicators, as a character predicate. -/
def isFlowIndicatorChar (c : Char) : Bool :=
  c == ',' || c == '[' || c == ']' || c == '{' || c == '}'

lemma hasFlowIndicator_eq_any (l : List Char) :
    hasFlowIndicator l = l.any isFlowIndicatorChar := by
  induction l with
  | nil => rfl
  | cons c cs ih =>
    simp only [hasFlowIndicator, List.any_cons, ih, isFlowIndicatorChar, Bool.or_assoc]

/-- A list whose characters all satisfy a predicate `p` that excludes the five
    indicators has no flow indicator. -/
lemma not_hasFlowIndicator_of_all (p : Char → Bool)
    (hp : p ',' = false ∧ p '[' = false ∧ p ']' = false ∧ p '{' = false ∧ p '}' = false)
    {l : List Char} (h : ∀ c ∈ l, p c = true) : hasFlowIndicator l = false := by
  rw [hasFlowIndicator_eq_any, List.any_eq_false]
  intro c hc
  have hpc := h c hc
  cases hcs : isFlowIndicatorChar c with
  | false => exact Bool.false_ne_true
  | true =>
    intro _
    simp only [isFlowIndicatorChar, Bool.or_eq_true, beq_iff_eq] at hcs
    rcases hcs with ((((rfl | rfl) | rfl) | rfl) | rfl) <;> simp_all

/-- The numeric alphabet: everything the Core Schema number lexers accept. -/
def isNumChar (c : Char) : Bool :=
  c.isDigit || decide ('0' ≤ c ∧ c ≤ '9') || decide ('0' ≤ c ∧ c ≤ '7') || c == '_' || c == '-' || c == '+' || c == '.' || c == 'e' || c == 'E' ||
  c == 'x' || c == 'X' || c == 'o' || c == 'O' ||
  decide ('a' ≤ c ∧ c ≤ 'f') || decide ('A' ≤ c ∧ c ≤ 'F')

lemma isNumChar_excludes_indicators :
    isNumChar ',' = false ∧ isNumChar '[' = false ∧ isNumChar ']' = false ∧
    isNumChar '{' = false ∧ isNumChar '}' = false := by decide

lemma isNumChar_of_isDigit {c : Char} (h : c.isDigit = true) : isNumChar c = true := by
  simp [isNumChar, h]

/-- `hasFlowIndicator l = false` once every character is numeric. -/
lemma not_hasFlowIndicator_of_num {l : List Char} (h : ∀ c ∈ l, isNumChar c = true) :
    hasFlowIndicator l = false :=
  not_hasFlowIndicator_of_all isNumChar isNumChar_excludes_indicators h

/-! ## §2 — The lexers only accept numeric characters -/

lemma isNatL_go_num {b : Bool} {l : List Char} (h : isNatL.go b l = true) :
    ∀ c ∈ l, isNumChar c = true := by
  induction l generalizing b with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil)
  | cons d ds ih =>
    intro c hc
    simp only [isNatL.go] at h
    split at h
    · rename_i hd
      split at h
      · rcases List.mem_cons.mp hc with rfl | hc'
        · simp [isNumChar, hd]
        · exact ih h c hc'
      · exact absurd h Bool.false_ne_true
    · split at h
      · rename_i hd
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact isNumChar_of_isDigit hd
        · exact ih h c hc'
      · exact absurd h Bool.false_ne_true

lemma toNatL?_num {l : List Char} {n : Nat} (h : toNatL? l = some n) :
    ∀ c ∈ l, isNumChar c = true := by
  unfold toNatL? at h
  split at h
  · exact isNatL_go_num (by assumption)
  · exact absurd h (by simp)

lemma toIntL?_num {l : List Char} {n : Int} (h : toIntL? l = some n) :
    ∀ c ∈ l, isNumChar c = true := by
  unfold toIntL? at h
  split at h
  · rename_i rest
    intro c hc
    rcases List.mem_cons.mp hc with rfl | hc'
    · decide
    · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      exact toNatL?_num hm c hc'
  · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
    exact toNatL?_num hm

lemma parseHex_go_num {acc : Int} {l : List Char} {n : Int} (h : parseHex.go acc l = some n) :
    ∀ c ∈ l, isNumChar c = true := by
  induction l generalizing acc with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil)
  | cons d ds ih =>
    intro c hc
    simp only [parseHex.go] at h
    rcases List.mem_cons.mp hc with rfl | hc'
    · split at h
      · rename_i hr; simp [isNumChar, hr]
      · split at h
        · rename_i hr; simp [isNumChar, hr]
        · split at h
          · rename_i hr; simp [isNumChar, hr]
          · exact absurd h (by simp)
    · split at h
      · exact ih h c hc'
      · split at h
        · exact ih h c hc'
        · split at h
          · exact ih h c hc'
          · exact absurd h (by simp)

lemma parseOctal_go_num {acc : Int} {l : List Char} {n : Int} (h : parseOctal.go acc l = some n) :
    ∀ c ∈ l, isNumChar c = true := by
  induction l generalizing acc with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil)
  | cons d ds ih =>
    intro c hc
    simp only [parseOctal.go] at h
    split at h
    · rename_i hr
      rcases List.mem_cons.mp hc with rfl | hc'
      · simp [isNumChar, hr]
      · exact ih h c hc'
    · exact absurd h (by simp)

/-- Every character of the input is either the dropped sign or in the remainder. -/
lemma mem_splitSign {l : List Char} {c : Char} (hc : c ∈ l) :
    c = '-' ∨ c = '+' ∨ c ∈ (splitSign l).2 := by
  unfold splitSign
  split
  · rcases List.mem_cons.mp hc with rfl | h
    · exact Or.inl rfl
    · exact Or.inr (Or.inr h)
  · rcases List.mem_cons.mp hc with rfl | h
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr h)
  · exact Or.inr (Or.inr hc)

lemma isIntL_num {l : List Char} {n : Int} (h : isIntL l = some n) :
    ∀ c ∈ l, isNumChar c = true := by
  intro c hc
  rcases mem_splitSign hc with rfl | rfl | hrest
  · decide
  · decide
  · unfold isIntL at h
    rcases hs : splitSign l with ⟨isNeg, rest⟩
    rw [hs] at h hrest
    simp only at h hrest
    split at h
    · rename_i hex _
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hrest with rfl | hrest'
      · decide
      · rcases List.mem_cons.mp hrest' with rfl | hrest''
        · decide
        · exact parseHex_go_num hm c hrest''
    · rename_i hex _
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hrest with rfl | hrest'
      · decide
      · rcases List.mem_cons.mp hrest' with rfl | hrest''
        · decide
        · exact parseHex_go_num hm c hrest''
    · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hrest with rfl | hrest'
      · decide
      · rcases List.mem_cons.mp hrest' with rfl | hrest''
        · decide
        · exact parseOctal_go_num hm c hrest''
    · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      rcases List.mem_cons.mp hrest with rfl | hrest'
      · decide
      · rcases List.mem_cons.mp hrest' with rfl | hrest''
        · decide
        · exact parseOctal_go_num hm c hrest''
    · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      exact toIntL?_num hm c hrest

/-- Every character of the input is the separator or lies in one of the parts. -/
lemma mem_splitOnChar {sep : Char} {l : List Char} {c : Char} (hc : c ∈ l) :
    c = sep ∨ ∃ p ∈ splitOnChar sep l, c ∈ p := by
  induction l with
  | nil => exact absurd hc (List.not_mem_nil)
  | cons d ds ih =>
    simp only [splitOnChar]
    split
    · rename_i hd
      rcases List.mem_cons.mp hc with rfl | hc'
      · exact Or.inl hd
      · rcases ih hc' with h | ⟨p, hp, hcp⟩
        · exact Or.inl h
        · exact Or.inr ⟨p, List.mem_cons_of_mem _ hp, hcp⟩
    · rename_i hd
      split
      · rename_i p ps hsplit
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inr ⟨c :: p, List.mem_cons_self, List.mem_cons_self⟩
        · rcases ih hc' with h | ⟨q, hq, hcq⟩
          · exact Or.inl h
          · rw [hsplit] at hq
            rcases List.mem_cons.mp hq with rfl | hq'
            · exact Or.inr ⟨d :: q, List.mem_cons_self, List.mem_cons_of_mem _ hcq⟩
            · exact Or.inr ⟨q, List.mem_cons_of_mem _ hq', hcq⟩
      · rename_i hsplit
        rcases List.mem_cons.mp hc with rfl | hc'
        · exact Or.inr ⟨[c], List.mem_cons_self, List.mem_cons_self⟩
        · rcases ih hc' with h | ⟨q, hq, -⟩
          · exact Or.inl h
          · rw [hsplit] at hq; exact absurd hq (List.not_mem_nil)

lemma parseMantissaL?_num {l : List Char} {f : Float} (h : parseMantissaL? l = some f) :
    ∀ c ∈ l, isNumChar c = true := by
  intro c hc
  unfold parseMantissaL? at h
  split at h
  · exact absurd h (by simp)
  · split at h
    · rename_i hlit
      simp only [Bool.or_eq_true, beq_iff_eq] at hlit
      rcases hlit with rfl | rfl <;>
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hc <;>
        rcases hc with rfl | rfl | rfl <;> decide
    · split at h
      · rename_i frac
        obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
        rcases List.mem_cons.mp hc with rfl | hc'
        · decide
        · exact toNatL?_num hm c hc'
      · split at h
        · split at h
          · rename_i intPart fracPart hparts
            split at h
            · rename_i i f' hi hf
              rcases mem_splitOnChar (sep := '.') hc with rfl | ⟨p, hp, hcp⟩
              · decide
              · rw [hparts] at hp
                rcases List.mem_cons.mp hp with rfl | hp'
                · exact toIntL?_num hi c hcp
                · rcases List.mem_cons.mp hp' with rfl | hp''
                  · exact toNatL?_num hf c hcp
                  · exact absurd hp'' (List.not_mem_nil)
            · exact absurd h (by simp)
          · exact absurd h (by simp)
        · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
          exact toIntL?_num hm c hc

lemma parseExponentL?_num {l : List Char} {n : Int} (h : parseExponentL? l = some n) :
    ∀ c ∈ l, isNumChar c = true := by
  intro c hc
  unfold parseExponentL? at h
  split at h
  · exact absurd h (by simp)
  · rcases mem_splitSign hc with rfl | rfl | hrest
    · decide
    · decide
    · rcases hs : splitSign l with ⟨isNeg, rest⟩
      rw [hs] at h hrest
      simp only at h hrest
      obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
      exact toNatL?_num hm c hrest

lemma parseFloatL?_num {l : List Char} {f : Float} (h : parseFloatL? l = some f) :
    ∀ c ∈ l, isNumChar c = true := by
  intro c hc
  unfold parseFloatL? at h
  split at h
  · exact absurd h (by simp)
  · rcases mem_splitSign hc with rfl | rfl | hrest
    · decide
    · decide
    · rcases hs : splitSign l with ⟨isNeg, rest⟩
      rw [hs] at h hrest
      simp only at h hrest
      split at h
      · -- scientific notation
        have key : ∀ (sep : Char) (m e : List Char), isNumChar sep = true →
            splitOnChar sep rest = [m, e] →
            (∀ c ∈ m, isNumChar c = true) → (∀ c ∈ e, isNumChar c = true) →
            isNumChar c = true := by
          intro sep m e hsep hparts hm he
          rcases mem_splitOnChar (sep := sep) hrest with rfl | ⟨p, hp, hcp⟩
          · exact hsep
          · rw [hparts] at hp
            rcases List.mem_cons.mp hp with rfl | hp'
            · exact hm c hcp
            · rcases List.mem_cons.mp hp' with rfl | hp''
              · exact he c hcp
              · exact absurd hp'' (List.not_mem_nil)
        split at h
        · rename_i m e hparts
          split at h
          · rename_i mant ex hmant hex
            split at hparts
            · exact key 'e' m e (by decide) hparts (parseMantissaL?_num hmant) (parseExponentL?_num hex)
            · exact key 'E' m e (by decide) hparts (parseMantissaL?_num hmant) (parseExponentL?_num hex)
          · exact absurd h (by simp)
        · exact absurd h (by simp)
      · obtain ⟨m, hm, -⟩ := Option.map_eq_some_iff.mp h
        exact parseMantissaL?_num hm c hrest

/-! ## §3 — The literal recognizers -/

lemma hasFlowIndicator_null_literals :
    hasFlowIndicator "".toList = false ∧ hasFlowIndicator "null".toList = false ∧
    hasFlowIndicator "Null".toList = false ∧ hasFlowIndicator "NULL".toList = false ∧
    hasFlowIndicator "~".toList = false := by native_decide

lemma isNull_eq_false_of_hasFlowIndicator {s : String} (h : hasFlowIndicator s.toList = true) :
    isNull s = false := by
  have lits := hasFlowIndicator_null_literals
  unfold isNull
  simp only [Bool.or_eq_false_iff, beq_eq_false_iff_ne, ne_eq]
  refine ⟨⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩, ?_⟩ <;> intro hs <;> subst hs <;> simp_all

lemma hasFlowIndicator_bool_literals :
    hasFlowIndicator "true".toList = false ∧ hasFlowIndicator "True".toList = false ∧
    hasFlowIndicator "TRUE".toList = false ∧ hasFlowIndicator "false".toList = false ∧
    hasFlowIndicator "False".toList = false ∧ hasFlowIndicator "FALSE".toList = false := by
  native_decide

lemma isBool_eq_none_of_hasFlowIndicator {s : String} (h : hasFlowIndicator s.toList = true) :
    isBool s = none := by
  have lits := hasFlowIndicator_bool_literals
  unfold isBool
  split <;> simp_all

lemma hasFlowIndicator_float_literals :
    hasFlowIndicator ".inf".toList = false ∧ hasFlowIndicator ".Inf".toList = false ∧
    hasFlowIndicator ".INF".toList = false ∧ hasFlowIndicator "+.inf".toList = false ∧
    hasFlowIndicator "+.Inf".toList = false ∧ hasFlowIndicator "+.INF".toList = false ∧
    hasFlowIndicator "-.inf".toList = false ∧ hasFlowIndicator "-.Inf".toList = false ∧
    hasFlowIndicator "-.INF".toList = false ∧ hasFlowIndicator ".nan".toList = false ∧
    hasFlowIndicator ".NaN".toList = false ∧ hasFlowIndicator ".NAN".toList = false := by
  native_decide

lemma isInt_eq_none_of_hasFlowIndicator {s : String} (h : hasFlowIndicator s.toList = true) :
    isInt s = none := by
  unfold isInt
  cases hi : isIntL s.toList with
  | none => rfl
  | some n =>
    have := not_hasFlowIndicator_of_num (isIntL_num hi)
    rw [this] at h
    exact absurd h Bool.false_ne_true

lemma isFloat_eq_none_of_hasFlowIndicator {s : String} (h : hasFlowIndicator s.toList = true) :
    isFloat s = none := by
  have lits := hasFlowIndicator_float_literals
  unfold isFloat
  split
  all_goals first
    | simp_all
    | skip
  unfold parseFloat?
  cases hf : parseFloatL? s.toList with
  | none => rfl
  | some f =>
    have := not_hasFlowIndicator_of_num (parseFloatL?_num hf)
    rw [this] at h
    exact absurd h Bool.false_ne_true

/-! ## §4 — Capstone -/

/-- **A plain scalar containing a flow indicator is a string.**  No Core Schema
    spelling of null, bool, int or float contains `,` `[` `]` `{` or `}`, so
    implicit resolution of such content always falls through to `.str`. -/
lemma resolveImplicit_of_hasFlowIndicator (c : String) (h : hasFlowIndicator c.toList = true) :
    resolveImplicit c = .str c := by
  unfold resolveImplicit
  rw [isNull_eq_false_of_hasFlowIndicator h, isBool_eq_none_of_hasFlowIndicator h,
      isInt_eq_none_of_hasFlowIndicator h, isFloat_eq_none_of_hasFlowIndicator h]
  rfl

end L4YAML.Schema
