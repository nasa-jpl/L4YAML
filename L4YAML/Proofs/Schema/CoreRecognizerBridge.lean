/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import L4YAML.Schema.Schema
public import L4YAML.Spec.CoreSchema

@[expose] public section Blanket

/-! Universal conversion-success bridges for the independent YAML 1.2.2
Core Schema lexical recognizers.  These prove that every allowed number
spelling produces a value; they do not assert correctness of the Float value. -/

namespace L4YAML.Proofs.CoreRecognizerBridge
open L4YAML L4YAML.Schema L4YAML.Spec.CoreSchema

private lemma digit_same (c : Char) : asciiDigit c = c.isDigit := by
  rfl

private lemma nat_go_all (cs : List Char) :
    ∀ b : Bool, cs.all asciiDigit = true →
      isNatL.go b cs = (if cs.isEmpty then b else true) := by
  induction cs with
  | nil => intro b _; rfl
  | cons c cs ih =>
      intro b h
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : cs.all asciiDigit = true := (Bool.and_eq_true _ _).mp h |>.2
      have hneq : c ≠ '_' := by
        intro heq
        subst c
        simp [asciiDigit] at hc
      have htail : isNatL.go true cs = true := by
        simpa using ih true ht
      simp [isNatL.go, hneq, ← digit_same, hc, htail]

private lemma nat_some (cs : List Char) (h : oneOrMore asciiDigit cs = true) :
    (toNatL? cs).isSome = true := by
  have hpair : cs.isEmpty = false ∧ cs.all asciiDigit = true := by
    simpa [oneOrMore, Bool.and_eq_true] using h
  have hnat : isNatL cs = true := by
    change isNatL.go false cs = true
    rw [nat_go_all cs false hpair.2]
    simp [hpair.1]
  simp [toNatL?, hnat]

private lemma hex_go_some (cs : List Char) (h : cs.all asciiHex = true) :
    ∀ acc : Int, (parseHex.go acc cs).isSome = true := by
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
      intro acc
      have hc : asciiHex c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : cs.all asciiHex = true := (Bool.and_eq_true _ _).mp h |>.2
      have hd : (('0' ≤ c ∧ c ≤ '9') ∨ ('a' ≤ c ∧ c ≤ 'f')) ∨
          ('A' ≤ c ∧ c ≤ 'F') := by
        simpa [asciiHex, asciiDigit, Bool.or_eq_true] using hc
      rcases hd with (hd | ha) | hA
      · simp [parseHex.go, hd, ih ht]
      · have hnotd : ¬ ('0' ≤ c ∧ c ≤ '9') := by
          intro hd
          have haNat : 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 102 := ha
          have hdNat : 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 := hd
          omega
        simp [parseHex.go, hnotd, ha, ih ht]
      · have hnotd : ¬ ('0' ≤ c ∧ c ≤ '9') := by
          intro hd
          have hANat : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 70 := hA
          have hdNat : 48 ≤ c.val.toNat ∧ c.val.toNat ≤ 57 := hd
          omega
        have hnota : ¬ ('a' ≤ c ∧ c ≤ 'f') := by
          intro ha
          have hANat : 65 ≤ c.val.toNat ∧ c.val.toNat ≤ 70 := hA
          have haNat : 97 ≤ c.val.toNat ∧ c.val.toNat ≤ 102 := ha
          omega
        simp [parseHex.go, hnotd, hnota, hA, ih ht]

private lemma oct_go_some (cs : List Char) (h : cs.all asciiOctal = true) :
    ∀ acc : Int, (parseOctal.go acc cs).isSome = true := by
  induction cs with
  | nil => intro acc; rfl
  | cons c cs ih =>
      intro acc
      have hc : asciiOctal c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : cs.all asciiOctal = true := (Bool.and_eq_true _ _).mp h |>.2
      have hd : '0' ≤ c ∧ c ≤ '7' := by
        simpa [asciiOctal] using hc
      simp [parseOctal.go, hd, ih ht]

private lemma toInt_some_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (toIntL? cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore] at h
  | cons c cs =>
      have hc : asciiDigit c = true := by
        have hsplit : (c :: cs).isEmpty = false ∧
            (c :: cs).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        have hpair := hsplit.2
        exact (Bool.and_eq_true _ _).mp hpair |>.1
      have hminus : c ≠ '-' := by
        intro heq
        subst c
        simp [asciiDigit] at hc
      have hn := nat_some (c :: cs) h
      simpa [toIntL?, hminus] using hn

private lemma digit_not (c forbidden : Char) (h : asciiDigit c = true)
    (hf : asciiDigit forbidden = false) : c ≠ forbidden := by
  intro heq
  subst c
  simp [hf] at h

private lemma int_some_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore] at h
  | cons c rest =>
      have hn := toInt_some_digits (c :: rest) h
      have hc : asciiDigit c = true := by
        have ha : (c :: rest).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        exact (Bool.and_eq_true _ _).mp ha |>.1
      have hcminus : c ≠ '-' := digit_not c '-' hc (by decide)
      have hcplus : c ≠ '+' := digit_not c '+' hc (by decide)
      cases rest with
      | nil => simpa [isIntL, splitSign, hcminus, hcplus] using hn
      | cons d ds =>
          have hd : asciiDigit d = true := by
            have ha : (c :: d :: ds).all asciiDigit = true := by
              simpa [oneOrMore, Bool.and_eq_true] using h
            have ht := (Bool.and_eq_true _ _).mp ha |>.2
            exact (Bool.and_eq_true _ _).mp ht |>.1
          have hdx : d ≠ 'x' := digit_not d 'x' hd (by decide)
          have hdX : d ≠ 'X' := digit_not d 'X' hd (by decide)
          have hdo : d ≠ 'o' := digit_not d 'o' hd (by decide)
          have hdO : d ≠ 'O' := digit_not d 'O' hd (by decide)
          by_cases hc0 : c = '0'
          · subst c
            simpa [isIntL, splitSign, hdx, hdX, hdo, hdO] using hn
          · simpa [isIntL, splitSign, hc0, hcminus, hcplus] using hn

private lemma splitSign_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    splitSign cs = (false, cs) := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      have hc : asciiDigit c = true := by
        have ha : (c :: rest).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        exact (Bool.and_eq_true _ _).mp ha |>.1
      have hm : c ≠ '-' := digit_not c '-' hc (by decide)
      have hp : c ≠ '+' := digit_not c '+' hc (by decide)
      simp [splitSign, hm, hp]

private lemma int_some_signed_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (isIntL ('+' :: cs)).isSome = true ∧
    (isIntL ('-' :: cs)).isSome = true := by
  have hs := splitSign_digits cs h
  have hi := int_some_digits cs h
  have hi' := hi
  simp only [isIntL, hs] at hi'
  constructor
  · simpa only [isIntL, splitSign] using hi'
  · simp only [isIntL, splitSign]
    split at hi' <;> simp_all [Option.isSome_map]

private lemma int_some_decimal (cs : List Char)
    (h : oneOrMore asciiDigit (withoutSign cs) = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp [withoutSign, oneOrMore] at h
  | cons c rest =>
      by_cases hp : c = '+'
      · subst c
        have hr : oneOrMore asciiDigit rest = true := by
          simpa [withoutSign] using h
        exact (int_some_signed_digits rest hr).1
      · by_cases hm : c = '-'
        · subst c
          have hr : oneOrMore asciiDigit rest = true := by
            simpa [withoutSign] using h
          exact (int_some_signed_digits rest hr).2
        · have hr : oneOrMore asciiDigit (c :: rest) = true := by
            simpa [withoutSign, hp, hm] using h
          exact int_some_digits (c :: rest) hr

private lemma int_some_hex (rest : List Char)
    (h : oneOrMore asciiHex rest = true) :
    (isIntL ('0' :: 'x' :: rest)).isSome = true := by
  have ha : rest.all asciiHex = true := by
    have hp : rest.isEmpty = false ∧ rest.all asciiHex = true := by
      simpa [oneOrMore, Bool.and_eq_true] using h
    exact hp.2
  have hr := hex_go_some rest ha 0
  simpa [isIntL, splitSign, Option.isSome_map] using hr

private lemma int_some_octal (rest : List Char)
    (h : oneOrMore asciiOctal rest = true) :
    (isIntL ('0' :: 'o' :: rest)).isSome = true := by
  have ha : rest.all asciiOctal = true := by
    have hp : rest.isEmpty = false ∧ rest.all asciiOctal = true := by
      simpa [oneOrMore, Bool.and_eq_true] using h
    exact hp.2
  have hr := oct_go_some rest ha 0
  simpa [isIntL, splitSign, Option.isSome_map] using hr

private lemma int_some_octal_match (cs : List Char)
    (h : (match cs with
      | '0' :: 'o' :: rest => oneOrMore asciiOctal rest
      | _ => false) = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp at h
  | cons c tail =>
      by_cases hc : c = '0'
      · subst c
        cases tail with
        | nil => simp at h
        | cons d rest =>
            by_cases hd : d = 'o'
            · subst d
              exact int_some_octal rest (by simpa using h)
            · simp [hd] at h
      · simp [hc] at h

private lemma int_some_hex_match (cs : List Char)
    (h : (match cs with
      | '0' :: 'x' :: rest => oneOrMore asciiHex rest
      | _ => false) = true) :
    (isIntL cs).isSome = true := by
  cases cs with
  | nil => simp at h
  | cons c tail =>
      by_cases hc : c = '0'
      · subst c
        cases tail with
        | nil => simp at h
        | cons d rest =>
            by_cases hd : d = 'x'
            · subst d
              exact int_some_hex rest (by simpa using h)
            · simp [hd] at h
      · simp [hc] at h

lemma int_some_of_integerSpelling (s : String)
    (h : integerSpelling s = true) :
    (isInt s).isSome = true := by
  have hor :
      ((oneOrMore asciiDigit (withoutSign s.toList) ||
        (match s.toList with
          | '0' :: 'o' :: rest => oneOrMore asciiOctal rest
          | _ => false)) ||
        (match s.toList with
          | '0' :: 'x' :: rest => oneOrMore asciiHex rest
          | _ => false)) = true := by
    exact h
  have hs : (isIntL s.toList).isSome = true := by
    rcases (Bool.or_eq_true _ _).mp hor with (hor' | hx)
    · rcases (Bool.or_eq_true _ _).mp hor' with (hd | ho)
      · exact int_some_decimal s.toList hd
      · exact int_some_octal_match s.toList ho
    · exact int_some_hex_match s.toList hx
  simpa [isInt, h] using hs



private lemma exponent_some_of_digits (cs : List Char)
    (h : oneOrMore asciiDigit (withoutSign cs) = true) :
    (parseExponentL? cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore, withoutSign] at h
  | cons c rest =>
      by_cases hplus : c = '+'
      · subst c
        have hr : oneOrMore asciiDigit rest = true := by
          simpa [withoutSign] using h
        have hn := nat_some rest hr
        simpa [parseExponentL?, splitSign] using hn
      · by_cases hminus : c = '-'
        · subst c
          have hr : oneOrMore asciiDigit rest = true := by
            simpa [withoutSign] using h
          have hn := nat_some rest hr
          simpa [parseExponentL?, splitSign] using hn
        · have hr : oneOrMore asciiDigit (c :: rest) = true := by
            simpa [withoutSign, hplus, hminus] using h
          have hn := nat_some (c :: rest) hr
          have hs := splitSign_digits (c :: rest) hr
          simpa [parseExponentL?, hs] using hn

private lemma digits_no_dot (cs : List Char)
    (h : cs.all asciiDigit = true) : '.' ∉ cs := by
  induction cs with
  | nil => simp
  | cons c tail ih =>
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp h |>.1
      have ht : tail.all asciiDigit = true := (Bool.and_eq_true _ _).mp h |>.2
      have hnd : c ≠ '.' := digit_not c '.' hc (by decide)
      have hdc : '.' ≠ c := Ne.symm hnd
      simp [hdc, ih ht]

private lemma mantissa_some_digits (cs : List Char)
    (h : oneOrMore asciiDigit cs = true) :
    (parseMantissaL? cs).isSome = true := by
  cases cs with
  | nil => simp [oneOrMore] at h
  | cons c rest =>
      have ha : (c :: rest).all asciiDigit = true := by
        have hp : (c :: rest).isEmpty = false ∧
            (c :: rest).all asciiDigit = true := by
          simpa [oneOrMore, Bool.and_eq_true] using h
        exact hp.2
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp ha |>.1
      have hnd : c ≠ '.' := digit_not c '.' hc (by decide)
      have hno := digits_no_dot (c :: rest) ha
      have hnrec : '.' ∉ rest := by
        intro hm
        exact hno (List.mem_cons_of_mem c hm)
      have hneqc : '.' ≠ c := Ne.symm hnd
      have hs1 : (c :: rest) ≠ ['0', '.'] := by
        intro heq
        simp [heq] at hno
      have hs2 : (c :: rest) ≠ ['0', '.', '0'] := by
        intro heq
        simp [heq] at hno
      have hsp1 : ¬(c = '0' ∧ rest = ['.']) := by
        intro hp
        exact hs1 (by simp [hp.1, hp.2])
      have hsp2 : ¬(c = '0' ∧ rest = ['.', '0']) := by
        intro hp
        exact hs2 (by simp [hp.1, hp.2])
      have hn := toInt_some_digits (c :: rest) h
      simpa [parseMantissaL?, hnd, hneqc, hnrec, hsp1, hsp2] using hn

private lemma mantissa_some_leading_dot (frac : List Char)
    (h : oneOrMore asciiDigit frac = true) :
    (parseMantissaL? ('.' :: frac)).isSome = true := by
  have hn := nat_some frac h
  simpa [parseMantissaL?] using hn

private lemma splitOnChar_no_dot (cs : List Char) (h : '.' ∉ cs) :
    splitOnChar '.' cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons c tail ih =>
      have hc : c ≠ '.' := by
        intro hc
        exact h (by simp [hc])
      have ht : '.' ∉ tail := by
        intro hm
        exact h (List.mem_cons_of_mem c hm)
      simp [splitOnChar, hc, ih ht]

private lemma splitOnChar_one_dot (whole frac : List Char)
    (hw : '.' ∉ whole) (hf : '.' ∉ frac) :
    splitOnChar '.' (whole ++ '.' :: frac) = [whole, frac] := by
  induction whole with
  | nil =>
      simp [splitOnChar, splitOnChar_no_dot frac hf]
  | cons c tail ih =>
      have hc : c ≠ '.' := by
        intro hc
        exact hw (by simp [hc])
      have ht : '.' ∉ tail := by
        intro hm
        exact hw (List.mem_cons_of_mem c hm)
      simp [splitOnChar, hc, ih ht]

private lemma mantissa_some_whole_dot (whole frac : List Char)
    (hw : oneOrMore asciiDigit whole = true)
    (hf : frac.all asciiDigit = true) :
    (parseMantissaL? (whole ++ '.' :: frac)).isSome = true := by
  have hwAll : whole.all asciiDigit = true := by
    have hp : whole.isEmpty = false ∧ whole.all asciiDigit = true := by
      simpa [oneOrMore, Bool.and_eq_true] using hw
    exact hp.2
  have hnWhole := digits_no_dot whole hwAll
  have hnFrac := digits_no_dot frac hf
  have hs := splitOnChar_one_dot whole frac hnWhole hnFrac
  have hi := toInt_some_digits whole hw
  have hfracOpt : (if frac.isEmpty then some 0 else toNatL? frac).isSome = true := by
    by_cases he : frac.isEmpty
    · simp [he]
    · have hm : oneOrMore asciiDigit frac = true := by
        simp [oneOrMore, he, hf]
      simpa [he] using nat_some frac hm
  cases whole with
  | nil => simp [oneOrMore] at hw
  | cons c rest =>
      have hc : asciiDigit c = true :=
        (Bool.and_eq_true _ _).mp hwAll |>.1
      have hcdot : c ≠ '.' := digit_not c '.' hc (by decide)
      have hcontains : (c :: rest ++ '.' :: frac).contains '.' = true := by
        simp
      by_cases hsp1 : (c :: rest ++ '.' :: frac) = ['0', '.']
      · simp [parseMantissaL?, hsp1]
      · by_cases hsp2 : (c :: rest ++ '.' :: frac) = ['0', '.', '0']
        · simp [parseMantissaL?, hsp2]
        · have hs' : splitOnChar '.' (c :: rest ++ '.' :: frac) = [c :: rest, frac] := hs
          have hs'' : splitOnChar '.' (c :: (rest ++ '.' :: frac)) = [c :: rest, frac] := by
            simpa using hs'
          have hsp1' : ¬(c = '0' ∧ rest ++ '.' :: frac = ['.']) := by
            intro hp
            exact hsp1 (by simp [hp.1, hp.2])
          have hsp2' : ¬(c = '0' ∧ rest ++ '.' :: frac = ['.', '0']) := by
            intro hp
            exact hsp2 (by simp [hp.1, hp.2])
          have hfracOpt' : (if frac = [] then some 0 else toNatL? frac).isSome = true := by
            simpa using hfracOpt
          cases hi' : toIntL? (c :: rest) with
          | none => simp [hi'] at hi
          | some i =>
              cases hf' : (if frac = [] then some 0 else toNatL? frac) with
              | none => simp [hf'] at hfracOpt'
              | some f =>
                  simp only [parseMantissaL?]
                  simp [hcdot]
                  simp only [hsp1', hsp2']
                  rw [hs'']
                  simp [hi', hf']

private lemma span_loop_digits (cs acc : List Char) :
    List.span.loop asciiDigit cs acc =
      (acc.reverse ++ cs.takeWhile asciiDigit, cs.dropWhile asciiDigit) := by
  induction cs generalizing acc with
  | nil => simp [List.span.loop, List.takeWhile, List.dropWhile]
  | cons c cs ih =>
      by_cases hc : asciiDigit c = true
      · simp [List.span.loop, hc, List.takeWhile, List.dropWhile, ih,
          List.reverse_cons, List.append_assoc]
      · simp [List.span.loop, hc, List.takeWhile, List.dropWhile]

private lemma span_digits_eq (cs : List Char) :
    cs.span asciiDigit = (cs.takeWhile asciiDigit, cs.dropWhile asciiDigit) := by
  simpa [List.span] using span_loop_digits cs []

private lemma mantissa_some_of_spelling (cs : List Char)
    (h : mantissaSpelling cs = true) :
    (parseMantissaL? cs).isSome = true := by
  cases cs with
  | nil => simp [mantissaSpelling, List.span, List.span.loop, oneOrMore] at h
  | cons c rest =>
      by_cases hc : c = '.'
      · subst c
        exact mantissa_some_leading_dot rest (by simpa [mantissaSpelling] using h)
      · let whole := (c :: rest).takeWhile asciiDigit
        let tail := (c :: rest).dropWhile asciiDigit
        have hjoin : whole ++ tail = c :: rest := by
          exact List.takeWhile_append_dropWhile
        cases ht : tail with
        | nil =>
            have hw : oneOrMore asciiDigit whole = true := by
              unfold mantissaSpelling at h
              split at h
              · simp_all
              · rw [span_digits_eq] at h
                simpa [tail, ht, whole] using h
            have hm := mantissa_some_digits whole hw
            simpa [← hjoin, ht] using hm
        | cons d frac =>
            by_cases hd : d = '.'
            · subst d
              have hp : oneOrMore asciiDigit whole = true ∧
                  frac.all asciiDigit = true := by
                unfold mantissaSpelling at h
                split at h
                · simp_all
                · rw [span_digits_eq] at h
                  simpa [tail, ht, whole, Bool.and_eq_true] using h
              have hm := mantissa_some_whole_dot whole frac hp.1 hp.2
              simpa [← hjoin, ht] using hm
            · unfold mantissaSpelling at h
              split at h
              · simp_all
              · rw [span_digits_eq] at h
                simp [tail, ht, hd] at h

private lemma splitExponent_shape (cs : List Char) :
    let (m, exponent) := splitExponent cs
    ('e' ∉ m ∧ 'E' ∉ m) ∧
      match exponent with
      | none => cs = m
      | some tail => cs = m ++ 'e' :: tail ∨ cs = m ++ 'E' :: tail := by
  induction cs with
  | nil => simp [splitExponent]
  | cons c rest ih =>
      by_cases he : c = 'e'
      · subst c
        simp [splitExponent]
      · by_cases hE : c = 'E'
        · subst c
          simp [splitExponent]
        · cases hs : splitExponent rest with
          | mk m exp =>
              have hi := ih
              simp only [hs] at hi
              have hne : 'e' ≠ c := Ne.symm he
              have hnE : 'E' ≠ c := Ne.symm hE
              have hf : splitExponent (c :: rest) = (c :: m, exp) := by
                simp [splitExponent, hs]
              cases exp with
              | none =>
                  simp only [hf]
                  simp [hne, hnE, hi.1.1, hi.1.2, hi.2]
              | some t =>
                  simp only [hf]
                  simp [hne, hnE, hi.1.1, hi.1.2, hi.2,
                    List.cons_append]

private lemma digits_no_char (cs : List Char) (h : cs.all asciiDigit = true)
    (sep : Char) (hn : asciiDigit sep = false) : sep ∉ cs := by
  induction cs with
  | nil => simp
  | cons c rest ih =>
      have hc : asciiDigit c = true := (Bool.and_eq_true _ _).mp h |>.1
      have hr : rest.all asciiDigit = true := (Bool.and_eq_true _ _).mp h |>.2
      have hne : sep ≠ c := by
        intro heq
        subst c
        simp [hn] at hc
      simp [hne, ih hr]

private lemma splitOnChar_no_sep (sep : Char) (cs : List Char)
    (h : sep ∉ cs) : splitOnChar sep cs = [cs] := by
  induction cs with
  | nil => rfl
  | cons c tail ih =>
      have hc : c ≠ sep := by
        intro heq
        exact h (by simp [heq])
      have ht : sep ∉ tail := by
        intro hm
        exact h (List.mem_cons_of_mem c hm)
      simp [splitOnChar, hc, ih ht]

private lemma splitOnChar_one_sep (sep : Char) (whole rest : List Char)
    (hw : sep ∉ whole) (hr : sep ∉ rest) :
    splitOnChar sep (whole ++ sep :: rest) = [whole, rest] := by
  induction whole with
  | nil => simp [splitOnChar, splitOnChar_no_sep sep rest hr]
  | cons c tail ih =>
      have hc : c ≠ sep := by
        intro heq
        exact hw (by simp [heq])
      have ht : sep ∉ tail := by
        intro hm
        exact hw (List.mem_cons_of_mem c hm)
      simp [splitOnChar, hc, ih ht]

private lemma signed_digits_no_char (cs : List Char)
    (h : oneOrMore asciiDigit (withoutSign cs) = true)
    (sep : Char) (hn : asciiDigit sep = false)
    (hplus : sep ≠ '+') (hminus : sep ≠ '-') : sep ∉ cs := by
  cases cs with
  | nil => simp [withoutSign, oneOrMore] at h
  | cons c rest =>
      by_cases hp : c = '+'
      · subst c
        have hr : rest.all asciiDigit = true := by
          have h' : oneOrMore asciiDigit rest = true := by
            simpa [withoutSign] using h
          have hp : (!rest.isEmpty && rest.all asciiDigit) = true := h'
          exact ((Bool.and_eq_true _ _).mp hp).2
        simp [hplus, digits_no_char rest hr sep hn]
      · by_cases hm : c = '-'
        · subst c
          have hr : rest.all asciiDigit = true := by
            have h' : oneOrMore asciiDigit rest = true := by
              simpa [withoutSign] using h
            have hp : (!rest.isEmpty && rest.all asciiDigit) = true := h'
            exact ((Bool.and_eq_true _ _).mp hp).2
          simp [hminus, digits_no_char rest hr sep hn]
        · have hr : (c :: rest).all asciiDigit = true := by
            have h' : oneOrMore asciiDigit (c :: rest) = true := by
              simpa [withoutSign, hp, hm] using h
            have hp : (!(c :: rest).isEmpty && (c :: rest).all asciiDigit) = true := h'
            exact ((Bool.and_eq_true _ _).mp hp).2
          exact digits_no_char (c :: rest) hr sep hn

private def parseFloatRemainder? (isNeg : Bool) (rest : List Char) : Option Float :=
  if rest.contains 'e' || rest.contains 'E' then
    let parts := if rest.contains 'e' then splitOnChar 'e' rest else splitOnChar 'E' rest
    match parts with
    | [mantissaStr, expStr] =>
      match parseMantissaL? mantissaStr, parseExponentL? expStr with
      | some mantissa, some exp =>
        let signedMantissa := if isNeg then -mantissa else mantissa
        some (signedMantissa * (Float.pow 10.0 (Float.ofInt exp)))
      | _, _ => none
    | _ => none
  else
    (parseMantissaL? rest).map fun value => if isNeg then -value else value

private lemma parseFloat_of_splitSign (l rest : List Char) (neg : Bool)
    (hne : l.isEmpty = false) (hs : splitSign l = (neg, rest)) :
    parseFloatL? l = parseFloatRemainder? neg rest := by
  simp [parseFloatL?, hne, hs, parseFloatRemainder?] <;> rfl

private lemma parseFloatRemainder_some (cs mantissa : List Char)
    (exponent : Option (List Char)) (neg : Bool)
    (hm : mantissaSpelling mantissa = true)
    (he : (match exponent with
        | none => true
        | some rest => oneOrMore asciiDigit (withoutSign rest)) = true)
    (hs : splitExponent cs = (mantissa, exponent)) :
    (parseFloatRemainder? neg cs).isSome = true := by
  have hshape := splitExponent_shape cs
  simp only [hs] at hshape
  obtain ⟨⟨hme, hmE⟩, hform⟩ := hshape
  have hmant := mantissa_some_of_spelling mantissa hm
  cases exponent with
  | none =>
      have hid : cs = mantissa := hform
      subst cs
      have hce : mantissa.contains 'e' = false := by
        simp [List.contains_eq_mem, hme]
      have hcE : mantissa.contains 'E' = false := by
        simp [List.contains_eq_mem, hmE]
      unfold parseFloatRemainder?
      simp only [hce, hcE, Bool.false_or, Bool.false_eq_true, ↓reduceIte]
      cases hp : parseMantissaL? mantissa with
      | none => simp [hp] at hmant
      | some v => simp
  | some tail =>
      have hex := exponent_some_of_digits tail he
      have hte : 'e' ∉ tail := signed_digits_no_char tail he 'e' (by decide)
        (by decide) (by decide)
      have htE : 'E' ∉ tail := signed_digits_no_char tail he 'E' (by decide)
        (by decide) (by decide)
      rcases hform with hform | hform
      · subst cs
        have hce : (mantissa ++ 'e' :: tail).contains 'e' = true := by
          simp [List.contains_eq_mem]
        have hsplit := splitOnChar_one_sep 'e' mantissa tail hme hte
        unfold parseFloatRemainder?
        simp only [hce, Bool.true_or, ↓reduceIte, hsplit]
        cases hp : parseMantissaL? mantissa with
        | none => simp [hp] at hmant
        | some v =>
            cases hx : parseExponentL? tail with
            | none => simp [hx] at hex
            | some x => simp
      · subst cs
        have hce : (mantissa ++ 'E' :: tail).contains 'e' = false := by
          simp [List.contains_eq_mem, hme, hte]
        have hcE : (mantissa ++ 'E' :: tail).contains 'E' = true := by
          simp [List.contains_eq_mem]
        have hsplit := splitOnChar_one_sep 'E' mantissa tail hmE htE
        unfold parseFloatRemainder?
        simp only [hce, hcE, Bool.false_or, ↓reduceIte, hsplit]
        cases hp : parseMantissaL? mantissa with
        | none => simp [hp] at hmant
        | some v =>
            cases hx : parseExponentL? tail with
            | none => simp [hx] at hex
            | some x => simp [hp, hx]

private lemma splitSign_withoutSign (cs : List Char) :
    (splitSign cs).2 = withoutSign cs := by
  cases cs with
  | nil => rfl
  | cons c rest =>
      by_cases hp : c = '+'
      · subst c; rfl
      · by_cases hm : c = '-'
        · subst c; rfl
        · simp [splitSign, withoutSign, hp, hm]

private lemma numberSpelling_nonempty (cs : List Char)
    (h : (let (m, exponent) := splitExponent (withoutSign cs)
      mantissaSpelling m &&
        match exponent with
        | none => true
        | some rest => oneOrMore asciiDigit (withoutSign rest)) = true) :
    cs.isEmpty = false := by
  cases cs with
  | nil => simp [splitExponent, withoutSign, mantissaSpelling,
      List.span, List.span.loop, oneOrMore] at h
  | cons c rest => rfl

private lemma parseFloat_some_of_numberSpelling (s : String)
    (h : numberSpelling s = true) :
    (parseFloat? s).isSome = true := by
  have hbody : (let (m, exponent) := splitExponent (withoutSign s.toList)
      mantissaSpelling m &&
        match exponent with
        | none => true
        | some rest => oneOrMore asciiDigit (withoutSign rest)) = true := h
  have hne := numberSpelling_nonempty s.toList hbody
  let p := splitExponent (withoutSign s.toList)
  have hp : (mantissaSpelling p.1 &&
      match p.2 with
      | none => true
      | some rest => oneOrMore asciiDigit (withoutSign rest)) = true := by
    simpa [p] using hbody
  have hpair := (Bool.and_eq_true _ _).mp hp
  have hs : splitExponent (withoutSign s.toList) = (p.1, p.2) := by
    simp [p]
  cases hsign : splitSign s.toList with
  | mk neg rest =>
      have hr : rest = withoutSign s.toList := by
        have hf := splitSign_withoutSign s.toList
        simpa [hsign] using hf
      subst rest
      rw [parseFloat?, parseFloat_of_splitSign s.toList
        (withoutSign s.toList) neg hne hsign]
      exact parseFloatRemainder_some (withoutSign s.toList) p.1 p.2 neg
        hpair.1 hpair.2 hs

private lemma withoutSign_cases (cs : List Char) :
    cs = withoutSign cs ∨
    cs = '+' :: withoutSign cs ∨
    cs = '-' :: withoutSign cs := by
  cases cs with
  | nil => left; rfl
  | cons c rest =>
      by_cases hp : c = '+'
      · subst c; simp [withoutSign]
      · by_cases hm : c = '-'
        · subst c; simp [withoutSign]
        · left; simp [withoutSign, hp, hm]

private lemma string_of_withoutSign_cases (s suffix : String)
    (h : String.ofList (withoutSign s.toList) = suffix) :
    s = suffix ∨ s = "+" ++ suffix ∨ s = "-" ++ suffix := by
  have hs : String.ofList s.toList = s := by simp
  rcases withoutSign_cases s.toList with hc | hc | hc
  · left
    rw [←hs, hc]
    exact h
  · right; left
    rw [←hs, hc]
    simpa using congrArg (fun x : String => "+" ++ x) h
  · right; right
    rw [←hs, hc]
    simpa using congrArg (fun x : String => "-" ++ x) h

private lemma inf_some (s : String)
    (h : infinitySpelling s = true) : (isFloat s).isSome = true := by
  have hsp : String.ofList (withoutSign s.toList) = ".inf" ∨
      String.ofList (withoutSign s.toList) = ".Inf" ∨
      String.ofList (withoutSign s.toList) = ".INF" := by
    simp only [infinitySpelling, Bool.or_eq_true, beq_iff_eq] at h
    rcases h with hab | hc
    · rcases hab with ha | hb
      · exact Or.inl ha
      · exact Or.inr (Or.inl hb)
    · exact Or.inr (Or.inr hc)
  rcases hsp with hh | hh | hh
  · rcases string_of_withoutSign_cases s ".inf" hh with hh | hh | hh
    all_goals subst s <;> decide
  · rcases string_of_withoutSign_cases s ".Inf" hh with hh | hh | hh
    all_goals subst s <;> decide
  · rcases string_of_withoutSign_cases s ".INF" hh with hh | hh | hh
    all_goals subst s <;> decide

private lemma nan_some (s : String)
    (h : nanSpelling s = true) : (isFloat s).isSome = true := by
  simp only [nanSpelling, Bool.or_eq_true, beq_iff_eq] at h
  rcases h with hab | hc
  · rcases hab with ha | hb
    · subst s; decide
    · subst s; decide
  · subst s; decide

lemma float_some_of_floatSpelling (s : String)
    (h : floatSpelling s = true) : (isFloat s).isSome = true := by
  have hparts : numberSpelling s = true ∨ infinitySpelling s = true ∨
      nanSpelling s = true := by
    have hor : (numberSpelling s = true ∨ infinitySpelling s = true) ∨
        nanSpelling s = true := by
      simpa [floatSpelling, Bool.or_eq_true] using h
    rcases hor with (hn | hi) | hnan
    · exact Or.inl hn
    · exact Or.inr (Or.inl hi)
    · exact Or.inr (Or.inr hnan)
  rcases hparts with hn | hi | hna
  · have hp := parseFloat_some_of_numberSpelling s hn
    simp only [isFloat, h, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    split <;> simp [Option.isSome_map, hp]
  · exact inf_some s hi
  · exact nan_some s hna

end L4YAML.Proofs.CoreRecognizerBridge
end Blanket
