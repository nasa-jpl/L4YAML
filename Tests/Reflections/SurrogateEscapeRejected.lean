module

public import L4YAML.Output.Events

public meta import L4YAML.Output.Events
public import L4YAML.Output.EventsIx
public meta import L4YAML.Output.EventsIx
public import L4YAML.Proofs.Foundation.CharClass

@[expose] public section Blanket

/-!
# Reflection — a total coercion with a silent default turns a weak guard into silent corruption

**The principle.** A guard that is *weaker* than the precondition of the function it guards does
not fail loudly on the difference — it fails however that function's total fallback fails.  When
the fallback is a **substitution** rather than an error, the difference between the two conditions
becomes a set of inputs that are accepted and silently wrong.  The fix is not to widen the guard
by inspection; it is to make the guard *be* the precondition, so the fallback is unreachable.

**The instance.** `Char.ofNat : Nat → Char` is total:

    Char.ofNat n = dite n.isValidChar (Char.ofNatAux n) (fun _ => '\0')

`parseHexEscape` / `parseHexEscapeIx` guarded on `val < 0x110000`.  That is strictly weaker than
`Nat.isValidChar`, which additionally excludes the surrogates U+D800–U+DFFF (a lone surrogate is
not a Unicode scalar value and has no UTF-8 encoding).  The two conditions disagree on exactly
2048 code points, and on every one of them the scanner took its **success** branch and
`Char.ofNat` returned `'\0'`.  So `a: "\ud800"` parsed to a scalar containing NUL, on input the
scanner *accepted*, with no diagnostic — and re-emitted as `a: "\0"`, which is well-formed YAML
asserting a NUL the author never wrote.

Both guards are now `Nat.isValidChar` itself, so the substituting branch is unreachable from the
scanners.  YAML 1.2.2 `[60]`/`[61]` constrain the decoded value not at all — that gap is the
spec's — but §5.1 admits only Unicode characters, which settles it for a conforming processor.

**Why this is a proof-engineering reflection and not just a bug fix.** The corpus already carried
a lemma *about* this code, `EscapeResolution.char_isValidChar`: "every `Char` is a valid Unicode
code point".  True, and useless here — it quantifies over the **codomain**, so `'\0'` satisfies it.
The module docstring then cited it as if it established faithful decoding.  A lemma about where a
function's results *live* is not a lemma about *which* result you got; a total coercion with a
silent default is exactly where that distinction stops being pedantic.  The companion that does
the work is `CharClass.toNat_ofNat_of_isValidChar`, exercised below.

Rule 5 (positive) / boundary pins follow.  Everything runs through `partial def` pipelines, so the
checks are `native_decide`.
-/

namespace SurrogateEscapeRejected

open L4YAML.Events
open L4YAML.Proofs.CharClass

/-- The event stream `streamToEvents` emits for `input`, or a fixed marker on rejection. -/
def run (input : String) : String :=
  match streamToEvents input with | .ok s => s | .error _ => "«rejected»"

/-! ## §1 The lemma the old docstring was missing

`char_isValidChar` says the decoded character is *a* valid `Char`. This says it is the
*requested* one, and it needs the `isValidChar` hypothesis the other lemma does not have. -/

/-- U+0041 decodes to U+0041 — the property that held all along for non-surrogates. -/
example : (Char.ofNat 0x41).toNat = 0x41 :=
  toNat_ofNat_of_isValidChar (by decide)

/-- U+10FFFF, the last scalar value, decodes faithfully. -/
example : (Char.ofNat 0x10FFFF).toNat = 0x10FFFF :=
  toNat_ofNat_of_isValidChar (by decide)

/-- The counterexample the guard now excludes: `Char.ofNat` on a surrogate is NOT faithful.
    U+D800 is `< 0x110000`, so the old guard admitted it — and this is what it decoded to. -/
example : (Char.ofNat 0xD800).toNat = 0 := by native_decide

/-- …and the whole surrogate block collapses to the same character, so the old behaviour
    identified 2048 distinct escapes with each other and with `\0`. -/
example : Char.ofNat 0xD800 = Char.ofNat 0xDFFF := by native_decide

/-- `Nat.isValidChar` is what separates the two: it refutes the surrogate. -/
example : ¬ (0xD800 : Nat).isValidChar := by decide

/-! ## §2 Rejection pins — the four shapes that used to yield NUL

Each of these was accepted before 2026-08-11 and produced a scalar containing U+0000. -/

/-- `\uD800` — first surrogate, 4-digit form. -/
theorem reject_u_d800 : run "a: \"\\ud800\"\n" = "«rejected»" := by native_decide

/-- `\uDFFF` — last surrogate. -/
theorem reject_u_dfff : run "a: \"\\udfff\"\n" = "«rejected»" := by native_decide

/-- `\uDBFF` — a high surrogate mid-block. -/
theorem reject_u_dbff : run "a: \"\\udbff\"\n" = "«rejected»" := by native_decide

/-- `\U0000D800` — the same code point in the 8-digit form, which dispatches through the
    same guard. -/
theorem reject_U_0000d800 : run "a: \"\\U0000d800\"\n" = "«rejected»" := by native_decide

/-- A UTF-16 surrogate *pair* is still two lone surrogates to a UTF-8 processor: YAML has no
    pairing rule, so `\uD83D\uDE00` is rejected rather than composed to U+1F600. (It used to
    decode to two NULs.) -/
theorem reject_surrogate_pair : run "a: \"\\uD83D\\uDE00\"\n" = "«rejected»" := by native_decide

/-! ## §3 Boundary pins — the fix must not over-reject

The guard is a *hole* in the code-point line, not a ceiling: the characters either side of the
surrogate block, and the top of the range, still decode. -/

/-- U+D7FF — one below the block. -/
theorem accept_u_d7ff :
    run "a: \"\\ud7ff\"\n" = "+STR\n+DOC\n+MAP\n=VAL :a\n=VAL \"\ud7ff\n-MAP\n-DOC\n-STR\n" := by
  native_decide

/-- U+E000 — one above the block. -/
theorem accept_u_e000 :
    run "a: \"\\ue000\"\n" = "+STR\n+DOC\n+MAP\n=VAL :a\n=VAL \"\ue000\n-MAP\n-DOC\n-STR\n" := by
  native_decide

/-- `\x41` — the 2-digit form cannot reach a surrogate at all, so it is untouched. -/
theorem accept_x41 :
    run "a: \"\\x41\"\n" = "+STR\n+DOC\n+MAP\n=VAL :a\n=VAL \"A\n-MAP\n-DOC\n-STR\n" := by
  native_decide

/-- `\U0010FFFF` — the last scalar value still decodes; the `≥ 0x110000` half of the guard is
    unchanged. -/
theorem accept_U_0010ffff :
    run "a: \"\\U0010FFFF\"\n"
      = "+STR\n+DOC\n+MAP\n=VAL :a\n=VAL \"" ++ String.singleton (Char.ofNat 0x10FFFF)
        ++ "\n-MAP\n-DOC\n-STR\n" := by
  native_decide

/-- `\U00110000` — just past the end, still rejected (it always was). -/
theorem reject_U_00110000 : run "a: \"\\U00110000\"\n" = "«rejected»" := by native_decide

/-! ## §4 The indexed twin agrees on every verdict

`parseHexEscapeIx` carries the identical guard. Its `none` reaches the caller as
`unterminatedDoubleQuoted` rather than `unicodeOutOfRange` — the whole escape-error family is
message-diverse between the pipelines, not just this member (`\q`, `\u12`, `\x4` and
`\U0011` all surface the same way) — so the rejection pins are on the *verdict*, which is what
parity requires. The acceptance pins are byte-exact against §3's legacy streams. -/

/-- The indexed pipeline's verdict for `input`: `false` iff it rejects. -/
def acceptsIx (input : String) : Bool :=
  (streamToEventsIx input).isOk

/-- The indexed pipeline's event stream, for the byte-exact acceptance pins. -/
def runIx (input : String) : String :=
  match streamToEventsIx input with | .ok s => s | .error _ => "«rejected»"

theorem ix_rejects_u_d800 : acceptsIx "a: \"\\ud800\"\n" = false := by native_decide
theorem ix_rejects_u_dfff : acceptsIx "a: \"\\udfff\"\n" = false := by native_decide
theorem ix_rejects_u_dbff : acceptsIx "a: \"\\udbff\"\n" = false := by native_decide
theorem ix_rejects_U_0000d800 : acceptsIx "a: \"\\U0000d800\"\n" = false := by native_decide
theorem ix_rejects_surrogate_pair : acceptsIx "a: \"\\uD83D\\uDE00\"\n" = false := by native_decide

/-- Boundary agreement, byte-exact: the twin emits what legacy emits. -/
theorem ix_accepts_u_d7ff : runIx "a: \"\\ud7ff\"\n" = run "a: \"\\ud7ff\"\n" := by native_decide
theorem ix_accepts_u_e000 : runIx "a: \"\\ue000\"\n" = run "a: \"\\ue000\"\n" := by native_decide
theorem ix_accepts_x41 : runIx "a: \"\\x41\"\n" = run "a: \"\\x41\"\n" := by native_decide
theorem ix_accepts_U_0010ffff :
    runIx "a: \"\\U0010FFFF\"\n" = run "a: \"\\U0010FFFF\"\n" := by native_decide

end SurrogateEscapeRejected

end Blanket
