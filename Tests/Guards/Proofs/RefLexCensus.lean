/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
import L4YAML.Proofs.Serialization.RefLex
import L4YAML.Parser.Composition

/-!
# `refLex` against `parseYaml` — the capstone's two sides on fixed inputs

`EVENTSOF-CONCEPT.md` §6 Q2: with `eventsOf` executable, the restated
capstone's right-hand conjunct `SerializationWellFormed (eventsOf input)` can
be compared with `parseYaml`'s verdict BEFORE any proof is attempted.  Each
row pins both readings.  A disagreement would be a finding, not a failure; on
this tree every row agrees, including the three `&x` self-descendant shapes
(5a(iv): the token parser's declaration set accepts what YAML 1.2.2 §3.2.2.2
admits).  Shape-only rejections are `ExactSurfaceLanguage`'s business.
-/

namespace L4YAML.Proofs.Serialization.RefLexCensus

open L4YAML
open L4YAML.Proofs.Serialization.EventsOf

def loads (input : String) : Bool :=
  match TokenParser.parseYaml input with
  | .ok _ => true
  | .error _ => false

/-- (trace well-formed, parseYaml accepts) -/
def both (input : String) : Bool × Bool := (wellFormedB input, loads input)

-- agree: well-formed and loaded
#guard both "a: &x 1\nb: *x" = (true, true)
#guard both "!<tag:x> a" = (true, true)
#guard both "!<tag:x>" = (true, true)
#guard both "&a !<tag:x> b" = (true, true)
#guard both "!<tag x> a" = (false, false)
#guard both "- &a x\n- *a" = (true, true)
#guard both "{&a x: *a, b: \"*a\"}" = (true, true)
#guard both "!!str a" = (true, true)
#guard both "a: !!str &x b" = (true, true)
#guard both "%TAG !h! tag:e,2026:\n--- !h!item value" = (true, true)
#guard both "? &k a\n: *k" = (true, true)
#guard both "a: |\n  *x\n" = (true, true)
#guard both "a: \"&x\"" = (true, true)
#guard both "a: b # *x" = (true, true)
-- agree: ill-formed and refused
#guard both "*x" = (false, false)
#guard both "[*x]" = (false, false)
#guard both "a: &x 1\n...\nb: *x" = (false, false)
#guard both "--- &x 1\n--- *x" = (false, false)
#guard both "!h!item value" = (false, false)
-- 5a(iv): the self-descendant shapes YAML 1.2.2 §3.2.2.2 admits — the trace
-- accepts them, and so does the token parser since its declaration set landed
#guard both "&x [*x]" = (true, true)
#guard both "&x {a: *x}" = (true, true)
#guard both "&x\n- *x" = (true, true)
#guard both "%TAG !h! tag:e,2026:\r\n--- !h!item value" = (true, true)
#guard both "&ab b" = (true, true)
-- shape, not state: the trace is silent and the parser refuses on syntax
#guard both "\"abc" = (false, false)
#guard both "%TAG !h! x" = (false, false)
#guard both "%TAG ! !x\n\n--- a" = (true, true)
#guard both "%YAML 1.2\n# c\n---" = (true, true)
#guard both "%YAML 1.2\n  # c\n\n---\n" = (true, true)
#guard both "%X\n#c" = (false, false)
#guard both "a: |\r\n  *x\r\n" = (true, true)
#guard both "a: |\r  *x\r" = (true, true)
#guard both "a: >\r\n  x\r\n\r\n  *y\r\nb: 1" = (true, true)

-- Known divergences of the private lexers, pinned as measured; §8 of
-- EVENTSOF-CONCEPT.md replaces `blockBody`/`plain` by the scanner's leaf
-- functions, and these rows must then flip to agreement.
#guard both "a: |2\n   *x\n  *y\n" = (false, true)
#guard both "a: foo\n  &x\nb: *x" = (true, false)

-- A verbatim tag is opaque: no `useTag` event, unlike the shorthand `!a`.
#guard eventsOf "!<tag:x> a" = []
#guard eventsOf "!a" = [.useTag "!"]

end L4YAML.Proofs.Serialization.RefLexCensus
