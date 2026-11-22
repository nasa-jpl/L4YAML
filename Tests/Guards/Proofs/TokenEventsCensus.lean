import L4YAML.Scanner.Scanner
import L4YAML.Proofs.Serialization.RefLex
import L4YAML.Proofs.Serialization.TokenEvents

/-!
# `tokenEvents ∘ scan` against `eventsOf` (EVENTSOF-CONCEPT §9, S2 census)

Two independent readings of the same input's serialization trace: the scanner's
token stream and the reference lexer's skeleton.  S3 will prove the scan's
skeleton witness has the `tokenEvents` trace, so on every input both accept
the two must agree; disagreements are pinned as measured with the reason.
-/

namespace Tests.Guards.TokenEventsCensus

open L4YAML
open L4YAML.Proofs.Serialization.SerializationWellFormed
open L4YAML.Proofs.Serialization.EventsOf
open L4YAML.Proofs.Serialization.TokenEvents

def both (s : String) : Option (List Event) × Option (List Event) :=
  ((Scanner.scan s).toOption.map tokenEvents, (refLex s).map eventsOfSegs)

/-- Both readings accept and agree. -/
def agree (s : String) : Bool :=
  match both s with
  | (some a, some b) => a == b
  | _ => false

def agreeing : List String := [
  "", "a", "&x [*x]", "&x {a: *x}", "&x\n- *x", "\"&x\"", "# *x", "a # *x",
  "%TAG ! !x\n--- !a", "%TAG ! !x\n\n--- a", "%TAG !e! tag:x,2000:\n--- !e!a", "%TAG !! tag:y\n--- !!str a", "!<tag:x> a", "!<tag:x>", "&a !<tag:x> b", "%YAML 1.2\n# c\n---", "%YAML 1.2\r\n---",
  "---\n---", "--- a\n...\n--- b", "...", "a\n...", "!!str a", "!h!item",   "- &a x\n- *a", "? a\n: b", "a: >-\n  x\n", "'a''b'",
  "\"a\\\"b\"", "a:\n  - b\n  -\n    c", "{a: [b, {c: d}]}", "[a,\n b]", "a\r\nb",
  "a\rb\r...", "- - - a", "...\n--- a", "&a !t x"
]

#guard agreeing.all agree

-- `%TAG !h` is not a [89] `c-tag-handle` (`!`, `!!`, `!word!`): the scanner refuses it
-- (`invalidTagHandle`); the reference lexer's trace is the skeleton reading only.
#guard (both "%TAG !h tag:x\n---").1 = none

-- `scan` refuses an alias before its anchor and properties on an alias; the
-- skeleton still has a trace there (the surface conjunct, not this one, rejects).
#guard both "[*x]" = (none, some [.useAlias "x"])
#guard both "[&a *a]" = (none, some [.defineAnchor "a", .useAlias "a"])
#guard both "a: |\n  x\n  &y\nb: *y" = (none, some [.useAlias "y"])
#guard both "a: foo\n  &x\nb: *x" = (none, some [.defineAnchor "x", .useAlias "x"])

end Tests.Guards.TokenEventsCensus
