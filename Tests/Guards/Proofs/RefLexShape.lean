import L4YAML.Proofs.Serialization.RefLex

/-!
# `refLex` output has the shape of a `Skeleton` — the decidable half (Rule 2)

`refLex_sound : refLex input = some segs → Skeleton 0 input.toList segs`
is the next serialization lemma.  `Skeleton` is a `Prop` over surface
derivations, so it cannot be decided; this guard decides every side condition
of `SegAt`/`Skeleton` that is boolean — the segments concatenate back to the
input, each event lexeme is well-formed and maximal, document markers sit at
column 0, directive lines start with `%` and end in a break, `other` runs are
non-empty, event-free and never adjacent — on a fixed grid of inputs, so a
mis-segmenting arm of `step` fails here before a proof is attempted.

History: the first grid refuted the directive arm — `%TAG ! !x⏎⏎--- a` was
segmented `other "⏎" :: docStart …`, the blank line between the directive and
`---` emitted BEFORE the directive text it follows (`skeleton_text` false).
`[79] s-l-comments` lets a directive absorb the blank and comment lines after
it; `commentLines` now does the same.
-/
open L4YAML
open L4YAML.Proofs.Serialization.EventsOf

namespace Tests.Guards.RefLexShape

def anchorCh := L4YAML.Proofs.Serialization.SourceEvents.isAnchorCharBool
def tagCh := L4YAML.Proofs.Serialization.EventsOf.isTagCharBool

/-- The boolean side conditions of `SegAt col seg rest`. -/
def segShape (col : Nat) : Seg → List Char → Bool
  | .anchor n, rest =>
      n.toList ≠ [] && n.toList.all anchorCh && (rest.head?.all fun c => !anchorCh c)
  | .alias n, rest =>
      n.toList ≠ [] && n.toList.all anchorCh && (rest.head?.all fun c => !anchorCh c)
  | .tagUse h cs, rest =>
      handleOf cs == h && cs.all tagCh && cs.head? == some '!' &&
        (rest.head?.all fun c => !tagCh c)
  | .docStart dirs, _ =>
      col == 0 && dirs.all fun d => d.head? == some '%' && (d.getLast?.any isBreak)
  | .docEnd, _ => col == 0
  | .opaque cs, _ => cs ≠ []
  | .other cs, _ => cs ≠ [] && noEventLexeme col cs

/-- The boolean side conditions of `Skeleton col chars segs`. -/
def shape : Nat → List Char → List Seg → Bool
  | _, [], [] => true
  | col, chars, seg :: segs =>
      let t := seg.text
      chars.take t.length == t && segShape col seg (chars.drop t.length) &&
        !(seg.isOther && segs.head?.any Seg.isOther) &&
        shape (colAfter col t) (chars.drop t.length) segs
  | _, _, _ => false

/-- `true` when `refLex` refuses or its output has skeleton shape. -/
def ok (s : String) : Bool :=
  match refLex s with
  | none => true
  | some segs => shape 0 s.toList segs

def grid : List String := [
  "", "a", "&x [*x]", "&x {a: *x}", "&x\n- *x", "[*x]", "\"&x\"", "# *x", "a # *x",
  "%TAG ! !x\n--- !a", "%TAG ! !x\n\n--- a", "%YAML 1.2\n# c\n---", "%YAML 1.2\n  # c\n\n---\n",
  "%YAML 1.2\r\n---", "%X\n#c", "---\n---", "--- a\n...\n--- b", "...", "a\n...", "!!str a",
  "!h!item", "!<tag:x> a", "- &a x\n- *a", "? a\n: b", "a: |\n  x\n  &y\nb: *y", "a: >-\n  x\n",
  "'a''b'", "\"a\\\"b\"", "a:\n  - b\n  -\n    c", "{a: [b, {c: d}]}", "[a,\n b]", "a\r\nb",
  "a\rb\r...", " ---", "x---", "- - - a", "&a", "*", "!", "%X", "a\n%X\n---", "&a&b", "*a*b",
  "!a!b!c", "&a*b", "[&a *a]", "\"\n\"", "'\n'", "#", "\n\n\n", "  \n  a", "a\n\n", "---",
  "--- ", "---\t", "---x", "... "
]

-- Every grid input: refused, or segmented with skeleton shape.
#guard grid.all ok

-- The refuting input, now segmented in text order.
#guard (refLex "%TAG ! !x\n\n--- a").map (·.map Seg.isOther) = some [false, true, false]

-- `refLex` refuses exactly the inputs the skeleton cannot describe.
#guard grid.filter (fun s => (refLex s).isNone) = ["%X\n#c", "*", "%X"]

end Tests.Guards.RefLexShape
