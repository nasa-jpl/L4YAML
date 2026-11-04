module

public import Scripts.Html.Bytes
meta import Scripts.Html.Bytes

/-!
# `lake run svg-objects -- DIR` — SVG `<img>` → `<object>` (was `scripts/svg-objects.py`)

Verso renders every Markdown image as `<img>`.  An SVG loaded through `<img>` is
static — browsers disable all navigation inside it — so the Graphviz `URL=` links
the theorem-dependency graphs carry are dead; through
`<object type="image/svg+xml">` the same SVG keeps its hyperlinks.  Run over the
MULTI-page site only; the single page stays `<img>` because WeasyPrint rasterises
`<img src="*.svg">` natively and would render an `<object>` as its fallback text.

The reading is the Python's, operator for operator: `IMG_RE = <img\b[^>]*>` (case-
insensitive), `ATTR_RE = ([a-zA-Z-]+)\s*=\s*"([^"]*)"` over the tag (`dict(findall)`:
the last duplicate wins, names are case-sensitive), `src` with its `#…`/`?…` tail
removed must end in `.svg` (case-insensitive), and the rewrite is
`<object type="image/svg+xml" data="SRC"[ title="TITLE"]>ALT</object>` — the `src`
verbatim as `data=` (it resolves through the page's `<base>` as before), the alt
text moved into the element body.  Idempotent: a second run finds no `<img>`.
-/

namespace Scripts.Html.Svg

@[expose] public section

open Scripts.Html

/-- `IMG_RE` anchored at `i`: the end of the match. -/
def imgTagEnd? (cs : ByteArray) (i : Nat) : Option Nat :=
  if matchesAt cs i "<img" (icase := true) && (i + 4 == cs.size || !isWord8 cs[i + 4]!) then
    let j := skipWhile8 cs (· != ch '>') (i + 4)
    if j < cs.size then some (j + 1) else none
  else none

/-- One `ATTR_RE` attempt anchored at `i`: name, value, end. -/
def attrAt? (cs : ByteArray) (i : Nat) : Option (String × String × Nat) :=
  let nEnd := skipWhile8 cs (fun x => isAlpha8 x || x == ch '-') i
  if nEnd == i then none else
  let j := skipWhile8 cs isSpace8 nEnd
  if !(j < cs.size && cs[j]! == ch '=') then none else
  let j := skipWhile8 cs isSpace8 (j + 1)
  if !(j < cs.size && cs[j]! == ch '"') then none else
  let vEnd := skipWhile8 cs (· != ch '"') (j + 1)
  if vEnd ≥ cs.size then none else
  some (sliceStr cs i nEnd, sliceStr cs (j + 1) vEnd, vEnd + 1)

/-- `ATTR_RE.findall(tag)`, in order. -/
partial def attrs (tag : ByteArray) (i : Nat := 0) (acc : Array (String × String) := #[]) :
    Array (String × String) :=
  if i ≥ tag.size then acc
  else match attrAt? tag i with
    | some (k, v, e) => attrs tag e (acc.push (k, v))
    | none => attrs tag (i + 1) acc

/-- `dict(findall).get(k)`: the last occurrence. -/
def lookupLast (as : Array (String × String)) (k : String) : Option String :=
  as.foldl (fun acc kv => if kv.1 == k then some kv.2 else acc) none

/-- `src.split("#")[0].split("?")[0].lower().endswith(".svg")`. -/
def isSvgSrc (src : String) : Bool :=
  let t := (((src.splitOn "#").headD "").splitOn "?").headD ""
  t.toLower.endsWith ".svg"

/-- The replacement for one `<img …>` tag, or `none` when its `src` is not an SVG. -/
def objectFor (tag : ByteArray) : Option String :=
  let as := attrs tag
  let src := (lookupLast as "src").getD ""
  if !isSvgSrc src then none else
  let title := match lookupLast as "title" with
    | some t => if t.isEmpty then "" else s!" title=\"{t}\""
    | none => ""
  let alt := (lookupLast as "alt").getD ""
  some s!"<object type=\"image/svg+xml\" data=\"{src}\"{title}>{alt}</object>"

/-- `IMG_RE.sub(replace, html)` and the count of rewritten tags. -/
partial def rewriteBytes (cs : ByteArray) : ByteArray × Nat := go 0 0 ByteArray.empty 0
where
  go (i seg : Nat) (out : ByteArray) (n : Nat) : ByteArray × Nat :=
    if i ≥ cs.size then (out.append (cs.extract seg cs.size), n)
    else match imgTagEnd? cs i with
      | some e =>
        match objectFor (cs.extract i e) with
        | some r => go e e ((out.append (cs.extract seg i)).append r.toUTF8) (n + 1)
        | none => go e seg out n
      | none => go (i + 1) seg out n

def rewrite (html : String) : String × Nat :=
  let (b, n) := rewriteBytes html.toUTF8
  (String.fromUTF8! b, n)

#guard rewrite "<p><img src=\"g.svg\" alt=\"Graph\"></p>"
  == ("<p><object type=\"image/svg+xml\" data=\"g.svg\">Graph</object></p>", 1)
#guard rewrite "<IMG src=\"a.svg\">" == ("<object type=\"image/svg+xml\" data=\"a.svg\"></object>", 1)
#guard rewrite "<img SRC=\"a.svg\">" == ("<img SRC=\"a.svg\">", 0)
#guard rewrite "<img src=\"a.png\">" == ("<img src=\"a.png\">", 0)
#guard rewrite "<imgx src=\"a.svg\">" == ("<imgx src=\"a.svg\">", 0)
#guard rewrite "<img title=\"T\" alt=\"A &amp; B\" src=\"../x/g.SVG?v=1#top\" />"
  == ("<object type=\"image/svg+xml\" data=\"../x/g.SVG?v=1#top\" title=\"T\">A &amp; B</object>", 1)
#guard rewrite "<img src=\"a.svg\" title=\"\">" == ("<object type=\"image/svg+xml\" data=\"a.svg\"></object>", 1)
#guard rewrite "<img src=\"x.svg\" src=\"y.png\">" == ("<img src=\"x.svg\" src=\"y.png\">", 0)
#guard rewrite "<img src=\"a.svg\"" == ("<img src=\"a.svg\"", 0)
#guard rewrite "<img\nsrc = \"a.svg\"\n>" == ("<object type=\"image/svg+xml\" data=\"a.svg\"></object>", 1)
#guard (rewrite (rewrite "<img src=\"a.svg\"><img src=\"b.svg\">").1).2 == 0

end

end Scripts.Html.Svg
