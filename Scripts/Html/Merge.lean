module

public import Scripts.Html.Bytes
public import Scripts.Html.PdfCss
meta import Scripts.Html.Bytes

/-!
# `html-to-pdf`'s merge — one PDF-ready HTML document (was `scripts/html-to-pdf.py`)

The Python's `find_all_pages` / `BodyExtractor` / `_renumber_headings` / `merge_html`,
step for step:

* **pages** — a single file is the document in order; a site directory is ordered
  by its numbered table of contents (`<td class="num">3.2.1.</td><td><a href="…"`
  rows collected over every `index.html`, each href resolved against the page it
  appears on, kept only under the root, sorted by dotted number; root first;
  duplicates by resolved path dropped);
* **extract** — the tokens `html.parser.HTMLParser` would hand out (tags lower-
  cased, attributes re-serialised `k="v"`, comments/doctype/PIs dropped, `<script>`
  and `<style>` content raw); the head of the FIRST page and the body of every page,
  with the subtrees that would corrupt the PDF outline removed structurally:
  `<header>`, `<nav id="toc">`, `.bp_external_decl_body`, `bp_graph*` / `bp_summary*`,
  ids ending `--Dependency-Graph` / `--Blueprint-Summary`, `<script>`, `<template>`;
* **renumber** — the surviving `<hN>` get the smallest levels consistent with their
  nesting (a skip-free outline in every PDF reader);
* **assemble** — doctype, the first head, `pdfCss`, the chapters each in
  `<section class="chapter">` separated by a page-break `<div>`.

Two deliberate departures from the Python, both stated in Blueprint 09: character
references stay as written (`HTMLParser` decoded `&lt;` in text and `&amp;` in
attribute values and re-emitted them raw, which turned escaped markup into live
markup), and a valueless attribute is emitted bare (`HTMLParser` gave it the value
`None`, which the Python printed as `k="None"`).
-/

namespace Scripts.Html.Merge

@[expose] public section

open Scripts.Html

inductive Tok where
  | start (name : String) (attrs : Array (String × Option String)) (selfClosing : Bool)
  | close (name : String)
  | text (s : String)
  deriving Repr, BEq, Inhabited

/-- A start tag at `i` (`cs[i] = '<'`, a letter next): name, attributes, `/>`, end —
or `none` when no `>` closes it (`HTMLParser` then treats the rest as text). -/
partial def parseStart (cs : ByteArray) (i : Nat) :
    Option (String × Array (String × Option String) × Bool × Nat) :=
  let nEnd := skipWhile8 cs (fun x => !(isSpace8 x || x == ch '/' || x == ch '>')) (i + 1)
  attrsLoop ((sliceStr cs (i + 1) nEnd).toLower) nEnd #[]
where
  attrsLoop (name : String) (j : Nat) (acc : Array (String × Option String)) :
      Option (String × Array (String × Option String) × Bool × Nat) :=
    if j ≥ cs.size then none else
    let c := cs[j]!
    if c == ch '>' then some (name, acc, j ≥ 1 && cs[j - 1]! == ch '/', j + 1)
    else if c == ch '/' || isSpace8 c then attrsLoop name (j + 1) acc
    else
      let kEnd := skipWhile8 cs (fun x => !(isSpace8 x || x == ch '/' || x == ch '=' || x == ch '>')) (j + 1)
      let k := (sliceStr cs j kEnd).toLower
      let j2 := skipWhile8 cs isSpace8 kEnd
      if j2 < cs.size && cs[j2]! == ch '=' then
        let j3 := skipWhile8 cs isSpace8 (skipWhile8 cs (· == ch '=') j2)
        if j3 < cs.size && (cs[j3]! == ch '"' || cs[j3]! == ch '\'') then
          let q := cs[j3]!
          let vEnd := skipWhile8 cs (· != q) (j3 + 1)
          if vEnd ≥ cs.size then none
          else attrsLoop name (vEnd + 1) (acc.push (k, some (sliceStr cs (j3 + 1) vEnd)))
        else
          let vEnd := skipWhile8 cs (fun x => !(isSpace8 x || x == ch '>')) j3
          attrsLoop name vEnd (acc.push (k, some (sliceStr cs j3 vEnd)))
      else attrsLoop name kEnd (acc.push (k, none))

/-- `HTMLParser.feed` on the page's bytes. -/
partial def tokenize (cs : ByteArray) : Array Tok := run 0 0 #[]
where
  flush (acc : Array Tok) (a b : Nat) : Array Tok :=
    if a < b then acc.push (.text (sliceStr cs a b)) else acc
  rest (acc : Array Tok) (a : Nat) : Array Tok := flush acc a cs.size
  /-- a text run from `seg`, scanning for `<` from `i` -/
  run (seg i : Nat) (acc : Array Tok) : Array Tok :=
    let lt := skipWhile8 cs (· != ch '<') i
    if lt ≥ cs.size then flush acc seg lt else construct lt (flush acc seg lt)
  construct (i : Nat) (acc : Array Tok) : Array Tok :=
    let n := i + 1
    if n ≥ cs.size then rest acc i else
    let c := cs[n]!
    if isAlpha8 c then
      match parseStart cs i with
      | none => rest acc i
      | some (name, as, sc, e) =>
        let acc := acc.push (.start name as sc)
        if !sc && (name == "script" || name == "style") then cdata name e acc else run e e acc
    else if c == ch '/' then
      let j := skipWhile8 cs isSpace8 (n + 1)
      let nEnd := skipWhile8 cs (fun x => isWord8 x || x == ch '-' || x == ch '.' || x == ch ':') j
      let gt := skipWhile8 cs (· != ch '>') nEnd
      if gt ≥ cs.size then rest acc i
      else if nEnd > j && isAlpha8 cs[j]! then run (gt + 1) (gt + 1) (acc.push (.close (sliceStr cs j nEnd).toLower))
      else run (gt + 1) (gt + 1) acc
    else if c == ch '!' then
      if matchesAt cs i "<!--" then
        match findFrom cs (i + 4) "-->" with
        | some e => run (e + 3) (e + 3) acc
        | none => rest acc i
      else if matchesAt cs i "<![" then
        match findFrom cs (i + 3) "]>" with
        | some e => run (e + 2) (e + 2) acc
        | none => rest acc i
      else
        let gt := skipWhile8 cs (· != ch '>') n
        if gt ≥ cs.size then rest acc i else run (gt + 1) (gt + 1) acc
    else if c == ch '?' then
      let gt := skipWhile8 cs (· != ch '>') n
      if gt ≥ cs.size then rest acc i else run (gt + 1) (gt + 1) acc
    else run i n acc
  /-- raw content of `<script>`/`<style>` up to its own end tag -/
  cdata (name : String) (i : Nat) (acc : Array Tok) : Array Tok :=
    match findClose name i with
    | some (s, e) => run e e ((flush acc i s).push (.close name))
    | none => rest acc i
  findClose (name : String) (k : Nat) : Option (Nat × Nat) :=
    match findFrom cs k ("</" ++ name) (icase := true) with
    | none => none
    | some p =>
      let j := skipWhile8 cs isSpace8 (p + 2 + name.length)
      if j < cs.size && cs[j]! == ch '>' then some (p, j + 1) else findClose name (p + 1)

def attrsRender (as : Array (String × Option String)) : String :=
  as.foldl (fun s kv => s ++ match kv.2 with | some v => s!" {kv.1}=\"{v}\"" | none => s!" {kv.1}") ""

/-- `dict(attrs).get(k) or ""`. -/
def attrGet (as : Array (String × Option String)) (k : String) : String :=
  ((as.foldl (fun acc kv => if kv.1 == k then some kv.2 else acc) none).bind id).getD ""

def hasSub (s sub : String) : Bool := (s.splitOn sub).length > 1

/-- `BodyExtractor._should_drop`. -/
def shouldDrop (tag : String) (as : Array (String × Option String)) : Bool :=
  let cls := attrGet as "class"
  let idv := attrGet as "id"
  tag == "script" || tag == "template" || tag == "header"
  || (tag == "nav" && idv == "toc")
  || hasSub cls "bp_external_decl_body" || hasSub cls "bp_graph" || hasSub cls "bp_summary"
  || idv.endsWith "--Dependency-Graph" || idv.endsWith "--Blueprint-Summary"

structure Ext where
  inBody : Bool := false
  inHead : Bool := false
  body : String := ""
  head : String := ""
  dropTag : Option String := none
  dropCount : Nat := 0

/-- Append to the body if in it, and to the head if in it (the Python's two `if`s). -/
def Ext.emit (st : Ext) (s : String) : Ext :=
  let st := if st.inBody then { st with body := st.body ++ s } else st
  if st.inHead then { st with head := st.head ++ s } else st

/-- `BodyExtractor`'s handlers, one token at a time. -/
def step (st : Ext) : Tok → Ext
  | .start name as false =>
    if name == "body" then { st with inBody := true }
    else if name == "head" then { st with inHead := true }
    else if st.inBody && st.dropTag.isSome then
      if st.dropTag == some name then { st with dropCount := st.dropCount + 1 } else st
    else if st.inBody && shouldDrop name as then { st with dropTag := some name, dropCount := 1 }
    else st.emit s!"<{name}{attrsRender as}>"
  | .start name as true =>
    if st.inBody && st.dropTag.isSome then st
    else
      let s := s!"<{name}{attrsRender as}/>"
      if st.inBody then { st with body := st.body ++ s }
      else if st.inHead then { st with head := st.head ++ s }
      else st
  | .close name =>
    if name == "body" then { st with inBody := false }
    else if name == "head" then { st with inHead := false }
    else if st.inBody && st.dropTag.isSome then
      if st.dropTag == some name then
        let c := st.dropCount - 1
        if c == 0 then { st with dropTag := none, dropCount := 0 } else { st with dropCount := c }
      else st
    else st.emit s!"</{name}>"
  | .text d => if st.inBody && st.dropTag.isSome then st else st.emit d

def extract (page : ByteArray) : Ext := (tokenize page).foldl step {}

/-- `_renumber_headings`: `<(/?)(h)([1-6])\b` (case-insensitive) rewritten in one pass. -/
partial def renumberHeadings (body : ByteArray) : ByteArray := go 0 0 ByteArray.empty [] []
where
  go (i seg : Nat) (out : ByteArray) (ctx opened : List Nat) : ByteArray :=
    if i ≥ body.size then out.append (body.extract seg body.size)
    else if body[i]! != ch '<' then go (i + 1) seg out ctx opened
    else
      let (closing, j) := if i + 1 < body.size && body[i + 1]! == ch '/' then (true, i + 2) else (false, i + 1)
      if j + 1 < body.size && lower8 body[j]! == ch 'h' && 49 ≤ body[j + 1]! && body[j + 1]! ≤ 54
          && (j + 2 == body.size || !isWord8 body[j + 2]!) then
        let lvl := (body[j + 1]! - 48).toNat
        if closing then
          let (a, opened) := match opened with | a :: more => (a, more) | [] => (lvl, [])
          go (j + 2) (j + 2) ((out.append (body.extract seg i)).append s!"</h{a}".toUTF8) ctx opened
        else
          let ctx := lvl :: ctx.dropWhile (· ≥ lvl)
          let a := ctx.length
          go (j + 2) (j + 2) ((out.append (body.extract seg i)).append s!"<h{a}".toUTF8) ctx (a :: opened)
      else go (i + 1) seg out ctx opened

def renumber (s : String) : String := String.fromUTF8! (renumberHeadings s.toUTF8)

/-- `merge_html` on the pages' bytes (first page's head, every page's body). -/
def mergeBytes (pages : Array ByteArray) : String :=
  let head := (extract pages[0]!).head
  let body := (List.range pages.size).foldl (init := "") fun acc i =>
    let content := (extract pages[i]!).body
    let acc := if i > 0 then acc ++ "<div style=\"page-break-before: always;\"></div>" else acc
    acc ++ s!"<section class=\"chapter\">{content}</section>"
  "<!DOCTYPE html>\n<html lang=\"en\"><head><meta charset=\"utf-8\">\n"
    ++ head ++ "\n" ++ pdfCss ++ "\n</head>\n<body>\n" ++ renumber body ++ "\n</body></html>"

/-- `_NAV_ROW` anchored at `i`: number, href, end. -/
def navRowAt? (cs : ByteArray) (i : Nat) : Option (String × String × Nat) :=
  let p := "<td class=\"num\">"
  if !matchesAt cs i p then none else
  let a := i + p.length
  let b := skipWhile8 cs (fun x => isDigit8 x || x == ch '.') a
  if b == a || !matchesAt cs b "</td>" then none else
  let c := skipWhile8 cs isSpace8 (b + 5)
  let q := "<td><a href=\""
  if !matchesAt cs c q then none else
  let d := c + q.length
  let e := skipWhile8 cs (· != ch '"') d
  if e == d || e ≥ cs.size then none else
  some (sliceStr cs a b, sliceStr cs d e, e + 1)

/-- `_NAV_ROW.findall(text)`. -/
partial def navRows (cs : ByteArray) (i : Nat := 0) (acc : Array (String × String) := #[]) :
    Array (String × String) :=
  if i ≥ cs.size then acc
  else match navRowAt? cs i with
    | some (num, href, e) => navRows cs e (acc.push (num, href))
    | none => navRows cs (i + 1) acc

/-- `numkey`: `tuple(int(x) for x in n.strip(".").split("."))`. -/
def numKey (n : String) : Except String (List Nat) :=
  let s := stripDots n
  (s.splitOn ".").mapM fun x => match x.toNat? with
    | some v => .ok v
    | none => .error s!"invalid literal for int() with base 10: '{x}'"

partial def ltKey : List Nat → List Nat → Bool
  | [], [] => false
  | [], _ => true
  | _, [] => false
  | a :: as, b :: bs => if a < b then true else if b < a then false else ltKey as bs

#guard (tokenize "<!DOCTYPE html>\n<P Class=\"x\" hidden>a &amp; b<br/></p><!-- c --><script>if (a<b) x()</script>".toUTF8)
  == (#[.text "\n", .start "p" #[("class", some "x"), ("hidden", none)] false, .text "a &amp; b",
      .start "br" #[] true, .close "p", .start "script" #[] false, .text "if (a<b) x()", .close "script"] : Array Tok)
#guard (extract "<html><head><title>T</title></head><body><header><h1>Site</h1></header><main><h2 id=\"s\">S</h2><div class=\"bp_graph_x\"><div></div><h3>no</h3></div><p>k</p></main></body></html>".toUTF8).body
  == "<main><h2 id=\"s\">S</h2><p>k</p></main>"
#guard (extract "<html><head><meta charset=\"utf-8\"><style>a{}</style></head><body></body></html>".toUTF8).head
  == "<meta charset=\"utf-8\"><style>a{}</style>"
#guard renumber "<h1>a</h1><h3 id=\"x\">b</h3><H4>c</H4><h2>d</h2>" == "<h1>a</h1><h2 id=\"x\">b</h2><h3>c</h3><h2>d</h2>"
#guard renumber "</h3><h10>" == "</h3><h10>"
#guard navRows "<td class=\"num\">3.2.</td>\n  <td><a href=\"../x/\">X</a><td class=\"num\">4</td><td><a href=\"y.html#z\">".toUTF8
  == #[("3.2.", "../x/"), ("4", "y.html#z")]
#guard (numKey "3.2.1.").toOption == some [3, 2, 1]
#guard (numKey "3..2").toOption == none
#guard ltKey [3, 2] [3, 2, 1] == true

end

end Scripts.Html.Merge
