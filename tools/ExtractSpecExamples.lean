import Std.Data.HashMap

/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

/-!
# YAML 1.2.2 Spec Example Extractor

Scrapes the YAML 1.2.2 specification webpage and extracts all examples
into organized files following the spec's structure.

The spec page uses `<mark>` annotation tags to highlight character
classes (e.g., `·` for spaces, `→` for tabs, `↓` for newlines).
This extractor strips those annotations and replaces the visual
symbols with their actual characters, producing clean YAML files.

## Usage

```
lake build extractSpecExamples
./.lake/build/bin/extractSpecExamples
```

## Dependencies

Requires `curl` on `PATH` (no Lean library dependency).
-/

open System (FilePath)

open Std (HashMap)

/-! ## HTTP Fetch via curl subprocess -/

/-- Fetch HTML content from a URL by shelling out to `curl`. -/
def fetchUrl (url : String) : IO String := do
  IO.println s!"Fetching {url}..."
  let result ← IO.Process.output {
    cmd := "curl"
    args := #["-sL", "--fail", url]
  }
  if result.exitCode != 0 then
    throw <| IO.userError s!"curl failed (exit {result.exitCode}): {result.stderr}"
  pure result.stdout

/-! ## String Helpers -/

/-- Check if a character is an ASCII digit. -/
private def isDigit (c : Char) : Bool :=
  '0' ≤ c && c ≤ '9'

/-- Check if `s` contains substring `sub`. -/
private def stringContains (s : String) (sub : String) : Bool :=
  (s.splitOn sub).length > 1

/-- Find position of the first occurrence of `c` in `s`. -/
private def stringFindChar (s : String) (c : Char) : Option Nat :=
  let rec go (pos : Nat) (remaining : List Char) : Option Nat :=
    match remaining with
    | [] => none
    | ch :: rest => if ch == c then some pos else go (pos + 1) rest
  go 0 s.toList

/-- Take the first `n` characters of `s`. -/
private def stringTake (s : String) (n : Nat) : String :=
  String.ofList (s.toList.take n)

/-- Drop the first `n` characters of `s`. -/
private def stringDrop (s : String) (n : Nat) : String :=
  String.ofList (s.toList.drop n)

/-! ## HTML / Annotation Stripping -/

/-- Strip all `<mark ...>` opening and `</mark>` closing tags from a string. -/
private def stripMarkTags (s : String) : String :=
  -- Remove opening <mark ...> tags
  let rec stripOpen (input : String) (fuel : Nat) : String :=
    match fuel with
    | 0 => input
    | fuel' + 1 =>
      let parts := input.splitOn "<mark"
      if parts.length ≤ 1 then input
      else
        let rebuilt := parts.foldl (init := "") fun acc part =>
          if acc.isEmpty && parts.head? == some part then
            part   -- first segment (before first <mark)
          else
            -- Find the closing > of the <mark ...> tag
            match stringFindChar part '>' with
            | some idx => acc ++ stringDrop part (idx + 1)
            | none     => acc ++ part
        stripOpen rebuilt fuel'
  -- Remove closing </mark> tags
  let s := stripOpen s 20
  let parts := s.splitOn "</mark>"
  String.join parts

/-- Replace YAML spec annotation symbols with actual characters.
    The spec uses `·` for space, `→` for tab, `↓` for newline.
    Note: `·` and `→` substitute for the actual character (no space/tab byte in
    the HTML), while `↓` merely annotates an already-present newline (the line
    break byte is already in the `<pre>` content), so it is removed rather than
    doubled. -/
private def replaceAnnotationSymbols (s : String) : String :=
  let s := s.replace "·" " "     -- visible space → actual space
  let s := s.replace "→" "\t"    -- visible tab → actual tab
  let s := s.replace "↓" ""      -- visible newline → remove (newline already present)
  s

/-- Decode HTML entities. -/
private def decodeHtmlEntities (s : String) : String :=
  let s := s.replace "&gt;" ">"
  let s := s.replace "&lt;" "<"
  let s := s.replace "&amp;" "&"
  let s := s.replace "&quot;" "\""
  let s := s.replace "&#39;" "'"
  s

/-- Full cleanup pipeline: strip marks → replace symbols → decode entities. -/
private def cleanupContent (s : String) : String :=
  decodeHtmlEntities (replaceAnnotationSymbols (stripMarkTags s))

/-! ## Section / Example Parsing -/

/-- Parse section number from header text like "2.2 Structures". -/
private def parseSectionNumber (text : String) : Option String :=
  let text := text.trimAscii.copy
  let chars := text.toList
  let rec findSectionEnd (cs : List Char) (acc : List Char) : Option String :=
    match cs with
    | [] => if acc.isEmpty then none else some (String.ofList acc.reverse)
    | c :: rest =>
      if c == '.' || c == ' ' then
        if acc.isEmpty then none
        else if acc.all (fun ch => isDigit ch || ch == '.') then
          some (String.ofList acc.reverse)
        else
          none
      else if isDigit c || c == '.' then
        findSectionEnd rest (c :: acc)
      else
        none
  findSectionEnd chars []

/-- Extract example number from text like "Example 2.7". -/
private def parseExampleNumber (text : String) : Option String :=
  let text := text.trimAscii.copy.toLower
  if text.startsWith "example" then
    let rest := (text.drop 7).trimAscii.copy
    let chars := rest.toList
    let numChars := chars.takeWhile (fun c => isDigit c || c == '.')
    if numChars.isEmpty then none else some (String.ofList numChars)
  else
    none

/-! ## Main Extraction Logic -/

/-- An extracted spec example: (section, exampleNumber, yamlContent). -/
abbrev SpecExample := String × String × String

/-- Extract all examples from the YAML 1.2.2 spec HTML page. -/
def extractExamples (html : String) : IO (Array SpecExample) := do
  let lines := html.splitOn "\n"

  let mut examples : Array SpecExample := #[]
  let mut currentSection := ""
  let mut _currentSectionTitle := ""
  let mut inExample := false
  let mut exampleNumber := ""
  let mut exampleLines : Array String := #[]

  for line in lines do
    -- Detect section headers (h1, h2, h3)
    if stringContains line "<h1" || stringContains line "<h2"
       || stringContains line "<h3" then
      if let some startId := stringFindChar line '>' then
        let afterTag := stringDrop line (startId + 1)
        if let some endTag := stringFindChar afterTag '<' then
          let headerText := stringTake afterTag endTag
          if let some secNum := parseSectionNumber headerText then
            currentSection := secNum
            _currentSectionTitle := headerText.trimAscii.copy

    -- Detect example markers: <strong>Example 2.1 ...</strong>
    if stringContains line "<strong>" && stringContains (line.toLower) "example" then
      let parts := line.splitOn "<strong>"
      if let some strongStart := parts.toArray[1]? then
        let innerParts := strongStart.splitOn "</strong>"
        if let some strongContent := innerParts.toArray[0]? then
          if let some exNum := parseExampleNumber strongContent then
            exampleNumber := exNum
            if currentSection.isEmpty then
              currentSection := "2"

    -- Collect <pre> content
    if stringContains line "<pre" && !stringContains line "</pre>" then
      inExample := true
      exampleLines := #[]
    else if inExample then
      if stringContains line "</pre>" then
        if !exampleNumber.isEmpty then
          let raw := String.intercalate "\n" exampleLines.toList
          let cleaned := cleanupContent raw
          if !cleaned.trimAscii.copy.isEmpty then
            examples := examples.push (currentSection, exampleNumber, cleaned)
        inExample := false
        exampleNumber := ""
        exampleLines := #[]
      else
        exampleLines := exampleLines.push line

  pure examples

/-! ## File I/O -/

/-- Save one example to `baseDir/<section>/example-<num>.yaml`. -/
def saveExample (baseDir : FilePath) (sec : String) (exampleNum : String)
    (content : String) : IO Unit := do
  let sectionDir := baseDir / sec
  IO.FS.createDirAll sectionDir
  let filename := s!"example-{exampleNum}.yaml"
  let filepath := sectionDir / filename
  IO.FS.writeFile filepath content
  IO.println s!"  Saved: {filepath}"

/-! ## Entry Point -/

def main : IO Unit := do
  try
    IO.println "YAML 1.2.2 Spec Example Extractor"
    IO.println "==================================\n"

    let specUrl := "https://yaml.org/spec/1.2.2/"
    let html ← fetchUrl specUrl

    IO.println "Extracting examples..."
    let examples ← extractExamples html
    IO.println s!"\nFound {examples.size} examples\n"

    let baseDir : FilePath := "examples"
    IO.FS.createDirAll baseDir

    -- Group by section
    let mut sections : HashMap String (Array (String × String)) := {}
    for h : i in [:examples.size] do
      let (sec, exNum, content) := examples[i]
      let existing := sections.getD sec #[]
      sections := sections.insert sec (existing.push (exNum, content))

    -- Save
    let sectionEntries := sections.toArray
    for h : i in [:sectionEntries.size] do
      let (sec, exs) := sectionEntries[i]
      IO.println s!"Section {sec}: {exs.size} examples"
      for h2 : j in [:exs.size] do
        let (exNum, content) := exs[j]
        saveExample baseDir sec exNum content

    IO.println s!"\n✓ Extracted {examples.size} examples to ./examples/"
    IO.println "\nDirectory structure:"
    IO.println "  examples/"
    for h : i in [:sectionEntries.size] do
      let (sec, _) := sectionEntries[i]
      IO.println s!"    {sec}/"

  catch e =>
    IO.eprintln s!"Error: {e}"
    throw e
